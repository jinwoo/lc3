(* Memory-mapped registers *)
let mr_kbsr = 0xfe00 (* keyboard status *)
let mr_kbdr = 0xfe02 (* keyboard data *)

(* Memory *)
let memory_max = 1 lsl 16

(* Registers *)
let r_r0 = 0
let r_r7 = 7
let r_pc = 8
let r_cond = 9
let r_count = 10

(* Condition flags *)
let fl_pos = 1 lsl 0
let fl_zro = 1 lsl 1
let fl_neg = 1 lsl 2

type vm = { memory : int array; reg : int array; mutable running : bool }

let make_vm () =
  let memory = Array.make memory_max 0 in
  let reg = Array.make r_count 0 in
  (* Since exactly one condition flag should be set at any given time,
     set the Z flag. *)
  reg.(r_cond) <- fl_zro;
  (* Set the PC to starting position. 0x3000 is the default. *)
  reg.(r_pc) <- 0x3000;
  { memory; reg; running = true }

type opcode =
  | Op_br (* branch *)
  | Op_add (* add *)
  | Op_ld (* load *)
  | Op_st (* store *)
  | Op_jsr (* jump register *)
  | Op_and (* bitwise and *)
  | Op_ldr (* load register *)
  | Op_str (* store register *)
  | Op_rti (* unused *)
  | Op_not (* bitwise not *)
  | Op_ldi (* load indirect *)
  | Op_sti (* store indirect *)
  | Op_jmp (* jump *)
  | Op_res (* reserved (unused) *)
  | Op_lea (* load effective address *)
  | Op_trap (* execute trap *)

let opcode_of_int = function
  | 0 -> Op_br
  | 1 -> Op_add
  | 2 -> Op_ld
  | 3 -> Op_st
  | 4 -> Op_jsr
  | 5 -> Op_and
  | 6 -> Op_ldr
  | 7 -> Op_str
  | 8 -> Op_rti
  | 9 -> Op_not
  | 10 -> Op_ldi
  | 11 -> Op_sti
  | 12 -> Op_jmp
  | 13 -> Op_res
  | 14 -> Op_lea
  | 15 -> Op_trap
  | n -> invalid_arg ("invalid opcode " ^ string_of_int n)

(* Trap codes *)
type trapcode =
  (* Get character from keyboard, not echoed onto the terminal. *)
  | Trap_getc
  (* Output a character. *)
  | Trap_out
  (* Output a word string. *)
  | Trap_puts
  (* Get character from keyboard, echoed onto the terminal. *)
  | Trap_in
  (* Output a byte string. *)
  | Trap_putsp
  (* Halt the program. *)
  | Trap_halt

let trapcode_of_int = function
  | 0x20 -> Trap_getc
  | 0x21 -> Trap_out
  | 0x22 -> Trap_puts
  | 0x23 -> Trap_in
  | 0x24 -> Trap_putsp
  | 0x25 -> Trap_halt
  | n -> failwith ("invalid trapcode: " ^ string_of_int n)

let read_image { memory; _ } image_path =
  In_channel.with_open_bin image_path (fun ic ->
      let buf = Bytes.create 2 in
      match In_channel.really_input ic buf 0 2 with
      | None -> failwith "failed to read image"
      | Some () ->
          let origin = Bytes.get_uint16_be buf 0 in
          let max_read = memory_max - origin in
          let buf = Bytes.create max_read in
          let read = In_channel.input ic buf 0 max_read in
          let rec aux pos =
            if pos >= read then ()
            else
              let n = Bytes.get_uint16_be buf pos in
              memory.(origin + (pos / 2)) <- n;
              aux (pos + 2)
          in
          aux 0)

let original_tio = Unix.tcgetattr Unix.stdin

let disable_input_buffering () =
  let open Unix in
  let new_tio = { original_tio with c_icanon = false; c_echo = false } in
  tcsetattr stdin TCSANOW new_tio

let restore_input_buffering () =
  let open Unix in
  tcsetattr stdin TCSANOW original_tio

let check_key () =
  match Unix.select [ Unix.stdin ] [] [] 0. with
  | [], _, _ -> false
  | _ :: _, _, _ -> true

let handle_interrupt _ =
  restore_input_buffering ();
  print_newline ();
  exit (-2)

let setup () =
  Sys.set_signal Sys.sigint (Sys.Signal_handle handle_interrupt);
  disable_input_buffering ()

let mem_read { memory; _ } address =
  if address = mr_kbsr then
    if check_key () then (
      memory.(mr_kbsr) <- 1 lsl 15;
      memory.(mr_kbdr) <- input_char stdin |> int_of_char)
    else memory.(mr_kbsr) <- 0;
  memory.(address)

let mem_write { memory; _ } address value = memory.(address) <- value

let sign_extend x bit_count =
  if (x lsr (bit_count - 1)) land 1 <> 0 then x lor (0xffff lsl bit_count)
  else x

let update_flags { reg; _ } r =
  let fl =
    if reg.(r) = 0 then fl_zro
    else if
      reg.(r) lsr 15 <> 0 (* A 1 in the left-most bit indicates negative. *)
    then fl_neg
    else fl_pos
  in
  reg.(r_cond) <- fl

let exec_add ({ reg; _ } as vm) instr =
  let r0 = (instr lsr 9) land 0x7 in
  let r1 = (instr lsr 6) land 0x7 in
  let imm_flag = (instr lsr 5) land 0x1 in
  (if imm_flag <> 0 then
   let imm5 = sign_extend (instr land 0x1f) 5 in
   reg.(r0) <- (reg.(r1) + imm5) land 0xffff
  else
    let r2 = instr land 0x7 in
    reg.(r0) <- (reg.(r1) + reg.(r2)) land 0xffff);
  update_flags vm r0

let exec_and ({ reg; _ } as vm) instr =
  let r0 = (instr lsr 9) land 0x7 in
  let r1 = (instr lsr 6) land 0x7 in
  let imm_flag = (instr lsr 5) land 0x1 in
  (if imm_flag <> 0 then
   let imm5 = sign_extend (instr land 0x1f) 5 in
   reg.(r0) <- reg.(r1) land imm5
  else
    let r2 = instr land 0x7 in
    reg.(r0) <- reg.(r1) land reg.(r2));
  update_flags vm r0

let exec_not ({ reg; _ } as vm) instr =
  let r0 = (instr lsr 9) land 0x7 in
  let r1 = (instr lsr 6) land 0x7 in
  reg.(r0) <- lnot reg.(r1) land 0xffff;
  update_flags vm r0

let exec_br { reg; _ } instr =
  let pc_offset = sign_extend (instr land 0x1ff) 9 in
  let cond_flag = (instr lsr 9) land 0x7 in
  if cond_flag land reg.(r_cond) <> 0 then
    reg.(r_pc) <- (reg.(r_pc) + pc_offset) land 0xffff

let exec_jmp { reg; _ } instr =
  let r1 = (instr lsr 6) land 0x7 in
  reg.(r_pc) <- reg.(r1)

let exec_jsr { reg; _ } instr =
  let long_flag = (instr lsr 11) land 1 in
  reg.(r_r7) <- reg.(r_pc);
  if long_flag <> 0 then
    (* JSR *)
    let long_pc_offset = sign_extend (instr land 0x7ff) 11 in
    reg.(r_pc) <- (reg.(r_pc) + long_pc_offset) land 0xffff
  else
    (* JSRR *)
    let r1 = (instr lsr 6) land 0x7 in
    reg.(r_pc) <- reg.(r1)

let exec_ld ({ reg; _ } as vm) instr =
  let r0 = (instr lsr 9) land 0x7 in
  let pc_offset = sign_extend (instr land 0x1ff) 9 in
  reg.(r0) <- mem_read vm ((reg.(r_pc) + pc_offset) land 0xffff);
  update_flags vm r0

let exec_ldi ({ reg; _ } as vm) instr =
  let r0 = (instr lsr 9) land 0x7 in
  let pc_offset = sign_extend (instr land 0x1ff) 9 in
  reg.(r0) <- mem_read vm (mem_read vm ((reg.(r_pc) + pc_offset) land 0xffff));
  update_flags vm r0

let exec_ldr ({ reg; _ } as vm) instr =
  let r0 = (instr lsr 9) land 0x7 in
  let r1 = (instr lsr 6) land 0x7 in
  let offset = sign_extend (instr land 0x3f) 6 in
  reg.(r0) <- mem_read vm ((reg.(r1) + offset) land 0xffff);
  update_flags vm r0

let exec_lea ({ reg; _ } as vm) instr =
  let r0 = (instr lsr 9) land 0x7 in
  let pc_offset = sign_extend (instr land 0x1ff) 9 in
  reg.(r0) <- (reg.(r_pc) + pc_offset) land 0xffff;
  update_flags vm r0

let exec_st ({ reg; _ } as vm) instr =
  let r0 = (instr lsr 9) land 0x7 in
  let pc_offset = sign_extend (instr land 0x1ff) 9 in
  mem_write vm ((reg.(r_pc) + pc_offset) land 0xffff) reg.(r0)

let exec_sti ({ reg; _ } as vm) instr =
  let r0 = (instr lsr 9) land 0x7 in
  let pc_offset = sign_extend (instr land 0x1ff) 9 in
  mem_write vm (mem_read vm ((reg.(r_pc) + pc_offset) land 0xffff)) reg.(r0)

let exec_str ({ reg; _ } as vm) instr =
  let r0 = (instr lsr 9) land 0x7 in
  let r1 = (instr lsr 6) land 0x7 in
  let offset = sign_extend (instr land 0x3f) 6 in
  mem_write vm ((reg.(r1) + offset) land 0xffff) reg.(r0)

let exec_trap_getc ({ reg; _ } as vm) =
  reg.(r_r0) <- input_char stdin |> int_of_char;
  update_flags vm r_r0

let exec_trap_out { reg; _ } =
  output_char stdout (reg.(r_r0) |> char_of_int);
  flush stdout

let exec_trap_puts { memory; reg; _ } =
  let rec aux i =
    let c = memory.(reg.(r_r0) + i) in
    if c = 0 then ()
    else (
      output_char stdout (char_of_int c);
      aux (i + 1))
  in
  aux 0;
  flush stdout

let exec_trap_in ({ reg; _ } as vm) =
  print_string "Enter a character: ";
  flush stdout;
  let c = input_char stdin in
  output_char stdout c;
  flush stdout;
  reg.(r_r0) <- int_of_char c;
  update_flags vm r_r0

let exec_trap_putsp { memory; reg; _ } =
  let rec aux i =
    let c = memory.(reg.(r_r0) + i) in
    if c = 0 then ()
    else
      let char1 = c land 0xff in
      if char1 = 0 then ()
      else (
        output_char stdout (char_of_int char1);
        let char2 = c lsr 8 in
        if char2 = 0 then ()
        else (
          output_char stdout (char_of_int char2);
          aux (i + 1)))
  in
  aux 0;
  flush stdout

let exec_trap_halt vm =
  print_endline "HALT";
  flush stdout;
  vm.running <- false

let exec_trap ({ reg; _ } as vm) instr =
  reg.(r_r7) <- reg.(r_pc);
  match instr land 0xff |> trapcode_of_int with
  | Trap_getc -> exec_trap_getc vm
  | Trap_out -> exec_trap_out vm
  | Trap_puts -> exec_trap_puts vm
  | Trap_in -> exec_trap_in vm
  | Trap_putsp -> exec_trap_putsp vm
  | Trap_halt -> exec_trap_halt vm

let run ({ reg; running; _ } as vm) =
  let rec aux () =
    (if not running then ()
    else
      let pc = reg.(r_pc) in
      reg.(r_pc) <- pc + 1;
      let instr = mem_read vm pc in
      match instr lsr 12 |> opcode_of_int with
      | Op_add -> exec_add vm instr
      | Op_and -> exec_and vm instr
      | Op_not -> exec_not vm instr
      | Op_br -> exec_br vm instr
      | Op_jmp -> exec_jmp vm instr
      | Op_jsr -> exec_jsr vm instr
      | Op_ld -> exec_ld vm instr
      | Op_ldi -> exec_ldi vm instr
      | Op_ldr -> exec_ldr vm instr
      | Op_lea -> exec_lea vm instr
      | Op_st -> exec_st vm instr
      | Op_sti -> exec_sti vm instr
      | Op_str -> exec_str vm instr
      | Op_trap -> exec_trap vm instr
      | Op_rti -> failwith "RTI"
      | Op_res -> failwith "RES");
    aux ()
  in
  aux ()

let load_arguments vm =
  let argc = Array.length Sys.argv in
  if argc < 2 then (
    print_endline "lc3 [image-file1] ...";
    exit 2);
  for i = 1 to argc - 1 do
    read_image vm Sys.argv.(i)
  done

let () =
  let vm = make_vm () in
  load_arguments vm;
  setup ();
  run vm
