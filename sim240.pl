#!/usr/bin/perl

# Some global variables
my $version = "1.2";

# sim240.pl: Version 1.2
# Simulator for p18240
# Written by Paul Kennedy <pmkenned@andrew.cmu.edu>
# Last updated 4/5/2013
#
# Version 1.2 Notes
# * Fixed bug with run [n] where run n would execute n+1 instructions
# * Fixed parsing bug for ustep
# * Made state headings print before 'step' and 'ustep' output
# * Added 'exit' as a way to quit
#
# Version 1.1 Notes
# =============================================================================
# * Made the init_memory subroutine clear the entire memory
#
# Version 1.0 Notes
# =============================================================================
# Things TODO:
# * Get load() to work (load state from file)
# * Allow for printing out the entire condition code register at once
# * Get back feedback when doing ustep (e.g. printing the state)
# * Print the register file as a single line
#
# In progress:
# * Document code
# * Finish save() subroutine
#
# Done:
# * Use GetOptions for arguments such as version, verbose, etc.
# * Get labels working
# * Randomize memory
# * Allow for saving console output to file in addition to state
# * Allow for using .sim files for scripting
# * Add -r argument for simply running
#
# Things to consider doing:
# * Allow for piping as240 output into sim240?
# * When saving state with randomized memory, the file is huge since almost
#   all mem locations are non-zero. Consider keeping a record of changed
#   memory locations and only save those. Then memory state can be restored
#   by using the same seed, reading in the list file, and making the saved 
#   changes.
# * May want to not throw away the text from the list file.
#
# Known Bugs:
# If any additional bugs are found, please contact pmkenned@andrew.cmu.edu.

use strict;
use warnings;
use Getopt::Long;

# Global Variables

my $user; # holds user name from $USER environment var.
my $date; # holds date and time info

my $transcript; # holds transcript of every line printed
my $seed; # seed used for random memory

my $randomize_memory = 0; # flag that randomizes the memory
my $run_only = 0; # flag that just does "run, quit"


my $wide_header = "Cycle STATE PC   IR   SP   ZNCV MAR  MDR  R0   R1   R2   R3   R4   R5   R6   R7\n";

# print_per is a variable which determines when the simulator prints the state
# to the console.
# 'i' prints the state on every instruction. '
# 'u' prints the state on every microinstruction. '
# 'q' is for 'quiet'; it does not ever print
my $print_per = 'i'; # print on every instruction by default

my $cycle; # global cycle counter

# a hash of microinstruction binary opcodes
my %uinst_str_keys = (
# Microcode operations (i.e., FSM states)
   FETCH  => '00_0000_0000',
   FETCH1 => '00_0000_0001',
   FETCH2 => '00_0000_0010',
   DECODE => '00_0000_0100',
   STOP   => '00_1100_0000',
   STOP1  => '00_1100_0001',

# Load operations: MOV, LDA, LDR, LDI
   MOV    => '00_1110_1000',
   LDA    => '00_0001_0000',
   LDA1   => '00_0001_0001',
   LDA2   => '00_0001_0010',
   LDA3   => '00_0001_0011',
   LDA4   => '00_0001_0100',
   LDR    => '00_0010_0000',
   LDR1   => '00_0010_0001',
   LDR2   => '00_0010_0010',
   LDI    => '00_0011_0000',
   LDI1   => '00_0011_0001',
   LDI2   => '00_0011_0010',

# Store operations: STA, STR
   STA    => '00_0001_1000',
   STA1   => '00_0001_1001',
   STA2   => '00_0001_1010',
   STA3   => '00_0001_1011',
   STA4   => '00_0001_1100',
   STR    => '00_0010_1000',
   STR1   => '00_0010_1001',
   STR2   => '00_0010_1010',

# Branch operations: BRA, BRN, BRZ, BRC, BRV
   BRA    => '00_1010_0000',
   BRA1   => '00_1010_0001',
   BRA2   => '00_1010_0010',
   BRN    => '00_1011_0000',
   BRN1   => '00_1011_0001',
   BRN2   => '00_1011_0010',
   BRN3   => '00_1011_0011',
   BRZ    => '00_1010_1000',
   BRZ1   => '00_1010_1001',
   BRZ2   => '00_1010_1010',
   BRZ3   => '00_1010_1011',
   BRC    => '01_0010_0000',
   BRC1   => '01_0010_0001',
   BRC2   => '01_0010_0010',
   BRC3   => '01_0010_0011',
   BRV    => '00_1011_1000',
   BRV1   => '00_1011_1001',
   BRV2   => '00_1011_1010',
   BRV3   => '00_1011_1011',

# Arithmetic operations: ADD, SUB, INCR, DECR, NEG
   ADD    => '00_0011_1000',
   SUB    => '00_0100_0000',
   INCR   => '00_0101_0000',
   DECR   => '00_0101_1000',
   NEG    => '00_0100_1000',
   NEG1   => '00_0100_1001',
 
# Logical operations: AND, NOT, OR, XOR
   AND    => '00_0110_1000',
   NOT    => '00_0110_0000',
   OR     => '00_0111_0000',
   XOR    => '00_0111_1000',

# Comparison operations: CMI, CMR
   CMI    => '01_0001_0000',
   CMI1   => '01_0001_0001',
   CMI2   => '01_0001_0010',
   CMR    => '01_0001_1000',

# Shift operations: ASHR, LSHL, LSHR, ROL
   ASHR   => '00_1001_1000',
   LSHL   => '00_1000_0000',
   LSHR   => '00_1001_0000',
   ROL    => '00_1000_1000',

# Stack operations: JSR, LDSF, LDSP, POP, PUSH, RTN, STSF, STSP, ADDSP
   JSR    => '00_1101_1000',
   JSR1   => '00_1101_1001',
   JSR2   => '00_1101_1010',
   JSR3   => '00_1101_1011',
   JSR4   => '00_1101_1100',
   JSR5   => '00_1101_1101',
   LDSF   => '01_0000_0000',
   LDSF1  => '01_0000_0001',
   LDSF2  => '01_0000_0010',
   LDSF3  => '01_0000_0011',
   LDSF4  => '01_0000_0100',
   LDSP   => '00_1111_0000',
   POP    => '00_1101_0000',
   POP1   => '00_1101_0001',
   POP2   => '00_1101_0010',
   PUSH   => '00_1100_1000',
   PUSH1  => '00_1100_1001',
   PUSH2  => '00_1100_1010',
   RTN    => '00_1110_0000',
   RTN1   => '00_1110_0001',
   RTN2   => '00_1110_0010',
   STSF   => '01_0000_1000',
   STSF1  => '01_0000_1001',
   STSF2  => '01_0000_1010',
   STSF3  => '01_0000_1011',
   STSF4  => '01_0000_1100',
   STSP   => '00_1111_1000',
   ADDSP  => '00_0011_1100',
   ADDSP1 => '00_0011_1101',
   ADDSP2 => '00_0011_1110',

#   UNDEF  => xx_xxxx_xxxx # NOTE: needed?
);

# we need to do a reverse lookup of the bits in IR when figuring out
# what control state to go into when in the DECODE state
my %uinst_bin_keys = reverse %uinst_str_keys;

# hash: keys are addresses in canonical hex format (uppercase 4 digit)
my %memory = ();

# all the regs in the processor
my %state = (
    PC => '0000',
    SP => '0000',
    IR => '0000',
    MAR => '0000',
    MDR => '0000',
    regFile => ['0000',
                '0000',
                '0000',
                '0000',
                '0000',
                '0000',
                '0000',
                '0000'],
    Z => '0',
    N => '0',
    C => '0',
    V => '0',
    STATE => 'FETCH',
);

# keys are label strings, values are addresses
my %labels = ();

# keys are addresses, value is always 1
my %breakpoints = ();

# keys are strings indicating menu option
# values are regex's which match the input for the corresponding menu option
my %menu = (
    quit    => '^\s*(q(uit)?|exit)\s*$',
    help    => '^\s*(\?|h(elp)?)\s*$',                         # ? ; h ; help
    reset   => '^\s*reset\s*$',
    run     => '^\s*r(un)?\s*(\d*)?\s*([qiu])?\s*$',           # run ; run 5u ; r 6i
    step    => '^\s*s(tep)?$',                                 # s ; step
    ustep   => '^\s*u(step)?\s*$',                             # u ; ustep
    break   => '^\s*break\s+(\'?\w+\'?|[0-9a-f]{1,4})\s*$',    # break [addr/label]
    clear   => '^\s*clear\s+(\*|\'?\w+\'?|[0-9a-f]{1,4})\s*$', # clear [addr/label/*]
    lsbrk   => '^\s*lsbrk\s*$',
    load    => '^\s*load\s+([\w\.]+)\s*$',                     # load [file]
    save    => '^\s*save\s+([\w\.]+)\s*$',                     # save [file]
    set_reg => '^\s*(\*|pc|sp|ir|mar|mdr|z|c|v|n|r[0-7])\s*=\s*([0-9a-f]{1,4})$',
    get_reg => '^\s*(\*|pc|sp|ir|mar|mdr|z|c|v|n|state|r[0-7*])\s*\?$',
    set_mem => '^\s*m(em)?\[([0-9a-f]{1,4})\]\s*=\s*([0-9a-f]{1,4})$',   # m[10] = 0a10
    get_mem => '^\s*m(em)?\[([0-9a-f]{1,4})(:([0-9a-f]{1,4}))?\]\s*\?$', # m[50]? ; mem[10:20]?
    print   => '^\s*print\s*$',
);


# filehandles
my ($list_fh, $sim_fh);
my @list_lines;

main();

########################
# Main Subroutine 
########################

sub main {
    my $args = join(' ',@ARGV);

    my $get_version;

    GetOptions("seed=i"  => \$seed,
               "memory"  => \$randomize_memory,
               "run"     => \$run_only,
               "version" => \$get_version);

    if($get_version) {
        print "version: $version\n";
        exit;
    }

    $user = `echo \$USER`; # get user name
    $date = `date`;

    if(not defined $seed) {
        my @t = split(":",$date);
        $seed = $t[1] . substr($t[2],0,2);
    }

    tran("User: $user");
    tran("Date: $date");
    tran("Arguments: $args\n");
    tran("Seed: $seed\n\n");

    my $argc = $#ARGV+1;

    usage() if $argc < 1;


    my $list_filename = $ARGV[0];
    # sim file is optional (read input from STDIN if not specified)
    my $sim_filename = ($argc > 1) ? $ARGV[1] : undef;

    if(defined $sim_filename) {
        open($sim_fh, "<$sim_filename") or die $!;
    }
    else {
        $sim_fh = \*STDIN;
    }

    open ($list_fh,"<$list_filename") or die $!;

    @list_lines = <$list_fh>; # slurp file
    shift @list_lines; # remove 'addr data  label   opcode  operands'
    shift @list_lines; # remove '---- ----  -----   ------  --------'

	init();

    interface($sim_fh); # start taking input from user

    save_tran(); # save the transcript to a file

    close($sim_fh) if defined $sim_fh;
    close($list_fh);
}

sub init {

    get_labels();

    init_p18240(); # put p18240 into a known state
    init_memory(); # initialize the memory

}

sub usage {
    tran_print("./sim240 [list_file] [sim_file]\n");
    exit;
}

# Reads label from list file and adds them to the labels hash.
# Currently based on spacing format of list file.
sub get_labels {
    # check each line for a label
    foreach my $line (@list_lines) {
        next if(length($line) < 11); # must not be a label on this line
        my $addr = substr($line,0,4); # extract the address
        my $line_start_at_label = substr($line,11); # ignore addr and data
        my $end_of_label = index($line_start_at_label, ' '); # fine first space (end of label)
        my $label = substr($line_start_at_label,0,$end_of_label);
        $labels{$label} = $addr; # add this label to the labels hash
    }
}

# Interface Code
# Loop on user input executing commands until they quit
# Arguments:
#  * file handle for sim file.
# Return value:
#  * None
sub interface {
    my $input_fh = shift;

    my $done = 0; # flag indicating user is done and wants to quit

    if($run_only) {
        run();
        $done = 1;
    }

    until($done) {

        tran_print("> ");

        $_ = <$input_fh>;
        die "\$_ undefined. did you forget to quit? " unless(defined $_);
        chomp;

        # if we are taking input from STDIN, no need to print to STDOUT
        if($input_fh == \*STDIN) {
            tran($_ . "\n"); # just add to transcript
        # if we are taking input from a sim file, we should print to STDOUT
        } else {
            tran_print($_ . "\n");
        }


        # assume user input is valid until discovered not to be
        my $valid = 1;

        if(m/$menu{quit}/i) {
            $done = 1;
        } elsif(m/$menu{help}/i) {
            help();
        } elsif(m/$menu{reset}/i) {
            init();
        } elsif(m/$menu{run}/i) {
            run($2,$3);
        } elsif(m/$menu{step}/i) {
    		tran_print($wide_header) if $print_per eq 'i';
            step();
            print_state() if $print_per eq 'i';
        } elsif(m/$menu{ustep}/i) {
    		tran_print($wide_header) if $print_per eq 'u';
            cycle();
            print_state() if $print_per eq 'u';
        } elsif(m/$menu{break}/i) {
            set_breakpoint($1);
        } elsif(m/$menu{clear}/i) {
            clear_breakpoint($1);
        } elsif(m/$menu{lsbrk}/i) {
            list_breakpoints();
        } elsif(m/$menu{load}/i) {
            load($1);
        } elsif(m/$menu{save}/i) {
            save($1);
        } elsif(m/$menu{set_reg}/i) {
            set_reg($1,$2);
        } elsif(m/$menu{get_reg}/i) {
            get_reg($1);
        } elsif(m/$menu{set_mem}/i) {
            set_memory($2,$3);
        } elsif(m/$menu{get_mem}/i) {
            fget_memory({lo => $2, hi => $4});
        } elsif(m/$menu{print}/i) {
            print_tran_lpr();
        } elsif(m/^$/) { # user just struck enter
        } else {
            $valid = 0;
        }

        # User input did not match any regex
        unless($valid) {
            tran_print("Invalid input. Type 'help' for help.\n");
        }
    }
}

# help subroutine
# No arguments or return value. Just prints a help message.
sub help {
    my $help_msg = '';
    $help_msg .= "\n";
    $help_msg .= "quit,q,exit                Quit the simulator.\n";
    $help_msg .= "help,h,?                   Print this help message.\n";
    $help_msg .= "step,s                     Simulate one instruction.\n";
    $help_msg .= "ustep,u                    Simulate one micro-instruction.\n";
    $help_msg .= "run,r [n]                  Simulate the next n instructions.\n";
    $help_msg .= "break [addr/label]         Set a breakpoint for instruction located at [addr] or [label].\n";
    $help_msg .= "lsbrk                      List all of the breakpoints set.\n";
    $help_msg .= "clear [addr/label/*]       Clear a breakpoint set for [addr], [label], or clear all.\n";
    $help_msg .= "reset                      Reset the processor to initial state.\n";
    $help_msg .= "save [file]                Save the current state to a file.\n";
    $help_msg .= "load [file]                Load the state from a given file.\n";
    $help_msg .= "\n";
    $help_msg .= "You may set registers like so:          PC=100\n";
    $help_msg .= "You may view register contents like so: PC?\n";
    $help_msg .= "You may view the register file like so: R*?\n";
    $help_msg .= "You may view all registers like so:     *?\n";
    $help_msg .= "\n";
    $help_msg .= "You may set memory like so:  m[00A0]=100\n";
    $help_msg .= "You may view memory like so: m[00A0]? or with a range: m[0:A]?\n";
    $help_msg .= "\n";
    $help_msg .= "Note: All constants are interpreted as hexadecimal.\n";
    $help_msg .= "\n";
    tran_print($help_msg);
}

# Initialize the processor state
sub init_p18240 {

    $cycle = 0; # reset cycle counter

    foreach my $key (keys %state) {
        if($key eq 'regFile') {
            foreach my $index (0..7) {
                $state{regFile}->[$index] = '0000';
            }
        }
        elsif($key =~ /^[ZNCV]$/) {
            $state{$key} = '0';
        }
        elsif($key eq 'STATE') {
            $state{$key} = 'FETCH';
        }
        else {
            $state{$key} = '0000';
        }
    }
}

sub init_memory {

    %memory = (); # reset the memory

    if($randomize_memory) {
        srand($seed);

        for my $addr_dec (0 .. ((1<<16) - 1) ) {
            my $addr = sprintf("%.4x",$addr_dec);
            my $random = sprintf("%.4x",int(rand()*((1<<16)-1)));
            set_memory($addr,$random);
        }
    }

     # grab the address and data from each line and store in the memory hash
    foreach my $line (@list_lines) {
        my @arr = split(' ',$line);
        my $addr = $arr[0];
        my $data = $arr[1];
        $memory{$addr} = lc $data;
    }
}

# Run simulator for n instructions
# If n is undefined, run indefinitely
# In either case, the exception is to stop
# at breakpoints or the STOP microinstruction
sub run {
    my $num = (defined $_[0] and $_[0] ne '') ? $_[0] : (1<<32);

    my $print_per_tmp = $print_per;
    $print_per = $_[1] if (defined $_[1]);

    tran_print($wide_header) if $print_per ne 'q';

    STEP: foreach (1..$num) {
        step(); # simulate one instruction
        print_state() if $print_per eq 'i';
        last STEP if($state{STATE} eq 'STOP1');

        if(exists $breakpoints{$state{PC}}) {
            tran_print("Hit breakpoint at $state{PC}.\n");
            last STEP;
        }
    }

    $print_per = $print_per_tmp;
}

# Simulate one instruction
sub step {
    do {
        cycle();
        print_state() if $print_per eq 'u';
    } while($state{STATE} !~ /^(STOP1|FETCH)$/);
}

# Set a break point at a given address of label.
# Any thing which matches a hex value (e.g. a, 0B, etc) is interpreted
# as such *unless* it is surrounded by '' e.g. 'A' in which case it is
# interpreted as a label and looked up in the labels hash.
# Anything which does not match a hex value is also interpreted as a label
# with or without surrounding ''.
sub set_breakpoint {
    my $arg = shift;
    my ($addr,$label);
    my $is_label = 0;
    
    if($arg =~ /^'(\w+)'$/) { # 'label'
        $label = $1;
        $is_label = 1;
    } elsif($arg =~ /^[0-9a-f]{1,4}$/i) {
        $addr = to_4_digit_uc_hex($arg);
    } else {
        $is_label = 1;
        $label = $arg;
    }

    if($is_label) {
        if(exists $labels{$label}) {
            $addr = $labels{$label};
        }
        else {
            tran_print("Invalid label.\n");
            return;
        }
    }
    $breakpoints{$addr} = 1;
}

# Clear a break point. Use the same method as for setting breakpoints.
# An * can be used to clear all breakpoints.
sub clear_breakpoint {
    my $arg = shift;
    my ($addr,$label);
    my $all = 0;
    my $is_label = 0;
    
    if($arg =~ /^'(\w+)'$/) { # 'label'
        $label = $1;
        $is_label = 1;
    } elsif($arg =~ /^[0-9a-f]{1,4}$/i) {
        $addr = to_4_digit_uc_hex($arg);
    } elsif($arg eq '*') {
        $all = 1;
    } else {
        $label = $arg;
        $is_label = 1;
    }

    if($is_label) {
        if(exists $labels{$label}) {
            $addr = $labels{$label};
        }
        else {
            tran_print("Invalid label.\n");
            return;
        }
    }
 
    if($all) {
        %breakpoints = ();
    }
    else {
        if(exists $breakpoints{$addr}) {
            delete $breakpoints{$addr};
        }
        else { # no break point at that address
            if($is_label) {
                tran_print("No breakpoint at '$label'.\n");
            } else {
                tran_print("No breakpoint at $addr.\n");
            }
        }
    }
}

# Print out all of the breakpoints and the addresses.
sub list_breakpoints {
    tran_print(join("\n",keys %breakpoints) . "\n");
}

# TODO: load a state file
sub load {
    my $file = shift;
    tran_print("Feature not yet available.\n");
}

# TODO: finish this subroutine.
# Supposed to save all of the state to a file which can be
# restored using load.
sub save {
    my $file = shift;
    tran_print("saving to $file...\n");

    my $state_fh;
    open($state_fh, ">$file");

    print $state_fh "Seed: " . $seed . "\n";

    print $state_fh "Breakpoints:\n";
    print $state_fh join("\n",keys %breakpoints) . "\n\n";  

    print $state_fh "State:\n";
    print_state($state_fh);
    print $state_fh "\n";

    print $state_fh "Memory:\n";
    fget_memory({ fh => $state_fh,
                  lo => '0',
                  hi => 'ffff',
                  zeros => 0});

    close($state_fh);
}

# Set register subroutine.
sub set_reg {
    my $reg_name = uc $_[0];
    my $value = $_[1];

    if($reg_name =~ '^R([0-7])$') {
        $state{regFile}->[$1] = to_4_digit_uc_hex($value);
    }
    elsif($reg_name =~ /^[ZNCV]$/) {
        if($value =~ /^[01]$/) {
            $state{$reg_name} = $value;
        }
        else {
            tran_print("Value must be 0 or 1 for this register.\n");
        }
    }
    else {
        $state{$reg_name} = to_4_digit_uc_hex($value);
    }
}

sub get_reg {
    my $reg_name = uc $_[0];
    if($reg_name eq '*') {
        print_state();
    }
    elsif($reg_name eq 'R*') {
        fprint_regfile(\*STDOUT);
    }
    elsif($reg_name =~ /R([0-7])/) {
        tran_print("R$1: $state{regFile}->[$1]\n");
    }
    else {
        my $value = $state{$reg_name};
        tran_print("$reg_name: $value\n");
    }
}

sub print_state {
    my $fh = (defined $_[0]) ? $_[0] : \*STDOUT;
    my ($Z,$N,$C,$V) = ($state{Z}, $state{N}, $state{C}, $state{V});
    tran_print(sprintf("%0.4d ",$cycle), $fh);
    tran_print(' ' x (6-length($state{STATE})), $fh);
    tran_print("$state{STATE} $state{PC} $state{IR} $state{SP} $Z$N$C$V $state{MAR} $state{MDR} ", $fh);
    tran_print(join(' ', @{$state{regFile}}) . "\n", $fh);
}

# Consider removing. Could just be inlined.
sub fprint_regfile {
    my $fh = shift;

    my $even = 0;
    foreach my $index (0..7) {
        my $value = $state{regFile}->[$index];
        tran_print("R$index: $value", $fh);
        my $separator = $even ? "\n" : "\t";
        tran_print($separator, $fh);
        $even = ($even) ? 0 : 1;
    }
}

sub set_memory {
    my $addr = to_4_digit_uc_hex($_[0]);
    my $value = to_4_digit_uc_hex($_[1]);
    $memory{$addr} = $value;
}

sub fget_memory {
    my $args = shift;
    my $fh = $args->{fh};
    my $print_zeros = (exists $args->{zeros})? $args->{zeros} : 1;

    my $lo = hex $args->{lo};
    my $hi = (exists $args->{hi} and defined $args->{hi})? hex $args->{hi} : $lo;

    if($lo > $hi) {
        tran_print("Did you mean mem[$args->{lo}:$args->{hi}]?\n");
        return;
    }

    foreach my $addr_dec ($lo..$hi) {
        my $addr = uc sprintf("%.4x",$addr_dec);
        my $value = (exists $memory{$addr}) ? $memory{$addr} : '0000';
        unless($value eq '0000' and not $print_zeros) {
            my $value_no_regs = sprintf("%.4x",(hex $value)&0xffc0);
            my $state_str = hex_to_state($value_no_regs);
            my $rd = bs(hex $value,'5:3');
            my $rs = bs(hex $value,'2:0');
            tran_print("mem[$addr]: $value $state_str $rd $rs\n", $fh);
        }
    }
}

########################
# Simulator Code
########################

sub cycle {

    # Control Path ###
    my $cp_out = control();

    ### Start of ALU ###

    my $rf_selA = bs(hex $state{IR},'5:3');
    my $rf_selB = bs(hex $state{IR},'2:0');

    my $regA = $state{regFile}->[$rf_selA];
    my $regB = $state{regFile}->[$rf_selB];

    my $inA = mux({PC => $state{PC}, MDR => $state{MDR}, SP=> $state{SP}, REG => $regA}, $cp_out->{srcA});
    my $inB = mux({PC => $state{PC}, MDR => $state{MDR}, SP=> $state{SP}, REG => $regB}, $cp_out->{srcB});

    my $alu_in = {
        alu_op => $cp_out->{alu_op},
        inA => $inA,
        inB => $inB,
    };

    my $alu_out = alu($alu_in);

    ### End of ALU ###

    ### Memory ###

    my $mem_data = memory( {
        re => $cp_out->{re},
        we => $cp_out->{we},
        data => $state{MDR},
        addr => $state{MAR},
    });

    ### Sequential Logic ###

    my $dest = $cp_out->{dest};

    if($dest ne 'NONE') {
        if($dest eq 'REG') {
            $state{regFile}->[$rf_selA] = $alu_out->{alu_result};
        }
        else {
            $state{$dest} = $alu_out->{alu_result};
        }
    }

	# store memory output to MDR
    if($cp_out->{re} eq 'MEM_RD') {
        $state{MDR} = $mem_data;
    }

	# load condition codes
    if($cp_out->{load_CC} eq 'LOAD_CC') {
        foreach ('Z','N','C','V') {
            $state{$_} = $alu_out->{$_};
        }
    }

    $state{STATE} = $cp_out->{next_control_state};

    $cycle++; # increment cycle counter
}

BEGIN { # start of lexical block for control subroutine

my $IR_state;
my $BRN_next;
my $BRZ_next;
my $BRC_next;
my $BRV_next;

my %nextState_logic = (
    FETCH => ['F_A',        'PC',  'x',    'MAR',   'NO_LOAD',    'NO_RD',    'NO_WR',    'FETCH1'],
    FETCH1=> ['F_A_PLUS_1', 'PC',  'x',    'PC',    'NO_LOAD',    'MEM_RD',   'NO_WR',    'FETCH2'],
    FETCH2=> ['F_A',        'MDR', 'x',    'IR',    'NO_LOAD',    'NO_RD',    'NO_WR',    'DECODE'],
    DECODE=> ['x',          'x',   'x',    'NONE',  'NO_LOAD',    'NO_RD',    'NO_WR',    \$IR_state],
    LDI   => ['F_A',        'PC',  'x',    'MAR',   'NO_LOAD',    'NO_RD',    'NO_WR',    'LDI1'],
    LDI1  => ['F_A_PLUS_1', 'PC',  'x',    'PC',    'NO_LOAD',    'MEM_RD',   'NO_WR',    'LDI2'],
    LDI2  => ['F_A',        'MDR', 'x',    'REG',   'LOAD_CC',    'NO_RD',    'NO_WR',    'FETCH'],
    ADD   => ['F_A_PLUS_B', 'REG', 'REG',  'REG',   'LOAD_CC',    'NO_RD',    'NO_WR',    'FETCH'],
    SUB   => ['F_A_MINUS_B','REG', 'REG',  'REG',   'LOAD_CC',    'NO_RD',    'NO_WR',    'FETCH'],
    INCR  => ['F_A_PLUS_1', 'REG', 'x',    'REG',   'LOAD_CC',    'NO_RD',    'NO_WR',    'FETCH'],
    DECR  => ['F_A_MINUS_1','REG', 'x',    'REG',   'LOAD_CC',    'NO_RD',    'NO_WR',    'FETCH'],
    LDR   => ['F_B',        'x',   'REG',  'MAR',   'NO_LOAD',    'NO_RD',    'NO_WR',    'LDR1'],
    LDR1  => ['x',          'x',   'x',    'NONE',  'NO_LOAD',    'MEM_RD',   'NO_WR',    'LDR2'],
    LDR2  => ['F_A',        'MDR', 'x',    'REG',   'LOAD_CC',    'NO_RD',    'NO_WR',    'FETCH'],
    BRA   => ['F_A',        'PC',  'x',    'MAR',   'NO_LOAD',    'NO_RD',    'NO_WR',    'BRA1'],
    BRA1  => ['x',          'x',   'x',    'NONE',  'NO_LOAD',    'MEM_RD',   'NO_WR',    'BRA2'],
    BRA2  => ['F_A',        'MDR', 'x',    'PC',    'NO_LOAD',    'NO_RD',    'NO_WR',    'FETCH'],
    BRN   => ['F_A',        'PC',  'x',    'MAR',   'NO_LOAD',    'NO_RD',    'NO_WR',    \$BRN_next],
    BRN1  => ['F_A_PLUS_1', 'PC',  'x',    'PC',    'NO_LOAD',    'NO_RD',    'NO_WR',    'FETCH'],
    BRN2  => ['x',          'x',   'x',    'NONE',  'NO_LOAD',    'MEM_RD',   'NO_WR',    'BRN3'],
    BRN3  => ['F_A',        'MDR', 'x',    'PC',    'NO_LOAD',    'NO_RD',    'NO_WR',    'FETCH'],
    BRZ   => ['F_A',        'PC',  'x',    'MAR',   'NO_LOAD',    'NO_RD',    'NO_WR',    \$BRZ_next],
    BRZ1  => ['F_A_PLUS_1', 'PC',  'x',    'PC',    'NO_LOAD',    'NO_RD',    'NO_WR',    'FETCH'],
    BRZ2  => ['x',          'x',   'x',    'NONE',  'NO_LOAD',    'MEM_RD',   'NO_WR',    'BRZ3'],
    BRZ3  => ['F_A',        'MDR', 'x',    'PC',    'NO_LOAD',    'NO_RD',    'NO_WR',    'FETCH'],
    STOP  => ['F_A_MINUS_1','PC',  'x',    'PC',    'NO_LOAD',    'NO_RD',    'NO_WR',    'STOP1'],
    STOP1 => ['x',          'x',   'x',    'NONE',  'NO_LOAD',    'NO_RD',    'NO_WR',    'STOP1'], # same as above
    BRC   => ['F_A',        'PC',  'x',    'MAR',   'NO_LOAD',    'NO_RD',    'NO_WR',    \$BRC_next],
    BRC1  => ['F_A_PLUS_1', 'PC',  'x',    'PC',    'NO_LOAD',    'NO_RD',    'NO_WR',    'FETCH'],
    BRC2  => ['x',          'x',   'x',    'NONE',  'NO_LOAD',    'MEM_RD',   'NO_WR',    'BRC3'],
    BRC3  => ['F_A',        'MDR', 'x',    'PC',    'NO_LOAD',    'NO_RD',    'NO_WR',    'FETCH'],
    BRV   => ['F_A',        'PC',  'x',    'MAR',   'NO_LOAD',    'NO_RD',    'NO_WR',    \$BRV_next],
    BRV1  => ['F_A_PLUS_1', 'PC',  'x',    'PC',    'NO_LOAD',    'NO_RD',    'NO_WR',    'FETCH'],
    BRV2  => ['x',          'x',   'x',    'NONE',  'NO_LOAD',    'MEM_RD',   'NO_WR',    'BRV3'],
    BRV3  => ['F_A',        'MDR', 'x',    'PC',    'NO_LOAD',    'NO_RD',    'NO_WR',    'FETCH'],
    AND   => ['F_A_AND_B',  'REG', 'REG',  'REG',   'LOAD_CC',    'NO_RD',    'NO_WR',    'FETCH'],
    NOT   => ['F_A_NOT',    'REG', 'x',    'REG',   'LOAD_CC',    'NO_RD',    'NO_WR',    'FETCH'],
    OR    => ['F_A_OR_B',   'REG', 'REG',  'REG',   'LOAD_CC',    'NO_RD',    'NO_WR',    'FETCH'],
    XOR   => ['F_A_XOR_B',  'REG', 'REG',  'REG',   'LOAD_CC',    'NO_RD',    'NO_WR',    'FETCH'],
    CMI   => ['F_A',        'PC',  'x',    'MAR',   'NO_LOAD',    'NO_RD',    'NO_WR',    'CMI1'],
    CMI1  => ['F_A_PLUS_1', 'PC',  'x',    'PC',    'NO_LOAD',    'MEM_RD',   'NO_WR',    'CMI2'],
    CMI2  => ['F_A_MINUS_B','REG', 'MDR',  'NONE',  'LOAD_CC',    'NO_RD',    'NO_WR',    'FETCH'],
    CMR   => ['F_A_MINUS_B','REG', 'REG',  'NONE',  'LOAD_CC',    'NO_RD',    'NO_WR',    'FETCH'],
    ASHR  => ['F_A_ASHR',   'REG', 'x',    'REG',   'LOAD_CC',    'NO_RD',    'NO_WR',    'FETCH'],
    LSHL  => ['F_A_SHL',    'REG', 'x',    'REG',   'LOAD_CC',    'NO_RD',    'NO_WR',    'FETCH'],
    LSHR  => ['F_A_LSHR',   'REG', 'x',    'REG',   'LOAD_CC',    'NO_RD',    'NO_WR',    'FETCH'],
    ROL   => ['F_A_ROL',    'REG', 'x',    'REG',   'LOAD_CC',    'NO_RD',    'NO_WR',    'FETCH'],
    MOV   => ['F_B',        'x',   'REG',  'REG',   'NO_LOAD',    'NO_RD',    'NO_WR',    'FETCH'],
    LDA   => ['F_A',        'PC',  'x',    'MAR',   'NO_LOAD',    'NO_RD',    'NO_WR',    'LDA1'],
    LDA1  => ['F_A_PLUS_1', 'PC',  'x',    'PC',    'NO_LOAD',    'MEM_RD',   'NO_WR',    'LDA2'],
    LDA2  => ['F_A',        'MDR', 'x',    'MAR',   'NO_LOAD',    'NO_RD',    'NO_WR',    'LDA3'],
    LDA3  => ['x',          'x',   'x',    'NONE',  'NO_LOAD',    'MEM_RD',   'NO_WR',    'LDA4'],
    LDA4  => ['F_A',        'MDR', 'x',    'REG',   'LOAD_CC',    'NO_RD',    'NO_WR',    'FETCH'],
    STA   => ['F_A',        'PC',  'x',    'MAR',   'NO_LOAD',    'NO_RD',    'NO_WR',    'STA1'],
    STA1  => ['F_A_PLUS_1', 'PC',  'x',    'PC',    'NO_LOAD',    'MEM_RD',   'NO_WR',    'STA2'],
    STA2  => ['F_A',        'MDR', 'x',    'MAR',   'NO_LOAD',    'NO_RD',    'NO_WR',    'STA3'],
    STA3  => ['F_B',        'x',   'REG',  'MDR',   'NO_LOAD',    'NO_RD',    'NO_WR',    'STA4'],
    STA4  => ['x',          'x',   'x',    'NONE',  'NO_LOAD',    'NO_RD',    'MEM_WR',   'FETCH'],
    STR   => ['F_A',        'REG', 'x',    'MAR',   'NO_LOAD',    'NO_RD',    'NO_WR',    'STR1'],
    STR1  => ['F_B',        'x',   'REG',  'MDR',   'NO_LOAD',    'NO_RD',    'NO_WR',    'STR2'],
    STR2  => ['x',          'x',   'x',    'NONE',  'NO_LOAD',    'NO_RD',    'MEM_WR',   'FETCH'],
    JSR   => ['F_A_MINUS_1','SP',  'x',    'SP',    'NO_LOAD',    'NO_RD',    'NO_WR',    'JSR1'],
    JSR1  => ['F_A',        'SP',  'x',    'MAR',   'NO_LOAD',    'NO_RD',    'NO_WR',    'JSR2'],
    JSR2  => ['F_A_PLUS_1', 'PC',  'x',    'MDR',   'NO_LOAD',    'NO_RD',    'NO_WR',    'JSR3'],
    JSR3  => ['F_A',        'PC',  'x',    'MAR',   'NO_LOAD',    'NO_RD',    'MEM_WR',   'JSR4'],
    JSR4  => ['x',          'x',   'x',    'NONE',  'NO_LOAD',    'MEM_RD',   'NO_WR',    'JSR5'],
    JSR5  => ['F_A',        'MDR', 'x',    'PC',    'NO_LOAD',    'NO_RD',    'NO_WR',    'FETCH'],
    LDSF  => ['F_A',        'PC',  'x',    'MAR',   'NO_LOAD',    'NO_RD',    'NO_WR',    'LDSF1'],
    LDSF1 => ['F_A_PLUS_1', 'PC',  'x',    'PC',    'NO_LOAD',    'MEM_RD',   'NO_WR',    'LDSF2'],
    LDSF2 => ['F_A_PLUS_B', 'MDR', 'SP',   'MAR',   'NO_LOAD',    'NO_RD',    'NO_WR',    'LDSF3'],
    LDSF3 => ['x',          'x',   'x',    'NONE',  'NO_LOAD',    'MEM_RD',   'NO_WR',    'LDSF4'],
    LDSF4 => ['F_A',        'MDR', 'x',    'REG',   'NO_LOAD',    'NO_RD',    'NO_WR',    'FETCH'],
    LDSP  => ['F_A',        'REG', 'x',    'SP',    'NO_LOAD',    'NO_RD',    'NO_WR',    'FETCH'],
    POP   => ['F_A',        'SP',  'x',    'MAR',   'NO_LOAD',    'NO_RD',    'NO_WR',    'POP1'],
    POP1  => ['F_A_PLUS_1', 'SP',  'x',    'SP',    'NO_LOAD',    'MEM_RD',   'NO_WR',    'POP2'],
    POP2  => ['F_A',        'MDR', 'x',    'REG',   'NO_LOAD',    'NO_RD',    'NO_WR',    'FETCH'],
    PUSH  => ['F_A_MINUS_1','SP',  'x',    'MAR',   'NO_LOAD',    'NO_RD',    'NO_WR',    'PUSH1'],
    PUSH1 => ['F_A',        'REG', 'x',    'MDR',   'NO_LOAD',    'NO_RD',    'NO_WR',    'PUSH2'],
    PUSH2 => ['F_A_MINUS_1','SP',  'x',    'SP',    'NO_LOAD',    'NO_RD',    'MEM_WR',   'FETCH'],
    RTN   => ['F_A',        'SP',  'x',    'MAR',   'NO_LOAD',    'NO_RD',    'NO_WR',    'RTN1'],
    RTN1  => ['F_A_PLUS_1', 'SP',  'x',    'SP',    'NO_LOAD',    'MEM_RD',   'NO_WR',    'RTN2'],
    RTN2  => ['F_A',        'MDR', 'x',    'PC',    'NO_LOAD',    'NO_RD',    'NO_WR',    'FETCH'],
    STSF  => ['F_A',        'PC',  'x',    'MAR',   'NO_LOAD',    'NO_RD',    'NO_WR',    'STSF1'],
    STSF1 => ['F_A_PLUS_1', 'PC',  'x',    'PC',    'NO_LOAD',    'MEM_RD',   'NO_WR',    'STSF2'],
    STSF2 => ['F_A_PLUS_B', 'MDR', 'SP',   'MAR',   'NO_LOAD',    'NO_RD',    'NO_WR',    'STSF3'],
    STSF3 => ['F_A',        'REG', 'x',    'MDR',   'NO_LOAD',    'NO_RD',    'NO_WR',    'STSF4'],
    STSF4 => ['x',          'x',   'x',    'NONE',  'NO_LOAD',    'NO_RD',    'MEM_WR',   'FETCH'], # NOTE: bug exists is SV code. NO_LOAD exists twice. 
    ADDSP => ['F_A',        'PC',  'x',    'MAR',   'NO_LOAD',    'NO_RD',    'NO_WR',    'ADDSP1'],
    ADDSP1=> ['F_A_PLUS_1', 'PC',  'x',    'PC',    'NO_LOAD',    'MEM_RD',   'NO_WR',    'ADDSP2'],
    ADDSP2=> ['F_A_PLUS_B', 'MDR', 'SP',   'SP',    'NO_LOAD',    'NO_RD',    'NO_WR',    'FETCH'],
    STSP  => ['F_A',        'SP',  'x',    'REG',   'NO_LOAD',    'NO_RD',    'NO_WR',    'FETCH'],
    NEG   => ['F_A_NOT',    'REG', 'x',    'REG',   'NO_LOAD',    'NO_RD',    'NO_WR',    'NEG1'],
    NEG1  => ['F_A_PLUS_1', 'REG', 'x',    'REG',   'NO_LOAD',    'NO_RD',    'NO_WR',    'FETCH'],
);


sub control {

    my $curr_state = $state{STATE};
    $BRN_next = $state{N} ? 'BRN2' : 'BRN1';
    $BRZ_next = $state{Z} ? 'BRZ2' : 'BRZ1';
    $BRC_next = $state{C} ? 'BRC2' : 'BRC1';
    $BRV_next = $state{V} ? 'BRV2' : 'BRV1';

    $IR_state = hex_to_state($state{IR});

    my @output = @{$nextState_logic{$curr_state}};

    my $next_control_state = (ref $output[7] eq 'SCALAR') ? ${$output[7]} : $output[7];

    my $rv = {
        alu_op => $output[0],
        srcA => $output[1],
        srcB => $output[2],
        dest => $output[3],
        load_CC => $output[4],
        re => $output[5],
        we => $output[6],
        next_control_state => $next_control_state,
    };

    return $rv;
}

} # end of lexical block for control subroutine

sub alu {
    my $args = shift;

    my $opcode = $args->{alu_op};
    my $inA = hex $args->{inA};
    my $inB = hex $args->{inB};

    my $out;
    my $Z = 0;
    my $C = 0;
    my $N = 0;
    my $V = 0;

    if($opcode eq 'F_A') {
        $out = $inA;
    } elsif($opcode eq 'F_A_PLUS_1') {
        $out = bs($inA+1,'15:0');
        $C = bs($inA+1,16);
        $V = !bs($inA,15) & bs($out,15); # NOTE: fixed bug
    } elsif($opcode eq 'F_A_PLUS_B') {
        $out = bs($inA + $inB, '15:0');
        $C = bs($inA + $inB,'16');
        $V = (bs($inA,15) & bs($inB,15) & !bs($out,15)) | (!bs($inA,15) & !bs($inB,15) & bs($out,15));
    } elsif($opcode eq 'F_A_PLUS_B_1') {
        $C = bs($inA + $inB + 1,16);
        $out = bs($inA + $inB + 1,'15:0');
        $V = (bs($inA,15) & bs($inB,15) & !bs($out,15)) | (!bs($inA,15) & !bs($inB,15) & bs($out,15));
    } elsif($opcode eq 'F_A_MINUS_B_1') {
        $out = bs($inA - $inB - 1,'15:0');          # A-B-1 (set carry below)
        $C = (($inB + 1) >= $inA);
        $V = (bs($inA,15) & !bs($inB,15) & !bs($out,15)) | (!bs($inA,15) & bs($inB,15) & bs($out,15));
    } elsif($opcode eq 'F_A_MINUS_B') {
        $out = bs($inA - $inB,'15:0');              # A-B (set carry below)
        $C = ($inB >= $inA) ? 1 : 0;
        $V = (bs($inA,15) & !bs($inB,15) & !bs($out,15)) | (!bs($inA,15) & bs($inB,15) & bs($out,15));
    } elsif($opcode eq 'F_A_MINUS_1') {
        $out = bs($inA-1,'15:0');
        $C = bs($inA-1,16);
        $V = !bs($inA,15) & bs($out,15);
    } elsif($opcode eq 'F_B') {
        $out = $inB;                                # Pass B
    } elsif($opcode eq 'F_A_NOT') {
        $out = bs(~$inA,'15:0');                    # not A
    } elsif($opcode eq 'F_A_AND_B') {
        $out = $inA & $inB;                          # A and B
    } elsif($opcode eq 'F_A_OR_B') {
        $out = $inA | $inB;                          # A or B
    } elsif($opcode eq 'F_A_XOR_B') {
        $out = $inA ^ $inB;                          # A xor B
    } elsif($opcode eq 'F_A_SHL') {
        $C = bs($inA,'15');
        $out = bs($inA << 1,'15:0');
    } elsif($opcode eq 'F_A_ROL') {
        $out = (bs($inA,'14:0') << 1) + bs($inA,15);
        $C = bs($inA,15);
    } elsif($opcode eq 'F_A_LSHR') {
        $C = bs($inA,0);
        $out = '0' . bs($inA,'15:1');
    } elsif($opcode eq 'F_A_ASHR') {
        $C = bs($inA,0);
        $out = (bs($inA,15) << 15) + bs($inA,'15:1');
    } elsif ($opcode eq 'x') {
        $out = 0;
        $Z = $N = $C = $V = 0;
    } else {
        # TODO: probably should do something else like return 'x'
        die "error: invalid alu opcode $opcode\n";
    }

    $N = bs($out,15);
    $Z = ($out == 0) ? 1 : 0;

    my $rv = {
        alu_result => uc sprintf("%.4x",$out),
        Z => $Z,
        N => $N,
        C => $C,
        V => $V,
    };

    return $rv;
}

# Simulates a memory.
# Arguments are specified in a hash:
# If value for 're' key is 'MEM_RD', read from memory.
# If value for 'we' key is 'MEM_WR', write to memory.
# Reading and writing both use the value of the 'addr' key.
# Writing writes the value of the 'data_in' key.
# Return value:
# Returns the data stored at 'addr' when reading; 0000 otherwise.
sub memory {
    my $args = shift;
    my $re = $args->{re};
    my $we = $args->{we};
    my $data_in = $args->{data};
    my $addr = $args->{addr};

    my $data_out = '0000'; # data_in would mimic bus more accurately...

    if($re eq 'MEM_RD') {
        $data_out = $memory{$addr} if(exists $memory{$addr});
    }
    if($we eq 'MEM_WR') {
        $memory{$addr} = $data_in;
    }

    return $data_out;
}

# Simulates a multiplexor. The inputs to be selected among can be in a hash
# or an array.
sub mux {
    my $inputs = shift;
    my $sel = shift;

    if($sel eq 'x') {
        return '0';
    }

    if(ref $inputs eq 'ARRAY') {
        return $inputs->[$sel];
    } elsif (ref $inputs eq 'HASH') {
        return $inputs->{$sel};
    } else {
        die "error: mux subroutine: input was " . ref $inputs . " reference\n";
    }
}

########################
# Supporting Subroutines
########################

# Bitslice subroutine.
# First argument is a number, second argument is a string which indicates
# which bits you want to extract. This follows verilog format
# That is, '5' will extract bit 5, '5:2' will extract bits 5 to 2.
# The return value is shifted down so that the least significant selected
# bit moves down to the least significant position.
sub bs {
    my $bit_str = shift;
    my $indices = shift;

    if($indices =~ /(\d+):(\d+)/) {
        ($bit_str >> $2) & ((2<<($1-$2))-1);
    }
    elsif($indices =~ /(\d+)/) {
        ($bit_str >> $1) & 1;
    }
}

# Takes a hexadecimal number as input and outputs a canonical form
# The cacnonical form is a 4 digit uppercase hexadecimal number
# Input can be 1 to 4 digits with any case.
sub to_4_digit_uc_hex {
    return uc sprintf("%.4x", hex $_[0]);
}

# Takes a hexadecimal number in canonical form and outputs the
# string corresponding to that opcode.
sub hex_to_state {
    my $bin = unpack('B16',pack('H4',$_[0]));
    my @arr = split('',$bin);
    my $bin_key = join('',@arr[0,1]) . '_' . join('',@arr[2..5]) . '_' . join('',@arr[6..9]);
    my $state;
    if(exists $uinst_bin_keys{$bin_key}) {
        $state = $uinst_bin_keys{$bin_key};
    }
    else {
#        tran_print("Invalid binary code in IR: $bin_key\n");
        $state = 'FETCH';
    }
    return $state;
}

# add string to transcript
sub tran {
    $transcript .= $_[0];
}

# add the string to the transcript and print to file
# if no file is specified, default is STDOUT
sub tran_print {
    my $fh = (defined $_[1]) ? $_[1] : \*STDOUT;
    tran($_[0]);
    print $fh $_[0];
}

sub save_tran {
    my $tran_fh;
    open($tran_fh, ">transcript.txt") or die $!;
    print $tran_fh $transcript;
    close($tran_fh);
}

# print to physical paper using lpr
sub print_tran_lpr {
    my $tran_line_count = ($transcript =~ tr/\n//);
    if($tran_line_count > 200) {
        print "The transcript is $tran_line_count lines long. Are you sure you wish to print it all out? [y/n] ";
        my $answer = <STDIN>;
        return unless $answer eq 'y';
    }
    system("echo '$transcript' | lpr");
}
