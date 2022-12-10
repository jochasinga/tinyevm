# toy-evm

A toy stack machine to play around with Ethereum bytecode.

## How it works 

**toy-evm** is a little stack machine that parses a limited set of Ethereum bytecode, convert them to the corresponding opcodes, and use a stack to do some computations.

The stack has a word size of 32 bytes (256-bit) and a limit of 1024 items.

## Example

The following bytecode `0x6001600101` is an equivalent of expression `1 + 1` in Solidity. Here is a breakdown:

| bytecode |  opcode |                  description                  |
|----------|---------|-----------------------------------------------|
|   0x60   |  PUSH1  | Push the next byte of bytecode on the stack   |
|   0x01   |         | The bytecode to push                          |
|   0x60   |  PUSH1  | Push the next byte on the stack               |
|   0x01   |         | The bytecode to push                          |
|   0x01   |   ADD   | Pop the last and second last items, add them up, and push the result back on the stack |

```
PUSH1 0x01 =  [ 0x01      ] <-
PUSH1 0x01 =  [ 0x01 0x01 ] <-
ADD        =  [           ] -> 0x01 + 0x01
           =  [ 0x02      ] <-
```

## Running Tests

Run the above test case with `cargo test test_eval_add`.

To run the test on the bytecode `0x6002600202` (5 bytes) or `2 * 2`, run `cargo test test_eval_mul`.

To run test on the bytecode `0x6001600081905550` (8 bytes), run `cargo test test_eval_push1_dup2_swap1_sstore_pop`

## Supported Opcodes

| Opcode | bytecode |
|--------|----------|
| ADD    | 0x01     |
| MUL    | 0x02     |
| SUB    | 0x03     |
| ISZERO | 0x15     |
| POP    | 0x50     |
| MSTORE | 0x52     |
| SSTORE | 0x55     |
| PUSH1  | 0x60     |
| PUSH2  | 0x61     |
| DUP1   | 0x80     |
| DUP2   | 0x81     |
| SWAP1  | 0x90     |

See also: [evm-opcodes](https://github.com/crytic/evm-opcodes) and [ethervm.io](https://ethervm.io/)

## How to use as a library

The project isn't organized as a library yet, but here is what is being written as a test.

```rust
use crate::evm::{lex_bytecode, eval_opcode};

fn main() {
    let opcodes = lex_bytecode("0x6001600101").unwrap();
    let (mut stack, _storage, _memory) = eval_opcode(opcodes);
    let (last, rest) = stack.pop();
    assert_eq!(last.unwrap(), 0x02);
    assert_eq!(*rest, Stack::EMPTY);
}
```

We can also read raw opcodes from file generated with Solidity compiler `solc --opcodes -o tests`:

```rust

use crate::evm::Opcode;

fn main() {
    let opcodes = Opcode::from_file("tests/Example.opcode");
    let (mut stack, storage, memory) = eval_opcode(opcodes);
}

```
