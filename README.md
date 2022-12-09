# toy-evm

A toy stack machine to play around with Ethereum bytecode.

## How it works 

**toy-evm** is a little stack machine that parses a limited set of Ethereum bytecode, convert them to the corresponding opcodes, and use a stack to do some computations.

The current version supports `ADD`, `MUL`, `PUSH1`, `DUP2`, `SWAP1`, `POP`, and `SSTORE` opcodes.

## Example

The following bytecode `0x6001600101` is an equivalent of expression `1 + 1` in Solidity. Here is a breakdown:

| bytecode |  opcode |                  description                  |
|----------|---------|-----------------------------------------------|
|   0x60   |  PUSH1  | Push the next 1 byte of code onto the stack   |
|   0x01   |         | The 1-byte (64-bit) code to push              |
|   0x60   |  PUSH1  | Push the next 1 byte onto the stack           |
|   0x01   |         | The 1-byte code to push                       |
|   0x01   |   ADD   | Add the data on the stack and push the result |

The total is 32 bytes or 256-bit (word size).

```
PUSH1 0x01 -> [ 0x01,      ]
PUSH1 0x01 -> [ 0x01, 0x01 ]
ADD        -> [            ] -> 0x01 + 0x01
           -> [ 0x02       ]
```

Run this test case with `cargo test test_eval_add`.

To run the test on the bytecode `0x6002600202` (5 bytes) or `2 * 2`, run `cargo test test_eval_mul`.

To run test on the bytecode `0x6001600081905550` (8 bytes), run `cargo test test_eval_push1_dup2_swap1_sstore_pop`

## How to use as a library

```rust
use crate::evm::{lex_bytecode, eval_opcode};

fn main() {
    let result = lex_bytecode("0x6001600101").unwrap();
    let (mut stack, _storage) = eval_opcode(result);
    let (hd, tl) = stack.pop();
    assert_eq!(hd.unwrap(), 0x02);
    assert_eq!(*tl, Stack::EMPTY);
}
```
