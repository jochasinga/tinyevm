# toy-evm

A toy stack machine to play around with Ethereum bytecode.

## How it works 

**toy-evm** is a little stack machine that parses a limited set of Ethereum bytecode, convert them to the corresponding opcodes, and use a stack to do some computations.

The current version only supports `ADD`, `PUSH1`, `DUP2`, `SWAP1`, `POP`, and `SSTORE` opcodes.

## Example

The following bytecode

```
0x6001600101
```

Can be broken down to

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

## How to run

```rust
use stack::*;

fn main() {
    let result = lex_bytecode("0x6001600101").unwrap();
    let mut stack = eval_opcode(result);
    let (hd, tl) = stack.pop();
    assert_eq!(hd.unwrap(), 0x02);
    assert_eq!(*tl, Stack::EMPTY);
}
```
