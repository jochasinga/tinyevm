# tinyevm

A tiny stack machine for learning Ethereum bytecode (WIP).

I created **TinyEVM** as a mean to learn about Ethereum Virtual Machine. TinyEVM parses a piece of Ethereum bytecode compiled from smart contract languages like Solidity, convert them to the a vector of opcodes, and use the stack to do computations.

The stack has a word size of 32 bytes (256-bit) and a limit of 1024 items.

## Examples

## `ADD`

The following bytecode `0x6001600101` is equivalent to the following:

| bytecode |  opcode |                  description                  |
|----------|---------|-----------------------------------------------|
|   0x60   |  PUSH1  | Push the next byte of bytecode on the stack   |
|   0x01   |         | The bytecode to push                          |
|   0x60   |  PUSH1  | Push the next byte on the stack               |
|   0x01   |         | The bytecode to push                          |
|   0x01   |   ADD   | Pop the last and second last items, add them up, and push the result back on the stack |

```rust
use tinyevm::{
    lex_bytecode, eval_opcode, Stack,
    types::{to_uint256, Endian},
};

fn main() {
    let opcodes = lex_bytecode("0x6001600101").unwrap();
    let (mut stack, _storage, _memory) = eval_opcode(opcodes);
    let (last, rest) = stack.pop();

    // Check that the result is 2.
    assert_eq!(last.unwrap(), to_uint256(&[0x02], Endian::Little));

    // Check that the stack is now empty.
    assert_eq!(*rest, Stack::EMPTY);
}
```

### `MSTORE`

The bytecode `0x6060604052` can be translated as the following:

| bytecode |  opcode |                  description                  |
|----------|---------|-----------------------------------------------|
|   0x60   |  PUSH1  | Push the next byte of bytecode onto the stack |
|   0x60   |         | The bytecode to push (1 byte)                 |
|   0x60   |  PUSH1  | Push the next byte onto the stack             |
|   0x40   |         | The bytecode to push (1 byte)                 |
|   0x52   |  MSTORE | Pop 0x40 and 0x60 and store 0x60 at 0x40 location |

```rust
use tinyevm::{
    lex_bytecode, eval_opcode,
    types:UInt256,
};

fn main() {
    let result = lex_bytecode("0x6060604052").unwrap();
    let (mut stack, _, memory) = eval_opcode(result);
    let (last, _) = stack.pop();

    // Check that the stack is empty.
    assert!(last.is_none());

    // Load the memory at the 0x40 location.
    let value: UInt256 = memory.load(0x40_usize);
    let mut bytes = [0x00; 32];
    value.to_little_endian(&mut bytes);

    // Check that the value is 0x60.
    assert_eq!(bytes[0], 0x60);
}
```
### `PUSH2` and `PUSH3`

The bytecode `0x6101006201302f01` can be translated as the following:

| bytecode   |  opcode |                  description                     |
|------------|---------|--------------------------------------------------|
|   0x61     |  PUSH2  | Push the next 2 bytes of bytecode onto the stack |
|   0x0100   |         | The bytecode to push (2 bytes)                   |
|   0x62     |  PUSH3  | Push the next 3 bytes onto the stack             |
|   0x01302f |         | The bytecode to push (3 bytes)                   |
|   0x01     |  ADD    | Pop last two items, add them, and push the sum back onto the stack |

```rust
use tinyevm::{lex_bytecode, eval_opcode}

fn main() {
    let opcodes = lex_bytecode("0x6101006201302f01").unwrap();
    let (mut stack, _, _) = eval_opcode(opcodes);
    let (last, rest) = stack.pop();

    // Check that 0x01302f + 0x0100 is equal to 77871 + 256
    let expected = &format!("{:x}", 77871 + 256);
    assert_eq!(last.unwrap(), UInt256::from_str_radix(expected, 16).unwrap());

    // Check that the stack is now empty.
    assert_eq!(*rest, Stack::EMPTY);
}
```

## Tests

Run the above test case with `cargo test test_eval_add`.

To run the test on the bytecode `0x6002600202` (5 bytes) or `2 * 2`, run `cargo test test_eval_mul`.

To run test on the bytecode `0x6001600081905550` (8 bytes), run `cargo test test_eval_push1_dup2_swap1_sstore_pop`

## Opcodes

Here is a list of supported opcodes.

| Opcode | bytecode |
|--------|----------|
| ADD    | 0x01     |
| MUL    | 0x02     |
| SUB    | 0x03     |
| DIV    | 0x04     |
| ISZERO | 0x15     |
| POP    | 0x50     |
| MSTORE | 0x52     |
| SSTORE | 0x55     |
| PUSH1  | 0x60     |
| PUSH2  | 0x61     |
| PUSH3  | 0x61     |
| DUP1   | 0x80     |
| DUP2   | 0x81     |
| SWAP1  | 0x90     |

See also: [evm-opcodes](https://github.com/crytic/evm-opcodes) and [ethervm.io](https://ethervm.io/)

## Library

At the moment this is meant to be used as a Rust library. Here is an example of evaluating a simple piece of bytecode.

```rust
use tinyevm::{
    lex_bytecode, eval_opcode, Stack,
    types::{to_uint256, Endian},
};

fn main() {
    let opcodes = lex_bytecode("0x6001600101").unwrap();
    let (mut stack, _storage, _memory) = eval_opcode(opcodes);
    let (last, rest) = stack.pop();
    assert_eq!(last.unwrap(), to_uint256(&[0x02], Endian::Little));
    assert_eq!(*rest, Stack::EMPTY);
}
```

It is also possible to read opcode files generated with Solidity compiler `solc --opcodes -o tests`:

```rust
use tinyevm::Opcode;

fn main() {
    let opcodes = Opcode::from_file("tests/Example.opcode");
    let (_stack, _storage, _memory) = eval_opcode(opcodes);
}
```

## Notes

Because all opcodes are treated as [`Opcode(u8)`](./opcode.rs). Any chunk of bytecodes greater than a byte being pushed to the stack (i.e. with `PUSH2`, `PUSH3`, and so on) is chopped up byte-by-byte. For example, `PUSH3 0x2030ff` will be interpreted as a vector of following opcodes

```rust
vec![Opcode(0x61), Opcode(0x20), Opcode(0x30), Opcode(0xff)]
```

and reassembled during evaluation.