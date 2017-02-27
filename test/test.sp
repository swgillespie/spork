type asdf = int;
type thing = asdf;

struct point {
    x: int;
    y: int;
}

fun fibonacci(n: int) -> int {
    if (n == 0) {
        let x = 42 + n;
        let y = x;
        if (y == 99) {
            return 23;
        }

        return 12;
    }

    return 99;
}