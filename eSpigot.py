from time import time


def spigot_algorithm(digits):
    array_len = digits + 2
    array = [1] * array_len
    carry = 0
    curr_sum = 0
    e_digits = [2]

    for _ in range(digits):
        for j in reversed(range(array_len)):
            denom = j + 2
            curr_sum = array[j] * 10 + carry  # multiply by 10 and sum
            array[j] = curr_sum % denom  # mod
            carry = curr_sum // denom  # div

        # print(carry)
        e_digits.append(carry)

    return e_digits


if __name__ == '__main__':
    DIGITS = 1000

    t1 = time()
    e_digits = spigot_algorithm(DIGITS)
    t2 = time()

    print(f'{e_digits.pop(0)}.{"".join([str(d) for d in e_digits])}')
    print(f'\nCalculated {DIGITS} e digits in {t2 - t1} seconds')
