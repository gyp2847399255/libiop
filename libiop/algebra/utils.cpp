#include "libiop/algebra/utils.hpp"


namespace libiop {

std::size_t gcd(const std::size_t a, const std::size_t b)
{
    return b == 0 ? a : gcd(b, a % b);
}

}