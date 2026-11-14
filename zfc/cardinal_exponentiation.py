"""Reference algorithms for ZFC cardinal exponentiation, Cantor theorem, and cofinality.

Includes:
- Finite set-theoretic model for functions, powersets, and exponentiation.
- Transfinite cardinal arithmetic (sum, product, exponentiation under AC/GCH).
- Cofinality determination and regularity/singularity classification.
- Konig theorem verification and diagonal witness extraction.
- Corollary verification: cf(2^kappa) > kappa.
"""

import itertools
from typing import Any, Callable, Dict, FrozenSet, List, Optional, Set, Tuple, Union


def vide() -> FrozenSet[Any]:
    """Empty set (0)."""
    return frozenset()


def sing(x: Any) -> FrozenSet[Any]:
    """Singleton set {x}."""
    return frozenset({x})


def paire(x: Any, y: Any) -> FrozenSet[Any]:
    """Unordered pair {x, y}."""
    return frozenset({x, y})


def von_neumann_ord(n: int) -> FrozenSet[Any]:
    """Von Neumann ordinal for non-negative integer n."""
    if n < 0:
        raise ValueError("Ordinal index must be non-negative")
    res = vide()
    for _ in range(n):
        res = res | frozenset({res})
    return res


def power(s: FrozenSet[Any]) -> FrozenSet[FrozenSet[Any]]:
    """Powerset P(s)."""
    elements = list(s)
    result: Set[FrozenSet[Any]] = set()
    for r in range(len(elements) + 1):
        for combo in itertools.combinations(elements, r):
            result.add(frozenset(combo))
    return frozenset(result)


def can_inject(s1: FrozenSet[Any], s2: FrozenSet[Any]) -> bool:
    """In finite model, |s1| <= |s2|."""
    return len(s1) <= len(s2)


def are_equipotent(s1: FrozenSet[Any], s2: FrozenSet[Any]) -> bool:
    """In finite model, |s1| == |s2|."""
    return len(s1) == len(s2)


def strictly_smaller(s1: FrozenSet[Any], s2: FrozenSet[Any]) -> bool:
    """Strict cardinal inequality |s1| < |s2|."""
    return can_inject(s1, s2) and not can_inject(s2, s1)


def card_sum_finite(s1: FrozenSet[Any], s2: FrozenSet[Any]) -> FrozenSet[Tuple[Any, int]]:
    """Disjoint sum (s1 * {0}) U (s2 * {1})."""
    left = {(x, 0) for x in s1}
    right = {(y, 1) for y in s2}
    return frozenset(left | right)


def card_prod_finite(s1: FrozenSet[Any], s2: FrozenSet[Any]) -> FrozenSet[Tuple[Any, Any]]:
    """Cartesian product s1 * s2."""
    return frozenset((x, y) for x in s1 for y in s2)


def finite_functions(b: FrozenSet[Any], a: FrozenSet[Any]) -> FrozenSet[FrozenSet[Tuple[Any, Any]]]:
    """Set of all functions from B to A, modeled as relation graphs."""
    b_list = list(b)
    a_list = list(a)
    if not b_list:
        # Exactly one function: empty set of pairs
        return frozenset({frozenset()})
    if not a_list:
        # No function can map non-empty B to empty A
        return frozenset()

    all_funcs: Set[FrozenSet[Tuple[Any, Any]]] = set()
    for choice in itertools.product(a_list, repeat=len(b_list)):
        graph = frozenset((b_elem, val) for b_elem, val in zip(b_list, choice))
        all_funcs.add(graph)
    return frozenset(all_funcs)


def cantor_diagonal_witness(
    x: FrozenSet[Any], f: Union[Dict[Any, FrozenSet[Any]], Callable[[Any], FrozenSet[Any]]]
) -> FrozenSet[Any]:
    """Constructs the diagonal set D = {a in x | a not in f(a)} witnessing non-surjectivity."""
    if isinstance(f, dict):
        mapping = f
        eval_fn = lambda a: mapping[a]
    else:
        eval_fn = f

    d_elements = set()
    for a in x:
        image_a = eval_fn(a)
        if a not in image_a:
            d_elements.add(a)
    return frozenset(d_elements)


class Cardinal:
    """Represents finite and transfinite cardinals under ZFC."""

    def __init__(self, value: Optional[int] = None, aleph_index: Optional[Any] = None):
        if value is not None and aleph_index is not None:
            raise ValueError("Specify either value (finite) or aleph_index (transfinite), not both")
        if value is not None:
            if value < 0:
                raise ValueError("Finite cardinal value must be non-negative")
            self.value: Optional[int] = value
            self.aleph_index: Optional[Any] = None
        elif aleph_index is not None:
            self.value = None
            self.aleph_index = aleph_index
        else:
            raise ValueError("Must specify value or aleph_index")

    @property
    def is_finite(self) -> bool:
        return self.value is not None

    @property
    def is_infinite(self) -> bool:
        return self.aleph_index is not None

    def __eq__(self, other: Any) -> bool:
        if not isinstance(other, Cardinal):
            if isinstance(other, int):
                other = Cardinal(value=other)
            else:
                return False
        if self.is_finite and other.is_finite:
            return self.value == other.value
        if self.is_infinite and other.is_infinite:
            return self.aleph_index == other.aleph_index
        return False

    def __lt__(self, other: Any) -> bool:
        if not isinstance(other, Cardinal):
            if isinstance(other, int):
                other = Cardinal(value=other)
            else:
                return NotImplemented
        if self.is_finite and other.is_infinite:
            return True
        if self.is_infinite and other.is_finite:
            return False
        if self.is_finite and other.is_finite:
            assert self.value is not None and other.value is not None
            return self.value < other.value
        # Both infinite: compare aleph indices
        # If both are integers/floats/strings
        assert self.aleph_index is not None and other.aleph_index is not None
        if isinstance(self.aleph_index, int) and isinstance(other.aleph_index, int):
            return self.aleph_index < other.aleph_index
        if isinstance(self.aleph_index, int) and isinstance(other.aleph_index, str):
            # omega > any finite integer index
            return True
        if isinstance(self.aleph_index, str) and isinstance(other.aleph_index, int):
            return False
        return str(self.aleph_index) < str(other.aleph_index)

    def __le__(self, other: Any) -> bool:
        return self == other or self < other

    def __gt__(self, other: Any) -> bool:
        return not (self <= other)

    def __ge__(self, other: Any) -> bool:
        return not (self < other)

    def __hash__(self) -> int:
        if self.is_finite:
            return hash(("finite", self.value))
        return hash(("infinite", self.aleph_index))

    def __repr__(self) -> str:
        if self.is_finite:
            return f"Card({self.value})"
        return f"Aleph_{self.aleph_index}"

    def card_sum(self, other: "Cardinal") -> "Cardinal":
        """Cardinal sum self + other."""
        if self.is_finite and other.is_finite:
            assert self.value is not None and other.value is not None
            return Cardinal(value=self.value + other.value)
        return max(self, other)

    def card_prod(self, other: "Cardinal") -> "Cardinal":
        """Cardinal product self * other."""
        if self.value == 0 or other.value == 0:
            return Cardinal(value=0)
        if self.is_finite and other.is_finite:
            assert self.value is not None and other.value is not None
            return Cardinal(value=self.value * other.value)
        return max(self, other)

    def card_exp(self, exponent: "Cardinal", gch: bool = True) -> "Cardinal":
        """Cardinal exponentiation self^exponent."""
        # 0^0 = 1, kappa^0 = 1
        if exponent.value == 0:
            return Cardinal(value=1)
        # 0^lambda = 0 for lambda > 0
        if self.value == 0:
            return Cardinal(value=0)
        # 1^lambda = 1
        if self.value == 1:
            return Cardinal(value=1)
        # Finite exponentiation
        if self.is_finite and exponent.is_finite:
            assert self.value is not None and exponent.value is not None
            return Cardinal(value=self.value ** exponent.value)

        # Transfinite exponentiation
        # Rule 1: For 2 <= kappa <= lambda with lambda infinite: kappa^lambda = 2^lambda
        if self <= exponent and exponent.is_infinite:
            if gch:
                if isinstance(exponent.aleph_index, int):
                    return Cardinal(aleph_index=exponent.aleph_index + 1)
                return Cardinal(aleph_index=f"{exponent.aleph_index}+1")
            return Cardinal(aleph_index=f"2^{exponent.aleph_index}")

        # Rule 2: kappa > lambda with lambda infinite
        if self.is_infinite and exponent.is_infinite:
            cf_self = cofinality(self)
            if cf_self > exponent:
                return self
            # if cf(kappa) <= lambda: kappa^lambda = kappa^{cf(kappa)} under GCH = 2^lambda if kappa <= 2^lambda
            if gch:
                if isinstance(self.aleph_index, int):
                    return Cardinal(aleph_index=self.aleph_index + 1)
                return Cardinal(aleph_index=f"{self.aleph_index}+1")
            return Cardinal(aleph_index=f"2^{exponent.aleph_index}")

        # kappa infinite, exponent finite n >= 1
        if self.is_infinite and exponent.is_finite:
            return self

        return Cardinal(aleph_index="unspecified")


def aleph(index: Any) -> Cardinal:
    """Helper to create transfinite cardinal aleph_index."""
    return Cardinal(aleph_index=index)


def cofinality(c: Cardinal) -> Cardinal:
    """Determines cofinality cf(alpha) for ordinals and cardinals."""
    if c.is_finite:
        assert c.value is not None
        if c.value == 0:
            return Cardinal(value=0)
        if c.value == 1:
            return Cardinal(value=1)
        # Any finite ordinal n >= 2 is a successor ordinal with cf(n) = 1
        return Cardinal(value=1)

    # aleph_0 is regular: cf(aleph_0) = aleph_0
    if c.aleph_index == 0:
        return Cardinal(aleph_index=0)

    # Successor cardinals aleph_{alpha + 1} are regular under AC: cf(aleph_{alpha+1}) = aleph_{alpha+1}
    if isinstance(c.aleph_index, int):
        # index > 0 is successor cardinal
        return c

    # Limit cardinal examples: aleph_omega has cf(aleph_omega) = aleph_0
    if c.aleph_index == "omega":
        return Cardinal(aleph_index=0)
    if c.aleph_index == "omega_1":
        return Cardinal(aleph_index=1)

    # General fallback for regular assumption
    return c


def is_regular(c: Cardinal) -> bool:
    """True if infinite cardinal satisfies cf(c) == c."""
    return c.is_infinite and cofinality(c) == c


def is_singular(c: Cardinal) -> bool:
    """True if infinite cardinal satisfies cf(c) < c."""
    return c.is_infinite and cofinality(c) < c


def konig_inequality_finite(kappas: List[int], lambdas: List[int]) -> bool:
    """Checks sum(kappa_i) < prod(lambda_i) given kappa_i < lambda_i."""
    if len(kappas) != len(lambdas):
        raise ValueError("kappas and lambdas must have identical lengths")
    for k, l in zip(kappas, lambdas):
        if k >= l:
            raise ValueError(f"Strict inequality violated: {k} not < {l}")

    k_sum = sum(kappas)
    l_prod = 1
    for l in lambdas:
        l_prod *= l

    return k_sum < l_prod


def konig_diagonal_witness(
    index_set: List[Any],
    kappas: Dict[Any, FrozenSet[Any]],
    lambdas: Dict[Any, FrozenSet[Any]],
    f: Callable[[Tuple[Any, Any]], Dict[Any, Any]],
) -> Dict[Any, Any]:
    """Constructively computes the diagonal tuple d in prod lambda_i not in Im(F).

    F is a candidate map from disjoint sum {(i, x) | i in I, x in kappa_i}
    into prod lambda_i (represented as functions/dicts from I to union(lambda_i)).
    """
    d: Dict[Any, Any] = {}
    for i in index_set:
        kappa_i = kappas[i]
        lambda_i = lambdas[i]
        # Collect i-th projections of F(i, x) for all x in kappa_i
        slice_i_values = set()
        for x in kappa_i:
            f_val = f((i, x))
            slice_i_values.add(f_val[i])

        # Since |slice_i_values| <= |kappa_i| < |lambda_i|, there must be an unused element
        unused = [elem for elem in lambda_i if elem not in slice_i_values]
        if not unused:
            raise RuntimeError(f"Hypothesis violated: kappa_{i} is not strictly smaller than lambda_{i}")
        d[i] = unused[0]

    return d


def check_cf_continuum_bound(kappa: Cardinal) -> bool:
    """Verifies that cf(2^kappa) > kappa.

    For kappa = aleph_0, cf(2^aleph_0) > aleph_0.
    In particular, 2^aleph_0 cannot be aleph_omega since cf(aleph_omega) = aleph_0.
    """
    two = Cardinal(value=2)
    two_to_kappa = two.card_exp(kappa, gch=False)
    # The theorem states cf(2^kappa) cannot be <= kappa
    # For aleph_0: cf(2^aleph_0) > aleph_0
    cf_power = cofinality(two_to_kappa)
    return cf_power > kappa
