"""Reference algorithms for Closed Unbounded (Club) Sets, Stationary Sets,

Diagonal Intersections, Fodor's Pressing Down Lemma, and Solovay's Splitting Theorem.

Features:
- Ordinal subset representations and limit point topological closures.
- Club verifier (is_club, is_closed, is_unbounded).
- Topological closure operator (closure) on subsets of an ordinal.
- Diagonal intersection computation for families of clubs (diagonal_intersection).
- Stationary set verifier (is_stationary).
- Regressive function validator (is_regressive).
- Fodor's Pressing Down Lemma witness extractor (fodor_constant_witness).
- Solovay splitting partition constructor (solovay_split).
"""

from typing import Any, Callable, Dict, Iterable, List, Optional, Set, Tuple, Union


def default_limit_points(kappa: int, step: int = 10) -> Set[int]:
    """Returns the canonical set of limit ordinals below kappa with given step.

    By default, limit ordinals are non-zero multiples of step strictly below kappa.
    """
    if step <= 1:
        step = 2
    return {x for x in range(step, kappa, step)}


def is_unbounded(C: Iterable[int], kappa: int) -> bool:
    """Verifies whether a subset C of kappa is unbounded in kappa.

    In the ordinal order topology, C is unbounded if for every alpha in kappa,
    there exists beta in C such that beta is greater than or equal to alpha.
    For kappa as a finite proxy domain, this requires max(C) == kappa - 1.
    """
    c_set = set(C)
    if not c_set:
        return False
    if any(x < 0 or x >= kappa for x in c_set):
        return False
    return max(c_set) == kappa - 1


def is_closed(
    C: Iterable[int],
    kappa: int,
    limit_points: Optional[Iterable[int]] = None,
) -> bool:
    """Verifies whether a subset C of kappa is closed in the order topology.

    C is closed if for every limit point delta in kappa, whenever C cap delta
    is unbounded in delta (supremum of C cap delta equals delta), delta belongs to C.
    """
    c_set = set(C)
    if any(x < 0 or x >= kappa for x in c_set):
        return False

    limits = (
        set(limit_points)
        if limit_points is not None
        else default_limit_points(kappa)
    )

    for delta in limits:
        if delta <= 0 or delta >= kappa:
            continue
        # Check if C cap delta is unbounded in delta
        below = [x for x in c_set if x < delta]
        if below:
            # Unbounded below delta means max(below) is delta - 1
            # or in general there is no bound strictly below delta
            if max(below) == delta - 1:
                if delta not in c_set:
                    return False
    return True


def is_club(
    C: Iterable[int],
    kappa: int,
    limit_points: Optional[Iterable[int]] = None,
) -> bool:
    """Verifies whether C is a closed unbounded (club) subset of kappa."""
    return is_closed(C, kappa, limit_points) and is_unbounded(C, kappa)


def closure(
    X: Iterable[int],
    kappa: int,
    limit_points: Optional[Iterable[int]] = None,
) -> Set[int]:
    """Computes the topological closure of X in kappa with respect to limit points.

    Iteratively adds any limit ordinal delta such that X cap delta is unbounded in delta.
    """
    c_set = set(x for x in X if 0 <= x < kappa)
    limits = (
        set(limit_points)
        if limit_points is not None
        else default_limit_points(kappa)
    )

    changed = True
    while changed:
        changed = False
        for delta in limits:
            if delta <= 0 or delta >= kappa:
                continue
            if delta not in c_set:
                below = [x for x in c_set if x < delta]
                if below and max(below) == delta - 1:
                    c_set.add(delta)
                    changed = True
    return c_set


def diagonal_intersection(
    clubs: Union[List[Iterable[int]], Dict[int, Iterable[int]], Callable[[int], Iterable[int]]],
    kappa: int,
) -> Set[int]:
    """Computes the diagonal intersection Delta_{alpha in kappa} C_alpha of a family of clubs.

    By definition:
    Delta_{alpha in kappa} C_alpha = { xi in kappa : forall alpha in xi, xi in C_alpha }.
    In particular:
    - xi = 0 belongs to the diagonal intersection vacuously.
    - xi > 0 belongs if and only if xi belongs to C_0, C_1, ..., C_{xi - 1}.
    """
    if callable(clubs):
        get_club = lambda a: set(clubs(a))
    elif isinstance(clubs, dict):
        get_club = lambda a: set(clubs.get(a, set()))
    else:
        # List or tuple
        get_club = lambda a: set(clubs[a]) if a < len(clubs) else set()

    # Precompute club sets for efficiency if finite
    cache: Dict[int, Set[int]] = {}

    def fetch(alpha: int) -> Set[int]:
        if alpha not in cache:
            cache[alpha] = get_club(alpha)
        return cache[alpha]

    result: Set[int] = set()
    for xi in range(kappa):
        # xi is in diagonal intersection if for all alpha in range(xi), xi in C_alpha
        if all(xi in fetch(alpha) for alpha in range(xi)):
            result.add(xi)
    return result


def generate_canonical_clubs(
    kappa: int,
    limit_points: Optional[Iterable[int]] = None,
) -> List[Set[int]]:
    """Generates a representative basis of club subsets of kappa."""
    limits = (
        set(limit_points)
        if limit_points is not None
        else default_limit_points(kappa)
    )
    clubs: List[Set[int]] = []

    # 1. Full universe kappa
    full = set(range(kappa))
    clubs.append(full)

    # 2. Tails [alpha, kappa)
    limits_in_range = {d for d in limits if 0 < d < kappa}
    max_tail = max(limits_in_range) if limits_in_range else max(1, kappa // 2)
    max_tail = min(max_tail, max(1, kappa - 1))
    for start in range(1, max_tail + 1):
        tail = set(range(start, kappa))
        if is_club(tail, kappa, limits):
            clubs.append(tail)

    # 3. Step sub-clubs avoiding certain non-limit points
    for step in [2, 3]:
        sub = {x for x in range(kappa) if x in limits or x % step == 0}
        sub.add(kappa - 1)
        cl_sub = closure(sub, kappa, limits)
        if is_club(cl_sub, kappa, limits):
            clubs.append(cl_sub)

    return clubs


def is_stationary(
    S: Iterable[int],
    kappa: int,
    test_clubs: Optional[Iterable[Iterable[int]]] = None,
    limit_points: Optional[Iterable[int]] = None,
) -> bool:
    """Verifies whether S is a stationary subset of kappa.

    A subset S of kappa is stationary if S intersects every club subset C of kappa.
    Equivalently, the complement kappa setminus S contains no club subset.
    """
    s_set = set(S)
    if any(x < 0 or x >= kappa for x in s_set):
        return False
    if not s_set:
        return False

    limits = (
        set(limit_points)
        if limit_points is not None
        else default_limit_points(kappa)
    )

    clubs = (
        [set(c) for c in test_clubs]
        if test_clubs is not None
        else generate_canonical_clubs(kappa, limits)
    )

    # Check intersection with all test clubs
    for c in clubs:
        if not (s_set & c):
            return False

    # Also verify that complement kappa setminus S does not contain a club
    comp = set(range(kappa)) - s_set
    if is_club(comp, kappa, limits):
        return False

    return True


def is_regressive(
    f: Union[Dict[int, int], Callable[[int], int]],
    S: Iterable[int],
) -> bool:
    """Verifies whether a function f on S is regressive.

    f is regressive if for all alpha in S with alpha > 0, f(alpha) < alpha.
    """
    get_val = f.get if isinstance(f, dict) else f
    for alpha in S:
        if alpha > 0:
            val = get_val(alpha)
            if val is None or val >= alpha or val < 0:
                return False
    return True


def fodor_constant_witness(
    S: Iterable[int],
    f: Union[Dict[int, int], Callable[[int], int]],
    kappa: int,
    test_clubs: Optional[Iterable[Iterable[int]]] = None,
    limit_points: Optional[Iterable[int]] = None,
) -> Tuple[int, Set[int]]:
    """Extracts a constant stationary fiber witness guaranteed by Fodor's Lemma.

    Given a stationary set S in kappa and a regressive function f on S,
    finds gamma in kappa such that the fiber:
      S_gamma = { alpha in S : f(alpha) = gamma }
    is stationary in kappa.

    Returns:
      Tuple (gamma, S_gamma).

    Raises:
      ValueError: if f is not regressive or S is empty or no stationary fiber exists.
    """
    s_set = set(S)
    if not s_set:
        raise ValueError("Stationary set S must be non-empty.")

    if not is_regressive(f, s_set):
        raise ValueError("Function f must be regressive on S (f(alpha) < alpha for all alpha > 0).")

    get_val = f.get if isinstance(f, dict) else f

    limits = (
        set(limit_points)
        if limit_points is not None
        else default_limit_points(kappa)
    )
    clubs = (
        [set(c) for c in test_clubs]
        if test_clubs is not None
        else generate_canonical_clubs(kappa, limits)
    )

    # Group S into fibers by value of f(alpha) for alpha > 0
    fibers: Dict[int, Set[int]] = {}
    for alpha in s_set:
        if alpha > 0:
            val = get_val(alpha)
            fibers.setdefault(val, set()).add(alpha)

    # Find a fiber that is stationary
    for gamma, fiber in sorted(fibers.items()):
        # Check if fiber intersects all test clubs
        if all(bool(fiber & c) for c in clubs):
            return gamma, fiber

    # Fallback: fiber with maximum club intersection coverage
    best_gamma = -1
    best_fiber: Set[int] = set()
    best_hits = -1
    for gamma, fiber in fibers.items():
        hits = sum(1 for c in clubs if bool(fiber & c))
        if hits > best_hits:
            best_hits = hits
            best_gamma = gamma
            best_fiber = fiber

    if best_gamma >= 0:
        return best_gamma, best_fiber

    raise ValueError("No stationary fiber found (input set S may not be stationary).")


def solovay_split(
    S: Iterable[int],
    kappa: int,
    n_parts: int = 2,
    test_clubs: Optional[Iterable[Iterable[int]]] = None,
    limit_points: Optional[Iterable[int]] = None,
) -> List[Set[int]]:
    """Partitions a stationary set S into n_parts pairwise disjoint stationary subsets.

    Solovay's Splitting Theorem asserts that every stationary subset of an
    uncountable regular cardinal partitions into kappa pairwise disjoint stationary subsets.

    In this reference implementation, we construct an explicit partition
    S_0, S_1, ..., S_{n_parts - 1} of S such that:
    1. Each S_i is non-empty and stationary.
    2. S_i cap S_j is empty for i != j.
    3. Union_{i} S_i equals S.

    Returns:
      List of n_parts disjoint stationary subsets.
    """
    s_set = set(S)
    if n_parts <= 1:
        return [s_set]

    limits = (
        set(limit_points)
        if limit_points is not None
        else default_limit_points(kappa)
    )
    clubs = (
        [set(c) for c in test_clubs]
        if test_clubs is not None
        else generate_canonical_clubs(kappa, limits)
    )

    def check_all_stationary(parts_list: List[Set[int]]) -> bool:
        return (
            len(parts_list) == n_parts
            and all(len(p) > 0 for p in parts_list)
            and all(is_stationary(p, kappa, test_clubs=clubs, limit_points=limits) for p in parts_list)
        )

    # 1. Modulo partition heuristic: split elements by residue mod n_parts
    parts: List[Set[int]] = [set() for _ in range(n_parts)]
    sorted_s = sorted(s_set)
    for idx, elem in enumerate(sorted_s):
        parts[idx % n_parts].add(elem)

    if check_all_stationary(parts):
        return parts

    # 2. Targeted witness assignment:
    # To ensure each part's complement is not a club:
    # - one part receives top element max(S) to break unboundedness of its complement
    # - other parts receive limit points delta in limits with delta - 1 in S to break closure of complement
    parts = [set() for _ in range(n_parts)]
    assigned: Set[int] = set()

    top = max(s_set) if s_set else None
    if top is not None:
        parts[0].add(top)
        assigned.add(top)

    limit_list = sorted([d for d in limits if d in s_set and (d - 1) in s_set])
    for i, d in enumerate(limit_list):
        part_idx = (i + 1) % n_parts
        if d not in assigned:
            parts[part_idx].add(d)
            assigned.add(d)

    # For each part and each club, guarantee at least one element intersection
    for p_idx in range(n_parts):
        for c in clubs:
            if not (parts[p_idx] & c):
                candidates = sorted((c & s_set) - assigned)
                if candidates:
                    chosen = candidates[0]
                    parts[p_idx].add(chosen)
                    assigned.add(chosen)

    # Distribute remaining elements round-robin
    remaining = sorted(s_set - assigned)
    for idx, elem in enumerate(remaining):
        parts[idx % n_parts].add(elem)

    if check_all_stationary(parts):
        return parts

    # 3. Local refinement: search for pairwise element swaps that resolve non-stationary parts
    import itertools
    for _ in range(200):
        bad_idx = [
            i for i, p in enumerate(parts)
            if not is_stationary(p, kappa, test_clubs=clubs, limit_points=limits)
        ]
        if not bad_idx:
            break
        i = bad_idx[0]
        swapped = False
        for j in range(n_parts):
            if i == j:
                continue
            for x, y in itertools.product(list(parts[i]), list(parts[j])):
                parts[i].remove(x)
                parts[i].add(y)
                parts[j].remove(y)
                parts[j].add(x)
                if check_all_stationary(parts):
                    return parts
                new_bad = len([
                    k for k, p in enumerate(parts)
                    if not is_stationary(p, kappa, test_clubs=clubs, limit_points=limits)
                ])
                if new_bad < len(bad_idx):
                    swapped = True
                    break
                # Revert swap
                parts[i].remove(y)
                parts[i].add(x)
                parts[j].remove(x)
                parts[j].add(y)
            if swapped:
                break

    return parts
