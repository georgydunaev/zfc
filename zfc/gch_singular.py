"""Reference algorithms for the Generalized Continuum Hypothesis (GCH),

Hausdorff Formula, Bernstein Formula, Silver Theorem on Singular Cardinals,
and Easton Theorem on Regular Cardinals.

Features:
- Cardinal exponentiation evaluator under GCH and under arbitrary Easton models.
- Hausdorff formula evaluator: aleph_(alpha + 1)^aleph_beta = aleph_alpha^aleph_beta * aleph_(alpha + 1).
- Bernstein formula evaluator: aleph_n^aleph_beta = 2^aleph_beta * aleph_n.
- Silver singular cardinal power checker and consistency validator.
- Easton function validator (is_valid_easton_function) and forcing model simulator.
- Global cardinal power assignment consistency validator.
"""

from typing import Any, Callable, Dict, List, Optional, Tuple, Union

from zfc.cardinal_exponentiation import (
    Cardinal,
    aleph,
    cofinality,
    is_regular,
    is_singular,
)


def card_succ(c: Cardinal) -> Cardinal:
    """Computes the cardinal successor c^+ of a cardinal c."""
    if c.is_finite:
        assert c.value is not None
        return Cardinal(value=c.value + 1)
    if isinstance(c.aleph_index, int):
        return aleph(c.aleph_index + 1)
    return aleph(f"{c.aleph_index}+1")


def gch_power(kappa: Cardinal) -> Cardinal:
    """Computes 2^kappa under GCH: 2^kappa = kappa^+ for infinite kappa."""
    if kappa.is_finite:
        assert kappa.value is not None
        return Cardinal(value=2 ** kappa.value)
    return card_succ(kappa)


def gch_card_exp(kappa: Cardinal, lambda_: Cardinal) -> Cardinal:
    """Evaluates cardinal exponentiation kappa^lambda under the Generalized Continuum Hypothesis.

    Rules for infinite cardinals:
    1. If kappa <= lambda: kappa^lambda = 2^lambda = lambda^+.
    2. If lambda < cf(kappa): kappa^lambda = kappa.
    3. If cf(kappa) <= lambda < kappa: kappa^lambda = kappa^+.
    """
    # 0^0 = 1, kappa^0 = 1
    if lambda_.value == 0:
        return Cardinal(value=1)
    # 0^lambda = 0 for lambda > 0
    if kappa.value == 0:
        return Cardinal(value=0)
    # 1^lambda = 1
    if kappa.value == 1:
        return Cardinal(value=1)

    # Finite exponentiation
    if kappa.is_finite and lambda_.is_finite:
        assert kappa.value is not None and lambda_.value is not None
        return Cardinal(value=kappa.value ** lambda_.value)

    # Infinite base with finite exponent n >= 1
    if kappa.is_infinite and lambda_.is_finite:
        return kappa

    # Finite base >= 2 with infinite exponent
    if kappa.is_finite and lambda_.is_infinite:
        return card_succ(lambda_)

    # Both infinite
    if kappa <= lambda_:
        # kappa <= lambda implies kappa^lambda = 2^lambda = lambda^+
        return card_succ(lambda_)

    # lambda < kappa
    cf_k = cofinality(kappa)
    if lambda_ < cf_k:
        # lambda < cf(kappa) implies kappa^lambda = kappa
        return kappa
    # cf(kappa) <= lambda < kappa implies kappa^lambda = kappa^+
    return card_succ(kappa)


def hausdorff_formula_evaluate(alpha: int, beta: int) -> Tuple[Cardinal, Cardinal]:
    """Evaluates both sides of the Hausdorff formula under GCH:

    Left: aleph_(alpha + 1)^aleph_beta
    Right: aleph_alpha^aleph_beta * aleph_(alpha + 1)
    Returns: (left_value, right_value).
    """
    aleph_alpha = aleph(alpha)
    aleph_succ_alpha = aleph(alpha + 1)
    aleph_beta = aleph(beta)

    left = gch_card_exp(aleph_succ_alpha, aleph_beta)
    right_exp = gch_card_exp(aleph_alpha, aleph_beta)
    right = right_exp.card_prod(aleph_succ_alpha)
    return (left, right)


def bernstein_formula_evaluate(n: int, beta: int) -> Tuple[Cardinal, Cardinal]:
    """Evaluates both sides of the Bernstein formula for finite index n in omega:

    Left: aleph_n^aleph_beta
    Right: 2^aleph_beta * aleph_n
    Returns: (left_value, right_value).
    """
    aleph_n = aleph(n)
    aleph_beta = aleph(beta)

    left = gch_card_exp(aleph_n, aleph_beta)
    pow_beta = gch_power(aleph_beta)
    right = pow_beta.card_prod(aleph_n)
    return (left, right)


def is_valid_easton_function(
    f: Union[Dict[Cardinal, Cardinal], Callable[[Cardinal], Cardinal]],
    regular_cardinals: Optional[List[Cardinal]] = None,
) -> Tuple[bool, List[str]]:
    """Checks whether a function F on regular cardinals satisfies Easton conditions:

    1. Cantor bound: for all regular kappa, F(kappa) >= kappa^+.
    2. Monotonicity: for all regular kappa <= lambda, F(kappa) <= F(lambda).
    3. Konig condition: for all regular kappa, cf(F(kappa)) > kappa.

    Returns: (is_valid, list_of_error_descriptions).
    """
    if regular_cardinals is None:
        regular_cardinals = [aleph(0), aleph(1), aleph(2), aleph(3)]

    eval_f: Callable[[Cardinal], Cardinal]
    if isinstance(f, dict):
        eval_f = lambda c: f[c]
    else:
        eval_f = f

    errors: List[str] = []

    # Check each regular cardinal
    for kappa in regular_cardinals:
        if not is_regular(kappa):
            errors.append(f"Domain element {kappa} is not a regular cardinal")
            continue

        target = eval_f(kappa)

        # Condition 1: Cantor bound F(kappa) >= kappa^+
        succ_kappa = card_succ(kappa)
        if target < succ_kappa:
            errors.append(
                f"Cantor bound violated at {kappa}: F({kappa}) = {target} < {succ_kappa}"
            )

        # Condition 3: Konig condition cf(F(kappa)) > kappa
        cf_target = cofinality(target)
        if cf_target <= kappa:
            errors.append(
                f"Konig cofinality condition violated at {kappa}: cf(F({kappa})) = {cf_target} <= {kappa}"
            )

    # Condition 2: Monotonicity
    for i, kappa in enumerate(regular_cardinals):
        for lambda_ in regular_cardinals[i + 1 :]:
            if kappa <= lambda_:
                fk = eval_f(kappa)
                fl = eval_f(lambda_)
                if fk > fl:
                    errors.append(
                        f"Monotonicity violated: {kappa} <= {lambda_} but F({kappa}) = {fk} > F({lambda_}) = {fl}"
                    )

    return (len(errors) == 0, errors)


class EastonModel:
    """Simulator of an Easton forcing model for power values at regular cardinals."""

    def __init__(
        self,
        easton_assignment: Union[Dict[Cardinal, Cardinal], Callable[[Cardinal], Cardinal]],
        verified_cardinals: Optional[List[Cardinal]] = None,
    ):
        self.assignment = easton_assignment
        is_valid, errors = is_valid_easton_function(
            easton_assignment, regular_cardinals=verified_cardinals
        )
        if not is_valid:
            raise ValueError(f"Invalid Easton function assignment: {'; '.join(errors)}")

    def power(self, kappa: Cardinal) -> Cardinal:
        """Returns 2^kappa in this Easton model."""
        if kappa.is_finite:
            assert kappa.value is not None
            return Cardinal(value=2 ** kappa.value)

        if is_regular(kappa):
            if isinstance(self.assignment, dict):
                if kappa in self.assignment:
                    return self.assignment[kappa]
                return card_succ(kappa)
            return self.assignment(kappa)

        # Fallback for singular cardinal: minimal bound is kappa^+
        return card_succ(kappa)

    def exp(self, kappa: Cardinal, lambda_: Cardinal) -> Cardinal:
        """Evaluates kappa^lambda in the Easton model."""
        if lambda_.value == 0:
            return Cardinal(value=1)
        if kappa.value == 0:
            return Cardinal(value=0)
        if kappa.value == 1:
            return Cardinal(value=1)

        if kappa.is_finite and lambda_.is_finite:
            assert kappa.value is not None and lambda_.value is not None
            return Cardinal(value=kappa.value ** lambda_.value)

        if kappa.is_infinite and lambda_.is_finite:
            return kappa

        if kappa <= lambda_:
            # kappa <= lambda implies kappa^lambda = 2^lambda
            return self.power(lambda_)

        # lambda < kappa for regular kappa
        if is_regular(kappa):
            pow_lambda = self.power(lambda_)
            if pow_lambda <= kappa:
                return kappa
            return pow_lambda

        # Default singular evaluation
        return card_succ(kappa)


def check_silver_condition(
    lambda_card: Cardinal,
    gch_below: bool,
    power_at_lambda: Optional[Cardinal] = None,
) -> Dict[str, Any]:
    """Analyzes a singular cardinal lambda under Silver's Theorem.

    Silver's Theorem (1974):
    If lambda is a singular cardinal of uncountable cofinality (cf(lambda) > omega),
    and GCH holds for all cardinals below lambda,
    then GCH holds at lambda: 2^lambda = lambda^+.

    Countable cofinality contrast (Magidor):
    If cf(lambda) = omega (e.g. aleph_omega), Silver's theorem does not apply,
    and 2^lambda can be strictly greater than lambda^+ (e.g. aleph_(omega + 2)).
    """
    cf_lambda = cofinality(lambda_card)
    is_sing = is_singular(lambda_card)
    has_uncountable_cf = is_sing and cf_lambda > aleph(0)
    silver_applies = is_sing and has_uncountable_cf and gch_below

    consistent = True
    explanation = ""

    if silver_applies:
        expected = card_succ(lambda_card)
        if power_at_lambda is not None:
            if power_at_lambda != expected:
                consistent = False
                explanation = (
                    f"Inconsistent with Silver Theorem: lambda = {lambda_card} is singular with "
                    f"uncountable cofinality cf = {cf_lambda} and GCH below lambda, so 2^{lambda_card} "
                    f"must be {expected}, but given {power_at_lambda}."
                )
            else:
                explanation = (
                    f"Consistent with Silver Theorem: 2^{lambda_card} = {expected} as required."
                )
        else:
            explanation = (
                f"Silver Theorem applies: forces 2^{lambda_card} = {expected}."
            )
    else:
        if is_sing and not has_uncountable_cf:
            explanation = (
                f"Silver Theorem does not apply: lambda = {lambda_card} has countable cofinality "
                f"cf = {cf_lambda} (Magidor consistency: 2^{lambda_card} can exceed {card_succ(lambda_card)})."
            )
        elif not is_sing:
            explanation = (
                f"Silver Theorem does not apply: lambda = {lambda_card} is a regular cardinal."
            )
        else:
            explanation = (
                f"Silver Theorem does not apply: GCH does not hold everywhere below {lambda_card}."
            )

    return {
        "lambda": lambda_card,
        "is_singular": is_sing,
        "cofinality": cf_lambda,
        "has_uncountable_cofinality": has_uncountable_cf,
        "gch_below": gch_below,
        "silver_applies": silver_applies,
        "consistent": consistent,
        "explanation": explanation,
    }


def validate_cardinal_power_assignment(
    powers: Dict[Cardinal, Cardinal]
) -> Tuple[bool, List[str]]:
    """Validates a global cardinal power assignment 2^kappa against ZFC bounds and Silver Theorem:

    1. Cantor strict inequality: 2^kappa > kappa.
    2. Monotonicity: kappa <= lambda implies 2^kappa <= 2^lambda.
    3. Konig cofinality condition: cf(2^kappa) > kappa.
    4. Silver Singular Cardinal Theorem:
       For any singular lambda with cf(lambda) > aleph_0,
       if 2^xi = xi^+ for all xi < lambda, then 2^lambda = lambda^+.
    """
    errors: List[str] = []
    cardinals = sorted(powers.keys())

    # 1. Cantor & Konig bounds
    for kappa in cardinals:
        pow_k = powers[kappa]
        if pow_k <= kappa:
            errors.append(
                f"Cantor inequality violated: 2^{kappa} = {pow_k} <= {kappa}"
            )
        cf_pow = cofinality(pow_k)
        if cf_pow <= kappa:
            errors.append(
                f"Konig cofinality bound violated: cf(2^{kappa}) = {cf_pow} <= {kappa}"
            )

    # 2. Monotonicity
    for i, kappa in enumerate(cardinals):
        for lambda_ in cardinals[i + 1 :]:
            if kappa <= lambda_:
                pk = powers[kappa]
                pl = powers[lambda_]
                if pk > pl:
                    errors.append(
                        f"Monotonicity violated: {kappa} <= {lambda_} but 2^{kappa} = {pk} > 2^{lambda_} = {pl}"
                    )

    # 3. Silver's Theorem check
    for lambda_ in cardinals:
        if is_singular(lambda_) and cofinality(lambda_) > aleph(0):
            # Check if GCH holds below lambda in this assignment
            below = [c for c in cardinals if c < lambda_]
            gch_below = len(below) > 0 and all(powers[c] == card_succ(c) for c in below)
            res = check_silver_condition(
                lambda_card=lambda_,
                gch_below=gch_below,
                power_at_lambda=powers[lambda_],
            )
            if not res["consistent"]:
                errors.append(res["explanation"])

    return (len(errors) == 0, errors)
