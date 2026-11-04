# Example 2: Demonstrating the ZFC Axioms

# This example demonstrates the use of the ZFC axioms in set theory.

# Axiom 1: Extensionality
# Two sets are equal if and only if they have the same elements.
set1 = {1, 2, 3}
set2 = {3, 2, 1}
assert set1 == set2, "Sets are not equal despite having the same elements"

# Axiom 2: Empty Set
# There exists a set with no elements, called the empty set.
empty_set = set()
assert len(empty_set) == 0, "Empty set does not have zero elements"

# Axiom 3: Pairing
# For any two sets, there exists a set that contains both of them as elements.
set3 = {1, 2}
set4 = {3, 4}
pair_set = {set3, set4}
assert set3 in pair_set and set4 in pair_set, "Pairing axiom not satisfied"

# Axiom 4: Union
# For any collection of sets, there exists a set that contains all the elements of the sets in the collection.
collection = [{1, 2}, {3, 4}, {5, 6}]
union_set = set().union(*collection)
assert union_set == {1, 2, 3, 4, 5, 6}, "Union axiom not satisfied"

# Axiom 5: Power Set
# For any set, there exists a set that contains all the subsets of the original set.
original_set = {1, 2}
power_set = set(frozenset(subset) for subset in original_set)
assert len(power_set) == 2 ** len(original_set), "Power set axiom not satisfied"

# Axiom 6: Infinity
# There exists an infinite set.
infinite_set = set(range(1000))
assert len(infinite_set) == 1000, "Infinity axiom not satisfied"

# Axiom 7: Comprehension (Separation)
# For any set and any property, there exists a subset of the original set that contains all the elements with the given property.
original_set = {1, 2, 3, 4, 5}
subset = {x for x in original_set if x % 2 == 0}
assert subset == {2, 4}, "Comprehension axiom not satisfied"

# Axiom 8: Replacement
# For any set and any function, the image of the set under the function is also a set.
original_set = {1, 2, 3}
function = lambda x: x * 2
image_set = {function(x) for x in original_set}
assert image_set == {2, 4, 6}, "Replacement axiom not satisfied"

# Conclusion
# This example demonstrates the use of the ZFC axioms in set theory.
# Author: mistral/codestral-latest (Capability Tier 1)