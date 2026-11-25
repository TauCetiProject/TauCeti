/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.MonoidAlgebra.Twisted.NoZeroDivisors
public import TauCeti.GroupTheory.Amenable.Abelian
public import Mathlib.RingTheory.OreLocalization.OreSet

/-!
# The Ore condition for twisted group algebras of amenable groups

Let `k` be a commutative ring and `α` a factor set on a group `G`. If `G` has Følner sets and the
twisted group algebra `k_α[G]` has no zero divisors, then `k_α[G]` satisfies the left and the
right Ore conditions (`TauCeti.TwistedMonoidAlgebra.exists_mul_eq_mul_of_hasFoelnerSets` and
`TauCeti.TwistedMonoidAlgebra.exists_mul_eq_mul_of_hasFoelnerSets'`), so its submonoid of
non-zero-divisors, which consists of the nonzero elements when `k_α[G]` is nontrivial, is a left
Ore set (`TauCeti.TwistedMonoidAlgebra.oreSetNonZeroDivisors`). Every commutative group has
Følner sets, so for commutative `G` this is an instance, and when `k_α[G]` is moreover nontrivial,
Mathlib's `OreLocalization` of `k_α[G]` at its non-zero-divisors is a division ring. This
applies to the based quantum torus `TauCeti.QuantumTorus R L u Λ` of a torsion-free lattice `L`
over a domain `R`, which is a domain by the unique-product argument of
`TauCeti.Algebra.MonoidAlgebra.Twisted.NoZeroDivisors`: its Ore localization is its skew field of
fractions.

The argument is a dimension count over a nontrivial `k`. Multiplication of supports satisfies
`supp (f g) ⊆ supp f · supp g` (`TauCeti.TwistedMonoidAlgebra.support_repr_mul_subset`). If a
finite `S ⊆ G` satisfies `|S A| < 2 |S|` for `A = supp r ∪ supp s`, the `k`-linear map
`(x, y) ↦ x r - y s` from pairs supported in `S` (a free module of rank `2 |S|`) to elements
supported in `S A` (rank `|S A|`) has a nonzero kernel
(`TauCeti.TwistedMonoidAlgebra.exists_mul_eq_mul_of_card_lt`), and without zero divisors a kernel
element `(x, y)` has `x ≠ 0` once `s ≠ 0`. Følner sets provide such `S`
(`TauCeti.HasFoelnerSets.exists_card_mul_lt'`).

## References

* D. Tamari, *A refined classification of semi-groups leading to generalized polynomial rings with
  a generalized degree concept*, Proc. ICM 1954, vol. 3, 439–440.
* A. Berenstein and A. Zelevinsky, *Quantum cluster algebras*, Advances in Mathematics 195
  (2005), §4, for the skew field of fractions of a based quantum torus.
-/

public section

open Finset Module Submodule
open scoped Pointwise

namespace TauCeti.TwistedMonoidAlgebra

section Ring

variable {k G : Type*} [CommRing k] [Monoid G] {α : G → G → kˣ} [IsFactorSet α]

/-- Over a nontrivial `k`, if a linear map sends pairs from the span of `S` into the span of `T`
and `|T| < 2|S|`, it kills a nonzero pair from the span of `S`. -/
private theorem exists_ne_zero_map_eq_zero [Nontrivial k] {S T : Finset G}
    (φ : twistedMonoidAlgebra k G α × twistedMonoidAlgebra k G α →ₗ[k] twistedMonoidAlgebra k G α)
    (hφ : ∀ x ∈ span k (basis k G α '' S), ∀ y ∈ span k (basis k G α '' S),
      φ (x, y) ∈ span k (basis k G α '' T)) (hST : #T < 2 * #S) :
    ∃ x ∈ span k (basis k G α '' S), ∃ y ∈ span k (basis k G α '' S),
      (x, y) ≠ 0 ∧ φ (x, y) = 0 := by
  have hb (U : Finset G) : LinearIndependent k fun i : U ↦ basis k G α i :=
    (basis k G α).linearIndependent.comp _ Subtype.val_injective
  have hmem (U : Finset G) (c : U →₀ k) :
      Finsupp.linearCombination k (fun i : U ↦ basis k G α i) c ∈ span k (basis k G α '' U) := by
    rw [Set.image_eq_range, ← Finsupp.range_linearCombination]
    exact LinearMap.mem_range_self ..
  set e := fun U : Finset G ↦ Finsupp.linearCombination k (fun i : U ↦ basis k G α i)
  let ψ : (S →₀ k) × (S →₀ k) →ₗ[k] span k (basis k G α '' T) :=
    (φ ∘ₗ (e S).prodMap (e S)).codRestrict _ fun p ↦ hφ _ (hmem S p.1) _ (hmem S p.2)
  by_contra! h
  have hψ : Function.Injective ψ := by
    refine (injective_iff_map_eq_zero ψ).2 fun p hp ↦ ?_
    by_contra hp0
    refine h _ (hmem S p.1) _ (hmem S p.2) ?_ (congrArg Subtype.val hp)
    contrapose hp0
    simp only [Prod.mk_eq_zero] at hp0
    exact Prod.ext (linearIndependent_iff.1 (hb S) _ hp0.1) (linearIndependent_iff.1 (hb S) _ hp0.2)
  have : Module.Finite k (span k (basis k G α '' T)) :=
    Module.Finite.span_of_finite k (T.finite_toSet.image _)
  have hV : finrank k (span k (basis k G α '' T)) ≤ #T := by
    rw [Set.image_eq_range]
    exact (finrank_range_le_card _).trans (by simp)
  have := LinearMap.finrank_le_finrank_of_injective hψ
  rw [finrank_prod, finrank_finsupp_self, Fintype.card_coe] at this
  omega

/-- **Counting form of the left Ore condition.** Over a nontrivial `k`, if
`|S (supp f ∪ supp g)| < 2|S|` for a finite `S ⊆ G`, then `x f = y g` for some pair `(x, y) ≠ 0`. -/
theorem exists_mul_eq_mul_of_card_lt [Nontrivial k] [DecidableEq G]
    (f g : twistedMonoidAlgebra k G α) {S : Finset G}
    (hS : #(S * (((basis k G α).repr f).support ∪ ((basis k G α).repr g).support)) < 2 * #S) :
    ∃ x y : twistedMonoidAlgebra k G α, (x, y) ≠ 0 ∧ x * f = y * g := by
  set T := S * (((basis k G α).repr f).support ∪ ((basis k G α).repr g).support)
  have hmul {x : twistedMonoidAlgebra k G α} (hx : x ∈ span k (basis k G α '' S))
      (h : twistedMonoidAlgebra k G α) (hh : ((basis k G α).repr h).support ⊆
        ((basis k G α).repr f).support ∪ ((basis k G α).repr g).support) :
      x * h ∈ span k (basis k G α '' T) := by
    rw [(basis k G α).mem_span_image] at hx ⊢
    exact (coe_subset.2 (support_repr_mul_subset x h)).trans
      (coe_subset.2 (mul_subset_mul (coe_subset.1 hx) hh))
  obtain ⟨x, -, y, -, hxy, h⟩ := exists_ne_zero_map_eq_zero
    (LinearMap.mulRight k f ∘ₗ LinearMap.fst k _ _ - LinearMap.mulRight k g ∘ₗ LinearMap.snd k _ _)
    (fun x hx y hy ↦ sub_mem (hmul hx f subset_union_left) (hmul hy g subset_union_right)) hS
  exact ⟨x, y, hxy, sub_eq_zero.1 h⟩

/-- **Counting form of the right Ore condition.** Over a nontrivial `k`, if
`|(supp f ∪ supp g) S| < 2|S|` for a finite `S ⊆ G`, then `f x = g y` for some pair `(x, y) ≠ 0`. -/
theorem exists_mul_eq_mul_of_card_lt' [Nontrivial k] [DecidableEq G]
    (f g : twistedMonoidAlgebra k G α) {S : Finset G}
    (hS : #((((basis k G α).repr f).support ∪ ((basis k G α).repr g).support) * S) < 2 * #S) :
    ∃ x y : twistedMonoidAlgebra k G α, (x, y) ≠ 0 ∧ f * x = g * y := by
  set T := (((basis k G α).repr f).support ∪ ((basis k G α).repr g).support) * S
  have hmul {x : twistedMonoidAlgebra k G α} (hx : x ∈ span k (basis k G α '' S))
      (h : twistedMonoidAlgebra k G α) (hh : ((basis k G α).repr h).support ⊆
        ((basis k G α).repr f).support ∪ ((basis k G α).repr g).support) :
      h * x ∈ span k (basis k G α '' T) := by
    rw [(basis k G α).mem_span_image] at hx ⊢
    exact (coe_subset.2 (support_repr_mul_subset h x)).trans
      (coe_subset.2 (mul_subset_mul hh (coe_subset.1 hx)))
  obtain ⟨x, -, y, -, hxy, h⟩ := exists_ne_zero_map_eq_zero
    (LinearMap.mulLeft k f ∘ₗ LinearMap.fst k _ _ - LinearMap.mulLeft k g ∘ₗ LinearMap.snd k _ _)
    (fun x hx y hy ↦ sub_mem (hmul hx f subset_union_left) (hmul hy g subset_union_right)) hS
  exact ⟨x, y, hxy, sub_eq_zero.1 h⟩

end Ring

section Group

variable {k G : Type*} [CommRing k] [Group G] {α : G → G → kˣ} [IsFactorSet α]
  [NoZeroDivisors (twistedMonoidAlgebra k G α)]

/-- **Tamari's left Ore condition.** If `G` has Følner sets and `k_α[G]` has no zero divisors,
then for every `r` and every `s ≠ 0` there are `s' ≠ 0` and `r'` with `s' r = r' s`. -/
theorem exists_mul_eq_mul_of_hasFoelnerSets (hG : HasFoelnerSets G)
    (r : twistedMonoidAlgebra k G α) {s : twistedMonoidAlgebra k G α} (hs : s ≠ 0) :
    ∃ s' r' : twistedMonoidAlgebra k G α, s' ≠ 0 ∧ s' * r = r' * s := by
  classical
  have : Nontrivial (twistedMonoidAlgebra k G α) := ⟨⟨s, 0, hs⟩⟩
  have := Module.nontrivial k (twistedMonoidAlgebra k G α)
  obtain ⟨F, -, hF⟩ := HasFoelnerSets.exists_card_mul_lt' hG
    (((basis k G α).repr r).support ∪ ((basis k G α).repr s).support) one_pos
  obtain ⟨x, y, hxy, h⟩ := exists_mul_eq_mul_of_card_lt r s (S := F) (by
    rw [one_add_one_eq_two] at hF
    exact_mod_cast hF)
  refine ⟨x, y, fun hx ↦ hxy ?_, h⟩
  rw [hx, zero_mul, eq_comm, mul_eq_zero, or_iff_left hs] at h
  rw [hx, h, Prod.mk_zero_zero]

/-- **Tamari's right Ore condition.** If `G` has Følner sets and `k_α[G]` has no zero divisors,
then for every `r` and every `s ≠ 0` there are `s' ≠ 0` and `r'` with `r s' = s r'`. -/
theorem exists_mul_eq_mul_of_hasFoelnerSets' (hG : HasFoelnerSets G)
    (r : twistedMonoidAlgebra k G α) {s : twistedMonoidAlgebra k G α} (hs : s ≠ 0) :
    ∃ s' r' : twistedMonoidAlgebra k G α, s' ≠ 0 ∧ r * s' = s * r' := by
  classical
  have : Nontrivial (twistedMonoidAlgebra k G α) := ⟨⟨s, 0, hs⟩⟩
  have := Module.nontrivial k (twistedMonoidAlgebra k G α)
  obtain ⟨F, -, hF⟩ := HasFoelnerSets.exists_card_mul_lt hG
    (((basis k G α).repr r).support ∪ ((basis k G α).repr s).support) one_pos
  obtain ⟨x, y, hxy, h⟩ := exists_mul_eq_mul_of_card_lt' r s (S := F) (by
    rw [one_add_one_eq_two] at hF
    exact_mod_cast hF)
  refine ⟨x, y, fun hx ↦ hxy ?_, h⟩
  rw [hx, mul_zero, eq_comm, mul_eq_zero, or_iff_right hs] at h
  rw [hx, h, Prod.mk_zero_zero]

open nonZeroDivisors in
/-- The non-zero-divisors of a twisted group algebra without zero divisors over a group with
Følner sets form a left Ore set. When the algebra is nontrivial, these are its nonzero
elements. -/
@[instance_reducible]
noncomputable def oreSetNonZeroDivisors (hG : HasFoelnerSets G) :
    OreLocalization.OreSet (twistedMonoidAlgebra k G α)⁰ :=
  (OreLocalization.nonempty_oreSet_iff_of_noZeroDivisors.2 fun r s ↦ by
    cases subsingleton_or_nontrivial (twistedMonoidAlgebra k G α)
    · exact ⟨0, 1, Subsingleton.elim _ _⟩
    obtain ⟨s', r', hs', h⟩ :=
      exists_mul_eq_mul_of_hasFoelnerSets hG r (nonZeroDivisors.ne_zero s.property)
    exact ⟨r', ⟨s', mem_nonZeroDivisors_of_ne_zero hs'⟩, h⟩).some

end Group

section CommGroup

variable {k G : Type*} [CommRing k] [CommGroup G] {α : G → G → kˣ} [IsFactorSet α]
  [NoZeroDivisors (twistedMonoidAlgebra k G α)]

open nonZeroDivisors in
/-- The non-zero-divisors of a twisted group algebra of a commutative group without zero divisors
form a left Ore set. When the algebra is nontrivial, these are its nonzero elements and its Ore
localization at them is a division ring. -/
noncomputable instance : OreLocalization.OreSet (twistedMonoidAlgebra k G α)⁰ :=
  oreSetNonZeroDivisors (HasFoelnerSets.of_commGroup G)

end CommGroup

end TauCeti.TwistedMonoidAlgebra
