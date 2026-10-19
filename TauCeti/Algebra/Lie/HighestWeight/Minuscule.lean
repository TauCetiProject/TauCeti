/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.HighestWeight.Character
public import TauCeti.Algebra.Lie.HighestWeight.FiniteDimensional
public import TauCeti.Algebra.Lie.HighestWeight.Trivial
import TauCeti.Algebra.Lie.Weights.InvariantForm

/-!
# Minuscule weights

Let `L` be a finite-dimensional Lie algebra with non-degenerate Killing form over an algebraically
closed field of characteristic zero, let `H` be a Cartan subalgebra and `b` a base of its root
system. A dominant integral weight `mu` is **minuscule** when every weight of the irreducible
module `L(mu)` lies in the Weyl orbit of `mu`; if `L(mu)` is nonzero its weights are then exactly
that orbit. This file defines `TauCeti.IsMinuscule` and proves the dimension count and the
coroot-pairing bounds that the orbit condition buys: a highest weight module whose weights lie in
one Weyl orbit has

`dim M = |W · lam|`,

the dimension being the size of a Weyl orbit, and every weight `χ` of such a module pairs with
every coroot `α^∨` in `{-1, 0, 1}` — a purely combinatorial and rank-one analysis, with no Weyl
character formula in sight.

## Why the orbit condition does all the work

Two facts about the formal character of `TauCeti/Algebra/Lie/Weights/FormalCharacter.lean` combine
to give the dimension count. Its coefficient at the highest weight of a highest weight module is `1`
(`TauCeti.formalCharacter_coeff_eq_one_of_isHighestWeightVector_of_lieSpan_eq_top`, the top weight
space being the line spanned by the generator); and it is Weyl-invariant
(`TauCeti.formalCharacter_coeff_weylGroup_smul`, the Weyl invariance of weight multiplicities,
proved from the rank-one theory and not from the character formula). So *every* weight in the orbit
of the highest weight already has multiplicity `1`, whatever the module
(`formalCharacter_coeff_weylGroup_smul_eq_one_of_isHighestWeightVector_of_lieSpan_eq_top`); the
orbit condition is exactly the statement that there are no other weights, and the dimension is
then the number of coefficients, all of them `1`.

For the coroot pairings, if a weight `χ` of a finite-dimensional module satisfies `χ(α^∨) = z ≥ 1`
for a root `α`, then `χ` cannot be a lowest weight in the `α` direction
(`TauCeti.exists_nat_neg_of_lie_coroot_eq_smul_of_forall_rootSpace_neg_lie_eq_zero`), so `χ - α` is
also a weight of the module (`TauCeti.genWeightSpace_sub_root_ne_bot_of_one_le`). When all weights
lie in a single Weyl orbit, `χ` and `χ - α` have the same squared length for the Weyl-invariant
form `TauCeti.invForm`, which forces `(z - 1) ⟨α, α⟩ = 0` and hence `z = 1`. Applying this to both
`α` and `-α` confines `χ(α^∨)` to `{-1, 0, 1}`.

Accordingly the substance of the file is stated for an arbitrary finite-dimensional module
whose weights lie in one orbit
(`TauCeti.finrank_eq_card_orbit_of_isHighestWeightVector_of_lieSpan_eq_top` and
`TauCeti.le_one_of_apply_coroot_eq_intCast_of_forall_mem_orbit`).

## The named carrier

`TauCeti.irreducibleQuotient` is built from the Verma module, and its canonical generator is a
highest weight vector of weight `mu` (`TauCeti.isHighestWeightVector_irreducibleQuotientGenerator`).
So at a minuscule weight the count and the coroot bounds apply to the named carrier:
`TauCeti.IsMinuscule.finrank_irreducibleQuotient_eq_card_orbit` gives `dim L(mu) = |W · mu|`,
`TauCeti.IsMinuscule.exists_int_abs_le_one_apply_coroot` bounds every weight of `L(mu)` on every
coroot by `1` in absolute value, and `TauCeti.IsMinuscule.apply_coroot_eq_zero_or_one` concludes
that `mu(α^∨) ∈ {0, 1}` for every positive root `α`.

At the zero weight the count is complete: `TauCeti.isMinuscule_zero` proves `0` minuscule, and
`TauCeti.finrank_irreducibleQuotient_zero`, which needs only triviality, agrees that
`dim L(0) = 1`.

## Main definitions

* `TauCeti.IsMinuscule`: `mu` is dominant integral and every weight of `L(mu)` is Weyl-conjugate to
  `mu`, with `TauCeti.isMinuscule_iff` its defining characterization.

## Main results

* `TauCeti.finrank_eq_card_orbit_of_isHighestWeightVector_of_lieSpan_eq_top`: **a highest weight
  module whose weights lie in one Weyl orbit has the dimension of that orbit**, the substance of
  the file. It rests on the fact that the orbit of the highest weight consists of weights, all of
  them simple
  (`formalCharacter_coeff_weylGroup_smul_eq_one_of_isHighestWeightVector_of_lieSpan_eq_top`), and
  hence that the orbit condition makes the weights exactly the orbit
  (`genWeightSpace_ne_bot_iff_mem_orbit_of_isHighestWeightVector_of_lieSpan_eq_top`).
* `TauCeti.le_one_of_apply_coroot_eq_intCast_of_forall_mem_orbit`: **every weight of a module
  supported on a single Weyl orbit pairs with every coroot to at most `1`.**
* `TauCeti.IsMinuscule.finrank_irreducibleQuotient_eq_card_orbit`: **`dim L(mu) = |W · mu|`**, the
  dimension count at the named carrier.
* `TauCeti.IsMinuscule.exists_int_abs_le_one_apply_coroot` and
  `TauCeti.IsMinuscule.apply_coroot_eq_zero_or_one`: **every weight of a minuscule module pairs with
  every coroot in `{-1, 0, 1}`, and a minuscule highest weight pairs with every positive coroot in
  `{0, 1}`.**
* `TauCeti.isMinuscule_zero`: **the zero weight is minuscule**, so the notion is not empty. It is
  unconditional, and the point orbit it exhibits matches the one-dimensionality of `L(0)` recorded
  by `TauCeti.finrank_irreducibleQuotient_zero`.

## Implementation notes

The Weyl group acts here as `(LieAlgebra.IsKilling.rootSystem H).weylGroup` acting on
`Module.Dual K H`, which is the action the invariance of weight multiplicities
(`TauCeti.formalCharacter_coeff_weylGroup_smul`) is stated for; the orbit is Mathlib's
`MulAction.orbit`, counted with `Nat.card`.

## References

* N. Bourbaki, *Groupes et algèbres de Lie*, Ch. VIII, §7.3, where minuscule weights are
  introduced.
* J. E. Humphreys, *Introduction to Lie Algebras and Representation Theory*, GTM 9, §13 and §21.2.
-/

public section

namespace TauCeti

open LieAlgebra LieModule Module

universe u v w

section General

variable {K : Type u} {L : Type v} [Field K] [CharZero K] [IsAlgClosed K]
  [LieRing L] [LieAlgebra K L] [IsKilling K L] [FiniteDimensional K L]
  {H : LieSubalgebra K L} [H.IsCartanSubalgebra]
  {M : Type w} [AddCommGroup M] [Module K M] [LieRingModule L M] [LieModule K L M]
  [FiniteDimensional K M]
  {b : (IsKilling.rootSystem H).Base} {lam : Dual K H} {v : M}

/-- **The weights of a highest weight module whose weights lie in one Weyl orbit are exactly that
orbit**: a linear form has a nonzero weight space in such a module precisely when it lies in the
Weyl orbit of the highest weight. -/
theorem genWeightSpace_ne_bot_iff_mem_orbit_of_isHighestWeightVector_of_lieSpan_eq_top
    (hv : IsHighestWeightVector b lam v) (hgen : LieSubmodule.lieSpan K L {v} = ⊤)
    (horb : ∀ chi : Dual K H, genWeightSpace M (chi : H → K) ≠ ⊥ →
      ∃ w : (IsKilling.rootSystem H).weylGroup, w • lam = chi)
    (chi : Dual K H) :
    genWeightSpace M (chi : H → K) ≠ ⊥ ↔
      chi ∈ MulAction.orbit (IsKilling.rootSystem H).weylGroup lam := by
  refine ⟨fun h ↦ MulAction.mem_orbit_iff.mpr (horb chi h), ?_⟩
  rintro ⟨w, rfl⟩
  exact genWeightSpace_weylGroup_smul_ne_bot_of_isHighestWeightVector_of_lieSpan_eq_top hv hgen w

/-- **A highest weight module whose weights lie in a single Weyl orbit has the dimension of that
orbit**: a finite-dimensional module generated by a highest weight vector of weight `lam`, all of
whose weights are Weyl-conjugate to `lam`, has dimension the cardinality of the Weyl orbit of
`lam`. This is the dimension count that minusculeness buys, stated before `TauCeti.IsMinuscule`
names the condition. -/
theorem finrank_eq_card_orbit_of_isHighestWeightVector_of_lieSpan_eq_top
    (hv : IsHighestWeightVector b lam v) (hgen : LieSubmodule.lieSpan K L {v} = ⊤)
    (horb : ∀ chi : Dual K H, genWeightSpace M (chi : H → K) ≠ ⊥ →
      ∃ w : (IsKilling.rootSystem H).weylGroup, w • lam = chi) :
    finrank K M = Nat.card (MulAction.orbit (IsKilling.rootSystem H).weylGroup lam) := by
  classical
  have hone : ∀ chi ∈ (formalCharacter K H M).coeff.support,
      (formalCharacter K H M).coeff chi = 1 := by
    intro chi hchi
    rw [Finsupp.mem_support_iff] at hchi
    obtain ⟨w, rfl⟩ := horb chi ((not_congr formalCharacter_coeff_eq_zero_iff).mp hchi)
    exact formalCharacter_coeff_weylGroup_smul_eq_one_of_isHighestWeightVector_of_lieSpan_eq_top
      hv hgen w
  have hsupp : (((formalCharacter K H M).coeff.support : Finset (Dual K H)) : Set (Dual K H)) =
      MulAction.orbit (IsKilling.rootSystem H).weylGroup lam := by
    ext chi
    rw [Finset.mem_coe, Finsupp.mem_support_iff,
      ← genWeightSpace_ne_bot_iff_mem_orbit_of_isHighestWeightVector_of_lieSpan_eq_top
        hv hgen horb chi]
    exact not_congr formalCharacter_coeff_eq_zero_iff
  have hsum := sum_formalCharacter_coeff_eq_finrank K H M
  rw [Finsupp.sum, Finset.sum_congr rfl hone, Finset.sum_const, nsmul_eq_mul, mul_one] at hsum
  have hcard : Nat.card (MulAction.orbit (IsKilling.rootSystem H).weylGroup lam) =
      (formalCharacter K H M).coeff.support.card := by
    rw [← hsupp, Nat.card_coe_set_eq, Set.ncard_coe_finset]
  rw [hcard]
  exact_mod_cast hsum.symm

attribute [local instance] Classical.propDecidable

/-- **The formal-character coefficient of a highest-weight module whose weights lie in one Weyl
orbit is the indicator of that orbit**: every Weyl translate of its highest weight occurs with
multiplicity one, and the orbit-support hypothesis excludes every other weight. -/
theorem formalCharacter_coeff_eq_ite_of_isHighestWeightVector_of_lieSpan_eq_top
    (hv : IsHighestWeightVector b lam v) (hgen : LieSubmodule.lieSpan K L {v} = ⊤)
    (horb : ∀ chi : Dual K H, genWeightSpace M (chi : H → K) ≠ ⊥ →
      ∃ w : (IsKilling.rootSystem H).weylGroup, w • lam = chi)
    (chi : Dual K H) :
    (formalCharacter K H M).coeff chi =
      if chi ∈ MulAction.orbit (IsKilling.rootSystem H).weylGroup lam then 1 else 0 := by
  classical
  have hsupp := genWeightSpace_ne_bot_iff_mem_orbit_of_isHighestWeightVector_of_lieSpan_eq_top
    hv hgen horb chi
  by_cases horb' : chi ∈ MulAction.orbit (IsKilling.rootSystem H).weylGroup lam
  · obtain ⟨w, rfl⟩ := horb'
    have hw : w • lam ∈ MulAction.orbit (IsKilling.rootSystem H).weylGroup lam :=
      ⟨w, rfl⟩
    simpa [hw] using
      formalCharacter_coeff_weylGroup_smul_eq_one_of_isHighestWeightVector_of_lieSpan_eq_top
        hv hgen w
  · have hbot : LieModule.genWeightSpace M (chi : H → K) = ⊥ := by
      by_contra hne
      exact horb' (hsupp.mp hne)
    simp [formalCharacter_coeff_eq_zero_iff.mpr hbot, horb']

/-- **Every weight of a module supported on a single Weyl orbit pairs with every coroot to at most
`1`.** If `chi` is a weight of `M` with `chi(αᵢ^∨) = z ≥ 1`, then `chi - αᵢ` is also a weight of
`M` by `TauCeti.genWeightSpace_sub_root_ne_bot_of_one_le`, so both `chi` and `chi - αᵢ` lie in the
Weyl orbit of `lam` and therefore have the same squared length under `TauCeti.invForm`; expanding
`⟨chi - αᵢ, chi - αᵢ⟩ = ⟨chi, chi⟩ + (1 - z) ⟨αᵢ, αᵢ⟩` then forces `z = 1`. -/
theorem le_one_of_apply_coroot_eq_intCast_of_forall_mem_orbit
    (horb : ∀ psi : Dual K H, genWeightSpace M (psi : H → K) ≠ ⊥ →
      ∃ w : (IsKilling.rootSystem H).weylGroup, w • lam = psi)
    {chi : Dual K H} (hchi : genWeightSpace M (chi : H → K) ≠ ⊥) {i : H.root} {z : ℤ}
    (hz : chi ((IsKilling.rootSystem H).coroot i) = (z : K)) :
    z ≤ 1 := by
  rcases le_or_gt z 0 with hz0 | hz0
  · omega
  have hz1 : 1 ≤ z := hz0
  have hsub := genWeightSpace_sub_root_ne_bot_of_one_le hchi hz hz1
  obtain ⟨w₁, hw₁⟩ := horb chi hchi
  obtain ⟨w₂, hw₂⟩ := horb (chi - (IsKilling.rootSystem H).root i) hsub
  set α : Dual K H := (IsKilling.rootSystem H).root i
  have hlen₁ : invForm chi chi = invForm lam lam := by
    rw [← hw₁]
    simpa only [rootInvariantForm_form] using
      (rootInvariantForm (H := H)).apply_weylGroup_smul (IsKilling.rootSystem H) w₁ lam lam
  have hlen₂ : invForm (chi - α) (chi - α) = invForm lam lam := by
    rw [← hw₂]
    simpa only [rootInvariantForm_form] using
      (rootInvariantForm (H := H)).apply_weylGroup_smul (IsKilling.rootSystem H) w₂ lam lam
  have hdiff : invForm chi chi - invForm (chi - α) (chi - α) =
      ((z : K) - 1) * invForm α α := by
    have hcor := invForm_coroot chi i
    rw [hz] at hcor
    simp only [map_sub, LinearMap.sub_apply]
    rw [(invForm_isSymm (H := H)).eq α chi]
    linear_combination -hcor
  have hα0 : invForm α α ≠ 0 := by
    simpa only [rootInvariantForm_form] using (rootInvariantForm (H := H)).ne_zero i
  rw [hlen₁, hlen₂, sub_self, eq_comm, mul_eq_zero] at hdiff
  rcases hdiff with h | h
  · have hcast : (z : K) = ((1 : ℤ) : K) := by push_cast; exact sub_eq_zero.mp h
    have := Int.cast_injective hcast
    omega
  · exact absurd h hα0

end General

section Minuscule

variable {K : Type u} {L : Type v} [Field K] [CharZero K] [IsAlgClosed K]
  [LieRing L] [LieAlgebra K L] [IsKilling K L] [FiniteDimensional K L]
  {H : LieSubalgebra K L} [H.IsCartanSubalgebra]

variable (b : (IsKilling.rootSystem H).Base) (mu : Dual K H)

/-- **A minuscule weight**: a dominant integral weight `mu` every companion weight of which in
`L(mu)` is Weyl-conjugate to it, so that the weights of a nonzero `L(mu)` are exactly one Weyl
orbit.

The condition is on the weights of `TauCeti.irreducibleQuotient`, so it holds vacuously at a
weight where that module vanishes; see the module docstring. -/
def IsMinuscule : Prop :=
  IsDominantIntegral b mu ∧
    ∀ nu : Dual K H, genWeightSpace (irreducibleQuotient b mu) (nu : H → K) ≠ ⊥ →
      ∃ w : (IsKilling.rootSystem H).weylGroup, w • mu = nu

variable {b mu}

/-- The defining condition on a minuscule weight, matching `TauCeti.isDominantIntegral_iff` beside
`TauCeti.IsDominantIntegral`. -/
theorem isMinuscule_iff :
    IsMinuscule b mu ↔ IsDominantIntegral b mu ∧
      ∀ nu : Dual K H, genWeightSpace (irreducibleQuotient b mu) (nu : H → K) ≠ ⊥ →
        ∃ w : (IsKilling.rootSystem H).weylGroup, w • mu = nu :=
  Iff.rfl

/-- A minuscule weight is dominant integral. -/
theorem IsMinuscule.isDominantIntegral (h : IsMinuscule b mu) : IsDominantIntegral b mu :=
  h.1

/-- Every weight of a minuscule `L(mu)` is Weyl-conjugate to `mu`. -/
theorem IsMinuscule.exists_weylGroup_smul_eq (h : IsMinuscule b mu) {nu : Dual K H}
    (hnu : genWeightSpace (irreducibleQuotient b mu) (nu : H → K) ≠ ⊥) :
    ∃ w : (IsKilling.rootSystem H).weylGroup, w • mu = nu :=
  h.2 nu hnu

attribute [local instance] Classical.propDecidable

/-- **The character of a minuscule module is the orbit indicator**: every Weyl translate of its
highest weight occurs with multiplicity one, and minuscule-ness excludes every other weight. -/
theorem formalCharacter_coeff_irreducibleQuotient_eq_ite_of_isMinuscule
    (h : IsMinuscule b mu) (chi : Dual K H) :
    letI := finiteDimensional_irreducibleQuotient_of_isDominantIntegral h.isDominantIntegral
    (formalCharacter K H (irreducibleQuotient b mu)).coeff chi =
      if chi ∈ MulAction.orbit (IsKilling.rootSystem H).weylGroup mu then 1 else 0 := by
  let _ := finiteDimensional_irreducibleQuotient_of_isDominantIntegral h.isDominantIntegral
  let hv := isHighestWeightVector_irreducibleQuotientGenerator b mu
  let hgen := lieSpan_irreducibleQuotientGenerator_eq_top b mu
  exact formalCharacter_coeff_eq_ite_of_isHighestWeightVector_of_lieSpan_eq_top hv hgen h.2 chi

/-- **The dimension of a minuscule module is the size of the Weyl orbit of its highest weight**,
`dim L(mu) = |W · mu|`. -/
theorem IsMinuscule.finrank_irreducibleQuotient_eq_card_orbit (h : IsMinuscule b mu) :
    finrank K (irreducibleQuotient b mu) =
      Nat.card (MulAction.orbit (IsKilling.rootSystem H).weylGroup mu) := by
  have _ := finiteDimensional_irreducibleQuotient_of_isDominantIntegral h.isDominantIntegral
  exact finrank_eq_card_orbit_of_isHighestWeightVector_of_lieSpan_eq_top
    (isHighestWeightVector_irreducibleQuotientGenerator b mu)
    (lieSpan_irreducibleQuotientGenerator_eq_top b mu) h.2

/-- **Every weight of a minuscule module pairs with every coroot to at most `1`.** -/
theorem IsMinuscule.le_one_of_apply_coroot_eq_intCast (h : IsMinuscule b mu) {nu : Dual K H}
    (hnu : genWeightSpace (irreducibleQuotient b mu) (nu : H → K) ≠ ⊥) {i : H.root} {z : ℤ}
    (hz : nu ((IsKilling.rootSystem H).coroot i) = (z : K)) :
    z ≤ 1 := by
  have _ := finiteDimensional_irreducibleQuotient_of_isDominantIntegral h.isDominantIntegral
  exact le_one_of_apply_coroot_eq_intCast_of_forall_mem_orbit h.2 hnu hz

/-- **Every weight of a minuscule module pairs with every coroot in `{-1, 0, 1}`.** Applying
`TauCeti.IsMinuscule.le_one_of_apply_coroot_eq_intCast` to both `i` and `-i` bounds the integer
value `nu(αᵢ^∨)` above by `1` and below by `-1`. -/
theorem IsMinuscule.exists_int_abs_le_one_apply_coroot (h : IsMinuscule b mu) {nu : Dual K H}
    (hnu : genWeightSpace (irreducibleQuotient b mu) (nu : H → K) ≠ ⊥) (i : H.root) :
    ∃ z : ℤ, (-1 ≤ z ∧ z ≤ 1) ∧ nu ((IsKilling.rootSystem H).coroot i) = (z : K) := by
  have _ := finiteDimensional_irreducibleQuotient_of_isDominantIntegral h.isDominantIntegral
  have hint := isIntegralWeight_of_formalCharacter_coeff_ne_zero
    ((not_congr formalCharacter_coeff_eq_zero_iff).mpr hnu)
  obtain ⟨z, hz⟩ := hint.exists_int_apply_coroot (i : Weight K H L)
  rw [← IsKilling.rootSystem_coroot_apply] at hz
  have hle : z ≤ 1 := h.le_one_of_apply_coroot_eq_intCast hnu hz
  have hneg : nu ((IsKilling.rootSystem H).coroot (-i)) = ((-z : ℤ) : K) := by
    rw [IsKilling.rootSystem_coroot_apply, IsKilling.val_neg_root, IsKilling.coroot_neg, map_neg,
      ← IsKilling.rootSystem_coroot_apply, hz, Int.cast_neg]
  have hge : -z ≤ 1 := h.le_one_of_apply_coroot_eq_intCast hnu hneg
  exact ⟨z, ⟨by omega, hle⟩, hz⟩

/-- **A minuscule weight takes only the values `0` and `1` on the positive coroots**
(Bourbaki, Ch. VIII, §7.3, Prop. 8): it takes a natural value on every positive coroot by dominance
(`TauCeti.IsDominantIntegral.exists_nat_apply_coroot`), and at most `1` because `mu` itself is a
weight of `L(mu)`. -/
theorem IsMinuscule.apply_coroot_eq_zero_or_one (h : IsMinuscule b mu) {i : H.root}
    (hi : i ∈ posRoots (IsKilling.rootSystem H) b) :
    mu ((IsKilling.rootSystem H).coroot i) = 0 ∨ mu ((IsKilling.rootSystem H).coroot i) = 1 := by
  obtain ⟨n, hn⟩ := h.isDominantIntegral.exists_nat_apply_coroot hi
  have hn' : mu ((IsKilling.rootSystem H).coroot i) = ((n : ℤ) : K) := by
    rw [hn, Int.cast_natCast]
  have hle : (n : ℤ) ≤ 1 := h.le_one_of_apply_coroot_eq_intCast
    (isHighestWeightVector_irreducibleQuotientGenerator b mu).genWeightSpace_ne_bot hn'
  rcases (by omega : n = 0 ∨ n = 1) with rfl | rfl
  · left; simpa using hn
  · right; simpa using hn

end Minuscule

section Zero

variable {K : Type u} {L : Type v} [Field K] [CharZero K] [IsAlgClosed K]
  [LieRing L] [LieAlgebra K L] [IsKilling K L] [FiniteDimensional K L]
  {H : LieSubalgebra K L} [H.IsCartanSubalgebra]

variable (b : (IsKilling.rootSystem H).Base)

/-- **The zero weight is minuscule.** Its module `L(0)` is the trivial one-dimensional module, so
its only weight is `0`, which is its own Weyl orbit. -/
@[simp]
theorem isMinuscule_zero : IsMinuscule b (0 : Dual K H) := by
  have hw := isHighestWeightVector_irreducibleQuotientGenerator b (0 : Dual K H)
  have _ := finiteDimensional_irreducibleQuotient_of_isDominantIntegral
    (isDominantIntegral_zero (b := b))
  have _ : LieModule.IsTrivial L (irreducibleQuotient b (0 : Dual K H)) :=
    isTrivial_of_isHighestWeightVector_weight_zero_of_lieSpan_eq_top hw
      (lieSpan_irreducibleQuotientGenerator_eq_top b 0)
  have _ : LieModule.IsTrivial H (irreducibleQuotient b (0 : Dual K H)) :=
    ⟨fun x m ↦ LieModule.IsTrivial.trivial (x : L) m⟩
  refine ⟨isDominantIntegral_zero, fun nu hnu ↦ ⟨1, ?_⟩⟩
  rw [one_smul, eq_comm]
  exact LinearMap.ext fun x ↦ congrFun (eq_zero_of_genWeightSpace_ne_bot_of_isTrivial hnu) x

end Zero

end TauCeti
