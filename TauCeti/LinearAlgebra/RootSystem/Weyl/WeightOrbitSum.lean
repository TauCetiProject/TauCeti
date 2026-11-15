/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.RootSystem.DominantCone
public import TauCeti.LinearAlgebra.RootSystem.Weyl.Invariant
import TauCeti.LinearAlgebra.RootSystem.Weyl.DominantIntegral

/-!
# Weyl orbit sums and the expansion of an invariant element

Let `P` be a root pairing with weight space `M` and a finite Weyl group. The **orbit sum** of a
weight `x` is the element `m_x = ∑_{y ∈ W x} e^y` of the integral group algebra `ℤ[M]`, each
*distinct* weight of the Weyl orbit of `x` occurring once, with no stabilizer multiplicity. Orbit
sums are the simplest Weyl-invariant elements, and this file shows that they are enough: a
Weyl-invariant element of `ℤ[M]` whose support lies below a weight `lam` and is integral on the
simple coroots is the combination

`f = ∑_{mu} f(mu) · m_mu`,

the sum running over the dominant integral weights `mu` below `lam`, which form a finite set. This
is the orbit-sum expansion of a formal character: applied to the character of the irreducible
module `L(lam)` it gives `ch L(lam) = m_lam + ∑_{mu < lam} c_mu m_mu`, unitriangular with respect
to the dominance order. That specialization is
`TauCeti.formalCharacter_eq_orbitSum_add_lower` in
`TauCeti/Algebra/Lie/HighestWeight/OrbitSum.lean`; nothing here needs a Lie algebra.

Dominance is the order-free condition that every simple coroot takes a natural value, so the
results apply over any characteristic-zero domain, in particular over the algebraically closed
field of a Lie algebra, which carries no ordering.

## The argument

The expansion compares coefficients at a weight `y`. Every term `f(mu) · m_mu` with `y` in the
orbit of `mu` contributes `f(mu) = f(y)`, by invariance. If `f(y) ≠ 0`, the support of `f` is a set
of weights below `lam`, integral on the simple coroots and stable under the simple reflections, so
`y` has a dominant Weyl translate inside it
(`TauCeti.exists_weylGroup_smul_dominant_of_forall_reflection_mem_of_sub_mem_posRootCone`); and a
Weyl orbit contains at most one dominant integral weight
(`TauCeti.weylGroup_smul_eq_self_of_dominantIntegral`). So exactly one term contributes, and it
contributes `f(y)`.

## Main definitions

* `RootPairing.weylWeightOrbit`: the finite set of the distinct weights in the Weyl orbit of a
  weight.
* `RootPairing.weightOrbitSum`: the orbit sum `m_x = ∑_{y ∈ W x} e^y`.

The finite set of the dominant integral weights below `lam` over which the expansion runs is
`RootPairing.dominantWeightsBelow`, from `TauCeti/LinearAlgebra/RootSystem/DominantCone.lean`.

## Main results

* `RootPairing.coeff_weightOrbitSum`: the coefficients of `m_x` are `1` on the orbit of `x` and `0`
  elsewhere, and `RootPairing.isWeylInvariant_weightOrbitSum`: `m_x` is Weyl-invariant.
* `RootPairing.isWeylInvariant_sum_single_smul`: the sum `∑_w e^{w x}` of all Weyl translates of
  `x`, counted with repetition, is Weyl-invariant.
* `TauCeti.IsWeylInvariant.eq_sum_coeff_smul_weightOrbitSum`: **a Weyl-invariant element supported
  below `lam` on integral weights is the combination of the orbit sums of the dominant integral
  weights below `lam`, with its own coefficients.**

## References

* J. E. Humphreys, *Introduction to Lie Algebras and Representation Theory*, GTM 9, §13.2 and
  §22.5.
* N. Bourbaki, *Lie Groups and Lie Algebras, Chapters 7-9*, Ch. VIII, §7.
-/

public section

universe u v w x

namespace RootPairing

open Finset TauCeti

variable {ι : Type u} {R : Type v} {M : Type w} {N : Type x}
  [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  (P : RootPairing ι R M N)

/-! ### Weyl orbits and orbit sums -/

section OrbitSum

variable [Finite P.weylGroup]

/-- The **Weyl orbit** of a weight `x`, as the finite set of its *distinct* Weyl translates `w • x`.
As a set it is Mathlib's `MulAction.orbit` (`RootPairing.coe_weylWeightOrbit`). -/
noncomputable def weylWeightOrbit (x : M) : Finset M :=
  (Set.finite_range fun w : P.weylGroup ↦ w • x).toFinset

/-- The **orbit sum** `m_x = ∑_{y ∈ W x} e^y` of a weight `x` in the integral group algebra
`ℤ[M]`: every distinct weight of the Weyl orbit of `x` occurs once, with coefficient `1`. -/
noncomputable def weightOrbitSum (x : M) : AddMonoidAlgebra ℤ M :=
  ∑ y ∈ P.weylWeightOrbit x, AddMonoidAlgebra.single y 1

variable {P}

/-- A weight lies in the Weyl orbit of `x` exactly when it is a Weyl translate of `x`. -/
@[simp]
theorem mem_weylWeightOrbit {x y : M} :
    y ∈ P.weylWeightOrbit x ↔ ∃ w : P.weylGroup, w • x = y := by
  simp [weylWeightOrbit]

/-- The Weyl orbit of `x`, as a set, is the orbit of `x` under the action of the Weyl group. -/
@[simp, norm_cast]
theorem coe_weylWeightOrbit (x : M) :
    (P.weylWeightOrbit x : Set M) = MulAction.orbit P.weylGroup x := by
  ext y
  simp [MulAction.mem_orbit_iff]

/-- Every Weyl translate of `x` lies in the Weyl orbit of `x`. -/
theorem smul_mem_weylWeightOrbit (w : P.weylGroup) (x : M) : w • x ∈ P.weylWeightOrbit x :=
  mem_weylWeightOrbit.mpr ⟨w, rfl⟩

/-- A weight lies in its own Weyl orbit. -/
theorem self_mem_weylWeightOrbit (x : M) : x ∈ P.weylWeightOrbit x :=
  mem_weylWeightOrbit.mpr ⟨1, one_smul _ x⟩

/-- Weyl-conjugate weights have the same Weyl orbit. -/
@[simp]
theorem weylWeightOrbit_smul (w : P.weylGroup) (x : M) :
    P.weylWeightOrbit (w • x) = P.weylWeightOrbit x := by
  exact Finset.coe_injective (by simp only [coe_weylWeightOrbit, MulAction.orbit_smul])

/-- The Weyl orbit of a weight is the Weyl orbit of any of its members. -/
theorem weylWeightOrbit_eq_of_mem {x y : M} (h : y ∈ P.weylWeightOrbit x) :
    P.weylWeightOrbit y = P.weylWeightOrbit x := by
  apply Finset.coe_injective
  rw [coe_weylWeightOrbit, coe_weylWeightOrbit]
  exact MulAction.orbit_eq_iff.mpr (by
    simpa only [← coe_weylWeightOrbit, Finset.mem_coe] using h)

/-- A Weyl translate of `y` lies in the Weyl orbit of `x` exactly when `y` does. -/
theorem smul_mem_weylWeightOrbit_iff {x y : M} (w : P.weylGroup) :
    w • y ∈ P.weylWeightOrbit x ↔ y ∈ P.weylWeightOrbit x := by
  simp only [← Finset.mem_coe, coe_weylWeightOrbit]
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · simpa only [inv_smul_smul] using MulAction.mem_orbit_of_mem_orbit w⁻¹ h
  · exact MulAction.mem_orbit_of_mem_orbit w h

/-- The Weyl orbit of the zero weight is `{0}`. -/
@[simp]
theorem weylWeightOrbit_zero : P.weylWeightOrbit (0 : M) = {0} := by
  ext y
  simp [eq_comm]

/-- **The coefficients of an orbit sum**: `m_x` has coefficient `1` at every weight of the Weyl
orbit of `x` and `0` at every other weight. -/
@[simp]
theorem coeff_weightOrbitSum [DecidableEq M] (x y : M) :
    (P.weightOrbitSum x).coeff y = if y ∈ P.weylWeightOrbit x then 1 else 0 := by
  simp [weightOrbitSum, AddMonoidAlgebra.coeff_sum, AddMonoidAlgebra.coeff_single,
    Finsupp.single_apply]

/-- The orbit sum of `x` has coefficient `1` on the Weyl orbit of `x`. -/
theorem coeff_weightOrbitSum_of_mem {x y : M} (h : y ∈ P.weylWeightOrbit x) :
    (P.weightOrbitSum x).coeff y = 1 := by
  classical
  simp [coeff_weightOrbitSum, h]

/-- The orbit sum of `x` has coefficient `0` off the Weyl orbit of `x`. -/
theorem coeff_weightOrbitSum_of_notMem {x y : M} (h : y ∉ P.weylWeightOrbit x) :
    (P.weightOrbitSum x).coeff y = 0 := by
  classical
  simp [coeff_weightOrbitSum, h]

/-- Weyl-conjugate weights have the same orbit sum. -/
@[simp]
theorem weightOrbitSum_smul (w : P.weylGroup) (x : M) :
    P.weightOrbitSum (w • x) = P.weightOrbitSum x := by
  rw [weightOrbitSum, weightOrbitSum, weylWeightOrbit_smul]

/-- The orbit sum of the zero weight is the unit `e^0 = 1` of `ℤ[M]`. -/
@[simp]
theorem weightOrbitSum_zero : P.weightOrbitSum (0 : M) = 1 := by
  rw [weightOrbitSum, weylWeightOrbit_zero, sum_singleton, AddMonoidAlgebra.one_def]

/-- **An orbit sum is Weyl-invariant.** -/
theorem isWeylInvariant_weightOrbitSum (x : M) : IsWeylInvariant P (P.weightOrbitSum x) := by
  classical
  refine (isWeylInvariant_iff P _).mpr fun w y ↦ ?_
  simp only [coeff_weightOrbitSum, smul_mem_weylWeightOrbit_iff]

end OrbitSum

variable {P} in
/-- **The sum of all Weyl translates of a weight is Weyl-invariant.** In `∑_w e^{w x}` each weight
of the Weyl orbit of `x` occurs once for every Weyl group element sending `x` to it, and
translating by a Weyl group element permutes those elements. -/
theorem isWeylInvariant_sum_single_smul [Fintype P.weylGroup] (x : M) :
    IsWeylInvariant P (∑ w : P.weylGroup, AddMonoidAlgebra.single (w • x) (1 : ℤ)) := by
  classical
  refine (isWeylInvariant_iff P _).mpr fun v y ↦ ?_
  simp only [AddMonoidAlgebra.coeff_sum, Finset.sum_apply', AddMonoidAlgebra.coeff_single,
    Finsupp.single_apply]
  exact Fintype.sum_equiv (Equiv.mulLeft v⁻¹) _ _ fun w ↦ by simp [mul_smul, inv_smul_eq_iff]

end RootPairing

/-! ### The orbit-sum expansion -/

namespace TauCeti

open Finset RootPairing

variable {ι : Type u} {R : Type v} {M : Type w} {N : Type x}
  [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  {P : RootPairing ι R M N}
  [Finite ι] [CharZero R] [IsDomain R] [P.IsRootSystem] [P.IsCrystallographic]
  {b : P.Base} [P.IsReduced] [Finite P.weylGroup] {f : AddMonoidAlgebra ℤ M} {lam : M}

/-- **The orbit-sum expansion of a Weyl-invariant element.** Let `f ∈ ℤ[M]` be Weyl-invariant,
with every weight in its support lying below `lam` and integral on the simple coroots. Then `f`
is the combination of the orbit sums of the dominant integral weights below `lam`, each weighted
by its own coefficient in `f`:

`f = ∑_{mu ∈ dominantWeightsBelow lam} f(mu) · m_mu`.

Each Weyl orbit in the support of `f` contains exactly one dominant integral weight, which lies
below `lam`, so the orbit sums of these weights account for every coefficient of `f` once. -/
theorem IsWeylInvariant.eq_sum_coeff_smul_weightOrbitSum (hf : IsWeylInvariant P f)
    (hcone : ∀ y, f.coeff y ≠ 0 → lam - y ∈ posRootCone P b)
    (hint : ∀ y, f.coeff y ≠ 0 → ∀ i ∈ b.support, ∃ z : ℤ, P.coroot' i y = (z : R)) :
    f = ∑ mu ∈ P.dominantWeightsBelow b lam, f.coeff mu • P.weightOrbitSum mu := by
  classical
  refine AddMonoidAlgebra.ext (Finsupp.ext fun y ↦ ?_)
  -- every term with `y` in the orbit of `mu` contributes `f(mu) = f(y)`
  have hterm : ∀ mu : M, f.coeff mu * (P.weightOrbitSum mu).coeff y =
      if y ∈ P.weylWeightOrbit mu then f.coeff y else 0 := fun mu ↦ by
    rw [coeff_weightOrbitSum]
    split_ifs with h
    · obtain ⟨w, rfl⟩ := mem_weylWeightOrbit.mp h
      rw [mul_one, hf.coeff_smul]
    · rw [mul_zero]
  simp only [AddMonoidAlgebra.coeff_sum, Finset.sum_apply', AddMonoidAlgebra.coeff_smul_apply,
    smul_eq_mul, hterm]
  by_cases hy : f.coeff y = 0
  · simp [hy]
  -- the support of `f` is reflection-stable, so `y` has a dominant translate `w • y` in it
  have hrefl : ∀ x ∈ {x : M | f.coeff x ≠ 0}, ∀ i ∈ b.support,
      P.reflection i x ∈ {x : M | f.coeff x ≠ 0} := fun x hx i _ ↦ by
    have hsmul : P.reflection i x = (RootPairing.weylGroup.ofIdx P i) • x := by
      rw [RootPairing.weylGroup.ofIdx_smul, RootPairing.Equiv.reflection_smul]
    simpa only [Set.mem_ofPred_eq, hsmul, hf.coeff_smul] using hx
  obtain ⟨w, hwS, hwdom⟩ :=
    exists_weylGroup_smul_dominant_of_forall_reflection_mem_of_sub_mem_posRootCone b hcone hint
      hrefl (mu := y) hy
  have hmem : w • y ∈ P.dominantWeightsBelow b lam :=
    mem_dominantWeightsBelow.mpr ⟨hcone _ hwS, hwdom⟩
  rw [sum_eq_single_of_mem (w • y) hmem fun mu hmu hne ↦ ?_]
  · simp only [weylWeightOrbit_smul, self_mem_weylWeightOrbit, ↓reduceIte]
  -- a second dominant weight `mu` whose orbit contains `y` would be `w • y` itself
  refine ite_eq_right_iff.mpr fun hymu ↦ ?_
  obtain ⟨v, rfl⟩ := mem_weylWeightOrbit.mp hymu
  rw [← mul_smul] at hwdom
  have hfix := weylGroup_smul_eq_self_of_dominantIntegral (mem_dominantWeightsBelow.mp hmu).2 hwdom
  exact (hne (by rw [← mul_smul, hfix])).elim

end TauCeti
