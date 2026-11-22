/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
public import Mathlib.Analysis.Convex.Basic
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic

/-!
# Order properties of star-ordered algebras with a continuous functional calculus

In a star-ordered algebra `A` carrying a continuous functional calculus over a star-ordered
scalar semiring `R`, any unital `⋆`-homomorphism `C(spectrum R 0, R) →⋆ₐ[R] A` forces
`star (algebraMap R A r) = algebraMap R A (star r)`, hence `StarModule R A`
(`TauCeti.starModule_of_cfc`). Consequently `A` is an ordered `R`-module
(`TauCeti.isOrderedModule_of_cfc`) without needing a separate `StarModule R A` assumption.

Over `ℝ`, the square-root congruence argument also generalizes Mathlib's C⋆-algebra theorems
`IsStrictlyPositive.add_nonneg` and `IsStrictlyPositive.nonneg_add` to arbitrary star-ordered
algebras with a real continuous functional calculus (`IsStrictlyPositive.add_nonneg_of_cfc`,
`IsStrictlyPositive.nonneg_add_of_cfc`): if `a` is strictly positive and `0 ≤ b`, then
`a + b = √a (1 + √a⁻¹ b √a⁻¹) √a` is strictly positive. Consequently the cone
`{p : A | IsStrictlyPositive p}` of strictly positive elements is convex over `ℝ`
(`TauCeti.convex_setOf_isStrictlyPositive`).

## Main declarations

* `TauCeti.starModule_of_cfc`: a star-ordered algebra with a continuous functional calculus over a
  star-ordered scalar semiring `R` is a `StarModule R A`.
* `TauCeti.isOrderedModule_of_cfc`: a star-ordered algebra with a continuous functional calculus
  over a star-ordered scalar semiring `R` is an ordered `R`-module.
* `IsStrictlyPositive.add_nonneg_of_cfc`, `IsStrictlyPositive.nonneg_add_of_cfc`: adding a
  nonnegative element to a strictly positive element (on either side) yields a strictly positive
  element in any real-CFC star-ordered algebra.
* `TauCeti.convex_setOf_isStrictlyPositive`: `{p : A | IsStrictlyPositive p}` is convex over `ℝ`.
* `IsStrictlyPositive.one_sub_smul_add_smul`: `(1 - t) • 1 + t • p` is strictly positive for
  `t ∈ [0, 1]`.
-/

public section

namespace TauCeti

section StarModule

variable {R A : Type*} [CommSemiring R] [StarRing R]
  [MetricSpace R] [IsTopologicalSemiring R] [ContinuousStar R]
  [Ring A] [StarRing A] [TopologicalSpace A] [Algebra R A]

/-- In an algebra carrying a continuous functional calculus over a scalar semiring `R`, the scalar
action satisfies `StarModule R A`. -/
theorem starModule_of_cfc {p : A → Prop} [ContinuousFunctionalCalculus R A p] :
    StarModule R A := by
  obtain ⟨φ, -⟩ :=
    ContinuousFunctionalCalculus.exists_cfc_of_predicate (R := R) (0 : A) (cfc_predicate_zero R)
  have hstar (r : R) : star (algebraMap R A r) = algebraMap R A (star r) := by
    have h := map_star φ (algebraMap R C(spectrum R (0 : A), R) r)
    have hc : star (algebraMap R C(spectrum R (0 : A), R) r) =
        algebraMap R C(spectrum R (0 : A), R) (star r) := by
      ext x
      rfl
    simpa only [AlgHomClass.commutes, hc] using h.symm
  exact ⟨fun r a ↦ by
    rw [Algebra.smul_def, star_mul, hstar, ← Algebra.commutes, ← Algebra.smul_def]⟩

end StarModule

section OrderedModule

variable {R A : Type*} [CommSemiring R] [PartialOrder R] [StarRing R] [StarOrderedRing R]
  [MetricSpace R] [IsTopologicalSemiring R] [ContinuousStar R]
  [Ring A] [PartialOrder A] [StarRing A] [StarOrderedRing A]
  [TopologicalSpace A] [Algebra R A]

/-- In a star-ordered algebra carrying a continuous functional calculus over a star-ordered
scalar semiring `R`, the scalar action makes `A` an ordered `R`-module without requiring an
explicit `StarModule R A` instance. -/
theorem isOrderedModule_of_cfc {p : A → Prop} [ContinuousFunctionalCalculus R A p] :
    IsOrderedModule R A :=
  have : StarModule R A := starModule_of_cfc (p := p)
  inferInstance

end OrderedModule

end TauCeti

section StrictPositivity

variable {A : Type*} [Ring A] [PartialOrder A] [StarRing A] [StarOrderedRing A]
  [TopologicalSpace A] [Algebra ℝ A] [ContinuousFunctionalCalculus ℝ A IsSelfAdjoint]
  [NonnegSpectrumClass ℝ A] [IsSemitopologicalRing A] [T2Space A]

/-- Adding a nonnegative element `b` to a strictly positive element `a` in a real-CFC star-ordered
algebra yields a strictly positive element `a + b` (generalizing `IsStrictlyPositive.add_nonneg`
from C⋆-algebras to any algebra with a real continuous functional calculus). -/
theorem IsStrictlyPositive.add_nonneg_of_cfc {a b : A} (ha : IsStrictlyPositive a) (hb : 0 ≤ b) :
    IsStrictlyPositive (a + b) := by
  have hs : IsStrictlyPositive (CFC.sqrt a) := ha.sqrt
  let u : Aˣ := hs.isUnit.unit
  have hu_sa : IsSelfAdjoint (u : A) := hs.isSelfAdjoint
  have hu' : IsSelfAdjoint u := Units.ext hu_sa.star_eq
  have hinv_sa : IsSelfAdjoint (↑u⁻¹ : A) := congrArg Units.val hu'.inv.star_eq
  let q : A := (↑u⁻¹ : A) * b * star (↑u⁻¹ : A)
  have hq0 : 0 ≤ q := star_right_conjugate_nonneg hb (↑u⁻¹ : A)
  have h1q : IsStrictlyPositive (1 + q) := by
    have hcfc : cfc (fun x : ℝ ↦ 1 + x) q = 1 + q := by
      rw [cfc_add .., cfc_const _ _ hq0.isSelfAdjoint, cfc_id' ℝ q, Algebra.algebraMap_eq_smul_one,
        one_smul]
    rw [← hcfc]
    exact (cfc_isStrictlyPositive_iff (fun x : ℝ ↦ 1 + x) q).2 fun x hx ↦
      add_pos_of_pos_of_nonneg one_pos (spectrum_nonneg_of_nonneg hq0 hx)
  have hconj : (u : A) * (1 + q) * (u : A) = a + b := by
    have huu : (u : A) * (u : A) = a := by
      simpa only [u, IsUnit.unit_spec] using CFC.sqrt_mul_sqrt_self a ha.nonneg
    calc (u : A) * (1 + q) * (u : A)
        = (u : A) * (u : A) + ((u : A) * ↑u⁻¹) * b * (↑u⁻¹ * (u : A)) := by
            simp only [q, hinv_sa.star_eq, mul_add, add_mul, mul_one, mul_assoc]
      _ = a + b := by rw [huu, u.mul_inv, u.inv_mul, one_mul, mul_one]
  rw [← hconj]
  exact IsStrictlyPositive.conjugate_of_isUnit_of_isSelfAdjoint (1 + q) (u : A) u.isUnit hu_sa h1q

/-- Adding a strictly positive element `b` to a nonnegative element `a` in a real-CFC star-ordered
algebra yields a strictly positive element `a + b` (generalizing `IsStrictlyPositive.nonneg_add`
from C⋆-algebras to any algebra with a real continuous functional calculus). -/
theorem IsStrictlyPositive.nonneg_add_of_cfc {a b : A} (ha : 0 ≤ a) (hb : IsStrictlyPositive b) :
    IsStrictlyPositive (a + b) :=
  add_comm b a ▸ hb.add_nonneg_of_cfc ha

/-- The cone `{p : A | IsStrictlyPositive p}` of strictly positive elements is convex over `ℝ`. -/
theorem TauCeti.convex_setOf_isStrictlyPositive : Convex ℝ {p : A | IsStrictlyPositive p} := by
  have : IsOrderedModule ℝ A := TauCeti.isOrderedModule_of_cfc
  rw [convex_iff_forall_pos]
  intro p hp q hq u v hu hv _
  exact (hp.smul hu).add_nonneg_of_cfc (smul_nonneg hv.le hq.nonneg)

/-- Affine interpolation `(1 - t) • 1 + t • p` between `1` and a strictly positive element `p`
remains strictly positive for every `t ∈ [0, 1]`. -/
theorem IsStrictlyPositive.one_sub_smul_add_smul {p : A} (hp : IsStrictlyPositive p) {t : ℝ}
    (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    IsStrictlyPositive ((1 - t) • (1 : A) + t • p) :=
  TauCeti.convex_setOf_isStrictlyPositive isStrictlyPositive_one hp (sub_nonneg.2 ht.2) ht.1
    (sub_add_cancel 1 t)

end StrictPositivity
