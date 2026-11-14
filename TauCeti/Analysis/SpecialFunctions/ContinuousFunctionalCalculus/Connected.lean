/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Convex.PathConnected
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Isometric
public import TauCeti.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Polar
public import TauCeti.Topology.Algebra.Star.Unitary
import Mathlib.Analysis.Normed.Ring.Units
import TauCeti.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Cartan

/-!
# Polar paths and path-connectedness of groups of units via the continuous functional calculus

In an algebra `A` with a real continuous functional calculus and compatible star order, the set
`{p : A | IsStrictlyPositive p}` of strictly positive elements is convex and contains `1`: for any
strictly positive `p` and `t ∈ [0, 1]`, the affine interpolation `(1 - t) • 1 + t • p` remains
strictly positive.

When `A` is a complete normed `ℝ`-algebra, `Units.val : Aˣ → A` is an open embedding onto
`{a : A | IsUnit a}`, so this straight line lifts to an explicit path
`IsStrictlyPositive.linePathToOne` from `1` to `p.isUnit.unit` in `Aˣ`. Combining the right polar
decomposition `a = a.polarUnitary * √(a⋆ a)` (`Units.polarUnitary_mul_sqrt_star_mul`) with any path
`γ` from `1` to `a.polarUnitary` in `unitary A` yields the explicit polar-linear path

`t ↦ (γ t : A) * ((1 - t) • 1 + t • √(a⋆ a))`

from `1` to `a` inside `Aˣ` (`Units.polarPathToOne`). Consequently, whenever `unitary A` is
path-connected, `Aˣ` and `{a : A | IsUnit a}` are path-connected as well
(`Units.pathConnectedSpace_of_unitary`, `Units.isPathConnected_isUnit_of_unitary`), without needing
an isometric functional calculus or operator logarithms.

When the real continuous functional calculus is isometric (for example in any unital C⋆-algebra),
`Units.polarUnitary : Aˣ → unitary A` is a continuous retraction (`Units.continuous_polarUnitary`),
so `Aˣ` is path-connected if and only if `unitary A` is (`Units.pathConnectedSpace_iff_unitary`).

## Main declarations

* `IsStrictlyPositive.add_nonneg_of_cfc`, `IsStrictlyPositive.convex_setOf`: `{p : A |
  IsStrictlyPositive p}` is closed under adding nonnegative elements and convex over `ℝ`.
* `IsStrictlyPositive.one_sub_smul_add_smul`: `(1 - t) • 1 + t • p` is strictly positive for
  `t ∈ [0, 1]`.
* `IsStrictlyPositive.isPathConnected_setOf`: `{p : A | IsStrictlyPositive p}` is path-connected.
* `IsStrictlyPositive.linePathToOne`: the straight-line path `t ↦ (1 - t) • 1 + t • p` from `1` to
  `hp.isUnit.unit` in `Aˣ`.
* `Units.polarPathToOne`: the polar-linear path from `1` to `a : Aˣ` induced by a path from `1` to
  `a.polarUnitary` in `unitary A`.
* `Units.pathConnectedSpace_of_unitary`, `Units.isPathConnected_isUnit_of_unitary`:
  path-connectedness of `unitary A` implies path-connectedness of `Aˣ` and `{a : A | IsUnit a}`.
* `Units.joined_one_iff_joined_polarUnitary`, `Units.pathConnectedSpace_iff_unitary`: equivalence
  under an isometric real continuous functional calculus.

## References

* R. G. Douglas, *Banach Algebra Techniques in Operator Theory*, 2nd ed., Springer (1998),
  Proposition 4.29 and Corollary 4.30.
* K. R. Davidson, *C⋆-Algebras by Example*, Fields Institute Monographs 6, American Mathematical
  Society (1996), §I.5.
-/

public section

noncomputable section

open Set
open scoped unitInterval

section Convex

variable {A : Type*} [Ring A] [PartialOrder A] [StarRing A] [StarOrderedRing A]
  [TopologicalSpace A] [Algebra ℝ A] [ContinuousFunctionalCalculus ℝ A IsSelfAdjoint]

private theorem real_smul_nonneg {c : ℝ} (hc : 0 ≤ c) {q : A} (hq : 0 ≤ q) : 0 ≤ c • q := by
  have hself : IsSelfAdjoint (algebraMap ℝ A (√c)) := cfc_predicate_algebraMap (√c)
  have hconj : 0 ≤ algebraMap ℝ A (√c) * q * star (algebraMap ℝ A (√c)) :=
    star_right_conjugate_nonneg hq (algebraMap ℝ A (√c))
  rwa [hself.star_eq, mul_assoc, ← Algebra.commutes (√c) q, ← mul_assoc, ← map_mul,
    Real.mul_self_sqrt hc, ← Algebra.smul_def] at hconj

variable [NonnegSpectrumClass ℝ A] [IsSemitopologicalRing A] [T2Space A]

/-- Adding a nonnegative element `b` to a strictly positive element `a` in a real-CFC star-ordered
algebra yields a strictly positive element `a + b` (generalizing `IsStrictlyPositive.add_nonneg`
from C⋆-algebras to any algebra with a real continuous functional calculus). -/
theorem IsStrictlyPositive.add_nonneg_of_cfc {a b : A} (ha : IsStrictlyPositive a) (hb : 0 ≤ b) :
    IsStrictlyPositive (a + b) := by
  have hs : IsStrictlyPositive (CFC.sqrt a) := ha.sqrt
  let u : Aˣ := hs.isUnit.unit
  have hu_sa : IsSelfAdjoint (u : A) := hs.isSelfAdjoint
  have hinv_sa : IsSelfAdjoint (↑u⁻¹ : A) := by
    rw [IsSelfAdjoint, ← Units.coe_star]
    refine congrArg Units.val (inv_eq_of_mul_eq_one_right (G := Aˣ) (Units.ext ?_)).symm
    rw [Units.val_mul, Units.coe_star, ← hu_sa.star_eq, ← star_mul, u.inv_mul, star_one,
      Units.val_one]
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

/-- The cone `{p : A | IsStrictlyPositive p}` of strictly positive elements is convex over `ℝ`. -/
theorem IsStrictlyPositive.convex_setOf : Convex ℝ {p : A | IsStrictlyPositive p} := by
  rw [convex_iff_forall_pos]
  intro p hp q hq u v hu hv _
  have hup_unit : IsUnit (u • p) :=
    isUnit_iff_exists.2 ⟨u⁻¹ • ↑hp.isUnit.unit⁻¹, by simp [hu.ne']⟩
  have hup : IsStrictlyPositive (u • p) :=
    hup_unit.isStrictlyPositive (real_smul_nonneg hu.le hp.nonneg)
  exact hup.add_nonneg_of_cfc (real_smul_nonneg hv.le hq.nonneg)

/-- Affine interpolation `(1 - t) • 1 + t • p` between `1` and a strictly positive element `p`
remains strictly positive for every `t ∈ [0, 1]`. -/
theorem IsStrictlyPositive.one_sub_smul_add_smul {p : A} (hp : IsStrictlyPositive p) {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) 1) :
    IsStrictlyPositive ((1 - t) • (1 : A) + t • p) :=
  IsStrictlyPositive.convex_setOf isStrictlyPositive_one hp (sub_nonneg.2 ht.2) ht.1
    (sub_add_cancel 1 t)

/-- The set of strictly positive elements in `A` is path-connected. -/
theorem IsStrictlyPositive.isPathConnected_setOf [ContinuousSMul ℝ A] :
    IsPathConnected {p : A | IsStrictlyPositive p} :=
  IsStrictlyPositive.convex_setOf.isPathConnected ⟨1, isStrictlyPositive_one⟩

end Convex

section BanachUnits

/-- In a complete normed ring `R`, the set `{r : R | IsUnit r}` of invertible elements is
path-connected if and only if the topological group `Rˣ` is path-connected. -/
theorem TauCeti.isPathConnected_isUnit_iff {R : Type*} [NormedRing R] [CompleteSpace R] :
    IsPathConnected {r : R | IsUnit r} ↔ PathConnectedSpace Rˣ := by
  have hrange : range (Units.val : Rˣ → R) = {r : R | IsUnit r} := by
    ext r
    exact ⟨fun ⟨u, hu⟩ ↦ hu ▸ u.isUnit, fun hr ↦ ⟨hr.unit, hr.unit_spec⟩⟩
  let e := (Units.isOpenEmbedding_val (R := R)).isEmbedding.toHomeomorph
  rw [← hrange, isPathConnected_iff_pathConnectedSpace]
  exact ⟨fun _ ↦ e.symm.pathConnectedSpace, fun _ ↦ e.pathConnectedSpace⟩

end BanachUnits

section PolarPath

variable {A : Type*} [NormedRing A] [StarRing A] [NormedAlgebra ℝ A] [CompleteSpace A]
  [PartialOrder A] [StarOrderedRing A] [ContinuousFunctionalCalculus ℝ A IsSelfAdjoint]
  [NonnegSpectrumClass ℝ A]

/-- The straight-line path `t ↦ (1 - t) • 1 + t • p` in `Aˣ` from `1` to `hp.isUnit.unit` for a
strictly positive element `p : A`. -/
def IsStrictlyPositive.linePathToOne {p : A} (hp : IsStrictlyPositive p) :
    Path (1 : Aˣ) hp.isUnit.unit where
  toFun t := (hp.one_sub_smul_add_smul t.2).isUnit.unit
  continuous_toFun := by
    rw [(Units.isOpenEmbedding_val (R := A)).isEmbedding.continuous_iff]
    have hEq : ((Units.val : Aˣ → A) ∘ fun t : I ↦ (hp.one_sub_smul_add_smul t.2).isUnit.unit) =
        fun t : I ↦ (1 - (t : ℝ)) • (1 : A) + (t : ℝ) • p := by
      ext t
      exact IsUnit.unit_spec _
    rw [hEq]
    fun_prop
  source' := Units.ext <| by simp
  target' := Units.ext <| by simp

/-- Coercing `hp.linePathToOne t` to `A` gives the affine combination `(1 - t) • 1 + t • p`. -/
@[simp]
theorem IsStrictlyPositive.val_linePathToOne_apply {p : A} (hp : IsStrictlyPositive p) (t : I) :
    (hp.linePathToOne t : A) = (1 - (t : ℝ)) • (1 : A) + (t : ℝ) • p :=
  IsUnit.unit_spec _

/-- Every point along `hp.linePathToOne` is strictly positive in `A`. -/
theorem IsStrictlyPositive.isStrictlyPositive_linePathToOne_apply {p : A}
    (hp : IsStrictlyPositive p) (t : I) :
    IsStrictlyPositive (hp.linePathToOne t : A) := by
  rw [hp.val_linePathToOne_apply]
  exact hp.one_sub_smul_add_smul t.2

section ContinuousStar

variable [ContinuousStar A]

namespace Units

/-- Given a unit `a : Aˣ` and a path `γ : Path 1 a.polarUnitary` in `unitary A`, the polar-linear
path `t ↦ γ t * ((1 - t) • 1 + t • √(a⋆ a))` joins `1` to `a` inside `Aˣ`. -/
def polarPathToOne (a : Aˣ) (γ : Path 1 a.polarUnitary) : Path 1 a :=
  ((γ.map Unitary.continuous_toUnits).mul a.isStrictlyPositive_sqrt_star_mul.linePathToOne).cast
    (by simp) <| Units.ext <| by simp [polarUnitary_mul_sqrt_star_mul]

/-- Evaluating `a.polarPathToOne γ` at `t` gives `(γ t : A) * ((1 - t) • 1 + t • √(a⋆ a))`. -/
@[simp]
theorem val_polarPathToOne_apply (a : Aˣ) (γ : Path 1 a.polarUnitary) (t : I) :
    (a.polarPathToOne γ t : A) =
      (γ t : A) * ((1 - (t : ℝ)) • (1 : A) + (t : ℝ) • CFC.sqrt (star (a : A) * a)) := by
  simp [polarPathToOne]

/-- A unit `a : Aˣ` is joined to `1` in `Aˣ` whenever its polar unitary `a.polarUnitary` is joined
to `1` in `unitary A`. -/
theorem joined_one_of_joined_polarUnitary {a : Aˣ} (h : Joined 1 a.polarUnitary) :
    Joined 1 a :=
  let ⟨γ⟩ := h
  ⟨a.polarPathToOne γ⟩

/-- Whenever `unitary A` is path-connected, the group of units `Aˣ` is path-connected. -/
theorem pathConnectedSpace_of_unitary [PathConnectedSpace (unitary A)] :
    PathConnectedSpace Aˣ where
  nonempty := ⟨1⟩
  joined a b :=
    (joined_one_of_joined_polarUnitary (PathConnectedSpace.joined 1 a.polarUnitary)).symm.trans
      (joined_one_of_joined_polarUnitary (PathConnectedSpace.joined 1 b.polarUnitary))

/-- Whenever `unitary A` is path-connected, the set `{a : A | IsUnit a}` of invertible elements in
`A` is path-connected. -/
theorem isPathConnected_isUnit_of_unitary [PathConnectedSpace (unitary A)] :
    IsPathConnected {a : A | IsUnit a} :=
  have := pathConnectedSpace_of_unitary (A := A)
  TauCeti.isPathConnected_isUnit_iff.2 this

end Units

end ContinuousStar

end PolarPath

section Isometric

variable {A : Type*} [NormedRing A] [StarRing A] [NormedAlgebra ℝ A] [CompleteSpace A]
  [PartialOrder A] [StarOrderedRing A] [IsometricContinuousFunctionalCalculus ℝ A IsSelfAdjoint]
  [NonnegSpectrumClass ℝ A] [ContinuousStar A]

namespace Units

/-- Under an isometric real continuous functional calculus, a unit `a : Aˣ` lies in the path
component of `1` in `Aˣ` if and only if `a.polarUnitary` lies in the path component of `1` in
`unitary A`. -/
theorem joined_one_iff_joined_polarUnitary {a : Aˣ} :
    Joined 1 a ↔ Joined 1 a.polarUnitary := by
  refine ⟨fun ⟨γ⟩ ↦ ?_, joined_one_of_joined_polarUnitary⟩
  exact ⟨(γ.map continuous_polarUnitary).cast polarUnitary_one.symm rfl⟩

/-- Under an isometric real continuous functional calculus, the group of units `Aˣ` is
path-connected if and only if the unitary group `unitary A` is path-connected. -/
theorem pathConnectedSpace_iff_unitary :
    PathConnectedSpace Aˣ ↔ PathConnectedSpace (unitary A) := by
  refine ⟨fun _ ↦ ?_, fun _ ↦ pathConnectedSpace_of_unitary⟩
  have hsurj : Function.Surjective (polarUnitary : Aˣ → unitary A) :=
    fun u ↦ ⟨Unitary.toUnits u, polarUnitary_toUnits u⟩
  exact hsurj.pathConnectedSpace continuous_polarUnitary

end Units

end Isometric
