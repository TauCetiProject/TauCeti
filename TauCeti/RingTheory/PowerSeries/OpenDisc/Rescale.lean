/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Normed.Ring.MulUnit
public import TauCeti.RingTheory.PowerSeries.OpenDisc.AnalyticSubst
public import TauCeti.RingTheory.PowerSeries.OpenDisc.Taylor
public import TauCeti.RingTheory.PowerSeries.Restricted.Rescale
import TauCeti.RingTheory.MvPowerSeries.Rescale

/-!
# Rescaling and affine coordinate changes on open discs

This file develops the rescaling and affine coordinate-change maps between algebras of power
series on open discs:

1. **Rescaling.** Over any normed commutative ring `R`, if `‖u‖ * S₀ ≤ R₀`, rescaling
   `f(X) ↦ f(u X)` defines an `R`-algebra homomorphism `rescaleAlgHom` from the open disc of radius
   `R₀` to that of radius `S₀`. When `u : Rˣ` is a multiplicative unit with `‖(u : R)‖ * S₀ = R₀`,
   this upgrades to an `R`-algebra isomorphism `rescaleEquiv` whose inverse rescales by `u⁻¹` and
   which identifies the smaller-radius Gauss norms at radii `s` and `‖u‖ * s`.
2. **Affine coordinate changes.** Over a complete ultrametric normed commutative ring `R`,
   combining Taylor translation `taylorHom` at `a` (`‖a‖ < R₀`) with rescaling by `u`
   (`‖u‖ * S₀ ≤ R₀`) defines the continuous `R`-algebra homomorphism `affineAlgHom` pulling back
   along `X ↦ a + u X` without requiring `NormOneClass R`. Using the commutation identity
   `taylor b (rescale u g) = rescale u (taylor (u * b) g)`
   (`PowerSeries.OnOpenDisc.taylor_rescale`), affine pullbacks compose by
   `(a, u) ∘ (b, v) = (a + u b, u v)` and yield `R`-algebra isomorphisms `affineEquiv` when `u` is
   a multiplicative unit with `‖(u : R)‖ * S₀ = R₀`, with inverse pulling back along
   `X ↦ -u⁻¹ a + u⁻¹ X`. On nonempty target open discs, `affineAlgHom` and `rescaleAlgHom` agree
   with `analyticSubst` without requiring `NormOneClass R`, and `taylorHom` agrees with
   `analyticSubst` when `NormOneClass R` holds.

## Main definitions

* `TauCeti.PowerSeries.OnOpenDisc.rescaleAlgHom` and `TauCeti.PowerSeries.OnOpenDisc.rescaleEquiv`:
  rescaling `f(X) ↦ f(u X)` on open discs, and the isomorphism for multiplicative units.
* `TauCeti.PowerSeries.OnOpenDisc.affineAlgHom` and `TauCeti.PowerSeries.OnOpenDisc.affineEquiv`:
  affine pullbacks `f(X) ↦ f(a + u X)` as `R`-algebra homomorphisms and isomorphisms.

## Main results

* `TauCeti.PowerSeries.OnOpenDisc.norm_restrict_rescaleAlgHom_le`,
  `TauCeti.PowerSeries.OnOpenDisc.norm_restrict_rescaleAlgHom`,
  `TauCeti.PowerSeries.OnOpenDisc.norm_restrict_rescaleEquiv`, and
  `TauCeti.PowerSeries.OnOpenDisc.uniformContinuous_rescaleAlgHom`: Gauss bounds and uniform
  continuity of rescaling.
* `TauCeti.PowerSeries.OnOpenDisc.affineAlgHom_comp_affineAlgHom` and
  `TauCeti.PowerSeries.OnOpenDisc.affineEquiv_symm_apply`: composition and inversion of affine
  coordinate changes.
* `TauCeti.PowerSeries.OnOpenDisc.taylorHom_analyticSubst`,
  `TauCeti.PowerSeries.OnOpenDisc.affineAlgHom_eq_analyticSubst`,
  `TauCeti.PowerSeries.OnOpenDisc.taylorHom_eq_analyticSubst`, and
  `TauCeti.PowerSeries.OnOpenDisc.rescaleAlgHom_eq_analyticSubst`: compatibility and agreement with
  analytic substitution.

## References

* P. Colmez, *Fonctions d'une variable p-adique*, Astérisque 330 (2010), §I.4.
* S. Bosch, U. Güntzer and R. Remmert, *Non-Archimedean Analysis*, Grundlehren 261, §5.1.
-/

public section

open Filter PowerSeries
open scoped Topology

namespace TauCeti.PowerSeries.OnOpenDisc

private theorem norm_mul_lt_of_lt_of_mul_le {R : Type*} [SeminormedRing R] {u : R}
    {s S₀ R₀ : ℝ} (hR₀ : 0 < R₀) (hs : s < S₀) (hu : ‖u‖ * S₀ ≤ R₀) :
    ‖u‖ * s < R₀ := by
  rcases (norm_nonneg u).eq_or_lt with hu0 | hu0
  · simpa [← hu0] using hR₀
  · exact (mul_lt_mul_of_pos_left hs hu0).trans_le hu

section Rescale

variable {R : Type*} [NormedCommRing R] {R₀ S₀ T₀ : ℝ}

/-- **Rescaling on open discs.** If `‖u‖ * S₀ ≤ R₀`, substituting `X ↦ u * X` carries series on
the open disc of radius `R₀` to series on the open disc of radius `S₀` as an `R`-algebra
homomorphism. -/
noncomputable def rescaleAlgHom {u : R} (hu : ‖u‖ * S₀ ≤ R₀) :
    OnOpenDisc.subring R R₀ →ₐ[R] OnOpenDisc.subring R S₀ where
  toFun f := ⟨PowerSeries.rescale u (f : R⟦X⟧),
    OnOpenDisc.mem_subring.mpr (((OnOpenDisc.mem_subring.mp f.2).mono hu).rescale)⟩
  map_one' := Subtype.ext (map_one (PowerSeries.rescale u))
  map_mul' f g := Subtype.ext (map_mul (PowerSeries.rescale u) (f : R⟦X⟧) g)
  map_zero' := Subtype.ext (map_zero (PowerSeries.rescale u))
  map_add' f g := Subtype.ext (map_add (PowerSeries.rescale u) (f : R⟦X⟧) g)
  commutes' a := Subtype.ext (by simp)

/-- `rescaleAlgHom` acts as `PowerSeries.rescale` on the underlying formal series. -/
@[simp]
theorem coe_rescaleAlgHom {u : R} (hu : ‖u‖ * S₀ ≤ R₀) (f : OnOpenDisc.subring R R₀) :
    (rescaleAlgHom hu f : R⟦X⟧) = PowerSeries.rescale u (f : R⟦X⟧) := (rfl)

/-- `rescaleAlgHom` multiplies the `n`th coefficient by `u ^ n`. -/
theorem coeff_rescaleAlgHom {u : R} (hu : ‖u‖ * S₀ ≤ R₀) (f : OnOpenDisc.subring R R₀)
    (n : ℕ) :
    coeff n (rescaleAlgHom hu f : R⟦X⟧) = u ^ n * coeff n (f : R⟦X⟧) := by
  rw [coe_rescaleAlgHom, coeff_rescale]

/-- `rescaleAlgHom` sends `X` to `u * X`. -/
@[simp]
theorem rescaleAlgHom_X {u : R} (hu : ‖u‖ * S₀ ≤ R₀) :
    rescaleAlgHom hu (OnOpenDisc.polynomialHom Polynomial.X) =
      algebraMap R _ u * OnOpenDisc.polynomialHom Polynomial.X :=
  Subtype.ext <| PowerSeries.ext fun n ↦ by simp [coeff_C_mul]

/-- Rescaling by `1` at the same radius is the identity. -/
@[simp]
theorem rescaleAlgHom_one (h1 : ‖(1 : R)‖ * R₀ ≤ R₀) :
    rescaleAlgHom h1 = AlgHom.id R (OnOpenDisc.subring R R₀) :=
  AlgHom.ext fun f ↦ Subtype.ext (by simp)

/-- Rescaling by `0` evaluates at the origin. -/
@[simp]
theorem rescaleAlgHom_zero (h0 : ‖(0 : R)‖ * S₀ ≤ R₀) (f : OnOpenDisc.subring R R₀) :
    rescaleAlgHom h0 f = algebraMap R _ (constantCoeff (f : R⟦X⟧)) :=
  Subtype.ext (by simp)

/-- Rescaling homomorphisms compose by multiplying their scaling factors. -/
theorem rescaleAlgHom_comp_rescaleAlgHom {u v : R} (hu : ‖u‖ * S₀ ≤ R₀) (hv : ‖v‖ * T₀ ≤ S₀)
    (huv : ‖u * v‖ * T₀ ≤ R₀) :
    (rescaleAlgHom hv).comp (rescaleAlgHom hu) = rescaleAlgHom huv :=
  AlgHom.ext fun f ↦ Subtype.ext (by simp [PowerSeries.rescale_rescale])

/-- Evaluating a rescaled open-disc series at `b` evaluates the original series at `u • b`. -/
theorem evalAt_rescaleAlgHom {A : Type*} [Semiring A] [Algebra R A] [TopologicalSpace A]
    {u : R} (hu : ‖u‖ * S₀ ≤ R₀) (f : OnOpenDisc.subring R R₀) (b : A) :
    (rescaleAlgHom hu f : R⟦X⟧).evalAt b = (f : R⟦X⟧).evalAt (u • b) :=
  PowerSeries.evalAt_rescale (f : R⟦X⟧) u b

/-- If `0 < R₀` and `u : Rˣ` is a norm-multiplicative unit with `‖(u : R)‖ * S₀ = R₀`, then
`‖((u⁻¹ : Rˣ) : R)‖ * R₀ = S₀`. -/
theorem norm_units_inv_mul_eq_of_pos (hR₀ : 0 < R₀) {u : Rˣ} (hu : IsNormMulUnit (u : R))
    (huS : ‖(u : R)‖ * S₀ = R₀) :
    ‖(((u⁻¹ : Rˣ) : R))‖ * R₀ = S₀ := by
  have hu0 : ‖(u : R)‖ ≠ 0 := fun h0 ↦ hR₀.ne (by simpa [h0] using huS)
  rw [NormedRing.norm_units_inv_of_norm_mul hu0 hu.norm_mul, ← huS,
    inv_mul_cancel_left₀ hu0]

private theorem onOpenDisc_rescale_units_inv (u : Rˣ) (hu : IsNormMulUnit (u : R))
    (huS : ‖(u : R)‖ * S₀ = R₀) {g : R⟦X⟧} (hg : g.OnOpenDisc S₀) :
    (PowerSeries.rescale (((u⁻¹ : Rˣ) : R)) g).OnOpenDisc R₀ := by
  rcases le_or_gt R₀ 0 with hR₀ | hR₀
  · exact onOpenDisc_of_nonpos hR₀ _
  · exact (hg.mono (norm_units_inv_mul_eq_of_pos hR₀ hu huS).le).rescale

/-- **Rescaling by a multiplicative unit is an algebra isomorphism** between the open discs of
radii `R₀` and `S₀` when `‖(u : R)‖ * S₀ = R₀`, with inverse rescaling by `u⁻¹`. -/
noncomputable def rescaleEquiv (u : Rˣ) (hu : IsNormMulUnit (u : R))
    (huS : ‖(u : R)‖ * S₀ = R₀) :
    OnOpenDisc.subring R R₀ ≃ₐ[R] OnOpenDisc.subring R S₀ :=
  { rescaleAlgHom huS.le with
    invFun g := ⟨PowerSeries.rescale (((u⁻¹ : Rˣ) : R)) (g : R⟦X⟧),
      OnOpenDisc.mem_subring.mpr <|
        onOpenDisc_rescale_units_inv u hu huS (OnOpenDisc.mem_subring.mp g.2)⟩
    left_inv f := Subtype.ext (by simp [PowerSeries.rescale_rescale])
    right_inv g := Subtype.ext (by simp [PowerSeries.rescale_rescale]) }

/-- `rescaleEquiv` acts by `PowerSeries.rescale` on the underlying formal series. -/
@[simp]
theorem coe_rescaleEquiv (u : Rˣ) (hu : IsNormMulUnit (u : R)) (huS : ‖(u : R)‖ * S₀ = R₀)
    (f : OnOpenDisc.subring R R₀) :
    (rescaleEquiv u hu huS f : R⟦X⟧) = PowerSeries.rescale (u : R) (f : R⟦X⟧) := (rfl)

/-- The inverse of `rescaleEquiv` rescales by `u⁻¹`. -/
@[simp]
theorem coe_rescaleEquiv_symm (u : Rˣ) (hu : IsNormMulUnit (u : R)) (huS : ‖(u : R)‖ * S₀ = R₀)
    (g : OnOpenDisc.subring R S₀) :
    ((rescaleEquiv u hu huS).symm g : R⟦X⟧) =
      PowerSeries.rescale (((u⁻¹ : Rˣ) : R)) (g : R⟦X⟧) := (rfl)

section UltrametricRescale

variable [IsUltrametricDist R]

attribute [local instance] radius_pos

/-- Restricting a rescaled open-disc series to a smaller closed disc of radius `s` applies
`restrictedRescaleAlgHom` to the restriction at any smaller closed disc of radius `r` with
`‖u‖ * s ≤ r`. -/
theorem restrict_rescaleAlgHom {u : R} (hu : ‖u‖ * S₀ ≤ R₀)
    (s : Set.Ioo (0 : ℝ) S₀) (r : Set.Ioo (0 : ℝ) R₀) (hsr : ‖u‖ * s ≤ r)
    (f : OnOpenDisc.subring R R₀) :
    restrict s (rescaleAlgHom hu f) =
      TauCeti.PowerSeries.restrictedRescaleAlgHom s.2.1.le hsr (restrict r f) :=
  Subtype.ext (by simp)

/-- On smaller closed discs with `‖u‖ * s ≤ r`, rescaling does not increase the Gauss norm.
No `NormOneClass R` hypothesis is needed. -/
theorem norm_restrict_rescaleAlgHom_le {u : R} (hu : ‖u‖ * S₀ ≤ R₀)
    (s : Set.Ioo (0 : ℝ) S₀) (r : Set.Ioo (0 : ℝ) R₀) (hsr : ‖u‖ * s ≤ r)
    (f : OnOpenDisc.subring R R₀) :
    ‖restrict s (rescaleAlgHom hu f)‖ ≤ ‖restrict r f‖ := by
  rw [restrict_rescaleAlgHom hu s r hsr f]
  exact TauCeti.PowerSeries.norm_restrictedRescaleAlgHom_le s.2.1.le hsr (restrict r f)

/-- Rescaling by a norm-multiplicative element `u` identifies the Gauss norm at a smaller radius
`s < S₀` with the Gauss norm at `r = ‖u‖ * s < R₀`. -/
theorem norm_restrict_rescaleAlgHom {u : R} (hu : IsNormMulUnit u) (huS : ‖u‖ * S₀ ≤ R₀)
    (s : Set.Ioo (0 : ℝ) S₀) (r : Set.Ioo (0 : ℝ) R₀) (hr : (r : ℝ) = ‖u‖ * s)
    (f : OnOpenDisc.subring R R₀) :
    ‖restrict s (rescaleAlgHom huS f)‖ = ‖restrict r f‖ := by
  rw [norm_eq_gaussNorm, norm_eq_gaussNorm, PowerSeries.gaussNorm_eq, PowerSeries.gaussNorm_eq]
  congr 1
  funext n
  simpa only [coe_restrict, coe_rescaleAlgHom, PowerSeries.rescale_eq, PowerSeries.coeff,
    Finsupp.prod_single_index, pow_zero] using
    _root_.MvPowerSeries.norm_coeff_rescale_mul_prod (fun _ : Unit ↦ u) (fun _ ↦ hu)
      (fun _ ↦ hr.symm) (f : R⟦X⟧) (Finsupp.single () n)

/-- Rescaling by a multiplicative unit `u` identifies the Gauss norm at a smaller radius `s < S₀`
with the Gauss norm at `r = ‖(u : R)‖ * s < R₀`. -/
theorem norm_restrict_rescaleEquiv (u : Rˣ) (hu : IsNormMulUnit (u : R))
    (huS : ‖(u : R)‖ * S₀ = R₀) (s : Set.Ioo (0 : ℝ) S₀) (r : Set.Ioo (0 : ℝ) R₀)
    (hr : (r : ℝ) = ‖(u : R)‖ * s) (f : OnOpenDisc.subring R R₀) :
    ‖restrict s (rescaleEquiv u hu huS f)‖ = ‖restrict r f‖ :=
  norm_restrict_rescaleAlgHom hu huS.le s r hr f

/-- Rescaling out of a nonempty open disc (`0 < R₀`) is uniformly continuous for the Gauss
uniformities. -/
theorem uniformContinuous_rescaleAlgHom [Fact (0 < R₀)] {u : R} (hu : ‖u‖ * S₀ ≤ R₀) :
    UniformContinuous (rescaleAlgHom hu) := by
  refine uniformContinuous_iff.mpr fun s ↦ ?_
  obtain ⟨r, hsr, hrR⟩ := exists_between (norm_mul_lt_of_lt_of_mul_le Fact.out s.2.2 hu)
  let r' : Set.Ioo (0 : ℝ) R₀ := ⟨r, (mul_nonneg (norm_nonneg u) s.2.1.le).trans_lt hsr, hrR⟩
  have : Fact (0 < r) := ⟨r'.2.1⟩
  simp_rw [restrict_rescaleAlgHom hu s r' hsr.le]
  exact (TauCeti.PowerSeries.lipschitzWith_restrictedRescaleAlgHom s.2.1.le
    hsr.le).uniformContinuous.comp (uniformContinuous_restrict r')

/-- Rescaling out of a nonempty open disc (`0 < R₀`) is continuous for the Gauss topologies. -/
@[continuity]
theorem continuous_rescaleAlgHom [Fact (0 < R₀)] {u : R} (hu : ‖u‖ * S₀ ≤ R₀) :
    Continuous (rescaleAlgHom hu) :=
  (uniformContinuous_rescaleAlgHom hu).continuous

end UltrametricRescale

end Rescale

section Affine

variable {R : Type*} [NormedCommRing R] [IsUltrametricDist R] [CompleteSpace R]
  {R₀ S₀ T₀ : ℝ}

attribute [local instance] radius_pos

/-- **Translating an analytic substitution** translates the inner series:
`(f(g))(X + b) = f(g(X + b))`. No `NormOneClass R` hypothesis is needed. -/
theorem taylorHom_analyticSubst [Fact (0 < S₀)] {b : R} (hb : ‖b‖ < S₀)
    (g : OnOpenDisc.subring R S₀)
    (hg : ∀ s : Set.Ioo (0 : ℝ) S₀, ‖restrict s g‖ < R₀)
    (f : OnOpenDisc.subring R R₀) :
    taylorHom hb (analyticSubst g hg f) =
      analyticSubst (taylorHom hb g) (norm_restrict_taylorHom_lt hb g hg) f := by
  have heq : (taylorHom hb).comp (analyticSubst g hg) =
      analyticSubst (taylorHom hb g) (norm_restrict_taylorHom_lt hb g hg) :=
    eq_analyticSubst _ _ _ ((continuous_taylorHom hb).comp (continuous_analyticSubst g hg))
      (by simp)
  exact AlgHom.congr_fun heq f

/-- **Affine pullback `f(X) ↦ f(a + u X)` on open discs**, defined as Taylor translation by `a`
(`‖a‖ < R₀`) followed by rescaling by `u` (`‖u‖ * S₀ ≤ R₀`). Unlike a direct definition through
`analyticSubst`, this requires neither `NormOneClass R` nor positivity of `S₀`. -/
noncomputable def affineAlgHom {a u : R} (ha : ‖a‖ < R₀) (hu : ‖u‖ * S₀ ≤ R₀) :
    OnOpenDisc.subring R R₀ →ₐ[R] OnOpenDisc.subring R S₀ :=
  (rescaleAlgHom hu).comp (taylorHom ha)

/-- `affineAlgHom` acts as `rescaleAlgHom` applied to `taylorHom`. -/
theorem affineAlgHom_apply {a u : R} (ha : ‖a‖ < R₀) (hu : ‖u‖ * S₀ ≤ R₀)
    (f : OnOpenDisc.subring R R₀) :
    affineAlgHom ha hu f = rescaleAlgHom hu (taylorHom ha f) := (rfl)

/-- The underlying formal series of `affineAlgHom ha hu f` is `rescale u (taylor a f)`. -/
@[simp]
theorem coe_affineAlgHom {a u : R} (ha : ‖a‖ < R₀) (hu : ‖u‖ * S₀ ≤ R₀)
    (f : OnOpenDisc.subring R R₀) :
    (affineAlgHom ha hu f : R⟦X⟧) = PowerSeries.rescale u (PowerSeries.taylor a (f : R⟦X⟧)) := by
  simp [affineAlgHom_apply]

/-- `affineAlgHom` sends `X` to `a + u * X`. -/
@[simp]
theorem affineAlgHom_X {a u : R} (ha : ‖a‖ < R₀) (hu : ‖u‖ * S₀ ≤ R₀) :
    affineAlgHom ha hu (OnOpenDisc.polynomialHom Polynomial.X) =
      algebraMap R _ a + algebraMap R _ u * OnOpenDisc.polynomialHom Polynomial.X := by
  rw [affineAlgHom_apply, taylorHom_polynomialHom, Polynomial.taylor_X, map_add, map_add,
    rescaleAlgHom_X, OnOpenDisc.polynomialHom_C, AlgHom.commutes, add_comm]

/-- At centre `a = 0`, `affineAlgHom` reduces to `rescaleAlgHom`. -/
@[simp]
theorem affineAlgHom_zero_left {u : R} (h0 : ‖(0 : R)‖ < R₀) (hu : ‖u‖ * S₀ ≤ R₀) :
    affineAlgHom h0 hu = rescaleAlgHom hu := by
  have : Fact (0 < R₀) := ⟨by simpa using h0⟩
  ext f
  simp [affineAlgHom_apply]

/-- For unit scale `u = 1` on the same disc, `affineAlgHom` reduces to `taylorHom`. -/
@[simp]
theorem affineAlgHom_one_right {a : R} (ha : ‖a‖ < R₀) (h1 : ‖(1 : R)‖ * R₀ ≤ R₀) :
    affineAlgHom ha h1 = taylorHom ha := by
  ext f
  simp [affineAlgHom_apply]

/-- On smaller closed discs with `‖a‖ ≤ r` and `‖u‖ * s ≤ r`, `affineAlgHom` does not increase the
Gauss norm. -/
theorem norm_restrict_affineAlgHom_le {a u : R} (ha : ‖a‖ < R₀) (hu : ‖u‖ * S₀ ≤ R₀)
    (s : Set.Ioo (0 : ℝ) S₀) (r : Set.Ioo (0 : ℝ) R₀) (har : ‖a‖ ≤ r) (hsr : ‖u‖ * s ≤ r)
    (f : OnOpenDisc.subring R R₀) :
    ‖restrict s (affineAlgHom ha hu f)‖ ≤ ‖restrict r f‖ :=
  (norm_restrict_rescaleAlgHom_le hu s r hsr (taylorHom ha f)).trans
    (norm_restrict_taylorHom_le ha r r le_rfl har f)

/-- Affine pullbacks on open discs are continuous for the Gauss topologies. -/
@[continuity]
theorem continuous_affineAlgHom {a u : R} (ha : ‖a‖ < R₀) (hu : ‖u‖ * S₀ ≤ R₀) :
    Continuous (affineAlgHom ha hu) := by
  have : Fact (0 < R₀) := ⟨(norm_nonneg a).trans_lt ha⟩
  exact (continuous_rescaleAlgHom hu).comp (continuous_taylorHom ha)

/-- **Composition of affine pullbacks on open discs**: pulling back along `X ↦ a + u Y` and then
along `Y ↦ b + v Z` pulls back along `X ↦ (a + u b) + (u v) Z`. -/
theorem affineAlgHom_comp_affineAlgHom {a u b v : R} (ha : ‖a‖ < R₀) (hu : ‖u‖ * S₀ ≤ R₀)
    (hb : ‖b‖ < S₀) (hv : ‖v‖ * T₀ ≤ S₀)
    (haub : ‖a + u * b‖ < R₀) (huv : ‖u * v‖ * T₀ ≤ R₀) :
    (affineAlgHom hb hv).comp (affineAlgHom ha hu) = affineAlgHom haub huv := by
  have hub : ‖u‖ * ‖b‖ < R₀ := norm_mul_lt_of_lt_of_mul_le ((norm_nonneg a).trans_lt ha) hb hu
  have hub' : ‖u * b‖ < R₀ := (norm_mul_le u b).trans_lt hub
  ext f : 1
  apply Subtype.ext
  calc (affineAlgHom hb hv (affineAlgHom ha hu f) : R⟦X⟧)
      = PowerSeries.rescale v (PowerSeries.taylor b
          (PowerSeries.rescale u (PowerSeries.taylor a (f : R⟦X⟧)))) := by
          simp [coe_affineAlgHom]
    _ = PowerSeries.rescale v (PowerSeries.rescale u
          (PowerSeries.taylor (u * b) (PowerSeries.taylor a (f : R⟦X⟧)))) := by
          rw [((OnOpenDisc.mem_subring.mp f.2).taylor ha).taylor_rescale hub']
    _ = PowerSeries.rescale (u * v) (PowerSeries.taylor (a + u * b) (f : R⟦X⟧)) := by
          have h := congrArg Subtype.val (taylorHom_taylorHom ha hub' f)
          simp only [coe_taylorHom, add_comm (u * b) a] at h
          rw [PowerSeries.rescale_rescale, h]
    _ = (affineAlgHom haub huv f : R⟦X⟧) := (coe_affineAlgHom haub huv f).symm

/-- **Affine automorphism between open discs**: when `‖a‖ < R₀` and `u : Rˣ` is a multiplicative
unit with `‖(u : R)‖ * S₀ = R₀`, pulling back along `X ↦ a + u X` is an `R`-algebra isomorphism
between the open-disc algebras at `R₀` and `S₀`. -/
noncomputable def affineEquiv {a : R} (ha : ‖a‖ < R₀) (u : Rˣ) (hu : IsNormMulUnit (u : R))
    (huS : ‖(u : R)‖ * S₀ = R₀) :
    OnOpenDisc.subring R R₀ ≃ₐ[R] OnOpenDisc.subring R S₀ :=
  (taylorEquiv ha).trans (rescaleEquiv u hu huS)

/-- `affineEquiv` acts as `affineAlgHom`. -/
@[simp]
theorem affineEquiv_apply {a : R} (ha : ‖a‖ < R₀) (u : Rˣ) (hu : IsNormMulUnit (u : R))
    (huS : ‖(u : R)‖ * S₀ = R₀) (f : OnOpenDisc.subring R R₀) :
    affineEquiv ha u hu huS f = affineAlgHom ha huS.le f :=
  Subtype.ext (by simp [affineEquiv])

omit [IsUltrametricDist R] [CompleteSpace R] in
/-- If `‖a‖ < R₀` and `u : Rˣ` is a norm-multiplicative unit with `‖(u : R)‖ * S₀ = R₀`, then the
inverse affine centre `-((u⁻¹ : Rˣ) : R) * a` has norm strictly less than `S₀`. -/
theorem norm_neg_units_inv_mul_lt {a : R} (ha : ‖a‖ < R₀) {u : Rˣ}
    (hu : IsNormMulUnit (u : R)) (huS : ‖(u : R)‖ * S₀ = R₀) :
    ‖-((u⁻¹ : Rˣ) : R) * a‖ < S₀ := by
  have hR₀ : 0 < R₀ := (norm_nonneg a).trans_lt ha
  have hu0 : 0 < ‖(u : R)‖ := (norm_nonneg _).lt_of_ne' fun h0 ↦
    hR₀.ne (by simpa [h0] using huS)
  have hinv : 0 < ‖(((u⁻¹ : Rˣ) : R))‖ := by
    rw [NormedRing.norm_units_inv_of_norm_mul hu0.ne' hu.norm_mul]
    exact inv_pos.mpr hu0
  rw [neg_mul, norm_neg]
  exact (norm_mul_le _ _).trans_lt <|
    (mul_lt_mul_of_pos_left ha hinv).trans_eq (norm_units_inv_mul_eq_of_pos hR₀ hu huS)

/-- The inverse of `affineEquiv` is the affine pullback with centre `-((u⁻¹ : Rˣ) : R) * a` and
scale `((u⁻¹ : Rˣ) : R)`. -/
@[simp]
theorem affineEquiv_symm_apply {a : R} (ha : ‖a‖ < R₀) (u : Rˣ)
    (hu : IsNormMulUnit (u : R)) (huS : ‖(u : R)‖ * S₀ = R₀)
    (g : OnOpenDisc.subring R S₀) :
    (affineEquiv ha u hu huS).symm g =
      affineAlgHom (norm_neg_units_inv_mul_lt ha hu huS)
        (norm_units_inv_mul_eq_of_pos ((norm_nonneg a).trans_lt ha) hu huS).le g := by
  have hR₀ : 0 < R₀ := (norm_nonneg a).trans_lt ha
  have hu0 : 0 < ‖(u : R)‖ := (norm_nonneg _).lt_of_ne' fun h0 ↦
    hR₀.ne (by simpa [h0] using huS)
  have hS₀ : 0 < S₀ := by nlinarith
  have h1 : ‖(1 : R)‖ = 1 := mul_left_cancel₀ hu0.ne' (by simpa using (hu.norm_mul 1).symm)
  have haub : ‖-((u⁻¹ : Rˣ) : R) * a + ((u⁻¹ : Rˣ) : R) * a‖ < S₀ := by simpa using hS₀
  have huv : ‖(((u⁻¹ : Rˣ) : R)) * (u : R)‖ * S₀ ≤ S₀ := by simp [h1]
  have hcomp := AlgHom.congr_fun (affineAlgHom_comp_affineAlgHom
    (norm_neg_units_inv_mul_lt ha hu huS) (norm_units_inv_mul_eq_of_pos hR₀ hu huS).le
    ha huS.le haub huv) g
  rw [AlgHom.comp_apply] at hcomp
  rw [AlgEquiv.symm_apply_eq, affineEquiv_apply, hcomp]
  exact Subtype.ext (by simp [neg_mul])

section AnalyticSubstComparison

omit [CompleteSpace R] in
/-- The affine polynomial `a + u * X` has smaller-disc Gauss norm strictly below `R₀` whenever
`‖a‖ < R₀` and `‖u‖ * S₀ ≤ R₀`. No `NormOneClass R` hypothesis is needed. -/
theorem norm_restrict_algebraMap_add_algebraMap_mul_X_lt {a u : R} (ha : ‖a‖ < R₀)
    (hu : ‖u‖ * S₀ ≤ R₀) (s : Set.Ioo (0 : ℝ) S₀) :
    ‖restrict s (algebraMap R (OnOpenDisc.subring R S₀) a +
      algebraMap R (OnOpenDisc.subring R S₀) u * OnOpenDisc.polynomialHom Polynomial.X)‖ < R₀ := by
  have hus : ‖u‖ * s < R₀ := norm_mul_lt_of_lt_of_mul_le ((norm_nonneg a).trans_lt ha) s.2.2 hu
  refine (TauCeti.PowerSeries.norm_le_iff.mpr fun n ↦ ?_).trans_lt (max_lt ha hus)
  rw [coe_restrict, Subring.coe_add, Subring.coe_mul, OnOpenDisc.coe_algebraMap,
    OnOpenDisc.coe_algebraMap, Algebra.algebraMap_self, RingHom.id_apply, RingHom.id_apply,
    OnOpenDisc.coe_polynomialHom, Polynomial.coe_X]
  rcases n with _ | _ | n <;> simp

omit [CompleteSpace R] in
/-- The translated coordinate `a + X` has smaller-disc Gauss norm strictly below `S₀` whenever
`‖a‖ < S₀`. -/
theorem norm_restrict_algebraMap_add_X_lt [NormOneClass R] {a : R} (ha : ‖a‖ < S₀)
    (s : Set.Ioo (0 : ℝ) S₀) :
    ‖restrict s (algebraMap R (OnOpenDisc.subring R S₀) a +
      OnOpenDisc.polynomialHom Polynomial.X)‖ < S₀ := by
  have h1 : ‖(1 : R)‖ * S₀ ≤ S₀ := by simp
  simpa using norm_restrict_algebraMap_add_algebraMap_mul_X_lt ha h1 s

omit [CompleteSpace R] in
/-- The rescaled coordinate `u * X` has smaller-disc Gauss norm strictly below `R₀ > 0` whenever
`‖u‖ * S₀ ≤ R₀`. No `NormOneClass R` hypothesis is needed. -/
theorem norm_restrict_algebraMap_mul_X_lt [Fact (0 < R₀)] {u : R} (hu : ‖u‖ * S₀ ≤ R₀)
    (s : Set.Ioo (0 : ℝ) S₀) :
    ‖restrict s (algebraMap R (OnOpenDisc.subring R S₀) u *
      OnOpenDisc.polynomialHom Polynomial.X)‖ < R₀ := by
  have h0 : ‖(0 : R)‖ < R₀ := by simpa using (Fact.out : 0 < R₀)
  simpa using norm_restrict_algebraMap_add_algebraMap_mul_X_lt h0 hu s

variable [Fact (0 < S₀)]

/-- **Agreement of `affineAlgHom` with `analyticSubst`.** Over a complete ultrametric ring, the
affine pullback `affineAlgHom ha hu` into a nonempty open disc coincides with analytic substitution
by `a + u * X`, without requiring `NormOneClass R`. -/
theorem affineAlgHom_eq_analyticSubst {a u : R} (ha : ‖a‖ < R₀) (hu : ‖u‖ * S₀ ≤ R₀) :
    affineAlgHom ha hu =
      analyticSubst (algebraMap R _ a + algebraMap R _ u * OnOpenDisc.polynomialHom Polynomial.X)
        (norm_restrict_algebraMap_add_algebraMap_mul_X_lt ha hu) :=
  eq_analyticSubst _ _ (affineAlgHom ha hu) (continuous_affineAlgHom ha hu) (affineAlgHom_X ha hu)

/-- **Agreement of `taylorHom` with `analyticSubst`.** -/
theorem taylorHom_eq_analyticSubst [NormOneClass R] {a : R} (ha : ‖a‖ < S₀) :
    taylorHom ha =
      analyticSubst (algebraMap R _ a + OnOpenDisc.polynomialHom Polynomial.X)
        (norm_restrict_algebraMap_add_X_lt ha) := by
  have h1 : ‖(1 : R)‖ * S₀ ≤ S₀ := by simp
  rw [← affineAlgHom_one_right ha h1, affineAlgHom_eq_analyticSubst]
  exact analyticSubst_congr (by simp) _ _

/-- **Agreement of `rescaleAlgHom` with `analyticSubst`** between nonempty open discs, without
requiring `NormOneClass R`. -/
theorem rescaleAlgHom_eq_analyticSubst [Fact (0 < R₀)] {u : R} (hu : ‖u‖ * S₀ ≤ R₀) :
    rescaleAlgHom hu =
      analyticSubst (algebraMap R _ u * OnOpenDisc.polynomialHom Polynomial.X)
        (norm_restrict_algebraMap_mul_X_lt hu) := by
  have h0 : ‖(0 : R)‖ < R₀ := by simpa using (Fact.out : 0 < R₀)
  rw [← affineAlgHom_zero_left h0 hu, affineAlgHom_eq_analyticSubst]
  exact analyticSubst_congr (by simp) _ _

end AnalyticSubstComparison

end Affine

end TauCeti.PowerSeries.OnOpenDisc
