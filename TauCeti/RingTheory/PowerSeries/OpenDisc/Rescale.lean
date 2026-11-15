/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Normed.Ring.MulUnit
public import TauCeti.RingTheory.PowerSeries.OpenDisc.AnalyticSubst
public import TauCeti.RingTheory.PowerSeries.OpenDisc.Taylor
public import TauCeti.RingTheory.PowerSeries.Rescale

/-!
# Radius restriction, rescaling, and affine coordinate changes on open discs

This file develops the radius-comparison, rescaling, and affine coordinate-change maps between
algebras of power series on open discs:

1. **Radius comparisons and closed-disc inclusions.** Shrinking the radius from `R₀` to `R₁ ≤ R₀`
   gives a uniformly continuous ring homomorphism `radiusHom` with dense range, and restricting
   from the closed-disc algebra `IsRestricted.subring R₀` into `OnOpenDisc.subring R R₀` gives a
   uniformly continuous ring homomorphism `ofIsRestricted` bounded in every smaller-radius Gauss
   norm and having dense range.
2. **Rescaling.** Over any normed commutative ring `R`, if `‖u‖ * S₀ ≤ R₀`, rescaling
   `f(X) ↦ f(u X)` defines an `R`-algebra homomorphism `rescaleAlgHom` from the open disc of radius
   `R₀` to that of radius `S₀`. When `u : Rˣ` is a multiplicative unit with `‖(u : R)‖ * S₀ = R₀`,
   this upgrades to an `R`-algebra isomorphism `rescaleEquiv` whose inverse rescales by `u⁻¹` and
   which identifies the smaller-radius Gauss norms at radii `s` and `‖u‖ * s`.
3. **Affine coordinate changes.** Over a complete ultrametric normed commutative ring `R`,
   combining Taylor translation `taylorAlgHom` at `a` (`‖a‖ < R₀`) with rescaling by `u`
   (`‖u‖ * S₀ ≤ R₀`) defines the continuous `R`-algebra homomorphism `affineAlgHom` pulling back
   along `X ↦ a + u X` without requiring `NormOneClass R`. Using the commutation identity
   `taylor b (rescale u g) = rescale u (taylor (u * b) g)`
   (`PowerSeries.OnOpenDisc.taylor_rescale`), affine pullbacks compose by
   `(a, u) ∘ (b, v) = (a + u b, u v)` and yield `R`-algebra isomorphisms `affineEquiv` when `u` is
   a multiplicative unit with `‖(u : R)‖ * S₀ = R₀`. When `NormOneClass R` holds, `taylorHom`,
   `rescaleAlgHom`, and `affineAlgHom` agree with `analyticSubst`.

## Main definitions

* `TauCeti.PowerSeries.OnOpenDisc.radiusHom` and `TauCeti.PowerSeries.OnOpenDisc.ofIsRestricted`:
  inclusions from larger open discs and from the boundary closed-disc algebra.
* `TauCeti.PowerSeries.OnOpenDisc.rescaleAlgHom` and `TauCeti.PowerSeries.OnOpenDisc.rescaleEquiv`:
  rescaling `f(X) ↦ f(u X)` on open discs, and the isomorphism for multiplicative units.
* `TauCeti.PowerSeries.OnOpenDisc.taylorAlgHom`, `TauCeti.PowerSeries.OnOpenDisc.affineAlgHom`,
  and `TauCeti.PowerSeries.OnOpenDisc.affineEquiv`: Taylor translation and affine pullbacks
  `f(X) ↦ f(a + u X)` as `R`-algebra homomorphisms and isomorphisms.

## Main results

* `PowerSeries.OnOpenDisc.taylor_rescale`: `taylor b (rescale u f) = rescale u (taylor (u * b) f)`
  whenever `‖u * b‖ < R₀`.
* `TauCeti.PowerSeries.OnOpenDisc.uniformContinuous_radiusHom`,
  `TauCeti.PowerSeries.OnOpenDisc.denseRange_radiusHom`,
  `TauCeti.PowerSeries.OnOpenDisc.uniformContinuous_ofIsRestricted`, and
  `TauCeti.PowerSeries.OnOpenDisc.denseRange_ofIsRestricted`: topological comparison properties.
* `TauCeti.PowerSeries.OnOpenDisc.norm_restrict_rescaleAlgHom_le`,
  `TauCeti.PowerSeries.OnOpenDisc.norm_restrict_rescaleAlgHom`,
  `TauCeti.PowerSeries.OnOpenDisc.norm_restrict_rescaleEquiv`, and
  `TauCeti.PowerSeries.OnOpenDisc.uniformContinuous_rescaleAlgHom`: Gauss bounds and uniform
  continuity of rescaling.
* `TauCeti.PowerSeries.OnOpenDisc.affineAlgHom_comp_affineAlgHom`: composition of affine
  coordinate changes.
* `TauCeti.PowerSeries.OnOpenDisc.taylorHom_analyticSubst` and
  `TauCeti.PowerSeries.OnOpenDisc.affineAlgHom_eq_analyticSubst`: compatibility and agreement with
  analytic substitution.

## References

* P. Colmez, *Fonctions d'une variable p-adique*, Astérisque 330 (2010), §I.4.
* S. Bosch, U. Güntzer and R. Remmert, *Non-Archimedean Analysis*, Grundlehren 261, §5.1.
-/

public section

namespace PowerSeries

section TaylorRescale

variable {R : Type*} [NormedCommRing R] [CompleteSpace R] {R₀ : ℝ} {f : R⟦X⟧}

/-- **Intertwining of Taylor translation and rescaling** on an open disc: if `f` lies on the open
disc of radius `R₀` and `‖u * b‖ < R₀`, then translating `f(u X)` by `b` is rescaling by `u` the
translate of `f` by `u * b`. -/
theorem OnOpenDisc.taylor_rescale (hf : f.OnOpenDisc R₀) {u b : R} (hub : ‖u * b‖ < R₀) :
    PowerSeries.taylor b (PowerSeries.rescale u f) =
      PowerSeries.rescale u (PowerSeries.taylor (u * b) f) := by
  ext n
  rw [coeff_taylor, coeff_rescale, coeff_taylor, hasseDeriv_rescale, evalAt_def,
    ← (((hf.hasseDeriv n).hasSum_evalAt hub).mul_left (u ^ n)).tsum_eq]
  congr 1
  ext k
  simp only [coeff_C_mul, coeff_rescale, smul_eq_mul, mul_pow]
  ring

end TaylorRescale

end PowerSeries

open Filter PowerSeries
open scoped Topology

namespace TauCeti.PowerSeries.OnOpenDisc

section Radius

variable {R : Type*} [NormedRing R] {R₀ R₁ R₂ : ℝ}

/-- Restriction of series from an open disc of radius `R₀` to a smaller open disc of radius
`R₁ ≤ R₀`. -/
noncomputable def radiusHom (h : R₁ ≤ R₀) :
    OnOpenDisc.subring R R₀ →+* OnOpenDisc.subring R R₁ :=
  Subring.inclusion (OnOpenDisc.subring_antitone R h)

/-- `radiusHom` leaves the underlying formal power series unchanged. -/
@[simp]
theorem coe_radiusHom (h : R₁ ≤ R₀) (f : OnOpenDisc.subring R R₀) :
    (radiusHom h f : R⟦X⟧) = f :=
  Subring.coe_inclusion _ f

/-- Restricting an open disc to itself is the identity. -/
@[simp]
theorem radiusHom_self : radiusHom (R := R) (le_refl R₀) = RingHom.id _ :=
  RingHom.ext fun _ ↦ rfl

/-- Radius restrictions compose transitively. -/
theorem radiusHom_comp_radiusHom (h₁ : R₁ ≤ R₀) (h₂ : R₂ ≤ R₁) :
    (radiusHom (R := R) h₂).comp (radiusHom h₁) = radiusHom (h₂.trans h₁) :=
  RingHom.ext fun _ ↦ rfl

/-- Radius restriction commutes with the inclusion of polynomials. -/
@[simp]
theorem radiusHom_polynomialHom (h : R₁ ≤ R₀) (p : Polynomial R) :
    radiusHom h (OnOpenDisc.polynomialHom p) = OnOpenDisc.polynomialHom p :=
  Subtype.ext (by simp)

section UltrametricRadius

variable [IsUltrametricDist R]

attribute [local instance] radius_pos

/-- Restricting to a closed disc inside `R₁` after `radiusHom h` is restricting directly from
`R₀`. -/
theorem restrict_radiusHom (h : R₁ ≤ R₀) (r : Set.Ioo (0 : ℝ) R₁)
    (f : OnOpenDisc.subring R R₀) :
    restrict r (radiusHom h f) = restrict ⟨r, r.2.1, r.2.2.trans_le h⟩ f :=
  Subtype.ext (by simp)

/-- Radius restriction between open discs is uniformly continuous for the Gauss uniformities. -/
theorem uniformContinuous_radiusHom (h : R₁ ≤ R₀) :
    UniformContinuous (radiusHom (R := R) h) := by
  refine uniformContinuous_iff.mpr fun r ↦ ?_
  simp_rw [restrict_radiusHom]
  exact uniformContinuous_restrict ⟨r, r.2.1, r.2.2.trans_le h⟩

/-- Radius restriction between open discs is continuous for the Gauss topologies. -/
@[continuity]
theorem continuous_radiusHom (h : R₁ ≤ R₀) : Continuous (radiusHom (R := R) h) :=
  (uniformContinuous_radiusHom h).continuous

/-- Larger-disc series are dense in smaller-disc series for the Gauss topology. -/
theorem denseRange_radiusHom (h : R₁ ≤ R₀) : DenseRange (radiusHom (R := R) h) := by
  have hcomp : radiusHom h ∘ OnOpenDisc.polynomialHom (R := R) (R₀ := R₀) =
      OnOpenDisc.polynomialHom (R := R) (R₀ := R₁) :=
    funext (radiusHom_polynomialHom h)
  exact Dense.mono (hcomp ▸ Set.range_comp_subset_range _ _)
    (denseRange_polynomialHom (R := R) (R₀ := R₁))

/-- Inclusion of series restricted at `R₀` into series on the open disc of radius `R₀`. -/
noncomputable def ofIsRestricted :
    IsRestricted.subring (R := R) R₀ →+* OnOpenDisc.subring R R₀ :=
  Subring.inclusion (IsRestricted.subring_le_onOpenDiscSubring (R := R) R₀)

/-- `ofIsRestricted` leaves the underlying formal power series unchanged. -/
@[simp]
theorem coe_ofIsRestricted (f : IsRestricted.subring (R := R) R₀) :
    (ofIsRestricted f : R⟦X⟧) = f :=
  Subring.coe_inclusion _ f

/-- Every smaller-radius Gauss norm of `ofIsRestricted f` is bounded by the Gauss norm of `f` at
`R₀`. -/
theorem norm_restrict_ofIsRestricted_le [Fact (0 < R₀)] (r : Set.Ioo (0 : ℝ) R₀)
    (f : IsRestricted.subring (R := R) R₀) :
    ‖restrict r (ofIsRestricted f)‖ ≤ ‖f‖ :=
  norm_le_iff.mpr fun n ↦ by
    rw [coe_restrict, coe_ofIsRestricted]
    exact (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ r.2.1.le r.2.2.le n)
      (norm_nonneg _)).trans (norm_coeff_mul_pow_le f n)

/-- The inclusion from the boundary closed-disc algebra into the open-disc algebra is uniformly
continuous. -/
theorem uniformContinuous_ofIsRestricted [Fact (0 < R₀)] :
    UniformContinuous (ofIsRestricted (R := R) (R₀ := R₀)) :=
  uniformContinuous_iff.mpr fun r ↦
    (AddMonoidHomClass.lipschitz_of_bound ((restrict r).comp ofIsRestricted) 1
      (fun f ↦ by simpa only [RingHom.comp_apply, one_mul] using
        norm_restrict_ofIsRestricted_le r f)).uniformContinuous

/-- The inclusion from the boundary closed-disc algebra into the open-disc algebra is
continuous. -/
@[continuity]
theorem continuous_ofIsRestricted [Fact (0 < R₀)] :
    Continuous (ofIsRestricted (R := R) (R₀ := R₀)) :=
  uniformContinuous_ofIsRestricted.continuous

/-- Series restricted at `R₀` are dense in series on the open disc of radius `R₀`. -/
theorem denseRange_ofIsRestricted : DenseRange (ofIsRestricted (R := R) (R₀ := R₀)) := by
  let pHom : Polynomial R → IsRestricted.subring (R := R) R₀ :=
    fun p ↦ ⟨p, isRestricted_polynomial p⟩
  have hcomp : ofIsRestricted ∘ pHom = OnOpenDisc.polynomialHom (R := R) (R₀ := R₀) :=
    funext fun p ↦ Subtype.ext (by simp [pHom])
  exact Dense.mono (hcomp ▸ Set.range_comp_subset_range _ _)
    (denseRange_polynomialHom (R := R) (R₀ := R₀))

end UltrametricRadius

end Radius

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

private theorem onOpenDisc_rescale_units_inv (u : Rˣ) (hu : IsNormMulUnit (u : R))
    (huS : ‖(u : R)‖ * S₀ = R₀) {g : R⟦X⟧} (hg : g.OnOpenDisc S₀) :
    (PowerSeries.rescale (((u⁻¹ : Rˣ) : R)) g).OnOpenDisc R₀ := by
  rcases (norm_nonneg (u : R)).eq_or_lt with hu0 | hu0
  · -- When `‖u‖ = 0` for a unit `u`, `‖1‖ = 0`, so the coefficient ring is trivial.
    have h1 : ‖(1 : R)‖ ≤ 0 := by
      simpa only [Units.mul_inv, ← hu0, zero_mul] using norm_mul_le (u : R) ((u⁻¹ : Rˣ) : R)
    have h1' : ‖(1 : R)‖ = 0 := le_antisymm h1 (norm_nonneg _)
    have hx (x : R) : x = 0 := norm_eq_zero.mp <| le_antisymm
      (by simpa [h1'] using norm_mul_le x 1) (norm_nonneg _)
    have hg0 : PowerSeries.rescale (((u⁻¹ : Rˣ) : R)) g = 0 :=
      PowerSeries.ext fun n ↦ by simp [hx]
    exact hg0 ▸ onOpenDisc_zero
  · have hinv : ‖(((u⁻¹ : Rˣ) : R))‖ * R₀ = S₀ := by
      rw [NormedRing.norm_units_inv_of_norm_mul hu0.ne' hu.norm_mul, ← huS,
        inv_mul_cancel_left₀ hu0.ne']
    exact (hg.mono hinv.le).rescale

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

/-- On smaller closed discs with `‖u‖ * s ≤ r`, rescaling does not increase the Gauss norm.
No `NormOneClass R` hypothesis is needed. -/
theorem norm_restrict_rescaleAlgHom_le {u : R} (hu : ‖u‖ * S₀ ≤ R₀)
    (s : Set.Ioo (0 : ℝ) S₀) (r : Set.Ioo (0 : ℝ) R₀) (hsr : ‖u‖ * s ≤ r)
    (f : OnOpenDisc.subring R R₀) :
    ‖restrict s (rescaleAlgHom hu f)‖ ≤ ‖restrict r f‖ := by
  refine norm_le_iff.mpr fun n ↦ ?_
  rw [coe_restrict, coe_rescaleAlgHom, coeff_rescale]
  rcases eq_or_ne n 0 with rfl | hn
  · simpa using norm_coeff_mul_pow_le (restrict r f) 0
  · have hpow : ‖u ^ n * coeff n (f : R⟦X⟧)‖ ≤ ‖u‖ ^ n * ‖coeff n (f : R⟦X⟧)‖ :=
      (norm_mul_le _ _).trans
        (mul_le_mul_of_nonneg_right (norm_pow_le' u (Nat.pos_of_ne_zero hn)) (norm_nonneg _))
    calc ‖u ^ n * coeff n (f : R⟦X⟧)‖ * (s : ℝ) ^ n
        ≤ (‖u‖ ^ n * ‖coeff n (f : R⟦X⟧)‖) * (s : ℝ) ^ n :=
          mul_le_mul_of_nonneg_right hpow (pow_nonneg s.2.1.le n)
      _ = ‖coeff n (f : R⟦X⟧)‖ * (‖u‖ * s) ^ n := by ring
      _ ≤ ‖coeff n (f : R⟦X⟧)‖ * (r : ℝ) ^ n :=
          mul_le_mul_of_nonneg_left
            (pow_le_pow_left₀ (mul_nonneg (norm_nonneg _) s.2.1.le) hsr n) (norm_nonneg _)
      _ ≤ ‖restrict r f‖ := by
          simpa only [coe_restrict] using norm_coeff_mul_pow_le (restrict r f) n

/-- Rescaling by a norm-multiplicative element `u` identifies the Gauss norm at a smaller radius
`s < S₀` with the Gauss norm at `r = ‖u‖ * s < R₀`. -/
theorem norm_restrict_rescaleAlgHom {u : R} (hu : IsNormMulUnit u) (huS : ‖u‖ * S₀ ≤ R₀)
    (s : Set.Ioo (0 : ℝ) S₀) (r : Set.Ioo (0 : ℝ) R₀) (hr : (r : ℝ) = ‖u‖ * s)
    (f : OnOpenDisc.subring R R₀) :
    ‖restrict s (rescaleAlgHom huS f)‖ = ‖restrict r f‖ := by
  have hpow (n : ℕ) (c : R) : ‖u ^ n * c‖ = ‖u‖ ^ n * ‖c‖ := by
    induction n with
    | zero => simp
    | succ n ih => rw [pow_succ', mul_assoc, hu.norm_mul, ih, pow_succ', mul_assoc]
  rw [norm_eq_gaussNorm, norm_eq_gaussNorm, PowerSeries.gaussNorm_eq, PowerSeries.gaussNorm_eq]
  congr 1
  funext n
  rw [coe_restrict, coe_restrict, coe_rescaleAlgHom, coeff_rescale, hpow, hr]
  ring

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
  have ⟨r, hsr⟩ : ∃ r : Set.Ioo (0 : ℝ) R₀, ‖u‖ * s ≤ r := by
    rcases (norm_nonneg u).eq_or_lt with hu0 | hu0
    · exact ⟨⟨R₀ / 2, half_pos Fact.out, half_lt_self Fact.out⟩,
        by simp [← hu0, (half_pos (Fact.out : 0 < R₀)).le]⟩
    · exact ⟨⟨‖u‖ * s, mul_pos hu0 s.2.1, (mul_lt_mul_of_pos_left s.2.2 hu0).trans_le hu⟩,
        le_rfl⟩
  let ψ : IsRestricted.subring (R := R) (r : ℝ) →+ IsRestricted.subring (R := R) (s : ℝ) :=
    AddMonoidHom.mk' (fun g ↦ ⟨PowerSeries.rescale u g, by
        rcases (norm_nonneg u).eq_or_lt with hu0 | hu0
        · obtain rfl : u = 0 := norm_eq_zero.mp hu0.symm
          simpa [rescale_zero_apply] using PowerSeries.isRestricted_C (s : ℝ) _
        · exact (isRestricted_of_abs_le g.2
            (by rw [abs_of_pos (mul_pos hu0 s.2.1), abs_of_pos r.2.1]; exact hsr)).rescale⟩)
      (fun g₁ g₂ ↦ Subtype.ext (map_add (PowerSeries.rescale u) (g₁ : R⟦X⟧) g₂))
  have hψ_coe (g : IsRestricted.subring (R := R) (r : ℝ)) :
      (ψ g : R⟦X⟧) = PowerSeries.rescale u (g : R⟦X⟧) := (rfl)
  have hψ_bound (g : IsRestricted.subring (R := R) (r : ℝ)) : ‖ψ g‖ ≤ 1 * ‖g‖ := by
    rw [one_mul]
    refine norm_le_iff.mpr fun n ↦ ?_
    rw [hψ_coe, coeff_rescale]
    rcases eq_or_ne n 0 with rfl | hn
    · simpa using norm_coeff_mul_pow_le g 0
    · have hpow : ‖u ^ n * coeff n (g : R⟦X⟧)‖ ≤ ‖u‖ ^ n * ‖coeff n (g : R⟦X⟧)‖ :=
        (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right
          (norm_pow_le' u (Nat.pos_of_ne_zero hn)) (norm_nonneg _))
      calc ‖u ^ n * coeff n (g : R⟦X⟧)‖ * (s : ℝ) ^ n
          ≤ (‖u‖ ^ n * ‖coeff n (g : R⟦X⟧)‖) * (s : ℝ) ^ n :=
            mul_le_mul_of_nonneg_right hpow (pow_nonneg s.2.1.le n)
        _ = ‖coeff n (g : R⟦X⟧)‖ * (‖u‖ * s) ^ n := by ring
        _ ≤ ‖coeff n (g : R⟦X⟧)‖ * (r : ℝ) ^ n :=
            mul_le_mul_of_nonneg_left
              (pow_le_pow_left₀ (mul_nonneg (norm_nonneg _) s.2.1.le) hsr n) (norm_nonneg _)
        _ ≤ ‖g‖ := norm_coeff_mul_pow_le g n
  have hcomp : (fun f ↦ restrict s (rescaleAlgHom hu f)) = ψ ∘ restrict r :=
    funext fun f ↦ Subtype.ext (by simp [ψ])
  rw [hcomp]
  exact (AddMonoidHomClass.lipschitz_of_bound ψ 1 hψ_bound).uniformContinuous.comp
    (uniformContinuous_restrict r)

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

/-- Taylor translation `f(X) ↦ f(X + a)` bundled as an `R`-algebra homomorphism on the open
disc. -/
noncomputable def taylorAlgHom {a : R} (ha : ‖a‖ < R₀) :
    OnOpenDisc.subring R R₀ →ₐ[R] OnOpenDisc.subring R R₀ where
  __ := taylorHom ha
  commutes' c := Subtype.ext <| by simpa using taylor_coe a (Polynomial.C c)

/-- `taylorAlgHom` acts as `taylorHom`. -/
@[simp]
theorem coe_taylorAlgHom {a : R} (ha : ‖a‖ < R₀) (f : OnOpenDisc.subring R R₀) :
    taylorAlgHom ha f = taylorHom ha f := (rfl)

/-- Forgetting `R`-linearity of `taylorAlgHom` gives `taylorHom`. -/
@[simp]
theorem coe_taylorAlgHom_ringHom {a : R} (ha : ‖a‖ < R₀) :
    (taylorAlgHom ha : OnOpenDisc.subring R R₀ →+* OnOpenDisc.subring R R₀) =
      taylorHom ha := (rfl)

/-- Taylor translation by an interior point bundled as an `R`-algebra automorphism of the open-disc
algebra. -/
noncomputable def taylorAlgEquiv {a : R} (ha : ‖a‖ < R₀) :
    OnOpenDisc.subring R R₀ ≃ₐ[R] OnOpenDisc.subring R R₀ := by
  have : Fact (0 < R₀) := ⟨(norm_nonneg a).trans_lt ha⟩
  exact AlgEquiv.ofAlgHom (taylorAlgHom ha) (taylorAlgHom (a := -a) (by simpa using ha))
    (AlgHom.ext fun f ↦ by simp [taylorHom_taylorHom])
    (AlgHom.ext fun f ↦ by simp [taylorHom_taylorHom])

/-- `taylorAlgEquiv` acts as `taylorHom`. -/
@[simp]
theorem coe_taylorAlgEquiv {a : R} (ha : ‖a‖ < R₀) (f : OnOpenDisc.subring R R₀) :
    taylorAlgEquiv ha f = taylorHom ha f :=
  Subtype.ext (by simp [taylorAlgEquiv])

/-- The inverse of `taylorAlgEquiv` translates by `-a`. -/
@[simp]
theorem taylorAlgEquiv_symm_apply {a : R} (ha : ‖a‖ < R₀) (f : OnOpenDisc.subring R R₀) :
    (taylorAlgEquiv ha).symm f = taylorHom (a := -a) (by simpa using ha) f :=
  Subtype.ext (by simp [taylorAlgEquiv])

/-- If `g` maps smaller closed discs of `S₀` strictly inside `R₀` and `‖b‖ < S₀`, then the
translate `taylorHom hb g` also maps smaller closed discs of `S₀` strictly inside `R₀`. -/
theorem norm_restrict_taylorHom_lt {b : R} (hb : ‖b‖ < S₀) (g : OnOpenDisc.subring R S₀)
    (hg : ∀ s : Set.Ioo (0 : ℝ) S₀, ‖restrict s g‖ < R₀)
    (s : Set.Ioo (0 : ℝ) S₀) :
    ‖restrict s (taylorHom hb g)‖ < R₀ := by
  obtain ⟨t, hst, htS⟩ := exists_between (max_lt s.2.2 hb)
  let t' : Set.Ioo (0 : ℝ) S₀ := ⟨t, s.2.1.trans ((le_max_left _ _).trans_lt hst), htS⟩
  exact (norm_restrict_taylorHom_le hb s t'
    ((le_max_left _ _).trans hst.le) ((le_max_right _ _).trans hst.le) g).trans_lt (hg t')

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
      (fun c ↦ by simp [taylorHom_polynomialHom]) (by simp)
  exact RingHom.congr_fun heq f

/-- **Affine pullback `f(X) ↦ f(a + u X)` on open discs**, defined as Taylor translation by `a`
(`‖a‖ < R₀`) followed by rescaling by `u` (`‖u‖ * S₀ ≤ R₀`). Unlike a direct definition through
`analyticSubst`, this requires neither `NormOneClass R` nor positivity of `S₀`. -/
noncomputable def affineAlgHom {a u : R} (ha : ‖a‖ < R₀) (hu : ‖u‖ * S₀ ≤ R₀) :
    OnOpenDisc.subring R R₀ →ₐ[R] OnOpenDisc.subring R S₀ :=
  (rescaleAlgHom hu).comp (taylorAlgHom ha)

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
  have ha' : OnOpenDisc.polynomialHom (R₀ := R₀) (Polynomial.C a) = algebraMap R _ a :=
    Subtype.ext (by simp)
  rw [affineAlgHom_apply, taylorHom_polynomialHom, Polynomial.taylor_X, map_add, map_add,
    rescaleAlgHom_X, ha', AlgHom.commutes, add_comm]

/-- At centre `a = 0`, `affineAlgHom` reduces to `rescaleAlgHom`. -/
@[simp]
theorem affineAlgHom_zero_left {u : R} (h0 : ‖(0 : R)‖ < R₀) (hu : ‖u‖ * S₀ ≤ R₀) :
    affineAlgHom h0 hu = rescaleAlgHom hu := by
  have : Fact (0 < R₀) := ⟨by simpa using h0⟩
  ext f
  simp [affineAlgHom_apply]

/-- For unit scale `u = 1` on the same disc, `affineAlgHom` reduces to `taylorAlgHom`. -/
@[simp]
theorem affineAlgHom_one_right {a : R} (ha : ‖a‖ < R₀) (h1 : ‖(1 : R)‖ * R₀ ≤ R₀) :
    affineAlgHom ha h1 = taylorAlgHom ha := by
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
  have hub : ‖u‖ * ‖b‖ < R₀ := by
    rcases (norm_nonneg u).eq_or_lt with hu0 | hu0
    · simpa [← hu0] using (norm_nonneg a).trans_lt ha
    · exact (mul_lt_mul_of_pos_left hb hu0).trans_le hu
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
  (taylorAlgEquiv ha).trans (rescaleEquiv u hu huS)

/-- `affineEquiv` acts as `affineAlgHom`. -/
@[simp]
theorem coe_affineEquiv {a : R} (ha : ‖a‖ < R₀) (u : Rˣ) (hu : IsNormMulUnit (u : R))
    (huS : ‖(u : R)‖ * S₀ = R₀) (f : OnOpenDisc.subring R R₀) :
    affineEquiv ha u hu huS f = affineAlgHom ha huS.le f :=
  Subtype.ext (by simp [affineEquiv])

section AnalyticSubstComparison

variable [NormOneClass R] [Fact (0 < S₀)]

omit [CompleteSpace R] [Fact (0 < S₀)] in
/-- The affine polynomial `a + u * X` has smaller-disc Gauss norm strictly below `R₀` whenever
`‖a‖ < R₀` and `‖u‖ * S₀ ≤ R₀`. -/
theorem norm_restrict_affine_lt {a u : R} (ha : ‖a‖ < R₀) (hu : ‖u‖ * S₀ ≤ R₀)
    (s : Set.Ioo (0 : ℝ) S₀) :
    ‖restrict s (algebraMap R (OnOpenDisc.subring R S₀) a +
      algebraMap R (OnOpenDisc.subring R S₀) u * OnOpenDisc.polynomialHom Polynomial.X)‖ < R₀ := by
  have hus : ‖u‖ * s < R₀ := by
    rcases (norm_nonneg u).eq_or_lt with hu0 | hu0
    · simpa [← hu0] using (norm_nonneg a).trans_lt ha
    · exact (mul_lt_mul_of_pos_left s.2.2 hu0).trans_le hu
  have ha_norm : ‖restrict s (algebraMap R (OnOpenDisc.subring R S₀) a)‖ = ‖a‖ := by
    have h : restrict s (algebraMap R (OnOpenDisc.subring R S₀) a) =
        ⟨PowerSeries.C a, PowerSeries.isRestricted_C _ a⟩ := Subtype.ext (by simp)
    rw [h, norm_C]
  have hu_norm : ‖restrict s (algebraMap R (OnOpenDisc.subring R S₀) u)‖ = ‖u‖ := by
    have h : restrict s (algebraMap R (OnOpenDisc.subring R S₀) u) =
        ⟨PowerSeries.C u, PowerSeries.isRestricted_C _ u⟩ := Subtype.ext (by simp)
    rw [h, norm_C]
  calc ‖restrict s (algebraMap R (OnOpenDisc.subring R S₀) a +
        algebraMap R (OnOpenDisc.subring R S₀) u * OnOpenDisc.polynomialHom Polynomial.X)‖
      = ‖restrict s (algebraMap R (OnOpenDisc.subring R S₀) a) +
          restrict s (algebraMap R (OnOpenDisc.subring R S₀) u) *
            restrict s (OnOpenDisc.polynomialHom Polynomial.X)‖ := by
        rw [map_add, map_mul]
    _ ≤ max ‖restrict s (algebraMap R (OnOpenDisc.subring R S₀) a)‖
          ‖restrict s (algebraMap R (OnOpenDisc.subring R S₀) u) *
            restrict s (OnOpenDisc.polynomialHom Polynomial.X)‖ :=
        IsUltrametricDist.norm_add_le_max _ _
    _ ≤ max ‖a‖ (‖u‖ * s) := by
        rw [ha_norm]
        exact max_le_max le_rfl
          ((norm_mul_le _ _).trans_eq (by rw [hu_norm, norm_restrict_X]))
    _ < R₀ := max_lt ha hus

omit [CompleteSpace R] [Fact (0 < S₀)] in
/-- The translated coordinate `a + X` has smaller-disc Gauss norm strictly below `S₀` whenever
`‖a‖ < S₀`. -/
theorem norm_restrict_taylor_lt {a : R} (ha : ‖a‖ < S₀) (s : Set.Ioo (0 : ℝ) S₀) :
    ‖restrict s (algebraMap R (OnOpenDisc.subring R S₀) a +
      OnOpenDisc.polynomialHom Polynomial.X)‖ < S₀ := by
  have h1 : ‖(1 : R)‖ * S₀ ≤ S₀ := by simp
  simpa using norm_restrict_affine_lt ha h1 s

omit [CompleteSpace R] [Fact (0 < S₀)] in
/-- The rescaled coordinate `u * X` has smaller-disc Gauss norm strictly below `R₀ > 0` whenever
`‖u‖ * S₀ ≤ R₀`. -/
theorem norm_restrict_rescale_lt [Fact (0 < R₀)] {u : R} (hu : ‖u‖ * S₀ ≤ R₀)
    (s : Set.Ioo (0 : ℝ) S₀) :
    ‖restrict s (algebraMap R (OnOpenDisc.subring R S₀) u *
      OnOpenDisc.polynomialHom Polynomial.X)‖ < R₀ := by
  have h0 : ‖(0 : R)‖ < R₀ := by simpa using (Fact.out : 0 < R₀)
  simpa using norm_restrict_affine_lt h0 hu s

/-- **Agreement of `affineAlgHom` with `analyticSubst`.** Over a complete ultrametric ring with
`NormOneClass R`, the affine pullback `affineAlgHom ha hu` coincides with analytic substitution by
`a + u * X`. -/
theorem affineAlgHom_eq_analyticSubst {a u : R} (ha : ‖a‖ < R₀) (hu : ‖u‖ * S₀ ≤ R₀) :
    (affineAlgHom ha hu).toRingHom =
      analyticSubst (algebraMap R _ a + algebraMap R _ u * OnOpenDisc.polynomialHom Polynomial.X)
        (norm_restrict_affine_lt ha hu) := by
  refine eq_analyticSubst _ _ _ (continuous_affineAlgHom ha hu) (fun c ↦ ?_) ?_
  · have hc (V₀ : ℝ) : OnOpenDisc.polynomialHom (R₀ := V₀) (Polynomial.C c) = algebraMap R _ c :=
      Subtype.ext (by simp)
    rw [hc R₀, hc S₀]
    exact (affineAlgHom ha hu).commutes c
  · exact affineAlgHom_X ha hu

/-- **Agreement of `taylorHom` with `analyticSubst`.** -/
theorem taylorHom_eq_analyticSubst {a : R} (ha : ‖a‖ < S₀) :
    taylorHom ha =
      analyticSubst (algebraMap R _ a + OnOpenDisc.polynomialHom Polynomial.X)
        (norm_restrict_taylor_lt ha) := by
  refine eq_analyticSubst _ _ _ (continuous_taylorHom ha)
    (fun c ↦ by simp [taylorHom_polynomialHom]) ?_
  rw [taylorHom_polynomialHom, Polynomial.taylor_X, map_add, add_comm]
  congr 1
  exact Subtype.ext (by simp)

/-- **Agreement of `rescaleAlgHom` with `analyticSubst`** on nonempty open discs. -/
theorem rescaleAlgHom_eq_analyticSubst [Fact (0 < R₀)] {u : R} (hu : ‖u‖ * S₀ ≤ R₀) :
    (rescaleAlgHom hu).toRingHom =
      analyticSubst (algebraMap R _ u * OnOpenDisc.polynomialHom Polynomial.X)
        (norm_restrict_rescale_lt hu) := by
  refine eq_analyticSubst _ _ _ (continuous_rescaleAlgHom hu) (fun c ↦ ?_) (rescaleAlgHom_X hu)
  have hc (V₀ : ℝ) : OnOpenDisc.polynomialHom (R₀ := V₀) (Polynomial.C c) = algebraMap R _ c :=
    Subtype.ext (by simp)
  rw [hc R₀, hc S₀]
  exact (rescaleAlgHom hu).commutes c

end AnalyticSubstComparison

end Affine

end TauCeti.PowerSeries.OnOpenDisc
