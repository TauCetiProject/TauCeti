/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Normed.Ring.MulUnit
public import TauCeti.RingTheory.PowerSeries.OpenDisc.Map
public import TauCeti.RingTheory.PowerSeries.Restricted.Rescale
import TauCeti.Algebra.Order.GroupWithZero.Basic

/-!
# Rescaling and affine coordinate changes on open discs

This file develops the rescaling and affine coordinate-change maps between algebras of power
series on open discs:

1. **Rescaling.** Over any normed commutative ring `R`, if `‖u‖ * S₀ ≤ R₀`, rescaling
   `f(X) ↦ f(u X)` defines an `R`-algebra homomorphism `rescaleAlgHom` from the open disc of radius
   `R₀` to that of radius `S₀`. When `u : Rˣ` is a multiplicative unit with `‖(u : R)‖ * S₀ = R₀`,
   this upgrades to an `R`-algebra isomorphism `rescaleEquiv` whose inverse rescales by `u⁻¹`.
   When `R` is ultrametric, rescaling satisfies smaller-disc Gauss estimates, is uniformly
   continuous out of nonempty open discs (`0 < R₀`), and identifies the smaller-radius Gauss norms
   at radii `s` and `‖u‖ * s` whenever `u` is norm-multiplicative (`∀ x, ‖u * x‖ = ‖u‖ * ‖x‖`).
2. **Affine coordinate changes.** Over a complete ultrametric normed commutative ring `R`,
   combining Taylor translation `taylorHom` at `a` (`‖a‖ < R₀`) with rescaling by `u`
   (`‖u‖ * S₀ ≤ R₀`) defines the continuous `R`-algebra homomorphism `affineAlgHom` pulling back
   along `X ↦ a + u X` without requiring `NormOneClass R`. Using the commutation identity
   `taylor b (rescale u g) = rescale u (taylor (u * b) g)`
   (`PowerSeries.OnOpenDisc.taylor_rescale`), affine pullbacks are contravariant in the coordinate
   composition `(X ↦ a + u X) ∘ (X ↦ b + v X) = (X ↦ (a + u b) + (u v) X)`
   (`(affineAlgHom hb hv).comp (affineAlgHom ha hu) = affineAlgHom haub huv`) and yield
   `R`-algebra isomorphisms `affineEquiv` when `u` is a multiplicative unit with
   `‖(u : R)‖ * S₀ = R₀`, with inverse pulling back along `X ↦ -u⁻¹ a + u⁻¹ X`. Without requiring
   `NormOneClass R`, `affineAlgHom` agrees with `analyticSubst` on nonempty target open discs
   (`0 < S₀`), and `rescaleAlgHom` agrees with `analyticSubst` when both open discs are nonempty
   (`0 < R₀` and `0 < S₀`).

## Main definitions

* `TauCeti.PowerSeries.OnOpenDisc.rescaleAlgHom` and `TauCeti.PowerSeries.OnOpenDisc.rescaleEquiv`:
  rescaling `f(X) ↦ f(u X)` on open discs, and the isomorphism for multiplicative units.
* `TauCeti.PowerSeries.OnOpenDisc.affineAlgHom` and `TauCeti.PowerSeries.OnOpenDisc.affineEquiv`:
  affine pullbacks `f(X) ↦ f(a + u X)` as `R`-algebra homomorphisms and isomorphisms.
* `TauCeti.PowerSeries.OnOpenDisc.rescaleUniformEquiv` and
  `TauCeti.PowerSeries.OnOpenDisc.affineHomeomorph`: the uniform equivalence and homeomorphism
  induced by multiplicative-unit rescalings out of nonempty open discs and by affine
  automorphisms.

## Main results

* `TauCeti.PowerSeries.OnOpenDisc.norm_restrict_rescaleAlgHom_le`,
  `TauCeti.PowerSeries.OnOpenDisc.norm_restrict_rescaleAlgHom`,
  `TauCeti.PowerSeries.OnOpenDisc.norm_restrict_rescaleEquiv`, and
  `TauCeti.PowerSeries.OnOpenDisc.uniformContinuous_rescaleAlgHom`: Gauss bounds and uniform
  continuity of rescaling.
* `TauCeti.PowerSeries.OnOpenDisc.norm_restrict_affineEquiv`: affine automorphisms identify
  smaller closed-disc Gauss norms.
* `TauCeti.PowerSeries.OnOpenDisc.norm_restrict_C_add_C_mul_X`: the smaller closed-disc Gauss norm
  of the affine polynomial `a + u X` over any ultrametric normed ring.
* `TauCeti.PowerSeries.OnOpenDisc.evalAt_affineAlgHom`,
  `TauCeti.PowerSeries.OnOpenDisc.evalAtHom_comp_affineAlgHom`,
  `TauCeti.PowerSeries.OnOpenDisc.affineAlgHom_comp_affineAlgHom`, and
  `TauCeti.PowerSeries.OnOpenDisc.affineEquiv_symm_apply`: point evaluation, composition, and
  inversion of affine coordinate changes.
* `TauCeti.PowerSeries.OnOpenDisc.mapHom_rescaleAlgHom` and
  `TauCeti.PowerSeries.OnOpenDisc.mapHom_affineAlgHom`: naturality with bounded coefficient maps.
* `TauCeti.PowerSeries.OnOpenDisc.affineAlgHom_eq_analyticSubst` and
  `TauCeti.PowerSeries.OnOpenDisc.rescaleAlgHom_eq_analyticSubst`: agreement of affine pullbacks
  and rescaling with analytic substitution.

## References

* P. Colmez, *Fonctions d'une variable p-adique*, Astérisque 330 (2010), §I.4.
* S. Bosch, U. Güntzer and R. Remmert, *Non-Archimedean Analysis*, Grundlehren 261, §5.1.
-/

public section

open Filter PowerSeries
open scoped Topology

namespace TauCeti.PowerSeries.OnOpenDisc

section Rescale

variable {R : Type*} [NormedCommRing R] {R₀ S₀ T₀ : ℝ}

/-- **Rescaling on open discs.** If `‖u‖ * S₀ ≤ R₀`, substituting `X ↦ u * X` carries series on
the open disc of radius `R₀` to series on the open disc of radius `S₀` as an `R`-algebra
homomorphism. -/
noncomputable def rescaleAlgHom {u : R} (hu : ‖u‖ * S₀ ≤ R₀) :
    OnOpenDisc.subring R R₀ →ₐ[R] OnOpenDisc.subring R S₀ where
  toFun f := ⟨PowerSeries.rescale u (f : R⟦X⟧),
    OnOpenDisc.mem_subring.mpr (((OnOpenDisc.mem_subring.mp f.property).mono hu).rescale)⟩
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

/-- On polynomials, `rescaleAlgHom` substitutes `u * X` for `X`. -/
@[simp low]
theorem rescaleAlgHom_polynomialHom {u : R} (hu : ‖u‖ * S₀ ≤ R₀) (p : Polynomial R) :
    rescaleAlgHom hu (OnOpenDisc.polynomialHom p) =
      OnOpenDisc.polynomialHom (p.comp (Polynomial.C u * Polynomial.X)) := by
  have heq : (rescaleAlgHom hu : OnOpenDisc.subring R R₀ →+* OnOpenDisc.subring R S₀).comp
      OnOpenDisc.polynomialHom =
      OnOpenDisc.polynomialHom.comp (Polynomial.compRingHom (Polynomial.C u * Polynomial.X)) :=
    Polynomial.ringHom_ext (fun a ↦ Subtype.ext (by simp)) (Subtype.ext (by simp))
  simpa only [RingHom.comp_apply, RingHom.coe_coe, Polynomial.coe_compRingHom_apply] using
    RingHom.congr_fun heq p

/-- Rescaling by `1` at the same radius is the identity. -/
@[simp]
theorem rescaleAlgHom_one (h1 : ‖(1 : R)‖ * R₀ ≤ R₀) :
    rescaleAlgHom h1 = AlgHom.id R (OnOpenDisc.subring R R₀) :=
  AlgHom.ext fun f ↦ Subtype.ext (by simp)

/-- Rescaling by `0` evaluates at the origin. -/
@[simp]
theorem rescaleAlgHom_zero_apply (h0 : ‖(0 : R)‖ * S₀ ≤ R₀) (f : OnOpenDisc.subring R R₀) :
    rescaleAlgHom h0 f = algebraMap R _ (constantCoeff (f : R⟦X⟧)) :=
  Subtype.ext (by simp)

/-- Rescaling homomorphisms compose by multiplying their scaling factors. -/
theorem rescaleAlgHom_comp_rescaleAlgHom {u v : R} (hu : ‖u‖ * S₀ ≤ R₀) (hv : ‖v‖ * T₀ ≤ S₀)
    (huv : ‖u * v‖ * T₀ ≤ R₀) :
    (rescaleAlgHom hv).comp (rescaleAlgHom hu) = rescaleAlgHom huv :=
  AlgHom.ext fun f ↦ Subtype.ext (by simp [PowerSeries.rescale_rescale])

/-- Applying two rescaling homomorphisms in turn rescales by the product of the scalars. -/
theorem rescaleAlgHom_rescaleAlgHom {u v : R} (hu : ‖u‖ * S₀ ≤ R₀) (hv : ‖v‖ * T₀ ≤ S₀)
    (huv : ‖u * v‖ * T₀ ≤ R₀) (f : OnOpenDisc.subring R R₀) :
    rescaleAlgHom hv (rescaleAlgHom hu f) = rescaleAlgHom huv f :=
  AlgHom.congr_fun (rescaleAlgHom_comp_rescaleAlgHom hu hv huv) f

/-- Open-disc radius restriction on the target commutes with `rescaleAlgHom`. -/
@[simp]
theorem radiusHom_rescaleAlgHom {S₁ : ℝ} (hS : S₁ ≤ S₀) {u : R} (hu : ‖u‖ * S₀ ≤ R₀)
    (f : OnOpenDisc.subring R R₀) :
    radiusHom hS (rescaleAlgHom hu f) =
      rescaleAlgHom ((mul_le_mul_of_nonneg_left hS (norm_nonneg u)).trans hu) f :=
  Subtype.ext (by simp)

/-- Rescaling after open-disc radius restriction on the source rescales directly. -/
@[simp]
theorem rescaleAlgHom_radiusHom {R₁ : ℝ} (hR : R₀ ≤ R₁) {u : R} (hu : ‖u‖ * S₀ ≤ R₀)
    (f : OnOpenDisc.subring R R₁) :
    rescaleAlgHom hu (radiusHom hR f) = rescaleAlgHom (hu.trans hR) f :=
  Subtype.ext (by simp)

/-- Bounded coefficient maps intertwine `rescaleAlgHom` at `u` and at `φ u`. -/
theorem mapHom_rescaleAlgHom {S : Type*} [NormedCommRing S] (φ : R →+* S) {C : ℝ}
    (hφ : ∀ x, ‖φ x‖ ≤ C * ‖x‖) {u : R} (hu : ‖u‖ * S₀ ≤ R₀) (hφu : ‖φ u‖ * S₀ ≤ R₀)
    (f : OnOpenDisc.subring R R₀) :
    mapHom φ hφ (rescaleAlgHom hu f) = rescaleAlgHom hφu (mapHom φ hφ f) :=
  Subtype.ext <| PowerSeries.ext fun n ↦ by simp [coeff_rescale]

/-- Evaluating a rescaled open-disc series at `b` evaluates the original series at `u • b`. -/
theorem evalAt_rescaleAlgHom {A : Type*} [Semiring A] [Algebra R A] [TopologicalSpace A]
    {u : R} (hu : ‖u‖ * S₀ ≤ R₀) (f : OnOpenDisc.subring R R₀) (b : A) :
    (rescaleAlgHom hu f : R⟦X⟧).evalAt b = (f : R⟦X⟧).evalAt (u • b) := by
  rw [coe_rescaleAlgHom, PowerSeries.evalAt_rescale]

private theorem onOpenDisc_rescale_units_inv (u : Rˣ) (hu : IsNormMulUnit (u : R))
    (huS : ‖(u : R)‖ * S₀ = R₀) {g : R⟦X⟧} (hg : g.OnOpenDisc S₀) :
    (PowerSeries.rescale (((u⁻¹ : Rˣ) : R)) g).OnOpenDisc R₀ := by
  rcases le_or_gt R₀ 0 with hR₀ | hR₀
  · exact onOpenDisc_of_nonpos hR₀ _
  · exact (hg.mono (hu.norm_units_inv_mul_eq hR₀.ne' huS).le).rescale

/-- **Rescaling by a multiplicative unit is an algebra isomorphism** between the open discs of
radii `R₀` and `S₀` when `‖(u : R)‖ * S₀ = R₀`, with inverse rescaling by `u⁻¹`. -/
noncomputable def rescaleEquiv (u : Rˣ) (hu : IsNormMulUnit (u : R))
    (huS : ‖(u : R)‖ * S₀ = R₀) :
    OnOpenDisc.subring R R₀ ≃ₐ[R] OnOpenDisc.subring R S₀ :=
  { rescaleAlgHom huS.le with
    invFun g := ⟨PowerSeries.rescale (((u⁻¹ : Rˣ) : R)) (g : R⟦X⟧),
      OnOpenDisc.mem_subring.mpr <|
        onOpenDisc_rescale_units_inv u hu huS (OnOpenDisc.mem_subring.mp g.property)⟩
    left_inv f := Subtype.ext (by simp [PowerSeries.rescale_rescale])
    right_inv g := Subtype.ext (by simp [PowerSeries.rescale_rescale]) }

/-- `rescaleEquiv` acts as `rescaleAlgHom`. -/
@[simp]
theorem rescaleEquiv_apply (u : Rˣ) (hu : IsNormMulUnit (u : R)) (huS : ‖(u : R)‖ * S₀ = R₀)
    (f : OnOpenDisc.subring R R₀) :
    rescaleEquiv u hu huS f = rescaleAlgHom huS.le f := (rfl)

/-- The inverse of `rescaleEquiv` rescales by `u⁻¹` on the underlying formal series. -/
@[simp]
theorem coe_rescaleEquiv_symm (u : Rˣ) (hu : IsNormMulUnit (u : R)) (huS : ‖(u : R)‖ * S₀ = R₀)
    (g : OnOpenDisc.subring R S₀) :
    ((rescaleEquiv u hu huS).symm g : R⟦X⟧) =
      PowerSeries.rescale (((u⁻¹ : Rˣ) : R)) (g : R⟦X⟧) := (rfl)

/-- On a nonempty open disc (`0 < R₀`), the inverse of `rescaleEquiv` acts as `rescaleAlgHom` by
`u⁻¹`. -/
@[simp]
theorem rescaleEquiv_symm_apply [Fact (0 < R₀)] (u : Rˣ) (hu : IsNormMulUnit (u : R))
    (huS : ‖(u : R)‖ * S₀ = R₀) (g : OnOpenDisc.subring R S₀) :
    (rescaleEquiv u hu huS).symm g =
      rescaleAlgHom (hu.norm_units_inv_mul_eq (Fact.out : 0 < R₀).ne' huS).le g :=
  Subtype.ext (by simp)

section UltrametricRescale

variable [IsUltrametricDist R]

attribute [local instance] radius_pos

/-- Closed-to-open-disc inclusion intertwines `restrictedRescaleAlgHom` with `rescaleAlgHom`. -/
@[simp]
theorem ofIsRestricted_restrictedRescaleAlgHom {u : R} (hs : 0 ≤ S₀) (hu : ‖u‖ * S₀ ≤ R₀)
    (f : IsRestricted.subring (R := R) R₀) :
    ofIsRestricted (TauCeti.PowerSeries.restrictedRescaleAlgHom hs hu f) =
      rescaleAlgHom hu (ofIsRestricted f) :=
  Subtype.ext (by simp)

/-- Restricting a rescaled open-disc series to a smaller closed disc of radius `s` applies
`restrictedRescaleAlgHom` to the restriction at any smaller closed disc of radius `r` with
`‖u‖ * s ≤ r`. -/
theorem restrict_rescaleAlgHom {u : R} (hu : ‖u‖ * S₀ ≤ R₀)
    (s : Set.Ioo (0 : ℝ) S₀) (r : Set.Ioo (0 : ℝ) R₀) (hsr : ‖u‖ * s ≤ r)
    (f : OnOpenDisc.subring R R₀) :
    restrict s (rescaleAlgHom hu f) =
      TauCeti.PowerSeries.restrictedRescaleAlgHom s.property.1.le hsr (restrict r f) :=
  Subtype.ext (by simp)

/-- On smaller closed discs with `‖u‖ * s ≤ r`, rescaling does not increase the Gauss norm.
No `NormOneClass R` hypothesis is needed. -/
theorem norm_restrict_rescaleAlgHom_le {u : R} (hu : ‖u‖ * S₀ ≤ R₀)
    (s : Set.Ioo (0 : ℝ) S₀) (r : Set.Ioo (0 : ℝ) R₀) (hsr : ‖u‖ * s ≤ r)
    (f : OnOpenDisc.subring R R₀) :
    ‖restrict s (rescaleAlgHom hu f)‖ ≤ ‖restrict r f‖ := by
  rw [restrict_rescaleAlgHom hu s r hsr f]
  exact TauCeti.PowerSeries.norm_restrictedRescaleAlgHom_le s.property.1.le hsr (restrict r f)

/-- Rescaling by a norm-multiplicative element `u` identifies the Gauss norm at a smaller radius
`s < S₀` with the Gauss norm at `r = ‖u‖ * s < R₀`. -/
theorem norm_restrict_rescaleAlgHom {u : R} (hu : ∀ x : R, ‖u * x‖ = ‖u‖ * ‖x‖)
    (huS : ‖u‖ * S₀ ≤ R₀) (s : Set.Ioo (0 : ℝ) S₀) (r : Set.Ioo (0 : ℝ) R₀)
    (hr : (r : ℝ) = ‖u‖ * s) (f : OnOpenDisc.subring R R₀) :
    ‖restrict s (rescaleAlgHom huS f)‖ = ‖restrict r f‖ := by
  rw [restrict_rescaleAlgHom huS s r hr.symm.le f]
  exact TauCeti.PowerSeries.norm_restrictedRescaleAlgHom hu s.property.1.le hr.symm (restrict r f)

/-- Rescaling by a multiplicative unit `u` identifies the Gauss norm at a smaller radius `s < S₀`
with the Gauss norm at `r = ‖(u : R)‖ * s < R₀`. -/
theorem norm_restrict_rescaleEquiv (u : Rˣ) (hu : IsNormMulUnit (u : R))
    (huS : ‖(u : R)‖ * S₀ = R₀) (s : Set.Ioo (0 : ℝ) S₀) (r : Set.Ioo (0 : ℝ) R₀)
    (hr : (r : ℝ) = ‖(u : R)‖ * s) (f : OnOpenDisc.subring R R₀) :
    ‖restrict s (rescaleEquiv u hu huS f)‖ = ‖restrict r f‖ := by
  rw [rescaleEquiv_apply]
  exact norm_restrict_rescaleAlgHom hu.norm_mul huS.le s r hr f

/-- Rescaling out of a nonempty open disc (`0 < R₀`) is uniformly continuous for the Gauss
uniformities. -/
theorem uniformContinuous_rescaleAlgHom [Fact (0 < R₀)] {u : R} (hu : ‖u‖ * S₀ ≤ R₀) :
    UniformContinuous (rescaleAlgHom hu) := by
  refine uniformContinuous_iff.mpr fun s ↦ ?_
  obtain ⟨r, hsr, hrR⟩ :=
    exists_between (mul_lt_of_lt_of_mul_le (norm_nonneg u) Fact.out s.property.2 hu)
  let r' : Set.Ioo (0 : ℝ) R₀ := ⟨r, (mul_nonneg (norm_nonneg u) s.property.1.le).trans_lt hsr, hrR⟩
  have : Fact (0 < r) := ⟨r'.property.1⟩
  simp_rw [restrict_rescaleAlgHom hu s r' hsr.le]
  exact (TauCeti.PowerSeries.lipschitzWith_restrictedRescaleAlgHom s.property.1.le
    hsr.le).uniformContinuous.comp (uniformContinuous_restrict r')

/-- Rescaling out of a nonempty open disc (`0 < R₀`) is continuous for the Gauss topologies. -/
@[continuity]
theorem continuous_rescaleAlgHom [Fact (0 < R₀)] {u : R} (hu : ‖u‖ * S₀ ≤ R₀) :
    Continuous (rescaleAlgHom hu) :=
  (uniformContinuous_rescaleAlgHom hu).continuous

/-- Out of a nonempty open disc (`0 < R₀`), rescaling by a multiplicative unit `u` with
`‖(u : R)‖ * S₀ = R₀` is a uniform equivalence for the Gauss uniformities. -/
noncomputable def rescaleUniformEquiv [Fact (0 < R₀)] (u : Rˣ)
    (hu : IsNormMulUnit (u : R)) (huS : ‖(u : R)‖ * S₀ = R₀) :
    OnOpenDisc.subring R R₀ ≃ᵤ OnOpenDisc.subring R S₀ where
  toEquiv := (rescaleEquiv u hu huS).toEquiv
  uniformContinuous_toFun := uniformContinuous_rescaleAlgHom huS.le
  uniformContinuous_invFun := by
    have : Fact (0 < S₀) :=
      ⟨pos_of_mul_pos_right (huS ▸ Fact.out : 0 < ‖(u : R)‖ * S₀) (norm_nonneg _)⟩
    convert uniformContinuous_rescaleAlgHom
      (hu.norm_units_inv_mul_eq (Fact.out : 0 < R₀).ne' huS).le using 1
    funext g
    exact rescaleEquiv_symm_apply u hu huS g

/-- `rescaleUniformEquiv` acts as `rescaleEquiv`. -/
@[simp]
theorem rescaleUniformEquiv_apply [Fact (0 < R₀)] (u : Rˣ)
    (hu : IsNormMulUnit (u : R)) (huS : ‖(u : R)‖ * S₀ = R₀) (f : OnOpenDisc.subring R R₀) :
    rescaleUniformEquiv u hu huS f = rescaleEquiv u hu huS f := (rfl)

/-- The inverse of `rescaleUniformEquiv` acts as the inverse of `rescaleEquiv`. -/
@[simp]
theorem rescaleUniformEquiv_symm_apply [Fact (0 < R₀)] (u : Rˣ)
    (hu : IsNormMulUnit (u : R)) (huS : ‖(u : R)‖ * S₀ = R₀) (g : OnOpenDisc.subring R S₀) :
    (rescaleUniformEquiv u hu huS).symm g = (rescaleEquiv u hu huS).symm g := (rfl)

end UltrametricRescale

end Rescale

section PolynomialBounds

variable {R : Type*} [NormedRing R] [IsUltrametricDist R] {S₀ : ℝ}

attribute [local instance] radius_pos

/-- Over any ultrametric normed ring, the affine polynomial `a + u * X` has smaller-disc Gauss
norm `max ‖a‖ (‖u‖ * s)`. -/
theorem norm_restrict_C_add_C_mul_X (a u : R) (s : Set.Ioo (0 : ℝ) S₀) :
    ‖restrict s (OnOpenDisc.polynomialHom (Polynomial.C a + Polynomial.C u * Polynomial.X))‖ =
      max ‖a‖ (‖u‖ * (s : ℝ)) := by
  refine le_antisymm (TauCeti.PowerSeries.norm_le_iff.mpr fun n ↦ ?_) (max_le ?_ ?_)
  · rcases n with _ | _ | n <;> simp
  · convert TauCeti.PowerSeries.norm_coeff_mul_pow_le
      (restrict s (OnOpenDisc.polynomialHom (Polynomial.C a + Polynomial.C u * Polynomial.X))) 0
      using 1
    simp
  · convert TauCeti.PowerSeries.norm_coeff_mul_pow_le
      (restrict s (OnOpenDisc.polynomialHom (Polynomial.C a + Polynomial.C u * Polynomial.X))) 1
      using 1
    simp

end PolynomialBounds

section Affine

variable {R : Type*} [NormedCommRing R] [IsUltrametricDist R] [CompleteSpace R]
  {R₀ S₀ T₀ : ℝ}

attribute [local instance] radius_pos

/-- **Affine pullback `f(X) ↦ f(a + u X)` on open discs**, defined as Taylor translation by `a`
(`‖a‖ < R₀`) followed by rescaling by `u` (`‖u‖ * S₀ ≤ R₀`). Unlike a direct definition through
`analyticSubst`, this does not require positivity of `S₀`, and its Gauss-norm bound and composition
law avoid the `NormOneClass R` hypothesis needed by `norm_restrict_analyticSubst_le` and
`analyticSubst_comp_analyticSubst`. -/
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
  simp [affineAlgHom_apply, polynomialHom_C, add_comm]

/-- On polynomials, `affineAlgHom` substitutes `a + u * X` for `X`. -/
@[simp low]
theorem affineAlgHom_polynomialHom {a u : R} (ha : ‖a‖ < R₀) (hu : ‖u‖ * S₀ ≤ R₀)
    (p : Polynomial R) :
    affineAlgHom ha hu (OnOpenDisc.polynomialHom p) =
      OnOpenDisc.polynomialHom (p.comp (Polynomial.C a + Polynomial.C u * Polynomial.X)) := by
  rw [affineAlgHom_apply, taylorHom_polynomialHom, rescaleAlgHom_polynomialHom,
    Polynomial.taylor_apply, Polynomial.comp_assoc, Polynomial.add_comp, Polynomial.X_comp,
    Polynomial.C_comp, add_comm]

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

/-- Open-disc radius restriction on the target commutes with `affineAlgHom`. -/
@[simp]
theorem radiusHom_affineAlgHom {S₁ : ℝ} (hS : S₁ ≤ S₀) {a u : R} (ha : ‖a‖ < R₀)
    (hu : ‖u‖ * S₀ ≤ R₀) (f : OnOpenDisc.subring R R₀) :
    radiusHom hS (affineAlgHom ha hu f) =
      affineAlgHom ha ((mul_le_mul_of_nonneg_left hS (norm_nonneg u)).trans hu) f :=
  Subtype.ext (by simp)

/-- Affine pullback after open-disc radius restriction on the source pulls back directly. -/
@[simp]
theorem affineAlgHom_radiusHom {R₁ : ℝ} (hR : R₀ ≤ R₁) {a u : R} (ha : ‖a‖ < R₀)
    (hu : ‖u‖ * S₀ ≤ R₀) (f : OnOpenDisc.subring R R₁) :
    affineAlgHom ha hu (radiusHom hR f) = affineAlgHom (ha.trans_le hR) (hu.trans hR) f :=
  Subtype.ext (by simp)

/-- Bounded coefficient maps intertwine `affineAlgHom` at `(a, u)` and at `(φ a, φ u)` whenever
`‖φ a‖ < R₀` and `‖φ u‖ * S₀ ≤ R₀`. -/
theorem mapHom_affineAlgHom {S : Type*} [NormedCommRing S] [IsUltrametricDist S]
    [CompleteSpace S] (φ : R →+* S) {C : ℝ} (hφ : ∀ x, ‖φ x‖ ≤ C * ‖x‖) {a u : R}
    (ha : ‖a‖ < R₀) (hu : ‖u‖ * S₀ ≤ R₀) (hφa : ‖φ a‖ < R₀) (hφu : ‖φ u‖ * S₀ ≤ R₀)
    (f : OnOpenDisc.subring R R₀) :
    mapHom φ hφ (affineAlgHom ha hu f) = affineAlgHom hφa hφu (mapHom φ hφ f) := by
  rw [affineAlgHom_apply, mapHom_rescaleAlgHom φ hφ hu hφu, mapHom_taylorHom φ hφ ha hφa,
    ← affineAlgHom_apply]

/-- Evaluating an affine pullback `affineAlgHom ha hu f` at an algebra point `b` with `‖b‖ < S₀`
evaluates `f` at `u • b + algebraMap R A a`. -/
theorem evalAt_affineAlgHom {A : Type*} [NormedRing A] [Algebra R A] [IsBoundedSMul R A]
    [CompleteSpace A] [IsUltrametricDist A] [NormOneClass A] {a u : R} {b : A}
    (ha : ‖a‖ < R₀) (hu : ‖u‖ * S₀ ≤ R₀) (hb : ‖b‖ < S₀)
    (f : OnOpenDisc.subring R R₀) :
    (affineAlgHom ha hu f : R⟦X⟧).evalAt b =
      (f : R⟦X⟧).evalAt (u • b + algebraMap R A a) := by
  have hub : ‖u • b‖ < R₀ := (norm_smul_le u b).trans_lt
    (mul_lt_of_lt_of_mul_le (norm_nonneg u) ((norm_nonneg a).trans_lt ha) hb hu)
  rw [affineAlgHom_apply, evalAt_rescaleAlgHom, evalAt_taylorHom ha hub]

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

/-- Evaluating affine pullbacks `f(a + u X)` at an algebra point `b` with `‖b‖ < S₀` is evaluation
of `f` at `u • b + algebraMap R A a`, as ring homomorphisms. Unlike `evalAt_affineAlgHom`, this
needs neither `IsUltrametricDist A` nor `NormOneClass A`, taking the bound on the evaluation point
as a hypothesis instead. -/
theorem evalAtHom_comp_affineAlgHom {A : Type*} [NormedRing A] [Algebra R A]
    [IsBoundedSMul R A] [CompleteSpace A] {a u : R} {b : A} (ha : ‖a‖ < R₀) (hu : ‖u‖ * S₀ ≤ R₀)
    (hb : ‖b‖ < S₀) (hab : ‖u • b + algebraMap R A a‖ < R₀) :
    (OnOpenDisc.evalAtHom R hb).comp
        (affineAlgHom ha hu : OnOpenDisc.subring R R₀ →+* OnOpenDisc.subring R S₀) =
      OnOpenDisc.evalAtHom R hab := by
  refine ringHom_ext ((continuous_evalAtHom hb).comp (continuous_affineAlgHom ha hu))
    (continuous_evalAtHom hab) (fun c ↦ ?_) ?_ <;>
  simp only [RingHom.comp_apply, RingHom.coe_coe, affineAlgHom_polynomialHom,
    OnOpenDisc.evalAtHom_apply, OnOpenDisc.coe_polynomialHom, evalAt_coe]
  · simp
  · simp [Algebra.smul_def, add_comm]

/-- **Composition of affine pullbacks on open discs**: pulling back along `X ↦ a + u Y` and then
along `Y ↦ b + v Z` pulls back along `X ↦ (a + u b) + (u v) Z`. -/
theorem affineAlgHom_comp_affineAlgHom {a u b v : R} (ha : ‖a‖ < R₀) (hu : ‖u‖ * S₀ ≤ R₀)
    (hb : ‖b‖ < S₀) (hv : ‖v‖ * T₀ ≤ S₀)
    (haub : ‖a + u * b‖ < R₀) (huv : ‖u * v‖ * T₀ ≤ R₀) :
    (affineAlgHom hb hv).comp (affineAlgHom ha hu) = affineAlgHom haub huv := by
  have hub : ‖u‖ * ‖b‖ < R₀ :=
    mul_lt_of_lt_of_mul_le (norm_nonneg u) ((norm_nonneg a).trans_lt ha) hb hu
  have hub' : ‖u * b‖ < R₀ := (norm_mul_le u b).trans_lt hub
  ext f : 1
  apply Subtype.ext
  calc (affineAlgHom hb hv (affineAlgHom ha hu f) : R⟦X⟧)
      = PowerSeries.rescale v (PowerSeries.taylor b
          (PowerSeries.rescale u (PowerSeries.taylor a (f : R⟦X⟧)))) := by
          simp [coe_affineAlgHom]
    _ = PowerSeries.rescale v (PowerSeries.rescale u
          (PowerSeries.taylor (u * b) (PowerSeries.taylor a (f : R⟦X⟧)))) := by
          rw [((OnOpenDisc.mem_subring.mp f.property).taylor ha).taylor_rescale hub']
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

/-- The inverse of `affineEquiv` is the affine pullback with centre `-((u⁻¹ : Rˣ) : R) * a` and
scale `((u⁻¹ : Rˣ) : R)`. -/
@[simp]
theorem affineEquiv_symm_apply {a : R} (ha : ‖a‖ < R₀) (u : Rˣ)
    (hu : IsNormMulUnit (u : R)) (huS : ‖(u : R)‖ * S₀ = R₀)
    (g : OnOpenDisc.subring R S₀) :
    (affineEquiv ha u hu huS).symm g =
      affineAlgHom (a := -((u⁻¹ : Rˣ) : R) * a)
        (by rw [neg_mul, norm_neg]; exact hu.norm_units_inv_mul_lt ha huS)
        (hu.norm_units_inv_mul_eq ((norm_nonneg a).trans_lt ha).ne' huS).le g := by
  have hR₀ : 0 < R₀ := (norm_nonneg a).trans_lt ha
  have hinv_a : ‖((u⁻¹ : Rˣ) : R) * a‖ < S₀ := hu.norm_units_inv_mul_lt ha huS
  have hS₀ : 0 < S₀ := (norm_nonneg _).trans_lt hinv_a
  have h1 : ‖(1 : R)‖ = 1 :=
    NormedRing.norm_one_of_norm_mul (left_ne_zero_of_mul (huS.trans_ne hR₀.ne')) hu.norm_mul
  have haub : ‖-((u⁻¹ : Rˣ) : R) * a + ((u⁻¹ : Rˣ) : R) * a‖ < S₀ := by simpa using hS₀
  have huv : ‖(((u⁻¹ : Rˣ) : R)) * (u : R)‖ * S₀ ≤ S₀ := by simp [h1]
  have hcomp := AlgHom.congr_fun (affineAlgHom_comp_affineAlgHom (a := -((u⁻¹ : Rˣ) : R) * a)
    (by rw [neg_mul, norm_neg]; exact hinv_a)
    (hu.norm_units_inv_mul_eq hR₀.ne' huS).le ha huS.le haub huv) g
  rw [AlgHom.comp_apply] at hcomp
  rw [AlgEquiv.symm_apply_eq, affineEquiv_apply, hcomp]
  exact Subtype.ext (by simp [neg_mul])

/-- An affine automorphism `affineEquiv` identifies the Gauss norm at a smaller radius `s < S₀`
with the Gauss norm at `r = ‖(u : R)‖ * s < R₀`, provided the closed disc of radius `r` contains
the centre `a`. -/
theorem norm_restrict_affineEquiv {a : R} (ha : ‖a‖ < R₀) (u : Rˣ) (hu : IsNormMulUnit (u : R))
    (huS : ‖(u : R)‖ * S₀ = R₀) (s : Set.Ioo (0 : ℝ) S₀) (r : Set.Ioo (0 : ℝ) R₀)
    (har : ‖a‖ ≤ r) (hr : (r : ℝ) = ‖(u : R)‖ * s) (f : OnOpenDisc.subring R R₀) :
    ‖restrict s (affineEquiv ha u hu huS f)‖ = ‖restrict r f‖ := by
  rw [affineEquiv_apply, affineAlgHom_apply]
  exact (norm_restrict_rescaleAlgHom hu.norm_mul huS.le s r hr (taylorHom ha f)).trans
    (norm_restrict_taylorHom ha r har f)

/-- An affine automorphism `affineEquiv` is a homeomorphism for the Gauss topologies. -/
noncomputable def affineHomeomorph {a : R} (ha : ‖a‖ < R₀) (u : Rˣ)
    (hu : IsNormMulUnit (u : R)) (huS : ‖(u : R)‖ * S₀ = R₀) :
    OnOpenDisc.subring R R₀ ≃ₜ OnOpenDisc.subring R S₀ where
  toEquiv := (affineEquiv ha u hu huS).toEquiv
  continuous_toFun :=
    (continuous_affineAlgHom ha huS.le).congr fun f ↦ (affineEquiv_apply ha u hu huS f).symm
  continuous_invFun :=
    (continuous_affineAlgHom (a := -((u⁻¹ : Rˣ) : R) * a)
      (by rw [neg_mul, norm_neg]; exact hu.norm_units_inv_mul_lt ha huS)
      (hu.norm_units_inv_mul_eq ((norm_nonneg a).trans_lt ha).ne' huS).le).congr
      fun g ↦ (affineEquiv_symm_apply ha u hu huS g).symm

/-- `affineHomeomorph` acts as `affineEquiv`. -/
@[simp]
theorem affineHomeomorph_apply {a : R} (ha : ‖a‖ < R₀) (u : Rˣ)
    (hu : IsNormMulUnit (u : R)) (huS : ‖(u : R)‖ * S₀ = R₀) (f : OnOpenDisc.subring R R₀) :
    affineHomeomorph ha u hu huS f = affineEquiv ha u hu huS f := (rfl)

/-- The inverse of `affineHomeomorph` acts as the inverse of `affineEquiv`. -/
@[simp]
theorem affineHomeomorph_symm_apply {a : R} (ha : ‖a‖ < R₀) (u : Rˣ)
    (hu : IsNormMulUnit (u : R)) (huS : ‖(u : R)‖ * S₀ = R₀) (g : OnOpenDisc.subring R S₀) :
    (affineHomeomorph ha u hu huS).symm g = (affineEquiv ha u hu huS).symm g := (rfl)

section AnalyticSubstComparison

omit [CompleteSpace R] in
/-- The affine polynomial `a + u * X` has smaller-disc Gauss norm strictly below `R₀` whenever
`‖a‖ < R₀` and `‖u‖ * S₀ ≤ R₀`. No `NormOneClass R` hypothesis is needed. -/
theorem norm_restrict_algebraMap_add_algebraMap_mul_X_lt {a u : R} (ha : ‖a‖ < R₀)
    (hu : ‖u‖ * S₀ ≤ R₀) (s : Set.Ioo (0 : ℝ) S₀) :
    ‖restrict s (algebraMap R (OnOpenDisc.subring R S₀) a +
      algebraMap R (OnOpenDisc.subring R S₀) u * OnOpenDisc.polynomialHom Polynomial.X)‖ < R₀ := by
  have hus : ‖u‖ * s < R₀ :=
    mul_lt_of_lt_of_mul_le (norm_nonneg u) ((norm_nonneg a).trans_lt ha) s.property.2 hu
  refine (TauCeti.PowerSeries.norm_le_iff.mpr fun n ↦ ?_).trans_lt (max_lt ha hus)
  rcases n with _ | _ | n <;> simp

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
