/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.MvPowerSeries.Rescale
public import TauCeti.RingTheory.PowerSeries.Entire.Topology
public import TauCeti.RingTheory.PowerSeries.OpenDisc.Eval
import TauCeti.RingTheory.PowerSeries.Rescale

/-!
# Radius restriction, inclusions, and rescaling on open discs

An open disc of radius `S₀` inside an open disc of radius `R₀` induces a restriction homomorphism
`TauCeti.PowerSeries.OnOpenDisc.radiusHom` from `OnOpenDisc.subring R R₀` to
`OnOpenDisc.subring R S₀`. Together with the inclusions from entire series (`IsEntire.subring R`)
and from series restricted on the boundary circle (`IsRestricted.subring R₀`), these homomorphisms
are uniformly continuous for the Gauss topologies and have dense image, since each source subring
already contains the polynomials.

Multiplying the variable by a scalar `u` with `‖u‖ S₀ ≤ R₀` defines the rescaling homomorphism
`TauCeti.PowerSeries.OnOpenDisc.rescaleHom`, sending `f(X)` to `f(u X)` from the open disc of
radius `R₀` to that of radius `S₀`. Over an ultrametric ring with `0 < R₀`, rescaling is uniformly
continuous and controlled on smaller closed discs without assuming `‖1‖ = 1`. When `u` is a
multiplicative unit (`TauCeti.IsNormMulUnit`) with `‖u‖ S₀ = R₀`, rescaling is a ring equivalence
`TauCeti.PowerSeries.OnOpenDisc.rescaleEquiv` that identifies the smaller closed-disc Gauss norms
and induces a uniform equivalence `TauCeti.PowerSeries.OnOpenDisc.rescaleUniformEquiv` when both
radii are positive.

## Main definitions

* `TauCeti.PowerSeries.OnOpenDisc.radiusHom`: restriction of open-disc series from radius `R₀` to a
  smaller radius `S₀ ≤ R₀`.
* `TauCeti.PowerSeries.OnOpenDisc.rescaleHom`: variable rescaling `f(X) ↦ f(u X)` along a bound
  `‖u‖ S₀ ≤ R₀`.
* `TauCeti.PowerSeries.OnOpenDisc.rescaleEquiv` and
  `TauCeti.PowerSeries.OnOpenDisc.rescaleUniformEquiv`: the ring and uniform equivalences attached
  to a multiplicative unit `u` with `‖u‖ S₀ = R₀`.

## Main results

* `TauCeti.PowerSeries.OnOpenDisc.uniformContinuous_radiusHom` and
  `TauCeti.PowerSeries.OnOpenDisc.denseRange_radiusHom`: radius restriction is uniformly continuous
  with dense image.
* `TauCeti.PowerSeries.OnOpenDisc.uniformContinuous_inclusion_entire`,
  `TauCeti.PowerSeries.OnOpenDisc.denseRange_inclusion_entire`,
  `TauCeti.PowerSeries.OnOpenDisc.uniformContinuous_inclusion_isRestricted`, and
  `TauCeti.PowerSeries.OnOpenDisc.denseRange_inclusion_isRestricted`: uniform continuity and
  density for the inclusions from entire and closed-disc restricted series.
* `TauCeti.PowerSeries.OnOpenDisc.norm_restrict_rescaleHom_le` and
  `TauCeti.PowerSeries.OnOpenDisc.uniformContinuous_rescaleHom`: closed-disc Gauss bounds and
  uniform continuity for rescaling.
* `TauCeti.PowerSeries.OnOpenDisc.norm_restrict_rescaleEquiv`: multiplicative-unit rescaling
  identifies the closed-disc Gauss norms at radii `s` and `‖u‖ s`.

## References

* P. Colmez, *Fonctions d'une variable p-adique*, Astérisque 330 (2010), §I.4.
* S. Bosch, U. Güntzer and R. Remmert, *Non-Archimedean Analysis*, Grundlehren 261, §5.1.
-/

public section

open Filter PowerSeries
open scoped Topology

namespace TauCeti.PowerSeries.OnOpenDisc

section RadiusHom

variable {R : Type*} [NormedRing R] {R₀ S₀ T₀ : ℝ}

/-- Restrict series on the open disc of radius `R₀` to a smaller open disc of radius `S₀ ≤ R₀`. -/
noncomputable def radiusHom (h : S₀ ≤ R₀) :
    OnOpenDisc.subring R R₀ →+* OnOpenDisc.subring R S₀ :=
  Subring.inclusion (OnOpenDisc.subring_antitone R h)

/-- Radius restriction leaves the underlying formal power series unchanged. -/
@[simp]
theorem coe_radiusHom (h : S₀ ≤ R₀) (f : OnOpenDisc.subring R R₀) :
    (radiusHom h f : R⟦X⟧) = f :=
  (rfl)

/-- Radius restriction between open discs is injective, since it preserves every coefficient. -/
theorem radiusHom_injective (h : S₀ ≤ R₀) :
    Function.Injective (radiusHom (R := R) h) :=
  Subring.inclusion_injective _

/-- Restricting an open disc to its own radius is the identity. -/
@[simp]
theorem radiusHom_self (f : OnOpenDisc.subring R R₀) :
    radiusHom le_rfl f = f :=
  Subtype.ext (by simp)

/-- Radius restrictions compose transitively. -/
@[simp]
theorem radiusHom_comp_radiusHom (h₁ : T₀ ≤ S₀) (h₂ : S₀ ≤ R₀) :
    (radiusHom (R := R) h₁).comp (radiusHom h₂) = radiusHom (h₁.trans h₂) := by
  ext f : 1
  exact Subtype.ext (by simp)

/-- Applying two radius restrictions in turn is restricting directly to the smallest radius. -/
@[simp]
theorem radiusHom_radiusHom (h₁ : T₀ ≤ S₀) (h₂ : S₀ ≤ R₀) (f : OnOpenDisc.subring R R₀) :
    radiusHom h₁ (radiusHom h₂ f) = radiusHom (h₁.trans h₂) f :=
  Subtype.ext (by simp)

/-- Radius restriction commutes with the inclusion of polynomials. -/
@[simp]
theorem radiusHom_polynomialHom (h : S₀ ≤ R₀) (p : Polynomial R) :
    radiusHom h (OnOpenDisc.polynomialHom p) = OnOpenDisc.polynomialHom p :=
  Subtype.ext (by simp)

/-- Radius restriction commutes with scalar multiplication from any base algebra. -/
@[simp]
theorem radiusHom_smul {S : Type*} [CommSemiring S] [Algebra S R] (h : S₀ ≤ R₀) (s : S)
    (f : OnOpenDisc.subring R R₀) :
    radiusHom h (s • f) = s • radiusHom h f :=
  Subtype.ext (by simp)

end RadiusHom

section EvalRadiusHom

variable {R A : Type*} [NormedCommRing R] [NormedRing A] [Algebra R A] [IsBoundedSMul R A]
  [CompleteSpace A] {R₀ S₀ : ℝ} {b : A}

/-- Restricting to a smaller open disc containing `b` and evaluating there agrees with evaluation on
the larger open disc. -/
theorem evalAtHom_comp_radiusHom (hb : ‖b‖ < S₀) (h : S₀ ≤ R₀) :
    (OnOpenDisc.evalAtHom R hb).comp (radiusHom h) = OnOpenDisc.evalAtHom R (hb.trans_le h) := by
  ext f
  simp

end EvalRadiusHom

section RescaleHom

variable {R : Type*} [NormedCommRing R] {R₀ S₀ T₀ : ℝ}

/-- Rescaling the variable by `u` carries series on the open disc of radius `R₀` to series on the
open disc of radius `S₀` whenever `‖u‖ * S₀ ≤ R₀`. -/
noncomputable def rescaleHom (u : R) (hu : ‖u‖ * S₀ ≤ R₀) :
    OnOpenDisc.subring R R₀ →+* OnOpenDisc.subring R S₀ where
  toFun f := ⟨PowerSeries.rescale u (f : R⟦X⟧),
    OnOpenDisc.mem_subring.mpr (((OnOpenDisc.mem_subring.mp f.2).mono hu).rescale)⟩
  map_one' := Subtype.ext (map_one (PowerSeries.rescale u))
  map_mul' f g := Subtype.ext (map_mul (PowerSeries.rescale u) (f : R⟦X⟧) g)
  map_zero' := Subtype.ext (map_zero (PowerSeries.rescale u))
  map_add' f g := Subtype.ext (map_add (PowerSeries.rescale u) (f : R⟦X⟧) g)

/-- The underlying formal power series of `rescaleHom u hu f` is `PowerSeries.rescale u f`. -/
@[simp]
theorem coe_rescaleHom (u : R) (hu : ‖u‖ * S₀ ≤ R₀) (f : OnOpenDisc.subring R R₀) :
    (rescaleHom u hu f : R⟦X⟧) = PowerSeries.rescale u (f : R⟦X⟧) :=
  (rfl)

/-- Rescaling multiplies the `n`th coefficient by `u ^ n`. -/
theorem coeff_rescaleHom (u : R) (hu : ‖u‖ * S₀ ≤ R₀) (f : OnOpenDisc.subring R R₀) (n : ℕ) :
    coeff n (rescaleHom u hu f : R⟦X⟧) = u ^ n * coeff n (f : R⟦X⟧) :=
  coeff_rescale (f : R⟦X⟧) u n

/-- Rescaling fixes constant series. -/
@[simp]
theorem rescaleHom_C (u : R) (hu : ‖u‖ * S₀ ≤ R₀) (a : R) :
    rescaleHom u hu (OnOpenDisc.polynomialHom (Polynomial.C a)) =
      OnOpenDisc.polynomialHom (Polynomial.C a) :=
  Subtype.ext (by simp)

/-- Rescaling sends the variable `X` to `u X`. -/
@[simp]
theorem rescaleHom_X (u : R) (hu : ‖u‖ * S₀ ≤ R₀) :
    rescaleHom u hu (OnOpenDisc.polynomialHom Polynomial.X) =
      OnOpenDisc.polynomialHom (Polynomial.C u * Polynomial.X) :=
  Subtype.ext (by simp [rescale_X])

/-- Rescaling commutes with scalar multiplication from any base algebra. -/
@[simp]
theorem rescaleHom_smul {S : Type*} [CommSemiring S] [Algebra S R] (u : R) (hu : ‖u‖ * S₀ ≤ R₀)
    (s : S) (f : OnOpenDisc.subring R R₀) :
    rescaleHom u hu (s • f) = s • rescaleHom u hu f :=
  Subtype.ext <| by
    ext n
    simp [Algebra.smul_def, mul_left_comm]

/-- Rescaling by `0` extracts the constant coefficient as a constant series. -/
theorem rescaleHom_zero (hu : ‖(0 : R)‖ * S₀ ≤ R₀) (f : OnOpenDisc.subring R R₀) :
    rescaleHom 0 hu f = OnOpenDisc.polynomialHom (Polynomial.C (constantCoeff (f : R⟦X⟧))) :=
  Subtype.ext (by simp)

/-- Rescaling by `1` at the same radius is the identity. -/
@[simp]
theorem rescaleHom_one [NormOneClass R] (f : OnOpenDisc.subring R R₀) :
    rescaleHom (1 : R) (by simp) f = f :=
  Subtype.ext (by simp)

/-- Rescaling homomorphisms compose by multiplying their scalars. -/
theorem rescaleHom_comp_rescaleHom (u v : R) (hu : ‖u‖ * S₀ ≤ R₀) (hv : ‖v‖ * T₀ ≤ S₀)
    (huv : ‖u * v‖ * T₀ ≤ R₀) :
    (rescaleHom v hv).comp (rescaleHom u hu) = rescaleHom (u * v) huv := by
  ext f : 1
  exact Subtype.ext (rescale_rescale (f : R⟦X⟧) u v)

/-- Applying two rescaling homomorphisms in turn rescales by the product of the scalars. -/
theorem rescaleHom_rescaleHom (u v : R) (hu : ‖u‖ * S₀ ≤ R₀) (hv : ‖v‖ * T₀ ≤ S₀)
    (huv : ‖u * v‖ * T₀ ≤ R₀) (f : OnOpenDisc.subring R R₀) :
    rescaleHom v hv (rescaleHom u hu f) = rescaleHom (u * v) huv f :=
  RingHom.congr_fun (rescaleHom_comp_rescaleHom u v hu hv huv) f

/-- Rescaling commutes with radius restriction on the target open disc. -/
theorem radiusHom_rescaleHom {S₁ : ℝ} (u : R) (hu : ‖u‖ * S₀ ≤ R₀) (hS : S₁ ≤ S₀)
    (hu' : ‖u‖ * S₁ ≤ R₀) (f : OnOpenDisc.subring R R₀) :
    radiusHom hS (rescaleHom u hu f) = rescaleHom u hu' f :=
  Subtype.ext (by simp)

/-- Rescaling commutes with radius restriction on the source open disc. -/
theorem rescaleHom_radiusHom {R₁ : ℝ} (u : R) (hR : R₁ ≤ R₀) (hu : ‖u‖ * S₀ ≤ R₁)
    (f : OnOpenDisc.subring R R₀) :
    rescaleHom u hu (radiusHom hR f) = rescaleHom u (hu.trans hR) f :=
  Subtype.ext (by simp)

/-- Evaluating a rescaled open-disc series at an algebra point `b` evaluates the original series at
`u • b`. -/
theorem evalAt_rescaleHom {A : Type*} [Semiring A] [Algebra R A] [TopologicalSpace A]
    (u : R) (hu : ‖u‖ * S₀ ≤ R₀) (f : OnOpenDisc.subring R R₀) (b : A) :
    (rescaleHom u hu f : R⟦X⟧).evalAt b = (f : R⟦X⟧).evalAt (u • b) :=
  evalAt_rescale (f : R⟦X⟧) u b

/-- Rescaling by a multiplicative unit `u` with `‖u‖ * S₀ = R₀` identifies the open-disc algebras at
radii `R₀` and `S₀`, with inverse given by rescaling by `u⁻¹`. -/
noncomputable def rescaleEquiv (u : Rˣ) (hu : TauCeti.IsNormMulUnit (u : R))
    (hrs : ‖(u : R)‖ * S₀ = R₀) :
    OnOpenDisc.subring R R₀ ≃+* OnOpenDisc.subring R S₀ :=
  RingEquiv.ofRingHom (rescaleHom (u : R) hrs.le)
    { toFun := fun f ↦ ⟨PowerSeries.rescale ((u⁻¹ : Rˣ) : R) (f : R⟦X⟧),
        OnOpenDisc.mem_subring.mpr <| by
          by_cases hu0 : ‖(u : R)‖ = 0
          · rw [hu0, zero_mul] at hrs
            exact onOpenDisc_of_nonpos hrs.symm.le _
          · have hnorm : ‖((u⁻¹ : Rˣ) : R)‖ * R₀ ≤ S₀ := by
              rw [TauCeti.NormedRing.norm_units_inv_of_norm_mul hu0 hu.norm_mul, ← hrs,
                inv_mul_cancel_left₀ hu0]
            exact ((OnOpenDisc.mem_subring.mp f.2).mono hnorm).rescale⟩
      map_one' := Subtype.ext (map_one _)
      map_mul' := fun f g ↦ Subtype.ext (map_mul _ (f : R⟦X⟧) g)
      map_zero' := Subtype.ext (map_zero _)
      map_add' := fun f g ↦ Subtype.ext (map_add _ (f : R⟦X⟧) g) }
    (RingHom.ext fun f ↦ Subtype.ext <| by
      simp [RingHom.comp_apply, rescale_rescale])
    (RingHom.ext fun f ↦ Subtype.ext <| by
      simp [RingHom.comp_apply, rescale_rescale])

/-- The forward map of `rescaleEquiv` acts as `PowerSeries.rescale u` on formal power series. -/
@[simp]
theorem coe_rescaleEquiv (u : Rˣ) (hu : TauCeti.IsNormMulUnit (u : R))
    (hrs : ‖(u : R)‖ * S₀ = R₀) (f : OnOpenDisc.subring R R₀) :
    (rescaleEquiv u hu hrs f : R⟦X⟧) = PowerSeries.rescale (u : R) (f : R⟦X⟧) :=
  (rfl)

/-- The inverse of `rescaleEquiv` rescales by `u⁻¹`. -/
@[simp]
theorem coe_rescaleEquiv_symm (u : Rˣ) (hu : TauCeti.IsNormMulUnit (u : R))
    (hrs : ‖(u : R)‖ * S₀ = R₀) (f : OnOpenDisc.subring R S₀) :
    ((rescaleEquiv u hu hrs).symm f : R⟦X⟧) = PowerSeries.rescale ((u⁻¹ : Rˣ) : R) (f : R⟦X⟧) :=
  (rfl)

/-- As a ring homomorphism, `rescaleEquiv` is `rescaleHom`. -/
@[simp]
theorem toRingHom_rescaleEquiv (u : Rˣ) (hu : TauCeti.IsNormMulUnit (u : R))
    (hrs : ‖(u : R)‖ * S₀ = R₀) :
    (rescaleEquiv u hu hrs : OnOpenDisc.subring R R₀ →+* OnOpenDisc.subring R S₀) =
      rescaleHom (u : R) hrs.le :=
  (rfl)

end RescaleHom

section Ultrametric

variable {R : Type*} [NormedRing R] [IsUltrametricDist R] {R₀ S₀ : ℝ}

attribute [local instance] radius_pos

/-- Restricting to a smaller open disc and then to a closed disc of radius `s < S₀` is restricting
directly to that closed disc. -/
@[simp]
theorem restrict_radiusHom (h : S₀ ≤ R₀) (s : Set.Ioo (0 : ℝ) S₀)
    (f : OnOpenDisc.subring R R₀) :
    restrict s (radiusHom h f) = restrict ⟨s, s.2.1, s.2.2.trans_le h⟩ f :=
  Subtype.ext (by simp)

/-- Radius restriction preserves the Gauss norm on every closed disc inside the smaller open
disc. -/
theorem norm_restrict_radiusHom (h : S₀ ≤ R₀) (s : Set.Ioo (0 : ℝ) S₀)
    (f : OnOpenDisc.subring R R₀) :
    ‖restrict s (radiusHom h f)‖ = ‖restrict ⟨s, s.2.1, s.2.2.trans_le h⟩ f‖ := by
  rw [restrict_radiusHom]

/-- Radius restriction between open discs is uniformly continuous for the Gauss uniformities. -/
theorem uniformContinuous_radiusHom (h : S₀ ≤ R₀) :
    UniformContinuous (radiusHom (R := R) h) := by
  refine uniformContinuous_iff.mpr fun s ↦ ?_
  have heq : (fun x : OnOpenDisc.subring R R₀ ↦ restrict s (radiusHom h x)) =
      restrict ⟨s, s.2.1, s.2.2.trans_le h⟩ :=
    funext (restrict_radiusHom h s)
  rw [heq]
  exact uniformContinuous_restrict _

/-- Radius restriction between open discs is continuous for the Gauss topologies. -/
@[continuity]
theorem continuous_radiusHom (h : S₀ ≤ R₀) :
    Continuous (radiusHom (R := R) h) :=
  (uniformContinuous_radiusHom h).continuous

/-- Series on a larger open disc are dense in series on any smaller open disc. -/
theorem denseRange_radiusHom (h : S₀ ≤ R₀) :
    DenseRange (radiusHom (R := R) h) := by
  refine (denseRange_polynomialHom (R := R) (R₀ := S₀)).mono ?_
  rintro _ ⟨p, rfl⟩
  exact ⟨OnOpenDisc.polynomialHom p, radiusHom_polynomialHom h p⟩

/-- Restricting an entire series through an open disc to a smaller closed disc agrees with its
direct restriction from entire series. -/
@[simp]
theorem restrict_inclusion_entire (r : Set.Ioo (0 : ℝ) R₀) (f : IsEntire.subring R) :
    restrict r (Subring.inclusion (IsEntire.subring_le_onOpenDiscSubring R₀) f) =
      TauCeti.PowerSeries.IsEntire.restrict ⟨r, r.2.1⟩ f :=
  Subtype.ext (by simp)

/-- The inclusion of entire series into series on any open disc is uniformly continuous. -/
theorem uniformContinuous_inclusion_entire :
    UniformContinuous (Subring.inclusion (IsEntire.subring_le_onOpenDiscSubring (R := R) R₀)) := by
  refine uniformContinuous_iff.mpr fun r ↦ ?_
  have heq : (fun f : IsEntire.subring R ↦
      restrict r (Subring.inclusion (IsEntire.subring_le_onOpenDiscSubring R₀) f)) =
      TauCeti.PowerSeries.IsEntire.restrict ⟨r, r.2.1⟩ :=
    funext (restrict_inclusion_entire r)
  rw [heq]
  exact TauCeti.PowerSeries.IsEntire.uniformContinuous_restrict ⟨r, r.2.1⟩

/-- The inclusion of entire series into series on any open disc is continuous. -/
@[continuity]
theorem continuous_inclusion_entire :
    Continuous (Subring.inclusion (IsEntire.subring_le_onOpenDiscSubring (R := R) R₀)) :=
  uniformContinuous_inclusion_entire.continuous

/-- Entire series are dense in series on any open disc. -/
theorem denseRange_inclusion_entire :
    DenseRange (Subring.inclusion (IsEntire.subring_le_onOpenDiscSubring (R := R) R₀)) := by
  refine (denseRange_polynomialHom (R := R) (R₀ := R₀)).mono ?_
  rintro _ ⟨p, rfl⟩
  exact ⟨IsEntire.polynomialHom p, Subtype.ext (by simp)⟩

/-- Restricting a boundary-restricted series through the open disc to a smaller closed disc agrees
with closed-disc radius restriction. -/
@[simp]
theorem restrict_inclusion_isRestricted (r : Set.Ioo (0 : ℝ) R₀)
    (f : IsRestricted.subring (R := R) R₀) :
    restrict r (Subring.inclusion (IsRestricted.subring_le_onOpenDiscSubring R₀) f) =
      TauCeti.PowerSeries.restrictedRadiusHom r.2.1.le r.2.2.le f :=
  Subtype.ext (by simp)

/-- Series restricted at `R₀` are dense in series on the open disc of radius `R₀`. -/
theorem denseRange_inclusion_isRestricted :
    DenseRange (Subring.inclusion (IsRestricted.subring_le_onOpenDiscSubring (R := R) R₀)) := by
  refine (denseRange_polynomialHom (R := R) (R₀ := R₀)).mono ?_
  rintro _ ⟨p, rfl⟩
  exact ⟨⟨p, TauCeti.PowerSeries.isRestricted_polynomial p⟩, Subtype.ext (by simp)⟩

/-- For `0 < R₀`, the inclusion of series restricted at `R₀` into series on the open disc of radius
`R₀` is uniformly continuous. -/
theorem uniformContinuous_inclusion_isRestricted [Fact (0 < R₀)] :
    UniformContinuous
      (Subring.inclusion (IsRestricted.subring_le_onOpenDiscSubring (R := R) R₀)) := by
  refine uniformContinuous_iff.mpr fun r ↦ ?_
  refine AddMonoidHomClass.uniformContinuous_of_bound
    ((restrict r).toAddMonoidHom.comp
      (Subring.inclusion (IsRestricted.subring_le_onOpenDiscSubring R₀)).toAddMonoidHom) 1
    fun f ↦ ?_
  rw [one_mul, TauCeti.PowerSeries.norm_eq_gaussNorm, TauCeti.PowerSeries.norm_eq_gaussNorm]
  simpa using TauCeti.PowerSeries.gaussNorm_le_gaussNorm_of_le (fun _ ↦ norm_nonneg _)
    r.2.1.le r.2.2.le (TauCeti.PowerSeries.hasGaussNorm_of_isRestricted f.2)

/-- For `0 < R₀`, the inclusion of series restricted at `R₀` into series on the open disc of radius
`R₀` is continuous. -/
@[continuity]
theorem continuous_inclusion_isRestricted [Fact (0 < R₀)] :
    Continuous (Subring.inclusion (IsRestricted.subring_le_onOpenDiscSubring (R := R) R₀)) :=
  uniformContinuous_inclusion_isRestricted.continuous

end Ultrametric

section UltrametricRescale

variable {R : Type*} [NormedCommRing R] [IsUltrametricDist R] {R₀ S₀ : ℝ}

attribute [local instance] radius_pos

/-- On smaller closed discs, rescaling by `u` is bounded by any source closed-disc Gauss norm of
radius `r ≥ ‖u‖ s`. No `NormOneClass` hypothesis is needed. -/
theorem norm_restrict_rescaleHom_le (u : R) (hu : ‖u‖ * S₀ ≤ R₀) (s : Set.Ioo (0 : ℝ) S₀)
    (r : Set.Ioo (0 : ℝ) R₀) (husr : ‖u‖ * s ≤ r) (f : OnOpenDisc.subring R R₀) :
    ‖restrict s (rescaleHom u hu f)‖ ≤ ‖restrict r f‖ := by
  refine TauCeti.PowerSeries.norm_le_iff.mpr fun n ↦ ?_
  rcases n with _ | n
  · simpa using TauCeti.PowerSeries.norm_coeff_mul_pow_le (restrict r f) 0
  · have hs0 : 0 ≤ (s : ℝ) := s.2.1.le
    have : 0 ≤ ‖u‖ * (s : ℝ) := mul_nonneg (norm_nonneg u) hs0
    calc ‖coeff (n + 1) (restrict s (rescaleHom u hu f) : R⟦X⟧)‖ * (s : ℝ) ^ (n + 1)
        = ‖u ^ (n + 1) * coeff (n + 1) (f : R⟦X⟧)‖ * (s : ℝ) ^ (n + 1) := by
          rw [coe_restrict, coe_rescaleHom, coeff_rescale]
      _ ≤ (‖u‖ ^ (n + 1) * ‖coeff (n + 1) (f : R⟦X⟧)‖) * (s : ℝ) ^ (n + 1) := by
          gcongr
          exact (norm_mul_le _ _).trans
            (mul_le_mul_of_nonneg_right (norm_pow_le' u n.succ_pos) (norm_nonneg _))
      _ = ‖coeff (n + 1) (f : R⟦X⟧)‖ * (‖u‖ * s) ^ (n + 1) := by
          rw [mul_pow]
          ring
      _ ≤ ‖coeff (n + 1) (f : R⟦X⟧)‖ * (r : ℝ) ^ (n + 1) := by gcongr
      _ = ‖coeff (n + 1) (restrict r f : R⟦X⟧)‖ * (r : ℝ) ^ (n + 1) := by rw [coe_restrict]
      _ ≤ ‖restrict r f‖ := TauCeti.PowerSeries.norm_coeff_mul_pow_le (restrict r f) (n + 1)

/-- For `0 < R₀`, rescaling is uniformly continuous for the open-disc Gauss uniformities. -/
theorem uniformContinuous_rescaleHom [Fact (0 < R₀)] (u : R) (hu : ‖u‖ * S₀ ≤ R₀) :
    UniformContinuous (rescaleHom u hu) := by
  refine uniformContinuous_of_continuousAt_zero (rescaleHom u hu) ?_
  rw [ContinuousAt, map_zero, tendsto_iff]
  intro s
  rw [map_zero]
  have hus0 : 0 ≤ ‖u‖ * (s : ℝ) := mul_nonneg (norm_nonneg u) s.2.1.le
  have husR : ‖u‖ * (s : ℝ) < R₀ := by
    rcases (norm_nonneg u).eq_or_lt with hu0 | hu0
    · simpa [← hu0] using (Fact.out : 0 < R₀)
    · exact (mul_lt_mul_of_pos_left s.2.2 hu0).trans_le hu
  obtain ⟨r, hsr, hrR⟩ := exists_between husR
  let r' : Set.Ioo (0 : ℝ) R₀ := ⟨r, hus0.trans_lt hsr, hrR⟩
  let : Fact (0 < (r' : ℝ)) := ⟨r'.2.1⟩
  refine squeeze_zero_norm (norm_restrict_rescaleHom_le u hu s r' hsr.le) ?_
  simpa only [map_zero, norm_zero] using
    ((uniformContinuous_restrict (R := R) r').continuous.tendsto 0).norm

/-- For `0 < R₀`, rescaling is continuous for the open-disc Gauss topologies. -/
@[continuity]
theorem continuous_rescaleHom [Fact (0 < R₀)] (u : R) (hu : ‖u‖ * S₀ ≤ R₀) :
    Continuous (rescaleHom u hu) :=
  (uniformContinuous_rescaleHom u hu).continuous

/-- Rescaling by a multiplicative unit `u` with `‖u‖ * S₀ = R₀` identifies the closed-disc Gauss
norm at radius `s < S₀` with the closed-disc Gauss norm at radius `r = ‖u‖ s < R₀`. -/
theorem norm_restrict_rescaleEquiv (u : Rˣ) (hu : TauCeti.IsNormMulUnit (u : R))
    (hrs : ‖(u : R)‖ * S₀ = R₀) (s : Set.Ioo (0 : ℝ) S₀) (r : Set.Ioo (0 : ℝ) R₀)
    (hsr : ‖(u : R)‖ * s = r) (f : OnOpenDisc.subring R R₀) :
    ‖restrict s (rescaleEquiv u hu hrs f)‖ = ‖restrict r f‖ := by
  rw [TauCeti.PowerSeries.norm_eq_gaussNorm, TauCeti.PowerSeries.norm_eq_gaussNorm,
    PowerSeries.gaussNorm_eq, PowerSeries.gaussNorm_eq]
  congr 1
  funext n
  rw [coe_restrict, coe_restrict, coe_rescaleEquiv, coeff_rescale]
  simpa [PowerSeries.coeff, Finsupp.prod_single_index] using
    MvPowerSeries.norm_coeff_rescale_mul_prod (σ := Unit) (fun _ ↦ (u : R)) (fun _ ↦ hu)
      (r := fun _ ↦ (r : ℝ)) (s := fun _ ↦ (s : ℝ)) (fun _ ↦ hsr) (f : R⟦X⟧)
      (Finsupp.single () n)

/-- For positive radii `R₀` and `S₀`, rescaling by a multiplicative unit `u` with `‖u‖ * S₀ = R₀`
is a uniform equivalence between the open-disc algebras. -/
noncomputable def rescaleUniformEquiv [Fact (0 < R₀)] [Fact (0 < S₀)] (u : Rˣ)
    (hu : TauCeti.IsNormMulUnit (u : R)) (hrs : ‖(u : R)‖ * S₀ = R₀) :
    OnOpenDisc.subring R R₀ ≃ᵤ OnOpenDisc.subring R S₀ where
  toEquiv := (rescaleEquiv u hu hrs).toEquiv
  uniformContinuous_toFun := uniformContinuous_rescaleHom (u : R) hrs.le
  uniformContinuous_invFun := by
    have hu0 : ‖(u : R)‖ ≠ 0 := fun h0 ↦
      (Fact.out : 0 < R₀).ne' (by simpa [h0] using hrs.symm)
    have hinv : ‖((u⁻¹ : Rˣ) : R)‖ * R₀ ≤ S₀ := by
      rw [TauCeti.NormedRing.norm_units_inv_of_norm_mul hu0 hu.norm_mul, ← hrs,
        inv_mul_cancel_left₀ hu0]
    exact uniformContinuous_rescaleHom ((u⁻¹ : Rˣ) : R) hinv

/-- `rescaleUniformEquiv` agrees with `rescaleEquiv` on elements. -/
@[simp]
theorem rescaleUniformEquiv_apply [Fact (0 < R₀)] [Fact (0 < S₀)] (u : Rˣ)
    (hu : TauCeti.IsNormMulUnit (u : R)) (hrs : ‖(u : R)‖ * S₀ = R₀)
    (f : OnOpenDisc.subring R R₀) :
    rescaleUniformEquiv u hu hrs f = rescaleEquiv u hu hrs f :=
  (rfl)

/-- The inverse of `rescaleUniformEquiv` agrees with `(rescaleEquiv u hu hrs).symm`. -/
@[simp]
theorem rescaleUniformEquiv_symm_apply [Fact (0 < R₀)] [Fact (0 < S₀)] (u : Rˣ)
    (hu : TauCeti.IsNormMulUnit (u : R)) (hrs : ‖(u : R)‖ * S₀ = R₀)
    (g : OnOpenDisc.subring R S₀) :
    (rescaleUniformEquiv u hu hrs).symm g = (rescaleEquiv u hu hrs).symm g :=
  (rfl)

end UltrametricRescale

end TauCeti.PowerSeries.OnOpenDisc
