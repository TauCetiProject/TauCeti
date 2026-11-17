/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.PowerSeries.Map
public import TauCeti.RingTheory.PowerSeries.OpenDisc.Radius

/-!
# Coefficient maps on open-disc power series

A bounded ring homomorphism `φ : R →+* S`, satisfying `‖φ x‖ ≤ C ‖x‖` for some constant `C`,
acts coefficientwise on series on the open disc of radius `R₀` without shrinking the radius:
at every smaller radius `0 < r < R₀`, multiplying `‖aₙ‖ rⁿ → 0` by `C` still tends to `0`.
No ultrametric or commutativity hypothesis is needed for this algebraic homomorphism
(`TauCeti.PowerSeries.OnOpenDisc.mapHom`), its functoriality, its kernel description, or its
surjectivity along strict surjections with linearly bounded coefficient lifts.

Over ultrametric rings, restriction to any smaller closed disc identifies `mapHom φ hφ` with the
closed-disc map `TauCeti.MvPowerSeries.restrictedMap φ hφ`. Hence `mapHom φ hφ` satisfies the
closed-disc Gauss-norm estimate `‖restrict r (mapHom φ hφ f)‖ ≤ C ‖restrict r f‖`, is uniformly
continuous for the open-disc Gauss uniformities, and is a uniform embedding when `φ` preserves
norms. Composing `mapHom φ hφ` with point evaluation evaluates open-disc series along any bounded
homomorphism into a complete normed commutative ring.

## Main definitions

* `TauCeti.PowerSeries.OnOpenDisc.mapHom`: the coefficientwise ring homomorphism on
  `OnOpenDisc.subring R R₀` induced by a bounded ring homomorphism `φ : R →+* S`.

## Main results

* `TauCeti.PowerSeries.OnOpenDisc.mapHom_eq_zero_iff`: the kernel consists of series whose
  coefficients lie in `RingHom.ker φ`.
* `TauCeti.PowerSeries.OnOpenDisc.exists_mapHom_eq_and_norm_coeff_le` and
  `TauCeti.PowerSeries.OnOpenDisc.mapHom_surjective`: linearly bounded coefficient lifts yield
  open-disc lifts with the same coefficient bound.
* `TauCeti.PowerSeries.OnOpenDisc.norm_restrict_mapHom_le` and
  `TauCeti.PowerSeries.OnOpenDisc.uniformContinuous_mapHom`: closed-disc Gauss-norm bounds and
  uniform continuity.
* `TauCeti.PowerSeries.OnOpenDisc.isUniformEmbedding_mapHom`: norm-preserving coefficient maps are
  uniform embeddings for the open-disc Gauss uniformities.
* `TauCeti.PowerSeries.OnOpenDisc.hasSum_evalAt_mapHom` and
  `TauCeti.PowerSeries.OnOpenDisc.norm_evalAt_mapHom_le`: convergent evaluation and Gauss-norm
  bounds along bounded coefficient homomorphisms.

## References

* P. Colmez, *Fonctions d'une variable p-adique*, Astérisque 330 (2010), §I.4.
* S. Bosch, U. Güntzer and R. Remmert, *Non-Archimedean Analysis*, Grundlehren 261, §5.1.
-/

public section

open Filter PowerSeries
open scoped Topology Uniformity

namespace TauCeti.PowerSeries.OnOpenDisc

section NormedRing

variable {R S T : Type*} [NormedRing R] [NormedRing S] [NormedRing T] {R₀ S₀ : ℝ}
  (φ : R →+* S) {C : ℝ} (hφ : ∀ x, ‖φ x‖ ≤ C * ‖x‖)

/-- Coefficientwise application of a bounded ring homomorphism `φ : R →+* S` to series on the open
disc of radius `R₀`. Neither commutativity nor an ultrametric norm is required. -/
noncomputable def mapHom :
    OnOpenDisc.subring R R₀ →+* OnOpenDisc.subring S R₀ where
  toFun f := ⟨PowerSeries.map φ (f : R⟦X⟧),
    OnOpenDisc.mem_subring.mpr ((OnOpenDisc.mem_subring.mp f.2).map φ hφ)⟩
  map_one' := Subtype.ext (map_one (PowerSeries.map φ))
  map_mul' f g := Subtype.ext (map_mul (PowerSeries.map φ) (f : R⟦X⟧) g)
  map_zero' := Subtype.ext (map_zero (PowerSeries.map φ))
  map_add' f g := Subtype.ext (map_add (PowerSeries.map φ) (f : R⟦X⟧) g)

/-- `mapHom` acts as `PowerSeries.map φ` on the underlying formal power series. -/
@[simp]
theorem coe_mapHom (f : OnOpenDisc.subring R R₀) :
    (mapHom φ hφ f : S⟦X⟧) = PowerSeries.map φ (f : R⟦X⟧) :=
  (rfl)

/-- `mapHom` applies `φ` to each coefficient. -/
theorem coeff_mapHom (f : OnOpenDisc.subring R R₀) (n : ℕ) :
    coeff n (mapHom φ hφ f : S⟦X⟧) = φ (coeff n (f : R⟦X⟧)) :=
  coeff_map φ n (f : R⟦X⟧)

/-- A series lies in the kernel of `mapHom φ hφ` if and only if all of its coefficients lie in
`RingHom.ker φ`. -/
theorem mapHom_eq_zero_iff (f : OnOpenDisc.subring R R₀) :
    mapHom φ hφ f = 0 ↔ ∀ n, coeff n (f : R⟦X⟧) ∈ RingHom.ker φ := by
  rw [Subtype.ext_iff, ZeroMemClass.coe_zero, PowerSeries.ext_iff]
  simp [RingHom.mem_ker]

/-- `mapHom` maps constant series by applying `φ` to the constant. -/
theorem mapHom_C (a : R) :
    mapHom (R₀ := R₀) φ hφ (OnOpenDisc.polynomialHom (Polynomial.C a)) =
      OnOpenDisc.polynomialHom (Polynomial.C (φ a)) :=
  Subtype.ext (by simp)

/-- `mapHom` fixes the variable `X`. -/
theorem mapHom_X :
    mapHom (R₀ := R₀) φ hφ (OnOpenDisc.polynomialHom Polynomial.X) =
      OnOpenDisc.polynomialHom Polynomial.X :=
  Subtype.ext (by simp)

/-- Bounded coefficient maps commute with polynomial inclusion. -/
@[simp]
theorem mapHom_polynomialHom (p : Polynomial R) :
    mapHom (R₀ := R₀) φ hφ (OnOpenDisc.polynomialHom p) =
      OnOpenDisc.polynomialHom (p.map φ) :=
  Subtype.ext <| PowerSeries.ext fun n ↦ by simp

/-- Bounded coefficient maps commute with radius restriction between open discs. -/
@[simp]
theorem radiusHom_mapHom (h : S₀ ≤ R₀) (f : OnOpenDisc.subring R R₀) :
    radiusHom h (mapHom φ hφ f) = mapHom φ hφ (radiusHom h f) :=
  Subtype.ext (by simp)

/-- An injective bounded coefficient homomorphism induces an injective map on open-disc series. -/
theorem mapHom_injective (hinj : Function.Injective φ) :
    Function.Injective (mapHom (R₀ := R₀) φ hφ) := by
  intro f g h
  apply Subtype.ext
  ext n
  exact hinj (by
    simpa only [coeff_mapHom] using
      congrArg (fun q : OnOpenDisc.subring S R₀ ↦ coeff n (q : S⟦X⟧)) h)

/-- Linearly bounded coefficient lifts along `φ` produce an open-disc lift satisfying the same
coefficientwise norm bound. -/
theorem exists_mapHom_eq_and_norm_coeff_le {C' : ℝ}
    (hlift : ∀ s, ∃ r, φ r = s ∧ ‖r‖ ≤ C' * ‖s‖) (g : OnOpenDisc.subring S R₀) :
    ∃ f : OnOpenDisc.subring R R₀, mapHom φ hφ f = g ∧
      ∀ n, ‖coeff n (f : R⟦X⟧)‖ ≤ C' * ‖coeff n (g : S⟦X⟧)‖ := by
  choose r hr hrn using hlift
  let f : R⟦X⟧ := mk fun n ↦ r (coeff n (g : S⟦X⟧))
  have hf : f.OnOpenDisc R₀ := onOpenDisc_iff.mpr fun ρ hρ hρR ↦ by
    rw [isRestricted_iff']
    have hgρ : Tendsto (fun n ↦ max C' 0 * (‖coeff n (g : S⟦X⟧)‖ * ρ ^ n)) atTop (𝓝 0) := by
      simpa only [mul_zero] using
        (((isRestricted_iff' ρ (g : S⟦X⟧)).mp
          ((onOpenDisc_iff.mp (OnOpenDisc.mem_subring.mp g.2)) ρ hρ hρR)).const_mul (max C' 0))
    refine squeeze_zero (fun n ↦ by positivity) (fun n ↦ ?_) hgρ
    rw [coeff_mk, ← mul_assoc]
    exact mul_le_mul_of_nonneg_right
      ((hrn _).trans (mul_le_mul_of_nonneg_right (le_max_left C' 0) (norm_nonneg _)))
      (by positivity)
  refine ⟨⟨f, OnOpenDisc.mem_subring.mpr hf⟩, Subtype.ext ?_, fun n ↦ ?_⟩
  · ext n
    simp [f, hr]
  · simpa [f] using hrn (coeff n (g : S⟦X⟧))

/-- **Open-disc series along a strict surjection.** If every element of `S` lifts along `φ` with a
linear norm bound, then `mapHom φ hφ` is surjective. -/
theorem mapHom_surjective {C' : ℝ} (hlift : ∀ s, ∃ r, φ r = s ∧ ‖r‖ ≤ C' * ‖s‖) :
    Function.Surjective (mapHom (R₀ := R₀) φ hφ) := fun g ↦
  (exists_mapHom_eq_and_norm_coeff_le φ hφ hlift g).imp fun _ hf ↦ hf.1

/-- The identity coefficient homomorphism induces the identity on open-disc series. -/
@[simp]
theorem mapHom_id {C₁ : ℝ} (hC₁ : ∀ x : R, ‖RingHom.id R x‖ ≤ C₁ * ‖x‖) :
    mapHom (R₀ := R₀) (RingHom.id R) hC₁ = RingHom.id _ :=
  RingHom.ext fun _ ↦ Subtype.ext <| PowerSeries.ext fun _ ↦ by simp

/-- `mapHom` is functorial under composition of bounded ring homomorphisms. -/
theorem mapHom_comp (ψ : S →+* T) {C₂ C₃ : ℝ} (hψ : ∀ y, ‖ψ y‖ ≤ C₂ * ‖y‖)
    (hψφ : ∀ x, ‖ψ.comp φ x‖ ≤ C₃ * ‖x‖) :
    mapHom (R₀ := R₀) (ψ.comp φ) hψφ = (mapHom ψ hψ).comp (mapHom φ hφ) :=
  RingHom.ext fun _ ↦ Subtype.ext <| PowerSeries.ext fun _ ↦ by simp

/-- Applying two bounded coefficient maps in turn applies the composite homomorphism. -/
@[simp]
theorem mapHom_mapHom (ψ : S →+* T) {C₂ : ℝ} (hψ : ∀ y, ‖ψ y‖ ≤ C₂ * ‖y‖)
    (f : OnOpenDisc.subring R R₀) :
    mapHom ψ hψ (mapHom φ hφ f) =
      mapHom (ψ.comp φ) (C := max C₂ 0 * C) (fun x ↦ by
        rw [mul_assoc]
        exact (hψ (φ x)).trans <| (mul_le_mul_of_nonneg_right (le_max_left C₂ 0)
          (norm_nonneg _)).trans <| mul_le_mul_of_nonneg_left (hφ x) (le_max_right C₂ 0)) f :=
  Subtype.ext <| PowerSeries.ext fun _ ↦ by simp

end NormedRing

section NormedCommRing

variable {R S : Type*} [NormedCommRing R] [NormedCommRing S] {R₀ S₀ : ℝ}
  (φ : R →+* S) {C : ℝ} (hφ : ∀ x, ‖φ x‖ ≤ C * ‖x‖)

/-- Bounded coefficient maps act on scalar multiples by applying `φ` to the scalar. -/
@[simp]
theorem mapHom_smul (a : R) (f : OnOpenDisc.subring R R₀) :
    mapHom φ hφ (a • f) = φ a • mapHom φ hφ f :=
  Subtype.ext <| by
    ext n
    simp

/-- Bounded coefficient maps commute with variable rescaling whenever both rescaling bounds hold. -/
theorem mapHom_rescaleHom (u : R) (hu : ‖u‖ * S₀ ≤ R₀) (hφu : ‖φ u‖ * S₀ ≤ R₀)
    (f : OnOpenDisc.subring R R₀) :
    mapHom φ hφ (rescaleHom u hu f) = rescaleHom (φ u) hφu (mapHom φ hφ f) :=
  Subtype.ext (by simp [rescale_map])

end NormedCommRing

section Evaluation

variable {R S : Type*} [NormedRing R] [NormedCommRing S] [CompleteSpace S] {R₀ : ℝ}
  (φ : R →+* S) {C : ℝ} (hφ : ∀ x, ‖φ x‖ ≤ C * ‖x‖)

/-- Evaluating the `φ`-mapped open-disc series at `b` with `‖b‖ < R₀` sums `φ(aₙ) bⁿ`. Even a
non-contractive bounded `φ` evaluates on the full open disc of radius `R₀`, and `R` need not be
commutative. -/
theorem hasSum_evalAt_mapHom {b : S} (hb : ‖b‖ < R₀) (f : OnOpenDisc.subring R R₀) :
    HasSum (fun n ↦ φ (coeff n (f : R⟦X⟧)) * b ^ n) ((mapHom φ hφ f : S⟦X⟧).evalAt b) := by
  simpa only [coe_mapHom, coeff_map, smul_eq_mul] using
    (OnOpenDisc.mem_subring.mp (mapHom φ hφ f).2).hasSum_evalAt hb

end Evaluation

section Ultrametric

variable {R S : Type*} [NormedRing R] [IsUltrametricDist R]
  [NormedRing S] [IsUltrametricDist S] {R₀ : ℝ}
  (φ : R →+* S) {C : ℝ} (hφ : ∀ x, ‖φ x‖ ≤ C * ‖x‖)

attribute [local instance] radius_pos

/-- Restricting `mapHom φ hφ` to a smaller closed disc agrees with `restrictedMap φ hφ`. -/
@[simp]
theorem restrict_mapHom (r : Set.Ioo (0 : ℝ) R₀) (f : OnOpenDisc.subring R R₀) :
    restrict r (mapHom φ hφ f) = TauCeti.MvPowerSeries.restrictedMap φ hφ (restrict r f) :=
  Subtype.ext (by simp [TauCeti.PowerSeries.coe_restrictedMap_powerSeries])

/-- On each smaller closed disc, `mapHom φ hφ` scales the Gauss norm by at most `C`. -/
theorem norm_restrict_mapHom_le (r : Set.Ioo (0 : ℝ) R₀) (f : OnOpenDisc.subring R R₀) :
    ‖restrict r (mapHom φ hφ f)‖ ≤ C * ‖restrict r f‖ := by
  rw [restrict_mapHom]
  exact TauCeti.MvPowerSeries.norm_restrictedMap_le φ hφ (restrict r f)

/-- A norm-preserving coefficient homomorphism preserves every smaller closed-disc Gauss norm. -/
theorem norm_restrict_mapHom (hφ' : ∀ x, ‖φ x‖ = ‖x‖) (r : Set.Ioo (0 : ℝ) R₀)
    (f : OnOpenDisc.subring R R₀) :
    ‖restrict r (mapHom φ hφ f)‖ = ‖restrict r f‖ := by
  rw [restrict_mapHom]
  exact TauCeti.MvPowerSeries.norm_restrictedMap φ hφ hφ' (restrict r f)

/-- Bounded coefficient maps are uniformly continuous for the open-disc Gauss uniformities. -/
theorem uniformContinuous_mapHom :
    UniformContinuous (mapHom (R₀ := R₀) φ hφ) := by
  refine uniformContinuous_iff.mpr fun r ↦ ?_
  have heq : (fun f : OnOpenDisc.subring R R₀ ↦ restrict r (mapHom φ hφ f)) =
      fun f ↦ TauCeti.MvPowerSeries.restrictedMap φ hφ (restrict r f) :=
    funext (restrict_mapHom φ hφ r)
  rw [heq]
  exact (TauCeti.MvPowerSeries.lipschitzWith_restrictedMap φ hφ).uniformContinuous.comp
    (uniformContinuous_restrict r)

/-- Bounded coefficient maps are continuous for the open-disc Gauss topologies. -/
@[continuity]
theorem continuous_mapHom :
    Continuous (mapHom (R₀ := R₀) φ hφ) :=
  (uniformContinuous_mapHom φ hφ).continuous

/-- A norm-preserving coefficient homomorphism is uniformly inducing for the open-disc Gauss
uniformities. -/
theorem isUniformInducing_mapHom (hφ' : ∀ x, ‖φ x‖ = ‖x‖) :
    IsUniformInducing (mapHom (R₀ := R₀) φ hφ) := by
  rw [isUniformInducing_iff,
    ← (isUniformInducing_restrictFamily (R := S) (R₀ := R₀)).comap_uniformity,
    ← (isUniformInducing_restrictFamily (R := R) (R₀ := R₀)).comap_uniformity]
  simp only [Pi.uniformity, comap_iInf, comap_comap]
  congr 1
  funext r
  let e : IsRestricted.subring (R := R) (r : ℝ) →+* IsRestricted.subring (R := S) (r : ℝ) :=
    TauCeti.MvPowerSeries.restrictedMap φ hφ
  have he : Isometry e :=
    AddMonoidHomClass.isometry_iff_norm e |>.mpr fun g ↦
      TauCeti.MvPowerSeries.norm_restrictedMap φ hφ hφ' g
  have heq (h : OnOpenDisc.subring R R₀) : restrict r (mapHom φ hφ h) = e (restrict r h) :=
    restrict_mapHom φ hφ r h
  conv_rhs => rw [← he.isUniformInducing.comap_uniformity, comap_comap]
  congr 1
  funext ⟨f, g⟩
  simp only [Function.comp_apply, restrictFamily_apply, heq]

/-- A norm-preserving coefficient homomorphism is a uniform embedding of open-disc algebras. -/
theorem isUniformEmbedding_mapHom (hφ' : ∀ x, ‖φ x‖ = ‖x‖) :
    IsUniformEmbedding (mapHom (R₀ := R₀) φ hφ) := by
  refine ⟨isUniformInducing_mapHom φ hφ hφ', mapHom_injective φ hφ fun x y hxy ↦ ?_⟩
  apply sub_eq_zero.mp
  apply norm_eq_zero.mp
  rw [← hφ', map_sub, hxy, sub_self, norm_zero]

end Ultrametric

section UltrametricEval

variable {R S : Type*} [NormedRing R] [IsUltrametricDist R]
  [NormedCommRing S] [IsUltrametricDist S] [NormOneClass S] {R₀ : ℝ}
  (φ : R →+* S) {C : ℝ} (hφ : ∀ x, ‖φ x‖ ≤ C * ‖x‖)

attribute [local instance] radius_pos

/-- Evaluating a `φ`-mapped open-disc series at `b` in an ultrametric algebra with `‖1‖ = 1` is
bounded by `C` times any smaller closed-disc Gauss norm whose radius bounds `‖b‖`. -/
theorem norm_evalAt_mapHom_le {b : S} (r : Set.Ioo (0 : ℝ) R₀) (hbr : ‖b‖ ≤ r)
    (f : OnOpenDisc.subring R R₀) :
    ‖(mapHom φ hφ f : S⟦X⟧).evalAt b‖ ≤ C * ‖restrict r f‖ := by
  have hf := TauCeti.PowerSeries.hasGaussNorm_of_isRestricted (restrict r (mapHom φ hφ f)).2
  rw [coe_restrict] at hf
  calc ‖(mapHom φ hφ f : S⟦X⟧).evalAt b‖
      ≤ (mapHom φ hφ f : S⟦X⟧).gaussNorm norm r := norm_evalAt_le_gaussNorm hf hbr
    _ = ‖restrict r (mapHom φ hφ f)‖ := by
        rw [TauCeti.PowerSeries.norm_eq_gaussNorm, coe_restrict]
    _ ≤ C * ‖restrict r f‖ := norm_restrict_mapHom_le φ hφ r f

end UltrametricEval

end TauCeti.PowerSeries.OnOpenDisc
