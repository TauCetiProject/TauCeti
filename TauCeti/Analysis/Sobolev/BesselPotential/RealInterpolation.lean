/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.FunctionalSpaces.BesovSpace.RealInterpolation
public import TauCeti.Analysis.Sobolev.BesselPotential.Besov

/-!
# Real interpolation of Bessel-potential Sobolev spaces

Let `E` be a finite-dimensional real inner product space and `F` a complex Banach space. For
`1 ≤ p, q ≤ ∞`, distinct smoothness orders `s₀ ≠ s₁`, and `0 < θ < 1`, the real interpolation
space of two Bessel-potential spaces `H^{s₀,p}(E, F)` and `H^{s₁,p}(E, F)` is the inhomogeneous
Besov space of order `s_θ = (1 - θ) s₀ + θ s₁` and fine index `q`:

`(H^{s₀,p}(E, F), H^{s₁,p}(E, F))_{θ,q} ≃L[ℂ] B^{s_θ}_{p,q}(E, F)`.

For `p = q = 2` and values in a complex Hilbert space `H`, `B^{s_θ}_{2,2}(E, H)` agrees with
`H^{s_θ}(E, H)` (`TauCeti.BesovSpace.besselPotentialSpaceEquiv`), giving the Hilbert-space Sobolev
interpolation identity

`(H^{s₀}(E, H), H^{s₁}(E, H))_{θ,2} ≃L[ℂ] H^{s_θ}(E, H)`

with no auxiliary Littlewood–Paley bump function in its statement.

The proof follows Bergh–Löfström, Theorems 6.2.4 and 6.4.5(4), by sandwiching the Bessel-potential
couple between two Besov couples at the extreme fine indices `1` and `∞`:

* Each endpoint satisfies the continuous inclusions
  `B^{sᵢ}_{p,1}(E, F) ⊆ H^{sᵢ,p}(E, F) ⊆ B^{sᵢ}_{p,∞}(E, F)`
  (`TauCeti.BesovSpace.toBesselPotentialSpace` and `BesselPotentialSpace.toBesovSpace`).
* Lifting these inclusions to the sum spaces gives couple morphisms
  `TauCeti.CompatibleCouple.besovOneToBesselPotentialSum` and
  `TauCeti.CompatibleCouple.besselPotentialToBesovTopSum` that preserve the ambient tempered
  distribution.
* Because `(B^{s₀}_{p,q₀}, B^{s₁}_{p,q₁})_{θ,q} ≃L[ℂ] B^{s_θ}_{p,q}`
  (`TauCeti.CompatibleCouple.besovKMethodEquiv`) does not depend on `q₀` or `q₁`, both outer
  couples have the same real interpolation space `B^{s_θ}_{p,q}`, and functoriality of the
  `K`-method (`TauCeti.CompatibleCouple.KMethodSpace.map`) furnishes mutually inverse continuous
  linear maps between `(H^{s₀,p}, H^{s₁,p})_{θ,q}` and `B^{s_θ}_{p,q}`.

## Main declarations

* `BesselPotentialSpace.continuous_toDistr` and `BesselPotentialSpace.toDistrCLM`: the continuous
  linear embedding `H^{s,p}(E, F) →L[ℂ] 𝓢'(E, F)`.
* `TauCeti.CompatibleCouple.besselPotential`: the compatible couple
  `(H^{s₀,p}(E, F), H^{s₁,p}(E, F))` inside `𝓢'(E, F)`.
* `TauCeti.CompatibleCouple.besovOneToBesselPotentialSum` and
  `TauCeti.CompatibleCouple.besselPotentialToBesovTopSum`: the sandwich morphisms of sum spaces
  induced by `B^s_{p,1} ⊆ H^{s,p} ⊆ B^s_{p,∞}`.
* `TauCeti.CompatibleCouple.mem_range_sumSpaceEmbed_besselPotential` and
  `TauCeti.CompatibleCouple.mem_kMethod_besselPotential_iff`: for `s₀ ≠ s₁` and `0 < θ < 1`,
  membership in `(H^{s₀,p}, H^{s₁,p})_{θ,q}` is `MemBesov φ ((1 - θ) s₀ + θ s₁) p q`.
* `TauCeti.CompatibleCouple.besselPotentialKMethodEquiv`: the Banach-space isomorphism
  `(H^{s₀,p}(E, F), H^{s₁,p}(E, F))_{θ,q} ≃L[ℂ] B^{(1 - θ) s₀ + θ s₁}_{p,q}(E, F)`.
* `TauCeti.CompatibleCouple.mem_kMethod_besselPotential_two_iff` and
  `TauCeti.CompatibleCouple.besselPotentialHilbertKMethodEquiv`: the Hilbert-space specialization
  `(H^{s₀}(E, H), H^{s₁}(E, H))_{θ,2} ≃L[ℂ] H^{(1 - θ) s₀ + θ s₁}(E, H)`.

## References

* J. Bergh and J. Löfström, *Interpolation Spaces: An Introduction*, Grundlehren 223, Springer,
  1976, Theorems 6.2.4 and 6.4.5(4).
* H. Triebel, *Theory of Function Spaces*, Section 2.4.2.
-/

public noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal SchwartzMap BesselPotentialSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

namespace BesselPotentialSpace

section ToDistr

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]
  {s : ℝ} {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The embedding `H^{s,p}(E, F) → 𝓢'(E, F)` is continuous: it factors as `J^{-s} ∘ ι ∘ toLp`,
where `toLp : H^{s,p} ≃ₗᵢ[ℂ] Lᵖ`, `ι : Lᵖ →L[ℂ] 𝓢'`, and `J^{-s} : 𝓢' →L[ℂ] 𝓢'`. -/
theorem continuous_toDistr : Continuous (toDistr : H^{s, p}(E, F) → 𝓢'(E, F)) := by
  have h : (toDistr : H^{s, p}(E, F) → 𝓢'(E, F)) =
      fun u ↦ TemperedDistribution.besselPotential E F (-s)
        (Lp.toTemperedDistributionCLM F (volume : Measure E) p (toLpₗᵢ E F s p u)) := by
    funext u
    rw [toLpₗᵢ_apply, Lp.toTemperedDistributionCLM_apply, besselPotential_neg_toLp_eq]
  rw [h]
  exact (TemperedDistribution.besselPotential E F (-s)).continuous.comp <|
    (Lp.toTemperedDistributionCLM F (volume : Measure E) p).continuous.comp
      (toLpₗᵢ E F s p).toLinearIsometry.continuous

variable (E F s p) in
/-- Coercion from the Bessel-potential space `H^{s,p}(E, F)` to tempered distributions as a
continuous linear map. -/
def toDistrCLM : H^{s, p}(E, F) →L[ℂ] 𝓢'(E, F) where
  toFun := toDistr
  map_add' := toDistr_add
  map_smul' := toDistr_smul
  cont := continuous_toDistr

@[simp]
theorem toDistrCLM_apply (u : H^{s, p}(E, F)) : toDistrCLM E F s p u = u.toDistr :=
  (rfl)

theorem toDistrCLM_injective : Function.Injective (toDistrCLM E F s p) :=
  fun _ _ h ↦ ext h

end ToDistr

end BesselPotentialSpace

namespace TauCeti.CompatibleCouple

open TemperedDistribution KMethodSpace

/-! ### The Bessel-potential compatible couple and its Besov sandwich -/

section Couple

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]
  {s₀ s₁ : ℝ} {p : ℝ≥0∞} [Fact (1 ≤ p)]

variable (E F s₀ s₁ p) in
/-- The compatible couple `(H^{s₀,p}(E, F), H^{s₁,p}(E, F))` of Bessel-potential spaces, with both
endpoints continuously embedded in the ambient space `𝓢'(E, F)` of tempered distributions. -/
def besselPotential :
    CompatibleCouple ℂ H^{s₀, p}(E, F) H^{s₁, p}(E, F) 𝓢'(E, F) where
  embed₀ := BesselPotentialSpace.toDistrCLM E F s₀ p
  embed₁ := BesselPotentialSpace.toDistrCLM E F s₁ p
  embed₀_injective := BesselPotentialSpace.toDistrCLM_injective
  embed₁_injective := BesselPotentialSpace.toDistrCLM_injective

@[simp]
theorem besselPotential_embed₀ :
    (besselPotential E F s₀ s₁ p).embed₀ = BesselPotentialSpace.toDistrCLM E F s₀ p :=
  (rfl)

@[simp]
theorem besselPotential_embed₁ :
    (besselPotential E F s₀ s₁ p).embed₁ = BesselPotentialSpace.toDistrCLM E F s₁ p :=
  (rfl)

/-- A pair `(u₀, u₁)` lies in the intersection of `(H^{s₀,p}, H^{s₁,p})` if and only if `u₀` and
`u₁` represent the same tempered distribution. -/
theorem mem_besselPotential_inter_iff {x : H^{s₀, p}(E, F) × H^{s₁, p}(E, F)} :
    x ∈ (besselPotential E F s₀ s₁ p).inter ↔ x.1.toDistr = x.2.toDistr := by
  simp [mem_inter_iff]

/-- Two decompositions in `H^{s₀,p} + H^{s₁,p}` agree if and only if their sums agree in
`𝓢'(E, F)`. -/
theorem besselPotential_fstToSum_add_sndToSum_eq_iff
    {u₀ v₀ : H^{s₀, p}(E, F)} {u₁ v₁ : H^{s₁, p}(E, F)} :
    (besselPotential E F s₀ s₁ p).fstToSum u₀ + (besselPotential E F s₀ s₁ p).sndToSum u₁ =
        (besselPotential E F s₀ s₁ p).fstToSum v₀ + (besselPotential E F s₀ s₁ p).sndToSum v₁ ↔
      u₀.toDistr + u₁.toDistr = v₀.toDistr + v₁.toDistr := by
  rw [← (besselPotential E F s₀ s₁ p).sumSpaceEmbed_injective.eq_iff]
  simp

private theorem besovOneToBesselPotentialSum_compat {φ : ContDiffBump (0 : E)}
    (x : (besov F φ s₀ s₁ p 1 1).inter) :
    (besselPotential E F s₀ s₁ p).fstToSum
        (BesovSpace.toBesselPotentialSpace ((besov F φ s₀ s₁ p 1 1).interFst x)) =
      (besselPotential E F s₀ s₁ p).sndToSum
        (BesovSpace.toBesselPotentialSpace ((besov F φ s₀ s₁ p 1 1).interSnd x)) :=
  (besselPotential E F s₀ s₁ p).sumSpace_ext <| by
    simpa using (besov F φ s₀ s₁ p 1 1).embed₀_interFst x

/-- The continuous inclusion `B^{s₀}_{p,1} + B^{s₁}_{p,1} →L[ℂ] H^{s₀,p} + H^{s₁,p}` induced by
`TauCeti.BesovSpace.toBesselPotentialSpace` on each endpoint. -/
def besovOneToBesselPotentialSum {φ : ContDiffBump (0 : E)} :
    (besov F φ s₀ s₁ p 1 1).SumSpace →L[ℂ] (besselPotential E F s₀ s₁ p).SumSpace :=
  (besov F φ s₀ s₁ p 1 1).sumLift
    ((besselPotential E F s₀ s₁ p).fstToSum.comp BesovSpace.toBesselPotentialSpace)
    ((besselPotential E F s₀ s₁ p).sndToSum.comp BesovSpace.toBesselPotentialSpace)
    besovOneToBesselPotentialSum_compat

@[simp]
theorem besovOneToBesselPotentialSum_fstToSum {φ : ContDiffBump (0 : E)}
    (u₀ : BesovSpace F φ s₀ p 1) :
    besovOneToBesselPotentialSum ((besov F φ s₀ s₁ p 1 1).fstToSum u₀) =
      (besselPotential E F s₀ s₁ p).fstToSum (BesovSpace.toBesselPotentialSpace u₀) := by
  rw [besovOneToBesselPotentialSum]
  exact ((besov F φ s₀ s₁ p 1 1).sumLift_fstToSum _ _ _ u₀).trans (by simp)

@[simp]
theorem besovOneToBesselPotentialSum_sndToSum {φ : ContDiffBump (0 : E)}
    (u₁ : BesovSpace F φ s₁ p 1) :
    besovOneToBesselPotentialSum ((besov F φ s₀ s₁ p 1 1).sndToSum u₁) =
      (besselPotential E F s₀ s₁ p).sndToSum (BesovSpace.toBesselPotentialSpace u₁) := by
  rw [besovOneToBesselPotentialSum]
  exact ((besov F φ s₀ s₁ p 1 1).sumLift_sndToSum _ _ _ u₁).trans (by simp)

@[simp]
theorem sumSpaceEmbed_besovOneToBesselPotentialSum {φ : ContDiffBump (0 : E)}
    (u : (besov F φ s₀ s₁ p 1 1).SumSpace) :
    (besselPotential E F s₀ s₁ p).sumSpaceEmbed (besovOneToBesselPotentialSum u) =
      (besov F φ s₀ s₁ p 1 1).sumSpaceEmbed u := by
  obtain ⟨u₀, u₁, rfl⟩ := (besov F φ s₀ s₁ p 1 1).exists_fstToSum_add_sndToSum_eq u
  simp

private theorem besselPotentialToBesovTopSum_compat (φ : ContDiffBump (0 : E))
    (x : (besselPotential E F s₀ s₁ p).inter) :
    (besov F φ s₀ s₁ p ∞ ∞).fstToSum
        (BesselPotentialSpace.toBesovSpace φ ((besselPotential E F s₀ s₁ p).interFst x)) =
      (besov F φ s₀ s₁ p ∞ ∞).sndToSum
        (BesselPotentialSpace.toBesovSpace φ ((besselPotential E F s₀ s₁ p).interSnd x)) :=
  (besov F φ s₀ s₁ p ∞ ∞).sumSpace_ext <| by
    simpa using (besselPotential E F s₀ s₁ p).embed₀_interFst x

/-- The continuous inclusion `H^{s₀,p} + H^{s₁,p} →L[ℂ] B^{s₀}_{p,∞} + B^{s₁}_{p,∞}` induced by
`BesselPotentialSpace.toBesovSpace` on each endpoint. -/
def besselPotentialToBesovTopSum (φ : ContDiffBump (0 : E)) :
    (besselPotential E F s₀ s₁ p).SumSpace →L[ℂ] (besov F φ s₀ s₁ p ∞ ∞).SumSpace :=
  (besselPotential E F s₀ s₁ p).sumLift
    ((besov F φ s₀ s₁ p ∞ ∞).fstToSum.comp (BesselPotentialSpace.toBesovSpace φ))
    ((besov F φ s₀ s₁ p ∞ ∞).sndToSum.comp (BesselPotentialSpace.toBesovSpace φ))
    (besselPotentialToBesovTopSum_compat φ)

@[simp]
theorem besselPotentialToBesovTopSum_fstToSum (φ : ContDiffBump (0 : E))
    (u₀ : H^{s₀, p}(E, F)) :
    besselPotentialToBesovTopSum φ ((besselPotential E F s₀ s₁ p).fstToSum u₀) =
      (besov F φ s₀ s₁ p ∞ ∞).fstToSum (BesselPotentialSpace.toBesovSpace φ u₀) := by
  rw [besselPotentialToBesovTopSum]
  exact ((besselPotential E F s₀ s₁ p).sumLift_fstToSum _ _ _ u₀).trans (by simp)

@[simp]
theorem besselPotentialToBesovTopSum_sndToSum (φ : ContDiffBump (0 : E))
    (u₁ : H^{s₁, p}(E, F)) :
    besselPotentialToBesovTopSum φ ((besselPotential E F s₀ s₁ p).sndToSum u₁) =
      (besov F φ s₀ s₁ p ∞ ∞).sndToSum (BesselPotentialSpace.toBesovSpace φ u₁) := by
  rw [besselPotentialToBesovTopSum]
  exact ((besselPotential E F s₀ s₁ p).sumLift_sndToSum _ _ _ u₁).trans (by simp)

@[simp]
theorem sumSpaceEmbed_besselPotentialToBesovTopSum (φ : ContDiffBump (0 : E))
    (u : (besselPotential E F s₀ s₁ p).SumSpace) :
    (besov F φ s₀ s₁ p ∞ ∞).sumSpaceEmbed (besselPotentialToBesovTopSum φ u) =
      (besselPotential E F s₀ s₁ p).sumSpaceEmbed u := by
  obtain ⟨u₀, u₁, rfl⟩ := (besselPotential E F s₀ s₁ p).exists_fstToSum_add_sndToSum_eq u
  simp

end Couple

/-! ### Real interpolation of `H^{s,p}` and the `L²` Sobolev scale -/

section Interpolation

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]
  {s₀ s₁ θ : ℝ} {p q : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Every tempered distribution in `B^{(1 - θ) s₀ + θ s₁}_{p,q}` lies in the sum space of
`(H^{s₀,p}, H^{s₁,p})` when `s₀ ≠ s₁` and `0 < θ < 1`: it lies in `B^{s₀}_{p,1} + B^{s₁}_{p,1}`,
which embeds into `H^{s₀,p} + H^{s₁,p}`. -/
theorem mem_range_sumSpaceEmbed_besselPotential {φ : ContDiffBump (0 : E)}
    (hs : s₀ ≠ s₁) (hθ : θ ∈ Ioo 0 1) {u : 𝓢'(E, F)}
    (hu : u.MemBesov φ ((1 - θ) * s₀ + θ * s₁) p q) :
    u ∈ range (besselPotential E F s₀ s₁ p).sumSpaceEmbed := by
  obtain ⟨w, rfl⟩ := mem_range_sumSpaceEmbed_besov (q₀ := 1) (q₁ := 1) hs hθ hu
  exact ⟨besovOneToBesselPotentialSum w, by simp⟩

/-- **Real interpolation of Bessel-potential spaces**, membership form
(Bergh–Löfström, Theorem 6.4.5(4)): for `s₀ ≠ s₁`, `0 < θ < 1`, and `1 ≤ q`, an element of
`H^{s₀,p} + H^{s₁,p}` lies in `(H^{s₀,p}, H^{s₁,p})_{θ,q}` if and only if its ambient tempered
distribution lies in `B^{(1 - θ) s₀ + θ s₁}_{p,q}`. -/
theorem mem_kMethod_besselPotential_iff (φ : ContDiffBump (0 : E))
    (hs : s₀ ≠ s₁) (hθ : θ ∈ Ioo 0 1) (hq : 1 ≤ q)
    {u : (besselPotential E F s₀ s₁ p).SumSpace} :
    u ∈ (besselPotential E F s₀ s₁ p).kMethod θ q ↔
      ((besselPotential E F s₀ s₁ p).sumSpaceEmbed u).MemBesov
        φ ((1 - θ) * s₀ + θ * s₁) p q := by
  constructor
  · intro hu
    have htop : besselPotentialToBesovTopSum φ u ∈ (besov F φ s₀ s₁ p ∞ ∞).kMethod θ q :=
      map_mem_kMethod (besselPotentialToBesovTopSum φ).toLinearMap
        (T₀ := BesselPotentialSpace.toBesovSpace φ)
        (T₁ := BesselPotentialSpace.toBesovSpace φ)
        (fun x ↦ by simp) (fun x ↦ by simp) hu
    simpa using (mem_kMethod_besov_iff hs hθ hq).1 htop
  · intro hu
    obtain ⟨w, hw⟩ := mem_range_sumSpaceEmbed_besov (q₀ := 1) (q₁ := 1) hs hθ hu
    have hw_mem : w ∈ (besov F φ s₀ s₁ p 1 1).kMethod θ q :=
      (mem_kMethod_besov_iff hs hθ hq).2 (hw.symm ▸ hu)
    have himg : besovOneToBesselPotentialSum w ∈ (besselPotential E F s₀ s₁ p).kMethod θ q :=
      map_mem_kMethod besovOneToBesselPotentialSum.toLinearMap
        (T₀ := BesovSpace.toBesselPotentialSpace)
        (T₁ := BesovSpace.toBesselPotentialSpace)
        (fun x ↦ by simp) (fun x ↦ by simp) hw_mem
    have hwu : besovOneToBesselPotentialSum w = u :=
      (besselPotential E F s₀ s₁ p).sumSpace_ext (by simp [hw])
    rwa [hwu] at himg

section Equiv

variable [Fact (1 ≤ q)]

private def besovOneToBesselPotentialKMethod {φ : ContDiffBump (0 : E)} :
    (besov F φ s₀ s₁ p 1 1).KMethodSpace θ q →L[ℂ]
      (besselPotential E F s₀ s₁ p).KMethodSpace θ q :=
  KMethodSpace.map besovOneToBesselPotentialSum.toLinearMap
    (T₀ := BesovSpace.toBesselPotentialSpace)
    (T₁ := BesovSpace.toBesselPotentialSpace)
    (fun x ↦ by simp) (fun x ↦ by simp)

private def besselPotentialToBesovTopKMethod (φ : ContDiffBump (0 : E)) :
    (besselPotential E F s₀ s₁ p).KMethodSpace θ q →L[ℂ]
      (besov F φ s₀ s₁ p ∞ ∞).KMethodSpace θ q :=
  KMethodSpace.map (besselPotentialToBesovTopSum φ).toLinearMap
    (T₀ := BesselPotentialSpace.toBesovSpace φ)
    (T₁ := BesselPotentialSpace.toBesovSpace φ)
    (fun x ↦ by simp) (fun x ↦ by simp)

/-- **Real interpolation of Bessel-potential spaces** (Bergh–Löfström, Theorems 6.2.4 and
6.4.5(4)). For distinct smoothness orders `s₀ ≠ s₁`, `0 < θ < 1`, and `1 ≤ p, q ≤ ∞`, the real
interpolation space `(H^{s₀,p}(E, F), H^{s₁,p}(E, F))_{θ,q}` is isomorphic as a Banach space to
`B^{(1 - θ) s₀ + θ s₁}_{p,q}(E, F)` via the ambient tempered distribution. -/
def besselPotentialKMethodEquiv (φ : ContDiffBump (0 : E))
    (hs : s₀ ≠ s₁) (hθ : θ ∈ Ioo 0 1) :
    (besselPotential E F s₀ s₁ p).KMethodSpace θ q ≃L[ℂ]
      BesovSpace F φ ((1 - θ) * s₀ + θ * s₁) p q :=
  ContinuousLinearEquiv.equivOfInverse
    ((besovKMethodEquiv (q₀ := ∞) (q₁ := ∞) hs hθ).toContinuousLinearMap.comp
      (besselPotentialToBesovTopKMethod φ))
    (besovOneToBesselPotentialKMethod.comp
      (besovKMethodEquiv (q₀ := 1) (q₁ := 1) hs hθ).symm.toContinuousLinearMap)
    (fun u ↦ KMethodSpace.ext <|
      (besselPotential E F s₀ s₁ p).sumSpace_ext <| by
        simp [besovOneToBesselPotentialKMethod, besselPotentialToBesovTopKMethod])
    (fun v ↦ BesovSpace.ext <| by
      simp [besovOneToBesselPotentialKMethod, besselPotentialToBesovTopKMethod])

@[simp]
theorem toDistr_besselPotentialKMethodEquiv (φ : ContDiffBump (0 : E))
    (hs : s₀ ≠ s₁) (hθ : θ ∈ Ioo 0 1)
    (u : (besselPotential E F s₀ s₁ p).KMethodSpace θ q) :
    (besselPotentialKMethodEquiv φ hs hθ u).toDistr =
      (besselPotential E F s₀ s₁ p).sumSpaceEmbed (toSumₗ u) := by
  simp [besselPotentialKMethodEquiv, besselPotentialToBesovTopKMethod]

@[simp]
theorem sumSpaceEmbed_toSumₗ_besselPotentialKMethodEquiv_symm (φ : ContDiffBump (0 : E))
    (hs : s₀ ≠ s₁) (hθ : θ ∈ Ioo 0 1)
    (v : BesovSpace F φ ((1 - θ) * s₀ + θ * s₁) p q) :
    (besselPotential E F s₀ s₁ p).sumSpaceEmbed
        (toSumₗ ((besselPotentialKMethodEquiv φ hs hθ).symm v)) =
      v.toDistr := by
  rw [← toDistr_besselPotentialKMethodEquiv φ hs hθ, ContinuousLinearEquiv.apply_symm_apply]

end Equiv

end Interpolation

section Hilbert

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {s₀ s₁ θ : ℝ}

/-- Every tempered distribution in `H^{(1 - θ) s₀ + θ s₁}(E, H)` lies in the sum space of
`(H^{s₀}(E, H), H^{s₁}(E, H))` when `s₀ ≠ s₁` and `0 < θ < 1`. -/
theorem mem_range_sumSpaceEmbed_besselPotential_two (hs : s₀ ≠ s₁) (hθ : θ ∈ Ioo 0 1)
    {u : 𝓢'(E, H)} (hu : u.MemSobolev ((1 - θ) * s₀ + θ * s₁) 2) :
    u ∈ range (besselPotential E H s₀ s₁ 2).sumSpaceEmbed :=
  mem_range_sumSpaceEmbed_besselPotential hs hθ
    ((memBesov_two_two_iff_memSobolev (default : ContDiffBump (0 : E))).2 hu)

/-- **Real interpolation of Hilbert-space Sobolev spaces**, membership form: for `s₀ ≠ s₁` and
`0 < θ < 1`, an element of `H^{s₀}(E, H) + H^{s₁}(E, H)` lies in
`(H^{s₀}(E, H), H^{s₁}(E, H))_{θ,2}` if and only if its ambient tempered distribution lies in
`H^{(1 - θ) s₀ + θ s₁}(E, H)`. -/
theorem mem_kMethod_besselPotential_two_iff (hs : s₀ ≠ s₁) (hθ : θ ∈ Ioo 0 1)
    {u : (besselPotential E H s₀ s₁ 2).SumSpace} :
    u ∈ (besselPotential E H s₀ s₁ 2).kMethod θ 2 ↔
      ((besselPotential E H s₀ s₁ 2).sumSpaceEmbed u).MemSobolev
        ((1 - θ) * s₀ + θ * s₁) 2 := by
  rw [mem_kMethod_besselPotential_iff (default : ContDiffBump (0 : E)) hs hθ
    (Fact.out : (1 : ℝ≥0∞) ≤ 2), memBesov_two_two_iff_memSobolev]

/-- **Real interpolation of Hilbert-space Sobolev spaces.** For distinct orders `s₀ ≠ s₁` and
`0 < θ < 1`, the real interpolation space `(H^{s₀}(E, H), H^{s₁}(E, H))_{θ,2}` is isomorphic as a
Banach space to `H^{(1 - θ) s₀ + θ s₁}(E, H)` via the ambient tempered distribution. -/
def besselPotentialHilbertKMethodEquiv (hs : s₀ ≠ s₁) (hθ : θ ∈ Ioo 0 1) :
    (besselPotential E H s₀ s₁ 2).KMethodSpace θ 2 ≃L[ℂ]
      H^{(1 - θ) * s₀ + θ * s₁}(E, H) :=
  (besselPotentialKMethodEquiv (default : ContDiffBump (0 : E)) hs hθ).trans
    (BesovSpace.besselPotentialSpaceEquiv H (default : ContDiffBump (0 : E))
      ((1 - θ) * s₀ + θ * s₁))

@[simp]
theorem toDistr_besselPotentialHilbertKMethodEquiv (hs : s₀ ≠ s₁) (hθ : θ ∈ Ioo 0 1)
    (u : (besselPotential E H s₀ s₁ 2).KMethodSpace θ 2) :
    (besselPotentialHilbertKMethodEquiv hs hθ u).toDistr =
      (besselPotential E H s₀ s₁ 2).sumSpaceEmbed (toSumₗ u) := by
  simp [besselPotentialHilbertKMethodEquiv]

@[simp]
theorem sumSpaceEmbed_toSumₗ_besselPotentialHilbertKMethodEquiv_symm
    (hs : s₀ ≠ s₁) (hθ : θ ∈ Ioo 0 1)
    (v : H^{(1 - θ) * s₀ + θ * s₁}(E, H)) :
    (besselPotential E H s₀ s₁ 2).sumSpaceEmbed
        (toSumₗ ((besselPotentialHilbertKMethodEquiv hs hθ).symm v)) =
      v.toDistr := by
  rw [← toDistr_besselPotentialHilbertKMethodEquiv hs hθ, ContinuousLinearEquiv.apply_symm_apply]

end Hilbert

end TauCeti.CompatibleCouple
