/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.FunctionalSpaces.BesovSpace.Interpolation
public import TauCeti.Analysis.Sobolev.BesselPotential.Besov
public import TauCeti.Analysis.Sobolev.BesselPotential.Schwartz

/-!
# Real interpolation of Bessel-potential spaces

Let `E` be a finite-dimensional real inner product space, `F` a complex Banach space, and
`1 ≤ p ≤ ∞`. Mathlib's Bessel-potential spaces `H^{s₀,p}(E, F)` and `H^{s₁,p}(E, F)` embed
continuously and injectively into the space `𝓢'(E, F)` of tempered distributions
(`BesselPotentialSpace.toDistrCLM`), forming the compatible couple
`TauCeti.CompatibleCouple.besselPotential E F p s₀ s₁`.

For distinct smoothness orders `s₀ ≠ s₁`, `0 < θ < 1`, and `1 ≤ q ≤ ∞`, the real interpolation
space of this couple is the inhomogeneous Besov space of order `s_θ = (1 - θ) s₀ + θ s₁` with fine
index `q`:

`(H^{s₀,p}(E, F), H^{s₁,p}(E, F))_{θ,q} ≃L[ℂ] B^{(1 - θ) s₀ + θ s₁}_{p,q}(E, F)`.

Notice that the endpoints have no fine index, while real interpolation introduces the fine index `q`
independently of the couple, and `s₀ ≠ s₁` is essential so that the endpoint fine indices of the
enclosing Besov spaces wash out.

## Proof strategy

For any bump function `φ : ContDiffBump (0 : E)` and each endpoint order `sᵢ`, the continuous
inclusions

`B^{sᵢ}_{p,1} →L[ℂ] H^{sᵢ,p} →L[ℂ] B^{sᵢ}_{p,∞}`

(`TauCeti.BesovSpace.toBesselPotentialSpace` and `BesselPotentialSpace.toBesovSpace`) preserve the
underlying tempered distribution. Lifting them to sum spaces via `CompatibleCouple.sumLift` gives
continuous couple morphisms

`(B^{s₀}_{p,1}, B^{s₁}_{p,1}) → (H^{s₀,p}, H^{s₁,p}) → (B^{s₀}_{p,∞}, B^{s₁}_{p,∞})`.

Functoriality of the real `K`-method (`CompatibleCouple.KMethodSpace.map`) sandwiches
`(H^{s₀,p}, H^{s₁,p})_{θ,q}` between `(B^{s₀}_{p,1}, B^{s₁}_{p,1})_{θ,q}` and
`(B^{s₀}_{p,∞}, B^{s₁}_{p,∞})_{θ,q}`. When `s₀ ≠ s₁`, both Besov interpolation spaces are
canonically isomorphic to `B^{s_θ}_{p,q}` (`TauCeti.CompatibleCouple.besovKMethodEquiv`), and
chasing the underlying tempered distribution shows that the resulting maps between
`(H^{s₀,p}, H^{s₁,p})_{θ,q}` and `B^{s_θ}_{p,q}` are mutual inverses.

At `p = q = 2` on a complex Hilbert space `H`, combining this equivalence with
`B^s_{2,2} ≃L[ℂ] H^{s,2}` (`TauCeti.BesovSpace.besselPotentialSpaceEquiv`) yields the Hilbert
Sobolev interpolation formula

`(H^{s₀,2}(E, H), H^{s₁,2}(E, H))_{θ,2} ≃L[ℂ] H^{(1 - θ) s₀ + θ s₁, 2}(E, H)`.

## Main declarations

* `BesselPotentialSpace.continuous_toDistr`, `BesselPotentialSpace.toDistrCLM`: the continuous
  linear injection `H^{s,p}(E, F) →L[ℂ] 𝓢'(E, F)`.
* `TauCeti.CompatibleCouple.besselPotential`: the compatible couple `(H^{s₀,p}, H^{s₁,p})` inside
  `𝓢'(E, F)`.
* `TauCeti.CompatibleCouple.besovToBesselPotentialSum`,
  `TauCeti.CompatibleCouple.besselPotentialToBesovSum`: the sum-space morphisms induced by
  `B^s_{p,1} ⊆ H^{s,p} ⊆ B^s_{p,∞}`.
* `TauCeti.CompatibleCouple.mem_range_sumSpaceEmbed_besselPotential`,
  `TauCeti.CompatibleCouple.mem_kMethod_besselPotential_iff`: unbundled sum-space and
  real-interpolation membership characterisations for `(H^{s₀,p}, H^{s₁,p})`.
* `TauCeti.CompatibleCouple.besselPotentialKMethodEquiv`: the real interpolation equivalence
  `(H^{s₀,p}, H^{s₁,p})_{θ,q} ≃L[ℂ] B^{(1 - θ) s₀ + θ s₁}_{p,q}` for `s₀ ≠ s₁` and `0 < θ < 1`.
* `SchwartzMap.toBesselPotentialInterCLM`,
  `TauCeti.CompatibleCouple.norm_besselPotentialKMethodEquiv_ofInter_eq_of_norm_le`: canonical
  embedding of Schwartz functions into `H^{s₀,p} ∩ H^{s₁,p}` and exact evaluation of the resulting
  Besov norm on low-frequency Schwartz functions.
* `TauCeti.CompatibleCouple.mem_kMethod_besselPotential_two_iff`,
  `TauCeti.CompatibleCouple.besselPotentialTwoKMethodEquiv`: the Hilbert specialization
  `(H^{s₀,2}, H^{s₁,2})_{θ,2} ≃L[ℂ] H^{(1 - θ) s₀ + θ s₁, 2}`.

## References

* J. Bergh and J. Löfström, *Interpolation Spaces: An Introduction*, Grundlehren 223, Springer,
  1976, §6.4 (Theorem 6.4.5(4) and (7)).
* H. Triebel, *Theory of Function Spaces*, Birkhäuser, 1983, §2.4.2.
-/

public noncomputable section

open MeasureTheory FourierTransform TemperedDistribution Set
open scoped ENNReal SchwartzMap BesselPotentialSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

namespace BesselPotentialSpace

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]
  {s : ℝ} {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- **Bessel-potential spaces embed continuously in the tempered distributions.** Since
`u = J^{-s} (toLp u)` in `𝓢'(E, F)` and `toLp` is an isometry onto `Lᵖ`, `toDistr` is continuous. -/
theorem continuous_toDistr : Continuous (toDistr : H^{s, p}(E, F) → 𝓢'(E, F)) := by
  have h : (toDistr : H^{s, p}(E, F) → 𝓢'(E, F)) =
      besselPotential E F (-s) ∘L Lp.toTemperedDistributionCLM F volume p ∘L
        (toLpₗᵢ E F s p).toContinuousLinearEquiv.toContinuousLinearMap := by
    funext f
    simp
  rw [h]
  exact ContinuousLinearMap.continuous _

variable (E F s p) in
/-- The inclusion `H^{s,p}(E, F) ⊆ 𝓢'(E, F)` as a continuous linear map. -/
def toDistrCLM : H^{s, p}(E, F) →L[ℂ] 𝓢'(E, F) where
  toFun := toDistr
  map_add' := toDistr_add
  map_smul' := toDistr_smul
  cont := continuous_toDistr

@[simp]
theorem toDistrCLM_apply (f : H^{s, p}(E, F)) : toDistrCLM E F s p f = f.toDistr :=
  (rfl)

theorem toDistrCLM_injective : Function.Injective (toDistrCLM E F s p) :=
  fun _ _ ↦ ext

end BesselPotentialSpace

namespace TauCeti.CompatibleCouple

section BesselPotentialCouple

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]

section Defs

variable (E F) (p : ℝ≥0∞) [Fact (1 ≤ p)] (s₀ s₁ : ℝ)

/-- The compatible couple `(H^{s₀,p}(E, F), H^{s₁,p}(E, F))` of Bessel-potential spaces, embedded
into the common ambient space `𝓢'(E, F)` of tempered distributions by
`BesselPotentialSpace.toDistrCLM`. -/
def besselPotential : CompatibleCouple ℂ H^{s₀, p}(E, F) H^{s₁, p}(E, F) 𝓢'(E, F) where
  embed₀ := BesselPotentialSpace.toDistrCLM E F s₀ p
  embed₁ := BesselPotentialSpace.toDistrCLM E F s₁ p
  embed₀_injective := BesselPotentialSpace.toDistrCLM_injective
  embed₁_injective := BesselPotentialSpace.toDistrCLM_injective

end Defs

section Basic

variable {p : ℝ≥0∞} [Fact (1 ≤ p)] {s₀ s₁ : ℝ}

@[simp]
theorem besselPotential_embed₀ :
    (besselPotential E F p s₀ s₁).embed₀ = BesselPotentialSpace.toDistrCLM E F s₀ p :=
  (rfl)

@[simp]
theorem besselPotential_embed₁ :
    (besselPotential E F p s₀ s₁).embed₁ = BesselPotentialSpace.toDistrCLM E F s₁ p :=
  (rfl)

@[simp]
theorem besselPotential_swap :
    (besselPotential E F p s₀ s₁).swap = besselPotential E F p s₁ s₀ := by
  ext <;> rfl

/-- The intersection of `(H^{s₀,p}, H^{s₁,p})` consists of pairs with the same tempered
distribution. -/
theorem mem_besselPotential_inter_iff {x : H^{s₀, p}(E, F) × H^{s₁, p}(E, F)} :
    x ∈ (besselPotential E F p s₀ s₁).inter ↔ x.1.toDistr = x.2.toDistr := by
  rw [mem_inter_iff, besselPotential_embed₀, besselPotential_embed₁,
    BesselPotentialSpace.toDistrCLM_apply, BesselPotentialSpace.toDistrCLM_apply]

/-- Two decompositions in `H^{s₀,p} + H^{s₁,p}` agree exactly when their sums in `𝓢'(E, F)`
agree. -/
theorem besselPotential_fstToSum_add_sndToSum_eq_iff {u₀ v₀ : H^{s₀, p}(E, F)}
    {u₁ v₁ : H^{s₁, p}(E, F)} :
    (besselPotential E F p s₀ s₁).fstToSum u₀ + (besselPotential E F p s₀ s₁).sndToSum u₁ =
        (besselPotential E F p s₀ s₁).fstToSum v₀ + (besselPotential E F p s₀ s₁).sndToSum v₁ ↔
      u₀.toDistr + u₁.toDistr = v₀.toDistr + v₁.toDistr := by
  rw [← (besselPotential E F p s₀ s₁).sumSpaceEmbed_injective.eq_iff]
  simp

end Basic

/-! ### Sandwiching between Besov couples -/

section Sandwich

variable {φ : ContDiffBump (0 : E)} {p : ℝ≥0∞} [Fact (1 ≤ p)] {s₀ s₁ : ℝ}

private theorem besovToBesselPotential_compat
    (x : (besov F φ p 1 1 s₀ s₁).inter) :
    (besselPotential E F p s₀ s₁).fstToSum
        (BesovSpace.toBesselPotentialSpace ((besov F φ p 1 1 s₀ s₁).interFst x)) =
      (besselPotential E F p s₀ s₁).sndToSum
        (BesovSpace.toBesselPotentialSpace ((besov F φ p 1 1 s₀ s₁).interSnd x)) := by
  apply (besselPotential E F p s₀ s₁).sumSpace_ext
  simpa only [sumSpaceEmbed_fstToSum, sumSpaceEmbed_sndToSum, besselPotential_embed₀,
    besselPotential_embed₁, BesselPotentialSpace.toDistrCLM_apply,
    BesovSpace.toDistr_toBesselPotentialSpace, interFst_apply, interSnd_apply] using
    mem_besov_inter_iff.1 x.2

variable (F φ p s₀ s₁) in
/-- The continuous linear map `B^{s₀}_{p,1} + B^{s₁}_{p,1} →L[ℂ] H^{s₀,p} + H^{s₁,p}` induced by
`BesovSpace.toBesselPotentialSpace` on each endpoint. -/
def besovToBesselPotentialSum :
    (besov F φ p 1 1 s₀ s₁).SumSpace →L[ℂ] (besselPotential E F p s₀ s₁).SumSpace :=
  (besov F φ p 1 1 s₀ s₁).sumLift
    ((besselPotential E F p s₀ s₁).fstToSum.comp BesovSpace.toBesselPotentialSpace)
    ((besselPotential E F p s₀ s₁).sndToSum.comp BesovSpace.toBesselPotentialSpace)
    besovToBesselPotential_compat

@[simp]
theorem besovToBesselPotentialSum_fstToSum (u : BesovSpace F φ s₀ p 1) :
    besovToBesselPotentialSum F φ p s₀ s₁ ((besov F φ p 1 1 s₀ s₁).fstToSum u) =
      (besselPotential E F p s₀ s₁).fstToSum (BesovSpace.toBesselPotentialSpace u) :=
  (besov F φ p 1 1 s₀ s₁).sumLift_fstToSum _ _ _ u

@[simp]
theorem besovToBesselPotentialSum_sndToSum (u : BesovSpace F φ s₁ p 1) :
    besovToBesselPotentialSum F φ p s₀ s₁ ((besov F φ p 1 1 s₀ s₁).sndToSum u) =
      (besselPotential E F p s₀ s₁).sndToSum (BesovSpace.toBesselPotentialSpace u) :=
  (besov F φ p 1 1 s₀ s₁).sumLift_sndToSum _ _ _ u

@[simp]
theorem sumSpaceEmbed_besovToBesselPotentialSum (u : (besov F φ p 1 1 s₀ s₁).SumSpace) :
    (besselPotential E F p s₀ s₁).sumSpaceEmbed (besovToBesselPotentialSum F φ p s₀ s₁ u) =
      (besov F φ p 1 1 s₀ s₁).sumSpaceEmbed u := by
  obtain ⟨u₀, u₁, rfl⟩ := (besov F φ p 1 1 s₀ s₁).exists_fstToSum_add_sndToSum_eq u
  simp

private theorem besselPotentialToBesov_compat
    (x : (besselPotential E F p s₀ s₁).inter) :
    (besov F φ p ∞ ∞ s₀ s₁).fstToSum
        (BesselPotentialSpace.toBesovSpace φ ((besselPotential E F p s₀ s₁).interFst x)) =
      (besov F φ p ∞ ∞ s₀ s₁).sndToSum
        (BesselPotentialSpace.toBesovSpace φ ((besselPotential E F p s₀ s₁).interSnd x)) := by
  apply (besov F φ p ∞ ∞ s₀ s₁).sumSpace_ext
  simpa only [sumSpaceEmbed_fstToSum, sumSpaceEmbed_sndToSum, besov_embed₀, besov_embed₁,
    BesovSpace.toDistrCLM_apply, BesselPotentialSpace.toDistr_toBesovSpace, interFst_apply,
    interSnd_apply] using mem_besselPotential_inter_iff.1 x.2

variable (F φ p s₀ s₁) in
/-- The continuous linear map `H^{s₀,p} + H^{s₁,p} →L[ℂ] B^{s₀}_{p,∞} + B^{s₁}_{p,∞}` induced by
`BesselPotentialSpace.toBesovSpace φ` on each endpoint. -/
def besselPotentialToBesovSum :
    (besselPotential E F p s₀ s₁).SumSpace →L[ℂ] (besov F φ p ∞ ∞ s₀ s₁).SumSpace :=
  (besselPotential E F p s₀ s₁).sumLift
    ((besov F φ p ∞ ∞ s₀ s₁).fstToSum.comp (BesselPotentialSpace.toBesovSpace φ))
    ((besov F φ p ∞ ∞ s₀ s₁).sndToSum.comp (BesselPotentialSpace.toBesovSpace φ))
    besselPotentialToBesov_compat

@[simp]
theorem besselPotentialToBesovSum_fstToSum (u : H^{s₀, p}(E, F)) :
    besselPotentialToBesovSum F φ p s₀ s₁ ((besselPotential E F p s₀ s₁).fstToSum u) =
      (besov F φ p ∞ ∞ s₀ s₁).fstToSum (BesselPotentialSpace.toBesovSpace φ u) :=
  (besselPotential E F p s₀ s₁).sumLift_fstToSum _ _ _ u

@[simp]
theorem besselPotentialToBesovSum_sndToSum (u : H^{s₁, p}(E, F)) :
    besselPotentialToBesovSum F φ p s₀ s₁ ((besselPotential E F p s₀ s₁).sndToSum u) =
      (besov F φ p ∞ ∞ s₀ s₁).sndToSum (BesselPotentialSpace.toBesovSpace φ u) :=
  (besselPotential E F p s₀ s₁).sumLift_sndToSum _ _ _ u

@[simp]
theorem sumSpaceEmbed_besselPotentialToBesovSum (u : (besselPotential E F p s₀ s₁).SumSpace) :
    (besov F φ p ∞ ∞ s₀ s₁).sumSpaceEmbed (besselPotentialToBesovSum F φ p s₀ s₁ u) =
      (besselPotential E F p s₀ s₁).sumSpaceEmbed u := by
  obtain ⟨u₀, u₁, rfl⟩ := (besselPotential E F p s₀ s₁).exists_fstToSum_add_sndToSum_eq u
  simp

end Sandwich

/-! ### Real interpolation of Bessel-potential spaces -/

section Interpolation

variable {φ : ContDiffBump (0 : E)} {p : ℝ≥0∞} [Fact (1 ≤ p)] {s₀ s₁ θ : ℝ} {q : ℝ≥0∞}

/-- Every tempered distribution in `B^{s_θ}_{p,q}`, where `s_θ = (1 - θ) s₀ + θ s₁`, lies in the
sum space `H^{s₀,p} + H^{s₁,p}` for distinct `s₀ ≠ s₁`, `0 < θ < 1` and `q ≠ 0`. -/
theorem mem_range_sumSpaceEmbed_besselPotential (hs : s₀ ≠ s₁) (hθ : θ ∈ Ioo 0 1) (hq : q ≠ 0)
    {u : 𝓢'(E, F)} (hu : u.MemBesov φ ((1 - θ) * s₀ + θ * s₁) p q) :
    u ∈ range (besselPotential E F p s₀ s₁).sumSpaceEmbed := by
  obtain ⟨w, hw⟩ := mem_range_sumSpaceEmbed_besov (q₀ := 1) (q₁ := 1) hs hθ hq hu
  exact ⟨besovToBesselPotentialSum F φ p s₀ s₁ w,
    (sumSpaceEmbed_besovToBesselPotentialSum w).trans hw⟩

/-- **Real interpolation of Bessel-potential spaces**, membership form (Bergh–Löfström,
Theorem 6.4.5(4)): for distinct `s₀ ≠ s₁`, `0 < θ < 1` and `1 ≤ q`, an element `u` of
`H^{s₀,p} + H^{s₁,p}` lies in `(H^{s₀,p}, H^{s₁,p})_{θ,q}` exactly when its underlying tempered
distribution lies in `B^{(1 - θ) s₀ + θ s₁}_{p,q}`. -/
theorem mem_kMethod_besselPotential_iff (hs : s₀ ≠ s₁) (hθ : θ ∈ Ioo 0 1) (hq : 1 ≤ q)
    {u : (besselPotential E F p s₀ s₁).SumSpace} :
    u ∈ (besselPotential E F p s₀ s₁).kMethod θ q ↔
      ((besselPotential E F p s₀ s₁).sumSpaceEmbed u).MemBesov φ ((1 - θ) * s₀ + θ * s₁) p q := by
  constructor
  · intro hu
    have hmap := map_mem_kMethod (besselPotentialToBesovSum F φ p s₀ s₁).toLinearMap
      besselPotentialToBesovSum_fstToSum besselPotentialToBesovSum_sndToSum hu
    rw [ContinuousLinearMap.coe_coe, mem_kMethod_besov_iff hs hθ hq,
      sumSpaceEmbed_besselPotentialToBesovSum] at hmap
    exact hmap
  · intro hu
    have hq0 : q ≠ 0 := (zero_lt_one.trans_le hq).ne'
    obtain ⟨w, hw⟩ := mem_range_sumSpaceEmbed_besov (q₀ := 1) (q₁ := 1) hs hθ hq0 hu
    have hw_mem : w ∈ (besov F φ p 1 1 s₀ s₁).kMethod θ q :=
      (mem_kMethod_besov_iff hs hθ hq).2 (hw.symm ▸ hu)
    have hmap := map_mem_kMethod (besovToBesselPotentialSum F φ p s₀ s₁).toLinearMap
      besovToBesselPotentialSum_fstToSum besovToBesselPotentialSum_sndToSum hw_mem
    have hwu : besovToBesselPotentialSum F φ p s₀ s₁ w = u :=
      (besselPotential E F p s₀ s₁).sumSpaceEmbed_injective
        ((sumSpaceEmbed_besovToBesselPotentialSum w).trans hw)
    rwa [ContinuousLinearMap.coe_coe, hwu] at hmap

section Equiv

variable [Fact (1 ≤ q)]

open KMethodSpace

variable (φ) in
/-- **Real interpolation of Bessel-potential spaces** (Bergh–Löfström, Theorem 6.4.5(4)). For
distinct smoothness orders `s₀ ≠ s₁`, `0 < θ < 1` and `1 ≤ p, q ≤ ∞`, the real interpolation space
`(H^{s₀,p}(E, F), H^{s₁,p}(E, F))_{θ,q}` is isomorphic to the Besov space
`B^{(1 - θ) s₀ + θ s₁}_{p,q}(E, F)` built from `φ`, preserving the underlying tempered distribution
(`toDistr_besselPotentialKMethodEquiv`). -/
def besselPotentialKMethodEquiv (hs : s₀ ≠ s₁) (hθ : θ ∈ Ioo 0 1) :
    (besselPotential E F p s₀ s₁).KMethodSpace θ q ≃L[ℂ]
      BesovSpace F φ ((1 - θ) * s₀ + θ * s₁) p q :=
  ContinuousLinearEquiv.equivOfInverse
    ((besovKMethodEquiv (q₀ := ∞) (q₁ := ∞) hs hθ).toContinuousLinearMap.comp
      (KMethodSpace.map (besselPotentialToBesovSum F φ p s₀ s₁).toLinearMap
        besselPotentialToBesovSum_fstToSum besselPotentialToBesovSum_sndToSum))
    ((KMethodSpace.map (besovToBesselPotentialSum F φ p s₀ s₁).toLinearMap
        besovToBesselPotentialSum_fstToSum besovToBesselPotentialSum_sndToSum).comp
      (besovKMethodEquiv (q₀ := 1) (q₁ := 1) hs hθ).symm.toContinuousLinearMap)
    (fun u ↦ KMethodSpace.ext <| (besselPotential E F p s₀ s₁).sumSpaceEmbed_injective <| by simp)
    (fun v ↦ BesovSpace.ext <| by simp)

@[simp]
theorem toDistr_besselPotentialKMethodEquiv (hs : s₀ ≠ s₁) (hθ : θ ∈ Ioo 0 1)
    (u : (besselPotential E F p s₀ s₁).KMethodSpace θ q) :
    (besselPotentialKMethodEquiv φ hs hθ u).toDistr =
      (besselPotential E F p s₀ s₁).sumSpaceEmbed (KMethodSpace.toSumₗ u) := by
  simp [besselPotentialKMethodEquiv]

@[simp]
theorem sumSpaceEmbed_toSumₗ_besselPotentialKMethodEquiv_symm (hs : s₀ ≠ s₁) (hθ : θ ∈ Ioo 0 1)
    (v : BesovSpace F φ ((1 - θ) * s₀ + θ * s₁) p q) :
    (besselPotential E F p s₀ s₁).sumSpaceEmbed
        (KMethodSpace.toSumₗ ((besselPotentialKMethodEquiv φ hs hθ).symm v)) =
      v.toDistr := by
  simp [besselPotentialKMethodEquiv]

end Equiv

end Interpolation

end BesselPotentialCouple

end TauCeti.CompatibleCouple

/-! ### Schwartz functions and Hilbert specialization -/

namespace SchwartzMap

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]

/-- The canonical continuous linear inclusion of Schwartz functions into the intersection
`H^{s₀,p}(E, F) ∩ H^{s₁,p}(E, F)` of two Bessel-potential spaces. -/
def toBesselPotentialInterCLM (s₀ s₁ : ℝ) (p : ℝ≥0∞) [Fact (1 ≤ p)] :
    𝓢(E, F) →L[ℂ] (TauCeti.CompatibleCouple.besselPotential E F p s₀ s₁).inter :=
  ((toBesselPotentialSpaceCLM s₀ p).prod (toBesselPotentialSpaceCLM s₁ p)).codRestrict _
    fun f ↦ TauCeti.CompatibleCouple.mem_besselPotential_inter_iff.2 (by simp)

variable {s₀ s₁ : ℝ} {p : ℝ≥0∞} [Fact (1 ≤ p)]

@[simp]
theorem coe_toBesselPotentialInterCLM_apply (f : 𝓢(E, F)) :
    (f.toBesselPotentialInterCLM s₀ s₁ p : H^{s₀, p}(E, F) × H^{s₁, p}(E, F)) =
      (f.toBesselPotentialSpaceCLM s₀ p, f.toBesselPotentialSpaceCLM s₁ p) :=
  (rfl)

theorem interFst_toBesselPotentialInterCLM (f : 𝓢(E, F)) :
    (TauCeti.CompatibleCouple.besselPotential E F p s₀ s₁).interFst
        (f.toBesselPotentialInterCLM s₀ s₁ p) =
      f.toBesselPotentialSpaceCLM s₀ p := by
  simp

theorem interSnd_toBesselPotentialInterCLM (f : 𝓢(E, F)) :
    (TauCeti.CompatibleCouple.besselPotential E F p s₀ s₁).interSnd
        (f.toBesselPotentialInterCLM s₀ s₁ p) =
      f.toBesselPotentialSpaceCLM s₁ p := by
  simp

end SchwartzMap

namespace TauCeti.CompatibleCouple

section Schwartz

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]
  {φ : ContDiffBump (0 : E)} {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)] {s₀ s₁ θ : ℝ}

theorem toDistr_besselPotentialKMethodEquiv_ofInter (hs : s₀ ≠ s₁) (hθ : θ ∈ Ioo 0 1)
    (f : 𝓢(E, F)) :
    (besselPotentialKMethodEquiv φ hs hθ
        (KMethodSpace.ofInter θ q hθ (f.toBesselPotentialInterCLM s₀ s₁ p))).toDistr =
      (f : 𝓢'(E, F)) := by
  simp

/-- A low-frequency Schwartz function `f` whose Fourier transform vanishes outside the closed ball
of radius `φ.rIn` is sent by `ofInter` and `besselPotentialKMethodEquiv` to an element of
`B^{(1 - θ) s₀ + θ s₁}_{p,q}` of norm `‖f.toLp p‖`, independently of `s₀`, `s₁`, `θ` and `q`. -/
theorem norm_besselPotentialKMethodEquiv_ofInter_eq_of_norm_le (hs : s₀ ≠ s₁) (hθ : θ ∈ Ioo 0 1)
    (f : 𝓢(E, F)) (hf : ∀ ξ, 𝓕 f ξ ≠ 0 → ‖ξ‖ ≤ φ.rIn) :
    ‖besselPotentialKMethodEquiv φ hs hθ
        (KMethodSpace.ofInter θ q hθ (f.toBesselPotentialInterCLM s₀ s₁ p))‖ =
      ‖f.toLp p‖ := by
  obtain ⟨v, hv, hvn⟩ := BesovSpace.exists_toDistr_eq_and_norm_eq_of_norm_le
    (φ := φ) (s := (1 - θ) * s₀ + θ * s₁) (p := p) (q := q) f hf
  have hveq :
      besselPotentialKMethodEquiv φ hs hθ
          (KMethodSpace.ofInter θ q hθ (f.toBesselPotentialInterCLM s₀ s₁ p)) = v :=
    BesovSpace.ext (by simp [hv])
  rw [hveq, hvn]

end Schwartz

section Hilbert

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {s₀ s₁ θ : ℝ}

/-- **Real interpolation of Hilbert Bessel-potential spaces**, membership form (Bergh–Löfström,
Theorem 6.4.5(7)): for distinct `s₀ ≠ s₁` and `0 < θ < 1`, an element `u` of `H^{s₀,2} + H^{s₁,2}`
lies in `(H^{s₀,2}, H^{s₁,2})_{θ,2}` exactly when its underlying tempered distribution lies in
`H^{(1 - θ) s₀ + θ s₁, 2}`. -/
theorem mem_kMethod_besselPotential_two_iff (hs : s₀ ≠ s₁) (hθ : θ ∈ Ioo 0 1)
    {u : (besselPotential E H 2 s₀ s₁).SumSpace} :
    u ∈ (besselPotential E H 2 s₀ s₁).kMethod θ 2 ↔
      ((besselPotential E H 2 s₀ s₁).sumSpaceEmbed u).MemSobolev ((1 - θ) * s₀ + θ * s₁) 2 := by
  rw [mem_kMethod_besselPotential_iff (φ := default) hs hθ one_le_two,
    TemperedDistribution.memBesov_two_two_iff_memSobolev]

/-- **Real interpolation of Hilbert Bessel-potential spaces** (Bergh–Löfström, Theorem 6.4.5(7)).
For distinct smoothness orders `s₀ ≠ s₁`, `0 < θ < 1` and a complex Hilbert space `H`,
`(H^{s₀,2}(E, H), H^{s₁,2}(E, H))_{θ,2}` is isomorphic to `H^{(1 - θ) s₀ + θ s₁, 2}(E, H)`,
preserving the underlying tempered distribution (`toDistr_besselPotentialTwoKMethodEquiv`). -/
def besselPotentialTwoKMethodEquiv (hs : s₀ ≠ s₁) (hθ : θ ∈ Ioo 0 1) :
    (besselPotential E H 2 s₀ s₁).KMethodSpace θ 2 ≃L[ℂ] H^{(1 - θ) * s₀ + θ * s₁}(E, H) :=
  (besselPotentialKMethodEquiv (default : ContDiffBump (0 : E)) hs hθ).trans
    (BesovSpace.besselPotentialSpaceEquiv H (default : ContDiffBump (0 : E))
      ((1 - θ) * s₀ + θ * s₁))

@[simp]
theorem toDistr_besselPotentialTwoKMethodEquiv (hs : s₀ ≠ s₁) (hθ : θ ∈ Ioo 0 1)
    (u : (besselPotential E H 2 s₀ s₁).KMethodSpace θ 2) :
    (besselPotentialTwoKMethodEquiv hs hθ u).toDistr =
      (besselPotential E H 2 s₀ s₁).sumSpaceEmbed (KMethodSpace.toSumₗ u) := by
  simp [besselPotentialTwoKMethodEquiv]

@[simp]
theorem sumSpaceEmbed_toSumₗ_besselPotentialTwoKMethodEquiv_symm (hs : s₀ ≠ s₁) (hθ : θ ∈ Ioo 0 1)
    (v : H^{(1 - θ) * s₀ + θ * s₁}(E, H)) :
    (besselPotential E H 2 s₀ s₁).sumSpaceEmbed
        (KMethodSpace.toSumₗ ((besselPotentialTwoKMethodEquiv hs hθ).symm v)) =
      v.toDistr := by
  simp [besselPotentialTwoKMethodEquiv]

end Hilbert

end TauCeti.CompatibleCouple
