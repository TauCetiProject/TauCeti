/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.FunctionalSpaces.BesovSpace.RealInterpolation
public import TauCeti.Analysis.Sobolev.BesselPotential.Besov
public import TauCeti.Analysis.Sobolev.BesselPotential.Distribution
public import TauCeti.Analysis.Sobolev.BesselPotential.Inclusion

/-!
# Real interpolation of Bessel-potential Sobolev spaces

Let `E` be a finite-dimensional real inner product space and `F` a complex Banach space. For
`1 ≤ p, q ≤ ∞`, distinct smoothness orders `s₀ ≠ s₁`, and `0 < θ < 1`, the Bessel-potential spaces
`H^{s₀,p}(E, F)` and `H^{s₁,p}(E, F)` embed continuously and injectively into the tempered
distributions (`BesselPotentialSpace.toDistrCLM`), forming a compatible couple
(`TauCeti.CompatibleCouple.besselPotentialSpace`). Its real interpolation space is the inhomogeneous
Besov space of order `s_θ = (1 - θ) s₀ + θ s₁` and fine index `q`:

`(H^{s₀,p}(E, F), H^{s₁,p}(E, F))_{θ,q} ≃L[ℂ] B^{s_θ}_{p,q}(E, F)`,

built from the Littlewood–Paley blocks `Δⱼ` of any bump function `φ`.

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
  `TauCeti.CompatibleCouple.besovOneToBesselPotentialSpaceSum` and
  `TauCeti.CompatibleCouple.besselPotentialSpaceToBesovTopSum` that preserve the ambient tempered
  distribution.
* Because `(B^{s₀}_{p,q₀}, B^{s₁}_{p,q₁})_{θ,q} ≃L[ℂ] B^{s_θ}_{p,q}`
  (`TauCeti.CompatibleCouple.besovKMethodEquiv`) does not depend on `q₀` or `q₁`, both outer
  couples have the same real interpolation space `B^{s_θ}_{p,q}`, and functoriality of the
  `K`-method (`TauCeti.CompatibleCouple.KMethodSpace.map`) furnishes mutually inverse continuous
  linear maps between `(H^{s₀,p}, H^{s₁,p})_{θ,q}` and `B^{s_θ}_{p,q}`.

## Main declarations

* `TauCeti.CompatibleCouple.besselPotentialSpaceSumToMin`: the inclusion of the sum space of the
  couple `(H^{s₀,p}(E, F), H^{s₁,p}(E, F))` into `H^{min s₀ s₁, p}`.
* `TauCeti.CompatibleCouple.besovOneToBesselPotentialSpaceSum` and
  `TauCeti.CompatibleCouple.besselPotentialSpaceToBesovTopSum`: the sandwich morphisms of sum spaces
  induced by `B^s_{p,1} ⊆ H^{s,p} ⊆ B^s_{p,∞}`.
* `TauCeti.CompatibleCouple.besselPotentialSpaceKMethodEquiv`: the Banach-space isomorphism
  `(H^{s₀,p}(E, F), H^{s₁,p}(E, F))_{θ,q} ≃L[ℂ] B^{(1 - θ) s₀ + θ s₁}_{p,q}(E, F)`, keeping the
  underlying tempered distribution.
* `TauCeti.CompatibleCouple.mem_range_sumSpaceEmbed_besselPotentialSpace`,
  `TauCeti.CompatibleCouple.mem_kMethod_besselPotentialSpace_iff`, and
  `TauCeti.CompatibleCouple.memBesov_iff_exists_mem_kMethod_besselPotentialSpace`: membership and
  image characterizations of `(H^{s₀,p}, H^{s₁,p})_{θ,q}`.
* `TauCeti.CompatibleCouple.mem_kMethod_besselPotentialSpace_two_iff`,
  `TauCeti.CompatibleCouple.memSobolev_iff_exists_mem_kMethod_besselPotentialSpace_two`, and
  `TauCeti.CompatibleCouple.besselPotentialSpaceHilbertKMethodEquiv`: the Hilbert-space
  specialization `(H^{s₀}(E, H), H^{s₁}(E, H))_{θ,2} ≃L[ℂ] H^{(1 - θ) s₀ + θ s₁}(E, H)`.

## References

* J. Bergh and J. Löfström, *Interpolation Spaces: An Introduction*, Grundlehren 223, Springer,
  1976, Theorems 6.2.4 and 6.4.5(4).
* H. Triebel, *Interpolation Theory, Function Spaces, Differential Operators*, North-Holland,
  1978, §2.4.2.
-/

public noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal SchwartzMap BesselPotentialSpace

namespace TauCeti

namespace CompatibleCouple

open BesselPotentialSpace TemperedDistribution KMethodSpace

section Banach

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]

/-! ### The Bessel-potential compatible couple and its Besov sandwich -/

section Couple

variable {p : ℝ≥0∞} [Fact (1 ≤ p)] {s₀ s₁ : ℝ}

/-- A Schwartz function has the same class in the sum space `H^{s₀,p} + H^{s₁,p}` whether it is
read in `H^{s₀,p}` or in `H^{s₁,p}`. -/
theorem besselPotentialSpace_fstToSum_toBesselPotentialSpaceCLM (f : 𝓢(E, F)) :
    (besselPotentialSpace E F s₀ p s₁ p).fstToSum
        (SchwartzMap.toBesselPotentialSpaceCLM s₀ p f) =
      (besselPotentialSpace E F s₀ p s₁ p).sndToSum
        (SchwartzMap.toBesselPotentialSpaceCLM s₁ p f) :=
  (besselPotentialSpace E F s₀ p s₁ p).sumSpace_ext <| by
    simp [SchwartzMap.toDistr_toBesselPotentialSpaceCLM]

variable (E F p s₀ s₁) in
/-- The sum space `H^{s₀,p} + H^{s₁,p}` lies in `H^{min s₀ s₁, p}`: the map induced by the
inclusions of `H^{s₀,p}` and `H^{s₁,p}` into `H^{min s₀ s₁, p}`. It keeps the underlying tempered
distribution (`TauCeti.CompatibleCouple.toDistr_besselPotentialSpaceSumToMin`). -/
def besselPotentialSpaceSumToMin :
    (besselPotentialSpace E F s₀ p s₁ p).SumSpace →L[ℂ] H^{min s₀ s₁, p}(E, F) :=
  (besselPotentialSpace E F s₀ p s₁ p).sumLift (inclusion (min_le_left s₀ s₁))
    (inclusion (min_le_right s₀ s₁)) fun x ↦ BesselPotentialSpace.ext <| by
      simpa [toDistr_inclusion] using (besselPotentialSpace E F s₀ p s₁ p).embed₀_interFst x

@[simp]
theorem besselPotentialSpaceSumToMin_fstToSum (x : H^{s₀, p}(E, F)) :
    besselPotentialSpaceSumToMin E F p s₀ s₁ ((besselPotentialSpace E F s₀ p s₁ p).fstToSum x) =
      inclusion (min_le_left s₀ s₁) x :=
  sumLift_fstToSum _ _ _ _ x

@[simp]
theorem besselPotentialSpaceSumToMin_sndToSum (x : H^{s₁, p}(E, F)) :
    besselPotentialSpaceSumToMin E F p s₀ s₁ ((besselPotentialSpace E F s₀ p s₁ p).sndToSum x) =
      inclusion (min_le_right s₀ s₁) x :=
  sumLift_sndToSum _ _ _ _ x

@[simp]
theorem toDistr_besselPotentialSpaceSumToMin (w : (besselPotentialSpace E F s₀ p s₁ p).SumSpace) :
    (besselPotentialSpaceSumToMin E F p s₀ s₁ w).toDistr =
      (besselPotentialSpace E F s₀ p s₁ p).sumSpaceEmbed w := by
  obtain ⟨x₀, x₁, rfl⟩ := (besselPotentialSpace E F s₀ p s₁ p).exists_fstToSum_add_sndToSum_eq w
  simp [toDistr_inclusion]

/-- A pair `(u₀, u₁)` lies in the intersection of `(H^{s₀,p}, H^{s₁,p})` if and only if `u₀` and
`u₁` represent the same tempered distribution. -/
theorem mem_besselPotentialSpace_inter_iff {x : H^{s₀, p}(E, F) × H^{s₁, p}(E, F)} :
    x ∈ (besselPotentialSpace E F s₀ p s₁ p).inter ↔ x.1.toDistr = x.2.toDistr := by
  simp [mem_inter_iff]

/-- Two decompositions in `H^{s₀,p} + H^{s₁,p}` agree if and only if their sums agree in
`𝓢'(E, F)`. -/
theorem besselPotentialSpace_fstToSum_add_sndToSum_eq_iff
    {u₀ v₀ : H^{s₀, p}(E, F)} {u₁ v₁ : H^{s₁, p}(E, F)} :
    (besselPotentialSpace E F s₀ p s₁ p).fstToSum u₀ +
          (besselPotentialSpace E F s₀ p s₁ p).sndToSum u₁ =
        (besselPotentialSpace E F s₀ p s₁ p).fstToSum v₀ +
          (besselPotentialSpace E F s₀ p s₁ p).sndToSum v₁ ↔
      u₀.toDistr + u₁.toDistr = v₀.toDistr + v₁.toDistr := by
  rw [← (besselPotentialSpace E F s₀ p s₁ p).sumSpaceEmbed_injective.eq_iff]
  simp

private theorem besovOneToBesselPotentialSpaceSum_compat {φ : ContDiffBump (0 : E)}
    (x : (besov F φ s₀ s₁ p 1 1).inter) :
    (besselPotentialSpace E F s₀ p s₁ p).fstToSum
        (BesovSpace.toBesselPotentialSpace ((besov F φ s₀ s₁ p 1 1).interFst x)) =
      (besselPotentialSpace E F s₀ p s₁ p).sndToSum
        (BesovSpace.toBesselPotentialSpace ((besov F φ s₀ s₁ p 1 1).interSnd x)) :=
  (besselPotentialSpace E F s₀ p s₁ p).sumSpace_ext <| by
    simpa using (besov F φ s₀ s₁ p 1 1).embed₀_interFst x

/-- The continuous inclusion `B^{s₀}_{p,1} + B^{s₁}_{p,1} →L[ℂ] H^{s₀,p} + H^{s₁,p}` induced by
`TauCeti.BesovSpace.toBesselPotentialSpace` on each endpoint. -/
def besovOneToBesselPotentialSpaceSum {φ : ContDiffBump (0 : E)} :
    (besov F φ s₀ s₁ p 1 1).SumSpace →L[ℂ] (besselPotentialSpace E F s₀ p s₁ p).SumSpace :=
  (besov F φ s₀ s₁ p 1 1).sumLift
    ((besselPotentialSpace E F s₀ p s₁ p).fstToSum.comp BesovSpace.toBesselPotentialSpace)
    ((besselPotentialSpace E F s₀ p s₁ p).sndToSum.comp BesovSpace.toBesselPotentialSpace)
    besovOneToBesselPotentialSpaceSum_compat

@[simp]
theorem besovOneToBesselPotentialSpaceSum_fstToSum {φ : ContDiffBump (0 : E)}
    (u₀ : BesovSpace F φ s₀ p 1) :
    besovOneToBesselPotentialSpaceSum ((besov F φ s₀ s₁ p 1 1).fstToSum u₀) =
      (besselPotentialSpace E F s₀ p s₁ p).fstToSum (BesovSpace.toBesselPotentialSpace u₀) := by
  rw [besovOneToBesselPotentialSpaceSum]
  exact ((besov F φ s₀ s₁ p 1 1).sumLift_fstToSum _ _ _ u₀).trans (by simp)

@[simp]
theorem besovOneToBesselPotentialSpaceSum_sndToSum {φ : ContDiffBump (0 : E)}
    (u₁ : BesovSpace F φ s₁ p 1) :
    besovOneToBesselPotentialSpaceSum ((besov F φ s₀ s₁ p 1 1).sndToSum u₁) =
      (besselPotentialSpace E F s₀ p s₁ p).sndToSum (BesovSpace.toBesselPotentialSpace u₁) := by
  rw [besovOneToBesselPotentialSpaceSum]
  exact ((besov F φ s₀ s₁ p 1 1).sumLift_sndToSum _ _ _ u₁).trans (by simp)

@[simp]
theorem sumSpaceEmbed_besovOneToBesselPotentialSpaceSum {φ : ContDiffBump (0 : E)}
    (u : (besov F φ s₀ s₁ p 1 1).SumSpace) :
    (besselPotentialSpace E F s₀ p s₁ p).sumSpaceEmbed (besovOneToBesselPotentialSpaceSum u) =
      (besov F φ s₀ s₁ p 1 1).sumSpaceEmbed u := by
  obtain ⟨u₀, u₁, rfl⟩ := (besov F φ s₀ s₁ p 1 1).exists_fstToSum_add_sndToSum_eq u
  simp

private theorem besselPotentialSpaceToBesovTopSum_compat (φ : ContDiffBump (0 : E))
    (x : (besselPotentialSpace E F s₀ p s₁ p).inter) :
    (besov F φ s₀ s₁ p ∞ ∞).fstToSum
        (toBesovSpace φ ((besselPotentialSpace E F s₀ p s₁ p).interFst x)) =
      (besov F φ s₀ s₁ p ∞ ∞).sndToSum
        (toBesovSpace φ ((besselPotentialSpace E F s₀ p s₁ p).interSnd x)) :=
  (besov F φ s₀ s₁ p ∞ ∞).sumSpace_ext <| by
    simpa using (besselPotentialSpace E F s₀ p s₁ p).embed₀_interFst x

/-- The continuous inclusion `H^{s₀,p} + H^{s₁,p} →L[ℂ] B^{s₀}_{p,∞} + B^{s₁}_{p,∞}` induced by
`BesselPotentialSpace.toBesovSpace` on each endpoint. -/
def besselPotentialSpaceToBesovTopSum (φ : ContDiffBump (0 : E)) :
    (besselPotentialSpace E F s₀ p s₁ p).SumSpace →L[ℂ] (besov F φ s₀ s₁ p ∞ ∞).SumSpace :=
  (besselPotentialSpace E F s₀ p s₁ p).sumLift
    ((besov F φ s₀ s₁ p ∞ ∞).fstToSum.comp (toBesovSpace φ))
    ((besov F φ s₀ s₁ p ∞ ∞).sndToSum.comp (toBesovSpace φ))
    (besselPotentialSpaceToBesovTopSum_compat φ)

@[simp]
theorem besselPotentialSpaceToBesovTopSum_fstToSum (φ : ContDiffBump (0 : E))
    (u₀ : H^{s₀, p}(E, F)) :
    besselPotentialSpaceToBesovTopSum φ ((besselPotentialSpace E F s₀ p s₁ p).fstToSum u₀) =
      (besov F φ s₀ s₁ p ∞ ∞).fstToSum (toBesovSpace φ u₀) := by
  rw [besselPotentialSpaceToBesovTopSum]
  exact ((besselPotentialSpace E F s₀ p s₁ p).sumLift_fstToSum _ _ _ u₀).trans (by simp)

@[simp]
theorem besselPotentialSpaceToBesovTopSum_sndToSum (φ : ContDiffBump (0 : E))
    (u₁ : H^{s₁, p}(E, F)) :
    besselPotentialSpaceToBesovTopSum φ ((besselPotentialSpace E F s₀ p s₁ p).sndToSum u₁) =
      (besov F φ s₀ s₁ p ∞ ∞).sndToSum (toBesovSpace φ u₁) := by
  rw [besselPotentialSpaceToBesovTopSum]
  exact ((besselPotentialSpace E F s₀ p s₁ p).sumLift_sndToSum _ _ _ u₁).trans (by simp)

@[simp]
theorem sumSpaceEmbed_besselPotentialSpaceToBesovTopSum (φ : ContDiffBump (0 : E))
    (u : (besselPotentialSpace E F s₀ p s₁ p).SumSpace) :
    (besov F φ s₀ s₁ p ∞ ∞).sumSpaceEmbed (besselPotentialSpaceToBesovTopSum φ u) =
      (besselPotentialSpace E F s₀ p s₁ p).sumSpaceEmbed u := by
  obtain ⟨u₀, u₁, rfl⟩ := (besselPotentialSpace E F s₀ p s₁ p).exists_fstToSum_add_sndToSum_eq u
  simp

end Couple

/-! ### Real interpolation of `H^{s,p}` -/

/-- Every tempered distribution in `B^{(1 - θ) s₀ + θ s₁}_{p,q}` lies in the sum space of
`(H^{s₀,p}, H^{s₁,p})` when `s₀ ≠ s₁` and `0 < θ < 1`: it lies in `B^{s₀}_{p,1} + B^{s₁}_{p,1}`,
which embeds into `H^{s₀,p} + H^{s₁,p}`. -/
theorem mem_range_sumSpaceEmbed_besselPotentialSpace {p q : ℝ≥0∞} [Fact (1 ≤ p)]
    {φ : ContDiffBump (0 : E)} {s₀ s₁ θ : ℝ} (hs : s₀ ≠ s₁) (hθ : θ ∈ Ioo 0 1) {u : 𝓢'(E, F)}
    (hu : u.MemBesov φ ((1 - θ) * s₀ + θ * s₁) p q) :
    u ∈ range (besselPotentialSpace E F s₀ p s₁ p).sumSpaceEmbed := by
  obtain ⟨w, rfl⟩ := mem_range_sumSpaceEmbed_besov (q₀ := 1) (q₁ := 1) hs hθ hu
  exact ⟨besovOneToBesselPotentialSpaceSum w, by simp⟩

section Interpolation

variable {p : ℝ≥0∞} [Fact (1 ≤ p)] (φ : ContDiffBump (0 : E)) {s₀ s₁ θ : ℝ} {q : ℝ≥0∞}

section Equiv

variable [Fact (1 ≤ q)] (hs : s₀ ≠ s₁) (hθ : θ ∈ Ioo 0 1)

private def besovOneToBesselPotentialSpaceKMethod {φ : ContDiffBump (0 : E)} :
    (besov F φ s₀ s₁ p 1 1).KMethodSpace θ q →L[ℂ]
      (besselPotentialSpace E F s₀ p s₁ p).KMethodSpace θ q :=
  map besovOneToBesselPotentialSpaceSum.toLinearMap
    (T₀ := BesovSpace.toBesselPotentialSpace)
    (T₁ := BesovSpace.toBesselPotentialSpace)
    (fun x ↦ by simp) (fun x ↦ by simp)

private def besselPotentialSpaceToBesovTopKMethod :
    (besselPotentialSpace E F s₀ p s₁ p).KMethodSpace θ q →L[ℂ]
      (besov F φ s₀ s₁ p ∞ ∞).KMethodSpace θ q :=
  map (besselPotentialSpaceToBesovTopSum φ).toLinearMap
    (T₀ := toBesovSpace φ)
    (T₁ := toBesovSpace φ)
    (fun x ↦ by simp) (fun x ↦ by simp)

/-- **Real interpolation of Bessel-potential spaces** (Bergh–Löfström, Theorems 6.2.4 and
6.4.5(4)). For `s₀ ≠ s₁`, `0 < θ < 1`, `1 ≤ p ≤ ∞` and `1 ≤ q ≤ ∞`, the real interpolation space
`(H^{s₀,p}, H^{s₁,p})_{θ,q}` is the Besov space `B^{s_θ}_{p,q}` with `s_θ = (1 - θ) s₀ + θ s₁`,
with equivalent norms. The isomorphism keeps the underlying tempered distribution
(`TauCeti.CompatibleCouple.toDistr_besselPotentialSpaceKMethodEquiv_apply`). -/
def besselPotentialSpaceKMethodEquiv :
    (besselPotentialSpace E F s₀ p s₁ p).KMethodSpace θ q ≃L[ℂ]
      BesovSpace F φ ((1 - θ) * s₀ + θ * s₁) p q :=
  ContinuousLinearEquiv.ofContinuousLinearMap
    ((besovKMethodEquiv (q₀ := ∞) (q₁ := ∞) hs hθ).toContinuousLinearMap.comp
      (besselPotentialSpaceToBesovTopKMethod φ))
    (besovOneToBesselPotentialSpaceKMethod.comp
      (besovKMethodEquiv (q₀ := 1) (q₁ := 1) hs hθ).symm.toContinuousLinearMap)
    (ContinuousLinearMap.ext fun v ↦ BesovSpace.ext <| by
      simp [besovOneToBesselPotentialSpaceKMethod, besselPotentialSpaceToBesovTopKMethod])
    (ContinuousLinearMap.ext fun u ↦ KMethodSpace.ext <|
      (besselPotentialSpace E F s₀ p s₁ p).sumSpace_ext <| by
        simp [besovOneToBesselPotentialSpaceKMethod, besselPotentialSpaceToBesovTopKMethod])

@[simp]
theorem toDistr_besselPotentialSpaceKMethodEquiv_apply
    (u : (besselPotentialSpace E F s₀ p s₁ p).KMethodSpace θ q) :
    (besselPotentialSpaceKMethodEquiv φ hs hθ u).toDistr =
      (besselPotentialSpace E F s₀ p s₁ p).sumSpaceEmbed (toSumₗ u) := by
  simp [besselPotentialSpaceKMethodEquiv, besselPotentialSpaceToBesovTopKMethod]

@[simp]
theorem sumSpaceEmbed_toSumₗ_besselPotentialSpaceKMethodEquiv_symm_apply
    (v : BesovSpace F φ ((1 - θ) * s₀ + θ * s₁) p q) :
    (besselPotentialSpace E F s₀ p s₁ p).sumSpaceEmbed
        (toSumₗ ((besselPotentialSpaceKMethodEquiv φ hs hθ).symm v)) = v.toDistr := by
  rw [← toDistr_besselPotentialSpaceKMethodEquiv_apply φ hs hθ,
    ContinuousLinearEquiv.apply_symm_apply]

end Equiv

/-- **Real interpolation of Bessel-potential spaces**, membership form: for `s₀ ≠ s₁`,
`0 < θ < 1` and `1 ≤ q`, an element `u` of `H^{s₀,p} + H^{s₁,p}` lies in
`(H^{s₀,p}, H^{s₁,p})_{θ,q}` exactly when its tempered distribution lies in the Besov space
`B^{s_θ}_{p,q}`, where `s_θ = (1 - θ) s₀ + θ s₁`. -/
theorem mem_kMethod_besselPotentialSpace_iff (hs : s₀ ≠ s₁) (hθ : θ ∈ Ioo 0 1) (hq : 1 ≤ q)
    {u : (besselPotentialSpace E F s₀ p s₁ p).SumSpace} :
    u ∈ (besselPotentialSpace E F s₀ p s₁ p).kMethod θ q ↔
      ((besselPotentialSpace E F s₀ p s₁ p).sumSpaceEmbed u).MemBesov φ
        ((1 - θ) * s₀ + θ * s₁) p q := by
  have : Fact (1 ≤ q) := ⟨hq⟩
  refine ⟨fun hu ↦ ?_, fun hu ↦ ?_⟩
  · simpa using (besselPotentialSpaceKMethodEquiv φ hs hθ (KMethodSpace.mk u hu)).memBesov_toDistr
  · have h := sumSpaceEmbed_toSumₗ_besselPotentialSpaceKMethodEquiv_symm_apply φ hs hθ
      hu.toBesovSpace
    rw [MemBesov.toDistr_toBesovSpace] at h
    rw [← sumSpace_ext _ h]
    exact toSumₗ_mem _

/-- **Real interpolation of Bessel-potential spaces**, image form: for `s₀ ≠ s₁`, `0 < θ < 1`
and `1 ≤ q`, a tempered distribution lies in the Besov space `B^{s_θ}_{p,q}`, where
`s_θ = (1 - θ) s₀ + θ s₁`, exactly when it is the image of an element of
`(H^{s₀,p}, H^{s₁,p})_{θ,q}`. -/
theorem memBesov_iff_exists_mem_kMethod_besselPotentialSpace (hs : s₀ ≠ s₁) (hθ : θ ∈ Ioo 0 1)
    (hq : 1 ≤ q) {v : 𝓢'(E, F)} :
    v.MemBesov φ ((1 - θ) * s₀ + θ * s₁) p q ↔
      ∃ u ∈ (besselPotentialSpace E F s₀ p s₁ p).kMethod θ q,
        (besselPotentialSpace E F s₀ p s₁ p).sumSpaceEmbed u = v := by
  refine ⟨fun hv ↦ ?_, ?_⟩
  · have : Fact (1 ≤ q) := ⟨hq⟩
    exact ⟨_, toSumₗ_mem ((besselPotentialSpaceKMethodEquiv φ hs hθ).symm hv.toBesovSpace),
      by simp⟩
  · rintro ⟨u, hu, rfl⟩
    exact (mem_kMethod_besselPotentialSpace_iff φ hs hθ hq).1 hu

end Interpolation

end Banach

/-! ### The `L²` Hilbert-space Sobolev scale -/

section Hilbert

variable {E H : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H] {s₀ s₁ θ : ℝ}

/-- Every tempered distribution in `H^{(1 - θ) s₀ + θ s₁}(E, H)` lies in the sum space of
`(H^{s₀}(E, H), H^{s₁}(E, H))` when `s₀ ≠ s₁` and `0 < θ < 1`. -/
theorem mem_range_sumSpaceEmbed_besselPotentialSpace_two (hs : s₀ ≠ s₁) (hθ : θ ∈ Ioo 0 1)
    {u : 𝓢'(E, H)} (hu : u.MemSobolev ((1 - θ) * s₀ + θ * s₁) 2) :
    u ∈ range (besselPotentialSpace E H s₀ 2 s₁ 2).sumSpaceEmbed :=
  mem_range_sumSpaceEmbed_besselPotentialSpace hs hθ
    ((memBesov_two_two_iff_memSobolev (default : ContDiffBump (0 : E))).2 hu)

/-- **Real interpolation of Hilbert-space Sobolev spaces**, membership form: for `s₀ ≠ s₁` and
`0 < θ < 1`, an element of `H^{s₀}(E, H) + H^{s₁}(E, H)` lies in
`(H^{s₀}(E, H), H^{s₁}(E, H))_{θ,2}` if and only if its ambient tempered distribution lies in
`H^{(1 - θ) s₀ + θ s₁}(E, H)`. -/
theorem mem_kMethod_besselPotentialSpace_two_iff (hs : s₀ ≠ s₁) (hθ : θ ∈ Ioo 0 1)
    {u : (besselPotentialSpace E H s₀ 2 s₁ 2).SumSpace} :
    u ∈ (besselPotentialSpace E H s₀ 2 s₁ 2).kMethod θ 2 ↔
      ((besselPotentialSpace E H s₀ 2 s₁ 2).sumSpaceEmbed u).MemSobolev
        ((1 - θ) * s₀ + θ * s₁) 2 := by
  rw [mem_kMethod_besselPotentialSpace_iff (default : ContDiffBump (0 : E)) hs hθ
    (Fact.out : (1 : ℝ≥0∞) ≤ 2), memBesov_two_two_iff_memSobolev]

/-- **Real interpolation of Hilbert-space Sobolev spaces**, image form: for `s₀ ≠ s₁` and
`0 < θ < 1`, a tempered distribution lies in `H^{(1 - θ) s₀ + θ s₁}(E, H)` if and only if it is the
image of an element of `(H^{s₀}(E, H), H^{s₁}(E, H))_{θ,2}`. -/
theorem memSobolev_iff_exists_mem_kMethod_besselPotentialSpace_two (hs : s₀ ≠ s₁) (hθ : θ ∈ Ioo 0 1)
    {v : 𝓢'(E, H)} :
    v.MemSobolev ((1 - θ) * s₀ + θ * s₁) 2 ↔
      ∃ u ∈ (besselPotentialSpace E H s₀ 2 s₁ 2).kMethod θ 2,
        (besselPotentialSpace E H s₀ 2 s₁ 2).sumSpaceEmbed u = v := by
  rw [← memBesov_two_two_iff_memSobolev (default : ContDiffBump (0 : E)),
    memBesov_iff_exists_mem_kMethod_besselPotentialSpace _ hs hθ (Fact.out : (1 : ℝ≥0∞) ≤ 2)]

/-- **Real interpolation of Hilbert-space Sobolev spaces.** For distinct orders `s₀ ≠ s₁` and
`0 < θ < 1`, the real interpolation space `(H^{s₀}(E, H), H^{s₁}(E, H))_{θ,2}` is isomorphic as a
Banach space to `H^{(1 - θ) s₀ + θ s₁}(E, H)` via the ambient tempered distribution. -/
def besselPotentialSpaceHilbertKMethodEquiv (hs : s₀ ≠ s₁) (hθ : θ ∈ Ioo 0 1) :
    (besselPotentialSpace E H s₀ 2 s₁ 2).KMethodSpace θ 2 ≃L[ℂ]
      H^{(1 - θ) * s₀ + θ * s₁}(E, H) :=
  (besselPotentialSpaceKMethodEquiv (default : ContDiffBump (0 : E)) hs hθ).trans
    (BesovSpace.besselPotentialSpaceEquiv H (default : ContDiffBump (0 : E))
      ((1 - θ) * s₀ + θ * s₁))

@[simp]
theorem toDistr_besselPotentialSpaceHilbertKMethodEquiv_apply (hs : s₀ ≠ s₁) (hθ : θ ∈ Ioo 0 1)
    (u : (besselPotentialSpace E H s₀ 2 s₁ 2).KMethodSpace θ 2) :
    (besselPotentialSpaceHilbertKMethodEquiv hs hθ u).toDistr =
      (besselPotentialSpace E H s₀ 2 s₁ 2).sumSpaceEmbed (toSumₗ u) := by
  simp [besselPotentialSpaceHilbertKMethodEquiv]

@[simp]
theorem sumSpaceEmbed_toSumₗ_besselPotentialSpaceHilbertKMethodEquiv_symm_apply
    (hs : s₀ ≠ s₁) (hθ : θ ∈ Ioo 0 1)
    (v : H^{(1 - θ) * s₀ + θ * s₁}(E, H)) :
    (besselPotentialSpace E H s₀ 2 s₁ 2).sumSpaceEmbed
        (toSumₗ ((besselPotentialSpaceHilbertKMethodEquiv hs hθ).symm v)) =
      v.toDistr := by
  rw [← toDistr_besselPotentialSpaceHilbertKMethodEquiv_apply hs hθ,
    ContinuousLinearEquiv.apply_symm_apply]

end Hilbert

end CompatibleCouple

end TauCeti
