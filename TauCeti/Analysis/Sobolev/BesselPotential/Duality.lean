/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.FunctionalSpaces.BesselPotentialSpace
public import Mathlib.Analysis.InnerProductSpace.Dual
public import Mathlib.MeasureTheory.Function.Holder
public import TauCeti.Analysis.Sobolev.BesselPotential.Schwartz
import TauCeti.Analysis.Distribution.SchwartzSpace.Fourier
import TauCeti.Analysis.Sobolev.BesselPotential.Multiplication

/-!
# The density pairing of the Bessel-potential spaces `H^{s,p}` and `H^{-s,q}`

Let `E` be a finite-dimensional real inner product space, `1 / p + 1 / q = 1`, and let
`B : F →L[ℂ] G →L[ℂ] K` be a continuous bilinear map, for instance the evaluation pairing of a
fiber `F` with its dual. Writing `J^s = 𝓕⁻ (⟨ξ⟩ ^ s 𝓕 ·)` for the Bessel potential, an element `u`
of Mathlib's Bessel-potential space `H^{s,p}(E, F)` is a tempered distribution with
`J^s u ∈ Lᵖ`, and `J^s u` is its `Lᵖ` part `u.toLp`. The **density pairing**

`⟨u, w⟩ = ∫ B ((J^s u) x) ((J^{-s} w) x) dx`,  `u ∈ H^{s,p}(E, F)`, `w ∈ H^{-s,q}(E, G)`,

pairs the `Lᵖ` and `L^q` parts by Hölder's inequality, with reciprocal Fourier weights
`⟨ξ⟩ ^ s` and `⟨ξ⟩ ^ (-s)`. It is the continuous extension of `∫ B (φ x) (ψ x) dx` from Schwartz
functions: the Bessel potentials have the even symbol `⟨ξ⟩ ^ s`, so they are symmetric for the
bilinear pairing (`SchwartzMap.integral_bilin_fourierMultiplierCLM_eq`), and `J^s` and `J^{-s}`
cancel. For scalar test functions it is the distributional action `u ψ` of `u`.

For `p = 2` and a complex Hilbert space `F`, the pairing of `H^s(E, F)` with `H^{-s}(E, F⋆)`,
`F⋆ = StrongDual ℂ F`, identifies `H^{-s}(E, F⋆)` isometrically with the continuous dual of
`H^s(E, F)`. This is the duality between positive and negative order Sobolev spaces used to extend
operators to distributions by transposition. The pairing is bilinear, not sesquilinear: no complex
conjugation is involved, and the identification is complex-linear.

## Main declarations

* `ContinuousLinearMap.besselPotentialPairing B s p q`: the density pairing
  `H^{s,p}(E, F) × H^{-s,q}(E, G) → K` induced by `B`, as a continuous bilinear map.
* `ContinuousLinearMap.besselPotentialPairing_apply`: its integral formula.
* `ContinuousLinearMap.norm_besselPotentialPairing_le`: `‖⟨u, w⟩‖ ≤ ‖B‖ ‖u‖ ‖w‖`.
* `ContinuousLinearMap.besselPotentialPairing_toBesselPotentialSpaceCLM`: on Schwartz functions
  the pairing is `∫ B (φ x) (ψ x) dx`, and
  `ContinuousLinearMap.eq_besselPotentialPairing_of_forall`: for `p, q < ∞` it is the only
  continuous bilinear map with this property.
* `BesselPotentialSpace.toDistr_apply_eq_besselPotentialPairing`: the distribution `u` acts on a
  scalar Schwartz function `ψ` by `u ψ = ⟨u, ψ⟩`.
* `BesselPotentialSpace.dualEquiv`: the isometric isomorphism
  `H^{-s}(E, F⋆) ≃ₗᵢ[ℂ] (H^s(E, F))⋆` given by the density pairing, with
  `BesselPotentialSpace.dualEquiv_apply_eq_integral` and its Schwartz-function form
  `BesselPotentialSpace.dualEquiv_toBesselPotentialSpaceCLM`.

## References

* G. B. Folland, *Real Analysis: Modern Techniques and Their Applications*, 2nd ed., Wiley, 1999,
  §9.3 (the dual of `H_s` is `H_{-s}` under the extension of the bilinear pairing of Schwartz
  functions).
* M. E. Taylor, *Partial Differential Equations I*, 2nd ed., Springer, 2011, Chapter 4, §1.
-/

public section

noncomputable section

open MeasureTheory FourierTransform
open scoped ENNReal SchwartzMap BesselPotentialSpace

variable {E F G K : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [NormedAddCommGroup G] [NormedSpace ℂ G]
  [NormedAddCommGroup K] [NormedSpace ℂ K]

namespace ContinuousLinearMap

variable [CompleteSpace F] [CompleteSpace G] [CompleteSpace K]

/-- The **density pairing** `⟨u, w⟩ = ∫ B ((J^s u) x) ((J^{-s} w) x) dx` of the Bessel-potential
spaces `H^{s,p}(E, F)` and `H^{-s,q}(E, G)` for Hölder conjugate `p` and `q`, induced by a
continuous bilinear map `B`. It pairs the `Lᵖ` and `L^q` parts of `u` and `w` by Mathlib's
`ContinuousLinearMap.lpPairing`, and extends `∫ B (φ x) (ψ x) dx` from Schwartz functions
(`ContinuousLinearMap.besselPotentialPairing_toBesselPotentialSpaceCLM`). -/
def besselPotentialPairing (B : F →L[ℂ] G →L[ℂ] K) (s : ℝ) (p q : ℝ≥0∞) [Fact (1 ≤ p)]
    [Fact (1 ≤ q)] [p.HolderConjugate q] :
    H^{s, p}(E, F) →L[ℂ] H^{-s, q}(E, G) →L[ℂ] K :=
  (B.lpPairing volume p q).bilinearComp
    (BesselPotentialSpace.toLpₗᵢ E F s p).toLinearIsometry.toContinuousLinearMap
    (BesselPotentialSpace.toLpₗᵢ E G (-s) q).toLinearIsometry.toContinuousLinearMap

variable {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)] [p.HolderConjugate q]

/-- The density pairing is the integral of `B` applied to the `Lᵖ` and `L^q` parts. -/
theorem besselPotentialPairing_apply (B : F →L[ℂ] G →L[ℂ] K) (s : ℝ) (u : H^{s, p}(E, F))
    (w : H^{-s, q}(E, G)) :
    B.besselPotentialPairing s p q u w = ∫ x, B (u.toLp x) (w.toLp x) := by
  simp [besselPotentialPairing, lpPairing_eq_integral]

/-- Hölder's inequality for the density pairing: `‖⟨u, w⟩‖ ≤ ‖B‖ ‖u‖_{H^{s,p}} ‖w‖_{H^{-s,q}}`. -/
theorem norm_besselPotentialPairing_le (B : F →L[ℂ] G →L[ℂ] K) (s : ℝ) (u : H^{s, p}(E, F))
    (w : H^{-s, q}(E, G)) :
    ‖B.besselPotentialPairing s p q u w‖ ≤ ‖B‖ * ‖u‖ * ‖w‖ := by
  rw [besselPotentialPairing_apply, ← BesselPotentialSpace.norm_toLp_eq u,
    ← BesselPotentialSpace.norm_toLp_eq w]
  calc ‖∫ x, B (u.toLp x) (w.toLp x)‖ ≤ ∫ x, ‖B (u.toLp x) (w.toLp x)‖ :=
        norm_integral_le_integral_norm _
    _ = ‖B.holder 1 u.toLp w.toLp‖ := by
        rw [L1.norm_eq_integral_norm]
        exact integral_congr_ae ((B.coeFn_holder (r := 1) u.toLp w.toLp).mono fun x hx ↦ by
          simp only [hx])
    _ ≤ ‖B‖ * ‖u.toLp‖ * ‖w.toLp‖ := B.norm_holder_apply_apply_le _ _

/-- On Schwartz functions the density pairing is the integral `∫ B (φ x) (ψ x) dx`, whatever the
order `s`: the Bessel potentials `J^s` and `J^{-s}` of the two factors cancel. -/
theorem besselPotentialPairing_toBesselPotentialSpaceCLM (B : F →L[ℂ] G →L[ℂ] K) (s : ℝ)
    (φ : 𝓢(E, F)) (ψ : 𝓢(E, G)) :
    B.besselPotentialPairing s p q (SchwartzMap.toBesselPotentialSpaceCLM s p φ)
        (SchwartzMap.toBesselPotentialSpaceCLM (-s) q ψ) = ∫ x, B (φ x) (ψ x) := by
  rw [besselPotentialPairing_apply, SchwartzMap.toLp_toBesselPotentialSpaceCLM,
    SchwartzMap.toLp_toBesselPotentialSpaceCLM]
  calc _ = ∫ x, B (SchwartzMap.fourierMultiplierCLM F
          (fun x : E ↦ (((1 + ‖x‖ ^ 2) ^ (s / 2) : ℝ) : ℂ)) φ x)
        (SchwartzMap.fourierMultiplierCLM G
          (fun x : E ↦ (((1 + ‖x‖ ^ 2) ^ (-s / 2) : ℝ) : ℂ)) ψ x) := by
        refine integral_congr_ae ?_
        filter_upwards [SchwartzMap.coeFn_toLp (SchwartzMap.fourierMultiplierCLM F
            (fun x : E ↦ (((1 + ‖x‖ ^ 2) ^ (s / 2) : ℝ) : ℂ)) φ) p volume,
          SchwartzMap.coeFn_toLp (SchwartzMap.fourierMultiplierCLM G
            (fun x : E ↦ (((1 + ‖x‖ ^ 2) ^ (-s / 2) : ℝ) : ℂ)) ψ) q volume] with x h₁ h₂
        rw [h₁, h₂]
    -- Move `J^s` to the second factor, where it cancels `J^{-s}`.
    _ = ∫ x, B (φ x) (ψ x) := by
        rw [SchwartzMap.integral_bilin_fourierMultiplierCLM_eq (by fun_prop) (by simp),
          SchwartzMap.fourierMultiplierCLM_one_add_norm_sq_rpow_fourierMultiplierCLM_neg]

/-- **Uniqueness of the density pairing.** For `p, q < ∞`, a continuous bilinear map on
`H^{s,p}(E, F) × H^{-s,q}(E, G)` that is `∫ B (φ x) (ψ x) dx` on Schwartz functions is the density
pairing, since Schwartz functions are dense in both factors. -/
theorem eq_besselPotentialPairing_of_forall (hp : p ≠ ∞) (hq : q ≠ ∞) (B : F →L[ℂ] G →L[ℂ] K)
    (s : ℝ) {T : H^{s, p}(E, F) →L[ℂ] H^{-s, q}(E, G) →L[ℂ] K}
    (hT : ∀ (φ : 𝓢(E, F)) (ψ : 𝓢(E, G)), T (SchwartzMap.toBesselPotentialSpaceCLM s p φ)
      (SchwartzMap.toBesselPotentialSpaceCLM (-s) q ψ) = ∫ x, B (φ x) (ψ x)) :
    T = B.besselPotentialPairing s p q :=
  BesselPotentialSpace.continuousLinearMap_ext hp fun φ ↦
    BesselPotentialSpace.continuousLinearMap_ext hq fun ψ ↦ by
      rw [hT, besselPotentialPairing_toBesselPotentialSpaceCLM]

end ContinuousLinearMap

namespace BesselPotentialSpace

section Distribution

variable [CompleteSpace F] {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)] [p.HolderConjugate q]

/-- The distribution underlying `u ∈ H^{s,p}(E, F)` acts on a scalar Schwartz function `ψ`, viewed
in `H^{-s,q}(E)`, by the density pairing with the scalar multiplication `(v, c) ↦ c • v`. -/
theorem toDistr_apply_eq_besselPotentialPairing {s : ℝ} (u : H^{s, p}(E, F)) (ψ : 𝓢(E, ℂ)) :
    u.toDistr ψ = (ContinuousLinearMap.lsmul ℂ ℂ).flip.besselPotentialPairing s p q u
      (SchwartzMap.toBesselPotentialSpaceCLM (-s) q ψ) := by
  rw [ContinuousLinearMap.besselPotentialPairing_apply, ← besselPotential_neg_toLp_eq (f := u),
    TemperedDistribution.besselPotential, TemperedDistribution.fourierMultiplierCLM_apply_apply,
    SchwartzMap.fourier_smulLeftCLM_fourierInv_eq (by fun_prop) (by simp),
    Lp.toTemperedDistribution_apply, SchwartzMap.toLp_toBesselPotentialSpaceCLM]
  refine integral_congr_ae ?_
  filter_upwards [SchwartzMap.coeFn_toLp (SchwartzMap.fourierMultiplierCLM ℂ
    (fun x : E ↦ (((1 + ‖x‖ ^ 2) ^ (-s / 2) : ℝ) : ℂ)) ψ) q volume] with x hx
  simp [hx]

end Distribution

section Dual

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

/-- The inner product of `H^s(E, F)` is the `L²` inner product of the `L²` parts. -/
@[simp]
theorem inner_toLp_toLp {s : ℝ} (f g : H^{s}(E, F)) : inner ℂ f.toLp g.toLp = inner ℂ f g :=
  rfl

/-- If `w ∈ H^{-s}(E, F⋆)` is pointwise the Riesz dual of `g ∈ H^s(E, F)`, then pairing with `w` is
taking the inner product with `g`. -/
private theorem besselPotentialPairing_eq_inner {s : ℝ} (w : H^{-s}(E, StrongDual ℂ F))
    (g : H^{s}(E, F)) (h : ∀ᵐ x, w.toLp x = InnerProductSpace.toDual ℂ F (g.toLp x))
    (u : H^{s}(E, F)) :
    (ContinuousLinearMap.id ℂ (StrongDual ℂ F)).flip.besselPotentialPairing s 2 2 u w =
      inner ℂ g u := by
  rw [ContinuousLinearMap.besselPotentialPairing_apply, ← inner_toLp_toLp, L2.inner_def]
  refine integral_congr_ae (h.mono fun x hx ↦ ?_)
  simp [hx]

/-- The density pairing as a linear isometry `H^{-s}(E, F⋆) → (H^s(E, F))⋆`. The norm of `w` is
attained on the element of `H^s(E, F)` whose `L²` part is the pointwise Riesz dual of the `L²` part
of `w`. -/
private def toDualₗᵢ (s : ℝ) : H^{-s}(E, StrongDual ℂ F) →ₗᵢ[ℂ] StrongDual ℂ H^{s}(E, F) where
  toLinearMap :=
    ((ContinuousLinearMap.id ℂ (StrongDual ℂ F)).flip.besselPotentialPairing (E := E) s 2 2).flip
  norm_map' w := by
    let J : StrongDual ℂ F →SL[starRingEnd ℂ] F :=
      (InnerProductSpace.toDual ℂ F).symm.toContinuousLinearEquiv
    have hg : ∀ᵐ x, w.toLp x =
        InnerProductSpace.toDual ℂ F ((ofLp s (J.compLp w.toLp)).toLp x) := by
      filter_upwards [J.coeFn_compLp w.toLp] with x hx
      rw [toLp_ofLp, hx]
      simp [J]
    have hw : ((ContinuousLinearMap.id ℂ (StrongDual ℂ F)).flip.besselPotentialPairing
        s 2 2).flip w = innerSL ℂ (ofLp s (J.compLp w.toLp)) :=
      ContinuousLinearMap.ext fun u ↦ besselPotentialPairing_eq_inner w _ hg u
    simp only [ContinuousLinearMap.coe_coe, hw, innerSL_apply_norm]
    rw [← norm_toLp_eq, ← norm_toLp_eq w, toLp_ofLp, Lp.norm_def, Lp.norm_def]
    congr 1
    refine eLpNorm_congr_norm_ae (Lp.aestronglyMeasurable _) (Lp.aestronglyMeasurable _)
      ((J.coeFn_compLp w.toLp).mono fun x hx ↦ ?_)
    rw [hx]
    simp [J]

private theorem toDualₗᵢ_apply (s : ℝ) (w : H^{-s}(E, StrongDual ℂ F)) (u : H^{s}(E, F)) :
    toDualₗᵢ s w u =
      (ContinuousLinearMap.id ℂ (StrongDual ℂ F)).flip.besselPotentialPairing s 2 2 u w :=
  rfl

/-- Every functional on `H^s(E, F)` is a density pairing: by the Riesz representation theorem it is
`⟪g, ·⟫` for some `g`, and the pointwise Riesz dual of `g` represents it. -/
private theorem toDualₗᵢ_surjective (s : ℝ) :
    Function.Surjective (toDualₗᵢ (E := E) (F := F) s) := by
  intro Λ
  let L : F →SL[starRingEnd ℂ] StrongDual ℂ F :=
    (InnerProductSpace.toDual ℂ F).toContinuousLinearEquiv
  refine ⟨ofLp (-s) (L.compLp ((InnerProductSpace.toDual ℂ H^{s}(E, F)).symm Λ).toLp),
    ContinuousLinearMap.ext fun u ↦ ?_⟩
  rw [toDualₗᵢ_apply, besselPotentialPairing_eq_inner _ _ ?_ u,
    InnerProductSpace.toDual_symm_apply]
  filter_upwards [L.coeFn_compLp ((InnerProductSpace.toDual ℂ H^{s}(E, F)).symm Λ).toLp]
    with x hx
  rw [toLp_ofLp, hx]
  simp [L]

/-- **Duality of the Bessel-potential spaces.** The density pairing
`⟨w, u⟩ = ∫ (J^{-s} w) x ((J^s u) x) dx` identifies `H^{-s}(E, F⋆)`, `F⋆ = StrongDual ℂ F`,
complex-linearly and isometrically with the continuous dual of `H^s(E, F)`, for every real `s` and
every complex Hilbert space `F`. -/
def dualEquiv (s : ℝ) : H^{-s}(E, StrongDual ℂ F) ≃ₗᵢ[ℂ] StrongDual ℂ H^{s}(E, F) :=
  LinearIsometryEquiv.ofSurjective (toDualₗᵢ s) (toDualₗᵢ_surjective s)

/-- `dualEquiv s w` is the density pairing with `w`, for the evaluation pairing of `F` with `F⋆`. -/
theorem dualEquiv_apply {s : ℝ} (w : H^{-s}(E, StrongDual ℂ F)) (u : H^{s}(E, F)) :
    dualEquiv s w u =
      (ContinuousLinearMap.id ℂ (StrongDual ℂ F)).flip.besselPotentialPairing s 2 2 u w := by
  rw [dualEquiv, LinearIsometryEquiv.coe_ofSurjective, toDualₗᵢ_apply]

/-- The integral formula for `dualEquiv`: `w` acts on `u` by `∫ (J^{-s} w) x ((J^s u) x) dx`. -/
theorem dualEquiv_apply_eq_integral {s : ℝ} (w : H^{-s}(E, StrongDual ℂ F)) (u : H^{s}(E, F)) :
    dualEquiv s w u = ∫ x, w.toLp x (u.toLp x) := by
  simp [dualEquiv_apply, ContinuousLinearMap.besselPotentialPairing_apply]

/-- On Schwartz functions `dualEquiv` is the integral of the pointwise evaluation pairing. -/
@[simp]
theorem dualEquiv_toBesselPotentialSpaceCLM {s : ℝ} (ψ : 𝓢(E, StrongDual ℂ F)) (φ : 𝓢(E, F)) :
    dualEquiv s (SchwartzMap.toBesselPotentialSpaceCLM (-s) 2 ψ)
        (SchwartzMap.toBesselPotentialSpaceCLM s 2 φ) = ∫ x, ψ x (φ x) := by
  simp [dualEquiv_apply, ContinuousLinearMap.besselPotentialPairing_toBesselPotentialSpaceCLM]

end Dual

end BesselPotentialSpace
