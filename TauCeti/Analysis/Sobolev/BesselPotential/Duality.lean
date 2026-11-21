/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.FunctionalSpaces.BesselPotentialSpace
public import Mathlib.Analysis.InnerProductSpace.Dual
public import Mathlib.MeasureTheory.Function.Holder
public import TauCeti.Analysis.Sobolev.BesselPotential.ComplexOrder
public import TauCeti.Analysis.Sobolev.BesselPotential.Inclusion
public import TauCeti.Analysis.Sobolev.BesselPotential.Schwartz
import Mathlib.Analysis.Normed.Operator.Extend
import TauCeti.Analysis.Distribution.SchwartzSpace.Fourier
import TauCeti.Analysis.Distribution.SchwartzSpace.ReciprocalWeight
import TauCeti.Analysis.Sobolev.BesselPotential.Multiplication
import TauCeti.Analysis.SpecialFunctions.JapaneseBracket.Peetre
import TauCeti.MeasureTheory.Function.L2Space

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
functions: the transpose of a Fourier multiplier for the bilinear pairing has the reflected
symbol (`SchwartzMap.integral_bilin_fourierMultiplierCLM_eq`), the Bessel potentials have the even
symbol `⟨ξ⟩ ^ s`, so they are symmetric, and `J^s` and `J^{-s}` cancel. For scalar test functions
it is the distributional action `u ψ` of `u`.

For `p = 2` and a complex Hilbert space `F`, the pairing of `H^s(E, F)` with `H^{-s}(E, F⋆)`,
`F⋆ = StrongDual ℂ F`, identifies `H^{-s}(E, F⋆)` isometrically with the continuous dual of
`H^s(E, F)`. This is the duality between positive and negative order Sobolev spaces used to extend
operators to distributions by transposition. The pairing is bilinear, not sesquilinear: no complex
conjugation is involved, and the identification is complex-linear.

The sesquilinear counterpart is the `L²` inner product: for Schwartz functions `a` and `b` with
values in a complex Hilbert space, the inner product of the `L²` parts of `a ∈ H^{-r}` and
`b ∈ H^r` is `∫ ⟪a, b⟫`, so `|∫ ⟪a, b⟫| ≤ ‖a‖_{H^{-r}} ‖b‖_{H^r}`.

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
* `BesselPotentialSpace.norm_toDistr_apply_le`: hence `‖u ψ‖ ≤ ‖u‖_{H^{s,p}} ‖ψ‖_{H^{-s,q}}`.
* `BesselPotentialSpace.dualEquiv`: the isometric isomorphism
  `H^{-s}(E, F⋆) ≃ₗᵢ[ℂ] (H^s(E, F))⋆` given by the density pairing, with
  `BesselPotentialSpace.dualEquiv_apply_eq_integral` and its Schwartz-function form
  `BesselPotentialSpace.dualEquiv_toBesselPotentialSpaceCLM`.
* `SchwartzMap.inner_toLp_toBesselPotentialSpaceCLM_neg`,
  `SchwartzMap.norm_integral_inner_le_norm_toBesselPotentialSpaceCLM_mul_norm`: the `L²` pairing
  of `H^{-r}` and `H^r` on Schwartz functions, and `|∫ ⟪a, b⟫| ≤ ‖a‖_{H^{-r}} ‖b‖_{H^r}`.
* `SchwartzMap.norm_toBesselPotentialSpaceCLM_neg_le_of_forall`: conversely, a bound
  `|∫ ⟪a, v⟫| ≤ C ‖v‖_{H^r}` for all Schwartz `v` gives `‖a‖_{H^{-r}} ≤ C`; together
  (`SchwartzMap.norm_toBesselPotentialSpaceCLM_neg_le_iff`), the `H^{-r}` norm is the dual norm of
  the `H^r` norm for the `L²` pairing.
* `SchwartzMap.inner_toLp_besselPotentialCLM_left`: the Bessel potentials `J^a` of real order are
  symmetric for the `L²` inner product of Schwartz functions.
* `BesselPotentialSpace.inner_inclusion_toBesselPotentialSpaceCLM`,
  `BesselPotentialSpace.norm_inner_inclusion_le`: for `m ≤ r`, the `H^m` inner product of
  `Y ∈ H^r` with a Schwartz function `φ` is `⟪Y, J^{2 (m - r)} φ⟫_{H^r}`, hence bounded by
  `‖φ‖_{H^{2m - r}} ‖Y‖_{H^r}`.
* `BesselPotentialSpace.exists_inclusion_eq_and_norm_le`: conversely, an element of `H^m` whose
  `H^m` inner products with Schwartz functions `φ` are bounded by `M ‖φ‖_{H^{2m - r}}` lies in
  `H^r`, with norm at most `M`.

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
@[simp]
theorem besselPotentialPairing_toBesselPotentialSpaceCLM (B : F →L[ℂ] G →L[ℂ] K) (s : ℝ)
    (φ : 𝓢(E, F)) (ψ : 𝓢(E, G)) :
    B.besselPotentialPairing s p q (SchwartzMap.toBesselPotentialSpaceCLM s p φ)
        (SchwartzMap.toBesselPotentialSpaceCLM (-s) q ψ) = ∫ x, B (φ x) (ψ x) := by
  rw [besselPotentialPairing_apply]
  calc _ = ∫ x, B (SchwartzMap.fourierMultiplierCLM F
          (fun x : E ↦ (((1 + ‖x‖ ^ 2) ^ (s / 2) : ℝ) : ℂ)) φ x)
        (SchwartzMap.fourierMultiplierCLM G
          (fun x : E ↦ (((1 + ‖x‖ ^ 2) ^ (-s / 2) : ℝ) : ℂ)) ψ x) := by
        refine integral_congr_ae ?_
        filter_upwards [SchwartzMap.coeFn_toLp_toBesselPotentialSpaceCLM (p := p) φ,
          SchwartzMap.coeFn_toLp_toBesselPotentialSpaceCLM (s := -s) (p := q) ψ] with x h₁ h₂
        rw [h₁, h₂]
    -- Move `J^s` to the second factor, where it cancels `J^{-s}`.
    _ = ∫ x, B (φ x) (ψ x) := by
        rw [SchwartzMap.integral_bilin_fourierMultiplierCLM_eq (by fun_prop)]
        simp only [norm_neg]
        rw [SchwartzMap.fourierMultiplierCLM_one_add_norm_sq_rpow_fourierMultiplierCLM_neg]

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

variable (q) in
/-- The distribution underlying `u ∈ H^{s,p}(E, F)` acts on a scalar Schwartz function `ψ`, viewed
in `H^{-s,q}(E)`, by the density pairing with the scalar multiplication `(v, c) ↦ c • v`. -/
theorem toDistr_apply_eq_besselPotentialPairing {s : ℝ} (u : H^{s, p}(E, F)) (ψ : 𝓢(E, ℂ)) :
    u.toDistr ψ = (ContinuousLinearMap.lsmul ℂ ℂ).flip.besselPotentialPairing s p q u
      (SchwartzMap.toBesselPotentialSpaceCLM (-s) q ψ) := by
  rw [ContinuousLinearMap.besselPotentialPairing_apply, ← besselPotential_neg_toLp_eq (f := u),
    TemperedDistribution.besselPotential, TemperedDistribution.fourierMultiplierCLM_apply_apply,
    SchwartzMap.fourier_smulLeftCLM_fourierInv_eq (by fun_prop)]
  simp only [norm_neg]
  rw [Lp.toTemperedDistribution_apply]
  refine integral_congr_ae ?_
  filter_upwards [SchwartzMap.coeFn_toLp_toBesselPotentialSpaceCLM (s := -s) (p := q) ψ] with x hx
  rw [hx]
  simp

variable (q) in
/-- The distribution underlying `u ∈ H^{s,p}(E, F)` is bounded on scalar Schwartz functions by the
dual norm: `‖u ψ‖ ≤ ‖u‖_{H^{s,p}} ‖ψ‖_{H^{-s,q}}`. -/
theorem norm_toDistr_apply_le {s : ℝ} (u : H^{s, p}(E, F)) (ψ : 𝓢(E, ℂ)) :
    ‖u.toDistr ψ‖ ≤ ‖u‖ * ‖SchwartzMap.toBesselPotentialSpaceCLM (-s) q ψ‖ := by
  rw [toDistr_apply_eq_besselPotentialPairing q]
  refine (ContinuousLinearMap.norm_besselPotentialPairing_le _ s u _).trans ?_
  rw [mul_assoc]
  refine mul_le_of_le_one_left (by positivity) ?_
  rw [ContinuousLinearMap.opNorm_flip]
  exact ContinuousLinearMap.opNorm_lsmul_le

end Distribution

section Dual

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

/-- The inner product of `H^s(E, F)` is the `L²` inner product of the `L²` parts. -/
@[simp]
theorem inner_toLp_toLp {s : ℝ} (f g : H^{s}(E, F)) : inner ℂ f.toLp g.toLp = inner ℂ f g :=
  rfl

/-- Composing the `L²` part of `v` pointwise with a semilinear map `T` gives an element of a
Bessel-potential space, of any order, whose `L²` part is `T ∘ v.toLp`. -/
private theorem exists_ae_toLp_eq_comp {F₁ F₂ : Type*} [NormedAddCommGroup F₁] [NormedSpace ℂ F₁]
    [CompleteSpace F₁] [NormedAddCommGroup F₂] [NormedSpace ℂ F₂] [CompleteSpace F₂]
    {σ : ℂ →+* ℂ} [RingHomIsometric σ]
    (T : F₁ →SL[σ] F₂) {s₁ : ℝ} (s₂ : ℝ) (v : H^{s₁}(E, F₁)) :
    ∃ v' : H^{s₂}(E, F₂), ∀ᵐ x, v'.toLp x = T (v.toLp x) :=
  ⟨ofLp s₂ (T.compLp v.toLp), by simpa using T.coeFn_compLp v.toLp⟩

variable {s : ℝ} {w : H^{-s}(E, StrongDual ℂ F)} {g : H^{s}(E, F)}

/-- If `w ∈ H^{-s}(E, F⋆)` is pointwise the Riesz dual of `g ∈ H^s(E, F)`, then pairing with `w` is
taking the inner product with `g`. -/
private theorem besselPotentialPairing_eq_inner
    (h : ∀ᵐ x, w.toLp x = InnerProductSpace.toDual ℂ F (g.toLp x)) (u : H^{s}(E, F)) :
    (ContinuousLinearMap.id ℂ (StrongDual ℂ F)).flip.besselPotentialPairing s 2 2 u w =
      inner ℂ g u := by
  rw [ContinuousLinearMap.besselPotentialPairing_apply, ← inner_toLp_toLp, L2.inner_def]
  refine integral_congr_ae (h.mono fun x hx ↦ ?_)
  simp [hx]

/-- If `w ∈ H^{-s}(E, F⋆)` is pointwise the Riesz dual of `g ∈ H^s(E, F)`, then `‖w‖ = ‖g‖`, since
the Riesz map is isometric. -/
private theorem norm_eq_of_ae_toLp_eq_toDual
    (h : ∀ᵐ x, w.toLp x = InnerProductSpace.toDual ℂ F (g.toLp x)) : ‖w‖ = ‖g‖ := by
  rw [← norm_toLp_eq, ← norm_toLp_eq g, Lp.norm_def, Lp.norm_def]
  congr 1
  exact eLpNorm_congr_norm_ae (Lp.aestronglyMeasurable _) (Lp.aestronglyMeasurable _)
    (h.mono fun x hx ↦ by simp [hx])

variable (s) in
/-- The density pairing as a linear isometry `H^{-s}(E, F⋆) → (H^s(E, F))⋆`. The norm of `w` is
attained on the element of `H^s(E, F)` whose `L²` part is the pointwise Riesz dual of the `L²` part
of `w`. -/
private def toDualₗᵢ : H^{-s}(E, StrongDual ℂ F) →ₗᵢ[ℂ] StrongDual ℂ H^{s}(E, F) where
  toLinearMap :=
    ((ContinuousLinearMap.id ℂ (StrongDual ℂ F)).flip.besselPotentialPairing (E := E) s 2 2).flip
  norm_map' w := by
    obtain ⟨g, hg⟩ := exists_ae_toLp_eq_comp
      ((InnerProductSpace.toDual ℂ F).symm.toContinuousLinearEquiv :
        StrongDual ℂ F →SL[starRingEnd ℂ] F) s w
    have hw : ∀ᵐ x, w.toLp x = InnerProductSpace.toDual ℂ F (g.toLp x) :=
      hg.mono fun x hx ↦ by simp [hx]
    have hT : ((ContinuousLinearMap.id ℂ (StrongDual ℂ F)).flip.besselPotentialPairing
        s 2 2).flip w = innerSL ℂ g :=
      ContinuousLinearMap.ext (besselPotentialPairing_eq_inner hw)
    simp only [ContinuousLinearMap.coe_coe, hT, innerSL_apply_norm, norm_eq_of_ae_toLp_eq_toDual hw]

variable (s) in
private theorem toDualₗᵢ_apply (w : H^{-s}(E, StrongDual ℂ F)) (u : H^{s}(E, F)) :
    toDualₗᵢ s w u =
      (ContinuousLinearMap.id ℂ (StrongDual ℂ F)).flip.besselPotentialPairing s 2 2 u w :=
  rfl

variable (s) in
/-- Every functional on `H^s(E, F)` is a density pairing: by the Riesz representation theorem it is
`⟪g, ·⟫` for some `g`, and the pointwise Riesz dual of `g` represents it. -/
private theorem toDualₗᵢ_surjective : Function.Surjective (toDualₗᵢ (E := E) (F := F) s) := by
  intro Λ
  obtain ⟨w, hw⟩ := exists_ae_toLp_eq_comp
    ((InnerProductSpace.toDual ℂ F).toContinuousLinearEquiv :
      F →SL[starRingEnd ℂ] StrongDual ℂ F) (-s) ((InnerProductSpace.toDual ℂ H^{s}(E, F)).symm Λ)
  refine ⟨w, ContinuousLinearMap.ext fun u ↦ ?_⟩
  rw [toDualₗᵢ_apply, besselPotentialPairing_eq_inner (by simpa using hw),
    InnerProductSpace.toDual_symm_apply]

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
  simp [dualEquiv_apply]

end Dual

end BesselPotentialSpace

namespace SchwartzMap

section L2Pairing

open scoped InnerProductSpace

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

/-- **The `L²` pairing of `H^{-r}` and `H^r`.** For Schwartz functions `a` and `b`, the `L²` inner
product of the `L²` parts of `a ∈ H^{-r}` and `b ∈ H^r` is `∫ ⟪a, b⟫`, for every real `r`. -/
theorem inner_toLp_toBesselPotentialSpaceCLM_neg (r : ℝ) (a b : 𝓢(E, F)) :
    ⟪(toBesselPotentialSpaceCLM (-r) 2 a).toLp, (toBesselPotentialSpaceCLM r 2 b).toLp⟫_ℂ =
      ∫ x, ⟪a x, b x⟫_ℂ := by
  -- The weights `⟨ξ⟩ ^ (-r)` and `⟨ξ⟩ ^ r` are reciprocal.
  rw [toLp_toBesselPotentialSpaceCLM, toLp_toBesselPotentialSpaceCLM,
    inner_toL2_toL2_eq _ _ volume, ← integral_inner_fourier_fourier,
    integral_inner_eq_integral_inner_smul_fourier
      (fun ξ ↦ (mul_comm _ _).trans (TauCeti.one_add_norm_sq_rpow_neg_mul_rpow ξ r)) a b]
  congr 1
  funext ξ
  simp only [fourierMultiplierCLM_apply, fourier_fourierInv_eq]
  rw [smulLeftCLM_apply_apply (by fun_prop), smulLeftCLM_apply_apply (by fun_prop)]

/-- **Duality of `H^{-r}` and `H^r` under the `L²` pairing**:
`|∫ ⟪a, b⟫| ≤ ‖a‖_{H^{-r}} ‖b‖_{H^r}` for Schwartz functions `a` and `b`. -/
theorem norm_integral_inner_le_norm_toBesselPotentialSpaceCLM_mul_norm (r : ℝ)
    (a b : 𝓢(E, F)) :
    ‖∫ x, ⟪a x, b x⟫_ℂ‖ ≤
      ‖toBesselPotentialSpaceCLM (-r) 2 a‖ * ‖toBesselPotentialSpaceCLM r 2 b‖ := by
  rw [← inner_toLp_toBesselPotentialSpaceCLM_neg r, ← BesselPotentialSpace.norm_toLp_eq,
    ← BesselPotentialSpace.norm_toLp_eq (toBesselPotentialSpaceCLM r 2 b)]
  exact norm_inner_le_norm _ _

/-- **The `H^{-r}` norm by duality.** If `‖∫ ⟪a, v⟫‖ ≤ C ‖v‖_{H^r}` for every Schwartz function
`v`, then `‖a‖_{H^{-r}} ≤ C`: the bound is attained, since the weights `⟨ξ⟩ ^ (-r)` and `⟨ξ⟩ ^ r`
are reciprocal (`SchwartzMap.eLpNorm_smul_fourier_le_of_forall_norm_integral_inner_le`). -/
theorem norm_toBesselPotentialSpaceCLM_neg_le_of_forall (r : ℝ) (a : 𝓢(E, F)) {C : ℝ}
    (hC : 0 ≤ C)
    (h : ∀ v : 𝓢(E, F), ‖∫ x, ⟪a x, v x⟫_ℂ‖ ≤ C * ‖toBesselPotentialSpaceCLM r 2 v‖) :
    ‖toBesselPotentialSpaceCLM (-r) 2 a‖ ≤ C := by
  simp only [norm_toBesselPotentialSpaceCLM] at h ⊢
  refine eLpNorm_smul_fourier_le_of_forall_norm_integral_inner_le (by fun_prop)
    (TauCeti.one_add_norm_sq_rpow_neg_mul_rpow · r) hC fun v ↦ ?_
  -- `∫ ⟪v, a⟫` is the conjugate of `∫ ⟪a, v⟫`.
  rw [← integral_inner_conj_symm, RCLike.norm_conj]
  exact h v

/-- **`H^{-r}` is the dual of `H^r` for the `L²` pairing.** For `C ≥ 0`, a Schwartz function `a`
has `‖a‖_{H^{-r}} ≤ C` exactly when `‖∫ ⟪a, v⟫‖ ≤ C ‖v‖_{H^r}` for every Schwartz function `v`. -/
theorem norm_toBesselPotentialSpaceCLM_neg_le_iff (r : ℝ) (a : 𝓢(E, F)) {C : ℝ} (hC : 0 ≤ C) :
    ‖toBesselPotentialSpaceCLM (-r) 2 a‖ ≤ C ↔
      ∀ v : 𝓢(E, F), ‖∫ x, ⟪a x, v x⟫_ℂ‖ ≤ C * ‖toBesselPotentialSpaceCLM r 2 v‖ :=
  ⟨fun h v ↦ (norm_integral_inner_le_norm_toBesselPotentialSpaceCLM_mul_norm r a v).trans
    (mul_le_mul_of_nonneg_right h (norm_nonneg _)),
    norm_toBesselPotentialSpaceCLM_neg_le_of_forall r a hC⟩

/-- Bessel potentials of real order are symmetric for the `L²` inner product of Schwartz
functions: `⟪J^a X, Y⟫_{L²} = ⟪X, J^a Y⟫_{L²}`. -/
theorem inner_toLp_besselPotentialCLM_left (a : ℝ) (X Y : 𝓢(E, F)) :
    ⟪(besselPotentialCLM (a : ℂ) X).toLp 2, Y.toLp 2⟫_ℂ =
      ⟪X.toLp 2, (besselPotentialCLM (a : ℂ) Y).toLp 2⟫_ℂ := by
  -- Both sides are `∫ ⟪J^a X, Y⟫`, read in the `H^0`–`H^0` and the `H^{-a}`–`H^a` pairings.
  have h0 := inner_toLp_toBesselPotentialSpaceCLM_neg 0 (besselPotentialCLM (a : ℂ) X) Y
  have ha := inner_toLp_toBesselPotentialSpaceCLM_neg a (besselPotentialCLM (a : ℂ) X) Y
  simp only [toLp_toBesselPotentialSpaceCLM_eq_besselPotentialCLM,
    besselPotentialCLM_besselPotentialCLM_apply, Complex.ofReal_neg, neg_zero, Complex.ofReal_zero,
    add_neg_cancel, besselPotentialCLM_zero, ContinuousLinearMap.id_apply] at h0 ha
  rw [h0, ha]

end L2Pairing

end SchwartzMap

namespace BesselPotentialSpace

section Inclusion

open SchwartzMap
open scoped InnerProductSpace

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

/-- For `Y ∈ H^r` and `m ≤ r`, the `H^m` inner product of `Y` with a Schwartz function `φ` is the
`H^r` inner product of `Y` with `J^{2 (m - r)} φ`. -/
theorem inner_inclusion_toBesselPotentialSpaceCLM {m r : ℝ} (h : m ≤ r) (Y : H^{r}(E, F))
    (φ : 𝓢(E, F)) :
    ⟪inclusion h Y, toBesselPotentialSpaceCLM m 2 φ⟫_ℂ =
      ⟪Y, toBesselPotentialSpaceCLM r 2 (besselPotentialCLM ((2 * (m - r) : ℝ) : ℂ) φ)⟫_ℂ := by
  refine (denseRange_toBesselPotentialSpaceCLM (p := 2) r ENNReal.ofNat_ne_top).induction_on Y
    (isClosed_eq (by fun_prop) (by fun_prop)) fun ψ ↦ ?_
  -- Write `J^m ψ = J^{m - r} (J^r ψ)` and move `J^{m - r}` to the other side.
  have hψ : besselPotentialCLM (m : ℂ) ψ =
      besselPotentialCLM ((m - r : ℝ) : ℂ) (besselPotentialCLM (r : ℂ) ψ) := by
    simp
  rw [inclusion_toBesselPotentialSpaceCLM, ← inner_toLp_toLp, ← inner_toLp_toLp]
  simp only [toLp_toBesselPotentialSpaceCLM_eq_besselPotentialCLM]
  rw [hψ, inner_toLp_besselPotentialCLM_left, besselPotentialCLM_besselPotentialCLM_apply,
    besselPotentialCLM_besselPotentialCLM_apply,
    show (m : ℂ) + ((m - r : ℝ) : ℂ) = ((2 * (m - r) : ℝ) : ℂ) + r by push_cast; ring]

/-- For `x ∈ H^s` and `m ≤ s`, the `H^m` inner product of a Schwartz function `φ` with `x` is
bounded by `‖φ‖_{H^{2m - s}} ‖x‖_{H^s}`. -/
theorem norm_inner_inclusion_le {m s : ℝ} (h : m ≤ s) (φ : 𝓢(E, F)) (x : H^{s}(E, F)) :
    ‖⟪toBesselPotentialSpaceCLM m 2 φ, inclusion h x⟫_ℂ‖ ≤
      ‖toBesselPotentialSpaceCLM (2 * m - s) 2 φ‖ * ‖x‖ := by
  rw [norm_inner_symm, inner_inclusion_toBesselPotentialSpaceCLM]
  refine (norm_inner_le_norm _ _).trans_eq ?_
  rw [norm_toBesselPotentialSpaceCLM_besselPotentialCLM, Complex.ofReal_re,
    show s + 2 * (m - s) = 2 * m - s by ring, mul_comm]

/-- **A duality criterion for `H^r`.** Let `m ≤ r` and `M ≥ 0`. If the `H^m` inner products of
`y ∈ H^m` with Schwartz functions `φ` are bounded by `M ‖φ‖_{H^{2m - r}}`, then `y` lies in `H^r`,
with norm at most `M`. -/
theorem exists_inclusion_eq_and_norm_le {m r M : ℝ} (hmr : m ≤ r) (hM : 0 ≤ M)
    (y : H^{m}(E, F))
    (hy : ∀ φ : 𝓢(E, F), ‖⟪toBesselPotentialSpaceCLM m 2 φ, y⟫_ℂ‖ ≤
      M * ‖toBesselPotentialSpaceCLM (2 * m - r) 2 φ‖) :
    ∃ Y : H^{r}(E, F), inclusion hmr Y = y ∧ ‖Y‖ ≤ M := by
  -- The functional `χ ↦ ⟪y, J^{2 (r - m)} χ⟫_{H^m}` is bounded in the `H^r` norm.
  let L : 𝓢(E, F) →ₗ[ℂ] ℂ :=
    { toFun χ := ⟪y, toBesselPotentialSpaceCLM m 2
        (besselPotentialCLM ((2 * (r - m) : ℝ) : ℂ) χ)⟫_ℂ
      map_add' χ χ' := by simp [inner_add_right]
      map_smul' a χ := by simp [inner_smul_right] }
  have hL (χ : 𝓢(E, F)) : ‖L χ‖ ≤ M * ‖toBesselPotentialSpaceCLM r 2 χ‖ := by
    -- `L χ` is by definition the inner product `⟪y, J^{2 (r - m)} χ⟫_{H^m}`.
    change ‖⟪y, _⟫_ℂ‖ ≤ _
    rw [norm_inner_symm]
    refine (hy _).trans_eq ?_
    rw [norm_toBesselPotentialSpaceCLM_besselPotentialCLM, Complex.ofReal_re,
      show 2 * m - r + 2 * (r - m) = r by ring]
  have hdense := denseRange_toBesselPotentialSpaceCLM (E := E) (F := F) (p := 2) r
    ENNReal.ofNat_ne_top
  set Λ := L.extendOfNorm (toBesselPotentialSpaceCLM r 2).toLinearMap
  have hΛ (χ : 𝓢(E, F)) : Λ (toBesselPotentialSpaceCLM r 2 χ) = L χ :=
    LinearMap.extendOfNorm_eq hdense ⟨M, hL⟩ χ
  -- By the Riesz representation theorem in `H^r`, `Λ` is the inner product with some `Y`.
  set Y := (InnerProductSpace.toDual ℂ H^{r}(E, F)).symm Λ
  refine ⟨Y, ?_, ?_⟩
  · have hd (w : H^{m}(E, F)) : ⟪inclusion hmr Y - y, w⟫_ℂ = 0 := by
      refine (denseRange_toBesselPotentialSpaceCLM (p := 2) m ENNReal.ofNat_ne_top).induction_on
        w (isClosed_eq (by fun_prop) continuous_const) fun φ ↦ ?_
      rw [inner_sub_left, inner_inclusion_toBesselPotentialSpaceCLM,
        InnerProductSpace.toDual_symm_apply, hΛ]
      -- Unfold `L`; the two Bessel potentials then cancel.
      change ⟪y, toBesselPotentialSpaceCLM m 2 (besselPotentialCLM ((2 * (r - m) : ℝ) : ℂ)
        (besselPotentialCLM ((2 * (m - r) : ℝ) : ℂ) φ))⟫_ℂ - _ = 0
      rw [besselPotentialCLM_besselPotentialCLM_apply, ← Complex.ofReal_add,
        show 2 * (m - r) + 2 * (r - m) = 0 by ring, Complex.ofReal_zero, besselPotentialCLM_zero,
        ContinuousLinearMap.id_apply, sub_self]
    exact sub_eq_zero.1 (inner_self_eq_zero.1 (hd _))
  · rw [LinearIsometryEquiv.norm_map]
    exact LinearMap.opNorm_extendOfNorm_le hdense hM hL

end Inclusion

end BesselPotentialSpace
