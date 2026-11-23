/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.Circle
public import Mathlib.Analysis.Normed.Operator.Basic
public import Mathlib.Analysis.Normed.Operator.LinearIsometry
public import TauCeti.LinearAlgebra.Complex.Complexification
import Mathlib.Analysis.Normed.Module.Normalize

/-!
# The complexification of a real seminormed space

For a real normed space `X`, the complexification `X_ℂ = X ⊕ i X` is the complex vector space of
formal sums `x + i y` with `x y : X`, where `(a + b i) • (x + i y) = (a x - b y) + i (b x + a y)`
(its algebraic structure is in `TauCeti.LinearAlgebra.Complex.Complexification`).
It is the standard device for applying complex-analytic spectral theory to operators on a real
Banach space: a bounded real operator `T` extends to the complex-linear operator
`T_ℂ (x + i y) = T x + i T y`.

There are many equivalent complex norms on `X_ℂ`; this file uses the *Taylor norm*

`‖z‖ = ⨆ w ∈ 𝕋, ‖Re (w • z)‖`,

that is, `‖x + i y‖ = sup_θ ‖cos θ • x - sin θ • y‖`.  With this norm the passage from `X` to
`X_ℂ` loses no constants:

* the embedding `x ↦ x + i 0` is an isometry (`TauCeti.Complexification.norm_ofReal`);
* the real and imaginary parts are bounded by the norm, and the norm by their sum
  (`norm_re_le`, `norm_im_le`, `norm_le_norm_re_add_norm_im`), so `X_ℂ` carries the product
  topology and is complete whenever `X` is;
* the complexification of a bounded operator has the same operator norm
  (`ContinuousLinearMap.norm_complexify`).

Together with `ContinuousLinearMap.complexify_comp`, the last point means that an operator-norm
estimate for real operators, such as a growth bound `‖S t‖ ≤ M e^{ω t}` for a family of operators
or a bound `‖Rⁿ‖ ≤ C` on the powers of one operator, holds verbatim for their complexifications.
(On a real Hilbert space the Taylor norm is in general not the Hilbert norm `√(‖x‖² + ‖y‖²)`; the
two are equivalent.)

The construction, estimates, product equivalence, and extension of bounded operators also work
for real seminormed spaces, giving a Taylor seminorm. Definiteness is needed only to obtain the
`NormedAddCommGroup` instance from this seminormed structure.

## Main declarations

* `TauCeti.Complexification.norm_le_iff`: the characterization of the Taylor seminorm by bounds
  on the real parts of rotations.
* `TauCeti.Complexification.instNormedSpace`, `TauCeti.Complexification.instCompleteSpace`: the
  complex seminormed space structure, complete when `X` is, and continuous conjugation
  `TauCeti.Complexification.conjCLE`, also as the real-linear map
  `TauCeti.Complexification.conjCLM`.
* `TauCeti.Complexification.equivProd`: `X_ℂ` is real-linearly homeomorphic to `X × X`.
* `TauCeti.Complexification.equivPi`: the complexification of `ι → ℝ` is complex-linearly
  homeomorphic to `ι → ℂ`.
* `TauCeti.Complexification.continuousLinearMapEquiv`: complexification of real continuous Hom
  agrees with complex Hom between complexifications (the bounded counterpart of
  `TauCeti.Complexification.linearMapEquiv`, to which it reduces on underlying linear maps:
  `TauCeti.Complexification.coe_continuousLinearMapEquiv_apply`).
* `ContinuousLinearMap.complexify` and `ContinuousLinearEquiv.complexify`: the complex-linear
  extension of bounded real operators and equivalences, with
  `ContinuousLinearMap.norm_complexify` and the continuous algebra homomorphism
  `ContinuousLinearMap.complexifyAlgHom` (`ContinuousLinearMap.continuous_complexifyAlgHom`).
  The underlying linear map is `LinearMap.complexify` (`ContinuousLinearMap.coe_complexify`),
  so `T.complexify` is the unique complex-linear extension of `T`
  (`ContinuousLinearMap.eq_complexify_iff`) and has finite rank exactly when `T` does
  (`LinearMap.hasFiniteRange_complexify_iff`).

## References

* G. A. Muñoz, Y. Sarantopoulos, A. Tonge, *Complexifications of real Banach spaces,
  polynomials and multilinear maps*, Studia Math. 134 (1999), 1–33.
-/

public section

noncomputable section

open Set

namespace TauCeti

namespace Complexification

section Norm

variable {X : Type*} [SeminormedAddCommGroup X] [NormedSpace ℝ X]

/-- The Taylor seminorm `‖z‖ = ⨆ w ∈ 𝕋, ‖Re (w • z)‖` on the complexification. -/
instance : Norm (Complexification X) := ⟨fun z ↦ ⨆ w : Circle, ‖((w : ℂ) • z).re‖⟩

theorem norm_def (z : Complexification X) : ‖z‖ = ⨆ w : Circle, ‖((w : ℂ) • z).re‖ := (rfl)

/-- The real part of a scalar multiple is controlled by the two components. -/
private theorem norm_smul_re_le_aux (c : ℂ) (z : Complexification X) :
    ‖(c • z).re‖ ≤ ‖c‖ * (‖z.re‖ + ‖z.im‖) := by
  rw [smul_re, mul_add]
  refine (norm_sub_le _ _).trans (add_le_add ?_ ?_) <;> rw [norm_smul] <;>
    gcongr <;> simp [Complex.abs_re_le_norm, Complex.abs_im_le_norm]

private theorem bddAbove_range_norm_smul_re (z : Complexification X) :
    BddAbove (range fun w : Circle ↦ ‖((w : ℂ) • z).re‖) :=
  ⟨‖z.re‖ + ‖z.im‖, by
    rintro _ ⟨w, rfl⟩
    simpa using norm_smul_re_le_aux (w : ℂ) z⟩

/-- The seminorm of the real part of every rotation is bounded by the Taylor seminorm. -/
theorem norm_circle_smul_re_le (w : Circle) (z : Complexification X) :
    ‖((w : ℂ) • z).re‖ ≤ ‖z‖ :=
  le_ciSup (bddAbove_range_norm_smul_re z) w

/-- The Taylor seminorm is the least bound on the real parts of all rotations. -/
theorem norm_le_iff {z : Complexification X} {r : ℝ} :
    ‖z‖ ≤ r ↔ ∀ w : Circle, ‖((w : ℂ) • z).re‖ ≤ r :=
  ciSup_le_iff (bddAbove_range_norm_smul_re z)

/-- The seminorm of the real part is at most the Taylor seminorm. -/
theorem norm_re_le (z : Complexification X) : ‖z.re‖ ≤ ‖z‖ := by
  simpa using norm_circle_smul_re_le 1 z

/-- The seminorm of the imaginary part is at most the Taylor seminorm. -/
theorem norm_im_le (z : Complexification X) : ‖z.im‖ ≤ ‖z‖ := by
  simpa using norm_circle_smul_re_le ⟨-Complex.I, by simp [Submonoid.unitSphere]⟩ z

/-- The Taylor seminorm is at most the sum of the seminorms of the two components. -/
theorem norm_le_norm_re_add_norm_im (z : Complexification X) : ‖z‖ ≤ ‖z.re‖ + ‖z.im‖ :=
  norm_le_iff.2 fun w ↦ by simpa using norm_smul_re_le_aux (w : ℂ) z

/-- The seminorm of the real part of a complex multiple is bounded by the scalar norm times
the Taylor seminorm. -/
theorem norm_smul_re_le (c : ℂ) (z : Complexification X) : ‖(c • z).re‖ ≤ ‖c‖ * ‖z‖ := by
  rcases eq_or_ne c 0 with rfl | hc
  · simp
  -- Write `c = ‖c‖ • u` with `u = normalize c` on the unit circle.
  let u : Circle := ⟨NormedSpace.normalize c, by
    simpa [Submonoid.unitSphere] using NormedSpace.norm_normalize hc⟩
  have hu : (u : ℂ) = NormedSpace.normalize c := rfl
  have hcu : c • z = ‖c‖ • ((u : ℂ) • z) := by
    rw [hu, ← smul_assoc, NormedSpace.norm_smul_normalize]
  rw [hcu, real_smul_re, norm_smul, norm_norm]
  gcongr
  exact norm_circle_smul_re_le u z

private theorem norm_nonneg' (z : Complexification X) : 0 ≤ ‖z‖ :=
  (norm_nonneg z.re).trans (norm_re_le z)

@[simp]
theorem norm_ofReal (x : X) : ‖ofReal x‖ = ‖x‖ :=
  le_antisymm ((norm_le_norm_re_add_norm_im _).trans (by simp)) (by
    simpa using norm_re_le (ofReal x))

/-- The Taylor seminorm satisfies the axioms of a complex seminormed space. -/
private theorem seminormedSpaceCore : SeminormedSpace.Core ℂ (Complexification X) where
  norm_nonneg := norm_nonneg'
  norm_smul c z := by
    have hle : ∀ (c : ℂ) (z : Complexification X), ‖c • z‖ ≤ ‖c‖ * ‖z‖ := fun c z ↦
      norm_le_iff.2 fun w ↦ by
        rw [smul_smul]
        simpa using norm_smul_re_le ((w : ℂ) * c) z
    refine le_antisymm (hle c z) ?_
    rcases eq_or_ne c 0 with rfl | hc
    · simpa using norm_nonneg' (0 : Complexification X)
    calc ‖c‖ * ‖z‖ = ‖c‖ * ‖c⁻¹ • c • z‖ := by rw [inv_smul_smul₀ hc]
      _ ≤ ‖c‖ * (‖c⁻¹‖ * ‖c • z‖) := by gcongr; exact hle _ _
      _ = ‖c • z‖ := by rw [norm_inv, mul_inv_cancel_left₀ (norm_ne_zero_iff.2 hc)]
  norm_triangle z w := norm_le_iff.2 fun u ↦ by
    rw [smul_add, add_re]
    exact (norm_add_le _ _).trans (add_le_add (norm_circle_smul_re_le u z)
      (norm_circle_smul_re_le u w))

/-- The seminormed additive group structure of the Taylor seminorm. -/
instance instSeminormedAddCommGroup : SeminormedAddCommGroup (Complexification X) :=
  SeminormedAddCommGroup.ofCore (𝕜 := ℂ) (by exact seminormedSpaceCore)

/-- The complexification carries the complex seminormed space structure from its Taylor seminorm. -/
instance instNormedSpace : NormedSpace ℂ (Complexification X) where
  norm_smul_le c z := by exact (seminormedSpaceCore.norm_smul c z).le

variable (X)

/-- The real part, as a bounded real-linear map of norm at most one. -/
def reCLM : Complexification X →L[ℝ] X :=
  (reLm X).mkContinuous 1 fun z ↦ by simpa using norm_re_le z

/-- The imaginary part, as a bounded real-linear map of norm at most one. -/
def imCLM : Complexification X →L[ℝ] X :=
  (imLm X).mkContinuous 1 fun z ↦ by simpa using norm_im_le z

/-- The real embedding, as a real-linear isometry. -/
def ofRealLI : X →ₗᵢ[ℝ] Complexification X where
  __ := ofRealLm X
  norm_map' x := by rw [ofRealLm_apply, norm_ofReal]

/-- The underlying linear map of `reCLM` is `reLm`. -/
@[simp, norm_cast] theorem coe_reCLM : (reCLM X : Complexification X →ₗ[ℝ] X) = reLm X := (rfl)

/-- The underlying linear map of `imCLM` is `imLm`. -/
@[simp, norm_cast] theorem coe_imCLM : (imCLM X : Complexification X →ₗ[ℝ] X) = imLm X := (rfl)

/-- The underlying linear map of `ofRealLI` is `ofRealLm`. -/
@[simp] theorem toLinearMap_ofRealLI : (ofRealLI X).toLinearMap = ofRealLm X := (rfl)

variable {X}

@[simp] theorem reCLM_apply (z : Complexification X) : reCLM X z = z.re := by
  rw [← ContinuousLinearMap.coe_coe, coe_reCLM, reLm_apply]
@[simp] theorem imCLM_apply (z : Complexification X) : imCLM X z = z.im := by
  rw [← ContinuousLinearMap.coe_coe, coe_imCLM, imLm_apply]
@[simp] theorem ofRealLI_apply (x : X) : ofRealLI X x = ofReal x := by
  rw [← LinearIsometry.coe_toLinearMap, toLinearMap_ofRealLI, ofRealLm_apply]

variable (X)

/-- Taking real parts undoes the real embedding. -/
@[simp]
theorem reCLM_comp_ofRealLI :
    reCLM X ∘L (ofRealLI X).toContinuousLinearMap = ContinuousLinearMap.id ℝ X := by
  ext x
  simp

/-- The complexification is real-linearly homeomorphic to `X × X` via `z ↦ (re z, im z)`. -/
def equivProd : Complexification X ≃L[ℝ] X × X :=
  (equivProdLm X).toContinuousLinearEquivOfBounds 1 2
    (fun z ↦ by simpa using ⟨norm_re_le z, norm_im_le z⟩)
    (fun p ↦ (norm_le_norm_re_add_norm_im ((equivProdLm X).symm p)).trans <| by
      simpa [two_mul] using add_le_add (norm_fst_le p) (norm_snd_le p))

/-- The underlying linear equivalence of `equivProd` is `equivProdLm`. -/
@[simp] theorem toLinearEquiv_equivProd : (equivProd X).toLinearEquiv = equivProdLm X := (rfl)

variable {X}

@[simp]
theorem equivProd_apply (z : Complexification X) : equivProd X z = (z.re, z.im) := by
  rw [← ContinuousLinearEquiv.coe_toLinearEquiv, toLinearEquiv_equivProd, equivProdLm_apply]

@[simp]
theorem equivProd_symm_apply (p : X × X) : (equivProd X).symm p = ⟨p.1, p.2⟩ := by
  rw [← ContinuousLinearEquiv.coe_symm_toLinearEquiv, toLinearEquiv_equivProd,
    equivProdLm_symm_apply]

/-- The complexification is complete whenever the original real seminormed space is complete. -/
instance instCompleteSpace [CompleteSpace X] : CompleteSpace (Complexification X) :=
  ((equivProd X).isUniformEmbedding.isUniformInducing.completeSpace_congr
    (equivProd X).surjective).2 inferInstance

end Norm

/-- The Taylor seminorm is a norm when the original real seminorm is a norm. -/
instance instNormedAddCommGroup {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] :
    NormedAddCommGroup (Complexification X) where
  eq_of_dist_eq_zero {z w} h := by
    rw [dist_eq_norm] at h
    ext
    · exact sub_eq_zero.1 (norm_le_zero_iff.1 (h ▸ norm_re_le (z - w)))
    · exact sub_eq_zero.1 (norm_le_zero_iff.1 (h ▸ norm_im_le (z - w)))

variable (ι : Type*) [Fintype ι]

/-- The complexification of the real coordinate space `ι → ℝ` is complex-linearly homeomorphic to
`ι → ℂ`, by combining the real and imaginary parts coordinatewise. -/
def equivPi : Complexification (ι → ℝ) ≃L[ℂ] (ι → ℂ) where
  toFun z i := ⟨z.re i, z.im i⟩
  invFun v := ⟨fun i ↦ (v i).re, fun i ↦ (v i).im⟩
  map_add' _ _ := (rfl)
  map_smul' c z := by
    funext i
    rw [Pi.smul_apply, smul_eq_mul]
    apply Complex.ext
    · simp only [smul_re, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Complex.mul_re,
        RingHom.id_apply]
    · simp only [smul_im, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Complex.mul_im,
        RingHom.id_apply]
      ring
  left_inv _ := (rfl)
  right_inv _ := (rfl)
  continuous_toFun := by
    have hre : Continuous fun z : Complexification (ι → ℝ) ↦ z.re :=
      (reCLM _).continuous.congr reCLM_apply
    have him : Continuous fun z : Complexification (ι → ℝ) ↦ z.im :=
      (imCLM _).continuous.congr imCLM_apply
    -- Each coordinate is `Complex.equivRealProdCLM.symm (z.re i, z.im i)`.
    refine continuous_pi fun i ↦ (Complex.equivRealProdCLM.symm.continuous.comp
      (((continuous_apply i).comp hre).prodMk ((continuous_apply i).comp him))).congr fun z ↦ ?_
    apply Complex.ext <;> simp
  continuous_invFun := by
    have h : Continuous fun v : ι → ℂ ↦ (equivProd (ι → ℝ)).symm
        (fun i ↦ (v i).re, fun i ↦ (v i).im) := by fun_prop
    exact h.congr fun v ↦ equivProd_symm_apply _

variable {ι}

@[simp]
theorem equivPi_apply (z : Complexification (ι → ℝ)) (i : ι) :
    equivPi ι z i = ⟨z.re i, z.im i⟩ := (rfl)

@[simp]
theorem equivPi_symm_apply (v : ι → ℂ) :
    (equivPi ι).symm v = ⟨fun i ↦ (v i).re, fun i ↦ (v i).im⟩ := (rfl)

end Complexification

end TauCeti

namespace ContinuousLinearMap

open TauCeti TauCeti.Complexification

variable {X Y Z : Type*} [SeminormedAddCommGroup X] [NormedSpace ℝ X] [SeminormedAddCommGroup Y]
  [NormedSpace ℝ Y] [SeminormedAddCommGroup Z] [NormedSpace ℝ Z]

/-- The complexification `T_ℂ (x + i y) = T x + i T y` of a bounded real operator, a bounded
complex-linear operator. -/
def complexify (T : X →L[ℝ] Y) : Complexification X →L[ℂ] Complexification Y :=
  (T : X →ₗ[ℝ] Y).complexify.mkContinuous ‖T‖ fun z ↦
    norm_le_iff.2 fun w ↦ by
      -- `T` commutes with rotations: the real part of `w • T_ℂ z` is `T (w • z).re`.
      have hre : ((w : ℂ) • (T : X →ₗ[ℝ] Y).complexify z).re = T ((w : ℂ) • z).re := by
        simp
      rw [hre]
      exact (T.le_opNorm _).trans
        (mul_le_mul_of_nonneg_left (norm_circle_smul_re_le w z) (norm_nonneg T))

/-- The underlying linear map of `T.complexify` is the complexification of `T` as a linear map. -/
@[simp, norm_cast]
theorem coe_complexify (T : X →L[ℝ] Y) :
    (T.complexify : Complexification X →ₗ[ℂ] Complexification Y) =
      (T : X →ₗ[ℝ] Y).complexify := (rfl)

@[simp]
theorem complexify_apply_re (T : X →L[ℝ] Y) (z : Complexification X) :
    (T.complexify z).re = T z.re := by
  simpa only [← coe_complexify, coe_coe] using (T : X →ₗ[ℝ] Y).complexify_apply_re z

@[simp]
theorem complexify_apply_im (T : X →L[ℝ] Y) (z : Complexification X) :
    (T.complexify z).im = T z.im := by
  simpa only [← coe_complexify, coe_coe] using (T : X →ₗ[ℝ] Y).complexify_apply_im z

@[simp]
theorem complexify_ofReal (T : X →L[ℝ] Y) (x : X) :
    T.complexify (ofReal x) = ofReal (T x) := by
  simpa only [← coe_complexify, coe_coe] using (T : X →ₗ[ℝ] Y).complexify_ofReal x

/-- The complexification is the unique complex-linear extension of `T`. -/
theorem eq_complexify_iff (T : X →L[ℝ] Y) (S : Complexification X →L[ℂ] Complexification Y) :
    S = T.complexify ↔ ∀ x, S (ofReal x) = ofReal (T x) := by
  rw [← coe_inj, coe_complexify, LinearMap.eq_complexify_iff]
  simp only [coe_coe]

/-- Complexification preserves the operator norm. -/
@[simp]
theorem norm_complexify (T : X →L[ℝ] Y) : ‖T.complexify‖ = ‖T‖ := by
  refine le_antisymm (LinearMap.mkContinuous_norm_le _ (norm_nonneg T) _) ?_
  refine T.opNorm_le_bound (norm_nonneg _) fun x ↦ ?_
  simpa using T.complexify.le_opNorm (ofReal x)

/-- Complexification sends the zero operator to the zero operator. -/
@[simp]
theorem complexify_zero : (0 : X →L[ℝ] Y).complexify = 0 :=
  coe_injective <| by simp only [coe_complexify, toLinearMap_zero, LinearMap.complexify_zero]

/-- Complexification of bounded operators is additive. -/
@[simp]
theorem complexify_add (S T : X →L[ℝ] Y) : (S + T).complexify = S.complexify + T.complexify :=
  coe_injective <| by simp only [coe_complexify, toLinearMap_add, LinearMap.complexify_add]

/-- Complexification of bounded operators commutes with negation. -/
@[simp]
theorem complexify_neg (T : X →L[ℝ] Y) : (-T).complexify = -T.complexify :=
  coe_injective <| by simp only [coe_complexify, toLinearMap_neg, LinearMap.complexify_neg]

/-- Complexification of bounded operators commutes with subtraction. -/
@[simp]
theorem complexify_sub (S T : X →L[ℝ] Y) : (S - T).complexify = S.complexify - T.complexify :=
  coe_injective <| by simp only [coe_complexify, toLinearMap_sub, LinearMap.complexify_sub]

/-- Complexification of bounded operators commutes with real scalar multiplication. -/
@[simp]
theorem complexify_smul (r : ℝ) (T : X →L[ℝ] Y) : (r • T).complexify = r • T.complexify :=
  coe_injective <| by simp only [coe_complexify, toLinearMap_smul, LinearMap.complexify_smul]

/-- Complexification preserves identity maps. -/
@[simp]
theorem complexify_id : (ContinuousLinearMap.id ℝ X).complexify = ContinuousLinearMap.id ℂ _ :=
  coe_injective <| by simp only [coe_complexify, coe_id, LinearMap.complexify_id]

/-- Complexification preserves composition of bounded operators. -/
@[simp]
theorem complexify_comp (T : Y →L[ℝ] Z) (S : X →L[ℝ] Y) :
    (T.comp S).complexify = T.complexify.comp S.complexify :=
  coe_injective <| by simp only [coe_complexify, toLinearMap_comp, LinearMap.complexify_comp]

variable (X Y)

/-- Complexification of bounded operators, as a real-linear isometry. -/
def complexifyₗᵢ : (X →L[ℝ] Y) →ₗᵢ[ℝ] (Complexification X →L[ℂ] Complexification Y) where
  toFun := complexify
  map_add' _ _ := by ext <;> simp
  map_smul' _ _ := by ext <;> simp
  norm_map' := norm_complexify

/-- Complexification of bounded endomorphisms, as a homomorphism of real algebras. -/
def complexifyAlgHom : (X →L[ℝ] X) →ₐ[ℝ] (Complexification X →L[ℂ] Complexification X) where
  toFun := complexify
  map_one' := complexify_id
  map_mul' := complexify_comp
  map_zero' := (complexifyₗᵢ X X).map_zero
  map_add' := (complexifyₗᵢ X X).map_add
  commutes' r := by ext <;> simp [Algebra.algebraMap_eq_smul_one]

variable {X Y}

@[simp]
theorem complexifyₗᵢ_apply (T : X →L[ℝ] Y) : complexifyₗᵢ X Y T = T.complexify := (rfl)

@[simp]
theorem complexifyAlgHom_apply (T : X →L[ℝ] X) : complexifyAlgHom X T = T.complexify := (rfl)

/-- Complexification of bounded endomorphisms is continuous, being an isometry. -/
theorem continuous_complexifyAlgHom : Continuous (complexifyAlgHom X) :=
  (complexifyₗᵢ X X).continuous

/-- Complexification preserves natural powers of bounded endomorphisms. -/
@[simp]
theorem complexify_pow (T : X →L[ℝ] X) (n : ℕ) : (T ^ n).complexify = T.complexify ^ n :=
  map_pow (complexifyAlgHom X) T n

end ContinuousLinearMap

namespace TauCeti.Complexification

variable {X : Type*} [SeminormedAddCommGroup X] [NormedSpace ℝ X]

variable (X) in
/-- Complex conjugation on `TauCeti.Complexification X` as a continuous conjugate-linear
equivalence. -/
def conjCLE : Complexification X ≃L⋆[ℂ] Complexification X :=
  have hcont : Continuous (conj X) := ((equivProd X).symm.continuous.comp <|
    (reCLM X).continuous.prodMk (continuous_neg.comp (imCLM X).continuous)).congr
    fun _ ↦ by ext <;> simp
  { toLinearEquiv := LinearEquiv.ofInvolutive (conj X) conj_conj
    continuous_toFun := hcont, continuous_invFun := hcont }

@[simp] theorem coe_conjCLE : ⇑(conjCLE X) = conj X := (rfl)
@[simp] theorem conjCLE_symm : (conjCLE X).symm = conjCLE X := by ext <;> rfl

variable (X) in
/-- Complex conjugation on `TauCeti.Complexification X` as a continuous real-linear map. -/
def conjCLM : Complexification X →L[ℝ] Complexification X :=
  ⟨{ toFun := conj X
     map_add' := map_add (conj X)
     map_smul' := fun r z ↦ by ext <;> simp },
    (conjCLE X).continuous⟩

@[simp] theorem coe_conjCLM : ⇑(conjCLM X) = conj X := (rfl)

end TauCeti.Complexification

namespace ContinuousLinearEquiv

open TauCeti

variable {X Y Z : Type*} [SeminormedAddCommGroup X] [NormedSpace ℝ X]
  [SeminormedAddCommGroup Y] [NormedSpace ℝ Y] [SeminormedAddCommGroup Z] [NormedSpace ℝ Z]

/-- Complexification of a continuous `ℝ`-linear equivalence between real seminormed spaces, as a
continuous `ℂ`-linear equivalence between their Taylor-seminormed complexifications. -/
def complexify (e : X ≃L[ℝ] Y) : Complexification X ≃L[ℂ] Complexification Y :=
  ofContinuousLinearMap e.toContinuousLinearMap.complexify
    e.symm.toContinuousLinearMap.complexify
    (ContinuousLinearMap.ext fun _ ↦ by ext <;> simp)
    (ContinuousLinearMap.ext fun _ ↦ by ext <;> simp)

@[simp] theorem toContinuousLinearMap_complexify (e : X ≃L[ℝ] Y) :
    e.complexify.toContinuousLinearMap = e.toContinuousLinearMap.complexify := (rfl)
@[simp] theorem complexify_symm (e : X ≃L[ℝ] Y) : e.complexify.symm = e.symm.complexify := (rfl)
@[simp] theorem complexify_apply_re (e : X ≃L[ℝ] Y) (z : Complexification X) :
    (e.complexify z).re = e z.re := e.toContinuousLinearMap.complexify_apply_re z
@[simp] theorem complexify_apply_im (e : X ≃L[ℝ] Y) (z : Complexification X) :
    (e.complexify z).im = e z.im := e.toContinuousLinearMap.complexify_apply_im z
@[simp] theorem complexify_refl :
    (ContinuousLinearEquiv.refl ℝ X).complexify =
      ContinuousLinearEquiv.refl ℂ (Complexification X) := by ext <;> simp
@[simp] theorem complexify_trans (e : X ≃L[ℝ] Y) (e' : Y ≃L[ℝ] Z) :
    (e.trans e').complexify = e.complexify.trans e'.complexify := by ext <;> simp

end ContinuousLinearEquiv

namespace TauCeti.Complexification

variable {X Y : Type*} [SeminormedAddCommGroup X] [NormedSpace ℝ X]
  [SeminormedAddCommGroup Y] [NormedSpace ℝ Y]

private def homExtension (u : Complexification (X →L[ℝ] Y)) :
    Complexification X →L[ℂ] Complexification Y :=
  u.re.complexify + Complex.I • u.im.complexify

private def homRestriction (T : Complexification X →L[ℂ] Complexification Y) :
    Complexification (X →L[ℝ] Y) :=
  ⟨(reCLM Y).comp ((T.restrictScalars ℝ).comp (ofRealLI X).toContinuousLinearMap),
    (imCLM Y).comp ((T.restrictScalars ℝ).comp (ofRealLI X).toContinuousLinearMap)⟩

/-- Componentwise, the extension of bounded operators is the extension of their underlying
linear maps. -/
private theorem coe_homExtension (u : Complexification (X →L[ℝ] Y)) :
    (homExtension u : Complexification X →ₗ[ℂ] Complexification Y) =
      linearMapEquiv X Y ((ContinuousLinearMap.coeLM ℝ).complexify u) := by
  simp [homExtension, linearMapEquiv_apply]

/-- Componentwise, the restriction of a bounded operator is the restriction of its underlying
linear map. -/
private theorem complexify_coeLM_homRestriction
    (T : Complexification X →L[ℂ] Complexification Y) :
    (ContinuousLinearMap.coeLM ℝ).complexify (homRestriction T) = (linearMapEquiv X Y).symm T := by
  rw [linearMapEquiv_symm_apply]
  ext1 <;> simp [homRestriction]

private theorem homRestriction_re_apply (T : Complexification X →L[ℂ] Complexification Y)
    (x : X) : (homRestriction T).re x = (T (ofReal x)).re := by
  simpa using congrArg (fun u ↦ u.re x) (complexify_coeLM_homRestriction T)
private theorem homRestriction_im_apply (T : Complexification X →L[ℂ] Complexification Y)
    (x : X) : (homRestriction T).im x = (T (ofReal x)).im := by
  simpa using congrArg (fun u ↦ u.im x) (complexify_coeLM_homRestriction T)

private theorem homExtension_norm_le (u : Complexification (X →L[ℝ] Y)) :
    ‖homExtension u‖ ≤ 2 * ‖u‖ := by
  calc
    ‖homExtension u‖ ≤ ‖u.re.complexify‖ + ‖Complex.I • u.im.complexify‖ := norm_add_le _ _
    _ = ‖u.re‖ + ‖u.im‖ := by simp [norm_smul]
    _ ≤ 2 * ‖u‖ := by linarith [norm_re_le u, norm_im_le u]

private theorem homRestriction_norm_le (T : Complexification X →L[ℂ] Complexification Y) :
    ‖homRestriction T‖ ≤ 2 * ‖T‖ := by
  have hr : ‖(homRestriction T).re‖ ≤ ‖T‖ :=
    ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun x ↦ by
      rw [homRestriction_re_apply]
      exact (norm_re_le (T (ofReal x))).trans (by simpa using T.le_opNorm (ofReal x))
  have hi : ‖(homRestriction T).im‖ ≤ ‖T‖ :=
    ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun x ↦ by
      rw [homRestriction_im_apply]
      exact (norm_im_le (T (ofReal x))).trans (by simpa using T.le_opNorm (ofReal x))
  exact (norm_le_norm_re_add_norm_im _).trans (by linarith)

variable (X Y) in
/-- Complexification of real continuous Hom agrees with complex continuous Hom between
complexifications. Both model spaces have their existing Taylor norms. -/
def continuousLinearMapEquiv :
    Complexification (X →L[ℝ] Y) ≃L[ℂ] (Complexification X →L[ℂ] Complexification Y) :=
  LinearEquiv.toContinuousLinearEquivOfBounds
    { toFun := homExtension
      invFun := homRestriction
      map_add' := fun u v ↦ ContinuousLinearMap.coe_injective <| by
        simp only [ContinuousLinearMap.toLinearMap_add, coe_homExtension, map_add]
      map_smul' := fun c u ↦ ContinuousLinearMap.coe_injective <| by
        simp only [ContinuousLinearMap.toLinearMap_smul, coe_homExtension, map_smul,
          RingHom.id_apply]
      left_inv := fun u ↦ ((ContinuousLinearMap.coeLM ℝ).injective_complexify_iff.2
          ContinuousLinearMap.coe_injective) <| by
        rw [complexify_coeLM_homRestriction, coe_homExtension, LinearEquiv.symm_apply_apply]
      right_inv := fun T ↦ ContinuousLinearMap.coe_injective <| by
        rw [coe_homExtension, complexify_coeLM_homRestriction, LinearEquiv.apply_symm_apply] }
    2 2 homExtension_norm_le homRestriction_norm_le

/-- Forgetting continuity, `continuousLinearMapEquiv` is `linearMapEquiv` applied to the
underlying linear maps of the two components. -/
@[simp] theorem coe_continuousLinearMapEquiv_apply (u : Complexification (X →L[ℝ] Y)) :
    (continuousLinearMapEquiv X Y u : Complexification X →ₗ[ℂ] Complexification Y) =
      linearMapEquiv X Y ((ContinuousLinearMap.coeLM ℝ).complexify u) :=
  coe_homExtension u

/-- Forgetting continuity, the inverse of `continuousLinearMapEquiv` is the inverse of
`linearMapEquiv`, componentwise. -/
@[simp] theorem complexify_coeLM_continuousLinearMapEquiv_symm_apply
    (T : Complexification X →L[ℂ] Complexification Y) :
    (ContinuousLinearMap.coeLM ℝ).complexify ((continuousLinearMapEquiv X Y).symm T) =
      (linearMapEquiv X Y).symm T :=
  complexify_coeLM_homRestriction T

@[simp] theorem continuousLinearMapEquiv_apply_re (u : Complexification (X →L[ℝ] Y))
    (v : Complexification X) :
    (continuousLinearMapEquiv X Y u v).re = u.re v.re - u.im v.im := by
  simpa [-coe_continuousLinearMapEquiv_apply] using
    congrArg (fun T ↦ (T v).re) (coe_continuousLinearMapEquiv_apply u)
@[simp] theorem continuousLinearMapEquiv_apply_im (u : Complexification (X →L[ℝ] Y))
    (v : Complexification X) :
    (continuousLinearMapEquiv X Y u v).im = u.im v.re + u.re v.im := by
  simpa [-coe_continuousLinearMapEquiv_apply] using
    congrArg (fun T ↦ (T v).im) (coe_continuousLinearMapEquiv_apply u)

/-- Real operators extend by the existing complexification map. -/
@[simp] theorem continuousLinearMapEquiv_ofReal (T : X →L[ℝ] Y) :
    continuousLinearMapEquiv X Y (ofReal T) = T.complexify :=
  ContinuousLinearMap.coe_injective <| by simp

/-- Real coordinate of the inverse is restriction to included real vectors followed by Re. -/
@[simp] theorem continuousLinearMapEquiv_symm_apply_re
    (T : Complexification X →L[ℂ] Complexification Y) (x : X) :
    ((continuousLinearMapEquiv X Y).symm T).re x = (T (ofReal x)).re := by
  simpa [-complexify_coeLM_continuousLinearMapEquiv_symm_apply] using
    congrArg (fun u ↦ u.re x) (complexify_coeLM_continuousLinearMapEquiv_symm_apply T)

/-- Imaginary coordinate of the inverse is restriction to included real vectors followed by Im. -/
@[simp] theorem continuousLinearMapEquiv_symm_apply_im
    (T : Complexification X →L[ℂ] Complexification Y) (x : X) :
    ((continuousLinearMapEquiv X Y).symm T).im x = (T (ofReal x)).im := by
  simpa [-complexify_coeLM_continuousLinearMapEquiv_symm_apply] using
    congrArg (fun u ↦ u.im x) (complexify_coeLM_continuousLinearMapEquiv_symm_apply T)

/-- The model comparison increases norms by at most two. -/
theorem norm_continuousLinearMapEquiv_apply_le (u : Complexification (X →L[ℝ] Y)) :
    ‖continuousLinearMapEquiv X Y u‖ ≤ 2 * ‖u‖ := homExtension_norm_le u

/-- The inverse comparison increases norms by at most two. -/
theorem norm_continuousLinearMapEquiv_symm_apply_le
    (T : Complexification X →L[ℂ] Complexification Y) :
    ‖(continuousLinearMapEquiv X Y).symm T‖ ≤ 2 * ‖T‖ :=
  homRestriction_norm_le T

end TauCeti.Complexification
