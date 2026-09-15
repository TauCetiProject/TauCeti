/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.Circle
public import Mathlib.Analysis.Normed.Operator.Basic
public import Mathlib.Analysis.Normed.Operator.LinearIsometry
public import Mathlib.Tactic.Module

/-!
# The complexification of a real normed space

For a real normed space `X`, the complexification `X_ℂ = X ⊕ i X` is the complex vector space of
formal sums `x + i y` with `x y : X`, where `(a + b i) • (x + i y) = (a x - b y) + i (b x + a y)`.
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

## Main declarations

* `TauCeti.Complexification`: the complexification of a real vector space, with its complex
  module structure.
* `TauCeti.Complexification.ofReal`, `TauCeti.Complexification.re_add_I_smul_im`: the real
  embedding, and the decomposition `z = re z + i im z`.
* `TauCeti.Complexification.norm_le_iff`: the characterization of the Taylor norm by bounds on the
  real parts of rotations.
* `TauCeti.Complexification.instNormedSpace`, `TauCeti.Complexification.instCompleteSpace`: the
  complex normed space structure, complete when `X` is.
* `TauCeti.Complexification.equivProd`: `X_ℂ` is real-linearly homeomorphic to `X × X`.
* `ContinuousLinearMap.complexify`: the complex-linear extension of a bounded real operator, with
  `ContinuousLinearMap.norm_complexify` and the bundled
  `ContinuousLinearMap.complexifyAlgHom`.
* `TauCeti.Complexification.ext_ofReal`: complex-linear maps out of `X_ℂ` are determined on `X`,
  so `T.complexify` is the unique complex-linear extension of `T`.

## References

* G. A. Muñoz, Y. Sarantopoulos, A. Tonge, *Complexifications of real Banach spaces,
  polynomials and multilinear maps*, Studia Math. 134 (1999), 1–33.
-/

public section

noncomputable section

open Set

namespace TauCeti

/-- The complexification `X ⊕ i X` of a real vector space `X`: an element with real part `re` and
imaginary part `im` stands for the formal sum `re + i im`. -/
@[ext]
structure Complexification (X : Type*) where
  /-- The real part of an element of the complexification. -/
  re : X
  /-- The imaginary part of an element of the complexification. -/
  im : X

namespace Complexification

section Module

variable {X : Type*} [AddCommGroup X]

instance : Zero (Complexification X) := ⟨⟨0, 0⟩⟩

instance : Add (Complexification X) := ⟨fun z w => ⟨z.re + w.re, z.im + w.im⟩⟩

instance : Neg (Complexification X) := ⟨fun z => ⟨-z.re, -z.im⟩⟩

instance : Sub (Complexification X) := ⟨fun z w => ⟨z.re - w.re, z.im - w.im⟩⟩

instance : SMul ℕ (Complexification X) := ⟨fun n z => ⟨n • z.re, n • z.im⟩⟩

instance : SMul ℤ (Complexification X) := ⟨fun n z => ⟨n • z.re, n • z.im⟩⟩

@[simp] theorem zero_re : (0 : Complexification X).re = 0 := (rfl)
@[simp] theorem zero_im : (0 : Complexification X).im = 0 := (rfl)
@[simp] theorem add_re (z w : Complexification X) : (z + w).re = z.re + w.re := (rfl)
@[simp] theorem add_im (z w : Complexification X) : (z + w).im = z.im + w.im := (rfl)
@[simp] theorem neg_re (z : Complexification X) : (-z).re = -z.re := (rfl)
@[simp] theorem neg_im (z : Complexification X) : (-z).im = -z.im := (rfl)
@[simp] theorem sub_re (z w : Complexification X) : (z - w).re = z.re - w.re := (rfl)
@[simp] theorem sub_im (z w : Complexification X) : (z - w).im = z.im - w.im := (rfl)

instance : AddCommGroup (Complexification X) :=
  Function.Injective.addCommGroup (fun z : Complexification X => (z.re, z.im))
    (fun _ _ h => by
      simp only [Prod.mk.injEq] at h
      exact Complexification.ext h.1 h.2)
    (rfl) (fun _ _ => (rfl)) (fun _ => (rfl)) (fun _ _ => (rfl)) (fun _ _ => (rfl))
    (fun _ _ => (rfl))

/-- The embedding `x ↦ x + i 0` of a real vector space into its complexification. -/
def ofReal (x : X) : Complexification X := ⟨x, 0⟩

@[simp] theorem ofReal_re (x : X) : (ofReal x).re = x := (rfl)
@[simp] theorem ofReal_im (x : X) : (ofReal x).im = 0 := (rfl)

variable [Module ℝ X]

/-- Complex scalars act by `(a + b i) • (x + i y) = (a x - b y) + i (b x + a y)`. -/
instance : SMul ℂ (Complexification X) :=
  ⟨fun c z => ⟨c.re • z.re - c.im • z.im, c.im • z.re + c.re • z.im⟩⟩

@[simp]
theorem smul_re (c : ℂ) (z : Complexification X) : (c • z).re = c.re • z.re - c.im • z.im :=
  (rfl)

@[simp]
theorem smul_im (c : ℂ) (z : Complexification X) : (c • z).im = c.im • z.re + c.re • z.im :=
  (rfl)

instance : Module ℂ (Complexification X) where
  one_smul z := by ext <;> simp
  mul_smul c d z := by ext <;> simp only [smul_re, smul_im, Complex.mul_re, Complex.mul_im] <;>
    module
  smul_zero c := by ext <;> simp
  smul_add c z w := by ext <;> simp only [smul_re, smul_im, add_re, add_im] <;> module
  add_smul c d z := by ext <;> simp only [smul_re, smul_im, add_re, add_im, Complex.add_re,
    Complex.add_im] <;> module
  zero_smul z := by ext <;> simp

/-- Real scalars act componentwise. -/
@[simp]
theorem real_smul_re (r : ℝ) (z : Complexification X) : (r • z).re = r • z.re := by
  rw [← Complex.coe_smul, smul_re, Complex.ofReal_re, Complex.ofReal_im, zero_smul, sub_zero]

/-- Real scalars act componentwise. -/
@[simp]
theorem real_smul_im (r : ℝ) (z : Complexification X) : (r • z).im = r • z.im := by
  rw [← Complex.coe_smul, smul_im, Complex.ofReal_re, Complex.ofReal_im, zero_smul, zero_add]

/-- Every element of the complexification is `re + i im`. -/
theorem re_add_I_smul_im (z : Complexification X) :
    ofReal z.re + Complex.I • ofReal z.im = z := by
  ext <;> simp

/-- Complex-linear maps out of the complexification agree once they agree on real vectors. -/
theorem ext_ofReal {E : Type*} [AddCommGroup E] [Module ℂ E]
    {f g : Complexification X →ₗ[ℂ] E} (h : ∀ x, f (ofReal x) = g (ofReal x)) : f = g := by
  ext z
  rw [← re_add_I_smul_im z, map_add, map_add, map_smul, map_smul, h, h]

end Module

section Norm

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

/-- The Taylor norm `‖z‖ = ⨆ w ∈ 𝕋, ‖Re (w • z)‖` on the complexification. -/
instance : Norm (Complexification X) := ⟨fun z => ⨆ w : Circle, ‖((w : ℂ) • z).re‖⟩

theorem norm_def (z : Complexification X) : ‖z‖ = ⨆ w : Circle, ‖((w : ℂ) • z).re‖ := (rfl)

/-- The real part of a scalar multiple is controlled by the two components. -/
private theorem norm_smul_re_le_aux (c : ℂ) (z : Complexification X) :
    ‖(c • z).re‖ ≤ ‖c‖ * (‖z.re‖ + ‖z.im‖) := by
  rw [smul_re, mul_add]
  refine (norm_sub_le _ _).trans (add_le_add ?_ ?_) <;> rw [norm_smul] <;>
    gcongr <;> simp [Complex.abs_re_le_norm, Complex.abs_im_le_norm]

private theorem bddAbove_range_norm_smul_re (z : Complexification X) :
    BddAbove (range fun w : Circle => ‖((w : ℂ) • z).re‖) :=
  ⟨‖z.re‖ + ‖z.im‖, by
    rintro _ ⟨w, rfl⟩
    simpa using norm_smul_re_le_aux (w : ℂ) z⟩

/-- The real part of every rotation is bounded by the norm. -/
theorem norm_circle_smul_re_le (w : Circle) (z : Complexification X) :
    ‖((w : ℂ) • z).re‖ ≤ ‖z‖ :=
  le_ciSup (bddAbove_range_norm_smul_re z) w

/-- The Taylor norm is the least bound on the real parts of all rotations. -/
theorem norm_le_iff {z : Complexification X} {r : ℝ} :
    ‖z‖ ≤ r ↔ ∀ w : Circle, ‖((w : ℂ) • z).re‖ ≤ r :=
  ciSup_le_iff (bddAbove_range_norm_smul_re z)

/-- The norm of the real part is at most the norm. -/
theorem norm_re_le (z : Complexification X) : ‖z.re‖ ≤ ‖z‖ := by
  simpa using norm_circle_smul_re_le 1 z

/-- The norm of the imaginary part is at most the norm. -/
theorem norm_im_le (z : Complexification X) : ‖z.im‖ ≤ ‖z‖ := by
  have h := norm_circle_smul_re_le ⟨-Complex.I, by simp [Submonoid.unitSphere]⟩ z
  simpa using h

/-- The norm is at most the sum of the norms of the two components. -/
theorem norm_le_norm_re_add_norm_im (z : Complexification X) : ‖z‖ ≤ ‖z.re‖ + ‖z.im‖ :=
  norm_le_iff.2 fun w => by simpa using norm_smul_re_le_aux (w : ℂ) z

/-- The real part of an arbitrary complex multiple is bounded by the product of the norms. -/
theorem norm_smul_re_le (c : ℂ) (z : Complexification X) : ‖(c • z).re‖ ≤ ‖c‖ * ‖z‖ := by
  rcases eq_or_ne c 0 with rfl | hc
  · simp
  have hnorm : (0 : ℝ) < ‖c‖ := norm_pos_iff.2 hc
  let u : Circle := ⟨c / (‖c‖ : ℂ), by
    simp [Submonoid.unitSphere, hnorm.ne']⟩
  have hu : ((‖c‖ : ℝ) : ℂ) * (u : ℂ) = c :=
    mul_div_cancel₀ c (Complex.ofReal_ne_zero.2 hnorm.ne')
  have hcu : c • z = ‖c‖ • ((u : ℂ) • z) := by
    rw [← Complex.coe_smul, smul_smul]
    exact congrArg (· • z) hu.symm
  rw [hcu, real_smul_re, norm_smul, Real.norm_of_nonneg hnorm.le]
  exact mul_le_mul_of_nonneg_left (norm_circle_smul_re_le u z) hnorm.le

private theorem norm_nonneg' (z : Complexification X) : 0 ≤ ‖z‖ :=
  (norm_nonneg z.re).trans (norm_re_le z)

@[simp]
theorem norm_ofReal (x : X) : ‖ofReal x‖ = ‖x‖ :=
  le_antisymm ((norm_le_norm_re_add_norm_im _).trans (by simp)) (by
    simpa using norm_re_le (ofReal x))

/-- The Taylor norm satisfies the axioms of a complex normed space. -/
theorem normedSpaceCore : NormedSpace.Core ℂ (Complexification X) where
  norm_nonneg := norm_nonneg'
  norm_smul c z := by
    have hle : ∀ (c : ℂ) (z : Complexification X), ‖c • z‖ ≤ ‖c‖ * ‖z‖ := fun c z =>
      norm_le_iff.2 fun w => by
        rw [smul_smul]
        simpa using norm_smul_re_le ((w : ℂ) * c) z
    refine le_antisymm (hle c z) ?_
    rcases eq_or_ne c 0 with rfl | hc
    · simpa using norm_nonneg' (0 : Complexification X)
    calc ‖c‖ * ‖z‖ = ‖c‖ * ‖c⁻¹ • c • z‖ := by rw [smul_smul, inv_mul_cancel₀ hc, one_smul]
      _ ≤ ‖c‖ * (‖c⁻¹‖ * ‖c • z‖) := by gcongr; exact hle _ _
      _ = ‖c • z‖ := by rw [norm_inv, ← mul_assoc, mul_inv_cancel₀ (norm_ne_zero_iff.2 hc),
          one_mul]
  norm_triangle z w := norm_le_iff.2 fun u => by
    rw [smul_add, add_re]
    exact (norm_add_le _ _).trans (add_le_add (norm_circle_smul_re_le u z)
      (norm_circle_smul_re_le u w))
  norm_eq_zero_iff z := by
    refine ⟨fun h => ?_, fun h => ?_⟩
    · ext
      · exact norm_le_zero_iff.1 (h ▸ norm_re_le z)
      · exact norm_le_zero_iff.1 (h ▸ norm_im_le z)
    · subst h
      exact le_antisymm (norm_le_iff.2 fun w => by simp)
        (by simpa using norm_circle_smul_re_le 1 (0 : Complexification X))

instance instNormedAddCommGroup : NormedAddCommGroup (Complexification X) :=
  NormedAddCommGroup.ofCore normedSpaceCore

/-- The complexification of a real normed space is a complex normed space under the Taylor
norm. -/
instance instNormedSpace : NormedSpace ℂ (Complexification X) :=
  NormedSpace.ofCore normedSpaceCore

variable (X)

/-- The real part, as a bounded real-linear map of norm at most one. -/
def reCLM : Complexification X →L[ℝ] X :=
  LinearMap.mkContinuous
    { toFun := re
      map_add' := add_re
      map_smul' := real_smul_re } 1 fun z => by simpa using norm_re_le z

/-- The imaginary part, as a bounded real-linear map of norm at most one. -/
def imCLM : Complexification X →L[ℝ] X :=
  LinearMap.mkContinuous
    { toFun := im
      map_add' := add_im
      map_smul' := real_smul_im } 1 fun z => by simpa using norm_im_le z

/-- The real embedding, as a real-linear isometry. -/
def ofRealLI : X →ₗᵢ[ℝ] Complexification X where
  toFun := ofReal
  map_add' _ _ := by ext <;> simp
  map_smul' _ _ := by ext <;> simp
  norm_map' := norm_ofReal

variable {X}

@[simp] theorem reCLM_apply (z : Complexification X) : reCLM X z = z.re := (rfl)
@[simp] theorem imCLM_apply (z : Complexification X) : imCLM X z = z.im := (rfl)
@[simp] theorem ofRealLI_apply (x : X) : ofRealLI X x = ofReal x := (rfl)

variable (X)

/-- The complexification is real-linearly homeomorphic to `X × X` via `z ↦ (re z, im z)`. -/
def equivProd : Complexification X ≃L[ℝ] X × X :=
  LinearEquiv.toContinuousLinearEquivOfBounds
    { toFun := fun z => (z.re, z.im)
      invFun := fun p => ⟨p.1, p.2⟩
      map_add' := fun _ _ => (rfl)
      map_smul' := fun r z => by ext <;> simp
      left_inv := fun _ => (rfl)
      right_inv := fun _ => (rfl) } 1 2
    (fun z => by simpa using ⟨norm_re_le z, norm_im_le z⟩)
    (fun p => by
      refine (norm_le_norm_re_add_norm_im (⟨p.1, p.2⟩ : Complexification X)).trans ?_
      have h1 : ‖p.1‖ ≤ ‖p‖ := norm_fst_le p
      have h2 : ‖p.2‖ ≤ ‖p‖ := norm_snd_le p
      dsimp only
      linarith)

variable {X}

@[simp]
theorem equivProd_apply (z : Complexification X) : equivProd X z = (z.re, z.im) := (rfl)

@[simp]
theorem equivProd_symm_apply (p : X × X) : (equivProd X).symm p = ⟨p.1, p.2⟩ := (rfl)

/-- The complexification of a real Banach space is a complex Banach space. -/
instance instCompleteSpace [CompleteSpace X] : CompleteSpace (Complexification X) :=
  (completeSpace_iff_isComplete_range (equivProd X).isUniformEmbedding.isUniformInducing).2
    ((equivProd X).surjective.range_eq ▸ isComplete_univ)

end Norm

end Complexification

end TauCeti

namespace ContinuousLinearMap

open TauCeti TauCeti.Complexification

variable {X Y Z : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [NormedAddCommGroup Y]
  [NormedSpace ℝ Y] [NormedAddCommGroup Z] [NormedSpace ℝ Z]

/-- The complexification `T_ℂ (x + i y) = T x + i T y` of a bounded real operator, a bounded
complex-linear operator. -/
def complexify (T : X →L[ℝ] Y) : Complexification X →L[ℂ] Complexification Y :=
  LinearMap.mkContinuous
    { toFun := fun z => ⟨T z.re, T z.im⟩
      map_add' := fun z w => by ext <;> simp
      map_smul' := fun c z => by ext <;> simp } ‖T‖ fun z =>
    norm_le_iff.2 fun w => by
      -- `T` commutes with rotations: the real part of `w • T_ℂ z` is `T (w • z).re`.
      have hre : ((w : ℂ) • (⟨T z.re, T z.im⟩ : Complexification Y)).re = T ((w : ℂ) • z).re := by
        simp
      simp only [LinearMap.coe_mk, AddHom.coe_mk, hre]
      exact (T.le_opNorm _).trans
        (mul_le_mul_of_nonneg_left (norm_circle_smul_re_le w z) (norm_nonneg T))

@[simp]
theorem complexify_apply_re (T : X →L[ℝ] Y) (z : Complexification X) :
    (T.complexify z).re = T z.re := (rfl)

@[simp]
theorem complexify_apply_im (T : X →L[ℝ] Y) (z : Complexification X) :
    (T.complexify z).im = T z.im := (rfl)

@[simp]
theorem complexify_ofReal (T : X →L[ℝ] Y) (x : X) :
    T.complexify (ofReal x) = ofReal (T x) := by
  ext <;> simp

/-- The complexification is the unique complex-linear extension of `T`. -/
theorem eq_complexify_iff (T : X →L[ℝ] Y) (S : Complexification X →L[ℂ] Complexification Y) :
    S = T.complexify ↔ ∀ x, S (ofReal x) = ofReal (T x) := by
  refine ⟨fun h x => h ▸ complexify_ofReal T x, fun h => ?_⟩
  refine ContinuousLinearMap.coe_injective (ext_ofReal fun x => ?_)
  simp [h]

/-- Complexification preserves the operator norm. -/
@[simp]
theorem norm_complexify (T : X →L[ℝ] Y) : ‖T.complexify‖ = ‖T‖ := by
  refine le_antisymm (LinearMap.mkContinuous_norm_le _ (norm_nonneg T) _) ?_
  refine T.opNorm_le_bound (norm_nonneg _) fun x => ?_
  simpa using T.complexify.le_opNorm (ofReal x)

/-- Complexification preserves identity maps. -/
@[simp]
theorem complexify_id : (ContinuousLinearMap.id ℝ X).complexify = ContinuousLinearMap.id ℂ _ := by
  ext <;> simp

/-- Complexification preserves composition of bounded operators. -/
@[simp]
theorem complexify_comp (T : Y →L[ℝ] Z) (S : X →L[ℝ] Y) :
    (T.comp S).complexify = T.complexify.comp S.complexify := by
  ext <;> simp

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

/-- Complexification preserves natural powers of bounded endomorphisms. -/
@[simp]
theorem complexify_pow (T : X →L[ℝ] X) (n : ℕ) : (T ^ n).complexify = T.complexify ^ n :=
  map_pow (complexifyAlgHom X) T n

end ContinuousLinearMap
