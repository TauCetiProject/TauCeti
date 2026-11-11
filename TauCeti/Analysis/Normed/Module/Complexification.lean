/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.LinearMap.FiniteRange
public import Mathlib.Analysis.Complex.Circle
public import Mathlib.Analysis.Normed.Operator.Basic
public import Mathlib.Analysis.Normed.Operator.LinearIsometry
public import Mathlib.Tactic.Module
public import TauCeti.LinearAlgebra.Complex.Conjugation

/-!
# The complexification of a real seminormed space

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

The construction, estimates, product equivalence, and extension of bounded operators also work
for real seminormed spaces, giving a Taylor seminorm. Definiteness is needed only to obtain the
`NormedAddCommGroup` instance from this seminormed structure.

## Main declarations

* `TauCeti.Complexification`: the complexification of a real vector space, with its complex
  module structure, conjugation `TauCeti.Complexification.conj`, and algebraic isomorphism
  `TauCeti.tensorEquivComplexification` with `ℂ ⊗[ℝ] W`.
* `TauCeti.Complexification.ofReal`, `TauCeti.Complexification.re_add_I_smul_im`: the real
  embedding, and the decomposition `z = re z + i im z`.
* `TauCeti.Complexification.norm_le_iff`: the characterization of the Taylor seminorm by bounds
  on the real parts of rotations.
* `TauCeti.Complexification.instNormedSpace`, `TauCeti.Complexification.instCompleteSpace`: the
  complex seminormed space structure, complete when `X` is, and continuous conjugation
  `TauCeti.Complexification.conjCLE`.
* `TauCeti.Complexification.equivProd`: `X_ℂ` is real-linearly homeomorphic to `X × X`.
* `TauCeti.Complexification.equivPi`: the complexification of `ι → ℝ` is complex-linearly
  homeomorphic to `ι → ℂ`.
* `ContinuousLinearMap.complexify` and `ContinuousLinearEquiv.complexify`: the complex-linear
  extension of bounded real operators and equivalences, with
  `ContinuousLinearMap.norm_complexify` and the continuous algebra homomorphism
  `ContinuousLinearMap.complexifyAlgHom` (`ContinuousLinearMap.continuous_complexifyAlgHom`).
* `TauCeti.Complexification.ext_ofReal`: complex-linear maps out of `X_ℂ` are determined on `X`,
  so `T.complexify` is the unique complex-linear extension of `T`.

## References

* G. A. Muñoz, Y. Sarantopoulos, A. Tonge, *Complexifications of real Banach spaces,
  polynomials and multilinear maps*, Studia Math. 134 (1999), 1–33.
-/

public section

noncomputable section

open Set
open scoped TensorProduct

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

variable {X : Type*}

instance [Zero X] : Zero (Complexification X) := ⟨⟨0, 0⟩⟩

instance [Add X] : Add (Complexification X) := ⟨fun z w ↦ ⟨z.re + w.re, z.im + w.im⟩⟩

instance [Neg X] : Neg (Complexification X) := ⟨fun z ↦ ⟨-z.re, -z.im⟩⟩

instance [Sub X] : Sub (Complexification X) := ⟨fun z w ↦ ⟨z.re - w.re, z.im - w.im⟩⟩

instance [SMul ℕ X] : SMul ℕ (Complexification X) := ⟨fun n z ↦ ⟨n • z.re, n • z.im⟩⟩

instance [SMul ℤ X] : SMul ℤ (Complexification X) := ⟨fun n z ↦ ⟨n • z.re, n • z.im⟩⟩

@[simp] theorem zero_re [Zero X] : (0 : Complexification X).re = 0 := (rfl)
@[simp] theorem zero_im [Zero X] : (0 : Complexification X).im = 0 := (rfl)
@[simp] theorem add_re [Add X] (z w : Complexification X) : (z + w).re = z.re + w.re := (rfl)
@[simp] theorem add_im [Add X] (z w : Complexification X) : (z + w).im = z.im + w.im := (rfl)
@[simp] theorem neg_re [Neg X] (z : Complexification X) : (-z).re = -z.re := (rfl)
@[simp] theorem neg_im [Neg X] (z : Complexification X) : (-z).im = -z.im := (rfl)
@[simp] theorem sub_re [Sub X] (z w : Complexification X) : (z - w).re = z.re - w.re := (rfl)
@[simp] theorem sub_im [Sub X] (z w : Complexification X) : (z - w).im = z.im - w.im := (rfl)

instance [AddCommGroup X] : AddCommGroup (Complexification X) :=
  Function.Injective.addCommGroup (fun z : Complexification X ↦ (z.re, z.im))
    (fun _ _ h ↦ by
      simp only [Prod.mk.injEq] at h
      exact Complexification.ext h.1 h.2)
    (rfl) (fun _ _ ↦ (rfl)) (fun _ ↦ (rfl)) (fun _ _ ↦ (rfl)) (fun _ _ ↦ (rfl))
    (fun _ _ ↦ (rfl))

/-- The embedding `x ↦ x + i 0` of a real vector space into its complexification. -/
def ofReal [Zero X] (x : X) : Complexification X := ⟨x, 0⟩

@[simp] theorem ofReal_re [Zero X] (x : X) : (ofReal x).re = x := (rfl)
@[simp] theorem ofReal_im [Zero X] (x : X) : (ofReal x).im = 0 := (rfl)

/-- The real embedding sends zero to zero. -/
@[simp] theorem ofReal_zero [Zero X] : ofReal (0 : X) = 0 := (rfl)

variable [AddCommGroup X] [Module ℝ X]

/-- Complex scalars act by `(a + b i) • (x + i y) = (a x - b y) + i (b x + a y)`. -/
instance : SMul ℂ (Complexification X) :=
  ⟨fun c z ↦ ⟨c.re • z.re - c.im • z.im, c.im • z.re + c.re • z.im⟩⟩

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
  simp [← Complex.coe_smul]

/-- Real scalars act componentwise. -/
@[simp]
theorem real_smul_im (r : ℝ) (z : Complexification X) : (r • z).im = r • z.im := by
  simp [← Complex.coe_smul]

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
  have h := norm_circle_smul_re_le ⟨-Complex.I, by simp [Submonoid.unitSphere]⟩ z
  simpa using h

/-- The Taylor seminorm is at most the sum of the seminorms of the two components. -/
theorem norm_le_norm_re_add_norm_im (z : Complexification X) : ‖z‖ ≤ ‖z.re‖ + ‖z.im‖ :=
  norm_le_iff.2 fun w ↦ by simpa using norm_smul_re_le_aux (w : ℂ) z

/-- The seminorm of the real part of a complex multiple is bounded by the scalar norm times
the Taylor seminorm. -/
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

/-- The Taylor seminorm satisfies the axioms of a complex seminormed space. -/
theorem seminormedSpaceCore : SeminormedSpace.Core ℂ (Complexification X) where
  norm_nonneg := norm_nonneg'
  norm_smul c z := by
    have hle : ∀ (c : ℂ) (z : Complexification X), ‖c • z‖ ≤ ‖c‖ * ‖z‖ := fun c z ↦
      norm_le_iff.2 fun w ↦ by
        rw [smul_smul]
        simpa using norm_smul_re_le ((w : ℂ) * c) z
    refine le_antisymm (hle c z) ?_
    rcases eq_or_ne c 0 with rfl | hc
    · simpa using norm_nonneg' (0 : Complexification X)
    calc ‖c‖ * ‖z‖ = ‖c‖ * ‖c⁻¹ • c • z‖ := by rw [smul_smul, inv_mul_cancel₀ hc, one_smul]
      _ ≤ ‖c‖ * (‖c⁻¹‖ * ‖c • z‖) := by
        gcongr
        exact hle _ _
      _ = ‖c • z‖ := by rw [norm_inv, ← mul_assoc, mul_inv_cancel₀ (norm_ne_zero_iff.2 hc),
          one_mul]
  norm_triangle z w := norm_le_iff.2 fun u ↦ by
    rw [smul_add, add_re]
    exact (norm_add_le _ _).trans (add_le_add (norm_circle_smul_re_le u z)
      (norm_circle_smul_re_le u w))
instance instSeminormedAddCommGroup : SeminormedAddCommGroup (Complexification X) :=
  SeminormedAddCommGroup.ofCore seminormedSpaceCore

/-- The complexification carries the complex seminormed space structure from its Taylor seminorm. -/
instance instNormedSpace : NormedSpace ℂ (Complexification X) where
  norm_smul_le c z := (seminormedSpaceCore.norm_smul c z).le

variable (X)

/-- The real part, as a bounded real-linear map of norm at most one. -/
def reCLM : Complexification X →L[ℝ] X :=
  LinearMap.mkContinuous
    { toFun := re
      map_add' := add_re
      map_smul' := real_smul_re } 1 fun z ↦ by simpa using norm_re_le z

/-- The imaginary part, as a bounded real-linear map of norm at most one. -/
def imCLM : Complexification X →L[ℝ] X :=
  LinearMap.mkContinuous
    { toFun := im
      map_add' := add_im
      map_smul' := real_smul_im } 1 fun z ↦ by simpa using norm_im_le z

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

/-- Taking real parts undoes the real embedding. -/
@[simp]
theorem reCLM_comp_ofRealLI :
    reCLM X ∘L (ofRealLI X).toContinuousLinearMap = ContinuousLinearMap.id ℝ X := by
  ext x
  simp

/-- The complexification is real-linearly homeomorphic to `X × X` via `z ↦ (re z, im z)`. -/
def equivProd : Complexification X ≃L[ℝ] X × X :=
  LinearEquiv.toContinuousLinearEquivOfBounds
    { toFun := fun z ↦ (z.re, z.im)
      invFun := fun p ↦ ⟨p.1, p.2⟩
      map_add' := fun _ _ ↦ (rfl)
      map_smul' := fun r z ↦ by ext <;> simp
      left_inv := fun _ ↦ (rfl)
      right_inv := fun _ ↦ (rfl) } 1 2
    (fun z ↦ by simpa using ⟨norm_re_le z, norm_im_le z⟩)
    (fun p ↦ by
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
    have hre : Continuous fun z : Complexification (ι → ℝ) ↦ z.re := (reCLM _).continuous
    have him : Continuous fun z : Complexification (ι → ℝ) ↦ z.im := (imCLM _).continuous
    refine continuous_pi fun i ↦ ?_
    refine (Complex.equivRealProdCLM.symm.continuous.comp
      (((continuous_apply i).comp hre).prodMk ((continuous_apply i).comp him))).congr fun z ↦ ?_
    apply Complex.ext <;> simp
  continuous_invFun := by
    have h : Continuous fun v : ι → ℂ ↦ (equivProd (ι → ℝ)).symm
        (fun i ↦ (v i).re, fun i ↦ (v i).im) :=
      (equivProd (ι → ℝ)).symm.continuous.comp
        ((continuous_pi fun i ↦ Complex.continuous_re.comp (continuous_apply i)).prodMk
          (continuous_pi fun i ↦ Complex.continuous_im.comp (continuous_apply i)))
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
  LinearMap.mkContinuous
    { toFun := fun z ↦ ⟨T z.re, T z.im⟩
      map_add' := fun z w ↦ by ext <;> simp
      map_smul' := fun c z ↦ by ext <;> simp } ‖T‖ fun z ↦
    norm_le_iff.2 fun w ↦ by
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

/-- Complexification preserves finite rank. -/
theorem hasFiniteRange_complexify (T : X →L[ℝ] Y) (hT : T.toLinearMap.HasFiniteRange) :
    T.complexify.toLinearMap.HasFiniteRange := by
  let i := (ofRealLI Y).toLinearMap
  let J := (LinearMap.lsmul ℂ (Complexification Y) Complex.I).restrictScalars ℝ
  have hreal : T.complexify.toLinearMap.restrictScalars ℝ =
      (i.comp T.toLinearMap).comp (reCLM X).toLinearMap +
        (J.comp (i.comp T.toLinearMap)).comp (imCLM X).toLinearMap := by
    ext z <;> simp [i, J]
  apply Submodule.FG.of_restrictScalars ℝ
  rw [← LinearMap.range_restrictScalars, hreal]
  exact ((hT.comp_left i).comp_right (reCLM X).toLinearMap).add
    (((hT.comp_left i).comp_left J).comp_right (imCLM X).toLinearMap)

/-- The complexification is the unique complex-linear extension of `T`. -/
theorem eq_complexify_iff (T : X →L[ℝ] Y) (S : Complexification X →L[ℂ] Complexification Y) :
    S = T.complexify ↔ ∀ x, S (ofReal x) = ofReal (T x) := by
  refine ⟨fun h x ↦ h ▸ complexify_ofReal T x, fun h ↦ ?_⟩
  refine ContinuousLinearMap.coe_injective (ext_ofReal fun x ↦ ?_)
  simp [h]

/-- Complexification preserves the operator norm. -/
@[simp]
theorem norm_complexify (T : X →L[ℝ] Y) : ‖T.complexify‖ = ‖T‖ := by
  refine le_antisymm (LinearMap.mkContinuous_norm_le _ (norm_nonneg T) _) ?_
  refine T.opNorm_le_bound (norm_nonneg _) fun x ↦ ?_
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

/-- Complexification of bounded endomorphisms is continuous, being an isometry. -/
theorem continuous_complexifyAlgHom : Continuous (complexifyAlgHom X) :=
  (complexifyₗᵢ X X).continuous

/-- Complexification preserves natural powers of bounded endomorphisms. -/
@[simp]
theorem complexify_pow (T : X →L[ℝ] X) (n : ℕ) : (T ^ n).complexify = T.complexify ^ n :=
  map_pow (complexifyAlgHom X) T n

end ContinuousLinearMap

namespace TauCeti.Complexification

/-- Complex conjugation `x + i y ↦ x - i y` on `TauCeti.Complexification W`, as a
`starRingEnd ℂ`-semilinear involution. -/
def conj (W : Type*) [AddCommGroup W] [Module ℝ W] :
    Complexification W →ₛₗ[starRingEnd ℂ] Complexification W where
  toFun z := ⟨z.re, -z.im⟩
  map_add' _ _ := by ext <;> simp; abel
  map_smul' _ _ := by
    ext <;> simp only [smul_re, smul_im, Complex.conj_re, Complex.conj_im] <;> module

section
variable {W : Type*} [AddCommGroup W] [Module ℝ W]
@[simp] theorem conj_re (z : Complexification W) : (conj W z).re = z.re := (rfl)
@[simp] theorem conj_im (z : Complexification W) : (conj W z).im = -z.im := (rfl)
@[simp] theorem conj_conj (z : Complexification W) : conj W (conj W z) = z := by ext <;> simp
@[simp] theorem conj_ofReal (w : W) : conj W (ofReal w) = ofReal w := by ext <;> simp
end

variable {X Y : Type*} [SeminormedAddCommGroup X] [NormedSpace ℝ X]
  [SeminormedAddCommGroup Y] [NormedSpace ℝ Y]

/-- Complex conjugation on `TauCeti.Complexification X` as a continuous conjugate-linear
equivalence. -/
def conjCLE (X : Type*) [SeminormedAddCommGroup X] [NormedSpace ℝ X] :
    Complexification X ≃L⋆[ℂ] Complexification X :=
  have hcont : Continuous (conj X) := ((equivProd X).symm.continuous.comp <|
    (reCLM X).continuous.prodMk (continuous_neg.comp (imCLM X).continuous)).congr
    fun _ ↦ by ext <;> simp
  { toLinearEquiv := LinearEquiv.ofInvolutive (conj X) conj_conj
    continuous_toFun := hcont, continuous_invFun := hcont }

@[simp] theorem coe_conjCLE : ⇑(conjCLE X) = conj X := (rfl)
@[simp] theorem conjCLE_symm : (conjCLE X).symm = conjCLE X := by ext <;> rfl

/-- Complexification of a bounded real operator commutes with complex conjugation. -/
theorem conj_complexify (T : X →L[ℝ] Y) (z : Complexification X) :
    conj Y (T.complexify z) = T.complexify (conj X z) := by ext <;> simp

end TauCeti.Complexification

namespace TauCeti

variable {W : Type*} [AddCommGroup W] [Module ℝ W]

/-- The canonical `ℂ`-linear isomorphism `ℂ ⊗[ℝ] W ≃ₗ[ℂ] TauCeti.Complexification W` sending
`u` to `⟨realPart W u, imaginaryPart W u⟩` and `⟨x, y⟩` to `1 ⊗ₜ x + I ⊗ₜ y`. -/
def tensorEquivComplexification (W : Type*) [AddCommGroup W] [Module ℝ W] :
    ℂ ⊗[ℝ] W ≃ₗ[ℂ] Complexification W where
  toFun u := ⟨realPart W u, imaginaryPart W u⟩
  map_add' _ _ := by ext <;> simp
  map_smul' _ _ := by ext <;> simp [realPart_smul, imaginaryPart_smul, add_comm]
  invFun z := 1 ⊗ₜ[ℝ] z.re + Complex.I ⊗ₜ[ℝ] z.im
  left_inv := one_tmul_realPart_add_I_tmul_imaginaryPart W
  right_inv _ := by ext <;> simp

@[simp] theorem tensorEquivComplexification_re (u : ℂ ⊗[ℝ] W) :
    (tensorEquivComplexification W u).re = realPart W u := (rfl)
@[simp] theorem tensorEquivComplexification_im (u : ℂ ⊗[ℝ] W) :
    (tensorEquivComplexification W u).im = imaginaryPart W u := (rfl)
@[simp] theorem tensorEquivComplexification_tmul (c : ℂ) (w : W) :
    tensorEquivComplexification W (c ⊗ₜ[ℝ] w) = c • Complexification.ofReal w := by ext <;> simp
@[simp] theorem tensorEquivComplexification_symm_apply (z : Complexification W) :
    (tensorEquivComplexification W).symm z = 1 ⊗ₜ[ℝ] z.re + Complex.I ⊗ₜ[ℝ] z.im := (rfl)

/-- `tensorEquivComplexification` intertwines `tmulConj` with `Complexification.conj`. -/
theorem tensorEquivComplexification_tmulConj (u : ℂ ⊗[ℝ] W) :
    tensorEquivComplexification W (tmulConj W u) =
      Complexification.conj W (tensorEquivComplexification W u) := by ext <;> simp

/-- `tensorEquivComplexification` intertwines `LinearMap.baseChange ℂ` with
`ContinuousLinearMap.complexify`. -/
theorem tensorEquivComplexification_baseChange {X Y : Type*}
    [SeminormedAddCommGroup X] [NormedSpace ℝ X] [SeminormedAddCommGroup Y] [NormedSpace ℝ Y]
    (T : X →L[ℝ] Y) (u : ℂ ⊗[ℝ] X) :
    tensorEquivComplexification Y (T.toLinearMap.baseChange ℂ u) =
      T.complexify (tensorEquivComplexification X u) := by ext <;> simp

end TauCeti

namespace ContinuousLinearEquiv

open TauCeti

variable {X Y Z : Type*} [SeminormedAddCommGroup X] [NormedSpace ℝ X]
  [SeminormedAddCommGroup Y] [NormedSpace ℝ Y] [SeminormedAddCommGroup Z] [NormedSpace ℝ Z]

/-- Complexification of a continuous `ℝ`-linear equivalence between real seminormed spaces, as a
continuous `ℂ`-linear equivalence between their Taylor-seminormed complexifications. -/
def complexify (e : X ≃L[ℝ] Y) : Complexification X ≃L[ℂ] Complexification Y :=
  equivOfInverse e.toContinuousLinearMap.complexify e.symm.toContinuousLinearMap.complexify
    (fun _ ↦ by ext <;> simp) (fun _ ↦ by ext <;> simp)

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
