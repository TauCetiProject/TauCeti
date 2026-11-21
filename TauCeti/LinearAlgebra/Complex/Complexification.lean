/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.LinearMap.FiniteRange
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.RingTheory.TensorProduct.Finite
public import TauCeti.LinearAlgebra.Complex.Conjugation
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Mathlib.Tactic.Module

/-!
# The complexification of a real vector space

For a real vector space `X`, the complexification `X_ℂ = X ⊕ i X` is the complex vector space of
formal sums `x + i y` with `x y : X`, where `(a + b i) • (x + i y) = (a x - b y) + i (b x + a y)`.
A real-linear map `T` extends to the complex-linear map `T_ℂ (x + i y) = T x + i T y`.

This file contains the purely algebraic part of the construction. The Taylor seminorm on `X_ℂ`
for a real seminormed space `X`, and the complexification of bounded operators, are in
`TauCeti.Analysis.Normed.Module.Complexification`.

## Main declarations

* `TauCeti.Complexification`: the complexification of a real vector space, with its complex
  module structure and conjugation `TauCeti.Complexification.conj`.
* `TauCeti.Complexification.ofReal`, `TauCeti.Complexification.re_add_I_smul_im`: the real
  embedding, and the decomposition `z = re z + i im z`; `TauCeti.Complexification.reLm`,
  `TauCeti.Complexification.imLm` and `TauCeti.Complexification.ofRealLm` are the real-linear
  real part, imaginary part and real embedding.
* `TauCeti.Complexification.ext_ofReal`: complex-(semi)linear maps out of `X_ℂ` are determined on
  `X`.
* `LinearMap.complexify`: the complex-linear extension `T_ℂ` of a real-linear map `T`, the unique
  one (`LinearMap.eq_complexify_iff`); it has finite rank exactly when `T` does
  (`LinearMap.hasFiniteRange_complexify_iff`).
* `TauCeti.tensorEquivComplexification`: the algebraic isomorphism `ℂ ⊗[ℝ] W ≃ₗ[ℂ] W_ℂ`.
* `TauCeti.Complexification.instFiniteComplex`, `TauCeti.Complexification.finrank_complex`: the
  complexification of a finite-dimensional real vector space is finite-dimensional over `ℂ`, of
  complex dimension the real dimension of the original space.
-/

@[expose] public section

noncomputable section

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

/-- Complex-semilinear maps out of the complexification agree once they agree on real vectors. -/
theorem ext_ofReal {S E : Type*} [Semiring S] {σ : ℂ →+* S} [AddCommMonoid E] [Module S E]
    {f g : Complexification X →ₛₗ[σ] E} (h : ∀ x, f (ofReal x) = g (ofReal x)) : f = g := by
  ext z
  rw [← re_add_I_smul_im z]
  simp only [map_add, map_smulₛₗ, h]

variable (X)

/-- The real part, as a real-linear map. -/
def reLm : Complexification X →ₗ[ℝ] X where
  toFun := re
  map_add' := add_re
  map_smul' := real_smul_re

/-- The imaginary part, as a real-linear map. -/
def imLm : Complexification X →ₗ[ℝ] X where
  toFun := im
  map_add' := add_im
  map_smul' := real_smul_im

/-- The real embedding, as a real-linear map. -/
def ofRealLm : X →ₗ[ℝ] Complexification X where
  toFun := ofReal
  map_add' _ _ := by ext <;> simp
  map_smul' _ _ := by ext <;> simp

variable {X}

@[simp] theorem reLm_apply (z : Complexification X) : reLm X z = z.re := (rfl)
@[simp] theorem imLm_apply (z : Complexification X) : imLm X z = z.im := (rfl)
@[simp] theorem ofRealLm_apply (x : X) : ofRealLm X x = ofReal x := (rfl)

end Module

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

end Complexification

end TauCeti

namespace LinearMap

open TauCeti TauCeti.Complexification

variable {X Y : Type*} [AddCommGroup X] [Module ℝ X] [AddCommGroup Y] [Module ℝ Y]

/-- The complexification `T_ℂ (x + i y) = T x + i T y` of a real-linear map, a complex-linear
map. -/
def complexify (T : X →ₗ[ℝ] Y) : Complexification X →ₗ[ℂ] Complexification Y where
  toFun z := ⟨T z.re, T z.im⟩
  map_add' _ _ := by ext <;> simp
  map_smul' _ _ := by ext <;> simp

@[simp]
theorem complexify_apply_re (T : X →ₗ[ℝ] Y) (z : Complexification X) :
    (T.complexify z).re = T z.re := (rfl)

@[simp]
theorem complexify_apply_im (T : X →ₗ[ℝ] Y) (z : Complexification X) :
    (T.complexify z).im = T z.im := (rfl)

@[simp]
theorem complexify_ofReal (T : X →ₗ[ℝ] Y) (x : X) :
    T.complexify (ofReal x) = ofReal (T x) := by
  ext <;> simp

/-- Complexification preserves and reflects finite rank. -/
@[simp]
theorem hasFiniteRange_complexify_iff (T : X →ₗ[ℝ] Y) :
    T.complexify.HasFiniteRange ↔ T.HasFiniteRange := by
  -- Since `ℂ` is finite over `ℝ`, it suffices to compare real ranges.
  rw [hasFiniteRange_iff_range, ← Submodule.FG.restrictScalars_iff (R := ℝ),
    ← range_restrictScalars, ← hasFiniteRange_iff_range]
  let J := (lsmul ℂ (Complexification Y) Complex.I).restrictScalars ℝ
  -- `T = re ∘ T_ℂ ∘ ofReal` and `T_ℂ = ofReal ∘ T ∘ re + I • ofReal ∘ T ∘ im` over `ℝ`.
  have hT : T = reLm Y ∘ₗ T.complexify.restrictScalars ℝ ∘ₗ ofRealLm X := by
    ext x
    simp
  have hreal : T.complexify.restrictScalars ℝ =
      ofRealLm Y ∘ₗ T ∘ₗ reLm X + J ∘ₗ ofRealLm Y ∘ₗ T ∘ₗ imLm X := by
    ext z <;> simp [J]
  refine ⟨fun h ↦ hT ▸ (h.comp_right _).comp_left _, fun h ↦ hreal ▸ ?_⟩
  exact ((h.comp_left (ofRealLm Y)).comp_right (reLm X)).add
    (((h.comp_left (ofRealLm Y)).comp_left J).comp_right (imLm X))

/-- The complexification is the unique complex-linear extension of `T`. -/
theorem eq_complexify_iff (T : X →ₗ[ℝ] Y) (S : Complexification X →ₗ[ℂ] Complexification Y) :
    S = T.complexify ↔ ∀ x, S (ofReal x) = ofReal (T x) :=
  ⟨fun h x ↦ h ▸ complexify_ofReal T x, fun h ↦ ext_ofReal fun x ↦ by simp [h]⟩

end LinearMap

namespace TauCeti

variable {W : Type*} [AddCommGroup W] [Module ℝ W]

variable (W) in
/-- The canonical `ℂ`-linear isomorphism `ℂ ⊗[ℝ] W ≃ₗ[ℂ] TauCeti.Complexification W` sending
`u` to `⟨realPart W u, imaginaryPart W u⟩` and `⟨x, y⟩` to `1 ⊗ₜ x + I ⊗ₜ y`. -/
def tensorEquivComplexification : ℂ ⊗[ℝ] W ≃ₗ[ℂ] Complexification W where
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

/-- The complexification of a finite-dimensional real vector space is finite-dimensional over
`ℂ`. -/
instance Complexification.instFiniteComplex [Module.Finite ℝ W] :
    Module.Finite ℂ (Complexification W) :=
  .equiv (tensorEquivComplexification W)

/-- The complexification of a real vector space has complex dimension its real dimension. -/
@[simp] theorem Complexification.finrank_complex :
    Module.finrank ℂ (Complexification W) = Module.finrank ℝ W :=
  (tensorEquivComplexification W).finrank_eq.symm.trans Module.finrank_baseChange

end TauCeti
