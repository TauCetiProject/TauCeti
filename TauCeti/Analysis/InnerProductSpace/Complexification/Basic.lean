/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT-5.6 Thinking

## Provenance

* Original repository: Davis--Kahan/DKPS formalization (Kitware, Inc.).
* Original module: `DavisKahan/SpectralTheory/Complexification/Basic.lean`.
* Extraction class: **moved**, not restated.  It depends only on Mathlib and `ForTauCeti`;
  the enclosing namespace
  `TauCeti.DavisKahan.Experimental.Foundation.RealComplexification` became
  `TauCeti.RealComplexification`, dropping a paper's name and a staging word.
* **The namespace is now split across the two libraries**, deliberately and visibly:
  `Complexification/Subspace.lean` and its `complexifySubmodule` are still in `DavisKahan`
  under the old path, so a consumer of both opens both.  That is recorded at each such
  `open` rather than hidden, and it resolves when the rest of the cluster moves.
* Original authors / copyright: Jon Crall, GPT-5.6 Thinking; Copyright (c) 2026
  Kitware, Inc.; Apache 2.0.
* Spectra influence: **none**.
-/
module

public import Mathlib.Algebra.Module.MinimalAxioms
public import Mathlib.Analysis.InnerProductSpace.ProdL2
public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Analysis.Normed.Operator.Banach

/-!
# Complexification of real Hilbert spaces

This file supplies the concrete complexification foundation needed to reuse the
complex operator-angle and spectral calculus for real Hilbert spaces.

For a real Hilbert space `E`, its complexification is the L2 product `E × E`.
The pair `(x, y)` represents `x + i y`, with complex scalar multiplication

`(a + i b) • (x + i y) = (a x - b y) + i (b x + a y)`.

The complex inner product is

`⟪(x,y),(u,v)⟫ = (⟪x,u⟫ + ⟪y,v⟫) + i (⟪x,v⟫ - ⟪y,u⟫)`.

The construction includes:

* the canonical isometric real-linear embedding `ofReal`;
* complex conjugation as a real-linear isometric involution;
* complexification of bounded real-linear operators;
* preservation of zero, identity, addition, subtraction, scalar multiplication,
  and composition;
* exact preservation of operator norm;
* reflection of equality and transport of symmetry.

No unbounded-operator, spectral-cutoff, or Ky Fan file depends on this module.
-/

public section

namespace TauCeti

open scoped InnerProductSpace ComplexConjugate

noncomputable section

/-- The complexification of a real normed space, represented by its real and
imaginary coordinates with the L2 product norm. -/
@[expose]
def RealComplexification (E : Type*) := WithLp 2 (E × E)

namespace RealComplexification

variable {E F G : Type*}

/-- Additive structure, inherited from the underlying `WithLp 2 (E × E)`. -/
instance instAddCommGroup [AddCommGroup E] :
    AddCommGroup (RealComplexification E) :=
  inferInstanceAs (AddCommGroup (WithLp 2 (E × E)))

/-- The `L²` product norm, inherited from `WithLp 2 (E × E)`.  This is the choice that makes the
complexification an inner-product space rather than merely a normed one. -/
instance instNormedAddCommGroup [NormedAddCommGroup E] :
    NormedAddCommGroup (RealComplexification E) :=
  inferInstanceAs (NormedAddCommGroup (WithLp 2 (E × E)))

/-- Completeness is inherited from `E`. -/
instance instCompleteSpace [NormedAddCommGroup E] [CompleteSpace E] :
    CompleteSpace (RealComplexification E) :=
  inferInstanceAs (CompleteSpace (WithLp 2 (E × E)))

/-- Real scalar action, coordinatewise. -/
instance instSMulReal [SMul ℝ E] : SMul ℝ (RealComplexification E) :=
  inferInstanceAs (SMul ℝ (WithLp 2 (E × E)))

/-- Real module structure, inherited from the product. -/
instance instModuleReal [AddCommGroup E] [Module ℝ E] :
    Module ℝ (RealComplexification E) :=
  inferInstanceAs (Module ℝ (WithLp 2 (E × E)))

/-- The `L²` norm is compatible with real scaling. -/
instance instNormedSpaceReal [NormedAddCommGroup E] [NormedSpace ℝ E] :
    NormedSpace ℝ (RealComplexification E) :=
  inferInstanceAs (NormedSpace ℝ (WithLp 2 (E × E)))

/-- Construct a complexified vector from its real and imaginary coordinates. -/
@[expose]
def mk (x y : E) : RealComplexification E :=
  WithLp.toLp 2 (x, y)

/-- The real coordinate of a complexified vector. -/
@[expose]
def re (z : RealComplexification E) : E :=
  (WithLp.ofLp z).1

/-- The imaginary coordinate of a complexified vector. -/
@[expose]
def im (z : RealComplexification E) : E :=
  (WithLp.ofLp z).2

/-- The real part of a vector built from coordinates. -/
@[simp] theorem re_mk (x y : E) : re (mk x y) = x := rfl
/-- The imaginary part of a vector built from coordinates. -/
@[simp] theorem im_mk (x y : E) : im (mk x y) = y := rfl
/-- Rebuilding a vector from its own coordinates is the identity. -/
@[simp] theorem mk_re_im (z : RealComplexification E) : mk (re z) (im z) = z := by
  exact WithLp.toLp_ofLp 2 z

/-- Two complexified vectors are equal when their real and imaginary coordinates agree.  Tagged
`@[ext]`, so `ext` splits any goal about them into two real goals. -/
@[ext]
theorem ext {z w : RealComplexification E} (hre : re z = re w) (him : im z = im w) : z = w := by
  apply WithLp.ofLp_injective
  exact Prod.ext hre him

/-- Zero has zero real part. -/
@[simp] theorem re_zero [AddCommGroup E] : re (0 : RealComplexification E) = 0 := rfl
/-- Zero has zero imaginary part. -/
@[simp] theorem im_zero [AddCommGroup E] : im (0 : RealComplexification E) = 0 := rfl
/-- Addition is coordinatewise on real parts. -/
@[simp] theorem re_add [AddCommGroup E] (z w : RealComplexification E) :
    re (z + w) = re z + re w := rfl
/-- Addition is coordinatewise on imaginary parts. -/
@[simp] theorem im_add [AddCommGroup E] (z w : RealComplexification E) :
    im (z + w) = im z + im w := rfl
/-- Negation on real parts. -/
@[simp] theorem re_neg [AddCommGroup E] (z : RealComplexification E) :
    re (-z) = -re z := rfl
/-- Negation on imaginary parts. -/
@[simp] theorem im_neg [AddCommGroup E] (z : RealComplexification E) :
    im (-z) = -im z := rfl
/-- Subtraction on real parts. -/
@[simp] theorem re_sub [AddCommGroup E] (z w : RealComplexification E) :
    re (z - w) = re z - re w := rfl
/-- Subtraction on imaginary parts. -/
@[simp] theorem im_sub [AddCommGroup E] (z w : RealComplexification E) :
    im (z - w) = im z - im w := rfl
/-- Real scaling acts on the real part. -/
@[simp] theorem re_real_smul [AddCommGroup E] [Module ℝ E]
    (r : ℝ) (z : RealComplexification E) : re (r • z) = r • re z := rfl
/-- Real scaling acts on the imaginary part. -/
@[simp] theorem im_real_smul [AddCommGroup E] [Module ℝ E]
    (r : ℝ) (z : RealComplexification E) : im (r • z) = r • im z := rfl

/-- Complex scalar multiplication on the real L2 product. -/
instance instSMulComplex [AddCommGroup E] [Module ℝ E] :
    SMul ℂ (RealComplexification E) where
  smul c z := mk (c.re • re z - c.im • im z) (c.im • re z + c.re • im z)

/-- Real part of a complex scaling: `re (c • z) = c.re • re z - c.im • im z`, the real half of
complex multiplication. -/
@[simp] theorem re_complex_smul [AddCommGroup E] [Module ℝ E]
    (c : ℂ) (z : RealComplexification E) :
    re (c • z) = c.re • re z - c.im • im z := rfl

/-- Imaginary part of a complex scaling: `im (c • z) = c.im • re z + c.re • im z`. -/
@[simp] theorem im_complex_smul [AddCommGroup E] [Module ℝ E]
    (c : ℂ) (z : RealComplexification E) :
    im (c • z) = c.im • re z + c.re • im z := rfl

/-- **The complex module structure**, where the complexification earns its name: `i` acts by
`(x, y) ↦ (-y, x)`.  Built from minimal axioms because the four laws are exactly the four real
identities that have to be checked coordinatewise. -/
instance instModuleComplex [AddCommGroup E] [Module ℝ E] :
    Module ℂ (RealComplexification E) :=
  Module.ofMinimalAxioms
    (fun c z w => by
      apply RealComplexification.ext <;>
        simp [smul_add, sub_eq_add_neg] <;> abel)
    (fun c d z => by apply RealComplexification.ext <;> simp [add_smul, sub_eq_add_neg] <;> module)
    (fun c d z => by
      apply RealComplexification.ext <;>
        simp [sub_eq_add_neg, Complex.mul_re, Complex.mul_im] <;> module)
    (fun z => by apply RealComplexification.ext <;> simp)

/-- Real and complex scalar actions are compatible, so `ℝ`-linear statements can be read inside
`ℂ`-linear ones without transport. -/
instance instIsScalarTower [AddCommGroup E] [Module ℝ E] :
    IsScalarTower ℝ ℂ (RealComplexification E) where
  smul_assoc r c z := by
    apply RealComplexification.ext
    · simp only [re_complex_smul, re_real_smul, Complex.smul_re, Complex.smul_im,
        smul_sub, smul_smul, smul_eq_mul]
    · simp only [im_complex_smul, im_real_smul, Complex.smul_re, Complex.smul_im,
        smul_add, smul_smul, smul_eq_mul]

/-- The squared L2 norm is the sum of the squared coordinate norms. -/
theorem norm_sq [NormedAddCommGroup E] (z : RealComplexification E) :
    ‖z‖ ^ 2 = ‖re z‖ ^ 2 + ‖im z‖ ^ 2 := by
  exact WithLp.prod_norm_sq_eq_of_L2 z

/-- Complex scalar multiplication scales the L2 norm exactly. -/
theorem norm_complex_smul [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (c : ℂ) (z : RealComplexification E) :
    ‖c • z‖ = ‖c‖ * ‖z‖ := by
  rw [← sq_eq_sq₀ (norm_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _))]
  rw [norm_sq (c • z), mul_pow, norm_sq z]
  simp only [re_complex_smul, im_complex_smul]
  rw [norm_sub_sq (𝕜 := ℝ), norm_add_sq (𝕜 := ℝ)]
  simp only [norm_smul, Real.norm_eq_abs, real_inner_smul_left,
    real_inner_smul_right, Complex.sq_norm, Complex.normSq_apply]
  have hsq (a b : ℝ) : (|a| * b) ^ 2 = a ^ 2 * b ^ 2 := by
    rw [mul_pow, sq_abs]
  rw [hsq c.re ‖re z‖, hsq c.im ‖im z‖,
    hsq c.im ‖re z‖, hsq c.re ‖im z‖]
  ring_nf

/-- The `L²` norm is compatible with *complex* scaling.  This is the non-formal instance of the
group: it needs `‖c • z‖ = ‖c‖ ‖z‖` for complex `c`, which is the Pythagorean computation above and
not a consequence of the real case. -/
instance instNormedSpaceComplex [NormedAddCommGroup E] [InnerProductSpace ℝ E] :
    NormedSpace ℂ (RealComplexification E) :=
  { (instModuleComplex (E := E)) with
    norm_smul_le := fun c z => (norm_complex_smul c z).le }

/-- The canonical complex inner product on a real Hilbert-space complexification. -/
instance instInnerProductSpaceComplex [NormedAddCommGroup E] [InnerProductSpace ℝ E] :
    InnerProductSpace ℂ (RealComplexification E) where
  inner z w :=
    ⟨⟪re z, re w⟫_ℝ + ⟪im z, im w⟫_ℝ,
      ⟪re z, im w⟫_ℝ - ⟪im z, re w⟫_ℝ⟩
  norm_sq_eq_re_inner z := by
    rw [norm_sq]
    simp []
  conj_inner_symm z w := by
    apply Complex.ext <;> simp [real_inner_comm]
  add_left z w u := by
    apply Complex.ext <;> simp [inner_add_left] <;> ring_nf
  smul_left z w c := by
    apply Complex.ext <;>
      simp [inner_add_left, inner_sub_left, real_inner_smul_left,
        Complex.mul_re, Complex.mul_im] <;> ring

/-- The complex inner product in coordinates: real part `⟪re z, re w⟫ + ⟪im z, im w⟫`, imaginary
part `⟪re z, im w⟫ - ⟪im z, re w⟫`.  True by `rfl`, and the form every computation unfolds to. -/
@[simp]
theorem inner_apply [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (z w : RealComplexification E) :
    ⟪z, w⟫_ℂ =
      ⟨⟪re z, re w⟫_ℝ + ⟪im z, im w⟫_ℝ,
        ⟪re z, im w⟫_ℝ - ⟪im z, re w⟫_ℝ⟩ :=
  rfl

/-- The canonical embedding of a real Hilbert space into its complexification. -/
@[expose]
def ofReal [NormedAddCommGroup E] [InnerProductSpace ℝ E] :
    E →ₗᵢ[ℝ] RealComplexification E where
  toFun x := mk x 0
  map_add' x y := by apply RealComplexification.ext <;> simp
  map_smul' r x := by apply RealComplexification.ext <;> simp
  norm_map' x := by
    rw [← sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _), norm_sq]
    simp

/-- The real part of a real vector is itself. -/
@[simp] theorem re_ofReal [NormedAddCommGroup E] [InnerProductSpace ℝ E] (x : E) :
    re (ofReal x) = x := rfl
/-- A real vector has zero imaginary part. -/
@[simp] theorem im_ofReal [NormedAddCommGroup E] [InnerProductSpace ℝ E] (x : E) :
    im (ofReal x) = 0 := rfl
/-- The complex inner product of two real vectors is the real one, coerced -- so the embedding
`E → RealComplexification E` is isometric. -/
theorem inner_ofReal [NormedAddCommGroup E] [InnerProductSpace ℝ E] (x y : E) :
    ⟪ofReal x, ofReal y⟫_ℂ = (⟪x, y⟫_ℝ : ℂ) := by
  apply Complex.ext <;> simp

/-- Multiplication by `i` sends the real copy to the imaginary copy. -/
@[simp] theorem I_smul_ofReal [NormedAddCommGroup E] [InnerProductSpace ℝ E] (x : E) :
    Complex.I • ofReal x = mk 0 x := by
  apply RealComplexification.ext <;> simp

/-- Complex conjugation on the complexification. -/
@[expose]
def conjugation [NormedAddCommGroup E] [InnerProductSpace ℝ E] :
    RealComplexification E →ₗᵢ[ℝ] RealComplexification E where
  toFun z := mk (re z) (-im z)
  map_add' z w := by
    apply RealComplexification.ext <;> simp
    abel
  map_smul' r z := by apply RealComplexification.ext <;> simp
  norm_map' z := by
    rw [← sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _), norm_sq, norm_sq]
    simp

/-- Conjugation fixes the real part. -/
@[simp] theorem re_conj [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (z : RealComplexification E) : re (conjugation z) = re z := rfl
/-- Conjugation negates the imaginary part. -/
@[simp] theorem im_conj [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (z : RealComplexification E) : im (conjugation z) = -im z := rfl
/-- Conjugation is an involution. -/
@[simp] theorem conjugation_involutive [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (z : RealComplexification E) : conjugation (conjugation z) = z := by
  apply RealComplexification.ext <;> simp
/-- Conjugation fixes real vectors, which characterises the real subspace. -/
@[simp] theorem conjugation_ofReal [NormedAddCommGroup E] [InnerProductSpace ℝ E] (x : E) :
    conjugation (ofReal x) = ofReal x := by
  apply RealComplexification.ext <;> simp
/-- Conjugation is **conjugate**-linear, not linear: the scalar comes out starred. -/
@[simp] theorem conjugation_complex_smul [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (c : ℂ) (z : RealComplexification E) :
    conjugation (c • z) = conj c • conjugation z := by
  apply RealComplexification.ext <;> simp [Complex.conj_re, Complex.conj_im]
  module

/-- Coordinatewise extension of a bounded real-linear operator. -/
@[expose]
def complexify [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    (T : E →L[ℝ] F) : RealComplexification E →L[ℂ] RealComplexification F := by
  let L : RealComplexification E →ₗ[ℂ] RealComplexification F :=
    { toFun := fun z => mk (T (re z)) (T (im z))
      map_add' := fun z w => by apply RealComplexification.ext <;> simp
      map_smul' := fun c z => by apply RealComplexification.ext <;> simp }
  exact L.mkContinuous ‖T‖ (fun z => by
    rw [← sq_le_sq₀ (norm_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _))]
    rw [norm_sq, mul_pow, norm_sq]
    have hre : ‖T (re z)‖ ^ 2 ≤ ‖T‖ ^ 2 * ‖re z‖ ^ 2 := by
      rw [← mul_pow]
      exact (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _))).2
        (T.le_opNorm _)
    have him : ‖T (im z)‖ ^ 2 ≤ ‖T‖ ^ 2 * ‖im z‖ ^ 2 := by
      rw [← mul_pow]
      exact (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _))).2
        (T.le_opNorm _)
    change ‖T (re z)‖ ^ 2 + ‖T (im z)‖ ^ 2 ≤
      ‖T‖ ^ 2 * (‖re z‖ ^ 2 + ‖im z‖ ^ 2)
    nlinarith)

/-- The complexified operator acts on real parts by the original operator. -/
@[simp] theorem re_complexify [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    (T : E →L[ℝ] F) (z : RealComplexification E) :
    re (complexify T z) = T (re z) := rfl

/-- The complexified operator acts on imaginary parts by the original operator. -/
@[simp] theorem im_complexify [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    (T : E →L[ℝ] F) (z : RealComplexification E) :
    im (complexify T z) = T (im z) := rfl

/-- Complexification agrees with the original operator on real vectors. -/
@[simp] theorem complexify_ofReal [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    (T : E →L[ℝ] F) (x : E) :
    complexify T (ofReal x) = ofReal (T x) := by
  apply RealComplexification.ext <;> simp

/-- The complexification of the zero operator is zero. -/
@[simp] theorem complexify_zero [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] :
    complexify (0 : E →L[ℝ] F) = 0 := by
  apply ContinuousLinearMap.ext
  intro z
  apply RealComplexification.ext <;> simp

/-- The complexification of the identity is the identity. -/
@[simp] theorem complexify_id [NormedAddCommGroup E] [InnerProductSpace ℝ E] :
    complexify (ContinuousLinearMap.id ℝ E) = ContinuousLinearMap.id ℂ (RealComplexification E)
    := by
  apply ContinuousLinearMap.ext
  intro z
  apply RealComplexification.ext <;> simp

/-- Complexification is additive. -/
@[simp] theorem complexify_add [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    (S T : E →L[ℝ] F) : complexify (S + T) = complexify S + complexify T := by
  apply ContinuousLinearMap.ext
  intro z
  apply RealComplexification.ext <;> simp

/-- Complexification commutes with negation. -/
@[simp] theorem complexify_neg [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    (T : E →L[ℝ] F) : complexify (-T) = -complexify T := by
  apply ContinuousLinearMap.ext
  intro z
  apply RealComplexification.ext <;> simp

/-- Complexification commutes with subtraction. -/
@[simp] theorem complexify_sub [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    (S T : E →L[ℝ] F) : complexify (S - T) = complexify S - complexify T := by
  apply ContinuousLinearMap.ext
  intro z
  apply RealComplexification.ext <;> simp

/-- Complexification is **real**-homogeneous.  It is not complex-homogeneous -- the complexified
operator is `ℂ`-linear, but `complexify` itself only transports real scalars. -/
@[simp] theorem complexify_real_smul [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    (r : ℝ) (T : E →L[ℝ] F) :
    complexify (r • T) = (r : ℂ) • complexify T := by
  apply ContinuousLinearMap.ext
  intro z
  apply RealComplexification.ext
  · change r • T (re z) =
      (r : ℂ).re • T (re z) - (r : ℂ).im • T (im z)
    simp
  · change r • T (im z) =
      (r : ℂ).im • T (re z) + (r : ℂ).re • T (im z)
    simp

/-- Complexification is functorial: it commutes with composition. -/
@[simp] theorem complexify_comp [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    [NormedAddCommGroup G] [InnerProductSpace ℝ G]
    (S : F →L[ℝ] G) (T : E →L[ℝ] F) :
    complexify (S ∘L T) = complexify S ∘L complexify T := by
  apply ContinuousLinearMap.ext
  intro z
  apply RealComplexification.ext <;> simp

/-- Complexification preserves operator norm exactly. -/
theorem norm_complexify [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    (T : E →L[ℝ] F) : ‖complexify T‖ = ‖T‖ := by
  apply le_antisymm
  · exact ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun z => by
      rw [← sq_le_sq₀ (norm_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _))]
      rw [norm_sq, mul_pow, norm_sq]
      have hre : ‖T (re z)‖ ^ 2 ≤ ‖T‖ ^ 2 * ‖re z‖ ^ 2 := by
        rw [← mul_pow]
        exact (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _))).2
          (T.le_opNorm _)
      have him : ‖T (im z)‖ ^ 2 ≤ ‖T‖ ^ 2 * ‖im z‖ ^ 2 := by
        rw [← mul_pow]
        exact (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _))).2
          (T.le_opNorm _)
      change ‖T (re z)‖ ^ 2 + ‖T (im z)‖ ^ 2 ≤
        ‖T‖ ^ 2 * (‖re z‖ ^ 2 + ‖im z‖ ^ 2)
      nlinarith
  · refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun x => ?_
    simpa using (complexify T).le_opNorm (ofReal x)

/-- **Complexification is an isometry of operator spaces**, not merely norm-preserving on
each operator: it is additive, so `norm_complexify` upgrades to a statement about distances.
This is the form needed to transport a topological property *back* from the complexification,
where `norm_complexify` alone only transports one forward. -/
theorem isometry_complexify [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] :
    Isometry (complexify : (E →L[ℝ] F) → RealComplexification E →L[ℂ] RealComplexification F) :=
  AddMonoidHomClass.isometry_of_norm
    ({ toFun := complexify, map_zero' := complexify_zero,
        map_add' := complexify_add } : (E →L[ℝ] F) →+ _)
    norm_complexify

/-- Complexification reflects equality of bounded real operators. -/
theorem complexify_injective [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] :
    Function.Injective
      (complexify : (E →L[ℝ] F) → RealComplexification E →L[ℂ] RealComplexification F)
    := by
  intro S T h
  apply ContinuousLinearMap.ext
  intro x
  have hx : complexify S (ofReal x) = complexify T (ofReal x) := by rw [h]
  simpa using congrArg re hx

/-- A real scalar acts through its complex coercion. -/
theorem coe_real_smul [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (r : ℝ) (z : RealComplexification E) : (r : ℂ) • z = r • z := by
  apply RealComplexification.ext
  · simp only [re_complex_smul, Complex.ofReal_re, Complex.ofReal_im, zero_smul, sub_zero]
    rfl
  · simp only [im_complex_smul, Complex.ofReal_re, Complex.ofReal_im, zero_smul, zero_add]
    rfl

/-- **A coordinate of a vector is no longer than the vector.**  The single
statement of `‖re z‖ ≤ ‖z‖` in this repository, and the earliest in import
order, so every consumer can reach it.

It was `private` until 2026-07-30, guarded by a note saying a public copy would make
unqualified uses ambiguous in `Sources/DavisKahan1970/Ideals/HilbertSchmidtRealDescent.lean`,
which opens two of the namespaces that had a copy.  That was true, and it was the wrong
conclusion: the ambiguity came from the *other three* copies, not from this one being visible.

Getting there took a broken tree first, and the sequence is worth keeping.  `edward (aiq-gpu)`
deleted the `PartialMapComplexification` sibling in `4dacc008` and pointed that module here;
separately this one was still `private`.  Each fix is right alone and they are fatal together —
with the sibling gone and this one private, no public copy was reachable from
`PartialMap/Complexification.lean` and the build stopped.  Lane `{lane:CPLX-DEDUP-1}` then
deleted the remaining copies and made this one public, which is the state described above. -/
theorem norm_re_le [NormedAddCommGroup E] (z : RealComplexification E) :
    ‖re z‖ ≤ ‖z‖ := by
  have h := norm_sq z
  nlinarith [norm_nonneg (re z), norm_nonneg (im z), norm_nonneg z]

/-- **Restrict a complex operator to the real copy and take its real
coordinate.**  No invariance assumption is needed to define this: the map is
`x ↦ re (T (ofReal x))` for any bounded `T`, and it is bounded by `‖T‖` because
neither coordinate projection nor the real embedding changes a norm.

Stated **rectangularly**, between two different spaces.  Three copies of this
definition existed until 2026-07-30 and they were not three copies of one thing:
`Sources/DavisKahan1970/Ideals/HilbertSchmidtRealDescent.lean` had the
rectangular one while `Complexification/FunctionalCalculus.lean` and
`OperatorIdeal/ApproximationNumbers/Real/Threshold.lean` had the square case,
which is this at `F = E`.  This module is the only one all three consumers
import, so it is where the general form belongs. -/
@[expose]
noncomputable def realPartOperator [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    (T : RealComplexification E →L[ℂ] RealComplexification F) : E →L[ℝ] F := by
  let L : E →ₗ[ℝ] F :=
    { toFun := fun x => re (T (ofReal x))
      map_add' := fun x y => by simp
      map_smul' := fun r x => by simp }
  exact L.mkContinuous ‖T‖ fun x => by
    calc
      ‖re (T (ofReal x))‖ ≤ ‖T (ofReal x)‖ := norm_re_le _
      _ ≤ ‖T‖ * ‖ofReal x‖ := T.le_opNorm _
      _ = ‖T‖ * ‖x‖ := by rw [ofReal.norm_map]

/-- Pointwise formula for the real restriction: embed, apply, take the real
coordinate. -/
@[simp]
theorem realPartOperator_apply [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    (T : RealComplexification E →L[ℂ] RealComplexification F) (x : E) :
    realPartOperator T x = re (T (ofReal x)) := rfl

/-- Every vector is its real part plus `i` times its imaginary part. -/
theorem eq_ofReal_add_I_smul_ofReal [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (z : RealComplexification E) : z = ofReal (re z) + Complex.I • ofReal (im z) := by
  apply RealComplexification.ext <;> simp

/-- An operator commuting with conjugation maps the real copy **into** the real copy: the
imaginary part of `T (ofReal x)` vanishes.

This is the whole content of the conjugation condition, and it is what makes `realify` below
a two-sided inverse of `complexify`. -/
theorem im_apply_ofReal_eq_zero [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    {T : RealComplexification E →L[ℂ] RealComplexification F}
    (hT : ∀ z, T (conjugation z) = conjugation (T z)) (x : E) : im (T (ofReal x)) = 0 := by
  have h := hT (ofReal x)
  rw [conjugation_ofReal] at h
  have hneg : im (T (ofReal x)) = -im (T (ofReal x)) := by
    have := congrArg im h
    simpa using this
  have h2 : (2 : ℝ) • im (T (ofReal x)) = 0 := by
    rw [two_smul]
    exact add_eq_zero_iff_eq_neg.mpr hneg
  simpa using h2

/-- The real operator underlying a `ℂ`-linear operator: read off the action on the real copy.

Paired with `complexify_realify` this says `complexify` is a bijection onto the operators
commuting with `conjugation` — the surjectivity half that `complexify_injective` leaves open. -/
@[expose]
noncomputable def realify [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    (T : RealComplexification E →L[ℂ] RealComplexification F) : E →L[ℝ] F :=
  LinearMap.mkContinuous
    { toFun := fun x => re (T (ofReal x))
      map_add' := fun x y => by simp
      map_smul' := fun r x => by
        have : ofReal (r • x) = (r : ℂ) • ofReal (x : E) := by
          rw [coe_real_smul]; exact map_smul ofReal r x
        rw [this, map_smul, coe_real_smul]
        rfl }
    ‖T‖ fun x => by
      refine (norm_re_le _).trans ?_
      simpa using T.le_opNorm (ofReal x)

/-- `realify T` acts by reading the real part of `T` on the real copy. -/
@[simp] theorem realify_apply [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    (T : RealComplexification E →L[ℂ] RealComplexification F) (x : E) :
    realify T x = re (T (ofReal x)) := rfl

/-- **`complexify` is onto the conjugation-commuting operators.**  Together with
`complexify_injective`, complexification identifies `E →L[ℝ] F` with exactly those
`ℂ`-linear operators that commute with `conjugation`. -/
theorem complexify_realify [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    {T : RealComplexification E →L[ℂ] RealComplexification F}
    (hT : ∀ z, T (conjugation z) = conjugation (T z)) : complexify (realify T) = T := by
  have him := im_apply_ofReal_eq_zero hT
  apply ContinuousLinearMap.ext
  intro z
  have hz : T z = T (ofReal (re z)) + Complex.I • T (ofReal (im z)) := by
    conv_lhs => rw [eq_ofReal_add_I_smul_ofReal z]
    rw [map_add, map_smul]
  apply RealComplexification.ext
  · rw [re_complexify, realify_apply, hz]
    simp [him]
  · rw [im_complexify, realify_apply, hz]
    simp [him]

/-- The complexification of a real operator commutes with conjugation. -/
theorem complexify_conjugation [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    (T : E →L[ℝ] F) (z : RealComplexification E) :
    complexify T (conjugation z) = conjugation (complexify T z) := by
  apply RealComplexification.ext <;> simp

/-- Symmetry of a real operator is equivalent to symmetry of its complexification. -/
theorem complexify_isSymmetric_iff [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (T : E →L[ℝ] E) :
    ((complexify T : RealComplexification E →L[ℂ] RealComplexification E) :
      RealComplexification E →ₗ[ℂ] RealComplexification E).IsSymmetric ↔
      (T : E →ₗ[ℝ] E).IsSymmetric := by
  constructor
  · intro h x y
    have hxy := h (ofReal x) (ofReal y)
    simpa [inner_apply] using congrArg Complex.re hxy
  · intro h z w
    apply Complex.ext
    · simp [inner_apply, h]
    · simp [inner_apply, h]

/-- Self-adjointness is preserved and reflected by complexification. -/
theorem complexify_isSelfAdjoint_iff [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] (T : E →L[ℝ] E) :
    IsSelfAdjoint (complexify T) ↔ IsSelfAdjoint T := by
  rw [ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric,
    ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric,
    complexify_isSymmetric_iff]

end RealComplexification

end

end TauCeti
