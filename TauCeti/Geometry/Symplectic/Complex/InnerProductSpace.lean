/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.LinearMap
public import TauCeti.Geometry.Symplectic.Complex.Module.Basic

/-!
# The complex inner product of an orthogonal complex structure

An orthogonal almost complex structure `J` on a real inner product space gives a complex
inner product `⟨v,w⟩ = ⟪v,w⟫_ℝ + i ⟪J v,w⟫_ℝ` on `J.complexModule`.
The construction preserves the original norm and real scalar action. It is a named choice of
structure rather than a global instance, since it depends on `J`.

`TauCeti.AlmostComplexStructure.norm_apply` supplies norm preservation from preservation of the
real inner product, `TauCeti.AlmostComplexStructure.inner_apply_left_eq_neg_swap` the antisymmetry
`⟪J v, w⟫ = -⟪J w, v⟫`, and `TauCeti.AlmostComplexStructure.inner_apply_self` the orthogonality
`⟪J v, v⟫ = 0`. Hence `p` and `J p` are orthogonal of equal norm, and Cauchy–Schwarz for the
complex inner product bounds the components of any vector along them
(`TauCeti.AlmostComplexStructure.inner_sq_add_inner_sq_le`). Consequently, by
`TauCeti.AlmostComplexStructure.norm_re_smul_add_im_smul`, the parametrization
`z ↦ Re z • n + Im z • J n` of the complex line of a unit vector `n` is isometric.

Conversely, multiplication by `i` on a complex inner product space preserves the real inner product
`Re ⟪·, ·⟫_ℂ` (`TauCeti.AlmostComplexStructure.real_inner_ofComplexModule_ofComplexModule`).

Conversely, on a complex inner product space the imaginary part `Im ⟪·, ·⟫` of the inner product,
when it is given as a symplectic form, is compatible with multiplication by `i`
(`TauCeti.SymplecticForm.compatible_ofComplexModule_of_forall_eq_im_inner`): its associated metric
`Im ⟪v, i w⟫` is the real inner product `Re ⟪v, w⟫`.

This is the usual Hermitian metric associated with an orthogonal complex structure; see
H. B. Lawson and M.-L. Michelsohn, *Spin Geometry* (1989), Chapter I §5.
-/

public section

namespace TauCeti.AlmostComplexStructure

open scoped RealInnerProductSpace

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-- An orthogonal almost complex structure preserves norms. -/
@[simp]
theorem norm_apply {J : AlmostComplexStructure V} (hJ : ∀ v w, ⟪J v, J w⟫ = ⟪v, w⟫)
    (v : V) : ‖J v‖ = ‖v‖ :=
  (J.toLinearMap.isometryOfInner hJ).norm_map v

/-- For an orthogonal almost complex structure, `(v, w) ↦ ⟪J v, w⟫` is antisymmetric:
`⟪J v, w⟫ = -⟪J w, v⟫`. -/
theorem inner_apply_left_eq_neg_swap {J : AlmostComplexStructure V}
    (hJ : ∀ v w, ⟪J v, J w⟫ = ⟪v, w⟫) (v w : V) : ⟪J v, w⟫ = -⟪J w, v⟫ := by
  simpa only [innerₗ_apply_apply, real_inner_comm v (J w)] using
    J.bilinForm_apply_left_eq_neg_apply_right (g := innerₗ V) hJ v w

/-- An orthogonal almost complex structure turns every vector by a right angle, `⟪J v, v⟫ = 0`. -/
theorem inner_apply_self {J : AlmostComplexStructure V} (hJ : ∀ v w, ⟪J v, J w⟫ = ⟪v, w⟫)
    (v : V) : ⟪J v, v⟫ = 0 := by
  rw [real_inner_comm]
  exact J.bilinForm_apply_apply_self_eq_zero (g := innerₗ V) ⟨fun x y ↦ real_inner_comm y x⟩ hJ v

/-- **The complex line of a unit vector is isometric to `ℂ`.** For an orthogonal `J` and a unit
vector `n`, the vectors `n` and `J n` are orthonormal, so `‖Re z • n + Im z • J n‖ = ‖z‖`. -/
theorem norm_re_smul_add_im_smul (J : AlmostComplexStructure V)
    (hJ : ∀ v w, ⟪J v, J w⟫ = ⟪v, w⟫) {n : V} (hn : ‖n‖ = 1) (z : ℂ) :
    ‖z.re • n + z.im • J n‖ = ‖z‖ := by
  have hJn : ‖J n‖ = 1 := by rw [J.norm_apply hJ, hn]
  have horth : ⟪n, J n⟫ = 0 := by rw [real_inner_comm, J.inner_apply_self hJ]
  rw [← sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _), Complex.sq_norm, Complex.normSq_apply]
  simp [norm_add_sq_real, norm_smul, real_inner_smul_left, real_inner_smul_right, horth, hn, hJn,
    ← sq]

/-- The complex inner product induced by an orthogonal complex structure, using the original
norm on `V` and the scalar action `J.complexModule`. Its real part is the original inner product.
-/
@[implicit_reducible]
noncomputable def complexInnerProductSpace (J : AlmostComplexStructure V)
    (hJ : ∀ v, ‖J v‖ = ‖v‖) : InnerProductSpace ℂ V := by
  letI := J.complexModule
  let c : InnerProductSpace.Core ℂ V := by
    have hinner (v w : V) : ⟪J v, J w⟫ = ⟪v, w⟫ :=
      ({ J.toLinearMap with norm_map' := hJ } : V →ₗᵢ[ℝ] V).inner_map_map v w
    have hswap (v w : V) : ⟪J v, w⟫ = -⟪v, J w⟫ :=
      J.bilinForm_apply_left_eq_neg_apply_right (g := innerₗ V) hinner v w
    refine
      { inner := fun v w ↦ ⟨⟪v, w⟫, ⟪J v, w⟫⟩
        conj_inner_symm := ?_
        re_inner_nonneg := fun v ↦ real_inner_self_nonneg
        add_left := ?_
        smul_left := ?_
        definite := ?_ }
    · intro v w
      apply Complex.ext
      · exact real_inner_comm _ _
      · simp only [Complex.conj_im]
        rw [hswap, neg_neg, real_inner_comm]
    · intro v w x
      apply Complex.ext <;> simp [inner_add_left, map_add]
    · intro v w z
      rw [J.complexModule_smul_def]
      apply Complex.ext <;>
        simp [inner_add_left, inner_smul_left, map_add, map_smul, hswap]; ring
    · intro v hv
      exact inner_self_eq_zero.mp (congrArg Complex.re hv)
  have hnorm (v : V) : Real.sqrt ⟪v, v⟫ = ‖v‖ :=
    (norm_eq_sqrt_real_inner v).symm
  -- Use the core norm only to establish scalar compatibility; the resulting structure below
  -- keeps the original normed additive group, hence also its topology and real scalar action.
  have hsmul (z : ℂ) (v : V) :
      Real.sqrt ⟪z • v, z • v⟫ = ‖z‖ * Real.sqrt ⟪v, v⟫ := by
    let := c.toNormedAddCommGroup
    let : InnerProductSpace ℂ V := InnerProductSpace.ofCore c.toCore
    exact norm_smul z v
  letI : NormedSpace ℂ V :=
    { norm_smul_le := fun z v ↦ by simpa only [hnorm] using (hsmul z v).le }
  exact
    { inner := c.inner
      conj_inner_symm := c.conj_inner_symm
      add_left := c.add_left
      smul_left := c.smul_left
      norm_sq_eq_re_inner := fun v ↦ norm_sq_eq_re_inner (𝕜 := ℝ) v }

/-- The induced complex inner product uses exactly the complex scalar action determined by `J`.
This equation identifies the inherited module even when the construction is opaque downstream.
-/
@[simp]
lemma complexInnerProductSpace_toModule (J : AlmostComplexStructure V)
    (hJ : ∀ v, ‖J v‖ = ‖v‖) :
    (J.complexInnerProductSpace hJ).toNormedSpace.toModule = J.complexModule := by
  rfl

/-- The Hermitian structure extends the caller's original real scalar action. -/
lemma complexInnerProductSpace_isScalarTower (J : AlmostComplexStructure V)
    (hJ : ∀ v, ‖J v‖ = ‖v‖) :
    letI := J.complexInnerProductSpace hJ
    IsScalarTower ℝ ℂ V := by
  let := J.complexInnerProductSpace hJ
  exact J.complexModule_isScalarTower

/-- The scalar action inherited from the Hermitian structure is the action defined by `J`. -/
lemma complexInnerProductSpace_smul_def (J : AlmostComplexStructure V)
    (hJ : ∀ v, ‖J v‖ = ‖v‖) (z : ℂ) (v : V) :
    letI := J.complexInnerProductSpace hJ
    z • v = z.re • v + z.im • J v := by
  let := J.complexInnerProductSpace hJ
  exact J.complexModule_smul_def z v

/-- The Hermitian metric has real part the original metric and imaginary part `⟪J v,w⟫_ℝ`.
-/
@[simp]
lemma complexInnerProductSpace_inner (J : AlmostComplexStructure V)
    (hJ : ∀ v, ‖J v‖ = ‖v‖) (v w : V) :
    letI := J.complexInnerProductSpace hJ
    inner ℂ v w = (inner ℝ v w : ℂ) + Complex.I * (inner ℝ (J v) w : ℂ) := by
  let := J.complexInnerProductSpace hJ
  apply Complex.ext <;> simp <;> rfl

/-- Cauchy–Schwarz for the Hermitian metric of an orthogonal complex structure, in real terms: the
components of `d` along the orthogonal pair `p`, `J p` of equal norms satisfy
`⟪d, J p⟫² + ⟪d, p⟫² ≤ ‖d‖² ‖p‖²`. -/
theorem inner_sq_add_inner_sq_le {J : AlmostComplexStructure V}
    (hJ : ∀ v w, ⟪J v, J w⟫ = ⟪v, w⟫) (d p : V) :
    ⟪d, J p⟫ ^ 2 + ⟪d, p⟫ ^ 2 ≤ ‖d‖ ^ 2 * ‖p‖ ^ 2 := by
  let := J.complexInnerProductSpace (norm_apply hJ)
  have h := pow_le_pow_left₀ (norm_nonneg _) (norm_inner_le_norm (𝕜 := ℂ) p d) 2
  simp only [complexInnerProductSpace_inner, Complex.sq_norm, mul_comm Complex.I,
    Complex.normSq_add_mul_I, mul_pow] at h
  rw [real_inner_comm p d, real_inner_comm (J p) d]
  linarith

/-- Multiplication by `i` preserves the real inner product `Re ⟪·, ·⟫_ℂ` of a complex inner
product space, so `ofComplexModule E` is an orthogonal complex structure. -/
theorem real_inner_ofComplexModule_ofComplexModule {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] (v w : E) :
    letI := InnerProductSpace.complexToReal (G := E)
    ⟪ofComplexModule E v, ofComplexModule E w⟫ = ⟪v, w⟫ := by
  let := InnerProductSpace.complexToReal (G := E)
  simp [real_inner_eq_re_inner, inner_smul_left, inner_smul_right, ← mul_assoc]

end TauCeti.AlmostComplexStructure

namespace TauCeti.SymplecticForm

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]

/-- The imaginary part `Im ⟪·, ·⟫` of a complex inner product, as a symplectic form, is compatible
with multiplication by `i`: it is invariant under `i`, and `ω(v, i v) = ‖v‖²`. -/
theorem compatible_ofComplexModule_of_forall_eq_im_inner (ω : SymplecticForm F)
    (hω : ∀ v w, ω v w = (inner ℂ v w).im) :
    ω.Compatible (AlmostComplexStructure.ofComplexModule F) := by
  refine .of_tames ((ω.invariant_iff _).2 fun v w ↦ ?_) fun v hv ↦ ?_
  · simp [hω, inner_smul_left, inner_smul_right]
  · rw [hω, AlmostComplexStructure.ofComplexModule_apply, inner_smul_right,
      inner_self_eq_norm_sq_to_K]
    simp only [Complex.mul_im, Complex.I_re, Complex.I_im, zero_mul, one_mul, zero_add]
    exact_mod_cast pow_pos (norm_pos_iff.2 hv) 2

end TauCeti.SymplecticForm
