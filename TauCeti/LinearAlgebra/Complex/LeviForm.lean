/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.LinearAlgebra.BilinearForm.Properties
public import Mathlib.LinearAlgebra.SesquilinearForm.Basic
public import TauCeti.LinearAlgebra.Complex.Finrank
public import TauCeti.LinearAlgebra.Complex.Module
public import TauCeti.LinearAlgebra.Dimension.Submodule
public import TauCeti.LinearAlgebra.TotallyReal.QuadraticForm

/-!
# The Levi form of a real bilinear form on a complex vector space

Let `V` be a complex vector space and `B` a real bilinear form on its underlying real space.
The **Levi form** of `B` is the sesquilinear form

`B.leviForm v w = (B v w + B (I • v) (I • w) + I * (B (I • v) w - B v (I • w))) / 4`,

conjugate-linear in `v` and complex-linear in `w`. It is the `(1,1)`-part of `B`: on a coordinate
basis `e_j` of `V`, with `I • e_j` the imaginary coordinate directions, write
`B_{x_j y_k} = B (e_j) (I • e_k)` and similarly for the other entries. Then the entry
`B.leviForm (e_j) (e_k)` is `(B_{x_j x_k} + B_{y_j y_k} + I (B_{y_j x_k} - B_{x_j y_k})) / 4`, so
for the (symmetric) real Hessian `B` of a function `f` the entry `B.leviForm (e_k) (e_j)` is the
Wirtinger derivative `∂²f / ∂z_j ∂(conj z_k)`. The real part of its diagonal is one quarter of
`B v v + B (I • v) (I • v)`, and for symmetric `B` the diagonal is this real number.

The Levi form forgets the part of `B` which anticommutes with multiplication by `I`. This is why
it transforms well under holomorphic maps: the second derivative of a holomorphic map is complex
bilinear, and its contribution to a real Hessian is killed by the Levi form.

## Main definitions

* `LinearMap.BilinForm.leviForm`: the Levi form of a real bilinear form.

## Main results

* `LinearMap.BilinForm.re_leviForm_apply`, `LinearMap.BilinForm.im_leviForm_apply`: the real
  and imaginary parts of the Levi form.
* `LinearMap.BilinForm.leviForm_apply_self`: for symmetric `B`, the diagonal value is the real
  number `(B v v + B (I • v) (I • v)) / 4`.
* `LinearMap.BilinForm.isSymm_leviForm`: the Levi form of a symmetric form is Hermitian.
* `LinearMap.BilinForm.leviForm_add`, `LinearMap.BilinForm.leviForm_smul`: the Levi form is real
  linear in `B`.
* `LinearMap.BilinForm.leviForm_compl₁₂_apply`: pullback along a complex-linear map.
* `LinearMap.BilinForm.leviForm_eq_zero_iff`: the Levi form vanishes exactly on the forms which
  anticommute with multiplication by `I`, such as real parts of complex bilinear forms.
* `LinearMap.BilinForm.finrank_add_finrank_le_of_re_leviForm_pos`: if the Levi form is positive
  on a complex subspace `P`, every real subspace on which `B` is nonpositive has dimension at most
  `dim_ℝ V - dim_ℂ P`.
* `LinearMap.BilinForm.sigNeg_add_finrank_le_of_re_leviForm_pos`: if the Levi form of `B` is
  positive definite on a complex subspace `P` of the `n`-dimensional space `V`, then the negative
  index of inertia of `B` is at most `2n - dim_ℂ P`. In particular, if the Levi form has at least
  `n - q` positive directions, the negative index of `B` is at most `n + q`.

## References

* R. Hain, *Notes on the Morse theory of complex manifolds*.
* L. Hörmander, *An introduction to complex analysis in several variables*, Chapter II.
-/

public section

open Complex ComplexConjugate

namespace LinearMap.BilinForm

variable {V W : Type*} [AddCommGroup V] [Module ℝ V] [Module ℂ V] [IsScalarTower ℝ ℂ V]
  [AddCommGroup W] [Module ℝ W] [Module ℂ W] [IsScalarTower ℝ ℂ W]

/-- The **Levi form** of a real bilinear form `B` on a complex vector space: the sesquilinear form
`(B v w + B (I • v) (I • w) + I * (B (I • v) w - B v (I • w))) / 4`, conjugate-linear in `v` and
complex-linear in `w`. It is the `(1,1)`-part of `B`; for symmetric `B` its diagonal is one
quarter of `B v v + B (I • v) (I • v)`. -/
noncomputable def leviForm (B : LinearMap.BilinForm ℝ V) : V →ₗ⋆[ℂ] V →ₗ[ℂ] ℂ :=
  LinearMap.mk₂'ₛₗ (starRingEnd ℂ) (RingHom.id ℂ)
    (fun v w ↦ (4 : ℂ)⁻¹ *
      ((B v w + B (I • v) (I • w) : ℝ) + I * (B (I • v) w - B v (I • w) : ℝ)))
    (fun v₁ v₂ w ↦ by simp only [smul_add, map_add, LinearMap.add_apply]; push_cast; ring)
    (fun c v w ↦ by
      -- Split `c • v` into real multiples of `v` and `I • v`; `re_smul_add_im_smul` is a `simp`
      -- lemma folding this back, so only the linearity lemmas are used before `Complex.ext`.
      rw [← re_smul_add_im_smul c v]
      simp only [smul_add, smul_comm I, smul_smul, I_mul_I, neg_smul, one_smul, map_add,
        map_smul, map_neg, LinearMap.add_apply, LinearMap.smul_apply, LinearMap.neg_apply,
        smul_eq_mul, starRingEnd_apply]
      apply Complex.ext <;> simp <;> ring)
    (fun v w₁ w₂ ↦ by simp only [smul_add, map_add]; push_cast; ring)
    (fun c v w ↦ by
      rw [← re_smul_add_im_smul c w]
      simp only [smul_add, smul_comm I, smul_smul, I_mul_I, neg_smul, one_smul, map_add,
        map_smul, map_neg, smul_eq_mul, RingHom.id_apply]
      apply Complex.ext <;> simp <;> ring)

variable (B B' : LinearMap.BilinForm ℝ V)

/-- The defining formula of the Levi form. -/
theorem leviForm_apply (v w : V) :
    B.leviForm v w = (4 : ℂ)⁻¹ *
      ((B v w + B (I • v) (I • w) : ℝ) + I * (B (I • v) w - B v (I • w) : ℝ)) :=
  (rfl)

/-- The real part of the Levi form is the `I`-invariant part of `B`, divided by four. -/
@[simp]
theorem re_leviForm_apply (v w : V) :
    (B.leviForm v w).re = (B v w + B (I • v) (I • w)) / 4 := by
  rw [leviForm_apply]
  simp
  ring

/-- The imaginary part of the Levi form. -/
@[simp]
theorem im_leviForm_apply (v w : V) :
    (B.leviForm v w).im = (B (I • v) w - B v (I • w)) / 4 := by
  rw [leviForm_apply]
  simp
  ring

/-- The diagonal of the Levi form of a symmetric form is the real number
`(B v v + B (I • v) (I • v)) / 4`. -/
theorem leviForm_apply_self {B : LinearMap.BilinForm ℝ V} (hB : IsSymm B) (v : V) :
    B.leviForm v v = ((B v v + B (I • v) (I • v)) / 4 : ℝ) := by
  apply Complex.ext
  · simp
  · simp [hB.eq (I • v) v]

/-- The Levi form of a symmetric form is Hermitian. -/
theorem isSymm_leviForm {B : LinearMap.BilinForm ℝ V} (hB : IsSymm B) : B.leviForm.IsSymm where
  eq v w := by
    apply Complex.ext
    · simp [hB.eq w v, hB.eq (I • w) (I • v)]
    · simp [hB.eq w (I • v), hB.eq (I • w) v]
      ring

/-- The Levi form is real linear in the bilinear form. -/
@[simp]
theorem leviForm_zero : (0 : LinearMap.BilinForm ℝ V).leviForm = 0 := by
  ext v w
  apply Complex.ext <;> simp

@[simp]
theorem leviForm_add : (B + B').leviForm = B.leviForm + B'.leviForm := by
  ext v w
  apply Complex.ext <;> simp <;> ring

@[simp]
theorem leviForm_neg : (-B).leviForm = -B.leviForm := by
  ext v w
  apply Complex.ext <;> simp <;> ring

@[simp]
theorem leviForm_sub : (B - B').leviForm = B.leviForm - B'.leviForm := by
  ext v w
  apply Complex.ext <;> simp <;> ring

@[simp]
theorem leviForm_smul (r : ℝ) : (r • B).leviForm = (r : ℂ) • B.leviForm := by
  ext v w
  apply Complex.ext <;> simp <;> ring

/-- **Pullback along a complex-linear map.** The Levi form of `B (g ·) (g ·)` is the Levi form of
`B` evaluated on the images under `g`. -/
@[simp]
theorem leviForm_compl₁₂_apply (g : W →ₗ[ℂ] V) (v w : W) :
    leviForm (B.compl₁₂ (g.restrictScalars ℝ) (g.restrictScalars ℝ)) v w =
      B.leviForm (g v) (g w) := by
  simp [leviForm_apply]

/-- The Levi form of `B` vanishes exactly when `B` anticommutes with multiplication by `I`, that
is, when `B (I • v) (I • w) = -B v w`. Real parts of complex bilinear forms are of this kind. -/
theorem leviForm_eq_zero_iff : B.leviForm = 0 ↔ ∀ v w, B (I • v) (I • w) = -B v w := by
  constructor
  · intro h v w
    have h' := congrArg Complex.re (LinearMap.congr_fun₂ h v w)
    rw [re_leviForm_apply] at h'
    simp only [LinearMap.zero_apply, zero_re] at h'
    linarith
  · intro h
    -- Replacing `w` by `I • (-I • w)` turns the hypothesis into `B (I • v) w = B v (I • w)`.
    have h' (v w : V) : B (I • v) w = B v (I • w) := by
      have := h v (-I • w)
      rwa [smul_smul, mul_neg, I_mul_I, neg_neg, one_smul, neg_smul, map_neg, neg_neg] at this
    ext v w
    apply Complex.ext <;> simp [h, h']

section FiniteDimensional

open Module

variable [FiniteDimensional ℂ V]

/-- **Real index bound from a complex positive subspace.** If the Levi form of `B` is positive
definite on a complex subspace `P`, then every real subspace on which `B` is nonpositive
has dimension at most `dim_ℝ V - dim_ℂ P`. -/
theorem finrank_add_finrank_le_of_re_leviForm_pos {P : Submodule ℂ V}
    (hP : ∀ v ∈ P, v ≠ 0 → 0 < (B.leviForm v v).re) {W : Submodule ℝ V}
    (hW : ∀ v ∈ W, B v v ≤ 0) :
    finrank ℝ W + finrank ℂ P ≤ finrank ℝ V := by
  have : FiniteDimensional ℝ V := Module.Finite.trans ℂ V
  have : FiniteDimensional ℝ P := Module.Finite.trans ℂ P
  -- Restrict `B` and multiplication by `I` to the real space underlying `P`. There
  -- `Q v + Q (I • v)` is positive definite, so `W ∩ P` is totally real.
  let ι : P →ₗ[ℝ] V := P.subtype.restrictScalars ℝ
  let J : P →ₗ[ℝ] P := (I • LinearMap.id : P →ₗ[ℂ] P).restrictScalars ℝ
  let Q : QuadraticForm ℝ P := B.toQuadraticMap.comp ι
  have hQJ : (Q + Q.comp J).PosDef := by
    intro v hv
    have := hP v v.2 (by simpa using hv)
    rw [re_leviForm_apply] at this
    simpa [Q, J, ι] using (by linarith : 0 < B v v + B (I • (v : V)) (I • (v : V)))
  have h₁ := Q.two_mul_finrank_le_of_add_comp_posDef (W := W.comap ι) J hQJ fun v hv ↦ by
    simpa only [Q, QuadraticMap.comp_apply, LinearMap.BilinMap.toQuadraticMap_apply]
      using hW (ι v) hv
  have h₂ := Submodule.finrank_add_finrank_le_finrank_comap_add_finrank ι W
  have h₃ : finrank ℝ P = 2 * finrank ℂ P := TauCeti.finrank_real_eq_two_mul_finrank_complex
  have h₄ : finrank ℝ V = 2 * finrank ℂ V := TauCeti.finrank_real_eq_two_mul_finrank_complex
  have h₅ := Submodule.finrank_le P
  omega

/-- **Negative inertia bound from a complex positive subspace.** If the Levi form of `B` is
positive definite on a complex subspace `P`, then the negative index of inertia of `B` is at most
`dim_ℝ V - dim_ℂ P`. -/
theorem sigNeg_add_finrank_le_of_re_leviForm_pos {P : Submodule ℂ V}
    (hP : ∀ v ∈ P, v ≠ 0 → 0 < (B.leviForm v v).re) :
    sigNeg B.toQuadraticMap + finrank ℂ P ≤ finrank ℝ V := by
  have : FiniteDimensional ℝ V := Module.Finite.trans ℂ V
  obtain ⟨W, hWdim, hW⟩ := exists_finrank_eq_sigNeg_and_negDef B.toQuadraticMap
  rw [← hWdim]
  exact B.finrank_add_finrank_le_of_re_leviForm_pos hP fun v hv ↦ by
    simpa only [QuadraticMap.restrict_apply, _root_.neg_apply,
      LinearMap.BilinMap.toQuadraticMap_apply, neg_nonneg] using hW.nonneg ⟨v, hv⟩

end FiniteDimensional

end LinearMap.BilinForm
