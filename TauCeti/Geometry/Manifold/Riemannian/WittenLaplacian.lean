/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.DeRham.Witten
public import TauCeti.Geometry.Manifold.Riemannian.Codifferential
import TauCeti.Geometry.Manifold.ContMDiffMap.Basic
import TauCeti.Geometry.Manifold.DeRham.DegreeZero
import TauCeti.Geometry.Manifold.Riemannian.Gradient.ChainRule
import TauCeti.Geometry.Manifold.Riemannian.VolumeForm.Divergence.Basic

/-!
# The Witten codifferential and the Witten Laplacian

Let `M` be an oriented Riemannian manifold of dimension `m`, `f` a smooth function on `M` and `t`
a real parameter. Witten's deformation `d_t = e^{-t f} ∘ d ∘ e^{t f}` of the exterior derivative
(`TauCeti.wittenExtDerivₗ`) has the formal adjoint

`d_t^* = e^{t f} ∘ d^* ∘ e^{-t f}`

(`TauCeti.wittenCodifferential`), conjugating the codifferential `d^*`
(`TauCeti.SmoothForm.codifferential`) the other way. On a boundaryless manifold, for smooth forms
`α` of degree `k` and `β` of degree `k + 1`, one of them compactly supported,

`∫_M ⟨d_t α, β⟩ vol = ∫_M ⟨α, d_t^* β⟩ vol`

(`TauCeti.integralTopForm_inner_wittenExtDerivₗ_eq_inner_wittenCodifferential`), because
multiplication by the positive function `e^{± t f}` is symmetric for the pointwise inner product
of forms and does not change supports. Like `d^*`, the operator `d_t^*` squares to zero, and like
`d_t = d + t df ∧ ·` it is a local operator: `d_t^* = d^* + t ι_(grad f)` for the contraction
`ι_(grad f)` with the gradient of `f` (`TauCeti.wittenCodifferential_eq_add_smul_gradInteriorₗ`).
Classically `ι_(grad f)` is the pointwise adjoint of `df ∧ ·`; that adjointness is not proved
here. In terms of the Hodge star
`d_t^* β = d^* β + t (-1) ^ (m (k + 2)) ⋆(df ∧ ⋆β)` on `(k + 1)`-forms
(`TauCeti.wittenCodifferential_eq_add_smul`).

The **Witten Laplacian** `Δ_t = d_t^* d_t + d_t d_t^*` (`TauCeti.wittenLaplacian`, with only
`d_t^* d_t` in degree `0` and only `d_t d_t^*` in the top degree) is, for a Morse function `f`, the
operator whose low-lying spectrum concentrates near the critical points of `f` as `t → ∞`; this
is how Witten compares de Rham cohomology with the Morse complex. Unlike `d_t` and `d_t^*`, it is
not conjugate to the Hodge Laplacian, since the two conjugations go in opposite directions. At
`t = 0` it is the Hodge Laplacian (`TauCeti.wittenLaplacian_zero`), and in general it is the
Hodge Laplacian perturbed by a potential:

`Δ_t α = Δα + t K_f α + t² |df|² α`

(`TauCeti.wittenLaplacian_apply`). Expanding the Laplacian of the pair `(d + t df ∧ ·, d^* +
t ι_(grad f))` gives the coefficient `ι_(grad f) (df ∧ ·) + df ∧ ι_(grad f) ·` of `t²`, which the
Koszul identity turns into multiplication by `|df|²`, and the coefficient of `t`, the **Hessian
term** `K_f = (ι_(grad f) d + d ι_(grad f)) + (d^* (df ∧ ·) + df ∧ d^* ·)`
(`TauCeti.wittenHessianTerm`). The Hessian term is a zeroth-order operator: it is linear over
smooth functions (`TauCeti.wittenHessianTerm_funSMulₗ`), since the first-order terms produced by
the Leibniz rules for `d` and `d^*` cancel. On functions it is multiplication by `Δf`
(`TauCeti.wittenHessianTerm_ofFunction`) and on top-degree forms multiplication by `-Δf`
(`TauCeti.wittenHessianTerm_apply_top`). For `f = x²` on the line these are the harmonic
oscillators `-∂² + 4 t² x² - 2 t` on functions and `-∂² + 4 t² x² + 2 t` on one-forms. In an
orthonormal frame `(eᵢ)` the Hessian term is classically `∑_{i,j} Hess f(eᵢ, eⱼ) [eⁱ ∧ ·, ι_(eⱼ)]`;
that frame formula is not proved here.

This file proves the formal properties of `Δ_t` on smooth forms. Since `Δ_t` is the Laplacian
`TauCeti.SmoothForm.laplacian` of the pair `(d_t, d_t^*)`, they follow, exactly as for the Hodge
Laplacian, from the adjointness of `d_t^*` and `d_t` and from the preservation of compact
support. By Green's formulas
`∫_M ⟨d_t^* d_t α, β⟩ vol = ∫_M ⟨d_t α, d_t β⟩ vol` and
`∫_M ⟨d_t d_t^* α, β⟩ vol = ∫_M ⟨d_t^* α, d_t^* β⟩ vol`, the Witten Laplacian is formally
self-adjoint and nonnegative, and a compactly supported form of positive degree lies in its kernel
exactly when it is annihilated by both `d_t` and `d_t^*`. A compactly supported function `g` lies
in it exactly when `d_t g = 0`, that is, when `e^{t f} g` is locally constant. Every function
annihilated by `d_t` is Witten-harmonic, so `Δ_t e^{-t f} = 0`, and on a compact preconnected
boundaryless manifold the Witten-harmonic functions are exactly the multiples of `e^{-t f}`. For
`f = x²` on the line and `t > 0` this ground state is the Gaussian `e^{-t x²}` of the harmonic
oscillator.

The Hilbert-space realization of `Δ_t` as a self-adjoint operator and its spectral analysis as
`t → ∞` are not treated here.

## Main definitions

* `TauCeti.wittenCodifferential`: the Witten codifferential `d_t^* = e^{t f} d^* e^{-t f}`.
* `TauCeti.wittenLaplacian`: the Witten Laplacian `Δ_t = d_t^* d_t + d_t d_t^*`.
* `TauCeti.wittenHessianTerm`: the Hessian term `K_f`, the coefficient of `t` in `Δ_t`.

## Main results

* `TauCeti.integralTopForm_inner_wittenExtDerivₗ_eq_inner_wittenCodifferential`: `d_t^*` is the
  formal adjoint of `d_t`.
* `TauCeti.wittenCodifferential_comp_wittenCodifferential`: `d_t^* ∘ d_t^* = 0`.
* `TauCeti.wittenCodifferential_eq_smul_hodgeStar`: `d_t^* = (-1) ^ (m (k + 2) + 1) ⋆ d_{-t} ⋆`.
* `TauCeti.wittenCodifferential_eq_add_smul`: `d_t^* β = d^* β + t (-1) ^ (m (k + 2)) ⋆(df ∧ ⋆β)`.
* `TauCeti.wittenCodifferential_eq_add_smul_gradInteriorₗ`: `d_t^* = d^* + t ι_(grad f)`.
* `TauCeti.wittenLaplacian_zero`: at `t = 0` the Witten Laplacian is the Hodge Laplacian.
* `TauCeti.wittenLaplacian_eq_add_smul_add_smul`, `TauCeti.wittenLaplacian_apply`: Witten's
  expansion `Δ_t = Δ + t K_f + t² |df|²`.
* `TauCeti.wittenHessianTerm_funSMulₗ`: the Hessian term is linear over smooth functions.
* `TauCeti.wittenHessianTerm_ofFunction`, `TauCeti.wittenHessianTerm_apply_top`: on functions the
  Hessian term is multiplication by `Δf`, and on top-degree forms by `-Δf`.
* `TauCeti.integralTopForm_inner_wittenCodifferential_wittenExtDerivₗ`,
  `TauCeti.integralTopForm_inner_wittenExtDerivₗ_wittenCodifferential`: Green's formulas for
  `d_t^* d_t` and `d_t d_t^*`.
* `TauCeti.integralTopForm_inner_wittenLaplacian_eq_inner_wittenLaplacian`: `Δ_t` is formally
  self-adjoint.
* `TauCeti.integralTopForm_inner_wittenLaplacian_self_nonneg`: `0 ≤ ∫_M ⟨Δ_t α, α⟩ vol`.
* `TauCeti.wittenLaplacian_eq_zero_iff`: a compactly supported form of positive degree is
  Witten-harmonic exactly when `d_t α = 0` and `d_t^* α = 0`.
* `TauCeti.wittenLaplacian_eq_zero_iff_wittenExtDerivₗ_eq_zero`: a compactly supported function is
  Witten-harmonic exactly when `d_t g = 0`.
* `TauCeti.wittenLaplacian_expSMulEquiv_neg_ofFunction_one`: `Δ_t e^{-t f} = 0`.
* `TauCeti.wittenLaplacian_eq_zero_iff_exists_eq_smul`: on a compact preconnected boundaryless
  manifold, `Δ_t g = 0` exactly when `g` is a constant multiple of `e^{-t f}`.

## References

* E. Witten, *Supersymmetry and Morse theory*, J. Differential Geom. **17** (1982), 661–692,
  Section 2 (the deformed differential `d_t`, its adjoint `d_t^*`, the Laplacian
  `d_t d_t^* + d_t^* d_t` and its expansion in powers of `t`).
* H. L. Cycon, R. G. Froese, W. Kirsch and B. Simon, *Schrödinger Operators*, Springer, 1987,
  Chapter 11 (Witten's proof of the Morse inequalities).
-/

public section

noncomputable section

open Bundle Set
open scoped Manifold ContDiff RealInnerProductSpace

namespace TauCeti

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]

variable [FiniteDimensional ℝ E] [IsManifold I ∞ M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
  {m k l : ℕ}

omit [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)] in
/-- Multiplication by `e^{t f}` is symmetric for the pointwise inner product of forms. -/
private theorem alternatingFormInner_expSMulEquiv (f : C^∞⟮I, M; ℝ⟯) (t : ℝ)
    (α β : SmoothForm I M ℝ k) (x : M) :
    alternatingFormInner (TangentSpace I x) k ((expSMulEquiv k f t α).val x) (β.val x) =
      alternatingFormInner (TangentSpace I x) k (α.val x) ((expSMulEquiv k f t β).val x) := by
  simp only [coe_expSMulEquiv, LinearMap.map_smul, LinearMap.smul_apply]

/-- The Hodge star commutes with multiplication by `e^{t f}`. -/
theorem hodgeStar_expSMulEquiv (o : Manifold.Orientation I M (Fin m)) (f : C^∞⟮I, M; ℝ⟯) (t : ℝ)
    (hkl : k + l = m) (φ : SmoothForm I M ℝ k) :
    SmoothForm.hodgeStar o hkl (expSMulEquiv k f t φ) =
      expSMulEquiv l f t (SmoothForm.hodgeStar o hkl φ) := by
  apply Subtype.ext
  funext x
  simp only [SmoothForm.coe_hodgeStar, RoughForm.hodgeStar_apply, coe_expSMulEquiv, map_smul]

/-! ### The Witten codifferential -/

/-- **The Witten codifferential** `d_t^* = e^{t f} ∘ d^* ∘ e^{-t f}` of smooth `(k + 1)`-forms on
an oriented Riemannian manifold of dimension `m = k + 1 + l`, the formal adjoint of the Witten
differential `d_t = e^{-t f} ∘ d ∘ e^{t f}`
(`TauCeti.integralTopForm_inner_wittenExtDerivₗ_eq_inner_wittenCodifferential`). -/
def wittenCodifferential (o : Manifold.Orientation I M (Fin m)) (f : C^∞⟮I, M; ℝ⟯) (t : ℝ)
    (hkl : k + 1 + l = m) : SmoothForm I M ℝ (k + 1) →ₗ[ℝ] SmoothForm I M ℝ k :=
  (expSMulEquiv k f t).toLinearMap ∘ₗ SmoothForm.codifferential o hkl ∘ₗ
    (expSMulEquiv (k + 1) f (-t)).toLinearMap

/-- The defining conjugation formula `d_t^* β = e^{t f} d^* (e^{-t f} β)`. -/
theorem wittenCodifferential_def (o : Manifold.Orientation I M (Fin m)) (f : C^∞⟮I, M; ℝ⟯)
    (t : ℝ) (hkl : k + 1 + l = m) (β : SmoothForm I M ℝ (k + 1)) :
    wittenCodifferential o f t hkl β =
      expSMulEquiv k f t (SmoothForm.codifferential o hkl (expSMulEquiv (k + 1) f (-t) β)) :=
  (rfl)

/-- **Multiplication by `e^{-t f}` intertwines `d_t^*` with `d^*`:**
`e^{-t f} d_t^* β = d^* (e^{-t f} β)`. -/
theorem expSMulEquiv_neg_wittenCodifferential (o : Manifold.Orientation I M (Fin m))
    (f : C^∞⟮I, M; ℝ⟯) (t : ℝ) (hkl : k + 1 + l = m) (β : SmoothForm I M ℝ (k + 1)) :
    expSMulEquiv k f (-t) (wittenCodifferential o f t hkl β) =
      SmoothForm.codifferential o hkl (expSMulEquiv (k + 1) f (-t) β) := by
  rw [wittenCodifferential_def, ← expSMulEquiv_symm, LinearEquiv.symm_apply_apply]

/-- At `t = 0` the Witten codifferential is the codifferential. -/
@[simp]
theorem wittenCodifferential_zero (o : Manifold.Orientation I M (Fin m)) (f : C^∞⟮I, M; ℝ⟯)
    (hkl : k + 1 + l = m) :
    wittenCodifferential o f 0 hkl = SmoothForm.codifferential o hkl := by
  ext β : 1
  simp [wittenCodifferential_def]

/-- The Witten codifferential does not depend on the orientation. -/
@[simp]
theorem wittenCodifferential_neg_orientation (o : Manifold.Orientation I M (Fin m))
    (f : C^∞⟮I, M; ℝ⟯) (t : ℝ) (hkl : k + 1 + l = m) :
    wittenCodifferential (-o) f t hkl = wittenCodifferential o f t hkl := by
  ext β : 1
  simp [wittenCodifferential_def]

/-- **The Witten codifferential squares to zero**: `d_t^* d_t^* β = 0`, since it is conjugate to
the codifferential. -/
@[simp]
theorem wittenCodifferential_wittenCodifferential {l' : ℕ}
    (o : Manifold.Orientation I M (Fin m)) (f : C^∞⟮I, M; ℝ⟯) (t : ℝ) (hkl : k + 1 + l = m)
    (hkl' : k + 1 + 1 + l' = m) (β : SmoothForm I M ℝ (k + 1 + 1)) :
    wittenCodifferential o f t hkl (wittenCodifferential o f t hkl' β) = 0 := by
  rw [wittenCodifferential_def (hkl := hkl), expSMulEquiv_neg_wittenCodifferential,
    SmoothForm.codifferential_codifferential, map_zero]

/-- The Witten codifferential squares to zero as a linear map: `d_t^* ∘ d_t^* = 0`. -/
@[simp]
theorem wittenCodifferential_comp_wittenCodifferential {l' : ℕ}
    (o : Manifold.Orientation I M (Fin m)) (f : C^∞⟮I, M; ℝ⟯) (t : ℝ) (hkl : k + 1 + l = m)
    (hkl' : k + 1 + 1 + l' = m) :
    wittenCodifferential o f t hkl ∘ₗ wittenCodifferential o f t hkl' = 0 :=
  LinearMap.ext (wittenCodifferential_wittenCodifferential o f t hkl hkl')

/-- The Witten codifferential is `d_t^* = (-1) ^ (m (k + 2) + 1) ⋆ d_{-t} ⋆`, the formula
`d^* = (-1) ^ (m (k + 2) + 1) ⋆ d ⋆` of the codifferential with `d` replaced by `d_{-t}`. -/
theorem wittenCodifferential_eq_smul_hodgeStar (o : Manifold.Orientation I M (Fin m))
    (f : C^∞⟮I, M; ℝ⟯) (t : ℝ) (hkl : k + 1 + l = m) (hlk : l + 1 + k = m)
    (β : SmoothForm I M ℝ (k + 1)) :
    wittenCodifferential o f t hkl β =
      (-1 : ℝ) ^ (m * (k + 2) + 1) •
        SmoothForm.hodgeStar o hlk (wittenExtDerivₗ f (-t) l (SmoothForm.hodgeStar o hkl β)) := by
  -- `e^{t f} (±⋆ d (e^{-t f} ⋆β)) = e^{t f} (±⋆ e^{-t f} d_{-t} ⋆β) = ±⋆ d_{-t} ⋆β`.
  rw [wittenCodifferential_def, SmoothForm.codifferential_apply o hkl hlk, hodgeStar_expSMulEquiv,
    ← expSMulEquiv_wittenExtDerivₗ, hodgeStar_expSMulEquiv, map_smul, ← expSMulEquiv_symm,
    LinearEquiv.apply_symm_apply]

/-- **The Witten codifferential is the local operator
`d_t^* β = d^* β + t (-1) ^ (m (k + 2)) ⋆(df ∧ ⋆β)`** on `(k + 1)`-forms, where `df ∧ ·` is
exterior multiplication by the differential of `f` (`TauCeti.SmoothForm.extDerivWedgeₗ`). The
zeroth-order operator `(-1) ^ (m (k + 2)) ⋆(df ∧ ⋆·)` is the contraction with the gradient of `f`
(`TauCeti.wittenCodifferential_eq_add_smul_gradInteriorₗ`). -/
theorem wittenCodifferential_eq_add_smul (o : Manifold.Orientation I M (Fin m))
    (f : C^∞⟮I, M; ℝ⟯) (t : ℝ) (hkl : k + 1 + l = m) (hlk : l + 1 + k = m)
    (β : SmoothForm I M ℝ (k + 1)) :
    wittenCodifferential o f t hkl β =
      SmoothForm.codifferential o hkl β + (t * (-1 : ℝ) ^ (m * (k + 2))) •
        SmoothForm.hodgeStar o hlk
          (SmoothForm.extDerivWedgeₗ f l (SmoothForm.hodgeStar o hkl β)) := by
  rw [wittenCodifferential_eq_smul_hodgeStar o f t hkl hlk, wittenExtDerivₗ_eq_add_smul,
    LinearMap.add_apply, LinearMap.smul_apply, map_add, map_smul, smul_add,
    ← SmoothForm.codifferential_apply o hkl hlk, smul_smul, pow_succ]
  congr 2
  ring

/-- The Witten codifferential does not enlarge supports. -/
theorem tsupport_wittenCodifferential_subset (o : Manifold.Orientation I M (Fin m))
    (f : C^∞⟮I, M; ℝ⟯) (t : ℝ) (hkl : k + 1 + l = m) (β : SmoothForm I M ℝ (k + 1)) :
    _root_.tsupport (α := E [⋀^Fin k]→L[ℝ] ℝ) (wittenCodifferential o f t hkl β).val ⊆
      _root_.tsupport (α := E [⋀^Fin (k + 1)]→L[ℝ] ℝ) β.val := by
  rw [wittenCodifferential_def, tsupport_expSMulEquiv, ← tsupport_expSMulEquiv f (-t) β]
  exact SmoothForm.tsupport_codifferential_subset o hkl _

/-- The Witten codifferential of a compactly supported form is compactly supported. -/
theorem wittenCodifferential_mem_compactlySupportedForms (o : Manifold.Orientation I M (Fin m))
    (f : C^∞⟮I, M; ℝ⟯) (t : ℝ) (hkl : k + 1 + l = m) {β : SmoothForm I M ℝ (k + 1)}
    (hβ : β ∈ compactlySupportedForms I M (k + 1)) :
    wittenCodifferential o f t hkl β ∈ compactlySupportedForms I M k := by
  rw [wittenCodifferential_def, expSMulEquiv_mem_compactlySupportedForms_iff]
  exact SmoothForm.codifferential_mem_compactlySupportedForms o hkl
    ((expSMulEquiv_mem_compactlySupportedForms_iff f (-t)).2 hβ)

/-! ### The Witten Laplacian -/

/-- **The Witten Laplacian** `Δ_t = d_t^* d_t + d_t d_t^*` of smooth `k`-forms on an oriented
Riemannian manifold of dimension `m = k + l`, the Laplacian `TauCeti.SmoothForm.laplacian` of the
Witten differential `d_t = e^{-t f} d e^{t f}` and the Witten codifferential
`d_t^* = e^{t f} d^* e^{-t f}`. As for the Hodge Laplacian, in degree `0` only `d_t^* d_t` is
present and in the top degree only `d_t d_t^*`. It is formally self-adjoint and nonnegative
(`TauCeti.integralTopForm_inner_wittenLaplacian_eq_inner_wittenLaplacian`,
`TauCeti.integralTopForm_inner_wittenLaplacian_self_nonneg`), and at `t = 0` it is the Hodge
Laplacian (`TauCeti.wittenLaplacian_zero`). -/
def wittenLaplacian (o : Manifold.Orientation I M (Fin m)) (f : C^∞⟮I, M; ℝ⟯) (t : ℝ) :
    ∀ {k l : ℕ}, k + l = m → SmoothForm I M ℝ k →ₗ[ℝ] SmoothForm I M ℝ k :=
  SmoothForm.laplacian (wittenExtDerivₗ f t) fun hkl ↦ wittenCodifferential o f t hkl

/-- The Witten Laplacian is the Laplacian of the pair `(d_t, d_t^*)`. -/
theorem wittenLaplacian_def (o : Manifold.Orientation I M (Fin m)) (f : C^∞⟮I, M; ℝ⟯) (t : ℝ)
    (hkl : k + l = m) :
    wittenLaplacian o f t hkl =
      SmoothForm.laplacian (wittenExtDerivₗ f t) (fun hkl ↦ wittenCodifferential o f t hkl) hkl :=
  (rfl)

/-- On a zero-dimensional manifold the Witten Laplacian of functions is zero. -/
@[simp]
theorem wittenLaplacian_zero_zero (o : Manifold.Orientation I M (Fin m)) (f : C^∞⟮I, M; ℝ⟯)
    (t : ℝ) (hkl : 0 + 0 = m) (g : SmoothForm I M ℝ 0) : wittenLaplacian o f t hkl g = 0 :=
  SmoothForm.laplacian_zero_zero _ _ hkl g

/-- In positive dimension the Witten Laplacian of functions is `Δ_t g = d_t^* d_t g`. -/
theorem wittenLaplacian_zero_add_one (o : Manifold.Orientation I M (Fin m)) (f : C^∞⟮I, M; ℝ⟯)
    (t : ℝ) (hkl : 0 + (l + 1) = m) (hkl' : 0 + 1 + l = m) (g : SmoothForm I M ℝ 0) :
    wittenLaplacian o f t hkl g = wittenCodifferential o f t hkl' (wittenExtDerivₗ f t 0 g) :=
  SmoothForm.laplacian_zero_add_one _ _ hkl hkl' g

/-- In the top degree the Witten Laplacian is `Δ_t α = d_t d_t^* α`. -/
theorem wittenLaplacian_add_one_zero (o : Manifold.Orientation I M (Fin m)) (f : C^∞⟮I, M; ℝ⟯)
    (t : ℝ) (hkl : k + 1 + 0 = m) (α : SmoothForm I M ℝ (k + 1)) :
    wittenLaplacian o f t hkl α = wittenExtDerivₗ f t k (wittenCodifferential o f t hkl α) :=
  SmoothForm.laplacian_add_one_zero _ _ hkl α

/-- Strictly between degree `0` and the top degree the Witten Laplacian is
`Δ_t α = d_t^* d_t α + d_t d_t^* α`. -/
theorem wittenLaplacian_add_one_add_one (o : Manifold.Orientation I M (Fin m))
    (f : C^∞⟮I, M; ℝ⟯) (t : ℝ) (hkl : k + 1 + (l + 1) = m) (hkl' : k + 1 + 1 + l = m)
    (α : SmoothForm I M ℝ (k + 1)) :
    wittenLaplacian o f t hkl α =
      wittenCodifferential o f t hkl' (wittenExtDerivₗ f t (k + 1) α) +
        wittenExtDerivₗ f t k (wittenCodifferential o f t hkl α) :=
  SmoothForm.laplacian_add_one_add_one _ _ hkl hkl' α

/-- **At `t = 0` the Witten Laplacian is the Hodge Laplacian.** -/
@[simp]
theorem wittenLaplacian_zero (o : Manifold.Orientation I M (Fin m)) (f : C^∞⟮I, M; ℝ⟯)
    (hkl : k + l = m) : wittenLaplacian o f 0 hkl = SmoothForm.hodgeLaplacian o hkl := by
  simp only [wittenLaplacian_def, SmoothForm.hodgeLaplacian_def, wittenCodifferential_zero,
    show wittenExtDerivₗ (I := I) f 0 = mextDerivₗ I from funext (wittenExtDerivₗ_zero f)]

/-- The Witten Laplacian does not depend on the orientation. -/
@[simp]
theorem wittenLaplacian_neg_orientation (o : Manifold.Orientation I M (Fin m))
    (f : C^∞⟮I, M; ℝ⟯) (t : ℝ) (hkl : k + l = m) :
    wittenLaplacian (-o) f t hkl = wittenLaplacian o f t hkl := by
  simp only [wittenLaplacian_def, wittenCodifferential_neg_orientation]

/-- The Witten Laplacian does not enlarge supports. -/
theorem tsupport_wittenLaplacian_subset (o : Manifold.Orientation I M (Fin m))
    (f : C^∞⟮I, M; ℝ⟯) (t : ℝ) (hkl : k + l = m) (α : SmoothForm I M ℝ k) :
    _root_.tsupport (α := E [⋀^Fin k]→L[ℝ] ℝ) (wittenLaplacian o f t hkl α).val ⊆
      _root_.tsupport (α := E [⋀^Fin k]→L[ℝ] ℝ) α.val :=
  SmoothForm.tsupport_laplacian_subset (tsupport_wittenExtDerivₗ_subset f t)
    (tsupport_wittenCodifferential_subset o f t) hkl α

/-- The Witten Laplacian of a compactly supported form is compactly supported. -/
theorem wittenLaplacian_mem_compactlySupportedForms (o : Manifold.Orientation I M (Fin m))
    (f : C^∞⟮I, M; ℝ⟯) (t : ℝ) (hkl : k + l = m) {α : SmoothForm I M ℝ k}
    (hα : α ∈ compactlySupportedForms I M k) :
    wittenLaplacian o f t hkl α ∈ compactlySupportedForms I M k :=
  SmoothForm.laplacian_mem_compactlySupportedForms (wittenExtDerivₗ_mem_compactlySupportedForms f t)
    (wittenCodifferential_mem_compactlySupportedForms o f t) hkl hα

/-- **`e^{-t f}` is Witten-harmonic**: `Δ_t e^{-t f} = 0`, since `d_t` annihilates `e^{-t f}`.
For `f = x²` on the line and `t > 0` this is the Gaussian ground state `e^{-t x²}` of the harmonic
oscillator. -/
theorem wittenLaplacian_expSMulEquiv_neg_ofFunction_one (o : Manifold.Orientation I M (Fin m))
    (f : C^∞⟮I, M; ℝ⟯) (t : ℝ) (hl : 0 + l = m) :
    wittenLaplacian o f t hl
      (expSMulEquiv 0 f (-t) (SmoothForm.ofFunction (ContMDiffMap.const 1))) = 0 := by
  rcases l with _ | l
  · simp
  · rw [wittenLaplacian_zero_add_one o f t hl (by omega),
      wittenExtDerivₗ_expSMulEquiv_neg_ofFunction_one, map_zero]

/-! ### The expansion `Δ_t = Δ + t K_f + t² |df|²` -/

/-- **The Witten codifferential is `d_t^* = d^* + t ι_(grad f)`**, for the contraction with the
gradient of `f` (`TauCeti.SmoothForm.gradInteriorₗ`), just as `d_t = d + t df ∧ ·`
(`TauCeti.wittenExtDerivₗ_eq_add_smul`). -/
theorem wittenCodifferential_eq_add_smul_gradInteriorₗ (o : Manifold.Orientation I M (Fin m))
    (f : C^∞⟮I, M; ℝ⟯) (t : ℝ) (hkl : k + 1 + l = m) :
    wittenCodifferential o f t hkl =
      SmoothForm.codifferential o hkl + t • SmoothForm.gradInteriorₗ f k := by
  -- `e^{-t f} β = h β` for the smooth function `h = ContMDiffMap.expMul f (-t) = e^{-t f}`,
  -- whose gradient is `-t e^{-t f} grad f`; then `d^*(h β) = h d^*β + t e^{-t f} ι_(grad f) β`.
  have hgrad : Manifold.mgradient I (ContMDiffMap.expMul f (-t)) =
      fun x ↦ (-t * Real.exp (-t * f x)) • Manifold.mgradient I f x := by
    simp_rw [← Manifold.mgradient_exp_const_mul (-t) (f.contMDiff.mdifferentiableAt (by simp)),
      ← ContMDiffMap.expMul_apply f (-t)]
  ext β : 1
  have h1 := ContMDiffMap.expMul_mul_expMul_neg f t
  simp only [ContMDiffMap.expMul_apply] at h1
  have he := LinearMap.congr_fun (expSMulEquiv_eq_funSMulₗ (k := k + 1) f (-t)) β
  rw [LinearEquiv.coe_coe] at he
  rw [wittenCodifferential_def, he, SmoothForm.codifferential_funSMulₗ]
  apply Subtype.ext
  funext x
  simp only [coe_expSMulEquiv, Submodule.coe_sub, SmoothForm.coe_funSMulₗ,
    SmoothForm.coe_gradInteriorₗ, hgrad, RoughForm.interior_smul_field, LinearMap.add_apply,
    LinearMap.smul_apply, Submodule.coe_add, Submodule.coe_smul, Pi.add_apply, Pi.sub_apply,
    Pi.smul_apply, smul_sub, smul_smul, ContMDiffMap.expMul_apply]
  rw [h1 x,
    show Real.exp (t * f x) * (-t * Real.exp (-t * f x)) = -t by linear_combination -t * h1 x,
    one_smul, neg_smul, sub_neg_eq_add]

/-- **The Hessian term of the Witten Laplacian** on smooth `k`-forms of an oriented Riemannian
manifold of dimension `m = k + l`,

`K_f = (ι_(grad f) d + d ι_(grad f)) + (d^* (df ∧ ·) + df ∧ d^* ·)`,

with only the first summand of each pair in degree `0` and only the second in the top degree. It
is the coefficient of `t` in `Δ_t = Δ + t K_f + t² |df|²`
(`TauCeti.wittenLaplacian_eq_add_smul_add_smul`), and it is a zeroth-order operator, linear over
smooth functions (`TauCeti.wittenHessianTerm_funSMulₗ`): the derivatives of `α` in `K_f α` cancel.
On functions it is multiplication by the Hodge Laplacian `Δf` of `f`
(`TauCeti.wittenHessianTerm_ofFunction`). Classically, in an orthonormal frame `(eᵢ)`,
`K_f = ∑_{i,j} Hess f(eᵢ, eⱼ) [eⁱ ∧ ·, ι_(eⱼ)]`; that frame formula is not proved here. -/
def wittenHessianTerm (o : Manifold.Orientation I M (Fin m)) (f : C^∞⟮I, M; ℝ⟯) :
    ∀ {k l : ℕ}, k + l = m → SmoothForm I M ℝ k →ₗ[ℝ] SmoothForm I M ℝ k :=
  fun hkl ↦
    SmoothForm.laplacian (mextDerivₗ I) (fun {k _} _ ↦ SmoothForm.gradInteriorₗ f k) hkl +
      SmoothForm.laplacian (SmoothForm.extDerivWedgeₗ f)
        (fun hkl ↦ SmoothForm.codifferential o hkl) hkl

/-- The Hessian term is the sum of the Laplacians of the pairs `(d, ι_(grad f))` and
`(df ∧ ·, d^*)`. -/
theorem wittenHessianTerm_def (o : Manifold.Orientation I M (Fin m)) (f : C^∞⟮I, M; ℝ⟯)
    (hkl : k + l = m) :
    wittenHessianTerm o f hkl =
      SmoothForm.laplacian (mextDerivₗ I) (fun {k _} _ ↦ SmoothForm.gradInteriorₗ f k) hkl +
        SmoothForm.laplacian (SmoothForm.extDerivWedgeₗ f)
          (fun hkl ↦ SmoothForm.codifferential o hkl) hkl :=
  (rfl)

/-- The Hessian term does not depend on the orientation. -/
@[simp]
theorem wittenHessianTerm_neg_orientation (o : Manifold.Orientation I M (Fin m))
    (f : C^∞⟮I, M; ℝ⟯) (hkl : k + l = m) :
    wittenHessianTerm (-o) f hkl = wittenHessianTerm o f hkl := by
  simp only [wittenHessianTerm_def, SmoothForm.codifferential_neg_orientation]

/-- **The expansion of the Witten Laplacian** in powers of `t`:
`Δ_t = Δ + t K_f + t² (ι_(grad f) (df ∧ ·) + df ∧ ι_(grad f) ·)`, where `Δ` is the Hodge Laplacian
and `K_f` the Hessian term `TauCeti.wittenHessianTerm`. The last operator is multiplication by
`|df|²` (`TauCeti.SmoothForm.laplacian_extDerivWedgeₗ_gradInteriorₗ_apply`), which gives the
pointwise form `TauCeti.wittenLaplacian_apply`. -/
theorem wittenLaplacian_eq_add_smul_add_smul (o : Manifold.Orientation I M (Fin m))
    (f : C^∞⟮I, M; ℝ⟯) (t : ℝ) (hkl : k + l = m) :
    wittenLaplacian o f t hkl =
      SmoothForm.hodgeLaplacian o hkl + t • wittenHessianTerm o f hkl +
        t ^ 2 • SmoothForm.laplacian (SmoothForm.extDerivWedgeₗ f)
          (fun {k _} _ ↦ SmoothForm.gradInteriorₗ f k) hkl := by
  have hD : wittenExtDerivₗ (I := I) f t =
      fun k ↦ mextDerivₗ I k + t • SmoothForm.extDerivWedgeₗ f k :=
    funext (wittenExtDerivₗ_eq_add_smul f t)
  simp only [wittenLaplacian_def, hD, wittenCodifferential_eq_add_smul_gradInteriorₗ,
    SmoothForm.laplacian_add_smul, wittenHessianTerm_def, SmoothForm.hodgeLaplacian_def]

/-- **Witten's formula `Δ_t α = Δ α + t K_f α + t² |df|² α`**, pointwise, for the Hodge Laplacian
`Δ`, the zeroth-order Hessian term `K_f` (`TauCeti.wittenHessianTerm`) and the norm of the
gradient of `f`. -/
theorem wittenLaplacian_apply (o : Manifold.Orientation I M (Fin m)) (f : C^∞⟮I, M; ℝ⟯) (t : ℝ)
    (hkl : k + l = m) (α : SmoothForm I M ℝ k) (x : M) :
    (wittenLaplacian o f t hkl α).val x =
      (SmoothForm.hodgeLaplacian o hkl α).val x + t • (wittenHessianTerm o f hkl α).val x +
        (t ^ 2 * ‖Manifold.mgradient I f x‖ ^ 2) • α.val x := by
  have hP := SmoothForm.laplacian_extDerivWedgeₗ_gradInteriorₗ_apply (I := I)
    (o.fact_finrank_tangentSpace x).out f hkl α x
  simp only [wittenLaplacian_eq_add_smul_add_smul, LinearMap.add_apply, LinearMap.smul_apply,
    Submodule.coe_add, Submodule.coe_smul, Pi.add_apply, Pi.smul_apply, hP, smul_smul]

/-- **The Hessian term is a zeroth-order operator**: it is linear over smooth functions,
`K_f (g α) = g K_f α`. The first-order terms `dg ∧ ·` and `ι_(grad g)` produced by the Leibniz
rules for `d` and `d^*` combine into `⟪grad f, grad g⟫ - ⟪grad g, grad f⟫ = 0`, by the Koszul
identity `TauCeti.SmoothForm.extDerivWedgeₗ_gradInteriorₗ_add_apply`. -/
@[simp]
theorem wittenHessianTerm_funSMulₗ (o : Manifold.Orientation I M (Fin m)) (f : C^∞⟮I, M; ℝ⟯)
    (hkl : k + l = m) (g : C^∞⟮I, M; ℝ⟯) (α : SmoothForm I M ℝ k) :
    wittenHessianTerm o f hkl (SmoothForm.funSMulₗ g α) =
      SmoothForm.funSMulₗ g (wittenHessianTerm o f hkl α) := by
  apply Subtype.ext
  funext x
  have hm : Module.finrank ℝ E = m := (o.fact_finrank_tangentSpace x).out
  have hgf := real_inner_comm (Manifold.mgradient I f x) (Manifold.mgradient I g x)
  rcases k with _ | k <;> rcases l with _ | l
  · simp [wittenHessianTerm_def]
  · have h : 0 + 1 + l = m := by omega
    simp only [wittenHessianTerm_def, LinearMap.add_apply,
      SmoothForm.laplacian_zero_add_one _ _ hkl h,
      SmoothForm.mextDerivₗ_funSMulₗ, SmoothForm.extDerivWedgeₗ_funSMulₗ,
      SmoothForm.codifferential_funSMulₗ, map_add, SmoothForm.gradInteriorₗ_funSMulₗ,
      Submodule.coe_add, Submodule.coe_sub, SmoothForm.coe_funSMulₗ, Pi.add_apply, Pi.sub_apply,
      SmoothForm.gradInteriorₗ_extDerivWedgeₗ_zero_apply, hgf]
    abel
  · -- In the top degree the Koszul identity reads `dg ∧ ι_(grad f) α = ⟪grad f, grad g⟫ α`,
    -- and symmetrically.
    have hm' : Module.finrank ℝ E = k + 1 := by omega
    simp only [wittenHessianTerm_def, LinearMap.add_apply, SmoothForm.laplacian_add_one_zero,
      SmoothForm.mextDerivₗ_funSMulₗ, SmoothForm.extDerivWedgeₗ_funSMulₗ,
      SmoothForm.codifferential_funSMulₗ, map_add, map_sub, SmoothForm.gradInteriorₗ_funSMulₗ,
      Submodule.coe_add, Submodule.coe_sub, SmoothForm.coe_funSMulₗ, Pi.add_apply, Pi.sub_apply,
      SmoothForm.extDerivWedgeₗ_gradInteriorₗ_apply_top hm', hgf]
    abel
  · have h : k + 1 + 1 + l = m := by omega
    simp only [wittenHessianTerm_def, LinearMap.add_apply,
      SmoothForm.laplacian_add_one_add_one _ _ hkl h, SmoothForm.mextDerivₗ_funSMulₗ,
      SmoothForm.extDerivWedgeₗ_funSMulₗ, SmoothForm.codifferential_funSMulₗ, map_add, map_sub,
      SmoothForm.gradInteriorₗ_funSMulₗ, Submodule.coe_add, Submodule.coe_sub,
      SmoothForm.coe_funSMulₗ, Pi.add_apply, Pi.sub_apply]
    linear_combination (norm := module)
      SmoothForm.extDerivWedgeₗ_gradInteriorₗ_add_apply g f α x -
        SmoothForm.extDerivWedgeₗ_gradInteriorₗ_add_apply f g α x - hgf • α.val x

/-- **On functions the Hessian term is multiplication by `Δf`**: `K_f g = (Δf) g` for the Hodge
Laplacian `Δf = d^* df` of `f`. Together with `TauCeti.wittenLaplacian_apply` this is the
Schrödinger form `Δ_t g = Δg + t (Δf) g + t² |df|² g` of the Witten Laplacian on functions; for
`f = x²` on the line it is the harmonic oscillator `-g'' - 2 t g + 4 t² x² g`. -/
theorem wittenHessianTerm_ofFunction (o : Manifold.Orientation I M (Fin m)) (f : C^∞⟮I, M; ℝ⟯)
    (hl : 0 + l = m) (g : C^∞⟮I, M; ℝ⟯) :
    wittenHessianTerm o f hl (SmoothForm.ofFunction g) =
      SmoothForm.funSMulₗ g (SmoothForm.hodgeLaplacian o hl (SmoothForm.ofFunction f)) := by
  -- `g = g · 1`, and `K_f 1 = ι_(grad f) (d 1) + d^* (df ∧ 1) = d^* df`.
  set one := SmoothForm.ofFunction (I := I) (M := M) (ContMDiffMap.const (1 : ℝ))
  have hd1 : mextDerivₗ I 0 one = 0 := mextDerivₗ_ofFunction_const I 1
  rw [SmoothForm.ofFunction_eq_funSMulₗ_one g, wittenHessianTerm_funSMulₗ]
  congr 1
  rcases l with _ | l
  · simp [wittenHessianTerm_def]
  · have hε : SmoothForm.extDerivWedgeₗ f 0 one = mextDerivₗ I 0 (SmoothForm.ofFunction f) := by
      rw [SmoothForm.ofFunction_eq_funSMulₗ_one f, SmoothForm.mextDerivₗ_funSMulₗ, hd1, map_zero]
      exact (add_zero _).symm
    rw [wittenHessianTerm_def, LinearMap.add_apply, SmoothForm.laplacian_zero_add_one _ _ hl
      (by omega), SmoothForm.laplacian_zero_add_one _ _ hl (by omega), hd1, hε,
      SmoothForm.hodgeLaplacian_zero_add_one_eq_comp o hl (by omega)]
    simp only [map_zero, zero_add, LinearMap.comp_apply]

/-- **On top-degree forms the Hessian term is multiplication by `-Δf`**: `K_f α = -(Δf) α` for the
Hodge Laplacian `Δf = -div grad f` of `f`. Indeed `d^*` annihilates the volume form, and
`d ι_(grad f) vol = (div grad f) vol`. Together with `TauCeti.wittenLaplacian_apply` this gives
`Δ_t α = Δα - t (Δf) α + t² |df|² α` in the top degree; for `f = x²` on the line it is the
operator `-g'' + 2 t g + 4 t² x² g` on `g dx`. -/
theorem wittenHessianTerm_apply_top (o : Manifold.Orientation I M (Fin m)) (f : C^∞⟮I, M; ℝ⟯)
    (hkl : k + 0 = m) (hl : 0 + m = m) (α : SmoothForm I M ℝ k) (x : M) :
    (wittenHessianTerm o f hkl α).val x =
      (-(SmoothForm.hodgeLaplacian o hl (SmoothForm.ofFunction f)).val x 0) • α.val x := by
  rcases k with _ | k
  · obtain rfl : m = 0 := by omega
    simp [wittenHessianTerm_def]
  obtain rfl : m = k + 1 := by omega
  -- Write `α = g vol` for a smooth function `g` and the volume form `vol = ⋆1`.
  obtain ⟨g, hα⟩ := SmoothForm.exists_eq_funSMulₗ_hodgeStar_ofFunction_one o hkl hl α
  set one := SmoothForm.ofFunction (I := I) (M := M) (ContMDiffMap.const (1 : ℝ))
  set vol := SmoothForm.hodgeStar o hl one
  have hvol : (vol : RoughForm I M ℝ (k + 1)) = riemannianVolumeForm o :=
    SmoothForm.coe_hodgeStar_ofFunction_one o hl
  -- `K_f vol = d ι_(grad f) vol + df ∧ d^* vol`, and `d^* vol = 0`.
  have hK : (wittenHessianTerm o f hkl vol : RoughForm I M ℝ (k + 1)) =
      fun y ↦ Manifold.divergence I (Manifold.mgradient I f) y • riemannianVolumeForm o y := by
    rw [wittenHessianTerm_def, LinearMap.add_apply, SmoothForm.laplacian_add_one_zero,
      SmoothForm.laplacian_add_one_zero, SmoothForm.codifferential_hodgeStar_ofFunction_const]
    simp only [map_zero, add_zero, mextDerivₗ_apply, SmoothForm.coe_gradInteriorₗ, hvol]
    exact mextDeriv_interior_riemannianVolumeForm o
      (Manifold.mdifferentiable_mgradient (f.contMDiff.of_le (by simp)))
  -- `Δf = -div grad f`.
  have hΔ := congrFun (SmoothForm.hodgeLaplacian_eq_ofFunction_neg_laplaceBeltrami o hl
    (SmoothForm.ofFunction f)) x
  have hΔ0 : (SmoothForm.hodgeLaplacian o hl (SmoothForm.ofFunction f)).val x 0 =
      -Manifold.divergence I (Manifold.mgradient I f) x := by
    simp only [hΔ, RoughForm.ofFunction_apply, Pi.neg_apply, Manifold.laplaceBeltrami_def,
      SmoothForm.ofFunction_apply_zero]
  conv_lhs => rw [hα, wittenHessianTerm_funSMulₗ, SmoothForm.coe_funSMulₗ]
  rw [hK, hΔ0, neg_neg, hα, SmoothForm.coe_funSMulₗ, hvol, smul_comm]

/-! ### Green's formulas -/

variable [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M]

/-- **The Witten codifferential is the formal adjoint of the Witten differential**: on an oriented
boundaryless Riemannian manifold, for smooth forms `α` of degree `k` and `β` of degree `k + 1`,
one of them compactly supported, `∫_M ⟨d_t α, β⟩ vol = ∫_M ⟨α, d_t^* β⟩ vol`, where `⟨·, ·⟩` is
the pointwise inner product of forms and `vol` the Riemannian volume form. -/
theorem integralTopForm_inner_wittenExtDerivₗ_eq_inner_wittenCodifferential
    (o : Manifold.Orientation I M (Fin m)) (f : C^∞⟮I, M; ℝ⟯) (t : ℝ) (hkl : k + 1 + l = m)
    (α : SmoothForm I M ℝ k) (β : SmoothForm I M ℝ (k + 1))
    (h : α ∈ compactlySupportedForms I M k ∨ β ∈ compactlySupportedForms I M (k + 1)) :
    integralTopForm o (fun x ↦ alternatingFormInner (TangentSpace I x) (k + 1)
        ((wittenExtDerivₗ f t k α).val x) (β.val x) • riemannianVolumeForm o x) =
      integralTopForm o (fun x ↦ alternatingFormInner (TangentSpace I x) k
        (α.val x) ((wittenCodifferential o f t hkl β).val x) • riemannianVolumeForm o x) := by
  -- Move `e^{-t f}` from `d (e^{t f} α)` onto `β`, use that `d^*` is the adjoint of `d`, and
  -- move `e^{t f}` from `e^{t f} α` onto `d^* (e^{-t f} β)`.
  simp_rw [wittenExtDerivₗ_def, alternatingFormInner_expSMulEquiv, wittenCodifferential_def,
    ← alternatingFormInner_expSMulEquiv f t α]
  exact SmoothForm.integralTopForm_inner_mextDeriv_eq_inner_codifferential o hkl _ _
    (h.imp (expSMulEquiv_mem_compactlySupportedForms_iff f t).2
      (expSMulEquiv_mem_compactlySupportedForms_iff f (-t)).2)

/-- **Green's formula for `d_t^* d_t`**: on an oriented boundaryless Riemannian manifold,
`∫_M ⟨d_t^* d_t α, β⟩ vol = ∫_M ⟨d_t α, d_t β⟩ vol` for smooth `k`-forms `α` and `β`, one of them
compactly supported. -/
theorem integralTopForm_inner_wittenCodifferential_wittenExtDerivₗ
    (o : Manifold.Orientation I M (Fin m)) (f : C^∞⟮I, M; ℝ⟯) (t : ℝ) (hkl : k + 1 + l = m)
    (α β : SmoothForm I M ℝ k)
    (h : α ∈ compactlySupportedForms I M k ∨ β ∈ compactlySupportedForms I M k) :
    integralTopForm o (fun x ↦ alternatingFormInner (TangentSpace I x) k
        ((wittenCodifferential o f t hkl (wittenExtDerivₗ f t k α)).val x) (β.val x) •
          riemannianVolumeForm o x) =
      integralTopForm o (fun x ↦ alternatingFormInner (TangentSpace I x) (k + 1)
        ((wittenExtDerivₗ f t k α).val x) ((wittenExtDerivₗ f t k β).val x) •
          riemannianVolumeForm o x) :=
  SmoothForm.integralTopForm_inner_codiff_diff o (wittenExtDerivₗ_mem_compactlySupportedForms f t)
    (integralTopForm_inner_wittenExtDerivₗ_eq_inner_wittenCodifferential o f t) hkl α β h

/-- **Green's formula for `d_t d_t^*`**: on an oriented boundaryless Riemannian manifold,
`∫_M ⟨d_t d_t^* α, β⟩ vol = ∫_M ⟨d_t^* α, d_t^* β⟩ vol` for smooth `(k + 1)`-forms `α` and `β`,
one of them compactly supported. -/
theorem integralTopForm_inner_wittenExtDerivₗ_wittenCodifferential
    (o : Manifold.Orientation I M (Fin m)) (f : C^∞⟮I, M; ℝ⟯) (t : ℝ) (hkl : k + 1 + l = m)
    (α β : SmoothForm I M ℝ (k + 1))
    (h : α ∈ compactlySupportedForms I M (k + 1) ∨ β ∈ compactlySupportedForms I M (k + 1)) :
    integralTopForm o (fun x ↦ alternatingFormInner (TangentSpace I x) (k + 1)
        ((wittenExtDerivₗ f t k (wittenCodifferential o f t hkl α)).val x) (β.val x) •
          riemannianVolumeForm o x) =
      integralTopForm o (fun x ↦ alternatingFormInner (TangentSpace I x) k
        ((wittenCodifferential o f t hkl α).val x) ((wittenCodifferential o f t hkl β).val x) •
          riemannianVolumeForm o x) :=
  SmoothForm.integralTopForm_inner_diff_codiff o
    (wittenCodifferential_mem_compactlySupportedForms o f t)
    (integralTopForm_inner_wittenExtDerivₗ_eq_inner_wittenCodifferential o f t) hkl α β h

/-- **The Dirichlet pairing of the Witten Laplacian**: on an oriented boundaryless Riemannian
manifold, strictly between degree `0` and the top degree,
`∫_M ⟨Δ_t α, β⟩ vol = ∫_M ⟨d_t α, d_t β⟩ vol + ∫_M ⟨d_t^* α, d_t^* β⟩ vol` for smooth forms `α`
and `β`, one of them compactly supported. -/
theorem integralTopForm_inner_wittenLaplacian_add_one_add_one
    (o : Manifold.Orientation I M (Fin m)) (f : C^∞⟮I, M; ℝ⟯) (t : ℝ)
    (hkl : k + 1 + (l + 1) = m) (α β : SmoothForm I M ℝ (k + 1))
    (h : α ∈ compactlySupportedForms I M (k + 1) ∨ β ∈ compactlySupportedForms I M (k + 1)) :
    integralTopForm o (fun x ↦ alternatingFormInner (TangentSpace I x) (k + 1)
        ((wittenLaplacian o f t hkl α).val x) (β.val x) • riemannianVolumeForm o x) =
      integralTopForm o (fun x ↦ alternatingFormInner (TangentSpace I x) (k + 1 + 1)
        ((wittenExtDerivₗ f t (k + 1) α).val x) ((wittenExtDerivₗ f t (k + 1) β).val x) •
          riemannianVolumeForm o x) +
      integralTopForm o (fun x ↦ alternatingFormInner (TangentSpace I x) k
        ((wittenCodifferential o f t hkl α).val x) ((wittenCodifferential o f t hkl β).val x) •
          riemannianVolumeForm o x) :=
  SmoothForm.integralTopForm_inner_laplacian_add_one_add_one o
    (wittenExtDerivₗ_mem_compactlySupportedForms f t)
    (wittenCodifferential_mem_compactlySupportedForms o f t)
    (integralTopForm_inner_wittenExtDerivₗ_eq_inner_wittenCodifferential o f t) hkl α β h

/-- **The Witten Laplacian is formally self-adjoint**: on an oriented boundaryless Riemannian
manifold, `∫_M ⟨Δ_t α, β⟩ vol = ∫_M ⟨α, Δ_t β⟩ vol` for smooth `k`-forms `α` and `β`, one of them
compactly supported. -/
theorem integralTopForm_inner_wittenLaplacian_eq_inner_wittenLaplacian
    (o : Manifold.Orientation I M (Fin m)) (f : C^∞⟮I, M; ℝ⟯) (t : ℝ) (hkl : k + l = m)
    (α β : SmoothForm I M ℝ k)
    (h : α ∈ compactlySupportedForms I M k ∨ β ∈ compactlySupportedForms I M k) :
    integralTopForm o (fun x ↦ alternatingFormInner (TangentSpace I x) k
        ((wittenLaplacian o f t hkl α).val x) (β.val x) • riemannianVolumeForm o x) =
      integralTopForm o (fun x ↦ alternatingFormInner (TangentSpace I x) k
        (α.val x) ((wittenLaplacian o f t hkl β).val x) • riemannianVolumeForm o x) :=
  SmoothForm.integralTopForm_inner_laplacian_eq_inner_laplacian o
    (wittenExtDerivₗ_mem_compactlySupportedForms f t)
    (wittenCodifferential_mem_compactlySupportedForms o f t)
    (integralTopForm_inner_wittenExtDerivₗ_eq_inner_wittenCodifferential o f t) hkl α β h

/-- **The Witten Laplacian is nonnegative**: on an oriented boundaryless Riemannian manifold,
`0 ≤ ∫_M ⟨Δ_t α, α⟩ vol` for every compactly supported smooth form `α`. -/
theorem integralTopForm_inner_wittenLaplacian_self_nonneg (o : Manifold.Orientation I M (Fin m))
    (f : C^∞⟮I, M; ℝ⟯) (t : ℝ) (hkl : k + l = m) {α : SmoothForm I M ℝ k}
    (hα : α ∈ compactlySupportedForms I M k) :
    0 ≤ integralTopForm o (fun x ↦ alternatingFormInner (TangentSpace I x) k
      ((wittenLaplacian o f t hkl α).val x) (α.val x) • riemannianVolumeForm o x) :=
  SmoothForm.integralTopForm_inner_laplacian_self_nonneg o
    (integralTopForm_inner_wittenExtDerivₗ_eq_inner_wittenCodifferential o f t) hkl hα

/-! ### Witten-harmonic forms -/

/-- **Witten-harmonic functions**: on an oriented boundaryless Riemannian manifold, a compactly
supported smooth function `g` satisfies `Δ_t g = 0` exactly when `d_t g = 0`. -/
theorem wittenLaplacian_eq_zero_iff_wittenExtDerivₗ_eq_zero
    (o : Manifold.Orientation I M (Fin m)) (f : C^∞⟮I, M; ℝ⟯) (t : ℝ) (hl : 0 + l = m)
    {g : SmoothForm I M ℝ 0} (hg : g ∈ compactlySupportedForms I M 0) :
    wittenLaplacian o f t hl g = 0 ↔ wittenExtDerivₗ f t 0 g = 0 :=
  SmoothForm.laplacian_eq_zero_iff_apply_eq_zero o
    (wittenExtDerivₗ_mem_compactlySupportedForms f t)
    (integralTopForm_inner_wittenExtDerivₗ_eq_inner_wittenCodifferential o f t) hl hg

/-- **Witten-harmonic forms are `d_t`-closed and `d_t^*`-closed**: on an oriented boundaryless
Riemannian manifold, a compactly supported smooth form `α` of positive degree satisfies
`Δ_t α = 0` exactly when `d_t α = 0` and `d_t^* α = 0`. -/
theorem wittenLaplacian_eq_zero_iff (o : Manifold.Orientation I M (Fin m)) (f : C^∞⟮I, M; ℝ⟯)
    (t : ℝ) (hkl : k + 1 + l = m) {α : SmoothForm I M ℝ (k + 1)}
    (hα : α ∈ compactlySupportedForms I M (k + 1)) :
    wittenLaplacian o f t hkl α = 0 ↔
      wittenExtDerivₗ f t (k + 1) α = 0 ∧ wittenCodifferential o f t hkl α = 0 :=
  SmoothForm.laplacian_eq_zero_iff o
    (wittenExtDerivₗ_mem_compactlySupportedForms f t)
    (wittenCodifferential_mem_compactlySupportedForms o f t)
    (integralTopForm_inner_wittenExtDerivₗ_eq_inner_wittenCodifferential o f t) hkl hα

omit [SigmaCompactSpace M] in
/-- **Witten-harmonic functions on a closed preconnected manifold**: on a compact preconnected
oriented boundaryless Riemannian manifold, a smooth function `g` satisfies `Δ_t g = 0` exactly when
it is a constant multiple of `e^{-t f}`. -/
theorem wittenLaplacian_eq_zero_iff_exists_eq_smul [CompactSpace M] [PreconnectedSpace M]
    (o : Manifold.Orientation I M (Fin m)) (f : C^∞⟮I, M; ℝ⟯) (t : ℝ) (hl : 0 + l = m)
    (g : SmoothForm I M ℝ 0) :
    wittenLaplacian o f t hl g = 0 ↔
      ∃ c : ℝ, g = c • expSMulEquiv 0 f (-t) (SmoothForm.ofFunction (ContMDiffMap.const 1)) :=
  (wittenLaplacian_eq_zero_iff_wittenExtDerivₗ_eq_zero o f t hl (by simp)).trans
    (wittenExtDerivₗ_apply_eq_zero_iff_exists_eq_smul g)

end TauCeti
