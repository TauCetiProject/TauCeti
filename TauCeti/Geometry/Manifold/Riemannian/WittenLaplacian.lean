/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.DeRham.Witten
public import TauCeti.Geometry.Manifold.Riemannian.Codifferential

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
`d_t = d + t df ∧ ·` it is a local operator,
`d_t^* β = d^* β + t (-1) ^ (m (k + 2)) ⋆(df ∧ ⋆β)` on `(k + 1)`-forms
(`TauCeti.wittenCodifferential_eq_add_smul`).

The **Witten Laplacian** `Δ_t = d_t^* d_t + d_t d_t^*` (`TauCeti.wittenLaplacian`, with only
`d_t^* d_t` in degree `0` and only `d_t d_t^*` in the top degree) is, for a Morse function `f`, the
operator whose low-lying spectrum concentrates near the critical points of `f` as `t → ∞`; this
is how Witten compares de Rham cohomology with the Morse complex. Unlike `d_t` and `d_t^*`, it is
not conjugate to the Hodge Laplacian, since the two conjugations go in opposite directions;
classically `Δ_t = Δ + t K + t² |df|²` with `K` a zeroth-order operator built from the Hessian
of `f`, a formula not proved here. At `t = 0` it is the Hodge Laplacian
(`TauCeti.wittenLaplacian_zero`).

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

## Main results

* `TauCeti.integralTopForm_inner_wittenExtDerivₗ_eq_inner_wittenCodifferential`: `d_t^*` is the
  formal adjoint of `d_t`.
* `TauCeti.wittenCodifferential_comp_wittenCodifferential`: `d_t^* ∘ d_t^* = 0`.
* `TauCeti.wittenCodifferential_eq_smul_hodgeStar`: `d_t^* = (-1) ^ (m (k + 2) + 1) ⋆ d_{-t} ⋆`.
* `TauCeti.wittenCodifferential_eq_add_smul`: `d_t^* β = d^* β + t (-1) ^ (m (k + 2)) ⋆(df ∧ ⋆β)`.
* `TauCeti.wittenLaplacian_zero`: at `t = 0` the Witten Laplacian is the Hodge Laplacian.
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
  Section 2 (the deformed differential `d_t`, its adjoint `d_t^*` and the Laplacian
  `d_t d_t^* + d_t^* d_t`).
* H. L. Cycon, R. G. Froese, W. Kirsch and B. Simon, *Schrödinger Operators*, Springer, 1987,
  Chapter 11 (Witten's proof of the Morse inequalities).
-/

public section

noncomputable section

open Bundle Set
open scoped Manifold ContDiff

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
    alternatingFormInner (TangentSpace I x) k ((expSMulEquiv k f t α).1 x) (β.1 x) =
      alternatingFormInner (TangentSpace I x) k (α.1 x) ((expSMulEquiv k f t β).1 x) := by
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
`d_t^* β = d^* β + t (-1) ^ (m (k + 2)) ⋆(df ∧ ⋆β)`** on `(k + 1)`-forms, where `df` is the
exterior derivative of the smooth `0`-form of `f` and the degree `0 + 1 + l` of the wedge is
transported to `l + 1`. Classically the zeroth-order operator `(-1) ^ (m (k + 2)) ⋆(df ∧ ⋆·)` is the
pointwise adjoint of `df ∧ ·`, the contraction with the gradient of `f`; that identification is
not proved here. -/
theorem wittenCodifferential_eq_add_smul (o : Manifold.Orientation I M (Fin m))
    (f : C^∞⟮I, M; ℝ⟯) (t : ℝ) (hkl : k + 1 + l = m) (hlk : l + 1 + k = m)
    (β : SmoothForm I M ℝ (k + 1)) :
    wittenCodifferential o f t hkl β =
      SmoothForm.codifferential o hkl β + (t * (-1 : ℝ) ^ (m * (k + 2))) •
        SmoothForm.hodgeStar o hlk (LinearEquiv.cast (R := ℝ)
          (M := fun q : ℕ ↦ SmoothForm I M ℝ q) (show 0 + 1 + l = l + 1 by omega)
            (SmoothForm.wedge (mextDerivₗ I 0 (SmoothForm.ofFunction f))
              (SmoothForm.hodgeStar o hkl β))) := by
  rw [wittenCodifferential_eq_smul_hodgeStar o f t hkl hlk, wittenExtDerivₗ_eq_add_smul, map_add,
    map_smul, smul_add, ← SmoothForm.codifferential_apply o hkl hlk, smul_smul, pow_succ]
  congr 2
  ring

/-- The Witten codifferential does not enlarge supports. -/
theorem tsupport_wittenCodifferential_subset (o : Manifold.Orientation I M (Fin m))
    (f : C^∞⟮I, M; ℝ⟯) (t : ℝ) (hkl : k + 1 + l = m) (β : SmoothForm I M ℝ (k + 1)) :
    _root_.tsupport (α := E [⋀^Fin k]→L[ℝ] ℝ) (wittenCodifferential o f t hkl β).1 ⊆
      _root_.tsupport (α := E [⋀^Fin (k + 1)]→L[ℝ] ℝ) β.1 := by
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
    _root_.tsupport (α := E [⋀^Fin k]→L[ℝ] ℝ) (wittenLaplacian o f t hkl α).1 ⊆
      _root_.tsupport (α := E [⋀^Fin k]→L[ℝ] ℝ) α.1 :=
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
        ((wittenExtDerivₗ f t k α).1 x) (β.1 x) • riemannianVolumeForm o x) =
      integralTopForm o (fun x ↦ alternatingFormInner (TangentSpace I x) k
        (α.1 x) ((wittenCodifferential o f t hkl β).1 x) • riemannianVolumeForm o x) := by
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
        ((wittenCodifferential o f t hkl (wittenExtDerivₗ f t k α)).1 x) (β.1 x) •
          riemannianVolumeForm o x) =
      integralTopForm o (fun x ↦ alternatingFormInner (TangentSpace I x) (k + 1)
        ((wittenExtDerivₗ f t k α).1 x) ((wittenExtDerivₗ f t k β).1 x) •
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
        ((wittenExtDerivₗ f t k (wittenCodifferential o f t hkl α)).1 x) (β.1 x) •
          riemannianVolumeForm o x) =
      integralTopForm o (fun x ↦ alternatingFormInner (TangentSpace I x) k
        ((wittenCodifferential o f t hkl α).1 x) ((wittenCodifferential o f t hkl β).1 x) •
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
        ((wittenLaplacian o f t hkl α).1 x) (β.1 x) • riemannianVolumeForm o x) =
      integralTopForm o (fun x ↦ alternatingFormInner (TangentSpace I x) (k + 1 + 1)
        ((wittenExtDerivₗ f t (k + 1) α).1 x) ((wittenExtDerivₗ f t (k + 1) β).1 x) •
          riemannianVolumeForm o x) +
      integralTopForm o (fun x ↦ alternatingFormInner (TangentSpace I x) k
        ((wittenCodifferential o f t hkl α).1 x) ((wittenCodifferential o f t hkl β).1 x) •
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
        ((wittenLaplacian o f t hkl α).1 x) (β.1 x) • riemannianVolumeForm o x) =
      integralTopForm o (fun x ↦ alternatingFormInner (TangentSpace I x) k
        (α.1 x) ((wittenLaplacian o f t hkl β).1 x) • riemannianVolumeForm o x) :=
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
      ((wittenLaplacian o f t hkl α).1 x) (α.1 x) • riemannianVolumeForm o x) :=
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
