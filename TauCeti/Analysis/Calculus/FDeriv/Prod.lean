/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.FDeriv.Add
public import Mathlib.Analysis.Calculus.FDeriv.Prod

/-!
# Derivative lemmas on products

A function on a product `E × F` of the form `φ ∘ Prod.fst + ψ ∘ Prod.snd`, with `φ : E → G` and
`ψ : F → G`, is a *separated sum*: it depends on the two coordinates through two independent
functions. Its derivative at `(a, b)` is the coproduct `φ'.coprod ψ'` of the derivatives of the
two summands, so it vanishes exactly when both summands have vanishing derivative. This is the
first-order input for the study of critical points of separated sums, for instance of Morse
functions on a product manifold.

The derivative of a graph map `(x, y) ↦ (x, u (x, y))` can likewise be reconstructed from the
derivatives of its two coordinate slices. When the vertical slice has identity derivative, the
result is the canonical linear graph shear.

## Main declarations

* `HasFDerivAt.comp_fst_add_comp_snd`: the derivative of a separated sum is the coproduct of the
  derivatives of its summands.
* `TauCeti.fderiv_comp_fst_add_comp_snd`: the same for the totalized derivative.
* `TauCeti.fderiv_comp_fst_add_comp_snd_eq_zero_iff`: a separated sum of differentiable functions
  is critical at `(a, b)` exactly when both summands are critical at `a` and `b`.
* `TauCeti.fderiv_slice_left`, `TauCeti.fderiv_slice_right`: the derivatives of the two slices
  of a function on a product are the restrictions of its derivative.
* `TauCeti.fderiv_comp_graph_apply`: the chain rule along a graph `x ↦ f (x, u x)`.
* `HasFDerivAt.fderiv_comp_graph_eq_fderiv_slice_of_fderiv_right_eq_zero`: along a differentiable
  graph through a spatial critical point, only the parameter derivative contributes.
* `DifferentiableAt.hasFDerivAt_fst_prodMk_of_slices`: the derivative of a graph map from its
  horizontal derivative and its vertical identity derivative.
-/

public section

namespace TauCeti

variable {𝕜 E F G : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F] [NormedAddCommGroup G] [NormedSpace 𝕜 G]
  {φ : E → G} {ψ : F → G} {φ' : E →L[𝕜] G} {ψ' : F →L[𝕜] G} {a : E} {b : F}

/-- The derivative of a separated sum `φ ∘ Prod.fst + ψ ∘ Prod.snd` at `(a, b)` is the coproduct
of the derivatives of `φ` at `a` and of `ψ` at `b`. -/
theorem _root_.HasFDerivAt.comp_fst_add_comp_snd (hφ : HasFDerivAt φ φ' a)
    (hψ : HasFDerivAt ψ ψ' b) :
    HasFDerivAt (φ ∘ Prod.fst + ψ ∘ Prod.snd) (φ'.coprod ψ') (a, b) := by
  have h := (hφ.comp (a, b) (hasFDerivAt_fst (𝕜 := 𝕜) (p := (a, b)))).add
    (hψ.comp (a, b) (hasFDerivAt_snd (𝕜 := 𝕜) (p := (a, b))))
  rwa [ContinuousLinearMap.comp_fst_add_comp_snd] at h

/-- The totalized derivative of a separated sum of differentiable functions is the coproduct of
the derivatives of its summands. -/
@[simp]
theorem fderiv_comp_fst_add_comp_snd (hφ : DifferentiableAt 𝕜 φ a) (hψ : DifferentiableAt 𝕜 ψ b) :
    fderiv 𝕜 (φ ∘ Prod.fst + ψ ∘ Prod.snd) (a, b) = (fderiv 𝕜 φ a).coprod (fderiv 𝕜 ψ b) :=
  (hφ.hasFDerivAt.comp_fst_add_comp_snd hψ.hasFDerivAt).fderiv

/-- A separated sum of differentiable functions is critical at `(a, b)` exactly when both
summands are critical at `a` and at `b`. This is not a `simp` lemma: the `@[simp]` lemma
`TauCeti.fderiv_comp_fst_add_comp_snd` already rewrites its left-hand side to
`(fderiv 𝕜 φ a).coprod (fderiv 𝕜 ψ b) = 0`. -/
theorem fderiv_comp_fst_add_comp_snd_eq_zero_iff (hφ : DifferentiableAt 𝕜 φ a)
    (hψ : DifferentiableAt 𝕜 ψ b) :
    fderiv 𝕜 (φ ∘ Prod.fst + ψ ∘ Prod.snd) (a, b) = 0 ↔
      fderiv 𝕜 φ a = 0 ∧ fderiv 𝕜 ψ b = 0 := by
  rw [fderiv_comp_fst_add_comp_snd hφ hψ]
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · ext v
      simpa using congrArg (fun L : E × F →L[𝕜] G ↦ L (v, 0)) h
    · ext w
      simpa using congrArg (fun L : E × F →L[𝕜] G ↦ L (0, w)) h
  · rintro ⟨h₁, h₂⟩
    rw [h₁, h₂]
    ext <;> simp

/-- The derivative of the first-variable slice `fun x ↦ f (x, b)` is the derivative of `f`
restricted to the first factor. -/
theorem fderiv_slice_left {f : E × F → G} (hf : DifferentiableAt 𝕜 f (a, b)) :
    fderiv 𝕜 (fun x ↦ f (x, b)) a = (fderiv 𝕜 f (a, b)).comp (ContinuousLinearMap.inl 𝕜 E F) :=
  (hf.hasFDerivAt.comp a (hasFDerivAt_prodMk_left a b)).fderiv

/-- The derivative of the second-variable slice `fun y ↦ f (a, y)` is the derivative of `f`
restricted to the second factor. -/
theorem fderiv_slice_right {f : E × F → G} (hf : DifferentiableAt 𝕜 f (a, b)) :
    fderiv 𝕜 (fun y ↦ f (a, y)) b = (fderiv 𝕜 f (a, b)).comp (ContinuousLinearMap.inr 𝕜 E F) :=
  (hf.hasFDerivAt.comp b (hasFDerivAt_prodMk_right a b)).fderiv

/-- **The chain rule along a graph.** The derivative of `fun x ↦ f (x, u x)` is the derivative of
`f` in the first variable plus its derivative in the second variable applied to the derivative
of `u`. -/
theorem fderiv_comp_graph_apply {u : E → F} {f : E × F → G} (hu : DifferentiableAt 𝕜 u a)
    (hf : DifferentiableAt 𝕜 f (a, u a)) (v : E) :
    fderiv 𝕜 (fun x ↦ f (x, u x)) a v =
      fderiv 𝕜 f (a, u a) (v, 0) + fderiv 𝕜 (fun y ↦ f (a, y)) (u a) (fderiv 𝕜 u a v) := by
  have h : HasFDerivAt (fun x ↦ f (x, u x))
      ((fderiv 𝕜 f (a, u a)).comp ((ContinuousLinearMap.id 𝕜 E).prod (fderiv 𝕜 u a))) a :=
    hf.hasFDerivAt.comp a ((hasFDerivAt_id a).prodMk hu.hasFDerivAt)
  rw [h.fderiv, fderiv_slice_right hf, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.comp_apply, ← map_add]
  simp

/-- Along a differentiable graph through a point where the derivative in the second variable
vanishes, the derivative of a function on a product equals the derivative of its first-variable
slice. -/
theorem _root_.HasFDerivAt.fderiv_comp_graph_eq_fderiv_slice_of_fderiv_right_eq_zero
    {u : E → F} {f : E × F → G} {f' : E × F →L[𝕜] G}
    (hf : HasFDerivAt f f' (a, u a)) (hu : DifferentiableAt 𝕜 u a)
    (hzero : fderiv 𝕜 (fun y ↦ f (a, y)) (u a) = 0) :
    fderiv 𝕜 (fun x ↦ f (x, u x)) a = fderiv 𝕜 (fun x ↦ f (x, u a)) a := by
  ext v
  rw [fderiv_comp_graph_apply hu hf.differentiableAt v, hzero,
    fderiv_slice_left hf.differentiableAt]
  simp

/-- If a differentiable function on a product has horizontal slice derivative `A` and vertical
slice derivative the identity, then its graph map has derivative the canonical shear by `A`. -/
theorem _root_.DifferentiableAt.hasFDerivAt_fst_prodMk_of_slices
    {u : E × F → F} {A : E →L[𝕜] F}
    (hu : DifferentiableAt 𝕜 u (a, b))
    (hx : HasFDerivAt (fun x ↦ u (x, b)) A a)
    (hy : HasFDerivAt (fun y ↦ u (a, y)) (ContinuousLinearMap.id 𝕜 F) b) :
    HasFDerivAt (fun p : E × F ↦ (p.1, u p))
      ((ContinuousLinearEquiv.refl 𝕜 E).skewProd
        (ContinuousLinearEquiv.refl 𝕜 F) A : (E × F) →L[𝕜] (E × F))
      (a, b) := by
  have huDeriv := hu.hasFDerivAt
  have hx' (v : E) : fderiv 𝕜 u (a, b) (v, 0) = A v := by
    have hcomp := huDeriv.comp a (hasFDerivAt_prodMk_left (𝕜 := 𝕜) a b)
    have heq := hcomp.unique hx
    simpa using congrArg (fun L : E →L[𝕜] F ↦ L v) heq
  have hy' (w : F) : fderiv 𝕜 u (a, b) (0, w) = w := by
    have hcomp := huDeriv.comp b (hasFDerivAt_prodMk_right (𝕜 := 𝕜) a b)
    have heq := hcomp.unique hy
    simpa using congrArg (fun L : F →L[𝕜] F ↦ L w) heq
  have htotal (q : E × F) : fderiv 𝕜 u (a, b) q = A q.1 + q.2 := by
    calc
      fderiv 𝕜 u (a, b) q =
          fderiv 𝕜 u (a, b) (q.1, 0) + fderiv 𝕜 u (a, b) (0, q.2) := by
            rw [← map_add]
            congr 2
            ext <;> simp
      _ = A q.1 + q.2 := by rw [hx', hy']
  have hderiv := hasFDerivAt_fst.prodMk huDeriv
  convert hderiv using 1
  apply ContinuousLinearMap.ext
  intro q
  simpa [add_comm] using congrArg (fun z : F ↦ (q.1, z)) (htotal q).symm

end TauCeti

end
