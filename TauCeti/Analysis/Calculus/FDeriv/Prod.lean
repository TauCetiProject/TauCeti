/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.Calculus.FDeriv.Add
public import Mathlib.Analysis.Calculus.FDeriv.Prod

import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.FDeriv.CompCLM
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.TangentCone.Prod

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

For a function of a scalar first variable, the partial derivatives along the coordinate lines
`s ↦ (s, b)` and `t ↦ (a, t)` are its derivative applied to `(1, 0)` and `(0, 1)`. The same holds
one order higher for the first derivative, and more generally along any line `r ↦ p + r • q`.
A function whose partial derivative in the first variable vanishes everywhere is constant along
every horizontal line.

## Main declarations

* `HasFDerivAt.comp_fst_add_comp_snd`: the derivative of a separated sum is the coproduct of the
  derivatives of its summands.
* `TauCeti.hasDerivAt_prodMk_left`, `TauCeti.hasDerivAt_prodMk_right`: the coordinate lines
  through a point have velocities `(1, 0)` and `(0, 1)`.
* `TauCeti.hasDerivAt_fderiv_apply_fst`, `TauCeti.hasDerivAt_fderiv_apply_snd`: the partial
  derivatives of a first partial derivative.
* `TauCeti.hasDerivAt_fderiv_apply_line`: the derivative of a first derivative along a line.
* `TauCeti.apply_eq_apply_zero_of_fderiv_fst_eq_zero`: a function with vanishing partial
  derivative in its real first variable is constant along horizontal lines.
* `TauCeti.fderiv_comp_fst_add_comp_snd`: the same for the totalized derivative.
* `TauCeti.fderiv_comp_fst_add_comp_snd_eq_zero_iff`: a separated sum of differentiable functions
  is critical at `(a, b)` exactly when both summands are critical at `a` and `b`.
* `TauCeti.fderiv_slice_left`, `TauCeti.fderiv_slice_right`: the derivatives of the two slices
  of a function on a product are the restrictions of its derivative.
* `TauCeti.fderiv_comp_snd_apply_mk_zero`: a function of the second variable alone has zero
  derivative along the first factor.
* `TauCeti.fderiv_apply_eq_fderiv_slice_left_add_fderiv_slice_right`: the derivative of a function
  on a product is the sum of the derivatives of its two slices.
* `TauCeti.hasDerivAt_slice_left`, `TauCeti.hasDerivAt_slice_right`: the partial derivatives of
  a function in a scalar first or second variable are its derivative applied to `(1, 0)` and
  `(0, 1)`.
* `TauCeti.fderiv_apply_mk_one_zero`: the derivative of a function in a scalar first variable,
  applied to `(1, 0)`, is the derivative of its first-variable slice.
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

/-- The derivative of a function on a product is the sum of the derivatives of its two slices,
applied to the two components of the direction. -/
theorem fderiv_apply_eq_fderiv_slice_left_add_fderiv_slice_right {f : E × F → G}
    (hf : DifferentiableAt 𝕜 f (a, b)) (w : E × F) :
    fderiv 𝕜 f (a, b) w =
      fderiv 𝕜 (fun x ↦ f (x, b)) a w.1 + fderiv 𝕜 (fun y ↦ f (a, y)) b w.2 := by
  rw [fderiv_slice_left hf, fderiv_slice_right hf]
  simp only [ContinuousLinearMap.coe_comp, Function.comp_apply, ContinuousLinearMap.inl_apply,
    ContinuousLinearMap.inr_apply, ← map_add, Prod.mk_add_mk, add_zero, zero_add]

/-- A function of the second variable alone has zero derivative along the first factor. No
differentiability is needed: otherwise the derivative is zero. -/
theorem fderiv_comp_snd_apply_mk_zero (f : F → G) (z : E × F) (v : E) :
    fderiv 𝕜 (fun w : E × F ↦ f w.2) z (v, 0) = 0 := by
  by_cases hf : DifferentiableAt 𝕜 f z.2
  · have h : HasFDerivAt (fun w : E × F ↦ f w.2)
        ((fderiv 𝕜 f z.2).comp (ContinuousLinearMap.snd 𝕜 E F)) z :=
      hf.hasFDerivAt.comp z hasFDerivAt_snd
    simp [h.fderiv]
  · have hf' : ¬DifferentiableAt 𝕜 (fun w : E × F ↦ f w.2) z := by
      intro h
      have h' : DifferentiableAt 𝕜 (fun w : E × F ↦ f w.2) (z.1, z.2) := h
      exact hf (h'.comp z.2 (hasFDerivAt_prodMk_right (𝕜 := 𝕜) z.1 z.2).differentiableAt)
    simp [fderiv_zero_of_not_differentiableAt hf']

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

section CoordinateLines

variable {u : 𝕜 × F → G}

/-- The horizontal line `s ↦ (s, b)` has velocity `(1, 0)`. -/
theorem hasDerivAt_prodMk_left (s : 𝕜) (b : F) :
    HasDerivAt (fun s : 𝕜 ↦ (s, b)) ((1 : 𝕜), (0 : F)) s :=
  (hasDerivAt_id s).prodMk (hasDerivAt_const s b)

/-- The vertical line `t ↦ (a, t)` has velocity `(0, 1)`. -/
theorem hasDerivAt_prodMk_right (a : E) (t : 𝕜) :
    HasDerivAt (fun t : 𝕜 ↦ (a, t)) ((0 : E), (1 : 𝕜)) t :=
  (hasDerivAt_const t a).prodMk (hasDerivAt_id t)

/-- Where `u` is differentiable, its partial derivative in the first variable is its derivative
applied to `(1, 0)`. -/
theorem hasDerivAt_slice_left {s : 𝕜} {b : F} (hu : DifferentiableAt 𝕜 u (s, b)) :
    HasDerivAt (fun s ↦ u (s, b)) (fderiv 𝕜 u (s, b) (1, 0)) s :=
  hu.hasFDerivAt.comp_hasDerivAt s (hasDerivAt_prodMk_left s b)

/-- Where `u` is differentiable, its derivative applied to `(1, 0)` is its partial derivative in
the first variable. -/
theorem fderiv_apply_mk_one_zero {z : 𝕜 × F} (hu : DifferentiableAt 𝕜 u z) :
    fderiv 𝕜 u z (1, 0) = deriv (fun s ↦ u (s, z.2)) z.1 :=
  (hasDerivAt_slice_left (s := z.1) (b := z.2) hu).deriv.symm

/-- The derivative in the first variable of a first partial derivative `fderiv 𝕜 u · v` is the
second derivative of `u` in the direction `(1, 0)`. -/
theorem hasDerivAt_fderiv_apply_fst {s : 𝕜} {b : F} (hu : DifferentiableAt 𝕜 (fderiv 𝕜 u) (s, b))
    (v : 𝕜 × F) :
    HasDerivAt (fun s ↦ fderiv 𝕜 u (s, b) v) (fderiv 𝕜 (fderiv 𝕜 u) (s, b) (1, 0) v) s := by
  simpa [Function.comp_def] using
    (hu.hasFDerivAt.clm_apply (hasFDerivAt_const v _)).comp_hasDerivAt s
      (hasDerivAt_prodMk_left s b)

end CoordinateLines

/-- Where `u` is differentiable, its partial derivative in the second variable is its derivative
applied to `(0, 1)`. -/
theorem hasDerivAt_slice_right {u : E × 𝕜 → G} {a : E} {t : 𝕜}
    (hu : DifferentiableAt 𝕜 u (a, t)) :
    HasDerivAt (fun t ↦ u (a, t)) (fderiv 𝕜 u (a, t) (0, 1)) t :=
  hu.hasFDerivAt.comp_hasDerivAt t (hasDerivAt_prodMk_right a t)

/-- The derivative in the second variable of a first partial derivative `fderiv 𝕜 u · v` is the
second derivative of `u` in the direction `(0, 1)`. -/
theorem hasDerivAt_fderiv_apply_snd {u : E × 𝕜 → G} {a : E} {t : 𝕜}
    (hu : DifferentiableAt 𝕜 (fderiv 𝕜 u) (a, t)) (v : E × 𝕜) :
    HasDerivAt (fun t ↦ fderiv 𝕜 u (a, t) v) (fderiv 𝕜 (fderiv 𝕜 u) (a, t) (0, 1) v) t := by
  simpa [Function.comp_def] using
    (hu.hasFDerivAt.clm_apply (hasFDerivAt_const v _)).comp_hasDerivAt t
      (hasDerivAt_prodMk_right a t)

/-- The derivative along the line `r ↦ p + r • q` of a first derivative `fderiv 𝕜 u · v` is the
second derivative `fderiv 𝕜 (fderiv 𝕜 u) (p + s • q)` applied to `q` and then `v`, i.e. the
derivative in the direction `q` of `fderiv 𝕜 u · v`. -/
theorem hasDerivAt_fderiv_apply_line {u : E → G} {p q : E} {s : 𝕜}
    (hu : DifferentiableAt 𝕜 (fderiv 𝕜 u) (p + s • q)) (v : E) :
    HasDerivAt (fun r ↦ fderiv 𝕜 u (p + r • q) v) (fderiv 𝕜 (fderiv 𝕜 u) (p + s • q) q v) s := by
  have hline : HasDerivAt (fun r : 𝕜 ↦ p + r • q) q s := by
    simpa only [id_eq, one_smul] using ((hasDerivAt_id s).smul_const q).const_add p
  simpa [Function.comp_def] using
    (hu.hasFDerivAt.clm_apply (hasFDerivAt_const v _)).comp_hasDerivAt s hline

/-- A differentiable function on `ℝ × F` whose partial derivative in the first variable vanishes
everywhere is constant along every horizontal line. -/
theorem apply_eq_apply_zero_of_fderiv_fst_eq_zero {F G : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G] {u : ℝ × F → G}
    (hu : Differentiable ℝ u) (h : ∀ z, fderiv ℝ u z (1, 0) = 0) (s : ℝ) (b : F) :
    u (s, b) = u (0, b) := by
  have hl (s : ℝ) : HasDerivAt (fun s ↦ u (s, b)) 0 s := by
    simpa [h] using hasDerivAt_slice_left (hu (s, b))
  exact is_const_of_deriv_eq_zero (fun s ↦ (hl s).differentiableAt) (fun s ↦ (hl s).deriv) s 0

section FstClmApplySnd

open Set

variable {X Y V W : Type*} [NormedAddCommGroup X] [NormedSpace 𝕜 X] [NormedAddCommGroup Y]
  [NormedSpace 𝕜 Y] [NormedAddCommGroup V] [NormedSpace 𝕜 V] [NormedAddCommGroup W]
  [NormedSpace 𝕜 W]

/-- The derivative within `s ×ˢ univ` of `a ↦ (F a.1, C a.1 a.2)` at `(a₀, v)`, evaluated at
`(h, w)`, for `F : X → Y` and `C : X → V →L[𝕜] W` differentiable within `s` at `a₀`, is
`(DF h, DC h v + C a₀ w)`. -/
theorem fderivWithin_prodMk_fst_clm_apply_snd {s : Set X} {a₀ : X} {F : X → Y}
    {C : X → V →L[𝕜] W} (hF : DifferentiableWithinAt 𝕜 F s a₀)
    (hC : DifferentiableWithinAt 𝕜 C s a₀) (hs : UniqueDiffWithinAt 𝕜 s a₀) {v : V} (h : X)
    (w : V) :
    (fderivWithin 𝕜 (fun a : X × V ↦ (F a.1, C a.1 a.2)) (s ×ˢ univ) (a₀, v)) (h, w) =
      (fderivWithin 𝕜 F s a₀ h, fderivWithin 𝕜 C s a₀ h v + C a₀ w) := by
  have hmaps : MapsTo (Prod.fst : X × V → X) (s ×ˢ univ) s := fun _ hx ↦ hx.1
  have huniq : UniqueDiffWithinAt 𝕜 (s ×ˢ univ) (a₀, v) :=
    hs.prod uniqueDiffWithinAt_univ
  -- The calculus lemmas below are stated for explicit compositions with the two projections.
  -- The `change` steps only eta-expand those compositions and their derivatives.
  have hFp : DifferentiableWithinAt 𝕜 (fun a : X × V ↦ F a.1) (s ×ˢ univ) (a₀, v) := by
    change DifferentiableWithinAt 𝕜 (F ∘ Prod.fst) (s ×ˢ univ) (a₀, v)
    exact hF.comp (a₀, v) differentiableWithinAt_fst hmaps
  have hCp : DifferentiableWithinAt 𝕜 (fun a : X × V ↦ C a.1) (s ×ˢ univ) (a₀, v) := by
    change DifferentiableWithinAt 𝕜 (C ∘ Prod.fst) (s ×ˢ univ) (a₀, v)
    exact hC.comp (a₀, v) differentiableWithinAt_fst hmaps
  have hAp : DifferentiableWithinAt 𝕜 (fun a : X × V ↦ C a.1 a.2) (s ×ˢ univ) (a₀, v) :=
    hCp.clm_apply differentiableWithinAt_snd
  have hFp_eq := fderivWithin_comp (a₀, v) hF differentiableWithinAt_fst hmaps huniq
  change fderivWithin 𝕜 (fun a : X × V ↦ F a.1) (s ×ˢ univ) (a₀, v) = _ at hFp_eq
  have hCp_eq := fderivWithin_comp (a₀, v) hC differentiableWithinAt_fst hmaps huniq
  change fderivWithin 𝕜 (fun a : X × V ↦ C a.1) (s ×ˢ univ) (a₀, v) = _ at hCp_eq
  have hAp_eq := fderivWithin_clm_apply huniq hCp differentiableWithinAt_snd
  change fderivWithin 𝕜 (fun a : X × V ↦ C a.1 a.2) (s ×ˢ univ) (a₀, v) = _ at hAp_eq
  have hfst_app : (fderivWithin 𝕜 (Prod.fst : X × V → X) (s ×ˢ univ) (a₀, v)) (h, w) = h := by
    rw [fderivWithin_fst huniq]
    rfl
  have hsnd_app : (fderivWithin 𝕜 (Prod.snd : X × V → V) (s ×ˢ univ) (a₀, v)) (h, w) = w := by
    rw [fderivWithin_snd huniq]
    rfl
  rw [hFp.fderivWithin_prodMk hAp huniq, ContinuousLinearMap.prod_apply, hFp_eq,
    hAp_eq, hCp_eq]
  simp only [ContinuousLinearMap.comp_apply, add_apply, ContinuousLinearMap.flip_apply]
  rw [hfst_app, hsnd_app, add_comm]

end FstClmApplySnd

end TauCeti

end
