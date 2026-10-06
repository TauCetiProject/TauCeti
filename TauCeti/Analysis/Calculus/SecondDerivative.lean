/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Comp
public import Mathlib.Analysis.Calculus.FDeriv.Equiv
public import Mathlib.Analysis.Calculus.FDeriv.Symmetric
public import Mathlib.Topology.Algebra.Module.Spaces.ContinuousLinearMap
public import TauCeti.Analysis.Calculus.FDeriv.Prod
import TauCeti.Analysis.Calculus.FDeriv.ContinuousLinearMap

/-!
# The second derivative as a derivative

The second derivative `fderiv 𝕜 (fderiv 𝕜 g) x` of a map between normed spaces is, by definition,
the derivative at `x` of the map `fderiv 𝕜 g`. Mathlib supplies the differentiability of
`fderiv 𝕜 g` at a twice continuously differentiable point through `ContDiffAt.fderiv_right`; this
file packages that into the single `HasFDerivAt` statement that second-order arguments use, so
that the identification is made once rather than at each use.

An invertible second derivative therefore lets the differential avoid any prescribed value `c`
on some punctured neighbourhood of the point, the neighbourhood being allowed to depend on `c`.
That fixed-value avoidance is the local rigidity behind the isolation of nondegenerate critical
points, and it asks nothing of the value taken.

The file also records that on an open set the second directional derivative
`x ↦ D(Dg(·) v)(x) v` of a `C²` map is continuous, and the second-order chain rule
`D²(f ∘ φ)(v, w) = D²f(Dφ v, Dφ w) + Df(D²φ(v, w))`. At a point where the differential of the outer
function vanishes the first-order term drops out, so the second derivative of a composition is the
second derivative of the outer function evaluated on the images of the differential of the inner
one, i.e. the second derivative transforms as a bilinear form. The second derivative of a
separated sum `φ ∘ Prod.fst + ψ ∘ Prod.snd` on a product is the block-diagonal map built from the
second derivatives of the summands. Finally, the second derivative of a directional derivative
`y ↦ Dg(y) v` is the third derivative of `g` evaluated at `v`, and differentiating the symmetry
of the second derivative shows that the third derivative is symmetric in its last two
directions. No statement
here mentions critical points as such, so all of them belong here rather than with the Morse theory
that uses them.

## Main results

* `ContDiffAt.hasFDerivAt_fderiv`: at a twice continuously differentiable point,
  `fderiv 𝕜 g` is differentiable, with derivative the second derivative of `g`.
* `ContDiffOn.continuousOn_fderiv_fderiv_apply`: on an open set, the second directional
  derivative of a `C²` map in a fixed direction is continuous.
* `TauCeti.eventually_fderiv_ne`: where the second derivative is invertible, the differential
  avoids any prescribed value on a punctured neighbourhood of the point.
* `TauCeti.fderiv_fderiv_comp_apply`: the second-order chain rule for `C²` maps.
* `TauCeti.fderiv_fderiv_comp_apply_of_fderiv_eq_zero`: for `C²` maps, where the differential of
  the outer function vanishes, the second derivative of a composition is the pullback of the
  second derivative along the differential of the inner function.
* `TauCeti.fderiv_fderiv_comp_fst_add_comp_snd`: the second derivative of a separated sum on a
  product is block diagonal.
* `TauCeti.fderiv_fderiv_fderiv_apply`: the second derivative of a directional derivative of a
  `C³` map is its third derivative.
* `TauCeti.fderiv_fderiv_fderiv_apply_comm`: the third derivative of a sufficiently smooth map is
  symmetric in its last two directions.
-/

public section

open Filter Topology

namespace TauCeti

variable {𝕜 E F G : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F] [NormedAddCommGroup G] [NormedSpace 𝕜 G]

/-- At a twice continuously differentiable point, `fderiv 𝕜 g` is differentiable, with derivative
the second derivative of `g`. -/
theorem _root_.ContDiffAt.hasFDerivAt_fderiv {n : WithTop ℕ∞} {g : E → F} {x : E}
    (h : ContDiffAt 𝕜 n g x) (hn : 2 ≤ n) :
    HasFDerivAt (fderiv 𝕜 g) (fderiv 𝕜 (fderiv 𝕜 g) x) x :=
  ((h.fderiv_right (m := 1) (by exact_mod_cast hn)).differentiableAt one_ne_zero).hasFDerivAt

/-- On an open set `s`, the second directional derivative `x ↦ D(Dg(·) v)(x) v` of a `C²` map `g`
in a fixed direction `v` is continuous. -/
theorem _root_.ContDiffOn.continuousOn_fderiv_fderiv_apply {g : E → F} {s : Set E}
    (hg : ContDiffOn 𝕜 2 g s) (hs : IsOpen s) (v : E) :
    ContinuousOn (fun x ↦ fderiv 𝕜 (fun y ↦ fderiv 𝕜 g y v) x v) s :=
  (((hg.fderiv_of_isOpen hs (by norm_num)).clm_apply contDiffOn_const).continuousOn_fderiv_of_isOpen
    hs le_rfl).clm_apply continuousOn_const

/-- **Where the second derivative is invertible, the differential avoids any prescribed value near
the point.** Nothing is assumed about the value `c`, and in particular the differential need not
vanish at `x`. The punctured neighbourhood on which `c` is avoided may depend on `c`, so this is
avoidance of one fixed value rather than local injectivity of `fderiv 𝕜 g`. -/
theorem eventually_fderiv_ne {g : E → F} {x : E} {c : E →L[𝕜] F} (hg : ContDiffAt 𝕜 2 g x)
    (hinv : (fderiv 𝕜 (fderiv 𝕜 g) x).IsInvertible) :
    ∀ᶠ y in 𝓝[≠] x, fderiv 𝕜 g y ≠ c := by
  obtain ⟨e, he⟩ := hinv
  have hd : HasFDerivAt (fderiv 𝕜 g) (e : E →L[𝕜] E →L[𝕜] F) x := by
    rw [he]
    exact ContDiffAt.hasFDerivAt_fderiv hg le_rfl
  exact hd.eventually_ne ⟨_, e.antilipschitz⟩

/-- **The second-order chain rule.** If `f` is `C²` at `φ b` and `φ` is `C²` at `b`, then the
second derivative of `f ∘ φ` at `b` is `D²f(φ b)(Dφ v, Dφ w) + Df(φ b)(D²φ(v, w))`. -/
theorem fderiv_fderiv_comp_apply {f : E → G} {φ : F → E} {b : F}
    (hf : ContDiffAt 𝕜 2 f (φ b)) (hφ : ContDiffAt 𝕜 2 φ b) (v w : F) :
    fderiv 𝕜 (fderiv 𝕜 (f ∘ φ)) b v w =
      fderiv 𝕜 (fderiv 𝕜 f) (φ b) (fderiv 𝕜 φ b v) (fderiv 𝕜 φ b w) +
        fderiv 𝕜 f (φ b) (fderiv 𝕜 (fderiv 𝕜 φ) b v w) := by
  have hf1 : HasFDerivAt (fderiv 𝕜 f) (fderiv 𝕜 (fderiv 𝕜 f) (φ b)) (φ b) :=
    ContDiffAt.hasFDerivAt_fderiv hf le_rfl
  have hφ1 : HasFDerivAt (fderiv 𝕜 φ) (fderiv 𝕜 (fderiv 𝕜 φ) b) b :=
    ContDiffAt.hasFDerivAt_fderiv hφ le_rfl
  have hφ0 : HasFDerivAt φ (fderiv 𝕜 φ b) b := (hφ.differentiableAt (by norm_num)).hasFDerivAt
  have hA : HasFDerivAt (fun y ↦ fderiv 𝕜 f (φ y))
      ((fderiv 𝕜 (fderiv 𝕜 f) (φ b)).comp (fderiv 𝕜 φ b)) b := hf1.comp b hφ0
  have hev : ∀ᶠ y in 𝓝 b, fderiv 𝕜 (f ∘ φ) y = (fderiv 𝕜 f (φ y)).comp (fderiv 𝕜 φ y) := by
    have h1 : ∀ᶠ y in 𝓝 b, DifferentiableAt 𝕜 φ y :=
      ((hφ.of_le (by norm_num)).eventually (by norm_num)).mono fun _ hy ↦
        hy.differentiableAt one_ne_zero
    have h2 : ∀ᶠ y in 𝓝 b, DifferentiableAt 𝕜 f (φ y) :=
      hφ.continuousAt.eventually
        (((hf.of_le (by norm_num)).eventually (by norm_num)).mono fun _ hy ↦
          hy.differentiableAt one_ne_zero)
    filter_upwards [h1, h2] with y hy1 hy2 using fderiv_comp (x := y) hy2 hy1
  rw [((hA.clm_comp hφ1).congr_of_eventuallyEq hev).fderiv]
  simp [add_comm]

/-- **The second derivative at a critical point is a bilinear form pullback.** If `f` is `C²` at
`φ b`, `φ` is `C²` at `b`, and the differential of `f` vanishes at `φ b`, then the second
derivative of `f ∘ φ` at `b` is the second derivative of `f` at `φ b` evaluated on the images of
the differential of `φ`. -/
theorem fderiv_fderiv_comp_apply_of_fderiv_eq_zero {f : E → G} {φ : F → E} {b : F}
    (hf : ContDiffAt 𝕜 2 f (φ b)) (hφ : ContDiffAt 𝕜 2 φ b) (hc : fderiv 𝕜 f (φ b) = 0) (v w : F) :
    fderiv 𝕜 (fderiv 𝕜 (f ∘ φ)) b v w =
      fderiv 𝕜 (fderiv 𝕜 f) (φ b) (fderiv 𝕜 φ b v) (fderiv 𝕜 φ b w) := by
  simp [fderiv_fderiv_comp_apply hf hφ, hc]

/-- The second derivative of a separated sum `φ ∘ Prod.fst + ψ ∘ Prod.snd` at `(a, b)` is block
diagonal: it sends `(v, w)` to the coproduct of `D²φ a v` and `D²ψ b w`, i.e. to the functional
`(v', w') ↦ D²φ a v v' + D²ψ b w w'`. -/
theorem fderiv_fderiv_comp_fst_add_comp_snd {φ : E → G} {ψ : F → G} {a : E} {b : F}
    (hφ : ContDiffAt 𝕜 2 φ a) (hψ : ContDiffAt 𝕜 2 ψ b) :
    fderiv 𝕜 (fderiv 𝕜 (φ ∘ Prod.fst + ψ ∘ Prod.snd)) (a, b) =
      (ContinuousLinearMap.coprodEquivL 𝕜 :
          ((E →L[𝕜] G) × (F →L[𝕜] G)) ≃L[𝕜] (E × F →L[𝕜] G)) ∘L
        (fderiv 𝕜 (fderiv 𝕜 φ) a).prodMap (fderiv 𝕜 (fderiv 𝕜 ψ) b) := by
  -- Near `(a, b)` both summands are differentiable, so the first derivative is the coproduct of
  -- the derivatives of the summands, which is the image of the pair of derivatives under the
  -- linear homeomorphism `coprodEquivL`.
  have hev : fderiv 𝕜 (φ ∘ Prod.fst + ψ ∘ Prod.snd) =ᶠ[𝓝 (a, b)]
      fun p ↦ ContinuousLinearMap.coprodEquivL 𝕜 (fderiv 𝕜 φ p.1, fderiv 𝕜 ψ p.2) := by
    have h1 : ∀ᶠ p : E × F in 𝓝 (a, b), DifferentiableAt 𝕜 φ p.1 :=
      continuousAt_fst.eventually (((hφ.of_le (by norm_num)).eventually (by norm_num)).mono
        fun _ hy ↦ hy.differentiableAt one_ne_zero)
    have h2 : ∀ᶠ p : E × F in 𝓝 (a, b), DifferentiableAt 𝕜 ψ p.2 :=
      continuousAt_snd.eventually (((hψ.of_le (by norm_num)).eventually (by norm_num)).mono
        fun _ hy ↦ hy.differentiableAt one_ne_zero)
    filter_upwards [h1, h2] with ⟨u, w⟩ hu hw
    rw [fderiv_comp_fst_add_comp_snd hu hw]
    refine ContinuousLinearMap.ext fun q ↦ ?_
    simp [ContinuousLinearMap.coprodEquivL_apply_apply]
  have hD : HasFDerivAt (fun p : E × F ↦ (fderiv 𝕜 φ p.1, fderiv 𝕜 ψ p.2))
      ((fderiv 𝕜 (fderiv 𝕜 φ) a).prodMap (fderiv 𝕜 (fderiv 𝕜 ψ) b)) (a, b) :=
    ((hφ.hasFDerivAt_fderiv le_rfl).comp (a, b) (hasFDerivAt_fst (𝕜 := 𝕜) (p := (a, b)))).prodMk
      ((hψ.hasFDerivAt_fderiv le_rfl).comp (a, b) (hasFDerivAt_snd (𝕜 := 𝕜) (p := (a, b))))
  rw [hev.fderiv_eq]
  exact ((ContinuousLinearMap.coprodEquivL 𝕜 :
    ((E →L[𝕜] G) × (F →L[𝕜] G)) ≃L[𝕜] (E × F →L[𝕜] G)).hasFDerivAt.comp (a, b) hD).fderiv

/-- The second derivative of the directional derivative `y ↦ Dg(y) v` of a `C³` map `g` is the
third derivative of `g`, evaluated at `v`. -/
theorem fderiv_fderiv_fderiv_apply {g : E → F} {x : E} (hg : ContDiffAt 𝕜 3 g x) (v a b : E) :
    fderiv 𝕜 (fderiv 𝕜 fun y ↦ fderiv 𝕜 g y v) x a b =
      fderiv 𝕜 (fderiv 𝕜 (fderiv 𝕜 g)) x a b v := by
  have hDg : ContDiffAt 𝕜 2 (fderiv 𝕜 g) x := hg.fderiv_right (m := 2) (by norm_num)
  have hD2 : DifferentiableAt 𝕜 (fderiv 𝕜 (fderiv 𝕜 g)) x :=
    (hDg.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hv : ContDiffAt 𝕜 2 (fun y ↦ fderiv 𝕜 g y v) x := hDg.clm_apply contDiffAt_const
  have hfirst : (fun y ↦ fderiv 𝕜 (fun y ↦ fderiv 𝕜 g y v) y b) =ᶠ[𝓝 x]
      fun y ↦ fderiv 𝕜 (fderiv 𝕜 g) y b v := by
    have hev : ∀ᶠ y in 𝓝 x, ContDiffAt 𝕜 2 (fderiv 𝕜 g) y := hDg.eventually (by simp)
    filter_upwards [hev] with y hy
    exact fderiv_clm_apply_const_apply (hy.differentiableAt (by norm_num)) v b
  rw [← fderiv_clm_apply_const_apply ((hv.fderiv_right (m := 1) (by norm_num)).differentiableAt
    (by norm_num)), hfirst.fderiv_eq, fderiv_clm_apply (hD2.clm_apply (differentiableAt_const b))
    (differentiableAt_const v)]
  simp [fderiv_clm_apply_const_apply hD2]

/-- **The third derivative is symmetric in its last two directions.** For a map that is
`C^{minSmoothness 𝕜 3}` at `x` (so `C³` over `ℝ` or `ℂ`), differentiating the symmetry of the
second derivative near `x` gives `D³g(x)(a, b, c) = D³g(x)(a, c, b)`. -/
theorem fderiv_fderiv_fderiv_apply_comm {n : WithTop ℕ∞} {g : E → F} {x : E}
    (hg : ContDiffAt 𝕜 n g x) (hn : minSmoothness 𝕜 3 ≤ n) (a b c : E) :
    fderiv 𝕜 (fderiv 𝕜 (fderiv 𝕜 g)) x a b c = fderiv 𝕜 (fderiv 𝕜 (fderiv 𝕜 g)) x a c b := by
  obtain ⟨n', hn', hn'n, hn'top⟩ := exist_minSmoothness_le_ne_infty (m := 3) hn
  have hg' : ContDiffAt 𝕜 n' g x := hg.of_le hn'n
  have hD2 : DifferentiableAt 𝕜 (fderiv 𝕜 (fderiv 𝕜 g)) x :=
    ((hg'.fderiv_right (m := 2) (le_minSmoothness.trans hn')).fderiv_right (m := 1)
      (by norm_num)).differentiableAt (by norm_num)
  have hsymm : (fun y ↦ fderiv 𝕜 (fderiv 𝕜 g) y b c) =ᶠ[𝓝 x]
      fun y ↦ fderiv 𝕜 (fderiv 𝕜 g) y c b := by
    filter_upwards [hg'.eventually hn'top] with y hy
    exact hy.isSymmSndFDerivAt ((minSmoothness_monotone (by norm_num)).trans hn') b c
  have h := congrArg (fun L : E →L[𝕜] F ↦ L a) hsymm.fderiv_eq
  have hb : DifferentiableAt 𝕜 (fun y ↦ fderiv 𝕜 (fderiv 𝕜 g) y b) x :=
    hD2.clm_apply (differentiableAt_const b)
  have hc : DifferentiableAt 𝕜 (fun y ↦ fderiv 𝕜 (fderiv 𝕜 g) y c) x :=
    hD2.clm_apply (differentiableAt_const c)
  rwa [fderiv_clm_apply_const_apply hb, fderiv_clm_apply_const_apply hc,
    fderiv_clm_apply_const_apply hD2, fderiv_clm_apply_const_apply hD2] at h

end TauCeti

end
