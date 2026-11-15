/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.VectorField
public import TauCeti.Analysis.Normed.Operator.Bilinear
import Mathlib.Analysis.Calculus.FDeriv.CompCLM
import Mathlib.Analysis.Calculus.FDeriv.Equiv
import Mathlib.Analysis.Calculus.MeanValue
import TauCeti.Analysis.Calculus.Bilinear
import TauCeti.Analysis.Calculus.ParametricFDeriv

/-!
# The Lie derivative of bilinear-form fields on normed spaces

The Lie derivative of a field of continuous bilinear maps `b : E → E →L[𝕜] E →L[𝕜] F` along a
vector field `V : E → E` on a normed space `E` is

`L_V b (x) (u, w) = Db(x)(V x)(u, w) + b(x)(DV(x) u, w) + b(x)(u, DV(x) w)`.

As with `TauCeti.lieDerivForm` and `TauCeti.lieDerivEndomorphism`, the definition needs no flow and
is total, with junk values where `b` or `V` is not differentiable; `TauCeti.lieDerivBilinWithin`
localizes all derivatives to a set `s`, so it applies directly in charts of manifolds with boundary
or corners.

## Main declarations

* `TauCeti.lieDerivBilinWithin`, `TauCeti.lieDerivBilin`: the Lie derivative of a field of
  continuous bilinear maps within a set and on the whole space.
* `TauCeti.lieDerivBilinWithin_symm`, `TauCeti.lieDerivBilin_symm`: symmetry preservation.
* `TauCeti.lieDerivBilinWithin_fun_smul`, `TauCeti.lieDerivBilin_fun_smul`: Leibniz rule for
  multiplication by a scalar function.
* `TauCeti.contDiffWithinAt_lieDerivBilinWithin`, `TauCeti.contDiffAt_lieDerivBilin`: `C^n`
  regularity of the Lie derivative.
* `TauCeti.lieDerivBilinWithin_apply_vectorField`, `TauCeti.lieDerivBilin_apply_vectorField`: the
  bracket formula `(L_V b)(X, Y) = D(b(X, Y))(V) - b([V, X], Y) - b(X, [V, Y])`.
* `HasDerivWithinAt.pullbackBilinL`, `HasDerivAt.pullbackBilinL`: differentiating
  `r ↦ pullbackBilinL (L r) (B r)`.
* `TauCeti.hasDerivAt_pullbackBilinL_fderiv`: the time-dependent pullback-variation identity
  `∂_t (ψ_t^* b_t) = ψ_t^* (∂_t b_t + L_{V} b_t)`.

## References

* John M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Springer, 2012, Proposition 12.32 and
  Theorem 12.37.
* Bennett Chow and Dan Knopf, *The Ricci Flow: An Introduction*, AMS, 2004, Appendix A.
-/

public section

noncomputable section

open Set Filter ContinuousLinearMap VectorField
open scoped Topology ContDiff

-- Unify algebraic and normed instances on nested continuous-linear-map spaces.
attribute [local instance 1001] NormedAddCommGroup.toSeminormedAddCommGroup
  NormedAddCommGroup.toAddCommGroup AddCommGroup.toAddCommMonoid NormedSpace.toModule

private local instance {𝕜 V G : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup V]
    [NormedSpace 𝕜 V] [NormedAddCommGroup G] [NormedSpace 𝕜 G] :
    NormedAddCommGroup (V →L[𝕜] G) := ContinuousLinearMap.toNormedAddCommGroup

private local instance {𝕜 V G : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup V]
    [NormedSpace 𝕜 V] [NormedAddCommGroup G] [NormedSpace 𝕜 G] :
    NormedSpace 𝕜 (V →L[𝕜] G) := ContinuousLinearMap.toNormedSpace

namespace TauCeti

section LieDeriv

variable {𝕜 E F : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {U V V₁ X Y : E → E} {b b₁ c : E → E →L[𝕜] E →L[𝕜] F} {s t : Set E} {x : E}

/-- The Lie derivative within `s` at `x` of a field of continuous bilinear maps `b` along a vector
field `V`: `Db|_s(x)(V x) + (b x)(DV|_s(x) ·, ·) + (b x)(·, DV|_s(x) ·)`. -/
def lieDerivBilinWithin (V : E → E) (b : E → E →L[𝕜] E →L[𝕜] F) (s : Set E) (x : E) :
    E →L[𝕜] E →L[𝕜] F :=
  fderivWithin 𝕜 b s x (V x) +
    (b x).bilinearComp (fderivWithin 𝕜 V s x) (.id 𝕜 E) +
    (b x).bilinearComp (.id 𝕜 E) (fderivWithin 𝕜 V s x)

/-- The Lie derivative at `x` of a field of continuous bilinear maps `b` along a vector field `V`:
`Db(x)(V x) + (b x)(DV(x) ·, ·) + (b x)(·, DV(x) ·)`. -/
def lieDerivBilin (V : E → E) (b : E → E →L[𝕜] E →L[𝕜] F) (x : E) : E →L[𝕜] E →L[𝕜] F :=
  fderiv 𝕜 b x (V x) +
    (b x).bilinearComp (fderiv 𝕜 V x) (.id 𝕜 E) +
    (b x).bilinearComp (.id 𝕜 E) (fderiv 𝕜 V x)

theorem lieDerivBilinWithin_def (V : E → E) (b : E → E →L[𝕜] E →L[𝕜] F) (s : Set E) (x : E) :
    lieDerivBilinWithin V b s x =
      fderivWithin 𝕜 b s x (V x) +
        (b x).bilinearComp (fderivWithin 𝕜 V s x) (.id 𝕜 E) +
        (b x).bilinearComp (.id 𝕜 E) (fderivWithin 𝕜 V s x) :=
  (rfl)

theorem lieDerivBilin_def (V : E → E) (b : E → E →L[𝕜] E →L[𝕜] F) (x : E) :
    lieDerivBilin V b x =
      fderiv 𝕜 b x (V x) +
        (b x).bilinearComp (fderiv 𝕜 V x) (.id 𝕜 E) +
        (b x).bilinearComp (.id 𝕜 E) (fderiv 𝕜 V x) :=
  (rfl)

@[simp]
theorem lieDerivBilinWithin_univ (V : E → E) (b : E → E →L[𝕜] E →L[𝕜] F) :
    lieDerivBilinWithin V b univ = lieDerivBilin V b := by
  ext x u w
  simp [lieDerivBilinWithin_def, lieDerivBilin_def]

/-- Pointwise evaluation of `lieDerivBilinWithin` on two vectors `u` and `w`. -/
theorem lieDerivBilinWithin_apply (V : E → E) (b : E → E →L[𝕜] E →L[𝕜] F) (s : Set E)
    (x u w : E) :
    lieDerivBilinWithin V b s x u w =
      fderivWithin 𝕜 b s x (V x) u w +
        b x (fderivWithin 𝕜 V s x u) w + b x u (fderivWithin 𝕜 V s x w) :=
  (rfl)

/-- Pointwise evaluation of `lieDerivBilin` on two vectors `u` and `w`. -/
theorem lieDerivBilin_apply (V : E → E) (b : E → E →L[𝕜] E →L[𝕜] F) (x u w : E) :
    lieDerivBilin V b x u w =
      fderiv 𝕜 b x (V x) u w + b x (fderiv 𝕜 V x u) w + b x u (fderiv 𝕜 V x w) :=
  (rfl)

/-! ### Locality, constants, and linearity -/

theorem lieDerivBilinWithin_congr_set (hs : s =ᶠ[𝓝 x] t) :
    lieDerivBilinWithin V b s x = lieDerivBilinWithin V b t x := by
  simp only [lieDerivBilinWithin_def, fderivWithin_congr_set hs]

theorem _root_.Filter.EventuallyEq.lieDerivBilinWithin_eq_nhds
    (hV : V₁ =ᶠ[𝓝 x] V) (hb : b₁ =ᶠ[𝓝 x] b) :
    lieDerivBilinWithin V₁ b₁ s x = lieDerivBilinWithin V b s x := by
  have hVs :=
    (hV.filter_mono (nhdsWithin_le_nhds (s := s))).fderivWithin_eq (𝕜 := 𝕜) hV.self_of_nhds
  have hbs :=
    (hb.filter_mono (nhdsWithin_le_nhds (s := s))).fderivWithin_eq (𝕜 := 𝕜) hb.self_of_nhds
  simp only [lieDerivBilinWithin_def, hV.self_of_nhds, hb.self_of_nhds, hVs, hbs]

theorem _root_.Filter.EventuallyEq.lieDerivBilin_eq
    (hV : V₁ =ᶠ[𝓝 x] V) (hb : b₁ =ᶠ[𝓝 x] b) :
    lieDerivBilin V₁ b₁ x = lieDerivBilin V b x := by
  rw [← lieDerivBilinWithin_univ, ← lieDerivBilinWithin_univ,
    hV.lieDerivBilinWithin_eq_nhds hb]

@[simp]
theorem lieDerivBilinWithin_zero (V : E → E) (s : Set E) (x : E) :
    lieDerivBilinWithin V (0 : E → E →L[𝕜] E →L[𝕜] F) s x = 0 := by
  ext u w; simp [lieDerivBilinWithin_apply]

@[simp]
theorem lieDerivBilin_zero (V : E → E) :
    lieDerivBilin V (0 : E → E →L[𝕜] E →L[𝕜] F) = 0 := by
  rw [← lieDerivBilinWithin_univ]
  exact funext (lieDerivBilinWithin_zero V univ)

@[simp]
theorem lieDerivBilinWithin_zero_left (b : E → E →L[𝕜] E →L[𝕜] F) (s : Set E) (x : E) :
    lieDerivBilinWithin (0 : E → E) b s x = 0 := by
  ext u w; simp [lieDerivBilinWithin_apply]

@[simp]
theorem lieDerivBilin_zero_left (b : E → E →L[𝕜] E →L[𝕜] F) :
    lieDerivBilin (0 : E → E) b = 0 := by
  rw [← lieDerivBilinWithin_univ]
  exact funext (lieDerivBilinWithin_zero_left b univ)

/-- The Lie derivative of a constant bilinear form `B` is the derivation action of `DV(x)` on
`B`. -/
theorem lieDerivBilin_const (V : E → E) (B : E →L[𝕜] E →L[𝕜] F) (x : E) :
    lieDerivBilin V (fun _ ↦ B) x =
      B.bilinearComp (fderiv 𝕜 V x) (.id 𝕜 E) + B.bilinearComp (.id 𝕜 E) (fderiv 𝕜 V x) := by
  ext u w; simp [lieDerivBilin_apply]

theorem lieDerivBilinWithin_add (hs : UniqueDiffWithinAt 𝕜 s x)
    (hb : DifferentiableWithinAt 𝕜 b s x) (hc : DifferentiableWithinAt 𝕜 c s x) :
    lieDerivBilinWithin V (b + c) s x =
      lieDerivBilinWithin V b s x + lieDerivBilinWithin V c s x := by
  ext u w
  simp only [lieDerivBilinWithin_apply, fderivWithin_add hs hb hc, Pi.add_apply, add_apply]
  abel

theorem lieDerivBilin_add (hb : DifferentiableAt 𝕜 b x) (hc : DifferentiableAt 𝕜 c x) :
    lieDerivBilin V (b + c) x = lieDerivBilin V b x + lieDerivBilin V c x := by
  simpa only [lieDerivBilinWithin_univ] using
    lieDerivBilinWithin_add (V := V) uniqueDiffWithinAt_univ
      hb.differentiableWithinAt hc.differentiableWithinAt

theorem lieDerivBilinWithin_neg (V : E → E) (b : E → E →L[𝕜] E →L[𝕜] F)
    (hs : UniqueDiffWithinAt 𝕜 s x) :
    lieDerivBilinWithin V (-b) s x = -lieDerivBilinWithin V b s x := by
  ext u w
  rw [lieDerivBilinWithin_apply, fderivWithin_neg hs]
  simp only [Pi.neg_apply, neg_apply, lieDerivBilinWithin_apply]
  abel

@[simp]
theorem lieDerivBilin_neg (V : E → E) (b : E → E →L[𝕜] E →L[𝕜] F) :
    lieDerivBilin V (-b) = -lieDerivBilin V b := by
  ext x : 1
  simpa only [lieDerivBilinWithin_univ, Pi.neg_apply] using
    lieDerivBilinWithin_neg V b (x := x) uniqueDiffWithinAt_univ

theorem lieDerivBilin_sub (hb : DifferentiableAt 𝕜 b x) (hc : DifferentiableAt 𝕜 c x) :
    lieDerivBilin V (b - c) x = lieDerivBilin V b x - lieDerivBilin V c x := by
  rw [sub_eq_add_neg, lieDerivBilin_add hb hc.neg, lieDerivBilin_neg, Pi.neg_apply,
    ← sub_eq_add_neg]

@[simp]
theorem lieDerivBilinWithin_smul (a : 𝕜) (b : E → E →L[𝕜] E →L[𝕜] F)
    (hs : UniqueDiffWithinAt 𝕜 s x) :
    lieDerivBilinWithin V (a • b) s x = a • lieDerivBilinWithin V b s x := by
  ext u w
  rw [lieDerivBilinWithin_apply, fderivWithin_const_smul_field (f := b) a hs]
  simp [lieDerivBilinWithin_apply, smul_add]

@[simp]
theorem lieDerivBilin_smul (a : 𝕜) (b : E → E →L[𝕜] E →L[𝕜] F) :
    lieDerivBilin V (a • b) = a • lieDerivBilin V b := by
  ext x : 1
  simpa only [lieDerivBilinWithin_univ, Pi.smul_apply] using
    lieDerivBilinWithin_smul (V := V) (x := x) a b uniqueDiffWithinAt_univ

/-- **Leibniz rule** for multiplying a bilinear-form field by a scalar function within `s`:
`L_V (f • b) = (Df|_s(x)(V x)) • b x + f x • L_V b (x)`. -/
theorem lieDerivBilinWithin_fun_smul {f : E → 𝕜} (hs : UniqueDiffWithinAt 𝕜 s x)
    (hf : DifferentiableWithinAt 𝕜 f s x) (hb : DifferentiableWithinAt 𝕜 b s x) :
    lieDerivBilinWithin V (fun y ↦ f y • b y) s x =
      fderivWithin 𝕜 f s x (V x) • b x + f x • lieDerivBilinWithin V b s x := by
  have hdf := (hf.hasFDerivWithinAt.smul hb.hasFDerivWithinAt).fderivWithin hs
  change lieDerivBilinWithin V (f • b) s x = _
  ext u w
  simp only [lieDerivBilinWithin_apply, hdf, add_apply, smul_apply, smulRight_apply, smul_add]
  abel

/-- **Leibniz rule** for multiplying a bilinear-form field by a scalar function. -/
theorem lieDerivBilin_fun_smul {f : E → 𝕜} (hf : DifferentiableAt 𝕜 f x)
    (hb : DifferentiableAt 𝕜 b x) :
    lieDerivBilin V (fun y ↦ f y • b y) x =
      fderiv 𝕜 f x (V x) • b x + f x • lieDerivBilin V b x := by
  simpa only [lieDerivBilinWithin_univ, fderivWithin_univ] using
    lieDerivBilinWithin_fun_smul (V := V) uniqueDiffWithinAt_univ
      hf.differentiableWithinAt hb.differentiableWithinAt

theorem lieDerivBilinWithin_add_left (b : E → E →L[𝕜] E →L[𝕜] F)
    (hs : UniqueDiffWithinAt 𝕜 s x) (hU : DifferentiableWithinAt 𝕜 U s x)
    (hV : DifferentiableWithinAt 𝕜 V s x) :
    lieDerivBilinWithin (U + V) b s x =
      lieDerivBilinWithin U b s x + lieDerivBilinWithin V b s x := by
  ext u w
  simp only [lieDerivBilinWithin_apply, fderivWithin_add hs hU hV, Pi.add_apply, add_apply,
    map_add]
  abel

theorem lieDerivBilin_add_left (b : E → E →L[𝕜] E →L[𝕜] F)
    (hU : DifferentiableAt 𝕜 U x) (hV : DifferentiableAt 𝕜 V x) :
    lieDerivBilin (U + V) b x = lieDerivBilin U b x + lieDerivBilin V b x := by
  simpa only [lieDerivBilinWithin_univ] using
    lieDerivBilinWithin_add_left b uniqueDiffWithinAt_univ
      hU.differentiableWithinAt hV.differentiableWithinAt

theorem lieDerivBilin_neg_left (V : E → E) (b : E → E →L[𝕜] E →L[𝕜] F) (x : E) :
    lieDerivBilin (-V) b x = -lieDerivBilin V b x := by
  ext u w
  rw [lieDerivBilin_apply, fderiv_neg]
  simp only [Pi.neg_apply, neg_apply, map_neg, lieDerivBilin_apply]
  abel

theorem lieDerivBilin_const_smul_left (a : 𝕜) (V : E → E) (b : E → E →L[𝕜] E →L[𝕜] F) (x : E) :
    lieDerivBilin (a • V) b x = a • lieDerivBilin V b x := by
  ext u w
  rw [lieDerivBilin_apply, fderiv_const_smul_field (f := V) a]
  simp [lieDerivBilin_apply, smul_add]

/-! ### Flip and symmetry preservation -/

/-- The Lie derivative within `s` commutes with fibrewise transposition. -/
theorem lieDerivBilinWithin_flip (V : E → E) (b : E → E →L[𝕜] E →L[𝕜] F)
    (hs : UniqueDiffWithinAt 𝕜 s x) :
    lieDerivBilinWithin V (fun y ↦ (b y).flip) s x = (lieDerivBilinWithin V b s x).flip := by
  have hflipB : IsBoundedLinearMap 𝕜 (fun c : E →L[𝕜] E →L[𝕜] F ↦ c.flip) :=
    { map_add := fun c d ↦ by ext u w; simp
      map_smul := fun a c ↦ by ext u w; simp
      bound := ⟨1, by norm_num, fun c ↦ by simp⟩ }
  let L : (E →L[𝕜] E →L[𝕜] F) ≃L[𝕜] E →L[𝕜] E →L[𝕜] F :=
    ContinuousLinearEquiv.equivOfInverse hflipB.toContinuousLinearMap hflipB.toContinuousLinearMap
      (fun c ↦ by ext u w; rfl) (fun c ↦ by ext u w; rfl)
  have hL : ∀ c, L c = c.flip := fun _ ↦ rfl
  have hflip : fderivWithin 𝕜 (L ∘ b) s x = L.toContinuousLinearMap ∘L fderivWithin 𝕜 b s x :=
    L.comp_fderivWithin hs
  ext u w
  change lieDerivBilinWithin V (L ∘ b) s x u w = (lieDerivBilinWithin V b s x).flip u w
  simp only [lieDerivBilinWithin_apply, hflip, Function.comp_apply, comp_apply,
    ContinuousLinearEquiv.coe_coe, hL, flip_apply]
  abel

/-- The Lie derivative commutes with fibrewise transposition. -/
theorem lieDerivBilin_flip (V : E → E) (b : E → E →L[𝕜] E →L[𝕜] F) (x : E) :
    lieDerivBilin V (fun y ↦ (b y).flip) x = (lieDerivBilin V b x).flip := by
  simpa only [lieDerivBilinWithin_univ] using
    lieDerivBilinWithin_flip V b (x := x) uniqueDiffWithinAt_univ

/-- If `b` is symmetric on `s`, then `lieDerivBilinWithin V b s x` is symmetric. No
differentiability of `b` or `V` is required. -/
theorem lieDerivBilinWithin_symm (hs : UniqueDiffWithinAt 𝕜 s x) (hx : x ∈ s)
    (hb : ∀ y ∈ s, ∀ u w, b y u w = b y w u) (u w : E) :
    lieDerivBilinWithin V b s x u w = lieDerivBilinWithin V b s x w u := by
  have heq : EqOn (fun y ↦ (b y).flip) b s := fun y hy ↦ by ext a c; exact hb y hy c a
  have h0 : lieDerivBilinWithin V (fun y ↦ (b y).flip) s x = lieDerivBilinWithin V b s x := by
    simp only [lieDerivBilinWithin_def, fderivWithin_congr heq (heq hx), heq hx]
  exact (congrArg (fun d ↦ d w u) (h0.symm.trans (lieDerivBilinWithin_flip V b hs))).symm

/-- If `b` is symmetric, then `lieDerivBilin V b x` is symmetric. No differentiability of `b` or
`V` is required. -/
theorem lieDerivBilin_symm (hb : ∀ y u w, b y u w = b y w u) (x u w : E) :
    lieDerivBilin V b x u w = lieDerivBilin V b x w u := by
  simpa only [lieDerivBilinWithin_univ] using
    lieDerivBilinWithin_symm (V := V) uniqueDiffWithinAt_univ (mem_univ x) (fun y _ ↦ hb y) u w

/-! ### Regularity -/

/-- If `V` and `b` are `C^n` within `s` at `x` with `m + 1 ≤ n`, then `lieDerivBilinWithin V b s`
is `C^m` within `s` at `x`. -/
theorem contDiffWithinAt_lieDerivBilinWithin {m n : WithTop ℕ∞}
    (hV : ContDiffWithinAt 𝕜 n V s x) (hb : ContDiffWithinAt 𝕜 n b s x)
    (hs : UniqueDiffOn 𝕜 s) (hx : x ∈ s) (hmn : m + 1 ≤ n) :
    ContDiffWithinAt 𝕜 m (lieDerivBilinWithin V b s) s x := by
  have hm : m ≤ n := le_self_add.trans hmn
  have hdV : ContDiffWithinAt 𝕜 m (fderivWithin 𝕜 V s) s x := hV.fderivWithin_right hs hmn hx
  have hdb : ContDiffWithinAt 𝕜 m (fderivWithin 𝕜 b s) s x := hb.fderivWithin_right hs hmn hx
  have hb' : ContDiffWithinAt 𝕜 m b s x := hb.of_le hm
  have h1 : ContDiffWithinAt 𝕜 m (fun y ↦ fderivWithin 𝕜 b s y (V y)) s x :=
    hdb.clm_apply (hV.of_le hm)
  have h2 := hb'.clm_comp hdV
  have h3 := ((compL 𝕜 E E F).flip.contDiff.comp_contDiffWithinAt hdV).clm_comp hb'
  refine ((h1.add h2).add h3).congr_of_eventuallyEq_of_mem (Eventually.of_forall fun y ↦ ?_) hx
  ext u w; rfl

/-- If `V` and `b` are `C^n` at `x` with `m + 1 ≤ n`, then `lieDerivBilin V b` is `C^m` at `x`. -/
theorem contDiffAt_lieDerivBilin {m n : WithTop ℕ∞} (hV : ContDiffAt 𝕜 n V x)
    (hb : ContDiffAt 𝕜 n b x) (hmn : m + 1 ≤ n) :
    ContDiffAt 𝕜 m (lieDerivBilin V b) x := by
  rw [← contDiffWithinAt_univ, ← lieDerivBilinWithin_univ]
  exact contDiffWithinAt_lieDerivBilinWithin hV.contDiffWithinAt hb.contDiffWithinAt
    uniqueDiffOn_univ (mem_univ x) hmn

/-- If `V` and `b` are `C^n` with `m + 1 ≤ n`, then `lieDerivBilin V b` is `C^m`. -/
theorem contDiff_lieDerivBilin {m n : WithTop ℕ∞} (hV : ContDiff 𝕜 n V) (hb : ContDiff 𝕜 n b)
    (hmn : m + 1 ≤ n) : ContDiff 𝕜 m (lieDerivBilin V b) :=
  contDiff_iff_contDiffAt.2 fun _ ↦ contDiffAt_lieDerivBilin hV.contDiffAt hb.contDiffAt hmn

/-! ### The bracket formula -/

/-- **The bracket formula** for `lieDerivBilinWithin`: evaluated on vector fields `X` and `Y`
differentiable within `s` at `x`,
`(L_V b)(X, Y) = D(b(X, Y))|_s(x)(V x) - b x ([V, X]|_s x, Y x) - b x (X x, [V, Y]|_s x)`.
No differentiability of `V` is required. -/
theorem lieDerivBilinWithin_apply_vectorField (hs : UniqueDiffWithinAt 𝕜 s x)
    (hb : DifferentiableWithinAt 𝕜 b s x) (hX : DifferentiableWithinAt 𝕜 X s x)
    (hY : DifferentiableWithinAt 𝕜 Y s x) :
    lieDerivBilinWithin V b s x (X x) (Y x) =
      fderivWithin 𝕜 (fun y ↦ b y (X y) (Y y)) s x (V x) -
        b x (lieBracketWithin 𝕜 V X s x) (Y x) -
        b x (X x) (lieBracketWithin 𝕜 V Y s x) := by
  have hbX : HasFDerivWithinAt (fun y ↦ b y (X y))
      ((b x).comp (fderivWithin 𝕜 X s x) + (fderivWithin 𝕜 b s x).flip (X x)) s x :=
    hb.hasFDerivWithinAt.clm_apply hX.hasFDerivWithinAt
  have hbXY := (hbX.clm_apply hY.hasFDerivWithinAt).fderivWithin hs
  simp only [lieDerivBilinWithin_apply, lieBracketWithin_eq, hbXY, add_apply, comp_apply,
    flip_apply, map_sub, sub_apply]
  abel

/-- **The bracket formula** for `lieDerivBilin`: evaluated on differentiable vector fields `X` and
`Y`, `(L_V b)(X, Y) = D(b(X, Y))(x)(V x) - b x ([V, X] x, Y x) - b x (X x, [V, Y] x)`. -/
theorem lieDerivBilin_apply_vectorField (hb : DifferentiableAt 𝕜 b x)
    (hX : DifferentiableAt 𝕜 X x) (hY : DifferentiableAt 𝕜 Y x) :
    lieDerivBilin V b x (X x) (Y x) =
      fderiv 𝕜 (fun y ↦ b y (X y) (Y y)) x (V x) -
        b x (lieBracket 𝕜 V X x) (Y x) - b x (X x) (lieBracket 𝕜 V Y x) := by
  simpa only [lieDerivBilinWithin_univ, fderivWithin_univ, lieBracketWithin_univ] using
    lieDerivBilinWithin_apply_vectorField (V := V) uniqueDiffWithinAt_univ
      hb.differentiableWithinAt hX.differentiableWithinAt hY.differentiableWithinAt

end LieDeriv

/-! ### Pullback differentiation along families of maps -/

section PullbackFlow

/-- Product rule within a set for pulling a curve of continuous bilinear maps `B r` back along a
curve of continuous linear maps `L r`. -/
theorem _root_.HasDerivWithinAt.pullbackBilinL {𝕜 V W G : Type*} [NontriviallyNormedField 𝕜]
    [NormedAddCommGroup V] [NormedSpace 𝕜 V] [NormedAddCommGroup W] [NormedSpace 𝕜 W]
    [NormedAddCommGroup G] [NormedSpace 𝕜 G]
    {B : 𝕜 → V →L[𝕜] V →L[𝕜] G} {B' : V →L[𝕜] V →L[𝕜] G}
    {L : 𝕜 → W →L[𝕜] V} {L' : W →L[𝕜] V} {s : Set 𝕜} {t : 𝕜}
    (hB : HasDerivWithinAt B B' s t) (hL : HasDerivWithinAt L L' s t) :
    HasDerivWithinAt (fun r ↦ ContinuousLinearMap.pullbackBilinL (L r) (B r))
      (ContinuousLinearMap.pullbackBilinL (L t) B' +
        (B t).bilinearComp L' (L t) + (B t).bilinearComp (L t) L') s t := by
  let Φ : (W →L[𝕜] V) →L[𝕜] (V →L[𝕜] G) →L[𝕜] W →L[𝕜] G := (compL 𝕜 W V G).flip
  have hΦ : HasDerivWithinAt (fun r ↦ Φ (L r)) (Φ L') s t :=
    Φ.hasFDerivAt.comp_hasDerivWithinAt t hL
  have hBL := hB.clm_comp hL
  have heq : (fun r ↦ ContinuousLinearMap.pullbackBilinL (L r) (B r)) =
      fun r ↦ (Φ (L r)).comp ((B r).comp (L r)) := by
    ext r v w; simp [Φ]
  rw [heq]
  refine (hΦ.clm_comp hBL).congr_deriv ?_
  ext v w
  simp only [Φ, add_apply, pullbackBilinL_apply, bilinearComp_apply, comp_apply, flip_apply,
    compL_apply, map_add]
  abel

/-- Product rule for pulling a curve of continuous bilinear maps `B r` back along a curve of
continuous linear maps `L r`. -/
theorem _root_.HasDerivAt.pullbackBilinL {𝕜 V W G : Type*} [NontriviallyNormedField 𝕜]
    [NormedAddCommGroup V] [NormedSpace 𝕜 V] [NormedAddCommGroup W] [NormedSpace 𝕜 W]
    [NormedAddCommGroup G] [NormedSpace 𝕜 G]
    {B : 𝕜 → V →L[𝕜] V →L[𝕜] G} {B' : V →L[𝕜] V →L[𝕜] G}
    {L : 𝕜 → W →L[𝕜] V} {L' : W →L[𝕜] V} {t : 𝕜}
    (hB : HasDerivAt B B' t) (hL : HasDerivAt L L' t) :
    HasDerivAt (fun r ↦ ContinuousLinearMap.pullbackBilinL (L r) (B r))
      (ContinuousLinearMap.pullbackBilinL (L t) B' +
        (B t).bilinearComp L' (L t) + (B t).bilinearComp (L t) L') t := by
  rw [← hasDerivWithinAt_univ] at hB hL ⊢
  exact hB.pullbackBilinL hL

/-- **The time derivative of a pulled-back family of bilinear forms.** If `ψ_s x` moves at time `t`
with velocity `V (ψ_t x)`, its spatial derivative solves `∂_s Dψ_s x|_{s = t} = DV(ψ_t x) ∘ Dψ_t x`,
and `b` is jointly differentiable at `(t, ψ_t x)` with parameter derivative `b'` at `ψ_t x`, then
`s ↦ ψ_s^* b_s (x)` has derivative `ψ_t^* (b' + L_V b_t (ψ_t x))` at `t`. -/
theorem hasDerivAt_pullbackBilinL_fderiv {𝕜 E F : Type*} [NontriviallyNormedField 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    {b : 𝕜 → E → E →L[𝕜] E →L[𝕜] F} {b' : E →L[𝕜] E →L[𝕜] F}
    {ψ : 𝕜 → E → E} {V : E → E} {x : E} {t : 𝕜}
    (hb : DifferentiableAt 𝕜 (fun p : 𝕜 × E ↦ b p.1 p.2) (t, ψ t x))
    (hb' : HasDerivAt (fun s ↦ b s (ψ t x)) b' t)
    (hψ : HasDerivAt (fun s ↦ ψ s x) (V (ψ t x)) t)
    (hDψ : HasDerivAt (fun s ↦ fderiv 𝕜 (ψ s) x)
      (fderiv 𝕜 V (ψ t x) ∘L fderiv 𝕜 (ψ t) x) t) :
    HasDerivAt (fun s ↦ ContinuousLinearMap.pullbackBilinL (fderiv 𝕜 (ψ s) x) (b s (ψ s x)))
      (ContinuousLinearMap.pullbackBilinL (fderiv 𝕜 (ψ t) x)
        (b' + lieDerivBilin V (b t) (ψ t x))) t := by
  have hf := hasDerivAt_comp_prodMk hb hψ
  rw [(hasDerivAt_parameterCurve hb).unique hb', ← fderiv_timeSlice hb] at hf
  refine (hf.pullbackBilinL hDψ).congr_deriv ?_
  ext u w
  simp [lieDerivBilin_apply, add_assoc]

end PullbackFlow

end TauCeti

end
