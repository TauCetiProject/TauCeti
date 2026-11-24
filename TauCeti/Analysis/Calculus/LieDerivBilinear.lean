/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.VectorField
public import TauCeti.Analysis.Normed.Operator.Bilinear
public import TauCeti.Analysis.Calculus.Bilinear
import Mathlib.Analysis.Calculus.FDeriv.CompCLM
import Mathlib.Analysis.Calculus.FDeriv.Equiv
import TauCeti.Analysis.Calculus.ParametricFDeriv

/-!
# The Lie derivative of bilinear-form fields on normed spaces

Defines `TauCeti.lieDerivBilinWithin` and `TauCeti.lieDerivBilin` for fields of continuous bilinear
maps `b : E → E →L[𝕜] E →L[𝕜] F` along `V : E → E` by
`L_V b (x) (u, w) = Db(x)(V x)(u, w) + b(x)(DV(x) u, w) + b(x)(u, DV(x) w)`,
and proves linearity, the scalar Leibniz rule, symmetry preservation, `C^n` regularity, the bracket
formula, and pullback differentiation (`hasDerivAt_pullbackBilinL_fderiv`).

The flat API layout (`Within`/global pairs, congruence lemmas, regularity, and the bracket formula)
follows the model of `VectorField.lieBracketWithin` in `Mathlib.Analysis.Calculus.VectorField`.

## References

* John M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Springer, 2012, Proposition 12.32.
* Bennett Chow and Dan Knopf, *The Ricci Flow: An Introduction*, AMS, 2004, Appendix A.
-/

public section

noncomputable section

open Set Filter ContinuousLinearMap VectorField
open scoped Topology ContDiff

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

/-- The Lie derivative within `s` at `x` of a field of continuous bilinear maps `b` along `V`. -/
def lieDerivBilinWithin (V : E → E) (b : E → E →L[𝕜] E →L[𝕜] F) (s : Set E) (x : E) :
    E →L[𝕜] E →L[𝕜] F :=
  fderivWithin 𝕜 b s x (V x) + (b x).bilinearComp (fderivWithin 𝕜 V s x) (.id 𝕜 E) +
    (b x).bilinearComp (.id 𝕜 E) (fderivWithin 𝕜 V s x)

/-- The Lie derivative at `x` of a field of continuous bilinear maps `b` along `V`. -/
def lieDerivBilin (V : E → E) (b : E → E →L[𝕜] E →L[𝕜] F) (x : E) : E →L[𝕜] E →L[𝕜] F :=
  fderiv 𝕜 b x (V x) + (b x).bilinearComp (fderiv 𝕜 V x) (.id 𝕜 E) +
    (b x).bilinearComp (.id 𝕜 E) (fderiv 𝕜 V x)

theorem lieDerivBilinWithin_def (V : E → E) (b : E → E →L[𝕜] E →L[𝕜] F) (s : Set E) (x : E) :
    lieDerivBilinWithin V b s x = fderivWithin 𝕜 b s x (V x) +
      (b x).bilinearComp (fderivWithin 𝕜 V s x) (.id 𝕜 E) +
      (b x).bilinearComp (.id 𝕜 E) (fderivWithin 𝕜 V s x) := (rfl)

theorem lieDerivBilin_def (V : E → E) (b : E → E →L[𝕜] E →L[𝕜] F) (x : E) :
    lieDerivBilin V b x = fderiv 𝕜 b x (V x) + (b x).bilinearComp (fderiv 𝕜 V x) (.id 𝕜 E) +
      (b x).bilinearComp (.id 𝕜 E) (fderiv 𝕜 V x) := (rfl)

@[simp] theorem lieDerivBilinWithin_univ (V : E → E) (b : E → E →L[𝕜] E →L[𝕜] F) :
    lieDerivBilinWithin V b univ = lieDerivBilin V b := by
  ext x u w; simp [lieDerivBilinWithin_def, lieDerivBilin_def]

theorem lieDerivBilinWithin_apply (V : E → E) (b : E → E →L[𝕜] E →L[𝕜] F) (s : Set E)
    (x u w : E) : lieDerivBilinWithin V b s x u w =
      fderivWithin 𝕜 b s x (V x) u w + b x (fderivWithin 𝕜 V s x u) w +
        b x u (fderivWithin 𝕜 V s x w) := (rfl)

theorem lieDerivBilin_apply (V : E → E) (b : E → E →L[𝕜] E →L[𝕜] F) (x u w : E) :
    lieDerivBilin V b x u w =
      fderiv 𝕜 b x (V x) u w + b x (fderiv 𝕜 V x u) w + b x u (fderiv 𝕜 V x w) := (rfl)

/-- Variant of `lieDerivBilinWithin_congr_set` where the sets only coincide on the complement of a
point. -/
theorem lieDerivBilinWithin_congr_set' (y : E) (hs : s =ᶠ[𝓝[{y}ᶜ] x] t) :
    lieDerivBilinWithin V b s x = lieDerivBilinWithin V b t x := by
  simp only [lieDerivBilinWithin_def, fderivWithin_congr_set' _ hs]

theorem lieDerivBilinWithin_congr_set (hs : s =ᶠ[𝓝 x] t) :
    lieDerivBilinWithin V b s x = lieDerivBilinWithin V b t x :=
  lieDerivBilinWithin_congr_set' x <| hs.filter_mono inf_le_left

/-- Congruence of `lieDerivBilinWithin` for vector fields and bilinear fields agreeing on `𝓝[s] x`
and at `x`. -/
theorem _root_.Filter.EventuallyEq.lieDerivBilinWithin_eq
    (hV : V₁ =ᶠ[𝓝[s] x] V) (hxV : V₁ x = V x)
    (hb : b₁ =ᶠ[𝓝[s] x] b) (hxb : b₁ x = b x) :
    lieDerivBilinWithin V₁ b₁ s x = lieDerivBilinWithin V b s x := by
  simp only [lieDerivBilinWithin_def, hxV, hxb, hV.fderivWithin_eq (𝕜 := 𝕜) hxV,
    hb.fderivWithin_eq (𝕜 := 𝕜) hxb]

theorem _root_.Filter.EventuallyEq.lieDerivBilinWithin_eq_nhds
    (hV : V₁ =ᶠ[𝓝 x] V) (hb : b₁ =ᶠ[𝓝 x] b) :
    lieDerivBilinWithin V₁ b₁ s x = lieDerivBilinWithin V b s x :=
  (hV.filter_mono nhdsWithin_le_nhds).lieDerivBilinWithin_eq hV.self_of_nhds
    (hb.filter_mono nhdsWithin_le_nhds) hb.self_of_nhds

theorem _root_.Filter.EventuallyEq.lieDerivBilin_eq (hV : V₁ =ᶠ[𝓝 x] V) (hb : b₁ =ᶠ[𝓝 x] b) :
    lieDerivBilin V₁ b₁ x = lieDerivBilin V b x := by
  rw [← lieDerivBilinWithin_univ, ← lieDerivBilinWithin_univ, hV.lieDerivBilinWithin_eq_nhds hb]

@[simp] theorem lieDerivBilinWithin_zero (V : E → E) (s : Set E) (x : E) :
    lieDerivBilinWithin V (0 : E → E →L[𝕜] E →L[𝕜] F) s x = 0 := by
  ext u w; simp [lieDerivBilinWithin_apply]

@[simp] theorem lieDerivBilin_zero (V : E → E) :
    lieDerivBilin V (0 : E → E →L[𝕜] E →L[𝕜] F) = 0 := by ext x u w; simp [lieDerivBilin_apply]

@[simp] theorem lieDerivBilinWithin_zero_left (b : E → E →L[𝕜] E →L[𝕜] F) (s : Set E) (x : E) :
    lieDerivBilinWithin (0 : E → E) b s x = 0 := by ext u w; simp [lieDerivBilinWithin_apply]

@[simp] theorem lieDerivBilin_zero_left (b : E → E →L[𝕜] E →L[𝕜] F) :
    lieDerivBilin (0 : E → E) b = 0 := by ext x u w; simp [lieDerivBilin_apply]

theorem lieDerivBilin_const (V : E → E) (B : E →L[𝕜] E →L[𝕜] F) (x : E) :
    lieDerivBilin V (fun _ ↦ B) x =
      B.bilinearComp (fderiv 𝕜 V x) (.id 𝕜 E) + B.bilinearComp (.id 𝕜 E) (fderiv 𝕜 V x) := by
  ext u w; simp [lieDerivBilin_apply]

theorem lieDerivBilinWithin_add (hs : UniqueDiffWithinAt 𝕜 s x)
    (hb : DifferentiableWithinAt 𝕜 b s x) (hc : DifferentiableWithinAt 𝕜 c s x) :
    lieDerivBilinWithin V (b + c) s x =
      lieDerivBilinWithin V b s x + lieDerivBilinWithin V c s x := by
  ext u w; simp only [lieDerivBilinWithin_apply, fderivWithin_add hs hb hc, Pi.add_apply, add_apply]
  abel

theorem lieDerivBilin_add (hb : DifferentiableAt 𝕜 b x) (hc : DifferentiableAt 𝕜 c x) :
    lieDerivBilin V (b + c) x = lieDerivBilin V b x + lieDerivBilin V c x := by
  simpa only [lieDerivBilinWithin_univ] using lieDerivBilinWithin_add (V := V)
    uniqueDiffWithinAt_univ hb.differentiableWithinAt hc.differentiableWithinAt

theorem lieDerivBilinWithin_neg (V : E → E) (b : E → E →L[𝕜] E →L[𝕜] F)
    (hs : UniqueDiffWithinAt 𝕜 s x) :
    lieDerivBilinWithin V (-b) s x = -lieDerivBilinWithin V b s x := by
  ext u w; rw [lieDerivBilinWithin_apply, fderivWithin_neg hs]
  simp only [Pi.neg_apply, neg_apply, lieDerivBilinWithin_apply]; abel

@[simp] theorem lieDerivBilin_neg (V : E → E) (b : E → E →L[𝕜] E →L[𝕜] F) :
    lieDerivBilin V (-b) = -lieDerivBilin V b :=
  funext fun _ ↦ by simpa only [lieDerivBilinWithin_univ, Pi.neg_apply] using
    lieDerivBilinWithin_neg V b uniqueDiffWithinAt_univ

theorem lieDerivBilin_sub (hb : DifferentiableAt 𝕜 b x) (hc : DifferentiableAt 𝕜 c x) :
    lieDerivBilin V (b - c) x = lieDerivBilin V b x - lieDerivBilin V c x := by
  rw [sub_eq_add_neg, lieDerivBilin_add hb hc.neg, lieDerivBilin_neg, Pi.neg_apply,
    ← sub_eq_add_neg]

@[simp] theorem lieDerivBilinWithin_smul (a : 𝕜) (b : E → E →L[𝕜] E →L[𝕜] F)
    (hs : UniqueDiffWithinAt 𝕜 s x) :
    lieDerivBilinWithin V (a • b) s x = a • lieDerivBilinWithin V b s x := by
  ext u w; rw [lieDerivBilinWithin_apply, fderivWithin_const_smul_field (f := b) a hs]
  simp [lieDerivBilinWithin_apply, smul_add]

@[simp] theorem lieDerivBilin_smul (a : 𝕜) (b : E → E →L[𝕜] E →L[𝕜] F) :
    lieDerivBilin V (a • b) = a • lieDerivBilin V b :=
  funext fun _ ↦ by simpa only [lieDerivBilinWithin_univ, Pi.smul_apply] using
    lieDerivBilinWithin_smul (V := V) a b uniqueDiffWithinAt_univ

/-- **Leibniz rule** for multiplying a bilinear-form field by a scalar function within `s`. -/
theorem lieDerivBilinWithin_fun_smul {f : E → 𝕜} (hs : UniqueDiffWithinAt 𝕜 s x)
    (hf : DifferentiableWithinAt 𝕜 f s x) (hb : DifferentiableWithinAt 𝕜 b s x) :
    lieDerivBilinWithin V (fun y ↦ f y • b y) s x =
      fderivWithin 𝕜 f s x (V x) • b x + f x • lieDerivBilinWithin V b s x := by
  have hsmul : (fun y ↦ f y • b y) = f • b := funext fun y ↦ (Pi.smul_apply' y f b).symm
  have hdf := (hf.hasFDerivWithinAt.smul hb.hasFDerivWithinAt).fderivWithin hs
  ext u w
  rw [hsmul]
  simp only [lieDerivBilinWithin_apply, hdf, Pi.smul_apply', add_apply, smul_apply,
    smulRight_apply, smul_add]
  abel

/-- **Leibniz rule** for multiplying a bilinear-form field by a scalar function. -/
theorem lieDerivBilin_fun_smul {f : E → 𝕜} (hf : DifferentiableAt 𝕜 f x)
    (hb : DifferentiableAt 𝕜 b x) :
    lieDerivBilin V (fun y ↦ f y • b y) x =
      fderiv 𝕜 f x (V x) • b x + f x • lieDerivBilin V b x := by
  simpa only [lieDerivBilinWithin_univ, fderivWithin_univ] using lieDerivBilinWithin_fun_smul
    (V := V) uniqueDiffWithinAt_univ hf.differentiableWithinAt hb.differentiableWithinAt

theorem lieDerivBilinWithin_add_left (b : E → E →L[𝕜] E →L[𝕜] F) (hs : UniqueDiffWithinAt 𝕜 s x)
    (hU : DifferentiableWithinAt 𝕜 U s x) (hV : DifferentiableWithinAt 𝕜 V s x) :
    lieDerivBilinWithin (U + V) b s x =
      lieDerivBilinWithin U b s x + lieDerivBilinWithin V b s x := by
  ext u w
  simp only [lieDerivBilinWithin_apply, fderivWithin_add hs hU hV, Pi.add_apply, add_apply, map_add]
  abel

theorem lieDerivBilin_add_left (b : E → E →L[𝕜] E →L[𝕜] F)
    (hU : DifferentiableAt 𝕜 U x) (hV : DifferentiableAt 𝕜 V x) :
    lieDerivBilin (U + V) b x = lieDerivBilin U b x + lieDerivBilin V b x := by
  simpa only [lieDerivBilinWithin_univ] using lieDerivBilinWithin_add_left b
    uniqueDiffWithinAt_univ hU.differentiableWithinAt hV.differentiableWithinAt

/-- Negating the vector field negates the Lie derivative within `s`. -/
theorem lieDerivBilinWithin_neg_left (V : E → E) (b : E → E →L[𝕜] E →L[𝕜] F)
    (hs : UniqueDiffWithinAt 𝕜 s x) :
    lieDerivBilinWithin (-V) b s x = -lieDerivBilinWithin V b s x := by
  ext u w; rw [lieDerivBilinWithin_apply, fderivWithin_neg hs]
  simp only [Pi.neg_apply, neg_apply, map_neg, lieDerivBilinWithin_apply]; abel

theorem lieDerivBilin_neg_left (V : E → E) (b : E → E →L[𝕜] E →L[𝕜] F) (x : E) :
    lieDerivBilin (-V) b x = -lieDerivBilin V b x := by
  simpa only [lieDerivBilinWithin_univ] using
    lieDerivBilinWithin_neg_left V b (x := x) uniqueDiffWithinAt_univ

/-- Constant scalar multiplication on the vector field commutes with `lieDerivBilinWithin`. -/
theorem lieDerivBilinWithin_const_smul_left (a : 𝕜) (V : E → E) (b : E → E →L[𝕜] E →L[𝕜] F)
    (hs : UniqueDiffWithinAt 𝕜 s x) :
    lieDerivBilinWithin (a • V) b s x = a • lieDerivBilinWithin V b s x := by
  ext u w; rw [lieDerivBilinWithin_apply, fderivWithin_const_smul_field (f := V) a hs]
  simp [lieDerivBilinWithin_apply, smul_add]

theorem lieDerivBilin_const_smul_left (a : 𝕜) (V : E → E) (b : E → E →L[𝕜] E →L[𝕜] F) (x : E) :
    lieDerivBilin (a • V) b x = a • lieDerivBilin V b x := by
  simpa only [lieDerivBilinWithin_univ] using
    lieDerivBilinWithin_const_smul_left a V b (x := x) uniqueDiffWithinAt_univ

/-- The Lie derivative within `s` commutes with fibrewise transposition. -/
theorem lieDerivBilinWithin_flip (V : E → E) (b : E → E →L[𝕜] E →L[𝕜] F)
    (hs : UniqueDiffWithinAt 𝕜 s x) :
    lieDerivBilinWithin V (fun y ↦ (b y).flip) s x = (lieDerivBilinWithin V b s x).flip := by
  let L := (ContinuousLinearMap.flipₗᵢ 𝕜 E E F).toContinuousLinearEquiv
  have hcomp : (fun y ↦ (b y).flip) = L ∘ b := funext fun y ↦ by
    simp only [L, Function.comp_apply, LinearIsometryEquiv.coe_toContinuousLinearEquiv, coe_flipₗᵢ]
  ext u w
  rw [hcomp, lieDerivBilinWithin_apply, L.comp_fderivWithin hs]
  simp only [L, Function.comp_apply, ContinuousLinearEquiv.coe_coe,
    LinearIsometryEquiv.coe_toContinuousLinearEquiv, comp_apply, coe_flipₗᵢ, flip_apply,
    lieDerivBilinWithin_apply]
  abel

theorem lieDerivBilin_flip (V : E → E) (b : E → E →L[𝕜] E →L[𝕜] F) (x : E) :
    lieDerivBilin V (fun y ↦ (b y).flip) x = (lieDerivBilin V b x).flip := by
  simpa only [lieDerivBilinWithin_univ] using
    lieDerivBilinWithin_flip V b (x := x) uniqueDiffWithinAt_univ

theorem lieDerivBilinWithin_symm (hs : UniqueDiffWithinAt 𝕜 s x) (hx : x ∈ s)
    (hb : ∀ y ∈ s, ∀ u w, b y u w = b y w u) (u w : E) :
    lieDerivBilinWithin V b s x u w = lieDerivBilinWithin V b s x w u := by
  have heq : EqOn (fun y ↦ (b y).flip) b s := fun y hy ↦ by ext a c; exact hb y hy c a
  have h0 : lieDerivBilinWithin V (fun y ↦ (b y).flip) s x = lieDerivBilinWithin V b s x := by
    simp only [lieDerivBilinWithin_def, fderivWithin_congr heq (heq hx), heq hx]
  exact (congrArg (fun d ↦ d w u) (h0.symm.trans (lieDerivBilinWithin_flip V b hs))).symm

theorem lieDerivBilin_symm (hb : ∀ y u w, b y u w = b y w u) (x u w : E) :
    lieDerivBilin V b x u w = lieDerivBilin V b x w u := by
  simpa only [lieDerivBilinWithin_univ] using
    lieDerivBilinWithin_symm (V := V) uniqueDiffWithinAt_univ (mem_univ x) (fun y _ ↦ hb y) u w

/-- `C^m` regularity of `lieDerivBilinWithin` from `C^n` regularity of `V` and `b` (`m + 1 ≤ n`). -/
theorem contDiffWithinAt_lieDerivBilinWithin {m n : WithTop ℕ∞}
    (hV : ContDiffWithinAt 𝕜 n V s x) (hb : ContDiffWithinAt 𝕜 n b s x)
    (hs : UniqueDiffOn 𝕜 s) (hx : x ∈ s) (hmn : m + 1 ≤ n) :
    ContDiffWithinAt 𝕜 m (lieDerivBilinWithin V b s) s x := by
  have hm : m ≤ n := le_self_add.trans hmn
  have hdV := hV.fderivWithin_right hs hmn hx
  have hb' := hb.of_le hm
  have h1 := ((hb.fderivWithin_right hs hmn hx).clm_apply (hV.of_le hm)).add (hb'.clm_comp hdV)
  have h2 := ((compL 𝕜 E E F).flip.contDiff.comp_contDiffWithinAt hdV).clm_comp hb'
  exact (h1.add h2).congr_of_eventuallyEq_of_mem (Eventually.of_forall fun _ ↦ by ext; rfl) hx

theorem contDiffAt_lieDerivBilin {m n : WithTop ℕ∞} (hV : ContDiffAt 𝕜 n V x)
    (hb : ContDiffAt 𝕜 n b x) (hmn : m + 1 ≤ n) : ContDiffAt 𝕜 m (lieDerivBilin V b) x := by
  rw [← contDiffWithinAt_univ, ← lieDerivBilinWithin_univ]
  exact contDiffWithinAt_lieDerivBilinWithin hV.contDiffWithinAt hb.contDiffWithinAt
    uniqueDiffOn_univ (mem_univ x) hmn

theorem contDiff_lieDerivBilin {m n : WithTop ℕ∞} (hV : ContDiff 𝕜 n V) (hb : ContDiff 𝕜 n b)
    (hmn : m + 1 ≤ n) : ContDiff 𝕜 m (lieDerivBilin V b) :=
  contDiff_iff_contDiffAt.2 fun _ ↦ contDiffAt_lieDerivBilin hV.contDiffAt hb.contDiffAt hmn

/-- **The bracket formula** for `lieDerivBilinWithin` on differentiable vector fields `X`, `Y`. -/
theorem lieDerivBilinWithin_apply_vectorField (hs : UniqueDiffWithinAt 𝕜 s x)
    (hb : DifferentiableWithinAt 𝕜 b s x) (hX : DifferentiableWithinAt 𝕜 X s x)
    (hY : DifferentiableWithinAt 𝕜 Y s x) :
    lieDerivBilinWithin V b s x (X x) (Y x) =
      fderivWithin 𝕜 (fun y ↦ b y (X y) (Y y)) s x (V x) -
        b x (lieBracketWithin 𝕜 V X s x) (Y x) - b x (X x) (lieBracketWithin 𝕜 V Y s x) := by
  have hbXY := ((hb.hasFDerivWithinAt.clm_apply hX.hasFDerivWithinAt).clm_apply
    hY.hasFDerivWithinAt).fderivWithin hs
  simp only [lieDerivBilinWithin_apply, lieBracketWithin_eq, hbXY, add_apply, comp_apply,
    flip_apply, map_sub, sub_apply]; abel

/-- **The bracket formula** for `lieDerivBilin` on differentiable vector fields `X` and `Y`. -/
theorem lieDerivBilin_apply_vectorField (hb : DifferentiableAt 𝕜 b x)
    (hX : DifferentiableAt 𝕜 X x) (hY : DifferentiableAt 𝕜 Y x) :
    lieDerivBilin V b x (X x) (Y x) =
      fderiv 𝕜 (fun y ↦ b y (X y) (Y y)) x (V x) -
        b x (lieBracket 𝕜 V X x) (Y x) - b x (X x) (lieBracket 𝕜 V Y x) := by
  simpa only [lieDerivBilinWithin_univ, fderivWithin_univ, lieBracketWithin_univ] using
    lieDerivBilinWithin_apply_vectorField (V := V) uniqueDiffWithinAt_univ
      hb.differentiableWithinAt hX.differentiableWithinAt hY.differentiableWithinAt

end LieDeriv

section PullbackFlow

/-- **The time derivative of a pulled-back family of bilinear forms.** -/
theorem hasDerivAt_pullbackBilinL_fderiv {𝕜 E F : Type*} [NontriviallyNormedField 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    {b : 𝕜 → E → E →L[𝕜] E →L[𝕜] F} {b' : E →L[𝕜] E →L[𝕜] F}
    {ψ : 𝕜 → E → E} {V : E → E} {x : E} {t : 𝕜}
    (hb : DifferentiableAt 𝕜 (fun p : 𝕜 × E ↦ b p.1 p.2) (t, ψ t x))
    (hb' : HasDerivAt (fun s ↦ b s (ψ t x)) b' t) (hψ : HasDerivAt (fun s ↦ ψ s x) (V (ψ t x)) t)
    (hDψ : HasDerivAt (fun s ↦ fderiv 𝕜 (ψ s) x) (fderiv 𝕜 V (ψ t x) ∘L fderiv 𝕜 (ψ t) x) t) :
    HasDerivAt (fun s ↦ ContinuousLinearMap.pullbackBilinL (fderiv 𝕜 (ψ s) x) (b s (ψ s x)))
      (ContinuousLinearMap.pullbackBilinL (fderiv 𝕜 (ψ t) x)
        (b' + lieDerivBilin V (b t) (ψ t x))) t := by
  have hf := hasDerivAt_comp_prodMk hb hψ
  rw [(hasDerivAt_parameterCurve hb).unique hb', ← fderiv_timeSlice hb] at hf
  refine (hf.pullbackBilinL hDψ).congr_deriv ?_
  ext u w; simp [lieDerivBilin_apply, add_assoc]

end PullbackFlow

end TauCeti

end
