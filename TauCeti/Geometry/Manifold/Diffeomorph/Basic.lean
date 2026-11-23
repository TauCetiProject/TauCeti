/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.LocalDiffeomorph
public import Mathlib.Geometry.Manifold.VectorField.Pullback

-- Access the constructor only to supply its missing public characterization.
import all Mathlib.Geometry.Manifold.LocalDiffeomorph

/-!
# Differentials of diffeomorphisms

The differentials of a diffeomorphism and its inverse undo each other, so the differential is
nonzero wherever the tangent space is nontrivial, and the differential of a diffeomorphism undoes
the pullback of vector fields along it.
Differentiability at a point is also preserved by precomposition and postcomposition with a
diffeomorphism, so the chain rule for such compositions holds without differentiability
assumptions, including for maps conjugated by a diffeomorphism near a point, injectivity of the
differential is preserved by precomposition and postcomposition, and the tangent images of a map,
the ranges of its differentials, are unchanged by precomposition with a diffeomorphism and are
mapped by the differential under postcomposition.
These facts support inverse isometries, calibrated immersions, and transport of curve
differentiability through diffeomorphisms. The underlying equivalence and function of a
diffeomorphism viewed as a partial diffeomorphism are also characterized, for composition with
partial coordinates, and pulling back a `C^m` maximal-atlas chart along a `C^n` diffeomorphism
(`m ≤ n`) preserves membership in the maximal `C^m` atlas (`Diffeomorph.trans_mem_maximalAtlas`,
`Diffeomorph.trans_mem_maximalAtlas_iff`).
The linear map underlying the differential of a diffeomorphism viewed as a linear equivalence
(`Diffeomorph.mfderivToContinuousLinearEquiv_toLinearMap`) is the differential.
-/

public section

open Bundle Manifold Filter
open scoped ContDiff Manifold Topology

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
  {H' : Type*} [TopologicalSpace H'] {J : ModelWithCorners 𝕜 F H'}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {N : Type*} [TopologicalSpace N] [ChartedSpace H' N]
  {n : ℕ∞ω}

namespace Diffeomorph

/-- The partial equivalence underlying a diffeomorphism viewed as a partial diffeomorphism
is its everywhere-defined equivalence. -/
@[simp]
theorem toPartialDiffeomorph_toPartialEquiv (h : M ≃ₘ^n⟮I, J⟯ N) :
    h.toPartialDiffeomorph.toPartialEquiv = h.toEquiv.toPartialEquiv := (rfl)

/-- A diffeomorphism viewed as a partial diffeomorphism has the diffeomorphism as its function.
Not a simp lemma: `toPartialDiffeomorph_toPartialEquiv` already lets simp prove it. -/
theorem coe_toPartialDiffeomorph (h : M ≃ₘ^n⟮I, J⟯ N) : ⇑h.toPartialDiffeomorph = h := (rfl)

/-- Pulling back a chart `φ` of the maximal `C^m` atlas of `N'` along a `C^n` diffeomorphism
`h : M ≃ₘ^n⟮I, I⟯ N'` (`m ≤ n`) produces a chart of the maximal `C^m` atlas of `M`. -/
theorem trans_mem_maximalAtlas {N' : Type*} [TopologicalSpace N'] [ChartedSpace H N']
    {m : ℕ∞ω} [IsManifold I m M] (h : M ≃ₘ^n⟮I, I⟯ N') (hm : m ≤ n)
    {φ : OpenPartialHomeomorph N' H} (hφ : φ ∈ IsManifold.maximalAtlas I m N') :
    h.toHomeomorph.toOpenPartialHomeomorph.trans φ ∈ IsManifold.maximalAtlas I m M := by
  rw [IsManifold.mem_maximalAtlas_iff_contMDiffOn]
  exact ⟨(contMDiffOn_of_mem_maximalAtlas hφ).comp (h.contMDiff.of_le hm).contMDiffOn
      fun _ hx ↦ hx.2,
    (h.symm.contMDiff.of_le hm).comp_contMDiffOn
      ((contMDiffOn_symm_of_mem_maximalAtlas hφ).mono Set.inter_subset_left)⟩

/-- Pulling back `φ` along a `C^n` diffeomorphism `h : M ≃ₘ^n⟮I, I⟯ N'` (`m ≤ n`) produces a chart
of the maximal `C^m` atlas of `M` iff `φ` lies in the maximal `C^m` atlas of `N'`. -/
theorem trans_mem_maximalAtlas_iff {N' : Type*} [TopologicalSpace N'] [ChartedSpace H N']
    {m : ℕ∞ω} [IsManifold I m M] [IsManifold I m N'] (h : M ≃ₘ^n⟮I, I⟯ N') (hm : m ≤ n)
    {φ : OpenPartialHomeomorph N' H} :
    h.toHomeomorph.toOpenPartialHomeomorph.trans φ ∈ IsManifold.maximalAtlas I m M ↔
      φ ∈ IsManifold.maximalAtlas I m N' := by
  refine ⟨fun hφ ↦ ?_, h.trans_mem_maximalAtlas hm⟩
  have heq : h.symm.toHomeomorph.toOpenPartialHomeomorph.trans
      (h.toHomeomorph.toOpenPartialHomeomorph.trans φ) = φ := by
    ext x <;> simp
  simpa only [heq] using h.symm.trans_mem_maximalAtlas hm hφ

/-- The differentials of a diffeomorphism and its inverse compose to the identity. -/
@[simp]
theorem mfderiv_apply_mfderiv_symm_apply (h : M ≃ₘ^n⟮I, J⟯ N) (hn : n ≠ 0)
    (x : M) (v : TangentSpace J (h x)) :
    mfderiv I J h x (mfderiv J I h.symm (h x) v) = v := by
  have hid : (h : M → N) ∘ h.symm = id := funext h.apply_symm_apply
  have hder : mfderiv J J ((h : M → N) ∘ h.symm) (h x) v =
      mfderiv I J h (h.symm (h x)) (mfderiv J I h.symm (h x) v) :=
    mfderiv_comp_apply (h x) (h.mdifferentiable hn (h.symm (h x)))
      (h.symm.mdifferentiable hn (h x)) v
  rw [hid, mfderiv_id, h.symm_apply_apply] at hder
  exact hder.symm

/-- The differential of the inverse undoes the differential of a diffeomorphism. -/
@[simp]
theorem mfderiv_symm_apply_mfderiv_apply (h : M ≃ₘ^n⟮I, J⟯ N) (hn : n ≠ 0)
    (x : M) (v : TangentSpace I x) :
    mfderiv J I h.symm (h x) (mfderiv I J h x v) = v := by
  have hss : h.symm.symm = h := Diffeomorph.ext (fun _ => rfl)
  have hh := mfderiv_apply_mfderiv_symm_apply h.symm hn (h x) v
  rw [hss, h.symm_apply_apply] at hh
  exact hh

/-- The differential of a diffeomorphism at a point with a nontrivial tangent space is nonzero. -/
theorem mfderiv_ne_zero (h : M ≃ₘ^n⟮I, J⟯ N) (hn : n ≠ 0) {x : M}
    [Nontrivial (TangentSpace J (h x))] : mfderiv I J h x ≠ 0 := by
  intro h0
  obtain ⟨v, hv⟩ := exists_ne (0 : TangentSpace J (h x))
  have hv' := h.mfderiv_apply_mfderiv_symm_apply hn x v
  rw [h0] at hv'
  exact hv (hv'.symm.trans (zero_apply _))

/-- The differential of a diffeomorphism maps the pullback of a vector field at `x` to the value
of the field at `h x`. -/
@[simp]
theorem mfderiv_apply_mpullback (h : M ≃ₘ^n⟮I, J⟯ N) (hn : n ≠ 0) (V : Π y : N, TangentSpace J y)
    (x : M) : mfderiv I J h x (VectorField.mpullback I J h V x) = V (h x) :=
  (h.isInvertible_mfderiv hn).self_apply_inverse _

/-- Applying the tangent map of a diffeomorphism and then that of its inverse returns the
original tangent vector. -/
@[simp]
theorem tangentMap_symm_apply (h : M ≃ₘ^n⟮I, J⟯ N) (hn : n ≠ 0)
    (z : TangentBundle I M) :
    tangentMap J I h.symm (tangentMap I J h z) = z := by
  rw [← tangentMap_comp_at z ((h.symm.mdifferentiable hn) (h z.proj))
    ((h.mdifferentiable hn) z.proj)]
  have hinv : (h.symm : N → M) ∘ h = id := funext h.symm_apply_apply
  rw [hinv]
  exact congrFun tangentMap_id z

/-- Applying the tangent map of the inverse of a diffeomorphism and then that of the
diffeomorphism returns the original tangent vector. -/
@[simp]
theorem tangentMap_apply_symm (h : M ≃ₘ^n⟮I, J⟯ N) (hn : n ≠ 0)
    (z : TangentBundle J N) :
    tangentMap I J h (tangentMap J I h.symm z) = z := by
  have hss : h.symm.symm = h := Diffeomorph.ext fun _ ↦ rfl
  have hh := tangentMap_symm_apply h.symm hn z
  rw [hss] at hh
  exact hh

/-- The tangent map of the inverse acts on a fibre by the inverse differential. This holds
for every nonzero differentiability order, including finite orders. -/
theorem tangentMap_symm_mk (h : M ≃ₘ^n⟮I, J⟯ N) (hn : n ≠ 0)
    (x : M) (w : TangentSpace J (h x)) :
    tangentMap J I h.symm (Bundle.TotalSpace.mk' F (h x) w) =
      Bundle.TotalSpace.mk' E x ((mfderiv I J h x).inverse w) := by
  have hleft : Function.LeftInverse (tangentMap J I h.symm) (tangentMap I J h) :=
    h.tangentMap_symm_apply hn
  apply hleft.injective
  rw [h.tangentMap_apply_symm hn]
  exact congrArg (Bundle.TotalSpace.mk' F (h x))
    ((h.isInvertible_mfderiv hn).self_apply_inverse w).symm

/-- Postcomposition with a diffeomorphism preserves differentiability at a point. -/
theorem mdifferentiableAt_comp_iff (h : M ≃ₘ^n⟮I, J⟯ N) (hn : n ≠ 0)
    {E' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
    {H'' : Type*} [TopologicalSpace H''] {K : ModelWithCorners 𝕜 E' H''}
    {P : Type*} [TopologicalSpace P] [ChartedSpace H'' P]
    {f : P → M} {x : P} :
    MDifferentiableAt K J (h ∘ f) x ↔ MDifferentiableAt K I f x := by
  constructor
  · intro hf
    have hg := (h.symm.mdifferentiable hn (h (f x))).comp x hf
    have heq : (h.symm : N → M) ∘ ((h : M → N) ∘ f) = f := by
      funext y
      exact h.symm_apply_apply (f y)
    rw [heq] at hg
    exact hg
  · intro hf
    exact (h.mdifferentiable hn (f x)).comp x hf

/-- Precomposition with a diffeomorphism preserves differentiability at the corresponding point. -/
theorem mdifferentiableAt_comp_diffeomorph_iff (h : M ≃ₘ^n⟮I, J⟯ N) (hn : n ≠ 0)
    {E' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
    {H'' : Type*} [TopologicalSpace H''] {K : ModelWithCorners 𝕜 E' H''}
    {P : Type*} [TopologicalSpace P] [ChartedSpace H'' P]
    {f : N → P} {x : M} :
    MDifferentiableAt I K (f ∘ h) x ↔ MDifferentiableAt J K f (h x) := by
  constructor
  · intro hfh
    have hfh' : MDifferentiableAt I K (f ∘ h) (h.symm (h x)) := by
      rwa [h.symm_apply_apply]
    have hg := hfh'.comp (h x) (h.symm.mdifferentiable hn (h x))
    have heq : (f ∘ h) ∘ h.symm = f := funext fun y ↦ congrArg f (h.apply_symm_apply y)
    rwa [heq] at hg
  · intro hf
    exact hf.comp x (h.mdifferentiable hn x)

/-- The linear map underlying the differential of a diffeomorphism, viewed as a linear equivalence,
is the differential. -/
theorem mfderivToContinuousLinearEquiv_toLinearMap (h : M ≃ₘ^n⟮I, J⟯ N) (hn : n ≠ 0) (x : M) :
    (h.mfderivToContinuousLinearEquiv hn x).toLinearEquiv.toLinearMap =
      (mfderiv I J h x).toLinearMap :=
  congrArg ContinuousLinearMap.toLinearMap (h.mfderivToContinuousLinearEquiv_coe hn)

section TangentImage

variable {E' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
  {H'' : Type*} [TopologicalSpace H''] {K : ModelWithCorners 𝕜 E' H''}
  {P : Type*} [TopologicalSpace P] [ChartedSpace H'' P]

/-- **Chain rule for postcomposition with a diffeomorphism.** The differential of `h ∘ f` at `x`
is `dh ∘ df`. No differentiability of `f` is assumed: when `f` is not differentiable at `x`,
neither is `h ∘ f`, and both sides are zero. -/
theorem mfderiv_diffeomorph_comp (h : M ≃ₘ^n⟮I, J⟯ N) (hn : n ≠ 0) (f : P → M) (x : P) :
    mfderiv K J (h ∘ f) x = (mfderiv I J h (f x)).comp (mfderiv K I f x) := by
  by_cases hf : MDifferentiableAt K I f x
  · exact mfderiv_comp x (h.mdifferentiable hn (f x)) hf
  · have hhf : ¬MDifferentiableAt K J (h ∘ f) x := (h.mdifferentiableAt_comp_iff hn).not.mpr hf
    rw [mfderiv_zero_of_not_mdifferentiableAt hf, mfderiv_zero_of_not_mdifferentiableAt hhf,
      ContinuousLinearMap.comp_zero]

/-- **Chain rule for precomposition with a diffeomorphism.** The differential of `f ∘ h` at `x`
is `df ∘ dh`. No differentiability of `f` is assumed: when `f` is not differentiable at `h x`,
`f ∘ h` is not differentiable at `x`, and both sides are zero. -/
theorem mfderiv_comp_diffeomorph (h : M ≃ₘ^n⟮I, J⟯ N) (hn : n ≠ 0) (f : N → P) (x : M) :
    mfderiv I K (f ∘ h) x = (mfderiv J K f (h x)).comp (mfderiv I J h x) := by
  by_cases hf : MDifferentiableAt J K f (h x)
  · exact mfderiv_comp x hf (h.mdifferentiable hn x)
  · have hfh : ¬MDifferentiableAt I K (f ∘ h) x :=
      (h.mdifferentiableAt_comp_diffeomorph_iff hn).not.mpr hf
    rw [mfderiv_zero_of_not_mdifferentiableAt hf, mfderiv_zero_of_not_mdifferentiableAt hfh,
      ContinuousLinearMap.zero_comp]

/-- **Chain rule for precomposition with a diffeomorphism, for vector-valued functions.** The
differential of `f ∘ h` at `x`, with values in `E'`, is `df ∘ dh`. No differentiability of `f` is
assumed. -/
theorem mvfderiv_comp_diffeomorph (h : M ≃ₘ^n⟮I, J⟯ N) (hn : n ≠ 0) (f : N → E') (x : M) :
    mvfderiv I (f ∘ h) x = (mvfderiv J f (h x)).comp (mfderiv I J h x) := by
  rw [mvfderiv, mvfderiv, h.mfderiv_comp_diffeomorph hn, ContinuousLinearMap.comp_assoc,
    Function.comp_apply]

/-- The linear equivalence `Diffeomorph.mfderivToContinuousLinearEquiv` acts on tangent vectors
by the differential. -/
@[simp]
theorem mfderivToContinuousLinearEquiv_apply (h : M ≃ₘ^n⟮I, J⟯ N) (hn : n ≠ 0) (x : M)
    (v : TangentSpace I x) : h.mfderivToContinuousLinearEquiv hn x v = mfderiv I J h x v := by
  rw [← ContinuousLinearEquiv.coe_coe, h.mfderivToContinuousLinearEquiv_coe hn]

/-- **Chain rule for conjugation by a diffeomorphism.** If `h ∘ f` and `g ∘ h` agree near `x`,
then `dg_(h x) ∘ dh_x = dh_(f x) ∘ df_x`. No differentiability of `f` or `g` is assumed. -/
theorem mfderiv_apply_mfderiv_of_comp_eventuallyEq (h : M ≃ₘ^n⟮I, J⟯ N) (hn : n ≠ 0)
    {f : M → M} {g : N → N} {x : M} (hfg : h ∘ f =ᶠ[𝓝 x] g ∘ h) (v : TangentSpace I x) :
    mfderiv J J g (h x) (mfderiv I J h x v) = mfderiv I J h (f x) (mfderiv I I f x v) := by
  have h₁ := h.mfderiv_diffeomorph_comp (K := I) hn f x
  have h₂ := h.mfderiv_comp_diffeomorph (K := J) hn g x
  have h₃ := congrArg (· v) (hfg.mfderiv_eq (I := I) (I' := J))
  simp only [h₁, h₂, ContinuousLinearMap.comp_apply] at h₃
  exact h₃.symm

/-- Postcomposition with a diffeomorphism maps tangent images by its differential: the range of
the differential of `h ∘ f` at `x` is the image of the range of the differential of `f` under the
linear equivalence `dh`, `Diffeomorph.mfderivToContinuousLinearEquiv`.
No differentiability of `f` is assumed. -/
theorem range_mfderiv_diffeomorph_comp (h : M ≃ₘ^n⟮I, J⟯ N) (hn : n ≠ 0) (f : P → M) (x : P) :
    LinearMap.range (mfderiv K J (h ∘ f) x).toLinearMap =
      (LinearMap.range (mfderiv K I f x).toLinearMap).map
        (h.mfderivToContinuousLinearEquiv hn (f x)).toLinearEquiv.toLinearMap := by
  rw [h.mfderiv_diffeomorph_comp hn, ContinuousLinearMap.toLinearMap_comp, LinearMap.range_comp,
    h.mfderivToContinuousLinearEquiv_toLinearMap hn]

/-- Precomposition with a diffeomorphism does not change tangent images: the range of the
differential of `f ∘ h` at `x` is the range of the differential of `f` at `h x`. No
differentiability of `f` is assumed. -/
theorem range_mfderiv_comp_diffeomorph (h : M ≃ₘ^n⟮I, J⟯ N) (hn : n ≠ 0) (f : N → P) (x : M) :
    LinearMap.range (mfderiv I K (f ∘ h) x).toLinearMap =
      LinearMap.range (mfderiv J K f (h x)).toLinearMap := by
  rw [h.mfderiv_comp_diffeomorph hn, ContinuousLinearMap.toLinearMap_comp,
    LinearMap.range_comp_of_range_eq_top]
  exact LinearMap.range_eq_top.mpr (h.isInvertible_mfderiv hn).surjective

/-- Postcomposition with a diffeomorphism preserves injectivity of the differential at the point.
No differentiability of `f` is assumed. -/
theorem mfderiv_diffeomorph_comp_injective_iff (h : M ≃ₘ^n⟮I, J⟯ N) (hn : n ≠ 0) {f : P → M}
    {x : P} :
    Function.Injective (mfderiv K J (h ∘ f) x) ↔ Function.Injective (mfderiv K I f x) := by
  rw [h.mfderiv_diffeomorph_comp hn, ContinuousLinearMap.coe_comp]
  exact (h.isInvertible_mfderiv hn).injective.of_comp_iff _

/-- Precomposition with a diffeomorphism preserves injectivity of the differential at the
corresponding point. No differentiability of `f` is assumed. -/
theorem mfderiv_comp_diffeomorph_injective_iff (h : M ≃ₘ^n⟮I, J⟯ N) (hn : n ≠ 0) {f : N → P}
    {x : M} :
    Function.Injective (mfderiv I K (f ∘ h) x) ↔ Function.Injective (mfderiv J K f (h x)) := by
  rw [h.mfderiv_comp_diffeomorph hn, ContinuousLinearMap.coe_comp]
  exact Function.Injective.of_comp_iff' _ (h.isInvertible_mfderiv hn).bijective

end TangentImage

end Diffeomorph

end
