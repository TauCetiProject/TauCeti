/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Algebra.SMul
public import TauCeti.Geometry.Manifold.GroupAction.FixedTangentSubspace
public import TauCeti.Geometry.Manifold.SmoothEmbedding.NormalSpace.VectorBundle.Map

/-!
# The isotropy representation on the normal bundle of a submanifold of fixed points

Let a group `K` act on a manifold `N` by differentiable maps, and let `f : M → N` be a smooth
embedding of a submanifold of fixed points: `k • f x = f x` for every `k` and `x`. At `f x` the
differential of `y ↦ k • y` maps `T_(f x) N` to itself, and it fixes every tangent vector of the
submanifold (`TauCeti.SmoothEmbedding.mfderiv_smul_eq_self_of_mem_tangentRange`), so it descends to
the normal space `T_(f x) N / df_x (T_x M)`. This is the **isotropy representation on the normal
space** (`TauCeti.SmoothEmbedding.fixedNormalRepresentation`), Mathlib's quotient representation
`Representation.quotient` of the tangent representation
`TauCeti.tangentRepresentationOfMemFixedPoints` of `K` at the fixed point `f x`. On each fibre it
is the normal map `TauCeti.SmoothEmbedding.normalMap` induced by the commuting square
`(k • ·) ∘ f = f`, so on the normal bundle `k` acts by the bundle map
`TauCeti.SmoothEmbedding.normalBundleMap`, which is smooth when the action is
(`TauCeti.SmoothEmbedding.contMDiff_fixedNormalRepresentation`): `K` acts on the normal bundle of a
submanifold of fixed points by smooth vector bundle automorphisms covering the identity.

## Main definitions

* `TauCeti.SmoothEmbedding.fixedNormalRepresentation`: the representation of `K` on the normal
  space of a submanifold of fixed points.

## Main results

* `TauCeti.SmoothEmbedding.tangentRange_le_fixedTangentSubspace`: the tangent vectors of a
  submanifold of fixed points are fixed.
* `TauCeti.SmoothEmbedding.tangentRange_le_comap_tangentRepresentationOfMemFixedPoints`: the
  tangent representation at a point of the submanifold preserves its tangent space.
* `TauCeti.SmoothEmbedding.fixedNormalRepresentation_eq_normalMap`: the normal representation is
  the normal map of the square `(k • ·) ∘ f = f`.
* `TauCeti.SmoothEmbedding.contMDiff_fixedNormalRepresentation`: it acts on the normal bundle by
  smooth bundle maps.

## References

* M. F. Atiyah, *Convexity and commuting Hamiltonians*, Bull. London Math. Soc. 14 (1982), 1–15
  (the normal bundles of the fixed components and their weights).
-/

public noncomputable section

open Bundle MulAction Filter
open scoped Manifold ContDiff

namespace TauCeti.SmoothEmbedding

variable {E V H G M N : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup V] [NormedSpace ℝ V]
  [TopologicalSpace H] [TopologicalSpace G]
  {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ V G}
  [TopologicalSpace M] [ChartedSpace H M] [TopologicalSpace N] [ChartedSpace G N]
  {n : ℕ∞ω} {K : Type*} [Group K] [MulAction K N]
  (f : SmoothEmbedding I J n M N) (hf : ∀ (k : K) (x : M), k • f x = f x)

include hf in
/-- On a submanifold of fixed points, the differential of the action of `k` fixes every tangent
vector of the submanifold. -/
theorem mfderiv_smul_eq_self_of_mem_tangentRange {k : K} {x : M}
    (hd : MDifferentiableAt J J (fun y : N ↦ k • y) (f x)) (hn : n ≠ 0)
    {w : TangentSpace J (f x)} (hw : w ∈ f.tangentRange x hn) :
    mfderiv J J (fun y : N ↦ k • y) (f x) w = w := by
  obtain ⟨u, rfl⟩ := (f.mem_tangentRange_iff x hn w).1 hw
  have hc := mfderiv_comp_apply x hd (f.contMDiff.mdifferentiableAt hn) u
  rw [show (fun y : N ↦ k • y) ∘ f = f from funext (hf k)] at hc
  exact hc.symm

include hf in
/-- **The tangent vectors of a submanifold of fixed points are fixed.** For an action by
differentiable maps, the tangent space of a submanifold of fixed points lies in the fixed tangent
subspace. -/
theorem tangentRange_le_fixedTangentSubspace (x : M) (hn : n ≠ 0)
    (hd : ∀ k : K, MDifferentiableAt J J (fun y : N ↦ k • y) (f x)) :
    f.tangentRange x hn ≤ fixedTangentSubspace J K (f x) :=
  fun _ hw ↦ mem_fixedTangentSubspace.2 fun k _ ↦
    f.mfderiv_smul_eq_self_of_mem_tangentRange hf (hd k) hn hw

include hf in
/-- The tangent representation of `K` at a point `f x` of a submanifold of fixed points preserves
the tangent space of the submanifold. -/
theorem tangentRange_le_comap_tangentRepresentationOfMemFixedPoints (x : M) (hn : n ≠ 0)
    (hd : ∀ k : K, MDifferentiableAt J J (fun y : N ↦ k • y) (f x)) (k : K) :
    f.tangentRange x hn ≤ (f.tangentRange x hn).comap
      (tangentRepresentationOfMemFixedPoints (mem_fixedPoints.2 fun g ↦ hf g x) hd k) :=
  fun w hw ↦ by
    rw [Submodule.mem_comap, tangentRepresentationOfMemFixedPoints_apply,
      f.mfderiv_smul_eq_self_of_mem_tangentRange hf (hd k) hn hw]
    exact hw

/-- The **isotropy representation on the normal space** of a submanifold of fixed points: `k`
acts on the class of a tangent vector `w` at `f x` as the class of `d(k •)_(f x) w`. It is the
quotient of the tangent representation of `K` at the fixed point `f x` by the tangent space of the
submanifold, which it fixes. -/
def fixedNormalRepresentation (x : M) (hn : n ≠ 0)
    (hd : ∀ k : K, MDifferentiableAt J J (fun y : N ↦ k • y) (f x)) :
    Representation ℝ K (f.NormalSpace x hn) :=
  (tangentRepresentationOfMemFixedPoints (mem_fixedPoints.2 fun k ↦ hf k x) hd).quotient
    (f.tangentRange x hn) (f.tangentRange_le_comap_tangentRepresentationOfMemFixedPoints hf x hn hd)

/-- The normal representation acts on the class of `w` as the class of `d(k •)_(f x) w`. -/
@[simp]
theorem fixedNormalRepresentation_normalClass
    (x : M) (hn : n ≠ 0) (hd : ∀ k : K, MDifferentiableAt J J (fun y : N ↦ k • y) (f x))
    (k : K) (w : TangentSpace J (f x)) :
    f.fixedNormalRepresentation hf x hn hd k (f.normalClass x hn w) =
      f.normalClass x hn (mfderiv J J (fun y : N ↦ k • y) (f x) w) := by
  rw [normalClass_def, ← tangentRepresentationOfMemFixedPoints_apply (fun k ↦ hf k x) hd]
  -- The quotient representation acts on `mkQ w` by `Submodule.mapQ`, which is `mkQ` of the image.
  rfl

/-- The normal representation of `k` is the normal map induced by the commuting square
`(k • ·) ∘ f = f ∘ id`. -/
theorem fixedNormalRepresentation_eq_normalMap
    (x : M) (hn : n ≠ 0) (hd : ∀ k : K, MDifferentiableAt J J (fun y : N ↦ k • y) (f x))
    (k : K) :
    f.fixedNormalRepresentation hf x hn hd k =
      (f.normalMap f hn hn (u := _root_.id) (v := fun y : N ↦ k • y) (x := x)
        (EventuallyEq.of_eq (funext (hf k)))).toLinearMap := by
  ext ν
  obtain ⟨w, rfl⟩ := f.normalClass_surjective x hn ν
  simp only [fixedNormalRepresentation_normalClass, ContinuousLinearMap.coe_coe,
    normalMap_normalClass]
  exact congrArg (f.normalClass x hn) (eq_of_heq (heq_tangentSpaceCast (hf k x) _)).symm

/-- The action of `k` on the normal bundle, the bundle map induced by the square
`(k • ·) ∘ f = f ∘ id`, acts on each fibre by the normal representation. -/
theorem normalBundleMap_smul_apply (hn : n ≠ 0)
    (hd : ∀ (x : M) (k : K), MDifferentiableAt J J (fun y : N ↦ k • y) (f x)) (k : K)
    {P : Type*} (p : TotalSpace P fun x ↦ f.NormalSpace x hn) :
    f.normalBundleMap (K := P) (K' := P) f hn hn (u := _root_.id) (v := fun y : N ↦ k • y)
        (funext (hf k)) p =
      ⟨p.proj, f.fixedNormalRepresentation hf p.proj hn (hd p.proj) k p.snd⟩ := by
  rw [normalBundleMap_apply, fixedNormalRepresentation_eq_normalMap]
  -- The base map of the square is the identity.
  rfl

/-- **`K` acts on the normal bundle of a submanifold of fixed points by smooth bundle maps.** If
`K` acts by `C^(r + 1)` maps and the embedding is `C^(r + 1)`, then each `k` acts on the normal
bundle, fibrewise by the normal representation, by a `C^r` map covering the identity. -/
theorem contMDiff_fixedNormalRepresentation [FiniteDimensional ℝ E] [FiniteDimensional ℝ V]
    {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P] {r : ℕ∞ω}
    [IsManifold I (r + 1) M] [IsManifold J (r + 1) N] [ContMDiffConstSMul J (r + 1) K N]
    (hn : n ≠ 0) (hrn : r + 1 ≤ n)
    (hdim : Module.finrank ℝ P = Module.finrank ℝ V - Module.finrank ℝ E) (k : K) :
    haveI : IsManifold I 1 M := .of_le (n := r + 1) le_add_self
    haveI : IsManifold J 1 N := .of_le (n := r + 1) le_add_self
    letI := f.normalSpaceFiberBundle hn hdim
    ContMDiff (I.prod 𝓘(ℝ, P)) (I.prod 𝓘(ℝ, P)) r
      fun p : TotalSpace P (fun x ↦ f.NormalSpace x hn) ↦
        (⟨p.proj, f.fixedNormalRepresentation hf p.proj hn
          (fun g ↦ ContMDiffConstSMul.mdifferentiable_const_smul (n := r + 1) (by simp) g _)
          k p.snd⟩ : TotalSpace P fun x ↦ f.NormalSpace x hn) := by
  have : IsManifold I 1 M := .of_le (n := r + 1) le_add_self
  have : IsManifold J 1 N := .of_le (n := r + 1) le_add_self
  let := f.normalSpaceFiberBundle hn hdim
  have hc := f.contMDiff_normalBundleMap (P := P) (P' := P) (J := J) (J' := J) f hn hn hrn hrn
    hdim hdim (u := _root_.id) (v := fun y : N ↦ k • y) (contMDiff_const_smul k) (funext (hf k))
  refine hc.congr fun p ↦ ?_
  rw [f.normalBundleMap_smul_apply hf hn fun _ g ↦
    ContMDiffConstSMul.mdifferentiable_const_smul (n := r + 1) (by simp) g _]

end TauCeti.SmoothEmbedding
