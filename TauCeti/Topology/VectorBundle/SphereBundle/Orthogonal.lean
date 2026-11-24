/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
public import TauCeti.Topology.VectorBundle.IdempotentRange
public import TauCeti.Topology.VectorBundle.SphereBundle.LocallyTrivial
import TauCeti.Analysis.InnerProductSpace.Orthonormal.Family
import TauCeti.Analysis.InnerProductSpace.Projection.Basic
import TauCeti.Topology.Homotopy.SerreFibration.FiberBundle

/-!
# Unit spheres orthogonal to a continuous orthonormal frame

Let `E` be a finite-dimensional real inner product space and `f : X → ι → E` a continuous family
of orthonormal frames `f x = (f x i)ᵢ` over a topological space `X`, with `ι` finite. The pairs
`(x, q)` of a point `x` and a unit vector `q` orthogonal to every `f x i` form a closed subspace
`orthogonalSphereBundle f` of `X × Sᴱ`, where `Sᴱ` is the unit sphere of `E`
(`TauCeti.orthogonalSphereBundle`). Its fibre over `x` is the unit sphere of the orthogonal
complement of the span of the frame `f x`, a sphere of dimension `dim E - card ι - 1`.

This file shows that the projection to `X` (`TauCeti.orthogonalSphereBundleProj`) is locally
trivial, with fibre the unit sphere of any real normed space `F` of dimension `dim E - card ι`
(`TauCeti.exists_trivialization_orthogonalSphereBundleProj`). Consequently it is a Serre fibration
(`TauCeti.TopCat.mem_serreFibrations_orthogonalSphereBundleProj`) and a Hurewicz fibration over a
normal paracompact base (`TauCeti.isHurewiczFibration_orthogonalSphereBundleProj`).

Such families of spheres are the parameter spaces of families of two-spheres swept out by tangent
frames of a round sphere: for two orthonormal tangent vector fields `u`, `v` on `Sⁿ`, the space of
equators `{(x, q) | q ⊥ u x, v x}` of Barraud–Damian–Humilière–Oancea's Example 6.20 is the case
`f x = (u x, v x)`.

The orthogonal projections `p x = 1 - P x`, where `P x` is the orthogonal projection onto the span
of `f x`, form a continuous family of idempotents, since `P x w = ∑ᵢ ⟪f x i, w⟫ f x i`
(`Orthonormal.starProjection_apply_eq_sum`). Their ranges, the orthogonal complements, form a
vector bundle with the topology of a subspace of `X × E` (`TauCeti.rangeFiberBundle`), whose unit
sphere bundle is locally trivial (`TauCeti.exists_trivialization_sphereBundleProj`). Forgetting the
fibre structure identifies that sphere bundle with `orthogonalSphereBundle f`, which carries the
charts over.

## Main declarations

* `TauCeti.orthogonalSphereBundle f`: the pairs `(x, q)` with `q` a unit vector orthogonal to
  `f x`.
* `TauCeti.orthogonalSphereBundleProj f`: its projection to `X`.
* `TauCeti.exists_trivialization_orthogonalSphereBundleProj`: the projection is locally trivial.
* `TauCeti.TopCat.mem_serreFibrations_orthogonalSphereBundleProj`,
  `TauCeti.isHurewiczFibration_orthogonalSphereBundleProj`: it is a Serre fibration, and a
  Hurewicz fibration over a normal paracompact base.

## References

* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Floer homology with DG coefficients.
  Applications to cotangent bundles*, arXiv:2404.07953, §6.4.2, Definition 6.14 and
  Example 6.20.
-/

public section

noncomputable section

open Bundle Metric Module Set Topology
open scoped RealInnerProductSpace

universe u w

namespace TauCeti

variable {X : Type u} {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {ι : Type*}

/-! ### The space of orthogonal unit vectors -/

/-- The pairs `(x, q)` of a point `x` and a unit vector `q` orthogonal to every vector `f x i` of
the frame `f x`. When the frames are orthonormal, the fibre over `x` is the unit sphere of the
orthogonal complement of the span of `f x`. -/
def orthogonalSphereBundle (f : X → ι → E) : Set (X × sphere (0 : E) 1) :=
  {p | ∀ i, ⟪(p.2 : E), f p.1 i⟫ = 0}

variable {f : X → ι → E}

@[simp]
theorem mem_orthogonalSphereBundle {p : X × sphere (0 : E) 1} :
    p ∈ orthogonalSphereBundle f ↔ ∀ i, ⟪(p.2 : E), f p.1 i⟫ = 0 :=
  Iff.rfl

section Topology

variable [TopologicalSpace X]

theorem isClosed_orthogonalSphereBundle (hf : Continuous f) :
    IsClosed (orthogonalSphereBundle f) := by
  simp only [orthogonalSphereBundle, ofPred_forall]
  exact isClosed_iInter fun i ↦ isClosed_eq (by fun_prop) continuous_const

variable (f) in
/-- The projection `(x, q) ↦ x` of `TauCeti.orthogonalSphereBundle f`. -/
def orthogonalSphereBundleProj : C(orthogonalSphereBundle f, X) :=
  ⟨fun p ↦ (p : X × sphere (0 : E) 1).1, by fun_prop⟩

@[simp]
theorem orthogonalSphereBundleProj_apply (p : orthogonalSphereBundle f) :
    orthogonalSphereBundleProj f p = (p : X × sphere (0 : E) 1).1 :=
  (rfl)

end Topology

/-! ### The orthogonal complements as the ranges of projections -/

section Complement

variable [FiniteDimensional ℝ E]

variable (f) in
/-- The orthogonal projection onto the orthogonal complement of the span of `f x`. -/
private def complementProjection (x : X) : E →L[ℝ] E :=
  (Submodule.span ℝ (range (f x)))ᗮ.starProjection

private theorem mem_range_complementProjection_iff {x : X} {w : E} :
    w ∈ (complementProjection f x).range ↔ ∀ i, ⟪w, f x i⟫ = 0 := by
  simp [complementProjection, ← Submodule.span_singleton_le_iff_mem, ← Submodule.isOrtho_iff_le,
    Submodule.isOrtho_span]

/-- The unit sphere bundle of the orthogonal complements, with the topology of a subspace of
`X × E`, is `TauCeti.orthogonalSphereBundle f`. -/
private def sphereBundleHomeomorph [TopologicalSpace X] (F : Type*) :
    sphereBundle F (fun x ↦ (complementProjection f x).range) ≃ₜ orthogonalSphereBundle f where
  toFun v := ⟨(v.val.proj, ⟨(v.val.snd : E), mem_sphere_zero_iff_norm.2
      (mem_sphereBundle.1 v.property)⟩),
    mem_orthogonalSphereBundle.2 (mem_range_complementProjection_iff.1 (Subtype.prop v.val.snd))⟩
  invFun q := ⟨⟨q.val.1, ⟨q.val.2, mem_range_complementProjection_iff.2 q.property⟩⟩,
    mem_sphereBundle.2 (norm_eq_of_mem_sphere q.val.2)⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := by
    have h := (isEmbedding_totalSpace_range F (complementProjection f)).continuous.comp
      (continuous_subtypeVal (p := (· ∈ sphereBundle F _)))
    exact (h.fst.prodMk (h.snd.subtype_mk _)).subtype_mk _
  continuous_invFun := by
    refine (IsInducing.subtypeVal.continuous_iff).2 <|
      (isEmbedding_totalSpace_range F (complementProjection f)).continuous_iff.2 ?_
    exact (continuous_fst.comp continuous_subtypeVal).prodMk
      (continuous_subtypeVal.comp (continuous_snd.comp continuous_subtypeVal))

variable [Fintype ι]

omit [Fintype ι] in
private theorem continuous_complementProjection [Finite ι] [TopologicalSpace X]
    (hf : Continuous f) (ho : ∀ x, Orthonormal ℝ (f x)) : Continuous (complementProjection f) := by
  unfold complementProjection
  simp only [Submodule.starProjection_orthogonal']
  exact continuous_const.sub (Orthonormal.continuous_starProjection hf ho fun _ ↦ rfl)

/-- The model fibre `F` is isomorphic to every orthogonal complement. -/
private theorem nonempty_continuousLinearEquiv_range {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] [FiniteDimensional ℝ F] (ho : ∀ x, Orthonormal ℝ (f x))
    (hF : finrank ℝ F + Fintype.card ι = finrank ℝ E) (x : X) :
    Nonempty (F ≃L[ℝ] (complementProjection f x).range) :=
  ⟨ContinuousLinearEquiv.ofFinrankEq (by
    rw [complementProjection, Submodule.range_starProjection,
      (ho x).linearIndependent.finrank_orthogonal_span]
    omega)⟩

end Complement

/-! ### Local triviality -/

variable [TopologicalSpace X] [Fintype ι] [FiniteDimensional ℝ E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]

/-- **The unit spheres orthogonal to a continuous orthonormal frame form a locally trivial
bundle.** If the frames `f x` are orthonormal and depend continuously on `x`, every point of `X`
lies in the base set of a chart of the projection `TauCeti.orthogonalSphereBundleProj f` with
fibre the unit sphere of any real normed space `F` of dimension `dim E - card ι`. -/
theorem exists_trivialization_orthogonalSphereBundleProj (hf : Continuous f)
    (ho : ∀ x, Orthonormal ℝ (f x)) (hF : finrank ℝ F + Fintype.card ι = finrank ℝ E) (x : X) :
    ∃ e : Trivialization (sphere (0 : F) 1) (orthogonalSphereBundleProj f), x ∈ e.baseSet := by
  -- The orthogonal complements form a vector bundle, as the ranges of orthogonal projections.
  have hidem (x : X) : IsIdempotentElem (complementProjection f x) :=
    Submodule.isIdempotentElem_starProjection _
  let := rangeFiberBundle (continuous_complementProjection hf ho) hidem
    (nonempty_continuousLinearEquiv_range ho hF)
  have := rangeVectorBundle (continuous_complementProjection hf ho) hidem
    (nonempty_continuousLinearEquiv_range ho hF)
  have hnorm : Continuous fun v : TotalSpace F (fun x ↦ (complementProjection f x).range) ↦
      ‖v.snd‖ :=
    continuous_norm.comp
      (continuous_snd.comp (isEmbedding_totalSpace_range F (complementProjection f)).continuous)
  obtain ⟨e, he⟩ := exists_trivialization_sphereBundleProj F _ hnorm x
  -- Transport the chart of the sphere bundle along the identification with the space of pairs.
  have hproj : sphereBundleProj F _ ∘ (sphereBundleHomeomorph F).symm =
      orthogonalSphereBundleProj f := by
    ext q
    simp [sphereBundleHomeomorph]
  rw [← hproj]
  exact ⟨e.compHomeomorph (sphereBundleHomeomorph F).symm, he⟩

/-- The charts of `TauCeti.exists_trivialization_orthogonalSphereBundleProj` with fibre the unit
sphere of `ℝ^(dim E - card ι)`, the dimension being read off the orthonormal frame at the point. -/
private theorem exists_trivialization_euclidean (hf : Continuous f)
    (ho : ∀ x, Orthonormal ℝ (f x)) (x : X) :
    ∃ e : Trivialization (sphere (0 : EuclideanSpace ℝ (Fin (finrank ℝ E - Fintype.card ι))) 1)
      (orthogonalSphereBundleProj f), x ∈ e.baseSet := by
  have h := (ho x).linearIndependent.fintype_card_le_finrank
  exact exists_trivialization_orthogonalSphereBundleProj hf ho (by simp; omega) x

omit [Fintype ι] in
/-- **The unit spheres orthogonal to a continuous orthonormal frame form a Serre fibration.** -/
theorem TopCat.mem_serreFibrations_orthogonalSphereBundleProj [Finite ι] (hf : Continuous f)
    (ho : ∀ x, Orthonormal ℝ (f x)) :
    TopCat.serreFibrations (_root_.TopCat.ofHom (orthogonalSphereBundleProj f) :
      _root_.TopCat.of (orthogonalSphereBundle f) ⟶ _root_.TopCat.of X) :=
  have := Fintype.ofFinite ι
  TopCat.mem_serreFibrations_of_exists_trivialization (exists_trivialization_euclidean hf ho)

omit [Fintype ι] in
/-- **The unit spheres orthogonal to a continuous orthonormal frame over a normal paracompact base
form a Hurewicz fibration.** -/
theorem isHurewiczFibration_orthogonalSphereBundleProj [Finite ι] [NormalSpace X]
    [ParacompactSpace X] (hf : Continuous f) (ho : ∀ x, Orthonormal ℝ (f x)) :
    IsHurewiczFibration.{w} (orthogonalSphereBundleProj f) :=
  have := Fintype.ofFinite ι
  isHurewiczFibration_of_exists_trivialization (exists_trivialization_euclidean hf ho)

end TauCeti
