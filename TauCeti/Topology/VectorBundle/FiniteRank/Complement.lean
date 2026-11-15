/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.VectorBundle.FiniteRank.Biproduct
public import TauCeti.Topology.VectorBundle.Complement
public import TauCeti.Topology.VectorBundle.TrivialEmbedding
public import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Orthogonal complements of finite-rank bundle cores in trivial cores

Let `j : A ⟶ trivial 𝕜 B N` be a bundle map of real or complex finite-rank cores which is
injective on every fibre. Read `Fin N → 𝕜` as `EuclideanSpace 𝕜 (Fin N)`, with its standard inner
product. The orthogonal complements of the images of the fibres of `A` form a vector bundle, and
`orthogonal j hj` is the core of rank `N - A.rank` presenting it. Its inclusion
`orthogonalInclusion j hj` into the trivial core is injective on every fibre, with fibrewise
image exactly the orthogonal complement of the image of `j`
(`mem_range_fiberMap_orthogonalInclusion_iff`). Together with `j` it identifies the trivial core
with the Whitney sum:

* `orthogonalIso j hj : A ⊞ orthogonal j hj ≅ trivial 𝕜 B N`, whose underlying morphism is
  `biprod.desc j (orthogonalInclusion j hj)`.

Over a compact normal base, in particular a compact Hausdorff base, every core admits such a
fibrewise injective map into a trivial core (`exists_injective_hom_trivial`). Hence every real or
complex finite-rank core over such a base is a direct summand of a trivial core
(`exists_biprod_iso_trivial`). This is what lets a class in the Grothendieck group of bundles
over a compact base be written as a bundle minus a trivial bundle.

The complementary bundle is the one constructed in `TauCeti.Topology.VectorBundle.Complement`
from the continuous orthogonal range projections, presented as a core by `ofBundle`; the
embedding over a compact base is `TauCeti.exists_continuous_injective_fin_of_compactSpace`.

## References

* A. Hatcher, *Vector Bundles and K-Theory*, Proposition 1.4.
* M. F. Atiyah, *K-Theory*, Chapter I, §1.4.
-/

public section

open Bundle CategoryTheory CategoryTheory.Limits Function
open scoped InnerProductSpace

namespace TauCeti.FiniteRankBundleCore

/-- Over a compact normal base, in particular a compact Hausdorff base, every core admits a
bundle map into a trivial core which is injective on every fibre. -/
theorem exists_injective_hom_trivial {𝕜 B : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
    [NormedAlgebra ℝ 𝕜] [TopologicalSpace B] [CompactSpace B] [NormalSpace B]
    (A : FiniteRankBundleCore 𝕜 B) :
    ∃ (N : ℕ) (j : A ⟶ trivial 𝕜 B N), ∀ x, Injective (j.fiberMap x) := by
  obtain ⟨N, f, hf, hinj⟩ : ∃ (N : ℕ) (f : B → (Fin A.rank → 𝕜) →L[𝕜] (Fin N → 𝕜)),
      Continuous (fun p : A.core.TotalSpace ↦ f p.proj p.2) ∧ ∀ x, Injective (f x) :=
    exists_continuous_injective_fin_of_compactSpace (F := Fin A.rank → 𝕜) (E := A.core.Fiber)
  exact ⟨N, toTrivial f hf, fun x ↦ by rw [fiberMap_toTrivial]; exact hinj x⟩

section Orthogonal

variable {𝕜 B : Type*} [RCLike 𝕜] [TopologicalSpace B] {A : FiniteRankBundleCore 𝕜 B} {N : ℕ}
  (j : A ⟶ trivial 𝕜 B N) (hj : ∀ x, Injective (j.fiberMap x))

/-- The fibre maps of `j`, read in Euclidean space. -/
private noncomputable def euclideanMap (x : B) :
    A.core.Fiber x →L[𝕜] EuclideanSpace 𝕜 (Fin N) :=
  ((EuclideanSpace.equiv (Fin N) 𝕜).symm : (Fin N → 𝕜) →L[𝕜] EuclideanSpace 𝕜 (Fin N)).comp
    (j.fiberMap x)

private theorem euclideanMap_apply (x : B) (v : Fin A.rank → 𝕜) :
    euclideanMap j x v = (EuclideanSpace.equiv (Fin N) 𝕜).symm (j.fiberMap x v) :=
  rfl

private theorem continuous_euclideanMap :
    Continuous fun p : A.core.TotalSpace ↦ euclideanMap j p.proj p.2 :=
  (EuclideanSpace.equiv (Fin N) 𝕜).symm.continuous.comp (continuous_fiberMap_trivial j)

include hj in
private theorem euclideanMap_injective (x : B) : Injective (euclideanMap j x) :=
  (EuclideanSpace.equiv (Fin N) 𝕜).symm.injective.comp (hj x)

/-- The orthogonal complements of the fibrewise images of `j`. -/
private abbrev OrthogonalFiber (x : B) : Type _ :=
  (bundleComplementProjection (F := Fin A.rank → 𝕜) (euclideanMap j) x).range

/-- The rank of the orthogonal complement, in the form produced by the complement construction. -/
private noncomputable abbrev orthogonalRank : ℕ :=
  Module.finrank 𝕜 (EuclideanSpace 𝕜 (Fin N)) - Module.finrank 𝕜 (Fin A.rank → 𝕜)

/-- The orthogonal complement of the image of a fibrewise injective bundle map `j` into a trivial
core, for the standard inner product on `Fin N → 𝕜` (that of `EuclideanSpace 𝕜 (Fin N)`). -/
noncomputable def orthogonal : FiniteRankBundleCore 𝕜 B :=
  letI := bundleComplementFiberBundle (euclideanMap j) (continuous_euclideanMap j)
    (euclideanMap_injective j hj)
  haveI := bundleComplementVectorBundle (euclideanMap j) (continuous_euclideanMap j)
    (euclideanMap_injective j hj)
  ofBundle 𝕜 (orthogonalRank (A := A) (N := N)) (OrthogonalFiber j)

@[simp] theorem rank_orthogonal : (orthogonal j hj).rank = N - A.rank := by
  simp [orthogonal, orthogonalRank]

/-- The fibres of `orthogonal j hj` are the orthogonal complements of the images of `j`. -/
private noncomputable def orthogonalFiberEquiv (x : B) :
    (Fin (orthogonal j hj).rank → 𝕜) ≃L[𝕜] OrthogonalFiber j x :=
  letI := bundleComplementFiberBundle (euclideanMap j) (continuous_euclideanMap j)
    (euclideanMap_injective j hj)
  haveI := bundleComplementVectorBundle (euclideanMap j) (continuous_euclideanMap j)
    (euclideanMap_injective j hj)
  pointIndexedCoreFiberEquiv 𝕜 (Fin (orthogonalRank (A := A) (N := N)) → 𝕜)
    (OrthogonalFiber j) x

private theorem continuous_orthogonalFiberEquiv :
    Continuous fun p : (orthogonal j hj).core.TotalSpace ↦
      ((orthogonalFiberEquiv j hj p.proj p.2 : OrthogonalFiber j p.proj) :
        EuclideanSpace 𝕜 (Fin N)) :=
  letI := bundleComplementFiberBundle (euclideanMap j) (continuous_euclideanMap j)
    (euclideanMap_injective j hj)
  haveI := bundleComplementVectorBundle (euclideanMap j) (continuous_euclideanMap j)
    (euclideanMap_injective j hj)
  (continuous_snd.comp ((isEmbedding_totalSpace_range _ _).continuous.comp
    (pointIndexedCoreHomeomorph 𝕜 (Fin (orthogonalRank (A := A) (N := N)) → 𝕜)
      (OrthogonalFiber j)).continuous)).congr fun p ↦
    congrArg (fun q : TotalSpace _ (OrthogonalFiber j) ↦ (q.2 : EuclideanSpace 𝕜 (Fin N)))
      (pointIndexedCoreHomeomorph_apply 𝕜 _ _ p)

/-- The fibre maps of the inclusion of the orthogonal complement into `Fin N → 𝕜`. -/
private noncomputable def orthogonalFiberMap (x : B) :
    (Fin (orthogonal j hj).rank → 𝕜) →L[𝕜] (Fin N → 𝕜) :=
  (EuclideanSpace.equiv (Fin N) 𝕜 : EuclideanSpace 𝕜 (Fin N) →L[𝕜] (Fin N → 𝕜)).comp
    ((Submodule.subtypeL _).comp (orthogonalFiberEquiv j hj x : _ →L[𝕜] OrthogonalFiber j x))

/-- The inclusion of the orthogonal complement of the image of `j` into the trivial core. -/
noncomputable def orthogonalInclusion : orthogonal j hj ⟶ trivial 𝕜 B N :=
  toTrivial (orthogonalFiberMap j hj)
    (((EuclideanSpace.equiv (Fin N) 𝕜).continuous.comp
      (continuous_orthogonalFiberEquiv j hj)).congr fun _ ↦ rfl)

private theorem fiberMap_orthogonalInclusion (x : B) (v : Fin (orthogonal j hj).rank → 𝕜) :
    (orthogonalInclusion j hj).fiberMap x v =
      EuclideanSpace.equiv (Fin N) 𝕜 (orthogonalFiberEquiv j hj x v : EuclideanSpace 𝕜 (Fin N)) :=
  congrArg (fun f ↦ f v) (fiberMap_toTrivial (orthogonalFiberMap j hj) _ x)

/-- `j` and the inclusion of the orthogonal complement of its image together form an isomorphism
from the Whitney sum to the trivial core. -/
theorem isIso_biprod_desc_orthogonalInclusion :
    IsIso (biprod.desc j (orthogonalInclusion j hj)) := by
  -- On each fibre, the map sends `v` to `j (fst v) + ι (snd v)`. Read in Euclidean space this is
  -- the orthogonal splitting `P` of the image of `j` and its complement, applied to the biproduct
  -- coordinates `(fst v, snd v)`; both `P` and the biproduct coordinates are bijective.
  rw [isIso_iff_bijective]
  intro x
  -- `EuclideanSpace.equiv`, with its target written in the coordinates of the trivial core.
  let e : EuclideanSpace 𝕜 (Fin N) ≃L[𝕜] (Fin (trivial 𝕜 B N).rank → 𝕜) :=
    EuclideanSpace.equiv (Fin N) 𝕜
  let P := bundleComplementFiberEquiv (F := Fin A.rank → 𝕜) (euclideanMap j)
    (euclideanMap_injective j hj) x
  let D := orthogonal j hj
  have hdesc (v : Fin (A ⊞ D).rank → 𝕜) : (biprod.desc j (orthogonalInclusion j hj)).fiberMap x v =
      j.fiberMap x ((biprod.fst : A ⊞ D ⟶ A).fiberMap x v) +
        e (orthogonalFiberEquiv j hj x ((biprod.snd : A ⊞ D ⟶ D).fiberMap x v)) := by
    rw [biprod.desc_eq, fiberMap_add, fiberMap_comp, fiberMap_comp, add_apply,
      ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply, fiberMap_orthogonalInclusion]
    rfl
  have hP (a : Fin A.rank → 𝕜) (c : OrthogonalFiber j x) :
      e (P (a, c)) = j.fiberMap x a + e c := by
    rw [bundleComplementFiberEquiv_apply, map_add, euclideanMap_apply]
    exact congrArg (· + e c) (e.apply_symm_apply _)
  have htotal (v : Fin (A ⊞ D).rank → 𝕜) :
      (biprod.inl : A ⟶ A ⊞ D).fiberMap x ((biprod.fst : A ⊞ D ⟶ A).fiberMap x v) +
        (biprod.inr : D ⟶ A ⊞ D).fiberMap x ((biprod.snd : A ⊞ D ⟶ D).fiberMap x v) = v := by
    have h := congrArg (fun f : A ⊞ D ⟶ A ⊞ D ↦ f.fiberMap x v) (biprod.total (X := A) (Y := D))
    simp only [fiberMap_add, fiberMap_comp, fiberMap_id, add_apply,
      ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply] at h
    exact h
  refine ⟨fun v w hvw ↦ ?_, fun w ↦ ?_⟩
  · rw [hdesc, hdesc, ← hP, ← hP] at hvw
    obtain ⟨h₁, h₂⟩ := Prod.mk.inj (P.injective (e.injective hvw))
    rw [← htotal v, ← htotal w, h₁, (orthogonalFiberEquiv j hj x).injective h₂]
  · obtain ⟨⟨a, c⟩, hac⟩ := P.surjective (e.symm w)
    have hl (a : Fin A.rank → 𝕜) : (biprod.desc j (orthogonalInclusion j hj)).fiberMap x
        ((biprod.inl : A ⟶ A ⊞ D).fiberMap x a) = j.fiberMap x a := by
      rw [← ContinuousLinearMap.comp_apply, ← fiberMap_comp, biprod.inl_desc]
    have hr (b : Fin D.rank → 𝕜) : (biprod.desc j (orthogonalInclusion j hj)).fiberMap x
        ((biprod.inr : D ⟶ A ⊞ D).fiberMap x b) = (orthogonalInclusion j hj).fiberMap x b := by
      rw [← ContinuousLinearMap.comp_apply, ← fiberMap_comp, biprod.inr_desc]
    refine ⟨(biprod.inl : A ⟶ A ⊞ D).fiberMap x a +
      (biprod.inr : D ⟶ A ⊞ D).fiberMap x ((orthogonalFiberEquiv j hj x).symm c), ?_⟩
    rw [map_add, hl a, hr, fiberMap_orthogonalInclusion, ContinuousLinearEquiv.apply_symm_apply]
    exact (hP a c).symm.trans ((congrArg e hac).trans (e.apply_symm_apply w))

/-- The trivial core of rank `N` is the Whitney sum of `A` and the orthogonal complement of the
image of a fibrewise injective bundle map `j : A ⟶ trivial 𝕜 B N`. -/
noncomputable def orthogonalIso : A ⊞ orthogonal j hj ≅ trivial 𝕜 B N :=
  haveI := isIso_biprod_desc_orthogonalInclusion j hj
  asIso (biprod.desc j (orthogonalInclusion j hj))

@[simp] theorem orthogonalIso_hom :
    (orthogonalIso j hj).hom = biprod.desc j (orthogonalInclusion j hj) := (rfl)

/-- The inclusion of the orthogonal complement is injective on every fibre. -/
theorem fiberMap_orthogonalInclusion_injective (x : B) :
    Injective ((orthogonalInclusion j hj).fiberMap x) := by
  intro v w h
  rw [fiberMap_orthogonalInclusion, fiberMap_orthogonalInclusion] at h
  exact (orthogonalFiberEquiv j hj x).injective
    (Subtype.ext ((EuclideanSpace.equiv (Fin N) 𝕜).injective h))

/-- The fibrewise image of the inclusion of `orthogonal j hj` is the orthogonal complement of the
image of `j`, for the inner product of `EuclideanSpace 𝕜 (Fin N)`. -/
theorem mem_range_fiberMap_orthogonalInclusion_iff (x : B) (w : Fin (trivial 𝕜 B N).rank → 𝕜) :
    w ∈ ((orthogonalInclusion j hj).fiberMap x).range ↔
      ∀ v : Fin A.rank → 𝕜, ⟪(EuclideanSpace.equiv (Fin N) 𝕜).symm (j.fiberMap x v),
        (EuclideanSpace.equiv (Fin N) 𝕜).symm w⟫_𝕜 = 0 := by
  have hmem : w ∈ ((orthogonalInclusion j hj).fiberMap x).range ↔
      (EuclideanSpace.equiv (Fin N) 𝕜).symm w ∈ (euclideanMap j x).rangeᗮ := by
    rw [← range_bundleComplementProjection (F := Fin A.rank → 𝕜) (euclideanMap j) x]
    constructor
    · rintro ⟨v, rfl⟩
      rw [ContinuousLinearMap.coe_coe, fiberMap_orthogonalInclusion,
        ContinuousLinearEquiv.symm_apply_apply]
      exact (orthogonalFiberEquiv j hj x v).2
    · intro h
      refine ⟨(orthogonalFiberEquiv j hj x).symm ⟨_, h⟩, ?_⟩
      rw [ContinuousLinearMap.coe_coe, fiberMap_orthogonalInclusion,
        ContinuousLinearEquiv.apply_symm_apply]
      exact (EuclideanSpace.equiv (Fin N) 𝕜).apply_symm_apply w
  rw [hmem, Submodule.mem_orthogonal]
  simp only [LinearMap.mem_range, ContinuousLinearMap.coe_coe, forall_exists_index,
    forall_apply_eq_imp_iff]
  exact forall_congr' fun v ↦
    Iff.of_eq (congrArg (fun u ↦ ⟪u, (EuclideanSpace.equiv (Fin N) 𝕜).symm w⟫_𝕜 = 0)
      (euclideanMap_apply j x v))

end Orthogonal

/-- Over a compact normal base, in particular a compact Hausdorff base, every real or complex
finite-rank core is a direct summand of a trivial core. -/
theorem exists_biprod_iso_trivial {𝕜 B : Type*} [RCLike 𝕜] [TopologicalSpace B] [CompactSpace B]
    [NormalSpace B] (A : FiniteRankBundleCore 𝕜 B) :
    ∃ (N : ℕ) (D : FiniteRankBundleCore 𝕜 B), Nonempty (A ⊞ D ≅ trivial 𝕜 B N) := by
  obtain ⟨N, j, hj⟩ := exists_injective_hom_trivial A
  exact ⟨N, orthogonal j hj, ⟨orthogonalIso j hj⟩⟩

end TauCeti.FiniteRankBundleCore
