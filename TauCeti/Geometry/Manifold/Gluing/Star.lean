/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Gluing.GlueData
public import TauCeti.Topology.Category.TopCat.GlueData.Star

/-!
# Compatible manifold gluing in a star

Glue a hub manifold `X` to abstract leaf manifolds `Y i` along smooth open partial
homeomorphisms with pairwise disjoint sources. The resulting `TauCeti.starGlueData` satisfies
`TopCat.GlueData.IsCompatible`: it therefore acquires a manifold atlas from the general
compatible-gluing theorem, and every piece includes by a local diffeomorphism. Over `ℂ`,
holomorphic transitions give a complex manifold and local biholomorphisms.

This tests compatible gluing with heterogeneous pieces, empty off-diagonal overlaps, and an
arbitrary number of leaves. In particular it applies to finite stars, without requiring any
piece or overlap to be nonempty. The glued atlas is the named `TopCat.GlueData.chartedSpace`;
no additional atlas is installed globally.

## References

* John M. Lee, *Introduction to Smooth Manifolds*, second edition, Chapter 1
  (the smooth manifold chart lemma).
-/

public section

open Set TopologicalSpace Function
open scoped Manifold ContDiff

namespace TauCeti

universe u

variable {ι X : Type u} [TopologicalSpace X] {Y : ι → Type u}
  [∀ i, TopologicalSpace (Y i)] {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H} {n : ℕ∞ω}
  [ChartedSpace H X] [∀ i, ChartedSpace H (Y i)]
  (e : ∀ i, OpenPartialHomeomorph X (Y i))
  (he : Pairwise (Disjoint on fun i ↦ (e i).source))

/-- Each piece of the star retains its original atlas. -/
@[instance_reducible]
noncomputable instance instChartedSpaceStarGlueDataU (i : (starGlueData e he).J) :
    ChartedSpace H ((starGlueData e he).U i) := by
  cases i with
  | none => exact inferInstanceAs (ChartedSpace H X)
  | some i => exact inferInstanceAs (ChartedSpace H (Y i))

/-- Each overlap of the star carries its open-subspace atlas. -/
@[instance_reducible]
noncomputable instance instChartedSpaceStarGlueDataV
    (p : (starGlueData e he).J × (starGlueData e he).J) :
    ChartedSpace H ((starGlueData e he).V p) := by
  classical
  rcases p with ⟨i, j⟩
  cases i with
  | none =>
    cases j with
    | none => exact inferInstanceAs (ChartedSpace H (⊤ : Opens X))
    | some j => exact inferInstanceAs
        (ChartedSpace H (⟨(e j).source, (e j).open_source⟩ : Opens X))
  | some i =>
    cases j with
    | none => exact inferInstanceAs
        (ChartedSpace H (⟨(e i).target, (e i).open_target⟩ : Opens (Y i)))
    | some j => exact inferInstanceAs (ChartedSpace H
        (⟨{_x | i = j}, by by_cases h : i = j <;> simp [h]⟩ : Opens (Y i)))

/-- Each piece of a star of `C^n` manifolds is a `C^n` manifold. -/
instance instIsManifoldStarGlueDataU [IsManifold I n X] [∀ i, IsManifold I n (Y i)]
    (i : (starGlueData e he).J) : IsManifold I n ((starGlueData e he).U i) := by
  cases i with
  | none => exact inferInstanceAs (IsManifold I n X)
  | some i => exact inferInstanceAs (IsManifold I n (Y i))

private theorem isLocalDiffeomorph_starGlueData_f (i j : (starGlueData e he).J) :
    IsLocalDiffeomorph I I n ((starGlueData e he).f i j) := by
  classical
  cases i with
  | none =>
    cases j with
    | none => exact isLocalDiffeomorph_subtype_val (I := I) (U := (⊤ : Opens X))
    | some j =>
      exact isLocalDiffeomorph_subtype_val (I := I)
        (U := (⟨(e j).source, (e j).open_source⟩ : Opens X))
  | some i =>
    cases j with
    | none =>
      exact isLocalDiffeomorph_subtype_val (I := I)
        (U := (⟨(e i).target, (e i).open_target⟩ : Opens (Y i)))
    | some j =>
      exact isLocalDiffeomorph_subtype_val (I := I)
        (U := (⟨{_x : Y i | i = j}, by by_cases h : i = j <;> simp [h]⟩ : Opens (Y i)))

/-- Smooth transitions with pairwise disjoint hub sources give a compatible star gluing.
Both overlap maps into adjacent pieces are local diffeomorphisms, including when an overlap
is empty. Apply `TopCat.GlueData.IsCompatible.isManifold` to obtain the glued manifold. -/
theorem isCompatible_starGlueData
    (hs : ∀ i, ContMDiffOn I I n (e i) (e i).source)
    (ht : ∀ i, ContMDiffOn I I n (e i).symm (e i).target) :
    (starGlueData e he).IsCompatible I n := by
  classical
  let Φ (i : ι) : PartialDiffeomorph I I X (Y i) n :=
    { (e i) with contMDiffOn_toFun := hs i, contMDiffOn_invFun := ht i }
  constructor
  · exact isLocalDiffeomorph_starGlueData_f e he
  · intro i j
    cases i with
    | none =>
      cases j with
      | none =>
        rw [(starGlueData e he).toGlueData.t_id none]
        exact isLocalDiffeomorph_subtype_val (I := I) (n := n) (U := (⊤ : Opens X))
      | some j =>
        intro x
        simp only [starGlueData_t_none_some]
        exact (isLocalDiffeomorph_subtype_val (I := I)
          (U := (⟨(e j).source, (e j).open_source⟩ : Opens X)) x).comp I (Y j)
          (hg := (Φ j).isLocalDiffeomorphAt I I n x.2)
    | some i =>
      cases j with
      | none =>
        intro x
        simp only [starGlueData_t_some_none]
        exact (isLocalDiffeomorph_subtype_val (I := I)
          (U := (⟨(e i).target, (e i).open_target⟩ : Opens (Y i))) x).comp I X
          (hg := (Φ i).symm.isLocalDiffeomorphAt I I n x.2)
      | some j =>
        intro x
        have hij : i = j := x.2
        subst j
        rw [(starGlueData e he).toGlueData.t_id (some i)]
        exact isLocalDiffeomorph_subtype_val (I := I) (n := n)
          (U := (⟨{_x : Y i | i = i}, by simp⟩ : Opens (Y i))) x

end TauCeti
