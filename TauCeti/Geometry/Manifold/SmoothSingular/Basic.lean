/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicTopology.SimplicialSet.Subcomplex
public import Mathlib.AlgebraicTopology.SimplicialSet.TopAdj
public import TauCeti.Geometry.Manifold.ContMDiff.SmoothOnSubset

/-!
# Smooth singular simplices

Smooth singular simplices are the singular simplices which locally extend smoothly in
barycentric coordinates. They form a sub-simplicial set: faces and degeneracies preserve
local extendibility. Using the ambient barycentric space here agrees with the usual
full-dimensional simplex convention, since its affine hyperplane has an affine retraction.

The construction needs only a charted target, not a manifold hypothesis. Such hypotheses
are needed for the smoothing theorem, not for the carrier or its simplicial operators.

## References

* John M. Lee, *Introduction to Smooth Manifolds*, second edition, Chapter 18.
* Mathlib's `TopCat.toSSet` supplies the underlying singular simplicial set.
-/

public section

noncomputable section

open CategoryTheory Convexity Set Filter Topology
open scoped Manifold ContDiff Simplicial

namespace TauCeti

universe u

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  (I : ModelWithCorners ℝ E H) (M : Type u) [TopologicalSpace M] [ChartedSpace H M]

/-- Singular simplices which extend smoothly near every point of their barycentric simplex.
The extension is local in the ambient space of weight vectors. -/
def smoothSingularSubcomplex : (TopCat.toSSet.obj (TopCat.of M)).Subcomplex where
  obj n := {σ | SmoothOnSubset I
    ((TopCat.of M).toSSetObjEquiv n σ ∘
      (Equiv.ofInjective (fun x : StdSimplex ℝ (Fin (n.unop.len + 1)) ↦
        (x.weights : Fin (n.unop.len + 1) → ℝ))
          (StdSimplex.isEmbedding_toFun_comp_weights ℝ _).injective).symm)}
  map {n m} f σ hσ := by
    simp only [Set.mem_ofPred_eq, Set.mem_preimage] at hσ ⊢
    rw [smoothOnSubset_range_iff] at hσ ⊢
    -- The simplicial map extends to a linear push-forward of ambient weight vectors.
    let L : (Fin (m.unop.len + 1) → ℝ) → (Fin (n.unop.len + 1) → ℝ) :=
      fun w j ↦ ∑ i, if f.unop i = j then w i else 0
    have hL : ContDiff ℝ ∞ L := by
      apply contDiff_pi.mpr
      intro j
      apply ContDiff.sum
      intro i _
      split_ifs <;> fun_prop
    have hweights (x : StdSimplex ℝ (Fin (m.unop.len + 1))) :
        L x.weights = (StdSimplex.map f.unop x).weights := by
      ext j
      simp [L, StdSimplex.weights_map, Finsupp.mapDomain_fintype, Finsupp.single_apply]
    intro x
    obtain ⟨U, hU, g, hg, heq⟩ := hσ (StdSimplex.map f.unop x)
    refine ⟨L ⁻¹' U, ?_, g ∘ L,
      hg.comp hL.contMDiff.contMDiffOn (fun _ hy ↦ hy), ?_⟩
    · exact hL.continuous.continuousAt.preimage_mem_nhds (hweights x ▸ hU)
    · intro y hy
      exact (congrArg g (hweights y)).trans
        ((heq (StdSimplex.map f.unop y) (hweights y ▸ hy)).trans
          (TopCat.toSSetObjEquiv_naturality_apply f.unop σ y).symm)

/-- Membership in the smooth singular subcomplex is precisely local smooth extendibility,
expressed without an inverse to the barycentric parametrization. -/
theorem mem_smoothSingularSubcomplex_iff {n : SimplexCategoryᵒᵖ}
    (σ : (TopCat.toSSet.obj (TopCat.of M)).obj n) :
    σ ∈ (smoothSingularSubcomplex I M).obj n ↔
      ∀ x : StdSimplex ℝ (Fin (n.unop.len + 1)),
        ∃ U ∈ 𝓝 (x.weights : Fin (n.unop.len + 1) → ℝ),
          ∃ g : (Fin (n.unop.len + 1) → ℝ) → M,
            ContMDiffOn 𝓘(ℝ, Fin (n.unop.len + 1) → ℝ) I ∞ g U ∧
              ∀ y : StdSimplex ℝ (Fin (n.unop.len + 1)),
                (y.weights : Fin (n.unop.len + 1) → ℝ) ∈ U →
                  g y.weights = (TopCat.of M).toSSetObjEquiv n σ y :=
  smoothOnSubset_range_iff _ _ _

/-- A smooth singular simplex, regarded as a simplex of the smooth singular subcomplex. -/
abbrev SmoothSimplex (n : ℕ) := (smoothSingularSubcomplex I M : SSet) _⦋n⦌

namespace SmoothSimplex

variable {I M} {n : ℕ}

/-- The underlying continuous singular simplex. -/
def toContinuousMap (σ : SmoothSimplex I M n) : C(StdSimplex ℝ (Fin (n + 1)), M) :=
  (TopCat.of M).toSSetObjEquiv _ σ.val

/-- Smooth simplices are determined by their pointwise values. -/
@[ext]
theorem ext {σ τ : SmoothSimplex I M n}
    (h : ∀ x, σ.toContinuousMap x = τ.toContinuousMap x) : σ = τ :=
  Subtype.ext (((TopCat.of M).toSSetObjEquiv _).injective (ContinuousMap.ext h))

/-- Restrict an ambient smooth map to the barycentric simplex. -/
def ofContMDiff (g : (Fin (n + 1) → ℝ) → M)
    (hg : ContMDiff 𝓘(ℝ, Fin (n + 1) → ℝ) I ∞ g) : SmoothSimplex I M n :=
  ⟨((TopCat.of M).toSSetObjEquiv _).symm
      ⟨fun x ↦ g x.weights,
        hg.continuous.comp (StdSimplex.isEmbedding_toFun_comp_weights ℝ _).continuous⟩,
    (mem_smoothSingularSubcomplex_iff I M _).mpr fun _ ↦
      ⟨univ, univ_mem, g, hg.contMDiffOn, fun _ _ ↦ rfl⟩⟩

@[simp]
theorem toContinuousMap_ofContMDiff (g : (Fin (n + 1) → ℝ) → M)
    (hg : ContMDiff 𝓘(ℝ, Fin (n + 1) → ℝ) I ∞ g)
    (x : StdSimplex ℝ (Fin (n + 1))) :
    (ofContMDiff g hg).toContinuousMap x = g x.weights := by
  simp [toContinuousMap, ofContMDiff]

/-- Precomposition by a simplicial operator, including faces and degeneracies. -/
def map {m : ℕ} (σ : SmoothSimplex I M n) (f : ⦋m⦌ ⟶ ⦋n⦌) : SmoothSimplex I M m :=
  (smoothSingularSubcomplex I M : SSet).map f.op σ

@[simp]
theorem toContinuousMap_map {m : ℕ} (σ : SmoothSimplex I M n) (f : ⦋m⦌ ⟶ ⦋n⦌)
    (x : StdSimplex ℝ (Fin (m + 1))) :
    (σ.map f).toContinuousMap x = σ.toContinuousMap (StdSimplex.map f x) :=
  TopCat.toSSetObjEquiv_naturality_apply f σ.val x

@[simp]
theorem map_id (σ : SmoothSimplex I M n) : σ.map (𝟙 ⦋n⦌) = σ := by
  exact ConcreteCategory.congr_hom ((smoothSingularSubcomplex I M : SSet).map_id _) σ

/-- Simplicial precomposition reverses the order of composition. -/
theorem map_comp {m k : ℕ} (σ : SmoothSimplex I M n)
    (f : ⦋k⦌ ⟶ ⦋m⦌) (g : ⦋m⦌ ⟶ ⦋n⦌) : σ.map (f ≫ g) = (σ.map g).map f := by
  exact ConcreteCategory.congr_hom
    ((smoothSingularSubcomplex I M : SSet).map_comp g.op f.op) σ

/-- The `i`-th face of a smooth simplex. -/
def face (σ : SmoothSimplex I M (n + 1)) (i : Fin (n + 2)) : SmoothSimplex I M n :=
  σ.map (SimplexCategory.δ i)

/-- The named face agrees with the face operator of the smooth singular simplicial set. -/
theorem face_eq_delta (σ : SmoothSimplex I M (n + 1)) (i : Fin (n + 2)) :
    σ.face i = (smoothSingularSubcomplex I M : SSet).δ i σ :=
  (rfl)

@[simp]
theorem toContinuousMap_face (σ : SmoothSimplex I M (n + 1)) (i : Fin (n + 2))
    (x : StdSimplex ℝ (Fin (n + 1))) :
    (σ.face i).toContinuousMap x = σ.toContinuousMap (StdSimplex.map i.succAbove x) :=
  TopCat.toSSetObjEquiv_δ_apply σ.val i x

end SmoothSimplex

end TauCeti
