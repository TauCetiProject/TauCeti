/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicTopology.SimplicialSet.Subcomplex
public import Mathlib.AlgebraicTopology.SimplicialSet.TopAdj
public import TauCeti.Geometry.Convex.ConvexSpace.ContDiff
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
    have hmaps : MapsTo (StdSimplex.weightMap f.unop)
        (range fun x : StdSimplex ℝ (Fin (m.unop.len + 1)) ↦
          (x.weights : Fin (m.unop.len + 1) → ℝ))
        (range fun x : StdSimplex ℝ (Fin (n.unop.len + 1)) ↦
          (x.weights : Fin (n.unop.len + 1) → ℝ)) := by
      rintro _ ⟨x, rfl⟩
      exact ⟨x.map f.unop, (StdSimplex.weightMap_weights f.unop x).symm⟩
    convert hσ.comp (StdSimplex.contDiff_weightMap f.unop) hmaps using 1
    funext w
    rcases w with ⟨_, x, rfl⟩
    simp only [Function.comp_apply, StdSimplex.weightMap_weights,
      Equiv.ofInjective_symm_apply]
    exact TopCat.toSSetObjEquiv_naturality_apply f.unop σ x

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

/-- Every smooth simplex has smooth ambient extensions near each point. -/
theorem exists_extension (σ : SmoothSimplex I M n)
    (x : StdSimplex ℝ (Fin (n + 1))) :
    ∃ U ∈ 𝓝 (x.weights : Fin (n + 1) → ℝ), ∃ g : (Fin (n + 1) → ℝ) → M,
      ContMDiffOn 𝓘(ℝ, Fin (n + 1) → ℝ) I ∞ g U ∧
        ∀ y : StdSimplex ℝ (Fin (n + 1)), (y.weights : Fin (n + 1) → ℝ) ∈ U →
          g y.weights = σ.toContinuousMap y :=
  (mem_smoothSingularSubcomplex_iff I M σ.val).mp σ.property x

/-- Construct a smooth simplex from a continuous map with local ambient extensions. -/
def mk' (c : C(StdSimplex ℝ (Fin (n + 1)), M))
    (hc : ∀ x : StdSimplex ℝ (Fin (n + 1)),
      ∃ U ∈ 𝓝 (x.weights : Fin (n + 1) → ℝ), ∃ g : (Fin (n + 1) → ℝ) → M,
        ContMDiffOn 𝓘(ℝ, Fin (n + 1) → ℝ) I ∞ g U ∧
          ∀ y : StdSimplex ℝ (Fin (n + 1)), (y.weights : Fin (n + 1) → ℝ) ∈ U →
            g y.weights = c y) : SmoothSimplex I M n :=
  ⟨((TopCat.of M).toSSetObjEquiv _).symm c,
    (mem_smoothSingularSubcomplex_iff I M _).mpr (by simpa using hc)⟩

@[simp]
theorem toContinuousMap_mk' (c : C(StdSimplex ℝ (Fin (n + 1)), M))
    (hc : ∀ x : StdSimplex ℝ (Fin (n + 1)),
      ∃ U ∈ 𝓝 (x.weights : Fin (n + 1) → ℝ), ∃ g : (Fin (n + 1) → ℝ) → M,
        ContMDiffOn 𝓘(ℝ, Fin (n + 1) → ℝ) I ∞ g U ∧
          ∀ y : StdSimplex ℝ (Fin (n + 1)), (y.weights : Fin (n + 1) → ℝ) ∈ U →
            g y.weights = c y) :
    toContinuousMap (I := I) (mk' (I := I) c hc) = c :=
  ((TopCat.of M).toSSetObjEquiv (Opposite.op ⦋n⦌)).apply_symm_apply c

/-- Restrict an ambient smooth map to the barycentric simplex. -/
def ofContMDiff (g : (Fin (n + 1) → ℝ) → M)
    (hg : ContMDiff 𝓘(ℝ, Fin (n + 1) → ℝ) I ∞ g) : SmoothSimplex I M n :=
  mk' ⟨fun x ↦ g x.weights,
    hg.continuous.comp (StdSimplex.isEmbedding_toFun_comp_weights ℝ _).continuous⟩
    ((smoothOnSubset_range_iff _
      (StdSimplex.isEmbedding_toFun_comp_weights ℝ _).injective _).mp (by
        convert smoothOnSubset_restrict hg
          (s := range fun x : StdSimplex ℝ (Fin (n + 1)) ↦
            (x.weights : Fin (n + 1) → ℝ)) using 1
        funext w
        rcases w with ⟨_, x, rfl⟩
        simp only [Function.comp_apply, Equiv.ofInjective_symm_apply,
          ContinuousMap.coe_mk]))

@[simp]
theorem toContinuousMap_ofContMDiff (g : (Fin (n + 1) → ℝ) → M)
    (hg : ContMDiff 𝓘(ℝ, Fin (n + 1) → ℝ) I ∞ g)
    (x : StdSimplex ℝ (Fin (n + 1))) :
    (ofContMDiff g hg).toContinuousMap x = g x.weights := by
  simp [ofContMDiff]

-- Use the following evaluation lemmas explicitly: simp's subfunctor rules rewrite their
-- left-hand sides first, so marking them simp would fail the simp-normal-form linter.
theorem toContinuousMap_map {m : ℕ} (σ : SmoothSimplex I M n) (f : ⦋m⦌ ⟶ ⦋n⦌)
    (x : StdSimplex ℝ (Fin (m + 1))) :
    toContinuousMap ((smoothSingularSubcomplex I M : SSet).map f.op σ) x =
      σ.toContinuousMap (StdSimplex.map f x) :=
  TopCat.toSSetObjEquiv_naturality_apply f σ.val x

theorem toContinuousMap_δ (σ : SmoothSimplex I M (n + 1)) (i : Fin (n + 2))
    (x : StdSimplex ℝ (Fin (n + 1))) :
    toContinuousMap ((smoothSingularSubcomplex I M : SSet).δ i σ) x =
      σ.toContinuousMap (StdSimplex.map i.succAbove x) :=
  TopCat.toSSetObjEquiv_δ_apply σ.val i x

end SmoothSimplex

end TauCeti
