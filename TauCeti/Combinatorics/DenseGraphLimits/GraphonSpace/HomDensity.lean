/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Combinatorics.DenseGraphLimits.Counting
public import TauCeti.Combinatorics.DenseGraphLimits.GraphonSpace.Basic
public import TauCeti.Combinatorics.DenseGraphLimits.HomDensity.Structural
public import Mathlib.Topology.ContinuousMap.Bounded.Normed

/-!
# Homomorphism densities on graphon space

Homomorphism density is invariant under zero cut distance, so it descends from strict graphon
representatives to `GraphonSpace`.  The descended observable retains the quantitative counting
bound: for a finite graph `F`, it is Lipschitz with constant equal to the number of edges of `F`.
In particular every homomorphism density is continuous on graphon space.

These quotient-stable observables are the coordinates used by graphon separation, compactness, and
the equivalence between cut-distance convergence and convergence of all homomorphism densities.

The structural identities of homomorphism density descend as well: `t(⊥, ·) = 1`, relabelling
along an embedding changes nothing, and `t(F₁ ⊕ F₂, ·) = t(F₁, ·) t(F₂, ·)`. So, as bounded
continuous functions on graphon space, the homomorphism densities form a submonoid. This is the
shape in which they serve as test functions: by Stone–Weierstrass a point-separating submonoid of
bounded continuous functions determines finite measures
(`TauCeti.MeasureTheory.ext_of_forall_mem_submonoid_integral_eq_of_polish`), so wherever the
densities separate points, the integrals of all `t(F, ·)` determine a finite measure on graphon
space.

## Main definitions

* `TauCeti.DenseGraphLimits.homDensityOnSpace` is homomorphism density on the cut-distance
  quotient.
* `TauCeti.DenseGraphLimits.homDensityBCF` is the same function, bundled as a bounded continuous
  function.
* `TauCeti.DenseGraphLimits.homDensitySubmonoid` is the submonoid of bounded continuous functions
  on graphon space formed by the homomorphism densities of finite graphs.

## Main results

* `TauCeti.DenseGraphLimits.lipschitzWith_homDensity` is the edge-count Lipschitz bound on strict
  graphons, which makes the descent well defined;
* `TauCeti.DenseGraphLimits.homDensityOnSpace_mk` computes it on a representative;
* `TauCeti.DenseGraphLimits.homDensityOnSpace_nonneg` and
  `TauCeti.DenseGraphLimits.homDensityOnSpace_le_one` bound it in `[0, 1]`;
* `TauCeti.DenseGraphLimits.lipschitzWith_homDensityOnSpace` gives the edge-count Lipschitz bound;
* `TauCeti.DenseGraphLimits.continuous_homDensityOnSpace` gives continuity on every fixed-carrier
  graphon space;
* `TauCeti.DenseGraphLimits.homDensityOnSpace_bot`,
  `TauCeti.DenseGraphLimits.homDensityOnSpace_map_embedding` and
  `TauCeti.DenseGraphLimits.homDensityOnSpace_sum` are normalization, relabelling invariance and
  multiplicativity over disjoint unions on graphon space;
* `TauCeti.DenseGraphLimits.homDensityBCF_mem_homDensitySubmonoid` says the homomorphism density
  of a graph on any finite vertex type lies in `homDensitySubmonoid`.

## References

* L. Lovász, *Large Networks and Graph Limits*, AMS Colloquium Publications 60 (2012), Lemma 10.23.
* S. Janson, *Graphons, cut norm and distance, couplings and rearrangements*, NYJM Monographs 4
  (2013), Lemma 7.2.
* Roadmap: `TauCetiRoadmap/DenseGraphLimits/README.md`, Layer 2 — the descent of homomorphism
  density to `GraphonSpace`. The signatures follow
  `TauCetiRoadmap/DenseGraphLimits/Suggested.lean`.
-/

public section

noncomputable section

open MeasureTheory

open scoped BoundedContinuousFunction

namespace TauCeti

namespace DenseGraphLimits

variable {V Ω : Type*} [Fintype V] [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- Homomorphism density is Lipschitz for the cut-distance pseudometric on strict graphons, with
constant the number of edges of the finite graph. -/
theorem lipschitzWith_homDensity (F : SimpleGraph V) [DecidableRel F.Adj] :
    LipschitzWith (F.edgeFinset.card : NNReal) (homDensity F : Graphon Ω μ → ℝ) := by
  refine LipschitzWith.of_dist_le_mul fun U W => ?_
  rw [Real.dist_eq, NNReal.coe_natCast, Graphon.dist_eq_cutDist]
  exact abs_homDensity_sub_le_cutDist F U W

/-- The homomorphism density of a finite graph, as a function on graphon space.

It is well defined because homomorphism density is continuous for the cut-distance pseudometric,
hence constant on inseparable graphons. -/
def homDensityOnSpace (F : SimpleGraph V) [DecidableRel F.Adj] :
    GraphonSpace Ω μ → ℝ :=
  SeparationQuotient.lift (homDensity F) fun _ _ h =>
    (h.map (lipschitzWith_homDensity F).continuous).eq

/-- Homomorphism density on graphon space computes as the original density on representatives. -/
@[simp]
theorem homDensityOnSpace_mk (F : SimpleGraph V) [DecidableRel F.Adj] (W : Graphon Ω μ) :
    homDensityOnSpace (μ := μ) F (SeparationQuotient.mk W) = homDensity F W :=
  SeparationQuotient.lift_mk
    (fun _ _ h => (h.map (lipschitzWith_homDensity F).continuous).eq) W

/-- Homomorphism density on graphon space is nonnegative. -/
theorem homDensityOnSpace_nonneg (F : SimpleGraph V) [DecidableRel F.Adj] (W : GraphonSpace Ω μ) :
    0 ≤ homDensityOnSpace F W := by
  refine (SeparationQuotient.surjective_mk.forall
    (p := fun W => 0 ≤ homDensityOnSpace (μ := μ) F W)).2 (fun U => ?_) W
  rw [homDensityOnSpace_mk]
  exact homDensity_nonneg F U

/-- Homomorphism density on graphon space is at most `1`. -/
theorem homDensityOnSpace_le_one (F : SimpleGraph V) [DecidableRel F.Adj] (W : GraphonSpace Ω μ) :
    homDensityOnSpace F W ≤ 1 := by
  refine (SeparationQuotient.surjective_mk.forall
    (p := fun W => homDensityOnSpace (μ := μ) F W ≤ 1)).2 (fun U => ?_) W
  rw [homDensityOnSpace_mk]
  exact homDensity_le_one F U

/-- Homomorphism density on graphon space is Lipschitz with constant the number of edges of the
finite graph. -/
theorem lipschitzWith_homDensityOnSpace (F : SimpleGraph V) [DecidableRel F.Adj] :
    LipschitzWith (F.edgeFinset.card : NNReal) (homDensityOnSpace (μ := μ) F) := by
  refine LipschitzWith.of_dist_le_mul (SeparationQuotient.surjective_mk.forall₂.2 fun U W => ?_)
  rw [homDensityOnSpace_mk, homDensityOnSpace_mk, SeparationQuotient.dist_mk]
  exact (lipschitzWith_homDensity F).dist_le_mul U W

/-- Every finite-graph homomorphism density is continuous on graphon space. -/
theorem continuous_homDensityOnSpace (F : SimpleGraph V) [DecidableRel F.Adj] :
    Continuous (homDensityOnSpace (μ := μ) F) :=
  (lipschitzWith_homDensityOnSpace (μ := μ) F).continuous

section Structural

variable {V₁ V₂ : Type*} [Fintype V₁] [Fintype V₂]

/-- **Normalization on graphon space.** The edgeless graph has homomorphism density `1`. -/
@[simp]
theorem homDensityOnSpace_bot (x : GraphonSpace Ω μ) :
    homDensityOnSpace (⊥ : SimpleGraph V) x = 1 := by
  obtain ⟨W, rfl⟩ := SeparationQuotient.surjective_mk x
  rw [homDensityOnSpace_mk, homDensity_bot]

/-- Relabelling a finite graph along an embedding does not change its homomorphism density on
graphon space. -/
@[simp]
theorem homDensityOnSpace_map_embedding [DecidableEq V₂] (F : SimpleGraph V₁)
    [DecidableRel F.Adj] (f : V₁ ↪ V₂) (x : GraphonSpace Ω μ) :
    homDensityOnSpace (F.map f) x = homDensityOnSpace F x := by
  obtain ⟨W, rfl⟩ := SeparationQuotient.surjective_mk x
  rw [homDensityOnSpace_mk, homDensityOnSpace_mk, homDensity_map_embedding]

/-- **Multiplicativity on graphon space.** `t(F₁ ⊕g F₂, x) = t(F₁, x) · t(F₂, x)`. -/
@[simp]
theorem homDensityOnSpace_sum (F₁ : SimpleGraph V₁) [DecidableRel F₁.Adj] (F₂ : SimpleGraph V₂)
    [DecidableRel F₂.Adj] (x : GraphonSpace Ω μ) :
    homDensityOnSpace (F₁ ⊕g F₂) x = homDensityOnSpace F₁ x * homDensityOnSpace F₂ x := by
  obtain ⟨W, rfl⟩ := SeparationQuotient.surjective_mk x
  rw [homDensityOnSpace_mk, homDensityOnSpace_mk, homDensityOnSpace_mk, homDensity_sum]

end Structural

/-! ### Homomorphism densities as bounded continuous functions -/

section BoundedContinuous

variable {V₁ V₂ : Type*} [Fintype V₁] [Fintype V₂]

/-- The homomorphism density of a finite graph, as a bounded continuous function on graphon
space. It takes values in `[0, 1]`. -/
def homDensityBCF (F : SimpleGraph V) [DecidableRel F.Adj] : GraphonSpace Ω μ →ᵇ ℝ :=
  .mkOfBound ⟨homDensityOnSpace F, continuous_homDensityOnSpace F⟩ 1 fun x y =>
    Real.dist_le_of_mem_Icc_01 ⟨homDensityOnSpace_nonneg F x, homDensityOnSpace_le_one F x⟩
      ⟨homDensityOnSpace_nonneg F y, homDensityOnSpace_le_one F y⟩

@[simp]
theorem homDensityBCF_apply (F : SimpleGraph V) [DecidableRel F.Adj] (x : GraphonSpace Ω μ) :
    homDensityBCF F x = homDensityOnSpace F x := (rfl)

/-- The edgeless graph has constant homomorphism density `1` as a bounded continuous function. -/
@[simp]
theorem homDensityBCF_bot :
    homDensityBCF (μ := μ) (⊥ : SimpleGraph V) = 1 := by
  ext x
  simp

/-- Relabelling along an embedding preserves the bounded continuous homomorphism density. -/
@[simp]
theorem homDensityBCF_map_embedding [DecidableEq V₂] (F : SimpleGraph V₁)
    [DecidableRel F.Adj] (f : V₁ ↪ V₂) :
    homDensityBCF (μ := μ) (F.map f) = homDensityBCF F := by
  ext x
  simp

/-- The homomorphism density of a disjoint union is the product of the homomorphism densities, as
bounded continuous functions on graphon space. -/
@[simp]
theorem homDensityBCF_sum (F₁ : SimpleGraph V₁) [DecidableRel F₁.Adj] (F₂ : SimpleGraph V₂)
    [DecidableRel F₂.Adj] :
    homDensityBCF (μ := μ) (F₁ ⊕g F₂) = homDensityBCF F₁ * homDensityBCF F₂ := by
  ext x
  simp

/-- Every homomorphism density is that of a graph on some `Fin n`: relabel the vertices along
`Fintype.equivFin`. -/
private theorem exists_homDensityBCF_fin_eq (F : SimpleGraph V) [DecidableRel F.Adj] :
    ∃ (n : ℕ) (F' : SimpleGraph (Fin n)) (_ : DecidableRel F'.Adj),
      homDensityBCF (μ := μ) F' = homDensityBCF F := by
  refine ⟨Fintype.card V, F.map (Fintype.equivFin V).toEmbedding, inferInstance, ?_⟩
  ext x
  exact homDensityOnSpace_map_embedding F (Fintype.equivFin V).toEmbedding x

/-- **The homomorphism-density submonoid.** The bounded continuous functions on graphon space of
the form `t(F, ·)` for a finite graph `F`, indexed by graphs on `Fin n`. They are closed under
products, since `t(F₁, ·) t(F₂, ·) = t(F₁ ⊕g F₂, ·)`, and contain the constant `1 = t(⊥, ·)`.
`homDensityBCF_mem_homDensitySubmonoid` admits graphs on any finite vertex type. -/
def homDensitySubmonoid : Submonoid (GraphonSpace Ω μ →ᵇ ℝ) where
  carrier := {g | ∃ (n : ℕ) (F : SimpleGraph (Fin n)) (_ : DecidableRel F.Adj),
    homDensityBCF F = g}
  one_mem' := ⟨0, ⊥, inferInstance, by ext x; simp⟩
  mul_mem' := by
    rintro _ _ ⟨n₁, F₁, _, rfl⟩ ⟨n₂, F₂, _, rfl⟩
    rw [← homDensityBCF_sum]
    exact exists_homDensityBCF_fin_eq (F₁ ⊕g F₂)

/-- A member of the homomorphism-density submonoid is the density of a graph on some `Fin n`. -/
theorem mem_homDensitySubmonoid_iff {g : GraphonSpace Ω μ →ᵇ ℝ} :
    g ∈ homDensitySubmonoid ↔
      ∃ (n : ℕ) (F : SimpleGraph (Fin n)) (_ : DecidableRel F.Adj), homDensityBCF F = g :=
  (Iff.rfl)

/-- The homomorphism density of a graph on any finite vertex type lies in the homomorphism-density
submonoid. -/
theorem homDensityBCF_mem_homDensitySubmonoid (F : SimpleGraph V) [DecidableRel F.Adj] :
    homDensityBCF F ∈ homDensitySubmonoid (μ := μ) :=
  exists_homDensityBCF_fin_eq F

end BoundedContinuous

end DenseGraphLimits

end TauCeti
