/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.LocallyConvex.WithSeminorms
public import Mathlib.Topology.Algebra.UniformFilterBasis
public import Mathlib.Topology.Metrizable.Uniformity
public import TauCeti.RepresentationTheory.Continuous.LieSmoothVector.Seminorm

/-!
# The topology of the word seminorms on smooth vectors

Let `π` be a continuous representation of a real Lie group `G` on a normed space `V` over a
nontrivially normed field `𝕜`, and fix a finite family `X : ι → LeftInvariantDerivation I G`, for
instance a basis of the Lie algebra. The smooth vectors `lieSmoothVectors I π` carry the countable
family of word seminorms `P_k = ContRepresentation.wordSeminorm I π X k`, `k : ℕ`. This file puts
the topology of this family on the type synonym `ContRepresentation.LieSmoothSpace I π X` of the
smooth vectors, rather than on `lieSmoothVectors I π` itself, which keeps the subspace topology
of `V`.

The word seminorm of order zero is the norm of `V`
(`ContRepresentation.wordSeminorm_zero`). So the family separates points and the topology is
Hausdorff; it is first countable, as the family is countable, and hence metrizable; it is
locally convex; and the inclusion into `V` is a continuous injective linear map
(`ContRepresentation.LieSmoothSpace.inclusion`).

## Main definitions

* `ContRepresentation.LieSmoothSpace I π X`: the smooth vectors of `π`, with the topology of
  the word seminorms of `X`.
* `ContRepresentation.LieSmoothSpace.seminormFamily I π X`: the word seminorms `P_k` on it.
* `ContRepresentation.LieSmoothSpace.inclusion`: the inclusion into `V`, as a continuous linear
  map.

## Main results

* `ContRepresentation.LieSmoothSpace.withSeminorms`: the topology is that of the word
  seminorms.
* `ContRepresentation.LieSmoothSpace.instT2Space`,
  `ContRepresentation.LieSmoothSpace.instMetrizableSpace` and
  `ContRepresentation.LieSmoothSpace.instLocallyConvexSpace`: the topology is Hausdorff,
  metrizable and locally convex.
* `ContRepresentation.LieSmoothSpace.injective_inclusion`: the inclusion into `V` is injective.
* `ContRepresentation.LieSmoothSpace.tendsto_nhds`: convergence is convergence in every word
  seminorm.

## References

* J. Bernstein, B. Krötz, *Smooth Fréchet globalizations of Harish-Chandra modules*,
  Israel J. Math. 199 (2014), §§2.1–2.4.
-/

public section

noncomputable section

open scoped ContDiff Manifold Topology

open Filter

namespace ContRepresentation

open TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G]
  [LieGroup I ∞ G] [T2Space G] [BoundarylessManifold I G]
  {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  {𝕜 : Type*} [NontriviallyNormedField 𝕜] [NormedSpace 𝕜 V] [SMulCommClass ℝ 𝕜 V]
  (π : ContRepresentation 𝕜 G V)
  {ι : Type*} [Fintype ι]

attribute [local instance] LieGroup.minSmoothness_of_isRCLikeNormedField

/-- The smooth vectors `lieSmoothVectors I π` of a continuous representation, as a type carrying
the topology of the word seminorms `P_k` of the family `X` (`LieSmoothSpace.withSeminorms`). It
is a copy of the smooth vectors: the submodule `lieSmoothVectors I π` itself keeps the subspace
topology of `V`. -/
structure LieSmoothSpace (X : ι → LeftInvariantDerivation I G) where
  /-- A smooth vector, as an element of `LieSmoothSpace I π X`. -/
  ofSmooth ::
  /-- The smooth vector underlying an element of `LieSmoothSpace I π X`. -/
  toSmooth : lieSmoothVectors I π

namespace LieSmoothSpace

variable (X : ι → LeftInvariantDerivation I G)

/-- `LieSmoothSpace I π X` is a copy of the smooth vectors. -/
def equivSmooth : LieSmoothSpace I π X ≃ lieSmoothVectors I π where
  toFun := toSmooth
  invFun := ofSmooth
  left_inv _ := rfl
  right_inv _ := rfl

instance instAddCommGroup : AddCommGroup (LieSmoothSpace I π X) :=
  (equivSmooth I π X).addCommGroup

/-- `LieSmoothSpace I π X` is a copy of the smooth vectors, as additive groups. -/
def addEquivSmooth : LieSmoothSpace I π X ≃+ lieSmoothVectors I π where
  __ := equivSmooth I π X
  map_add' _ _ := rfl

instance instModule : Module 𝕜 (LieSmoothSpace I π X) :=
  (addEquivSmooth I π X).module 𝕜

/-- The identification of the smooth vectors with `LieSmoothSpace I π X`, as a linear
equivalence. -/
def equiv : lieSmoothVectors I π ≃ₗ[𝕜] LieSmoothSpace I π X :=
  ((addEquivSmooth I π X).linearEquiv 𝕜).symm

/-- The word seminorms `P_k` of `X`, `k : ℕ`, on `LieSmoothSpace I π X`. -/
def seminormFamily : SeminormFamily 𝕜 (LieSmoothSpace I π X) ℕ :=
  fun k ↦ (wordSeminorm I π X k).comp (equiv I π X).symm.toLinearMap

variable {I π X}

theorem seminormFamily_apply (k : ℕ) (v : LieSmoothSpace I π X) :
    seminormFamily I π X k v = wordSeminorm I π X k ((equiv I π X).symm v) :=
  (rfl)

variable (I π X)

/-- The topology of the word seminorms. -/
instance instTopologicalSpace : TopologicalSpace (LieSmoothSpace I π X) :=
  (seminormFamily I π X).moduleFilterBasis.topology'

/-- **The topology of `LieSmoothSpace I π X` is that of the word seminorms `P_k`.** -/
theorem withSeminorms : WithSeminorms (seminormFamily I π X) :=
  ⟨rfl⟩

instance instIsTopologicalAddGroup : IsTopologicalAddGroup (LieSmoothSpace I π X) :=
  (seminormFamily I π X).addGroupFilterBasis.isTopologicalAddGroup

instance instContinuousSMul : ContinuousSMul 𝕜 (LieSmoothSpace I π X) :=
  (withSeminorms I π X).continuousSMul

instance instUniformSpace : UniformSpace (LieSmoothSpace I π X) :=
  fast_instance% (seminormFamily I π X).addGroupFilterBasis.uniformSpace

instance instIsUniformAddGroup : IsUniformAddGroup (LieSmoothSpace I π X) :=
  (seminormFamily I π X).addGroupFilterBasis.isUniformAddGroup

/-- **The word seminorms separate points**: `P_0` is the norm of `V`. -/
instance instT1Space : T1Space (LieSmoothSpace I π X) := by
  refine (withSeminorms I π X).T1_of_separating fun v hv ↦ ⟨0, fun h0 ↦ hv ?_⟩
  rw [seminormFamily_apply, wordSeminorm_zero, norm_eq_zero] at h0
  exact (equiv I π X).symm.injective (Subtype.ext (by rw [h0, map_zero]; rfl))

instance instT2Space : T2Space (LieSmoothSpace I π X) :=
  inferInstance

/-- The countable family of word seminorms gives a first countable topology. -/
instance instFirstCountableTopology : FirstCountableTopology (LieSmoothSpace I π X) :=
  (withSeminorms I π X).firstCountableTopology

/-- **The topology of the word seminorms is metrizable.** -/
instance instMetrizableSpace : TopologicalSpace.MetrizableSpace (LieSmoothSpace I π X) :=
  have : (uniformity (LieSmoothSpace I π X)).IsCountablyGenerated :=
    IsUniformAddGroup.uniformity_countably_generated
  UniformSpace.metrizableSpace

section LocallyConvex

variable [NormedSpace ℝ 𝕜] [IsScalarTower ℝ 𝕜 V]

instance instModuleReal : Module ℝ (LieSmoothSpace I π X) :=
  (addEquivSmooth I π X).module ℝ

instance instIsScalarTower : IsScalarTower ℝ 𝕜 (LieSmoothSpace I π X) :=
  ⟨fun r c v ↦ congrArg ofSmooth (smul_assoc r c v.toSmooth)⟩

/-- **The topology of the word seminorms is locally convex.** -/
instance instLocallyConvexSpace : LocallyConvexSpace ℝ (LieSmoothSpace I π X) :=
  (withSeminorms I π X).toLocallyConvexSpace

end LocallyConvex

/-- **The inclusion of the smooth vectors into `V` is continuous** for the topology of the word
seminorms, since `P_0` is the norm of `V`. -/
def inclusion : LieSmoothSpace I π X →L[𝕜] V where
  toLinearMap := (lieSmoothVectors I π).subtype ∘ₗ (equiv I π X).symm.toLinearMap
  cont := WithSeminorms.continuous_normedSpace_rng V (withSeminorms I π X) _
    ⟨{0}, 1, fun v ↦ by
      rw [Seminorm.comp_apply, coe_normSeminorm, Finset.sup_singleton, one_smul,
        seminormFamily_apply, wordSeminorm_zero]
      rfl⟩

variable {I π X}

@[simp]
theorem inclusion_apply (v : LieSmoothSpace I π X) :
    inclusion I π X v = ((equiv I π X).symm v : V) :=
  (rfl)

/-- The inclusion of the smooth vectors into `V` is injective. -/
theorem injective_inclusion : Function.Injective (inclusion I π X) := fun _ _ h ↦
  (equiv I π X).symm.injective (Subtype.ext h)

/-- **Convergence in `LieSmoothSpace I π X` is convergence in every word seminorm.** -/
theorem tendsto_nhds {α : Type*} {l : Filter α} {u : α → LieSmoothSpace I π X}
    {v : LieSmoothSpace I π X} :
    Tendsto u l (𝓝 v) ↔ ∀ k, Tendsto (fun a ↦ seminormFamily I π X k (u a - v)) l (𝓝 0) := by
  rw [(withSeminorms I π X).tendsto_nhds]
  refine ⟨fun h k ↦ Metric.tendsto_nhds.2 fun ε hε ↦ (h k ε hε).mono fun a ha ↦ ?_,
    fun h k ε hε ↦ (Metric.tendsto_nhds.1 (h k) ε hε).mono fun a ha ↦ ?_⟩
  · rwa [Real.dist_0_eq_abs, abs_of_nonneg (apply_nonneg _ _)]
  · rwa [Real.dist_0_eq_abs, abs_of_nonneg (apply_nonneg _ _)] at ha

end LieSmoothSpace

end ContRepresentation
