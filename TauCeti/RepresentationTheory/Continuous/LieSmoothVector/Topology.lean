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
import TauCeti.Analysis.LocallyConvex.WithSeminorms

/-!
# The topology of the word seminorms on smooth vectors

Let `π` be a continuous representation of a real Lie group `G` on a normed space `V` over a
normed field `𝕜`, and fix a finite family `X : ι → LeftInvariantDerivation I G`, for
instance a basis of the Lie algebra. The smooth vectors `lieSmoothVectors I π` carry the countable
family of word seminorms `P_k = ContRepresentation.wordSeminorm I π X k`, `k : ℕ`. This file puts
the topology of this family on `ContRepresentation.LieSmoothSpace I π X`, a copy (a one-field
structure) of the smooth vectors, rather than on `lieSmoothVectors I π` itself, which keeps the
subspace topology of `V`. The linear equivalence `ContRepresentation.LieSmoothSpace.linearEquiv`
moves between the two. The elements are the smooth vectors for every `X`, but in general the
topology depends on `X` (for an empty family, every `P_k` is the norm of `V`). When `X` spans the
Lie algebra it is the usual topology of the smooth vectors; this file does not prove that.

The word seminorm of order zero is the norm of `V`
(`ContRepresentation.wordSeminorm_zero`). So the family separates points and the topology is
Hausdorff; it is first countable, as the family is countable, and hence metrizable; it is
locally convex; and the inclusion into `V` is a continuous injective linear map
(`ContRepresentation.LieSmoothSpace.inclusion`). For `Y` in the real span of `X`, the derived
action `dπ(Y)` is continuous, since `P_k(dπ(Y) v) ≤ C P_{k+1}(v)`.

## Main definitions

* `ContRepresentation.LieSmoothSpace I π X`: the smooth vectors of `π`, with the topology of
  the word seminorms of `X`.
* `ContRepresentation.LieSmoothSpace.seminormFamily I π X`: the word seminorms `P_k` on it.
* `ContRepresentation.LieSmoothSpace.inclusion`: the inclusion into `V`, as a continuous linear
  map.
* `ContRepresentation.LieSmoothSpace.derivative`: the derived action `dπ(Y)` of an element `Y`
  of the real span of `X`, as a continuous linear map.

## Main results

* `ContRepresentation.LieSmoothSpace.withSeminorms`: the topology is that of the word
  seminorms.
* `ContRepresentation.LieSmoothSpace.instT2Space`,
  `ContRepresentation.LieSmoothSpace.instMetrizableSpace` and
  `ContRepresentation.LieSmoothSpace.instLocallyConvexSpace`: the topology is Hausdorff,
  metrizable and locally convex.
* `ContRepresentation.LieSmoothSpace.inclusion_injective`: the inclusion into `V` is injective.
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

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G] [LieGroup I ∞ G]
  {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  {𝕜 : Type*} [NormedField 𝕜] [NormedSpace 𝕜 V] [SMulCommClass ℝ 𝕜 V]
  (π : ContRepresentation 𝕜 G V)
  {ι : Type*}

attribute [local instance] LieGroup.minSmoothness_of_isRCLikeNormedField

/-- The smooth vectors `lieSmoothVectors I π` of a continuous representation, as a type carrying
the topology of the word seminorms `P_k` of the family `X` (`LieSmoothSpace.withSeminorms`). It
is a copy of the smooth vectors: the submodule `lieSmoothVectors I π` itself keeps the subspace
topology of `V`. In general the topology depends on `X`; it is the topology of the smooth vectors
when `X` spans the Lie algebra, for instance when `X` is a basis. -/
@[ext]
structure LieSmoothSpace (X : ι → LeftInvariantDerivation I G) where
  /-- A smooth vector, as an element of `LieSmoothSpace I π X`. -/
  ofSmooth ::
  /-- The smooth vector underlying an element of `LieSmoothSpace I π X`. -/
  toSmooth : lieSmoothVectors I π

namespace LieSmoothSpace

variable (X : ι → LeftInvariantDerivation I G)

/-- `LieSmoothSpace I π X` is a copy of the smooth vectors. -/
def equiv : LieSmoothSpace I π X ≃ lieSmoothVectors I π where
  toFun := toSmooth
  invFun := ofSmooth
  left_inv _ := rfl
  right_inv _ := rfl

instance instAddCommGroup : AddCommGroup (LieSmoothSpace I π X) :=
  (equiv I π X).addCommGroup

/-- `LieSmoothSpace I π X` is a copy of the smooth vectors, as additive groups. -/
def addEquiv : LieSmoothSpace I π X ≃+ lieSmoothVectors I π where
  __ := equiv I π X
  map_add' _ _ := rfl

instance instModule : Module 𝕜 (LieSmoothSpace I π X) :=
  (addEquiv I π X).module 𝕜

/-- `LieSmoothSpace I π X` is a copy of the smooth vectors, as `𝕜`-modules. -/
def linearEquiv : LieSmoothSpace I π X ≃ₗ[𝕜] lieSmoothVectors I π :=
  (addEquiv I π X).linearEquiv 𝕜

variable {I π X}

@[simp]
theorem toSmooth_zero : (0 : LieSmoothSpace I π X).toSmooth = 0 :=
  (rfl)

@[simp]
theorem toSmooth_add (v w : LieSmoothSpace I π X) : (v + w).toSmooth = v.toSmooth + w.toSmooth :=
  (rfl)

@[simp]
theorem toSmooth_neg (v : LieSmoothSpace I π X) : (-v).toSmooth = -v.toSmooth :=
  (rfl)

@[simp]
theorem toSmooth_sub (v w : LieSmoothSpace I π X) : (v - w).toSmooth = v.toSmooth - w.toSmooth :=
  (rfl)

@[simp]
theorem toSmooth_smul (c : 𝕜) (v : LieSmoothSpace I π X) : (c • v).toSmooth = c • v.toSmooth :=
  (rfl)

@[simp]
theorem equiv_apply (v : LieSmoothSpace I π X) : equiv I π X v = v.toSmooth :=
  (rfl)

@[simp]
theorem equiv_symm_apply (v : lieSmoothVectors I π) : (equiv I π X).symm v = ofSmooth v :=
  (rfl)

@[simp]
theorem addEquiv_apply (v : LieSmoothSpace I π X) : addEquiv I π X v = v.toSmooth :=
  (rfl)

@[simp]
theorem addEquiv_symm_apply (v : lieSmoothVectors I π) : (addEquiv I π X).symm v = ofSmooth v :=
  (rfl)

@[simp]
theorem linearEquiv_apply (v : LieSmoothSpace I π X) : linearEquiv I π X v = v.toSmooth :=
  (rfl)

@[simp]
theorem linearEquiv_symm_apply (v : lieSmoothVectors I π) :
    (linearEquiv I π X).symm v = ofSmooth v :=
  (rfl)

section RealModule

variable [NormedSpace ℝ 𝕜] [IsScalarTower ℝ 𝕜 V]

variable (I π X) in
instance instModuleReal : Module ℝ (LieSmoothSpace I π X) :=
  (addEquiv I π X).module ℝ

@[simp]
theorem toSmooth_real_smul (r : ℝ) (v : LieSmoothSpace I π X) :
    (r • v).toSmooth = r • v.toSmooth :=
  (rfl)

variable (I π X) in
instance instIsScalarTower : IsScalarTower ℝ 𝕜 (LieSmoothSpace I π X) :=
  ⟨fun r c v ↦ congrArg ofSmooth (smul_assoc r c v.toSmooth)⟩

end RealModule

variable [FiniteDimensional ℝ E] [T2Space G] [BoundarylessManifold I G] [Fintype ι]

variable (I π X) in
/-- The word seminorms `P_k` of `X`, `k : ℕ`, on `LieSmoothSpace I π X`. -/
def seminormFamily : SeminormFamily 𝕜 (LieSmoothSpace I π X) ℕ :=
  fun k ↦ (wordSeminorm I π X k).comp (linearEquiv I π X).toLinearMap

@[simp]
theorem seminormFamily_apply (k : ℕ) (v : LieSmoothSpace I π X) :
    seminormFamily I π X k v = wordSeminorm I π X k v.toSmooth :=
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
  ext1
  simpa using h0

instance instT2Space : T2Space (LieSmoothSpace I π X) :=
  inferInstance

/-- The countable family of word seminorms gives a first countable topology. -/
instance instFirstCountableTopology : FirstCountableTopology (LieSmoothSpace I π X) :=
  have : (𝓝 (0 : LieSmoothSpace I π X)).IsCountablyGenerated := by
    rw [(seminormFamily I π X).withSeminorms_iff_nhds_eq_iInf.mp (withSeminorms I π X)]
    exact Filter.iInf.isCountablyGenerated _
  have : (uniformity (LieSmoothSpace I π X)).IsCountablyGenerated :=
    IsUniformAddGroup.uniformity_countably_generated
  UniformSpace.firstCountableTopology _

/-- **The topology of the word seminorms is metrizable.** -/
instance instMetrizableSpace : TopologicalSpace.MetrizableSpace (LieSmoothSpace I π X) :=
  have : (uniformity (LieSmoothSpace I π X)).IsCountablyGenerated :=
    IsUniformAddGroup.uniformity_countably_generated
  UniformSpace.metrizableSpace

section LocallyConvex

variable [NormedSpace ℝ 𝕜] [IsScalarTower ℝ 𝕜 V]

/-- **The topology of the word seminorms is locally convex.** -/
instance instLocallyConvexSpace : LocallyConvexSpace ℝ (LieSmoothSpace I π X) :=
  (withSeminorms I π X).toLocallyConvexSpace

instance instContinuousSMulReal : ContinuousSMul ℝ (LieSmoothSpace I π X) :=
  IsScalarTower.continuousSMul 𝕜

end LocallyConvex

/-- **The inclusion of the smooth vectors into `V` is continuous** for the topology of the word
seminorms, since `P_0` is the norm of `V`. -/
def inclusion : LieSmoothSpace I π X →L[𝕜] V where
  toLinearMap := (lieSmoothVectors I π).subtype ∘ₗ (linearEquiv I π X).toLinearMap
  cont := WithSeminorms.continuous_normedSpace_rng V (withSeminorms I π X) _
    ⟨{0}, 1, fun v ↦ by simp⟩

variable {I π X}

@[simp]
theorem inclusion_apply (v : LieSmoothSpace I π X) :
    inclusion I π X v = (v.toSmooth : V) :=
  (rfl)

/-- The inclusion of the smooth vectors into `V` is injective. -/
theorem inclusion_injective : Function.Injective (inclusion I π X) := fun _ _ h ↦
  LieSmoothSpace.ext (Subtype.ext h)

/-- **Convergence in `LieSmoothSpace I π X` is convergence in every word seminorm.** -/
theorem tendsto_nhds {α : Type*} {l : Filter α} {u : α → LieSmoothSpace I π X}
    {v : LieSmoothSpace I π X} :
    Tendsto u l (𝓝 v) ↔ ∀ k, Tendsto (fun a ↦ seminormFamily I π X k (u a - v)) l (𝓝 0) :=
  (withSeminorms I π X).tendsto_nhds_iff_tendsto_zero

section Derivative

variable [NormedAlgebra ℝ 𝕜] [IsScalarTower ℝ 𝕜 V]

variable (I π X) in
/-- **The derived action `dπ(Y)` is continuous** on `LieSmoothSpace I π X` for every `Y` in the
real span of `X`: if `Y = ∑ i, c i • X i`, then `P_k(dπ(Y) v) ≤ (∑ i, |c i|) P_{k+1}(v)`
(`ContRepresentation.wordSeminorm_lieSmoothVectorsDerivative_le_of_eq_sum`). -/
def derivative (Y : LeftInvariantDerivation I G) (hY : Y ∈ Submodule.span ℝ (Set.range X)) :
    LieSmoothSpace I π X →L[𝕜] LieSmoothSpace I π X where
  toLinearMap := (linearEquiv I π X).symm.toLinearMap ∘ₗ lieSmoothVectorsDerivative I π Y ∘ₗ
    (linearEquiv I π X).toLinearMap
  cont := by
    obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℝ).mp hY
    refine WithSeminorms.continuous_of_isBounded (withSeminorms I π X) (withSeminorms I π X) _
      (Seminorm.IsBounded.of_real fun k ↦ ⟨{k + 1}, ∑ i, |c i|, fun v ↦ ?_⟩)
    simp only [Finset.sup_singleton, seminormFamily_apply, LinearMap.comp_apply,
      LinearEquiv.coe_coe, linearEquiv_apply, linearEquiv_symm_apply]
    exact wordSeminorm_lieSmoothVectorsDerivative_le_of_eq_sum X k c hc.symm v.toSmooth

/-- The continuous derived action `dπ(Y)` is the derived action on the smooth vectors. -/
@[simp]
theorem toSmooth_derivative (Y : LeftInvariantDerivation I G)
    (hY : Y ∈ Submodule.span ℝ (Set.range X)) (v : LieSmoothSpace I π X) :
    (derivative I π X Y hY v).toSmooth = lieSmoothVectorsDerivative I π Y v.toSmooth :=
  (rfl)

end Derivative

end LieSmoothSpace

end ContRepresentation
