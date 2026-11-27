/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Continuous.LieSmoothVector.BasisChange
public import TauCeti.RepresentationTheory.Continuous.LieSmoothVector.Topology

/-!
# The topology of the smooth vectors does not depend on the basis

Let `π` be a continuous representation of a real Lie group `G` on a normed space `V`, and let
`X` and `Y` be finite families of left-invariant derivations. The spaces
`ContRepresentation.LieSmoothSpace I π X` and `ContRepresentation.LieSmoothSpace I π Y` have the
same elements, the smooth vectors of `π`, with the topologies of the word seminorms along `X` and
along `Y`.

If every `Y j` is a real combination `∑ i, c j i • X i`, then
`P^Y_k ≤ (1 + ∑ j, ∑ i, |c j i|)^k P^X_k` (`ContRepresentation.wordSeminorm_le_of_eq_sum`), so the
identity of the smooth vectors is continuous from the `X`-topology to the `Y`-topology. When `X`
and `Y` span the same real subspace, for instance when both are bases of the Lie algebra, it is a
continuous linear equivalence: the topology of the smooth vectors does not depend on the basis.

## Main definitions

* `ContRepresentation.LieSmoothSpace.changeFamily`: the identity of the smooth vectors, as a
  linear equivalence `LieSmoothSpace I π X ≃ₗ[𝕜] LieSmoothSpace I π Y`.
* `ContRepresentation.LieSmoothSpace.changeFamilyCLE`: the same map as a continuous linear
  equivalence, when `X` and `Y` span the same real subspace.
* `ContRepresentation.LieSmoothSpace.basisCLE`: the continuous linear equivalence between the
  topologies of two real bases of the Lie algebra.

## Main results

* `ContRepresentation.LieSmoothSpace.continuous_changeFamily`: if every `Y j` lies in the real
  span of `X`, the identity of the smooth vectors is continuous from the `X`-topology to the
  `Y`-topology.
* `ContRepresentation.LieSmoothSpace.continuous_changeFamily_of_span_eq_top`: the same when `X`
  spans the Lie algebra, for any finite family `Y`.

## References

* J. Bernstein, B. Krötz, *Smooth Fréchet globalizations of Harish-Chandra modules*,
  Israel J. Math. 199 (2014), §§2.1–2.4.
-/

public section

noncomputable section

open scoped ContDiff Manifold

namespace ContRepresentation

namespace LieSmoothSpace

open TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G] [LieGroup I ∞ G]
  {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  {𝕜 : Type*} [NormedField 𝕜] [NormedSpace 𝕜 V] [SMulCommClass ℝ 𝕜 V]
  {π : ContRepresentation 𝕜 G V} {ι κ : Type*}

attribute [local instance] LieGroup.minSmoothness_of_isRCLikeNormedField

variable (I π) in
/-- The identity of the smooth vectors, from the topology of the word seminorms along `X` to that
along `Y`, as a linear equivalence. -/
def changeFamily (X : ι → LeftInvariantDerivation I G) (Y : κ → LeftInvariantDerivation I G) :
    LieSmoothSpace I π X ≃ₗ[𝕜] LieSmoothSpace I π Y :=
  (linearEquiv I π X).trans (linearEquiv I π Y).symm

@[simp]
theorem toSmooth_changeFamily (X : ι → LeftInvariantDerivation I G)
    (Y : κ → LeftInvariantDerivation I G) (v : LieSmoothSpace I π X) :
    (changeFamily I π X Y v).toSmooth = v.toSmooth := by
  simp [changeFamily]

@[simp]
theorem changeFamily_symm (X : ι → LeftInvariantDerivation I G)
    (Y : κ → LeftInvariantDerivation I G) :
    (changeFamily I π X Y).symm = changeFamily I π Y X :=
  (rfl)

variable [FiniteDimensional ℝ E] [T2Space G] [BoundarylessManifold I G] [Fintype ι] [Fintype κ]
  [NormedAlgebra ℝ 𝕜] [IsScalarTower ℝ 𝕜 V]

/-- **The identity of the smooth vectors is continuous** from the topology of the word seminorms
along `X` to that along `Y`, when every `Y j` lies in the real span of `X`: if
`Y j = ∑ i, c j i • X i`, then `P^Y_k ≤ (1 + ∑ j, ∑ i, |c j i|)^k P^X_k`. -/
theorem continuous_changeFamily {X : ι → LeftInvariantDerivation I G}
    {Y : κ → LeftInvariantDerivation I G} (hY : ∀ j, Y j ∈ Submodule.span ℝ (Set.range X)) :
    Continuous (changeFamily I π X Y) := by
  choose c hc using fun j ↦ (Submodule.mem_span_range_iff_exists_fun ℝ).mp (hY j)
  refine WithSeminorms.continuous_of_isBounded (withSeminorms I π X) (withSeminorms I π Y)
    (changeFamily I π X Y).toLinearMap
    (Seminorm.IsBounded.of_real fun k ↦ ⟨{k}, (1 + ∑ j, ∑ i, |c j i|) ^ k, fun v ↦ ?_⟩)
  simp only [Finset.sup_singleton, LinearEquiv.coe_coe, seminormFamily_apply,
    toSmooth_changeFamily]
  exact wordSeminorm_le_of_eq_sum X c (fun j ↦ (hc j).symm) k v.toSmooth

/-- **The identity of the smooth vectors is continuous** from the topology of the word seminorms
along a spanning family `X` to that along any finite family `Y`. -/
theorem continuous_changeFamily_of_span_eq_top {X : ι → LeftInvariantDerivation I G}
    (hX : Submodule.span ℝ (Set.range X) = ⊤) (Y : κ → LeftInvariantDerivation I G) :
    Continuous (changeFamily I π X Y) :=
  continuous_changeFamily fun _ ↦ hX ▸ Submodule.mem_top

variable (I π) in
/-- **The topology of the smooth vectors depends only on the span of the family.** If `X` and `Y`
span the same real subspace of the Lie algebra, the identity of the smooth vectors is a
continuous linear equivalence between the topologies of the word seminorms along `X` and along
`Y`. -/
def changeFamilyCLE {X : ι → LeftInvariantDerivation I G} {Y : κ → LeftInvariantDerivation I G}
    (h : Submodule.span ℝ (Set.range X) = Submodule.span ℝ (Set.range Y)) :
    LieSmoothSpace I π X ≃L[𝕜] LieSmoothSpace I π Y where
  toLinearEquiv := changeFamily I π X Y
  continuous_toFun := continuous_changeFamily fun j ↦ h ▸ Submodule.subset_span ⟨j, rfl⟩
  continuous_invFun := continuous_changeFamily fun i ↦ h.symm ▸ Submodule.subset_span ⟨i, rfl⟩

@[simp]
theorem toSmooth_changeFamilyCLE {X : ι → LeftInvariantDerivation I G}
    {Y : κ → LeftInvariantDerivation I G}
    (h : Submodule.span ℝ (Set.range X) = Submodule.span ℝ (Set.range Y))
    (v : LieSmoothSpace I π X) :
    (changeFamilyCLE I π h v).toSmooth = v.toSmooth :=
  toSmooth_changeFamily X Y v

@[simp]
theorem changeFamilyCLE_symm {X : ι → LeftInvariantDerivation I G}
    {Y : κ → LeftInvariantDerivation I G}
    (h : Submodule.span ℝ (Set.range X) = Submodule.span ℝ (Set.range Y)) :
    (changeFamilyCLE I π h).symm = changeFamilyCLE I π h.symm :=
  (rfl)

variable (I π) in
/-- **The topology of the smooth vectors does not depend on the basis.** For two real bases `b`
and `b'` of the Lie algebra, the identity of the smooth vectors is a continuous linear
equivalence between the topologies of the word seminorms along `b` and along `b'`. -/
def basisCLE (b : Module.Basis ι ℝ (LeftInvariantDerivation I G))
    (b' : Module.Basis κ ℝ (LeftInvariantDerivation I G)) :
    LieSmoothSpace I π b ≃L[𝕜] LieSmoothSpace I π b' :=
  changeFamilyCLE I π (by rw [b.span_eq, b'.span_eq])

@[simp]
theorem toSmooth_basisCLE (b : Module.Basis ι ℝ (LeftInvariantDerivation I G))
    (b' : Module.Basis κ ℝ (LeftInvariantDerivation I G)) (v : LieSmoothSpace I π b) :
    (basisCLE I π b b' v).toSmooth = v.toSmooth :=
  toSmooth_changeFamily _ _ v

@[simp]
theorem basisCLE_symm (b : Module.Basis ι ℝ (LeftInvariantDerivation I G))
    (b' : Module.Basis κ ℝ (LeftInvariantDerivation I G)) :
    (basisCLE I π b b').symm = basisCLE I π b' b :=
  (rfl)

end LieSmoothSpace

end ContRepresentation
