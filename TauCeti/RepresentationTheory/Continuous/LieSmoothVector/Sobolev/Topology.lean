/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Continuous.LieSmoothVector.Sobolev.Comparison
public import TauCeti.RepresentationTheory.Continuous.LieSmoothVector.Topology

/-!
# The Sobolev seminorms define the topology of the smooth vectors

Let `π` be a continuous representation of a real Lie group `G` and `X₁, …, X_m` a spanning family
of its Lie algebra of left-invariant derivations. `ContRepresentation.LieSmoothSpace I π X`
carries the topology of the word seminorms `P_k(v) = ∑_{|w| ≤ k} ‖dπ(X_w) v‖`. The Sobolev
seminorms `Q_k(v) = (∑_{|α| ≤ k} ‖dπ(X^α) v‖²)^{1/2}` over the ordered monomials define the same
topology, since `Q_k ≤ P_k` (`ContRepresentation.sobolevSeminorm_le_wordSeminorm`) and
`P_k ≤ C_k Q_k` (`ContRepresentation.exists_wordSeminorm_le_mul_sobolevSeminorm`).

## Main definitions

* `ContRepresentation.LieSmoothSpace.sobolevSeminormFamily I π X`: the Sobolev seminorms `Q_k`
  on `LieSmoothSpace I π X`.

## Main results

* `ContRepresentation.LieSmoothSpace.withSeminorms_sobolevSeminormFamily`: for a spanning family,
  the topology of `LieSmoothSpace I π X` is that of the Sobolev seminorms.

## References

* J. Bernstein, B. Krötz, *Smooth Fréchet globalizations of Harish-Chandra modules*,
  Israel J. Math. 199 (2014), §2.4.2–§2.4.3.
-/

public section

noncomputable section

open scoped ContDiff Manifold

namespace ContRepresentation

open TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G] [LieGroup I ∞ G] [T2Space G]
  [BoundarylessManifold I G]
  {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  {𝕜 : Type*} [NormedField 𝕜] [NormedSpace 𝕜 V] [SMulCommClass ℝ 𝕜 V]
  (π : ContRepresentation 𝕜 G V) {m : ℕ}

attribute [local instance] LieGroup.minSmoothness_of_isRCLikeNormedField

namespace LieSmoothSpace

variable (X : Fin m → LeftInvariantDerivation I G)

/-- The Sobolev seminorms `Q_k` of `X`, `k : ℕ`, on `LieSmoothSpace I π X`. -/
def sobolevSeminormFamily : SeminormFamily 𝕜 (LieSmoothSpace I π X) ℕ :=
  fun k ↦ (sobolevSeminorm I π X k).comp (linearEquiv I π X).toLinearMap

variable {I π X}

@[simp]
theorem sobolevSeminormFamily_apply (k : ℕ) (v : LieSmoothSpace I π X) :
    sobolevSeminormFamily I π X k v = sobolevSeminorm I π X k v.toSmooth := by
  rw [sobolevSeminormFamily, Seminorm.comp_apply, LinearEquiv.coe_coe, linearEquiv_apply]

variable [NormedAlgebra ℝ 𝕜] [IsScalarTower ℝ 𝕜 V]

/-- **The Sobolev seminorms define the topology of the smooth vectors.** For a spanning family
`X`, the topology of `LieSmoothSpace I π X`, that of the word seminorms `P_k`, is the topology of
the Sobolev seminorms `Q_k`, since `Q_k ≤ P_k ≤ C_k Q_k`. -/
theorem withSeminorms_sobolevSeminormFamily (hX : Submodule.span ℝ (Set.range X) = ⊤) :
    WithSeminorms (sobolevSeminormFamily I π X) := by
  refine (withSeminorms I π X).congr
    (Seminorm.IsBounded.of_real fun k ↦ ⟨{k}, 1, fun v ↦ ?_⟩)
    (Seminorm.IsBounded.of_real fun k ↦ ?_)
  · simpa using sobolevSeminorm_le_wordSeminorm X k v.toSmooth
  · obtain ⟨C, hC⟩ := exists_wordSeminorm_le_mul_sobolevSeminorm (π := π) X hX k
    refine ⟨{k}, C, fun v ↦ ?_⟩
    simpa using hC v.toSmooth

end LieSmoothSpace

end ContRepresentation
