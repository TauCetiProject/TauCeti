/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.TensorProduct.Submodule
public import TauCeti.RepresentationTheory.Continuous.LieSmoothVector.Sobolev.BaseChange
public import TauCeti.RepresentationTheory.Continuous.LieSmoothVector.Topology

/-!
# The Sobolev seminorms define the topology of the smooth vectors

Let `π` be a continuous representation of a real Lie group `G` on a normed space `V` over a normed
field `𝕜` containing `ℝ`, and let `X₁, …, X_n` be a spanning family of its Lie algebra of
left-invariant derivations. `ContRepresentation.LieSmoothSpace I π X` carries the topology of the
word seminorms `P_k(v) = ∑_{|w| ≤ k} ‖dπ(X_w) v‖`. For a family `Z₁, …, Z_m` spanning
`𝕜 ⊗[ℝ] Lie(G)` over `𝕜`, the Sobolev seminorms `Q^Z_k(v) = (∑_{|α| ≤ k} ‖dπ(Z^α) v‖²)^{1/2}` over
the ordered monomials define the same topology: `Q^Z_k ≤ P^Z_k ≤ C_k Q^Z_k`
(`ContRepresentation.baseChangeSobolevSeminorm_le_baseChangeWordSeminorm`,
`ContRepresentation.exists_baseChangeWordSeminorm_le_mul_baseChangeSobolevSeminorm`), and the word
seminorms along `Z` and along `1 ⊗ X`, which are those along `X`, bound each other
(`ContRepresentation.baseChangeWordSeminorm_le_of_eq_sum`). The case `Z = 1 ⊗ X` is the topology
theorem for the real Sobolev seminorms `Q_k(v) = (∑_{|α| ≤ k} ‖dπ(X^α) v‖²)^{1/2}`.

## Main definitions

* `ContRepresentation.LieSmoothSpace.sobolevSeminormFamily I π X`: the Sobolev seminorms `Q_k`
  on `LieSmoothSpace I π X`.
* `ContRepresentation.LieSmoothSpace.baseChangeSobolevSeminormFamily I π X Z`: the Sobolev
  seminorms `Q^Z_k` along a family `Z` of `𝕜 ⊗[ℝ] Lie(G)` on `LieSmoothSpace I π X`.

## Main results

* `ContRepresentation.LieSmoothSpace.withSeminorms_baseChangeSobolevSeminormFamily`: for a
  `𝕜`-spanning family `Z` of `𝕜 ⊗[ℝ] Lie(G)`, the topology of `LieSmoothSpace I π X` is that of the
  Sobolev seminorms `Q^Z_k`.
* `ContRepresentation.LieSmoothSpace.withSeminorms_sobolevSeminormFamily`: for a spanning family,
  the topology of `LieSmoothSpace I π X` is that of the Sobolev seminorms.

## References

* J. Bernstein, B. Krötz, *Smooth Fréchet globalizations of Harish-Chandra modules*,
  Israel J. Math. 199 (2014), §2.4.2–§2.4.3.
-/

public section

noncomputable section

open scoped ContDiff Manifold TensorProduct

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

variable [NormedAlgebra ℝ 𝕜] [IsScalarTower ℝ 𝕜 V] {ι : Type*}

variable (I π) in
/-- The Sobolev seminorms `Q^Z_k`, `k : ℕ`, along a family `Z` of `𝕜 ⊗[ℝ] Lie(G)`, on
`LieSmoothSpace I π X`. -/
def baseChangeSobolevSeminormFamily (X : ι → LeftInvariantDerivation I G)
    (Z : Fin m → 𝕜 ⊗[ℝ] LeftInvariantDerivation I G) :
    SeminormFamily 𝕜 (LieSmoothSpace I π X) ℕ :=
  fun k ↦ (baseChangeSobolevSeminorm I π Z k).comp (linearEquiv I π X).toLinearMap

@[simp]
theorem baseChangeSobolevSeminormFamily_apply (X : ι → LeftInvariantDerivation I G)
    (Z : Fin m → 𝕜 ⊗[ℝ] LeftInvariantDerivation I G) (k : ℕ) (v : LieSmoothSpace I π X) :
    baseChangeSobolevSeminormFamily I π X Z k v = baseChangeSobolevSeminorm I π Z k v.toSmooth := by
  rw [baseChangeSobolevSeminormFamily, Seminorm.comp_apply, LinearEquiv.coe_coe, linearEquiv_apply]

/-- **The Sobolev seminorms along a basis of the complexified Lie algebra define the topology of
the smooth vectors.** For a real spanning family `X` of `Lie(G)` and a family `Z` spanning
`𝕜 ⊗[ℝ] Lie(G)` over `𝕜`, the topology of `LieSmoothSpace I π X`, that of the word seminorms of
`X`, is the topology of the Sobolev seminorms `Q^Z_k`. -/
theorem withSeminorms_baseChangeSobolevSeminormFamily [Fintype ι]
    {X : ι → LeftInvariantDerivation I G} (hX : Submodule.span ℝ (Set.range X) = ⊤)
    {Z : Fin m → 𝕜 ⊗[ℝ] LeftInvariantDerivation I G} (hZ : Submodule.span 𝕜 (Set.range Z) = ⊤) :
    WithSeminorms (baseChangeSobolevSeminormFamily I π X Z) := by
  -- `Z j = ∑ i, c j i • (1 ⊗ X i)` and `1 ⊗ X j = ∑ i, d j i • Z i`.
  choose c hc using fun j ↦ (Submodule.mem_span_range_iff_exists_fun 𝕜).1
    (span_one_tmul_eq_top (A := 𝕜) hX ▸ Submodule.mem_top (x := Z j))
  choose d hd using fun j ↦ (Submodule.mem_span_range_iff_exists_fun 𝕜).1
    (hZ ▸ Submodule.mem_top (x := (1 : 𝕜) ⊗ₜ[ℝ] X j))
  refine (withSeminorms I π X).congr
    (Seminorm.IsBounded.of_real fun k ↦
      ⟨{k}, (1 + ∑ j, ∑ i, ‖c j i‖) ^ k, fun v ↦ ?_⟩)
    (Seminorm.IsBounded.of_real fun k ↦ ?_)
  · simpa using (baseChangeSobolevSeminorm_le_baseChangeWordSeminorm Z k v.toSmooth).trans
      (baseChangeWordSeminorm_le_of_eq_sum _ c (fun j ↦ (hc j).symm) k v.toSmooth)
  · obtain ⟨C, hC⟩ := exists_baseChangeWordSeminorm_le_mul_baseChangeSobolevSeminorm
      (π := π) Z hZ k
    refine ⟨{k}, (1 + ∑ j, ∑ i, ‖d j i‖) ^ k * C, fun v ↦ ?_⟩
    simpa [mul_assoc] using
      (baseChangeWordSeminorm_le_of_eq_sum Z d (fun j ↦ (hd j).symm) k v.toSmooth).trans
        (mul_le_mul_of_nonneg_left (hC v.toSmooth) (by positivity))

/-- **The Sobolev seminorms define the topology of the smooth vectors.** For a spanning family
`X`, the topology of `LieSmoothSpace I π X`, that of the word seminorms `P_k`, is the topology of
the Sobolev seminorms `Q_k`: the case `Z = 1 ⊗ X` of
`ContRepresentation.LieSmoothSpace.withSeminorms_baseChangeSobolevSeminormFamily`. -/
theorem withSeminorms_sobolevSeminormFamily {X : Fin m → LeftInvariantDerivation I G}
    (hX : Submodule.span ℝ (Set.range X) = ⊤) :
    WithSeminorms (sobolevSeminormFamily I π X) := by
  convert withSeminorms_baseChangeSobolevSeminormFamily (π := π) hX
    (span_one_tmul_eq_top (A := 𝕜) hX) using 1
  ext k v
  simp

end LieSmoothSpace

end ContRepresentation
