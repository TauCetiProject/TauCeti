/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Continuous.LieSmoothVector.BaseChange
public import TauCeti.RepresentationTheory.Continuous.LieSmoothVector.Sobolev.Comparison

/-!
# Sobolev seminorms along a basis of the complexified Lie algebra

Let `π` be a continuous representation of a real Lie group `G` on a normed space `V` over a normed
field `𝕜` containing `ℝ` (for instance `𝕜 = ℂ`), and let `𝔤 = 𝕜 ⊗[ℝ] Lie(G)`. The derived action
extends `𝕜`-linearly to `𝔤` (`ContRepresentation.lieSmoothVectorsBaseChangeDerivedAction`). For a
family `Z₁, …, Z_m` of `𝔤`, this file defines the Sobolev seminorms
`Q^Z_k(v) = (∑_{|α| ≤ k} ‖dπ(Z^α) v‖²)^{1/2}` over the ordered monomials
`Z^α = Z₁^{α₁} ⋯ Z_m^{α_m}` (`ContRepresentation.baseChangeSobolevSeminorm`), as the Sobolev
seminorms `LinearMap.endSobolevSeminorm` along the operators `dπ(Z_j)`. For `Z = 1 ⊗ X` they are
the real Sobolev seminorms of `X` (`ContRepresentation.baseChangeSobolevSeminorm_one_tmul`).

They are comparable with the word seminorms `P^Z_k` of
`ContRepresentation.baseChangeWordSeminorm`: `Q^Z_k ≤ P^Z_k`
(`LinearMap.endSobolevSeminorm_le_endWordSeminorm`); and, for a family spanning `𝔤` over `𝕜`,
`P^Z_k ≤ C_k Q^Z_k` (`LinearMap.exists_endWordSeminorm_le_mul_endSobolevSeminorm`), because the
operators `dπ(Z_j)` come from the action
`ContRepresentation.lieSmoothVectorsBaseChangeEnvelopingAction` of `U(𝔤)`, in which every word of
length at most `k` is a `𝕜`-combination of ordered monomials of degree at most `k`
(`TauCeti.UniversalEnvelopingAlgebra.prod_map_mem_span_monomialWord`). So for a `𝕜`-spanning
family of `𝔤` the Sobolev seminorms `Q^Z_k` define the topology of the smooth vectors
(`ContRepresentation.LieSmoothSpace.withSeminorms_baseChangeSobolevSeminormFamily`, in
`TauCeti.RepresentationTheory.Continuous.LieSmoothVector.Sobolev.Topology`).

## Main definitions

* `ContRepresentation.baseChangeSobolevSeminorm`: the Sobolev seminorm `Q^Z_k`.

## Main results

* `ContRepresentation.baseChangeSobolevSeminorm_le_baseChangeWordSeminorm`: `Q^Z_k ≤ P^Z_k`.
* `ContRepresentation.exists_baseChangeWordSeminorm_le_mul_baseChangeSobolevSeminorm`:
  `P^Z_k ≤ C_k Q^Z_k` for a family spanning `𝕜 ⊗[ℝ] Lie(G)`.

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
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G]
  [LieGroup I ∞ G] [T2Space G] [BoundarylessManifold I G]
  {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  {𝕜 : Type*} [NormedField 𝕜] [NormedSpace 𝕜 V] [SMulCommClass ℝ 𝕜 V]
  [NormedAlgebra ℝ 𝕜] [IsScalarTower ℝ 𝕜 V]
  {π : ContRepresentation 𝕜 G V} {m : ℕ}

attribute [local instance] LieGroup.minSmoothness_of_isRCLikeNormedField

/-! ### The Sobolev seminorms -/

variable (I π) in
/-- The Sobolev seminorm `Q^Z_k(v) = (∑_{|α| ≤ k} ‖dπ(Z^α) v‖²)^{1/2}` on smooth vectors, along a
family `Z` of `𝕜 ⊗[ℝ] Lie(G)`, summed over the ordered monomials `Z^α = Z₁^{α₁} ⋯ Z_m^{α_m}`: the
Sobolev seminorm along the operators `dπ(Z_j)`. -/
def baseChangeSobolevSeminorm (Z : Fin m → 𝕜 ⊗[ℝ] LeftInvariantDerivation I G) (k : ℕ) :
    Seminorm 𝕜 (lieSmoothVectors I π) :=
  LinearMap.endSobolevSeminorm (lieSmoothVectors I π).subtype
    (fun j ↦ lieSmoothVectorsBaseChangeDerivedAction I π (Z j)) k

/-- The Sobolev seminorm along `Z` is the Sobolev seminorm along the operators `dπ(Z_j)`. -/
theorem baseChangeSobolevSeminorm_eq_endSobolevSeminorm
    (Z : Fin m → 𝕜 ⊗[ℝ] LeftInvariantDerivation I G) (k : ℕ) :
    baseChangeSobolevSeminorm I π Z k =
      LinearMap.endSobolevSeminorm (lieSmoothVectors I π).subtype
        (fun j ↦ lieSmoothVectorsBaseChangeDerivedAction I π (Z j)) k :=
  (rfl)

/-- The Sobolev seminorm along `Z` as an explicit square root of a sum of squares. -/
theorem baseChangeSobolevSeminorm_apply (Z : Fin m → 𝕜 ⊗[ℝ] LeftInvariantDerivation I G)
    (k : ℕ) (v : lieSmoothVectors I π) :
    baseChangeSobolevSeminorm I π Z k v =
      √(∑ α : SobolevIndex m k, ‖(((monomialWord α.exponent).map fun j ↦
        lieSmoothVectorsBaseChangeDerivedAction I π (Z j)).prod v : V)‖ ^ 2) :=
  LinearMap.endSobolevSeminorm_apply _ _ k v

/-- **The Sobolev seminorms of `1 ⊗ X` are the real Sobolev seminorms of `X`.** -/
@[simp]
theorem baseChangeSobolevSeminorm_one_tmul (X : Fin m → LeftInvariantDerivation I G) (k : ℕ) :
    baseChangeSobolevSeminorm I π (fun i ↦ (1 : 𝕜) ⊗ₜ X i) k = sobolevSeminorm I π X k := by
  simp [baseChangeSobolevSeminorm_eq_endSobolevSeminorm, sobolevSeminorm_eq_endSobolevSeminorm]

/-- **The Sobolev seminorm is bounded by the word seminorm**, `Q^Z_k ≤ P^Z_k`: every ordered
monomial is a word, and the `ℓ²` norm of a finite family is at most its `ℓ¹` norm. -/
theorem baseChangeSobolevSeminorm_le_baseChangeWordSeminorm
    (Z : Fin m → 𝕜 ⊗[ℝ] LeftInvariantDerivation I G) (k : ℕ) (v : lieSmoothVectors I π) :
    baseChangeSobolevSeminorm I π Z k v ≤ baseChangeWordSeminorm I π Z k v := by
  rw [baseChangeSobolevSeminorm_eq_endSobolevSeminorm, baseChangeWordSeminorm_eq_endWordSeminorm]
  exact LinearMap.endSobolevSeminorm_le_endWordSeminorm _ _ k v

/-- **The word seminorm is bounded by a multiple of the Sobolev seminorm** along a family `Z`
spanning `𝕜 ⊗[ℝ] Lie(G)` over `𝕜`: for every order `k` there is `C_k` with
`P^Z_k ≤ C_k Q^Z_k`. -/
theorem exists_baseChangeWordSeminorm_le_mul_baseChangeSobolevSeminorm
    (Z : Fin m → 𝕜 ⊗[ℝ] LeftInvariantDerivation I G) (hZ : Submodule.span 𝕜 (Set.range Z) = ⊤)
    (k : ℕ) :
    ∃ C : ℝ, ∀ v : lieSmoothVectors I π,
      baseChangeWordSeminorm I π Z k v ≤ C * baseChangeSobolevSeminorm I π Z k v := by
  simp only [baseChangeWordSeminorm_eq_endWordSeminorm,
    baseChangeSobolevSeminorm_eq_endSobolevSeminorm]
  refine LinearMap.exists_endWordSeminorm_le_mul_endSobolevSeminorm _ _ fun _ hw ↦ ?_
  simpa only [lieSmoothVectorsBaseChangeEnvelopingAction_ι] using
    UniversalEnvelopingAlgebra.prod_map_mem_span_monomialWord 𝕜
      (lieSmoothVectorsBaseChangeEnvelopingAction I π) Z hZ hw

end ContRepresentation
