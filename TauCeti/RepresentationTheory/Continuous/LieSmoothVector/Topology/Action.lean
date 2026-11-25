/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Continuous.LieSmoothVector.BasisChange
public import TauCeti.RepresentationTheory.Continuous.LieSmoothVector.Enveloping
public import TauCeti.RepresentationTheory.Continuous.LieSmoothVector.Topology

/-!
# Each group element acts continuously on the smooth vectors

Let `π` be a continuous representation of a real Lie group `G` on a normed space `V`, and let `X`
be a finite family of left-invariant derivations. By adjoint covariance
`π(g) dπ(Y) π(g)⁻¹ = dπ(Ad(g) Y)` (`ContRepresentation.lieSmoothVectorsDerivative_Ad`), the
operator of a word moves past `π(g)`: `dπ(X_w) π(g) = π(g) dπ((Ad(g⁻¹) X)_w)`. Hence, if
`‖π(g) v‖ ≤ C ‖v‖`, the word seminorms satisfy `P^X_k(π(g) v) ≤ C P^{Ad(g⁻¹) X}_k(v)`.

When `X` spans the Lie algebra, every `Ad(g⁻¹) X_j` is a real combination of the `X_i`, so
`P^{Ad(g⁻¹) X}_k` is bounded by a multiple of `P^X_k`
(`ContRepresentation.wordSeminorm_le_of_eq_sum`) and each `π(g)` is continuous on
`LieSmoothSpace I π X`. This makes the smooth vectors, with the topology of the word seminorms, a
continuous representation of `G` in the sense of `ContRepresentation` (each operator continuous).

## Main definitions

* `ContRepresentation.LieSmoothSpace.contRepresentation`: for a spanning family `X`, the action
  of `G` on `LieSmoothSpace I π X` by continuous linear maps.

## Main results

* `ContRepresentation.wordAction_mul_lieSmoothVectorsAction`:
  `dπ(X_w) π(g) = π(g) dπ((Ad(g⁻¹) X)_w)` on smooth vectors.
* `ContRepresentation.wordSeminorm_lieSmoothVectorsAction_le`:
  `P^X_k(π(g) v) ≤ C P^{Ad(g⁻¹) X}_k(v)` when `‖π(g) u‖ ≤ C ‖u‖` for all `u`.
* `ContRepresentation.LieSmoothSpace.continuous_lieSmoothVectorsAction`: for a spanning family,
  each `π(g)` is continuous for the topology of the word seminorms.

## References

* J. Bernstein, B. Krötz, *Smooth Fréchet globalizations of Harish-Chandra modules*,
  Israel J. Math. 199 (2014), §§2.1–2.4.
-/

public section

noncomputable section

open scoped ContDiff Manifold

namespace ContRepresentation

open TauCeti TauCeti.Lie

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G]
  [LieGroup I ∞ G] [T2Space G] [BoundarylessManifold I G]
  {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  {ι : Type*}

attribute [local instance] LieGroup.minSmoothness_of_isRCLikeNormedField

/-- **Words move past the group action.** On smooth vectors,
`dπ(X_w) π(g) = π(g) dπ((Ad(g⁻¹) X)_w)`. -/
theorem wordAction_mul_lieSmoothVectorsAction {R : Type*} [Ring R] [Module R V]
    [SMulCommClass ℝ R V] [ContinuousConstSMul R V] {π : ContRepresentation R G V} (g : G)
    (X : ι → LeftInvariantDerivation I G) (w : List ι) :
    wordAction I π X w * lieSmoothVectorsAction I π g =
      lieSmoothVectorsAction I π g * wordAction I π (fun i ↦ Ad (I := I) g⁻¹ (X i)) w := by
  have hinv : lieSmoothVectorsAction I π g * lieSmoothVectorsAction I π g⁻¹ = 1 := by
    rw [← map_mul, mul_inv_cancel, map_one]
  induction w with
  | nil => simp
  | cons i w ih =>
    rw [wordAction_cons, wordAction_cons, mul_assoc, ih, lieSmoothVectorsDerivative_Ad, inv_inv]
    simp only [mul_assoc, ← mul_assoc (lieSmoothVectorsAction I π g) _ _, hinv, one_mul]

variable {𝕜 : Type*} [NormedField 𝕜] [NormedSpace 𝕜 V] [SMulCommClass ℝ 𝕜 V]
  {π : ContRepresentation 𝕜 G V} [Fintype ι]

/-- **The word seminorms of a translate.** If `‖π(g) u‖ ≤ C ‖u‖` for every `u`, then
`P^X_k(π(g) v) ≤ C P^{Ad(g⁻¹) X}_k(v)`. -/
theorem wordSeminorm_lieSmoothVectorsAction_le (X : ι → LeftInvariantDerivation I G) (k : ℕ)
    (g : G) {C : ℝ} (hC : ∀ u : V, ‖π g u‖ ≤ C * ‖u‖) (v : lieSmoothVectors I π) :
    wordSeminorm I π X k (lieSmoothVectorsAction I π g v) ≤
      C * wordSeminorm I π (fun i ↦ Ad (I := I) g⁻¹ (X i)) k v := by
  rw [wordSeminorm_apply, wordSeminorm_apply, Finset.mul_sum]
  refine Finset.sum_le_sum fun w _ ↦ ?_
  rw [← mul_apply_eq_comp, wordAction_mul_lieSmoothVectorsAction, mul_apply_eq_comp,
    coe_lieSmoothVectorsAction_apply]
  exact hC _

namespace LieSmoothSpace

variable [NormedAlgebra ℝ 𝕜] [IsScalarTower ℝ 𝕜 V]

/-- **Each `π(g)` is continuous on the smooth vectors.** For a family `X` spanning the Lie
algebra, each `π(g)` is continuous for the topology of the word seminorms along `X`: if
`Ad(g⁻¹) X_j = ∑ i, c j i • X i` and `‖π(g) u‖ ≤ C ‖u‖`, then
`P^X_k(π(g) v) ≤ C (1 + ∑ j, ∑ i, |c j i|)^k P^X_k(v)`. -/
theorem continuous_lieSmoothVectorsAction {X : ι → LeftInvariantDerivation I G}
    (hX : Submodule.span ℝ (Set.range X) = ⊤) (g : G) :
    Continuous ((linearEquiv I π X).symm.toLinearMap ∘ₗ (lieSmoothVectorsAction I π g) ∘ₗ
      (linearEquiv I π X).toLinearMap) := by
  choose c hc using fun j ↦
    (Submodule.mem_span_range_iff_exists_fun ℝ).mp (hX ▸ Submodule.mem_top :
      Ad (I := I) g⁻¹ (X j) ∈ Submodule.span ℝ (Set.range X))
  let L : V →L[ℝ] V := (π g).restrictScalars ℝ
  refine WithSeminorms.continuous_of_isBounded (withSeminorms I π X) (withSeminorms I π X) _
    (Seminorm.IsBounded.of_real fun k ↦
      ⟨{k}, ‖L‖ * (1 + ∑ j, ∑ i, |c j i|) ^ k, fun v ↦ ?_⟩)
  simp only [Finset.sup_singleton, seminormFamily_apply, LinearMap.comp_apply,
    LinearEquiv.coe_coe, linearEquiv_apply, linearEquiv_symm_apply]
  refine (wordSeminorm_lieSmoothVectorsAction_le X k g
    (fun u ↦ by simpa only [L, ContinuousLinearMap.coe_restrictScalars'] using L.le_opNorm u)
    _).trans ?_
  rw [mul_assoc]
  exact mul_le_mul_of_nonneg_left
    (wordSeminorm_le_of_eq_sum X c (fun j ↦ (hc j).symm) k v.toSmooth) (norm_nonneg L)

variable (I π X) in
/-- **The smooth vectors are a continuous representation.** For a family `X` spanning the Lie
algebra, `G` acts on `LieSmoothSpace I π X` by continuous linear maps. -/
def contRepresentation (X : ι → LeftInvariantDerivation I G)
    (hX : Submodule.span ℝ (Set.range X) = ⊤) : ContRepresentation 𝕜 G (LieSmoothSpace I π X) :=
  .ofMonoidHom
    { toFun g := ⟨(linearEquiv I π X).symm.toLinearMap ∘ₗ (lieSmoothVectorsAction I π g) ∘ₗ
        (linearEquiv I π X).toLinearMap, continuous_lieSmoothVectorsAction hX g⟩
      map_one' := by ext v; simp [linearEquiv_symm_apply]
      map_mul' g h := by ext v; simp [linearEquiv_symm_apply] }

/-- The continuous action on `LieSmoothSpace I π X` is the action on smooth vectors. -/
@[simp]
theorem toSmooth_contRepresentation_apply (X : ι → LeftInvariantDerivation I G)
    (hX : Submodule.span ℝ (Set.range X) = ⊤) (g : G) (v : LieSmoothSpace I π X) :
    (contRepresentation I π X hX g v).toSmooth = lieSmoothVectorsAction I π g v.toSmooth := by
  simp [contRepresentation, ← toMonoidHom_apply, linearEquiv_symm_apply, linearEquiv_apply]

end LieSmoothSpace

end ContRepresentation
