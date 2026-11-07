/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Hamiltonian.WeightModel.Basic
public import TauCeti.Geometry.Toric.Algebraic.Lattice

/-!
# Integral weights of the weight model

Let `α : ι → StrongDual ℝ 𝔱` be weights on the Lie algebra `𝔱` of a torus, acting on
`ℂ^ι = EuclideanSpace ℝ ι × EuclideanSpace ℝ ι` by `ξ • z = (exp(i α_j(ξ)) z_j)_j`
(`TauCeti.weightRotation`), with moment map `μ(z) = -½ Σ_j |z_j|² α_j`
(`TauCeti.weightMomentMap`). The orbits and fixed points of this local model are described in
`TauCeti.Geometry.Symplectic.Hamiltonian.WeightModel.Basic`; this file relates the model to the
period lattice of the torus.

**Integral weights.** Let `i : N →+ 𝔱` be an integral lattice (`TauCeti.Toric.IsIntegralLattice`),
so that `2π i(N)` is the period lattice of the torus `𝔱 / 2π i(N)`. The action of `𝔱` on `ℂ^ι`
descends to this torus exactly when every weight takes integer values on `i(N)`, that is, when
every weight is the real extension of an integral character of `N`.

**Weights forming a lattice basis.** Suppose finally that the weights are dual to a `ℤ`-basis `b`
of `N`: `α_j(i n)` is the `j`-th coordinate of `n` in `b`. This is the local model of a symplectic
toric manifold at a fixed point. Then:

* `μ(z)` paired with `i(b_k)` is `-½ |z_k|²`, and the image of `μ` is the simplicial cone
  `{ν | ν(i(b_k)) ≤ 0 for all k}`;
* the stabilizer of `z` in `𝔱` is `2π i(N) + span{i(b_k) | z_k = 0}`, the preimage of the subtorus
  spanned by the normals `i(b_k)` of the facets `ν(i(b_k)) = 0` containing `μ(z)`;
* the torus acts effectively, and it acts freely at `z` exactly when `μ(z)` lies in the open cone
  `{ν | ν(i(b_k)) < 0 for all k}`.

## Main results

* `TauCeti.forall_weightRotation_two_pi_smul_eq_id_iff`: the action descends to the torus
  `𝔱 / 2π i(N)` exactly when the weights are integral.
* `TauCeti.weightRotation_apply_eq_self_iff_of_basis`: stabilizers for weights dual to a lattice
  basis.
* `TauCeti.weightRotation_apply_eq_self_iff_of_basis_weightMomentMap`: the stabilizer of `z` is
  determined by the facets of the moment cone through `μ(z)`.
* `TauCeti.range_weightMomentMap_of_basis`: the image is the simplicial cone of the basis.
* `TauCeti.linearIndependent_of_forall_apply_eq_coord`: such weights are linearly independent, so
  the results of the basic weight model for independent weights apply to them.
* `TauCeti.weightRotation_eq_id_iff_of_basis`,
  `TauCeti.forall_weightRotation_apply_eq_self_imp_iff_of_basis`: the torus acts effectively, and
  freely exactly over the open cone.

## References

* Victor Guillemin and Shlomo Sternberg, *Convexity properties of the moment mapping*, Invent.
  Math. 67 (1982), Section 2.
* Thomas Delzant, *Hamiltoniens périodiques et images convexes de l'application moment*, Bull.
  Soc. Math. France 116 (1988), 315–339.
* Ana Cannas da Silva, *Lectures on Symplectic Geometry*, Lecture Notes in Math. 1764, Springer
  (2001), Sections 27–29.
-/

public section

noncomputable section

namespace TauCeti

open Real

variable {ι : Type*} [Fintype ι]
variable {𝔱 : Type*} [NormedAddCommGroup 𝔱] [NormedSpace ℝ 𝔱]

/-! ### Integral weights -/

section Integral

variable {N : Type*} [AddCommGroup N] {i : N →+ 𝔱}

/-- **Integral weights.** For an integral lattice `i : N →+ 𝔱`, the action of `𝔱` on `ℂ^ι`
descends to the torus `𝔱 / 2π i(N)`, that is, `2π i(n)` acts trivially for every `n : N`, exactly
when every weight is the real extension of an integral character of `N`. -/
theorem forall_weightRotation_two_pi_smul_eq_id_iff (h : Toric.IsIntegralLattice i)
    (α : ι → StrongDual ℝ 𝔱) :
    (∀ n, weightRotation (fun j ↦ α j ((2 * π) • i n)) = ContinuousLinearMap.id ℝ _) ↔
      ∀ j, ∃ m : N →+ ℤ, h.realCharacter m = (α j : 𝔱 →ₗ[ℝ] ℝ) := by
  simp only [h.exists_realCharacter_eq_iff, ContinuousLinearMap.coe_coe]
  constructor
  · intro hn j n
    refine (weightRotation_two_pi_smul_apply_eq_self_iff α (i n) (WithLp.toLp 2 fun _ ↦ 1, 0)).1
      ?_ j (Or.inl (by simp))
    rw [hn, ContinuousLinearMap.id_apply]
  · exact fun hα n ↦ ContinuousLinearMap.ext fun x ↦
      (weightRotation_two_pi_smul_apply_eq_self_iff α (i n) x).2 fun j _ ↦ hα j n

/-! ### Weights dual to a lattice basis -/

variable (h : Toric.IsIntegralLattice i) (b : Module.Basis ι ℤ N) {α : ι → StrongDual ℝ 𝔱}
  (hα : ∀ j n, α j (i n) = b.coord j n)
include hα

omit [Fintype ι] in
/-- The weight `α_j` dual to a lattice basis `b` pairs with `i(b_j)` to `1`. -/
private theorem apply_basis_self_of_basis (j : ι) : α j (i (b j)) = 1 := by
  rw [hα, Module.Basis.coord_apply, Module.Basis.repr_self, Finsupp.single_eq_same, Int.cast_one]

omit [Fintype ι] in
/-- The weight `α_j` dual to a lattice basis `b` vanishes on `i(b_k)` for `k ≠ j`. -/
private theorem apply_basis_of_basis_of_ne {j k : ι} (hjk : j ≠ k) : α j (i (b k)) = 0 := by
  rw [hα, Module.Basis.coord_apply, Module.Basis.repr_self, Finsupp.single_eq_of_ne hjk,
    Int.cast_zero]

/-- For weights dual to a lattice basis `b`, the moment image of `z` pairs with `i(b_k)` to
`-½ |z_k|²`. -/
theorem weightMomentMap_apply_basis (x : EuclideanSpace ℝ ι × EuclideanSpace ℝ ι) (k : ι) :
    weightMomentMap α x (i (b k)) = -(1 / 2) * (x.1 k ^ 2 + x.2 k ^ 2) := by
  rw [weightMomentMap_apply, Finset.sum_eq_single k
    (fun j _ hj ↦ by rw [apply_basis_of_basis_of_ne b hα hj, zero_mul]) (by simp),
    apply_basis_self_of_basis b hα, one_mul]

/-- For weights dual to a lattice basis `b`, the moment image of `z` lies on the facet
`ν(i(b_k)) = 0` of the moment cone exactly when the coordinate `z_k` vanishes. -/
theorem weightMomentMap_apply_basis_eq_zero_iff (x : EuclideanSpace ℝ ι × EuclideanSpace ℝ ι)
    (k : ι) : weightMomentMap α x (i (b k)) = 0 ↔ x.1 k = 0 ∧ x.2 k = 0 := by
  rw [weightMomentMap_apply_basis b hα]
  constructor
  · intro hk
    constructor <;> nlinarith [sq_nonneg (x.1 k), sq_nonneg (x.2 k)]
  · rintro ⟨h1, h2⟩
    simp [h1, h2]

include h in
/-- For weights dual to a lattice basis `b`, every `ξ ∈ 𝔱` expands in the real basis `i(b_k)`
with coefficients `α_k(ξ)`. -/
theorem sum_apply_smul_of_basis (ξ : 𝔱) : ∑ k, α k ξ • i (b k) = ξ := by
  let B := h.isBaseChange.basis b
  have hB (k : ι) : B k = i (b k) := by simpa using h.isBaseChange.basis_apply b k
  have hcoord (k : ι) : (α k : 𝔱 →ₗ[ℝ] ℝ) = B.coord k :=
    B.ext fun j ↦ by
      rw [ContinuousLinearMap.coe_coe, Module.Basis.coord_apply, Module.Basis.repr_self, hB]
      by_cases hkj : k = j
      · rw [hkj, apply_basis_self_of_basis b hα, Finsupp.single_eq_same]
      · rw [apply_basis_of_basis_of_ne b hα hkj, Finsupp.single_eq_of_ne hkj]
  conv_rhs => rw [← B.sum_repr ξ]
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  rw [← hB, ← B.coord_apply, ← hcoord, ContinuousLinearMap.coe_coe]

omit [Fintype ι] in
/-- Weights dual to a lattice basis are linearly independent. -/
theorem linearIndependent_of_forall_apply_eq_coord : LinearIndependent ℝ α :=
  .of_pairwise_dual_eq_zero_one α (fun k ↦ (ContinuousLinearMap.apply ℝ ℝ (i (b k))).toLinearMap)
    (fun _ _ hkj ↦ apply_basis_of_basis_of_ne b hα hkj.symm) (apply_basis_self_of_basis b hα)

include h in
/-- **Stabilizers for weights dual to a lattice basis.** The element `ξ ∈ 𝔱` fixes `z` exactly
when, modulo the period lattice `2π i(N)`, it lies in the span of the vectors `i(b_k)` for which
the coordinate `z_k` vanishes. -/
theorem weightRotation_apply_eq_self_iff_of_basis (ξ : 𝔱)
    (x : EuclideanSpace ℝ ι × EuclideanSpace ℝ ι) :
    weightRotation (fun j ↦ α j ξ) x = x ↔ ∃ n : N, ξ - (2 * π) • i n ∈
      Submodule.span ℝ ((fun k ↦ i (b k)) '' {k | x.1 k = 0 ∧ x.2 k = 0}) := by
  rw [weightRotation_apply_eq_self_iff]
  constructor
  · intro hfix
    choose! c hc using hfix
    -- Subtract `2π` times the lattice vector with coordinates `c` in the basis `b`.
    have hn (j : ι) : α j (i (b.equivFun.symm c)) = c j := by
      rw [hα, Module.Basis.coord_apply, ← Module.Basis.equivFun_apply,
        LinearEquiv.apply_symm_apply]
    refine ⟨b.equivFun.symm c, ?_⟩
    rw [← sum_apply_smul_of_basis h b hα (ξ - _)]
    refine Submodule.sum_mem _ fun k _ ↦ ?_
    by_cases hk : x.1 k = 0 ∧ x.2 k = 0
    · exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, hk, rfl⟩)
    · rw [map_sub, map_smul, hn, smul_eq_mul, ← hc k (by tauto)]
      simp [mul_comm]
  · rintro ⟨n, hξ⟩ j hj
    -- `α_j` kills the span, since it kills every `i(b_k)` with `k ≠ j`.
    have hker : Submodule.span ℝ ((fun k ↦ i (b k)) '' {k | x.1 k = 0 ∧ x.2 k = 0}) ≤
        LinearMap.ker (α j : 𝔱 →ₗ[ℝ] ℝ) := by
      rw [Submodule.span_le]
      rintro _ ⟨k, hk, rfl⟩
      have hjk : j ≠ k := by
        rintro rfl
        rcases hk with ⟨h1, h2⟩
        tauto
      simp [apply_basis_of_basis_of_ne b hα hjk]
    have h0 := hker hξ
    simp only [LinearMap.mem_ker, ContinuousLinearMap.coe_coe, map_sub,
      map_smul, hα, smul_eq_mul] at h0
    exact ⟨b.coord j n, by linear_combination -h0⟩

include h in
/-- For weights dual to a lattice basis, the stabilizer of `z` in `𝔱` depends only on the face of
the moment cone containing `μ(z)`: it is the period lattice `2π i(N)` plus the span of the
`i(b_k)` for the facets `ν(i(b_k)) = 0` through `μ(z)`. -/
theorem weightRotation_apply_eq_self_iff_of_basis_weightMomentMap (ξ : 𝔱)
    (x : EuclideanSpace ℝ ι × EuclideanSpace ℝ ι) :
    weightRotation (fun j ↦ α j ξ) x = x ↔ ∃ n : N, ξ - (2 * π) • i n ∈
      Submodule.span ℝ ((fun k ↦ i (b k)) '' {k | weightMomentMap α x (i (b k)) = 0}) := by
  simp only [weightMomentMap_apply_basis_eq_zero_iff b hα]
  exact weightRotation_apply_eq_self_iff_of_basis h b hα ξ x

include h in
/-- **The torus acts freely on the open orthant.** For weights dual to a lattice basis, at a point
of `ℂ^ι` all of whose coordinates are nonzero, the stabilizer in `𝔱` is the period lattice
`2π i(N)`. -/
theorem weightRotation_apply_eq_self_iff_of_basis_of_forall_ne_zero
    {x : EuclideanSpace ℝ ι × EuclideanSpace ℝ ι} (hx : ∀ k, x.1 k ≠ 0 ∨ x.2 k ≠ 0) (ξ : 𝔱) :
    weightRotation (fun j ↦ α j ξ) x = x ↔ ∃ n : N, ξ = (2 * π) • i n := by
  have hempty : {k | x.1 k = 0 ∧ x.2 k = 0} = ∅ :=
    Set.eq_empty_of_forall_notMem fun k ⟨h1, h2⟩ ↦ (hx k).elim (· h1) (· h2)
  simp only [weightRotation_apply_eq_self_iff_of_basis h b hα, hempty, Set.image_empty,
    Submodule.span_empty, Submodule.mem_bot, sub_eq_zero]

include h in
/-- **The torus acts effectively.** For weights dual to a lattice basis, `ξ ∈ 𝔱` acts trivially on
`ℂ^ι` exactly when it lies in the period lattice `2π i(N)`. -/
theorem weightRotation_eq_id_iff_of_basis (ξ : 𝔱) :
    weightRotation (fun j ↦ α j ξ) = ContinuousLinearMap.id ℝ _ ↔ ∃ n : N, ξ = (2 * π) • i n := by
  refine ⟨fun hid ↦ ?_, fun ⟨n, hn⟩ ↦ ContinuousLinearMap.ext fun x ↦
    (weightRotation_apply_eq_self_iff_of_basis h b hα ξ x).2 ⟨n, by simp [hn]⟩⟩
  refine (weightRotation_apply_eq_self_iff_of_basis_of_forall_ne_zero h b hα
    (x := (WithLp.toLp 2 fun _ ↦ 1, 0)) (fun k ↦ Or.inl (by simp)) ξ).1 ?_
  rw [hid, ContinuousLinearMap.id_apply]

include h in
/-- **The torus acts freely exactly over the open cone.** For weights dual to a lattice basis, the
stabilizer of `z` in `𝔱` is the period lattice `2π i(N)` exactly when `μ(z)` lies in the open cone
`{ν | ν(i(b_k)) < 0 for all k}`, that is, when every coordinate `z_k` is nonzero. -/
theorem forall_weightRotation_apply_eq_self_imp_iff_of_basis
    (x : EuclideanSpace ℝ ι × EuclideanSpace ℝ ι) :
    (∀ ξ, weightRotation (fun j ↦ α j ξ) x = x → ∃ n : N, ξ = (2 * π) • i n) ↔
      ∀ k, weightMomentMap α x (i (b k)) < 0 := by
  have hlt (k : ι) : weightMomentMap α x (i (b k)) < 0 ↔ x.1 k ≠ 0 ∨ x.2 k ≠ 0 := by
    rw [← not_and_or, ← weightMomentMap_apply_basis_eq_zero_iff b hα,
      weightMomentMap_apply_basis b hα]
    constructor
    · intro hk; linarith
    · intro hk; exact lt_of_le_of_ne (by nlinarith [sq_nonneg (x.1 k), sq_nonneg (x.2 k)]) hk
  simp only [hlt]
  refine ⟨fun hfree k ↦ ?_, fun hx ξ ↦
    (weightRotation_apply_eq_self_iff_of_basis_of_forall_ne_zero h b hα hx ξ).1⟩
  by_contra! hk
  -- The element `π i(b_k)` fixes `z`, but is not in the period lattice.
  have hmem : i (b k) ∈ Submodule.span ℝ ((fun k ↦ i (b k)) '' {k | x.1 k = 0 ∧ x.2 k = 0}) :=
    Submodule.subset_span ⟨k, hk, rfl⟩
  obtain ⟨n, hn⟩ := hfree (π • i (b k)) <|
    (weightRotation_apply_eq_self_iff_of_basis h b hα _ x).2
      ⟨0, by simpa using Submodule.smul_mem _ π hmem⟩
  have hk' := congrArg (α k) hn
  simp only [map_smul, apply_basis_self_of_basis b hα, smul_eq_mul, mul_one, hα] at hk'
  have h2 : (((2 * b.coord k n : ℤ)) : ℝ) = (1 : ℤ) :=
    mul_right_cancel₀ pi_ne_zero (by push_cast; linear_combination -hk')
  have := Int.cast_injective h2
  omega

include h in
/-- **The moment image is a simplicial cone.** For weights dual to a lattice basis `b`, the image
of the moment map is the cone `{ν | ν(i(b_k)) ≤ 0 for all k}` cut out by the facets
`ν(i(b_k)) = 0`. -/
theorem range_weightMomentMap_of_basis :
    Set.range (weightMomentMap α) = {ν | ∀ k, ν (i (b k)) ≤ 0} := by
  ext ν
  constructor
  · rintro ⟨x, rfl⟩ k
    rw [weightMomentMap_apply_basis b hα]
    nlinarith [sq_nonneg (x.1 k), sq_nonneg (x.2 k)]
  · intro hν
    refine ⟨(WithLp.toLp 2 fun k ↦ √(-2 * ν (i (b k))), 0), ?_⟩
    -- Both functionals agree on the real basis `i(b_k)` of `𝔱`.
    refine ContinuousLinearMap.ext fun ξ ↦ ?_
    rw [← sum_apply_smul_of_basis h b hα ξ, map_sum, map_sum]
    refine Finset.sum_congr rfl fun k _ ↦ ?_
    rw [map_smul, map_smul, weightMomentMap_apply_basis b hα]
    simp only [PiLp.zero_apply]
    rw [Real.sq_sqrt (by linarith [hν k])]
    ring

end Integral

end TauCeti
