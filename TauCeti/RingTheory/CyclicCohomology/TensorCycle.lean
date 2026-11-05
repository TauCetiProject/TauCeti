/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.DG.Algebra.TensorProduct
public import TauCeti.RingTheory.CyclicCohomology.Cycle
public import TauCeti.RingTheory.CyclicCohomology.Periodicity.Cochain
import TauCeti.Algebra.Ring.NegOnePow
import TauCeti.Data.Fin.Tuple.Basic

/-!
# Tensor products of cycles

Let `(Ω₁, d₁, ∫₁, ρ₁)` be a cycle of dimension `p` over an algebra `A` and `(Ω₂, d₂, ∫₂, ρ₂)` a
cycle of dimension `q` over an algebra `B`. Their tensor product is a cycle of dimension `p + q`
over `A ⊗ B`:

* the differential graded algebra is the Koszul-signed graded tensor product `Ω₁ ᵍ⊗ Ω₂`, with
  `(ω ⊗ η)(ω' ⊗ η') = (-1) ^ (|η| |ω'|) ωω' ⊗ ηη'` and
  `d (ω ⊗ η) = dω ⊗ η + (-1) ^ |ω| ω ⊗ dη` (`TauCeti.isDGAlgebra_gradedTensorGrading`);
* the trace is `ω ⊗ η ↦ ∫₁ ω ⊗ ∫₂ η` on forms of bidegree `(p, q)`, and zero in every other
  bidegree (`TauCeti.gradedTensorTrace`);
* the homomorphism is `a ⊗ b ↦ ρ₁(a) ⊗ ρ₂(b)` (`TauCeti.gradedTensorHomOfMemZero`, from
  `TauCeti.RingTheory.GradedAlgebra.TensorProduct`).

The graded trace property of the tensor trace combines those of the factors with the Koszul sign
of the product, and closedness follows from the graded Leibniz rule of the tensor differential.
The character of the tensor product cycle is therefore a cyclic cocycle on `A ⊗ B`, by
`TauCeti.cycleCocycle`; this is Connes' exterior product of cycles.

When the second cycle has dimension zero, its trace only sees products of zero-forms, and the
character of the tensor product is the character of the first cycle tensored with the trace of
the product of the second arguments:

`(a₀ ⊗ b₀, …, aₚ ⊗ bₚ) ↦ ∫₁ ρ₁(a₀) dρ₁(a₁) ⋯ dρ₁(aₚ) ⊗ ∫₂ ρ₂(b₀) ρ₂(b₁) ⋯ ρ₂(bₚ)`.

When the second cycle has dimension two and its arguments are fixed to an idempotent `e ∈ B`, the
relations `E² = E`, `E dE E = 0`, and `E (dE)² E = E (dE)²` on `E = ρ₂(e)` collapse the expansion of
`cycleForm` on `(a₀ ⊗ e, …, aₚ₊₂ ⊗ e)` modulo right degree `> 2` to three terms, whose bidegree
`(p, 2)` component applies `TauCeti.cochainPeriodicity` (`S₀`) to the character of the first cycle.

## Main definitions

* `TauCeti.gradedTensorTrace`: the tensor product of two traces of dimensions `p` and `q`.

## Main results

* `TauCeti.IsClosedGradedTrace.gradedTensor`: the tensor product of closed graded traces of
  dimensions `p` and `q` is a closed graded trace of dimension `p + q`.
* `TauCeti.cycleCharacter_gradedTensorHomOfMemZero_tmul_of_zero`: the character of a tensor
  product with a cycle of dimension zero.
* `TauCeti.cycleCharacter_gradedTensorHomOfMemZero_tmul_of_two`: the character of a tensor
  product with a cycle of dimension two evaluated along an idempotent in the second factor.

## References

* A. Connes, *Noncommutative Geometry*, Chapter III, §1, for cycles and their tensor products.
* A. Connes, *Noncommutative differential geometry*, Publ. Math. IHÉS 62 (1985), Part II, §1.
-/

public section

open scoped TensorProduct

namespace TauCeti

variable {R Ω₁ Ω₂ M N : Type*} [CommRing R] [Ring Ω₁] [Algebra R Ω₁] [Ring Ω₂] [Algebra R Ω₂]
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  {𝒜₁ : ℤ → Submodule R Ω₁} {𝒜₂ : ℤ → Submodule R Ω₂} [GradedAlgebra 𝒜₁] [GradedAlgebra 𝒜₂]

/-! ### The tensor product of two traces -/

section Trace

variable (𝒜₁ 𝒜₂) in
/-- The tensor product of a trace `τ₁` of dimension `p` and a trace `τ₂` of dimension `q`: it sends
`ω ⊗ η` to `τ₁ ω ⊗ τ₂ η` when `ω` has degree `p` and `η` has degree `q`, and vanishes on the other
bidegrees. -/
noncomputable def gradedTensorTrace (τ₁ : Ω₁ →ₗ[R] M) (τ₂ : Ω₂ →ₗ[R] N) (p q : ℕ) :
    (𝒜₁ ᵍ⊗[R] 𝒜₂) →ₗ[R] M ⊗[R] N :=
  TensorProduct.map (τ₁ ∘ₗ GradedAlgebra.proj 𝒜₁ p) (τ₂ ∘ₗ GradedAlgebra.proj 𝒜₂ q) ∘ₗ
    (GradedTensorProduct.of R 𝒜₁ 𝒜₂).symm.toLinearMap

variable {τ₁ : Ω₁ →ₗ[R] M} {τ₂ : Ω₂ →ₗ[R] N} {p q : ℕ}

/-- The tensor trace on a pure tensor applies each trace to the relevant homogeneous component. -/
@[simp]
theorem gradedTensorTrace_tmul (a : Ω₁) (b : Ω₂) :
    gradedTensorTrace 𝒜₁ 𝒜₂ τ₁ τ₂ p q (a ᵍ⊗ₜ[R] b) =
      τ₁ (GradedAlgebra.proj 𝒜₁ p a) ⊗ₜ τ₂ (GradedAlgebra.proj 𝒜₂ q b) := by
  simp [gradedTensorTrace, GradedTensorProduct.tmul]

/-- On a pure tensor of bidegree `(p, q)` the tensor trace is the tensor product of the traces. -/
theorem gradedTensorTrace_tmul_of_mem {a : Ω₁} {b : Ω₂} (ha : a ∈ 𝒜₁ p) (hb : b ∈ 𝒜₂ q) :
    gradedTensorTrace 𝒜₁ 𝒜₂ τ₁ τ₂ p q (a ᵍ⊗ₜ[R] b) = τ₁ a ⊗ₜ τ₂ b := by
  rw [gradedTensorTrace_tmul, GradedAlgebra.proj_apply, GradedAlgebra.proj_apply,
    DirectSum.decompose_of_mem_same 𝒜₁ ha, DirectSum.decompose_of_mem_same 𝒜₂ hb]

/-- The tensor trace vanishes on pure tensors of bidegree other than `(p, q)`. -/
theorem gradedTensorTrace_tmul_of_mem_of_ne {i j : ℤ} {a : Ω₁} {b : Ω₂} (ha : a ∈ 𝒜₁ i)
    (hb : b ∈ 𝒜₂ j) (h : i ≠ p ∨ j ≠ q) :
    gradedTensorTrace 𝒜₁ 𝒜₂ τ₁ τ₂ p q (a ᵍ⊗ₜ[R] b) = 0 := by
  rw [gradedTensorTrace_tmul, GradedAlgebra.proj_apply, GradedAlgebra.proj_apply]
  rcases h with h | h
  · rw [DirectSum.decompose_of_mem_ne 𝒜₁ ha h, map_zero, TensorProduct.zero_tmul]
  · rw [DirectSum.decompose_of_mem_ne 𝒜₂ hb h, map_zero, TensorProduct.tmul_zero]

/-- The tensor trace is additive in the first trace. -/
@[simp]
theorem gradedTensorTrace_add_left (τ₁ τ₁' : Ω₁ →ₗ[R] M) (τ₂ : Ω₂ →ₗ[R] N) :
    gradedTensorTrace 𝒜₁ 𝒜₂ (τ₁ + τ₁') τ₂ p q =
      gradedTensorTrace 𝒜₁ 𝒜₂ τ₁ τ₂ p q + gradedTensorTrace 𝒜₁ 𝒜₂ τ₁' τ₂ p q := by
  simp only [gradedTensorTrace, LinearMap.add_comp, TensorProduct.map_add_left]

/-- The tensor trace is additive in the second trace. -/
@[simp]
theorem gradedTensorTrace_add_right (τ₁ : Ω₁ →ₗ[R] M) (τ₂ τ₂' : Ω₂ →ₗ[R] N) :
    gradedTensorTrace 𝒜₁ 𝒜₂ τ₁ (τ₂ + τ₂') p q =
      gradedTensorTrace 𝒜₁ 𝒜₂ τ₁ τ₂ p q + gradedTensorTrace 𝒜₁ 𝒜₂ τ₁ τ₂' p q := by
  simp only [gradedTensorTrace, LinearMap.add_comp, TensorProduct.map_add_right]

/-- The tensor trace is homogeneous in the first trace. -/
@[simp]
theorem gradedTensorTrace_smul_left (c : R) (τ₁ : Ω₁ →ₗ[R] M) (τ₂ : Ω₂ →ₗ[R] N) :
    gradedTensorTrace 𝒜₁ 𝒜₂ (c • τ₁) τ₂ p q = c • gradedTensorTrace 𝒜₁ 𝒜₂ τ₁ τ₂ p q := by
  simp only [gradedTensorTrace, LinearMap.smul_comp, TensorProduct.map_smul_left]

/-- The tensor trace is homogeneous in the second trace. -/
@[simp]
theorem gradedTensorTrace_smul_right (c : R) (τ₁ : Ω₁ →ₗ[R] M) (τ₂ : Ω₂ →ₗ[R] N) :
    gradedTensorTrace 𝒜₁ 𝒜₂ τ₁ (c • τ₂) p q = c • gradedTensorTrace 𝒜₁ 𝒜₂ τ₁ τ₂ p q := by
  simp only [gradedTensorTrace, LinearMap.smul_comp, TensorProduct.map_smul_right]

variable {d₁ : Ω₁ →ₗ[R] Ω₁} {d₂ : Ω₂ →ₗ[R] Ω₂}

/-- The graded trace property of the tensor trace on two pure tensors of homogeneous elements, of
total degrees `m` and `m'`. -/
private theorem gradedTensorTrace_mul_comm_tmul (h₁ : IsClosedGradedTrace 𝒜₁ d₁ p τ₁)
    (h₂ : IsClosedGradedTrace 𝒜₂ d₂ q τ₂) {i i' m m' : ℤ} {a a' : Ω₁} {b b' : Ω₂}
    (ha : a ∈ 𝒜₁ i) (hb : b ∈ 𝒜₂ (m - i)) (ha' : a' ∈ 𝒜₁ i') (hb' : b' ∈ 𝒜₂ (m' - i')) :
    gradedTensorTrace 𝒜₁ 𝒜₂ τ₁ τ₂ p q ((a ᵍ⊗ₜ[R] b) * (a' ᵍ⊗ₜ[R] b')) =
      (m * m').negOnePow •
        gradedTensorTrace 𝒜₁ 𝒜₂ τ₁ τ₂ p q ((a' ᵍ⊗ₜ[R] b') * (a ᵍ⊗ₜ[R] b)) := by
  rw [GradedTensorProduct.tmul_coe_mul_coe_tmul 𝒜₁ 𝒜₂ a ⟨b, hb⟩ ⟨a', ha'⟩ b',
    GradedTensorProduct.tmul_coe_mul_coe_tmul 𝒜₁ 𝒜₂ a' ⟨b', hb'⟩ ⟨a, ha⟩ b, map_zsmul_unit,
    map_zsmul_unit]
  have hl₁ := SetLike.mul_mem_graded ha ha'
  have hl₂ := SetLike.mul_mem_graded hb hb'
  have hr₁ := SetLike.mul_mem_graded ha' ha
  have hr₂ := SetLike.mul_mem_graded hb' hb
  by_cases hpq : i + i' = p ∧ m - i + (m' - i') = q
  · obtain ⟨hp, hq⟩ := hpq
    rw [hp] at hl₁
    rw [hq] at hl₂
    rw [add_comm, hp] at hr₁
    rw [add_comm, hq] at hr₂
    rw [gradedTensorTrace_tmul_of_mem hl₁ hl₂, gradedTensorTrace_tmul_of_mem hr₁ hr₂,
      h₁.map_mul_comm ha ha' hp, h₂.map_mul_comm hb hb' hq]
    simp only [← Int.negOnePow_def, negOnePow_smul_eq_negOnePowCast_smul (R := R),
      ← TensorProduct.smul_tmul', TensorProduct.tmul_smul, smul_smul]
    have hs : negOnePowCast R ((m - i) * i') *
        (negOnePowCast R ((m - i) * (m' - i')) * negOnePowCast R (i * i')) =
          negOnePowCast R (m * m') * negOnePowCast R ((m' - i') * i) := by
      simp only [negOnePowCast_eq_intCast, ← Int.cast_mul, ← Units.val_mul, ← Int.negOnePow_add]
      congr 2
      rw [Int.negOnePow_eq_iff]
      exact ⟨i * i' - i * m', by ring⟩
    rw [hs]
  · rcases not_and_or.1 hpq with h | h
    · rw [gradedTensorTrace_tmul_of_mem_of_ne hl₁ hl₂ (Or.inl h),
        gradedTensorTrace_tmul_of_mem_of_ne hr₁ hr₂ (Or.inl (by rwa [add_comm])), smul_zero,
        smul_zero, smul_zero]
    · rw [gradedTensorTrace_tmul_of_mem_of_ne hl₁ hl₂ (Or.inr h),
        gradedTensorTrace_tmul_of_mem_of_ne hr₁ hr₂ (Or.inr (by rwa [add_comm])), smul_zero,
        smul_zero, smul_zero]

/-- The closedness of the tensor trace on a pure tensor of homogeneous elements. -/
private theorem gradedTensorTrace_dgTensorDifferential_tmul (hd₁ : IsDGAlgebra 𝒜₁ d₁)
    (hd₂ : IsDGAlgebra 𝒜₂ d₂) (h₁ : IsClosedGradedTrace 𝒜₁ d₁ p τ₁)
    (h₂ : IsClosedGradedTrace 𝒜₂ d₂ q τ₂) {i : ℤ} {a : Ω₁} {b : Ω₂} (ha : a ∈ 𝒜₁ i)
    (hb : b ∈ 𝒜₂ ((p + q : ℕ) - 1 - i)) :
    gradedTensorTrace 𝒜₁ 𝒜₂ τ₁ τ₂ p q (dgTensorDifferential 𝒜₁ 𝒜₂ d₁ d₂ (a ᵍ⊗ₜ[R] b)) = 0 := by
  rw [dgTensorDifferential_tmul_of_mem ha, map_add, map_zsmul_unit]
  have h_left : gradedTensorTrace 𝒜₁ 𝒜₂ τ₁ τ₂ p q (d₁ a ᵍ⊗ₜ[R] b) = 0 := by
    by_cases hi : i + 1 = p
    · rw [gradedTensorTrace_tmul, GradedAlgebra.proj_apply,
        DirectSum.decompose_of_mem_same 𝒜₁ (hi ▸ hd₁.map_mem ha),
        h₁.map_map_eq_zero (by rwa [← hi, add_sub_cancel_right]), TensorProduct.zero_tmul]
    · exact gradedTensorTrace_tmul_of_mem_of_ne (hd₁.map_mem ha) hb (Or.inl hi)
  have h_right : gradedTensorTrace 𝒜₁ 𝒜₂ τ₁ τ₂ p q (a ᵍ⊗ₜ[R] d₂ b) = 0 := by
    by_cases hi : i = p
    · subst hi
      have hb' : b ∈ 𝒜₂ (q - 1) := by convert hb using 2; push_cast; ring
      rw [gradedTensorTrace_tmul, GradedAlgebra.proj_apply (𝒜 := 𝒜₂),
        DirectSum.decompose_of_mem_same 𝒜₂
          (by simpa only [sub_add_cancel] using hd₂.map_mem hb'),
        h₂.map_map_eq_zero hb', TensorProduct.tmul_zero]
    · exact gradedTensorTrace_tmul_of_mem_of_ne ha (hd₂.map_mem hb) (Or.inl hi)
  rw [h_left, h_right, smul_zero, add_zero]

/-- **The tensor product of closed graded traces is a closed graded trace**: if `τ₁` and `τ₂` are
closed graded traces of dimensions `p` and `q` on differential graded algebras, then their tensor
product is a closed graded trace of dimension `p + q` on the graded tensor product. -/
theorem IsClosedGradedTrace.gradedTensor (hd₁ : IsDGAlgebra 𝒜₁ d₁) (hd₂ : IsDGAlgebra 𝒜₂ d₂)
    (h₁ : IsClosedGradedTrace 𝒜₁ d₁ p τ₁) (h₂ : IsClosedGradedTrace 𝒜₂ d₂ q τ₂) :
    IsClosedGradedTrace (gradedTensorGrading 𝒜₁ 𝒜₂) (dgTensorDifferential 𝒜₁ 𝒜₂ d₁ d₂) (p + q)
      (gradedTensorTrace 𝒜₁ 𝒜₂ τ₁ τ₂ p q) where
  map_map_eq_zero {x} hx := by
    refine gradedTensorGrading_le 𝒜₁ 𝒜₂ (C := LinearMap.ker
      (gradedTensorTrace 𝒜₁ 𝒜₂ τ₁ τ₂ p q ∘ₗ dgTensorDifferential 𝒜₁ 𝒜₂ d₁ d₂))
      (fun i a ha b hb ↦ ?_) hx
    rw [LinearMap.mem_ker, LinearMap.comp_apply]
    exact gradedTensorTrace_dgTensorDifferential_tmul hd₁ hd₂ h₁ h₂ ha hb
  map_mul_comm {m m' x y} hx hy _ := by
    -- Reduce first the right factor, then the left factor, to homogeneous pure tensors.
    have hpure : ∀ i, ∀ a ∈ 𝒜₁ i, ∀ b ∈ 𝒜₂ (m - i),
        gradedTensorTrace 𝒜₁ 𝒜₂ τ₁ τ₂ p q ((a ᵍ⊗ₜ[R] b) * y) =
          negOnePowCast R (m * m') • gradedTensorTrace 𝒜₁ 𝒜₂ τ₁ τ₂ p q (y * (a ᵍ⊗ₜ[R] b)) := by
      intro i a ha b hb
      have h := gradedTensorGrading_le 𝒜₁ 𝒜₂ (C := LinearMap.ker
        (gradedTensorTrace 𝒜₁ 𝒜₂ τ₁ τ₂ p q ∘ₗ GradedTensorProduct.mulHom 𝒜₁ 𝒜₂ (a ᵍ⊗ₜ[R] b) -
          negOnePowCast R (m * m') • (gradedTensorTrace 𝒜₁ 𝒜₂ τ₁ τ₂ p q ∘ₗ
            (GradedTensorProduct.mulHom 𝒜₁ 𝒜₂).flip (a ᵍ⊗ₜ[R] b))))
        (fun i' a' ha' b' hb' ↦ by
          simp only [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.comp_apply,
            LinearMap.smul_apply, LinearMap.flip_apply, ← GradedTensorProduct.mul_def,
            sub_eq_zero]
          rw [← negOnePow_smul_eq_negOnePowCast_smul]
          exact gradedTensorTrace_mul_comm_tmul h₁ h₂ ha hb ha' hb') hy
      simpa only [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.comp_apply,
        LinearMap.smul_apply, LinearMap.flip_apply, ← GradedTensorProduct.mul_def,
        sub_eq_zero] using h
    have h := gradedTensorGrading_le 𝒜₁ 𝒜₂ (C := LinearMap.ker
      (gradedTensorTrace 𝒜₁ 𝒜₂ τ₁ τ₂ p q ∘ₗ (GradedTensorProduct.mulHom 𝒜₁ 𝒜₂).flip y -
        negOnePowCast R (m * m') •
          (gradedTensorTrace 𝒜₁ 𝒜₂ τ₁ τ₂ p q ∘ₗ GradedTensorProduct.mulHom 𝒜₁ 𝒜₂ y)))
      (fun i a ha b hb ↦ by
        simpa only [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.comp_apply,
          LinearMap.smul_apply, LinearMap.flip_apply, ← GradedTensorProduct.mul_def,
          sub_eq_zero] using hpure i a ha b hb) hx
    simp only [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.comp_apply,
      LinearMap.smul_apply, LinearMap.flip_apply, ← GradedTensorProduct.mul_def,
      sub_eq_zero] at h
    rw [h, negOnePow_smul_eq_negOnePowCast_smul (R := R)]

end Trace

/-! ### Tensoring with cycles of dimensions zero and two -/

section LowDimensionRight

variable {A B : Type*} [NonUnitalSemiring A] [Module R A] [SMulCommClass R A A]
  [IsScalarTower R A A] [NonUnitalSemiring B] [Module R B] [SMulCommClass R B B]
  [IsScalarTower R B B]
  {ρ₁ : A →ₙₐ[R] Ω₁} {ρ₂ : B →ₙₐ[R] Ω₂} {hρ₁ : ∀ a, ρ₁ a ∈ 𝒜₁ 0} {hρ₂ : ∀ b, ρ₂ b ∈ 𝒜₂ 0}
  {d₁ : Ω₁ →ₗ[R] Ω₁} {d₂ : Ω₂ →ₗ[R] Ω₂}

variable (𝒜₁ 𝒜₂) in
/-- The span of the pure tensors whose right factor is homogeneous of degree strictly above `k`. -/
private noncomputable def rightDegreeGt (k : ℤ) : Submodule R (𝒜₁ ᵍ⊗[R] 𝒜₂) :=
  Submodule.span R {x | ∃ j : ℤ, k < j ∧ ∃ (u : Ω₁) (v : Ω₂), v ∈ 𝒜₂ j ∧ x = u ᵍ⊗ₜ[R] v}

private theorem tmul_mem_rightDegreeGt {k j : ℤ} (hj : k < j) (u : Ω₁) {v : Ω₂} (hv : v ∈ 𝒜₂ j) :
    u ᵍ⊗ₜ[R] v ∈ rightDegreeGt 𝒜₁ 𝒜₂ k :=
  Submodule.subset_span ⟨j, hj, u, v, hv, rfl⟩

/-- Multiplying on the right by a homogeneous pure tensor of nonnegative right degree preserves
the span of pure tensors of right degree strictly above `k`. -/
private theorem mul_tmul_mem_rightDegreeGt {k : ℤ} {z : 𝒜₁ ᵍ⊗[R] 𝒜₂}
    (hz : z ∈ rightDegreeGt 𝒜₁ 𝒜₂ k) {i j : ℤ} {u : Ω₁} {v : Ω₂} (hu : u ∈ 𝒜₁ i) (hv : v ∈ 𝒜₂ j)
    (hj : 0 ≤ j) : z * (u ᵍ⊗ₜ[R] v) ∈ rightDegreeGt 𝒜₁ 𝒜₂ k := by
  have h : rightDegreeGt 𝒜₁ 𝒜₂ k ≤ (rightDegreeGt 𝒜₁ 𝒜₂ k).comap
      ((GradedTensorProduct.mulHom 𝒜₁ 𝒜₂).flip (u ᵍ⊗ₜ[R] v)) := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨j', hj', u', v', hv', rfl⟩
    rw [SetLike.mem_coe, Submodule.mem_comap, LinearMap.flip_apply,
      ← GradedTensorProduct.mul_def,
      GradedTensorProduct.tmul_coe_mul_coe_tmul 𝒜₁ 𝒜₂ u' ⟨v', hv'⟩ ⟨u, hu⟩ v, Units.smul_def]
    exact zsmul_mem (tmul_mem_rightDegreeGt (by omega) _ (SetLike.mul_mem_graded hv' hv)) _
  simpa only [Submodule.mem_comap, LinearMap.flip_apply, ← GradedTensorProduct.mul_def] using h hz

private theorem rightDegreeGt_le_ker_gradedTensorTrace {τ₁ : Ω₁ →ₗ[R] M} {τ₂ : Ω₂ →ₗ[R] N}
    (p q : ℕ) :
    rightDegreeGt 𝒜₁ 𝒜₂ q ≤ LinearMap.ker (gradedTensorTrace 𝒜₁ 𝒜₂ τ₁ τ₂ p q) := by
  refine Submodule.span_le.2 ?_
  rintro _ ⟨j, hj, u, v, hv, rfl⟩
  rw [SetLike.mem_coe, LinearMap.mem_ker, gradedTensorTrace_tmul, GradedAlgebra.proj_apply
    (𝒜 := 𝒜₂), DirectSum.decompose_of_mem_ne 𝒜₂ hv hj.ne', map_zero, TensorProduct.tmul_zero]

omit [GradedAlgebra 𝒜₁] [SMulCommClass R B B] [IsScalarTower R B B] in
/-- A product of zero-forms `ρ₂(b₁) ⋯ ρ₂(bₖ)` has degree zero. -/
private theorem prod_ofFn_mem_zero (hρ₂ : ∀ b, ρ₂ b ∈ 𝒜₂ 0) {k : ℕ} (b : Fin k → B) :
    (List.ofFn fun i ↦ ρ₂ (b i)).prod ∈ 𝒜₂ 0 := by
  have h := SetLike.list_prod_ofFn_mem_graded (fun _ : Fin k ↦ (0 : ℤ)) (fun i ↦ ρ₂ (b i))
    fun i ↦ hρ₂ (b i)
  rwa [show (List.ofFn fun _ : Fin k ↦ (0 : ℤ)).sum = 0 by simp] at h

/-- The form `ρ(x₀) dρ(x₁) ⋯ dρ(xₙ)` of a tensor product cycle on pure tensors `xᵢ = aᵢ ⊗ bᵢ` is
`ρ₁(a₀) dρ₁(a₁) ⋯ dρ₁(aₙ) ⊗ ρ₂(b₀) ⋯ ρ₂(bₙ)`, up to pure tensors of positive right degree. -/
private theorem cycleForm_gradedTensorHomOfMemZero_sub_mem (hd₁ : IsDGAlgebra 𝒜₁ d₁)
    (hd₂ : IsDGAlgebra 𝒜₂ d₂) {n : ℕ} (a : Fin (n + 1) → A) (b : Fin (n + 1) → B) :
    cycleForm (dgTensorDifferential 𝒜₁ 𝒜₂ d₁ d₂) (gradedTensorHomOfMemZero ρ₁ ρ₂ hρ₁ hρ₂) n
        (fun i ↦ a i ⊗ₜ b i) -
      cycleForm d₁ ρ₁ n a ᵍ⊗ₜ[R] (List.ofFn fun i ↦ ρ₂ (b i)).prod ∈ rightDegreeGt 𝒜₁ 𝒜₂ 0 := by
  induction n with
  | zero => simp [zero_mem]
  | succ n ih =>
    set c := a (Fin.last (n + 1))
    set e := b (Fin.last (n + 1))
    have hP := prod_ofFn_mem_zero hρ₂ (Fin.init b)
    rw [cycleForm_succ_apply, cycleForm_succ_apply]
    have hinit : Fin.init (fun i ↦ a i ⊗ₜ[R] b i) = fun i ↦ Fin.init a i ⊗ₜ[R] Fin.init b i :=
      rfl
    rw [hinit, gradedTensorHomOfMemZero_tmul, dgTensorDifferential_tmul_of_mem (hρ₁ c),
      Int.negOnePow_zero, one_smul]
    set X := cycleForm (dgTensorDifferential 𝒜₁ 𝒜₂ d₁ d₂)
      (gradedTensorHomOfMemZero ρ₁ ρ₂ hρ₁ hρ₂) n fun i ↦ Fin.init a i ⊗ₜ[R] Fin.init b i
    set ω := cycleForm d₁ ρ₁ n (Fin.init a)
    set P := (List.ofFn fun i ↦ ρ₂ (Fin.init b i)).prod
    have hprod : (List.ofFn fun i ↦ ρ₂ (b i)).prod = P * ρ₂ e := by
      rw [List.ofFn_succ', List.concat_eq_append, List.prod_append, List.prod_singleton]
      rfl
    -- The main term `(ω ⊗ P)(dρ₁(c) ⊗ ρ₂(e))` is the next form tensored with the next product.
    have hmain : (ω ᵍ⊗ₜ[R] P) * (d₁ (ρ₁ c) ᵍ⊗ₜ[R] ρ₂ e) = (ω * d₁ (ρ₁ c)) ᵍ⊗ₜ[R] (P * ρ₂ e) :=
      GradedTensorProduct.tmul_zero_coe_mul_coe_tmul 𝒜₁ 𝒜₂ ω ⟨P, hP⟩
        ⟨d₁ (ρ₁ c), hd₁.map_mem (hρ₁ c)⟩ (ρ₂ e)
    -- The other term `(ω ⊗ P)(ρ₁(c) ⊗ dρ₂(e))` has right factor of degree one.
    have hside : (ω ᵍ⊗ₜ[R] P) * (ρ₁ c ᵍ⊗ₜ[R] d₂ (ρ₂ e)) ∈ rightDegreeGt 𝒜₁ 𝒜₂ 0 := by
      rw [GradedTensorProduct.tmul_zero_coe_mul_coe_tmul 𝒜₁ 𝒜₂ ω ⟨P, hP⟩ ⟨ρ₁ c, hρ₁ c⟩]
      exact tmul_mem_rightDegreeGt (by omega) _ (SetLike.mul_mem_graded hP (hd₂.map_mem (hρ₂ e)))
    have hrest := mul_tmul_mem_rightDegreeGt (ih (Fin.init a) (Fin.init b))
      (hd₁.map_mem (hρ₁ c)) (hρ₂ e) le_rfl
    have hrest' := mul_tmul_mem_rightDegreeGt (ih (Fin.init a) (Fin.init b))
      (hρ₁ c) (hd₂.map_mem (hρ₂ e)) zero_le_one
    rw [hprod]
    have key : X * (d₁ (ρ₁ c) ᵍ⊗ₜ[R] ρ₂ e + ρ₁ c ᵍ⊗ₜ[R] d₂ (ρ₂ e)) -
        (ω * d₁ (ρ₁ c)) ᵍ⊗ₜ[R] (P * ρ₂ e) =
          (X - ω ᵍ⊗ₜ[R] P) * (d₁ (ρ₁ c) ᵍ⊗ₜ[R] ρ₂ e) +
            (X - ω ᵍ⊗ₜ[R] P) * (ρ₁ c ᵍ⊗ₜ[R] d₂ (ρ₂ e)) +
            (ω ᵍ⊗ₜ[R] P) * (ρ₁ c ᵍ⊗ₜ[R] d₂ (ρ₂ e)) := by
      rw [← hmain]
      simp only [mul_add, sub_mul]
      abel
    rw [key]
    exact add_mem (add_mem hrest hrest') hside

variable {τ₁ : Ω₁ →ₗ[R] M} {τ₂ : Ω₂ →ₗ[R] N}

/-- **The character of a tensor product with a cycle of dimension zero**: on pure tensors
`aᵢ ⊗ bᵢ` it is `∫₁ ρ₁(a₀) dρ₁(a₁) ⋯ dρ₁(aₚ) ⊗ ∫₂ ρ₂(b₀) ⋯ ρ₂(bₚ)`. -/
theorem cycleCharacter_gradedTensorHomOfMemZero_tmul_of_zero (hd₁ : IsDGAlgebra 𝒜₁ d₁)
    (hd₂ : IsDGAlgebra 𝒜₂ d₂) {p : ℕ} (a : Fin (p + 1) → A) (b : Fin (p + 1) → B) :
    cycleCharacter (dgTensorDifferential 𝒜₁ 𝒜₂ d₁ d₂) (gradedTensorTrace 𝒜₁ 𝒜₂ τ₁ τ₂ p 0)
        (gradedTensorHomOfMemZero ρ₁ ρ₂ hρ₁ hρ₂) p (fun i ↦ a i ⊗ₜ b i) =
      cycleCharacter d₁ τ₁ ρ₁ p a ⊗ₜ τ₂ (List.ofFn fun i ↦ ρ₂ (b i)).prod := by
  have h := rightDegreeGt_le_ker_gradedTensorTrace (τ₁ := τ₁) (τ₂ := τ₂) p 0
    (cycleForm_gradedTensorHomOfMemZero_sub_mem (ρ₁ := ρ₁) (ρ₂ := ρ₂) (hρ₁ := hρ₁)
      (hρ₂ := hρ₂) hd₁ hd₂ a b)
  rw [LinearMap.mem_ker, map_sub, sub_eq_zero] at h
  rw [cycleCharacter_apply, h, cycleCharacter_apply, gradedTensorTrace_tmul_of_mem
    (cycleForm_mem hd₁ hρ₁ a) (prod_ofFn_mem_zero hρ₂ b)]

omit [GradedAlgebra 𝒜₂] [SMulCommClass R B B] [IsScalarTower R B B] in
/-- Recursive expansion of `cochainPeriodicity` applied to `cycleForm` when shifting degree by one:
the terms `j ≤ n` factor out `* d₁(ρ₁(aₙ₊₃))` on the right, while the top term `j = n + 1` is the
signed bar coboundary of `cycleForm` at the `(n + 2)`-nd Hochschild face. -/
private theorem cochainPeriodicity_cycleForm_succ (hd₁ : IsDGAlgebra 𝒜₁ d₁)
    (hρ₁ : ∀ a, ρ₁ a ∈ 𝒜₁ 0) {n : ℕ} (a : Fin (n + 4) → A) :
    cochainPeriodicity R A Ω₁ (n + 1) (cycleForm d₁ ρ₁ (n + 1)) a =
      cochainPeriodicity R A Ω₁ n (cycleForm d₁ ρ₁ n) (Fin.init a) *
          d₁ (ρ₁ (a (Fin.last (n + 3)))) +
        cycleForm d₁ ρ₁ (n + 1) (Fin.init (Fin.init a)) *
          ρ₁ (a (Fin.last (n + 2)).castSucc * a (Fin.last (n + 3))) := by
  rw [cochainPeriodicity_apply, Fin.sum_univ_castSucc]
  refine congrArg₂ (· + ·) ?_ ?_
  · rw [cochainPeriodicity_apply, Finset.sum_mul]
    refine Finset.sum_congr rfl fun j₀ _ ↦ ?_
    rw [Fin.sum_Iic_castSucc, Finset.sum_mul]
    refine Finset.sum_congr rfl fun r₀ _ ↦ ?_
    rw [Fin.val_castSucc, Fin.val_castSucc, smul_mul_assoc]
    congr 1
    conv_lhs =>
      rw [Fin.succ_castSucc, hochschildFace_castSucc, hochschildFace_castSucc,
        cycleForm_succ_apply, Fin.init_contractNth_castSucc, Fin.init_contractNth_castSucc,
        Fin.contractNth_castSucc_castSucc_apply_last,
        Fin.contractNth_castSucc_castSucc_apply_last, ← hochschildFace_castSucc,
        ← hochschildFace_castSucc]
  · have hIic : Finset.Iic (Fin.last (n + 1)) = Finset.univ :=
      Finset.ext fun r ↦ by simp [Fin.le_last]
    rw [hIic, Fin.succ_last]
    set w := hochschildFace (Fin.last (n + 2)).castSucc a
    have hpow (r : Fin (n + 2)) :
        (-1 : ℤ) ^ ((Fin.last (n + 1) : ℕ) - r) = (-1 : ℤ) ^ (n + 1) * (-1 : ℤ) ^ (r : ℕ) := by
      have hr : (r : ℕ) ≤ n + 1 := Nat.le_of_lt_succ r.2
      have hrr : (-1 : ℤ) ^ ((r : ℕ) + r) = 1 := Even.neg_one_pow ⟨r, by omega⟩
      rw [Fin.val_last, show (-1 : ℤ) ^ (n + 1) = (-1 : ℤ) ^ (n + 1 - (r : ℕ) + r) by
        congr 1; omega, pow_add, mul_assoc, ← pow_add, hrr, mul_one]
    have hsum :
        (∑ r : Fin (n + 2),
            (-1 : ℤ) ^ ((Fin.last (n + 1) : ℕ) - r) •
              cycleForm d₁ ρ₁ (n + 1) (hochschildFace r.castSucc w)) =
          (-1 : ℤ) ^ (n + 1) • barCoboundary R A Ω₁ (n + 1) (cycleForm d₁ ρ₁ (n + 1)) w := by
      rw [barCoboundary_apply, Finset.smul_sum]
      refine Finset.sum_congr rfl fun r _ ↦ ?_
      rw [hpow, mul_smul, hochschildFace_castSucc]
    have hnn : (-1 : ℤ) ^ (n + 1 + (n + 1)) = 1 := Even.neg_one_pow ⟨n + 1, by omega⟩
    rw [hsum, barCoboundary_cycleForm hd₁ hρ₁, smul_smul, ← pow_add, hnn, one_smul]
    simp only [w, hochschildFace_castSucc, Fin.init_contractNth_castSucc_last,
      Fin.contractNth_castSucc_last_apply_last]

omit [GradedAlgebra 𝒜₁] [SMulCommClass R B B] [IsScalarTower R B B] in
/-- For an idempotent `e : B` and `E = ρ₂ e`, `D = d₂ E`, one has `E * D * E = 0` and
`E * D * D * E = E * D * D`. -/
private theorem idempotent_dgAlgebra_identities (hd₂ : IsDGAlgebra 𝒜₂ d₂)
    (hρ₂ : ∀ b, ρ₂ b ∈ 𝒜₂ 0) {e : B} (he : IsIdempotentElem e) :
    ρ₂ e * ρ₂ e = ρ₂ e ∧ ρ₂ e * d₂ (ρ₂ e) * ρ₂ e = 0 ∧
      ρ₂ e * d₂ (ρ₂ e) * d₂ (ρ₂ e) * ρ₂ e = ρ₂ e * d₂ (ρ₂ e) * d₂ (ρ₂ e) := by
  set E := ρ₂ e
  set D := d₂ E
  have hEE : E * E = E := by rw [← map_mul, he.eq]
  have hdEE : D = D * E + E * D := by
    have h := hd₂.toIsNonUnitalDGAlgebra.leibniz_of_mem_zero (hρ₂ e) E
    rwa [hEE] at h
  have hEDE : E * D * E = 0 := by
    have h1 : E * D = E * D * E + E * D := by
      conv_lhs => rw [hdEE]
      rw [mul_add, ← mul_assoc, ← mul_assoc, hEE]
    have h2 := congrArg (· - E * D) h1.symm
    rwa [add_sub_cancel_right, sub_self] at h2
  have hEDDE : E * D * D * E = E * D * D := by
    have h1 : E * D * D = (E * D) * (D * E + E * D) := congrArg ((E * D) * ·) hdEE
    rw [mul_add, ← mul_assoc, ← mul_assoc (E * D) E D, hEDE, zero_mul, add_zero] at h1
    exact h1.symm
  exact ⟨hEE, hEDE, hEDDE⟩

/-- Three-term expansion modulo right degree `> 2` of `cycleForm` on `(a₀ ⊗ e, …, aₙ₊₂ ⊗ e)` for
an idempotent `e : B`. -/
private theorem cycleForm_gradedTensorHomOfMemZero_two_sub_mem (hd₁ : IsDGAlgebra 𝒜₁ d₁)
    (hd₂ : IsDGAlgebra 𝒜₂ d₂) {e : B} (he : IsIdempotentElem e) {n : ℕ}
    (a : Fin (n + 3) → A) :
    cycleForm (dgTensorDifferential 𝒜₁ 𝒜₂ d₁ d₂) (gradedTensorHomOfMemZero ρ₁ ρ₂ hρ₁ hρ₂) (n + 2)
        (fun i ↦ a i ⊗ₜ e) -
      (cycleForm d₁ ρ₁ (n + 2) a ᵍ⊗ₜ[R] ρ₂ e +
        (cycleForm d₁ ρ₁ (n + 1) (Fin.init a) * ρ₁ (a (Fin.last (n + 2)))) ᵍ⊗ₜ[R]
          (ρ₂ e * d₂ (ρ₂ e)) +
        cochainPeriodicity R A Ω₁ n (cycleForm d₁ ρ₁ n) a ᵍ⊗ₜ[R]
          (ρ₂ e * d₂ (ρ₂ e) * d₂ (ρ₂ e))) ∈ rightDegreeGt 𝒜₁ 𝒜₂ 2 := by
  obtain ⟨hEE, hEDE, hEDDE⟩ := idempotent_dgAlgebra_identities hd₂ hρ₂ he
  set E := ρ₂ e
  set D := d₂ E
  have hE : E ∈ 𝒜₂ 0 := hρ₂ e
  have hD : D ∈ 𝒜₂ 1 := by simpa using hd₂.map_mem hE
  have hED : E * D ∈ 𝒜₂ 1 := by simpa using SetLike.mul_mem_graded hE hD
  have hEDD : E * D * D ∈ 𝒜₂ 2 := by simpa using SetLike.mul_mem_graded hED hD
  have hmul_ED_E (u : Ω₁) (c : A) :
      ((u ᵍ⊗ₜ[R] (E * D)) * (d₁ (ρ₁ c) ᵍ⊗ₜ[R] E) : 𝒜₁ ᵍ⊗[R] 𝒜₂) = 0 := by
    rw [GradedTensorProduct.tmul_coe_mul_coe_tmul 𝒜₁ 𝒜₂ u ⟨E * D, hED⟩
      ⟨d₁ (ρ₁ c), hd₁.map_mem (hρ₁ c)⟩ E, hEDE, gradedTensor_tmul_zero, smul_zero]
  have hmul_ED_D (u : Ω₁) (c : A) :
      ((u ᵍ⊗ₜ[R] (E * D)) * (ρ₁ c ᵍ⊗ₜ[R] D) : 𝒜₁ ᵍ⊗[R] 𝒜₂) =
        (u * ρ₁ c) ᵍ⊗ₜ[R] (E * D * D) := by
    rw [GradedTensorProduct.tmul_coe_mul_coe_tmul 𝒜₁ 𝒜₂ u ⟨E * D, hED⟩ ⟨ρ₁ c, hρ₁ c⟩ D]
    simp [mul_assoc]
  induction n with
  | zero =>
    have h0 : Fin.init (Fin.init fun i ↦ a i ⊗ₜ[R] e) 0 = a 0 ⊗ₜ[R] e := rfl
    have h1 : Fin.init (fun i ↦ a i ⊗ₜ[R] e) (Fin.last (0 + 1)) = a 1 ⊗ₜ[R] e := rfl
    have h2 : a (Fin.last (1 + 1)) = a 2 := rfl
    have ht01 : ((ρ₁ (a 0) ᵍ⊗ₜ[R] E) * (d₁ (ρ₁ (a 1)) ᵍ⊗ₜ[R] E) : 𝒜₁ ᵍ⊗[R] 𝒜₂) =
        (ρ₁ (a 0) * d₁ (ρ₁ (a 1))) ᵍ⊗ₜ[R] E := by
      rw [GradedTensorProduct.tmul_zero_coe_mul_coe_tmul 𝒜₁ 𝒜₂ (ρ₁ (a 0)) ⟨E, hE⟩
        ⟨d₁ (ρ₁ (a 1)), hd₁.map_mem (hρ₁ (a 1))⟩ E, hEE]
    have ht01' : ((ρ₁ (a 0) ᵍ⊗ₜ[R] E) * (ρ₁ (a 1) ᵍ⊗ₜ[R] D) : 𝒜₁ ᵍ⊗[R] 𝒜₂) =
        (ρ₁ (a 0) * ρ₁ (a 1)) ᵍ⊗ₜ[R] (E * D) :=
      GradedTensorProduct.tmul_zero_coe_mul_coe_tmul 𝒜₁ 𝒜₂ (ρ₁ (a 0)) ⟨E, hE⟩ ⟨ρ₁ (a 1), hρ₁ (a 1)⟩
        D
    have ht1 : (((ρ₁ (a 0) * d₁ (ρ₁ (a 1))) ᵍ⊗ₜ[R] E) * (d₁ (ρ₁ (a 2)) ᵍ⊗ₜ[R] E) :
        𝒜₁ ᵍ⊗[R] 𝒜₂) = (ρ₁ (a 0) * d₁ (ρ₁ (a 1)) * d₁ (ρ₁ (a 2))) ᵍ⊗ₜ[R] E := by
      rw [GradedTensorProduct.tmul_zero_coe_mul_coe_tmul 𝒜₁ 𝒜₂ _ ⟨E, hE⟩
        ⟨d₁ (ρ₁ (a 2)), hd₁.map_mem (hρ₁ (a 2))⟩ E, hEE]
    have ht2 : (((ρ₁ (a 0) * d₁ (ρ₁ (a 1))) ᵍ⊗ₜ[R] E) * (ρ₁ (a 2) ᵍ⊗ₜ[R] D) : 𝒜₁ ᵍ⊗[R] 𝒜₂) =
        (ρ₁ (a 0) * d₁ (ρ₁ (a 1)) * ρ₁ (a 2)) ᵍ⊗ₜ[R] (E * D) :=
      GradedTensorProduct.tmul_zero_coe_mul_coe_tmul 𝒜₁ 𝒜₂ _ ⟨E, hE⟩ ⟨ρ₁ (a 2), hρ₁ (a 2)⟩ D
    rw [cycleForm_succ_apply, cycleForm_succ_apply, cycleForm_zero_apply, h0, h1, h2]
    simp only [gradedTensorHomOfMemZero_tmul, dgTensorDifferential_tmul_of_mem (hρ₁ (a 1)),
      dgTensorDifferential_tmul_of_mem (hρ₁ (a 2)), Int.negOnePow_zero, one_smul,
      show ρ₂ e = E from rfl, show d₂ E = D from rfl,
      mul_add, add_mul, ht01, ht01', ht1, ht2, hmul_ED_E, hmul_ED_D, add_zero, ← add_assoc]
    have hform1 : cycleForm d₁ ρ₁ (0 + 1) (Fin.init a) = ρ₁ (a 0) * d₁ (ρ₁ (a 1)) := by
      rw [cycleForm_succ_apply, cycleForm_zero_apply]
      rfl
    have hform2 : cycleForm d₁ ρ₁ (0 + 2) a = ρ₁ (a 0) * d₁ (ρ₁ (a 1)) * d₁ (ρ₁ (a 2)) := by
      rw [cycleForm_succ_apply, hform1]
      rfl
    have hS0 : cochainPeriodicity R A Ω₁ 0 (cycleForm d₁ ρ₁ 0) a =
        ρ₁ (a 0) * ρ₁ (a 1) * ρ₁ (a 2) := by
      rw [cochainPeriodicity_apply, Fin.sum_univ_one]
      have hIic0 : Finset.Iic (0 : Fin 1) = {0} := Finset.ext fun r ↦ by simp [Fin.eq_zero r]
      rw [hIic0, Finset.sum_singleton]
      simp only [Fin.val_zero, Nat.sub_zero, pow_zero, one_smul, cycleForm_zero_apply]
      have hc : hochschildFace (0 : Fin 1).castSucc (hochschildFace (0 : Fin 1).succ.castSucc a) 0 =
          a 0 * (a 1 * a 2) := by
        rw [hochschildFace_castSucc, hochschildFace_castSucc]
        rfl
      rw [hc, map_mul, map_mul, mul_assoc]
    rw [hform2, hform1, hS0, sub_self]
    exact zero_mem _
  | succ n ih =>
    set c := a (Fin.last (n + 3))
    set X := cycleForm (dgTensorDifferential 𝒜₁ 𝒜₂ d₁ d₂)
      (gradedTensorHomOfMemZero ρ₁ ρ₂ hρ₁ hρ₂) (n + 2) fun i ↦ Fin.init a i ⊗ₜ[R] e
    set ω₂ := cycleForm d₁ ρ₁ (n + 2) (Fin.init a)
    set ω₁ := cycleForm d₁ ρ₁ (n + 1) (Fin.init (Fin.init a)) *
      ρ₁ (Fin.init a (Fin.last (n + 2)))
    set ω₀ := cochainPeriodicity R A Ω₁ n (cycleForm d₁ ρ₁ n) (Fin.init a)
    set Y := (ω₂ ᵍ⊗ₜ[R] E + ω₁ ᵍ⊗ₜ[R] (E * D) + ω₀ ᵍ⊗ₜ[R] (E * D * D) : 𝒜₁ ᵍ⊗[R] 𝒜₂)
    have hinit : Fin.init (fun i ↦ a i ⊗ₜ[R] e) = fun i ↦ Fin.init a i ⊗ₜ[R] e := rfl
    rw [cycleForm_succ_apply, hinit, gradedTensorHomOfMemZero_tmul,
      dgTensorDifferential_tmul_of_mem (hρ₁ c), Int.negOnePow_zero, one_smul]
    have hm1 : ((ω₂ ᵍ⊗ₜ[R] E) * (d₁ (ρ₁ c) ᵍ⊗ₜ[R] E) : 𝒜₁ ᵍ⊗[R] 𝒜₂) =
        (ω₂ * d₁ (ρ₁ c)) ᵍ⊗ₜ[R] E := by
      rw [GradedTensorProduct.tmul_zero_coe_mul_coe_tmul 𝒜₁ 𝒜₂ ω₂ ⟨E, hE⟩
        ⟨d₁ (ρ₁ c), hd₁.map_mem (hρ₁ c)⟩ E, hEE]
    have hm2 : ((ω₂ ᵍ⊗ₜ[R] E) * (ρ₁ c ᵍ⊗ₜ[R] D) : 𝒜₁ ᵍ⊗[R] 𝒜₂) =
        (ω₂ * ρ₁ c) ᵍ⊗ₜ[R] (E * D) :=
      GradedTensorProduct.tmul_zero_coe_mul_coe_tmul 𝒜₁ 𝒜₂ ω₂ ⟨E, hE⟩ ⟨ρ₁ c, hρ₁ c⟩ D
    have hm3 : ((ω₀ ᵍ⊗ₜ[R] (E * D * D)) * (d₁ (ρ₁ c) ᵍ⊗ₜ[R] E) : 𝒜₁ ᵍ⊗[R] 𝒜₂) =
        (ω₀ * d₁ (ρ₁ c)) ᵍ⊗ₜ[R] (E * D * D) := by
      rw [GradedTensorProduct.tmul_coe_mul_coe_tmul 𝒜₁ 𝒜₂ ω₀ ⟨E * D * D, hEDD⟩
        ⟨d₁ (ρ₁ c), hd₁.map_mem (hρ₁ c)⟩ E, hEDDE]
      simp
    have hm4 : (ω₀ ᵍ⊗ₜ[R] (E * D * D)) * (ρ₁ c ᵍ⊗ₜ[R] D) ∈ rightDegreeGt 𝒜₁ 𝒜₂ 2 := by
      rw [GradedTensorProduct.tmul_coe_mul_coe_tmul 𝒜₁ 𝒜₂ ω₀ ⟨E * D * D, hEDD⟩ ⟨ρ₁ c, hρ₁ c⟩ D]
      simp only [mul_zero, zpow_zero, one_smul]
      exact tmul_mem_rightDegreeGt (by omega) _ (SetLike.mul_mem_graded hEDD hD)
    have hYmul :
        Y * (d₁ (ρ₁ c) ᵍ⊗ₜ[R] E + ρ₁ c ᵍ⊗ₜ[R] D) =
          (cycleForm d₁ ρ₁ (n + 3) a ᵍ⊗ₜ[R] E +
            (cycleForm d₁ ρ₁ (n + 2) (Fin.init a) * ρ₁ c) ᵍ⊗ₜ[R] (E * D) +
            cochainPeriodicity R A Ω₁ (n + 1) (cycleForm d₁ ρ₁ (n + 1)) a ᵍ⊗ₜ[R]
              (E * D * D)) +
          (ω₀ ᵍ⊗ₜ[R] (E * D * D)) * (ρ₁ c ᵍ⊗ₜ[R] D) := by
      have hω1c : ω₁ * ρ₁ c = cycleForm d₁ ρ₁ (n + 1) (Fin.init (Fin.init a)) *
          ρ₁ (a (Fin.last (n + 2)).castSucc * c) := by
        simp only [ω₁, Fin.init, mul_assoc, map_mul]
      simp only [Y, add_mul, mul_add, hm1, hm2, hmul_ED_E, hmul_ED_D, hm3, add_zero]
      rw [cycleForm_succ_apply, cochainPeriodicity_cycleForm_succ hd₁ hρ₁, hω1c,
        gradedTensor_add_tmul]
      abel
    have hrest1 := mul_tmul_mem_rightDegreeGt (ih (Fin.init a))
      (hd₁.map_mem (hρ₁ c)) hE le_rfl
    have hrest2 := mul_tmul_mem_rightDegreeGt (ih (Fin.init a)) (hρ₁ c) hD zero_le_one
    have key : X * (d₁ (ρ₁ c) ᵍ⊗ₜ[R] E + ρ₁ c ᵍ⊗ₜ[R] D) -
        (cycleForm d₁ ρ₁ (n + 3) a ᵍ⊗ₜ[R] E +
          (cycleForm d₁ ρ₁ (n + 2) (Fin.init a) * ρ₁ c) ᵍ⊗ₜ[R] (E * D) +
          cochainPeriodicity R A Ω₁ (n + 1) (cycleForm d₁ ρ₁ (n + 1)) a ᵍ⊗ₜ[R]
            (E * D * D)) =
        (X - Y) * (d₁ (ρ₁ c) ᵍ⊗ₜ[R] E) + (X - Y) * (ρ₁ c ᵍ⊗ₜ[R] D) +
          (ω₀ ᵍ⊗ₜ[R] (E * D * D)) * (ρ₁ c ᵍ⊗ₜ[R] D) := by
      have hsub : X * (d₁ (ρ₁ c) ᵍ⊗ₜ[R] E + ρ₁ c ᵍ⊗ₜ[R] D) =
          (X - Y) * (d₁ (ρ₁ c) ᵍ⊗ₜ[R] E) + (X - Y) * (ρ₁ c ᵍ⊗ₜ[R] D) +
            Y * (d₁ (ρ₁ c) ᵍ⊗ₜ[R] E + ρ₁ c ᵍ⊗ₜ[R] D) := by
        simp only [mul_add, sub_mul]
        abel
      rw [hsub, hYmul]
      abel
    rw [key]
    exact add_mem (add_mem hrest1 hrest2) hm4

/-- **The character of a tensor product with a cycle of dimension two along an idempotent**: if
`e : B` is idempotent, then on `(a₀ ⊗ e, …, aₚ₊₂ ⊗ e)` the character of the tensor product cycle
applies `TauCeti.cochainPeriodicity` (`S₀`) to the character of the first cycle, tensored with the
value of the second character at `(e, e, e)`. -/
theorem cycleCharacter_gradedTensorHomOfMemZero_tmul_of_two (hd₁ : IsDGAlgebra 𝒜₁ d₁)
    (hd₂ : IsDGAlgebra 𝒜₂ d₂) {e : B} (he : IsIdempotentElem e) {p : ℕ} (a : Fin (p + 3) → A) :
    cycleCharacter (dgTensorDifferential 𝒜₁ 𝒜₂ d₁ d₂) (gradedTensorTrace 𝒜₁ 𝒜₂ τ₁ τ₂ p 2)
        (gradedTensorHomOfMemZero ρ₁ ρ₂ hρ₁ hρ₂) (p + 2) (fun i ↦ a i ⊗ₜ e) =
      cochainPeriodicity R A M p (cycleCharacter d₁ τ₁ ρ₁ p) a ⊗ₜ
        cycleCharacter d₂ τ₂ ρ₂ 2 (fun _ ↦ e) := by
  have h := rightDegreeGt_le_ker_gradedTensorTrace (τ₁ := τ₁) (τ₂ := τ₂) p 2
    (cycleForm_gradedTensorHomOfMemZero_two_sub_mem (ρ₁ := ρ₁) (ρ₂ := ρ₂) (hρ₁ := hρ₁)
      (hρ₂ := hρ₂) hd₁ hd₂ he a)
  rw [LinearMap.mem_ker, map_sub, sub_eq_zero] at h
  have hE : ρ₂ e ∈ 𝒜₂ 0 := hρ₂ e
  have hD : d₂ (ρ₂ e) ∈ 𝒜₂ 1 := by simpa using hd₂.map_mem hE
  have hED : ρ₂ e * d₂ (ρ₂ e) ∈ 𝒜₂ 1 := by simpa using SetLike.mul_mem_graded hE hD
  have hEDD : ρ₂ e * d₂ (ρ₂ e) * d₂ (ρ₂ e) ∈ 𝒜₂ 2 :=
    by simpa using SetLike.mul_mem_graded hED hD
  have hS0mem : cochainPeriodicity R A Ω₁ p (cycleForm d₁ ρ₁ p) a ∈ 𝒜₁ p := by
    rw [cochainPeriodicity_apply]
    exact sum_mem fun j _ ↦ sum_mem fun r _ ↦ zsmul_mem (cycleForm_mem hd₁ hρ₁ _) _
  have hform2 : cycleForm d₂ ρ₂ 2 (fun _ ↦ e) = ρ₂ e * d₂ (ρ₂ e) * d₂ (ρ₂ e) := by
    rw [cycleForm_succ_apply, cycleForm_succ_apply, cycleForm_zero_apply]
    rfl
  have hchar : τ₁ (cochainPeriodicity R A Ω₁ p (cycleForm d₁ ρ₁ p) a) =
      cochainPeriodicity R A M p (cycleCharacter d₁ τ₁ ρ₁ p) a := by
    simp only [cochainPeriodicity_apply, cycleCharacter_apply, map_sum, map_zsmul]
  rw [cycleCharacter_apply, h, map_add, map_add,
    gradedTensorTrace_tmul_of_mem_of_ne (cycleForm_mem hd₁ hρ₁ a) hE (Or.inr (by decide)),
    gradedTensorTrace_tmul_of_mem_of_ne
      (by simpa using SetLike.mul_mem_graded (cycleForm_mem hd₁ hρ₁ (Fin.init a)) (hρ₁ _))
      hED (Or.inr (by decide)),
    zero_add, zero_add, gradedTensorTrace_tmul_of_mem hS0mem hEDD, ← hform2,
    ← cycleCharacter_apply, hchar]

end LowDimensionRight

end TauCeti
