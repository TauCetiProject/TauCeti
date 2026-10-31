/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.DG.Algebra.TensorProduct
public import TauCeti.RingTheory.CyclicCohomology.Cycle
import TauCeti.Algebra.Ring.NegOnePow

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

## Main definitions

* `TauCeti.gradedTensorTrace`: the tensor product of two traces of dimensions `p` and `q`.

## Main results

* `TauCeti.IsClosedGradedTrace.gradedTensor`: the tensor product of closed graded traces of
  dimensions `p` and `q` is a closed graded trace of dimension `p + q`.
* `TauCeti.cycleCharacter_gradedTensorHomOfMemZero_tmul_of_zero`: the character of a tensor
  product with a cycle of dimension zero.

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

/-! ### Tensoring with a cycle of dimension zero -/

section DimensionZero

variable {A B : Type*} [NonUnitalSemiring A] [Module R A] [SMulCommClass R A A]
  [IsScalarTower R A A] [NonUnitalSemiring B] [Module R B] [SMulCommClass R B B]
  [IsScalarTower R B B]
  {ρ₁ : A →ₙₐ[R] Ω₁} {ρ₂ : B →ₙₐ[R] Ω₂} {hρ₁ : ∀ a, ρ₁ a ∈ 𝒜₁ 0} {hρ₂ : ∀ b, ρ₂ b ∈ 𝒜₂ 0}
  {d₁ : Ω₁ →ₗ[R] Ω₁} {d₂ : Ω₂ →ₗ[R] Ω₂}

variable (𝒜₁ 𝒜₂) in
/-- The span of the pure tensors whose right factor is homogeneous of positive degree. -/
private noncomputable def positiveRight : Submodule R (𝒜₁ ᵍ⊗[R] 𝒜₂) :=
  Submodule.span R {x | ∃ j : ℤ, 0 < j ∧ ∃ (u : Ω₁) (v : Ω₂), v ∈ 𝒜₂ j ∧ x = u ᵍ⊗ₜ[R] v}

private theorem tmul_mem_positiveRight {j : ℤ} (hj : 0 < j) (u : Ω₁) {v : Ω₂} (hv : v ∈ 𝒜₂ j) :
    u ᵍ⊗ₜ[R] v ∈ positiveRight 𝒜₁ 𝒜₂ :=
  Submodule.subset_span ⟨j, hj, u, v, hv, rfl⟩

/-- Multiplying on the right by a homogeneous pure tensor of nonnegative right degree preserves
the span of pure tensors of positive right degree. -/
private theorem mul_tmul_mem_positiveRight {z : 𝒜₁ ᵍ⊗[R] 𝒜₂} (hz : z ∈ positiveRight 𝒜₁ 𝒜₂)
    {i j : ℤ} {u : Ω₁} {v : Ω₂} (hu : u ∈ 𝒜₁ i) (hv : v ∈ 𝒜₂ j) (hj : 0 ≤ j) :
    z * (u ᵍ⊗ₜ[R] v) ∈ positiveRight 𝒜₁ 𝒜₂ := by
  have h : positiveRight 𝒜₁ 𝒜₂ ≤ (positiveRight 𝒜₁ 𝒜₂).comap
      ((GradedTensorProduct.mulHom 𝒜₁ 𝒜₂).flip (u ᵍ⊗ₜ[R] v)) := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨j', hj', u', v', hv', rfl⟩
    rw [SetLike.mem_coe, Submodule.mem_comap, LinearMap.flip_apply,
      ← GradedTensorProduct.mul_def,
      GradedTensorProduct.tmul_coe_mul_coe_tmul 𝒜₁ 𝒜₂ u' ⟨v', hv'⟩ ⟨u, hu⟩ v, Units.smul_def]
    exact zsmul_mem (tmul_mem_positiveRight (by omega) _ (SetLike.mul_mem_graded hv' hv)) _
  simpa only [Submodule.mem_comap, LinearMap.flip_apply, ← GradedTensorProduct.mul_def] using h hz

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
      cycleForm d₁ ρ₁ n a ᵍ⊗ₜ[R] (List.ofFn fun i ↦ ρ₂ (b i)).prod ∈ positiveRight 𝒜₁ 𝒜₂ := by
  induction n with
  | zero => simp [zero_mem]
  | succ n ih =>
    set c := a (Fin.last (n + 1))
    set e := b (Fin.last (n + 1))
    have hP := prod_ofFn_mem_zero hρ₂ (Fin.init b)
    have hω := cycleForm_mem hd₁ hρ₁ (Fin.init a)
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
    have hside : (ω ᵍ⊗ₜ[R] P) * (ρ₁ c ᵍ⊗ₜ[R] d₂ (ρ₂ e)) ∈ positiveRight 𝒜₁ 𝒜₂ := by
      rw [GradedTensorProduct.tmul_zero_coe_mul_coe_tmul 𝒜₁ 𝒜₂ ω ⟨P, hP⟩ ⟨ρ₁ c, hρ₁ c⟩]
      exact tmul_mem_positiveRight (by omega) _ (SetLike.mul_mem_graded hP (hd₂.map_mem (hρ₂ e)))
    have hrest := mul_tmul_mem_positiveRight (ih (Fin.init a) (Fin.init b))
      (hd₁.map_mem (hρ₁ c)) (hρ₂ e) le_rfl
    have hrest' := mul_tmul_mem_positiveRight (ih (Fin.init a) (Fin.init b))
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
  have hker : positiveRight 𝒜₁ 𝒜₂ ≤ LinearMap.ker (gradedTensorTrace 𝒜₁ 𝒜₂ τ₁ τ₂ p 0) := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨j, hj, u, v, hv, rfl⟩
    rw [SetLike.mem_coe, LinearMap.mem_ker, gradedTensorTrace_tmul, GradedAlgebra.proj_apply
      (𝒜 := 𝒜₂), DirectSum.decompose_of_mem_ne 𝒜₂ hv (by simpa using hj.ne'), map_zero,
      TensorProduct.tmul_zero]
  have h := hker (cycleForm_gradedTensorHomOfMemZero_sub_mem (ρ₁ := ρ₁) (ρ₂ := ρ₂) (hρ₁ := hρ₁)
    (hρ₂ := hρ₂) hd₁ hd₂ a b)
  rw [LinearMap.mem_ker, map_sub, sub_eq_zero] at h
  rw [cycleCharacter_apply, h, cycleCharacter_apply, gradedTensorTrace_tmul_of_mem
    (cycleForm_mem hd₁ hρ₁ a) (prod_ofFn_mem_zero hρ₂ b)]

end DimensionZero

end TauCeti
