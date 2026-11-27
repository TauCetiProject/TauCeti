/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.CStarAlgebra.MinTensor.CrossNorm
public import TauCeti.Analysis.CStarAlgebra.MinTensorNorm
import Mathlib.Topology.PartitionOfUnity
import Mathlib.Topology.UrysohnsLemma
import TauCeti.Algebra.Group.Hom.Defs
import TauCeti.Algebra.Order.Archimedean.Basic
import TauCeti.Algebra.TensorProduct.Mul

/-!
# `C(X) ⊙ B` has a unique C*-norm

Let `X` be a compact Hausdorff space and `B` a unital C*-algebra. The star homomorphism
`TauCeti.continuousMapTensorHom X B : C(X, ℂ) ⊗[ℂ] B → C(X, B)`, `f ⊗ b ↦ (x ↦ f x • b)`, gives
a C*-norm `‖·‖_∞` on the algebraic tensor product. The construction itself only needs `B` to be a
topological star algebra over `ℂ`. This file proves that `‖·‖_∞` is the only C*-norm:

* every star homomorphism `Ψ` from `C(X, ℂ) ⊗[ℂ] B` into a C*-algebra satisfies
  `‖Ψ y‖ ≤ ‖y‖_∞` (`NonUnitalStarAlgHom.norm_apply_le_norm_continuousMapTensorHom`);
* every injective one satisfies `‖y‖_∞ ≤ ‖Ψ y‖`
  (`TauCeti.norm_continuousMapTensorHom_le_norm_apply`).

So the minimal and maximal C*-norms are both `‖·‖_∞`
(`TauCeti.minTensorNorm_eq_norm_continuousMapTensorHom`,
`TauCeti.maxTensorNorm_eq_norm_continuousMapTensorHom`), every C*-norm on `C(X) ⊙ B` dominates
the minimal norm (`TauCeti.minTensorNorm_le_norm_apply_of_injective`) and agrees with it
(`TauCeti.norm_apply_eq_minTensorNorm_of_injective`), and `continuousMapTensorHom X B` is
injective.

**Upper bound.** Write `y⋆ y = Σ fᵢ ⊗ bᵢ` and fix `ε > 0`. Near each point `x` the `fᵢ` vary
by less than `δ`, so for every `φ` with `|φ| ≤ 1` supported near `x`,
`‖Ψ(φ ⊗ 1) Ψ(y⋆ y)‖ ≤ ‖φ ⊗ (y⋆ y)(x)‖ + δ Σ ‖bᵢ‖ ≤ ‖y⋆ y‖_∞ + ε`. Take a finite partition of
unity `hₖ` subordinate to such neighbourhoods. The elements `Ψ(φ ⊗ 1)` commute with
`d = Ψ(y⋆ y)`, so for `N = 2 ^ j`, `d ^ N = Σₖ (Ψ(hₖ ^ (1 / N) ⊗ 1) d) ^ N` and
`‖d‖ ^ N ≤ m (‖y⋆ y‖_∞ + ε) ^ N` with `m` the number of pieces; letting `j → ∞` gives
`‖d‖ ≤ ‖y⋆ y‖_∞ + ε`.

**Lower bound.** At a point `x`, an Urysohn function `g` with `g(x) = 1`, `0 ≤ g ≤ 1`, supported
where the `fᵢ` are `δ`-close to `fᵢ(x)`, has `‖Ψ(g ⊗ y(x)) − Ψ(g ⊗ 1) Ψ(y)‖ ≤ δ Σ ‖bᵢ‖`, and
`‖Ψ(g ⊗ y(x))‖ = ‖y(x)‖` because every C*-norm is a cross norm
(`TauCeti.norm_apply_tmul_of_injective`).

## References

* B. Blackadar, *Operator Algebras: Theory of C*-Algebras and von Neumann Algebras*,
  II.9.4.4, II.9.5.1–II.9.5.2.
-/

public section

noncomputable section

open TensorProduct

universe u v w

namespace TauCeti

section Construction

variable (X : Type u) [TopologicalSpace X] (B : Type v) [Semiring B] [Algebra ℂ B] [StarRing B]
  [StarModule ℂ B] [TopologicalSpace B] [IsTopologicalSemiring B] [ContinuousStar B]
  [ContinuousSMul ℂ B]

/-- The scalar functions `C(X, ℂ) → C(X, B)`, `f ↦ (x ↦ f x • 1)`. -/
def continuousMapScalarHom : C(X, ℂ) →⋆ₙₐ[ℂ] C(X, B) :=
  (ContinuousMap.compStarAlgHom X (StarAlgHom.ofId ℂ B)
    (continuous_algebraMap ℂ B)).toNonUnitalStarAlgHom

/-- The constant functions `B → C(X, B)`. -/
def continuousMapConstHom : B →⋆ₙₐ[ℂ] C(X, B) where
  toFun b := ContinuousMap.const X b
  map_smul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl
  map_mul' _ _ := rfl
  map_star' _ := rfl

variable {X B} in
@[simp]
theorem continuousMapScalarHom_apply (f : C(X, ℂ)) (x : X) :
    continuousMapScalarHom X B f x = algebraMap ℂ B (f x) :=
  (rfl)

omit [StarModule ℂ B] [ContinuousSMul ℂ B] in
variable {X B} in
@[simp]
theorem continuousMapConstHom_apply (b : B) (x : X) : continuousMapConstHom X B b x = b :=
  (rfl)

theorem commute_continuousMapScalarHom_continuousMapConstHom (f : C(X, ℂ)) (b : B) :
    Commute (continuousMapScalarHom X B f) (continuousMapConstHom X B b) := by
  ext x
  exact Algebra.commutes (f x) b

/-- The star homomorphism `C(X, ℂ) ⊗[ℂ] B → C(X, B)`, `f ⊗ b ↦ (x ↦ f x • b)`. Its norm is the
unique C*-norm on `C(X, ℂ) ⊗[ℂ] B` (`TauCeti.norm_apply_eq_minTensorNorm_of_injective`). -/
def continuousMapTensorHom : C(X, ℂ) ⊗[ℂ] B →⋆ₙₐ[ℂ] C(X, B) :=
  Algebra.TensorProduct.liftNonUnitalStarAlgHom (continuousMapScalarHom X B)
    (continuousMapConstHom X B) (commute_continuousMapScalarHom_continuousMapConstHom X B)

variable {X B}

@[simp]
theorem continuousMapTensorHom_tmul_apply (f : C(X, ℂ)) (b : B) (x : X) :
    continuousMapTensorHom X B (f ⊗ₜ b) x = f x • b := by
  simp [continuousMapTensorHom, Algebra.smul_def]

end Construction

variable {X : Type u} [TopologicalSpace X] [CompactSpace X] [T2Space X] {B : Type v}
  [CStarAlgebra B]

variable {D : Type w}

/-- The points where every `p.1`, `p ∈ S`, is `δ`-close to its value at `x`. -/
private def nearSet (S : Finset (C(X, ℂ) × B)) (x : X) (δ : ℝ) : Set X :=
  {x' | ∀ p ∈ S, ‖p.1 x' - p.1 x‖ < δ}

omit [CompactSpace X] [T2Space X] [CStarAlgebra B] in
private theorem isOpen_nearSet (S : Finset (C(X, ℂ) × B)) (x : X) (δ : ℝ) :
    IsOpen (nearSet S x δ) := by
  simp only [nearSet, Set.ofPred_forall]
  exact isOpen_biInter_finset fun p _ ↦ isOpen_lt (by fun_prop) continuous_const

omit [CompactSpace X] [T2Space X] [CStarAlgebra B] in
private theorem mem_nearSet_self (S : Finset (C(X, ℂ) × B)) (x : X) {δ : ℝ} (hδ : 0 < δ) :
    x ∈ nearSet S x δ :=
  fun p _ ↦ by simpa using hδ

omit [CompactSpace X] [T2Space X] in
/-- For `ε > 0` there is `δ > 0` with `δ Σ ‖p.2‖ ≤ ε`. -/
private theorem exists_pos_mul_sum_le (S : Finset (C(X, ℂ) × B)) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, δ * ∑ p ∈ S, ‖p.2‖ ≤ ε := by
  have hM : 0 ≤ ∑ p ∈ S, ‖p.2‖ := Finset.sum_nonneg fun _ _ ↦ norm_nonneg _
  refine ⟨ε / (∑ p ∈ S, ‖p.2‖ + 1), div_pos hε (by linarith), ?_⟩
  rw [div_mul_eq_mul_div, div_le_iff₀ (by linarith)]
  nlinarith

omit [T2Space X] in
/-- The local estimate: if `|φ| ≤ 1` and `φ` vanishes off `nearSet S x δ`, then `Ψ((φ ⊗ 1) y)`
is within `δ Σ ‖bᵢ‖` of `Ψ(φ ⊗ y(x))` for `y = Σ fᵢ ⊗ bᵢ`. -/
private theorem norm_apply_tmul_one_mul_sub_le [NonUnitalCStarAlgebra D]
    (Ψ : C(X, ℂ) ⊗[ℂ] B →⋆ₙₐ[ℂ] D) (S : Finset (C(X, ℂ) × B)) (x : X) {φ : C(X, ℂ)} {δ : ℝ}
    (hδ : 0 ≤ δ) (hφ : ∀ x', ‖φ x'‖ ≤ 1) (hloc : ∀ x', φ x' ≠ 0 → x' ∈ nearSet S x δ) :
    ‖Ψ ((φ ⊗ₜ 1) * ∑ p ∈ S, p.1 ⊗ₜ p.2) -
      Ψ (φ ⊗ₜ continuousMapTensorHom X B (∑ p ∈ S, p.1 ⊗ₜ p.2) x)‖ ≤
      δ * ∑ p ∈ S, ‖p.2‖ := by
  have h : Ψ ((φ ⊗ₜ 1) * ∑ p ∈ S, p.1 ⊗ₜ p.2) -
      Ψ (φ ⊗ₜ continuousMapTensorHom X B (∑ p ∈ S, p.1 ⊗ₜ p.2) x) =
      ∑ p ∈ S, Ψ ((φ * p.1 - p.1 x • φ) ⊗ₜ p.2) := by
    rw [Finset.mul_sum, map_sum, map_sum, ContinuousMap.coe_sum, Finset.sum_apply, tmul_sum,
      map_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun p _ ↦ ?_
    rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul, continuousMapTensorHom_tmul_apply,
      ← smul_tmul, ← map_sub, ← sub_tmul]
  rw [h, Finset.mul_sum]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun p hp ↦ ?_)
  refine (Ψ.norm_apply_tmul_le _ _).trans (mul_le_mul_of_nonneg_right ?_ (norm_nonneg _))
  refine (ContinuousMap.norm_le _ hδ).2 fun x' ↦ ?_
  have : (φ * p.1 - p.1 x • φ) x' = φ x' * (p.1 x' - p.1 x) := by
    simp only [ContinuousMap.sub_apply, ContinuousMap.mul_apply, ContinuousMap.smul_apply,
      smul_eq_mul]
    ring
  rw [this, norm_mul]
  by_cases h0 : φ x' = 0
  · simp [h0, hδ]
  · calc ‖φ x'‖ * ‖p.1 x' - p.1 x‖ ≤ 1 * δ :=
          mul_le_mul (hφ x') (hloc x' h0 p hp).le (norm_nonneg _) zero_le_one
      _ = δ := one_mul δ

omit [T2Space X] in
/-- The local bound of the upper estimate: `‖Ψ(φ ⊗ 1) Ψ(y)‖ ≤ ‖y‖_∞ + δ Σ ‖bᵢ‖` when `|φ| ≤ 1`
and `φ` vanishes off `nearSet S x δ`. -/
private theorem norm_apply_tmul_one_mul_le [NonUnitalCStarAlgebra D]
    (Ψ : C(X, ℂ) ⊗[ℂ] B →⋆ₙₐ[ℂ] D) (S : Finset (C(X, ℂ) × B)) (x : X) {φ : C(X, ℂ)} {δ : ℝ}
    (hδ : 0 ≤ δ) (hφ : ∀ x', ‖φ x'‖ ≤ 1) (hloc : ∀ x', φ x' ≠ 0 → x' ∈ nearSet S x δ) :
    ‖Ψ (φ ⊗ₜ 1) * Ψ (∑ p ∈ S, p.1 ⊗ₜ p.2)‖ ≤
      ‖continuousMapTensorHom X B (∑ p ∈ S, p.1 ⊗ₜ p.2)‖ + δ * ∑ p ∈ S, ‖p.2‖ := by
  set T := continuousMapTensorHom X B
  rw [← map_mul]
  set u := Ψ ((φ ⊗ₜ 1) * ∑ p ∈ S, p.1 ⊗ₜ p.2)
  set v := Ψ (φ ⊗ₜ T (∑ p ∈ S, p.1 ⊗ₜ p.2) x)
  have hφn : ‖φ‖ ≤ 1 := (ContinuousMap.norm_le _ zero_le_one).2 hφ
  calc ‖u‖ = ‖v + (u - v)‖ := by rw [add_sub_cancel]
    _ ≤ ‖v‖ + ‖u - v‖ := norm_add_le _ _
    _ ≤ ‖T (∑ p ∈ S, p.1 ⊗ₜ p.2)‖ + δ * ∑ p ∈ S, ‖p.2‖ := by
        refine add_le_add ?_ (norm_apply_tmul_one_mul_sub_le Ψ S x hδ hφ hloc)
        refine (Ψ.norm_apply_tmul_le _ _).trans ?_
        calc ‖φ‖ * ‖T (∑ p ∈ S, p.1 ⊗ₜ p.2) x‖ ≤ 1 * ‖T (∑ p ∈ S, p.1 ⊗ₜ p.2)‖ :=
              mul_le_mul hφn (ContinuousMap.norm_coe_le_norm _ _) (norm_nonneg _) zero_le_one
          _ = _ := one_mul _

/-- The `N`-th root `x ↦ ρ(x) ^ (1 / N)` of a function `0 ≤ ρ ≤ 1`, as a complex function. -/
private def rootFun (ρ : C(X, ℝ)) (N : ℕ) : C(X, ℂ) :=
  ⟨fun x ↦ ((ρ x ^ ((N : ℝ)⁻¹) : ℝ) : ℂ), by
    have : Continuous fun x ↦ ρ x ^ ((N : ℝ)⁻¹) :=
      ρ.continuous.rpow_const fun _ ↦ Or.inr (by positivity)
    fun_prop⟩

omit [CompactSpace X] [T2Space X] in
private theorem rootFun_apply (ρ : C(X, ℝ)) (N : ℕ) (x : X) :
    rootFun ρ N x = ((ρ x ^ ((N : ℝ)⁻¹) : ℝ) : ℂ) :=
  rfl

omit [CompactSpace X] [T2Space X] in
private theorem norm_rootFun_apply_le {ρ : C(X, ℝ)} (h0 : ∀ x, 0 ≤ ρ x) (h1 : ∀ x, ρ x ≤ 1)
    (N : ℕ) (x : X) : ‖rootFun ρ N x‖ ≤ 1 := by
  rw [rootFun_apply, Complex.norm_real, Real.norm_of_nonneg (Real.rpow_nonneg (h0 x) _)]
  exact Real.rpow_le_one (h0 x) (h1 x) (by positivity)

omit [CompactSpace X] [T2Space X] in
private theorem rootFun_apply_eq_zero {ρ : C(X, ℝ)} {N : ℕ} (hN : N ≠ 0) {x : X} (h : ρ x = 0) :
    rootFun ρ N x = 0 := by
  rw [rootFun_apply, h, Real.zero_rpow (inv_ne_zero (Nat.cast_ne_zero.2 hN)),
    Complex.ofReal_zero]

omit [T2Space X] in
/-- The power decomposition: for a partition of unity `ρ` and `N ≠ 0`,
`Ψ(z) ^ N = Σᵢ (Ψ(ρᵢ ^ (1 / N) ⊗ 1) Ψ(z)) ^ N`. -/
private theorem apply_pow_eq_sum {E : Type*} [CStarAlgebra E] (Ψ : C(X, ℂ) ⊗[ℂ] B →⋆ₙₐ[ℂ] E)
    {ι : Type*} [Fintype ι] (ρ : PartitionOfUnity ι X) (z : C(X, ℂ) ⊗[ℂ] B) {N : ℕ}
    (hN : N ≠ 0) :
    Ψ z ^ N = ∑ i, (Ψ (rootFun (ρ i) N ⊗ₜ 1) * Ψ z) ^ N := by
  have hsum : ∑ i, (⟨fun x' ↦ ((ρ i x' : ℝ) : ℂ), by fun_prop⟩ : C(X, ℂ)) = 1 := by
    ext x'
    rw [ContinuousMap.coe_sum, Finset.sum_apply]
    simp only [ContinuousMap.coe_mk, ContinuousMap.one_apply]
    rw [← Complex.ofReal_sum, ← finsum_eq_sum_of_fintype, ρ.sum_eq_one (Set.mem_univ x'),
      Complex.ofReal_one]
  obtain ⟨n, hn⟩ := Nat.exists_eq_succ_of_ne_zero hN
  have h1 : Ψ z ^ N = Ψ (1 ⊗ₜ 1) * Ψ z ^ N := by
    rw [hn, pow_succ', ← mul_assoc, ← map_mul, ← Algebra.TensorProduct.one_def, one_mul]
  rw [h1, ← hsum, sum_tmul, map_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  have hroot : (⟨fun x' ↦ ((ρ i x' : ℝ) : ℂ), by fun_prop⟩ : C(X, ℂ)) ⊗ₜ[ℂ] (1 : B) =
      (rootFun (ρ i) N ⊗ₜ[ℂ] (1 : B)) ^ N := by
    rw [Algebra.TensorProduct.tmul_pow, one_pow]
    congr 1
    ext x'
    rw [ContinuousMap.pow_apply, rootFun_apply, ContinuousMap.coe_mk, ← Complex.ofReal_pow,
      Real.rpow_inv_natCast_pow (ρ.nonneg i x') hN]
  rw [hroot, hn, map_pow_succ Ψ _ n, ← hn,
    ((Algebra.TensorProduct.commute_tmul_one (rootFun (ρ i) N) _).map Ψ).mul_pow, hn]

/-- The upper estimate for elements with self-adjoint image. -/
private theorem norm_apply_le_of_isSelfAdjoint [CStarAlgebra D] (Ψ : C(X, ℂ) ⊗[ℂ] B →⋆ₙₐ[ℂ] D)
    (z : C(X, ℂ) ⊗[ℂ] B) (hz : IsSelfAdjoint (Ψ z)) :
    ‖Ψ z‖ ≤ ‖continuousMapTensorHom X B z‖ := by
  refine le_of_forall_pos_le_add fun ε hε ↦ ?_
  obtain ⟨S, rfl⟩ := TensorProduct.exists_finset z
  obtain ⟨δ, hδ, hδM⟩ := exists_pos_mul_sum_le S hε
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover (fun x ↦ nearSet S x δ)
    (isOpen_nearSet S · δ) (fun x _ ↦ Set.mem_iUnion.2 ⟨x, mem_nearSet_self S x hδ⟩)
  obtain ⟨ρ, hρ⟩ := PartitionOfUnity.exists_isSubordinate isClosed_univ
    (fun i : t ↦ nearSet S i δ) (fun i ↦ isOpen_nearSet S i δ) fun x' _ ↦ by
      obtain ⟨i, hi, hx'⟩ := Set.mem_iUnion₂.1 (ht (Set.mem_univ x'))
      exact Set.mem_iUnion.2 ⟨⟨i, hi⟩, hx'⟩
  set R := ‖continuousMapTensorHom X B (∑ p ∈ S, p.1 ⊗ₜ p.2)‖ + ε
  have hR0 : 0 < R := by positivity
  refine le_of_forall_pow_two_pow_le (m := t.card) hR0 fun j ↦ ?_
  have hN0 : 2 ^ j ≠ 0 := pow_ne_zero _ two_ne_zero
  have hk : ∀ i : t, ‖Ψ (rootFun (ρ i) (2 ^ j) ⊗ₜ 1) * Ψ (∑ p ∈ S, p.1 ⊗ₜ p.2)‖ ≤ R := by
    intro i
    refine (norm_apply_tmul_one_mul_le Ψ S i hδ.le
      (norm_rootFun_apply_le (ρ.nonneg i) (ρ.le_one i) _) fun x' hx' ↦ hρ i
        (subset_tsupport _ fun h0 ↦ hx' (rootFun_apply_eq_zero hN0 h0))).trans ?_
    linarith
  calc ‖Ψ (∑ p ∈ S, p.1 ⊗ₜ p.2)‖ ^ 2 ^ j = ‖Ψ (∑ p ∈ S, p.1 ⊗ₜ p.2) ^ 2 ^ j‖ :=
        (hz.norm_pow_two_pow j).symm
    _ ≤ ∑ i : t, ‖(Ψ (rootFun (ρ i) (2 ^ j) ⊗ₜ 1) * Ψ (∑ p ∈ S, p.1 ⊗ₜ p.2)) ^ 2 ^ j‖ := by
        rw [apply_pow_eq_sum Ψ ρ _ hN0]; exact norm_sum_le _ _
    _ ≤ ∑ _i : t, R ^ 2 ^ j := Finset.sum_le_sum fun i _ ↦
        (norm_pow_le' _ (Nat.pos_of_ne_zero hN0)).trans
          (pow_le_pow_left₀ (norm_nonneg _) (hk i) _)
    _ = (t.card : ℝ) * R ^ 2 ^ j := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_coe, nsmul_eq_mul]

/-- **Upper bound.** Every star homomorphism from `C(X, ℂ) ⊗[ℂ] B` into a C*-algebra is bounded
by the supremum norm of `TauCeti.continuousMapTensorHom`. -/
theorem _root_.NonUnitalStarAlgHom.norm_apply_le_norm_continuousMapTensorHom
    [NonUnitalCStarAlgebra D]
    (Ψ : C(X, ℂ) ⊗[ℂ] B →⋆ₙₐ[ℂ] D) (y : C(X, ℂ) ⊗[ℂ] B) :
    ‖Ψ y‖ ≤ ‖continuousMapTensorHom X B y‖ := by
  set Ψ' := (Unitization.inrNonUnitalStarAlgHom ℂ D).comp Ψ
  have hΨ' : ∀ z, ‖Ψ' z‖ = ‖Ψ z‖ := fun z ↦ Unitization.norm_inr (𝕜 := ℂ) (Ψ z)
  have h := norm_apply_le_of_isSelfAdjoint Ψ' (star y * y)
    (by rw [map_mul, map_star]; exact IsSelfAdjoint.star_mul_self _)
  rw [map_mul, map_star, CStarRing.norm_star_mul_self, map_mul, map_star,
    CStarRing.norm_star_mul_self, hΨ'] at h
  exact (mul_self_le_mul_self_iff (norm_nonneg _) (norm_nonneg _)).2 h

/-- An Urysohn function at `x`: `|g| ≤ 1`, `g x = 1`, and `g` vanishes off the open set `U ∋ x`. -/
private theorem exists_bump_of_isOpen {U : Set X} (hU : IsOpen U) {x : X} (hx : x ∈ U) :
    ∃ g : C(X, ℂ), (∀ x', ‖g x'‖ ≤ 1) ∧ g x = 1 ∧ ∀ x', g x' ≠ 0 → x' ∈ U := by
  obtain ⟨f, hf0, hf1, hf01⟩ := exists_continuous_zero_one_of_isClosed hU.isClosed_compl
    isClosed_singleton (Set.disjoint_singleton_right.2 fun h ↦ h hx)
  refine ⟨⟨fun x' ↦ ((f x' : ℝ) : ℂ), by fun_prop⟩, fun x' ↦ ?_, ?_, fun x' hx' ↦ ?_⟩
  · rw [ContinuousMap.coe_mk, Complex.norm_real, Real.norm_of_nonneg (hf01 x').1]
    exact (hf01 x').2
  · rw [ContinuousMap.coe_mk, hf1 (Set.mem_singleton x), Pi.one_apply, Complex.ofReal_one]
  · by_contra hU'
    apply hx'
    rw [ContinuousMap.coe_mk, hf0 hU', Pi.zero_apply, Complex.ofReal_zero]

/-- **Lower bound.** Every injective star homomorphism from `C(X, ℂ) ⊗[ℂ] B` into a C*-algebra
dominates the supremum norm of `TauCeti.continuousMapTensorHom`. -/
theorem norm_continuousMapTensorHom_le_norm_apply [NonUnitalCStarAlgebra D]
    {Ψ : C(X, ℂ) ⊗[ℂ] B →⋆ₙₐ[ℂ] D} (hΨ : Function.Injective Ψ) (y : C(X, ℂ) ⊗[ℂ] B) :
    ‖continuousMapTensorHom X B y‖ ≤ ‖Ψ y‖ := by
  refine (ContinuousMap.norm_le _ (norm_nonneg _)).2 fun x ↦ ?_
  refine le_of_forall_pos_le_add fun ε hε ↦ ?_
  obtain ⟨S, rfl⟩ := TensorProduct.exists_finset y
  obtain ⟨δ, hδ, hδM⟩ := exists_pos_mul_sum_le S hε
  obtain ⟨g, hg1, hgx, hloc⟩ := exists_bump_of_isOpen (isOpen_nearSet S x δ)
    (mem_nearSet_self S x hδ)
  have hgn : ‖g‖ = 1 := le_antisymm ((ContinuousMap.norm_le _ zero_le_one).2 hg1)
    (by simpa [hgx] using g.norm_coe_le_norm x)
  have h1 := norm_apply_tmul_one_mul_sub_le Ψ S x hδ.le hg1 hloc
  have hu : ‖Ψ ((g ⊗ₜ 1) * ∑ p ∈ S, p.1 ⊗ₜ p.2)‖ ≤ ‖Ψ (∑ p ∈ S, p.1 ⊗ₜ p.2)‖ := by
    rw [map_mul]
    refine (norm_mul_le _ _).trans ?_
    calc ‖Ψ (g ⊗ₜ 1)‖ * ‖Ψ (∑ p ∈ S, p.1 ⊗ₜ p.2)‖ ≤ 1 * ‖Ψ (∑ p ∈ S, p.1 ⊗ₜ p.2)‖ := by
          refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
          rw [← hgn]
          exact Ψ.norm_apply_tmul_one_le g
      _ = _ := one_mul _
  set T := continuousMapTensorHom X B
  set u := Ψ ((g ⊗ₜ 1) * ∑ p ∈ S, p.1 ⊗ₜ p.2)
  set v := Ψ (g ⊗ₜ T (∑ p ∈ S, p.1 ⊗ₜ p.2) x)
  calc ‖T (∑ p ∈ S, p.1 ⊗ₜ p.2) x‖ = ‖v‖ := by
        rw [norm_apply_tmul_of_injective hΨ, hgn, one_mul]
    _ = ‖u + (v - u)‖ := by rw [add_sub_cancel]
    _ ≤ ‖u‖ + ‖v - u‖ := norm_add_le _ _
    _ ≤ ‖Ψ (∑ p ∈ S, p.1 ⊗ₜ p.2)‖ + ε := add_le_add hu (by rw [norm_sub_rev]; linarith)

variable (X B)

/-- The maximal norm on `C(X, ℂ) ⊗[ℂ] B` is at most the supremum norm. -/
theorem maxTensorNorm_le_norm_continuousMapTensorHom (y : C(X, ℂ) ⊗[ℂ] B) :
    maxTensorNorm C(X, ℂ) B y ≤ ‖continuousMapTensorHom X B y‖ :=
  maxTensorNorm_le_of_forall fun p ↦ p.tensorHom.norm_apply_le_norm_continuousMapTensorHom y

/-- The supremum norm on `C(X, ℂ) ⊗[ℂ] B` is at most the minimal norm. -/
theorem norm_continuousMapTensorHom_le_minTensorNorm (y : C(X, ℂ) ⊗[ℂ] B) :
    ‖continuousMapTensorHom X B y‖ ≤ minTensorNorm C(X, ℂ) B y := by
  obtain ⟨p, hp, -⟩ :=
    RepresentationPair.exists_tensorHom_spatial_injective_and_norm_tensorHom_spatial_tmul
      C(X, ℂ) B
  refine (norm_continuousMapTensorHom_le_norm_apply hp y).trans ?_
  rw [CommutingRepresentationPair.tensorHom_spatial]
  exact norm_spatialTensorHom_le_minTensorNorm _ _ y

/-- **The minimal norm on `C(X) ⊙ B` is the supremum norm** `‖y‖_∞` of `C(X, B)`. -/
theorem minTensorNorm_eq_norm_continuousMapTensorHom (y : C(X, ℂ) ⊗[ℂ] B) :
    minTensorNorm C(X, ℂ) B y = ‖continuousMapTensorHom X B y‖ :=
  le_antisymm ((minTensorNorm_le_maxTensorNorm y).trans
    (maxTensorNorm_le_norm_continuousMapTensorHom X B y))
    (norm_continuousMapTensorHom_le_minTensorNorm X B y)

/-- **The maximal norm on `C(X) ⊙ B` is the supremum norm** `‖y‖_∞` of `C(X, B)`. -/
theorem maxTensorNorm_eq_norm_continuousMapTensorHom (y : C(X, ℂ) ⊗[ℂ] B) :
    maxTensorNorm C(X, ℂ) B y = ‖continuousMapTensorHom X B y‖ :=
  le_antisymm (maxTensorNorm_le_norm_continuousMapTensorHom X B y)
    ((norm_continuousMapTensorHom_le_minTensorNorm X B y).trans (minTensorNorm_le_maxTensorNorm y))

/-- The minimal and maximal norms on `C(X) ⊙ B` agree. -/
theorem minTensorNorm_eq_maxTensorNorm_of_continuousMap (y : C(X, ℂ) ⊗[ℂ] B) :
    minTensorNorm C(X, ℂ) B y = maxTensorNorm C(X, ℂ) B y := by
  rw [minTensorNorm_eq_norm_continuousMapTensorHom, maxTensorNorm_eq_norm_continuousMapTensorHom]

/-- `f ⊗ b ↦ (x ↦ f x • b)` is injective on `C(X, ℂ) ⊗[ℂ] B`. -/
theorem continuousMapTensorHom_injective : Function.Injective (continuousMapTensorHom X B) := by
  refine (injective_iff_map_eq_zero _).2 fun y hy ↦ ?_
  rw [← minTensorNorm_eq_zero_iff, minTensorNorm_eq_norm_continuousMapTensorHom, hy, norm_zero]

variable {X B}

/-- **Every C*-norm on `C(X) ⊙ B` dominates the minimal norm.** -/
theorem minTensorNorm_le_norm_apply_of_injective [NonUnitalCStarAlgebra D]
    {Ψ : C(X, ℂ) ⊗[ℂ] B →⋆ₙₐ[ℂ] D} (hΨ : Function.Injective Ψ) (y : C(X, ℂ) ⊗[ℂ] B) :
    minTensorNorm C(X, ℂ) B y ≤ ‖Ψ y‖ := by
  rw [minTensorNorm_eq_norm_continuousMapTensorHom]
  exact norm_continuousMapTensorHom_le_norm_apply hΨ y

/-- **`C(X) ⊙ B` has a unique C*-norm**: every injective star homomorphism from `C(X, ℂ) ⊗[ℂ] B`
into a C*-algebra is isometric for the minimal norm. -/
theorem norm_apply_eq_minTensorNorm_of_injective [NonUnitalCStarAlgebra D]
    {Ψ : C(X, ℂ) ⊗[ℂ] B →⋆ₙₐ[ℂ] D} (hΨ : Function.Injective Ψ) (y : C(X, ℂ) ⊗[ℂ] B) :
    ‖Ψ y‖ = minTensorNorm C(X, ℂ) B y := by
  rw [minTensorNorm_eq_norm_continuousMapTensorHom]
  exact le_antisymm (Ψ.norm_apply_le_norm_continuousMapTensorHom y)
    (norm_continuousMapTensorHom_le_norm_apply hΨ y)

end TauCeti
