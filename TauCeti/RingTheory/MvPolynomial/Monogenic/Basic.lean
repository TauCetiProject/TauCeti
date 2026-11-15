/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.MvPolynomial.TensorModule
import Mathlib.Algebra.Algebra.Rat

/-!
# Monogenic multivariate polynomials and the Clifford Fischer decomposition

Given an `R`-module `M` and coordinate endomorphisms `c : σ → Module.End R M` indexed by a finite
type `σ`, two first-order operators act on `M`-valued polynomials `MvPolynomial σ R ⊗[R] M`:

* **Clifford coordinate multiplication** `MvPolynomial.cliffordMul c`, given on pure tensors by
  `X (p ⊗ₜ m) = ∑ᵢ (Xᵢ * p) ⊗ₜ cᵢ m`;
* **the polynomial Dirac operator** `MvPolynomial.cliffordDirac c`, given on pure tensors by
  `D (p ⊗ₜ m) = ∑ᵢ (∂p/∂Xᵢ) ⊗ₜ cᵢ m`.

The degree-`k` **monogenic submodule** `MvPolynomial.monogenicSubmodule c k` is the kernel of `D`
inside `homogeneousTensorSubmodule σ R M k`.

When the operators `cᵢ` satisfy the Riemannian Clifford relations `cᵢ ∘ₗ cᵢ = -1` and
`cᵢ ∘ₗ cⱼ + cⱼ ∘ₗ cᵢ = 0` for `i ≠ j`, the operators `X` and `D` satisfy the identities

* `X ∘ₗ X = -(mulLeft R (normSq σ R)).rTensor M` (`X² = -r²`),
* `D ∘ₗ D = -laplacian.rTensor M` (`D² = -Δ`), so every monogenic polynomial is harmonic,
* `D ∘ₗ X + X ∘ₗ D = -(2 • E + card σ • id)`, where `E` is the lifted Euler derivation.

From these identities alone, `u ↦ D (X u)` has trivial kernel under `[Nonempty σ]` and
`[HasUniqueDiv M]`, giving directness `monogenicSubmodule c (k + 1) ⊓ (P_k(M)).map X = ⊥`, and over
any commutative `ℚ`-algebra `R` strong induction on `k` yields the **Clifford Fischer
decomposition**
`P_{k+1}(M) = monogenicSubmodule c (k + 1) ⊔ (P_k(M)).map X`
and the iterated monogenic expansion
`P_k(M) = ⨆ j ≤ k, (monogenicSubmodule c (k - j)).map (X ^ j)`
for arbitrary (not necessarily finite-dimensional) `R`-modules `M`.

Independently of the Clifford relations, polynomial Cauchy-Kowalewskaya along a single variable
`i₀` with `c i₀` surjective shows that `D : P_{k+1}(M) → P_k(M)` is surjective over any commutative
`ℚ`-algebra, yielding the dimension formula
`finrank K (monogenicSubmodule c k) = (card σ - 1).multichoose k * finrank K M`
over a field `K` of characteristic zero whenever `M` is finite-dimensional and some `c i₀` is
surjective.

## Main definitions

* `MvPolynomial.cliffordMul c`: Clifford coordinate multiplication on `MvPolynomial σ R ⊗[R] M`.
* `MvPolynomial.cliffordDirac c`: the polynomial Dirac operator on `MvPolynomial σ R ⊗[R] M`.
* `MvPolynomial.monogenicSubmodule c k`: homogeneous degree-`k` polynomials in `ker D`.

## Main results

* `MvPolynomial.cliffordMul_comp_self_iff`: `X ∘ₗ X = -r²` iff `∀ i, c i ∘ₗ c i = -1` and the `c i`
  pairwise anticommute.
* `MvPolynomial.cliffordDirac_comp_self`: `D ∘ₗ D = -Δ`.
* `MvPolynomial.cliffordDirac_comp_cliffordMul_add_cliffordMul_comp_cliffordDirac`:
  `D ∘ₗ X + X ∘ₗ D = -(2 • E + card σ • id)`.
* `MvPolynomial.disjoint_monogenicSubmodule_map_cliffordMul`: directness of the Clifford Fischer
  decomposition under `[HasUniqueDiv M]`.
* `MvPolynomial.monogenicSubmodule_sup_map_cliffordMul`: the single-step Clifford Fischer
  decomposition over any commutative `ℚ`-algebra.
* `MvPolynomial.homogeneousTensorSubmodule_eq_iSup_map_cliffordMul_pow`: the full monogenic
  expansion of `homogeneousTensorSubmodule σ R M k`.
* `MvPolynomial.finrank_monogenicSubmodule`: rank of `monogenicSubmodule c k` over a field of
  characteristic zero.

## References

* R. Delanghe, F. Sommen, and V. Souček, *Clifford Algebra and Spinor-Valued Functions*,
  Mathematics and its Applications 53, Kluwer Academic Publishers (1992).
* H. B. Lawson and M.-L. Michelsohn, *Spin Geometry*, Princeton Mathematical Series 38 (1989).
-/

public section

open scoped TensorProduct

namespace MvPolynomial

private theorem degree_add_single_sub_single {σ : Type*} (s : σ →₀ ℕ) {i₀ j : σ}
    (hne : j ≠ i₀) (hsj : s j ≠ 0) :
    (s + Finsupp.single i₀ 1 - Finsupp.single j 1).degree = s.degree ∧
      (s + Finsupp.single i₀ 1 - Finsupp.single j 1 : σ →₀ ℕ) i₀ = s i₀ + 1 ∧
      s i₀ < s.degree := by
  have hle : (Finsupp.single j 1 : σ →₀ ℕ) ≤ s + Finsupp.single i₀ 1 := by
    rw [Finsupp.single_le_iff, Finsupp.add_apply, Finsupp.single_eq_of_ne' hne.symm]
    omega
  have hdeg : (s + Finsupp.single i₀ 1 - Finsupp.single j 1).degree = s.degree := by
    have h := map_add Finsupp.degree (s + Finsupp.single i₀ 1 - Finsupp.single j 1)
      (Finsupp.single j 1)
    rw [tsub_add_cancel_of_le hle, map_add Finsupp.degree, Finsupp.degree_single,
      Finsupp.degree_single] at h
    omega
  have hi₀ : (s + Finsupp.single i₀ 1 - Finsupp.single j 1 : σ →₀ ℕ) i₀ = s i₀ + 1 := by
    rw [Finsupp.tsub_apply, Finsupp.add_apply, Finsupp.single_eq_same,
      Finsupp.single_eq_of_ne' hne, tsub_zero]
  refine ⟨hdeg, hi₀, ?_⟩
  by_cases h0 : s i₀ = 0
  · have := Finsupp.le_degree j s
    omega
  · classical
    have hsub : ({i₀, j} : Finset σ) ⊆ s.support := by
      intro x hx
      rcases Finset.mem_insert.mp hx with rfl | hx'
      · exact Finsupp.mem_support_iff.mpr h0
      · rw [Finset.mem_singleton.mp hx']
        exact Finsupp.mem_support_iff.mpr hsj
    have hsum_le := Finset.sum_le_sum_of_subset (f := s) hsub
    rw [Finset.sum_pair hne.symm] at hsum_le
    rw [Finsupp.degree_apply]
    omega

section Semiring

variable {σ R M : Type*} [CommSemiring R] [AddCommMonoid M] [Module R M] [Fintype σ]

/-- **Clifford coordinate multiplication** on `MvPolynomial σ R ⊗[R] M`, sending `p ⊗ₜ m` to
`∑ᵢ (Xᵢ * p) ⊗ₜ cᵢ m`. -/
noncomputable def cliffordMul (c : σ → Module.End R M) :
    Module.End R (MvPolynomial σ R ⊗[R] M) :=
  ∑ i : σ, TensorProduct.map (LinearMap.mulLeft R (X i)) (c i)

/-- **The polynomial Dirac operator** on `MvPolynomial σ R ⊗[R] M`, sending `p ⊗ₜ m` to
`∑ᵢ (∂p/∂Xᵢ) ⊗ₜ cᵢ m`. -/
noncomputable def cliffordDirac (c : σ → Module.End R M) :
    Module.End R (MvPolynomial σ R ⊗[R] M) :=
  ∑ i : σ, TensorProduct.map (pderiv i).toLinearMap (c i)

/-- The submodule of **homogeneous monogenic polynomials** of degree `k` in
`MvPolynomial σ R ⊗[R] M`: homogeneous degree-`k` elements annihilated by `cliffordDirac c`. -/
noncomputable def monogenicSubmodule (c : σ → Module.End R M) (k : ℕ) :
    Submodule R (MvPolynomial σ R ⊗[R] M) :=
  homogeneousTensorSubmodule σ R M k ⊓ LinearMap.ker (cliffordDirac c)

@[simp]
theorem cliffordMul_tmul (c : σ → Module.End R M) (p : MvPolynomial σ R) (m : M) :
    cliffordMul c (p ⊗ₜ[R] m) = ∑ i : σ, (X i * p) ⊗ₜ[R] c i m := by
  simp [cliffordMul, LinearMap.sum_apply]

@[simp]
theorem cliffordDirac_tmul (c : σ → Module.End R M) (p : MvPolynomial σ R) (m : M) :
    cliffordDirac c (p ⊗ₜ[R] m) = ∑ i : σ, pderiv i p ⊗ₜ[R] c i m := by
  simp [cliffordDirac, LinearMap.sum_apply]

@[simp]
theorem cliffordMul_eq_zero_of_isEmpty [IsEmpty σ] (c : σ → Module.End R M) :
    cliffordMul c = 0 := by
  simp [cliffordMul]

@[simp]
theorem cliffordDirac_eq_zero_of_isEmpty [IsEmpty σ] (c : σ → Module.End R M) :
    cliffordDirac c = 0 := by
  simp [cliffordDirac]

theorem mem_monogenicSubmodule {c : σ → Module.End R M} {k : ℕ} {u : MvPolynomial σ R ⊗[R] M} :
    u ∈ monogenicSubmodule c k ↔
      u ∈ homogeneousTensorSubmodule σ R M k ∧ cliffordDirac c u = 0 :=
  Iff.rfl

theorem monogenicSubmodule_le_homogeneousTensorSubmodule (c : σ → Module.End R M) (k : ℕ) :
    monogenicSubmodule c k ≤ homogeneousTensorSubmodule σ R M k :=
  inf_le_left

theorem monogenicSubmodule_le_ker_cliffordDirac (c : σ → Module.End R M) (k : ℕ) :
    monogenicSubmodule c k ≤ LinearMap.ker (cliffordDirac c) :=
  inf_le_right

/-- Monomial coefficients of `cliffordMul c u`: the `s`-coefficient is the sum over `i ∈ s.support`
of `c i` applied to the `(s - single i 1)`-coefficient of `u`. -/
theorem coeffTensor_cliffordMul (c : σ → Module.End R M) (s : σ →₀ ℕ)
    (u : MvPolynomial σ R ⊗[R] M) :
    coeffTensor s (cliffordMul c u) =
      ∑ i ∈ s.support, c i (coeffTensor (s - Finsupp.single i 1) u) := by
  classical
  induction u using TensorProduct.inductionOn with
  | tmul p m =>
    rw [cliffordMul_tmul, map_sum]
    simp_rw [coeffTensor_tmul, coeff_X_mul', ite_smul, zero_smul, ← Finset.sum_filter]
    refine Finset.sum_congr (by ext i; simp) fun i _ ↦ ?_
    exact (map_smul (c i) _ _).symm
  | add x y hx hy =>
    simp_rw [map_add, hx, hy, ← Finset.sum_add_distrib]

/-- Monomial coefficients of `cliffordDirac c u`: the `s`-coefficient is the sum over all `i : σ`
of `(s i + 1) • c i` applied to the `(s + single i 1)`-coefficient of `u`. -/
theorem coeffTensor_cliffordDirac (c : σ → Module.End R M) (s : σ →₀ ℕ)
    (u : MvPolynomial σ R ⊗[R] M) :
    coeffTensor s (cliffordDirac c u) =
      ∑ i : σ, (s i + 1) • c i (coeffTensor (s + Finsupp.single i 1) u) := by
  induction u using TensorProduct.inductionOn with
  | tmul p m =>
    rw [cliffordDirac_tmul, map_sum]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [coeffTensor_tmul, coeffTensor_tmul, coeff_pderiv, mul_comm, mul_smul, ← Nat.cast_one,
      ← Nat.cast_add, Nat.cast_smul_eq_nsmul, map_smul]
  | add x y hx hy =>
    simp_rw [map_add, hx, hy, smul_add, ← Finset.sum_add_distrib]

/-- If `c i₀` is injective for at least one coordinate `i₀` and addition in `M` is cancellative,
then `cliffordMul c` is injective on `MvPolynomial σ R ⊗[R] M`. -/
theorem cliffordMul_injective [IsCancelAdd M] {c : σ → Module.End R M} {i₀ : σ}
    (hc : Function.Injective (c i₀)) :
    Function.Injective (cliffordMul c) := by
  classical
  intro u v huv
  refine ext_coeffTensor fun s ↦ ?_
  suffices ∀ n : ℕ, ∀ t : σ →₀ ℕ, t.degree - t i₀ = n → coeffTensor t u = coeffTensor t v from
    this _ s rfl
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro t htn
  have hsum := congrArg (coeffTensor (t + Finsupp.single i₀ 1)) huv
  rw [coeffTensor_cliffordMul, coeffTensor_cliffordMul] at hsum
  have hmem : i₀ ∈ (t + Finsupp.single i₀ 1).support := by simp
  rw [← Finset.add_sum_erase _ _ hmem, ← Finset.add_sum_erase _ _ hmem] at hsum
  have hrest : ∑ i ∈ (t + Finsupp.single i₀ 1).support.erase i₀,
        c i (coeffTensor (t + Finsupp.single i₀ 1 - Finsupp.single i 1) u) =
      ∑ i ∈ (t + Finsupp.single i₀ 1).support.erase i₀,
        c i (coeffTensor (t + Finsupp.single i₀ 1 - Finsupp.single i 1) v) := by
    refine Finset.sum_congr rfl fun i hi ↦ ?_
    obtain ⟨hne, hisupp⟩ := Finset.mem_erase.mp hi
    have hti : t i ≠ 0 := by
      rwa [Finsupp.mem_support_iff, Finsupp.add_apply, Finsupp.single_eq_of_ne' hne.symm,
        add_zero] at hisupp
    obtain ⟨hdeg, hi₀_val, hlt⟩ := degree_add_single_sub_single t hne hti
    rw [ih _ (by omega) _ rfl]
  rw [hrest, add_right_cancel_iff, add_tsub_cancel_right] at hsum
  exact hc hsum

/-- `cliffordMul c` raises homogeneous degree by one. -/
theorem cliffordMul_mem_homogeneousTensorSubmodule {c : σ → Module.End R M} {k : ℕ}
    {u : MvPolynomial σ R ⊗[R] M} (hu : u ∈ homogeneousTensorSubmodule σ R M k) :
    cliffordMul c u ∈ homogeneousTensorSubmodule σ R M (k + 1) := by
  refine homogeneousTensorSubmodule_inductionOn hu (fun hp m ↦ ?_) fun hx hy ↦ ?_
  · rw [cliffordMul_tmul]
    refine Submodule.sum_mem _ fun i _ ↦ tmul_mem_homogeneousTensorSubmodule ?_ _
    simpa [add_comm] using (isHomogeneous_X R i).mul hp
  · rw [map_add]
    exact Submodule.add_mem _ hx hy

/-- Iterating `cliffordMul c` `j` times raises homogeneous degree by `j`. -/
theorem cliffordMul_pow_mem_homogeneousTensorSubmodule {c : σ → Module.End R M} {k : ℕ} (j : ℕ)
    {u : MvPolynomial σ R ⊗[R] M} (hu : u ∈ homogeneousTensorSubmodule σ R M k) :
    (cliffordMul c ^ j) u ∈ homogeneousTensorSubmodule σ R M (k + j) := by
  induction j with
  | zero => simpa using hu
  | succ j ih =>
    rw [pow_succ', mul_apply_eq_comp, ← add_assoc]
    exact cliffordMul_mem_homogeneousTensorSubmodule ih

/-- `cliffordDirac c` lowers homogeneous degree by one. -/
theorem cliffordDirac_mem_homogeneousTensorSubmodule {c : σ → Module.End R M} {k : ℕ}
    {u : MvPolynomial σ R ⊗[R] M} (hu : u ∈ homogeneousTensorSubmodule σ R M k) :
    cliffordDirac c u ∈ homogeneousTensorSubmodule σ R M (k - 1) := by
  refine homogeneousTensorSubmodule_inductionOn hu (fun hp m ↦ ?_) fun hx hy ↦ ?_
  · rw [cliffordDirac_tmul]
    exact Submodule.sum_mem _ fun i _ ↦ tmul_mem_homogeneousTensorSubmodule hp.pderiv _
  · rw [map_add]
    exact Submodule.add_mem _ hx hy

/-- Degree-zero `M`-valued polynomials are annihilated by `cliffordDirac c`. -/
theorem cliffordDirac_eq_zero_of_mem_zero {c : σ → Module.End R M}
    {u : MvPolynomial σ R ⊗[R] M} (hu : u ∈ homogeneousTensorSubmodule σ R M 0) :
    cliffordDirac c u = 0 := by
  refine homogeneousTensorSubmodule_inductionOn hu (fun {p} hp m ↦ ?_) fun hx hy ↦ ?_
  · rw [cliffordDirac_tmul]
    refine Finset.sum_eq_zero fun i _ ↦ ?_
    have hp0 : pderiv i p = 0 := by
      rw [as_sum p, map_sum]
      refine Finset.sum_eq_zero fun d hd ↦ ?_
      have hd0 : d = 0 := (Finsupp.degree_eq_zero_iff d).mp <| by
        rw [Finsupp.degree_eq_weight_one]
        exact hp (mem_support_iff.mp hd)
      subst hd0
      simp
    rw [hp0, TensorProduct.zero_tmul]
  · simp [map_add, hx, hy]

@[simp]
theorem monogenicSubmodule_zero (c : σ → Module.End R M) :
    monogenicSubmodule c 0 = homogeneousTensorSubmodule σ R M 0 :=
  inf_eq_left.mpr fun _ hu ↦ cliffordDirac_eq_zero_of_mem_zero hu

@[simp]
theorem monogenicSubmodule_succ_eq_bot_of_isEmpty [IsEmpty σ] (c : σ → Module.End R M) (k : ℕ) :
    monogenicSubmodule c (k + 1) = ⊥ := by
  simp [monogenicSubmodule]

/-- In at most one variable, if each `c i` is injective and `[HasUniqueDiv M]` holds, every
positive-degree monogenic polynomial vanishes. -/
theorem monogenicSubmodule_succ_eq_bot_of_subsingleton [Subsingleton σ] [HasUniqueDiv M]
    {c : σ → Module.End R M} (hc : ∀ i, Function.Injective (c i)) (k : ℕ) :
    monogenicSubmodule c (k + 1) = ⊥ := by
  rcases isEmpty_or_nonempty σ with _ | ⟨⟨i₀⟩⟩
  · exact monogenicSubmodule_succ_eq_bot_of_isEmpty c k
  have huniv : (Finset.univ : Finset σ) = {i₀} :=
    Finset.eq_singleton_iff_unique_mem.mpr ⟨Finset.mem_univ i₀, fun j _ ↦ Subsingleton.elim j i₀⟩
  rw [eq_bot_iff]
  rintro u ⟨hu, hDu⟩
  rw [Submodule.mem_bot]
  refine ext_coeffTensor fun s ↦ ?_
  rw [map_zero]
  rcases eq_or_ne s 0 with rfl | hs0
  · refine homogeneousTensorSubmodule_inductionOn hu (fun {p} hp m ↦ ?_) fun hx hy ↦
      by simp [hx, hy]
    have hcoeff : p.coeff 0 = 0 := by
      by_contra hne
      exact Nat.zero_ne_add_one k (by simpa using hp hne)
    rw [coeffTensor_tmul, hcoeff, zero_smul]
  · have hsi : 1 ≤ s i₀ := Nat.one_le_iff_ne_zero.mpr fun h ↦ hs0 <| by
      ext j; rwa [Subsingleton.elim j i₀]
    have hsub : s - Finsupp.single i₀ 1 + Finsupp.single i₀ 1 = s := by
      ext j; rw [Subsingleton.elim j i₀]; simp; omega
    have hD := congrArg (coeffTensor (s - Finsupp.single i₀ 1)) hDu
    rw [map_zero, coeffTensor_cliffordDirac, huniv, Finset.sum_singleton, hsub] at hD
    exact hc i₀ (by simpa using hD)

@[simp]
theorem homogeneousComponentTensor_zero_cliffordMul (c : σ → Module.End R M)
    (u : MvPolynomial σ R ⊗[R] M) :
    homogeneousComponentTensor 0 (cliffordMul c u) = 0 := by
  obtain ⟨N, hN⟩ := exists_sum_homogeneousComponentTensor_eq u
  conv_lhs => rw [← hN]
  simp only [map_sum]
  exact Finset.sum_eq_zero fun j _ ↦
    homogeneousComponentTensor_eq_zero_of_ne
      (cliffordMul_mem_homogeneousTensorSubmodule (homogeneousComponentTensor_mem j u))
      (Nat.zero_ne_add_one j)

@[simp]
theorem homogeneousComponentTensor_succ_cliffordMul (c : σ → Module.End R M) (k : ℕ)
    (u : MvPolynomial σ R ⊗[R] M) :
    homogeneousComponentTensor (k + 1) (cliffordMul c u) =
      cliffordMul c (homogeneousComponentTensor k u) := by
  obtain ⟨N, hkN, hN⟩ := exists_sum_homogeneousComponentTensor_eq_of_le u (k + 1)
  have hmem (j : ℕ) :
      cliffordMul c (homogeneousComponentTensor j u) ∈
        homogeneousTensorSubmodule σ R M (j + 1) :=
    cliffordMul_mem_homogeneousTensorSubmodule (homogeneousComponentTensor_mem j u)
  conv_lhs => rw [← hN]
  simp only [map_sum]
  rw [Finset.sum_eq_single_of_mem k (Finset.mem_range.mpr hkN),
    homogeneousComponentTensor_eq_self (hmem k)]
  intro j _ hj
  exact homogeneousComponentTensor_eq_zero_of_ne (hmem j) (by omega)

@[simp]
theorem homogeneousComponentTensor_cliffordDirac (c : σ → Module.End R M) (k : ℕ)
    (u : MvPolynomial σ R ⊗[R] M) :
    homogeneousComponentTensor k (cliffordDirac c u) =
      cliffordDirac c (homogeneousComponentTensor (k + 1) u) := by
  obtain ⟨N, hkN, hN⟩ := exists_sum_homogeneousComponentTensor_eq_of_le u (k + 2)
  have hmem (j : ℕ) :
      cliffordDirac c (homogeneousComponentTensor (j + 1) u) ∈
        homogeneousTensorSubmodule σ R M j := by
    simpa using cliffordDirac_mem_homogeneousTensorSubmodule
      (homogeneousComponentTensor_mem (j + 1) u)
  conv_lhs => rw [← hN]
  simp only [map_sum]
  rw [Finset.sum_eq_single_of_mem (k + 1) (Finset.mem_range.mpr hkN),
    homogeneousComponentTensor_eq_self (hmem k)]
  intro j _ hj
  rcases j with _ | j
  · rw [cliffordDirac_eq_zero_of_mem_zero (homogeneousComponentTensor_mem 0 u), map_zero]
  · exact homogeneousComponentTensor_eq_zero_of_ne (hmem j) (by omega)

end Semiring

section Ring

variable {σ R M : Type*} [CommRing R] [AddCommGroup M] [Module R M] [Fintype σ]

/-- An `R`-linear endomorphism satisfying `f ∘ₗ f = -1` is bijective, with inverse `-f`. -/
theorem bijective_of_comp_self_eq_neg_one {f : Module.End R M} (hf : f ∘ₗ f = -1) :
    Function.Bijective f :=
  ⟨fun x y hxy ↦ by
    have := congrArg (-f) hxy
    simpa [← LinearMap.comp_apply, hf] using this,
   fun y ↦ ⟨-f y, by simp [← LinearMap.comp_apply, hf]⟩⟩

/-- **Square of Clifford coordinate multiplication**: `X ∘ₗ X = -r²` when each `cᵢ` squares to `-1`
and distinct `cᵢ, cⱼ` anticommute. -/
theorem cliffordMul_comp_self {c : σ → Module.End R M}
    (hc_sq : ∀ i, c i ∘ₗ c i = -1)
    (hc_anti : Pairwise fun i j ↦ c i ∘ₗ c j + c j ∘ₗ c i = 0) :
    cliffordMul c ∘ₗ cliffordMul c = -(LinearMap.mulLeft R (normSq σ R)).rTensor M := by
  refine TensorProduct.ext' fun p m ↦ ?_
  simp only [LinearMap.comp_apply, cliffordMul_tmul, map_sum, LinearMap.neg_apply,
    LinearMap.rTensor_tmul, LinearMap.mulLeft_apply, normSq_def]
  suffices ∀ s : Finset σ,
      ∑ i ∈ s, ∑ j ∈ s, (X j * (X i * p)) ⊗ₜ[R] c j (c i m) =
        -((∑ i ∈ s, X i ^ 2) * p) ⊗ₜ[R] m from this Finset.univ
  intro s
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    simp_rw [Finset.sum_insert ha]
    have hdiag : (X a * (X a * p)) ⊗ₜ[R] c a (c a m) = -((X a ^ 2 * p) ⊗ₜ[R] m) := by
      have hca : c a (c a m) = -m := by simpa using LinearMap.congr_fun (hc_sq a) m
      rw [← mul_assoc, ← sq, hca, TensorProduct.tmul_neg]
    have hoff : ∑ j ∈ s, (X j * (X a * p)) ⊗ₜ[R] c j (c a m) +
        ∑ i ∈ s, (X a * (X i * p)) ⊗ₜ[R] c a (c i m) = 0 := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_eq_zero fun i hi ↦ ?_
      have hanti : c a (c i m) + c i (c a m) = 0 := by
        simpa using LinearMap.congr_fun (hc_anti (fun h : a = i ↦ ha (h ▸ hi))) m
      rw [show X i * (X a * p) = X a * (X i * p) by ring, ← TensorProduct.tmul_add,
        add_comm (c i (c a m)), hanti, TensorProduct.tmul_zero]
    rw [add_mul, TensorProduct.add_tmul, neg_add, ← ih]
    calc
      _ = (X a * (X a * p)) ⊗ₜ[R] c a (c a m) +
          (∑ j ∈ s, (X j * (X a * p)) ⊗ₜ[R] c j (c a m) +
            ∑ i ∈ s, (X a * (X i * p)) ⊗ₜ[R] c a (c i m)) +
          ∑ i ∈ s, ∑ j ∈ s, (X j * (X i * p)) ⊗ₜ[R] c j (c i m) := by
        simp only [Finset.sum_add_distrib]; abel
      _ = _ := by rw [hdiag, hoff, add_zero]

private theorem coeff_normSq_single_two (i : σ) :
    (normSq σ R).coeff (Finsupp.single i 2) = 1 := by
  classical
  have hX2 (k : σ) : (X k : MvPolynomial σ R) ^ 2 = monomial (Finsupp.single k 2) 1 := by
    rw [sq, X, monomial_mul_monomial, one_mul, ← Finsupp.single_add]
  rw [normSq_def, coeff_sum]
  simp_rw [hX2, coeff_monomial]
  rw [Finset.sum_eq_single i (fun k _ hki ↦ ?_) (by simp)]
  · simp
  · rw [ite_eq_right_iff]
    intro hk
    exact (hki (Finsupp.single_left_injective (by decide : (2 : ℕ) ≠ 0) hk)).elim

private theorem coeff_normSq_single_add_single {i j : σ} (hij : i ≠ j) :
    (normSq σ R).coeff (Finsupp.single i 1 + Finsupp.single j 1) = 0 := by
  classical
  have hX2 (k : σ) : (X k : MvPolynomial σ R) ^ 2 = monomial (Finsupp.single k 2) 1 := by
    rw [sq, X, monomial_mul_monomial, one_mul, ← Finsupp.single_add]
  rw [normSq_def, coeff_sum]
  simp_rw [hX2, coeff_monomial]
  refine Finset.sum_eq_zero fun k _ ↦ ?_
  rw [ite_eq_right_iff]
  intro hk
  have hki := DFunLike.congr_fun hk i
  simp only [Finsupp.add_apply, Finsupp.single_apply] at hki
  split_ifs at hki <;> simp_all

/-- **Characterization of `X ∘ₗ X = -r²`**: Clifford coordinate multiplication squares to `-r²` if
and only if each `cᵢ` squares to `-1` and distinct `cᵢ, cⱼ` anticommute. -/
theorem cliffordMul_comp_self_iff {c : σ → Module.End R M} :
    cliffordMul c ∘ₗ cliffordMul c = -(LinearMap.mulLeft R (normSq σ R)).rTensor M ↔
      (∀ i, c i ∘ₗ c i = -1) ∧ Pairwise fun i j ↦ c i ∘ₗ c j + c j ∘ₗ c i = 0 := by
  refine ⟨fun h ↦ ⟨fun i ↦ ?_, fun i j hij ↦ ?_⟩, fun ⟨h1, h2⟩ ↦ cliffordMul_comp_self h1 h2⟩
  · classical
    ext m
    have hm := congrArg (coeffTensor (Finsupp.single i 2))
      (LinearMap.congr_fun h (1 ⊗ₜ[R] m))
    simp only [LinearMap.comp_apply, LinearMap.neg_apply, map_neg,
      LinearMap.rTensor_tmul, LinearMap.mulLeft_apply, mul_one] at hm
    have hs2 : Finsupp.single i 2 - Finsupp.single i 1 = (Finsupp.single i 1 : σ →₀ ℕ) := by
      ext k
      simp only [Finsupp.tsub_apply, Finsupp.single_apply]
      split_ifs <;> omega
    rw [coeffTensor_cliffordMul, Finsupp.support_single i (by decide : (2 : ℕ) ≠ 0),
      Finset.sum_singleton, hs2, coeffTensor_cliffordMul, Finsupp.support_single i one_ne_zero,
      Finset.sum_singleton, tsub_self, coeffTensor_tmul, coeff_one, ite_eq_left rfl, one_smul,
      coeffTensor_tmul, coeff_normSq_single_two, one_smul] at hm
    simpa using hm
  · classical
    ext m
    have hm := congrArg (coeffTensor (Finsupp.single i 1 + Finsupp.single j 1))
      (LinearMap.congr_fun h (1 ⊗ₜ[R] m))
    simp only [LinearMap.comp_apply, LinearMap.neg_apply, map_neg,
      LinearMap.rTensor_tmul, LinearMap.mulLeft_apply, mul_one] at hm
    have hsupp : (Finsupp.single i 1 + Finsupp.single j 1 : σ →₀ ℕ).support = {i, j} := by
      ext k
      simp only [Finsupp.mem_support_iff, Finsupp.add_apply, Finsupp.single_apply,
        Finset.mem_insert, Finset.mem_singleton]
      split_ifs <;> simp_all [eq_comm]
    rw [coeffTensor_cliffordMul, hsupp, Finset.sum_pair hij, add_tsub_cancel_left,
      add_tsub_cancel_right, coeffTensor_cliffordMul, coeffTensor_cliffordMul,
      Finsupp.support_single i one_ne_zero, Finsupp.support_single j one_ne_zero,
      Finset.sum_singleton, Finset.sum_singleton, tsub_self, tsub_self,
      coeffTensor_tmul, coeff_one, ite_eq_left rfl, one_smul, coeffTensor_tmul,
      coeff_normSq_single_add_single hij, zero_smul, neg_zero] at hm
    simpa [LinearMap.add_apply, LinearMap.comp_apply] using hm

/-- **Square of the polynomial Dirac operator**: `D ∘ₗ D = -Δ` when each `cᵢ` squares to `-1` and
distinct `cᵢ, cⱼ` anticommute. -/
theorem cliffordDirac_comp_self {c : σ → Module.End R M}
    (hc_sq : ∀ i, c i ∘ₗ c i = -1)
    (hc_anti : Pairwise fun i j ↦ c i ∘ₗ c j + c j ∘ₗ c i = 0) :
    cliffordDirac c ∘ₗ cliffordDirac c = -(laplacian (R := R) (σ := σ)).rTensor M := by
  refine TensorProduct.ext' fun p m ↦ ?_
  simp only [LinearMap.comp_apply, cliffordDirac_tmul, map_sum, LinearMap.neg_apply,
    LinearMap.rTensor_tmul, laplacian_apply]
  suffices ∀ s : Finset σ,
      ∑ i ∈ s, ∑ j ∈ s, pderiv j (pderiv i p) ⊗ₜ[R] c j (c i m) =
        -(∑ i ∈ s, pderiv i (pderiv i p)) ⊗ₜ[R] m from this Finset.univ
  intro s
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    simp_rw [Finset.sum_insert ha]
    have hdiag : pderiv a (pderiv a p) ⊗ₜ[R] c a (c a m) = -(pderiv a (pderiv a p) ⊗ₜ[R] m) := by
      have hca : c a (c a m) = -m := by simpa using LinearMap.congr_fun (hc_sq a) m
      rw [hca, TensorProduct.tmul_neg]
    have hoff : ∑ j ∈ s, pderiv j (pderiv a p) ⊗ₜ[R] c j (c a m) +
        ∑ i ∈ s, pderiv a (pderiv i p) ⊗ₜ[R] c a (c i m) = 0 := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_eq_zero fun i hi ↦ ?_
      have hanti : c a (c i m) + c i (c a m) = 0 := by
        simpa using LinearMap.congr_fun (hc_anti (fun h : a = i ↦ ha (h ▸ hi))) m
      rw [pderiv_comm i a, ← TensorProduct.tmul_add, add_comm (c i (c a m)), hanti,
        TensorProduct.tmul_zero]
    rw [TensorProduct.add_tmul, neg_add, ← ih]
    calc
      _ = pderiv a (pderiv a p) ⊗ₜ[R] c a (c a m) +
          (∑ j ∈ s, pderiv j (pderiv a p) ⊗ₜ[R] c j (c a m) +
            ∑ i ∈ s, pderiv a (pderiv i p) ⊗ₜ[R] c a (c i m)) +
          ∑ i ∈ s, ∑ j ∈ s, pderiv j (pderiv i p) ⊗ₜ[R] c j (c i m) := by
        simp only [Finset.sum_add_distrib]; abel
      _ = _ := by rw [hdiag, hoff, add_zero]

/-- Every monogenic polynomial is harmonic (`Δ u = 0`). -/
theorem laplacian_rTensor_eq_zero_of_mem_monogenicSubmodule {c : σ → Module.End R M}
    (hc_sq : ∀ i, c i ∘ₗ c i = -1)
    (hc_anti : Pairwise fun i j ↦ c i ∘ₗ c j + c j ∘ₗ c i = 0)
    {k : ℕ} {u : MvPolynomial σ R ⊗[R] M} (hu : u ∈ monogenicSubmodule c k) :
    (laplacian (R := R) (σ := σ)).rTensor M u = 0 := by
  have h := LinearMap.congr_fun (cliffordDirac_comp_self hc_sq hc_anti) u
  rw [LinearMap.comp_apply, hu.2, map_zero, LinearMap.neg_apply] at h
  exact neg_eq_zero.mp h.symm

omit [Fintype σ] in
private theorem cliffordDirac_cliffordMul_offDiag_eq_zero {c : σ → Module.End R M}
    (hc_anti : Pairwise fun i j ↦ c i ∘ₗ c j + c j ∘ₗ c i = 0)
    (p : MvPolynomial σ R) (m : M) {a : σ} {s : Finset σ} (ha : a ∉ s) :
    (∑ j ∈ s, pderiv j (X a * p) ⊗ₜ[R] c j (c a m) +
        ∑ i ∈ s, pderiv a (X i * p) ⊗ₜ[R] c a (c i m)) +
      (∑ j ∈ s, (X j * pderiv a p) ⊗ₜ[R] c j (c a m) +
        ∑ i ∈ s, (X a * pderiv i p) ⊗ₜ[R] c a (c i m)) = 0 := by
  have hs1 : ∑ j ∈ s, pderiv j (X a * p) ⊗ₜ[R] c j (c a m) =
      ∑ j ∈ s, (X a * pderiv j p) ⊗ₜ[R] c j (c a m) :=
    Finset.sum_congr rfl fun j hj ↦ by
      rw [pderiv_mul, pderiv_X_of_ne (fun h : a = j ↦ ha (h ▸ hj)), zero_mul, zero_add]
  have hs2 : ∑ i ∈ s, pderiv a (X i * p) ⊗ₜ[R] c a (c i m) =
      ∑ i ∈ s, (X i * pderiv a p) ⊗ₜ[R] c a (c i m) :=
    Finset.sum_congr rfl fun i hi ↦ by
      rw [pderiv_mul, pderiv_X_of_ne (fun h : i = a ↦ ha (h.symm ▸ hi)), zero_mul, zero_add]
  rw [hs1, hs2]
  have hc1 : ∑ i ∈ s, ((X a * pderiv i p) ⊗ₜ[R] c i (c a m) +
      (X a * pderiv i p) ⊗ₜ[R] c a (c i m)) = 0 :=
    Finset.sum_eq_zero fun i hi ↦ by
      have hanti : c a (c i m) + c i (c a m) = 0 := by
        simpa using LinearMap.congr_fun (hc_anti (fun h : a = i ↦ ha (h ▸ hi))) m
      rw [← TensorProduct.tmul_add, add_comm (c i (c a m)), hanti, TensorProduct.tmul_zero]
  have hc2 : ∑ i ∈ s, ((X i * pderiv a p) ⊗ₜ[R] c a (c i m) +
      (X i * pderiv a p) ⊗ₜ[R] c i (c a m)) = 0 :=
    Finset.sum_eq_zero fun i hi ↦ by
      have hanti : c a (c i m) + c i (c a m) = 0 := by
        simpa using LinearMap.congr_fun (hc_anti (fun h : a = i ↦ ha (h ▸ hi))) m
      rw [← TensorProduct.tmul_add, hanti, TensorProduct.tmul_zero]
  rw [Finset.sum_add_distrib] at hc1 hc2
  calc
    _ = (∑ i ∈ s, (X a * pderiv i p) ⊗ₜ[R] c i (c a m) +
          ∑ i ∈ s, (X a * pderiv i p) ⊗ₜ[R] c a (c i m)) +
        (∑ i ∈ s, (X i * pderiv a p) ⊗ₜ[R] c a (c i m) +
          ∑ i ∈ s, (X i * pderiv a p) ⊗ₜ[R] c i (c a m)) := by abel
    _ = 0 := by rw [hc1, hc2, add_zero]

/-- **Graded anticommutator of `D` and `X`**:
`D ∘ₗ X + X ∘ₗ D = -(2 • E + card σ • id)`, where `E` is the lifted Euler derivation. -/
theorem cliffordDirac_comp_cliffordMul_add_cliffordMul_comp_cliffordDirac
    {c : σ → Module.End R M}
    (hc_sq : ∀ i, c i ∘ₗ c i = -1)
    (hc_anti : Pairwise fun i j ↦ c i ∘ₗ c j + c j ∘ₗ c i = 0) :
    cliffordDirac c ∘ₗ cliffordMul c + cliffordMul c ∘ₗ cliffordDirac c =
      -(2 • (euler (R := R) (σ := σ)).toLinearMap.rTensor M +
        Fintype.card σ • LinearMap.id) := by
  refine TensorProduct.ext' fun p m ↦ ?_
  simp only [LinearMap.add_apply, LinearMap.comp_apply, cliffordMul_tmul, cliffordDirac_tmul,
    map_sum, LinearMap.neg_apply, LinearMap.smul_apply, LinearMap.rTensor_tmul,
    Derivation.coeFn_coe, LinearMap.id_apply, euler_apply_fintype, ← Finset.card_univ]
  suffices ∀ s : Finset σ,
      (∑ i ∈ s, ∑ j ∈ s, pderiv j (X i * p) ⊗ₜ[R] c j (c i m)) +
          (∑ i ∈ s, ∑ j ∈ s, (X j * pderiv i p) ⊗ₜ[R] c j (c i m)) =
        -(2 • ((∑ i ∈ s, X i * pderiv i p) ⊗ₜ[R] m) + s.card • (p ⊗ₜ[R] m)) from
    this Finset.univ
  intro s
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    simp_rw [Finset.sum_insert ha, Finset.card_insert_of_notMem ha, succ_nsmul _ s.card]
    have hdiag : pderiv a (X a * p) ⊗ₜ[R] c a (c a m) +
        (X a * pderiv a p) ⊗ₜ[R] c a (c a m) =
        -(2 • ((X a * pderiv a p) ⊗ₜ[R] m) + p ⊗ₜ[R] m) := by
      have hca : c a (c a m) = -m := by simpa using LinearMap.congr_fun (hc_sq a) m
      rw [pderiv_mul, pderiv_X_self, one_mul, hca, TensorProduct.add_tmul,
        TensorProduct.tmul_neg, TensorProduct.tmul_neg, two_nsmul]
      abel
    calc
      _ = (pderiv a (X a * p) ⊗ₜ[R] c a (c a m) + (X a * pderiv a p) ⊗ₜ[R] c a (c a m)) +
          ((∑ j ∈ s, pderiv j (X a * p) ⊗ₜ[R] c j (c a m) +
              ∑ i ∈ s, pderiv a (X i * p) ⊗ₜ[R] c a (c i m)) +
            (∑ j ∈ s, (X j * pderiv a p) ⊗ₜ[R] c j (c a m) +
              ∑ i ∈ s, (X a * pderiv i p) ⊗ₜ[R] c a (c i m))) +
          ((∑ i ∈ s, ∑ j ∈ s, pderiv j (X i * p) ⊗ₜ[R] c j (c i m)) +
            (∑ i ∈ s, ∑ j ∈ s, (X j * pderiv i p) ⊗ₜ[R] c j (c i m))) := by
        simp only [Finset.sum_add_distrib]; abel
      _ = -(2 • ((X a * pderiv a p + ∑ i ∈ s, X i * pderiv i p) ⊗ₜ[R] m) +
            (s.card • (p ⊗ₜ[R] m) + p ⊗ₜ[R] m)) := by
        rw [hdiag, cliffordDirac_cliffordMul_offDiag_eq_zero hc_anti p m ha, add_zero, ih,
          TensorProduct.add_tmul, smul_add]
        abel

/-- On homogeneous polynomials of degree `k` in `n = Fintype.card σ` variables,
`D (X u) = -X (D u) - (2k + n) • u`. -/
theorem cliffordDirac_cliffordMul_of_mem {c : σ → Module.End R M}
    (hc_sq : ∀ i, c i ∘ₗ c i = -1)
    (hc_anti : Pairwise fun i j ↦ c i ∘ₗ c j + c j ∘ₗ c i = 0)
    {k : ℕ} {u : MvPolynomial σ R ⊗[R] M} (hu : u ∈ homogeneousTensorSubmodule σ R M k) :
    cliffordDirac c (cliffordMul c u) =
      -cliffordMul c (cliffordDirac c u) - (2 * k + Fintype.card σ) • u := by
  have h := LinearMap.congr_fun
    (cliffordDirac_comp_cliffordMul_add_cliffordMul_comp_cliffordDirac hc_sq hc_anti) u
  simp only [LinearMap.add_apply, LinearMap.comp_apply, LinearMap.neg_apply, LinearMap.smul_apply,
    LinearMap.id_apply, euler_rTensor_eq_nsmul hu, ← mul_smul, ← add_smul] at h
  calc
    cliffordDirac c (cliffordMul c u) =
        (cliffordDirac c (cliffordMul c u) + cliffordMul c (cliffordDirac c u)) -
          cliffordMul c (cliffordDirac c u) := by abel
    _ = _ := by rw [h]; abel

/-- On monogenic polynomials of degree `k` in `n = Fintype.card σ` variables,
`D (X u) = -(2k + n) • u`. -/
theorem cliffordDirac_cliffordMul_of_mem_monogenicSubmodule {c : σ → Module.End R M}
    (hc_sq : ∀ i, c i ∘ₗ c i = -1)
    (hc_anti : Pairwise fun i j ↦ c i ∘ₗ c j + c j ∘ₗ c i = 0)
    {k : ℕ} {u : MvPolynomial σ R ⊗[R] M} (hu : u ∈ monogenicSubmodule c k) :
    cliffordDirac c (cliffordMul c u) = -((2 * k + Fintype.card σ) • u) := by
  rw [cliffordDirac_cliffordMul_of_mem hc_sq hc_anti hu.1, hu.2, map_zero, neg_zero, zero_sub]

/-- Action of `D` on odd powers `X ^ (2a + 1)` and positive even powers `X ^ (2a + 2)` applied to a
monogenic polynomial `v` of degree `ℓ`:
`D ((X ^ (2a + 1)) v) = -((2ℓ + n + 2a) • (X ^ (2a)) v)` and
`D ((X ^ (2a + 2)) v) = -((2a + 2) • (X ^ (2a + 1)) v)`. -/
theorem cliffordDirac_cliffordMul_pow_odd_and_even {c : σ → Module.End R M}
    (hc_sq : ∀ i, c i ∘ₗ c i = -1)
    (hc_anti : Pairwise fun i j ↦ c i ∘ₗ c j + c j ∘ₗ c i = 0)
    {ℓ : ℕ} {v : MvPolynomial σ R ⊗[R] M} (hv : v ∈ monogenicSubmodule c ℓ) (a : ℕ) :
    cliffordDirac c ((cliffordMul c ^ (2 * a + 1)) v) =
        -((2 * ℓ + Fintype.card σ + 2 * a) • (cliffordMul c ^ (2 * a)) v) ∧
      cliffordDirac c ((cliffordMul c ^ (2 * a + 2)) v) =
        -((2 * a + 2) • (cliffordMul c ^ (2 * a + 1)) v) := by
  induction a with
  | zero =>
    have h1 : cliffordDirac c ((cliffordMul c ^ 1) v) = -((2 * ℓ + Fintype.card σ) • v) := by
      simpa using cliffordDirac_cliffordMul_of_mem_monogenicSubmodule hc_sq hc_anti hv
    refine ⟨by simpa using h1, ?_⟩
    have hm1 := cliffordMul_pow_mem_homogeneousTensorSubmodule (c := c) 1 hv.1
    rw [show 2 * 0 + 2 = 1 + 1 from rfl, show 2 * 0 + 1 = 1 from rfl,
      pow_succ' (cliffordMul c) 1, mul_apply_eq_comp,
      cliffordDirac_cliffordMul_of_mem hc_sq hc_anti hm1, h1, map_neg, map_nsmul, neg_neg,
      pow_one]
    have hsplit : 2 * (ℓ + 1) + Fintype.card σ = (2 * ℓ + Fintype.card σ) + 2 := by omega
    rw [hsplit, add_smul (2 * ℓ + Fintype.card σ) 2, sub_add_eq_sub_sub, sub_self, zero_sub]
  | succ a ih =>
    obtain ⟨_, iheven⟩ := ih
    have hodd : cliffordDirac c ((cliffordMul c ^ (2 * (a + 1) + 1)) v) =
        -((2 * ℓ + Fintype.card σ + 2 * (a + 1)) • (cliffordMul c ^ (2 * (a + 1))) v) := by
      have hm2 := cliffordMul_pow_mem_homogeneousTensorSubmodule (c := c) (2 * a + 2) hv.1
      have hexp : 2 * (a + 1) + 1 = (2 * a + 2) + 1 := by omega
      rw [hexp, pow_succ' (cliffordMul c) (2 * a + 2), mul_apply_eq_comp,
        cliffordDirac_cliffordMul_of_mem hc_sq hc_anti hm2, iheven, map_neg, map_nsmul, neg_neg,
        ← mul_apply_eq_comp, ← pow_succ' (cliffordMul c) (2 * a + 1),
        show (2 * a + 1) + 1 = 2 * a + 2 from rfl]
      have hsplit : 2 * (ℓ + (2 * a + 2)) + Fintype.card σ =
          (2 * a + 2) + (2 * ℓ + Fintype.card σ + 2 * (a + 1)) := by omega
      rw [hsplit, add_smul (2 * a + 2), sub_add_eq_sub_sub, sub_self, zero_sub,
        show 2 * a + 2 = 2 * (a + 1) by omega]
    refine ⟨hodd, ?_⟩
    have hm3 := cliffordMul_pow_mem_homogeneousTensorSubmodule (c := c) (2 * (a + 1) + 1) hv.1
    have hexp : 2 * (a + 1) + 2 = (2 * (a + 1) + 1) + 1 := by omega
    rw [hexp, pow_succ' (cliffordMul c) (2 * (a + 1) + 1), mul_apply_eq_comp,
      cliffordDirac_cliffordMul_of_mem hc_sq hc_anti hm3, hodd, map_neg, map_nsmul, neg_neg,
      ← mul_apply_eq_comp, ← pow_succ' (cliffordMul c) (2 * (a + 1)),
      show 2 * (a + 1) + 1 + 1 = 2 * (a + 1) + 2 from rfl]
    have hsplit : 2 * (ℓ + (2 * (a + 1) + 1)) + Fintype.card σ =
        (2 * ℓ + Fintype.card σ + 2 * (a + 1)) + (2 * (a + 1) + 2) := by omega
    rw [hsplit, add_smul (2 * ℓ + Fintype.card σ + 2 * (a + 1)), sub_add_eq_sub_sub, sub_self,
      zero_sub]

/-- **Trivial kernel of `D ∘ₗ X`**: when `[Nonempty σ]` and `[HasUniqueDiv M]`, if
`cliffordDirac c (cliffordMul c u) = 0` then `u = 0`. -/
theorem eq_zero_of_cliffordDirac_cliffordMul_eq_zero [Nonempty σ] [HasUniqueDiv M]
    {c : σ → Module.End R M}
    (hc_sq : ∀ i, c i ∘ₗ c i = -1)
    (hc_anti : Pairwise fun i j ↦ c i ∘ₗ c j + c j ∘ₗ c i = 0)
    {u : MvPolynomial σ R ⊗[R] M} (h : cliffordDirac c (cliffordMul c u) = 0) :
    u = 0 := by
  refine eq_zero_of_forall_homogeneousComponentTensor_eq_zero fun k ↦ ?_
  set uk := homogeneousComponentTensor k u
  have huk_mem : uk ∈ homogeneousTensorSubmodule σ R M k := homogeneousComponentTensor_mem k u
  have hDX : cliffordDirac c (cliffordMul c uk) = 0 := by
    rw [← homogeneousComponentTensor_succ_cliffordMul, ← homogeneousComponentTensor_cliffordDirac,
      h, map_zero]
  have hXD : cliffordMul c (cliffordDirac c uk) = -((2 * k + Fintype.card σ) • uk) := by
    have hrel := cliffordDirac_cliffordMul_of_mem hc_sq hc_anti huk_mem
    rw [hDX, eq_comm, sub_eq_zero] at hrel
    exact neg_eq_iff_eq_neg.mp hrel
  have hXXD := congrArg (cliffordMul c) hXD
  have hXX := LinearMap.congr_fun (cliffordMul_comp_self hc_sq hc_anti) (cliffordDirac c uk)
  simp only [LinearMap.comp_apply, LinearMap.neg_apply] at hXX
  rw [hXX, map_neg, map_nsmul] at hXXD
  have hr2 : (LinearMap.mulLeft R (normSq σ R)).rTensor M (cliffordDirac c uk) =
      (2 * k + Fintype.card σ) • cliffordMul c uk := neg_injective hXXD
  have hΔ := congrArg ((laplacian (R := R) (σ := σ)).rTensor M) hr2
  have hDD := LinearMap.congr_fun (cliffordDirac_comp_self hc_sq hc_anti) (cliffordMul c uk)
  simp only [LinearMap.comp_apply, LinearMap.neg_apply, hDX, map_zero] at hDD
  rw [map_nsmul, neg_eq_zero.mp hDD.symm, smul_zero] at hΔ
  have hDuk : cliffordDirac c uk = 0 := eq_zero_of_laplacian_normSq_mul_rTensor_eq_zero hΔ
  rw [hDuk, map_zero, eq_comm, neg_eq_zero] at hXD
  have hpos : 2 * k + Fintype.card σ ≠ 0 := by
    have : 0 < Fintype.card σ := Fintype.card_pos
    omega
  exact IsSMulRegular.nat_of_hasUniqueDiv hpos (by simpa using hXD)

/-- **Directness of the Clifford Fischer decomposition** (operator form): under `[HasUniqueDiv M]`,
`ker (cliffordDirac c)` and `range (cliffordMul c)` have trivial intersection. -/
theorem disjoint_ker_cliffordDirac_range_cliffordMul [HasUniqueDiv M]
    {c : σ → Module.End R M}
    (hc_sq : ∀ i, c i ∘ₗ c i = -1)
    (hc_anti : Pairwise fun i j ↦ c i ∘ₗ c j + c j ∘ₗ c i = 0) :
    Disjoint (LinearMap.ker (cliffordDirac c)) (LinearMap.range (cliffordMul c)) := by
  rcases isEmpty_or_nonempty σ with _ | _
  · simp
  rw [Submodule.disjoint_def]
  rintro _ hD ⟨w, rfl⟩
  rw [eq_zero_of_cliffordDirac_cliffordMul_eq_zero hc_sq hc_anti hD, map_zero]

/-- **Directness of the Clifford Fischer decomposition** (graded form): under `[HasUniqueDiv M]`,
`monogenicSubmodule c (k + 1)` and `(homogeneousTensorSubmodule σ R M k).map (cliffordMul c)` are
disjoint. -/
theorem disjoint_monogenicSubmodule_map_cliffordMul [HasUniqueDiv M]
    {c : σ → Module.End R M}
    (hc_sq : ∀ i, c i ∘ₗ c i = -1)
    (hc_anti : Pairwise fun i j ↦ c i ∘ₗ c j + c j ∘ₗ c i = 0) (k : ℕ) :
    Disjoint (monogenicSubmodule c (k + 1))
      ((homogeneousTensorSubmodule σ R M k).map (cliffordMul c)) :=
  ((disjoint_ker_cliffordDirac_range_cliffordMul hc_sq hc_anti).mono_left
    (monogenicSubmodule_le_ker_cliffordDirac c (k + 1))).mono_right LinearMap.map_le_range

end Ring

section Rational

variable {σ R M : Type*} [CommRing R] [Algebra ℚ R] [AddCommGroup M] [Module R M] [Fintype σ]

private theorem inv_natCast_smul_nsmul {N : Type*} [AddCommGroup N] [Module R N]
    {n : ℕ} (hn : n ≠ 0) (x : N) :
    algebraMap ℚ R (n : ℚ)⁻¹ • (n • x) = x := by
  rw [← Nat.cast_smul_eq_nsmul R, smul_smul, ← map_natCast (algebraMap ℚ R), ← map_mul,
    inv_mul_cancel₀ (Nat.cast_ne_zero.mpr hn), map_one, one_smul]

private theorem exists_cliffordDirac_cliffordMul_of_mem_iSup [Nonempty σ]
    {c : σ → Module.End R M}
    (hc_sq : ∀ i, c i ∘ₗ c i = -1)
    (hc_anti : Pairwise fun i j ↦ c i ∘ₗ c j + c j ∘ₗ c i = 0) {k : ℕ}
    {v : MvPolynomial σ R ⊗[R] M}
    (hv : v ∈ ⨆ j ≤ k, (monogenicSubmodule c (k - j)).map (cliffordMul c ^ j)) :
    ∃ w ∈ homogeneousTensorSubmodule σ R M k, cliffordDirac c (cliffordMul c w) = v := by
  let S : Submodule R (MvPolynomial σ R ⊗[R] M) :=
    { carrier := {v | ∃ w ∈ homogeneousTensorSubmodule σ R M k,
        cliffordDirac c (cliffordMul c w) = v}
      zero_mem' := ⟨0, Submodule.zero_mem _, by simp⟩
      add_mem' := fun ⟨w₁, hw₁, heq₁⟩ ⟨w₂, hw₂, heq₂⟩ ↦
        ⟨w₁ + w₂, Submodule.add_mem _ hw₁ hw₂, by simp [heq₁, heq₂]⟩
      smul_mem' := fun r _ ⟨w, hw, heq⟩ ↦
        ⟨r • w, Submodule.smul_mem _ r hw, by simp [heq]⟩ }
  suffices (⨆ j ≤ k, (monogenicSubmodule c (k - j)).map (cliffordMul c ^ j)) ≤ S from this hv
  refine iSup₂_le fun j hj ↦ ?_
  rintro _ ⟨m, hm, rfl⟩
  have hmem : (cliffordMul c ^ j) m ∈ homogeneousTensorSubmodule σ R M k := by
    simpa [Nat.sub_add_cancel hj] using cliffordMul_pow_mem_homogeneousTensorSubmodule j hm.1
  rcases Nat.even_or_odd' j with ⟨a, rfl | rfl⟩
  · set q : ℕ := 2 * (k - 2 * a) + Fintype.card σ + 2 * a
    have hq : q ≠ 0 := by
      have : 0 < Fintype.card σ := Fintype.card_pos
      omega
    refine ⟨-(algebraMap ℚ R (q : ℚ)⁻¹ • (cliffordMul c ^ (2 * a)) m),
      Submodule.neg_mem _ (Submodule.smul_mem _ _ hmem), ?_⟩
    have hpow : cliffordMul c ((cliffordMul c ^ (2 * a)) m) =
        (cliffordMul c ^ (2 * a + 1)) m := by
      rw [pow_succ' (cliffordMul c) (2 * a), mul_apply_eq_comp]
    rw [map_neg, map_smul, map_neg, map_smul, hpow,
      (cliffordDirac_cliffordMul_pow_odd_and_even hc_sq hc_anti hm a).1, smul_neg, neg_neg]
    exact inv_natCast_smul_nsmul hq _
  · set q : ℕ := 2 * a + 2
    have hq : q ≠ 0 := by omega
    refine ⟨-(algebraMap ℚ R (q : ℚ)⁻¹ • (cliffordMul c ^ (2 * a + 1)) m),
      Submodule.neg_mem _ (Submodule.smul_mem _ _ hmem), ?_⟩
    have hpow : cliffordMul c ((cliffordMul c ^ (2 * a + 1)) m) =
        (cliffordMul c ^ (2 * a + 2)) m := by
      rw [show 2 * a + 2 = (2 * a + 1) + 1 by omega,
        pow_succ' (cliffordMul c) (2 * a + 1), mul_apply_eq_comp]
    rw [map_neg, map_smul, map_neg, map_smul, hpow,
      (cliffordDirac_cliffordMul_pow_odd_and_even hc_sq hc_anti hm a).2, smul_neg, neg_neg]
    exact inv_natCast_smul_nsmul hq _

/-- **The full monogenic Fischer expansion**: over any commutative `ℚ`-algebra `R`, every
homogeneous `M`-valued polynomial of degree `k` decomposes into a sum of `X ^ j` applied to
monogenic polynomials of degree `k - j`. -/
theorem homogeneousTensorSubmodule_eq_iSup_map_cliffordMul_pow
    {c : σ → Module.End R M}
    (hc_sq : ∀ i, c i ∘ₗ c i = -1)
    (hc_anti : Pairwise fun i j ↦ c i ∘ₗ c j + c j ∘ₗ c i = 0) (k : ℕ) :
    homogeneousTensorSubmodule σ R M k =
      ⨆ j ≤ k, (monogenicSubmodule c (k - j)).map (cliffordMul c ^ j) := by
  apply le_antisymm
  · induction k using Nat.strong_induction_on with
    | _ k ih =>
    rcases k with _ | k
    · refine fun u hu ↦ Submodule.mem_iSup_of_mem 0 (Submodule.mem_iSup_of_mem (Nat.zero_le 0) ?_)
      exact ⟨u, by rwa [Nat.sub_zero, monogenicSubmodule_zero], by simp⟩
    rcases isEmpty_or_nonempty σ with _ | _
    · simp
    intro u hu
    have hDu : cliffordDirac c u ∈
        ⨆ j ≤ k, (monogenicSubmodule c (k - j)).map (cliffordMul c ^ j) :=
      ih k (Nat.lt_succ_self k) (cliffordDirac_mem_homogeneousTensorSubmodule hu)
    obtain ⟨w, hw, hDXw⟩ := exists_cliffordDirac_cliffordMul_of_mem_iSup hc_sq hc_anti hDu
    have hm : u - cliffordMul c w ∈ monogenicSubmodule c (k + 1) :=
      ⟨Submodule.sub_mem _ hu (cliffordMul_mem_homogeneousTensorSubmodule hw), by simp [hDXw]⟩
    have hm0 : u - cliffordMul c w ∈
        (monogenicSubmodule c (k + 1 - 0)).map (cliffordMul c ^ 0) :=
      ⟨u - cliffordMul c w, hm, by simp⟩
    have hm_iSup : u - cliffordMul c w ∈
        ⨆ j ≤ k + 1, (monogenicSubmodule c (k + 1 - j)).map (cliffordMul c ^ j) :=
      Submodule.mem_iSup_of_mem 0 (Submodule.mem_iSup_of_mem (Nat.zero_le _) hm0)
    have hw_iSup : cliffordMul c w ∈
        ⨆ j ≤ k + 1, (monogenicSubmodule c (k + 1 - j)).map (cliffordMul c ^ j) := by
      have hmap : cliffordMul c w ∈
          (⨆ j ≤ k, (monogenicSubmodule c (k - j)).map (cliffordMul c ^ j)).map
            (cliffordMul c) := ⟨w, ih k (Nat.lt_succ_self k) hw, rfl⟩
      suffices (⨆ j ≤ k, (monogenicSubmodule c (k - j)).map (cliffordMul c ^ j)).map
          (cliffordMul c) ≤
        ⨆ j ≤ k + 1, (monogenicSubmodule c (k + 1 - j)).map (cliffordMul c ^ j) from this hmap
      rw [Submodule.map_iSup]
      refine iSup_le fun j ↦ ?_
      rw [Submodule.map_iSup]
      refine iSup_le fun hj ↦ ?_
      rw [← Submodule.map_comp]
      have hpow : cliffordMul c ∘ₗ cliffordMul c ^ j = cliffordMul c ^ (j + 1) := by
        rw [pow_succ']; rfl
      exact le_iSup₂_of_le (j + 1) (Nat.add_le_add_right hj 1)
        (by rw [Nat.succ_sub_succ_eq_sub, hpow])
    simpa using Submodule.add_mem _ hm_iSup hw_iSup
  · refine iSup₂_le fun j hj ↦ ?_
    rintro _ ⟨m, hm, rfl⟩
    simpa [Nat.sub_add_cancel hj] using cliffordMul_pow_mem_homogeneousTensorSubmodule j hm.1

/-- **Surjectivity of `D ∘ₗ X`** on `homogeneousTensorSubmodule σ R M k`: over any commutative
`ℚ`-algebra `R` with `[Nonempty σ]`, every homogeneous `M`-valued polynomial `v` of degree `k` can
be written as `D (X w)` for a unique homogeneous `M`-valued polynomial `w` of degree `k`. -/
theorem exists_cliffordDirac_cliffordMul_eq [Nonempty σ]
    {c : σ → Module.End R M}
    (hc_sq : ∀ i, c i ∘ₗ c i = -1)
    (hc_anti : Pairwise fun i j ↦ c i ∘ₗ c j + c j ∘ₗ c i = 0)
    {k : ℕ} {v : MvPolynomial σ R ⊗[R] M} (hv : v ∈ homogeneousTensorSubmodule σ R M k) :
    ∃ w ∈ homogeneousTensorSubmodule σ R M k, cliffordDirac c (cliffordMul c w) = v :=
  exists_cliffordDirac_cliffordMul_of_mem_iSup hc_sq hc_anti
    (homogeneousTensorSubmodule_eq_iSup_map_cliffordMul_pow hc_sq hc_anti k ▸ hv)

/-- **The Clifford Fischer decomposition**: over any commutative `ℚ`-algebra `R`, every homogeneous
`M`-valued polynomial of degree `k + 1` is the sum of a monogenic polynomial of degree `k + 1` and
`cliffordMul c` applied to a homogeneous polynomial of degree `k`. Directness is given by
`MvPolynomial.disjoint_monogenicSubmodule_map_cliffordMul`. -/
theorem monogenicSubmodule_sup_map_cliffordMul
    {c : σ → Module.End R M}
    (hc_sq : ∀ i, c i ∘ₗ c i = -1)
    (hc_anti : Pairwise fun i j ↦ c i ∘ₗ c j + c j ∘ₗ c i = 0) (k : ℕ) :
    monogenicSubmodule c (k + 1) ⊔
        (homogeneousTensorSubmodule σ R M k).map (cliffordMul c) =
      homogeneousTensorSubmodule σ R M (k + 1) := by
  rcases isEmpty_or_nonempty σ with _ | _
  · simp
  refine le_antisymm (sup_le (monogenicSubmodule_le_homogeneousTensorSubmodule c (k + 1)) ?_)
    fun u hu ↦ ?_
  · rintro _ ⟨w, hw, rfl⟩
    exact cliffordMul_mem_homogeneousTensorSubmodule hw
  · have hDu : cliffordDirac c u ∈ homogeneousTensorSubmodule σ R M k := by
      simpa using cliffordDirac_mem_homogeneousTensorSubmodule (c := c) hu
    obtain ⟨w, hw, hDXw⟩ := exists_cliffordDirac_cliffordMul_eq hc_sq hc_anti hDu
    refine Submodule.mem_sup.mpr ⟨u - cliffordMul c w,
      ⟨Submodule.sub_mem _ hu (cliffordMul_mem_homogeneousTensorSubmodule hw), by simp [hDXw]⟩,
      cliffordMul c w, ⟨w, hw, rfl⟩, sub_add_cancel u _⟩

private theorem cliffordDirac_smul_monomial_add_single (c : σ → Module.End R M) (i₀ : σ)
    (s : σ →₀ ℕ) (m' : M) [DecidableEq σ] :
    cliffordDirac c
        (algebraMap ℚ R ((s i₀ + 1 : ℕ) : ℚ)⁻¹ •
          (monomial (s + Finsupp.single i₀ 1) (1 : R) ⊗ₜ[R] m')) =
      monomial s (1 : R) ⊗ₜ[R] c i₀ m' +
        algebraMap ℚ R ((s i₀ + 1 : ℕ) : ℚ)⁻¹ •
          ∑ j ∈ Finset.univ.erase i₀,
            pderiv j (monomial (s + Finsupp.single i₀ 1) (1 : R)) ⊗ₜ[R] c j m' := by
  set s' : σ →₀ ℕ := s + Finsupp.single i₀ 1
  rw [map_smul, cliffordDirac_tmul, ← Finset.add_sum_erase _ _ (Finset.mem_univ i₀), smul_add]
  congr 1
  rw [pderiv_monomial, one_mul, add_tsub_cancel_right]
  have hcast : ((s' i₀ : ℕ) : R) = ((s i₀ + 1 : ℕ) : R) := by simp [s']
  have hmon : monomial s ((s' i₀ : ℕ) : R) = (s i₀ + 1) • monomial s (1 : R) := by
    rw [hcast, smul_monomial, nsmul_eq_mul, mul_one]
  rw [hmon, ← TensorProduct.smul_tmul',
    inv_natCast_smul_nsmul (Nat.succ_ne_zero _) (monomial s (1 : R) ⊗ₜ[R] c i₀ m')]

private def diracPreimageSubmodule (c : σ → Module.End R M) (P : Submodule R M) (i₀ : σ)
    (d : ℕ) : Submodule R (MvPolynomial σ R ⊗[R] M) where
  carrier := {v | ∃ u ∈ homogeneousTensorSubmodule σ R M d,
    (∀ t, coeffTensor t u ∈ P) ∧ (∀ t, t i₀ = 0 → coeffTensor t u = 0) ∧ cliffordDirac c u = v}
  zero_mem' := ⟨0, Submodule.zero_mem _, fun _ ↦ by simp, fun _ _ ↦ by simp, by simp⟩
  add_mem' := fun ⟨u₁, hu₁, hP₁, h0₁, h₁⟩ ⟨u₂, hu₂, hP₂, h0₂, h₂⟩ ↦
    ⟨u₁ + u₂, Submodule.add_mem _ hu₁ hu₂,
      fun t ↦ by rw [map_add]; exact P.add_mem (hP₁ t) (hP₂ t),
      fun t ht ↦ by simp [h0₁ t ht, h0₂ t ht], by simp [h₁, h₂]⟩
  smul_mem' := fun r _ ⟨u, hu, hP, h0, h⟩ ↦
    ⟨r • u, Submodule.smul_mem _ r hu,
      fun t ↦ by rw [map_smul]; exact P.smul_mem r (hP t),
      fun t ht ↦ by simp [h0 t ht], by simp [h]⟩

private theorem monomial_tmul_mem_diracPreimageSubmodule {c : σ → Module.End R M}
    {P Q : Submodule R M} {i₀ : σ}
    (hi₀ : ∀ m ∈ Q, ∃ m' ∈ P, c i₀ m' = m)
    (hc : ∀ j, Set.MapsTo (c j) P Q) (k : ℕ) :
    ∀ q : ℕ, ∀ (s : σ →₀ ℕ) (m : M), m ∈ Q → s.degree = k → k - s i₀ = q →
      monomial s (1 : R) ⊗ₜ[R] m ∈ diracPreimageSubmodule c P i₀ (k + 1) := by
  classical
  set S := diracPreimageSubmodule c P i₀ (k + 1)
  intro q
  induction q using Nat.strong_induction_on with
  | _ q ih =>
  intro s m hmQ hsdeg hsq
  obtain ⟨m', hm'P, rfl⟩ := hi₀ m hmQ
  set s' : σ →₀ ℕ := s + Finsupp.single i₀ 1
  have hs'deg : s'.degree = k + 1 := by
    rw [map_add Finsupp.degree, hsdeg, Finsupp.degree_single]
  set u₀ : MvPolynomial σ R ⊗[R] M :=
    algebraMap ℚ R ((s i₀ + 1 : ℕ) : ℚ)⁻¹ • (monomial s' (1 : R) ⊗ₜ[R] m')
  have hu₀_mem : u₀ ∈ homogeneousTensorSubmodule σ R M (k + 1) :=
    Submodule.smul_mem _ _
      (tmul_mem_homogeneousTensorSubmodule (isHomogeneous_monomial (1 : R) hs'deg) m')
  have hu₀_P : ∀ t, coeffTensor t u₀ ∈ P := fun t ↦ by
    rw [map_smul, coeffTensor_tmul]
    exact P.smul_mem _ (P.smul_mem _ hm'P)
  have hu₀_zero : ∀ t, t i₀ = 0 → coeffTensor t u₀ = 0 := fun t ht ↦ by
    have hne : s' ≠ t := fun h ↦ by simp [s', ← h] at ht
    rw [map_smul, coeffTensor_tmul, coeff_monomial,
      ite_eq_right_iff.mpr fun h ↦ (hne h).elim, zero_smul, smul_zero]
  have hrest : algebraMap ℚ R ((s i₀ + 1 : ℕ) : ℚ)⁻¹ •
      ∑ j ∈ Finset.univ.erase i₀, pderiv j (monomial s' (1 : R)) ⊗ₜ[R] c j m' ∈ S := by
    refine S.smul_mem _ (S.sum_mem fun j hj ↦ ?_)
    have hne : j ≠ i₀ := (Finset.mem_erase.mp hj).1
    have hs'j : s' j = s j := by
      rw [Finsupp.add_apply, Finsupp.single_eq_of_ne' hne.symm, add_zero]
    by_cases hsj : s j = 0
    · rw [pderiv_monomial, hs'j, hsj, Nat.cast_zero, mul_zero, monomial_zero,
        TensorProduct.zero_tmul]
      exact S.zero_mem
    · obtain ⟨htdeg, hti₀, _⟩ := degree_add_single_sub_single s hne hsj
      have hmon : monomial (s' - Finsupp.single j 1) ((s' j : ℕ) : R) =
          ((s' j : ℕ) : R) • monomial (s' - Finsupp.single j 1) (1 : R) := by
        rw [smul_monomial, smul_eq_mul, mul_one]
      rw [pderiv_monomial, one_mul, hmon, ← TensorProduct.smul_tmul']
      exact S.smul_mem _ (ih (k - (s i₀ + 1)) (by omega) (s' - Finsupp.single j 1) (c j m')
        (hc j hm'P) (htdeg.trans hsdeg) (by rw [hti₀]))
  obtain ⟨u_rest, hu_rest_mem, hu_rest_P, hu_rest_zero, hu_rest_eq⟩ := hrest
  exact ⟨u₀ - u_rest, Submodule.sub_mem _ hu₀_mem hu_rest_mem,
    fun t ↦ by rw [map_sub]; exact P.sub_mem (hu₀_P t) (hu_rest_P t),
    fun t ht ↦ by simp [hu₀_zero t ht, hu_rest_zero t ht],
    by rw [map_sub, cliffordDirac_smul_monomial_add_single, hu_rest_eq, add_sub_cancel_right]⟩

/-- **Submodule-valued polynomial Cauchy-Kowalewskaya for `cliffordDirac`**: over any commutative
`ℚ`-algebra `R`, if every `c j` maps `P` into `Q` and `c i₀` maps `P` surjectively onto `Q` for
some coordinate `i₀ : σ`, then every homogeneous degree-`k` polynomial `v` with coefficients in `Q`
is `cliffordDirac c u` for a homogeneous degree-`(k + 1)` polynomial `u` with coefficients in `P`
vanishing along `X i₀ = 0`. No Clifford or anticommutation relations on `c` are required. -/
theorem exists_cliffordDirac_eq_of_mapsTo {c : σ → Module.End R M}
    {P Q : Submodule R M} {i₀ : σ}
    (hi₀ : ∀ m ∈ Q, ∃ m' ∈ P, c i₀ m' = m)
    (hc : ∀ j, Set.MapsTo (c j) P Q)
    {k : ℕ} {v : MvPolynomial σ R ⊗[R] M}
    (hv : v ∈ homogeneousTensorSubmodule σ R M k)
    (hvQ : ∀ s, coeffTensor s v ∈ Q) :
    ∃ u ∈ homogeneousTensorSubmodule σ R M (k + 1),
      (∀ s, coeffTensor s u ∈ P) ∧ (∀ s, s i₀ = 0 → coeffTensor s u = 0) ∧
        cliffordDirac c u = v := by
  obtain ⟨I, hdeg, -, hsum⟩ := exists_finset_sum_monomial_tmul_coeffTensor hv
  rw [← hsum]
  exact (diracPreimageSubmodule c P i₀ (k + 1)).sum_mem fun s hs ↦
    monomial_tmul_mem_diracPreimageSubmodule hi₀ hc k (k - s i₀) s (coeffTensor s v)
      (hvQ s) (hdeg s hs) rfl

/-- **Polynomial Cauchy-Kowalewskaya for `cliffordDirac`**: over any commutative `ℚ`-algebra `R`,
if `c i₀` is surjective for at least one coordinate `i₀ : σ`, then `cliffordDirac c` maps
`homogeneousTensorSubmodule σ R M (k + 1)` surjectively onto `homogeneousTensorSubmodule σ R M k`
by polynomials vanishing along `X i₀ = 0`. No Clifford or anticommutation relations on `c` are
required. -/
theorem exists_cliffordDirac_eq_of_surjective {c : σ → Module.End R M} {i₀ : σ}
    (hc : Function.Surjective (c i₀)) {k : ℕ} {v : MvPolynomial σ R ⊗[R] M}
    (hv : v ∈ homogeneousTensorSubmodule σ R M k) :
    ∃ u ∈ homogeneousTensorSubmodule σ R M (k + 1),
      (∀ s, s i₀ = 0 → coeffTensor s u = 0) ∧ cliffordDirac c u = v := by
  obtain ⟨u, hu, -, hu0, hDu⟩ := exists_cliffordDirac_eq_of_mapsTo (P := ⊤) (Q := ⊤)
    (fun m _ ↦ let ⟨m', hm'⟩ := hc m; ⟨m', trivial, hm'⟩) (fun _ _ _ ↦ trivial) hv
    fun _ ↦ trivial
  exact ⟨u, hu, hu0, hDu⟩

/-- **Cauchy-Kowalewskaya coefficient surjectivity**: over any commutative `ℚ`-algebra `R`, if
`c i₀` is surjective and `i₁ ≠ i₀`, then evaluating the `(single i₁ k)`-monomial coefficient maps
`monogenicSubmodule c k` surjectively onto `M`. -/
theorem coeffTensor_single_monogenicSubmodule_surjective {c : σ → Module.End R M}
    {i₀ i₁ : σ} (hne : i₁ ≠ i₀) (hc : Function.Surjective (c i₀)) (k : ℕ) :
    Function.Surjective
      (fun u : monogenicSubmodule c k ↦ coeffTensor (Finsupp.single i₁ k) u.1) := fun m ↦ by
  rcases k with _ | k
  · refine ⟨⟨1 ⊗ₜ[R] m, ?_⟩, by simp⟩
    rw [monogenicSubmodule_zero]
    exact tmul_mem_homogeneousTensorSubmodule (isHomogeneous_one σ R) m
  · set w : MvPolynomial σ R ⊗[R] M :=
      monomial (Finsupp.single i₁ (k + 1)) (1 : R) ⊗ₜ[R] m
    have hw : w ∈ homogeneousTensorSubmodule σ R M (k + 1) :=
      tmul_mem_homogeneousTensorSubmodule
        (isHomogeneous_monomial (1 : R) (Finsupp.degree_single i₁ (k + 1))) m
    obtain ⟨u, hu, hu0, hDu⟩ := exists_cliffordDirac_eq_of_surjective hc
      (by simpa using cliffordDirac_mem_homogeneousTensorSubmodule (c := c) hw)
    refine ⟨⟨w - u, mem_monogenicSubmodule.mpr ⟨Submodule.sub_mem _ hw hu, by simp [hDu]⟩⟩, ?_⟩
    dsimp only
    classical
    rw [map_sub, hu0 _ (Finsupp.single_eq_of_ne' hne), sub_zero, coeffTensor_tmul]
    simp

end Rational

section Field

variable {σ K M : Type*} [Field K] [CharZero K] [AddCommGroup M] [Module K M] [Fintype σ]

/-- Over a field `K` and a finite `K`-vector space `M`, the submodule of degree-`k` monogenic
polynomials in finitely many variables is finite-dimensional. -/
instance [Module.Finite K M] (c : σ → Module.End K M) (k : ℕ) :
    FiniteDimensional K (monogenicSubmodule c k) :=
  Submodule.finiteDimensional_of_le (monogenicSubmodule_le_homogeneousTensorSubmodule c k)

/-- **Rank relation for monogenic polynomials**: over a field of characteristic zero, if `M` is
finite-dimensional and `c i₀` is surjective for some coordinate `i₀ : σ`, then
`finrank K (monogenicSubmodule c (k + 1)) + finrank K (P_k(M)) = finrank K (P_{k+1}(M))`. -/
theorem finrank_monogenicSubmodule_add_finrank [Module.Finite K M]
    {c : σ → Module.End K M} {i₀ : σ} (hc : Function.Surjective (c i₀)) (k : ℕ) :
    Module.finrank K (monogenicSubmodule c (k + 1)) +
        Module.finrank K (homogeneousTensorSubmodule σ K M k) =
      Module.finrank K (homogeneousTensorSubmodule σ K M (k + 1)) := by
  let Dk : homogeneousTensorSubmodule σ K M (k + 1) →ₗ[K] homogeneousTensorSubmodule σ K M k :=
    { toFun := fun u ↦ ⟨cliffordDirac c u.1,
        by simpa using cliffordDirac_mem_homogeneousTensorSubmodule (c := c) u.2⟩
      map_add' := fun u v ↦ Subtype.ext (map_add (cliffordDirac c) u.1 v.1)
      map_smul' := fun r u ↦ Subtype.ext (map_smul (cliffordDirac c) r u.1) }
  have hsurj : Function.Surjective Dk := fun ⟨v, hv⟩ ↦ by
    obtain ⟨u, hu, -, hDu⟩ := exists_cliffordDirac_eq_of_surjective hc hv
    exact ⟨⟨u, hu⟩, Subtype.ext hDu⟩
  have hker : LinearMap.ker Dk =
      (monogenicSubmodule c (k + 1)).comap (homogeneousTensorSubmodule σ K M (k + 1)).subtype := by
    ext ⟨u, hu⟩
    simp [Dk, mem_monogenicSubmodule, hu]
  have hker_eq : Module.finrank K (LinearMap.ker Dk) =
      Module.finrank K (monogenicSubmodule c (k + 1)) := by
    rw [hker]
    exact (Submodule.comapSubtypeEquivOfLe
      (monogenicSubmodule_le_homogeneousTensorSubmodule c (k + 1))).finrank_eq
  have h := LinearMap.finrank_range_add_finrank_ker (K := K)
    (V := homogeneousTensorSubmodule σ K M (k + 1))
    (V₂ := homogeneousTensorSubmodule σ K M k) Dk
  rw [LinearMap.range_eq_top.mpr hsurj, finrank_top, hker_eq, add_comm] at h
  exact h

/-- **Dimension of the degree-`k` monogenic submodule**: over a field of characteristic zero, if
`M` is finite-dimensional and `c i₀` is surjective for some coordinate `i₀ : σ`, then
`finrank K (monogenicSubmodule c k) = (Fintype.card σ - 1).multichoose k * finrank K M`. -/
theorem finrank_monogenicSubmodule [Module.Finite K M]
    {c : σ → Module.End K M} {i₀ : σ} (hc : Function.Surjective (c i₀)) (k : ℕ) :
    Module.finrank K (monogenicSubmodule c k) =
      (Fintype.card σ - 1).multichoose k * Module.finrank K M := by
  have : Nonempty σ := ⟨i₀⟩
  rcases k with _ | k
  · rw [monogenicSubmodule_zero, ← (homogeneousTensorZeroEquiv σ K M).finrank_eq,
      Nat.multichoose_zero_right, one_mul]
  · have h := finrank_monogenicSubmodule_add_finrank hc k
    rw [finrank_homogeneousTensorSubmodule, finrank_homogeneousTensorSubmodule] at h
    obtain ⟨m, hm⟩ : ∃ m, Fintype.card σ = m + 1 :=
      ⟨Fintype.card σ - 1, (Nat.sub_add_cancel Fintype.card_pos).symm⟩
    rw [hm, Nat.add_sub_cancel]
    rw [hm, Nat.multichoose_succ_succ, add_mul] at h
    exact Nat.add_right_cancel h

/-- **Unconditional dimension of the degree-`k` monogenic submodule** when `c i₀` is bijective:
over a field of characteristic zero, `finrank K (monogenicSubmodule c k) =
  (Fintype.card σ - 1).multichoose k * finrank K M` without assuming `M` is finite-dimensional. -/
theorem finrank_monogenicSubmodule_of_bijective
    {c : σ → Module.End K M} {i₀ : σ} (hc : Function.Bijective (c i₀)) (k : ℕ) :
    Module.finrank K (monogenicSubmodule c k) =
      (Fintype.card σ - 1).multichoose k * Module.finrank K M := by
  by_cases hfin : Module.Finite K M
  · exact finrank_monogenicSubmodule hc.2 k
  have : HasUniqueDiv M := @HasUniqueDiv.of_module_rat M _ (Module.compHom M (algebraMap ℚ K))
  rw [Module.finrank_of_not_finite hfin, mul_zero]
  rcases k with _ | k
  · rw [monogenicSubmodule_zero, ← (homogeneousTensorZeroEquiv σ K M).finrank_eq]
    exact Module.finrank_of_not_finite hfin
  by_cases hsub : Subsingleton σ
  · have hbot : monogenicSubmodule c (k + 1) = ⊥ :=
      monogenicSubmodule_succ_eq_bot_of_subsingleton
        (fun i ↦ Subsingleton.elim i i₀ ▸ hc.1) k
    rw [hbot, finrank_bot]
  · obtain ⟨i₁, hi₁⟩ : ∃ i₁ : σ, i₁ ≠ i₀ := by
      by_contra! h
      exact hsub ⟨fun a b ↦ (h a).trans (h b).symm⟩
    let f : monogenicSubmodule c (k + 1) →ₗ[K] M :=
      (coeffTensor (Finsupp.single i₁ (k + 1))).comp (monogenicSubmodule c (k + 1)).subtype
    have hsurj : Function.Surjective f :=
      coeffTensor_single_monogenicSubmodule_surjective hi₁ hc.2 (k + 1)
    have hinf : Cardinal.aleph0 ≤ Module.rank K M :=
      not_lt.mp (mt Module.rank_lt_aleph0_iff.mp hfin)
    rw [Module.finrank, Cardinal.toNat_eq_zero]
    refine Or.inr ?_
    simpa using (Cardinal.lift_le.mpr hinf).trans (f.lift_rank_le_of_surjective hsurj)

end Field

end MvPolynomial
