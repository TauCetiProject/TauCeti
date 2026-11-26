/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.MvPolynomial.TensorModule
import TauCeti.Algebra.Module.Rat
import TauCeti.Data.Finsupp.Weight
import TauCeti.RingTheory.TensorProduct.MvPolynomial

/-!
# Monogenic multivariate polynomials and the Clifford Fischer decomposition

For an `R`-module `M` and `c : σ → Module.End R M` (`[Fintype σ]`), `MvPolynomial.cliffordMul c`
(`p ⊗ₜ m ↦ ∑ᵢ (Xᵢ * p) ⊗ₜ cᵢ m`) and `MvPolynomial.cliffordDirac c`
(`p ⊗ₜ m ↦ ∑ᵢ (∂p/∂Xᵢ) ⊗ₜ cᵢ m`) act on `MvPolynomial σ R ⊗[R] M`, cutting out the degree-`k`
**monogenic submodule** `MvPolynomial.monogenicSubmodule c k = P_k(M) ⊓ ker D`. Under the
Riemannian Clifford relations `cᵢ ∘ₗ cᵢ = -1` and `cᵢ ∘ₗ cⱼ + cⱼ ∘ₗ cᵢ = 0` (`i ≠ j`), `X² = -r²`,
`D² = -Δ`, and `D ∘ₗ X + X ∘ₗ D = -(2 • E + card σ • id)`, giving directness under
`[HasUniqueDiv M]` and (over any commutative `ℚ`-algebra) the **Clifford Fischer decomposition**
and full monogenic expansion. Over a characteristic-zero field `K`, polynomial
Cauchy-Kowalewskaya along a surjective `c i₀` for finite-dimensional `M` (or a bijective `c i₀`
unconditionally) gives the rank `(card σ - 1).multichoose k * finrank K M`.

## Main definitions

* `MvPolynomial.cliffordMul`, `MvPolynomial.cliffordDirac`, and `MvPolynomial.monogenicSubmodule`.

## Main results

* `MvPolynomial.cliffordMul_comp_self_iff`, `MvPolynomial.cliffordDirac_comp_self`, and
  `MvPolynomial.cliffordDirac_comp_cliffordMul_add_cliffordMul_comp_cliffordDirac`.
* `MvPolynomial.disjoint_monogenicSubmodule_map_cliffordMul`,
  `MvPolynomial.monogenicSubmodule_sup_map_cliffordMul`, and
  `MvPolynomial.homogeneousTensorSubmodule_eq_iSup_map_cliffordMul_pow`.
* `MvPolynomial.exists_cliffordDirac_eq_of_mapsTo`,
  `MvPolynomial.coeffTensor_single_monogenicSubmodule_surjective`,
  `MvPolynomial.finrank_monogenicSubmodule`, and
  `MvPolynomial.finrank_monogenicSubmodule_of_bijective`.

## References

* R. Delanghe, F. Sommen, and V. Souček, *Clifford Algebra and Spinor-Valued Functions* (1992).
* H. B. Lawson and M.-L. Michelsohn, *Spin Geometry*, Princeton Math. Series 38 (1989).
-/

public section

open scoped TensorProduct

namespace MvPolynomial

section Semiring

variable {σ R M : Type*} [CommSemiring R] [AddCommMonoid M] [Module R M] [Fintype σ]

/-- **Clifford coordinate multiplication** `p ⊗ₜ m ↦ ∑ᵢ (Xᵢ * p) ⊗ₜ cᵢ m`. -/
noncomputable def cliffordMul (c : σ → Module.End R M) : Module.End R (MvPolynomial σ R ⊗[R] M) :=
  ∑ i : σ, TensorProduct.map (LinearMap.mulLeft R (X i)) (c i)

/-- **The polynomial Dirac operator** `p ⊗ₜ m ↦ ∑ᵢ (∂p/∂Xᵢ) ⊗ₜ cᵢ m`. -/
noncomputable def cliffordDirac (c : σ → Module.End R M) :
    Module.End R (MvPolynomial σ R ⊗[R] M) :=
  ∑ i : σ, TensorProduct.map (pderiv i).toLinearMap (c i)

/-- Degree-`k` **monogenic polynomials**: `homogeneousTensorSubmodule σ R M k ⊓ ker D`. -/
noncomputable def monogenicSubmodule (c : σ → Module.End R M) (k : ℕ) :
    Submodule R (MvPolynomial σ R ⊗[R] M) :=
  homogeneousTensorSubmodule σ R M k ⊓ LinearMap.ker (cliffordDirac c)

@[simp] theorem cliffordMul_tmul (c : σ → Module.End R M) (p : MvPolynomial σ R) (m : M) :
    cliffordMul c (p ⊗ₜ[R] m) = ∑ i : σ, (X i * p) ⊗ₜ[R] c i m := by
  simp [cliffordMul, LinearMap.sum_apply]

@[simp] theorem cliffordDirac_tmul (c : σ → Module.End R M) (p : MvPolynomial σ R) (m : M) :
    cliffordDirac c (p ⊗ₜ[R] m) = ∑ i : σ, pderiv i p ⊗ₜ[R] c i m := by
  simp [cliffordDirac, LinearMap.sum_apply]

@[simp] theorem cliffordMul_eq_zero_of_isEmpty [IsEmpty σ] (c : σ → Module.End R M) :
    cliffordMul c = 0 := by simp [cliffordMul]

@[simp] theorem cliffordDirac_eq_zero_of_isEmpty [IsEmpty σ] (c : σ → Module.End R M) :
    cliffordDirac c = 0 := by simp [cliffordDirac]

@[simp] theorem mem_monogenicSubmodule {c : σ → Module.End R M} {k : ℕ}
    {u : MvPolynomial σ R ⊗[R] M} :
    u ∈ monogenicSubmodule c k ↔
      u ∈ homogeneousTensorSubmodule σ R M k ∧ cliffordDirac c u = 0 := Iff.rfl

theorem monogenicSubmodule_le_homogeneousTensorSubmodule (c : σ → Module.End R M) (k : ℕ) :
    monogenicSubmodule c k ≤ homogeneousTensorSubmodule σ R M k := inf_le_left

theorem monogenicSubmodule_le_ker_cliffordDirac (c : σ → Module.End R M) (k : ℕ) :
    monogenicSubmodule c k ≤ LinearMap.ker (cliffordDirac c) := inf_le_right

theorem coeffTensor_cliffordMul (c : σ → Module.End R M) (s : σ →₀ ℕ)
    (u : MvPolynomial σ R ⊗[R] M) :
    coeffTensor s (cliffordMul c u) =
      ∑ i ∈ s.support, c i (coeffTensor (s - Finsupp.single i 1) u) := by
  classical
  induction u using TensorProduct.inductionOn with
  | tmul p m =>
    rw [cliffordMul_tmul, map_sum]
    simp_rw [coeffTensor_tmul, coeff_X_mul', ite_smul, zero_smul, ← Finset.sum_filter]
    exact Finset.sum_congr (by ext i; simp) fun i _ ↦ (map_smul (c i) _ _).symm
  | add x y hx hy => simp_rw [map_add, hx, hy, ← Finset.sum_add_distrib]

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
  | add x y hx hy => simp_rw [map_add, hx, hy, smul_add, ← Finset.sum_add_distrib]

/-- If `c i₀` is injective and `[IsCancelAdd M]`, then `cliffordMul c` is injective. -/
theorem cliffordMul_injective [IsCancelAdd M] {c : σ → Module.End R M} {i₀ : σ}
    (hc : Function.Injective (c i₀)) : Function.Injective (cliffordMul c) := by
  classical
  intro u v huv
  refine ext_lid_rTensor_lcoeff fun s ↦ ?_
  rw [← coeffTensor_apply, ← coeffTensor_apply]
  suffices ∀ n : ℕ, ∀ t : σ →₀ ℕ, t.degree - t i₀ = n → coeffTensor t u = coeffTensor t v from
    this _ s rfl
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro t htn
  have hsum := congrArg (coeffTensor (t + Finsupp.single i₀ 1)) huv
  have hmem : i₀ ∈ (t + Finsupp.single i₀ 1).support := by simp
  rw [coeffTensor_cliffordMul, coeffTensor_cliffordMul, ← Finset.add_sum_erase _ _ hmem,
    ← Finset.add_sum_erase _ _ hmem] at hsum
  have hrest : ∀ i ∈ (t + Finsupp.single i₀ 1).support.erase i₀,
      c i (coeffTensor (t + Finsupp.single i₀ 1 - Finsupp.single i 1) u) =
        c i (coeffTensor (t + Finsupp.single i₀ 1 - Finsupp.single i 1) v) := fun i hi ↦ by
    obtain ⟨hne, hisupp⟩ := Finset.mem_erase.mp hi
    have hti : t i ≠ 0 := by
      rwa [Finsupp.mem_support_iff, Finsupp.add_apply, Finsupp.single_eq_of_ne' hne.symm,
        add_zero] at hisupp
    have hdeg : (t + Finsupp.single i₀ 1 - Finsupp.single i 1).degree = t.degree := by
      rw [Finsupp.degree_tsub ((Finsupp.single_le_iff.mpr (Nat.pos_of_ne_zero hti)).trans
        le_self_add), map_add, Finsupp.degree_single, Finsupp.degree_single, add_tsub_cancel_right]
    have hi₀_val : (t + Finsupp.single i₀ 1 - Finsupp.single i 1 : σ →₀ ℕ) i₀ = t i₀ + 1 := by
      simp [Finsupp.single_eq_of_ne' hne]
    have := Finsupp.lt_degree_of_ne_zero hne hti
    rw [ih _ (by omega) _ rfl]
  rw [Finset.sum_congr rfl hrest, add_right_cancel_iff, add_tsub_cancel_right] at hsum
  exact hc hsum

theorem cliffordMul_mem_homogeneousTensorSubmodule {c : σ → Module.End R M} {k : ℕ}
    {u : MvPolynomial σ R ⊗[R] M} (hu : u ∈ homogeneousTensorSubmodule σ R M k) :
    cliffordMul c u ∈ homogeneousTensorSubmodule σ R M (k + 1) :=
  homogeneousTensorSubmodule_inductionOn hu
    (fun hp m ↦ by
      rw [cliffordMul_tmul]
      exact Submodule.sum_mem _ fun i _ ↦ tmul_mem_homogeneousTensorSubmodule
        (by simpa [add_comm] using (isHomogeneous_X R i).mul hp) (c i m))
    fun hx hy ↦ by rw [map_add]; exact Submodule.add_mem _ hx hy

theorem cliffordMul_pow_mem_homogeneousTensorSubmodule {c : σ → Module.End R M} {k : ℕ} (j : ℕ)
    {u : MvPolynomial σ R ⊗[R] M} (hu : u ∈ homogeneousTensorSubmodule σ R M k) :
    (cliffordMul c ^ j) u ∈ homogeneousTensorSubmodule σ R M (k + j) := by
  induction j with
  | zero => simpa using hu
  | succ j ih =>
    rw [pow_succ', mul_apply_eq_comp, ← add_assoc]
    exact cliffordMul_mem_homogeneousTensorSubmodule ih

theorem cliffordDirac_mem_homogeneousTensorSubmodule {c : σ → Module.End R M} {k : ℕ}
    {u : MvPolynomial σ R ⊗[R] M} (hu : u ∈ homogeneousTensorSubmodule σ R M k) :
    cliffordDirac c u ∈ homogeneousTensorSubmodule σ R M (k - 1) :=
  homogeneousTensorSubmodule_inductionOn hu
    (fun hp m ↦ by
      rw [cliffordDirac_tmul]
      exact Submodule.sum_mem _ fun i _ ↦ tmul_mem_homogeneousTensorSubmodule hp.pderiv (c i m))
    fun hx hy ↦ by rw [map_add]; exact Submodule.add_mem _ hx hy

theorem cliffordDirac_eq_zero_of_mem_zero {c : σ → Module.End R M}
    {u : MvPolynomial σ R ⊗[R] M} (hu : u ∈ homogeneousTensorSubmodule σ R M 0) :
    cliffordDirac c u = 0 := by
  have hu0 := congrArg Subtype.val ((homogeneousTensorZeroEquiv σ R M).apply_symm_apply ⟨u, hu⟩)
  dsimp only at hu0; rw [← hu0]; simp

@[simp] theorem monogenicSubmodule_zero (c : σ → Module.End R M) :
    monogenicSubmodule c 0 = homogeneousTensorSubmodule σ R M 0 :=
  inf_eq_left.mpr fun _ ↦ cliffordDirac_eq_zero_of_mem_zero

@[simp] theorem monogenicSubmodule_succ_eq_bot_of_isEmpty [IsEmpty σ] (c : σ → Module.End R M)
    (k : ℕ) : monogenicSubmodule c (k + 1) = ⊥ := by simp [monogenicSubmodule]

/-- For `[Subsingleton σ]`, `[HasUniqueDiv M]`, and injective `c i`, degree `k + 1` vanishes. -/
theorem monogenicSubmodule_succ_eq_bot_of_subsingleton [Subsingleton σ] [HasUniqueDiv M]
    {c : σ → Module.End R M} (hc : ∀ i, Function.Injective (c i)) (k : ℕ) :
    monogenicSubmodule c (k + 1) = ⊥ := by
  rcases isEmpty_or_nonempty σ with _ | ⟨⟨i₀⟩⟩
  · exact monogenicSubmodule_succ_eq_bot_of_isEmpty c k
  have huniv : (Finset.univ : Finset σ) = {i₀} :=
    Finset.eq_singleton_iff_unique_mem.mpr ⟨Finset.mem_univ i₀, fun j _ ↦ Subsingleton.elim j i₀⟩
  refine eq_bot_iff.mpr fun u ⟨hu, hDu⟩ ↦
    (Submodule.mem_bot R).mpr (ext_lid_rTensor_lcoeff fun s ↦ ?_)
  rw [← coeffTensor_apply, map_zero, map_zero]
  rcases eq_or_ne s 0 with rfl | hs0
  · exact mem_homogeneousTensorSubmodule_iff_coeffTensor.mp hu 0 (by simp)
  · have hsi : s i₀ ≠ 0 := fun h ↦ hs0 <| by ext j; rwa [Subsingleton.elim j i₀]
    have hD := congrArg (coeffTensor (s - Finsupp.single i₀ 1)) hDu
    rw [map_zero, coeffTensor_cliffordDirac, huniv, Finset.sum_singleton,
      tsub_add_cancel_of_le (Finsupp.single_le_iff.mpr (Nat.pos_of_ne_zero hsi))] at hD
    exact hc i₀ (by simpa using hD)

@[simp] theorem homogeneousComponentTensor_zero_cliffordMul (c : σ → Module.End R M)
    (u : MvPolynomial σ R ⊗[R] M) : homogeneousComponentTensor 0 (cliffordMul c u) = 0 := by
  obtain ⟨N, hN⟩ := exists_sum_homogeneousComponentTensor_eq u
  conv_lhs => rw [← hN]
  simp only [map_sum]
  exact Finset.sum_eq_zero fun j _ ↦ homogeneousComponentTensor_eq_zero_of_ne
    (cliffordMul_mem_homogeneousTensorSubmodule (homogeneousComponentTensor_mem j u))
    (Nat.zero_ne_add_one j)

@[simp] theorem homogeneousComponentTensor_succ_cliffordMul (c : σ → Module.End R M) (k : ℕ)
    (u : MvPolynomial σ R ⊗[R] M) :
    homogeneousComponentTensor (k + 1) (cliffordMul c u) =
      cliffordMul c (homogeneousComponentTensor k u) := by
  obtain ⟨N, hkN, hN⟩ := exists_sum_homogeneousComponentTensor_eq_of_le u (k + 1)
  have hmem (j : ℕ) :=
    cliffordMul_mem_homogeneousTensorSubmodule (c := c) (homogeneousComponentTensor_mem j u)
  conv_lhs => rw [← hN]
  simp only [map_sum]
  rw [Finset.sum_eq_single_of_mem k (Finset.mem_range.mpr hkN),
    homogeneousComponentTensor_eq_self (hmem k)]
  exact fun j _ hj ↦ homogeneousComponentTensor_eq_zero_of_ne (hmem j) (by omega)

@[simp] theorem homogeneousComponentTensor_cliffordDirac (c : σ → Module.End R M) (k : ℕ)
    (u : MvPolynomial σ R ⊗[R] M) :
    homogeneousComponentTensor k (cliffordDirac c u) =
      cliffordDirac c (homogeneousComponentTensor (k + 1) u) := by
  obtain ⟨N, hkN, hN⟩ := exists_sum_homogeneousComponentTensor_eq_of_le u (k + 2)
  have hmem (j : ℕ) : cliffordDirac c (homogeneousComponentTensor (j + 1) u) ∈
      homogeneousTensorSubmodule σ R M j := by
    simpa using cliffordDirac_mem_homogeneousTensorSubmodule
      (homogeneousComponentTensor_mem (j + 1) u)
  conv_lhs => rw [← hN]
  simp only [map_sum]
  rw [Finset.sum_eq_single_of_mem (k + 1) (Finset.mem_range.mpr hkN),
    homogeneousComponentTensor_eq_self (hmem k)]
  rintro (_ | j) _ hj
  · rw [cliffordDirac_eq_zero_of_mem_zero (homogeneousComponentTensor_mem 0 u), map_zero]
  · exact homogeneousComponentTensor_eq_zero_of_ne (hmem j) (by omega)

end Semiring

section Ring

variable {σ R M : Type*} [CommRing R] [AddCommGroup M] [Module R M] [Fintype σ]

omit [Fintype σ] in
private theorem sum_sum_tmul_of_clifford {c : σ → Module.End R M} (hc_sq : ∀ i, c i ∘ₗ c i = -1)
    (hc_anti : Pairwise fun i j ↦ c i ∘ₗ c j + c j ∘ₗ c i = 0)
    (F : σ → σ → MvPolynomial σ R) (hF : ∀ ⦃i j⦄, i ≠ j → F i j = F j i) (m : M) (s : Finset σ) :
    ∑ i ∈ s, ∑ j ∈ s, F j i ⊗ₜ[R] c j (c i m) = -(∑ i ∈ s, F i i) ⊗ₜ[R] m := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    simp_rw [Finset.sum_insert ha]
    have hca : c a (c a m) = -m := by simpa using LinearMap.congr_fun (hc_sq a) m
    have hoff : ∑ j ∈ s, F j a ⊗ₜ[R] c j (c a m) + ∑ i ∈ s, F a i ⊗ₜ[R] c a (c i m) = 0 := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_eq_zero fun i hi ↦ ?_
      have hne : a ≠ i := fun h ↦ ha (h ▸ hi)
      have hanti : c a (c i m) + c i (c a m) = 0 := by
        simpa using LinearMap.congr_fun (hc_anti hne) m
      rw [hF hne.symm, ← TensorProduct.tmul_add, add_comm (c i (c a m)), hanti,
        TensorProduct.tmul_zero]
    rw [TensorProduct.add_tmul, neg_add, ← ih]
    calc
      _ = F a a ⊗ₜ[R] c a (c a m) +
          (∑ j ∈ s, F j a ⊗ₜ[R] c j (c a m) + ∑ i ∈ s, F a i ⊗ₜ[R] c a (c i m)) +
          ∑ i ∈ s, ∑ j ∈ s, F j i ⊗ₜ[R] c j (c i m) := by simp only [Finset.sum_add_distrib]; abel
      _ = _ := by rw [hca, TensorProduct.tmul_neg, hoff, add_zero]

/-- **Square of Clifford coordinate multiplication**: `X ∘ₗ X = -r²`. -/
theorem cliffordMul_comp_self {c : σ → Module.End R M} (hc_sq : ∀ i, c i ∘ₗ c i = -1)
    (hc_anti : Pairwise fun i j ↦ c i ∘ₗ c j + c j ∘ₗ c i = 0) :
    cliffordMul c ∘ₗ cliffordMul c = -(LinearMap.mulLeft R (normSq σ R)).rTensor M := by
  refine TensorProduct.ext' fun p m ↦ ?_
  simp only [LinearMap.comp_apply, cliffordMul_tmul, map_sum, LinearMap.neg_apply,
    LinearMap.rTensor_tmul, LinearMap.mulLeft_apply, normSq_def]
  rw [sum_sum_tmul_of_clifford hc_sq hc_anti (fun j i ↦ X j * (X i * p))
    (fun _ _ _ ↦ mul_left_comm _ _ _) m Finset.univ]
  simp_rw [← mul_assoc, ← sq, ← Finset.sum_mul]

/-- **Characterization of `X ∘ₗ X = -r²`** via the Riemannian Clifford relations. -/
theorem cliffordMul_comp_self_iff {c : σ → Module.End R M} :
    cliffordMul c ∘ₗ cliffordMul c = -(LinearMap.mulLeft R (normSq σ R)).rTensor M ↔
      (∀ i, c i ∘ₗ c i = -1) ∧ Pairwise fun i j ↦ c i ∘ₗ c j + c j ∘ₗ c i = 0 := by
  refine ⟨fun h ↦ ?_, fun ⟨h1, h2⟩ ↦ cliffordMul_comp_self h1 h2⟩
  classical
  have hm (s : σ →₀ ℕ) (m : M) : coeffTensor s (cliffordMul c (cliffordMul c (1 ⊗ₜ[R] m))) =
      -((normSq σ R).coeff s • m) := by
    simpa [LinearMap.comp_apply] using
      congrArg (coeffTensor s) (LinearMap.congr_fun h (1 ⊗ₜ[R] m))
  refine ⟨fun i ↦ LinearMap.ext fun m ↦ ?_, fun i j hij ↦ LinearMap.ext fun m ↦ ?_⟩
  · have hmi := hm (Finsupp.single i 2) m
    have hs2 : Finsupp.single i 2 - Finsupp.single i 1 = (Finsupp.single i 1 : σ →₀ ℕ) := by
      ext k; simp only [Finsupp.tsub_apply, Finsupp.single_apply]; split_ifs <;> omega
    have hc2 : (normSq σ R).coeff (Finsupp.single i 2) = 1 := by
      rw [coeff_normSq, Finset.sum_eq_single i (fun k _ hki ↦ ite_eq_right_iff.mpr fun hk ↦
        (hki (Finsupp.single_left_injective (by decide : (2 : ℕ) ≠ 0) hk)).elim) (by simp)]
      simp
    rw [coeffTensor_cliffordMul, Finsupp.support_single i (by decide : (2 : ℕ) ≠ 0),
      Finset.sum_singleton, hs2, coeffTensor_cliffordMul,
      Finsupp.support_single i one_ne_zero, Finset.sum_singleton, tsub_self, hc2] at hmi
    simpa using hmi
  · have hmij := hm (Finsupp.single i 1 + Finsupp.single j 1) m
    have hsupp : (Finsupp.single i 1 + Finsupp.single j 1 : σ →₀ ℕ).support = {i, j} := by
      ext k; simp only [Finsupp.mem_support_iff, Finsupp.add_apply, Finsupp.single_apply,
        Finset.mem_insert, Finset.mem_singleton]; split_ifs <;> simp_all [eq_comm]
    have hc0 : (normSq σ R).coeff (Finsupp.single i 1 + Finsupp.single j 1) = 0 := by
      rw [coeff_normSq]
      refine Finset.sum_eq_zero fun k _ ↦ ite_eq_right_iff.mpr fun hk ↦ ?_
      have hki := DFunLike.congr_fun hk i
      simp only [Finsupp.add_apply, Finsupp.single_apply] at hki; split_ifs at hki <;> simp_all
    rw [coeffTensor_cliffordMul, hsupp, Finset.sum_pair hij, add_tsub_cancel_left,
      add_tsub_cancel_right, coeffTensor_cliffordMul, coeffTensor_cliffordMul,
      Finsupp.support_single i one_ne_zero, Finsupp.support_single j one_ne_zero,
      Finset.sum_singleton, Finset.sum_singleton, tsub_self, tsub_self, hc0] at hmij
    simpa [LinearMap.add_apply, LinearMap.comp_apply] using hmij

/-- **Square of the polynomial Dirac operator**: `D ∘ₗ D = -Δ`. -/
theorem cliffordDirac_comp_self {c : σ → Module.End R M} (hc_sq : ∀ i, c i ∘ₗ c i = -1)
    (hc_anti : Pairwise fun i j ↦ c i ∘ₗ c j + c j ∘ₗ c i = 0) :
    cliffordDirac c ∘ₗ cliffordDirac c = -(laplacian (R := R) (σ := σ)).rTensor M := by
  refine TensorProduct.ext' fun p m ↦ ?_
  simp only [LinearMap.comp_apply, cliffordDirac_tmul, map_sum, LinearMap.neg_apply,
    LinearMap.rTensor_tmul, laplacian_apply]
  rw [sum_sum_tmul_of_clifford hc_sq hc_anti (fun j i ↦ pderiv j (pderiv i p))
    (fun i j _ ↦ pderiv_comm i j p) m Finset.univ]

theorem laplacian_rTensor_eq_zero_of_mem_monogenicSubmodule {c : σ → Module.End R M}
    (hc_sq : ∀ i, c i ∘ₗ c i = -1) (hc_anti : Pairwise fun i j ↦ c i ∘ₗ c j + c j ∘ₗ c i = 0)
    {k : ℕ} {u : MvPolynomial σ R ⊗[R] M} (hu : u ∈ monogenicSubmodule c k) :
    (laplacian (R := R) (σ := σ)).rTensor M u = 0 := by
  have h := LinearMap.congr_fun (cliffordDirac_comp_self hc_sq hc_anti) u
  rw [LinearMap.comp_apply, hu.2, map_zero, LinearMap.neg_apply] at h
  exact neg_eq_zero.mp h.symm

/-- **Graded anticommutator of `D` and `X`**: `D ∘ₗ X + X ∘ₗ D = -(2 • E + card σ • id)`. -/
theorem cliffordDirac_comp_cliffordMul_add_cliffordMul_comp_cliffordDirac {c : σ → Module.End R M}
    (hc_sq : ∀ i, c i ∘ₗ c i = -1) (hc_anti : Pairwise fun i j ↦ c i ∘ₗ c j + c j ∘ₗ c i = 0) :
    cliffordDirac c ∘ₗ cliffordMul c + cliffordMul c ∘ₗ cliffordDirac c =
      -(2 • (euler (R := R) (σ := σ)).toLinearMap.rTensor M + Fintype.card σ • LinearMap.id) := by
  refine TensorProduct.ext' fun p m ↦ ?_
  simp only [LinearMap.add_apply, LinearMap.comp_apply, cliffordMul_tmul, cliffordDirac_tmul,
    map_sum, LinearMap.neg_apply, LinearMap.smul_apply, LinearMap.rTensor_tmul,
    Derivation.coeFn_coe, LinearMap.id_apply, euler_apply_fintype, ← Finset.sum_add_distrib,
    ← TensorProduct.add_tmul]
  rw [sum_sum_tmul_of_clifford hc_sq hc_anti
    (fun j i ↦ pderiv j (X i * p) + X j * pderiv i p) (fun i j hij ↦ ?_) m Finset.univ]
  · have hdiag : ∑ i : σ, (pderiv i (X i * p) + X i * pderiv i p) =
        2 • ∑ i : σ, X i * pderiv i p + Fintype.card σ • p := by
      rw [two_nsmul, ← Finset.sum_add_distrib, ← Finset.card_univ, ← Finset.sum_const p,
        ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun i _ ↦ by simp; ring
    rw [hdiag, TensorProduct.add_tmul, TensorProduct.smul_tmul', TensorProduct.smul_tmul']
  · rw [pderiv_mul, pderiv_X_of_ne hij.symm, pderiv_mul, pderiv_X_of_ne hij]; simp [add_comm]

theorem cliffordDirac_cliffordMul_of_mem {c : σ → Module.End R M} (hc_sq : ∀ i, c i ∘ₗ c i = -1)
    (hc_anti : Pairwise fun i j ↦ c i ∘ₗ c j + c j ∘ₗ c i = 0)
    {k : ℕ} {u : MvPolynomial σ R ⊗[R] M} (hu : u ∈ homogeneousTensorSubmodule σ R M k) :
    cliffordDirac c (cliffordMul c u) =
      -cliffordMul c (cliffordDirac c u) - (2 * k + Fintype.card σ) • u := by
  have h := LinearMap.congr_fun
    (cliffordDirac_comp_cliffordMul_add_cliffordMul_comp_cliffordDirac hc_sq hc_anti) u
  simp only [LinearMap.add_apply, LinearMap.comp_apply, LinearMap.neg_apply, LinearMap.smul_apply,
    LinearMap.id_apply, euler_rTensor_eq_nsmul hu, ← mul_smul, ← add_smul] at h
  rw [← add_sub_cancel_right (cliffordDirac c (cliffordMul c u))
    (cliffordMul c (cliffordDirac c u)), h]; abel

theorem cliffordDirac_cliffordMul_of_mem_monogenicSubmodule {c : σ → Module.End R M}
    (hc_sq : ∀ i, c i ∘ₗ c i = -1) (hc_anti : Pairwise fun i j ↦ c i ∘ₗ c j + c j ∘ₗ c i = 0)
    {k : ℕ} {u : MvPolynomial σ R ⊗[R] M} (hu : u ∈ monogenicSubmodule c k) :
    cliffordDirac c (cliffordMul c u) = -((2 * k + Fintype.card σ) • u) := by
  rw [cliffordDirac_cliffordMul_of_mem hc_sq hc_anti hu.1, hu.2, map_zero, neg_zero, zero_sub]

private theorem cliffordDirac_cliffordMul_pow_succ {c : σ → Module.End R M}
    (hc_sq : ∀ i, c i ∘ₗ c i = -1) (hc_anti : Pairwise fun i j ↦ c i ∘ₗ c j + c j ∘ₗ c i = 0)
    {ℓ d A B : ℕ} {v w : MvPolynomial σ R ⊗[R] M} (hv : v ∈ homogeneousTensorSubmodule σ R M ℓ)
    (hd : cliffordDirac c ((cliffordMul c ^ d) v) = -(A • w))
    (hw : cliffordMul c w = (cliffordMul c ^ d) v) (hAB : 2 * (ℓ + d) + Fintype.card σ = A + B) :
    cliffordDirac c ((cliffordMul c ^ (d + 1)) v) = -(B • (cliffordMul c ^ d) v) := by
  rw [pow_succ' (cliffordMul c) d, mul_apply_eq_comp,
    cliffordDirac_cliffordMul_of_mem hc_sq hc_anti
      (cliffordMul_pow_mem_homogeneousTensorSubmodule d hv),
    hd, map_neg, map_nsmul, neg_neg, hw, hAB, add_smul, sub_add_eq_sub_sub, sub_self, zero_sub]

/-- **Action of `cliffordDirac` on odd and even powers of `cliffordMul`** applied to a degree-`ℓ`
monogenic polynomial `v` (`a : ℕ`): `D (X^(2a + 1) v) = -(2ℓ + card σ + 2a) • X^(2a) v` and
`D (X^(2a + 2) v) = -(2a + 2) • X^(2a + 1) v`. When `σ` is nonempty, both scalar factors are
positive, allowing `D ∘ₗ X` to be inverted on each monogenic Fischer summand `X^j M_ℓ` over a
`ℚ`-algebra. -/
theorem cliffordDirac_cliffordMul_pow_odd_and_even {c : σ → Module.End R M}
    (hc_sq : ∀ i, c i ∘ₗ c i = -1) (hc_anti : Pairwise fun i j ↦ c i ∘ₗ c j + c j ∘ₗ c i = 0)
    {ℓ : ℕ} {v : MvPolynomial σ R ⊗[R] M} (hv : v ∈ monogenicSubmodule c ℓ) (a : ℕ) :
    cliffordDirac c ((cliffordMul c ^ (2 * a + 1)) v) =
        -((2 * ℓ + Fintype.card σ + 2 * a) • (cliffordMul c ^ (2 * a)) v) ∧
      cliffordDirac c ((cliffordMul c ^ (2 * a + 2)) v) =
        -((2 * a + 2) • (cliffordMul c ^ (2 * a + 1)) v) := by
  induction a with
  | zero =>
    have h1 : cliffordDirac c ((cliffordMul c ^ 1) v) =
        -((2 * ℓ + Fintype.card σ) • (cliffordMul c ^ 0) v) := by
      simpa using cliffordDirac_cliffordMul_of_mem_monogenicSubmodule hc_sq hc_anti hv
    exact ⟨h1, cliffordDirac_cliffordMul_pow_succ hc_sq hc_anti hv.1 h1 (by simp) (by omega)⟩
  | succ a ih =>
    have h2 : 2 * (a + 1) = (2 * a + 1) + 1 := by omega
    have hodd : cliffordDirac c ((cliffordMul c ^ (2 * (a + 1) + 1)) v) =
        -((2 * ℓ + Fintype.card σ + 2 * (a + 1)) • (cliffordMul c ^ (2 * (a + 1))) v) :=
      cliffordDirac_cliffordMul_pow_succ hc_sq hc_anti hv.1 ih.2
        (by rw [h2, pow_succ' (cliffordMul c) (2 * a + 1), mul_apply_eq_comp]) (by omega)
    exact ⟨hodd, cliffordDirac_cliffordMul_pow_succ hc_sq hc_anti hv.1 hodd
      (by rw [pow_succ' (cliffordMul c) (2 * (a + 1)), mul_apply_eq_comp]) (by omega)⟩

/-- **Trivial kernel of `D ∘ₗ X`** under `[Nonempty σ]` and `[HasUniqueDiv M]`. -/
theorem eq_zero_of_cliffordDirac_cliffordMul_eq_zero [Nonempty σ] [HasUniqueDiv M]
    {c : σ → Module.End R M} (hc_sq : ∀ i, c i ∘ₗ c i = -1)
    (hc_anti : Pairwise fun i j ↦ c i ∘ₗ c j + c j ∘ₗ c i = 0)
    {u : MvPolynomial σ R ⊗[R] M} (h : cliffordDirac c (cliffordMul c u) = 0) : u = 0 := by
  refine eq_zero_of_forall_homogeneousComponentTensor_eq_zero fun k ↦ ?_
  set uk := homogeneousComponentTensor k u
  have hDX : cliffordDirac c (cliffordMul c uk) = 0 := by
    rw [← homogeneousComponentTensor_succ_cliffordMul, ← homogeneousComponentTensor_cliffordDirac,
      h, map_zero]
  have hXD : cliffordMul c (cliffordDirac c uk) = -((2 * k + Fintype.card σ) • uk) := by
    have hrel := cliffordDirac_cliffordMul_of_mem hc_sq hc_anti (homogeneousComponentTensor_mem k u)
    rw [hDX, eq_comm, sub_eq_zero] at hrel; exact neg_eq_iff_eq_neg.mp hrel
  have hXXD := congrArg (cliffordMul c) hXD
  have hXX := LinearMap.congr_fun (cliffordMul_comp_self hc_sq hc_anti) (cliffordDirac c uk)
  simp only [LinearMap.comp_apply, LinearMap.neg_apply] at hXX
  rw [hXX, map_neg, map_nsmul] at hXXD
  have hΔ := congrArg ((laplacian (R := R) (σ := σ)).rTensor M) (neg_injective hXXD)
  have hDD := LinearMap.congr_fun (cliffordDirac_comp_self hc_sq hc_anti) (cliffordMul c uk)
  simp only [LinearMap.comp_apply, LinearMap.neg_apply, hDX, map_zero] at hDD
  rw [map_nsmul, neg_eq_zero.mp hDD.symm, smul_zero] at hΔ
  rw [eq_zero_of_laplacian_normSq_mul_rTensor_eq_zero hΔ, map_zero, eq_comm, neg_eq_zero] at hXD
  have hpos : 2 * k + Fintype.card σ ≠ 0 := by have := Fintype.card_pos (α := σ); omega
  exact IsSMulRegular.nat_of_hasUniqueDiv hpos (by simpa using hXD)

/-- **Directness of the Clifford Fischer decomposition** (operator form): `ker D ⊓ range X = ⊥`. -/
theorem disjoint_ker_cliffordDirac_range_cliffordMul [HasUniqueDiv M] {c : σ → Module.End R M}
    (hc_sq : ∀ i, c i ∘ₗ c i = -1) (hc_anti : Pairwise fun i j ↦ c i ∘ₗ c j + c j ∘ₗ c i = 0) :
    Disjoint (LinearMap.ker (cliffordDirac c)) (LinearMap.range (cliffordMul c)) := by
  rcases isEmpty_or_nonempty σ with _ | _
  · simp
  rw [Submodule.disjoint_def]
  rintro _ hD ⟨w, rfl⟩
  rw [eq_zero_of_cliffordDirac_cliffordMul_eq_zero hc_sq hc_anti hD, map_zero]

/-- **Directness of the Clifford Fischer decomposition** (graded form). -/
theorem disjoint_monogenicSubmodule_map_cliffordMul [HasUniqueDiv M] {c : σ → Module.End R M}
    (hc_sq : ∀ i, c i ∘ₗ c i = -1) (hc_anti : Pairwise fun i j ↦ c i ∘ₗ c j + c j ∘ₗ c i = 0)
    (k : ℕ) :
    Disjoint (monogenicSubmodule c (k + 1))
      ((homogeneousTensorSubmodule σ R M k).map (cliffordMul c)) :=
  ((disjoint_ker_cliffordDirac_range_cliffordMul hc_sq hc_anti).mono_left
    (monogenicSubmodule_le_ker_cliffordDirac c (k + 1))).mono_right LinearMap.map_le_range

end Ring

section Rational

variable {σ R M : Type*} [CommRing R] [Algebra ℚ R] [AddCommGroup M] [Module R M] [Fintype σ]

private theorem exists_cliffordDirac_cliffordMul_of_mem_iSup [Nonempty σ] {c : σ → Module.End R M}
    (hc_sq : ∀ i, c i ∘ₗ c i = -1) (hc_anti : Pairwise fun i j ↦ c i ∘ₗ c j + c j ∘ₗ c i = 0)
    {k : ℕ} {v : MvPolynomial σ R ⊗[R] M}
    (hv : v ∈ ⨆ j ≤ k, (monogenicSubmodule c (k - j)).map (cliffordMul c ^ j)) :
    ∃ w ∈ homogeneousTensorSubmodule σ R M k, cliffordDirac c (cliffordMul c w) = v := by
  let S : Submodule R (MvPolynomial σ R ⊗[R] M) :=
    { carrier := {v | ∃ w ∈ homogeneousTensorSubmodule σ R M k,
        cliffordDirac c (cliffordMul c w) = v}
      zero_mem' := ⟨0, Submodule.zero_mem _, by simp⟩
      add_mem' := fun ⟨w₁, hw₁, h₁⟩ ⟨w₂, hw₂, h₂⟩ ↦
        ⟨w₁ + w₂, Submodule.add_mem _ hw₁ hw₂, by simp [h₁, h₂]⟩
      smul_mem' := fun r _ ⟨w, hw, h⟩ ↦ ⟨r • w, Submodule.smul_mem _ r hw, by simp [h]⟩ }
  refine (iSup₂_le (a := S) fun j hj ↦ ?_) hv
  rintro _ ⟨m, hm, rfl⟩
  have hmem : (cliffordMul c ^ j) m ∈ homogeneousTensorSubmodule σ R M k := by
    simpa [Nat.sub_add_cancel hj] using cliffordMul_pow_mem_homogeneousTensorSubmodule j hm.1
  have ⟨q, hq, hDq⟩ : ∃ q : ℕ, q ≠ 0 ∧
      cliffordDirac c (cliffordMul c ((cliffordMul c ^ j) m)) = -(q • (cliffordMul c ^ j) m) := by
    rcases Nat.even_or_odd' j with ⟨a, rfl | rfl⟩
    · refine ⟨2 * (k - 2 * a) + Fintype.card σ + 2 * a,
        by have := Fintype.card_pos (α := σ); omega, ?_⟩
      rw [← mul_apply_eq_comp (cliffordMul c), ← pow_succ' (cliffordMul c) (2 * a)]
      exact (cliffordDirac_cliffordMul_pow_odd_and_even hc_sq hc_anti hm a).1
    · refine ⟨2 * a + 2, by omega, ?_⟩
      rw [← mul_apply_eq_comp (cliffordMul c), ← pow_succ' (cliffordMul c) (2 * a + 1)]
      exact (cliffordDirac_cliffordMul_pow_odd_and_even hc_sq hc_anti hm a).2
  refine ⟨-(algebraMap ℚ R (q : ℚ)⁻¹ • (cliffordMul c ^ j) m),
    Submodule.neg_mem _ (Submodule.smul_mem _ _ hmem), ?_⟩
  rw [map_neg, map_smul, map_neg, map_smul, hDq, smul_neg, neg_neg, ← Nat.cast_smul_eq_nsmul R,
    smul_smul, ← map_natCast (algebraMap ℚ R), ← map_mul,
    inv_mul_cancel₀ (Nat.cast_ne_zero.mpr hq), map_one, one_smul]

/-- **The full monogenic Fischer expansion** into powers of `cliffordMul c`. -/
theorem homogeneousTensorSubmodule_eq_iSup_map_cliffordMul_pow {c : σ → Module.End R M}
    (hc_sq : ∀ i, c i ∘ₗ c i = -1) (hc_anti : Pairwise fun i j ↦ c i ∘ₗ c j + c j ∘ₗ c i = 0)
    (k : ℕ) :
    homogeneousTensorSubmodule σ R M k =
      ⨆ j ≤ k, (monogenicSubmodule c (k - j)).map (cliffordMul c ^ j) := by
  refine le_antisymm ?_ (iSup₂_le fun j hj ↦ ?_)
  · induction k using Nat.strong_induction_on with
    | _ k ih =>
    rcases k with _ | k
    · exact fun u hu ↦ Submodule.mem_iSup_of_mem 0 <| Submodule.mem_iSup_of_mem (Nat.zero_le 0)
        ⟨u, by rwa [Nat.sub_zero, monogenicSubmodule_zero], by simp⟩
    rcases isEmpty_or_nonempty σ with _ | _
    · simp
    intro u hu
    obtain ⟨w, hw, hDXw⟩ := exists_cliffordDirac_cliffordMul_of_mem_iSup hc_sq hc_anti
      (ih k (Nat.lt_succ_self k) (cliffordDirac_mem_homogeneousTensorSubmodule (c := c) hu))
    have hm : u - cliffordMul c w ∈
        ⨆ j ≤ k + 1, (monogenicSubmodule c (k + 1 - j)).map (cliffordMul c ^ j) :=
      Submodule.mem_iSup_of_mem 0 <| Submodule.mem_iSup_of_mem (Nat.zero_le _) ⟨u - cliffordMul c w,
        ⟨Submodule.sub_mem _ hu (cliffordMul_mem_homogeneousTensorSubmodule hw), by simp [hDXw]⟩,
        by simp⟩
    have hw_iSup : cliffordMul c w ∈
        ⨆ j ≤ k + 1, (monogenicSubmodule c (k + 1 - j)).map (cliffordMul c ^ j) := by
      refine (?_ : (⨆ j ≤ k, (monogenicSubmodule c (k - j)).map (cliffordMul c ^ j)).map
          (cliffordMul c) ≤ _) ⟨w, ih k (Nat.lt_succ_self k) hw, rfl⟩
      simp_rw [Submodule.map_iSup, ← Submodule.map_comp]
      refine iSup₂_le fun j hj ↦ le_iSup₂_of_le (j + 1) (Nat.add_le_add_right hj 1) ?_
      rw [Nat.succ_sub_succ_eq_sub, pow_succ']; rfl
    simpa using Submodule.add_mem _ hm hw_iSup
  · rintro _ ⟨m, hm, rfl⟩
    simpa [Nat.sub_add_cancel hj] using cliffordMul_pow_mem_homogeneousTensorSubmodule j hm.1

/-- **Surjectivity of `D ∘ₗ X`** on `homogeneousTensorSubmodule σ R M k` over a `ℚ`-algebra. -/
theorem exists_cliffordDirac_cliffordMul_eq [Nonempty σ] {c : σ → Module.End R M}
    (hc_sq : ∀ i, c i ∘ₗ c i = -1) (hc_anti : Pairwise fun i j ↦ c i ∘ₗ c j + c j ∘ₗ c i = 0)
    {k : ℕ} {v : MvPolynomial σ R ⊗[R] M} (hv : v ∈ homogeneousTensorSubmodule σ R M k) :
    ∃ w ∈ homogeneousTensorSubmodule σ R M k, cliffordDirac c (cliffordMul c w) = v :=
  exists_cliffordDirac_cliffordMul_of_mem_iSup hc_sq hc_anti
    (homogeneousTensorSubmodule_eq_iSup_map_cliffordMul_pow hc_sq hc_anti k ▸ hv)

/-- **The Clifford Fischer decomposition** over a commutative `ℚ`-algebra `R`. -/
theorem monogenicSubmodule_sup_map_cliffordMul {c : σ → Module.End R M}
    (hc_sq : ∀ i, c i ∘ₗ c i = -1) (hc_anti : Pairwise fun i j ↦ c i ∘ₗ c j + c j ∘ₗ c i = 0)
    (k : ℕ) :
    monogenicSubmodule c (k + 1) ⊔ (homogeneousTensorSubmodule σ R M k).map (cliffordMul c) =
      homogeneousTensorSubmodule σ R M (k + 1) := by
  rcases isEmpty_or_nonempty σ with _ | _
  · simp
  refine le_antisymm (sup_le (monogenicSubmodule_le_homogeneousTensorSubmodule c (k + 1)) ?_)
    fun u hu ↦ ?_
  · rintro _ ⟨w, hw, rfl⟩; exact cliffordMul_mem_homogeneousTensorSubmodule hw
  · obtain ⟨w, hw, hDXw⟩ := exists_cliffordDirac_cliffordMul_eq hc_sq hc_anti
      (by simpa using cliffordDirac_mem_homogeneousTensorSubmodule (c := c) hu)
    exact Submodule.mem_sup.mpr ⟨u - cliffordMul c w,
      ⟨Submodule.sub_mem _ hu (cliffordMul_mem_homogeneousTensorSubmodule hw), by simp [hDXw]⟩,
      cliffordMul c w, ⟨w, hw, rfl⟩, sub_add_cancel u _⟩

private theorem cliffordDirac_smul_monomial_add_single (c : σ → Module.End R M) (i₀ : σ)
    (s : σ →₀ ℕ) (m' : M) [DecidableEq σ] :
    cliffordDirac c (algebraMap ℚ R ((s i₀ + 1 : ℕ) : ℚ)⁻¹ •
        (monomial (s + Finsupp.single i₀ 1) (1 : R) ⊗ₜ[R] m')) =
      monomial s (1 : R) ⊗ₜ[R] c i₀ m' + algebraMap ℚ R ((s i₀ + 1 : ℕ) : ℚ)⁻¹ •
        ∑ j ∈ Finset.univ.erase i₀,
          pderiv j (monomial (s + Finsupp.single i₀ 1) (1 : R)) ⊗ₜ[R] c j m' := by
  set s' : σ →₀ ℕ := s + Finsupp.single i₀ 1
  rw [map_smul, cliffordDirac_tmul, ← Finset.add_sum_erase _ _ (Finset.mem_univ i₀), smul_add]
  congr 1
  have hcast : ((s' i₀ : ℕ) : R) = ((s i₀ + 1 : ℕ) : R) := by simp [s']
  rw [pderiv_monomial, one_mul, add_tsub_cancel_right, hcast, ← mul_one (((s i₀ + 1 : ℕ) : R)),
    ← smul_eq_mul, ← smul_monomial, ← TensorProduct.smul_tmul', smul_smul,
    ← map_natCast (algebraMap ℚ R), ← map_mul,
    inv_mul_cancel₀ (Nat.cast_ne_zero.mpr (Nat.succ_ne_zero _)), map_one, one_smul]

private def diracPreimageSubmodule (c : σ → Module.End R M) (P : Submodule R M) (i₀ : σ)
    (d : ℕ) : Submodule R (MvPolynomial σ R ⊗[R] M) where
  carrier := {v | ∃ u ∈ homogeneousTensorSubmodule σ R M d,
    (∀ t, coeffTensor t u ∈ P) ∧ (∀ t, t i₀ = 0 → coeffTensor t u = 0) ∧ cliffordDirac c u = v}
  zero_mem' := ⟨0, Submodule.zero_mem _, fun _ ↦ by simp, fun _ _ ↦ by simp, by simp⟩
  add_mem' := fun ⟨u₁, hu₁, hP₁, h0₁, h₁⟩ ⟨u₂, hu₂, hP₂, h0₂, h₂⟩ ↦
    ⟨u₁ + u₂, Submodule.add_mem _ hu₁ hu₂, fun t ↦ by rw [map_add]; exact P.add_mem (hP₁ t) (hP₂ t),
      fun t ht ↦ by simp [h0₁ t ht, h0₂ t ht], by simp [h₁, h₂]⟩
  smul_mem' := fun r _ ⟨u, hu, hP, h0, h⟩ ↦
    ⟨r • u, Submodule.smul_mem _ r hu, fun t ↦ by rw [map_smul]; exact P.smul_mem r (hP t),
      fun t ht ↦ by simp [h0 t ht], by simp [h]⟩

private theorem monomial_tmul_mem_diracPreimageSubmodule {c : σ → Module.End R M}
    {P Q : Submodule R M} {i₀ : σ} (hi₀ : ∀ m ∈ Q, ∃ m' ∈ P, c i₀ m' = m)
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
  have hs'deg : s'.degree = k + 1 := by rw [map_add Finsupp.degree, hsdeg, Finsupp.degree_single]
  set u₀ : MvPolynomial σ R ⊗[R] M :=
    algebraMap ℚ R ((s i₀ + 1 : ℕ) : ℚ)⁻¹ • (monomial s' (1 : R) ⊗ₜ[R] m')
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
    · have htdeg : (s' - Finsupp.single j 1).degree = k := by
        rw [Finsupp.degree_tsub ((Finsupp.single_le_iff.mpr (Nat.pos_of_ne_zero hsj)).trans
          le_self_add), hs'deg, Finsupp.degree_single, Nat.add_sub_cancel]
      have := Finsupp.lt_degree_of_ne_zero hne hsj
      rw [pderiv_monomial, one_mul, ← mul_one ((s' j : ℕ) : R), ← smul_eq_mul, ← smul_monomial,
        ← TensorProduct.smul_tmul']
      exact S.smul_mem _ (ih (k - (s i₀ + 1)) (by omega) (s' - Finsupp.single j 1) (c j m')
        (hc j hm'P) htdeg (by simp [s', Finsupp.single_eq_of_ne' hne]))
  obtain ⟨u_rest, hu_rest, hP_rest, h0_rest, heq_rest⟩ := hrest
  refine ⟨u₀ - u_rest, Submodule.sub_mem _ (Submodule.smul_mem _ _
      (tmul_mem_homogeneousTensorSubmodule (isHomogeneous_monomial (1 : R) hs'deg) m')) hu_rest,
    fun t ↦ ?_, fun t ht ↦ ?_,
    by rw [map_sub, cliffordDirac_smul_monomial_add_single, heq_rest, add_sub_cancel_right]⟩
  · rw [map_sub, map_smul, coeffTensor_tmul]
    exact P.sub_mem (P.smul_mem _ (P.smul_mem _ hm'P)) (hP_rest t)
  · have hne : s' ≠ t := fun h ↦ by simp [s', ← h] at ht
    rw [map_sub, h0_rest t ht, sub_zero, map_smul, coeffTensor_tmul, coeff_monomial,
      ite_eq_right hne, zero_smul, smul_zero]

/-- **Submodule-valued polynomial Cauchy-Kowalewskaya for `cliffordDirac`**. -/
theorem exists_cliffordDirac_eq_of_mapsTo {c : σ → Module.End R M} {P Q : Submodule R M} {i₀ : σ}
    (hi₀ : ∀ m ∈ Q, ∃ m' ∈ P, c i₀ m' = m) (hc : ∀ j, Set.MapsTo (c j) P Q)
    {k : ℕ} {v : MvPolynomial σ R ⊗[R] M} (hv : v ∈ homogeneousTensorSubmodule σ R M k)
    (hvQ : ∀ s, coeffTensor s v ∈ Q) :
    ∃ u ∈ homogeneousTensorSubmodule σ R M (k + 1),
      (∀ s, coeffTensor s u ∈ P) ∧ (∀ s, s i₀ = 0 → coeffTensor s u = 0) ∧
        cliffordDirac c u = v := by
  obtain ⟨I, hdeg, -, hsum⟩ := exists_finset_sum_monomial_tmul_coeffTensor hv
  rw [← hsum]
  exact (diracPreimageSubmodule c P i₀ (k + 1)).sum_mem fun s hs ↦
    monomial_tmul_mem_diracPreimageSubmodule hi₀ hc k (k - s i₀) s (coeffTensor s v)
      (hvQ s) (hdeg s hs) rfl

/-- **Polynomial Cauchy-Kowalewskaya for `cliffordDirac`** when `c i₀` is surjective. -/
theorem exists_cliffordDirac_eq_of_surjective {c : σ → Module.End R M} {i₀ : σ}
    (hc : Function.Surjective (c i₀)) {k : ℕ} {v : MvPolynomial σ R ⊗[R] M}
    (hv : v ∈ homogeneousTensorSubmodule σ R M k) :
    ∃ u ∈ homogeneousTensorSubmodule σ R M (k + 1),
      (∀ s, s i₀ = 0 → coeffTensor s u = 0) ∧ cliffordDirac c u = v := by
  obtain ⟨u, hu, -, hu0, hDu⟩ := exists_cliffordDirac_eq_of_mapsTo (P := ⊤) (Q := ⊤)
    (fun m _ ↦ let ⟨m', hm'⟩ := hc m; ⟨m', trivial, hm'⟩) (fun _ _ _ ↦ trivial) hv fun _ ↦ trivial
  exact ⟨u, hu, hu0, hDu⟩

/-- **Cauchy-Kowalewskaya coefficient surjectivity** on `monogenicSubmodule c k` for `i₁ ≠ i₀`. -/
theorem coeffTensor_single_monogenicSubmodule_surjective {c : σ → Module.End R M}
    {i₀ i₁ : σ} (hne : i₁ ≠ i₀) (hc : Function.Surjective (c i₀)) (k : ℕ) :
    Function.Surjective
      (fun u : monogenicSubmodule c k ↦ coeffTensor (Finsupp.single i₁ k) u.val) := fun m ↦ by
  rcases k with _ | k
  · exact ⟨⟨1 ⊗ₜ[R] m, (monogenicSubmodule_zero c).symm ▸
      tmul_mem_homogeneousTensorSubmodule (isHomogeneous_one σ R) m⟩, by simp⟩
  · have hw : monomial (Finsupp.single i₁ (k + 1)) (1 : R) ⊗ₜ[R] m ∈
        homogeneousTensorSubmodule σ R M (k + 1) :=
      tmul_mem_homogeneousTensorSubmodule
        (isHomogeneous_monomial (1 : R) (Finsupp.degree_single i₁ (k + 1))) m
    obtain ⟨u, hu, hu0, hDu⟩ := exists_cliffordDirac_eq_of_surjective hc
      (cliffordDirac_mem_homogeneousTensorSubmodule (c := c) hw)
    have hm' : monomial (Finsupp.single i₁ (k + 1)) (1 : R) ⊗ₜ[R] m - u ∈
        monogenicSubmodule c (k + 1) :=
      mem_monogenicSubmodule.mpr ⟨Submodule.sub_mem _ hw hu, by rw [map_sub, hDu, sub_self]⟩
    refine ⟨⟨_, hm'⟩, ?_⟩
    dsimp only; classical
    rw [map_sub, hu0 _ (Finsupp.single_eq_of_ne' hne), sub_zero, coeffTensor_tmul, coeff_monomial,
      ite_eq_left rfl, one_smul]

end Rational

section Field

variable {σ K M : Type*} [Field K] [CharZero K] [AddCommGroup M] [Module K M] [Fintype σ]

/-- Finite-dimensional `M` makes `monogenicSubmodule c k` finite-dimensional. -/
instance [Module.Finite K M] (c : σ → Module.End K M) (k : ℕ) :
    FiniteDimensional K (monogenicSubmodule c k) :=
  Submodule.finiteDimensional_of_le (monogenicSubmodule_le_homogeneousTensorSubmodule c k)

theorem finrank_monogenicSubmodule_add_finrank [Module.Finite K M]
    {c : σ → Module.End K M} {i₀ : σ} (hc : Function.Surjective (c i₀)) (k : ℕ) :
    Module.finrank K (monogenicSubmodule c (k + 1)) +
        Module.finrank K (homogeneousTensorSubmodule σ K M k) =
      Module.finrank K (homogeneousTensorSubmodule σ K M (k + 1)) := by
  let Dk : homogeneousTensorSubmodule σ K M (k + 1) →ₗ[K] homogeneousTensorSubmodule σ K M k :=
    { toFun := fun u ↦ ⟨cliffordDirac c u.val,
        cliffordDirac_mem_homogeneousTensorSubmodule (c := c) u.property⟩
      map_add' := fun u v ↦ Subtype.ext (map_add (cliffordDirac c) u.val v.val)
      map_smul' := fun r u ↦ Subtype.ext (map_smul (cliffordDirac c) r u.val) }
  have hsurj : Function.Surjective Dk := fun ⟨v, hv⟩ ↦
    let ⟨u, hu, _, hDu⟩ := exists_cliffordDirac_eq_of_surjective hc hv
    ⟨⟨u, hu⟩, Subtype.ext hDu⟩
  have hker : LinearMap.ker Dk =
      (monogenicSubmodule c (k + 1)).comap (homogeneousTensorSubmodule σ K M (k + 1)).subtype := by
    ext ⟨u, hu⟩; simp [Dk, mem_monogenicSubmodule, hu]
  have h := LinearMap.finrank_range_add_finrank_ker (K := K)
    (V := homogeneousTensorSubmodule σ K M (k + 1)) (V₂ := homogeneousTensorSubmodule σ K M k) Dk
  rwa [LinearMap.range_eq_top.mpr hsurj, finrank_top, hker,
    (Submodule.comapSubtypeEquivOfLe
      (monogenicSubmodule_le_homogeneousTensorSubmodule c (k + 1))).finrank_eq, add_comm] at h

/-- **Dimension of `monogenicSubmodule c k`** for finite-dimensional `M` and surjective `c i₀`. -/
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
    have ⟨m, hm⟩ : ∃ m, Fintype.card σ = m + 1 := ⟨_, (Nat.sub_add_cancel Fintype.card_pos).symm⟩
    rw [hm, Nat.add_sub_cancel]; rw [hm, Nat.multichoose_succ_succ, add_mul] at h
    exact Nat.add_right_cancel h

/-- **Unconditional dimension of `monogenicSubmodule c k`** when some `c i₀` is bijective. -/
theorem finrank_monogenicSubmodule_of_bijective
    {c : σ → Module.End K M} {i₀ : σ} (hc : Function.Bijective (c i₀)) (k : ℕ) :
    Module.finrank K (monogenicSubmodule c k) =
      (Fintype.card σ - 1).multichoose k * Module.finrank K M := by
  by_cases hfin : Module.Finite K M
  · exact finrank_monogenicSubmodule hc.2 k
  have := HasUniqueDiv.of_module_algebraRat K M
  rw [Module.finrank_of_not_finite hfin, mul_zero]
  rcases k with _ | k
  · rw [monogenicSubmodule_zero, ← (homogeneousTensorZeroEquiv σ K M).finrank_eq]
    exact Module.finrank_of_not_finite hfin
  by_cases hsub : Subsingleton σ
  · rw [monogenicSubmodule_succ_eq_bot_of_subsingleton (fun i ↦ Subsingleton.elim i i₀ ▸ hc.1) k,
      finrank_bot]
  · obtain ⟨i₁, hi₁⟩ : ∃ i₁ : σ, i₁ ≠ i₀ := by
      by_contra! h; exact hsub ⟨fun a b ↦ (h a).trans (h b).symm⟩
    let f : monogenicSubmodule c (k + 1) →ₗ[K] M :=
      (coeffTensor (Finsupp.single i₁ (k + 1))).comp (monogenicSubmodule c (k + 1)).subtype
    have hinf : Cardinal.aleph0 ≤ Module.rank K M :=
      not_lt.mp (mt Module.rank_lt_aleph0_iff.mp hfin)
    rw [Module.finrank, Cardinal.toNat_eq_zero]
    have hle := (Cardinal.lift_le.mpr hinf).trans (f.lift_rank_le_of_surjective
      (coeffTensor_single_monogenicSubmodule_surjective hi₁ hc.2 (k + 1)))
    exact Or.inr (by simpa using hle)

end Field

end MvPolynomial
