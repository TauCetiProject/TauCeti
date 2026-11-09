/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Distribution.ContDiffMapSupportedIn
public import TauCeti.Analysis.Fourier.Torus.Periodization
import TauCeti.Analysis.Calculus.BumpFunction.Cutoff
import TauCeti.Analysis.Calculus.IteratedFDeriv.CompLinear

/-!
# The Schwartz kernel theorem for test functions supported in small compact sets

Let `K₁' ⊆ ℝ^a` and `K₂' ⊆ ℝ^b` be compact sets that meet none of their translates by nonzero
integer vectors (for instance sets of diameter less than one,
`TauCeti.UnitAddTorus.eq_zero_of_add_mem_of_diam_lt_one`), and let `B` be a bilinear map on
`𝓓_{K₁'}(ℝ^a, ℂ) × 𝓓_{K₂'}(ℝ^b, ℂ)` with values in a complex Banach space, continuous in the
sense that `‖B φ ψ‖ ≤ C N_k(φ) N_k(ψ)` for one of the `C^k` seminorms `N_k`. For compact sets
`K₁`, `K₂` in the interiors of `K₁'`, `K₂'`, this file constructs the kernel of `B` on
`K₁ × K₂`: a continuous linear map `T` on `𝓓_{K₁ × K₂}(ℝ^a × ℝ^b, ℂ)` with
`T (φ ⊗ ψ) = B φ ψ` for `φ` supported in `K₁` and `ψ` supported in `K₂`, where
`(φ ⊗ ψ)(x, y) = φ x * ψ y` is `ContDiffMapSupportedIn.tensor`. Every continuous linear map on
`𝓓_{K₁' × K₂'}` representing `B` on tensor products restricts to `T`
(`LinearMap.exists_schwartzKernel_supportedIn`). In particular the kernel on `K₁ × K₂` does
not depend on any of the choices in its construction, and kernels built on overlapping sets
agree on their common domain.

The proof transfers the Schwartz kernel theorem on the torus
(`LinearMap.existsUnique_schwartzKernel`) to these compact sets. Fix cutoffs `χᵢ` supported in
`Kᵢ'` and equal to one on `Kᵢ`. The bilinear map `(f, g) ↦ B (χ₁ f) (χ₂ g)` on smooth functions
on the tori `(ℝ / ℤ)^a` and `(ℝ / ℤ)^b` is continuous for the `C^k` norms, so it has a kernel
`K` on the product torus, and `T Φ` is `K` applied to the periodization of `Φ`
(`TauCeti.UnitAddTorus.periodize`). Since `Kᵢ'` meets none of its integer translates, the
periodization of `φ` cut off by `χ₁` is `φ` again, and periodization takes tensor products to
tensor products; this gives `T (φ ⊗ ψ) = B φ ψ`. For the comparison, a map `T'` as above
induces `h ↦ T' ((χ₁ ⊗ χ₂) h)` on the product torus, which represents the same bilinear map on
the torus, hence is `K` by uniqueness there.

## Main definitions

* `ContDiffMapSupportedIn.tensor`: the tensor product `(x, y) ↦ φ x * ψ y` of two smooth
  functions supported in compact sets, supported in the product set.

## Main results

* `LinearMap.exists_schwartzKernel_supportedIn`: existence of the kernel on `K₁ × K₂` and its
  agreement with every kernel on `K₁' × K₂'`.

## References

* L. Hörmander, *The Analysis of Linear Partial Differential Operators I*, second edition,
  Springer, 1990, proof of Theorem 5.2.1 (the Schwartz kernel theorem, proved by Fourier series
  on a cube).
-/

public section

noncomputable section

open Function Set TopologicalSpace
open scoped ContDiff Distributions

namespace ContDiffMapSupportedIn

variable {E D : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup D]
  [NormedSpace ℝ D] {K₁ : Compacts E} {K₂ : Compacts D}

/-- The tensor product `(x, y) ↦ φ x * ψ y` of smooth functions `φ` supported in `K₁` and `ψ`
supported in `K₂`, a smooth function supported in `K₁ ×ˢ K₂`. -/
def tensor (φ : 𝓓_{K₁}(E, ℂ)) (ψ : 𝓓_{K₂}(D, ℂ)) : 𝓓_{K₁ ×ˢ K₂}(E × D, ℂ) :=
  .of_support_subset ((φ.contDiff.comp contDiff_fst).mul (ψ.contDiff.comp contDiff_snd))
    fun _ hp ↦ ⟨φ.support_subset (left_ne_zero_of_mul hp),
      ψ.support_subset (right_ne_zero_of_mul hp)⟩

@[simp]
theorem tensor_apply (φ : 𝓓_{K₁}(E, ℂ)) (ψ : 𝓓_{K₂}(D, ℂ)) (p : E × D) :
    φ.tensor ψ p = φ p.1 * ψ p.2 :=
  (rfl)

theorem tensor_add_left (φ φ' : 𝓓_{K₁}(E, ℂ)) (ψ : 𝓓_{K₂}(D, ℂ)) :
    (φ + φ').tensor ψ = φ.tensor ψ + φ'.tensor ψ := by
  ext p
  simp [add_mul]

theorem tensor_add_right (φ : 𝓓_{K₁}(E, ℂ)) (ψ ψ' : 𝓓_{K₂}(D, ℂ)) :
    φ.tensor (ψ + ψ') = φ.tensor ψ + φ.tensor ψ' := by
  ext p
  simp [mul_add]

theorem tensor_smul_left (c : ℂ) (φ : 𝓓_{K₁}(E, ℂ)) (ψ : 𝓓_{K₂}(D, ℂ)) :
    (c • φ).tensor ψ = c • φ.tensor ψ := by
  ext p
  simp [mul_assoc]

theorem tensor_smul_right (c : ℂ) (φ : 𝓓_{K₁}(E, ℂ)) (ψ : 𝓓_{K₂}(D, ℂ)) :
    φ.tensor (c • ψ) = c • φ.tensor ψ := by
  ext p
  simp [mul_left_comm]

/-! ### Multiplication by smooth functions and cutoffs -/

section Mul

variable {K : Compacts E}

/-- The `C^i` seminorms, `i ≤ k`, of `χ g` are bounded by `2 ^ k N_k(χ) M` when `M` bounds the
derivatives of `g` of order at most `k`. -/
theorem seminorm_bilinLeftCLM_mul_le (χ : 𝓓_{K}(E, ℂ)) {g : E → ℂ} (hg : ContDiff ℝ ∞ g)
    {k : ℕ} {M : ℝ} (hM : ∀ j ≤ k, ∀ x, ‖iteratedFDeriv ℝ j g x‖ ≤ M) {i : ℕ} (hi : i ≤ k) :
    N[ℂ]_{K, i} (bilinLeftCLM (ContinuousLinearMap.mul ℂ ℂ) hg χ) ≤
      2 ^ k * ContDiffMapSupportedIn.supSeminorm ℂ E ℂ ⊤ K k χ * M := by
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0 (Nat.zero_le k) 0)
  refine (ContDiffMapSupportedIn.seminorm_top_le_iff ℂ (by positivity) i _).2 fun x _ ↦ ?_
  rw [bilinLeftCLM_apply]
  simp only [ContinuousLinearMap.mul_apply']
  refine (norm_iteratedFDeriv_mul_le χ.contDiff hg x (mod_cast le_top)).trans ?_
  calc _ ≤ ∑ j ∈ Finset.range (i + 1), (i.choose j : ℝ) *
        ContDiffMapSupportedIn.supSeminorm ℂ E ℂ ⊤ K k χ * M := by
        gcongr with j hj
        · exact (norm_iteratedFDeriv_apply_le_seminorm_top ℂ).trans
            (Seminorm.le_finset_sup_apply (Finset.mem_Iic.2
              ((Finset.mem_range_succ_iff.1 hj).trans hi)))
        · exact hM _ ((Nat.sub_le i j).trans hi) x
    _ = 2 ^ i * ContDiffMapSupportedIn.supSeminorm ℂ E ℂ ⊤ K k χ * M := by
        rw [← Finset.sum_mul, ← Finset.sum_mul, ← Nat.cast_sum, Nat.sum_range_choose]
        push_cast
        ring
    _ ≤ _ := by gcongr; exact one_le_two

/-- A compact set `K` in the interior of a compact set `K'` of a finite-dimensional space has a
smooth cutoff supported in `K'` and equal to one on `K`. -/
theorem exists_eqOn_one_of_subset_interior [FiniteDimensional ℝ E] {K K' : Compacts E}
    (h : (K : Set E) ⊆ interior K') : ∃ χ : 𝓓_{K'}(E, ℂ), EqOn χ 1 K := by
  obtain ⟨ψ, hψ, -, hψ1, -, hψK'⟩ := K.isCompact.exists_contDiff_cutoff isOpen_interior h
  have hsmooth : ContDiff ℝ ∞ fun x ↦ (ψ x : ℂ) := Complex.ofRealCLM.contDiff.comp hψ
  have hsupp : support (fun x ↦ (ψ x : ℂ)) ⊆ K' := fun x hx ↦
    interior_subset (hψK' (subset_tsupport ψ (by simpa using hx)))
  refine ⟨.of_support_subset hsmooth hsupp, fun x hx ↦ ?_⟩
  rw [ContDiffMapSupportedIn.coe_of_support_subset, interior_subset (hψ1 hx), Pi.one_apply,
    Complex.ofReal_one]

end Mul

end ContDiffMapSupportedIn

namespace TauCeti.UnitAddTorus

open ContDiffMapSupportedIn _root_.UnitAddTorus

/-! ### Cutting off smooth functions on the torus -/

section Cutoff

variable {d : Type*} [Fintype d] {K : Compacts (d → ℝ)}

/-- The lift of a smooth function on the torus, multiplied by a cutoff `χ` supported in `K`. -/
private def cutoffLift (χ : 𝓓_{K}(d → ℝ, ℂ)) : smoothFunctions d →ₗ[ℂ] 𝓓_{K}(d → ℝ, ℂ) where
  toFun f := bilinLeftCLM (ContinuousLinearMap.mul ℂ ℂ) (mem_smoothFunctions.1 f.2) χ
  map_add' f g := by
    ext x
    simp [mul_add]
  map_smul' c f := by
    ext x
    simp only [bilinLeftCLM_apply, ContinuousLinearMap.mul_apply', SetLike.val_smul,
      Pi.smul_apply, smul_eq_mul, RingHom.id_apply, FunLike.coe_smul]
    ring

private theorem cutoffLift_apply (χ : 𝓓_{K}(d → ℝ, ℂ)) (f : smoothFunctions d) (x : d → ℝ) :
    cutoffLift χ f x = χ x * (f : UnitAddTorus d → ℂ) (fun i ↦ (x i : UnitAddCircle)) :=
  (rfl)

/-- The `C^k` seminorm of `χ f` is bounded by `2 ^ k N_k(χ) M` for `DerivBound k M f`. -/
private theorem supSeminorm_cutoffLift_le (χ : 𝓓_{K}(d → ℝ, ℂ)) {f : smoothFunctions d}
    {k : ℕ} {M : ℝ} (hf : DerivBound k M (f : UnitAddTorus d → ℂ)) :
    ContDiffMapSupportedIn.supSeminorm ℂ _ ℂ ⊤ K k (cutoffLift χ f) ≤
      2 ^ k * ContDiffMapSupportedIn.supSeminorm ℂ _ ℂ ⊤ K k χ * M := by
  have hM0 := hf.nonneg
  refine Seminorm.finset_sup_apply_le (by positivity) fun i hi ↦ ?_
  exact seminorm_bilinLeftCLM_mul_le χ (mem_smoothFunctions.1 f.2)
    (fun j hj x ↦ hf.norm_iteratedFDeriv_le hj x) (Finset.mem_Iic.1 hi)

/-- On a set meeting none of its nonzero integer translates, a cutoff equal to one on the
support of `φ` recovers `φ` from its periodization. -/
private theorem cutoffLift_periodize {K' : Compacts (d → ℝ)}
    (hK : ∀ x ∈ K, ∀ ℓ : d → ℤ, x + (fun i ↦ (ℓ i : ℝ)) ∈ K → ℓ = 0) (χ : 𝓓_{K}(d → ℝ, ℂ))
    (hKK' : K' ≤ K) (hχ : EqOn χ 1 K') (φ : 𝓓_{K'}(d → ℝ, ℂ)) :
    cutoffLift χ ⟨periodize φ, periodize_mem_smoothFunctions φ.contDiff φ.hasCompactSupport⟩ =
      monoCLM ℂ φ := by
  ext x
  rw [cutoffLift_apply, monoCLM_apply, ite_eq_left ⟨le_rfl, hKK'⟩, Submodule.coe_mk]
  by_cases hx : x ∈ K
  · rw [periodize_coe_of_mem hK (φ.support_subset.trans hKK') hx]
    by_cases hφ : φ x = 0
    · rw [hφ, mul_zero]
    · rw [hχ (φ.support_subset hφ), Pi.one_apply, one_mul]
  · rw [χ.zero_on_compl hx, φ.zero_on_compl fun h ↦ hx (hKK' h), Pi.zero_apply, zero_mul]

end Cutoff

/-! ### The product of two tori -/

section Prod

variable {a b : Type*}

/-- The identification of `ℝ^(a ⊕ b)` with `ℝ^a × ℝ^b`. -/
private abbrev splitEquiv (a b : Type*) :
    (a ⊕ b → ℝ) ≃L[ℝ] (a → ℝ) × (b → ℝ) :=
  ContinuousLinearEquiv.sumPiEquivProdPi ℝ a b fun _ ↦ ℝ

private theorem splitEquiv_apply (x : a ⊕ b → ℝ) :
    splitEquiv a b x = (fun i ↦ x (.inl i), fun i ↦ x (.inr i)) :=
  (rfl)

private theorem splitEquiv_symm_apply (p : (a → ℝ) × (b → ℝ)) :
    (splitEquiv a b).symm p = Sum.elim p.1 p.2 := by
  ext i
  cases i <;> rfl

/-- The integer translates of the preimage of a product of sets meeting none of their nonzero
integer translates. -/
private theorem eq_zero_of_mem_preimage_splitEquiv {S₁ : Set (a → ℝ)} {S₂ : Set (b → ℝ)}
    (hS₁ : ∀ x ∈ S₁, ∀ ℓ : a → ℤ, x + (fun i ↦ (ℓ i : ℝ)) ∈ S₁ → ℓ = 0)
    (hS₂ : ∀ y ∈ S₂, ∀ ℓ : b → ℤ, y + (fun i ↦ (ℓ i : ℝ)) ∈ S₂ → ℓ = 0) :
    ∀ x ∈ splitEquiv a b ⁻¹' (S₁ ×ˢ S₂), ∀ ℓ : a ⊕ b → ℤ,
      x + (fun i ↦ (ℓ i : ℝ)) ∈ splitEquiv a b ⁻¹' (S₁ ×ˢ S₂) → ℓ = 0 := by
  intro x hx ℓ hxℓ
  have h₁ := hS₁ _ hx.1 (fun i ↦ ℓ (.inl i)) hxℓ.1
  have h₂ := hS₂ _ hx.2 (fun i ↦ ℓ (.inr i)) hxℓ.2
  ext i
  cases i with
  | inl i => exact congrFun h₁ i
  | inr i => exact congrFun h₂ i

variable [Fintype a] [Fintype b]

private theorem norm_splitEquiv_le :
    ‖(splitEquiv a b : (a ⊕ b → ℝ) →L[ℝ] (a → ℝ) × (b → ℝ))‖ ≤ 1 := by
  refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun x ↦ ?_
  rw [one_mul, ContinuousLinearEquiv.coe_coe, splitEquiv_apply, Prod.norm_def, max_le_iff]
  exact ⟨(pi_norm_le_iff_of_nonneg (norm_nonneg x)).2 fun i ↦ norm_le_pi_norm x _,
    (pi_norm_le_iff_of_nonneg (norm_nonneg x)).2 fun i ↦ norm_le_pi_norm x _⟩

private theorem norm_splitEquiv_symm_le :
    ‖((splitEquiv a b).symm : (a → ℝ) × (b → ℝ) →L[ℝ] (a ⊕ b → ℝ))‖ ≤ 1 := by
  refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun p ↦ ?_
  rw [one_mul, ContinuousLinearEquiv.coe_coe, splitEquiv_symm_apply]
  refine (pi_norm_le_iff_of_nonneg (norm_nonneg p)).2 fun i ↦ ?_
  cases i with
  | inl i => exact (norm_le_pi_norm p.1 i).trans (norm_fst_le p)
  | inr i => exact (norm_le_pi_norm p.2 i).trans (norm_snd_le p)

variable {L : Compacts ((a → ℝ) × (b → ℝ))}

/-- The periodization to the product torus `UnitAddTorus (a ⊕ b)` of a smooth function on
`ℝ^a × ℝ^b` supported in a compact set. -/
private def periodizeProd : 𝓓_{L}((a → ℝ) × (b → ℝ), ℂ) →ₗ[ℂ] smoothFunctions (a ⊕ b) where
  toFun Φ := ⟨periodize (Φ ∘ splitEquiv a b),
    periodize_mem_smoothFunctions (Φ.contDiff.comp (splitEquiv a b).contDiff)
      (Φ.hasCompactSupport.comp_homeomorph (splitEquiv a b).toHomeomorph)⟩
  map_add' Φ Ψ := Subtype.ext (periodize_add
    (Φ.hasCompactSupport.comp_homeomorph (splitEquiv a b).toHomeomorph)
    (Ψ.hasCompactSupport.comp_homeomorph (splitEquiv a b).toHomeomorph))
  map_smul' c Φ := Subtype.ext (periodize_smul c (Φ ∘ splitEquiv a b))

private theorem coe_periodizeProd (Φ : 𝓓_{L}((a → ℝ) × (b → ℝ), ℂ)) :
    (periodizeProd Φ : UnitAddTorus (a ⊕ b) → ℂ) = periodize (Φ ∘ splitEquiv a b) :=
  (rfl)

private theorem periodizeProd_tensor {K₁ : Compacts (a → ℝ)} {K₂ : Compacts (b → ℝ)}
    (φ : 𝓓_{K₁}(a → ℝ, ℂ)) (ψ : 𝓓_{K₂}(b → ℝ, ℂ)) :
    periodizeProd (φ.tensor ψ) =
      ⟨tensor (periodize φ) (periodize ψ), tensor_mem_smoothFunctions
        (periodize_mem_smoothFunctions φ.contDiff φ.hasCompactSupport)
        (periodize_mem_smoothFunctions ψ.contDiff ψ.hasCompactSupport)⟩ :=
  Subtype.ext (periodize_tensor φ.hasCompactSupport ψ.hasCompactSupport)

/-- If `L` lies in a product of sets meeting none of their nonzero integer translates, the
`C^N` norms of the periodization of `Φ` are bounded by the `C^N` seminorm of `Φ`. -/
private theorem derivBound_periodizeProd {S₁ : Set (a → ℝ)} {S₂ : Set (b → ℝ)}
    (hS₁ : ∀ x ∈ S₁, ∀ ℓ : a → ℤ, x + (fun i ↦ (ℓ i : ℝ)) ∈ S₁ → ℓ = 0)
    (hS₂ : ∀ y ∈ S₂, ∀ ℓ : b → ℤ, y + (fun i ↦ (ℓ i : ℝ)) ∈ S₂ → ℓ = 0)
    (hL : (L : Set ((a → ℝ) × (b → ℝ))) ⊆ S₁ ×ˢ S₂) (Φ : 𝓓_{L}((a → ℝ) × (b → ℝ), ℂ)) (N : ℕ) :
    DerivBound N (ContDiffMapSupportedIn.supSeminorm ℂ _ ℂ ⊤ L N Φ)
      (periodizeProd Φ : UnitAddTorus (a ⊕ b) → ℂ) := by
  refine derivBound_periodize (eq_zero_of_mem_preimage_splitEquiv hS₁ hS₂)
    (Φ.contDiff.comp (splitEquiv a b).contDiff)
    (Φ.hasCompactSupport.comp_homeomorph (splitEquiv a b).toHomeomorph) ?_ fun j hj x ↦ ?_
  · exact (tsupport_comp_subset_preimage _ (splitEquiv a b).continuous).trans
      (preimage_mono (Φ.tsupport_subset.trans hL))
  · have h := ((splitEquiv a b : (a ⊕ b → ℝ) →L[ℝ] (a → ℝ) × (b → ℝ))
      |>.norm_iteratedFDeriv_comp_right_le Φ.contDiff x (i := j) (mod_cast le_top)).trans
        (mul_le_of_le_one_right (norm_nonneg _) (pow_le_one₀ (norm_nonneg _) norm_splitEquiv_le))
    rw [ContinuousLinearEquiv.coe_coe] at h
    refine h.trans ?_
    exact (norm_iteratedFDeriv_apply_le_seminorm_top ℂ).trans
      (Seminorm.le_finset_sup_apply (Finset.mem_Iic.2 hj))

/-- The lift of a smooth function on the product torus to `ℝ^a × ℝ^b`, multiplied by a cutoff
`χ` supported in `L`. -/
private def cutoffLiftProd (χ : 𝓓_{L}((a → ℝ) × (b → ℝ), ℂ)) :
    smoothFunctions (a ⊕ b) →ₗ[ℂ] 𝓓_{L}((a → ℝ) × (b → ℝ), ℂ) where
  toFun h := bilinLeftCLM (ContinuousLinearMap.mul ℂ ℂ)
    ((mem_smoothFunctions.1 h.2).comp (splitEquiv a b).symm.contDiff) χ
  map_add' f g := by
    ext x
    simp [mul_add]
  map_smul' c f := by
    ext x
    simp only [bilinLeftCLM_apply, ContinuousLinearMap.mul_apply', SetLike.val_smul,
      Function.comp_apply, Pi.smul_apply, smul_eq_mul, RingHom.id_apply,
      FunLike.coe_smul]
    ring

private theorem cutoffLiftProd_apply (χ : 𝓓_{L}((a → ℝ) × (b → ℝ), ℂ))
    (h : smoothFunctions (a ⊕ b)) (p : (a → ℝ) × (b → ℝ)) :
    cutoffLiftProd χ h p =
      χ p * (h : UnitAddTorus (a ⊕ b) → ℂ) (fun i ↦ ((splitEquiv a b).symm p i : UnitAddCircle)) :=
  (rfl)

private theorem supSeminorm_cutoffLiftProd_le (χ : 𝓓_{L}((a → ℝ) × (b → ℝ), ℂ))
    {h : smoothFunctions (a ⊕ b)} {k : ℕ} {M : ℝ}
    (hh : DerivBound k M (h : UnitAddTorus (a ⊕ b) → ℂ)) {i : ℕ} (hi : i ≤ k) :
    N[ℂ]_{L, i} (cutoffLiftProd χ h) ≤
      2 ^ k * ContDiffMapSupportedIn.supSeminorm ℂ _ ℂ ⊤ L k χ * M :=
  seminorm_bilinLeftCLM_mul_le χ ((mem_smoothFunctions.1 h.2).comp (splitEquiv a b).symm.contDiff)
    (fun j hj x ↦ by
      have h' := (((splitEquiv a b).symm : (a → ℝ) × (b → ℝ) →L[ℝ] (a ⊕ b → ℝ))
        |>.norm_iteratedFDeriv_comp_right_le (mem_smoothFunctions.1 h.2) x (i := j)
          (mod_cast le_top)).trans (mul_le_of_le_one_right
          (norm_nonneg _) (pow_le_one₀ (norm_nonneg _) norm_splitEquiv_symm_le))
      rw [ContinuousLinearEquiv.coe_coe] at h'
      exact h'.trans (hh.norm_iteratedFDeriv_le hj _)) hi

private theorem cutoffLiftProd_tensor {K₁ : Compacts (a → ℝ)} {K₂ : Compacts (b → ℝ)}
    (χ₁ : 𝓓_{K₁}(a → ℝ, ℂ)) (χ₂ : 𝓓_{K₂}(b → ℝ, ℂ)) (f : smoothFunctions a)
    (g : smoothFunctions b) :
    cutoffLiftProd (χ₁.tensor χ₂)
        ⟨tensor (f : UnitAddTorus a → ℂ) (g : UnitAddTorus b → ℂ),
          tensor_mem_smoothFunctions f.2 g.2⟩ =
      (cutoffLift χ₁ f).tensor (cutoffLift χ₂ g) := by
  ext p
  simp only [cutoffLiftProd_apply, ContDiffMapSupportedIn.tensor_apply, cutoffLift_apply,
    _root_.UnitAddTorus.tensor_apply, splitEquiv_symm_apply, Sum.elim_inl, Sum.elim_inr]
  ring

/-- If `L` lies in a product of sets meeting none of their nonzero integer translates and a
cutoff supported in that product is one on `L`, the cutoff recovers `Φ` from its periodization. -/
private theorem cutoffLiftProd_periodizeProd {K₁ : Compacts (a → ℝ)} {K₂ : Compacts (b → ℝ)}
    (hK₁ : ∀ x ∈ K₁, ∀ ℓ : a → ℤ, x + (fun i ↦ (ℓ i : ℝ)) ∈ K₁ → ℓ = 0)
    (hK₂ : ∀ y ∈ K₂, ∀ ℓ : b → ℤ, y + (fun i ↦ (ℓ i : ℝ)) ∈ K₂ → ℓ = 0)
    (χ : 𝓓_{K₁ ×ˢ K₂}((a → ℝ) × (b → ℝ), ℂ)) (hLK : L ≤ K₁ ×ˢ K₂) (hχ : EqOn χ 1 L)
    (Φ : 𝓓_{L}((a → ℝ) × (b → ℝ), ℂ)) :
    cutoffLiftProd χ (periodizeProd Φ) = monoCLM ℂ Φ := by
  ext p
  rw [cutoffLiftProd_apply, coe_periodizeProd, monoCLM_apply, ite_eq_left ⟨le_rfl, hLK⟩]
  by_cases hp : p ∈ (K₁ ×ˢ K₂ : Compacts ((a → ℝ) × (b → ℝ)))
  · have hx : (splitEquiv a b).symm p ∈ splitEquiv a b ⁻¹' ((K₁ : Set (a → ℝ)) ×ˢ K₂) := by
      rwa [mem_preimage, ContinuousLinearEquiv.apply_symm_apply]
    rw [periodize_coe_of_mem (f := Φ ∘ splitEquiv a b)
      (eq_zero_of_mem_preimage_splitEquiv hK₁ hK₂) (fun x hx ↦ hLK (Φ.support_subset hx)) hx,
      Function.comp_apply, ContinuousLinearEquiv.apply_symm_apply]
    by_cases hΦ : Φ p = 0
    · rw [hΦ, mul_zero]
    · rw [hχ (Φ.support_subset hΦ), Pi.one_apply, one_mul]
  · rw [χ.zero_on_compl hp, Φ.zero_on_compl fun h ↦ hp (hLK h), Pi.zero_apply, zero_mul]

end Prod

end TauCeti.UnitAddTorus

/-! ### The kernel theorem -/

namespace LinearMap

open ContDiffMapSupportedIn TauCeti.UnitAddTorus _root_.UnitAddTorus

variable {a b : Type*} [Fintype a] [Fintype b]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]
  {K₁ K₁' : Compacts (a → ℝ)} {K₂ K₂' : Compacts (b → ℝ)}

omit [CompleteSpace F] in
/-- A bilinear map bounded by a product of `C^k` seminorms induces, through cutoffs, a bilinear
map on smooth functions on two tori which is continuous for the `C^k` norms. -/
private theorem exists_bound_compl₁₂_cutoffLift
    (B : 𝓓_{K₁'}(a → ℝ, ℂ) →ₗ[ℂ] 𝓓_{K₂'}(b → ℝ, ℂ) →ₗ[ℂ] F)
    (hB : ∃ (C : ℝ) (k : ℕ), ∀ φ ψ, ‖B φ ψ‖ ≤
      C * ContDiffMapSupportedIn.supSeminorm ℂ _ ℂ ⊤ K₁' k φ *
        ContDiffMapSupportedIn.supSeminorm ℂ _ ℂ ⊤ K₂' k ψ)
    (χ₁ : 𝓓_{K₁'}(a → ℝ, ℂ)) (χ₂ : 𝓓_{K₂'}(b → ℝ, ℂ)) :
    ∃ (C : ℝ) (N : ℕ), ∀ (f : smoothFunctions a) (g : smoothFunctions b) (M₁ M₂ : ℝ),
      DerivBound N M₁ (f : UnitAddTorus a → ℂ) → DerivBound N M₂ (g : UnitAddTorus b → ℂ) →
        ‖B.compl₁₂ (cutoffLift χ₁) (cutoffLift χ₂) f g‖ ≤ C * M₁ * M₂ := by
  obtain ⟨C, k, hCk⟩ := hB
  have hC0 : 0 ≤ max C 0 := le_max_right _ _
  refine ⟨max C 0 * (2 ^ k * ContDiffMapSupportedIn.supSeminorm ℂ _ ℂ ⊤ K₁' k χ₁) *
    (2 ^ k * ContDiffMapSupportedIn.supSeminorm ℂ _ ℂ ⊤ K₂' k χ₂), k,
    fun f g M₁ M₂ hf hg ↦ ?_⟩
  have h₁ := supSeminorm_cutoffLift_le χ₁ hf
  have h₂ := supSeminorm_cutoffLift_le χ₂ hg
  rw [LinearMap.compl₁₂_apply]
  calc _ ≤ max C 0 * ContDiffMapSupportedIn.supSeminorm ℂ _ ℂ ⊤ K₁' k (cutoffLift χ₁ f) *
        ContDiffMapSupportedIn.supSeminorm ℂ _ ℂ ⊤ K₂' k (cutoffLift χ₂ g) :=
        (hCk _ _).trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
          (le_max_left _ _) (apply_nonneg _ _)) (apply_nonneg _ _))
    _ ≤ max C 0 * (2 ^ k * ContDiffMapSupportedIn.supSeminorm ℂ _ ℂ ⊤ K₁' k χ₁ * M₁) *
        (2 ^ k * ContDiffMapSupportedIn.supSeminorm ℂ _ ℂ ⊤ K₂' k χ₂ * M₂) :=
        mul_le_mul (mul_le_mul_of_nonneg_left h₁ hC0) h₂ (apply_nonneg _ _)
          (mul_nonneg hC0 (mul_nonneg (mul_nonneg (by positivity) (apply_nonneg _ _))
            hf.nonneg))
    _ = _ := by ring

omit [CompleteSpace F] in
/-- A continuous linear map on `𝓓_L(ℝ^a × ℝ^b, ℂ)`, composed with a cutoff lift from the product
torus, is continuous for one of the `C^N` norms on the torus. -/
private theorem exists_bound_comp_cutoffLiftProd {L : Compacts ((a → ℝ) × (b → ℝ))}
    (T' : 𝓓_{L}((a → ℝ) × (b → ℝ), ℂ) →L[ℂ] F) (χ : 𝓓_{L}((a → ℝ) × (b → ℝ), ℂ)) :
    ∃ (C : ℝ) (N : ℕ), ∀ (h : smoothFunctions (a ⊕ b)) M,
      DerivBound N M (h : UnitAddTorus (a ⊕ b) → ℂ) →
        ‖(T'.toLinearMap ∘ₗ cutoffLiftProd χ) h‖ ≤ C * M := by
  obtain ⟨s, C, -, hs⟩ := Seminorm.bound_of_continuous
    (ContDiffMapSupportedIn.withSeminorms ℂ _ ℂ ⊤ L)
    ((normSeminorm ℂ F).comp T'.toLinearMap) (continuous_norm.comp T'.continuous)
  obtain ⟨N, hN⟩ : ∃ N : ℕ, ∀ i ∈ s, i ≤ N :=
    ⟨s.sup fun i ↦ i, fun i hi ↦ Finset.le_sup (f := fun i ↦ i) hi⟩
  refine ⟨C * (2 ^ N * ContDiffMapSupportedIn.supSeminorm ℂ _ ℂ ⊤ L N χ), N,
    fun h M hM ↦ ?_⟩
  have hM0 := hM.nonneg
  refine (hs (cutoffLiftProd χ h)).trans ?_
  rw [smul_apply, NNReal.smul_def, smul_eq_mul, mul_assoc]
  gcongr
  exact Seminorm.finset_sup_apply_le (by positivity) fun i hi ↦
    supSeminorm_cutoffLiftProd_le _ hM (hN i hi)

/-- **The Schwartz kernel theorem for test functions supported in compact sets.** Let `K₁'` and
`K₂'` be compact sets meeting none of their translates by nonzero integer vectors, and let `B` be
a bilinear map on `𝓓_{K₁'}(ℝ^a, ℂ) × 𝓓_{K₂'}(ℝ^b, ℂ)` bounded by a product of `C^k` seminorms.
For compact sets `K₁`, `K₂` in the interiors of `K₁'`, `K₂'` there is a continuous linear map `T`
on `𝓓_{K₁ × K₂}(ℝ^a × ℝ^b, ℂ)` with `T (φ ⊗ ψ) = B φ ψ`, and every continuous linear map `T'` on
`𝓓_{K₁' × K₂'}(ℝ^a × ℝ^b, ℂ)` with `T' (φ ⊗ ψ) = B φ ψ` restricts to `T`. -/
theorem exists_schwartzKernel_supportedIn
    (B : 𝓓_{K₁'}(a → ℝ, ℂ) →ₗ[ℂ] 𝓓_{K₂'}(b → ℝ, ℂ) →ₗ[ℂ] F)
    (hB : ∃ (C : ℝ) (k : ℕ), ∀ φ ψ, ‖B φ ψ‖ ≤
      C * ContDiffMapSupportedIn.supSeminorm ℂ _ ℂ ⊤ K₁' k φ *
        ContDiffMapSupportedIn.supSeminorm ℂ _ ℂ ⊤ K₂' k ψ)
    (hK₁' : ∀ x ∈ K₁', ∀ ℓ : a → ℤ, x + (fun i ↦ (ℓ i : ℝ)) ∈ K₁' → ℓ = 0)
    (hK₂' : ∀ y ∈ K₂', ∀ ℓ : b → ℤ, y + (fun i ↦ (ℓ i : ℝ)) ∈ K₂' → ℓ = 0)
    (hK₁ : (K₁ : Set (a → ℝ)) ⊆ interior K₁') (hK₂ : (K₂ : Set (b → ℝ)) ⊆ interior K₂') :
    ∃ T : 𝓓_{K₁ ×ˢ K₂}((a → ℝ) × (b → ℝ), ℂ) →L[ℂ] F,
      (∀ φ ψ, T (φ.tensor ψ) = B (monoCLM ℂ φ) (monoCLM ℂ ψ)) ∧
      ∀ T' : 𝓓_{K₁' ×ˢ K₂'}((a → ℝ) × (b → ℝ), ℂ) →L[ℂ] F,
        (∀ φ ψ, T' (φ.tensor ψ) = B φ ψ) → ∀ Φ, T' (monoCLM ℂ Φ) = T Φ := by
  obtain ⟨χ₁, hχ₁⟩ := exists_eqOn_one_of_subset_interior hK₁
  obtain ⟨χ₂, hχ₂⟩ := exists_eqOn_one_of_subset_interior hK₂
  have hKK₁ : K₁ ≤ K₁' := hK₁.trans interior_subset
  have hKK₂ : K₂ ≤ K₂' := hK₂.trans interior_subset
  have hKK : K₁ ×ˢ K₂ ≤ K₁' ×ˢ K₂' := prod_mono hKK₁ hKK₂
  -- The bilinear map on the tori and its continuity for the `C^k` norms.
  set B' := B.compl₁₂ (cutoffLift χ₁) (cutoffLift χ₂)
  have hB' := exists_bound_compl₁₂_cutoffLift B hB χ₁ χ₂
  obtain ⟨C', N', hC'N'⟩ := exists_norm_schwartzKernel_le B' hB'
  -- The kernel on `K₁ × K₂`: the torus kernel applied to the periodization.
  have hbound (Φ : 𝓓_{K₁ ×ˢ K₂}((a → ℝ) × (b → ℝ), ℂ)) :
      ‖schwartzKernel B' hB' (periodizeProd Φ)‖ ≤
        max C' 0 * (Finset.Iic N').sup (fun i ↦ N[ℂ]_{K₁ ×ˢ K₂, i}) Φ := by
    have hΦ := derivBound_periodizeProd hK₁' hK₂' hKK Φ N'
    have hΦ0 := hΦ.nonneg
    refine (hC'N' _ _ hΦ).trans ?_
    gcongr
    · exact le_max_left _ _
    · exact le_rfl
  let T : 𝓓_{K₁ ×ˢ K₂}((a → ℝ) × (b → ℝ), ℂ) →L[ℂ] F :=
    ContDiffMapSupportedIn.mkCLMtoNormedSpace ℂ (fun Φ ↦ schwartzKernel B' hB' (periodizeProd Φ))
      (fun Φ Ψ ↦ by simp only [map_add]) (fun c Φ ↦ by simp only [map_smul])
      ⟨Finset.Iic N', max C' 0, le_max_right _ _, hbound⟩
  -- `mkCLMtoNormedSpace` has no evaluation lemma; it evaluates by definition.
  have hT (Φ : 𝓓_{K₁ ×ˢ K₂}((a → ℝ) × (b → ℝ), ℂ)) :
      T Φ = schwartzKernel B' hB' (periodizeProd Φ) :=
    rfl
  refine ⟨T, fun φ ψ ↦ ?_, fun T' hT' Φ ↦ ?_⟩
  · rw [hT, periodizeProd_tensor]
    refine (schwartzKernel_tensor B' hB'
      ⟨periodize φ, periodize_mem_smoothFunctions φ.contDiff φ.hasCompactSupport⟩
      ⟨periodize ψ, periodize_mem_smoothFunctions ψ.contDiff ψ.hasCompactSupport⟩).trans ?_
    rw [LinearMap.compl₁₂_apply, cutoffLift_periodize hK₁' χ₁ hKK₁ hχ₁ φ,
      cutoffLift_periodize hK₂' χ₂ hKK₂ hχ₂ ψ]
  · -- `T'` induces a kernel of `B'` on the product torus, which is the torus kernel of `B'` by
    -- uniqueness there.
    have hUK : T'.toLinearMap ∘ₗ cutoffLiftProd (χ₁.tensor χ₂) = schwartzKernel B' hB' :=
      eq_schwartzKernel B' hB' (exists_bound_comp_cutoffLiftProd T' _) fun f g ↦ by
        rw [LinearMap.comp_apply, ContinuousLinearMap.coe_coe, cutoffLiftProd_tensor, hT',
          LinearMap.compl₁₂_apply]
    have hχ : EqOn (χ₁.tensor χ₂) 1 (K₁ ×ˢ K₂ : Compacts ((a → ℝ) × (b → ℝ))) := fun p hp ↦ by
      rw [ContDiffMapSupportedIn.tensor_apply, hχ₁ hp.1, hχ₂ hp.2, Pi.one_apply, Pi.one_apply,
        Pi.one_apply, mul_one]
    rw [hT, ← hUK, LinearMap.comp_apply, ContinuousLinearMap.coe_coe,
      cutoffLiftProd_periodizeProd hK₁' hK₂' (χ₁.tensor χ₂) hKK hχ Φ]

end LinearMap
