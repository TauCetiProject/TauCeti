/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Meromorphic.Divisor

/-!
# Counting zeros and poles in a region

`TauCeti.divisorCount` sums the signed meromorphic divisor in a region, while
`TauCeti.zeroCount` sums its positive multiplicities. The signed count is appropriate for
argument principles; the natural count records zeros without subtracting poles.

The sums use `finsum`, which returns zero on infinite support. The finite-support results
below justify their use on bounded regions whose closures lie in a meromorphic domain.
Infinite order contributes zero, following Mathlib's divisor convention, so these counts
do not detect functions which vanish identically near a point.
-/

public section

open Set

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {f : 𝕜 → E} {U R S : Set 𝕜}

namespace TauCeti

/-- The sum of zero multiplicities minus pole multiplicities in `R`, using the divisor on `U`.
On infinite support this takes the default value zero. -/
noncomputable def divisorCount (f : 𝕜 → E) (U R : Set 𝕜) : ℤ :=
  ∑ᶠ z ∈ R, MeromorphicOn.divisor f U z

/-- The sum of positive divisor multiplicities in `R`; poles and infinite order contribute zero.
On infinite support this takes the default value zero. -/
noncomputable def zeroCount (f : 𝕜 → E) (U R : Set 𝕜) : ℕ :=
  ∑ᶠ z ∈ R, (MeromorphicOn.divisor f U z).toNat

/-- The signed count is the finite sum of divisor values in the region. -/
theorem divisorCount_def (f : 𝕜 → E) (U R : Set 𝕜) :
    divisorCount f U R = ∑ᶠ z ∈ R, MeromorphicOn.divisor f U z := (rfl)

/-- The zero count is the finite sum of positive divisor multiplicities in the region. -/
theorem zeroCount_def (f : 𝕜 → E) (U R : Set 𝕜) :
    zeroCount f U R = ∑ᶠ z ∈ R, (MeromorphicOn.divisor f U z).toNat := (rfl)

/-- Finite signed divisor support also gives finite support for the positive multiplicities. -/
theorem zeroCount_support_finite
    (hR : (R ∩ Function.support (MeromorphicOn.divisor f U)).Finite) :
    (R ∩ Function.support (fun z ↦ (MeromorphicOn.divisor f U z).toNat)).Finite :=
  hR.subset (inter_subset_inter_right R (Function.support_comp_subset Int.toNat_zero _))

/-- The signed count of an empty region is zero. -/
@[simp] theorem divisorCount_empty (f : 𝕜 → E) (U : Set 𝕜) :
    divisorCount f U ∅ = 0 := by simp [divisorCount_def]

/-- The zero count of an empty region is zero. -/
@[simp] theorem zeroCount_empty (f : 𝕜 → E) (U : Set 𝕜) :
    zeroCount f U ∅ = 0 := by simp [zeroCount_def]

/-- Constant functions have zero signed count, including the identically zero function. -/
@[simp] theorem divisorCount_const (c : E) (U R : Set 𝕜) :
    divisorCount (fun _ ↦ c) U R = 0 := by simp [divisorCount_def]

/-- Constant functions have zero zero count, including the identically zero function. -/
@[simp] theorem zeroCount_const (c : E) (U R : Set 𝕜) :
    zeroCount (fun _ ↦ c) U R = 0 := by simp [zeroCount_def]

/-- Without negative divisor values, the signed count agrees with the natural zero count. -/
theorem divisorCount_eq_zeroCount
    (hnonneg : ∀ z ∈ R, 0 ≤ MeromorphicOn.divisor f U z) :
    divisorCount f U R = (zeroCount f U R : ℤ) := by
  have hcast := (Nat.castAddMonoidHom ℤ).map_finsum_of_injective
    Nat.cast_injective (fun z ↦ ∑ᶠ _ : z ∈ R, (MeromorphicOn.divisor f U z).toNat)
  simp only [AddMonoidHom.map_finsum_Prop, Nat.coe_castAddMonoidHom] at hcast
  rw [divisorCount_def, zeroCount_def, hcast]
  exact finsum_congr fun z ↦ finsum_congr fun hz ↦ (Int.toNat_of_nonneg (hnonneg z hz)).symm

/-- Counting over the whole domain of the divisor sums every divisor value, since the divisor is
supported in its domain. -/
theorem divisorCount_self (f : 𝕜 → E) (U : Set 𝕜) :
    divisorCount f U U = ∑ᶠ z, MeromorphicOn.divisor f U z := by
  rw [divisorCount_def, finsum_mem_def,
    indicator_eq_self.2 (MeromorphicOn.divisor f U).supportWithinDomain]

/-- The signed count is additive on disjoint regions with finite divisor support. -/
theorem divisorCount_union (hRS : Disjoint R S)
    (hR : (R ∩ Function.support (MeromorphicOn.divisor f U)).Finite)
    (hS : (S ∩ Function.support (MeromorphicOn.divisor f U)).Finite) :
    divisorCount f U (R ∪ S) = divisorCount f U R + divisorCount f U S :=
  finsum_mem_union' hRS hR hS

/-- The zero count is additive on disjoint regions with finite positive support. -/
theorem zeroCount_union (hRS : Disjoint R S)
    (hR : (R ∩ Function.support (fun z ↦ (MeromorphicOn.divisor f U z).toNat)).Finite)
    (hS : (S ∩ Function.support (fun z ↦ (MeromorphicOn.divisor f U z).toNat)).Finite) :
    zeroCount f U (R ∪ S) = zeroCount f U R + zeroCount f U S :=
  finsum_mem_union' hRS hR hS

/-- Enlargement splits the zero count into the original region and the added region. -/
theorem zeroCount_add_sdiff (hRS : R ⊆ S)
    (hS : (S ∩ Function.support (fun z ↦ (MeromorphicOn.divisor f U z).toNat)).Finite) :
    zeroCount f U R + zeroCount f U (S \ R) = zeroCount f U S :=
  finsum_mem_add_sdiff' hRS hS

/-- The zero count is monotone under enlargement, even when the function has poles. -/
theorem zeroCount_mono (hRS : R ⊆ S)
    (hS : (S ∩ Function.support (fun z ↦ (MeromorphicOn.divisor f U z).toNat)).Finite) :
    zeroCount f U R ≤ zeroCount f U S := by
  rw [← zeroCount_add_sdiff hRS hS]
  exact Nat.le_add_right _ _

/-- The zero count over `S`, with respect to any domain `U`, is at most the count over a larger
region `T` with respect to a domain `V ⊇ T` of meromorphy. The divisors on `U` and `V` agree on
`U ∩ V` when `f` is meromorphic on both, and the divisor on `U` vanishes otherwise. -/
theorem zeroCount_le_zeroCount_of_subset {V T : Set 𝕜} (hf : MeromorphicOn f V) (hST : S ⊆ T)
    (hTV : T ⊆ V)
    (hT : (T ∩ Function.support (fun z ↦ (MeromorphicOn.divisor f V z).toNat)).Finite) :
    zeroCount f U S ≤ zeroCount f V T := by
  have hle : ∀ z ∈ S, (MeromorphicOn.divisor f U z).toNat ≤
      (MeromorphicOn.divisor f V z).toNat := by
    intro z hz
    by_cases hU : MeromorphicOn f U
    · by_cases hzU : z ∈ U
      · rw [hU.divisor_apply hzU, hf.divisor_apply (hTV (hST hz))]
      · simp [hzU]
    · simp [hU]
  have hS := hT.subset (inter_subset_inter_left _ hST)
  refine le_trans ?_ (zeroCount_mono hST hT)
  have hsub : (hS.toFinset : Set 𝕜) ⊆ S := fun z hz ↦ (hS.mem_toFinset.1 hz).1
  rw [zeroCount_def, zeroCount_def,
    finsum_mem_eq_sum_of_subset _ (t := hS.toFinset) (fun z hz ↦ hS.mem_toFinset.2
      ⟨hz.1, fun h ↦ hz.2 (Nat.eq_zero_of_le_zero (h ▸ hle z hz.1))⟩) hsub,
    finsum_mem_eq_sum_of_subset _ (t := hS.toFinset) (fun z hz ↦ hS.mem_toFinset.2 hz) hsub]
  exact Finset.sum_le_sum fun z hz ↦ hle z (hsub hz)

/-- For `f` analytic on a compact set `K`, the zero count over any `S ⊆ K`, with respect to any
domain `U`, is at most the total divisor of `f` on `K`. This is how bounds for divisor sums,
such as Jensen's bound on a disc, become bounds for zero counts. -/
theorem _root_.AnalyticOnNhd.zeroCount_le_finsum_divisor {K : Set 𝕜}
    (hf : AnalyticOnNhd 𝕜 f K) (hK : IsCompact K) (U : Set 𝕜) (hS : S ⊆ K) :
    (zeroCount f U S : ℤ) ≤ ∑ᶠ z, MeromorphicOn.divisor f K z := by
  have hfin : (K ∩ Function.support (fun z ↦ (MeromorphicOn.divisor f K z).toNat)).Finite :=
    zeroCount_support_finite <|
      hf.meromorphicOn.divisor_finite_inter_support_of_isCompact hK subset_rfl subset_rfl
  rw [← divisorCount_self, divisorCount_eq_zeroCount fun z _ ↦
    MeromorphicOn.AnalyticOnNhd.divisor_nonneg hf z]
  exact_mod_cast zeroCount_le_zeroCount_of_subset hf.meromorphicOn hS subset_rfl hfin

/-- A finite zero count vanishes exactly when each positive multiplicity vanishes. -/
theorem zeroCount_eq_zero_iff
    (hR : (R ∩ Function.support (fun z ↦ (MeromorphicOn.divisor f U z).toNat)).Finite) :
    zeroCount f U R = 0 ↔ ∀ z ∈ R, (MeromorphicOn.divisor f U z).toNat = 0 := by
  classical
  rw [zeroCount_def, finsum_mem_eq_sum _ hR, Finset.sum_eq_zero_iff]
  simp only [Finite.mem_toFinset, mem_inter_iff, Function.mem_support]
  constructor
  · intro h z hz
    by_contra hne
    exact hne (h z ⟨hz, hne⟩)
  · intro h z hz
    exact h z hz.1

/-- An enlargement leaves the count unchanged exactly when no positive multiplicity is added. -/
theorem zeroCount_eq_iff_of_subset (hRS : R ⊆ S)
    (hS : (S ∩ Function.support (fun z ↦ (MeromorphicOn.divisor f U z).toNat)).Finite) :
    zeroCount f U R = zeroCount f U S ↔
      ∀ z ∈ S \ R, (MeromorphicOn.divisor f U z).toNat = 0 := by
  have hdiff : ((S \ R) ∩ Function.support (fun z ↦ (MeromorphicOn.divisor f U z).toNat)).Finite :=
    hS.subset fun _ hz ↦ ⟨hz.1.1, hz.2⟩
  rw [← zeroCount_eq_zero_iff hdiff, ← zeroCount_add_sdiff hRS hS]
  omega

/-- If divisor values on the added region are nonnegative, unchanged count means zero divisor
on that difference. No regularity of the chosen values at removable singularities is needed. -/
theorem zeroCount_eq_iff_divisor_eq_zero (hRS : R ⊆ S)
    (hS : (S ∩ Function.support (fun z ↦ (MeromorphicOn.divisor f U z).toNat)).Finite)
    (hnonneg : ∀ z ∈ S \ R, 0 ≤ MeromorphicOn.divisor f U z) :
    zeroCount f U R = zeroCount f U S ↔ ∀ z ∈ S \ R, MeromorphicOn.divisor f U z = 0 := by
  rw [zeroCount_eq_iff_of_subset hRS hS]
  exact forall₂_congr fun z hz ↦ by
    have := hnonneg z hz
    omega

end TauCeti
