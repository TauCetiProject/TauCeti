/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.IntegralLattice.Characteristic.ParityKernel
public import TauCeti.LinearAlgebra.IntegralLattice.Examples
public import TauCeti.LinearAlgebra.IntegralLattice.Orthogonal.Sum
public import TauCeti.LinearAlgebra.IntegralLattice.RankOne.Basic
public import TauCeti.LinearAlgebra.IntegralLattice.Unit
import TauCeti.Data.Int.MulPred

/-!
# The standard odd unimodular lattice `I_{r, s}` and uniqueness of its even two-neighbors

`signedUnitLattice r s` (`I_{r, s}`) is `ℤ^{r + s}` inside `ℚ^{r + s}` (indexed by `Fin r ⊕ Fin s`)
with Gram matrix `diag(+1^r, -1^s)`, isometric to `I_r ⊕ (-I_s)`. The all-ones vector is
characteristic of norm `(r : ℤ) - s`; when `0 < r + s`, an even two-neighbor exists iff
`8 ∣ (r : ℤ) - s`, and coordinate sign-flip makes the even two-neighbor unique up to isometry.
In signature `(1, 0, 1)`, `signedUnitLattice 1 1` is isometric to `⟨1⟩ ⊕ ⟨-1⟩`, its canonical even
two-neighbor `evenSignedUnitNeighbor 1 1` is isometric to `hyperbolicPlane`, and for any even
lattice `Y`, `Y ⊕ hyperbolicPlane` is isometric to an even two-neighbor of `Y ⊕ I_{1, 1}`.

## References

* J.-P. Serre, *A Course in Arithmetic*, Chapter V, §2.2.
* J. Milnor and D. Husemoller, *Symmetric Bilinear Forms*, Chapter II, §§2–5.
-/

public section

open Module

namespace TauCeti.IntegralLattice

private abbrev signedUnitMatrix (r s : ℕ) : Matrix (Fin r ⊕ Fin s) (Fin r ⊕ Fin s) ℤ :=
  Matrix.diagonal (Sum.elim (fun _ ↦ 1) (fun _ ↦ -1))

/-- The standard signed unit lattice `I_{r, s}` on `Fin r ⊕ Fin s → ℚ`. -/
noncomputable def signedUnitLattice (r s : ℕ) : IntegralLattice (Fin r ⊕ Fin s → ℚ) :=
  ofGramMatrix (Pi.basisFun ℚ (Fin r ⊕ Fin s)) (signedUnitMatrix r s) (Matrix.isSymm_diagonal _)

/-- Membership in `signedUnitLattice r s` means all coordinates are integers. -/
@[simp] theorem mem_signedUnitLattice_carrier_iff (r s : ℕ) (x : Fin r ⊕ Fin s → ℚ) :
    x ∈ (signedUnitLattice r s).carrier ↔ ∀ k, ∃ z : ℤ, (z : ℚ) = x k :=
  mem_ofGramMatrix_basisFun_carrier_iff (signedUnitMatrix r s) (Matrix.isSymm_diagonal _) x

/-- The bilinear form of `signedUnitLattice r s` is the signed coordinate dot product. -/
@[simp] theorem signedUnitLattice_form_apply (r s : ℕ) (x y : Fin r ⊕ Fin s → ℚ) :
    (signedUnitLattice r s).form x y =
      (∑ i : Fin r, x (.inl i) * y (.inl i)) - ∑ j : Fin s, x (.inr j) * y (.inr j) := by
  rw [signedUnitLattice, form_ofGramMatrix_basisFun_apply]
  have hrow (k : Fin r ⊕ Fin s) : (∑ l, ((signedUnitMatrix r s k l : ℤ) : ℚ) * y l) =
      ((Sum.elim (fun _ ↦ (1 : ℤ)) (fun _ ↦ -1) k : ℤ) : ℚ) * y k := by
    rw [Finset.sum_eq_single k (fun l _ hlk ↦ by
      simp [signedUnitMatrix, Matrix.diagonal_apply_ne _ hlk.symm]) (by simp)]
    simp [signedUnitMatrix]
  simp_rw [hrow, Fintype.sum_sum_type]; simp [sub_eq_add_neg]

/-- The quadratic norm on `signedUnitLattice r s` is `(∑ i, xᵢ²) - ∑ j, yⱼ²`. -/
@[simp] theorem signedUnitLattice_norm_apply (r s : ℕ) (x : Fin r ⊕ Fin s → ℚ) :
    (signedUnitLattice r s).norm x =
      (∑ i : Fin r, x (.inl i) ^ 2) - ∑ j : Fin s, x (.inr j) ^ 2 := by
  simp only [norm_apply, signedUnitLattice_form_apply, sq]

/-- `signedUnitLattice r s` has rank `r + s`. -/
@[simp] theorem finrank_signedUnitLattice (r s : ℕ) :
    Module.finrank ℤ (signedUnitLattice r s) = r + s := by
  rw [(signedUnitLattice r s).finrank_carrier]; simp

/-- The canonical isometry `I_r ⊕ (-I_s) ≅ I_{r, s}`. -/
noncomputable def unitLatticeOrthogonalSumIsometrySignedUnitLattice (r s : ℕ) :
    Isometry ((unitLattice (Fin r)).orthogonalSum (-(unitLattice (Fin s))))
      (signedUnitLattice r s) where
  toLinearEquiv := (LinearEquiv.sumArrowLequivProdArrow (Fin r) (Fin s) ℚ ℚ).symm
  map_app' p q := by
    change (signedUnitLattice r s).form (Sum.elim p.1 p.2) (Sum.elim q.1 q.2) = _
    simp [signedUnitLattice_form_apply, orthogonalSum_form, LinearMap.BilinForm.prod_apply,
      sub_eq_add_neg]
  map_carrier := Submodule.ext fun x ↦ by
    rw [Submodule.mem_map_equiv, orthogonalSum_carrier, Submodule.mem_prod, neg_carrier,
      mem_unitLattice_carrier_iff, mem_unitLattice_carrier_iff, mem_signedUnitLattice_carrier_iff]
    exact ⟨fun ⟨h1, h2⟩ k ↦ Sum.casesOn k h1 h2, fun h ↦ ⟨fun i ↦ h (.inl i), fun j ↦ h (.inr j)⟩⟩

/-- `unitLatticeOrthogonalSumIsometrySignedUnitLattice` acts as `Sum.elim`. -/
@[simp] theorem unitLatticeOrthogonalSumIsometrySignedUnitLattice_apply (r s : ℕ)
    (p : (Fin r → ℚ) × (Fin s → ℚ)) :
    unitLatticeOrthogonalSumIsometrySignedUnitLattice r s p = Sum.elim p.1 p.2 := (rfl)

/-- `signedUnitLattice r s` has signed determinant `(-1) ^ s`. -/
@[simp] theorem signedUnitLattice_determinant (r s : ℕ) :
    (signedUnitLattice r s).determinant = (-1) ^ s := by
  rw [← (unitLatticeOrthogonalSumIsometrySignedUnitLattice r s).determinant_eq,
    determinant_orthogonalSum, unitLattice_determinant, determinant_neg, unitLattice_determinant,
    finrank_unitLattice, Fintype.card_fin]; ring

/-- `signedUnitLattice r s` has discriminant `1`. -/
@[simp] theorem signedUnitLattice_discriminant (r s : ℕ) :
    (signedUnitLattice r s).discriminant = 1 := by simp [discriminant_def]

/-- `signedUnitLattice r s` is nondegenerate for all `r` and `s`. -/
instance instIsNondegenerateSignedUnitLattice (r s : ℕ) :
    (signedUnitLattice r s).IsNondegenerate :=
  ⟨(signedUnitLattice r s).determinant_ne_zero_iff.mp (by simp)⟩

/-- `signedUnitLattice r s` is unimodular for all `r` and `s`. -/
theorem isUnimodular_signedUnitLattice (r s : ℕ) : (signedUnitLattice r s).IsUnimodular :=
  (signedUnitLattice r s).isUnimodular_iff_discriminant_eq_one.mpr (by simp)

/-- `signedUnitLattice r s` has signature `(r, 0, s)`. -/
@[simp] theorem signedUnitLattice_signature (r s : ℕ) :
    (signedUnitLattice r s).signature = (r, 0, s) := by
  rw [← (unitLatticeOrthogonalSumIsometrySignedUnitLattice r s).signature_eq,
    signature_orthogonalSum]
  have hp := unitLattice_signature (Fin r); have hn := signature_neg (unitLattice (Fin s))
  have hs := unitLattice_signature (Fin s); rw [Fintype.card_fin] at hp hs
  simp only [signature, Prod.mk.injEq] at hp hs hn ⊢; omega

/-- The canonical isometry `(rankOne 1).orthogonalSum (rankOne (-1)) ≅ signedUnitLattice 1 1`. -/
noncomputable def rankOneOrthogonalSumIsometrySignedUnitLattice :
    Isometry ((rankOne 1).orthogonalSum (rankOne (-1))) (signedUnitLattice 1 1) where
  toLinearEquiv :=
    ((LinearEquiv.funUnique (Fin 1) ℚ ℚ).symm.prodCongr
      (LinearEquiv.funUnique (Fin 1) ℚ ℚ).symm).trans
      (LinearEquiv.sumArrowLequivProdArrow (Fin 1) (Fin 1) ℚ ℚ).symm
  map_app' p q := by
    change (signedUnitLattice 1 1).form (Sum.elim (fun _ ↦ p.1) (fun _ ↦ p.2))
      (Sum.elim (fun _ ↦ q.1) (fun _ ↦ q.2)) = _
    simp [signedUnitLattice_form_apply, orthogonalSum_form, LinearMap.BilinForm.prod_apply]; ring
  map_carrier := Submodule.ext fun x ↦ by
    rw [Submodule.mem_map_equiv, orthogonalSum_carrier, Submodule.mem_prod,
      mem_rankOne_carrier_iff, mem_rankOne_carrier_iff, mem_signedUnitLattice_carrier_iff]
    refine ⟨fun ⟨h0, h1⟩ k ↦ ?_, fun h ↦ ⟨h (.inl 0), h (.inr 0)⟩⟩
    rcases k with i | j
    exacts [Subsingleton.elim i 0 ▸ h0, Subsingleton.elim j 0 ▸ h1]

/-- `rankOneOrthogonalSumIsometrySignedUnitLattice` sends `(a, b)` to
`Sum.elim (fun _ ↦ a) (fun _ ↦ b)`. -/
@[simp] theorem rankOneOrthogonalSumIsometrySignedUnitLattice_apply (p : ℚ × ℚ) :
    rankOneOrthogonalSumIsometrySignedUnitLattice p = Sum.elim (fun _ ↦ p.1) (fun _ ↦ p.2) :=
  (rfl)

/-- Membership in `(signedUnitLattice r s).evenSublattice` means integral coordinates with
even coordinate sum. -/
theorem mem_evenSublattice_signedUnitLattice_carrier_iff (r s : ℕ) (x : Fin r ⊕ Fin s → ℚ) :
    x ∈ (signedUnitLattice r s).evenSublattice.carrier ↔
      (∀ k, ∃ z : ℤ, (z : ℚ) = x k) ∧
        ∃ m : ℤ, (∑ i : Fin r, x (.inl i)) + ∑ j : Fin s, x (.inr j) = 2 * m := by
  have hev (a : ℤ) : (∃ k : ℤ, (a : ℚ) = 2 * k) ↔ Even a :=
    ⟨fun ⟨k, hk⟩ ↦ ⟨k, Int.cast_injective (α := ℚ) (by push_cast; linarith)⟩,
      fun ⟨k, hk⟩ ↦ ⟨k, by exact_mod_cast (by omega : a = 2 * k)⟩⟩
  rw [(signedUnitLattice r s).mem_evenSublattice_carrier_iff_exists_norm,
    mem_signedUnitLattice_carrier_iff]
  refine and_congr_right fun hxZ ↦ ?_
  choose z hz using hxZ
  have hnorm : (signedUnitLattice r s).norm x =
      (((∑ i : Fin r, z (.inl i) ^ 2) - ∑ j : Fin s, z (.inr j) ^ 2 : ℤ) : ℚ) := by
    simp [signedUnitLattice_norm_apply, ← hz]
  have hsum : (∑ i : Fin r, x (.inl i)) + ∑ j : Fin s, x (.inr j) =
      (((∑ i : Fin r, z (.inl i)) + ∑ j : Fin s, z (.inr j) : ℤ) : ℚ) := by
    simp [← hz]
  rw [hnorm, hsum, hev, hev]
  have hdiff : Even (((∑ i : Fin r, z (.inl i) ^ 2) - ∑ j : Fin s, z (.inr j) ^ 2) -
      ((∑ i : Fin r, z (.inl i)) + ∑ j : Fin s, z (.inr j))) := by
    have heq : ((∑ i : Fin r, z (.inl i) ^ 2) - ∑ j : Fin s, z (.inr j) ^ 2) -
        ((∑ i : Fin r, z (.inl i)) + ∑ j : Fin s, z (.inr j)) =
        (∑ i : Fin r, (z (.inl i) ^ 2 - z (.inl i))) -
          ∑ j : Fin s, (z (.inr j) ^ 2 - z (.inr j) + 2 * z (.inr j)) := by
      simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum]; ring
    rw [heq]
    exact (even_iff_two_dvd.mpr (Finset.dvd_sum fun _ _ ↦ Int.two_dvd_sq_sub_self _)).sub
      (even_iff_two_dvd.mpr (Finset.dvd_sum fun _ _ ↦ dvd_add (Int.two_dvd_sq_sub_self _)
        (dvd_mul_right 2 _)))
  exact ⟨fun h ↦ by simpa using h.sub hdiff, fun h ↦ by simpa using h.add hdiff⟩

/-- The `k`-th standard coordinate vector in `signedUnitLattice r s`. -/
def signedUnitBasisVector (r s : ℕ) (k : Fin r ⊕ Fin s) : signedUnitLattice r s :=
  ⟨Pi.single k 1, (mem_signedUnitLattice_carrier_iff r s _).mpr fun l ↦ by
    by_cases h : l = k; · subst h; exact ⟨1, by simp⟩
    · exact ⟨0, by simp [h]⟩⟩

/-- Ambient coercion of `signedUnitBasisVector`. -/
@[simp] theorem coe_signedUnitBasisVector (r s : ℕ) (k : Fin r ⊕ Fin s) :
    (signedUnitBasisVector r s k : Fin r ⊕ Fin s → ℚ) = Pi.single k 1 := (rfl)

private theorem sum_pi_single_sq {α σ : Type*} [Fintype α] [DecidableEq σ] (f : α → σ)
    (hf : Function.Injective f) (i : α) :
    (∑ i' : α, (Pi.single (M := fun _ ↦ ℚ) (f i) 1 (f i')) ^ 2) = 1 := by
  rw [Finset.sum_eq_single i (fun i' _ h ↦ by simp [Pi.single_eq_of_ne (hf.ne h)]) (by simp)]; simp

/-- Each positive-index standard basis vector of `signedUnitLattice r s` has integral norm `1`. -/
@[simp] theorem integralNorm_signedUnitBasisVector_inl (r s : ℕ) (i : Fin r) :
    (signedUnitLattice r s).integralNorm (signedUnitBasisVector r s (.inl i)) = 1 :=
  Int.cast_injective (α := ℚ) (by
    rw [integralNorm_cast, signedUnitLattice_norm_apply, coe_signedUnitBasisVector,
      sum_pi_single_sq Sum.inl Sum.inl_injective i, Finset.sum_eq_zero fun j _ ↦ by simp]; norm_num)

/-- Each negative-index standard basis vector of `signedUnitLattice r s` has integral norm `-1`. -/
@[simp] theorem integralNorm_signedUnitBasisVector_inr (r s : ℕ) (j : Fin s) :
    (signedUnitLattice r s).integralNorm (signedUnitBasisVector r s (.inr j)) = -1 :=
  Int.cast_injective (α := ℚ) (by
    rw [integralNorm_cast, signedUnitLattice_norm_apply, coe_signedUnitBasisVector,
      Finset.sum_eq_zero fun i _ ↦ by simp, sum_pi_single_sq Sum.inr Sum.inr_injective j]; norm_num)

/-- Every standard basis vector of `signedUnitLattice r s` has odd integral norm. -/
theorem odd_integralNorm_signedUnitBasisVector (r s : ℕ) (k : Fin r ⊕ Fin s) :
    Odd ((signedUnitLattice r s).integralNorm (signedUnitBasisVector r s k)) := by
  rcases k with i | j <;> simp [odd_one]

/-- `signedUnitLattice r s` is even if and only if `r = 0` and `s = 0`. -/
@[simp] theorem isEven_signedUnitLattice_iff (r s : ℕ) :
    (signedUnitLattice r s).IsEven ↔ r = 0 ∧ s = 0 := by
  have hno (k : Fin r ⊕ Fin s) (h : (signedUnitLattice r s).IsEven) : False :=
    Int.not_odd_iff_even.mpr (((signedUnitLattice r s).even_integralNorm_iff _).mpr
      ((signedUnitLattice r s).isEven_iff_forall_norm.mp h (signedUnitBasisVector r s k)))
      (odd_integralNorm_signedUnitBasisVector r s k)
  refine ⟨fun h ↦ ⟨by_contra fun hr ↦ hno (.inl ⟨0, Nat.pos_of_ne_zero hr⟩) h,
    by_contra fun hs ↦ hno (.inr ⟨0, Nat.pos_of_ne_zero hs⟩) h⟩, ?_⟩
  rintro ⟨rfl, rfl⟩; exact (signedUnitLattice 0 0).isEven_iff_forall_norm.mpr fun _ ↦ ⟨0, by simp⟩

/-- `signedUnitLattice r s` is odd whenever `0 < r + s`. -/
theorem not_isEven_signedUnitLattice_of_pos {r s : ℕ} (h : 0 < r + s) :
    ¬ (signedUnitLattice r s).IsEven := by rw [isEven_signedUnitLattice_iff]; omega

/-- The all-ones vector `(1, …, 1)` in `signedUnitLattice r s`. -/
def signedUnitCharacteristicVector (r s : ℕ) : signedUnitLattice r s :=
  ⟨fun _ ↦ 1, (mem_signedUnitLattice_carrier_iff r s _).mpr fun _ ↦ ⟨1, rfl⟩⟩

/-- Ambient coercion of `signedUnitCharacteristicVector`. -/
@[simp] theorem coe_signedUnitCharacteristicVector (r s : ℕ) :
    (signedUnitCharacteristicVector r s : Fin r ⊕ Fin s → ℚ) = fun _ ↦ 1 := (rfl)

/-- The all-ones vector is a characteristic vector of `signedUnitLattice r s`. -/
theorem isCharacteristicVector_signedUnitCharacteristicVector (r s : ℕ) :
    (signedUnitLattice r s).IsCharacteristicVector (signedUnitCharacteristicVector r s) := by
  rw [(signedUnitLattice r s).isCharacteristicVector_iff]; intro y
  choose z hz using (mem_signedUnitLattice_carrier_iff r s y).mp y.2
  have hsub : (signedUnitLattice r s).integralNorm y -
      (signedUnitLattice r s).integralForm (signedUnitCharacteristicVector r s) y =
      (∑ i : Fin r, (z (.inl i) ^ 2 - z (.inl i))) -
        ∑ j : Fin s, (z (.inr j) ^ 2 - z (.inr j)) := Int.cast_injective (α := ℚ) (by
    simp [integralNorm_cast, integralForm_cast, Finset.sum_sub_distrib, ← hz]; ring)
  exact Int.modEq_iff_dvd.mpr (hsub ▸ dvd_sub
    (Finset.dvd_sum fun _ _ ↦ Int.two_dvd_sq_sub_self _)
    (Finset.dvd_sum fun _ _ ↦ Int.two_dvd_sq_sub_self _))

/-- The all-ones characteristic vector of `signedUnitLattice r s` has norm `(r : ℤ) - s`. -/
@[simp] theorem integralNorm_signedUnitCharacteristicVector (r s : ℕ) :
    (signedUnitLattice r s).integralNorm (signedUnitCharacteristicVector r s) = (r : ℤ) - s :=
  Int.cast_injective (α := ℚ) (by simp [integralNorm_cast])

private def signedUnitSignFlipEquiv (r s : ℕ) (k : Fin r ⊕ Fin s) :
    (Fin r ⊕ Fin s → ℚ) ≃ₗ[ℚ] (Fin r ⊕ Fin s → ℚ) where
  toFun x := Function.update x k (-x k)
  invFun x := Function.update x k (-x k)
  map_add' x y := by ext l; by_cases h : l = k <;> simp [h, add_comm]
  map_smul' c x := by ext l; by_cases h : l = k <;> simp [h]
  left_inv x := by ext l; by_cases h : l = k <;> simp [h]
  right_inv x := by ext l; by_cases h : l = k <;> simp [h]

private theorem form_signedUnitSignFlipEquiv (r s : ℕ) (k : Fin r ⊕ Fin s)
    (x y : Fin r ⊕ Fin s → ℚ) :
    (signedUnitLattice r s).form (signedUnitSignFlipEquiv r s k x)
      (signedUnitSignFlipEquiv r s k y) = (signedUnitLattice r s).form x y := by
  have hmul (l) : signedUnitSignFlipEquiv r s k x l * signedUnitSignFlipEquiv r s k y l =
      x l * y l := by
    dsimp only [signedUnitSignFlipEquiv, LinearEquiv.coe_mk, LinearMap.coe_mk, AddHom.coe_mk]
    by_cases h : l = k; · subst h; simp
    · simp [h]
  simp only [signedUnitLattice_form_apply, hmul]

private theorem mem_evenSublattice_signedUnitSignFlipEquiv_iff (r s : ℕ) (k : Fin r ⊕ Fin s)
    (x : Fin r ⊕ Fin s → ℚ) :
    signedUnitSignFlipEquiv r s k x ∈ (signedUnitLattice r s).evenSublattice.carrier ↔
      x ∈ (signedUnitLattice r s).evenSublattice.carrier := by
  have hdir (u) (hu : u ∈ (signedUnitLattice r s).evenSublattice.carrier) :
      signedUnitSignFlipEquiv r s k u ∈ (signedUnitLattice r s).evenSublattice.carrier := by
    have huL := (signedUnitLattice r s).evenSublattice_carrier_le hu
    have hfu : signedUnitSignFlipEquiv r s k u ∈ (signedUnitLattice r s).carrier := by
      rw [mem_signedUnitLattice_carrier_iff] at huL ⊢; intro l; obtain ⟨z, hz⟩ := huL l
      by_cases h : l = k; · subst h; exact ⟨-z, by simp [signedUnitSignFlipEquiv, ← hz]⟩
      · exact ⟨z, by simpa [signedUnitSignFlipEquiv, h] using hz⟩
    rw [(signedUnitLattice r s).mem_evenSublattice_carrier_iff ⟨_, huL⟩,
      (signedUnitLattice r s).even_integralNorm_iff] at hu
    exact ((signedUnitLattice r s).mem_evenSublattice_carrier_iff ⟨_, hfu⟩).mpr
      (((signedUnitLattice r s).even_integralNorm_iff ⟨_, hfu⟩).mpr
        (by simpa only [Submodule.coe_mk, norm_apply, form_signedUnitSignFlipEquiv] using hu))
  exact ⟨fun h ↦ (signedUnitSignFlipEquiv r s k).left_inv x ▸ hdir _ h, hdir x⟩

/-- Divisibility of `(r : ℤ) - s` by `8` gives `8 ∣ integralNorm w`. -/
theorem eight_dvd_integralNorm_signedUnitCharacteristicVector {r s : ℕ} (h8 : 8 ∣ (r : ℤ) - s) :
    8 ∣ (signedUnitLattice r s).integralNorm (signedUnitCharacteristicVector r s) := by simpa

/-- The canonical even overlattice `I_{r, s}^+` when `8 ∣ (r : ℤ) - s`. -/
noncomputable def evenSignedUnitNeighbor (r s : ℕ) (h8 : 8 ∣ (r : ℤ) - s) :
    IntegralLattice (Fin r ⊕ Fin s → ℚ) :=
  (signedUnitLattice r s).halfCharacteristicOverlattice (isUnimodular_signedUnitLattice r s)
    (isCharacteristicVector_signedUnitCharacteristicVector r s)
    (eight_dvd_integralNorm_signedUnitCharacteristicVector h8)

/-- `evenSignedUnitNeighbor r s h8` shares the ambient bilinear form of `signedUnitLattice r s`. -/
@[simp] theorem evenSignedUnitNeighbor_form (r s : ℕ) (h8 : 8 ∣ (r : ℤ) - s) :
    (evenSignedUnitNeighbor r s h8).form = (signedUnitLattice r s).form :=
  (signedUnitLattice r s).halfCharacteristicOverlattice_form ..

/-- `evenSignedUnitNeighbor r s h8` is an even integral lattice. -/
theorem isEven_evenSignedUnitNeighbor (r s : ℕ) (h8 : 8 ∣ (r : ℤ) - s) :
    (evenSignedUnitNeighbor r s h8).IsEven :=
  (signedUnitLattice r s).isEven_halfCharacteristicOverlattice ..

/-- `evenSignedUnitNeighbor r s h8` is unimodular for all `r` and `s` with `8 ∣ (r : ℤ) - s`. -/
theorem isUnimodular_evenSignedUnitNeighbor (r s : ℕ) (h8 : 8 ∣ (r : ℤ) - s) :
    (evenSignedUnitNeighbor r s h8).IsUnimodular :=
  (signedUnitLattice r s).isUnimodular_halfCharacteristicOverlattice ..

/-- `evenSignedUnitNeighbor r s h8` is a Kneser two-neighbor of `signedUnitLattice r s`. -/
theorem isNeighbor_evenSignedUnitNeighbor {r s : ℕ} (hpos : 0 < r + s) (h8 : 8 ∣ (r : ℤ) - s) :
    (signedUnitLattice r s).IsNeighbor (evenSignedUnitNeighbor r s h8) 2 :=
  (signedUnitLattice r s).isNeighbor_halfCharacteristicOverlattice
    (isUnimodular_signedUnitLattice r s) (not_isEven_signedUnitLattice_of_pos hpos) _ _

/-- `evenSignedUnitNeighbor r s h8` has signature `(r, 0, s)`. -/
@[simp] theorem evenSignedUnitNeighbor_signature (r s : ℕ) (h8 : 8 ∣ (r : ℤ) - s) :
    (evenSignedUnitNeighbor r s h8).signature = (r, 0, s) := by
  rw [signature_eq_of_form_eq (evenSignedUnitNeighbor_form r s h8), signedUnitLattice_signature]

/-- Flipping coordinate `k` maps `evenSignedUnitNeighbor` to the shifted overlattice. -/
noncomputable def signedUnitHalfCharacteristicIsometryShifted (r s : ℕ) (h8 : 8 ∣ (r : ℤ) - s)
    (k : Fin r ⊕ Fin s) :
    Isometry (evenSignedUnitNeighbor r s h8)
      ((signedUnitLattice r s).shiftedHalfCharacteristicOverlattice
        (isUnimodular_signedUnitLattice r s)
        (isCharacteristicVector_signedUnitCharacteristicVector r s)
        (eight_dvd_integralNorm_signedUnitCharacteristicVector h8)
        (signedUnitBasisVector r s k)) where
  toLinearEquiv := signedUnitSignFlipEquiv r s k
  map_app' x y := by
    rw [evenSignedUnitNeighbor_form, shiftedHalfCharacteristicOverlattice_form]
    exact form_signedUnitSignFlipEquiv r s k x y
  map_carrier := Submodule.ext fun x ↦ by
    rw [Submodule.mem_map_equiv, LinearEquiv.restrictScalars_symm_apply,
      show (signedUnitSignFlipEquiv r s k).symm = signedUnitSignFlipEquiv r s k from rfl,
      evenSignedUnitNeighbor, (signedUnitLattice r s).mem_halfCharacteristicOverlattice_carrier_iff,
      (signedUnitLattice r s).mem_shiftedHalfCharacteristicOverlattice_carrier_iff,
      mem_evenSublattice_signedUnitSignFlipEquiv_iff]
    refine or_congr Iff.rfl ?_
    rw [← mem_evenSublattice_signedUnitSignFlipEquiv_iff r s k (x - _), map_sub]
    let e := (signedUnitBasisVector r s k : Fin r ⊕ Fin s → ℚ)
    let w := (signedUnitCharacteristicVector r s : Fin r ⊕ Fin s → ℚ)
    have hdiff : signedUnitSignFlipEquiv r s k (e + (1 / 2 : ℚ) • w) - (1 / 2 : ℚ) • w =
        -((2 : ℤ) • e) := by
      ext l; dsimp only [e, w, signedUnitSignFlipEquiv, LinearEquiv.coe_mk, LinearMap.coe_mk,
        AddHom.coe_mk, coe_signedUnitBasisVector, coe_signedUnitCharacteristicVector, Pi.add_apply,
        Pi.sub_apply, Pi.smul_apply, Pi.neg_apply]
      by_cases hlk : l = k; · subst hlk; simp [smul_eq_mul, zsmul_eq_mul]; norm_num
      · simp [Function.update_of_ne hlk, Pi.single_eq_of_ne hlk]
    have he2 : ((2 : ℤ) • signedUnitBasisVector r s k : Fin r ⊕ Fin s → ℚ) ∈
        (signedUnitLattice r s).evenSublattice.carrier :=
      ((signedUnitLattice r s).mem_evenSublattice_carrier_iff _).mpr
        (((signedUnitLattice r s).mem_evenSubmodule_iff _).mp
          ((signedUnitLattice r s).two_smul_mem_evenSubmodule _))
    rw [show signedUnitSignFlipEquiv r s k x - signedUnitSignFlipEquiv r s k (e + (1 / 2 : ℚ) • w) =
        (signedUnitSignFlipEquiv r s k x - (1 / 2 : ℚ) • w) -
          (signedUnitSignFlipEquiv r s k (e + (1 / 2 : ℚ) • w) - (1 / 2 : ℚ) • w) by abel,
      hdiff, Submodule.sub_mem_iff_left _ ((signedUnitLattice r s).evenSublattice.carrier.neg_mem
        he2)]

/-- Every even Kneser two-neighbor of `signedUnitLattice r s` forces `8 ∣ (r : ℤ) - s` and is
integrally isometric to `evenSignedUnitNeighbor r s h8`. -/
theorem nonempty_isometry_evenSignedUnitNeighbor_of_isNeighbor_signedUnitLattice {r s : ℕ}
    {M : IntegralLattice (Fin r ⊕ Fin s → ℚ)} (hM : (signedUnitLattice r s).IsNeighbor M 2)
    (hMe : M.IsEven) :
    ∃ h8 : 8 ∣ (r : ℤ) - s, Nonempty (Isometry (evenSignedUnitNeighbor r s h8) M) := by
  have hpos : 0 < r + s := by
    by_contra h0; obtain ⟨rfl, rfl⟩ : r = 0 ∧ s = 0 := by omega
    have hcar : (signedUnitLattice 0 0).carrier ⊓ M.carrier = (signedUnitLattice 0 0).carrier :=
      Submodule.ext fun x ↦ by simp [Subsingleton.elim x 0]
    have hrel := hM.relIndex_inf_left; rw [hcar, AddSubgroup.relIndex_self] at hrel; omega
  obtain ⟨k⟩ : Nonempty (Fin r ⊕ Fin s) := Fintype.card_pos_iff.mp (by simpa using hpos)
  obtain ⟨h8', hEq⟩ :=
    (signedUnitLattice r s).eq_halfCharacteristicOverlattice_or_shifted_of_isNeighbor
      (isUnimodular_signedUnitLattice r s) hM hMe
      (isCharacteristicVector_signedUnitCharacteristicVector r s)
      (odd_integralNorm_signedUnitBasisVector r s k)
  have h8 : 8 ∣ (r : ℤ) - s := by rwa [integralNorm_signedUnitCharacteristicVector] at h8'
  rcases hEq with rfl | rfl; exacts [⟨h8, ⟨Isometry.ofEq rfl⟩⟩,
    ⟨h8, ⟨signedUnitHalfCharacteristicIsometryShifted r s h8 k⟩⟩]

/-- Explicit integral isometry from `hyperbolicPlane` to `evenSignedUnitNeighbor 1 1`. -/
noncomputable def hyperbolicPlaneIsometryEvenSignedUnitNeighborOneOne :
    Isometry hyperbolicPlane (evenSignedUnitNeighbor 1 1 (by decide)) where
  toLinearEquiv :=
    { toFun := fun u ↦ Sum.elim (fun _ ↦ u 0 / 2 + u 1) (fun _ ↦ u 0 / 2 - u 1)
      invFun := fun x ↦ ![x (.inl 0) + x (.inr 0), (x (.inl 0) - x (.inr 0)) / 2]
      map_add' := fun u v ↦ by ext (i | j) <;> simp <;> ring
      map_smul' := fun c u ↦ by ext (i | j) <;> simp <;> ring
      left_inv := fun u ↦ by ext i; fin_cases i <;> simp
      right_inv := fun x ↦ by
        ext (i | j)
        · fin_cases i; simp; ring
        · fin_cases j; simp; ring }
  map_app' u v := by
    simp only [evenSignedUnitNeighbor_form, signedUnitLattice_form_apply,
      hyperbolicPlane_form_apply, Fin.sum_univ_one, Sum.elim_inl, Sum.elim_inr]
    ring
  map_carrier := Submodule.ext fun x ↦ by
    rw [Submodule.mem_map_equiv, LinearEquiv.restrictScalars_symm_apply]
    change ![x (.inl 0) + x (.inr 0), (x (.inl 0) - x (.inr 0)) / 2] ∈ hyperbolicPlane.carrier ↔
      x ∈ (evenSignedUnitNeighbor 1 1 (by decide)).carrier
    rw [mem_hyperbolicPlane_carrier_iff, evenSignedUnitNeighbor,
      (signedUnitLattice 1 1).mem_halfCharacteristicOverlattice_carrier_iff,
      mem_evenSublattice_signedUnitLattice_carrier_iff,
      mem_evenSublattice_signedUnitLattice_carrier_iff]
    constructor
    · intro hx
      obtain ⟨p, hp⟩ := hx 0; obtain ⟨q, hq⟩ := hx 1
      have hp' : (p : ℚ) = x (.inl 0) + x (.inr 0) := by simpa using hp
      have hq' : (q : ℚ) = (x (.inl 0) - x (.inr 0)) / 2 := by simpa using hq
      rcases Int.even_or_odd p with ⟨m, rfl⟩ | ⟨m, rfl⟩
      · left; refine ⟨fun k ↦ ?_, m, by simp only [Fin.sum_univ_one]; push_cast at hp' ⊢; linarith⟩
        rcases k with i | j
        · fin_cases i; exact ⟨m + q, by push_cast at hp' hq' ⊢; linarith⟩
        · fin_cases j; exact ⟨m - q, by push_cast at hp' hq' ⊢; linarith⟩
      · right; refine ⟨fun k ↦ ?_, m, by simp only [Fin.sum_univ_one, Pi.sub_apply, Pi.smul_apply,
          coe_signedUnitCharacteristicVector, smul_eq_mul, mul_one]; push_cast at hp' ⊢; linarith⟩
        rcases k with i | j <;> simp only [Pi.sub_apply, Pi.smul_apply,
          coe_signedUnitCharacteristicVector, smul_eq_mul, mul_one]
        · fin_cases i; exact ⟨m + q, by push_cast at hp' hq' ⊢; linarith⟩
        · fin_cases j; exact ⟨m - q, by push_cast at hp' hq' ⊢; linarith⟩
    · rintro (⟨hZ, m, hm⟩ | ⟨hZ, m, hm⟩)
      · obtain ⟨za, hza⟩ := hZ (.inl 0); simp only [Fin.sum_univ_one] at hm
        intro i; fin_cases i
        · exact ⟨2 * m, by simpa using (by push_cast; linarith : ((2 * m : ℤ) : ℚ) = _)⟩
        · exact ⟨za - m, by simpa using (by push_cast; linarith : ((za - m : ℤ) : ℚ) = _)⟩
      · obtain ⟨za, hza⟩ := hZ (.inl 0)
        simp only [Fin.sum_univ_one, Pi.sub_apply, Pi.smul_apply,
          coe_signedUnitCharacteristicVector, smul_eq_mul, mul_one] at hza hm
        intro i; fin_cases i
        · exact ⟨2 * m + 1, by simpa using (by push_cast; linarith : ((2 * m + 1 : ℤ) : ℚ) = _)⟩
        · exact ⟨za - m, by simpa using (by push_cast; linarith : ((za - m : ℤ) : ℚ) = _)⟩

/-- Explicit coordinate formula for `hyperbolicPlaneIsometryEvenSignedUnitNeighborOneOne`. -/
@[simp] theorem hyperbolicPlaneIsometryEvenSignedUnitNeighborOneOne_apply (u : Fin 2 → ℚ) :
    hyperbolicPlaneIsometryEvenSignedUnitNeighborOneOne u =
      Sum.elim (fun _ ↦ u 0 / 2 + u 1) (fun _ ↦ u 0 / 2 - u 1) := (rfl)

/-- Every even Kneser two-neighbor of `signedUnitLattice 1 1` is isometric to `hyperbolicPlane`. -/
theorem nonempty_isometry_hyperbolicPlane_of_isNeighbor_signedUnitLattice_one_one
    {M : IntegralLattice (Fin 1 ⊕ Fin 1 → ℚ)} (hM : (signedUnitLattice 1 1).IsNeighbor M 2)
    (hMe : M.IsEven) : Nonempty (Isometry hyperbolicPlane M) := by
  obtain ⟨_, ⟨f⟩⟩ := nonempty_isometry_evenSignedUnitNeighbor_of_isNeighbor_signedUnitLattice hM hMe
  exact ⟨hyperbolicPlaneIsometryEvenSignedUnitNeighborOneOne.trans f⟩

universe u v
variable {V : Type u} [AddCommGroup V] [Module ℚ V]

private theorem isNeighbor_signedUnitLattice_transport_symm {r s : ℕ} {N K : IntegralLattice V}
    (e : Isometry (signedUnitLattice r s) N) (hK : N.IsNeighbor K 2) :
    (signedUnitLattice r s).IsNeighbor
      (K.transport (e : (Fin r ⊕ Fin s → ℚ) ≃ₗ[ℚ] V).symm) 2 := by
  simpa only [e.transport_symm_eq] using hK.transport (e : (Fin r ⊕ Fin s → ℚ) ≃ₗ[ℚ] V).symm

/-- **Signature congruence mod `8` from an even Kneser two-neighbor of `I_{r, s}`.** -/
theorem eight_dvd_sub_of_isNeighbor_of_isometry_signedUnitLattice {r s : ℕ}
    {N K : IntegralLattice V} (e : Isometry (signedUnitLattice r s) N)
    (hK : N.IsNeighbor K 2) (hKe : K.IsEven) : 8 ∣ (r : ℤ) - s :=
  (nonempty_isometry_evenSignedUnitNeighbor_of_isNeighbor_signedUnitLattice
    (isNeighbor_signedUnitLattice_transport_symm e hK)
    ((K.transportIsometry (e : (Fin r ⊕ Fin s → ℚ) ≃ₗ[ℚ] V).symm).isEven_iff.mp hKe)).1

/-- **Every even Kneser two-neighbor of a lattice isometric to `I_{r, s}` is isometric to
`evenSignedUnitNeighbor r s h8`.** -/
theorem nonempty_isometry_evenSignedUnitNeighbor_of_isNeighbor_of_isometry_signedUnitLattice
    {r s : ℕ} {N K : IntegralLattice V} (e : Isometry (signedUnitLattice r s) N)
    (hK : N.IsNeighbor K 2) (hKe : K.IsEven) (h8 : 8 ∣ (r : ℤ) - s) :
    Nonempty (Isometry (evenSignedUnitNeighbor r s h8) K) := by
  obtain ⟨_, ⟨f⟩⟩ := nonempty_isometry_evenSignedUnitNeighbor_of_isNeighbor_signedUnitLattice
    (isNeighbor_signedUnitLattice_transport_symm e hK)
    ((K.transportIsometry (e : (Fin r ⊕ Fin s → ℚ) ≃ₗ[ℚ] V).symm).isEven_iff.mp hKe)
  exact ⟨f.trans (K.transportIsometry (e : (Fin r ⊕ Fin s → ℚ) ≃ₗ[ℚ] V).symm).symm⟩

/-- **Uniqueness up to isometry of even Kneser two-neighbors of `I_{r, s}`.** -/
theorem nonempty_isometry_of_isNeighbor_of_isometry_signedUnitLattice
    {W : Type v} [AddCommGroup W] [Module ℚ W] {r s : ℕ}
    {N₁ K₁ : IntegralLattice V} {N₂ K₂ : IntegralLattice W}
    (e₁ : Isometry (signedUnitLattice r s) N₁) (hK₁ : N₁.IsNeighbor K₁ 2) (hK₁e : K₁.IsEven)
    (e₂ : Isometry (signedUnitLattice r s) N₂) (hK₂ : N₂.IsNeighbor K₂ 2) (hK₂e : K₂.IsEven) :
    Nonempty (Isometry K₁ K₂) := by
  have h8 := eight_dvd_sub_of_isNeighbor_of_isometry_signedUnitLattice e₁ hK₁ hK₁e
  obtain ⟨f₁⟩ :=
    nonempty_isometry_evenSignedUnitNeighbor_of_isNeighbor_of_isometry_signedUnitLattice
      e₁ hK₁ hK₁e h8
  obtain ⟨f₂⟩ :=
    nonempty_isometry_evenSignedUnitNeighbor_of_isNeighbor_of_isometry_signedUnitLattice
      e₂ hK₂ hK₂e h8
  exact ⟨f₁.symm.trans f₂⟩

/-- For any even lattice `Y`, `Y ⊕ hyperbolicPlane` is isometric to an even Kneser two-neighbor
of `Y ⊕ signedUnitLattice 1 1`. -/
theorem exists_isNeighbor_orthogonalSum_signedUnitLattice_one_one {Y : IntegralLattice V}
    (hY : Y.IsEven) :
    ∃ K : IntegralLattice (V × (Fin 1 ⊕ Fin 1 → ℚ)),
      (Y.orthogonalSum (signedUnitLattice 1 1)).IsNeighbor K 2 ∧ K.IsEven ∧
        Nonempty (Isometry (Y.orthogonalSum hyperbolicPlane) K) :=
  ⟨Y.orthogonalSum (evenSignedUnitNeighbor 1 1 (by decide)),
    (isNeighbor_evenSignedUnitNeighbor (by decide) (by decide)).orthogonalSum_left Y,
    (isEven_orthogonalSum_iff _ _).mpr ⟨hY, isEven_evenSignedUnitNeighbor 1 1 (by decide)⟩,
    ⟨(Isometry.refl Y).orthogonalSum hyperbolicPlaneIsometryEvenSignedUnitNeighborOneOne⟩⟩

end TauCeti.IntegralLattice
