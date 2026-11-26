/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.IntegralLattice.Characteristic.Basic
public import TauCeti.LinearAlgebra.IntegralLattice.Characteristic.EvenSublattice
public import TauCeti.LinearAlgebra.IntegralLattice.RankOne.Basic
public import TauCeti.LinearAlgebra.IntegralLattice.Unit
import TauCeti.Data.Int.MulPred

/-!
# The standard signed unit lattice `I_{r, s}`

For natural numbers `r` and `s`, `signedUnitLattice r s` (`I_{r, s}`) is the standard odd
unimodular lattice `ℤ^{r + s}` inside `ℚ^{r + s}` (indexed by `Fin r ⊕ Fin s`) with diagonal Gram
matrix `diag(+1^r, -1^s)`, canonically isometric to `unitLattice (Fin r) ⊕ (-unitLattice (Fin s))`.
In signature `(1, 0, 1)`, it is canonically isometric to `rankOne 1 ⊕ rankOne (-1)`.

This file establishes the basic invariants (rank, determinant, discriminant, nondegeneracy,
unimodularity, signature, parity, even sublattice), standard basis vectors, the all-ones
characteristic vector of norm `(r : ℤ) - s`, and the coordinate sign-flip self-isometry
`signedUnitSignFlipIsometry`. Kneser two-neighbors of `I_{r, s}` are developed separately in
`TauCeti.LinearAlgebra.IntegralLattice.Neighbor.SignedUnitLattice`.

## Main definitions

* `TauCeti.IntegralLattice.signedUnitLattice`: the standard lattice `I_{r, s}` on
  `Fin r ⊕ Fin s → ℚ`.
* `TauCeti.IntegralLattice.unitLatticeOrthogonalSumIsometrySignedUnitLattice`: the canonical
  isometry `I_r ⊕ (-I_s) ≅ I_{r, s}`.
* `TauCeti.IntegralLattice.rankOneOrthogonalSumIsometrySignedUnitLattice`: the canonical isometry
  `⟨1⟩ ⊕ ⟨-1⟩ ≅ I_{1, 1}`.
* `TauCeti.IntegralLattice.signedUnitBasisVector`: the `k`-th standard coordinate vector.
* `TauCeti.IntegralLattice.signedUnitCharacteristicVector`: the all-ones characteristic vector.
* `TauCeti.IntegralLattice.signedUnitSignFlipIsometry`: the involutive self-isometry negating a
  single coordinate.

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
    rcases p with ⟨p₁, p₂⟩; rcases q with ⟨q₁, q₂⟩
    simp only [AddHom.toFun_eq_coe, LinearMap.coe_toAddHom, LinearEquiv.coe_coe,
      signedUnitLattice_form_apply, orthogonalSum_form, LinearMap.BilinForm.prod_apply,
      LinearEquiv.sumArrowLequivProdArrow_symm_apply_inl,
      LinearEquiv.sumArrowLequivProdArrow_symm_apply_inr, neg_form, LinearMap.neg_apply,
      unitLattice_form_apply, sub_eq_add_neg]
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
    rcases p with ⟨p₁, p₂⟩; rcases q with ⟨q₁, q₂⟩
    simp only [AddHom.toFun_eq_coe, LinearMap.coe_toAddHom, LinearEquiv.coe_coe,
      signedUnitLattice_form_apply, orthogonalSum_form, LinearMap.BilinForm.prod_apply,
      LinearEquiv.trans_apply, LinearEquiv.prodCongr_apply,
      LinearEquiv.sumArrowLequivProdArrow_symm_apply_inl,
      LinearEquiv.sumArrowLequivProdArrow_symm_apply_inr, LinearEquiv.funUnique_symm_apply,
      AddEquiv.funUnique_symm_apply, Fin.sum_univ_one, rankOne_form_apply, Int.cast_one,
      Int.cast_neg]
    ring
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

/-- The `k`-th standard coordinate vector in `signedUnitLattice r s`. -/
def signedUnitBasisVector (r s : ℕ) (k : Fin r ⊕ Fin s) : signedUnitLattice r s :=
  ⟨Pi.single k 1, (mem_signedUnitLattice_carrier_iff r s _).mpr fun l ↦ by
    by_cases h : l = k; · subst h; exact ⟨1, by simp⟩
    · exact ⟨0, by simp [h]⟩⟩

/-- Ambient coercion of `signedUnitBasisVector`. -/
@[simp] theorem coe_signedUnitBasisVector (r s : ℕ) (k : Fin r ⊕ Fin s) :
    (signedUnitBasisVector r s k : Fin r ⊕ Fin s → ℚ) = Pi.single k 1 := (rfl)

/-- Each positive-index standard basis vector of `signedUnitLattice r s` has integral norm `1`. -/
@[simp] theorem integralNorm_signedUnitBasisVector_inl (r s : ℕ) (i : Fin r) :
    (signedUnitLattice r s).integralNorm (signedUnitBasisVector r s (.inl i)) = 1 :=
  Int.cast_injective (α := ℚ) (by simp [integralNorm_cast, Pi.single_apply])

/-- Each negative-index standard basis vector of `signedUnitLattice r s` has integral norm `-1`. -/
@[simp] theorem integralNorm_signedUnitBasisVector_inr (r s : ℕ) (j : Fin s) :
    (signedUnitLattice r s).integralNorm (signedUnitBasisVector r s (.inr j)) = -1 :=
  Int.cast_injective (α := ℚ) (by simp [integralNorm_cast, Pi.single_apply])

/-- Every standard basis vector of `signedUnitLattice r s` has odd integral norm. -/
theorem odd_integralNorm_signedUnitBasisVector (r s : ℕ) (k : Fin r ⊕ Fin s) :
    Odd ((signedUnitLattice r s).integralNorm (signedUnitBasisVector r s k)) := by
  rcases k with i | j <;> simp [odd_one]

/-- `signedUnitLattice r s` is even if and only if `r = 0` and `s = 0`. -/
@[simp] theorem isEven_signedUnitLattice_iff (r s : ℕ) :
    (signedUnitLattice r s).IsEven ↔ r = 0 ∧ s = 0 := by
  refine ⟨fun h ↦ ⟨by_contra fun hr ↦ not_isEven_of_odd_integralNorm
      (odd_integralNorm_signedUnitBasisVector r s (.inl ⟨0, Nat.pos_of_ne_zero hr⟩)) h,
    by_contra fun hs ↦ not_isEven_of_odd_integralNorm
      (odd_integralNorm_signedUnitBasisVector r s (.inr ⟨0, Nat.pos_of_ne_zero hs⟩)) h⟩, ?_⟩
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
  choose z hz using (mem_signedUnitLattice_carrier_iff r s y).mp y.property
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

/-- Membership in `(signedUnitLattice r s).evenSublattice` means integral coordinates with
even coordinate sum. -/
theorem mem_evenSublattice_signedUnitLattice_carrier_iff (r s : ℕ) (x : Fin r ⊕ Fin s → ℚ) :
    x ∈ (signedUnitLattice r s).evenSublattice.carrier ↔
      (∀ k, ∃ z : ℤ, (z : ℚ) = x k) ∧
        ∃ m : ℤ, (∑ i : Fin r, x (.inl i)) + ∑ j : Fin s, x (.inr j) = 2 * m := by
  rw [(signedUnitLattice r s).mem_evenSublattice_carrier_iff_exists_norm]
  have hchar (hx : x ∈ (signedUnitLattice r s).carrier) :
      (∃ k : ℤ, (signedUnitLattice r s).norm x = 2 * k) ↔
        ∃ m : ℤ, (∑ i : Fin r, x (.inl i)) + ∑ j : Fin s, x (.inr j) = 2 * m := by
    let y : signedUnitLattice r s := ⟨x, hx⟩
    choose z hz using (mem_signedUnitLattice_carrier_iff r s x).mp hx
    have hform : (signedUnitLattice r s).integralForm (signedUnitCharacteristicVector r s) y =
        (∑ i : Fin r, z (.inl i)) - ∑ j : Fin s, z (.inr j) :=
      Int.cast_injective (α := ℚ) (by simp [y, integralForm_cast, ← hz])
    rw [← (signedUnitLattice r s).even_integralNorm_iff y, even_iff_two_dvd,
      ← (((signedUnitLattice r s).isCharacteristicVector_iff _).mp
        (isCharacteristicVector_signedUnitCharacteristicVector r s) y).dvd_iff,
      ← even_iff_two_dvd, hform, Int.even_sub, ← Int.even_add, even_iff_exists_two_mul]
    exact exists_congr fun m ↦ by simp [← Int.cast_inj (α := ℚ), ← hz]
  exact ⟨fun ⟨hx, hk⟩ ↦ ⟨(mem_signedUnitLattice_carrier_iff r s x).mp hx, (hchar hx).mp hk⟩,
    fun ⟨hxZ, hm⟩ ↦ ⟨(mem_signedUnitLattice_carrier_iff r s x).mpr hxZ,
      (hchar ((mem_signedUnitLattice_carrier_iff r s x).mpr hxZ)).mpr hm⟩⟩

/-- The involutive self-isometry of `signedUnitLattice r s` that negates coordinate `k`. -/
def signedUnitSignFlipIsometry (r s : ℕ) (k : Fin r ⊕ Fin s) :
    Isometry (signedUnitLattice r s) (signedUnitLattice r s) where
  toLinearEquiv := LinearEquiv.piCongrRight
    (Function.update (fun _ ↦ LinearEquiv.refl ℚ ℚ) k (LinearEquiv.neg ℚ))
  map_app' x y := by
    have hmul (l) :
        (Function.update (fun _ ↦ LinearEquiv.refl ℚ ℚ) k (LinearEquiv.neg ℚ) l) (x l) *
          (Function.update (fun _ ↦ LinearEquiv.refl ℚ ℚ) k (LinearEquiv.neg ℚ) l) (y l) =
        x l * y l := by by_cases h : l = k <;> simp [h]
    simp only [AddHom.toFun_eq_coe, LinearMap.coe_toAddHom, LinearEquiv.coe_coe,
      signedUnitLattice_form_apply, LinearEquiv.piCongrRight_apply, hmul]
  map_carrier := Submodule.ext fun x ↦ by
    rw [Submodule.mem_map_equiv, LinearEquiv.restrictScalars_symm_apply,
      LinearEquiv.piCongrRight_symm, mem_signedUnitLattice_carrier_iff,
      mem_signedUnitLattice_carrier_iff]
    refine forall_congr' fun l ↦ ?_
    rw [LinearEquiv.piCongrRight_apply]
    by_cases hlk : l = k
    · subst hlk
      simpa using ⟨fun ⟨z, hz⟩ ↦ ⟨-z, by push_cast; linarith⟩,
        fun ⟨z, hz⟩ ↦ ⟨-z, by push_cast; linarith⟩⟩
    · simp only [Function.update_of_ne hlk, LinearEquiv.refl_symm, LinearEquiv.refl_apply]

/-- `signedUnitSignFlipIsometry` negates coordinate `k` and leaves all other coordinates fixed. -/
@[simp] theorem signedUnitSignFlipIsometry_apply (r s : ℕ) (k : Fin r ⊕ Fin s)
    (x : Fin r ⊕ Fin s → ℚ) :
    signedUnitSignFlipIsometry r s k x = Function.update x k (-x k) := by
  rw [← Isometry.coe_toLinearEquiv]
  ext l; by_cases h : l = k <;> simp [signedUnitSignFlipIsometry, h]

/-- `signedUnitSignFlipIsometry` is an involution: its inverse is itself. -/
@[simp] theorem signedUnitSignFlipIsometry_symm (r s : ℕ) (k : Fin r ⊕ Fin s) :
    (signedUnitSignFlipIsometry r s k).symm = signedUnitSignFlipIsometry r s k :=
  Isometry.ext fun x ↦ by
    rw [Isometry.coe_symm]
    refine (LinearEquiv.symm_apply_eq _).mpr ?_
    ext l; by_cases h : l = k <;> simp [h]

end TauCeti.IntegralLattice
