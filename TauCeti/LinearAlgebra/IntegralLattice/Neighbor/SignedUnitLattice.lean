/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.IntegralLattice.Neighbor.IndefiniteUnitPlane
public import TauCeti.LinearAlgebra.IntegralLattice.Unit

/-!
# The standard odd unimodular lattice `I_{r, s}` and uniqueness of its even two-neighbors

For natural numbers `r` and `s`, the lattice `signedUnitLattice r s` (classically written
`I_{r, s}`) is `ℤ^{r + s}` inside `ℚ^{r + s}` (indexed by `Fin r ⊕ Fin s`) equipped with the
diagonal bilinear form having `r` entries equal to `+1` and `s` entries equal to `-1`. It is
canonically isometric to `(unitLattice (Fin r)).orthogonalSum (-(unitLattice (Fin s)))`, so it is
unimodular of signature `(r, 0, s)` and is odd whenever `0 < r + s`.

The all-ones vector `(1, …, 1)` is a characteristic vector of `signedUnitLattice r s` of integral
norm `(r : ℤ) - s`. When `0 < r + s`, the norm-parity kernel classification of
`TauCeti.LinearAlgebra.IntegralLattice.Characteristic.ParityKernel` shows that an even Kneser
two-neighbor of `signedUnitLattice r s` exists if and only if `8 ∣ (r : ℤ) - s`, in which case
every even two-neighbor equals either `halfCharacteristicOverlattice` or
`shiftedHalfCharacteristicOverlattice` with respect to any standard basis vector `e_k`. Flipping
the `k`-th coordinate is an auto-isometry of `signedUnitLattice r s` that sends `(1 / 2) • w` into
`e_k + (1 / 2) • w` modulo the even sublattice, so the two even two-neighbors are integrally
isometric.

Consequently, for any lattices `N₁, N₂` isometric to `signedUnitLattice r s`, the existence of an
even two-neighbor forces `0 < r + s` and `8 ∣ (r : ℤ) - s`, and any two even Kneser two-neighbors
of `N₁` and `N₂` are integrally isometric.

## Main definitions

* `TauCeti.IntegralLattice.signedUnitLattice`: the odd unimodular lattice `I_{r, s}` on
  `Fin r ⊕ Fin s → ℚ`.
* `TauCeti.IntegralLattice.unitLatticeOrthogonalSumIsometrySignedUnitLattice`: the canonical
  isometry `I_r ⊕ (-I_s) ≅ I_{r, s}`.
* `TauCeti.IntegralLattice.signedUnitLatticeOneOneIsometryIndefiniteUnitPlane`: the canonical
  isometry `I_{1, 1} ≅ indefiniteUnitPlane`.
* `TauCeti.IntegralLattice.evenSignedUnitNeighbor`: the canonical even unimodular two-neighbor
  `I_{r, s}^+` of `I_{r, s}` when `8 ∣ (r : ℤ) - s`.
* `TauCeti.IntegralLattice.signedUnitHalfCharacteristicIsometryShifted`: the coordinate sign-flip
  isometry identifying the two even two-neighbors of `I_{r, s}`.

## Main results

* `TauCeti.IntegralLattice.signedUnitLattice_signature`: `I_{r, s}` has signature `(r, 0, s)`.
* `TauCeti.IntegralLattice.isUnimodular_signedUnitLattice`: `I_{r, s}` is unimodular.
* `TauCeti.IntegralLattice.isEven_signedUnitLattice_iff`: `I_{r, s}` is even iff `r = 0 ∧ s = 0`.
* `TauCeti.IntegralLattice.eight_dvd_sub_of_isNeighbor_of_isometry_signedUnitLattice`: if a lattice
  isometric to `I_{r, s}` has an even two-neighbor, then `8 ∣ (r : ℤ) - s`.
* `TauCeti.IntegralLattice.nonempty_isometry_of_isNeighbor_of_isometry_signedUnitLattice`: any two
  even Kneser two-neighbors of lattices isometric to `I_{r, s}` are integrally isometric.

## References

* J.-P. Serre, *A Course in Arithmetic*, Chapter V, §2.2.
* J. Milnor and D. Husemoller, *Symmetric Bilinear Forms*, Chapter II, §§2–5.
-/

public section

open Module

namespace TauCeti.IntegralLattice

/-! ## Definition and basic invariants of `I_{r, s}` -/

private def signedUnitMatrixDiag (r s : ℕ) : Fin r ⊕ Fin s → ℤ :=
  Sum.elim (fun _ ↦ 1) (fun _ ↦ -1)

private def signedUnitMatrix (r s : ℕ) : Matrix (Fin r ⊕ Fin s) (Fin r ⊕ Fin s) ℤ :=
  Matrix.diagonal (signedUnitMatrixDiag r s)

private theorem isSymm_signedUnitMatrix (r s : ℕ) : (signedUnitMatrix r s).IsSymm :=
  Matrix.isSymm_diagonal _

/-- The standard signed unit lattice `I_{r, s}` on `Fin r ⊕ Fin s → ℚ`, with diagonal Gram matrix
having `r` entries `+1` and `s` entries `-1`. -/
noncomputable def signedUnitLattice (r s : ℕ) : IntegralLattice (Fin r ⊕ Fin s → ℚ) :=
  ofGramMatrix (Pi.basisFun ℚ (Fin r ⊕ Fin s)) (signedUnitMatrix r s) (isSymm_signedUnitMatrix r s)

/-- Membership in `signedUnitLattice r s` means all coordinates are integers. -/
@[simp]
theorem mem_signedUnitLattice_carrier_iff (r s : ℕ) (x : Fin r ⊕ Fin s → ℚ) :
    x ∈ (signedUnitLattice r s).carrier ↔ ∀ k, ∃ z : ℤ, (z : ℚ) = x k := by
  simpa only [signedUnitLattice] using
    mem_ofGramMatrix_basisFun_carrier_iff (signedUnitMatrix r s) (isSymm_signedUnitMatrix r s) x

/-- The bilinear form of `signedUnitLattice r s` is the difference of the positive and negative dot
products. -/
@[simp]
theorem signedUnitLattice_form_apply (r s : ℕ) (x y : Fin r ⊕ Fin s → ℚ) :
    (signedUnitLattice r s).form x y =
      (∑ i : Fin r, x (.inl i) * y (.inl i)) - ∑ j : Fin s, x (.inr j) * y (.inr j) := by
  rw [signedUnitLattice, form_ofGramMatrix_basisFun_apply]
  have hrow (k : Fin r ⊕ Fin s) :
      (∑ l, ((signedUnitMatrix r s k l : ℤ) : ℚ) * y l) =
        ((signedUnitMatrixDiag r s k : ℤ) : ℚ) * y k := by
    rw [Finset.sum_eq_single k]
    · simp [signedUnitMatrix]
    · intro l _ hlk
      simp [signedUnitMatrix, Matrix.diagonal_apply_ne _ hlk.symm]
    · intro hk
      exact (hk (Finset.mem_univ k)).elim
  simp_rw [hrow]
  rw [Fintype.sum_sum_type]
  simp only [signedUnitMatrixDiag, Sum.elim_inl, Int.cast_one, one_mul, Sum.elim_inr,
    Int.cast_neg, neg_mul, mul_neg, Finset.sum_neg_distrib, sub_eq_add_neg]

/-- The quadratic norm on `signedUnitLattice r s` is `(∑ i, xᵢ²) - ∑ j, yⱼ²`. -/
@[simp]
theorem signedUnitLattice_norm_apply (r s : ℕ) (x : Fin r ⊕ Fin s → ℚ) :
    (signedUnitLattice r s).norm x =
      (∑ i : Fin r, x (.inl i) ^ 2) - ∑ j : Fin s, x (.inr j) ^ 2 := by
  rw [norm_apply, signedUnitLattice_form_apply]
  simp only [sq]

/-- `signedUnitLattice r s` has rank `r + s`. -/
@[simp]
theorem finrank_signedUnitLattice (r s : ℕ) :
    Module.finrank ℤ (signedUnitLattice r s) = r + s := by
  rw [(signedUnitLattice r s).finrank_carrier]
  simp

/-- The canonical isometry `I_r ⊕ (-I_s) ≅ I_{r, s}`. -/
noncomputable def unitLatticeOrthogonalSumIsometrySignedUnitLattice (r s : ℕ) :
    Isometry ((unitLattice (Fin r)).orthogonalSum (-(unitLattice (Fin s))))
      (signedUnitLattice r s) where
  toLinearEquiv := (LinearEquiv.sumArrowLequivProdArrow (Fin r) (Fin s) ℚ ℚ).symm
  map_app' p q := by
    have hp : (LinearEquiv.sumArrowLequivProdArrow (Fin r) (Fin s) ℚ ℚ).symm p =
        Sum.elim p.1 p.2 := rfl
    have hq : (LinearEquiv.sumArrowLequivProdArrow (Fin r) (Fin s) ℚ ℚ).symm q =
        Sum.elim q.1 q.2 := rfl
    simp only [LinearEquiv.coe_toLinearMap, LinearMap.toFun_eq_coe]
    rw [hp, hq]
    simp only [signedUnitLattice_form_apply, Sum.elim_inl, Sum.elim_inr, orthogonalSum_form,
      LinearMap.BilinForm.prod_apply, unitLattice_form_apply, neg_form, LinearMap.neg_apply,
      sub_eq_add_neg]
  map_carrier := by
    ext x
    rw [Submodule.mem_map_equiv, orthogonalSum_carrier, Submodule.mem_prod, neg_carrier,
      mem_unitLattice_carrier_iff, mem_unitLattice_carrier_iff, mem_signedUnitLattice_carrier_iff]
    exact ⟨fun ⟨h1, h2⟩ k ↦ Sum.casesOn k h1 h2, fun h ↦ ⟨fun i ↦ h (.inl i), fun j ↦ h (.inr j)⟩⟩

/-- `unitLatticeOrthogonalSumIsometrySignedUnitLattice` acts as `Sum.elim`. -/
@[simp]
theorem unitLatticeOrthogonalSumIsometrySignedUnitLattice_apply (r s : ℕ)
    (p : (Fin r → ℚ) × (Fin s → ℚ)) :
    unitLatticeOrthogonalSumIsometrySignedUnitLattice r s p = Sum.elim p.1 p.2 :=
  (rfl)

/-- `signedUnitLattice r s` has signed determinant `(-1) ^ s`. -/
@[simp]
theorem signedUnitLattice_determinant (r s : ℕ) :
    (signedUnitLattice r s).determinant = (-1) ^ s := by
  rw [← (unitLatticeOrthogonalSumIsometrySignedUnitLattice r s).determinant_eq,
    determinant_orthogonalSum, unitLattice_determinant, determinant_neg, unitLattice_determinant,
    finrank_unitLattice, Fintype.card_fin]
  ring

/-- `signedUnitLattice r s` has discriminant `1`. -/
@[simp]
theorem signedUnitLattice_discriminant (r s : ℕ) :
    (signedUnitLattice r s).discriminant = 1 := by
  rw [discriminant_def, signedUnitLattice_determinant]
  simp

/-- `signedUnitLattice r s` is nondegenerate for all `r` and `s`. -/
instance instIsNondegenerateSignedUnitLattice (r s : ℕ) :
    (signedUnitLattice r s).IsNondegenerate :=
  ⟨(signedUnitLattice r s).determinant_ne_zero_iff.mp (by simp)⟩

/-- `signedUnitLattice r s` is unimodular for all `r` and `s`. -/
theorem isUnimodular_signedUnitLattice (r s : ℕ) : (signedUnitLattice r s).IsUnimodular := by
  rw [(signedUnitLattice r s).isUnimodular_iff_discriminant_eq_one]
  exact signedUnitLattice_discriminant r s

/-- `signedUnitLattice r s` has signature `(r, 0, s)`. -/
@[simp]
theorem signedUnitLattice_signature (r s : ℕ) :
    (signedUnitLattice r s).signature = (r, 0, s) := by
  have hp := unitLattice_signature (Fin r)
  have hn := signature_neg (unitLattice (Fin s))
  rw [Fintype.card_fin] at hp
  have hs := unitLattice_signature (Fin s)
  rw [Fintype.card_fin] at hs
  simp only [signature, Prod.mk.injEq] at hp hs hn
  rw [← (unitLatticeOrthogonalSumIsometrySignedUnitLattice r s).signature_eq,
    signature_orthogonalSum, hp.1, hp.2.1, hp.2.2, hn.1, hn.2.1, hn.2.2, hs.1, hs.2.1, hs.2.2]
  simp

private def finOneSumFinOneLinearEquiv : (Fin 1 ⊕ Fin 1 → ℚ) ≃ₗ[ℚ] (Fin 2 → ℚ) where
  toFun x := ![x (.inl 0), x (.inr 0)]
  invFun y := Sum.elim (fun _ ↦ y 0) (fun _ ↦ y 1)
  map_add' x y := by
    rw [funext_iff, Fin.forall_fin_two]
    exact ⟨rfl, rfl⟩
  map_smul' c x := by
    rw [funext_iff, Fin.forall_fin_two]
    exact ⟨rfl, rfl⟩
  left_inv x := by
    ext (i | j)
    · rw [Subsingleton.elim i 0]; rfl
    · rw [Subsingleton.elim j 0]; rfl
  right_inv y := by
    rw [funext_iff, Fin.forall_fin_two]
    exact ⟨rfl, rfl⟩

/-- The canonical isometry `I_{1, 1} ≅ indefiniteUnitPlane`. -/
noncomputable def signedUnitLatticeOneOneIsometryIndefiniteUnitPlane :
    Isometry (signedUnitLattice 1 1) indefiniteUnitPlane where
  toLinearEquiv := finOneSumFinOneLinearEquiv
  map_app' x y := by
    simp only [finOneSumFinOneLinearEquiv, indefiniteUnitPlane_form_apply, Matrix.cons_val_zero,
      Matrix.cons_val_one, signedUnitLattice_form_apply, Fin.sum_univ_one]
  map_carrier := by
    ext y
    rw [Submodule.mem_map_equiv, mem_signedUnitLattice_carrier_iff,
      mem_indefiniteUnitPlane_carrier_iff, Fin.forall_fin_two]
    refine ⟨fun h ↦ ⟨h (.inl 0), h (.inr 0)⟩, fun ⟨h0, h1⟩ k ↦ ?_⟩
    rcases k with i | j
    · rw [Subsingleton.elim i 0]; exact h0
    · rw [Subsingleton.elim j 0]; exact h1

/-! ## Basis vectors, parity, and the all-ones characteristic vector -/

/-- The `k`-th standard coordinate vector in `signedUnitLattice r s`. -/
def signedUnitBasisVector (r s : ℕ) (k : Fin r ⊕ Fin s) : signedUnitLattice r s :=
  ⟨Pi.single k 1, (mem_signedUnitLattice_carrier_iff r s _).mpr fun l ↦ by
    by_cases h : l = k
    · subst h; exact ⟨1, by simp⟩
    · exact ⟨0, by simp [h]⟩⟩

/-- Ambient coercion of `signedUnitBasisVector`. -/
@[simp]
theorem coe_signedUnitBasisVector (r s : ℕ) (k : Fin r ⊕ Fin s) :
    (signedUnitBasisVector r s k : Fin r ⊕ Fin s → ℚ) = Pi.single k 1 :=
  (rfl)

/-- Each positive-index standard basis vector of `signedUnitLattice r s` has integral norm `1`. -/
@[simp]
theorem integralNorm_signedUnitBasisVector_inl (r s : ℕ) (i : Fin r) :
    (signedUnitLattice r s).integralNorm (signedUnitBasisVector r s (.inl i)) = 1 := by
  apply Int.cast_injective (α := ℚ)
  rw [integralNorm_cast, signedUnitLattice_norm_apply, coe_signedUnitBasisVector]
  let f : Fin r ⊕ Fin s → ℚ := Pi.single (.inl i) 1
  have h1 : (∑ i' : Fin r, f (.inl i') ^ 2) = 1 := by
    rw [Finset.sum_eq_single i]
    · simp [f]
    · intro i' _ hi'
      have hne : (Sum.inl i' : Fin r ⊕ Fin s) ≠ Sum.inl i := fun h ↦ hi' (Sum.inl.inj h)
      simp [f, Pi.single_eq_of_ne hne]
    · intro hi; exact (hi (Finset.mem_univ i)).elim
  have h2 : (∑ j : Fin s, f (.inr j) ^ 2) = 0 :=
    Finset.sum_eq_zero fun j _ ↦ by simp [f]
  -- Fold the inline `Pi.single` applications into the local abbreviation `f`.
  change (∑ i' : Fin r, f (.inl i') ^ 2) - ∑ j : Fin s, f (.inr j) ^ 2 = ((1 : ℤ) : ℚ)
  rw [h1, h2]
  norm_num

/-- Each negative-index standard basis vector of `signedUnitLattice r s` has integral norm `-1`. -/
@[simp]
theorem integralNorm_signedUnitBasisVector_inr (r s : ℕ) (j : Fin s) :
    (signedUnitLattice r s).integralNorm (signedUnitBasisVector r s (.inr j)) = -1 := by
  apply Int.cast_injective (α := ℚ)
  rw [integralNorm_cast, signedUnitLattice_norm_apply, coe_signedUnitBasisVector]
  let f : Fin r ⊕ Fin s → ℚ := Pi.single (.inr j) 1
  have h1 : (∑ i : Fin r, f (.inl i) ^ 2) = 0 :=
    Finset.sum_eq_zero fun i _ ↦ by simp [f]
  have h2 : (∑ j' : Fin s, f (.inr j') ^ 2) = 1 := by
    rw [Finset.sum_eq_single j]
    · simp [f]
    · intro j' _ hj'
      have hne : (Sum.inr j' : Fin r ⊕ Fin s) ≠ Sum.inr j := fun h ↦ hj' (Sum.inr.inj h)
      simp [f, Pi.single_eq_of_ne hne]
    · intro hj; exact (hj (Finset.mem_univ j)).elim
  -- Fold the inline `Pi.single` applications into the local abbreviation `f`.
  change (∑ i : Fin r, f (.inl i) ^ 2) - ∑ j' : Fin s, f (.inr j') ^ 2 = ((-1 : ℤ) : ℚ)
  rw [h1, h2]
  norm_num

/-- Every standard basis vector of `signedUnitLattice r s` has odd integral norm. -/
theorem odd_integralNorm_signedUnitBasisVector (r s : ℕ) (k : Fin r ⊕ Fin s) :
    Odd ((signedUnitLattice r s).integralNorm (signedUnitBasisVector r s k)) := by
  rcases k with i | j
  · rw [integralNorm_signedUnitBasisVector_inl]
    exact odd_one
  · rw [integralNorm_signedUnitBasisVector_inr]
    exact Odd.neg odd_one

/-- `signedUnitLattice r s` is even if and only if `r = 0` and `s = 0`. -/
@[simp]
theorem isEven_signedUnitLattice_iff (r s : ℕ) :
    (signedUnitLattice r s).IsEven ↔ r = 0 ∧ s = 0 := by
  constructor
  · intro h
    rw [isEven_iff_forall_norm] at h
    refine ⟨?_, ?_⟩
    · by_contra hr
      have hr' : 0 < r := Nat.pos_of_ne_zero hr
      have hev := ((signedUnitLattice r s).even_integralNorm_iff
        (signedUnitBasisVector r s (.inl ⟨0, hr'⟩))).mpr
        (h (signedUnitBasisVector r s (.inl ⟨0, hr'⟩)))
      exact Int.not_odd_iff_even.mpr hev
        (odd_integralNorm_signedUnitBasisVector r s (.inl ⟨0, hr'⟩))
    · by_contra hs
      have hs' : 0 < s := Nat.pos_of_ne_zero hs
      have hev := ((signedUnitLattice r s).even_integralNorm_iff
        (signedUnitBasisVector r s (.inr ⟨0, hs'⟩))).mpr
        (h (signedUnitBasisVector r s (.inr ⟨0, hs'⟩)))
      exact Int.not_odd_iff_even.mpr hev
        (odd_integralNorm_signedUnitBasisVector r s (.inr ⟨0, hs'⟩))
  · rintro ⟨rfl, rfl⟩
    rw [isEven_iff_forall_norm]
    intro x
    exact ⟨0, by simp⟩

/-- `signedUnitLattice r s` is odd whenever `0 < r + s`. -/
theorem not_isEven_signedUnitLattice_of_pos {r s : ℕ} (h : 0 < r + s) :
    ¬ (signedUnitLattice r s).IsEven := by
  rw [isEven_signedUnitLattice_iff]
  omega

/-- The all-ones vector `(1, …, 1)` in `signedUnitLattice r s`. -/
def signedUnitCharacteristicVector (r s : ℕ) : signedUnitLattice r s :=
  ⟨fun _ ↦ 1, (mem_signedUnitLattice_carrier_iff r s _).mpr fun _ ↦ ⟨1, rfl⟩⟩

/-- Ambient coercion of `signedUnitCharacteristicVector`. -/
@[simp]
theorem coe_signedUnitCharacteristicVector (r s : ℕ) :
    (signedUnitCharacteristicVector r s : Fin r ⊕ Fin s → ℚ) = fun _ ↦ 1 :=
  (rfl)

/-- The all-ones vector is a characteristic vector of `signedUnitLattice r s`. -/
theorem isCharacteristicVector_signedUnitCharacteristicVector (r s : ℕ) :
    (signedUnitLattice r s).IsCharacteristicVector (signedUnitCharacteristicVector r s) := by
  have hdvd (a : ℤ) : 2 ∣ a ^ 2 - a := by
    rcases Int.even_or_odd a with ⟨k, rfl⟩ | ⟨k, rfl⟩
    · exact ⟨2 * k ^ 2 - k, by ring⟩
    · exact ⟨2 * k ^ 2 + k, by ring⟩
  rw [(signedUnitLattice r s).isCharacteristicVector_iff]
  intro y
  choose z hz using (mem_signedUnitLattice_carrier_iff r s y).mp y.2
  have hform : (signedUnitLattice r s).integralForm (signedUnitCharacteristicVector r s) y =
      (∑ i : Fin r, z (.inl i)) - ∑ j : Fin s, z (.inr j) := by
    apply Int.cast_injective (α := ℚ)
    rw [integralForm_cast, signedUnitLattice_form_apply, coe_signedUnitCharacteristicVector]
    simp only [← hz, one_mul, Int.cast_sub, Int.cast_sum]
  have hnorm : (signedUnitLattice r s).integralNorm y =
      (∑ i : Fin r, z (.inl i) ^ 2) - ∑ j : Fin s, z (.inr j) ^ 2 := by
    apply Int.cast_injective (α := ℚ)
    rw [integralNorm_cast, signedUnitLattice_norm_apply]
    simp only [← hz, Int.cast_sub, Int.cast_sum, Int.cast_pow]
  rw [hform, hnorm, Int.modEq_iff_dvd]
  have hrew : ((∑ i : Fin r, z (.inl i) ^ 2) - ∑ j : Fin s, z (.inr j) ^ 2) -
      ((∑ i : Fin r, z (.inl i)) - ∑ j : Fin s, z (.inr j)) =
      (∑ i : Fin r, (z (.inl i) ^ 2 - z (.inl i))) -
        ∑ j : Fin s, (z (.inr j) ^ 2 - z (.inr j)) := by
    simp only [Finset.sum_sub_distrib]
    ring
  rw [hrew]
  exact dvd_sub (Finset.dvd_sum fun i _ ↦ hdvd _) (Finset.dvd_sum fun j _ ↦ hdvd _)

/-- The all-ones characteristic vector of `signedUnitLattice r s` has integral norm
`(r : ℤ) - s`. -/
@[simp]
theorem integralNorm_signedUnitCharacteristicVector (r s : ℕ) :
    (signedUnitLattice r s).integralNorm (signedUnitCharacteristicVector r s) = (r : ℤ) - s := by
  apply Int.cast_injective (α := ℚ)
  rw [integralNorm_cast, signedUnitLattice_norm_apply, coe_signedUnitCharacteristicVector]
  simp

/-! ## Coordinate sign-flip and isometry of the two even two-neighbors -/

private def signedUnitSignFlipEquiv (r s : ℕ) (k : Fin r ⊕ Fin s) :
    (Fin r ⊕ Fin s → ℚ) ≃ₗ[ℚ] (Fin r ⊕ Fin s → ℚ) where
  toFun x := Function.update x k (-x k)
  invFun x := Function.update x k (-x k)
  map_add' x y := by
    ext l
    by_cases h : l = k <;> simp [h, add_comm]
  map_smul' c x := by
    ext l
    by_cases h : l = k <;> simp [h]
  left_inv x := by
    ext l
    by_cases h : l = k <;> simp [h]
  right_inv x := by
    ext l
    by_cases h : l = k <;> simp [h]

private theorem mul_signedUnitSignFlipEquiv_apply (r s : ℕ) (k : Fin r ⊕ Fin s)
    (x y : Fin r ⊕ Fin s → ℚ) (l : Fin r ⊕ Fin s) :
    signedUnitSignFlipEquiv r s k x l * signedUnitSignFlipEquiv r s k y l = x l * y l := by
  dsimp only [signedUnitSignFlipEquiv, LinearEquiv.coe_mk, LinearMap.coe_mk, AddHom.coe_mk]
  by_cases h : l = k
  · subst h; simp
  · simp [h]

private theorem form_signedUnitSignFlipEquiv (r s : ℕ) (k : Fin r ⊕ Fin s)
    (x y : Fin r ⊕ Fin s → ℚ) :
    (signedUnitLattice r s).form (signedUnitSignFlipEquiv r s k x)
      (signedUnitSignFlipEquiv r s k y) = (signedUnitLattice r s).form x y := by
  simp only [signedUnitLattice_form_apply, mul_signedUnitSignFlipEquiv_apply]

private theorem mem_evenSublattice_signedUnitSignFlipEquiv_iff (r s : ℕ) (k : Fin r ⊕ Fin s)
    (x : Fin r ⊕ Fin s → ℚ) :
    signedUnitSignFlipEquiv r s k x ∈ (signedUnitLattice r s).evenSublattice.carrier ↔
      x ∈ (signedUnitLattice r s).evenSublattice.carrier := by
  have hmem (u : Fin r ⊕ Fin s → ℚ) :
      signedUnitSignFlipEquiv r s k u ∈ (signedUnitLattice r s).carrier →
        u ∈ (signedUnitLattice r s).carrier := by
    rw [mem_signedUnitLattice_carrier_iff, mem_signedUnitLattice_carrier_iff]
    intro h l
    obtain ⟨z, hz⟩ := h l
    dsimp only [signedUnitSignFlipEquiv, LinearEquiv.coe_mk, LinearMap.coe_mk, AddHom.coe_mk] at hz
    by_cases hlk : l = k
    · subst hlk
      simp only [Function.update_self] at hz
      exact ⟨-z, by push_cast; linarith⟩
    · rw [Function.update_of_ne hlk] at hz
      exact ⟨z, hz⟩
  have hfwd (u : Fin r ⊕ Fin s → ℚ)
      (hu : u ∈ (signedUnitLattice r s).evenSublattice.carrier) :
      signedUnitSignFlipEquiv r s k u ∈ (signedUnitLattice r s).evenSublattice.carrier := by
    have huL := (signedUnitLattice r s).evenSublattice_carrier_le hu
    have hinv_u : signedUnitSignFlipEquiv r s k (signedUnitSignFlipEquiv r s k u) = u :=
      (signedUnitSignFlipEquiv r s k).left_inv u
    have hτuL : signedUnitSignFlipEquiv r s k u ∈ (signedUnitLattice r s).carrier :=
      hmem _ (hinv_u.symm ▸ huL)
    rw [(signedUnitLattice r s).mem_evenSublattice_carrier_iff ⟨_, hτuL⟩,
      (signedUnitLattice r s).even_integralNorm_iff]
    obtain ⟨m, hm⟩ := ((signedUnitLattice r s).even_integralNorm_iff ⟨u, huL⟩).mp
      (((signedUnitLattice r s).mem_evenSublattice_carrier_iff ⟨u, huL⟩).mp hu)
    refine ⟨m, ?_⟩
    dsimp only at hm ⊢
    rw [norm_apply, form_signedUnitSignFlipEquiv, ← norm_apply]
    exact hm
  refine ⟨fun h ↦ ?_, hfwd x⟩
  have h2 := hfwd _ h
  have hinv : signedUnitSignFlipEquiv r s k (signedUnitSignFlipEquiv r s k x) = x :=
    (signedUnitSignFlipEquiv r s k).left_inv x
  rwa [hinv] at h2

/-- Divisibility of `(r : ℤ) - s` by `8` is equivalent to `8` dividing the norm of
`signedUnitCharacteristicVector r s`. -/
theorem eight_dvd_integralNorm_signedUnitCharacteristicVector {r s : ℕ}
    (h8 : 8 ∣ (r : ℤ) - s) :
    8 ∣ (signedUnitLattice r s).integralNorm (signedUnitCharacteristicVector r s) := by
  rwa [integralNorm_signedUnitCharacteristicVector]

/-- The canonical even overlattice `I_{r, s}^+` obtained by adjoining `(1 / 2, …, 1 / 2)` to
`(signedUnitLattice r s).evenSublattice` when `8 ∣ (r : ℤ) - s`. -/
noncomputable def evenSignedUnitNeighbor (r s : ℕ) (h8 : 8 ∣ (r : ℤ) - s) :
    IntegralLattice (Fin r ⊕ Fin s → ℚ) :=
  (signedUnitLattice r s).halfCharacteristicOverlattice (isUnimodular_signedUnitLattice r s)
    (isCharacteristicVector_signedUnitCharacteristicVector r s)
    (eight_dvd_integralNorm_signedUnitCharacteristicVector h8)

/-- `evenSignedUnitNeighbor r s h8` shares the ambient bilinear form of `signedUnitLattice r s`. -/
@[simp]
theorem evenSignedUnitNeighbor_form (r s : ℕ) (h8 : 8 ∣ (r : ℤ) - s) :
    (evenSignedUnitNeighbor r s h8).form = (signedUnitLattice r s).form :=
  (signedUnitLattice r s).halfCharacteristicOverlattice_form _ _ _

/-- `evenSignedUnitNeighbor r s h8` is an even integral lattice. -/
theorem isEven_evenSignedUnitNeighbor (r s : ℕ) (h8 : 8 ∣ (r : ℤ) - s) :
    (evenSignedUnitNeighbor r s h8).IsEven :=
  (signedUnitLattice r s).isEven_halfCharacteristicOverlattice _ _ _

/-- `evenSignedUnitNeighbor r s h8` is unimodular for all `r` and `s` with `8 ∣ (r : ℤ) - s`. -/
theorem isUnimodular_evenSignedUnitNeighbor (r s : ℕ) (h8 : 8 ∣ (r : ℤ) - s) :
    (evenSignedUnitNeighbor r s h8).IsUnimodular :=
  (signedUnitLattice r s).isUnimodular_halfCharacteristicOverlattice
    (isUnimodular_signedUnitLattice r s) _ _

/-- `evenSignedUnitNeighbor r s h8` is a Kneser two-neighbor of `signedUnitLattice r s` whenever
`0 < r + s`. -/
theorem isNeighbor_evenSignedUnitNeighbor {r s : ℕ} (hpos : 0 < r + s) (h8 : 8 ∣ (r : ℤ) - s) :
    (signedUnitLattice r s).IsNeighbor (evenSignedUnitNeighbor r s h8) 2 :=
  (signedUnitLattice r s).isNeighbor_halfCharacteristicOverlattice
    (isUnimodular_signedUnitLattice r s) (not_isEven_signedUnitLattice_of_pos hpos) _ _

/-- `evenSignedUnitNeighbor r s h8` has signature `(r, 0, s)`. -/
@[simp]
theorem evenSignedUnitNeighbor_signature (r s : ℕ) (h8 : 8 ∣ (r : ℤ) - s) :
    (evenSignedUnitNeighbor r s h8).signature = (r, 0, s) := by
  rw [signature_eq_of_form_eq (evenSignedUnitNeighbor_form r s h8), signedUnitLattice_signature]

private theorem signedUnitSignFlipEquiv_mem_evenSignedUnitNeighbor_iff (r s : ℕ)
    (h8 : 8 ∣ (r : ℤ) - s) (k : Fin r ⊕ Fin s) (x : Fin r ⊕ Fin s → ℚ) :
    signedUnitSignFlipEquiv r s k x ∈ (evenSignedUnitNeighbor r s h8).carrier ↔
      x ∈ ((signedUnitLattice r s).shiftedHalfCharacteristicOverlattice
        (isUnimodular_signedUnitLattice r s)
        (isCharacteristicVector_signedUnitCharacteristicVector r s)
        (eight_dvd_integralNorm_signedUnitCharacteristicVector h8)
        (signedUnitBasisVector r s k)).carrier := by
  rw [evenSignedUnitNeighbor, (signedUnitLattice r s).mem_halfCharacteristicOverlattice_carrier_iff,
    (signedUnitLattice r s).mem_shiftedHalfCharacteristicOverlattice_carrier_iff,
    mem_evenSublattice_signedUnitSignFlipEquiv_iff]
  refine or_congr Iff.rfl ?_
  rw [← mem_evenSublattice_signedUnitSignFlipEquiv_iff r s k
    (x - ((signedUnitBasisVector r s k : Fin r ⊕ Fin s → ℚ) +
      (1 / 2 : ℚ) • (signedUnitCharacteristicVector r s : Fin r ⊕ Fin s → ℚ))), map_sub]
  have hdiff : signedUnitSignFlipEquiv r s k
      ((signedUnitBasisVector r s k : Fin r ⊕ Fin s → ℚ) +
        (1 / 2 : ℚ) • (signedUnitCharacteristicVector r s : Fin r ⊕ Fin s → ℚ)) -
      (1 / 2 : ℚ) • (signedUnitCharacteristicVector r s : Fin r ⊕ Fin s → ℚ) =
      -((2 : ℤ) • (signedUnitBasisVector r s k : Fin r ⊕ Fin s → ℚ)) := by
    ext l
    dsimp only [signedUnitSignFlipEquiv, LinearEquiv.coe_mk, LinearMap.coe_mk, AddHom.coe_mk,
      coe_signedUnitBasisVector, coe_signedUnitCharacteristicVector, Pi.add_apply, Pi.sub_apply,
      Pi.smul_apply, Pi.neg_apply]
    by_cases hlk : l = k
    · subst hlk
      simp only [Function.update_self, smul_eq_mul, zsmul_eq_mul]
      norm_num
    · simp [Function.update_of_ne hlk, Pi.single_eq_of_ne hlk]
  have htwo : (2 : ℤ) • (signedUnitBasisVector r s k : Fin r ⊕ Fin s → ℚ) ∈
      (signedUnitLattice r s).evenSublattice.carrier :=
    ((signedUnitLattice r s).mem_evenSublattice_carrier_iff
      ((2 : ℤ) • signedUnitBasisVector r s k)).mpr
      (((signedUnitLattice r s).mem_evenSubmodule_iff _).mp
        ((signedUnitLattice r s).two_smul_mem_evenSubmodule _))
  have heven : -((2 : ℤ) • (signedUnitBasisVector r s k : Fin r ⊕ Fin s → ℚ)) ∈
      (signedUnitLattice r s).evenSublattice.carrier :=
    (signedUnitLattice r s).evenSublattice.carrier.neg_mem htwo
  have hsub : signedUnitSignFlipEquiv r s k x - signedUnitSignFlipEquiv r s k
      ((signedUnitBasisVector r s k : Fin r ⊕ Fin s → ℚ) +
        (1 / 2 : ℚ) • (signedUnitCharacteristicVector r s : Fin r ⊕ Fin s → ℚ)) =
      (signedUnitSignFlipEquiv r s k x -
        (1 / 2 : ℚ) • (signedUnitCharacteristicVector r s : Fin r ⊕ Fin s → ℚ)) -
        (signedUnitSignFlipEquiv r s k
          ((signedUnitBasisVector r s k : Fin r ⊕ Fin s → ℚ) +
            (1 / 2 : ℚ) • (signedUnitCharacteristicVector r s : Fin r ⊕ Fin s → ℚ)) -
          (1 / 2 : ℚ) • (signedUnitCharacteristicVector r s : Fin r ⊕ Fin s → ℚ)) := by
    abel
  rw [hsub, hdiff, Submodule.sub_mem_iff_left _ heven]

/-- Flipping the `k`-th coordinate gives an explicit isometry from `evenSignedUnitNeighbor r s h8`
onto the shifted half-characteristic overlattice at `signedUnitBasisVector r s k`. -/
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
  map_carrier := by
    ext x
    rw [Submodule.mem_map_equiv]
    exact signedUnitSignFlipEquiv_mem_evenSignedUnitNeighbor_iff r s h8 k x

/-! ## Classification and uniqueness of even two-neighbors of `I_{r, s}` -/

private theorem pos_add_of_isNeighbor_signedUnitLattice {r s : ℕ}
    {M : IntegralLattice (Fin r ⊕ Fin s → ℚ)} (hM : (signedUnitLattice r s).IsNeighbor M 2) :
    0 < r + s := by
  by_contra h0
  obtain ⟨rfl, rfl⟩ : r = 0 ∧ s = 0 := by omega
  have hsub : Subsingleton (Fin 0 ⊕ Fin 0 → ℚ) := inferInstance
  have hcar : (signedUnitLattice 0 0).carrier ⊓ M.carrier = (signedUnitLattice 0 0).carrier := by
    ext x
    simp [Subsingleton.elim x 0]
  have hrel := hM.relIndex_inf_left
  rw [hcar, AddSubgroup.relIndex_self] at hrel
  omega

/-- Every even Kneser two-neighbor of `signedUnitLattice r s` forces `0 < r + s` and
`8 ∣ (r : ℤ) - s`, and is integrally isometric to `evenSignedUnitNeighbor r s h8`. -/
theorem nonempty_isometry_evenSignedUnitNeighbor_of_isNeighbor_signedUnitLattice {r s : ℕ}
    {M : IntegralLattice (Fin r ⊕ Fin s → ℚ)} (hM : (signedUnitLattice r s).IsNeighbor M 2)
    (hMe : M.IsEven) :
    ∃ h8 : 8 ∣ (r : ℤ) - s, Nonempty (Isometry (evenSignedUnitNeighbor r s h8) M) := by
  have hpos := pos_add_of_isNeighbor_signedUnitLattice hM
  obtain ⟨k⟩ : Nonempty (Fin r ⊕ Fin s) := Fintype.card_pos_iff.mp (by simpa using hpos)
  obtain ⟨h8', hEq⟩ :=
    (signedUnitLattice r s).eq_halfCharacteristicOverlattice_or_shifted_of_isNeighbor
      (isUnimodular_signedUnitLattice r s) hM hMe
      (isCharacteristicVector_signedUnitCharacteristicVector r s)
      (odd_integralNorm_signedUnitBasisVector r s k)
  have h8 : 8 ∣ (r : ℤ) - s := by
    rwa [integralNorm_signedUnitCharacteristicVector] at h8'
  refine ⟨h8, ?_⟩
  rcases hEq with rfl | rfl
  · exact ⟨Isometry.ofEq rfl⟩
  · exact ⟨signedUnitHalfCharacteristicIsometryShifted r s h8 k⟩

section Transport

universe u v

variable {V : Type u} [AddCommGroup V] [Module ℚ V]

private theorem isNeighbor_signedUnitLattice_transport_symm {r s : ℕ} {N K : IntegralLattice V}
    (e : Isometry (signedUnitLattice r s) N) (hK : N.IsNeighbor K 2) :
    (signedUnitLattice r s).IsNeighbor
      (K.transport (e : (Fin r ⊕ Fin s → ℚ) ≃ₗ[ℚ] V).symm) 2 := by
  have h' := hK.transport (e : (Fin r ⊕ Fin s → ℚ) ≃ₗ[ℚ] V).symm
  rwa [e.transport_symm_eq] at h'

/-- **Signature congruence mod `8` from an even Kneser two-neighbor of `I_{r, s}`.** If a lattice
`N` isometric to `signedUnitLattice r s` admits an even Kneser two-neighbor `K`, then
`8 ∣ (r : ℤ) - s`. -/
theorem eight_dvd_sub_of_isNeighbor_of_isometry_signedUnitLattice {r s : ℕ}
    {N K : IntegralLattice V} (e : Isometry (signedUnitLattice r s) N)
    (hK : N.IsNeighbor K 2) (hKe : K.IsEven) :
    8 ∣ (r : ℤ) - s := by
  have hK' := isNeighbor_signedUnitLattice_transport_symm e hK
  have hKe' : (K.transport (e : (Fin r ⊕ Fin s → ℚ) ≃ₗ[ℚ] V).symm).IsEven :=
    (K.transportIsometry (e : (Fin r ⊕ Fin s → ℚ) ≃ₗ[ℚ] V).symm).isEven_iff.mp hKe
  exact (nonempty_isometry_evenSignedUnitNeighbor_of_isNeighbor_signedUnitLattice hK' hKe').1

/-- **Every even Kneser two-neighbor of a lattice isometric to `I_{r, s}` is isometric to
`evenSignedUnitNeighbor r s h8`.** -/
theorem nonempty_isometry_evenSignedUnitNeighbor_of_isNeighbor_of_isometry_signedUnitLattice
    {r s : ℕ} {N K : IntegralLattice V} (e : Isometry (signedUnitLattice r s) N)
    (hK : N.IsNeighbor K 2) (hKe : K.IsEven) (h8 : 8 ∣ (r : ℤ) - s) :
    Nonempty (Isometry (evenSignedUnitNeighbor r s h8) K) := by
  have hK' := isNeighbor_signedUnitLattice_transport_symm e hK
  have hKe' : (K.transport (e : (Fin r ⊕ Fin s → ℚ) ≃ₗ[ℚ] V).symm).IsEven :=
    (K.transportIsometry (e : (Fin r ⊕ Fin s → ℚ) ≃ₗ[ℚ] V).symm).isEven_iff.mp hKe
  obtain ⟨_, ⟨f⟩⟩ :=
    nonempty_isometry_evenSignedUnitNeighbor_of_isNeighbor_signedUnitLattice hK' hKe'
  exact ⟨f.trans (K.transportIsometry (e : (Fin r ⊕ Fin s → ℚ) ≃ₗ[ℚ] V).symm).symm⟩

/-- **Uniqueness up to isometry of even Kneser two-neighbors of `I_{r, s}`.** Any two even Kneser
two-neighbors `K₁` and `K₂` of lattices `N₁` and `N₂` isometric to `signedUnitLattice r s` are
integrally isometric. -/
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

end Transport

/-- `evenSignedUnitNeighbor 1 1` (`I_{1, 1}^+`) is integrally isometric to `hyperbolicPlane`. -/
theorem nonempty_isometry_evenSignedUnitNeighbor_one_one_hyperbolicPlane :
    Nonempty (Isometry (evenSignedUnitNeighbor 1 1 (by decide)) hyperbolicPlane) := by
  obtain ⟨f⟩ := nonempty_isometry_evenSignedUnitNeighbor_of_isNeighbor_of_isometry_signedUnitLattice
    signedUnitLatticeOneOneIsometryIndefiniteUnitPlane isNeighbor_indefiniteUnitPlaneFirstNeighbor
    isEven_indefiniteUnitPlaneFirstNeighbor (by decide)
  exact ⟨f.trans hyperbolicPlaneIsometryIndefiniteUnitPlaneFirstNeighbor.symm⟩

end TauCeti.IntegralLattice
