/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.IntegralLattice.Characteristic.ParityKernel
public import TauCeti.LinearAlgebra.IntegralLattice.Examples
public import TauCeti.LinearAlgebra.IntegralLattice.SignedUnit

/-!
# Even Kneser two-neighbors of `I_{r, s}`

When `8 ∣ (r : ℤ) - s`, the standard signed unit lattice `signedUnitLattice r s` (`I_{r, s}`) has
the canonical even unimodular overlattice `evenSignedUnitNeighbor r s h8` (`I_{r, s}^+`) of its
even sublattice `(I_{r, s})_even`. When `0 < r + s`, `I_{r, s}^+` is a Kneser two-neighbor of
`I_{r, s}`, and coordinate sign-flip makes the even two-neighbor unique up to isometry: every even
Kneser two-neighbor of a lattice isometric to `I_{r, s}` forces `8 ∣ (r : ℤ) - s` and is isometric
to `I_{r, s}^+`.

In signature `(1, 0, 1)`, `evenSignedUnitNeighbor 1 1` is explicitly isometric to
`hyperbolicPlane`, so for any even lattice `Y`, `Y ⊕ hyperbolicPlane` is isometric to an even
Kneser two-neighbor of `Y ⊕ signedUnitLattice 1 1`.

## Main definitions

* `TauCeti.IntegralLattice.evenSignedUnitNeighbor`: the canonical even unimodular overlattice
  `I_{r, s}^+` of `(I_{r, s})_even` when `8 ∣ (r : ℤ) - s`.
* `TauCeti.IntegralLattice.evenSignedUnitNeighborIsometryShiftedHalfCharacteristicOverlattice`:
  the sign-flip isometry identifying `I_{r, s}^+` with the shifted half-characteristic overlattice.
* `TauCeti.IntegralLattice.hyperbolicPlaneIsometryEvenSignedUnitNeighborOneOne`: the explicit
  isometry `hyperbolicPlane ≅ evenSignedUnitNeighbor 1 1`.

## Main results

* `TauCeti.IntegralLattice.mem_evenSignedUnitNeighbor_carrier_iff`: explicit coordinate membership
  characterization of `I_{r, s}^+`.
* `TauCeti.IntegralLattice.nonempty_isometry_evenSignedUnitNeighbor_of_isNeighbor_signedUnitLattice`
  — every even two-neighbor of `I_{r, s}` forces `8 ∣ (r : ℤ) - s` and is isometric to `I_{r, s}^+`.
* `TauCeti.IntegralLattice.nonempty_isometry_of_isNeighbor_of_isometry_signedUnitLattice`:
  uniqueness up to isometry of even two-neighbors of any lattice isometric to `I_{r, s}`.
* `TauCeti.IntegralLattice.exists_isNeighbor_orthogonalSum_signedUnitLattice_one_one`: swap
  turning `Y ⊕ hyperbolicPlane` into an even two-neighbor of `Y ⊕ I_{1, 1}` for even `Y`.

## References

* J.-P. Serre, *A Course in Arithmetic*, Chapter V, §2.2.
* J. Milnor and D. Husemoller, *Symmetric Bilinear Forms*, Chapter II, §§2–5.
* M. Kneser, *Klassenzahlen definiter quadratischer Formen*, Arch. Math. 8 (1957), 241--250.
-/

public section

open Module

namespace TauCeti.IntegralLattice

/-- Divisibility of `(r : ℤ) - s` by `8` gives `8 ∣ integralNorm w`. -/
theorem eight_dvd_integralNorm_signedUnitCharacteristicVector {r s : ℕ} (h8 : 8 ∣ (r : ℤ) - s) :
    8 ∣ (signedUnitLattice r s).integralNorm (signedUnitCharacteristicVector r s) := by simpa

/-- The canonical even unimodular two-neighbor `I_{r, s}^+` (an overlattice of
`(signedUnitLattice r s).evenSublattice`) when `8 ∣ (r : ℤ) - s`. When `0 < r + s` it is a
Kneser two-neighbor of `signedUnitLattice r s`; for `r = s = 0` it coincides with
`signedUnitLattice 0 0`. -/
noncomputable def evenSignedUnitNeighbor (r s : ℕ) (h8 : 8 ∣ (r : ℤ) - s) :
    IntegralLattice (Fin r ⊕ Fin s → ℚ) :=
  (signedUnitLattice r s).halfCharacteristicOverlattice
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
  (signedUnitLattice r s).isUnimodular_halfCharacteristicOverlattice
    (isUnimodular_signedUnitLattice r s) ..

/-- `evenSignedUnitNeighbor r s h8` is a Kneser two-neighbor of `signedUnitLattice r s` whenever
`0 < r + s`. -/
theorem isNeighbor_evenSignedUnitNeighbor {r s : ℕ} (hpos : 0 < r + s) (h8 : 8 ∣ (r : ℤ) - s) :
    (signedUnitLattice r s).IsNeighbor (evenSignedUnitNeighbor r s h8) 2 :=
  (signedUnitLattice r s).isNeighbor_halfCharacteristicOverlattice
    (not_isEven_signedUnitLattice_of_pos hpos) _ _

/-- `evenSignedUnitNeighbor r s h8` has signature `(r, 0, s)`. -/
@[simp] theorem evenSignedUnitNeighbor_signature (r s : ℕ) (h8 : 8 ∣ (r : ℤ) - s) :
    (evenSignedUnitNeighbor r s h8).signature = (r, 0, s) := by
  rw [signature_eq_of_form_eq (evenSignedUnitNeighbor_form r s h8), signedUnitLattice_signature]

/-- Explicit coordinate membership in `evenSignedUnitNeighbor r s h8`: a vector lies in
`I_{r, s}^+` if and only if either all coordinates are integers with even sum, or all coordinates
lie in `ℤ + 1 / 2` with total sum `2 * m + ((r : ℚ) + s) / 2` for some integer `m`. -/
theorem mem_evenSignedUnitNeighbor_carrier_iff (r s : ℕ) (h8 : 8 ∣ (r : ℤ) - s)
    (x : Fin r ⊕ Fin s → ℚ) :
    x ∈ (evenSignedUnitNeighbor r s h8).carrier ↔
      ((∀ k, ∃ z : ℤ, (z : ℚ) = x k) ∧
        ∃ m : ℤ, (∑ i : Fin r, x (.inl i)) + ∑ j : Fin s, x (.inr j) = 2 * m) ∨
      ((∀ k, ∃ z : ℤ, (z : ℚ) + 1 / 2 = x k) ∧
        ∃ m : ℤ, (∑ i : Fin r, x (.inl i)) + ∑ j : Fin s, x (.inr j) =
          2 * m + ((r : ℚ) + s) / 2) := by
  rw [evenSignedUnitNeighbor, (signedUnitLattice r s).mem_halfCharacteristicOverlattice_carrier_iff,
    mem_evenSublattice_signedUnitLattice_carrier_iff,
    mem_evenSublattice_signedUnitLattice_carrier_iff]
  refine or_congr Iff.rfl (and_congr (forall_congr' fun k ↦ exists_congr fun z ↦ ?_)
    (exists_congr fun m ↦ ?_))
  · simp only [Pi.sub_apply, Pi.smul_apply, coe_signedUnitCharacteristicVector, smul_eq_mul,
      mul_one]
    exact ⟨fun hz ↦ by linarith, fun hz ↦ by linarith⟩
  · simp only [Pi.sub_apply, Pi.smul_apply, coe_signedUnitCharacteristicVector, smul_eq_mul,
      mul_one, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul]
    exact ⟨fun hm ↦ by linarith, fun hm ↦ by linarith⟩

private theorem signedUnitSignFlipIsometry_mem_evenSublattice_iff (r s : ℕ) (k : Fin r ⊕ Fin s)
    (u : Fin r ⊕ Fin s → ℚ) :
    signedUnitSignFlipIsometry r s k u ∈ (signedUnitLattice r s).evenSublattice.carrier ↔
      u ∈ (signedUnitLattice r s).evenSublattice.carrier := by
  have heq : (signedUnitLattice r s).evenSublattice.transport
      (signedUnitSignFlipIsometry r s k).toLinearEquiv =
        (signedUnitLattice r s).evenSublattice := by
    rw [← evenSublattice_transport, (signedUnitSignFlipIsometry r s k).transport_eq]
  have hmem := SetLike.ext_iff.mp (congrArg IntegralLattice.carrier heq) u
  rw [transport_carrier, Submodule.mem_map_equiv, LinearEquiv.restrictScalars_symm_apply] at hmem
  simpa only [← Isometry.coe_symm, signedUnitSignFlipIsometry_symm] using hmem

/-- Flipping coordinate `k` maps `evenSignedUnitNeighbor r s h8` isometrically onto the shifted
half-characteristic overlattice `shiftedHalfCharacteristicOverlattice`. -/
noncomputable def evenSignedUnitNeighborIsometryShiftedHalfCharacteristicOverlattice
    (r s : ℕ) (h8 : 8 ∣ (r : ℤ) - s) (k : Fin r ⊕ Fin s) :
    Isometry (evenSignedUnitNeighbor r s h8)
      ((signedUnitLattice r s).shiftedHalfCharacteristicOverlattice
        (isCharacteristicVector_signedUnitCharacteristicVector r s)
        (eight_dvd_integralNorm_signedUnitCharacteristicVector h8)
        (signedUnitBasisVector r s k)) where
  toLinearEquiv := (signedUnitSignFlipIsometry r s k).toLinearEquiv
  map_app' x y := by
    rw [evenSignedUnitNeighbor_form, shiftedHalfCharacteristicOverlattice_form]
    exact (signedUnitSignFlipIsometry r s k).map_app x y
  map_carrier := Submodule.ext fun x ↦ by
    rw [Submodule.mem_map_equiv, LinearEquiv.restrictScalars_symm_apply, ← Isometry.coe_symm,
      signedUnitSignFlipIsometry_symm, evenSignedUnitNeighbor,
      (signedUnitLattice r s).mem_halfCharacteristicOverlattice_carrier_iff,
      (signedUnitLattice r s).mem_shiftedHalfCharacteristicOverlattice_carrier_iff,
      signedUnitSignFlipIsometry_mem_evenSublattice_iff]
    refine or_congr Iff.rfl ?_
    rw [← signedUnitSignFlipIsometry_mem_evenSublattice_iff r s k (x - _), map_sub]
    let e := (signedUnitBasisVector r s k : Fin r ⊕ Fin s → ℚ)
    let w := (signedUnitCharacteristicVector r s : Fin r ⊕ Fin s → ℚ)
    have hdiff : signedUnitSignFlipIsometry r s k (e + (1 / 2 : ℚ) • w) - (1 / 2 : ℚ) • w =
        -((2 : ℤ) • e) := by
      ext l
      rw [Pi.sub_apply, signedUnitSignFlipIsometry_apply, Pi.neg_apply, Pi.smul_apply]
      by_cases hlk : l = k
      · subst hlk
        simp only [e, w, Function.update_self, Pi.add_apply, Pi.smul_apply,
          coe_signedUnitBasisVector, coe_signedUnitCharacteristicVector, Pi.single_eq_same,
          smul_eq_mul, zsmul_eq_mul]
        norm_num
      · simp only [e, w, Function.update_of_ne hlk, Pi.add_apply, Pi.smul_apply,
          coe_signedUnitBasisVector, coe_signedUnitCharacteristicVector, Pi.single_eq_of_ne hlk,
          smul_eq_mul, zsmul_eq_mul, zero_add, sub_self, mul_zero, neg_zero]
    have he2 : ((2 : ℤ) • signedUnitBasisVector r s k : Fin r ⊕ Fin s → ℚ) ∈
        (signedUnitLattice r s).evenSublattice.carrier :=
      ((signedUnitLattice r s).mem_evenSublattice_carrier_iff _).mpr
        (((signedUnitLattice r s).mem_evenSubmodule_iff _).mp
          ((signedUnitLattice r s).two_smul_mem_evenSubmodule _))
    rw [← sub_sub_sub_cancel_right (signedUnitSignFlipIsometry r s k x)
        (signedUnitSignFlipIsometry r s k (e + (1 / 2 : ℚ) • w)) ((1 / 2 : ℚ) • w), hdiff,
      Submodule.sub_mem_iff_left _ ((signedUnitLattice r s).evenSublattice.carrier.neg_mem he2)]

/-- `evenSignedUnitNeighborIsometryShiftedHalfCharacteristicOverlattice` negates coordinate `k`. -/
@[simp] theorem evenSignedUnitNeighborIsometryShiftedHalfCharacteristicOverlattice_apply
    (r s : ℕ) (h8 : 8 ∣ (r : ℤ) - s) (k : Fin r ⊕ Fin s) (x : Fin r ⊕ Fin s → ℚ) :
    evenSignedUnitNeighborIsometryShiftedHalfCharacteristicOverlattice r s h8 k x =
      Function.update x k (-x k) :=
  signedUnitSignFlipIsometry_apply r s k x

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
  rcases hEq with rfl | rfl
  exacts [⟨h8, ⟨Isometry.ofEq rfl⟩⟩,
    ⟨h8, ⟨evenSignedUnitNeighborIsometryShiftedHalfCharacteristicOverlattice r s h8 k⟩⟩]

private def hyperbolicPlaneToSignedUnitOneOneEquiv :
    (Fin 2 → ℚ) ≃ₗ[ℚ] (Fin 1 ⊕ Fin 1 → ℚ) where
  toFun u := Sum.elim (fun _ ↦ u 0 / 2 + u 1) (fun _ ↦ u 0 / 2 - u 1)
  invFun x := ![x (.inl 0) + x (.inr 0), (x (.inl 0) - x (.inr 0)) / 2]
  map_add' u v := by ext (i | j) <;> simp <;> ring
  map_smul' c u := by ext (i | j) <;> simp <;> ring
  left_inv u := by ext i; fin_cases i <;> simp
  right_inv x := by
    ext (i | j)
    · fin_cases i; simp; ring
    · fin_cases j; simp; ring

private theorem hyperbolicPlaneToSignedUnitOneOneEquiv_apply (u : Fin 2 → ℚ) :
    hyperbolicPlaneToSignedUnitOneOneEquiv u =
      Sum.elim (fun _ ↦ u 0 / 2 + u 1) (fun _ ↦ u 0 / 2 - u 1) := (rfl)

private theorem hyperbolicPlaneToSignedUnitOneOneEquiv_symm_apply (x : Fin 1 ⊕ Fin 1 → ℚ) :
    hyperbolicPlaneToSignedUnitOneOneEquiv.symm x =
      ![x (.inl 0) + x (.inr 0), (x (.inl 0) - x (.inr 0)) / 2] := (rfl)

private theorem exists_int_add_shift_iff_half_sub (x : Fin 1 ⊕ Fin 1 → ℚ) (c : ℚ) (m : ℤ)
    (hsum : x (.inl 0) + x (.inr 0) = 2 * m + 2 * c) :
    (∀ k : Fin 1 ⊕ Fin 1, ∃ z : ℤ, (z : ℚ) + c = x k) ↔
      ∃ q : ℤ, (q : ℚ) = (x (.inl 0) - x (.inr 0)) / 2 := by
  constructor
  · intro hZ
    obtain ⟨za, hza⟩ := hZ (.inl 0)
    exact ⟨za - m, by push_cast; linarith⟩
  · rintro ⟨q, hq⟩ (i | j)
    · fin_cases i; exact ⟨m + q, by push_cast; linarith⟩
    · fin_cases j; exact ⟨m - q, by push_cast; linarith⟩

/-- Explicit integral isometry from `hyperbolicPlane` to `evenSignedUnitNeighbor 1 1`. -/
noncomputable def hyperbolicPlaneIsometryEvenSignedUnitNeighborOneOne :
    Isometry hyperbolicPlane (evenSignedUnitNeighbor 1 1 (by decide)) where
  toLinearEquiv := hyperbolicPlaneToSignedUnitOneOneEquiv
  map_app' u v := by
    simp only [AddHom.toFun_eq_coe, LinearMap.coe_toAddHom, LinearEquiv.coe_coe,
      hyperbolicPlaneToSignedUnitOneOneEquiv_apply, evenSignedUnitNeighbor_form,
      signedUnitLattice_form_apply, hyperbolicPlane_form_apply, Fin.sum_univ_one, Sum.elim_inl,
      Sum.elim_inr]
    ring
  map_carrier := Submodule.ext fun x ↦ by
    rw [Submodule.mem_map_equiv, LinearEquiv.restrictScalars_symm_apply,
      hyperbolicPlaneToSignedUnitOneOneEquiv_symm_apply, mem_hyperbolicPlane_carrier_iff,
      mem_evenSignedUnitNeighbor_carrier_iff]
    simp only [Fin.forall_fin_two, Matrix.cons_val_zero, Matrix.cons_val_one, Fin.sum_univ_one]
    constructor
    · rintro ⟨⟨p, hp⟩, hq⟩
      rcases Int.even_or_odd p with ⟨m, rfl⟩ | ⟨m, rfl⟩
      · have hsum : x (.inl 0) + x (.inr 0) = 2 * m := by push_cast at hp; linarith
        left
        refine ⟨fun k ↦ ?_, m, hsum⟩
        have hZ := (exists_int_add_shift_iff_half_sub x 0 m (by linarith)).mpr hq k
        simpa only [add_zero] using hZ
      · have hsum : x (.inl 0) + x (.inr 0) = 2 * m + 1 := by push_cast at hp; linarith
        right
        refine ⟨(exists_int_add_shift_iff_half_sub x (1 / 2) m (by linarith)).mpr hq, m, ?_⟩
        norm_num; linarith
    · rintro (⟨hZ, m, hm⟩ | ⟨hZ, m, hm⟩)
      · refine ⟨⟨2 * m, by push_cast; linarith⟩,
          (exists_int_add_shift_iff_half_sub x 0 m (by linarith)).mp fun k ↦ ?_⟩
        simpa only [add_zero] using hZ k
      · have hsum : x (.inl 0) + x (.inr 0) = 2 * m + 2 * (1 / 2 : ℚ) := by
          norm_num at hm ⊢; linarith
        exact ⟨⟨2 * m + 1, by push_cast; linarith⟩,
          (exists_int_add_shift_iff_half_sub x (1 / 2) m hsum).mp hZ⟩

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

/-- **Signature congruence mod `8` from an even Kneser two-neighbor of `I_{r, s}`.** -/
theorem eight_dvd_sub_of_isNeighbor_of_isometry_signedUnitLattice {r s : ℕ}
    {N K : IntegralLattice V} (e : Isometry (signedUnitLattice r s) N)
    (hK : N.IsNeighbor K 2) (hKe : K.IsEven) : 8 ∣ (r : ℤ) - s :=
  (nonempty_isometry_evenSignedUnitNeighbor_of_isNeighbor_signedUnitLattice
    (hK.transport_symm_of_isometry e)
    ((K.transportIsometry (e : (Fin r ⊕ Fin s → ℚ) ≃ₗ[ℚ] V).symm).isEven_iff.mp hKe)).1

/-- **Every even Kneser two-neighbor of a lattice isometric to `I_{r, s}` is isometric to
`evenSignedUnitNeighbor r s h8`.** -/
theorem nonempty_isometry_evenSignedUnitNeighbor_of_isNeighbor_of_isometry_signedUnitLattice
    {r s : ℕ} {N K : IntegralLattice V} (e : Isometry (signedUnitLattice r s) N)
    (hK : N.IsNeighbor K 2) (hKe : K.IsEven) (h8 : 8 ∣ (r : ℤ) - s) :
    Nonempty (Isometry (evenSignedUnitNeighbor r s h8) K) := by
  obtain ⟨_, ⟨f⟩⟩ := nonempty_isometry_evenSignedUnitNeighbor_of_isNeighbor_signedUnitLattice
    (hK.transport_symm_of_isometry e)
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
