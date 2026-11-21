/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.Rank
public import TauCeti.NumberTheory.IntegralLattice.Localization.Discriminant.Basic
import Mathlib.NumberTheory.Padics.RingHoms
import TauCeti.Algebra.Group.Primary.Generators
import TauCeti.LinearAlgebra.BilinearForm.Diagonalization
import TauCeti.NumberTheory.Padics.PadicIntegers

/-!
# Additive structure of the `p`-primary discriminant group from a diagonal Jordan form

Let `L` be a nondegenerate integral lattice and `p` a prime (including `p = 2`). Whenever the
localization `L_p = ℤ_p ⊗[ℤ] L` has an orthogonal basis `b` with self-pairings
`B(bᵢ, bᵢ) = uᵢ pᵏⁱ` (`uᵢ ∈ ℤ_pˣ`), the dual classes of `p^{-kᵢ} bᵢ` give an additive isomorphism
`∏ᵢ ℤ/pᵏⁱ ≃+ (A_L)_p` (`TauCeti.IntegralLattice.piZModPowEquivPrimaryComponent`), and hence the
generator count `AddGroup.rank (A_L)_p = #{i | kᵢ ≠ 0}`
(`TauCeti.IntegralLattice.rank_primaryComponent_discriminantGroup_eq_card_filter`).

## Main results

* `TauCeti.IntegralLattice.diagonalDualVec` and
  `TauCeti.IntegralLattice.localizationDualToCompletion_diagonalDualVec`: the chosen `p`-adic
  dual basis vectors representing `p^{-kᵢ} bᵢ`.
* `TauCeti.IntegralLattice.piZModPowEquivPrimaryComponent` and
  `TauCeti.IntegralLattice.piZModPowEquivPrimaryComponent_intCast`: additive equivalence
  `∏ᵢ ℤ/pᵏⁱ ≃+ (A_L)_p` and its evaluation on integer tuples.
* `TauCeti.IntegralLattice.rank_primaryComponent_discriminantGroup_eq_card_filter`: generator count
  `AddGroup.rank (A_L)_p = #{i | kᵢ ≠ 0}`.
-/

public section

open Module TensorProduct AddCommGroup Finset

namespace TauCeti.IntegralLattice

variable {V : Type*} [AddCommGroup V] [Module ℚ V] {L : IntegralLattice V} [L.IsNondegenerate]
  {p : ℕ} [Fact p.Prime] {ι : Type*} {b : Basis ι ℤ_[p] (L.LocalCarrier p)} {u : ι → ℤ_[p]ˣ}
  {k : ι → ℕ}

/-! ### The dual basis vectors `p^{-kᵢ} bᵢ` -/

/-- For a diagonal Jordan form `B(bᵢ, bᵢ) = uᵢ pᵏⁱ`, the vector `p^{-kᵢ} bᵢ` of the completed
rational space lies in the localized dual. -/
private theorem exists_localizationDualToCompletion_eq
    (hb : (L.localIntegralForm p).iIsOrtho b)
    (hbu : ∀ i, L.localIntegralForm p (b i) (b i) = u i * (p : ℤ_[p]) ^ k i) (i : ι) :
    ∃ y : L.LocalDualCarrier p, L.localizationDualToCompletion p y =
      ((p : ℚ_[p]) ^ k i)⁻¹ • L.localizationToCompletion p (b i) := by
  have hp : (p : ℚ_[p]) ≠ 0 := Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero
  rw [← LinearMap.mem_range, range_localizationDualToCompletion,
    LinearMap.BilinForm.mem_dualSubmodule]
  rintro _ ⟨x, rfl⟩
  refine Submodule.mem_one.mpr ⟨b.repr x i * u i, ?_⟩
  rw [LinearMap.BilinForm.smul_left, completedRationalForm_localizationToCompletion,
    hb.apply_basis_left, hbu]
  simp only [map_mul, map_pow, map_natCast]
  field_simp

/-- Chosen `p`-adic dual vector representing `p^{-kᵢ} bᵢ` for a diagonal Jordan form
`B(bᵢ, bᵢ) = uᵢ pᵏⁱ`. -/
noncomputable def diagonalDualVec
    (hb : (L.localIntegralForm p).iIsOrtho b)
    (hbu : ∀ i, L.localIntegralForm p (b i) (b i) = u i * (p : ℤ_[p]) ^ k i) (i : ι) :
    L.LocalDualCarrier p :=
  Classical.choose (exists_localizationDualToCompletion_eq hb hbu i)

/-- The chosen dual vector `diagonalDualVec` embeds into the completed rational space as
`p^{-kᵢ} bᵢ`. -/
theorem localizationDualToCompletion_diagonalDualVec
    (hb : (L.localIntegralForm p).iIsOrtho b)
    (hbu : ∀ i, L.localIntegralForm p (b i) (b i) = u i * (p : ℤ_[p]) ^ k i) (i : ι) :
    L.localizationDualToCompletion p (diagonalDualVec hb hbu i) =
      ((p : ℚ_[p]) ^ k i)⁻¹ • L.localizationToCompletion p (b i) :=
  Classical.choose_spec (exists_localizationDualToCompletion_eq hb hbu i)

variable {y : ι → L.LocalDualCarrier p}

/-- The dual vector `p^{-kᵢ} bᵢ` pairs with `bⱼ` to `δᵢⱼ uᵢ`. -/
theorem localDualPairingEquiv_basis [DecidableEq ι]
    (hb : (L.localIntegralForm p).iIsOrtho b)
    (hbu : ∀ i, L.localIntegralForm p (b i) (b i) = u i * (p : ℤ_[p]) ^ k i)
    (hy : ∀ i, L.localizationDualToCompletion p (y i) =
      ((p : ℚ_[p]) ^ k i)⁻¹ • L.localizationToCompletion p (b i)) (i j : ι) :
    L.localDualPairingEquiv p (y i) (b j) = if i = j then (u i : ℤ_[p]) else 0 := by
  have hp : (p : ℚ_[p]) ≠ 0 := Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero
  apply FaithfulSMul.algebraMap_injective ℤ_[p] ℚ_[p]
  rw [← completedRationalForm_localizationDualToCompletion, hy, LinearMap.BilinForm.smul_left,
    completedRationalForm_localizationToCompletion]
  split_ifs with hij
  · subst hij
    rw [hbu]
    simp only [map_mul, map_pow, map_natCast]
    field_simp
  · simp [LinearMap.BilinForm.iIsOrtho_def.mp hb i j hij]

omit [L.IsNondegenerate] in
/-- `pᵏⁱ` times the dual vector `p^{-kᵢ} bᵢ` is `bᵢ`. -/
private theorem pow_nsmul_eq_localCarrierToDual
    (hy : ∀ i, L.localizationDualToCompletion p (y i) =
      ((p : ℚ_[p]) ^ k i)⁻¹ • L.localizationToCompletion p (b i)) (i : ι) :
    p ^ k i • y i = L.localCarrierToDual p (b i) := by
  have hp : (p : ℚ_[p]) ≠ 0 := Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero
  apply L.localizationDualToCompletion_injective p
  rw [map_nsmul, localizationDualToCompletion_localCarrierToDual, hy,
    ← Nat.cast_smul_eq_nsmul ℚ_[p], smul_smul, Nat.cast_pow, mul_inv_cancel₀ (pow_ne_zero _ hp),
    one_smul]

/-- The classes of the dual vectors `p^{-kᵢ} bᵢ` generate the discriminant group of `L_p`. -/
private theorem exists_mk_eq_sum_nsmul [Fintype ι] (hb : (L.localIntegralForm p).iIsOrtho b)
    (hbu : ∀ i, L.localIntegralForm p (b i) (b i) = u i * (p : ℤ_[p]) ^ k i)
    (hy : ∀ i, L.localizationDualToCompletion p (y i) =
      ((p : ℚ_[p]) ^ k i)⁻¹ • L.localizationToCompletion p (b i)) (z : L.LocalDualCarrier p) :
    ∃ n : ι → ℕ, (Submodule.Quotient.mk z : L.LocalDiscriminantGroup p) =
      ∑ i, n i • Submodule.Quotient.mk (y i) := by
  classical
  -- The coordinates of `z` in the basis `p^{-kᵢ} bᵢ` are `B(z, bᵢ) uᵢ⁻¹`.
  set c : ι → ℤ_[p] := fun i ↦ L.localDualPairingEquiv p z (b i) * ↑(u i)⁻¹
  have hz : z = ∑ i, c i • y i := by
    apply (L.localDualPairingEquiv p).injective
    refine b.ext fun j ↦ ?_
    simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply,
      localDualPairingEquiv_basis hb hbu hy, smul_eq_mul, mul_ite, mul_zero,
      Finset.sum_ite_eq', Finset.mem_univ, ite_true, c]
    rw [mul_assoc, Units.inv_mul, mul_one]
  -- Reduce each coordinate modulo `pᵏⁱ`; the remainders contribute vectors of `L_p`.
  choose t ht using fun i ↦ Ideal.mem_span_singleton'.mp (PadicInt.appr_spec (k i) (c i))
  refine ⟨fun i ↦ (c i).appr (k i), ?_⟩
  have hc i : c i = ((c i).appr (k i) : ℤ_[p]) + t i * (p : ℤ_[p]) ^ k i := by
    rw [ht i, add_sub_cancel]
  rw [hz, ← Submodule.mkQ_apply, map_sum]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  have h0 : (Submodule.Quotient.mk ((p : ℤ_[p]) ^ k i • y i) : L.LocalDiscriminantGroup p) = 0 := by
    rw [← Nat.cast_pow, Nat.cast_smul_eq_nsmul, pow_nsmul_eq_localCarrierToDual hy]
    exact (Submodule.Quotient.mk_eq_zero _).mpr ⟨b i, rfl⟩
  rw [Submodule.mkQ_apply, hc i, add_smul, mul_smul, Submodule.Quotient.mk_add,
    Submodule.Quotient.mk_smul _ (t i), h0, smul_zero, add_zero, Nat.cast_smul_eq_nsmul,
    Submodule.Quotient.mk_smul]

/-! ### The additive equivalence `∏ᵢ ℤ/pᵏⁱ ≃+ (A_L)_p` -/

/-- The `p`-primary class of the dual vector `p^{-kᵢ} bᵢ` is killed by `pᵏⁱ`. -/
theorem pow_nsmul_symm_mk_eq_zero
    (hy : ∀ i, L.localizationDualToCompletion p (y i) =
      ((p : ℚ_[p]) ^ k i)⁻¹ • L.localizationToCompletion p (b i)) (i : ι) :
    p ^ k i • (L.primaryComponentEquivLocalDiscriminantGroup p).symm
      (Submodule.Quotient.mk (y i)) = 0 := by
  rw [← map_nsmul, ← Submodule.Quotient.mk_smul, pow_nsmul_eq_localCarrierToDual hy,
    (Submodule.Quotient.mk_eq_zero _).mpr (LinearMap.mem_range_self _ (b i)), map_zero]

/-- The additive homomorphism `(cᵢ) ↦ ∑ᵢ cᵢ [p^{-kᵢ} bᵢ]` from `∏ᵢ ℤ/pᵏⁱ` to `(A_L)_p`. -/
private noncomputable def piZModPowHom [Fintype ι]
    (hy : ∀ i, L.localizationDualToCompletion p (y i) =
      ((p : ℚ_[p]) ^ k i)⁻¹ • L.localizationToCompletion p (b i)) :
    (∀ i, ZMod (p ^ k i)) →+ primaryComponent L.DiscriminantGroup p :=
  haveI : ∀ i, NeZero (p ^ k i) := fun i ↦ ⟨pow_ne_zero _ (Fact.out : p.Prime).ne_zero⟩
  ∑ i, (ZMod.lift (p ^ k i) ⟨zmultiplesHom _
      ((L.primaryComponentEquivLocalDiscriminantGroup p).symm (Submodule.Quotient.mk (y i))), by
    rw [zmultiplesHom_apply, natCast_zsmul]
    exact pow_nsmul_symm_mk_eq_zero hy i⟩).comp
    (Pi.evalAddMonoidHom (fun i ↦ ZMod (p ^ k i)) i)

private theorem piZModPowHom_intCast [Fintype ι]
    (hy : ∀ i, L.localizationDualToCompletion p (y i) =
      ((p : ℚ_[p]) ^ k i)⁻¹ • L.localizationToCompletion p (b i)) (n : ι → ℤ) :
    piZModPowHom hy (fun i ↦ (n i : ZMod (p ^ k i))) =
      ∑ i, n i • (L.primaryComponentEquivLocalDiscriminantGroup p).symm
        (Submodule.Quotient.mk (y i)) := by
  have : ∀ i, NeZero (p ^ k i) := fun i ↦ ⟨pow_ne_zero _ (Fact.out : p.Prime).ne_zero⟩
  simp [piZModPowHom, ZMod.lift_coe]

private theorem bijective_piZModPowHom [Fintype ι]
    (hb : (L.localIntegralForm p).iIsOrtho b)
    (hbu : ∀ i, L.localIntegralForm p (b i) (b i) = u i * (p : ℤ_[p]) ^ k i)
    (hy : ∀ i, L.localizationDualToCompletion p (y i) =
      ((p : ℚ_[p]) ^ k i)⁻¹ • L.localizationToCompletion p (b i)) :
    Function.Bijective (piZModPowHom hy) := by
  classical
  have : ∀ i, NeZero (p ^ k i) := fun i ↦ ⟨pow_ne_zero _ (Fact.out : p.Prime).ne_zero⟩
  refine ⟨(injective_iff_map_eq_zero _).mpr fun c hc ↦ ?_, fun c ↦ ?_⟩
  · have hc_val : c = fun i ↦ (((c i).val : ℤ) : ZMod (p ^ k i)) :=
      funext fun i ↦ by rw [Int.cast_natCast, ZMod.natCast_zmod_val]
    rw [hc_val, piZModPowHom_intCast] at hc
    have hmk : (Submodule.Quotient.mk (∑ i, (c i).val • y i) : L.LocalDiscriminantGroup p) = 0 := by
      have hmap := congrArg (L.primaryComponentEquivLocalDiscriminantGroup p) hc
      rw [map_zero, map_sum] at hmap
      rw [← Submodule.mkQ_apply, map_sum]
      refine (Finset.sum_congr rfl fun i _ ↦ ?_).trans hmap
      rw [Submodule.mkQ_apply, Submodule.Quotient.mk_smul, ← natCast_zsmul, map_zsmul,
        (L.primaryComponentEquivLocalDiscriminantGroup p).apply_symm_apply, natCast_zsmul]
    obtain ⟨x, hx⟩ := (Submodule.Quotient.mk_eq_zero _).mp hmk
    ext j
    have hpair := congrArg (fun w ↦ L.localDualPairingEquiv p w (b j)) hx
    simp only [localDualPairingEquiv_localCarrierToDual, (L.isSymm_localIntegralForm p).eq x (b j),
      hb.apply_basis_left j x, hbu, map_sum, map_nsmul, LinearMap.sum_apply, LinearMap.smul_apply,
      localDualPairingEquiv_basis hb hbu hy, nsmul_eq_mul, mul_ite, mul_zero,
      Finset.sum_ite_eq', Finset.mem_univ, ite_true] at hpair
    have hdvd : (p : ℤ_[p]) ^ k j ∣ ((c j).val : ℤ_[p]) := by
      refine ⟨b.repr x j, (u j).isUnit.mul_right_cancel ?_⟩
      linear_combination -hpair
    exact (ZMod.natCast_zmod_val (c j)) ▸
      (ZMod.natCast_eq_zero_iff (c j).val (p ^ k j)).mpr
        ((PadicInt.pow_p_dvd_natCast_iff _ _).mp hdvd)
  · obtain ⟨z, hz⟩ := Submodule.Quotient.mk_surjective _
      (L.primaryComponentEquivLocalDiscriminantGroup p c)
    obtain ⟨n, hn⟩ := exists_mk_eq_sum_nsmul hb hbu hy z
    refine ⟨fun i ↦ ((n i : ℤ) : ZMod (p ^ k i)),
      (L.primaryComponentEquivLocalDiscriminantGroup p).injective ?_⟩
    rw [piZModPowHom_intCast, map_sum, ← hz, hn]
    simp

/-- **Additive structure of `(A_L)_p` from a diagonal Jordan form.** For any prime `p` (including
`p = 2`) and any orthogonal basis `b` of `L_p` with `B(bᵢ, bᵢ) = uᵢ pᵏⁱ` (`uᵢ ∈ ℤ_pˣ`), the dual
classes of `p^{-kᵢ} bᵢ` give an additive isomorphism `∏ᵢ ℤ/pᵏⁱ ≃+ (A_L)_p`. -/
noncomputable def piZModPowEquivPrimaryComponent [Fintype ι]
    (hb : (L.localIntegralForm p).iIsOrtho b)
    (hbu : ∀ i, L.localIntegralForm p (b i) (b i) = u i * (p : ℤ_[p]) ^ k i) :
    (∀ i, ZMod (p ^ k i)) ≃+ primaryComponent L.DiscriminantGroup p :=
  AddEquiv.ofBijective
    (piZModPowHom (localizationDualToCompletion_diagonalDualVec hb hbu))
    (bijective_piZModPowHom hb hbu (localizationDualToCompletion_diagonalDualVec hb hbu))

/-- Evaluating `piZModPowEquivPrimaryComponent` on an integer tuple `(n i : ZMod (p ^ k i))`
gives the corresponding `ℤ`-linear combination of the dual classes `[diagonalDualVec hb hbu i]`. -/
theorem piZModPowEquivPrimaryComponent_intCast [Fintype ι]
    (hb : (L.localIntegralForm p).iIsOrtho b)
    (hbu : ∀ i, L.localIntegralForm p (b i) (b i) = u i * (p : ℤ_[p]) ^ k i) (n : ι → ℤ) :
    piZModPowEquivPrimaryComponent hb hbu (fun i ↦ (n i : ZMod (p ^ k i))) =
      ∑ i, n i • (L.primaryComponentEquivLocalDiscriminantGroup p).symm
        (Submodule.Quotient.mk (diagonalDualVec hb hbu i)) :=
  piZModPowHom_intCast (localizationDualToCompletion_diagonalDualVec hb hbu) n

/-- **Generator count (`AddGroup.rank`) of `(A_L)_p` from a diagonal Jordan form.** For any prime
`p` and any orthogonal basis `b` of `L_p` with `B(bᵢ, bᵢ) = uᵢ pᵏⁱ` (`uᵢ ∈ ℤ_pˣ`), the rank of
`(A_L)_p` equals `#{i | kᵢ ≠ 0}`. -/
theorem rank_primaryComponent_discriminantGroup_eq_card_filter [Fintype ι]
    (hb : (L.localIntegralForm p).iIsOrtho b)
    (hbu : ∀ i, L.localIntegralForm p (b i) (b i) = u i * (p : ℤ_[p]) ^ k i) :
    AddGroup.rank (primaryComponent L.DiscriminantGroup p) = #{i | k i ≠ 0} :=
  (AddGroup.rank_congr (L.piZModPowEquivPrimaryComponent hb hbu).symm).trans
    (AddCommGroup.rank_pi_zmod_pow k)

end TauCeti.IntegralLattice
