/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.Padics.RingHoms
public import TauCeti.GroupTheory.Rank
public import TauCeti.NumberTheory.IntegralLattice.Localization.Discriminant.Basic
import TauCeti.GroupTheory.FiniteAbelian.PrimePowerRank
import TauCeti.LinearAlgebra.BilinearForm.Diagonalization
import TauCeti.NumberTheory.Padics.PadicIntegers
import TauCeti.NumberTheory.Padics.RingHoms

/-!
# Additive structure of the `p`-primary discriminant group from a diagonal Jordan form

Given an orthogonal basis `b` of `L_p` with `B(bᵢ, bᵢ) = uᵢ pᵏⁱ` (`uᵢ ∈ ℤ_pˣ`), `[p^{-kᵢ} bᵢ]`
identifies `∏ᵢ ℤ/pᵏⁱ ≃+ (A_L)_p`, giving `AddGroup.rank (A_L)_p = #{i | kᵢ ≠ 0}` and `kᵢ ≠ 0`
when `finrank ℤ L = AddGroup.rank (A_L)_p`.

## Main results

* `TauCeti.IntegralLattice.piZModPowEquivPrimaryComponent`,
  `TauCeti.IntegralLattice.piZModPowEquivPrimaryComponent_intCast`,
  `TauCeti.IntegralLattice.piZModPowEquivPrimaryComponent_symm_mk`
* `TauCeti.IntegralLattice.rank_primaryComponent_discriminantGroup_eq_card_filter`
* `TauCeti.IntegralLattice.ne_zero_of_finrank_eq_rank`
-/

public section

open Module TensorProduct AddCommGroup Finset

namespace TauCeti.IntegralLattice

variable {V : Type*} [AddCommGroup V] [Module ℚ V] {L : IntegralLattice V} [L.IsNondegenerate]
  {p : ℕ} [Fact p.Prime] {ι : Type*} {b : Basis ι ℤ_[p] (L.LocalCarrier p)} {u : ι → ℤ_[p]ˣ}
  {k : ι → ℕ} {y : ι → L.LocalDualCarrier p}

omit [L.IsNondegenerate] in
/-- The local discriminant class of `p^{-kᵢ} bᵢ` is killed by `pᵏⁱ`. -/
private theorem pow_nsmul_mkQ_eq_zero
    (hy : ∀ i, L.localizationDualToCompletion p (y i) =
      ((p : ℚ_[p]) ^ k i)⁻¹ • L.localizationToCompletion p (b i)) (i : ι) :
    p ^ k i • (LinearMap.range (L.localCarrierToDual p)).mkQ (y i) = 0 := by
  rw [← map_nsmul, pow_nsmul_eq_localCarrierToDual hy, Submodule.mkQ_apply,
    Submodule.Quotient.mk_eq_zero]
  exact LinearMap.mem_range_self _ (b i)

/-- Every class in the local discriminant group decomposes in the basis classes `[p^{-kᵢ} bᵢ]`
with coefficients given by truncating `B(z, bᵢ) uᵢ⁻¹` modulo `pᵏⁱ`. -/
private theorem mkQ_eq_sum_appr_nsmul [Fintype ι] (hb : (L.localIntegralForm p).iIsOrtho b)
    (hbu : ∀ i, L.localIntegralForm p (b i) (b i) = u i * (p : ℤ_[p]) ^ k i)
    (hy : ∀ i, L.localizationDualToCompletion p (y i) =
      ((p : ℚ_[p]) ^ k i)⁻¹ • L.localizationToCompletion p (b i)) (z : L.LocalDualCarrier p) :
    (LinearMap.range (L.localCarrierToDual p)).mkQ z =
      ∑ i, (L.localDualPairingEquiv p z (b i) * ↑(u i)⁻¹).appr (k i) •
        (LinearMap.range (L.localCarrierToDual p)).mkQ (y i) := by
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
  have hc i : c i = ((c i).appr (k i) : ℤ_[p]) + t i * (p : ℤ_[p]) ^ k i := by
    rw [ht i, add_sub_cancel]
  have hp_smul i :
      ((p : ℤ_[p]) ^ k i) • (LinearMap.range (L.localCarrierToDual p)).mkQ (y i) = 0 := by
    rw [← Nat.cast_pow, Nat.cast_smul_eq_nsmul, pow_nsmul_mkQ_eq_zero hy i]
  have hterm i : (LinearMap.range (L.localCarrierToDual p)).mkQ (c i • y i) =
      (c i).appr (k i) • (LinearMap.range (L.localCarrierToDual p)).mkQ (y i) := by
    conv_lhs => rw [hc i, add_smul, mul_smul]
    simp only [map_add, map_smul, map_nsmul, hp_smul, smul_zero, add_zero, Nat.cast_smul_eq_nsmul]
  conv_lhs => rw [hz, map_sum]
  exact Finset.sum_congr rfl fun i _ ↦ hterm i

/-! ### The additive equivalence `∏ᵢ ℤ/pᵏⁱ ≃+ (A_L)_p` -/

/-- The `p`-primary class of the dual vector `p^{-kᵢ} bᵢ` is killed by `pᵏⁱ`. -/
theorem pow_nsmul_symm_mk_eq_zero
    (hy : ∀ i, L.localizationDualToCompletion p (y i) =
      ((p : ℚ_[p]) ^ k i)⁻¹ • L.localizationToCompletion p (b i)) (i : ι) :
    p ^ k i • (L.primaryComponentEquivLocalDiscriminantGroup p).symm
      (Submodule.Quotient.mk (y i)) = 0 := by
  rw [← map_nsmul, ← Submodule.mkQ_apply, pow_nsmul_mkQ_eq_zero hy i, map_zero]

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

/-- Evaluating `piZModPowHom` at the residues `toZModPow (k i) (B(z, bᵢ) uᵢ⁻¹)` recovers the
`p`-primary discriminant class of `z`. -/
private theorem piZModPowHom_toZModPow [Fintype ι]
    (hb : (L.localIntegralForm p).iIsOrtho b)
    (hbu : ∀ i, L.localIntegralForm p (b i) (b i) = u i * (p : ℤ_[p]) ^ k i)
    (hy : ∀ i, L.localizationDualToCompletion p (y i) =
      ((p : ℚ_[p]) ^ k i)⁻¹ • L.localizationToCompletion p (b i)) (z : L.LocalDualCarrier p) :
    piZModPowHom hy
        (fun i ↦ PadicInt.toZModPow (k i)
          (L.localDualPairingEquiv p z (b i) * (↑(u i)⁻¹ : ℤ_[p]))) =
      (L.primaryComponentEquivLocalDiscriminantGroup p).symm (Submodule.Quotient.mk z) := by
  apply (L.primaryComponentEquivLocalDiscriminantGroup p).injective
  have hcast :
      (fun i ↦ PadicInt.toZModPow (k i)
          (L.localDualPairingEquiv p z (b i) * (↑(u i)⁻¹ : ℤ_[p]))) =
        fun i ↦ (((L.localDualPairingEquiv p z (b i) * (↑(u i)⁻¹ : ℤ_[p])).appr (k i) : ℤ) :
          ZMod (p ^ k i)) :=
    funext fun i ↦ by rw [Int.cast_natCast, ← PadicInt.toZModPow_eq_natCast_appr]
  rw [hcast, piZModPowHom_intCast,
    (L.primaryComponentEquivLocalDiscriminantGroup p).apply_symm_apply]
  simp only [map_sum, natCast_zsmul, map_nsmul,
    (L.primaryComponentEquivLocalDiscriminantGroup p).apply_symm_apply, ← Submodule.mkQ_apply]
  exact (mkQ_eq_sum_appr_nsmul hb hbu hy z).symm

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
    have hmk : (LinearMap.range (L.localCarrierToDual p)).mkQ (∑ i, (c i).val • y i) = 0 := by
      have hmap := congrArg (L.primaryComponentEquivLocalDiscriminantGroup p) hc
      simpa only [map_zero, map_sum, natCast_zsmul, map_nsmul,
        (L.primaryComponentEquivLocalDiscriminantGroup p).apply_symm_apply,
        Submodule.mkQ_apply] using hmap
    obtain ⟨x, hx⟩ := (Submodule.Quotient.mk_eq_zero (LinearMap.range (L.localCarrierToDual p))).mp
      (by simpa only [Submodule.mkQ_apply] using hmk)
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
    refine ⟨fun i ↦ PadicInt.toZModPow (k i)
      (L.localDualPairingEquiv p z (b i) * (↑(u i)⁻¹ : ℤ_[p])), ?_⟩
    rw [piZModPowHom_toZModPow hb hbu hy, hz,
      (L.primaryComponentEquivLocalDiscriminantGroup p).symm_apply_apply]

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

/-- The inverse of `piZModPowEquivPrimaryComponent` recovers the `i`-th coordinate of the
`p`-primary class of a dual vector `z` by reducing `L.localDualPairingEquiv p z (b i) * ↑(u i)⁻¹`
modulo `p ^ k i`. -/
@[simp]
theorem piZModPowEquivPrimaryComponent_symm_mk [Fintype ι]
    (hb : (L.localIntegralForm p).iIsOrtho b)
    (hbu : ∀ i, L.localIntegralForm p (b i) (b i) = u i * (p : ℤ_[p]) ^ k i)
    (z : L.LocalDualCarrier p) (i : ι) :
    (L.piZModPowEquivPrimaryComponent hb hbu).symm
        ((L.primaryComponentEquivLocalDiscriminantGroup p).symm (Submodule.Quotient.mk z)) i =
      PadicInt.toZModPow (k i) (L.localDualPairingEquiv p z (b i) * (↑(u i)⁻¹ : ℤ_[p])) := by
  exact congrFun ((L.piZModPowEquivPrimaryComponent hb hbu).symm_apply_eq.mpr
    (piZModPowHom_toZModPow hb hbu (localizationDualToCompletion_diagonalDualVec hb hbu) z).symm) i

/-- **Generator count (`AddGroup.rank`) of `(A_L)_p` from a diagonal Jordan form.** For any prime
`p` and any orthogonal basis `b` of `L_p` with `B(bᵢ, bᵢ) = uᵢ pᵏⁱ` (`uᵢ ∈ ℤ_pˣ`), the rank of
`(A_L)_p` equals `#{i | kᵢ ≠ 0}`. -/
theorem rank_primaryComponent_discriminantGroup_eq_card_filter [Fintype ι]
    (hb : (L.localIntegralForm p).iIsOrtho b)
    (hbu : ∀ i, L.localIntegralForm p (b i) (b i) = u i * (p : ℤ_[p]) ^ k i) :
    AddGroup.rank (primaryComponent L.DiscriminantGroup p) = #{i | k i ≠ 0} :=
  (AddGroup.rank_congr (L.piZModPowEquivPrimaryComponent hb hbu).symm).trans
    (AddCommGroup.rank_pi_zmod_pow k)

/-- If a nondegenerate lattice achieves the minimal rank `finrank ℤ L = AddGroup.rank (A_L)_p`,
then every diagonal Jordan exponent `kᵢ` is nonzero. -/
theorem ne_zero_of_finrank_eq_rank
    (L : IntegralLattice V) [L.IsNondegenerate] {p : ℕ} [Fact p.Prime]
    {b : Basis (Fin (finrank ℤ L)) ℤ_[p] (L.LocalCarrier p)} {u : Fin (finrank ℤ L) → ℤ_[p]ˣ}
    {k : Fin (finrank ℤ L) → ℕ}
    (hb : (L.localIntegralForm p).iIsOrtho b)
    (hbu : ∀ i, L.localIntegralForm p (b i) (b i) = u i * (p : ℤ_[p]) ^ k i)
    (hLrank : finrank ℤ L = AddGroup.rank (primaryComponent L.DiscriminantGroup p))
    (i : Fin (finrank ℤ L)) : k i ≠ 0 := by
  classical
  have hk_all : ({j : Fin (finrank ℤ L) | k j ≠ 0} : Finset (Fin (finrank ℤ L))) = Finset.univ :=
    Finset.eq_of_subset_of_card_le (Finset.subset_univ _)
      (by simp [← L.rank_primaryComponent_discriminantGroup_eq_card_filter hb hbu, ← hLrank])
  exact (Finset.mem_filter.mp (Finset.eq_univ_iff_forall.mp hk_all i)).2

end TauCeti.IntegralLattice
