/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Logic.Equiv.Fin.Rotate
public import TauCeti.Analysis.Matrix.UnitaryGroup.Weyl
public import TauCeti.Topology.Algebra.Matrix.SurfaceRelationModuli.Basic
import TauCeti.LinearAlgebra.Matrix.Diagonal

/-!
# Genus-one twisted `SU(r)` surface commutator relation moduli

This file classifies the genus-one (`g = 1`) twisted `SU(r)` commutator relation moduli
`TauCeti.SpecialUnitary.relationModuli r ζ 1` in the coprime case `IsPrimitiveRoot ζ r`, proving
existence via a rescaled clock-and-shift pair in `SU(r)` and uniqueness up to `SU(r)`-conjugation,
and records genus-one consequences and non-coprime counterexamples.

## Main results

* `TauCeti.SpecialUnitary.relationModuli_genus_one`: when `IsPrimitiveRoot ζ r`, the genus-one
  moduli `relationModuli r ζ 1` is nonempty and a subsingleton.
* `TauCeti.SpecialUnitary.contractibleSpace_relationModuli_one` and
  `TauCeti.SpecialUnitary.simplyConnectedSpace_relationModuli_one`: when `IsPrimitiveRoot ζ r`,
  `relationModuli r ζ 1` is contractible and simply connected.
* `TauCeti.SpecialUnitary.exists_ne_one_smul_eq_self_relationModuli_one`: for `2 ≤ r` and
  `IsPrimitiveRoot ζ r`, a nontrivial central holonomy twist acts trivially on
  `relationModuli r ζ 1`, witnessing non-freeness of the central-twist action on the coarse
  quotient.
* `TauCeti.SpecialUnitary.nontrivial_relationModuli_two_one_one` and
  `TauCeti.SpecialUnitary.exists_notMem_center_commute_relationSet_two_one_one`: at the non-coprime
  parameters `r = 2`, `ζ = 1`, `g = 1`, neither uniqueness up to conjugation nor centrality of
  stabilizers holds.

## References

* M. F. Atiyah, R. Bott, *The Yang-Mills equations over Riemann surfaces*, Philos. Trans. Roy. Soc.
  London Ser. A **308** (1983), 523-615, §9.
* K. Wehrheim, C. T. Woodward, *Floer field theory for coprime rank and degree*, Geom. Topol.
  **20** (2016), 3135-3188, §3.3.
-/

public section

open Matrix Topology
open scoped commutatorElement

namespace TauCeti.SpecialUnitary

/-! ### Genus-one existence, uniqueness, and simple connectivity -/

/-- For `ζ ^ r = 1` and `1 ≤ r`, advancing the index in `Fin r` by `finRotate r` multiplies
`ζ ^ (i : ℕ)` by `ζ`. -/
private theorem pow_finRotate_eq {r : ℕ} (hr : 1 ≤ r) {ζ : ℂ} (hζ : ζ ^ r = 1) (i : Fin r) :
    ζ ^ (finRotate r i : ℕ) = ζ * ζ ^ (i : ℕ) := by
  have : NeZero r := ⟨by omega⟩
  rw [finRotate_apply, Fin.val_add, Fin.val_one']
  have hmod : ∀ m : ℕ, ζ ^ (m % r) = ζ ^ m := fun m => by
    conv_rhs => rw [← Nat.div_add_mod m r]
    rw [pow_add, pow_mul, hζ, one_pow, one_mul]
  rw [hmod, pow_add, hmod, pow_one, mul_comm]

/-- Rescaling two unitary matrices `U, V ∈ U(r)` by circle elements `c₁, c₂` into `SU(r)` preserves
their matrix commutator. -/
private theorem commutator_circle_smul_eq {r : ℕ} {U V : unitaryGroup (Fin r) ℂ}
    {c₁ c₂ : Circle} {A B : Matrix.specialUnitaryGroup (Fin r) ℂ}
    (hA : (A : Matrix (Fin r) (Fin r) ℂ) = (c₁ : ℂ) • (U : Matrix (Fin r) (Fin r) ℂ))
    (hB : (B : Matrix (Fin r) (Fin r) ℂ) = (c₂ : ℂ) • (V : Matrix (Fin r) (Fin r) ℂ)) :
    (↑⁅A, B⁆ : Matrix (Fin r) (Fin r) ℂ) =
      (U : Matrix (Fin r) (Fin r) ℂ) * V * star (U : Matrix (Fin r) (Fin r) ℂ) *
        star (V : Matrix (Fin r) (Fin r) ℂ) := by
  let α₁ : ℂ := c₁
  let α₂ : ℂ := c₂
  have hA' : (A : Matrix (Fin r) (Fin r) ℂ) = α₁ • (U : Matrix (Fin r) (Fin r) ℂ) := hA
  have hB' : (B : Matrix (Fin r) (Fin r) ℂ) = α₂ • (V : Matrix (Fin r) (Fin r) ℂ) := hB
  have hc₁_inv : α₁ * star α₁ = 1 := Unitary.mem_iff_self_mul_star.mp c₁.coe_mem_unitary
  have hc₂_inv : α₂ * star α₂ = 1 := Unitary.mem_iff_self_mul_star.mp c₂.coe_mem_unitary
  have h1 : (α₁ • (U : Matrix (Fin r) (Fin r) ℂ)) * (α₂ • (V : Matrix (Fin r) (Fin r) ℂ)) =
      (α₁ * α₂) • ((U : Matrix (Fin r) (Fin r) ℂ) * V) := by
    rw [smul_mul_assoc, mul_smul_comm, smul_smul]
  have h2 : (star α₁ • star (U : Matrix (Fin r) (Fin r) ℂ)) *
      (star α₂ • star (V : Matrix (Fin r) (Fin r) ℂ)) =
      (star α₁ * star α₂) •
        (star (U : Matrix (Fin r) (Fin r) ℂ) * star (V : Matrix (Fin r) (Fin r) ℂ)) := by
    rw [smul_mul_assoc, mul_smul_comm, smul_smul]
  have hcs : (α₁ * α₂) * (star α₁ * star α₂) = 1 := by
    calc (α₁ * α₂) * (star α₁ * star α₂) = (α₁ * star α₁) * (α₂ * star α₂) := by ring
      _ = 1 := by rw [hc₁_inv, hc₂_inv, mul_one]
  rw [commutatorElement_def, Submonoid.coe_mul, Submonoid.coe_mul, Submonoid.coe_mul,
    ← star_eq_inv, Matrix.specialUnitaryGroup.coe_star,
    ← star_eq_inv, Matrix.specialUnitaryGroup.coe_star, hA', hB', star_smul, star_smul,
    Matrix.mul_assoc (_ * _), h1, h2, smul_mul_assoc, mul_smul_comm, smul_smul, hcs, one_smul,
    ← Matrix.mul_assoc]

/-- Clock-and-shift construction of a standard pair `(A, B)` in `SU(r)` with `⁅A, B⁆ = ζ • 1` when
`1 ≤ r` and `ζ` is a primitive `r`-th root of unity. -/
private theorem exists_clock_shift_pair {r : ℕ} (hr : 1 ≤ r) {ζ : ℂ} (hζ : IsPrimitiveRoot ζ r) :
    ∃ (A B : Matrix.specialUnitaryGroup (Fin r) ℂ) (c₁ c₂ : Circle),
      (A : Matrix (Fin r) (Fin r) ℂ) = diagonal (fun k : Fin r => ζ ^ (k : ℕ) * (c₁ : ℂ)) ∧
      (B : Matrix (Fin r) (Fin r) ℂ) =
        (c₂ : ℂ) • ((permutationUnitary (finRotate r) : unitaryGroup (Fin r) ℂ) :
          Matrix (Fin r) (Fin r) ℂ) ∧
      (↑⁅A, B⁆ : Matrix (Fin r) (Fin r) ℂ) = ζ • 1 := by
  have hnorm : ‖ζ‖ = 1 := Complex.norm_eq_one_of_pow_eq_one hζ.pow_eq_one (by omega)
  let z : Fin r → Circle := fun k =>
    ⟨ζ ^ (k : ℕ), mem_sphere_zero_iff_norm.mpr (by rw [norm_pow, hnorm, one_pow])⟩
  let z' : Fin r → Circle := fun i => z (finRotate r i)
  let DU : unitaryGroup (Fin r) ℂ := unitaryTorusHom (Fin r) z
  let QU : unitaryGroup (Fin r) ℂ := permutationUnitary (finRotate r)
  have hrelU : QU * unitaryTorusHom (Fin r) z' = DU * QU := by
    apply mul_right_cancel (b := QU⁻¹)
    rw [mul_inv_cancel_right]
    have h := unitaryTorusNormalizer_mul_unitaryTorusHom_mul_inv
      ⟨permutationUnitary (finRotate r), permutationUnitary_mem_normalizer (finRotate r)⟩ z'
    rw [unitaryTorusNormalizerPerm_permutationUnitary] at h
    exact h.trans (congrArg (unitaryTorusHom (Fin r))
      (funext fun i => congrArg z ((finRotate r).apply_symm_apply i)))
  have hrel_mat : (DU : Matrix (Fin r) (Fin r) ℂ) * QU =
      ζ • ((QU : Matrix (Fin r) (Fin r) ℂ) * DU) := by
    have h1 := congrArg Subtype.val hrelU
    rw [Submonoid.coe_mul, Submonoid.coe_mul] at h1
    have h2 : (unitaryTorusHom (Fin r) z' : Matrix (Fin r) (Fin r) ℂ) =
        ζ • (DU : Matrix (Fin r) (Fin r) ℂ) := by
      dsimp only [DU, z']
      rw [coe_unitaryTorusHom, coe_unitaryTorusHom, ← diagonal_smul]
      exact congrArg diagonal (funext fun i => pow_finRotate_eq hr hζ.pow_eq_one i)
    rw [← h1, h2, mul_smul_comm]
  obtain ⟨c₁, hc₁⟩ := exists_circle_smul_mem_specialUnitaryGroup DU
  obtain ⟨c₂, hc₂⟩ := exists_circle_smul_mem_specialUnitaryGroup QU
  let A : Matrix.specialUnitaryGroup (Fin r) ℂ := ⟨(c₁ : ℂ) • (DU : Matrix (Fin r) (Fin r) ℂ), hc₁⟩
  let B : Matrix.specialUnitaryGroup (Fin r) ℂ := ⟨(c₂ : ℂ) • (QU : Matrix (Fin r) (Fin r) ℂ), hc₂⟩
  refine ⟨A, B, c₁, c₂, ?_, rfl, ?_⟩
  · change ((c₁ : ℂ) • (DU : Matrix (Fin r) (Fin r) ℂ)) = _
    rw [coe_unitaryTorusHom, ← diagonal_smul]
    exact congrArg diagonal (funext fun _ => mul_comm _ _)
  · calc (↑⁅A, B⁆ : Matrix (Fin r) (Fin r) ℂ)
        = (ζ • ((QU : Matrix (Fin r) (Fin r) ℂ) * DU)) * star (DU : Matrix (Fin r) (Fin r) ℂ) *
            star (QU : Matrix (Fin r) (Fin r) ℂ) := by
          rw [commutator_circle_smul_eq (U := DU) (V := QU) (c₁ := c₁) (c₂ := c₂)
            (A := A) (B := B) rfl rfl, hrel_mat]
      _ = ζ • ((QU : Matrix (Fin r) (Fin r) ℂ) *
            ((DU : Matrix (Fin r) (Fin r) ℂ) * star (DU : Matrix (Fin r) (Fin r) ℂ)) *
            star (QU : Matrix (Fin r) (Fin r) ℂ)) := by
          rw [smul_mul_assoc, smul_mul_assoc,
            Matrix.mul_assoc (QU : Matrix (Fin r) (Fin r) ℂ) (DU : Matrix (Fin r) (Fin r) ℂ)
              (star (DU : Matrix (Fin r) (Fin r) ℂ))]
      _ = ζ • 1 := by
          rw [(Unitary.mem_iff.mp DU.2).2, Matrix.mul_one, (Unitary.mem_iff.mp QU.2).2]

/-- If `diagonal z * B₁ = ζ • (B₁ * diagonal z)` with `B₁ ∈ SU(r)`, `1 ≤ r`, and
`IsPrimitiveRoot ζ r`, the diagonal entries `z` are a permutation of `ζ ^ k * μ` (`μ ≠ 0`). -/
private theorem exists_perm_pow_eq_of_mul_eq_smul_mul {r : ℕ} (hr : 1 ≤ r) {ζ : ℂ}
    (hζ : IsPrimitiveRoot ζ r) (z : Fin r → Circle) (B₁ : Matrix.specialUnitaryGroup (Fin r) ℂ)
    (hrel : diagonal (fun i => (z i : ℂ)) * (B₁ : Matrix (Fin r) (Fin r) ℂ) =
      ζ • ((B₁ : Matrix (Fin r) (Fin r) ℂ) * diagonal (fun i => (z i : ℂ)))) :
    ∃ (σ : Equiv.Perm (Fin r)) (μ : ℂ), μ ≠ 0 ∧ ∀ k : Fin r, (z (σ k) : ℂ) = ζ ^ (k : ℕ) * μ := by
  have hstep : ∀ j : Fin r, ∃ i : Fin r, (z i : ℂ) = ζ * (z j : ℂ) := fun j => by
    have hcol : ∃ i : Fin r, (B₁ : Matrix (Fin r) (Fin r) ℂ) i j ≠ 0 := by
      by_contra! hall
      have hB₁U : (B₁ : Matrix (Fin r) (Fin r) ℂ) ∈ unitary (Matrix (Fin r) (Fin r) ℂ) :=
        (mem_specialUnitaryGroup_iff.mp B₁.2).1
      have hunit := congrArg (fun M : Matrix (Fin r) (Fin r) ℂ => M j j)
        (Unitary.mem_iff.mp hB₁U).1
      simp [Matrix.mul_apply, hall] at hunit
    obtain ⟨i, hij⟩ := hcol
    have hent := congrArg (fun M : Matrix (Fin r) (Fin r) ℂ => M i j) hrel
    rw [diagonal_mul, Matrix.smul_apply, mul_diagonal, smul_eq_mul] at hent
    refine ⟨i, sub_eq_zero.mp ((mul_eq_zero.mp ?_).resolve_right hij)⟩
    linear_combination hent
  let i₀ : Fin r := ⟨0, hr⟩
  let μ : ℂ := (z i₀ : ℂ)
  have hμ : μ ≠ 0 := Circle.coe_ne_zero (z i₀)
  have hpow : ∀ m : ℕ, ∃ i : Fin r, (z i : ℂ) = ζ ^ m * μ := fun m => by
    induction m with
    | zero => exact ⟨i₀, by simp [μ]⟩
    | succ m ih =>
      obtain ⟨j, hj⟩ := ih
      obtain ⟨i, hi⟩ := hstep j
      exact ⟨i, by rw [hi, hj, pow_succ', mul_assoc]⟩
  choose g hg using fun k : Fin r => hpow (k : ℕ)
  have hg_inj : Function.Injective g := fun k₁ k₂ hk => by
    have hgk : ζ ^ (k₁ : ℕ) * μ = ζ ^ (k₂ : ℕ) * μ := by rw [← hg k₁, hk, hg k₂]
    exact Fin.ext (hζ.injOn_pow_mul hμ
      (Finset.mem_coe.mpr (Finset.mem_range.mpr k₁.isLt))
      (Finset.mem_coe.mpr (Finset.mem_range.mpr k₂.isLt)) hgk)
  exact ⟨Equiv.ofBijective g (Finite.injective_iff_bijective.mp hg_inj), μ, hμ, hg⟩

/-- Any pair `(A, B)` in `SU(r)` with `⁅A, B⁆ = ζ • 1` (`1 ≤ r`, `IsPrimitiveRoot ζ r`) can be
conjugated in `SU(r)` so that `A = diagonal (fun k => ζ ^ (k : ℕ) * μ)` for some `μ ≠ 0`. -/
private theorem exists_conj_first_eq_clock {r : ℕ} (hr : 1 ≤ r) {ζ : ℂ} (hζ : IsPrimitiveRoot ζ r)
    (A B : Matrix.specialUnitaryGroup (Fin r) ℂ)
    (hAB : (↑⁅A, B⁆ : Matrix (Fin r) (Fin r) ℂ) = ζ • 1) :
    ∃ (u : Matrix.specialUnitaryGroup (Fin r) ℂ) (μ : ℂ), μ ≠ 0 ∧
      ((u * A * u⁻¹ : Matrix.specialUnitaryGroup (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ) =
        diagonal (fun k : Fin r => ζ ^ (k : ℕ) * μ) := by
  obtain ⟨u₁, z, hu₁⟩ := Matrix.specialUnitaryGroup.exists_conj_eq_diagonal A
  let A₁ := u₁ * A * u₁⁻¹
  let B₁ := u₁ * B * u₁⁻¹
  have hrel₁ : diagonal (fun i => (z i : ℂ)) * (B₁ : Matrix (Fin r) (Fin r) ℂ) =
      ζ • ((B₁ : Matrix (Fin r) (Fin r) ℂ) * diagonal (fun i => (z i : ℂ))) := by
    have hc : (↑⁅A₁, B₁⁆ : Matrix (Fin r) (Fin r) ℂ) = ζ • 1 := by
      have h := conjAct_smul_mem_relationSet (ConjAct.toConjAct u₁)
        (x := fun _ : Fin 1 => (A, B)) (mem_relationSet_one_iff.mpr hAB)
      simpa only [mem_relationSet_one_iff, Pi.smul_apply, Prod.smul_mk, ConjAct.smul_def,
        ConjAct.ofConjAct_toConjAct] using h
    rw [← hu₁]
    calc (A₁ : Matrix (Fin r) (Fin r) ℂ) * B₁
        = (↑⁅A₁, B₁⁆ : Matrix (Fin r) (Fin r) ℂ) * B₁ * A₁ := by
          simp only [commutatorElement_def, ← Submonoid.coe_mul, inv_mul_cancel_right]
      _ = ζ • ((B₁ : Matrix (Fin r) (Fin r) ℂ) * A₁) := by
          rw [hc, Matrix.smul_mul, Matrix.one_mul, smul_mul_assoc]
  obtain ⟨σ, μ, hμ, hσ⟩ := exists_perm_pow_eq_of_mul_eq_smul_mul hr hζ z B₁ hrel₁
  let PU : unitaryGroup (Fin r) ℂ := permutationUnitary σ⁻¹
  obtain ⟨c, hc⟩ := exists_circle_smul_mem_specialUnitaryGroup PU
  let u₂ : Matrix.specialUnitaryGroup (Fin r) ℂ := ⟨(c : ℂ) • (PU : Matrix (Fin r) (Fin r) ℂ), hc⟩
  refine ⟨u₂ * u₁, μ, hμ, ?_⟩
  have hconjU : (PU * unitaryTorusHom (Fin r) z * PU⁻¹ : unitaryGroup (Fin r) ℂ) =
      unitaryTorusHom (Fin r) (fun k => z (σ k)) := by
    have h := unitaryTorusNormalizer_mul_unitaryTorusHom_mul_inv
      ⟨permutationUnitary σ⁻¹, permutationUnitary_mem_normalizer σ⁻¹⟩ z
    rw [unitaryTorusNormalizerPerm_permutationUnitary] at h
    exact h.trans (congrArg (unitaryTorusHom (Fin r))
      (funext fun i => by rw [Equiv.Perm.inv_def, Equiv.symm_symm]))
  have hcmul : (c : ℂ) * star (c : ℂ) = 1 := Unitary.mem_iff_self_mul_star.mp c.coe_mem_unitary
  calc (((u₂ * u₁) * A * (u₂ * u₁)⁻¹ : Matrix.specialUnitaryGroup (Fin r) ℂ) :
        Matrix (Fin r) (Fin r) ℂ)
      = (u₂ : Matrix (Fin r) (Fin r) ℂ) * A₁ * star (u₂ : Matrix (Fin r) (Fin r) ℂ) := by
        simp only [A₁, _root_.mul_inv_rev, Submonoid.coe_mul, ← star_eq_inv,
          Matrix.specialUnitaryGroup.coe_star, Matrix.mul_assoc]
    _ = (PU : Matrix (Fin r) (Fin r) ℂ) * diagonal (fun i => (z i : ℂ)) *
          star (PU : Matrix (Fin r) (Fin r) ℂ) := by
        rw [hu₁]
        dsimp only [u₂]
        rw [star_smul, smul_mul_assoc, smul_mul_assoc, mul_smul_comm, smul_smul, hcmul, one_smul]
    _ = diagonal (fun k : Fin r => ζ ^ (k : ℕ) * μ) := by
        rw [← coe_unitaryTorusHom, ← Unitary.coe_star, Unitary.star_eq_inv, ← Submonoid.coe_mul,
          ← Submonoid.coe_mul, hconjU, coe_unitaryTorusHom]
        exact congrArg diagonal (funext hσ)

/-- Telescoping prefix product on `Fin r` solving `δ k * (δ ((finRotate r).symm k))⁻¹ = η k` on
the circle whenever `∏ j, η j = 1`. -/
private theorem prefixProd_mul_finRotate_symm_inv {r : ℕ} (hr : 1 ≤ r) {η : Fin r → Circle}
    (hη : ∏ j : Fin r, η j = 1) :
    ∃ δ : Fin r → Circle, ∀ k : Fin r, δ k * (δ ((finRotate r).symm k))⁻¹ = η k := by
  have : NeZero r := ⟨by omega⟩
  let δ : Fin r → Circle := fun k => ∏ j ∈ Finset.Iic k, η j
  refine ⟨δ, fun k => ?_⟩
  rcases Nat.eq_zero_or_pos (k : ℕ) with hk0 | hkpos
  · have hk_zero : k = ⟨0, hr⟩ := Fin.ext hk0
    subst hk_zero
    have hsymm : (finRotate r).symm ⟨0, hr⟩ = ⟨r - 1, by omega⟩ := by
      apply (finRotate r).injective
      rw [Equiv.apply_symm_apply, finRotate_apply, Fin.ext_iff, Fin.val_add, Fin.val_one']
      simp [Nat.sub_add_cancel hr]
    have hIic0 : Finset.Iic (⟨0, hr⟩ : Fin r) = {⟨0, hr⟩} := by
      ext j
      simp only [Finset.mem_Iic, Finset.mem_singleton, Fin.le_def, Fin.ext_iff]
      omega
    have hIic_last : Finset.Iic (⟨r - 1, by omega⟩ : Fin r) = Finset.univ := by
      ext j
      simp only [Finset.mem_Iic, Finset.mem_univ, iff_true, Fin.le_def]
      omega
    dsimp only [δ]
    rw [hsymm, hIic0, hIic_last, Finset.prod_singleton, hη, inv_one, mul_one]
  · let k' : Fin r := ⟨(k : ℕ) - 1, by omega⟩
    have hrot : finRotate r k' = k := by
      rw [finRotate_apply, Fin.ext_iff, Fin.val_add, Fin.val_one']
      have hr2 : 1 < r := by omega
      have h1 : 1 % r = 1 := Nat.mod_eq_of_lt hr2
      have hk1 : ((k : ℕ) - 1) + 1 = (k : ℕ) := Nat.sub_add_cancel hkpos
      dsimp only [k']
      rw [h1, hk1, Nat.mod_eq_of_lt k.isLt]
    have hsymm : (finRotate r).symm k = k' := (finRotate r).symm_apply_eq.mpr hrot.symm
    have hIic : Finset.Iic k = insert k (Finset.Iic k') := by
      ext j
      simp only [Finset.mem_Iic, Finset.mem_insert, Fin.le_def, Fin.ext_iff, k']
      omega
    have hnotMem : k ∉ Finset.Iic k' := by
      simp only [Finset.mem_Iic, Fin.le_def, k']
      omega
    dsimp only [δ]
    rw [hsymm, hIic, Finset.prod_insert hnotMem, mul_inv_cancel_right]

/-- If both `B₀` and `B` satisfy `⁅A₀, -⁆ = ζ • 1` in `SU(r)`, then `A₀` commutes with `B * B₀⁻¹`
at the matrix level. -/
private theorem commute_mul_inv_of_commutator_eq_smul_one {r : ℕ} {ζ : ℂ}
    {A₀ B₀ B : Matrix.specialUnitaryGroup (Fin r) ℂ}
    (hrel₀ : (↑⁅A₀, B₀⁆ : Matrix (Fin r) (Fin r) ℂ) = ζ • 1)
    (hrel : (↑⁅A₀, B⁆ : Matrix (Fin r) (Fin r) ℂ) = ζ • 1) :
    Commute (A₀ : Matrix (Fin r) (Fin r) ℂ)
      ((B * B₀⁻¹ : Matrix.specialUnitaryGroup (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ) := by
  have hmul : ∀ {X : Matrix.specialUnitaryGroup (Fin r) ℂ},
      (↑⁅A₀, X⁆ : Matrix (Fin r) (Fin r) ℂ) = ζ • 1 →
      (A₀ : Matrix (Fin r) (Fin r) ℂ) * (X : Matrix (Fin r) (Fin r) ℂ) =
        ζ • ((X : Matrix (Fin r) (Fin r) ℂ) * (A₀ : Matrix (Fin r) (Fin r) ℂ)) := by
    intro X hX
    calc (A₀ : Matrix (Fin r) (Fin r) ℂ) * (X : Matrix (Fin r) (Fin r) ℂ)
        = (↑⁅A₀, X⁆ : Matrix (Fin r) (Fin r) ℂ) * (X : Matrix (Fin r) (Fin r) ℂ) *
            (A₀ : Matrix (Fin r) (Fin r) ℂ) := by
          simp only [commutatorElement_def, ← Submonoid.coe_mul, inv_mul_cancel_right]
      _ = ζ • ((X : Matrix (Fin r) (Fin r) ℂ) * (A₀ : Matrix (Fin r) (Fin r) ℂ)) := by
          rw [hX, Matrix.smul_mul, Matrix.one_mul, smul_mul_assoc]
  let MB₀inv : Matrix (Fin r) (Fin r) ℂ := (B₀⁻¹ : Matrix.specialUnitaryGroup (Fin r) ℂ)
  have hB₀1 : (B₀ : Matrix (Fin r) (Fin r) ℂ) * MB₀inv = 1 := by
    rw [← Submonoid.coe_mul, mul_inv_cancel, OneMemClass.coe_one]
  have hB₀2 : MB₀inv * (B₀ : Matrix (Fin r) (Fin r) ℂ) = 1 := by
    rw [← Submonoid.coe_mul, inv_mul_cancel, OneMemClass.coe_one]
  have hinv : (ζ • (A₀ : Matrix (Fin r) (Fin r) ℂ)) * MB₀inv =
      MB₀inv * (A₀ : Matrix (Fin r) (Fin r) ℂ) := by
    calc (ζ • (A₀ : Matrix (Fin r) (Fin r) ℂ)) * MB₀inv
        = MB₀inv * (ζ • ((B₀ : Matrix (Fin r) (Fin r) ℂ) *
            (A₀ : Matrix (Fin r) (Fin r) ℂ))) * MB₀inv := by
          rw [Matrix.mul_smul, ← Matrix.mul_assoc MB₀inv, hB₀2, Matrix.one_mul]
      _ = MB₀inv * (A₀ : Matrix (Fin r) (Fin r) ℂ) := by
          rw [← hmul hrel₀, Matrix.mul_assoc, Matrix.mul_assoc, hB₀1, Matrix.mul_one]
  calc (A₀ : Matrix (Fin r) (Fin r) ℂ) * ((B * B₀⁻¹ : Matrix.specialUnitaryGroup (Fin r) ℂ))
      = ((A₀ : Matrix (Fin r) (Fin r) ℂ) * B) * MB₀inv := by
        rw [Submonoid.coe_mul, ← Matrix.mul_assoc]
    _ = B * ((ζ • (A₀ : Matrix (Fin r) (Fin r) ℂ)) * MB₀inv) := by
        rw [hmul hrel, ← Matrix.mul_smul, Matrix.mul_assoc]
    _ = ((B * B₀⁻¹ : Matrix.specialUnitaryGroup (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ) * A₀ := by
        rw [hinv, ← Matrix.mul_assoc, ← Submonoid.coe_mul]

/-- If `A₀` has distinct diagonal entries `ζ ^ k * c₁` and both `B₀` and `B` satisfy
`⁅A₀, -⁆ = ζ • 1`, then `(B * B₀⁻¹)⁻¹` is diagonal of determinant `1`. -/
private theorem exists_torus_of_commutator_eq {r : ℕ} {ζ : ℂ} (hζ : IsPrimitiveRoot ζ r)
    {A₀ B₀ B : Matrix.specialUnitaryGroup (Fin r) ℂ} {c₁ : Circle}
    (hA₀ : (A₀ : Matrix (Fin r) (Fin r) ℂ) = diagonal (fun k : Fin r => ζ ^ (k : ℕ) * (c₁ : ℂ)))
    (hrel₀ : (↑⁅A₀, B₀⁆ : Matrix (Fin r) (Fin r) ℂ) = ζ • 1)
    (hrel : (↑⁅A₀, B⁆ : Matrix (Fin r) (Fin r) ℂ) = ζ • 1) :
    ∃ η : Fin r → Circle, (∏ j : Fin r, η j = 1) ∧
      (((B * B₀⁻¹)⁻¹ : Matrix.specialUnitaryGroup (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ) =
        diagonal (fun j => (η j : ℂ)) := by
  let C : Matrix.specialUnitaryGroup (Fin r) ℂ := B * B₀⁻¹
  have hcommC : Commute (diagonal (fun k : Fin r => ζ ^ (k : ℕ) * (c₁ : ℂ)))
      (C : Matrix (Fin r) (Fin r) ℂ) := by
    rw [← hA₀]
    exact commute_mul_inv_of_commutator_eq_smul_one hrel₀ hrel
  have hinj : Function.Injective (fun k : Fin r => ζ ^ (k : ℕ) * (c₁ : ℂ)) := fun k₁ k₂ hk =>
    Fin.ext (hζ.injOn_pow_mul (Circle.coe_ne_zero c₁)
      (Finset.mem_coe.mpr (Finset.mem_range.mpr k₁.isLt))
      (Finset.mem_coe.mpr (Finset.mem_range.mpr k₂.isLt)) hk)
  have hCdiag : (⟨(C⁻¹ : Matrix.specialUnitaryGroup (Fin r) ℂ),
      specialUnitaryGroup_le_unitaryGroup (C⁻¹).2⟩ : unitaryGroup (Fin r) ℂ) ∈
      unitaryTorus (Fin r) := by
    rw [mem_unitaryTorus_iff, ← star_eq_inv, Matrix.specialUnitaryGroup.coe_star]
    exact (isDiag_of_commute_diagonal hinj hcommC).conjTranspose
  obtain ⟨η, hη⟩ := mem_unitaryTorus_iff_exists_unitaryTorusHom.mp hCdiag
  have hη_mat : ((C⁻¹ : Matrix.specialUnitaryGroup (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ) =
      diagonal (fun j => (η j : ℂ)) := by
    simpa [coe_unitaryTorusHom] using (congrArg Subtype.val hη).symm
  have hprod_coe : ((∏ j : Fin r, η j : Circle) : ℂ) = 1 := by
    change Circle.coeHom (∏ j : Fin r, η j) = 1
    rw [map_prod]
    exact det_diagonal.symm.trans (hη_mat ▸ (mem_specialUnitaryGroup_iff.mp (C⁻¹).2).2)
  exact ⟨η, Circle.coe_eq_one.mp hprod_coe, hη_mat⟩

/-- Conjugating the rescaled cyclic shift `B₀ = c₂ • permutationUnitary (finRotate r)` by a
rescaled diagonal matrix `D = α • unitaryTorusHom δ` multiplies `B₀` on the left by
`diagonal (fun k => δ k * (δ ((finRotate r).symm k))⁻¹)`. -/
private theorem conj_shift_eq_torus_mul {r : ℕ} {B₀ C : Matrix.specialUnitaryGroup (Fin r) ℂ}
    {c₂ α : Circle} {δ η : Fin r → Circle}
    (hB₀ : (B₀ : Matrix (Fin r) (Fin r) ℂ) =
      (c₂ : ℂ) • ((permutationUnitary (finRotate r) : unitaryGroup (Fin r) ℂ) :
        Matrix (Fin r) (Fin r) ℂ))
    (hδ : ∀ k : Fin r, δ k * (δ ((finRotate r).symm k))⁻¹ = η k)
    (hη_mat : ((C⁻¹ : Matrix.specialUnitaryGroup (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ) =
      diagonal (fun j => (η j : ℂ)))
    (hα : (α : ℂ) • (unitaryTorusHom (Fin r) δ : Matrix (Fin r) (Fin r) ℂ) ∈
      Matrix.specialUnitaryGroup (Fin r) ℂ) :
    (⟨(α : ℂ) • (unitaryTorusHom (Fin r) δ : Matrix (Fin r) (Fin r) ℂ), hα⟩ :
        Matrix.specialUnitaryGroup (Fin r) ℂ) * B₀ *
      (⟨(α : ℂ) • (unitaryTorusHom (Fin r) δ : Matrix (Fin r) (Fin r) ℂ), hα⟩)⁻¹ =
      C⁻¹ * B₀ := by
  let DU : unitaryGroup (Fin r) ℂ := unitaryTorusHom (Fin r) δ
  let QU : unitaryGroup (Fin r) ℂ := permutationUnitary (finRotate r)
  let D : Matrix.specialUnitaryGroup (Fin r) ℂ := ⟨(α : ℂ) • (DU : Matrix _ _ ℂ), hα⟩
  have hconjQ : (QU * DU⁻¹ * QU⁻¹ : unitaryGroup (Fin r) ℂ) =
      unitaryTorusHom (Fin r) (fun k => (δ ((finRotate r).symm k))⁻¹) := by
    have hinv : DU⁻¹ = unitaryTorusHom (Fin r) (fun k => (δ k)⁻¹) := (map_inv _ _).symm
    have h := unitaryTorusNormalizer_mul_unitaryTorusHom_mul_inv
      ⟨permutationUnitary (finRotate r), permutationUnitary_mem_normalizer (finRotate r)⟩
      (fun k => (δ k)⁻¹)
    rw [unitaryTorusNormalizerPerm_permutationUnitary, ← hinv] at h
    exact h
  have hcomm_mat : (↑⁅D, B₀⁆ : Matrix (Fin r) (Fin r) ℂ) =
      ((C⁻¹ : Matrix.specialUnitaryGroup (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ) := by
    rw [commutator_circle_smul_eq (U := DU) (V := QU) rfl hB₀, hη_mat, ← coe_unitaryTorusHom,
      ← funext hδ, ← Pi.mul_def, map_mul, ← hconjQ, Submonoid.coe_mul, Submonoid.coe_mul,
      Submonoid.coe_mul, ← Unitary.star_eq_inv, Unitary.coe_star, ← Unitary.star_eq_inv,
      Unitary.coe_star]
    dsimp only [DU]
    simp only [Matrix.mul_assoc]
  have hcomm : ⁅D, B₀⁆ = C⁻¹ := Subtype.ext hcomm_mat
  calc D * B₀ * D⁻¹ = ⁅D, B₀⁆ * B₀ := by group
    _ = C⁻¹ * B₀ := by rw [hcomm]

/-- If `(A₀, B)` and `(A₀, B₀)` both solve `⁅A₀, -⁆ = ζ • 1` with the standard clock matrix `A₀`
and shift matrix `B₀`, some diagonal element of `SU(r)` conjugates `(A₀, B)` to `(A₀, B₀)`. -/
private theorem exists_diag_conj_second_eq {r : ℕ} (hr : 1 ≤ r) {ζ : ℂ}
    (hζ : IsPrimitiveRoot ζ r) {A₀ B₀ B : Matrix.specialUnitaryGroup (Fin r) ℂ} {c₁ c₂ : Circle}
    (hA₀ : (A₀ : Matrix (Fin r) (Fin r) ℂ) = diagonal (fun k : Fin r => ζ ^ (k : ℕ) * (c₁ : ℂ)))
    (hB₀ : (B₀ : Matrix (Fin r) (Fin r) ℂ) =
      (c₂ : ℂ) • ((permutationUnitary (finRotate r) : unitaryGroup (Fin r) ℂ) :
        Matrix (Fin r) (Fin r) ℂ))
    (hrel₀ : (↑⁅A₀, B₀⁆ : Matrix (Fin r) (Fin r) ℂ) = ζ • 1)
    (hrel : (↑⁅A₀, B⁆ : Matrix (Fin r) (Fin r) ℂ) = ζ • 1) :
    ∃ D : Matrix.specialUnitaryGroup (Fin r) ℂ,
      D * A₀ * D⁻¹ = A₀ ∧ D * B * D⁻¹ = B₀ := by
  let C : Matrix.specialUnitaryGroup (Fin r) ℂ := B * B₀⁻¹
  obtain ⟨η, hη_prod, hη_mat⟩ := exists_torus_of_commutator_eq hζ hA₀ hrel₀ hrel
  obtain ⟨δ, hδ⟩ := prefixProd_mul_finRotate_symm_inv hr hη_prod
  obtain ⟨α, hα⟩ := exists_circle_smul_mem_specialUnitaryGroup (unitaryTorusHom (Fin r) δ)
  let D : Matrix.specialUnitaryGroup (Fin r) ℂ :=
    ⟨(α : ℂ) • (unitaryTorusHom (Fin r) δ : Matrix (Fin r) (Fin r) ℂ), hα⟩
  have hdiag_comm : ∀ {X : Matrix.specialUnitaryGroup (Fin r) ℂ} (f : Fin r → ℂ),
      (X : Matrix (Fin r) (Fin r) ℂ) = diagonal f → D * X = X * D := fun f hX => Subtype.ext <| by
    rw [Submonoid.coe_mul, Submonoid.coe_mul, hX]
    dsimp only [D]
    rw [coe_unitaryTorusHom, smul_mul_assoc, mul_smul_comm, diagonal_mul_diagonal,
      diagonal_mul_diagonal]
    exact congrArg (α.1 • ·) (congrArg diagonal (funext fun _ => mul_comm _ _))
  have hDA : D * A₀ * D⁻¹ = A₀ := mul_inv_eq_iff_eq_mul.mpr (hdiag_comm _ hA₀)
  have hDC : D * C = C * D := Commute.inv_right_iff.mp (hdiag_comm _ hη_mat)
  have hDB₀ : D * B₀ * D⁻¹ = C⁻¹ * B₀ := conj_shift_eq_torus_mul hB₀ hδ hη_mat hα
  refine ⟨D, hDA, ?_⟩
  calc D * B * D⁻¹ = D * (C * B₀) * D⁻¹ := by simp [C]
    _ = C * (D * B₀ * D⁻¹) := by simp only [← mul_assoc, hDC]
    _ = B₀ := by rw [hDB₀, mul_inv_cancel_left]

/-- Iterated conjugation of `A₁` by `B₁` scales `A₁` by powers of `ζ⁻¹` whenever
`⁅A₁, B₁⁆ = ζ • 1` and `ζ ≠ 0`. -/
private theorem conj_pow_eq_inv_pow_smul {r : ℕ} {ζ : ℂ} (hζ : ζ ≠ 0)
    {A₁ B₁ : Matrix.specialUnitaryGroup (Fin r) ℂ}
    (hrel₁ : (↑⁅A₁, B₁⁆ : Matrix (Fin r) (Fin r) ℂ) = ζ • 1) (n : ℕ) :
    ((B₁ ^ n * A₁ * (B₁ ^ n)⁻¹ : Matrix.specialUnitaryGroup (Fin r) ℂ) :
      Matrix (Fin r) (Fin r) ℂ) = (ζ⁻¹) ^ n • (A₁ : Matrix (Fin r) (Fin r) ℂ) := by
  have hB₁A₁ : ((B₁ * A₁ * B₁⁻¹ : Matrix.specialUnitaryGroup (Fin r) ℂ) :
      Matrix (Fin r) (Fin r) ℂ) = ζ⁻¹ • (A₁ : Matrix (Fin r) (Fin r) ℂ) := by
    let MB₁inv : Matrix (Fin r) (Fin r) ℂ := (B₁⁻¹ : Matrix.specialUnitaryGroup (Fin r) ℂ)
    have hAB₁ : (A₁ : Matrix (Fin r) (Fin r) ℂ) * (B₁ : Matrix (Fin r) (Fin r) ℂ) =
        ζ • ((B₁ : Matrix (Fin r) (Fin r) ℂ) * (A₁ : Matrix (Fin r) (Fin r) ℂ)) := by
      calc (A₁ : Matrix (Fin r) (Fin r) ℂ) * (B₁ : Matrix (Fin r) (Fin r) ℂ)
          = (↑⁅A₁, B₁⁆ : Matrix (Fin r) (Fin r) ℂ) * (B₁ : Matrix (Fin r) (Fin r) ℂ) *
              (A₁ : Matrix (Fin r) (Fin r) ℂ) := by
            simp only [commutatorElement_def, ← Submonoid.coe_mul, inv_mul_cancel_right]
        _ = ζ • ((B₁ : Matrix (Fin r) (Fin r) ℂ) * (A₁ : Matrix (Fin r) (Fin r) ℂ)) := by
            rw [hrel₁, Matrix.smul_mul, Matrix.one_mul, smul_mul_assoc]
    have hB₁_inv : (B₁ : Matrix (Fin r) (Fin r) ℂ) * MB₁inv = 1 := by
      rw [← Submonoid.coe_mul, mul_inv_cancel, OneMemClass.coe_one]
    calc (((B₁ * A₁ * B₁⁻¹ : Matrix.specialUnitaryGroup (Fin r) ℂ)) : Matrix (Fin r) (Fin r) ℂ)
        = ζ⁻¹ • ((ζ • ((B₁ : Matrix (Fin r) (Fin r) ℂ) * (A₁ : Matrix (Fin r) (Fin r) ℂ))) *
            MB₁inv) := by
          rw [smul_mul_assoc, smul_smul, inv_mul_cancel₀ hζ, one_smul, Submonoid.coe_mul,
            Submonoid.coe_mul]
      _ = ζ⁻¹ • (A₁ : Matrix (Fin r) (Fin r) ℂ) := by
          rw [← hAB₁, Matrix.mul_assoc, hB₁_inv, Matrix.mul_one]
  induction n with
  | zero => simp
  | succ n ih =>
    have hexp : B₁ ^ (n + 1) * A₁ * (B₁ ^ (n + 1))⁻¹ =
        B₁ * (B₁ ^ n * A₁ * (B₁ ^ n)⁻¹) * B₁⁻¹ := by
      rw [pow_succ', _root_.mul_inv_rev]
      group
    rw [hexp, Submonoid.coe_mul, Submonoid.coe_mul, ih, mul_smul_comm, smul_mul_assoc,
      ← Submonoid.coe_mul, ← Submonoid.coe_mul, hB₁A₁, smul_smul, pow_succ]

/-- For `1 ≤ r` and `IsPrimitiveRoot ζ r`, any solution `(A, B)` of `⁅A, B⁆ = ζ • 1` in `SU(r)` is
simultaneously conjugate in `SU(r)` to the standard clock-and-shift pair `(A₀, B₀)`. -/
private theorem exists_conj_eq_clock_shift_pair {r : ℕ} (hr : 1 ≤ r) {ζ : ℂ}
    (hζ : IsPrimitiveRoot ζ r) {A₀ B₀ : Matrix.specialUnitaryGroup (Fin r) ℂ} {c₁ c₂ : Circle}
    (hA₀ : (A₀ : Matrix (Fin r) (Fin r) ℂ) = diagonal (fun k : Fin r => ζ ^ (k : ℕ) * (c₁ : ℂ)))
    (hB₀ : (B₀ : Matrix (Fin r) (Fin r) ℂ) =
      (c₂ : ℂ) • ((permutationUnitary (finRotate r) : unitaryGroup (Fin r) ℂ) :
        Matrix (Fin r) (Fin r) ℂ))
    (hrel₀ : (↑⁅A₀, B₀⁆ : Matrix (Fin r) (Fin r) ℂ) = ζ • 1)
    (A B : Matrix.specialUnitaryGroup (Fin r) ℂ)
    (hAB : (↑⁅A, B⁆ : Matrix (Fin r) (Fin r) ℂ) = ζ • 1) :
    ∃ w : Matrix.specialUnitaryGroup (Fin r) ℂ,
      w * A * w⁻¹ = A₀ ∧ w * B * w⁻¹ = B₀ := by
  have : NeZero r := ⟨by omega⟩
  have hζ0 : ζ ≠ 0 := hζ.ne_zero (by omega)
  obtain ⟨u₁, μ, _, hu₁⟩ := exists_conj_first_eq_clock hr hζ A B hAB
  let A₁ := u₁ * A * u₁⁻¹
  let B₁ := u₁ * B * u₁⁻¹
  have hrel₁ : (↑⁅A₁, B₁⁆ : Matrix (Fin r) (Fin r) ℂ) = ζ • 1 := by
    have h := conjAct_smul_mem_relationSet (ConjAct.toConjAct u₁)
      (x := fun _ : Fin 1 => (A, B)) (mem_relationSet_one_iff.mpr hAB)
    simpa only [mem_relationSet_one_iff, Pi.smul_apply, Prod.smul_mk, ConjAct.smul_def,
      ConjAct.ofConjAct_toConjAct] using h
  have hratio : (μ / (c₁ : ℂ)) ^ r = 1 := by
    have hdetA₁ := (mem_specialUnitaryGroup_iff.mp A₁.2).2
    have hdetA₀ := (mem_specialUnitaryGroup_iff.mp A₀.2).2
    rw [hu₁, det_diagonal, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ,
      Fintype.card_fin] at hdetA₁
    rw [hA₀, det_diagonal, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ,
      Fintype.card_fin] at hdetA₀
    have hprod_ne : (∏ k : Fin r, ζ ^ (k : ℕ)) ≠ 0 :=
      Finset.prod_ne_zero_iff.mpr fun _ _ => pow_ne_zero _ hζ0
    rw [div_pow, mul_left_cancel₀ hprod_ne (hdetA₁.trans hdetA₀.symm),
      div_self (pow_ne_zero _ (Circle.coe_ne_zero c₁))]
  obtain ⟨m, _, hm⟩ := hζ.eq_pow_of_pow_eq_one hratio
  have hA₂ : B₁ ^ m * A₁ * (B₁ ^ m)⁻¹ = A₀ := Subtype.ext <| by
    rw [conj_pow_eq_inv_pow_smul hζ0 hrel₁ m, hu₁, hA₀, ← diagonal_smul]
    refine congrArg diagonal (funext fun k => ?_)
    have hμ_eq : μ = ζ ^ m * (c₁ : ℂ) := by rw [hm, div_mul_cancel₀ _ (Circle.coe_ne_zero c₁)]
    rw [Pi.smul_apply, smul_eq_mul, hμ_eq, inv_pow]
    linear_combination (ζ ^ (k : ℕ) * (c₁ : ℂ)) * inv_mul_cancel₀ (pow_ne_zero m hζ0)
  have hB₁_self : B₁ ^ m * B₁ * (B₁ ^ m)⁻¹ = B₁ := by group
  have hrel₂ : (↑⁅A₀, B₁⁆ : Matrix (Fin r) (Fin r) ℂ) = ζ • 1 := by
    have h := conjAct_smul_mem_relationSet (ConjAct.toConjAct (B₁ ^ m))
      (x := fun _ : Fin 1 => (A₁, B₁)) (mem_relationSet_one_iff.mpr hrel₁)
    simpa only [mem_relationSet_one_iff, Pi.smul_apply, Prod.smul_mk, ConjAct.smul_def,
      ConjAct.ofConjAct_toConjAct, hA₂, hB₁_self] using h
  obtain ⟨D, hDA₀, hDB₁⟩ := exists_diag_conj_second_eq hr hζ hA₀ hB₀ hrel₀ hrel₂
  refine ⟨D * B₁ ^ m * u₁, ?_, ?_⟩
  · calc (D * B₁ ^ m * u₁) * A * (D * B₁ ^ m * u₁)⁻¹
        = D * (B₁ ^ m * A₁ * (B₁ ^ m)⁻¹) * D⁻¹ := by simp only [A₁, _root_.mul_inv_rev, mul_assoc]
      _ = A₀ := by rw [hA₂, hDA₀]
  · calc (D * B₁ ^ m * u₁) * B * (D * B₁ ^ m * u₁)⁻¹
        = D * (B₁ ^ m * B₁ * (B₁ ^ m)⁻¹) * D⁻¹ := by simp only [B₁, _root_.mul_inv_rev, mul_assoc]
      _ = B₀ := by rw [hB₁_self, hDB₁]

/-- **Genus-one twisted `SU(r)` moduli is a single point.** When `ζ` is a primitive `r`-th root of
unity, `relationModuli r ζ 1` is nonempty and a subsingleton. No positivity assumption on `r` is
needed: for `r = 0`, `SU(0)` is trivial and `Matrix (Fin 0) (Fin 0) ℂ` is a subsingleton. -/
theorem relationModuli_genus_one {r : ℕ} {ζ : ℂ} (hζ : IsPrimitiveRoot ζ r) :
    Nonempty (relationModuli r ζ 1) ∧ Subsingleton (relationModuli r ζ 1) := by
  rcases Nat.eq_zero_or_pos r with rfl | hr
  · have hx₀ : (fun _ : Fin 1 => (1, 1)) ∈ relationSet 0 ζ 1 :=
      mem_relationSet_one_iff.mpr (Subsingleton.elim _ _)
    have : Subsingleton (relationSet 0 ζ 1) :=
      ⟨fun _ _ => Subtype.ext (funext fun _ => Prod.ext (Subsingleton.elim _ _)
        (Subsingleton.elim _ _))⟩
    exact ⟨⟨relationModuliMk ⟨_, hx₀⟩⟩, inferInstance⟩
  obtain ⟨A₀, B₀, c₁, c₂, hA₀, hB₀, hrel₀⟩ := exists_clock_shift_pair hr hζ
  let x₀ : relationSet r ζ 1 := ⟨fun _ => (A₀, B₀), mem_relationSet_one_iff.mpr hrel₀⟩
  have heq : ∀ x : relationSet r ζ 1, relationModuliMk x = relationModuliMk x₀ := fun x => by
    obtain ⟨w, hwA, hwB⟩ := exists_conj_eq_clock_shift_pair hr hζ hA₀ hB₀ hrel₀
      (x.1 0).1 (x.1 0).2 (mem_relationSet_one_iff.mp x.2)
    rw [relationModuliMk_eq_iff]
    refine ⟨w⁻¹, funext fun j => ?_⟩
    rw [Fin.eq_zero j]
    apply Prod.ext
    · dsimp only [x₀]
      simp only [Pi.smul_apply, Prod.smul_fst, ConjAct.smul_def, ConjAct.ofConjAct_toConjAct,
        inv_inv, ← hwA]
      group
    · dsimp only [x₀]
      simp only [Pi.smul_apply, Prod.smul_snd, ConjAct.smul_def, ConjAct.ofConjAct_toConjAct,
        inv_inv, ← hwB]
      group
  refine ⟨⟨relationModuliMk x₀⟩, ⟨fun q₁ q₂ => ?_⟩⟩
  obtain ⟨x₁, rfl⟩ := relationModuliMk_surjective r ζ 1 q₁
  obtain ⟨x₂, rfl⟩ := relationModuliMk_surjective r ζ 1 q₂
  exact (heq x₁).trans (heq x₂).symm

/-- When `IsPrimitiveRoot ζ r`, `relationModuli r ζ 1` is contractible. -/
theorem contractibleSpace_relationModuli_one {r : ℕ} {ζ : ℂ} (hζ : IsPrimitiveRoot ζ r) :
    ContractibleSpace (relationModuli r ζ 1) := by
  have := (relationModuli_genus_one hζ).1
  have := (relationModuli_genus_one hζ).2
  infer_instance

/-- When `IsPrimitiveRoot ζ r`, `relationModuli r ζ 1` is simply connected. -/
theorem simplyConnectedSpace_relationModuli_one {r : ℕ} {ζ : ℂ} (hζ : IsPrimitiveRoot ζ r) :
    SimplyConnectedSpace (relationModuli r ζ 1) := by
  have := contractibleSpace_relationModuli_one hζ
  infer_instance

/-! ### Non-freeness of central twists at genus one and non-coprime counterexamples -/

/-- **Non-freeness of the central-twist action on the genus-one coprime moduli.** For `2 ≤ r` and
`IsPrimitiveRoot ζ r`, there is a nontrivial central twist `ε ≠ 1` that acts as the identity on
`relationModuli r ζ 1` (since `relationModuli r ζ 1` is a single point while `center(SU(r))` has
nontrivial element `ζ • 1`). -/
theorem exists_ne_one_smul_eq_self_relationModuli_one {r : ℕ} (hr : 2 ≤ r) {ζ : ℂ}
    (hζ : IsPrimitiveRoot ζ r) :
    ∃ ε : Fin 1 → Subgroup.center (Matrix.specialUnitaryGroup (Fin r) ℂ) ×
        Subgroup.center (Matrix.specialUnitaryGroup (Fin r) ℂ),
      ε ≠ 1 ∧ ∀ q : relationModuli r ζ 1, ε • q = q := by
  have hpow : ζ ^ Fintype.card (Fin r) = 1 := by simpa using hζ.pow_eq_one
  let zζ : Subgroup.center (Matrix.specialUnitaryGroup (Fin r) ℂ) :=
    ⟨⟨scalar (Fin r) ζ, Matrix.specialUnitaryGroup.scalar_mem hpow⟩,
      Matrix.specialUnitaryGroup.mem_center_of_coe_eq_scalar rfl⟩
  refine ⟨fun _ => (zζ, 1), fun h => hζ.ne_one hr ?_, fun _ => ?_⟩
  · have h0 := congrArg (fun f => ((f 0).1.1 : Matrix (Fin r) (Fin r) ℂ) ⟨0, by omega⟩
      ⟨0, by omega⟩) h
    simpa [zζ] using h0
  · exact (relationModuli_genus_one hζ).2.elim _ _

/-- **Non-coprime counterexample (`r = 2`, `ζ = 1`, `g = 1`): non-uniqueness.** Without
`IsPrimitiveRoot ζ r`, the untwisted genus-one moduli `relationModuli 2 1 1` has distinct points
represented by `(1, 1)` and `(-1, 1)`. -/
theorem nontrivial_relationModuli_two_one_one :
    Nontrivial (relationModuli 2 1 1) := by
  let m1 : Matrix.specialUnitaryGroup (Fin 2) ℂ :=
    ⟨scalar (Fin 2) (-1), Matrix.specialUnitaryGroup.scalar_mem (by norm_num)⟩
  let x₁ : relationSet 2 1 1 := ⟨fun _ => (1, 1), by simp⟩
  let x₂ : relationSet 2 1 1 := ⟨fun _ => (m1, 1), by simp⟩
  refine ⟨relationModuliMk x₁, relationModuliMk x₂, fun h => ?_⟩
  obtain ⟨u, hu⟩ := (relationModuliMk_eq_iff x₁ x₂).mp h
  have hu0 : ((ConjAct.toConjAct u • x₂.1) 0).1 = (x₁.1 0).1 := congrArg Prod.fst (congrFun hu 0)
  have hm1_cen : m1 ∈ Subgroup.center (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
    Matrix.specialUnitaryGroup.mem_center_of_coe_eq_scalar rfl
  rw [Pi.smul_apply, Prod.smul_fst, ConjAct.smul_def, ConjAct.ofConjAct_toConjAct,
    Subgroup.mem_center_iff.mp hm1_cen u, mul_inv_cancel_right] at hu0
  have h00 := congr_fun₂ (congrArg Subtype.val hu0) 0 0
  norm_num [m1, x₁] at h00

/-- **Non-coprime counterexample (`r = 2`, `ζ = 1`, `g = 1`): non-central stabilizer.** At
`r = 2`, `ζ = 1`, `g = 1`, the diagonal matrix `diag(I, -I) ∈ SU(2)` fixes `(1, 1) ∈ relationSet`
without lying in `Subgroup.center (SU(2))`. -/
theorem exists_notMem_center_commute_relationSet_two_one_one :
    ∃ (x : relationSet 2 1 1) (u : Matrix.specialUnitaryGroup (Fin 2) ℂ),
      (∀ j, Commute u (x.1 j).1 ∧ Commute u (x.1 j).2) ∧
      u ∉ Subgroup.center (Matrix.specialUnitaryGroup (Fin 2) ℂ) := by
  let d : Fin 2 → ℂ := ![Complex.I, -Complex.I]
  have hd_mem : diagonal d ∈ Matrix.specialUnitaryGroup (Fin 2) ℂ := by
    refine mem_specialUnitaryGroup_iff.mpr ⟨?_, ?_⟩
    · rw [diagonal_mem_unitary, Pi.mem_unitary_iff]
      intro i
      fin_cases i <;> simp [d, Unitary.mem_iff_star_mul_self]
    · simp [d, det_diagonal, Fin.prod_univ_two]
  let u : Matrix.specialUnitaryGroup (Fin 2) ℂ := ⟨diagonal d, hd_mem⟩
  let x : relationSet 2 1 1 := ⟨fun _ => (1, 1), by simp⟩
  refine ⟨x, u, fun _ => ⟨Commute.one_right u, Commute.one_right u⟩, fun hu => ?_⟩
  obtain ⟨c, _, hc⟩ := Matrix.specialUnitaryGroup.mem_center_iff.mp hu
  have h00 := congr_fun₂ hc 0 0
  have h11 := congr_fun₂ hc 1 1
  simp only [scalar_apply, diagonal_apply_eq, u, d, Matrix.cons_val_zero,
    Matrix.cons_val_one] at h00 h11
  have h2I : (2 : ℂ) * Complex.I = 0 := by linear_combination h11 - h00
  exact mul_ne_zero two_ne_zero Complex.I_ne_zero h2I

end TauCeti.SpecialUnitary
