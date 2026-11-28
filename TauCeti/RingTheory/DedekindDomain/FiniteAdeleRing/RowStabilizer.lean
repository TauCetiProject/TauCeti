/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import TauCeti.RingTheory.DedekindDomain.FiniteAdeleRing.FractionalIdeal

/-!
# Stabilizers of rank-two finite adelic row lattices

For a nonzero fractional ideal `J`, the finite adelic row lattice is `Ô ⊕ JÔ`.
Its endomorphism order consists of matrices with entries in `[[Ô, JÔ], [J⁻¹Ô, Ô]]`.
Its stabilizer consists of the matrices in this order whose determinant is an everywhere
integral unit. These constructions require no choice of generator for `J`.

## References

* C. Birkbeck, B. Heuer and C. Williams, *Overconvergent Hilbert modular forms via perfectoid
  modular varieties*, Ann. Inst. Fourier 73 (2023), Notation 5.1(3) and Definition 5.2(1).
  We use row vectors; the determinant-unit condition enforces equality of lattices.
-/

public section
noncomputable section

open IsDedekindDomain IsDedekindDomain.FiniteAdeleRing
open scoped Matrix nonZeroDivisors

namespace TauCeti

variable {R : Type*} [CommRing R] [IsDedekindDomain R]
variable {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]

/-- The finite adelic row lattice `Ô ⊕ JÔ`, with its natural `Ô`-module structure.
The unit parameter `J` records that the fractional ideal is nonzero. -/
def finiteAdelicRowLattice (J : (FractionalIdeal R⁰ K)ˣ) :
    Submodule (integralAdeles R K) (Fin 2 → 𝔸ᶠ[R, K]) where
  carrier := {x | x 0 ∈ integralAdeles R K ∧
    x 1 ∈ finiteAdelicIdeal J}
  zero_mem' := ⟨zero_mem _, zero_mem _⟩
  add_mem' hx hy := ⟨add_mem hx.1 hy.1, add_mem hx.2 hy.2⟩
  smul_mem' a _ hx := ⟨mul_mem a.property hx.1,
    (finiteAdelicIdeal J).smul_mem a hx.2⟩

/-- Membership in the finite adelic row lattice is coordinatewise membership in `Ô` and
`JÔ`. -/
@[simp]
theorem mem_finiteAdelicRowLattice {J : (FractionalIdeal R⁰ K)ˣ}
    {x : Fin 2 → 𝔸ᶠ[R, K]} :
    x ∈ finiteAdelicRowLattice J ↔ x 0 ∈ integralAdeles R K ∧
      x 1 ∈ finiteAdelicIdeal J := Iff.rfl

/-- The row endomorphism order of the finite adelic row lattice. -/
def finiteAdelicRowOrder (J : (FractionalIdeal R⁰ K)ˣ) :
    Subring (Matrix (Fin 2) (Fin 2) 𝔸ᶠ[R, K]) where
  carrier := {M | ∀ x ∈ finiteAdelicRowLattice J, x ᵥ* M ∈ finiteAdelicRowLattice J}
  zero_mem' := by simp
  one_mem' := by intro x hx; simpa using hx
  add_mem' hM hN x hx := by
    simpa only [Matrix.vecMul_add] using (finiteAdelicRowLattice J).add_mem (hM x hx) (hN x hx)
  neg_mem' hM x hx := by
    simpa only [Matrix.vecMul_neg] using (finiteAdelicRowLattice J).neg_mem (hM x hx)
  mul_mem' hM hN x hx := by
    rw [← Matrix.vecMul_vecMul]
    exact hN _ (hM x hx)

/-- Membership in the row endomorphism order means preservation of the row lattice. -/
theorem mem_finiteAdelicRowOrder {J : (FractionalIdeal R⁰ K)ˣ}
    {M : Matrix (Fin 2) (Fin 2) 𝔸ᶠ[R, K]} :
    M ∈ finiteAdelicRowOrder J ↔
      ∀ x ∈ finiteAdelicRowLattice J, x ᵥ* M ∈ finiteAdelicRowLattice J := Iff.rfl

/-- The four entry ideals of the row endomorphism order, listed row by row as
`Ô, JÔ, J⁻¹Ô, Ô`. -/
theorem mem_finiteAdelicRowOrder_iff_entries {J : (FractionalIdeal R⁰ K)ˣ}
    {M : Matrix (Fin 2) (Fin 2) 𝔸ᶠ[R, K]} :
    M ∈ finiteAdelicRowOrder J ↔
      M 0 0 ∈ integralAdeles R K ∧
      M 0 1 ∈ finiteAdelicIdeal J ∧
      M 1 0 ∈ finiteAdelicIdeal J⁻¹ ∧
      M 1 1 ∈ integralAdeles R K := by
  obtain ⟨t, ht⟩ := toFractionalIdeal_surjective J
  have htinv : toFractionalIdeal t⁻¹ = J⁻¹ := by
    rw [map_inv, ht]
  have htmem : (t : 𝔸ᶠ[R, K]) ∈ finiteAdelicIdeal J := by
    rw [← ht]
    exact coe_mem_finiteAdelicIdeal t
  constructor
  · intro h
    rw [mem_finiteAdelicRowOrder] at h
    have h₀ := h ![1, 0] (mem_finiteAdelicRowLattice.mpr ⟨one_mem _, zero_mem _⟩)
    have h₁ := h ![0, (t : 𝔸ᶠ[R, K])] (mem_finiteAdelicRowLattice.mpr
      ⟨zero_mem _, htmem⟩)
    simp only [mem_finiteAdelicRowLattice, Matrix.vecMul, dotProduct, Fin.sum_univ_two,
      Matrix.cons_val_zero, Matrix.cons_val_one, one_mul, zero_mul, add_zero, zero_add] at h₀ h₁
    refine ⟨h₀.1, h₀.2, ?_, ?_⟩
    · simpa only [mem_finiteAdelicIdeal_iff t⁻¹ htinv, inv_inv] using h₁.1
    · rw [mem_finiteAdelicIdeal_iff t ht] at h₁
      simpa only [← mul_assoc, Units.inv_mul, one_mul] using h₁.2
  · rintro ⟨haa, hab, hba, hbb⟩
    rw [mem_finiteAdelicRowOrder]
    intro x hx
    rcases mem_finiteAdelicRowLattice.mp hx with ⟨hx₀, hx₁⟩
    have hcross : x 1 * M 1 0 ∈ integralAdeles R K := by
      simpa using mul_mem_finiteAdelicIdeal hx₁ hba
    have hupper : x 0 * M 0 1 ∈ finiteAdelicIdeal J :=
      (finiteAdelicIdeal J).smul_mem ⟨x 0, hx₀⟩ hab
    have hlower : x 1 * M 1 1 ∈ finiteAdelicIdeal J := by
      simpa only [Subalgebra.smul_def, smul_eq_mul, mul_comm] using
        (finiteAdelicIdeal J).smul_mem ⟨M 1 1, hbb⟩ hx₁
    exact mem_finiteAdelicRowLattice.mpr (by
      simpa only [Matrix.vecMul, dotProduct, Fin.sum_univ_two] using
        And.intro (add_mem (mul_mem hx₀ haa) hcross) (add_mem hupper hlower))

/-- The determinant of a row-lattice endomorphism is integral at every finite place. -/
theorem det_mem_integralAdeles_of_mem_finiteAdelicRowOrder
    {J : (FractionalIdeal R⁰ K)ˣ}
    {M : Matrix (Fin 2) (Fin 2) 𝔸ᶠ[R, K]} (hM : M ∈ finiteAdelicRowOrder J) :
    M.det ∈ integralAdeles R K := by
  rcases mem_finiteAdelicRowOrder_iff_entries.mp hM with ⟨haa, hab, hba, hbb⟩
  rw [Matrix.det_fin_two]
  exact sub_mem (mul_mem haa hbb) (by simpa using mul_mem_finiteAdelicIdeal hab hba)

/-- The adjugate preserves the same row order, since its off-diagonal entries change only sign. -/
theorem adjugate_mem_finiteAdelicRowOrder
    {J : (FractionalIdeal R⁰ K)ˣ}
    {M : Matrix (Fin 2) (Fin 2) 𝔸ᶠ[R, K]} (hM : M ∈ finiteAdelicRowOrder J) :
    M.adjugate ∈ finiteAdelicRowOrder J := by
  rcases mem_finiteAdelicRowOrder_iff_entries.mp hM with ⟨haa, hab, hba, hbb⟩
  rw [mem_finiteAdelicRowOrder_iff_entries, Matrix.adjugate_fin_two]
  exact ⟨hbb, neg_mem hab, neg_mem hba, haa⟩

/-- The finite adelic row stabilizer is the unit subgroup of the row endomorphism order.
It consists of matrices that preserve the row lattice in both directions. -/
def finiteAdelicRowStabilizer (J : (FractionalIdeal R⁰ K)ˣ) :
    Subgroup (Matrix.GeneralLinearGroup (Fin 2) 𝔸ᶠ[R, K]) :=
  (finiteAdelicRowOrder J).toSubmonoid.units

/-- A matrix stabilizes the row lattice exactly when its action preserves and reflects
membership in the lattice. -/
theorem mem_finiteAdelicRowStabilizer_iff
    {J : (FractionalIdeal R⁰ K)ˣ}
    {g : Matrix.GeneralLinearGroup (Fin 2) 𝔸ᶠ[R, K]} :
    g ∈ finiteAdelicRowStabilizer J ↔
      ∀ x, x ᵥ* (g : Matrix (Fin 2) (Fin 2) 𝔸ᶠ[R, K]) ∈
        finiteAdelicRowLattice J ↔
        x ∈ finiteAdelicRowLattice J := by
  rw [finiteAdelicRowStabilizer, Submonoid.mem_units_iff]
  simp only [Subring.mem_toSubmonoid, mem_finiteAdelicRowOrder]
  constructor
  · rintro ⟨hg, hgi⟩ x
    refine ⟨fun hx ↦ ?_, fun hx ↦ hg x hx⟩
    have h := hgi _ hx
    simpa only [Units.coeHom_apply, Matrix.vecMul_vecMul, g.mul_inv, Matrix.vecMul_one] using h
  · intro h
    refine ⟨fun x hx ↦ (h x).mpr hx, fun x hx ↦ ?_⟩
    apply (h (x ᵥ* (g⁻¹ : Matrix.GeneralLinearGroup (Fin 2) 𝔸ᶠ[R, K]))).mp
    simpa only [Units.coeHom_apply, Matrix.vecMul_vecMul, g.inv_mul, Matrix.vecMul_one] using hx

/-- The finite adelic stabilizer is the image of the units of its row endomorphism order. -/
theorem range_unitsMap_finiteAdelicRowOrder (J : (FractionalIdeal R⁰ K)ˣ) :
    (Units.map (finiteAdelicRowOrder J).subtype.toMonoidHom).range =
      finiteAdelicRowStabilizer J := by
  ext g
  rw [MonoidHom.mem_range, finiteAdelicRowStabilizer]
  constructor
  · rintro ⟨u, rfl⟩
    rw [Submonoid.mem_units_iff]
    exact ⟨u.val.property, u.inv.property⟩
  · intro hg
    refine ⟨(finiteAdelicRowOrder J).toSubmonoid.unitsEquivUnitsType ⟨g, hg⟩, ?_⟩
    -- The equivalence retains the ambient matrix, and the subtype inclusion forgets only
    -- the proof that it lies in the order.
    apply Units.ext
    rfl

/-- A matrix in `GL₂(A_f)` stabilizes the lattice precisely when it belongs to the row order
and its determinant is an everywhere integral unit. -/
theorem mem_finiteAdelicRowStabilizer_iff_order_and_det
    {J : (FractionalIdeal R⁰ K)ˣ}
    {g : Matrix.GeneralLinearGroup (Fin 2) 𝔸ᶠ[R, K]} :
    g ∈ finiteAdelicRowStabilizer J ↔
      (g : Matrix (Fin 2) (Fin 2) 𝔸ᶠ[R, K]) ∈ finiteAdelicRowOrder J ∧
      Matrix.GeneralLinearGroup.det g ∈ integralUnits R K := by
  rw [finiteAdelicRowStabilizer, Submonoid.mem_units_iff]
  simp only [Subring.mem_toSubmonoid]
  constructor
  · rintro ⟨hg, hgi⟩
    refine ⟨hg, ?_⟩
    rw [mem_integralUnits_iff_val_mem_and_inv_mem]
    exact ⟨det_mem_integralAdeles_of_mem_finiteAdelicRowOrder hg,
      det_mem_integralAdeles_of_mem_finiteAdelicRowOrder hgi⟩
  · rintro ⟨hg, hd⟩
    refine ⟨hg, ?_⟩
    have hdinv := (mem_integralUnits_iff_val_mem_and_inv_mem.mp hd).2
    have hinv : (↑g⁻¹ : Matrix (Fin 2) (Fin 2) 𝔸ᶠ[R, K]) =
        (↑(Matrix.GeneralLinearGroup.det g)⁻¹ : 𝔸ᶠ[R, K]) •
          (g : Matrix (Fin 2) (Fin 2) 𝔸ᶠ[R, K]).adjugate := by
      rw [Matrix.coe_units_inv, Matrix.inv_def,
        ← Matrix.GeneralLinearGroup.val_det_apply, Ring.inverse_unit]
    rw [mem_finiteAdelicRowOrder]
    intro x hx
    rw [hinv, Matrix.vecMul_smul]
    simpa only [Subalgebra.smul_def] using (finiteAdelicRowLattice J).smul_mem
      ⟨_, hdinv⟩ (mem_finiteAdelicRowOrder.mp (adjugate_mem_finiteAdelicRowOrder hg) x hx)

/-- The explicit entry-ideal and determinant-unit description of the finite adelic row
stabilizer. -/
theorem mem_finiteAdelicRowStabilizer_iff_entries
    {J : (FractionalIdeal R⁰ K)ˣ}
    {g : Matrix.GeneralLinearGroup (Fin 2) 𝔸ᶠ[R, K]} :
    g ∈ finiteAdelicRowStabilizer J ↔
      g 0 0 ∈ integralAdeles R K ∧
      g 0 1 ∈ finiteAdelicIdeal J ∧
      g 1 0 ∈ finiteAdelicIdeal J⁻¹ ∧
      g 1 1 ∈ integralAdeles R K ∧
      Matrix.GeneralLinearGroup.det g ∈ integralUnits R K := by
  simp only [mem_finiteAdelicRowStabilizer_iff_order_and_det,
    mem_finiteAdelicRowOrder_iff_entries, and_assoc]

end TauCeti
