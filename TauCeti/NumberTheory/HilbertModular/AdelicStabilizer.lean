/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import TauCeti.NumberTheory.HilbertModular.PolarizationLattice
public import TauCeti.RingTheory.DedekindDomain.FiniteAdeleRing.FractionalIdeal

/-!
# The finite adelic stabilizer of a polarization lattice

For `J = c⁻¹𝔡⁻¹`, the finite adelic row lattice is `Ô ⊕ JÔ`. Its endomorphism order
consists of matrices with entries in `[[Ô, JÔ], [J⁻¹Ô, Ô]]`. Its stabilizer is the image of
this order's units in `GL₂(A_f)`, or equivalently the matrices in the order whose determinant
is an everywhere integral unit. Invertibility over `A_f` alone does not imply this condition.
No generator of the fractional ideal `c` is chosen in these constructions.

## References

* C. Birkbeck, B. Heuer and C. Williams, *Overconvergent Hilbert modular forms via perfectoid
  modular varieties*, Ann. Inst. Fourier 73 (2023), Notation 5.1(3) and Definition 5.2(1).
  We use row vectors; the determinant-unit condition enforces equality of lattices.
-/

public section
noncomputable section

open NumberField FractionalIdeal IsDedekindDomain IsDedekindDomain.FiniteAdeleRing
open scoped Matrix nonZeroDivisors

namespace TauCeti.HilbertModular

variable {K : Type*} [Field K] [NumberField K]

/-- The nonzero second coordinate ideal `J = c⁻¹𝔡⁻¹` of the polarization lattice. -/
def polarizationCoordinateIdeal (c : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    (FractionalIdeal (𝓞 K)⁰ K)ˣ :=
  c⁻¹ * Units.mk0 (dual ℤ ℚ 1) (dual_ne_zero ℤ ℚ one_ne_zero)

@[simp]
theorem coe_polarizationCoordinateIdeal (c : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    (polarizationCoordinateIdeal c : FractionalIdeal (𝓞 K)⁰ K) =
      c.val⁻¹ * dual ℤ ℚ 1 := by
  simp [polarizationCoordinateIdeal]

/-- The finite adelic polarization lattice `Ô ⊕ c⁻¹𝔡⁻¹Ô`, with its natural `Ô`-module
structure. The unit parameter `c` records that the polarization ideal is nonzero. -/
def adelicPolarizationLattice (c : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    Submodule (integralAdeles (𝓞 K) K) (Fin 2 → 𝔸ᶠ[𝓞 K, K]) where
  carrier := {x | x 0 ∈ integralAdeles (𝓞 K) K ∧
    x 1 ∈ finiteAdelicIdeal (polarizationCoordinateIdeal c)}
  zero_mem' := ⟨zero_mem _, zero_mem _⟩
  add_mem' hx hy := ⟨add_mem hx.1 hy.1, add_mem hx.2 hy.2⟩
  smul_mem' a _ hx := ⟨mul_mem a.property hx.1,
    (finiteAdelicIdeal (polarizationCoordinateIdeal c)).smul_mem a hx.2⟩

@[simp]
theorem mem_adelicPolarizationLattice {c : (FractionalIdeal (𝓞 K)⁰ K)ˣ}
    {x : Fin 2 → 𝔸ᶠ[𝓞 K, K]} :
    x ∈ adelicPolarizationLattice c ↔ x 0 ∈ integralAdeles (𝓞 K) K ∧
      x 1 ∈ finiteAdelicIdeal (polarizationCoordinateIdeal c) := Iff.rfl

/-- The rational points of the finite adelic row lattice are exactly the original polarization
lattice. -/
theorem algebraMap_mem_adelicPolarizationLattice_iff
    (c : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (x : Fin 2 → K) :
    (fun i ↦ algebraMap K 𝔸ᶠ[𝓞 K, K] (x i)) ∈ adelicPolarizationLattice c ↔
      x ∈ polarizationLattice (c : FractionalIdeal (𝓞 K)⁰ K) := by
  simp only [mem_adelicPolarizationLattice, algebraMap_mem_finiteAdelicIdeal_iff,
    mem_polarizationLattice, coe_polarizationCoordinateIdeal]
  rw [algebraMap_mem_integralAdeles_iff, mem_one_iff]
  rfl

/-- The row endomorphism order of the finite adelic polarization lattice. -/
def adelicPolarizationOrder (c : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    Subring (Matrix (Fin 2) (Fin 2) 𝔸ᶠ[𝓞 K, K]) where
  carrier := {M | ∀ x ∈ adelicPolarizationLattice c, x ᵥ* M ∈ adelicPolarizationLattice c}
  zero_mem' := by simp
  one_mem' := by intro x hx; simpa using hx
  add_mem' hM hN x hx := by
    simpa only [Matrix.vecMul_add] using (adelicPolarizationLattice c).add_mem (hM x hx) (hN x hx)
  neg_mem' hM x hx := by
    simpa only [Matrix.vecMul_neg] using (adelicPolarizationLattice c).neg_mem (hM x hx)
  mul_mem' hM hN x hx := by
    rw [← Matrix.vecMul_vecMul]
    exact hN _ (hM x hx)

/-- Membership in the row endomorphism order means preservation of the row lattice. -/
theorem mem_adelicPolarizationOrder {c : (FractionalIdeal (𝓞 K)⁰ K)ˣ}
    {M : Matrix (Fin 2) (Fin 2) 𝔸ᶠ[𝓞 K, K]} :
    M ∈ adelicPolarizationOrder c ↔
      ∀ x ∈ adelicPolarizationLattice c, x ᵥ* M ∈ adelicPolarizationLattice c := Iff.rfl

/-- The four entry ideals of the row endomorphism order, listed row by row as
`Ô, JÔ, J⁻¹Ô, Ô`. -/
theorem mem_adelicPolarizationOrder_iff {c : (FractionalIdeal (𝓞 K)⁰ K)ˣ}
    {M : Matrix (Fin 2) (Fin 2) 𝔸ᶠ[𝓞 K, K]} :
    M ∈ adelicPolarizationOrder c ↔
      M 0 0 ∈ integralAdeles (𝓞 K) K ∧
      M 0 1 ∈ finiteAdelicIdeal (polarizationCoordinateIdeal c) ∧
      M 1 0 ∈ finiteAdelicIdeal (polarizationCoordinateIdeal c)⁻¹ ∧
      M 1 1 ∈ integralAdeles (𝓞 K) K := by
  obtain ⟨t, ht⟩ := toFractionalIdeal_surjective (polarizationCoordinateIdeal c)
  have htinv : toFractionalIdeal t⁻¹ = (polarizationCoordinateIdeal c)⁻¹ := by
    rw [map_inv, ht]
  have htmem : (t : 𝔸ᶠ[𝓞 K, K]) ∈ finiteAdelicIdeal (polarizationCoordinateIdeal c) := by
    rw [mem_finiteAdelicIdeal_iff t ht]
    simp
  constructor
  · intro h
    have h₀ := h ![1, 0] (mem_adelicPolarizationLattice.mpr ⟨one_mem _, zero_mem _⟩)
    have h₁ := h ![0, (t : 𝔸ᶠ[𝓞 K, K])] (mem_adelicPolarizationLattice.mpr
      ⟨zero_mem _, htmem⟩)
    simp only [mem_adelicPolarizationLattice, Matrix.vecMul, dotProduct, Fin.sum_univ_two,
      Matrix.cons_val_zero, Matrix.cons_val_one, one_mul, zero_mul, add_zero, zero_add] at h₀ h₁
    refine ⟨h₀.1, h₀.2, ?_, ?_⟩
    · simpa only [mem_finiteAdelicIdeal_iff t⁻¹ htinv, inv_inv] using h₁.1
    · rw [mem_finiteAdelicIdeal_iff t ht] at h₁
      simpa only [← mul_assoc, Units.inv_mul, one_mul] using h₁.2
  · rintro ⟨haa, hab, hba, hbb⟩ x hx
    rcases mem_adelicPolarizationLattice.mp hx with ⟨hx₀, hx₁⟩
    have hcross : x 1 * M 1 0 ∈ integralAdeles (𝓞 K) K := by
      simpa using mul_mem_finiteAdelicIdeal hx₁ hba
    have hupper : x 0 * M 0 1 ∈ finiteAdelicIdeal (polarizationCoordinateIdeal c) :=
      (finiteAdelicIdeal (polarizationCoordinateIdeal c)).smul_mem ⟨x 0, hx₀⟩ hab
    have hlower : x 1 * M 1 1 ∈ finiteAdelicIdeal (polarizationCoordinateIdeal c) := by
      simpa only [Subalgebra.smul_def, smul_eq_mul, mul_comm] using
        (finiteAdelicIdeal (polarizationCoordinateIdeal c)).smul_mem ⟨M 1 1, hbb⟩ hx₁
    exact mem_adelicPolarizationLattice.mpr (by
      simpa only [Matrix.vecMul, dotProduct, Fin.sum_univ_two] using
        And.intro (add_mem (mul_mem hx₀ haa) hcross) (add_mem hupper hlower))

/-- The determinant of a row-lattice endomorphism is integral at every finite place. -/
theorem det_mem_integralAdeles_of_mem_adelicPolarizationOrder
    {c : (FractionalIdeal (𝓞 K)⁰ K)ˣ}
    {M : Matrix (Fin 2) (Fin 2) 𝔸ᶠ[𝓞 K, K]} (hM : M ∈ adelicPolarizationOrder c) :
    M.det ∈ integralAdeles (𝓞 K) K := by
  rcases mem_adelicPolarizationOrder_iff.mp hM with ⟨haa, hab, hba, hbb⟩
  rw [Matrix.det_fin_two]
  exact sub_mem (mul_mem haa hbb) (by simpa using mul_mem_finiteAdelicIdeal hab hba)

/-- The adjugate preserves the same row order, since its off-diagonal entries change only sign. -/
theorem adjugate_mem_adelicPolarizationOrder
    {c : (FractionalIdeal (𝓞 K)⁰ K)ˣ}
    {M : Matrix (Fin 2) (Fin 2) 𝔸ᶠ[𝓞 K, K]} (hM : M ∈ adelicPolarizationOrder c) :
    M.adjugate ∈ adelicPolarizationOrder c := by
  rcases mem_adelicPolarizationOrder_iff.mp hM with ⟨haa, hab, hba, hbb⟩
  rw [mem_adelicPolarizationOrder_iff, Matrix.adjugate_fin_two]
  exact ⟨hbb, neg_mem hab, neg_mem hba, haa⟩

/-- The finite adelic row stabilizer is the unit subgroup of the row endomorphism order.
It consists of matrices that preserve the row lattice in both directions. -/
def adelicPolarizationStabilizer (c : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    Subgroup (Matrix.GeneralLinearGroup (Fin 2) 𝔸ᶠ[𝓞 K, K]) :=
  (adelicPolarizationOrder c).toSubmonoid.units

/-- A matrix stabilizes the row lattice exactly when its action preserves and reflects
membership in the lattice. -/
theorem mem_adelicPolarizationStabilizer_iff
    {c : (FractionalIdeal (𝓞 K)⁰ K)ˣ}
    {g : Matrix.GeneralLinearGroup (Fin 2) 𝔸ᶠ[𝓞 K, K]} :
    g ∈ adelicPolarizationStabilizer c ↔
      ∀ x, x ᵥ* (g : Matrix (Fin 2) (Fin 2) 𝔸ᶠ[𝓞 K, K]) ∈
        adelicPolarizationLattice c ↔
        x ∈ adelicPolarizationLattice c := by
  constructor
  · rintro ⟨hg, hgi⟩ x
    refine ⟨fun hx ↦ ?_, fun hx ↦ hg x hx⟩
    have h := hgi _ hx
    simpa only [Units.coeHom_apply, Matrix.vecMul_vecMul, g.mul_inv, Matrix.vecMul_one] using h
  · intro h
    refine ⟨fun x hx ↦ (h x).mpr hx, fun x hx ↦ ?_⟩
    apply (h (x ᵥ* (g⁻¹ : Matrix.GeneralLinearGroup (Fin 2) 𝔸ᶠ[𝓞 K, K]))).mp
    simpa only [Units.coeHom_apply, Matrix.vecMul_vecMul, g.inv_mul, Matrix.vecMul_one] using hx

/-- The finite adelic stabilizer is the image of the units of its row endomorphism order. -/
theorem range_unitsMap_adelicPolarizationOrder (c : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    (Units.map (adelicPolarizationOrder c).subtype.toMonoidHom).range =
      adelicPolarizationStabilizer c := by
  ext g
  constructor
  · rintro ⟨u, rfl⟩
    exact ⟨u.val.property, u.inv.property⟩
  · intro hg
    refine ⟨(adelicPolarizationOrder c).toSubmonoid.unitsEquivUnitsType ⟨g, hg⟩, ?_⟩
    rfl

/-- A matrix in `GL₂(A_f)` stabilizes the lattice precisely when it belongs to the row order
and its determinant is an everywhere integral unit. -/
theorem mem_adelicPolarizationStabilizer_iff_order_and_det
    {c : (FractionalIdeal (𝓞 K)⁰ K)ˣ}
    {g : Matrix.GeneralLinearGroup (Fin 2) 𝔸ᶠ[𝓞 K, K]} :
    g ∈ adelicPolarizationStabilizer c ↔
      (g : Matrix (Fin 2) (Fin 2) 𝔸ᶠ[𝓞 K, K]) ∈ adelicPolarizationOrder c ∧
      Matrix.GeneralLinearGroup.det g ∈ integralUnits (𝓞 K) K := by
  constructor
  · rintro ⟨hg, hgi⟩
    refine ⟨hg, ?_⟩
    rw [integralUnits_eq_units_integralAdeles, Submonoid.mem_units_iff]
    exact ⟨det_mem_integralAdeles_of_mem_adelicPolarizationOrder hg,
      det_mem_integralAdeles_of_mem_adelicPolarizationOrder hgi⟩
  · rintro ⟨hg, hd⟩
    refine ⟨hg, ?_⟩
    have hdinv : (↑(Matrix.GeneralLinearGroup.det g)⁻¹ : 𝔸ᶠ[𝓞 K, K]) ∈
        integralAdeles (𝓞 K) K := by
      rw [integralUnits_eq_units_integralAdeles, Submonoid.mem_units_iff] at hd
      exact hd.2
    have hinv : (↑g⁻¹ : Matrix (Fin 2) (Fin 2) 𝔸ᶠ[𝓞 K, K]) =
        (↑(Matrix.GeneralLinearGroup.det g)⁻¹ : 𝔸ᶠ[𝓞 K, K]) •
          (g : Matrix (Fin 2) (Fin 2) 𝔸ᶠ[𝓞 K, K]).adjugate := by
      rw [Matrix.coe_units_inv, Matrix.inv_def,
        ← Matrix.GeneralLinearGroup.val_det_apply, Ring.inverse_unit]
    intro x hx
    rw [Units.coeHom_apply, hinv, Matrix.vecMul_smul]
    simpa only [Subalgebra.smul_def] using (adelicPolarizationLattice c).smul_mem
      ⟨_, hdinv⟩ (adjugate_mem_adelicPolarizationOrder hg x hx)

/-- The explicit entry-ideal and determinant-unit description of the finite adelic row
stabilizer. -/
theorem mem_adelicPolarizationStabilizer_iff_entries
    {c : (FractionalIdeal (𝓞 K)⁰ K)ˣ}
    {g : Matrix.GeneralLinearGroup (Fin 2) 𝔸ᶠ[𝓞 K, K]} :
    g ∈ adelicPolarizationStabilizer c ↔
      g 0 0 ∈ integralAdeles (𝓞 K) K ∧
      g 0 1 ∈ finiteAdelicIdeal (polarizationCoordinateIdeal c) ∧
      g 1 0 ∈ finiteAdelicIdeal (polarizationCoordinateIdeal c)⁻¹ ∧
      g 1 1 ∈ integralAdeles (𝓞 K) K ∧
      Matrix.GeneralLinearGroup.det g ∈ integralUnits (𝓞 K) K := by
  simp only [mem_adelicPolarizationStabilizer_iff_order_and_det,
    mem_adelicPolarizationOrder_iff, and_assoc]

end TauCeti.HilbertModular
