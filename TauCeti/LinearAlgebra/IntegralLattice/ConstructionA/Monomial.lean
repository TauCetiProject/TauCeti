/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.IntegralLattice.ConstructionA.Naturality

/-!
# Monomial coordinate changes and Construction A

A monomial change of coordinates preserves the rational form used in Construction A exactly
when each of its coefficients is a sign. Thus a monomial code equivalence has a coordinatewise
isometric lift precisely when its coefficients modulo the modulus are reductions of signs.
The existing signed-coordinate isometry then supplies the lattice isometry.
-/

public section

namespace TauCeti.ConstructionA

variable {ι κ : Type*}

section

variable [Fintype ι] [Fintype κ]

/-- A rational monomial map preserves the Construction A form exactly when every multiplier is
a sign. This criterion is independent of the modulus. -/
theorem form_monomialEquiv_iff (m : ℕ+) (u : ι → ℚˣ) (e : ι ≃ κ) :
    (∀ x y : ι → ℚ, form m (monomialEquiv u e x) (monomialEquiv u e y) =
      form m x y) ↔ ∀ i, (u i : ℚ) ^ 2 = 1 := by
  constructor
  · intro h
    apply (dotProduct_monomialEquiv_iff u e).mp
    intro x y
    have hxy := h x y
    simp only [form_apply] at hxy
    exact (div_left_inj' (by exact_mod_cast m.ne_zero)).mp hxy
  · intro h x y
    simp only [form_apply]
    rw [(dotProduct_monomialEquiv_iff u e).mpr h x y]

/-- Rational monomial isometries are precisely signed coordinate changes. -/
theorem monomialEquiv_preserves_form_iff_exists_signed (m : ℕ+) (u : ι → ℚˣ)
    (e : ι ≃ κ) :
    (∀ x y : ι → ℚ, form m (monomialEquiv u e x) (monomialEquiv u e y) =
      form m x y) ↔
      ∃ v : ι → ℤˣ, monomialEquiv u e = signedEquiv v e := by
  rw [form_monomialEquiv_iff]
  rw [exists_signed_monomialEquiv_iff]
  constructor
  · intro hu i
    obtain h | h := (sq_eq_one_iff).mp (hu i)
    · exact Or.inl (Units.ext h)
    · exact Or.inr (Units.ext h)
  · intro hu i
    obtain h | h := hu i
    · simp [h]
    · simp [h]

end

variable {m : ℕ+}

/-- A modular monomial map acts on a Construction A carrier through a rational signed
coordinate change exactly when all its coefficients are signed residues. -/
theorem exists_signedEquiv_and_lattice_map_monomialEquiv_iff
    (C : AdditiveCode (ZMod m) ι) (u : ι → (ZMod m)ˣ) (e : ι ≃ κ) :
    (∃ v : ι → ℤˣ, monomialEquiv u e = signedEquiv v e ∧
      (lattice m C).map
          (((signedEquiv (R := ℚ) v e).toLinearMap).restrictScalars ℤ :
            (ι → ℚ) →ₗ[ℤ] (κ → ℚ)) =
        lattice m (C.map (monomialEquiv u e).toAddEquiv.toAddMonoidHom)) ↔
      ∀ i, u i = 1 ∨ u i = -1 := by
  constructor
  · rintro ⟨v, hv, _⟩
    exact (exists_signed_monomialEquiv_iff u e).mp ⟨v, hv⟩
  · intro hu
    obtain ⟨v, heq⟩ := (exists_signed_monomialEquiv_iff u e).mpr hu
    refine ⟨v, heq, ?_⟩
    rw [heq]
    exact lattice_map_signedEquiv C v e

section

variable [Fintype ι] [Fintype κ]

/-- A modular monomial map lifts to a signed isometry of the associated Construction A
integral lattices exactly when all its coefficients are signed residues. -/
theorem exists_signedEquiv_and_integralLatticeIsometry_iff (C : AdditiveCode (ZMod m) ι)
    (hC : AddSubgroup.toZModSubmodule m C ≤
      (AddSubgroup.toZModSubmodule m C).euclideanDual)
    (u : ι → (ZMod m)ˣ) (e : ι ≃ κ) :
    (∃ v : ι → ℤˣ, monomialEquiv u e = signedEquiv v e ∧
      ∃ hD : AddSubgroup.toZModSubmodule m
          (C.map (monomialEquiv u e).toAddEquiv.toAddMonoidHom) ≤
            (AddSubgroup.toZModSubmodule m
              (C.map (monomialEquiv u e).toAddEquiv.toAddMonoidHom)).euclideanDual,
        ∃ f : IntegralLattice.Isometry (integralLattice m C hC)
            (integralLattice m
              (C.map (monomialEquiv u e).toAddEquiv.toAddMonoidHom) hD),
          ∀ x : ι → ℚ, f x = signedEquiv v e x) ↔
      ∀ i, u i = 1 ∨ u i = -1 := by
  constructor
  · rintro ⟨v, hv, _⟩
    exact (exists_signed_monomialEquiv_iff u e).mp ⟨v, hv⟩
  · intro hu
    obtain ⟨v, hv⟩ := (exists_signed_monomialEquiv_iff u e).mpr hu
    refine ⟨v, hv, ?_⟩
    rw [hv]
    exact ⟨map_signedEquiv_le_euclideanDual C hC v e,
      integralLatticeSignedEquiv C hC v e,
      fun x ↦ integralLatticeSignedEquiv_apply C hC v e x⟩

end

end TauCeti.ConstructionA
