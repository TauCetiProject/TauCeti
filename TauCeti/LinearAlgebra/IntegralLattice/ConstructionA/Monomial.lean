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
  constructor
  · intro hu
    let v : ι → ℤˣ := fun i ↦ if (u i : ℚ) = 1 then 1 else -1
    refine ⟨v, LinearEquiv.ext fun x ↦ funext fun j ↦ ?_⟩
    obtain h | h := (sq_eq_one_iff).mp (hu (e.symm j))
    · have h' : u (e.symm j) = 1 := Units.ext h
      simp [monomialEquiv_apply, signedEquiv_apply, v, h']
    · have h' : u (e.symm j) = -1 := Units.ext h
      simp [monomialEquiv_apply, signedEquiv_apply, v, h']
  · rintro ⟨v, hv⟩ i
    exact (dotProduct_monomialEquiv_iff u e).mp (fun x y ↦ by
      rw [hv, dotProduct_signedEquiv]) i

end

variable {m : ℕ+}

/-- When the coefficients of a modular monomial map are signed residues, its action on a
Construction A carrier is the restriction of a rational signed coordinate change. -/
theorem exists_lattice_map_monomialEquiv (C : AdditiveCode (ZMod m) ι)
    (u : ι → (ZMod m)ˣ) (e : ι ≃ κ) (hu : ∀ i, u i = 1 ∨ u i = -1) :
    ∃ v : ι → ℤˣ, monomialEquiv u e = signedEquiv v e ∧
      (lattice m C).map
          (((signedEquiv (R := ℚ) v e).toLinearMap).restrictScalars ℤ :
            (ι → ℚ) →ₗ[ℤ] (κ → ℚ)) =
        lattice m (C.map (monomialEquiv u e).toAddEquiv.toAddMonoidHom) := by
  obtain ⟨v, heq⟩ := (exists_signed_monomialEquiv_iff u e).mpr hu
  refine ⟨v, heq, ?_⟩
  rw [heq]
  exact lattice_map_signedEquiv C v e

section

variable [Fintype ι] [Fintype κ]

/-- A modular monomial map with signed coefficients lifts to an isometry of the associated
Construction A integral lattices, with the prescribed signed action on rational coordinates. -/
theorem exists_integralLatticeIsometry_of_monomial (C : AdditiveCode (ZMod m) ι)
    (hC : AddSubgroup.toZModSubmodule m C ≤
      (AddSubgroup.toZModSubmodule m C).euclideanDual)
    (u : ι → (ZMod m)ˣ) (e : ι ≃ κ) (hu : ∀ i, u i = 1 ∨ u i = -1) :
    ∃ v : ι → ℤˣ, monomialEquiv u e = signedEquiv v e ∧
      ∃ hD : AddSubgroup.toZModSubmodule m
          (C.map (monomialEquiv u e).toAddEquiv.toAddMonoidHom) ≤
            (AddSubgroup.toZModSubmodule m
              (C.map (monomialEquiv u e).toAddEquiv.toAddMonoidHom)).euclideanDual,
        ∃ f : IntegralLattice.Isometry (integralLattice m C hC)
            (integralLattice m
              (C.map (monomialEquiv u e).toAddEquiv.toAddMonoidHom) hD),
          ∀ x : ι → ℚ, f x = signedEquiv v e x := by
  obtain ⟨v, hv⟩ := (exists_signed_monomialEquiv_iff u e).mpr hu
  refine ⟨v, hv, ?_⟩
  rw [hv]
  exact ⟨map_signedEquiv_le_euclideanDual C hC v e,
    integralLatticeSignedEquiv C hC v e,
    fun x ↦ integralLatticeSignedEquiv_apply C hC v e x⟩

end

end TauCeti.ConstructionA
