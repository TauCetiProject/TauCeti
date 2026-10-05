/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.IntegralLattice.ConstructionA.Basic
public import TauCeti.LinearAlgebra.IntegralLattice.Isometry.Basic
public import TauCeti.InformationTheory.Coding.Additive.Equivalence

/-!
# Coordinate changes in Construction A

Construction A is natural for relabellings of the coordinates and for changing signs of
coordinates.  This file packages these changes using units of the integers, whose only values are
`1` and `-1`.  The same signed coordinate change is used over the residue alphabet and over the
rational ambient space, so the isometry of lattices has an explicit coordinate formula.

The restriction to signs is essential: an arbitrary unit of `ZMod m` preserves Hamming data but
need not preserve the Euclidean form defining Construction A.

## References

* W. Ebeling, *Lattices and Codes*, §1.3.
* M. Harada, A. Munemasa, and B. Venkov, “Classification of ternary extremal self-dual codes of
  length 28”, §2.
-/

public section

namespace TauCeti.ConstructionA

open Matrix

variable {ι κ : Type*}

variable {m : ℕ+}

/-- Construction A commutes with a signed coordinate change.  The carrier equality is stated in
the common rational ambient space, and is the carrier part of the lattice isometry below. -/
@[simp]
theorem lattice_map_signedEquiv (C : AdditiveCode (ZMod m) ι) (u : ι → ℤˣ) (e : ι ≃ κ) :
    (lattice m C).map
        (((signedEquiv (R := ℚ) u e).toLinearMap).restrictScalars ℤ :
          (ι → ℚ) →ₗ[ℤ] (κ → ℚ)) =
      lattice m (C.map (signedEquiv (R := ZMod m) u e).toAddEquiv.toAddMonoidHom) := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    obtain ⟨z, hz, rfl⟩ := (mem_lattice m).mp hy
    rw [mem_lattice]
    refine ⟨signedEquiv (R := ℤ) u e z, ?_, ?_⟩
    · refine ⟨fun i ↦ (z i : ZMod m), hz, ?_⟩
      -- `AddSubgroup.map` is displayed through its additive homomorphism; use the corresponding
      -- linear-equivalence expression to apply the integer-cast compatibility lemma.
      change signedEquiv (R := ZMod m) u e (fun i ↦ (z i : ZMod m)) = _
      rw [← signedEquiv_intCast (R := ZMod m)]
    · ext j
      simp [signedEquiv_apply]
  · rw [mem_lattice]
    rintro ⟨z, hz, rfl⟩
    obtain ⟨w, hw, hwz⟩ := hz
    let v : ι → ℤ := (signedEquiv (R := ℤ) u e).symm z
    have hv : signedEquiv (R := ZMod m) u e (fun i ↦ (v i : ZMod m)) =
        fun j ↦ (z j : ZMod m) := by
      rw [signedEquiv_intCast (R := ZMod m)]
      exact congrArg (fun a j ↦ (a j : ZMod m))
        ((signedEquiv (R := ℤ) u e).apply_symm_apply z)
    have hcv : (fun i ↦ (v i : ZMod m)) = w :=
      (signedEquiv (R := ZMod m) u e).injective (hv.trans hwz.symm)
    refine ⟨fun i ↦ (v i : ℚ), (intCast_mem_lattice m v).mpr (by simpa [hcv] using hw), ?_⟩
    ext j
    simp only [LinearMap.coe_restrictScalars, LinearEquiv.coe_coe, signedEquiv_apply]
    have h := congrFun ((signedEquiv (R := ℤ) u e).apply_symm_apply z) j
    rw [signedEquiv_apply] at h
    exact_mod_cast h

/-- Construction A commutes with relabelling the coordinates of an additive code. -/
@[simp]
theorem lattice_reindex (C : AdditiveCode (ZMod m) ι) (e : κ ≃ ι) :
    (lattice m C).map
        (((LinearEquiv.funCongrLeft ℚ ℚ e).toLinearMap).restrictScalars ℤ :
          (ι → ℚ) →ₗ[ℤ] (κ → ℚ)) =
      lattice m (AdditiveCode.reindex C e) := by
  rw [AdditiveCode.reindex_eq_map_funCongrLeft]
  simpa only [signedEquiv_one, Equiv.symm_symm] using
    lattice_map_signedEquiv C (1 : ι → ℤˣ) e.symm

section

variable [Fintype ι] [Fintype κ]

/-- A signed coordinate change preserves self-orthogonality of an additive code over `ZMod m`. -/
theorem map_signedEquiv_le_euclideanDual (C : AdditiveCode (ZMod m) ι)
    (hC : AddSubgroup.toZModSubmodule m C ≤ (AddSubgroup.toZModSubmodule m C).euclideanDual)
    (u : ι → ℤˣ) (e : ι ≃ κ) :
    AddSubgroup.toZModSubmodule m
        (C.map (signedEquiv (R := ZMod m) u e).toAddEquiv.toAddMonoidHom) ≤
      (AddSubgroup.toZModSubmodule m
        (C.map (signedEquiv (R := ZMod m) u e).toAddEquiv.toAddMonoidHom)).euclideanDual := by
  rw [← Submodule.isSelfOrthogonal_iff_le, Submodule.isSelfOrthogonal_iff] at hC ⊢
  rintro x hx y hy
  -- The orthogonality characterization exposes the `ZMod` submodule; map membership is carried
  -- by the original additive code, where its witnesses have the desired form.
  change x ∈ C.map (signedEquiv (R := ZMod m) u e).toAddEquiv.toAddMonoidHom at hx
  change y ∈ C.map (signedEquiv (R := ZMod m) u e).toAddEquiv.toAddMonoidHom at hy
  obtain ⟨a, ha, rfl⟩ := hx
  obtain ⟨b, hb, rfl⟩ := hy
  simpa only [signedEquiv_toAddMonoidHom_apply, dotProduct_signedEquiv] using hC a ha b hb

/-- Relabelling coordinates preserves self-orthogonality of an additive code over `ZMod m`. -/
theorem reindex_le_euclideanDual (C : AdditiveCode (ZMod m) ι)
    (hC : AddSubgroup.toZModSubmodule m C ≤ (AddSubgroup.toZModSubmodule m C).euclideanDual)
    (e : κ ≃ ι) :
    AddSubgroup.toZModSubmodule m (AdditiveCode.reindex C e) ≤
      (AddSubgroup.toZModSubmodule m (AdditiveCode.reindex C e)).euclideanDual := by
  rw [AdditiveCode.reindex_eq_map_funCongrLeft]
  simpa only [signedEquiv_one, Equiv.symm_symm] using
    map_signedEquiv_le_euclideanDual C hC (1 : ι → ℤˣ) e.symm

/-- The signed coordinate change is an isometry from the Construction A lattice of a code to the
lattice of the signed, reindexed code. -/
noncomputable def integralLatticeSignedEquiv (C : AdditiveCode (ZMod m) ι)
    (hC : AddSubgroup.toZModSubmodule m C ≤ (AddSubgroup.toZModSubmodule m C).euclideanDual)
    (u : ι → ℤˣ) (e : ι ≃ κ) :
    IntegralLattice.Isometry (integralLattice m C hC)
      (integralLattice m (C.map (signedEquiv (R := ZMod m) u e).toAddEquiv.toAddMonoidHom)
        (map_signedEquiv_le_euclideanDual C hC u e)) where
  toIsometryEquiv :=
    { toLinearEquiv := signedEquiv (R := ℚ) u e
      map_app' := by
        intro x y
        rw [integralLattice_form, integralLattice_form]
        -- `IsometryEquiv` displays its map through a linear map; this gives the exact spelling
        -- used by the dot-product lemma rather than unfolding the signed coordinate map.
        change form m ((signedEquiv (R := ℚ) u e).toLinearMap x)
          ((signedEquiv (R := ℚ) u e).toLinearMap y) = form m x y
        rw [form_apply, form_apply]
        have hdot : (signedEquiv (R := ℚ) u e).toLinearMap x ⬝ᵥ
            (signedEquiv (R := ℚ) u e).toLinearMap y = x ⬝ᵥ y := by
          simpa only [LinearEquiv.coe_toLinearMap] using dotProduct_signedEquiv u e x y
        exact congrArg (fun a : ℚ ↦ a / (m : ℚ)) hdot }
  map_carrier := by
    rw [integralLattice_carrier, integralLattice_carrier]
    exact lattice_map_signedEquiv C u e

/-- The Construction A signed-coordinate isometry acts by the same signed permutation on
rational vectors. -/
@[simp]
theorem integralLatticeSignedEquiv_apply (C : AdditiveCode (ZMod m) ι)
    (hC : AddSubgroup.toZModSubmodule m C ≤ (AddSubgroup.toZModSubmodule m C).euclideanDual)
    (u : ι → ℤˣ) (e : ι ≃ κ) (x : ι → ℚ) :
    integralLatticeSignedEquiv C hC u e x = signedEquiv u e x := by
  rfl

/-- Relabelling coordinates induces an isometry between the corresponding Construction A
lattices. -/
noncomputable def integralLatticeReindexEquiv (C : AdditiveCode (ZMod m) ι)
    (hC : AddSubgroup.toZModSubmodule m C ≤ (AddSubgroup.toZModSubmodule m C).euclideanDual)
    (e : κ ≃ ι) :
    IntegralLattice.Isometry (integralLattice m C hC)
      (integralLattice m (AdditiveCode.reindex C e) (reindex_le_euclideanDual C hC e)) where
  toIsometryEquiv :=
    { toLinearEquiv := LinearEquiv.funCongrLeft ℚ ℚ e
      map_app' := by
        intro x y
        rw [integralLattice_form, integralLattice_form, form_apply, form_apply]
        -- The isometry field displays the relabelling through its linear map; expose its
        -- pointwise precomposition action to apply dot-product invariance.
        change ((x ∘ e) ⬝ᵥ (y ∘ e)) / (m : ℚ) = (x ⬝ᵥ y) / (m : ℚ)
        rw [comp_equiv_dotProduct_comp_equiv] }
  map_carrier := by
    rw [integralLattice_carrier, integralLattice_carrier]
    exact lattice_reindex C e

/-- The Construction A reindexing isometry acts by precomposition with the coordinate
equivalence. -/
@[simp]
theorem integralLatticeReindexEquiv_apply (C : AdditiveCode (ZMod m) ι)
    (hC : AddSubgroup.toZModSubmodule m C ≤ (AddSubgroup.toZModSubmodule m C).euclideanDual)
    (e : κ ≃ ι) (x : ι → ℚ) :
    integralLatticeReindexEquiv C hC e x = x ∘ e := by
  rfl

end

end TauCeti.ConstructionA
