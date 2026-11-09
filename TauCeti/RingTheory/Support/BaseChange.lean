/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axel Delaval, Jie Xu, Shitan Xu
-/
module

public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
public import Mathlib.RingTheory.LocalRing.Module

/-!
# Annihilators of finite modules after scalar extension

If a finite module vanishes after scalar extension, its annihilator generates the unit
ideal in the new coefficient ring. The proof uses a residue field at a hypothetical
maximal ideal containing the extended annihilator.
-/

public section

open TensorProduct

/-- If the base change of a finite `A`-module `C` to an `A`-algebra `B` vanishes, then the
annihilator of `C` generates the unit ideal of `B`. -/
theorem Module.annihilator_map_eq_top_of_subsingleton_tensorProduct {A B C : Type*} [CommRing A]
    [CommRing B] [Algebra A B] [AddCommGroup C] [Module A C] [Module.Finite A C]
    [Subsingleton (B ⊗[A] C)] :
    (Module.annihilator A C).map (algebraMap A B) = ⊤ := by
  by_contra h
  obtain ⟨q, hq, hle⟩ := Ideal.exists_le_maximal _ h
  let p : PrimeSpectrum A := ⟨q.comap (algebraMap A B), inferInstance⟩
  have hp : p ∈ Module.support A C := by
    rw [Module.mem_support_iff_of_finite]
    exact Ideal.map_le_iff_le_comap.mp hle
  rw [Module.mem_support_iff_nontrivial_residueField_tensorProduct] at hp
  let := (Ideal.ResidueField.mapₐ p.asIdeal q (Algebra.ofId A B) rfl).toAlgebra
  have : IsScalarTower A p.asIdeal.ResidueField q.ResidueField := IsScalarTower.of_algHom _
  have : Module.FaithfullyFlat p.asIdeal.ResidueField q.ResidueField := inferInstance
  have : Nontrivial (q.ResidueField ⊗[A] C) :=
    (AlgebraTensorModule.cancelBaseChange A p.asIdeal.ResidueField q.ResidueField
      q.ResidueField C).symm.toEquiv.nontrivial
  exact not_subsingleton _ (AlgebraTensorModule.cancelBaseChange A B q.ResidueField
      q.ResidueField C).symm.toEquiv.subsingleton
