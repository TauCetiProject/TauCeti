/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.LocalField.Herbrand.CyclicReduction
public import TauCeti.NumberTheory.LocalField.Herbrand.HasseArf.CyclicPGroup
public import TauCeti.NumberTheory.LocalField.Herbrand.PPrimary

/-!
# The Hasse--Arf theorem

The Hasse--Arf theorem says that every upper ramification break of a finite abelian Galois
extension of nonarchimedean local fields is an integer.

The proof separates the elementary nonpositive breaks from the positive wild breaks. An upper
break of an abelian extension is detected in a cyclic subextension. A positive break of that
cyclic extension remains a break after quotienting out the prime-to-residue-characteristic part
of its Galois group. The resulting cyclic extension has prime-power degree, where integrality
follows from the norm-conductor form of Hasse--Arf.

## Main result

* `TauCeti.LocalFieldsRamification.hasseArf`: every upper ramification break of a finite abelian
  extension is integral.

## References

* [J.-P. Serre, *Corps Locaux*][serre1968], Chapter V, §7.
-/

public section
noncomputable section

open IntermediateField ValuativeRel

namespace TauCeti.LocalFieldsRamification

universe u v

variable (K : Type u) (L : Type v) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] [Field L] [ValuativeRel L] [TopologicalSpace L]
  [IsNonarchimedeanLocalField L] [Algebra K L] [ValuativeExtension K L]
  [Module.Finite K L] [IsAbelianGalois K L]

/-- **Hasse--Arf.** Every upper ramification break of a finite abelian Galois extension of
nonarchimedean local fields is an integer. -/
theorem hasseArf {w : RamificationIndexDomain} (hw : UpperJump K L w) :
    ∃ z : ℤ, (w : ℝ) = z := by
  by_cases hwpos : 0 < (w : ℝ)
  · obtain ⟨F, hFcyclic, hFjump, -⟩ :=
      (upperJump_iff_exists_isCyclic_intermediateField K L w).1 hw
    let _ := finiteIntermediateFieldValuativeRel K L F
    let _ := finiteIntermediateFieldTopology K L F
    have := finiteIntermediateField_isNonarchimedeanLocalField K L F
    have := finiteIntermediateField_valuativeExtension K L F
    let _ := hFcyclic
    let p := ringChar (IsLocalRing.ResidueField 𝒪[F])
    let _ : Fact p.Prime :=
      ⟨CharP.char_is_prime (IsLocalRing.ResidueField 𝒪[F]) p⟩
    obtain ⟨E, hE, hEcyclic, hpE, hEjump⟩ :=
      hFjump.exists_isPGroup_intermediateField_of_isCyclic_of_pos p hwpos
    let _ := finiteIntermediateFieldValuativeRel K F E
    let _ := finiteIntermediateFieldTopology K F E
    have := finiteIntermediateField_isNonarchimedeanLocalField K F E
    have := finiteIntermediateField_valuativeExtension K F E
    let _ := hE
    let _ := hEcyclic
    exact hEjump.exists_eq_intCast_of_isPGroup hpE
  · rcases hw.eq_neg_one_or_eq_zero_of_nonpos (not_lt.mp hwpos) with h | h
    · exact ⟨-1, by simpa using h⟩
    · exact ⟨0, by simpa using h⟩

end TauCeti.LocalFieldsRamification
