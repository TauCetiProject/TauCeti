/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.NumberTheory.NumberField.Discriminant.RamifiedSupport.Basic
public import TauCeti.RingTheory.DedekindDomain.PrimesAbove
import Mathlib.NumberTheory.NumberField.ClassNumber
public import TauCeti.RingTheory.ClassGroup.HeightOneSpectrum

/-!
# Finite sets of places for the `S`-idele sequence

For an extension `L/K` of number fields, there is a finite set `S` of finite places of `K`
containing all ramified places such that the primes of `L` above `S` generate the class group
of `L`. The first condition permits local computations outside `S` using unramified units;
the second makes every idele class of `L` have an `S`-idele representative. Together they
allow the exact sequence of `S`-units, `S`-ideles and idele classes to be used without an
extra existence hypothesis on `S`.

The construction uses the finite prime generators of
`ClassGroup.exists_finite_closure_classGroupMk_image_eq_top` and the finite ramified support
`TauCeti.NumberField.ramifiedSupport`.

## References

* J. S. Milne, *Class Field Theory*, Chapter VII, §4, proof of Theorem 4.3.
-/

public section

open IsDedekindDomain NumberField

namespace TauCeti.GlobalNumberFields

variable (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

/-- An extension of number fields has a finite set of base places outside which it is
unramified and whose primes upstairs generate the class group. No Galois hypothesis is needed. -/
theorem exists_finset_primesAbove_closure_eq_top_and_isUnramified :
    ∃ S : Finset (HeightOneSpectrum (𝓞 K)),
      Subgroup.closure (HeightOneSpectrum.classGroupMk ''
        HeightOneSpectrum.primesAbove (𝓞 K) (𝓞 L) (S : Set _)) = ⊤ ∧
      ∀ w : HeightOneSpectrum (𝓞 L), w.under (𝓞 K) ∉ S →
        Algebra.IsUnramifiedAt (𝓞 K) w.asIdeal := by
  classical
  obtain ⟨T, hT, hgen⟩ := ClassGroup.exists_finite_closure_classGroupMk_image_eq_top
    (R := 𝓞 L)
  let S := (hT.image (HeightOneSpectrum.under (𝓞 K))).toFinset ∪
    TauCeti.NumberField.ramifiedSupport K L
  have hTS : T ⊆ HeightOneSpectrum.primesAbove (𝓞 K) (𝓞 L) (S : Set _) := by
    intro w hw
    rw [HeightOneSpectrum.mem_primesAbove_iff]
    exact Finset.mem_union_left _ ((hT.image _).mem_toFinset.mpr ⟨w, hw, rfl⟩)
  refine ⟨S, eq_top_iff.mpr (hgen ▸ Subgroup.closure_mono (Set.image_mono hTS)), ?_⟩
  intro w hw
  exact TauCeti.NumberField.isUnramifiedAway_ramifiedSupport (w.under (𝓞 K))
    (fun h ↦ hw (Finset.mem_union_right _ h)) w.asIdeal

end TauCeti.GlobalNumberFields
