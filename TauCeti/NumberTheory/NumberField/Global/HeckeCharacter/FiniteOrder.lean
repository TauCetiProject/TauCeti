/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.NumberField.Global.HeckeCharacter.Basic

import Mathlib.RingTheory.RootsOfUnity.Complex
import Mathlib.RingTheory.RootsOfUnity.Basic

/-!
# Finite-order Hecke characters

A finite-order Hecke character is locally constant: its kernel is an open subgroup of the idele
class group.  This is the topological half of the Layer 9 equivalence between finite order, open
kernel, and factorization through a ray class group.

The proof uses only the finite-order hypothesis.  If `χ ^ n = 1`, every value of `χ` belongs to
the finite subgroup of `n`th roots of unity in `ℂˣ`.  A finite subset of the Hausdorff space `ℂˣ`
is discrete, so an open neighbourhood of `1` meeting those roots only at `1` pulls back to the
kernel of `χ`.

The remaining direction of the Layer 9 equivalence -- that an open kernel contains a ray subgroup
-- is deliberately not included here.  It is the separate adelic neighbourhood-basis step in
Layer 7; once supplied, it combines with this file and
`HeckeCharacter.mem_range_ofRayClassCharacter_iff` to give the named ray-class factorization.

## Main definitions

* `HeckeCharacter.IsFiniteOrder χ` is the assertion that `χ` has finite order in the group of
  Hecke characters.

## Main results

* `HeckeCharacter.isOpen_ker_of_isFiniteOrder`: a finite-order Hecke character has open kernel.
* `HeckeCharacter.isOpen_ker_ofRayClassCharacter`: in particular, a character pulled back from a
  ray class group has open kernel.

## References

* J. Neukirch, *Algebraic Number Theory*, Chapter VII, §6.
-/

public section
noncomputable section

open IsDedekindDomain NumberField Set
open scoped NumberField

namespace TauCeti.GlobalNumberFields

variable {K : Type*} [Field K] [NumberField K]

namespace HeckeCharacter

/-- A Hecke character has **finite order** when it has finite order as an element of the
commutative group of continuous idele-class characters. -/
abbrev IsFiniteOrder (χ : HeckeCharacter K) : Prop := IsOfFinOrder χ

/-- The image of a finite-order Hecke character lies in the corresponding finite group of roots
of unity. -/
private theorem range_subset_rootsOfUnity {χ : HeckeCharacter K} {n : ℕ}
    (hχ : χ ^ n = 1) :
    Set.range (χ : IdeleClassGroup (𝓞 K) K → ℂˣ) ⊆ rootsOfUnity n ℂ := by
  rintro _ ⟨c, rfl⟩
  change (χ c) ^ n = 1
  rw [← ContinuousMonoidHom.pow_apply χ n c, hχ]
  rfl

/-- **A finite-order Hecke character has open kernel.**  Its image is contained in a finite group
of roots of unity; isolating `1` within that finite discrete subgroup and pulling back its open
neighbourhood gives exactly the kernel. -/
theorem isOpen_ker_of_isFiniteOrder {χ : HeckeCharacter K} (hχ : χ.IsFiniteOrder) :
    IsOpen ((χ : IdeleClassGroup (𝓞 K) K →* ℂˣ).ker : Set (IdeleClassGroup (𝓞 K) K)) := by
  obtain ⟨n, hn, hχn⟩ := hχ.exists_pow_eq_one
  let _ : NeZero n := ⟨hn.ne'⟩
  have hroot : (1 : ℂˣ) ∈ rootsOfUnity n ℂ := by simp
  obtain ⟨U, hUopen, hU⟩ :=
    isOpen_inter_eq_singleton_of_mem_discrete
      (Set.Finite.isDiscrete <| inferInstanceAs (Finite (rootsOfUnity n ℂ))) hroot
  have hpreimage : χ ⁻¹' U = (χ : IdeleClassGroup (𝓞 K) K →* ℂˣ).ker := by
    ext c
    change χ c ∈ U ↔ χ c = 1
    constructor
    · intro hc
      have hcroot : χ c ∈ rootsOfUnity n ℂ :=
        range_subset_rootsOfUnity hχn (Set.mem_range_self c)
      have : χ c ∈ ({1} : Set ℂˣ) := by
        rw [← hU]
        exact ⟨hc, hcroot⟩
      simpa using this
    · intro hc
      have hUone : (1 : ℂˣ) ∈ U := by
        have : (1 : ℂˣ) ∈ U ∩ (rootsOfUnity n ℂ : Set ℂˣ) := by simp [hU]
        exact this.1
      rwa [hc]
  rw [← hpreimage]
  exact hUopen.preimage χ.continuous

/-- **A Hecke character pulled back from a ray class character has open kernel.** -/
theorem isOpen_ker_ofRayClassCharacter {𝔪 : Modulus K} (η : RayClassCharacter 𝔪) :
    IsOpen (((ofRayClassCharacter 𝔪 η : HeckeCharacter K) :
      IdeleClassGroup (𝓞 K) K →* ℂˣ).ker : Set (IdeleClassGroup (𝓞 K) K)) :=
  isOpen_ker_of_isFiniteOrder (isOfFinOrder_ofRayClassCharacter η)

end HeckeCharacter

end TauCeti.GlobalNumberFields
