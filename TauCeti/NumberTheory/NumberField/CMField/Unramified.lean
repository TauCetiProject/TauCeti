/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.NumberField.CMField
public import Mathlib.RingTheory.Unramified.Locus
import TauCeti.NumberTheory.NumberField.CMField.Basic
import TauCeti.NumberTheory.NumberField.CMField.ResidueField
import TauCeti.NumberTheory.NumberField.Frobenius.DecompositionGroup

/-!
# Ramification of a CM field over its maximal real subfield

Let `K` be a CM field with maximal real subfield `K⁺` and complex conjugation `x ↦ conj x`. The
Galois group of `K / K⁺` is `{1, conj}`, so `K / K⁺` is unramified at a prime `w` of `𝓞 K` exactly
when `conj` is not in the inertia group of `w`, that is when `conj x - x ∉ w` for some `x ∈ 𝓞 K`
(`NumberField.IsCMField.isUnramifiedAt_iff_exists_sub_notMem`). This holds at every prime not fixed
by conjugation (`NumberField.IsCMField.exists_sub_notMem_of_map_ne`), since the inertia group lies
in the decomposition group.

When `K` contains a primitive fourth and a primitive seventh root of unity, for instance a
primitive `5040`-th root of unity, conjugation acts nontrivially on the residue field of every
prime it fixes (`NumberField.IsCMField.two_notMem_and_exists_sub_notMem_of_isPrimitiveRoot`).
So then `K / K⁺` is unramified at every finite place
(`NumberField.IsCMField.isUnramifiedAt_of_isPrimitiveRoot`). This is what makes every unit of a
completion of `K⁺` a local norm from `K`.

## Main results

* `NumberField.IsCMField.isUnramifiedAt_iff_exists_sub_notMem`: `K / K⁺` is unramified at `w`
  exactly when conjugation moves some integer modulo `w`.
* `NumberField.IsCMField.exists_sub_notMem_of_map_ne`: conjugation moves some integer modulo every
  prime that it does not fix.
* `NumberField.IsCMField.isUnramifiedAt_of_isPrimitiveRoot`: a CM field containing a primitive
  fourth and a primitive seventh root of unity is unramified over `K⁺` at every finite place.
-/

public section

open NumberField

namespace NumberField.IsCMField

variable {K : Type*} [Field K] [NumberField K] [IsCMField K]

local notation3 "K⁺" => maximalRealSubfield K

/-- **Unramifiedness of a CM field over `K⁺`.** A CM field `K` is unramified over its maximal real
subfield at a prime `w` of `𝓞 K` exactly when complex conjugation moves some integer modulo `w`:
`conj x - x ∉ w` for some `x ∈ 𝓞 K`. -/
theorem isUnramifiedAt_iff_exists_sub_notMem (w : Ideal (𝓞 K)) [w.IsPrime] :
    Algebra.IsUnramifiedAt (𝓞 K⁺) w ↔ ∃ x, ringOfIntegersComplexConj K x - x ∉ w := by
  -- conjugation acts on `𝓞 K` by `ringOfIntegersComplexConj`
  have hconj (x : 𝓞 K) : complexConj K • x = ringOfIntegersComplexConj K x :=
    RingOfIntegers.ext (by simp)
  have hmem : complexConj K ∈ w.inertia (K ≃ₐ[K⁺] K) ↔
      ∀ x, ringOfIntegersComplexConj K x - x ∈ w := by
    simp only [Ideal.mem_inertia, hconj]
  rw [Ideal.isUnramifiedAt_iff_inertia_eq_bot (K := K⁺), Subgroup.eq_bot_iff_forall]
  refine ⟨fun h ↦ ?_, fun ⟨x, hx⟩ σ hσ ↦ ?_⟩
  · by_contra! hall
    exact complexConj_ne_one K (h _ (hmem.2 hall))
  · refine (eq_one_or_eq_complexConj σ).resolve_right ?_
    rintro rfl
    exact hx (hmem.1 hσ x)

/-- **Conjugation moves an integer modulo a prime it does not fix.** If complex conjugation does
not fix the ideal `w` of the ring of integers of a CM field, then `conj x - x ∉ w` for some
`x ∈ 𝓞 K`. -/
theorem exists_sub_notMem_of_map_ne {w : Ideal (𝓞 K)}
    (hw : w.map (ringOfIntegersComplexConj K) ≠ w) :
    ∃ x, ringOfIntegersComplexConj K x - x ∉ w := by
  by_contra! hall
  -- otherwise conjugation, moving every integer by an element of `w`, would map `w` into itself
  have hmem (x : 𝓞 K) (hx : x ∈ w) : ringOfIntegersComplexConj K x ∈ w := by
    simpa using w.add_mem (hall x) hx
  refine hw (le_antisymm (Ideal.map_le_iff_le_comap.2 hmem) fun x hx ↦ ?_)
  rw [← ringOfIntegersComplexConj_apply_apply K x]
  exact Ideal.mem_map_of_mem _ (hmem x hx)

/-- **A CM field with fourth and seventh roots of unity is unramified over `K⁺`.** If the CM field
`K` contains a primitive fourth and a primitive seventh root of unity, for instance a primitive
`5040`-th root of unity, then `K / K⁺` is unramified at every prime of `𝓞 K`. -/
theorem isUnramifiedAt_of_isPrimitiveRoot {ζ₄ ζ₇ : K} (h₄ : IsPrimitiveRoot ζ₄ 4)
    (h₇ : IsPrimitiveRoot ζ₇ 7) (w : Ideal (𝓞 K)) [w.IsPrime] :
    Algebra.IsUnramifiedAt (𝓞 K⁺) w := by
  rw [isUnramifiedAt_iff_exists_sub_notMem]
  by_cases hw : w.map (ringOfIntegersComplexConj K) = w
  · exact (two_notMem_and_exists_sub_notMem_of_isPrimitiveRoot h₄ h₇ w hw).2
  · exact exists_sub_notMem_of_map_ne hw

end NumberField.IsCMField
