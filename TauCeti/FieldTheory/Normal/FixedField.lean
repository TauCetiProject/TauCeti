/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.Galois.Basic
public import Mathlib.FieldTheory.Minpoly.IsConjRoot
public import Mathlib.FieldTheory.PurelyInseparable.Basic

/-!
# The fixed field of the automorphism group of a normal extension

For a normal extension `E / F`, the fixed field `E ^ Aut(E/F)` sits between `F` and `E` with
`F ⊆ E ^ Aut(E/F)` purely inseparable and `E ^ Aut(E/F) ⊆ E` Galois. This is the splitting of
Stacks, Fields, Lemma 9.27.3(2), whose proof reads "We set `E_insep = E^{Aut(E/F)}`. Details
omitted." Mathlib has the Galois half as `IsGalois.of_fixed_field`; the purely inseparable half
is new here. The two are stated separately, one conclusion each.

Order matters for the consumer (`TauCeti.Ring.IsJapanese.of_isPurelyInseparable`):
the purely inseparable step has to sit *below* the separable one, because the integral closure
of a polynomial ring in a separable extension is no longer a polynomial ring.

## Main results

* `TauCeti.IntermediateField.isPurelyInseparable_fixedField_top`: for `E / F` normal, the fixed
  field of `Gal(E/F)` is purely inseparable over `F`.

## Provenance

The mathematics is Stacks, Fields, Lemma 9.27.3(2) (tag 030M), the splitting used by Stacks
10.161.12 (tag 032N) in its normalization-finiteness argument.
-/

public section

namespace TauCeti

/-- Source: Stacks, Fields, Lemma 9.27.3(2): "`F ⊂ E_insep` is purely inseparable", with
`E_insep = E^{Aut(E/F)}` (proof: "Details omitted"). For a normal extension `E / F`, the fixed
field of the full automorphism group is purely inseparable over `F`. -/
theorem IntermediateField.isPurelyInseparable_fixedField_top (F E : Type*) [Field F] [Field E]
    [Algebra F E] [Normal F E] :
    IsPurelyInseparable F (IntermediateField.fixedField (⊤ : Subgroup Gal(E/F))) := by
  refine ⟨inferInstance, fun x hx ↦ ?_⟩
  have hsep : IsSeparable F (x : E) := hx.map (IsScalarTower.toAlgHom F _ E) (RingHom.injective _)
  -- Every conjugate of `x` is `σ x` for some automorphism `σ`, which fixes `x`; so `x` has no
  -- conjugate besides itself, and being separable it lies in `F`.
  have hbot : (x : E) ∈ (⊥ : Subalgebra F E) := by
    by_contra h
    obtain ⟨y, hne, hy⟩ :=
      (notMem_iff_exists_ne_and_isConjRoot hsep (Normal.splits ‹_› _)).mp h
    obtain ⟨σ, rfl⟩ := hy.symm.exists_algEquiv
    exact hne (x.2 ⟨σ, Subgroup.mem_top σ⟩).symm
  obtain ⟨a, ha⟩ := Algebra.mem_bot.mp hbot
  exact ⟨a, Subtype.ext <| (IntermediateField.coe_algebraMap_apply _ a).trans ha⟩

end TauCeti
