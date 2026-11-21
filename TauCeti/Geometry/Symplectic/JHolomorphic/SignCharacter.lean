/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Basic.Sign.Defs
public import Mathlib.Data.ZMod.Defs
public import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.Data.ZMod.Basic
import TauCeti.LinearAlgebra.FreeModule.Int

/-!
# The twist index of a square-zero torus

In Taubes's count of embedded pseudoholomorphic curves in a symplectic four-manifold, a
square-zero torus `C` enters with a label `(σ, i)` read off from its normal operator twisted by
the real flat sign lines of `C`. These lines are the homomorphisms `χ : Λ → ℤ/2` from the lattice
`Λ = H₁(C; ℤ)`, the *sign characters* of `C`, with `χ = 0` the trivial line. Given the
determinant sign `s χ` of the normal operator twisted by each `χ`, the label has `σ = s 0`, and
`i` is the number of nonzero sign characters with negative sign (`TauCeti.twistIndex`).

This file proves the twist-index facts below.

* **Change of trivialization.** An isomorphism `Λ ≃ Λ'` of lattices transports sign characters and
  preserves the twist index (`TauCeti.twistIndex_comp_addMonoidHomCongrLeft`). Reversing the
  orientation of `C` acts on `Λ` by `-1`, which fixes every sign character since `-1 = 1` in
  `ℤ/2`.
* **The twist index of a torus.** A torus has `H₁ ≅ ℤ²`, so for any nonzero `ι` and any `χ` other
  than `0` and `ι` its sign characters are `0`, `ι`, `χ` and `χ + ι`; this enumeration is proved in
  `TauCeti.LinearAlgebra.FreeModule.Int`. The twist index is therefore
  `[s ι < 0] + [s χ < 0] + [s (χ + ι) < 0]` (`TauCeti.twistIndex_eq_of_finrank_eq_two`) and is at
  most `3` (`TauCeti.twistIndex_le_three`). As an element of `Fin 4` it is the label
  `TauCeti.twistLabel`.

How sign characters pull back to finite covers of `C`, in particular to the double cover defined by
a nonzero sign character, is described in `TauCeti.GroupTheory.Index.DomRestrict`.

The signs `s χ` are inputs: their construction as oriented determinant signs of the twisted normal
operators is separate. The local series attached to the label are `TauCeti.torusWeightSeries`.

## References

* C. H. Taubes, *Counting pseudo-holomorphic submanifolds in dimension 4*, J. Differential Geom.
  **44** (1996), 818–893.
-/

public section

open Module

namespace TauCeti

variable {Λ Λ' : Type*} [AddCommGroup Λ] [AddCommGroup Λ']

/-- The **twist index** of an assignment `s` of signs to the sign characters `χ : Λ → ℤ/2`: the
number of nonzero sign characters `χ` with `s χ = -1`. For `Λ = H₁(C; ℤ)` of a square-zero torus
`C` and `s χ` the determinant sign of its normal operator twisted by `χ`, this is the index `i` of
the label `(σ, i)` of `C` in Taubes's weighted count. -/
noncomputable def twistIndex (s : (Λ →+ ZMod 2) → SignType) : ℕ :=
  Nat.card {χ : Λ →+ ZMod 2 // χ ≠ 0 ∧ s χ = -1}

theorem twistIndex_def (s : (Λ →+ ZMod 2) → SignType) :
    twistIndex s = Nat.card {χ : Λ →+ ZMod 2 // χ ≠ 0 ∧ s χ = -1} := (rfl)

/-- **Change of trivialization.** Transporting the sign characters along an isomorphism of
lattices `e : Λ ≃ Λ'` does not change the twist index. -/
@[simp]
theorem twistIndex_comp_addMonoidHomCongrLeft (e : Λ ≃+ Λ') (s : (Λ' →+ ZMod 2) → SignType) :
    twistIndex (s ∘ e.addMonoidHomCongrLeft) = twistIndex s := by
  rw [twistIndex_def, twistIndex_def]
  exact Nat.card_congr (e.addMonoidHomCongrLeft.toEquiv.subtypeEquiv fun χ ↦ by
    simp only [Function.comp_apply, ne_eq, AddEquiv.toEquiv_eq_coe, EquivLike.coe_coe,
      EmbeddingLike.map_eq_zero_iff])

/-- **The twist index of a torus.** On a lattice of rank two, if `ι` is a nonzero sign character
and `χ` is neither `0` nor `ι`, the three nonzero sign characters are `ι`, `χ` and `χ + ι`, so
the twist index counts the negative signs among `s ι`, `s χ` and `s (χ + ι)`. -/
theorem twistIndex_eq_of_finrank_eq_two [Module.Free ℤ Λ] [Module.Finite ℤ Λ]
    (h : finrank ℤ Λ = 2) {ι χ : Λ →+ ZMod 2} (hι : ι ≠ 0) (hχ₀ : χ ≠ 0) (hχι : χ ≠ ι)
    (s : (Λ →+ ZMod 2) → SignType) :
    twistIndex s = (if s ι = -1 then 1 else 0) + (if s χ = -1 then 1 else 0) +
      (if s (χ + ι) = -1 then 1 else 0) := by
  classical
  let _ := Fintype.ofFinite (Λ →+ ZMod 2)
  have := nodup_addMonoidHom_zmod_two hι hχ₀ hχι
  rw [twistIndex_def, Nat.card_eq_fintype_card, Fintype.card_subtype, Finset.card_filter,
    univ_addMonoidHom_zmod_two_eq_of_finrank_eq_two h hι hχ₀ hχι]
  simp_all [-Finset.sum_boole, Finset.sum_insert, eq_comm (a := (0 : Λ →+ ZMod 2)), add_assoc]

/-- A lattice of rank two has twist index at most `3`, so the label `(σ, i)` of a torus has
`i ∈ {0, 1, 2, 3}`. -/
theorem twistIndex_le_three [Module.Free ℤ Λ] [Module.Finite ℤ Λ] (h : finrank ℤ Λ = 2)
    (s : (Λ →+ ZMod 2) → SignType) : twistIndex s ≤ 3 := by
  classical
  let _ := Fintype.ofFinite (Λ →+ ZMod 2)
  rw [twistIndex_def, Nat.card_eq_fintype_card, Fintype.card_subtype]
  calc _ ≤ (Finset.univ.erase (0 : Λ →+ ZMod 2)).card :=
        Finset.card_le_card fun χ hχ ↦ by simpa using (Finset.mem_filter.1 hχ).2.1
    _ = 3 := by
      rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ,
        ← Nat.card_eq_fintype_card, natCard_addMonoidHom_zmod_two_of_finrank_eq_two h]

/-- The **twist label** `i ∈ Fin 4` of a torus: the twist index of the signs `s` on the sign
characters of a lattice of rank two, which is at most `3` by `TauCeti.twistIndex_le_three`. This
is the index of the local series `TauCeti.torusWeightSeries σ i` attached to the torus. -/
noncomputable def twistLabel [Module.Free ℤ Λ] [Module.Finite ℤ Λ] (h : finrank ℤ Λ = 2)
    (s : (Λ →+ ZMod 2) → SignType) : Fin 4 :=
  ⟨twistIndex s, Nat.lt_succ_of_le (twistIndex_le_three h s)⟩

@[simp]
theorem val_twistLabel [Module.Free ℤ Λ] [Module.Finite ℤ Λ] (h : finrank ℤ Λ = 2)
    (s : (Λ →+ ZMod 2) → SignType) :
    (twistLabel h s : ℕ) = twistIndex s := (rfl)

end TauCeti
