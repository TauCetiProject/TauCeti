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
import TauCeti.GroupTheory.Index.DomRestrict
import TauCeti.LinearAlgebra.FreeModule.Int

/-!
# The twist index of a square-zero torus

In Taubes's count of embedded pseudoholomorphic curves in a symplectic four-manifold, a
square-zero torus `C` enters with a label `(σ, i)` read off from its normal operator twisted by
the real flat sign lines of `C`. These lines are the homomorphisms `χ : Λ → ℤ/2` from the lattice
`Λ = H₁(C; ℤ)`, the *sign characters* of `C`, with `χ = 0` the trivial line. Given the
determinant sign `s χ` of the normal operator twisted by each `χ`, the label has `σ = s 0`, and
`i` is the number of nonzero sign characters with negative sign (`TauCeti.twistIndex`).

This file proves the structural facts about the sign characters on which that label rests.

* **Change of trivialization.** An isomorphism `Λ ≃ Λ'` of lattices transports sign characters and
  preserves the twist index (`TauCeti.twistIndex_comp_addMonoidHomCongrLeft`). Reversing the
  orientation of `C` acts on `Λ` by `-1`, which fixes every sign character since `-1 = 1` in
  `ℤ/2`.
* **Four sign characters.** A torus has `H₁ ≅ ℤ²`, hence four sign characters
  (`TauCeti.natCard_addMonoidHom_zmod_two_of_finrank_eq_two`). For any nonzero `ι` and any `χ`
  other than `0` and `ι`, these are `0`, `ι`, `χ` and `χ + ι`
  (`TauCeti.eq_zero_or_eq_or_eq_or_eq_add_of_finrank_eq_two`), so the twist index is
  `[s ι < 0] + [s χ < 0] + [s (χ + ι) < 0]` (`TauCeti.twistIndex_eq_of_finrank_eq_two`) and is at
  most `3` (`TauCeti.twistIndex_le_three`).
* **Pullback to the double cover.** A nonzero sign character `ι` defines a connected double cover
  of `C`, whose `H₁` is the kernel of `ι`. Pulling sign characters back to it is restriction to
  `ker ι`. It kills exactly `0` and `ι` (`AddMonoidHom.domRestrict_ker_eq_zero_iff_zmod_two`),
  and the other two sign characters `χ` and `χ + ι` restrict to one and the same nonzero character
  of the cover (`AddMonoidHom.domRestrict_ker_add_self`,
  `TauCeti.setOf_domRestrict_ker_ne_zero_eq_of_finrank_eq_two`). Covers of odd degree pull sign
  characters back bijectively (`AddMonoidHom.bijective_domRestrictHom_zmod_of_coprime`).

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
theorem twistIndex_comp_addMonoidHomCongrLeft (e : Λ ≃+ Λ') (s : (Λ' →+ ZMod 2) → SignType) :
    twistIndex (s ∘ e.addMonoidHomCongrLeft) = twistIndex s := by
  rw [twistIndex_def, twistIndex_def]
  exact Nat.card_congr (e.addMonoidHomCongrLeft.toEquiv.subtypeEquiv fun χ ↦ by
    simp only [Function.comp_apply, ne_eq, AddEquiv.toEquiv_eq_coe, EquivLike.coe_coe,
      EmbeddingLike.map_eq_zero_iff])

/-- A lattice of rank two, such as `H₁` of a torus, has four sign characters. -/
theorem natCard_addMonoidHom_zmod_two_of_finrank_eq_two [Module.Free ℤ Λ] [Module.Finite ℤ Λ]
    (h : finrank ℤ Λ = 2) : Nat.card (Λ →+ ZMod 2) = 4 := by
  rw [natCard_addMonoidHom_eq_pow_finrank, h, Nat.card_zmod]
  norm_num

/-- On a lattice of rank two, the sign characters are `0`, `ι`, `χ` and `χ + ι` for a nonzero `ι`
and a `χ` other than `0` and `ι`. -/
private theorem univ_eq_of_finrank_eq_two [Module.Free ℤ Λ] [Module.Finite ℤ Λ]
    [Fintype (Λ →+ ZMod 2)] [DecidableEq (Λ →+ ZMod 2)] (h : finrank ℤ Λ = 2)
    {ι χ : Λ →+ ZMod 2} (hι : ι ≠ 0) (hχ₀ : χ ≠ 0) (hχι : χ ≠ ι) :
    (Finset.univ : Finset (Λ →+ ZMod 2)) = {0, ι, χ, χ + ι} := by
  have hadd₀ : χ + ι ≠ 0 := fun h' ↦ hχι (sub_eq_zero.1 ((ZModModule.sub_eq_add χ ι).trans h'))
  have haddι : χ + ι ≠ ι := fun h' ↦ hχ₀ (by simpa using h')
  have haddχ : χ + ι ≠ χ := fun h' ↦ hι (by simpa using h')
  refine (Finset.eq_univ_of_card _ ?_).symm
  rw [Finset.card_insert_of_notMem (by simp [hι.symm, hχ₀.symm, hadd₀.symm]),
    Finset.card_insert_of_notMem (by simp [hχι.symm, haddι.symm]),
    Finset.card_pair haddχ.symm, ← Nat.card_eq_fintype_card,
    natCard_addMonoidHom_zmod_two_of_finrank_eq_two h]

/-- **The four sign characters of a torus.** On a lattice of rank two, if `ι` is a nonzero sign
character and `χ` is neither `0` nor `ι`, every sign character is `0`, `ι`, `χ` or `χ + ι`. -/
theorem eq_zero_or_eq_or_eq_or_eq_add_of_finrank_eq_two [Module.Free ℤ Λ] [Module.Finite ℤ Λ]
    (h : finrank ℤ Λ = 2) {ι χ : Λ →+ ZMod 2} (hι : ι ≠ 0) (hχ₀ : χ ≠ 0) (hχι : χ ≠ ι)
    (ψ : Λ →+ ZMod 2) : ψ = 0 ∨ ψ = ι ∨ ψ = χ ∨ ψ = χ + ι := by
  classical
  have : Finite (Λ →+ ZMod 2) := Nat.finite_of_card_ne_zero
    (by rw [natCard_addMonoidHom_zmod_two_of_finrank_eq_two h]; norm_num)
  let _ := Fintype.ofFinite (Λ →+ ZMod 2)
  have hψ := Finset.mem_univ ψ
  rw [univ_eq_of_finrank_eq_two h hι hχ₀ hχι] at hψ
  simpa using hψ

/-- **The twist index of a torus.** On a lattice of rank two, if `ι` is a nonzero sign character
and `χ` is neither `0` nor `ι`, the three nonzero sign characters are `ι`, `χ` and `χ + ι`, so
the twist index counts the negative signs among `s ι`, `s χ` and `s (χ + ι)`. -/
theorem twistIndex_eq_of_finrank_eq_two [Module.Free ℤ Λ] [Module.Finite ℤ Λ]
    (h : finrank ℤ Λ = 2) {ι χ : Λ →+ ZMod 2} (hι : ι ≠ 0) (hχ₀ : χ ≠ 0) (hχι : χ ≠ ι)
    (s : (Λ →+ ZMod 2) → SignType) :
    twistIndex s = (if s ι = -1 then 1 else 0) + (if s χ = -1 then 1 else 0) +
      (if s (χ + ι) = -1 then 1 else 0) := by
  classical
  have : Finite (Λ →+ ZMod 2) := Nat.finite_of_card_ne_zero
    (by rw [natCard_addMonoidHom_zmod_two_of_finrank_eq_two h]; norm_num)
  let _ := Fintype.ofFinite (Λ →+ ZMod 2)
  have hadd₀ : χ + ι ≠ 0 := fun h' ↦ hχι (sub_eq_zero.1 ((ZModModule.sub_eq_add χ ι).trans h'))
  have haddι : χ + ι ≠ ι := fun h' ↦ hχ₀ (by simpa using h')
  have haddχ : χ + ι ≠ χ := fun h' ↦ hι (by simpa using h')
  rw [twistIndex_def, Nat.card_eq_fintype_card, Fintype.card_subtype, Finset.card_filter,
    univ_eq_of_finrank_eq_two h hι hχ₀ hχι,
    Finset.sum_insert (by simp [hι.symm, hχ₀.symm, hadd₀.symm]),
    Finset.sum_insert (by simp [hχι.symm, haddι.symm]), Finset.sum_pair haddχ.symm]
  simp [hι, hχ₀, hadd₀, add_assoc]

/-- A lattice of rank two has twist index at most `3`, so the label `(σ, i)` of a torus has
`i ∈ {0, 1, 2, 3}`. -/
theorem twistIndex_le_three [Module.Free ℤ Λ] [Module.Finite ℤ Λ] (h : finrank ℤ Λ = 2)
    (s : (Λ →+ ZMod 2) → SignType) : twistIndex s ≤ 3 := by
  classical
  have hcard := natCard_addMonoidHom_zmod_two_of_finrank_eq_two h
  have : Finite (Λ →+ ZMod 2) := Nat.finite_of_card_ne_zero (by rw [hcard]; norm_num)
  let _ := Fintype.ofFinite (Λ →+ ZMod 2)
  rw [twistIndex_def, Nat.card_eq_fintype_card, Fintype.card_subtype]
  calc _ ≤ (Finset.univ.erase (0 : Λ →+ ZMod 2)).card :=
        Finset.card_le_card fun χ hχ ↦ by simpa using (Finset.mem_filter.1 hχ).2.1
    _ = 3 := by
      rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ,
        ← Nat.card_eq_fintype_card, hcard]

/-- **Pullback to the double cover.** On a lattice of rank two, let `ι` be a nonzero sign
character and `χ` a sign character that does not vanish on the double cover `ker ι`. Then the
sign characters that do not vanish on `ker ι` are exactly `χ` and `χ + ι`, which have the same
pullback by `AddMonoidHom.domRestrict_ker_add_self`. -/
theorem setOf_domRestrict_ker_ne_zero_eq_of_finrank_eq_two [Module.Free ℤ Λ] [Module.Finite ℤ Λ]
    (h : finrank ℤ Λ = 2) {ι χ : Λ →+ ZMod 2} (hι : ι ≠ 0) (hχ : χ.domRestrict ι.ker ≠ 0) :
    {ψ : Λ →+ ZMod 2 | ψ.domRestrict ι.ker ≠ 0} = {χ, χ + ι} := by
  obtain ⟨hχ₀, hχι⟩ : χ ≠ 0 ∧ χ ≠ ι := by
    simpa [not_or] using (AddMonoidHom.domRestrict_ker_eq_zero_iff_zmod_two hι).not.1 hχ
  have hadd₀ : χ + ι ≠ 0 := fun h' ↦ hχι (sub_eq_zero.1 ((ZModModule.sub_eq_add χ ι).trans h'))
  have haddι : χ + ι ≠ ι := fun h' ↦ hχ₀ (by simpa using h')
  ext ψ
  rcases eq_zero_or_eq_or_eq_or_eq_add_of_finrank_eq_two h hι hχ₀ hχι ψ with
    rfl | rfl | rfl | rfl <;>
    simp [AddMonoidHom.domRestrict_ker_eq_zero_iff_zmod_two hι, hι, hχ₀, hχι, hadd₀, haddι,
      hχ₀.symm, hχι.symm, hadd₀.symm, haddι.symm]

end TauCeti
