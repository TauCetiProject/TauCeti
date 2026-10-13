/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.AbsoluteGaloisGroup
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.FieldTheory.Galois.Infinite
import Mathlib.NumberTheory.Cyclotomic.Basic
import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed
import TauCeti.FieldTheory.Galois.FixedField
import TauCeti.NumberTheory.Cyclotomic.Adjoin

/-!
# Subfields of `F(μ_m)` are cut out by their rational cyclotomic part

Let `F` be a field of characteristic zero and `M` a subfield of `F(μ_m)` inside the algebraic
closure `AlgebraicClosure F`. The number field `ℚ(μ_m) ∩ M` already determines `M`
Galois-theoretically: an element of the absolute Galois group `G_F` fixing `ℚ(μ_m) ∩ M` fixes
`M`, so `ℚ(μ_m) ∩ M` generates `M` over `F`. This lets a statement about a subfield of a local
cyclotomic extension `ℚ_p(μ_m)` be proved on a number field, as in the cyclotomic normalization of
the local Artin map.

The proof is Galois theory in the finite Galois extension `ℚ(μ_m) / ℚ`
(`IntermediateField.apply_eq_self_of_forall_mem_inf`), followed by the infinite Galois
correspondence for `AlgebraicClosure F / F`.

## Main results

* `TauCeti.apply_eq_self_of_forall_mem_adjoin_pow_eq_one`: an element of `G_F` fixing
  `ℚ(μ_m) ∩ M` fixes `M`.
* `TauCeti.le_adjoin_inf_of_le_adjoin_pow_eq_one`: `ℚ(μ_m) ∩ M` generates `M` over `F`.
-/

public section

namespace TauCeti

/-- **Reduction to `ℚ(μ_m)`.** Let `F` be a field of characteristic zero and `M` a subfield of
`F(μ_m)` inside `AlgebraicClosure F`. An element `σ ∈ G_F` that fixes `ℚ(μ_m) ∩ M` fixes `M`. -/
theorem apply_eq_self_of_forall_mem_adjoin_pow_eq_one {F : Type*} [Field F] [CharZero F] (m : ℕ)
    [NeZero m] {M : IntermediateField F (AlgebraicClosure F)}
    (hM : M ≤ IntermediateField.adjoin F {z : AlgebraicClosure F | z ^ m = 1})
    (σ : Field.absoluteGaloisGroup F)
    (hσ : ∀ x ∈ IntermediateField.adjoin ℚ {z : AlgebraicClosure F | z ^ m = 1}, x ∈ M →
      σ.toRingEquiv x = x)
    (x : M) : σ.toRingEquiv (x : AlgebraicClosure F) = x := by
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot (AlgebraicClosure F) m
  have := hζ.isCyclotomicExtension_adjoin_nth_roots (K := ℚ)
  have := IsCyclotomicExtension.finiteDimensional {m} ℚ
    (IntermediateField.adjoin ℚ {z : AlgebraicClosure F | z ^ m = 1})
  have := IsCyclotomicExtension.isGalois {m} ℚ
    (IntermediateField.adjoin ℚ {z : AlgebraicClosure F | z ^ m = 1})
  exact IntermediateField.apply_eq_self_of_forall_mem_inf _
    (hM.trans (IntermediateField.adjoin.mono _ _ _ (IntermediateField.subset_adjoin ℚ _)))
    (σ : AlgebraicClosure F ≃ₐ[F] AlgebraicClosure F) hσ x.2

/-- **`ℚ(μ_m) ∩ M` generates `M` over `F`**, for `F` a field of characteristic zero and `M` a
subfield of `F(μ_m)` inside `AlgebraicClosure F`: whatever in `G_F` fixes `ℚ(μ_m) ∩ M` fixes `M`. -/
theorem le_adjoin_inf_of_le_adjoin_pow_eq_one {F : Type*} [Field F] [CharZero F] (m : ℕ)
    [NeZero m] {M : IntermediateField F (AlgebraicClosure F)}
    (hM : M ≤ IntermediateField.adjoin F {z : AlgebraicClosure F | z ^ m = 1}) :
    M ≤ IntermediateField.adjoin F
      ((IntermediateField.adjoin ℚ {z : AlgebraicClosure F | z ^ m = 1} ⊓
        M.restrictScalars ℚ : IntermediateField ℚ (AlgebraicClosure F)) :
          Set (AlgebraicClosure F)) := by
  intro z hz
  rw [← InfiniteGalois.fixedField_fixingSubgroup (IntermediateField.adjoin F _)]
  rintro ⟨τ, hτ⟩
  rw [IntermediateField.mem_fixingSubgroup_iff] at hτ
  exact apply_eq_self_of_forall_mem_adjoin_pow_eq_one m hM τ
    (fun w hwE hwM ↦ hτ w (IntermediateField.subset_adjoin _ _ ⟨hwE, hwM⟩)) ⟨z, hz⟩

end TauCeti
