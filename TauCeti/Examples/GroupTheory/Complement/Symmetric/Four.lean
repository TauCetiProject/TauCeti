/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.Complement.CrossedProjection
public import TauCeti.GroupTheory.Perm.ParityRetract
import TauCeti.Algebra.Group.Subgroup.Pointwise

/-!
# Complements of `A₄` in `S₄` and non-abelian crossed projections

The alternating subgroup `A₄` of `S₄ = Equiv.Perm (Fin 4)` is normal of index `2`, but unlike `A₃`
in `S₃` (`TauCeti.Examples.SymmetricThree`) it is non-abelian
(`TauCeti.Examples.SymmetricFour.not_isMulCommutative_alternatingGroup`). This file works through
the non-commutative crossed-projection dictionary for `A₄ ◁ S₄`:

* **Transposition complements and parity retraction.** Every transposition generates a complement
  of `A₄` (`Equiv.Perm.IsSwap.isComplement'_alternatingGroup_zpowers`). Along `K = ⟨(0 1)⟩`, the
  crossed projection sends `σ` to `σ * parityRetract σ`, fixing `A₄` and killing `(0 1)`; it is not
  a homomorphism.
* **Factor order in the crossed identity.** The crossed identity
  `c (g * k) = g • c k * c g` holds on all of `S₄` without commutativity, and its `oneLocus`
  recovers `⟨(0 1)⟩`. By contrast, the reversed factor order `c (g * k) = c g * (g • c k)` fails on
  the non-commuting three-cycles `g = (0 1 2)` and `k = (0 1 3)` in `A₄`: their product has
  projection `(0 2)(1 3)`, whereas `c g * (g • c k)` is the distinct Klein-four involution
  `(0 1)(2 3)`. More generally, no complement of `A₄` in `S₄` satisfies the reversed identity
  (`TauCeti.Examples.SymmetricFour.not_forall_crossedProjection_mul_eq_reversed`).
* **Non-abelian inner conjugation.** Conjugating `⟨(0 1)⟩` by `a = (0 1 2) ∈ A₄` yields `⟨(1 2)⟩`,
  twisting the crossed projection `c` to `x ↦ x • a * c x * a⁻¹`. Because `A₄` is non-abelian, the
  abelian right-multiplied formula `x ↦ c x * (x • a * a⁻¹)` fails already at `x = (0 1 3)`.
* **Restriction.** Restricting `⟨(0 1)⟩` to `A₄` gives the trivial local complement `⊥`, whose left
  projection is the identity of `A₄`.
-/

public section

open Equiv groupCohomology
open scoped IsMulCommutative Pointwise

namespace TauCeti.Examples.SymmetricFour

attribute [local instance] Subgroup.conjugationAction

/-! ### Non-commutativity of `A₄` -/

/-- The three-cycle `(0 1 2) = (0 1) * (1 2)`, as an element of `A₄`. -/
def cycle012 : alternatingGroup (Fin 4) :=
  ⟨swap 0 1 * swap 1 2, by rw [Perm.mem_alternatingGroup]; decide⟩

/-- Coercion of `cycle012` to `Perm (Fin 4)`. -/
@[simp]
theorem coe_cycle012 : (cycle012 : Perm (Fin 4)) = swap 0 1 * swap 1 2 := (rfl)

/-- The three-cycle `(0 1 3) = (0 1) * (1 3)`, as an element of `A₄`. -/
def cycle013 : alternatingGroup (Fin 4) :=
  ⟨swap 0 1 * swap 1 3, by rw [Perm.mem_alternatingGroup]; decide⟩

/-- Coercion of `cycle013` to `Perm (Fin 4)`. -/
@[simp]
theorem coe_cycle013 : (cycle013 : Perm (Fin 4)) = swap 0 1 * swap 1 3 := (rfl)

/-- The three-cycles `(0 1 2)` and `(0 1 3)` in `A₄` do not commute. -/
theorem cycle012_mul_cycle013_ne : cycle012 * cycle013 ≠ cycle013 * cycle012 := by
  intro h
  have h' : (swap (0 : Fin 4) 1 * swap 1 2) * (swap 0 1 * swap 1 3) =
      (swap 0 1 * swap 1 3) * (swap 0 1 * swap 1 2) := congrArg Subtype.val h
  revert h'
  decide

/-- **`A₄` is not commutative.** -/
theorem not_isMulCommutative_alternatingGroup :
    ¬ IsMulCommutative (alternatingGroup (Fin 4)) := fun _ =>
  cycle012_mul_cycle013_ne (mul_comm cycle012 cycle013)

/-! ### Transposition complements and explicit crossed projection -/

/-- The transposition `(0 1)` of `Fin 4` is a swap. -/
theorem isSwap_swap_zero_one : (swap (0 : Fin 4) 1).IsSwap :=
  ⟨0, 1, by decide, rfl⟩

/-- The transposition `(1 2)` of `Fin 4` is a swap. -/
theorem isSwap_swap_one_two : (swap (1 : Fin 4) 2).IsSwap :=
  ⟨1, 2, by decide, rfl⟩

/-- The two-element subgroup `⟨(0 1)⟩` is a complement of `A₄` in `S₄`. -/
theorem isComplement'_zpowers_swap_zero_one :
    (alternatingGroup (Fin 4)).IsComplement' (Subgroup.zpowers (swap 0 1)) :=
  isSwap_swap_zero_one.isComplement'_alternatingGroup_zpowers

/-- The two-element subgroup `⟨(1 2)⟩` is a complement of `A₄` in `S₄`. -/
theorem isComplement'_zpowers_swap_one_two :
    (alternatingGroup (Fin 4)).IsComplement' (Subgroup.zpowers (swap 1 2)) :=
  isSwap_swap_one_two.isComplement'_alternatingGroup_zpowers

section CrossedProjection

variable
  (h₀₁ : (alternatingGroup (Fin 4)).IsComplement' (Subgroup.zpowers (swap 0 1)))
  (h₁₂ : (alternatingGroup (Fin 4)).IsComplement' (Subgroup.zpowers (swap 1 2)))

/-- Along `⟨(0 1)⟩`, the crossed projection sends `σ` to `σ * parityRetract σ`: it fixes even
permutations and multiplies odd permutations on the right by `(0 1)`. -/
theorem coe_crossedProjection_apply (σ : Perm (Fin 4)) :
    (h₀₁.crossedProjection σ : Perm (Fin 4)) =
      σ * Perm.parityRetract isSwap_swap_zero_one σ := by
  have hd : Perm.parityRetract isSwap_swap_zero_one σ ∈ Subgroup.zpowers (swap 0 1) := by
    rw [← Perm.range_parityRetract isSwap_swap_zero_one]
    exact ⟨σ, rfl⟩
  have hn : σ * (Perm.parityRetract isSwap_swap_zero_one σ)⁻¹ ∈ alternatingGroup (Fin 4) := by
    rw [Perm.inv_parityRetract]
    exact Perm.mul_parityRetract_mem_alternatingGroup isSwap_swap_zero_one σ
  rw [h₀₁.crossedProjection_eq_of_mul_inv_mem hd hn, Perm.inv_parityRetract]

/-- The crossed projection along `⟨(0 1)⟩` kills `(0 1)`. -/
theorem crossedProjection_swap_zero_one : h₀₁.crossedProjection (swap 0 1) = 1 :=
  h₀₁.crossedProjection_coe_right ⟨swap 0 1, Subgroup.mem_zpowers _⟩

/-- The crossed projection along `⟨(0 1)⟩` sends `(0 2)` to the three-cycle `(0 1 2)`. -/
theorem coe_crossedProjection_swap_zero_two :
    (h₀₁.crossedProjection (swap 0 2) : Perm (Fin 4)) = swap 0 1 * swap 1 2 := by
  rw [coe_crossedProjection_apply,
    Perm.parityRetract_of_sign_eq_neg_one isSwap_swap_zero_one (by decide)]
  decide

/-- The crossed projection along `⟨(0 1)⟩` sends `(2 3)` to the double transposition
`(2 3)(0 1)` in the Klein four-group. -/
theorem coe_crossedProjection_swap_two_three :
    (h₀₁.crossedProjection (swap 2 3) : Perm (Fin 4)) = swap 2 3 * swap 0 1 := by
  rw [coe_crossedProjection_apply,
    Perm.parityRetract_of_sign_eq_neg_one isSwap_swap_zero_one (by decide)]

/-- **The crossed projection along `⟨(0 1)⟩` is not a homomorphism.** -/
theorem crossedProjection_mul_ne :
    h₀₁.crossedProjection (swap 0 1 * (cycle012 : Perm (Fin 4))) ≠
      h₀₁.crossedProjection (swap 0 1) * h₀₁.crossedProjection cycle012 := by
  intro h
  have h' := congrArg Subtype.val h
  rw [coe_crossedProjection_apply h₀₁, crossedProjection_swap_zero_one, one_mul,
    h₀₁.crossedProjection_coe cycle012, coe_cycle012,
    Perm.parityRetract_of_sign_eq_neg_one isSwap_swap_zero_one (by decide)] at h'
  revert h'
  decide

/-! ### Non-commutative crossed law versus the reversed factor order -/

/-- On the three-cycles `(0 1 2)` and `(0 1 3)` in `A₄`, the crossed projection of the product
equals `(0 1 2) • c (0 1 3) * c (0 1 2) = (0 2)(1 3)`. -/
theorem coe_crossedProjection_cycle012_mul_cycle013 :
    (h₀₁.crossedProjection ((cycle012 : Perm (Fin 4)) * cycle013) : Perm (Fin 4)) =
      swap 0 2 * swap 1 3 := by
  rw [← Subgroup.coe_mul, h₀₁.crossedProjection_coe, Subgroup.coe_mul, coe_cycle012, coe_cycle013]
  decide

/-- Evaluating the reversed factor order `c g * (g • c k)` at `g = (0 1 2)` and `k = (0 1 3)` gives
the Klein-four involution `(0 1)(2 3)` rather than `(0 2)(1 3)`. -/
theorem coe_crossedProjection_reversed_cycle012_cycle013 :
    ((h₀₁.crossedProjection cycle012 *
        ((cycle012 : Perm (Fin 4)) • h₀₁.crossedProjection cycle013) :
        alternatingGroup (Fin 4)) : Perm (Fin 4)) =
      swap 0 1 * swap 2 3 := by
  rw [h₀₁.crossedProjection_coe, h₀₁.crossedProjection_coe, Subgroup.coe_mul,
    Subgroup.coe_conjugationAction_smul, coe_cycle012, coe_cycle013]
  decide

/-- **The reversed factor order fails on `g = (0 1 2)` and `k = (0 1 3)` in `S₄`.** While
`c (g * k) = g • c k * c g` holds on all of `S₄`, swapping the two factors in `A₄` gives a
different element. -/
theorem crossedProjection_cycle012_mul_cycle013_ne_reversed :
    h₀₁.crossedProjection ((cycle012 : Perm (Fin 4)) * cycle013) ≠
      h₀₁.crossedProjection cycle012 *
        ((cycle012 : Perm (Fin 4)) • h₀₁.crossedProjection cycle013) := by
  intro h
  have h' := congrArg Subtype.val h
  rw [coe_crossedProjection_cycle012_mul_cycle013,
    coe_crossedProjection_reversed_cycle012_cycle013] at h'
  revert h'
  decide

/-- **No complement of `A₄` in `S₄` satisfies the reversed factor order**, because `A₄` is
non-abelian. -/
theorem not_forall_crossedProjection_mul_eq_reversed {D : Subgroup (Perm (Fin 4))}
    (h : (alternatingGroup (Fin 4)).IsComplement' D) :
    ¬ ∀ g k : Perm (Fin 4),
      h.crossedProjection (g * k) = h.crossedProjection g * (g • h.crossedProjection k) := by
  rw [h.forall_crossedProjection_mul_eq_iff_isMulCommutative]
  exact not_isMulCommutative_alternatingGroup

/-! ### Non-commutative inner conjugation by `(0 1 2) ∈ A₄` -/

/-- **Conjugating `⟨(0 1)⟩` by `(0 1 2) ∈ A₄` gives `⟨(1 2)⟩`.** -/
theorem conj_cycle012_smul_zpowers_swap_zero_one :
    MulAut.conj (cycle012 : Perm (Fin 4)) • Subgroup.zpowers (swap (0 : Fin 4) 1) =
      Subgroup.zpowers (swap (1 : Fin 4) 2) := by
  have hconj : MulAut.conj (cycle012 : Perm (Fin 4)) (swap (0 : Fin 4) 1) = swap 1 2 := by
    rw [MulAut.conj_apply, coe_cycle012]
    decide
  rw [← map_conj_eq_conj_smul, MonoidHom.map_zpowers]
  exact congrArg Subgroup.zpowers hconj

/-- **Non-abelian inner-twist formula.** The crossed projection along `⟨(1 2)⟩` is obtained from
that along `⟨(0 1)⟩` by `x ↦ x • a * c x * a⁻¹` for `a = (0 1 2) ∈ A₄`. -/
theorem crossedProjection_one_two_eq (x : Perm (Fin 4)) :
    h₁₂.crossedProjection x = x • cycle012 * h₀₁.crossedProjection x * cycle012⁻¹ :=
  (h₀₁.eq_conj_smul_iff_crossedProjection_eq_mul h₁₂ cycle012).mp
    conj_cycle012_smul_zpowers_swap_zero_one.symm x

/-- **The abelian principal-cocycle formula fails for non-abelian `A₄`.** Right-multiplying by
`x • a * a⁻¹` instead of forming `x • a * c x * a⁻¹` fails at `x = (0 1 3)` for `a = (0 1 2)`. -/
theorem crossedProjection_one_two_ne_mul_smul_mul_inv :
    h₁₂.crossedProjection (cycle013 : Perm (Fin 4)) ≠
      h₀₁.crossedProjection cycle013 * ((cycle013 : Perm (Fin 4)) • cycle012 * cycle012⁻¹) := by
  intro h
  have h' := congrArg Subtype.val h
  rw [h₁₂.crossedProjection_coe, h₀₁.crossedProjection_coe, Subgroup.coe_mul, Subgroup.coe_mul,
    Subgroup.coe_conjugationAction_smul, Subgroup.coe_inv, coe_cycle012, coe_cycle013] at h'
  revert h'
  decide

/-! ### Restriction to `A₄` -/

/-- Restricting the complement `⟨(0 1)⟩` to `A₄` gives the trivial subgroup `⊥`. -/
theorem zpowers_swap_zero_one_inf_alternatingGroup :
    Subgroup.zpowers (swap (0 : Fin 4) 1) ⊓ alternatingGroup (Fin 4) = ⊥ := by
  rw [inf_comm]
  exact disjoint_iff.mp isComplement'_zpowers_swap_zero_one.disjoint

/-- Restricting `h₀₁` to `A₄` restricts its crossed projection to the identity on `A₄`. -/
theorem leftProjection_isLocalComplement_inf_alternatingGroup (n : alternatingGroup (Fin 4)) :
    (h₀₁.isLocalComplement_inf (le_refl (alternatingGroup (Fin 4)))).leftProjection n = n := by
  rw [h₀₁.leftProjection_isLocalComplement_inf le_rfl, h₀₁.crossedProjection_coe]

end CrossedProjection

end TauCeti.Examples.SymmetricFour
