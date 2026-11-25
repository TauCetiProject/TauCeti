/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.Automorphism.IntLattice
public import TauCeti.GroupTheory.Automorphism.Outer
public import TauCeti.GroupTheory.Perm.Centralizer
public import TauCeti.GroupTheory.Perm.Fin
public import Mathlib.Data.ZMod.Aut

/-!
# Outer automorphism groups of small groups

Checks for `TauCeti.OuterAut`, the automorphisms of a group modulo the inner automorphisms:

* the outer automorphism groups of the trivial group and of `S₃` are trivial: every automorphism
  of `S₃` is conjugation by an element (`S₃` has trivial centre, and an automorphism is determined
  by the images of a 3-cycle and a transposition, which leaves at most `2 · 3 = 6` automorphisms);
* `OuterAut ℤ` has exactly two elements, `±id`;
* `OuterAut ℤ² ≅ GL₂(ℤ)`: for the abelian `ℤ²` there are no nontrivial inner automorphisms, and
  the automorphisms of `ℤ²` are the invertible integer matrices (the case `ι = Fin 2` of the
  library's `TauCeti.outerAutIntPiEquiv`).

The groups `ℤ` and `ℤ²` are written multiplicatively, as `Multiplicative ℤ` and
`Multiplicative (Fin 2 → ℤ)`.
-/

public section

namespace TauCeti.OuterAutExamples

open TauCeti Multiplicative

/-- The outer automorphism group of the trivial group is trivial. -/
instance subsingleton_outerAut_unit : Subsingleton (OuterAut Unit) :=
  QuotientGroup.mk_surjective.subsingleton

/-- **Every automorphism of `S₃` is inner**, so `OuterAut S₃` is trivial. -/
instance subsingleton_outerAut_perm_fin_three : Subsingleton (OuterAut (Equiv.Perm (Fin 3))) := by
  -- `S₃` has trivial centre, the kernel of `MulAut.conj`.
  have hconj : Function.Injective (MulAut.conj : Equiv.Perm (Fin 3) →* MulAut _) := by
    rw [← MonoidHom.ker_eq_bot_iff, MulAut.ker_conj, Equiv.Perm.center_eq_bot (by simp)]
  -- An automorphism preserves the elements of each order, and is determined by the images of a
  -- 3-cycle and a transposition: there are at most `2 · 3 = 6` automorphisms.
  have hord (φ : MulAut (Equiv.Perm (Fin 3))) (n : ℕ) {x : Equiv.Perm (Fin 3)}
      (hx : x ^ n = 1 ∧ x ≠ 1) : φ x ^ n = 1 ∧ φ x ≠ 1 :=
    ⟨by rw [← map_pow, hx.1, map_one], (map_ne_one_iff φ φ.injective).2 hx.2⟩
  let f (φ : MulAut (Equiv.Perm (Fin 3))) : {x : Equiv.Perm (Fin 3) // x ^ 3 = 1 ∧ x ≠ 1} ×
      {x : Equiv.Perm (Fin 3) // x ^ 2 = 1 ∧ x ≠ 1} :=
    (⟨φ (finRotate 3), hord φ 3 (by decide)⟩, ⟨φ (Equiv.swap 0 1), hord φ 2 (by decide)⟩)
  have hf : Function.Injective f := fun φ ψ h ↦ MulEquiv.toMonoidHom_injective <|
    MonoidHom.ext_perm_fin (congrArg Subtype.val (Prod.ext_iff.1 h).1)
      (congrArg Subtype.val (Prod.ext_iff.1 h).2)
  have hcard : Nat.card (MulAut (Equiv.Perm (Fin 3))) ≤ Nat.card (Equiv.Perm (Fin 3)) := by
    refine (Nat.card_le_card_of_injective f hf).trans ?_
    simp only [Nat.card_eq_fintype_card]
    decide
  have hbij := hconj.bijective_of_nat_card_le hcard
  refine ⟨fun a b ↦ ?_⟩
  obtain ⟨φ, rfl⟩ := QuotientGroup.mk_surjective a
  obtain ⟨ψ, rfl⟩ := QuotientGroup.mk_surjective b
  obtain ⟨g, rfl⟩ := hbij.2 φ
  obtain ⟨h, rfl⟩ := hbij.2 ψ
  rw [OuterAut.mk_conj, OuterAut.mk_conj]

/-- **`OuterAut ℤ² ≅ GL₂(ℤ)`**: the outer automorphisms of the abelian group `ℤ²` are its
automorphisms, the invertible `2 × 2` integer matrices. -/
noncomputable example :
    OuterAut (Multiplicative (Fin 2 → ℤ)) ≃* Matrix.GeneralLinearGroup (Fin 2) ℤ :=
  outerAutIntPiEquiv (Fin 2)

/-- The matrix in `GL₂(ℤ)` of the outer class of `φ` has as its `j`-th column the image under `φ`
of the `j`-th standard basis vector. -/
example (φ : MulAut (Multiplicative (Fin 2 → ℤ))) (i j : Fin 2) :
    (outerAutIntPiEquiv (Fin 2) (φ : OuterAut _) : Matrix (Fin 2) (Fin 2) ℤ) i j =
      (φ (ofAdd (Pi.single j 1))).toAdd i := by
  simp

/-- **`OuterAut ℤ` has exactly two elements**, the classes of `id` and of `-id`. -/
theorem card_outerAut_int : Nat.card (OuterAut (Multiplicative ℤ)) = 2 := by
  -- `ZMod 0` is `ℤ`, so `ZMod.AddAutEquivUnits 0` identifies `AddAut ℤ` with `ℤˣ`.
  rw [Nat.card_congr ((OuterAut.mulEquivOfIsMulCommutative.trans
      (MulAutMultiplicative ℤ)).toEquiv.trans (ZMod.AddAutEquivUnits 0).toEquiv)]
  exact (Nat.card_congr (Additive.toMul : Additive ℤˣ ≃ ℤˣ)).trans
    (Nat.card_eq_fintype_card.trans Fintype.card_units_int)

end TauCeti.OuterAutExamples
