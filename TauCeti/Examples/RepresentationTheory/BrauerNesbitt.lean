/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Field.ZMod
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
public import Mathlib.RepresentationTheory.Character
public import Mathlib.RepresentationTheory.Maschke
public import TauCeti.Algebra.MonoidAlgebra.CyclicTwo
public import TauCeti.RepresentationTheory.Charpoly
public import TauCeti.RepresentationTheory.FDRep.Basic
public import TauCeti.RepresentationTheory.BrauerNesbitt.TraceForm

/-!
# Checks for the hypotheses of the Brauer–Nesbitt theorem

The Brauer–Nesbitt theorem compares semisimple representations through their characteristic
polynomials. These examples show what fails when the hypotheses or the invariant are weakened.

* **Semisimplicity is needed.** Over `𝔽₂`, the group `ℤ/2` acting trivially on `𝔽₂²` and acting
  by `(1 1; 0 1)` gives two representations with characteristic polynomial `(X - 1) ^ 2` at every
  element that are not equivalent. The unipotent action is written for any commutative ring `k` as
  the action `a ↦ (1 a; 0 1)` of `(k, +)`, and `𝔽₂ = ℤ/2`.
* **Traces do not suffice in characteristic `p`.** For an odd prime `p`, the representations
  `sgn^{⊕p}` and `1^{⊕p}` of `ℤ/2` over `𝔽_p` are semisimple (Maschke, since `2 ≠ 0` in `𝔽_p`),
  have equal characters (the traces `±p` vanish), and are not equivalent (the generator acts by
  `-1` on one and by `1` on the other). For `p = 3` this shows the bound `p > d` in the trace form
  of Brauer–Nesbitt (`Representation.nonempty_equiv_of_character_eq_of_finrank_lt`) is sharp, and
  `p = 7` gives the same failure in dimension `7`. Over `𝔽₃` in dimension `2` the trace form
  applies. The lemmas are stated for `sgn^{⊕n}` and `1^{⊕n}` over any field `k`, under the
  conditions on `n` and `k` that each argument uses.
-/

public section

noncomputable section

open Polynomial Representation

namespace TauCeti.Examples.RepresentationTheory.BrauerNesbitt

/-! ### Semisimplicity is needed -/

section Unipotent

variable (k : Type*) [CommRing k]

/-- The unipotent representation `a ↦ (1 a; 0 1)` of the additive group of `k`, written
multiplicatively, on `k²`. -/
def unipotent : Representation k (Multiplicative k) (Fin 2 → k) where
  toFun a := Matrix.toLin' !![1, a.toAdd; 0, 1]
  map_one' := by
    rw [toAdd_one, Module.End.one_eq_id, ← Matrix.toLin'_one]
    congr 1
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  map_mul' a b := by
    rw [Module.End.mul_eq_comp, ← Matrix.toLin'_mul, toAdd_mul]
    congr 1
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, add_comm]

/-- The element `a` acts on `k²` by the matrix `(1 a; 0 1)`. -/
@[simp]
theorem unipotent_apply (a : Multiplicative k) :
    unipotent k a = Matrix.toLin' !![1, a.toAdd; 0, 1] :=
  (rfl)

/-- Every element acts by a unipotent matrix: the characteristic polynomial is `(X - 1) ^ 2`. -/
theorem charpoly_unipotent_apply (a : Multiplicative k) :
    (unipotent k a).charpoly = (X - 1) ^ 2 := by
  nontriviality k
  rw [unipotent_apply, Matrix.charpoly_toLin', Matrix.charpoly_fin_two]
  simp [Matrix.trace_fin_two, Matrix.det_fin_two]
  ring

/-- The unipotent representation and the trivial representation on `k²` have the same
characteristic polynomial at every element. -/
theorem charpoly_unipotent_eq_trivial (a : Multiplicative k) :
    (unipotent k a).charpoly = (trivial k (Multiplicative k) (Fin 2 → k) a).charpoly := by
  nontriviality k
  rw [charpoly_unipotent_apply, charpoly_trivial_apply, Module.finrank_fin_fun]

/-- Over a nontrivial ring the unipotent representation is not equivalent to the trivial one. -/
theorem isEmpty_equiv_unipotent_trivial [Nontrivial k] :
    IsEmpty ((unipotent k).Equiv (trivial k (Multiplicative k) (Fin 2 → k))) := by
  refine ⟨fun φ => ?_⟩
  have h := IntertwiningMap.isIntertwining _ _ φ.toIntertwiningMap (Multiplicative.ofAdd 1)
    (Pi.single 1 1)
  rw [trivial_apply, Equiv.coe_toIntertwiningMap] at h
  have := congrArg (· 0) (φ.toLinearEquiv.injective h)
  simp [unipotent_apply, Matrix.toLin'_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_two] at this

/-- **Semisimplicity is needed in Brauer–Nesbitt.** Over `𝔽₂ = ℤ/2`, the trivial action of `ℤ/2`
on `𝔽₂²` and the action through `(1 1; 0 1)` have the same characteristic polynomials at every
element but are not equivalent. -/
example : (∀ a, (unipotent (ZMod 2) a).charpoly =
      (trivial (ZMod 2) (Multiplicative (ZMod 2)) (Fin 2 → ZMod 2) a).charpoly) ∧
    IsEmpty ((unipotent (ZMod 2)).Equiv
      (trivial (ZMod 2) (Multiplicative (ZMod 2)) (Fin 2 → ZMod 2))) :=
  ⟨charpoly_unipotent_eq_trivial _, isEmpty_equiv_unipotent_trivial _⟩

end Unipotent

/-! ### Traces do not suffice in characteristic `p` -/

section Sign

variable (k : Type*) [Field k] (n : ℕ)

/-- The sign representation of `ℤ/2`, written multiplicatively, on `kⁿ`: the generator acts by
`-1`. It is the sign character `TauCeti.cyclicTwoSign` with values in
`Module.End k (Fin n → k)`. -/
def sign : Representation k (Multiplicative (ZMod 2)) (Fin n → k) :=
  cyclicTwoSign _

/-- Each element `a` acts on `sgn^{⊕n}` by `(-1) ^ a.toAdd.val`. -/
theorem sign_apply (a : Multiplicative (ZMod 2)) : sign k n a = (-1) ^ a.toAdd.val :=
  cyclicTwoSign_apply _ a

/-- The generator of `ℤ/2` acts on `sgn^{⊕n}` by `-1`. -/
@[simp]
theorem sign_ofAdd_one : sign k n (Multiplicative.ofAdd 1) = -1 :=
  cyclicTwoSign_ofAdd_one _

/-- The trivial representation of `ℤ/2`, written multiplicatively, on `kⁿ`. -/
abbrev triv : Representation k (Multiplicative (ZMod 2)) (Fin n → k) :=
  trivial k _ _

variable {k n}

/-- If `n = 0` in `k`, the characters of `sgn^{⊕n}` and `1^{⊕n}` are equal: both vanish
identically. -/
theorem character_sign_eq_trivial (hn : (n : k) = 0) (a : Multiplicative (ZMod 2)) :
    (sign k n).character a = (triv k n).character a := by
  induction a using Multiplicative.rec with | ofAdd a => ?_
  rw [char_trivial, Module.finrank_fin_fun, hn, character, sign_apply, toAdd_ofAdd]
  obtain rfl | rfl : a = 0 ∨ a = 1 := by revert a; decide
  all_goals simp [hn, ZMod.val_one]

/-- For `n ≠ 0`, if `-1 ≠ 1` in `k`, the representations `sgn^{⊕n}` and `1^{⊕n}` of `ℤ/2` are
not equivalent: the generator acts by `-1` on one and by `1` on the other. -/
theorem isEmpty_equiv_sign_trivial (hn : n ≠ 0) (h : (-1 : k) ≠ 1) :
    IsEmpty ((sign k n).Equiv (triv k n)) := by
  refine ⟨fun φ => h ?_⟩
  have hφ := IntertwiningMap.isIntertwining _ _ φ.toIntertwiningMap (Multiplicative.ofAdd 1)
    (Pi.single ⟨0, Nat.pos_of_ne_zero hn⟩ 1)
  rw [trivial_apply, Equiv.coe_toIntertwiningMap, sign_ofAdd_one] at hφ
  simpa using congrArg (· ⟨0, Nat.pos_of_ne_zero hn⟩) (φ.toLinearEquiv.injective hφ)

/-- If `2 ≠ 0` in `k`, then `sgn^{⊕n}` and `1^{⊕n}` are semisimple, by Maschke's theorem. -/
theorem isSemisimpleRepresentation_sign_and_trivial (h2 : (2 : k) ≠ 0) :
    (sign k n).IsSemisimpleRepresentation ∧ (triv k n).IsSemisimpleRepresentation := by
  have : NeZero (Nat.card (Multiplicative (ZMod 2)) : k) := ⟨by
    rwa [Nat.card_eq_fintype_card, Fintype.card_multiplicative, ZMod.card, Nat.cast_ofNat]⟩
  exact ⟨inferInstance, inferInstance⟩

/-- **The bound `p > d` is sharp.** Over `𝔽₃`, `sgn^{⊕3}` and `1^{⊕3}` of `ℤ/2` are semisimple of
dimension `3` with equal characters, and are not equivalent. -/
example : ((sign (ZMod 3) 3).IsSemisimpleRepresentation ∧
      (triv (ZMod 3) 3).IsSemisimpleRepresentation) ∧
    (∀ a, (sign (ZMod 3) 3).character a = (triv (ZMod 3) 3).character a) ∧
    IsEmpty ((sign (ZMod 3) 3).Equiv (triv (ZMod 3) 3)) :=
  ⟨isSemisimpleRepresentation_sign_and_trivial (by decide),
    character_sign_eq_trivial (ZMod.natCast_self 3),
    isEmpty_equiv_sign_trivial (by decide) (by decide)⟩

/-- **Below the bound, traces suffice.** Over `𝔽₃`, semisimple representations of a monoid of
dimension `2 < 3` with equal characters are equivalent; `sgn^{⊕3}` and `1^{⊕3}` above satisfy
every hypothesis except `d < p`. -/
example {G V W : Type*} [Monoid G] [AddCommGroup V] [Module (ZMod 3) V]
    [FiniteDimensional (ZMod 3) V] [AddCommGroup W] [Module (ZMod 3) W]
    [FiniteDimensional (ZMod 3) W] (ρ : Representation (ZMod 3) G V)
    (σ : Representation (ZMod 3) G W) [ρ.IsSemisimpleRepresentation]
    [σ.IsSemisimpleRepresentation] (hV : Module.finrank (ZMod 3) V = 2)
    (hW : Module.finrank (ZMod 3) W = 2) (h : ∀ g, ρ.character g = σ.character g) :
    Nonempty (ρ.Equiv σ) :=
  nonempty_equiv_of_character_eq_of_finrank_lt 3 ρ σ (hV.trans hW.symm) (by omega) h

/-- `7` is prime. -/
local instance fact_prime_seven : Fact (Nat.Prime 7) := ⟨by decide⟩

/-- Over `𝔽₇`, `sgn^{⊕7}` and `1^{⊕7}` of `ℤ/2` have equal characters and are not equivalent; in
characteristic zero equal characters would give an equivalence in every dimension. -/
example : (∀ a, (sign (ZMod 7) 7).character a = (triv (ZMod 7) 7).character a) ∧
    IsEmpty ((sign (ZMod 7) 7).Equiv (triv (ZMod 7) 7)) :=
  ⟨character_sign_eq_trivial (ZMod.natCast_self 7),
    isEmpty_equiv_sign_trivial (by decide) (by decide)⟩

end Sign

end TauCeti.Examples.RepresentationTheory.BrauerNesbitt
