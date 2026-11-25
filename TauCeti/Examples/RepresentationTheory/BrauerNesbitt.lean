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
public import TauCeti.RepresentationTheory.Charpoly
public import TauCeti.RepresentationTheory.FDRep.Basic

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
  have equal characters (the traces `±p` vanish), and are not equivalent (the determinants of the
  generator are `-1` and `1`). For `p = 3` this shows the bound `p > d` in the trace form of
  Brauer–Nesbitt is sharp, and `p = 7` gives the same failure in dimension `7`.
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
@[expose] def unipotent : Representation k (Multiplicative k) (Fin 2 → k) where
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
theorem unipotent_apply (a : Multiplicative k) :
    unipotent k a = Matrix.toLin' !![1, a.toAdd; 0, 1] :=
  rfl

/-- Every element acts by a unipotent matrix: the characteristic polynomial is `(X - 1) ^ 2`. -/
theorem charpoly_unipotent_apply [Nontrivial k] (a : Multiplicative k) :
    (unipotent k a).charpoly = (X - 1) ^ 2 := by
  rw [unipotent_apply, Matrix.charpoly_toLin', Matrix.charpoly_fin_two]
  simp [Matrix.trace_fin_two, Matrix.det_fin_two]
  ring

/-- The unipotent representation and the trivial representation on `k²` have the same
characteristic polynomial at every element. -/
theorem charpoly_unipotent_eq_trivial [Nontrivial k] (a : Multiplicative k) :
    (unipotent k a).charpoly = (trivial k (Multiplicative k) (Fin 2 → k) a).charpoly := by
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
`-1`. -/
@[expose] def sign : Representation k (Multiplicative (ZMod 2)) (Fin n → k) where
  toFun a := (-1) ^ a.toAdd.val
  map_one' := by simp
  map_mul' a b := by
    rw [toAdd_mul, ZMod.val_add, ← pow_add, neg_one_pow_eq_pow_mod_two (a.toAdd.val + _)]

/-- The generator `a` acts on `sgn^{⊕n}` by `(-1) ^ a`. -/
theorem sign_apply (a : Multiplicative (ZMod 2)) : sign k n a = (-1) ^ a.toAdd.val :=
  rfl

/-- The generator of `ℤ/2` acts on `sgn^{⊕n}` by `-1`. -/
theorem sign_ofAdd_one : sign k n (Multiplicative.ofAdd 1) = -1 := by
  rw [sign_apply, toAdd_ofAdd]
  exact pow_one _

/-- The trivial representation of `ℤ/2`, written multiplicatively, on `kⁿ`. -/
abbrev triv : Representation k (Multiplicative (ZMod 2)) (Fin n → k) :=
  trivial k _ _

/-- The determinant of the generator on `sgn^{⊕n}` is `(-1) ^ n`. -/
theorem det_sign_ofAdd_one : LinearMap.det (sign k n (Multiplicative.ofAdd 1)) = (-1) ^ n := by
  rw [sign_ofAdd_one, ← neg_one_smul k (1 : Module.End k (Fin n → k)), LinearMap.det_smul,
    map_one, mul_one, Module.finrank_fin_fun]

variable (p : ℕ) [Fact p.Prime]

/-- Over `𝔽_p`, the characters of `sgn^{⊕p}` and `1^{⊕p}` are equal: both vanish identically. -/
theorem character_sign_eq_trivial (a : Multiplicative (ZMod 2)) :
    (sign (ZMod p) p).character a = (triv (ZMod p) p).character a := by
  induction a using Multiplicative.rec with | ofAdd a => ?_
  rw [char_trivial, Module.finrank_fin_fun, ZMod.natCast_self, character, sign_apply]
  fin_cases a
  · change LinearMap.trace _ _ ((-1) ^ 0) = 0
    rw [pow_zero, LinearMap.trace_one, Module.finrank_fin_fun, ZMod.natCast_self]
  · change LinearMap.trace _ _ ((-1) ^ 1) = 0
    rw [pow_one, map_neg, LinearMap.trace_one, Module.finrank_fin_fun, ZMod.natCast_self, neg_zero]

/-- For an odd prime `p`, the representations `sgn^{⊕p}` and `1^{⊕p}` of `ℤ/2` over `𝔽_p` are
not equivalent. -/
theorem isEmpty_equiv_sign_trivial (hp : p ≠ 2) :
    IsEmpty ((sign (ZMod p) p).Equiv (triv (ZMod p) p)) := by
  have : Fact (2 < p) := ⟨lt_of_le_of_ne (Fact.out : p.Prime).two_le (Ne.symm hp)⟩
  refine ⟨fun φ => ZMod.neg_one_ne_one (n := p) ?_⟩
  have h := φ.det_apply_eq (Multiplicative.ofAdd 1)
  rwa [det_sign_ofAdd_one, isTrivial_def, LinearMap.det_id,
    (Fact.out : p.Prime).odd_of_ne_two hp |>.neg_one_pow] at h

/-- `sgn^{⊕p}` and `1^{⊕p}` are semisimple over `𝔽_p` for an odd prime `p`, by Maschke's
theorem. -/
theorem isSemisimpleRepresentation_sign (hp : p ≠ 2) :
    (sign (ZMod p) p).IsSemisimpleRepresentation ∧
      (triv (ZMod p) p).IsSemisimpleRepresentation := by
  have : NeZero (Nat.card (Multiplicative (ZMod 2)) : ZMod p) := ⟨by
    rw [Nat.card_eq_fintype_card, Fintype.card_multiplicative, ZMod.card, Nat.cast_ofNat]
    intro h
    have h2 := (ZMod.natCast_eq_zero_iff 2 p).mp (by exact_mod_cast h)
    exact hp ((Nat.prime_dvd_prime_iff_eq Fact.out Nat.prime_two).mp h2)⟩
  exact ⟨inferInstance, inferInstance⟩

/-- **The bound `p > d` is sharp.** Over `𝔽₃`, `sgn^{⊕3}` and `1^{⊕3}` of `ℤ/2` are semisimple of
dimension `3` with equal characters, and are not equivalent. -/
example : (sign (ZMod 3) 3).IsSemisimpleRepresentation ∧
    (∀ a, (sign (ZMod 3) 3).character a = (triv (ZMod 3) 3).character a) ∧
    IsEmpty ((sign (ZMod 3) 3).Equiv (triv (ZMod 3) 3)) :=
  ⟨(isSemisimpleRepresentation_sign (p := 3) (by decide)).1, character_sign_eq_trivial (p := 3),
    isEmpty_equiv_sign_trivial (p := 3) (by decide)⟩

/-- `7` is prime. -/
local instance fact_prime_seven : Fact (Nat.Prime 7) := ⟨by decide⟩

/-- Over `𝔽₇`, `sgn^{⊕7}` and `1^{⊕7}` of `ℤ/2` have equal characters and are not equivalent; in
characteristic zero equal characters would give an equivalence in every dimension. -/
example : (∀ a, (sign (ZMod 7) 7).character a = (triv (ZMod 7) 7).character a) ∧
    IsEmpty ((sign (ZMod 7) 7).Equiv (triv (ZMod 7) 7)) :=
  ⟨character_sign_eq_trivial (p := 7), isEmpty_equiv_sign_trivial (p := 7) (by decide)⟩

end Sign

end TauCeti.Examples.RepresentationTheory.BrauerNesbitt
