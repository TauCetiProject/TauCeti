/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.CharP.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.GroupTheory.Perm.Sign
public import TauCeti.FieldTheory.MilnorK.Basic
public import TauCeti.FieldTheory.MilnorK.SteinbergPairing

import Mathlib.Algebra.CharP.Two

/-!
# Skew-symmetry and graded commutativity of Milnor symbols

For any commutative semiring `R`, the degree-two multiplication `(a, b) ↦ ofUnit a * ofUnit b` in
`TauCeti.MilnorK R` is a Steinberg pairing. When `F` is a field, the integral symbol identities
for Steinberg pairings transfer immediately to `MilnorK F`:

* `{a, -a} = 0` and `{a, b} = -{b, a}`,
* `{a, a} = {a, -1}`, hence `2 • {a, a} = 0` (and `{a, a} = 0` when `CharP F 2`).

In higher degrees, permuting the entries of a Milnor symbol `{a₁, …, aₙ}` multiplies it by the
sign of the permutation (`MilnorK.symbol_comp_perm`), repeated-entry symbols are `2`-torsion
(`MilnorK.two_nsmul_symbol_eq_zero_of_eq`) and vanish in characteristic `2`
(`MilnorK.symbol_eq_zero_of_eq_of_charTwo`), and `MilnorK F` is graded-commutative:
`x * y = (-1)^(i * j) • (y * x)` for `x ∈ degree F i` and `y ∈ degree F j`
(`MilnorK.mul_comm_of_mem_degree`).

Note that `{a, a}` need not vanish integrally in general (for example, `{-1, -1} ≠ 0` over any
ordered ring).

## Main results

* `TauCeti.MilnorK.isSteinbergPairing_mul_ofUnit`: `(a, b) ↦ ofUnit a * ofUnit b` is a Steinberg
  pairing.
* `TauCeti.MilnorK.ofUnit_mul_ofUnit_swap`: `{a, b} = -{b, a}` in `MilnorK F`.
* `TauCeti.MilnorK.ofUnit_mul_ofUnit_self`: `{a, a} = {a, -1}` in `MilnorK F`.
* `TauCeti.MilnorK.symbol_swap_adjacent`: swapping adjacent entries negates a Milnor symbol.
* `TauCeti.MilnorK.symbol_comp_perm`: permuting entries multiplies a Milnor symbol by the
  permutation sign.
* `TauCeti.MilnorK.two_nsmul_symbol_eq_zero_of_eq`: any symbol with a repeated entry is
  `2`-torsion.
* `TauCeti.MilnorK.symbol_eq_zero_of_eq_of_charTwo`: in characteristic `2`, any symbol with a
  repeated entry vanishes.
* `TauCeti.MilnorK.mul_comm_of_mem_degree`: graded commutativity of `MilnorK F`.

## References

* C. A. Weibel, *The K-book: An Introduction to Algebraic K-Theory*, Ch. III, §§6.3, 7.1.
-/

public section

namespace TauCeti.MilnorK

universe u

section CommSemiring

variable {R : Type u} [CommSemiring R]

/-- The degree-two product `(a, b) ↦ ofUnit a * ofUnit b` in `MilnorK R` is a Steinberg
pairing. -/
theorem isSteinbergPairing_mul_ofUnit :
    IsSteinbergPairing (fun a b : Rˣ ↦ ofUnit a * ofUnit b) where
  map_mul_left a₁ a₂ b := by rw [ofUnit_mul, add_mul]
  map_mul_right a b₁ b₂ := by rw [ofUnit_mul, mul_add]
  map_add_eq_one _ _ hab := ofUnit_mul_ofUnit_of_add_eq_one hab

end CommSemiring

section Field

variable {F : Type u} [Field F]

/-! ### Degree-two integral identities in `MilnorK F` -/

/-- For every unit `a` of a field `F`, `{a, -a} = 0` in `MilnorK F`. -/
@[simp]
theorem ofUnit_mul_ofUnit_neg_self (a : Fˣ) : ofUnit a * ofUnit (-a) = 0 :=
  isSteinbergPairing_mul_ofUnit.map_neg_self a

/-- For every unit `a` of a field `F`, `{-a, a} = 0` in `MilnorK F`. -/
@[simp]
theorem ofUnit_mul_ofUnit_neg_self_left (a : Fˣ) : ofUnit (-a) * ofUnit a = 0 :=
  isSteinbergPairing_mul_ofUnit.map_neg_self_left a

/-- Skew-symmetry in degree two: `{a, b} = -{b, a}` in `MilnorK F`. -/
theorem ofUnit_mul_ofUnit_swap (a b : Fˣ) : ofUnit a * ofUnit b = -(ofUnit b * ofUnit a) :=
  isSteinbergPairing_mul_ofUnit.map_swap a b

/-- The diagonal identity in degree two: `{a, a} = {a, -1}` in `MilnorK F`. -/
theorem ofUnit_mul_ofUnit_self (a : Fˣ) : ofUnit a * ofUnit a = ofUnit a * ofUnit (-1) :=
  isSteinbergPairing_mul_ofUnit.map_self a

/-- Every diagonal degree-two symbol is `2`-torsion: `2 • ({a} * {a}) = 0`. -/
theorem two_nsmul_ofUnit_mul_ofUnit_self (a : Fˣ) : 2 • (ofUnit a * ofUnit a) = 0 :=
  isSteinbergPairing_mul_ofUnit.two_nsmul_map_self a

/-- In characteristic `2`, diagonal degree-two symbols vanish: `{a} * {a} = 0`. -/
theorem ofUnit_mul_ofUnit_self_of_charTwo [CharP F 2] (a : Fˣ) :
    ofUnit a * ofUnit a = 0 :=
  isSteinbergPairing_mul_ofUnit.map_self_of_charTwo a

/-! ### Adjacent swaps, repeated entries, and permutations -/

/-- Interchanging two adjacent entries negates a Milnor symbol. -/
theorem symbol_swap_adjacent (l₁ l₂ : List Fˣ) (a b : Fˣ) :
    symbol (l₁ ++ a :: b :: l₂) = -symbol (l₁ ++ b :: a :: l₂) := by
  simp only [symbol_append, symbol_cons]
  rw [← mul_assoc (ofUnit a), ofUnit_mul_ofUnit_swap a b, neg_mul (ofUnit b * ofUnit a),
    mul_neg (symbol l₁), mul_assoc]

/-- A consecutive repeated entry `(a, a)` in a Milnor symbol can be replaced by `(a, -1)`. -/
theorem symbol_repeat_adjacent (l₁ l₂ : List Fˣ) (a : Fˣ) :
    symbol (l₁ ++ a :: a :: l₂) = symbol (l₁ ++ a :: (-1) :: l₂) := by
  simp only [symbol_append, symbol_cons]
  rw [← mul_assoc (ofUnit a), ofUnit_mul_ofUnit_self, mul_assoc]

/-- Any Milnor symbol with a consecutive repeated entry is `2`-torsion. -/
theorem two_nsmul_symbol_repeat_adjacent (l₁ l₂ : List Fˣ) (a : Fˣ) :
    2 • symbol (l₁ ++ a :: a :: l₂) = 0 := by
  simp only [symbol_append, symbol_cons]
  rw [← mul_assoc (ofUnit a), ← mul_smul_comm, ← smul_mul_assoc,
    two_nsmul_ofUnit_mul_ofUnit_self, zero_mul, mul_zero]

/-- In characteristic `2`, any Milnor symbol with a consecutive repeated entry vanishes. -/
theorem symbol_repeat_adjacent_of_charTwo [CharP F 2] (l₁ l₂ : List Fˣ) (a : Fˣ) :
    symbol (l₁ ++ a :: a :: l₂) = 0 := by
  simp only [symbol_append, symbol_cons]
  rw [← mul_assoc (ofUnit a), ofUnit_mul_ofUnit_self_of_charTwo, zero_mul, mul_zero]

/-- Swapping two adjacent indices `i.castSucc` and `i.succ` negates the Milnor symbol of a
tuple. -/
theorem symbol_comp_swap_castSucc_succ {n : ℕ} (a : Fin (n + 1) → Fˣ) (i : Fin n) :
    symbol (List.ofFn (a ∘ Equiv.swap i.castSucc i.succ)) = -symbol (List.ofFn a) := by
  set l : List Fˣ := List.ofFn a
  set l' : List Fˣ := List.ofFn (a ∘ Equiv.swap i.castSucc i.succ)
  have hlen : l.length = n + 1 := List.length_ofFn
  have hlen' : l'.length = n + 1 := List.length_ofFn
  have hl : l = l.take i.1 ++ a i.castSucc :: a i.succ :: l.drop (i.1 + 2) := by
    have hd1 : l.drop i.1 = l[i.1] :: l.drop (i.1 + 1) :=
      List.drop_eq_getElem_cons (by omega)
    have hd2 : l.drop (i.1 + 1) = l[i.1 + 1] :: l.drop (i.1 + 2) :=
      List.drop_eq_getElem_cons (by omega)
    have hg0 : l[i.1] = a i.castSucc := by
      simp only [l, List.getElem_ofFn]; rfl
    have hg1 : l[i.1 + 1] = a i.succ := by
      simp only [l, List.getElem_ofFn]; rfl
    calc l = l.take i.1 ++ l.drop i.1 := (List.take_append_drop i.1 l).symm
      _ = l.take i.1 ++ l[i.1] :: l.drop (i.1 + 1) := by rw [hd1]
      _ = l.take i.1 ++ l[i.1] :: l[i.1 + 1] :: l.drop (i.1 + 2) := by rw [hd2]
      _ = l.take i.1 ++ a i.castSucc :: a i.succ :: l.drop (i.1 + 2) := by rw [hg0, hg1]
  have hswap : ∀ k : Fin (n + 1), k.1 ≠ i.1 → k.1 ≠ i.1 + 1 →
      Equiv.swap i.castSucc i.succ k = k := fun k hk1 hk2 ↦
    Equiv.swap_apply_of_ne_of_ne (fun h ↦ hk1 (congrArg Fin.val h))
      (fun h ↦ hk2 (congrArg Fin.val h))
  have htake_eq : l'.take i.1 = l.take i.1 := by
    refine List.ext_getElem (by simp [hlen, hlen']) fun j hj _ ↦ ?_
    have hj_lt : j < i.1 := lt_of_lt_of_le hj (List.length_take_le i.1 l')
    simp only [List.getElem_take, l', l, List.getElem_ofFn, Function.comp_apply]
    rw [hswap ⟨j, by omega⟩ (by dsimp; omega) (by dsimp; omega)]
  have hdrop_eq : l'.drop (i.1 + 2) = l.drop (i.1 + 2) := by
    refine List.ext_getElem (by simp [hlen, hlen']) fun j hj _ ↦ ?_
    simp only [List.getElem_drop, l', l, List.getElem_ofFn, Function.comp_apply]
    rw [hswap ⟨i.1 + 2 + j, by simp [hlen'] at hj; omega⟩ (by dsimp; omega) (by dsimp; omega)]
  have hl' : l' = l.take i.1 ++ a i.succ :: a i.castSucc :: l.drop (i.1 + 2) := by
    have hd1 : l'.drop i.1 = l'[i.1] :: l'.drop (i.1 + 1) := List.drop_eq_getElem_cons (by omega)
    have hd2 : l'.drop (i.1 + 1) = l'[i.1 + 1] :: l'.drop (i.1 + 2) :=
      List.drop_eq_getElem_cons (by omega)
    have hg0 : l'[i.1] = a i.succ := by
      simp only [l', List.getElem_ofFn, Function.comp_apply]
      exact congrArg a (Equiv.swap_apply_left i.castSucc i.succ)
    have hg1 : l'[i.1 + 1] = a i.castSucc := by
      simp only [l', List.getElem_ofFn, Function.comp_apply]
      exact congrArg a (Equiv.swap_apply_right i.castSucc i.succ)
    calc l' = l'.take i.1 ++ l'.drop i.1 := (List.take_append_drop i.1 l').symm
      _ = l'.take i.1 ++ l'[i.1] :: l'.drop (i.1 + 1) := by rw [hd1]
      _ = l'.take i.1 ++ l'[i.1] :: l'[i.1 + 1] :: l'.drop (i.1 + 2) := by rw [hd2]
      _ = l.take i.1 ++ a i.succ :: a i.castSucc :: l.drop (i.1 + 2) := by
        rw [htake_eq, hdrop_eq, hg0, hg1]
  calc symbol l' = symbol (l.take i.1 ++ a i.succ :: a i.castSucc :: l.drop (i.1 + 2)) :=
        congrArg symbol hl'
    _ = -symbol (l.take i.1 ++ a i.castSucc :: a i.succ :: l.drop (i.1 + 2)) :=
        symbol_swap_adjacent _ _ _ _
    _ = -symbol l := congrArg (fun x ↦ -symbol x) hl.symm

/-- **Skew-symmetry of Milnor symbols.** Permuting the entries of an `n`-symbol multiplies it by
the sign of the permutation. -/
theorem symbol_comp_perm {n : ℕ} (a : Fin n → Fˣ) (σ : Equiv.Perm (Fin n)) :
    symbol (List.ofFn (a ∘ σ)) = (Equiv.Perm.sign σ : ℤ) • symbol (List.ofFn a) := by
  cases n with
  | zero =>
    rw [Subsingleton.elim σ 1]
    simp
  | succ m =>
    have hmem : σ ∈ Submonoid.closure (Set.range fun i : Fin m ↦ Equiv.swap i.castSucc i.succ) := by
      rw [Equiv.Perm.mclosure_swap_castSucc_succ]
      trivial
    revert a
    refine Submonoid.closure_induction
      (motive := fun (τ : Equiv.Perm (Fin (m + 1))) _ ↦ ∀ a : Fin (m + 1) → Fˣ,
        symbol (List.ofFn (a ∘ τ)) = (Equiv.Perm.sign τ : ℤ) • symbol (List.ofFn a))
      ?_ ?_ ?_ hmem
    · rintro _ ⟨i, rfl⟩ a
      rw [symbol_comp_swap_castSucc_succ, Equiv.Perm.sign_swap (Fin.castSucc_lt_succ (i := i)).ne]
      simp
    · intro a
      simp
    · intro τ₁ τ₂ _ _ h₁ h₂ a
      have hcomp : a ∘ ⇑(τ₁ * τ₂) = (a ∘ τ₁) ∘ τ₂ := rfl
      rw [hcomp, h₂ (a ∘ τ₁), h₁ a, ← mul_smul, map_mul, Units.val_mul, mul_comm]

/-- Any Milnor symbol with two equal entries at distinct indices is `2`-torsion. -/
theorem two_nsmul_symbol_eq_zero_of_eq {n : ℕ} {a : Fin n → Fˣ} {i j : Fin n} (hij : i ≠ j)
    (ha : a i = a j) : 2 • symbol (List.ofFn a) = 0 := by
  have hcomp : a ∘ Equiv.swap i j = a := by
    funext k
    dsimp only [Function.comp_apply]
    by_cases hki : k = i
    · subst hki; rw [Equiv.swap_apply_left, ha]
    · by_cases hkj : k = j
      · subst hkj; rw [Equiv.swap_apply_right, ha]
      · rw [Equiv.swap_apply_of_ne_of_ne hki hkj]
  have hneg : symbol (List.ofFn a) = -symbol (List.ofFn a) := by
    have h := symbol_comp_perm a (Equiv.swap i j)
    rw [hcomp, Equiv.Perm.sign_swap hij] at h
    simpa using h
  rw [two_nsmul]
  conv_lhs => rhs; rw [hneg]
  exact add_neg_cancel _

/-- In characteristic `2`, any Milnor symbol with two equal entries at distinct indices
vanishes. -/
theorem symbol_eq_zero_of_eq_of_charTwo [CharP F 2] {n : ℕ} {a : Fin n → Fˣ} {i j : Fin n}
    (hij : i ≠ j) (ha : a i = a j) : symbol (List.ofFn a) = 0 := by
  have hn : 2 ≤ n := by
    have h1 : i.1 ≠ j.1 := fun h ↦ hij (Fin.ext h)
    omega
  let p0 : Fin n := ⟨0, by omega⟩
  let p1 : Fin n := ⟨1, by omega⟩
  have hp01 : p0 ≠ p1 := fun h ↦ by have := congrArg Fin.val h; simp [p0, p1] at this
  let τ₁ : Equiv.Perm (Fin n) := Equiv.swap i p0
  have hτ₁_ne : τ₁ j ≠ p0 := by
    intro h
    exact hij (τ₁.injective (by rw [h]; exact Equiv.swap_apply_left i p0))
  let τ₂ : Equiv.Perm (Fin n) := Equiv.swap (τ₁ j) p1
  let σ : Equiv.Perm (Fin n) := (τ₂ * τ₁)⁻¹
  have hσ0 : σ p0 = i := by
    apply (τ₂ * τ₁).injective
    rw [← Equiv.Perm.mul_apply, mul_inv_cancel, Equiv.Perm.one_apply, Equiv.Perm.mul_apply,
      Equiv.swap_apply_left]
    exact (Equiv.swap_apply_of_ne_of_ne hτ₁_ne.symm hp01).symm
  have hσ1 : σ p1 = j := by
    apply (τ₂ * τ₁).injective
    rw [← Equiv.Perm.mul_apply, mul_inv_cancel, Equiv.Perm.one_apply, Equiv.Perm.mul_apply]
    exact (Equiv.swap_apply_left (τ₁ j) p1).symm
  have hzero : symbol (List.ofFn (a ∘ σ)) = 0 := by
    set l : List Fˣ := List.ofFn (a ∘ σ)
    have hlen : l.length = n := List.length_ofFn
    have hsplit : l = [] ++ a i :: a i :: l.drop 2 := by
      have hd0 : l = l[0] :: l.drop 1 := by
        simpa using List.drop_eq_getElem_cons (l := l) (i := 0) (by omega)
      have hd1 : l.drop 1 = l[1] :: l.drop 2 :=
        List.drop_eq_getElem_cons (l := l) (i := 1) (by omega)
      have h0 : l[0] = a i := by
        simp only [l, List.getElem_ofFn, Function.comp_apply]
        exact congrArg a hσ0
      have h1 : l[1] = a i := by
        simp only [l, List.getElem_ofFn, Function.comp_apply]
        rw [ha]
        exact congrArg a hσ1
      calc l = l[0] :: l.drop 1 := hd0
        _ = l[0] :: l[1] :: l.drop 2 := by rw [hd1]
        _ = [] ++ a i :: a i :: l.drop 2 := by rw [List.nil_append, h0, h1]
    rw [hsplit]
    exact symbol_repeat_adjacent_of_charTwo [] (l.drop 2) (a i)
  rw [symbol_comp_perm] at hzero
  have hmul := congrArg (fun z : MilnorK F ↦ (Equiv.Perm.sign σ : ℤ) • z) hzero
  rw [smul_zero, ← mul_smul, ← Units.val_mul, Int.units_mul_self, Units.val_one, one_smul] at hmul
  exact hmul

/-! ### Graded commutativity of `MilnorK F` -/

/-- Moving a degree-one generator past a symbol of length `n` multiplies by `(-1)^n`. -/
theorem ofUnit_mul_symbol (a : Fˣ) (l : List Fˣ) :
    ofUnit a * symbol l = (-1 : ℤ) ^ l.length • (symbol l * ofUnit a) := by
  induction l with
  | nil => simp
  | cons b l ih =>
    rw [symbol_cons, List.length_cons, ← mul_assoc, ofUnit_mul_ofUnit_swap a b,
      neg_mul (ofUnit b * ofUnit a), mul_assoc, ih, mul_smul_comm, ← neg_smul, pow_succ,
      mul_neg_one, mul_assoc]

/-- Commuting two Milnor symbols multiplies by `(-1)^(l₁.length * l₂.length)`. -/
theorem symbol_mul_symbol_comm (l₁ l₂ : List Fˣ) :
    symbol l₁ * symbol l₂ = (-1 : ℤ) ^ (l₁.length * l₂.length) • (symbol l₂ * symbol l₁) := by
  induction l₁ with
  | nil => simp
  | cons a l₁ ih =>
    rw [symbol_cons, List.length_cons, mul_assoc, ih, mul_smul_comm, ← mul_assoc,
      ofUnit_mul_symbol, smul_mul_assoc, ← mul_smul, ← pow_add, add_mul, one_mul, add_comm,
      mul_assoc]

/-- **Graded commutativity of `MilnorK F`.** Homogeneous elements of degrees `i` and `j` satisfy
`x * y = (-1)^(i * j) • (y * x)`. -/
theorem mul_comm_of_mem_degree {i j : ℕ} {x y : MilnorK F} (hx : x ∈ degree F i)
    (hy : y ∈ degree F j) : x * y = (-1 : ℤ) ^ (i * j) • (y * x) := by
  rw [degree_eq_span_symbol] at hx hy
  refine Submodule.span_induction
    (p := fun u _ ↦ u * y = (-1 : ℤ) ^ (i * j) • (y * u)) ?_ ?_ ?_ ?_ hx
  · rintro _ ⟨l₁, rfl, rfl⟩
    refine Submodule.span_induction
      (p := fun v _ ↦ symbol l₁ * v = (-1 : ℤ) ^ (l₁.length * j) • (v * symbol l₁))
      ?_ ?_ ?_ ?_ hy
    · rintro _ ⟨l₂, rfl, rfl⟩
      exact symbol_mul_symbol_comm l₁ l₂
    · simp
    · intro v₁ v₂ _ _ hv₁ hv₂
      rw [mul_add, add_mul, smul_add, hv₁, hv₂]
    · intro r v _ hv
      rw [mul_smul_comm, smul_mul_assoc, smul_comm, hv]
  · simp
  · intro u₁ u₂ _ _ hu₁ hu₂
    rw [add_mul, mul_add, smul_add, hu₁, hu₂]
  · intro r u _ hu
    rw [smul_mul_assoc, mul_smul_comm, smul_comm, hu]

end Field

end TauCeti.MilnorK
