/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.Perm.Sign
public import TauCeti.FieldTheory.MilnorKTheory.Grading

/-!
# Skew-symmetry and graded commutativity of Milnor K-theory

Over any field `F`, the Steinberg relation in `MilnorK F` forces the degree-one generators to
anti-commute (`TauCeti.MilnorK.ofUnit_mul_comm`) and satisfy `ofUnit a * ofUnit (-a) = 0` and
`ofUnit a * ofUnit a = ofUnit a * ofUnit (-1)`.

Consequently:

* `MilnorK F` is graded-commutative: `x * y = (-1)^(m * n) • (y * x)` for `x ∈ degree F m` and
  `y ∈ degree F n` (`TauCeti.MilnorK.mul_comm_of_mem_degree`).
* Permuting the entries of a Milnor symbol multiplies it by the sign of the permutation
  (`TauCeti.MilnorK.symbol_ofFn_comp_perm`).
* Symbols with an opposite pair `a, -a` vanish (`TauCeti.MilnorK.symbol_neg_self_of_ne`), symbols
  with a repeated entry are `2`-torsion (`TauCeti.MilnorK.two_nsmul_symbol_of_duplicate`), and in
  characteristic `2` symbols with a repeated entry vanish
  (`TauCeti.MilnorK.symbol_eq_zero_of_duplicate_of_charTwo`).

## References

* J. Milnor, *Algebraic K-theory and quadratic forms*, Invent. Math. **9** (1970), §1.
* C. Weibel, *The K-book: An Introduction to Algebraic K-Theory*, Chapter III, §7.1.
-/

public section

namespace TauCeti.MilnorK

variable {F : Type*} [Field F]

/-! ### Degree-two field identities in `MilnorK F` -/

/-- The class `ofUnit (-1)` is `2`-torsion. -/
theorem two_nsmul_ofUnit_neg_one : 2 • ofUnit (-1 : Fˣ) = 0 := by
  rw [← ofUnit_pow]
  simp

/-- In `MilnorK F`, `-ofUnit (-1) = ofUnit (-1)`. -/
theorem neg_ofUnit_neg_one : -ofUnit (-1 : Fˣ) = ofUnit (-1 : Fˣ) := by
  rw [← ofUnit_inv]
  simp

/-- Over a field, `ofUnit a * ofUnit (-a) = 0` for every unit `a`. -/
@[simp]
theorem ofUnit_mul_neg_self (a : Fˣ) : ofUnit a * ofUnit (-a) = 0 :=
  isSteinbergPairing_ofUnit_mul.map_neg_self a

/-- Over a field, degree-one generators anti-commute:
`ofUnit a * ofUnit b = -(ofUnit b * ofUnit a)`. -/
theorem ofUnit_mul_comm (a b : Fˣ) : ofUnit a * ofUnit b = -(ofUnit b * ofUnit a) :=
  isSteinbergPairing_ofUnit_mul.map_swap a b

/-- Over a field, `ofUnit a * ofUnit a = ofUnit a * ofUnit (-1)`. -/
theorem ofUnit_mul_self (a : Fˣ) : ofUnit a * ofUnit a = ofUnit a * ofUnit (-1) :=
  isSteinbergPairing_ofUnit_mul.map_self a

/-- Over a field, `2 • (ofUnit a * ofUnit a) = 0`. -/
theorem two_nsmul_ofUnit_mul_self (a : Fˣ) : 2 • (ofUnit a * ofUnit a) = 0 :=
  isSteinbergPairing_ofUnit_mul.two_nsmul_map_self a

/-- Over a field of characteristic `2`, `ofUnit a * ofUnit a = 0`. -/
theorem ofUnit_mul_self_eq_zero_of_charTwo [CharP F 2] (a : Fˣ) :
    ofUnit a * ofUnit a = 0 :=
  isSteinbergPairing_ofUnit_mul.map_self_eq_zero_of_charTwo a

/-! ### Graded commutativity -/

/-- Moving a degree-one generator past a Milnor symbol multiplies by `(-1) ^ l.length`. -/
theorem ofUnit_mul_symbol (a : Fˣ) (l : List Fˣ) :
    ofUnit a * symbol l = (-1 : ℤ) ^ l.length • (symbol l * ofUnit a) := by
  induction l with
  | nil => simp
  | cons b l ih =>
    rw [symbol_cons, List.length_cons, pow_succ, mul_comm ((-1 : ℤ) ^ l.length) (-1), mul_zsmul,
      neg_one_zsmul]
    calc
      ofUnit a * (ofUnit b * symbol l) = (ofUnit a * ofUnit b) * symbol l :=
        (mul_assoc _ _ _).symm
      _ = -(ofUnit b * ofUnit a) * symbol l := by rw [ofUnit_mul_comm a b]
      _ = -((ofUnit b * ofUnit a) * symbol l) := neg_mul (ofUnit b * ofUnit a) (symbol l)
      _ = -(ofUnit b * (ofUnit a * symbol l)) := by rw [mul_assoc]
      _ = -(ofUnit b * ((-1 : ℤ) ^ l.length • (symbol l * ofUnit a))) := by rw [ih]
      _ = -((-1 : ℤ) ^ l.length • (ofUnit b * (symbol l * ofUnit a))) := by
        rw [mul_smul_comm]
      _ = -((-1 : ℤ) ^ l.length • ((ofUnit b * symbol l) * ofUnit a)) := by
        rw [mul_assoc]

/-- Commuting two Milnor symbols multiplies by `(-1) ^ (l₁.length * l₂.length)`. -/
theorem symbol_mul_symbol (l₁ l₂ : List Fˣ) :
    symbol l₁ * symbol l₂ =
      (-1 : ℤ) ^ (l₁.length * l₂.length) • (symbol l₂ * symbol l₁) := by
  induction l₁ with
  | nil => simp
  | cons a l₁ ih =>
    rw [symbol_cons, List.length_cons, add_mul, one_mul, pow_add, mul_zsmul]
    calc
      ofUnit a * symbol l₁ * symbol l₂ = ofUnit a * (symbol l₁ * symbol l₂) :=
        mul_assoc _ _ _
      _ = ofUnit a *
            ((-1 : ℤ) ^ (l₁.length * l₂.length) • (symbol l₂ * symbol l₁)) := by
        rw [ih]
      _ = (-1 : ℤ) ^ (l₁.length * l₂.length) •
            (ofUnit a * (symbol l₂ * symbol l₁)) := by
        rw [mul_smul_comm]
      _ = (-1 : ℤ) ^ (l₁.length * l₂.length) •
            ((ofUnit a * symbol l₂) * symbol l₁) := by
        rw [mul_assoc]
      _ = (-1 : ℤ) ^ (l₁.length * l₂.length) •
            (((-1 : ℤ) ^ l₂.length • (symbol l₂ * ofUnit a)) * symbol l₁) := by
        rw [ofUnit_mul_symbol a l₂]
      _ = (-1 : ℤ) ^ (l₁.length * l₂.length) •
            ((-1 : ℤ) ^ l₂.length • ((symbol l₂ * ofUnit a) * symbol l₁)) := by
        rw [smul_mul_assoc]
      _ = (-1 : ℤ) ^ (l₁.length * l₂.length) •
            ((-1 : ℤ) ^ l₂.length • (symbol l₂ * (ofUnit a * symbol l₁))) := by
        rw [mul_assoc]

/-- **Graded commutativity of `MilnorK F`**: homogeneous elements of degrees `m` and `n` satisfy
`x * y = (-1)^(m * n) • (y * x)`. -/
theorem mul_comm_of_mem_degree {m n : ℕ} {x y : MilnorK F}
    (hx : x ∈ degree F m) (hy : y ∈ degree F n) :
    x * y = (-1 : ℤ) ^ (m * n) • (y * x) := by
  rw [degree_eq_span] at hx hy
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨l₁, rfl, rfl⟩ := hx
    induction hy using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨l₂, rfl, rfl⟩ := hy
      exact symbol_mul_symbol l₁ l₂
    | zero => simp
    | add y₁ y₂ _ _ h₁ h₂ => rw [mul_add, add_mul, smul_add, h₁, h₂]
    | smul k y _ hy => rw [mul_smul_comm, smul_mul_assoc, smul_comm, hy]
  | zero => simp
  | add x₁ x₂ _ _ h₁ h₂ => rw [add_mul, mul_add, smul_add, h₁, h₂]
  | smul k x _ hx => rw [smul_mul_assoc, mul_smul_comm, smul_comm, hx]

/-! ### Skew-symmetry under entry swaps and permutations -/

/-- Swapping two adjacent entries of a Milnor symbol negates it. -/
theorem symbol_swap_adjacent (l₁ : List Fˣ) (a b : Fˣ) (l₂ : List Fˣ) :
    symbol (l₁ ++ a :: b :: l₂) = -symbol (l₁ ++ b :: a :: l₂) := by
  rw [symbol_append, symbol_cons, symbol_cons, symbol_append, symbol_cons, symbol_cons]
  calc
    symbol l₁ * (ofUnit a * (ofUnit b * symbol l₂))
      = symbol l₁ * ((ofUnit a * ofUnit b) * symbol l₂) := by rw [mul_assoc]
    _ = symbol l₁ * (-(ofUnit b * ofUnit a) * symbol l₂) := by rw [ofUnit_mul_comm a b]
    _ = symbol l₁ * -((ofUnit b * ofUnit a) * symbol l₂) :=
      congrArg (symbol l₁ * ·) (neg_mul (ofUnit b * ofUnit a) (symbol l₂))
    _ = -(symbol l₁ * ((ofUnit b * ofUnit a) * symbol l₂)) :=
      mul_neg (symbol l₁) ((ofUnit b * ofUnit a) * symbol l₂)
    _ = -(symbol l₁ * (ofUnit b * (ofUnit a * symbol l₂))) := by rw [mul_assoc]

/-- Swapping any two separated entries of a Milnor symbol negates it. -/
theorem symbol_swap_middle (l₁ : List Fˣ) (a : Fˣ) (l₂ : List Fˣ) (b : Fˣ)
    (l₃ : List Fˣ) :
    symbol (l₁ ++ a :: (l₂ ++ b :: l₃)) = -symbol (l₁ ++ b :: (l₂ ++ a :: l₃)) := by
  have hinner : ofUnit a * symbol l₂ * ofUnit b = -(ofUnit b * symbol l₂ * ofUnit a) := by
    calc
      ofUnit a * symbol l₂ * ofUnit b
        = ((-1 : ℤ) ^ l₂.length • (symbol l₂ * ofUnit a)) * ofUnit b := by
          rw [ofUnit_mul_symbol a l₂]
      _ = (-1 : ℤ) ^ l₂.length • ((symbol l₂ * ofUnit a) * ofUnit b) :=
          smul_mul_assoc ((-1 : ℤ) ^ l₂.length) (symbol l₂ * ofUnit a) (ofUnit b)
      _ = (-1 : ℤ) ^ l₂.length • (symbol l₂ * (ofUnit a * ofUnit b)) := by rw [mul_assoc]
      _ = (-1 : ℤ) ^ l₂.length • (symbol l₂ * -(ofUnit b * ofUnit a)) := by
          rw [ofUnit_mul_comm a b]
      _ = (-1 : ℤ) ^ l₂.length • -(symbol l₂ * (ofUnit b * ofUnit a)) :=
          congrArg ((-1 : ℤ) ^ l₂.length • ·) (mul_neg (symbol l₂) (ofUnit b * ofUnit a))
      _ = -((-1 : ℤ) ^ l₂.length • (symbol l₂ * (ofUnit b * ofUnit a))) :=
          smul_neg ((-1 : ℤ) ^ l₂.length) (symbol l₂ * (ofUnit b * ofUnit a))
      _ = -((-1 : ℤ) ^ l₂.length • ((symbol l₂ * ofUnit b) * ofUnit a)) := by rw [mul_assoc]
      _ = -(((-1 : ℤ) ^ l₂.length • (symbol l₂ * ofUnit b)) * ofUnit a) := by
          rw [smul_mul_assoc]
      _ = -(ofUnit b * symbol l₂ * ofUnit a) := by rw [← ofUnit_mul_symbol b l₂]
  simp only [symbol_append, symbol_cons]
  calc
    symbol l₁ * (ofUnit a * (symbol l₂ * (ofUnit b * symbol l₃)))
      = symbol l₁ * ((ofUnit a * symbol l₂ * ofUnit b) * symbol l₃) := by
        simp only [mul_assoc]
    _ = symbol l₁ * (-(ofUnit b * symbol l₂ * ofUnit a) * symbol l₃) := by rw [hinner]
    _ = symbol l₁ * -((ofUnit b * symbol l₂ * ofUnit a) * symbol l₃) :=
        congrArg (symbol l₁ * ·) (neg_mul (ofUnit b * symbol l₂ * ofUnit a) (symbol l₃))
    _ = -(symbol l₁ * ((ofUnit b * symbol l₂ * ofUnit a) * symbol l₃)) :=
        mul_neg (symbol l₁) ((ofUnit b * symbol l₂ * ofUnit a) * symbol l₃)
    _ = -(symbol l₁ * (ofUnit b * (symbol l₂ * (ofUnit a * symbol l₃)))) := by
        simp only [mul_assoc]

/-- Splitting `List.ofFn v` and `List.ofFn (v ∘ Equiv.swap i j)` at indices `i < j`. -/
private theorem exists_split_ofFn_swap {α : Type*} {n : ℕ} (v : Fin n → α)
    {i j : Fin n} (hij : i < j) :
    ∃ l₁ l₂ l₃ : List α,
      List.ofFn v = l₁ ++ v i :: (l₂ ++ v j :: l₃) ∧
      List.ofFn (v ∘ Equiv.swap i j) = l₁ ++ v j :: (l₂ ++ v i :: l₃) := by
  have hsplit : ∀ w : Fin n → α,
      List.ofFn w =
        (List.ofFn w).take i ++
          w i :: (((List.ofFn w).drop (i + 1)).take (j - i - 1) ++
            w j :: (List.ofFn w).drop (j + 1)) := by
    intro w
    have h1 : (List.ofFn w).drop i = w i :: (List.ofFn w).drop (i + 1) := by
      rw [List.drop_eq_getElem_cons (by simp)]
      simp
    have hij' : (i : ℕ) + 1 + (j - i - 1) = j := by omega
    have h2 : ((List.ofFn w).drop (i + 1)).drop (j - i - 1) =
        w j :: (List.ofFn w).drop (j + 1) := by
      rw [List.drop_drop, hij', List.drop_eq_getElem_cons (by simp)]
      simp
    rw [← h2, List.take_append_drop, ← h1, List.take_append_drop]
  have htake : (List.ofFn (v ∘ Equiv.swap i j)).take i = (List.ofFn v).take i := by
    apply List.ext_getElem
    · simp
    · intro k hk₁ hk₂
      simp only [List.getElem_take, List.getElem_ofFn, Function.comp_apply]
      have hki : k < i := by simp only [List.length_take, List.length_ofFn] at hk₁; omega
      have hne_i : (⟨k, by omega⟩ : Fin n) ≠ i := fun h => by
        have := congrArg Fin.val h; dsimp at this; omega
      have hne_j : (⟨k, by omega⟩ : Fin n) ≠ j := fun h => by
        have := congrArg Fin.val h; dsimp at this; omega
      rw [Equiv.swap_apply_of_ne_of_ne hne_i hne_j]
  have hmid : ((List.ofFn (v ∘ Equiv.swap i j)).drop (i + 1)).take (j - i - 1) =
      ((List.ofFn v).drop (i + 1)).take (j - i - 1) := by
    apply List.ext_getElem
    · simp
    · intro k hk₁ hk₂
      simp only [List.getElem_take, List.getElem_drop, List.getElem_ofFn, Function.comp_apply]
      have hkj : k < j - i - 1 := by
        simp only [List.length_take, List.length_drop, List.length_ofFn] at hk₁; omega
      have hne_i : (⟨i + 1 + k, by omega⟩ : Fin n) ≠ i := fun h => by
        have := congrArg Fin.val h; dsimp at this; omega
      have hne_j : (⟨i + 1 + k, by omega⟩ : Fin n) ≠ j := fun h => by
        have := congrArg Fin.val h; dsimp at this; omega
      rw [Equiv.swap_apply_of_ne_of_ne hne_i hne_j]
  have hdrop : (List.ofFn (v ∘ Equiv.swap i j)).drop (j + 1) = (List.ofFn v).drop (j + 1) := by
    apply List.ext_getElem
    · simp
    · intro k hk₁ hk₂
      simp only [List.getElem_drop, List.getElem_ofFn, Function.comp_apply]
      have hlt : j + 1 + k < n := by
        simp only [List.length_drop, List.length_ofFn] at hk₁; omega
      have hne_i : (⟨j + 1 + k, hlt⟩ : Fin n) ≠ i := fun h => by
        have := congrArg Fin.val h; dsimp at this; omega
      have hne_j : (⟨j + 1 + k, hlt⟩ : Fin n) ≠ j := fun h => by
        have := congrArg Fin.val h; dsimp at this; omega
      rw [Equiv.swap_apply_of_ne_of_ne hne_i hne_j]
  refine ⟨_, _, _, hsplit v, ?_⟩
  rw [hsplit (v ∘ Equiv.swap i j), htake, hmid, hdrop]
  simp

/-- Swapping two distinct entries `i ≠ j` of a Milnor symbol negates it. -/
theorem symbol_ofFn_comp_swap {n : ℕ} (v : Fin n → Fˣ) {i j : Fin n} (hij : i ≠ j) :
    symbol (List.ofFn (v ∘ Equiv.swap i j)) = -symbol (List.ofFn v) := by
  rcases lt_or_gt_of_ne hij with hlt | hgt
  · obtain ⟨l₁, l₂, l₃, hv, hvs⟩ := exists_split_ofFn_swap v hlt
    rw [hv, hvs, symbol_swap_middle]
  · rw [Equiv.swap_comm]
    obtain ⟨l₁, l₂, l₃, hv, hvs⟩ := exists_split_ofFn_swap v hgt
    rw [hv, hvs, symbol_swap_middle]

/-- **Skew-symmetry of Milnor symbols**: permuting the entries of a Milnor symbol multiplies it
by the sign of the permutation. -/
theorem symbol_ofFn_comp_perm {n : ℕ} (v : Fin n → Fˣ) (σ : Equiv.Perm (Fin n)) :
    symbol (List.ofFn (v ∘ σ)) = (Equiv.Perm.sign σ : ℤ) • symbol (List.ofFn v) := by
  induction σ using Equiv.Perm.swap_induction_on generalizing v with
  | one => simp
  | swap_mul f i j hij ih =>
    have hcomp : v ∘ (Equiv.swap i j * f) = (v ∘ Equiv.swap i j) ∘ f := rfl
    rw [hcomp, ih (v ∘ Equiv.swap i j), symbol_ofFn_comp_swap v hij, smul_neg, map_mul,
      Equiv.Perm.sign_swap hij, Units.val_mul, Units.val_neg, Units.val_one, neg_one_mul, neg_zsmul]

/-! ### Repeated and opposite entries -/

/-- A repeated adjacent entry in a Milnor symbol may be replaced by `a, -1`. -/
theorem symbol_self_middle (l₁ : List Fˣ) (a : Fˣ) (l₂ : List Fˣ) :
    symbol (l₁ ++ a :: a :: l₂) = symbol (l₁ ++ a :: (-1) :: l₂) := by
  simp only [symbol_append, symbol_cons, ← mul_assoc]
  rw [mul_assoc (symbol l₁) (ofUnit a) (ofUnit a), ofUnit_mul_self, ← mul_assoc]

/-- A Milnor symbol containing two adjacent opposite entries `a, -a` vanishes. -/
@[simp]
theorem symbol_neg_self_middle (l₁ : List Fˣ) (a : Fˣ) (l₂ : List Fˣ) :
    symbol (l₁ ++ a :: (-a) :: l₂) = 0 := by
  simp only [symbol_append, symbol_cons, ← mul_assoc]
  rw [mul_assoc (symbol l₁) (ofUnit a) (ofUnit (-a)), ofUnit_mul_neg_self, mul_zero, zero_mul]

/-- A Milnor symbol containing opposite entries `v j = -v i` at distinct positions vanishes. -/
theorem symbol_neg_self_of_ne {n : ℕ} (v : Fin n → Fˣ) {i j : Fin n} (hij : i ≠ j)
    (h : v j = -v i) : symbol (List.ofFn v) = 0 := by
  have hvanish : ∀ (l₁ l₂ l₃ : List Fˣ) (a : Fˣ),
      symbol (l₁ ++ a :: (l₂ ++ (-a) :: l₃)) = 0 := by
    intro l₁ l₂ l₃ a
    have hinner : ofUnit a * symbol l₂ * ofUnit (-a) = 0 := by
      calc
        ofUnit a * symbol l₂ * ofUnit (-a)
          = ((-1 : ℤ) ^ l₂.length • (symbol l₂ * ofUnit a)) * ofUnit (-a) := by
            rw [ofUnit_mul_symbol a l₂]
        _ = (-1 : ℤ) ^ l₂.length • ((symbol l₂ * ofUnit a) * ofUnit (-a)) :=
            smul_mul_assoc ((-1 : ℤ) ^ l₂.length) (symbol l₂ * ofUnit a) (ofUnit (-a))
        _ = (-1 : ℤ) ^ l₂.length • (symbol l₂ * (ofUnit a * ofUnit (-a))) := by
            rw [mul_assoc]
        _ = 0 := by rw [ofUnit_mul_neg_self, mul_zero, smul_zero]
    simp only [symbol_append, symbol_cons]
    calc
      symbol l₁ * (ofUnit a * (symbol l₂ * (ofUnit (-a) * symbol l₃)))
        = symbol l₁ * ((ofUnit a * symbol l₂ * ofUnit (-a)) * symbol l₃) := by
          simp only [mul_assoc]
      _ = 0 := by rw [hinner, zero_mul, mul_zero]
  rcases lt_or_gt_of_ne hij with hlt | hgt
  · obtain ⟨l₁, l₂, l₃, hv, -⟩ := exists_split_ofFn_swap v hlt
    rw [hv, h]
    exact hvanish l₁ l₂ l₃ (v i)
  · obtain ⟨l₁, l₂, l₃, hv, -⟩ := exists_split_ofFn_swap v hgt
    have hi : v i = -v j := by rw [h, neg_neg]
    rw [hv, hi]
    exact hvanish l₁ l₂ l₃ (v j)

/-- A Milnor symbol with a repeated entry is `2`-torsion. -/
theorem two_nsmul_symbol_of_duplicate {n : ℕ} (v : Fin n → Fˣ) {i j : Fin n} (hij : i ≠ j)
    (h : v i = v j) : 2 • symbol (List.ofFn v) = 0 := by
  have hswap : v ∘ Equiv.swap i j = v := by
    funext k
    by_cases hki : k = i
    · subst hki; simp [h]
    · by_cases hkj : k = j
      · subst hkj; simp [h]
      · simp [Equiv.swap_apply_of_ne_of_ne hki hkj]
  have hneg := symbol_ofFn_comp_swap v hij
  rw [hswap] at hneg
  rw [two_nsmul]
  calc
    symbol (List.ofFn v) + symbol (List.ofFn v)
      = -symbol (List.ofFn v) + symbol (List.ofFn v) := congrArg (· + symbol (List.ofFn v)) hneg
    _ = 0 := neg_add_cancel _

/-- Over a field of characteristic `2`, any Milnor symbol with a repeated entry vanishes. -/
theorem symbol_eq_zero_of_duplicate_of_charTwo [CharP F 2] {n : ℕ} (v : Fin n → Fˣ)
    {i j : Fin n} (hij : i ≠ j) (h : v i = v j) :
    symbol (List.ofFn v) = 0 := by
  apply symbol_neg_self_of_ne v hij
  ext
  simp only [Units.val_neg, h]
  exact (CharTwo.neg_eq _).symm

end TauCeti.MilnorK
