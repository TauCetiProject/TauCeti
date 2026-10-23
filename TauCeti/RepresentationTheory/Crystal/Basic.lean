/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.RootSystem.Base
public import Mathlib.Logic.Equiv.Option

/-!
# Normal crystals over a root datum

Fix a root datum `P : RootDatum ι X Y` with a base `b`, so that the simple roots are the
`P.root i` and the simple coroots the `P.coroot i` for `i : b.support`. A *normal crystal* over
`(P, b)` is a type `B` with a weight map `wt : B → X`, raising and lowering operators
`e i, f i : B → Option B` (with `none` playing the role of Kashiwara's `0`) and natural numbers
`ε i x`, `φ i x` such that

* `f i` and `e i` are partial inverses: `f i x = some y ↔ e i y = some x`;
* raising adds the simple root to the weight and lowers `ε i` by one;
* `ε i x` is the length of the `e i`-string above `x` and `φ i x` that of the `f i`-string below
  it, which is encoded by `ε i x = 0 ↔ e i x = none`, `φ i x = 0 ↔ f i x = none` and the shift of
  `ε i` along `e i`;
* `φ i x - ε i x = ⟨wt x, α_i^∨⟩`.

These are Kashiwara's crystal axioms together with his *seminormality* condition, which Joseph
and the path-model literature call *normality*; since `ε i` and `φ i` are natural numbers every
string is finite. Crystals of Littelmann paths and of integrable highest weight modules are of
this kind.

The structure records `ε` and `φ` as data, but `TauCeti.NormalCrystal.ext` shows that a normal
crystal is determined by its weight map and its raising operators: the lowering operators and the
string lengths carry no further freedom.

A bijection of the underlying types transports a normal crystal structure
(`TauCeti.NormalCrystal.congr`): the weight and the string lengths are pulled back and the root
operators are conjugated, and the bijection itself is a strict isomorphism.

## Main definitions

* `TauCeti.NormalCrystal`: a normal crystal over a root datum with a base.
* `TauCeti.NormalCrystal.dual`: the dual crystal, exchanging `e` with `f`, `ε` with `φ` and
  negating the weight.
* `TauCeti.NormalCrystal.eIter`, `TauCeti.NormalCrystal.fIter`: iterated root operators.
* `TauCeti.NormalCrystal.StrictHom`: strict morphisms of normal crystals, with identities,
  composition and duals.
* `TauCeti.NormalCrystal.congr`: transport of a normal crystal along a bijection of its
  underlying type.
* `TauCeti.NormalCrystal.StrictHom.congr`, `TauCeti.NormalCrystal.StrictHom.congrInv`: the strict
  isomorphism implementing the transport and its inverse.

## Main results

* `TauCeti.NormalCrystal.ext`: a normal crystal is determined by `wt` and `e`.
* `TauCeti.NormalCrystal.isSome_eIter_iff`, `TauCeti.NormalCrystal.isSome_fIter_iff`: the string
  identities `e i ^ n x ≠ 0 ↔ n ≤ ε i x` and `f i ^ n x ≠ 0 ↔ n ≤ φ i x`, with the weight and
  string-length changes `TauCeti.NormalCrystal.wt_of_eIter_eq_some`,
  `TauCeti.NormalCrystal.ε_of_eIter_eq_some` and their lowering counterparts.
* `TauCeti.NormalCrystal.StrictHom.ε_apply`, `TauCeti.NormalCrystal.StrictHom.φ_apply`,
  `TauCeti.NormalCrystal.StrictHom.f_apply`: a map preserving weights and commuting with the
  raising operators preserves the string lengths and commutes with the lowering operators.
* `TauCeti.NormalCrystal.congr_refl`, `TauCeti.NormalCrystal.congr_trans`: functoriality of the
  transport.
* `TauCeti.NormalCrystal.congr_dual`: transport commutes with the dual crystal.
* `TauCeti.NormalCrystal.congr_e_eq_some_iff`,
  `TauCeti.NormalCrystal.congr_f_eq_some_iff`: transport at the level of the root operators.
* `TauCeti.NormalCrystal.StrictHom.congrInv_comp_congr`,
  `TauCeti.NormalCrystal.StrictHom.congr_comp_congrInv`: the two composites of the transport
  isomorphism are identities.
* `TauCeti.NormalCrystal.StrictHom.eq_congr_of_bijective`: a bijective strict morphism exhibits
  its target as the transport of its source.

## References

* M. Kashiwara, *On crystal bases*, CMS Conf. Proc. 16 (1995), §7.
* A. Joseph, *Quantum groups and their primitive ideals*, Springer (1995), §5.2.
* D. Bump and A. Schilling, *Crystal bases: representations and combinatorics*, World Scientific
  (2017), Ch. 2.
* P. Littelmann, *Paths and root operators in representation theory*, Ann. of Math. 142 (1995).
-/

public section

namespace TauCeti

universe u v w x₁ x₂ x₃

variable {ι : Type u} {X : Type v} {Y : Type w} [AddCommGroup X] [AddCommGroup Y]
  (P : RootDatum ι X Y) (b : P.Base)

/-- A **normal crystal** over the root datum `P` with base `b`: a weight map, partial raising and
lowering operators `e i`, `f i` indexed by the simple roots, and natural string lengths `ε i`,
`φ i`, satisfying Kashiwara's crystal axioms together with normality (`ε i x` and `φ i x` are the
lengths of the `e i`- and `f i`-strings through `x`). The value `none` of `e i` or `f i` stands
for Kashiwara's `0`. -/
structure NormalCrystal (B : Type x₁) where
  /-- The weight map. -/
  wt : B → X
  /-- The raising operator attached to a simple root. -/
  e : b.support → B → Option B
  /-- The lowering operator attached to a simple root. -/
  f : b.support → B → Option B
  /-- The length of the raising string above an element. -/
  ε : b.support → B → ℕ
  /-- The length of the lowering string below an element. -/
  φ : b.support → B → ℕ
  /-- Lowering and raising are partial inverses. -/
  f_eq_some_iff {i : b.support} {x y : B} : f i x = some y ↔ e i y = some x
  /-- Raising adds the simple root to the weight. -/
  wt_of_e_eq_some {i : b.support} {x y : B} : e i x = some y → wt y = wt x + P.root i
  /-- The raising string above `x` is empty exactly when `e i x` is undefined. -/
  ε_eq_zero_iff {i : b.support} {x : B} : ε i x = 0 ↔ e i x = none
  /-- Raising shortens the raising string by one. -/
  ε_of_e_eq_some {i : b.support} {x y : B} : e i x = some y → ε i y + 1 = ε i x
  /-- The lowering string below `x` is empty exactly when `f i x` is undefined. -/
  φ_eq_zero_iff {i : b.support} {x : B} : φ i x = 0 ↔ f i x = none
  /-- The difference of the string lengths is the pairing of the weight with the coroot. -/
  φ_sub_ε (i : b.support) (x : B) :
    (φ i x : ℤ) - ε i x = P.toLinearMap (wt x) (P.coroot i)

namespace NormalCrystal

variable {P b} {B : Type x₁} {B' : Type x₂} {B'' : Type x₃}

section Basic

variable (c : NormalCrystal P b B) {i : b.support} {x y : B}

theorem e_eq_some_iff : c.e i x = some y ↔ c.f i y = some x :=
  c.f_eq_some_iff.symm

theorem e_ne_none_iff : c.e i x ≠ none ↔ c.ε i x ≠ 0 :=
  c.ε_eq_zero_iff.symm.not

theorem f_ne_none_iff : c.f i x ≠ none ↔ c.φ i x ≠ 0 :=
  c.φ_eq_zero_iff.symm.not

/-- Lowering subtracts the simple root from the weight. -/
theorem wt_of_f_eq_some (h : c.f i x = some y) : c.wt y = c.wt x - P.root i := by
  rw [c.wt_of_e_eq_some (c.f_eq_some_iff.1 h), add_sub_cancel_right]

/-- Lowering lengthens the raising string by one. -/
theorem ε_of_f_eq_some (h : c.f i x = some y) : c.ε i y = c.ε i x + 1 :=
  (c.ε_of_e_eq_some (c.f_eq_some_iff.1 h)).symm

/-- Raising lengthens the lowering string by one. -/
theorem φ_of_e_eq_some (h : c.e i x = some y) : c.φ i y = c.φ i x + 1 := by
  have hy := c.φ_sub_ε i y
  have hx := c.φ_sub_ε i x
  have hε := c.ε_of_e_eq_some h
  rw [c.wt_of_e_eq_some h, map_add, LinearMap.add_apply, P.root_coroot_two] at hy
  omega

/-- Lowering shortens the lowering string by one. -/
theorem φ_of_f_eq_some (h : c.f i x = some y) : c.φ i y + 1 = c.φ i x :=
  (c.φ_of_e_eq_some (c.f_eq_some_iff.1 h)).symm

/-- A map commuting with the raising operators preserves the lengths of raising strings. -/
theorem ε_apply_eq_of_e_map (d : NormalCrystal P b B') {g : B → B'}
    (hg : ∀ x, d.e i (g x) = (c.e i x).map g) (x : B) : d.ε i (g x) = c.ε i x := by
  suffices ∀ n x, c.ε i x = n → d.ε i (g x) = n from this _ x rfl
  intro n
  induction n with
  | zero => intro x hn; rw [d.ε_eq_zero_iff, hg, c.ε_eq_zero_iff.1 hn, Option.map_none]
  | succ n ih =>
    intro x hn
    obtain ⟨y, hy⟩ :=
      Option.ne_none_iff_exists'.1 ((c.e_ne_none_iff (i := i) (x := x)).2 (by omega))
    have hdy : d.e i (g x) = some (g y) := by rw [hg, hy, Option.map_some]
    have := c.ε_of_e_eq_some hy
    rw [← d.ε_of_e_eq_some hdy, ih y (by omega)]

/-- A weight-preserving map commuting with the raising operators preserves the lengths of
lowering strings. -/
theorem φ_apply_eq_of_e_map (d : NormalCrystal P b B') {g : B → B'}
    (hwt : ∀ x, d.wt (g x) = c.wt x) (hg : ∀ x, d.e i (g x) = (c.e i x).map g) (x : B) :
    d.φ i (g x) = c.φ i x := by
  have hd := d.φ_sub_ε i (g x)
  have hc := c.φ_sub_ε i x
  rw [hwt, c.ε_apply_eq_of_e_map d hg] at hd
  omega

/-- A weight-preserving map commuting with the raising operators commutes with the lowering
operators. -/
theorem f_apply_eq_of_e_map (d : NormalCrystal P b B') {g : B → B'}
    (hwt : ∀ x, d.wt (g x) = c.wt x) (hg : ∀ x, d.e i (g x) = (c.e i x).map g) (x : B) :
    d.f i (g x) = (c.f i x).map g := by
  cases h : c.f i x with
  | none =>
    rw [Option.map_none, ← d.φ_eq_zero_iff, c.φ_apply_eq_of_e_map d hwt hg, c.φ_eq_zero_iff, h]
  | some y =>
    rw [Option.map_some, d.f_eq_some_iff, hg, c.f_eq_some_iff.1 h, Option.map_some]

/-- **A normal crystal is determined by its weight map and its raising operators.** -/
@[ext]
theorem ext {c d : NormalCrystal P b B} (hwt : c.wt = d.wt) (he : c.e = d.e) : c = d := by
  have he' (i : b.support) (x : B) : d.e i (id x) = (c.e i x).map id := by simp [he]
  have hwt' (x : B) : d.wt (id x) = c.wt x := by simp [hwt]
  have hε : c.ε = d.ε := funext₂ fun i x => (c.ε_apply_eq_of_e_map d (he' i) x).symm
  have hφ : c.φ = d.φ := funext₂ fun i x => (c.φ_apply_eq_of_e_map d hwt' (he' i) x).symm
  have hf : c.f = d.f := funext₂ fun i x => by
    simpa using (c.f_apply_eq_of_e_map d hwt' (he' i) x).symm
  cases c; cases d
  simp_all

end Basic

/-! ### The dual crystal -/

section Dual

variable (c : NormalCrystal P b B)

/-- The **dual crystal**: the same underlying type with the raising and lowering operators and the
two string lengths exchanged and the weight negated. -/
def dual : NormalCrystal P b B where
  wt x := -c.wt x
  e := c.f
  f := c.e
  ε := c.φ
  φ := c.ε
  f_eq_some_iff := c.e_eq_some_iff
  wt_of_e_eq_some h := by rw [c.wt_of_f_eq_some h, neg_sub, sub_eq_neg_add]
  ε_eq_zero_iff := c.φ_eq_zero_iff
  ε_of_e_eq_some h := c.φ_of_f_eq_some h
  φ_eq_zero_iff := c.ε_eq_zero_iff
  φ_sub_ε i x := by
    rw [map_neg, LinearMap.neg_apply, ← c.φ_sub_ε i x, neg_sub]

@[simp]
theorem dual_wt (x : B) : c.dual.wt x = -c.wt x := (rfl)

@[simp]
theorem dual_e : c.dual.e = c.f := (rfl)

@[simp]
theorem dual_f : c.dual.f = c.e := (rfl)

@[simp]
theorem dual_ε : c.dual.ε = c.φ := (rfl)

@[simp]
theorem dual_φ : c.dual.φ = c.ε := (rfl)

@[simp]
theorem dual_dual : c.dual.dual = c :=
  ext (funext fun x => by simp) (by simp)

end Dual

/-! ### Strings -/

section Strings

variable (c : NormalCrystal P b B)

/-- The `n`-fold raising operator `e i ^ n`, as a partial map. -/
def eIter (i : b.support) : ℕ → B → Option B
  | 0, x => some x
  | n + 1, x => (c.e i x).bind (eIter i n)

/-- The `n`-fold lowering operator `f i ^ n`, as a partial map. -/
def fIter (i : b.support) : ℕ → B → Option B
  | 0, x => some x
  | n + 1, x => (c.f i x).bind (fIter i n)

variable {i : b.support} {n : ℕ} {x y : B}

@[simp]
theorem eIter_zero (x : B) : c.eIter i 0 x = some x := (rfl)

theorem eIter_succ (n : ℕ) (x : B) : c.eIter i (n + 1) x = (c.e i x).bind (c.eIter i n) := (rfl)

@[simp]
theorem fIter_zero (x : B) : c.fIter i 0 x = some x := (rfl)

theorem fIter_succ (n : ℕ) (x : B) : c.fIter i (n + 1) x = (c.f i x).bind (c.fIter i n) := (rfl)

@[simp]
theorem eIter_one (x : B) : c.eIter i 1 x = c.e i x := by
  simp [eIter_succ]

@[simp]
theorem fIter_one (x : B) : c.fIter i 1 x = c.f i x := by
  simp [fIter_succ]

theorem eIter_succ' (n : ℕ) (x : B) : c.eIter i (n + 1) x = (c.eIter i n x).bind (c.e i) := by
  induction n generalizing x with
  | zero => simp [eIter_succ]
  | succ n ih =>
    rw [eIter_succ, eIter_succ c n, Option.bind_assoc]
    exact congrArg _ (funext ih)

@[simp]
theorem dual_eIter : c.dual.eIter = c.fIter := by
  funext i n x
  induction n generalizing x with
  | zero => rfl
  | succ n ih => simp only [eIter_succ, fIter_succ, dual_e, ih]

@[simp]
theorem dual_fIter : c.dual.fIter = c.eIter := by
  simpa using c.dual.dual_eIter.symm

theorem fIter_succ' (n : ℕ) (x : B) : c.fIter i (n + 1) x = (c.fIter i n x).bind (c.f i) := by
  simpa using c.dual.eIter_succ' n x

/-- Raising `n` times adds `n` copies of the simple root to the weight. -/
theorem wt_of_eIter_eq_some (h : c.eIter i n x = some y) : c.wt y = c.wt x + n • P.root i := by
  induction n generalizing x with
  | zero => simp_all
  | succ n ih =>
    rw [eIter_succ, Option.bind_eq_some_iff] at h
    obtain ⟨z, hz, h⟩ := h
    rw [ih h, c.wt_of_e_eq_some hz, succ_nsmul', add_assoc]

/-- Raising `n` times shortens the raising string by `n`. -/
theorem ε_of_eIter_eq_some (h : c.eIter i n x = some y) : c.ε i y + n = c.ε i x := by
  induction n generalizing x with
  | zero => simp_all
  | succ n ih =>
    rw [eIter_succ, Option.bind_eq_some_iff] at h
    obtain ⟨z, hz, h⟩ := h
    rw [← c.ε_of_e_eq_some hz, ← ih h, add_assoc]

/-- **String identity for raising**: `e i ^ n x` is defined exactly when `n ≤ ε i x`. -/
@[simp]
theorem isSome_eIter_iff : (c.eIter i n x).isSome ↔ n ≤ c.ε i x := by
  induction n generalizing x with
  | zero => simp
  | succ n ih =>
    rw [eIter_succ]
    cases h : c.e i x with
    | none => simp [c.ε_eq_zero_iff.2 h]
    | some z => rw [Option.bind_some, ih, ← c.ε_of_e_eq_some h, Nat.add_le_add_iff_right]

@[simp]
theorem eIter_eq_none_iff : c.eIter i n x = none ↔ c.ε i x < n := by
  rw [← Option.not_isSome_iff_eq_none, c.isSome_eIter_iff, not_le]

/-- Lowering `n` times subtracts `n` copies of the simple root from the weight. -/
theorem wt_of_fIter_eq_some (h : c.fIter i n x = some y) : c.wt y = c.wt x - n • P.root i := by
  rw [← dual_eIter] at h
  have := c.dual.wt_of_eIter_eq_some h
  simp only [dual_wt] at this
  rw [sub_eq_add_neg, ← neg_neg (c.wt y), this, neg_add, neg_neg]

/-- Lowering `n` times shortens the lowering string by `n`. -/
theorem φ_of_fIter_eq_some (h : c.fIter i n x = some y) : c.φ i y + n = c.φ i x := by
  rw [← dual_eIter] at h
  simpa using c.dual.ε_of_eIter_eq_some h

/-- **String identity for lowering**: `f i ^ n x` is defined exactly when `n ≤ φ i x`. -/
@[simp]
theorem isSome_fIter_iff : (c.fIter i n x).isSome ↔ n ≤ c.φ i x := by
  simpa using c.dual.isSome_eIter_iff (i := i) (n := n) (x := x)

@[simp]
theorem fIter_eq_none_iff : c.fIter i n x = none ↔ c.φ i x < n := by
  rw [← Option.not_isSome_iff_eq_none, c.isSome_fIter_iff, not_le]

/-- The iterated root operators are partial inverses of each other. -/
theorem fIter_eq_some_iff : c.fIter i n x = some y ↔ c.eIter i n y = some x := by
  induction n generalizing x y with
  | zero => simp [eq_comm]
  | succ n ih =>
    simp only [fIter_succ, eIter_succ', Option.bind_eq_some_iff, ih, c.f_eq_some_iff]
    exact ⟨fun ⟨z, hz, hy⟩ => ⟨z, hy, hz⟩, fun ⟨z, hy, hz⟩ => ⟨z, hz, hy⟩⟩

end Strings

/-! ### Transport along a bijection -/

section Congr

variable (c : NormalCrystal P b B) (e : B ≃ B')

/-- Transport of an option along a bijection: `y` is the image of exactly the preimage of `y`.
This is the form in which `Equiv.optionCongr` is used to conjugate the root operators. -/
private theorem map_equiv_eq_some_iff {e : B ≃ B'} {o : Option B} {y : B'} :
    o.map e = some y ↔ o = some (e.symm y) := by
  rw [Option.map_eq_some_iff]
  constructor
  · rintro ⟨a, ha, rfl⟩
    rw [ha, Equiv.symm_apply_apply]
  · rintro rfl
    exact ⟨e.symm y, rfl, Equiv.apply_symm_apply e y⟩

/-- **Transport of a normal crystal along a bijection**: the weight and the string lengths are
pulled back along `e` and the root operators are conjugated by `e`. -/
def congr : NormalCrystal P b B' where
  wt x := c.wt (e.symm x)
  e i x := (c.e i (e.symm x)).map e
  f i x := (c.f i (e.symm x)).map e
  ε i x := c.ε i (e.symm x)
  φ i x := c.φ i (e.symm x)
  f_eq_some_iff := by
    intro i x y
    rw [map_equiv_eq_some_iff, map_equiv_eq_some_iff, c.f_eq_some_iff]
  wt_of_e_eq_some := by
    intro i x y h
    exact c.wt_of_e_eq_some (map_equiv_eq_some_iff.1 h)
  ε_eq_zero_iff := by
    intro i x
    rw [Option.map_eq_none_iff]
    exact c.ε_eq_zero_iff
  ε_of_e_eq_some := by
    intro i x y h
    exact c.ε_of_e_eq_some (map_equiv_eq_some_iff.1 h)
  φ_eq_zero_iff := by
    intro i x
    rw [Option.map_eq_none_iff]
    exact c.φ_eq_zero_iff
  φ_sub_ε := fun i x => c.φ_sub_ε i (e.symm x)

@[simp]
theorem congr_wt (x : B') : (c.congr e).wt x = c.wt (e.symm x) := (rfl)

@[simp]
theorem congr_e (i : b.support) (x : B') :
    (c.congr e).e i x = (c.e i (e.symm x)).map e := (rfl)

@[simp]
theorem congr_f (i : b.support) (x : B') :
    (c.congr e).f i x = (c.f i (e.symm x)).map e := (rfl)

@[simp]
theorem congr_ε (i : b.support) (x : B') :
    (c.congr e).ε i x = c.ε i (e.symm x) := (rfl)

@[simp]
theorem congr_φ (i : b.support) (x : B') :
    (c.congr e).φ i x = c.φ i (e.symm x) := (rfl)

/-- Transport along a bijection, at the level of the raising operators: the raising operator of the
transport is the transported raising operator of the source. -/
theorem congr_e_eq_some_iff (i : b.support) (x y : B') :
    (c.congr e).e i x = some y ↔ c.e i (e.symm x) = some (e.symm y) := by
  rw [congr_e, map_equiv_eq_some_iff]

/-- Transport along a bijection, at the level of the lowering operators. -/
theorem congr_f_eq_some_iff (i : b.support) (x y : B') :
    (c.congr e).f i x = some y ↔ c.f i (e.symm x) = some (e.symm y) := by
  rw [congr_f, map_equiv_eq_some_iff]

/-- Transport along the identity bijection is the identity. -/
@[simp]
theorem congr_refl : c.congr (Equiv.refl B) = c :=
  NormalCrystal.ext (funext fun x => by simp) (funext₂ fun i x => by simp)

/-- Transport along a composite bijection is the composite of the transports. -/
@[simp]
theorem congr_trans (e' : B' ≃ B'') :
    (c.congr e).congr e' = c.congr (e.trans e') :=
  NormalCrystal.ext (funext fun x => by simp) (funext₂ fun i x => by simp)

/-- Transport commutes with the dual crystal. -/
@[simp]
theorem congr_dual : (c.congr e).dual = c.dual.congr e := (rfl)

end Congr

/-! ### Strict morphisms -/

/-- A **strict morphism** of normal crystals: a map of the underlying types preserving weights and
commuting with the raising operators. It then also preserves the string lengths and commutes with
the lowering operators (`TauCeti.NormalCrystal.StrictHom.ε_apply`,
`TauCeti.NormalCrystal.StrictHom.φ_apply`, `TauCeti.NormalCrystal.StrictHom.f_apply`). -/
structure StrictHom (c : NormalCrystal P b B) (d : NormalCrystal P b B') where
  /-- The underlying map. -/
  toFun : B → B'
  /-- A strict morphism preserves weights. -/
  wt_toFun (x : B) : d.wt (toFun x) = c.wt x
  /-- A strict morphism commutes with the raising operators. -/
  e_toFun (i : b.support) (x : B) : d.e i (toFun x) = (c.e i x).map toFun

namespace StrictHom

variable {c : NormalCrystal P b B} {d : NormalCrystal P b B'} {d' : NormalCrystal P b B''}

instance : FunLike (StrictHom c d) B B' where
  coe := toFun
  coe_injective ψ χ h := by cases ψ; cases χ; congr

@[simp]
theorem toFun_eq_coe (ψ : StrictHom c d) : ψ.toFun = ψ := (rfl)

@[simp]
theorem coe_mk (g : B → B') (hwt he) : ⇑(⟨g, hwt, he⟩ : StrictHom c d) = g := (rfl)

@[ext]
theorem ext {ψ χ : StrictHom c d} (h : ∀ x, ψ x = χ x) : ψ = χ :=
  DFunLike.ext _ _ h

variable (ψ : StrictHom c d) (i : b.support) (x : B)

@[simp]
theorem wt_apply : d.wt (ψ x) = c.wt x := ψ.wt_toFun x

@[simp]
theorem e_apply : d.e i (ψ x) = (c.e i x).map ψ := ψ.e_toFun i x

@[simp]
theorem ε_apply : d.ε i (ψ x) = c.ε i x :=
  c.ε_apply_eq_of_e_map d (ψ.e_apply i) x

@[simp]
theorem φ_apply : d.φ i (ψ x) = c.φ i x :=
  c.φ_apply_eq_of_e_map d ψ.wt_apply (ψ.e_apply i) x

@[simp]
theorem f_apply : d.f i (ψ x) = (c.f i x).map ψ :=
  c.f_apply_eq_of_e_map d ψ.wt_apply (ψ.e_apply i) x

@[simp]
theorem eIter_apply (n : ℕ) : d.eIter i n (ψ x) = (c.eIter i n x).map ψ := by
  induction n generalizing x with
  | zero => rfl
  | succ n ih =>
    rw [eIter_succ, eIter_succ, e_apply]
    cases c.e i x <;> simp [ih]

@[simp]
theorem fIter_apply (n : ℕ) : d.fIter i n (ψ x) = (c.fIter i n x).map ψ := by
  induction n generalizing x with
  | zero => rfl
  | succ n ih =>
    rw [fIter_succ, fIter_succ, f_apply]
    cases c.f i x <;> simp [ih]

variable (c) in
/-- The identity strict morphism. -/
def id : StrictHom c c where
  toFun x := x
  wt_toFun _ := rfl
  e_toFun _ x := by simp

@[simp]
theorem id_apply : StrictHom.id c x = x := (rfl)

/-- Composition of strict morphisms. -/
def comp (χ : StrictHom d d') (ψ : StrictHom c d) : StrictHom c d' where
  toFun x := χ (ψ x)
  wt_toFun x := by simp
  e_toFun i x := by simp [Option.map_map, Function.comp_def]

@[simp]
theorem comp_apply (χ : StrictHom d d') : χ.comp ψ x = χ (ψ x) := (rfl)

@[simp]
theorem comp_id : ψ.comp (StrictHom.id c) = ψ := (rfl)

@[simp]
theorem id_comp : (StrictHom.id d).comp ψ = ψ := (rfl)

theorem comp_assoc {B''' : Type*} {d'' : NormalCrystal P b B'''} (θ : StrictHom d' d'')
    (χ : StrictHom d d') : (θ.comp χ).comp ψ = θ.comp (χ.comp ψ) := (rfl)

/-- A strict morphism is also a strict morphism between the dual crystals. -/
def dual : StrictHom c.dual d.dual where
  toFun := ψ
  wt_toFun x := by simp
  e_toFun i x := by simp

@[simp]
theorem dual_apply : ψ.dual x = ψ x := (rfl)

/-- The bijection underlying the transport is a strict morphism. -/
def congr (c : NormalCrystal P b B) (e : B ≃ B') : StrictHom c (c.congr e) where
  toFun := ⇑e
  wt_toFun x := by simp
  e_toFun i x := by simp

/-- The inverse of the strict morphism underlying the transport. -/
def congrInv (c : NormalCrystal P b B) (e : B ≃ B') : StrictHom (c.congr e) c where
  toFun := ⇑e.symm
  wt_toFun x := by simp
  e_toFun i x := by simp [congr_e, Option.map_map]

@[simp]
theorem congr_apply (c : NormalCrystal P b B) (e : B ≃ B') (x : B) :
    StrictHom.congr c e x = e x := (rfl)

@[simp]
theorem congrInv_apply (c : NormalCrystal P b B) (e : B ≃ B') (x : B') :
    StrictHom.congrInv c e x = e.symm x := (rfl)

@[simp]
theorem congrInv_comp_congr (c : NormalCrystal P b B) (e : B ≃ B') :
    (StrictHom.congrInv c e).comp (StrictHom.congr c e) = StrictHom.id c := by
  ext x
  simp

@[simp]
theorem congr_comp_congrInv (c : NormalCrystal P b B) (e : B ≃ B') :
    (StrictHom.congr c e).comp (StrictHom.congrInv c e) = StrictHom.id (c.congr e) := by
  ext x
  simp

/-- A bijective strict morphism exhibits its target as the transport of its source along the
underlying equivalence. -/
theorem eq_congr_of_bijective {c : NormalCrystal P b B} {d : NormalCrystal P b B'}
    {ψ : StrictHom c d} (h : Function.Bijective ψ) :
    d = c.congr (Equiv.ofBijective ψ h) := by
  refine NormalCrystal.ext (funext fun x => ?_) (funext₂ fun i x => ?_)
  · rw [congr_wt]
    conv_lhs => rw [← Equiv.apply_symm_apply (Equiv.ofBijective ψ h) x]
    exact ψ.wt_apply _
  · rw [congr_e]
    conv_lhs => rw [← Equiv.apply_symm_apply (Equiv.ofBijective ψ h) x]
    exact ψ.e_apply _ _

end StrictHom

end NormalCrystal

end TauCeti
