/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.RootSystem.Base

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

## Main definitions

* `TauCeti.NormalCrystal`: a normal crystal over a root datum with a base.
* `TauCeti.NormalCrystal.dual`: the dual crystal, exchanging `e` with `f`, `ε` with `φ` and
  negating the weight.
* `TauCeti.NormalCrystal.eIter`, `TauCeti.NormalCrystal.fIter`: iterated root operators.
* `TauCeti.NormalCrystal.StrictHom`: strict morphisms of normal crystals, with identities,
  composition and duals.
* `TauCeti.NormalCrystal.StrictIso`: strict isomorphisms of normal crystals, with inverses,
  composition and duals.
* `TauCeti.NormalCrystal.transport`: the transport of a normal crystal along a bijection of the
  underlying types, with the strict isomorphism `TauCeti.NormalCrystal.transportIso`.

## Main results

* `TauCeti.NormalCrystal.ext`: a normal crystal is determined by `wt` and `e`.
* `TauCeti.NormalCrystal.isSome_eIter_iff`, `TauCeti.NormalCrystal.isSome_fIter_iff`: the string
  identities `e i ^ n x ≠ 0 ↔ n ≤ ε i x` and `f i ^ n x ≠ 0 ↔ n ≤ φ i x`, with the weight and
  string-length changes `TauCeti.NormalCrystal.wt_of_eIter_eq_some`,
  `TauCeti.NormalCrystal.ε_of_eIter_eq_some` and their lowering counterparts.
* `TauCeti.NormalCrystal.StrictHom.ε_apply`, `TauCeti.NormalCrystal.StrictHom.φ_apply`,
  `TauCeti.NormalCrystal.StrictHom.f_apply`: a map preserving weights and commuting with the
  raising operators preserves the string lengths and commutes with the lowering operators.
* `TauCeti.NormalCrystal.StrictIso.eq_transport`: the target of a strict isomorphism is the
  transport of its source along the underlying bijection.

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

end StrictHom

/-! ### Strict isomorphisms and transport -/

/-- A **strict isomorphism** of normal crystals: a bijection of the underlying types preserving
weights and commuting with the raising operators. Its inverse is again a strict isomorphism
(`TauCeti.NormalCrystal.StrictIso.symm`). -/
structure StrictIso (c : NormalCrystal P b B) (d : NormalCrystal P b B') extends B ≃ B' where
  /-- A strict isomorphism preserves weights. -/
  wt_toFun (x : B) : d.wt (toFun x) = c.wt x
  /-- A strict isomorphism commutes with the raising operators. -/
  e_toFun (i : b.support) (x : B) : d.e i (toFun x) = (c.e i x).map toFun

namespace StrictIso

variable {c : NormalCrystal P b B} {d : NormalCrystal P b B'} {d' : NormalCrystal P b B''}

instance : EquivLike (StrictIso c d) B B' where
  coe ψ := ψ.toFun
  inv ψ := ψ.invFun
  left_inv ψ := ψ.left_inv
  right_inv ψ := ψ.right_inv
  coe_injective' ψ χ h _ := by
    obtain ⟨ψ, _, _⟩ := ψ
    obtain ⟨χ, _, _⟩ := χ
    congr
    exact Equiv.coe_fn_injective h

@[simp]
theorem coe_toEquiv (ψ : StrictIso c d) : ⇑ψ.toEquiv = ψ := (rfl)

@[simp]
theorem coe_mk (g : B ≃ B') (hwt he) : ⇑(⟨g, hwt, he⟩ : StrictIso c d) = g := (rfl)

@[ext]
theorem ext {ψ χ : StrictIso c d} (h : ∀ x, ψ x = χ x) : ψ = χ :=
  DFunLike.ext _ _ h

/-- The strict morphism underlying a strict isomorphism. -/
def toStrictHom (ψ : StrictIso c d) : StrictHom c d where
  toFun := ψ
  wt_toFun := ψ.wt_toFun
  e_toFun := ψ.e_toFun

@[simp]
theorem coe_toStrictHom (ψ : StrictIso c d) : ⇑ψ.toStrictHom = ψ := (rfl)

variable (ψ : StrictIso c d) (i : b.support) (x : B)

@[simp]
theorem wt_apply : d.wt (ψ x) = c.wt x := ψ.wt_toFun x

@[simp]
theorem e_apply : d.e i (ψ x) = (c.e i x).map ψ := ψ.e_toFun i x

@[simp]
theorem ε_apply : d.ε i (ψ x) = c.ε i x := ψ.toStrictHom.ε_apply i x

@[simp]
theorem φ_apply : d.φ i (ψ x) = c.φ i x := ψ.toStrictHom.φ_apply i x

@[simp]
theorem f_apply : d.f i (ψ x) = (c.f i x).map ψ := ψ.toStrictHom.f_apply i x

variable (c) in
/-- The identity strict isomorphism. -/
def refl : StrictIso c c where
  toEquiv := Equiv.refl B
  wt_toFun _ := rfl
  e_toFun _ x := by simp

@[simp]
theorem refl_apply : StrictIso.refl c x = x := (rfl)

/-- The inverse of a strict isomorphism. -/
def symm : StrictIso d c where
  toEquiv := ψ.toEquiv.symm
  wt_toFun y := by
    obtain ⟨x, rfl⟩ := ψ.toEquiv.surjective y
    rw [Equiv.toFun_as_coe, Equiv.symm_apply_apply, coe_toEquiv, wt_apply]
  e_toFun i y := by
    obtain ⟨x, rfl⟩ := ψ.toEquiv.surjective y
    rw [Equiv.toFun_as_coe, Equiv.symm_apply_apply, coe_toEquiv, e_apply, Option.map_map]
    simp [← coe_toEquiv, Function.comp_def]

@[simp]
theorem toEquiv_symm : ψ.symm.toEquiv = ψ.toEquiv.symm := (rfl)

@[simp]
theorem coe_toEquiv_symm : ⇑ψ.toEquiv.symm = ψ.symm := (rfl)

@[simp]
theorem symm_apply_apply : ψ.symm (ψ x) = x := ψ.toEquiv.symm_apply_apply x

@[simp]
theorem apply_symm_apply (y : B') : ψ (ψ.symm y) = y := ψ.toEquiv.apply_symm_apply y

@[simp]
theorem symm_symm : ψ.symm.symm = ψ := (rfl)

/-- Composition of strict isomorphisms. -/
def trans (χ : StrictIso d d') : StrictIso c d' where
  toEquiv := ψ.toEquiv.trans χ.toEquiv
  wt_toFun x := by simp
  e_toFun i x := by simp [Option.map_map, Function.comp_def]

@[simp]
theorem trans_apply (χ : StrictIso d d') : ψ.trans χ x = χ (ψ x) := (rfl)

@[simp]
theorem self_trans_symm : ψ.trans ψ.symm = StrictIso.refl c := ext fun x => by simp

@[simp]
theorem symm_trans_self : ψ.symm.trans ψ = StrictIso.refl d := ext fun x => by simp

/-- A bijective strict morphism is a strict isomorphism. -/
noncomputable def ofBijective (ψ : StrictHom c d) (h : Function.Bijective ψ) : StrictIso c d where
  toEquiv := Equiv.ofBijective ψ h
  wt_toFun := ψ.wt_apply
  e_toFun := ψ.e_apply

@[simp]
theorem coe_ofBijective (ψ : StrictHom c d) (h : Function.Bijective ψ) :
    ⇑(ofBijective ψ h) = ψ := (rfl)

/-- A strict isomorphism is also a strict isomorphism between the dual crystals. -/
def dual : StrictIso c.dual d.dual where
  toEquiv := ψ.toEquiv
  wt_toFun x := by simp
  e_toFun i x := by simp

@[simp]
theorem dual_apply : ψ.dual x = ψ x := (rfl)

end StrictIso

section Transport

variable (c : NormalCrystal P b B) (σ : B ≃ B')

/-- The **transport** of a normal crystal along a bijection `σ : B ≃ B'`: the normal crystal on
`B'` for which `σ` is a strict isomorphism (`TauCeti.NormalCrystal.transportIso`). -/
def transport : NormalCrystal P b B' where
  wt y := c.wt (σ.symm y)
  e i y := (c.e i (σ.symm y)).map σ
  f i y := (c.f i (σ.symm y)).map σ
  ε i y := c.ε i (σ.symm y)
  φ i y := c.φ i (σ.symm y)
  f_eq_some_iff {i x y} := by
    simp only [Option.map_eq_some_iff, ← Equiv.eq_symm_apply, exists_eq_right, c.f_eq_some_iff]
  wt_of_e_eq_some {i x y} h := by
    obtain ⟨z, hz, rfl⟩ := Option.map_eq_some_iff.1 h
    rw [Equiv.symm_apply_apply, c.wt_of_e_eq_some hz]
  ε_eq_zero_iff := by simp [c.ε_eq_zero_iff]
  ε_of_e_eq_some {i x y} h := by
    obtain ⟨z, hz, rfl⟩ := Option.map_eq_some_iff.1 h
    rw [Equiv.symm_apply_apply, c.ε_of_e_eq_some hz]
  φ_eq_zero_iff := by simp [c.φ_eq_zero_iff]
  φ_sub_ε i y := c.φ_sub_ε i (σ.symm y)

@[simp]
theorem transport_wt (y : B') : (c.transport σ).wt y = c.wt (σ.symm y) := (rfl)

@[simp]
theorem transport_e (i : b.support) (y : B') :
    (c.transport σ).e i y = (c.e i (σ.symm y)).map σ := (rfl)

@[simp]
theorem transport_f (i : b.support) (y : B') :
    (c.transport σ).f i y = (c.f i (σ.symm y)).map σ := (rfl)

@[simp]
theorem transport_ε (i : b.support) (y : B') : (c.transport σ).ε i y = c.ε i (σ.symm y) := (rfl)

@[simp]
theorem transport_φ (i : b.support) (y : B') : (c.transport σ).φ i y = c.φ i (σ.symm y) := (rfl)

/-- The bijection `σ` as a strict isomorphism onto the transported crystal. -/
def transportIso : StrictIso c (c.transport σ) where
  toEquiv := σ
  wt_toFun x := by simp
  e_toFun i x := by simp

@[simp]
theorem coe_transportIso : ⇑(c.transportIso σ) = σ := (rfl)

/-- **Uniqueness of transport**: the target of a strict isomorphism is the transport of its
source along the underlying bijection. -/
theorem StrictIso.eq_transport {d : NormalCrystal P b B'} (ψ : StrictIso c d) :
    d = c.transport ψ.toEquiv :=
  NormalCrystal.ext (funext fun y => by obtain ⟨x, rfl⟩ := ψ.toEquiv.surjective y; simp)
    (funext₂ fun i y => by obtain ⟨x, rfl⟩ := ψ.toEquiv.surjective y; simp)

end Transport

end NormalCrystal

end TauCeti
