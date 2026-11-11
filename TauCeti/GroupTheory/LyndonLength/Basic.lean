/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Order.Hom.GroupNorm
public import Mathlib.Data.ZMod.Defs
public import Mathlib.GroupTheory.DivisibleHull
import TauCeti.Algebra.Order.Group.MinMax

/-!
# Lyndon length functions

Let `Λ` be a linearly ordered abelian group and `G` a group. A *Lyndon length function* is a map
`l : G → Λ` with

* (L1) `l 1 = 0` (and `l g ≥ 0`, which follows from the other axioms);
* (L2) `l g⁻¹ = l g`;
* (L3) `c(g, f) > c(g, h) → c(g, h) = c(f, h)`,

where `c(g, f) = (l g + l f - l (g⁻¹ * f)) / 2` is the *Gromov product*. It lies in the
divisible hull of `Λ`, Mathlib's `DivisibleHull Λ`, which is again a linearly ordered abelian
group. A Lyndon length function is *free* when moreover (L4) every Gromov product lies in `Λ` and
(L5) `l (g ^ 2) > l g` for `g ≠ 1`, and *regular* when (L6) any two elements `g`, `f` have a
common initial segment `u` of length `c(g, f)`: `g = u * g₁` and `f = u * f₁` with
`l g = l u + l g₁` and `l f = l u + l f₁`.

The based length function `g ↦ d(x, g • x)` of an isometric action on a `Λ`-tree is a Lyndon
length function. Conversely, by Chiswell's theorem every Lyndon length function whose Gromov
products lie in `Λ`, i.e. which satisfies (L4), arises in this way; in general the Gromov products
lie in `½Λ ⊆ DivisibleHull Λ`, and the length function arises from an action on a `½Λ`-tree. Free
Lyndon length functions are those of free actions without inversions. Freeness and regularity are
independent properties; the main example of a free regular length function is the word length
on a free group (`TauCeti.LyndonLength.freeGroupNorm`).

Axiom (L3) is equivalent to the ultrametric (`0`-hyperbolicity) inequality
`min (c(g, f), c(f, h)) ≤ c(g, h)` (`TauCeti.LyndonLength.min_gromovProduct_le`), and it implies the
triangle inequality `l (g * f) ≤ l g + l f`. Thus Lyndon length functions are `Λ`-valued group
seminorms in the sense of Mathlib's `GroupSeminormClass`, and `map_mul_le_add`, `apply_nonneg`,
`map_one_eq_zero` and `map_inv_eq_map` apply to them.

## Main definitions

* `TauCeti.LyndonLength G Λ`: Lyndon length functions `G → Λ`.
* `TauCeti.LyndonLength.gromovProduct`: the Gromov product `c(g, f)` in `DivisibleHull Λ`.
* `TauCeti.LyndonLength.IsFree`: axioms (L4) and (L5).
* `TauCeti.LyndonLength.IsRegular`: axiom (L6).
* `TauCeti.LyndonLength.comap`: restriction along a group homomorphism.
* `TauCeti.LyndonLength.absLength`: the absolute value of a linearly ordered abelian group, a free
  regular Lyndon length function, the length function of the action of `Λ` on itself by
  translations.
* `TauCeti.LyndonLength.discrete`: the length function that is `1` off the identity.

## Main results

* `TauCeti.LyndonLength.gromovProduct_eq_of_lt`: axiom (L3) for the Gromov product.
* `TauCeti.LyndonLength.min_gromovProduct_le`: Gromov products are `0`-hyperbolic.
* `TauCeti.LyndonLength.gromovProduct_nonneg`, `TauCeti.LyndonLength.gromovProduct_le_left`,
  `TauCeti.LyndonLength.gromovProduct_le_right`: `0 ≤ c(g, f) ≤ min (l g) (l f)`.
* `TauCeti.LyndonLength.IsFree.comap`: restriction along an injective homomorphism preserves
  freeness.
* `TauCeti.LyndonLength.isFree_zero_iff`: the zero length function is free only on the trivial
  group.
* `TauCeti.LyndonLength.IsFree.sq_ne_one`: a group with a free Lyndon length function has no
  elements of order two. In particular `TauCeti.LyndonLength.discrete` is not free on `ℤ/2`.
* `TauCeti.LyndonLength.isFree_absLength`, `TauCeti.LyndonLength.isRegular_absLength`: the
  absolute value of a linearly ordered abelian group, for instance of `Lex (Fin 2 → ℤ)`, is free
  and regular.

## References

* R. C. Lyndon, *Length functions in groups*, Math. Scand. 12 (1963), 209–234.
* I. Chiswell, *Introduction to Λ-trees*, World Scientific, 2001, Chapter 2.
* O. Kharlampovich, A. Myasnikov, V. Remeslennikov, D. Serbin, *Groups with free regular length
  functions in `ℤⁿ`*, Trans. Amer. Math. Soc. 364 (2012), 2847–2882, §2.1–§2.2.
* A. Myasnikov, V. Remeslennikov, D. Serbin, *Regular free length functions on Lyndon's free
  `ℤ[t]`-group `F^{ℤ[t]}`*, Contemp. Math. 378 (2005), §2.
-/

public section

namespace TauCeti

/-- A *Lyndon length function* on a group `G` with values in a linearly ordered abelian group `Λ`:
a map `l : G → Λ` with `l 1 = 0`, `l g⁻¹ = l g` and the axiom (L3)
`c(g, f) > c(g, h) → c(g, h) = c(f, h)` on the Gromov products
`c(g, f) = (l g + l f - l (g⁻¹ * f)) / 2`. Since halving is strictly monotone, (L3) is stated
for the doubled Gromov products, which lie in `Λ`; see
`TauCeti.LyndonLength.gromovProduct_eq_of_lt` for the statement in terms of
`TauCeti.LyndonLength.gromovProduct`. Nonnegativity of `l` follows from these axioms
(`apply_nonneg`). -/
structure LyndonLength (G Λ : Type*) [Group G] [AddCommGroup Λ] [LinearOrder Λ] where
  /-- The length function. -/
  toFun : G → Λ
  /-- (L1) The identity has length zero. -/
  map_one' : toFun 1 = 0
  /-- (L2) Inverse elements have the same length. -/
  map_inv' : ∀ g, toFun g⁻¹ = toFun g
  /-- (L3), for twice the Gromov product. -/
  eq_of_lt' : ∀ g f h,
    toFun g + toFun h - toFun (g⁻¹ * h) < toFun g + toFun f - toFun (g⁻¹ * f) →
      toFun g + toFun h - toFun (g⁻¹ * h) = toFun f + toFun h - toFun (f⁻¹ * h)

namespace LyndonLength

variable {G H Λ : Type*} [Group G] [Group H] [AddCommGroup Λ] [LinearOrder Λ]

instance : FunLike (LyndonLength G Λ) G Λ where
  coe := toFun
  coe_injective l l' h := by
    cases l
    cases l'
    congr

@[ext]
theorem ext {l l' : LyndonLength G Λ} (h : ∀ g, l g = l' g) : l = l' :=
  DFunLike.ext _ _ h

@[simp]
theorem toFun_eq_coe (l : LyndonLength G Λ) : l.toFun = l :=
  (rfl)

@[simp]
theorem coe_mk (l : G → Λ) (h₁ h₂ h₃) : ⇑(⟨l, h₁, h₂, h₃⟩ : LyndonLength G Λ) = l :=
  (rfl)

/-- The Gromov product `c(g, f) = (l g + l f - l (g⁻¹ * f)) / 2` of a Lyndon length function, in
the divisible hull of `Λ`. -/
def gromovProduct (l : LyndonLength G Λ) (g f : G) : DivisibleHull Λ :=
  DivisibleHull.mk (l g + l f - l (g⁻¹ * f)) 2

/-- The zero length function. -/
instance : Zero (LyndonLength G Λ) where
  zero :=
    { toFun := 0
      map_one' := rfl
      map_inv' _ := rfl
      eq_of_lt' _ _ _ h := by simp at h }

@[simp]
theorem coe_zero : ⇑(0 : LyndonLength G Λ) = 0 :=
  (rfl)

variable [IsOrderedAddMonoid Λ]

/-- Lyndon length functions are `Λ`-valued group seminorms. The triangle inequality
`l (g * f) ≤ l g + l f` is nonnegativity of the Gromov product `c(g⁻¹, f)`, which follows from
(L3) because `c(g⁻¹, 1) = c(1, f) = 0`. -/
instance : GroupSeminormClass (LyndonLength G Λ) G Λ where
  map_mul_le_add l g f := by
    by_contra! hlt
    have h := l.eq_of_lt' g⁻¹ 1 f
    simp only [toFun_eq_coe, inv_inv, mul_one, inv_one, one_mul, l.map_one', l.map_inv',
      zero_add, add_zero, sub_self] at h
    have hlt' : l g + l f - l (g * f) < 0 := sub_neg.2 hlt
    exact hlt'.ne (h hlt')
  map_one_eq_zero l := l.map_one'
  map_inv_eq_map l := l.map_inv'

variable (l : LyndonLength G Λ) {g f h g' f' : G}

/-- Twice the Gromov product is `l g + l f - l (g⁻¹ * f)`, an element of `Λ`. -/
theorem two_nsmul_gromovProduct (g f : G) :
    2 • l.gromovProduct g f = ((l g + l f - l (g⁻¹ * f) : Λ) : DivisibleHull Λ) := by
  simp only [gromovProduct, DivisibleHull.nsmul_mk, DivisibleHull.mk_eq_mk_iff_smul_eq_smul]
  simp

/-- Gromov products compare as their doubles in `Λ`. -/
theorem gromovProduct_le_gromovProduct_iff :
    l.gromovProduct g f ≤ l.gromovProduct g' f' ↔
      l g + l f - l (g⁻¹ * f) ≤ l g' + l f' - l (g'⁻¹ * f') := by
  simp [gromovProduct]

/-- Gromov products compare strictly as their doubles in `Λ`. -/
theorem gromovProduct_lt_gromovProduct_iff :
    l.gromovProduct g f < l.gromovProduct g' f' ↔
      l g + l f - l (g⁻¹ * f) < l g' + l f' - l (g'⁻¹ * f') := by
  simp only [lt_iff_le_not_ge, gromovProduct_le_gromovProduct_iff]

/-- Two Gromov products are equal exactly when their doubles in `Λ` are. -/
theorem gromovProduct_eq_gromovProduct_iff :
    l.gromovProduct g f = l.gromovProduct g' f' ↔
      l g + l f - l (g⁻¹ * f) = l g' + l f' - l (g'⁻¹ * f') := by
  simp only [le_antisymm_iff, gromovProduct_le_gromovProduct_iff]

/-- An element `c` of `Λ` is the Gromov product `c(g, f)` exactly when
`2 • c = l g + l f - l (g⁻¹ * f)`. -/
theorem coe_eq_gromovProduct_iff {c : Λ} :
    (c : DivisibleHull Λ) = l.gromovProduct g f ↔ 2 • c = l g + l f - l (g⁻¹ * f) := by
  simp [gromovProduct, DivisibleHull.mk_eq_mk_iff_smul_eq_smul]

/-- An element `c` of `Λ` is at most `c(g, f)` exactly when `2 • c ≤ l g + l f - l (g⁻¹ * f)`. -/
theorem coe_le_gromovProduct_iff {c : Λ} :
    (c : DivisibleHull Λ) ≤ l.gromovProduct g f ↔ 2 • c ≤ l g + l f - l (g⁻¹ * f) := by
  simp [gromovProduct]

/-- The Gromov product `c(g, f)` is at most an element `c` of `Λ` exactly when
`l g + l f - l (g⁻¹ * f) ≤ 2 • c`. -/
theorem gromovProduct_le_coe_iff {c : Λ} :
    l.gromovProduct g f ≤ (c : DivisibleHull Λ) ↔ l g + l f - l (g⁻¹ * f) ≤ 2 • c := by
  simp [gromovProduct]

/-- Axiom (L3): if `c(g, f) > c(g, h)` then `c(g, h) = c(f, h)`. -/
theorem gromovProduct_eq_of_lt (hlt : l.gromovProduct g h < l.gromovProduct g f) :
    l.gromovProduct g h = l.gromovProduct f h := by
  rw [gromovProduct_lt_gromovProduct_iff] at hlt
  rw [gromovProduct_eq_gromovProduct_iff]
  simpa only [toFun_eq_coe] using l.eq_of_lt' g f h hlt

@[simp]
theorem gromovProduct_one_right (g : G) : l.gromovProduct g 1 = 0 := by
  simp [gromovProduct]

@[simp]
theorem gromovProduct_one_left (f : G) : l.gromovProduct 1 f = 0 := by
  simp [gromovProduct]

@[simp]
theorem gromovProduct_self (g : G) : l.gromovProduct g g = l g := by
  rw [eq_comm, coe_eq_gromovProduct_iff]
  simp [two_nsmul]

/-- The Gromov product is symmetric, by (L2). -/
theorem gromovProduct_comm (g f : G) : l.gromovProduct g f = l.gromovProduct f g := by
  rw [gromovProduct_eq_gromovProduct_iff, ← map_inv_eq_map l (g⁻¹ * f), mul_inv_rev, inv_inv,
    add_comm (l g)]

/-- Gromov products are nonnegative. This is the triangle inequality for `g⁻¹` and `f`. -/
theorem gromovProduct_nonneg (g f : G) : 0 ≤ l.gromovProduct g f := by
  rw [← DivisibleHull.mk_zero 1]
  refine (l.coe_le_gromovProduct_iff (c := 0)).2 ?_
  simpa [sub_nonneg] using map_mul_le_add l g⁻¹ f

/-- The Gromov product `c(g, f)` is at most `l g`. -/
theorem gromovProduct_le_left (g f : G) : l.gromovProduct g f ≤ l g := by
  rw [gromovProduct_le_coe_iff, two_nsmul, sub_le_iff_le_add, add_assoc, add_le_add_iff_left]
  simpa using map_mul_le_add l g (g⁻¹ * f)

/-- The Gromov product `c(g, f)` is at most `l f`. -/
theorem gromovProduct_le_right (g f : G) : l.gromovProduct g f ≤ l f := by
  rw [gromovProduct_comm]
  exact l.gromovProduct_le_left f g

/-- Gromov products of a Lyndon length function are `0`-hyperbolic:
`min (c(g, f), c(f, h)) ≤ c(g, h)`. Given (L1) and (L2), this inequality is equivalent to (L3). -/
theorem min_gromovProduct_le (g f h : G) :
    min (l.gromovProduct g f) (l.gromovProduct f h) ≤ l.gromovProduct g h := by
  by_contra! hlt
  exact (lt_min_iff.1 hlt).2.ne (l.gromovProduct_eq_of_lt (lt_min_iff.1 hlt).1)

/-! ### Free and regular length functions -/

/-- A Lyndon length function is *free* when (L4) every Gromov product lies in `Λ` and (L5)
`l g < l (g ^ 2)` for every `g ≠ 1`. -/
structure IsFree (l : LyndonLength G Λ) : Prop where
  /-- (L4) Gromov products lie in `Λ`. -/
  exists_coe_eq_gromovProduct : ∀ g f, ∃ c : Λ, (c : DivisibleHull Λ) = l.gromovProduct g f
  /-- (L5) Squaring increases the length of every nontrivial element. -/
  lt_map_sq : ∀ g, g ≠ 1 → l g < l (g ^ 2)

/-- A Lyndon length function is *regular* when (L6) any two elements `g`, `f` have a common
initial segment of length `c(g, f)`: there are `u`, `g₁`, `f₁` with `g = u * g₁`,
`f = u * f₁`, `l g = l u + l g₁`, `l f = l u + l f₁` and `l u = c(g, f)`. -/
def IsRegular (l : LyndonLength G Λ) : Prop :=
  ∀ g f, ∃ u g₁ f₁, g = u * g₁ ∧ f = u * f₁ ∧ l g = l u + l g₁ ∧ l f = l u + l f₁ ∧
    (l u : DivisibleHull Λ) = l.gromovProduct g f

omit [IsOrderedAddMonoid Λ] in
theorem isRegular_iff : l.IsRegular ↔ ∀ g f, ∃ u g₁ f₁, g = u * g₁ ∧ f = u * f₁ ∧
    l g = l u + l g₁ ∧ l f = l u + l f₁ ∧ (l u : DivisibleHull Λ) = l.gromovProduct g f :=
  Iff.rfl

/-- A group with a free Lyndon length function has no elements of order two. -/
theorem IsFree.sq_ne_one {l : LyndonLength G Λ} (hl : l.IsFree) (hg : g ≠ 1) : g ^ 2 ≠ 1 := by
  intro h
  have := hl.lt_map_sq g hg
  rw [h, map_one_eq_zero] at this
  exact (apply_nonneg l g).not_gt this

/-! ### Restriction along a homomorphism -/

/-- The restriction `h ↦ l (φ h)` of a Lyndon length function along a group homomorphism. -/
def comap (φ : H →* G) : LyndonLength H Λ where
  toFun h := l (φ h)
  map_one' := by simp
  map_inv' h := by simp
  eq_of_lt' g f h := by
    simpa only [map_mul, map_inv, toFun_eq_coe] using l.eq_of_lt' (φ g) (φ f) (φ h)

@[simp]
theorem comap_apply (φ : H →* G) (h : H) : l.comap φ h = l (φ h) :=
  (rfl)

@[simp]
theorem gromovProduct_comap (φ : H →* G) (g f : H) :
    (l.comap φ).gromovProduct g f = l.gromovProduct (φ g) (φ f) := by
  simp [gromovProduct]

@[simp]
theorem comap_id : l.comap (MonoidHom.id G) = l :=
  (rfl)

theorem comap_comp {K : Type*} [Group K] (φ : H →* G) (ψ : K →* H) :
    (l.comap φ).comap ψ = l.comap (φ.comp ψ) :=
  (rfl)

@[simp]
theorem comap_zero (φ : H →* G) : (0 : LyndonLength G Λ).comap φ = 0 :=
  (rfl)

/-- Restriction along an injective homomorphism preserves freeness. -/
theorem IsFree.comap {l : LyndonLength G Λ} (hl : l.IsFree) {φ : H →* G}
    (hφ : Function.Injective φ) : (l.comap φ).IsFree where
  exists_coe_eq_gromovProduct g f := by simpa using hl.exists_coe_eq_gromovProduct (φ g) (φ f)
  lt_map_sq g hg := by
    simpa using hl.lt_map_sq (φ g) ((map_ne_one_iff φ hφ).2 hg)

/-! ### Examples -/

/-- The zero length function is free exactly on the trivial group. -/
theorem isFree_zero_iff : (0 : LyndonLength G Λ).IsFree ↔ Subsingleton G := by
  refine ⟨fun h => ⟨fun g f => ?_⟩, fun _ => ⟨fun g f => ⟨0, ?_⟩, fun g hg => ?_⟩⟩
  · have key : ∀ x : G, x = 1 := fun x => by
      by_contra hx
      simpa using h.lt_map_sq x hx
    rw [key g, key f]
  · rw [coe_eq_gromovProduct_iff]
    simp
  · exact absurd (Subsingleton.elim g 1) hg

variable (G) in
/-- The length function on `G` that is `0` at the identity and `1` elsewhere. -/
def discrete [DecidableEq G] : LyndonLength G ℤ where
  toFun g := if g = 1 then 0 else 1
  map_one' := by simp
  map_inv' g := by simp
  eq_of_lt' g f h := by
    -- The doubled Gromov products only depend on which of `g`, `f`, `h` are trivial or equal.
    simp only [inv_mul_eq_one]
    by_cases hg : g = 1 <;> by_cases hf : f = 1 <;> by_cases hh : h = 1 <;>
      by_cases hgf : g = f <;> by_cases hfh : f = h <;> by_cases hgh : g = h <;>
      simp_all

@[simp]
theorem discrete_apply [DecidableEq G] (g : G) : discrete G g = if g = 1 then 0 else 1 :=
  (rfl)

/-- On `ℤ/2`, the length function that is `1` off the identity is not free: (L5) fails for the
generator, whose square is trivial. -/
theorem not_isFree_discrete_zmod_two : ¬(discrete (Multiplicative (ZMod 2))).IsFree := fun h =>
  h.sq_ne_one (g := Multiplicative.ofAdd 1) (by decide) (by decide)

variable (Λ) in
/-- The absolute value `|a|` on a linearly ordered abelian group `Λ`, written multiplicatively,
as a Lyndon length function. It is the based length function, at `0`, of the action of `Λ` on
the `Λ`-tree `Λ` by translations. -/
def absLength : LyndonLength (Multiplicative Λ) Λ where
  toFun a := |a.toAdd|
  map_one' := by simp
  map_inv' a := by simp
  eq_of_lt' a b c := by
    simp only [toAdd_mul, toAdd_inv]
    -- Remove every absolute value by a case split on signs; each case is linear arithmetic.
    rcases abs_cases a.toAdd with ⟨ha, -⟩ | ⟨ha, -⟩ <;>
      rcases abs_cases b.toAdd with ⟨hb, -⟩ | ⟨hb, -⟩ <;>
      rcases abs_cases c.toAdd with ⟨hc, -⟩ | ⟨hc, -⟩ <;>
      rcases abs_cases (-a.toAdd + c.toAdd) with ⟨hac, -⟩ | ⟨hac, -⟩ <;>
      rcases abs_cases (-a.toAdd + b.toAdd) with ⟨hab, -⟩ | ⟨hab, -⟩ <;>
      rcases abs_cases (-b.toAdd + c.toAdd) with ⟨hbc, -⟩ | ⟨hbc, -⟩ <;>
      rw [ha, hb, hc, hac, hab, hbc] <;> grind

@[simp]
theorem absLength_apply (a : Multiplicative Λ) : absLength Λ a = |a.toAdd| :=
  (rfl)

/-- The absolute value of a linearly ordered abelian group is a free Lyndon length function. -/
theorem isFree_absLength : (absLength Λ).IsFree where
  exists_coe_eq_gromovProduct a b := by
    refine ⟨|max 0 (min a.toAdd b.toAdd) + min 0 (max a.toAdd b.toAdd)|, ?_⟩
    rw [coe_eq_gromovProduct_iff]
    simpa [neg_add_eq_sub] using two_nsmul_abs_max_zero_min_add_min_zero_max a.toAdd b.toAdd
  lt_map_sq a ha := by
    have ha' : a.toAdd ≠ 0 := by simpa using ha
    simp only [absLength_apply, toAdd_pow, two_nsmul]
    rcases ha'.lt_or_gt with h | h
    · rw [abs_of_neg h, abs_of_neg (by grind)]
      grind
    · rw [abs_of_pos h, abs_of_pos (by grind)]
      grind

/-- The absolute value of a linearly ordered abelian group is a regular Lyndon length function:
`a` and `b` have the common initial segment `min a b` if both are nonnegative, `max a b` if both
are nonpositive, and `0` otherwise. -/
theorem isRegular_absLength : (absLength Λ).IsRegular := by
  intro a b
  have ha := abs_max_zero_min_add_min_zero_max_add_abs_sub a.toAdd b.toAdd
  have hb := abs_max_zero_min_add_min_zero_max_add_abs_sub b.toAdd a.toAdd
  have hu := two_nsmul_abs_max_zero_min_add_min_zero_max a.toAdd b.toAdd
  rw [min_comm b.toAdd, max_comm b.toAdd] at hb
  set u := max 0 (min a.toAdd b.toAdd) + min 0 (max a.toAdd b.toAdd)
  refine ⟨.ofAdd u, .ofAdd (-u + a.toAdd), .ofAdd (-u + b.toAdd), ?_, ?_, ?_, ?_, ?_⟩
  · simp [← ofAdd_add]
  · simp [← ofAdd_add]
  · simpa [neg_add_eq_sub] using ha.symm
  · simpa [neg_add_eq_sub] using hb.symm
  · rw [coe_eq_gromovProduct_iff]
    simpa [neg_add_eq_sub] using hu

end LyndonLength

end TauCeti
