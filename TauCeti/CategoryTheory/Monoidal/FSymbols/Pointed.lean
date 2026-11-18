/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.ZMod.Basic
public import TauCeti.CategoryTheory.GradedObject.Twisted.Braided
public import TauCeti.CategoryTheory.Monoidal.FSymbols.Map

/-!
# Pointed fusion rules, 3-cocycles, and `ℤ/2` examples

A fusion rule is **pointed** when the simples form a monoid `I` and `N_{ab}^c = [a + b = c]`.
Every composite basis space `Left a b c d` and `Right a b c d` then has cardinality `1` when
`a + b + c = d` and `0` otherwise, collapsing the F- and R-symbol equations to scalar equations:

* `TauCeti.FusionRules.ofAddMonoid I` and `TauCeti.FusionRules.ofMonoid G`: pointed fusion rules.
* `TauCeti.FSymbols.twistingCocycleEquiv`: equivalence between `FSymbols R (ofAddMonoid I)` and
  `TauCeti.GradedObject.TwistingCocycle I R` (Quinn, §5), with `F^{abc}_{a+b+c} = (ω a b c)⁻¹`.
* `TauCeti.RSymbols.pointedBraidingEquiv`: equivalence between `RSymbols (ofTwistingCocycle c)` and
  abelian `3`-cocycle braidings `TauCeti.GradedObject.PointedBraiding c` (Joyal–Street, §3).
* `TauCeti.FSymbols.zmod2Equiv` and `TauCeti.RSymbols.zmod2Equiv`: classification on `ZMod 2` via
  `{ u : Rˣ // u * u = 1 }` (`F^{111}_1 = u`) and `{ r : Rˣ // r * r = u }` (`R^{11}_0 = r`),
  including `RSymbols.zmod2Super` (`u = 1`, `r = -1`) and `RSymbols.instIsEmptyZMod2NegOneInt`.

## References

* [P. Etingof, S. Gelaki, D. Nikshych, V. Ostrik, *Tensor Categories*][egno15], §2.3 (Ex. 2.3.8),
  §2.6 (Prop. 2.6.1), and §8.4 (abelian `3`-cocycles).
* A. Joyal and R. Street, *Braided tensor categories*, Adv. Math. **102** (1993), 20–78, §3.
* F. Quinn, *Group categories and their field theories*, Geom. Topol. Monogr. **2** (1999),
  407–453, §5.
-/

public section

namespace TauCeti

universe u v

/-! ### Pointed fusion rules -/

namespace FusionRules

/-- Pointed fusion rules on an additive monoid `I`, with `unit = 0` and
`N a b c = if a + b = c then 1 else 0`. -/
def ofAddMonoid (I : Type u) [AddMonoid I] [DecidableEq I] : FusionRules I where
  unit := 0
  N a b c := if a + b = c then 1 else 0
  N_unit_left _ _ := by simp
  N_unit_right _ _ := by simp

@[simp] theorem ofAddMonoid_unit (I : Type u) [AddMonoid I] [DecidableEq I] :
    (ofAddMonoid I).unit = 0 := (rfl)
@[simp] theorem ofAddMonoid_N (I : Type u) [AddMonoid I] [DecidableEq I] (a b c : I) :
    (ofAddMonoid I).N a b c = if a + b = c then 1 else 0 := (rfl)

/-- Pointed fusion rules on a multiplicative monoid `G`, with `unit = 1` and
`N a b c = if a * b = c then 1 else 0`. -/
def ofMonoid (G : Type u) [Monoid G] [DecidableEq G] : FusionRules G where
  unit := 1
  N a b c := if a * b = c then 1 else 0
  N_unit_left _ _ := by simp
  N_unit_right _ _ := by simp

@[simp] theorem ofMonoid_unit (G : Type u) [Monoid G] [DecidableEq G] :
    (ofMonoid G).unit = 1 := (rfl)
@[simp] theorem ofMonoid_N (G : Type u) [Monoid G] [DecidableEq G] (a b c : G) :
    (ofMonoid G).N a b c = if a * b = c then 1 else 0 := (rfl)

/-- Reindexing `ofAddMonoid (Additive G)` along `Additive.toMul` recovers `ofMonoid G`. -/
@[simp] theorem reindex_ofAddMonoid_additive (G : Type u) [Monoid G] [DecidableEq G] :
    (ofAddMonoid (Additive G)).reindex Additive.toMul = ofMonoid G := by ext <;> simp [← ofMul_mul]

section AddMonoidHelpers

variable {I : Type u} [AddMonoid I] [DecidableEq I]

/-- An index in `Fin ((ofAddMonoid I).N a b c)` witnesses `a + b = c`. -/
theorem eq_of_fin_ofAddMonoid {a b c : I} (i : Fin ((ofAddMonoid I).N a b c)) : a + b = c := by
  by_contra h; exact Nat.not_lt_zero i.val (by simpa [h] using i.isLt)

/-- The canonical basis index in `Fin ((ofAddMonoid I).N a b c)` when `a + b = c`. -/
def ofAddMonoidIdx {a b c : I} (h : a + b = c) : Fin ((ofAddMonoid I).N a b c) := ⟨0, by simp [h]⟩

@[simp] theorem val_ofAddMonoidIdx {a b c : I} (h : a + b = c) : (ofAddMonoidIdx h).val = 0 := (rfl)

theorem fin_ofAddMonoid_eq {a b c : I} (h : a + b = c) (i : Fin ((ofAddMonoid I).N a b c)) :
    i = ofAddMonoidIdx h := Fin.ext (by simpa [h] using i.isLt)

theorem eq_of_left_ofAddMonoid {a b c d : I} (x : (ofAddMonoid I).Left a b c d) :
    a + b + c = d := by rw [eq_of_fin_ofAddMonoid x.2.1, eq_of_fin_ofAddMonoid x.2.2]

theorem eq_of_right_ofAddMonoid {a b c d : I} (y : (ofAddMonoid I).Right a b c d) :
    a + b + c = d := by rw [add_assoc, eq_of_fin_ofAddMonoid y.2.1, eq_of_fin_ofAddMonoid y.2.2]

/-- The unique element of `(ofAddMonoid I).Left a b c d` when `a + b + c = d`. -/
def ofAddMonoidLeft {a b c d : I} (h : a + b + c = d) : (ofAddMonoid I).Left a b c d :=
  ⟨a + b, ofAddMonoidIdx rfl, ofAddMonoidIdx h⟩

@[simp] theorem ofAddMonoidLeft_fst {a b c d : I} (h : a + b + c = d) :
    (ofAddMonoidLeft h).1 = a + b := (rfl)
theorem ofAddMonoidLeft_def {a b c d : I} (h : a + b + c = d) :
    ofAddMonoidLeft h = ⟨a + b, ofAddMonoidIdx rfl, ofAddMonoidIdx h⟩ := (rfl)

/-- The unique element of `(ofAddMonoid I).Right a b c d` when `a + b + c = d`. -/
def ofAddMonoidRight {a b c d : I} (h : a + b + c = d) : (ofAddMonoid I).Right a b c d :=
  ⟨b + c, ofAddMonoidIdx rfl, ofAddMonoidIdx (by rwa [← add_assoc])⟩

@[simp] theorem ofAddMonoidRight_fst {a b c d : I} (h : a + b + c = d) :
    (ofAddMonoidRight h).1 = b + c := (rfl)
theorem ofAddMonoidRight_def {a b c d : I} (h : a + b + c = d) :
    ofAddMonoidRight h = ⟨b + c, ofAddMonoidIdx rfl, ofAddMonoidIdx (by rwa [← add_assoc])⟩ := (rfl)

theorem left_ofAddMonoid_eq {a b c d : I} (h : a + b + c = d)
    (x : (ofAddMonoid I).Left a b c d) : x = ofAddMonoidLeft h := by
  rcases x with ⟨_, i, j⟩; obtain rfl := eq_of_fin_ofAddMonoid i
  simp [ofAddMonoidLeft_def, fin_ofAddMonoid_eq rfl i, fin_ofAddMonoid_eq h j]

theorem right_ofAddMonoid_eq {a b c d : I} (h : a + b + c = d)
    (y : (ofAddMonoid I).Right a b c d) : y = ofAddMonoidRight h := by
  rcases y with ⟨_, k, l⟩; obtain rfl := eq_of_fin_ofAddMonoid k
  simp [ofAddMonoidRight_def, fin_ofAddMonoid_eq rfl k,
    fin_ofAddMonoid_eq (by rwa [← add_assoc]) l]

theorem sum_fin_ofAddMonoid_of_eq {M : Type*} [AddCommMonoid M] {a b c : I} (h : a + b = c)
    (f : Fin ((ofAddMonoid I).N a b c) → M) : ∑ i, f i = f (ofAddMonoidIdx h) :=
  Fintype.sum_eq_single (ofAddMonoidIdx h) fun i hi ↦ (hi (fin_ofAddMonoid_eq h i)).elim

theorem sum_fin_ofAddMonoid_of_ne {M : Type*} [AddCommMonoid M] {a b c : I} (h : a + b ≠ c)
    (f : Fin ((ofAddMonoid I).N a b c) → M) : ∑ i, f i = 0 :=
  have : IsEmpty (Fin ((ofAddMonoid I).N a b c)) := ⟨fun i ↦ h (eq_of_fin_ofAddMonoid i)⟩
  Fintype.sum_empty f

theorem sum_ofAddMonoid_fst {M : Type*} [AddCommMonoid M] [Fintype I] (a b : I)
    (g : ∀ e : I, Fin ((ofAddMonoid I).N a b e) → M) :
    ∑ e : I, ∑ i : Fin ((ofAddMonoid I).N a b e), g e i = g (a + b) (ofAddMonoidIdx rfl) := by
  rw [Fintype.sum_eq_single (a + b) fun e he ↦ sum_fin_ofAddMonoid_of_ne he.symm _,
    sum_fin_ofAddMonoid_of_eq rfl]

end AddMonoidHelpers

end FusionRules

/-! ### Equivalence between pointed F-symbols and normalized 3-cocycles -/

namespace FSymbols

section Pointed

open FusionRules (ofAddMonoid ofAddMonoidIdx ofAddMonoidLeft ofAddMonoidRight
  eq_of_fin_ofAddMonoid fin_ofAddMonoid_eq eq_of_left_ofAddMonoid eq_of_right_ofAddMonoid
  left_ofAddMonoid_eq right_ofAddMonoid_eq sum_fin_ofAddMonoid_of_eq sum_ofAddMonoid_fst)
open GradedObject (TwistingCocycle)

variable {R : Type v} [CommRing R] {I : Type u} [Fintype I] [DecidableEq I] [AddMonoid I]

private theorem ofAddMonoid_pentagon_sides
    (F : ∀ a b c' d : I, Matrix ((ofAddMonoid I).Left a b c' d) ((ofAddMonoid I).Right a b c' d) R)
    (φ : I → I → I → R) (hF : ∀ a b c' d x y, F a b c' d x y = φ a b c') {A B C D E p q r s : I}
    (i₁ : Fin ((ofAddMonoid I).N A B p)) (i₂ : Fin ((ofAddMonoid I).N p C q))
    (i₃ : Fin ((ofAddMonoid I).N q D E)) (k : Fin ((ofAddMonoid I).N C D r))
    (m : Fin ((ofAddMonoid I).N B r s)) (n : Fin ((ofAddMonoid I).N A s E)) :
    (∑ l : Fin ((ofAddMonoid I).N p r E),
        F p C D E ⟨q, i₂, i₃⟩ ⟨r, k, l⟩ * F A B r E ⟨p, i₁, l⟩ ⟨s, m, n⟩ =
      φ (A + B) C D * φ A B (C + D)) ∧
    (∑ t : I, ∑ j : Fin ((ofAddMonoid I).N B C t), ∑ j' : Fin ((ofAddMonoid I).N A t q),
        ∑ m' : Fin ((ofAddMonoid I).N t D s),
        F A B C q ⟨p, i₁, i₂⟩ ⟨t, j, j'⟩ * F A t D E ⟨q, j', i₃⟩ ⟨s, m', n⟩ *
          F B C D s ⟨t, j, m'⟩ ⟨r, k, m⟩ =
      φ A B C * φ A (B + C) D * φ B C D) := by
  obtain rfl := eq_of_fin_ofAddMonoid i₁; obtain rfl := eq_of_fin_ofAddMonoid i₂
  obtain rfl := eq_of_fin_ofAddMonoid i₃; obtain rfl := eq_of_fin_ofAddMonoid k
  obtain rfl := eq_of_fin_ofAddMonoid m
  refine ⟨by rw [sum_fin_ofAddMonoid_of_eq (add_assoc (A + B) C D).symm, hF, hF], ?_⟩
  rw [sum_ofAddMonoid_fst B C, sum_fin_ofAddMonoid_of_eq (add_assoc A B C).symm,
    sum_fin_ofAddMonoid_of_eq (add_assoc B C D), hF, hF, hF]

/-- The F-symbols attached to a normalized `3`-cocycle `c : TwistingCocycle I R`, with
`F^{abc}_{a+b+c} = (c.ω a b c)⁻¹` and `Finv^{abc}_{a+b+c} = c.ω a b c`. -/
def ofTwistingCocycle (c : TwistingCocycle I R) : FSymbols R (ofAddMonoid I) where
  F a b c' _ := Matrix.of fun _ _ ↦ (((c.ω a b c')⁻¹ : Rˣ) : R)
  Finv a b c' _ := Matrix.of fun _ _ ↦ (c.ω a b c' : R)
  F_mul_Finv a b c' d := by
    ext x₁ x₂; have h := eq_of_left_ofAddMonoid x₁
    rw [left_ofAddMonoid_eq h x₁, left_ofAddMonoid_eq h x₂, Matrix.mul_apply, Matrix.one_apply_eq,
      Fintype.sum_eq_single (ofAddMonoidRight h) fun y hy ↦ (hy (right_ofAddMonoid_eq h y)).elim]
    simp only [Matrix.of_apply, Units.inv_mul]
  Finv_mul_F a b c' d := by
    ext y₁ y₂; have h := eq_of_right_ofAddMonoid y₁
    rw [right_ofAddMonoid_eq h y₁, right_ofAddMonoid_eq h y₂, Matrix.mul_apply, Matrix.one_apply_eq,
      Fintype.sum_eq_single (ofAddMonoidLeft h) fun x hx ↦ (hx (left_ofAddMonoid_eq h x)).elim]
    simp only [Matrix.of_apply, Units.mul_inv]
  pentagon A B C D _ _ _ _ _ i₁ i₂ i₃ k m n := by
    obtain ⟨hL, hR⟩ := ofAddMonoid_pentagon_sides
      (fun a b c' _ ↦ Matrix.of fun _ _ ↦ (((c.ω a b c')⁻¹ : Rˣ) : R))
      (fun a b c' ↦ (((c.ω a b c')⁻¹ : Rˣ) : R)) (fun _ _ _ _ _ _ ↦ rfl) i₁ i₂ i₃ k m n
    refine (hL.trans ?_).trans hR.symm; rw [mul_comm]
    simpa only [mul_inv_rev, Units.val_mul, mul_assoc] using
      congrArg (fun u : Rˣ ↦ ((u⁻¹ : Rˣ) : R)) (c.cocycle A B C D)
  triangle _ _ _ j l := by
    have h := eq_of_fin_ofAddMonoid j; rw [fin_ofAddMonoid_eq h j, fin_ofAddMonoid_eq h l]; simp

@[simp] theorem ofTwistingCocycle_F_apply (c : TwistingCocycle I R) (a b c' d : I)
    (x : (ofAddMonoid I).Left a b c' d) (y : (ofAddMonoid I).Right a b c' d) :
    (ofTwistingCocycle c).F a b c' d x y = (((c.ω a b c')⁻¹ : Rˣ) : R) := Matrix.of_apply _ _ _

@[simp] theorem ofTwistingCocycle_Finv_apply (c : TwistingCocycle I R) (a b c' d : I)
    (y : (ofAddMonoid I).Right a b c' d) (x : (ofAddMonoid I).Left a b c' d) :
    (ofTwistingCocycle c).Finv a b c' d y x = (c.ω a b c' : R) := Matrix.of_apply _ _ _

private theorem pointed_F_eq_canonical (P : FSymbols R (ofAddMonoid I)) (a b c' d : I)
    (x : (ofAddMonoid I).Left a b c' d) (y : (ofAddMonoid I).Right a b c' d) :
    P.F a b c' d x y = P.F a b c' (a + b + c') (ofAddMonoidLeft rfl) (ofAddMonoidRight rfl) := by
  obtain rfl := eq_of_left_ofAddMonoid x; rw [left_ofAddMonoid_eq rfl x, right_ofAddMonoid_eq rfl y]

/-- Extract the normalized `3`-cocycle `ω a b c = Finv^{abc}_{a+b+c}` from pointed F-symbols. -/
def toTwistingCocycle (P : FSymbols R (ofAddMonoid I)) : TwistingCocycle I R where
  ω a b c' :=
    { val := P.Finv a b c' (a + b + c') (ofAddMonoidRight rfl) (ofAddMonoidLeft rfl)
      inv := P.F a b c' (a + b + c') (ofAddMonoidLeft rfl) (ofAddMonoidRight rfl)
      val_inv := by
        have h := P.sum_Finv_mul_F a b c' (a + b + c') (ofAddMonoidRight rfl) (ofAddMonoidRight rfl)
        rw [Fintype.sum_eq_single (ofAddMonoidLeft rfl)
          fun x hx ↦ (hx (left_ofAddMonoid_eq rfl x)).elim] at h; simpa using h
      inv_val := by
        have h := P.sum_F_mul_Finv a b c' (a + b + c') (ofAddMonoidLeft rfl) (ofAddMonoidLeft rfl)
        rw [Fintype.sum_eq_single (ofAddMonoidRight rfl)
          fun y hy ↦ (hy (right_ofAddMonoid_eq rfl y)).elim] at h; simpa using h }
  cocycle i₁ i₂ i₃ i₄ := by
    have hBCDE : i₁ + (i₂ + (i₃ + i₄)) = i₁ + i₂ + i₃ + i₄ := by
      rw [← add_assoc i₂ i₃ i₄, ← add_assoc i₁ (i₂ + i₃) i₄, add_assoc i₁ i₂ i₃]
    have hp := P.pentagon i₁ i₂ i₃ i₄ (i₁ + i₂ + i₃ + i₄) (i₁ + i₂) (i₁ + i₂ + i₃) (i₃ + i₄)
      (i₂ + (i₃ + i₄)) (ofAddMonoidIdx rfl) (ofAddMonoidIdx rfl) (ofAddMonoidIdx rfl)
      (ofAddMonoidIdx rfl) (ofAddMonoidIdx rfl) (ofAddMonoidIdx hBCDE)
    obtain ⟨hL, hR⟩ := ofAddMonoid_pentagon_sides P.F _ P.pointed_F_eq_canonical
      (ofAddMonoidIdx (a := i₁) (b := i₂) rfl) (ofAddMonoidIdx (a := i₁ + i₂) (b := i₃) rfl)
      (ofAddMonoidIdx (a := i₁ + i₂ + i₃) (b := i₄) rfl) (ofAddMonoidIdx (a := i₃) (b := i₄) rfl)
      (ofAddMonoidIdx (a := i₂) (b := i₃ + i₄) rfl) (ofAddMonoidIdx hBCDE)
    refine inv_inj.mp (Units.ext ?_)
    simp only [mul_inv_rev, Units.val_mul, Units.inv_mk, ← mul_assoc]
    exact (mul_comm _ _).trans ((hL.symm.trans hp).trans hR)
  ω_zero i₁ i₃ := inv_inj.mp <| Units.ext <| by
    let j : Fin ((ofAddMonoid I).N i₁ i₃ (i₁ + 0 + i₃)) := ofAddMonoidIdx (by simp)
    simpa only [inv_one, Units.inv_mk, Units.val_one] using
      (P.pointed_F_eq_canonical i₁ 0 i₃ (i₁ + 0 + i₃) ⟨i₁, (ofAddMonoid I).unitRight i₁, j⟩
        ⟨i₃, (ofAddMonoid I).unitLeft i₃, j⟩).symm.trans (P.triangle_self i₁ i₃ (i₁ + 0 + i₃) j)

@[simp] theorem val_toTwistingCocycle_ω (P : FSymbols R (ofAddMonoid I)) (a b c' : I) :
    (P.toTwistingCocycle.ω a b c' : R) =
      P.Finv a b c' (a + b + c') (ofAddMonoidRight rfl) (ofAddMonoidLeft rfl) := (rfl)

@[simp] theorem val_inv_toTwistingCocycle_ω (P : FSymbols R (ofAddMonoid I)) (a b c' : I) :
    (((P.toTwistingCocycle.ω a b c')⁻¹ : Rˣ) : R) =
      P.F a b c' (a + b + c') (ofAddMonoidLeft rfl) (ofAddMonoidRight rfl) :=
  (Units.inv_eq_val_inv (P.toTwistingCocycle.ω a b c')).symm

theorem F_eq_inv_toTwistingCocycle_ω (P : FSymbols R (ofAddMonoid I)) (a b c' d : I)
    (x : (ofAddMonoid I).Left a b c' d) (y : (ofAddMonoid I).Right a b c' d) :
    P.F a b c' d x y = (((P.toTwistingCocycle.ω a b c')⁻¹ : Rˣ) : R) := by
  rw [val_inv_toTwistingCocycle_ω, pointed_F_eq_canonical]

theorem Finv_eq_toTwistingCocycle_ω (P : FSymbols R (ofAddMonoid I)) (a b c' d : I)
    (y : (ofAddMonoid I).Right a b c' d) (x : (ofAddMonoid I).Left a b c' d) :
    P.Finv a b c' d y x = (P.toTwistingCocycle.ω a b c' : R) := by
  obtain rfl := eq_of_right_ofAddMonoid y
  rw [val_toTwistingCocycle_ω, right_ofAddMonoid_eq rfl y, left_ofAddMonoid_eq rfl x]

@[simp] theorem toTwistingCocycle_ofTwistingCocycle (c : TwistingCocycle I R) :
    (ofTwistingCocycle c).toTwistingCocycle = c := by ext; simp

@[simp] theorem ofTwistingCocycle_toTwistingCocycle (P : FSymbols R (ofAddMonoid I)) :
    ofTwistingCocycle P.toTwistingCocycle = P := by
  ext a b c' d x y; rw [ofTwistingCocycle_F_apply, F_eq_inv_toTwistingCocycle_ω]

/-- Equivalence between F-symbols on `FusionRules.ofAddMonoid I` and normalized `3`-cocycles
`TauCeti.GradedObject.TwistingCocycle I R`, with inverse `FSymbols.ofTwistingCocycle`. -/
def twistingCocycleEquiv : FSymbols R (ofAddMonoid I) ≃ TwistingCocycle I R where
  toFun := toTwistingCocycle
  invFun := ofTwistingCocycle
  left_inv := ofTwistingCocycle_toTwistingCocycle
  right_inv := toTwistingCocycle_ofTwistingCocycle

@[simp] theorem twistingCocycleEquiv_apply (P : FSymbols R (ofAddMonoid I)) :
    twistingCocycleEquiv P = P.toTwistingCocycle := (rfl)
@[simp] theorem twistingCocycleEquiv_symm_apply (c : TwistingCocycle I R) :
    twistingCocycleEquiv.symm c = ofTwistingCocycle c := (rfl)

/-- Base change commutes with `FSymbols.ofTwistingCocycle`. -/
@[simp] theorem map_ofTwistingCocycle {S : Type*} [CommRing S] (f : R →+* S)
    (c : TwistingCocycle I R) :
    (ofTwistingCocycle c).map f = ofTwistingCocycle (c.map (f : R →* S)) := by
  ext a b c' d x y
  rw [map_F_apply, ofTwistingCocycle_F_apply, ofTwistingCocycle_F_apply,
    TwistingCocycle.map_ω, ← map_inv (Units.map (f : R →* S)), Units.coe_map]
  simp only [MonoidHom.coe_ofClass]

@[simp] theorem toTwistingCocycle_map {S : Type*} [CommRing S] (f : R →+* S)
    (P : FSymbols R (ofAddMonoid I)) :
    (P.map f).toTwistingCocycle = P.toTwistingCocycle.map (f : R →* S) := by
  rw [← toTwistingCocycle_ofTwistingCocycle (P.toTwistingCocycle.map (f : R →* S)),
    ← map_ofTwistingCocycle, ofTwistingCocycle_toTwistingCocycle]

end Pointed

end FSymbols

/-! ### Pointed braidings and abelian 3-cocycles -/

namespace RSymbols

section Pointed

open FusionRules (ofAddMonoid ofAddMonoidIdx eq_of_fin_ofAddMonoid fin_ofAddMonoid_eq
  sum_fin_ofAddMonoid_of_eq sum_ofAddMonoid_fst)
open GradedObject (TwistingCocycle PointedBraiding)

variable {K : Type v} [CommRing K] {I : Type u} [Fintype I] [DecidableEq I] [AddCommMonoid I]
  {c : TwistingCocycle I K}

private theorem ofAddMonoid_hexagon_forward_sides
    (R : ∀ a b d : I, Matrix (Fin ((ofAddMonoid I).N a b d)) (Fin ((ofAddMonoid I).N b a d)) K)
    (ρ : I → I → K) (hR : ∀ a b d i j, R a b d i j = ρ a b) (c : TwistingCocycle I K)
    {a b c' d e g : I} (i : Fin ((ofAddMonoid I).N a b e)) (j : Fin ((ofAddMonoid I).N e c' d))
    (n : Fin ((ofAddMonoid I).N c' a g)) (o : Fin ((ofAddMonoid I).N b g d)) :
    (∑ f : I, ∑ k : Fin ((ofAddMonoid I).N b c' f), ∑ l : Fin ((ofAddMonoid I).N a f d),
        ∑ m : Fin ((ofAddMonoid I).N f a d),
        (FSymbols.ofTwistingCocycle c).F a b c' d ⟨e, i, j⟩ ⟨f, k, l⟩ * R a f d l m *
          (FSymbols.ofTwistingCocycle c).F b c' a d ⟨f, k, m⟩ ⟨g, n, o⟩ =
      (((c.ω a b c')⁻¹ : Kˣ) : K) * ρ a (b + c') * (((c.ω b c' a)⁻¹ : Kˣ) : K)) ∧
    (∑ p : Fin ((ofAddMonoid I).N b a e), ∑ q : Fin ((ofAddMonoid I).N a c' g),
        R a b e i p * (FSymbols.ofTwistingCocycle c).F b a c' d ⟨e, p, j⟩ ⟨g, q, o⟩ *
          R a c' g q n =
      ρ a b * (((c.ω b a c')⁻¹ : Kˣ) : K) * ρ a c') := by
  obtain rfl := eq_of_fin_ofAddMonoid i; obtain rfl := eq_of_fin_ofAddMonoid j
  obtain rfl := eq_of_fin_ofAddMonoid n
  refine ⟨?_, by rw [sum_fin_ofAddMonoid_of_eq (add_comm b a),
    sum_fin_ofAddMonoid_of_eq (add_comm a c'), FSymbols.ofTwistingCocycle_F_apply, hR, hR]⟩
  rw [sum_ofAddMonoid_fst b c', sum_fin_ofAddMonoid_of_eq (add_assoc a b c').symm,
    sum_fin_ofAddMonoid_of_eq (by abel : (b + c') + a = a + b + c'),
    FSymbols.ofTwistingCocycle_F_apply, FSymbols.ofTwistingCocycle_F_apply, hR]

private theorem ofAddMonoid_hexagon_reverse_sides
    (R : ∀ a b d : I, Matrix (Fin ((ofAddMonoid I).N a b d)) (Fin ((ofAddMonoid I).N b a d)) K)
    (ρ : I → I → K) (hR : ∀ a b d i j, R a b d i j = ρ a b) (c : TwistingCocycle I K)
    {a b c' d f g : I} (k : Fin ((ofAddMonoid I).N b c' f)) (l : Fin ((ofAddMonoid I).N a f d))
    (n : Fin ((ofAddMonoid I).N c' a g)) (o : Fin ((ofAddMonoid I).N g b d)) :
    (∑ e : I, ∑ i : Fin ((ofAddMonoid I).N a b e), ∑ j : Fin ((ofAddMonoid I).N e c' d),
        ∑ m : Fin ((ofAddMonoid I).N c' e d),
        (FSymbols.ofTwistingCocycle c).Finv a b c' d ⟨f, k, l⟩ ⟨e, i, j⟩ * R e c' d j m *
          (FSymbols.ofTwistingCocycle c).Finv c' a b d ⟨e, i, m⟩ ⟨g, n, o⟩ =
      (c.ω a b c' : K) * ρ (a + b) c' * (c.ω c' a b : K)) ∧
    (∑ p : Fin ((ofAddMonoid I).N c' b f), ∑ q : Fin ((ofAddMonoid I).N a c' g),
        R b c' f k p * (FSymbols.ofTwistingCocycle c).Finv a c' b d ⟨f, p, l⟩ ⟨g, q, o⟩ *
          R a c' g q n =
      ρ b c' * (c.ω a c' b : K) * ρ a c') := by
  obtain rfl := eq_of_fin_ofAddMonoid k; obtain rfl := eq_of_fin_ofAddMonoid l
  obtain rfl := eq_of_fin_ofAddMonoid n
  refine ⟨?_, by rw [sum_fin_ofAddMonoid_of_eq (add_comm c' b),
    sum_fin_ofAddMonoid_of_eq (add_comm a c'), FSymbols.ofTwistingCocycle_Finv_apply, hR, hR]⟩
  rw [sum_ofAddMonoid_fst a b, sum_fin_ofAddMonoid_of_eq (add_assoc a b c'),
    sum_fin_ofAddMonoid_of_eq (by abel : c' + (a + b) = a + (b + c')),
    FSymbols.ofTwistingCocycle_Finv_apply, FSymbols.ofTwistingCocycle_Finv_apply, hR]

/-- Construct `RSymbols` on `FSymbols.ofTwistingCocycle c` from a `PointedBraiding c`. -/
def ofPointedBraiding (B : PointedBraiding c) : RSymbols (FSymbols.ofTwistingCocycle c) where
  R a b _ := Matrix.of fun _ _ ↦ (B.r a b : K)
  Rinv a b _ := Matrix.of fun _ _ ↦ (((B.r a b)⁻¹ : Kˣ) : K)
  R_mul_Rinv a b d := by
    ext i₁ i₂; have h := eq_of_fin_ofAddMonoid i₁
    rw [fin_ofAddMonoid_eq h i₁, fin_ofAddMonoid_eq h i₂, Matrix.mul_apply, Matrix.one_apply_eq,
      sum_fin_ofAddMonoid_of_eq (add_comm b a ▸ h)]
    simp only [Matrix.of_apply, Units.mul_inv]
  Rinv_mul_R a b d := by
    ext j₁ j₂; have h' := eq_of_fin_ofAddMonoid j₁
    rw [fin_ofAddMonoid_eq h' j₁, fin_ofAddMonoid_eq h' j₂, Matrix.mul_apply, Matrix.one_apply_eq,
      sum_fin_ofAddMonoid_of_eq (add_comm a b ▸ h')]
    simp only [Matrix.of_apply, Units.inv_mul]
  hexagon_forward a b c' _ _ _ i j n o := by
    obtain ⟨hL, hR⟩ := ofAddMonoid_hexagon_forward_sides
      (fun a b _ ↦ Matrix.of fun _ _ ↦ (B.r a b : K)) (fun a b ↦ (B.r a b : K))
      (fun _ _ _ _ _ ↦ rfl) c i j n o
    refine (hL.trans ?_).trans hR.symm
    simpa only [Units.val_mul, mul_assoc] using congrArg Units.val (B.hexagon_forward a b c')
  hexagon_reverse a b c' _ _ _ k l n o := by
    obtain ⟨hL, hR⟩ := ofAddMonoid_hexagon_reverse_sides
      (fun a b _ ↦ Matrix.of fun _ _ ↦ (B.r a b : K)) (fun a b ↦ (B.r a b : K))
      (fun _ _ _ _ _ ↦ rfl) c k l n o
    refine (hL.trans ?_).trans hR.symm
    simpa only [Units.val_mul, mul_assoc] using congrArg Units.val (B.hexagon_reverse a b c')

@[simp] theorem ofPointedBraiding_R_apply (B : PointedBraiding c) (a b d : I)
    (i : Fin ((ofAddMonoid I).N a b d)) (j : Fin ((ofAddMonoid I).N b a d)) :
    (ofPointedBraiding B).R a b d i j = (B.r a b : K) := Matrix.of_apply _ _ _

@[simp] theorem ofPointedBraiding_Rinv_apply (B : PointedBraiding c) (a b d : I)
    (j : Fin ((ofAddMonoid I).N b a d)) (i : Fin ((ofAddMonoid I).N a b d)) :
    (ofPointedBraiding B).Rinv a b d j i = (((B.r a b)⁻¹ : Kˣ) : K) := Matrix.of_apply _ _ _

private theorem pointed_R_eq_canonical (Q : RSymbols (FSymbols.ofTwistingCocycle c)) (x y d : I)
    (i : Fin ((ofAddMonoid I).N x y d)) (j : Fin ((ofAddMonoid I).N y x d)) :
    Q.R x y d i j = Q.R x y (x + y) (ofAddMonoidIdx rfl) (ofAddMonoidIdx (add_comm y x)) := by
  obtain rfl := eq_of_fin_ofAddMonoid i
  rw [fin_ofAddMonoid_eq rfl i, fin_ofAddMonoid_eq (add_comm y x) j]

/-- Extract a `PointedBraiding c` from `RSymbols (FSymbols.ofTwistingCocycle c)`. -/
def toPointedBraiding (Q : RSymbols (FSymbols.ofTwistingCocycle c)) : PointedBraiding c where
  r a b :=
    { val := Q.R a b (a + b) (ofAddMonoidIdx rfl) (ofAddMonoidIdx (add_comm b a))
      inv := Q.Rinv a b (a + b) (ofAddMonoidIdx (add_comm b a)) (ofAddMonoidIdx rfl)
      val_inv := by
        have h := Q.sum_R_mul_Rinv a b (a + b) (ofAddMonoidIdx rfl) (ofAddMonoidIdx rfl)
        rw [sum_fin_ofAddMonoid_of_eq (add_comm b a)] at h; simpa using h
      inv_val := by
        have h := Q.sum_Rinv_mul_R a b (a + b)
          (ofAddMonoidIdx (add_comm b a)) (ofAddMonoidIdx (add_comm b a))
        rw [sum_fin_ofAddMonoid_of_eq rfl] at h; simpa using h }
  hexagon_forward a b c' := by
    have ho : b + (c' + a) = a + b + c' := by abel
    have hhex := Q.hexagon_forward a b c' (a + b + c') (a + b) (c' + a) (ofAddMonoidIdx rfl)
      (ofAddMonoidIdx rfl) (ofAddMonoidIdx rfl) (ofAddMonoidIdx ho)
    obtain ⟨hL, hR⟩ := ofAddMonoid_hexagon_forward_sides Q.R _ Q.pointed_R_eq_canonical c
      (ofAddMonoidIdx (a := a) (b := b) rfl) (ofAddMonoidIdx (a := a + b) (b := c') rfl)
      (ofAddMonoidIdx (a := c') (b := a) rfl) (ofAddMonoidIdx ho)
    ext; simpa only [Units.val_mul, mul_assoc] using (hL.symm.trans hhex).trans hR
  hexagon_reverse a b c' := by
    have ho : (c' + a) + b = a + (b + c') := by abel
    have hhex := Q.hexagon_reverse a b c' (a + (b + c')) (b + c') (c' + a) (ofAddMonoidIdx rfl)
      (ofAddMonoidIdx rfl) (ofAddMonoidIdx rfl) (ofAddMonoidIdx ho)
    obtain ⟨hL, hR⟩ := ofAddMonoid_hexagon_reverse_sides Q.R _ Q.pointed_R_eq_canonical c
      (ofAddMonoidIdx (a := b) (b := c') rfl) (ofAddMonoidIdx (a := a) (b := b + c') rfl)
      (ofAddMonoidIdx (a := c') (b := a) rfl) (ofAddMonoidIdx ho)
    ext; simpa only [Units.val_mul, mul_assoc] using (hL.symm.trans hhex).trans hR

@[simp] theorem val_toPointedBraiding_r (Q : RSymbols (FSymbols.ofTwistingCocycle c)) (a b : I) :
    (Q.toPointedBraiding.r a b : K) =
      Q.R a b (a + b) (ofAddMonoidIdx rfl) (ofAddMonoidIdx (add_comm b a)) := (rfl)

@[simp] theorem val_inv_toPointedBraiding_r (Q : RSymbols (FSymbols.ofTwistingCocycle c))
    (a b : I) : (((Q.toPointedBraiding.r a b)⁻¹ : Kˣ) : K) =
      Q.Rinv a b (a + b) (ofAddMonoidIdx (add_comm b a)) (ofAddMonoidIdx rfl) :=
  (Units.inv_eq_val_inv (Q.toPointedBraiding.r a b)).symm

theorem R_eq_toPointedBraiding_r (Q : RSymbols (FSymbols.ofTwistingCocycle c)) (a b d : I)
    (i : Fin ((ofAddMonoid I).N a b d)) (j : Fin ((ofAddMonoid I).N b a d)) :
    Q.R a b d i j = (Q.toPointedBraiding.r a b : K) := by
  rw [val_toPointedBraiding_r, pointed_R_eq_canonical]

theorem Rinv_eq_inv_toPointedBraiding_r (Q : RSymbols (FSymbols.ofTwistingCocycle c)) (a b d : I)
    (j : Fin ((ofAddMonoid I).N b a d)) (i : Fin ((ofAddMonoid I).N a b d)) :
    Q.Rinv a b d j i = (((Q.toPointedBraiding.r a b)⁻¹ : Kˣ) : K) := by
  obtain rfl := eq_of_fin_ofAddMonoid i
  rw [val_inv_toPointedBraiding_r, fin_ofAddMonoid_eq (add_comm b a) j, fin_ofAddMonoid_eq rfl i]

@[simp] theorem toPointedBraiding_ofPointedBraiding (B : PointedBraiding c) :
    (ofPointedBraiding B).toPointedBraiding = B := by ext; simp

@[simp] theorem ofPointedBraiding_toPointedBraiding (Q : RSymbols (FSymbols.ofTwistingCocycle c)) :
    ofPointedBraiding Q.toPointedBraiding = Q := by
  ext a b d i j; rw [ofPointedBraiding_R_apply, R_eq_toPointedBraiding_r]

/-- Equivalence between `RSymbols (FSymbols.ofTwistingCocycle c)` and
`TauCeti.GradedObject.PointedBraiding c`, with inverse `RSymbols.ofPointedBraiding`. -/
def pointedBraidingEquiv (c : TwistingCocycle I K) :
    RSymbols (FSymbols.ofTwistingCocycle c) ≃ PointedBraiding c where
  toFun := toPointedBraiding
  invFun := ofPointedBraiding
  left_inv := ofPointedBraiding_toPointedBraiding
  right_inv := toPointedBraiding_ofPointedBraiding

@[simp] theorem pointedBraidingEquiv_apply (c : TwistingCocycle I K)
    (Q : RSymbols (FSymbols.ofTwistingCocycle c)) :
    pointedBraidingEquiv c Q = Q.toPointedBraiding := (rfl)
@[simp] theorem pointedBraidingEquiv_symm_apply (c : TwistingCocycle I K) (B : PointedBraiding c) :
    (pointedBraidingEquiv c).symm B = ofPointedBraiding B := (rfl)

/-- Base change commutes with `RSymbols.ofPointedBraiding` up to `RSymbols.cast`. -/
@[simp] theorem cast_map_ofPointedBraiding {L : Type*} [CommRing L] (f : K →+* L)
    (B : PointedBraiding c)
    (h : (FSymbols.ofTwistingCocycle c).map f = FSymbols.ofTwistingCocycle (c.map (f : K →* L)) :=
      FSymbols.map_ofTwistingCocycle f c) :
    ((ofPointedBraiding B).map f).cast h = ofPointedBraiding (B.map (f : K →* L)) := by ext; simp

end Pointed

end RSymbols

/-! ### Complete classification of F-symbols and R-symbols on `ZMod 2` -/

namespace FSymbols

section ZMod2

open FusionRules (ofAddMonoid ofAddMonoidLeft ofAddMonoidRight)
open GradedObject (TwistingCocycle)

variable {R : Type v} [CommRing R]

/-- The pointed F-symbols on `ZMod 2` with `F^{111}_1 = u` (`u * u = 1`) and `1` on all other
nonempty blocks. -/
@[expose]
def zmod2 (u : Rˣ) (hu : u * u = 1) : FSymbols R (ofAddMonoid (ZMod 2)) :=
  ofTwistingCocycle (TwistingCocycle.zmod2 u hu)

theorem zmod2_eq_ofTwistingCocycle (u : Rˣ) (hu : u * u = 1) :
    zmod2 u hu = ofTwistingCocycle (TwistingCocycle.zmod2 u hu) := (rfl)

@[simp] theorem zmod2_F_one_one_one (u : Rˣ) (hu : u * u = 1)
    (x : (ofAddMonoid (ZMod 2)).Left 1 1 1 1) (y : (ofAddMonoid (ZMod 2)).Right 1 1 1 1) :
    (zmod2 u hu).F 1 1 1 1 x y = (u : R) := by simp [zmod2, inv_eq_of_mul_eq_one_right hu]

@[simp] theorem zmod2_Finv_one_one_one (u : Rˣ) (hu : u * u = 1)
    (y : (ofAddMonoid (ZMod 2)).Right 1 1 1 1) (x : (ofAddMonoid (ZMod 2)).Left 1 1 1 1) :
    (zmod2 u hu).Finv 1 1 1 1 y x = (u : R) := by simp [zmod2]

/-- F-symbols on `FusionRules.ofAddMonoid (ZMod 2)` are in bijection with `{ u : Rˣ // u * u = 1 }`
via the `(1, 1, 1)` entry `F^{111}_1 = u`, with inverse `FSymbols.zmod2`. -/
def zmod2Equiv : FSymbols R (ofAddMonoid (ZMod 2)) ≃ { u : Rˣ // u * u = 1 } :=
  twistingCocycleEquiv.trans TwistingCocycle.zmod2Equiv

@[simp] theorem val_zmod2Equiv_apply (P : FSymbols R (ofAddMonoid (ZMod 2))) :
    (((zmod2Equiv P).1 : Rˣ) : R) =
      P.F 1 1 1 1 (ofAddMonoidLeft (by decide)) (ofAddMonoidRight (by decide)) := by
  have hinv : (zmod2Equiv P).1 = ((zmod2Equiv P).1)⁻¹ :=
    (inv_eq_of_mul_eq_one_right (zmod2Equiv P).2).symm
  rw [hinv, P.F_eq_inv_toTwistingCocycle_ω 1 1 1 1]; simp [zmod2Equiv]

@[simp] theorem zmod2Equiv_symm_apply (u : { u : Rˣ // u * u = 1 }) :
    zmod2Equiv.symm u = zmod2 u.1 u.2 := by simp [zmod2Equiv, zmod2]

@[simp] theorem zmod2Equiv_zmod2 (u : Rˣ) (hu : u * u = 1) : zmod2Equiv (zmod2 u hu) = ⟨u, hu⟩ := by
  rw [← zmod2Equiv_symm_apply ⟨u, hu⟩]; exact zmod2Equiv.apply_symm_apply ⟨u, hu⟩

@[simp] theorem zmod2_zmod2Equiv (P : FSymbols R (ofAddMonoid (ZMod 2))) :
    zmod2 (zmod2Equiv P).1 (zmod2Equiv P).2 = P := by
  rw [← zmod2Equiv_symm_apply (zmod2Equiv P)]; exact zmod2Equiv.symm_apply_apply P

end ZMod2

end FSymbols

namespace RSymbols

section ZMod2

open FusionRules (ofAddMonoid ofAddMonoidIdx)
open GradedObject (TwistingCocycle PointedBraiding)

variable {K : Type v} [CommRing K]

/-- Construct R-symbols on `FSymbols.zmod2 u hu` from a square root `r : Kˣ` of `u` (`r * r = u`),
giving `R^{11}_0 = r` and `1` on all unit blocks. -/
def zmod2 {u : Kˣ} (hu : u * u = 1) (r : Kˣ) (hr : r * r = u) : RSymbols (FSymbols.zmod2 u hu) :=
  ofPointedBraiding (PointedBraiding.zmod2 hu r hr)

theorem zmod2_eq_ofPointedBraiding {u : Kˣ} (hu : u * u = 1) (r : Kˣ) (hr : r * r = u) :
    zmod2 hu r hr = ofPointedBraiding (PointedBraiding.zmod2 hu r hr) := (rfl)

@[simp] theorem zmod2_R_one_one {u : Kˣ} (hu : u * u = 1) (r : Kˣ) (hr : r * r = u)
    (i j : Fin ((ofAddMonoid (ZMod 2)).N 1 1 0)) : (zmod2 hu r hr).R 1 1 0 i j = (r : K) := by
  simp [zmod2]

@[simp] theorem zmod2_Rinv_one_one {u : Kˣ} (hu : u * u = 1) (r : Kˣ) (hr : r * r = u)
    (j i : Fin ((ofAddMonoid (ZMod 2)).N 1 1 0)) :
    (zmod2 hu r hr).Rinv 1 1 0 j i = ((r⁻¹ : Kˣ) : K) := by simp [zmod2]

/-- R-symbols on `FSymbols.zmod2 u hu` are in bijection with `{ r : Kˣ // r * r = u }` via the
nontrivial braiding entry `R^{11}_0 = r`, witnessing `(R^{11}_0)^2 = F^{111}_1`, with inverse
`RSymbols.zmod2`. -/
def zmod2Equiv (u : Kˣ) (hu : u * u = 1) :
    RSymbols (FSymbols.zmod2 u hu) ≃ { r : Kˣ // r * r = u } :=
  (pointedBraidingEquiv (TwistingCocycle.zmod2 u hu)).trans (PointedBraiding.zmod2Equiv u hu)

@[simp] theorem val_zmod2Equiv_apply (u : Kˣ) (hu : u * u = 1)
    (Q : RSymbols (FSymbols.zmod2 u hu)) : (((zmod2Equiv u hu Q).1 : Kˣ) : K) =
      Q.R 1 1 0 (ofAddMonoidIdx (by decide)) (ofAddMonoidIdx (by decide)) :=
  (congrArg Units.val (PointedBraiding.coe_zmod2Equiv_apply u hu Q.toPointedBraiding)).trans
    (R_eq_toPointedBraiding_r Q 1 1 0 _ _).symm

@[simp] theorem zmod2Equiv_symm_apply (u : Kˣ) (hu : u * u = 1) (r : { r : Kˣ // r * r = u }) :
    (zmod2Equiv u hu).symm r = zmod2 hu r.1 r.2 :=
  congrArg ofPointedBraiding (PointedBraiding.zmod2Equiv_symm_apply u hu r)

@[simp] theorem zmod2Equiv_zmod2 {u : Kˣ} (hu : u * u = 1) (r : Kˣ) (hr : r * r = u) :
    zmod2Equiv u hu (zmod2 hu r hr) = ⟨r, hr⟩ := by
  rw [← zmod2Equiv_symm_apply u hu ⟨r, hr⟩]; exact (zmod2Equiv u hu).apply_symm_apply ⟨r, hr⟩

@[simp] theorem zmod2_zmod2Equiv (u : Kˣ) (hu : u * u = 1) (Q : RSymbols (FSymbols.zmod2 u hu)) :
    zmod2 hu (zmod2Equiv u hu Q).1 (zmod2Equiv u hu Q).2 = Q := by
  rw [← zmod2Equiv_symm_apply u hu (zmod2Equiv u hu Q)]; exact (zmod2Equiv u hu).symm_apply_apply Q

/-- For the trivial `ZMod 2` F-symbols (`u = 1`), `r = -1` gives the super-vector-space braiding
`R^{11}_0 = -1`. -/
def zmod2Super : RSymbols (FSymbols.zmod2 (1 : Kˣ) (mul_one 1)) := zmod2 (mul_one 1) (-1) (by simp)

@[simp] theorem zmod2Super_R_one_one (i j : Fin ((ofAddMonoid (ZMod 2)).N 1 1 0)) :
    (zmod2Super : RSymbols (FSymbols.zmod2 (1 : Kˣ) (mul_one 1))).R 1 1 0 i j = -1 := by
  simp [zmod2Super]

@[simp] theorem zmod2Super_Rinv_one_one (j i : Fin ((ofAddMonoid (ZMod 2)).N 1 1 0)) :
    (zmod2Super : RSymbols (FSymbols.zmod2 (1 : Kˣ) (mul_one 1))).Rinv 1 1 0 j i = -1 := by
  simp [zmod2Super]

/-- Over `ℤ`, the nontrivial `ZMod 2` F-symbols with `F^{111}_1 = -1` admit no R-symbols, since
`-1` is not a square in `ℤˣ`. -/
instance instIsEmptyZMod2NegOneInt : IsEmpty (RSymbols (FSymbols.zmod2 (-1 : ℤˣ) (by decide))) :=
  ⟨fun Q ↦ by
    obtain ⟨r, hr⟩ := zmod2Equiv (-1 : ℤˣ) (by decide) Q
    rcases Int.units_eq_one_or r with rfl | rfl <;> exact absurd hr (by decide)⟩

end ZMod2

end RSymbols

end TauCeti
