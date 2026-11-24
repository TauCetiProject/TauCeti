/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.ZMod.Basic
public import TauCeti.CategoryTheory.GradedObject.Twisted.Braided
public import TauCeti.CategoryTheory.Monoidal.FSymbols.Transport

/-!
# Monoid-based and pointed fusion rules, `3`-cocycles, and `ℤ/2` classification

In tensor category theory, fusion rules are **pointed** when the simple objects form a group `G`
under tensor product (`N_{ab}^c = [a * b = c]`, every simple invertible; EGNO, §2.3, Ex. 2.3.8).
More generally, any type `I` equipped with `0` and `+` defines additive operation-indexed fusion
rules `TauCeti.FusionRules.ofAdd I` with `N_{ab}^c = [a + b = c]` (the additive counterpart of
`TauCeti.FusionRules.ofMul`). When `I` is a finite `AddMonoid`, every composite basis space
`Left a b c d` and `Right a b c d` has cardinality `1` if `a + b + c = d` and `0` otherwise, so the
F- and R-symbol matrix equations over any commutative semiring `R` collapse to scalar equations:

* `TauCeti.FusionRules.ofAdd I`: additive monoid-type fusion rules `N_{ab}^c = [a + b = c]` on
  `[AddZeroClass I]` (specializing to pointed fusion rules when `I` is an `AddGroup`), together
  with `TauCeti.FusionRules.Equiv.ofAddEquiv`, `ofAddMultiplicative`, and `ofMulAdditive`.
* `TauCeti.FSymbols.twistingCocycleEquiv` and `TauCeti.FSymbols.mulTwistingCocycleEquiv`:
  equivalences `FSymbols R (ofAdd I) ≃ TauCeti.GradedObject.TwistingCocycle I R` and
  `FSymbols R (ofMul M) ≃ TauCeti.GradedObject.TwistingCocycle (Additive M) R` over any commutative
  semiring `R` (Quinn, §5), with `F^{abc}_{a+b+c} = (ω a b c)⁻¹`.
* `TauCeti.RSymbols.pointedBraidingEquiv`: equivalence between `RSymbols (ofTwistingCocycle c)` and
  scalar braiding data `TauCeti.GradedObject.PointedBraiding c` over `[AddCommMonoid I]` and
  `[CommSemiring K]` (abelian `3`-cocycles when `I` is an abelian group; Joyal–Street, §3).
* `TauCeti.FSymbols.zmod2Equiv` and `TauCeti.RSymbols.zmod2Equiv`: complete classification on the
  pointed group `ZMod 2` via `{ u : Rˣ // u * u = 1 }` (`F^{111}_1 = u`) and
  `{ r : Kˣ // r * r = u }` (`R^{11}_0 = r`), including the super-vector-space braiding
  `RSymbols.zmod2Super` (`u = 1`, `r = -1`) and `RSymbols.instIsEmptyZMod2NegOneInt`.

## References

* [P. Etingof, S. Gelaki, D. Nikshych, V. Ostrik, *Tensor Categories*][egno15], §2.3 (Ex. 2.3.8),
  §2.6 (Prop. 2.6.1), and §8.4 (abelian `3`-cocycles).
* A. Joyal and R. Street, *Braided tensor categories*, Adv. Math. **102** (1993), 20–78, §3.
* F. Quinn, *Group categories and their field theories*, Geom. Topol. Monogr. **2** (1999),
  407–453, §5.
-/

public section

namespace TauCeti

universe u u' v

/-! ### Additive monoid-type fusion rules -/

namespace FusionRules

/-- Additive operation-indexed fusion rules on `I` (`[AddZeroClass I]`), with `unit = 0` and
`N a b c = if a + b = c then 1 else 0`. When `I` is an `AddGroup`, these are the pointed fusion
rules of `I`-graded objects. -/
def ofAdd (I : Type u) [AddZeroClass I] [DecidableEq I] : FusionRules I where
  unit := 0
  N a b c := if a + b = c then 1 else 0
  N_unit_left_self _ := by simp
  N_unit_left_of_ne _ _ h := by simpa using h
  N_unit_right_self _ := by simp
  N_unit_right_of_ne _ _ h := by simpa using h

section AddZeroClass

variable {I : Type u} [AddZeroClass I] [DecidableEq I]

@[simp]
theorem ofAdd_unit : (ofAdd I).unit = 0 := (rfl)

@[simp]
theorem ofAdd_N (a b c : I) : (ofAdd I).N a b c = if a + b = c then 1 else 0 := (rfl)

/-- An index in `Fin ((ofAdd I).N a b c)` witnesses `a + b = c`. -/
theorem add_eq_of_ofAdd {a b c : I} (i : Fin ((ofAdd I).N a b c)) : a + b = c := by
  by_contra h
  simpa [ofAdd_N, h] using i.isLt

/-- There is no fusion channel `a ⊗ b → c` in `ofAdd I` when `a + b ≠ c`. -/
theorem isEmpty_fin_ofAdd_N {a b c : I} (h : a + b ≠ c) : IsEmpty (Fin ((ofAdd I).N a b c)) :=
  ⟨fun i ↦ h (add_eq_of_ofAdd i)⟩

/-- The canonical basis index in `Fin ((ofAdd I).N a b c)` when `a + b = c`. -/
def ofAddIdx {a b c : I} (h : a + b = c) : Fin ((ofAdd I).N a b c) := ⟨0, by simp [h]⟩

@[simp]
theorem val_ofAddIdx {a b c : I} (h : a + b = c) : (ofAddIdx h).val = 0 := (rfl)

instance (a b c : I) : Subsingleton (Fin ((ofAdd I).N a b c)) :=
  Fin.subsingleton_iff_le_one.mpr <| by rw [ofAdd_N]; split_ifs <;> simp

instance (a b c d : I) : Subsingleton ((ofAdd I).Left a b c d) :=
  ⟨by
    rintro ⟨e, i, j⟩ ⟨e', i', j'⟩
    obtain rfl := add_eq_of_ofAdd i
    obtain rfl := add_eq_of_ofAdd i'
    rw [Subsingleton.elim i i', Subsingleton.elim j j']⟩

instance (a b c d : I) : Subsingleton ((ofAdd I).Right a b c d) :=
  ⟨by
    rintro ⟨f, k, l⟩ ⟨f', k', l'⟩
    obtain rfl := add_eq_of_ofAdd k
    obtain rfl := add_eq_of_ofAdd k'
    rw [Subsingleton.elim k k', Subsingleton.elim l l']⟩

theorem fin_ofAdd_eq {a b c : I} (h : a + b = c) (i : Fin ((ofAdd I).N a b c)) :
    i = ofAddIdx h :=
  Subsingleton.elim i (ofAddIdx h)

theorem sum_fin_ofAdd_of_eq {M : Type*} [AddCommMonoid M] {a b c : I} (h : a + b = c)
    (f : Fin ((ofAdd I).N a b c) → M) : ∑ i, f i = f (ofAddIdx h) :=
  Fintype.sum_eq_single (ofAddIdx h) fun i hi ↦ (hi (fin_ofAdd_eq h i)).elim

theorem sum_fin_ofAdd_of_ne {M : Type*} [AddCommMonoid M] {a b c : I} (h : a + b ≠ c)
    (f : Fin ((ofAdd I).N a b c) → M) : ∑ i, f i = 0 :=
  have := isEmpty_fin_ofAdd_N h
  Fintype.sum_empty f

theorem sum_ofAdd_fst {M : Type*} [AddCommMonoid M] [Fintype I] (a b : I)
    (g : ∀ e : I, Fin ((ofAdd I).N a b e) → M) :
    ∑ e : I, ∑ i : Fin ((ofAdd I).N a b e), g e i = g (a + b) (ofAddIdx rfl) := by
  rw [Fintype.sum_eq_single (a + b) fun e he ↦ sum_fin_ofAdd_of_ne he.symm _,
    sum_fin_ofAdd_of_eq rfl]

end AddZeroClass

section AddMonoid

variable {I : Type u} [AddMonoid I] [DecidableEq I]

theorem eq_of_left_ofAdd {a b c d : I} (x : (ofAdd I).Left a b c d) : a + b + c = d := by
  rw [add_eq_of_ofAdd x.snd.fst, add_eq_of_ofAdd x.snd.snd]

theorem eq_of_right_ofAdd {a b c d : I} (y : (ofAdd I).Right a b c d) : a + b + c = d := by
  rw [add_assoc, add_eq_of_ofAdd y.snd.fst, add_eq_of_ofAdd y.snd.snd]

/-- The unique element of `(ofAdd I).Left a b c d` when `a + b + c = d`. -/
def ofAddLeft {a b c d : I} (h : a + b + c = d) : (ofAdd I).Left a b c d :=
  ⟨a + b, ofAddIdx rfl, ofAddIdx h⟩

@[simp]
theorem ofAddLeft_fst {a b c d : I} (h : a + b + c = d) : (ofAddLeft h).fst = a + b := (rfl)

/-- The unique element of `(ofAdd I).Right a b c d` when `a + b + c = d`. -/
def ofAddRight {a b c d : I} (h : a + b + c = d) : (ofAdd I).Right a b c d :=
  ⟨b + c, ofAddIdx rfl, ofAddIdx (by rwa [← add_assoc])⟩

@[simp]
theorem ofAddRight_fst {a b c d : I} (h : a + b + c = d) : (ofAddRight h).fst = b + c := (rfl)

theorem left_ofAdd_eq {a b c d : I} (h : a + b + c = d) (x : (ofAdd I).Left a b c d) :
    x = ofAddLeft h :=
  Subsingleton.elim x (ofAddLeft h)

theorem right_ofAdd_eq {a b c d : I} (h : a + b + c = d) (y : (ofAdd I).Right a b c d) :
    y = ofAddRight h :=
  Subsingleton.elim y (ofAddRight h)

end AddMonoid

namespace Equiv

/-- An additive isomorphism induces an isomorphism of additive monoid-type fusion rules. -/
def ofAddEquiv {I : Type u} {I' : Type u'} [AddZeroClass I] [DecidableEq I] [AddZeroClass I']
    [DecidableEq I'] (e : I ≃+ I') : (ofAdd I).Equiv (ofAdd I') where
  toEquiv := e.toEquiv
  map_unit' := by simp
  map_N' a b c := by simp [← map_add, e.injective.eq_iff]

@[simp]
theorem ofAddEquiv_apply {I : Type u} {I' : Type u'} [AddZeroClass I] [DecidableEq I]
    [AddZeroClass I'] [DecidableEq I'] (e : I ≃+ I') (a : I) : ofAddEquiv e a = e a := (rfl)

/-- Isomorphism between `ofAdd I` and `ofMul (Multiplicative I)`. -/
def ofAddMultiplicative (I : Type u) [AddZeroClass I] [DecidableEq I] :
    (ofAdd I).Equiv (ofMul (Multiplicative I)) where
  toEquiv := Multiplicative.ofAdd
  map_unit' := by simp
  map_N' a b c := by simp [← ofAdd_add]

@[simp]
theorem ofAddMultiplicative_apply {I : Type u} [AddZeroClass I] [DecidableEq I] (a : I) :
    ofAddMultiplicative I a = Multiplicative.ofAdd a := (rfl)

/-- Isomorphism between `ofMul M` and `ofAdd (Additive M)`. -/
def ofMulAdditive (M : Type u) [MulOneClass M] [DecidableEq M] :
    (ofMul M).Equiv (ofAdd (Additive M)) where
  toEquiv := Additive.ofMul
  map_unit' := by simp
  map_N' a b c := by simp [← ofMul_mul]

@[simp]
theorem ofMulAdditive_apply {M : Type u} [MulOneClass M] [DecidableEq M] (a : M) :
    ofMulAdditive M a = Additive.ofMul a := (rfl)

end Equiv

end FusionRules

/-! ### Equivalence between monoid-indexed F-symbols and normalized `3`-cocycles -/

namespace FSymbols

section Pointed

open FusionRules (ofAdd ofAddIdx ofAddLeft ofAddRight add_eq_of_ofAdd fin_ofAdd_eq
  eq_of_left_ofAdd eq_of_right_ofAdd left_ofAdd_eq right_ofAdd_eq sum_fin_ofAdd_of_eq
  sum_ofAdd_fst)
open GradedObject (TwistingCocycle)

variable {R : Type v} [CommSemiring R] {I : Type u} [Fintype I] [DecidableEq I] [AddMonoid I]

private theorem ofAdd_pentagon_sides
    (F : ∀ a b c' d : I, Matrix ((ofAdd I).Left a b c' d) ((ofAdd I).Right a b c' d) R)
    (φ : I → I → I → R) (hF : ∀ a b c' d x y, F a b c' d x y = φ a b c') {A B C D E p q r s : I}
    (i₁ : Fin ((ofAdd I).N A B p)) (i₂ : Fin ((ofAdd I).N p C q))
    (i₃ : Fin ((ofAdd I).N q D E)) (k : Fin ((ofAdd I).N C D r))
    (m : Fin ((ofAdd I).N B r s)) (n : Fin ((ofAdd I).N A s E)) :
    (∑ l : Fin ((ofAdd I).N p r E),
        F p C D E ⟨q, i₂, i₃⟩ ⟨r, k, l⟩ * F A B r E ⟨p, i₁, l⟩ ⟨s, m, n⟩ =
      φ (A + B) C D * φ A B (C + D)) ∧
    (∑ t : I, ∑ j : Fin ((ofAdd I).N B C t), ∑ j' : Fin ((ofAdd I).N A t q),
        ∑ m' : Fin ((ofAdd I).N t D s),
        F A B C q ⟨p, i₁, i₂⟩ ⟨t, j, j'⟩ * F A t D E ⟨q, j', i₃⟩ ⟨s, m', n⟩ *
          F B C D s ⟨t, j, m'⟩ ⟨r, k, m⟩ =
      φ A B C * φ A (B + C) D * φ B C D) := by
  obtain rfl := add_eq_of_ofAdd i₁; obtain rfl := add_eq_of_ofAdd i₂
  obtain rfl := add_eq_of_ofAdd i₃; obtain rfl := add_eq_of_ofAdd k
  obtain rfl := add_eq_of_ofAdd m
  refine ⟨by rw [sum_fin_ofAdd_of_eq (add_assoc (A + B) C D).symm, hF, hF], ?_⟩
  rw [sum_ofAdd_fst B C, sum_fin_ofAdd_of_eq (add_assoc A B C).symm,
    sum_fin_ofAdd_of_eq (add_assoc B C D), hF, hF, hF]

/-- The F-symbols on `FusionRules.ofAdd I` attached to a normalized `3`-cocycle
`c : TwistingCocycle I R`, with `F^{abc}_{a+b+c} = (c.ω a b c)⁻¹` and
`Finv^{abc}_{a+b+c} = c.ω a b c`. -/
def ofTwistingCocycle (c : TwistingCocycle I R) : FSymbols R (ofAdd I) where
  F a b c' _ := Matrix.of fun _ _ ↦ (((c.ω a b c')⁻¹ : Rˣ) : R)
  Finv a b c' _ := Matrix.of fun _ _ ↦ (c.ω a b c' : R)
  F_mul_Finv a b c' d := by
    ext x₁ x₂
    have h := eq_of_left_ofAdd x₁
    rw [Subsingleton.elim x₁ x₂, Matrix.mul_apply, Matrix.one_apply_eq,
      Fintype.sum_eq_single (ofAddRight h) fun y hy ↦ (hy (right_ofAdd_eq h y)).elim]
    simp only [Matrix.of_apply, Units.inv_mul]
  Finv_mul_F a b c' d := by
    ext y₁ y₂
    have h := eq_of_right_ofAdd y₁
    rw [Subsingleton.elim y₁ y₂, Matrix.mul_apply, Matrix.one_apply_eq,
      Fintype.sum_eq_single (ofAddLeft h) fun x hx ↦ (hx (left_ofAdd_eq h x)).elim]
    simp only [Matrix.of_apply, Units.mul_inv]
  pentagon A B C D _ _ _ _ _ i₁ i₂ i₃ k m n := by
    obtain ⟨hL, hR⟩ := ofAdd_pentagon_sides
      (fun a b c' _ ↦ Matrix.of fun _ _ ↦ (((c.ω a b c')⁻¹ : Rˣ) : R))
      (fun a b c' ↦ (((c.ω a b c')⁻¹ : Rˣ) : R)) (fun _ _ _ _ _ _ ↦ rfl) i₁ i₂ i₃ k m n
    refine (hL.trans ?_).trans hR.symm
    rw [mul_comm]
    simpa only [mul_inv_rev, Units.val_mul, mul_assoc] using
      congrArg (fun u : Rˣ ↦ ((u⁻¹ : Rˣ) : R)) (c.cocycle A B C D)
  triangle _ _ _ j l := by simp [Subsingleton.elim j l]

@[simp]
theorem ofTwistingCocycle_F_apply (c : TwistingCocycle I R) (a b c' d : I)
    (x : (ofAdd I).Left a b c' d) (y : (ofAdd I).Right a b c' d) :
    (ofTwistingCocycle c).F a b c' d x y = (((c.ω a b c')⁻¹ : Rˣ) : R) := Matrix.of_apply _ _ _

@[simp]
theorem ofTwistingCocycle_Finv_apply (c : TwistingCocycle I R) (a b c' d : I)
    (y : (ofAdd I).Right a b c' d) (x : (ofAdd I).Left a b c' d) :
    (ofTwistingCocycle c).Finv a b c' d y x = (c.ω a b c' : R) := Matrix.of_apply _ _ _

private theorem pointed_F_eq_canonical (P : FSymbols R (ofAdd I)) (a b c' d : I)
    (x : (ofAdd I).Left a b c' d) (y : (ofAdd I).Right a b c' d) :
    P.F a b c' d x y = P.F a b c' (a + b + c') (ofAddLeft rfl) (ofAddRight rfl) := by
  obtain rfl := eq_of_left_ofAdd x
  rw [left_ofAdd_eq rfl x, right_ofAdd_eq rfl y]

/-- Extract the normalized `3`-cocycle `ω a b c = Finv^{abc}_{a+b+c}` from F-symbols on
`FusionRules.ofAdd I` (in particular, from pointed F-symbols when `I` is an `AddGroup`). -/
def toTwistingCocycle (P : FSymbols R (ofAdd I)) : TwistingCocycle I R where
  ω a b c' :=
    { val := P.Finv a b c' (a + b + c') (ofAddRight rfl) (ofAddLeft rfl)
      inv := P.F a b c' (a + b + c') (ofAddLeft rfl) (ofAddRight rfl)
      val_inv := by
        have h := P.sum_Finv_mul_F a b c' (a + b + c') (ofAddRight rfl) (ofAddRight rfl)
        rw [Fintype.sum_eq_single (ofAddLeft rfl) fun x hx ↦ (hx (left_ofAdd_eq rfl x)).elim] at h
        simpa using h
      inv_val := by
        have h := P.sum_F_mul_Finv a b c' (a + b + c') (ofAddLeft rfl) (ofAddLeft rfl)
        rw [Fintype.sum_eq_single (ofAddRight rfl) fun y hy ↦ (hy (right_ofAdd_eq rfl y)).elim] at h
        simpa using h }
  cocycle i₁ i₂ i₃ i₄ := by
    have hBCDE : i₁ + (i₂ + (i₃ + i₄)) = i₁ + i₂ + i₃ + i₄ := by
      rw [← add_assoc i₂ i₃ i₄, ← add_assoc i₁ (i₂ + i₃) i₄, add_assoc i₁ i₂ i₃]
    have hp := P.pentagon i₁ i₂ i₃ i₄ (i₁ + i₂ + i₃ + i₄) (i₁ + i₂) (i₁ + i₂ + i₃) (i₃ + i₄)
      (i₂ + (i₃ + i₄)) (ofAddIdx rfl) (ofAddIdx rfl) (ofAddIdx rfl)
      (ofAddIdx rfl) (ofAddIdx rfl) (ofAddIdx hBCDE)
    obtain ⟨hL, hR⟩ := ofAdd_pentagon_sides P.F _ P.pointed_F_eq_canonical
      (ofAddIdx (a := i₁) (b := i₂) rfl) (ofAddIdx (a := i₁ + i₂) (b := i₃) rfl)
      (ofAddIdx (a := i₁ + i₂ + i₃) (b := i₄) rfl) (ofAddIdx (a := i₃) (b := i₄) rfl)
      (ofAddIdx (a := i₂) (b := i₃ + i₄) rfl) (ofAddIdx hBCDE)
    refine inv_inj.mp (Units.ext ?_)
    simp only [mul_inv_rev, Units.val_mul, Units.inv_mk, ← mul_assoc]
    exact (mul_comm _ _).trans ((hL.symm.trans hp).trans hR)
  ω_zero i₁ i₃ := inv_inj.mp <| Units.ext <| by
    let j : Fin ((ofAdd I).N i₁ i₃ (i₁ + 0 + i₃)) := ofAddIdx (by simp)
    simpa only [inv_one, Units.inv_mk, Units.val_one] using
      (P.pointed_F_eq_canonical i₁ 0 i₃ (i₁ + 0 + i₃) ⟨i₁, (ofAdd I).unitRight i₁, j⟩
        ⟨i₃, (ofAdd I).unitLeft i₃, j⟩).symm.trans (P.triangle_self i₁ i₃ (i₁ + 0 + i₃) j)

@[simp]
theorem val_toTwistingCocycle_ω (P : FSymbols R (ofAdd I)) (a b c' : I) :
    (P.toTwistingCocycle.ω a b c' : R) =
      P.Finv a b c' (a + b + c') (ofAddRight rfl) (ofAddLeft rfl) := (rfl)

@[simp]
theorem val_inv_toTwistingCocycle_ω (P : FSymbols R (ofAdd I)) (a b c' : I) :
    (((P.toTwistingCocycle.ω a b c')⁻¹ : Rˣ) : R) =
      P.F a b c' (a + b + c') (ofAddLeft rfl) (ofAddRight rfl) :=
  (Units.inv_eq_val_inv (P.toTwistingCocycle.ω a b c')).symm

theorem F_eq_inv_toTwistingCocycle_ω (P : FSymbols R (ofAdd I)) (a b c' d : I)
    (x : (ofAdd I).Left a b c' d) (y : (ofAdd I).Right a b c' d) :
    P.F a b c' d x y = (((P.toTwistingCocycle.ω a b c')⁻¹ : Rˣ) : R) := by
  rw [val_inv_toTwistingCocycle_ω, pointed_F_eq_canonical]

theorem Finv_eq_toTwistingCocycle_ω (P : FSymbols R (ofAdd I)) (a b c' d : I)
    (y : (ofAdd I).Right a b c' d) (x : (ofAdd I).Left a b c' d) :
    P.Finv a b c' d y x = (P.toTwistingCocycle.ω a b c' : R) := by
  obtain rfl := eq_of_right_ofAdd y
  rw [val_toTwistingCocycle_ω, right_ofAdd_eq rfl y, left_ofAdd_eq rfl x]

@[simp]
theorem toTwistingCocycle_ofTwistingCocycle (c : TwistingCocycle I R) :
    (ofTwistingCocycle c).toTwistingCocycle = c := by ext; simp

@[simp]
theorem ofTwistingCocycle_toTwistingCocycle (P : FSymbols R (ofAdd I)) :
    ofTwistingCocycle P.toTwistingCocycle = P := by
  ext a b c' d x y
  rw [ofTwistingCocycle_F_apply, F_eq_inv_toTwistingCocycle_ω]

/-- Equivalence between F-symbols on `FusionRules.ofAdd I` and normalized `3`-cocycles
`TauCeti.GradedObject.TwistingCocycle I R`, with inverse `FSymbols.ofTwistingCocycle`. -/
def twistingCocycleEquiv : FSymbols R (ofAdd I) ≃ TwistingCocycle I R where
  toFun := toTwistingCocycle
  invFun := ofTwistingCocycle
  left_inv := ofTwistingCocycle_toTwistingCocycle
  right_inv := toTwistingCocycle_ofTwistingCocycle

@[simp]
theorem twistingCocycleEquiv_apply (P : FSymbols R (ofAdd I)) :
    twistingCocycleEquiv P = P.toTwistingCocycle := (rfl)

@[simp]
theorem twistingCocycleEquiv_symm_apply (c : TwistingCocycle I R) :
    twistingCocycleEquiv.symm c = ofTwistingCocycle c := (rfl)

/-- Equivalence between F-symbols on `FusionRules.ofMul M` for a finite monoid `M` and normalized
`3`-cocycles `TauCeti.GradedObject.TwistingCocycle (Additive M) R`. -/
def mulTwistingCocycleEquiv {M : Type u} [Fintype M] [DecidableEq M] [Monoid M] :
    FSymbols R (FusionRules.ofMul M) ≃ TwistingCocycle (Additive M) R :=
  (reindexEquiv (FusionRules.Equiv.ofMulAdditive M)).trans twistingCocycleEquiv

/-- Base change commutes with `FSymbols.ofTwistingCocycle`. -/
@[simp]
theorem map_ofTwistingCocycle {S : Type*} [CommSemiring S] (f : R →+* S)
    (c : TwistingCocycle I R) :
    (ofTwistingCocycle c).map f = ofTwistingCocycle (c.map (f : R →* S)) := by
  ext a b c' d x y
  rw [map_F, Matrix.map_apply, ofTwistingCocycle_F_apply, ofTwistingCocycle_F_apply,
    TwistingCocycle.map_ω, ← map_inv (Units.map (f : R →* S)), Units.coe_map]
  simp only [MonoidHom.coe_ofClass]

@[simp]
theorem toTwistingCocycle_map {S : Type*} [CommSemiring S] (f : R →+* S)
    (P : FSymbols R (ofAdd I)) :
    (P.map f).toTwistingCocycle = P.toTwistingCocycle.map (f : R →* S) := by
  rw [← toTwistingCocycle_ofTwistingCocycle (P.toTwistingCocycle.map (f : R →* S)),
    ← map_ofTwistingCocycle, ofTwistingCocycle_toTwistingCocycle]

end Pointed

end FSymbols

/-! ### Scalar braidings and abelian `3`-cocycles -/

namespace RSymbols

section Pointed

open FusionRules (ofAdd ofAddIdx add_eq_of_ofAdd fin_ofAdd_eq sum_fin_ofAdd_of_eq sum_ofAdd_fst)
open GradedObject (TwistingCocycle PointedBraiding)

variable {K : Type v} [CommSemiring K] {I : Type u} [Fintype I] [DecidableEq I] [AddCommMonoid I]
  {c : TwistingCocycle I K}

private theorem ofAdd_hexagon_forward_sides
    (R : ∀ a b d : I, Matrix (Fin ((ofAdd I).N a b d)) (Fin ((ofAdd I).N b a d)) K)
    (ρ : I → I → K) (hR : ∀ a b d i j, R a b d i j = ρ a b) (c : TwistingCocycle I K)
    {a b c' d e g : I} (i : Fin ((ofAdd I).N a b e)) (j : Fin ((ofAdd I).N e c' d))
    (n : Fin ((ofAdd I).N c' a g)) (o : Fin ((ofAdd I).N b g d)) :
    (∑ f : I, ∑ k : Fin ((ofAdd I).N b c' f), ∑ l : Fin ((ofAdd I).N a f d),
        ∑ m : Fin ((ofAdd I).N f a d),
        (FSymbols.ofTwistingCocycle c).F a b c' d ⟨e, i, j⟩ ⟨f, k, l⟩ * R a f d l m *
          (FSymbols.ofTwistingCocycle c).F b c' a d ⟨f, k, m⟩ ⟨g, n, o⟩ =
      (((c.ω a b c')⁻¹ : Kˣ) : K) * ρ a (b + c') * (((c.ω b c' a)⁻¹ : Kˣ) : K)) ∧
    (∑ p : Fin ((ofAdd I).N b a e), ∑ q : Fin ((ofAdd I).N a c' g),
        R a b e i p * (FSymbols.ofTwistingCocycle c).F b a c' d ⟨e, p, j⟩ ⟨g, q, o⟩ *
          R a c' g q n =
      ρ a b * (((c.ω b a c')⁻¹ : Kˣ) : K) * ρ a c') := by
  obtain rfl := add_eq_of_ofAdd i; obtain rfl := add_eq_of_ofAdd j
  obtain rfl := add_eq_of_ofAdd n
  refine ⟨?_, by rw [sum_fin_ofAdd_of_eq (add_comm b a),
    sum_fin_ofAdd_of_eq (add_comm a c'), FSymbols.ofTwistingCocycle_F_apply, hR, hR]⟩
  rw [sum_ofAdd_fst b c', sum_fin_ofAdd_of_eq (add_assoc a b c').symm,
    sum_fin_ofAdd_of_eq (by abel : (b + c') + a = a + b + c'),
    FSymbols.ofTwistingCocycle_F_apply, FSymbols.ofTwistingCocycle_F_apply, hR]

private theorem ofAdd_hexagon_reverse_sides
    (R : ∀ a b d : I, Matrix (Fin ((ofAdd I).N a b d)) (Fin ((ofAdd I).N b a d)) K)
    (ρ : I → I → K) (hR : ∀ a b d i j, R a b d i j = ρ a b) (c : TwistingCocycle I K)
    {a b c' d f g : I} (k : Fin ((ofAdd I).N b c' f)) (l : Fin ((ofAdd I).N a f d))
    (n : Fin ((ofAdd I).N c' a g)) (o : Fin ((ofAdd I).N g b d)) :
    (∑ e : I, ∑ i : Fin ((ofAdd I).N a b e), ∑ j : Fin ((ofAdd I).N e c' d),
        ∑ m : Fin ((ofAdd I).N c' e d),
        (FSymbols.ofTwistingCocycle c).Finv a b c' d ⟨f, k, l⟩ ⟨e, i, j⟩ * R e c' d j m *
          (FSymbols.ofTwistingCocycle c).Finv c' a b d ⟨e, i, m⟩ ⟨g, n, o⟩ =
      (c.ω a b c' : K) * ρ (a + b) c' * (c.ω c' a b : K)) ∧
    (∑ p : Fin ((ofAdd I).N c' b f), ∑ q : Fin ((ofAdd I).N a c' g),
        R b c' f k p * (FSymbols.ofTwistingCocycle c).Finv a c' b d ⟨f, p, l⟩ ⟨g, q, o⟩ *
          R a c' g q n =
      ρ b c' * (c.ω a c' b : K) * ρ a c') := by
  obtain rfl := add_eq_of_ofAdd k; obtain rfl := add_eq_of_ofAdd l
  obtain rfl := add_eq_of_ofAdd n
  refine ⟨?_, by rw [sum_fin_ofAdd_of_eq (add_comm c' b),
    sum_fin_ofAdd_of_eq (add_comm a c'), FSymbols.ofTwistingCocycle_Finv_apply, hR, hR]⟩
  rw [sum_ofAdd_fst a b, sum_fin_ofAdd_of_eq (add_assoc a b c'),
    sum_fin_ofAdd_of_eq (by abel : c' + (a + b) = a + (b + c')),
    FSymbols.ofTwistingCocycle_Finv_apply, FSymbols.ofTwistingCocycle_Finv_apply, hR]

/-- Construct `RSymbols` on `FSymbols.ofTwistingCocycle c` from a `PointedBraiding c`. -/
def ofPointedBraiding (B : PointedBraiding c) : RSymbols (FSymbols.ofTwistingCocycle c) where
  R a b _ := Matrix.of fun _ _ ↦ (B.r a b : K)
  Rinv a b _ := Matrix.of fun _ _ ↦ (((B.r a b)⁻¹ : Kˣ) : K)
  R_mul_Rinv a b d := by
    ext i₁ i₂
    have h := add_eq_of_ofAdd i₁
    rw [Subsingleton.elim i₁ i₂, Matrix.mul_apply, Matrix.one_apply_eq,
      sum_fin_ofAdd_of_eq (add_comm b a ▸ h)]
    simp only [Matrix.of_apply, Units.mul_inv]
  Rinv_mul_R a b d := by
    ext j₁ j₂
    have h' := add_eq_of_ofAdd j₁
    rw [Subsingleton.elim j₁ j₂, Matrix.mul_apply, Matrix.one_apply_eq,
      sum_fin_ofAdd_of_eq (add_comm a b ▸ h')]
    simp only [Matrix.of_apply, Units.inv_mul]
  hexagon_forward a b c' _ _ _ i j n o := by
    obtain ⟨hL, hR⟩ := ofAdd_hexagon_forward_sides
      (fun a b _ ↦ Matrix.of fun _ _ ↦ (B.r a b : K)) (fun a b ↦ (B.r a b : K))
      (fun _ _ _ _ _ ↦ rfl) c i j n o
    refine (hL.trans ?_).trans hR.symm
    simpa only [Units.val_mul, mul_assoc] using congrArg Units.val (B.hexagon_forward a b c')
  hexagon_reverse a b c' _ _ _ k l n o := by
    obtain ⟨hL, hR⟩ := ofAdd_hexagon_reverse_sides
      (fun a b _ ↦ Matrix.of fun _ _ ↦ (B.r a b : K)) (fun a b ↦ (B.r a b : K))
      (fun _ _ _ _ _ ↦ rfl) c k l n o
    refine (hL.trans ?_).trans hR.symm
    simpa only [Units.val_mul, mul_assoc] using congrArg Units.val (B.hexagon_reverse a b c')

@[simp]
theorem ofPointedBraiding_R_apply (B : PointedBraiding c) (a b d : I)
    (i : Fin ((ofAdd I).N a b d)) (j : Fin ((ofAdd I).N b a d)) :
    (ofPointedBraiding B).R a b d i j = (B.r a b : K) := Matrix.of_apply _ _ _

@[simp]
theorem ofPointedBraiding_Rinv_apply (B : PointedBraiding c) (a b d : I)
    (j : Fin ((ofAdd I).N b a d)) (i : Fin ((ofAdd I).N a b d)) :
    (ofPointedBraiding B).Rinv a b d j i = (((B.r a b)⁻¹ : Kˣ) : K) := Matrix.of_apply _ _ _

private theorem pointed_R_eq_canonical (Q : RSymbols (FSymbols.ofTwistingCocycle c)) (x y d : I)
    (i : Fin ((ofAdd I).N x y d)) (j : Fin ((ofAdd I).N y x d)) :
    Q.R x y d i j = Q.R x y (x + y) (ofAddIdx rfl) (ofAddIdx (add_comm y x)) := by
  obtain rfl := add_eq_of_ofAdd i
  rw [fin_ofAdd_eq rfl i, fin_ofAdd_eq (add_comm y x) j]

/-- Extract a `PointedBraiding c` from `RSymbols (FSymbols.ofTwistingCocycle c)`. -/
def toPointedBraiding (Q : RSymbols (FSymbols.ofTwistingCocycle c)) : PointedBraiding c where
  r a b :=
    { val := Q.R a b (a + b) (ofAddIdx rfl) (ofAddIdx (add_comm b a))
      inv := Q.Rinv a b (a + b) (ofAddIdx (add_comm b a)) (ofAddIdx rfl)
      val_inv := by
        have h := Q.sum_R_mul_Rinv a b (a + b) (ofAddIdx rfl) (ofAddIdx rfl)
        rw [sum_fin_ofAdd_of_eq (add_comm b a)] at h
        simpa using h
      inv_val := by
        have h := Q.sum_Rinv_mul_R a b (a + b)
          (ofAddIdx (add_comm b a)) (ofAddIdx (add_comm b a))
        rw [sum_fin_ofAdd_of_eq rfl] at h
        simpa using h }
  hexagon_forward a b c' := by
    have ho : b + (c' + a) = a + b + c' := by abel
    have hhex := Q.hexagon_forward a b c' (a + b + c') (a + b) (c' + a) (ofAddIdx rfl)
      (ofAddIdx rfl) (ofAddIdx rfl) (ofAddIdx ho)
    obtain ⟨hL, hR⟩ := ofAdd_hexagon_forward_sides Q.R _ Q.pointed_R_eq_canonical c
      (ofAddIdx (a := a) (b := b) rfl) (ofAddIdx (a := a + b) (b := c') rfl)
      (ofAddIdx (a := c') (b := a) rfl) (ofAddIdx ho)
    ext
    simpa only [Units.val_mul, mul_assoc] using (hL.symm.trans hhex).trans hR
  hexagon_reverse a b c' := by
    have ho : (c' + a) + b = a + (b + c') := by abel
    have hhex := Q.hexagon_reverse a b c' (a + (b + c')) (b + c') (c' + a) (ofAddIdx rfl)
      (ofAddIdx rfl) (ofAddIdx rfl) (ofAddIdx ho)
    obtain ⟨hL, hR⟩ := ofAdd_hexagon_reverse_sides Q.R _ Q.pointed_R_eq_canonical c
      (ofAddIdx (a := b) (b := c') rfl) (ofAddIdx (a := a) (b := b + c') rfl)
      (ofAddIdx (a := c') (b := a) rfl) (ofAddIdx ho)
    ext
    simpa only [Units.val_mul, mul_assoc] using (hL.symm.trans hhex).trans hR

@[simp]
theorem val_toPointedBraiding_r (Q : RSymbols (FSymbols.ofTwistingCocycle c)) (a b : I) :
    (Q.toPointedBraiding.r a b : K) =
      Q.R a b (a + b) (ofAddIdx rfl) (ofAddIdx (add_comm b a)) := (rfl)

@[simp]
theorem val_inv_toPointedBraiding_r (Q : RSymbols (FSymbols.ofTwistingCocycle c)) (a b : I) :
    (((Q.toPointedBraiding.r a b)⁻¹ : Kˣ) : K) =
      Q.Rinv a b (a + b) (ofAddIdx (add_comm b a)) (ofAddIdx rfl) :=
  (Units.inv_eq_val_inv (Q.toPointedBraiding.r a b)).symm

theorem R_eq_toPointedBraiding_r (Q : RSymbols (FSymbols.ofTwistingCocycle c)) (a b d : I)
    (i : Fin ((ofAdd I).N a b d)) (j : Fin ((ofAdd I).N b a d)) :
    Q.R a b d i j = (Q.toPointedBraiding.r a b : K) := by
  rw [val_toPointedBraiding_r, pointed_R_eq_canonical]

theorem Rinv_eq_inv_toPointedBraiding_r (Q : RSymbols (FSymbols.ofTwistingCocycle c)) (a b d : I)
    (j : Fin ((ofAdd I).N b a d)) (i : Fin ((ofAdd I).N a b d)) :
    Q.Rinv a b d j i = (((Q.toPointedBraiding.r a b)⁻¹ : Kˣ) : K) := by
  obtain rfl := add_eq_of_ofAdd i
  rw [val_inv_toPointedBraiding_r, fin_ofAdd_eq (add_comm b a) j, fin_ofAdd_eq rfl i]

@[simp]
theorem toPointedBraiding_ofPointedBraiding (B : PointedBraiding c) :
    (ofPointedBraiding B).toPointedBraiding = B := by ext; simp

@[simp]
theorem ofPointedBraiding_toPointedBraiding (Q : RSymbols (FSymbols.ofTwistingCocycle c)) :
    ofPointedBraiding Q.toPointedBraiding = Q := by
  ext a b d i j
  rw [ofPointedBraiding_R_apply, R_eq_toPointedBraiding_r]

/-- Equivalence between `RSymbols (FSymbols.ofTwistingCocycle c)` and
`TauCeti.GradedObject.PointedBraiding c`, with inverse `RSymbols.ofPointedBraiding`. -/
def pointedBraidingEquiv (c : TwistingCocycle I K) :
    RSymbols (FSymbols.ofTwistingCocycle c) ≃ PointedBraiding c where
  toFun := toPointedBraiding
  invFun := ofPointedBraiding
  left_inv := ofPointedBraiding_toPointedBraiding
  right_inv := toPointedBraiding_ofPointedBraiding

@[simp]
theorem pointedBraidingEquiv_apply (c : TwistingCocycle I K)
    (Q : RSymbols (FSymbols.ofTwistingCocycle c)) :
    pointedBraidingEquiv c Q = Q.toPointedBraiding := (rfl)

@[simp]
theorem pointedBraidingEquiv_symm_apply (c : TwistingCocycle I K) (B : PointedBraiding c) :
    (pointedBraidingEquiv c).symm B = ofPointedBraiding B := (rfl)

/-- Base change commutes with `RSymbols.ofPointedBraiding` up to `RSymbols.cast`. -/
@[simp]
theorem cast_map_ofPointedBraiding {L : Type*} [CommSemiring L] (f : K →+* L)
    (B : PointedBraiding c)
    (h : (FSymbols.ofTwistingCocycle c).map f = FSymbols.ofTwistingCocycle (c.map (f : K →* L)) :=
      FSymbols.map_ofTwistingCocycle f c) :
    ((ofPointedBraiding B).map f).cast h = ofPointedBraiding (B.map (f : K →* L)) := by
  ext
  simp

end Pointed

end RSymbols

/-! ### Complete classification of F-symbols and R-symbols on `ZMod 2` -/

namespace FSymbols

section ZMod2

open FusionRules (ofAdd ofAddLeft ofAddRight)
open GradedObject (TwistingCocycle)

variable {R : Type v} [CommSemiring R]

/-- The pointed F-symbols on `ZMod 2` with `F^{111}_1 = u` (`u * u = 1`) and `1` on all other
nonempty blocks. -/
def zmod2 (u : Rˣ) (hu : u * u = 1) : FSymbols R (ofAdd (ZMod 2)) :=
  ofTwistingCocycle (TwistingCocycle.zmod2 u hu)

theorem zmod2_eq_ofTwistingCocycle (u : Rˣ) (hu : u * u = 1) :
    zmod2 u hu = ofTwistingCocycle (TwistingCocycle.zmod2 u hu) := (rfl)

@[simp]
theorem zmod2_F_apply (u : Rˣ) (hu : u * u = 1) (a b c d : ZMod 2)
    (x : (ofAdd (ZMod 2)).Left a b c d) (y : (ofAdd (ZMod 2)).Right a b c d) :
    (zmod2 u hu).F a b c d x y = if a = 1 ∧ b = 1 ∧ c = 1 then (u : R) else 1 := by
  rw [zmod2_eq_ofTwistingCocycle, ofTwistingCocycle_F_apply, TwistingCocycle.zmod2_ω]
  split_ifs <;> simp [inv_eq_of_mul_eq_one_right hu]

@[simp]
theorem zmod2_Finv_apply (u : Rˣ) (hu : u * u = 1) (a b c d : ZMod 2)
    (y : (ofAdd (ZMod 2)).Right a b c d) (x : (ofAdd (ZMod 2)).Left a b c d) :
    (zmod2 u hu).Finv a b c d y x = if a = 1 ∧ b = 1 ∧ c = 1 then (u : R) else 1 := by
  rw [zmod2_eq_ofTwistingCocycle, ofTwistingCocycle_Finv_apply, TwistingCocycle.zmod2_ω]
  split_ifs <;> simp

/-- F-symbols on `FusionRules.ofAdd (ZMod 2)` are in bijection with `{ u : Rˣ // u * u = 1 }` via
the `(1, 1, 1)` entry `F^{111}_1 = u`, with inverse `FSymbols.zmod2`. -/
def zmod2Equiv : FSymbols R (ofAdd (ZMod 2)) ≃ { u : Rˣ // u * u = 1 } :=
  twistingCocycleEquiv.trans TwistingCocycle.zmod2Equiv

@[simp]
theorem val_zmod2Equiv_apply (P : FSymbols R (ofAdd (ZMod 2))) :
    (((zmod2Equiv P).val : Rˣ) : R) =
      P.F 1 1 1 1 (ofAddLeft (by decide)) (ofAddRight (by decide)) := by
  have hinv : (zmod2Equiv P).val = ((zmod2Equiv P).val)⁻¹ :=
    (inv_eq_of_mul_eq_one_right (zmod2Equiv P).property).symm
  rw [hinv, P.F_eq_inv_toTwistingCocycle_ω 1 1 1 1]
  simp [zmod2Equiv]

@[simp]
theorem zmod2Equiv_symm_apply (u : { u : Rˣ // u * u = 1 }) :
    zmod2Equiv.symm u = zmod2 u.val u.property := by
  simp [zmod2Equiv, zmod2_eq_ofTwistingCocycle]

@[simp]
theorem zmod2Equiv_zmod2 (u : Rˣ) (hu : u * u = 1) : zmod2Equiv (zmod2 u hu) = ⟨u, hu⟩ := by
  rw [← zmod2Equiv_symm_apply ⟨u, hu⟩]
  exact zmod2Equiv.apply_symm_apply ⟨u, hu⟩

@[simp]
theorem zmod2_zmod2Equiv (P : FSymbols R (ofAdd (ZMod 2))) :
    zmod2 (zmod2Equiv P).val (zmod2Equiv P).property = P := by
  rw [← zmod2Equiv_symm_apply (zmod2Equiv P)]
  exact zmod2Equiv.symm_apply_apply P

end ZMod2

end FSymbols

namespace RSymbols

section ZMod2

open FusionRules (ofAdd ofAddIdx)
open GradedObject (TwistingCocycle PointedBraiding)

section CommSemiring

variable {K : Type v} [CommSemiring K]

/-- Construct R-symbols on `FSymbols.zmod2 u hu` from a square root `r : Kˣ` of `u` (`r * r = u`),
giving `R^{11}_0 = r` and `1` on all unit blocks. -/
def zmod2 {u : Kˣ} (hu : u * u = 1) (r : Kˣ) (hr : r * r = u) : RSymbols (FSymbols.zmod2 u hu) :=
  (ofPointedBraiding (PointedBraiding.zmod2 hu r hr)).cast
    (FSymbols.zmod2_eq_ofTwistingCocycle u hu).symm

theorem zmod2_eq_cast_ofPointedBraiding {u : Kˣ} (hu : u * u = 1) (r : Kˣ) (hr : r * r = u) :
    zmod2 hu r hr =
      (ofPointedBraiding (PointedBraiding.zmod2 hu r hr)).cast
        (FSymbols.zmod2_eq_ofTwistingCocycle u hu).symm := (rfl)

@[simp]
theorem zmod2_R_apply {u : Kˣ} (hu : u * u = 1) (r : Kˣ) (hr : r * r = u) (a b c : ZMod 2)
    (i : Fin ((ofAdd (ZMod 2)).N a b c)) (j : Fin ((ofAdd (ZMod 2)).N b a c)) :
    (zmod2 hu r hr).R a b c i j = if a = 1 ∧ b = 1 then (r : K) else 1 := by
  rw [zmod2_eq_cast_ofPointedBraiding, cast_R, ofPointedBraiding_R_apply, PointedBraiding.zmod2_r]
  split_ifs <;> simp

@[simp]
theorem zmod2_Rinv_apply {u : Kˣ} (hu : u * u = 1) (r : Kˣ) (hr : r * r = u) (a b c : ZMod 2)
    (j : Fin ((ofAdd (ZMod 2)).N b a c)) (i : Fin ((ofAdd (ZMod 2)).N a b c)) :
    (zmod2 hu r hr).Rinv a b c j i = if a = 1 ∧ b = 1 then ((r⁻¹ : Kˣ) : K) else 1 := by
  rw [zmod2_eq_cast_ofPointedBraiding, cast_Rinv, ofPointedBraiding_Rinv_apply,
    PointedBraiding.zmod2_r]
  split_ifs <;> simp

/-- R-symbols on `FSymbols.zmod2 u hu` are in bijection with `{ r : Kˣ // r * r = u }` via the
nontrivial braiding entry `R^{11}_0 = r`, witnessing `(R^{11}_0)^2 = F^{111}_1`, with inverse
`RSymbols.zmod2`. -/
def zmod2Equiv (u : Kˣ) (hu : u * u = 1) :
    RSymbols (FSymbols.zmod2 u hu) ≃ { r : Kˣ // r * r = u } :=
  (castEquiv (FSymbols.zmod2_eq_ofTwistingCocycle u hu)).trans
    ((pointedBraidingEquiv (TwistingCocycle.zmod2 u hu)).trans (PointedBraiding.zmod2Equiv u hu))

@[simp]
theorem val_zmod2Equiv_apply (u : Kˣ) (hu : u * u = 1) (Q : RSymbols (FSymbols.zmod2 u hu)) :
    (((zmod2Equiv u hu Q).val : Kˣ) : K) =
      Q.R 1 1 0 (ofAddIdx (by decide)) (ofAddIdx (by decide)) := by
  have h := (congrArg Units.val (PointedBraiding.coe_zmod2Equiv_apply u hu
    (Q.cast (FSymbols.zmod2_eq_ofTwistingCocycle u hu)).toPointedBraiding)).trans
    (R_eq_toPointedBraiding_r (Q.cast (FSymbols.zmod2_eq_ofTwistingCocycle u hu)) 1 1 0
      (ofAddIdx (by decide)) (ofAddIdx (by decide))).symm
  simpa [zmod2Equiv] using h

@[simp]
theorem zmod2Equiv_symm_apply (u : Kˣ) (hu : u * u = 1) (r : { r : Kˣ // r * r = u }) :
    (zmod2Equiv u hu).symm r = zmod2 hu r.val r.property := by
  simp [zmod2Equiv, zmod2_eq_cast_ofPointedBraiding]

@[simp]
theorem zmod2Equiv_zmod2 {u : Kˣ} (hu : u * u = 1) (r : Kˣ) (hr : r * r = u) :
    zmod2Equiv u hu (zmod2 hu r hr) = ⟨r, hr⟩ := by
  rw [← zmod2Equiv_symm_apply u hu ⟨r, hr⟩]
  exact (zmod2Equiv u hu).apply_symm_apply ⟨r, hr⟩

@[simp]
theorem zmod2_zmod2Equiv (u : Kˣ) (hu : u * u = 1) (Q : RSymbols (FSymbols.zmod2 u hu)) :
    zmod2 hu (zmod2Equiv u hu Q).val (zmod2Equiv u hu Q).property = Q := by
  rw [← zmod2Equiv_symm_apply u hu (zmod2Equiv u hu Q)]
  exact (zmod2Equiv u hu).symm_apply_apply Q

end CommSemiring

section CommRing

variable {K : Type v} [CommRing K]

/-- For the trivial `ZMod 2` F-symbols (`u = 1`), `r = -1` gives the super-vector-space braiding
`R^{11}_0 = -1`. -/
def zmod2Super : RSymbols (FSymbols.zmod2 (1 : Kˣ) (mul_one 1)) :=
  zmod2 (mul_one 1) (-1) (by simp)

@[simp]
theorem zmod2Super_R_apply (a b c : ZMod 2)
    (i : Fin ((ofAdd (ZMod 2)).N a b c)) (j : Fin ((ofAdd (ZMod 2)).N b a c)) :
    (zmod2Super : RSymbols (FSymbols.zmod2 (1 : Kˣ) (mul_one 1))).R a b c i j =
      if a = 1 ∧ b = 1 then -1 else 1 := by
  simp [zmod2Super]

@[simp]
theorem zmod2Super_Rinv_apply (a b c : ZMod 2)
    (j : Fin ((ofAdd (ZMod 2)).N b a c)) (i : Fin ((ofAdd (ZMod 2)).N a b c)) :
    (zmod2Super : RSymbols (FSymbols.zmod2 (1 : Kˣ) (mul_one 1))).Rinv a b c j i =
      if a = 1 ∧ b = 1 then -1 else 1 := by
  simp [zmod2Super]

end CommRing

/-- Over `ℤ`, the nontrivial `ZMod 2` F-symbols with `F^{111}_1 = -1` admit no R-symbols, since
`-1` is not a square in `ℤˣ`. -/
instance instIsEmptyZMod2NegOneInt : IsEmpty (RSymbols (FSymbols.zmod2 (-1 : ℤˣ) (by decide))) :=
  ⟨fun Q ↦ by
    obtain ⟨r, hr⟩ := zmod2Equiv (-1 : ℤˣ) (by decide) Q
    rcases Int.units_eq_one_or r with rfl | rfl <;> exact absurd hr (by decide)⟩

end ZMod2

end RSymbols

end TauCeti
