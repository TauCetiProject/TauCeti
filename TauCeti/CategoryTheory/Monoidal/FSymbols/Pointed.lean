/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.ZMod.Basic
public import TauCeti.CategoryTheory.GradedObject.Twisted.Basic
public import TauCeti.CategoryTheory.Monoidal.FSymbols.Map

/-!
# Pointed fusion rules, 3-cocycles, and `ℤ/2` examples

A fusion rule is **pointed** when the simples form a monoid `I` and tensor product is the monoid
operation (`N_{ab}^c = [a + b = c]`). Every composite basis space `Left a b c d` and `Right a b c d`
then has cardinality `1` when `a + b + c = d` and `0` otherwise, so the matrix-level F-symbol and
R-symbol equations collapse to scalar group-cohomological equations in `Rˣ`:

* `TauCeti.FusionRules.ofAddMonoid I` and `TauCeti.FusionRules.ofMonoid G`: pointed fusion rules
  attached to an additive or multiplicative monoid.
* `TauCeti.FSymbols.twistingCocycleEquiv`: equivalence between `FSymbols R (ofAddMonoid I)` and
  `TauCeti.GradedObject.TwistingCocycle I R`, matching `F^{abc}_{a+b+c} = (ω a b c)⁻¹` and
  `Finv^{abc}_{a+b+c} = ω a b c`.
* `TauCeti.PointedBraiding c` and `TauCeti.RSymbols.pointedBraidingEquiv`: for a commutative
  additive monoid `I`, equivalence between `RSymbols (FSymbols.ofTwistingCocycle c)` and
  Eilenberg–MacLane abelian `3`-cocycle braidings `r : I → I → Rˣ` for `c`.
* `TauCeti.FSymbols.zmod2Equiv` and `TauCeti.RSymbols.zmod2Equiv`: complete classification on
  `ZMod 2`, identifying F-symbols with `{ u : Rˣ // u * u = 1 }` via `F^{111}_1 = u` and R-symbols
  with `{ r : Rˣ // r * r = u }` via `(R^{11}_0)^2 = F^{111}_1`, including the symmetric and super
  braidings for `u = 1` and nonexistence over `ℤ` for `u = -1`.

## References

* [P. Etingof, S. Gelaki, D. Nikshych, V. Ostrik, *Tensor Categories*][egno15], §2.3 (Ex. 2.3.8),
  §2.6 (Prop. 2.6.1), and §8.4 (abelian `3`-cocycles).
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
  N_unit_left a b := by simp
  N_unit_right a b := by simp

@[simp]
theorem ofAddMonoid_unit (I : Type u) [AddMonoid I] [DecidableEq I] :
    (ofAddMonoid I).unit = 0 :=
  (rfl)

@[simp]
theorem ofAddMonoid_N (I : Type u) [AddMonoid I] [DecidableEq I] (a b c : I) :
    (ofAddMonoid I).N a b c = if a + b = c then 1 else 0 :=
  (rfl)

/-- Pointed fusion rules on a multiplicative monoid `G`, with `unit = 1` and
`N a b c = if a * b = c then 1 else 0`. -/
def ofMonoid (G : Type u) [Monoid G] [DecidableEq G] : FusionRules G where
  unit := 1
  N a b c := if a * b = c then 1 else 0
  N_unit_left a b := by simp
  N_unit_right a b := by simp

@[simp]
theorem ofMonoid_unit (G : Type u) [Monoid G] [DecidableEq G] :
    (ofMonoid G).unit = 1 :=
  (rfl)

@[simp]
theorem ofMonoid_N (G : Type u) [Monoid G] [DecidableEq G] (a b c : G) :
    (ofMonoid G).N a b c = if a * b = c then 1 else 0 :=
  (rfl)

/-- Reindexing `ofAddMonoid (Additive G)` along `Additive.toMul` recovers `ofMonoid G`. -/
@[simp]
theorem reindex_ofAddMonoid_additive (G : Type u) [Monoid G] [DecidableEq G] :
    (ofAddMonoid (Additive G)).reindex Additive.toMul = ofMonoid G := by
  ext <;> simp [← ofMul_mul]

section AddMonoidHelpers

variable {I : Type u} [AddMonoid I] [DecidableEq I]

/-- An index in `Fin ((ofAddMonoid I).N a b c)` witnesses `a + b = c`. -/
theorem eq_of_fin_ofAddMonoid {a b c : I} (i : Fin ((ofAddMonoid I).N a b c)) : a + b = c := by
  by_contra h
  exact Nat.not_lt_zero i.val (by simpa [h] using i.isLt)

/-- The canonical basis index in `Fin ((ofAddMonoid I).N a b c)` when `a + b = c`. -/
def ofAddMonoidIdx {a b c : I} (h : a + b = c) : Fin ((ofAddMonoid I).N a b c) :=
  ⟨0, by simp [h]⟩

@[simp]
theorem val_ofAddMonoidIdx {a b c : I} (h : a + b = c) : (ofAddMonoidIdx h).val = 0 :=
  (rfl)

theorem fin_ofAddMonoid_eq {a b c : I} (h : a + b = c) (i : Fin ((ofAddMonoid I).N a b c)) :
    i = ofAddMonoidIdx h :=
  Fin.ext (by simpa [h] using i.isLt)

theorem eq_of_left_ofAddMonoid {a b c d : I} (x : (ofAddMonoid I).Left a b c d) :
    a + b + c = d := by
  rw [eq_of_fin_ofAddMonoid x.2.1, eq_of_fin_ofAddMonoid x.2.2]

theorem eq_of_right_ofAddMonoid {a b c d : I} (y : (ofAddMonoid I).Right a b c d) :
    a + b + c = d := by
  rw [add_assoc, eq_of_fin_ofAddMonoid y.2.1, eq_of_fin_ofAddMonoid y.2.2]

/-- The unique element of `(ofAddMonoid I).Left a b c d` when `a + b + c = d`. -/
def ofAddMonoidLeft {a b c d : I} (h : a + b + c = d) : (ofAddMonoid I).Left a b c d :=
  ⟨a + b, ofAddMonoidIdx rfl, ofAddMonoidIdx h⟩

/-- The unique element of `(ofAddMonoid I).Right a b c d` when `a + b + c = d`. -/
def ofAddMonoidRight {a b c d : I} (h : a + b + c = d) : (ofAddMonoid I).Right a b c d :=
  ⟨b + c, ofAddMonoidIdx rfl, ofAddMonoidIdx (by rwa [← add_assoc])⟩

theorem left_ofAddMonoid_eq {a b c d : I} (h : a + b + c = d)
    (x : (ofAddMonoid I).Left a b c d) : x = ofAddMonoidLeft h := by
  rcases x with ⟨e, i, j⟩
  obtain rfl : a + b = e := eq_of_fin_ofAddMonoid i
  simp [ofAddMonoidLeft, fin_ofAddMonoid_eq rfl i, fin_ofAddMonoid_eq h j]

theorem right_ofAddMonoid_eq {a b c d : I} (h : a + b + c = d)
    (y : (ofAddMonoid I).Right a b c d) : y = ofAddMonoidRight h := by
  rcases y with ⟨f, k, l⟩
  obtain rfl : b + c = f := eq_of_fin_ofAddMonoid k
  have h' : a + (b + c) = d := by rwa [← add_assoc]
  simp [ofAddMonoidRight, fin_ofAddMonoid_eq rfl k, fin_ofAddMonoid_eq h' l]

theorem sum_fin_ofAddMonoid_of_eq {M : Type*} [AddCommMonoid M] {a b c : I} (h : a + b = c)
    (f : Fin ((ofAddMonoid I).N a b c) → M) :
    ∑ i, f i = f (ofAddMonoidIdx h) :=
  Fintype.sum_eq_single (ofAddMonoidIdx h) fun i hi ↦ (hi (fin_ofAddMonoid_eq h i)).elim

theorem sum_fin_ofAddMonoid_of_ne {M : Type*} [AddCommMonoid M] {a b c : I} (h : a + b ≠ c)
    (f : Fin ((ofAddMonoid I).N a b c) → M) :
    ∑ i, f i = 0 := by
  have : IsEmpty (Fin ((ofAddMonoid I).N a b c)) := ⟨fun i ↦ h (eq_of_fin_ofAddMonoid i)⟩
  exact Fintype.sum_empty f

theorem sum_ofAddMonoid_fst {M : Type*} [AddCommMonoid M] [Fintype I] (a b : I)
    (g : ∀ e : I, Fin ((ofAddMonoid I).N a b e) → M) :
    ∑ e : I, ∑ i : Fin ((ofAddMonoid I).N a b e), g e i = g (a + b) (ofAddMonoidIdx rfl) := by
  rw [Fintype.sum_eq_single (a + b)]
  · exact sum_fin_ofAddMonoid_of_eq rfl _
  · intro e he
    exact sum_fin_ofAddMonoid_of_ne he.symm _

end AddMonoidHelpers

end FusionRules

/-! ### Equivalence between pointed F-symbols and normalized 3-cocycles -/

namespace FSymbols

section Pointed

variable {R : Type v} [CommRing R] {I : Type u} [Fintype I] [DecidableEq I] [AddMonoid I]

/-- The F-symbols attached to a normalized `3`-cocycle `c : GradedObject.TwistingCocycle I R`, with
`F^{abc}_{a+b+c} = (c.ω a b c)⁻¹` and `Finv^{abc}_{a+b+c} = c.ω a b c`. -/
def ofTwistingCocycle (c : GradedObject.TwistingCocycle I R) :
    FSymbols R (FusionRules.ofAddMonoid I) where
  F a b c' _ := Matrix.of fun _ _ ↦ (((c.ω a b c')⁻¹ : Rˣ) : R)
  Finv a b c' _ := Matrix.of fun _ _ ↦ (c.ω a b c' : R)
  F_mul_Finv a b c' d := by
    ext x₁ x₂
    have h : a + b + c' = d := FusionRules.eq_of_left_ofAddMonoid x₁
    rw [FusionRules.left_ofAddMonoid_eq h x₁, FusionRules.left_ofAddMonoid_eq h x₂,
      Matrix.mul_apply, Matrix.one_apply_eq,
      Fintype.sum_eq_single (FusionRules.ofAddMonoidRight h)]
    · simp only [Matrix.of_apply, Units.inv_mul]
    · intro y hy
      exact (hy (FusionRules.right_ofAddMonoid_eq h y)).elim
  Finv_mul_F a b c' d := by
    ext y₁ y₂
    have h : a + b + c' = d := FusionRules.eq_of_right_ofAddMonoid y₁
    rw [FusionRules.right_ofAddMonoid_eq h y₁, FusionRules.right_ofAddMonoid_eq h y₂,
      Matrix.mul_apply, Matrix.one_apply_eq,
      Fintype.sum_eq_single (FusionRules.ofAddMonoidLeft h)]
    · simp only [Matrix.of_apply, Units.mul_inv]
    · intro x hx
      exact (hx (FusionRules.left_ofAddMonoid_eq h x)).elim
  pentagon A B C D E p q r s i₁ i₂ i₃ k m _ := by
    obtain rfl : A + B = p := FusionRules.eq_of_fin_ofAddMonoid i₁
    obtain rfl : A + B + C = q := FusionRules.eq_of_fin_ofAddMonoid i₂
    obtain rfl : A + B + C + D = E := FusionRules.eq_of_fin_ofAddMonoid i₃
    obtain rfl : C + D = r := FusionRules.eq_of_fin_ofAddMonoid k
    obtain rfl : B + (C + D) = s := FusionRules.eq_of_fin_ofAddMonoid m
    have hLHS : A + B + (C + D) = A + B + C + D := (add_assoc (A + B) C D).symm
    have hBC : A + (B + C) = A + B + C := (add_assoc A B C).symm
    have hBCD : B + C + D = B + (C + D) := add_assoc B C D
    rw [FusionRules.sum_fin_ofAddMonoid_of_eq hLHS, FusionRules.sum_ofAddMonoid_fst B C,
      FusionRules.sum_fin_ofAddMonoid_of_eq hBC, FusionRules.sum_fin_ofAddMonoid_of_eq hBCD]
    have hcoc :
        ((c.ω (A + B) C D)⁻¹ * (c.ω A B (C + D))⁻¹ : Rˣ) =
          (c.ω A B C)⁻¹ * (c.ω A (B + C) D)⁻¹ * (c.ω B C D)⁻¹ := by
      have h := congrArg Inv.inv (c.cocycle A B C D)
      simpa [mul_inv, mul_comm, mul_left_comm, mul_assoc] using h
    simpa [Matrix.of_apply, Units.val_mul, mul_assoc] using congrArg Units.val hcoc
  triangle a c' d j l := by
    have h : a + c' = d := FusionRules.eq_of_fin_ofAddMonoid j
    rw [FusionRules.fin_ofAddMonoid_eq h j, FusionRules.fin_ofAddMonoid_eq h l]
    simp

@[simp]
theorem ofTwistingCocycle_F_apply (c : GradedObject.TwistingCocycle I R) (a b c' d : I)
    (x : (FusionRules.ofAddMonoid I).Left a b c' d)
    (y : (FusionRules.ofAddMonoid I).Right a b c' d) :
    (ofTwistingCocycle c).F a b c' d x y = (((c.ω a b c')⁻¹ : Rˣ) : R) :=
  Matrix.of_apply _ _ _

@[simp]
theorem ofTwistingCocycle_Finv_apply (c : GradedObject.TwistingCocycle I R) (a b c' d : I)
    (y : (FusionRules.ofAddMonoid I).Right a b c' d)
    (x : (FusionRules.ofAddMonoid I).Left a b c' d) :
    (ofTwistingCocycle c).Finv a b c' d y x = (c.ω a b c' : R) :=
  Matrix.of_apply _ _ _

/-- The invertible scalar `Finv^{abc}_{a+b+c} : Rˣ` with inverse `F^{abc}_{a+b+c}` extracted from
pointed F-symbols. -/
def pointedUnit (P : FSymbols R (FusionRules.ofAddMonoid I)) (a b c' : I) : Rˣ where
  val := P.Finv a b c' (a + b + c')
    (FusionRules.ofAddMonoidRight rfl) (FusionRules.ofAddMonoidLeft rfl)
  inv := P.F a b c' (a + b + c')
    (FusionRules.ofAddMonoidLeft rfl) (FusionRules.ofAddMonoidRight rfl)
  val_inv := by
    have h := P.sum_Finv_mul_F a b c' (a + b + c')
      (FusionRules.ofAddMonoidRight rfl) (FusionRules.ofAddMonoidRight rfl)
    rw [Fintype.sum_eq_single (FusionRules.ofAddMonoidLeft rfl)] at h
    · simpa using h
    · intro x hx
      exact (hx (FusionRules.left_ofAddMonoid_eq rfl x)).elim
  inv_val := by
    have h := P.sum_F_mul_Finv a b c' (a + b + c')
      (FusionRules.ofAddMonoidLeft rfl) (FusionRules.ofAddMonoidLeft rfl)
    rw [Fintype.sum_eq_single (FusionRules.ofAddMonoidRight rfl)] at h
    · simpa using h
    · intro y hy
      exact (hy (FusionRules.right_ofAddMonoid_eq rfl y)).elim

@[simp]
theorem val_pointedUnit (P : FSymbols R (FusionRules.ofAddMonoid I)) (a b c' : I) :
    (P.pointedUnit a b c' : R) =
      P.Finv a b c' (a + b + c')
        (FusionRules.ofAddMonoidRight rfl) (FusionRules.ofAddMonoidLeft rfl) :=
  (rfl)

@[simp]
theorem val_inv_pointedUnit (P : FSymbols R (FusionRules.ofAddMonoid I)) (a b c' : I) :
    (((P.pointedUnit a b c')⁻¹ : Rˣ) : R) =
      P.F a b c' (a + b + c')
        (FusionRules.ofAddMonoidLeft rfl) (FusionRules.ofAddMonoidRight rfl) :=
  (Units.inv_eq_val_inv (P.pointedUnit a b c')).symm

/-- Extract the normalized `3`-cocycle `ω a b c = Finv^{abc}_{a+b+c}` from pointed F-symbols. -/
def toTwistingCocycle (P : FSymbols R (FusionRules.ofAddMonoid I)) :
    GradedObject.TwistingCocycle I R where
  ω := P.pointedUnit
  cocycle i₁ i₂ i₃ i₄ := by
    have hLHS : i₁ + i₂ + (i₃ + i₄) = i₁ + i₂ + i₃ + i₄ :=
      (add_assoc (i₁ + i₂) i₃ i₄).symm
    have hBC : i₁ + (i₂ + i₃) = i₁ + i₂ + i₃ := (add_assoc i₁ i₂ i₃).symm
    have hBCD : i₂ + i₃ + i₄ = i₂ + (i₃ + i₄) := add_assoc i₂ i₃ i₄
    have hBCDE : i₁ + (i₂ + (i₃ + i₄)) = i₁ + i₂ + i₃ + i₄ := by
      rw [← hBCD, ← add_assoc i₁ (i₂ + i₃) i₄, hBC]
    have hp := P.pentagon i₁ i₂ i₃ i₄ (i₁ + i₂ + i₃ + i₄)
      (i₁ + i₂) (i₁ + i₂ + i₃) (i₃ + i₄) (i₂ + (i₃ + i₄))
      (FusionRules.ofAddMonoidIdx rfl) (FusionRules.ofAddMonoidIdx rfl)
      (FusionRules.ofAddMonoidIdx rfl) (FusionRules.ofAddMonoidIdx rfl)
      (FusionRules.ofAddMonoidIdx rfl) (FusionRules.ofAddMonoidIdx hBCDE)
    rw [FusionRules.sum_fin_ofAddMonoid_of_eq hLHS, FusionRules.sum_ofAddMonoid_fst i₂ i₃,
      FusionRules.sum_fin_ofAddMonoid_of_eq hBC, FusionRules.sum_fin_ofAddMonoid_of_eq hBCD] at hp
    have eqF (a b c' d : I) (h : a + b + c' = d)
        (x : (FusionRules.ofAddMonoid I).Left a b c' d)
        (y : (FusionRules.ofAddMonoid I).Right a b c' d) :
        P.F a b c' d x y =
          P.F a b c' (a + b + c') (FusionRules.ofAddMonoidLeft rfl)
            (FusionRules.ofAddMonoidRight rfl) := by
      subst h
      rw [FusionRules.left_ofAddMonoid_eq rfl x, FusionRules.right_ofAddMonoid_eq rfl y]
    rw [eqF (i₁ + i₂) i₃ i₄ _ rfl, eqF i₁ i₂ (i₃ + i₄) _ hLHS,
      eqF i₁ i₂ i₃ _ rfl, eqF i₁ (i₂ + i₃) i₄ _ (by rw [hBC]),
      eqF i₂ i₃ i₄ _ hBCD] at hp
    have hrev (x y z : R) : x * y * z = z * y * x := by
      rw [mul_comm (x * y) z, mul_comm x y, mul_assoc]
    refine inv_inj.mp (Units.ext ?_)
    simp only [mul_inv, Units.val_mul, val_inv_pointedUnit]
    exact hp.trans (hrev _ _ _)
  ω_zero i₁ i₃ := by
    ext
    rw [val_pointedUnit]
    have htri :=
      P.Finv_triangle_self i₁ i₃ (i₁ + 0 + i₃) (FusionRules.ofAddMonoidIdx (by simp))
    have hR : FusionRules.ofAddMonoidRight (a := i₁) (b := 0) (c := i₃) rfl =
        ⟨i₃, (FusionRules.ofAddMonoid I).unitLeft i₃,
          FusionRules.ofAddMonoidIdx (by simp)⟩ :=
      (FusionRules.right_ofAddMonoid_eq rfl _).symm
    have hL : FusionRules.ofAddMonoidLeft (a := i₁) (b := 0) (c := i₃) rfl =
        ⟨i₁, (FusionRules.ofAddMonoid I).unitRight i₁,
          FusionRules.ofAddMonoidIdx (by simp)⟩ :=
      (FusionRules.left_ofAddMonoid_eq rfl _).symm
    rw [hR, hL]
    exact htri

@[simp]
theorem val_toTwistingCocycle_ω (P : FSymbols R (FusionRules.ofAddMonoid I)) (a b c' : I) :
    (P.toTwistingCocycle.ω a b c' : R) =
      P.Finv a b c' (a + b + c')
        (FusionRules.ofAddMonoidRight rfl) (FusionRules.ofAddMonoidLeft rfl) :=
  (rfl)

@[simp]
theorem val_inv_toTwistingCocycle_ω (P : FSymbols R (FusionRules.ofAddMonoid I)) (a b c' : I) :
    (((P.toTwistingCocycle.ω a b c')⁻¹ : Rˣ) : R) =
      P.F a b c' (a + b + c')
        (FusionRules.ofAddMonoidLeft rfl) (FusionRules.ofAddMonoidRight rfl) :=
  val_inv_pointedUnit P a b c'

/-- Equivalence between F-symbols on `FusionRules.ofAddMonoid I` and normalized `3`-cocycles
`TauCeti.GradedObject.TwistingCocycle I R`, matching `F^{abc}_{a+b+c} = (ω a b c)⁻¹`. -/
def twistingCocycleEquiv :
    FSymbols R (FusionRules.ofAddMonoid I) ≃ GradedObject.TwistingCocycle I R where
  toFun := toTwistingCocycle
  invFun := ofTwistingCocycle
  left_inv P := by
    ext a b c' d x y
    have h : a + b + c' = d := FusionRules.eq_of_left_ofAddMonoid x
    subst h
    rw [ofTwistingCocycle_F_apply, val_inv_toTwistingCocycle_ω,
      FusionRules.left_ofAddMonoid_eq rfl x, FusionRules.right_ofAddMonoid_eq rfl y]
  right_inv c := by
    ext a b c'
    rfl

@[simp]
theorem twistingCocycleEquiv_apply (P : FSymbols R (FusionRules.ofAddMonoid I)) :
    twistingCocycleEquiv P = P.toTwistingCocycle :=
  (rfl)

@[simp]
theorem twistingCocycleEquiv_symm_apply (c : GradedObject.TwistingCocycle I R) :
    twistingCocycleEquiv.symm c = ofTwistingCocycle c :=
  (rfl)

/-- Base change commutes with `FSymbols.ofTwistingCocycle`. -/
theorem map_ofTwistingCocycle {S : Type*} [CommRing S] (f : R →+* S)
    (c : GradedObject.TwistingCocycle I R) :
    (ofTwistingCocycle c).map f =
      ofTwistingCocycle
        { ω := fun a b c' ↦ Units.map (f : R →* S) (c.ω a b c')
          cocycle := fun i₁ i₂ i₃ i₄ ↦ by
            simpa [← map_mul] using
              congrArg (Units.map (f : R →* S)) (c.cocycle i₁ i₂ i₃ i₄)
          ω_zero := fun i₁ i₃ ↦ by simp } := by
  ext a b c' d x y
  rw [map_F_apply, ofTwistingCocycle_F_apply, ofTwistingCocycle_F_apply,
    ← map_inv (Units.map (f : R →* S)), Units.coe_map]
  rfl

end Pointed

end FSymbols

/-! ### Pointed braidings and abelian 3-cocycles -/

/-- A scalar braiding datum `r : I → I → Kˣ` on a commutative additive monoid `I` compatible
with a normalized `3`-cocycle `c : GradedObject.TwistingCocycle I K`, i.e., an Eilenberg–MacLane
abelian `3`-cocycle extending `c`. -/
@[ext]
structure PointedBraiding {I : Type u} [AddCommMonoid I] {K : Type v} [CommRing K]
    (c : GradedObject.TwistingCocycle I K) where
  /-- The scalar braiding entries `r a b = R^{ab}_{a+b}`. -/
  r : I → I → Kˣ
  /-- Forward scalar hexagon identity. -/
  hexagon_forward (a b c' : I) :
    (c.ω a b c')⁻¹ * r a (b + c') * (c.ω b c' a)⁻¹ = r a b * (c.ω b a c')⁻¹ * r a c'
  /-- Reverse scalar hexagon identity. -/
  hexagon_reverse (a b c' : I) :
    c.ω a b c' * r (a + b) c' * c.ω c' a b = r b c' * c.ω a c' b * r a c'

namespace PointedBraiding

variable {I : Type u} [AddCommMonoid I] {K : Type v} [CommRing K]
  {c : GradedObject.TwistingCocycle I K}

@[simp]
theorem r_zero_right (B : PointedBraiding c) (a : I) : B.r a 0 = 1 := by
  simpa using (B.hexagon_forward a 0 0).symm

@[simp]
theorem r_zero_left (B : PointedBraiding c) (a : I) : B.r 0 a = 1 := by
  simpa using (B.hexagon_reverse 0 0 a).symm

end PointedBraiding

namespace RSymbols

section Pointed

variable {K : Type v} [CommRing K] {I : Type u} [Fintype I] [DecidableEq I] [AddCommMonoid I]
  {c : GradedObject.TwistingCocycle I K}

/-- Construct `RSymbols` on `FSymbols.ofTwistingCocycle c` from a `PointedBraiding c`. -/
def ofPointedBraiding (B : PointedBraiding c) : RSymbols (FSymbols.ofTwistingCocycle c) where
  R a b _ := Matrix.of fun _ _ ↦ (B.r a b : K)
  Rinv a b _ := Matrix.of fun _ _ ↦ (((B.r a b)⁻¹ : Kˣ) : K)
  R_mul_Rinv a b d := by
    ext i₁ i₂
    have h : a + b = d := FusionRules.eq_of_fin_ofAddMonoid i₁
    have h' : b + a = d := by rwa [add_comm]
    rw [FusionRules.fin_ofAddMonoid_eq h i₁, FusionRules.fin_ofAddMonoid_eq h i₂,
      Matrix.mul_apply, Matrix.one_apply_eq, FusionRules.sum_fin_ofAddMonoid_of_eq h']
    simp only [Matrix.of_apply, Units.mul_inv]
  Rinv_mul_R a b d := by
    ext j₁ j₂
    have h' : b + a = d := FusionRules.eq_of_fin_ofAddMonoid j₁
    have h : a + b = d := by rwa [add_comm]
    rw [FusionRules.fin_ofAddMonoid_eq h' j₁, FusionRules.fin_ofAddMonoid_eq h' j₂,
      Matrix.mul_apply, Matrix.one_apply_eq, FusionRules.sum_fin_ofAddMonoid_of_eq h]
    simp only [Matrix.of_apply, Units.inv_mul]
  hexagon_forward a b c' d e g i j n _ := by
    obtain rfl : a + b = e := FusionRules.eq_of_fin_ofAddMonoid i
    obtain rfl : a + b + c' = d := FusionRules.eq_of_fin_ofAddMonoid j
    obtain rfl : c' + a = g := FusionRules.eq_of_fin_ofAddMonoid n
    have ha : a + (b + c') = a + b + c' := (add_assoc a b c').symm
    have hba : (b + c') + a = a + b + c' := by abel
    have hba' : b + a = a + b := add_comm b a
    have hac : a + c' = c' + a := add_comm a c'
    rw [FusionRules.sum_ofAddMonoid_fst b c', FusionRules.sum_fin_ofAddMonoid_of_eq ha,
      FusionRules.sum_fin_ofAddMonoid_of_eq hba, FusionRules.sum_fin_ofAddMonoid_of_eq hba',
      FusionRules.sum_fin_ofAddMonoid_of_eq hac]
    simpa [Matrix.of_apply, Units.val_mul, mul_assoc] using
      congrArg Units.val (B.hexagon_forward a b c')
  hexagon_reverse a b c' d f g k l n _ := by
    obtain rfl : b + c' = f := FusionRules.eq_of_fin_ofAddMonoid k
    obtain rfl : a + (b + c') = d := FusionRules.eq_of_fin_ofAddMonoid l
    obtain rfl : c' + a = g := FusionRules.eq_of_fin_ofAddMonoid n
    have habc : a + b + c' = a + (b + c') := add_assoc a b c'
    have hcab : c' + (a + b) = a + (b + c') := by abel
    have hcb : c' + b = b + c' := add_comm c' b
    have hac : a + c' = c' + a := add_comm a c'
    rw [FusionRules.sum_ofAddMonoid_fst a b, FusionRules.sum_fin_ofAddMonoid_of_eq habc,
      FusionRules.sum_fin_ofAddMonoid_of_eq hcab, FusionRules.sum_fin_ofAddMonoid_of_eq hcb,
      FusionRules.sum_fin_ofAddMonoid_of_eq hac]
    simpa [Matrix.of_apply, Units.val_mul, mul_assoc] using
      congrArg Units.val (B.hexagon_reverse a b c')

@[simp]
theorem ofPointedBraiding_R_apply (B : PointedBraiding c) (a b d : I)
    (i : Fin ((FusionRules.ofAddMonoid I).N a b d))
    (j : Fin ((FusionRules.ofAddMonoid I).N b a d)) :
    (ofPointedBraiding B).R a b d i j = (B.r a b : K) :=
  Matrix.of_apply _ _ _

@[simp]
theorem ofPointedBraiding_Rinv_apply (B : PointedBraiding c) (a b d : I)
    (j : Fin ((FusionRules.ofAddMonoid I).N b a d))
    (i : Fin ((FusionRules.ofAddMonoid I).N a b d)) :
    (ofPointedBraiding B).Rinv a b d j i = (((B.r a b)⁻¹ : Kˣ) : K) :=
  Matrix.of_apply _ _ _

/-- Extract a `PointedBraiding c` from `RSymbols (FSymbols.ofTwistingCocycle c)`. -/
def toPointedBraiding (Q : RSymbols (FSymbols.ofTwistingCocycle c)) : PointedBraiding c where
  r a b :=
    { val := Q.R a b (a + b) (FusionRules.ofAddMonoidIdx rfl)
        (FusionRules.ofAddMonoidIdx (add_comm b a))
      inv := Q.Rinv a b (a + b) (FusionRules.ofAddMonoidIdx (add_comm b a))
        (FusionRules.ofAddMonoidIdx rfl)
      val_inv := by
        have h := Q.sum_R_mul_Rinv a b (a + b)
          (FusionRules.ofAddMonoidIdx rfl) (FusionRules.ofAddMonoidIdx rfl)
        rw [FusionRules.sum_fin_ofAddMonoid_of_eq (add_comm b a)] at h
        simpa using h
      inv_val := by
        have h := Q.sum_Rinv_mul_R a b (a + b)
          (FusionRules.ofAddMonoidIdx (add_comm b a)) (FusionRules.ofAddMonoidIdx (add_comm b a))
        rw [FusionRules.sum_fin_ofAddMonoid_of_eq rfl] at h
        simpa using h }
  hexagon_forward a b c' := by
    have ha : a + (b + c') = a + b + c' := (add_assoc a b c').symm
    have hba : (b + c') + a = a + b + c' := by abel
    have hbg : b + (c' + a) = a + b + c' := by abel
    have hba' : b + a = a + b := add_comm b a
    have hac : a + c' = c' + a := add_comm a c'
    have hhex := Q.hexagon_forward a b c' (a + b + c') (a + b) (c' + a)
      (FusionRules.ofAddMonoidIdx rfl) (FusionRules.ofAddMonoidIdx rfl)
      (FusionRules.ofAddMonoidIdx rfl) (FusionRules.ofAddMonoidIdx hbg)
    rw [FusionRules.sum_ofAddMonoid_fst b c', FusionRules.sum_fin_ofAddMonoid_of_eq ha,
      FusionRules.sum_fin_ofAddMonoid_of_eq hba, FusionRules.sum_fin_ofAddMonoid_of_eq hba',
      FusionRules.sum_fin_ofAddMonoid_of_eq hac] at hhex
    have eqR (x y d : I) (hx : x + y = d) (i : Fin ((FusionRules.ofAddMonoid I).N x y d))
        (j : Fin ((FusionRules.ofAddMonoid I).N y x d)) :
        Q.R x y d i j =
          Q.R x y (x + y) (FusionRules.ofAddMonoidIdx rfl)
            (FusionRules.ofAddMonoidIdx (add_comm y x)) := by
      subst hx
      rw [FusionRules.fin_ofAddMonoid_eq rfl i, FusionRules.fin_ofAddMonoid_eq (add_comm y x) j]
    rw [eqR a (b + c') _ ha, eqR a b _ rfl, eqR a c' _ hac] at hhex
    ext
    simpa [Units.val_mul, mul_assoc] using hhex
  hexagon_reverse a b c' := by
    have habc : a + b + c' = a + (b + c') := add_assoc a b c'
    have hcab : c' + (a + b) = a + (b + c') := by abel
    have hgb : (c' + a) + b = a + (b + c') := by abel
    have hcb : c' + b = b + c' := add_comm c' b
    have hac : a + c' = c' + a := add_comm a c'
    have hhex := Q.hexagon_reverse a b c' (a + (b + c')) (b + c') (c' + a)
      (FusionRules.ofAddMonoidIdx rfl) (FusionRules.ofAddMonoidIdx rfl)
      (FusionRules.ofAddMonoidIdx rfl) (FusionRules.ofAddMonoidIdx hgb)
    rw [FusionRules.sum_ofAddMonoid_fst a b, FusionRules.sum_fin_ofAddMonoid_of_eq habc,
      FusionRules.sum_fin_ofAddMonoid_of_eq hcab, FusionRules.sum_fin_ofAddMonoid_of_eq hcb,
      FusionRules.sum_fin_ofAddMonoid_of_eq hac] at hhex
    have eqR (x y d : I) (hx : x + y = d) (i : Fin ((FusionRules.ofAddMonoid I).N x y d))
        (j : Fin ((FusionRules.ofAddMonoid I).N y x d)) :
        Q.R x y d i j =
          Q.R x y (x + y) (FusionRules.ofAddMonoidIdx rfl)
            (FusionRules.ofAddMonoidIdx (add_comm y x)) := by
      subst hx
      rw [FusionRules.fin_ofAddMonoid_eq rfl i, FusionRules.fin_ofAddMonoid_eq (add_comm y x) j]
    rw [eqR (a + b) c' _ habc, eqR b c' _ rfl, eqR a c' _ hac] at hhex
    ext
    simpa [Units.val_mul, mul_assoc] using hhex

@[simp]
theorem val_toPointedBraiding_r (Q : RSymbols (FSymbols.ofTwistingCocycle c)) (a b : I) :
    (Q.toPointedBraiding.r a b : K) =
      Q.R a b (a + b) (FusionRules.ofAddMonoidIdx rfl)
        (FusionRules.ofAddMonoidIdx (add_comm b a)) :=
  (rfl)

@[simp]
theorem val_inv_toPointedBraiding_r (Q : RSymbols (FSymbols.ofTwistingCocycle c)) (a b : I) :
    (((Q.toPointedBraiding.r a b)⁻¹ : Kˣ) : K) =
      Q.Rinv a b (a + b) (FusionRules.ofAddMonoidIdx (add_comm b a))
        (FusionRules.ofAddMonoidIdx rfl) :=
  (Units.inv_eq_val_inv (Q.toPointedBraiding.r a b)).symm

/-- Equivalence between `RSymbols (FSymbols.ofTwistingCocycle c)` and `PointedBraiding c`. -/
def pointedBraidingEquiv (c : GradedObject.TwistingCocycle I K) :
    RSymbols (FSymbols.ofTwistingCocycle c) ≃ PointedBraiding c where
  toFun := toPointedBraiding
  invFun := ofPointedBraiding
  left_inv Q := by
    ext a b d i j
    have h : a + b = d := FusionRules.eq_of_fin_ofAddMonoid i
    subst h
    rw [ofPointedBraiding_R_apply, val_toPointedBraiding_r,
      FusionRules.fin_ofAddMonoid_eq rfl i, FusionRules.fin_ofAddMonoid_eq (add_comm b a) j]
  right_inv B := by
    ext a b
    rfl

@[simp]
theorem pointedBraidingEquiv_apply (c : GradedObject.TwistingCocycle I K)
    (Q : RSymbols (FSymbols.ofTwistingCocycle c)) :
    pointedBraidingEquiv c Q = Q.toPointedBraiding :=
  (rfl)

@[simp]
theorem pointedBraidingEquiv_symm_apply (c : GradedObject.TwistingCocycle I K)
    (B : PointedBraiding c) :
    (pointedBraidingEquiv c).symm B = ofPointedBraiding B :=
  (rfl)

end Pointed

end RSymbols

/-! ### Complete classification of F-symbols and R-symbols on `ZMod 2` -/

namespace FSymbols

section ZMod2

variable {R : Type v} [CommRing R]

/-- The normalized `3`-cocycle on `ZMod 2` with `ω 1 1 1 = u` (for `u * u = 1`) and `1`
elsewhere. Note `u⁻¹ = u` since `u * u = 1`. -/
def zmod2TwistingCocycle (u : Rˣ) (hu : u * u = 1) :
    GradedObject.TwistingCocycle (ZMod 2) R where
  ω a b c := if a = 1 ∧ b = 1 ∧ c = 1 then u else 1
  cocycle i₁ i₂ i₃ i₄ := by
    have h01 : ∀ x : ZMod 2, x = 0 ∨ x = 1 := by decide
    have h11 : (1 : ZMod 2) + 1 = 0 := by decide
    rcases h01 i₁ with rfl | rfl <;>
      rcases h01 i₂ with rfl | rfl <;>
      rcases h01 i₃ with rfl | rfl <;>
      rcases h01 i₄ with rfl | rfl <;>
      simp [h11, hu]
  ω_zero i₁ i₃ := by simp

/-- The pointed F-symbols on `ZMod 2` with `F^{111}_1 = u` (for `u * u = 1`) and `1` on all other
nonempty blocks. -/
def zmod2 (u : Rˣ) (hu : u * u = 1) : FSymbols R (FusionRules.ofAddMonoid (ZMod 2)) :=
  ofTwistingCocycle (zmod2TwistingCocycle u hu)

@[simp]
theorem zmod2_F_one_one_one (u : Rˣ) (hu : u * u = 1)
    (x : (FusionRules.ofAddMonoid (ZMod 2)).Left 1 1 1 1)
    (y : (FusionRules.ofAddMonoid (ZMod 2)).Right 1 1 1 1) :
    (zmod2 u hu).F 1 1 1 1 x y = (u : R) := by
  have hinv : u⁻¹ = u := inv_eq_of_mul_eq_one_right hu
  simp [zmod2, zmod2TwistingCocycle, hinv]

/-- F-symbols on `FusionRules.ofAddMonoid (ZMod 2)` are in bijection with `{ u : Rˣ // u * u = 1 }`
via the `(1, 1, 1)` entry `F^{111}_1 = u`. -/
def zmod2Equiv : FSymbols R (FusionRules.ofAddMonoid (ZMod 2)) ≃ { u : Rˣ // u * u = 1 } :=
  twistingCocycleEquiv.trans
    { toFun := fun c ↦
        ⟨(c.ω 1 1 1)⁻¹, by
          have h11 : (1 : ZMod 2) + 1 = 0 := by decide
          have hc := c.cocycle 1 1 1 1
          rw [h11] at hc
          simp only [GradedObject.TwistingCocycle.ω_zero_left,
            GradedObject.TwistingCocycle.ω_zero_right, GradedObject.TwistingCocycle.ω_zero,
            mul_one] at hc
          rw [← mul_inv, ← hc, inv_one]⟩
      invFun := fun u ↦ zmod2TwistingCocycle u.1 u.2
      left_inv := fun c ↦ by
        have h01 : ∀ x : ZMod 2, x = 0 ∨ x = 1 := by decide
        have h11 : (1 : ZMod 2) + 1 = 0 := by decide
        have hsq : c.ω 1 1 1 * c.ω 1 1 1 = 1 := by
          have hc := c.cocycle 1 1 1 1
          rw [h11] at hc
          simpa using hc.symm
        have hinv : (c.ω 1 1 1)⁻¹ = c.ω 1 1 1 := inv_eq_of_mul_eq_one_right hsq
        ext a b c'
        rcases h01 a with rfl | rfl <;>
          rcases h01 b with rfl | rfl <;>
          rcases h01 c' with rfl | rfl <;>
          simp [zmod2TwistingCocycle, hinv]
      right_inv := fun ⟨u, hu⟩ ↦ by
        ext1
        have hinv : u⁻¹ = u := inv_eq_of_mul_eq_one_right hu
        simp [zmod2TwistingCocycle, hinv] }

@[simp]
theorem val_zmod2Equiv_apply (P : FSymbols R (FusionRules.ofAddMonoid (ZMod 2))) :
    (((zmod2Equiv P).1 : Rˣ) : R) =
      P.F 1 1 1 (1 + 1 + 1) (FusionRules.ofAddMonoidLeft rfl)
        (FusionRules.ofAddMonoidRight rfl) := by
  simp [zmod2Equiv]

@[simp]
theorem zmod2Equiv_symm_apply (u : { u : Rˣ // u * u = 1 }) :
    zmod2Equiv.symm u = zmod2 u.1 u.2 := by
  simp [zmod2Equiv, zmod2]

end ZMod2

end FSymbols

namespace RSymbols

section ZMod2

variable {K : Type v} [CommRing K]

/-- Pointed braiding on `FSymbols.zmod2TwistingCocycle u hu` with `r 1 1 = r` (where `r * r = u`)
and `1` elsewhere. -/
def zmod2PointedBraiding {u : Kˣ} (hu : u * u = 1) (r : Kˣ) (hr : r * r = u) :
    PointedBraiding (FSymbols.zmod2TwistingCocycle u hu) where
  r a b := if a = 1 ∧ b = 1 then r else 1
  hexagon_forward a b c' := by
    have h01 : ∀ x : ZMod 2, x = 0 ∨ x = 1 := by decide
    have h11 : (1 : ZMod 2) + 1 = 0 := by decide
    have hinv : u⁻¹ = u := inv_eq_of_mul_eq_one_right hu
    have hru : r * u * r = 1 := by rw [mul_right_comm, hr, hu]
    rcases h01 a with rfl | rfl <;>
      rcases h01 b with rfl | rfl <;>
      rcases h01 c' with rfl | rfl <;>
      simp [FSymbols.zmod2TwistingCocycle, h11, hinv, hu, hru]
  hexagon_reverse a b c' := by
    have h01 : ∀ x : ZMod 2, x = 0 ∨ x = 1 := by decide
    have h11 : (1 : ZMod 2) + 1 = 0 := by decide
    have hru : r * u * r = 1 := by rw [mul_right_comm, hr, hu]
    rcases h01 a with rfl | rfl <;>
      rcases h01 b with rfl | rfl <;>
      rcases h01 c' with rfl | rfl <;>
      simp [FSymbols.zmod2TwistingCocycle, h11, hu, hru]

/-- Construct R-symbols on `FSymbols.zmod2 u hu` from a square root `r : Kˣ` of `u`
(`r * r = u`), giving `R^{11}_0 = r` and `1` on all unit blocks. -/
def zmod2 {u : Kˣ} (hu : u * u = 1) (r : Kˣ) (hr : r * r = u) :
    RSymbols (FSymbols.zmod2 u hu) :=
  ofPointedBraiding (zmod2PointedBraiding hu r hr)

@[simp]
theorem zmod2_R_one_one {u : Kˣ} (hu : u * u = 1) (r : Kˣ) (hr : r * r = u)
    (i j : Fin ((FusionRules.ofAddMonoid (ZMod 2)).N 1 1 0)) :
    (zmod2 hu r hr).R 1 1 0 i j = (r : K) := by
  simp [zmod2, zmod2PointedBraiding]

/-- R-symbols on `FSymbols.zmod2 u hu` are in bijection with `{ r : Kˣ // r * r = u }` via the
nontrivial braiding entry `R^{11}_0 = r`, witnessing `(R^{11}_0)^2 = F^{111}_1`. -/
def zmod2Equiv (u : Kˣ) (hu : u * u = 1) :
    RSymbols (FSymbols.zmod2 u hu) ≃ { r : Kˣ // r * r = u } :=
  (pointedBraidingEquiv (FSymbols.zmod2TwistingCocycle u hu)).trans
    { toFun := fun B ↦
        ⟨B.r 1 1, by
          have h11 : (1 : ZMod 2) + 1 = 0 := by decide
          have hinv : u⁻¹ = u := inv_eq_of_mul_eq_one_right hu
          have hhex := B.hexagon_forward 1 1 1
          rw [h11, PointedBraiding.r_zero_right] at hhex
          simp only [FSymbols.zmod2TwistingCocycle, and_self, ↓reduceIte, hinv, mul_one] at hhex
          calc B.r 1 1 * B.r 1 1
            _ = B.r 1 1 * B.r 1 1 * (u * u) := by rw [hu, mul_one]
            _ = (B.r 1 1 * u * B.r 1 1) * u := by simp [mul_comm, mul_left_comm, mul_assoc]
            _ = (u * u) * u := by rw [← hhex]
            _ = u := by rw [hu, one_mul]⟩
      invFun := fun r ↦ zmod2PointedBraiding hu r.1 r.2
      left_inv := fun B ↦ by
        have h01 : ∀ x : ZMod 2, x = 0 ∨ x = 1 := by decide
        ext a b
        rcases h01 a with rfl | rfl <;>
          rcases h01 b with rfl | rfl <;>
          simp [zmod2PointedBraiding]
      right_inv := fun ⟨r, hr⟩ ↦ by
        ext1
        simp [zmod2PointedBraiding] }

@[simp]
theorem val_zmod2Equiv_apply (u : Kˣ) (hu : u * u = 1) (Q : RSymbols (FSymbols.zmod2 u hu)) :
    (((zmod2Equiv u hu Q).1 : Kˣ) : K) =
      Q.R 1 1 (1 + 1) (FusionRules.ofAddMonoidIdx rfl)
        (FusionRules.ofAddMonoidIdx (add_comm 1 1)) := by
  revert Q
  unfold zmod2Equiv FSymbols.zmod2
  intro Q
  simp

@[simp]
theorem zmod2Equiv_symm_apply (u : Kˣ) (hu : u * u = 1) (r : { r : Kˣ // r * r = u }) :
    (zmod2Equiv u hu).symm r = zmod2 hu r.1 r.2 := by
  change ((pointedBraidingEquiv (FSymbols.zmod2TwistingCocycle u hu)).trans _).symm r =
    ofPointedBraiding (zmod2PointedBraiding hu r.1 r.2)
  simp

/-- For the trivial `ZMod 2` F-symbols (`u = 1`), `r = -1` gives the super-vector-space braiding
`R^{11}_0 = -1`. -/
def zmod2Super : RSymbols (FSymbols.zmod2 (1 : Kˣ) (mul_one 1)) :=
  zmod2 (mul_one 1) (-1) (by simp)

@[simp]
theorem zmod2Super_R_one_one (i j : Fin ((FusionRules.ofAddMonoid (ZMod 2)).N 1 1 0)) :
    (zmod2Super : RSymbols (FSymbols.zmod2 (1 : Kˣ) (mul_one 1))).R 1 1 0 i j = -1 := by
  simp [zmod2Super]

/-- Over `ℤ`, the nontrivial `ZMod 2` F-symbols with `F^{111}_1 = -1` admit no R-symbols, since
`-1` is not a square in `ℤˣ`. -/
instance instIsEmptyZMod2NegOneInt :
    IsEmpty (RSymbols (FSymbols.zmod2 (-1 : ℤˣ) (by decide))) :=
  ⟨fun Q ↦ by
    obtain ⟨r, hr⟩ := zmod2Equiv (-1 : ℤˣ) (by decide) Q
    rcases Int.units_eq_one_or r with rfl | rfl <;> revert hr <;> decide⟩

end ZMod2

end RSymbols

end TauCeti
