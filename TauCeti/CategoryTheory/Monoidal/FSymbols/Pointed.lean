/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Group.Equiv.TypeTags
public import Mathlib.Algebra.Group.TypeTags.Finite
public import Mathlib.Data.ZMod.Basic
public import TauCeti.CategoryTheory.GradedObject.Twisted.Braided
public import TauCeti.CategoryTheory.Monoidal.FSymbols.Transport

/-!
# Monoid-based and pointed fusion rules, `3`-cocycles, and `ℤ/2` classification

In tensor category theory, fusion rules are **pointed** when the simple objects form a group `G`
under tensor product (`N_{ab}^c = [a * b = c]`, every simple invertible; EGNO, §2.3, Ex. 2.3.8).
More generally, `TauCeti.FusionRules.ofMul M` defines monoid-type fusion rules on any
`[MulOneClass M]`. When `M` is a finite `Monoid`, every composite basis space `Left a b c d` and
`Right a b c d` of `FusionRules.ofMul M` has cardinality `1` if `a * b * c = d` and `0` otherwise,
so the F- and R-symbol matrix equations over any commutative semiring `R` collapse to scalar
equations:

* `TauCeti.FusionRules.ofMulIdx`, `TauCeti.FusionRules.ofMulLeft`, and
  `TauCeti.FusionRules.ofMulRight`: canonical channel and composite-basis index witnesses on
  `FusionRules.ofMul M`.
* `TauCeti.FSymbols.twistingCocycleEquiv`: equivalence
  `FSymbols R (FusionRules.ofMul M) ≃ TauCeti.GradedObject.TwistingCocycle (Additive M) R` over any
  commutative semiring `R` (Quinn, §5), with `F^{abc}_{abc} = (ω a b c)⁻¹` and
  `ofTwistingCocycle 1 = ofMul R M`.
* `TauCeti.RSymbols.pointedBraidingEquiv`: equivalence between `RSymbols (ofTwistingCocycle c)` and
  scalar braiding data `TauCeti.GradedObject.PointedBraiding c` over `[CommMonoid M]` and
  `[CommSemiring K]` (abelian `3`-cocycles when `M` is an abelian group; Joyal–Street, §3).
* `TauCeti.FSymbols.zmod2Equiv` and `TauCeti.RSymbols.zmod2Equiv`: complete classification on the
  pointed group `Multiplicative (ZMod 2)` via `{ u : Rˣ // u * u = 1 }` (`F^{111}_1 = u`) and
  `{ r : Kˣ // r * r = u }` (`R^{11}_0 = r`), together with the solvability criteria
  `RSymbols.nonempty_zmod2_iff` and `RSymbols.isEmpty_zmod2_iff`, the super-vector-space braiding
  `RSymbols.zmod2Super` (`u = 1`, `r = -1`), and `RSymbols.instIsEmptyZMod2NegOneInt`.

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

/-! ### Canonical channel and composite-basis witnesses for `FusionRules.ofMul` -/

namespace FusionRules

section MulOneClass

variable {M : Type u} [MulOneClass M] [DecidableEq M]

/-- The canonical basis index in `Fin ((ofMul M).N a b c)` when `a * b = c`. -/
def ofMulIdx {a b c : M} (h : a * b = c) : Fin ((ofMul M).N a b c) := ⟨0, by simp [h]⟩

@[simp]
theorem val_ofMulIdx {a b c : M} (h : a * b = c) : (ofMulIdx h : ℕ) = 0 := (rfl)

end MulOneClass

section Monoid

variable {M : Type u} [Monoid M] [DecidableEq M]

theorem mul_eq_of_left_ofMul {a b c d : M} (x : (ofMul M).Left a b c d) : a * b * c = d := by
  rw [mul_eq_of_ofMul x.snd.fst, mul_eq_of_ofMul x.snd.snd]

theorem mul_eq_of_right_ofMul {a b c d : M} (y : (ofMul M).Right a b c d) : a * b * c = d := by
  rw [mul_assoc, mul_eq_of_ofMul y.snd.fst, mul_eq_of_ofMul y.snd.snd]

/-- The unique element of `(ofMul M).Left a b c d` when `a * b * c = d`. -/
def ofMulLeft {a b c d : M} (h : a * b * c = d) : (ofMul M).Left a b c d :=
  ⟨a * b, ofMulIdx rfl, ofMulIdx h⟩

@[simp]
theorem ofMulLeft_fst {a b c d : M} (h : a * b * c = d) : (ofMulLeft h).fst = a * b := (rfl)

/-- The unique element of `(ofMul M).Right a b c d` when `a * b * c = d`. -/
def ofMulRight {a b c d : M} (h : a * b * c = d) : (ofMul M).Right a b c d :=
  ⟨b * c, ofMulIdx rfl, ofMulIdx (by rwa [← mul_assoc])⟩

@[simp]
theorem ofMulRight_fst {a b c d : M} (h : a * b * c = d) : (ofMulRight h).fst = b * c := (rfl)

end Monoid

end FusionRules

/-! ### Equivalence between monoid-indexed F-symbols and normalized `3`-cocycles -/

namespace FSymbols

section Pointed

open FusionRules (ofMulIdx ofMulLeft ofMulRight mul_eq_of_ofMul
  mul_eq_of_left_ofMul mul_eq_of_right_ofMul sum_sum_ofMul)
open GradedObject (TwistingCocycle)

variable {R : Type v} [CommSemiring R] {M : Type u} [Fintype M] [DecidableEq M] [Monoid M]

private theorem ofMul_pentagon_sides
    (F : ∀ a b c' d : M,
      Matrix ((FusionRules.ofMul M).Left a b c' d) ((FusionRules.ofMul M).Right a b c' d) R)
    (φ : M → M → M → R) (hF : ∀ a b c' d x y, F a b c' d x y = φ a b c') {A B C D E p q r s : M}
    (i₁ : Fin ((FusionRules.ofMul M).N A B p)) (i₂ : Fin ((FusionRules.ofMul M).N p C q))
    (i₃ : Fin ((FusionRules.ofMul M).N q D E)) (k : Fin ((FusionRules.ofMul M).N C D r))
    (m : Fin ((FusionRules.ofMul M).N B r s)) (n : Fin ((FusionRules.ofMul M).N A s E)) :
    (∑ l : Fin ((FusionRules.ofMul M).N p r E),
        F p C D E ⟨q, i₂, i₃⟩ ⟨r, k, l⟩ * F A B r E ⟨p, i₁, l⟩ ⟨s, m, n⟩ =
      φ (A * B) C D * φ A B (C * D)) ∧
    (∑ t : M, ∑ j : Fin ((FusionRules.ofMul M).N B C t),
        ∑ j' : Fin ((FusionRules.ofMul M).N A t q),
        ∑ m' : Fin ((FusionRules.ofMul M).N t D s),
        F A B C q ⟨p, i₁, i₂⟩ ⟨t, j, j'⟩ * F A t D E ⟨q, j', i₃⟩ ⟨s, m', n⟩ *
          F B C D s ⟨t, j, m'⟩ ⟨r, k, m⟩ =
      φ A B C * φ A (B * C) D * φ B C D) := by
  obtain rfl := mul_eq_of_ofMul i₁; obtain rfl := mul_eq_of_ofMul i₂
  obtain rfl := mul_eq_of_ofMul i₃; obtain rfl := mul_eq_of_ofMul k
  obtain rfl := mul_eq_of_ofMul m
  refine ⟨by rw [Fintype.sum_subsingleton _ (ofMulIdx (mul_assoc (A * B) C D).symm), hF, hF], ?_⟩
  rw [sum_sum_ofMul, Fintype.sum_subsingleton _ (ofMulIdx rfl),
    Fintype.sum_subsingleton _ (ofMulIdx (mul_assoc A B C).symm),
    Fintype.sum_subsingleton _ (ofMulIdx (mul_assoc B C D)), hF, hF, hF]

/-- The F-symbols on `FusionRules.ofMul M` attached to a normalized `3`-cocycle
`c : TwistingCocycle (Additive M) R`, with `F^{abc}_{abc} = (c.ω a b c)⁻¹` and
`Finv^{abc}_{abc} = c.ω a b c`. -/
def ofTwistingCocycle (c : TwistingCocycle (Additive M) R) :
    FSymbols R (FusionRules.ofMul M) where
  F a b c' _ := Matrix.of fun _ _ ↦ (((c.ω (.ofMul a) (.ofMul b) (.ofMul c'))⁻¹ : Rˣ) : R)
  Finv a b c' _ := Matrix.of fun _ _ ↦ (c.ω (.ofMul a) (.ofMul b) (.ofMul c') : R)
  F_mul_Finv a b c' d := by
    ext x₁ x₂
    have h := mul_eq_of_left_ofMul x₁
    rw [Subsingleton.elim x₁ x₂, Matrix.mul_apply, Matrix.one_apply_eq,
      Fintype.sum_subsingleton _ (ofMulRight h)]
    simp only [Matrix.of_apply, Units.inv_mul]
  Finv_mul_F a b c' d := by
    ext y₁ y₂
    have h := mul_eq_of_right_ofMul y₁
    rw [Subsingleton.elim y₁ y₂, Matrix.mul_apply, Matrix.one_apply_eq,
      Fintype.sum_subsingleton _ (ofMulLeft h)]
    simp only [Matrix.of_apply, Units.mul_inv]
  pentagon A B C D _ _ _ _ _ i₁ i₂ i₃ k m n := by
    obtain ⟨hL, hR⟩ := ofMul_pentagon_sides
      (fun a b c' _ ↦ Matrix.of fun _ _ ↦ (((c.ω (.ofMul a) (.ofMul b) (.ofMul c'))⁻¹ : Rˣ) : R))
      (fun a b c' ↦ (((c.ω (.ofMul a) (.ofMul b) (.ofMul c'))⁻¹ : Rˣ) : R))
      (fun _ _ _ _ _ _ ↦ rfl) i₁ i₂ i₃ k m n
    refine (hL.trans ?_).trans hR.symm
    rw [mul_comm]
    simpa only [← ofMul_mul, mul_inv_rev, Units.val_mul, mul_assoc] using
      congrArg (fun u : Rˣ ↦ ((u⁻¹ : Rˣ) : R))
        (c.cocycle (.ofMul A) (.ofMul B) (.ofMul C) (.ofMul D))
  triangle _ _ _ j l := by simp [Subsingleton.elim j l]

@[simp]
theorem ofTwistingCocycle_F_apply (c : TwistingCocycle (Additive M) R) (a b c' d : M)
    (x : (FusionRules.ofMul M).Left a b c' d) (y : (FusionRules.ofMul M).Right a b c' d) :
    (ofTwistingCocycle c).F a b c' d x y =
      (((c.ω (.ofMul a) (.ofMul b) (.ofMul c'))⁻¹ : Rˣ) : R) :=
  Matrix.of_apply _ _ _

@[simp]
theorem ofTwistingCocycle_Finv_apply (c : TwistingCocycle (Additive M) R) (a b c' d : M)
    (y : (FusionRules.ofMul M).Right a b c' d) (x : (FusionRules.ofMul M).Left a b c' d) :
    (ofTwistingCocycle c).Finv a b c' d y x =
      (c.ω (.ofMul a) (.ofMul b) (.ofMul c') : R) :=
  Matrix.of_apply _ _ _

@[simp]
theorem ofTwistingCocycle_one :
    ofTwistingCocycle (1 : TwistingCocycle (Additive M) R) = ofMul R M := by
  ext
  simp

private theorem pointed_F_eq_canonical (P : FSymbols R (FusionRules.ofMul M)) (a b c' d : M)
    (x : (FusionRules.ofMul M).Left a b c' d) (y : (FusionRules.ofMul M).Right a b c' d) :
    P.F a b c' d x y = P.F a b c' (a * b * c') (ofMulLeft rfl) (ofMulRight rfl) := by
  obtain rfl := mul_eq_of_left_ofMul x
  rw [Subsingleton.elim x (ofMulLeft rfl), Subsingleton.elim y (ofMulRight rfl)]

/-- Extract the normalized `3`-cocycle `ω a b c = Finv^{abc}_{abc}` from F-symbols on
`FusionRules.ofMul M` (in particular, from pointed F-symbols when `M` is a `Group`). -/
def toTwistingCocycle (P : FSymbols R (FusionRules.ofMul M)) : TwistingCocycle (Additive M) R where
  ω a b c' :=
    { val := P.Finv a.toMul b.toMul c'.toMul (a.toMul * b.toMul * c'.toMul)
        (ofMulRight rfl) (ofMulLeft rfl)
      inv := P.F a.toMul b.toMul c'.toMul (a.toMul * b.toMul * c'.toMul)
        (ofMulLeft rfl) (ofMulRight rfl)
      val_inv := by
        have h := P.sum_Finv_mul_F a.toMul b.toMul c'.toMul (a.toMul * b.toMul * c'.toMul)
          (ofMulRight rfl) (ofMulRight rfl)
        rw [Fintype.sum_subsingleton _ (ofMulLeft rfl)] at h
        simpa using h
      inv_val := by
        have h := P.sum_F_mul_Finv a.toMul b.toMul c'.toMul (a.toMul * b.toMul * c'.toMul)
          (ofMulLeft rfl) (ofMulLeft rfl)
        rw [Fintype.sum_subsingleton _ (ofMulRight rfl)] at h
        simpa using h }
  cocycle i₁ i₂ i₃ i₄ := by
    have hBCDE : i₁.toMul * (i₂.toMul * (i₃.toMul * i₄.toMul)) =
        i₁.toMul * i₂.toMul * i₃.toMul * i₄.toMul := by
      simp only [mul_assoc]
    have hp := P.pentagon i₁.toMul i₂.toMul i₃.toMul i₄.toMul
      (i₁.toMul * i₂.toMul * i₃.toMul * i₄.toMul) (i₁.toMul * i₂.toMul)
      (i₁.toMul * i₂.toMul * i₃.toMul) (i₃.toMul * i₄.toMul)
      (i₂.toMul * (i₃.toMul * i₄.toMul)) (ofMulIdx rfl) (ofMulIdx rfl) (ofMulIdx rfl)
      (ofMulIdx rfl) (ofMulIdx rfl) (ofMulIdx hBCDE)
    obtain ⟨hL, hR⟩ := ofMul_pentagon_sides P.F _ P.pointed_F_eq_canonical
      (ofMulIdx (a := i₁.toMul) (b := i₂.toMul) rfl)
      (ofMulIdx (a := i₁.toMul * i₂.toMul) (b := i₃.toMul) rfl)
      (ofMulIdx (a := i₁.toMul * i₂.toMul * i₃.toMul) (b := i₄.toMul) rfl)
      (ofMulIdx (a := i₃.toMul) (b := i₄.toMul) rfl)
      (ofMulIdx (a := i₂.toMul) (b := i₃.toMul * i₄.toMul) rfl) (ofMulIdx hBCDE)
    refine inv_inj.mp (Units.ext ?_)
    simp only [toMul_add, mul_inv_rev, Units.val_mul, Units.inv_mk, ← mul_assoc]
    exact (mul_comm _ _).trans ((hL.symm.trans hp).trans hR)
  ω_zero i₁ i₃ := inv_inj.mp <| Units.ext <| by
    simp only [inv_one, Units.inv_mk, Units.val_one]
    have key : ∀ u, u = (FusionRules.ofMul M).unit →
        P.F i₁.toMul u i₃.toMul (i₁.toMul * u * i₃.toMul) (ofMulLeft rfl) (ofMulRight rfl) = 1 := by
      rintro _ rfl
      let j : Fin ((FusionRules.ofMul M).N i₁.toMul i₃.toMul
        (i₁.toMul * (FusionRules.ofMul M).unit * i₃.toMul)) := ofMulIdx (by simp)
      exact (P.pointed_F_eq_canonical _ _ _ _
        ⟨i₁.toMul, (FusionRules.ofMul M).unitRight i₁.toMul, j⟩
        ⟨i₃.toMul, (FusionRules.ofMul M).unitLeft i₃.toMul, j⟩).symm.trans
          (P.triangle_self _ _ _ j)
    exact key _ (by simp)

@[simp]
theorem val_toTwistingCocycle_ω (P : FSymbols R (FusionRules.ofMul M)) (a b c' : Additive M) :
    (P.toTwistingCocycle.ω a b c' : R) =
      P.Finv a.toMul b.toMul c'.toMul (a.toMul * b.toMul * c'.toMul)
        (ofMulRight rfl) (ofMulLeft rfl) :=
  (rfl)

@[simp]
theorem val_inv_toTwistingCocycle_ω (P : FSymbols R (FusionRules.ofMul M)) (a b c' : Additive M) :
    (((P.toTwistingCocycle.ω a b c')⁻¹ : Rˣ) : R) =
      P.F a.toMul b.toMul c'.toMul (a.toMul * b.toMul * c'.toMul)
        (ofMulLeft rfl) (ofMulRight rfl) :=
  (Units.inv_eq_val_inv (P.toTwistingCocycle.ω a b c')).symm

theorem F_eq_inv_toTwistingCocycle_ω (P : FSymbols R (FusionRules.ofMul M)) (a b c' d : M)
    (x : (FusionRules.ofMul M).Left a b c' d) (y : (FusionRules.ofMul M).Right a b c' d) :
    P.F a b c' d x y =
      (((P.toTwistingCocycle.ω (.ofMul a) (.ofMul b) (.ofMul c'))⁻¹ : Rˣ) : R) := by
  rw [val_inv_toTwistingCocycle_ω, toMul_ofMul, toMul_ofMul, toMul_ofMul, pointed_F_eq_canonical]

theorem Finv_eq_toTwistingCocycle_ω (P : FSymbols R (FusionRules.ofMul M)) (a b c' d : M)
    (y : (FusionRules.ofMul M).Right a b c' d) (x : (FusionRules.ofMul M).Left a b c' d) :
    P.Finv a b c' d y x = (P.toTwistingCocycle.ω (.ofMul a) (.ofMul b) (.ofMul c') : R) := by
  obtain rfl := mul_eq_of_right_ofMul y
  rw [val_toTwistingCocycle_ω, toMul_ofMul, toMul_ofMul, toMul_ofMul,
    Subsingleton.elim y (ofMulRight rfl), Subsingleton.elim x (ofMulLeft rfl)]

@[simp]
theorem toTwistingCocycle_ofTwistingCocycle (c : TwistingCocycle (Additive M) R) :
    (ofTwistingCocycle c).toTwistingCocycle = c := by ext; simp

@[simp]
theorem ofTwistingCocycle_toTwistingCocycle (P : FSymbols R (FusionRules.ofMul M)) :
    ofTwistingCocycle P.toTwistingCocycle = P := by
  ext a b c' d x y
  rw [ofTwistingCocycle_F_apply, F_eq_inv_toTwistingCocycle_ω]

@[simp]
theorem toTwistingCocycle_ofMul : (ofMul R M).toTwistingCocycle = 1 := by
  rw [← ofTwistingCocycle_one, toTwistingCocycle_ofTwistingCocycle]

/-- Equivalence between F-symbols on `FusionRules.ofMul M` and normalized `3`-cocycles
`TauCeti.GradedObject.TwistingCocycle (Additive M) R`, with inverse `FSymbols.ofTwistingCocycle`. -/
def twistingCocycleEquiv : FSymbols R (FusionRules.ofMul M) ≃ TwistingCocycle (Additive M) R where
  toFun := toTwistingCocycle
  invFun := ofTwistingCocycle
  left_inv := ofTwistingCocycle_toTwistingCocycle
  right_inv := toTwistingCocycle_ofTwistingCocycle

@[simp]
theorem twistingCocycleEquiv_apply (P : FSymbols R (FusionRules.ofMul M)) :
    twistingCocycleEquiv P = P.toTwistingCocycle := (rfl)

@[simp]
theorem twistingCocycleEquiv_symm_apply (c : TwistingCocycle (Additive M) R) :
    twistingCocycleEquiv.symm c = ofTwistingCocycle c := (rfl)

/-- Base change commutes with `FSymbols.ofTwistingCocycle`. -/
@[simp]
theorem map_ofTwistingCocycle {S : Type*} [CommSemiring S] (f : R →+* S)
    (c : TwistingCocycle (Additive M) R) :
    (ofTwistingCocycle c).map f = ofTwistingCocycle (c.map (f : R →* S)) := by
  ext a b c' d x y
  rw [map_F, Matrix.map_apply, ofTwistingCocycle_F_apply, ofTwistingCocycle_F_apply,
    TwistingCocycle.map_ω, ← map_inv (Units.map (f : R →* S)), Units.coe_map]
  simp only [MonoidHom.coe_ofClass]

@[simp]
theorem toTwistingCocycle_map {S : Type*} [CommSemiring S] (f : R →+* S)
    (P : FSymbols R (FusionRules.ofMul M)) :
    (P.map f).toTwistingCocycle = P.toTwistingCocycle.map (f : R →* S) := by
  rw [← toTwistingCocycle_ofTwistingCocycle (P.toTwistingCocycle.map (f : R →* S)),
    ← map_ofTwistingCocycle, ofTwistingCocycle_toTwistingCocycle]

/-- Relabeling along a multiplicative isomorphism commutes with `FSymbols.ofTwistingCocycle`. -/
@[simp]
theorem reindex_ofTwistingCocycle {M' : Type u'} [Fintype M'] [DecidableEq M'] [Monoid M']
    (e : M ≃* M') (c : TwistingCocycle (Additive M) R) :
    (ofTwistingCocycle c).reindex (FusionRules.Equiv.ofMulEquiv e) =
      ofTwistingCocycle (TwistingCocycle.domCongr (MulEquiv.toAdditive e) c) := by
  ext
  simp

@[simp]
theorem toTwistingCocycle_reindex {M' : Type u'} [Fintype M'] [DecidableEq M'] [Monoid M']
    (e : M ≃* M') (P : FSymbols R (FusionRules.ofMul M)) :
    (P.reindex (FusionRules.Equiv.ofMulEquiv e)).toTwistingCocycle =
      TwistingCocycle.domCongr (MulEquiv.toAdditive e) P.toTwistingCocycle := by
  rw [← toTwistingCocycle_ofTwistingCocycle
    (TwistingCocycle.domCongr (MulEquiv.toAdditive e) P.toTwistingCocycle),
    ← reindex_ofTwistingCocycle, ofTwistingCocycle_toTwistingCocycle]

end Pointed

end FSymbols

/-! ### Scalar braidings and abelian `3`-cocycles -/

namespace RSymbols

section Pointed

open FusionRules (ofMulIdx mul_eq_of_ofMul sum_sum_ofMul)
open GradedObject (TwistingCocycle PointedBraiding)

variable {K : Type v} [CommSemiring K] {M : Type u} [Fintype M] [DecidableEq M] [CommMonoid M]
  {c : TwistingCocycle (Additive M) K}

private theorem ofMul_hexagon_forward_sides
    (R : ∀ a b d : M,
      Matrix (Fin ((FusionRules.ofMul M).N a b d)) (Fin ((FusionRules.ofMul M).N b a d)) K)
    (ρ : M → M → K) (hR : ∀ a b d i j, R a b d i j = ρ a b) (c : TwistingCocycle (Additive M) K)
    {a b c' d e g : M} (i : Fin ((FusionRules.ofMul M).N a b e))
    (j : Fin ((FusionRules.ofMul M).N e c' d))
    (n : Fin ((FusionRules.ofMul M).N c' a g)) (o : Fin ((FusionRules.ofMul M).N b g d)) :
    (∑ f : M, ∑ k : Fin ((FusionRules.ofMul M).N b c' f),
        ∑ l : Fin ((FusionRules.ofMul M).N a f d),
        ∑ m : Fin ((FusionRules.ofMul M).N f a d),
        (FSymbols.ofTwistingCocycle c).F a b c' d ⟨e, i, j⟩ ⟨f, k, l⟩ * R a f d l m *
          (FSymbols.ofTwistingCocycle c).F b c' a d ⟨f, k, m⟩ ⟨g, n, o⟩ =
      (((c.ω (.ofMul a) (.ofMul b) (.ofMul c'))⁻¹ : Kˣ) : K) * ρ a (b * c') *
        (((c.ω (.ofMul b) (.ofMul c') (.ofMul a))⁻¹ : Kˣ) : K)) ∧
    (∑ p : Fin ((FusionRules.ofMul M).N b a e), ∑ q : Fin ((FusionRules.ofMul M).N a c' g),
        R a b e i p * (FSymbols.ofTwistingCocycle c).F b a c' d ⟨e, p, j⟩ ⟨g, q, o⟩ *
          R a c' g q n =
      ρ a b * (((c.ω (.ofMul b) (.ofMul a) (.ofMul c'))⁻¹ : Kˣ) : K) * ρ a c') := by
  obtain rfl := mul_eq_of_ofMul i; obtain rfl := mul_eq_of_ofMul j
  obtain rfl := mul_eq_of_ofMul n
  refine ⟨?_, by rw [Fintype.sum_subsingleton _ (ofMulIdx (mul_comm b a)),
    Fintype.sum_subsingleton _ (ofMulIdx (mul_comm a c')),
    FSymbols.ofTwistingCocycle_F_apply, hR, hR]⟩
  rw [sum_sum_ofMul, Fintype.sum_subsingleton _ (ofMulIdx rfl),
    Fintype.sum_subsingleton _ (ofMulIdx (mul_assoc a b c').symm),
    Fintype.sum_subsingleton _ (ofMulIdx (by rw [mul_comm (b * c') a, ← mul_assoc])),
    FSymbols.ofTwistingCocycle_F_apply, FSymbols.ofTwistingCocycle_F_apply, hR]

private theorem ofMul_hexagon_reverse_sides
    (R : ∀ a b d : M,
      Matrix (Fin ((FusionRules.ofMul M).N a b d)) (Fin ((FusionRules.ofMul M).N b a d)) K)
    (ρ : M → M → K) (hR : ∀ a b d i j, R a b d i j = ρ a b) (c : TwistingCocycle (Additive M) K)
    {a b c' d f g : M} (k : Fin ((FusionRules.ofMul M).N b c' f))
    (l : Fin ((FusionRules.ofMul M).N a f d))
    (n : Fin ((FusionRules.ofMul M).N c' a g)) (o : Fin ((FusionRules.ofMul M).N g b d)) :
    (∑ e : M, ∑ i : Fin ((FusionRules.ofMul M).N a b e),
        ∑ j : Fin ((FusionRules.ofMul M).N e c' d),
        ∑ m : Fin ((FusionRules.ofMul M).N c' e d),
        (FSymbols.ofTwistingCocycle c).Finv a b c' d ⟨f, k, l⟩ ⟨e, i, j⟩ * R e c' d j m *
          (FSymbols.ofTwistingCocycle c).Finv c' a b d ⟨e, i, m⟩ ⟨g, n, o⟩ =
      (c.ω (.ofMul a) (.ofMul b) (.ofMul c') : K) * ρ (a * b) c' *
        (c.ω (.ofMul c') (.ofMul a) (.ofMul b) : K)) ∧
    (∑ p : Fin ((FusionRules.ofMul M).N c' b f), ∑ q : Fin ((FusionRules.ofMul M).N a c' g),
        R b c' f k p * (FSymbols.ofTwistingCocycle c).Finv a c' b d ⟨f, p, l⟩ ⟨g, q, o⟩ *
          R a c' g q n =
      ρ b c' * (c.ω (.ofMul a) (.ofMul c') (.ofMul b) : K) * ρ a c') := by
  obtain rfl := mul_eq_of_ofMul k; obtain rfl := mul_eq_of_ofMul l
  obtain rfl := mul_eq_of_ofMul n
  refine ⟨?_, by rw [Fintype.sum_subsingleton _ (ofMulIdx (mul_comm c' b)),
    Fintype.sum_subsingleton _ (ofMulIdx (mul_comm a c')),
    FSymbols.ofTwistingCocycle_Finv_apply, hR, hR]⟩
  rw [sum_sum_ofMul, Fintype.sum_subsingleton _ (ofMulIdx rfl),
    Fintype.sum_subsingleton _ (ofMulIdx (mul_assoc a b c')),
    Fintype.sum_subsingleton _
      (ofMulIdx (by simp [mul_comm, mul_left_comm] : c' * (a * b) = a * (b * c'))),
    FSymbols.ofTwistingCocycle_Finv_apply, FSymbols.ofTwistingCocycle_Finv_apply, hR]

/-- Construct `RSymbols` on `FSymbols.ofTwistingCocycle c` from a `PointedBraiding c`. -/
def ofPointedBraiding (B : PointedBraiding c) : RSymbols (FSymbols.ofTwistingCocycle c) where
  R a b _ := Matrix.of fun _ _ ↦ (B.r (.ofMul a) (.ofMul b) : K)
  Rinv a b _ := Matrix.of fun _ _ ↦ (((B.r (.ofMul a) (.ofMul b))⁻¹ : Kˣ) : K)
  R_mul_Rinv a b d := by
    ext i₁ i₂
    have h := mul_eq_of_ofMul i₁
    rw [Subsingleton.elim i₁ i₂, Matrix.mul_apply, Matrix.one_apply_eq,
      Fintype.sum_subsingleton _ (ofMulIdx (mul_comm b a ▸ h))]
    simp only [Matrix.of_apply, Units.mul_inv]
  Rinv_mul_R a b d := by
    ext j₁ j₂
    have h' := mul_eq_of_ofMul j₁
    rw [Subsingleton.elim j₁ j₂, Matrix.mul_apply, Matrix.one_apply_eq,
      Fintype.sum_subsingleton _ (ofMulIdx (mul_comm a b ▸ h'))]
    simp only [Matrix.of_apply, Units.inv_mul]
  hexagon_forward a b c' _ _ _ i j n o := by
    obtain ⟨hL, hR⟩ := ofMul_hexagon_forward_sides
      (fun a b _ ↦ Matrix.of fun _ _ ↦ (B.r (.ofMul a) (.ofMul b) : K))
      (fun a b ↦ (B.r (.ofMul a) (.ofMul b) : K))
      (fun _ _ _ _ _ ↦ rfl) c i j n o
    refine (hL.trans ?_).trans hR.symm
    simpa only [← ofMul_mul, Units.val_mul, mul_assoc] using
      congrArg Units.val (B.hexagon_forward (.ofMul a) (.ofMul b) (.ofMul c'))
  hexagon_reverse a b c' _ _ _ k l n o := by
    obtain ⟨hL, hR⟩ := ofMul_hexagon_reverse_sides
      (fun a b _ ↦ Matrix.of fun _ _ ↦ (B.r (.ofMul a) (.ofMul b) : K))
      (fun a b ↦ (B.r (.ofMul a) (.ofMul b) : K))
      (fun _ _ _ _ _ ↦ rfl) c k l n o
    refine (hL.trans ?_).trans hR.symm
    simpa only [← ofMul_mul, Units.val_mul, mul_assoc] using
      congrArg Units.val (B.hexagon_reverse (.ofMul a) (.ofMul b) (.ofMul c'))

@[simp]
theorem ofPointedBraiding_R_apply (B : PointedBraiding c) (a b d : M)
    (i : Fin ((FusionRules.ofMul M).N a b d)) (j : Fin ((FusionRules.ofMul M).N b a d)) :
    (ofPointedBraiding B).R a b d i j = (B.r (.ofMul a) (.ofMul b) : K) :=
  Matrix.of_apply _ _ _

@[simp]
theorem ofPointedBraiding_Rinv_apply (B : PointedBraiding c) (a b d : M)
    (j : Fin ((FusionRules.ofMul M).N b a d)) (i : Fin ((FusionRules.ofMul M).N a b d)) :
    (ofPointedBraiding B).Rinv a b d j i = (((B.r (.ofMul a) (.ofMul b))⁻¹ : Kˣ) : K) :=
  Matrix.of_apply _ _ _

@[simp]
theorem cast_ofPointedBraiding_one
    (h : FSymbols.ofTwistingCocycle (1 : TwistingCocycle (Additive M) K) = FSymbols.ofMul K M :=
      FSymbols.ofTwistingCocycle_one) :
    (ofPointedBraiding (1 : PointedBraiding (1 : TwistingCocycle (Additive M) K))).cast h =
      ofMul K M := by
  ext
  simp

private theorem pointed_R_eq_canonical (Q : RSymbols (FSymbols.ofTwistingCocycle c)) (x y d : M)
    (i : Fin ((FusionRules.ofMul M).N x y d)) (j : Fin ((FusionRules.ofMul M).N y x d)) :
    Q.R x y d i j = Q.R x y (x * y) (ofMulIdx rfl) (ofMulIdx (mul_comm y x)) := by
  obtain rfl := mul_eq_of_ofMul i
  rw [Subsingleton.elim i (ofMulIdx rfl), Subsingleton.elim j (ofMulIdx (mul_comm y x))]

/-- Extract a `PointedBraiding c` from `RSymbols (FSymbols.ofTwistingCocycle c)`. -/
def toPointedBraiding (Q : RSymbols (FSymbols.ofTwistingCocycle c)) : PointedBraiding c where
  r a b :=
    { val := Q.R a.toMul b.toMul (a.toMul * b.toMul)
        (ofMulIdx rfl) (ofMulIdx (mul_comm b.toMul a.toMul))
      inv := Q.Rinv a.toMul b.toMul (a.toMul * b.toMul)
        (ofMulIdx (mul_comm b.toMul a.toMul)) (ofMulIdx rfl)
      val_inv := by
        have h := Q.sum_R_mul_Rinv a.toMul b.toMul (a.toMul * b.toMul) (ofMulIdx rfl) (ofMulIdx rfl)
        rw [Fintype.sum_subsingleton _ (ofMulIdx (mul_comm b.toMul a.toMul))] at h
        simpa using h
      inv_val := by
        have h := Q.sum_Rinv_mul_R a.toMul b.toMul (a.toMul * b.toMul)
          (ofMulIdx (mul_comm b.toMul a.toMul)) (ofMulIdx (mul_comm b.toMul a.toMul))
        rw [Fintype.sum_subsingleton _ (ofMulIdx rfl)] at h
        simpa using h }
  hexagon_forward a b c' := by
    have ho : b.toMul * (c'.toMul * a.toMul) = a.toMul * b.toMul * c'.toMul := by
      simp [mul_comm, mul_left_comm]
    have hhex := Q.hexagon_forward a.toMul b.toMul c'.toMul (a.toMul * b.toMul * c'.toMul)
      (a.toMul * b.toMul) (c'.toMul * a.toMul) (ofMulIdx rfl)
      (ofMulIdx rfl) (ofMulIdx rfl) (ofMulIdx ho)
    obtain ⟨hL, hR⟩ := ofMul_hexagon_forward_sides Q.R _ Q.pointed_R_eq_canonical c
      (ofMulIdx (a := a.toMul) (b := b.toMul) rfl)
      (ofMulIdx (a := a.toMul * b.toMul) (b := c'.toMul) rfl)
      (ofMulIdx (a := c'.toMul) (b := a.toMul) rfl) (ofMulIdx ho)
    ext
    simpa only [ofMul_toMul, toMul_add, Units.val_mul, mul_assoc] using
      (hL.symm.trans hhex).trans hR
  hexagon_reverse a b c' := by
    have ho : (c'.toMul * a.toMul) * b.toMul = a.toMul * (b.toMul * c'.toMul) := by
      simp [mul_comm, mul_left_comm]
    have hhex := Q.hexagon_reverse a.toMul b.toMul c'.toMul (a.toMul * (b.toMul * c'.toMul))
      (b.toMul * c'.toMul) (c'.toMul * a.toMul) (ofMulIdx rfl)
      (ofMulIdx rfl) (ofMulIdx rfl) (ofMulIdx ho)
    obtain ⟨hL, hR⟩ := ofMul_hexagon_reverse_sides Q.R _ Q.pointed_R_eq_canonical c
      (ofMulIdx (a := b.toMul) (b := c'.toMul) rfl)
      (ofMulIdx (a := a.toMul) (b := b.toMul * c'.toMul) rfl)
      (ofMulIdx (a := c'.toMul) (b := a.toMul) rfl) (ofMulIdx ho)
    ext
    simpa only [ofMul_toMul, toMul_add, Units.val_mul, mul_assoc] using
      (hL.symm.trans hhex).trans hR

@[simp]
theorem val_toPointedBraiding_r (Q : RSymbols (FSymbols.ofTwistingCocycle c))
    (a b : Additive M) :
    (Q.toPointedBraiding.r a b : K) =
      Q.R a.toMul b.toMul (a.toMul * b.toMul)
        (ofMulIdx rfl) (ofMulIdx (mul_comm b.toMul a.toMul)) :=
  (rfl)

@[simp]
theorem val_inv_toPointedBraiding_r (Q : RSymbols (FSymbols.ofTwistingCocycle c))
    (a b : Additive M) :
    (((Q.toPointedBraiding.r a b)⁻¹ : Kˣ) : K) =
      Q.Rinv a.toMul b.toMul (a.toMul * b.toMul)
        (ofMulIdx (mul_comm b.toMul a.toMul)) (ofMulIdx rfl) :=
  (Units.inv_eq_val_inv (Q.toPointedBraiding.r a b)).symm

theorem R_eq_toPointedBraiding_r (Q : RSymbols (FSymbols.ofTwistingCocycle c)) (a b d : M)
    (i : Fin ((FusionRules.ofMul M).N a b d)) (j : Fin ((FusionRules.ofMul M).N b a d)) :
    Q.R a b d i j = (Q.toPointedBraiding.r (.ofMul a) (.ofMul b) : K) := by
  rw [val_toPointedBraiding_r, toMul_ofMul, toMul_ofMul, pointed_R_eq_canonical]

theorem Rinv_eq_inv_toPointedBraiding_r (Q : RSymbols (FSymbols.ofTwistingCocycle c)) (a b d : M)
    (j : Fin ((FusionRules.ofMul M).N b a d)) (i : Fin ((FusionRules.ofMul M).N a b d)) :
    Q.Rinv a b d j i = (((Q.toPointedBraiding.r (.ofMul a) (.ofMul b))⁻¹ : Kˣ) : K) := by
  obtain rfl := mul_eq_of_ofMul i
  rw [val_inv_toPointedBraiding_r, toMul_ofMul, toMul_ofMul,
    Subsingleton.elim j (ofMulIdx (mul_comm b a)), Subsingleton.elim i (ofMulIdx rfl)]

@[simp]
theorem toPointedBraiding_ofPointedBraiding (B : PointedBraiding c) :
    (ofPointedBraiding B).toPointedBraiding = B := by ext; simp

@[simp]
theorem ofPointedBraiding_toPointedBraiding (Q : RSymbols (FSymbols.ofTwistingCocycle c)) :
    ofPointedBraiding Q.toPointedBraiding = Q := by
  ext a b d i j
  rw [ofPointedBraiding_R_apply, R_eq_toPointedBraiding_r]

@[simp]
theorem toPointedBraiding_cast_ofMul
    (h : FSymbols.ofMul K M = FSymbols.ofTwistingCocycle (1 : TwistingCocycle (Additive M) K) :=
      FSymbols.ofTwistingCocycle_one.symm) :
    ((ofMul K M).cast h).toPointedBraiding = 1 := by
  ext
  simp

/-- Equivalence between `RSymbols (FSymbols.ofTwistingCocycle c)` and
`TauCeti.GradedObject.PointedBraiding c`, with inverse `RSymbols.ofPointedBraiding`. -/
def pointedBraidingEquiv (c : TwistingCocycle (Additive M) K) :
    RSymbols (FSymbols.ofTwistingCocycle c) ≃ PointedBraiding c where
  toFun := toPointedBraiding
  invFun := ofPointedBraiding
  left_inv := ofPointedBraiding_toPointedBraiding
  right_inv := toPointedBraiding_ofPointedBraiding

@[simp]
theorem pointedBraidingEquiv_apply (c : TwistingCocycle (Additive M) K)
    (Q : RSymbols (FSymbols.ofTwistingCocycle c)) :
    pointedBraidingEquiv c Q = Q.toPointedBraiding := (rfl)

@[simp]
theorem pointedBraidingEquiv_symm_apply (c : TwistingCocycle (Additive M) K)
    (B : PointedBraiding c) :
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

/-! ### Complete classification of F-symbols and R-symbols on `Multiplicative (ZMod 2)` -/

namespace FSymbols

section ZMod2

open FusionRules (ofMulLeft ofMulRight)
open GradedObject (TwistingCocycle)

variable {R : Type v} [CommSemiring R]

/-- The pointed F-symbols on `Multiplicative (ZMod 2)` with `F^{111}_1 = u` (`u * u = 1`) and `1`
on all other nonempty blocks. -/
def zmod2 (u : Rˣ) (hu : u * u = 1) : FSymbols R (FusionRules.ofMul (Multiplicative (ZMod 2))) :=
  ofTwistingCocycle
    ((TwistingCocycle.zmod2 u hu).comap
      (AddEquiv.additiveMultiplicative (ZMod 2) : Additive (Multiplicative (ZMod 2)) →+ ZMod 2))

theorem zmod2_eq_ofTwistingCocycle (u : Rˣ) (hu : u * u = 1) :
    zmod2 u hu =
      ofTwistingCocycle
        ((TwistingCocycle.zmod2 u hu).comap
          (AddEquiv.additiveMultiplicative (ZMod 2) :
            Additive (Multiplicative (ZMod 2)) →+ ZMod 2)) :=
  (rfl)

@[simp]
theorem zmod2_F_apply (u : Rˣ) (hu : u * u = 1) (a b c d : Multiplicative (ZMod 2))
    (x : (FusionRules.ofMul (Multiplicative (ZMod 2))).Left a b c d)
    (y : (FusionRules.ofMul (Multiplicative (ZMod 2))).Right a b c d) :
    (zmod2 u hu).F a b c d x y =
      if a.toAdd = 1 ∧ b.toAdd = 1 ∧ c.toAdd = 1 then (u : R) else 1 := by
  rw [zmod2_eq_ofTwistingCocycle, ofTwistingCocycle_F_apply]
  simp only [TwistingCocycle.comap_ω, AddMonoidHom.coe_ofClass,
    AddEquiv.additiveMultiplicative_apply, toMul_ofMul, TwistingCocycle.zmod2_ω]
  split_ifs <;> simp [inv_eq_of_mul_eq_one_right hu]

@[simp]
theorem zmod2_Finv_apply (u : Rˣ) (hu : u * u = 1) (a b c d : Multiplicative (ZMod 2))
    (y : (FusionRules.ofMul (Multiplicative (ZMod 2))).Right a b c d)
    (x : (FusionRules.ofMul (Multiplicative (ZMod 2))).Left a b c d) :
    (zmod2 u hu).Finv a b c d y x =
      if a.toAdd = 1 ∧ b.toAdd = 1 ∧ c.toAdd = 1 then (u : R) else 1 := by
  rw [zmod2_eq_ofTwistingCocycle, ofTwistingCocycle_Finv_apply]
  simp only [TwistingCocycle.comap_ω, AddMonoidHom.coe_ofClass,
    AddEquiv.additiveMultiplicative_apply, toMul_ofMul, TwistingCocycle.zmod2_ω]
  split_ifs <;> simp

/-- F-symbols on `FusionRules.ofMul (Multiplicative (ZMod 2))` are in bijection with
`{ u : Rˣ // u * u = 1 }` via the `(1, 1, 1)` entry `F^{111}_1 = u`, with inverse
`FSymbols.zmod2`. -/
def zmod2Equiv :
    FSymbols R (FusionRules.ofMul (Multiplicative (ZMod 2))) ≃ { u : Rˣ // u * u = 1 } :=
  twistingCocycleEquiv.trans
    ((TwistingCocycle.domCongr (AddEquiv.additiveMultiplicative (ZMod 2))).trans
      TwistingCocycle.zmod2Equiv)

@[simp]
theorem val_zmod2Equiv_apply (P : FSymbols R (FusionRules.ofMul (Multiplicative (ZMod 2)))) :
    (((zmod2Equiv P).val : Rˣ) : R) =
      P.F (.ofAdd 1) (.ofAdd 1) (.ofAdd 1) (.ofAdd 1)
        (ofMulLeft (by decide)) (ofMulRight (by decide)) := by
  have hinv : (zmod2Equiv P).val = ((zmod2Equiv P).val)⁻¹ :=
    (inv_eq_of_mul_eq_one_right (zmod2Equiv P).property).symm
  rw [hinv, P.F_eq_inv_toTwistingCocycle_ω (.ofAdd 1) (.ofAdd 1) (.ofAdd 1) (.ofAdd 1)]
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
theorem zmod2_zmod2Equiv (P : FSymbols R (FusionRules.ofMul (Multiplicative (ZMod 2)))) :
    zmod2 (zmod2Equiv P).val (zmod2Equiv P).property = P := by
  rw [← zmod2Equiv_symm_apply (zmod2Equiv P)]
  exact zmod2Equiv.symm_apply_apply P

end ZMod2

end FSymbols

namespace RSymbols

section ZMod2

open FusionRules (ofMulIdx)
open GradedObject (TwistingCocycle PointedBraiding)

section CommSemiring

variable {K : Type v} [CommSemiring K]

/-- Construct R-symbols on `FSymbols.zmod2 u hu` from a square root `r : Kˣ` of `u` (`r * r = u`),
giving `R^{11}_0 = r` and `1` on all unit blocks. -/
def zmod2 {u : Kˣ} (hu : u * u = 1) (r : Kˣ) (hr : r * r = u) : RSymbols (FSymbols.zmod2 u hu) :=
  (ofPointedBraiding
    ((PointedBraiding.zmod2 hu r hr).comap
      (AddEquiv.additiveMultiplicative (ZMod 2) :
        Additive (Multiplicative (ZMod 2)) →+ ZMod 2))).cast
    (FSymbols.zmod2_eq_ofTwistingCocycle u hu).symm

theorem zmod2_eq_cast_ofPointedBraiding {u : Kˣ} (hu : u * u = 1) (r : Kˣ) (hr : r * r = u) :
    zmod2 hu r hr =
      (ofPointedBraiding
        ((PointedBraiding.zmod2 hu r hr).comap
          (AddEquiv.additiveMultiplicative (ZMod 2) :
            Additive (Multiplicative (ZMod 2)) →+ ZMod 2))).cast
        (FSymbols.zmod2_eq_ofTwistingCocycle u hu).symm :=
  (rfl)

@[simp]
theorem zmod2_R_apply {u : Kˣ} (hu : u * u = 1) (r : Kˣ) (hr : r * r = u)
    (a b c : Multiplicative (ZMod 2))
    (i : Fin ((FusionRules.ofMul (Multiplicative (ZMod 2))).N a b c))
    (j : Fin ((FusionRules.ofMul (Multiplicative (ZMod 2))).N b a c)) :
    (zmod2 hu r hr).R a b c i j = if a.toAdd = 1 ∧ b.toAdd = 1 then (r : K) else 1 := by
  rw [zmod2_eq_cast_ofPointedBraiding, cast_R, ofPointedBraiding_R_apply]
  simp only [PointedBraiding.comap_r, AddMonoidHom.coe_ofClass,
    AddEquiv.additiveMultiplicative_apply, toMul_ofMul, PointedBraiding.zmod2_r]
  split_ifs <;> simp

@[simp]
theorem zmod2_Rinv_apply {u : Kˣ} (hu : u * u = 1) (r : Kˣ) (hr : r * r = u)
    (a b c : Multiplicative (ZMod 2))
    (j : Fin ((FusionRules.ofMul (Multiplicative (ZMod 2))).N b a c))
    (i : Fin ((FusionRules.ofMul (Multiplicative (ZMod 2))).N a b c)) :
    (zmod2 hu r hr).Rinv a b c j i =
      if a.toAdd = 1 ∧ b.toAdd = 1 then ((r⁻¹ : Kˣ) : K) else 1 := by
  rw [zmod2_eq_cast_ofPointedBraiding, cast_Rinv, ofPointedBraiding_Rinv_apply]
  simp only [PointedBraiding.comap_r, AddMonoidHom.coe_ofClass,
    AddEquiv.additiveMultiplicative_apply, toMul_ofMul, PointedBraiding.zmod2_r]
  split_ifs <;> simp

/-- R-symbols on `FSymbols.zmod2 u hu` are in bijection with `{ r : Kˣ // r * r = u }` via the
nontrivial braiding entry `R^{11}_0 = r`, witnessing `(R^{11}_0)^2 = F^{111}_1`, with inverse
`RSymbols.zmod2`. -/
def zmod2Equiv (u : Kˣ) (hu : u * u = 1) :
    RSymbols (FSymbols.zmod2 u hu) ≃ { r : Kˣ // r * r = u } :=
  (Equiv.cast (congrArg RSymbols (FSymbols.zmod2_eq_ofTwistingCocycle u hu))).trans
    ((pointedBraidingEquiv _).trans
      ((PointedBraiding.comapEquiv (AddEquiv.additiveMultiplicative (ZMod 2))
        (TwistingCocycle.zmod2 u hu)).trans (PointedBraiding.zmod2Equiv u hu)))

@[simp]
theorem val_zmod2Equiv_apply (u : Kˣ) (hu : u * u = 1) (Q : RSymbols (FSymbols.zmod2 u hu)) :
    (((zmod2Equiv u hu Q).val : Kˣ) : K) =
      Q.R (.ofAdd 1) (.ofAdd 1) 1 (ofMulIdx (by decide)) (ofMulIdx (by decide)) := by
  have hcast {P₁ P₂ : FSymbols K (FusionRules.ofMul (Multiplicative (ZMod 2)))} (h : P₁ = P₂)
      (Q' : RSymbols P₁) : _root_.cast (congrArg RSymbols h) Q' = Q'.cast h := by
    cases h; simp
  have h := R_eq_toPointedBraiding_r (Q.cast (FSymbols.zmod2_eq_ofTwistingCocycle u hu))
    (.ofAdd 1) (.ofAdd 1) 1 (ofMulIdx (by decide)) (ofMulIdx (by decide))
  simpa [zmod2Equiv, hcast (FSymbols.zmod2_eq_ofTwistingCocycle u hu)] using h.symm

@[simp]
theorem zmod2Equiv_symm_apply (u : Kˣ) (hu : u * u = 1) (r : { r : Kˣ // r * r = u }) :
    (zmod2Equiv u hu).symm r = zmod2 hu r.val r.property := by
  have hcast {P₁ P₂ : FSymbols K (FusionRules.ofMul (Multiplicative (ZMod 2)))} (h : P₁ = P₂)
      (Q' : RSymbols P₂) : (Equiv.cast (congrArg RSymbols h)).symm Q' = Q'.cast h.symm := by
    cases h; simp
  simpa [zmod2Equiv, zmod2_eq_cast_ofPointedBraiding] using
    hcast (FSymbols.zmod2_eq_ofTwistingCocycle u hu) _

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

/-- `FSymbols.zmod2 u hu` admits R-symbols over `K` if and only if `u` is a square in `Kˣ`. -/
theorem nonempty_zmod2_iff (u : Kˣ) (hu : u * u = 1) :
    Nonempty (RSymbols (FSymbols.zmod2 u hu)) ↔ ∃ r : Kˣ, r * r = u := by
  rw [(zmod2Equiv u hu).nonempty_congr, nonempty_subtype]

/-- `FSymbols.zmod2 u hu` admits no R-symbols over `K` if and only if `u` has no square root in
`Kˣ`. -/
theorem isEmpty_zmod2_iff (u : Kˣ) (hu : u * u = 1) :
    IsEmpty (RSymbols (FSymbols.zmod2 u hu)) ↔ ∀ r : Kˣ, r * r ≠ u := by
  rw [(zmod2Equiv u hu).isEmpty_congr]
  simp [isEmpty_subtype]

end CommSemiring

section CommRing

variable {K : Type v} [CommRing K]

/-- For the trivial `Multiplicative (ZMod 2)` F-symbols (`u = 1`), `r = -1` gives the
super-vector-space braiding `R^{11}_0 = -1`. -/
def zmod2Super : RSymbols (FSymbols.zmod2 (1 : Kˣ) (mul_one 1)) :=
  zmod2 (mul_one 1) (-1) (by simp)

@[simp]
theorem zmod2Super_R_apply (a b c : Multiplicative (ZMod 2))
    (i : Fin ((FusionRules.ofMul (Multiplicative (ZMod 2))).N a b c))
    (j : Fin ((FusionRules.ofMul (Multiplicative (ZMod 2))).N b a c)) :
    (zmod2Super : RSymbols (FSymbols.zmod2 (1 : Kˣ) (mul_one 1))).R a b c i j =
      if a.toAdd = 1 ∧ b.toAdd = 1 then -1 else 1 := by
  simp [zmod2Super]

@[simp]
theorem zmod2Super_Rinv_apply (a b c : Multiplicative (ZMod 2))
    (j : Fin ((FusionRules.ofMul (Multiplicative (ZMod 2))).N b a c))
    (i : Fin ((FusionRules.ofMul (Multiplicative (ZMod 2))).N a b c)) :
    (zmod2Super : RSymbols (FSymbols.zmod2 (1 : Kˣ) (mul_one 1))).Rinv a b c j i =
      if a.toAdd = 1 ∧ b.toAdd = 1 then -1 else 1 := by
  simp [zmod2Super]

end CommRing

/-- Over `ℤ`, the nontrivial `Multiplicative (ZMod 2)` F-symbols with `F^{111}_1 = -1` admit no
R-symbols, since `-1` is not a square in `ℤˣ`. -/
instance instIsEmptyZMod2NegOneInt : IsEmpty (RSymbols (FSymbols.zmod2 (-1 : ℤˣ) (by decide))) :=
  (isEmpty_zmod2_iff (-1 : ℤˣ) (by decide)).mpr fun r ↦ by
    rcases Int.units_eq_one_or r with rfl | rfl <;> decide

end ZMod2

end RSymbols

end TauCeti
