/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.Finite.Basic
public import TauCeti.AlgebraicGeometry.Frobenius.Basic

/-!
# Iterated absolute Frobenius

The `n`-fold absolute Frobenius of a scheme in characteristic `p` is the endomorphism obtained by
composing its absolute Frobenius `n` times.  It fixes the underlying topological space and raises
sections to their `p ^ n`-th powers.  These iterates are the absolute maps underlying relative
Frobenius twists and finite-field Frobenius morphisms.

## Main definitions

* `AlgebraicGeometry.Scheme.iterateFrobenius`: the `n`-fold absolute Frobenius of a scheme.

## Main results

* `AlgebraicGeometry.Scheme.iterateFrobenius_zero`, `_succ`, and `_add`: the iteration laws.
* `AlgebraicGeometry.Scheme.iterateFrobenius_naturality`: every morphism of characteristic-`p`
  schemes commutes with every iterate.
* `AlgebraicGeometry.Scheme.iterateFrobenius_appTop_apply`: the iterate raises global sections to
  their `p ^ n`-th powers.
* `AlgebraicGeometry.Scheme.qPowerFrobenius`: the absolute `q`-power map of a scheme over a finite
  field of cardinality `q`.

## References

* The Stacks Project, chapter Varieties, section Frobenii, Remark 33.36.11.
-/

public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Scheme

variable {X Y : Scheme.{u}} {p : ℕ} [Fact p.Prime]

/-- The `n`-fold absolute Frobenius of a scheme in which the prime `p` vanishes. -/
noncomputable def iterateFrobenius (X : Scheme.{u}) (p : ℕ) [Fact p.Prime]
    (hX : (p : Γ(X, ⊤)) = 0) : ℕ → (X ⟶ X)
  | 0 => 𝟙 X
  | n + 1 => X.iterateFrobenius p hX n ≫ X.frobenius p hX

/-- The zeroth absolute Frobenius iterate is the identity. -/
@[simp]
theorem iterateFrobenius_zero (hX : (p : Γ(X, ⊤)) = 0) :
    X.iterateFrobenius p hX 0 = 𝟙 X :=
  (rfl)

/-- A successor absolute Frobenius iterate is obtained by composing with one Frobenius. -/
theorem iterateFrobenius_succ (hX : (p : Γ(X, ⊤)) = 0) (n : ℕ) :
    X.iterateFrobenius p hX (n + 1) =
      X.iterateFrobenius p hX n ≫ X.frobenius p hX :=
  (rfl)

/-- The first absolute Frobenius iterate is the absolute Frobenius. -/
@[simp]
theorem iterateFrobenius_one (hX : (p : Γ(X, ⊤)) = 0) :
    X.iterateFrobenius p hX 1 = X.frobenius p hX := by
  simp [iterateFrobenius_succ]

/-- Adding iteration exponents corresponds to composition of absolute Frobenius iterates. -/
theorem iterateFrobenius_add (hX : (p : Γ(X, ⊤)) = 0) (m n : ℕ) :
    X.iterateFrobenius p hX (m + n) =
      X.iterateFrobenius p hX m ≫ X.iterateFrobenius p hX n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Nat.add_succ, iterateFrobenius_succ, ih, iterateFrobenius_succ, Category.assoc]

/-- Every absolute Frobenius iterate fixes the underlying point of the scheme. -/
theorem iterateFrobenius_apply (hX : (p : Γ(X, ⊤)) = 0) (n : ℕ) (x : X) :
    X.iterateFrobenius p hX n x = x := by
  induction n with
  | zero => rfl
  | succ n ih => simp [iterateFrobenius_succ, ih]

/-- Every absolute Frobenius iterate has the identity map on the underlying space. -/
@[simp]
theorem iterateFrobenius_base (hX : (p : Γ(X, ⊤)) = 0) (n : ℕ) :
    (X.iterateFrobenius p hX n).base = 𝟙 _ := by
  induction n with
  | zero => rfl
  | succ n ih => simp [iterateFrobenius_succ, ih]

/-- The `n`-fold absolute Frobenius raises global sections to their `p ^ n`-th powers. -/
@[simp]
theorem iterateFrobenius_appTop_apply (hX : (p : Γ(X, ⊤)) = 0) (n : ℕ)
    (s : Γ(X, ⊤)) :
    (X.iterateFrobenius p hX n).appTop s = s ^ p ^ n := by
  induction n generalizing s with
  | zero => simp
  | succ n ih =>
    rw [iterateFrobenius_succ, Scheme.Hom.comp_appTop, CommRingCat.comp_apply,
      frobenius_appTop_apply, ih, Nat.pow_succ', pow_mul]

omit [Fact p.Prime] in
/-- The prime `p` vanishes on the global sections of the spectrum of a ring of
characteristic `p`. -/
theorem natCast_spec_eq_zero (R : CommRingCat.{u}) [CharP R p] :
    (p : Γ(Spec R, ⊤)) = 0 := by
  have hR : (p : R) = 0 := CharP.cast_eq_zero R p
  simpa only [map_natCast, map_zero] using congr((ΓSpecIso R).inv $hR)

/-- On an affine scheme, iterated absolute Frobenius is induced by the corresponding iterated
Frobenius of the coordinate ring. -/
theorem Spec_map_iterateFrobenius (R : Type u) [CommRing R] [CharP R p] (n : ℕ) :
    Spec.map (CommRingCat.ofHom (_root_.iterateFrobenius R p n)) =
      (Spec (CommRingCat.of R)).iterateFrobenius p
        (natCast_spec_eq_zero (CommRingCat.of R)) n := by
  induction n with
  | zero =>
    simpa only [_root_.iterateFrobenius_zero, CommRingCat.ofHom_id,
      iterateFrobenius_zero] using Spec.map_id (CommRingCat.of R)
  | succ n ih =>
    rw [iterateFrobenius_succ]
    rw [← ih, ← Spec_map_powRingHom (CommRingCat.of R) (CharP.cast_eq_zero R p),
      ← Spec.map_comp]
    congr 1
    rw [← CommRingCat.ofHom_comp,
      TauCeti.powRingHom_eq_frobenius (CharP.cast_eq_zero R p)]
    simpa only [_root_.iterateFrobenius_one] using
      congrArg CommRingCat.ofHom (_root_.iterateFrobenius_add R p n 1)

/-- Every morphism of schemes in characteristic `p` commutes with every absolute Frobenius
iterate. -/
@[reassoc]
theorem iterateFrobenius_naturality (hX : (p : Γ(X, ⊤)) = 0)
    (hY : (p : Γ(Y, ⊤)) = 0) (f : X ⟶ Y) (n : ℕ) :
    X.iterateFrobenius p hX n ≫ f = f ≫ Y.iterateFrobenius p hY n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [iterateFrobenius_succ, iterateFrobenius_succ, Category.assoc,
      frobenius_naturality hX hY f, ← Category.assoc, ih, Category.assoc]

/-- The absolute `q`-power Frobenius of a scheme over a finite field `k`, where
`q = Nat.card k = p ^ a`. -/
noncomputable def qPowerFrobenius (k : Type u) [Field k] [CharP k p]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k)) (a : ℕ) (_ha : Nat.card k = p ^ a) :
    X ⟶ X :=
  X.iterateFrobenius p
    (natCast_eq_zero_of_hom f (natCast_spec_eq_zero (CommRingCat.of k))) a

/-- The finite-field `q`-power Frobenius is the specified absolute Frobenius iterate. -/
theorem qPowerFrobenius_eq_iterated (k : Type u) [Field k] [CharP k p]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k)) (a : ℕ)
    (ha : Nat.card k = p ^ a) :
    qPowerFrobenius k f a ha =
      X.iterateFrobenius p
        (natCast_eq_zero_of_hom f (natCast_spec_eq_zero (CommRingCat.of k))) a :=
  (rfl)

/-- The finite-field `q`-power Frobenius raises global sections to their `q`-th powers. -/
@[simp]
theorem qPowerFrobenius_appTop_apply (k : Type u) [Field k] [CharP k p]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k)) (a : ℕ)
    (ha : Nat.card k = p ^ a) (s : Γ(X, ⊤)) :
    (qPowerFrobenius k f a ha).appTop s = s ^ Nat.card k := by
  rw [qPowerFrobenius_eq_iterated, iterateFrobenius_appTop_apply, ha]

/-- Every morphism between schemes over the same finite field commutes with their `q`-power
Frobenius maps. -/
@[reassoc]
theorem qPowerFrobenius_naturality (k : Type u) [Field k] [CharP k p]
    {X Y : Scheme.{u}} (fX : X ⟶ Spec (CommRingCat.of k))
    (fY : Y ⟶ Spec (CommRingCat.of k)) (g : X ⟶ Y) (a : ℕ)
    (ha : Nat.card k = p ^ a) :
    qPowerFrobenius k fX a ha ≫ g = g ≫ qPowerFrobenius k fY a ha := by
  exact iterateFrobenius_naturality
    (natCast_eq_zero_of_hom fX (natCast_spec_eq_zero (CommRingCat.of k)))
    (natCast_eq_zero_of_hom fY (natCast_spec_eq_zero (CommRingCat.of k))) g a

/-- The finite-field `q`-power Frobenius is a morphism over the given finite field. -/
@[reassoc (attr := simp)]
theorem qPowerFrobenius_over (k : Type u) [Field k] [Finite k] [CharP k p]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k)) (a : ℕ)
    (ha : Nat.card k = p ^ a) :
    qPowerFrobenius k f a ha ≫ f = f := by
  rw [qPowerFrobenius_eq_iterated,
    iterateFrobenius_naturality
      (natCast_eq_zero_of_hom f (natCast_spec_eq_zero (CommRingCat.of k)))
      (natCast_spec_eq_zero (CommRingCat.of k)) f a]
  suffices (Spec (CommRingCat.of k)).iterateFrobenius p
      (natCast_spec_eq_zero (CommRingCat.of k)) a = 𝟙 _ by
    rw [this, Category.comp_id]
  rw [← Spec_map_iterateFrobenius]
  let _ : Fintype k := Fintype.ofFinite k
  have ha' : Fintype.card k = p ^ a := by simpa using ha
  rw [_root_.iterateFrobenius_eq_pow, FiniteField.frobenius_pow ha']
  exact Spec.map_id _

end AlgebraicGeometry.Scheme
