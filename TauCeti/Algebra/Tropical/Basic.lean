/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Order.Group.OrderIso
public import Mathlib.Algebra.Order.Monoid.OrderDual
public import Mathlib.Algebra.Tropical.Basic
public import Mathlib.Data.Finsupp.Order

/-!
# Infimum-tropical exponents

`InfTropical A` is the tropicalization of an inf-semilattice-ordered additive commutative group.
Auxiliary addition is infimum, and multiplication is addition of exponents. Taking the
order dual of the exponent group gives supremum as auxiliary addition.

`InfTropical.reindex` transports exponent vectors along an equivalence of index sets. For
linearly ordered exponents, the comparisons `equivMinTropical` and `equivMaxTropical` identify
this construction with Mathlib's min- and max-tropical types.
-/

public section

namespace TauCeti

/-- The type of min-tropical exponents. Auxiliary addition is infimum and multiplication is
the original addition. -/
@[expose]
def InfTropical (A : Type*) := Multiplicative A

namespace InfTropical

variable {A : Type*}

/-- Reinterpret an exponent as a min-tropical element.
See `ofAddEquiv` for the equivalence. -/
@[expose]
def ofAdd (a : A) : InfTropical A := Multiplicative.ofAdd a

/-- Reinterpret a min-tropical element as an exponent.
See `toAddEquiv` for the equivalence. -/
@[expose]
def toAdd (a : InfTropical A) : A := Multiplicative.toAdd a

theorem ofAdd_def (a : A) : ofAdd a = Multiplicative.ofAdd a := (rfl)

theorem toAdd_def (a : InfTropical A) : toAdd a = Multiplicative.toAdd a := (rfl)

/-- The equivalence between exponents and min-tropical elements. -/
def ofAddEquiv : A ≃ InfTropical A where
  toFun := ofAdd
  invFun := toAdd
  left_inv _ := rfl
  right_inv _ := rfl

/-- The equivalence between min-tropical elements and exponents. -/
def toAddEquiv : InfTropical A ≃ A := ofAddEquiv.symm

@[simp]
theorem ofAddEquiv_apply (a : A) : ofAddEquiv a = ofAdd a := (rfl)

@[simp]
theorem toAddEquiv_apply (a : InfTropical A) : toAddEquiv a = toAdd a := (rfl)

@[simp]
theorem ofAddEquiv_symm : ofAddEquiv.symm = (toAddEquiv : InfTropical A ≃ A) := (rfl)

@[simp]
theorem toAddEquiv_symm : toAddEquiv.symm = (ofAddEquiv : A ≃ InfTropical A) := (rfl)

@[simp]
theorem toAdd_ofAdd (a : A) : toAdd (ofAdd a) = a := (rfl)

@[simp]
theorem ofAdd_toAdd (a : InfTropical A) : ofAdd (toAdd a) = a := (rfl)

@[simp]
theorem ofAdd_inj {a b : A} : ofAdd a = ofAdd b ↔ a = b := ofAddEquiv.injective.eq_iff

@[simp]
theorem toAdd_inj {a b : InfTropical A} : toAdd a = toAdd b ↔ a = b :=
  toAddEquiv.injective.eq_iff

@[ext]
theorem ext {a b : InfTropical A} (hab : toAdd a = toAdd b) : a = b := toAdd_inj.mp hab

instance [Inhabited A] : Inhabited (InfTropical A) := ⟨ofAdd default⟩
instance [Subsingleton A] : Subsingleton (InfTropical A) := toAddEquiv.injective.subsingleton
instance [Unique A] : Unique (InfTropical A) := inferInstanceAs (Unique (Multiplicative A))
instance [DecidableEq A] : DecidableEq (InfTropical A) :=
  inferInstanceAs (DecidableEq (Multiplicative A))
instance [Nontrivial A] : Nontrivial (InfTropical A) :=
  inferInstanceAs (Nontrivial (Multiplicative A))

instance [Zero A] : One (InfTropical A) := inferInstanceAs (One (Multiplicative A))
instance [Add A] : Mul (InfTropical A) := inferInstanceAs (Mul (Multiplicative A))
instance [Neg A] : Inv (InfTropical A) := inferInstanceAs (Inv (Multiplicative A))
instance [Sub A] : Div (InfTropical A) := inferInstanceAs (Div (Multiplicative A))
instance [AddSemigroup A] : Semigroup (InfTropical A) :=
  inferInstanceAs (Semigroup (Multiplicative A))
instance [AddCommSemigroup A] : CommSemigroup (InfTropical A) :=
  inferInstanceAs (CommSemigroup (Multiplicative A))
instance [AddZeroClass A] : MulOneClass (InfTropical A) :=
  inferInstanceAs (MulOneClass (Multiplicative A))
instance [AddMonoid A] : Monoid (InfTropical A) := inferInstanceAs (Monoid (Multiplicative A))
instance [AddCommMonoid A] : CommMonoid (InfTropical A) :=
  inferInstanceAs (CommMonoid (Multiplicative A))
instance [AddGroup A] : Group (InfTropical A) := inferInstanceAs (Group (Multiplicative A))
instance [AddCommGroup A] : CommGroup (InfTropical A) :=
  inferInstanceAs (CommGroup (Multiplicative A))

@[simp]
theorem toAdd_one [Zero A] : toAdd (1 : InfTropical A) = 0 := (rfl)

@[simp]
theorem ofAdd_zero [Zero A] : ofAdd (0 : A) = 1 := (rfl)

@[simp]
theorem toAdd_eq_zero [Zero A] {a : InfTropical A} : toAdd a = 0 ↔ a = 1 := by
  rw [← toAdd_ofAdd (0 : A), toAdd_inj, ofAdd_zero]

@[simp]
theorem ofAdd_eq_one [Zero A] {a : A} : ofAdd a = 1 ↔ a = 0 := by
  rw [← ofAdd_zero, ofAdd_inj]

@[simp]
theorem toAdd_mul [Add A] (a b : InfTropical A) : toAdd (a * b) = toAdd a + toAdd b := (rfl)

@[simp]
theorem ofAdd_add [Add A] (a b : A) : ofAdd (a + b) = ofAdd a * ofAdd b := (rfl)

@[simp]
theorem toAdd_inv [Neg A] (a : InfTropical A) : toAdd a⁻¹ = -toAdd a := (rfl)

@[simp]
theorem ofAdd_neg [Neg A] (a : A) : ofAdd (-a) = (ofAdd a)⁻¹ := (rfl)

@[simp]
theorem toAdd_div [Sub A] (a b : InfTropical A) : toAdd (a / b) = toAdd a - toAdd b := (rfl)

@[simp]
theorem ofAdd_sub [Sub A] (a b : A) : ofAdd (a - b) = ofAdd a / ofAdd b := (rfl)

@[simp]
theorem toAdd_pow [AddMonoid A] (a : InfTropical A) (n : ℕ) : toAdd (a ^ n) = n • toAdd a :=
  _root_.toAdd_pow a n

@[simp]
theorem ofAdd_nsmul [AddMonoid A] (n : ℕ) (a : A) : ofAdd (n • a) = ofAdd a ^ n := by
  apply toAdd_inj.mp
  simp only [toAdd_ofAdd, toAdd_pow]

@[simp]
theorem toAdd_zpow [AddGroup A] (a : InfTropical A) (n : ℤ) : toAdd (a ^ n) = n • toAdd a :=
  _root_.toAdd_zpow a n

@[simp]
theorem ofAdd_zsmul [AddGroup A] (n : ℤ) (a : A) : ofAdd (n • a) = ofAdd a ^ n := by
  apply toAdd_inj.mp
  simp only [toAdd_ofAdd, toAdd_zpow]

/-- Recursion on the underlying exponent of a min-tropical element. -/
@[elab_as_elim, cases_eliminator, induction_eliminator]
def rec {motive : InfTropical A → Sort*} (ofAdd : ∀ a, motive (ofAdd a)) :
    ∀ a, motive a := fun a => ofAdd (toAdd a)

@[simp]
theorem rec_ofAdd {motive : InfTropical A → Sort*} (h : ∀ a, motive (ofAdd a)) (a : A) :
    rec h (ofAdd a) = h a := (rfl)

/-- Min-tropical addition is infimum of exponents. -/
instance [Min A] : Add (InfTropical A) where
  add a b := ofAdd (toAdd a ⊓ toAdd b)

/-- The underlying exponent of tropical addition is the infimum of the exponents. -/
@[simp]
theorem toAdd_add [Min A] (a b : InfTropical A) :
    toAdd (a + b) = toAdd a ⊓ toAdd b := (rfl)

@[simp]
theorem ofAdd_inf [Min A] (a b : A) : ofAdd (a ⊓ b) = ofAdd a + ofAdd b := (rfl)

instance [SemilatticeInf A] : AddCommSemigroup (InfTropical A) where
  add_assoc a b c := ext (by simp only [toAdd_add, inf_assoc])
  add_comm a b := ext (by simp only [toAdd_add, inf_comm])

instance [AddCommGroup A] [SemilatticeInf A] [IsOrderedAddMonoid A] : Distrib (InfTropical A) where
  left_distrib a b c := by
    apply ext
    simp only [toAdd_mul, toAdd_add]
    exact (OrderIso.addLeft (toAdd a)).map_inf (toAdd b) (toAdd c)
  right_distrib a b c := by
    apply ext
    simp only [toAdd_mul, toAdd_add]
    exact (OrderIso.addRight (toAdd c)).map_inf (toAdd a) (toAdd b)

/-- Infimum tropical addition is idempotent. -/
@[simp]
theorem add_self [SemilatticeInf A] (a : InfTropical A) : a + a = a := ext (inf_idem (toAdd a))

section Finsupp

variable {J J' J'' : Type*} [AddZeroClass A] [SemilatticeInf A]

/-- A homomorphism from integer exponents is determined by its values on the standard generators. -/
@[ext]
theorem monoidHom_ext {Q : Type*} [Monoid Q] ⦃f g : InfTropical (J →₀ ℤ) →* Q⦄
    (h : ∀ j, f (ofAdd (Finsupp.single j 1)) = g (ofAdd (Finsupp.single j 1))) : f = g :=
  Finsupp.mulHom_ext' fun j => MonoidHom.ext_mint (h j)

/-- Relabelling the exponent indices is an equivalence preserving both tropical operations. -/
noncomputable def reindex (e : J ≃ J') :
    InfTropical (J →₀ A) ≃+* InfTropical (J' →₀ A) where
  toEquiv := toAddEquiv.trans ((Finsupp.equivCongrLeft e).trans ofAddEquiv)
  map_mul' a b := by
    apply ext
    ext j
    exact congrArg (fun x : J →₀ A => x (e.symm j)) (toAdd_mul a b)
  map_add' a b := by
    apply ext
    ext j
    simp only [toAdd_add, Finsupp.inf_apply]
    rfl

@[simp]
theorem reindex_ofAdd (e : J ≃ J') (a : J →₀ A) :
    reindex e (ofAdd a) = ofAdd (Finsupp.equivMapDomain e a) := (rfl)

@[simp]
theorem toAdd_reindex (e : J ≃ J') (a : InfTropical (J →₀ A)) (j : J') :
    toAdd (reindex e a) j = toAdd a (e.symm j) := (rfl)

@[simp]
theorem reindex_refl : reindex (Equiv.refl J) = RingEquiv.refl (InfTropical (J →₀ A)) := by
  apply RingEquiv.ext
  intro a
  apply ext
  exact Finsupp.equivMapDomain_refl (toAdd a)

/-- Relabellings compose in the same order as equivalences of the index sets. -/
@[simp]
theorem reindex_reindex (e : J ≃ J') (e' : J' ≃ J'') (a : InfTropical (J →₀ A)) :
    reindex e' (reindex e a) = reindex (e.trans e') a := by
  ext j
  simp

@[simp]
theorem reindex_trans (e : J ≃ J') (e' : J' ≃ J'') :
    (reindex (A := A) e).trans (reindex e') = reindex (e.trans e') := by
  ext a
  simp

@[simp]
theorem reindex_symm (e : J ≃ J') : (reindex (A := A) e).symm = reindex e.symm := (rfl)

end Finsupp

/-- Infimum addition and multiplication by addition on `InfTropical A` agree with the
corresponding operations on `MinTropical A` when `A` is linearly ordered. -/
def equivMinTropical [Add A] [LinearOrder A] : InfTropical A ≃+* MinTropical A where
  toEquiv := toAddEquiv.trans MinTropical.tropEquiv
  map_mul' a b := by apply MinTropical.untrop_injective; simp
  map_add' a b := by apply MinTropical.untrop_injective; simp

@[simp]
theorem equivMinTropical_apply [Add A] [LinearOrder A] (a : InfTropical A) :
    equivMinTropical a = MinTropical.trop (toAdd a) := (rfl)

@[simp]
theorem equivMinTropical_symm_apply [Add A] [LinearOrder A] (a : MinTropical A) :
    equivMinTropical.symm a = ofAdd (MinTropical.untrop a) := (rfl)

/-- Supremum addition (via `Aᵒᵈ`) and multiplication by addition on `InfTropical Aᵒᵈ` agree
with the corresponding operations on `MaxTropical A` when `A` is linearly ordered. -/
def equivMaxTropical [Add A] [LinearOrder A] : InfTropical Aᵒᵈ ≃+* MaxTropical A :=
  equivMinTropical.trans MinTropical.equivMaxTropical

@[simp]
theorem equivMaxTropical_apply [Add A] [LinearOrder A] (a : InfTropical Aᵒᵈ) :
    equivMaxTropical a = MaxTropical.trop (OrderDual.ofDual (toAdd a)) := (rfl)

@[simp]
theorem equivMaxTropical_symm_apply [Add A] [LinearOrder A] (a : MaxTropical A) :
    equivMaxTropical.symm a = ofAdd (OrderDual.toDual (MaxTropical.untrop a)) := by
  apply RingEquiv.injective (equivMaxTropical (A := A))
  rw [RingEquiv.apply_symm_apply, equivMaxTropical_apply]
  rfl

/-- For finite `J`, finitely supported exponents are arbitrary tuples of tropical exponents.
Both operations are componentwise. -/
noncomputable def equivFun [AddZeroClass A] [SemilatticeInf A] [Finite J] :
    InfTropical (J →₀ A) ≃+* (J → InfTropical A) where
  toEquiv := toAddEquiv.trans Finsupp.equivFunOnFinite
  map_mul' a b := by
    funext j
    exact congrArg (fun x : J →₀ A => x j) (toAdd_mul a b)
  map_add' a b := by
    funext j
    exact congrArg (fun x : J →₀ A => x j) (toAdd_add a b)

@[simp]
theorem equivFun_apply [AddZeroClass A] [SemilatticeInf A] [Finite J]
    (a : InfTropical (J →₀ A)) (j : J) : equivFun a j = ofAdd (toAdd a j) := (rfl)

@[simp]
theorem toAdd_equivFun_symm [AddZeroClass A] [SemilatticeInf A] [Finite J]
    (a : J → InfTropical A) (j : J) : toAdd (equivFun.symm a) j = toAdd (a j) := (rfl)

/-- For finite `J`, finitely supported exponents are also arbitrary tuples in `MinTropical A`. -/
noncomputable def equivMinTropicalFun [AddZeroClass A] [LinearOrder A] [Finite J] :
    InfTropical (J →₀ A) ≃+* (J → MinTropical A) where
  toEquiv := equivFun.toEquiv.trans
    ((MulEquiv.piCongrRight fun _ : J => equivMinTropical.toMulEquiv).toEquiv)
  map_add' := (equivFun.toAddEquiv.trans
    (AddEquiv.piCongrRight fun _ : J => equivMinTropical.toAddEquiv)).map_add
  map_mul' := (equivFun.toMulEquiv.trans
    (MulEquiv.piCongrRight fun _ : J => equivMinTropical.toMulEquiv)).map_mul

@[simp]
theorem equivMinTropicalFun_apply [AddZeroClass A] [LinearOrder A] [Finite J]
    (a : InfTropical (J →₀ A)) (j : J) :
    equivMinTropicalFun a j = MinTropical.trop (toAdd a j) := (rfl)

@[simp]
theorem toAdd_equivMinTropicalFun_symm [AddZeroClass A] [LinearOrder A] [Finite J]
    (a : J → MinTropical A) (j : J) : toAdd (equivMinTropicalFun.symm a) j = (a j).untrop :=
  (rfl)

end InfTropical

end TauCeti
