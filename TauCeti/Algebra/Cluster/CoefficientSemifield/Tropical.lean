/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Cluster.CoefficientSemifield.Basic
public import TauCeti.Algebra.Group.FreeAbelianCharacter
public import Mathlib.Algebra.Order.Group.Int
public import Mathlib.Algebra.Order.Group.Lattice
public import Mathlib.Algebra.Order.Monoid.OrderDual
public import Mathlib.Algebra.Tropical.Basic
public import Mathlib.Data.Finsupp.Order

/-!
# Tropical coefficient semifields

`InfTropical A` is the tropicalization of an inf-semilattice-ordered additive commutative group.
Auxiliary addition is infimum, and multiplication is addition of exponents. Taking the
order dual of the exponent group gives supremum as auxiliary addition.

The tropical coefficient semifield `Trop J` is the free abelian group on `J`, with auxiliary
addition given by the componentwise minimum of exponents. Its generators encode the frozen
columns of a geometric cluster seed. The index type may be infinite: every element still has
finite support. Relabelling the generators preserves both operations, and for finite `J` the
exponent presentation agrees with the product of one-dimensional tropical groups.

Group evaluation `Trop.eval` extends any family `J → Q` in a commutative group to a
homomorphism `Trop J →* Q` using `TauCeti.freeAbelianCharEquiv`. Such evaluations
need not preserve tropical addition, so they are deliberately not coefficient-semifield
homomorphisms. In contrast, `InfTropical.reindex` preserves both operations.

## References

* S. Fomin and A. Zelevinsky, *Cluster algebras IV: Coefficients*, Definition 2.2.

The group evaluation reuses `freeAbelianCharEquiv`; finite exponents and relabelling reuse
Mathlib's `Finsupp.equivFunOnFinite` and `Finsupp.equivCongrLeft`.
-/

public section

namespace TauCeti

/-- The type of min-tropical exponents. Its coefficient semifield structure uses
infimum as auxiliary addition and the original addition as multiplication. -/
@[expose]
def InfTropical (A : Type*) := Multiplicative A

namespace InfTropical

variable {A : Type*}

/-- Reinterpret an exponent as a min-tropical element. -/
@[expose]
def ofAdd (a : A) : InfTropical A := Multiplicative.ofAdd a

/-- Reinterpret a min-tropical element as an exponent. -/
@[expose]
def toAdd (a : InfTropical A) : A := Multiplicative.toAdd a

/-- The equivalence between exponents and min-tropical elements. -/
@[expose]
def ofAddEquiv : A ≃ InfTropical A where
  toFun := ofAdd
  invFun := toAdd
  left_inv _ := rfl
  right_inv _ := rfl

/-- The equivalence between min-tropical elements and exponents. -/
@[expose]
def toAddEquiv : InfTropical A ≃ A := ofAddEquiv.symm

@[simp]
theorem ofAddEquiv_apply (a : A) : ofAddEquiv a = ofAdd a := rfl

@[simp]
theorem toAddEquiv_apply (a : InfTropical A) : toAddEquiv a = toAdd a := rfl

@[simp]
theorem toAdd_ofAdd (a : A) : toAdd (ofAdd a) = a := _root_.toAdd_ofAdd a

@[simp]
theorem ofAdd_toAdd (a : InfTropical A) : ofAdd (toAdd a) = a := _root_.ofAdd_toAdd a

@[ext]
theorem ext {a b : InfTropical A} (hab : toAdd a = toAdd b) : a = b :=
  Multiplicative.toAdd.injective hab

/-- Recursion on the underlying exponent of a min-tropical element. -/
@[elab_as_elim, cases_eliminator, induction_eliminator]
def rec {motive : InfTropical A → Sort*} (ofAdd : ∀ a, motive (ofAdd a)) :
    ∀ a, motive a := fun a => ofAdd (toAdd a)

instance [Inhabited A] : Inhabited (InfTropical A) := ⟨ofAdd default⟩
instance [Subsingleton A] : Subsingleton (InfTropical A) :=
  Multiplicative.toAdd.injective.subsingleton
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

/-- Min-tropical addition is infimum of exponents. -/
instance [Min A] : Add (InfTropical A) where
  add a b := ofAdd (toAdd a ⊓ toAdd b)

/-- The underlying exponent of tropical addition is the infimum of the exponents. -/
@[simp]
theorem toAdd_add [Min A] (a b : InfTropical A) :
    toAdd (a + b) = toAdd a ⊓ toAdd b := rfl

@[simp]
theorem ofAdd_inf [Min A] (a b : A) : ofAdd (a ⊓ b) = ofAdd a + ofAdd b := rfl

instance [SemilatticeInf A] : AddCommSemigroup (InfTropical A) where
  add_assoc a b c := congrArg Multiplicative.ofAdd (inf_assoc a.toAdd b.toAdd c.toAdd)
  add_comm a b := congrArg Multiplicative.ofAdd (inf_comm a.toAdd b.toAdd)

/-- Infimum distributes over translations in an ordered additive commutative group. -/
instance instCoefficientSemifield [AddCommGroup A] [SemilatticeInf A] [IsOrderedAddMonoid A] :
    CoefficientSemifield (InfTropical A) where
  left_distrib a b c := congrArg Multiplicative.ofAdd
    ((OrderIso.addLeft a.toAdd).map_inf b.toAdd c.toAdd)
  right_distrib a b c := congrArg Multiplicative.ofAdd
    ((OrderIso.addRight c.toAdd).map_inf a.toAdd b.toAdd)

/-- Infimum tropical addition is idempotent. -/
@[simp]
theorem add_self [SemilatticeInf A] (a : InfTropical A) : a + a = a := by
  apply ext
  exact inf_idem (toAdd a)

end InfTropical

/-- The tropical coefficient semifield on `J`: finitely supported integer exponents,
with multiplication adding exponents and auxiliary addition taking their minimum. -/
abbrev Trop (J : Type*) := InfTropical (J →₀ ℤ)

namespace Trop

variable {J J' J'' : Type*}

/-- The tropical generator with exponent one at `j` and zero elsewhere. -/
@[expose]
noncomputable def generator (j : J) : Trop J := InfTropical.ofAdd (Finsupp.single j 1)

@[simp]
theorem toAdd_generator (j : J) : InfTropical.toAdd (generator j) = Finsupp.single j 1 := rfl

/-- Every tropical element is generated by the standard generators. -/
@[ext]
theorem monoidHom_ext {Q : Type*} [CommGroup Q] (f g : Trop J →* Q)
    (h : ∀ j, f (generator j) = g (generator j)) : f = g :=
  freeAbelianChar_hom_ext f g h

@[simp]
theorem generator_inj {i j : J} : generator i = generator j ↔ i = j := by
  constructor
  · intro h
    apply (Finsupp.single_left_inj (one_ne_zero : (1 : ℤ) ≠ 0)).mp
    exact congrArg InfTropical.toAdd h
  · exact congrArg generator

@[simp]
theorem generator_ne_one (j : J) : generator j ≠ 1 := by
  intro h
  have h' : (Finsupp.single j 1 : J →₀ ℤ) = 0 := by
    rw [← toAdd_generator, h]
    exact _root_.toAdd_one
  classical
  have h'' := DFunLike.congr_fun h' j
  simp at h''

/-- The multiplicative universal property of the free abelian group of tropical exponents. -/
noncomputable def evalEquiv {Q : Type*} [CommGroup Q] : (J → Q) ≃* (Trop J →* Q) :=
  freeAbelianCharEquiv.symm

/-- Evaluate tropical monomials in a commutative group at the given values of the generators. -/
@[expose]
noncomputable def eval {Q : Type*} [CommGroup Q] (q : J → Q) : Trop J →* Q :=
  evalEquiv q

@[simp]
theorem evalEquiv_apply {Q : Type*} [CommGroup Q] (q : J → Q) :
    evalEquiv q = eval q := rfl

/-- Evaluation of a finitely supported exponent vector is the product of the corresponding
powers of the chosen coordinates. -/
@[simp]
theorem eval_ofAdd {Q : Type*} [CommGroup Q] (q : J → Q) (a : J →₀ ℤ) :
    eval q (InfTropical.ofAdd a) = a.prod (fun j n ↦ q j ^ n) :=
  freeAbelianCharEquiv_symm_apply_ofAdd q a

/-- Group evaluation sends each tropical generator to its chosen coordinate. -/
@[simp]
theorem eval_generator {Q : Type*} [CommGroup Q] (q : J → Q) (j : J) :
    eval q (generator j) = q j :=
  freeAbelianCharEquiv_symm_apply_ofAdd_single q j

/-- A group homomorphism is uniquely determined by its values on tropical generators. -/
theorem eval_unique {Q : Type*} [CommGroup Q] (f : Trop J →* Q) :
    f = eval (fun j ↦ f (generator j)) :=
  (monoidHom_ext f _ (fun j => (eval_generator (fun i => f (generator i)) j).symm))

@[simp]
theorem eval_generator_left {Q : Type*} [CommGroup Q] (f : Trop J →* Q) :
    eval (fun j ↦ f (generator j)) = f := eval_unique f |>.symm

@[simp]
theorem comp_eval {Q R : Type*} [CommGroup Q] [CommGroup R] (f : Q →* R) (q : J → Q) :
    f.comp (eval q) = eval (f ∘ q) := by
  apply monoidHom_ext
  intro j
  change f (eval q (generator j)) = eval (f ∘ q) (generator j)
  rw [eval_generator, eval_generator]
  rfl

/-- Minimum of two distinct tropical generators is the multiplicative identity. -/
@[simp]
theorem generator_add_generator {i j : J} (h : i ≠ j) : generator i + generator j = 1 := by
  classical
  apply InfTropical.ext
  have h_one : InfTropical.toAdd (1 : Trop J) = 0 := _root_.toAdd_one
  rw [InfTropical.toAdd_add, h_one, toAdd_generator, toAdd_generator]
  ext k
  simp only [Finsupp.single_apply, Finsupp.zero_apply, Finsupp.inf_apply]
  by_cases hi : i = k <;> by_cases hj : j = k <;> simp_all

/-- The normalization factor for an inverse generator is that inverse generator itself. -/
@[simp]
theorem inv_generator_add_one (j : J) : (generator j)⁻¹ + 1 = (generator j)⁻¹ := by
  classical
  apply InfTropical.ext
  have h_one : InfTropical.toAdd (1 : Trop J) = 0 := _root_.toAdd_one
  rw [InfTropical.toAdd_add, h_one]
  have hmin (x : ℤ) (hx : 0 ≤ x) : min (-x) 0 = -x := inf_eq_left.mpr (neg_nonpos.mpr hx)
  have hinv : InfTropical.toAdd (generator j)⁻¹ = -InfTropical.toAdd (generator j) :=
    _root_.toAdd_inv (generator j)
  rw [hinv]
  ext k
  simp only [toAdd_generator, Finsupp.single_apply, Finsupp.neg_apply, Finsupp.inf_apply]
  exact hmin _ (by split <;> simp)

end Trop

namespace InfTropical

variable {J J' J'' A : Type*} [AddZeroClass A] [SemilatticeInf A]

/-- Relabelling the exponent indices is an isomorphism of coefficient semifields. -/
@[expose]
noncomputable def reindex (e : J ≃ J') :
    InfTropical (J →₀ A) ≃+* InfTropical (J' →₀ A) where
  toEquiv := toAddEquiv.trans ((Finsupp.equivCongrLeft e).trans ofAddEquiv)
  map_mul' a b := by
    apply ext
    ext j
    exact congrArg (fun x : J →₀ A => x (e.symm j)) (_root_.toAdd_mul a b)
  map_add' a b := by
    apply ext
    ext j
    simp only [toAdd_add, Finsupp.inf_apply]
    rfl

@[simp]
theorem reindex_ofAdd (e : J ≃ J') (a : J →₀ A) :
    reindex e (ofAdd a) = ofAdd (Finsupp.equivMapDomain e a) := rfl

@[simp]
theorem toAdd_reindex (e : J ≃ J') (a : InfTropical (J →₀ A)) (j : J') :
    toAdd (reindex e a) j = toAdd a (e.symm j) := rfl

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
  apply ext
  ext j
  rw [toAdd_reindex, toAdd_reindex, toAdd_reindex]
  rfl

@[simp]
theorem reindex_trans (e : J ≃ J') (e' : J' ≃ J'') :
    (reindex (A := A) e).trans (reindex e') = reindex (e.trans e') := by
  apply RingEquiv.ext
  intro a
  exact reindex_reindex e e' a

@[simp]
theorem reindex_symm (e : J ≃ J') : (reindex (A := A) e).symm = reindex e.symm := rfl

end InfTropical

namespace Trop

@[simp]
theorem reindex_generator (e : J ≃ J') (j : J) :
    InfTropical.reindex e (generator j) = generator (e j) := by
  apply InfTropical.ext
  exact Finsupp.equivMapDomain_single e j 1

/-- Group evaluation is compatible with relabelling the generators. The evaluation is a group
homomorphism, with no assertion that it preserves auxiliary addition. -/
@[simp]
theorem eval_reindex {Q : Type*} [CommGroup Q] (q : J' → Q) (e : J ≃ J') (a : Trop J) :
    eval q (InfTropical.reindex e a) = eval (q ∘ e) a := by
  obtain ⟨a, rfl⟩ := InfTropical.ofAddEquiv.surjective a
  simp only [InfTropical.ofAddEquiv_apply, InfTropical.reindex_ofAdd, eval_ofAdd]
  exact Finsupp.prod_equivMapDomain e a (fun j n => q j ^ n)

end Trop

namespace CoefficientSemifield

/-- A linearly ordered additive commutative group, with minimum as auxiliary addition,
is a coefficient semifield. -/
@[to_dual
  /-- A linearly ordered additive commutative group, with maximum as auxiliary addition,
  is a coefficient semifield. -/]
instance instMinTropical {A : Type*} [AddCommGroup A] [LinearOrder A]
    [IsOrderedAddMonoid A] : CoefficientSemifield (MinTropical A) where
  left_distrib := mul_add
  right_distrib := add_mul

end CoefficientSemifield

namespace InfTropical

variable {J A : Type*}

/-- Infimum addition and multiplication by addition on `InfTropical A` agree with the
corresponding operations on `MinTropical A` when `A` is linearly ordered. -/
@[expose]
def equivMinTropical [Add A] [LinearOrder A] : InfTropical A ≃+* MinTropical A where
  toEquiv := toAddEquiv.trans MinTropical.tropEquiv
  map_mul' a b := by apply MinTropical.untrop_injective; exact _root_.toAdd_mul a b
  map_add' a b := by apply MinTropical.untrop_injective; exact toAdd_add a b

@[simp]
theorem equivMinTropical_apply [Add A] [LinearOrder A] (a : InfTropical A) :
    equivMinTropical a = MinTropical.trop (toAdd a) := rfl

@[simp]
theorem equivMinTropical_symm_apply [Add A] [LinearOrder A] (a : MinTropical A) :
    equivMinTropical.symm a = ofAdd (MinTropical.untrop a) := rfl

/-- Comparison with `MaxTropical` follows from `MinTropical.equivMaxTropical`. -/
def equivMaxTropical [Add A] [LinearOrder A] : InfTropical Aᵒᵈ ≃+* MaxTropical A :=
  equivMinTropical.trans MinTropical.equivMaxTropical

/-- For finite `J`, finitely supported exponents are arbitrary tuples of tropical exponents.
Both operations are componentwise. -/
@[expose]
noncomputable def equivFun [AddZeroClass A] [SemilatticeInf A] [Finite J] :
    InfTropical (J →₀ A) ≃+* (J → InfTropical A) where
  toEquiv := toAddEquiv.trans Finsupp.equivFunOnFinite
  map_mul' a b := by
    funext j
    exact congrArg (fun x : J →₀ A => x j) (_root_.toAdd_mul a b)
  map_add' a b := by
    funext j
    exact congrArg (fun x : J →₀ A => x j) (toAdd_add a b)

@[simp]
theorem equivFun_apply [AddZeroClass A] [SemilatticeInf A] [Finite J]
    (a : InfTropical (J →₀ A)) (j : J) : equivFun a j = ofAdd (toAdd a j) := rfl

@[simp]
theorem toAdd_equivFun_symm [AddZeroClass A] [SemilatticeInf A] [Finite J]
    (a : J → InfTropical A) (j : J) : toAdd (equivFun.symm a) j = toAdd (a j) := rfl

/-- For finite `J`, finitely supported exponents are also arbitrary tuples in `MinTropical A`. -/
@[expose]
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
    equivMinTropicalFun a j = MinTropical.trop (toAdd a j) := rfl

/-- Infimum becomes supremum after reversing the order of the exponents. -/
example [AddCommGroup A] [Lattice A] [IsOrderedAddMonoid A] :
    CoefficientSemifield (InfTropical Aᵒᵈ) := inferInstance

example [AddCommGroup A] [Lattice A] [IsOrderedAddMonoid A] (a b : A) :
    (ofAdd (OrderDual.toDual a) + ofAdd (OrderDual.toDual b)).toAdd =
      OrderDual.toDual (a ⊔ b) := by
  change OrderDual.toDual a ⊓ OrderDual.toDual b = _
  rfl

end InfTropical

namespace Trop

variable {J A : Type*}

/-- There is only one monomial when there are no generators. -/
example [IsEmpty J] : Unique (Trop J) := inferInstance

/-- Evaluating a Laurent monomial in any commutative group uses integer powers. -/
example {Q : Type*} [CommGroup Q] (q : Fin 2 → Q) :
    eval q ((generator 0)⁻¹ * generator 1 ^ (2 : ℤ)) = (q 0)⁻¹ * q 1 ^ (2 : ℤ) := by simp

/-- Transposing two generators exchanges their exponents. -/
example : InfTropical.reindex (Equiv.swap (0 : Fin 2) 1)
    ((generator 0)⁻¹ * generator 1 ^ (2 : ℤ)) = generator 0 ^ (2 : ℤ) * (generator 1)⁻¹ := by
  simp [mul_comm]

end Trop

end TauCeti
