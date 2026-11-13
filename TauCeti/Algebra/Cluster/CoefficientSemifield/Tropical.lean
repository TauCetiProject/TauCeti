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
public import Mathlib.Algebra.Tropical.Basic
public import Mathlib.Data.Finsupp.Order

/-!
# Tropical coefficient semifields

`InfTropical A` is the tropicalization of a lattice-ordered additive commutative group.
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
homomorphisms. In contrast, `Trop.reindex` is an isomorphism for both operations.

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

/-- Interpret an exponent as a min-tropical element. -/
@[expose]
def ofAdd (a : A) : InfTropical A := Multiplicative.ofAdd a

instance [Unique A] : Unique (InfTropical A) := inferInstanceAs (Unique (Multiplicative A))

/-- Infimum distributes over translations in a lattice-ordered additive commutative group. -/
instance instCoefficientSemifield [AddCommGroup A] [Lattice A] [IsOrderedAddMonoid A] :
    CoefficientSemifield (InfTropical A) where
  toCommGroup := inferInstanceAs (CommGroup (Multiplicative A))
  add a b := Multiplicative.ofAdd (a.toAdd ⊓ b.toAdd)
  add_assoc a b c := congrArg Multiplicative.ofAdd (inf_assoc a.toAdd b.toAdd c.toAdd)
  add_comm a b := congrArg Multiplicative.ofAdd (inf_comm a.toAdd b.toAdd)
  left_distrib a b c := congrArg Multiplicative.ofAdd (add_inf b.toAdd c.toAdd a.toAdd)
  right_distrib a b c := congrArg Multiplicative.ofAdd (inf_add a.toAdd b.toAdd c.toAdd)

variable [AddCommGroup A] [Lattice A] [IsOrderedAddMonoid A]

@[simp]
theorem toAdd_one :
    (1 : InfTropical A).toAdd = (0 : A) :=
  (rfl)

@[simp]
theorem toAdd_inv (a : InfTropical A) :
    a⁻¹.toAdd = -a.toAdd :=
  (rfl)

@[simp]
theorem toAdd_mul (a b : InfTropical A) :
    (a * b).toAdd = a.toAdd + b.toAdd :=
  (rfl)

@[simp]
theorem toAdd_zpow (a : InfTropical A) (n : ℤ) :
    (a ^ n).toAdd = n • a.toAdd :=
  (rfl)

@[simp]
theorem toAdd_add (a b : InfTropical A) :
    (a + b).toAdd = a.toAdd ⊓ b.toAdd :=
  (rfl)

@[simp]
theorem ofAdd_inf (a b : A) : ofAdd (a ⊓ b) = ofAdd a + ofAdd b :=
  (rfl)

/-- Tropical addition is idempotent. -/
@[simp]
theorem add_self (a : InfTropical A) : a + a = a := by
  apply Multiplicative.toAdd.injective
  simp

end InfTropical

/-- The tropical coefficient semifield on `J`: finitely supported integer exponents,
with multiplication adding exponents and auxiliary addition taking their minimum. -/
abbrev Trop (J : Type*) := InfTropical (J →₀ ℤ)

namespace Trop

variable {J J' J'' : Type*}

/-- The tropical generator with exponent one at `j` and zero elsewhere. -/
noncomputable def generator (j : J) : Trop J := InfTropical.ofAdd (Finsupp.single j 1)

@[simp]
theorem toAdd_generator (j : J) : (generator j).toAdd = Finsupp.single j 1 :=
  (rfl)

/-- Evaluate tropical monomials in a commutative group at the given values of the generators. -/
noncomputable def eval {Q : Type*} [CommGroup Q] (q : J → Q) : Trop J →* Q :=
  freeAbelianCharEquiv.symm q

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

/-- The minimum of two distinct generators is the multiplicative identity. -/
@[simp]
theorem generator_add_generator {i j : J} (h : i ≠ j) : generator i + generator j = 1 := by
  classical
  apply Multiplicative.toAdd.injective
  ext k
  by_cases hi : i = k <;> by_cases hj : j = k <;> simp_all

/-- The normalization factor for an inverse generator is that inverse generator itself. -/
@[simp]
theorem inv_generator_add_one (j : J) : (generator j)⁻¹ + 1 = (generator j)⁻¹ := by
  classical
  apply Multiplicative.toAdd.injective
  ext k
  by_cases h : j = k <;> simp [h]

section OrderedExponents

variable {A : Type*} [AddCommGroup A] [Lattice A] [IsOrderedAddMonoid A]

/-- Relabelling the exponent indices is an isomorphism of coefficient semifields. -/
noncomputable def reindex (e : J ≃ J') :
    InfTropical (J →₀ A) ≃+* InfTropical (J' →₀ A) where
  toEquiv := Multiplicative.toAdd.trans ((Finsupp.equivCongrLeft e).trans Multiplicative.ofAdd)
  map_mul' a b := by
    apply Multiplicative.toAdd.injective
    ext j
    change a.toAdd (e.symm j) + b.toAdd (e.symm j) = _
    rfl
  map_add' a b := by
    apply Multiplicative.toAdd.injective
    ext j
    change (a.toAdd ⊓ b.toAdd) (e.symm j) =
      (Finsupp.equivMapDomain e a.toAdd ⊓ Finsupp.equivMapDomain e b.toAdd) j
    simp

@[simp]
theorem reindex_ofAdd (e : J ≃ J') (a : J →₀ A) :
    reindex e (InfTropical.ofAdd a) = InfTropical.ofAdd (Finsupp.equivMapDomain e a) :=
  (rfl)

@[simp]
theorem toAdd_reindex (e : J ≃ J') (a : InfTropical (J →₀ A)) (j : J') :
    (reindex e a).toAdd j = a.toAdd (e.symm j) :=
  (rfl)

@[simp]
theorem reindex_refl : reindex (Equiv.refl J) = RingEquiv.refl (InfTropical (J →₀ A)) := by
  ext a
  apply Multiplicative.toAdd.injective
  ext j
  simp

/-- Relabellings compose in the same order as equivalences of the index sets. -/
@[simp]
theorem reindex_trans (e : J ≃ J') (e' : J' ≃ J'') :
    reindex (A := A) (e.trans e') = (reindex e).trans (reindex e') := by
  ext a
  apply Multiplicative.toAdd.injective
  ext j
  simp

@[simp]
theorem reindex_symm (e : J ≃ J') : (reindex (A := A) e).symm = reindex e.symm := by
  rfl

end OrderedExponents

@[simp]
theorem reindex_generator (e : J ≃ J') (j : J) :
    reindex e (generator j) = generator (e j) := by
  apply Multiplicative.toAdd.injective
  exact Finsupp.equivMapDomain_single e j 1

/-- Group evaluation is compatible with relabelling the generators. The evaluation is a group
homomorphism, with no assertion that it preserves auxiliary addition. -/
theorem eval_reindex {Q : Type*} [CommGroup Q] (q : J' → Q) (e : J ≃ J') (a : Trop J) :
    eval q (reindex e a) = eval (q ∘ e) a := by
  change eval q (reindex e (InfTropical.ofAdd a.toAdd)) =
    eval (q ∘ e) (InfTropical.ofAdd a.toAdd)
  simp [Finsupp.prod_equivMapDomain]

end Trop

namespace CoefficientSemifield

/-- A linearly ordered additive commutative group, with minimum as auxiliary addition,
is a coefficient semifield. -/
instance instMinTropical {A : Type*} [AddCommGroup A] [LinearOrder A]
    [IsOrderedAddMonoid A] : CoefficientSemifield (MinTropical A) where
  toCommGroup := inferInstance
  toAddCommSemigroup := inferInstance
  left_distrib := mul_add
  right_distrib := add_mul

end CoefficientSemifield

namespace Trop

variable {J A : Type*} [AddCommGroup A] [LinearOrder A] [IsOrderedAddMonoid A]

/-- For finite `J`, a tropical monomial is equivalently an arbitrary tuple of
exponents, regarded as one-dimensional tropical numbers. Both operations are componentwise. -/
noncomputable def equivFun [Finite J] :
    InfTropical (J →₀ A) ≃+* (J → MinTropical A) where
  toEquiv := Multiplicative.toAdd.trans
    (Finsupp.equivFunOnFinite.trans (Equiv.piCongrRight fun _ => MinTropical.tropEquiv))
  map_mul' a b := by
    funext j
    apply MinTropical.untrop_injective
    rfl
  map_add' a b := by
    funext j
    apply MinTropical.untrop_injective
    change (a.toAdd ⊓ b.toAdd) j = min (a.toAdd j) (b.toAdd j)
    simp

@[simp]
theorem equivFun_apply [Finite J] (a : InfTropical (J →₀ A)) (j : J) :
    equivFun a j = MinTropical.trop (a.toAdd j) :=
  (rfl)

@[simp]
theorem toAdd_equivFun_symm [Finite J] (a : J → MinTropical A) (j : J) :
    ((equivFun (J := J)).symm a).toAdd j = (a j).untrop :=
  (rfl)

/-! ### Checks of the tropical conventions -/

/-- There is only one monomial when there are no generators. -/
example [IsEmpty J] : Unique (Trop J) := inferInstance

/-- Evaluating a Laurent monomial in any commutative group uses integer powers. -/
example {Q : Type*} [CommGroup Q] (q : Fin 2 → Q) :
    eval q ((generator 0)⁻¹ * generator 1 ^ (2 : ℤ)) =
      (q 0)⁻¹ * q 1 ^ (2 : ℤ) := by
  simp

/-- Transposing two generators exchanges their exponents. -/
example : reindex (Equiv.swap (0 : Fin 2) 1)
    ((generator 0)⁻¹ * generator 1 ^ (2 : ℤ)) =
      generator 0 ^ (2 : ℤ) * (generator 1)⁻¹ := by
  simp [mul_comm]

end Trop

end TauCeti
