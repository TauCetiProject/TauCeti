/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Cluster.CoefficientSemifield.Hom
public import TauCeti.Algebra.Group.FreeAbelianCharacter
public import Mathlib.Algebra.Tropical.Basic
public import Mathlib.Data.Finsupp.Basic
public import Mathlib.Order.Preorder.Finsupp

/-!
# Tropical coefficient semifields

The tropical coefficient semifield `Trop J` is the free abelian group on `J`, with auxiliary
addition given by the componentwise minimum of exponents. Its generators encode the frozen
columns of a geometric cluster seed. The index type may be infinite: every element still has
finite support. Relabelling the generators preserves both operations, and for finite `J` the
exponent presentation agrees with the product of one-dimensional tropical groups.

Group evaluation is supplied by `TauCeti.freeAbelianCharEquiv`: its inverse extends any
family `J → Q` in a commutative group to a homomorphism `Trop J →* Q`. Such evaluations
need not preserve tropical addition, so they are deliberately not coefficient-semifield
homomorphisms. In contrast, `Trop.reindex` is an isomorphism for both operations.

## References

* S. Fomin and A. Zelevinsky, *Cluster algebras IV: Coefficients*, Definition 2.2.

The group evaluation reuses `freeAbelianCharEquiv`; finite exponents and relabelling reuse
Mathlib's `Finsupp.equivFunOnFinite` and `Finsupp.equivCongrLeft`.
-/

public section

namespace TauCeti

/-- The tropical coefficient semifield on `J`: finitely supported integer exponents,
with multiplication adding exponents and auxiliary addition taking their minimum. -/
abbrev Trop (J : Type*) := Multiplicative (J →₀ ℤ)

namespace Trop

variable {J J' J'' : Type*}

/-- The auxiliary addition of tropical monomials is the pointwise minimum of exponents. -/
noncomputable instance : CoefficientSemifield (Trop J) where
  toCommGroup := inferInstanceAs (CommGroup (Multiplicative (J →₀ ℤ)))
  add a b := Multiplicative.ofAdd (a.toAdd ⊓ b.toAdd)
  add_assoc a b c := congrArg Multiplicative.ofAdd (inf_assoc a.toAdd b.toAdd c.toAdd)
  add_comm a b := congrArg Multiplicative.ofAdd (inf_comm a.toAdd b.toAdd)
  left_distrib a b c := by
    apply Multiplicative.toAdd.injective
    ext j
    exact (min_add_add_left (a.toAdd j) (b.toAdd j) (c.toAdd j)).symm
  right_distrib a b c := by
    apply Multiplicative.toAdd.injective
    ext j
    exact (min_add_add_right (a.toAdd j) (b.toAdd j) (c.toAdd j)).symm

@[simp]
theorem toAdd_add (a b : Trop J) : (a + b).toAdd = a.toAdd ⊓ b.toAdd :=
  (rfl)

@[simp]
theorem ofAdd_inf (a b : J →₀ ℤ) :
    (Multiplicative.ofAdd (a ⊓ b) : Trop J) = Multiplicative.ofAdd a + Multiplicative.ofAdd b :=
  (rfl)

/-- Tropical addition is idempotent. -/
@[simp]
theorem add_self (a : Trop J) : a + a = a := by
  apply Multiplicative.toAdd.injective
  simp

/-- The tropical generator with exponent one at `j` and zero elsewhere. -/
noncomputable def generator (j : J) : Trop J := Multiplicative.ofAdd (Finsupp.single j 1)

@[simp]
theorem toAdd_generator (j : J) : (generator j).toAdd = Finsupp.single j 1 :=
  (rfl)

/-- Group evaluation sends each tropical generator to its chosen coordinate. -/
@[simp]
theorem eval_generator {Q : Type*} [CommGroup Q] (q : J → Q) (j : J) :
    freeAbelianCharEquiv.symm q (generator j) = q j := by
  simpa only [generator] using freeAbelianCharEquiv_symm_apply_ofAdd_single q j

/-- Extending the family of tropical generators gives the identity group homomorphism. -/
@[simp]
theorem freeAbelianCharEquiv_symm_generator :
    freeAbelianCharEquiv.symm (generator (J := J)) = MonoidHom.id (Trop J) := by
  apply freeAbelianCharEquiv.injective
  rw [MulEquiv.apply_symm_apply]
  funext j
  apply Multiplicative.toAdd.injective
  simp [freeAbelianCharEquiv_apply]

/-- A tropical monomial is the finite product of its generators to their integer exponents. -/
theorem eq_prod_generator (a : Trop J) :
    a = a.toAdd.prod (fun j n ↦ generator j ^ n) := by
  simpa only [freeAbelianCharEquiv_symm_generator, MonoidHom.id_apply, ofAdd_toAdd] using
    freeAbelianCharEquiv_symm_apply_ofAdd (M := Trop J) generator a.toAdd

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

/-- Relabelling the tropical generators is an isomorphism of coefficient semifields. -/
noncomputable def reindex (e : J ≃ J') : Trop J ≃+* Trop J' where
  toEquiv := Multiplicative.toAdd.trans ((Finsupp.equivCongrLeft e).trans Multiplicative.ofAdd)
  map_mul' a b := by
    apply Multiplicative.toAdd.injective
    ext j
    simp [Finsupp.equivCongrLeft_apply, Finsupp.equivMapDomain_apply]
  map_add' a b := by
    apply Multiplicative.toAdd.injective
    ext j
    simp [Finsupp.equivCongrLeft_apply, Finsupp.equivMapDomain_apply]

@[simp]
theorem reindex_ofAdd (e : J ≃ J') (a : J →₀ ℤ) :
    reindex e (Multiplicative.ofAdd a) = Multiplicative.ofAdd (Finsupp.equivMapDomain e a) :=
  (rfl)

@[simp]
theorem toAdd_reindex (e : J ≃ J') (a : Trop J) (j : J') :
    (reindex e a).toAdd j = a.toAdd (e.symm j) :=
  (rfl)

@[simp]
theorem reindex_generator (e : J ≃ J') (j : J) :
    reindex e (generator j) = generator (e j) := by
  apply Multiplicative.toAdd.injective
  exact Finsupp.equivMapDomain_single e j 1

@[simp]
theorem reindex_refl : reindex (Equiv.refl J) = RingEquiv.refl (Trop J) := by
  ext a j
  simp

/-- Relabellings compose in the same order as equivalences of the index sets. -/
@[simp]
theorem reindex_trans (e : J ≃ J') (e' : J' ≃ J'') :
    reindex (e.trans e') = (reindex e).trans (reindex e') := by
  ext a j
  simp

@[simp]
theorem reindex_symm (e : J ≃ J') : (reindex e).symm = reindex e.symm := by
  rfl

@[simp]
theorem reindex_toCoefficientSemifieldHom_comp_symm (e : J ≃ J') :
    (reindex e).toCoefficientSemifieldHom.comp
        (reindex e.symm).toCoefficientSemifieldHom =
      CoefficientSemifieldHom.id (Trop J') := by
  rw [← reindex_symm e]
  exact (reindex e).toCoefficientSemifieldHom_comp_symm_toCoefficientSemifieldHom

@[simp]
theorem reindex_symm_toCoefficientSemifieldHom_comp (e : J ≃ J') :
    (reindex e.symm).toCoefficientSemifieldHom.comp
        (reindex e).toCoefficientSemifieldHom =
      CoefficientSemifieldHom.id (Trop J) := by
  rw [← reindex_symm e]
  exact (reindex e).symm_toCoefficientSemifieldHom_comp_toCoefficientSemifieldHom

/-- Group evaluation is compatible with relabelling the generators. The evaluation is a group
homomorphism, with no assertion that it preserves auxiliary addition. -/
theorem eval_reindex {Q : Type*} [CommGroup Q] (q : J' → Q) (e : J ≃ J') (a : Trop J) :
    freeAbelianCharEquiv.symm q (reindex e a) =
      freeAbelianCharEquiv.symm (q ∘ e) a := by
  induction a using Multiplicative.rec
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

variable {J : Type*}

/-- For finite `J`, a tropical monomial is equivalently an arbitrary tuple of integer
exponents, regarded as one-dimensional tropical numbers. Both operations are componentwise. -/
noncomputable def equivFun [Finite J] : Trop J ≃+* (J → MinTropical ℤ) where
  toEquiv := Multiplicative.toAdd.trans
    (Finsupp.equivFunOnFinite.trans (Equiv.piCongrRight fun _ => MinTropical.tropEquiv))
  map_mul' a b := by
    funext j
    apply MinTropical.untrop_injective
    simp
  map_add' a b := by
    funext j
    apply MinTropical.untrop_injective
    simp

@[simp]
theorem equivFun_apply [Finite J] (a : Trop J) (j : J) :
    equivFun a j = MinTropical.trop (a.toAdd j) :=
  (rfl)

@[simp]
theorem toAdd_equivFun_symm [Finite J] (a : J → MinTropical ℤ) (j : J) :
    ((equivFun (J := J)).symm a).toAdd j = (a j).untrop :=
  (rfl)

/-! ### Checks of the tropical conventions -/

/-- There is only one monomial when there are no generators. -/
example [IsEmpty J] : Unique (Trop J) := inferInstance

/-- Evaluating a Laurent monomial in any commutative group uses integer powers. -/
example {Q : Type*} [CommGroup Q] (q : Fin 2 → Q) :
    freeAbelianCharEquiv.symm q ((generator 0)⁻¹ * generator 1 ^ (2 : ℤ)) =
      (q 0)⁻¹ * q 1 ^ (2 : ℤ) := by
  simp

/-- Transposing two generators exchanges their exponents. -/
example : reindex (Equiv.swap (0 : Fin 2) 1)
    ((generator 0)⁻¹ * generator 1 ^ (2 : ℤ)) =
      generator 0 ^ (2 : ℤ) * (generator 1)⁻¹ := by
  simp [mul_comm]

end Trop

end TauCeti
