/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Cluster.CoefficientSemifield.Basic
public import TauCeti.Algebra.Group.FreeAbelianCharacter
public import TauCeti.Algebra.Tropical.Basic
public import Mathlib.Algebra.Order.Group.Int

/-!
# Tropical coefficient semifields

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
Mathlib's `Finsupp.equivFunOnFinite` and `Equiv` reindexing.
-/

public section

namespace TauCeti

namespace InfTropical

variable {A : Type*}

/-- An inf-semilattice-ordered additive commutative group, with infimum as auxiliary addition
and addition as multiplication, is a coefficient semifield. -/
instance instCoefficientSemifield [AddCommGroup A] [SemilatticeInf A] [IsOrderedAddMonoid A] :
    CoefficientSemifield (InfTropical A) where
  left_distrib := mul_add
  right_distrib := add_mul

end InfTropical

/-- The tropical coefficient semifield on `J`: finitely supported integer exponents,
with multiplication adding exponents and auxiliary addition taking their minimum. -/
abbrev Trop (J : Type*) := InfTropical (J →₀ ℤ)

namespace Trop

variable {J J' J'' : Type*}

/-- The tropical generator with exponent one at `j` and zero elsewhere. -/
noncomputable def generator (j : J) : Trop J := InfTropical.ofAdd (Finsupp.single j 1)

theorem generator_def (j : J) : generator j = InfTropical.ofAdd (Finsupp.single j 1) := (rfl)

@[simp]
theorem toAdd_generator (j : J) : InfTropical.toAdd (generator j) = Finsupp.single j 1 := (rfl)


/-- A homomorphism from the free abelian group of tropical exponents is determined by its values
on the tropical generators. -/
@[ext]
theorem monoidHom_ext {Q : Type*} [Monoid Q] ⦃f g : Trop J →* Q⦄
    (h : ∀ j, f (generator j) = g (generator j)) : f = g :=
  MonoidHom.ext_finsupp_mint h

@[simp]
theorem generator_inj {i j : J} : generator i = generator j ↔ i = j := by
  constructor
  · intro h
    apply (Finsupp.single_left_inj (one_ne_zero : (1 : ℤ) ≠ 0)).mp
    simpa only [toAdd_generator] using congrArg InfTropical.toAdd h
  · exact congrArg generator

@[simp]
theorem generator_ne_one (j : J) : generator j ≠ 1 :=
  fun h => one_ne_zero (Finsupp.single_eq_zero.mp (congrArg InfTropical.toAdd h))

/-- The multiplicative universal property of the free abelian group of tropical exponents. -/
noncomputable def evalEquiv {Q : Type*} [CommGroup Q] : (J → Q) ≃* (Trop J →* Q) :=
  freeAbelianCharEquiv.symm

/-- Evaluate tropical monomials in a commutative group at the given values of the generators. -/
noncomputable def eval {Q : Type*} [CommGroup Q] (q : J → Q) : Trop J →* Q :=
  evalEquiv q

@[simp]
theorem evalEquiv_apply {Q : Type*} [CommGroup Q] (q : J → Q) :
    evalEquiv q = eval q := (rfl)

@[simp]
theorem evalEquiv_symm_apply {Q : Type*} [CommGroup Q] (f : Trop J →* Q) :
    evalEquiv.symm f = (fun j ↦ f (generator j)) := by
  funext j
  rw [evalEquiv]
  exact freeAbelianCharEquiv_apply f j

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

/-- A group homomorphism with prescribed values on the tropical generators equals evaluation. -/
theorem eval_unique {Q : Type*} [CommGroup Q] (f : Trop J →* Q) (q : J → Q)
    (h : ∀ j, f (generator j) = q j) : f = eval q :=
  monoidHom_ext (by simp [h])

@[simp]
theorem eval_comp_generator {Q : Type*} [CommGroup Q] (f : Trop J →* Q) :
    eval (fun j ↦ f (generator j)) = f :=
  monoidHom_ext (by simp)

@[simp]
theorem eval_generator_left : eval generator = MonoidHom.id (Trop J) :=
  eval_comp_generator (MonoidHom.id (Trop J))

/-- A tropical exponent vector is the product of the corresponding integer powers of generators. -/
theorem ofAdd_eq_prod (a : J →₀ ℤ) :
    InfTropical.ofAdd a = a.prod (fun j n ↦ generator j ^ n) := by
  simpa only [eval_generator_left, MonoidHom.id_apply] using (eval_ofAdd (generator : J → Trop J) a)

/-- Evaluation commutes with postcomposition by a group homomorphism;
`comp_eval_apply` is the pointwise form. -/
@[simp]
theorem comp_eval {Q R : Type*} [CommGroup Q] [CommGroup R] (f : Q →* R) (q : J → Q) :
    f.comp (eval q) = eval (f ∘ q) := by
  apply monoidHom_ext
  simp

@[simp]
theorem comp_eval_apply {Q R : Type*} [CommGroup Q] [CommGroup R] (f : Q →* R) (q : J → Q)
    (a : Trop J) : f (eval q a) = eval (f ∘ q) a :=
  DFunLike.congr_fun (comp_eval f q) a

/-- Minimum of two distinct tropical generators is the multiplicative identity. -/
@[simp]
theorem generator_add_generator {i j : J} (h : i ≠ j) : generator i + generator j = 1 := by
  apply InfTropical.ext
  simp only [InfTropical.toAdd_add, InfTropical.toAdd_one, toAdd_generator]
  ext k
  simp only [Finsupp.zero_apply, Finsupp.inf_apply]
  by_cases hi : i = k <;> by_cases hj : j = k <;> simp_all

/-- The normalization factor for a generator is the multiplicative identity. -/
@[simp]
theorem generator_add_one (j : J) : generator j + 1 = 1 := by
  apply InfTropical.ext
  simp

@[simp]
theorem one_add_generator (j : J) : 1 + generator j = 1 := by
  apply InfTropical.ext
  simp

/-- The normalization factor for an inverse generator is that inverse generator itself. -/
@[simp]
theorem inv_generator_add_one (j : J) : (generator j)⁻¹ + 1 = (generator j)⁻¹ :=
  InfTropical.ext <| inf_eq_left.mpr <| neg_nonpos.mpr <| Finsupp.single_nonneg.mpr zero_le_one

@[simp]
theorem one_add_inv_generator (j : J) : 1 + (generator j)⁻¹ = (generator j)⁻¹ := by
  apply InfTropical.ext
  simp

@[simp]
theorem reindex_generator (e : J ≃ J') (j : J) :
    InfTropical.reindex e (generator j) = generator (e j) := by
  rw [generator_def, InfTropical.reindex_ofAdd, Finsupp.equivMapDomain_single, generator_def]

/-- Group evaluation is compatible with relabelling the generators. The evaluation is a group
homomorphism, with no assertion that it preserves auxiliary addition. -/
@[simp]
theorem eval_reindex {Q : Type*} [CommGroup Q] (q : J' → Q) (e : J ≃ J') (a : Trop J) :
    eval q (InfTropical.reindex e a) = eval (q ∘ e) a := by
  obtain ⟨a, rfl⟩ := InfTropical.ofAddEquiv.surjective a
  simp only [InfTropical.ofAddEquiv_apply, InfTropical.reindex_ofAdd, eval_ofAdd]
  exact Finsupp.prod_equivMapDomain e a (fun j n => q j ^ n)

@[simp]
theorem eval_comp_reindex {Q : Type*} [CommGroup Q] (q : J' → Q) (e : J ≃ J') :
    (eval q).comp ((InfTropical.reindex (A := ℤ) e : Trop J ≃+* Trop J') : Trop J →* Trop J') =
      eval (q ∘ e) :=
  MonoidHom.ext (eval_reindex q e)

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

variable {A : Type*}

/-- Infimum becomes supremum after reversing the order of the exponents. -/
example [AddCommGroup A] [Lattice A] [IsOrderedAddMonoid A] :
    CoefficientSemifield (InfTropical Aᵒᵈ) := inferInstance

example [Lattice A] (a b : A) :
    (ofAdd (OrderDual.toDual a) + ofAdd (OrderDual.toDual b)).toAdd =
      OrderDual.toDual (a ⊔ b) := by
  simp

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
