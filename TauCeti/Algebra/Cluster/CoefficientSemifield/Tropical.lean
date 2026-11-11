/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Cluster.CoefficientSemifield.Basic
public import TauCeti.Algebra.Group.FreeAbelianCharacter
public import Mathlib.Algebra.Tropical.Basic
public import Mathlib.Data.Finsupp.Basic
public import Mathlib.Order.Preorder.Finsupp

/-!
# Tropical coefficient semifields

The tropical coefficient semifield `Trop J` is the free abelian group on `J`, with auxiliary
addition given by the componentwise minimum of exponents. Its generators correspond to the
frozen variables of a geometric cluster seed; monomials encode the frozen parts of columns of
the extended exchange matrix. The index type may be infinite: every element still has finite
support. Relabelling the generators preserves both operations, and for finite `J` the exponent
presentation agrees with the product of one-dimensional tropical groups.

Group evaluation is supplied by `Trop.charEquiv`, using `TauCeti.freeAbelianCharEquiv`: its
inverse extends any family `J → Q` in a commutative group to a homomorphism `Trop J →* Q`.
Such evaluations
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
def Trop (J : Type*) := Multiplicative (J →₀ ℤ)

namespace Trop

noncomputable section

variable {J J' J'' : Type*}

/-- The exponent vector of a tropical monomial. -/
def toAdd : Trop J ≃ (J →₀ ℤ) := Multiplicative.toAdd

/-- The tropical monomial with a specified exponent vector. -/
def ofAdd : (J →₀ ℤ) ≃ Trop J := toAdd.symm

instance : Inhabited (Trop J) := inferInstanceAs (Inhabited (Multiplicative (J →₀ ℤ)))

instance [DecidableEq J] : DecidableEq (Trop J) :=
  inferInstanceAs (DecidableEq (Multiplicative (J →₀ ℤ)))

instance [IsEmpty J] : Unique (Trop J) :=
  inferInstanceAs (Unique (Multiplicative (J →₀ ℤ)))

@[ext]
theorem ext {a b : Trop J} (h : toAdd a = toAdd b) : a = b := toAdd.injective h

@[simp]
theorem toAdd_ofAdd (a : J →₀ ℤ) : toAdd (ofAdd a) = a := toAdd.apply_symm_apply a

@[simp]
theorem ofAdd_toAdd (a : Trop J) : ofAdd (toAdd a) = a := toAdd.symm_apply_apply a

/-- Tropical multiplication adds exponent vectors. -/
instance : CommGroup (Trop J) := inferInstanceAs (CommGroup (Multiplicative (J →₀ ℤ)))

/-- The auxiliary addition of tropical monomials is the pointwise minimum of exponents. -/
instance : Add (Trop J) := ⟨fun a b => ofAdd (toAdd a ⊓ toAdd b)⟩

@[simp]
theorem toAdd_one : toAdd (1 : Trop J) = 0 := (rfl)

@[simp]
theorem toAdd_mul (a b : Trop J) : toAdd (a * b) = toAdd a + toAdd b := (rfl)

@[simp]
theorem toAdd_inv (a : Trop J) : toAdd a⁻¹ = -toAdd a := (rfl)

@[simp]
theorem toAdd_div (a b : Trop J) : toAdd (a / b) = toAdd a - toAdd b := (rfl)

@[simp]
theorem toAdd_pow (a : Trop J) (n : ℕ) : toAdd (a ^ n) = n • toAdd a := (rfl)

@[simp]
theorem toAdd_zpow (a : Trop J) (n : ℤ) : toAdd (a ^ n) = n • toAdd a := (rfl)

@[simp]
theorem toAdd_add (a b : Trop J) : toAdd (a + b) = toAdd a ⊓ toAdd b :=
  (rfl)

/-- Tropical multiplication distributes over the auxiliary minimum. -/
instance : CoefficientSemifield (Trop J) where
  add_assoc a b c := by
    apply toAdd.injective
    simp only [toAdd_add, inf_assoc]
  add_comm a b := by
    apply toAdd.injective
    simp only [toAdd_add, inf_comm]
  left_distrib a b c := by
    apply toAdd.injective
    ext j
    simp only [toAdd_mul, toAdd_add, Finsupp.add_apply, Finsupp.inf_apply]
    exact (min_add_add_left (toAdd a j) (toAdd b j) (toAdd c j)).symm
  right_distrib a b c := by
    apply toAdd.injective
    ext j
    simp only [toAdd_mul, toAdd_add, Finsupp.add_apply, Finsupp.inf_apply]
    exact (min_add_add_right (toAdd a j) (toAdd b j) (toAdd c j)).symm

@[simp]
theorem ofAdd_inf (a b : J →₀ ℤ) :
    (ofAdd (a ⊓ b) : Trop J) = ofAdd a + ofAdd b :=
  (rfl)

/-- Tropical addition is idempotent. -/
@[simp]
theorem add_self (a : Trop J) : a + a = a := by
  apply toAdd.injective
  simp

/-- The tropical generator with exponent one at `j` and zero elsewhere. -/
noncomputable def generator (j : J) : Trop J := ofAdd (Finsupp.single j 1)

@[simp]
theorem toAdd_generator (j : J) : toAdd (generator j) = Finsupp.single j 1 :=
  (rfl)

/-- Group homomorphisms out of `Trop J` are determined by their generator values. -/
noncomputable def charEquiv {Q : Type*} [CommGroup Q] : (Trop J →* Q) ≃* (J → Q) :=
  freeAbelianCharEquiv

@[simp]
theorem charEquiv_apply {Q : Type*} [CommGroup Q] (χ : Trop J →* Q) (j : J) :
    charEquiv χ j = χ (generator j) := by
  exact freeAbelianCharEquiv_apply χ j

/-- Group evaluation sends each tropical generator to its chosen coordinate. -/
@[simp]
theorem charEquiv_symm_apply_generator {Q : Type*} [CommGroup Q] (q : J → Q) (j : J) :
    charEquiv.symm q (generator j) = q j := by
  rw [← charEquiv_apply, MulEquiv.apply_symm_apply]

@[simp]
theorem charEquiv_symm_apply_ofAdd {Q : Type*} [CommGroup Q] (q : J → Q) (a : J →₀ ℤ) :
    charEquiv.symm q (ofAdd a) = a.prod fun j n => q j ^ n := by
  exact freeAbelianCharEquiv_symm_apply_ofAdd q a

@[ext]
theorem hom_ext {Q : Type*} [CommGroup Q] {χ ψ : Trop J →* Q}
    (h : ∀ j, χ (generator j) = ψ (generator j)) : χ = ψ :=
  charEquiv.injective (funext fun j => by simpa only [charEquiv_apply] using h j)

/-- Distinct indices give distinct tropical generators. -/
theorem generator_injective : Function.Injective (generator : J → Trop J) := by
  intro i j h
  exact Finsupp.single_left_injective (by decide : (1 : ℤ) ≠ 0) (congrArg toAdd h)

@[simp]
theorem generator_inj {i j : J} : generator i = generator j ↔ i = j :=
  generator_injective.eq_iff

@[simp]
theorem generator_ne_one (j : J) : generator j ≠ 1 := by
  classical
  intro h
  have := congrArg (fun a => toAdd a j) h
  simp at this

/-- The minimum of two distinct generators is the multiplicative identity. -/
@[simp]
theorem generator_add_generator_of_ne {i j : J} (h : i ≠ j) : generator i + generator j = 1 := by
  classical
  apply toAdd.injective
  ext k
  by_cases hi : i = k <;> by_cases hj : j = k <;> simp_all

/-- The normalization factor for an inverse generator is that inverse generator itself. -/
@[simp]
theorem inv_generator_add_one (j : J) : (generator j)⁻¹ + 1 = (generator j)⁻¹ := by
  classical
  apply toAdd.injective
  ext k
  by_cases h : j = k <;> simp [h]

/-- The normalization factor is unchanged when its summands are exchanged. -/
@[simp]
theorem one_add_inv_generator (j : J) : 1 + (generator j)⁻¹ = (generator j)⁻¹ := by
  rw [add_comm, inv_generator_add_one]

/-- A positive generator has normalization factor one. -/
@[simp]
theorem generator_add_one (j : J) : generator j + 1 = 1 := by
  classical
  apply toAdd.injective
  ext k
  by_cases h : j = k <;> simp [h]

@[simp]
theorem one_add_generator (j : J) : 1 + generator j = 1 := by
  rw [add_comm, generator_add_one]

/-- Relabelling the tropical generators is an isomorphism of coefficient semifields. -/
noncomputable def reindex (e : J ≃ J') : Trop J ≃+* Trop J' where
  toEquiv := toAdd.trans ((Finsupp.equivCongrLeft e).trans ofAdd)
  map_mul' a b := by
    apply toAdd.injective
    ext j
    simp [Finsupp.equivCongrLeft_apply, Finsupp.equivMapDomain_apply]
  map_add' a b := by
    apply toAdd.injective
    ext j
    simp [Finsupp.equivCongrLeft_apply, Finsupp.equivMapDomain_apply]

@[simp]
theorem reindex_ofAdd (e : J ≃ J') (a : J →₀ ℤ) :
    reindex e (ofAdd a) = ofAdd (Finsupp.equivMapDomain e a) :=
  (rfl)

@[simp]
theorem toAdd_reindex (e : J ≃ J') (a : Trop J) (j : J') :
    toAdd (reindex e a) j = toAdd a (e.symm j) :=
  (rfl)

@[simp]
theorem reindex_generator (e : J ≃ J') (j : J) :
    reindex e (generator j) = generator (e j) := by
  apply toAdd.injective
  exact Finsupp.equivMapDomain_single e j 1

@[simp]
theorem reindex_refl : reindex (Equiv.refl J) = RingEquiv.refl (Trop J) := by
  ext a j
  simp

/-- Relabellings compose in the same order as equivalences of the index sets. -/
@[simp]
theorem reindex_trans (e : J ≃ J') (e' : J' ≃ J'') :
    (reindex e).trans (reindex e') = reindex (e.trans e') := by
  ext a j
  simp

@[simp]
theorem reindex_reindex (e : J ≃ J') (e' : J' ≃ J'') (a : Trop J) :
    reindex e' (reindex e a) = reindex (e.trans e') a := by
  apply toAdd.injective
  ext j
  simp

@[simp]
theorem reindex_symm (e : J ≃ J') : (reindex e).symm = reindex e.symm :=
  (rfl)

/-- Group evaluation is compatible with relabelling the generators. The evaluation is a group
homomorphism, with no assertion that it preserves auxiliary addition. -/
@[simp]
theorem charEquiv_symm_apply_reindex {Q : Type*} [CommGroup Q] (q : J' → Q)
    (e : J ≃ J') (a : Trop J) :
    charEquiv.symm q (reindex e a) = charEquiv.symm (q ∘ e) a := by
  obtain ⟨a, rfl⟩ := ofAdd.surjective a
  simp [Finsupp.prod_equivMapDomain]

end

end Trop

namespace CoefficientSemifield

/-- A linearly ordered additive commutative group, with minimum as auxiliary addition,
is a coefficient semifield. -/
instance instMinTropical {A : Type*} [AddCommGroup A] [LinearOrder A]
    [AddLeftMono A] : CoefficientSemifield (MinTropical A) where
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
  toEquiv := toAdd.trans
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
    equivFun a j = MinTropical.trop (toAdd a j) :=
  (rfl)

@[simp]
theorem toAdd_equivFun_symm [Finite J] (a : J → MinTropical ℤ) (j : J) :
    toAdd ((equivFun (J := J)).symm a) j = (a j).untrop :=
  (rfl)

/-! ### Checks of the tropical conventions -/

/-- The finite-tuple presentation carries the intended coefficient-semifield structure. -/
example : CoefficientSemifield (J → MinTropical ℤ) := inferInstance

/-- There is only one monomial when there are no generators. -/
noncomputable example [IsEmpty J] : Unique (Trop J) := inferInstance

/-- Evaluating a Laurent monomial in any commutative group uses integer powers. -/
example {Q : Type*} [CommGroup Q] (q : Fin 2 → Q) :
    charEquiv.symm q ((generator 0)⁻¹ * generator 1 ^ (2 : ℤ)) =
      (q 0)⁻¹ * q 1 ^ (2 : ℤ) := by
  simp

/-- Transposing two generators exchanges their exponents. -/
example : reindex (Equiv.swap (0 : Fin 2) 1)
    ((generator 0)⁻¹ * generator 1 ^ (2 : ℤ)) =
      generator 0 ^ (2 : ℤ) * (generator 1)⁻¹ := by
  simp [mul_comm]

end Trop

end TauCeti
