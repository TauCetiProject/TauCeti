/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.MonoidAlgebra.Twisted.Basic

/-!
# Coefficient bars on twisted monoid algebras

A scalar automorphism acts coefficientwise in the distinguished monomial basis. If it
exchanges the two arguments of the factor set on a commutative monoid, the resulting map
reverses multiplication. An involutive scalar automorphism therefore gives a semilinear
anti-involution fixing every normalized monomial. No infinite-order parameter or domain
hypothesis is needed.

This supplies the coefficient bar used for based quantum tori. The scalar compatibility is
an explicit hypothesis: it can fail at finite order even when the twisted algebra exists.

## References

* A. Berenstein and A. Zelevinsky, *Quantum cluster algebras*, §6, equation (6.2).
-/

public section

namespace TauCeti.TwistedMonoidAlgebra

variable {R G : Type*} [CommSemiring R] [Monoid G]
variable {α : G → G → Rˣ} [IsFactorSet α]

/-- Apply a scalar automorphism to the coefficients in the distinguished monomial basis. -/
noncomputable def bar (σ : R ≃+* R) :
    twistedMonoidAlgebra R G α ≃+ twistedMonoidAlgebra R G α :=
  (basis R G α).repr.toAddEquiv.trans
    ((Finsupp.mapRange.addEquiv σ.toAddEquiv).trans (basis R G α).repr.symm.toAddEquiv)

/-- The monomial coefficients of the bar are obtained by applying the scalar automorphism. -/
@[simp]
theorem repr_bar (σ : R ≃+* R) (x : twistedMonoidAlgebra R G α) (g : G) :
    (basis R G α).repr (bar σ x) g = σ ((basis R G α).repr x g) := by
  simp [bar]

/-- The coefficient bar is semilinear with respect to its scalar automorphism. -/
@[simp]
theorem bar_smul (σ : R ≃+* R) (r : R) (x : twistedMonoidAlgebra R G α) :
    bar σ (r • x) = σ r • bar σ x := by
  apply (basis R G α).repr.injective
  ext g
  simp [map_mul]

/-- Every normalized monomial is fixed by the coefficient bar. -/
@[simp]
theorem bar_of (σ : R ≃+* R) (g : G) :
    bar σ (of g : twistedMonoidAlgebra R G α) = of g := by
  apply (basis R G α).repr.injective
  have hb : (basis R G α).repr (of g) = Finsupp.single g 1 := by
    rw [← basis_apply R G α g]
    exact (basis R G α).repr_self g
  ext h
  simp only [repr_bar, hb]
  classical
  by_cases hgh : g = h <;> simp [hgh]

@[simp]
theorem bar_one (σ : R ≃+* R) : bar σ (1 : twistedMonoidAlgebra R G α) = 1 := by
  simpa only [of_one] using bar_of (α := α) σ 1

/-- The identity scalar automorphism induces the identity coefficient bar. -/
@[simp]
theorem bar_refl : bar (α := α) (RingEquiv.refl R) = AddEquiv.refl _ := by
  apply AddEquiv.ext
  intro x
  apply (basis R G α).repr.injective
  ext g
  simp

/-- Inverting scalar transport inverts its coefficient bar. -/
@[simp]
theorem bar_symm (σ : R ≃+* R) : (bar (α := α) σ).symm = bar σ.symm := by
  apply AddEquiv.ext
  intro x
  apply (bar σ).injective
  apply (basis R G α).repr.injective
  ext g
  simp only [AddEquiv.apply_symm_apply, repr_bar, RingEquiv.apply_symm_apply]

/-- Inverse scalar transport cancels forward transport, without an involutivity assumption. -/
@[simp]
theorem bar_symm_bar (σ : R ≃+* R) (x : twistedMonoidAlgebra R G α) :
    bar σ.symm (bar σ x) = x := by
  simpa only [bar_symm] using (bar (α := α) σ).symm_apply_apply x

/-- Forward scalar transport cancels inverse transport. -/
@[simp]
theorem bar_bar_symm (σ : R ≃+* R) (x : twistedMonoidAlgebra R G α) :
    bar σ (bar σ.symm x) = x := by
  simpa only [bar_symm] using (bar (α := α) σ).apply_symm_apply x

/-- Successive scalar transports induce the composite coefficient bar. -/
@[simp]
theorem bar_trans (σ τ : R ≃+* R) :
    (bar (α := α) σ).trans (bar τ) = bar (σ.trans τ) := by
  apply AddEquiv.ext
  intro x
  apply (basis R G α).repr.injective
  ext g
  simp only [AddEquiv.trans_apply, repr_bar, RingEquiv.trans_apply]

/-- Pointwise composition of coefficient bars follows the scalar composition order. -/
theorem bar_apply_bar (σ τ : R ≃+* R) (x : twistedMonoidAlgebra R G α) :
    bar τ (bar σ x) = bar (σ.trans τ) x :=
  DFunLike.congr_fun (bar_trans σ τ) x

/-- Coefficient transport restricts to the specified scalar automorphism. -/
@[simp]
theorem bar_algebraMap (σ : R ≃+* R) (r : R) :
    bar σ (algebraMap R (twistedMonoidAlgebra R G α) r) =
      algebraMap R _ (σ r) := by
  simp only [Algebra.algebraMap_eq_smul_one, bar_smul, bar_one]

/-- Natural-number scalars are fixed by every coefficient bar. -/
@[simp]
theorem bar_natCast (σ : R ≃+* R) (n : ℕ) :
    bar σ (n : twistedMonoidAlgebra R G α) = n :=
  map_natCast' (bar σ) (bar_one σ) n

/-- Numeral scalars are fixed by every coefficient bar. -/
@[simp]
theorem bar_ofNat (σ : R ≃+* R) (n : ℕ) [n.AtLeastTwo] :
    bar σ (ofNat(n) : twistedMonoidAlgebra R G α) = ofNat(n) :=
  bar_natCast σ n

/-- The coefficient bar as a semilinear map for the scalar automorphism. -/
noncomputable def barLinearMap (σ : R ≃+* R) :
    twistedMonoidAlgebra R G α →ₛₗ[(σ : R →+* R)] twistedMonoidAlgebra R G α where
  toFun := bar σ
  map_add' := map_add (bar σ)
  map_smul' := bar_smul σ

@[simp]
theorem barLinearMap_apply (σ : R ≃+* R) (x : twistedMonoidAlgebra R G α) :
    barLinearMap σ x = bar σ x := by rfl

/-- A semilinear map intertwines an ordinary linear map with the bar precisely when the two
maps agree on the normalized monomials. This includes uniqueness by taking the linear identity. -/
theorem eq_comp_barLinearMap_iff (σ : R ≃+* R) {M : Type*}
    [AddCommMonoid M] [Module R M]
    (f : twistedMonoidAlgebra R G α →ₛₗ[(σ : R →+* R)] M)
    (l : twistedMonoidAlgebra R G α →ₗ[R] M) :
    f = l.comp (barLinearMap σ) ↔ ∀ g, f (of g) = l (of g) := by
  constructor
  · intro h g
    rw [h]
    simp
  · intro h
    apply (basis R G α).ext
    intro g
    simpa only [basis_apply, LinearMap.comp_apply, barLinearMap_apply, bar_of] using h g

/-- An involutive scalar automorphism gives an involutive coefficient bar. -/
theorem bar_involutive (σ : R ≃+* R) (hσ : Function.Involutive σ) :
    Function.Involutive (bar (α := α) σ) := by
  intro x
  apply (basis R G α).repr.injective
  ext g
  simp only [repr_bar]
  exact hσ _

/-- Applying an involutive bar twice recovers the original element. -/
@[simp]
theorem bar_bar (σ : R ≃+* R) (hσ : Function.Involutive σ)
    (x : twistedMonoidAlgebra R G α) : bar σ (bar σ x) = x :=
  bar_involutive σ hσ x

section Ring

variable {R G : Type*} [CommRing R] [Monoid G]
variable {α : G → G → Rˣ} [IsFactorSet α]

/-- Integer scalars are fixed by every coefficient bar over a ring. -/
@[simp]
theorem bar_intCast (σ : R ≃+* R) (z : ℤ) :
    bar σ (z : twistedMonoidAlgebra R G α) = z :=
  map_intCast' (bar σ) (bar_one σ) z

end Ring

section Commutative

variable {R G : Type*} [CommSemiring R] [CommMonoid G]
variable {α : G → G → Rˣ} [IsFactorSet α]

/-- If the scalar automorphism reverses the factor set, the coefficient bar reverses products. -/
theorem bar_mul (σ : R ≃+* R) (hα : ∀ g h, σ (α g h : R) = (α h g : R))
    (x y : twistedMonoidAlgebra R G α) : bar σ (x * y) = bar σ y * bar σ x := by
  conv_lhs =>
    rw [← (basis R G α).linearCombination_repr x,
      ← (basis R G α).linearCombination_repr y]
  conv_rhs =>
    rw [← (basis R G α).linearCombination_repr x,
      ← (basis R G α).linearCombination_repr y]
  simp only [Finsupp.linearCombination_apply, Finsupp.sum, basis_apply, Finset.sum_mul,
    Finset.mul_sum, map_sum, bar_smul,
    bar_of, smul_mul_smul_comm, of_mul_of, smul_smul, map_mul, hα]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro g _hg
  apply Finset.sum_congr rfl
  intro h _hh
  rw [mul_comm g h]
  congr 1
  ac_rfl

/-- An anti-multiplicative coefficient bar is an equivalence with the opposite semiring.
Its inverse uses the inverse scalar automorphism, not an assumed scalar involution. -/
noncomputable def barRingEquiv (σ : R ≃+* R)
    (hα : ∀ g h, σ (α g h : R) = (α h g : R)) :
    twistedMonoidAlgebra R G α ≃+* (twistedMonoidAlgebra R G α)ᵐᵒᵖ where
  toFun x := MulOpposite.op (bar σ x)
  invFun y := bar σ.symm y.unop
  left_inv x := bar_symm_bar σ x
  right_inv y := by
    apply MulOpposite.unop_injective
    exact bar_bar_symm σ y.unop
  map_mul' x y := by
    rw [bar_mul σ hα, MulOpposite.op_mul]
  map_add' x y := by
    rw [map_add, MulOpposite.op_add]

@[simp]
theorem barRingEquiv_apply (σ : R ≃+* R)
    (hα : ∀ g h, σ (α g h : R) = (α h g : R))
    (x : twistedMonoidAlgebra R G α) :
    barRingEquiv σ hα x = MulOpposite.op (bar σ x) := by rfl

@[simp]
theorem barRingEquiv_symm_apply (σ : R ≃+* R)
    (hα : ∀ g h, σ (α g h : R) = (α h g : R))
    (y : (twistedMonoidAlgebra R G α)ᵐᵒᵖ) :
    (barRingEquiv σ hα).symm y = bar σ.symm y.unop := by rfl

/-- An anti-multiplicative coefficient bar preserves powers of a single element. -/
@[simp]
theorem bar_pow (σ : R ≃+* R) (hα : ∀ g h, σ (α g h : R) = (α h g : R))
    (x : twistedMonoidAlgebra R G α) (n : ℕ) : bar σ (x ^ n) = bar σ x ^ n := by
  apply MulOpposite.op_injective
  simpa only [barRingEquiv_apply, MulOpposite.op_pow] using (barRingEquiv σ hα).map_pow x n

end Commutative

end TauCeti.TwistedMonoidAlgebra
