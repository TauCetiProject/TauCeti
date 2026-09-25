/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.F4.ShortRoot.Modular.Exponential
public import TauCeti.Algebra.Lie.F4.ShortRoot.Quotient.Pinning.First
public import TauCeti.Algebra.Lie.F4.ShortRoot.Quotient.Pinning.DividedSquare

/-!
# Integral root exponentials on the modular F₄ quotient

This file transports the integral Chevalley root exponential through reduction modulo two and the
quotient by the modular short-root ideal.  The resulting formula is valid over every commutative
`ZMod 2`-algebra.  Its three terms are stated using the genuine integral adjoint action, so the
concrete quotient column formulas can identify them without choosing representatives.

## References

* R. W. Carter, *Simple Groups of Lie Type*, §4.4, for Chevalley root exponentials.
-/

public section

namespace TauCeti.DynkinType

open TauCeti.F4ShortRoot
open _root_.LieAlgebra _root_.LieAlgebra.IsKilling LieModule Module
open scoped TensorProduct

noncomputable section

private theorem quadraticPolynomial_congr
    {A M : Type*} [CommRing A] [AddCommGroup M] [Module A M]
    {x₀ x₁ x₂ y₀ y₁ y₂ : M} (t : A)
    (h₀ : x₀ = y₀) (h₁ : x₁ = y₁) (h₂ : x₂ = y₂) :
    x₀ + t • x₁ + t ^ 2 • x₂ = y₀ + t • y₁ + t ^ 2 • y₂ := by
  subst y₀
  subst y₁
  subst y₂
  rfl

private theorem map_quadraticPolynomial
    {A M N : Type*} [CommRing A] [AddCommGroup M] [Module A M]
    [AddCommGroup N] [Module A N] (f : M →ₗ[A] N) (t : A) (x₀ x₁ x₂ : M) :
    f (x₀ + t • x₁ + t ^ 2 • x₂) =
      f x₀ + t • f x₁ + t ^ 2 • f x₂ := by
  rw [map_add, map_add, map_smul, map_smul]

/-- A short signed-simple source has parameter exponent two. -/
theorem isogenyExponent_eq_two_of_short (k : Fin 4 ⊕ Fin 4)
    (hk : f4Length (f4SignedSimpleRootIndex k) = 1) :
    isogenyExponent k = 2 := by
  cases k <;> simp only [f4SignedSimpleRootIndex_inl, f4SignedSimpleRootIndex_inr,
    f4Length_opposite] at hk <;> rw [f4Length_def] at hk <;> decide +revert

/-- A long signed-simple source has parameter exponent one. -/
theorem isogenyExponent_eq_one_of_long (k : Fin 4 ⊕ Fin 4)
    (hk : f4Length (f4SignedSimpleRootIndex k) = 2) :
    isogenyExponent k = 1 := by
  cases k <;> simp only [f4SignedSimpleRootIndex_inl, f4SignedSimpleRootIndex_inr,
    f4Length_opposite] at hk <;> rw [f4Length_def] at hk <;> decide +revert

/-- A long signed-simple root has zero divided-square action on the short-root ideal. -/
theorem f4ShortRootIdealDividedSquareColumn_eq_zero_of_long
    (k : Fin 4 ⊕ Fin 4)
    (hk : f4Length (f4SignedSimpleRootIndex k) = 2)
    (a : Fin 26) :
    f4ShortRootIdealDividedSquareColumn k a = 0 := by
  rw [f4ShortRootIdealDividedSquareColumn_eq]
  have hc := f4DividedSquareCoeff_mod_two_eq_zero_of_long k hk a
  calc
    (f4DividedSquareCoeff k a : ZMod 2) •
        f4ShortRootLieIdealBasis (f4DividedSquareTarget k a) =
      (0 : ZMod 2) • f4ShortRootLieIdealBasis (f4DividedSquareTarget k a) :=
        congrArg (fun c : ZMod 2 =>
          c • f4ShortRootLieIdealBasis (f4DividedSquareTarget k a)) hc
    _ = 0 := zero_smul _ _

/-- Reversal exchanges a short signed-simple source with a long one. -/
theorem f4Length_isogenyReverse_eq_two_of_short (k : Fin 4 ⊕ Fin 4)
    (hk : f4Length (f4SignedSimpleRootIndex k) = 1) :
  f4Length (f4SignedSimpleRootIndex (isogenyReverse k)) = 2 := by
  rw [← f4SpecialIsogenyIndexEquiv_f4SignedSimpleRootIndex]
  exact (f4Length_f4SpecialIsogenyIndexEquiv_eq_two_iff _).2 hk

/-- Reduction modulo two followed by the quotient by the modular short-root ideal, after an
arbitrary scalar extension. -/
noncomputable def f4ShortRootBaseChangeQuotient
    {A : Type*} [CommRing A] [Algebra (ZMod 2) A] :
    A ⊗[ℤ] f4ChevalleyLieLattice →ₗ[A]
      A ⊗[ZMod 2] (f4ModularChevalleyLieAlgebra ⧸ f4ShortRootSubspace) :=
  (f4ShortRootSubspace.mkQ.baseChange A).comp
    (TauCeti.cancelBaseChange ℤ (ZMod 2) A
      f4ChevalleyLieLattice).symm.toLinearMap

/-- Evaluation of the scalar-extended quotient map through scalar-tower cancellation. -/
theorem f4ShortRootBaseChangeQuotient_apply
    {A : Type*} [CommRing A] [Algebra (ZMod 2) A]
    (x : A ⊗[ℤ] f4ChevalleyLieLattice) :
    f4ShortRootBaseChangeQuotient x =
      f4ShortRootSubspace.mkQ.baseChange A
        ((TauCeti.cancelBaseChange ℤ (ZMod 2) A
          f4ChevalleyLieLattice).symm x) := by rfl

/-- The scalar-extended quotient map on a pure integral tensor. -/
theorem f4ShortRootBaseChangeQuotient_tmul
    {A : Type*} [CommRing A] [Algebra (ZMod 2) A]
    (a : A) (x : f4ChevalleyLieLattice) :
    f4ShortRootBaseChangeQuotient (a ⊗ₜ[ℤ] x) =
      a ⊗ₜ[ZMod 2] f4ShortRootSubspace.mkQ (1 ⊗ₜ[ℤ] x) := by
  -- Unfold the composite quotient map to apply scalar-tower cancellation on a pure tensor.
  change (f4ShortRootSubspace.mkQ.baseChange A)
      ((TauCeti.cancelBaseChange ℤ (ZMod 2) A
        f4ChevalleyLieLattice).symm (a ⊗ₜ[ℤ] x)) = _
  let q := f4ShortRootSubspace.mkQ.baseChange A
  let e := TauCeti.cancelBaseChange ℤ (ZMod 2) A
    f4ChevalleyLieLattice
  calc
    q (e.symm (a ⊗ₜ[ℤ] x)) = q (a ⊗ₜ[ZMod 2] (1 ⊗ₜ[ℤ] x)) :=
      congrArg q (TauCeti.cancelBaseChange_symm_tmul
        ℤ (ZMod 2) A f4ChevalleyLieLattice a x)
    _ = _ := LinearMap.baseChange_tmul f4ShortRootSubspace.mkQ a (1 ⊗ₜ[ℤ] x)

/-- After passing to the quotient, the root exponential has its three-term integral
divided-power polynomial on every pure tensor. -/
theorem f4ShortRootBaseChangeQuotient_rootExponential_tmul
    {A : Type*} [CommRing A] [Algebra (ZMod 2) A]
    (k : Fin 4 ⊕ Fin 4) (t : A) (x : f4ChevalleyLieLattice) :
    f4ShortRootBaseChangeQuotient (f4RootExponential k t ((1 : A) ⊗ₜ[ℤ] x)) =
      (1 : A) ⊗ₜ[ZMod 2] f4ShortRootSubspace.mkQ (1 ⊗ₜ[ℤ] x) +
        t • ((1 : A) ⊗ₜ[ZMod 2]
          f4ShortRootSubspace.mkQ (1 ⊗ₜ[ℤ] ⁅f4IntegralRootVector (f4SignedSimpleRootIndex k), x⁆)) +
        t ^ 2 • ((1 : A) ⊗ₜ[ZMod 2]
          f4ShortRootSubspace.mkQ
            (1 ⊗ₜ[ℤ] f4IntegralDividedAdjointSquare k x)) := by
  let q := f4ShortRootBaseChangeQuotient (A := A)
  exact (congrArg q (f4RootExponential_tmul k t x)).trans
    ((map_quadraticPolynomial q t _ _ _).trans
      (quadraticPolynomial_congr t
        (f4ShortRootBaseChangeQuotient_tmul (1 : A) x)
        (f4ShortRootBaseChangeQuotient_tmul (1 : A)
          (⁅f4IntegralRootVector (f4SignedSimpleRootIndex k), x⁆))
        (f4ShortRootBaseChangeQuotient_tmul (1 : A) (f4IntegralDividedAdjointSquare k x))))

/-- The canonical integral lift of a quotient basis coordinate: a long root vector, or the long
simple coroot `h₁`, `h₀` at coordinates `12`, `13`. -/
noncomputable def f4IntegralShortRootQuotientLift (a : Fin 26) :
    f4ChevalleyLieLattice :=
  match f4ShortRootWeightIndexEquiv a with
  | Sum.inl i => f4IntegralRootVector (f4SpecialIsogenyIndexEquiv i)
  | Sum.inr j =>
      f4IntegralSimpleCoroot (Fin.cast rank_F4.symm (![1, 0] j : Fin 4))

/-- Reduction modulo two of the canonical integral lift is the canonical ambient modular lift. -/
theorem f4IntegralShortRootQuotientLift_modular (a : Fin 26) :
    1 ⊗ₜ[ℤ] f4IntegralShortRootQuotientLift a =
      f4ShortRootQuotientLift a := by
  rw [f4ShortRootQuotientLift_eq_basis]
  rcases h : f4ShortRootWeightIndexEquiv a with i | j
  · have ha : a = f4ShortRootWeightIndexEquiv.symm (Sum.inl i) := by
      apply f4ShortRootWeightIndexEquiv.injective
      rw [h, Equiv.apply_symm_apply]
    subst a
    simp only [f4IntegralShortRootQuotientLift, Equiv.apply_symm_apply,
      f4LongRootBasisCoordinate_symm_inl,
      f4ModularChevalleyBasis_inl_eq_rootVector,
      f4PinnedRootIndex_f4KillingRootLabel]
    exact (f4ModularRootVector_eq _).symm
  · have ha : a = f4ShortRootWeightIndexEquiv.symm (Sum.inr j) := by
      apply f4ShortRootWeightIndexEquiv.injective
      rw [h, Equiv.apply_symm_apply]
    subst a
    have hj : j = 0 ∨ j = 1 := by omega
    rcases hj with rfl | rfl
    · rw [f4ShortRootWeightIndexEquiv_symm_apply_inr_zero,
        f4ModularChevalleyBasis_longRootBasisCoordinate_twelve]
      simpa [f4IntegralShortRootQuotientLift] using
        (f4ModularSimpleCoroot_eq
          (Fin.cast rank_F4.symm (1 : Fin 4))).symm
    · rw [f4ShortRootWeightIndexEquiv_symm_apply_inr_one,
        f4ModularChevalleyBasis_longRootBasisCoordinate_thirteen]
      simpa [f4IntegralShortRootQuotientLift] using
        (f4ModularSimpleCoroot_eq
          (Fin.cast rank_F4.symm (0 : Fin 4))).symm

/-- Reduction of the canonical integral lift represents the corresponding quotient basis
coordinate. -/
theorem f4IntegralShortRootQuotientLift_mkQ (a : Fin 26) :
    f4ShortRootSubspace.mkQ (1 ⊗ₜ[ℤ] f4IntegralShortRootQuotientLift a) =
      f4ShortRootQuotientBasis a := by
  rw [f4IntegralShortRootQuotientLift_modular,
    f4ShortRootSubspace_mkQ_quotientLift]

/-- The bracket of an integral root vector with a canonical lift reduces to the first-order
quotient column. -/
theorem f4IntegralRootBracket_quotientLift_mkQ
    (k : Fin 4 ⊕ Fin 4) (a : Fin 26) :
    f4ShortRootSubspace.mkQ
        (1 ⊗ₜ[ℤ] ⁅f4IntegralRootVector (f4SignedSimpleRootIndex k),
          f4IntegralShortRootQuotientLift a⁆) =
      f4ShortRootQuotientFirstColumn k a := by
  let x := f4IntegralShortRootQuotientLift a
  let q := f4ShortRootSubspace.mkQ
  have hbracket : ⁅f4ModularRootVector (f4SignedSimpleRootIndex k),
        (1 : ZMod 2) ⊗ₜ[ℤ] x⁆ =
      (1 : ZMod 2) ⊗ₜ[ℤ] ⁅f4IntegralRootVector (f4SignedSimpleRootIndex k), x⁆ := by
    rw [f4ModularRootVector_eq, LieAlgebra.ExtendScalars.bracket_tmul, one_mul]
  calc
    q (1 ⊗ₜ[ℤ] ⁅f4IntegralRootVector (f4SignedSimpleRootIndex k), x⁆) =
        q ⁅f4ModularRootVector (f4SignedSimpleRootIndex k), 1 ⊗ₜ[ℤ] x⁆ :=
      congrArg q hbracket.symm
    _ = q ⁅f4ModularRootVector (f4SignedSimpleRootIndex k),
          f4ShortRootQuotientLift a⁆ :=
      congrArg q (congrArg
        (fun z => ⁅f4ModularRootVector (f4SignedSimpleRootIndex k), z⁆)
        (f4IntegralShortRootQuotientLift_modular a))
    _ = f4ShortRootQuotientFirstColumn k a :=
      (f4ShortRootQuotientFirstColumn_eq k a).symm

/-- The reduced second integral divided power on a canonical lift is the named quotient
divided-square column. -/
theorem f4IntegralDividedAdjointSquare_quotientLift_mkQ
    (k : Fin 4 ⊕ Fin 4) (a : Fin 26) :
    f4ShortRootSubspace.mkQ
        (1 ⊗ₜ[ℤ] f4IntegralDividedAdjointSquare k
          (f4IntegralShortRootQuotientLift a)) =
      f4ShortRootQuotientDividedSquareColumn k a := by
  let x := f4IntegralShortRootQuotientLift a
  let q := f4ShortRootSubspace.mkQ
  calc
    q (1 ⊗ₜ[ℤ] f4IntegralDividedAdjointSquare k x) =
        q (f4ModularDividedAdjointSquare k (1 ⊗ₜ[ℤ] x)) :=
      congrArg q (f4ModularDividedAdjointSquare_tmul k x).symm
    _ = q (f4ModularDividedAdjointSquare k (f4ShortRootQuotientLift a)) :=
      congrArg q (congrArg (f4ModularDividedAdjointSquare k)
        (f4IntegralShortRootQuotientLift_modular a))
    _ = f4ShortRootQuotientDividedSquareColumn k a :=
      (f4ShortRootQuotientDividedSquareColumn_eq k a).symm

/-- On every canonical quotient-basis lift, the arbitrary-scalar root exponential is the
three-term integral divided-power polynomial, with constant term normalized to the quotient
basis.  The two remaining terms retain their integral lifts until the concrete quotient-column
identification is applied. -/
theorem f4ShortRootBaseChangeQuotient_rootExponential_integralShortRootQuotientLift
    {A : Type*} [CommRing A] [Algebra (ZMod 2) A]
    (k : Fin 4 ⊕ Fin 4) (t : A) (a : Fin 26) :
    f4ShortRootBaseChangeQuotient
        (f4RootExponential k t
          ((1 : A) ⊗ₜ[ℤ] f4IntegralShortRootQuotientLift a)) =
      (1 : A) ⊗ₜ[ZMod 2] f4ShortRootQuotientBasis a +
        t • ((1 : A) ⊗ₜ[ZMod 2]
          f4ShortRootSubspace.mkQ
            (1 ⊗ₜ[ℤ] ⁅f4IntegralRootVector (f4SignedSimpleRootIndex k),
              f4IntegralShortRootQuotientLift a⁆)) +
        t ^ 2 • ((1 : A) ⊗ₜ[ZMod 2]
          f4ShortRootSubspace.mkQ
            (1 ⊗ₜ[ℤ] f4IntegralDividedAdjointSquare k
              (f4IntegralShortRootQuotientLift a))) := by
  have hpoly := f4ShortRootBaseChangeQuotient_rootExponential_tmul
    (A := A) k t (f4IntegralShortRootQuotientLift a)
  have hzero :
      (1 : A) ⊗ₜ[ZMod 2]
          f4ShortRootSubspace.mkQ (1 ⊗ₜ[ℤ] f4IntegralShortRootQuotientLift a) =
        (1 : A) ⊗ₜ[ZMod 2] f4ShortRootQuotientBasis a :=
    congrArg (fun z => (1 : A) ⊗ₜ[ZMod 2] z)
      (f4IntegralShortRootQuotientLift_mkQ a)
  exact hpoly.trans (quadraticPolynomial_congr t hzero rfl rfl)

/-- The quotient of the genuine integral root exponential on a canonical lift is its canonical
quadratic column polynomial, over every commutative algebra of characteristic two. -/
theorem f4ShortRootBaseChangeQuotient_rootExponential_quotientColumns
    {A : Type*} [CommRing A] [Algebra (ZMod 2) A]
    (k : Fin 4 ⊕ Fin 4) (t : A) (a : Fin 26) :
    f4ShortRootBaseChangeQuotient
        (f4RootExponential k t
          ((1 : A) ⊗ₜ[ℤ] f4IntegralShortRootQuotientLift a)) =
      (1 : A) ⊗ₜ[ZMod 2] f4ShortRootQuotientBasis a +
        t • ((1 : A) ⊗ₜ[ZMod 2] f4ShortRootQuotientFirstColumn k a) +
        t ^ 2 • ((1 : A) ⊗ₜ[ZMod 2]
          f4ShortRootQuotientDividedSquareColumn k a) := by
  have h := f4ShortRootBaseChangeQuotient_rootExponential_integralShortRootQuotientLift
    (A := A) k t a
  have h₁ := congrArg (fun z => (1 : A) ⊗ₜ[ZMod 2] z)
    (f4IntegralRootBracket_quotientLift_mkQ k a)
  have h₂ := congrArg (fun z => (1 : A) ⊗ₜ[ZMod 2] z)
    (f4IntegralDividedAdjointSquare_quotientLift_mkQ k a)
  exact h.trans (quadraticPolynomial_congr t rfl h₁ h₂)

/-- Scalar extension of the pinned coordinate equivalence from the modular quotient to the
short-root ideal. -/
noncomputable def f4ShortRootQuotientToIdealBaseChange
    {A : Type*} [CommRing A] [Algebra (ZMod 2) A] :
    A ⊗[ZMod 2] (f4ModularChevalleyLieAlgebra ⧸ f4ShortRootSubspace) →ₗ[A]
      A ⊗[ZMod 2] f4ShortRootLieIdeal :=
  f4ShortRootQuotientToIdealEquiv.toLinearMap.baseChange A

@[simp] theorem f4ShortRootQuotientToIdealBaseChange_tmul
    {A : Type*} [CommRing A] [Algebra (ZMod 2) A]
    (x : f4ModularChevalleyLieAlgebra ⧸ f4ShortRootSubspace) :
    f4ShortRootQuotientToIdealBaseChange ((1 : A) ⊗ₜ[ZMod 2] x) =
      (1 : A) ⊗ₜ[ZMod 2] f4ShortRootQuotientToIdealEquiv x := by
  exact LinearMap.baseChange_tmul f4ShortRootQuotientToIdealEquiv.toLinearMap 1 x

/-- The canonical quotient-column polynomial after transport to the short-root ideal. -/
noncomputable def f4ShortRootTransportedQuotientPolynomial
    {A : Type*} [CommRing A] [Algebra (ZMod 2) A]
    (k : Fin 4 ⊕ Fin 4) (t : A) (a : Fin 26) :
    A ⊗[ZMod 2] f4ShortRootLieIdeal :=
    (1 : A) ⊗ₜ[ZMod 2] f4ShortRootLieIdealBasis a +
      t • ((1 : A) ⊗ₜ[ZMod 2]
        f4ShortRootQuotientToIdealEquiv
          (f4ShortRootQuotientFirstColumn k a)) +
      t ^ 2 • ((1 : A) ⊗ₜ[ZMod 2]
        f4ShortRootQuotientToIdealEquiv
          (f4ShortRootQuotientDividedSquareColumn k a))

/-- The target root exponential on a canonical basis vector, written using its named columns. -/
theorem f4ShortRootExponential_basis_apply
    {A : Type*} [CommRing A] [Algebra (ZMod 2) A]
    (k : Fin 4 ⊕ Fin 4) (t : A) (a : Fin 26) :
    f4ShortRootExponential k t
        ((1 : A) ⊗ₜ[ZMod 2] f4ShortRootLieIdealBasis a) =
      (1 : A) ⊗ₜ[ZMod 2] f4ShortRootLieIdealBasis a +
        t • ((1 : A) ⊗ₜ[ZMod 2] f4ShortRootIdealFirstColumn k a) +
        t ^ 2 • ((1 : A) ⊗ₜ[ZMod 2]
          f4ShortRootIdealDividedSquareColumn k a) := by
  have h := f4ShortRootExponential_apply (A := A) k t
    (f4ShortRootLieIdealBasis a)
  have h₁ := congrArg (fun z => (1 : A) ⊗ₜ[ZMod 2] z)
    (f4ShortRootIdealFirstColumn_apply k a).symm
  have h₂ := congrArg (fun z => (1 : A) ⊗ₜ[ZMod 2] z)
    (f4ShortRootIdealDividedSquareColumn_apply k a).symm
  exact h.trans (quadraticPolynomial_congr t rfl h₁ h₂)

private theorem f4ShortRootTransportedQuotientPolynomial_eq_exponential_of_short
    {A : Type*} [CommRing A] [Algebra (ZMod 2) A]
    (k : Fin 4 ⊕ Fin 4) (t : A) (a : Fin 26)
    (hk : f4Length (f4SignedSimpleRootIndex k) = 1) :
    f4ShortRootTransportedQuotientPolynomial k t a =
      f4ShortRootExponential (isogenyReverse k) (t ^ isogenyExponent k)
        ((1 : A) ⊗ₜ[ZMod 2] f4ShortRootLieIdealBasis a) := by
  let u₀ := (1 : A) ⊗ₜ[ZMod 2] f4ShortRootLieIdealBasis a
  let i₁ := (1 : A) ⊗ₜ[ZMod 2] f4ShortRootIdealFirstColumn (isogenyReverse k) a
  have hleft : f4ShortRootTransportedQuotientPolynomial k t a = u₀ + t ^ 2 • i₁ := by
    unfold f4ShortRootTransportedQuotientPolynomial
    have h := quadraticPolynomial_congr t (rfl : u₀ = u₀)
      (congrArg (fun z => (1 : A) ⊗ₜ[ZMod 2] z)
        (f4ShortRootQuotientToIdealEquiv_firstColumn_eq_zero_of_short k hk a))
      (congrArg (fun z => (1 : A) ⊗ₜ[ZMod 2] z)
        (f4ShortRootQuotientToIdealEquiv_dividedSquare_eq_firstColumn_of_short k hk a))
    simpa only [TensorProduct.tmul_zero, smul_zero, add_zero] using h
  have hright : f4ShortRootExponential (isogenyReverse k) (t ^ 2) u₀ =
      u₀ + t ^ 2 • i₁ := by
    have h := (f4ShortRootExponential_basis_apply (A := A) (isogenyReverse k) (t ^ 2) a).trans
      (quadraticPolynomial_congr (t ^ 2) (rfl : u₀ = u₀) (rfl : i₁ = i₁)
        (congrArg (fun z => (1 : A) ⊗ₜ[ZMod 2] z)
          (f4ShortRootIdealDividedSquareColumn_eq_zero_of_long (isogenyReverse k)
            (f4Length_isogenyReverse_eq_two_of_short k hk) a)))
    simpa only [TensorProduct.tmul_zero, smul_zero, add_zero] using h
  exact hleft.trans (hright.symm.trans (congrArg
    (fun u => f4ShortRootExponential (isogenyReverse k) u u₀)
    (congrArg (t ^ ·) (isogenyExponent_eq_two_of_short k hk)).symm))

private theorem f4ShortRootTransportedQuotientPolynomial_eq_exponential_of_long
    {A : Type*} [CommRing A] [Algebra (ZMod 2) A]
    (k : Fin 4 ⊕ Fin 4) (t : A) (a : Fin 26)
    (hk : f4Length (f4SignedSimpleRootIndex k) = 2) :
    f4ShortRootTransportedQuotientPolynomial k t a =
      f4ShortRootExponential (isogenyReverse k) (t ^ isogenyExponent k)
        ((1 : A) ⊗ₜ[ZMod 2] f4ShortRootLieIdealBasis a) := by
  have hexp : t ^ isogenyExponent k = t := by
    rw [isogenyExponent_eq_one_of_long k hk, pow_one]
  have htarget := f4ShortRootExponential_basis_apply (A := A) (isogenyReverse k) t a
  have hcoeff : f4ShortRootTransportedQuotientPolynomial k t a =
      (1 : A) ⊗ₜ[ZMod 2] f4ShortRootLieIdealBasis a +
        t • ((1 : A) ⊗ₜ[ZMod 2] f4ShortRootIdealFirstColumn (isogenyReverse k) a) +
        t ^ 2 • ((1 : A) ⊗ₜ[ZMod 2]
          f4ShortRootIdealDividedSquareColumn (isogenyReverse k) a) :=
    quadraticPolynomial_congr t rfl
      (congrArg (fun z => (1 : A) ⊗ₜ[ZMod 2] z)
        (f4ShortRootQuotientToIdealEquiv_firstColumn_of_long k hk a))
      (congrArg (fun z => (1 : A) ⊗ₜ[ZMod 2] z)
        (f4ShortRootQuotientToIdealEquiv_dividedSquare_of_long k hk a))
  exact hcoeff.trans (htarget.symm.trans (congrArg
    (fun u => f4ShortRootExponential (isogenyReverse k) u
      ((1 : A) ⊗ₜ[ZMod 2] f4ShortRootLieIdealBasis a)) hexp.symm))

/-- The transported canonical quotient-column polynomial is the target short-root exponential
with the special-isogeny parameter exponent. -/
theorem f4ShortRootQuotientColumns_eq_exponential
    {A : Type*} [CommRing A] [Algebra (ZMod 2) A]
    (k : Fin 4 ⊕ Fin 4) (t : A) (a : Fin 26) :
    f4ShortRootTransportedQuotientPolynomial k t a =
      f4ShortRootExponential (isogenyReverse k) (t ^ isogenyExponent k)
        ((1 : A) ⊗ₜ[ZMod 2] f4ShortRootLieIdealBasis a) :=
  (f4Length_eq_one_or_eq_two (f4SignedSimpleRootIndex k)).elim
    (f4ShortRootTransportedQuotientPolynomial_eq_exponential_of_short k t a)
    (f4ShortRootTransportedQuotientPolynomial_eq_exponential_of_long k t a)

/-- After the canonical coordinate identification, the quotient exponential is the target
short-root exponential with the special-isogeny parameter exponent. -/
theorem f4ShortRootQuotient_rootExponential_pinning
    {A : Type*} [CommRing A] [Algebra (ZMod 2) A]
    (k : Fin 4 ⊕ Fin 4) (t : A) (a : Fin 26) :
    f4ShortRootQuotientToIdealBaseChange
        (f4ShortRootBaseChangeQuotient
          (f4RootExponential k t
            ((1 : A) ⊗ₜ[ℤ] f4IntegralShortRootQuotientLift a))) =
      f4ShortRootExponential (isogenyReverse k) (t ^ isogenyExponent k)
        ((1 : A) ⊗ₜ[ZMod 2] f4ShortRootLieIdealBasis a) := by
  let E := f4ShortRootQuotientToIdealBaseChange (A := A)
  have hpoly := congrArg E
    (f4ShortRootBaseChangeQuotient_rootExponential_quotientColumns
      (A := A) k t a)
  have h₀ : E ((1 : A) ⊗ₜ[ZMod 2] f4ShortRootQuotientBasis a) =
      (1 : A) ⊗ₜ[ZMod 2] f4ShortRootLieIdealBasis a := by
    calc
      _ = (1 : A) ⊗ₜ[ZMod 2]
          f4ShortRootQuotientToIdealEquiv (f4ShortRootQuotientBasis a) :=
        LinearMap.baseChange_tmul f4ShortRootQuotientToIdealEquiv.toLinearMap 1 _
      _ = _ := congrArg (fun z => (1 : A) ⊗ₜ[ZMod 2] z)
        (f4ShortRootQuotientToIdealEquiv_basis a)
  have h₁ : E ((1 : A) ⊗ₜ[ZMod 2] f4ShortRootQuotientFirstColumn k a) =
      (1 : A) ⊗ₜ[ZMod 2]
        f4ShortRootQuotientToIdealEquiv (f4ShortRootQuotientFirstColumn k a) :=
    LinearMap.baseChange_tmul f4ShortRootQuotientToIdealEquiv.toLinearMap 1 _
  have h₂ : E ((1 : A) ⊗ₜ[ZMod 2]
      f4ShortRootQuotientDividedSquareColumn k a) =
      (1 : A) ⊗ₜ[ZMod 2]
        f4ShortRootQuotientToIdealEquiv
          (f4ShortRootQuotientDividedSquareColumn k a) :=
    LinearMap.baseChange_tmul f4ShortRootQuotientToIdealEquiv.toLinearMap 1 _
  have hmap :
      E ((1 : A) ⊗ₜ[ZMod 2] f4ShortRootQuotientBasis a +
          t • ((1 : A) ⊗ₜ[ZMod 2] f4ShortRootQuotientFirstColumn k a) +
          t ^ 2 • ((1 : A) ⊗ₜ[ZMod 2]
            f4ShortRootQuotientDividedSquareColumn k a)) =
        f4ShortRootTransportedQuotientPolynomial k t a := by
    exact (map_quadraticPolynomial E t _ _ _).trans
      (quadraticPolynomial_congr t h₀ h₁ h₂)
  exact hpoly.trans (hmap.trans (f4ShortRootQuotientColumns_eq_exponential k t a))

end

end TauCeti.DynkinType
