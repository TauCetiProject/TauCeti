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

The reduced integral Chevalley root exponential acts on the modular F4 short-root quotient by a
three-term quadratic formula over every commutative `ZMod 2`-algebra. The formula identifies the
quotient root columns used in the special-isogeny pinning.

## References

* R. W. Carter, *Simple Groups of Lie Type*, §4.4, for Chevalley root exponentials.
-/

public section

namespace TauCeti.DynkinType

open TauCeti.F4ShortRoot
open _root_.LieAlgebra _root_.LieAlgebra.IsKilling LieModule Module
open scoped TensorProduct

noncomputable section

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
theorem f4ShortRootIdealDividedSquareColumn_eq_zero_of_long (k : Fin 4 ⊕ Fin 4)
    (hk : f4Length (f4SignedSimpleRootIndex k) = 2)
    (a : Fin 26) :
    f4ShortRootIdealDividedSquareColumn k a = 0 := by
  rw [f4ShortRootIdealDividedSquareColumn_eq]
  have hc := f4DividedSquareCoeff_mod_two_eq_zero_of_long k hk a
  calc (f4DividedSquareCoeff k a : ZMod 2) •
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
noncomputable def f4ShortRootBaseChangeQuotient {A : Type*} [CommRing A] [Algebra (ZMod 2) A] :
    A ⊗[ℤ] f4ChevalleyLieLattice →ₗ[A]
      A ⊗[ZMod 2] (f4ModularChevalleyLieAlgebra ⧸ f4ShortRootSubspace) :=
  (f4ShortRootSubspace.mkQ.baseChange A).comp
    (TauCeti.LieAlgebra.ExtendScalars.cancelBaseChange ℤ (ZMod 2) A
      f4ChevalleyLieLattice).symm.toLinearMap

/-- Evaluation of the scalar-extended quotient map through scalar-tower cancellation. -/
theorem f4ShortRootBaseChangeQuotient_apply {A : Type*} [CommRing A] [Algebra (ZMod 2) A]
    (x : A ⊗[ℤ] f4ChevalleyLieLattice) :
    f4ShortRootBaseChangeQuotient x = f4ShortRootSubspace.mkQ.baseChange A
        ((TauCeti.LieAlgebra.ExtendScalars.cancelBaseChange ℤ (ZMod 2) A
          f4ChevalleyLieLattice).symm x) := by rfl

/-- The scalar-extended quotient map on a pure integral tensor. -/
theorem f4ShortRootBaseChangeQuotient_tmul {A : Type*} [CommRing A] [Algebra (ZMod 2) A]
    (a : A) (x : f4ChevalleyLieLattice) :
    f4ShortRootBaseChangeQuotient (a ⊗ₜ[ℤ] x) =
      a ⊗ₜ[ZMod 2] f4ShortRootSubspace.mkQ (1 ⊗ₜ[ℤ] x) := by
  -- Unfold the composite quotient map to apply scalar-tower cancellation on a pure tensor.
  change (f4ShortRootSubspace.mkQ.baseChange A)
      ((TauCeti.LieAlgebra.ExtendScalars.cancelBaseChange ℤ (ZMod 2) A
        f4ChevalleyLieLattice).symm (a ⊗ₜ[ℤ] x)) = _
  let q := f4ShortRootSubspace.mkQ.baseChange A
  let e := TauCeti.LieAlgebra.ExtendScalars.cancelBaseChange ℤ (ZMod 2) A f4ChevalleyLieLattice
  calc q (e.symm (a ⊗ₜ[ℤ] x)) = q (a ⊗ₜ[ZMod 2] (1 ⊗ₜ[ℤ] x)) :=
      congrArg q
        (TauCeti.LieAlgebra.ExtendScalars.cancelBaseChange_symm_tmul ℤ (ZMod 2) A
          f4ChevalleyLieLattice a x)
    _ = _ := LinearMap.baseChange_tmul f4ShortRootSubspace.mkQ a (1 ⊗ₜ[ℤ] x)

/-- After passing to the quotient, the root exponential has its three-term integral
divided-power polynomial on every pure tensor. -/
theorem f4ShortRootBaseChangeQuotient_rootExponential_tmul
    {A : Type*} [CommRing A] [Algebra (ZMod 2) A]
    (k : Fin 4 ⊕ Fin 4) (t : A) (x : f4ChevalleyLieLattice) :
    f4ShortRootBaseChangeQuotient (f4RootExponential k t ((1 : A) ⊗ₜ[ℤ] x)) =
      (1 : A) ⊗ₜ[ZMod 2] f4ShortRootSubspace.mkQ (1 ⊗ₜ[ℤ] x) + t • ((1 : A) ⊗ₜ[ZMod 2]
          f4ShortRootSubspace.mkQ (1 ⊗ₜ[ℤ] ⁅f4IntegralRootVector (f4SignedSimpleRootIndex k), x⁆)) +
        t ^ 2 • ((1 : A) ⊗ₜ[ZMod 2] f4ShortRootSubspace.mkQ
            (1 ⊗ₜ[ℤ] f4IntegralDividedAdjointSquare k x)) := by
  simp only [f4RootExponential_tmul, map_add, map_smul, f4ShortRootBaseChangeQuotient_tmul]

/-- The canonical integral lift of a quotient basis coordinate: a long root vector, or the long
simple coroot `h₁`, `h₀` at coordinates `12`, `13`. -/
noncomputable def f4IntegralShortRootQuotientLift (a : Fin 26) : f4ChevalleyLieLattice :=
  match f4ShortRootWeightIndexEquiv a with
  | Sum.inl i => f4IntegralRootVector (f4SpecialIsogenyIndexEquiv i)
  | Sum.inr j =>
      f4IntegralSimpleCoroot (Fin.cast rank_F4.symm (![1, 0] j : Fin 4))

/-- Reduction modulo two of the canonical integral lift is the canonical ambient modular lift. -/
theorem f4IntegralShortRootQuotientLift_modular (a : Fin 26) :
    1 ⊗ₜ[ℤ] f4IntegralShortRootQuotientLift a = f4ShortRootQuotientLift a := by
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
      simpa [f4IntegralShortRootQuotientLift] using (f4ModularSimpleCoroot_eq
          (Fin.cast rank_F4.symm (1 : Fin 4))).symm
    · rw [f4ShortRootWeightIndexEquiv_symm_apply_inr_one,
        f4ModularChevalleyBasis_longRootBasisCoordinate_thirteen]
      simpa [f4IntegralShortRootQuotientLift] using (f4ModularSimpleCoroot_eq
          (Fin.cast rank_F4.symm (0 : Fin 4))).symm

/-- Reduction of the canonical integral lift represents the corresponding quotient basis
coordinate. -/
theorem f4IntegralShortRootQuotientLift_mkQ (a : Fin 26) :
    f4ShortRootSubspace.mkQ (1 ⊗ₜ[ℤ] f4IntegralShortRootQuotientLift a) =
      f4ShortRootQuotientBasis a := by
  rw [f4IntegralShortRootQuotientLift_modular, f4ShortRootSubspace_mkQ_quotientLift]

/-- The bracket of an integral root vector with a canonical lift reduces to the first-order
quotient column. -/
theorem f4IntegralRootBracket_quotientLift_mkQ (k : Fin 4 ⊕ Fin 4) (a : Fin 26) :
    f4ShortRootSubspace.mkQ (1 ⊗ₜ[ℤ] ⁅f4IntegralRootVector (f4SignedSimpleRootIndex k),
          f4IntegralShortRootQuotientLift a⁆) =
      f4ShortRootQuotientFirstColumn k a := by
  let x := f4IntegralShortRootQuotientLift a
  let q := f4ShortRootSubspace.mkQ
  have hbracket : ⁅f4ModularRootVector (f4SignedSimpleRootIndex k), (1 : ZMod 2) ⊗ₜ[ℤ] x⁆ =
      (1 : ZMod 2) ⊗ₜ[ℤ] ⁅f4IntegralRootVector (f4SignedSimpleRootIndex k), x⁆ := by
    rw [f4ModularRootVector_eq, LieAlgebra.ExtendScalars.bracket_tmul, one_mul]
  calc q (1 ⊗ₜ[ℤ] ⁅f4IntegralRootVector (f4SignedSimpleRootIndex k), x⁆) =
        q ⁅f4ModularRootVector (f4SignedSimpleRootIndex k), 1 ⊗ₜ[ℤ] x⁆ :=
      congrArg q hbracket.symm
    _ = q ⁅f4ModularRootVector (f4SignedSimpleRootIndex k), f4ShortRootQuotientLift a⁆ :=
      congrArg q (congrArg (fun z => ⁅f4ModularRootVector (f4SignedSimpleRootIndex k), z⁆)
        (f4IntegralShortRootQuotientLift_modular a))
    _ = f4ShortRootQuotientFirstColumn k a :=
      (f4ShortRootQuotientFirstColumn_eq k a).symm

/-- The reduced second integral divided power on a canonical lift is the named quotient
divided-square column. -/
theorem f4IntegralDividedAdjointSquare_quotientLift_mkQ (k : Fin 4 ⊕ Fin 4) (a : Fin 26) :
    f4ShortRootSubspace.mkQ (1 ⊗ₜ[ℤ] f4IntegralDividedAdjointSquare k
          (f4IntegralShortRootQuotientLift a)) =
      f4ShortRootQuotientDividedSquareColumn k a := by
  let x := f4IntegralShortRootQuotientLift a
  let q := f4ShortRootSubspace.mkQ
  calc q (1 ⊗ₜ[ℤ] f4IntegralDividedAdjointSquare k x) =
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
    f4ShortRootBaseChangeQuotient (f4RootExponential k t
          ((1 : A) ⊗ₜ[ℤ] f4IntegralShortRootQuotientLift a)) =
      (1 : A) ⊗ₜ[ZMod 2] f4ShortRootQuotientBasis a + t • ((1 : A) ⊗ₜ[ZMod 2]
          f4ShortRootSubspace.mkQ (1 ⊗ₜ[ℤ] ⁅f4IntegralRootVector (f4SignedSimpleRootIndex k),
              f4IntegralShortRootQuotientLift a⁆)) +
        t ^ 2 • ((1 : A) ⊗ₜ[ZMod 2] f4ShortRootSubspace.mkQ
            (1 ⊗ₜ[ℤ] f4IntegralDividedAdjointSquare k (f4IntegralShortRootQuotientLift a))) := by
  simp only [f4ShortRootBaseChangeQuotient_rootExponential_tmul,
    f4IntegralShortRootQuotientLift_mkQ]

/-- The quotient of the genuine integral root exponential on a canonical lift is its canonical
quadratic column polynomial, over every commutative algebra of characteristic two. -/
theorem f4ShortRootBaseChangeQuotient_rootExponential_quotientColumns
    {A : Type*} [CommRing A] [Algebra (ZMod 2) A]
    (k : Fin 4 ⊕ Fin 4) (t : A) (a : Fin 26) :
    f4ShortRootBaseChangeQuotient (f4RootExponential k t
          ((1 : A) ⊗ₜ[ℤ] f4IntegralShortRootQuotientLift a)) =
      (1 : A) ⊗ₜ[ZMod 2] f4ShortRootQuotientBasis a +
        t • ((1 : A) ⊗ₜ[ZMod 2] f4ShortRootQuotientFirstColumn k a) +
        t ^ 2 • ((1 : A) ⊗ₜ[ZMod 2] f4ShortRootQuotientDividedSquareColumn k a) := by
  simp only [f4ShortRootBaseChangeQuotient_rootExponential_integralShortRootQuotientLift,
    f4IntegralRootBracket_quotientLift_mkQ, f4IntegralDividedAdjointSquare_quotientLift_mkQ]

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
    (1 : A) ⊗ₜ[ZMod 2] f4ShortRootLieIdealBasis a + t • ((1 : A) ⊗ₜ[ZMod 2]
        f4ShortRootQuotientToIdealEquiv (f4ShortRootQuotientFirstColumn k a)) +
      t ^ 2 • ((1 : A) ⊗ₜ[ZMod 2] f4ShortRootQuotientToIdealEquiv
          (f4ShortRootQuotientDividedSquareColumn k a))

/-- The target root exponential on a canonical basis vector, written using its named columns. -/
theorem f4ShortRootExponential_basis_apply {A : Type*} [CommRing A] [Algebra (ZMod 2) A]
    (k : Fin 4 ⊕ Fin 4) (t : A) (a : Fin 26) :
    f4ShortRootExponential k t ((1 : A) ⊗ₜ[ZMod 2] f4ShortRootLieIdealBasis a) =
      (1 : A) ⊗ₜ[ZMod 2] f4ShortRootLieIdealBasis a +
        t • ((1 : A) ⊗ₜ[ZMod 2] f4ShortRootIdealFirstColumn k a) +
        t ^ 2 • ((1 : A) ⊗ₜ[ZMod 2] f4ShortRootIdealDividedSquareColumn k a) := by
  simp only [f4ShortRootExponential_apply, f4ShortRootIdealFirstColumn_apply,
    f4ShortRootIdealDividedSquareColumn_apply]

private theorem f4ShortRootTransportedQuotientPolynomial_eq_exponential_of_short
    {A : Type*} [CommRing A] [Algebra (ZMod 2) A]
    (k : Fin 4 ⊕ Fin 4) (t : A) (a : Fin 26)
    (hk : f4Length (f4SignedSimpleRootIndex k) = 1) :
    f4ShortRootTransportedQuotientPolynomial k t a =
      f4ShortRootExponential (isogenyReverse k) (t ^ isogenyExponent k)
        ((1 : A) ⊗ₜ[ZMod 2] f4ShortRootLieIdealBasis a) := by
  simp only [isogenyExponent_eq_two_of_short k hk, f4ShortRootExponential_basis_apply,
    f4ShortRootIdealDividedSquareColumn_eq_zero_of_long (isogenyReverse k)
      (f4Length_isogenyReverse_eq_two_of_short k hk) a,
    f4ShortRootTransportedQuotientPolynomial,
    f4ShortRootQuotientToIdealEquiv_firstColumn_eq_zero_of_short k hk a,
    f4ShortRootQuotientToIdealEquiv_dividedSquare_eq_firstColumn_of_short k hk a,
    TensorProduct.tmul_zero, smul_zero, add_zero]

private theorem f4ShortRootTransportedQuotientPolynomial_eq_exponential_of_long
    {A : Type*} [CommRing A] [Algebra (ZMod 2) A]
    (k : Fin 4 ⊕ Fin 4) (t : A) (a : Fin 26)
    (hk : f4Length (f4SignedSimpleRootIndex k) = 2) :
    f4ShortRootTransportedQuotientPolynomial k t a =
      f4ShortRootExponential (isogenyReverse k) (t ^ isogenyExponent k)
        ((1 : A) ⊗ₜ[ZMod 2] f4ShortRootLieIdealBasis a) := by
  simp only [isogenyExponent_eq_one_of_long k hk, pow_one, f4ShortRootExponential_basis_apply,
    f4ShortRootTransportedQuotientPolynomial,
    f4ShortRootQuotientToIdealEquiv_firstColumn_of_long k hk a,
    f4ShortRootQuotientToIdealEquiv_dividedSquare_of_long k hk a]

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
  refine Eq.trans ?_ (f4ShortRootQuotientColumns_eq_exponential k t a)
  simp only [f4ShortRootBaseChangeQuotient_rootExponential_quotientColumns,
    f4ShortRootTransportedQuotientPolynomial, map_add, map_smul,
    f4ShortRootQuotientToIdealBaseChange_tmul, f4ShortRootQuotientToIdealEquiv_basis]

end

end TauCeti.DynkinType
