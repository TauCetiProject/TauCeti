/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.CliffordAlgebra.Quadratic.Lie.Representation
public import TauCeti.RepresentationTheory.Spin.Polarization.TypeB.Representation
public import TauCeti.RepresentationTheory.Spin.Polarization.TypeD.Representation

/-!
# The spin representation of the orthogonal Lie algebra of a polarized quadratic space

For a polarization `P` of a finite-dimensional quadratic space `(V, Q)` over a field in which `2`
is invertible, the orthogonal Lie algebra `𝔰𝔬(Q) = skewAdjointLieSubalgebra (polarBilin Q)` acts
on the spinor module `S = ⋀·W`: a skew-adjoint endomorphism is realized as a quadratic element of
the Clifford algebra by `CliffordAlgebra.soEquivQuadratic`, and that element acts through the Fock
action `TauCeti.spinAction`. This is the spin representation without a choice of basis; the
coordinate models `TauCeti.SpinPolarizationData.typeBSpinLieRep` and
`TauCeti.SpinPolarizationData.typeDSpinLieRep` of the split matrix algebras are its pullbacks
along the basis transports of matrices to endomorphisms.

The normalization is pinned by the Clifford operators of vectors: the operator of `f ∈ 𝔰𝔬(Q)`
has commutator `c(f x)` with the operator `c(x)` of each vector `x`. This is the image of the
Clifford identity `⁅soEquivQuadratic f, ι x⁆ = ι (f x)` under the algebra homomorphism
`spinAction`, so no differentiated group action enters. On the infinitesimal rotation
`x ↦ polar Q b x • a - polar Q a x • b` the operator is the half-commutator
`⅟2 • (c(a) c(b) - c(b) c(a))`; for `w ∈ W` and `w' ∈ W'` it is exterior multiplication by `w`
after contraction by `w'`, shifted by `⅟2 • polar Q w w'`. On a hyperbolic pair with
`polar Q w w' = 1` it therefore has the spin weights `-½` on `1` and `+½` on `w`.

In even dimension, that is when the polarization has no orthogonal remainder, the action preserves
the two half-spin summands `S⁺` and `S⁻`, and restricts to them.

## Main declarations

* `TauCeti.SpinPolarizationData.soSpinLieRep`: the spin representation of `𝔰𝔬(Q)` on `⋀·W`.
* `TauCeti.SpinPolarizationData.soSpinLieRep_apply`: it is the Fock action of the quadratic
  realization.
* `TauCeti.SpinPolarizationData.lie_soSpinLieRep_cliffordOperator`: its commutator with the
  Clifford operator of a vector.
* `TauCeti.SpinPolarizationData.soSpinLieRep_eq_invOf_two_smul_cliffordOperator_mul_sub`: its
  value on an infinitesimal rotation is the half-commutator of two Clifford operators.
* `TauCeti.SpinPolarizationData.soSpinLieRep_apply_eq_mul_contractLeft_sub`: the value on the
  rotation of an isotropic pair is a number operator shifted by a scalar.
* `TauCeti.SpinPolarizationData.typeBSpinLieRep_eq_soSpinLieRep_comp` and
  `TauCeti.SpinPolarizationData.typeDSpinLieRep_eq_soSpinLieRep_comp`: the type-`B` and type-`D`
  coordinate representations factor through it.
* `TauCeti.SpinPolarizationData.soSpinPlusLieRep` and
  `TauCeti.SpinPolarizationData.soSpinMinusLieRep`: its restrictions to the half-spin summands
  in even dimension, with
  `TauCeti.SpinPolarizationData.typeDSpinPlusLieRep_eq_soSpinPlusLieRep_comp` and
  `TauCeti.SpinPolarizationData.typeDSpinMinusLieRep_eq_soSpinMinusLieRep_comp`.

Their irreducibility is in `TauCeti/RepresentationTheory/Spin/Polarization/Irreducible.lean`.

## References

* W. Fulton and J. Harris, *Representation Theory: A First Course* (1991), §20.1: the spin
  representation of `𝔰𝔬(Q)` through the embedding of `⋀²V` in the Clifford algebra.
* C. Chevalley, *The Algebraic Theory of Spinors* (1954), Chapter II.
-/

public section

open CliffordAlgebra

namespace TauCeti.SpinPolarizationData

universe u v w

attribute [local instance 100] LieRing.ofAssociativeRing

variable {K : Type u} [Field K] {V : Type v} [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] {Q : QuadraticForm K V} (P : SpinPolarizationData Q)
  [Invertible (2 : K)]

/-! ### The spin representation of `𝔰𝔬(Q)` -/

/-- **The spin representation of the orthogonal Lie algebra** `𝔰𝔬(Q)` on the spinor module
`⋀·W` of a polarization: a skew-adjoint endomorphism acts through the Fock action of its quadratic
Clifford realization. The quadratic form is nondegenerate because it carries a polarization
(`TauCeti.SpinPolarizationData.nondegenerate`). -/
noncomputable def soSpinLieRep :
    skewAdjointLieSubalgebra (QuadraticMap.polarBilin Q) →ₗ⁅K⁆
      Module.End K (ExteriorAlgebra K P.W) :=
  cliffordInducedRep Q (P.nondegenerate ((isUnit_of_invertible (2 : K)).isSMulRegular K))
    (LieHom.id) (spinAction Q P)

/-- A skew-adjoint endomorphism acts on the spinor module through the Fock action of its quadratic
Clifford realization, for any proof of nondegeneracy. -/
theorem soSpinLieRep_apply (hQ : Q.Nondegenerate)
    (f : skewAdjointLieSubalgebra (QuadraticMap.polarBilin Q)) :
    P.soSpinLieRep f = spinAction Q P (soEquivQuadratic Q hQ f : CliffordAlgebra Q) := by
  rw [soSpinLieRep, cliffordInducedRep_apply, LieHom.id_apply]

/-- **The normalization of the spin representation.** The operator of a skew-adjoint
endomorphism `f` has commutator `c(f x)` with the Clifford operator `c(x)` of each vector `x`. It
is the image of `CliffordAlgebra.soEquivQuadratic_lie_ι` under the Fock action. -/
@[simp]
theorem lie_soSpinLieRep_cliffordOperator
    (f : skewAdjointLieSubalgebra (QuadraticMap.polarBilin Q)) (x : V) :
    ⁅P.soSpinLieRep f, P.cliffordOperator x⁆ =
      P.cliffordOperator ((f : Module.End K V) x) := by
  have hQ := P.nondegenerate ((isUnit_of_invertible (2 : K)).isSMulRegular K)
  rw [P.soSpinLieRep_apply hQ, ← spinAction_ι, ← spinAction_ι, ← AlgHom.toLieHom_apply,
    ← AlgHom.toLieHom_apply, ← LieHom.map_lie, soEquivQuadratic_lie_ι, AlgHom.toLieHom_apply]

/-- A skew-adjoint endomorphism acting on vectors as the infinitesimal rotation
`x ↦ polar Q b x • a - polar Q a x • b` acts on the spinor module through the Clifford bivector of
`a` and `b`. -/
theorem soSpinLieRep_eq_spinAction_bivector
    (f : skewAdjointLieSubalgebra (QuadraticMap.polarBilin Q)) (a b : V)
    (hf : ∀ x, (f : Module.End K V) x =
      QuadraticMap.polar Q b x • a - QuadraticMap.polar Q a x • b) :
    P.soSpinLieRep f = spinAction Q P (bivector Q a b) := by
  have hQ := P.nondegenerate ((isUnit_of_invertible (2 : K)).isSMulRegular K)
  have h : soEquivQuadratic Q hQ f = ⟨bivector Q a b, bivector_mem_quadraticLieSubalgebra Q a b⟩ :=
    quadraticLieSubalgebra_eq_bivector_of_lie_ι Q hQ _ _ (soEquivQuadratic_lie_ι Q hQ f)
      (Module.finBasis K V) a b fun _ => hf _
  rw [P.soSpinLieRep_apply hQ, h]

/-- **The spin operator of an infinitesimal rotation is a half-commutator.** A skew-adjoint
endomorphism acting on vectors as `x ↦ polar Q b x • a - polar Q a x • b` acts on the spinor
module by `⅟2 • (c(a) c(b) - c(b) c(a))`, where `c` is the Clifford operator of a vector. -/
theorem soSpinLieRep_eq_invOf_two_smul_cliffordOperator_mul_sub
    (f : skewAdjointLieSubalgebra (QuadraticMap.polarBilin Q)) (a b : V)
    (hf : ∀ x, (f : Module.End K V) x =
      QuadraticMap.polar Q b x • a - QuadraticMap.polar Q a x • b) :
    P.soSpinLieRep f =
      ⅟(2 : K) • (P.cliffordOperator a * P.cliffordOperator b -
        P.cliffordOperator b * P.cliffordOperator a) := by
  rw [P.soSpinLieRep_eq_spinAction_bivector f a b hf, bivector_def]
  simp

/-- **The spin operator of the rotation of an isotropic pair.** For `w ∈ W` and `w' ∈ W'`, a
skew-adjoint endomorphism acting on vectors as `x ↦ polar Q w' x • w - polar Q w x • w'` acts on
the spinor module as exterior multiplication by `w` after contraction by `w'`, minus
`⅟2 • polar Q w w'`. For a hyperbolic pair, `polar Q w w' = 1`, this is the number operator
shifted by `-½`. -/
theorem soSpinLieRep_apply_eq_mul_contractLeft_sub (w : P.W) (w' : P.W')
    (f : skewAdjointLieSubalgebra (QuadraticMap.polarBilin Q))
    (hf : ∀ x, (f : Module.End K V) x =
      QuadraticMap.polar Q w' x • (w : V) - QuadraticMap.polar Q w x • (w' : V))
    (s : ExteriorAlgebra K P.W) :
    P.soSpinLieRep f s =
      ExteriorAlgebra.ι K w * contractLeft (P.pairingEquiv w') s -
        (⅟(2 : K) * QuadraticMap.polar Q w w') • s := by
  have hb : bivector Q (w : V) w' = ι Q (w : V) * ι Q (w' : V) -
      ⅟(2 : K) • algebraMap K (CliffordAlgebra Q) (QuadraticMap.polar Q w w') :=
    eq_sub_of_add_eq (ι_mul_ι_eq_bivector_add Q (w : V) w').symm
  rw [P.soSpinLieRep_eq_spinAction_bivector f w w' hf, hb, map_sub, map_mul, map_smul,
    AlgHom.commutes, LinearMap.sub_apply, mul_apply_eq_comp, spinAction_ι_contract,
    spinAction_ι_wedge, LinearMap.smul_apply, Module.algebraMap_end_apply, smul_smul]

/-- **The spin operator of the rotation of an isotropic pair on the vacuum.** For `w ∈ W` and
`w' ∈ W'`, the rotation sends the scalar spinor `1` to `-(⅟2 * polar Q w w') • 1`. For a hyperbolic
pair, `polar Q w w' = 1`, the vacuum is thus an eigenvector of spin weight `-½`. -/
theorem soSpinLieRep_apply_one (w : P.W) (w' : P.W')
    (f : skewAdjointLieSubalgebra (QuadraticMap.polarBilin Q))
    (hf : ∀ x, (f : Module.End K V) x =
      QuadraticMap.polar Q w' x • (w : V) - QuadraticMap.polar Q w x • (w' : V)) :
    P.soSpinLieRep f 1 = -(⅟(2 : K) * QuadraticMap.polar Q w w') • (1 : ExteriorAlgebra K P.W) := by
  rw [P.soSpinLieRep_apply_eq_mul_contractLeft_sub w w' f hf, ← map_one (algebraMap K _),
    contractLeft_algebraMap, mul_zero, zero_sub, neg_smul]

/-- **The spin operator of the rotation of an isotropic pair on `w`.** For `w ∈ W` and `w' ∈ W'`,
the rotation sends the spinor `w` to `(⅟2 * polar Q w w') • w`. For a hyperbolic pair,
`polar Q w w' = 1`, so `w ≠ 0`, the spinor `w` is thus an eigenvector of spin weight `+½`. -/
theorem soSpinLieRep_apply_ι (w : P.W) (w' : P.W')
    (f : skewAdjointLieSubalgebra (QuadraticMap.polarBilin Q))
    (hf : ∀ x, (f : Module.End K V) x =
      QuadraticMap.polar Q w' x • (w : V) - QuadraticMap.polar Q w x • (w' : V)) :
    P.soSpinLieRep f (ExteriorAlgebra.ι K w) =
      (⅟(2 : K) * QuadraticMap.polar Q w w') • ExteriorAlgebra.ι K w := by
  rw [P.soSpinLieRep_apply_eq_mul_contractLeft_sub w w' f hf, ExteriorAlgebra.ι, contractLeft_ι,
    pairingEquiv_apply, ← Algebra.commutes, ← Algebra.smul_def, ← sub_smul]
  congr 1
  linear_combination (-QuadraticMap.polar Q (w : V) w') * mul_invOf_self (2 : K)

/-! ### The coordinate models -/

section Coordinates

variable {ι : Type w} [Fintype ι] [DecidableEq ι] (b : Module.Basis ι K P.W)

/-- **The type-`B` spin representation is the spin representation of `𝔰𝔬(Q)` in coordinates.**
The split type-`B` matrix algebra acts on the spinor module through the endomorphisms its matrices
represent in the odd hyperbolic basis. -/
theorem typeBSpinLieRep_eq_soSpinLieRep_comp (z : P.line) (hz : Q (z : V) = 1) :
    P.typeBSpinLieRep b z hz = P.soSpinLieRep.comp
      (skewAdjointLieEquivOfBasis (P.typeBBasis b z hz) (QuadraticMap.polarBilin Q)
        (P.polarBilin_toMatrix_typeBBasis b z hz)).toLieHom := by
  have hQ := P.nondegenerate ((isUnit_of_invertible (2 : K)).isSMulRegular K)
  refine LieHom.ext fun A => ?_
  have h : P.typeBQuadraticEquiv b z hz A = soEquivQuadratic Q hQ
      (skewAdjointLieEquivOfBasis (P.typeBBasis b z hz) (QuadraticMap.polarBilin Q)
        (P.polarBilin_toMatrix_typeBBasis b z hz) A) :=
    quadraticLieSubalgebra_ext Q hQ fun x => by
      rw [typeBQuadraticEquiv_lie_ι, soEquivQuadratic_lie_ι]
      -- `A` is a matrix of the `def`-wrapped algebra, so the transport lemma is applied, not
      -- rewritten.
      exact congrArg (CliffordAlgebra.ι Q)
        (LinearMap.congr_fun (coe_skewAdjointLieEquivOfBasis_apply _ _ _ A) x).symm
  rw [typeBSpinLieRep_apply, h]
  -- The right side is `soSpinLieRep` applied to the transported matrix, up to `LieHom.comp_apply`,
  -- which does not rewrite because the matrix algebra is a `def` over the skew-adjoint matrices.
  exact (P.soSpinLieRep_apply hQ _).symm

/-- **The type-`D` spin representation is the spin representation of `𝔰𝔬(Q)` in coordinates.**
The split type-`D` matrix algebra acts on the spinor module through the endomorphisms its matrices
represent in the hyperbolic basis. -/
theorem typeDSpinLieRep_eq_soSpinLieRep_comp (hline : P.line = ⊥) :
    P.typeDSpinLieRep b hline = P.soSpinLieRep.comp
      (skewAdjointLieEquivOfBasis (P.typeDBasis b hline) (QuadraticMap.polarBilin Q)
        (P.polarBilin_toMatrix_typeDBasis b hline)).toLieHom := by
  have hQ := P.nondegenerate_of_line_eq_bot hline
  refine LieHom.ext fun A => ?_
  have h : P.typeDQuadraticEquiv b hline A = soEquivQuadratic Q hQ
      (skewAdjointLieEquivOfBasis (P.typeDBasis b hline) (QuadraticMap.polarBilin Q)
        (P.polarBilin_toMatrix_typeDBasis b hline) A) :=
    quadraticLieSubalgebra_ext Q hQ fun x => by
      rw [typeDQuadraticEquiv_lie_ι, soEquivQuadratic_lie_ι]
      -- `A` is a matrix of the `def`-wrapped algebra, so the transport lemma is applied, not
      -- rewritten.
      exact congrArg (CliffordAlgebra.ι Q)
        (LinearMap.congr_fun (coe_skewAdjointLieEquivOfBasis_apply _ _ _ A) x).symm
  rw [typeDSpinLieRep_apply, h]
  -- The right side is `soSpinLieRep` applied to the transported matrix, up to `LieHom.comp_apply`,
  -- which does not rewrite because the matrix algebra is a `def` over the skew-adjoint matrices.
  exact (P.soSpinLieRep_apply hQ _).symm

end Coordinates

/-! ### The half-spin representations of `𝔰𝔬(Q)` -/

/-- **The even half-spin representation of `𝔰𝔬(Q)`**: in even dimension the spin representation
preserves the even half-spin summand `S⁺`, and this is its restriction there. -/
noncomputable def soSpinPlusLieRep (hline : P.line = ⊥) :
    skewAdjointLieSubalgebra (QuadraticMap.polarBilin Q) →ₗ⁅K⁆ Module.End K (spinPlus Q P) :=
  (spinPlusAction Q P hline).toLieHom.comp <|
    quadraticLiftToEven Q (P.nondegenerate_of_line_eq_bot hline) LieHom.id

/-- After coercion to the spinor module, the even half-spin action of `𝔰𝔬(Q)` is the spin
action. -/
@[simp]
theorem coe_soSpinPlusLieRep_apply (hline : P.line = ⊥)
    (f : skewAdjointLieSubalgebra (QuadraticMap.polarBilin Q)) (s : spinPlus Q P) :
    ((P.soSpinPlusLieRep hline f s : spinPlus Q P) : ExteriorAlgebra K P.W) =
      P.soSpinLieRep f s := by
  have hQ := P.nondegenerate_of_line_eq_bot hline
  rw [soSpinPlusLieRep, LieHom.comp_apply, AlgHom.toLieHom_apply, coe_spinPlusAction_apply,
    coe_quadraticLiftToEven_apply, quadraticLift_apply, LieHom.id_apply, P.soSpinLieRep_apply hQ]

/-- **The odd half-spin representation of `𝔰𝔬(Q)`**: in even dimension the spin representation
preserves the odd half-spin summand `S⁻`, and this is its restriction there. -/
noncomputable def soSpinMinusLieRep (hline : P.line = ⊥) :
    skewAdjointLieSubalgebra (QuadraticMap.polarBilin Q) →ₗ⁅K⁆ Module.End K (spinMinus Q P) :=
  (spinMinusAction Q P hline).toLieHom.comp <|
    quadraticLiftToEven Q (P.nondegenerate_of_line_eq_bot hline) LieHom.id

/-- After coercion to the spinor module, the odd half-spin action of `𝔰𝔬(Q)` is the spin
action. -/
@[simp]
theorem coe_soSpinMinusLieRep_apply (hline : P.line = ⊥)
    (f : skewAdjointLieSubalgebra (QuadraticMap.polarBilin Q)) (s : spinMinus Q P) :
    ((P.soSpinMinusLieRep hline f s : spinMinus Q P) : ExteriorAlgebra K P.W) =
      P.soSpinLieRep f s := by
  have hQ := P.nondegenerate_of_line_eq_bot hline
  rw [soSpinMinusLieRep, LieHom.comp_apply, AlgHom.toLieHom_apply, coe_spinMinusAction_apply,
    coe_quadraticLiftToEven_apply, quadraticLift_apply, LieHom.id_apply, P.soSpinLieRep_apply hQ]

section Coordinates

variable {ι : Type w} [Fintype ι] [DecidableEq ι] (b : Module.Basis ι K P.W)

/-- The even type-`D` half-spin representation is the even half-spin representation of `𝔰𝔬(Q)`
in the hyperbolic basis. -/
theorem typeDSpinPlusLieRep_eq_soSpinPlusLieRep_comp (hline : P.line = ⊥) :
    P.typeDSpinPlusLieRep b hline = (P.soSpinPlusLieRep hline).comp
      (skewAdjointLieEquivOfBasis (P.typeDBasis b hline) (QuadraticMap.polarBilin Q)
        (P.polarBilin_toMatrix_typeDBasis b hline)).toLieHom := by
  refine LieHom.ext fun A => LinearMap.ext fun s => Subtype.ext ?_
  rw [coe_typeDSpinPlusLieRep_apply, P.typeDSpinLieRep_eq_soSpinLieRep_comp b hline]
  -- Both sides apply a composite to the same matrix; `LieHom.comp_apply` does not rewrite because
  -- the matrix algebra is a `def` over the skew-adjoint matrices.
  exact (P.coe_soSpinPlusLieRep_apply hline _ s).symm

/-- The odd type-`D` half-spin representation is the odd half-spin representation of `𝔰𝔬(Q)`
in the hyperbolic basis. -/
theorem typeDSpinMinusLieRep_eq_soSpinMinusLieRep_comp (hline : P.line = ⊥) :
    P.typeDSpinMinusLieRep b hline = (P.soSpinMinusLieRep hline).comp
      (skewAdjointLieEquivOfBasis (P.typeDBasis b hline) (QuadraticMap.polarBilin Q)
        (P.polarBilin_toMatrix_typeDBasis b hline)).toLieHom := by
  refine LieHom.ext fun A => LinearMap.ext fun s => Subtype.ext ?_
  rw [coe_typeDSpinMinusLieRep_apply, P.typeDSpinLieRep_eq_soSpinLieRep_comp b hline]
  -- Both sides apply a composite to the same matrix; `LieHom.comp_apply` does not rewrite because
  -- the matrix algebra is a `def` over the skew-adjoint matrices.
  exact (P.coe_soSpinMinusLieRep_apply hline _ s).symm

end Coordinates

end TauCeti.SpinPolarizationData
