/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Lie.UniversalEnveloping
public import TauCeti.RepresentationTheory.Spin.Polarization.CliffordAction
public import TauCeti.RepresentationTheory.Spin.Polarization.TypeB.RootGenerators

/-!
# The type-B spin representation of an odd polarization

`TauCeti.SpinPolarizationData.typeBQuadraticEquiv` identifies the split type-`B` matrix Lie
algebra `LieAlgebra.Orthogonal.typeB ι K` with the quadratic elements of the Clifford algebra of
an odd polarization, and those act on the spinor module `ExteriorAlgebra K P.W` through
`TauCeti.SpinPolarizationData.spinAction`. Composing the two gives the **spin representation** of
the type-`B` matrix algebra, which this file assembles and extends to the universal enveloping
algebra.

The numbered root and coroot generators are read through their Clifford realizations in
`TauCeti/RepresentationTheory/Spin/Polarization/TypeB/RootGenerators.lean`; this file also records
the field-generic actions of the root operators on the exterior basis: a difference-root operator
contracts one coordinate and creates another, the represented simple-root operators are square-zero,
and the simple-root operators move the exterior vacuum and singletons. The integrality of that
action is the subject of `TauCeti/RepresentationTheory/Spin/Polarization/TypeB/KostantLattice.lean`.
Nothing here is specific to `ℚ`: any field in which `2` is invertible carries the same
representation.

The enveloping-algebra extension is what the Chevalley--Demazure construction consumes, since
divided powers of root vectors and binomial coefficients in coroots live in the enveloping
algebra and not in the Lie algebra.

## Main declarations

* `TauCeti.SpinPolarizationData.typeBSpinLieRep`: the spin representation of the split type-`B`
  matrix Lie algebra.
* `TauCeti.SpinPolarizationData.typeBSpinLieRep_apply`: its value on a matrix.
* `TauCeti.SpinPolarizationData.typeBSpinRep`: its extension to the universal enveloping algebra.
* `TauCeti.SpinPolarizationData.typeBSpinRep_ι`: the extension evaluated on a Lie generator.
* `TauCeti.SpinPolarizationData.typeBSpinRep_differenceRootGenerator_apply`: a difference-root
  operator contracts one exterior coordinate and creates another.
* `TauCeti.SpinPolarizationData.typeBSpinRep_simpleRootGenerator_sq`: the represented simple-root
  operators are square-zero.
* `typeBSpinRep_simpleRootGenerator_last_exteriorBasis_empty` and
  `typeBSpinRep_simpleNegativeRootGenerator_last_exteriorBasis_singleton`:
  the terminal root actions on the exterior vacuum and final singleton.
* `typeBSpinRep_simpleRootGenerator_castSucc_exteriorBasis_singleton` and
  `typeBSpinRep_simpleNegativeRootGenerator_castSucc_exteriorBasis_singleton`: the nonterminal
  simple-root actions on exterior singletons.

## References

* C. Chevalley, *The Algebraic Theory of Spinors*, Chapter II.
* J. E. Humphreys, *Introduction to Lie Algebras and Representation Theory*, §17.
-/

public section

open CliffordAlgebra

namespace TauCeti

universe u v

attribute [local instance 100] LieRing.ofAssociativeRing

namespace SpinPolarizationData

variable {K : Type u} [Field K] {V : Type v} [AddCommGroup V] [Module K V]
  {Q : QuadraticForm K V} (P : SpinPolarizationData Q) {ι : Type*} [Fintype ι] [DecidableEq ι]
  (b : Module.Basis ι K P.W) (z : P.line) (hz : Q (z : V) = 1) [Invertible (2 : K)]

/-- The type-`B` matrix Lie algebra acting on the spinor module through the quadratic Clifford
realization associated to an odd polarization. -/
noncomputable def typeBSpinLieRep :
    LieAlgebra.Orthogonal.typeB ι K →ₗ⁅K⁆ Module.End K (ExteriorAlgebra K P.W) :=
  (spinAction Q P).toLieHom.comp <|
    (quadraticLieSubalgebra Q).incl.comp (P.typeBQuadraticEquiv b z hz).toLieHom

/-- The spin representation sends a type-`B` matrix to the spin action of its quadratic Clifford
realization. -/
@[simp]
theorem typeBSpinLieRep_apply (x : LieAlgebra.Orthogonal.typeB ι K) :
    P.typeBSpinLieRep b z hz x =
      spinAction Q P (P.typeBQuadraticEquiv b z hz x : CliffordAlgebra Q) := by
  rw [typeBSpinLieRep, LieHom.comp_apply, LieHom.comp_apply, LieSubalgebra.coe_incl,
    AlgHom.toLieHom_apply]
  rfl

/-- The type-`B` spin representation extended to the universal enveloping algebra. -/
noncomputable def typeBSpinRep :
    _root_.UniversalEnvelopingAlgebra K (LieAlgebra.Orthogonal.typeB ι K) →ₐ[K]
      Module.End K (ExteriorAlgebra K P.W) :=
  _root_.UniversalEnvelopingAlgebra.lift K (P.typeBSpinLieRep b z hz)

/-- A Lie generator acts in the enveloping-algebra representation through its quadratic
Clifford element. -/
@[simp]
theorem typeBSpinRep_ι (x : LieAlgebra.Orthogonal.typeB ι K) :
    P.typeBSpinRep b z hz
        (_root_.UniversalEnvelopingAlgebra.mkAlgHom K
          (LieAlgebra.Orthogonal.typeB ι K) (TensorAlgebra.ι K x)) =
      spinAction Q P (P.typeBQuadraticEquiv b z hz x : CliffordAlgebra Q) := by
  rw [typeBSpinRep, _root_.UniversalEnvelopingAlgebra.lift_ι_apply',
    P.typeBSpinLieRep_apply b z hz]

/-- The difference-root operator indexed by distinct coordinates `i` and `j` contracts the `j`-th
exterior coordinate and then creates the `i`-th one. -/
theorem typeBSpinRep_differenceRootGenerator_apply (i j : ι) (hij : i ≠ j)
    (x : ExteriorAlgebra K P.W) :
    P.typeBSpinRep b z hz
        (_root_.UniversalEnvelopingAlgebra.ι K (typeBDifferenceRootGenerator i j hij)) x =
      ExteriorAlgebra.ι K (b i) *
        CliffordAlgebra.contractLeft (b.coord j) x := by
  rw [_root_.UniversalEnvelopingAlgebra.ι_apply, P.typeBSpinRep_ι b z hz,
    P.typeBQuadraticEquiv_typeBDifferenceRootGenerator b z hz,
    bivector_eq_ι_mul_ι_of_isOrtho Q (P.isOrtho_basis_dualVector b hij), map_mul,
    Module.End.mul_apply, spinAction_ι_wedge, spinAction_ι_contract,
    P.pairingEquiv_dualVector]

section TerminalRoot

variable {n : ℕ} (b : Module.Basis (Fin (n + 1)) K P.W)
  (z : P.line) (hz : Q (z : V) = 1)

/-- A positive short-root operator creates its exterior coordinate after the grade involution,
scaled by the line coordinate of the distinguished remainder vector. -/
theorem typeBSpinRep_shortRootGenerator_apply (i : Fin (n + 1))
    (x : ExteriorAlgebra K P.W) :
    P.typeBSpinRep b z hz
        (_root_.UniversalEnvelopingAlgebra.ι K (typeBShortRootGenerator i)) x =
      ExteriorAlgebra.ι K (b i) *
        (P.lineCoordinate z • CliffordAlgebra.involute x) := by
  rw [_root_.UniversalEnvelopingAlgebra.ι_apply, P.typeBSpinRep_ι b z hz,
    P.typeBQuadraticEquiv_typeBShortRootGenerator b z hz,
    bivector_eq_ι_mul_ι_of_isOrtho Q (P.isOrtho_W_line _ z), map_mul,
    Module.End.mul_apply, spinAction_ι_wedge, spinAction_ι_lineOperator]

/-- A negative short-root operator contracts its exterior coordinate and applies the grade
involution, scaled by the line coordinate of the distinguished remainder vector. -/
theorem typeBSpinRep_shortNegativeRootGenerator_apply (i : Fin (n + 1))
    (x : ExteriorAlgebra K P.W) :
    P.typeBSpinRep b z hz
        (_root_.UniversalEnvelopingAlgebra.ι K (typeBShortNegativeRootGenerator i)) x =
      P.lineCoordinate z • CliffordAlgebra.involute
        (CliffordAlgebra.contractLeft (b.coord i) x) := by
  rw [_root_.UniversalEnvelopingAlgebra.ι_apply, P.typeBSpinRep_ι b z hz,
    P.typeBQuadraticEquiv_typeBShortNegativeRootGenerator b z hz,
    bivector_eq_ι_mul_ι_of_isOrtho Q (P.isOrtho_line_W' z _), map_mul,
    Module.End.mul_apply, spinAction_ι_contract, P.pairingEquiv_dualVector,
    spinAction_ι_lineOperator]

/-- The terminal positive short-root operator creates the final exterior coordinate from the
vacuum when the distinguished remainder vector has coordinate one. -/
theorem typeBSpinRep_simpleRootGenerator_last_exteriorBasis_empty
    (hcoord : P.lineCoordinate z = 1) :
    P.typeBSpinRep b z hz
        (_root_.UniversalEnvelopingAlgebra.ι K
          (typeBSimpleRootGeneratorFamily (.inl (Fin.last n))))
        (b.ExteriorAlgebra ∅) =
      b.ExteriorAlgebra {Fin.last n} := by
  rw [typeBSimpleRootGeneratorFamily_inl, typeBSimpleRootGenerator_last,
    P.typeBSpinRep_shortRootGenerator_apply b z hz, hcoord,
    TauCeti.ExteriorAlgebra.involute_basis]
  have hEmpty : b.ExteriorAlgebra (∅ : Finset (Fin (n + 1))) = 1 := by
    rw [ExteriorAlgebra.basis_apply]
    simp
  simp only [Finset.card_empty, pow_zero, one_smul]
  rw [hEmpty, mul_one, TauCeti.ExteriorAlgebra.basis_singleton]

/-- The terminal negative short-root operator annihilates the final exterior coordinate to the
vacuum when the distinguished remainder vector has coordinate one. -/
theorem typeBSpinRep_simpleNegativeRootGenerator_last_exteriorBasis_singleton
    (hcoord : P.lineCoordinate z = 1) :
    P.typeBSpinRep b z hz
        (_root_.UniversalEnvelopingAlgebra.ι K
          (typeBSimpleRootGeneratorFamily (.inr (Fin.last n))))
        (b.ExteriorAlgebra {Fin.last n}) =
      b.ExteriorAlgebra ∅ := by
  rw [typeBSimpleRootGeneratorFamily_inr, typeBSimpleNegativeRootGenerator_last,
    P.typeBSpinRep_shortNegativeRootGenerator_apply b z hz,
    TauCeti.ExteriorAlgebra.basis_singleton, CliffordAlgebra.contractLeft_ι,
    hcoord]
  simp [ExteriorAlgebra.basis_apply]

end TerminalRoot

section SimpleRoot

variable {n : ℕ} (b : Module.Basis (Fin (n + 1)) K P.W)
  (z : P.line) (hz : Q (z : V) = 1)

private theorem typeBQuadraticEquiv_typeBSimpleRootGenerator_mul_self
    (i : Fin (n + 1)) :
    (P.typeBQuadraticEquiv b z hz (typeBSimpleRootGenerator i) : CliffordAlgebra Q) ^ 2 = 0 := by
  refine Fin.lastCases ?_ (fun j ↦ ?_) i
  · rw [typeBSimpleRootGenerator_last, pow_two]
    exact P.typeBQuadraticEquiv_typeBShortRootGenerator_mul_self b z hz (Fin.last n)
  · rw [typeBSimpleRootGenerator_castSucc, pow_two]
    exact P.typeBQuadraticEquiv_typeBDifferenceRootGenerator_mul_self b z hz
      j.castSucc j.succ (ne_of_lt j.castSucc_lt_succ)

private theorem typeBQuadraticEquiv_typeBSimpleNegativeRootGenerator_mul_self
    (i : Fin (n + 1)) :
    (P.typeBQuadraticEquiv b z hz
      (typeBSimpleNegativeRootGenerator i) : CliffordAlgebra Q) ^ 2 = 0 := by
  refine Fin.lastCases ?_ (fun j ↦ ?_) i
  · rw [typeBSimpleNegativeRootGenerator_last, pow_two]
    exact P.typeBQuadraticEquiv_typeBShortNegativeRootGenerator_mul_self b z hz (Fin.last n)
  · rw [typeBSimpleNegativeRootGenerator_castSucc, pow_two]
    exact P.typeBQuadraticEquiv_typeBDifferenceRootGenerator_mul_self b z hz
      j.succ j.castSucc (ne_of_gt j.castSucc_lt_succ)

/-- Every represented positive or negative simple-root vector is square-zero. -/
theorem typeBSpinRep_simpleRootGenerator_sq (k : Fin (n + 1) ⊕ Fin (n + 1)) :
    P.typeBSpinRep b z hz
        (_root_.UniversalEnvelopingAlgebra.ι K (typeBSimpleRootGeneratorFamily k)) ^ 2 = 0 := by
  rw [_root_.UniversalEnvelopingAlgebra.ι_apply, P.typeBSpinRep_ι b z hz, pow_two, ← map_mul]
  cases k with
  | inl i =>
      rw [typeBSimpleRootGeneratorFamily_inl, ← pow_two,
        P.typeBQuadraticEquiv_typeBSimpleRootGenerator_mul_self b z hz i, map_zero]
  | inr i =>
      rw [typeBSimpleRootGeneratorFamily_inr, ← pow_two,
        P.typeBQuadraticEquiv_typeBSimpleNegativeRootGenerator_mul_self b z hz i, map_zero]

/-- A nonterminal positive simple-root operator moves the next exterior singleton one coordinate
to the left. -/
theorem typeBSpinRep_simpleRootGenerator_castSucc_exteriorBasis_singleton (j : Fin n) :
    P.typeBSpinRep b z hz
        (_root_.UniversalEnvelopingAlgebra.ι K
          (typeBSimpleRootGeneratorFamily (.inl j.castSucc)))
        (b.ExteriorAlgebra {j.succ}) =
      b.ExteriorAlgebra {j.castSucc} := by
  rw [typeBSimpleRootGeneratorFamily_inl, typeBSimpleRootGenerator_castSucc,
    P.typeBSpinRep_differenceRootGenerator_apply b z hz,
    TauCeti.ExteriorAlgebra.basis_singleton, CliffordAlgebra.contractLeft_ι]
  simp [TauCeti.ExteriorAlgebra.basis_singleton]

/-- A nonterminal negative simple-root operator moves an exterior singleton one coordinate to the
right. -/
theorem typeBSpinRep_simpleNegativeRootGenerator_castSucc_exteriorBasis_singleton (j : Fin n) :
    P.typeBSpinRep b z hz
        (_root_.UniversalEnvelopingAlgebra.ι K
          (typeBSimpleRootGeneratorFamily (.inr j.castSucc)))
        (b.ExteriorAlgebra {j.castSucc}) =
      b.ExteriorAlgebra {j.succ} := by
  rw [typeBSimpleRootGeneratorFamily_inr, typeBSimpleNegativeRootGenerator_castSucc,
    P.typeBSpinRep_differenceRootGenerator_apply b z hz,
    TauCeti.ExteriorAlgebra.basis_singleton, CliffordAlgebra.contractLeft_ι]
  simp [TauCeti.ExteriorAlgebra.basis_singleton]

end SimpleRoot

end SpinPolarizationData

end TauCeti
