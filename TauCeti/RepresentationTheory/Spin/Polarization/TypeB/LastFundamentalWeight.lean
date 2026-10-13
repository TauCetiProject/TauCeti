/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.HighestWeight.Basis
public import TauCeti.Algebra.Lie.Orthogonal.TypeB.Basis
public import TauCeti.Algebra.Lie.Orthogonal.TypeB.Killing
public import TauCeti.RepresentationTheory.Spin.Polarization.TypeB.CartanWeights
public import TauCeti.RepresentationTheory.Spin.Polarization.TypeB.KostantLattice

/-!
# The last-fundamental-weight vector in the type-B spin representation

The spin module of an odd polarization is the exterior algebra `S = ⋀·W` of the first isotropic
summand, acted on by the split type-`B` matrix Lie algebra through
`TauCeti.SpinPolarizationData.typeBSpinLieRep`. Its exterior basis diagonalizes the numbered
simple coroots, with integral eigenvalues the coordinates of the spin weight
`TauCeti.DynkinType.typeBSpinWeight` of the index set; the underlying weights are the
half-integral sign vectors `½(±1, …, ±1)` of `TauCeti.spinWeight`. The
last fundamental weight `ωₗ` of `Bₙ₊₁`, the one attached to the terminal short node of the Dynkin
diagram, is carried by the basis vector with **every** coordinate occupied. This file combines two
facts that identify that vector:

* every positive simple-root generator annihilates it, hence so does the Lie subalgebra they
  generate;
* its coroot weight is `Pi.single (Fin.last n) 1`, that last fundamental weight.

The standard type-`B` Lie basis identifies these conditions with the canonical highest-weight
predicate for its compatible Borel. Thus the all-coordinate spinor is a highest-weight vector of
weight `ωₗ`; the resulting identification `S ≅ L(ωₗ)` is packaged in
`TauCeti/RepresentationTheory/Spin/Polarization/TypeB/Fundamental.lean`.

The last section reads the weights against the standard Lie algebra basis
`TauCeti.typeBLieBasis`, whose raising generators are the positive simple-root generators above.
In the basis of fundamental weights `ωᵢ`, dual to its simple coroots, the weight of the index set
`s` has integral coordinates `DynkinType.typeBSpinWeight s`; in particular the all-coordinate weight
is exactly the dual basis vector `ωₗ` at the terminal short node, the abstract last fundamental
weight of the basis. These are the hypotheses of the Lie-basis characterization
`LieAlgebra.Basis.isHighestWeightVector_iff_forall_e` of highest-weight vectors. In characteristic
zero, `TauCeti.isKilling_typeB` supplies the required nondegenerate Killing form whenever the
standard module is triangularizable, in particular over an algebraically closed field.

The annihilation is read off the two ways a simple-root generator acts on the exterior basis. The
terminal short generator creates the last coordinate (after the grade involution, and scaled by
the line coordinate of the distinguished remainder vector), and that coordinate is already
present, so the result vanishes. A nonterminal long generator `e_{εⱼ - εⱼ₊₁}` contracts the
`(j+1)`-st coordinate and then creates the `j`-th one, which the contraction left untouched, so
that vanishes too. Neither computation depends on the normalization of the remainder vector: the
scalar is irrelevant once the wedge is zero. Both read off the same condition, that the
coordinate the generator creates is already occupied, so the annihilation is stated for every
index set containing that coordinate; the all-coordinate vector, where this holds for every
generator at once, is the case used here.

The annihilation statements, and the comparison with the fundamental weights, hold over any
field in which `2` is invertible, which is all the underlying Clifford comparison needs. The
enveloping-algebra weight-vector statement is over `ℚ`, where
`TauCeti.UniversalEnvelopingAlgebra.IsCartanWeightVector` lives.

## Main results

* `TauCeti.SpinPolarizationData.typeBSpinLieRep_simpleRootGenerator_exteriorBasis_eq_zero_of_mem`:
  a positive simple-root generator annihilates every exterior-basis vector whose index set
  contains the generator's own coordinate, in particular the all-coordinate one.
* `typeBSpinLieRep_lieSpan_range_simpleRootGenerator_le_lieAnnihilator`, in the same namespace:
  generatorwise vanishing extends to the Lie subalgebra the positive simple-root generators
  generate, with
  `typeBSpinLieRep_lieSpan_range_simpleRootGenerator_le_lieAnnihilator_exteriorBasis_univ` its
  instance at the all-coordinate vector.
* `TauCeti.SpinPolarizationData.isCartanWeightVector_typeBSpinRep_exteriorBasis_univ`: the
  all-coordinate vector has the last fundamental weight.
* `TauCeti.SpinPolarizationData.typeBWeightEquiv_spinWeight_apply_simpleCorootGenerator`: a spin
  weight takes on each numbered simple coroot the corresponding coordinate of
  `TauCeti.DynkinType.typeBSpinWeight`.
* `TauCeti.SpinPolarizationData.typeBWeightEquiv_spinWeight_eq_sum_dualBasis`: a spin weight in
  the fundamental-weight basis of `TauCeti.typeBLieBasis`, with
  `TauCeti.SpinPolarizationData.typeBWeightEquiv_spinWeight_univ` its all-coordinate case `ωₗ`.
* `TauCeti.SpinPolarizationData.typeBSpinLieRep_apply_cartan_exteriorBasis_univ`: the diagonal
  Cartan acts on the all-coordinate vector through that fundamental weight.
* `TauCeti.SpinPolarizationData.isHighestWeightVector_typeBSpinLieRep_exteriorBasis_univ`: the
  all-coordinate vector is a highest-weight vector for the compatible Borel and abstract
  type-`B` root datum.

## References

* C. Chevalley, *The Algebraic Theory of Spinors*, Chapter II.
* W. Fulton and J. Harris, *Representation Theory: A First Course* (1991), Section 20.2.
* N. Bourbaki, *Groupes et algèbres de Lie*, Chapters 4--6, Planche II.
* The comparison with the fundamental weights follows the type-`D` one in
  `TauCeti/RepresentationTheory/Spin/Polarization/TypeD/HighestWeight.lean`.
-/

public section

namespace TauCeti

universe u v

attribute [local instance 100] LieRing.ofAssociativeRing

namespace SpinPolarizationData

/-! ## Annihilation by the positive simple-root generators -/

section Quadratic

variable {K : Type u} [Field K] {V : Type v} [AddCommGroup V] [Module K V]
  {Q : QuadraticForm K V} (P : SpinPolarizationData Q) {n : ℕ}
  (b : Module.Basis (Fin (n + 1)) K P.W) (z : P.line) (hz : Q (z : V) = 1)
  [Invertible (2 : K)]

/-- A positive simple type-`B` generator annihilates an exterior-basis vector whose index set
already contains the generator's own coordinate, in the enveloping-algebra form of the spin
representation. This is the computation behind
`typeBSpinLieRep_simpleRootGenerator_exteriorBasis_eq_zero_of_mem`, which is the form consumed
here. -/
private theorem typeBSpinRep_simpleRootGenerator_exteriorBasis_eq_zero_of_mem
    {i : Fin (n + 1)} {s : Finset (Fin (n + 1))} (hi : i ∈ s) :
    P.typeBSpinRep b z hz
        (_root_.UniversalEnvelopingAlgebra.ι K (typeBSimpleRootGenerator i))
        (b.ExteriorAlgebra s) = 0 := by
  revert hi
  refine Fin.lastCases ?_ (fun j ↦ ?_) i
  · intro hi
    rw [typeBSimpleRootGenerator_last, P.typeBSpinRep_shortRootGenerator_apply b z hz]
    simp [hi]
  · intro hi
    have hne : (j.castSucc : Fin (n + 1)) ≠ j.succ := Fin.castSucc_lt_succ.ne
    rw [typeBSimpleRootGenerator_castSucc, P.typeBSpinRep_differenceRootGenerator_apply b z hz]
    simp [mul_smul_comm, hne, hi, Finset.mem_erase]

/-- **A positive simple type-`B` generator annihilates every exterior-basis vector whose index
set contains the generator's own coordinate.** The terminal generator creates a coordinate that
is already present, and a nonterminal one creates the coordinate it did not contract; the
all-coordinate vector is the case `s = Finset.univ`. -/
theorem typeBSpinLieRep_simpleRootGenerator_exteriorBasis_eq_zero_of_mem
    {i : Fin (n + 1)} {s : Finset (Fin (n + 1))} (hi : i ∈ s) :
    P.typeBSpinLieRep b z hz (typeBSimpleRootGenerator i) (b.ExteriorAlgebra s) = 0 := by
  have h := P.typeBSpinRep_simpleRootGenerator_exteriorBasis_eq_zero_of_mem b z hz hi
  rwa [_root_.UniversalEnvelopingAlgebra.ι_apply, P.typeBSpinRep_ι b z hz,
    ← P.typeBSpinLieRep_apply b z hz] at h

/-- **A vector annihilated by every positive simple-root generator is annihilated by the Lie
subalgebra they generate.** Annihilation is closed under brackets, so generatorwise vanishing
already gives vanishing on the whole Lie span. -/
theorem typeBSpinLieRep_lieSpan_range_simpleRootGenerator_le_lieAnnihilator
    {v : ExteriorAlgebra K P.W}
    (hv : ∀ i : Fin (n + 1), P.typeBSpinLieRep b z hz (typeBSimpleRootGenerator i) v = 0) :
    letI : LieRingModule (LieAlgebra.Orthogonal.typeB (Fin (n + 1)) K)
        (ExteriorAlgebra K P.W) :=
      LieRingModule.compLieHom _ (P.typeBSpinLieRep b z hz)
    letI : LieModule K (LieAlgebra.Orthogonal.typeB (Fin (n + 1)) K)
        (ExteriorAlgebra K P.W) :=
      LieModule.compLieHom _ (P.typeBSpinLieRep b z hz)
    LieSubalgebra.lieSpan K (LieAlgebra.Orthogonal.typeB (Fin (n + 1)) K)
        (Set.range (typeBSimpleRootGenerator (K := K))) ≤
      TauCeti.lieAnnihilator K _ v := by
  let _ : LieRingModule (LieAlgebra.Orthogonal.typeB (Fin (n + 1)) K)
      (ExteriorAlgebra K P.W) :=
    LieRingModule.compLieHom _ (P.typeBSpinLieRep b z hz)
  let _ : LieModule K (LieAlgebra.Orthogonal.typeB (Fin (n + 1)) K)
      (ExteriorAlgebra K P.W) :=
    LieModule.compLieHom _ (P.typeBSpinLieRep b z hz)
  refine TauCeti.lieSpan_le_lieAnnihilator K _ ?_
  rintro - ⟨i, rfl⟩
  simpa [LieRingModule.compLieHom_apply] using hv i

/-- **The Lie subalgebra generated by the positive simple-root generators annihilates the
all-coordinate exterior-basis vector.** Every coordinate is occupied, so every generator
annihilates it. -/
theorem typeBSpinLieRep_lieSpan_range_simpleRootGenerator_le_lieAnnihilator_exteriorBasis_univ :
    letI : LieRingModule (LieAlgebra.Orthogonal.typeB (Fin (n + 1)) K)
        (ExteriorAlgebra K P.W) :=
      LieRingModule.compLieHom _ (P.typeBSpinLieRep b z hz)
    letI : LieModule K (LieAlgebra.Orthogonal.typeB (Fin (n + 1)) K)
        (ExteriorAlgebra K P.W) :=
      LieModule.compLieHom _ (P.typeBSpinLieRep b z hz)
    LieSubalgebra.lieSpan K (LieAlgebra.Orthogonal.typeB (Fin (n + 1)) K)
        (Set.range (typeBSimpleRootGenerator (K := K))) ≤
      TauCeti.lieAnnihilator K _
        (b.ExteriorAlgebra (Finset.univ : Finset (Fin (n + 1)))) :=
  P.typeBSpinLieRep_lieSpan_range_simpleRootGenerator_le_lieAnnihilator b z hz fun i ↦
    P.typeBSpinLieRep_simpleRootGenerator_exteriorBasis_eq_zero_of_mem b z hz
      (Finset.mem_univ i)

end Quadratic

/-! ## The last fundamental weight -/

section Rational

variable {V : Type u} [AddCommGroup V] [Module ℚ V] {Q : QuadraticForm ℚ V}
  (P : SpinPolarizationData Q) {n : ℕ} (b : Module.Basis (Fin (n + 1)) ℚ P.W)
  (z : P.line) (hz : Q (z : V) = 1)

/-- **The all-coordinate exterior-basis vector has the last fundamental weight `ωₗ`** for the
type-`B` Cartan action. Together with
`typeBSpinLieRep_lieSpan_range_simpleRootGenerator_le_lieAnnihilator_exteriorBasis_univ`
this is the generator-level highest-weight datum of the type-`B` spin module. -/
theorem isCartanWeightVector_typeBSpinRep_exteriorBasis_univ :
    TauCeti.UniversalEnvelopingAlgebra.IsCartanWeightVector
      (typeBSimpleCorootGenerator (K := ℚ)) (P.typeBSpinRep b z hz)
      (Pi.single (Fin.last n) 1)
      (b.ExteriorAlgebra (Finset.univ : Finset (Fin (n + 1)))) := by
  simpa only [DynkinType.typeBSpinWeight_univ_eq_single] using
    P.isCartanWeightVector_typeBSpinRep_exteriorBasis b z hz
      (Finset.univ : Finset (Fin (n + 1)))

end Rational

/-! ## The weights in fundamental-weight coordinates -/

section CommRing

variable {K : Type u} [CommRing K] [Invertible (2 : K)] {n : ℕ}

/-- **A spin sign-vector weight evaluated on a numbered simple coroot is the corresponding
coordinate of the integral spin weight `DynkinType.typeBSpinWeight`.** At the terminal short node
the coroot is `2εₙ`, which doubles the half-integral entry `±½`; at a long node it is
`εⱼ - εⱼ₊₁`, which takes an adjacent difference of entries. -/
@[simp 1100]
theorem typeBWeightEquiv_spinWeight_apply_simpleCorootGenerator
    (s : Finset (Fin (n + 1))) (i : Fin (n + 1)) :
    typeBWeightEquiv (spinWeight K s)
        ⟨typeBSimpleCorootGenerator i, typeBSimpleCorootGenerator_mem_typeBDiagonalCartan i⟩ =
      (DynkinType.typeBSpinWeight s i : K) := by
  simp only [typeBWeightEquiv_apply, typeBSimpleCorootGenerator_eq_diagonal,
    coe_typeBDiagonalEquiv_apply, typeBDiagonalMatrix_apply, typeBDiagonalValue_inr_inl,
    ↓reduceIte]
  rw [← eq_intCast (algebraMap ℤ K), DynkinType.algebraMap_typeBSpinWeight_apply]
  refine Fin.lastCases ?_ (fun j ↦ ?_) i
  · simp [Pi.single_apply, mul_two]
  · simp [Fin.orderSucc_castSucc, Pi.single_apply, mul_sub, Finset.sum_sub_distrib]

end CommRing

section Field

variable {K : Type u} [Field K] [Invertible (2 : K)] {n : ℕ}

/-- **The spin weight of an exterior-basis vector in the fundamental-weight basis.** Expanded in
the basis dual to the simple coroots of `TauCeti.typeBLieBasis`, that is, in the fundamental
weights `ωᵢ` of `Bₙ₊₁`, the sign-vector weight of the index set `s` has the integral coefficients
`DynkinType.typeBSpinWeight s i`. -/
theorem typeBWeightEquiv_spinWeight_eq_sum_dualBasis (s : Finset (Fin (n + 1))) :
    typeBWeightEquiv (spinWeight K s) =
      ∑ i, (DynkinType.typeBSpinWeight s i : K) •
        (typeBLieBasis (K := K) n).cartanBasis.dualBasis i := by
  refine (typeBLieBasis (K := K) n).cartanBasis.ext fun i ↦ ?_
  have hcartan : (typeBLieBasis (K := K) n).cartanBasis i =
      ⟨typeBSimpleCorootGenerator i, typeBSimpleCorootGenerator_mem_typeBDiagonalCartan i⟩ :=
    Subtype.ext (by simp)
  rw [hcartan, typeBWeightEquiv_spinWeight_apply_simpleCorootGenerator, ← hcartan]
  simp [Finsupp.single_apply, -DynkinType.typeBSpinWeight_apply]

/-- **The all-coordinate spin weight is the last fundamental weight `ωₗ`**: the basis vector at
the terminal short node of the basis dual to the simple coroots of `TauCeti.typeBLieBasis`. -/
theorem typeBWeightEquiv_spinWeight_univ :
    typeBWeightEquiv (spinWeight K (Finset.univ : Finset (Fin (n + 1)))) =
      (typeBLieBasis (K := K) n).cartanBasis.dualBasis (Fin.last n) := by
  rw [typeBWeightEquiv_spinWeight_eq_sum_dualBasis, DynkinType.typeBSpinWeight_univ_eq_single]
  simp [Pi.single_apply]

variable {V : Type v} [AddCommGroup V] [Module K V] {Q : QuadraticForm K V}
  (P : SpinPolarizationData Q) (b : Module.Basis (Fin (n + 1)) K P.W)
  (z : P.line) (hz : Q (z : V) = 1)

/-- **The diagonal Cartan acts on the all-coordinate exterior-basis vector through the last
fundamental weight** of `TauCeti.typeBLieBasis`. Together with the annihilation by its raising
generators, `typeBSpinLieRep_simpleRootGenerator_exteriorBasis_eq_zero_of_mem`, this is the
highest-weight datum of the type-`B` spin module in the form consumed by the Lie-basis
characterization of highest-weight vectors. -/
theorem typeBSpinLieRep_apply_cartan_exteriorBasis_univ (A : typeBDiagonalCartan K (Fin (n + 1))) :
    P.typeBSpinLieRep b z hz (A : LieAlgebra.Orthogonal.typeB (Fin (n + 1)) K)
        (b.ExteriorAlgebra (Finset.univ : Finset (Fin (n + 1)))) =
      (typeBLieBasis (K := K) n).cartanBasis.dualBasis (Fin.last n) A •
        b.ExteriorAlgebra (Finset.univ : Finset (Fin (n + 1))) := by
  rw [P.typeBSpinLieRep_apply_cartan_exteriorBasis, typeBWeightEquiv_spinWeight_univ]

end Field

/-! ## The highest-weight vector -/

section HighestWeight

variable {K : Type u} [Field K] [CharZero K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {Q : QuadraticForm K V} (P : SpinPolarizationData Q)
  {n : ℕ} (b : Module.Basis (Fin (n + 1)) K P.W)
  (z : P.line) (hz : Q (z : V) = 1) [Invertible (2 : K)]
  [LieAlgebra.IsKilling K (LieAlgebra.Orthogonal.typeB (Fin (n + 1)) K)]

/-- **The all-coordinate spinor is a highest-weight vector of last fundamental weight.**
The base and Borel are those of `typeBLieBasis`; its Cartan basis consists of the simple
coroots, so the displayed dual basis vector is the abstract fundamental weight at the terminal
short node. -/
theorem isHighestWeightVector_typeBSpinLieRep_exteriorBasis_univ :
    letI := (typeBLieBasis (K := K) n).isCartanSubalgebra
    letI := (typeBLieBasis (K := K) n).isTriangularizable
    letI : LieRingModule (LieAlgebra.Orthogonal.typeB (Fin (n + 1)) K)
        (ExteriorAlgebra K P.W) :=
      LieRingModule.compLieHom _ (P.typeBSpinLieRep b z hz)
    letI : LieModule K (LieAlgebra.Orthogonal.typeB (Fin (n + 1)) K)
        (ExteriorAlgebra K P.W) :=
      LieModule.compLieHom _ (P.typeBSpinLieRep b z hz)
    IsHighestWeightVector (typeBLieBasis (K := K) n).base
      ((typeBLieBasis (K := K) n).cartanBasis.dualBasis (Fin.last n))
      (b.ExteriorAlgebra (Finset.univ : Finset (Fin (n + 1)))) := by
  let _ := (typeBLieBasis (K := K) n).isCartanSubalgebra
  let _ := (typeBLieBasis (K := K) n).isTriangularizable
  let _ : LieRingModule (LieAlgebra.Orthogonal.typeB (Fin (n + 1)) K)
      (ExteriorAlgebra K P.W) :=
    LieRingModule.compLieHom _ (P.typeBSpinLieRep b z hz)
  let _ : LieModule K (LieAlgebra.Orthogonal.typeB (Fin (n + 1)) K)
      (ExteriorAlgebra K P.W) :=
    LieModule.compLieHom _ (P.typeBSpinLieRep b z hz)
  rw [(typeBLieBasis (K := K) n).isHighestWeightVector_iff_forall_e]
  refine ⟨(b.ExteriorAlgebra).ne_zero _, ?_, ?_⟩
  · exact P.typeBSpinLieRep_apply_cartan_exteriorBasis_univ b z hz
  · intro i
    simpa only [typeBLieBasis_e, LieRingModule.compLieHom_apply, Module.End.lie_apply] using
      P.typeBSpinLieRep_simpleRootGenerator_exteriorBasis_eq_zero_of_mem b z hz
        (Finset.mem_univ i)

end HighestWeight

end SpinPolarizationData

end TauCeti
