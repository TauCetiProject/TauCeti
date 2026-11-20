/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.IntegralLattice.Binary.Determinant23.Basic
public import TauCeti.NumberTheory.IntegralLattice.Mass
import TauCeti.LinearAlgebra.IntegralLattice.Neighbor.BasisChange
import TauCeti.LinearAlgebra.IntegralLattice.StandardCoordinates
import TauCeti.NumberTheory.BinaryQuadraticForm.Reduction
import TauCeti.NumberTheory.IntegralLattice.Binary.NormOne
import TauCeti.NumberTheory.IntegralLattice.Neighbor

/-!
# The genus of the binary lattice of determinant 23

The genus of the lattice `!![4, 1; 1, 6]` separates the class number from the proper class number
and is the standard check of the rank-two mass `m = h⁺ / (2w)`. Its lattices are the positive
definite even lattices of rank two and determinant `23`, and they fall into two classes:

* the lattice `!![2, 1; 1, 12]`, with primitive norm form `x² + xy + 6y²`, whose isometry group
  has order four, with an improper automorphism because the form is properly equivalent to its
  reflection;
* the lattice `!![4, 1; 1, 6]`, with primitive norm form `2x² + xy + 3y²`, whose isometry group
  `{±1}` has order two and consists of proper isometries.

So the class number is `h = 2`, the second class splits into two proper classes, and the proper
class number is `h⁺ = 3`. With `w = 2` units in the quadratic order of discriminant `-23`, the
masses are

  `m = 1/4 + 1/2 = 3/4 = h⁺ / (2w)`, `m⁺ = 3/2 = h⁺ / w`,

whereas `h / (2w) = 1/2`.

Reduction of positive definite binary forms shows that every positive definite even lattice of
rank two and determinant `23` is isometric to one of the two lattices above, which are not
isometric because only the first has a vector of norm two. Equal rank, determinant and parity do
not by themselves place two lattices in one genus; here the genus is checked by exhibiting the
first as a Kneser `3`-neighbor of the second. In the rational space of `!![4, 1; 1, 6]` the vectors
`(2/3, -1/3)` and `(-1/3, -4/3)` span a lattice with Gram matrix `!![2, 1; 1, 12]`, and it meets
the standard lattice in a sublattice of index `3` in each. Neighbors at a prime not dividing
`2 · 23` lie in one genus.

## Main definitions

* `TauCeti.IntegralLattice.binaryDeterminant23Principal`: the lattice `!![2, 1; 1, 12]`.

## Main results

* `IsPosDef.nonempty_isometry_binaryDeterminant23Principal_or_binaryDeterminant23`: a positive
  definite even lattice of rank two and determinant `23` is isometric to `!![2, 1; 1, 12]` or to
  `!![4, 1; 1, 6]`.
* `TauCeti.IntegralLattice.sameGenus_binaryDeterminant23_binaryDeterminant23Principal`: the two
  lattices lie in one genus.
* `TauCeti.IntegralLattice.classNumber_binaryDeterminant23` and
  `TauCeti.IntegralLattice.properClassNumber_binaryDeterminant23`: `h = 2` and `h⁺ = 3`.
* `TauCeti.IntegralLattice.mass_binaryDeterminant23` and
  `TauCeti.IntegralLattice.properMass_binaryDeterminant23`: `m = 3/4` and `m⁺ = 3/2`.

## References

* D. A. Cox, *Primes of the Form x² + ny²*, §2, for reduced forms and the three classes of
  discriminant `-23`.
* J. H. Conway and N. J. A. Sloane, *Low-dimensional lattices. IV. The mass formula*,
  Proc. R. Soc. Lond. A 419 (1988), §2, equation (1).
* M. Kneser, *Klassenzahlen definiter quadratischer Formen*, Arch. Math. 8 (1957), 241--250.
-/

public section

open Module Matrix

namespace TauCeti.IntegralLattice

/-! ## The lattice `!![2, 1; 1, 12]` -/

private def principal23Matrix : Matrix (Fin 2) (Fin 2) ℤ := !![2, 1; 1, 12]

private theorem principal23Matrix_isSymm : principal23Matrix.IsSymm := by
  apply Matrix.IsSymm.ext
  intro i j
  fin_cases i <;> fin_cases j <;> rfl

/-- The integral binary lattice with Gram matrix `!![2, 1; 1, 12]`, whose primitive norm form
`x² + xy + 6y²` is the principal form of discriminant `-23`. -/
noncomputable def binaryDeterminant23Principal : IntegralLattice (Fin 2 → ℚ) :=
  ofGramMatrix (Pi.basisFun ℚ (Fin 2)) principal23Matrix principal23Matrix_isSymm

/-- The standard integral basis of `!![2, 1; 1, 12]`. -/
noncomputable def binaryDeterminant23PrincipalBasis :
    Basis (Fin 2) ℤ binaryDeterminant23Principal :=
  ofGramMatrix.basis (Pi.basisFun ℚ (Fin 2)) principal23Matrix principal23Matrix_isSymm

/-- The carrier basis is the standard coordinate basis. -/
@[simp] theorem coe_binaryDeterminant23PrincipalBasis (i : Fin 2) :
    (binaryDeterminant23PrincipalBasis i : Fin 2 → ℚ) = Pi.single i 1 :=
  (ofGramMatrix.coe_basis (Pi.basisFun ℚ (Fin 2)) principal23Matrix
    principal23Matrix_isSymm i).trans (Pi.basisFun_apply ℚ (Fin 2) i)

/-- Vectors of `!![2, 1; 1, 12]` have integral coordinates. -/
theorem mem_binaryDeterminant23Principal_carrier_iff (x : Fin 2 → ℚ) :
    x ∈ binaryDeterminant23Principal.carrier ↔ ∀ i, ∃ n : ℤ, (n : ℚ) = x i :=
  mem_ofGramMatrix_basisFun_carrier_iff _ _ x

/-- The displayed matrix is the Gram matrix in the standard integral basis. -/
@[simp] theorem gramMatrix_binaryDeterminant23PrincipalBasis :
    binaryDeterminant23Principal.gramMatrix binaryDeterminant23PrincipalBasis =
      !![2, 1; 1, 12] :=
  gramMatrix_ofGramMatrix _ _ _

/-- The norm form of `!![2, 1; 1, 12]` is `2x² + 2xy + 12y²`. -/
@[simp] theorem binaryDeterminant23Principal_binaryNormForm :
    binaryDeterminant23Principal.binaryNormForm binaryDeterminant23PrincipalBasis =
      ⟨2, 2, 12⟩ := by
  ext <;> simp only [binaryNormForm_a, binaryNormForm_b, binaryNormForm_c,
    gramMatrix_binaryDeterminant23PrincipalBasis] <;> norm_num

/-- Its primitive norm form is the principal form `x² + xy + 6y²`. -/
theorem binaryDeterminant23Principal_primPart :
    (binaryDeterminant23Principal.binaryNormForm binaryDeterminant23PrincipalBasis).primPart =
      ⟨1, 1, 6⟩ := by
  rw [binaryDeterminant23Principal_binaryNormForm]
  ext <;> norm_num [BinaryQuadraticForm.primPart_a, BinaryQuadraticForm.primPart_b,
    BinaryQuadraticForm.primPart_c, BinaryQuadraticForm.content_def]

/-- Its primitive discriminant is minus 23. -/
@[simp] theorem binaryDeterminant23Principal_binaryDiscriminant :
    binaryDeterminant23Principal.binaryDiscriminant (by simp) = -23 := by
  rw [binaryDiscriminant_eq_discrim_primPart _ binaryDeterminant23PrincipalBasis,
    binaryDeterminant23Principal_primPart]
  norm_num [BinaryQuadraticForm.discrim_def, discrim]

/-- The first basis vector of `!![2, 1; 1, 12]` has norm two. -/
theorem binaryDeterminant23Principal_integralNorm_basis_zero :
    binaryDeterminant23Principal.integralNorm (binaryDeterminant23PrincipalBasis 0) = 2 := by
  simp [integralNorm_apply, ← gramMatrix_apply]

/-- **The two lattices of determinant 23 are not isometric**: `!![2, 1; 1, 12]` has a vector of
norm two, while every nonzero vector of `!![4, 1; 1, 6]` has norm at least four. -/
instance : IsEmpty (Isometry binaryDeterminant23Principal binaryDeterminant23) := by
  refine ⟨fun e ↦ ?_⟩
  have h := binaryDeterminant23_four_le_integralNorm
    (e.carrierEquiv.map_ne_zero_iff.mpr (binaryDeterminant23PrincipalBasis.ne_zero 0))
  rw [integralNorm_apply, Isometry.carrierEquiv_map_integralForm, ← integralNorm_apply,
    binaryDeterminant23Principal_integralNorm_basis_zero] at h
  omega

/-! ## Classification by reduction -/

/-- The reduced forms of discriminant `-92` with even leading coefficient are
`2x² + 2xy + 12y²` and `4x² ± 2xy + 6y²`. -/
private theorem eq_of_mem_reducedForms_92 :
    ∀ f ∈ reducedForms 92, f.a % 2 = 0 →
      (f.a = 2 ∧ f.b = 2 ∧ f.c = 12) ∨
      (f.a = 4 ∧ f.b = 2 ∧ f.c = 6) ∨ (f.a = 4 ∧ f.b = -2 ∧ f.c = 6) := by
  decide +kernel

variable {V : Type*} [AddCommGroup V] [Module ℚ V] {L : IntegralLattice V}

/-- A positive definite even binary lattice of determinant 23 has a basis with norm form
`2x² + 2xy + 12y²` or `4x² + 2xy + 6y²`. -/
private theorem IsPosDef.exists_binaryNormForm_eq_of_determinant_eq_23 (hL : L.IsPosDef)
    (he : L.IsEven) (hn : finrank ℤ L = 2) (hd : L.determinant = 23) :
    ∃ b : Basis (Fin 2) ℤ L,
      L.binaryNormForm b = ⟨2, 2, 12⟩ ∨ L.binaryNormForm b = ⟨4, 2, 6⟩ := by
  let b := Module.finBasisOfFinrankEq ℤ L hn
  have hf : L.binaryNormForm b ∈ BinaryQuadraticForm.posDef 92 := by
    refine BinaryQuadraticForm.mem_posDef.mpr ⟨?_, ?_⟩
    · rw [discrim_binaryNormForm, hd]; norm_num
    · rw [binaryNormForm_a, gramMatrix_apply, ← integralNorm_apply]
      exact hL.posDef_integralNorm _ (b.ne_zero 0)
  obtain ⟨γ, hγ⟩ := BinaryQuadraticForm.exists_smul_isReducedForm ⟨_, hf⟩
  obtain ⟨b', hb'⟩ := L.exists_binaryNormForm_eq_smul b γ
  have hr : IsReducedForm (L.binaryNormForm b') := by
    simpa only [hb', SubMulAction.val_smul] using hγ
  have hea : Even (L.binaryNormForm b').a := by
    simpa only [binaryNormForm_a, gramMatrix_apply, ← integralNorm_apply] using
      (L.isEven_iff_basis b').mp he 0
  have hmem : L.binaryNormForm b' ∈ reducedForms 92 :=
    (mem_reducedForms (by decide : 92 ≠ 0)).mpr
      ⟨by rw [discrim_binaryNormForm, hd]; norm_num, hr⟩
  rcases eq_of_mem_reducedForms_92 _ hmem (Int.even_iff.mp hea) with
    ⟨ha, hb, hc⟩ | ⟨ha, hb, hc⟩ | ⟨ha, hb, hc⟩
  · exact ⟨b', Or.inl (BinaryQuadraticForm.ext ha hb hc)⟩
  · exact ⟨b', Or.inr (BinaryQuadraticForm.ext ha hb hc)⟩
  · refine ⟨b'.unitsSMul (Function.update 1 (1 : Fin 2) (-1)), Or.inr ?_⟩
    have hf : L.binaryNormForm b' = ⟨4, -2, 6⟩ := BinaryQuadraticForm.ext ha hb hc
    rw [binaryNormForm_unitsSMul_neg, hf]
    ext <;> norm_num [BinaryQuadraticForm.reflected_a, BinaryQuadraticForm.reflected_b,
      BinaryQuadraticForm.reflected_c]

/-- **Classification of the even binary lattices of determinant 23.** A positive definite even
lattice of rank two and determinant `23` is isometric to `!![2, 1; 1, 12]` or to
`!![4, 1; 1, 6]`. -/
theorem IsPosDef.nonempty_isometry_binaryDeterminant23Principal_or_binaryDeterminant23
    (hL : L.IsPosDef) (he : L.IsEven) (hn : finrank ℤ L = 2) (hd : L.determinant = 23) :
    Nonempty (Isometry L binaryDeterminant23Principal) ∨
      Nonempty (Isometry L binaryDeterminant23) := by
  obtain ⟨b, hb | hb⟩ := hL.exists_binaryNormForm_eq_of_determinant_eq_23 he hn hd
  · obtain ⟨e, -⟩ := (exists_isometry_map_basis_iff b binaryDeterminant23PrincipalBasis).mpr
      (by rw [hb, binaryDeterminant23Principal_binaryNormForm])
    exact Or.inl ⟨e⟩
  · obtain ⟨e, -⟩ := (exists_isometry_map_basis_iff b binaryDeterminant23Basis).mpr
      (by rw [hb, binaryDeterminant23_binaryNormForm])
    exact Or.inr ⟨e⟩

/-! ## The two lattices lie in one genus -/

/-- The vectors `(2/3, -1/3)` and `(-1/3, -4/3)` of `ℚ²`. -/
private def neighborVectors : Fin 2 → Fin 2 → ℚ := ![![2 / 3, -1 / 3], ![-1 / 3, -4 / 3]]

private theorem linearIndependent_neighborVectors : LinearIndependent ℚ neighborVectors := by
  refine LinearIndependent.pair_iff.mpr fun s t h ↦ ?_
  have h0 := congrFun h 0
  have h1 := congrFun h 1
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Pi.add_apply,
    Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at h0 h1
  constructor <;> linarith

/-- The rational basis `(2/3, -1/3), (-1/3, -4/3)` of `ℚ²`. -/
private noncomputable def neighborBasis : Basis (Fin 2) ℚ (Fin 2 → ℚ) :=
  basisOfLinearIndependentOfCardEqFinrank' neighborVectors linearIndependent_neighborVectors
    (by simp)

private theorem neighborBasis_apply (i : Fin 2) : neighborBasis i = neighborVectors i := by
  exact congrFun (coe_basisOfLinearIndependentOfCardEqFinrank' _ _ _) i

/-- The lattice spanned by `(2/3, -1/3), (-1/3, -4/3)`, with Gram matrix `!![2, 1; 1, 12]`. -/
private noncomputable def neighborLattice : IntegralLattice (Fin 2 → ℚ) :=
  ofGramMatrix neighborBasis principal23Matrix principal23Matrix_isSymm

/-- The form of the lattice spanned by `(2/3, -1/3), (-1/3, -4/3)` on its defining basis. -/
private theorem neighborLattice_form_apply (i j : Fin 2) :
    neighborLattice.form (neighborBasis i) (neighborBasis j) = principal23Matrix i j := by
  have h := congrArg (Int.cast : ℤ → ℚ)
    (integralForm_ofGramMatrix_apply neighborBasis principal23Matrix principal23Matrix_isSymm i j)
  rwa [integralForm_cast, ofGramMatrix.coe_basis, ofGramMatrix.coe_basis] at h

/-- The form of `!![4, 1; 1, 6]` has Gram matrix `!![2, 1; 1, 12]` in the basis
`(2/3, -1/3), (-1/3, -4/3)`. -/
private theorem binaryDeterminant23_form_eq_neighborLattice_form :
    binaryDeterminant23.form = neighborLattice.form := by
  refine LinearMap.BilinForm.ext_basis neighborBasis fun i j ↦ ?_
  rw [neighborLattice_form_apply, binaryDeterminant23_form_apply, neighborBasis_apply,
    neighborBasis_apply]
  fin_cases i <;> fin_cases j <;> norm_num [neighborVectors, principal23Matrix]

/-- **`!![2, 1; 1, 12]` is a `3`-neighbor of `!![4, 1; 1, 6]`.** The change of basis from the
standard basis to `(2/3, -1/3), (-1/3, -4/3)` passes the neighbor test. -/
private theorem isNeighbor_binaryDeterminant23_neighborLattice :
    binaryDeterminant23.IsNeighbor neighborLattice 3 := by
  have hA : (Pi.basisFun ℚ (Fin 2)).toMatrix neighborBasis =
      !![2 / 3, -1 / 3; -1 / 3, -4 / 3] := by
    ext i j
    rw [Basis.toMatrix_apply, Pi.basisFun_repr, neighborBasis_apply]
    fin_cases i <;> fin_cases j <;> rfl
  rw [isNeighbor_iff_isNeighborBasisChange (Pi.basisFun ℚ (Fin 2)) neighborBasis
    binaryDeterminant23_carrier (by rw [neighborLattice, ofGramMatrix_carrier])
    binaryDeterminant23_form_eq_neighborLattice_form, hA]
  decide +kernel

/-- **The lattices `!![2, 1; 1, 12]` and `!![4, 1; 1, 6]` lie in one genus.** The first is
isometric to a Kneser `3`-neighbor of the second, and `3` is prime to `2 · 23`. -/
theorem sameGenus_binaryDeterminant23_binaryDeterminant23Principal :
    binaryDeterminant23.SameGenus binaryDeterminant23Principal := by
  have hN := isNeighbor_binaryDeterminant23_neighborLattice.sameGenus (by norm_num)
  refine hN.trans (Isometry.sameGenus (Isometry.ofGramMatrixEq
    (ofGramMatrix.basis neighborBasis principal23Matrix principal23Matrix_isSymm)
    binaryDeterminant23PrincipalBasis ?_))
  rw [gramMatrix_binaryDeterminant23PrincipalBasis]
  exact gramMatrix_ofGramMatrix _ _ _

/-- Its Gram determinant is 23. -/
@[simp] theorem binaryDeterminant23Principal_determinant :
    binaryDeterminant23Principal.determinant = 23 :=
  sameGenus_binaryDeterminant23_binaryDeterminant23Principal.determinant_eq.symm.trans
    binaryDeterminant23_determinant

/-- The lattice `!![2, 1; 1, 12]` is even. -/
theorem binaryDeterminant23Principal_isEven : binaryDeterminant23Principal.IsEven :=
  sameGenus_binaryDeterminant23_binaryDeterminant23Principal.isEven_iff.mp
    binaryDeterminant23_isEven

/-- The lattice `!![2, 1; 1, 12]` is positive definite. -/
theorem binaryDeterminant23Principal_isPosDef : binaryDeterminant23Principal.IsPosDef :=
  sameGenus_binaryDeterminant23_binaryDeterminant23Principal.isPosDef_iff.mp
    binaryDeterminant23_isPosDef

/-! ## Classes, proper classes and masses -/

/-- **The genus of `!![4, 1; 1, 6]` consists of two classes**, those of `!![2, 1; 1, 12]` and
`!![4, 1; 1, 6]`. -/
theorem genusClasses_binaryDeterminant23 :
    binaryDeterminant23.genusClasses =
      {binaryDeterminant23Principal.isometryClass, binaryDeterminant23.isometryClass} := by
  ext c
  obtain ⟨M, rfl⟩ := isometryClass_surjective c
  rw [isometryClass_mem_genusClasses_iff, Set.mem_insert_iff, Set.mem_singleton_iff, eq_comm,
    isometryClass_eq_isometryClass_iff, eq_comm (b := binaryDeterminant23.isometryClass),
    isometryClass_eq_isometryClass_iff]
  constructor
  · intro h
    rcases IsPosDef.nonempty_isometry_binaryDeterminant23Principal_or_binaryDeterminant23
      (h.isPosDef_iff.mp binaryDeterminant23_isPosDef)
      (h.isEven_iff.mp binaryDeterminant23_isEven)
      (h.finrank_eq.symm.trans (by rw [finrank_carrier, Module.finrank_fin_fun]))
      (h.determinant_eq.symm.trans binaryDeterminant23_determinant) with e | e
    · exact Or.inl ⟨e.some.symm⟩
    · exact Or.inr ⟨e.some.symm⟩
  · rintro (e | e)
    · exact sameGenus_binaryDeterminant23_binaryDeterminant23Principal.trans e.some.sameGenus
    · exact e.some.sameGenus

/-- The classes of `!![2, 1; 1, 12]` and `!![4, 1; 1, 6]` are distinct. -/
private theorem isometryClass_binaryDeterminant23Principal_ne :
    binaryDeterminant23Principal.isometryClass ≠ binaryDeterminant23.isometryClass := fun h ↦
  (isometryClass_eq_isometryClass_iff.mp h).elim isEmptyElim

/-- **The class number of the genus of `!![4, 1; 1, 6]` is two.** -/
@[simp]
theorem classNumber_binaryDeterminant23 : binaryDeterminant23.classNumber = 2 := by
  rw [classNumber_def, genusClasses_binaryDeterminant23, Nat.card_coe_set_eq,
    Set.ncard_pair isometryClass_binaryDeterminant23Principal_ne]

/-- **`!![2, 1; 1, 12]` has an orientation-reversing automorphism**: its primitive norm form
`x² + xy + 6y²` is properly equivalent to its reflection `x² - xy + 6y²`. So its proper isometry
subgroup has index two. -/
theorem index_specialOrthogonalGroup_binaryDeterminant23Principal :
    (specialOrthogonalGroup binaryDeterminant23Principal).index = 2 := by
  rw [index_specialOrthogonalGroup_eq_two_iff_reflected binaryDeterminant23PrincipalBasis,
    binaryDeterminant23Principal_primPart]
  refine ⟨ModularGroup.T ^ (-1 : ℤ), ?_⟩
  rw [BinaryQuadraticForm.T_zpow_smul]
  ext <;> norm_num [BinaryQuadraticForm.reflected_a, BinaryQuadraticForm.reflected_b,
    BinaryQuadraticForm.reflected_c]

/-- The proper isometry group of `!![2, 1; 1, 12]` has order two, the number of units of the
quadratic order of discriminant `-23`. -/
theorem card_specialOrthogonalGroup_binaryDeterminant23Principal :
    Nat.card (specialOrthogonalGroup binaryDeterminant23Principal) = 2 := by
  have hV : Module.finrank ℚ (Fin 2 → ℚ) = 2 := Module.finrank_fin_fun ℚ
  rw [card_specialOrthogonalGroup_of_binaryDiscriminant_neg hV
    (by rw [binaryDeterminant23Principal_binaryDiscriminant]; norm_num), binaryOrder_def,
    QuadraticOrder.card_units_of_neg _ _
      (by rw [binaryDeterminant23Principal_binaryDiscriminant]; norm_num),
    binaryDeterminant23Principal_binaryDiscriminant]
  norm_num

/-- The full isometry group of `!![2, 1; 1, 12]` has order four. -/
@[simp]
theorem card_isometry_binaryDeterminant23Principal :
    Nat.card (Isometry binaryDeterminant23Principal binaryDeterminant23Principal) = 4 := by
  rw [← (specialOrthogonalGroup binaryDeterminant23Principal).card_mul_index,
    card_specialOrthogonalGroup_binaryDeterminant23Principal,
    index_specialOrthogonalGroup_binaryDeterminant23Principal]

/-- **The proper class number of the genus of `!![4, 1; 1, 6]` is three**: the class of
`!![2, 1; 1, 12]` is one proper class and that of `!![4, 1; 1, 6]` splits into two. -/
@[simp]
theorem properClassNumber_binaryDeterminant23 : binaryDeterminant23.properClassNumber = 3 := by
  have hV : 0 < Module.finrank ℚ (Fin 2 → ℚ) := by simp
  have hfin : binaryDeterminant23.genusClasses.Finite := by
    rw [genusClasses_binaryDeterminant23]
    exact Set.toFinite _
  have hP := natCard_preimage_toIsometryQuotient_mul_index binaryDeterminant23Principal hV
  have hL := natCard_preimage_toIsometryQuotient_mul_index binaryDeterminant23 hV
  rw [index_specialOrthogonalGroup_binaryDeterminant23Principal] at hP
  rw [index_specialOrthogonalGroup_binaryDeterminant23, mul_one] at hL
  classical
  have hT : hfin.toFinset =
      {binaryDeterminant23Principal.isometryClass, binaryDeterminant23.isometryClass} := by
    ext c
    simp [genusClasses_binaryDeterminant23]
  rw [properClassNumber_eq_sum hfin, hT,
    Finset.sum_pair isometryClass_binaryDeterminant23Principal_ne, hL]
  omega

/-- **The mass of the genus of `!![4, 1; 1, 6]` is `3/4`**: `1/4 + 1/2`, from the classes of
`!![2, 1; 1, 12]` and `!![4, 1; 1, 6]`. It equals `h⁺ / (2w)` with `h⁺ = 3` and `w = 2`, not
`h / (2w) = 1/2`. -/
@[simp]
theorem mass_binaryDeterminant23 : binaryDeterminant23.mass = 3 / 4 := by
  have hcard (M : IntegralLattice (Fin 2 → ℚ)) :
      Nat.card (Isometry M.isometryClass.out M.isometryClass.out) =
        Nat.card (Isometry M M) := by
    obtain ⟨e⟩ := isometryClass_eq_isometryClass_iff.mp (isometryClass_out M.isometryClass)
    exact e.natCard_isometry_eq
  rw [mass_def, genusClasses_binaryDeterminant23,
    finsum_mem_pair isometryClass_binaryDeterminant23Principal_ne, hcard, hcard,
    card_isometry_binaryDeterminant23Principal, card_isometry_binaryDeterminant23]
  norm_num

/-- **The proper mass of the genus of `!![4, 1; 1, 6]` is `3/2`**, which is `h⁺ / w`. -/
@[simp]
theorem properMass_binaryDeterminant23 : binaryDeterminant23.properMass = 3 / 2 := by
  rw [properMass_eq_two_mul_mass binaryDeterminant23_isPosDef.finite_genusClasses
    (by rw [finrank_carrier, Module.finrank_fin_fun]; norm_num), mass_binaryDeterminant23]
  norm_num

end TauCeti.IntegralLattice
