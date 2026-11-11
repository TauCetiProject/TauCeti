/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.SpringSystem.Tetrahedron.Basic
public import TauCeti.RepresentationTheory.Symmetric.Four.Basic
import TauCeti.RepresentationTheory.Induction.Permutation

/-!
# The symmetry module of the spring tetrahedron and its displacement character

The symmetries `R_σ` of the regular tetrahedron with centred vertices `q₀, …, q₃`
(`TauCeti.tetrahedronSymmetryMatrix`) make `ℝ³` a representation of `S₄ = Equiv.Perm (Fin 4)`.
This file identifies it with the standard representation `V` of `S₄`, the sum-zero vectors of
`ℝ[Fin 4]`: the frame map `f ↦ ∑ᵢ f(i) qᵢ` is an `S₄`-equivariant linear equivalence, with
inverse `x ↦ ∑ᵢ (qᵢ ⬝ x) δᵢ`, and it is an isometry for the standard inner products, because
the Gram matrix of the centred vertices is `I - ¼ J` and `J` vanishes on sum-zero vectors.

On the twelve-dimensional displacement representation `(σ • u)ᵢ = R_σ u_{σ⁻¹ i}`
(`TauCeti.tetrahedronDisplacementRep`) only the blocks of the fixed vertices contribute to the
trace, so its character is the product of the permutation character of the four vertices and
the character of `ℝ³`. Writing `f(σ)` for the number of fixed points of `σ`, it is
`f(σ) (f(σ) - 1)`: in the class order `1, (01), (01)(23), (012), (0123)` of
`TauCeti.symmetricGroupFourClassData` it takes the values `(12, 2, 0, 0, 0)`. Comparing with the
rows of `TauCeti.symmetricGroupFourCharacterTable` gives the character identity
`χ = 1 + χ_E + 2 χ_V + χ_{sgn ⊗ V}`, the character form of the decomposition
`1 ⊕ E ⊕ 2V ⊕ (sgn ⊗ V)` of the displacements; the summands themselves are not constructed here.

## Main definitions

* `TauCeti.tetrahedronSymmetryRep`: the representation `σ ↦ R_σ` of `S₄` on `ℝ³`.
* `TauCeti.tetrahedronStandardEquiv`: the frame map, an equivalence of representations from the
  standard representation of `S₄` to `ℝ³`.

## Main results

* `TauCeti.dotProduct_tetrahedronStandardEquiv`: the frame map is an isometry.
* `TauCeti.trace_tetrahedronSymmetryMatrix`: `tr R_σ = f(σ) - 1`.
* `TauCeti.char_tetrahedronDisplacementRep`: the displacement character is `f(σ) (f(σ) - 1)`.
* `TauCeti.char_tetrahedronDisplacementRep_symmetricGroupFourClassData_rep`: its values
  `(12, 2, 0, 0, 0)` on the classes of `S₄`.
* `TauCeti.char_tetrahedronDisplacementRep_eq`: the identity `χ = 1 + χ_E + 2 χ_V + χ_{sgn ⊗ V}`.

## References

* A. Knutson, *Group theory in physics: an example*, tetrahedron handout for Math 261 (Cornell,
  2001), pp. 3–5.
* W. Fulton and J. Harris, *Representation Theory: A First Course*, Springer GTM 129 (1991),
  §2.3, for the standard representation of `S₄` as the orthogonal symmetries of the
  tetrahedron.
-/

public section

namespace TauCeti

open Matrix Equiv

/-! ### The symmetry representation on `ℝ³` -/

/-- The representation of `S₄` on `ℝ³` by the symmetries `R_σ` of the tetrahedron, which map the
centred vertex `qᵢ` to `q_{σ i}` (`TauCeti.tetrahedronSymmetryMatrix_mulVec`). -/
noncomputable def tetrahedronSymmetryRep : Representation ℝ (Perm (Fin 4)) (Fin 3 → ℝ) :=
  Matrix.toLinAlgEquiv'.toAlgHom.toMonoidHom.comp tetrahedronSymmetryMatrix

/-- `σ` acts on `ℝ³` by multiplication with `R_σ`. -/
@[simp]
theorem tetrahedronSymmetryRep_apply (σ : Perm (Fin 4)) (x : Fin 3 → ℝ) :
    tetrahedronSymmetryRep σ x = tetrahedronSymmetryMatrix σ *ᵥ x :=
  (rfl)

/-- The character of the symmetry representation is the trace of `R_σ`. -/
theorem char_tetrahedronSymmetryRep (σ : Perm (Fin 4)) :
    tetrahedronSymmetryRep.character σ = (tetrahedronSymmetryMatrix σ).trace :=
  Matrix.trace_toLin'_eq _

/-! ### The frame map from the standard representation -/

/-- The centred vertices recover the coefficients of a sum-zero vector from its frame image:
`qⱼ ⬝ ∑ᵢ f(i) qᵢ = f(j) - ¼ ∑ᵢ f(i) = f(j)`. -/
private theorem dotProduct_sum_coeff_smul_tetrahedronCenteredVertex
    {v : MonoidAlgebra ℝ (Fin 4)} (hv : v ∈ augmentationSubrepresentation ℝ (Perm (Fin 4)) (Fin 4))
    (j : Fin 4) :
    tetrahedronCenteredVertex j ⬝ᵥ ∑ i, v.coeff i • tetrahedronCenteredVertex i = v.coeff j := by
  rw [mem_augmentationSubrepresentation_iff, Module.Basis.coe_sumCoords_of_fintype] at hv
  have h := sum_dotProduct_tetrahedronCenteredVertex_smul (fun i ↦ v.coeff i) j
  have hv' : ∑ i, v.coeff i = 0 := by simpa using hv
  simp only [smul_eq_mul, hv', mul_zero, sub_zero] at h
  simp only [dotProduct_sum, dotProduct_smul, smul_eq_mul]
  rw [← h]
  exact Finset.sum_congr rfl fun i _ ↦ by rw [dotProduct_comm, mul_comm]

/-- The frame map `f ↦ ∑ᵢ f(i) qᵢ` from the sum-zero vectors of `ℝ[Fin 4]` to `ℝ³`, as a linear
equivalence with inverse `x ↦ ∑ᵢ (qᵢ ⬝ x) δᵢ`. -/
private noncomputable def tetrahedronStandardLinearEquiv :
    (augmentationSubrepresentation ℝ (Perm (Fin 4)) (Fin 4)).toSubmodule ≃ₗ[ℝ] (Fin 3 → ℝ) where
  toFun v := ∑ i, (v : MonoidAlgebra ℝ (Fin 4)).coeff i • tetrahedronCenteredVertex i
  map_add' v w := by simp [add_smul, Finset.sum_add_distrib]
  map_smul' c v := by simp [Finset.smul_sum, smul_smul]
  invFun x := ⟨∑ i, MonoidAlgebra.single i (tetrahedronCenteredVertex i ⬝ᵥ x), by
    refine mem_augmentationSubrepresentation_iff.2 ?_
    rw [Module.Basis.coe_sumCoords_of_fintype]
    simp [Finsupp.single_apply, ← sum_dotProduct, sum_tetrahedronCenteredVertex]⟩
  left_inv v := by
    ext j
    simp [MonoidAlgebra.coeff_sum, dotProduct_sum_coeff_smul_tetrahedronCenteredVertex v.2]
  right_inv x := by
    have h := congrArg (· *ᵥ x) sum_vecMulVec_tetrahedronCenteredVertex
    simp only [Matrix.sum_mulVec, vecMulVec_mulVec, op_smul_eq_smul, one_mulVec] at h
    simpa [MonoidAlgebra.coeff_sum, Finsupp.single_apply] using h

private theorem tetrahedronStandardLinearEquiv_apply
    (v : (augmentationSubrepresentation ℝ (Perm (Fin 4)) (Fin 4)).toSubmodule) :
    tetrahedronStandardLinearEquiv v =
      ∑ i, (v : MonoidAlgebra ℝ (Fin 4)).coeff i • tetrahedronCenteredVertex i :=
  (rfl)

/-- **The tetrahedron realizes the standard representation of `S₄`.** The frame map
`f ↦ ∑ᵢ f(i) qᵢ` is an equivalence of representations from the standard representation of `S₄`
on the sum-zero vectors of `ℝ[Fin 4]` to the symmetry representation on `ℝ³`; its inverse is
`x ↦ ∑ᵢ (qᵢ ⬝ x) δᵢ` (`TauCeti.coeff_tetrahedronStandardEquiv_symm_apply`). -/
noncomputable def tetrahedronStandardEquiv :
    (standardRepresentation ℝ (Fin 4)).Equiv tetrahedronSymmetryRep :=
  .mk tetrahedronStandardLinearEquiv fun σ ↦ LinearMap.ext fun v ↦ by
    simp only [LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply,
      tetrahedronSymmetryRep_apply, tetrahedronStandardLinearEquiv_apply,
      coe_standardRepresentation_apply, Representation.coeff_ofMulAction, Matrix.mulVec_sum,
      Matrix.mulVec_smul, tetrahedronSymmetryMatrix_mulVec]
    rw [← Equiv.sum_comp σ]
    simp [Perm.smul_def]

/-- The frame map sends a sum-zero vector `f` to `∑ᵢ f(i) qᵢ`. -/
theorem tetrahedronStandardEquiv_apply
    (v : (augmentationSubrepresentation ℝ (Perm (Fin 4)) (Fin 4)).toSubmodule) :
    tetrahedronStandardEquiv v =
      ∑ i, (v : MonoidAlgebra ℝ (Fin 4)).coeff i • tetrahedronCenteredVertex i :=
  (rfl)

/-- The inverse of the frame map sends `x` to `∑ᵢ (qᵢ ⬝ x) δᵢ`. -/
theorem coe_tetrahedronStandardEquiv_symm_apply (x : Fin 3 → ℝ) :
    (tetrahedronStandardEquiv.symm x : MonoidAlgebra ℝ (Fin 4)) =
      ∑ i, MonoidAlgebra.single i (tetrahedronCenteredVertex i ⬝ᵥ x) :=
  (rfl)

/-- The `j`-th coefficient of the inverse frame image of `x` is `qⱼ ⬝ x`. -/
@[simp]
theorem coeff_tetrahedronStandardEquiv_symm_apply (x : Fin 3 → ℝ) (j : Fin 4) :
    (tetrahedronStandardEquiv.symm x : MonoidAlgebra ℝ (Fin 4)).coeff j =
      tetrahedronCenteredVertex j ⬝ᵥ x := by
  simp [coe_tetrahedronStandardEquiv_symm_apply, MonoidAlgebra.coeff_sum, Finsupp.single_apply]

/-- The centred vertex `qⱼ` reads off the `j`-th coefficient of a sum-zero vector from its frame
image. -/
@[simp]
theorem dotProduct_tetrahedronStandardEquiv
    (v : (augmentationSubrepresentation ℝ (Perm (Fin 4)) (Fin 4)).toSubmodule) (j : Fin 4) :
    tetrahedronCenteredVertex j ⬝ᵥ tetrahedronStandardEquiv v =
      (v : MonoidAlgebra ℝ (Fin 4)).coeff j :=
  dotProduct_sum_coeff_smul_tetrahedronCenteredVertex v.2 j

/-- **The frame map is an isometry**: the standard inner product of the frame images of two
sum-zero vectors is the standard inner product `∑ᵢ f(i) g(i)` of their coefficients. -/
theorem dotProduct_tetrahedronStandardEquiv_tetrahedronStandardEquiv
    (v w : (augmentationSubrepresentation ℝ (Perm (Fin 4)) (Fin 4)).toSubmodule) :
    tetrahedronStandardEquiv v ⬝ᵥ tetrahedronStandardEquiv w =
      ∑ i, (v : MonoidAlgebra ℝ (Fin 4)).coeff i * (w : MonoidAlgebra ℝ (Fin 4)).coeff i := by
  conv_lhs => rw [tetrahedronStandardEquiv_apply w]
  simp only [dotProduct_sum, dotProduct_smul, smul_eq_mul]
  exact Finset.sum_congr rfl fun i _ ↦ by
    rw [dotProduct_comm, dotProduct_tetrahedronStandardEquiv, mul_comm]

/-! ### Characters -/

/-- **The trace of a tetrahedral symmetry** `R_σ` is one less than the number of fixed points of
`σ`, the character of the standard representation of `S₄`. -/
theorem trace_tetrahedronSymmetryMatrix (σ : Perm (Fin 4)) :
    (tetrahedronSymmetryMatrix σ).trace = Nat.card {i : Fin 4 // σ i = i} - 1 := by
  rw [← char_tetrahedronSymmetryRep, ← Representation.char_iso tetrahedronStandardEquiv,
    char_standardRepresentation, char_ofMulAction]
  simp only [Perm.smul_def]

/-- **The displacement character of the spring tetrahedron** is `f(σ) (f(σ) - 1)`, where `f(σ)`
is the number of fixed points of `σ`: only the blocks of the fixed vertices contribute to the
trace, each with `tr R_σ = f(σ) - 1`. -/
theorem char_tetrahedronDisplacementRep (σ : Perm (Fin 4)) :
    tetrahedronDisplacementRep.character σ =
      Nat.card {i : Fin 4 // σ i = i} * (Nat.card {i : Fin 4 // σ i = i} - 1) := by
  rw [← trace_tetrahedronSymmetryMatrix, Representation.character,
    LinearMap.trace_eq_matrix_trace ℝ (Pi.basisFun ℝ _), Matrix.trace]
  have h (i : Fin 4) (k : Fin 3) :
      LinearMap.toMatrix (Pi.basisFun ℝ _) (Pi.basisFun ℝ _) (tetrahedronDisplacementRep σ)
        (i, k) (i, k) = if σ i = i then tetrahedronSymmetryMatrix σ k k else 0 := by
    have hc := congrFun (curry_tetrahedronDisplacementRep σ (Pi.single (i, k) 1) i) k
    rw [Function.curry_apply] at hc
    rw [LinearMap.toMatrix_apply, Pi.basisFun_apply, Pi.basisFun_repr, hc]
    by_cases hi : σ i = i
    · have : σ.symm i = i := by rw [Equiv.symm_apply_eq, hi]
      simp [this, hi]
    · have : σ.symm i ≠ i := by rwa [Ne, Equiv.symm_apply_eq, eq_comm]
      simp [this, hi]
  have hs (i : Fin 4) : ∑ k, (if σ i = i then tetrahedronSymmetryMatrix σ k k else 0) =
      if σ i = i then (tetrahedronSymmetryMatrix σ).trace else 0 := by
    split_ifs <;> simp [Matrix.trace]
  simp only [Fintype.sum_prod_type, Matrix.diag_apply, h]
  simp only [hs]
  rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul,
    Nat.card_eq_fintype_card, Fintype.card_subtype]

/-- **The displacement character on the classes of `S₄`**: `(12, 2, 0, 0, 0)` at the class
representatives `1, (01), (01)(23), (012), (0123)` of `TauCeti.symmetricGroupFourClassData`. -/
theorem char_tetrahedronDisplacementRep_symmetricGroupFourClassData_rep
    (j : SymmetricGroupFourClassIndex) :
    tetrahedronDisplacementRep.character (symmetricGroupFourClassData.rep j) =
      (![12, 2, 0, 0, 0] : Fin 5 → ℝ) (j.cast numClasses_symmetricGroupFourClassData) := by
  have hc : Nat.card {i : Fin 4 // symmetricGroupFourClassData.rep j i = i} =
      (![4, 2, 0, 1, 0] : Fin 5 → ℕ) (j.cast numClasses_symmetricGroupFourClassData) := by
    rw [Nat.card_eq_fintype_card]
    fin_cases j <;> decide
  rw [char_tetrahedronDisplacementRep, hc]
  fin_cases j <;> norm_num [Fin.cast, Matrix.cons_val]

/-- **The displacement character decomposes as `1 + χ_E + 2 χ_V + χ_{sgn ⊗ V}`**, the characters
of the trivial representation, of the two-dimensional representation `E`, of the standard
representation `V` and of its sign twist: the character form of the decomposition
`1 ⊕ E ⊕ 2V ⊕ (sgn ⊗ V)` of the displacements of the spring tetrahedron. -/
theorem char_tetrahedronDisplacementRep_eq (σ : Perm (Fin 4)) :
    tetrahedronDisplacementRep.character σ =
      (Representation.trivial ℝ (Perm (Fin 4)) ℝ).character σ +
        (symmetricGroupFourTwoDimensionalRepresentation ℝ).character σ +
        2 * (standardRepresentation ℝ (Fin 4)).character σ +
        (Representation.charTwist (signLinearCharacter ℝ (Fin 4))
          (standardRepresentation ℝ (Fin 4))).character σ := by
  -- Every character is a class function, so it suffices to compare the values at the class
  -- representatives, which are the rows of the character table of `S₄`.
  obtain ⟨c, hc⟩ := isConj_iff.1 (symmetricGroupFourClassData.isConj_rep_index σ)
  rw [← hc]
  simp only [Representation.char_conj, Representation.char_trivial,
    Representation.char_charTwist, char_tetrahedronDisplacementRep_symmetricGroupFourClassData_rep,
    coe_signLinearCharacter_symmetricGroupFourClassData_rep,
    char_standardRepresentation_symmetricGroupFourClassData_rep,
    char_symmetricGroupFourTwoDimensionalRepresentation_symmetricGroupFourClassData_rep]
  generalize (symmetricGroupFourClassData.index σ).cast numClasses_symmetricGroupFourClassData = j
  fin_cases j <;> norm_num

end TauCeti
