/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.E6.DoubledMinuscule.Basic
public import TauCeti.Algebra.Lie.Matrix.IntegralCast
import TauCeti.Algebra.Lie.Sl2.Basic
import TauCeti.LinearAlgebra.Matrix.MulVec
public import TauCeti.Algebra.Lie.UniversalEnveloping.Kostant.CoordinateLattice
public import TauCeti.Algebra.Lie.UniversalEnveloping.Kostant.Serre

/-!
# The admissible doubled minuscule lattice of type E6

This file extends the integral doubled minuscule representation
`V(ϖ₁) ⊕ V(ϖ₆)` to the rational type-`E₆` Serre algebra and proves that its coordinate
`ℤ`-lattice is preserved by the Serre Kostant form. Its raising and lowering matrices are
square-zero, and its coordinate basis consists of Cartan weight vectors with weights
`TauCeti.DynkinType.e6DoubledMinusculeWeight`.

The resulting admissible lattice is both full-weight and stable under the type-`E₆` diagram
symmetry at the level of its weight basis. It is therefore the lattice input for the graph-stable
type-`E₆` Chevalley--Demazure carrier required by Layer 9 of the ReductiveGroups roadmap and by
the `²E₆` branch of the CFSGStatement roadmap.

The rationalization and coordinate-lattice argument specialize the formal pattern of
`TauCeti/Algebra/Lie/E6/Minuscule/AdmissibleLattice.lean`; the mathematical change is the
contragredient second block and its doubled weight basis.

## Main declarations

* `TauCeti.E6DoubledMinuscule.rationalSerreRepresentation`: the rational doubled minuscule
  representation.
* `TauCeti.E6DoubledMinuscule.rep`: its universal-enveloping-algebra representation.
* `TauCeti.E6DoubledMinuscule.isSl2Triple_rep_serreRootGenerator`: the represented generators at
  every node form an `sl₂` triple.
* `TauCeti.E6DoubledMinuscule.lattice`: the coordinate `ℤ`-lattice.
* `TauCeti.E6DoubledMinuscule.rep_serreKostantForm_mem_lattice`: the Serre Kostant form preserves
  the lattice.

## References

* N. Bourbaki, *Lie Groups and Lie Algebras, Chapters 4--6*, Plate V.
* J. E. Humphreys, *Introduction to Lie Algebras and Representation Theory*, §§26--27.
* J. C. Jantzen, *Representations of Algebraic Groups*, II.1--2.
* R. W. Carter, *Simple Groups of Lie Type*, §12.2.
-/

public section

open scoped Matrix

namespace TauCeti.E6DoubledMinuscule

open TauCeti.DynkinType

attribute [local instance 100] LieRing.ofAssociativeRing LieRing.instLieAlgebra

/-! ## The rational representation -/

/-- The rational raising matrices of the doubled minuscule representation. -/
noncomputable def raisingMatrixQ (i : Fin 6) :
    Matrix (Fin 27 ⊕ Fin 27) (Fin 27 ⊕ Fin 27) ℚ :=
  matrixIntCastLieHom ℚ (raisingMatrix i)

/-- The rational lowering matrices of the doubled minuscule representation. -/
noncomputable def loweringMatrixQ (i : Fin 6) :
    Matrix (Fin 27 ⊕ Fin 27) (Fin 27 ⊕ Fin 27) ℚ :=
  matrixIntCastLieHom ℚ (loweringMatrix i)

/-- The rational Cartan generators of the doubled minuscule representation. -/
noncomputable def cartanGeneratorMatrixQ (i : Fin 6) :
    Matrix (Fin 27 ⊕ Fin 27) (Fin 27 ⊕ Fin 27) ℚ :=
  matrixIntCastLieHom ℚ (cartanGeneratorMatrix i)

/-- Entry formula for a rational raising matrix. -/
@[simp]
theorem raisingMatrixQ_apply (i : Fin 6) (a b : Fin 27 ⊕ Fin 27) :
    raisingMatrixQ i a b =
      if e6DoubledMinusculeWeight b i = -1 ∧ a = reflection i b
      then (summandSign b : ℚ) else 0 := by
  rw [raisingMatrixQ, matrixIntCastLieHom_apply, raisingMatrix_apply]
  split_ifs <;> norm_num

/-- Entry formula for a rational lowering matrix. -/
@[simp]
theorem loweringMatrixQ_apply (i : Fin 6) (a b : Fin 27 ⊕ Fin 27) :
    loweringMatrixQ i a b =
      if e6DoubledMinusculeWeight b i = 1 ∧ a = reflection i b
      then (summandSign b : ℚ) else 0 := by
  rw [loweringMatrixQ, matrixIntCastLieHom_apply, loweringMatrix_apply]
  split_ifs <;> norm_num

/-- A rational Cartan generator is diagonal with the doubled minuscule weights on its diagonal. -/
@[simp]
theorem cartanGeneratorMatrixQ_apply (i : Fin 6) (a b : Fin 27 ⊕ Fin 27) :
    cartanGeneratorMatrixQ i a b =
      if a = b then (e6DoubledMinusculeWeight b i : ℚ) else 0 := by
  rw [cartanGeneratorMatrixQ, matrixIntCastLieHom_apply, cartanGeneratorMatrix_apply]
  split_ifs <;> norm_num

/-- The rational doubled minuscule matrices satisfy the type-`E₆` Serre relations. -/
theorem isSerreSystemQ :
    TauCeti.IsSerreSystem ℚ (CartanMatrix.E 6)ᵀ cartanGeneratorMatrixQ raisingMatrixQ
      loweringMatrixQ := by
  have h := isSerreSystem.map (matrixIntCastLieHom ℚ)
  have hH : matrixIntCastLieHom ℚ ∘ cartanGeneratorMatrix = cartanGeneratorMatrixQ := by
    funext i
    rfl
  have hE : matrixIntCastLieHom ℚ ∘ raisingMatrix = raisingMatrixQ := by
    funext i
    rfl
  have hF : matrixIntCastLieHom ℚ ∘ loweringMatrix = loweringMatrixQ := by
    funext i
    rfl
  rw [hH, hE, hF] at h
  refine { h with
    ad_pow_lie_E_E := ?_
    ad_pow_lie_F_F := ?_ }
  · intro i j
    rw [← ad_pow_apply_eq_ad_pow_apply ℤ ℚ]
    exact h.ad_pow_lie_E_E i j
  · intro i j
    rw [← ad_pow_apply_eq_ad_pow_apply ℤ ℚ]
    exact h.ad_pow_lie_F_F i j

/-- At every node, the rational Cartan, raising, and lowering matrices of the doubled minuscule
representation form an `sl₂` triple. -/
theorem isSl2TripleQ (i : Fin 6) :
    _root_.IsSl2Triple (cartanGeneratorMatrixQ i) (raisingMatrixQ i) (loweringMatrixQ i) := by
  have hdiag : (CartanMatrix.E 6)ᵀ i i = 2 := by fin_cases i <;> decide
  refine
    { h_ne_zero := ?_
      lie_e_f := isSerreSystemQ.lie_E_F_self i
      lie_h_e_nsmul := by rw [isSerreSystemQ.lie_H_E i i, hdiag, ofNat_zsmul]
      lie_h_f_nsmul := by rw [isSerreSystemQ.lie_H_F i i, hdiag, ofNat_zsmul] }
  obtain ⟨a, ha⟩ := exists_e6MinusculeWeight_apply_eq_neg_one i
  intro hzero
  simpa [ha] using congrFun (congrFun hzero (.inl a)) (.inl a)

/-- The rational `54`-dimensional doubled minuscule representation. -/
noncomputable def rationalSerreRepresentation :
    Matrix.ToLieAlgebra ℚ (CartanMatrix.E 6)ᵀ →ₗ⁅ℚ⁆
      Matrix (Fin 27 ⊕ Fin 27) (Fin 27 ⊕ Fin 27) ℚ :=
  TauCeti.serreLift isSerreSystemQ

@[simp]
theorem rationalSerreRepresentation_serreH (i : Fin 6) :
    rationalSerreRepresentation (TauCeti.serreH ℚ (CartanMatrix.E 6)ᵀ i) =
      cartanGeneratorMatrixQ i :=
  TauCeti.serreLift_serreH isSerreSystemQ i

@[simp]
theorem rationalSerreRepresentation_serreE (i : Fin 6) :
    rationalSerreRepresentation (TauCeti.serreE ℚ (CartanMatrix.E 6)ᵀ i) = raisingMatrixQ i :=
  TauCeti.serreLift_serreE isSerreSystemQ i

@[simp]
theorem rationalSerreRepresentation_serreF (i : Fin 6) :
    rationalSerreRepresentation (TauCeti.serreF ℚ (CartanMatrix.E 6)ᵀ i) = loweringMatrixQ i :=
  TauCeti.serreLift_serreF isSerreSystemQ i

/-! ## The enveloping-algebra action -/

/-- The rational doubled minuscule representation extended to the universal enveloping algebra. -/
noncomputable def rep :
    _root_.UniversalEnvelopingAlgebra ℚ
        (Matrix.ToLieAlgebra ℚ (CartanMatrix.E 6)ᵀ) →ₐ[ℚ]
      Module.End ℚ ((Fin 27 ⊕ Fin 27) → ℚ) :=
  _root_.UniversalEnvelopingAlgebra.lift ℚ
    ((Matrix.toLinAlgEquiv (Pi.basisFun ℚ (Fin 27 ⊕ Fin 27))).toAlgHom.toLieHom.comp
      rationalSerreRepresentation)

/-- Included Lie elements act by matrix-vector multiplication. -/
theorem rep_ι_apply (x : Matrix.ToLieAlgebra ℚ (CartanMatrix.E 6)ᵀ)
    (v : (Fin 27 ⊕ Fin 27) → ℚ) :
    rep (_root_.UniversalEnvelopingAlgebra.ι ℚ x) v = rationalSerreRepresentation x *ᵥ v := by
  rw [rep, _root_.UniversalEnvelopingAlgebra.lift_ι_apply, LieHom.comp_apply,
    AlgHom.toLieHom_apply, AlgEquiv.toAlgHom_apply, Matrix.toLinAlgEquiv_apply]
  exact (Pi.basisFun ℚ (Fin 27 ⊕ Fin 27)).sum_repr (rationalSerreRepresentation x *ᵥ v)

/-- Every rational raising matrix is square-zero. -/
@[simp]
theorem raisingMatrixQ_sq (i : Fin 6) : raisingMatrixQ i ^ 2 = 0 := by
  rw [raisingMatrixQ, pow_two, ← matrixIntCastLieHom_mul, ← pow_two, raisingMatrix_pow_two,
    map_zero]

/-- Every rational lowering matrix is square-zero. -/
@[simp]
theorem loweringMatrixQ_sq (i : Fin 6) : loweringMatrixQ i ^ 2 = 0 := by
  rw [loweringMatrixQ, pow_two, ← matrixIntCastLieHom_mul, ← pow_two, loweringMatrix_pow_two,
    map_zero]

/-- Every represented positive or negative Serre root generator is square-zero. -/
theorem rep_serreRootGenerator_sq (k : Fin 6 ⊕ Fin 6) :
    rep (_root_.UniversalEnvelopingAlgebra.ι ℚ
      (TauCeti.serreRootGenerator (CartanMatrix.E 6)ᵀ k)) ^ 2 = 0 := by
  apply LinearMap.ext
  intro v
  rw [pow_two, Module.End.mul_apply]
  cases k with
  | inl i =>
      simpa only [TauCeti.serreRootGenerator_inl, rep_ι_apply,
        rationalSerreRepresentation_serreE, LinearMap.zero_apply] using
        mulVec_mulVec_eq_zero_of_pow_two_eq_zero (raisingMatrixQ_sq i) v
  | inr i =>
      simpa only [TauCeti.serreRootGenerator_inr, rep_ι_apply,
        rationalSerreRepresentation_serreF, LinearMap.zero_apply] using
        mulVec_mulVec_eq_zero_of_pow_two_eq_zero (loweringMatrixQ_sq i) v

/-- Every represented Serre root generator acts nilpotently. -/
theorem isNilpotent_rep_serreRootGenerator (k : Fin 6 ⊕ Fin 6) :
    IsNilpotent (rep (_root_.UniversalEnvelopingAlgebra.ι ℚ
      (TauCeti.serreRootGenerator (CartanMatrix.E 6)ᵀ k))) :=
  ⟨2, rep_serreRootGenerator_sq k⟩

/-- The represented Cartan, positive, and negative Serre generators at every node form an `sl₂`
triple. -/
theorem isSl2Triple_rep_serreRootGenerator (i : Fin 6) :
    _root_.IsSl2Triple
      (rep (_root_.UniversalEnvelopingAlgebra.ι ℚ (TauCeti.serreH ℚ (CartanMatrix.E 6)ᵀ i)))
      (rep (_root_.UniversalEnvelopingAlgebra.ι ℚ
        (TauCeti.serreRootGenerator (CartanMatrix.E 6)ᵀ (.inl i))))
      (rep (_root_.UniversalEnvelopingAlgebra.ι ℚ
        (TauCeti.serreRootGenerator (CartanMatrix.E 6)ᵀ (.inr i)))) := by
  let toEnd := (Matrix.toLinAlgEquiv' (R := ℚ) (n := Fin 27 ⊕ Fin 27)).toAlgHom.toLieHom
  have hrep (x : Matrix.ToLieAlgebra ℚ (CartanMatrix.E 6)ᵀ) :
      rep (_root_.UniversalEnvelopingAlgebra.ι ℚ x) = toEnd (rationalSerreRepresentation x) :=
    LinearMap.ext fun v ↦ by
      rw [rep_ι_apply, AlgHom.toLieHom_apply, AlgEquiv.toAlgHom_apply,
        Matrix.toLinAlgEquiv'_apply]
  have h := (isSl2TripleQ i).map toEnd fun hz ↦ (isSl2TripleQ i).h_ne_zero
    (Matrix.toLinAlgEquiv'.injective (hz.trans (map_zero _).symm))
  rw [TauCeti.serreRootGenerator_inl, TauCeti.serreRootGenerator_inr, hrep, hrep, hrep,
    rationalSerreRepresentation_serreH, rationalSerreRepresentation_serreE,
    rationalSerreRepresentation_serreF]
  exact h

/-! ## The admissible coordinate lattice -/

/-- The coordinate `ℤ`-lattice in the rational doubled minuscule module. -/
def lattice : Submodule ℤ ((Fin 27 ⊕ Fin 27) → ℚ) :=
  TauCeti.coordinateLattice (Fin 27 ⊕ Fin 27)

/-- A vector belongs to the doubled minuscule lattice exactly when every coordinate is integral. -/
@[simp]
theorem mem_lattice_iff {v : (Fin 27 ⊕ Fin 27) → ℚ} :
    v ∈ lattice ↔ ∀ a, ∃ z : ℤ, (z : ℚ) = v a :=
  TauCeti.mem_coordinateLattice_iff (Fin 27 ⊕ Fin 27)

/-- Every standard coordinate vector belongs to the doubled minuscule lattice. -/
theorem single_mem_lattice (a : Fin 27 ⊕ Fin 27) : Pi.single a (1 : ℚ) ∈ lattice := by
  rw [← Pi.basisFun_apply]
  exact TauCeti.basisFun_mem_coordinateLattice (Fin 27 ⊕ Fin 27) a

/-- The coordinate basis of the doubled minuscule lattice. -/
noncomputable def latticeBasis : Module.Basis (Fin 27 ⊕ Fin 27) ℤ lattice :=
  TauCeti.coordinateLatticeBasis (Fin 27 ⊕ Fin 27)

/-- Coercing a lattice-basis vector gives the corresponding coordinate vector. -/
@[simp]
theorem coe_latticeBasis (a : Fin 27 ⊕ Fin 27) :
    ((latticeBasis a : lattice) : (Fin 27 ⊕ Fin 27) → ℚ) = Pi.single a 1 := by
  rw [← Pi.basisFun_apply, latticeBasis]
  exact TauCeti.coe_coordinateLatticeBasis (Fin 27 ⊕ Fin 27) a

/-- Every represented Serre root generator preserves the doubled minuscule lattice. -/
theorem rep_serreRootGenerator_mem_lattice (k : Fin 6 ⊕ Fin 6)
    {v : (Fin 27 ⊕ Fin 27) → ℚ} (hv : v ∈ lattice) :
    rep (_root_.UniversalEnvelopingAlgebra.ι ℚ
      (TauCeti.serreRootGenerator (CartanMatrix.E 6)ᵀ k)) v ∈ lattice := by
  rw [rep_ι_apply]
  cases k with
  | inl i =>
      rw [TauCeti.serreRootGenerator_inl, rationalSerreRepresentation_serreE, raisingMatrixQ]
      exact Matrix.intCastLieHom_mulVec_mem_coordinateLattice (raisingMatrix i) hv
  | inr i =>
      rw [TauCeti.serreRootGenerator_inr, rationalSerreRepresentation_serreF, loweringMatrixQ]
      exact Matrix.intCastLieHom_mulVec_mem_coordinateLattice (loweringMatrix i) hv

/-- Every standard coordinate vector has its named doubled minuscule weight. -/
theorem isCartanWeightVector_single (a : Fin 27 ⊕ Fin 27) :
    TauCeti.UniversalEnvelopingAlgebra.IsCartanWeightVector
      (TauCeti.serreH ℚ (CartanMatrix.E 6)ᵀ) rep (e6DoubledMinusculeWeight a)
      (Pi.single a 1) := by
  refine (TauCeti.UniversalEnvelopingAlgebra.isCartanWeightVector_iff
    (TauCeti.serreH ℚ (CartanMatrix.E 6)ᵀ) rep).mpr fun i ↦ ?_
  rw [rep_ι_apply, rationalSerreRepresentation_serreH]
  ext b
  simp [Matrix.mulVec, dotProduct, cartanGeneratorMatrixQ_apply, Pi.single_apply]

/-- Every doubled minuscule lattice-basis vector has its named Cartan weight. -/
theorem isCartanWeightVector_latticeBasis (a : Fin 27 ⊕ Fin 27) :
    TauCeti.UniversalEnvelopingAlgebra.IsCartanWeightVector
      (TauCeti.serreH ℚ (CartanMatrix.E 6)ᵀ) rep (e6DoubledMinusculeWeight a)
      ((latticeBasis a : lattice) : (Fin 27 ⊕ Fin 27) → ℚ) := by
  rw [coe_latticeBasis]
  exact isCartanWeightVector_single a

/-- **The doubled minuscule coordinate lattice is admissible for the type-`E₆` Serre Kostant
form.** -/
theorem rep_serreKostantForm_mem_lattice
    {u : _root_.UniversalEnvelopingAlgebra ℚ
      (Matrix.ToLieAlgebra ℚ (CartanMatrix.E 6)ᵀ)}
    (hu : u ∈ TauCeti.serreKostantForm (CartanMatrix.E 6)ᵀ)
    {v : (Fin 27 ⊕ Fin 27) → ℚ} (hv : v ∈ lattice) : rep u v ∈ lattice := by
  rw [TauCeti.serreKostantForm_def] at hu
  exact TauCeti.UniversalEnvelopingAlgebra.kostantForm_apply_mem_coordinateLattice
    (TauCeti.serreRootGenerator (CartanMatrix.E 6)ᵀ)
    (TauCeti.serreH ℚ (CartanMatrix.E 6)ᵀ) rep
    (wt := e6DoubledMinusculeWeight) rep_serreRootGenerator_sq
    (fun k _ hw ↦ rep_serreRootGenerator_mem_lattice k hw) isCartanWeightVector_single hu hv

end TauCeti.E6DoubledMinuscule
