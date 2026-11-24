/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.Orthogonal.TypeD.Serre.Equiv
public import TauCeti.RepresentationTheory.Spin.Polarization.TypeD.Serre.Comparison

/-!
# The type-D Serre presentation of the quadratic Clifford Lie algebra

Let `P` be an even polarization of a quadratic space over a field of characteristic zero, with a
basis `b` of its exterior summand indexed by `Fin n`, `4 ≤ n`. Composing the matrix Serre
presentation `TauCeti.TypeDStd.serreEquiv` with the quadratic equivalence
`TauCeti.SpinPolarizationData.typeDQuadraticEquiv` identifies the Lie algebra presented by Serre's
relations for `CartanMatrix.D n` with the quadratic Lie subalgebra of the Clifford algebra
(`TauCeti.SpinPolarizationData.typeDSerreQuadraticEquiv`). It sends the presented Cartan, raising
and lowering generators to the numbered Clifford representatives
`TauCeti.SpinPolarizationData.typeDSimpleCorootBivector`,
`TauCeti.SpinPolarizationData.typeDSimpleRootBivector` and
`TauCeti.SpinPolarizationData.typeDSimpleNegativeRootBivector`, with the chain and fork signs fixed
by `TauCeti.SpinPolarizationData.typeDQuadraticEquiv_comp_serreRepresentation`.

A symmetry `σ` of the Cartan matrix induces the automorphism
`TauCeti.SpinPolarizationData.typeDDiagramAut` of the quadratic Lie subalgebra, the matrix
diagram automorphism `TauCeti.TypeDStd.diagramAut` conjugated by the quadratic equivalence. It is
also the transport of `TauCeti.serreDiagramAut` along the Serre presentation, and it permutes the
numbered Clifford representatives along `σ`. It preserves the Cartan subalgebra spanned by the
coroot representatives and the Borel subalgebra generated as a Lie subalgebra by these and the
simple positive root representatives. For `D₄` the triality permutation gives the automorphism
`TauCeti.SpinPolarizationData.typeDTrialityAut`, of order dividing three.

## Main definitions

* `TauCeti.SpinPolarizationData.typeDSerreQuadraticEquiv`: the Serre presentation of the
  quadratic Clifford Lie algebra.
* `TauCeti.SpinPolarizationData.typeDDiagramAut`: the diagram automorphism of the quadratic
  Clifford Lie algebra induced by a symmetry of the Cartan matrix.
* `TauCeti.SpinPolarizationData.typeDTrialityAut`: the triality automorphism in rank four.

## Main results

* `TauCeti.SpinPolarizationData.typeDSerreQuadraticEquiv_serreE` and its companions: the values
  on the presented generators.
* `TauCeti.SpinPolarizationData.typeDDiagramAut_eq`: the diagram automorphism is the transport of
  the Serre diagram automorphism along the presentation.
* `TauCeti.SpinPolarizationData.typeDDiagramAut_simpleRootBivector` and its companions: it
  permutes the numbered Clifford representatives.
* `TauCeti.SpinPolarizationData.map_typeDDiagramAut_cartan` and
  `TauCeti.SpinPolarizationData.map_typeDDiagramAut_borel`: it preserves the Cartan and Borel
  subalgebras.
* `TauCeti.SpinPolarizationData.typeDTrialityAut_typeDTrialityAut_typeDTrialityAut`: triality has
  order dividing three.

## References

* N. Bourbaki, *Lie Groups and Lie Algebras, Chapters 4--6*, Plate IV.
* W. Fulton and J. Harris, *Representation Theory: A First Course* (1991), Sections 20.1–20.3.
-/

public section

open CliffordAlgebra

namespace TauCeti.SpinPolarizationData

universe u v

variable {K : Type u} [Field K] [CharZero K] {V : Type v} [AddCommGroup V] [Module K V]
  {Q : QuadraticForm K V} (P : SpinPolarizationData Q)

section Presentation

variable {n : ℕ} (b : Module.Basis (Fin n) K P.W) (hn : 4 ≤ n) (hline : P.line = ⊥)

private theorem typeDQuadraticEquiv_cartanGenerator_eq (i : Fin n) :
    P.typeDQuadraticEquiv b hline (TypeDStd.cartanGenerator n hn i) =
      ⟨P.typeDSimpleCorootBivector b (by omega) i,
        P.typeDSimpleCorootBivector_mem_quadraticLieSubalgebra b (by omega) i⟩ :=
  Subtype.ext (by simp)

private theorem typeDQuadraticEquiv_rootGenerator_inl_eq (i : Fin n) :
    P.typeDQuadraticEquiv b hline (TypeDStd.rootGenerator n hn (.inl i)) =
      ⟨P.typeDSimpleRootBivector b (by omega) i,
        P.typeDSimpleRootBivector_mem_quadraticLieSubalgebra b (by omega) i⟩ :=
  Subtype.ext (by simp)

private theorem typeDQuadraticEquiv_rootGenerator_inr_eq (i : Fin n) :
    P.typeDQuadraticEquiv b hline (TypeDStd.rootGenerator n hn (.inr i)) =
      ⟨P.typeDSimpleNegativeRootBivector b (by omega) i,
        P.typeDSimpleNegativeRootBivector_mem_quadraticLieSubalgebra b (by omega) i⟩ :=
  Subtype.ext (by simp)

/-- **The type-`D` Serre presentation of the quadratic Clifford Lie algebra**: the isomorphism
from the Lie algebra presented by Serre's relations for `CartanMatrix.D n` to the quadratic Lie
subalgebra, through the split orthogonal matrix algebra. -/
noncomputable def typeDSerreQuadraticEquiv :
    Matrix.ToLieAlgebra K (CartanMatrix.D n) ≃ₗ⁅K⁆ quadraticLieSubalgebra Q :=
  (TypeDStd.serreEquiv n hn).trans (P.typeDQuadraticEquiv b hline)

/-- The Serre presentation of the quadratic Clifford Lie algebra is the Serre lift of the
numbered Clifford representatives. -/
theorem typeDSerreQuadraticEquiv_toLieHom :
    (P.typeDSerreQuadraticEquiv b hn hline).toLieHom =
      TauCeti.serreLift (P.isSerreSystem_typeDSimpleRootBivector_quadraticLieSubalgebra b hn) :=
  TauCeti.eq_serreLift (fun i => Subtype.ext (by simp [typeDSerreQuadraticEquiv]))
    fun i => Subtype.ext (by simp [typeDSerreQuadraticEquiv])

/-- The Serre presentation sends a presented Cartan generator to the numbered Clifford coroot
representative. -/
@[simp]
theorem typeDSerreQuadraticEquiv_serreH (i : Fin n) :
    (P.typeDSerreQuadraticEquiv b hn hline (serreH K (CartanMatrix.D n) i) : CliffordAlgebra Q) =
      P.typeDSimpleCorootBivector b (by omega) i := by
  simp [typeDSerreQuadraticEquiv]

/-- The Serre presentation sends a presented positive generator to the numbered positive Clifford
root representative. -/
@[simp]
theorem typeDSerreQuadraticEquiv_serreE (i : Fin n) :
    (P.typeDSerreQuadraticEquiv b hn hline (serreE K (CartanMatrix.D n) i) : CliffordAlgebra Q) =
      P.typeDSimpleRootBivector b (by omega) i := by
  simp [typeDSerreQuadraticEquiv]

/-- The Serre presentation sends a presented negative generator to the numbered negative Clifford
root representative. -/
@[simp]
theorem typeDSerreQuadraticEquiv_serreF (i : Fin n) :
    (P.typeDSerreQuadraticEquiv b hn hline (serreF K (CartanMatrix.D n) i) : CliffordAlgebra Q) =
      P.typeDSimpleNegativeRootBivector b (by omega) i := by
  simp [typeDSerreQuadraticEquiv]

/-- The inverse presentation sends the numbered Clifford coroot representative to the presented
Cartan generator. -/
theorem typeDSerreQuadraticEquiv_symm_simpleCorootBivector (i : Fin n) :
    (P.typeDSerreQuadraticEquiv b hn hline).symm
        ⟨P.typeDSimpleCorootBivector b (by omega) i,
          P.typeDSimpleCorootBivector_mem_quadraticLieSubalgebra b (by omega) i⟩ =
      serreH K (CartanMatrix.D n) i := by
  rw [LieEquiv.symm_apply_eq]
  exact Subtype.ext (P.typeDSerreQuadraticEquiv_serreH b hn hline i).symm

/-- The inverse presentation sends the numbered positive Clifford root representative to the
presented positive generator. -/
@[simp]
theorem typeDSerreQuadraticEquiv_symm_simpleRootBivector (i : Fin n) :
    (P.typeDSerreQuadraticEquiv b hn hline).symm
        ⟨P.typeDSimpleRootBivector b (by omega) i,
          P.typeDSimpleRootBivector_mem_quadraticLieSubalgebra b (by omega) i⟩ =
      serreE K (CartanMatrix.D n) i := by
  rw [LieEquiv.symm_apply_eq]
  exact Subtype.ext (P.typeDSerreQuadraticEquiv_serreE b hn hline i).symm

/-- The inverse presentation sends the numbered negative Clifford root representative to the
presented negative generator. -/
@[simp]
theorem typeDSerreQuadraticEquiv_symm_simpleNegativeRootBivector (i : Fin n) :
    (P.typeDSerreQuadraticEquiv b hn hline).symm
        ⟨P.typeDSimpleNegativeRootBivector b (by omega) i,
          P.typeDSimpleNegativeRootBivector_mem_quadraticLieSubalgebra b (by omega) i⟩ =
      serreF K (CartanMatrix.D n) i := by
  rw [LieEquiv.symm_apply_eq]
  exact Subtype.ext (P.typeDSerreQuadraticEquiv_serreF b hn hline i).symm

/-! ### Diagram automorphisms -/

section Diagram

variable {σ : Equiv.Perm (Fin n)} (hσ : (CartanMatrix.D n).submatrix σ σ = CartanMatrix.D n)

/-- **The diagram automorphism of the quadratic Clifford Lie algebra** induced by a permutation
`σ` of the nodes preserving `CartanMatrix.D n`: the matrix diagram automorphism
`TauCeti.TypeDStd.diagramAut`, conjugated by the quadratic equivalence. -/
noncomputable def typeDDiagramAut : quadraticLieSubalgebra Q ≃ₗ⁅K⁆ quadraticLieSubalgebra Q :=
  ((P.typeDQuadraticEquiv b hline).symm.trans (TypeDStd.diagramAut n hn hσ)).trans
    (P.typeDQuadraticEquiv b hline)

/-- **The diagram automorphism is the Serre diagram automorphism transported along the Serre
presentation** of the quadratic Clifford Lie algebra. -/
theorem typeDDiagramAut_eq :
    P.typeDDiagramAut b hn hline hσ =
      ((P.typeDSerreQuadraticEquiv b hn hline).symm.trans
        (serreDiagramAut K (CartanMatrix.D n) hσ)).trans (P.typeDSerreQuadraticEquiv b hn hline) :=
  LieEquiv.ext fun _ => by
    simp [typeDDiagramAut, TypeDStd.diagramAut_apply, typeDSerreQuadraticEquiv]

/-- The diagram automorphism permutes the numbered Clifford coroot representatives along
`σ`. -/
theorem typeDDiagramAut_simpleCorootBivector (i : Fin n) :
    P.typeDDiagramAut b hn hline hσ
        ⟨P.typeDSimpleCorootBivector b (by omega) i,
          P.typeDSimpleCorootBivector_mem_quadraticLieSubalgebra b (by omega) i⟩ =
      ⟨P.typeDSimpleCorootBivector b (by omega) (σ i),
        P.typeDSimpleCorootBivector_mem_quadraticLieSubalgebra b (by omega) (σ i)⟩ := by
  rw [← typeDQuadraticEquiv_cartanGenerator_eq P b hn hline,
    ← typeDQuadraticEquiv_cartanGenerator_eq P b hn hline]
  simp [typeDDiagramAut]

/-- The diagram automorphism permutes the numbered positive Clifford root representatives along
`σ`. -/
@[simp]
theorem typeDDiagramAut_simpleRootBivector (i : Fin n) :
    P.typeDDiagramAut b hn hline hσ
        ⟨P.typeDSimpleRootBivector b (by omega) i,
          P.typeDSimpleRootBivector_mem_quadraticLieSubalgebra b (by omega) i⟩ =
      ⟨P.typeDSimpleRootBivector b (by omega) (σ i),
        P.typeDSimpleRootBivector_mem_quadraticLieSubalgebra b (by omega) (σ i)⟩ := by
  rw [← typeDQuadraticEquiv_rootGenerator_inl_eq P b hn hline,
    ← typeDQuadraticEquiv_rootGenerator_inl_eq P b hn hline]
  simp [typeDDiagramAut]

/-- The diagram automorphism permutes the numbered negative Clifford root representatives along
`σ`. -/
@[simp]
theorem typeDDiagramAut_simpleNegativeRootBivector (i : Fin n) :
    P.typeDDiagramAut b hn hline hσ
        ⟨P.typeDSimpleNegativeRootBivector b (by omega) i,
          P.typeDSimpleNegativeRootBivector_mem_quadraticLieSubalgebra b (by omega) i⟩ =
      ⟨P.typeDSimpleNegativeRootBivector b (by omega) (σ i),
        P.typeDSimpleNegativeRootBivector_mem_quadraticLieSubalgebra b (by omega) (σ i)⟩ := by
  rw [← typeDQuadraticEquiv_rootGenerator_inr_eq P b hn hline,
    ← typeDQuadraticEquiv_rootGenerator_inr_eq P b hn hline]
  simp [typeDDiagramAut]

/-- The diagram automorphism maps the Cartan subalgebra spanned by the numbered Clifford coroot
representatives onto itself. -/
theorem map_typeDDiagramAut_cartan :
    (LieSubalgebra.lieSpan K (quadraticLieSubalgebra Q)
        (Set.range fun i => (⟨P.typeDSimpleCorootBivector b (by omega) i,
          P.typeDSimpleCorootBivector_mem_quadraticLieSubalgebra b (by omega) i⟩ :
            quadraticLieSubalgebra Q))).map (P.typeDDiagramAut b hn hline hσ).toLieHom =
      LieSubalgebra.lieSpan K (quadraticLieSubalgebra Q)
        (Set.range fun i => (⟨P.typeDSimpleCorootBivector b (by omega) i,
          P.typeDSimpleCorootBivector_mem_quadraticLieSubalgebra b (by omega) i⟩ :
            quadraticLieSubalgebra Q)) :=
  LieSubalgebra.map_lieSpan_range_of_surjective _ σ.surjective fun i =>
    P.typeDDiagramAut_simpleCorootBivector b hn hline hσ i

/-- The diagram automorphism maps the Borel subalgebra, generated as a Lie subalgebra by the
numbered Clifford coroot and simple positive root representatives, onto itself. -/
theorem map_typeDDiagramAut_borel :
    (LieSubalgebra.lieSpan K (quadraticLieSubalgebra Q)
        ((Set.range fun i => (⟨P.typeDSimpleCorootBivector b (by omega) i,
          P.typeDSimpleCorootBivector_mem_quadraticLieSubalgebra b (by omega) i⟩ :
            quadraticLieSubalgebra Q)) ∪
        Set.range fun i => (⟨P.typeDSimpleRootBivector b (by omega) i,
          P.typeDSimpleRootBivector_mem_quadraticLieSubalgebra b (by omega) i⟩ :
            quadraticLieSubalgebra Q))).map (P.typeDDiagramAut b hn hline hσ).toLieHom =
      LieSubalgebra.lieSpan K (quadraticLieSubalgebra Q)
        ((Set.range fun i => (⟨P.typeDSimpleCorootBivector b (by omega) i,
          P.typeDSimpleCorootBivector_mem_quadraticLieSubalgebra b (by omega) i⟩ :
            quadraticLieSubalgebra Q)) ∪
        Set.range fun i => (⟨P.typeDSimpleRootBivector b (by omega) i,
          P.typeDSimpleRootBivector_mem_quadraticLieSubalgebra b (by omega) i⟩ :
            quadraticLieSubalgebra Q)) := by
  rw [LieSubalgebra.span_union, (LieSubalgebra.gc_map_comap
      (f := (P.typeDDiagramAut b hn hline hσ).toLieHom)).l_sup,
    P.map_typeDDiagramAut_cartan b hn hline hσ]
  congr 1
  exact LieSubalgebra.map_lieSpan_range_of_surjective _ σ.surjective fun i =>
    P.typeDDiagramAut_simpleRootBivector b hn hline hσ i

end Diagram

end Presentation

/-! ### Triality -/

section Triality

variable (b : Module.Basis (Fin 4) K P.W) (hline : P.line = ⊥)

/-- **The triality automorphism of the quadratic Clifford Lie algebra of an even polarization of
rank four**: the diagram automorphism `TauCeti.SpinPolarizationData.typeDDiagramAut` of the
triality permutation `TauCeti.trialityPermD4`, cycling the three outer nodes `0 → 2 → 3 → 0` of
`D₄` and fixing the central node `1`. -/
noncomputable def typeDTrialityAut : quadraticLieSubalgebra Q ≃ₗ⁅K⁆ quadraticLieSubalgebra Q :=
  P.typeDDiagramAut b le_rfl hline (by
    ext i j
    simpa only [Matrix.submatrix_apply, DynkinType.cartanMatrix_D] using
      cartanMatrix_D4_trialityPermD4 i j)

/-- Triality is the diagram automorphism of the triality permutation. -/
theorem typeDTrialityAut_eq_typeDDiagramAut
    (h : (CartanMatrix.D 4).submatrix trialityPermD4 trialityPermD4 = CartanMatrix.D 4) :
    P.typeDTrialityAut b hline = P.typeDDiagramAut b le_rfl hline h :=
  (rfl)

/-- Triality permutes the numbered Clifford coroot representatives along `trialityPermD4`. -/
theorem typeDTrialityAut_simpleCorootBivector (i : Fin 4) :
    P.typeDTrialityAut b hline
        ⟨P.typeDSimpleCorootBivector b (by omega) i,
          P.typeDSimpleCorootBivector_mem_quadraticLieSubalgebra b (by omega) i⟩ =
      ⟨P.typeDSimpleCorootBivector b (by omega) (trialityPermD4 i),
        P.typeDSimpleCorootBivector_mem_quadraticLieSubalgebra b (by omega)
          (trialityPermD4 i)⟩ :=
  P.typeDDiagramAut_simpleCorootBivector b le_rfl hline _ i

/-- Triality permutes the numbered positive Clifford root representatives along
`trialityPermD4`. -/
@[simp]
theorem typeDTrialityAut_simpleRootBivector (i : Fin 4) :
    P.typeDTrialityAut b hline
        ⟨P.typeDSimpleRootBivector b (by omega) i,
          P.typeDSimpleRootBivector_mem_quadraticLieSubalgebra b (by omega) i⟩ =
      ⟨P.typeDSimpleRootBivector b (by omega) (trialityPermD4 i),
        P.typeDSimpleRootBivector_mem_quadraticLieSubalgebra b (by omega)
          (trialityPermD4 i)⟩ :=
  P.typeDDiagramAut_simpleRootBivector b le_rfl hline _ i

/-- Triality permutes the numbered negative Clifford root representatives along
`trialityPermD4`. -/
@[simp]
theorem typeDTrialityAut_simpleNegativeRootBivector (i : Fin 4) :
    P.typeDTrialityAut b hline
        ⟨P.typeDSimpleNegativeRootBivector b (by omega) i,
          P.typeDSimpleNegativeRootBivector_mem_quadraticLieSubalgebra b (by omega) i⟩ =
      ⟨P.typeDSimpleNegativeRootBivector b (by omega) (trialityPermD4 i),
        P.typeDSimpleNegativeRootBivector_mem_quadraticLieSubalgebra b (by omega)
          (trialityPermD4 i)⟩ :=
  P.typeDDiagramAut_simpleNegativeRootBivector b le_rfl hline _ i

/-- **Triality of the quadratic Clifford Lie algebra has order dividing three.** -/
@[simp]
theorem typeDTrialityAut_typeDTrialityAut_typeDTrialityAut (x : quadraticLieSubalgebra Q) :
    P.typeDTrialityAut b hline (P.typeDTrialityAut b hline (P.typeDTrialityAut b hline x)) = x := by
  simp [typeDTrialityAut, typeDDiagramAut, ← TypeDStd.trialityAut_eq_diagramAut _]

end Triality

end TauCeti.SpinPolarizationData
