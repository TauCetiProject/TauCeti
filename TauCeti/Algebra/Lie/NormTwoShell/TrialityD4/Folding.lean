/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.NormTwoShell.Folding
public import TauCeti.Algebra.Lie.NormTwoShell.TrialityD4.FixedBasis

/-!
# Folding the D₄ Chevalley frame along triality to the Serre system of G₂

Building on the matrix-level folding of `CartanMatrix.D 4` along `TauCeti.trialityPermD4` to
`CartanMatrix.G₂` in `TauCeti.LinearAlgebra.Matrix.Cartan.Folding.TrialityD4`, this file evaluates
the folded Chevalley frame
`(Matrix.ShellLieAlgebra.foldedH, Matrix.ShellLieAlgebra.foldedE, Matrix.ShellLieAlgebra.foldedF)`
in `Matrix.ShellLieAlgebra (CartanMatrix.D 4)` and constructs the folded `G₂` Serre comparison
homomorphism into the triality-fixed Lie subalgebra over any commutative ring.

Specifically:
* Along `TauCeti.D4Triality.vertexOrbitEquiv`, `foldedH`, `foldedE`, and `foldedF` evaluate to
  `TauCeti.D4Triality.invariantCartan` and the simple-orbit root sums
  `invariantRoot false (simpleOrbit k)` and `invariantRoot true (simpleOrbit k)`
  (`foldedH_vertexOrbitEquiv`, `foldedE_vertexOrbitEquiv`, `foldedF_vertexOrbitEquiv`).
* Transporting `Matrix.ShellLieAlgebra.isSerreSystem_folded` to the integral fixed subalgebra
  (`isSerreSystem_g2Fixed`) and across `toFixedSubalgebraBaseChange`
  (`isSerreSystem_g2FixedBaseChange`) yields the `G₂` Serre comparison homomorphism
  `TauCeti.D4Triality.g2SerreLift A` over every commutative ring `A`.

## References

* N. Bourbaki, *Lie Groups and Lie Algebras, Chapters 4--6*, Plates IV and IX.
* V. G. Kac, *Infinite dimensional Lie algebras*, third edition, §7.9.
-/

public section

open scoped TensorProduct

namespace TauCeti.D4Triality

open _root_.Matrix

/-! ### Explicit evaluation of the folded Chevalley frame -/

/-- The folded Cartan generators of `D₄` triality are `invariantCartan 0` and
`invariantCartan 1`. -/
@[simp]
theorem foldedH_vertexOrbitEquiv (k : Fin 2) :
    ShellLieAlgebra.foldedH (CartanMatrix.D 4) trialityPermD4 (vertexOrbitEquiv k) =
      invariantCartan k := by
  rw [ShellLieAlgebra.foldedH_def, foldingScale_eq_one, one_smul, invariantCartan_eq_sum]
  refine Finset.sum_congr ?_ fun _ _ ↦ rfl
  ext i
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, sameCycle_vertexOrbitEquiv_out_iff]

/-- The folded raising generators of `D₄` triality are `invariantRoot false (simpleOrbit 0)` and
`invariantRoot false (simpleOrbit 1)`. -/
@[simp]
theorem foldedE_vertexOrbitEquiv (k : Fin 2) :
    ShellLieAlgebra.foldedE (CartanMatrix.D_diag (n := 4)) trialityPermD4 (vertexOrbitEquiv k) =
      invariantRoot false (simpleOrbit k) := by
  refine (ShellLieAlgebra.basis (CartanMatrix.D 4)).repr.injective (Finsupp.ext fun idx ↦ ?_)
  rcases idx with i | a
  · simp [ShellLieAlgebra.foldedE_def, ShellLieAlgebra.chevalleyE_def,
      ← ShellLieAlgebra.basis_inr]
  · obtain ⟨⟨neg', j⟩, rfl⟩ := rootEquiv.surjective a
    rw [rootEquiv_apply, basis_repr_invariantRoot, ShellLieAlgebra.foldedE_def, map_sum,
      Finsupp.finsetSum_apply]
    simp only [sameCycle_vertexOrbitEquiv_out_iff, ShellLieAlgebra.chevalleyE_def,
      ← ShellLieAlgebra.basis_inr, Module.Basis.repr_self, Finsupp.single_apply, Sum.inr.injEq,
      Subtype.ext_iff, coe_root]
    cases neg' <;> fin_cases k <;> fin_cases j <;>
      decide

/-- The folded lowering generators of `D₄` triality are `invariantRoot true (simpleOrbit 0)` and
`invariantRoot true (simpleOrbit 1)`. -/
@[simp]
theorem foldedF_vertexOrbitEquiv (k : Fin 2) :
    ShellLieAlgebra.foldedF (CartanMatrix.D_diag (n := 4)) trialityPermD4 (vertexOrbitEquiv k) =
      invariantRoot true (simpleOrbit k) := by
  refine (ShellLieAlgebra.basis (CartanMatrix.D 4)).repr.injective (Finsupp.ext fun idx ↦ ?_)
  rcases idx with i | a
  · simp [ShellLieAlgebra.foldedF_def, ShellLieAlgebra.chevalleyF_def,
      ← ShellLieAlgebra.basis_inr]
  · obtain ⟨⟨neg', j⟩, rfl⟩ := rootEquiv.surjective a
    rw [rootEquiv_apply, basis_repr_invariantRoot, ShellLieAlgebra.foldedF_def,
      foldingScale_eq_one, one_smul, map_sum, Finsupp.finsetSum_apply]
    simp only [sameCycle_vertexOrbitEquiv_out_iff, ShellLieAlgebra.chevalleyF_def,
      ← ShellLieAlgebra.basis_inr, Module.Basis.repr_self, Finsupp.single_apply, Sum.inr.injEq,
      Subtype.ext_iff, coe_root]
    cases neg' <;> fin_cases k <;> fin_cases j <;>
      decide

/-! ### The folded `G₂` Serre system and homomorphism over any commutative ring -/

/-- `invariantCartan` and the simple-orbit vectors `invariantRoot false (simpleOrbit k)`,
`invariantRoot true (simpleOrbit k)` form an integral Serre system for `CartanMatrix.G₂` in
`Matrix.ShellLieAlgebra (CartanMatrix.D 4)`. -/
theorem isSerreSystem_g2 :
    IsSerreSystem ℤ CartanMatrix.G₂ invariantCartan
      (fun k : Fin 2 ↦ invariantRoot false (simpleOrbit k))
      (fun k : Fin 2 ↦ invariantRoot true (simpleOrbit k)) := by
  have h := (ShellLieAlgebra.isSerreSystem_folded trialityPermD4
    (Fact.out : (CartanMatrix.D 4).PosDef) (CartanMatrix.D_diag (n := 4))
    (CartanMatrix.D_off_diag_nonpos 4) reindex_cartanMatrix).submatrix vertexOrbitEquiv.injective
  simpa only [submatrix_foldedCartanMatrix_vertexOrbitEquiv, Function.comp_def,
    foldedH_vertexOrbitEquiv, foldedE_vertexOrbitEquiv, foldedF_vertexOrbitEquiv] using h

/-- The folded `G₂` generators inside the integral triality-fixed Lie subring form a Serre system
for `CartanMatrix.G₂`. -/
theorem isSerreSystem_g2Fixed :
    IsSerreSystem ℤ CartanMatrix.G₂
      (fun k : Fin 2 ↦ fixedBasis (.inl k))
      (fun k : Fin 2 ↦ fixedBasis (.inr (false, simpleOrbit k)))
      (fun k : Fin 2 ↦ fixedBasis (.inr (true, simpleOrbit k))) :=
  IsSerreSystem.of_injective trialityLieEquiv.toLieHom.fixedSubalgebra.incl Subtype.val_injective
    (by simpa only [Function.comp_def, LieSubalgebra.coe_incl, coe_fixedBasis_inl,
      coe_fixedBasis_inr] using isSerreSystem_g2)

/-- Over any commutative ring `A`, the scalar-extended folded `G₂` generators in the triality-fixed
Lie subalgebra form an `A`-Serre system for `CartanMatrix.G₂`. -/
theorem isSerreSystem_g2FixedBaseChange (A : Type*) [CommRing A] :
    IsSerreSystem A CartanMatrix.G₂
      (fun k : Fin 2 ↦ fixedSubalgebraBaseChangeBasis A (.inl k))
      (fun k : Fin 2 ↦ fixedSubalgebraBaseChangeBasis A (.inr (false, simpleOrbit k)))
      (fun k : Fin 2 ↦ fixedSubalgebraBaseChangeBasis A (.inr (true, simpleOrbit k))) := by
  have h := (isSerreSystem_g2Fixed.map (toFixedSubalgebraBaseChange A)).changeScalars (S := A)
  simpa only [Function.comp_def, toFixedSubalgebraBaseChange_fixedBasis] using h

/-- **The folded `G₂` Serre comparison homomorphism over any commutative ring `A`**, mapping the
Serre presentation `Matrix.ToLieAlgebra A CartanMatrix.G₂` into the triality-fixed Lie subalgebra
of `A ⊗[ℤ] Matrix.ShellLieAlgebra (CartanMatrix.D 4)`. -/
noncomputable def g2SerreLift (A : Type*) [CommRing A] :
    Matrix.ToLieAlgebra A CartanMatrix.G₂ →ₗ⁅A⁆
      (LieEquiv.baseChange A trialityLieEquiv).toLieHom.fixedSubalgebra :=
  serreLift (isSerreSystem_g2FixedBaseChange A)

@[simp]
theorem g2SerreLift_serreH (A : Type*) [CommRing A] (k : Fin 2) :
    g2SerreLift A (serreH A CartanMatrix.G₂ k) =
      fixedSubalgebraBaseChangeBasis A (.inl k) :=
  serreLift_serreH _ k

@[simp]
theorem g2SerreLift_serreE (A : Type*) [CommRing A] (k : Fin 2) :
    g2SerreLift A (serreE A CartanMatrix.G₂ k) =
      fixedSubalgebraBaseChangeBasis A (.inr (false, simpleOrbit k)) :=
  serreLift_serreE _ k

@[simp]
theorem g2SerreLift_serreF (A : Type*) [CommRing A] (k : Fin 2) :
    g2SerreLift A (serreF A CartanMatrix.G₂ k) =
      fixedSubalgebraBaseChangeBasis A (.inr (true, simpleOrbit k)) :=
  serreLift_serreF _ k

end TauCeti.D4Triality
