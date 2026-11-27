/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Representation.Comodule.Coordinate
public import TauCeti.Algebra.Coalgebra.Comodule.MatrixCoefficient.BaseChange
public import TauCeti.Geometry.Hodge.MumfordTate.HodgeComponent

/-!
# From a representation of `S` to a Hodge structure and back

Let `V` be a finite-dimensional real representation of the Deligne torus `S`, pure of weight `n`:
its Hodge components `V^{p,q}` (`TauCeti.DeligneTorus.hodgeComponent`) vanish unless
`p + q = n`. They form a Hodge decomposition of `ℂ ⊗[ℝ] V`
(`TauCeti.DeligneTorus.isHodgeDecomposition_hodgeComponent`), hence a Hodge structure `hs`. In a
real basis `e` of `V`, whose complexification is fixed by the conjugation, `hs` has a coordinate
morphism `h : S → GL_{d,ℝ}` (`TauCeti.Hodge.HodgeStructureOn.realCoordinateBialgHom`). This file
proves that `h` is the coordinate morphism of `V` itself in the basis `e`
(`TauCeti.DeligneTorus.realCoordinateBialgHom_ofDecomposition`), so that the representation of
`S` defined by `hs` is `V` (`TauCeti.DeligneTorus.comoduleOfCoordinateBialgHom_ofDecomposition`).

Together with the round trip starting from a Hodge structure,
`TauCeti.Hodge.HodgeStructureOn.ofDecomposition_isHodgeDecomposition_corestrictStandardComodule`,
this gives both round trips of the dictionary between real
Hodge structures of weight `n` and real representations of `S` pure of weight `n`.

The proof compares the two morphisms on the generic matrix after the injective map
`S → ℂ ⊗[ℝ] S ≅ ℂ[ℤ²]`. On the side of `V`, a vector of `V^{p,n-p}` has coaction
`v ⊗ X^{(-p,p-n)}` over `ℂ[ℤ²]`, so the coefficient matrix of `ℂ ⊗[ℝ] V` in `e` is the sum over
`p` of the matrices of the Hodge projections times `X^{(-p,p-n)}`, which is the matrix
`TauCeti.Hodge.HodgeStructureOn.splitCoordinateMatrix` defining `h`
(`TauCeti.DeligneTorus.coefficientMatrix_baseChange_map_splittingBialgEquiv`).

## References

* J. S. Milne, *Introduction to Shimura varieties*, §2, *Hodge structures as representations of
  `S`*, pp. 26–27.
-/

public section

open TauCeti.DeligneTorus TauCeti.GeneralLinear
open scoped TensorProduct

namespace TauCeti.DeligneTorus

variable {V : Type*} [AddCommGroup V] [Module ℝ V] [Comodule ℝ S V] [Module.Finite ℝ V] {n : ℤ}
  (hV : ∀ p q, p + q ≠ n → hodgeComponent V p q = ⊥) {d : ℕ} (e : Module.Basis (Fin d) ℝ V)

/-- **The matrix coefficients of a pure representation of `S`, read in `ℂ[ℤ²]`.** For a real
representation `V` of `S` pure of weight `n` with a basis `e`, the coefficient matrix of
`ℂ ⊗[ℝ] V` in the complexification of `e`, mapped along the splitting `ℂ ⊗[ℝ] S ≅ ℂ[ℤ²]`, is the
matrix `∑ p, P p * X^{(-p, p - n)}` of the Hodge projections `P p` of the Hodge structure formed
by the Hodge components of `V`. -/
theorem coefficientMatrix_baseChange_map_splittingBialgEquiv :
    letI := Comodule.baseChange (R := ℝ) (H := S) (M := V) ℂ
    (Comodule.coefficientMatrix (C := ℂ ⊗[ℝ] S) (e.baseChange ℂ)).map splittingBialgEquiv =
      (Hodge.HodgeStructureOn.ofDecomposition
        (isHodgeDecomposition_hodgeComponent hV)).splitCoordinateMatrix (e.baseChange ℂ) := by
  set hs := Hodge.HodgeStructureOn.ofDecomposition (isHodgeDecomposition_hodgeComponent hV)
  let _ := Comodule.baseChange (R := ℝ) (H := S) (M := V) ℂ
  -- the splitting `ℂ ⊗[ℝ] S ≅ ℂ[ℤ²]`, as a coalgebra map
  let f : ℂ ⊗[ℝ] S →ₗc[ℂ] MonoidAlgebra ℂ (Multiplicative (ℤ × ℤ)) :=
    (splittingBialgEquiv : ℂ ⊗[ℝ] S →ₐc[ℂ] MonoidAlgebra ℂ (Multiplicative (ℤ × ℤ)))
  let _ := Comodule.Corestrict (R := ℂ) (C := ℂ ⊗[ℝ] S) (M := ℂ ⊗[ℝ] V) f
  change (Comodule.coefficientMatrix (C := ℂ ⊗[ℝ] S) (e.baseChange ℂ)).map f = _
  rw [← Comodule.coefficientMatrix_corestrict]
  refine Matrix.ext fun i j ↦ ?_
  rw [Hodge.HodgeStructureOn.splitCoordinateMatrix_apply, Comodule.coefficientMatrix_apply,
    Comodule.matrixCoefficient_def]
  conv_lhs => rw [← hs.sum_proj_hodgeSupport (e.baseChange ℂ j)]
  rw [map_sum, map_sum, map_sum]
  refine Finset.sum_congr rfl fun p _ ↦ ?_
  have hp : hs.proj p (e.baseChange ℂ j) ∈ hodgeComponent V p (n - p) := by
    simpa [hs] using hs.proj_mem p (e.baseChange ℂ j)
  rw [hodgeComponent_def, DiagonalizableGroup.mem_weightSpace, neg_sub] at hp
  rw [Comodule.corestrict_coact_apply, hp]
  simp

/-- **From a representation of `S` to a Hodge structure and back, on coordinate rings.** For a
real representation `V` of `S` pure of weight `n` with a basis `e`, the coordinate morphism
`S → GL_{d,ℝ}` of the Hodge structure formed by the Hodge components of `V`, in the
complexification of `e`, is the coordinate morphism of `V` in `e`. -/
theorem realCoordinateBialgHom_ofDecomposition :
    (Hodge.HodgeStructureOn.ofDecomposition
        (isHodgeDecomposition_hodgeComponent hV)).realCoordinateBialgHom
      e.complexificationConjugation_toEquiv_baseChange = Comodule.coordinateBialgHom e := by
  let _ := Comodule.baseChange (R := ℝ) (H := S) (M := V) ℂ
  have hinj : Function.Injective fun s : S ↦
      splittingBialgEquiv ((1 : ℂ) ⊗ₜ[ℝ] s) :=
    splittingBialgEquiv.injective.comp
      (Algebra.TensorProduct.includeRight_injective (algebraMap ℝ ℂ).injective)
  refine BialgHom.coe_toAlgHom_injective (coordinateHopfAlgebra_algHom_ext ℝ d fun i j ↦ hinj ?_)
  simp only [BialgHom.coe_toAlgHom]
  rw [Hodge.HodgeStructureOn.one_tmul_realCoordinateBialgHom,
    Hodge.HodgeStructureOn.complexCoordinateBialgHom_one_tmul_X,
    BialgEquiv.apply_symm_apply, Comodule.coordinateBialgHom_X,
    ← coefficientMatrix_baseChange_map_splittingBialgEquiv hV,
    Comodule.coefficientMatrix_baseChange]
  simp only [Matrix.map_apply, TensorProduct.mk_apply]

/-- **From a representation of `S` to a Hodge structure and back.** The representation of `S`
on `V` read off, through the basis `e`, from the Hodge structure formed by the Hodge components
of `V` is the original representation. -/
theorem comoduleOfCoordinateBialgHom_ofDecomposition :
    e.comoduleOfCoordinateBialgHom
        ((Hodge.HodgeStructureOn.ofDecomposition
          (isHodgeDecomposition_hodgeComponent hV)).realCoordinateBialgHom
            e.complexificationConjugation_toEquiv_baseChange) = ‹Comodule ℝ S V› := by
  rw [realCoordinateBialgHom_ofDecomposition hV,
    Module.Basis.comoduleOfCoordinateBialgHom_coordinateBialgHom]

end TauCeti.DeligneTorus
