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
`TauCeti.Hodge.HodgeStructureOn.splitCoordinateMatrix` defining `h`.

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

omit [Comodule ℝ S V] [Module.Finite ℝ V] in
/-- The complexification of a real basis is fixed by the conjugation of `ℂ ⊗[ℝ] V`. -/
theorem complexificationConjugation_baseChange (i : Fin d) :
    (Hodge.complexificationConjugation V).toEquiv (e.baseChange ℂ i) = e.baseChange ℂ i := by
  simp

/-- **From a representation of `S` to a Hodge structure and back, on coordinate rings.** For a
real representation `V` of `S` pure of weight `n` with a basis `e`, the coordinate morphism
`S → GL_{d,ℝ}` of the Hodge structure formed by the Hodge components of `V`, in the
complexification of `e`, is the coordinate morphism of `V` in `e`. -/
theorem realCoordinateBialgHom_ofDecomposition :
    (Hodge.HodgeStructureOn.ofDecomposition
        (isHodgeDecomposition_hodgeComponent hV)).realCoordinateBialgHom
      (complexificationConjugation_baseChange e) = Comodule.coordinateBialgHom e := by
  set hs := Hodge.HodgeStructureOn.ofDecomposition (isHodgeDecomposition_hodgeComponent hV)
  let _ := Comodule.baseChange (R := ℝ) (H := S) (M := V) ℂ
  -- the matrix coefficients of the complexified representation, read in `ℂ[ℤ²]`
  have hcoeff (i j : Fin d) :
      (letI := Comodule.Corestrict (R := ℂ) (M := ℂ ⊗[ℝ] V) (C := ℂ ⊗[ℝ] S)
          (D := MonoidAlgebra ℂ (Multiplicative (ℤ × ℤ)))
          ((splittingBialgEquiv : ℂ ⊗[ℝ] S →ₐc[ℂ] MonoidAlgebra ℂ (Multiplicative (ℤ × ℤ))) :
            ℂ ⊗[ℝ] S →ₗc[ℂ] MonoidAlgebra ℂ (Multiplicative (ℤ × ℤ)));
        Comodule.coefficientMatrix (C := MonoidAlgebra ℂ (Multiplicative (ℤ × ℤ)))
          (e.baseChange ℂ) i j) = hs.splitCoordinateMatrix (e.baseChange ℂ) i j := by
    let _ := Comodule.Corestrict (R := ℂ) (M := ℂ ⊗[ℝ] V) (C := ℂ ⊗[ℝ] S)
      (D := MonoidAlgebra ℂ (Multiplicative (ℤ × ℤ)))
      ((splittingBialgEquiv : ℂ ⊗[ℝ] S →ₐc[ℂ] MonoidAlgebra ℂ (Multiplicative (ℤ × ℤ))) :
        ℂ ⊗[ℝ] S →ₗc[ℂ] MonoidAlgebra ℂ (Multiplicative (ℤ × ℤ)))
    rw [Hodge.HodgeStructureOn.splitCoordinateMatrix_apply, Comodule.coefficientMatrix_apply,
      Comodule.matrixCoefficient_def]
    conv_lhs => rw [← hs.sum_proj_hodgeSupport (e.baseChange ℂ j)]
    rw [map_sum, map_sum, map_sum]
    refine Finset.sum_congr rfl fun p _ ↦ ?_
    have hp : hs.proj p (e.baseChange ℂ j) ∈ hodgeComponent V p (n - p) := by
      simpa [hs] using hs.proj_mem p (e.baseChange ℂ j)
    rw [hodgeComponent_def, DiagonalizableGroup.mem_weightSpace] at hp
    rw [Comodule.corestrict_coact_apply, hp,
      TensorProduct.map_tmul, TensorProduct.lid_tmul, Module.Basis.coord_apply,
      LinearMap.id_apply, MonoidAlgebra.smul_single', mul_one]
    congr 3
    ring
  have hinj : Function.Injective fun s : S ↦
      splittingBialgEquiv ((1 : ℂ) ⊗ₜ[ℝ] s) :=
    splittingBialgEquiv.injective.comp
      (Algebra.TensorProduct.includeRight_injective (algebraMap ℝ ℂ).injective)
  refine BialgHom.coe_toAlgHom_injective (coordinateHopfAlgebra_algHom_ext ℝ d fun i j ↦ hinj ?_)
  simp only [BialgHom.coe_toAlgHom]
  rw [Hodge.HodgeStructureOn.one_tmul_realCoordinateBialgHom,
    Hodge.HodgeStructureOn.complexCoordinateBialgHom_one_tmul_X,
    BialgEquiv.apply_symm_apply, Comodule.coordinateBialgHom_X, ← hcoeff,
    Comodule.coefficientMatrix_corestrict, Comodule.coefficientMatrix_baseChange]
  rfl

/-- **From a representation of `S` to a Hodge structure and back.** The representation of `S`
on `V` read off, through the basis `e`, from the Hodge structure formed by the Hodge components
of `V` is the original representation. -/
theorem comoduleOfCoordinateBialgHom_ofDecomposition :
    e.comoduleOfCoordinateBialgHom
        ((Hodge.HodgeStructureOn.ofDecomposition
          (isHodgeDecomposition_hodgeComponent hV)).realCoordinateBialgHom
            (complexificationConjugation_baseChange e)) = ‹Comodule ℝ S V› := by
  rw [realCoordinateBialgHom_ofDecomposition hV,
    Module.Basis.comoduleOfCoordinateBialgHom_coordinateBialgHom]

end TauCeti.DeligneTorus
