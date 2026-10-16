/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Coalgebra.Comodule.ExteriorAlgebra.Power
public import TauCeti.LinearAlgebra.ExteriorPower.BaseChange
import TauCeti.LinearAlgebra.ExteriorPower.Basic

/-!
# Point actions on exterior powers and scalar extension

Let `M` be a comodule over a commutative bialgebra `H`, and let `g` be an `A`-point of `H`.
There are two ways to let `g` act on exterior powers after extending scalars to `A`: through the
exterior algebra over `A` of its action on `A ⊗[R] M`, or through the exterior-algebra comodule of
`M` and its homogeneous pieces. The comparison `TauCeti.exteriorAlgebraEquivBaseChange`
intertwines the two actions.

As a consequence, for a submodule `W` of `M`, the point stabilizes the scalar extension of the
exterior image `⋀ⁿ W → ⋀ⁿ M` of `W` in the finite-degree comodule `⋀ⁿ M` exactly when it
stabilizes the `n`th power of `A ⊗ W` inside the exterior algebra over `A`. Over a field, for
`n = dim W` the latter is the top exterior line of `A ⊗ W`, which turns a subspace stabilizer into
the stabilizer of a line in a rational representation. No flatness or reducedness assumption is
needed.

## References

* J. S. Milne, *Algebraic Groups* (2017), Theorem 4.27 and Lemma 4.28.
-/

public section

open scoped TensorProduct

namespace TauCeti.Comodule

variable {R H M A : Type*} [CommRing R] [CommSemiring H] [Bialgebra R H]
  [AddCommGroup M] [Module R M] [Comodule R H M] [CommRing A] [Algebra R A]

attribute [local instance] exteriorAlgebra exteriorPower

/-- Scalar extension of exterior algebras intertwines the exterior algebra of a point action with
the point action on the exterior-algebra comodule. -/
@[simp]
theorem _root_.TauCeti.exteriorAlgebraEquivBaseChange_map_endOfPoint (g : H →ₐ[R] A)
    (x : ExteriorAlgebra A (A ⊗[R] M)) :
    exteriorAlgebraEquivBaseChange A (ExteriorAlgebra.map (endOfPoint M g) x) =
      endOfPoint (ExteriorAlgebra R M) g (exteriorAlgebraEquivBaseChange A x) := by
  rw [← exteriorAlgebraEndOfPoint_apply]
  suffices h : (exteriorAlgebraEquivBaseChange A).toAlgHom.comp
      (ExteriorAlgebra.map (endOfPoint M g)) =
        (exteriorAlgebraEndOfPoint g).comp (exteriorAlgebraEquivBaseChange A).toAlgHom from
    AlgHom.congr_fun h x
  apply ExteriorAlgebra.hom_ext
  refine LinearMap.ext fun y ↦ ?_
  have hι := LinearMap.congr_fun (baseChange_comp_endOfPoint (Hom.exteriorAlgebraι R H M) g) y
  simp only [LinearMap.comp_apply, Hom.exteriorAlgebraι_toLinearMap] at hι
  simp [hι]

/-- A point stabilizes the scalar extension of the exterior image of `⋀ⁿ W` in the comodule
`⋀ⁿ M` if and only if the exterior algebra of its action stabilizes the `n`th power of the
scalar-extended subspace `A ⊗ W`. -/
theorem map_endOfPoint_baseChange_range_exteriorPowerMap_eq_iff (W : Submodule R M) (n : ℕ)
    (g : H →ₐ[R] A) :
    ((LinearMap.range (_root_.exteriorPower.map n W.subtype)).baseChange A).map
        (endOfPoint (⋀[R]^n M) g) =
      (LinearMap.range (_root_.exteriorPower.map n W.subtype)).baseChange A ↔
    (((W.baseChange A).map (ExteriorAlgebra.ι A)) ^ n).map
        (ExteriorAlgebra.map (endOfPoint M g)).toLinearMap =
      ((W.baseChange A).map (ExteriorAlgebra.ι A)) ^ n := by
  let s := (⋀[R]^n M).subtype.baseChange A
  let e := (exteriorAlgebraEquivBaseChange (R := R) (M := M) A).toAlgHom
  have he : Function.Injective e.toLinearMap := (exteriorAlgebraEquivBaseChange A).injective
  -- Inside `ExteriorAlgebra R M`, the exterior image of `W` is the `n`th power of `W`.
  have himage : (LinearMap.range (_root_.exteriorPower.map n W.subtype)).map (⋀[R]^n M).subtype =
      (W.map (ExteriorAlgebra.ι R)) ^ n := by
    rw [← LinearMap.range_comp, _root_.exteriorPower.subtype_comp_map_eq, LinearMap.range_comp,
      Submodule.range_subtype, TauCeti.ExteriorAlgebra.exteriorPower_map_map,
      Submodule.range_subtype]
  have hι : e.toLinearMap ∘ₗ ExteriorAlgebra.ι A = (ExteriorAlgebra.ι R).baseChange A :=
    LinearMap.ext (exteriorAlgebraEquivBaseChange_ι A)
  -- Both submodules land on the scalar extension of `(W.map ι) ^ n` in `A ⊗ ⋀ M`.
  have hsame : ((LinearMap.range (_root_.exteriorPower.map n W.subtype)).baseChange A).map s =
      (((W.baseChange A).map (ExteriorAlgebra.ι A)) ^ n).map e.toLinearMap := by
    rw [← Submodule.baseChange_map, himage, Submodule.map_pow, ← Submodule.map_comp, hι,
      ← Submodule.baseChange_map, Submodule.baseChange_pow]
  have hs : s ∘ₗ endOfPoint (⋀[R]^n M) g = endOfPoint (ExteriorAlgebra R M) g ∘ₗ s := by
    simpa using baseChange_comp_endOfPoint (Hom.exteriorPowerSubtype R H M n) g
  have hT : e.toLinearMap ∘ₗ (ExteriorAlgebra.map (endOfPoint M g)).toLinearMap =
      endOfPoint (ExteriorAlgebra R M) g ∘ₗ e.toLinearMap :=
    LinearMap.ext (exteriorAlgebraEquivBaseChange_map_endOfPoint g)
  rw [← (Submodule.map_injective_of_injective
      (exteriorPower.baseChange_subtype_injective (R := R) (M := M) A n)).eq_iff,
    ← (Submodule.map_injective_of_injective he).eq_iff, ← Submodule.map_comp,
    ← Submodule.map_comp, hs, hT, Submodule.map_comp, Submodule.map_comp, hsame]

end TauCeti.Comodule
