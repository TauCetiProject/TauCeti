/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Representation.PointsAction.Basic
public import TauCeti.Algebra.Coalgebra.Comodule.ExteriorAlgebra.Power

/-!
# Base-point action on exterior powers of a comodule

When `H` is a commutative Hopf algebra over a commutative ring `R`, each exterior power `⋀[R]^n M`
of a right `H`-comodule `M` carries the comodule structure `TauCeti.Comodule.exteriorPower`. This
file records that a base-valued point `g` acts on `⋀[R]^n M` via `exteriorPower.map n` of its action
on `M`.

## Main results

* `TauCeti.Comodule.basePointsRepresentation_exteriorPower`: base-valued points act on the `n`th
  exterior power by `exteriorPower.map n`.

## References

* J. C. Jantzen, *Representations of Algebraic Groups*, I.2.7.
* J. S. Milne, *Algebraic Groups* (2017), §§4.a and 4.5.
-/

public section

open WithConv

namespace TauCeti.Comodule

variable {R H M : Type*} [CommRing R] [CommSemiring H] [HopfAlgebra R H]
  [AddCommGroup M] [Module R M] [Comodule R H M]

/-- Base-valued points act on the `n`th exterior power by `exteriorPower.map n`. -/
theorem basePointsRepresentation_exteriorPower (n : ℕ) (g : WithConv (H →ₐ[R] R)) :
    (letI : Comodule R H (⋀[R]^n M) := exteriorPower R H M n
     basePointsRepresentation (R := R) (H := H) (⋀[R]^n M) g) =
      _root_.exteriorPower.map n (basePointsRepresentation (R := R) (H := H) M g) := by
  let _ : Comodule R H (⋀[R]^n M) := exteriorPower R H M n
  refine _root_.exteriorPower.linearMap_ext (R := R) (M := M) (n := n) ?_
  ext v
  simp only [LinearMap.compAlternatingMap_apply, _root_.exteriorPower.map_apply_ιMulti]
  have h := congrArg (Algebra.TensorProduct.lid R (ExteriorAlgebra R M))
    (baseChange_subtype_endOfPoint_ιMulti (R := R) (H := H) (M := M) n g.ofConv (1 : R) v)
  simp only [endOfPoint_tmul, one_smul, endOfPoint_one_tmul_eq_one_tmul_basePointsRepresentation,
    LinearMap.baseChange_tmul, map_list_prod, List.map_ofFn, Function.comp_def,
    Algebra.TensorProduct.lid_tmul, Submodule.subtype_apply] at h
  simpa only [_root_.exteriorPower.ιMulti_apply_coe, ExteriorAlgebra.ιMulti_apply,
    Function.comp_def] using h

end TauCeti.Comodule
