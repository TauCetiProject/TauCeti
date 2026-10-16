/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.Curved.Module.Right.HomComplex
public import TauCeti.Algebra.Homology.DG.Module.Right.Composition

/-!
# Composition in curved differential graded right-module Hom complexes

Homogeneous right-module cochains between curved differential graded right modules are the same
cochains as in the uncurved case, so `TauCeti.dgRightModuleCochains.comp` and
`TauCeti.dgRightModuleCochains.id` compose them and supply the identity cochain.  The curved Hom
differential is the graded commutator with the module differentials, so it obeys the graded
Leibniz rule

`\delta(g \circ f) = \delta(g) \circ f + (-1)^p g \circ \delta(f)`

for `g` of degree `p`, and the identity cochain is closed.  Neither statement sees the curvature:
both are instances of the corresponding rules for the graded commutator.  They are the algebraic
input for the differential graded category of curved right modules.

## Main results

* `TauCeti.dgRightModuleCochains.curvedDifferential_comp`: the graded Leibniz rule for
  composition of cochains between curved modules.
* `TauCeti.dgRightModuleCochains.curvedDifferential_id`: the identity cochain of a curved module
  is closed.

## References

* L. Positselski, *Two kinds of derived categories, Koszul duality, and comodule-contramodule
  correspondence*, Section 3.1.
* B. Keller, *Deriving DG categories*, Section 2, for the uncurved Leibniz rule.
-/

public section

open MulOpposite

namespace TauCeti

universe u

variable {R A M N P : Type u}
  [CommRing R] [Ring A] [Algebra R A]
  [AddCommGroup M] [Module R M] [Module Aᵐᵒᵖ M] [IsScalarTower R Aᵐᵒᵖ M]
  [AddCommGroup N] [Module R N] [Module Aᵐᵒᵖ N] [IsScalarTower R Aᵐᵒᵖ N]
  [AddCommGroup P] [Module R P] [Module Aᵐᵒᵖ P] [IsScalarTower R Aᵐᵒᵖ P]
  {𝒜 : ℤ → Submodule R A} [GradedAlgebra 𝒜] {d : A →ₗ[R] A} {w : A}
  {h : IsCurvedDGAlgebra 𝒜 d w}
  {ℳ : ℤ → Submodule R M}
    [SetLike.GradedSMul (InternalGrading.ofDecomposition 𝒜).opposite.piece ℳ]
    [DirectSum.Decomposition ℳ] {dM : M →ₗ[R] M}
  {ℳN : ℤ → Submodule R N}
    [SetLike.GradedSMul (InternalGrading.ofDecomposition 𝒜).opposite.piece ℳN]
    [DirectSum.Decomposition ℳN] {dN : N →ₗ[R] N}
  {ℳP : ℤ → Submodule R P}
    [SetLike.GradedSMul (InternalGrading.ofDecomposition 𝒜).opposite.piece ℳP]
    [DirectSum.Decomposition ℳP] {dP : P →ₗ[R] P}
  {hM : IsCurvedDGRightModule h ℳ dM} {hN : IsCurvedDGRightModule h ℳN dN}
  {hP : IsCurvedDGRightModule h ℳP dP}

namespace dgRightModuleCochains

/-- The curved Hom differential satisfies the graded Leibniz rule for composition of cochains,
with the sign carried by the degree of the outer factor. -/
theorem curvedDifferential_comp {p q : ℤ}
    (g : dgRightModuleCochains (R := R) (A := A) (ℳ := ℳN) (ℳN := ℳP) p)
    (f : dgRightModuleCochains (R := R) (A := A) (ℳ := ℳ) (ℳN := ℳN) q) :
    curvedDifferential (hM := hM) (hN := hP) (p + q) (comp g f rfl) =
      comp (curvedDifferential (hM := hN) (hN := hP) p g) f (by omega) +
        p.negOnePow • comp g (curvedDifferential (hM := hM) (hN := hN) q f) (by omega) := by
  ext x
  simpa only [gradedCommutator_apply, curvedDifferential_apply, comp_apply, Submodule.coe_add,
    LinearMap.add_apply, Submodule.coe_smul_of_tower, LinearMap.smul_apply] using
    LinearMap.congr_fun (congrArg Subtype.val (gradedCommutator_comp hM.isHomogeneous hM.leibniz
      hN.isHomogeneous hN.leibniz hP.isHomogeneous hP.leibniz g f)) x

/-- The identity cochain of a curved module is closed. -/
@[simp]
theorem curvedDifferential_id (hM : IsCurvedDGRightModule h ℳ dM) :
    curvedDifferential (hM := hM) (hN := hM) 0 (id (R := R) (A := A) (ℳ := ℳ)) = 0 := by
  ext x
  simpa only [gradedCommutator_apply, curvedDifferential_apply] using
    LinearMap.congr_fun (congrArg Subtype.val (gradedCommutator_id hM.isHomogeneous hM.leibniz)) x

end dgRightModuleCochains

end TauCeti
