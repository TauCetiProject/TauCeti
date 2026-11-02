/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.AdjointAction.InnerAutomorphismGroup
public import TauCeti.LinearAlgebra.SymmetricAlgebra.LieModule
import Mathlib.GroupTheory.GroupAction.FixingSubgroup
import TauCeti.LinearAlgebra.Dual.Exp
import TauCeti.LinearAlgebra.SymmetricAlgebra.Derivation.Exp
import TauCeti.RepresentationTheory.SymmetricAlgebra.Basic

/-!
# Lie invariants of symmetric algebras are invariant under inner automorphisms

A Lie algebra `L` acts on the symmetric algebra `S(M)` of a Lie module `M` by derivations, and
`TauCeti.SymmetricAlgebra.lieInvariants` is the subalgebra they kill. If `x : L` acts nilpotently
on `M`, the derivation by which it acts is the derivation induced by the nilpotent endomorphism
`⁅x, -⁆` of `M`, so the algebra automorphism of `S(M)` induced by `exp ⁅x, -⁆` fixes every Lie
invariant.

For the adjoint module `M = L` and for the coadjoint module `M = L*` the automorphisms
`exp (ad x)` and their transposes generate the actions of the group `Int L = TauCeti.intLieAlgebra`
of inner automorphisms on `S(L)` and on the polynomial functions `S(L*)` on `L`. Therefore:

* the Lie invariants `S(L)^L` are invariant under `Int L` acting on `S(L)`;
* the Lie invariants `S(L*)^L` are invariant under `Int L` acting on `S(L*)` through the
  contragredient representation, so an `L`-invariant polynomial function `p` on `L` satisfies
  `p (g x) = p x` for every inner automorphism `g`.

The second statement is what Chevalley's restriction theorem needs to apply the density of the
conjugates of a Cartan subalgebra under `Int L`
(`LieSubalgebra.polynomial_eq_zero_of_invariant_of_cartan`) to Lie-invariant polynomial
functions, such as the trace-power polynomials `TauCeti.tracePowerPolynomial`.

## Main results

* `TauCeti.SymmetricAlgebra.map_exp_toEnd_apply_of_mem_lieInvariants`: if `x` acts nilpotently on
  `M`, then `exp ⁅x, -⁆` fixes the Lie invariants of `S(M)`.
* `TauCeti.SymmetricAlgebra.map_apply_of_mem_intLieAlgebra`: an inner automorphism fixes the Lie
  invariants of `S(L)`.
* `TauCeti.SymmetricAlgebra.map_dualMap_apply_of_mem_intLieAlgebra`: the transpose of an inner
  automorphism fixes the Lie invariants of `S(L*)`.
* `TauCeti.SymmetricAlgebra.lift_eval_smul_of_mem_intLieAlgebra`: a Lie-invariant polynomial
  function on `L` is invariant under the inner automorphisms.

## References

* J. E. Humphreys, *Introduction to Lie Algebras and Representation Theory*, GTM 9, §23.1, where
  the polynomial functions on `L` invariant under `Int L` are those killed by the derivations
  `ad x`.
-/

public section

namespace TauCeti.SymmetricAlgebra

open _root_.SymmetricAlgebra LieAlgebra LinearMap.GeneralLinearGroup Module

universe u v w

variable {K : Type u} {L : Type v} [CommRing K] [Algebra ℚ K] [LieRing L] [LieAlgebra K L]

section LieModule

variable {M : Type w} [AddCommGroup M] [Module K M] [LieRingModule L M] [LieModule K L M]
  [Module ℚ M]

/-- **Lie invariants are fixed by exponentials.** If `x` acts nilpotently on `M`, the algebra
automorphism of `S(M)` induced by `exp ⁅x, -⁆` fixes every Lie invariant. -/
theorem map_exp_toEnd_apply_of_mem_lieInvariants {x : L}
    (hx : IsNilpotent (LieModule.toEnd K L M x)) {p : _root_.SymmetricAlgebra K M}
    (hp : p ∈ lieInvariants K L M) :
    map K (IsNilpotent.exp (LieModule.toEnd K L M x)) p = p :=
  map_exp_apply_of_derivationOfEnd_eq_zero hx <| by
    rw [← lieModuleDerivation_apply]
    exact mem_lieInvariants.mp hp x

end LieModule

variable [LieAlgebra ℚ L]

/-- **Inner automorphisms fix the Lie invariants of `S(L)`.** The algebra automorphism of the
symmetric algebra `S(L)` induced by an element of `Int L` fixes every element killed by the
adjoint action of `L`. -/
theorem map_apply_of_mem_intLieAlgebra {g : LinearMap.GeneralLinearGroup K L}
    (hg : g ∈ intLieAlgebra K L) {p : _root_.SymmetricAlgebra K L} (hp : p ∈ lieInvariants K L L) :
    map K (g : Module.End K L) p = p := by
  let ρ : Representation K (LinearMap.GeneralLinearGroup K L) L := Units.coeHom _
  let := ρ.symmetricAlgebraMulSemiringAction
  have hsmul (g : LinearMap.GeneralLinearGroup K L) (p : _root_.SymmetricAlgebra K L) :
      g • p = map K (g : Module.End K L) p := by
    rw [ρ.symmetricAlgebraMulSemiringAction_smul, Representation.symmetricAlgebra_apply,
      Units.coeHom_apply]
  -- `Int L` fixes the Lie invariants pointwise because its generators `exp (ad x)` do.
  have hG : intLieAlgebra K L ≤
      fixingSubgroup _ (lieInvariants K L L : Set (_root_.SymmetricAlgebra K L)) :=
    intLieAlgebra_le_iff.mpr fun x hx ↦ (mem_fixingSubgroup_iff _).mpr fun p hp ↦ by
      rw [hsmul, coe_ofLinearEquiv_expAd]
      exact map_exp_toEnd_apply_of_mem_lieInvariants hx hp
  rw [← hsmul]
  exact (mem_fixingSubgroup_iff _).mp (hG hg) p hp

/-- **The transposes of inner automorphisms fix the Lie invariants of `S(L*)`.** The algebra
automorphism of the polynomial functions `S(L*)` on `L` induced by the transpose of an element of
`Int L` fixes every element killed by the coadjoint action of `L`. -/
theorem map_dualMap_apply_of_mem_intLieAlgebra {g : LinearMap.GeneralLinearGroup K L}
    (hg : g ∈ intLieAlgebra K L) {p : _root_.SymmetricAlgebra K (Dual K L)}
    (hp : p ∈ lieInvariants K L (Dual K L)) :
    map K (g : Module.End K L).dualMap p = p := by
  -- The contragredient action of `g` on `S(L*)` is the map induced by the transpose of `g⁻¹`.
  let ρ : Representation K (LinearMap.GeneralLinearGroup K L) L := Units.coeHom _
  let := ρ.dual.symmetricAlgebraMulSemiringAction
  have hsmul (g : LinearMap.GeneralLinearGroup K L) (p : _root_.SymmetricAlgebra K (Dual K L)) :
      g⁻¹ • p = map K (g : Module.End K L).dualMap p := by
    rw [ρ.dual.symmetricAlgebraMulSemiringAction_smul, Representation.symmetricAlgebra_apply,
      Representation.dual_apply, inv_inv, Units.coeHom_apply, LinearMap.dualMap_def]
  -- `Int L` fixes the Lie invariants pointwise because the transposes of its generators do.
  have hG : intLieAlgebra K L ≤ fixingSubgroup _ 
      (lieInvariants K L (Dual K L) : Set (_root_.SymmetricAlgebra K (Dual K L))) := by
    refine intLieAlgebra_le_iff.mpr fun x hx ↦ (Subgroup.inv_mem_iff _).mp ?_
    refine (mem_fixingSubgroup_iff _).mpr fun p hp ↦ ?_
    -- The transpose of `ad x` is the coadjoint action of `-x`.
    have hcoad : (ad K L x).dualMap = LieModule.toEnd K L (Dual K L) (-x) := by
      ext φ y
      simp
    rw [hsmul, coe_ofLinearEquiv_expAd, LinearMap.dualMap_exp hx, hcoad]
    exact map_exp_toEnd_apply_of_mem_lieInvariants (hcoad ▸ hx.dualMap) hp
  rw [← hsmul]
  exact (mem_fixingSubgroup_iff _).mp (hG (inv_mem hg)) p hp

/-- **Lie-invariant polynomial functions are invariant under inner automorphisms.** If `p` in the
algebra `S(L*)` of polynomial functions on `L` is killed by the coadjoint action of `L`, then
`p (g x) = p x` for every `g ∈ Int L` and every `x : L`. -/
theorem lift_eval_smul_of_mem_intLieAlgebra {g : LinearMap.GeneralLinearGroup K L}
    (hg : g ∈ intLieAlgebra K L) {p : _root_.SymmetricAlgebra K (Dual K L)}
    (hp : p ∈ lieInvariants K L (Dual K L)) (x : L) :
    lift (Dual.eval K L (g • x)) p = lift (Dual.eval K L x) p := by
  -- Evaluation at `g x` is evaluation at `x` after the transpose of `g`.
  have h : lift (Dual.eval K L (g • x)) =
      (lift (Dual.eval K L x)).comp (map K (g : Module.End K L).dualMap) := by
    refine algHom_ext (LinearMap.ext fun φ ↦ ?_)
    simp [Units.smul_def]
  rw [h, AlgHom.comp_apply, map_dualMap_apply_of_mem_intLieAlgebra hg hp]

end TauCeti.SymmetricAlgebra
