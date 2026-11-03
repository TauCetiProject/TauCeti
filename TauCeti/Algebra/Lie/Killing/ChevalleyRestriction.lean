/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.AdjointAction.RootExponential
public import TauCeti.Algebra.Lie.AdjointAction.SymmetricInvariants
public import TauCeti.Algebra.Lie.Killing.CartanRestriction
public import TauCeti.Algebra.Lie.Sl2.Weyl.Automorphism
public import TauCeti.LinearAlgebra.SymmetricAlgebra.Evaluation

/-!
# Chevalley's restriction theorem: injectivity and the coreflections

Let `L` be a finite-dimensional Lie algebra over a field `K` of characteristic zero whose Killing
form is nondegenerate, and `H` a splitting Cartan subalgebra. Restricting polynomial functions from
`L` to `H` is, through the Killing identifications, the algebra map
`TauCeti.lieCartanRestriction H : S(L) →ₐ[K] S(H)`. This file proves that it is **injective on the
invariants** `S(L)^L`, and that the restriction of an invariant is fixed by the coreflection of
every root.

On the side of polynomial functions the argument is the classical one. An invariant polynomial
function `p ∈ S(L*)^L` is invariant under the group `Int(L)` of inner automorphisms
(`TauCeti.SymmetricAlgebra.lift_eval_smul_of_mem_intLieAlgebra`). If it vanishes on `H` it
therefore vanishes on every conjugate `g h`, `g ∈ Int(L)`, `h ∈ H`, and these conjugates are
Zariski dense in `L` (`LieSubalgebra.polynomial_eq_zero_of_invariant_of_cartan`), so `p = 0`. The
two statements are joined by reading `p` as a polynomial in the coordinates of a basis of `L`
(`Module.Basis.lift_eval_apply_eq_eval_equivMvPolynomial_dualBasis`). The Killing equivalence
`S(L) ≃ S(L*)` identifies the invariants on both sides
(`TauCeti.killingSymmetricEquiv_mem_lieInvariants_iff`) and turns restriction to `H` into
`lieCartanRestriction` (`TauCeti.map_dualMap_killingSymmetricEquiv`).

For a nonzero root `α` with `sl₂` triple `(α^∨, e, f)`, the inner automorphism
`σ = exp(ad e) exp(-ad f) exp(ad e)` (`TauCeti.weylAut`) acts on `H` by the coreflection
`h ↦ h - α(h) • α^∨`, and it preserves the Killing form, so it commutes with the
Killing-orthogonal projection `L → H` defining the restriction. An invariant is fixed by `σ`, so
its restriction is fixed by the coreflection.

## Main results

* `TauCeti.eq_zero_of_mem_lieInvariants_of_lift_eval_eq_zero`: an invariant polynomial function on
  `L` vanishing on `H` is zero.
* `LieSubalgebra.lieCartanRestriction_injOn_lieInvariants`: `lieCartanRestriction H` is injective
  on `S(L)^L`.
* `TauCeti.map_coreflection_lieCartanRestriction`: the coreflection of a root fixes the
  restriction of an invariant.

## References

* J. E. Humphreys, *Introduction to Lie Algebras and Representation Theory*, GTM 9, §23.1.
* J. Dixmier, *Enveloping Algebras*, §7.3.
-/

public section

namespace TauCeti

open LieAlgebra LieAlgebra.IsKilling _root_.LieModule Module _root_.SymmetricAlgebra
  TauCeti.SymmetricAlgebra

variable {K L : Type*} [Field K] [CharZero K] [LieRing L] [LieAlgebra K L] [FiniteDimensional K L]
  [IsKilling K L] {H : LieSubalgebra K L} [H.IsCartanSubalgebra] [IsTriangularizable K H L]

/-- **An invariant polynomial function vanishing on a Cartan subalgebra is zero.** If an element
`p` of the algebra `S(L*)` of polynomial functions on `L` is killed by the coadjoint action of `L`
and vanishes at every point of the splitting Cartan subalgebra `H`, then `p = 0`. -/
theorem eq_zero_of_mem_lieInvariants_of_lift_eval_eq_zero {p : SymmetricAlgebra K (Dual K L)}
    (hp : p ∈ lieInvariants K L (Dual K L)) (hH : ∀ h ∈ H, lift (Dual.eval K L h) p = 0) :
    p = 0 := by
  classical
  let := ratLieAlgebra K L
  let b := Module.finBasis K L
  refine (equivMvPolynomial b.dualBasis).injective ?_
  rw [map_zero]
  refine H.polynomial_eq_zero_of_invariant_of_cartan b (fun g hg x ↦ ?_) fun h hh ↦ ?_
  · rw [← b.lift_eval_apply_eq_eval_equivMvPolynomial_dualBasis,
      ← b.lift_eval_apply_eq_eval_equivMvPolynomial_dualBasis,
      lift_eval_smul_of_mem_intLieAlgebra hg hp]
  · rw [← b.lift_eval_apply_eq_eval_equivMvPolynomial_dualBasis, hH h hh]

/-- **The coreflections fix the restriction of an invariant.** For a root `α`, the coreflection
`h ↦ h - α(h) • α^∨` of `H` fixes the restriction `TauCeti.lieCartanRestriction H p` of every
invariant `p ∈ S(L)^L`. On `H` it is the inner automorphism `exp(ad e) exp(-ad f) exp(ad e)` of an
`sl₂` triple of `α`, which fixes `p`. -/
theorem map_coreflection_lieCartanRestriction (i : H.root) {p : _root_.SymmetricAlgebra K L}
    (hp : p ∈ lieInvariants K L L) :
    _root_.SymmetricAlgebra.map K ((rootSystem H).coreflection i).toLinearMap
        (lieCartanRestriction H p) =
      lieCartanRestriction H p := by
  let := ratLieAlgebra K L
  have hα : (i : Weight K H L).IsNonZero := (Finset.mem_filter.mp i.2).2
  obtain ⟨h, e, f, t, heα, hfα⟩ := exists_isSl2Triple_of_weight_isNonZero hα
  have he := isNilpotent_ad_of_mem_rootSpace H (χ := ⇑(i : Weight K H L)) hα heα
  have hf := isNilpotent_ad_of_mem_rootSpace H (χ := ⇑(-(i : Weight K H L))) hα.neg hfα
  set σ := weylAut t he hf
  set s := (rootSystem H).coreflection i
  -- on `H`, the Weyl automorphism is the coreflection
  have hσ (y : H) : σ y = (s y : L) := by
    have hye : ⁅(y : L), e⁆ = (i : Weight K H L) y • e := lie_eq_smul_of_mem_rootSpace heα y
    have hyf : ⁅(y : L), f⁆ = -((i : Weight K H L) y • f) := by
      simpa using lie_eq_smul_of_mem_rootSpace hfα y
    rw [weylAut_apply_of_lie_eq_smul he hf t hye hyf, t.h_eq_coroot hα heα hfα,
      RootPairing.coreflection_apply]
    simp
  -- `σ` preserves the Killing form, so it commutes with the Killing-orthogonal projection
  have hπ (x : L) : killingCartanProjection H (σ x) = s (killingCartanProjection H x) := by
    refine ((eq_killingCartanProjection_iff H).mpr fun y ↦ ?_).symm
    have hy : σ (s y : L) = y := by rw [hσ, RootPairing.coreflection_same]
    rw [← hσ, ← hy, killingForm_of_equiv_apply, killingForm_of_equiv_apply,
      killingForm_killingCartanProjection]
  -- hence restriction to `H` intertwines `σ` with the coreflection
  have hcomm : (_root_.SymmetricAlgebra.map K s.toLinearMap).comp (lieCartanRestriction H) =
      (lieCartanRestriction H).comp (_root_.SymmetricAlgebra.map K σ.toLinearEquiv.toLinearMap) :=
    _root_.SymmetricAlgebra.algHom_ext (LinearMap.ext fun x ↦ by simp [hπ])
  have hfix := map_apply_of_mem_intLieAlgebra (t.ofLinearEquiv_weylAut_mem_intLieAlgebra he hf) hp
  have hcoe : ((LinearMap.GeneralLinearGroup.ofLinearEquiv σ.toLinearEquiv :
      LinearMap.GeneralLinearGroup K L) : Module.End K L) = σ.toLinearEquiv.toLinearMap :=
    LinearMap.ext fun x ↦ by simp
  rw [hcoe] at hfix
  conv_rhs => rw [← hfix]
  rw [← AlgHom.comp_apply, hcomm, AlgHom.comp_apply]

end TauCeti

namespace LieSubalgebra

open LieAlgebra _root_.LieModule Module _root_.SymmetricAlgebra TauCeti TauCeti.SymmetricAlgebra

variable {K L : Type*} [Field K] [CharZero K] [LieRing L] [LieAlgebra K L] [FiniteDimensional K L]
  [IsKilling K L] (H : LieSubalgebra K L) [H.IsCartanSubalgebra] [IsTriangularizable K H L]

/-- **Chevalley's restriction theorem, injectivity.** Restriction of polynomial functions from `L`
to the splitting Cartan subalgebra `H`, read on `S(L)` as `TauCeti.lieCartanRestriction H`, is
injective on the invariants `S(L)^L`. -/
theorem lieCartanRestriction_injOn_lieInvariants :
    Set.InjOn (lieCartanRestriction H) (lieInvariants K L L) := by
  intro p hp q hq hpq
  rw [← sub_eq_zero]
  refine (killingSymmetricEquiv K L).injective ?_
  rw [map_zero]
  refine eq_zero_of_mem_lieInvariants_of_lift_eval_eq_zero (H := H)
    ((killingSymmetricEquiv_mem_lieInvariants_iff K L).mpr (sub_mem hp hq)) fun h hh ↦ ?_
  -- evaluating at a point of `H` factors through restricting the polynomial function to `H`
  have heval : lift (Dual.eval K L h) = (lift (Dual.eval K H ⟨h, hh⟩)).comp
      (_root_.SymmetricAlgebra.map K H.incl.toLinearMap.dualMap) :=
    algHom_ext (LinearMap.ext fun φ ↦ by simp)
  rw [heval, AlgHom.comp_apply, map_dualMap_killingSymmetricEquiv, map_sub, hpq, sub_self,
    map_zero, map_zero]

end LieSubalgebra
