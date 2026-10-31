/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.AdjointAction.RootExponential
public import TauCeti.Algebra.Lie.AdjointAction.SymmetricInvariants
public import TauCeti.Algebra.Lie.Killing.CartanRestriction
public import TauCeti.LinearAlgebra.SymmetricAlgebra.Evaluation

/-!
# Chevalley's restriction theorem: injectivity

Let `L` be a finite-dimensional Lie algebra over a field `K` of characteristic zero whose Killing
form is nondegenerate, and `H` a splitting Cartan subalgebra. Restricting polynomial functions from
`L` to `H` is, through the Killing identifications, the algebra map
`TauCeti.lieCartanRestriction H : S(L) →ₐ[K] S(H)`. This file proves that it is **injective on the
invariants** `S(L)^L`.

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

## Main results

* `TauCeti.eq_zero_of_mem_lieInvariants_of_lift_eval_eq_zero`: an invariant polynomial function on
  `L` vanishing on `H` is zero.
* `TauCeti.lieCartanRestriction_injOn_lieInvariants`: `lieCartanRestriction H` is injective on
  `S(L)^L`.

## References

* J. E. Humphreys, *Introduction to Lie Algebras and Representation Theory*, GTM 9, §23.1.
* J. Dixmier, *Enveloping Algebras*, §7.3.
-/

public section

namespace TauCeti

open LieAlgebra _root_.LieModule Module _root_.SymmetricAlgebra TauCeti.SymmetricAlgebra

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

variable (H) in
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
      (map K H.incl.toLinearMap.dualMap) :=
    algHom_ext (LinearMap.ext fun φ ↦ by simp)
  rw [heval, AlgHom.comp_apply, map_dualMap_killingSymmetricEquiv, map_sub, hpq, sub_self,
    map_zero, map_zero]

end TauCeti
