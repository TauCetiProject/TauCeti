/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.ThricePuncturedSphere.Classification
public import TauCeti.AlgebraicTopology.UniversalCover.Classification.Pullback
public import TauCeti.Combinatorics.PermutationTriple.BranchPoints

/-!
# Pulling covers of the thrice-punctured sphere back along `z ↦ 1 − z`

The six anharmonic self-homeomorphisms of `ℂ ∖ {0, 1}` permute the three punctures, and pulling a
cover back along one of them permutes the roles of `0`, `1` and `∞` in its monodromy triple. This
file proves that for the involution `mob01 : z ↦ 1 − z`, which exchanges the punctures `0` and `1`
and fixes the basepoint `1/2`: the pullback of a cover along `mob01` has monodromy triple the
branch-point operation `swap01` of the original triple, on the nose for fibre-numbered covers and
hence on isomorphism classes for bare covers.

The computation is transport-free because `mob01` fixes the basepoint. Its induced automorphism of
`π₁(ℂ ∖ {0, 1}, 1/2)` exchanges `periph0` and `periph1` and carries `periphInf` to
`periph1⁻¹ * periphInf * periph1`
(`TauCeti.ThricePuncturedSphere.homeomorphMulEquivOfEq_mob01_periph0` and its companions), which
are exactly the three components of `swap01`. Among the six anharmonic maps only the identity and
`mob01` fix the basepoint `1/2`; the remaining four move it, so they act on triples only after a
choice of connecting path and are compared with their branch-point operations on isomorphism
classes alone.

On isomorphism classes the statement reads: the pullback along `mob01` is the action of
`MulOpposite.op (Equiv.swap 0 1)` on `TauCeti.ConnectedIsoClass`, the right action of `Perm (Fin 3)`
by reindexing the branch points. This identifies the topological branch-point operation with the
combinatorial one at the generator exchanging `0` and `1`.

## Main declarations

* `TauCeti.ThricePuncturedSphere.permutationTriple_comp_mob01`: precomposing a representation of
  `π₁(ℂ ∖ {0, 1}, 1/2)` with the automorphism induced by `mob01` applies `swap01` to its triple.
* `TauCeti.ConnectedFiberNumberedCover.connectedTriple_pullback_mob01`: **the triple of the
  pullback of a numbered cover along `mob01` is `swap01` of its triple.**
* `TauCeti.ConnectedFiberNumberedCoverClass.triple_pullback_mob01`: the same on classes of numbered
  covers.
* `TauCeti.ConnectedCoverClass.isoClass_pullback_mob01`: **pulling a bare cover back along `mob01`
  acts on the isomorphism class of its triple by the branch-point exchange of `0` and `1`.**

## References

* E. Girondo and G. González-Diez, *Introduction to Compact Riemann Surfaces and Dessins
  d'Enfants*, London Mathematical Society Student Texts 79, Cambridge University Press, 2012,
  §2.7 (the monodromy of a cover) and Theorem 2.61 (covers with the same branch values are
  isomorphic exactly when their monodromies are conjugate).
* S. K. Lando, A. K. Zvonkin, *Graphs on Surfaces and Their Applications*, Encyclopaedia of
  Mathematical Sciences 141, Springer 2004, §1.5 (permuting the branch points of a constellation).
-/

public section

open CategoryTheory Equiv

namespace TauCeti

open ThricePuncturedSphere

variable {n : ℕ}

namespace ThricePuncturedSphere

/-- Precomposing a representation of `π₁(ℂ ∖ {0, 1}, 1/2)` with the automorphism induced by
`z ↦ 1 − z` exchanges the roles of `0` and `1` in its permutation triple. -/
theorem permutationTriple_comp_mob01
    (ρ : FundamentalGroup ThricePuncturedSphere basePt →* Perm (Fin n)) :
    permutationTriple
        (ρ.comp (FundamentalGroup.homeomorphMulEquivOfEq mob01 mob01_basePt).toMonoidHom) =
      (permutationTriple ρ).swap01 :=
  PermutationTriple.ext_of_two
    (by rw [PermutationTriple.swap01_σ0, permutationTriple_σ0, permutationTriple_σ1,
      MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, homeomorphMulEquivOfEq_mob01_periph0])
    (by rw [PermutationTriple.swap01_σ1, permutationTriple_σ1, permutationTriple_σ0,
      MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, homeomorphMulEquivOfEq_mob01_periph1])

end ThricePuncturedSphere

/-- **The monodromy triple of the pullback of a numbered cover along `z ↦ 1 − z` exchanges the
branch points `0` and `1`.** This is the branch-point operation `swap01` of
`TauCeti.PermutationTriple`, realized on the nose because `z ↦ 1 − z` fixes the basepoint. -/
@[simp]
theorem ConnectedFiberNumberedCover.connectedTriple_pullback_mob01
    (c : ConnectedFiberNumberedCover (X := TopCat.of ThricePuncturedSphere) basePt n) :
    (c.pullback mob01 mob01_basePt).connectedTriple =
      c.connectedTriple.reindexBranchPoints (Equiv.swap 0 1) := by
  apply Subtype.ext
  rw [ConnectedTriple.coe_reindexBranchPoints, PermutationTriple.reindexBranchPoints_swap_zero_one,
    coe_connectedTriple, coe_connectedTriple, IsCoveringMap.monodromyTriple_def,
    IsCoveringMap.monodromyTriple_def, permCongrHom_comp_monodromyPerm_pullback]
  exact permutationTriple_comp_mob01 _

/-- The triple of the pullback of a class of numbered covers along `z ↦ 1 − z` is the triple of
the class with the branch points `0` and `1` exchanged. -/
@[simp]
theorem ConnectedFiberNumberedCoverClass.triple_pullback_mob01
    (C : ConnectedFiberNumberedCoverClass (X := TopCat.of ThricePuncturedSphere) basePt n) :
    (C.pullback mob01 mob01_basePt).triple = C.triple.reindexBranchPoints (Equiv.swap 0 1) :=
  ind (fun c => by
    rw [pullback_mk, triple_mk, triple_mk]
    exact c.connectedTriple_pullback_mob01) C

/-- **Pulling a cover of `ℂ ∖ {0, 1}` back along `z ↦ 1 − z` acts on the isomorphism class of its
triple by exchanging the branch points `0` and `1`.** The topological branch-point operation on
covers is the combinatorial one on `TauCeti.ConnectedIsoClass`, at the generator
`Equiv.swap 0 1` of the right action of `Perm (Fin 3)`. -/
@[simp]
theorem ConnectedCoverClass.isoClass_pullback_mob01
    (C : ConnectedCoverClass (X := TopCat.of ThricePuncturedSphere) basePt n) :
    (C.pullback mob01 mob01_basePt).isoClass =
      MulOpposite.op (Equiv.swap (0 : Fin 3) 1) • C.isoClass := by
  obtain ⟨N, rfl⟩ := ConnectedFiberNumberedCoverClass.forgetNumbering_surjective C
  rw [← ConnectedFiberNumberedCoverClass.forgetNumbering_pullback,
    ConnectedFiberNumberedCoverClass.isoClass_forgetNumbering,
    ConnectedFiberNumberedCoverClass.isoClass_forgetNumbering,
    ConnectedFiberNumberedCoverClass.triple_pullback_mob01, ConnectedIsoClass.op_smul_mk]

end TauCeti
