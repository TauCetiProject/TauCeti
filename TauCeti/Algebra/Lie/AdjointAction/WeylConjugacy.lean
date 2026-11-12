/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.HighestWeight.ChevalleyRestriction
public import TauCeti.Algebra.Lie.HighestWeight.CentralCharacter.OrbitSeparation
public import TauCeti.Algebra.Lie.Sl2.Weyl.Cartan
import TauCeti.Algebra.Lie.Weights.InvariantForm

/-!
# Elements of a Cartan subalgebra conjugate under `Int(L)` are Weyl-conjugate

Let `L` be a finite-dimensional Lie algebra with non-degenerate Killing form over an algebraically
closed field `K` of characteristic zero, and `H` a Cartan subalgebra. Two elements `x, y ∈ H` are
conjugate under the group `Int(L)` of inner automorphisms exactly when they are conjugate under
the Weyl group of the root system of `H`, acting on `H` through
`RootPairing.Equiv.coweightEquiv`.

One direction is that the Weyl group acts on `H` by inner automorphisms
(`TauCeti.exists_mem_intLieAlgebra_forall_smul_eq_coweightEquiv`). The other is the
invariant-theoretic argument through Chevalley's restriction theorem. Every Weyl invariant
`q ∈ S(H)^W` is the restriction to `H` of an invariant polynomial function `p` on `L`
(`LieSubalgebra.map_lieInvariants_lieCartanRestriction`), and `p` is constant on `Int(L)`-orbits
(`TauCeti.SymmetricAlgebra.lift_eval_smul_of_mem_intLieAlgebra`). So the Killing duals of `x` and
`y` take the same value on every Weyl invariant, and Weyl invariants separate Weyl orbits of
weights (`TauCeti.forall_mem_linearInvariants_lift_eq_iff`). The Killing duality is
Weyl-equivariant (`TauCeti.weylGroupCorootRep_cartanEquivDual_symm`), which brings the conclusion
back to `H`.

This is the uniqueness input for weighted Dynkin diagrams: the neutral element of an `sl₂` triple
has exactly one dominant representative in its `Int(L)`-orbit.

## Main results

* `TauCeti.exists_coweightEquiv_eq_of_smul_eq`: if `g ∈ Int(L)` carries `x ∈ H` to `y ∈ H`, some
  element of the Weyl group carries `x` to `y`.
* `TauCeti.exists_mem_intLieAlgebra_smul_eq_iff_exists_coweightEquiv_eq`: elements of `H` are
  `Int(L)`-conjugate exactly when they are Weyl-conjugate.

## References

* D. H. Collingwood and W. M. McGovern, *Nilpotent Orbits in Semisimple Lie Algebras*, Van
  Nostrand Reinhold, 1993, §2.2.
* J. E. Humphreys, *Introduction to Lie Algebras and Representation Theory*, GTM 9, §23.1, for
  Chevalley's restriction theorem.
-/

public section

namespace TauCeti

open LieAlgebra LieAlgebra.IsKilling _root_.LieModule Module _root_.SymmetricAlgebra
  TauCeti.SymmetricAlgebra

variable {K L : Type*} [Field K] [CharZero K] [IsAlgClosed K] [LieRing L] [LieAlgebra K L]
  [LieAlgebra ℚ L] [FiniteDimensional K L] [IsKilling K L] {H : LieSubalgebra K L}
  [H.IsCartanSubalgebra]

/-- Weyl invariants take equal values at the Killing duals of `Int(L)`-conjugate elements of `H`:
such an invariant is the restriction of an invariant polynomial function on `L`. -/
private theorem lift_cartanEquivDual_eq_of_smul_eq {q : _root_.SymmetricAlgebra K H}
    (hq : q ∈ linearInvariants H) {g : LinearMap.GeneralLinearGroup K L}
    (hg : g ∈ intLieAlgebra K L) {x y : H} (hxy : g • (x : L) = y) :
    lift (cartanEquivDual H x) q = lift (cartanEquivDual H y) q := by
  rw [← LieSubalgebra.map_lieInvariants_lieCartanRestriction H] at hq
  obtain ⟨p, hp, rfl⟩ := Subalgebra.mem_map.mp hq
  -- evaluating the polynomial function `κ p` on `L` at a point of `H` evaluates the restriction
  rw [← lift_eval_killingSymmetricEquiv, ← lift_eval_killingSymmetricEquiv, ← hxy,
    lift_eval_smul_of_mem_intLieAlgebra hg
      ((killingSymmetricEquiv_mem_lieInvariants_iff K L).mpr hp)]

/-- **Elements of a Cartan subalgebra conjugate under `Int(L)` are Weyl-conjugate.** If an inner
automorphism `g ∈ Int(L)` carries `x ∈ H` to `y ∈ H`, then some element `w` of the Weyl group of
the root system of `H` carries `x` to `y` through its action
`RootPairing.Equiv.coweightEquiv` on `H`. -/
theorem exists_coweightEquiv_eq_of_smul_eq {g : LinearMap.GeneralLinearGroup K L}
    (hg : g ∈ intLieAlgebra K L) {x y : H} (hxy : g • (x : L) = y) :
    ∃ w : (rootSystem H).weylGroup, (w : (rootSystem H).Aut).coweightEquiv x = y := by
  obtain ⟨w, hw⟩ := forall_mem_linearInvariants_lift_eq_iff.mp fun q hq ↦
    (lift_cartanEquivDual_eq_of_smul_eq hq hg hxy).symm
  refine ⟨w, ?_⟩
  -- the Killing duality is Weyl-equivariant
  have h := weylGroupCorootRep_cartanEquivDual_symm w (cartanEquivDual H x)
  rwa [RootPairing.weylGroupCorootRep_equivOp_apply, LinearEquiv.symm_apply_apply, ← hw,
    inv_smul_smul, LinearEquiv.symm_apply_apply] at h

/-- **`Int(L)`-conjugacy on a Cartan subalgebra is Weyl conjugacy.** Two elements `x, y` of `H` are
conjugate under the group `Int(L)` of inner automorphisms exactly when some element of the Weyl
group of the root system of `H` carries `x` to `y`. -/
theorem exists_mem_intLieAlgebra_smul_eq_iff_exists_coweightEquiv_eq {x y : H} :
    (∃ g ∈ intLieAlgebra K L, g • (x : L) = y) ↔
      ∃ w : (rootSystem H).weylGroup, (w : (rootSystem H).Aut).coweightEquiv x = y := by
  refine ⟨fun ⟨g, hg, hxy⟩ ↦ exists_coweightEquiv_eq_of_smul_eq hg hxy, fun ⟨w, hw⟩ ↦ ?_⟩
  obtain ⟨g, hg, hgH⟩ := exists_mem_intLieAlgebra_forall_smul_eq_coweightEquiv w
  exact ⟨g, hg, by rw [hgH, hw]⟩

end TauCeti
