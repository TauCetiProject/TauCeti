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
(`LieSubalgebra.map_lieInvariants_lieCartanRestriction`), and Weyl invariants separate Weyl orbits
of weights (`TauCeti.forall_mem_linearInvariants_lift_eq_iff`). As the Killing duality is
Weyl-equivariant (`TauCeti.weylGroupCorootRep_cartanEquivDual_symm`), invariant polynomial
functions on `L` separate Weyl orbits in `H`; this needs no inner automorphisms. Since such
functions are constant on `Int(L)`-orbits
(`TauCeti.SymmetricAlgebra.lift_eval_smul_of_mem_intLieAlgebra`), `Int(L)`-conjugate elements of
`H` are Weyl-conjugate.

This is the uniqueness input for weighted Dynkin diagrams: the neutral element of an `sl₂` triple
has exactly one dominant representative in its `Int(L)`-orbit.

## Main results

* `TauCeti.forall_mem_lieInvariants_lift_eval_eq_iff`: elements of `H` take equal values on every
  invariant polynomial function on `L` exactly when they are Weyl-conjugate.
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
  [FiniteDimensional K L] [IsKilling K L] {H : LieSubalgebra K L} [H.IsCartanSubalgebra]

/-- **Invariant polynomial functions separate Weyl orbits in a Cartan subalgebra.** Two elements
`x, y ∈ H` take equal values on every invariant polynomial function on `L` exactly when some
element of the Weyl group of the root system of `H` carries `x` to `y` through its action
`RootPairing.Equiv.coweightEquiv` on `H`. -/
theorem forall_mem_lieInvariants_lift_eval_eq_iff {x y : H} :
    (∀ p ∈ lieInvariants K L (Dual K L),
      lift (Dual.eval K L (x : L)) p = lift (Dual.eval K L (y : L)) p) ↔
      ∃ w : (rootSystem H).weylGroup, (w : (rootSystem H).Aut).coweightEquiv x = y := by
  -- an invariant polynomial function on `L` is `κ p` for some `p ∈ S(L)^L`, and its values at
  -- points of `H` are those of the Weyl invariant `lieCartanRestriction H p` at Killing duals; by
  -- Chevalley restriction every Weyl invariant arises this way
  have hinv : (∀ p ∈ lieInvariants K L (Dual K L),
      lift (Dual.eval K L (x : L)) p = lift (Dual.eval K L (y : L)) p) ↔
      ∀ q ∈ linearInvariants H, lift (cartanEquivDual H x) q = lift (cartanEquivDual H y) q := by
    rw [← map_killingSymmetricEquiv_lieInvariants,
      ← LieSubalgebra.map_lieInvariants_lieCartanRestriction H]
    simp only [Subalgebra.mem_map, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂]
    exact forall₂_congr fun p _ ↦
      (lift_eval_killingSymmetricEquiv H x p).congr (lift_eval_killingSymmetricEquiv H y p)
  rw [hinv, forall₂_congr fun _ _ ↦ eq_comm, forall_mem_linearInvariants_lift_eq_iff]
  refine exists_congr fun w ↦ ?_
  -- the Killing duality is Weyl-equivariant
  have h := weylGroupCorootRep_cartanEquivDual_symm w (cartanEquivDual H x)
  rw [RootPairing.weylGroupCorootRep_equivOp_apply, LinearEquiv.symm_apply_apply] at h
  rw [h, LinearEquiv.symm_apply_eq, inv_smul_eq_iff, eq_comm]

variable [LieAlgebra ℚ L]

/-- **Elements of a Cartan subalgebra conjugate under `Int(L)` are Weyl-conjugate.** If an inner
automorphism `g ∈ Int(L)` carries `x ∈ H` to `y ∈ H`, then some element `w` of the Weyl group of
the root system of `H` carries `x` to `y` through its action
`RootPairing.Equiv.coweightEquiv` on `H`. -/
theorem exists_coweightEquiv_eq_of_smul_eq {g : LinearMap.GeneralLinearGroup K L}
    (hg : g ∈ intLieAlgebra K L) {x y : H} (hxy : g • (x : L) = y) :
    ∃ w : (rootSystem H).weylGroup, (w : (rootSystem H).Aut).coweightEquiv x = y :=
  -- invariant polynomial functions are constant on `Int(L)`-orbits
  forall_mem_lieInvariants_lift_eval_eq_iff.mp fun _ hp ↦ by
    rw [← hxy, lift_eval_smul_of_mem_intLieAlgebra hg hp]

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
