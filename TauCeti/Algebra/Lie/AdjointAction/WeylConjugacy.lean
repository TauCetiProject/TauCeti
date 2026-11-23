/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.HighestWeight.ChevalleyRestriction
import TauCeti.Algebra.Lie.AdjointAction.SymmetricInvariants
public import TauCeti.Algebra.Lie.Sl2.Weyl.Cartan

/-!
# Elements of a Cartan subalgebra conjugate under `Int(L)` are Weyl-conjugate

Let `L` be a finite-dimensional Lie algebra with non-degenerate Killing form over an algebraically
closed field `K` of characteristic zero, and `H` a Cartan subalgebra. Two elements `x, y ∈ H` are
conjugate under the group `Int(L)` of inner automorphisms exactly when they are conjugate under
the Weyl group of the root system of `H`, acting on `H` through
`RootPairing.Equiv.coweightEquiv`.

One direction is that the Weyl group acts on `H` by inner automorphisms
(`TauCeti.exists_mem_intLieAlgebra_forall_smul_eq_coweightEquiv`). For the other, invariant
polynomial functions on `L` are constant on `Int(L)`-orbits
(`TauCeti.SymmetricAlgebra.lift_eval_smul_of_mem_intLieAlgebra`), and by Chevalley's restriction
theorem they separate Weyl orbits in `H`
(`TauCeti.forall_mem_lieInvariants_lift_eval_eq_iff_exists_weylGroup`).

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

open LieAlgebra LieAlgebra.IsKilling TauCeti.SymmetricAlgebra

variable {K L : Type*} [Field K] [CharZero K] [IsAlgClosed K] [LieRing L] [LieAlgebra K L]
  [LieAlgebra ℚ L] [FiniteDimensional K L] [IsKilling K L] {H : LieSubalgebra K L}
  [H.IsCartanSubalgebra]

/-- **Elements of a Cartan subalgebra conjugate under `Int(L)` are Weyl-conjugate.** If an inner
automorphism `g ∈ Int(L)` carries `x ∈ H` to `y ∈ H`, then some element `w` of the Weyl group of
the root system of `H` carries `x` to `y` through its action
`RootPairing.Equiv.coweightEquiv` on `H`. -/
theorem exists_coweightEquiv_eq_of_smul_eq {g : LinearMap.GeneralLinearGroup K L}
    (hg : g ∈ intLieAlgebra K L) {x y : H} (hxy : g • (x : L) = y) :
    ∃ w : (rootSystem H).weylGroup, (w : (rootSystem H).Aut).coweightEquiv x = y :=
  -- invariant polynomial functions are constant on `Int(L)`-orbits
  forall_mem_lieInvariants_lift_eval_eq_iff_exists_weylGroup.mp fun _ hp ↦ by
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
