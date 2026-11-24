/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Singular.Cubical.MonoidAlgebra.Augmentation

/-!
# Cubical chains on a totally disconnected space with a monoid action

Let `G` be a topological monoid acting continuously from the right on a totally disconnected space
`Y`, for instance a discrete one such as the fibre of a covering map. Every singular cube in `Y` is
constant, so the normalized cubical chains of `Y` vanish in positive dimensions, and the normalized
`0`-chains are the free module on the points of `Y`. So the DG right module `C_*(Y; R)` over the
chains `C_*(G; R)` is concentrated in degree zero
(`TauCeti.isConcentratedInDegreeZero_cubicalChainModuleDG`), and its underlying module is the free
module `Y →₀ R` (`TauCeti.cubicalChainModuleZeroEquiv`). Under this identification the point chain
of `g ∈ G` acts by the permutation `y ↦ y · g` of the basis
(`TauCeti.op_lof_point_smul_cubicalChainModuleZeroEquiv`).

This is the form taken by the DG local system of a covering map, whose fibre is discrete: it is
the permutation module of the fibre, concentrated in degree zero.

## Main definitions

* `TauCeti.cubicalChainModuleZeroEquiv Y G R`: the module of chains of a totally disconnected space
  is the free module on its points.

## Main results

* `TauCeti.cubicalChainModuleLof_zero_bijective`: every chain of a totally disconnected space is a
  `0`-chain, in a unique way.
* `TauCeti.isConcentratedInDegreeZero_cubicalChainModuleDG`: the DG right module of chains of a
  totally disconnected space is concentrated in degree zero.
* `TauCeti.op_lof_point_smul_cubicalChainModuleZeroEquiv`: the point chain of `g` acts on the free
  module by the permutation `y ↦ y · g` of the points.

## References

* W. S. Massey, *Singular Homology Theory*, GTM 70, Springer, 1980, Chapter II.
* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Morse homology with differential graded
  coefficients*, Progress in Mathematics 360, Birkhäuser, 2025, §7.1.
-/

public section

noncomputable section

open MulOpposite

namespace TauCeti

open NormalizedCubicalChain

variable (Y G : Type*) [TopologicalSpace Y] [TotallyDisconnectedSpace Y] (R : Type*) [CommRing R]

/-- **Every chain of a totally disconnected space is a `0`-chain, in a unique way**: the inclusion
of the `0`-chains into the module of chains is bijective, since the chains of positive dimension
vanish. -/
theorem cubicalChainModuleLof_zero_bijective :
    Function.Bijective (cubicalChainModuleLof Y G R 0) := by
  refine ⟨fun c c' h ↦ DirectSum.of_injective (β := fun n ↦ NormalizedCubicalChain Y R n) 0 ?_,
    fun m ↦ ?_⟩
  · simpa [← DirectSum.lof_eq_of R] using congrArg (cubicalChainModuleEquiv Y G R) h
  induction m using cubicalChainModule.induction_on with
  | lof n c =>
    cases n with
    | zero => exact ⟨c, rfl⟩
    | succ n => exact ⟨0, by rw [Subsingleton.elim c 0, map_zero, map_zero]⟩
  | add m m' hm hm' =>
    obtain ⟨c, rfl⟩ := hm
    obtain ⟨c', rfl⟩ := hm'
    exact ⟨c + c', map_add _ c c'⟩

/-- **The chains of a totally disconnected space are the free module on its points**: the
normalized `0`-chains (`TauCeti.NormalizedCubicalChain.zeroChainEquiv`), which are all the
chains (`TauCeti.cubicalChainModuleLof_zero_bijective`). -/
def cubicalChainModuleZeroEquiv : (Y →₀ R) ≃ₗ[R] cubicalChainModule Y G R :=
  (zeroChainEquiv Y R).trans
    (LinearEquiv.ofBijective _ (cubicalChainModuleLof_zero_bijective Y G R))

variable {Y G R}

/-- The basis vector at a point is the point chain of that point. -/
@[simp]
theorem cubicalChainModuleZeroEquiv_single (y : Y) (r : R) :
    cubicalChainModuleZeroEquiv Y G R (Finsupp.single y r) =
      r • cubicalChainModulePoint Y G R y := by
  rw [cubicalChainModuleZeroEquiv, LinearEquiv.trans_apply, zeroChainEquiv_single,
    LinearEquiv.ofBijective_apply, map_smul, cubicalChainModulePoint_def]

variable (Y G R) in
/-- **The chains of a totally disconnected space are concentrated in degree zero**, as a DG right
module over the chains of a topological monoid acting on the space. -/
theorem isConcentratedInDegreeZero_cubicalChainModuleDG [Monoid G] [TopologicalSpace G]
    [ContinuousMul G] [MulAction Gᵐᵒᵖ Y] [ContinuousSMul Gᵐᵒᵖ Y] :
    (cubicalChainModuleDG Y G R).IsConcentratedInDegreeZero :=
  DGRightModuleCat.isConcentratedInDegreeZero_iff.2 fun q hq ↦ (Submodule.eq_bot_iff _).2
    fun m hm ↦ by
      rcases mem_cubicalChainModuleGrading_iff.1 hm with h | ⟨n, c, hn, rfl⟩
      · exact h
      · obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := Nat.exists_eq_succ_of_ne_zero (by omega)
        rw [Subsingleton.elim c 0, map_zero]

/-- **The point chain of `g` permutes the basis of points**: on the chains of a totally
disconnected space, identified with the free module on its points, the point chain of `g ∈ G` acts
by the map induced by `y ↦ y · g`. -/
theorem op_lof_point_smul_cubicalChainModuleZeroEquiv [Monoid G] [TopologicalSpace G]
    [ContinuousMul G] [MulAction Gᵐᵒᵖ Y] [ContinuousSMul Gᵐᵒᵖ Y] (g : G) (x : Y →₀ R) :
    op (cubicalChainLof G R 0 (ofCube G R (SingularCube.point g))) •
        cubicalChainModuleZeroEquiv Y G R x =
      cubicalChainModuleZeroEquiv Y G R (Finsupp.mapDomain (op g • ·) x) := by
  induction x using Finsupp.induction_linear with
  | zero => simp
  | add x x' hx hx' => rw [map_add, smul_add, hx, hx', Finsupp.mapDomain_add, map_add]
  | single y r =>
    rw [Finsupp.mapDomain_single, cubicalChainModuleZeroEquiv_single,
      cubicalChainModuleZeroEquiv_single, smul_comm, op_point_smul_cubicalChainModulePoint]

end TauCeti
