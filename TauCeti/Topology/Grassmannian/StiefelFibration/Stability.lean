/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Algebra.OrthogonalGroup
public import TauCeti.Topology.Grassmannian.StiefelFibration.ForgetLast

/-!
# The stable range of the special orthogonal groups

The block embedding `SO(n + 1) → SO(r + n + 1)`, `B ↦ diag(1_r, B)`, is the inclusion of the fibre
of the Stiefel fibration `SO(r + n + 1) → V_r(ℝ^(r + n + 1))` over the standard frame
(`TauCeti.specialOrthogonalFrameFiberHomeomorph`). The base is `n`-connected
(`TauCeti.finiteOrthonormalFrame.subsingleton_homotopyGroup`), so the inclusion of the fibre is an
`n`-connected map (`TauCeti.TopCat.isNConnected_fiberι_of_mem_serreFibrations`). Hence the block
embedding induces isomorphisms `π_k(SO(n + 1)) → π_k(SO(r + n + 1))` for `k < n` and surjections
for `k = n`: the homotopy groups of `SO(m)` stabilize, `π_k(SO(m))` being independent of `m` once
`m ≥ k + 2`.

## Main results

* `TauCeti.Matrix.SpecialOrthogonalGroup.isNConnected_fromBlocksOne`: the block embedding
  `SO(m) → SO(r + m)` is `(m - 1)`-connected, so it is bijective on `π_k` for `k < m - 1` and
  surjective for `k = m - 1`
  (`ContinuousMap.IsNConnected.map_injective`, `ContinuousMap.IsNConnected.map_surjective`).

## References

* A. Hatcher, *Algebraic Topology*, Cambridge University Press, 2002, §4.2, the stable range of
  `SO(n)` following Example 4.53.
* N. Steenrod, *The Topology of Fibre Bundles*, Princeton University Press, 1951, §25.
* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Floer homology with DG coefficients.
  Applications to cotangent bundles*, arXiv:2404.07953, Lemma 6.35, which compares
  `π_(n-1)(SO(n))` with the stable groups.
-/

public section

open Matrix Matrix.SpecialOrthogonalGroup

noncomputable section

namespace TauCeti.Matrix.SpecialOrthogonalGroup

open finiteOrthonormalFrame

variable (r m : ℕ)

/-- **Stability of the special orthogonal groups.** The block embedding `SO(m) → SO(r + m)`,
`B ↦ diag(1_r, B)`, is an `(m - 1)`-connected map: it induces isomorphisms on `π_k` for
`k < m - 1` and surjections for `k = m - 1`. -/
theorem isNConnected_fromBlocksOne :
    (⟨fromBlocksOne ℝ r m, continuous_fromBlocksOne m⟩ :
      C(specialOrthogonalGroup (Fin m) ℝ, specialOrthogonalGroup (Fin (r + m)) ℝ)).IsNConnected
        (m - 1) := by
  cases m with
  | zero =>
    -- `SO(r)` is path-connected, so its `π_0` is trivial.
    refine ⟨fun _ ↦ ⟨1, PathConnectedSpace.joined _ _⟩, fun k hk ↦ absurd hk k.not_lt_zero,
      fun k hk B y ↦ ?_⟩
    obtain rfl : k = 0 := Nat.le_zero.1 hk
    have := (pathConnectedSpace_iff_subsingleton_homotopyGroup_zero (fromBlocksOne ℝ r 0 B)).1
      inferInstance
    exact ⟨Classical.arbitrary _, Subsingleton.elim _ _⟩
  | succ n =>
    rw [Nat.add_sub_cancel]
    let p : _root_.TopCat.of (specialOrthogonalGroup (Fin (r + (n + 1))) ℝ) ⟶
        _root_.TopCat.of (finiteOrthonormalFrame ℝ r (r + (n + 1))) :=
      _root_.TopCat.ofHom ⟨specialOrthogonalFrameMap r (n + 1),
        continuous_specialOrthogonalFrameMap r (n + 1)⟩
    -- The base `V_r(ℝ^(r + n + 1))` is `n`-connected, so the fibre over the standard frame is
    -- `n`-connected in the total space.
    have hfib : (p.fiberι (specialOrthogonalFrameMap r (n + 1) 1)).hom.IsNConnected n :=
      TopCat.isNConnected_fiberι_of_mem_serreFibrations
        specialOrthogonalFrameMap_mem_serreFibrations fun k hk ↦
          finiteOrthonormalFrame.subsingleton_homotopyGroup (by simp; omega) _
    -- The block embedding is the fibre inclusion after the homeomorphism of `SO(n + 1)` with the
    -- fibre.
    let φ := specialOrthogonalFrameFiberHomeomorph r (n + 1)
    convert hfib.comp (φ.toHomotopyEquiv.isWeakHomotopyEquivalence.isNConnected n) using 1
    ext B : 1
    exact (coe_specialOrthogonalFrameFiberHomeomorph_apply B).symm.trans
      (TopCat.Hom.fiberι_apply p _ (φ B)).symm

end TauCeti.Matrix.SpecialOrthogonalGroup
