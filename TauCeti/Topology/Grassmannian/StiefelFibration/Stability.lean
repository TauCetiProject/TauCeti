/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Algebra.OrthogonalGroup
public import TauCeti.Topology.Grassmannian.StiefelFibration.Basic
public import TauCeti.Topology.Grassmannian.StiefelFibration.ForgetLast
import TauCeti.Topology.Homotopy.HomotopyGroup.PathComponent
import TauCeti.Topology.Homotopy.HomotopyGroup.TopologicalMonoid

/-!
# The stable range of the orthogonal and special orthogonal groups

The block embedding `SO(n + 1) → SO(r + n + 1)`, `B ↦ diag(1_r, B)`, is the inclusion of the fibre
of the Stiefel fibration `SO(r + n + 1) → V_r(ℝ^(r + n + 1))` over the standard frame
(`TauCeti.specialOrthogonalFrameFiberHomeomorph`). The base is `n`-connected
(`TauCeti.finiteOrthonormalFrame.subsingleton_homotopyGroup`), so the inclusion of the fibre is an
`n`-connected map (`TauCeti.TopCat.isNConnected_fiberι_of_mem_serreFibrations`). Hence the block
embedding induces isomorphisms `π_k(SO(n + 1)) → π_k(SO(r + n + 1))` for `k < n` and surjections
for `k = n`: the homotopy groups of `SO(m)` stabilize, `π_k(SO(m))` being independent of `m` once
`m ≥ k + 2`.

Reindexing `1 ⊕ Fin n` to `Fin n ⊕ 1` specializes `r = 1` to the upper-left block inclusion
`SO(n) → SO(n + 1)` (`TauCeti.isNConnected_specialOrthogonalBlockSucc`). Since `SO(m)` embeds onto
the identity path component of `O(m)`, the inclusion `SO(m) → O(m)` induces bijections on `π_N`
for every nonempty `N`
(`Matrix.specialOrthogonalGroup.bijective_homotopyGroup_map_toOrthogonalGroup`),
and transporting across the `SO`/`O` square together with `π_0` surjectivity via the diagonal
reflection yields `n`-connectivity of `O(n + 1) → O(n + 2)`
(`TauCeti.isNConnected_orthogonalBlockSucc`).

## Main results

* `TauCeti.Matrix.SpecialOrthogonalGroup.isNConnected_fromBlocksOne`: the block embedding
  `SO(m) → SO(r + m)` is `(m - 1)`-connected, so it is bijective on `π_k` for `k < m - 1` and
  surjective for `k = m - 1`
  (`ContinuousMap.IsNConnected.map_injective`, `ContinuousMap.IsNConnected.map_surjective`).
* `Matrix.specialOrthogonalGroup.bijective_homotopyGroup_map_toOrthogonalGroup`: the inclusion
  `SO(n) → O(n)` induces bijections on `π_N` for every nonempty `N`.
* `TauCeti.isNConnected_specialOrthogonalBlockSucc`: `SO(n) → SO(n + 1)` is `(n - 1)`-connected.
* `TauCeti.isNConnected_orthogonalBlockSucc`: `O(n + 1) → O(n + 2)` is `n`-connected.

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
          finiteOrthonormalFrame.subsingleton_homotopyGroup_real (by simp; omega) _
    -- The block embedding is the fibre inclusion after the homeomorphism of `SO(n + 1)` with the
    -- fibre.
    let φ := specialOrthogonalFrameFiberHomeomorph r (n + 1)
    convert hfib.comp (φ.toHomotopyEquiv.isWeakHomotopyEquivalence.isNConnected n) using 1
    ext B : 1
    exact (coe_specialOrthogonalFrameFiberHomeomorph_apply B).symm.trans
      (TopCat.Hom.fiberι_apply p _ (φ B)).symm

end TauCeti.Matrix.SpecialOrthogonalGroup

namespace Matrix.specialOrthogonalGroup

open Topology

/-- In positive dimension, the inclusion `SO(n) → O(n)` induces bijections on homotopy groups
(since `SO(n)` embeds onto the identity path component of `O(n)`). -/
theorem bijective_homotopyGroup_map_toOrthogonalGroup {n : ℕ} (N : Type*) [Nonempty N] :
    Function.Bijective (HomotopyGroup.map (N := N)
      ⟨toOrthogonalGroup (n := Fin n) (R := ℝ), continuous_toOrthogonalGroup⟩
      (map_one toOrthogonalGroup)) :=
  HomotopyGroup.bijective_map_of_isEmbedding_of_pathComponent_subset
    (isClosedEmbedding_toOrthogonalGroup (n := Fin n) (R := ℝ)).isEmbedding
    (fun A hA ↦ by
      have hdet : (A : Matrix (Fin n) (Fin n) ℝ).det = 1 := by
        simpa using (TauCeti.Matrix.joined_orthogonalGroup_iff_det_eq.1 hA).symm
      exact ⟨⟨A, A.property, hdet⟩, Subtype.ext (coe_toOrthogonalGroup _)⟩)
    (map_one toOrthogonalGroup)

end Matrix.specialOrthogonalGroup

namespace TauCeti

/-- **Step connectivity for `SO`**: the block inclusion `SO(n) → SO(n + 1)` is
`(n - 1)`-connected. -/
theorem isNConnected_specialOrthogonalBlockSucc (n : ℕ) :
    (continuousSpecialOrthogonalBlockSucc ℝ n).toContinuousMap.IsNConnected (n - 1) := by
  let e : Fin (n + 1) ≃ Fin (1 + n) :=
    (finSumFinEquiv.symm.trans (Equiv.sumComm (Fin n) (Fin 1))).trans finSumFinEquiv
  let φHomeo : _root_.Matrix.specialOrthogonalGroup (Fin (n + 1)) ℝ ≃ₜ
      _root_.Matrix.specialOrthogonalGroup (Fin (1 + n)) ℝ :=
    (_root_.Matrix.specialOrthogonalReindexContinuousMulEquiv ℝ e).toHomeomorph
  have hcomp : φHomeo.toHomotopyEquiv.toFun.comp
        (continuousSpecialOrthogonalBlockSucc ℝ n).toContinuousMap =
      ⟨fromBlocksOne ℝ 1 n, finiteOrthonormalFrame.continuous_fromBlocksOne n⟩ := by
    ext A i j
    rw [ContinuousMap.comp_apply, Homeomorph.coe_toHomotopyEquiv]
    -- Unfold `φHomeo` to `specialOrthogonalReindexContinuousMulEquiv ℝ e`.
    change (_root_.Matrix.specialOrthogonalReindexContinuousMulEquiv ℝ e
      (continuousSpecialOrthogonalBlockSucc ℝ n A) :
        _root_.Matrix (Fin (1 + n)) (Fin (1 + n)) ℝ) i j = _
    rw [continuousSpecialOrthogonalBlockSucc_apply,
      _root_.Matrix.coe_specialOrthogonalReindexContinuousMulEquiv_apply]
    exact congrFun (congrFun (reindex_coe_specialOrthogonalBlockSucc_eq_fromBlocksOne ℝ n A) i) j
  refine (ContinuousMap.IsWeakHomotopyEquivalence.isNConnected_comp_iff
    φHomeo.toHomotopyEquiv.isWeakHomotopyEquivalence).1 ?_
  rw [hcomp]
  exact TauCeti.Matrix.SpecialOrthogonalGroup.isNConnected_fromBlocksOne 1 n

private lemma homotopyGroup_toOrthogonalGroup_blockSucc_sq (n : ℕ) (N : Type*) :
    HomotopyGroup.map (N := N)
        ⟨_root_.Matrix.specialOrthogonalGroup.toOrthogonalGroup,
          _root_.Matrix.specialOrthogonalGroup.continuous_toOrthogonalGroup⟩
        (map_one _root_.Matrix.specialOrthogonalGroup.toOrthogonalGroup) ∘
      HomotopyGroup.map (N := N) (continuousSpecialOrthogonalBlockSucc ℝ (n + 1)).toContinuousMap
        (map_one (continuousSpecialOrthogonalBlockSucc ℝ (n + 1))) =
    HomotopyGroup.map (N := N) (continuousOrthogonalBlockSucc ℝ (n + 1)).toContinuousMap
        (map_one (continuousOrthogonalBlockSucc ℝ (n + 1))) ∘
      HomotopyGroup.map (N := N)
        ⟨_root_.Matrix.specialOrthogonalGroup.toOrthogonalGroup,
          _root_.Matrix.specialOrthogonalGroup.continuous_toOrthogonalGroup⟩
        (map_one _root_.Matrix.specialOrthogonalGroup.toOrthogonalGroup) := by
  have hcomp :
      (⟨_root_.Matrix.specialOrthogonalGroup.toOrthogonalGroup,
          _root_.Matrix.specialOrthogonalGroup.continuous_toOrthogonalGroup⟩ :
          C(_root_.Matrix.specialOrthogonalGroup (Fin (n + 2)) ℝ,
            _root_.Matrix.orthogonalGroup (Fin (n + 2)) ℝ)).comp
        (continuousSpecialOrthogonalBlockSucc ℝ (n + 1)).toContinuousMap =
      (continuousOrthogonalBlockSucc ℝ (n + 1)).toContinuousMap.comp
        ⟨_root_.Matrix.specialOrthogonalGroup.toOrthogonalGroup,
          _root_.Matrix.specialOrthogonalGroup.continuous_toOrthogonalGroup⟩ :=
    ContinuousMap.ext fun A ↦ Subtype.ext <| by simp
  exact (HomotopyGroup.map_comp_map _
      (map_one _root_.Matrix.specialOrthogonalGroup.toOrthogonalGroup) _
      (map_one (continuousSpecialOrthogonalBlockSucc ℝ (n + 1)))).trans
    (HomotopyGroup.map_comp_map_of_comp_eq hcomp.symm
      (map_one (continuousOrthogonalBlockSucc ℝ (n + 1)))
      (map_one _root_.Matrix.specialOrthogonalGroup.toOrthogonalGroup) _).symm

/-- **Step connectivity for `O`**: for `n ≥ 1`, the block inclusion `O(n) → O(n + 1)` is
`(n - 1)`-connected. Equivalently, `O(n + 1) → O(n + 2)` is `n`-connected for every `n`. -/
theorem isNConnected_orthogonalBlockSucc (n : ℕ) :
    (continuousOrthogonalBlockSucc ℝ (n + 1)).toContinuousMap.IsNConnected n := by
  let f := continuousOrthogonalBlockSucc ℝ (n + 1)
  have hex : ∀ y : _root_.Matrix.orthogonalGroup (Fin (n + 2)) ℝ, ∃ x, Joined (f x) y := by
    intro y
    rcases det_eq_one_or_neg_one_of_mem_orthogonalGroup y.property with hy | hy
    · exact ⟨1, TauCeti.Matrix.joined_orthogonalGroup_iff_det_eq.2 (by simp [f, hy])⟩
    · refine ⟨orthogonalDiagonalReflection ℝ 0,
        TauCeti.Matrix.joined_orthogonalGroup_iff_det_eq.2 ?_⟩
      dsimp only [f]
      rw [continuousOrthogonalBlockSucc_apply, coe_orthogonalBlockSucc,
        _root_.Matrix.det_blockSucc, det_orthogonalDiagonalReflection, hy]
  refine ⟨hex, fun k hk x ↦ ?_, fun k hk x ↦ ?_⟩
  · cases k with
    | zero =>
      refine HomotopyGroup.map_injective_of_isEmpty_of_joined f.toContinuousMap rfl fun a b hab ↦ ?_
      rw [TauCeti.Matrix.joined_orthogonalGroup_iff_det_eq] at hab ⊢
      simpa [f] using hab
    | succ m =>
      refine HomotopyGroup.injective_map_of_one f (Fin (m + 1)) ?_ x
      have hinjSO := (HomotopyGroup.injective_map_congr rfl rfl
          (map_one (continuousSpecialOrthogonalBlockSucc ℝ (n + 1)))).1
        ((isNConnected_specialOrthogonalBlockSucc (n + 1)).injective (m + 1) (by omega) 1)
      have bi₁ := _root_.Matrix.specialOrthogonalGroup.bijective_homotopyGroup_map_toOrthogonalGroup
        (n := n + 1) (Fin (m + 1))
      have bi₂ := _root_.Matrix.specialOrthogonalGroup.bijective_homotopyGroup_map_toOrthogonalGroup
        (n := n + 2) (Fin (m + 1))
      exact Function.Injective.of_comp_right
        (homotopyGroup_toOrthogonalGroup_blockSucc_sq n (Fin (m + 1)) ▸ bi₂.1.comp hinjSO) bi₁.2
  · cases k with
    | zero =>
      exact HomotopyGroup.map_surjective_of_isEmpty_of_exists_joined f.toContinuousMap rfl hex
    | succ m =>
      refine HomotopyGroup.surjective_map_of_one f (Fin (m + 1)) ?_ x
      have hsurjSO := (HomotopyGroup.surjective_map_congr rfl rfl
          (map_one (continuousSpecialOrthogonalBlockSucc ℝ (n + 1)))).1
        ((isNConnected_specialOrthogonalBlockSucc (n + 1)).surjective (m + 1) (by omega) 1)
      have bi₂ := _root_.Matrix.specialOrthogonalGroup.bijective_homotopyGroup_map_toOrthogonalGroup
        (n := n + 2) (Fin (m + 1))
      exact (homotopyGroup_toOrthogonalGroup_blockSucc_sq n (Fin (m + 1)) ▸
        bi₂.2.comp hsurjSO).of_comp

end TauCeti
