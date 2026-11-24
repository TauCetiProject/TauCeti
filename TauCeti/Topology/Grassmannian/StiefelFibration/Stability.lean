/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Algebra.OrthogonalGroup
public import TauCeti.Topology.Grassmannian.StiefelFibration.Basic
public import TauCeti.Topology.Grassmannian.StiefelFibration.ForgetLast
import TauCeti.Topology.Algebra.Matrix.UnitaryGroup
import TauCeti.Topology.Homotopy.HomotopyGroup.PathComponent

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
theorem bijective_homotopyGroup_toOrthogonalGroup {n : ℕ} (N : Type*) [Nonempty N] :
    Function.Bijective (HomotopyGroup.map (N := N)
      ⟨toOrthogonalGroup (n := Fin n) (R := ℝ), continuous_toOrthogonalGroup⟩
      (map_one toOrthogonalGroup)) := by
  let S := Set.range (toOrthogonalGroup (n := Fin n) (R := ℝ))
  let e : specialOrthogonalGroup (Fin n) ℝ ≃ₜ S :=
    (isClosedEmbedding_toOrthogonalGroup (n := Fin n) (R := ℝ)).isEmbedding.toHomeomorph
  have hS : pathComponent (1 : orthogonalGroup (Fin n) ℝ) ⊆ S := fun A hA ↦ by
    have hdet : (A : Matrix (Fin n) (Fin n) ℝ).det = 1 := by
      simpa using (TauCeti.Matrix.joined_orthogonalGroup_iff_det_eq.1 hA).symm
    exact ⟨⟨A, A.property, hdet⟩, Subtype.ext (coe_toOrthogonalGroup _)⟩
  have h1 : ((e 1 : S) : orthogonalGroup (Fin n) ℝ) = 1 := map_one toOrthogonalGroup
  have hsub := HomotopyGroup.bijective_map_subtypeVal_of_pathComponent_subset
    (N := N) (x := e 1) (h1.symm ▸ hS) h1
  have he := (HomotopyGroup.homeomorphEquiv (N := N) e 1).bijective
  rw [funext (HomotopyGroup.homeomorphEquiv_apply e 1)] at he
  have hcomp : (⟨Subtype.val, continuous_subtypeVal⟩ : C(S, _)).comp ⟨e, e.continuous⟩ =
      ⟨toOrthogonalGroup (n := Fin n) (R := ℝ), continuous_toOrthogonalGroup⟩ :=
    ContinuousMap.ext fun _ ↦ rfl
  have hbij := hsub.comp he
  rwa [HomotopyGroup.map_comp_map_of_comp_eq hcomp h1 rfl (map_one toOrthogonalGroup)] at hbij

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
  let φ : C(_root_.Matrix.specialOrthogonalGroup (Fin (n + 1)) ℝ,
      _root_.Matrix.specialOrthogonalGroup (Fin (1 + n)) ℝ) :=
    φHomeo.toHomotopyEquiv.toFun
  have hcomp : φ.comp (continuousSpecialOrthogonalBlockSucc ℝ n).toContinuousMap =
      ⟨fromBlocksOne ℝ 1 n, finiteOrthonormalFrame.continuous_fromBlocksOne n⟩ := by
    ext A i j
    have hA : φ ((continuousSpecialOrthogonalBlockSucc ℝ n).toContinuousMap A) =
        _root_.Matrix.specialOrthogonalReindexContinuousMulEquiv ℝ e
          (specialOrthogonalBlockSucc ℝ n A) := by
      change _root_.Matrix.specialOrthogonalReindexContinuousMulEquiv ℝ e
        (continuousSpecialOrthogonalBlockSucc ℝ n A) = _
      rw [continuousSpecialOrthogonalBlockSucc_apply]
    rw [ContinuousMap.comp_apply, hA,
      _root_.Matrix.coe_specialOrthogonalReindexContinuousMulEquiv_apply]
    exact congrFun (congrFun (reindex_coe_specialOrthogonalBlockSucc_eq_fromBlocksOne ℝ n A) i) j
  refine (ContinuousMap.IsWeakHomotopyEquivalence.isNConnected_comp_iff
    φHomeo.toHomotopyEquiv.isWeakHomotopyEquivalence).1 ?_
  rw [hcomp]
  exact TauCeti.Matrix.SpecialOrthogonalGroup.isNConnected_fromBlocksOne 1 n

section LeftTranslation

private lemma leftTranslation_homotopyGroup_sq {G H : Type*} [Group G] [Group H]
    [TopologicalSpace G] [TopologicalSpace H] [ContinuousMul G] [ContinuousMul H]
    (f : G →ₜ* H) (N : Type*) (x : G) :
    HomotopyGroup.map (N := N)
        ⟨Homeomorph.mulLeft (f x), (Homeomorph.mulLeft (f x)).continuous⟩ (mul_one (f x)) ∘
      HomotopyGroup.map (N := N) f.toContinuousMap (map_one f) =
    HomotopyGroup.map (N := N) f.toContinuousMap rfl ∘
      HomotopyGroup.map (N := N)
        ⟨Homeomorph.mulLeft x, (Homeomorph.mulLeft x).continuous⟩ (mul_one x) := by
  have hcomm :
      (⟨Homeomorph.mulLeft (f x), (Homeomorph.mulLeft (f x)).continuous⟩ : C(H, H)).comp
        f.toContinuousMap =
      f.toContinuousMap.comp
        ⟨Homeomorph.mulLeft x, (Homeomorph.mulLeft x).continuous⟩ :=
    ContinuousMap.ext fun y ↦ (map_mul f x y).symm
  exact (HomotopyGroup.map_comp_map _ (mul_one (f x)) f.toContinuousMap (map_one f)).trans
    (HomotopyGroup.map_comp_map_of_comp_eq hcomm.symm rfl (mul_one x) _).symm

private lemma injective_homotopyGroup_map_of_one {G H : Type*} [Group G] [Group H]
    [TopologicalSpace G] [TopologicalSpace H] [ContinuousMul G] [ContinuousMul H]
    (f : G →ₜ* H) (N : Type*)
    (hinj : Function.Injective (HomotopyGroup.map (N := N) f.toContinuousMap (map_one f)))
    (x : G) :
    Function.Injective (HomotopyGroup.map (N := N) f.toContinuousMap (x := x) rfl) := by
  have hx :=
    (HomotopyGroup.homeomorphEquivOfEq (N := N) (Homeomorph.mulLeft x) (mul_one x)).bijective
  have hfx := (HomotopyGroup.homeomorphEquivOfEq (N := N) (Homeomorph.mulLeft (f x))
    (mul_one (f x))).bijective
  intro a b hab
  obtain ⟨a', rfl⟩ := hx.2 a
  obtain ⟨b', rfl⟩ := hx.2 b
  have hcomp :
      (HomotopyGroup.map (N := N) f.toContinuousMap rfl ∘
        HomotopyGroup.map (N := N)
          ⟨Homeomorph.mulLeft x, (Homeomorph.mulLeft x).continuous⟩ (mul_one x)) a' =
      (HomotopyGroup.map (N := N) f.toContinuousMap rfl ∘
        HomotopyGroup.map (N := N)
          ⟨Homeomorph.mulLeft x, (Homeomorph.mulLeft x).continuous⟩ (mul_one x)) b' := hab
  rw [← leftTranslation_homotopyGroup_sq] at hcomp
  exact congrArg _ (hinj (hfx.1 hcomp))

private lemma surjective_homotopyGroup_map_of_one {G H : Type*} [Group G] [Group H]
    [TopologicalSpace G] [TopologicalSpace H] [ContinuousMul G] [ContinuousMul H]
    (f : G →ₜ* H) (N : Type*)
    (hsurj : Function.Surjective (HomotopyGroup.map (N := N) f.toContinuousMap (map_one f)))
    (x : G) :
    Function.Surjective (HomotopyGroup.map (N := N) f.toContinuousMap (x := x) rfl) := by
  have hfx := (HomotopyGroup.homeomorphEquivOfEq (N := N) (Homeomorph.mulLeft (f x))
    (mul_one (f x))).bijective
  have hcomp : Function.Surjective
      (HomotopyGroup.map (N := N) f.toContinuousMap rfl ∘
        HomotopyGroup.map (N := N)
          ⟨Homeomorph.mulLeft x, (Homeomorph.mulLeft x).continuous⟩ (mul_one x)) := by
    rw [← leftTranslation_homotopyGroup_sq]
    exact hfx.2.comp hsurj
  exact hcomp.of_comp

end LeftTranslation

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
      refine injective_homotopyGroup_map_of_one f (Fin (m + 1)) ?_ x
      have hinjSO := (HomotopyGroup.injective_map_congr rfl rfl
          (map_one (continuousSpecialOrthogonalBlockSucc ℝ (n + 1)))).1
        ((isNConnected_specialOrthogonalBlockSucc (n + 1)).injective (m + 1) (by omega) 1)
      have bi₁ := _root_.Matrix.specialOrthogonalGroup.bijective_homotopyGroup_toOrthogonalGroup
        (n := n + 1) (Fin (m + 1))
      have bi₂ := _root_.Matrix.specialOrthogonalGroup.bijective_homotopyGroup_toOrthogonalGroup
        (n := n + 2) (Fin (m + 1))
      intro a b hab
      obtain ⟨a', rfl⟩ := bi₁.2 a
      obtain ⟨b', rfl⟩ := bi₁.2 b
      have hcomp := congrArg id hab
      rw [← Function.comp_apply (f := HomotopyGroup.map (N := Fin (m + 1)) f.toContinuousMap _),
        ← Function.comp_apply (f := HomotopyGroup.map (N := Fin (m + 1)) f.toContinuousMap _),
        ← homotopyGroup_toOrthogonalGroup_blockSucc_sq n (Fin (m + 1))] at hcomp
      exact congrArg _ (hinjSO (bi₂.1 hcomp))
  · cases k with
    | zero =>
      exact HomotopyGroup.map_surjective_of_isEmpty_of_exists_joined f.toContinuousMap rfl hex
    | succ m =>
      refine surjective_homotopyGroup_map_of_one f (Fin (m + 1)) ?_ x
      have hsurjSO := (HomotopyGroup.surjective_map_congr rfl rfl
          (map_one (continuousSpecialOrthogonalBlockSucc ℝ (n + 1)))).1
        ((isNConnected_specialOrthogonalBlockSucc (n + 1)).surjective (m + 1) (by omega) 1)
      have bi₂ := _root_.Matrix.specialOrthogonalGroup.bijective_homotopyGroup_toOrthogonalGroup
        (n := n + 2) (Fin (m + 1))
      have hcomp : Function.Surjective
          (HomotopyGroup.map (N := Fin (m + 1)) f.toContinuousMap (map_one f) ∘
            HomotopyGroup.map (N := Fin (m + 1))
              ⟨_root_.Matrix.specialOrthogonalGroup.toOrthogonalGroup,
                _root_.Matrix.specialOrthogonalGroup.continuous_toOrthogonalGroup⟩
              (map_one
                _root_.Matrix.specialOrthogonalGroup.toOrthogonalGroup)) := by
        rw [← homotopyGroup_toOrthogonalGroup_blockSucc_sq n (Fin (m + 1))]
        exact bi₂.2.comp hsurjSO
      exact hcomp.of_comp

end TauCeti
