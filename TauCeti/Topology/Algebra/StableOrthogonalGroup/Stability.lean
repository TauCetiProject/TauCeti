/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Algebra.StableOrthogonalGroup
public import TauCeti.Topology.Grassmannian.StiefelFibration.Stability
public import TauCeti.Topology.Homotopy.HomotopyGroup.SequentialColimit
import TauCeti.Topology.Algebra.Matrix.UnitaryGroup
import TauCeti.Topology.Homotopy.HomotopyGroup.PathComponent

/-!
# Connectivity and homotopy-group stability for `O` and `SO`

Combining the stability theorem for the Stiefel fibrations
(`TauCeti.Matrix.SpecialOrthogonalGroup.isNConnected_fromBlocksOne`) with
`TauCeti.TopCat.isNConnected_ι_of_forall_succ`, each finite-stage inclusion `SO(n) → SO` and
`O(n) → O` (`n ≥ 1`) is `(n - 1)`-connected and induces isomorphisms `π_N(SO(n)) ≃* π_N(SO)` and
`π_N(O(n)) ≃* π_N(O)` for `1 ≤ Nat.card N` and `Nat.card N + 2 ≤ n`. Furthermore, since `SO`
embeds onto the identity path component of `O`, the inclusion `SO → O` induces isomorphisms
`π_N(SO) ≃* π_N(O)` for every nonempty `N`.

## Main results

* `TauCeti.isNConnected_specialOrthogonalBlockSucc`, `TauCeti.isNConnected_orthogonalBlockSucc`:
  step connectivity of the block inclusions `SO(n) → SO(n + 1)` and `O(n + 1) → O(n + 2)`.
* `TauCeti.StableSpecialOrthogonalGroup.isNConnected_of`,
  `TauCeti.StableOrthogonalGroup.isNConnected_of`: `SO(n) → SO` and `O(n) → O` (`n ≥ 1`) are
  `(n - 1)`-connected.
* `TauCeti.StableSpecialOrthogonalGroup.homotopyGroupMulEquivOf`,
  `TauCeti.StableOrthogonalGroup.homotopyGroupMulEquivOf`: stable homotopy group isomorphisms
  `π_N(SO(n)) ≃* π_N(SO)` and `π_N(O(n)) ≃* π_N(O)` for `1 ≤ Nat.card N` and
  `Nat.card N + 2 ≤ n`.
* `TauCeti.StableSpecialOrthogonalGroup.homotopyGroupMulEquivToStableOrthogonalGroup`:
  `π_N(SO) ≃* π_N(O)` for all nonempty `N`.
-/

public section

noncomputable section

open CategoryTheory Limits Topology Set

namespace TauCeti

section Connectivity

private instance (n : ℕ) : T1Space (orthogonalTopDiagram.obj n) := by
  change T1Space (Matrix.orthogonalGroup (Fin n) ℝ); infer_instance

private instance (n : ℕ) : T1Space (specialOrthogonalTopDiagram.obj n) := by
  change T1Space (Matrix.specialOrthogonalGroup (Fin n) ℝ); infer_instance

/-- Reindexing `Matrix.specialOrthogonalGroup m ℝ` along an equivalence `e : m ≃ n` as a
topological group isomorphism. -/
def specialOrthogonalReindexContinuousMulEquiv {m n : Type*} [Fintype m] [Fintype n]
    [DecidableEq m] [DecidableEq n] (e : m ≃ n) :
    Matrix.specialOrthogonalGroup m ℝ ≃ₜ* Matrix.specialOrthogonalGroup n ℝ :=
  let u := Matrix.unitaryReindexContinuousMulEquiv ℝ e
  { toFun A := ⟨(u ⟨A.val, A.property.1⟩ : Matrix n n ℝ),
      (u ⟨A.val, A.property.1⟩).property,
      by simp [u, (Matrix.mem_specialOrthogonalGroup_iff.1 A.property).2]⟩
    invFun B := ⟨(u.symm ⟨B.val, B.property.1⟩ : Matrix m m ℝ),
      (u.symm ⟨B.val, B.property.1⟩).property,
      by simp [u, (Matrix.mem_specialOrthogonalGroup_iff.1 B.property).2]⟩
    left_inv A := Subtype.ext <| by simp [u]
    right_inv B := Subtype.ext <| by simp [u]
    map_mul' A B := Subtype.ext <| by
      simpa using congrArg Subtype.val (map_mul u ⟨A.val, A.property.1⟩ ⟨B.val, B.property.1⟩)
    continuous_toFun := continuous_induced_rng.2 <|
      (continuous_subtypeVal.comp (map_continuous u)).comp
        (continuous_subtypeVal.subtype_mk fun A : Matrix.specialOrthogonalGroup m ℝ ↦
          A.property.1)
    continuous_invFun := continuous_induced_rng.2 <|
      (continuous_subtypeVal.comp (map_continuous u.symm)).comp
        (continuous_subtypeVal.subtype_mk fun B : Matrix.specialOrthogonalGroup n ℝ ↦
          B.property.1) }

@[simp]
theorem coe_specialOrthogonalReindexContinuousMulEquiv_apply {m n : Type*} [Fintype m] [Fintype n]
    [DecidableEq m] [DecidableEq n] (e : m ≃ n) (A : Matrix.specialOrthogonalGroup m ℝ) :
    (specialOrthogonalReindexContinuousMulEquiv e A : Matrix n n ℝ) =
      Matrix.reindex e e A.val := by
  simp [specialOrthogonalReindexContinuousMulEquiv]

private def specialOrthogonalToSub (n : ℕ) :
    Matrix.specialOrthogonalGroup (Fin n) ℝ ≃ₜ
      {A : Matrix.orthogonalGroup (Fin n) ℝ // (A : Matrix (Fin n) (Fin n) ℝ).det = 1} where
  toFun A :=
    ⟨Matrix.specialOrthogonalGroup.toOrthogonalGroup A, by
      rw [Matrix.specialOrthogonalGroup.coe_toOrthogonalGroup]
      exact (Matrix.mem_specialOrthogonalGroup_iff.1 A.property).2⟩
  invFun A := ⟨A.val.val, A.val.property, A.property⟩
  left_inv A := Subtype.ext (Matrix.specialOrthogonalGroup.coe_toOrthogonalGroup A)
  right_inv A := Subtype.ext (Subtype.ext (Matrix.specialOrthogonalGroup.coe_toOrthogonalGroup _))
  continuous_toFun := (continuous_toOrthogonalGroup n).subtype_mk _
  continuous_invFun := Continuous.subtype_mk
    (continuous_subtypeVal.comp (continuous_subtypeVal :
      Continuous fun A : {A : Matrix.orthogonalGroup (Fin n) ℝ //
        (A : Matrix (Fin n) (Fin n) ℝ).det = 1} ↦ A.val)) _

/-- **Step connectivity for `SO`**: the block inclusion `SO(n) → SO(n + 1)` is
`(n - 1)`-connected. -/
theorem isNConnected_specialOrthogonalBlockSucc (n : ℕ) :
    (continuousSpecialOrthogonalBlockSucc n).toContinuousMap.IsNConnected (n - 1) := by
  let e : Fin (n + 1) ≃ Fin (1 + n) :=
    (finSumFinEquiv.symm.trans (Equiv.sumComm (Fin n) (Fin 1))).trans finSumFinEquiv
  let φHomeo : Matrix.specialOrthogonalGroup (Fin (n + 1)) ℝ ≃ₜ
      Matrix.specialOrthogonalGroup (Fin (1 + n)) ℝ :=
    (specialOrthogonalReindexContinuousMulEquiv e).toHomeomorph
  let φ : C(Matrix.specialOrthogonalGroup (Fin (n + 1)) ℝ,
      Matrix.specialOrthogonalGroup (Fin (1 + n)) ℝ) :=
    φHomeo.toHomotopyEquiv.toFun
  have hcomp : φ.comp (continuousSpecialOrthogonalBlockSucc n).toContinuousMap =
      ⟨Matrix.SpecialOrthogonalGroup.fromBlocksOne ℝ 1 n,
        finiteOrthonormalFrame.continuous_fromBlocksOne n⟩ := by
    ext A i j
    change (specialOrthogonalReindexContinuousMulEquiv e (specialOrthogonalBlockSucc ℝ n A) :
        Matrix (Fin (1 + n)) (Fin (1 + n)) ℝ) i j =
      (Matrix.SpecialOrthogonalGroup.fromBlocksOne ℝ 1 n A :
        Matrix (Fin (1 + n)) (Fin (1 + n)) ℝ) i j
    rw [coe_specialOrthogonalReindexContinuousMulEquiv_apply]
    exact congrFun (congrFun (reindex_coe_specialOrthogonalBlockSucc_eq_fromBlocksOne ℝ n A) i) j
  have hwhe : φ.IsWeakHomotopyEquivalence :=
    φHomeo.toHomotopyEquiv.isWeakHomotopyEquivalence
  refine (ContinuousMap.IsWeakHomotopyEquivalence.isNConnected_comp_iff hwhe).1 ?_
  rw [hcomp]
  exact TauCeti.Matrix.SpecialOrthogonalGroup.isNConnected_fromBlocksOne 1 n

/-- **Stability connectivity for `SO`**: the stage inclusion `SO(n) → SO` is
`(n - 1)`-connected. -/
theorem StableSpecialOrthogonalGroup.isNConnected_of (n : ℕ) :
    (StableSpecialOrthogonalGroup.of n).toContinuousMap.IsNConnected (n - 1) := by
  have hι : (StableSpecialOrthogonalGroup.topCocone.ι.app n).hom =
      (StableSpecialOrthogonalGroup.of n).toContinuousMap :=
    ContinuousMap.ext fun _ ↦ rfl
  rw [← hι]
  refine TopCat.isNConnected_ι_of_forall_succ StableSpecialOrthogonalGroup.isColimitTopCocone
    (fun m ↦ (TopCat.isClosedEmbedding_ι_of_isColimit_of_succ
      StableSpecialOrthogonalGroup.isClosedEmbedding_topDiagram_succ
      StableSpecialOrthogonalGroup.isColimitTopCocone m).isEmbedding) n (n - 1) fun k hnk ↦ ?_
  have hconn := (isNConnected_specialOrthogonalBlockSucc k).mono (Nat.sub_le_sub_right hnk 1)
  have hfn : (specialOrthogonalTopDiagram.map (homOfLE k.le_succ)).hom =
      (continuousSpecialOrthogonalBlockSucc k).toContinuousMap :=
    ContinuousMap.ext fun A ↦ specialOrthogonalTopDiagram_map_succ k A
  rwa [hfn]

private theorem bijective_homotopyGroup_toOrthogonalGroup {n : ℕ} (N : Type*) [Nonempty N] :
    Function.Bijective (HomotopyGroup.map (N := N)
      ⟨Matrix.specialOrthogonalGroup.toOrthogonalGroup (n := Fin n) (R := ℝ),
        continuous_toOrthogonalGroup n⟩
      (map_one Matrix.specialOrthogonalGroup.toOrthogonalGroup)) := by
  let S : Set (Matrix.orthogonalGroup (Fin n) ℝ) :=
    {A | (A : Matrix (Fin n) (Fin n) ℝ).det = 1}
  have hS : pathComponent (1 : Matrix.orthogonalGroup (Fin n) ℝ) ⊆ S := fun A hA ↦ by
    have hdet := (TauCeti.Matrix.joined_orthogonalGroup_iff_det_eq.1 hA).symm
    simpa [S] using hdet
  have h1S : (1 : Matrix.orthogonalGroup (Fin n) ℝ) ∈ S := by simp [S]
  have hsub : Function.Bijective (HomotopyGroup.map (N := N)
      ⟨Subtype.val, continuous_subtypeVal⟩
      (rfl : ((⟨1, h1S⟩ : S) : Matrix.orthogonalGroup (Fin n) ℝ) = 1)) :=
    HomotopyGroup.bijective_map_subtypeVal_of_pathComponent_subset
      (x := (⟨1, h1S⟩ : S)) hS rfl
  let toSubC : C(Matrix.specialOrthogonalGroup (Fin n) ℝ, S) :=
    ⟨specialOrthogonalToSub n, (specialOrthogonalToSub n).continuous⟩
  have hcomp :
      (⟨Subtype.val, continuous_subtypeVal⟩ : C(S, _)).comp toSubC =
      ⟨Matrix.specialOrthogonalGroup.toOrthogonalGroup (n := Fin n) (R := ℝ),
        continuous_toOrthogonalGroup n⟩ :=
    ContinuousMap.ext fun _ ↦ rfl
  have h1 : toSubC 1 = (⟨1, h1S⟩ : S) :=
    Subtype.ext (map_one Matrix.specialOrthogonalGroup.toOrthogonalGroup)
  have he0 : Function.Bijective (HomotopyGroup.map (N := N) toSubC rfl) :=
    (HomotopyGroup.homeomorphEquiv (N := N) (specialOrthogonalToSub n) 1).bijective
  have he : Function.Bijective (HomotopyGroup.map (N := N) toSubC h1) :=
    (HomotopyGroup.bijective_map_congr (f₁ := toSubC) (f₂ := toSubC) rfl rfl h1).1 he0
  have hbij := hsub.comp he
  rw [HomotopyGroup.map_comp_map_of_comp_eq hcomp
    (rfl : ((⟨1, h1S⟩ : S) : Matrix.orthogonalGroup (Fin n) ℝ) = 1) h1
    (map_one Matrix.specialOrthogonalGroup.toOrthogonalGroup)] at hbij
  exact hbij

/-- **Step connectivity for `O`**: for `n ≥ 1`, the block inclusion `O(n) → O(n + 1)` is
`(n - 1)`-connected. Equivalently, `O(n + 1) → O(n + 2)` is `n`-connected for every `n`. -/
theorem isNConnected_orthogonalBlockSucc (n : ℕ) :
    (continuousOrthogonalBlockSucc (n + 1)).toContinuousMap.IsNConnected n := by
  let f : C(Matrix.orthogonalGroup (Fin (n + 1)) ℝ, Matrix.orthogonalGroup (Fin (n + 2)) ℝ) :=
    (continuousOrthogonalBlockSucc (n + 1)).toContinuousMap
  have hf1 : f 1 = 1 := map_one (continuousOrthogonalBlockSucc (n + 1))
  let fSO :
      C(Matrix.specialOrthogonalGroup (Fin (n + 1)) ℝ,
        Matrix.specialOrthogonalGroup (Fin (n + 2)) ℝ) :=
    (continuousSpecialOrthogonalBlockSucc (n + 1)).toContinuousMap
  have hfSO1 : fSO 1 = 1 := map_one (continuousSpecialOrthogonalBlockSucc (n + 1))
  let i₁ : C(Matrix.specialOrthogonalGroup (Fin (n + 1)) ℝ,
      Matrix.orthogonalGroup (Fin (n + 1)) ℝ) :=
    ⟨Matrix.specialOrthogonalGroup.toOrthogonalGroup, continuous_toOrthogonalGroup (n + 1)⟩
  let i₂ : C(Matrix.specialOrthogonalGroup (Fin (n + 2)) ℝ,
      Matrix.orthogonalGroup (Fin (n + 2)) ℝ) :=
    ⟨Matrix.specialOrthogonalGroup.toOrthogonalGroup, continuous_toOrthogonalGroup (n + 2)⟩
  have hSO_sq (m : ℕ) :
      HomotopyGroup.map (N := Fin (m + 1)) i₂
          (map_one Matrix.specialOrthogonalGroup.toOrthogonalGroup) ∘
        HomotopyGroup.map (N := Fin (m + 1)) fSO hfSO1 =
      HomotopyGroup.map (N := Fin (m + 1)) f hf1 ∘
        HomotopyGroup.map (N := Fin (m + 1)) i₁
          (map_one Matrix.specialOrthogonalGroup.toOrthogonalGroup) := by
    have hcomp : i₂.comp fSO = f.comp i₁ := by
      ext A i j
      exact congrFun (congrFun (congrArg Subtype.val
        (toOrthogonalGroup_specialOrthogonalBlockSucc ℝ (n + 1) A)) i) j
    exact (HomotopyGroup.map_comp_map i₂ _ fSO hfSO1).trans
      (HomotopyGroup.map_comp_map_of_comp_eq hcomp.symm hf1
        (map_one Matrix.specialOrthogonalGroup.toOrthogonalGroup) _).symm
  let mulX (x : Matrix.orthogonalGroup (Fin (n + 1)) ℝ) :
      C(Matrix.orthogonalGroup (Fin (n + 1)) ℝ, Matrix.orthogonalGroup (Fin (n + 1)) ℝ) :=
    ⟨Homeomorph.mulLeft x, (Homeomorph.mulLeft x).continuous⟩
  let mulFx (x : Matrix.orthogonalGroup (Fin (n + 1)) ℝ) :
      C(Matrix.orthogonalGroup (Fin (n + 2)) ℝ, Matrix.orthogonalGroup (Fin (n + 2)) ℝ) :=
    ⟨Homeomorph.mulLeft (f x), (Homeomorph.mulLeft (f x)).continuous⟩
  have hmul_sq (m : ℕ) (x : Matrix.orthogonalGroup (Fin (n + 1)) ℝ)
      (hf1fx : mulFx x 1 = f x) :
      HomotopyGroup.map (N := Fin (m + 1)) (mulFx x) hf1fx ∘
        HomotopyGroup.map (N := Fin (m + 1)) f hf1 =
      HomotopyGroup.map (N := Fin (m + 1)) f rfl ∘
        HomotopyGroup.map (N := Fin (m + 1)) (mulX x) (mul_one x) := by
    have hcomm : (mulFx x).comp f = f.comp (mulX x) := by
      ext y i j
      change (continuousOrthogonalBlockSucc (n + 1) x *
        continuousOrthogonalBlockSucc (n + 1) y : Matrix _ _ ℝ) i j =
        (continuousOrthogonalBlockSucc (n + 1) (x * y) : Matrix _ _ ℝ) i j
      rw [← map_mul (continuousOrthogonalBlockSucc (n + 1))]
    exact (HomotopyGroup.map_comp_map (mulFx x) hf1fx f hf1).trans
      (HomotopyGroup.map_comp_map_of_comp_eq hcomm.symm rfl (mul_one x) _).symm
  have hex : ∀ y : Matrix.orthogonalGroup (Fin (n + 2)) ℝ, ∃ x, Joined (f x) y := by
    intro y
    rcases det_eq_one_or_neg_one_of_mem_orthogonalGroup y.property with hy | hy
    · refine ⟨1, TauCeti.Matrix.joined_orthogonalGroup_iff_det_eq.2 ?_⟩
      simp [f, hy]
    · refine ⟨orthogonalDiagonalReflection ℝ 0,
        TauCeti.Matrix.joined_orthogonalGroup_iff_det_eq.2 ?_⟩
      change ((continuousOrthogonalBlockSucc (n + 1)
          (orthogonalDiagonalReflection ℝ 0) :
          Matrix (Fin (n + 2)) (Fin (n + 2)) ℝ)).det =
        (y : Matrix (Fin (n + 2)) (Fin (n + 2)) ℝ).det
      rw [continuousOrthogonalBlockSucc_apply, coe_orthogonalBlockSucc, Matrix.det_blockSucc,
        det_orthogonalDiagonalReflection, hy]
  refine ⟨hex, fun k hk x ↦ ?_, fun k hk x ↦ ?_⟩
  · cases k with
    | zero =>
      refine HomotopyGroup.map_injective_of_isEmpty_of_joined f rfl fun a b hab ↦ ?_
      rw [TauCeti.Matrix.joined_orthogonalGroup_iff_det_eq] at hab ⊢
      simpa [f] using hab
    | succ m =>
      have hinjSO : Function.Injective (HomotopyGroup.map (N := Fin (m + 1)) fSO hfSO1) :=
        (HomotopyGroup.injective_map_congr rfl rfl hfSO1).1
          ((isNConnected_specialOrthogonalBlockSucc (n + 1)).injective (m + 1)
            (by omega) 1)
      have bi₁ := bijective_homotopyGroup_toOrthogonalGroup (n := n + 1) (Fin (m + 1))
      have bi₂ := bijective_homotopyGroup_toOrthogonalGroup (n := n + 2) (Fin (m + 1))
      have hinj1 : Function.Injective (HomotopyGroup.map (N := Fin (m + 1)) f hf1) := by
        intro a b hab
        obtain ⟨a', rfl⟩ := bi₁.2 a
        obtain ⟨b', rfl⟩ := bi₁.2 b
        have hcomp :
            (HomotopyGroup.map (N := Fin (m + 1)) f hf1 ∘
              HomotopyGroup.map (N := Fin (m + 1)) i₁
                (map_one Matrix.specialOrthogonalGroup.toOrthogonalGroup)) a' =
            (HomotopyGroup.map (N := Fin (m + 1)) f hf1 ∘
              HomotopyGroup.map (N := Fin (m + 1)) i₁
                (map_one Matrix.specialOrthogonalGroup.toOrthogonalGroup)) b' := hab
        rw [← hSO_sq m] at hcomp
        exact congrArg (HomotopyGroup.map (N := Fin (m + 1)) i₁ _) (hinjSO (bi₂.1 hcomp))
      have hx0 : Function.Bijective (HomotopyGroup.map (N := Fin (m + 1)) (mulX x) rfl) :=
        (HomotopyGroup.homeomorphEquiv (N := Fin (m + 1)) (Homeomorph.mulLeft x) 1).bijective
      have hx : Function.Bijective
          (HomotopyGroup.map (N := Fin (m + 1)) (mulX x) (mul_one x)) :=
        (HomotopyGroup.bijective_map_congr (f₁ := mulX x) (f₂ := mulX x) rfl rfl (mul_one x)).1
          hx0
      have hf1fx : mulFx x 1 = f x := mul_one (f x)
      have hfx0 : Function.Bijective (HomotopyGroup.map (N := Fin (m + 1)) (mulFx x) rfl) :=
        (HomotopyGroup.homeomorphEquiv (N := Fin (m + 1)) (Homeomorph.mulLeft (f x)) 1).bijective
      have hfx : Function.Bijective (HomotopyGroup.map (N := Fin (m + 1)) (mulFx x) hf1fx) :=
        (HomotopyGroup.bijective_map_congr (f₁ := mulFx x) (f₂ := mulFx x) rfl rfl hf1fx).1 hfx0
      intro a b hab
      obtain ⟨a', rfl⟩ := hx.2 a
      obtain ⟨b', rfl⟩ := hx.2 b
      have hcomp :
          (HomotopyGroup.map (N := Fin (m + 1)) f rfl ∘
            HomotopyGroup.map (N := Fin (m + 1)) (mulX x) (mul_one x)) a' =
          (HomotopyGroup.map (N := Fin (m + 1)) f rfl ∘
            HomotopyGroup.map (N := Fin (m + 1)) (mulX x) (mul_one x)) b' := hab
      rw [← hmul_sq m x hf1fx] at hcomp
      exact congrArg (HomotopyGroup.map (N := Fin (m + 1)) (mulX x) (mul_one x))
        (hinj1 (hfx.1 hcomp))
  · cases k with
    | zero =>
      exact HomotopyGroup.map_surjective_of_isEmpty_of_exists_joined f rfl hex
    | succ m =>
      have hsurjSO : Function.Surjective (HomotopyGroup.map (N := Fin (m + 1)) fSO hfSO1) :=
        (HomotopyGroup.surjective_map_congr rfl rfl hfSO1).1
          ((isNConnected_specialOrthogonalBlockSucc (n + 1)).surjective (m + 1)
            (by omega) 1)
      have bi₂ := bijective_homotopyGroup_toOrthogonalGroup (n := n + 2) (Fin (m + 1))
      have hsurj1 : Function.Surjective (HomotopyGroup.map (N := Fin (m + 1)) f hf1) := by
        have hcomp : Function.Surjective
            (HomotopyGroup.map (N := Fin (m + 1)) f hf1 ∘
              HomotopyGroup.map (N := Fin (m + 1)) i₁
                (map_one Matrix.specialOrthogonalGroup.toOrthogonalGroup)) := by
          rw [← hSO_sq m]
          exact bi₂.2.comp hsurjSO
        exact hcomp.of_comp
      have hf1fx : mulFx x 1 = f x := mul_one (f x)
      have hfx0 : Function.Bijective (HomotopyGroup.map (N := Fin (m + 1)) (mulFx x) rfl) :=
        (HomotopyGroup.homeomorphEquiv (N := Fin (m + 1)) (Homeomorph.mulLeft (f x)) 1).bijective
      have hfx : Function.Bijective (HomotopyGroup.map (N := Fin (m + 1)) (mulFx x) hf1fx) :=
        (HomotopyGroup.bijective_map_congr (f₁ := mulFx x) (f₂ := mulFx x) rfl rfl hf1fx).1 hfx0
      have hcomp : Function.Surjective
          (HomotopyGroup.map (N := Fin (m + 1)) f rfl ∘
            HomotopyGroup.map (N := Fin (m + 1)) (mulX x) (mul_one x)) := by
        rw [← hmul_sq m x hf1fx]
        exact hfx.2.comp hsurj1
      exact hcomp.of_comp

/-- **Stability connectivity for `O`**: for `n ≥ 1`, the stage inclusion `O(n) → O` is
`(n - 1)`-connected. -/
theorem StableOrthogonalGroup.isNConnected_of (n : ℕ) (hn : 1 ≤ n) :
    (StableOrthogonalGroup.of n).toContinuousMap.IsNConnected (n - 1) := by
  have hι : (StableOrthogonalGroup.topCocone.ι.app n).hom =
      (StableOrthogonalGroup.of n).toContinuousMap :=
    ContinuousMap.ext fun _ ↦ rfl
  rw [← hι]
  refine TopCat.isNConnected_ι_of_forall_succ StableOrthogonalGroup.isColimitTopCocone
    (fun m ↦ (TopCat.isClosedEmbedding_ι_of_isColimit_of_succ
      StableOrthogonalGroup.isClosedEmbedding_topDiagram_succ
      StableOrthogonalGroup.isColimitTopCocone m).isEmbedding) n (n - 1) fun k hnk ↦ ?_
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
  have hconn := (isNConnected_orthogonalBlockSucc m).mono (by omega : n - 1 ≤ m)
  have hfn : (orthogonalTopDiagram.map (homOfLE (m + 1).le_succ)).hom =
      (continuousOrthogonalBlockSucc (m + 1)).toContinuousMap :=
    ContinuousMap.ext fun A ↦ orthogonalTopDiagram_map_succ (m + 1) A
  rwa [hfn]

/-- **Homotopy group stability for `SO`**: for a finite nonempty cube-index type `N` with
`Nat.card N + 2 ≤ n`, the stage inclusion `SO(n) → SO` induces a group isomorphism
`π_N(SO(n), x) ≃* π_N(SO, of n x)`. -/
@[expose]
def StableSpecialOrthogonalGroup.homotopyGroupMulEquivOf {N : Type*} [Finite N] [DecidableEq N]
    [Nonempty N] {n : ℕ} (hn : Nat.card N + 2 ≤ n)
    (x : Matrix.specialOrthogonalGroup (Fin n) ℝ) :
    HomotopyGroup N (Matrix.specialOrthogonalGroup (Fin n) ℝ) x ≃*
      HomotopyGroup N StableSpecialOrthogonalGroup (StableSpecialOrthogonalGroup.of n x) :=
  let hc := StableSpecialOrthogonalGroup.isNConnected_of n
  MulEquiv.ofBijective
    (HomotopyGroup.mapHom (N := N) (StableSpecialOrthogonalGroup.of n).toContinuousMap rfl)
    ⟨hc.map_injective N (by omega) x, hc.map_surjective N (by omega) x⟩

@[simp]
theorem StableSpecialOrthogonalGroup.homotopyGroupMulEquivOf_apply {N : Type*} [Finite N]
    [DecidableEq N] [Nonempty N] {n : ℕ} (hn : Nat.card N + 2 ≤ n)
    (x : Matrix.specialOrthogonalGroup (Fin n) ℝ)
    (a : HomotopyGroup N (Matrix.specialOrthogonalGroup (Fin n) ℝ) x) :
    StableSpecialOrthogonalGroup.homotopyGroupMulEquivOf hn x a =
      HomotopyGroup.map (StableSpecialOrthogonalGroup.of n).toContinuousMap rfl a :=
  rfl

/-- **Homotopy group stability for `O`**: for a finite nonempty cube-index type `N` with
`Nat.card N + 2 ≤ n`, the stage inclusion `O(n) → O` induces a group isomorphism
`π_N(O(n), x) ≃* π_N(O, of n x)`. -/
@[expose]
def StableOrthogonalGroup.homotopyGroupMulEquivOf {N : Type*} [Finite N] [DecidableEq N]
    [Nonempty N] {n : ℕ} (hn : Nat.card N + 2 ≤ n)
    (x : Matrix.orthogonalGroup (Fin n) ℝ) :
    HomotopyGroup N (Matrix.orthogonalGroup (Fin n) ℝ) x ≃*
      HomotopyGroup N StableOrthogonalGroup (StableOrthogonalGroup.of n x) :=
  let hc := StableOrthogonalGroup.isNConnected_of n (by omega)
  MulEquiv.ofBijective
    (HomotopyGroup.mapHom (N := N) (StableOrthogonalGroup.of n).toContinuousMap rfl)
    ⟨hc.map_injective N (by omega) x, hc.map_surjective N (by omega) x⟩

@[simp]
theorem StableOrthogonalGroup.homotopyGroupMulEquivOf_apply {N : Type*} [Finite N]
    [DecidableEq N] [Nonempty N] {n : ℕ} (hn : Nat.card N + 2 ≤ n)
    (x : Matrix.orthogonalGroup (Fin n) ℝ)
    (a : HomotopyGroup N (Matrix.orthogonalGroup (Fin n) ℝ) x) :
    StableOrthogonalGroup.homotopyGroupMulEquivOf hn x a =
      HomotopyGroup.map (StableOrthogonalGroup.of n).toContinuousMap rfl a :=
  rfl

/-- **Positive-dimensional homotopy groups of `SO` and `O` coincide**: since `SO` embeds onto the
identity path component of `O`, the inclusion `SO → O` induces a group isomorphism
`π_N(SO, x) ≃* π_N(O, toStableOrthogonalGroup x)` for every nonempty cube-index type `N`. -/
@[expose]
def StableSpecialOrthogonalGroup.homotopyGroupMulEquivToStableOrthogonalGroup
    {N : Type*} [DecidableEq N] [Nonempty N] (x : StableSpecialOrthogonalGroup) :
    HomotopyGroup N StableSpecialOrthogonalGroup x ≃*
      HomotopyGroup N StableOrthogonalGroup
        (StableSpecialOrthogonalGroup.toStableOrthogonalGroup x) :=
  let S := Set.range StableSpecialOrthogonalGroup.toStableOrthogonalGroup
  let e : StableSpecialOrthogonalGroup ≃ₜ S :=
    { toFun a := ⟨StableSpecialOrthogonalGroup.toStableOrthogonalGroup a, a, rfl⟩
      invFun b := Classical.choose b.property
      left_inv a := StableSpecialOrthogonalGroup.toStableOrthogonalGroup_injective
        (Classical.choose_spec (⟨a, rfl⟩ :
          StableSpecialOrthogonalGroup.toStableOrthogonalGroup a ∈ S))
      right_inv b := Subtype.ext (Classical.choose_spec b.property)
      continuous_toFun :=
        StableSpecialOrthogonalGroup.toStableOrthogonalGroup.continuous.subtype_mk _
      continuous_invFun := by
        rw [StableSpecialOrthogonalGroup.isClosedEmbedding_toStableOrthogonalGroup
          |>.isEmbedding.continuous_iff]
        refine continuous_subtypeVal.congr fun b ↦ ?_
        exact (Classical.choose_spec b.property).symm }
  let hS : pathComponent (StableSpecialOrthogonalGroup.toStableOrthogonalGroup x) ⊆ S :=
    fun y hy ↦ by
      rw [mem_pathComponent_iff, StableOrthogonalGroup.joined_iff_det_eq,
        StableSpecialOrthogonalGroup.det_toStableOrthogonalGroup] at hy
      dsimp only [S]
      rw [StableSpecialOrthogonalGroup.range_toStableOrthogonalGroup]
      exact hy.symm
  let hbij : Function.Bijective (HomotopyGroup.map (N := N)
      StableSpecialOrthogonalGroup.toStableOrthogonalGroup.toContinuousMap rfl) := by
    have hcomp : (⟨Subtype.val, continuous_subtypeVal⟩ : C(S, StableOrthogonalGroup)).comp
        ⟨e, e.continuous⟩ =
        StableSpecialOrthogonalGroup.toStableOrthogonalGroup.toContinuousMap :=
      ContinuousMap.ext fun _ ↦ rfl
    have he : Function.Bijective (HomotopyGroup.map (N := N) (x := x)
        (⟨e, e.continuous⟩ : C(StableSpecialOrthogonalGroup, S)) rfl) :=
      (HomotopyGroup.homeomorphMulEquiv (N := N) e x).bijective
    have hsub := HomotopyGroup.bijective_map_subtypeVal_of_pathComponent_subset
      (N := N) (x := e x) hS rfl
    have h := hsub.comp he
    rw [HomotopyGroup.map_comp_map_of_comp_eq hcomp
      (rfl : ((e x : S) : StableOrthogonalGroup) =
        StableSpecialOrthogonalGroup.toStableOrthogonalGroup x)
      (rfl : e x = e x) rfl] at h
    exact h
  MulEquiv.ofBijective
    (HomotopyGroup.mapHom (N := N)
      StableSpecialOrthogonalGroup.toStableOrthogonalGroup.toContinuousMap rfl)
    hbij

@[simp]
theorem StableSpecialOrthogonalGroup.homotopyGroupMulEquivToStableOrthogonalGroup_apply
    {N : Type*} [DecidableEq N] [Nonempty N] (x : StableSpecialOrthogonalGroup)
    (a : HomotopyGroup N StableSpecialOrthogonalGroup x) :
    StableSpecialOrthogonalGroup.homotopyGroupMulEquivToStableOrthogonalGroup x a =
      HomotopyGroup.map
        StableSpecialOrthogonalGroup.toStableOrthogonalGroup.toContinuousMap rfl a :=
  rfl

end Connectivity

end TauCeti
