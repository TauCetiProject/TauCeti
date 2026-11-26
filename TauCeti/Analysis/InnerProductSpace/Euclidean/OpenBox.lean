/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Topology.Sets.Opens

/-!
# Open coordinate boxes in Euclidean space

Open coordinate boxes `TauCeti.openBox a b` in `EuclideanSpace ℝ ι`, consisting of vectors whose
`i`-th coordinate lies in `(a i, b i)` for every `i`, are closed under binary intersections
(`TauCeti.openBox_inf_openBox`), nonempty precisely when `a i < b i` for every `i`
(`TauCeti.nonempty_openBox_iff`), and form a topological basis of open subsets of
`EuclideanSpace ℝ ι` (`TauCeti.isBasis_openBoxes`).
-/

public noncomputable section

open Set Metric

namespace TauCeti

/-- The open coordinate box `∏ i, (a i, b i)` in `EuclideanSpace ℝ ι`. -/
def openBox {ι : Type*} [Fintype ι] (a b : ι → ℝ) :
    TopologicalSpace.Opens (EuclideanSpace ℝ ι) :=
  ⟨{x | ∀ i, x i ∈ Ioo (a i) (b i)}, by
    rw [Set.ofPred_forall]
    exact isOpen_iInter_of_finite fun i ↦
      isOpen_Ioo.preimage (EuclideanSpace.proj (𝕜 := ℝ) i).continuous⟩

/-- A point lies in `openBox a b` if and only if each coordinate lies in `(a i, b i)`. -/
@[simp]
theorem mem_openBox {ι : Type*} [Fintype ι] {a b : ι → ℝ} {x : EuclideanSpace ℝ ι} :
    x ∈ openBox a b ↔ ∀ i, x i ∈ Ioo (a i) (b i) := by
  rfl

/-- The intersection of two open coordinate boxes is the box given by componentwise `max` and
`min`. -/
@[simp]
theorem openBox_inf_openBox {ι : Type*} [Fintype ι] (a₁ b₁ a₂ b₂ : ι → ℝ) :
    openBox a₁ b₁ ⊓ openBox a₂ b₂ =
      openBox (fun i ↦ max (a₁ i) (a₂ i)) (fun i ↦ min (b₁ i) (b₂ i)) := by
  refine SetLike.ext fun x ↦ ?_
  simp only [TopologicalSpace.Opens.mem_inf, mem_openBox, ← forall_and]
  exact forall_congr' fun i ↦ by rw [← mem_inter_iff, Ioo_inter_Ioo]

/-- An open coordinate box `openBox a b` is nonempty if and only if `a i < b i` for every `i`. -/
theorem nonempty_openBox_iff {ι : Type*} [Fintype ι] {a b : ι → ℝ} :
    Nonempty (openBox a b) ↔ ∀ i, a i < b i := by
  constructor
  · rintro ⟨⟨x, hx⟩⟩ i
    exact (hx i).left.trans (hx i).right
  · intro hab
    refine ⟨⟨(EuclideanSpace.equiv ι ℝ).symm (fun i ↦ (a i + b i) / 2), fun i ↦ ?_⟩⟩
    have hi : ((EuclideanSpace.equiv ι ℝ).symm (fun j ↦ (a j + b j) / 2)) i = (a i + b i) / 2 :=
      rfl
    rw [hi]
    constructor <;> linarith [hab i]

/-- An open coordinate box `openBox a b` is empty if and only if `b i ≤ a i` for some `i`. -/
theorem isEmpty_openBox_iff {ι : Type*} [Fintype ι] {a b : ι → ℝ} :
    IsEmpty (openBox a b) ↔ ∃ i, b i ≤ a i := by
  rw [← not_nonempty_iff, nonempty_openBox_iff]
  simp only [not_forall, not_lt]

/-- The open coordinate boxes form a basis of open subsets of `EuclideanSpace ℝ ι`. -/
theorem isBasis_openBoxes (ι : Type*) [Fintype ι] :
    TopologicalSpace.Opens.IsBasis
      {U : TopologicalSpace.Opens (EuclideanSpace ℝ ι) | ∃ a b, U = openBox a b} := by
  rw [TopologicalSpace.Opens.isBasis_iff_nbhd]
  intro U x hx
  let L := EuclideanSpace.equiv ι ℝ
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp (U.isOpen.preimage L.symm.continuous) (L x) hx
  refine ⟨openBox (fun i ↦ x i - r) (fun i ↦ x i + r), ⟨_, _, rfl⟩,
    fun i ↦ ⟨sub_lt_self _ hr, lt_add_of_pos_right _ hr⟩, fun y hy ↦ ?_⟩
  have hyb : L y ∈ Metric.ball (L x) r := by
    rw [ball_pi _ hr]
    intro i _
    dsimp only
    rw [Real.ball_eq_Ioo]
    exact (mem_openBox.mp hy) i
  have hyU : L.symm (L y) ∈ (U : Set (EuclideanSpace ℝ ι)) := hball hyb
  rwa [ContinuousLinearEquiv.symm_apply_apply] at hyU

end TauCeti
