/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.Euclidean.Sparsity

/-!
# The restricted nullspace property and exact recovery by basis pursuit

A design `X : Matrix m ι ℝ` acts on `EuclideanSpace ℝ ι` by `Matrix.toEuclideanLin X`. Basis
pursuit estimates a vector `β` from its noiseless measurements `y = Xβ` by minimizing the `ℓ¹`
norm `‖b‖₁` over all `b` with `Xb = y`. The restricted nullspace property of `X` with respect to
a set `S` of coordinates says that the kernel of `X` meets the cone
`C_1(S) = {δ | ‖δ_{Sᶜ}‖₁ ≤ ‖δ_S‖₁}` only at `0`, where `‖δ_S‖₁` is the restricted `ℓ¹` norm
`EuclideanSpace.restrictedL1Norm δ S`. It is exactly the condition under which basis pursuit
recovers every vector supported in `S`.

## Main definitions

* `Matrix.HasRestrictedNullspace X S`: `Xδ = 0` and `‖δ_{Sᶜ}‖₁ ≤ ‖δ_S‖₁` imply `δ = 0`.
* `Matrix.IsBasisPursuitSolution X y b`: `Xb = y` and `b` minimizes `‖·‖₁` on `{b' | Xb' = y}`.

## Main results

* `Matrix.hasRestrictedNullspace_iff_basisPursuit`: `X` has the restricted nullspace property
  with respect to `S` iff every `β` supported in `S` is the unique basis pursuit solution for
  `y = Xβ` (Wainwright, Thm 7.8).
* `Matrix.HasRestrictedNullspace.isBasisPursuitSolution`,
  `Matrix.HasRestrictedNullspace.eq_of_isBasisPursuitSolution`: the two halves of exact recovery.
* `Matrix.hasRestrictedNullspace_empty`, `Matrix.HasRestrictedNullspace.anti`: the property holds
  for `S = ∅` and passes to subsets of `S`.

## References

* M. J. Wainwright, *High-Dimensional Statistics: A Non-Asymptotic Viewpoint*, Cambridge
  University Press, 2019, Def 7.7 and Thm 7.8 (p. 202).
* S. Foucart and H. Rauhut, *A Mathematical Introduction to Compressive Sensing*, Birkhäuser,
  2013, Def 4.1 and Thm 4.5 (p. 79).

The results are adapted from the lean-CKSD project (<https://github.com/bjbraams/lean-CKSD>),
file `CKSD/Nonparametric/SparseRecovery/Basic.lean` (`HasNullspaceProperty`,
`hasNullspaceProperty_iff`), restated for the non-strict cone and for basis pursuit solutions.
-/

public section

noncomputable section

open Finset EuclideanSpace

namespace Matrix

variable {m ι : Type*} [Fintype ι] [DecidableEq ι]

/-! ### The restricted nullspace property -/

/-- The restricted nullspace property of `X` with respect to `S`: the kernel of `X` meets the cone
`C_1(S) = {δ | ‖δ_{Sᶜ}‖₁ ≤ ‖δ_S‖₁}` only at `0`. -/
def HasRestrictedNullspace (X : Matrix m ι ℝ) (S : Finset ι) : Prop :=
  ∀ δ : EuclideanSpace ℝ ι, toEuclideanLin X δ = 0 →
    δ.restrictedL1Norm Sᶜ ≤ δ.restrictedL1Norm S → δ = 0

/-- The restricted nullspace property says that `Xδ = 0` and `‖δ_{Sᶜ}‖₁ ≤ ‖δ_S‖₁` imply
`δ = 0`. -/
theorem hasRestrictedNullspace_def (X : Matrix m ι ℝ) (S : Finset ι) :
    X.HasRestrictedNullspace S ↔ ∀ δ : EuclideanSpace ℝ ι, toEuclideanLin X δ = 0 →
      δ.restrictedL1Norm Sᶜ ≤ δ.restrictedL1Norm S → δ = 0 :=
  Iff.rfl

/-- Every matrix has the restricted nullspace property with respect to `∅`, since the cone
`C_1(∅)` is `{0}`. -/
@[simp]
theorem hasRestrictedNullspace_empty (X : Matrix m ι ℝ) : X.HasRestrictedNullspace ∅ := by
  intro δ _ hδ
  rw [compl_empty, restrictedL1Norm_empty] at hδ
  have h0 := restrictedL1Norm_eq_zero_iff.1 (le_antisymm hδ (δ.restrictedL1Norm_nonneg _))
  ext j
  exact h0 j (mem_univ j)

/-- The restricted nullspace property with respect to `S` passes to every subset of `S`, since
the cone `C_1(T)` is contained in `C_1(S)` for `T ⊆ S`. -/
theorem HasRestrictedNullspace.anti {X : Matrix m ι ℝ} {S T : Finset ι}
    (h : X.HasRestrictedNullspace S) (hTS : T ⊆ S) : X.HasRestrictedNullspace T :=
  fun δ hXδ hδ ↦ h δ hXδ <| calc
    δ.restrictedL1Norm Sᶜ ≤ δ.restrictedL1Norm Tᶜ :=
        δ.restrictedL1Norm_mono (compl_subset_compl.2 hTS)
    _ ≤ δ.restrictedL1Norm T := hδ
    _ ≤ δ.restrictedL1Norm S := δ.restrictedL1Norm_mono hTS

/-! ### Basis pursuit -/

/-- Basis pursuit: `b` satisfies `Xb = y` and minimizes the `ℓ¹` norm on the affine set
`{b' | Xb' = y}`. Mathlib's `IsMinOn f s b` does not ask for `b ∈ s`, so feasibility is a
separate conjunct. -/
def IsBasisPursuitSolution (X : Matrix m ι ℝ) (y : EuclideanSpace ℝ m)
    (b : EuclideanSpace ℝ ι) : Prop :=
  toEuclideanLin X b = y ∧
    IsMinOn (fun b' : EuclideanSpace ℝ ι ↦ b'.restrictedL1Norm univ)
      {b' | toEuclideanLin X b' = y} b

/-- A basis pursuit solution is a feasible point minimizing the `ℓ¹` norm on the feasible set. -/
theorem isBasisPursuitSolution_def (X : Matrix m ι ℝ) (y : EuclideanSpace ℝ m)
    (b : EuclideanSpace ℝ ι) :
    X.IsBasisPursuitSolution y b ↔ toEuclideanLin X b = y ∧
      IsMinOn (fun b' : EuclideanSpace ℝ ι ↦ b'.restrictedL1Norm univ)
        {b' | toEuclideanLin X b' = y} b :=
  Iff.rfl

/-- `b` is a basis pursuit solution for `y` iff `Xb = y` and `‖b‖₁ ≤ ‖b'‖₁` whenever
`Xb' = y`. -/
theorem isBasisPursuitSolution_iff {X : Matrix m ι ℝ} {y : EuclideanSpace ℝ m}
    {b : EuclideanSpace ℝ ι} :
    X.IsBasisPursuitSolution y b ↔ toEuclideanLin X b = y ∧
      ∀ b' : EuclideanSpace ℝ ι, toEuclideanLin X b' = y →
        b.restrictedL1Norm univ ≤ b'.restrictedL1Norm univ :=
  and_congr_right' isMinOn_iff

/-- A basis pursuit solution has `ℓ¹` norm at most that of every feasible point. -/
theorem IsBasisPursuitSolution.restrictedL1Norm_le {X : Matrix m ι ℝ} {y : EuclideanSpace ℝ m}
    {b b' : EuclideanSpace ℝ ι} (hb : X.IsBasisPursuitSolution y b)
    (hb' : toEuclideanLin X b' = y) : b.restrictedL1Norm univ ≤ b'.restrictedL1Norm univ :=
  (isBasisPursuitSolution_iff.1 hb).2 b' hb'

/-! ### Exact recovery -/

/-- Under the restricted nullspace property with respect to `S`, a vector `b` with the same
measurements as a vector `β` supported in `S` and with `‖b‖₁ ≤ ‖β‖₁` equals `β`. -/
theorem HasRestrictedNullspace.eq_of_restrictedL1Norm_le {X : Matrix m ι ℝ} {S : Finset ι}
    (h : X.HasRestrictedNullspace S) {β b : EuclideanSpace ℝ ι} (hβ : ∀ j ∉ S, β j = 0)
    (hXb : toEuclideanLin X b = toEuclideanLin X β)
    (hb : b.restrictedL1Norm univ ≤ β.restrictedL1Norm univ) : b = β := by
  have hcone := restrictedL1Norm_univ_add_restrictedL1Norm_compl_le hβ (b - β)
  rw [add_sub_cancel] at hcone
  exact sub_eq_zero.1 (h (b - β) (by rw [map_sub, hXb, sub_self]) (by linarith))

/-- Under the restricted nullspace property with respect to `S`, every vector supported in `S` is
a basis pursuit solution for its own measurements. -/
theorem HasRestrictedNullspace.isBasisPursuitSolution {X : Matrix m ι ℝ} {S : Finset ι}
    (h : X.HasRestrictedNullspace S) {β : EuclideanSpace ℝ ι} (hβ : ∀ j ∉ S, β j = 0) :
    X.IsBasisPursuitSolution (toEuclideanLin X β) β := by
  refine isBasisPursuitSolution_iff.2 ⟨rfl, fun b hb ↦ ?_⟩
  by_contra hlt
  have hbβ := h.eq_of_restrictedL1Norm_le hβ hb (not_le.1 hlt).le
  rw [hbβ] at hlt
  exact hlt le_rfl

/-- Under the restricted nullspace property with respect to `S`, the only basis pursuit solution
for the measurements of a vector `β` supported in `S` is `β` itself. -/
theorem HasRestrictedNullspace.eq_of_isBasisPursuitSolution {X : Matrix m ι ℝ} {S : Finset ι}
    (h : X.HasRestrictedNullspace S) {β b : EuclideanSpace ℝ ι} (hβ : ∀ j ∉ S, β j = 0)
    (hb : X.IsBasisPursuitSolution (toEuclideanLin X β) b) : b = β :=
  h.eq_of_restrictedL1Norm_le hβ hb.1 (hb.restrictedL1Norm_le rfl)

/-- **Exact recovery by basis pursuit** (Wainwright, Thm 7.8): `X` has the restricted nullspace
property with respect to `S` iff, for every `β` supported in `S`, `β` is the unique basis pursuit
solution for its measurements `y = Xβ`. -/
theorem hasRestrictedNullspace_iff_basisPursuit (X : Matrix m ι ℝ) (S : Finset ι) :
    X.HasRestrictedNullspace S ↔
      ∀ β : EuclideanSpace ℝ ι, (∀ j ∉ S, β j = 0) →
        ∀ b, X.IsBasisPursuitSolution (toEuclideanLin X β) b ↔ b = β := by
  refine ⟨fun h β hβ b ↦ ⟨h.eq_of_isBasisPursuitSolution hβ, ?_⟩, fun h δ hXδ hδ ↦ ?_⟩
  · rintro rfl
    exact h.isBasisPursuitSolution hβ
  -- Split `δ` as `β - b` with `β = δ_S` supported in `S` and `b = -δ_{Sᶜ}`.
  set β : EuclideanSpace ℝ ι := WithLp.toLp 2 ((S : Set ι).indicator (WithLp.ofLp δ))
  set b : EuclideanSpace ℝ ι :=
    -WithLp.toLp 2 (((Sᶜ : Finset ι) : Set ι).indicator (WithLp.ofLp δ))
  have hβ : ∀ j ∉ S, β j = 0 := fun j hj ↦ by simp [β, hj]
  have hδβb : δ = β - b := by
    ext j
    simp only [β, b, sub_neg_eq_add, PiLp.add_apply, coe_compl]
    exact (congrFun (Set.indicator_self_add_compl (S : Set ι) (WithLp.ofLp δ)) j).symm
  have hXb : toEuclideanLin X b = toEuclideanLin X β := by
    refine (sub_eq_zero.1 ?_).symm
    rw [← map_sub, ← hδβb, hXδ]
  have hβsol : X.IsBasisPursuitSolution (toEuclideanLin X β) β := (h β hβ β).2 rfl
  have hbsol : X.IsBasisPursuitSolution (toEuclideanLin X β) b := by
    refine isBasisPursuitSolution_iff.2
      ⟨hXb, fun b' hb' ↦ le_trans ?_ (hβsol.restrictedL1Norm_le hb')⟩
    rw [restrictedL1Norm_neg, restrictedL1Norm_toLp_indicator, restrictedL1Norm_toLp_indicator,
      univ_inter, univ_inter]
    exact hδ
  rw [hδβb, (h β hβ b).1 hbsol, sub_self]

end Matrix
