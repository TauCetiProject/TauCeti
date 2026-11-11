/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.LinearAlgebra.GradedCorrespondence.Basic

/-!
# Terminal resolutions for graph correspondences

An incoming coefficient of negative normal degree approaches a face from the
negative side; positive normal degree approaches from the positive side. At the
face, negative inputs have chamber values `(a, e a)`, positive inputs have values
`(e⁻¹ a, a)`, and tangent inputs have `(a, a)`. If the linear equivalence `e` fixes
tangent coefficients, these finite homogeneous sums have a unique common lift
through the graph correspondence, linear in the incoming coefficient.

The two chamber sums are constructed independently from the homogeneous inputs.
No finiteness of the grading set or basis of its pieces is needed. The input may
include all three normal signs simultaneously. This is the coefficient identity
at a terminal ordinary-wall crossing.

The two totals commute with grading-preserving coefficient maps that intertwine
the wall actions. Normal-sign branches may differ exactly when the target wall
action fixes the corresponding coefficient images. In particular, preserving the
relevant normal sign is sufficient. These maps may kill coefficients or identify
degrees; only their finite homogeneous sums are used.
The totals preserve chosen additive positive monoids when the transports used
in their respective normal-sign branches do so.

We use `GradedCorrespondence.graph` and Mathlib's internal direct-sum universal
property. The terminal-face convention is that of Gross–Hacking–Siebert,
*Theta functions on varieties with effective anti-canonical class*, §3.2
(arXiv:1601.07081v4).

## Attribution

Adapted from `Mei/LinearAlgebra/GradedCorrespondence/Terminal.lean` in
[yuma-mizuno-lean/Mei](https://github.com/yuma-mizuno-lean/Mei), at commit
`3d2e9c869ee44c41ae9c7b5c6e2042898430d0ca` (Apache 2.0).
Original author credit is retained; the file uses the required Tau Ceti copyright header.
-/

public noncomputable section

namespace TauCeti.GradedCorrespondence

variable {R M ι : Type*} [Semiring R] [AddCommMonoid M] [Module R M]
  [DecidableEq ι] (ℳ : ι → Submodule R M) [DirectSum.Decomposition ℳ]
  (e : M ≃ₗ[R] M) (w : ι → ℤ)

open Classical in
/-- Negative-side values of all incoming homogeneous coefficients. Inputs from
the positive side cross by the inverse equivalence; the other inputs stay put. -/
def terminalGraphLift : Module.End R M :=
  DirectSum.homogeneousExtend ℳ (fun i => if 0 < w i then
    e.symm.toLinearMap.comp (ℳ i).subtype else (ℳ i).subtype)

open Classical in
/-- Positive-side values of all incoming homogeneous coefficients. Inputs from
the negative side cross by the equivalence; the other inputs stay put. -/
def terminalGraphRight : Module.End R M :=
  DirectSum.homogeneousExtend ℳ (fun i => if w i < 0 then
    e.toLinearMap.comp (ℳ i).subtype else (ℳ i).subtype)

open Classical in
/-- On one homogeneous input the common-lift candidate is the incoming value
or its inverse transport, according to its normal degree. -/
theorem terminalGraphLift_of_mem {i : ι} {a : M} (ha : a ∈ ℳ i) :
    terminalGraphLift ℳ e w a = if 0 < w i then e.symm a else a := by
  rw [terminalGraphLift, DirectSum.homogeneousExtend_of_mem ℳ _ ha]
  split_ifs <;> rfl

open Classical in
/-- The terminal lift on a homogeneous subtype input is its inverse transport
in positive normal degree and the input itself otherwise. -/
@[simp] theorem terminalGraphLift_coe {i : ι} (a : ℳ i) :
    terminalGraphLift ℳ e w a = if 0 < w i then e.symm a else a :=
  terminalGraphLift_of_mem ℳ e w a.property

open Classical in
/-- On one homogeneous input the positive-side value is the incoming value
or its forward transport, according to its normal degree. -/
theorem terminalGraphRight_of_mem {i : ι} {a : M} (ha : a ∈ ℳ i) :
    terminalGraphRight ℳ e w a = if w i < 0 then e a else a := by
  rw [terminalGraphRight, DirectSum.homogeneousExtend_of_mem ℳ _ ha]
  split_ifs <;> rfl

open Classical in
/-- The positive-side terminal value on a homogeneous subtype input is its
forward transport in negative normal degree and the input itself otherwise. -/
@[simp] theorem terminalGraphRight_coe {i : ι} (a : ℳ i) :
    terminalGraphRight ℳ e w a = if w i < 0 then e a else a :=
  terminalGraphRight_of_mem ℳ e w a.property

open Classical in
/-- The lift candidate is the finite sum of inverse-transferred positive inputs
and unchanged nonpositive inputs, retaining their whole decorations. -/
theorem terminalGraphLift_eq_sum (a : M) :
    terminalGraphLift ℳ e w a =
      ∑ i ∈ (DirectSum.decompose ℳ a).support,
        if 0 < w i then e.symm (DirectSum.decompose ℳ a i) else
          (DirectSum.decompose ℳ a i : M) := by
  rw [terminalGraphLift, DirectSum.homogeneousExtend_eq_sum]
  apply Finset.sum_congr rfl
  intro i _
  split_ifs <;> rfl

open Classical in
/-- The positive-side total is the finite sum of forward-transferred negative
inputs and unchanged nonnegative inputs. -/
theorem terminalGraphRight_eq_sum (a : M) :
    terminalGraphRight ℳ e w a =
      ∑ i ∈ (DirectSum.decompose ℳ a).support,
        if w i < 0 then e (DirectSum.decompose ℳ a i) else
          (DirectSum.decompose ℳ a i : M) := by
  rw [terminalGraphRight, DirectSum.homogeneousExtend_eq_sum]
  apply Finset.sum_congr rfl
  intro i _
  split_ifs <;> rfl

/-- The negative-side terminal total is positive when inverse transport preserves
positivity on positive normal degrees and unchanged inputs do so on the others. -/
theorem terminalGraphLift_mem_addSubmonoid (Pos : ι → AddSubmonoid M) (P : AddSubmonoid M)
    (hcross : ∀ i (a : ℳ i), 0 < w i → (a : M) ∈ Pos i → e.symm a ∈ P)
    (hstay : ∀ i (a : ℳ i), w i ≤ 0 → (a : M) ∈ Pos i → (a : M) ∈ P)
    (a : M) (ha : ∀ i, (DirectSum.decompose ℳ a i : M) ∈ Pos i) :
    terminalGraphLift ℳ e w a ∈ P := by
  classical
  rw [terminalGraphLift_eq_sum]
  apply P.sum_mem
  intro i hi
  have hmem := ha i
  split_ifs with h
  · exact hcross i (DirectSum.decompose ℳ a i) h hmem
  · exact hstay i (DirectSum.decompose ℳ a i) (by omega) hmem

/-- The positive-side terminal total is positive when forward transport preserves
positivity on negative normal degrees and unchanged inputs do so on the others. -/
theorem terminalGraphRight_mem_addSubmonoid (Pos : ι → AddSubmonoid M) (P : AddSubmonoid M)
    (hcross : ∀ i (a : ℳ i), w i < 0 → (a : M) ∈ Pos i → e a ∈ P)
    (hstay : ∀ i (a : ℳ i), 0 ≤ w i → (a : M) ∈ Pos i → (a : M) ∈ P)
    (a : M) (ha : ∀ i, (DirectSum.decompose ℳ a i : M) ∈ Pos i) :
    terminalGraphRight ℳ e w a ∈ P := by
  classical
  rw [terminalGraphRight_eq_sum]
  apply P.sum_mem
  intro i hi
  have hmem := ha i
  split_ifs with h
  · exact hcross i (DirectSum.decompose ℳ a i) h hmem
  · exact hstay i (DirectSum.decompose ℳ a i) (by omega) hmem

section Naturality

variable {N κ : Type*} [AddCommMonoid N] [Module R N] [DecidableEq κ]
  (𝓝 : κ → Submodule R N) [DirectSum.Decomposition 𝓝]
  (e' : N ≃ₗ[R] N) (w' : κ → ℤ) (r : M →ₗ[R] N) (σ : ι → κ)

/-- Negative-side terminal totals commute with an intertwining coefficient map
exactly when the target wall action fixes the image of every homogeneous input
whose positive-normal branch changes. The fixed images need not vanish. -/
theorem terminalGraphLift_naturality_iff
    (hr : ∀ i a, a ∈ ℳ i → r a ∈ 𝓝 (σ i))
    (he : r.comp e.toLinearMap = e'.toLinearMap.comp r) :
    r.comp (terminalGraphLift ℳ e w) = (terminalGraphLift 𝓝 e' w').comp r ↔
      ∀ i (a : ℳ i), ¬ (0 < w i ↔ 0 < w' (σ i)) → e' (r a) = r a := by
  have hinv (a : M) : r (e.symm a) = e'.symm (r a) := by
    apply e'.injective
    simpa only [LinearMap.comp_apply, LinearEquiv.coe_coe,
      LinearEquiv.apply_symm_apply] using (LinearMap.congr_fun he (e.symm a)).symm
  constructor
  · intro h i a hsign
    have hv := LinearMap.congr_fun h a
    simp only [LinearMap.comp_apply, terminalGraphLift_coe,
      terminalGraphLift_of_mem 𝓝 e' w' (hr i a a.property)] at hv
    by_cases hi : 0 < w i <;> by_cases hj : 0 < w' (σ i)
    · exact (hsign (by simp [hi, hj])).elim
    · simp only [hi, hj, ite_true, ite_false, hinv] at hv
      simpa only [LinearEquiv.apply_symm_apply] using (congrArg e' hv).symm
    · simp only [hi, hj, ite_true, ite_false] at hv
      simpa only [LinearEquiv.apply_symm_apply] using congrArg e' hv
    · exact (hsign (by simp [hi, hj])).elim
  · intro hfix
    apply DirectSum.decompose_lhom_ext ℳ
    intro i
    apply LinearMap.ext
    intro a
    simp only [LinearMap.comp_apply, Submodule.subtype_apply, terminalGraphLift_coe,
      terminalGraphLift_of_mem 𝓝 e' w' (hr i a a.property)]
    by_cases hi : 0 < w i <;> by_cases hj : 0 < w' (σ i)
    · simpa only [hi, hj, ite_true] using hinv a
    · simp only [hi, hj, ite_true, ite_false]
      rw [hinv]
      apply e'.injective
      simpa only [LinearEquiv.apply_symm_apply] using
        (hfix i a (by simp [hi, hj])).symm
    · simp only [hi, hj, ite_true, ite_false]
      apply e'.injective
      simpa only [LinearEquiv.apply_symm_apply] using hfix i a (by simp [hi, hj])
    · simp only [hi, hj, ite_false]

/-- Positive-side terminal totals commute with an intertwining coefficient map
exactly when the target wall action fixes coefficient images on homogeneous
inputs whose negative-normal branch changes. -/
theorem terminalGraphRight_naturality_iff
    (hr : ∀ i a, a ∈ ℳ i → r a ∈ 𝓝 (σ i))
    (he : r.comp e.toLinearMap = e'.toLinearMap.comp r) :
    r.comp (terminalGraphRight ℳ e w) = (terminalGraphRight 𝓝 e' w').comp r ↔
      ∀ i (a : ℳ i), ¬ (w i < 0 ↔ w' (σ i) < 0) → e' (r a) = r a := by
  have hmap (a : M) : r (e a) = e' (r a) := LinearMap.congr_fun he a
  constructor
  · intro h i a hsign
    have hv := LinearMap.congr_fun h a
    simp only [LinearMap.comp_apply, terminalGraphRight_coe,
      terminalGraphRight_of_mem 𝓝 e' w' (hr i a a.property)] at hv
    by_cases hi : w i < 0 <;> by_cases hj : w' (σ i) < 0
    · exact (hsign (by simp [hi, hj])).elim
    · simpa only [hi, hj, ite_true, ite_false, hmap] using hv
    · simpa only [hi, hj, ite_true, ite_false] using hv.symm
    · exact (hsign (by simp [hi, hj])).elim
  · intro hfix
    apply DirectSum.decompose_lhom_ext ℳ
    intro i
    apply LinearMap.ext
    intro a
    simp only [LinearMap.comp_apply, Submodule.subtype_apply, terminalGraphRight_coe,
      terminalGraphRight_of_mem 𝓝 e' w' (hr i a a.property)]
    by_cases hi : w i < 0 <;> by_cases hj : w' (σ i) < 0
    · simpa only [hi, hj, ite_true] using hmap a
    · simpa only [hi, hj, ite_true, ite_false, hmap] using hfix i a (by simp [hi, hj])
    · simpa only [hi, hj, ite_true, ite_false] using (hfix i a (by simp [hi, hj])).symm
    · simp only [hi, hj, ite_false]

/-- A coefficient map intertwining the wall actions also intertwines the
negative-side terminal totals. Only positivity of normal degrees must agree;
the coefficient map and degree map may have kernels or identify degrees. -/
theorem terminalGraphLift_naturality
    (hr : ∀ i a, a ∈ ℳ i → r a ∈ 𝓝 (σ i))
    (he : r.comp e.toLinearMap = e'.toLinearMap.comp r)
    (hpos : ∀ i, 0 < w i ↔ 0 < w' (σ i)) :
    r.comp (terminalGraphLift ℳ e w) = (terminalGraphLift 𝓝 e' w').comp r := by
  apply (terminalGraphLift_naturality_iff ℳ e w 𝓝 e' w' r σ hr he).mpr
  intro i a hsign
  exact (hsign (hpos i)).elim

/-- A coefficient map intertwining the wall actions also intertwines the
positive-side terminal totals. Only negativity of normal degrees must agree;
no injectivity assumption is imposed on either map. -/
theorem terminalGraphRight_naturality
    (hr : ∀ i a, a ∈ ℳ i → r a ∈ 𝓝 (σ i))
    (he : r.comp e.toLinearMap = e'.toLinearMap.comp r)
    (hneg : ∀ i, w i < 0 ↔ w' (σ i) < 0) :
    r.comp (terminalGraphRight ℳ e w) = (terminalGraphRight 𝓝 e' w').comp r := by
  apply (terminalGraphRight_naturality_iff ℳ e w 𝓝 e' w' r σ hr he).mpr
  intro i a hsign
  exact (hsign (hneg i)).elim

end Naturality

/-- Forward transport identifies the two terminal sums when tangent
coefficients agree. This includes incoming coefficients from either side. -/
theorem comp_terminalGraphLift
    (hzero : ∀ i (a : ℳ i), w i = 0 → e a = a) :
    e.toLinearMap.comp (terminalGraphLift ℳ e w) = terminalGraphRight ℳ e w := by
  ext a
  induction a using DirectSum.Decomposition.inductionOn ℳ with
  | zero => simp
  | @homogeneous i a =>
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe,
      terminalGraphLift_of_mem ℳ e w a.property, terminalGraphRight_of_mem ℳ e w a.property]
    split_ifs with hp hn hn
    · omega
    · exact e.apply_symm_apply a
    · rfl
    · exact hzero i a (by omega)
  | add a b ha hb => simp_all

/-- The two independently constructed terminal totals have exactly one common
linear lift through the graph, also after precomposition by any incoming map. -/
theorem existsUnique_terminalGraphLift {E : Type*} [AddCommMonoid E] [Module R E]
    (hzero : ∀ i (a : ℳ i), w i = 0 → e a = a) (α : E →ₗ[R] M) :
    ∃! l : E →ₗ[R] M,
      (graph ℳ ℳ e).left.comp l = (terminalGraphLift ℳ e w).comp α ∧
      (graph ℳ ℳ e).right.comp l = (terminalGraphRight ℳ e w).comp α := by
  refine ⟨(terminalGraphLift ℳ e w).comp α, ⟨by simp, ?_⟩, ?_⟩
  · rw [graph_right, ← LinearMap.comp_assoc, comp_terminalGraphLift ℳ e w hzero]
  · intro l hl
    simpa only [graph_left, LinearMap.id_comp] using hl.1

end TauCeti.GradedCorrespondence
