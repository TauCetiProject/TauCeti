/-
Copyright (c) 2026 Mei contributors. All rights reserved.
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
Original copyright and author credit are retained.
-/

public noncomputable section

namespace TauCeti.GradedCorrespondence

variable {R M ι : Type*} [Semiring R] [AddCommMonoid M] [Module R M]
  [DecidableEq ι] (ℳ : ι → Submodule R M) [DirectSum.Decomposition ℳ]
  (e : M ≃ₗ[R] M) (w : ι → ℤ)

/-- Negative-side values of all incoming homogeneous coefficients. Inputs from
the positive side cross by the inverse equivalence; the other inputs stay put. -/
def terminalGraphLeft : Module.End R M :=
  DirectSum.homogeneousExtend ℳ (fun i => if 0 < w i then
    e.symm.toLinearMap.comp (ℳ i).subtype else (ℳ i).subtype)

/-- Positive-side values of all incoming homogeneous coefficients. Inputs from
the negative side cross by the equivalence; the other inputs stay put. -/
def terminalGraphRight : Module.End R M :=
  terminalGraphLeft ℳ e.symm (fun i => -w i)

/-- Restricting the negative-side total to a homogeneous piece gives its
inverse transport in positive normal degree and the inclusion otherwise. -/
@[simp] theorem terminalGraphLeft_comp_subtype (i : ι) :
    (terminalGraphLeft ℳ e w).comp (ℳ i).subtype =
      if 0 < w i then e.symm.toLinearMap.comp (ℳ i).subtype else (ℳ i).subtype := by
  ext a
  simp only [LinearMap.comp_apply, Submodule.subtype_apply, terminalGraphLeft,
    DirectSum.homogeneousExtend_coe]

/-- The prescribed restrictions on homogeneous pieces characterize the
negative-side terminal total uniquely. -/
theorem eq_terminalGraphLeft (f : Module.End R M)
    (hf : ∀ i, f.comp (ℳ i).subtype =
      if 0 < w i then e.symm.toLinearMap.comp (ℳ i).subtype else (ℳ i).subtype) :
    f = terminalGraphLeft ℳ e w :=
  DirectSum.homogeneousExtend_unique ℳ _ f hf

/-- Restricting the positive-side total to a homogeneous piece gives its
forward transport in negative normal degree and the inclusion otherwise. -/
@[simp] theorem terminalGraphRight_comp_subtype (i : ι) :
    (terminalGraphRight ℳ e w).comp (ℳ i).subtype =
      if w i < 0 then e.toLinearMap.comp (ℳ i).subtype else (ℳ i).subtype := by
  simpa only [terminalGraphRight, neg_pos, LinearEquiv.symm_symm] using
    terminalGraphLeft_comp_subtype ℳ e.symm (fun i => -w i) i

/-- The prescribed restrictions on homogeneous pieces characterize the
positive-side terminal total uniquely. -/
theorem eq_terminalGraphRight (f : Module.End R M)
    (hf : ∀ i, f.comp (ℳ i).subtype =
      if w i < 0 then e.toLinearMap.comp (ℳ i).subtype else (ℳ i).subtype) :
    f = terminalGraphRight ℳ e w := by
  apply eq_terminalGraphLeft ℳ e.symm (fun i => -w i) f
  simpa only [neg_pos, LinearEquiv.symm_symm] using hf

/-- On one homogeneous input the negative-side total is the incoming value
or its inverse transport, according to its normal degree. -/
theorem terminalGraphLeft_of_mem {i : ι} {a : M} (ha : a ∈ ℳ i) :
    terminalGraphLeft ℳ e w a = if 0 < w i then e.symm a else a := by
  rw [terminalGraphLeft, DirectSum.homogeneousExtend_of_mem ℳ _ ha]
  split_ifs <;> simp

/-- The negative-side total on a homogeneous subtype input is its inverse transport
in positive normal degree and the input itself otherwise. -/
@[simp] theorem terminalGraphLeft_coe {i : ι} (a : ℳ i) :
    terminalGraphLeft ℳ e w a = if 0 < w i then e.symm a else a :=
  terminalGraphLeft_of_mem ℳ e w a.property

/-- On one homogeneous input the positive-side value is the incoming value
or its forward transport, according to its normal degree. -/
theorem terminalGraphRight_of_mem {i : ι} {a : M} (ha : a ∈ ℳ i) :
    terminalGraphRight ℳ e w a = if w i < 0 then e a else a := by
  simpa only [terminalGraphRight, neg_pos, LinearEquiv.symm_symm] using
    terminalGraphLeft_of_mem ℳ e.symm (fun i => -w i) ha

/-- The positive-side terminal value on a homogeneous subtype input is its
forward transport in negative normal degree and the input itself otherwise. -/
@[simp] theorem terminalGraphRight_coe {i : ι} (a : ℳ i) :
    terminalGraphRight ℳ e w a = if w i < 0 then e a else a :=
  terminalGraphRight_of_mem ℳ e w a.property

/-- The negative-side total is the finite sum of inverse-transferred positive inputs
and unchanged nonpositive inputs, retaining their whole decorations. -/
theorem terminalGraphLeft_eq_sum [∀ i (a : ℳ i), Decidable (a ≠ 0)] (a : M) :
    terminalGraphLeft ℳ e w a =
      ∑ i ∈ (DirectSum.decompose ℳ a).support,
        if 0 < w i then e.symm (DirectSum.decompose ℳ a i) else
          (DirectSum.decompose ℳ a i : M) := by
  rw [terminalGraphLeft, DirectSum.homogeneousExtend_eq_sum]
  apply Finset.sum_congr rfl
  intro i _
  split_ifs <;> simp

/-- The positive-side total is the finite sum of forward-transferred negative
inputs and unchanged nonnegative inputs. -/
theorem terminalGraphRight_eq_sum [∀ i (a : ℳ i), Decidable (a ≠ 0)] (a : M) :
    terminalGraphRight ℳ e w a =
      ∑ i ∈ (DirectSum.decompose ℳ a).support,
        if w i < 0 then e (DirectSum.decompose ℳ a i) else
          (DirectSum.decompose ℳ a i : M) := by
  simpa only [terminalGraphRight, neg_pos, LinearEquiv.symm_symm] using
    terminalGraphLeft_eq_sum ℳ e.symm (fun i => -w i) a

/-- The negative-side terminal total is positive when inverse transport preserves
positivity on positive normal degrees and unchanged inputs do so on the others. -/
theorem terminalGraphLeft_mem_addSubmonoid (Pos : ι → AddSubmonoid M) (P : AddSubmonoid M)
    (hcross : ∀ i (a : ℳ i), 0 < w i → (a : M) ∈ Pos i → e.symm a ∈ P)
    (hstay : ∀ i (a : ℳ i), w i ≤ 0 → (a : M) ∈ Pos i → (a : M) ∈ P)
    (a : M) (ha : ∀ i, (DirectSum.decompose ℳ a i : M) ∈ Pos i) :
    terminalGraphLeft ℳ e w a ∈ P := by
  classical
  rw [terminalGraphLeft_eq_sum]
  apply P.sum_mem
  intro i _
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
  apply terminalGraphLeft_mem_addSubmonoid ℳ e.symm (fun i => -w i) Pos P
  · simpa only [neg_pos, LinearEquiv.symm_symm] using hcross
  · simpa only [neg_nonpos] using hstay
  · exact ha

section Naturality

variable {N κ : Type*} [AddCommMonoid N] [Module R N] [DecidableEq κ]
  (𝓝 : κ → Submodule R N) [DirectSum.Decomposition 𝓝]
  (e' : N ≃ₗ[R] N) (w' : κ → ℤ) (r : M →ₗ[R] N) (σ : ι → κ)

/-- Negative-side terminal totals commute with an intertwining coefficient map
exactly when the target wall action fixes the image of every homogeneous input
whose positive-normal branch changes. The fixed images need not vanish. -/
theorem comp_terminalGraphLeft_iff
    (hr : ∀ i a, a ∈ ℳ i → r a ∈ 𝓝 (σ i))
    (he : r.comp e.toLinearMap = e'.toLinearMap.comp r) :
    r.comp (terminalGraphLeft ℳ e w) = (terminalGraphLeft 𝓝 e' w').comp r ↔
      ∀ i (a : ℳ i), ¬ (0 < w i ↔ 0 < w' (σ i)) → e' (r a) = r a := by
  have heinv : r.comp e.symm.toLinearMap = e'.symm.toLinearMap.comp r := by
    rw [e.comp_toLinearMap_symm_eq, LinearMap.comp_assoc,
      e'.eq_toLinearMap_symm_comp, he]
  have hinv (a : M) : r (e.symm a) = e'.symm (r a) := LinearMap.congr_fun heinv a
  constructor
  · intro h i a hsign
    have hv := LinearMap.congr_fun h a
    simp only [LinearMap.comp_apply, terminalGraphLeft_coe,
      terminalGraphLeft_of_mem 𝓝 e' w' (hr i a a.property)] at hv
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
    simp only [LinearMap.comp_apply, Submodule.subtype_apply, terminalGraphLeft_coe,
      terminalGraphLeft_of_mem 𝓝 e' w' (hr i a a.property)]
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
theorem comp_terminalGraphRight_iff
    (hr : ∀ i a, a ∈ ℳ i → r a ∈ 𝓝 (σ i))
    (he : r.comp e.toLinearMap = e'.toLinearMap.comp r) :
    r.comp (terminalGraphRight ℳ e w) = (terminalGraphRight 𝓝 e' w').comp r ↔
      ∀ i (a : ℳ i), ¬ (w i < 0 ↔ w' (σ i) < 0) → e' (r a) = r a := by
  have heinv : r.comp e.symm.toLinearMap = e'.symm.toLinearMap.comp r := by
    rw [e.comp_toLinearMap_symm_eq, LinearMap.comp_assoc,
      e'.eq_toLinearMap_symm_comp, he]
  simpa only [terminalGraphRight, neg_pos, e'.symm_apply_eq, eq_comm] using
    comp_terminalGraphLeft_iff ℳ e.symm (fun i => -w i)
      𝓝 e'.symm (fun j => -w' j) r σ hr heinv

/-- A coefficient map intertwining the wall actions also intertwines the
negative-side terminal totals. Only positivity of normal degrees must agree;
the coefficient map and degree map may have kernels or identify degrees. -/
theorem comp_terminalGraphLeft_of_pos
    (hr : ∀ i a, a ∈ ℳ i → r a ∈ 𝓝 (σ i))
    (he : r.comp e.toLinearMap = e'.toLinearMap.comp r)
    (hpos : ∀ i, 0 < w i ↔ 0 < w' (σ i)) :
    r.comp (terminalGraphLeft ℳ e w) = (terminalGraphLeft 𝓝 e' w').comp r := by
  apply (comp_terminalGraphLeft_iff ℳ e w 𝓝 e' w' r σ hr he).mpr
  intro i a hsign
  exact (hsign (hpos i)).elim

/-- A coefficient map intertwining the wall actions also intertwines the
positive-side terminal totals. Only negativity of normal degrees must agree;
no injectivity assumption is imposed on either map. -/
theorem comp_terminalGraphRight_of_neg
    (hr : ∀ i a, a ∈ ℳ i → r a ∈ 𝓝 (σ i))
    (he : r.comp e.toLinearMap = e'.toLinearMap.comp r)
    (hneg : ∀ i, w i < 0 ↔ w' (σ i) < 0) :
    r.comp (terminalGraphRight ℳ e w) = (terminalGraphRight 𝓝 e' w').comp r := by
  apply (comp_terminalGraphRight_iff ℳ e w 𝓝 e' w' r σ hr he).mpr
  intro i a hsign
  exact (hsign (hneg i)).elim

end Naturality

/-- Forward transport identifies the two terminal sums when tangent
coefficients agree. This includes incoming coefficients from either side. -/
theorem toLinearMap_comp_terminalGraphLeft
    (hzero : ∀ i (a : ℳ i), w i = 0 → e a = a) :
    e.toLinearMap.comp (terminalGraphLeft ℳ e w) = terminalGraphRight ℳ e w := by
  ext a
  induction a using DirectSum.Decomposition.inductionOn ℳ with
  | zero => simp
  | @homogeneous i a =>
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe,
      terminalGraphLeft_of_mem ℳ e w a.property, terminalGraphRight_of_mem ℳ e w a.property]
    split_ifs with hp hn hn
    · omega
    · exact e.apply_symm_apply a
    · rfl
    · exact hzero i a (by omega)
  | add a b ha hb => simp_all

/-- The two independently constructed terminal totals have exactly one common
linear lift through the graph, also after precomposition by any incoming map. -/
theorem existsUnique_terminalGraphLeft {E : Type*} [AddCommMonoid E] [Module R E]
    (hzero : ∀ i (a : ℳ i), w i = 0 → e a = a) (α : E →ₗ[R] M) :
    ∃! l : E →ₗ[R] M,
      (graph ℳ ℳ e).left.comp l = (terminalGraphLeft ℳ e w).comp α ∧
      (graph ℳ ℳ e).right.comp l = (terminalGraphRight ℳ e w).comp α := by
  apply (graph_existsUnique_lift_iff ℳ ℳ e _ _).mpr
  rw [← LinearMap.comp_assoc, toLinearMap_comp_terminalGraphLeft ℳ e w hzero]

end TauCeti.GradedCorrespondence
