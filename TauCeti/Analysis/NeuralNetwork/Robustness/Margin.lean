/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.PiL2
public import TauCeti.Analysis.Normed.Group.Pi

/-!
# Lipschitz-margin certificates of robustness

A classifier with class index type `ι` on a set `X` is a map `f : X → ι → ℝ` of logits. It
predicts the class `i` at `x` when `f x j < f x i` for every `j ≠ i`. A certificate on a set `S`
says that `f` predicts `i` at every point of `S`. When `S` is a ball about `x`, `f` predicts `i`
at each point at distance less than the radius from `x`.

A Lipschitz bound on the logits gives such a certificate. The gap `f y i - f y j` moves by at
most `√2 L dist x y` when `f` is `L`-Lipschitz into `EuclideanSpace ℝ ι`, so a margin `m` at `x`
certifies every ball of radius `ε` with `√2 L ε ≤ m`. With one Lipschitz constant for each gap,
the margin of each gap is compared with its own constant.

The coordinate bounds behind the constants `√2` and `2` are
`EuclideanSpace.abs_sub_le_sqrt_two_mul_norm` and `Pi.abs_sub_le_two_mul_norm`.

## Main declarations

* `TauCeti.CertifiedOn f S i`: `f` predicts the class `i` at every point of `S`.
* `TauCeti.certifiedOn_union`, `TauCeti.certifiedOn_iUnion`, `TauCeti.certifiedOn_sUnion`,
  `TauCeti.CertifiedOn.mono`, `TauCeti.certifiedOn_empty`: the predicate as a function of `S`.
* `TauCeti.CertifiedOn.lt_of_ball`: a certificate on a ball of positive radius gives the
  prediction at the centre.
* `TauCeti.CertifiedOn.comp_ofLp`: a certificate on a sup-norm ball gives one on the `ℓᵖ` ball of
  the same radius.
* `TauCeti.certifiedOn_ball_of_lipschitzWith_gap`: the certificate from one Lipschitz constant
  for each gap.
* `TauCeti.certifiedOn_ball_of_lipschitzWith`: the certificate from one Lipschitz constant of
  the logits in `EuclideanSpace ℝ ι`.
* `TauCeti.certifiedOn_ball_of_lipschitzWith_pi`: the same with the logits in the sup norm.

## References

* Yusuke Tsuzuku, Issei Sato, Masashi Sugiyama, *Lipschitz-Margin Training: Scalable
  Certification of Perturbation Invariance for Deep Neural Networks*, NeurIPS 2018,
  Propositions 1 and 2.
-/

public section

open Metric Set WithLp
open scoped NNReal ENNReal

namespace TauCeti

section CertifiedOn

variable {X Y ι : Type*} {f : X → ι → ℝ} {S T : Set X} {i : ι}

/-- The classifier `f` with logits `f x : ι → ℝ` is certified on `S` with class `i` when it
predicts `i` at every point of `S`: `f x j < f x i` for all `x ∈ S` and `j ≠ i`. -/
def CertifiedOn (f : X → ι → ℝ) (S : Set X) (i : ι) : Prop :=
  ∀ x ∈ S, ∀ j, j ≠ i → f x j < f x i

/-- The defining property of `CertifiedOn`. -/
theorem certifiedOn_iff : CertifiedOn f S i ↔ ∀ x ∈ S, ∀ j, j ≠ i → f x j < f x i :=
  Iff.rfl

/-- A certificate on `S` gives the prediction at each point of `S`. -/
theorem CertifiedOn.lt (h : CertifiedOn f S i) {x : X} (hx : x ∈ S) {j : ι} (hj : j ≠ i) :
    f x j < f x i :=
  h x hx j hj

/-- A certificate on `S` restricts to every subset of `S`. -/
theorem CertifiedOn.mono (h : CertifiedOn f S i) (hTS : T ⊆ S) : CertifiedOn f T i :=
  fun x hx => h x (hTS hx)

/-- Every classifier is certified on the empty set with every class. -/
@[simp]
theorem certifiedOn_empty (f : X → ι → ℝ) (i : ι) : CertifiedOn f ∅ i :=
  fun _ hx => hx.elim

/-- A certificate on `{x}` is the prediction of `i` at `x`. -/
@[simp]
theorem certifiedOn_singleton {x : X} :
    CertifiedOn f {x} i ↔ ∀ j, j ≠ i → f x j < f x i := by
  simp [certifiedOn_iff]

/-- A certificate on a union of two sets is a certificate on each of them. -/
@[simp]
theorem certifiedOn_union : CertifiedOn f (S ∪ T) i ↔ CertifiedOn f S i ∧ CertifiedOn f T i := by
  simp only [certifiedOn_iff, mem_union, or_imp, forall_and]

/-- A certificate on an indexed union is a certificate on each of its sets. -/
@[simp]
theorem certifiedOn_iUnion {κ : Sort*} {s : κ → Set X} :
    CertifiedOn f (⋃ a, s a) i ↔ ∀ a, CertifiedOn f (s a) i := by
  simp only [certifiedOn_iff, mem_iUnion, forall_exists_index]
  exact forall_comm

/-- A certificate on the union of a family of sets is a certificate on each set of the
family. -/
@[simp]
theorem certifiedOn_sUnion {s : Set (Set X)} :
    CertifiedOn f (⋃₀ s) i ↔ ∀ t ∈ s, CertifiedOn f t i := by
  rw [sUnion_eq_biUnion]
  simp only [certifiedOn_iUnion]

/-- Precomposition by `φ` certifies `T` exactly when `f` is certified on the image `φ '' T`. -/
theorem certifiedOn_comp_iff {φ : Y → X} {T : Set Y} :
    CertifiedOn (f ∘ φ) T i ↔ CertifiedOn f (φ '' T) i := by
  simp [certifiedOn_iff]

/-- A certificate on a ball of positive radius gives the prediction at its centre. -/
theorem CertifiedOn.lt_of_ball [PseudoMetricSpace X] {x : X} {r : ℝ}
    (h : CertifiedOn f (ball x r) i) (hr : 0 < r) {j : ι} (hj : j ≠ i) : f x j < f x i :=
  h.lt (mem_ball_self hr) hj

/-- A certificate on the sup-norm ball of radius `r` about `ofLp x` gives a certificate on the
`ℓᵖ` ball of radius `r` about `x`, since the sup norm is at most the `ℓᵖ` norm. For `p = 2` this
transports an `ℓ∞` certificate to an `ℓ²` certificate. -/
theorem CertifiedOn.comp_ofLp {p : ℝ≥0∞} [Fact (1 ≤ p)] {η : Type*} [Fintype η]
    {β : η → Type*} [∀ a, PseudoMetricSpace (β a)] {g : (∀ a, β a) → ι → ℝ} {x : PiLp p β}
    {r : ℝ} (h : CertifiedOn g (ball (ofLp x) r) i) :
    CertifiedOn (fun y : PiLp p β => g (ofLp y)) (ball x r) i := by
  refine certifiedOn_comp_iff.2 (h.mono ?_)
  simpa using ((PiLp.lipschitzWith_ofLp p β).mapsTo_ball one_ne_zero x r).image_subset

end CertifiedOn

section Margin

variable {ι X : Type*} [PseudoMetricSpace X]

/-- **Per-pair Lipschitz-margin certificate.** If each gap `y ↦ f y i - f y j` with `j ≠ i` is
`L j`-Lipschitz, positive at `x`, and at least `L j * ε` at `x`, then `f` is certified on the
open ball of radius `ε` about `x` with class `i`. -/
theorem certifiedOn_ball_of_lipschitzWith_gap {f : X → ι → ℝ} {i : ι} {L : ι → ℝ≥0}
    (hf : ∀ j, j ≠ i → LipschitzWith (L j) fun y => f y i - f y j) {x : X} {ε : ℝ}
    (hpos : ∀ j, j ≠ i → 0 < f x i - f x j) (hε : ∀ j, j ≠ i → (L j : ℝ) * ε ≤ f x i - f x j) :
    CertifiedOn f (ball x ε) i := by
  intro y hy j hj
  have hdist : f x i - f x j - (f y i - f y j) ≤ L j * dist x y := by
    have := (hf j hj).dist_le_mul x y
    rw [Real.dist_eq] at this
    exact (le_abs_self _).trans this
  have hlt : (L j : ℝ) * dist x y < f x i - f x j := by
    rcases eq_zero_or_pos (L j) with h0 | h0
    · simpa [h0] using hpos j hj
    · exact (mul_lt_mul_of_pos_left (mem_ball'.1 hy) h0).trans_le (hε j hj)
  linarith

/-- **Lipschitz-margin certificate.** If the logits `f : X → EuclideanSpace ℝ ι` are
`L`-Lipschitz, every gap `f x i - f x j` with `j ≠ i` is at least `m > 0`, and `√2 L ε ≤ m`, then
`f` is certified on the open ball of radius `ε` about `x` with class `i`. -/
theorem certifiedOn_ball_of_lipschitzWith [Fintype ι] {f : X → EuclideanSpace ℝ ι} {L : ℝ≥0}
    (hf : LipschitzWith L f) {x : X} {i : ι} {m ε : ℝ} (hm : 0 < m)
    (hgap : ∀ j, j ≠ i → m ≤ f x i - f x j) (hε : √2 * L * ε ≤ m) :
    CertifiedOn (fun y => (f y : ι → ℝ)) (ball x ε) i :=
  certifiedOn_ball_of_lipschitzWith_gap (L := fun _ => NNReal.sqrt 2 * L)
    (fun _ _ => (EuclideanSpace.lipschitzWith_apply_sub_apply i _).comp hf)
    (fun j hj => hm.trans_le (hgap j hj))
    (fun j hj => by simpa using hε.trans (hgap j hj))

/-- **Lipschitz-margin certificate, sup norm.** If the logits `f : X → ι → ℝ` are `L`-Lipschitz
for the sup norm, every gap `f x i - f x j` with `j ≠ i` is at least `m > 0`, and `2 L ε ≤ m`,
then `f` is certified on the open ball of radius `ε` about `x` with class `i`. -/
theorem certifiedOn_ball_of_lipschitzWith_pi [Fintype ι] {f : X → ι → ℝ} {L : ℝ≥0}
    (hf : LipschitzWith L f) {x : X} {i : ι} {m ε : ℝ} (hm : 0 < m)
    (hgap : ∀ j, j ≠ i → m ≤ f x i - f x j) (hε : 2 * L * ε ≤ m) :
    CertifiedOn f (ball x ε) i :=
  certifiedOn_ball_of_lipschitzWith_gap (L := fun _ => (1 + 1) * L)
    (fun j _ => ((LipschitzWith.eval (α := fun _ : ι => ℝ) i).sub
      (LipschitzWith.eval (α := fun _ : ι => ℝ) j)).comp hf)
    (fun j hj => hm.trans_le (hgap j hj))
    (fun j hj => by simpa [one_add_one_eq_two] using hε.trans (hgap j hj))

end Margin

end TauCeti
