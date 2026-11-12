/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Convex.Quasiconvex
public import Mathlib.Analysis.LocallyConvex.WeakSpace
public import Mathlib.Analysis.Normed.Module.DoubleDual
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Topology.Instances.EReal.Lemmas
public import Mathlib.Topology.Semicontinuity.Basic
import Mathlib.Analysis.Convex.Jensen
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import TauCeti.Analysis.LocallyConvex.WeakSpace
import TauCeti.Analysis.Normed.Module.DoubleDual
import TauCeti.Analysis.Normed.Module.Mazur
import TauCeti.Analysis.Normed.Module.WeakSpace.EberleinSmulian
import TauCeti.Topology.Semicontinuity.Basic

/-!
# Weak lower semicontinuity and the direct method of the calculus of variations

This file develops the topological and sequential forms of the direct method of the calculus of
variations on reflexive normed and seminormed spaces, together with the coercivity (bounded
sublevel) and weak lower semicontinuity calculus that feeds them.

## Main definitions and results

### Bounded sublevels (`TauCeti.HasBoundedSublevelsOn`)
* `TauCeti.HasBoundedSublevelsOn E S`: every sublevel `{u ∈ S | E u ≤ b}` is bounded in the
  bornology of `V`.
* `TauCeti.hasBoundedSublevelsOn_iff_forall_isBounded_range`: on a seminormed group, bounded
  sublevels are equivalent to norm boundedness of every sequence in `S` with energy bounded above.
* `TauCeti.hasBoundedSublevelsOn_of_tendsto_cobounded`: divergence `E u → +∞` along
  `cobounded V ⊓ 𝓟 S` implies bounded sublevels on `S`.
* Stability under subset restriction (`HasBoundedSublevelsOn.mono`), domination
  (`HasBoundedSublevelsOn.of_le`), pointwise maxima (`HasBoundedSublevelsOn.sup_left`,
  `HasBoundedSublevelsOn.sup_right`), positive scaling (`HasBoundedSublevelsOn.const_mul`),
  addition of an energy bounded below (`HasBoundedSublevelsOn.add_of_bddBelow`), translation
  (`HasBoundedSublevelsOn.comp_add_right`), and continuous semilinear equivalences
  (`HasBoundedSublevelsOn.comp_continuousLinearEquiv`), together with `Bornology.IsBounded` and
  norm witnesses (`Bornology.IsBounded.hasBoundedSublevelsOn`, `TauCeti.hasBoundedSublevelsOn_norm`,
  `TauCeti.hasBoundedSublevelsOn_norm_rpow`, `TauCeti.hasBoundedSublevelsOn_norm_pow`).

### Weak and sequential weak lower semicontinuity (`TauCeti.SeqWeakLowerSemicontinuousOn`)
* `TauCeti.lowerSemicontinuousOn_toWeakSpace_iff_exists_isClosed` and
  `TauCeti.lowerSemicontinuousOn_toWeakSpace_iff_isClosed_sublevel`: topological weak lower
  semicontinuity on `S` via weak closedness of sublevels.
* `TauCeti.SeqWeakLowerSemicontinuousOn 𝕜 E S`: `(E v : EReal) ≤ liminf (E ∘ u) atTop` whenever
  `u n ∈ S` converges weakly to `v ∈ S`, with lower limit in `EReal` so sequences unbounded above
  or below are handled uniformly; `SeqWeakLowerSemicontinuousOn.le_of_tendsto` extracts the
  finite-limit inequality.
* `TauCeti.lowerSemicontinuousOn_toWeakSpace_iff_seqWeakLowerSemicontinuousOn`: on a weakly
  compact set `K`, topological and sequential weak lower semicontinuity coincide, building on
  Kaplansky's theorem (`TauCeti.frechetUrysohnSpace_toWeakSpace_of_isCompact`).
* `ConvexOn.le_liminf_of_tendsto_toWeakSpace`: sequential weak `liminf` inequality for convex
  energies assuming lower semicontinuity within `S` only at the single limit point `x` (without
  requiring `x ∈ S`).
* Weak lower semicontinuity of norms, norm powers `‖·‖ ^ p` (`0 ≤ p`) and `‖·‖ ^ n`, operator
  energies `‖D ·‖ ^ p` and `‖D ·‖ ^ n`, and weak continuity of real parts of continuous linear
  functionals (`StrongDual.continuous_re_comp_toWeakSpace_symm`).

### Direct-method theorems and minimizing sequences
* `TauCeti.exists_isMinOn_of_weak_closed`: topological direct method on a nonempty weakly closed
  set `S` with bounded sublevels in a reflexive seminormed space over a proper field, assuming no
  a priori lower bound on `E`, together with the norm-topology quasiconvex corollary
  `QuasiconvexOn.exists_isMinOn` and weak compactness of bounded minimizer sets
  (`TauCeti.isCompact_toWeakSpace_setOf_isMinOn_of_isBounded`,
  `HasBoundedSublevelsOn.isCompact_toWeakSpace_setOf_isMinOn`).
* `TauCeti.exists_subseq_tendsto_toWeakSpace_isMinOn` and
  `TauCeti.exists_isMinOn_of_bounded_minimizing_sequence`: sequential direct method from a single
  norm-bounded minimizing sequence on a sequentially weakly closed set in a reflexive normed space,
  plus full weak convergence when the minimizer is unique
  (`TauCeti.tendsto_toWeakSpace_of_unique_isMinOn`), a single-sublevel localization
  (`TauCeti.exists_isMinOn_of_bounded_minimizing_sequence_sublevel`), and automatic lower
  boundedness and attainment under `HasBoundedSublevelsOn` and `SeqWeakLowerSemicontinuousOn`
  (`SeqWeakLowerSemicontinuousOn.bddBelow_image`, `SeqWeakLowerSemicontinuousOn.exists_isMinOn`).

## References

* V. Ivrii, *Microlocal Analysis, Sharp Spectral Asymptotics and Applications*, §13.1, Theorem 1
  and Theorem 4.
* J. K. Hunter, *Applied Analysis*, World Scientific, 2001, §4.2.
* H. Brezis, *Functional Analysis, Sobolev Spaces and Partial Differential Equations*, Springer,
  2011, §3.3 and Corollary 3.9.
-/

public section

open Bornology Filter Function Metric NormedSpace Set Topology
open scoped BigOperators

namespace TauCeti

/-! ### Bounded sublevels -/

/-- An energy `E : V → β` has bounded sublevels on `S : Set V` if every sublevel
`{u ∈ S | E u ≤ b}` is bounded in the bornology of `V`. -/
def HasBoundedSublevelsOn {V β : Type*} [Bornology V] [Preorder β] (E : V → β) (S : Set V) :
    Prop :=
  ∀ b : β, IsBounded {u ∈ S | E u ≤ b}

/-- Definitional unfolding of `TauCeti.HasBoundedSublevelsOn`. -/
theorem hasBoundedSublevelsOn_def {V β : Type*} [Bornology V] [Preorder β] {E : V → β}
    {S : Set V} :
    HasBoundedSublevelsOn E S ↔ ∀ b : β, IsBounded {u ∈ S | E u ≤ b} :=
  Iff.rfl

/-- Any energy has bounded sublevels on an already bounded set. -/
theorem _root_.Bornology.IsBounded.hasBoundedSublevelsOn {V β : Type*} [Bornology V] [Preorder β]
    {S : Set V} (hS : IsBounded S) (E : V → β) :
    HasBoundedSublevelsOn E S :=
  fun _ ↦ hS.subset fun _ hu ↦ hu.1

/-- Every energy has bounded sublevels on the empty set. -/
@[simp]
theorem hasBoundedSublevelsOn_empty {V β : Type*} [Bornology V] [Preorder β] (E : V → β) :
    HasBoundedSublevelsOn E ∅ :=
  isBounded_empty.hasBoundedSublevelsOn E

namespace HasBoundedSublevelsOn

section Bornology

variable {V β : Type*} [Bornology V] [Preorder β] {E E₁ E₂ : V → β} {S T : Set V}

/-- Every sublevel `{u ∈ S | E u ≤ b}` is bounded. -/
theorem isBounded_sublevel (h : HasBoundedSublevelsOn E S) (b : β) :
    IsBounded {u ∈ S | E u ≤ b} :=
  h b

/-- Every sublevel written as `S ∩ E ⁻¹' Iic b` is bounded. -/
theorem isBounded_inter_preimage_Iic (h : HasBoundedSublevelsOn E S) (b : β) :
    IsBounded (S ∩ E ⁻¹' Iic b) :=
  h b

/-- Bounded sublevels are inherited by subsets of the admissible set. -/
theorem mono (h : HasBoundedSublevelsOn E S) (hTS : T ⊆ S) : HasBoundedSublevelsOn E T :=
  fun b ↦ (h b).subset fun _ hu ↦ ⟨hTS hu.1, hu.2⟩

/-- If `E₁` has bounded sublevels on `S` and `E₁ ≤ E₂` on `S`, then `E₂` has bounded sublevels on
`S`. -/
theorem of_le (h : HasBoundedSublevelsOn E₁ S) (hle : ∀ u ∈ S, E₁ u ≤ E₂ u) :
    HasBoundedSublevelsOn E₂ S :=
  fun b ↦ (h b).subset fun _ ⟨hu, hEu⟩ ↦ ⟨hu, (hle _ hu).trans hEu⟩

/-- Any family in `S` whose energy image is bounded above has bounded range. -/
theorem isBounded_range_of_bddAbove {ι : Type*} (h : HasBoundedSublevelsOn E S) {u : ι → V}
    (hu : ∀ i, u i ∈ S) (hbdd : BddAbove (range (E ∘ u))) :
    IsBounded (range u) := by
  obtain ⟨b, hb⟩ := hbdd
  exact (h b).subset (range_subset_iff.2 fun i ↦ ⟨hu i, hb (mem_range_self i)⟩)

end Bornology

/-- Pointwise maximum with another energy preserves bounded sublevels on the left. -/
theorem sup_left {V β : Type*} [Bornology V] [SemilatticeSup β] {E₁ : V → β} (E₂ : V → β)
    {S : Set V} (h : HasBoundedSublevelsOn E₁ S) :
    HasBoundedSublevelsOn (fun u ↦ E₁ u ⊔ E₂ u) S :=
  h.of_le fun _ _ ↦ le_sup_left

/-- Pointwise maximum with another energy preserves bounded sublevels on the right. -/
theorem sup_right {V β : Type*} [Bornology V] [SemilatticeSup β] (E₁ : V → β) {E₂ : V → β}
    {S : Set V} (h : HasBoundedSublevelsOn E₂ S) :
    HasBoundedSublevelsOn (fun u ↦ E₁ u ⊔ E₂ u) S :=
  h.of_le fun _ _ ↦ le_sup_right

section RealEnergy

variable {V : Type*} [Bornology V] {E E₁ E₂ : V → ℝ} {S : Set V}

/-- Adding a constant preserves bounded sublevels. -/
theorem add_const (h : HasBoundedSublevelsOn E S) (c : ℝ) :
    HasBoundedSublevelsOn (fun u ↦ E u + c) S :=
  fun b ↦ (h (b - c)).subset fun _ ⟨hu, hEu⟩ ↦ ⟨hu, le_sub_iff_add_le.2 hEu⟩

/-- Subtracting a constant preserves bounded sublevels. -/
theorem sub_const (h : HasBoundedSublevelsOn E S) (c : ℝ) :
    HasBoundedSublevelsOn (fun u ↦ E u - c) S := by
  simpa only [sub_eq_add_neg] using h.add_const (-c)

/-- Scaling an energy by a positive real constant preserves bounded sublevels. -/
theorem const_mul (h : HasBoundedSublevelsOn E S) {c : ℝ} (hc : 0 < c) :
    HasBoundedSublevelsOn (fun u ↦ c * E u) S :=
  fun b ↦ (h (b / c)).subset fun _ ⟨hu, hEu⟩ ↦ ⟨hu, (le_div_iff₀' hc).2 hEu⟩

/-- Adding an energy bounded below on `S` to an energy with bounded sublevels on `S` yields an
energy with bounded sublevels on `S`. -/
theorem add_of_bddBelow (h₁ : HasBoundedSublevelsOn E₁ S) (h₂ : BddBelow (E₂ '' S)) :
    HasBoundedSublevelsOn (fun u ↦ E₁ u + E₂ u) S := by
  obtain ⟨m, hm⟩ := h₂
  exact (h₁.add_const m).of_le fun u hu ↦ add_le_add_right (hm (mem_image_of_mem E₂ hu)) (E₁ u)

end RealEnergy

/-- Affine translation of the variable preserves bounded sublevels in a seminormed group. -/
theorem comp_add_right {V β : Type*} [SeminormedAddCommGroup V] [Preorder β] {E : V → β}
    {S : Set V} (h : HasBoundedSublevelsOn E S) (v : V) :
    HasBoundedSublevelsOn (fun u ↦ E (u + v)) ((· + v) ⁻¹' S) := by
  intro b
  refine ((isometry_add_right (-v)).lipschitzWith.isBounded_image (h b)).subset ?_
  rintro u ⟨huS, hEu⟩
  exact ⟨u + v, ⟨huS, hEu⟩, add_neg_cancel_right u v⟩

/-- Change of variable by a continuous semilinear equivalence preserves bounded sublevels. -/
theorem comp_continuousLinearEquiv {𝕜₁ 𝕜₂ V W β : Type*}
    [NontriviallyNormedField 𝕜₁] [NontriviallyNormedField 𝕜₂]
    {σ : 𝕜₁ →+* 𝕜₂} {σ' : 𝕜₂ →+* 𝕜₁} [RingHomInvPair σ σ'] [RingHomInvPair σ' σ]
    [RingHomIsometric σ'] [SeminormedAddCommGroup V] [NormedSpace 𝕜₂ V]
    [SeminormedAddCommGroup W] [NormedSpace 𝕜₁ W] [Preorder β] {E : V → β} {S : Set V}
    (h : HasBoundedSublevelsOn E S) (e : W ≃SL[σ] V) :
    HasBoundedSublevelsOn (fun w ↦ E (e w)) (e ⁻¹' S) := by
  intro b
  refine ((h b).image (e.symm : V →SL[σ'] W)).subset ?_
  rintro w ⟨hwS, hEw⟩
  exact ⟨e w, ⟨hwS, hEw⟩, e.symm_apply_apply w⟩

end HasBoundedSublevelsOn

/-- On a seminormed group, `E` has bounded sublevels on `S` if and only if every sequence in `S`
whose energy values are bounded above has norm-bounded range. -/
theorem hasBoundedSublevelsOn_iff_forall_isBounded_range {V β : Type*}
    [SeminormedAddCommGroup V] [Preorder β] {E : V → β} {S : Set V} :
    HasBoundedSublevelsOn E S ↔
      ∀ u : ℕ → V, (∀ n, u n ∈ S) → BddAbove (range (E ∘ u)) → IsBounded (range u) := by
  refine ⟨fun h u hu hbdd ↦ h.isBounded_range_of_bddAbove hu hbdd, fun hseq b ↦ ?_⟩
  by_contra hnb
  rw [isBounded_iff_forall_norm_le] at hnb
  push Not at hnb
  choose u hu hnorm using fun n : ℕ ↦ hnb n
  have hb : IsBounded (range u) :=
    hseq u (fun n ↦ (hu n).1) ⟨b, forall_mem_range.2 fun n ↦ (hu n).2⟩
  obtain ⟨C, hC⟩ := isBounded_iff_forall_norm_le.1 hb
  obtain ⟨n, hn⟩ := exists_nat_gt C
  exact hn.not_ge ((hnorm n).le.trans (hC (u n) (mem_range_self n)))

/-- If `E u → +∞` along `cobounded V ⊓ 𝓟 S`, then `E` has bounded sublevels on `S`. -/
theorem hasBoundedSublevelsOn_of_tendsto_cobounded {V β : Type*} [Bornology V] [LinearOrder β]
    [NoMaxOrder β] {E : V → β} {S : Set V} (h : Tendsto E (cobounded V ⊓ 𝓟 S) atTop) :
    HasBoundedSublevelsOn E S := by
  intro b
  obtain ⟨c, hbc⟩ := exists_gt b
  have hc : {u : V | u ∈ S → c ≤ E u} ∈ cobounded V :=
    mem_inf_principal.1 ((tendsto_atTop.1 h) c)
  refine (isBounded_compl_iff.2 hc).subset fun u ⟨huS, hEu⟩ hu' ↦ ?_
  exact (hEu.trans_lt hbc).not_ge (hu' huS)

/-- The norm has bounded sublevels on every subset of a seminormed group. -/
theorem hasBoundedSublevelsOn_norm {V : Type*} [SeminormedAddCommGroup V] (S : Set V) :
    HasBoundedSublevelsOn (fun u : V ↦ ‖u‖) S :=
  fun b ↦ isBounded_iff_forall_norm_le.2 ⟨b, fun _ ⟨_, hu⟩ ↦ hu⟩

/-- For `0 < p`, the norm power `u ↦ ‖u‖ ^ p` has bounded sublevels on every subset of a
seminormed group. -/
theorem hasBoundedSublevelsOn_norm_rpow {V : Type*} [SeminormedAddCommGroup V] {p : ℝ}
    (hp : 0 < p) (S : Set V) :
    HasBoundedSublevelsOn (fun u : V ↦ ‖u‖ ^ p) S := fun b ↦
  (hasBoundedSublevelsOn_norm S (b ^ p⁻¹)).subset fun u ⟨huS, hu⟩ ↦
    ⟨huS, (Real.rpow_rpow_inv (norm_nonneg u) hp.ne').symm.trans_le
      (Real.rpow_le_rpow (Real.rpow_nonneg (norm_nonneg u) p) hu (inv_nonneg.2 hp.le))⟩

/-- For `n ≠ 0`, the norm power `u ↦ ‖u‖ ^ n` has bounded sublevels on every subset of a
seminormed group. -/
theorem hasBoundedSublevelsOn_norm_pow {V : Type*} [SeminormedAddCommGroup V] {n : ℕ}
    (hn : n ≠ 0) (S : Set V) :
    HasBoundedSublevelsOn (fun u : V ↦ ‖u‖ ^ n) S := by
  convert hasBoundedSublevelsOn_norm_rpow (Nat.cast_pos.2 (Nat.pos_of_ne_zero hn)) S with u
  exact (Real.rpow_natCast ‖u‖ n).symm

/-! ### Weak and sequential weak lower semicontinuity -/

section WeakTopology

variable (𝕜 : Type*) {V : Type*} [CommSemiring 𝕜] [TopologicalSpace 𝕜] [ContinuousAdd 𝕜]
  [ContinuousConstSMul 𝕜 𝕜] [AddCommMonoid V] [Module 𝕜 V] [TopologicalSpace V]

/-- Weak lower semicontinuity of `E` on `S` is equivalent to every sublevel `{u ∈ S | E u ≤ b}`
being the intersection of `toWeakSpace 𝕜 V '' S` with a closed subset of `WeakSpace 𝕜 V`. -/
theorem lowerSemicontinuousOn_toWeakSpace_iff_exists_isClosed {β : Type*} [LinearOrder β]
    {E : V → β} {S : Set V} :
    LowerSemicontinuousOn (fun w : WeakSpace 𝕜 V ↦ E ((toWeakSpace 𝕜 V).symm w))
      (toWeakSpace 𝕜 V '' S) ↔
      ∀ b : β, ∃ C : Set (WeakSpace 𝕜 V), IsClosed C ∧
        toWeakSpace 𝕜 V '' {u ∈ S | E u ≤ b} = (toWeakSpace 𝕜 V '' S) ∩ C := by
  rw [lowerSemicontinuousOn_iff_preimage_Iic]
  refine forall_congr' fun b ↦ ?_
  have hpre : (toWeakSpace 𝕜 V '' S) ∩
      (fun w : WeakSpace 𝕜 V ↦ E ((toWeakSpace 𝕜 V).symm w)) ⁻¹' Iic b =
      toWeakSpace 𝕜 V '' {u ∈ S | E u ≤ b} := by
    rw [← Function.comp_def E, preimage_comp, ← (toWeakSpace 𝕜 V).image_eq_preimage_symm,
      ← image_inter (toWeakSpace 𝕜 V).injective]
    rfl
  simp only [hpre, eq_comm]

/-- On a weakly closed set `S`, weak lower semicontinuity of `E` on `S` is equivalent to weak
closedness of every sublevel `{u ∈ S | E u ≤ b}`. -/
theorem lowerSemicontinuousOn_toWeakSpace_iff_isClosed_sublevel {β : Type*} [LinearOrder β]
    {E : V → β} {S : Set V} (hS : IsClosed (toWeakSpace 𝕜 V '' S)) :
    LowerSemicontinuousOn (fun w : WeakSpace 𝕜 V ↦ E ((toWeakSpace 𝕜 V).symm w))
      (toWeakSpace 𝕜 V '' S) ↔
      ∀ b : β, IsClosed (toWeakSpace 𝕜 V '' {u ∈ S | E u ≤ b}) := by
  rw [lowerSemicontinuousOn_toWeakSpace_iff_exists_isClosed]
  refine forall_congr' fun b ↦ ⟨fun ⟨C, hC, hEq⟩ ↦ hEq ▸ hS.inter hC, fun hb ↦ ⟨_, hb, ?_⟩⟩
  exact (inter_eq_right.2 (image_mono (s := {u ∈ S | E u ≤ b}) (t := S) fun _ h ↦ h.1)).symm

/-- Sequential weak lower semicontinuity of a real energy `E : V → ℝ` on `S : Set V` over scalar
ring `𝕜`: whenever `u n ∈ S` converges weakly to `v ∈ S`, `(E v : EReal)` is at most the `EReal`
lower limit of `E (u n)`. Using `EReal` includes sequences whose energies are unbounded above or
below without extra boundedness side conditions. -/
def SeqWeakLowerSemicontinuousOn (E : V → ℝ) (S : Set V) : Prop :=
  ∀ ⦃u : ℕ → V⦄ ⦃v : V⦄, (∀ n, u n ∈ S) → v ∈ S →
    Tendsto (fun n ↦ toWeakSpace 𝕜 V (u n)) atTop (𝓝 (toWeakSpace 𝕜 V v)) →
    (E v : EReal) ≤ liminf (fun n ↦ (E (u n) : EReal)) atTop

variable {𝕜}

/-- Definitional unfolding of `TauCeti.SeqWeakLowerSemicontinuousOn`. -/
theorem seqWeakLowerSemicontinuousOn_def {E : V → ℝ} {S : Set V} :
    SeqWeakLowerSemicontinuousOn 𝕜 E S ↔
      ∀ ⦃u : ℕ → V⦄ ⦃v : V⦄, (∀ n, u n ∈ S) → v ∈ S →
        Tendsto (fun n ↦ toWeakSpace 𝕜 V (u n)) atTop (𝓝 (toWeakSpace 𝕜 V v)) →
        (E v : EReal) ≤ liminf (fun n ↦ (E (u n) : EReal)) atTop :=
  Iff.rfl

/-- Every energy is sequentially weakly lower semicontinuous on the empty set. -/
@[simp]
theorem seqWeakLowerSemicontinuousOn_empty (E : V → ℝ) :
    SeqWeakLowerSemicontinuousOn 𝕜 E ∅ :=
  fun _ _ _ hv _ ↦ False.elim hv

/-- Every constant energy is sequentially weakly lower semicontinuous. -/
@[simp]
theorem seqWeakLowerSemicontinuousOn_const {c : ℝ} {S : Set V} :
    SeqWeakLowerSemicontinuousOn 𝕜 (fun _ : V ↦ c) S :=
  fun _ _ _ _ _ ↦ (liminf_const (f := atTop) (c : EReal)).ge

namespace SeqWeakLowerSemicontinuousOn

/-- Finite-limit consequence of sequential weak lower semicontinuity: if `u n ∈ S` converges
weakly to `v ∈ S` and `E (u n) → r` in `ℝ`, then `E v ≤ r`. -/
theorem le_of_tendsto {E : V → ℝ} {S : Set V} (h : SeqWeakLowerSemicontinuousOn 𝕜 E S)
    {u : ℕ → V} {v : V} {r : ℝ} (hu : ∀ n, u n ∈ S) (hv : v ∈ S)
    (hlim : Tendsto (fun n ↦ toWeakSpace 𝕜 V (u n)) atTop (𝓝 (toWeakSpace 𝕜 V v)))
    (hEu : Tendsto (fun n ↦ E (u n)) atTop (𝓝 r)) :
    E v ≤ r := by
  have hliminf : liminf (fun n ↦ (E (u n) : EReal)) atTop = (r : EReal) :=
    (EReal.tendsto_coe.2 hEu).liminf_eq
  exact EReal.coe_le_coe_iff.1 ((h hu hv hlim).trans_eq hliminf)

/-- Sequential weak lower semicontinuity is inherited by subsets. -/
theorem mono {E : V → ℝ} {S T : Set V} (h : SeqWeakLowerSemicontinuousOn 𝕜 E S) (hTS : T ⊆ S) :
    SeqWeakLowerSemicontinuousOn 𝕜 E T :=
  fun _ _ hu hv hlim ↦ h (fun n ↦ hTS (hu n)) (hTS hv) hlim

/-- Pointwise maximum of two sequentially weakly lower semicontinuous energies on `S` is
sequentially weakly lower semicontinuous on `S`. -/
theorem sup {E₁ E₂ : V → ℝ} {S : Set V} (h₁ : SeqWeakLowerSemicontinuousOn 𝕜 E₁ S)
    (h₂ : SeqWeakLowerSemicontinuousOn 𝕜 E₂ S) :
    SeqWeakLowerSemicontinuousOn 𝕜 (fun u ↦ E₁ u ⊔ E₂ u) S := by
  intro u v hu hv hlim
  rw [EReal.coe_strictMono.monotone.map_sup]
  exact sup_le
    ((h₁ hu hv hlim).trans (liminf_le_liminf
      (Eventually.of_forall fun _ ↦ EReal.coe_le_coe_iff.2 le_sup_left)))
    ((h₂ hu hv hlim).trans (liminf_le_liminf
      (Eventually.of_forall fun _ ↦ EReal.coe_le_coe_iff.2 le_sup_right)))

/-- Nonnegative scalar multiplication preserves sequential weak lower semicontinuity. -/
theorem const_mul {E : V → ℝ} {S : Set V} (h : SeqWeakLowerSemicontinuousOn 𝕜 E S) {c : ℝ}
    (hc : 0 ≤ c) :
    SeqWeakLowerSemicontinuousOn 𝕜 (fun u ↦ c * E u) S := by
  intro u v hu hv hlim
  have hc' : (0 : EReal) ≤ (c : EReal) := EReal.coe_nonneg.2 hc
  calc ((c * E v : ℝ) : EReal)
      = (c : EReal) * (E v : EReal) := EReal.coe_mul c (E v)
    _ ≤ (c : EReal) * liminf (fun n ↦ (E (u n) : EReal)) atTop :=
        mul_le_mul_of_nonneg_left (h hu hv hlim) hc'
    _ = liminf (fun n ↦ (c : EReal) * (E (u n) : EReal)) atTop :=
        (EReal.liminf_const_mul_of_nonneg_of_ne_top hc' (EReal.coe_ne_top c)).symm
    _ = liminf (fun n ↦ ((c * E (u n) : ℝ) : EReal)) atTop := by
        simp only [EReal.coe_mul]

/-- The sum of two sequentially weakly lower semicontinuous energies on `S` is sequentially weakly
lower semicontinuous on `S`. -/
theorem add {E₁ E₂ : V → ℝ} {S : Set V} (h₁ : SeqWeakLowerSemicontinuousOn 𝕜 E₁ S)
    (h₂ : SeqWeakLowerSemicontinuousOn 𝕜 E₂ S) :
    SeqWeakLowerSemicontinuousOn 𝕜 (fun u ↦ E₁ u + E₂ u) S := by
  intro u v hu hv hlim
  calc ((E₁ v + E₂ v : ℝ) : EReal)
      = (E₁ v : EReal) + (E₂ v : EReal) := EReal.coe_add (E₁ v) (E₂ v)
    _ ≤ liminf (fun n ↦ (E₁ (u n) : EReal)) atTop +
          liminf (fun n ↦ (E₂ (u n) : EReal)) atTop :=
        add_le_add (h₁ hu hv hlim) (h₂ hu hv hlim)
    _ ≤ liminf (fun n ↦ (E₁ (u n) : EReal) + (E₂ (u n) : EReal)) atTop := EReal.le_liminf_add
    _ = liminf (fun n ↦ ((E₁ (u n) + E₂ (u n) : ℝ) : EReal)) atTop := by
        simp only [EReal.coe_add]

/-- A finite sum of sequentially weakly lower semicontinuous energies on `S` is sequentially weakly
lower semicontinuous on `S`. -/
theorem sum {ι : Type*} {t : Finset ι} {f : ι → V → ℝ} {S : Set V}
    (hf : ∀ i ∈ t, SeqWeakLowerSemicontinuousOn 𝕜 (f i) S) :
    SeqWeakLowerSemicontinuousOn 𝕜 (fun u ↦ ∑ i ∈ t, f i u) S := by
  classical
  induction t using Finset.induction_on with
  | empty =>
      simpa only [Finset.sum_empty] using seqWeakLowerSemicontinuousOn_const (𝕜 := 𝕜)
  | insert a s ha ih =>
      simp only [Finset.sum_insert ha]
      exact (hf a (Finset.mem_insert_self a s)).add
        (ih fun i hi ↦ hf i (Finset.mem_insert_of_mem hi))

end SeqWeakLowerSemicontinuousOn

/-- Topological weak lower semicontinuity on `S` implies sequential weak lower semicontinuity on
`S`. -/
theorem _root_.LowerSemicontinuousOn.seqWeakLowerSemicontinuousOn {E : V → ℝ} {S : Set V}
    (hlsc : LowerSemicontinuousOn
      (fun w : WeakSpace 𝕜 V ↦ E ((toWeakSpace 𝕜 V).symm w)) (toWeakSpace 𝕜 V '' S)) :
    SeqWeakLowerSemicontinuousOn 𝕜 E S := by
  intro u v hu hv hlim
  have hlsc' : LowerSemicontinuousOn
      (fun w : WeakSpace 𝕜 V ↦ (E ((toWeakSpace 𝕜 V).symm w) : EReal)) (toWeakSpace 𝕜 V '' S) :=
    continuous_coe_real_ereal.comp_lowerSemicontinuousOn hlsc EReal.coe_strictMono.monotone
  have hle := hlsc'.le_liminf_of_tendsto (mem_image_of_mem (toWeakSpace 𝕜 V) hv)
    (Eventually.of_forall fun n ↦ mem_image_of_mem (toWeakSpace 𝕜 V) (hu n)) hlim
  simpa only [Function.comp_def, LinearEquiv.symm_apply_apply] using hle

end WeakTopology

/-- **Equivalence of topological and sequential weak lower semicontinuity on weakly compact sets.**
If `K` is weakly compact in a real or complex normed space, topological weak lower semicontinuity
on `K` coincides with `SeqWeakLowerSemicontinuousOn 𝕜 E K`. -/
theorem lowerSemicontinuousOn_toWeakSpace_iff_seqWeakLowerSemicontinuousOn
    {𝕜 V : Type*} [RCLike 𝕜] [NormedAddCommGroup V] [NormedSpace 𝕜 V] {E : V → ℝ} {K : Set V}
    (hK : IsCompact (toWeakSpace 𝕜 V '' K)) :
    LowerSemicontinuousOn (fun w : WeakSpace 𝕜 V ↦ E ((toWeakSpace 𝕜 V).symm w))
      (toWeakSpace 𝕜 V '' K) ↔ SeqWeakLowerSemicontinuousOn 𝕜 E K := by
  refine ⟨LowerSemicontinuousOn.seqWeakLowerSemicontinuousOn, fun hseq ↦ ?_⟩
  let : FrechetUrysohnSpace (toWeakSpace 𝕜 V '' K) :=
    frechetUrysohnSpace_toWeakSpace_of_isCompact hK
  have hcoe : LowerSemicontinuousOn
      (fun w : WeakSpace 𝕜 V ↦ (E ((toWeakSpace 𝕜 V).symm w) : EReal))
      (toWeakSpace 𝕜 V '' K) := by
    rw [lowerSemicontinuousOn_iff_forall_seq_le_liminf]
    intro w z hw hz hlim
    choose u huK huw using hw
    obtain ⟨v, hvK, rfl⟩ := hz
    have hlim' : Tendsto (fun n ↦ toWeakSpace 𝕜 V (u n)) atTop (𝓝 (toWeakSpace 𝕜 V v)) := by
      simpa only [huw] using hlim
    simpa only [Function.comp_def, ← huw, LinearEquiv.symm_apply_apply] using hseq huK hvK hlim'
  intro w hw c hc
  filter_upwards [hcoe w hw (c : EReal) (EReal.coe_lt_coe_iff.2 hc)] with z hz
  exact EReal.coe_lt_coe_iff.1 hz

/-! ### Convex energies, norms, and linear perturbations -/

section ConvexAndNorms

variable {𝕜 V : Type*} [RCLike 𝕜]

/-- A real-quasiconvex norm-lower-semicontinuous energy on a subset `S` of a locally convex space
is sequentially weakly lower semicontinuous on `S`. -/
theorem _root_.QuasiconvexOn.seqWeakLowerSemicontinuousOn [AddCommGroup V] [Module 𝕜 V]
    [Module ℝ V] [IsScalarTower ℝ 𝕜 V] [TopologicalSpace V] [IsTopologicalAddGroup V]
    [ContinuousSMul 𝕜 V] [LocallyConvexSpace ℝ V] {S : Set V} {E : V → ℝ}
    (hf : QuasiconvexOn ℝ S E) (hlsc : LowerSemicontinuousOn E S) :
    SeqWeakLowerSemicontinuousOn 𝕜 E S :=
  (hf.lowerSemicontinuousOn_comp_toWeakSpace_symm hlsc).seqWeakLowerSemicontinuousOn

/-- If `E` is real-convex on `S` and lower semicontinuous within `S` at the single limit point `x`,
then along any sequence `u` in `S` converging weakly to `x` one has
`(E x : EReal) ≤ liminf (E ∘ u) atTop`. Neither lower semicontinuity elsewhere on `S` nor
membership `x ∈ S` is needed. -/
theorem _root_.ConvexOn.le_liminf_of_tendsto_toWeakSpace [SeminormedAddCommGroup V]
    [NormedSpace 𝕜 V] [NormedSpace ℝ V] [IsScalarTower ℝ 𝕜 V] {S : Set V} {E : V → ℝ}
    (hconv : ConvexOn ℝ S E) {x : V} (hlsc : LowerSemicontinuousWithinAt E S x)
    {u : ℕ → V} (hu : ∀ n, u n ∈ S)
    (hlim : Tendsto (fun n ↦ toWeakSpace 𝕜 V (u n)) atTop (𝓝 (toWeakSpace 𝕜 V x))) :
    (E x : EReal) ≤ liminf (fun n ↦ (E (u n) : EReal)) atTop := by
  by_contra! hlt
  -- Apply Mazur's lemma along a subsequence realizing the lower limit.
  obtain ⟨c, hlimc, hcx'⟩ := EReal.lt_iff_exists_real_btwn.1 hlt
  have hcx : c < E x := EReal.coe_lt_coe_iff.1 hcx'
  have hfreq : ∃ᶠ n in atTop, E (u n) < c := by
    simpa only [EReal.coe_lt_coe_iff] using (frequently_lt_of_liminf_lt) hlimc
  obtain ⟨φ, hφ, hEφ⟩ := extraction_of_frequently_atTop hfreq
  obtain ⟨s, w, hw, hsum, htend⟩ :=
    exists_tendsto_sum_smul_of_tendsto_weak (hlim.comp hφ.tendsto_atTop)
  set v : ℕ → V := fun n ↦ ∑ i ∈ s n, w n i • u (φ (n + i))
  have hvS (n : ℕ) : v n ∈ S :=
    hconv.1.sum_mem (hw n) (hsum n) fun i _ ↦ hu (φ (n + i))
  have hEv (n : ℕ) : E (v n) ≤ c := by
    calc E (v n) ≤ ∑ i ∈ s n, w n i • E (u (φ (n + i))) :=
          hconv.map_sum_le (hw n) (hsum n) fun i _ ↦ hu (φ (n + i))
      _ ≤ ∑ i ∈ s n, w n i * c := by
          refine Finset.sum_le_sum fun i hi ↦ ?_
          rw [smul_eq_mul]
          exact mul_le_mul_of_nonneg_left (hEφ (n + i)).le (hw n i hi)
      _ = c := by rw [← Finset.sum_mul, hsum n, one_mul]
  have hv_nhds : Tendsto v atTop (𝓝[S] x) :=
    tendsto_nhdsWithin_iff.2 ⟨htend, Eventually.of_forall hvS⟩
  obtain ⟨n, hn⟩ := (hv_nhds.eventually (hlsc c hcx)).exists
  exact hn.not_ge (hEv n)

section Seminormed

variable [SeminormedAddCommGroup V] [NormedSpace 𝕜 V]

/-- The norm on a real or complex seminormed space is weakly lower semicontinuous. -/
theorem lowerSemicontinuous_norm_comp_toWeakSpace_symm :
    LowerSemicontinuous fun w : WeakSpace 𝕜 V ↦ ‖(toWeakSpace 𝕜 V).symm w‖ := by
  let : NormedSpace ℝ V := NormedSpace.restrictScalars ℝ 𝕜 V
  let : IsScalarTower ℝ 𝕜 V := RestrictScalars.isScalarTower ℝ 𝕜 V
  have : LocallyConvexSpace ℝ V := NormedSpace.toLocallyConvexSpace' 𝕜
  exact (convexOn_univ_norm (E := V)).lowerSemicontinuous_comp_toWeakSpace_symm
    continuous_norm.lowerSemicontinuous

/-- For `0 ≤ p`, the norm power `u ↦ ‖u‖ ^ p` on a real or complex seminormed space is weakly
lower semicontinuous. -/
theorem lowerSemicontinuous_norm_rpow_comp_toWeakSpace_symm {p : ℝ} (hp : 0 ≤ p) :
    LowerSemicontinuous fun w : WeakSpace 𝕜 V ↦ ‖(toWeakSpace 𝕜 V).symm w‖ ^ p := by
  have h := ((Real.continuous_rpow_const hp).comp
    (continuous_id.max continuous_const)).comp_lowerSemicontinuous
      (lowerSemicontinuous_norm_comp_toWeakSpace_symm (𝕜 := 𝕜) (V := V))
      fun a b hab ↦ Real.rpow_le_rpow (le_max_right a 0) (max_le_max_right 0 hab) hp
  simpa only [Function.comp_def, id_eq, max_eq_left (norm_nonneg _)] using h

/-- For `n : ℕ`, the norm power `u ↦ ‖u‖ ^ n` on a real or complex seminormed space is weakly
lower semicontinuous. -/
theorem lowerSemicontinuous_norm_pow_comp_toWeakSpace_symm (n : ℕ) :
    LowerSemicontinuous fun w : WeakSpace 𝕜 V ↦ ‖(toWeakSpace 𝕜 V).symm w‖ ^ n := by
  convert lowerSemicontinuous_norm_rpow_comp_toWeakSpace_symm (𝕜 := 𝕜) (V := V)
    (Nat.cast_nonneg n) with w
  exact (Real.rpow_natCast _ n).symm

/-- For a continuous linear map `D : V →L[𝕜] F` and `0 ≤ p`, the operator energy `u ↦ ‖D u‖ ^ p` is
weakly lower semicontinuous on `V`. -/
theorem _root_.ContinuousLinearMap.lowerSemicontinuous_norm_rpow_comp_toWeakSpace_symm
    {F : Type*} [SeminormedAddCommGroup F] [NormedSpace 𝕜 F] (D : V →L[𝕜] F) {p : ℝ}
    (hp : 0 ≤ p) :
    LowerSemicontinuous fun w : WeakSpace 𝕜 V ↦ ‖D ((toWeakSpace 𝕜 V).symm w)‖ ^ p :=
  (TauCeti.lowerSemicontinuous_norm_rpow_comp_toWeakSpace_symm (𝕜 := 𝕜) (V := F) hp).comp
    (WeakSpace.map D).continuous

/-- For a continuous linear map `D : V →L[𝕜] F` and `n : ℕ`, the operator energy `u ↦ ‖D u‖ ^ n`
(in particular the quadratic energy `‖D u‖ ^ 2`) is weakly lower semicontinuous on `V`. -/
theorem _root_.ContinuousLinearMap.lowerSemicontinuous_norm_pow_comp_toWeakSpace_symm
    {F : Type*} [SeminormedAddCommGroup F] [NormedSpace 𝕜 F] (D : V →L[𝕜] F) (n : ℕ) :
    LowerSemicontinuous fun w : WeakSpace 𝕜 V ↦ ‖D ((toWeakSpace 𝕜 V).symm w)‖ ^ n :=
  (TauCeti.lowerSemicontinuous_norm_pow_comp_toWeakSpace_symm (𝕜 := 𝕜) (V := F) n).comp
    (WeakSpace.map D).continuous

/-- The real part of any continuous `𝕜`-linear functional on `V` is continuous for the weak
topology of `V`. -/
theorem _root_.StrongDual.continuous_re_comp_toWeakSpace_symm (ℓ : StrongDual 𝕜 V) :
    Continuous fun w : WeakSpace 𝕜 V ↦ RCLike.re (ℓ ((toWeakSpace 𝕜 V).symm w)) :=
  RCLike.continuous_re.comp (WeakBilin.eval_continuous (topDualPairing 𝕜 V).flip ℓ)

end Seminormed

end ConvexAndNorms

/-! ### Direct-method theorems and minimizing sequences -/

/-- If `S` is nonempty and `E '' S` is bounded below, there exists a minimizing sequence `u` in `S`
satisfying the quantitative bound `E (u n) < sInf (E '' S) + 1 / (n + 1)` and
`E (u n) → sInf (E '' S)`. -/
theorem exists_seq_forall_mem_and_lt_csInf_add_one_div {α : Type*} {E : α → ℝ} {S : Set α}
    (hS : S.Nonempty) (hbdd : BddBelow (E '' S)) :
    ∃ u : ℕ → α, (∀ n, u n ∈ S) ∧ (∀ n, E (u n) < sInf (E '' S) + 1 / ((n : ℝ) + 1)) ∧
      Tendsto (fun n ↦ E (u n)) atTop (𝓝 (sInf (E '' S))) :=
  exists_seq_forall_mem_and_lt_csInf_add hS hbdd (fun _ ↦ by positivity)
    tendsto_one_div_add_atTop_nhds_zero_nat

/-- Under `HasBoundedSublevelsOn E S`, every nonempty set `S` on which `E` is bounded below admits
a bounded minimizing sequence in `S` within `1 / (n + 1)` of `sInf (E '' S)`. -/
theorem HasBoundedSublevelsOn.exists_seq_tendsto_csInf {V : Type*} [Bornology V] {E : V → ℝ}
    {S : Set V} (h : HasBoundedSublevelsOn E S) (hS : S.Nonempty) (hbdd : BddBelow (E '' S)) :
    ∃ u : ℕ → V, (∀ n, u n ∈ S) ∧ IsBounded (range u) ∧
      (∀ n, E (u n) < sInf (E '' S) + 1 / ((n : ℝ) + 1)) ∧
      Tendsto (fun n ↦ E (u n)) atTop (𝓝 (sInf (E '' S))) := by
  obtain ⟨u, hu, hlt, htend⟩ := exists_seq_forall_mem_and_lt_csInf_add_one_div hS hbdd
  have hbdd_above : BddAbove (range (E ∘ u)) := by
    refine ⟨sInf (E '' S) + 1, forall_mem_range.2 fun n ↦ (hlt n).le.trans ?_⟩
    gcongr
    exact div_le_one_of_le₀ (by linarith [Nat.cast_nonneg (α := ℝ) n]) (by positivity)
  exact ⟨u, hu, h.isBounded_range_of_bddAbove hu hbdd_above, hlt, htend⟩

section TopologicalDirectMethod

variable {𝕜 V β : Type*} [NontriviallyNormedField 𝕜] [ProperSpace 𝕜]
  [SeminormedAddCommGroup V] [NormedSpace 𝕜 V] [LinearOrder β]

/-- **Topological direct method on a single bounded sublevel.** In a reflexive seminormed space
over a proper nontrivially normed field, if `S` is weakly closed, `E` is weakly lower
semicontinuous on `S`, and a single sublevel `{u ∈ S | E u ≤ b}` is nonempty and norm-bounded,
then `E` attains its minimum on `S`. -/
theorem exists_isMinOn_of_weak_closed_of_isBounded_sublevel {E : V → β} {S : Set V} {b : β}
    (hne : {u ∈ S | E u ≤ b}.Nonempty)
    (hreflexive : Surjective (inclusionInDoubleDual 𝕜 V))
    (hclosed : IsClosed (toWeakSpace 𝕜 V '' S))
    (hsub_bdd : IsBounded {u ∈ S | E u ≤ b})
    (hlsc : LowerSemicontinuousOn
      (fun w : WeakSpace 𝕜 V ↦ E ((toWeakSpace 𝕜 V).symm w)) (toWeakSpace 𝕜 V '' S)) :
    ∃ u ∈ S, IsMinOn E S u := by
  set g : WeakSpace 𝕜 V → β := fun w ↦ E ((toWeakSpace 𝕜 V).symm w)
  have hpre : (toWeakSpace 𝕜 V '' S) ∩ g ⁻¹' Iic b = toWeakSpace 𝕜 V '' {u ∈ S | E u ≤ b} := by
    dsimp only [g]
    rw [← Function.comp_def E, preimage_comp, ← (toWeakSpace 𝕜 V).image_eq_preimage_symm,
      ← image_inter (toWeakSpace 𝕜 V).injective]
    rfl
  have hsub_closed : IsClosed (toWeakSpace 𝕜 V '' {u ∈ S | E u ≤ b}) :=
    (lowerSemicontinuousOn_toWeakSpace_iff_isClosed_sublevel 𝕜 hclosed).1 hlsc b
  have hsub_compact : IsCompact ((toWeakSpace 𝕜 V '' S) ∩ g ⁻¹' Iic b) := by
    rw [hpre, ← hsub_closed.closure_eq]
    exact isCompact_closure_toWeakSpace hreflexive hsub_bdd
  have hne_weak : ((toWeakSpace 𝕜 V '' S) ∩ g ⁻¹' Iic b).Nonempty := by
    rw [hpre]
    exact hne.image (toWeakSpace 𝕜 V)
  obtain ⟨w, ⟨u, huS, rfl⟩, hmin⟩ :=
    hlsc.exists_isMinOn_of_isCompact_inter_preimage_Iic hne_weak hsub_compact
  refine ⟨u, huS, isMinOn_iff.2 fun v hvS ↦ ?_⟩
  simpa only [g, LinearEquiv.symm_apply_apply] using
    isMinOn_iff.1 hmin _ (mem_image_of_mem (toWeakSpace 𝕜 V) hvS)

/-- **The topological direct method.** On a reflexive seminormed space over a proper nontrivially
normed field (where reflexivity means surjectivity of `NormedSpace.inclusionInDoubleDual 𝕜 V`), an
energy that is weakly lower semicontinuous on a nonempty weakly closed set `S` with norm-bounded
sublevels attains its minimum on `S`. No a priori lower bound on the energy is assumed. -/
theorem exists_isMinOn_of_weak_closed (E : V → β) (S : Set V) (hne : S.Nonempty)
    (hreflexive : Surjective (inclusionInDoubleDual 𝕜 V))
    (hclosed : IsClosed (toWeakSpace 𝕜 V '' S))
    (hbounded_sublevels : HasBoundedSublevelsOn E S)
    (hlsc : LowerSemicontinuousOn
      (fun w : WeakSpace 𝕜 V ↦ E ((toWeakSpace 𝕜 V).symm w)) (toWeakSpace 𝕜 V '' S)) :
    ∃ u ∈ S, IsMinOn E S u := by
  obtain ⟨u₀, hu₀⟩ := hne
  exact exists_isMinOn_of_weak_closed_of_isBounded_sublevel ⟨u₀, hu₀, le_rfl⟩ hreflexive hclosed
    (hbounded_sublevels (E u₀)) hlsc

/-- Any norm-bounded set of minimizers of a weakly lower semicontinuous energy on a weakly closed
subset of a reflexive seminormed space is weakly compact. -/
theorem isCompact_toWeakSpace_setOf_isMinOn_of_isBounded {E : V → β} {S : Set V}
    (hreflexive : Surjective (inclusionInDoubleDual 𝕜 V))
    (hclosed : IsClosed (toWeakSpace 𝕜 V '' S))
    (hlsc : LowerSemicontinuousOn
      (fun w : WeakSpace 𝕜 V ↦ E ((toWeakSpace 𝕜 V).symm w)) (toWeakSpace 𝕜 V '' S))
    (hbdd : IsBounded {u ∈ S | IsMinOn E S u}) :
    IsCompact (toWeakSpace 𝕜 V '' {u ∈ S | IsMinOn E S u}) := by
  set g : WeakSpace 𝕜 V → β := fun w ↦ E ((toWeakSpace 𝕜 V).symm w)
  have himg : toWeakSpace 𝕜 V '' {u ∈ S | IsMinOn E S u} =
      {w ∈ toWeakSpace 𝕜 V '' S | IsMinOn g (toWeakSpace 𝕜 V '' S) w} := by
    ext w
    obtain ⟨u, rfl⟩ := (toWeakSpace 𝕜 V).surjective w
    simp only [(toWeakSpace 𝕜 V).injective.mem_set_image, mem_ofPred_eq, isMinOn_iff,
      forall_mem_image, g, LinearEquiv.symm_apply_apply]
  have hmin_closed : IsClosed (toWeakSpace 𝕜 V '' {u ∈ S | IsMinOn E S u}) := by
    rw [himg]
    exact hlsc.isClosed_setOf_isMinOn hclosed
  rw [← hmin_closed.closure_eq]
  exact isCompact_closure_toWeakSpace hreflexive hbdd

/-- When `E` has bounded sublevels on a weakly closed set `S` in a reflexive seminormed space and
is weakly lower semicontinuous on `S`, the set of minimizers `{u ∈ S | IsMinOn E S u}` is weakly
compact. -/
theorem HasBoundedSublevelsOn.isCompact_toWeakSpace_setOf_isMinOn {E : V → β} {S : Set V}
    (hbounded_sublevels : HasBoundedSublevelsOn E S)
    (hreflexive : Surjective (inclusionInDoubleDual 𝕜 V))
    (hclosed : IsClosed (toWeakSpace 𝕜 V '' S))
    (hlsc : LowerSemicontinuousOn
      (fun w : WeakSpace 𝕜 V ↦ E ((toWeakSpace 𝕜 V).symm w)) (toWeakSpace 𝕜 V '' S)) :
    IsCompact (toWeakSpace 𝕜 V '' {u ∈ S | IsMinOn E S u}) := by
  refine isCompact_toWeakSpace_setOf_isMinOn_of_isBounded hreflexive hclosed hlsc ?_
  rcases ({u ∈ S | IsMinOn E S u}).eq_empty_or_nonempty with hemp | ⟨u₀, hu₀, hmin⟩
  · exact hemp.symm ▸ isBounded_empty
  · rw [hmin.setOf_eq_inter_preimage_Iic hu₀]
    exact hbounded_sublevels (E u₀)

end TopologicalDirectMethod

/-- **Direct method for quasiconvex energies.** On a nonempty norm-closed real-convex subset `S` of
a reflexive real or complex seminormed space, any norm-lower-semicontinuous real-quasiconvex energy
with norm-bounded sublevels attains its minimum on `S`. -/
theorem _root_.QuasiconvexOn.exists_isMinOn {𝕜 V β : Type*} [RCLike 𝕜]
    [SeminormedAddCommGroup V] [NormedSpace 𝕜 V] [Module ℝ V] [IsScalarTower ℝ 𝕜 V]
    [LinearOrder β] {S : Set V} {E : V → β} (hf : QuasiconvexOn ℝ S E)
    (hS_conv : Convex ℝ S) (hS_closed : IsClosed S) (hne : S.Nonempty)
    (hreflexive : Surjective (inclusionInDoubleDual 𝕜 V))
    (hbounded_sublevels : HasBoundedSublevelsOn E S) (hlsc : LowerSemicontinuousOn E S) :
    ∃ u ∈ S, IsMinOn E S u := by
  have : LocallyConvexSpace ℝ V := NormedSpace.toLocallyConvexSpace' 𝕜
  exact exists_isMinOn_of_weak_closed E S hne hreflexive (hS_conv.isClosed_toWeakSpace 𝕜 hS_closed)
    hbounded_sublevels (hf.lowerSemicontinuousOn_comp_toWeakSpace_symm hlsc)

section SequentialDirectMethod

variable {𝕜 V : Type*} [RCLike 𝕜] [NormedAddCommGroup V] [NormedSpace 𝕜 V]

/-- **Subsequential weak convergence of bounded minimizing sequences.** In a reflexive real or
complex normed space, if `E` is bounded below on a sequentially weakly closed set `S` and
sequentially weakly lower semicontinuous on `S` along sequences with finite energy limits, then
every norm-bounded minimizing sequence `u` in `S` admits a subsequence converging weakly to a
minimizer `v ∈ S` of `E` on `S`. -/
theorem exists_subseq_tendsto_toWeakSpace_isMinOn (E : V → ℝ) (S : Set V)
    (hreflexive : Surjective (inclusionInDoubleDual 𝕜 V))
    (hbelow : BddBelow (E '' S))
    (hseqclosed : ∀ (u : ℕ → V) (v : V), (∀ n, u n ∈ S) →
      Tendsto (fun n ↦ toWeakSpace 𝕜 V (u n)) atTop (𝓝 (toWeakSpace 𝕜 V v)) → v ∈ S)
    (hseqlsc : ∀ (u : ℕ → V) (v : V) (r : ℝ), (∀ n, u n ∈ S) →
      Tendsto (fun n ↦ toWeakSpace 𝕜 V (u n)) atTop (𝓝 (toWeakSpace 𝕜 V v)) →
      Tendsto (fun n ↦ E (u n)) atTop (𝓝 r) → E v ≤ r)
    (u : ℕ → V) (hu : ∀ n, u n ∈ S) (hb : IsBounded (range u))
    (hminseq : Tendsto (fun n ↦ E (u n)) atTop (𝓝 (sInf (E '' S)))) :
    ∃ v ∈ S, ∃ φ : ℕ → ℕ, StrictMono φ ∧
      Tendsto (fun n ↦ toWeakSpace 𝕜 V (u (φ n))) atTop (𝓝 (toWeakSpace 𝕜 V v)) ∧
      IsMinOn E S v := by
  have hcpt : IsCompact (closure (toWeakSpace 𝕜 V '' range u)) :=
    isCompact_closure_toWeakSpace hreflexive hb
  obtain ⟨v, φ, hφ, hlim⟩ :=
    tendsto_subseq_toWeakSpace_of_isCompact_closure hcpt (fun n ↦ mem_range_self n)
  have hvS : v ∈ S := hseqclosed (fun n ↦ u (φ n)) v (fun n ↦ hu (φ n)) hlim
  have hEv_le : E v ≤ sInf (E '' S) :=
    hseqlsc (fun n ↦ u (φ n)) v (sInf (E '' S)) (fun n ↦ hu (φ n)) hlim
      (hminseq.comp hφ.tendsto_atTop)
  have hEv_eq : E v = sInf (E '' S) :=
    le_antisymm hEv_le (csInf_le hbelow (mem_image_of_mem E hvS))
  exact ⟨v, hvS, φ, hφ, hlim, (isMinOn_iff_eq_csInf hvS hbelow).2 hEv_eq⟩

/-- **The sequential direct method.** On a reflexive real or complex normed space, a real energy
bounded below on a sequentially weakly closed set `S`, sequentially weakly lower semicontinuous
there, attains its infimum as soon as one norm-bounded minimizing sequence exists. -/
theorem exists_isMinOn_of_bounded_minimizing_sequence (E : V → ℝ) (S : Set V)
    (hreflexive : Surjective (inclusionInDoubleDual 𝕜 V))
    (hbelow : BddBelow (E '' S))
    (hseqclosed : ∀ (u : ℕ → V) (v : V), (∀ n, u n ∈ S) →
      Tendsto (fun n ↦ toWeakSpace 𝕜 V (u n)) atTop (𝓝 (toWeakSpace 𝕜 V v)) → v ∈ S)
    (hseqlsc : ∀ (u : ℕ → V) (v : V) (r : ℝ), (∀ n, u n ∈ S) →
      Tendsto (fun n ↦ toWeakSpace 𝕜 V (u n)) atTop (𝓝 (toWeakSpace 𝕜 V v)) →
      Tendsto (fun n ↦ E (u n)) atTop (𝓝 r) → E v ≤ r)
    (u : ℕ → V) (hu : ∀ n, u n ∈ S) (hb : IsBounded (range u))
    (hminseq : Tendsto (fun n ↦ E (u n)) atTop (𝓝 (sInf (E '' S)))) :
    ∃ v ∈ S, IsMinOn E S v := by
  obtain ⟨v, hvS, -, -, -, hmin⟩ :=
    exists_subseq_tendsto_toWeakSpace_isMinOn E S hreflexive hbelow hseqclosed hseqlsc u hu hb
      hminseq
  exact ⟨v, hvS, hmin⟩

/-- **Full weak convergence under uniqueness.** When `v ∈ S` is the unique minimizer of `E` on `S`,
every norm-bounded minimizing sequence in `S` converges weakly to `v` without passing to a
subsequence. -/
theorem tendsto_toWeakSpace_of_unique_isMinOn {E : V → ℝ} {S : Set V}
    (hreflexive : Surjective (inclusionInDoubleDual 𝕜 V))
    (hbelow : BddBelow (E '' S))
    (hseqclosed : ∀ (u : ℕ → V) (w : V), (∀ n, u n ∈ S) →
      Tendsto (fun n ↦ toWeakSpace 𝕜 V (u n)) atTop (𝓝 (toWeakSpace 𝕜 V w)) → w ∈ S)
    (hseqlsc : ∀ (u : ℕ → V) (w : V) (r : ℝ), (∀ n, u n ∈ S) →
      Tendsto (fun n ↦ toWeakSpace 𝕜 V (u n)) atTop (𝓝 (toWeakSpace 𝕜 V w)) →
      Tendsto (fun n ↦ E (u n)) atTop (𝓝 r) → E w ≤ r)
    {v : V} (huniq : ∀ w ∈ S, IsMinOn E S w → w = v)
    {u : ℕ → V} (hu : ∀ n, u n ∈ S) (hb : IsBounded (range u))
    (hminseq : Tendsto (fun n ↦ E (u n)) atTop (𝓝 (sInf (E '' S)))) :
    Tendsto (fun n ↦ toWeakSpace 𝕜 V (u n)) atTop (𝓝 (toWeakSpace 𝕜 V v)) := by
  refine tendsto_of_subseq_tendsto fun ns hns ↦ ?_
  obtain ⟨ψ, -, hnsψ⟩ := strictMono_subseq_of_tendsto_atTop hns
  have hb' : IsBounded (range fun n ↦ u (ns (ψ n))) :=
    hb.subset (range_subset_iff.2 fun n ↦ mem_range_self (ns (ψ n)))
  obtain ⟨w, hwS, φ, -, hlim, hmin⟩ :=
    exists_subseq_tendsto_toWeakSpace_isMinOn E S hreflexive hbelow hseqclosed hseqlsc
      (fun n ↦ u (ns (ψ n))) (fun n ↦ hu (ns (ψ n))) hb' (hminseq.comp (hnsψ.tendsto_atTop))
  exact ⟨ψ ∘ φ, huniq w hwS hmin ▸ hlim⟩

/-- **Sublevel-local sequential direct method.** Sequential weak closedness and sequential weak
lower semicontinuity need only hold within a single bounded sublevel `S' = {w ∈ S | E w ≤ b}`
containing a minimizing sequence for `E` on `S`. -/
theorem exists_isMinOn_of_bounded_minimizing_sequence_sublevel (E : V → ℝ) (S : Set V) (b : ℝ)
    (hreflexive : Surjective (inclusionInDoubleDual 𝕜 V))
    (hbelow : BddBelow (E '' S))
    (hsub_bdd : IsBounded {w ∈ S | E w ≤ b})
    (hseqclosed : ∀ (u : ℕ → V) (v : V), (∀ n, u n ∈ S ∧ E (u n) ≤ b) →
      Tendsto (fun n ↦ toWeakSpace 𝕜 V (u n)) atTop (𝓝 (toWeakSpace 𝕜 V v)) →
      v ∈ S ∧ E v ≤ b)
    (hseqlsc : ∀ (u : ℕ → V) (v : V) (r : ℝ), (∀ n, u n ∈ S ∧ E (u n) ≤ b) →
      Tendsto (fun n ↦ toWeakSpace 𝕜 V (u n)) atTop (𝓝 (toWeakSpace 𝕜 V v)) →
      Tendsto (fun n ↦ E (u n)) atTop (𝓝 r) → E v ≤ r)
    (u : ℕ → V) (hu : ∀ n, u n ∈ S ∧ E (u n) ≤ b)
    (hminseq : Tendsto (fun n ↦ E (u n)) atTop (𝓝 (sInf (E '' S)))) :
    ∃ v ∈ S, IsMinOn E S v := by
  set S' : Set V := S ∩ E ⁻¹' Iic b
  have hbelow' : BddBelow (E '' S') := hbelow.mono (image_mono inter_subset_left)
  have hsInf_eq : sInf (E '' S') = sInf (E '' S) := by
    refine le_antisymm ?_ (csInf_le_csInf hbelow ⟨E (u 0), mem_image_of_mem E (hu 0)⟩
      (image_mono inter_subset_left))
    exact ge_of_tendsto' hminseq fun n ↦ csInf_le hbelow' (mem_image_of_mem E (hu n))
  have hb_range : IsBounded (range u) := hsub_bdd.subset (range_subset_iff.2 hu)
  obtain ⟨v, hvS', hmin'⟩ :=
    exists_isMinOn_of_bounded_minimizing_sequence E S' hreflexive hbelow' hseqclosed hseqlsc u hu
      hb_range (hsInf_eq.symm ▸ hminseq)
  exact ⟨v, hvS'.1, hmin'.of_inter_preimage_Iic ⟨u 0, hu 0⟩⟩

/-- If `S` is sequentially weakly closed in a reflexive normed space, `E` has bounded sublevels on
`S`, and `SeqWeakLowerSemicontinuousOn 𝕜 E S` holds, then `E '' S` is automatically bounded below
(including when `S = ∅`). -/
theorem SeqWeakLowerSemicontinuousOn.bddBelow_image {E : V → ℝ} {S : Set V}
    (hlsc : SeqWeakLowerSemicontinuousOn 𝕜 E S)
    (hreflexive : Surjective (inclusionInDoubleDual 𝕜 V))
    (hseqclosed : ∀ (u : ℕ → V) (v : V), (∀ n, u n ∈ S) →
      Tendsto (fun n ↦ toWeakSpace 𝕜 V (u n)) atTop (𝓝 (toWeakSpace 𝕜 V v)) → v ∈ S)
    (hbounded_sublevels : HasBoundedSublevelsOn E S) :
    BddBelow (E '' S) := by
  by_contra hnb
  have hex (n : ℕ) : ∃ u ∈ S, E u < -(n : ℝ) := by
    by_contra! hge
    exact hnb ⟨-(n : ℝ), forall_mem_image.2 hge⟩
  choose u huS hEu using hex
  have hu0 (n : ℕ) : E (u n) ≤ 0 :=
    (hEu n).le.trans (neg_nonpos.2 (Nat.cast_nonneg n))
  have hb : IsBounded (range u) :=
    (hbounded_sublevels 0).subset (range_subset_iff.2 fun n ↦ ⟨huS n, hu0 n⟩)
  obtain ⟨v, φ, hφ, hlim⟩ :=
    tendsto_subseq_toWeakSpace_of_isCompact_closure
      (isCompact_closure_toWeakSpace hreflexive hb) (fun n ↦ mem_range_self n)
  have hvS : v ∈ S := hseqclosed (fun n ↦ u (φ n)) v (fun n ↦ huS (φ n)) hlim
  have hbot : Tendsto (fun n ↦ (E (u (φ n)) : EReal)) atTop (𝓝 ⊥) := by
    rw [EReal.tendsto_nhds_bot_iff_real]
    intro x
    obtain ⟨N, hN⟩ := exists_nat_gt (-x)
    filter_upwards [eventually_ge_atTop N] with n hn
    rw [EReal.coe_lt_coe_iff]
    have hn_le : (N : ℝ) ≤ (φ n : ℝ) :=
      Nat.cast_le.2 (hn.trans (hφ.id_le n))
    linarith [hEu (φ n)]
  have hle : (E v : EReal) ≤ ⊥ :=
    (hlsc (fun n ↦ huS (φ n)) hvS hlim).trans_eq hbot.liminf_eq
  exact EReal.coe_ne_bot (E v) (le_bot_iff.1 hle)

/-- **Sequential direct method under `HasBoundedSublevelsOn` and `SeqWeakLowerSemicontinuousOn`.**
On a nonempty sequentially weakly closed set `S` in a reflexive real or complex normed space, any
energy with norm-bounded sublevels that is sequentially weakly lower semicontinuous on `S` is
bounded below on `S` and attains its minimum on `S`. -/
theorem SeqWeakLowerSemicontinuousOn.exists_isMinOn {E : V → ℝ} {S : Set V}
    (hlsc : SeqWeakLowerSemicontinuousOn 𝕜 E S) (hne : S.Nonempty)
    (hreflexive : Surjective (inclusionInDoubleDual 𝕜 V))
    (hseqclosed : ∀ (u : ℕ → V) (v : V), (∀ n, u n ∈ S) →
      Tendsto (fun n ↦ toWeakSpace 𝕜 V (u n)) atTop (𝓝 (toWeakSpace 𝕜 V v)) → v ∈ S)
    (hbounded_sublevels : HasBoundedSublevelsOn E S) :
    ∃ v ∈ S, IsMinOn E S v := by
  have hbelow : BddBelow (E '' S) :=
    hlsc.bddBelow_image hreflexive hseqclosed hbounded_sublevels
  obtain ⟨u, hu, hb, -, hminseq⟩ := hbounded_sublevels.exists_seq_tendsto_csInf hne hbelow
  exact exists_isMinOn_of_bounded_minimizing_sequence E S hreflexive hbelow hseqclosed
    (fun w z r hw hlim hEw ↦ hlsc.le_of_tendsto hw (hseqclosed w z hw hlim) hlim hEw)
    u hu hb hminseq

end SequentialDirectMethod

end TauCeti
