/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Group.Continuity
public import Mathlib.Analysis.Normed.Ring.Basic
public import TauCeti.Topology.ApproximateUnit
public import TauCeti.Topology.MetricSpace.SimultaneousApproximation
import Mathlib.Analysis.Normed.Ring.Lemmas

/-!
# Bounded approximate identities in normed rings

An approximate identity of a (possibly nonunital) normed ring `A` is recorded as a proper
filter `l` on `A`: it is a *left* approximate identity when `e * a → a` along `l` for every `a`,
a *right* one when `a * e → a`, and a two-sided one when `l.IsApproximateUnit`. It is
*bounded by* `C` when `‖e‖ ≤ C` eventually along `l`.

We prove:

* the finite-set criteria: `A` has a left, right or two-sided approximate identity bounded by
  `C` iff every finite subset of `A` is approximately fixed, to any accuracy, by a single
  element of norm at most `C`; equivalently, iff there is such an approximate identity in the
  form of a net indexed by `Finset A × ℕ`, all of whose terms have norm at most `C`;
* Dixon's combination: if `(e)` is a left approximate identity bounded by `C` and `(f)` a right
  one bounded by `D`, then `e + f - f * e` is a two-sided approximate identity bounded by
  `C + D + C * D`. In the unitization, `1 - (e + f - f * e) = (1 - f) * (1 - e)`;
* dense-set criteria: if a filter is eventually norm bounded and left- or right-approximates
  every element of a dense set, then it does so on the whole ring
  (`TauCeti.tendsto_mul_right_of_dense`, `TauCeti.tendsto_mul_left_of_dense`);
* transfer under continuous multiplicative maps with dense range, provided the image of the
  approximate unit is eventually norm bounded. This allows a bounded approximate unit of a
  dense subalgebra to serve in its completion;
* squaring an eventually bounded two-sided approximate identity gives another two-sided
  approximate identity (`Filter.IsApproximateUnit.map_mul_self`);
* `IsClosed.mem_of_tendsto_mul`: if an eventually norm-bounded filter of elements `e` is a
  two-sided approximate unit for `x` and `e * x * e` eventually lies in a closed set `s`, then
  `x ∈ s`.

## References

* H. G. Dales, *Banach Algebras and Automatic Continuity*, §2.9.
* P. G. Dixon, *Approximate identities in normed algebras*,
  Proc. London Math. Soc. (3) 26 (1973), 485–496.
-/

public section

open Filter Topology

namespace TauCeti

variable {A : Type*} [NonUnitalSeminormedRing A] {C D : ℝ}

/-! ### Finite-set and net criteria -/

/-- A normed ring has a left approximate identity bounded by `C` iff every finite set of
elements is approximately fixed under left multiplication, to any accuracy, by a single element
of norm at most `C`. -/
theorem exists_tendsto_mul_right_iff_forall_finset :
    (∃ l : Filter A, l.NeBot ∧ (∀ᶠ e in l, ‖e‖ ≤ C) ∧ ∀ a, Tendsto (· * a) l (𝓝 a)) ↔
      ∀ s : Finset A, ∀ ε > 0, ∃ e, ‖e‖ ≤ C ∧ ∀ a ∈ s, ‖e * a - a‖ < ε := by
  simpa [dist_eq_norm] using
    exists_neBot_tendsto_iff_forall_finset_dist_lt (p := fun e : A ↦ ‖e‖ ≤ C)
      (F := fun a e ↦ e * a) (x := id)

/-- A normed ring has a right approximate identity bounded by `C` iff every finite set of
elements is approximately fixed under right multiplication, to any accuracy, by a single
element of norm at most `C`. -/
theorem exists_tendsto_mul_left_iff_forall_finset :
    (∃ l : Filter A, l.NeBot ∧ (∀ᶠ e in l, ‖e‖ ≤ C) ∧ ∀ a, Tendsto (a * ·) l (𝓝 a)) ↔
      ∀ s : Finset A, ∀ ε > 0, ∃ e, ‖e‖ ≤ C ∧ ∀ a ∈ s, ‖a * e - a‖ < ε := by
  simpa [dist_eq_norm] using
    exists_neBot_tendsto_iff_forall_finset_dist_lt (p := fun e : A ↦ ‖e‖ ≤ C)
      (F := fun a e ↦ a * e) (x := id)

/-- A normed ring has a two-sided approximate identity bounded by `C` iff every finite set of
elements is approximately fixed under both left and right multiplication, to any accuracy, by a
single element of norm at most `C`. -/
theorem exists_isApproximateUnit_iff_forall_finset :
    (∃ l : Filter A, l.IsApproximateUnit ∧ ∀ᶠ e in l, ‖e‖ ≤ C) ↔
      ∀ s : Finset A, ∀ ε > 0, ∃ e, ‖e‖ ≤ C ∧ ∀ a ∈ s, ‖e * a - a‖ < ε ∧ ‖a * e - a‖ < ε := by
  simp only [IsApproximateUnit.iff_neBot_and_tendsto_prod, and_assoc]
  refine (exists_congr fun _ ↦ and_congr_right fun _ ↦ and_comm).trans ?_
  simpa [Prod.dist_eq, dist_eq_norm] using
    exists_neBot_tendsto_iff_forall_finset_dist_lt (p := fun e : A ↦ ‖e‖ ≤ C)
      (F := fun a e ↦ (e * a, a * e)) (x := fun a ↦ (a, a))

/-- A normed ring has a left approximate identity bounded by `C` iff it has one in the form of
a net, indexed by `Finset A × ℕ`, all of whose terms have norm at most `C`. -/
theorem exists_tendsto_mul_right_iff_exists_net :
    (∃ l : Filter A, l.NeBot ∧ (∀ᶠ e in l, ‖e‖ ≤ C) ∧ ∀ a, Tendsto (· * a) l (𝓝 a)) ↔
      ∃ e : Finset A × ℕ → A, (∀ i, ‖e i‖ ≤ C) ∧
        ∀ a, Tendsto (fun i ↦ e i * a) atTop (𝓝 a) :=
  exists_neBot_tendsto_iff_exists_net (p := fun e : A ↦ ‖e‖ ≤ C)
    (F := fun a e ↦ e * a) (x := id)

/-- A normed ring has a right approximate identity bounded by `C` iff it has one in the form of
a net, indexed by `Finset A × ℕ`, all of whose terms have norm at most `C`. -/
theorem exists_tendsto_mul_left_iff_exists_net :
    (∃ l : Filter A, l.NeBot ∧ (∀ᶠ e in l, ‖e‖ ≤ C) ∧ ∀ a, Tendsto (a * ·) l (𝓝 a)) ↔
      ∃ e : Finset A × ℕ → A, (∀ i, ‖e i‖ ≤ C) ∧
        ∀ a, Tendsto (fun i ↦ a * e i) atTop (𝓝 a) :=
  exists_neBot_tendsto_iff_exists_net (p := fun e : A ↦ ‖e‖ ≤ C)
    (F := fun a e ↦ a * e) (x := id)

/-- A normed ring has a two-sided approximate identity bounded by `C` iff it has one in the form
of a net, indexed by `Finset A × ℕ`, all of whose terms have norm at most `C`. -/
theorem exists_isApproximateUnit_iff_exists_net :
    (∃ l : Filter A, l.IsApproximateUnit ∧ ∀ᶠ e in l, ‖e‖ ≤ C) ↔
      ∃ e : Finset A × ℕ → A, (∀ i, ‖e i‖ ≤ C) ∧ (map e atTop).IsApproximateUnit := by
  classical
  simp only [IsApproximateUnit.iff_neBot_and_tendsto_prod, and_assoc]
  refine (exists_congr fun _ ↦ and_congr_right fun _ ↦ and_comm).trans ?_
  simpa [IsApproximateUnit.iff_neBot_and_tendsto_prod, tendsto_map'_iff, Function.comp_def,
    atTop_neBot.map] using
    exists_neBot_tendsto_iff_exists_net (p := fun e : A ↦ ‖e‖ ≤ C)
      (F := fun a e ↦ (e * a, a * e)) (x := fun a ↦ (a, a))

/-! ### Combining one-sided approximate identities -/

/-- The norm of Dixon's combination `e + f - f * e` of two elements. -/
theorem norm_add_sub_mul_le (e f : A) : ‖e + f - f * e‖ ≤ ‖e‖ + ‖f‖ + ‖e‖ * ‖f‖ :=
  (norm_sub_le _ _).trans <| add_le_add (norm_add_le _ _) <|
    (norm_mul_le f e).trans_eq (mul_comm _ _)

/-- How far Dixon's combination `u = e + f - f * e` is from fixing `a` under left
multiplication: it is at most `1 + ‖f‖` times the left error `‖e * a - a‖`, since
`u * a - a = (e * a - a) - f * (e * a - a)`. -/
theorem norm_add_sub_mul_mul_sub_le (e f a : A) :
    ‖(e + f - f * e) * a - a‖ ≤ (1 + ‖f‖) * ‖e * a - a‖ := by
  have : (e + f - f * e) * a - a = (e * a - a) - f * (e * a - a) := by
    simp only [add_mul, sub_mul, mul_sub, mul_assoc]
    abel
  rw [this, add_mul, one_mul]
  exact (norm_sub_le _ _).trans (by gcongr; exact norm_mul_le _ _)

/-- How far Dixon's combination `u = e + f - f * e` is from fixing `a` under right
multiplication: it is at most `1 + ‖e‖` times the right error `‖a * f - a‖`, since
`a * u - a = (a * f - a) - (a * f - a) * e`. -/
theorem norm_mul_add_sub_mul_sub_le (e f a : A) :
    ‖a * (e + f - f * e) - a‖ ≤ (1 + ‖e‖) * ‖a * f - a‖ := by
  have : a * (e + f - f * e) - a = (a * f - a) - (a * f - a) * e := by
    simp only [mul_add, mul_sub, sub_mul, mul_assoc]
    abel
  rw [this, add_mul, one_mul, mul_comm ‖e‖]
  exact (norm_sub_le _ _).trans (by gcongr; exact norm_mul_le _ _)

variable {l₁ l₂ : Filter A}

/-- If `e` is eventually bounded by `C` along `l₁` and `f` by `D` along `l₂`, then Dixon's
combination `e + f - f * e` is eventually bounded by `C + D + C * D`. -/
theorem eventually_norm_add_sub_mul_le (hC : ∀ᶠ e in l₁, ‖e‖ ≤ C) (hD : ∀ᶠ f in l₂, ‖f‖ ≤ D) :
    ∀ᶠ p in l₁ ×ˢ l₂, ‖p.1 + p.2 - p.2 * p.1‖ ≤ C + D + C * D := by
  filter_upwards [hC.prod_mk hD] with ⟨e, f⟩ ⟨he, hf⟩
  exact (norm_add_sub_mul_le e f).trans <| add_le_add (add_le_add he hf) <|
    mul_le_mul he hf (norm_nonneg f) ((norm_nonneg e).trans he)

/-- If `e * a → a` along `l₁` and `l₂` is eventually bounded, then Dixon's combination
`u = e + f - f * e` satisfies `u * a → a` along `l₁ ×ˢ l₂`. -/
theorem tendsto_add_sub_mul_mul {a : A} (h₁ : Tendsto (· * a) l₁ (𝓝 a))
    (hD : ∀ᶠ f in l₂, ‖f‖ ≤ D) :
    Tendsto (fun p : A × A ↦ (p.1 + p.2 - p.2 * p.1) * a) (l₁ ×ˢ l₂) (𝓝 a) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have h : Tendsto (fun p : A × A ↦ (1 + D) * ‖p.1 * a - a‖) (l₁ ×ˢ l₂) (𝓝 0) := by
    simpa using ((tendsto_iff_norm_sub_tendsto_zero.1 h₁).comp tendsto_fst).const_mul (1 + D)
  refine squeeze_zero' (.of_forall fun _ ↦ norm_nonneg _) ?_ h
  filter_upwards [tendsto_snd.eventually hD] with ⟨e, f⟩ hf
  exact (norm_add_sub_mul_mul_sub_le e f a).trans (by gcongr)

/-- If `a * f → a` along `l₂` and `l₁` is eventually bounded, then Dixon's combination
`u = e + f - f * e` satisfies `a * u → a` along `l₁ ×ˢ l₂`. -/
theorem tendsto_mul_add_sub_mul {a : A} (h₂ : Tendsto (a * ·) l₂ (𝓝 a))
    (hC : ∀ᶠ e in l₁, ‖e‖ ≤ C) :
    Tendsto (fun p : A × A ↦ a * (p.1 + p.2 - p.2 * p.1)) (l₁ ×ˢ l₂) (𝓝 a) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have h : Tendsto (fun p : A × A ↦ (1 + C) * ‖a * p.2 - a‖) (l₁ ×ˢ l₂) (𝓝 0) := by
    simpa using ((tendsto_iff_norm_sub_tendsto_zero.1 h₂).comp tendsto_snd).const_mul (1 + C)
  refine squeeze_zero' (.of_forall fun _ ↦ norm_nonneg _) ?_ h
  filter_upwards [tendsto_fst.eventually hC] with ⟨e, f⟩ he
  exact (norm_mul_add_sub_mul_sub_le e f a).trans (by gcongr)

/-- **Dixon's combination.** If `l₁` is a left approximate identity and `l₂` a right
approximate identity, both eventually bounded, then the image of `l₁ ×ˢ l₂` under
`(e, f) ↦ e + f - f * e` is a two-sided approximate identity. -/
theorem isApproximateUnit_map_add_sub_mul [l₁.NeBot] [l₂.NeBot]
    (h₁ : ∀ a, Tendsto (· * a) l₁ (𝓝 a)) (hC : ∀ᶠ e in l₁, ‖e‖ ≤ C)
    (h₂ : ∀ a, Tendsto (a * ·) l₂ (𝓝 a)) (hD : ∀ᶠ f in l₂, ‖f‖ ≤ D) :
    (map (fun p : A × A ↦ p.1 + p.2 - p.2 * p.1) (l₁ ×ˢ l₂)).IsApproximateUnit where
  tendsto_mul_left a := tendsto_map'_iff.2 (tendsto_mul_add_sub_mul (h₂ a) hC)
  tendsto_mul_right a := tendsto_map'_iff.2 (tendsto_add_sub_mul_mul (h₁ a) hD)

/-- A normed ring with a left approximate identity bounded by `C` and a right approximate
identity bounded by `D` has a two-sided approximate identity bounded by `C + D + C * D`. -/
theorem exists_isApproximateUnit_of_left_of_right
    (h₁ : ∃ l : Filter A, l.NeBot ∧ (∀ᶠ e in l, ‖e‖ ≤ C) ∧ ∀ a, Tendsto (· * a) l (𝓝 a))
    (h₂ : ∃ l : Filter A, l.NeBot ∧ (∀ᶠ f in l, ‖f‖ ≤ D) ∧ ∀ a, Tendsto (a * ·) l (𝓝 a)) :
    ∃ l : Filter A, l.IsApproximateUnit ∧ ∀ᶠ u in l, ‖u‖ ≤ C + D + C * D := by
  obtain ⟨l₁, _, hC, h₁⟩ := h₁
  obtain ⟨l₂, _, hD, h₂⟩ := h₂
  exact ⟨_, isApproximateUnit_map_add_sub_mul h₁ hC h₂ hD,
    eventually_map.2 (eventually_norm_add_sub_mul_le hC hD)⟩

/-- If `l` is eventually norm-bounded in a nonunital seminormed ring `A` and `e * x → x` along `l`
for every `x` in a dense set `s`, then `e * a → a` along `l` for every `a : A`. -/
theorem tendsto_mul_right_of_dense {l : Filter A} (hC : ∀ᶠ e in l, ‖e‖ ≤ C)
    {s : Set A} (hs : Dense s) (h : ∀ x ∈ s, Tendsto (· * x) l (𝓝 x)) (a : A) :
    Tendsto (· * a) l (𝓝 a) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  let M : ℝ := max C 0
  have hM0 : 0 ≤ M := le_max_right C 0
  let δ : ℝ := ε / (2 * (M + 1))
  have hδ : 0 < δ := by positivity
  obtain ⟨x, hxball, hxs⟩ := Metric.dense_iff.mp hs a δ hδ
  have hax : ‖a - x‖ < δ := by
    rw [Metric.mem_ball, dist_comm, dist_eq_norm] at hxball
    exact hxball
  have hxa : ‖x - a‖ < δ := by rwa [norm_sub_rev]
  have hx_ev := Metric.tendsto_nhds.mp (h x hxs) (ε / 2) (half_pos hε)
  have hMδ : (M + 1) * δ = ε / 2 := by
    dsimp only [δ]
    field_simp
  filter_upwards [hC, hx_ev] with e he hxe
  rw [dist_eq_norm] at hxe ⊢
  have heM : ‖e‖ ≤ M := he.trans (le_max_left C 0)
  have hdecomp : e * a - a = e * (a - x) + (e * x - x) + (x - a) := by
    simp only [mul_sub]
    abel
  have hle : ‖e * a - a‖ ≤ ‖e‖ * ‖a - x‖ + ‖e * x - x‖ + ‖x - a‖ := by
    rw [hdecomp]
    exact norm_add₃_le.trans (by gcongr; exact norm_mul_le _ _)
  have hprod : ‖e‖ * ‖a - x‖ ≤ M * δ :=
    mul_le_mul heM hax.le (norm_nonneg _) hM0
  linarith

/-- If `l` is eventually norm-bounded in a nonunital seminormed ring `A` and `x * e → x` along `l`
for every `x` in a dense set `s`, then `a * e → a` along `l` for every `a : A`. -/
theorem tendsto_mul_left_of_dense {l : Filter A} (hC : ∀ᶠ e in l, ‖e‖ ≤ C)
    {s : Set A} (hs : Dense s) (h : ∀ x ∈ s, Tendsto (x * ·) l (𝓝 x)) (a : A) :
    Tendsto (a * ·) l (𝓝 a) := by
  have hdense : Dense (MulOpposite.op '' s) :=
    MulOpposite.op_surjective.denseRange.dense_image MulOpposite.continuous_op hs
  have hop : Tendsto (· * MulOpposite.op a) (l.map MulOpposite.op) (𝓝 (MulOpposite.op a)) :=
    tendsto_mul_right_of_dense (A := Aᵐᵒᵖ) (l := l.map MulOpposite.op)
      (eventually_map.mpr <| hC.mono fun _ he => by simpa [MulOpposite.norm_op] using he) hdense
      (fun _ ⟨x, hxs, hx⟩ => by
        subst hx
        rw [tendsto_map'_iff]
        simpa only [Function.comp_def, ← MulOpposite.op_mul] using
          (MulOpposite.continuous_op.tendsto x).comp (h x hxs))
      (MulOpposite.op a)
  simpa only [Function.comp_def, ← MulOpposite.op_mul, MulOpposite.unop_op] using
    (MulOpposite.continuous_unop.tendsto (MulOpposite.op a)).comp (tendsto_map'_iff.mp hop)

/-- If `u` is eventually norm bounded along `l`, `u i * a → a`, and `a * v i → a`, then the
two-sided products `u i * a * v i` tend to `a`. -/
theorem tendsto_mul_mul_of_isBoundedUnder {ι : Type*} {l : Filter ι} {u v : ι → A} {a : A}
    (hu : l.IsBoundedUnder (· ≤ ·) (norm ∘ u))
    (hleft : Tendsto (fun i => u i * a) l (𝓝 a))
    (hright : Tendsto (fun i => a * v i) l (𝓝 a)) :
    Tendsto (fun i => u i * a * v i) l (𝓝 a) := by
  have hzero : Tendsto (fun i => u i * (a * v i - a)) l (𝓝 0) :=
    Filter.isBoundedUnder_le_mul_tendsto_zero hu (by simpa using hright.sub_const a)
  simpa only [mul_sub, ← mul_assoc, sub_add_cancel, zero_add] using hzero.add hleft

end TauCeti

namespace Filter.IsApproximateUnit

variable {A B F : Type*} [TopologicalSpace A] [Mul A] [NonUnitalSeminormedRing B]
  [FunLike F A B] [MulHomClass F A B]

/-- A continuous multiplicative map with dense range carries an approximate unit to an
approximate unit of a seminormed ring, provided its image is eventually norm bounded. No norm
or additive structure on the source is needed, and the target need not be complete. -/
theorem map_of_denseRange {l : Filter A} (hl : l.IsApproximateUnit) (f : F)
    (hf : Continuous f) (hd : DenseRange f) {C : ℝ} (hC : ∀ᶠ e in l, ‖f e‖ ≤ C) :
    (l.map f).IsApproximateUnit where
  tendsto_mul_left :=
    TauCeti.tendsto_mul_left_of_dense (eventually_map.mpr hC) hd fun _ ⟨a, ha⟩ => by
      rw [← ha, tendsto_map'_iff]
      simpa only [Function.comp_def, ← map_mul] using (hf.tendsto a).comp (hl.tendsto_mul_left a)
  tendsto_mul_right :=
    TauCeti.tendsto_mul_right_of_dense (eventually_map.mpr hC) hd fun _ ⟨a, ha⟩ => by
      rw [← ha, tendsto_map'_iff]
      simpa only [Function.comp_def, ← map_mul] using (hf.tendsto a).comp (hl.tendsto_mul_right a)
  neBot := hl.neBot.map f

/-- Squaring an eventually bounded two-sided approximate identity of a seminormed ring produces
another two-sided approximate identity. -/
theorem map_mul_self {A : Type*} [NonUnitalSeminormedRing A] {l : Filter A}
    (hl : l.IsApproximateUnit) {C : ℝ} (hC : ∀ᶠ e in l, ‖e‖ ≤ C) :
    (l.map fun e ↦ e * e).IsApproximateUnit where
  tendsto_mul_left a := by
    refine tendsto_map'_iff.2 (tendsto_iff_norm_sub_tendsto_zero.2 ?_)
    have h0 : Tendsto (fun e : A ↦ ‖a * e - a‖ * C + ‖a * e - a‖) l (𝓝 0) := by
      simpa using ((tendsto_iff_norm_sub_tendsto_zero.1 (hl.tendsto_mul_left a)).mul_const C).add
        (tendsto_iff_norm_sub_tendsto_zero.1 (hl.tendsto_mul_left a))
    refine squeeze_zero' (.of_forall fun _ ↦ norm_nonneg _) ?_ h0
    filter_upwards [hC] with e he
    have hsub : a * (e * e) - a = (a * e - a) * e + (a * e - a) := by
      simp only [sub_mul, mul_assoc]
      abel
    rw [Function.comp_apply, hsub]
    exact (norm_add_le _ _).trans <| add_le_add
      ((norm_mul_le _ _).trans (mul_le_mul_of_nonneg_left he (norm_nonneg _))) le_rfl
  tendsto_mul_right a := by
    refine tendsto_map'_iff.2 (tendsto_iff_norm_sub_tendsto_zero.2 ?_)
    have h0 : Tendsto (fun e : A ↦ C * ‖e * a - a‖ + ‖e * a - a‖) l (𝓝 0) := by
      simpa using ((tendsto_iff_norm_sub_tendsto_zero.1 (hl.tendsto_mul_right a)).const_mul C).add
        (tendsto_iff_norm_sub_tendsto_zero.1 (hl.tendsto_mul_right a))
    refine squeeze_zero' (.of_forall fun _ ↦ norm_nonneg _) ?_ h0
    filter_upwards [hC] with e he
    have hsub : e * e * a - a = e * (e * a - a) + (e * a - a) := by
      simp only [mul_sub, mul_assoc]
      abel
    rw [Function.comp_apply, hsub]
    exact (norm_add_le _ _).trans <| add_le_add
      ((norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right he (norm_nonneg _))) le_rfl
  neBot := have := hl.neBot; inferInstance

end Filter.IsApproximateUnit

namespace IsClosed

variable {A : Type*} [NonUnitalSeminormedRing A]

/-- If `x * e → x` and `e * x → x` along a proper filter of eventually norm-bounded `e` with
`e * x * e` eventually in a closed set `s`, then `x ∈ s`. -/
theorem mem_of_tendsto_mul {s : Set A} {x : A} (hs : IsClosed s) {l : Filter A} [l.NeBot]
    (hmem : ∀ᶠ e in l, e * x * e ∈ s) (hbdd : IsBoundedUnder (· ≤ ·) l (‖·‖))
    (hr : Tendsto (x * ·) l (𝓝 x)) (hl : Tendsto (· * x) l (𝓝 x)) : x ∈ s :=
  hs.mem_of_tendsto (TauCeti.tendsto_mul_mul_of_isBoundedUnder (u := id) (v := id) hbdd hl hr) hmem

end IsClosed
