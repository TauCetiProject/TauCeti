/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Group.Continuity
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Topology.ApproximateUnit
public import TauCeti.Topology.MetricSpace.SimultaneousApproximation

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
  `C + D + C * D`. In the unitization, `1 - (e + f - f * e) = (1 - f) * (1 - e)`.

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

/-- The two one-sided convergences of an approximate unit, as one convergence in `A × A`; this
lets the two-sided criteria below be read off from the single-family ones. -/
private theorem isApproximateUnit_iff_tendsto_prod {l : Filter A} :
    l.IsApproximateUnit ↔
      l.NeBot ∧ ∀ a, Tendsto (fun e ↦ (e * a, a * e)) l (𝓝 (a, a)) := by
  simp only [nhds_prod_eq, tendsto_prod_iff']
  exact ⟨fun h ↦ ⟨h.neBot, fun a ↦ ⟨h.tendsto_mul_right a, h.tendsto_mul_left a⟩⟩,
    fun ⟨_, h⟩ ↦ ⟨fun a ↦ (h a).2, fun a ↦ (h a).1⟩⟩

/-- A normed ring has a two-sided approximate identity bounded by `C` iff every finite set of
elements is approximately fixed under both left and right multiplication, to any accuracy, by a
single element of norm at most `C`. -/
theorem exists_isApproximateUnit_iff_forall_finset :
    (∃ l : Filter A, l.IsApproximateUnit ∧ ∀ᶠ e in l, ‖e‖ ≤ C) ↔
      ∀ s : Finset A, ∀ ε > 0, ∃ e, ‖e‖ ≤ C ∧ ∀ a ∈ s, ‖e * a - a‖ < ε ∧ ‖a * e - a‖ < ε := by
  simp only [isApproximateUnit_iff_tendsto_prod, and_assoc]
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
  simp only [isApproximateUnit_iff_tendsto_prod, and_assoc]
  refine (exists_congr fun _ ↦ and_congr_right fun _ ↦ and_comm).trans ?_
  simpa [isApproximateUnit_iff_tendsto_prod, tendsto_map'_iff, Function.comp_def,
    atTop_neBot.map] using
    exists_neBot_tendsto_iff_exists_net (p := fun e : A ↦ ‖e‖ ≤ C)
      (F := fun a e ↦ (e * a, a * e)) (x := fun a ↦ (a, a))

/-! ### Combining one-sided approximate identities -/

/-- The norm of Dixon's combination `e + f - f * e` of two elements. -/
theorem norm_add_sub_mul_le (e f : A) : ‖e + f - f * e‖ ≤ ‖e‖ + ‖f‖ + ‖e‖ * ‖f‖ :=
  (norm_sub_le _ _).trans <| add_le_add (norm_add_le _ _) <|
    (norm_mul_le f e).trans_eq (mul_comm _ _)

/-- How far Dixon's combination `u = e + f - f * e` is from fixing `a` under left
multiplication, controlled by `e` alone: `u * a - a = (e * a - a) - f * (e * a - a)`. -/
theorem norm_add_sub_mul_mul_sub_le (e f a : A) :
    ‖(e + f - f * e) * a - a‖ ≤ (1 + ‖f‖) * ‖e * a - a‖ := by
  have : (e + f - f * e) * a - a = (e * a - a) - f * (e * a - a) := by
    simp only [add_mul, sub_mul, mul_sub, mul_assoc]
    abel
  rw [this, add_mul, one_mul]
  exact (norm_sub_le _ _).trans (by gcongr; exact norm_mul_le _ _)

/-- How far Dixon's combination `u = e + f - f * e` is from fixing `a` under right
multiplication, controlled by `f` alone: `a * u - a = (a * f - a) - (a * f - a) * e`. -/
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

/-- If `l₁` is a left approximate identity and `l₂` is eventually bounded, then Dixon's
combination `e + f - f * e` is a left approximate identity along `l₁ ×ˢ l₂`. -/
theorem tendsto_add_sub_mul_mul (h₁ : ∀ a, Tendsto (· * a) l₁ (𝓝 a))
    (hD : ∀ᶠ f in l₂, ‖f‖ ≤ D) (a : A) :
    Tendsto (fun p : A × A ↦ (p.1 + p.2 - p.2 * p.1) * a) (l₁ ×ˢ l₂) (𝓝 a) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have h : Tendsto (fun p : A × A ↦ (1 + D) * ‖p.1 * a - a‖) (l₁ ×ˢ l₂) (𝓝 0) := by
    simpa using ((tendsto_iff_norm_sub_tendsto_zero.1 (h₁ a)).comp tendsto_fst).const_mul (1 + D)
  refine squeeze_zero' (.of_forall fun _ ↦ norm_nonneg _) ?_ h
  filter_upwards [tendsto_snd.eventually hD] with ⟨e, f⟩ hf
  exact (norm_add_sub_mul_mul_sub_le e f a).trans (by gcongr)

/-- If `l₂` is a right approximate identity and `l₁` is eventually bounded, then Dixon's
combination `e + f - f * e` is a right approximate identity along `l₁ ×ˢ l₂`. -/
theorem tendsto_mul_add_sub_mul (h₂ : ∀ a, Tendsto (a * ·) l₂ (𝓝 a))
    (hC : ∀ᶠ e in l₁, ‖e‖ ≤ C) (a : A) :
    Tendsto (fun p : A × A ↦ a * (p.1 + p.2 - p.2 * p.1)) (l₁ ×ˢ l₂) (𝓝 a) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have h : Tendsto (fun p : A × A ↦ (1 + C) * ‖a * p.2 - a‖) (l₁ ×ˢ l₂) (𝓝 0) := by
    simpa using ((tendsto_iff_norm_sub_tendsto_zero.1 (h₂ a)).comp tendsto_snd).const_mul (1 + C)
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
  tendsto_mul_left a := tendsto_map'_iff.2 (tendsto_mul_add_sub_mul h₂ hC a)
  tendsto_mul_right a := tendsto_map'_iff.2 (tendsto_add_sub_mul_mul h₁ hD a)

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

end TauCeti
