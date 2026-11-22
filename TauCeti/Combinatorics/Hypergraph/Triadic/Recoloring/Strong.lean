/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Hypergraph.Colored.EditDiscrepancy
public import TauCeti.Combinatorics.Hypergraph.Triadic.StrongTopRegularization

import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import TauCeti.Combinatorics.Hypergraph.Triadic.Recoloring.Coupled
import TauCeti.Data.Nat.Factorial.Basic

/-!
# Strong top-regular approximation

Combining strong top regularization (`Colored3Graph.exists_strong_topRegularOverMostPolyads`) with
coupled triple recoloring
(`Colored3Graph.TopRegularOverMostPolyads.exists_approximates3_of_polyadEnergy_sub_le`) and rank
amplification (`Colored3Graph.TopRegularOverMostPolyads.of_rank_one_div_pow`) yields the scheduled
coupled recoloring step at `recoloringHostBound`
(`Colored3Graph.TopRegularOverMostPolyads.exists_approximates3_of_recoloringHostBound_le`) and the
full scheduled strong top-regular approximation theorem
(`Colored3Graph.exists_approximates3_topRegularOverMostPolyads`):

For any edit budget `ε > 0`, positive schedules `δ μ : ℕ → ℝ`, and rank schedule `r : ℕ → ℕ`, every
lower skeleton `S` on any finite vertex set `V` admits a palette refinement `C` with
`C.pairColorCount ≤ topRegularApproximationPaletteBound ...` and an `ε`-close coloring `H'` that
is `(δ C.complexity, r C.complexity)`-top-regular off a `μ C.complexity`-proportion of the
injective triples. Small hosts are handled by a discrete palette refinement giving every ordered
distinct pair its own color.

## Main definitions

* `TauCeti.recoloringTolerance`: fine rank-one tolerance required for scheduled recoloring.
* `TauCeti.recoloringMass`: fine exceptional proportion required for scheduled recoloring.
* `TauCeti.recoloringHostBound`: host size threshold above which scheduled coupled recoloring runs.
* `TauCeti.topRegularApproximationPaletteBound`: host-independent bound on `C.pairColorCount`.

## Main results

* `TauCeti.Colored3Graph.TopRegularOverMostPolyads.exists_approximates3_of_recoloringHostBound_le`:
  scheduled coupled recoloring across a polyad energy gap on a host of size at least
  `recoloringHostBound`.
* `TauCeti.Colored3Graph.exists_approximates3_topRegularOverMostPolyads`: scheduled strong
  top-regular approximation over any lower skeleton on any finite vertex set.

## References

* V. Rödl and M. Schacht, *Regular partitions of hypergraphs: regularity lemmas*,
  Combin. Probab. Comput. 16 (2007), the regular approximation lemma.
* N. Alon, E. Fischer, M. Krivelevich and M. Szegedy, *Efficient testing of large graphs*,
  Combinatorica 20 (2000), the strong regularity lemma.
-/

public section

open Finset

namespace TauCeti

section Helpers

private theorem mul_add_le_of_div_two_add_one (q : ℕ) {a x y : ℝ} (ha : 0 ≤ a)
    (hx : x = a / (2 * ((q : ℝ) + 1))) (hy : y ≤ x) : (q : ℝ) * (x + y) ≤ a := by
  calc (q : ℝ) * (x + y) ≤ (q : ℝ) * (2 * x) :=
        mul_le_mul_of_nonneg_left (by linarith) (Nat.cast_nonneg q)
    _ ≤ a := by rw [hx, ← mul_assoc, mul_div_assoc', div_le_iff₀ (by positivity)]; nlinarith

private theorem small_polyad_mass_le {v q cardD : ℕ} {P β μ' : ℝ}
    (hv4 : 4 ≤ v) (hDP : (cardD : ℝ) ≤ P) (hP : 0 ≤ P) (hβ : 0 < β) (hμ' : 0 < μ')
    (hv_real : 4 * P * 221 * ((q : ℝ) + 10) / (β ^ 2 * μ') < v) :
    (cardD : ℝ) * (221 * (3 * (v : ℝ) ^ 2 + q + 7) / β ^ 2) / v.descFactorial 3 ≤ μ' := by
  have hv_desc : v ^ 3 ≤ 4 * v.descFactorial 3 :=
    Nat.pow_le_mul_descFactorial (by norm_num) (by
      have : 4 * Nat.choose 3 2 = 12 := by decide
      omega)
  have hv_desc_pos : (0 : ℝ) < v.descFactorial 3 := by
    have : 0 < v.descFactorial 3 := by
      have := (pow_pos (by omega : 0 < v) 3).trans_le hv_desc; omega
    exact_mod_cast this
  have hN₀_le : 221 * (3 * (v : ℝ) ^ 2 + q + 7) / β ^ 2 ≤
      221 * ((q : ℝ) + 10) * (v : ℝ) ^ 2 / β ^ 2 := by
    refine div_le_div_of_nonneg_right ?_ (sq_nonneg _)
    have hv1 : (1 : ℝ) ≤ (v : ℝ) ^ 2 := by exact_mod_cast (by nlinarith : 1 ≤ v ^ 2)
    have hqv : (q : ℝ) ≤ q * (v : ℝ) ^ 2 := le_mul_of_one_le_right (Nat.cast_nonneg q) hv1
    linarith
  have hv_mul : 4 * P * 221 * ((q : ℝ) + 10) ≤ (v : ℝ) * (β ^ 2 * μ') :=
    ((div_lt_iff₀ (mul_pos (pow_pos hβ 2) hμ')).1 hv_real).le
  rw [div_le_iff₀ hv_desc_pos]
  calc (cardD : ℝ) * (221 * (3 * (v : ℝ) ^ 2 + q + 7) / β ^ 2)
      ≤ P * (221 * ((q : ℝ) + 10) * (v : ℝ) ^ 2 / β ^ 2) :=
        mul_le_mul hDP hN₀_le (by positivity) hP
    _ = (4 * P * 221 * ((q : ℝ) + 10)) * ((v : ℝ) ^ 2 / (4 * β ^ 2)) := by field_simp [hβ.ne']
    _ ≤ ((v : ℝ) * (β ^ 2 * μ')) * ((v : ℝ) ^ 2 / (4 * β ^ 2)) :=
        mul_le_mul_of_nonneg_right hv_mul (by positivity)
    _ = μ' * ((v : ℝ) ^ 3 / 4) := by field_simp [hβ.ne']
    _ ≤ μ' * v.descFactorial 3 := by
        have hv_descR : (v : ℝ) ^ 3 ≤ 4 * (v.descFactorial 3 : ℝ) := by exact_mod_cast hv_desc
        exact mul_le_mul_of_nonneg_left (by linarith) hμ'.le

end Helpers

/-! ### Explicit bounds for scheduled top-regular approximation -/

/-- The fine tolerance in scheduled coupled recoloring: to reach `(δ n, r n)`-top regularity over
a coarse complex of complexity `n` for a palette of `q` top colors, a fine palette refinement is
required to be rank-one top-regular at this tolerance. -/
noncomputable def recoloringTolerance (q : ℕ) (δ : ℕ → ℝ) (r : ℕ → ℕ) (n : ℕ) : ℝ :=
  ((δ n) ^ 2 / (2 : ℝ) ^ r n) ^ 2 / (8 * ((q : ℝ) + 1))

/-- Unfolding lemma for `recoloringTolerance`. -/
theorem recoloringTolerance_def (q : ℕ) (δ : ℕ → ℝ) (r : ℕ → ℕ) (n : ℕ) :
    recoloringTolerance q δ r n = ((δ n) ^ 2 / (2 : ℝ) ^ r n) ^ 2 / (8 * ((q : ℝ) + 1)) :=
  (rfl)

/-- The fine tolerance is positive wherever the coarse tolerance is. -/
theorem recoloringTolerance_pos (q : ℕ) {δ : ℕ → ℝ} (r : ℕ → ℕ) {n : ℕ} (hδ : 0 < δ n) :
    0 < recoloringTolerance q δ r n := by
  rw [recoloringTolerance_def]
  positivity

/-- The fine exceptional proportion in scheduled coupled recoloring: to reach an exceptional
proportion `μ n` over a coarse complex of complexity `n`, a fine palette refinement is required
to be top-regular off this proportion. -/
noncomputable def recoloringMass (δ μ : ℕ → ℝ) (r : ℕ → ℕ) (n : ℕ) : ℝ :=
  μ n * (((δ n) ^ 2 / (2 : ℝ) ^ r n) ^ 2 / 4) / 2

/-- Unfolding lemma for `recoloringMass`. -/
theorem recoloringMass_def (δ μ : ℕ → ℝ) (r : ℕ → ℕ) (n : ℕ) :
    recoloringMass δ μ r n = μ n * (((δ n) ^ 2 / (2 : ℝ) ^ r n) ^ 2 / 4) / 2 :=
  (rfl)

/-- The fine exceptional proportion is positive wherever the coarse tolerance and exceptional
proportion are. -/
theorem recoloringMass_pos {δ μ : ℕ → ℝ} (r : ℕ → ℕ) {n : ℕ} (hδ : 0 < δ n) (hμ : 0 < μ n) :
    0 < recoloringMass δ μ r n := by
  rw [recoloringMass_def]
  positivity

/-- The host size required by scheduled coupled recoloring with edit budget `ε`, over a coarse
complex of complexity at most `K` whose fine palette refinement has at most `P` polyads: each fine
polyad with fewer triples than the Hoeffding support bound is left unrecolored, and on such a
host these polyads carry a negligible proportion of the triples. -/
noncomputable def recoloringHostBound (q : ℕ) (ε : ℝ) (δ μ : ℕ → ℝ) (r : ℕ → ℕ) (K P : ℕ) :
    ℕ :=
  max 4 ((range (K + 1)).sup fun n ↦
    ⌊4 * (P : ℝ) * 221 * ((q : ℝ) + 10) /
      ((min (ε / (2 * ((q : ℝ) + 1))) (recoloringTolerance q δ r n)) ^ 2 *
        recoloringMass δ μ r n)⌋₊ + 1)

/-- Unfolding lemma for `recoloringHostBound`. -/
theorem recoloringHostBound_def (q : ℕ) (ε : ℝ) (δ μ : ℕ → ℝ) (r : ℕ → ℕ) (K P : ℕ) :
    recoloringHostBound q ε δ μ r K P =
      max 4 ((range (K + 1)).sup fun n ↦
        ⌊4 * (P : ℝ) * 221 * ((q : ℝ) + 10) /
          ((min (ε / (2 * ((q : ℝ) + 1))) (recoloringTolerance q δ r n)) ^ 2 *
            recoloringMass δ μ r n)⌋₊ + 1) :=
  (rfl)

/-- Host-independent upper bound on `C.pairColorCount` in
`Colored3Graph.exists_approximates3_topRegularOverMostPolyads`, for top palette size `q`, `t`
vertex cells, `m` initial pair colors, edit budget `ε`, positive schedules `δ` and `μ`, and rank
schedule `r`. The square of the host bound absorbs the discrete palette refinement on small
hosts. -/
noncomputable def topRegularApproximationPaletteBound (q t : ℕ) (ε : ℝ) (δ μ : ℕ → ℝ)
    (r : ℕ → ℕ) (m : ℕ) : ℕ :=
  let M := strongTopRegularityBound t ((ε / (2 * ((q : ℝ) + 1))) ^ 2) (recoloringTolerance q δ r)
    (recoloringMass δ μ r) (fun _ ↦ 1) m
  let M' := strongTopRegularityStep t (recoloringTolerance q δ r) (recoloringMass δ μ r)
    (fun _ ↦ 1) M
  max M (recoloringHostBound q ε δ μ r (t + M + t ^ 3 * M ^ 3) (t ^ 3 * M' ^ 3) ^ 2)

/-- Unfolding lemma for `topRegularApproximationPaletteBound`. -/
theorem topRegularApproximationPaletteBound_def (q t : ℕ) (ε : ℝ) (δ μ : ℕ → ℝ) (r : ℕ → ℕ)
    (m : ℕ) :
    topRegularApproximationPaletteBound q t ε δ μ r m =
      let M := strongTopRegularityBound t ((ε / (2 * ((q : ℝ) + 1))) ^ 2)
        (recoloringTolerance q δ r) (recoloringMass δ μ r) (fun _ ↦ 1) m
      let M' := strongTopRegularityStep t (recoloringTolerance q δ r) (recoloringMass δ μ r)
        (fun _ ↦ 1) M
      max M (recoloringHostBound q ε δ μ r (t + M + t ^ 3 * M ^ 3) (t ^ 3 * M' ^ 3) ^ 2) :=
  (rfl)

namespace Colored3Graph

variable {κ κ₂ V : Type*} [Fintype V] [DecidableEq V] [DecidableEq κ]

/-- **Scheduled coupled recoloring across a small polyad energy gap.** Let `D` refine `C` along a
pair-color projection `f` recovering `C.skeleton.pairColors.color`, with both complexes selecting
polyad decompositions, let `n = C.complexity`, and let `ε`, `δ n` and `μ n` be positive. Suppose
that `H` is rank-one top-regular over all polyads of `D` at tolerance `recoloringTolerance q δ r n`
outside a `recoloringMass δ μ r n`-proportion of the injective triples, where `q` is the number of
top colors, and that the polyad energy gap from `C` to `D` is at most `(ε / (2 (q + 1)))²`. On a
host of size at least `recoloringHostBound q ε δ μ r K P`, where `n ≤ K` and `D` has at most `P`
polyads, there is a coloring `H'` within edit discrepancy `ε` of `H` that is
`(δ n, r n)`-top-regular over `C` outside a `μ n`-proportion of the injective triples. -/
theorem TopRegularOverMostPolyads.exists_approximates3_of_recoloringHostBound_le [Fintype κ]
    {H : Colored3Graph κ V} {C D : TriadicComplex3 V} {ε : ℝ} {δ μ : ℕ → ℝ} {r : ℕ → ℕ}
    (h : H.TopRegularOverMostPolyads D (recoloringTolerance (Fintype.card κ) δ r C.complexity)
      (recoloringMass δ μ r C.complexity) 1)
    (hC : C.IsPolyadDecomposition) (hD : D.IsPolyadDecomposition)
    (hV : D.skeleton.vertexPart ≤ C.skeleton.vertexPart)
    (f : Fin D.pairColorCount → Fin C.pairColorCount)
    (hf : ∀ p, C.skeleton.pairColors.color p = f (D.skeleton.pairColors.color p))
    (hgap : H.polyadEnergy D.skeleton - H.polyadEnergy C.skeleton ≤
      (ε / (2 * ((Fintype.card κ : ℝ) + 1))) ^ 2)
    (hε : 0 < ε) (hδ : 0 < δ C.complexity) (hμ : 0 < μ C.complexity) {K P : ℕ}
    (hK : C.complexity ≤ K) (hP : Fintype.card (Polyad3 D.skeleton) ≤ P)
    (hcard : recoloringHostBound (Fintype.card κ) ε δ μ r K P ≤ Fintype.card V) :
    ∃ H' : Colored3Graph κ V, H.Approximates3 H' ε ∧
      H'.TopRegularOverMostPolyads C (δ C.complexity) (μ C.complexity) (r C.complexity) := by
  set q := Fintype.card κ
  set n := C.complexity
  set γ : ℝ := ε / (2 * ((q : ℝ) + 1))
  set δ₁ : ℝ := (δ n) ^ 2 / (2 : ℝ) ^ r n
  set θ : ℝ := δ₁ ^ 2 / 4
  set β : ℝ := min γ (recoloringTolerance q δ r n)
  have hγ : 0 < γ := by positivity
  have hδ₁ : 0 < δ₁ := by positivity
  have hθ : 0 < θ := by positivity
  have hη : 0 < recoloringTolerance q δ r n := recoloringTolerance_pos q r hδ
  have hμ' : 0 < recoloringMass δ μ r n := recoloringMass_pos r hδ hμ
  have hβ : 0 < β := lt_min hγ hη
  -- The host is large enough for the Hoeffding support bound at complexity `n ≤ K`.
  rw [recoloringHostBound_def] at hcard
  have hv4 : 4 ≤ Fintype.card V := (le_max_left _ _).trans hcard
  have hv_sup : ⌊4 * (P : ℝ) * 221 * ((q : ℝ) + 10) / (β ^ 2 * recoloringMass δ μ r n)⌋₊ + 1 ≤
      Fintype.card V :=
    (le_sup (f := fun k ↦ ⌊4 * (P : ℝ) * 221 * ((q : ℝ) + 10) /
      ((min γ (recoloringTolerance q δ r k)) ^ 2 * recoloringMass δ μ r k)⌋₊ + 1)
      (mem_range.2 (Nat.lt_succ_of_le hK))).trans ((le_max_right _ _).trans hcard)
  have hv_real : 4 * (P : ℝ) * 221 * ((q : ℝ) + 10) / (β ^ 2 * recoloringMass δ μ r n) <
      Fintype.card V :=
    (Nat.lt_floor_add_one _).trans_le (by exact_mod_cast hv_sup)
  set N₀ : ℝ := 221 * (3 * (Fintype.card V : ℝ) ^ 2 + q + 7) / β ^ 2
  have hN₀ : 221 * (3 * (Fintype.card V : ℝ) ^ 2 + q + 7) ≤ β ^ 2 * N₀ := by
    rw [mul_div_cancel₀ _ (pow_ne_zero 2 hβ.ne')]
  have htol : 2 * ((q : ℝ) * (recoloringTolerance q δ r n + β) + θ) ≤ δ₁ ^ 2 := by
    have hqη : (q : ℝ) * (recoloringTolerance q δ r n + β) ≤ δ₁ ^ 2 / 4 :=
      mul_add_le_of_div_two_add_one q (by positivity)
        (by rw [recoloringTolerance_def, div_div]; congr 1; ring) (min_le_right _ _)
    dsimp only [θ]
    linarith
  -- Recolor at rank one, then amplify the rank.
  obtain ⟨H', happrox, hreg₁⟩ :=
    h.exists_approximates3_of_polyadEnergy_sub_le hC hD hV f hf hgap hη.le hδ₁ hβ hθ hN₀ htol
  refine ⟨H', happrox.mono ?_, (hreg₁.mono le_rfl ?_ le_rfl).of_rank_one_div_pow hδ⟩
  · rw [Real.sqrt_sq hγ.le]
    exact mul_add_le_of_div_two_add_one q hε.le rfl (min_le_left _ _)
  · have hsmall := small_polyad_mass_le hv4 (by exact_mod_cast hP) (Nat.cast_nonneg _) hβ hμ'
      hv_real
    rw [div_le_iff₀ hθ]
    have : recoloringMass δ μ r n + recoloringMass δ μ r n = μ n * θ := by
      rw [recoloringMass_def]; ring
    linarith

/-- Discrete palette refinement: giving every ordered distinct pair its own pair color yields a
triadic complex over `S.vertexPart` with at most `|V|²` pair colors whose polyads each have
support cardinality at most `1`, so every coloring is top-regular over every polyad. -/
private theorem exists_discrete_topRegularOverMostPolyads
    (H : Colored3Graph κ V) (S : PairSkeleton3 κ₂ V) {δ μ : ℕ → ℝ}
    (hδ : ∀ n, 0 < δ n) (hμ : ∀ n, 0 < μ n) (r : ℕ → ℕ) :
    ∃ (C : TriadicComplex3 V) (π : Fin C.pairColorCount → κ₂),
      C.pairColorCount ≤ Fintype.card V ^ 2 ∧
      C.skeleton.vertexPart = S.vertexPart ∧
      (∀ p, π (C.skeleton.pairColors.color p) = S.pairColors.color p) ∧
      (∀ c, π (C.skeleton.pairColors.rev c) = S.pairColors.rev (π c)) ∧
      C.polyads = univ ∧
      H.TopRegularOverMostPolyads C (δ C.complexity) (μ C.complexity) (r C.complexity) := by
  let discrete : PairColorSystem {p : V × V // p.1 ≠ p.2} V :=
    ⟨id, fun p ↦ ⟨p.val.swap, p.property.symm⟩, fun ⟨⟨_, _⟩, _⟩ ↦ rfl, fun _ ↦ rfl⟩
  let e := Fintype.equivFin {p : V × V // p.1 ≠ p.2}
  let C : TriadicComplex3 V :=
    ⟨Fintype.card {p : V × V // p.1 ≠ p.2}, ⟨S.vertexPart, discrete.relabel e⟩, univ⟩
  let π : Fin C.pairColorCount → κ₂ := fun c ↦ S.pairColors.color (e.symm c)
  refine ⟨C, π, (Fintype.card_subtype_le _).trans_eq (by rw [Fintype.card_prod, sq]), rfl,
    fun p ↦ by simp [C, π, discrete], fun c ↦ by simp [C, π, discrete, S.pairColors.color_rev],
    rfl, topRegularOverMostPolyads_of_forall (fun P _ ↦ ?_) (hμ C.complexity).le⟩
  refine H.isTopRegularOverPolyad_of_card_support_le_one P (r C.complexity) ?_ (hδ C.complexity)
  refine card_le_one.2 fun x hx y hy ↦ Subtype.ext <| funext fun i ↦ ?_
  have h₀₁ : coordPair x 0 1 (by decide) = coordPair y 0 1 (by decide) :=
    e.injective (by
      have h1 := ((P.mem_pairSupport₀₁ _).1 (coordPair_mem_pairSupport₀₁ hx)).2.2
      have h2 := ((P.mem_pairSupport₀₁ _).1 (coordPair_mem_pairSupport₀₁ hy)).2.2
      simpa [C, discrete] using h1.trans h2.symm)
  have h₀₂ : coordPair x 0 2 (by decide) = coordPair y 0 2 (by decide) :=
    e.injective (by
      have h1 := ((P.mem_pairSupport₀₂ _).1 (coordPair_mem_pairSupport₀₂ hx)).2.2
      have h2 := ((P.mem_pairSupport₀₂ _).1 (coordPair_mem_pairSupport₀₂ hy)).2.2
      simpa [C, discrete] using h1.trans h2.symm)
  have h₀₁' := congrArg (fun p : {p : V × V // p.1 ≠ p.2} ↦ (p : V × V)) h₀₁
  have h₀₂' := congrArg (fun p : {p : V × V // p.1 ≠ p.2} ↦ (p : V × V)) h₀₂
  simp only [coe_coordPair, Prod.mk.injEq] at h₀₁' h₀₂'
  match i with
  | ⟨0, _⟩ => exact h₀₁'.1
  | ⟨1, _⟩ => exact h₀₁'.2
  | ⟨2, _⟩ => exact h₀₂'.2

/-- **Scheduled strong top-regular approximation.** Let `ε > 0`, let `δ μ : ℕ → ℝ` be positive
schedules, and let `r : ℕ → ℕ` be a rank schedule. On every finite vertex set `V`, every lower
skeleton `S` admits a palette refinement `C` with the vertex cells of `S`, all its polyads, and
`C.pairColorCount` bounded independently of `V` by
`topRegularApproximationPaletteBound (Nat.card κ) #S.vertexPart.parts ε δ μ r (Fintype.card κ₂)`,
together with an `ε`-close coloring `H'` that is `(δ C.complexity, r C.complexity)`-top-regular
off a `μ C.complexity`-proportion of the injective triples. -/
theorem exists_approximates3_topRegularOverMostPolyads [Finite κ] [Fintype κ₂]
    (H : Colored3Graph κ V) (S : PairSkeleton3 κ₂ V) {ε : ℝ} (hε : 0 < ε)
    {δ μ : ℕ → ℝ} (hδ : ∀ n, 0 < δ n) (hμ : ∀ n, 0 < μ n) (r : ℕ → ℕ) :
    ∃ (C : TriadicComplex3 V) (π : Fin C.pairColorCount → κ₂) (H' : Colored3Graph κ V),
      C.pairColorCount ≤ topRegularApproximationPaletteBound (Nat.card κ)
        #S.vertexPart.parts ε δ μ r (Fintype.card κ₂) ∧
      C.skeleton.vertexPart = S.vertexPart ∧
      (∀ p, π (C.skeleton.pairColors.color p) = S.pairColors.color p) ∧
      (∀ c, π (C.skeleton.pairColors.rev c) = S.pairColors.rev (π c)) ∧
      C.polyads = univ ∧
      H.Approximates3 H' ε ∧
      H'.TopRegularOverMostPolyads C (δ C.complexity) (μ C.complexity) (r C.complexity) := by
  have := Fintype.ofFinite κ
  rw [Nat.card_eq_fintype_card]
  set q := Fintype.card κ
  set t := #S.vertexPart.parts
  set η := recoloringTolerance q δ r
  set μ' := recoloringMass δ μ r
  set γ : ℝ := ε / (2 * ((q : ℝ) + 1))
  set M := strongTopRegularityBound t (γ ^ 2) η μ' (fun _ ↦ 1) (Fintype.card κ₂)
  set M' := strongTopRegularityStep t η μ' (fun _ ↦ 1) M
  set N := recoloringHostBound q ε δ μ r (t + M + t ^ 3 * M ^ 3) (t ^ 3 * M' ^ 3)
  have hbound : topRegularApproximationPaletteBound q t ε δ μ r (Fintype.card κ₂) =
      max M (N ^ 2) := by
    rw [topRegularApproximationPaletteBound_def]
  rw [hbound]
  by_cases hcard : N ≤ Fintype.card V
  · obtain ⟨C, D, π, f, hCcard, hDcard, hCV, hDV, hπ, hrev, hf, -, hCpol, hDpol, hDreg, hgap⟩ :=
      H.exists_strong_topRegularOverMostPolyads S (g := γ ^ 2) (η := η) (μ := μ')
        (by positivity) (fun n ↦ recoloringTolerance_pos q r (hδ n))
        (fun n ↦ recoloringMass_pos r (hδ n) (hμ n)) (fun _ ↦ 1)
    have hCcomp : C.complexity ≤ t + M + t ^ 3 * M ^ 3 :=
      C.complexity_le.trans (by rw [hCV]; gcongr)
    have hDM' : D.pairColorCount ≤ M' :=
      hDcard.trans (topRegularRefinementBound_le_strongTopRegularityStep η μ' (fun _ ↦ 1) hCcard
        hCcomp)
    have hDpoly : Fintype.card (Polyad3 D.skeleton) ≤ t ^ 3 * M' ^ 3 :=
      (card_polyad3_le D.skeleton).trans (by rw [hDV, Fintype.card_fin]; gcongr)
    obtain ⟨H', happrox, hreg⟩ := hDreg.exists_approximates3_of_recoloringHostBound_le
      (C.isPolyadDecomposition_of_polyads_eq_univ hCpol)
      (D.isPolyadDecomposition_of_polyads_eq_univ hDpol) (hDV.trans hCV.symm).le f
      (fun p ↦ (hf p).symm) hgap hε (hδ _) (hμ _) hCcomp hDpoly hcard
    exact ⟨C, π, H', hCcard.trans (le_max_left _ _), hCV, hπ, hrev, hCpol, happrox, hreg⟩
  · obtain ⟨C, π, hCcard, hCV, hπ, hrev, hCpol, hreg⟩ :=
      exists_discrete_topRegularOverMostPolyads H S hδ hμ r
    refine ⟨C, π, H, (hCcard.trans (Nat.pow_le_pow_left (not_le.1 hcard).le 2)).trans
      (le_max_right _ _), hCV, hπ, hrev, hCpol, H.approximates3_self hε.le, hreg⟩

end Colored3Graph

end TauCeti
