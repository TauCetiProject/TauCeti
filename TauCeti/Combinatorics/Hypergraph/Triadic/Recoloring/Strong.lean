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

/-!
# Strong top-regular approximation

Combining strong top regularization (`Colored3Graph.exists_strong_topRegularOverMostPolyads`) with
coupled triple recoloring
(`Colored3Graph.TopRegularOverMostPolyads.exists_approximates3_of_polyadEnergy_sub_le`) and rank
amplification (`Colored3Graph.TopRegularOverMostPolyads.of_rank_one_div_pow`) yields the full
scheduled strong top-regular approximation theorem
(`Colored3Graph.exists_approximates3_topRegularOverMostPolyads`):

For any edit budget `ε > 0`, positive schedules `δ μ : ℕ → ℝ`, and rank schedule `r : ℕ → ℕ`, every
lower skeleton `S` on any finite vertex set `V` admits a palette refinement `C` with
`C.pairColorCount ≤ topRegularApproximationPaletteBound ...` and an `ε`-close coloring `H'` that
is `(δ C.complexity, r C.complexity)`-top-regular off a `μ C.complexity`-proportion of the
injective triples. Small hosts are handled by a discrete palette refinement giving every ordered
distinct pair its own color.

## Main definitions

* `TauCeti.topRegularApproximationPaletteBound`: host-independent bound on `C.pairColorCount`.

## Main results

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
  have hv_desc : v ^ 3 ≤ 4 * v.descFactorial 3 := by
    rw [Nat.descFactorial_succ, Nat.descFactorial_succ, Nat.descFactorial_one]
    have h1 : v ≤ 2 * (v - 1) := by omega
    have h2 : v ≤ 2 * (v - 2) := by omega
    calc v ^ 3 = v * (v * v) := by ring
      _ ≤ v * ((2 * (v - 1)) * (2 * (v - 2))) := Nat.mul_le_mul_left v (Nat.mul_le_mul h1 h2)
      _ = 4 * ((v - 2) * ((v - 1) * v)) := by ring
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

/-! ### Explicit bound for scheduled top-regular approximation -/

/-- Host-independent upper bound on `C.pairColorCount` in
`Colored3Graph.exists_approximates3_topRegularOverMostPolyads`, for top palette size `q`, `t`
vertex cells, `m` initial pair colors, edit budget `ε`, positive schedules `δ` and `μ`, and rank
schedule `r`. The maximum with `N²` absorbs the discrete palette refinement on small hosts. -/
noncomputable def topRegularApproximationPaletteBound (q t : ℕ) (ε : ℝ) (δ μ : ℕ → ℝ)
    (r : ℕ → ℕ) (m : ℕ) : ℕ :=
  let η' : ℕ → ℝ := fun n ↦ ((δ n) ^ 2 / (2 : ℝ) ^ r n) ^ 2 / (8 * ((q : ℝ) + 1))
  let μ' : ℕ → ℝ := fun n ↦ μ n * (((δ n) ^ 2 / (2 : ℝ) ^ r n) ^ 2 / 4) / 2
  let M := strongTopRegularityBound t ((ε / (2 * ((q : ℝ) + 1))) ^ 2) η' μ' (fun _ ↦ 1) m
  let M' := strongTopRegularityStep t η' μ' (fun _ ↦ 1) M
  let P : ℝ := ((t ^ 3 * M' ^ 3 + 1 : ℕ) : ℝ)
  let β : ℕ → ℝ := fun n ↦ min (ε / (2 * ((q : ℝ) + 1))) (η' n)
  let N := max 4 ((range (t + M + t ^ 3 * M ^ 3 + 1)).sup fun n ↦
    ⌊4 * P * 221 * ((q : ℝ) + 10) / ((β n) ^ 2 * μ' n)⌋₊ + 1)
  max M (N ^ 2)

/-- Unfolding lemma for `topRegularApproximationPaletteBound`. -/
theorem topRegularApproximationPaletteBound_def (q t : ℕ) (ε : ℝ) (δ μ : ℕ → ℝ) (r : ℕ → ℕ)
    (m : ℕ) :
    topRegularApproximationPaletteBound q t ε δ μ r m =
      let η' : ℕ → ℝ := fun n ↦ ((δ n) ^ 2 / (2 : ℝ) ^ r n) ^ 2 / (8 * ((q : ℝ) + 1))
      let μ' : ℕ → ℝ := fun n ↦ μ n * (((δ n) ^ 2 / (2 : ℝ) ^ r n) ^ 2 / 4) / 2
      let M := strongTopRegularityBound t ((ε / (2 * ((q : ℝ) + 1))) ^ 2) η' μ' (fun _ ↦ 1) m
      let M' := strongTopRegularityStep t η' μ' (fun _ ↦ 1) M
      let P : ℝ := ((t ^ 3 * M' ^ 3 + 1 : ℕ) : ℝ)
      let β : ℕ → ℝ := fun n ↦ min (ε / (2 * ((q : ℝ) + 1))) (η' n)
      let N := max 4 ((range (t + M + t ^ 3 * M ^ 3 + 1)).sup fun n ↦
        ⌊4 * P * 221 * ((q : ℝ) + 10) / ((β n) ^ 2 * μ' n)⌋₊ + 1)
      max M (N ^ 2) :=
  (rfl)

namespace Colored3Graph

variable {κ κ₂ V : Type*} [Fintype V] [DecidableEq V] [DecidableEq κ]

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
  set q := Nat.card κ
  set t := #S.vertexPart.parts
  set m₀ := Fintype.card κ₂
  let δ₁ : ℕ → ℝ := fun n ↦ (δ n) ^ 2 / (2 : ℝ) ^ r n
  let θ : ℕ → ℝ := fun n ↦ (δ₁ n) ^ 2 / 4
  let η' : ℕ → ℝ := fun n ↦ (δ₁ n) ^ 2 / (8 * ((q : ℝ) + 1))
  let μ' : ℕ → ℝ := fun n ↦ μ n * θ n / 2
  let β : ℕ → ℝ := fun n ↦ min (ε / (2 * ((q : ℝ) + 1))) (η' n)
  set γ : ℝ := ε / (2 * ((q : ℝ) + 1))
  set M := strongTopRegularityBound t (γ ^ 2) η' μ' (fun _ ↦ 1) m₀
  set M' := strongTopRegularityStep t η' μ' (fun _ ↦ 1) M
  set P : ℝ := ((t ^ 3 * M' ^ 3 + 1 : ℕ) : ℝ)
  set N := max 4 ((range (t + M + t ^ 3 * M ^ 3 + 1)).sup fun n ↦
    ⌊4 * P * 221 * ((q : ℝ) + 10) / ((β n) ^ 2 * μ' n)⌋₊ + 1)
  have hbound : topRegularApproximationPaletteBound q t ε δ μ r m₀ = max M (N ^ 2) := by
    rw [topRegularApproximationPaletteBound_def]
  rw [hbound]
  by_cases hcard : N ≤ Fintype.card V
  · have hγ : 0 < γ := by positivity
    have hδ₁ (n : ℕ) : 0 < δ₁ n := by have := hδ n; positivity
    have hθ (n : ℕ) : 0 < θ n := by have := hδ₁ n; positivity
    have hη' (n : ℕ) : 0 < η' n := by have := hδ₁ n; positivity
    have hμ' (n : ℕ) : 0 < μ' n := by have := hμ n; have := hθ n; positivity
    have hβ (n : ℕ) : 0 < β n := lt_min hγ (hη' n)
    obtain ⟨C, D, π, f, hCcard, hDcard, hCV, hDV, hπ, hrev, hf, -, hCpol, hDpol, hDreg, hgap⟩ :=
      H.exists_strong_topRegularOverMostPolyads S (pow_pos hγ 2) hη' hμ' (fun _ ↦ 1)
    have hCM : C.pairColorCount ≤ M := hCcard
    have hCcomp : C.complexity ≤ t + M + t ^ 3 * M ^ 3 :=
      C.complexity_le.trans (by rw [hCV]; gcongr)
    have hDM' : D.pairColorCount ≤ M' :=
      hDcard.trans (topRegularRefinementBound_le_strongTopRegularityStep η' μ' (fun _ ↦ 1) hCM
        hCcomp)
    have hDpoly : Fintype.card (Polyad3 D.skeleton) ≤ t ^ 3 * M' ^ 3 :=
      (card_polyad3_le D.skeleton).trans (by rw [hDV, Fintype.card_fin]; gcongr)
    set n := C.complexity
    have hv4 : 4 ≤ Fintype.card V := (le_max_left _ _).trans hcard
    have hv_sup : ⌊4 * P * 221 * ((q : ℝ) + 10) / ((β n) ^ 2 * μ' n)⌋₊ + 1 ≤ Fintype.card V :=
      (le_sup (f := fun k ↦ ⌊4 * P * 221 * ((q : ℝ) + 10) / ((β k) ^ 2 * μ' k)⌋₊ + 1)
        (mem_range.2 (Nat.lt_succ_of_le hCcomp))).trans ((le_max_right _ _).trans hcard)
    have hv_real : 4 * P * 221 * ((q : ℝ) + 10) / ((β n) ^ 2 * μ' n) < Fintype.card V :=
      (Nat.lt_floor_add_one _).trans_le (by exact_mod_cast hv_sup)
    set N₀ : ℝ := 221 * (3 * (Fintype.card V : ℝ) ^ 2 + q + 7) / (β n) ^ 2
    have hN₀_bound : 221 * (3 * (Fintype.card V : ℝ) ^ 2 + q + 7) ≤ (β n) ^ 2 * N₀ := by
      dsimp only [N₀]; rw [mul_div_cancel₀ _ (pow_ne_zero 2 (hβ n).ne')]
    have htol_n : 2 * ((q : ℝ) * (η' n + β n) + θ n) ≤ (δ₁ n) ^ 2 := by
      have hqη : (q : ℝ) * (η' n + β n) ≤ (δ₁ n) ^ 2 / 4 :=
        mul_add_le_of_div_two_add_one q (by positivity)
          (by dsimp only [η']; rw [div_div]; congr 1; ring) (min_le_right _ _)
      dsimp only [θ]; linarith
    have hq_card : q = Fintype.card κ := Nat.card_eq_fintype_card
    obtain ⟨H', happrox, hreg₁⟩ := hDreg.exists_approximates3_of_polyadEnergy_sub_le
      (C.isPolyadDecomposition_of_polyads_eq_univ hCpol)
      (D.isPolyadDecomposition_of_polyads_eq_univ hDpol) (hDV.trans hCV.symm).le f
      (fun p ↦ (hf p).symm) hgap (hη' n).le (hδ₁ n) (hβ n) (hθ n)
      (by rwa [← hq_card]) (by rwa [← hq_card])
    refine ⟨C, π, H', hCM.trans (le_max_left _ _), hCV, hπ, hrev, hCpol, happrox.mono ?_,
      (hreg₁.mono le_rfl ?_ le_rfl).of_rank_one_div_pow (hδ n)⟩
    · rw [← hq_card, Real.sqrt_sq hγ.le]
      exact mul_add_le_of_div_two_add_one q hε.le rfl (min_le_left _ _)
    · have hDP : (Fintype.card (Polyad3 D.skeleton) : ℝ) ≤ P := by
        dsimp only [P]; exact_mod_cast hDpoly.trans (Nat.le_succ _)
      have hsmall := small_polyad_mass_le hv4 hDP (by positivity) (hβ n) (hμ' n) hv_real
      rw [div_le_iff₀ (hθ n)]
      have : μ' n + μ' n = μ n * θ n := by dsimp only [μ']; ring
      linarith
  · obtain ⟨C, π, hCcard, hCV, hπ, hrev, hCpol, hreg⟩ :=
      exists_discrete_topRegularOverMostPolyads H S hδ hμ r
    refine ⟨C, π, H, (hCcard.trans (Nat.pow_le_pow_left (not_le.1 hcard).le 2)).trans
      (le_max_right _ _), hCV, hπ, hrev, hCpol, H.approximates3_self hε.le, hreg⟩

end Colored3Graph

end TauCeti
