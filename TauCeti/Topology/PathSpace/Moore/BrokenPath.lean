/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.PathSpace.Moore.ArcStraightening

/-!
# Broken Moore paths with prescribed arc durations

Let `ρ` be a path interpolation on a set `U` of pairs of points (`TauCeti.IsPathInterpolation`),
for instance the minimizing geodesics between close points of a Riemannian manifold. Given points
`q 0, …, q n` with consecutive pairs in `U` and durations `ℓ 0, …, ℓ (n - 1)`, the **broken Moore
path** `TauCeti.brokenMoorePath hρ n q ℓ` concatenates, for each `i`, the interpolating path
`ρ (q i, q (i + 1))` run in time `ℓ i`. An arc of duration zero is the constant path of length
zero, so it is only allowed between equal points. The broken Moore path has length `∑ i, ℓ i`
(`TauCeti.length_brokenMoorePath`) and depends continuously on the points and on the durations,
also where durations vanish (`TauCeti.continuous_brokenMoorePath`).

Changing the durations continuously therefore gives a homotopy of broken Moore paths with the same
vertices, which deforms a broken path run with equal arc durations into one run at another speed
on each arc. The arc-straightening homotopy `TauCeti.MoorePath.arcStraightening`
ends at the broken path `TauCeti.MoorePath.brokenPathMap` through the sampled vertices, with the
duration of the original path split equally among the arcs. It is the broken Moore path through
the same vertices with all `n + 1` durations equal to `γ.length / (n + 1)`
(`TauCeti.MoorePath.brokenPathMap_eq_brokenMoorePath`).

## Main definitions

* `TauCeti.brokenMoorePath hρ n q ℓ h`: the concatenation of the interpolating paths
  `ρ (q i, q (i + 1))`, run in times `ℓ i`.

## Main results

* `TauCeti.continuous_rescale_ofUnitPath`: interpolating arcs depend continuously on their end
  points and durations.
* `TauCeti.brokenMoorePath_succ`: a broken Moore path is its first arc followed by the broken
  Moore path through the remaining points.
* `TauCeti.length_brokenMoorePath`: its length is the sum of the durations.
* `TauCeti.continuous_brokenMoorePath`: it depends continuously on the points and the durations.
* `TauCeti.brokenMoorePath_apply_mul_add`: with all durations equal to `c`, at time `i * c + τ`
  the broken Moore path is on its `i`-th arc, at time `τ` of that arc.
* `TauCeti.MoorePath.brokenPathMap_eq_brokenMoorePath`: the end of the arc-straightening homotopy
  is the broken Moore path through the sampled vertices with equal durations.

## References

* M. Abouzaid, *Symplectic cohomology and Viterbo's theorem*, in *Free loop spaces in geometry
  and topology*, IRMA Lect. Math. Theor. Phys. 24 (2015), §11.2.
* J. Milnor, *Morse Theory*, Annals of Mathematics Studies 51, Princeton, 1963, §16.
-/

public noncomputable section

open scoped NNReal unitInterval
open Set unitInterval

namespace TauCeti

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
  {ρ : X × X → C(I, X)} {U : Set (X × X)}

/-! ### Arcs of prescribed duration -/

section Arc

/-- The interpolating path from `x` to `y`, run in time `ℓ`, starts at `x`. -/
theorem source_rescale_ofUnitPath (hρ : IsPathInterpolation ρ U) {x y : X}
    (hxy : (x, y) ∈ U) (ℓ : ℝ≥0) : ((MoorePath.ofUnitPath (ρ (x, y))).rescale ℓ).source = x := by
  rw [MoorePath.source_rescale, MoorePath.source_ofUnitPath, hρ.apply_zero _ hxy]

/-- The interpolating path from `x` to `y`, run in time `ℓ`, ends at `y`, provided `x = y` when
`ℓ = 0`. -/
theorem target_rescale_ofUnitPath (hρ : IsPathInterpolation ρ U) {x y : X}
    (hxy : (x, y) ∈ U) {ℓ : ℝ≥0} (hℓ : ℓ = 0 → x = y) :
    ((MoorePath.ofUnitPath (ρ (x, y))).rescale ℓ).target = y := by
  rcases eq_or_ne ℓ 0 with rfl | hℓ0
  · rw [MoorePath.rescale_zero, MoorePath.target_refl, MoorePath.source_ofUnitPath,
      hρ.apply_zero _ hxy, hℓ rfl]
  · rw [MoorePath.target_rescale _ hℓ0, MoorePath.target_ofUnitPath, hρ.apply_one _ hxy]

/-- **Interpolating arcs depend continuously on their end points and durations**, also where
durations vanish, provided that an arc of duration zero joins equal points. -/
theorem continuous_rescale_ofUnitPath (hρ : IsPathInterpolation ρ U) {F : Y → X × X}
    {L : Y → ℝ≥0} (hF : Continuous F) (hL : Continuous L) (hFU : ∀ y, F y ∈ U)
    (h : ∀ y, L y = 0 → (F y).1 = (F y).2) :
    Continuous fun y ↦ (MoorePath.ofUnitPath (ρ (F y))).rescale (L y) := by
  refine (MoorePath.continuous_ofUnitPath.comp
    (hρ.continuousOn.comp_continuous hF hFU)).moorePath_rescale_of_forall_eq_source hL
    fun y hy t ↦ ?_
  -- An arc of duration zero joins equal points, along which the interpolating path is constant.
  have hxy : F y = ((F y).1, (F y).1) := Prod.ext rfl (h y hy).symm
  have hU := hFU y
  rw [hxy] at hU
  simp only [Function.comp_apply, MoorePath.ofUnitPath_apply, MoorePath.source_ofUnitPath]
  rw [hxy, hρ.apply_diag _ hU, ContinuousMap.const_apply, ContinuousMap.const_apply]

end Arc

/-! ### Broken Moore paths -/

section Broken

omit [TopologicalSpace X] in
/-- If the consecutive points of `q 0, …, q (n + 1)` form pairs in `U`, with equal points where
the duration vanishes, so do those of `q 1, …, q (n + 1)`. -/
private theorem forall_tail_mem {n : ℕ} {q : Fin (n + 2) → X} {ℓ : Fin (n + 1) → ℝ≥0}
    (h : ∀ i : Fin (n + 1), (q i.castSucc, q i.succ) ∈ U ∧ (ℓ i = 0 → q i.castSucc = q i.succ))
    (i : Fin n) :
    (Fin.tail q i.castSucc, Fin.tail q i.succ) ∈ U ∧
      (Fin.tail ℓ i = 0 → Fin.tail q i.castSucc = Fin.tail q i.succ) := by
  simpa only [Fin.tail, Fin.succ_castSucc] using h i.succ

/-- The broken Moore path through `q 0, …, q n`, together with its end points. -/
private def brokenMoorePathAux (hρ : IsPathInterpolation ρ U) : (n : ℕ) → (q : Fin (n + 1) → X) →
    (ℓ : Fin n → ℝ≥0) →
    (∀ i : Fin n, (q i.castSucc, q i.succ) ∈ U ∧ (ℓ i = 0 → q i.castSucc = q i.succ)) →
    {γ : MoorePath X // γ.source = q 0 ∧ γ.target = q (Fin.last n)}
  | 0, q, _, _ => ⟨MoorePath.refl (q 0), MoorePath.source_refl _, MoorePath.target_refl _⟩
  | n + 1, q, ℓ, h =>
    let γ := brokenMoorePathAux hρ n (Fin.tail q) (Fin.tail ℓ) (forall_tail_mem h)
    ⟨((MoorePath.ofUnitPath (ρ (q (Fin.castSucc 0), q (Fin.succ 0)))).rescale (ℓ 0)).trans γ.val
        (by rw [target_rescale_ofUnitPath hρ (h 0).1 (h 0).2, γ.property.1, Fin.tail]),
      by
        rw [MoorePath.source_trans, source_rescale_ofUnitPath hρ (h 0).1]
        exact congrArg q Fin.castSucc_zero,
      by rw [MoorePath.target_trans, γ.property.2, Fin.tail, Fin.succ_last]⟩

/-- **The broken Moore path** through points `q 0, …, q n` with durations `ℓ 0, …, ℓ (n - 1)`:
the concatenation of the interpolating paths `ρ (q i, q (i + 1))`, each run in time `ℓ i`. The
consecutive points must form pairs in `U`, and be equal where the duration vanishes. -/
def brokenMoorePath (hρ : IsPathInterpolation ρ U) (n : ℕ) (q : Fin (n + 1) → X)
    (ℓ : Fin n → ℝ≥0)
    (h : ∀ i : Fin n, (q i.castSucc, q i.succ) ∈ U ∧ (ℓ i = 0 → q i.castSucc = q i.succ)) :
    MoorePath X :=
  (brokenMoorePathAux hρ n q ℓ h).val

variable (hρ : IsPathInterpolation ρ U)

@[simp]
theorem brokenMoorePath_zero (q : Fin 1 → X) (ℓ : Fin 0 → ℝ≥0)
    (h : ∀ i : Fin 0, (q i.castSucc, q i.succ) ∈ U ∧ (ℓ i = 0 → q i.castSucc = q i.succ)) :
    brokenMoorePath hρ 0 q ℓ h = MoorePath.refl (q 0) := by
  simp only [brokenMoorePath, brokenMoorePathAux]

@[simp]
theorem source_brokenMoorePath (n : ℕ) (q : Fin (n + 1) → X) (ℓ : Fin n → ℝ≥0)
    (h : ∀ i : Fin n, (q i.castSucc, q i.succ) ∈ U ∧ (ℓ i = 0 → q i.castSucc = q i.succ)) :
    (brokenMoorePath hρ n q ℓ h).source = q 0 :=
  (brokenMoorePathAux hρ n q ℓ h).property.1

@[simp]
theorem target_brokenMoorePath (n : ℕ) (q : Fin (n + 1) → X) (ℓ : Fin n → ℝ≥0)
    (h : ∀ i : Fin n, (q i.castSucc, q i.succ) ∈ U ∧ (ℓ i = 0 → q i.castSucc = q i.succ)) :
    (brokenMoorePath hρ n q ℓ h).target = q (Fin.last n) :=
  (brokenMoorePathAux hρ n q ℓ h).property.2

/-- The broken Moore path through `q 0, …, q (n + 1)` is the interpolating path from `q 0` to
`q 1`, run in time `ℓ 0`, followed by the broken Moore path through `q 1, …, q (n + 1)`. -/
theorem brokenMoorePath_succ (n : ℕ) (q : Fin (n + 2) → X) (ℓ : Fin (n + 1) → ℝ≥0)
    (h : ∀ i : Fin (n + 1), (q i.castSucc, q i.succ) ∈ U ∧ (ℓ i = 0 → q i.castSucc = q i.succ))
    (h' : ∀ i : Fin n, (Fin.tail q i.castSucc, Fin.tail q i.succ) ∈ U ∧
      (Fin.tail ℓ i = 0 → Fin.tail q i.castSucc = Fin.tail q i.succ)) :
    brokenMoorePath hρ (n + 1) q ℓ h =
      ((MoorePath.ofUnitPath (ρ (q (Fin.castSucc 0), q (Fin.succ 0)))).rescale (ℓ 0)).trans
        (brokenMoorePath hρ n (Fin.tail q) (Fin.tail ℓ) h')
        (by
          rw [target_rescale_ofUnitPath hρ (h 0).1 (h 0).2, source_brokenMoorePath]
          rfl) := by
  simp only [brokenMoorePath, brokenMoorePathAux]

/-- The broken Moore path only depends on its points and durations. -/
theorem brokenMoorePath_congr {n : ℕ} {q q' : Fin (n + 1) → X} {ℓ ℓ' : Fin n → ℝ≥0}
    (h : ∀ i : Fin n, (q i.castSucc, q i.succ) ∈ U ∧ (ℓ i = 0 → q i.castSucc = q i.succ))
    (h' : ∀ i : Fin n, (q' i.castSucc, q' i.succ) ∈ U ∧ (ℓ' i = 0 → q' i.castSucc = q' i.succ))
    (hq : q = q') (hℓ : ℓ = ℓ') :
    brokenMoorePath hρ n q ℓ h = brokenMoorePath hρ n q' ℓ' h' := by
  subst hq hℓ
  rfl

/-- The length of a broken Moore path is the sum of its durations. -/
@[simp]
theorem length_brokenMoorePath (n : ℕ) (q : Fin (n + 1) → X) (ℓ : Fin n → ℝ≥0)
    (h : ∀ i : Fin n, (q i.castSucc, q i.succ) ∈ U ∧ (ℓ i = 0 → q i.castSucc = q i.succ)) :
    (brokenMoorePath hρ n q ℓ h).length = ∑ i, ℓ i := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [brokenMoorePath_succ hρ n q ℓ h (forall_tail_mem h), MoorePath.length_trans,
      MoorePath.length_rescale, ih, Fin.sum_univ_succ, Fin.tail_def]

/-- **Broken Moore paths depend continuously on their points and durations**, also where
durations vanish. -/
theorem continuous_brokenMoorePath (n : ℕ) {F : Y → Fin (n + 1) → X} {L : Y → Fin n → ℝ≥0}
    (hF : Continuous F) (hL : Continuous L)
    (h : ∀ y, ∀ i : Fin n,
      (F y i.castSucc, F y i.succ) ∈ U ∧ (L y i = 0 → F y i.castSucc = F y i.succ)) :
    Continuous fun y ↦ brokenMoorePath hρ n (F y) (L y) (h y) := by
  induction n with
  | zero =>
    simp only [brokenMoorePath_zero]
    exact MoorePath.continuous_refl.comp ((continuous_apply 0).comp hF)
  | succ n ih =>
    simp only [fun y ↦ brokenMoorePath_succ hρ n (F y) (L y) (h y) (forall_tail_mem (h y))]
    exact (continuous_rescale_ofUnitPath hρ (by fun_prop) ((continuous_apply 0).comp hL)
      (fun y ↦ (h y 0).1) fun y ↦ (h y 0).2).moorePath_trans
        (ih hF.finTail hL.finTail fun y ↦ forall_tail_mem (h y)) _

/-- **A broken Moore path with equal durations, on its `i`-th arc.** If every arc is run in time
`c`, then at time `i * c + τ`, for `τ ≤ c`, the broken Moore path is at time `τ` of the
interpolating path from `q i` to `q (i + 1)` run in time `c`. -/
theorem brokenMoorePath_apply_mul_add {n : ℕ} (q : Fin (n + 1) → X) (c : ℝ≥0)
    (h : ∀ i : Fin n, (q i.castSucc, q i.succ) ∈ U ∧ (c = 0 → q i.castSucc = q i.succ))
    (i : Fin n) {τ : ℝ≥0} (hτ : τ ≤ c) :
    brokenMoorePath hρ n q (fun _ ↦ c) h ((i : ℕ) * c + τ) =
      (MoorePath.ofUnitPath (ρ (q i.castSucc, q i.succ))).rescale c τ := by
  induction n with
  | zero => exact i.elim0
  | succ n ih =>
    rw [brokenMoorePath_succ hρ n q _ h (forall_tail_mem h)]
    induction i using Fin.cases with
    | zero =>
      rw [Fin.val_zero, Nat.cast_zero, zero_mul, zero_add]
      exact MoorePath.trans_apply_of_le _ _ _ (by rwa [MoorePath.length_rescale])
    | succ j =>
      have ht : ((j.succ : ℕ) : ℝ≥0) * c + τ =
          ((MoorePath.ofUnitPath (ρ (q (Fin.castSucc 0), q (Fin.succ 0)))).rescale c).length +
            ((j : ℕ) * c + τ) := by
        rw [MoorePath.length_rescale, Fin.val_succ, Nat.cast_succ]
        ring
      rw [ht, MoorePath.trans_apply_length_add]
      exact (ih (Fin.tail q) (forall_tail_mem h) j).trans (by rw [Fin.tail, Fin.tail,
        Fin.succ_castSucc])

end Broken

/-! ### The end of the arc-straightening homotopy -/

namespace MoorePath

variable (hρ : IsPathInterpolation ρ U)

/-- Before the end of the arc-straightening homotopy of a Moore path of positive length, at time
`t = L s` with `s = (i + a) / (n + 1)`, both its final broken path and the broken Moore path with
equal durations are at time `a` of the interpolating path from the `i`-th to the `(i + 1)`-st
vertex. -/
private theorem brokenPathMap_apply_of_lt {n : ℕ} (γ : arcsWithin U (n + 1))
    {q : Fin (n + 2) → X}
    (hq : ∀ i : Fin (n + 2), q i = (γ : MoorePath X).toUnitPath (arcPoint (n + 1) i 0))
    (h : ∀ i : Fin (n + 1), (q i.castSucc, q i.succ) ∈ U ∧
      ((γ : MoorePath X).length / (n + 1) = 0 → q i.castSucc = q i.succ))
    (hL : (γ : MoorePath X).length ≠ 0) {t : ℝ≥0} (ht : t < (γ : MoorePath X).length) :
    brokenPathMap hρ n.succ_pos γ t =
      brokenMoorePath hρ (n + 1) q (fun _ ↦ (γ : MoorePath X).length / (n + 1)) h t := by
  set L := (γ : MoorePath X).length
  have hLpos : (0 : ℝ) < L := by positivity
  let s : I := ⟨t / L, by positivity, (div_le_one hLpos).2 (by exact_mod_cast ht.le)⟩
  set i := arcIndex (n + 1) s
  set a := arcParam (n + 1) s
  have hi : i < n + 1 := arcIndex_lt n.succ_pos s
  have hts : t = L * toNNReal (arcPoint (n + 1) i a) := by
    rw [arcPoint_arcIndex_arcParam n.succ_pos s]
    exact NNReal.eq (by simp [s, mul_div_cancel₀ _ hLpos.ne'])
  have hti : t = (i : ℝ≥0) * (L / (n + 1)) + toNNReal a * (L / (n + 1)) := by
    refine NNReal.eq ?_
    rw [hts]
    push_cast
    rw [coe_toNNReal, coe_toNNReal, coe_arcPoint hi]
    push_cast
    ring
  have hlen : (brokenPathMap hρ n.succ_pos γ).length = L := length_brokenPathMap hρ _ γ
  conv_lhs => rw [hts, ← hlen, ← toUnitPath_apply, toUnitPath_brokenPathMap,
    brokenPath_arcPoint_of_arcsWithin hρ (mem_arcsWithin.1 γ.property) hi]
  rw [hti, brokenMoorePath_apply_mul_add hρ q _ h ⟨i, hi⟩
    (mul_le_of_le_one_left zero_le (toNNReal_le_one a))]
  -- Run in time `c = L / (n + 1)`, the interpolating path is at time `a` at time `a c`.
  simp [hq, rescale_apply, mul_div_cancel_right₀ _ (div_ne_zero hL (by positivity) :
    L / (n + 1) ≠ 0)]

/-- The broken path at the end of the arc-straightening homotopy of a Moore path `γ` whose arcs
lie in `U` is the broken Moore path through the vertices `γ.toUnitPath (i / (n + 1))`, `i ≤ n + 1`,
with all durations equal to `γ.length / (n + 1)`. -/
theorem brokenPathMap_eq_brokenMoorePath {n : ℕ} (γ : arcsWithin U (n + 1))
    {q : Fin (n + 2) → X}
    (hq : ∀ i : Fin (n + 2), q i = (γ : MoorePath X).toUnitPath (arcPoint (n + 1) i 0))
    (h : ∀ i : Fin (n + 1), (q i.castSucc, q i.succ) ∈ U ∧
      ((γ : MoorePath X).length / (n + 1) = 0 → q i.castSucc = q i.succ)) :
    brokenPathMap hρ n.succ_pos γ =
      brokenMoorePath hρ (n + 1) q (fun _ ↦ (γ : MoorePath X).length / (n + 1)) h := by
  set L := (γ : MoorePath X).length
  have hlen : (brokenPathMap hρ n.succ_pos γ).length = L := length_brokenPathMap hρ _ γ
  have hlen' : (brokenMoorePath hρ (n + 1) q (fun _ ↦ L / (n + 1)) h).length = L := by
    rw [length_brokenMoorePath, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
      ← Nat.cast_succ, mul_div_cancel₀ _ (by positivity)]
  rcases eq_or_ne L 0 with hL | hL
  · -- Both paths have length zero and start at the source of `γ`.
    rw [eq_refl_of_length_eq_zero (hlen.trans hL), eq_refl_of_length_eq_zero (hlen'.trans hL),
      source_brokenMoorePath, hq, Fin.val_zero, arcPoint_zero_zero, toUnitPath_zero,
      brokenPathMap_apply, source_arcStraighteningMap]
  refine ext (hlen.trans hlen'.symm) fun t ↦ ?_
  rcases le_or_gt L t with hLt | htL
  · -- After the end of the paths both are at the target of `γ`.
    rw [apply_of_length_le _ (hlen.trans_le hLt), apply_of_length_le _ (hlen'.trans_le hLt),
      target_brokenMoorePath, hq, Fin.val_last, arcPoint_self_zero n.succ_pos, toUnitPath_one,
      brokenPathMap_apply, target_arcStraighteningMap]
  · exact brokenPathMap_apply_of_lt hρ γ hq h hL htL

end MoorePath

end TauCeti
