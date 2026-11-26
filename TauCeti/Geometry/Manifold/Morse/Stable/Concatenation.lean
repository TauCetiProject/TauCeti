/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Morse.Stable.Stratum

/-!
# Concatenation of broken trajectories

Let `f` be a smooth function on a compact boundaryless manifold `M` and `X` a pseudo-gradient
field adapted to `f`. Fix a set `L` of levels of `f`. The trajectories from `p` to `r` are recorded
on the levels of `L` strictly between `f r` and `f p`, as families of points
`w : L ∩ (f r, f p) → M` (`TauCeti.IsAdaptedPseudoGradient.morseTrajectoryRecords`), and so are the
broken trajectories (`TauCeti.IsAdaptedPseudoGradient.morseBrokenTrajectoryRecords`). When `f` is
a Morse function, `X` satisfies the Morse–Smale condition, `L` is a countable set of regular values
and `p ≠ r`, the records of broken trajectories form the compactified space of trajectories
`𝓜(p, r)`, the closure of the records of unbroken ones
(`TauCeti.IsAdaptedPseudoGradient.IsMorseSmale.closure_morseTrajectoryRecords`).

This file equips these spaces with their composition maps. A record `w₁` from `p` to `q` and a
record `w₂` from `q` to `r` are **concatenated** at `q` (`TauCeti.morseRecordConcat`): on a level
above `f q` the concatenation is `w₁`, on a level below `f q` it is `w₂`. A single set `L` of
levels serves all pairs of points, so that the levels on the two sides of `f q` are the levels from
`p` to `r`. When `f q` is not a level of `L`, for instance when `q` is a critical point and `L` is
made of regular values:

* concatenation is continuous (`TauCeti.continuous_morseRecordConcat`), strictly associative
  (`TauCeti.morseRecordConcat_assoc`), and the records from `p` to `p`, on no level, are units for
  it (`TauCeti.morseRecordConcat_self_left`, `TauCeti.morseRecordConcat_self_right`);
* it sends broken trajectories from `p` to `q` and from `q` to `r` to a broken trajectory from `p`
  to `r` (`TauCeti.IsAdaptedPseudoGradient.morseRecordConcat_mem_morseBrokenTrajectoryRecords`),
  through the two chains of critical points put end to end;
* every broken trajectory from `p` to `r ≠ p` is either unbroken or the concatenation at its first
  breaking point `q` of an unbroken trajectory from `p` to `q` and a broken trajectory from `q` to
  `r` (`TauCeti.IsAdaptedPseudoGradient.morseBrokenTrajectoryRecords_eq_union`);
* if `L` has a level strictly between `f q` and `f p`, no concatenation at `q ≠ r` is unbroken
  (`TauCeti.IsAdaptedPseudoGradient.disjoint_morseTrajectoryRecords_image2_morseRecordConcat`).

So when `L` has a level between any two critical values, the broken trajectories from `p` to
`r ≠ p` that are not unbroken are exactly the union, over the critical points `q ≠ p, r`, of the
images of the concatenation maps `𝓜(p, q) × 𝓜(q, r) → 𝓜(p, r)`.

Bundled as continuous maps between the spaces of broken trajectories
(`TauCeti.IsAdaptedPseudoGradient.morseBrokenTrajectoryConcat`), with their associativity
(`TauCeti.IsAdaptedPseudoGradient.morseBrokenTrajectoryConcat_assoc`), they provide the maps from
which the composition maps `ι x z y : 𝓜(x, z) × 𝓜(z, y) → 𝓜(x, y)` of a twisting chain system of
Barraud and Cornea (`TauCeti.TwistingChainSystem`) are built, once the index type is the set of
critical points of `f` and `L` contains no critical value
(`TauCeti.IsAdaptedPseudoGradient.morseRecordsComp`).

## Main definitions

* `TauCeti.morseRecordConcat`: the concatenation of records at a point `q`.
* `TauCeti.IsAdaptedPseudoGradient.morseBrokenTrajectoryConcat`: the concatenation of broken
  trajectories at a point `q`, as a continuous map.

## Main results

* `TauCeti.continuous_morseRecordConcat`: concatenation is continuous.
* `TauCeti.morseRecordConcat_assoc`: concatenation is associative.
* `TauCeti.IsAdaptedPseudoGradient.morseRecordConcat_mem_morseBrokenTrajectoryRecords`: the
  concatenation of broken trajectories is a broken trajectory.
* `TauCeti.IsAdaptedPseudoGradient.morseBrokenTrajectoryConcat_assoc`: concatenation of broken
  trajectories is associative.
* `TauCeti.IsAdaptedPseudoGradient.morseBrokenTrajectoryRecords_eq_union`: a broken trajectory is
  unbroken or a concatenation at its first breaking point.
* `TauCeti.IsAdaptedPseudoGradient.disjoint_morseTrajectoryRecords_image2_morseRecordConcat`:
  if `q ≠ r` and `L` has a level strictly between `f q` and `f p`, concatenations at `q` are not
  unbroken.

## References

* J.-F. Barraud, O. Cornea, *Lagrangian intersections and the Serre spectral sequence*, Ann. of
  Math. 166 (2007), 657–722, Section 2 and Appendix A.
* M. Hutchings, *Lecture notes on Morse homology (with an eye towards Floer theory and
  pseudoholomorphic curves)*, 2002, §2 (the compactified spaces of flow lines and their boundary
  strata).
-/

public section

open Set Topology
open scoped ContDiff Manifold

namespace TauCeti

/-! ### Concatenation of records -/

section Concat

variable {M : Type*} (f : M → ℝ) (L : Set ℝ)

/-- The **concatenation** at `q` of a family `w₁` of points on the levels of `L` strictly between
`f q` and `f p` and a family `w₂` of points on the levels of `L` strictly between `f r` and `f q`:
the family on the levels of `L` strictly between `f r` and `f p` that is `w₁` above `f q` and `w₂`
below `f q`. On the level `f q` itself, when it belongs to `L`, its value is `q`; this case does not
arise when `q` is a critical point and `L` is made of regular values. -/
noncomputable def morseRecordConcat (p q r : M) (w₁ : ↥(L ∩ Ioo (f q) (f p)) → M)
    (w₂ : ↥(L ∩ Ioo (f r) (f q)) → M) : ↥(L ∩ Ioo (f r) (f p)) → M := fun c ↦
  if h₁ : f q < c then w₁ ⟨c, c.property.1, h₁, c.property.2.2⟩
  else if h₂ : (c : ℝ) < f q then w₂ ⟨c, c.property.1, c.property.2.1, h₂⟩ else q

variable {f L} {p q r s : M}

/-- Above `f q`, the concatenation at `q` is the first family. -/
theorem morseRecordConcat_apply_of_lt (w₁ : ↥(L ∩ Ioo (f q) (f p)) → M)
    (w₂ : ↥(L ∩ Ioo (f r) (f q)) → M) (c : ↥(L ∩ Ioo (f r) (f p))) (h : f q < c) :
    morseRecordConcat f L p q r w₁ w₂ c = w₁ ⟨c, c.property.1, h, c.property.2.2⟩ := by
  simp [morseRecordConcat, h]

/-- Below `f q`, the concatenation at `q` is the second family. -/
theorem morseRecordConcat_apply_of_gt (w₁ : ↥(L ∩ Ioo (f q) (f p)) → M)
    (w₂ : ↥(L ∩ Ioo (f r) (f q)) → M) (c : ↥(L ∩ Ioo (f r) (f p))) (h : (c : ℝ) < f q) :
    morseRecordConcat f L p q r w₁ w₂ c = w₂ ⟨c, c.property.1, c.property.2.1, h⟩ := by
  simp [morseRecordConcat, h, h.not_gt]

/-- On the level `f q`, when it belongs to `L`, the concatenation at `q` is `q`. -/
theorem morseRecordConcat_apply_of_eq (w₁ : ↥(L ∩ Ioo (f q) (f p)) → M)
    (w₂ : ↥(L ∩ Ioo (f r) (f q)) → M) (c : ↥(L ∩ Ioo (f r) (f p))) (h : (c : ℝ) = f q) :
    morseRecordConcat f L p q r w₁ w₂ c = q := by
  simp [morseRecordConcat, h]

/-- **Concatenation at the source is trivial.** There is no level strictly between `f p` and itself,
so concatenating at `p` returns the second family. -/
@[simp]
theorem morseRecordConcat_self_left (w₁ : ↥(L ∩ Ioo (f p) (f p)) → M)
    (w₂ : ↥(L ∩ Ioo (f r) (f p)) → M) : morseRecordConcat f L p p r w₁ w₂ = w₂ :=
  funext fun c ↦ morseRecordConcat_apply_of_gt w₁ w₂ c c.property.2.2

/-- **Concatenation at the target is trivial.** There is no level strictly between `f r` and itself,
so concatenating at `r` returns the first family. -/
@[simp]
theorem morseRecordConcat_self_right (w₁ : ↥(L ∩ Ioo (f r) (f p)) → M)
    (w₂ : ↥(L ∩ Ioo (f r) (f r)) → M) : morseRecordConcat f L p r r w₁ w₂ = w₁ :=
  funext fun c ↦ morseRecordConcat_apply_of_lt w₁ w₂ c c.property.2.1

/-- **Concatenation is associative.** If `f s ≤ f q` and `f q` is not a level of `L`,
concatenating at `q` and then at `s` is concatenating at `s` and then at `q`. -/
theorem morseRecordConcat_assoc (hq : f q ∉ L) (hsq : f s ≤ f q)
    (w₁ : ↥(L ∩ Ioo (f q) (f p)) → M) (w₂ : ↥(L ∩ Ioo (f s) (f q)) → M)
    (w₃ : ↥(L ∩ Ioo (f r) (f s)) → M) :
    morseRecordConcat f L p s r (morseRecordConcat f L p q s w₁ w₂) w₃ =
      morseRecordConcat f L p q r w₁ (morseRecordConcat f L q s r w₂ w₃) := by
  funext c
  -- The level `c` is not `f q`; compare it with `f q` and `f s`. On the level `f s < f q` both
  -- sides are `s`.
  have hcq : (c : ℝ) ≠ f q := fun h ↦ hq (h ▸ c.property.1)
  rcases lt_or_gt_of_ne hcq with hcq | hcq <;>
    rcases lt_trichotomy (c : ℝ) (f s) with hcs | hcs | hcs <;>
    simp only [morseRecordConcat] <;> split_ifs <;> first | rfl | linarith

variable [TopologicalSpace M]

/-- **Concatenation is continuous**, jointly in the two families. -/
@[fun_prop]
theorem continuous_morseRecordConcat (p q r : M) :
    Continuous fun w : (↥(L ∩ Ioo (f q) (f p)) → M) × (↥(L ∩ Ioo (f r) (f q)) → M) ↦
      morseRecordConcat f L p q r w.1 w.2 := by
  -- Each point of the concatenation is a point of one of the families, or the constant `q`.
  refine continuous_pi fun c ↦ ?_
  unfold morseRecordConcat
  split_ifs <;> fun_prop

end Concat

/-! ### Concatenation of broken trajectories -/

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [CompactSpace M] [T2Space M]
  {f : M → ℝ} {X : (x : M) → TangentSpace 𝓘(ℝ, E) x} {L : Set ℝ} {p q r s : M}

namespace IsAdaptedPseudoGradient

variable (hX : IsAdaptedPseudoGradient f X)

/-- Two chains of critical points joined by trajectories, the first ending where the second starts,
put end to end: the chain `x₁ 0, …, x₁ k₁ = x₂ 0, …, x₂ k₂`, with the trajectories `z₁` followed by
the trajectories `z₂`. -/
private theorem exists_chain_append {k₁ k₂ : ℕ} {x₁ : Fin (k₁ + 1) → M} {z₁ : Fin k₁ → M}
    {x₂ : Fin (k₂ + 1) → M} {z₂ : Fin k₂ → M} (h₁ : x₁ (Fin.last k₁) = x₂ 0)
    (hc₁ : ∀ j, mfderiv 𝓘(ℝ, E) 𝓘(ℝ) f (x₁ j) = 0) (hc₂ : ∀ j, mfderiv 𝓘(ℝ, E) 𝓘(ℝ) f (x₂ j) = 0)
    (hne₁ : ∀ j : Fin k₁, x₁ j.castSucc ≠ x₁ j.succ)
    (hne₂ : ∀ j : Fin k₂, x₂ j.castSucc ≠ x₂ j.succ)
    (hz₁ : ∀ j : Fin k₁,
      z₁ j ∈ hX.flow.unstableSet (x₁ j.castSucc) ∩ hX.flow.stableSet (x₁ j.succ))
    (hz₂ : ∀ j : Fin k₂,
      z₂ j ∈ hX.flow.unstableSet (x₂ j.castSucc) ∩ hX.flow.stableSet (x₂ j.succ)) :
    ∃ x : Fin (k₁ + k₂ + 1) → M, x 0 = x₁ 0 ∧ x (Fin.last _) = x₂ (Fin.last k₂) ∧
      (∀ j, mfderiv 𝓘(ℝ, E) 𝓘(ℝ) f (x j) = 0) ∧ (∀ j : Fin (k₁ + k₂), x j.castSucc ≠ x j.succ) ∧
      ∀ j : Fin (k₁ + k₂), Fin.append z₁ z₂ j ∈
        hX.flow.unstableSet (x j.castSucc) ∩ hX.flow.stableSet (x j.succ) := by
  let x : Fin (k₁ + k₂ + 1) → M := fun i ↦
    if h : (i : ℕ) ≤ k₁ then x₁ ⟨i, by omega⟩ else x₂ ⟨i - k₁, by omega⟩
  -- Up to `k₁` the chain is `x₁`, and from `k₁` on it is `x₂`, shifted by `k₁`.
  have hx₁ (i : Fin (k₁ + k₂ + 1)) (h : (i : ℕ) ≤ k₁) : x i = x₁ ⟨i, by omega⟩ := by
    simp [x, h]
  have hx₂ (i : Fin (k₁ + k₂ + 1)) (h : k₁ ≤ (i : ℕ)) : x i = x₂ ⟨i - k₁, by omega⟩ := by
    rcases h.lt_or_eq with h | h
    · have hi : ¬(i : ℕ) ≤ k₁ := by omega
      simp [x, hi]
    · -- At `k₁` the two chains meet.
      have h₀ : (⟨i - k₁, by omega⟩ : Fin (k₂ + 1)) = 0 := Fin.ext (by simp; omega)
      rw [hx₁ i h.ge, h₀, ← h₁]
      exact congrArg x₁ (Fin.ext h.symm)
  -- Each step of the chain is a step of `x₁` or of `x₂`.
  have hstep (j : Fin (k₁ + k₂)) : ∃ (a b : M) (y : M), x j.castSucc = a ∧ x j.succ = b ∧
      Fin.append z₁ z₂ j = y ∧ a ≠ b ∧ y ∈ hX.flow.unstableSet a ∩ hX.flow.stableSet b := by
    induction j using Fin.addCases with
    | left j =>
      refine ⟨_, _, _, ?_, ?_, Fin.append_left z₁ z₂ j, hne₁ j, hz₁ j⟩
      · exact (hx₁ _ (by simp)).trans (congrArg x₁ (Fin.ext (by simp)))
      · exact (hx₁ _ (by simp)).trans (congrArg x₁ (Fin.ext (by simp)))
    | right j =>
      refine ⟨_, _, _, ?_, ?_, Fin.append_right z₁ z₂ j, hne₂ j, hz₂ j⟩
      · exact (hx₂ _ (by simp)).trans (congrArg x₂ (Fin.ext (by simp)))
      · exact (hx₂ _ (by simp; omega)).trans (congrArg x₂ (Fin.ext (by simp; omega)))
  refine ⟨x, (hx₁ 0 (by simp)).trans (congrArg x₁ (Fin.ext (by simp))),
    (hx₂ _ (by simp)).trans (congrArg x₂ (Fin.ext (by simp))), fun i ↦ ?_, fun j ↦ ?_,
    fun j ↦ ?_⟩
  · by_cases h : (i : ℕ) ≤ k₁
    · rw [hx₁ i h]; exact hc₁ _
    · rw [hx₂ i (by omega)]; exact hc₂ _
  · obtain ⟨a, b, y, ha, hb, -, hab, -⟩ := hstep j
    rwa [ha, hb]
  · obtain ⟨a, b, y, ha, hb, hy, -, hyab⟩ := hstep j
    rwa [ha, hb, hy]

/-- **The concatenation of broken trajectories is a broken trajectory.** If `f q` is not a level of
`L`, the concatenation at `q` of a broken trajectory from `p` to `q` and a broken trajectory from
`q` to `r` is a broken trajectory from `p` to `r`, through the two chains of critical points put
end to end. -/
theorem morseRecordConcat_mem_morseBrokenTrajectoryRecords (hq : f q ∉ L)
    {w₁ : ↥(L ∩ Ioo (f q) (f p)) → M} {w₂ : ↥(L ∩ Ioo (f r) (f q)) → M}
    (h₁ : w₁ ∈ hX.morseBrokenTrajectoryRecords p q Subtype.val)
    (h₂ : w₂ ∈ hX.morseBrokenTrajectoryRecords q r Subtype.val) :
    morseRecordConcat f L p q r w₁ w₂ ∈ hX.morseBrokenTrajectoryRecords p r Subtype.val := by
  obtain ⟨k₁, x₁, z₁, hx₁0, hx₁k, hc₁, hne₁, hz₁, hw₁⟩ := hX.mem_morseBrokenTrajectoryRecords.1 h₁
  obtain ⟨k₂, x₂, z₂, hx₂0, hx₂k, hc₂, hne₂, hz₂, hw₂⟩ := hX.mem_morseBrokenTrajectoryRecords.1 h₂
  obtain ⟨x, hx0, hxk, hc, hne, hz⟩ :=
    hX.exists_chain_append (hx₁k.trans hx₂0.symm) hc₁ hc₂ hne₁ hne₂ hz₁ hz₂
  refine hX.mem_morseBrokenTrajectoryRecords.2
    ⟨k₁ + k₂, x, Fin.append z₁ z₂, hx0.trans hx₁0, hxk.trans hx₂k, hc, hne, hz, fun c ↦ ?_⟩
  -- The level `c` is above or below `f q`, and its point is a point of `w₁` or of `w₂`.
  rcases lt_or_gt_of_ne fun h : (c : ℝ) = f q ↦ hq (h ▸ c.property.1) with hcq | hcq
  · obtain ⟨hwc, j, t, ht⟩ := hw₂ ⟨c, c.property.1, c.property.2.1, hcq⟩
    rw [morseRecordConcat_apply_of_gt _ _ c hcq]
    exact ⟨hwc, Fin.natAdd k₁ j, t, by rw [Fin.append_right, ht]⟩
  · obtain ⟨hwc, j, t, ht⟩ := hw₁ ⟨c, c.property.1, hcq, c.property.2.2⟩
    rw [morseRecordConcat_apply_of_lt _ _ c hcq]
    exact ⟨hwc, Fin.castAdd k₂ j, t, by rw [Fin.append_left, ht]⟩

/-- The **concatenation of broken trajectories** at `q`, as a continuous map from pairs of a broken
trajectory from `p` to `q` and one from `q` to `r`, recorded on the levels of `L`, to the broken
trajectories from `p` to `r`. It needs `f q` not to be a level of `L`, which holds when `q` is a
critical point and `L` is made of regular values. -/
noncomputable def morseBrokenTrajectoryConcat (hq : f q ∉ L) :
    C(↥(hX.morseBrokenTrajectoryRecords p q (Subtype.val : ↥(L ∩ Ioo (f q) (f p)) → ℝ)) ×
        ↥(hX.morseBrokenTrajectoryRecords q r (Subtype.val : ↥(L ∩ Ioo (f r) (f q)) → ℝ)),
      ↥(hX.morseBrokenTrajectoryRecords p r (Subtype.val : ↥(L ∩ Ioo (f r) (f p)) → ℝ))) where
  toFun w := ⟨morseRecordConcat f L p q r w.1 w.2,
    hX.morseRecordConcat_mem_morseBrokenTrajectoryRecords hq w.1.property w.2.property⟩
  continuous_toFun := ((continuous_morseRecordConcat p q r).comp
    ((continuous_subtypeVal.comp continuous_fst).prodMk
      (continuous_subtypeVal.comp continuous_snd))).subtype_mk _

/-- The underlying record of a concatenation of broken trajectories is the concatenation of
their records. -/
@[simp]
theorem coe_morseBrokenTrajectoryConcat_apply (hq : f q ∉ L)
    (w : ↥(hX.morseBrokenTrajectoryRecords p q (Subtype.val : ↥(L ∩ Ioo (f q) (f p)) → ℝ)) ×
      ↥(hX.morseBrokenTrajectoryRecords q r (Subtype.val : ↥(L ∩ Ioo (f r) (f q)) → ℝ))) :
    (hX.morseBrokenTrajectoryConcat hq w : ↥(L ∩ Ioo (f r) (f p)) → M) =
      morseRecordConcat f L p q r w.1 w.2 :=
  (rfl)

/-- **Concatenation of broken trajectories is associative.** If neither `f q` nor `f s` is a level
of `L`, concatenating at `q` and then at `s` is concatenating at `s` and then at `q`. -/
theorem morseBrokenTrajectoryConcat_assoc (hq : f q ∉ L) (hs : f s ∉ L)
    (a : ↥(hX.morseBrokenTrajectoryRecords p q (Subtype.val : ↥(L ∩ Ioo (f q) (f p)) → ℝ)))
    (b : ↥(hX.morseBrokenTrajectoryRecords q s (Subtype.val : ↥(L ∩ Ioo (f s) (f q)) → ℝ)))
    (c : ↥(hX.morseBrokenTrajectoryRecords s r (Subtype.val : ↥(L ∩ Ioo (f r) (f s)) → ℝ))) :
    hX.morseBrokenTrajectoryConcat hs (hX.morseBrokenTrajectoryConcat hq (a, b), c) =
      hX.morseBrokenTrajectoryConcat hq (a, hX.morseBrokenTrajectoryConcat hs (b, c)) :=
  Subtype.ext <|
    morseRecordConcat_assoc hq (hX.value_le_of_mem_morseBrokenTrajectoryRecords b.property) _ _ _

/-- **Splitting a broken trajectory at its first breaking point.** Let `L` contain no critical value
of `f`. A broken trajectory from `p` to `r` with at least two components, through the chain
`x 0 = p, x 1, …, x (k + 2) = r`, is the concatenation at `q = x 1` of the unbroken trajectory from
`p` to `q` formed by its first component and the broken trajectory from `q` to `r` formed by the
others. -/
private theorem mem_iUnion_image2_morseRecordConcat_of_chain {k : ℕ} {x : Fin (k + 2 + 1) → M}
    {z : Fin (k + 2) → M} {w : ↥(L ∩ Ioo (f r) (f p)) → M} (hx0 : x 0 = p)
    (hxk : x (Fin.last (k + 2)) = r) (hc : ∀ j, mfderiv 𝓘(ℝ, E) 𝓘(ℝ) f (x j) = 0)
    (hne : ∀ j : Fin (k + 2), x j.castSucc ≠ x j.succ)
    (hz : ∀ j : Fin (k + 2),
      z j ∈ hX.flow.unstableSet (x j.castSucc) ∩ hX.flow.stableSet (x j.succ))
    (hw : ∀ c, f (w c) = c ∧ ∃ j t, hX.flow t (z j) = w c)
    (hL : ∀ y, mfderiv 𝓘(ℝ, E) 𝓘(ℝ) f y = 0 → f y ∉ L) :
    w ∈ ⋃ (q : M) (_ : mfderiv 𝓘(ℝ, E) 𝓘(ℝ) f q = 0 ∧ q ≠ p ∧ q ≠ r),
      image2 (morseRecordConcat f L p q r) (hX.morseTrajectoryRecords p q Subtype.val)
        (hX.morseBrokenTrajectoryRecords q r Subtype.val) := by
  set q := x 1
  have hanti := hX.strictAnti_apply_of_chain hne hz
  have hfq : f q ∈ Ioo (f r) (f p) := by
    rw [← hx0, ← hxk]
    exact ⟨hanti Fin.one_lt_last, hanti Fin.zero_lt_one⟩
  refine mem_iUnion₂.2 ⟨q, ⟨hc 1, fun h ↦ hfq.2.ne (congrArg f h),
    fun h ↦ hfq.1.ne' (congrArg f h)⟩,
    fun c ↦ w ⟨c, c.property.1, hfq.1.trans c.property.2.1, c.property.2.2⟩,
    hX.mem_morseTrajectoryRecords_of_chain hx0 rfl hz (fun _ ↦ hw _) fun c ↦ c.property.2,
    fun c ↦ w ⟨c, c.property.1, c.property.2.1, c.property.2.2.trans hfq.2⟩,
    hX.mem_morseBrokenTrajectoryRecords_of_chain rfl hxk hc hne hz (fun _ ↦ hw _)
      fun c ↦ c.property.2.2,
    funext fun c ↦ ?_⟩
  -- The two parts concatenate to the record, since no level is `f q`.
  · rcases lt_or_gt_of_ne fun h : (c : ℝ) = f q ↦ hL q (hc 1) (h ▸ c.property.1) with h | h
    · rw [morseRecordConcat_apply_of_gt _ _ c h]
    · rw [morseRecordConcat_apply_of_lt _ _ c h]

/-- **A broken trajectory is unbroken, or a concatenation at its first breaking point.** Let `L`
contain no critical value of `f`. A broken trajectory from `p` to `r ≠ p`, recorded on the levels
of `L` strictly between `f r` and `f p`, is either an unbroken trajectory, or the concatenation at
a critical point `q ≠ p, r` of an unbroken trajectory from `p` to `q` and a broken trajectory from
`q` to `r`; conversely all of these are broken trajectories from `p` to `r`. -/
theorem morseBrokenTrajectoryRecords_eq_union (hpr : p ≠ r)
    (hp : mfderiv 𝓘(ℝ, E) 𝓘(ℝ) f p = 0) (hr : mfderiv 𝓘(ℝ, E) 𝓘(ℝ) f r = 0)
    (hL : ∀ y, mfderiv 𝓘(ℝ, E) 𝓘(ℝ) f y = 0 → f y ∉ L) :
    hX.morseBrokenTrajectoryRecords p r (Subtype.val : ↥(L ∩ Ioo (f r) (f p)) → ℝ) =
      hX.morseTrajectoryRecords p r Subtype.val ∪
        ⋃ (q : M) (_ : mfderiv 𝓘(ℝ, E) 𝓘(ℝ) f q = 0 ∧ q ≠ p ∧ q ≠ r),
          image2 (morseRecordConcat f L p q r)
            (hX.morseTrajectoryRecords p q Subtype.val)
            (hX.morseBrokenTrajectoryRecords q r Subtype.val) := by
  refine subset_antisymm ?_ (union_subset
    (hX.morseTrajectoryRecords_subset_morseBrokenTrajectoryRecords hp hr hpr _)
    (iUnion₂_subset fun q ⟨hq, hqp, _⟩ ↦ image2_subset_iff.2 fun w₁ h₁ w₂ h₂ ↦
      hX.morseRecordConcat_mem_morseBrokenTrajectoryRecords (hL q hq)
        (hX.morseTrajectoryRecords_subset_morseBrokenTrajectoryRecords hp hq hqp.symm _ h₁) h₂))
  intro w hw
  obtain ⟨k, x, z, hx0, hxk, hc, hne, hz, hw⟩ := hX.mem_morseBrokenTrajectoryRecords.1 hw
  -- A broken trajectory from `p` to `r ≠ p` has at least one component; with one component it is
  -- unbroken, and otherwise it splits at its first breaking point.
  obtain _ | _ | k := k
  · exact absurd (hx0.symm.trans hxk) hpr
  · exact Or.inl (hX.mem_morseTrajectoryRecords_of_chain hx0 hxk hz hw fun c ↦ c.property.2)
  · exact Or.inr (hX.mem_iUnion_image2_morseRecordConcat_of_chain hx0 hxk hc hne hz hw hL)

/-- **Concatenations are not unbroken.** Let `q ≠ r`, and let `L` have a level strictly between
`f q` and `f p`. Then no concatenation at `q` of a broken trajectory from `p` to `q` and a broken
trajectory from `q` to `r` is an unbroken trajectory from `p` to `r`. -/
theorem disjoint_morseTrajectoryRecords_image2_morseRecordConcat (hqr : q ≠ r)
    (hL : ∃ c ∈ L, c ∈ Ioo (f q) (f p)) :
    Disjoint (hX.morseTrajectoryRecords p r (Subtype.val : ↥(L ∩ Ioo (f r) (f p)) → ℝ))
      (image2 (morseRecordConcat f L p q r) (hX.morseBrokenTrajectoryRecords p q Subtype.val)
        (hX.morseBrokenTrajectoryRecords q r Subtype.val)) := by
  -- On a level between `f q` and `f p`, the concatenation is a point of the first broken
  -- trajectory, which meets no unbroken trajectory to `r` since `f r < f q`.
  refine disjoint_left.2 ?_
  rintro w hw ⟨w₁, h₁, w₂, h₂, rfl⟩
  obtain ⟨c, hcL, hc⟩ := hL
  have hrq := hX.value_lt_of_mem_morseBrokenTrajectoryRecords hqr h₂
  exact hX.apply_ne_of_mem_morseBrokenTrajectoryRecords_of_mem_morseTrajectoryRecords h₁ hw hrq
    ⟨c, hcL, hc⟩ ⟨c, hcL, hrq.trans hc.1, hc.2⟩ (by rw [morseRecordConcat_apply_of_lt _ _ _ hc.1])

end IsAdaptedPseudoGradient

end TauCeti
