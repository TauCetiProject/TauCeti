/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Morse.Stable.Stratum
import TauCeti.Data.Fin.Basic

/-!
# Concatenation of broken trajectories

Let `f` be a smooth function on a compact boundaryless manifold `M` and `X` a pseudo-gradient
field adapted to `f`. Fix a family `c : ι → ℝ` of levels of `f`. The trajectories from `p` to `r`
are recorded on the levels of `c` strictly between `f r` and `f p`, as families of points
`w : c ⁻¹' (f r, f p) → M` (`TauCeti.IsAdaptedPseudoGradient.morseTrajectoryRecords`), and so are
the broken trajectories (`TauCeti.IsAdaptedPseudoGradient.morseBrokenTrajectoryRecords`). When `f`
is a Morse function, `X` satisfies the Morse–Smale condition, `c` is a countable family of regular
values and `p ≠ r`, the records of broken trajectories form the compactified space of trajectories
`𝓜(p, r)`, the closure of the records of unbroken ones
(`TauCeti.IsAdaptedPseudoGradient.IsMorseSmale.closure_morseTrajectoryRecords`).

This file equips these spaces with their composition maps. A record `w₁` from `p` to `q` and a
record `w₂` from `q` to `r` are **concatenated** at `q` (`TauCeti.concatLevelRecords`): on a level
above `f q` the concatenation is `w₁`, on a level below `f q` it is `w₂`. A single family `c` of
levels serves all pairs of points, so that the levels on the two sides of `f q` are the levels from
`p` to `r`. Concatenation needs that no level of `c` is the level of `q`, as when `q` is a critical
point and the levels are regular values. Then:

* concatenation is continuous (`TauCeti.continuous_concatLevelRecords`), strictly associative
  (`TauCeti.concatLevelRecords_assoc`), and the records from `p` to `p`, on no level, are units for
  it (`TauCeti.concatLevelRecords_self_left`, `TauCeti.concatLevelRecords_self_right`);
* it sends broken trajectories from `p` to `q` and from `q` to `r` to a broken trajectory from `p`
  to `r` (`TauCeti.IsAdaptedPseudoGradient.concatLevelRecords_mem`), through the two chains of
  critical points put end to end (`TauCeti.IsAdaptedPseudoGradient.chain_concatLevelRecords`);
* every broken trajectory from `p` to `r ≠ p` is either unbroken or the concatenation at its first
  breaking point `q` of an unbroken trajectory from `p` to `q` and a broken trajectory from `q` to
  `r` (`TauCeti.IsAdaptedPseudoGradient.morseBrokenTrajectoryRecords_eq_union`);
* if `c` has a level strictly between `f q` and `f p`, no concatenation at `q ≠ r` is unbroken
  (`TauCeti.IsAdaptedPseudoGradient.concatLevelRecords_notMem_morseTrajectoryRecords`).

So when `c` has a level between any two critical values, the broken trajectories from `p` to
`r ≠ p` that are not unbroken are exactly the union, over the critical points `q ≠ p, r`, of the
images of the concatenation maps `𝓜(p, q) × 𝓜(q, r) → 𝓜(p, r)`. Bundled as continuous maps
between the spaces of broken trajectories (`TauCeti.IsAdaptedPseudoGradient.morseRecordsConcat`),
associative as well (`TauCeti.IsAdaptedPseudoGradient.morseRecordsConcat_assoc`), these are the
maps from which the composition maps of the compactified trajectory spaces of Barraud and Cornea
are built, on which twisting chain systems (`TauCeti.TwistingChainSystem`) live.

## Main definitions

* `TauCeti.concatLevelRecords`: the concatenation of records at a point `q`.
* `TauCeti.IsAdaptedPseudoGradient.morseRecordsConcat`: the concatenation of broken trajectories at
  a point `q`, as a continuous map.

## Main results

* `TauCeti.continuous_concatLevelRecords`: concatenation is continuous.
* `TauCeti.concatLevelRecords_assoc`: concatenation is associative.
* `TauCeti.IsAdaptedPseudoGradient.concatLevelRecords_mem`: the concatenation of broken
  trajectories is a broken trajectory.
* `TauCeti.IsAdaptedPseudoGradient.morseRecordsConcat_assoc`: concatenation of broken trajectories
  is associative.
* `TauCeti.IsAdaptedPseudoGradient.morseBrokenTrajectoryRecords_eq_union`: a broken trajectory is
  unbroken or a concatenation at its first breaking point.
* `TauCeti.IsAdaptedPseudoGradient.concatLevelRecords_notMem_morseTrajectoryRecords`: if `q ≠ r`
  and `c` has a level strictly between `f q` and `f p`, concatenations at `q` are not unbroken.

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

variable {M : Type*} {f : M → ℝ} {ι : Type*} {p q r : M} {c : ι → ℝ}

variable (c) in
/-- **Concatenation of records.** Records `w₁` on the levels of `c` between `f q` and `f p` and
`w₂` on those between `f r` and `f q`, none of which is the level of `q`, give the record on the
levels between `f r` and `f p` that is `w₁` above the level of `q` and `w₂` below it. -/
noncomputable def concatLevelRecords (hq : ∀ i, c i ≠ f q) (w₁ : c ⁻¹' Ioo (f q) (f p) → M)
    (w₂ : c ⁻¹' Ioo (f r) (f q) → M) (i : c ⁻¹' Ioo (f r) (f p)) : M :=
  if h : f q < c i then w₁ ⟨i, h, i.property.2⟩
  else w₂ ⟨i, i.property.1, lt_of_le_of_ne (not_lt.1 h) (hq i)⟩

variable (hq : ∀ i, c i ≠ f q) (w₁ : c ⁻¹' Ioo (f q) (f p) → M) (w₂ : c ⁻¹' Ioo (f r) (f q) → M)

/-- Above the level of `q`, a concatenation of records is the first record. -/
theorem concatLevelRecords_of_lt {i : c ⁻¹' Ioo (f r) (f p)} (h : f q < c i) :
    concatLevelRecords c hq w₁ w₂ i = w₁ ⟨i, h, i.property.2⟩ := by
  simp only [concatLevelRecords, h, ↓reduceDIte]

/-- Below the level of `q`, a concatenation of records is the second record. -/
theorem concatLevelRecords_of_gt {i : c ⁻¹' Ioo (f r) (f p)} (h : c i < f q) :
    concatLevelRecords c hq w₁ w₂ i = w₂ ⟨i, i.property.1, h⟩ := by
  simp only [concatLevelRecords, h.not_gt, ↓reduceDIte]

/-- **The values of a concatenation of records are those of the two records.** If every value of
`w₁` and every value of `w₂` satisfies `P` at its level, so does every value of their
concatenation. -/
theorem concatLevelRecords_induction {P : ι → M → Prop}
    (h₁ : ∀ i : c ⁻¹' Ioo (f q) (f p), P i (w₁ i)) (h₂ : ∀ i : c ⁻¹' Ioo (f r) (f q), P i (w₂ i))
    (i : c ⁻¹' Ioo (f r) (f p)) : P i (concatLevelRecords c hq w₁ w₂ i) := by
  by_cases h : f q < c i
  · rw [concatLevelRecords_of_lt hq w₁ w₂ h]
    exact h₁ ⟨i, h, i.property.2⟩
  · rw [concatLevelRecords_of_gt hq w₁ w₂ (lt_of_le_of_ne (not_lt.1 h) (hq i))]
    exact h₂ ⟨i, i.property.1, lt_of_le_of_ne (not_lt.1 h) (hq i)⟩

/-- **Concatenation at the source is trivial.** No level lies strictly between `f p` and itself, so
concatenating at `p` returns the second record. -/
@[simp]
theorem concatLevelRecords_self_left (hp : ∀ i, c i ≠ f p) (w₁ : c ⁻¹' Ioo (f p) (f p) → M)
    (w₂ : c ⁻¹' Ioo (f r) (f p) → M) : concatLevelRecords c hp w₁ w₂ = w₂ :=
  funext fun i ↦ concatLevelRecords_of_gt hp w₁ w₂ i.property.2

/-- **Concatenation at the target is trivial.** No level lies strictly between `f r` and itself, so
concatenating at `r` returns the first record. -/
@[simp]
theorem concatLevelRecords_self_right (hr : ∀ i, c i ≠ f r) (w₁ : c ⁻¹' Ioo (f r) (f p) → M)
    (w₂ : c ⁻¹' Ioo (f r) (f r) → M) : concatLevelRecords c hr w₁ w₂ = w₁ :=
  funext fun i ↦ concatLevelRecords_of_lt hr w₁ w₂ i.property.1

/-- **Concatenation of records is associative.** If `f s ≤ f q` and no level of `c` is the level
of `q` or of `s`, concatenating at `q` and then at `s` is concatenating at `s` and then at `q`. -/
theorem concatLevelRecords_assoc {s : M} (hs : ∀ i, c i ≠ f s) (hsq : f s ≤ f q)
    (a : c ⁻¹' Ioo (f q) (f p) → M) (b : c ⁻¹' Ioo (f s) (f q) → M)
    (d : c ⁻¹' Ioo (f r) (f s) → M) :
    concatLevelRecords c hs (concatLevelRecords c hq a b) d =
      concatLevelRecords c hq a (concatLevelRecords c hs b d) := by
  funext i
  -- Compare the level `c i` with `f q` and `f s`; it is neither of them.
  have := hq i
  have := hs i
  simp only [concatLevelRecords]
  split_ifs <;> first | rfl | (exfalso; grind)

/-- Concatenation of records is continuous. -/
@[fun_prop]
theorem continuous_concatLevelRecords [TopologicalSpace M] :
    Continuous fun w : (c ⁻¹' Ioo (f q) (f p) → M) × (c ⁻¹' Ioo (f r) (f q) → M) ↦
      concatLevelRecords c hq w.1 w.2 :=
  continuous_pi fun i ↦ by
    by_cases h : f q < c i
    · simp only [concatLevelRecords, h, ↓reduceDIte]
      exact (continuous_apply _).comp continuous_fst
    · simp only [concatLevelRecords, h, ↓reduceDIte]
      exact (continuous_apply _).comp continuous_snd

end Concat

/-! ### Concatenation of broken trajectories -/

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [CompactSpace M] [T2Space M]
  {f : M → ℝ} {X : (x : M) → TangentSpace 𝓘(ℝ, E) x} {ι : Type*}

namespace IsAdaptedPseudoGradient

variable (hX : IsAdaptedPseudoGradient f X)

section Concat

variable {p q r : M} {c : ι → ℝ} (hq : ∀ i, c i ≠ f q) {w₁ : c ⁻¹' Ioo (f q) (f p) → M}
  {w₂ : c ⁻¹' Ioo (f r) (f q) → M}

variable {hX} in
/-- **The concatenation of records lies on the glued broken trajectory.** If the points of `w₁`
lie on the orbits of the points `z₁ j` and those of `w₂` on the orbits of the points `z₂ j`, the
points of their concatenation lie on the orbits of the points `Fin.append z₁ z₂ j`, the
trajectories of the two broken trajectories put end to end. -/
theorem exists_flow_append_eq_concatLevelRecords {k₁ k₂ : ℕ} {z₁ : Fin k₁ → M} {z₂ : Fin k₂ → M}
    (h₁ : ∀ i, ∃ j t, hX.flow t (z₁ j) = w₁ i) (h₂ : ∀ i, ∃ j t, hX.flow t (z₂ j) = w₂ i)
    (i : c ⁻¹' Ioo (f r) (f p)) :
    ∃ j t, hX.flow t (Fin.append z₁ z₂ j) = concatLevelRecords c hq w₁ w₂ i :=
  concatLevelRecords_induction (P := fun _ m ↦ ∃ j t, hX.flow t (Fin.append z₁ z₂ j) = m) hq w₁ w₂
    (fun i ↦ (h₁ i).elim fun j h ↦ ⟨Fin.castAdd k₂ j, by rwa [Fin.append_left]⟩)
    (fun i ↦ (h₂ i).elim fun j h ↦ ⟨Fin.natAdd k₁ j, by rwa [Fin.append_right]⟩) i

variable {hX} in
/-- **The glued chain of two broken trajectories records their concatenation.** If `w₁` is
recorded along the chain `x₁` of critical points from `p` to `q`, joined by the orbits of the
points `z₁ j`, and `w₂` along the chain `x₂` from `q` to `r`, joined by the orbits of the points
`z₂ j`, then the concatenation of `w₁` and `w₂` is recorded along the chain
`Fin.append (Fin.init x₁) x₂` from `p` to `r`, joined by the orbits of the points
`Fin.append z₁ z₂`. -/
theorem chain_concatLevelRecords {k₁ : ℕ} {x₁ : Fin (k₁ + 1) → M} {z₁ : Fin k₁ → M}
    (hx0₁ : x₁ 0 = p) (hxk₁ : x₁ (Fin.last k₁) = q)
    (hxc₁ : ∀ j, mfderiv 𝓘(ℝ, E) 𝓘(ℝ) f (x₁ j) = 0)
    (hxne₁ : ∀ j : Fin k₁, x₁ j.castSucc ≠ x₁ j.succ)
    (hz₁ : ∀ j : Fin k₁, z₁ j ∈ hX.flow.unstableSet (x₁ j.castSucc) ∩ hX.flow.stableSet (x₁ j.succ))
    (hw₁ : ∀ i, f (w₁ i) = c i ∧ ∃ j t, hX.flow t (z₁ j) = w₁ i)
    {k₂ : ℕ} {x₂ : Fin (k₂ + 1) → M} {z₂ : Fin k₂ → M} (hx0₂ : x₂ 0 = q)
    (hxk₂ : x₂ (Fin.last k₂) = r) (hxc₂ : ∀ j, mfderiv 𝓘(ℝ, E) 𝓘(ℝ) f (x₂ j) = 0)
    (hxne₂ : ∀ j : Fin k₂, x₂ j.castSucc ≠ x₂ j.succ)
    (hz₂ : ∀ j : Fin k₂, z₂ j ∈ hX.flow.unstableSet (x₂ j.castSucc) ∩ hX.flow.stableSet (x₂ j.succ))
    (hw₂ : ∀ i, f (w₂ i) = c i ∧ ∃ j t, hX.flow t (z₂ j) = w₂ i) :
    Fin.append (Fin.init x₁) x₂ (0 : Fin (k₁ + k₂ + 1)) = p ∧
      Fin.append (Fin.init x₁) x₂ (Fin.last (k₁ + k₂)) = r ∧
      (∀ j : Fin (k₁ + k₂ + 1), mfderiv 𝓘(ℝ, E) 𝓘(ℝ) f (Fin.append (Fin.init x₁) x₂ j) = 0) ∧
      (∀ j : Fin (k₁ + k₂),
        Fin.append (Fin.init x₁) x₂ j.castSucc ≠ Fin.append (Fin.init x₁) x₂ j.succ) ∧
      (∀ j : Fin (k₁ + k₂), Fin.append z₁ z₂ j ∈
        hX.flow.unstableSet (Fin.append (Fin.init x₁) x₂ j.castSucc) ∩
          hX.flow.stableSet (Fin.append (Fin.init x₁) x₂ j.succ)) ∧
      ∀ i, f (concatLevelRecords c hq w₁ w₂ i) = c i ∧
        ∃ j t, hX.flow t (Fin.append z₁ z₂ j) = concatLevelRecords c hq w₁ w₂ i := by
  -- The broken trajectory runs through the first one up to `q`, and then through the second one.
  have h₁₂ : x₁ (Fin.last k₁) = x₂ 0 := hxk₁.trans hx0₂.symm
  refine ⟨(Fin.append_init_zero h₁₂).trans hx0₁, Fin.append_init_last.trans hxk₂, fun l ↦ ?_,
    Fin.forall_append_init_castSucc_succ (z₁ := z₁) (z₂ := z₂) (P := fun a b _ ↦ a ≠ b) h₁₂
      hxne₁ hxne₂,
    Fin.forall_append_init_castSucc_succ
      (P := fun a b y ↦ y ∈ hX.flow.unstableSet a ∩ hX.flow.stableSet b) h₁₂ hz₁ hz₂,
    fun i ↦ ⟨concatLevelRecords_induction (P := fun i m ↦ f m = c i) hq w₁ w₂
      (fun i ↦ (hw₁ i).1) (fun i ↦ (hw₂ i).1) i,
      exists_flow_append_eq_concatLevelRecords hq (fun i ↦ (hw₁ i).2) (fun i ↦ (hw₂ i).2) i⟩⟩
  rcases Fin.append_init_eq_or_eq l with ⟨l₁, h⟩ | ⟨l₂, h⟩
  · exact h ▸ hxc₁ l₁
  · exact h ▸ hxc₂ l₂

variable (hw₁ : w₁ ∈ hX.morseBrokenTrajectoryRecords p q ((c ⁻¹' Ioo (f q) (f p)).domRestrict c))
  (hw₂ : w₂ ∈ hX.morseBrokenTrajectoryRecords q r ((c ⁻¹' Ioo (f r) (f q)).domRestrict c))
include hw₁ hw₂

/-- **The concatenation of records of broken trajectories records a broken trajectory**, through
the two chains of critical points put end to end. -/
theorem concatLevelRecords_mem :
    concatLevelRecords c hq w₁ w₂ ∈
      hX.morseBrokenTrajectoryRecords p r ((c ⁻¹' Ioo (f r) (f p)).domRestrict c) := by
  obtain ⟨k₁, x₁, z₁, hx0₁, hxk₁, hxc₁, hxne₁, hz₁, hrec₁⟩ :=
    hX.mem_morseBrokenTrajectoryRecords.1 hw₁
  obtain ⟨k₂, x₂, z₂, hx0₂, hxk₂, hxc₂, hxne₂, hz₂, hrec₂⟩ :=
    hX.mem_morseBrokenTrajectoryRecords.1 hw₂
  exact hX.mem_morseBrokenTrajectoryRecords.2 ⟨k₁ + k₂, (Fin.append (Fin.init x₁) x₂ :), _,
    chain_concatLevelRecords hq hx0₁ hxk₁ hxc₁ hxne₁ hz₁ hrec₁ hx0₂ hxk₂ hxc₂ hxne₂ hz₂ hrec₂⟩

/-- **Concatenations are not unbroken.** If `q ≠ r` and some level of `c` lies strictly between
`f q` and `f p`, the concatenation at `q` of records of broken trajectories from `p` to `q` and
from `q` to `r` is not the record of an unbroken trajectory from `p` to `r`. -/
theorem concatLevelRecords_notMem_morseTrajectoryRecords (hqr : q ≠ r) {i₀ : ι}
    (hi₀ : c i₀ ∈ Ioo (f q) (f p)) :
    concatLevelRecords c hq w₁ w₂ ∉
      hX.morseTrajectoryRecords p r ((c ⁻¹' Ioo (f r) (f p)).domRestrict c) := by
  intro hw
  -- On the level `c i₀`, the concatenation is a point of the first broken trajectory, which meets
  -- no unbroken trajectory to `r` since `f r < f q`.
  have hrq := hX.value_lt_of_mem_morseBrokenTrajectoryRecords hqr hw₂
  exact hX.apply_ne_of_mem_morseBrokenTrajectoryRecords_of_mem_morseTrajectoryRecords hw₁ hw hrq
    ⟨i₀, hi₀⟩ ⟨i₀, hrq.trans hi₀.1, hi₀.2⟩ (by rw [concatLevelRecords_of_lt hq w₁ w₂ hi₀.1])

end Concat

section ConcatMap

variable {p q r : M} {c : ι → ℝ}

/-- **Concatenation of records of broken trajectories**, as a continuous map from pairs of records
of broken trajectories from `p` to `q` and from `q` to `r` to records of broken trajectories from
`p` to `r`, on the levels of `c` between the levels of the ends. -/
noncomputable def morseRecordsConcat (hq : ∀ i, c i ≠ f q) :
    C(hX.morseBrokenTrajectoryRecords p q ((c ⁻¹' Ioo (f q) (f p)).domRestrict c) ×
        hX.morseBrokenTrajectoryRecords q r ((c ⁻¹' Ioo (f r) (f q)).domRestrict c),
      hX.morseBrokenTrajectoryRecords p r ((c ⁻¹' Ioo (f r) (f p)).domRestrict c)) where
  toFun w := ⟨concatLevelRecords c hq w.1.val w.2.val,
    hX.concatLevelRecords_mem hq w.1.property w.2.property⟩
  continuous_toFun := ((continuous_concatLevelRecords hq).comp
    (continuous_subtypeVal.prodMap continuous_subtypeVal)).subtype_mk _

/-- The record underlying a concatenation of records. -/
@[simp]
theorem coe_morseRecordsConcat (hq : ∀ i, c i ≠ f q)
    (w : hX.morseBrokenTrajectoryRecords p q ((c ⁻¹' Ioo (f q) (f p)).domRestrict c) ×
      hX.morseBrokenTrajectoryRecords q r ((c ⁻¹' Ioo (f r) (f q)).domRestrict c)) :
    (hX.morseRecordsConcat hq w : _ → M) = concatLevelRecords c hq w.1.val w.2.val :=
  (rfl)

/-- **Concatenation of broken trajectories is associative.** If no level of `c` is the level of
`q` or of `s`, concatenating at `q` and then at `s` is concatenating at `s` and then at `q`. -/
theorem morseRecordsConcat_assoc {s : M} (hq : ∀ i, c i ≠ f q) (hs : ∀ i, c i ≠ f s)
    (a : hX.morseBrokenTrajectoryRecords p q ((c ⁻¹' Ioo (f q) (f p)).domRestrict c))
    (b : hX.morseBrokenTrajectoryRecords q s ((c ⁻¹' Ioo (f s) (f q)).domRestrict c))
    (d : hX.morseBrokenTrajectoryRecords s r ((c ⁻¹' Ioo (f r) (f s)).domRestrict c)) :
    hX.morseRecordsConcat hs (hX.morseRecordsConcat hq (a, b), d) =
      hX.morseRecordsConcat hq (a, hX.morseRecordsConcat hs (b, d)) :=
  Subtype.ext <| concatLevelRecords_assoc hq hs
    (hX.value_le_of_mem_morseBrokenTrajectoryRecords b.property) _ _ _

end ConcatMap

/-! ### Splitting a broken trajectory at its first breaking point -/

section Split

variable {p r : M} {c : ι → ℝ}

/-- **Splitting a broken trajectory at its first breaking point.** Let no level of `c` be a
critical value of `f`. A broken trajectory from `p` to `r` with at least two components, through
the chain `x 0 = p, x 1, …, x (k + 2) = r`, is the concatenation at `q = x 1` of the unbroken
trajectory from `p` to `q` formed by its first component and the broken trajectory from `q` to `r`
formed by the others. -/
private theorem mem_iUnion_image2_concatLevelRecords_of_chain {k : ℕ} {x : Fin (k + 2 + 1) → M}
    {z : Fin (k + 2) → M} {w : c ⁻¹' Ioo (f r) (f p) → M} (hx0 : x 0 = p)
    (hxk : x (Fin.last (k + 2)) = r) (hxc : ∀ j, mfderiv 𝓘(ℝ, E) 𝓘(ℝ) f (x j) = 0)
    (hne : ∀ j : Fin (k + 2), x j.castSucc ≠ x j.succ)
    (hz : ∀ j : Fin (k + 2),
      z j ∈ hX.flow.unstableSet (x j.castSucc) ∩ hX.flow.stableSet (x j.succ))
    (hw : ∀ i, f (w i) = c i ∧ ∃ j t, hX.flow t (z j) = w i)
    (hc : ∀ y, mfderiv 𝓘(ℝ, E) 𝓘(ℝ) f y = 0 → ∀ i, c i ≠ f y) :
    w ∈ ⋃ (q : M) (hq : mfderiv 𝓘(ℝ, E) 𝓘(ℝ) f q = 0 ∧ q ≠ p ∧ q ≠ r),
      image2 (concatLevelRecords c (hc q hq.1))
        (hX.morseTrajectoryRecords p q ((c ⁻¹' Ioo (f q) (f p)).domRestrict c))
        (hX.morseBrokenTrajectoryRecords q r ((c ⁻¹' Ioo (f r) (f q)).domRestrict c)) := by
  set q := x 1
  have hanti := hX.strictAnti_apply_of_chain hne hz
  have hfq : f q ∈ Ioo (f r) (f p) := by
    rw [← hx0, ← hxk]
    exact ⟨hanti Fin.one_lt_last, hanti Fin.zero_lt_one⟩
  refine mem_iUnion₂.2 ⟨q, ⟨hxc 1, fun h ↦ hfq.2.ne (congrArg f h),
    fun h ↦ hfq.1.ne' (congrArg f h)⟩,
    fun i ↦ w ⟨i, hfq.1.trans i.property.1, i.property.2⟩,
    hX.mem_morseTrajectoryRecords_of_chain hx0 rfl hz (fun _ ↦ hw _) fun i ↦ i.property,
    fun i ↦ w ⟨i, i.property.1, i.property.2.trans hfq.2⟩,
    hX.mem_morseBrokenTrajectoryRecords_of_chain rfl hxk hxc hne hz (fun _ ↦ hw _)
      fun i ↦ i.property.2,
    funext fun i ↦ ?_⟩
  -- The two parts concatenate to the record, since no level is `f q`.
  · rcases lt_or_gt_of_ne (hc q (hxc 1) i) with h | h
    · rw [concatLevelRecords_of_gt _ _ _ h]
    · rw [concatLevelRecords_of_lt _ _ _ h]

/-- **A broken trajectory is unbroken, or a concatenation at its first breaking point.** Let no
level of `c` be a critical value of `f`. A broken trajectory from `p` to `r ≠ p`, recorded on the
levels of `c` strictly between `f r` and `f p`, is either an unbroken trajectory, or the
concatenation at a critical point `q ≠ p, r` of an unbroken trajectory from `p` to `q` and a broken
trajectory from `q` to `r`; conversely all of these are broken trajectories from `p` to `r`. -/
theorem morseBrokenTrajectoryRecords_eq_union (hpr : p ≠ r)
    (hp : mfderiv 𝓘(ℝ, E) 𝓘(ℝ) f p = 0) (hr : mfderiv 𝓘(ℝ, E) 𝓘(ℝ) f r = 0)
    (hc : ∀ y, mfderiv 𝓘(ℝ, E) 𝓘(ℝ) f y = 0 → ∀ i, c i ≠ f y) :
    hX.morseBrokenTrajectoryRecords p r ((c ⁻¹' Ioo (f r) (f p)).domRestrict c) =
      hX.morseTrajectoryRecords p r ((c ⁻¹' Ioo (f r) (f p)).domRestrict c) ∪
        ⋃ (q : M) (hq : mfderiv 𝓘(ℝ, E) 𝓘(ℝ) f q = 0 ∧ q ≠ p ∧ q ≠ r),
          image2 (concatLevelRecords c (hc q hq.1))
            (hX.morseTrajectoryRecords p q ((c ⁻¹' Ioo (f q) (f p)).domRestrict c))
            (hX.morseBrokenTrajectoryRecords q r ((c ⁻¹' Ioo (f r) (f q)).domRestrict c)) := by
  refine subset_antisymm ?_ (union_subset
    (hX.morseTrajectoryRecords_subset_morseBrokenTrajectoryRecords hp hr hpr _)
    (iUnion₂_subset fun q ⟨hq, hqp, _⟩ ↦ image2_subset_iff.2 fun w₁ h₁ w₂ h₂ ↦
      hX.concatLevelRecords_mem (hc q hq)
        (hX.morseTrajectoryRecords_subset_morseBrokenTrajectoryRecords hp hq hqp.symm _ h₁) h₂))
  intro w hw
  obtain ⟨k, x, z, hx0, hxk, hxc, hne, hz, hw⟩ := hX.mem_morseBrokenTrajectoryRecords.1 hw
  -- A broken trajectory from `p` to `r ≠ p` has at least one component; with one component it is
  -- unbroken, and otherwise it splits at its first breaking point.
  obtain _ | _ | k := k
  · exact absurd (hx0.symm.trans hxk) hpr
  · exact Or.inl (hX.mem_morseTrajectoryRecords_of_chain hx0 hxk hz hw fun i ↦ i.property)
  · exact Or.inr (hX.mem_iUnion_image2_concatLevelRecords_of_chain hx0 hxk hxc hne hz hw hc)

end Split

end IsAdaptedPseudoGradient

end TauCeti
