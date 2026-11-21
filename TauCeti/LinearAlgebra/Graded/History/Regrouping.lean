/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.LinearAlgebra.Graded.History.Expansion
import Mathlib.RingTheory.Finiteness.Basic

/-!
# Uniform regrouping along paths of graded modules

Two consecutive propagation blocks can be expanded using finite supports on an
input range, even when their chamber modules and degree sets differ. For the
unrestricted nested sum it suffices to control the second block on the range of
the first composite. For selected histories a stronger support bound is needed:
the second block must be controlled on every retained first-block history.
Cancellation between first-block histories cannot supply that stronger bound.

Finite generation of the input range supplies a rectangular support with this
stronger property. Consequently any incidence-selected expansion of a concatenated
path is a nested sum on the two blocks, simultaneously for all incoming parameters
and after any linear output map. No global finiteness of the gradings is assumed.
The construction reuses `Quiver.Path.exists_uniform_historySupport` and
`Quiver.Path.homogeneousHistory_comp`.

Adapted from `yuma-mizuno-lean/Mei`, commit
`bac6f02d25746bc1c2ec808601d4e9284911c475` (Apache 2.0),
`Mei/LinearAlgebra/GradedModule/History/Path/Regrouping.lean`.
-/

public noncomputable section

namespace Quiver.Path

variable {R Q : Type*} [Semiring R] [Quiver Q]
  {M : Q → Type*} [∀ q, AddCommMonoid (M q)] [∀ q, Module R (M q)]
  (T : ∀ {a b : Q}, (a ⟶ b) → M a →ₗ[R] M b)
  {ι : Q → Type*} [∀ q, DecidableEq (ι q)]
  (ℳ : ∀ q, ι q → Submodule R (M q)) [∀ q, DirectSum.Decomposition (ℳ q)]
  {a b c : Q} (p : Path a b) (q : Path b c)
  {E O : Type*} [AddCommMonoid E] [Module R E] [AddCommMonoid O] [Module R O]
  (f : E →ₗ[R] M a) (g : M c →ₗ[R] O)

/-- Consecutive blocks regroup as an identity of linear maps. The second support
only needs to control the first composite, rather than its individual histories. -/
theorem sum_sum_comp_homogeneousHistory_comp_eq
    (S : Finset (p.Degrees ι)) (U : Finset (q.Degrees ι))
    (hS : ∀ d ∉ S, (p.homogeneousHistory T ℳ d).comp f = 0)
    (hU : ∀ e ∉ U, (q.homogeneousHistory T ℳ e).comp ((p.composeLinear T).comp f) = 0) :
    (∑ e ∈ U, ∑ d ∈ S,
      g.comp ((q.homogeneousHistory T ℳ e).comp
        ((p.homogeneousHistory T ℳ d).comp f))) =
      g.comp (((p.comp q).composeLinear T).comp f) := by
  calc
    _ = ∑ e ∈ U, g.comp ((q.homogeneousHistory T ℳ e).comp
        ((p.composeLinear T).comp f)) := by
      apply Finset.sum_congr rfl
      intro e _
      simpa only [LinearMap.comp_assoc] using
        p.sum_comp_homogeneousHistory_comp_eq T ℳ f
          (g.comp (q.homogeneousHistory T ℳ e)) S hS
    _ = _ := by
      simpa only [composeLinear_comp, LinearMap.comp_assoc] using
        q.sum_comp_homogeneousHistory_comp_eq T ℳ ((p.composeLinear T).comp f) g U hU

open Classical in
/-- Reindex any selected histories on a finite rectangle as histories of the
concatenation. Selection can depend on both blocks and need not factor. -/
theorem sum_ite_comp_homogeneousHistory_comp
    (S : Finset (p.Degrees ι)) (U : Finset (q.Degrees ι))
    (P : p.Degrees ι → q.Degrees ι → Prop) :
    (∑ d ∈ S, ∑ e ∈ U, if P d e then
      g.comp ((q.homogeneousHistory T ℳ e).comp
        ((p.homogeneousHistory T ℳ d).comp f)) else 0) =
      ∑ h ∈ (S ×ˢ U).map (p.degreesComp (ι := ι) q).symm.toEmbedding,
        if P ((p.degreesComp (ι := ι) q) h).1 ((p.degreesComp (ι := ι) q) h).2 then
          g.comp (((p.comp q).homogeneousHistory T ℳ h).comp f) else 0 := by
  classical
  rw [Finset.sum_map, Finset.sum_product]
  apply Finset.sum_congr rfl
  intro d _
  apply Finset.sum_congr rfl
  intro e _
  simp only [Equiv.coe_toEmbedding, Equiv.apply_symm_apply, homogeneousHistory_comp,
    LinearMap.comp_assoc]

/-- A rectangular support for each individual first-block history controls the
concatenation before cancellation. This is the support required for selected sums. -/
theorem homogeneousHistory_comp_eq_zero_of_notMem_rectangle
    (S : Finset (p.Degrees ι)) (U : Finset (q.Degrees ι))
    (hS : ∀ d ∉ S, (p.homogeneousHistory T ℳ d).comp f = 0)
    (hU : ∀ d ∈ S, ∀ e ∉ U,
      (q.homogeneousHistory T ℳ e).comp ((p.homogeneousHistory T ℳ d).comp f) = 0)
    (h : (p.comp q).Degrees ι)
    (hh : h ∉ (S ×ˢ U).map (p.degreesComp (ι := ι) q).symm.toEmbedding) :
    ((p.comp q).homogeneousHistory T ℳ h).comp f = 0 := by
  have hsplit := (p.degreesComp (ι := ι) q).symm_apply_apply h
  rw [← hsplit, homogeneousHistory_comp, LinearMap.comp_assoc]
  by_cases hd : ((p.degreesComp (ι := ι) q) h).1 ∈ S
  · apply hU _ hd
    intro he
    exact hh (Finset.mem_map.mpr
      ⟨(p.degreesComp (ι := ι) q) h, Finset.mem_product.mpr ⟨hd, he⟩, hsplit⟩)
  · rw [hS _ hd, LinearMap.comp_zero]

/-- Finite generation of the incoming range supplies finite supports controlling
every pair of histories separately. In particular this supports arbitrary later
selection by geometric incidence, even when first-block histories cancel. -/
theorem exists_uniform_historySupport_rectangle (hf : (LinearMap.range f).FG) :
    ∃ (S : Finset (p.Degrees ι)) (U : Finset (q.Degrees ι)),
      (∀ d ∉ S, (p.homogeneousHistory T ℳ d).comp f = 0) ∧
      (∀ d ∈ S, ∀ e ∉ U,
        (q.homogeneousHistory T ℳ e).comp ((p.homogeneousHistory T ℳ d).comp f) = 0) := by
  classical
  obtain ⟨S, hS⟩ := p.exists_uniform_historySupport T ℳ f hf
  have hs (d : p.Degrees ι) : ∃ U : Finset (q.Degrees ι), ∀ e ∉ U,
      (q.homogeneousHistory T ℳ e).comp ((p.homogeneousHistory T ℳ d).comp f) = 0 := by
    apply q.exists_uniform_historySupport T ℳ
    rw [LinearMap.range_comp]
    exact hf.map _
  choose U hU using hs
  refine ⟨S, S.biUnion U, hS, fun d hd e he => hU d e ?_⟩
  exact fun hmem => he (Finset.mem_biUnion.mpr ⟨d, hd, hmem⟩)

end Quiver.Path
