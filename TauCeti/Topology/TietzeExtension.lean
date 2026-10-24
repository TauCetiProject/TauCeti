/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.TietzeExtension

/-!
# Tietze extension with prescribed constant values

Let `e : X₁ → X` be a closed embedding into a normal space and let `s` and `t` be disjoint closed
subsets of `X`. A continuous function `f` on `X₁` with values in a space satisfying the Tietze
extension property, equal to `a` on `e ⁻¹' s` and to `b` on `e ⁻¹' t`, extends along `e` to a
continuous function on `X` equal to `a` on all of `s` and to `b` on all of `t`
(`ContinuousMap.exists_extension_eqOn_const`). For `X₁` empty this is Urysohn's lemma.

This relative form of Urysohn's lemma is what proves normality of spaces built by attaching:
a separating function on the old space is extended over the attached space while it separates the
traces of two closed sets there.

## References

* J. R. Munkres, *Topology*, 2nd ed., Prentice Hall (2000), §35, Theorem 35.1.
-/

public section

open Set

namespace ContinuousMap

universe u₁ u v

variable {X₁ : Type u₁} [TopologicalSpace X₁] {X : Type u} [TopologicalSpace X] [NormalSpace X]
  {Y : Type v} [TopologicalSpace Y] [TietzeExtension.{u, v} Y] {e : X₁ → X}

/-- **Tietze extension with prescribed values.** Let `e` be a closed embedding into a normal
space and let `s` and `t` be disjoint closed sets. A continuous function `f` equal to `a` on
`e ⁻¹' s` and to `b` on `e ⁻¹' t` extends along `e` to a continuous function equal to `a` on `s`
and to `b` on `t`. -/
theorem exists_extension_eqOn_const (he : Topology.IsClosedEmbedding e) (f : C(X₁, Y))
    {s t : Set X} (hs : IsClosed s) (ht : IsClosed t) (hst : Disjoint s t) {a b : Y}
    (hfs : EqOn f (fun _ ↦ a) (e ⁻¹' s)) (hft : EqOn f (fun _ ↦ b) (e ⁻¹' t)) :
    ∃ g : C(X, Y), g ∘ e = f ∧ EqOn g (fun _ ↦ a) s ∧ EqOn g (fun _ ↦ b) t := by
  classical
  obtain ⟨g₀, hg₀⟩ := f.exists_extension' he
  -- The function to extend: `a` on `s`, `b` on `t` and `g₀` elsewhere. It is continuous on each
  -- of the closed sets `range e`, `s` and `t`, hence on their union.
  let φ : X → Y := s.piecewise (fun _ ↦ a) (t.piecewise (fun _ ↦ b) g₀)
  have hφs : EqOn φ (fun _ ↦ a) s := fun x hx ↦ by simp [φ, hx]
  have hφt : EqOn φ (fun _ ↦ b) t := fun x hx ↦ by
    simp [φ, hx, hst.notMem_of_mem_right hx]
  have hφe : EqOn φ g₀ (range e) := by
    rintro _ ⟨x, rfl⟩
    have hg₀x : g₀ (e x) = f x := congrFun hg₀ x
    by_cases hs' : e x ∈ s
    · rw [hφs hs', hg₀x, hfs hs']
    by_cases ht' : e x ∈ t
    · rw [hφt ht', hg₀x, hft ht']
    simp [φ, hs', ht']
  have hC : IsClosed (range e ∪ s ∪ t) := (he.isClosed_range.union hs).union ht
  have hφ : ContinuousOn φ (range e ∪ s ∪ t) :=
    ((g₀.continuous.continuousOn.congr hφe).union_of_isClosed
      (continuousOn_const.congr hφs) he.isClosed_range hs).union_of_isClosed
      (continuousOn_const.congr hφt) (he.isClosed_range.union hs) ht
  obtain ⟨g, hg⟩ := (⟨_, hφ.domRestrict⟩ : C(↥(range e ∪ s ∪ t), Y)).exists_restrict_eq hC
  have hgφ : EqOn g φ (range e ∪ s ∪ t) := fun x hx ↦ congr($hg ⟨x, hx⟩)
  refine ⟨g, funext fun x ↦ ?_, fun x hx ↦ ?_, fun x hx ↦ ?_⟩
  · rw [Function.comp_apply, hgφ (.inl (.inl ⟨x, rfl⟩)), hφe ⟨x, rfl⟩, ← hg₀, Function.comp_apply]
  · rw [hgφ (.inl (.inr hx)), hφs hx]
  · rw [hgφ (.inr hx), hφt hx]

end ContinuousMap
