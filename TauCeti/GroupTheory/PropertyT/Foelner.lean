/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.PropertyT.Basic
public import TauCeti.RepresentationTheory.Continuous.LeftRegular.Foelner
public import TauCeti.GroupTheory.Amenable.Basic

import Mathlib.Algebra.Group.Shrink
import Mathlib.MeasureTheory.Measure.Count
import TauCeti.GroupTheory.Amenable.DiscreteFoelner

/-!
# Følner sets obstruct relative property (T) for infinite subgroups

For a group `G` with Følner sets, the counting-measure left regular representation has almost
invariant unit vectors. Every vector fixed by an infinite subgroup `Λ ≤ G` is constant along each
right coset of `Λ` and therefore vanishes in `ℓ²(G)`. Hence no infinite subgroup of a group with
Følner sets — and in particular no infinite subgroup of an amenable discrete group — has relative
property (T). Taking `Λ = ⊤` recovers the obstruction to property (T) for infinite groups with
Følner sets.

## Main results

* `Subgroup.not_relativePropertyT_of_hasFoelnerSets`: an infinite subgroup of a group `G` with
  Følner sets does not have relative property (T) in any Hilbert-space universe in which `G` is
  `Small`.
* `Subgroup.not_relativePropertyT_of_amenable`: an infinite subgroup of an amenable discrete group
  does not have relative property (T).
* `Subgroup.not_relativePropertyT_top_of_hasFoelnerSets`: an infinite group with Følner sets does
  not have property (T).

## References

* B. Bekka, P. de la Harpe, A. Valette, *Kazhdan's Property (T)*, Appendix G.5.
* C. Anantharaman, S. Popa, *An Introduction to II₁ Factors*, Example 14.2.8.
-/

public section

open MeasureTheory
open scoped ENNReal

namespace Subgroup

universe u v

/-- In a group `G` in universe `u` with Følner sets, the counting-measure regular representation
witnesses failure of relative property (T) for every infinite subgroup `Λ`. -/
private theorem not_relativePropertyT_of_hasFoelnerSets_self {G : Type u} [Group G]
    (hG : TauCeti.HasFoelnerSets G) (Λ : Subgroup G) [Infinite Λ] :
    ¬ Λ.RelativePropertyT.{u} := by
  classical
  let : MeasurableSpace G := ⊤
  let ρ := (Measure.count : Measure G).leftRegular ℂ ℂ 2
  intro hT
  rw [relativePropertyT_def] at hT
  obtain ⟨f, hf, hfixed⟩ := hT (Lp ℂ 2 (Measure.count : Measure G)) ρ
    (Measure.isUnitary_leftRegular Measure.count)
    (Measure.hasAlmostInvariantVectors_count_leftRegular hG)
  refine hf (Lp.ext <| Filter.EventuallyEq.trans (.of_forall fun x ↦ ?_)
    (Lp.coeFn_zero ℂ 2 (Measure.count : Measure G)).symm)
  -- Along the infinite coset `Λ x`, `f` takes the constant value `f x`.
  let s : Set G := Set.range fun h : Λ ↦ (h : G) * x
  have hs_inf : s.Infinite :=
    Set.infinite_range_of_injective ((mul_left_injective x).comp Subtype.val_injective)
  have hconst : ∀ᵐ y ∂Measure.count.restrict s, f y = f x := by
    rw [ae_restrict_iff' (@MeasurableSpace.measurableSet_top G s), Measure.ae_count_iff]
    rintro y ⟨h, rfl⟩
    have hg := Measure.ae_count_iff.mp
      (Measure.coeFn_leftRegular (𝕜 := ℂ) Measure.count 2 (h : G) f) ((h : G) * x)
    have hh : (Measure.count : Measure G).leftRegular ℂ ℂ 2 (h : G) f = f := hfixed h
    rw [hh] at hg
    simpa using hg
  have hc : MemLp (fun _ : G ↦ f x) 2 (Measure.count.restrict s) :=
    (memLp_congr_ae hconst).mp ((Lp.memLp f).restrict s)
  have hs_count : (Measure.count.restrict s) Set.univ = ∞ := by
    simp [Measure.count_apply_infinite hs_inf]
  have hiff := memLp_const_iff (μ := Measure.count.restrict s) (c := f x) (p := 2)
    (by norm_num) (by simp)
  exact (hiff.mp hc).resolve_right (by simp [hs_count])

/-- An infinite subgroup of a group with Følner sets does not have relative property (T), in any
Hilbert-space universe `u` in which the ambient group is `Small`. -/
theorem not_relativePropertyT_of_hasFoelnerSets {G : Type v} [Group G] [Small.{u} G]
    (hG : TauCeti.HasFoelnerSets G) (Λ : Subgroup G) [Infinite Λ] :
    ¬ Λ.RelativePropertyT.{u} := by
  let e : Shrink.{u} G ≃* G := Shrink.mulEquiv
  have hF : TauCeti.HasFoelnerSets (Shrink.{u} G) := e.hasFoelnerSets_iff.mpr hG
  have : Infinite (Λ.map e.symm.toMonoidHom) :=
    Infinite.of_injective (fun x : Λ ↦ ⟨e.symm x, ⟨x, x.2, rfl⟩⟩) fun x y hxy ↦
      Subtype.ext (e.symm.injective (congrArg Subtype.val hxy))
  intro hT
  exact not_relativePropertyT_of_hasFoelnerSets_self hF (Λ.map e.symm.toMonoidHom)
    (hT.map e.symm.toMonoidHom)

/-- An infinite subgroup of an amenable discrete group does not have relative property (T), in any
Hilbert-space universe `u` in which the ambient group is `Small`. -/
theorem not_relativePropertyT_of_amenable {G : Type v} [Group G] [TopologicalSpace G]
    [DiscreteTopology G] [TauCeti.Amenable G] [Small.{u} G] (Λ : Subgroup G) [Infinite Λ] :
    ¬ Λ.RelativePropertyT.{u} :=
  not_relativePropertyT_of_hasFoelnerSets TauCeti.Amenable.hasFoelnerSets Λ

/-- An infinite group with Følner sets does not have property (T), with Hilbert spaces
quantified in the universe of the group. -/
theorem not_relativePropertyT_top_of_hasFoelnerSets {G : Type u} [Group G] [Infinite G]
    (hG : TauCeti.HasFoelnerSets G) : ¬ (⊤ : Subgroup G).RelativePropertyT.{u} := by
  have : Infinite (⊤ : Subgroup G) :=
    Infinite.of_injective (fun g : G ↦ ⟨g, mem_top g⟩) fun _ _ h ↦ congrArg Subtype.val h
  exact not_relativePropertyT_of_hasFoelnerSets hG ⊤

end Subgroup
