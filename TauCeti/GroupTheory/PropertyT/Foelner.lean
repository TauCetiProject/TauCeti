/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.PropertyT.Basic
public import TauCeti.RepresentationTheory.Continuous.LeftRegular.Foelner

/-!
# Følner sets obstruct relative property (T) for infinite subgroups

In a group with Følner sets, the counting-measure regular representation has almost invariant
unit vectors, while its restriction to any infinite subgroup has no nonzero invariant vector.
Lifting the group with `ULift` places the regular Hilbert space in any universe at least that of
the group, so no infinite subgroup of a group with Følner sets has relative property (T). In
particular, an infinite group with Følner sets does not have property (T).

The reference is Bekka–de la Harpe–Valette, *Kazhdan's Property (T)*, Appendix G.5.
-/

public section

open MeasureTheory

namespace Subgroup

universe u v

/-- In a group with Følner sets, no infinite subgroup has relative property (T). Lifting the
group places its regular Hilbert space in `Type (max u v)`, which for `G : Type` is any universe
`Type u`. -/
theorem not_relativePropertyT_of_hasFoelnerSets {G : Type v} [Group G] (Λ : Subgroup G)
    [Infinite Λ] (hG : TauCeti.HasFoelnerSets G) : ¬ Λ.RelativePropertyT.{max u v} := by
  classical
  let G' := ULift.{u} G
  let e : G' ≃* G := MulEquiv.ulift
  let Λ' : Subgroup G' := Λ.map e.symm.toMonoidHom
  have : Infinite Λ' := Infinite.of_injective
    (fun x : Λ ↦ (⟨e.symm x, ⟨x, x.2, rfl⟩⟩ : Λ'))
    fun x y h ↦ Subtype.ext (e.symm.injective (congrArg Subtype.val h))
  let : MeasurableSpace G' := ⊤
  have : DiscreteMeasurableSpace G' := ⟨fun _ ↦ trivial⟩
  let ρ := (Measure.count : Measure G').leftRegular ℂ ℂ 2
  have hG' : TauCeti.HasFoelnerSets G' := e.hasFoelnerSets_iff.mpr hG
  intro hT
  have hT' : Λ'.RelativePropertyT.{max u v} := hT.map e.symm.toMonoidHom
  rw [relativePropertyT_def] at hT'
  obtain ⟨v, hv, hfixed⟩ := hT' (Lp ℂ 2 (Measure.count : Measure G')) ρ
    (Measure.isUnitary_leftRegular Measure.count)
    (Measure.hasAlmostInvariantVectors_count_leftRegular hG')
  have hinv : (ρ.restrict Λ'.subtype).invariants = ⊥ :=
    Measure.invariants_restrict_count_leftRegular Λ' (by simp)
  exact hv (by simpa [hinv] using hfixed)

/-- An infinite group with Følner sets does not have property (T), with Hilbert spaces
quantified in the universe of the group. -/
theorem not_relativePropertyT_top_of_hasFoelnerSets {G : Type u} [Group G] [Infinite G]
    (hG : TauCeti.HasFoelnerSets G) : ¬ (⊤ : Subgroup G).RelativePropertyT.{u} := by
  have : Infinite (⊤ : Subgroup G) :=
    Infinite.of_surjective Subgroup.topEquiv.toEquiv Subgroup.topEquiv.surjective
  exact not_relativePropertyT_of_hasFoelnerSets.{u, u} ⊤ hG

end Subgroup
