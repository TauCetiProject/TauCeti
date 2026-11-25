/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.ModelTheory.RelationalConfiguration.Isomorphism
import TauCeti.GroupTheory.GroupAction.Orbit.Invariant
import TauCeti.ModelTheory.RelationalConfiguration.LanguageMap
import TauCeti.SetTheory.Descriptive.InvariantSeparation

/-!
# Invariant analytic separation for the logic action

For any language on a countable carrier, analytic classes of configurations that share no orbit
admit a measurable invariant separator (`invariant_analytic_separation_of_forall_not_orbitRel`).
In particular, disjoint classes have such a separator when the excluded class is invariant
(`invariant_analytic_separation`). An invariant included class also ensures that disjoint
classes share no orbit. Measurability here means measurability for the product σ-algebra on
configurations. With uncountably many relation symbols this can be strictly smaller than the
Borel σ-algebra of the product topology.

The proof reduces to countably many relation symbols using
`exists_countable_sublanguage_separating_orbits`, applies
`Setoid.exists_invariant_measurableSet_separating` to the analytic orbit relation in the reduct,
and pulls the separator back along the measurable equivariant reduct map.

## References

* R. L. Vaught, *Invariant sets in topology and logic*, Fundamenta Mathematicae **82** (1974),
  269–294, statement (10), p. 281.
-/

public section

universe u v w

open FirstOrder FirstOrder.Language MeasureTheory Set
open scoped Pointwise

namespace TauCeti.RelationalConfiguration

variable {L : Language.{u, v}} {V : Type w} [Countable V]

/-- **Invariant analytic separation for classes sharing no orbit.** In a language of arbitrary
cardinality on a countable carrier, analytic classes that share no orbit are separated by an
invariant measurable set for the product σ-algebra. -/
theorem invariant_analytic_separation_of_forall_not_orbitRel
    {A B : Set (RelationalConfiguration L V)} (hA : AnalyticSet A) (hB : AnalyticSet B)
    (hAB : ∀ a ∈ A, ∀ b ∈ B,
      ¬ MulAction.orbitRel (Equiv.Perm V) (RelationalConfiguration L V) a b) :
    ∃ C : Set (RelationalConfiguration L V), MeasurableSet C ∧
      MulAction.IsInvariantBlock (Equiv.Perm V) C ∧ A ⊆ C ∧ Disjoint C B := by
  obtain ⟨R, hR, hsep⟩ := exists_countable_sublanguage_separating_orbits hA hB hAB
  have : Countable R := hR.to_subtype
  let g := symbSublangIncl (L := L) ∅ R
  let E := MulAction.orbitRel (Equiv.Perm V) (RelationalConfiguration (symbSublang ∅ R) V)
  have hquot : Disjoint (Quotient.mk E '' (g.reductConfiguration '' A))
      (Quotient.mk E '' (g.reductConfiguration '' B)) := by
    rw [← image_comp, ← image_comp]
    exact disjoint_image_image fun a ha b hb hab => hsep a ha b hb (Quotient.exact hab)
  obtain ⟨C₀, hC₀_meas, hC₀_inv, hAC₀, hC₀B⟩ :=
    E.exists_invariant_measurableSet_separating analyticSet_setOf_orbitRel
      (hA.image_of_continuous g.continuous_reductConfiguration)
      (hB.image_of_continuous g.continuous_reductConfiguration) hquot
  have hC₀_action : MulAction.IsInvariantBlock (Equiv.Perm V) C₀ :=
    isInvariantBlock_iff_preimage_image_quotientMk.2 hC₀_inv
  refine ⟨g.reductConfiguration ⁻¹' C₀, hC₀_meas.preimage g.measurable_reductConfiguration,
    ?_, image_subset_iff.1 hAC₀, disjoint_image_right.1 hC₀B⟩
  intro σ
  rintro _ ⟨c, hc, rfl⟩
  rw [mem_preimage, g.reductConfiguration_perm_smul]
  exact hC₀_action σ (smul_mem_smul_set hc)

/-- **Invariant analytic separation for the logic action.** In a language of arbitrary cardinality
on a countable carrier, disjoint analytic classes with the excluded class invariant are separated
by an invariant measurable set for the product σ-algebra. -/
theorem invariant_analytic_separation
    {A B : Set (RelationalConfiguration L V)} (hA : AnalyticSet A) (hB : AnalyticSet B)
    (hB_inv : MulAction.IsInvariantBlock (Equiv.Perm V) B) (hAB : Disjoint A B) :
    ∃ C : Set (RelationalConfiguration L V), MeasurableSet C ∧
      MulAction.IsInvariantBlock (Equiv.Perm V) C ∧ A ⊆ C ∧ Disjoint C B :=
  invariant_analytic_separation_of_forall_not_orbitRel hA hB fun a ha b hb hab => by
    obtain ⟨σ, rfl⟩ := MulAction.mem_orbit_iff.1 (MulAction.orbitRel_apply.1 hab)
    exact disjoint_left.1 hAB ha (hB_inv σ (smul_mem_smul_set hb))

end TauCeti.RelationalConfiguration
