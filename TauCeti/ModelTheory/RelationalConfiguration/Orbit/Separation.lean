/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.ModelTheory.RelationalConfiguration.Isomorphism
import TauCeti.ModelTheory.RelationalConfiguration.SublanguageSeparation
import TauCeti.SetTheory.Descriptive.InvariantSeparation

/-!
# Invariant analytic separation for the logic action

For any language on a countable carrier, disjoint analytic classes of configurations admit a
measurable invariant separator when one of the classes is invariant. Measurability here means
the product σ-algebra on configurations. With uncountably many relation symbols this can be
strictly smaller than the Borel σ-algebra of the product topology.

The proof reduces to countably many relation symbols using
`exists_countable_sublanguage_separating_orbits`, applies
`Setoid.exists_invariant_measurableSet_separating` to the analytic orbit relation in the reduct,
and pulls the separator back along the measurable equivariant reduct map. Only the excluded
class needs to be invariant.

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

/-- **Invariant analytic separation for the logic action.** In a language of arbitrary cardinality
on a countable carrier, disjoint analytic classes with the excluded class invariant are separated
by an invariant measurable set for the product σ-algebra. -/
theorem invariant_analytic_separation
    {A B : Set (RelationalConfiguration L V)} (hA : AnalyticSet A) (hB : AnalyticSet B)
    (hB_inv : MulAction.IsInvariantBlock (Equiv.Perm V) B) (hAB : Disjoint A B) :
    ∃ C : Set (RelationalConfiguration L V), MeasurableSet C ∧
      MulAction.IsInvariantBlock (Equiv.Perm V) C ∧ A ⊆ C ∧ Disjoint C B := by
  obtain ⟨R, hR, hsep⟩ := exists_countable_sublanguage_separating_orbits hA hB
    (fun a ha b hb hab => by
      obtain ⟨σ, rfl⟩ := MulAction.mem_orbit_iff.1 (MulAction.orbitRel_apply.1 hab)
      exact disjoint_left.1 hAB ha (hB_inv σ (smul_mem_smul_set hb)))
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
  have hC₀_action : MulAction.IsInvariantBlock (Equiv.Perm V) C₀ := by
    have hsat : (⋃ σ : Equiv.Perm V, σ • C₀) = C₀ := by
      calc
        (⋃ σ : Equiv.Perm V, σ • C₀) =
            Quotient.mk E ⁻¹' (Quotient.mk E '' C₀) := by
          simp only [← image_smul]
          exact (MulAction.quotient_preimage_image_eq_union_mul (G := Equiv.Perm V) C₀).symm
        _ = C₀ := hC₀_inv
    exact fun σ => (subset_iUnion (fun σ : Equiv.Perm V => σ • C₀) σ).trans hsat.le
  refine ⟨g.reductConfiguration ⁻¹' C₀, hC₀_meas.preimage g.measurable_reductConfiguration,
    ?_, fun a ha => hAC₀ ⟨a, ha, rfl⟩, disjoint_left.2 ?_⟩
  · intro σ
    rintro _ ⟨c, hc, rfl⟩
    rw [mem_preimage, g.reductConfiguration_perm_smul]
    exact hC₀_action σ (smul_mem_smul_set hc)
  · exact fun b hbC hb => disjoint_left.1 hC₀B hbC ⟨b, hb, rfl⟩

end TauCeti.RelationalConfiguration
