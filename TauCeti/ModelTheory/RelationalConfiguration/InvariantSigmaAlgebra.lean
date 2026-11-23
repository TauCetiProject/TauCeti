/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.MeasurableSpace.Invariants
public import TauCeti.ModelTheory.RelationalConfiguration.LopezEscobar

/-!
# The invariant σ-algebra of the coding space

The **invariant σ-algebra** on `RelationalConfiguration L V` is
`⨅ σ : Equiv.Perm V, MeasurableSpace.invariants (σ • ·)`, the sets measurable for the product
σ-algebra and fixed by the logic action. This file identifies its measurable sets with the
measurable sets that are fixed blocks of the action, for every language and carrier, and, on a
countable carrier in a relational language, with the model classes of `L_{ω₁ω}` sentences. The
second statement is López–Escobar's theorem (`exists_modelsOf_eq_iff`) in its action form.

## Main results

* `TauCeti.RelationalConfiguration.isomorphismInvariant_iff_isFixedBlock`: isomorphism invariance
  is being a fixed block of the logic action.
* `TauCeti.RelationalConfiguration.measurableSet_iInf_invariants_iff`: the measurable sets of the
  invariant σ-algebra are the measurable fixed blocks, for every language and carrier.
* `TauCeti.RelationalConfiguration.lopezEscobar_action_iff`: **López–Escobar's theorem, action
  form**: on a countable carrier, the measurable fixed blocks are the model classes.
* `TauCeti.RelationalConfiguration.measurableSet_iInf_invariants_iff_exists_modelsOf`: on a
  countable carrier, the invariant σ-algebra consists of the model classes.

## References

* R. L. Vaught, *Invariant sets in topology and logic*, Fundamenta Mathematicae **82** (1974),
  269–294, Corollary 3.3.
* D. Marker, *Lectures on Infinitary Model Theory*, Lecture Notes in Logic 46, Cambridge University
  Press, 2016, Theorem 4.26.
-/

public section

universe u v w

open FirstOrder FirstOrder.Language MeasureTheory Set
open scoped Pointwise

namespace TauCeti.RelationalConfiguration

variable {L : Language.{u, v}} {V : Type w} {B : Set (RelationalConfiguration L V)}

/-- In a relational language, a set of configurations is isomorphism invariant exactly when it is a
fixed block of the logic action. -/
theorem isomorphismInvariant_iff_isFixedBlock [L.IsRelational] :
    IsomorphismInvariant B ↔ MulAction.IsFixedBlock (Equiv.Perm V) B := by
  rw [isomorphismInvariant_iff_isInvariantBlock, MulAction.isInvariantBlock_iff_isFixedBlock]

/-- **The invariant σ-algebra.** For every language and carrier, a set of configurations is
measurable for `⨅ σ, MeasurableSpace.invariants (σ • ·)` exactly when it is measurable for the
product σ-algebra and a fixed block of the logic action. -/
theorem measurableSet_iInf_invariants_iff :
    MeasurableSet[⨅ σ : Equiv.Perm V,
        MeasurableSpace.invariants (fun c : RelationalConfiguration L V => σ • c)] B ↔
      MeasurableSet B ∧ MulAction.IsFixedBlock (Equiv.Perm V) B := by
  simp only [MeasurableSpace.measurableSet_iInf, MeasurableSpace.measurableSet_invariants,
    preimage_smul, forall_and, forall_const]
  refine and_congr_right fun _ => ⟨fun h σ => ?_, fun h σ => h σ⁻¹⟩
  simpa only [inv_inv] using h σ⁻¹

/-- **López–Escobar's theorem, action form.** On a countable carrier, in a relational language of
arbitrary cardinality, the sets of configurations that are measurable for the product σ-algebra
and fixed by the logic action are exactly the model classes of `L_{ω₁ω}` sentences. -/
theorem lopezEscobar_action_iff [L.IsRelational] [Countable V] :
    MeasurableSet B ∧ MulAction.IsFixedBlock (Equiv.Perm V) B ↔
      ∃ φ : L.Sentenceω, B = modelsOf φ := by
  rw [← isomorphismInvariant_iff_isFixedBlock, ← exists_modelsOf_eq_iff]
  exact exists_congr fun _ => eq_comm

/-- **The invariant σ-algebra is the definable one.** On a countable carrier, in a relational
language of arbitrary cardinality, the measurable sets of the invariant σ-algebra
`⨅ σ, MeasurableSpace.invariants (σ • ·)` are exactly the model classes of `L_{ω₁ω}` sentences. -/
theorem measurableSet_iInf_invariants_iff_exists_modelsOf [L.IsRelational] [Countable V] :
    MeasurableSet[⨅ σ : Equiv.Perm V,
        MeasurableSpace.invariants (fun c : RelationalConfiguration L V => σ • c)] B ↔
      ∃ φ : L.Sentenceω, B = modelsOf φ := by
  rw [measurableSet_iInf_invariants_iff, lopezEscobar_action_iff]

end TauCeti.RelationalConfiguration
