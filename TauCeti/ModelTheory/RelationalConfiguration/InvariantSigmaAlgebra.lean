/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.ModelTheory.RelationalConfiguration.LopezEscobar
public import TauCeti.MeasureTheory.MeasurableSpace.Invariants

/-!
# The invariant σ-algebra of the coding space

The **invariant σ-algebra** on `RelationalConfiguration L V` is
`⨅ σ : Equiv.Perm V, MeasurableSpace.invariants (σ • ·)`, the sets measurable for the product
σ-algebra and fixed by the logic action. This file identifies its measurable sets, on a countable
carrier in a relational language, with the model classes of `L_{ω₁ω}` sentences: this is
López–Escobar's theorem (`exists_modelsOf_eq_iff`) in its action form.

## Main results

* `TauCeti.RelationalConfiguration.measurableSet_iInf_invariants_iff_exists_modelsOf`: on a
  countable carrier, the invariant σ-algebra consists of the model classes. It combines the general
  description of the invariant σ-algebra of a group action
  (`TauCeti.measurableSet_iInf_invariants_iff`) with the action form of López–Escobar's theorem
  (`TauCeti.RelationalConfiguration.lopezEscobar_action_iff`).

## References

* R. L. Vaught, *Invariant sets in topology and logic*, Fundamenta Mathematicae **82** (1974),
  269–294, Corollary 3.3.
* D. Marker, *Lectures on Infinitary Model Theory*, Lecture Notes in Logic 46, Cambridge University
  Press, 2016, Theorem 4.2.7.
-/

public section

universe u v w

open FirstOrder FirstOrder.Language MeasureTheory Set
open scoped Pointwise

namespace TauCeti.RelationalConfiguration

variable {L : Language.{u, v}} {V : Type w} {B : Set (RelationalConfiguration L V)}

/-- **The invariant σ-algebra is the definable one.** On a countable carrier, in a relational
language of arbitrary cardinality, the measurable sets of the invariant σ-algebra
`⨅ σ, MeasurableSpace.invariants (σ • ·)` are exactly the model classes of `L_{ω₁ω}` sentences. -/
theorem measurableSet_iInf_invariants_iff_exists_modelsOf [L.IsRelational] [Countable V] :
    MeasurableSet[⨅ σ : Equiv.Perm V,
        MeasurableSpace.invariants (fun c : RelationalConfiguration L V => σ • c)] B ↔
      ∃ φ : L.Sentenceω, B = modelsOf φ := by
  rw [TauCeti.measurableSet_iInf_invariants_iff, lopezEscobar_action_iff]

end TauCeti.RelationalConfiguration
