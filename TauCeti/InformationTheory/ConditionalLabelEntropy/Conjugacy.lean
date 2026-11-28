/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Dynamics.Ergodic.MeasurePreserving
public import TauCeti.InformationTheory.ConditionalLabelEntropy
import Mathlib.MeasureTheory.Integral.Lebesgue.Map
import TauCeti.Probability.Kernel.Sub

/-!
# Conjugacy invariance of the conditional entropy of labels

The conditional entropy `TauCeti.conditionalLabelEntropy μ a b` of standard-Borel labels is
unchanged when both labels are pulled back along a measure-preserving map
(`TauCeti.conditionalLabelEntropy_comp_of_measurePreserving`). For a measure-preserving
equivalence `s` of `(X, μ)`, the translate of the partition with label `a` by `s` has label
`a ∘ s⁻¹`, and pulling back along `s` gives the inverse formula
`H(a ∘ s⁻¹ | a) = H(a | a ∘ s)` (`TauCeti.conditionalLabelEntropy_comp_symm`).

## References

* G. A. Margulis and G. M. Tomanov, Invariant measures for actions of unipotent groups over local
  fields on homogeneous spaces, Invent. Math. 116 (1994), 347–392, §9.3, pp. 381–383,
  doi:10.1007/BF01231565.
-/

public section

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace TauCeti

variable {X X' Y Z : Type*} {mX : MeasurableSpace X} [MeasurableSpace X'] [MeasurableSpace Y]
  [StandardBorelSpace Y] [Nonempty Y] [MeasurableSpace Z] {μ : Measure X} [IsFiniteMeasure μ]

/-- **Conjugacy invariance.** Pulling both labels back along a measure-preserving map does not
change the conditional entropy. -/
theorem conditionalLabelEntropy_comp_of_measurePreserving {μ' : Measure X'} [IsFiniteMeasure μ']
    {φ : X' → X} (hφ : MeasurePreserving φ μ' μ) {a : X → Y} {b : X → Z}
    (ha : AEMeasurable a μ) (hb : AEMeasurable b μ) :
    conditionalLabelEntropy μ' (a ∘ φ) (b ∘ φ) = conditionalLabelEntropy μ a b := by
  have hμ := hφ.map_eq
  subst hμ
  rw [conditionalLabelEntropy_eq_of_ae_eq (hb.comp_measurable hφ.measurable)
      (condDistrib_map hb ha hφ.aemeasurable),
    conditionalLabelEntropy_def, lintegral_map' _ hφ.aemeasurable]
  · rfl
  · simpa only [Kernel.comap_apply, Function.comp_def] using (measurable_atomInformation.comp
      (((condDistrib a b (μ'.map φ)).comap Prod.fst measurable_fst).measurable_apply_singleton
        measurable_snd)).comp_aemeasurable (hb.prodMk ha)

/-- **The inverse formula.** For a measure-preserving measurable equivalence `s` of `(X, μ)`, the
conditional entropy of the translated label `a ∘ s⁻¹` given `a` equals that of `a` given
`a ∘ s`. -/
theorem conditionalLabelEntropy_comp_symm (s : X ≃ᵐ X) (hs : MeasurePreserving s μ μ)
    {a : X → Y} (ha : AEMeasurable a μ) :
    conditionalLabelEntropy μ (a ∘ s.symm) a = conditionalLabelEntropy μ a (a ∘ s) := by
  rw [← conditionalLabelEntropy_comp_of_measurePreserving hs
    (ha.comp_quasiMeasurePreserving (hs.symm s).quasiMeasurePreserving) ha]
  congr 1
  ext x
  simp

end TauCeti
