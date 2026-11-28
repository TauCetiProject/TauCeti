/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import TauCeti.NumberTheory.Padics.Cohomology
import TauCeti.RepresentationTheory.Homological.ContCohomology.Coefficients.Localization.Padic
import TauCeti.RingTheory.TensorProduct.IsBaseChange

/-!
# Checks: rationalisation of lattice cohomology

Checks that the hypotheses of `TauCeti.ContinuousCohomology.rationalizationEquiv` are met by the
inclusion `ℤ_p → ℚ_p` with the trivial action of a compact group `G`, so that
`ℚ_p ⊗[ℤ_p] Hⁿ(G, ℤ_p) ≃ Hⁿ(G, ℚ_p)` in every degree.

For `G = ℤ_p` with the trivial action, first cohomology is computed on both sides of the
comparison: `H¹(ℤ_p, ℤ_p) = ℤ_p` and `H¹(ℤ_p, ℚ_p) = Hom_cts(ℤ_p, ℚ_p) = ℚ_p`, by evaluation of
a continuous character at `1` (`TauCeti.padicIntH1LinearEquiv`).
-/

open CategoryTheory TauCeti.ContinuousCohomology
open scoped TensorProduct

variable (p : ℕ) [Fact p.Prime] (G : Type) [Group G]

/-- The inclusion `ℤ_p → ℚ_p` of trivial representations of a compact group satisfies the
hypotheses of `rationalizationEquiv`: its scalar extension `ℚ_p ⊗ ℤ_p → ℚ_p` is bijective. -/
noncomputable example [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] (n : ℕ) :
    ℚ_[p] ⊗[ℤ_[p]] continuousCohomology n (TopRep.of (ContRepresentation.trivial ℤ_[p] G ℤ_[p]))
      ≃ₗ[ℤ_[p]] continuousCohomology n (TopRep.of (ContRepresentation.trivial ℤ_[p] G ℚ_[p])) :=
  rationalizationEquiv
    (ι := (TopRep.ofHom
      { toLinearMap := Algebra.linearMap ℤ_[p] ℚ_[p]
        cont := continuous_subtypeVal
        isIntertwining' _ := rfl } :
      TopRep.of (ContRepresentation.trivial ℤ_[p] G ℤ_[p]) ⟶
        TopRep.of (ContRepresentation.trivial ℤ_[p] G ℚ_[p])))
    (IsBaseChange.linearMap ℤ_[p] ℚ_[p]).liftBaseChange_bijective n

section PadicIntH1

open TauCeti TauCeti.ContCohomology

/-! `ℤ_p` also acts on itself by translation (Mathlib's `Multiplicative.smul`), so the
`ℤ_p`-coefficient check names the action it refers to. -/

/-- For the trivial action of `ℤ_p`, `H¹(ℤ_p, ℤ_p) = ℤ_p`. -/
noncomputable example [i : DistribMulAction (Multiplicative ℤ_[p]) ℤ_[p]]
    [@ContinuousSMul (Multiplicative ℤ_[p]) ℤ_[p] i.toSMul _ _]
    [@SMulCommClass (Multiplicative ℤ_[p]) ℤ_[p] ℤ_[p] i.toSMul _]
    (htriv : ∀ (g : Multiplicative ℤ_[p]) (a : ℤ_[p]), SMul.smul (self := i.toSMul) g a = a) :
    H1 (Multiplicative ℤ_[p]) ℤ_[p] ≃ₗ[ℤ_[p]] ℤ_[p] :=
  padicIntH1LinearEquiv htriv

/-- For the trivial action of `ℤ_p`, `H¹(ℤ_p, ℚ_p) = Hom_cts(ℤ_p, ℚ_p) = ℚ_p`. -/
noncomputable example [i : DistribMulAction (Multiplicative ℤ_[p]) ℚ_[p]]
    [@ContinuousSMul (Multiplicative ℤ_[p]) ℚ_[p] i.toSMul _ _]
    [@SMulCommClass (Multiplicative ℤ_[p]) ℤ_[p] ℚ_[p] i.toSMul _]
    (htriv : ∀ (g : Multiplicative ℤ_[p]) (a : ℚ_[p]), g • a = a) :
    H1 (Multiplicative ℤ_[p]) ℚ_[p] ≃ₗ[ℤ_[p]] ℚ_[p] :=
  padicIntH1LinearEquiv htriv

/-- The class in `H¹(ℤ_p, ℚ_p)` with value `1/p` at `1` is the character `x ↦ x / p`. -/
example [i : DistribMulAction (Multiplicative ℤ_[p]) ℚ_[p]]
    [@ContinuousSMul (Multiplicative ℤ_[p]) ℚ_[p] i.toSMul _ _]
    (htriv : ∀ (g : Multiplicative ℤ_[p]) (a : ℚ_[p]), g • a = a) (x : ℤ_[p]) :
    Multiplicative.toAdd ((H1EquivOfSmulEqSelf htriv
      ((padicIntH1Equiv htriv).symm (p : ℚ_[p])⁻¹)).toMul (Multiplicative.ofAdd x)) =
      (x : ℚ_[p]) / p := by
  simp [Algebra.smul_def, div_eq_mul_inv]

end PadicIntH1
