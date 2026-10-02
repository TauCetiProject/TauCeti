/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Continuous.Pontryagin.Basic
import Mathlib.Analysis.CStarAlgebra.GelfandDuality

/-!
# Continuity of the integrated-character parameter

Let `π` be a strongly continuous unitary representation of an abelian topological group equipped
with a regular invariant measure, and let `A` be a complete commutative star subalgebra containing
all integrated operators.
A character of `A` that is nonzero on some integrated operator determines a continuous group
character by `ContRepresentation.existsUnique_pontryaginDual_of_integratedOperatorL1`.

This file packages the characters on which that construction is defined and proves that the
resulting map to the Pontryagin dual is continuous.  Near a character `ω`, choose an integrated
operator `π(f)` on which `ω` is nonzero.  The detected group character then has the local formula

`χ(g) = ω(π(g)π(f)) / ω(π(f))`.

The numerator is jointly continuous in `ω` and `g`: norm continuity of translated integrated
operators combines with the isometric Gelfand transform and continuous evaluation.  The
denominator remains nonzero in a neighbourhood of `ω`, so the displayed quotient proves the
required local continuity.  This continuity is the input needed to push a character-space
spectral measure to the Pontryagin dual.

## Main declarations

* `ContRepresentation.integratedCharacterSet`: algebra characters that do not annihilate every
  integrated operator.
* `ContRepresentation.integratedCharacterToPontryaginDual`: the group character detected by an
  integrated-algebra character.
* `ContRepresentation.continuous_integratedCharacterToPontryaginDual`: continuity of this
  assignment.

## References

* G. B. Folland, *A Course in Abstract Harmonic Analysis*, second edition, §§3.2 and 4.4.
-/

public section

noncomputable section

open Filter MeasureTheory WeakDual
open scoped IsMulCommutative Topology

variable {G H : Type*} [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G]
  [MeasurableSpace G] [BorelSpace G]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {μ : Measure G} [μ.IsAddLeftInvariant] [μ.InnerRegularCompactLTTop]
  [IsLocallyFiniteMeasure μ]

namespace ContRepresentation

variable (π : ContRepresentation ℂ (Multiplicative G) H)
  (hcont : ∀ v, Continuous fun g : G => π (.ofAdd g) v)
  (hbdd : ∃ C, ∀ g, ‖π g‖ ≤ C)
  (A : StarSubalgebra ℂ (H →L[ℂ] H)) [CompleteSpace A] [IsMulCommutative A]
  (hA : ∀ f : G →₁[μ] ℂ, π.integratedOperatorL1 hcont hbdd μ f ∈ A)

/-- The characters of an algebra containing the integrated form which do not annihilate every
integrated operator.  These are exactly the algebra characters from which the representation
detects a point of the Pontryagin dual. -/
def integratedCharacterSet : Set (characterSpace ℂ A) :=
  {ω | ∃ f : G →₁[μ] ℂ, ω ⟨π.integratedOperatorL1 hcont hbdd μ f, hA f⟩ ≠ 0}

omit [μ.IsAddLeftInvariant] [IsLocallyFiniteMeasure μ] [CompleteSpace A] in
/-- Membership in the integrated-character set means nonvanishing on some integrated operator. -/
@[simp]
theorem mem_integratedCharacterSet_iff (ω : characterSpace ℂ A) :
    ω ∈ π.integratedCharacterSet hcont hbdd A hA ↔
      ∃ f : G →₁[μ] ℂ, ω ⟨π.integratedOperatorL1 hcont hbdd μ f, hA f⟩ ≠ 0 :=
  Iff.rfl

omit [μ.IsAddLeftInvariant] [IsLocallyFiniteMeasure μ] in
/-- The integrated-character set is open in the character space. -/
theorem isOpen_integratedCharacterSet :
    IsOpen (π.integratedCharacterSet hcont hbdd A hA) := by
  let _ : CStarAlgebra A := {}
  let _ : CommCStarAlgebra A := {}
  rw [isOpen_iff_mem_nhds]
  intro ω hω
  obtain ⟨f, hf⟩ := (π.mem_integratedCharacterSet_iff hcont hbdd A hA ω).mp hω
  apply mem_of_superset
    ((isOpen_ne_fun (gelfandTransform ℂ A _).continuous continuous_const).mem_nhds hf)
  intro ψ hψ
  exact (π.mem_integratedCharacterSet_iff hcont hbdd A hA ψ).mpr ⟨f, hψ⟩

variable (hπ : TauCeti.ContRepresentation.IsUnitary π)

/-- The continuous group character detected by an algebra character that does not annihilate the
integrated form. -/
noncomputable def integratedCharacterToPontryaginDual
    (ω : π.integratedCharacterSet hcont hbdd A hA) : PontryaginDual (Multiplicative G) :=
  Classical.choose
    (π.existsUnique_pontryaginDual_of_integratedOperatorL1 hbdd hπ A hA ω.1
      ((π.mem_integratedCharacterSet_iff hcont hbdd A hA ω).mp ω.2))

/-- The defining multiplier identity for the group character detected by an integrated
character. -/
theorem integratedCharacterToPontryaginDual_spec
    (ω : π.integratedCharacterSet hcont hbdd A hA) (g : G) (f : G →₁[μ] ℂ) :
    ω.1
        ⟨π.integratedOperatorL1 hcont hbdd μ
          (Lp.compMeasurePreserving (fun t => -g + t)
            (measurePreserving_add_left μ (-g)) f), hA _⟩ =
      (π.integratedCharacterToPontryaginDual hcont hbdd A hA hπ ω (.ofAdd g) : ℂ) *
        ω.1 ⟨π.integratedOperatorL1 hcont hbdd μ f, hA f⟩ :=
  (Classical.choose_spec
    (π.existsUnique_pontryaginDual_of_integratedOperatorL1 hbdd hπ A hA ω.1
      ((π.mem_integratedCharacterSet_iff hcont hbdd A hA ω).mp ω.2))).1 g f

/-- Local quotient formula for the group character detected by an integrated character. -/
theorem coe_integratedCharacterToPontryaginDual_apply_eq_div
    (ω : π.integratedCharacterSet hcont hbdd A hA) (g : G) (f : G →₁[μ] ℂ)
    (hf : ω.1 ⟨π.integratedOperatorL1 hcont hbdd μ f, hA f⟩ ≠ 0) :
    (π.integratedCharacterToPontryaginDual hcont hbdd A hA hπ ω (.ofAdd g) : ℂ) =
      ω.1 ⟨π.integratedOperatorL1 hcont hbdd μ
        (Lp.compMeasurePreserving (fun t => -g + t)
          (measurePreserving_add_left μ (-g)) f), hA _⟩ /
        ω.1 ⟨π.integratedOperatorL1 hcont hbdd μ f, hA f⟩ :=
  (eq_div_iff hf).2
    (π.integratedCharacterToPontryaginDual_spec hcont hbdd A hA hπ ω g f).symm

/-- The group character detected by a nonvanishing integrated character depends continuously on
the algebra character. -/
theorem continuous_integratedCharacterToPontryaginDual :
    Continuous (π.integratedCharacterToPontryaginDual hcont hbdd A hA hπ) := by
  let _ : CStarAlgebra A := {}
  let _ : CommCStarAlgebra A := {}
  let D := π.integratedCharacterSet hcont hbdd A hA
  let θ : D → PontryaginDual (Multiplicative G) :=
    π.integratedCharacterToPontryaginDual hcont hbdd A hA hπ
  apply ContinuousMonoidHom.continuous_of_continuous_uncurry
  apply continuous_induced_rng.mpr
  rw [continuous_iff_continuousAt]
  rintro ⟨ω, g⟩
  obtain ⟨f, hf⟩ := (π.mem_integratedCharacterSet_iff hcont hbdd A hA ω).mp ω.2
  let a : A := ⟨π.integratedOperatorL1 hcont hbdd μ f, hA f⟩
  let v : Multiplicative G → A := fun g =>
    ⟨π.integratedOperatorL1 hcont hbdd μ
      (Lp.compMeasurePreserving (fun t => -g.toAdd + t)
        (measurePreserving_add_left μ (-g.toAdd)) f), hA _⟩
  have hv : Continuous v := by
    apply continuous_induced_rng.mpr
    refine ((π.continuous_comp_integratedOperatorL1 (hcont := hcont) (hbdd := hbdd) f).comp
      continuous_toAdd).congr fun g => ?_
    exact π.comp_integratedOperatorL1 (hcont := hcont) (hbdd := hbdd) g.toAdd f
  have hgv : Continuous fun g => gelfandTransform ℂ A (v g) :=
    (gelfandTransform_isometry A).continuous.comp hv
  have hnum : Continuous fun p : D × Multiplicative G =>
      (p.1.1 (v p.2) : ℂ) := by
    exact continuous_eval.comp
      ((hgv.comp continuous_snd).prodMk (continuous_subtype_val.comp continuous_fst))
  have hden : Continuous fun p : D × Multiplicative G =>
      (p.1.1 a : ℂ) :=
    (gelfandTransform ℂ A a).continuous.comp (continuous_subtype_val.comp continuous_fst)
  have hquot : ContinuousAt (fun p : D × Multiplicative G =>
      p.1.1 (v p.2) / p.1.1 a) (ω, g) :=
    hnum.continuousAt.div hden.continuousAt (by simpa only [a] using hf)
  have hden_ne : ∀ᶠ p in 𝓝 (ω, g), p.1.1 a ≠ 0 :=
    hden.continuousAt.eventually_ne (by simpa only [a] using hf)
  apply hquot.congr_of_eventuallyEq
  filter_upwards [hden_ne] with p hp
  exact π.coe_integratedCharacterToPontryaginDual_apply_eq_div
    hcont hbdd A hA hπ p.1 p.2.toAdd f hp

end ContRepresentation
