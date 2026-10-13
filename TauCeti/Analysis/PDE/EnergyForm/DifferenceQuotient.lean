/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.EnergyForm.Sobolev
public import TauCeti.Analysis.Sobolev.W1p.DifferenceQuotient

/-!
# Difference quotients in either argument of the Sobolev energy form

For essentially bounded coefficients, the energy form is bilinear on the whole-space Sobolev
space. A difference quotient in either argument is therefore the inverse step times the
energy difference between a translate and the original argument. These identities isolate the
linearity step in discrete integration by parts.
-/

public section

noncomputable section

open MeasureTheory Set TopologicalSpace

namespace TauCeti.PDE

variable {ι : Type*} [Fintype ι] {mu : Measure (EuclideanSpace ℝ ι)} [mu.IsAddHaarMeasure]
  {a : EuclideanSpace ℝ ι → Matrix ι ι ℝ}
  {b : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι} {c : EuclideanSpace ℝ ι → ℝ}

/-- Expanding a difference quotient in the first argument of the energy form. -/
theorem energyFormH1_differenceQuotient_left
    (hcoeff : MemLp (fun x => energyIntegrand (a x) (b x) (c x)) ⊤
      (mu.restrict ((⊤ : Opens (EuclideanSpace ℝ ι)) : Set (EuclideanSpace ℝ ι))))
    (w : EuclideanSpace ℝ ι) (t : ℝ) (u v : W1p mu ⊤ 2) :
    energyFormH1 a b c
        (W1p.differenceQuotient le_rfl w t (Set.mapsTo_univ (· + t • w) _) u) v
      = t⁻¹ * (energyFormH1 a b c (W1p.translate (Set.mapsTo_univ (· + t • w) _) u) v
        - energyFormH1 a b c u v) := by
  rw [W1p.differenceQuotient_def, W1p.restrictL_self,
    ← energyFormH1L_apply (b := b) (c := c) hcoeff]
  simp only [map_smul, map_sub, smul_apply, sub_apply, energyFormH1L_apply, smul_eq_mul]

/-- Expanding a difference quotient in the second argument of the energy form. -/
theorem energyFormH1_differenceQuotient_right
    (hcoeff : MemLp (fun x => energyIntegrand (a x) (b x) (c x)) ⊤
      (mu.restrict ((⊤ : Opens (EuclideanSpace ℝ ι)) : Set (EuclideanSpace ℝ ι))))
    (w : EuclideanSpace ℝ ι) (t : ℝ) (u v : W1p mu ⊤ 2) :
    energyFormH1 a b c u
        (W1p.differenceQuotient le_rfl w t (Set.mapsTo_univ (· + t • w) _) v)
      = t⁻¹ * (energyFormH1 a b c u (W1p.translate (Set.mapsTo_univ (· + t • w) _) v)
        - energyFormH1 a b c u v) := by
  rw [W1p.differenceQuotient_def, W1p.restrictL_self,
    ← energyFormH1L_apply (b := b) (c := c) hcoeff]
  simp only [map_smul, map_sub, energyFormH1L_apply, smul_eq_mul]

end TauCeti.PDE
