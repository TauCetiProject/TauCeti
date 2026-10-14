/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.EvolutionSpace.Basic

/-!
# Integration by parts for parabolic energy functions

For two functions in `EvolutionSpace ι a b`, the pivot inner product has weak derivative
`u'(v) + v'(u)`. Consequently, integration by parts moves a weak time derivative between
the two functions, with boundary terms given by their canonical continuous time traces.
The formula holds between any two times in `[a,b]`, in either order, including the endpoints.

This allows time-dependent energy functions to be used as test functions in parabolic
equations and their adjoints. Both time derivatives take values in `V*`, while the endpoint
pairings take place in the pivot space `H`; no `H`-valued time derivative is assumed.
The pivot map need not be injective or have dense range.

The proof uses the mixed weak product rule for symmetric bilinear forms and the fundamental
theorem of calculus for weak derivatives on an interval.

## References

* L. C. Evans, *Partial Differential Equations*, second edition, §5.9.2, Theorem 3.
* E. Zeidler, *Nonlinear Functional Analysis and its Applications II/A*, Chapter 23.
-/

public section

noncomputable section

namespace TauCeti.EvolutionSpace

open MeasureTheory Set
open scoped InnerProductSpace

variable {V H : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  {ι : V →L[ℝ] H} {a b : ℝ}

/-- The pairing of an energy function's weak time derivative with another energy function
is integrable on the open time interval. -/
theorem integrableOn_timeDeriv_value (u v : EvolutionSpace ι a b) :
    IntegrableOn (fun r ↦ timeDeriv u r (value v r)) (Ioo a b) :=
  (Lp.memLp (timeDeriv u)).integrable_apply (Lp.memLp (value v))

/-- The derivative-value pairing is interval integrable between any two times in `[a,b]`,
including endpoints and either time order. -/
theorem intervalIntegrable_timeDeriv_value (u v : EvolutionSpace ι a b) (s t : Icc a b) :
    IntervalIntegrable (fun r ↦ timeDeriv u r (value v r)) volume (s : ℝ) (t : ℝ) := by
  have hab : a ≤ b := s.property.1.trans s.property.2
  exact ((intervalIntegrable_iff_integrableOn_Ioo_of_le hab).2
    (integrableOn_timeDeriv_value u v)).mono_set
      (by simpa only [uIcc_of_le hab] using
        ordConnected_Icc.uIcc_subset s.property t.property)

variable [CompleteSpace V] [CompleteSpace H]

/-- **Integration by parts in the parabolic energy space.** The weak time derivative may
be moved between two energy functions, with the endpoint terms evaluated on their canonical
continuous pivot representatives. The times may coincide or occur in either order. -/
theorem integral_timeDeriv_value_eq_sub (hab : a < b) (u v : EvolutionSpace ι a b)
    (s t : Icc a b) :
    ∫ r in (s : ℝ)..(t : ℝ), timeDeriv u r (value v r) =
      ⟪toContinuousMap hab u t, toContinuousMap hab v t⟫_ℝ -
        ⟪toContinuousMap hab u s, toContinuousMap hab v s⟫_ℝ -
          ∫ r in (s : ℝ)..(t : ℝ), timeDeriv v r (value u r) := by
  have hp := (hasWeakLineDerivOn u).inner_sub_inner_eq_integral_of_gelfandDual
    (hasWeakLineDerivOn v) (Lp.memLp (value u)) (Lp.memLp (timeDeriv u))
    (Lp.memLp (value v)) (Lp.memLp (timeDeriv v))
    ((toContinuousMap hab u).continuous.comp continuous_projIcc).continuousOn
    ((toContinuousMap hab v).continuous.comp continuous_projIcc).continuousOn
    (value_ae_eq_toContinuousMap hab u) (value_ae_eq_toContinuousMap hab v)
    s.property t.property
  simp only [Function.comp_apply, projIcc_of_mem hab.le s.property,
    projIcc_of_mem hab.le t.property,
    intervalIntegral.integral_add (intervalIntegrable_timeDeriv_value u v s t)
      (intervalIntegrable_timeDeriv_value v u s t)] at hp
  linarith

end TauCeti.EvolutionSpace
