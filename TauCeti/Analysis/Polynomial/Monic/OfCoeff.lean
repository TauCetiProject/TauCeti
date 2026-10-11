/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Polynomial.Monic.OfCoeff
public import Mathlib.Analysis.Polynomial.CauchyBound
import Mathlib.Analysis.Normed.Group.Constructions

/-!
# A root bound in monic coefficient coordinates

A root of `TauCeti.Polynomial.monicOfCoeff c` has norm strictly less than
`‖c‖ + 1`. Thus locally bounded coefficient tuples give locally bounded roots,
without choosing or continuously labelling them. This is the bound used to remove
singularities of analytic root branches.

The estimate specializes Mathlib's `Polynomial.IsRoot.norm_lt_cauchyBound`
(Daniel Weber's formalization of Cauchy's root bound) to the finite coefficient tuple.
-/

public section

open Polynomial

namespace TauCeti.Polynomial

/-- Every root of the monic polynomial with lower coefficients `c` has norm
strictly less than `‖c‖ + 1`. -/
theorem norm_lt_of_isRoot_monicOfCoeff {K : Type*} [NormedField K] {d : ℕ}
    (c : Fin d → K) {z : K} (hz : (monicOfCoeff c).IsRoot z) : ‖z‖ < ‖c‖ + 1 := by
  have hsup : (Finset.range d).sup (fun i => ‖(monicOfCoeff c).coeff i‖₊) ≤ ‖c‖₊ := by
    refine Finset.sup_le fun i hi => ?_
    rw [Finset.mem_range] at hi
    rw [coeff_monicOfCoeff c ⟨i, hi⟩]
    exact nnnorm_le_pi_nnnorm c ⟨i, hi⟩
  have hb : (monicOfCoeff c).cauchyBound ≤ ‖c‖₊ + 1 := by
    rw [cauchyBound, (monic_monicOfCoeff c).leadingCoeff, nnnorm_one, div_one,
      natDegree_monicOfCoeff]
    exact add_le_add hsup le_rfl
  exact_mod_cast (hz.norm_lt_cauchyBound (monic_monicOfCoeff c).ne_zero).trans_le hb

/-- Evaluating a monic coefficient family at a continuous function is continuous. -/
@[fun_prop]
theorem continuousOn_eval_monicOfCoeff {R B : Type*} [CommSemiring R]
    [TopologicalSpace R] [IsTopologicalSemiring R] [TopologicalSpace B] {d : ℕ}
    (c : B → Fin d → R) {r : B → R} {t : Set B}
    (hc : ContinuousOn c t) (hr : ContinuousOn r t) :
    ContinuousOn (fun x => (monicOfCoeff (c x)).eval (r x)) t := by
  simp_rw [eval_monicOfCoeff]
  exact (hr.pow d).add (continuousOn_finsetSum _ fun i _ =>
    (continuousOn_pi.1 hc i).mul (hr.pow i.val))

end TauCeti.Polynomial
