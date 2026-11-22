/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Polynomial.CauchyBound
import Mathlib.Analysis.Normed.Group.Continuity

/-!
# Local Cauchy root bounds along filters

Along any filter where the coefficients of a polynomial family `p` up to `q.natDegree` converge to
those of a nonzero polynomial `q` over a normed division ring and the degrees eventually do not
exceed `q.natDegree`, any eventual root selection is eventually bounded in norm
(`TauCeti.eventually_norm_le_of_isRoot`).

Because `q.coeff q.natDegree ≠ 0`, the `q.natDegree`-th coefficient of `p y` eventually stays
bounded away from zero while the lower coefficients stay bounded above, so Mathlib's Cauchy root
bound `Polynomial.IsRoot.norm_lt_cauchyBound` (Daniel Weber) is eventually uniformly bounded.
-/

public section

open Filter Set Topology

namespace TauCeti

/-- Along any filter where the coefficients up to `q.natDegree` converge to those of a nonzero
polynomial `q` over a normed division ring and the degrees eventually do not exceed `q.natDegree`,
any root selection is eventually bounded in norm by Cauchy's bound. -/
theorem eventually_norm_le_of_isRoot {α K : Type*} [NormedDivisionRing K]
    {l : Filter α} {p : α → Polynomial K} {q : Polynomial K} {f : α → K} (hq : q ≠ 0)
    (hcoeff : ∀ i ≤ q.natDegree, Tendsto (fun y ↦ (p y).coeff i) l (𝓝 (q.coeff i)))
    (hdeg : ∀ᶠ y in l, (p y).natDegree ≤ q.natDegree)
    (hroot : ∀ᶠ y in l, (p y).IsRoot (f y)) :
    ∃ M : ℝ, ∀ᶠ y in l, ‖f y‖ ≤ M := by
  set d := q.natDegree
  have hqd : q.coeff d ≠ 0 := by
    simpa only [d, Polynomial.coeff_natDegree] using Polynomial.leadingCoeff_ne_zero.2 hq
  have hc₀ : 0 < ‖q.coeff d‖₊ := nnNorm_pos.2 hqd
  -- Eventually the `d`-th coefficient stays above half its limit norm and lower ones stay bounded.
  have hlead : ∀ᶠ y in l, ‖q.coeff d‖₊ / 2 < ‖(p y).coeff d‖₊ :=
    ((continuous_nnNorm.tendsto _).comp (hcoeff d le_rfl)).eventually
      (Ioi_mem_nhds (NNReal.half_lt_self hc₀.ne'))
  have hlow : ∀ᶠ y in l, ∀ i ∈ Finset.range d, ‖(p y).coeff i‖₊ ≤ ‖q.coeff i‖₊ + 1 :=
    (eventually_all_finset (Finset.range d)).2 fun i hi ↦
      ((continuous_nnNorm.tendsto _).comp
        (hcoeff i (Nat.le_of_lt (Finset.mem_range.1 hi)))).eventually
        (Iic_mem_nhds (lt_add_of_pos_right _ zero_lt_one))
  let M : NNReal := (∑ i ∈ Finset.range d, (‖q.coeff i‖₊ + 1)) / (‖q.coeff d‖₊ / 2) + 1
  refine ⟨M, ?_⟩
  filter_upwards [hlead, hlow, hdeg, hroot] with y hyl hyi hyd hyr
  have hypd_pos : 0 < ‖(p y).coeff d‖₊ := (half_pos hc₀).trans hyl
  have hypd_ne : (p y).coeff d ≠ 0 := nnNorm_ne_zero_iff.1 hypd_pos.ne'
  have hydeg : (p y).natDegree = d := le_antisymm hyd (Polynomial.le_natDegree_of_ne_zero hypd_ne)
  have hyp_ne : p y ≠ 0 := fun h0 ↦ hypd_ne (by simp [h0])
  have hsup : Finset.sup (Finset.range d) (‖(p y).coeff ·‖₊) ≤
      ∑ i ∈ Finset.range d, (‖q.coeff i‖₊ + 1) :=
    Finset.sup_le fun i hi ↦
      (hyi i hi).trans
        (Finset.single_le_sum (f := fun j ↦ ‖q.coeff j‖₊ + 1) (fun _ _ ↦ zero_le) hi)
  have hcauchy : (p y).cauchyBound ≤ M := by
    rw [Polynomial.cauchyBound, ← Polynomial.coeff_natDegree, hydeg]
    exact add_le_add_left (div_le_div₀ zero_le hsup (half_pos hc₀) hyl.le) 1
  exact_mod_cast (hyr.norm_lt_cauchyBound hyp_ne).le.trans hcauchy

end TauCeti
