/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Dagger.FaithfullyFlat
public import TauCeti.RingTheory.MvPowerSeries.TateAlgebra.ClosedIdeal

import TauCeti.RingTheory.MvPowerSeries.TateAlgebra.Groebner
import TauCeti.Topology.Algebra.Ring.MaximalIdeals

/-!
# Strictly closed ideals of Monsky–Washnitzer algebras

Every ideal of the Monsky–Washnitzer algebra over a complete nontrivially normed ultrametric
field is closed for the unit Gauss norm. Moreover, every coset has an element of least norm:
the infimum defining the residue norm is attained. Thus presentation quotients of
overconvergent algebras carry genuine residue norms, not merely seminorms.

Closedness follows by contracting the closed extended ideal in the Tate algebra, using
faithful flatness. To obtain a least-norm representative, approximate a Tate-algebra
minimizer by the image of the original ideal. The ultrametric inequality preserves its
norm once the approximation error is smaller than the positive minimum; a zero minimum
is handled by contraction instead.

## References

* E. Grosse-Klönne, *Rigid analytic spaces with overconvergent structure sheaf*,
  J. reine angew. Math. 519 (2000), §1.4(4).
-/

public section

namespace TauCeti.Dagger.washnitzerAlgebra

open _root_.MvPowerSeries

variable {K σ : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
  [Finite σ]

local notation "W" => washnitzerAlgebra σ K
local notation "T" => IsRestricted.subring (R := K) (fun _ : σ ↦ (1 : ℝ))

/-- Every ideal of the Monsky–Washnitzer algebra is closed for the Gauss norm. -/
instance isClosed_ideal (I : Ideal W) : IsClosed (I : Set W) := by
  have hc : IsClosed (I.map (toTate σ K) : Set T) :=
    TauCeti.MvPowerSeries.isClosed_ideal_isRestrictedSubring _
  exact I.comap_map_toTate ▸ hc.preimage (isometry_toTate (σ := σ) (R := K)).continuous

/-- **Strict closedness of overconvergent ideals.** Every coset of an ideal in the
Monsky–Washnitzer algebra has a representative of least Gauss norm. -/
theorem _root_.Ideal.exists_norm_sub_le_washnitzerAlgebra (I : Ideal W) (f : W) :
    ∃ g ∈ I, ∀ h ∈ I, ‖f - g‖ ≤ ‖f - h‖ := by
  let J : Ideal T := I.map (toTate σ K)
  obtain ⟨g, hg, hmin⟩ := J.exists_norm_sub_le_isRestricted_subring (toTate σ K f)
  by_cases hzero : toTate σ K f - g = 0
  · have hfJ : toTate σ K f ∈ I.map (toTate σ K) := (sub_eq_zero.mp hzero).symm ▸ hg
    have hf : f ∈ I := I.comap_map_toTate ▸ hfJ
    exact ⟨f, hf, by simp⟩
  · have hpos : 0 < ‖toTate σ K f - g‖ := norm_pos_iff.mpr hzero
    have hclosure := Ideal.map_subset_closure_image_of_denseRange denseRange_toTate I hg
    obtain ⟨_, ⟨a, ha, rfl⟩, hdist⟩ := Metric.mem_closure_iff.mp hclosure _ hpos
    refine ⟨a, ha, fun h hh ↦ ?_⟩
    have happrox : ‖toTate σ K f - toTate σ K a‖ ≤ ‖toTate σ K f - g‖ := by
      have heq : toTate σ K f - toTate σ K a = (toTate σ K f - g) +
          (g - toTate σ K a) := by abel
      rw [heq]
      exact (IsUltrametricDist.norm_add_le_max _ _).trans
        (max_le le_rfl (by simpa [dist_eq_norm] using hdist.le))
    simpa only [← map_sub, norm_toTate] using
      happrox.trans (hmin (toTate σ K h) (Ideal.mem_map_of_mem _ hh))

/-- A least-norm adjustment attains the residue Gauss norm of the original series. -/
theorem _root_.Ideal.exists_norm_sub_eq_norm_mk_washnitzerAlgebra (I : Ideal W) (f : W) :
    ∃ g ∈ I, ‖f - g‖ = ‖Ideal.Quotient.mk I f‖ := by
  obtain ⟨g, hg, hmin⟩ := I.exists_norm_sub_le_washnitzerAlgebra f
  exact ⟨g, hg, (Ideal.Quotient.norm_sub_eq_norm_mk_iff hg).mpr hmin⟩

/-- Every residue class of an overconvergent algebra has a representative attaining its
residue Gauss norm. -/
theorem _root_.Ideal.exists_mk_eq_and_norm_eq_washnitzerAlgebra (I : Ideal W) (q : W ⧸ I) :
    ∃ f : W, Ideal.Quotient.mk I f = q ∧ ‖f‖ = ‖q‖ :=
  Ideal.Quotient.exists_mk_eq_and_norm_eq_iff.mpr I.exists_norm_sub_le_washnitzerAlgebra q

-- Closedness supplies Mathlib's normed quotient, without a reducedness hypothesis.
noncomputable example (I : Ideal W) : NormedCommRing (W ⧸ I) := inferInstance

example (I : Ideal W) : IsUltrametricDist (W ⧸ I) := inferInstance

-- A nonreduced quotient retains the Gauss norm of its nilpotent coordinate.
example (i : σ) :
    ‖Ideal.Quotient.mk (Ideal.span {X σ K i ^ 2}) (X σ K i)‖ = 1 := by
  let x := X σ K i
  let I : Ideal W := Ideal.span {x ^ 2}
  obtain ⟨g, hg, hnorm⟩ := I.exists_norm_sub_eq_norm_mk_washnitzerAlgebra x
  have hdiv : (_root_.MvPowerSeries.X i : MvPowerSeries σ K) ^ 2 ∣
      (g : MvPowerSeries σ K) := by
    have h := map_dvd (washnitzerAlgebra σ K).val (Ideal.mem_span_singleton.mp hg)
    simpa [x, coe_X] using h
  have hgcoeff : coeff (Finsupp.single i 1) (g : MvPowerSeries σ K) = 0 :=
    X_pow_dvd_iff.mp hdiv _ (by simp)
  have hcoeff : coeff (Finsupp.single i 1) ((x - g : W) : MvPowerSeries σ K) = 1 := by
    simp [x, hgcoeff, coe_X]
  have hle := norm_coeff_le (x - g) (Finsupp.single i 1)
  rw [hcoeff, norm_one, hnorm] at hle
  exact le_antisymm ((Ideal.Quotient.norm_mk_le I x).trans_eq (norm_X i)) hle

-- Squaring that same class gives zero, in every characteristic.
example (i : σ) :
    Ideal.Quotient.mk (Ideal.span {X σ K i ^ 2}) (X σ K i) ^ 2 = 0 := by
  rw [← map_pow, Ideal.Quotient.eq_zero_iff_mem]
  exact Ideal.subset_span (by simp)

end TauCeti.Dagger.washnitzerAlgebra
