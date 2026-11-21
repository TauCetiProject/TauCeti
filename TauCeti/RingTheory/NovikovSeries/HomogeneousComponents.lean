/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.NovikovSeries.Grading
public import TauCeti.RingTheory.NovikovSeries.Topology
public import Mathlib.Topology.Algebra.InfiniteSum.Basic

/-!
# Homogeneous components of Novikov series

Let `f : H → ι` be a degree function on the exponents of Novikov series. The homogeneous pieces
`TauCeti.NovikovSeries.gradeBy R N f i` are independent, but the Novikov ring is in general not
their direct sum: a series whose support meets infinitely many degrees is not a finite sum of
homogeneous series. This file shows that the completion is nevertheless recovered from the
homogeneous pieces through the period topology of `TauCeti.RingTheory.NovikovSeries.Topology`.

* Taking the **homogeneous component** of degree `i` (`TauCeti.NovikovSeries.gradeProj`) is
  continuous (`TauCeti.NovikovSeries.continuous_gradeProj`), and every homogeneous piece is closed
  (`TauCeti.NovikovSeries.isClosed_gradeBy`).
* Every series is the sum, convergent in the period topology, of its homogeneous components
  (`TauCeti.NovikovSeries.hasSum_gradeProj`), and this is its only decomposition into a convergent
  sum of homogeneous series (`TauCeti.NovikovSeries.hasSum_iff_eq_gradeProj`). Hence the sum of
  the homogeneous pieces is dense (`TauCeti.NovikovSeries.dense_iSup_gradeBy`).
* A series is a finite sum of homogeneous series exactly when its support meets finitely many
  degrees (`TauCeti.NovikovSeries.mem_iSup_gradeBy_iff_finite`). So the sum of the homogeneous
  pieces is closed exactly when it is everything, that is, exactly when the Novikov ring is the
  internal direct sum of its homogeneous pieces
  (`TauCeti.NovikovSeries.isClosed_iSup_gradeBy_iff`,
  `TauCeti.NovikovSeries.isInternal_gradeBy_iff`). For an additive degree with values in a
  torsion-free group and nontrivial coefficients, this happens exactly when the period or the
  degree vanishes (`TauCeti.NovikovSeries.isInternal_gradeBy_iff_eq_zero_or_eq_zero`).

For the Floer Novikov ring, graded by twice the first Chern number, the last statement says that,
for nontrivial coefficients, the integer direct sum of the homogeneous pieces is the whole ring
only when the first Chern number or the symplectic area vanishes on spherical classes; in general
the ring is the completion of that direct sum, with each series the convergent sum of its
homogeneous components.

## References

* H. Hofer and D. A. Salamon, *Floer homology and Novikov rings*, in *The Floer memorial
  volume*, Progr. Math. 133 (1995), 483–524.
* D. McDuff and D. Salamon, *J-holomorphic curves and symplectic topology*, Section 11.1, on the
  Novikov ring and its grading.
-/

public section

noncomputable section

open Filter Function Set Topology

namespace TauCeti

namespace NovikovSeries

variable {R H ι : Type*} [Ring R] [AddZeroClass H] {N : H →+ ℝ}

/-- Every homogeneous piece is closed in the period topology: it is cut out by the vanishing of
the coefficients at the exponents of other degrees, each of which is locally constant. -/
theorem isClosed_gradeBy (f : H → ι) (i : ι) :
    IsClosed (gradeBy R N f i : Set (NovikovSeries R H N)) := by
  have heq : (gradeBy R N f i : Set (NovikovSeries R H N)) =
      ⋂ h ∈ (f ⁻¹' {i})ᶜ, {a | a.coeff h = 0} := by
    ext a
    simp only [SetLike.mem_coe, mem_gradeBy_iff, mem_iInter, mem_ofPred_eq]
    exact ⟨fun ha h hh => by_contra fun hne => hh (ha (mem_support.2 hne)),
      fun ha h hh => by_contra fun hne => mem_support.1 hh (ha h hne)⟩
  rw [heq]
  exact isClosed_biInter fun h _ => (isLocallyConstant_coeff h).isClosed_fiber 0

section Proj

variable [DecidableEq ι]

/-- Taking a homogeneous component preserves every subgroup `U_C` of the period filtration. -/
theorem gradeProj_mem_periodFiltration (f : H → ι) (i : ι) {C : ℝ} {a : NovikovSeries R H N}
    (ha : a ∈ periodFiltration R N C) : gradeProj R N f i a ∈ periodFiltration R N C :=
  mem_periodFiltration.2 fun h hh => by
    rw [coeff_gradeProj, mem_periodFiltration.1 ha h hh, ite_self]

/-- Taking a homogeneous component is continuous in the period topology. -/
theorem continuous_gradeProj (f : H → ι) (i : ι) :
    Continuous (gradeProj R N f i) :=
  continuous_of_continuousAt_zero (gradeProj R N f i) <| by
    rw [ContinuousAt, map_zero]
    exact (hasBasis_nhds_zero.tendsto_iff hasBasis_nhds_zero).2 fun C _ =>
      ⟨C, trivial, fun _ ha => gradeProj_mem_periodFiltration f i ha⟩

/-- **Every Novikov series is the sum of its homogeneous components**, convergent in the period
topology: below any period cutoff only finitely many degrees occur in the support. -/
theorem hasSum_gradeProj (f : H → ι) (a : NovikovSeries R H N) :
    HasSum (fun i => gradeProj R N f i a) a := by
  rw [HasSum, SummationFilter.unconditional_filter, tendsto_nhds_iff]
  intro C
  filter_upwards [eventually_ge_atTop ((a.finite_lt C).toFinset.image f)] with s hs h hh
  rw [coeff_sum_gradeProj]
  split_ifs with hhs
  · rfl
  · by_contra hne
    exact hhs (hs (Finset.mem_image_of_mem f ((a.finite_lt C).mem_toFinset.2 ⟨Ne.symm hne, hh⟩)))

/-- **Uniqueness of the homogeneous decomposition.** A family of series of the respective degrees
sums to `a` exactly when it is the family of homogeneous components of `a`. -/
theorem hasSum_iff_eq_gradeProj {f : H → ι} {b : ι → NovikovSeries R H N}
    (hb : ∀ i, b i ∈ gradeBy R N f i) {a : NovikovSeries R H N} :
    HasSum b a ↔ ∀ i, b i = gradeProj R N f i a := by
  refine ⟨fun h i => ?_, fun h => funext h ▸ hasSum_gradeProj f a⟩
  -- The `i`-th component of the sum is the sum of the `i`-th components, which is `b i`.
  have hi : HasSum (fun j => gradeProj R N f i (b j)) (b i) := by
    convert hasSum_ite_eq i (b i) using 2 with j
    by_cases hj : j = i
    · rw [ite_eq_left hj, hj, gradeProj_eq_self_of_mem_gradeBy (hb i)]
    · rw [ite_eq_right hj, gradeProj_eq_zero_of_mem_gradeBy hj (hb j)]
  exact hi.unique (h.map (gradeProj R N f i) (continuous_gradeProj f i))

end Proj

/-- The finite sums of homogeneous series are dense in the period topology. -/
theorem dense_iSup_gradeBy (f : H → ι) :
    Dense ((⨆ i, gradeBy R N f i : Submodule R (NovikovSeries R H N)) :
      Set (NovikovSeries R H N)) := fun a => by
  classical
  have ha := hasSum_gradeProj f a
  rw [HasSum, SummationFilter.unconditional_filter] at ha
  exact mem_closure_of_tendsto ha (Eventually.of_forall fun s =>
    Submodule.sum_mem _ fun i _ => Submodule.mem_iSup_of_mem i (gradeProj_mem_gradeBy f i a))

/-- The sum of the homogeneous pieces is closed in the period topology exactly when it is
everything, that is, when every series meets only finitely many degrees. -/
theorem isClosed_iSup_gradeBy_iff {f : H → ι} :
    IsClosed ((⨆ i, gradeBy R N f i : Submodule R (NovikovSeries R H N)) :
      Set (NovikovSeries R H N)) ↔ ∀ a : NovikovSeries R H N, (f '' a.support).Finite := by
  rw [← iSup_gradeBy_eq_top_iff]
  refine ⟨fun h => ?_, fun h => by simp [h]⟩
  rw [← Submodule.coe_eq_univ, ← h.closure_eq, (dense_iSup_gradeBy f).closure_eq]

end NovikovSeries

end TauCeti
