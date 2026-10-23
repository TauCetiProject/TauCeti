/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.FilterBasis
public import Mathlib.Topology.Algebra.IsUniformGroup.Basic
public import Mathlib.Topology.Algebra.Nonarchimedean.Basic
public import Mathlib.Topology.Algebra.OpenSubgroup
public import Mathlib.Topology.LocallyConstant.Basic
public import Mathlib.Topology.UniformSpace.AbstractCompletion
public import TauCeti.RingTheory.NovikovSeries.Basic

/-!
# The period-filtration topology on Novikov series

Let `H` be an additive group, `N : H →+ ℝ` a period homomorphism and `R` an additive commutative
group of coefficients. For a real cutoff `C`, the Novikov series whose coefficients vanish at every
exponent of period `< C` form an additive subgroup `U_C`
(`TauCeti.NovikovSeries.periodFiltration`). These subgroups decrease as `C` grows and meet only in
`0`; they form a basis of neighbourhoods of `0` for a separated group topology, the *period
topology*. A sequence of Novikov series converges in it when, below every period cutoff, its
coefficients are eventually constant.

The Novikov series are complete for this topology, and the finitely supported ones are dense: the
truncation `TauCeti.NovikovSeries.trunc C a` of a series `a`, which keeps the coefficients of
period `< C`, differs from `a` by an element of `U_C`. Consequently the Novikov series are the
completion of the group ring `H →₀ R` for the uniform structure of its period filtration
(`TauCeti.NovikovSeries.completionPkg`), and every uniformly continuous map from the group ring
to a complete separated uniform space extends uniquely to the Novikov series. The packaging as an
`AbstractCompletion` follows Mathlib's `LaurentSeries.LaurentSeriesPkg` in
`Mathlib/RingTheory/LaurentSeries.lean`; no code is copied from there.

## Main definitions

* `TauCeti.NovikovSeries.periodFiltration C`: the additive subgroup `U_C` of Novikov series with
  no nonzero coefficient of period `< C`.
* The instances `TopologicalSpace`, `IsTopologicalAddGroup`, `UniformSpace` and
  `IsUniformAddGroup` on `TauCeti.NovikovSeries R H N`: the period topology.
* `TauCeti.NovikovSeries.groupRingUniformSpace`: the uniform structure of the period filtration
  on the group ring `H →₀ R`.
* `TauCeti.NovikovSeries.completionPkg`: the Novikov series as an abstract completion of the
  group ring.

## Main results

* `TauCeti.NovikovSeries.exists_mem_periodFiltration`: every series lies in some `U_C`.
* `TauCeti.NovikovSeries.exists_pos_mem_periodFiltration_iff`: a series vanishes at every exponent
  of period `≤ 0` exactly when it lies in `U_C` for some `C > 0`.
* `TauCeti.NovikovSeries.hasBasis_nhds_zero` and `TauCeti.NovikovSeries.hasBasis_uniformity`:
  the subgroups `U_C` form a basis of the period topology and its uniformity.
* `TauCeti.NovikovSeries.tendsto_nhds_iff`: convergence in the period topology means eventual
  agreement of coefficients below every cutoff.
* The instances `T2Space` and `CompleteSpace`: the period topology is separated and complete.
* The instances `NonarchimedeanAddGroup` and `ContinuousConstSMul`: the period topology has a
  basis of open subgroups, and coefficientwise scalar multiplication is continuous.
* `TauCeti.NovikovSeries.tendsto_ofFinsupp_trunc` and
  `TauCeti.NovikovSeries.denseRange_ofFinsupp`: the truncations of a series converge to it, so the
  finitely supported series are dense.
* `TauCeti.NovikovSeries.isUniformInducing_ofFinsupp`: the period filtration uniformity of the
  group ring is induced from the Novikov series.

## References

* M. Hutchings and Y.-J. Lee, *Circle-valued Morse theory and Reidemeister torsion*,
  Geom. Topol. 3 (1999), Section 2.
* A. Pajitnov, *Circle-valued Morse Theory*, de Gruyter 2006, Chapter 3.
-/

public section

noncomputable section

open Filter Function Set Topology Uniformity

namespace TauCeti

namespace NovikovSeries

variable {R H : Type*} [AddZeroClass H] {N : H →+ ℝ}

section Filtration

variable [AddGroup R] {C : ℝ} {a : NovikovSeries R H N}

variable (R N) in
/-- The additive subgroup `U_C` of Novikov series whose coefficients vanish at every exponent of
period `< C`. These subgroups form a basis of neighbourhoods of `0` in the period topology. -/
def periodFiltration (C : ℝ) : AddSubgroup (NovikovSeries R H N) where
  carrier := {a | ∀ h, N h < C → a.coeff h = 0}
  add_mem' ha hb h hh := by simp [ha h hh, hb h hh]
  zero_mem' _ _ := rfl
  neg_mem' ha h hh := by simp [ha h hh]

@[simp]
theorem mem_periodFiltration : a ∈ periodFiltration R N C ↔ ∀ h, N h < C → a.coeff h = 0 :=
  Iff.rfl

theorem antitone_periodFiltration : Antitone (periodFiltration R N) :=
  fun _ _ hCD _ ha h hh => ha h (hh.trans_le hCD)

/-- A Novikov series vanishes at every exponent of period `≤ 0` exactly when it lies in `U_C` for
some positive cutoff `C`: a nonzero such series lies in `U_C` for its least support period `C`. -/
theorem exists_pos_mem_periodFiltration_iff :
    (∃ C, 0 < C ∧ a ∈ periodFiltration R N C) ↔ ∀ h, N h ≤ 0 → a.coeff h = 0 := by
  refine ⟨fun ⟨C, hC, ha⟩ h hh => ha h (hh.trans_lt hC), fun ha => ?_⟩
  rcases eq_or_ne a 0 with rfl | ha₀
  · exact ⟨1, one_pos, zero_mem _⟩
  obtain ⟨g, hg, hmin⟩ := exists_isLeast_image_support (support_nonempty_iff.2 ha₀)
  exact ⟨N g, lt_of_not_ge fun hg₀ => mem_support.1 hg (ha g hg₀), fun h hh =>
    by_contra fun hh' => (hmin.2 ⟨h, mem_support.2 hh', rfl⟩).not_gt hh⟩

/-- An element of every `U_C` is zero. -/
theorem eq_zero_of_forall_mem_periodFiltration (ha : ∀ C, a ∈ periodFiltration R N C) : a = 0 :=
  ext fun h => ha (N h + 1) h (lt_add_one _)

/-- Every Novikov series lies in some `U_C`, since the periods of its support are bounded
below. -/
theorem exists_mem_periodFiltration (a : NovikovSeries R H N) :
    ∃ C, a ∈ periodFiltration R N C := by
  obtain ⟨C, hC⟩ := a.bddBelow_image_support
  exact ⟨C, fun h hh => by_contra fun ha => (hC ⟨h, mem_support.2 ha, rfl⟩).not_gt hh⟩

/-- The monomial `r e^h` lies in `U_(N h)`. -/
theorem single_mem_periodFiltration (h : H) (r : R) :
    single h r ∈ periodFiltration R N (N h) := fun _ hg =>
  coeff_single_of_ne (ne_of_apply_ne N hg.ne) r

variable (R N) in
theorem iInf_periodFiltration : ⨅ C, periodFiltration R N C = ⊥ :=
  eq_bot_iff.2 fun _ ha =>
    eq_zero_of_forall_mem_periodFiltration fun C => AddSubgroup.mem_iInf.1 ha C

end Filtration

section Topology

variable [AddCommGroup R]

variable (R H N) in
/-- The additive group filter basis made of the subgroups `U_C`, which defines the period
topology. -/
@[instance_reducible]
def periodFilterBasis : AddGroupFilterBasis (NovikovSeries R H N) :=
  addGroupFilterBasisOfComm (range fun C => (periodFiltration R N C : Set _))
    (range_nonempty _)
    (by
      rintro _ _ ⟨C, rfl⟩ ⟨D, rfl⟩
      exact ⟨_, mem_range_self (max C D),
        subset_inter (antitone_periodFiltration (le_max_left C D))
          (antitone_periodFiltration (le_max_right C D))⟩)
    (by
      rintro _ ⟨C, rfl⟩
      exact zero_mem (periodFiltration R N C))
    (by
      rintro _ ⟨C, rfl⟩
      exact ⟨_, mem_range_self C, by
        rintro _ ⟨a, ha, b, hb, rfl⟩
        exact add_mem ha hb⟩)
    (by
      rintro _ ⟨C, rfl⟩
      exact ⟨_, mem_range_self C, fun a ha => neg_mem ha⟩)

/-- The period topology on Novikov series: the subgroups `U_C` form a basis of neighbourhoods
of `0`. -/
instance : TopologicalSpace (NovikovSeries R H N) :=
  (periodFilterBasis R H N).topology

instance : IsTopologicalAddGroup (NovikovSeries R H N) :=
  (periodFilterBasis R H N).isTopologicalAddGroup

/-- The uniform structure of the period topology, for which `a` and `b` are close when `b - a`
lies in some `U_C`. -/
instance : UniformSpace (NovikovSeries R H N) :=
  IsTopologicalAddGroup.rightUniformSpace _

instance : IsUniformAddGroup (NovikovSeries R H N) :=
  isUniformAddGroup_of_addCommGroup

/-- The subgroups `U_C` form a basis of neighbourhoods of `0` in the period topology. -/
theorem hasBasis_nhds_zero :
    (𝓝 (0 : NovikovSeries R H N)).HasBasis (fun _ : ℝ => True)
      fun C => (periodFiltration R N C : Set (NovikovSeries R H N)) := by
  refine ((periodFilterBasis R H N).nhds_zero_hasBasis).to_hasBasis ?_ ?_
  · rintro _ ⟨C, rfl⟩
    exact ⟨C, trivial, subset_rfl⟩
  · exact fun C _ => ⟨_, mem_range_self C, subset_rfl⟩

theorem periodFiltration_mem_nhds_zero (C : ℝ) :
    (periodFiltration R N C : Set (NovikovSeries R H N)) ∈ 𝓝 0 :=
  hasBasis_nhds_zero.mem_of_mem trivial

theorem isOpen_periodFiltration (C : ℝ) :
    IsOpen (periodFiltration R N C : Set (NovikovSeries R H N)) :=
  AddSubgroup.isOpen_of_mem_nhds _ (periodFiltration_mem_nhds_zero C)

theorem isClosed_periodFiltration (C : ℝ) :
    IsClosed (periodFiltration R N C : Set (NovikovSeries R H N)) :=
  AddSubgroup.isClosed_of_isOpen _ (isOpen_periodFiltration C)

/-- The sets `{b | b - a ∈ U_C}` form a basis of neighbourhoods of `a` in the period topology. -/
theorem hasBasis_nhds (a : NovikovSeries R H N) :
    (𝓝 a).HasBasis (fun _ : ℝ => True) fun C => {b | b - a ∈ periodFiltration R N C} := by
  rw [← nhds_translation_sub a]
  exact hasBasis_nhds_zero.comap _

/-- The entourages `{(a, b) | b - a ∈ U_C}` form a basis of the period uniformity. -/
theorem hasBasis_uniformity :
    (𝓤 (NovikovSeries R H N)).HasBasis (fun _ : ℝ => True)
      fun C => {p | p.2 - p.1 ∈ periodFiltration R N C} := by
  rw [uniformity_eq_comap_nhds_zero]
  exact hasBasis_nhds_zero.comap _

/-- A family of Novikov series converges to `a` in the period topology if and only if, below
every period cutoff, its coefficients eventually agree with those of `a`. -/
theorem tendsto_nhds_iff {ι : Type*} {l : Filter ι} {f : ι → NovikovSeries R H N}
    {a : NovikovSeries R H N} :
    Tendsto f l (𝓝 a) ↔ ∀ C : ℝ, ∀ᶠ i in l, ∀ h, N h < C → (f i).coeff h = a.coeff h := by
  simp [(hasBasis_nhds a).tendsto_right_iff, mem_periodFiltration, sub_eq_zero]

instance : T2Space (NovikovSeries R H N) :=
  IsTopologicalAddGroup.t2Space_of_zero_sep fun a ha => by
    obtain ⟨h, hh⟩ := support_nonempty_iff.2 ha
    exact ⟨_, periodFiltration_mem_nhds_zero (N h + 1), fun ha' =>
      mem_support.1 hh (ha' h (lt_add_one _))⟩

/-- The period topology is nonarchimedean: the open subgroups `U_C` form a basis of
neighbourhoods of `0`. -/
instance : NonarchimedeanAddGroup (NovikovSeries R H N) where
  is_nonarchimedean U hU := by
    obtain ⟨C, -, hC⟩ := hasBasis_nhds_zero.mem_iff.1 hU
    exact ⟨⟨periodFiltration R N C, isOpen_periodFiltration C⟩, hC⟩

/-- Coefficientwise scalar multiplication is continuous in the period topology. -/
instance {S : Type*} [DistribSMul S R] : ContinuousConstSMul S (NovikovSeries R H N) where
  continuous_const_smul s := continuous_iff_continuousAt.2 fun a =>
    ((hasBasis_nhds a).tendsto_iff (hasBasis_nhds (s • a))).2 fun C _ =>
      ⟨C, trivial, fun b hb h hh => by
        have hbh := hb h hh
        rw [coeff_sub] at hbh ⊢
        rw [coeff_smul, coeff_smul, ← smul_sub, hbh, smul_zero]⟩

/-- The coefficient of a series at the exponent `h` is locally constant in the period
topology. -/
theorem isLocallyConstant_coeff (h : H) :
    IsLocallyConstant fun a : NovikovSeries R H N => a.coeff h :=
  (IsLocallyConstant.iff_eventually_eq _).2 fun a => by
    filter_upwards [tendsto_nhds_iff.1 (tendsto_id (x := 𝓝 a)) (N h + 1)] with b hb
    exact hb h (lt_add_one _)

/-- The Novikov series are complete for the period topology: the limit of a Cauchy filter has, at
each exponent, the coefficient on which the filter eventually agrees. -/
instance : CompleteSpace (NovikovSeries R H N) := by
  refine ⟨fun {F} hF => ?_⟩
  obtain ⟨hne, hF⟩ := hasBasis_uniformity.cauchy_iff.1 hF
  choose S hSF hS using fun C => hF C trivial
  have hS' : ∀ C, ∀ a ∈ S C, ∀ b ∈ S C, ∀ h, N h < C → a.coeff h = b.coeff h :=
    fun C a ha b hb h hh => (sub_eq_zero.1 (hS C a ha b hb h hh)).symm
  choose x hx using fun C => hne.nonempty_of_mem (hSF C)
  -- The coefficient of the limit at `h` is read off from the set `S (N h + 1)`.
  have hcoeff : ∀ C, ∀ a ∈ S C, ∀ h, N h < C → a.coeff h = (x (N h + 1)).coeff h := by
    intro C a ha h hh
    obtain ⟨b, hbC, hbh⟩ := hne.nonempty_of_mem (inter_mem (hSF C) (hSF (N h + 1)))
    exact (hS' C a ha b hbC h hh).trans
      (hS' _ b hbh _ (hx _) h (lt_add_one _))
  let lim : NovikovSeries R H N :=
    ⟨fun h => (x (N h + 1)).coeff h, fun C => ((x C).finite_lt C).subset fun h hh => by
      refine ⟨?_, hh.2⟩
      rw [hcoeff C (x C) (hx C) h hh.2]
      exact hh.1⟩
  refine ⟨lim, (hasBasis_nhds lim).ge_iff.2 fun C _ => mem_of_superset (hSF C) fun a ha h hh => ?_⟩
  simp [lim, hcoeff C a ha h hh]

end Topology

section Truncation

variable [AddCommGroup R]

/-- A Novikov series differs from its truncation below `C` by an element of `U_C`. -/
theorem sub_ofFinsupp_trunc_mem_periodFiltration (C : ℝ) (a : NovikovSeries R H N) :
    a - ofFinsupp (trunc C a) ∈ periodFiltration R N C := fun h hh => by
  simp [trunc_apply_of_lt hh]

/-- Truncation preserves membership in `U_D`. -/
theorem ofFinsupp_trunc_mem_periodFiltration {D : ℝ} (C : ℝ) {a : NovikovSeries R H N}
    (ha : a ∈ periodFiltration R N D) : ofFinsupp (trunc C a) ∈ periodFiltration R N D :=
  fun h hh => by simp [ha h hh]

/-- The truncations of a Novikov series converge to it as the cutoff tends to `+∞`. -/
theorem tendsto_ofFinsupp_trunc (a : NovikovSeries R H N) :
    Tendsto (fun C => ofFinsupp (trunc C a)) atTop (𝓝 a) :=
  (hasBasis_nhds a).tendsto_right_iff.2 fun C _ => by
    filter_upwards [eventually_ge_atTop C] with D hD
    rw [← neg_mem_iff, neg_sub]
    exact antitone_periodFiltration hD (sub_ofFinsupp_trunc_mem_periodFiltration D a)

/-- The finitely supported Novikov series are dense in the period topology. -/
theorem denseRange_ofFinsupp : DenseRange (ofFinsupp : (H →₀ R) → NovikovSeries R H N) :=
  fun a => mem_closure_of_tendsto (tendsto_ofFinsupp_trunc a) (Eventually.of_forall fun _ =>
    mem_range_self _)

end Truncation

section Completion

variable [AddCommGroup R]

variable (R H N) in
/-- The uniform structure of the period filtration on the group ring `H →₀ R`: the subgroups of
finitely supported functions vanishing at every exponent of period `< C` form a basis of
neighbourhoods of `0` (`TauCeti.NovikovSeries.hasBasis_groupRingUniformSpace`). It is the uniform
structure induced by the inclusion into the Novikov series. -/
@[instance_reducible]
def groupRingUniformSpace : UniformSpace (H →₀ R) :=
  UniformSpace.comap (ofFinsupp (N := N)) inferInstance

/-- The entourages of pairs of finitely supported functions that agree at every exponent of period
`< C` form a basis of the period filtration uniformity on the group ring. -/
theorem hasBasis_groupRingUniformSpace :
    (@uniformity (H →₀ R) (groupRingUniformSpace R H N)).HasBasis (fun _ : ℝ => True)
      fun C => {p | ∀ h, N h < C → p.1 h = p.2 h} := by
  refine (hasBasis_uniformity.comap (Prod.map ofFinsupp ofFinsupp)).to_hasBasis ?_ ?_ <;>
    refine fun C _ => ⟨C, trivial, fun p hp h hh => ?_⟩
  · simp [hp h hh]
  · exact (sub_eq_zero.1 (by simpa using hp h hh : p.2 h - p.1 h = 0)).symm

/-- The group ring carries the uniform structure induced by the inclusion into the Novikov
series. -/
theorem isUniformInducing_ofFinsupp :
    @IsUniformInducing _ _ (groupRingUniformSpace R H N) _ (ofFinsupp (R := R) (N := N)) :=
  @IsUniformInducing.mk _ _ (groupRingUniformSpace R H N) _ _ rfl

variable (R H N) in
/-- The Novikov series are the completion of the group ring `H →₀ R` for the uniform structure
of its period filtration: they are complete and separated, and the inclusion `ofFinsupp` is a
uniform inducing map with dense range. -/
@[expose]
def completionPkg : @AbstractCompletion (H →₀ R) (groupRingUniformSpace R H N) :=
  @AbstractCompletion.mk _ (groupRingUniformSpace R H N) (NovikovSeries R H N) ofFinsupp
    inferInstance inferInstance inferInstance
    isUniformInducing_ofFinsupp denseRange_ofFinsupp

@[simp]
theorem completionPkg_coe :
    @AbstractCompletion.coe _ (groupRingUniformSpace R H N) (completionPkg R H N) =
      ⇑(ofFinsupp (R := R) (N := N)) :=
  rfl

end Completion

end NovikovSeries

end TauCeti
