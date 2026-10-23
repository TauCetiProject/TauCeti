/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.NovikovModule.Basic
public import TauCeti.RingTheory.NovikovSeries.TopologicalRing
public import Mathlib.Topology.Algebra.Module.Equiv.Basic

/-!
# The potential-cutoff topology on completed modules

A completed combination with potential `F` is small when its coefficients vanish above a low
potential threshold. The subgroups `potentialFiltration R F C` define this topology intrinsically,
without choosing orbit lifts. Convergence means eventual agreement above every threshold,
uniformly over all generators there, not just convergence of each coefficient separately.

The topology is separated and complete, and finite combinations are dense. For a finite family
of torsors with equivariant potential, every choice of lifts gives a continuous linear
equivalence with a finite product of Novikov series. Thus the topology is independent of lifts,
and the Novikov scalar action is continuous. Reference potentials enter the exact cutoff
formula, so no normalization of those potentials is required.

The filter-basis construction and the coefficient stabilization argument parallel
`TauCeti.RingTheory.NovikovSeries.Topology`, with potential cutoffs directed towards negative
infinity rather than period cutoffs towards positive infinity.

## References

* M. Hutchings and Y.-J. Lee, *Circle-valued Morse theory and Reidemeister torsion*,
  Geom. Topol. 3 (1999), Section 2.
* A. Pajitnov, *Circle-valued Morse Theory*, de Gruyter 2006, Chapter 3.
-/

public section

noncomputable section

open Filter Function Set Topology Uniformity

namespace TauCeti.NovikovModule

variable {R S : Type*} [Ring R] {F : S → ℝ}

/-- Completed combinations vanishing above potential `C`. These subgroups increase with `C`
and form a basis of neighborhoods of zero as `C` tends to negative infinity. -/
def potentialFiltration (R : Type*) [Ring R] (F : S → ℝ) (C : ℝ) :
    AddSubgroup (NovikovModule R F) where
  carrier := {a | ∀ s, C < F s → a.val s = 0}
  zero_mem' _ _ := rfl
  add_mem' ha hb s hs := by simp [ha s hs, hb s hs]
  neg_mem' ha s hs := by simp [ha s hs]

@[simp]
theorem mem_potentialFiltration {C : ℝ} {a : NovikovModule R F} :
    a ∈ potentialFiltration R F C ↔ ∀ s, C < F s → a.val s = 0 := Iff.rfl

/-- Raising the cutoff enlarges its vanishing subgroup. -/
theorem monotone_potentialFiltration : Monotone (potentialFiltration R F) :=
  fun _ _ hCD _ ha s hs => ha s (hCD.trans_lt hs)

/-- The additive filter basis of potential-cutoff subgroups. -/
@[instance_reducible]
def potentialFilterBasis (R : Type*) [Ring R] (F : S → ℝ) :
    AddGroupFilterBasis (NovikovModule R F) :=
  addGroupFilterBasisOfComm (range fun C => (potentialFiltration R F C : Set _))
    (range_nonempty _)
    (by
      rintro _ _ ⟨C, rfl⟩ ⟨D, rfl⟩
      exact ⟨_, mem_range_self (min C D),
        subset_inter (monotone_potentialFiltration (min_le_left C D))
          (monotone_potentialFiltration (min_le_right C D))⟩)
    (by rintro _ ⟨C, rfl⟩; exact zero_mem (potentialFiltration R F C))
    (by
      rintro _ ⟨C, rfl⟩
      exact ⟨_, mem_range_self C, by
        rintro _ ⟨a, ha, b, hb, rfl⟩
        exact add_mem ha hb⟩)
    (by
      rintro _ ⟨C, rfl⟩
      exact ⟨_, mem_range_self C, fun a ha => neg_mem ha⟩)

/-- The intrinsic topology defined by vanishing above potential cutoffs. -/
instance : TopologicalSpace (NovikovModule R F) := (potentialFilterBasis R F).topology

instance : IsTopologicalAddGroup (NovikovModule R F) :=
  (potentialFilterBasis R F).isTopologicalAddGroup

/-- The additive uniformity of the potential-cutoff topology. -/
instance : UniformSpace (NovikovModule R F) := IsTopologicalAddGroup.rightUniformSpace _

instance : IsUniformAddGroup (NovikovModule R F) := isUniformAddGroup_of_addCommGroup

/-- Potential-cutoff subgroups form a neighborhood basis at zero. -/
theorem hasBasis_nhds_zero :
    (𝓝 (0 : NovikovModule R F)).HasBasis (fun _ : ℝ => True)
      fun C => (potentialFiltration R F C : Set _) := by
  refine ((potentialFilterBasis R F).nhds_zero_hasBasis).to_hasBasis ?_ ?_
  · rintro _ ⟨C, rfl⟩
    exact ⟨C, trivial, subset_rfl⟩
  · exact fun C _ => ⟨_, mem_range_self C, subset_rfl⟩

/-- Potential-cutoff subgroups are open in the intrinsic topology. -/
theorem isOpen_potentialFiltration (C : ℝ) :
    IsOpen (potentialFiltration R F C : Set (NovikovModule R F)) :=
  AddSubgroup.isOpen_of_mem_nhds _ (hasBasis_nhds_zero.mem_of_mem trivial)

/-- Potential-cutoff subgroups are closed in the intrinsic topology. -/
theorem isClosed_potentialFiltration (C : ℝ) :
    IsClosed (potentialFiltration R F C : Set (NovikovModule R F)) :=
  AddSubgroup.isClosed_of_isOpen _ (isOpen_potentialFiltration C)

/-- Neighborhoods of a combination prescribe agreement above a potential cutoff. -/
theorem hasBasis_nhds (a : NovikovModule R F) :
    (𝓝 a).HasBasis (fun _ : ℝ => True)
      fun C => {b | b - a ∈ potentialFiltration R F C} := by
  rw [← nhds_translation_sub a]
  exact hasBasis_nhds_zero.comap _

/-- Entourages prescribe uniform agreement above a potential cutoff. -/
theorem hasBasis_uniformity :
    (𝓤 (NovikovModule R F)).HasBasis (fun _ : ℝ => True)
      fun C => {p | p.2 - p.1 ∈ potentialFiltration R F C} := by
  rw [uniformity_eq_comap_nhds_zero]
  exact hasBasis_nhds_zero.comap _

/-- Convergence is eventual agreement of all coefficients above each fixed threshold. -/
theorem tendsto_nhds_iff {α : Type*} {l : Filter α} {f : α → NovikovModule R F}
    {a : NovikovModule R F} :
    Tendsto f l (𝓝 a) ↔ ∀ C : ℝ, ∀ᶠ i in l,
      ∀ s, C < F s → (f i).val s = a.val s := by
  simp [(hasBasis_nhds a).tendsto_right_iff, sub_eq_zero]

instance : T2Space (NovikovModule R F) :=
  IsTopologicalAddGroup.t2Space_of_zero_sep fun a ha => by
    obtain ⟨s, hs⟩ : ∃ s, a.val s ≠ 0 := by
      by_contra! h
      exact ha (Subtype.ext (funext h))
    exact ⟨_, hasBasis_nhds_zero.mem_of_mem (i := F s - 1) trivial,
      fun h => hs (h s (by linarith))⟩

/-- Every Cauchy filter stabilizes each cutoff simultaneously, yielding a completed combination. -/
instance : CompleteSpace (NovikovModule R F) := by
  refine ⟨fun {l} hl => ?_⟩
  obtain ⟨hne, hl⟩ := hasBasis_uniformity.cauchy_iff.1 hl
  choose U hUl hU using fun C => hl C trivial
  have hU' : ∀ C, ∀ a ∈ U C, ∀ b ∈ U C, ∀ s, C < F s → a.val s = b.val s :=
    fun C a ha b hb s hs => (sub_eq_zero.1 (hU C a ha b hb s hs)).symm
  choose x hx using fun C => hne.nonempty_of_mem (hUl C)
  have hcoeff : ∀ C, ∀ a ∈ U C, ∀ s, C < F s → a.val s = (x (F s - 1)).val s := by
    intro C a ha s hs
    obtain ⟨b, hbC, hbs⟩ := hne.nonempty_of_mem (inter_mem (hUl C) (hUl (F s - 1)))
    exact (hU' C a ha b hbC s hs).trans (hU' _ b hbs _ (hx _) s (by linarith))
  let lim : NovikovModule R F :=
    ⟨fun s => (x (F s - 1)).val s, mem_iff.2 fun C =>
      (finite_gt (x C) C).subset fun s hs => by
        refine ⟨?_, hs.2⟩
        rw [hcoeff C (x C) (hx C) s hs.2]
        exact hs.1⟩
  refine ⟨lim, (hasBasis_nhds lim).ge_iff.2 fun C _ =>
    mem_of_superset (hUl C) fun a ha s hs => ?_⟩
  simp [lim, hcoeff C a ha s hs]

/-- Finite truncations converge as their potential threshold tends to negative infinity. -/
theorem tendsto_ofFinsupp_trunc (a : NovikovModule R F) :
    Tendsto (fun C => ofFinsupp (trunc C a)) atBot (𝓝 a) := by
  refine tendsto_nhds_iff.2 fun C => ?_
  filter_upwards [eventually_le_atBot C] with D hD s hs
  simp [hD.trans_lt hs]

/-- Finite combinations are dense for the intrinsic cutoff topology. -/
theorem denseRange_ofFinsupp : DenseRange (ofFinsupp : (S →₀ R) → NovikovModule R F) :=
  fun a => mem_closure_of_tendsto (tendsto_ofFinsupp_trunc a)
    (Eventually.of_forall fun _ => mem_range_self _)

section Coordinates

variable {H ι : Type*} [AddGroup H] [Finite ι] {P : ι → Type*}
    [∀ i, AddTorsor H (P i)] {N : H →+ ℝ} {F : (Σ i, P i) → ℝ}
    (hF : ∀ i h (p : P i), F ⟨i, h +ᵥ p⟩ = F ⟨i, p⟩ - N h)
    (r : ∀ i, P i)

/-- The intrinsic potential cutoff is the orbitwise period cutoff, with its reference constant. -/
theorem mem_potentialFiltration_iff_coordinates {C : ℝ} {a : NovikovModule R F} :
    a ∈ potentialFiltration R F C ↔ ∀ i,
      coordinates hF r a i ∈ NovikovSeries.periodFiltration R N (F ⟨i, r i⟩ - C) := by
  simp only [mem_potentialFiltration, NovikovSeries.mem_periodFiltration]
  exact (coordinates_coeff_eq_zero_iff hF r a C).symm

/-- Coordinates in any lifts are continuous for the intrinsic potential topology. -/
@[fun_prop]
theorem continuous_coordinates : Continuous (coordinates (R := R) hF r) := by
  refine continuous_pi fun i => continuous_iff_continuousAt.2 fun a => ?_
  apply NovikovSeries.tendsto_nhds_iff.2
  intro C
  filter_upwards [tendsto_nhds_iff.1 (tendsto_id (x := 𝓝 a)) (F ⟨i, r i⟩ - C)] with b hb h hh
  simpa only [coordinates_coeff, id_eq] using hb ⟨i, h +ᵥ r i⟩ (by rw [hF]; linarith)

/-- Reconstructing coefficients from finitely many orbit coordinates is continuous. -/
@[fun_prop]
theorem continuous_coordinates_symm : Continuous (coordinates (R := R) hF r).symm := by
  refine continuous_iff_continuousAt.2 fun b => tendsto_nhds_iff.2 fun C => ?_
  have hi : ∀ i, ∀ᶠ b' in 𝓝 b, ∀ h, N h < F ⟨i, r i⟩ - C →
      (b' i).coeff h = (b i).coeff h := fun i =>
    NovikovSeries.tendsto_nhds_iff.1 (continuous_apply i |>.tendsto b) _
  filter_upwards [eventually_all.2 hi] with b' hb ⟨i, p⟩ hp
  simp only [coordinates_symm_apply]
  exact hb i (p -ᵥ r i) (by linarith [potential_eq_sub_vsub hF r i p])

/-- Every choice of orbit lifts identifies the intrinsic completion topologically and
Novikov-linearly with the finite product of period-completed coefficients. -/
def coordinatesContinuousLinearEquiv :
    letI := module (R := R) hF
    NovikovModule R F ≃L[NovikovSeries R H N] (ι → NovikovSeries R H N) :=
  letI := module (R := R) hF
  { coordinatesLinearEquiv hF r with
    continuous_toFun := by
      rw [LinearEquiv.toFun_eq_coe]
      exact (continuous_coordinates (R := R) hF r).congr fun a =>
        (coordinatesLinearEquiv_apply hF r a).symm
    continuous_invFun := by
      rw [LinearEquiv.invFun_eq_symm]
      exact (continuous_coordinates_symm (R := R) hF r).congr fun b =>
        (coordinatesLinearEquiv_symm_apply hF r b).symm }

@[simp]
theorem coordinatesContinuousLinearEquiv_apply (a : NovikovModule R F) :
    coordinatesContinuousLinearEquiv hF r a = coordinates hF r a := by
  simp [coordinatesContinuousLinearEquiv]

@[simp]
theorem coordinatesContinuousLinearEquiv_symm_apply (b : ι → NovikovSeries R H N) :
    letI := module (R := R) hF
    (coordinatesContinuousLinearEquiv hF r).symm b = (coordinates hF r).symm b := by
  let := module (R := R) hF
  rw [← ContinuousLinearEquiv.coe_symm_toLinearEquiv]
  exact coordinatesLinearEquiv_symm_apply hF r b

/-- The intrinsic cutoff topology makes the lift-independent Novikov scalar action continuous. -/
theorem continuousSMul_module :
    letI := module (R := R) hF
    ContinuousSMul (NovikovSeries R H N) (NovikovModule R F) := by
  let := module (R := R) hF
  let r := fun i => Classical.arbitrary (P i)
  refine ⟨?_⟩
  have hc : Continuous (fun p : NovikovSeries R H N × NovikovModule R F =>
      p.1 • coordinates hF r p.2) :=
    continuous_fst.smul ((continuous_coordinates hF r).comp continuous_snd)
  exact ((continuous_coordinates_symm hF r).comp hc).congr fun p => by
    simp only [Function.comp_apply, ← coordinates_smul, LinearEquiv.symm_apply_apply]

end Coordinates

end TauCeti.NovikovModule
