/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.ZLattice.Covolume
public import Mathlib.Data.Set.Card
public import TauCeti.Algebra.Module.ZLattice.Integral
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import TauCeti.Topology.MetricSpace.DiscreteAddSubgroup

/-!
# Shells and representation numbers of a lattice

For a `ℤ`-submodule `L` of a real normed space `E` and a real number `t`, the *shell* of squared
norm `t` is the set of lattice vectors

`shell L t = {v ∈ L | ‖v‖² = t}`,

and the *representation number* `r_L(t)` is its cardinality. More generally, for `γ : E` the
shell of the translate `γ + L` is `cosetShell L γ t = {v ∈ L | ‖γ + v‖² = t}`, with cardinality
`r_{γ+L}(t)`. In a real inner product space these are the counts that the theta series
`Θ_L(τ) = ∑_{v ∈ L} e^{π i ‖v‖² τ}` and the coset theta series `θ_{γ+L}` expand: grouping the terms
by squared norm, `r_L(t)` is the coefficient of `e^{π i t τ}`. That identification is not made
here.

The shells are sets with a finiteness theorem rather than `Finset`s, since membership is not
decidable and the finiteness is the content: for a discrete `L` in a finite-dimensional space,
every shell lies in a bounded set, which meets `L` in finitely many points.

This file proves that every shell is finite, that `r_L(0) = 1` and that negative numbers are not
represented; that the representation numbers of a translate depend only on its coset, are
unchanged by `γ ↦ -γ`, and are invariant under linear isometries; that an even lattice represents
only even natural numbers and an integral lattice only natural numbers; and that for a full
lattice `L` in a real normed space of dimension `n` the representation numbers grow at most like
`t^{n/2}`, from the count of lattice points in a ball, which is `O(R^n)` by Mathlib's asymptotic
lattice-point count `ZLattice.covolume.tendsto_card_le_div''`.

## Main definitions

* `ZLattice.shell L t`: the lattice vectors of squared norm `t`.
* `ZLattice.representationNumber L t`: the number `r_L(t)` of lattice vectors of squared norm `t`.
* `ZLattice.cosetShell L γ t`: the lattice vectors `v` with `‖γ + v‖² = t`.
* `ZLattice.cosetRepresentationNumber L γ t`: their number `r_{γ+L}(t)`.

## Main statements

* `ZLattice.finite_shell`, `ZLattice.finite_cosetShell`: shells of a discrete subgroup of a
  finite-dimensional space are finite.
* `ZLattice.representationNumber_zero`: `r_L(0) = 1`.
* `ZLattice.cosetRepresentationNumber_add_mem`, `ZLattice.cosetRepresentationNumber_neg`:
  `r_{γ+L}` depends only on the coset `γ + L`, and `r_{-γ+L} = r_{γ+L}`.
* `ZLattice.representationNumber_comap`, `ZLattice.cosetRepresentationNumber_comap`: invariance
  under linear isometry equivalences.
* `ZLattice.IsEven.shell_eq_empty`, `ZLattice.IsIntegral.shell_eq_empty`: an even lattice has no
  vector of squared norm outside `2ℕ`, an integral lattice none outside `ℕ`.
* `ZLattice.ncard_closedBall_inter_isBigO`: a full lattice has `O(R^n)` points in the ball of
  radius `R`.
* `ZLattice.representationNumber_isBigO`: `r_L(t) = O(t^{n/2})` as `t → ∞`.

## References

* J.-P. Serre, *A Course in Arithmetic*, Ch. VII §6.
* J. H. Conway and N. J. A. Sloane, *Sphere Packings, Lattices and Groups*, Chapter 2, §2.3.
-/

public section

open Filter Asymptotics Metric Module MeasureTheory
open scoped RealInnerProductSpace

namespace ZLattice

variable {E F : Type*} [NormedAddCommGroup E] [NormedAddCommGroup F]

/-! ### Shells and representation numbers -/

/-- The shell of squared norm `t` of `L`: the vectors `v ∈ L` with `‖v‖² = t`. It is finite when
`L` is discrete in a finite-dimensional space (`ZLattice.finite_shell`). -/
def shell (L : Submodule ℤ E) (t : ℝ) : Set E :=
  {v | v ∈ L ∧ ‖v‖ ^ 2 = t}

/-- The representation number `r_L(t)`: the number of vectors of `L` of squared norm `t`. For a
discrete `L` in a finite-dimensional space every shell is finite, so this is a genuine count. -/
noncomputable def representationNumber (L : Submodule ℤ E) (t : ℝ) : ℕ :=
  (shell L t).ncard

/-- The shell of squared norm `t` of the translate `γ + L`: the vectors `v ∈ L` with
`‖γ + v‖² = t`. For `γ` in the dual lattice these are the vectors of the coset `γ + L` of squared
norm `t`, translated back into `L`. -/
def cosetShell (L : Submodule ℤ E) (γ : E) (t : ℝ) : Set E :=
  {v | v ∈ L ∧ ‖γ + v‖ ^ 2 = t}

/-- The representation number `r_{γ+L}(t)` of the translate `γ + L`: the number of vectors
`v ∈ L` with `‖γ + v‖² = t`. -/
noncomputable def cosetRepresentationNumber (L : Submodule ℤ E) (γ : E) (t : ℝ) : ℕ :=
  (cosetShell L γ t).ncard

variable {L : Submodule ℤ E} {t : ℝ}

@[simp]
theorem mem_shell {v : E} : v ∈ shell L t ↔ v ∈ L ∧ ‖v‖ ^ 2 = t :=
  Iff.rfl

@[simp]
theorem mem_cosetShell {γ v : E} : v ∈ cosetShell L γ t ↔ v ∈ L ∧ ‖γ + v‖ ^ 2 = t :=
  Iff.rfl

variable (L)

theorem representationNumber_def (t : ℝ) : representationNumber L t = (shell L t).ncard :=
  (rfl)

theorem cosetRepresentationNumber_def (γ : E) (t : ℝ) :
    cosetRepresentationNumber L γ t = (cosetShell L γ t).ncard :=
  (rfl)

theorem shell_subset (t : ℝ) : shell L t ⊆ L :=
  fun _ hv ↦ hv.1

theorem cosetShell_subset (γ : E) (t : ℝ) : cosetShell L γ t ⊆ L :=
  fun _ hv ↦ hv.1

/-- The shells of the translate `0 + L` are the shells of `L`. -/
@[simp]
theorem cosetShell_zero_left (t : ℝ) : cosetShell L 0 t = shell L t := by
  ext v
  simp

@[simp]
theorem cosetRepresentationNumber_zero_left (t : ℝ) :
    cosetRepresentationNumber L 0 t = representationNumber L t := by
  rw [cosetRepresentationNumber_def, cosetShell_zero_left, representationNumber_def]

/-- The only lattice vector of squared norm `0` is `0`. -/
@[simp]
theorem shell_zero : shell L 0 = {0} := by
  ext v
  simp only [mem_shell, Set.mem_singleton_iff, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
    pow_eq_zero_iff, norm_eq_zero]
  exact ⟨fun h ↦ h.2, fun h ↦ ⟨h ▸ L.zero_mem, h⟩⟩

/-- A lattice represents `0` exactly once: `r_L(0) = 1`. -/
@[simp]
theorem representationNumber_zero : representationNumber L 0 = 1 := by
  rw [representationNumber_def, shell_zero, Set.ncard_singleton]

/-- No translate of a lattice has a vector of negative squared norm. -/
theorem cosetShell_eq_empty_of_neg (γ : E) (ht : t < 0) : cosetShell L γ t = ∅ :=
  Set.eq_empty_of_forall_notMem fun v hv ↦ (hv.2 ▸ ht).not_ge (by positivity)

theorem cosetRepresentationNumber_eq_zero_of_neg (γ : E) (ht : t < 0) :
    cosetRepresentationNumber L γ t = 0 := by
  rw [cosetRepresentationNumber_def, cosetShell_eq_empty_of_neg L γ ht, Set.ncard_empty]

/-- A lattice has no vector of negative squared norm. -/
theorem shell_eq_empty_of_neg (ht : t < 0) : shell L t = ∅ := by
  simpa using cosetShell_eq_empty_of_neg L 0 ht

theorem representationNumber_eq_zero_of_neg (ht : t < 0) : representationNumber L t = 0 := by
  simpa using cosetRepresentationNumber_eq_zero_of_neg L 0 ht

/-! ### Dependence on the coset -/

/-- Translating `γ` by a lattice vector `w` translates the shells of `γ + L` by `-w`. -/
theorem cosetShell_add_mem (γ : E) {w : E} (hw : w ∈ L) (t : ℝ) :
    cosetShell L (γ + w) t = (· - w) '' cosetShell L γ t := by
  ext v
  simp only [mem_cosetShell, Set.mem_image]
  refine ⟨fun ⟨hv, h⟩ ↦ ⟨w + v, ⟨add_mem hw hv, by rwa [← add_assoc]⟩, by abel⟩, ?_⟩
  rintro ⟨u, ⟨hu, h⟩, rfl⟩
  exact ⟨sub_mem hu hw, by rwa [add_add_sub_cancel]⟩

/-- The representation numbers of `γ + L` depend only on the coset of `γ` modulo `L`. -/
theorem cosetRepresentationNumber_add_mem (γ : E) {w : E} (hw : w ∈ L) (t : ℝ) :
    cosetRepresentationNumber L (γ + w) t = cosetRepresentationNumber L γ t := by
  rw [cosetRepresentationNumber_def, cosetShell_add_mem L γ hw,
    Set.ncard_image_of_injective _ (sub_left_injective (b := w)), cosetRepresentationNumber_def]

/-- Translates by vectors congruent modulo `L` have the same representation numbers. -/
theorem cosetRepresentationNumber_eq_of_sub_mem {γ δ : E} (h : γ - δ ∈ L) (t : ℝ) :
    cosetRepresentationNumber L γ t = cosetRepresentationNumber L δ t := by
  simpa using cosetRepresentationNumber_add_mem L δ h t

/-- Negating `γ` negates the shells of `γ + L`. -/
theorem cosetShell_neg (γ : E) (t : ℝ) : cosetShell L (-γ) t = -cosetShell L γ t := by
  ext v
  simp only [mem_cosetShell, Set.mem_neg, neg_mem_iff]
  rw [← norm_neg (-γ + v), neg_add, neg_neg]

/-- The translates `γ + L` and `-γ + L` have the same representation numbers. -/
@[simp]
theorem cosetRepresentationNumber_neg (γ : E) (t : ℝ) :
    cosetRepresentationNumber L (-γ) t = cosetRepresentationNumber L γ t := by
  rw [cosetRepresentationNumber_def, cosetShell_neg, ← Set.image_neg_eq_neg,
    Set.ncard_image_of_injective _ neg_injective, cosetRepresentationNumber_def]

/-! ### Invariance under isometries -/

section Isometry

variable [NormedSpace ℝ E] [NormedSpace ℝ F] (e : F ≃ₗᵢ[ℝ] E)

/-- A linear isometry equivalence `e` carries the shells of the pull-back of `L` along `e` to the
shells of `L`. -/
theorem cosetShell_comap (γ : F) (t : ℝ) :
    cosetShell (ZLattice.comap ℝ L e.toLinearEquiv.toLinearMap) γ t =
      e ⁻¹' cosetShell L (e γ) t := by
  ext v
  simp [← map_add, e.norm_map]

/-- Representation numbers of translates are invariant under linear isometry equivalences. -/
@[simp]
theorem cosetRepresentationNumber_comap (γ : F) (t : ℝ) :
    cosetRepresentationNumber (ZLattice.comap ℝ L e.toLinearEquiv.toLinearMap) γ t =
      cosetRepresentationNumber L (e γ) t := by
  rw [cosetRepresentationNumber_def, cosetShell_comap,
    Set.ncard_preimage_of_injective_subset_range e.injective (by simp [e.surjective.range_eq]),
    cosetRepresentationNumber_def]

/-- A linear isometry equivalence `e` carries the shells of the pull-back of `L` along `e` to the
shells of `L`. -/
theorem shell_comap (t : ℝ) :
    shell (ZLattice.comap ℝ L e.toLinearEquiv.toLinearMap) t = e ⁻¹' shell L t := by
  simpa using cosetShell_comap L e 0 t

/-- Representation numbers are invariant under linear isometry equivalences. -/
@[simp]
theorem representationNumber_comap (t : ℝ) :
    representationNumber (ZLattice.comap ℝ L e.toLinearEquiv.toLinearMap) t =
      representationNumber L t := by
  simpa using cosetRepresentationNumber_comap L e 0 t

end Isometry

/-! ### Finiteness -/

section Finite

variable [NormedSpace ℝ E] [FiniteDimensional ℝ E] [DiscreteTopology L]

/-- The shells of a translate of a discrete subgroup of a finite-dimensional space are finite. -/
theorem finite_cosetShell (γ : E) (t : ℝ) : (cosetShell L γ t).Finite := by
  have : DiscreteTopology L.toAddSubgroup := ‹DiscreteTopology L›
  refine (L.toAddSubgroup.finite_inter (isBounded_closedBall (x := -γ) (r := √t))).subset
    fun v ⟨hv, h⟩ ↦ ⟨?_, hv⟩
  rw [mem_closedBall, dist_eq_norm, sub_neg_eq_add, add_comm, ← h, Real.sqrt_sq (norm_nonneg _)]

/-- The shells of a discrete subgroup of a finite-dimensional space are finite. -/
theorem finite_shell (t : ℝ) : (shell L t).Finite := by
  simpa using finite_cosetShell L 0 t

variable {L}

/-- `r_{γ+L}(t)` vanishes exactly when the shell is empty. -/
theorem cosetRepresentationNumber_eq_zero_iff {γ : E} :
    cosetRepresentationNumber L γ t = 0 ↔ cosetShell L γ t = ∅ :=
  Set.ncard_eq_zero (finite_cosetShell L γ t)

/-- `r_L(t)` vanishes exactly when no lattice vector has squared norm `t`. -/
theorem representationNumber_eq_zero_iff :
    representationNumber L t = 0 ↔ shell L t = ∅ :=
  Set.ncard_eq_zero (finite_shell L t)

end Finite

/-! ### The represented numbers of even and integral lattices -/

variable {L}

/-- An even lattice only represents even natural numbers. -/
theorem IsEven.shell_eq_empty (h : IsEven L) (ht : ¬ ∃ m : ℕ, t = 2 * m) : shell L t = ∅ := by
  refine Set.eq_empty_of_forall_notMem fun v ⟨hv, hvt⟩ ↦ ht ?_
  obtain ⟨m, hm⟩ := isEven_iff.mp h v hv
  have hm0 : 0 ≤ m := by
    have : (0 : ℝ) ≤ 2 * m := hm ▸ by positivity
    exact_mod_cast (by linarith : (0 : ℝ) ≤ m)
  lift m to ℕ using hm0
  exact ⟨m, by rw [← hvt, hm]; norm_cast⟩

theorem IsEven.representationNumber_eq_zero (h : IsEven L) (ht : ¬ ∃ m : ℕ, t = 2 * m) :
    representationNumber L t = 0 := by
  rw [representationNumber_def, h.shell_eq_empty ht, Set.ncard_empty]

section Inner

variable [InnerProductSpace ℝ E]

/-- An integral lattice only represents natural numbers. -/
theorem IsIntegral.shell_eq_empty (h : IsIntegral L) (ht : ¬ ∃ m : ℕ, t = m) : shell L t = ∅ := by
  refine Set.eq_empty_of_forall_notMem fun v ⟨hv, hvt⟩ ↦ ht ?_
  obtain ⟨m, hm⟩ := isIntegral_iff.mp h v hv v hv
  rw [real_inner_self_eq_norm_sq, hvt] at hm
  have hm0 : 0 ≤ m := by
    have : (0 : ℝ) ≤ m := hm ▸ hvt ▸ by positivity
    exact_mod_cast this
  lift m to ℕ using hm0
  exact ⟨m, by rw [hm]; norm_cast⟩

theorem IsIntegral.representationNumber_eq_zero (h : IsIntegral L) (ht : ¬ ∃ m : ℕ, t = m) :
    representationNumber L t = 0 := by
  rw [representationNumber_def, h.shell_eq_empty ht, Set.ncard_empty]

end Inner

/-! ### Growth of the representation numbers -/

section Growth

variable [NormedSpace ℝ E] [FiniteDimensional ℝ E] (L) [DiscreteTopology L] [IsZLattice ℝ L]

/-- A full lattice in a real normed space of dimension `n` has `O(R^n)` points in the closed ball
of radius `R` about the origin, as `R → ∞`. -/
theorem ncard_closedBall_inter_isBigO :
    (fun R : ℝ ↦ ((closedBall (0 : E) R ∩ L).ncard : ℝ)) =O[atTop]
      fun R ↦ R ^ finrank ℝ E := by
  rcases subsingleton_or_nontrivial E with hE | hE
  · refine IsBigO.of_bound 1 (Eventually.of_forall fun R ↦ ?_)
    simp only [finrank_zero_of_subsingleton, pow_zero, norm_one, mul_one, Real.norm_natCast]
    exact_mod_cast Set.ncard_le_one_of_subsingleton _
  let : MeasurableSpace E := borel E
  have : BorelSpace E := ⟨rfl⟩
  set n := finrank ℝ E
  have hn : n ≠ 0 := finrank_pos.ne'
  -- The sublevel sets of `x ↦ ‖x‖ ^ n` are the closed balls.
  have hball : ∀ R, 0 ≤ R → {x : E | ‖x‖ ^ n ≤ R ^ n} = closedBall 0 R := by
    intro R hR
    ext x
    simp [pow_le_pow_iff_left₀ (norm_nonneg x) hR hn]
  have h1 : {x : E | x ∈ Set.univ ∧ ‖x‖ ^ n ≤ 1} = closedBall 0 1 := by
    simpa using hball 1 zero_le_one
  -- Mathlib's asymptotic count of lattice points in the dilates of the unit ball, in the
  -- coordinates of a `ℤ`-basis `b` of `L`.
  let b := Free.chooseBasis ℤ L
  have : Nonempty (Free.ChooseBasisIndex ℤ L) := by
    have : Nontrivial L := nontrivial_of_finrank_pos <| (ZLattice.rank ℝ L).symm ▸ finrank_pos
    infer_instance
  have hcard : Fintype.card (Free.ChooseBasisIndex ℤ L) = n := by
    rw [← finrank_eq_card_chooseBasisIndex, ZLattice.rank ℝ L]
  -- The image of the unit sphere in the coordinates of `b` is null, being the preimage of a
  -- sphere under a linear equivalence.
  have hnull :
      volume (frontier ((b.ofZLatticeBasis ℝ L).equivFun '' closedBall (0 : E) 1)) = 0 := by
    let f := (b.ofZLatticeBasis ℝ L).equivFunL
    rw [show (b.ofZLatticeBasis ℝ L).equivFun '' closedBall (0 : E) 1 = f.symm ⁻¹' closedBall 0 1
        from (b.ofZLatticeBasis ℝ L).equivFun.image_eq_preimage_symm _,
      ← IsOpenMap.preimage_frontier_eq_frontier_preimage (f := f.symm)
        f.symm.toHomeomorph.isOpenMap f.symm.continuous,
      ← Measure.map_apply f.symm.continuous.measurable isClosed_frontier.measurableSet,
      frontier_closedBall _ one_ne_zero]
    exact Measure.addHaar_sphere _ _ _
  have key := covolume.tendsto_card_le_div'' b (X := Set.univ) (F := fun x ↦ ‖x‖ ^ n)
    (fun _ _ _ _ ↦ Set.mem_univ _)
    (fun x r hr ↦ by rw [hcard, norm_smul, Real.norm_of_nonneg hr, mul_pow])
    (h1 ▸ isBounded_closedBall) (h1 ▸ measurableSet_closedBall) (h1 ▸ hnull)
  have hO : (fun c : ℝ ↦ (Nat.card ({x : E | x ∈ Set.univ ∧ ‖x‖ ^ n ≤ c} ∩ L : Set E) : ℝ))
      =O[atTop] fun c ↦ c :=
    isBigO_of_div_tendsto_nhds ((eventually_gt_atTop 0).mono fun c hc h0 ↦ absurd h0 hc.ne') _ key
  refine (hO.comp_tendsto (tendsto_pow_atTop hn)).congr' ?_ (Eventually.of_forall fun _ ↦ rfl)
  filter_upwards [eventually_ge_atTop 0] with R hR
  simp only [Function.comp_apply, Nat.card_coe_set_eq, Set.mem_univ, true_and, hball R hR]

/-- The representation numbers of a full lattice in a real normed space of dimension `n` grow at
most like `t^{n/2}`: `r_L(t) = O(t^{n/2})` as `t → ∞`. -/
theorem representationNumber_isBigO :
    (fun t : ℝ ↦ (representationNumber L t : ℝ)) =O[atTop]
      fun t ↦ t ^ ((finrank ℝ E : ℝ) / 2) := by
  have hball := (ncard_closedBall_inter_isBigO L).comp_tendsto Real.tendsto_sqrt_atTop
  refine IsBigO.trans ?_ (hball.congr' (Eventually.of_forall fun _ ↦ rfl) ?_)
  · refine IsBigO.of_bound 1 (Eventually.of_forall fun t ↦ ?_)
    simp only [Real.norm_natCast, Function.comp_apply, one_mul]
    have : DiscreteTopology L.toAddSubgroup := ‹DiscreteTopology L›
    refine Nat.cast_le.mpr (Set.ncard_le_ncard (fun v ⟨hv, hvt⟩ ↦ ⟨?_, hv⟩)
      (L.toAddSubgroup.finite_inter isBounded_closedBall))
    rw [mem_closedBall_zero_iff, ← hvt, Real.sqrt_sq (norm_nonneg v)]
  · filter_upwards [eventually_ge_atTop 0] with t ht
    rw [Function.comp_apply, Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul ht]
    congr 1
    ring

end Growth

end ZLattice
