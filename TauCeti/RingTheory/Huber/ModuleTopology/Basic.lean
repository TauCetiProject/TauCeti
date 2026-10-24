/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Huber.Basic
public import Mathlib.Topology.Algebra.Module.ModuleTopology

import Mathlib.Topology.Algebra.OpenSubgroup

/-!
# The natural topology of a finite module over a Huber ring

Let `A` be a Huber ring with a pair of definition `(A₀, I)` and let `M` be an `A`-module carrying
its natural topology, Mathlib's `IsModuleTopology A M`. For a finitely generated `A₀`-submodule
`M₀ ⊆ M` spanning `M` over `A`, the submodules `Iⁿ • M₀` form a neighbourhood basis of `0`
(Huber, *A generalization of formal schemes and rigid analytic varieties*, §2, before Lemma 2.3).
No noetherian, Tate, or completeness hypothesis is needed.

This is the description of the natural topology through which finite modules over a Huber ring
are compared with `I`-adically topologised modules over its ring of definition: it is the input
for strictness of linear maps and for completeness of finite modules when `A₀` is noetherian.

The file also records the absorption property of a ring of definition: a power of `I` carries a
finitely generated `A₀`-submodule lying in the `A`-span of `K` into `K`.

## Main results

* `TauCeti.Huber.PairOfDefinition.hasBasis_nhds_zero_idealOfDefinition_pow_smul`: the
  submodules `Iⁿ • M₀` form a neighbourhood basis of `0` for the natural topology.
* `TauCeti.Huber.PairOfDefinition.isOpen_of_span_eq_top`: an `A₀`-submodule spanning a finite
  module over `A` is open.
* `TauCeti.Huber.PairOfDefinition.exists_pow_smul_le`: some `Iʲ • L` lies in `K` whenever `L` is
  finitely generated and lies in the `A`-span of `K`. This is the ideal-of-definition analogue
  of `Subring.exists_pow_smul_le`, which uses the powers of a single topologically nilpotent
  element.

## References

* R. Huber, *A generalization of formal schemes and rigid analytic varieties*, Math. Z. 217
  (1994), §2, before Lemma 2.3.
-/

public section

open Filter Topology

namespace TauCeti.Huber.PairOfDefinition

variable {A : Type*} [CommRing A] [TopologicalSpace A] {M : Type*} [AddCommGroup M] [Module A M]

/-- The cubes `(Iⁿ)ᵏ` form a neighbourhood basis of `0` in a finite power of `A`. -/
private theorem hasBasis_nhds_zero_pi (P : PairOfDefinition A) (ι : Type*) [Finite ι] :
    (𝓝 (0 : ι → A)).HasBasis (fun _ : ℕ ↦ True)
      fun n ↦ Set.univ.pi fun _ ↦ (P.idealImage n : Set A) := by
  rw [nhds_pi]
  exact P.hasBasis_nhds_zero.pi_self.to_hasBasis
    (fun Ik _ ↦ ⟨Ik.2, trivial, fun x hx i _ ↦ hx i trivial⟩)
    fun n _ ↦ ⟨(Set.univ, n), ⟨Set.finite_univ, trivial⟩, subset_rfl⟩

/-- The linear-combination map of a finite family `v` carries the cube `(Iⁿ)ᵏ` onto
`Iⁿ • span A₀ (range v)`. -/
private theorem image_linearCombination_pi_idealImage (P : PairOfDefinition A) {ι : Type*}
    [Fintype ι] (v : ι → M) (n : ℕ) :
    Fintype.linearCombination A v '' Set.univ.pi (fun _ ↦ (P.idealImage n : Set A)) =
      ((P.idealOfDefinition ^ n • Submodule.span P.ringOfDefinition (Set.range v) :
        Submodule P.ringOfDefinition M) : Set M) := by
  ext x
  constructor
  · rintro ⟨c, hc, rfl⟩
    rw [Fintype.linearCombination_apply]
    refine Submodule.sum_mem _ fun i _ ↦ ?_
    obtain ⟨y, hy, hyc⟩ := (P.mem_idealImage n).mp (hc i trivial)
    rw [← hyc, ← Subring.smul_def]
    exact Submodule.smul_mem_smul hy (Submodule.subset_span ⟨i, rfl⟩)
  · intro hx
    obtain ⟨a, ha, rfl⟩ := (Submodule.mem_ideal_smul_span_iff_exists_sum _ v x).mp hx
    refine ⟨fun i ↦ (a i : A), fun i _ ↦ (P.mem_idealImage n).mpr ⟨a i, ha i, rfl⟩, ?_⟩
    rw [Fintype.linearCombination_apply,
      Finsupp.sum_fintype a (fun i c ↦ c • v i) fun _ ↦ zero_smul _ _]
    simp_rw [Subring.smul_def]

section IsTopologicalRing

variable [IsTopologicalRing A]

/-- **The natural topology of a module over a Huber ring is the `I`-adic topology of any finitely
generated spanning lattice.** If `M` carries its natural topology and `M₀` is a finitely
generated `A₀`-submodule spanning `M` over `A`, then the submodules `Iⁿ • M₀` form a
neighbourhood basis of `0` in `M`. -/
theorem hasBasis_nhds_zero_idealOfDefinition_pow_smul (P : PairOfDefinition A)
    [TopologicalSpace M] [IsModuleTopology A M] {M₀ : Submodule P.ringOfDefinition M} (hM₀ : M₀.FG)
    (hspan : Submodule.span A (M₀ : Set M) = ⊤) :
    (𝓝 (0 : M)).HasBasis (fun _ : ℕ ↦ True)
      fun n ↦ ((P.idealOfDefinition ^ n • M₀ : Submodule P.ringOfDefinition M) : Set M) := by
  obtain ⟨s, rfl⟩ := hM₀
  let v : s → M := Subtype.val
  have hv : Set.range v = s := Subtype.range_val
  have hsurj : Function.Surjective (Fintype.linearCombination A v) := by
    rw [← span_range_eq_top_iff_surjective_fintypeLinearCombination, hv, ← hspan,
      Submodule.span_span_of_tower]
  have hq := IsModuleTopology.isOpenQuotientMap_of_surjective hsurj
  rw [← map_zero (Fintype.linearCombination A v), ← hq.map_nhds_eq]
  simpa only [image_linearCombination_pi_idealImage, hv] using
    (P.hasBasis_nhds_zero_pi s).map (Fintype.linearCombination A v)

/-- **A spanning lattice is open.** If `M` is a finite `A`-module with its natural topology, every
`A₀`-submodule of `M` spanning `M` over `A` is open in `M`. -/
theorem isOpen_of_span_eq_top (P : PairOfDefinition A) [Module.Finite A M] [TopologicalSpace M]
    [IsModuleTopology A M] {M₀ : Submodule P.ringOfDefinition M}
    (hspan : Submodule.span A (M₀ : Set M) = ⊤) : IsOpen (M₀ : Set M) := by
  have := IsModuleTopology.isTopologicalAddGroup A M
  -- `M₀` contains the `A₀`-span `L` of finitely many of its elements, still spanning `M`.
  obtain ⟨t, htM₀, ht⟩ := (Submodule.fg_span_iff_fg_span_finset_subset (M₀ : Set M)).mp
    (hspan ▸ Module.Finite.fg_top)
  let L := Submodule.span P.ringOfDefinition (t : Set M)
  have hLspan : Submodule.span A (L : Set M) = ⊤ := by
    rw [Submodule.span_span_of_tower, ← ht, hspan]
  have hL : (L : Set M) ∈ 𝓝 0 := by
    simpa using (P.hasBasis_nhds_zero_idealOfDefinition_pow_smul ⟨t, rfl⟩ hLspan).mem_of_mem
      (i := 0) trivial
  exact M₀.toAddSubgroup.isOpen_of_mem_nhds
    (mem_of_superset hL (Submodule.span_le.mpr htM₀))

end IsTopologicalRing

section SeparatelyContinuousMul

variable [SeparatelyContinuousMul A]

/-- A power of `I` carries each element of the `A`-span of an `A₀`-submodule `K` into `K`. -/
private theorem exists_pow_smul_mem (P : PairOfDefinition A) (K : Submodule P.ringOfDefinition M)
    {m : M} (hm : m ∈ Submodule.span A (K : Set M)) :
    ∃ j : ℕ, ∀ t ∈ P.idealOfDefinition ^ j, t • m ∈ K := by
  induction hm using Submodule.span_induction with
  | mem x hx => exact ⟨0, fun t _ ↦ K.smul_mem t hx⟩
  | zero => exact ⟨0, fun t _ ↦ by simp⟩
  | add x y _ _ ihx ihy =>
    obtain ⟨jx, hjx⟩ := ihx
    obtain ⟨jy, hjy⟩ := ihy
    refine ⟨max jx jy, fun t ht ↦ ?_⟩
    rw [smul_add]
    exact K.add_mem (hjx t (Ideal.pow_le_pow_right (le_max_left _ _) ht))
      (hjy t (Ideal.pow_le_pow_right (le_max_right _ _) ht))
  | smul c x _ ih =>
    obtain ⟨j, hj⟩ := ih
    obtain ⟨i, hi⟩ := P.exists_pow_idealOfDefinition_mul_mem P.isOpen_ringOfDefinition c
    refine ⟨i + j, fun t ht ↦ ?_⟩
    rw [pow_add] at ht
    refine Submodule.mul_induction_on ht (fun a ha b hb ↦ ?_) fun a b ha hb ↦ ?_
    · have h : (a * b) • c • x = (⟨c * a, hi a ha⟩ : P.ringOfDefinition) • b • x := by
        simp only [Subring.smul_def, smul_smul, Subring.coe_mul]
        ring_nf
      rw [h]
      exact K.smul_mem _ (hj b hb)
    · rw [add_smul]
      exact K.add_mem ha hb

/-- **A ring of definition absorbs finitely generated submodules of the span.** If `L` is a
finitely generated `A₀`-submodule lying in the `A`-span of an `A₀`-submodule `K`, then
`Iʲ • L ≤ K` for some `j`. -/
theorem exists_pow_smul_le (P : PairOfDefinition A) (K : Submodule P.ringOfDefinition M)
    {L : Submodule P.ringOfDefinition M} (hL : L.FG)
    (hLK : (L : Set M) ⊆ Submodule.span A (K : Set M)) :
    ∃ j : ℕ, P.idealOfDefinition ^ j • L ≤ K := by
  obtain ⟨G, rfl⟩ := hL
  choose! f hf using fun g (hg : g ∈ (G : Set M)) ↦
    P.exists_pow_smul_mem K (hLK (Submodule.subset_span hg))
  refine ⟨G.sup f, Submodule.smul_le.mpr fun t ht m hm ↦ ?_⟩
  induction hm using Submodule.span_induction with
  | mem g hg => exact hf g hg t (Ideal.pow_le_pow_right (Finset.le_sup (f := f) hg) ht)
  | zero => simp
  | add x y _ _ hx hy => rw [smul_add]; exact K.add_mem hx hy
  | smul c x _ hx => rw [smul_comm]; exact K.smul_mem c hx

end SeparatelyContinuousMul

end TauCeti.Huber.PairOfDefinition
