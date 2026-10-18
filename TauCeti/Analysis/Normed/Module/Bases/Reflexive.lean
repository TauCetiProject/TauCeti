/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Module.Bases
public import TauCeti.Analysis.Normed.Module.Dual.Reflexive.WeakCompact
import Mathlib.Analysis.Normed.Group.Quotient

/-!
# Schauder bases and reflexivity

A Schauder basis is shrinking if its coordinate functionals span a norm-dense
subspace of the continuous dual. It is boundedly complete if every scalar sequence
with bounded initial partial sums gives a convergent basis expansion.

James's basis criterion characterizes reflexivity by these two properties.
All series here use initial segments, rather than unconditional summation.

## References

* R. E. Megginson, *An Introduction to Banach Space Theory*, §4.4, Theorem 4.4.15.
-/

/-
The forward direction uses weak compactness of bounded sets; the reverse direction
reconstructs a vector from the coordinates assigned by a bidual functional.
The proof reuses Mathlib's basis projections and their uniform norm bound, together
with the weak compactness characterization of reflexivity.
-/

public section

noncomputable section

open Filter Function NormedSpace Set Topology

namespace SchauderBasis

section General

variable {𝕜 E : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] (b : SchauderBasis 𝕜 E)

/-- A basis is shrinking when its coordinate functionals span a norm-dense subspace
of the continuous dual. -/
def IsShrinking : Prop :=
  Dense (Submodule.span 𝕜 (range b.coord) : Set (StrongDual 𝕜 E))

/-- A basis is shrinking precisely when the norm closure of the span of its
coordinate functionals is the whole continuous dual. -/
theorem isShrinking_iff : b.IsShrinking ↔
    (Submodule.span 𝕜 (range b.coord)).topologicalClosure = ⊤ :=
  Submodule.dense_iff_topologicalClosure_eq_top

/-- A basis is boundedly complete when bounded initial partial sums of any scalar
sequence converge in norm. The summation filter is the conditional one. -/
def IsBoundedlyComplete : Prop :=
  ∀ a : ℕ → 𝕜,
    BddAbove (range (fun n ↦ ‖∑ i ∈ Finset.range n, a i • b i‖)) →
    ∃ x, HasSum (fun i ↦ a i • b i) x (SummationFilter.conditional ℕ)

/-- A coordinate of a finite initial sum is its prescribed coefficient once that
coordinate has been included. -/
-- Normalize before the generic map-of-sum simp lemma expands the coordinate application.
@[simp 1100]
theorem coord_sum_range (a : ℕ → 𝕜) {i n : ℕ} (hi : i < n) :
    b.coord i (∑ j ∈ Finset.range n, a j • b j) = a i := by
  classical
  simp [map_sum, b.ortho, Pi.single_apply, hi]

/-- Precomposition with an initial projection is a finite linear combination of coordinates. -/
theorem comp_proj_eq_sum (f : StrongDual 𝕜 E) (n : ℕ) :
    f.comp (b.proj n) = ∑ i ∈ Finset.range n, f (b i) • b.coord i := by
  ext x
  simp [proj_apply, mul_comm]

/-- Coordinates of a convergent basis series are its coefficients. -/
theorem coord_eq_of_hasSum {a : ℕ → 𝕜} {x : E}
    (h : HasSum (fun i ↦ a i • b i) x (SummationFilter.conditional ℕ)) (i : ℕ) :
    b.coord i x = a i := by
  have ht : Tendsto (fun n ↦ ∑ j ∈ Finset.range n, a j • b j) atTop (𝓝 x) := by
    simpa only [HasSum, SummationFilter.conditional_filter_eq_map_range,
      tendsto_map'_iff, Function.comp_def] using h
  exact tendsto_nhds_unique ((b.coord i).continuous.tendsto x |>.comp ht)
    (tendsto_const_nhds.congr' (eventually_atTop.2 ⟨i + 1,
      fun n hn ↦ (b.coord_sum_range a (by omega)).symm⟩))

/-- Bounded completeness says precisely that every coefficient sequence with bounded
initial partial sums is the coordinate sequence of a vector. -/
theorem isBoundedlyComplete_iff : b.IsBoundedlyComplete ↔
    ∀ a : ℕ → 𝕜,
      BddAbove (range (fun n ↦ ‖∑ i ∈ Finset.range n, a i • b i‖)) →
      ∃ x, ∀ i, b.coord i x = a i := by
  constructor
  · intro h a ha
    obtain ⟨x, hx⟩ := h a ha
    exact ⟨x, fun i ↦ b.coord_eq_of_hasSum hx i⟩
  · intro h a ha
    obtain ⟨x, hx⟩ := h a ha
    exact ⟨x, by simpa only [hx] using b.expansion x⟩

/-- A shrinking basis determines continuous bidual functionals by their values on
the coordinate functionals. -/
theorem IsShrinking.ext {b : SchauderBasis 𝕜 E} (hb : b.IsShrinking)
    {Φ Ψ : StrongDual 𝕜 (StrongDual 𝕜 E)} (h : ∀ i, Φ (b.coord i) = Ψ (b.coord i)) :
    Φ = Ψ :=
  ContinuousLinearMap.ext_on hb (by rintro _ ⟨i, rfl⟩; exact h i)

end General

section RCLike

variable {𝕜 E : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] (b : SchauderBasis 𝕜 E)

/-- Every Schauder basis of a reflexive space is shrinking. Completeness follows
from reflexivity and need not be assumed separately. -/
theorem isShrinking_of_surjective_inclusionInDoubleDual
    (hE : Surjective (inclusionInDoubleDual 𝕜 E)) : b.IsShrinking := by
  -- Fix the normed structure on the dual before synthesizing the quotient's instances.
  let : NormedAddCommGroup (StrongDual 𝕜 E) := inferInstance
  let S := (Submodule.span 𝕜 (range b.coord)).topologicalClosure
  let : IsClosed (S : Set (StrongDual 𝕜 E)) := Submodule.isClosed_topologicalClosure _
  rw [b.isShrinking_iff]
  apply top_unique
  intro f _
  apply (Submodule.Quotient.mk_eq_zero S).1
  apply (SeparatingDual.eq_zero_iff_forall_dual_eq_zero (R := 𝕜) _).2
  intro Ψ
  obtain ⟨x, hx⟩ := hE (Ψ.comp S.mkQL)
  have hcoord (i : ℕ) : b.coord i x = 0 := by
    have hi : b.coord i ∈ S :=
      Submodule.le_topologicalClosure _ (Submodule.subset_span (mem_range_self i))
    have := DFunLike.congr_fun hx (b.coord i)
    simpa [dual_def, (Submodule.Quotient.mk_eq_zero S).2 hi] using this
  have hxzero : x = 0 := by
    have ht := b.tendsto_proj x
    simp only [SchauderBasis.proj_apply, hcoord, zero_smul, Finset.sum_const_zero] at ht
    exact tendsto_nhds_unique ht tendsto_const_nhds
  have := DFunLike.congr_fun hx f
  simpa [hxzero, dual_def] using this.symm

/-- Every Schauder basis of a reflexive space is boundedly complete. -/
theorem isBoundedlyComplete_of_surjective_inclusionInDoubleDual
    (hE : Surjective (inclusionInDoubleDual 𝕜 E)) : b.IsBoundedlyComplete := by
  -- A weak cluster point of the bounded partial sums has the prescribed coordinates.
  rw [b.isBoundedlyComplete_iff]
  intro a ⟨C, hC⟩
  let s (n : ℕ) := ∑ i ∈ Finset.range n, a i • b i
  have hbound (n : ℕ) : ‖s n‖ ≤ C := hC (mem_range_self n)
  obtain ⟨w, _, hw⟩ := (TauCeti.isCompact_toWeakSpace_closedBall hE 0 C).exists_mapClusterPt
    (u := fun n ↦ toWeakSpace 𝕜 E (s n)) (f := atTop)
    (by
      rw [Filter.map_le_iff_le_comap, Filter.comap_principal, Filter.le_principal_iff]
      exact Eventually.of_forall fun n ↦ ⟨s n,
        by simpa only [Metric.mem_closedBall, dist_zero_right] using hbound n, rfl⟩)
  refine ⟨(toWeakSpace 𝕜 E).symm w, fun i ↦ ?_⟩
  have heval := WeakBilin.eval_continuous (topDualPairing 𝕜 E).flip (b.coord i)
  have hc := hw.continuousAt_comp heval.continuousAt
  have ht : Tendsto (fun n ↦ b.coord i (s n)) atTop (𝓝 (a i)) :=
    tendsto_const_nhds.congr' (eventually_atTop.2 ⟨i + 1,
      fun n hn ↦ (b.coord_sum_range a (by omega)).symm⟩)
  exact eq_of_nhds_neBot (hc.clusterPt.mono ht)

variable [CompleteSpace E]

/-- A shrinking and boundedly complete Schauder basis makes its space reflexive. -/
theorem surjective_inclusionInDoubleDual_of_isShrinking_of_isBoundedlyComplete
    (hs : b.IsShrinking) (hc : b.IsBoundedlyComplete) :
    Surjective (inclusionInDoubleDual 𝕜 E) := by
  intro Φ
  have hbound : BddAbove (range (fun n ↦
      ‖∑ i ∈ Finset.range n, Φ (b.coord i) • b i‖)) := by
    refine ⟨‖Φ‖ * b.nnnormProjBound, ?_⟩
    rintro _ ⟨n, rfl⟩
    apply norm_le_dual_bound 𝕜 _ (by positivity)
    intro f
    have heq : f (∑ i ∈ Finset.range n, Φ (b.coord i) • b i) =
        Φ (f.comp (SchauderBasis.proj b n)) := by
      simp [b.comp_proj_eq_sum, mul_comm]
    rw [heq]
    calc
      ‖Φ (f.comp (SchauderBasis.proj b n))‖ ≤ ‖Φ‖ * ‖f.comp (SchauderBasis.proj b n)‖ :=
        Φ.le_opNorm _
      _ ≤ ‖Φ‖ * (‖f‖ * b.nnnormProjBound) :=
        mul_le_mul_of_nonneg_left
          ((ContinuousLinearMap.opNorm_comp_le _ _).trans
            (mul_le_mul_of_nonneg_left (b.norm_proj_le_nnnormProjBound n) (norm_nonneg f)))
          (norm_nonneg Φ)
      _ = (‖Φ‖ * b.nnnormProjBound) * ‖f‖ := by ring
  obtain ⟨x, hx⟩ := b.isBoundedlyComplete_iff.1 hc _ hbound
  exact ⟨x, hs.ext fun i ↦ by simpa only [dual_def] using hx i⟩

/-- **James's basis criterion.** A Banach space with a Schauder basis is reflexive
if and only if that basis is shrinking and boundedly complete. -/
theorem surjective_inclusionInDoubleDual_iff :
    Surjective (inclusionInDoubleDual 𝕜 E) ↔ b.IsShrinking ∧ b.IsBoundedlyComplete :=
  ⟨fun hE ↦ ⟨b.isShrinking_of_surjective_inclusionInDoubleDual hE,
      b.isBoundedlyComplete_of_surjective_inclusionInDoubleDual hE⟩,
    fun ⟨hs, hc⟩ ↦ b.surjective_inclusionInDoubleDual_of_isShrinking_of_isBoundedlyComplete hs hc⟩

end RCLike

end SchauderBasis
