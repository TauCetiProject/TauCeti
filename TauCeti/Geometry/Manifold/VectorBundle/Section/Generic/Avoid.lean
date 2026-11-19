/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Complex.Analytic
public import TauCeti.Geometry.Manifold.VectorBundle.Section.Generic

/-!
# Generic sections that do not vanish on a given countable set

Let `s₀ + ∑ i, a i • s i` be the affine finite-parameter perturbation of a smooth section of a
real vector bundle by a family `s` spanning every fiber (`ContMDiffSection.affineFamily`). For a
point `x`, the parameters whose section does not vanish at `x` form an open set, and a dense one
when one perturbing section is nonzero there: its complement is a proper affine subspace of the
parameter space. Intersecting countably many of these open dense sets
with the residual set of regular parameters with finitely many zeros
(`ContMDiffSection.mem_residual_setOf_regular_and_finite_zero_affineFamily`) shows that a generic
smooth section with regular, finitely many zeros is nonzero on a given countable set.

For a compact complex manifold, through its underlying real smooth manifold
(`IsManifold.restrictScalars_of_ne_zero`), this gives continuous sections of a real smooth bundle
of matching rank with finitely many zeros, none of them in a given countable set. For a line bundle
with model fiber `ℂ` over a compact Riemann surface, this is a continuous section with finitely
many zeros that does not vanish at a given point, the input of the Euler number of a point twist
in the proof of the Riemann–Roch formula for real Cauchy–Riemann operators
(McDuff–Salamon, Theorem C.1.10). Applied to the zero set of a section of
another bundle, the finite-set form gives two sections with disjoint zero sets.

For the generic-section existence theorems the model fiber must be nontrivial: on a bundle of
rank zero over a nonempty base every section vanishes everywhere. The density and residual
avoidance lemmas instead ask directly for a nonzero perturbation direction at each avoided point.

## Main results

* `ContMDiffSection.isOpen_setOf_affineFamily_apply_ne_zero` and
  `ContMDiffSection.dense_setOf_affineFamily_apply_ne_zero`: the parameters whose section does not
  vanish at a point form an open dense set.
* `ContMDiffSection.mem_residual_setOf_forall_mem_affineFamily_ne_zero`: the parameters whose
  section does not vanish on a countable set form a residual set.
* `TauCeti.exists_contMDiffSection_regular_finite_zero_forall_mem_ne_zero`: a compact smooth bundle
  of equal base and fiber dimensions has a smooth section with regular, finitely many zeros, none
  of them in a given countable set.
* `TauCeti.exists_continuous_section_finite_zero_forall_mem_ne_zero` and
  `TauCeti.exists_continuous_section_finite_zero_ne`: the continuous forms over compact complex
  manifolds and compact Riemann surfaces.

## References

* M. W. Hirsch, *Differential Topology*, Chapter 3.
* D. McDuff, D. Salamon, *J-holomorphic Curves and Symplectic Topology*, 2nd ed., Appendix A.3 and
  Theorem C.1.10.
-/

public section

open Bundle Filter Function Module Set
open scoped Manifold ContDiff Topology

namespace ContMDiffSection

variable {X H M F : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [TopologicalSpace H] {I : ModelWithCorners ℝ X H}
  [TopologicalSpace M] [ChartedSpace H M]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  {V : M → Type*} [TopologicalSpace (TotalSpace F V)]
  [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)] [∀ x, TopologicalSpace (V x)]
  [FiberBundle F V] [VectorBundle ℝ F V]
  {ι : Type*} [Fintype ι]

/-- The parameters whose perturbed section does not vanish at a given point form an open set. -/
theorem isOpen_setOf_affineFamily_apply_ne_zero (s₀ : ContMDiffSection I F ∞ V)
    (s : ι → ContMDiffSection I F ∞ V) (x : M) :
    IsOpen {a | affineFamily s₀ s a x ≠ 0} := by
  let e := (trivializationAt F V x).continuousLinearEquivAt ℝ x
    (mem_baseSet_trivializationAt F V x)
  have hc : Continuous fun a ↦ e (affineFamily s₀ s a x) := by
    simp only [affineFamily_apply, map_add, map_sum, map_smul]
    exact continuous_const.add (continuous_finsetSum _ fun i _ ↦
      (continuous_apply i).smul continuous_const)
  have hset : {a | affineFamily s₀ s a x ≠ 0} = (fun a ↦ e (affineFamily s₀ s a x)) ⁻¹' {0}ᶜ := by
    ext a
    exact (map_ne_zero_iff e e.injective).symm
  rw [hset]
  exact hc.isOpen_preimage _ isOpen_compl_singleton

/-- If one perturbing section is nonzero at `x`, the parameters whose perturbed section does not
vanish at `x` are dense: the others form a proper affine subspace. -/
theorem dense_setOf_affineFamily_apply_ne_zero (s₀ : ContMDiffSection I F ∞ V)
    (s : ι → ContMDiffSection I F ∞ V) {x : M} (hdir : ∃ i, s i x ≠ 0) :
    Dense {a | affineFamily s₀ s a x ≠ 0} := by
  classical
  obtain ⟨i, hi⟩ := hdir
  let b : ι → ℝ := Pi.single i 1
  have hb : ∑ j, b j • s j x = s i x := by simp [b]
  intro a
  by_cases ha : affineFamily s₀ s a x = 0
  · refine mem_closure_of_tendsto (f := fun t : ℝ ↦ a + t • b) (b := 𝓝[≠] 0) ?_ ?_
    · exact ((continuous_const.add (continuous_id.smul continuous_const)).tendsto' 0 a
        (by simp)).mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with t ht
      have h : affineFamily s₀ s (a + t • b) x = t • s i x := by
        rw [← zero_add (t • s i x), ← ha, ← hb]
        simp only [affineFamily_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul, add_smul,
          mul_smul, Finset.sum_add_distrib, Finset.smul_sum, add_assoc]
      rw [h]
      exact smul_ne_zero ht hi
  · exact subset_closure ha

/-- If at least one perturbing section is nonzero at every point of a countable set, the parameters
whose perturbed section does not vanish on that set form a residual set. -/
theorem mem_residual_setOf_forall_mem_affineFamily_ne_zero
    (s₀ : ContMDiffSection I F ∞ V) (s : ι → ContMDiffSection I F ∞ V) {S : Set M}
    (hS : S.Countable) (hdir : ∀ x ∈ S, ∃ i, s i x ≠ 0) :
    {a | ∀ x ∈ S, affineFamily s₀ s a x ≠ 0} ∈ residual (ι → ℝ) := by
  refine mem_of_superset ((countable_bInter_mem hS).2 fun x hx ↦ residual_of_dense_open
    (isOpen_setOf_affineFamily_apply_ne_zero s₀ s x)
    (dense_setOf_affineFamily_apply_ne_zero s₀ s (hdir x hx))) fun a ha ↦ ?_
  simpa using ha

end ContMDiffSection

namespace TauCeti

open ContMDiffSection

section Real

variable {X M F : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [FiniteDimensional ℝ X] [TopologicalSpace M] [ChartedSpace X M]
  [T2Space M] [CompactSpace M] [IsManifold 𝓘(ℝ, X) ∞ M]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F] [Nontrivial F]
  {V : M → Type*} [TopologicalSpace (TotalSpace F V)]
  [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)] [∀ x, TopologicalSpace (V x)]
  [FiberBundle F V] [VectorBundle ℝ F V] [ContMDiffVectorBundle ∞ F V 𝓘(ℝ, X)]

/-- A compact smooth bundle of equal base and fiber dimensions and nontrivial model fiber has a
smooth section with surjective intrinsic linearization at every zero and finitely many zeros, none
of them in a given countable set. -/
theorem exists_contMDiffSection_regular_finite_zero_forall_mem_ne_zero
    (hdim : finrank ℝ X = finrank ℝ F) {S : Set M} (hS : S.Countable) :
    ∃ s : ContMDiffSection 𝓘(ℝ, X) F ∞ V,
      (∀ x, s x = 0 → Surjective (TauCeti.sectionLinearization (F := F) 𝓘(ℝ, X) id s x)) ∧
        {x | s x = 0}.Finite ∧ ∀ x ∈ S, s x ≠ 0 := by
  let : SecondCountableTopology M := ChartedSpace.secondCountable_of_sigmaCompact X M
  obtain ⟨n, s, hspan⟩ := exists_fin_spanning_contMDiffSection (I := 𝓘(ℝ, X)) (F := F) (V := V)
  have hdir (x : M) : ∃ i, s i x ≠ 0 := by
    classical
    have : Nontrivial (V x) :=
      ((trivializationAt F V x).continuousLinearEquivAt ℝ x
        (mem_baseSet_trivializationAt F V x)).toEquiv.nontrivial
    by_contra! hall
    have hz : Submodule.span ℝ (range fun i ↦ s i x) = ⊥ :=
      Submodule.span_eq_bot.mpr (by rintro y ⟨i, rfl⟩; exact hall i)
    exact top_ne_bot ((hspan x).symm.trans hz)
  obtain ⟨a, ha, hS⟩ := (dense_of_mem_residual
    (inter_mem
      (mem_residual_setOf_regular_and_finite_zero_affineFamily 0 s hspan hdim)
      (mem_residual_setOf_forall_mem_affineFamily_ne_zero 0 s hS fun x _ ↦ hdir x))).nonempty
  exact ⟨affineFamily 0 s a, TauCeti.isRegularSectionParameter_iff.mp ha.1, ha.2, hS⟩

end Real

section Complex

variable {E X F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
  [TopologicalSpace X] [ChartedSpace E X] [T2Space X] [CompactSpace X] [IsManifold 𝓘(ℂ, E) 1 X]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F] [Nontrivial F]
  {L : X → Type*} [∀ z, AddCommGroup (L z)] [∀ z, Module ℝ (L z)] [∀ z, TopologicalSpace (L z)]
  [TopologicalSpace (TotalSpace F L)] [FiberBundle F L] [VectorBundle ℝ F L]
  [ContMDiffVectorBundle ∞ F L 𝓘(ℝ, E)]

/-- A real smooth vector bundle over a compact complex manifold, of real rank the real dimension
of the base and nontrivial model fiber, has a continuous section with finitely many zeros, none of
them in a given countable set. -/
theorem exists_continuous_section_finite_zero_forall_mem_ne_zero
    (hdim : finrank ℝ E = finrank ℝ F) {S : Set X} (hS : S.Countable) :
    ∃ s : ∀ z, L z, (Continuous fun z ↦ TotalSpace.mk' F z (s z)) ∧ {z | s z = 0}.Finite ∧
      ∀ y ∈ S, s y ≠ 0 := by
  have : IsManifold 𝓘(ℝ, E) ∞ X := IsManifold.restrictScalars_of_ne_zero ∞ one_ne_zero ‹_›
  have : FiniteDimensional ℝ E := .complexToReal E
  obtain ⟨s, -, hZ, hS⟩ :=
    exists_contMDiffSection_regular_finite_zero_forall_mem_ne_zero (F := F) (V := L) hdim hS
  exact ⟨s, s.contMDiff.continuous, hZ, hS⟩

end Complex

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X] [T2Space X] [CompactSpace X]
  [IsManifold 𝓘(ℂ, ℂ) 1 X]
  {L : X → Type*} [∀ z, AddCommGroup (L z)] [∀ z, Module ℝ (L z)] [∀ z, TopologicalSpace (L z)]
  [TopologicalSpace (TotalSpace ℂ L)] [FiberBundle ℂ L] [VectorBundle ℝ ℂ L]
  [ContMDiffVectorBundle ∞ ℂ L 𝓘(ℝ, ℂ)]

/-- A smooth complex line bundle with model fiber `ℂ` over a compact Riemann surface has a
continuous section with finitely many zeros that does not vanish at a given point. -/
theorem exists_continuous_section_finite_zero_ne (x : X) :
    ∃ s : ∀ z, L z, (Continuous fun z ↦ TotalSpace.mk' ℂ z (s z)) ∧ {z | s z = 0}.Finite ∧
      s x ≠ 0 := by
  obtain ⟨s, hs, hZ, hx⟩ :=
    exists_continuous_section_finite_zero_forall_mem_ne_zero (E := ℂ) (F := ℂ) (L := L) rfl
      (countable_singleton x)
  exact ⟨s, hs, hZ, hx x rfl⟩

end TauCeti
