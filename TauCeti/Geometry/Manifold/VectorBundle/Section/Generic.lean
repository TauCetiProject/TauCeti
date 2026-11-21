/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.VectorBundle.Section.FiniteSpan
public import TauCeti.Geometry.Manifold.VectorBundle.Section.Parametric
public import TauCeti.Geometry.Manifold.VectorBundle.Translate
public import TauCeti.Geometry.Manifold.VectorBundle.Scalar
public import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import TauCeti.Topology.VectorBundle.Trivialization

/-!
# Generic sections from finite smooth spanning families

A finite family spanning every fiber gives an actual finite-dimensional affine perturbation
of any smooth section (forcing the model fiber to be finite-dimensional whenever the base is
nonempty). Its parameter derivative is evaluation of the spanning family, so its universal
linearization is surjective. On a finite-dimensional base manifold, native parametric
transversality then supplies regular parameters without a topology on the space of all smooth
sections.

For each point where some perturbing section is nonzero, the parameters giving a nonzero value
form an open dense set. Countable intersections give sections avoiding any prescribed countable
set, while retaining regular, finitely many zeros when the base and fiber dimensions agree.
On a complex base, the smooth real theorem applies to the underlying real smooth structure via
`IsManifold.restrictScalars_of_ne_zero`, retaining both smoothness and regularity of the zeros.
The examples check this on compact complex manifolds and native complex line subbundles.

The density and residual avoidance lemmas require only a nonzero perturbation direction at each
avoided point. The countable-avoidance existence result requires a nontrivial model fiber, since
every section of a rank-zero bundle vanishes everywhere.

## References

* M. W. Hirsch, *Differential Topology*, Chapter 3.
* D. McDuff, D. Salamon, *J-holomorphic Curves and Symplectic Topology*, 2nd ed., Appendix A.3.
-/

public section

open Bundle Filter Function Module Set
open scoped Manifold ContDiff Topology

namespace ContMDiffSection

section AffineFamily

variable {X H M F : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [TopologicalSpace H] {I : ModelWithCorners ℝ X H}
  [TopologicalSpace M] [ChartedSpace H M]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  {V : M → Type*} [TopologicalSpace (TotalSpace F V)]
  [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)] [∀ x, TopologicalSpace (V x)]
  [FiberBundle F V] [VectorBundle ℝ F V]
  {ι : Type*} [Fintype ι]

/-- The affine finite-parameter perturbation of a smooth section by a finite smooth family. -/
noncomputable def affineFamily (s₀ : ContMDiffSection I F ∞ V)
    (s : ι → ContMDiffSection I F ∞ V) (a : ι → ℝ) : ContMDiffSection I F ∞ V :=
  s₀ + ∑ i, a i • s i

/-- The perturbation is the actual pointwise affine linear combination. -/
@[simp]
theorem affineFamily_apply (s₀ : ContMDiffSection I F ∞ V)
    (s : ι → ContMDiffSection I F ∞ V) (a : ι → ℝ) (x : M) :
    affineFamily s₀ s a x = s₀ x + ∑ i, a i • s i x := by
  rw [affineFamily, coe_add, Pi.add_apply]
  congr 1
  simpa only [coeAddHom_apply, Finset.sum_apply, coe_smul, Pi.smul_apply] using
    congrFun (map_sum (coeAddHom I F ∞ V) (fun i ↦ a i • s i) Finset.univ) x

/-- Zero parameter recovers the prescribed section. -/
@[simp]
theorem affineFamily_zero (s₀ : ContMDiffSection I F ∞ V)
    (s : ι → ContMDiffSection I F ∞ V) : affineFamily s₀ s 0 = s₀ := by
  ext x
  simp

/-- The universal perturbation is smooth jointly in its base point and finite parameters. -/
theorem contMDiff_affineFamily (s₀ : ContMDiffSection I F ∞ V)
    (s : ι → ContMDiffSection I F ∞ V) :
    ContMDiff (I.prod 𝓘(ℝ, ι → ℝ)) (I.prod 𝓘(ℝ, F)) ∞
      (fun z : M × (ι → ℝ) ↦ (⟨z.1, affineFamily s₀ s z.2 z.1⟩ : TotalSpace F V)) := by
  classical
  have hs (t : Finset ι) :
      ContMDiff (I.prod 𝓘(ℝ, ι → ℝ)) (I.prod 𝓘(ℝ, F)) ∞
        (fun z : M × (ι → ℝ) ↦ (⟨z.1, ∑ i ∈ t, z.2 i • s i z.1⟩ : TotalSpace F V)) := by
    induction t using Finset.induction_on with
    | empty =>
      simpa only [Finset.sum_empty, Function.comp_def, zeroSection] using
        (contMDiff_zeroSection ℝ V).comp contMDiff_fst
    | @insert i t hi ih =>
      have ha : ContMDiff (I.prod 𝓘(ℝ, ι → ℝ)) 𝓘(ℝ, ℝ) ∞
          (fun z : M × (ι → ℝ) ↦ z.2 i) :=
        (ContinuousLinearMap.proj i : (ι → ℝ) →L[ℝ] ℝ).contDiff.contMDiff.comp contMDiff_snd
      have hb := ha.smul_totalSpace ((s i).contMDiff.comp contMDiff_fst)
      simpa only [Finset.sum_insert hi, Function.comp_def] using hb.add_sectionAlong ih
  simpa only [affineFamily_apply, Function.comp_def] using
    (s₀.contMDiff.comp contMDiff_fst).add_sectionAlong (hs Finset.univ)

/-- A fiberwise spanning family makes the total intrinsic linearization of the actual affine
perturbation surjective. The conclusion even holds away from the zero section. -/
theorem surjective_sectionLinearization_affineFamily
    (s₀ : ContMDiffSection I F ∞ V) (s : ι → ContMDiffSection I F ∞ V)
    (hspan : ∀ x, Submodule.span ℝ (range fun i ↦ s i x) = ⊤)
    (z : M × (ι → ℝ)) :
    Surjective (TauCeti.sectionLinearization (F := F) (I.prod 𝓘(ℝ, ι → ℝ)) Prod.fst
      (fun w ↦ affineFamily s₀ s w.2 w.1) z) := by
  classical
  let e := trivializationAt F V z.1
  have he : z.1 ∈ e.baseSet := mem_baseSet_trivializationAt F V z.1
  let c : M × (ι → ℝ) → F := fun w ↦ (e ⟨w.1, affineFamily s₀ s w.2 w.1⟩).2
  let L : (ι → ℝ) →L[ℝ] F :=
    LinearMap.toContinuousLinearMap
      (Fintype.linearCombination ℝ (fun i ↦ e.continuousLinearMapAt ℝ z.1 (s i z.1)))
  have hL : Surjective L := by
    intro v
    obtain ⟨a, ha⟩ := (span_range_eq_top_iff_surjective_fintypeLinearCombination ℝ
      (fun i ↦ s i z.1)).mp (hspan z.1) (e.symmL ℝ z.1 v)
    refine ⟨a, ?_⟩
    have h := congrArg (e.continuousLinearMapAt ℝ z.1) ha
    simpa only [L, LinearMap.coe_toContinuousLinearMap', Fintype.linearCombination_apply,
      map_sum, map_smul, e.continuousLinearMapAt_symmL he] using h
  have hparam : (fun a ↦ c (z.1, a)) =
      fun a ↦ e.continuousLinearMapAt ℝ z.1 (s₀ z.1) + L a := by
    funext a
    simp only [c, ← Trivialization.continuousLinearMapAt_apply_of_mem ℝ e he, affineFamily_apply,
      map_add, map_sum, map_smul, L, LinearMap.coe_toContinuousLinearMap',
      Fintype.linearCombination_apply]
  have hp : HasFDerivAt (fun a ↦ c (z.1, a)) L z.2 := by
    rw [hparam]
    simpa only [zero_add, Pi.add_def] using (hasFDerivAt_const
      (e.continuousLinearMapAt ℝ z.1 (s₀ z.1)) z.2).add L.hasFDerivAt
  have hc : MDifferentiableAt (I.prod 𝓘(ℝ, ι → ℝ)) 𝓘(ℝ, F) c z :=
    ((contMDiffAt_totalSpace_iff.mp (contMDiff_affineFamily s₀ s z)).2).mdifferentiableAt
      (by simp)
  have hg : MDifferentiableAt 𝓘(ℝ, ι → ℝ) (I.prod 𝓘(ℝ, ι → ℝ))
      (fun a ↦ (z.1, a)) z.2 := mdifferentiableAt_const.prodMk mdifferentiableAt_id
  have hcomp : Surjective (mvfderiv (I.prod 𝓘(ℝ, ι → ℝ)) c z) := by
    have hsurj : Surjective ((mvfderiv (I.prod 𝓘(ℝ, ι → ℝ)) c z).comp
        (mfderiv 𝓘(ℝ, ι → ℝ) (I.prod 𝓘(ℝ, ι → ℝ)) (fun a ↦ (z.1, a)) z.2)) := by
      rw [← mvfderiv_comp z.2 hc hg]
      simpa only [Function.comp_def, mvfderiv_eq_fderiv, hp.fderiv,
        ContinuousLinearMap.coe_comp, ContinuousLinearEquiv.coe_coe] using
        hL.comp (NormedSpace.fromTangentSpace z.2).surjective
    exact Function.Surjective.of_comp
      (f := mvfderiv (I.prod 𝓘(ℝ, ι → ℝ)) c z)
      (g := mfderiv 𝓘(ℝ, ι → ℝ) (I.prod 𝓘(ℝ, ι → ℝ)) (fun a ↦ (z.1, a)) z.2) hsurj
  rw [TauCeti.sectionLinearization_def, ← e.symm_continuousLinearEquivAt_eq' he]
  exact (e.continuousLinearEquivAt ℝ z.1 he).symm.surjective.comp hcomp

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


end AffineFamily

section RegularParameters

variable {X M F : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [TopologicalSpace M] [ChartedSpace X M]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  {V : M → Type*} [TopologicalSpace (TotalSpace F V)]
  [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)] [∀ x, TopologicalSpace (V x)]
  [FiberBundle F V] [VectorBundle ℝ F V]
  {ι : Type*}

private theorem finiteDimensional_of_span [Finite ι] [Nonempty M]
    (s : ι → ContMDiffSection 𝓘(ℝ, X) F ∞ V)
    (hspan : ∀ x, Submodule.span ℝ (range fun i ↦ s i x) = ⊤) :
    FiniteDimensional ℝ F := by
  let := Fintype.ofFinite ι
  obtain ⟨x₀⟩ := ‹Nonempty M›
  have hx₀ := mem_baseSet_trivializationAt F V x₀
  exact .of_surjective
    (((trivializationAt F V x₀).linearEquivAt ℝ x₀ hx₀).toLinearMap.comp
      (Fintype.linearCombination ℝ fun i ↦ s i x₀))
    (((trivializationAt F V x₀).linearEquivAt ℝ x₀ hx₀).surjective.comp
      ((span_range_eq_top_iff_surjective_fintypeLinearCombination ℝ _).mp (hspan x₀)))

variable [Fintype ι] [FiniteDimensional ℝ X] [SecondCountableTopology M] [IsManifold 𝓘(ℝ, X) ∞ M]

/-- Over a finite-dimensional base manifold, regular parameters of the actual affine perturbation
by a finite fiberwise spanning family form a residual set. -/
theorem mem_residual_setOf_isRegular_affineFamily
    (s₀ : ContMDiffSection 𝓘(ℝ, X) F ∞ V)
    (s : ι → ContMDiffSection 𝓘(ℝ, X) F ∞ V)
    (hspan : ∀ x, Submodule.span ℝ (range fun i ↦ s i x) = ⊤) :
    {a | TauCeti.IsRegularSectionParameter (F := F) X Prod.fst
      (fun z ↦ affineFamily s₀ s z.2 z.1) a} ∈ residual (ι → ℝ) := by
  rcases isEmpty_or_nonempty M with _ | _
  · exact Filter.univ_mem' fun _ ↦ TauCeti.isRegularSectionParameter_iff.2 fun x ↦ isEmptyElim x
  have := finiteDimensional_of_span s hspan
  let : IsManifold 𝓘(ℝ, X) 1 M := IsManifold.of_le (n := ∞) (by norm_num)
  apply TauCeti.mem_residual_setOf_isRegularSectionParameter
    (n := ∞) (I := 𝓘(ℝ, X))
  · exact fun z _ ↦ contMDiff_affineFamily s₀ s z
  · intro z hz
    have hc := (contMDiffAt_totalSpace_iff.mp ((affineFamily s₀ s z.2).contMDiff z.1)).2
    exact (TauCeti.isFredholm_sectionLinearization_iff continuousAt_id
      (mem_baseSet_trivializationAt F V z.1) (hc.mdifferentiableAt (by simp)) hz).mpr
        (ContinuousLinearMap.isFredholm_of_finiteDimensional _)
  · exact fun z _ ↦ surjective_sectionLinearization_affineFamily s₀ s hspan z
  · exact fun _ _ ↦ WithTop.coe_le_coe.mpr le_top

/-- Over a finite-dimensional base manifold, regular parameters of an actual finite spanning
perturbation are dense. -/
theorem dense_setOf_isRegular_affineFamily
    (s₀ : ContMDiffSection 𝓘(ℝ, X) F ∞ V)
    (s : ι → ContMDiffSection 𝓘(ℝ, X) F ∞ V)
    (hspan : ∀ x, Submodule.span ℝ (range fun i ↦ s i x) = ⊤) :
    Dense {a | TauCeti.IsRegularSectionParameter (F := F) X Prod.fst
      (fun z ↦ affineFamily s₀ s z.2 z.1) a} :=
  dense_of_mem_residual (mem_residual_setOf_isRegular_affineFamily s₀ s hspan)

/-- When `F` has finite dimension exceeding the finite dimension of the base `X`, zero-free
parameters of the actual affine perturbation form a residual set: the slice index is the negative
difference of the two dimensions. -/
theorem mem_residual_setOf_affineFamily_ne_zero
    (s₀ : ContMDiffSection 𝓘(ℝ, X) F ∞ V)
    (s : ι → ContMDiffSection 𝓘(ℝ, X) F ∞ V)
    (hspan : ∀ x, Submodule.span ℝ (range fun i ↦ s i x) = ⊤)
    (hdim : finrank ℝ X < finrank ℝ F) :
    {a | ∀ x, affineFamily s₀ s a x ≠ 0} ∈ residual (ι → ℝ) := by
  have : FiniteDimensional ℝ F := Module.finite_of_finrank_pos (pos_of_gt hdim)
  let : IsManifold 𝓘(ℝ, X) 1 M := IsManifold.of_le (n := ∞) (by norm_num)
  filter_upwards [mem_residual_setOf_isRegular_affineFamily s₀ s hspan] with a ha
  apply (TauCeti.isRegularSectionParameter_iff_forall_ne_zero_of_index_neg ?_).mp ha
  intro x _
  rw [TauCeti.index_sectionLinearization_of_finiteDimensional]
  exact sub_neg.mpr (by exact_mod_cast hdim)

/-- Zero-free parameters are dense when the finite fiber dimension exceeds the finite base
dimension. -/
theorem dense_setOf_affineFamily_ne_zero
    (s₀ : ContMDiffSection 𝓘(ℝ, X) F ∞ V)
    (s : ι → ContMDiffSection 𝓘(ℝ, X) F ∞ V)
    (hspan : ∀ x, Submodule.span ℝ (range fun i ↦ s i x) = ⊤)
    (hdim : finrank ℝ X < finrank ℝ F) :
    Dense {a | ∀ x, affineFamily s₀ s a x ≠ 0} :=
  dense_of_mem_residual (mem_residual_setOf_affineFamily_ne_zero s₀ s hspan hdim)

/-- At equal base and fiber `finrank` (hence equal finite dimensions whenever `M` is nonempty, as
`hspan` forces `F` to be finite-dimensional), regular parameters have an actual discrete zero
manifold, hence finitely many zeros on a compact source. -/
theorem mem_residual_setOf_regular_and_finite_zero_affineFamily
    [CompactSpace M] [ContMDiffVectorBundle ∞ F V 𝓘(ℝ, X)]
    (s₀ : ContMDiffSection 𝓘(ℝ, X) F ∞ V)
    (s : ι → ContMDiffSection 𝓘(ℝ, X) F ∞ V)
    (hspan : ∀ x, Submodule.span ℝ (range fun i ↦ s i x) = ⊤)
    (hdim : finrank ℝ X = finrank ℝ F) :
    {a | TauCeti.IsRegularSectionParameter (F := F) X Prod.fst
      (fun z ↦ affineFamily s₀ s z.2 z.1) a ∧ {x | affineFamily s₀ s a x = 0}.Finite}
      ∈ residual (ι → ℝ) := by
  rcases isEmpty_or_nonempty M with _ | _
  · exact Filter.univ_mem' fun _ ↦
      ⟨TauCeti.isRegularSectionParameter_iff.2 fun x ↦ isEmptyElim x, toFinite _⟩
  have := finiteDimensional_of_span s hspan
  let : IsManifold 𝓘(ℝ, X) 1 M := IsManifold.of_le (n := ∞) (by norm_num)
  filter_upwards [mem_residual_setOf_isRegular_affineFamily s₀ s hspan] with a ha
  refine ⟨ha, TauCeti.finite_sectionZero_of_contMDiff (I := 𝓘(ℝ, X)) (by simp)
    (affineFamily s₀ s a).contMDiff ?_
    (TauCeti.isRegularSectionParameter_iff.mp ha) ?_⟩
  · intro x hx
    have hc := (contMDiffAt_totalSpace_iff.mp ((affineFamily s₀ s a).contMDiff x)).2
    exact (TauCeti.isFredholm_sectionLinearization_iff continuousAt_id
      (mem_baseSet_trivializationAt F V x) (hc.mdifferentiableAt (by simp)) hx).mpr
        (ContinuousLinearMap.isFredholm_of_finiteDimensional _)
  · intro x _
    rw [TauCeti.index_sectionLinearization_of_finiteDimensional, hdim, sub_self]

end RegularParameters

end ContMDiffSection

namespace TauCeti

open ContMDiffSection

variable {X M F : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [TopologicalSpace M] [ChartedSpace X M]
  [T2Space M] [CompactSpace M] [IsManifold 𝓘(ℝ, X) ∞ M]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  {V : M → Type*} [TopologicalSpace (TotalSpace F V)]
  [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)] [∀ x, TopologicalSpace (V x)]
  [FiberBundle F V] [VectorBundle ℝ F V] [ContMDiffVectorBundle ∞ F V 𝓘(ℝ, X)]

/-- A smooth real vector bundle of finite rank exceeding the dimension of its compact Hausdorff
base manifold has a smooth nowhere-zero section. The model space `X` of the base is not assumed
finite-dimensional: compactness forces this whenever the base is nonempty. -/
theorem exists_contMDiffSection_forall_ne_zero_of_finrank_lt (hdim : finrank ℝ X < finrank ℝ F) :
    ∃ s : ContMDiffSection 𝓘(ℝ, X) F ∞ V, ∀ x, s x ≠ 0 := by
  rcases isEmpty_or_nonempty M with _ | _
  · exact ⟨0, fun x ↦ isEmptyElim x⟩
  have : FiniteDimensional ℝ X := .of_locallyCompact_manifold M 𝓘(ℝ, X)
  have : FiniteDimensional ℝ F := Module.finite_of_finrank_pos (pos_of_gt hdim)
  let : SecondCountableTopology M := ChartedSpace.secondCountable_of_sigmaCompact X M
  obtain ⟨n, s, hspan⟩ := exists_fin_spanning_contMDiffSection (I := 𝓘(ℝ, X)) (F := F) (V := V)
  obtain ⟨a, ha⟩ := (dense_setOf_affineFamily_ne_zero 0 s hspan hdim).nonempty
  exact ⟨affineFamily 0 s a, ha⟩

/-- A smooth bundle over a compact Hausdorff base, of finite rank equal to the `finrank` of the
model space `X` of the base, has a smooth section with surjective intrinsic linearization at every
zero and finitely many zeros. The model space `X` is not assumed finite-dimensional: compactness
forces this whenever the base is nonempty. -/
theorem exists_contMDiffSection_regular_finite_zero_of_finrank_eq [FiniteDimensional ℝ F]
    (hdim : finrank ℝ X = finrank ℝ F) :
    ∃ s : ContMDiffSection 𝓘(ℝ, X) F ∞ V,
      (∀ x, s x = 0 → Surjective (TauCeti.sectionLinearization (F := F) 𝓘(ℝ, X) id s x)) ∧
        {x | s x = 0}.Finite := by
  rcases isEmpty_or_nonempty M with _ | _
  · exact ⟨0, fun x ↦ isEmptyElim x, toFinite _⟩
  have : FiniteDimensional ℝ X := .of_locallyCompact_manifold M 𝓘(ℝ, X)
  let : SecondCountableTopology M := ChartedSpace.secondCountable_of_sigmaCompact X M
  obtain ⟨n, s, hspan⟩ := exists_fin_spanning_contMDiffSection (I := 𝓘(ℝ, X)) (F := F) (V := V)
  obtain ⟨a, ha⟩ := (dense_of_mem_residual
    (mem_residual_setOf_regular_and_finite_zero_affineFamily 0 s hspan hdim)).nonempty
  exact ⟨affineFamily 0 s a, TauCeti.isRegularSectionParameter_iff.mp ha.1, ha.2⟩

/-- A smooth bundle over a compact Hausdorff base, of finite rank equal to the base model
`finrank` and with nontrivial model fibre, has a smooth section with surjective intrinsic
linearization at every zero and finitely many zeros, none in a given countable set. The base model
is not assumed finite-dimensional: compactness forces this whenever the base is nonempty. -/
theorem exists_contMDiffSection_regular_finite_zero_forall_mem_ne_zero
    [FiniteDimensional ℝ F] [Nontrivial F]
    (hdim : finrank ℝ X = finrank ℝ F) {S : Set M} (hS : S.Countable) :
    ∃ s : ContMDiffSection 𝓘(ℝ, X) F ∞ V,
      (∀ x, s x = 0 → Surjective (TauCeti.sectionLinearization (F := F) 𝓘(ℝ, X) id s x)) ∧
        {x | s x = 0}.Finite ∧ ∀ x ∈ S, s x ≠ 0 := by
  rcases isEmpty_or_nonempty M with _ | _
  · exact ⟨0, fun x ↦ isEmptyElim x, toFinite _, fun x ↦ isEmptyElim x⟩
  have : FiniteDimensional ℝ X := .of_locallyCompact_manifold M 𝓘(ℝ, X)
  let : SecondCountableTopology M := ChartedSpace.secondCountable_of_sigmaCompact X M
  obtain ⟨n, s, hspan⟩ := exists_fin_spanning_contMDiffSection (I := 𝓘(ℝ, X)) (F := F) (V := V)
  obtain ⟨a, ha, hS⟩ := (dense_of_mem_residual
    (inter_mem
      (mem_residual_setOf_regular_and_finite_zero_affineFamily 0 s hspan hdim)
      (mem_residual_setOf_forall_mem_affineFamily_ne_zero 0 s hS fun x _ ↦
        VectorBundle.exists_ne_zero_of_span_range_eq_top F (hspan x)))).nonempty
  exact ⟨affineFamily 0 s a, TauCeti.isRegularSectionParameter_iff.mp ha.1, ha.2, hS⟩


end TauCeti
