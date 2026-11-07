/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.VectorBundle.Section.SmoothZero
public import TauCeti.Analysis.Fredholm.LevelSet.GlobalParametric
import TauCeti.Geometry.Manifold.MFDeriv.Chart

/-!
# Parametric transversality for Fredholm bundle sections

Let `M` be a Banach manifold, `Λ` a Banach space of parameters, and `s` a section along a map
`b : M × Λ → B` to the base of a vector bundle. A parameter `l` is *regular* when the section
`s (·, l)` of the restricted bundle is regular: its intrinsic linearization is surjective at every
one of its zeros. If the linearization of `s` in the `M` direction is Fredholm and the total
linearization is surjective at every zero, the regular parameters form a residual set, hence a
dense set for Banach `Λ`. For such a parameter the zeros of `s (·, l)` then form a `C^n` manifold
whose dimension is the Fredholm index. This is the abstract transversality package used to show
that moduli spaces cut out by a generic perturbation are manifolds.

If the slice linearizations have negative index at all zeros, regularity is equivalent to
absence of zeros. Thus zero-free parameters form a residual, dense set: a negative expected
dimension means an empty moduli space. The index need not be constant, and its sign is required
only at actual zeros.

Smoothness of the section is required only at zeros, and all hypotheses are stated for the
intrinsic linearizations. The manifold structure on the zeros also uses a smooth bundle. The
finite differentiability threshold is the current Sard--Smale bound `(dim ker)² + 1`, not the
optimal bound. No norm on the individual bundle fibers is needed.

The proof reads the section in a source chart and a bundle trivialization at each zero, applies
the local parametric theorem for Banach-space equations to that coordinate expression, and takes
a countable cover of the actual section zero set. Zeros of a coordinate expression outside its
chart or trivialization are never treated as section zeros. Away from the centre of the chart, the
coordinate derivative in the `M` direction is the intrinsic one followed by the derivative of the
inverse chart, so non-regular section zeros give non-regular coordinate zeros.

## Main results

* `TauCeti.isMeagre_setOf_not_isRegularSectionParameter`: the non-regular parameters are meagre.
* `TauCeti.dense_setOf_isRegularSectionParameter`: regular parameters are dense.
* `TauCeti.eventually_residual_exists_isManifold_sectionZero`: for a residual set of parameters,
  the zeros form a `C^n` manifold of dimension the index, with a `C^n` immersion whose tangent
  spaces are the kernels.
* `TauCeti.isRegularSectionParameter_iff_forall_ne_zero_of_index_neg`: with negative slice
  indices at zeros, regularity is equivalent to absence of zeros.
* `TauCeti.mem_residual_setOf_forall_section_ne_zero_of_index_neg` and
  `TauCeti.dense_setOf_forall_section_ne_zero_of_index_neg`: zero-free parameters form a residual,
  dense set when the slice indices at zeros are negative.

## References

* D. McDuff, D. Salamon, *J-holomorphic Curves and Symplectic Topology*, 2nd ed.,
  Appendix A.3 (Theorem A.3.6 and its proof).
* S. Smale, *An infinite dimensional version of Sard's theorem*, Amer. J. Math.
  87 (1965), 861--866.

The local analytic input is
`TauCeti.exists_mem_nhds_isClosed_isNowhereDense_image_not_surjective_levelSetParameterMap`.
-/

public section

open Bundle Filter Function Module Set
open scoped ContDiff Manifold Topology

namespace TauCeti

variable {X Λ M B F EB HB : Type*} {E : B → Type*}
  [NormedAddCommGroup X] [NormedSpace ℝ X]
  [TopologicalSpace M] [ChartedSpace X M]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup EB] [NormedSpace ℝ EB]
  [TopologicalSpace HB] {I : ModelWithCorners ℝ EB HB}
  [TopologicalSpace B] [ChartedSpace HB B]
  [∀ a, TopologicalSpace (E a)] [TopologicalSpace (TotalSpace F E)]
  [∀ a, AddCommGroup (E a)] [∀ a, Module ℝ (E a)]
  [FiberBundle F E] [VectorBundle ℝ F E]
  {b : M × Λ → B} {s : ∀ z, E (b z)}

variable (X) in
/-- A parameter `l` is regular for a section along `b : M × Λ → B` when the section
`s (·, l)` along `b (·, l)` has surjective intrinsic linearization at each of its zeros.
Regularity of the total linearization is a separate condition. -/
def IsRegularSectionParameter (b : M × Λ → B) (s : ∀ z, E (b z)) (l : Λ) : Prop :=
  ∀ x, s (x, l) = 0 → Surjective
    (sectionLinearization (F := F) 𝓘(ℝ, X) (fun y ↦ b (y, l)) (fun y ↦ s (y, l)) x)

/-- Characterization of a regular parameter by the linearizations at its zeros. -/
theorem isRegularSectionParameter_iff {l : Λ} :
    IsRegularSectionParameter (F := F) X b s l ↔
      ∀ x, s (x, l) = 0 → Surjective
        (sectionLinearization (F := F) 𝓘(ℝ, X) (fun y ↦ b (y, l)) (fun y ↦ s (y, l)) x) :=
  (Iff.rfl)

/-- When every zero of a parameter slice has negative index, the parameter is regular if and
only if that slice has no zeros. This implication needs no smoothness or Fredholm assumption:
surjectivity alone forces the algebraic index to be nonnegative. -/
theorem isRegularSectionParameter_iff_forall_ne_zero_of_index_neg {l : Λ}
    (hindex : ∀ x, s (x, l) = 0 → LinearMap.index
      (sectionLinearization (F := F) 𝓘(ℝ, X) (fun y ↦ b (y, l))
        (fun y ↦ s (y, l)) x).toLinearMap < 0) :
    IsRegularSectionParameter (F := F) X b s l ↔ ∀ x, s (x, l) ≠ 0 := by
  rw [isRegularSectionParameter_iff]
  constructor
  · intro hl x hx
    have hi := hindex x hx
    rw [LinearMap.index_of_surjective (hl x hx)] at hi
    exact (not_lt_of_ge (Int.natCast_nonneg _)) hi
  · intro hl x hx
    exact (hl x hx).elim

/-- In a trivial bundle, a parameter is regular exactly when the fiber-valued equation
`f (·, l) = 0` has surjective manifold derivative at each of its solutions. -/
@[simp]
theorem isRegularSectionParameter_trivial (b : M × Λ → B) (f : M × Λ → F) (l : Λ) :
    IsRegularSectionParameter (E := Bundle.Trivial B F) (F := F) X b f l ↔
      ∀ x, f (x, l) = 0 → Surjective (mvfderiv 𝓘(ℝ, X) (fun y ↦ f (y, l)) x) := by
  simp only [isRegularSectionParameter_iff, sectionLinearization_trivial]

variable [NormedAddCommGroup Λ] [NormedSpace ℝ Λ] [CompleteSpace X] [CompleteSpace Λ]
  [CompleteSpace F] [IsManifold 𝓘(ℝ, X) 1 M]

omit [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace X] [CompleteSpace Λ]
  [CompleteSpace F] [IsManifold 𝓘(ℝ, X) 1 M] in
/-- The coordinate expression of a function on `M × Λ` in the chart at `(x, l)` is the
expression in the chart at `x`, with the parameter left alone. -/
private theorem comp_extChartAt_prod_symm_eq {c : M × Λ → F} {f : X × Λ → F} {x : M} (l : Λ)
    (hf : ∀ p, f p = c ((extChartAt 𝓘(ℝ, X) x).symm p.1, p.2)) :
    c ∘ (extChartAt (𝓘(ℝ, X).prod 𝓘(ℝ, Λ)) (x, l)).symm = f := by
  rw [extChartAt_prod]
  ext p
  simp [hf]

omit [NormedSpace ℝ F] [∀ a, TopologicalSpace (E a)] [∀ a, Module ℝ (E a)] [FiberBundle F E]
  [VectorBundle ℝ F E] [∀ a, AddCommGroup (E a)] [NormedAddCommGroup Λ] [NormedSpace ℝ Λ]
  [CompleteSpace X] [CompleteSpace Λ] [CompleteSpace F] [IsManifold 𝓘(ℝ, X) 1 M] in
/-- The coordinate equation `f` restricted to a fixed parameter is the section read in the
trivialization `e`, composed with the inverse chart. -/
private theorem coordinate_comp_symm_eq {x : M} {k : Λ} {e : Trivialization F (π F E)}
    {f : X × Λ → F}
    (hf : ∀ p, f p = (e ⟨b ((extChartAt 𝓘(ℝ, X) x).symm p.1, p.2),
      s ((extChartAt 𝓘(ℝ, X) x).symm p.1, p.2)⟩).2) :
    (fun y ↦ (e ⟨b (y, k), s (y, k)⟩).2) ∘ (extChartAt 𝓘(ℝ, X) x).symm = fun y ↦ f (y, k) := by
  ext y
  simp [hf]

omit [CompleteSpace X] [CompleteSpace Λ] [CompleteSpace F] [IsManifold 𝓘(ℝ, X) 1 M] in
/-- At a section zero, the derivative of the coordinate equation `f` in the `M` direction is the
intrinsic linearization at the centre of the chart, so it has the same surjectivity, Fredholm
and kernel properties as the intrinsic one, and the total derivative is surjective. Here `f` is
the section read in the chart at `x` and a trivialization `e` over the point `b (x, l)`. -/
private theorem coordinate_derivative_facts_at_zero {n : ℕ∞ω} {x : M} {l : Λ}
    {e : Trivialization F (π F E)} (hee : e = trivializationAt F E (b (x, l)))
    {f : X × Λ → F}
    (hf : ∀ p, f p = (e ⟨b ((extChartAt 𝓘(ℝ, X) x).symm p.1, p.2),
      s ((extChartAt 𝓘(ℝ, X) x).symm p.1, p.2)⟩).2)
    (hcont : ContMDiffAt (𝓘(ℝ, X).prod 𝓘(ℝ, Λ)) (I.prod 𝓘(ℝ, F)) n
      (fun w ↦ (⟨b w, s w⟩ : TotalSpace F E)) (x, l))
    (hFred : ContinuousLinearMap.IsFredholm
      (sectionLinearization (F := F) 𝓘(ℝ, X) (fun y ↦ b (y, l)) (fun y ↦ s (y, l)) x))
    (htotal : Surjective (sectionLinearization (F := F) (𝓘(ℝ, X).prod 𝓘(ℝ, Λ)) b s (x, l)))
    (hn : ((finrank ℝ (sectionLinearization (F := F) 𝓘(ℝ, X) (fun y ↦ b (y, l))
      (fun y ↦ s (y, l)) x).ker ^ 2 + 1 : ℕ) : ℕ∞ω) ≤ n)
    (hz : s (x, l) = 0) (hb : ∀ w, s w = 0 → ContinuousAt b w) :
    ContDiffAt ℝ n f (extChartAt 𝓘(ℝ, X) x x, l) ∧
      Surjective (fderiv ℝ f (extChartAt 𝓘(ℝ, X) x x, l)) ∧
      ContinuousLinearMap.IsFredholm ((fderiv ℝ f (extChartAt 𝓘(ℝ, X) x x, l)).comp
        (ContinuousLinearMap.inl ℝ X Λ)) ∧
      ((finrank ℝ ((fderiv ℝ f (extChartAt 𝓘(ℝ, X) x x, l)).comp
        (ContinuousLinearMap.inl ℝ X Λ)).ker * finrank ℝ ((fderiv ℝ f
        (extChartAt 𝓘(ℝ, X) x x, l)).comp (ContinuousLinearMap.inl ℝ X Λ)).ker + 1 : ℕ) :
          ℕ∞ω) ≤ n := by
  subst hee
  have he : b (x, l) ∈ (trivializationAt F E (b (x, l))).baseSet :=
    mem_baseSet_trivializationAt F E (b (x, l))
  let c : M × Λ → F := fun w ↦ (trivializationAt F E (b (x, l)) ⟨b w, s w⟩).2
  have hn0 : n ≠ 0 := by
    rintro rfl
    exact absurd hn (by simp)
  have hcn : ContMDiffAt (𝓘(ℝ, X).prod 𝓘(ℝ, Λ)) 𝓘(ℝ, F) n c (x, l) :=
    (contMDiffAt_totalSpace.mp hcont).2
  have hcd : MDifferentiableAt (𝓘(ℝ, X).prod 𝓘(ℝ, Λ)) 𝓘(ℝ, F) c (x, l) :=
    hcn.mdifferentiableAt hn0
  have hfeq := comp_extChartAt_prod_symm_eq (c := c) l hf
  have hpt : extChartAt (𝓘(ℝ, X).prod 𝓘(ℝ, Λ)) (x, l) (x, l) = (extChartAt 𝓘(ℝ, X) x x, l) := by
    simp
  have hfn : ContDiffAt ℝ n f (extChartAt 𝓘(ℝ, X) x x, l) := by
    simpa only [hfeq, hpt] using hcn.contDiffAt_comp_extChartAt_symm
  have hcl : MDifferentiableAt 𝓘(ℝ, X) 𝓘(ℝ, F) (fun y ↦ c (y, l)) x :=
    hcd.comp (I' := 𝓘(ℝ, X).prod 𝓘(ℝ, Λ)) (f := fun y ↦ (y, l)) x
      (mdifferentiableAt_id.prodMk mdifferentiableAt_const)
  have hbl : ContinuousAt (fun y ↦ b (y, l)) x :=
    ContinuousAt.comp (f := fun y ↦ (y, l)) (hb _ hz) (continuousAt_id.prodMk continuousAt_const)
  have hD₁ : (fderiv ℝ f (extChartAt 𝓘(ℝ, X) x x, l)).comp (ContinuousLinearMap.inl ℝ X Λ) =
      mvfderiv 𝓘(ℝ, X) (fun y ↦ c (y, l)) x := by
    rw [hcl.mvfderiv_eq_fderiv_comp_extChartAt_symm, coordinate_comp_symm_eq hf]
    exact ((hfn.differentiableAt hn0).hasFDerivAt.comp (extChartAt 𝓘(ℝ, X) x x)
      (hasFDerivAt_prodMk_left (𝕜 := ℝ) (extChartAt 𝓘(ℝ, X) x x) l)).fderiv.symm
  refine ⟨hfn, ?_, ?_, ?_⟩
  · rw [← hfeq, ← hpt, ← hcd.mvfderiv_eq_fderiv_comp_extChartAt_symm]
    exact (surjective_sectionLinearization_iff (hb _ hz) he hcd hz).mp htotal
  · rw [hD₁]
    exact (isFredholm_sectionLinearization_iff hbl he hcl hz).mp hFred
  · rw [ker_sectionLinearization hbl he hcl hz] at hn
    rw [hD₁, ← pow_two]
    exact hn

omit [CompleteSpace X] [CompleteSpace Λ] [CompleteSpace F] in
/-- Away from the centre of the chart, if the coordinate derivative in the `M` direction is
surjective at a section zero over the trivialization's base set, then the intrinsic
linearization there is surjective: it is the coordinate derivative composed with the derivative
of the chart. -/
private theorem surjective_sectionLinearization_of_surjective_fderiv_comp_inl {x x' : M} {k : Λ}
    {e : Trivialization F (π F E)} [MemTrivializationAtlas e] {f : X × Λ → F}
    (hf : ∀ p, f p = (e ⟨b ((extChartAt 𝓘(ℝ, X) x).symm p.1, p.2),
      s ((extChartAt 𝓘(ℝ, X) x).symm p.1, p.2)⟩).2)
    (hx' : x' ∈ (chartAt X x).source) (hwe : b (x', k) ∈ e.baseSet)
    (hw : s (x', k) = 0) (hb : ∀ w, s w = 0 → ContinuousAt b w)
    (hwd : DifferentiableAt ℝ f (extChartAt 𝓘(ℝ, X) x x', k))
    (hcoord : Surjective ((fderiv ℝ f (extChartAt 𝓘(ℝ, X) x x', k)).comp
      (ContinuousLinearMap.inl ℝ X Λ))) :
    Surjective (sectionLinearization (F := F) 𝓘(ℝ, X) (fun y ↦ b (y, k))
      (fun y ↦ s (y, k)) x') := by
  let c : M × Λ → F := fun w ↦ (e ⟨b w, s w⟩).2
  set φ := extChartAt 𝓘(ℝ, X) x with hφ
  have hx'φ : x' ∈ φ.source := by rwa [hφ, extChartAt_source]
  have hleft : φ.symm (φ x') = x' := φ.left_inv hx'φ
  have hfk : HasFDerivAt (fun y ↦ f (y, k)) ((fderiv ℝ f (φ x', k)).comp
      (ContinuousLinearMap.inl ℝ X Λ)) (φ x') :=
    HasFDerivAt.comp (g := f) (φ x') hwd.hasFDerivAt (hasFDerivAt_prodMk_left (φ x') k)
  have hck : MDifferentiableAt 𝓘(ℝ, X) 𝓘(ℝ, F) (fun y ↦ c (y, k)) x' := by
    refine (hfk.differentiableAt.mdifferentiableAt.comp x'
      (mdifferentiableAt_extChartAt hx')).congr_of_eventuallyEq ?_
    filter_upwards [extChartAt_source_mem_nhds' hx'φ] with y hy
    have hy' : y ∈ φ.source := hy
    simp only [comp_apply, hf, c]
    rw [φ.left_inv hy']
  have hbk : ContinuousAt (fun y ↦ b (y, k)) x' :=
    ContinuousAt.comp (f := fun y ↦ (y, k)) (hb _ hw) (continuousAt_id.prodMk continuousAt_const)
  refine (surjective_sectionLinearization_iff hbk hwe hck hw).mpr ?_
  have hsymm : MDifferentiableAt 𝓘(ℝ, X) 𝓘(ℝ, X) φ.symm (φ x') := by
    have h := mdifferentiableWithinAt_extChartAt_symm (I := 𝓘(ℝ, X)) (φ.map_source hx'φ)
    rwa [modelWithCornersSelf_coe, range_id, mdifferentiableWithinAt_univ] at h
  have hck' : MDifferentiableAt 𝓘(ℝ, X) 𝓘(ℝ, F) (fun y ↦ c (y, k)) (φ.symm (φ x')) := by
    rwa [hleft]
  have hcomp := mvfderiv_comp (φ x') hck' hsymm
  have hfd : fderiv ℝ ((fun y ↦ c (y, k)) ∘ φ.symm) (φ x') =
      (fderiv ℝ f (φ x', k)).comp (ContinuousLinearMap.inl ℝ X Λ) := by
    rw [coordinate_comp_symm_eq hf]
    exact hfk.fderiv
  rw [mvfderiv_eq_fderiv, hfd] at hcomp
  have hs : Surjective ((mvfderiv 𝓘(ℝ, X) (fun y ↦ c (y, k)) (φ.symm (φ x'))).comp
      (mfderiv 𝓘(ℝ, X) 𝓘(ℝ, X) φ.symm (φ x'))) := by
    rw [← hcomp, ContinuousLinearMap.coe_comp]
    exact hcoord.comp (NormedSpace.fromTangentSpace (φ x')).surjective
  rw [ContinuousLinearMap.coe_comp] at hs
  have h := hs.of_comp
  rwa [hleft] at h

/-- Near a zero, the parameters of nearby non-regular zeros lie in a nowhere dense set. The
section is read in the preferred source chart and bundle trivialization at the zero. -/
private theorem exists_section_badParameter_neighborhood {n : ℕ∞ω} {x : M} {l : Λ}
    (hcont : ContMDiffAt (𝓘(ℝ, X).prod 𝓘(ℝ, Λ)) (I.prod 𝓘(ℝ, F)) n
      (fun w ↦ (⟨b w, s w⟩ : TotalSpace F E)) (x, l))
    (hFred : ContinuousLinearMap.IsFredholm
      (sectionLinearization (F := F) 𝓘(ℝ, X) (fun y ↦ b (y, l)) (fun y ↦ s (y, l)) x))
    (htotal : Surjective (sectionLinearization (F := F) (𝓘(ℝ, X).prod 𝓘(ℝ, Λ)) b s (x, l)))
    (hn : ((finrank ℝ (sectionLinearization (F := F) 𝓘(ℝ, X) (fun y ↦ b (y, l))
      (fun y ↦ s (y, l)) x).ker ^ 2 + 1 : ℕ) : ℕ∞ω) ≤ n)
    (hz : s (x, l) = 0)
    (hb : ∀ w, s w = 0 → ContinuousAt b w) :
    ∃ Q ∈ 𝓝 (⟨(x, l), hz⟩ : ↥{w | s w = 0}), ∃ A : Set Λ, IsNowhereDense A ∧
      ∀ w : ↥{w | s w = 0}, w ∈ Q →
        ¬ Surjective (sectionLinearization (F := F) 𝓘(ℝ, X) (fun y ↦ b (y, (w : M × Λ).2))
          (fun y ↦ s (y, (w : M × Λ).2)) (w : M × Λ).1) → (w : M × Λ).2 ∈ A := by
  -- Structure of the proof: (1) read the section as an equation `f = 0` on `X × Λ`, in the chart
  -- at `x` and the trivialization at `b (x, l)`, and identify its derivatives at the centre with
  -- the intrinsic linearizations; (2) apply local Sard--Smale to `f`; (3) show that a nearby
  -- non-regular section zero is a non-regular zero of `f` close to the centre.
  let e := trivializationAt F E (b (x, l))
  let φ := extChartAt 𝓘(ℝ, X) x
  let f : X × Λ → F := fun p ↦ (e ⟨b (φ.symm p.1, p.2), s (φ.symm p.1, p.2)⟩).2
  have hf : ∀ p, f p = (e ⟨b (φ.symm p.1, p.2), s (φ.symm p.1, p.2)⟩).2 := fun _ ↦ rfl
  have he : b (x, l) ∈ e.baseSet := mem_baseSet_trivializationAt F E (b (x, l))
  obtain ⟨hfn, hsurj, hFred', hn'⟩ :=
    coordinate_derivative_facts_at_zero rfl hf hcont hFred htotal hn hz hb
  have hn0 : n ≠ 0 := by
    rintro rfl
    exact absurd hn (by simp)
  have hstrict : HasStrictFDerivAt f ((fderiv ℝ f (φ x, l)).comp (ContinuousLinearMap.inl ℝ X Λ)
      |>.coprod ((fderiv ℝ f (φ x, l)).comp (ContinuousLinearMap.inr ℝ X Λ))) (φ x, l) := by
    simpa only [ContinuousLinearMap.coprod_comp_inl_inr] using
      hfn.hasStrictFDerivAt_fderiv hn0
  -- A section zero in the chart source and over the trivialization's base set is a coordinate
  -- zero.
  have hfzero_of : ∀ {x' : M} {k : Λ}, x' ∈ φ.source → b (x', k) ∈ e.baseSet →
      s (x', k) = 0 → f (φ x', k) = 0 := by
    intro x' k hx' hbase hzero
    simp only [f]
    rw [φ.left_inv hx', hzero]
    exact congrArg Prod.snd (e.zeroSection ℝ hbase)
  obtain ⟨V, hV, A, hA, hVA⟩ :=
    exists_mem_nhds_isNowhereDense_forall_not_surjective_fderiv_comp_inl_mem hstrict hfn hFred'
      (by simpa only [ContinuousLinearMap.coprod_comp_inl_inr] using hsurj)
      (hfzero_of (mem_extChartAt_source x) he hz) hn'
  -- Points near `(x, l)` are read in the chart at `x`.
  let ψ : M × Λ → X × Λ := fun w ↦ (φ w.1, w.2)
  have hψ : ContinuousAt ψ (x, l) :=
    (ContinuousAt.comp (f := Prod.fst) (continuousAt_extChartAt (I := 𝓘(ℝ, X)) x)
      continuousAt_fst).prodMk continuousAt_snd
  have hsource : (chartAt X x).source ×ˢ univ ∈ 𝓝 (x, l) :=
    prod_mem_nhds (chart_source_mem_nhds X x) univ_mem
  have hbase : b ⁻¹' e.baseSet ∈ 𝓝 (x, l) :=
    (hb _ hz).preimage_mem_nhds (e.open_baseSet.mem_nhds he)
  -- Restrict to the chart source and the trivialization's base set: extended coordinate zeros
  -- outside them need not be section zeros. The intrinsic linearization is recovered here.
  refine ⟨Subtype.val ⁻¹' ((chartAt X x).source ×ˢ univ ∩ b ⁻¹' e.baseSet ∩ ψ ⁻¹' V),
    continuous_subtype_val.continuousAt.preimage_mem_nhds
      (inter_mem (inter_mem hsource hbase) (hψ.preimage_mem_nhds hV)), A, hA, ?_⟩
  rintro ⟨⟨x', k⟩, hw⟩ ⟨⟨⟨hx', -⟩, hwe⟩, hwV⟩ hbad
  simp only [mem_ofPred_eq] at hw hwe
  have hx'φ : x' ∈ φ.source := by rwa [extChartAt_source]
  obtain ⟨hwd, hwA⟩ := hVA _ hwV
  exact hwA (hfzero_of hx'φ hwe hw) fun hcoord ↦
    hbad (surjective_sectionLinearization_of_surjective_fderiv_comp_inl hf hx' hwe hw hb hwd
      hcoord)

variable [SecondCountableTopology ↥{z | s z = 0}] {n : ℕ∞ω}
    (hcont : ∀ z, s z = 0 → ContMDiffAt (𝓘(ℝ, X).prod 𝓘(ℝ, Λ)) (I.prod 𝓘(ℝ, F)) n
      (fun w ↦ (⟨b w, s w⟩ : TotalSpace F E)) z)
    (hFred : ∀ z, s z = 0 → ContinuousLinearMap.IsFredholm
      (sectionLinearization (F := F) 𝓘(ℝ, X) (fun y ↦ b (y, z.2)) (fun y ↦ s (y, z.2)) z.1))
    (htotal : ∀ z, s z = 0 →
      Surjective (sectionLinearization (F := F) (𝓘(ℝ, X).prod 𝓘(ℝ, Λ)) b s z))
    (hn : ∀ z, s z = 0 → ((finrank ℝ (sectionLinearization (F := F) 𝓘(ℝ, X)
      (fun y ↦ b (y, z.2)) (fun y ↦ s (y, z.2)) z.1).ker ^ 2 + 1 : ℕ) : ℕ∞ω) ≤ n)

include hcont hFred htotal hn

/-- **Parametric transversality for bundle sections.** Non-regular parameters are meagre when
the total linearization is surjective and the linearization in the `M` direction is Fredholm at
every zero. Second countability is needed only for the actual universal zero set. -/
theorem isMeagre_setOf_not_isRegularSectionParameter :
    IsMeagre {l | ¬ IsRegularSectionParameter (F := F) X b s l} := by
  have hb : ∀ z, s z = 0 → ContinuousAt b z := fun z hz ↦
    (contMDiffAt_totalSpace.mp (hcont z hz)).1.continuousAt
  have hlocal := fun z : ↥{z | s z = 0} ↦
    exists_section_badParameter_neighborhood (hcont z z.2) (hFred z z.2)
      (htotal z z.2) (hn z z.2) z.2 hb
  choose! Q hQ A hA hQA using hlocal
  obtain ⟨t, -, htcount, htcover⟩ := TopologicalSpace.countable_cover_nhdsWithin
    (f := Q) (s := (univ : Set ↥{z | s z = 0})) fun z _ ↦ nhdsWithin_le_nhds (hQ z)
  -- A countable cover of the true zero set captures every non-regular parameter.
  apply IsMeagre.mono (s := ⋃ z ∈ t, A z)
  · intro l hl
    have hl' : ¬ IsRegularSectionParameter (F := F) X b s l := hl
    rw [isRegularSectionParameter_iff] at hl'
    push Not at hl'
    obtain ⟨x, hx, hbad⟩ := hl'
    let w : ↥{z | s z = 0} := ⟨(x, l), hx⟩
    obtain ⟨z, hzt, hwQ⟩ := mem_iUnion₂.mp (htcover (mem_univ w))
    exact mem_iUnion₂.mpr ⟨z, hzt, hQA z w hwQ hbad⟩
  · exact isMeagre_biUnion htcount fun z _ ↦ (hA z).isMeagre

/-- Regular parameters of a universal Fredholm bundle section form a residual set. -/
theorem mem_residual_setOf_isRegularSectionParameter :
    {l | IsRegularSectionParameter (F := F) X b s l} ∈ residual Λ := by
  simpa only [IsMeagre, Set.compl_ofPred, Classical.not_not] using
    isMeagre_setOf_not_isRegularSectionParameter hcont hFred htotal hn

/-- Regular parameters of a universal Fredholm bundle section are dense in the Banach
parameter space. -/
theorem dense_setOf_isRegularSectionParameter :
    Dense {l | IsRegularSectionParameter (F := F) X b s l} :=
  dense_of_mem_residual
    (mem_residual_setOf_isRegularSectionParameter hcont hFred htotal hn)

omit [IsManifold 𝓘(ℝ, X) 1 M] in
/-- **Generic regular zeros.** For a residual set of parameters `l`, the zeros of `s (·, l)`
form a `C^n` manifold of dimension the index `d`, with a `C^n` immersion into `M` whose tangent
spaces are the kernels of the linearizations in the `M` direction. -/
theorem eventually_residual_exists_isManifold_sectionZero {d : ℕ}
    [IsManifold 𝓘(ℝ, X) n M] [ContMDiffVectorBundle n F E I] (hn0 : n ≠ 0)
    (hindex : ∀ z, s z = 0 → LinearMap.index (sectionLinearization (F := F) 𝓘(ℝ, X)
      (fun y ↦ b (y, z.2)) (fun y ↦ s (y, z.2)) z.1).toLinearMap = d) :
    ∀ᶠ l in residual Λ, ∃ cs : ChartedSpace (Fin d → ℝ) ↥{x | s (x, l) = 0},
      letI := cs
      IsManifold 𝓘(ℝ, Fin d → ℝ) n ↥{x | s (x, l) = 0} ∧
        Manifold.IsImmersionOfComplement F 𝓘(ℝ, Fin d → ℝ) 𝓘(ℝ, X) n
          (Subtype.val : ↥{x | s (x, l) = 0} → M) ∧
        ∀ z : ↥{x | s (x, l) = 0},
          (mfderiv 𝓘(ℝ, Fin d → ℝ) 𝓘(ℝ, X) Subtype.val z).range =
            (sectionLinearization (F := F) 𝓘(ℝ, X) (fun y ↦ b (y, l))
              (fun y ↦ s (y, l)) z.1).ker := by
  have : IsManifold 𝓘(ℝ, X) 1 M := .of_le (ENat.one_le_iff_ne_zero_withTop.mpr hn0)
  filter_upwards [mem_residual_setOf_isRegularSectionParameter hcont hFred htotal hn] with l hl
  exact exists_isManifold_sectionZero_of_contMDiff hn0
    (fun x hx ↦ ContMDiffAt.comp (g := fun w ↦ (⟨b w, s w⟩ : TotalSpace F E))
      (f := fun y ↦ (y, l)) x (hcont (x, l) hx) (contMDiffAt_id.prodMk contMDiffAt_const))
    (fun x hx ↦ hFred (x, l) hx) hl (fun x hx ↦ hindex (x, l) hx)

variable
  (hindex : ∀ z, s z = 0 → LinearMap.index (sectionLinearization (F := F) 𝓘(ℝ, X)
    (fun y ↦ b (y, z.2)) (fun y ↦ s (y, z.2)) z.1).toLinearMap < 0)

include hindex

/-- **Generic absence of negative-index zeros.** If the slice linearization is Fredholm of
negative index at each zero and the total section is transverse to zero, zero-free parameters
form a residual set. Second countability is needed only for the universal zero set. -/
theorem mem_residual_setOf_forall_section_ne_zero_of_index_neg :
    {l | ∀ x, s (x, l) ≠ 0} ∈ residual Λ := by
  filter_upwards [mem_residual_setOf_isRegularSectionParameter hcont hFred htotal hn] with l hl
  exact (isRegularSectionParameter_iff_forall_ne_zero_of_index_neg
    (fun x hx ↦ hindex (x, l) hx)).mp hl

/-- Zero-free parameters of a transverse universal section with negative slice indices are
dense in the Banach parameter space. In particular they occur arbitrarily near any prescribed
parameter, without a constant-index assumption. -/
theorem dense_setOf_forall_section_ne_zero_of_index_neg :
    Dense {l | ∀ x, s (x, l) ≠ 0} :=
  dense_of_mem_residual
    (mem_residual_setOf_forall_section_ne_zero_of_index_neg hcont hFred htotal hn hindex)

end TauCeti
