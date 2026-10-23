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

/-- In a trivial bundle, a parameter is regular exactly when the fiber-valued equation
`f (·, l) = 0` has surjective manifold derivative at each of its solutions. -/
@[simp]
theorem isRegularSectionParameter_trivial (b : M × Λ → B) (f : M × Λ → F) (l : Λ) :
    IsRegularSectionParameter (E := Bundle.Trivial B F) (F := F) X b f l ↔
      ∀ x, f (x, l) = 0 → Surjective (mvfderiv 𝓘(ℝ, X) (fun y ↦ f (y, l)) x) := by
  simp only [isRegularSectionParameter_iff, sectionLinearization_trivial]

variable [NormedAddCommGroup Λ] [NormedSpace ℝ Λ] [CompleteSpace X] [CompleteSpace Λ]
  [CompleteSpace F] [IsManifold 𝓘(ℝ, X) 1 M]

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
  -- The coordinate expression of the section, in the chart at `x` and the trivialization `e`.
  let c : M × Λ → F := fun w ↦ (e ⟨b w, s w⟩).2
  let f : X × Λ → F := fun p ↦ c (φ.symm p.1, p.2)
  have he : b (x, l) ∈ e.baseSet := mem_baseSet_trivializationAt F E (b (x, l))
  have hn0 : n ≠ 0 := by
    rintro rfl
    exact absurd hn (by simp)
  have hcn : ContMDiffAt (𝓘(ℝ, X).prod 𝓘(ℝ, Λ)) 𝓘(ℝ, F) n c (x, l) :=
    (contMDiffAt_totalSpace.mp hcont).2
  have hcd : MDifferentiableAt (𝓘(ℝ, X).prod 𝓘(ℝ, Λ)) 𝓘(ℝ, F) c (x, l) :=
    hcn.mdifferentiableAt hn0
  have hfeq : c ∘ (extChartAt (𝓘(ℝ, X).prod 𝓘(ℝ, Λ)) (x, l)).symm = f := by
    rw [extChartAt_prod]
    ext p
    simp [f, φ]
  have hpt : extChartAt (𝓘(ℝ, X).prod 𝓘(ℝ, Λ)) (x, l) (x, l) = (φ x, l) := by
    simp [φ]
  have hfn : ContDiffAt ℝ n f (φ x, l) := by
    simpa only [hfeq, hpt] using hcn.contDiffAt_comp_extChartAt_symm
  let D₁ := (fderiv ℝ f (φ x, l)).comp (ContinuousLinearMap.inl ℝ X Λ)
  let D₂ := (fderiv ℝ f (φ x, l)).comp (ContinuousLinearMap.inr ℝ X Λ)
  have hstrict : HasStrictFDerivAt f (D₁.coprod D₂) (φ x, l) := by
    simpa only [D₁, D₂, ContinuousLinearMap.coprod_comp_inl_inr] using
      hfn.hasStrictFDerivAt hn0
  have hsurj : Surjective (D₁.coprod D₂) := by
    rw [ContinuousLinearMap.coprod_comp_inl_inr, ← hfeq, ← hpt,
      ← hcd.mvfderiv_eq_fderiv_comp_extChartAt_symm]
    exact (surjective_sectionLinearization_iff (hb _ hz) he hcd hz).mp htotal
  -- At the centre of the chart, the coordinate derivative in the `M` direction is intrinsic.
  have hcl : MDifferentiableAt 𝓘(ℝ, X) 𝓘(ℝ, F) (fun y ↦ c (y, l)) x :=
    hcd.comp (I' := 𝓘(ℝ, X).prod 𝓘(ℝ, Λ)) (f := fun y ↦ (y, l)) x
      (mdifferentiableAt_id.prodMk mdifferentiableAt_const)
  have hbl : ContinuousAt (fun y ↦ b (y, l)) x :=
    ContinuousAt.comp (f := fun y ↦ (y, l)) (hb _ hz) (continuousAt_id.prodMk continuousAt_const)
  have hD₁ : D₁ = mvfderiv 𝓘(ℝ, X) (fun y ↦ c (y, l)) x := by
    rw [hcl.mvfderiv_eq_fderiv_comp_extChartAt_symm]
    exact ((hfn.differentiableAt hn0).hasFDerivAt.comp (φ x)
      (hasFDerivAt_prodMk_left (𝕜 := ℝ) (φ x) l)).fderiv.symm
  have hFred' : ContinuousLinearMap.IsFredholm D₁ := by
    rw [hD₁]
    exact (isFredholm_sectionLinearization_iff hbl he hcl hz).mp hFred
  have hn' : ((finrank ℝ D₁.ker * finrank ℝ D₁.ker + 1 : ℕ) : ℕ∞ω) ≤ n := by
    rw [ker_sectionLinearization hbl he hcl hz] at hn
    rw [hD₁, ← pow_two]
    exact hn
  -- A section zero in the chart source and over the trivialization's base set is a coordinate
  -- zero.
  have hfzero_of : ∀ {x' : M} {k : Λ}, x' ∈ φ.source → b (x', k) ∈ e.baseSet →
      s (x', k) = 0 → f (φ x', k) = 0 := by
    intro x' k hx' hbase hzero
    simp only [f, c]
    rw [φ.left_inv hx', hzero]
    exact congrArg Prod.snd (e.zeroSection ℝ hbase)
  have hfzero : f (φ x, l) = 0 := hfzero_of (mem_extChartAt_source x) he hz
  -- Apply local Sard--Smale to the coordinate equation, before restricting to section zeros.
  obtain ⟨N, hN, -, -, hA⟩ :=
    exists_mem_nhds_isClosed_isNowhereDense_image_not_surjective_levelSetParameterMap
      hstrict hfn hFred' hsurj hfzero hn' (U := univ) univ_mem
  let Φ := levelSetChart hstrict (LinearMap.range_eq_top.mpr hsurj)
    (hFred'.closedComplemented_ker_coprod hsurj) hfzero
  let g := levelSetParameterMap hstrict hsurj
    (hFred'.closedComplemented_ker_coprod hsurj) hfzero
  let A := g '' (N ∩ {k | ¬ Surjective
    ((fderiv ℝ f ((Φ.symm k : ↥{p | f p = 0}) : X × Λ)).comp
      (ContinuousLinearMap.inl ℝ X Λ))})
  have hΦsource : (⟨(φ x, l), hfzero⟩ : ↥{p | f p = 0}) ∈ Φ.source :=
    mem_levelSetChart_source hstrict _ _ hfzero
  have hΦzero : Φ ⟨(φ x, l), hfzero⟩ = 0 := levelSetChart_apply_self hstrict _ _ hfzero
  have hQ : Φ.source ∩ Φ ⁻¹' N ∈ 𝓝 (⟨(φ x, l), hfzero⟩ : ↥{p | f p = 0}) :=
    inter_mem (Φ.open_source.mem_nhds hΦsource)
      (Φ.continuousAt hΦsource (hΦzero ▸ hN))
  obtain ⟨V, hV, hVsub⟩ := (mem_nhds_subtype _ _ _).mp hQ
  have hne : ((finrank ℝ D₁.ker * finrank ℝ D₁.ker + 1 : ℕ) : ℕ∞ω) ≠ ∞ :=
    (fun m : ℕ ↦ (by simp : (m : ℕ∞ω) ≠ ∞)) _
  have hne0 : ((finrank ℝ D₁.ker * finrank ℝ D₁.ker + 1 : ℕ) : ℕ∞ω) ≠ 0 :=
    (fun m : ℕ ↦ (by simp : ((m + 1 : ℕ) : ℕ∞ω) ≠ 0)) _
  have hdiff : {p | DifferentiableAt ℝ f p} ∈ 𝓝 (φ x, l) := by
    filter_upwards [(hfn.of_le hn').eventually hne] with p hp
    exact hp.differentiableAt hne0
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
  refine ⟨Subtype.val ⁻¹' ((chartAt X x).source ×ˢ univ ∩ b ⁻¹' e.baseSet ∩
      ψ ⁻¹' (V ∩ {p | DifferentiableAt ℝ f p})),
    continuous_subtype_val.continuousAt.preimage_mem_nhds
      (inter_mem (inter_mem hsource hbase) (hψ.preimage_mem_nhds (inter_mem hV hdiff))),
    A, hA, ?_⟩
  rintro ⟨⟨x', k⟩, hw⟩ ⟨⟨⟨hx', -⟩, hwe⟩, hwV, hwd⟩ hbad
  simp only [mem_ofPred_eq] at hw hwe
  have hx'φ : x' ∈ φ.source := by rwa [extChartAt_source]
  have hleft : φ.symm (φ x') = x' := φ.left_inv hx'φ
  let v : ↥{p | f p = 0} := ⟨(φ x', k), hfzero_of hx'φ hwe hw⟩
  have hvV : v ∈ Subtype.val ⁻¹' V := by simpa [v, ψ] using hwV
  have hvQ : v ∈ Φ.source ∩ Φ ⁻¹' N := hVsub hvV
  have hvback : Φ.symm (Φ v) = v := Φ.left_inv hvQ.1
  -- Away from the centre the coordinate derivative is the intrinsic one followed by the
  -- derivative of the inverse chart; so a regular coordinate zero is a regular section zero.
  have hwd' : DifferentiableAt ℝ f (φ x', k) := hwd
  have hfk : HasFDerivAt (fun y ↦ f (y, k)) ((fderiv ℝ f (φ x', k)).comp
      (ContinuousLinearMap.inl ℝ X Λ)) (φ x') :=
    HasFDerivAt.comp (g := f) (φ x') hwd'.hasFDerivAt (hasFDerivAt_prodMk_left (φ x') k)
  have hck : MDifferentiableAt 𝓘(ℝ, X) 𝓘(ℝ, F) (fun y ↦ c (y, k)) x' := by
    refine (hfk.differentiableAt.mdifferentiableAt.comp x'
      (mdifferentiableAt_extChartAt hx')).congr_of_eventuallyEq ?_
    filter_upwards [extChartAt_source_mem_nhds' hx'φ] with y hy
    simp only [comp_apply, f, φ.left_inv hy]
  have hbk : ContinuousAt (fun y ↦ b (y, k)) x' :=
    ContinuousAt.comp (f := fun y ↦ (y, k)) (hb _ hw) (continuousAt_id.prodMk continuousAt_const)
  have hbadcoord : ¬ Surjective ((fderiv ℝ f (φ x', k)).comp
      (ContinuousLinearMap.inl ℝ X Λ)) := by
    intro hcoord
    apply hbad
    refine (surjective_sectionLinearization_iff hbk hwe hck hw).mpr ?_
    have hsymm : MDifferentiableAt 𝓘(ℝ, X) 𝓘(ℝ, X) φ.symm (φ x') := by
      have h := mdifferentiableWithinAt_extChartAt_symm (I := 𝓘(ℝ, X)) (φ.map_source hx'φ)
      rwa [modelWithCornersSelf_coe, range_id, mdifferentiableWithinAt_univ] at h
    have hck' : MDifferentiableAt 𝓘(ℝ, X) 𝓘(ℝ, F) (fun y ↦ c (y, k)) (φ.symm (φ x')) := by
      rwa [hleft]
    have hcomp := mvfderiv_comp (φ x') hck' hsymm
    have hfd : fderiv ℝ ((fun y ↦ c (y, k)) ∘ φ.symm) (φ x') =
        (fderiv ℝ f (φ x', k)).comp (ContinuousLinearMap.inl ℝ X Λ) :=
      hfk.fderiv
    rw [mvfderiv_eq_fderiv, hfd] at hcomp
    have hs : Surjective ((mvfderiv 𝓘(ℝ, X) (fun y ↦ c (y, k)) (φ.symm (φ x'))).comp
        (mfderiv 𝓘(ℝ, X) 𝓘(ℝ, X) φ.symm (φ x'))) := by
      rw [← hcomp, ContinuousLinearMap.coe_comp]
      exact hcoord.comp (NormedSpace.fromTangentSpace (φ x')).surjective
    rw [ContinuousLinearMap.coe_comp] at hs
    have h := hs.of_comp
    rwa [hleft] at h
  refine ⟨Φ v, ⟨hvQ.2, ?_⟩, ?_⟩
  · simp only [mem_ofPred_eq]
    rw [hvback]
    exact hbadcoord
  · exact levelSetParameterMap_levelSetChart hstrict hsurj
      (hFred'.closedComplemented_ker_coprod hsurj) hfzero hvQ.1

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

end TauCeti
