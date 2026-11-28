/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.VectorBundle.Section.CompactSupport.Complexification
public import TauCeti.Analysis.Distribution.TestFunction.PartitionOfUnity
public import TauCeti.Geometry.Manifold.VectorBundle.Density

/-!
# Native compact-test complexification examples

Nonzero chart tests, inverse/fixed-point formulas, strict projection-support containment,
finite, smooth and analytic algebraic orders, empty support, empty and disconnected bases, rank
  zero and the
infinite-dimensional model `C([0,1], ℝ)`. The final example uses the actual real density-valued
Hom bundle, without identifying it with a complex dual-density bundle.
-/

public section
noncomputable section
open Bundle Set TopologicalSpace TauCeti ContMDiffSection
open scoped ContDiff Manifold TensorProduct Topology Distributions TauCeti.Complexification

namespace TauCeti.Examples.CompactSupportComplexification

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- The identity chart on the real line has the required native smoothness. -/
theorem contMDiffOn_refl_real : ContMDiffOn 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ∞
    (OpenPartialHomeomorph.refl ℝ) (OpenPartialHomeomorph.refl ℝ).source :=
  (contMDiffOn_id : ContMDiffOn 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ∞ id
    (OpenPartialHomeomorph.refl ℝ).source).congr
      (by intro x _; simp only [OpenPartialHomeomorph.refl_apply, id_eq])

omit [NormedSpace ℝ F] in
/-- The identity chart lies inside the canonical trivial bundle frame. -/
theorem refl_source_subset_baseSet : (OpenPartialHomeomorph.refl ℝ).source ⊆
    (trivializationAt F (Bundle.Trivial ℝ F) 0).baseSet := by
  intro x _
  simp [Bundle.Trivial.fiberBundle_trivializationAt']

/-- An actual native chart extension in the canonical trivial frame of the real line. -/
def chartSection (φ : 𝓓((⟨(OpenPartialHomeomorph.refl ℝ).target,
    (OpenPartialHomeomorph.refl ℝ).open_target⟩ : Opens ℝ), F)) :
    compactlySupported 𝓘(ℝ, ℝ) F ∞ (Bundle.Trivial ℝ F) :=
  (trivializationAt F (Bundle.Trivial ℝ F) 0).chartTestSection (OpenPartialHomeomorph.refl ℝ)
    contMDiffOn_refl_real refl_source_subset_baseSet φ

/-- The bundled map evaluates by the stated original-fibre formula. -/
@[simp] theorem chartSection_apply (φ : 𝓓((⟨(OpenPartialHomeomorph.refl ℝ).target,
    (OpenPartialHomeomorph.refl ℝ).open_target⟩ : Opens ℝ), F)) (x : ℝ) :
    (chartSection φ).val x = φ x := by
  unfold chartSection
  rw [Trivialization.chartTestSection_apply_of_mem _ _ _ _ _
    (by simp only [OpenPartialHomeomorph.refl_source, mem_univ])]
  simp [Bundle.Trivial.fiberBundle_trivializationAt']

/-- The imaginary chart generator is an actual chart extension, not an assumed
supported section. -/
theorem imaginary_chartSection (φ : 𝓓((⟨(OpenPartialHomeomorph.refl ℝ).target,
    (OpenPartialHomeomorph.refl ℝ).open_target⟩ : Opens ℝ), F)) :
    CompactlySupported.ITmul (n := (⊤ : ℕ∞)) (chartSection φ) =
      (trivializationAt F (Bundle.Trivial ℝ F) 0).complexification.chartTestSection
        (OpenPartialHomeomorph.refl ℝ) contMDiffOn_refl_real
        (by intro x hx; simpa only [Trivialization.baseSet_complexification] using
          (refl_source_subset_baseSet (F := F) hx))
        (TestFunction.postcompCLM
          (Complex.I • (Complexification.ofRealLI F).toContinuousLinearMap) φ) := by
  exact Bundle.Trivialization.ITmul_chartTestSection _ _ _ _ _

/-- A nonzero actual chart test can have zero real projection and strictly smaller projected
support. -/
theorem exists_purely_imaginary_chartTest :
    ∃ φ : 𝓓((⟨(OpenPartialHomeomorph.refl ℝ).target,
    (OpenPartialHomeomorph.refl ℝ).open_target⟩ : Opens ℝ), ℝ),
      φ 0 = 1 ∧ CompactlySupported.realPart (CompactlySupported.ITmul (n := (⊤ : ℕ∞))
        (chartSection φ)) = 0 ∧
      CompactlySupported.ITmul (n := (⊤ : ℕ∞)) (chartSection φ) ≠ 0 ∧
      ContMDiffSection.tsupport (CompactlySupported.realPart (CompactlySupported.ITmul (n := (⊤ :
        ℕ∞)) (chartSection φ))).val ⊂
        ContMDiffSection.tsupport (CompactlySupported.ITmul (n := (⊤ : ℕ∞)) (chartSection φ)).val
          := by
  obtain ⟨φ, -, hφ⟩ := TestFunction.exists_tsupport_subset_apply_eq
    (n := (⊤ : ℕ∞)) (Ω := (⟨(OpenPartialHomeomorph.refl ℝ).target,
    (OpenPartialHomeomorph.refl ℝ).open_target⟩ : Opens ℝ)) (x := 0) (s := univ) (Filter.univ_mem)
      (by simp only [OpenPartialHomeomorph.refl_target]; exact subset_rfl) (1 : ℝ)
  have hs : chartSection φ ≠ 0 := by
    intro h
    have h0 := congrArg (fun s : compactlySupported 𝓘(ℝ, ℝ) ℝ ∞ (Bundle.Trivial ℝ ℝ) ↦ s.val 0) h
    have hval : φ 0 = 0 := by simpa using h0
    exact one_ne_zero (hφ.symm.trans hval)
  have hi : CompactlySupported.ITmul (n := (⊤ : ℕ∞)) (chartSection φ) ≠ 0 := by
    intro h
    apply hs
    have := congrArg (CompactlySupported.imaginaryPart (n := (⊤ : ℕ∞)) (I := 𝓘(ℝ, ℝ)) (F := ℝ) (V
      := Bundle.Trivial ℝ ℝ)) h
    simpa using this
  refine ⟨φ, hφ, CompactlySupported.realPart_ITmul _, hi, ?_⟩
  rw [CompactlySupported.realPart_ITmul]
  have hne : ContMDiffSection.tsupport (CompactlySupported.ITmul (n := (⊤ : ℕ∞)) (chartSection
    φ)).val ≠ ∅ := by
    intro h
    exact hi (Subtype.ext (ContMDiffSection.tsupport_eq_empty_iff.mp h))
  simpa [ContMDiffSection.tsupport_def] using Set.empty_ssubset.mpr (Set.ne_empty_iff_nonempty.mp
    hne)

/-- Algebraic reconstruction gives the nonzero original-fibre value 2+3i. -/
theorem reconstruction_nonzero (φ : 𝓓((⟨(OpenPartialHomeomorph.refl ℝ).target,
    (OpenPartialHomeomorph.refl ℝ).open_target⟩ : Opens ℝ), ℝ)) (hφ : φ 0 = 1) :
    (CompactlySupported.complexificationEquivProd (n := (⊤ : ℕ∞))).symm ((2 : ℝ) • chartSection φ,
      (3 : ℝ) • chartSection φ) ≠ 0 ∧
      ((CompactlySupported.complexificationEquivProd (n := (⊤ : ℕ∞))).symm ((2 : ℝ) • chartSection
        φ, (3 : ℝ) • chartSection φ)).val 0 =
        (1 : ℂ) ⊗ₜ[ℝ] (2 : ℝ) + Complex.I ⊗ₜ[ℝ] (3 : ℝ) := by
  have hv : ((CompactlySupported.complexificationEquivProd (n := (⊤ : ℕ∞)) (I := 𝓘(ℝ, ℝ)) (F := ℝ)
    (V := Bundle.Trivial ℝ ℝ)).symm
      ((2 : ℝ) • chartSection φ, (3 : ℝ) • chartSection φ)).val 0 =
      (1 : ℂ) ⊗ₜ[ℝ] (2 : ℝ) + Complex.I ⊗ₜ[ℝ] (3 : ℝ) := by
    simp only [CompactlySupported.complexificationEquivProd_symm_apply, Submodule.coe_add,
      ContMDiffSection.coe_add,
      Pi.add_apply, CompactlySupported.coe_oneTmul, oneTmulLinearMap_apply,
        CompactlySupported.coe_ITmul, ITmulLinearMap_apply,
        Submodule.coe_smul,
      ContMDiffSection.coe_smul, Pi.smul_apply, chartSection_apply, hφ, smul_eq_mul, mul_one]
  refine ⟨?_, hv⟩
  intro h
  have h0 := congrArg (fun s : compactlySupported 𝓘(ℝ, ℝ) (Complexification ℝ) ∞
      (fun x ↦ ℂ ⊗[ℝ] Bundle.Trivial ℝ ℝ x) ↦ realPart (Bundle.Trivial ℝ ℝ 0) (s.val 0)) h
  rw [hv] at h0
  norm_num only [map_add, realPart_tmul, Complex.one_re, Complex.I_re, zero_smul,
    one_smul, add_zero, Submodule.coe_zero, ContMDiffSection.coe_zero,
    Pi.zero_apply, map_zero] at h0

/-- Empty compact support on a nonempty base is included. -/
theorem supported_empty_real_line :
    supportedIn 𝓘(ℝ, ℝ) ℝ ∞ (Bundle.Trivial ℝ ℝ) (∅ : Set ℝ) = ⊥ :=
  supportedIn_empty

/-- An infinite-dimensional native model; no finite-dimensional fibre hypothesis is inferred. -/
def infiniteModelChartTest (φ : 𝓓((⟨(OpenPartialHomeomorph.refl ℝ).target,
    (OpenPartialHomeomorph.refl ℝ).open_target⟩ : Opens ℝ), C(↥(Icc (0 : ℝ) 1), ℝ))) :=
  CompactlySupported.ITmul (n := (⊤ : ℕ∞)) (chartSection φ)

variable (M : Type*) [TopologicalSpace M] [ChartedSpace ℝ M]
  [T2Space M] [IsManifold 𝓘(ℝ, ℝ) ∞ M]

/-- The native final-topology pair equivalence for the trivial bundle on a real-line manifold. -/
def trivialPairCLE :=
  CompactlySupported.complexificationCLEProd (n := (⊤ : ℕ∞)) (I := 𝓘(ℝ, ℝ)) (V := Bundle.Trivial M
    F)
    (fun x : M ↦ trivializationAt F (Bundle.Trivial M F) x) (fun _ ↦ (⊤ : Opens M))
    (by intro i; simp [Bundle.Trivial.fiberBundle_trivializationAt'])
    (by intro x; exact ⟨x, Set.mem_univ x⟩)

/-- The native fixed-subspace equivalence for the trivial bundle on a real-line manifold. -/
def trivialFixedCLE :=
  CompactlySupported.realPointsConjCLE (n := (⊤ : ℕ∞)) (I := 𝓘(ℝ, ℝ)) (V := Bundle.Trivial M F)
    (fun x : M ↦ trivializationAt F (Bundle.Trivial M F) x) (fun _ ↦ (⊤ : Opens M))
    (by intro i; simp [Bundle.Trivial.fiberBundle_trivializationAt'])
    (by intro x; exact ⟨x, Set.mem_univ x⟩)

/-- The continuous inverse reconstructs a nonzero test with original-fibre value 2+3i. -/
theorem continuous_inverse_nonzero
    (φ : 𝓓((⟨(OpenPartialHomeomorph.refl ℝ).target,
      (OpenPartialHomeomorph.refl ℝ).open_target⟩ : Opens ℝ), ℝ)) (hφ : φ 0 = 1) :
    let _ := compactlySupportedTopology (I := 𝓘(ℝ, ℝ)) (n := ∞)
      (fun x : ℝ ↦ trivializationAt ℝ (Bundle.Trivial ℝ ℝ) x) (fun _ ↦ (⊤ : Opens ℝ))
      (by intro i; simp [Bundle.Trivial.fiberBundle_trivializationAt'])
    let _ := compactlySupportedTopology (I := 𝓘(ℝ, ℝ)) (n := ∞)
      (fun x : ℝ ↦ (trivializationAt ℝ (Bundle.Trivial ℝ ℝ) x).complexification)
      (fun _ ↦ (⊤ : Opens ℝ))
      (by intro i; simp [Bundle.Trivial.fiberBundle_trivializationAt'])
    ((trivialPairCLE (F := ℝ) ℝ).symm
      ((2 : ℝ) • chartSection φ, (3 : ℝ) • chartSection φ)) ≠ 0 ∧
      ((trivialPairCLE (F := ℝ) ℝ).symm
        ((2 : ℝ) • chartSection φ, (3 : ℝ) • chartSection φ)).val 0 =
          (1 : ℂ) ⊗ₜ[ℝ] (2 : ℝ) + Complex.I ⊗ₜ[ℝ] (3 : ℝ) := by
  simpa only [trivialPairCLE, CompactlySupported.complexificationCLEProd_symm_apply] using
    reconstruction_nonzero φ hφ

/-- The native fixed endpoint includes each original real fibre by `1 ⊗ₜ` the original vector. -/
theorem native_fixed_endpoint_apply (φ : compactlySupported 𝓘(ℝ, ℝ) F ∞
    (Bundle.Trivial M F)) (x : M) :
    (trivialFixedCLE (F := F) M φ).val.val x = 1 ⊗ₜ[ℝ] φ.val x := by
  simp only [trivialFixedCLE, CompactlySupported.coe_realPointsConjCLE_apply,
    CompactlySupported.coe_oneTmul, oneTmulLinearMap_apply]

/-- A prescribed nonzero value in the actual infinite-dimensional continuous-function model. -/
theorem infinite_model_nonzero :
    ∃ φ : 𝓓((⟨(OpenPartialHomeomorph.refl ℝ).target,
      (OpenPartialHomeomorph.refl ℝ).open_target⟩ : Opens ℝ), C(↥(Icc (0 : ℝ) 1), ℝ)),
      φ 0 = ContinuousMap.const _ (1 : ℝ) ∧
        CompactlySupported.ITmul (n := (⊤ : ℕ∞)) (chartSection φ) ≠ 0 := by
  obtain ⟨φ, -, hφ⟩ := TestFunction.exists_tsupport_subset_apply_eq
    (n := (⊤ : ℕ∞)) (Ω := (⟨(OpenPartialHomeomorph.refl ℝ).target,
      (OpenPartialHomeomorph.refl ℝ).open_target⟩ : Opens ℝ)) (x := 0) (s := univ)
    Filter.univ_mem (by simp only [OpenPartialHomeomorph.refl_target]; exact subset_rfl)
    (ContinuousMap.const ↥(Icc (0 : ℝ) 1) (1 : ℝ))
  refine ⟨φ, hφ, ?_⟩
  intro h
  have h' := congrArg (CompactlySupported.imaginaryPart (n := (⊤ : ℕ∞)) (I := 𝓘(ℝ, ℝ))
    (F := C(↥(Icc (0 : ℝ) 1), ℝ)) (V := Bundle.Trivial ℝ C(↥(Icc (0 : ℝ) 1), ℝ))) h
  have h0 := congrArg (fun s : compactlySupported 𝓘(ℝ, ℝ) C(↥(Icc (0 : ℝ) 1), ℝ) ∞
      (Bundle.Trivial ℝ C(↥(Icc (0 : ℝ) 1), ℝ)) ↦ s.val 0) h'
  have hv : φ 0 = 0 := by simpa using h0
  have h1 := congrArg (fun f : C(↥(Icc (0 : ℝ) 1), ℝ) ↦ f ⟨0, by norm_num⟩)
    (hφ.symm.trans hv)
  norm_num at h1

/-- A native compact test equals one at `Sum.inl 0` and vanishes on the right component
of `ℝ ⊕ ℝ`. -/
theorem disconnected_nonzero :
    ∃ φ : compactlySupported 𝓘(ℝ, ℝ) ℝ ∞ (Bundle.Trivial (ℝ ⊕ ℝ) ℝ),
      φ.val (Sum.inl 0) = 1 ∧ ∀ x : ℝ, φ.val (Sum.inr x) = 0 := by
  let p : ℝ ⊕ ℝ := Sum.inl 0
  let c := chartAt ℝ p
  let t := trivializationAt ℝ (Bundle.Trivial (ℝ ⊕ ℝ) ℝ) p
  have hp : p ∈ c.source := mem_chart_source ℝ p
  have hct : c.source ⊆ t.baseSet := by
    intro x _
    simp [t, Bundle.Trivial.fiberBundle_trivializationAt']
  obtain ⟨χ, -, hχ⟩ := TestFunction.exists_tsupport_subset_apply_eq
    (n := (⊤ : ℕ∞)) (Ω := ⟨c.target, c.open_target⟩) (x := c p) (s := c.target)
    (c.open_target.mem_nhds (c.map_source hp)) subset_rfl (1 : ℝ)
  let φ := t.chartTestSection c (contMDiffOn_chart (I := 𝓘(ℝ, ℝ))) hct χ
  refine ⟨φ, ?_, ?_⟩
  · rw [Trivialization.chartTestSection_apply_of_mem _ _ _ _ _ hp]
    simp only [hχ, t, Bundle.Trivial.fiberBundle_trivializationAt',
      Bundle.Trivial.symmL_trivialization, ContinuousLinearMap.id_apply]
  · intro x
    apply Trivialization.chartTestSection_apply_of_notMem
    dsimp only [c, p]
    rw [ChartedSpace.sum_chartAt_inl, OpenPartialHomeomorph.lift_openEmbedding_source]
    simp

/-- Every native section on the literal Empty base is zero. -/
theorem emptyBase_sections :
    let _ := ChartedSpace.empty ℝ Empty
    ∀ φ : compactlySupported 𝓘(ℝ, ℝ) ℝ ∞ (Bundle.Trivial Empty ℝ), φ = 0 := by
  let _ := ChartedSpace.empty ℝ Empty
  dsimp only
  intro φ
  apply Subtype.ext
  apply ContMDiffSection.ext
  intro x
  exact Empty.elim x

/-- The actual pair equivalence is defined for the literal Empty base. -/
def emptyBasePair :=
  let _ := ChartedSpace.empty ℝ Empty
  trivialPairCLE (F := ℝ) Empty

/-- Every native section of the rank-zero trivial bundle is zero. -/
theorem rankZero_section (φ : compactlySupported 𝓘(ℝ, ℝ) (Fin 0 → ℝ) ∞
    (Bundle.Trivial ℝ (Fin 0 → ℝ))) : φ = 0 := by
  apply Subtype.ext
  apply ContMDiffSection.ext
  intro x
  exact Subsingleton.elim _ _

/-- The actual native final-topology equivalence includes regularity zero. -/
def finiteZeroPair :=
  CompactlySupported.complexificationCLEProd (n := 0) (I := 𝓘(ℝ, ℝ)) (V := Bundle.Trivial ℝ ℝ)
    (fun x : ℝ ↦ trivializationAt ℝ (Bundle.Trivial ℝ ℝ) x) (fun _ ↦ (⊤ : Opens ℝ))
    (by intro i; simp [Bundle.Trivial.fiberBundle_trivializationAt'])
    (by intro x; exact ⟨x, Set.mem_univ x⟩)

/-- The actual native final-topology equivalence includes finite regularity three. -/
def finiteThreePair :=
  CompactlySupported.complexificationCLEProd (n := 3) (I := 𝓘(ℝ, ℝ)) (V := Bundle.Trivial ℝ ℝ)
    (fun x : ℝ ↦ trivializationAt ℝ (Bundle.Trivial ℝ ℝ) x) (fun _ ↦ (⊤ : Opens ℝ))
    (by intro i; simp [Bundle.Trivial.fiberBundle_trivializationAt'])
    (by intro x; exact ⟨x, Set.mem_univ x⟩)

/-- The actual pair equivalence includes rank-zero fibres. -/
def rankZeroPair := trivialPairCLE (F := (Fin 0 → ℝ)) ℝ

/-- The actual pair equivalence includes disconnected nonempty manifolds. -/
def disconnectedPair := trivialPairCLE (F := ℝ) (ℝ ⊕ ℝ)

/-- The actual pair equivalence includes the model C([0,1],R). -/
def infinitePair := trivialPairCLE (F := C(↥(Icc (0 : ℝ) 1), ℝ)) ℝ

/-- The pair equivalence includes empty compact support on a nonempty real-line base. -/
def emptyCompactPair :=
  SupportedIn.complexificationCLEProd (n := (⊤ : ℕ∞)) (I := 𝓘(ℝ, ℝ)) (V := Bundle.Trivial ℝ ℝ)
    (fun x : ℝ ↦ trivializationAt ℝ (Bundle.Trivial ℝ ℝ) x) (fun _ ↦ (⊤ : Opens ℝ))
    (by intro i; simp [Bundle.Trivial.fiberBundle_trivializationAt'])
    (by intro x; exact ⟨x, Set.mem_univ x⟩) ⊥

/-- The native fixed-subspace endpoint includes empty compact support on a nonempty base. -/
def emptyCompactFixed :=
  SupportedIn.realPointsConjCLE (n := (⊤ : ℕ∞)) (I := 𝓘(ℝ, ℝ)) (V := Bundle.Trivial ℝ ℝ)
    (fun x : ℝ ↦ trivializationAt ℝ (Bundle.Trivial ℝ ℝ) x) (fun _ ↦ (⊤ : Opens ℝ))
    (by intro i; simp [Bundle.Trivial.fiberBundle_trivializationAt'])
    (by intro x; exact ⟨x, Set.mem_univ x⟩) ⊥

/-! ## Analytic-order algebra, without a chosen test topology -/

/-- An actual nonzero analytic test on the compact zero-dimensional real model. -/
def analyticZeroBaseOne :
    compactlySupported 𝓘(ℝ, Fin 0 → ℝ) ℝ ω (Bundle.Trivial (Fin 0 → ℝ) ℝ) := by
  refine ⟨⟨fun _ ↦ 1, ?_⟩, ?_⟩
  · have h : (fun x : Fin 0 → ℝ ↦ TotalSpace.mk' ℝ (E := Bundle.Trivial (Fin 0 → ℝ) ℝ) x (1 : ℝ)) =
        (fun _ ↦ TotalSpace.mk' ℝ (E := Bundle.Trivial (Fin 0 → ℝ) ℝ) (0 : Fin 0 → ℝ) (1 : ℝ)) := by
      funext x
      rw [Subsingleton.elim x 0]
    rw [h]
    exact contMDiff_const
  · rw [compactlySupported_eq_top]
    exact Submodule.mem_top

/-- The analytic constant section evaluates to one in its original real fibre. -/
@[simp] theorem analyticZeroBaseOne_apply (x : Fin 0 → ℝ) :
    analyticZeroBaseOne.val x = 1 := by rfl

/-- Analytic imaginary inclusion is nonzero on an actual compact base. -/
theorem analytic_imaginary_nonzero :
    CompactlySupported.ITmul analyticZeroBaseOne ≠ 0 := by
  intro h
  have hx := congrArg (fun φ ↦ φ.val (0 : Fin 0 → ℝ)) h
  have hz : (Complex.I ⊗ₜ[ℝ] (1 : ℝ)) = 0 := by
    simpa only [CompactlySupported.coe_ITmul, ITmulLinearMap_apply,
      Submodule.coe_zero, ContMDiffSection.coe_zero, Pi.zero_apply,
      analyticZeroBaseOne_apply] using hx
  have hi := congrArg (TauCeti.imaginaryPart ℝ) hz
  simp at hi

/-- Both analytic-order actions have their algebraic square laws, without chart-finality. -/
theorem analytic_compact_actions
    (φ : compactlySupported 𝓘(ℝ, ℝ) (Complexification F) ω
      (fun x : ℝ ↦ ℂ ⊗[ℝ] Bundle.Trivial ℝ F x)) :
    CompactlySupported.conjEquiv (CompactlySupported.conjEquiv φ) = φ ∧
      CompactlySupported.smulIEquiv (CompactlySupported.smulIEquiv φ) = -φ ∧
      (CompactlySupported.conjEquiv φ).val.tsupport = φ.val.tsupport ∧
      (CompactlySupported.smulIEquiv φ).val.tsupport = φ.val.tsupport := by
  simp

/-- Analytic prescribed-support stages permit any support set, including the empty set. -/
theorem analytic_supported_actions (K : Set ℝ)
    (φ : supportedIn 𝓘(ℝ, ℝ) (Complexification F) ω
      (fun x : ℝ ↦ ℂ ⊗[ℝ] Bundle.Trivial ℝ F x) K) :
    SupportedIn.conjEquiv K (SupportedIn.conjEquiv K φ) = φ ∧
      SupportedIn.smulIEquiv K (SupportedIn.smulIEquiv K φ) = -φ ∧
      (SupportedIn.conjEquiv K φ).val.tsupport = φ.val.tsupport ∧
      (SupportedIn.smulIEquiv K φ).val.tsupport = φ.val.tsupport := by
  simp

/-- The original analytic real fixed submodule is available before any test topology. -/
def analyticFixed :=
  CompactlySupported.realPointsConjEquiv (n := ω) (I := 𝓘(ℝ, ℝ))
    (F := F) (V := Bundle.Trivial ℝ F)

/-- The analytic fixed comparison accepts arbitrary support sets, not only compact stages. -/
def analyticSupportedFixed (K : Set ℝ) :=
  SupportedIn.realPointsConjEquiv (n := ω) (I := 𝓘(ℝ, ℝ))
    (F := F) (V := Bundle.Trivial ℝ F) K

/-- An analytic real section with prescribed support in the noncompact set `univ`. -/
def analyticUnboundedOne :
    supportedIn 𝓘(ℝ, ℝ) ℝ ω (Bundle.Trivial ℝ ℝ) Set.univ := by
  refine ⟨⟨fun _ ↦ 1, ?_⟩, mem_supportedIn.mpr (Set.subset_univ _)⟩
  intro x
  rw [Bundle.contMDiffAt_section_iff]
  simpa only [Bundle.Trivial.fiberBundle_trivializationAt',
    Bundle.Trivialization.coe_coe, Bundle.Trivial.trivialization_apply] using
    (contMDiffAt_const : ContMDiffAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ω (fun _ : ℝ ↦ (1 : ℝ)) x)

/-- The arbitrary-support fixed comparison contains the actual nonzero constant section. -/
theorem analytic_unbounded_fixed_value :
    (SupportedIn.realPointsConjEquiv (n := ω) (I := 𝓘(ℝ, ℝ)) (F := ℝ)
      (V := Bundle.Trivial ℝ ℝ) Set.univ analyticUnboundedOne).val.val 0 =
        1 ⊗ₜ[ℝ] (1 : ℝ) := by
  simp only [SupportedIn.coe_realPointsConjEquiv_apply,
    SupportedIn.complexificationEquivProd_symm_apply, Submodule.coe_zero,
    ContMDiffSection.coe_zero, Pi.zero_apply, TensorProduct.tmul_zero, add_zero]
  rfl

/-- The analytic-order fixed endpoint includes empty support on a nonempty base. -/
def analyticEmptySupportFixed :=
  SupportedIn.realPointsConjEquiv (n := ω) (I := 𝓘(ℝ, ℝ))
    (F := F) (V := Bundle.Trivial ℝ F) (⊥ : Compacts ℝ)

section DensityHom

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [T2Space M] [SigmaCompactSpace M] [IsManifold I ∞ M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {V : M → Type*} [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)]
  [TopologicalSpace (TotalSpace F V)] [∀ x, TopologicalSpace (V x)]
  [FiberBundle F V] [VectorBundle ℝ F V] [ContMDiffVectorBundle ∞ F V I]

/-- Actual real density-valued Hom coefficients, without a complex-dual-density identification. -/
def densityHomPair :=
  CompactlySupported.complexificationCLEProd (n := (⊤ : ℕ∞)) (I := I) (F := F →L[ℝ] ℝ)
    (V := fun x ↦ V x →L[ℝ] DensityBundle I M x)
    (fun x : M ↦ trivializationAt (F →L[ℝ] ℝ)
      (fun x ↦ V x →L[ℝ] DensityBundle I M x) x)
    (fun x ↦ ⟨(trivializationAt (F →L[ℝ] ℝ)
      (fun x ↦ V x →L[ℝ] DensityBundle I M x) x).baseSet,
        (trivializationAt (F →L[ℝ] ℝ)
          (fun x ↦ V x →L[ℝ] DensityBundle I M x) x).open_baseSet⟩)
    (fun _ ↦ subset_rfl)
    (fun x ↦ ⟨x, mem_baseSet_trivializationAt (F →L[ℝ] ℝ)
      (fun x ↦ V x →L[ℝ] DensityBundle I M x) x⟩)


end DensityHom

end TauCeti.Examples.CompactSupportComplexification

