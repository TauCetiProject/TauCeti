/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.VectorBundle.Section.Linearization
public import TauCeti.Analysis.Fredholm.LevelSet.GlobalParametric
import TauCeti.Geometry.Manifold.MFDeriv.ContinuousLinearMap

/-!
# Parametric transversality for Fredholm bundle sections

A section along a map from `X × Λ` to a manifold has regular parameter `l` if its
linearization in the `X` direction is surjective at every zero over `l`. Under
Fredholmness of that partial linearization and surjectivity of the total linearization,
the regular parameters form a residual set, hence a dense set for Banach `Λ`.

Smoothness is required only at zeros. Fredholmness and the finite differentiability
threshold are expressed in the preferred fiber coordinates, while regularity is intrinsic.
The threshold is the current Sard--Smale bound `(dim ker)² + 1`, not the optimal bound.
No norm on the individual bundle fibers is needed.

The proof applies the local parametric theorem for Banach-space equations in fiber
coordinates and takes a countable cover of the actual section zero set. It does not treat
zeros of a coordinate extension outside its trivialization as section zeros.

## References

* D. McDuff, D. Salamon, *J-holomorphic Curves and Symplectic Topology*, 2nd ed.,
  Appendix A.3.
* S. Smale, *An infinite dimensional version of Sard's theorem*, Amer. J. Math.
  87 (1965), 861--866.

The local analytic input is
`TauCeti.exists_mem_nhds_isClosed_isNowhereDense_image_not_surjective_levelSetParameterMap`.
-/

public section

open Bundle Filter Function Module Set
open scoped ContDiff Manifold Topology

namespace TauCeti

variable {X Λ B F EB HB : Type*} {E : B → Type*}
  [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup Λ] [NormedSpace ℝ Λ]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup EB] [NormedSpace ℝ EB]
  [TopologicalSpace HB] {I : ModelWithCorners ℝ EB HB}
  [TopologicalSpace B] [ChartedSpace HB B]
  [∀ a, TopologicalSpace (E a)] [TopologicalSpace (TotalSpace F E)]
  [∀ a, AddCommGroup (E a)] [∀ a, Module ℝ (E a)]
  [FiberBundle F E] [VectorBundle ℝ F E]
  {b : X × Λ → B} {s : ∀ z, E (b z)}

/-- A parameter is regular for a bundle section when the intrinsic linearization in the
`X` direction is surjective at every zero with that parameter. The `X` direction is the image
of `X` in the tangent space at `(x, l)`, identified with `X × Λ` by
`NormedSpace.fromTangentSpace`. Total regularity is a separate condition. -/
def IsRegularSectionParameter (b : X × Λ → B) (s : ∀ z, E (b z)) (l : Λ) : Prop :=
  ∀ x, s (x, l) = 0 → Surjective
    ((sectionLinearization (F := F) 𝓘(ℝ, X × Λ) b s (x, l)).comp
      ((NormedSpace.fromTangentSpace (𝕜 := ℝ) (x, l)).symm.toContinuousLinearMap.comp
        (ContinuousLinearMap.inl ℝ X Λ)))

/-- Characterization of a regular parameter by the partial linearizations at its zeros. -/
theorem isRegularSectionParameter_iff {l : Λ} :
    IsRegularSectionParameter (F := F) b s l ↔
      ∀ x, s (x, l) = 0 → Surjective
        ((sectionLinearization (F := F) 𝓘(ℝ, X × Λ) b s (x, l)).comp
          ((NormedSpace.fromTangentSpace (𝕜 := ℝ) (x, l)).symm.toContinuousLinearMap.comp
            (ContinuousLinearMap.inl ℝ X Λ))) :=
  (Iff.rfl)

/-- In a trivial bundle, section regularity is exactly regularity of the fiber-valued
level equation. -/
@[simp]
theorem isRegularSectionParameter_trivial (b : X × Λ → B) (f : X × Λ → F) (l : Λ) :
    IsRegularSectionParameter (E := Bundle.Trivial B F) (F := F) b f l ↔
      IsRegularParameter f 0 l := by
  simp only [isRegularSectionParameter_iff, isRegularParameter_iff,
    sectionLinearization_trivial, mvfderiv_comp_fromTangentSpace_symm_comp]

variable [CompleteSpace X] [CompleteSpace Λ] [CompleteSpace F]

private theorem exists_section_badParameter_neighborhood {n : ℕ∞ω} {z : X × Λ}
    (hcont : ContMDiffAt 𝓘(ℝ, X × Λ) (I.prod 𝓘(ℝ, F)) n
      (fun w ↦ (⟨b w, s w⟩ : TotalSpace F E)) z)
    (hFred : ContinuousLinearMap.IsFredholm
      ((fderiv ℝ (fun w ↦ (trivializationAt F E (b z) ⟨b w, s w⟩).2) z).comp
        (ContinuousLinearMap.inl ℝ X Λ)))
    (htotal : Surjective (sectionLinearization (F := F) 𝓘(ℝ, X × Λ) b s z))
    (hn : ((finrank ℝ
      ((fderiv ℝ (fun w ↦ (trivializationAt F E (b z) ⟨b w, s w⟩).2) z).comp
        (ContinuousLinearMap.inl ℝ X Λ)).ker ^ 2 + 1 : ℕ) : ℕ∞ω) ≤ n)
    (hz : s z = 0)
    (hb : ∀ w, s w = 0 → ContinuousAt b w) :
    ∃ Q ∈ 𝓝 (⟨z, hz⟩ : ↥{w | s w = 0}), ∃ A : Set Λ, IsNowhereDense A ∧
      ∀ w : ↥{w | s w = 0}, w ∈ Q →
        ¬ Surjective ((sectionLinearization (F := F) 𝓘(ℝ, X × Λ) b s w).comp
          ((NormedSpace.fromTangentSpace (𝕜 := ℝ) (w : X × Λ)).symm.toContinuousLinearMap.comp
            (ContinuousLinearMap.inl ℝ X Λ))) → (w : X × Λ).2 ∈ A := by
  let e := trivializationAt F E (b z)
  let f : X × Λ → F := fun w ↦ (e ⟨b w, s w⟩).2
  let D₁ := (fderiv ℝ f z).comp (ContinuousLinearMap.inl ℝ X Λ)
  let D₂ := (fderiv ℝ f z).comp (ContinuousLinearMap.inr ℝ X Λ)
  have hfn : ContDiffAt ℝ n f z :=
    (contMDiffAt_totalSpace.mp hcont).2.contDiffAt
  have hn0 : n ≠ 0 := by
    intro hzero
    have hpos : (0 : ℕ∞ω) < ((finrank ℝ D₁.ker ^ 2 + 1 : ℕ) : ℕ∞ω) := by simp
    exact not_lt_of_ge (hn.trans_eq hzero) hpos
  have hstrict : HasStrictFDerivAt f (D₁.coprod D₂) z := by
    simpa only [D₁, D₂, ContinuousLinearMap.coprod_comp_inl_inr] using
      hfn.hasStrictFDerivAt hn0
  have he : b z ∈ e.baseSet := mem_baseSet_trivializationAt F E (b z)
  have hsurj : Surjective (D₁.coprod D₂) := by
    rw [ContinuousLinearMap.coprod_comp_inl_inr]
    have h := (surjective_sectionLinearization_iff (hb z hz) he
      (hfn.differentiableAt hn0).mdifferentiableAt hz).mp htotal
    rw [mvfderiv_eq_fderiv, ContinuousLinearMap.coe_comp] at h
    exact h.of_comp
  have hfzero : f z = 0 := by
    dsimp only [f]
    rw [hz]
    exact congrArg Prod.snd (e.zeroSection ℝ he)
  have hn' : ((finrank ℝ D₁.ker * finrank ℝ D₁.ker + 1 : ℕ) : ℕ∞ω) ≤ n := by
    simpa only [pow_two] using hn
  -- Apply local Sard--Smale to the fiber equation, before restricting to actual section zeros.
  obtain ⟨N, hN, -, -, hA⟩ :=
    exists_mem_nhds_isClosed_isNowhereDense_image_not_surjective_levelSetParameterMap
      hstrict hfn hFred hsurj hfzero hn' (U := univ) univ_mem
  let Φ := levelSetChart hstrict (LinearMap.range_eq_top.mpr hsurj)
    (hFred.closedComplemented_ker_coprod hsurj) hfzero
  let g := levelSetParameterMap hstrict hsurj
    (hFred.closedComplemented_ker_coprod hsurj) hfzero
  let A := g '' (N ∩ {k | ¬ Surjective
    ((fderiv ℝ f ((Φ.symm k : ↥{w | f w = 0}) : X × Λ)).comp
      (ContinuousLinearMap.inl ℝ X Λ))})
  have hΦsource : (⟨z, hfzero⟩ : ↥{w | f w = 0}) ∈ Φ.source :=
    mem_levelSetChart_source hstrict _ _ hfzero
  have hΦzero : Φ ⟨z, hfzero⟩ = 0 := levelSetChart_apply_self hstrict _ _ hfzero
  have hQ : Φ.source ∩ Φ ⁻¹' N ∈ 𝓝 (⟨z, hfzero⟩ : ↥{w | f w = 0}) :=
    inter_mem (Φ.open_source.mem_nhds hΦsource)
      (Φ.continuousAt hΦsource (hΦzero ▸ hN))
  obtain ⟨V, hV, hVsub⟩ := (mem_nhds_subtype _ _ _).mp hQ
  have hne : ((finrank ℝ D₁.ker * finrank ℝ D₁.ker + 1 : ℕ) : ℕ∞ω) ≠ ∞ :=
    (fun m : ℕ ↦ (by simp : (m : ℕ∞ω) ≠ ∞)) _
  have hne0 : ((finrank ℝ D₁.ker * finrank ℝ D₁.ker + 1 : ℕ) : ℕ∞ω) ≠ 0 :=
    (fun m : ℕ ↦ (by simp : ((m + 1 : ℕ) : ℕ∞ω) ≠ 0)) _
  have hdiff : {w | DifferentiableAt ℝ f w} ∈ 𝓝 z := by
    filter_upwards [(hfn.of_le hn').eventually hne] with w hw
    exact hw.differentiableAt hne0
  have hbase : b ⁻¹' e.baseSet ∈ 𝓝 z :=
    (hb z hz).preimage_mem_nhds (e.open_baseSet.mem_nhds he)
  -- Restrict to the trivialization's base set: extended coordinate zeros outside it
  -- need not be section zeros. The intrinsic partial linearization is recovered here.
  refine ⟨Subtype.val ⁻¹' (V ∩ b ⁻¹' e.baseSet ∩ {w | DifferentiableAt ℝ f w}),
    continuous_subtype_val.continuousAt.preimage_mem_nhds
      (inter_mem (inter_mem hV hbase) hdiff), A, hA, ?_⟩
  intro w hw hbad
  have hwe : b w ∈ e.baseSet := hw.1.2
  have hwzero : f w = 0 := by
    dsimp only [f]
    rw [w.2]
    exact congrArg Prod.snd (e.zeroSection ℝ hwe)
  let v : ↥{w | f w = 0} := ⟨w, hwzero⟩
  have hvV : v ∈ Subtype.val ⁻¹' V := hw.1.1
  have hvQ := hVsub hvV
  have hvback : Φ.symm (Φ v) = v := Φ.left_inv hvQ.1
  have hbadcoord : ¬ Surjective ((fderiv ℝ f w).comp
      (ContinuousLinearMap.inl ℝ X Λ)) := by
    intro hcoord
    apply hbad
    rw [sectionLinearization_eq_symmL_comp (hb w w.2) hwe hw.2.mdifferentiableAt w.2,
      ContinuousLinearMap.comp_assoc, mvfderiv_comp_fromTangentSpace_symm_comp,
      ← e.symm_continuousLinearEquivAt_eq' hwe]
    exact (e.continuousLinearEquivAt ℝ (b w) hwe).symm.surjective.comp hcoord
  refine ⟨Φ v, ⟨hvQ.2, ?_⟩, ?_⟩
  · simp only [Set.mem_ofPred_eq]
    rw [hvback]
    exact hbadcoord
  · exact levelSetParameterMap_levelSetChart hstrict hsurj
      (hFred.closedComplemented_ker_coprod hsurj) hfzero hvQ.1

variable [SecondCountableTopology ↥{z | s z = 0}] {n : ℕ∞ω}
    (hcont : ∀ z, s z = 0 → ContMDiffAt 𝓘(ℝ, X × Λ) (I.prod 𝓘(ℝ, F)) n
      (fun w ↦ (⟨b w, s w⟩ : TotalSpace F E)) z)
    (hFred : ∀ z, s z = 0 → ContinuousLinearMap.IsFredholm
      ((fderiv ℝ (fun w ↦ (trivializationAt F E (b z) ⟨b w, s w⟩).2) z).comp
        (ContinuousLinearMap.inl ℝ X Λ)))
    (htotal : ∀ z, s z = 0 →
      Surjective (sectionLinearization (F := F) 𝓘(ℝ, X × Λ) b s z))
    (hn : ∀ z, s z = 0 → ((finrank ℝ
      ((fderiv ℝ (fun w ↦ (trivializationAt F E (b z) ⟨b w, s w⟩).2) z).comp
        (ContinuousLinearMap.inl ℝ X Λ)).ker ^ 2 + 1 : ℕ) : ℕ∞ω) ≤ n)

include hcont hFred htotal hn

/-- **Parametric transversality for bundle sections.** Non-regular parameters are meagre
when the total linearization is surjective and its `X` part is Fredholm at every zero.
The partial Fredholm hypothesis and smoothness threshold are checked in preferred fiber
coordinates. Second countability is needed only for the actual universal zero set. -/
theorem isMeagre_setOf_not_isRegularSectionParameter :
    IsMeagre {l | ¬ IsRegularSectionParameter (F := F) b s l} := by
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
    have hl' : ¬ IsRegularSectionParameter (F := F) b s l := hl
    rw [isRegularSectionParameter_iff] at hl'
    push Not at hl'
    obtain ⟨x, hx, hbad⟩ := hl'
    let w : ↥{z | s z = 0} := ⟨(x, l), hx⟩
    obtain ⟨z, hzt, hwQ⟩ := mem_iUnion₂.mp (htcover (mem_univ w))
    exact mem_iUnion₂.mpr ⟨z, hzt, hQA z w hwQ hbad⟩
  · exact isMeagre_biUnion htcount fun z _ ↦ (hA z).isMeagre

/-- Regular parameters of a universal Fredholm bundle section form a residual set. -/
theorem mem_residual_setOf_isRegularSectionParameter :
    {l | IsRegularSectionParameter (F := F) b s l} ∈ residual Λ := by
  simpa only [IsMeagre, Set.compl_ofPred, Classical.not_not] using
    isMeagre_setOf_not_isRegularSectionParameter hcont hFred htotal hn

/-- Regular parameters of a universal Fredholm bundle section are dense in the Banach
parameter space. -/
theorem dense_setOf_isRegularSectionParameter :
    Dense {l | IsRegularSectionParameter (F := F) b s l} :=
  dense_of_mem_residual
    (mem_residual_setOf_isRegularSectionParameter hcont hFred htotal hn)

end TauCeti
