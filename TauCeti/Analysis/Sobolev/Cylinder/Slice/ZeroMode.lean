/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.Cylinder.Slice.Average
public import TauCeti.Analysis.Sobolev.GraphStep.Basic
import TauCeti.Analysis.Sobolev.GraphStep.Density
import TauCeti.MeasureTheory.Function.Lp.LinearIsometry

/-!
# The zero mode of the cylinder is the Sobolev space of the line

A section of the trivial bundle over the cylinder `ℝ × S¹` that does not depend on `t` is a map
on the line `ℝ`. This file identifies the zero Fourier mode of the Sobolev space
`W^{1,2}(ℝ × S¹, V)` with the Sobolev space `W^{1,2}(ℝ, V)` of the line, realized as the
weak-derivative graph `TauCeti.WeakDerivStep` over `L²(ℝ, V)`.

* **On `L²`.** Since `[0, 1]` has length one, the first projection `(s, t) ↦ s` carries the strip
  measure to Lebesgue measure on the line
  (`TauCeti.CylinderSobolev.measurePreserving_fst_stripMeasure`), so `f ↦ f ∘ fst` is a linear
  isometry `TauCeti.CylinderSobolev.zeroModeLp : L²(ℝ, V) → L²(ℝ × [0, 1], V)`.
* **On `W^{1,2}`.** A path `ζ ∈ W^{1,2}(ℝ, V)` with weak derivative `ζ'` gives the `L²` jet
  `(ζ ∘ fst, ζ' ∘ fst, 0)` on the strip (`TauCeti.CylinderSobolev.coeFn_zeroModeL`). It lies in
  `W^{1,2}(ℝ × S¹, V)`, because smooth compactly supported paths are dense in `W^{1,2}(ℝ, V)` and
  for those it is the jet of the test section `(s, t) ↦ ζ(s)`. This defines the continuous linear
  map `TauCeti.CylinderSobolev.zeroModeL : W^{1,2}(ℝ, V) → W^{1,2}(ℝ × S¹, V)`, whose value is
  `zeroModeLp` of the value of the path (`TauCeti.CylinderSobolev.valueL_zeroModeL`). It is
  bounded below, `‖ζ‖ ≤ 2 ‖zeroModeL ζ‖`
  (`TauCeti.CylinderSobolev.norm_le_two_mul_norm_zeroModeL`), so it is injective with closed range.
* **Its range is the zero mode.** An element `x` of `W^{1,2}(ℝ × S¹, V)` is its own slice average
  exactly when it lies in the range of `zeroModeL`
  (`TauCeti.CylinderSobolev.sliceAverageL_eq_self_iff`): the slice average of the jet of a test
  section is the jet of a section that does not depend on `t`, and these jets are dense.

Through this identification, a first-order operator on the cylinder whose coefficients do not
depend on `t` restricts on the zero mode to an operator on the line; for the linearized Floer
operator along a time-independent cylinder this is the Morse trajectory operator, in
`TauCeti.Geometry.Symplectic.Floer.TimeIndependent.Sobolev`.

## References

* D. Salamon and E. Zehnder, *Morse theory for periodic solutions of Hamiltonian systems and the
  Maslov index*, Comm. Pure Appl. Math. **45** (1992), 1303–1360, on the zero Fourier mode of the
  linearized operator along time-independent solutions.
-/

public section

noncomputable section

open MeasureTheory Set Filter Topology TopologicalSpace
open scoped ENNReal

namespace TauCeti.CylinderSobolev

open StripSobolev WeakDerivStep

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-! ### Sections pulled back from the line -/

/-- The first projection `(s, t) ↦ s` carries the strip measure on `ℝ × [0, 1]` to Lebesgue
measure on the line, since `[0, 1]` has length one. -/
theorem measurePreserving_fst_stripMeasure :
    MeasurePreserving Prod.fst stripMeasure (volume.restrict ((⊤ : Opens ℝ) : Set ℝ)) := by
  have : IsProbabilityMeasure (volume.restrict (Icc (0 : ℝ) 1)) := ⟨by simp⟩
  rw [StripSobolev.stripMeasure_eq_prod, Opens.coe_top, Measure.restrict_univ]
  exact measurePreserving_fst

variable (V) in
/-- The zero mode of `L²(ℝ × S¹, V)`: a square-integrable map `f` on the line, read as the
section `(s, t) ↦ f(s)` of the cylinder that does not depend on `t`. It is a linear isometry from
`L²(ℝ, V)` into `L²(ℝ × [0, 1], V)`. -/
def zeroModeLp : Lp V 2 (volume.restrict ((⊤ : Opens ℝ) : Set ℝ)) →ₗᵢ[ℝ] Lp V 2 stripMeasure :=
  Lp.compMeasurePreservingₗᵢ ℝ Prod.fst measurePreserving_fst_stripMeasure

/-- The zero mode of `f ∈ L²(ℝ, V)` is represented by `(s, t) ↦ f(s)`. -/
theorem coeFn_zeroModeLp (f : Lp V 2 (volume.restrict ((⊤ : Opens ℝ) : Set ℝ))) :
    zeroModeLp V f =ᵐ[stripMeasure] fun z ↦ f z.1 :=
  Lp.coeFn_compMeasurePreserving f _

/-- An almost everywhere identity on the line holds almost everywhere on the strip for the
sections pulled back along the first projection. -/
private theorem ae_eq_comp_fst {E : Type*} {f g : ℝ → E}
    (h : f =ᵐ[volume.restrict ((⊤ : Opens ℝ) : Set ℝ)] g) :
    (fun z : ℝ × ℝ ↦ f z.1) =ᵐ[stripMeasure] fun z ↦ g z.1 :=
  measurePreserving_fst_stripMeasure.quasiMeasurePreserving.ae_eq_comp h

/-! ### The zero mode of `W^{1,2}` -/

variable [CompleteSpace V] {u : WeakDerivStep volume ⊤ 2
  (ContinuousLinearMap.id ℝ (Lp V 2 (volume.restrict ((⊤ : Opens ℝ) : Set ℝ))))}

/-- The `L²` jet `(ζ ∘ fst, ζ' ∘ fst, 0)` on the strip of a path `ζ` in `W^{1,2}(ℝ, V)`. -/
private def zeroModeJetL :
    WeakDerivStep volume ⊤ 2
        (ContinuousLinearMap.id ℝ (Lp V 2 (volume.restrict ((⊤ : Opens ℝ) : Set ℝ)))) →L[ℝ]
      Lp (V × V × V) 2 stripMeasure :=
  ((ContinuousLinearMap.inl ℝ V (V × V)).compLpL 2 stripMeasure).comp
      ((zeroModeLp V).toContinuousLinearMap.comp (prevL _)) +
    (((ContinuousLinearMap.inr ℝ V (V × V)).comp (ContinuousLinearMap.inl ℝ V V)).compLpL 2
        stripMeasure).comp
      ((zeroModeLp V).toContinuousLinearMap.comp
        (((ContinuousLinearMap.apply ℝ V (1 : ℝ)).compLpL 2 _).comp (weakFDerivL _)))

private theorem coeFn_zeroModeJetL
    (u : WeakDerivStep volume ⊤ 2
      (ContinuousLinearMap.id ℝ (Lp V 2 (volume.restrict ((⊤ : Opens ℝ) : Set ℝ))))) :
    zeroModeJetL u =ᵐ[stripMeasure] fun z ↦ (prev _ u z.1, weakFDeriv _ u z.1 1, 0) := by
  have hd := ae_eq_comp_fst ((ContinuousLinearMap.apply ℝ V (1 : ℝ)).coeFn_compLp
    (weakFDeriv (ContinuousLinearMap.id ℝ _) u))
  simp only [zeroModeJetL, add_apply, ContinuousLinearMap.comp_apply,
    LinearIsometry.coe_toContinuousLinearMap, prevL_apply, weakFDerivL_apply,
    ContinuousLinearMap.compLpL_apply]
  filter_upwards [Lp.coeFn_add (E := V × V × V) (p := 2) (μ := stripMeasure) _ _,
    ContinuousLinearMap.coeFn_compLp (ContinuousLinearMap.inl ℝ V (V × V)) (zeroModeLp V _),
    ContinuousLinearMap.coeFn_compLp
      ((ContinuousLinearMap.inr ℝ V (V × V)).comp (ContinuousLinearMap.inl ℝ V V))
      (zeroModeLp V _),
    coeFn_zeroModeLp (prev _ u), coeFn_zeroModeLp ((ContinuousLinearMap.apply ℝ V (1 : ℝ)).compLp
      (weakFDeriv (ContinuousLinearMap.id ℝ _) u)), hd] with z h₁ h₂ h₃ h₄ h₅ h₆
  rw [h₁, Pi.add_apply, h₂, h₃, h₄, h₅, h₆]
  simp

omit [CompleteSpace V] in
/-- The test section `(s, t) ↦ φ(s)` of a `C²` compactly supported path `φ`. -/
private theorem comp_fst_mem_testSection {φ : ℝ → V} (hφ : ContDiff ℝ 2 φ)
    (hφc : HasCompactSupport φ) : (fun z : ℝ × ℝ ↦ φ z.1) ∈ testSection V := by
  obtain ⟨R, -, hR⟩ := hφc.exists_pos_le_norm
  exact mem_testSection_iff.2 ⟨hφ.comp contDiff_fst, fun _ _ ↦ rfl, R, fun s _ hs ↦
    hR s (by rwa [Real.norm_eq_abs])⟩

omit [CompleteSpace V] in
/-- The jet of the section `(s, t) ↦ φ(s)` is `(φ(s), φ'(s), 0)`. -/
private theorem jet_comp_fst {φ : ℝ → V} (hφ : Differentiable ℝ φ) (z : ℝ × ℝ) :
    jet (fun z : ℝ × ℝ ↦ φ z.1) z = (φ z.1, fderiv ℝ φ z.1 1, 0) := by
  have h : HasFDerivAt (fun z : ℝ × ℝ ↦ φ z.1)
      ((fderiv ℝ φ z.1).comp (ContinuousLinearMap.fst ℝ ℝ ℝ)) z :=
    (hφ z.1).hasFDerivAt.comp z hasFDerivAt_fst
  simp [jet_apply, h.fderiv]

/-- For a path `ζ` represented by a `C²` compactly supported `φ`, the jet `(ζ ∘ fst, ζ' ∘ fst, 0)`
is the jet of the test section `(s, t) ↦ φ(s)`. -/
private theorem zeroModeJetL_eq_jetLp {φ : ℝ → V} (hφ : ContDiff ℝ 2 φ)
    (hφc : HasCompactSupport φ)
    (hu : ⇑(prev _ u) =ᵐ[volume.restrict ((⊤ : Opens ℝ) : Set ℝ)] φ) :
    zeroModeJetL u = jetLp (testSection V) ⟨_, comp_fst_mem_testSection hφ hφc⟩ := by
  have hφ1 : ContDiff ℝ 1 φ := hφ.of_le one_le_two
  have hw := ((hasWeakFDerivOn_base_prev _ u).congr_ae hu).ae_eq_fderiv
    ((hφ1.continuous_fderiv one_ne_zero).locallyIntegrable.locallyIntegrableOn _)
    fun s _ ↦ hφ1.differentiable one_ne_zero s
  refine Lp.ext ?_
  filter_upwards [coeFn_zeroModeJetL u, coeFn_jetLp (S := testSection V)
    ⟨_, comp_fst_mem_testSection hφ hφc⟩, ae_eq_comp_fst hu,
    measurePreserving_fst_stripMeasure.quasiMeasurePreserving.ae_eq_comp hw] with z h₁ h₂ h₃ h₄
  rw [h₁, h₂, jet_comp_fst (hφ1.differentiable one_ne_zero)]
  simp only [Function.comp_apply] at h₄
  simp only [h₃, h₄]

/-- The jet `(ζ ∘ fst, ζ' ∘ fst, 0)` of a path in `W^{1,2}(ℝ, V)` lies in `W^{1,2}(ℝ × S¹, V)`. -/
private theorem zeroModeJetL_mem_H1
    (u : WeakDerivStep volume ⊤ 2
      (ContinuousLinearMap.id ℝ (Lp V 2 (volume.restrict ((⊤ : Opens ℝ) : Set ℝ))))) :
    zeroModeJetL u ∈ H1 V := by
  have hcl : IsClosed {u : WeakDerivStep volume ⊤ 2
      (ContinuousLinearMap.id ℝ (Lp V 2 (volume.restrict ((⊤ : Opens ℝ) : Set ℝ)))) |
      zeroModeJetL u ∈ H1 V} :=
    (isClosed_jetClosure _).preimage zeroModeJetL.continuous
  refine closure_minimal (fun v hv ↦ ?_) hcl
    (dense_setOf_exists_contDiff_hasCompactSupport (E := ℝ) (F := V) (mu := volume)
      ENNReal.ofNat_ne_top u)
  obtain ⟨φ, hφ, hφc, hv⟩ := hv
  simp only [Set.mem_ofPred_eq, zeroModeJetL_eq_jetLp (hφ.of_le (by norm_cast)) hφc hv]
  exact jetLp_mem_jetClosure _

variable (V) in
/-- The zero mode of `W^{1,2}(ℝ × S¹, V)`: a path `ζ` in `W^{1,2}(ℝ, V)` with weak derivative
`ζ'`, read as the element of `W^{1,2}(ℝ × S¹, V)` with `L²` jet `(ζ ∘ fst, ζ' ∘ fst, 0)`, the jet of
the section `(s, t) ↦ ζ(s)` of the cylinder. -/
def zeroModeL :
    WeakDerivStep volume ⊤ 2
        (ContinuousLinearMap.id ℝ (Lp V 2 (volume.restrict ((⊤ : Opens ℝ) : Set ℝ)))) →L[ℝ]
      H1 V :=
  zeroModeJetL.codRestrict (H1 V) zeroModeJetL_mem_H1

/-- The `L²` jet of the zero mode of a path `ζ` is `(ζ ∘ fst, ζ' ∘ fst, 0)`. -/
theorem coeFn_zeroModeL
    (u : WeakDerivStep volume ⊤ 2
      (ContinuousLinearMap.id ℝ (Lp V 2 (volume.restrict ((⊤ : Opens ℝ) : Set ℝ))))) :
    (zeroModeL V u : Lp (V × V × V) 2 stripMeasure) =ᵐ[stripMeasure]
      fun z ↦ (prev _ u z.1, weakFDeriv _ u z.1 1, 0) :=
  coeFn_zeroModeJetL u

/-- For a path represented by a `C²` compactly supported `φ`, the zero mode is the jet of the test
section `(s, t) ↦ φ(s)`. -/
private theorem zeroModeL_eq_jetLp {φ : ℝ → V} (hφ : ContDiff ℝ 2 φ)
    (hφc : HasCompactSupport φ)
    (hu : ⇑(prev _ u) =ᵐ[volume.restrict ((⊤ : Opens ℝ) : Set ℝ)] φ) :
    zeroModeL V u =
      ⟨jetLp (testSection V) ⟨_, comp_fst_mem_testSection hφ hφc⟩, jetLp_mem_jetClosure _⟩ :=
  Subtype.ext (zeroModeJetL_eq_jetLp hφ hφc hu)

/-- The value of the zero mode of a path `ζ` is the zero mode of `ζ` in `L²`. -/
theorem valueL_zeroModeL
    (u : WeakDerivStep volume ⊤ 2
      (ContinuousLinearMap.id ℝ (Lp V 2 (volume.restrict ((⊤ : Opens ℝ) : Set ℝ))))) :
    valueL (zeroModeL V u) = zeroModeLp V (prev _ u) := by
  refine Lp.ext ?_
  filter_upwards [coeFn_valueL (zeroModeL V u), coeFn_zeroModeL u,
    coeFn_zeroModeLp (prev _ u)] with z h₁ h₂ h₃
  rw [h₁, h₂, h₃]

/-- **The zero mode is bounded below.** The `W^{1,2}` norm of a path on the line is at most twice
the `W^{1,2}` norm of its zero mode on the cylinder. -/
theorem norm_le_two_mul_norm_zeroModeL
    (u : WeakDerivStep volume ⊤ 2
      (ContinuousLinearMap.id ℝ (Lp V 2 (volume.restrict ((⊤ : Opens ℝ) : Set ℝ))))) :
    ‖u‖ ≤ 2 * ‖zeroModeL V u‖ := by
  set w := (ContinuousLinearMap.apply ℝ V (1 : ℝ)).compLp
    (weakFDeriv (ContinuousLinearMap.id ℝ _) u)
  have h₁ : ‖prev _ u‖ ≤ ‖zeroModeL V u‖ := by
    rw [← (zeroModeLp V).norm_map, ← Submodule.norm_coe]
    refine Lp.norm_le_norm_of_ae_le ?_
    filter_upwards [coeFn_zeroModeLp (prev _ u), coeFn_zeroModeL u] with z h h'
    rw [h, h']
    exact norm_fst_le ((prev _ u z.1, weakFDeriv _ u z.1 1, 0) : V × V × V)
  have h₂ : ‖weakFDeriv _ u‖ ≤ ‖zeroModeL V u‖ := by
    rw [← ContinuousLinearMap.norm_apply_one_compLp, ← (zeroModeLp V).norm_map,
      ← Submodule.norm_coe]
    refine Lp.norm_le_norm_of_ae_le ?_
    filter_upwards [coeFn_zeroModeLp w, coeFn_zeroModeL u,
      ae_eq_comp_fst ((ContinuousLinearMap.apply ℝ V (1 : ℝ)).coeFn_compLp
        (weakFDeriv (ContinuousLinearMap.id ℝ _) u))] with z h h' h''
    rw [h, h', h'', ContinuousLinearMap.apply_apply]
    exact (norm_fst_le ((weakFDeriv _ u z.1 1, 0) : V × V)).trans
      (norm_snd_le ((prev _ u z.1, weakFDeriv _ u z.1 1, 0) : V × V × V))
  linarith [norm_le_norm_prev_add_norm_weakFDeriv _ u]

/-- The zero mode of `W^{1,2}` is antilipschitz with constant `2`. -/
theorem antilipschitz_zeroModeL : AntilipschitzWith 2 (zeroModeL V) :=
  (zeroModeL V).antilipschitz_of_bound fun u ↦ by
    exact_mod_cast norm_le_two_mul_norm_zeroModeL u

/-- The zero mode of `W^{1,2}` is injective. -/
theorem zeroModeL_injective : Function.Injective (zeroModeL V) :=
  antilipschitz_zeroModeL.injective

/-- The range of the zero mode of `W^{1,2}` is closed. -/
theorem isClosed_range_zeroModeL : IsClosed (range (zeroModeL V)) :=
  antilipschitz_zeroModeL.isClosed_range (zeroModeL V).uniformContinuous

/-! ### The range of the zero mode is the image of the slice average -/

/-- The zero mode of a path does not depend on `t`: it is its own slice average. -/
theorem sliceAverageL_zeroModeL
    (u : WeakDerivStep volume ⊤ 2
      (ContinuousLinearMap.id ℝ (Lp V 2 (volume.restrict ((⊤ : Opens ℝ) : Set ℝ))))) :
    sliceAverageL (zeroModeL V u) = zeroModeL V u := by
  have hcl : IsClosed {u : WeakDerivStep volume ⊤ 2
      (ContinuousLinearMap.id ℝ (Lp V 2 (volume.restrict ((⊤ : Opens ℝ) : Set ℝ)))) |
      sliceAverageL (zeroModeL V u) = zeroModeL V u} :=
    isClosed_eq (sliceAverageL.continuous.comp (zeroModeL V).continuous) (zeroModeL V).continuous
  refine closure_minimal (fun v hv ↦ ?_) hcl
    (dense_setOf_exists_contDiff_hasCompactSupport (E := ℝ) (F := V) (mu := volume)
      ENNReal.ofNat_ne_top u)
  obtain ⟨φ, hφ, hφc, hv⟩ := hv
  have hφ2 : ContDiff ℝ 2 φ := hφ.of_le (by norm_cast)
  simp only [Set.mem_ofPred_eq, zeroModeL_eq_jetLp hφ2 hφc hv, sliceAverageL_jetLp]
  congr 3
  funext z
  simp [sliceAverage_apply]

/-- The slice average of an element of `W^{1,2}(ℝ × S¹, V)` lies in the range of the zero mode. -/
theorem sliceAverageL_mem_range_zeroModeL (x : H1 V) :
    sliceAverageL x ∈ range (zeroModeL V) := by
  have hcl : IsClosed {x : H1 V | sliceAverageL x ∈ range (zeroModeL V)} :=
    isClosed_range_zeroModeL.preimage sliceAverageL.continuous
  refine (denseRange_codRestrict_jetLp (testSection V)).induction_on x hcl fun ξ ↦ ?_
  -- The slice average of the jet of `ξ` is the jet of the section `(s, t) ↦ φ(s)`.
  obtain ⟨hψ, -, R, hR⟩ := mem_testSection_iff.1 (sliceAverage_mem_testSection ξ.property)
  set φ : ℝ → V := fun s ↦ sliceAverage (ξ : ℝ × ℝ → V) (s, 0)
  have hφ : ContDiff ℝ 2 φ := hψ.comp (contDiff_id.prodMk contDiff_const)
  have hφc : HasCompactSupport φ := HasCompactSupport.intro (K := Icc (-|R|) |R|) isCompact_Icc
    fun s hs ↦ hR s 0 (by
      simp only [mem_Icc, not_and_or, not_le] at hs
      rcases hs with hs | hs
      · rw [abs_of_neg (by linarith [abs_nonneg R])]; linarith [le_abs_self R]
      · linarith [le_abs_self R, le_abs_self s])
  have hψφ : sliceAverage (ξ : ℝ × ℝ → V) = fun z ↦ φ z.1 :=
    funext fun z ↦ sliceAverage_mk _ z.1 z.2
  obtain ⟨u, hu, -⟩ := exists_prev_ae_eq_and_weakFDeriv_ae_eq_of_differentiableOn
    (mu := volume) (Omega := ⊤) (p := 2) (fun s _ ↦ hφ.differentiable two_ne_zero s)
    (hφ.continuous.memLp_of_hasCompactSupport hφc)
    ((hφ.continuous_fderiv two_ne_zero).memLp_of_hasCompactSupport (hφc.fderiv (𝕜 := ℝ)))
  refine ⟨u, ?_⟩
  have hξ : (jetLp (testSection V)).codRestrict (H1 V) jetLp_mem_jetClosure ξ =
      ⟨jetLp (testSection V) ξ, jetLp_mem_jetClosure ξ⟩ := rfl
  rw [zeroModeL_eq_jetLp hφ hφc hu, hξ, sliceAverageL_jetLp]
  congr 3
  exact hψφ.symm

/-- **The zero mode is the range of `zeroModeL`.** An element of `W^{1,2}(ℝ × S¹, V)` is its own
slice average, a section that does not depend on `t`, exactly when it is the zero mode of a path
in `W^{1,2}(ℝ, V)`. -/
theorem sliceAverageL_eq_self_iff {x : H1 V} :
    sliceAverageL x = x ↔ x ∈ range (zeroModeL V) := by
  refine ⟨fun h ↦ h ▸ sliceAverageL_mem_range_zeroModeL x, ?_⟩
  rintro ⟨u, rfl⟩
  exact sliceAverageL_zeroModeL u

end TauCeti.CylinderSobolev
