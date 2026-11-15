/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Function.LpSpace.Complete
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
public import TauCeti.MeasureTheory.Function.LpSection.Measurable

/-!
# The spaces `Lᵖ` of sections of a vector bundle

Let `E → B` be a topological vector bundle over `𝕜 = ℝ` or `ℂ` with model fibre `F`, whose fibres
carry norms varying continuously over the total space (`TauCeti.ContinuousFiberNorm`), over a
second-countable base with a measure `μ` on its Borel sets. For `1 ≤ p ≤ ∞` the space
`TauCeti.LpSection 𝕜 F E p μ` consists of the a.e.-strongly measurable sections `s`
(`TauCeti.AEStronglyMeasurableSection`) whose fibre norm `x ↦ ‖s x‖` lies in `Lᵖ(μ)`, modulo
equality almost everywhere. With the norm `‖s‖ = ‖x ↦ ‖s x‖‖_{Lᵖ(μ)}`, that is
`(∫ ‖s x‖ ^ p ∂μ) ^ (1 / p)` for finite `p`, it is a normed space.

When the fibres carry inner products (a continuous Riemannian metric for `𝕜 = ℝ`, a continuous
Hermitian metric for `𝕜 = ℂ`), `L²` is an inner product space for `⟪s, t⟫ = ∫ ⟪s x, t x⟫ ∂μ`.
A measurable isometric frame `Φ` (`TauCeti.IsMeasurableIsometricFrame`) identifies `Lᵖ(E, μ)` with
Mathlib's `MeasureTheory.Lp V p μ` by a linear isometry reading sections in the frame
(`TauCeti.IsMeasurableIsometricFrame.lpSectionEquiv`). For a finite-rank bundle such frames exist,
so `Lᵖ(E, μ)` is complete for every measure `μ` (`TauCeti.LpSection.instCompleteSpace`) and `L²`
is a Hilbert space. Finite rank is what supplies completeness here; without an additional
hypothesis it can fail: over a one-point base with a Dirac measure the space is the model fibre
itself, which need not be complete.

The norm and inner product are defined intrinsically, through representatives; neither depends
on a choice of charts or frames.

## Main definitions

* `TauCeti.memLpSections 𝕜 F E p μ`: the submodule of measurable sections with `p`-integrable
  fibre norm.
* `TauCeti.LpSection 𝕜 F E p μ`: its quotient by the sections vanishing almost everywhere, with
  `TauCeti.LpSection.mk` building classes of sections and a coercion choosing representatives.
* `TauCeti.IsMeasurableIsometricFrame.lpSectionEquiv`: the linear isometry
  `LpSection 𝕜 F E p μ ≃ₗᵢ[𝕜] Lp V p μ` given by a measurable isometric frame.

## Main results

* `TauCeti.LpSection.ext_iff`: two classes agree exactly when their representatives agree almost
  everywhere.
* `TauCeti.LpSection.norm_mk_eq_integral`: the norm is `(∫ ‖s x‖ ^ p ∂μ) ^ (1 / p)` for finite
  `p ≠ 0`.
* `TauCeti.LpSection.inner_mk`: the `L²` inner product is `∫ ⟪s x, t x⟫ ∂μ`.
* `TauCeti.LpSection.instCompleteSpace`: completeness in finite rank, for any measure.

## References

* L. I. Nicolaescu, *Lectures on the Geometry of Manifolds*, 3rd ed., §10.2.3
  (Definition 10.2.30 and Proposition 10.2.31).
-/

public section

noncomputable section

open Bundle MeasureTheory Set Filter Module
open scoped Topology InnerProductSpace ENNReal ComplexConjugate

variable {𝕜 B F : Type*} [RCLike 𝕜] [TopologicalSpace B] [MeasurableSpace B]
  [OpensMeasurableSpace B] [SecondCountableTopology B] [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {E : B → Type*} [TopologicalSpace (TotalSpace F E)] {p : ℝ≥0∞} {μ : Measure B}

namespace MeasureTheory.Lp

omit [TopologicalSpace B] [OpensMeasurableSpace B] [SecondCountableTopology B]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F] [TopologicalSpace (TotalSpace F E)] in
/-- Applying a family of linear isometries `Φ x : V ≃ₗᵢ[𝕜] E x` pointwise to an `Lᵖ` function
gives a family of vectors with `p`-integrable norm. -/
theorem memLp_norm_linearIsometryEquiv_apply {V : Type*} [NormedAddCommGroup V] [NormedSpace 𝕜 V]
    [∀ x, NormedAddCommGroup (E x)] [∀ x, NormedSpace 𝕜 (E x)] (g : Lp V p μ)
    (Φ : ∀ x, V ≃ₗᵢ[𝕜] E x) : MemLp (fun x ↦ ‖Φ x (g x)‖) p μ := by
  simpa only [LinearIsometryEquiv.norm_map] using (Lp.memLp g).norm

end MeasureTheory.Lp

namespace TauCeti

section Normed

variable [∀ x, NormedAddCommGroup (E x)] [∀ x, NormedSpace 𝕜 (E x)] [FiberBundle F E]
  [VectorBundle 𝕜 F E] [ContinuousFiberNorm F E] {s t : ∀ x, E x}

variable (𝕜 F E p μ) in
/-- The sections of `E` that are a.e.-strongly measurable for `μ` and whose fibre norm lies in
`Lᵖ(μ)`. -/
def memLpSections : Submodule 𝕜 (∀ x, E x) where
  carrier := {s | AEStronglyMeasurableSection 𝕜 F μ s ∧ MemLp (fun x ↦ ‖s x‖) p μ}
  add_mem' {s t} hs ht := ⟨hs.1.add ht.1, (hs.2.add ht.2).of_le
    (hs.1.add ht.1).aestronglyMeasurable_norm <| .of_forall fun x ↦ by
      simp only [Pi.add_apply, norm_norm]
      rw [Real.norm_of_nonneg (add_nonneg (norm_nonneg _) (norm_nonneg _))]
      exact norm_add_le _ _⟩
  zero_mem' := ⟨.zero 𝕜 F E μ, by simp⟩
  smul_mem' c s hs := ⟨hs.1.const_smul c, (hs.2.const_mul ‖c‖).of_le
    (hs.1.const_smul c).aestronglyMeasurable_norm <| .of_forall fun x ↦ by
      simp [norm_smul]⟩

theorem mem_memLpSections_iff :
    s ∈ memLpSections 𝕜 F E p μ ↔
      AEStronglyMeasurableSection 𝕜 F μ s ∧ MemLp (fun x ↦ ‖s x‖) p μ :=
  Iff.rfl

/-- The fibre norm of a sum of measurable sections with `p`-integrable fibre norms is
`p`-integrable. -/
theorem memLp_norm_add (hs : AEStronglyMeasurableSection 𝕜 F μ s)
    (hsp : MemLp (fun x ↦ ‖s x‖) p μ) (ht : AEStronglyMeasurableSection 𝕜 F μ t)
    (htp : MemLp (fun x ↦ ‖t x‖) p μ) : MemLp (fun x ↦ ‖s x + t x‖) p μ :=
  (mem_memLpSections_iff.1 ((memLpSections 𝕜 F E p μ).add_mem
    (mem_memLpSections_iff.2 ⟨hs, hsp⟩) (mem_memLpSections_iff.2 ⟨ht, htp⟩))).2

omit [TopologicalSpace B] [OpensMeasurableSpace B] [SecondCountableTopology B] in
/-- Scaling a family of vectors with `p`-integrable norms keeps the norms `p`-integrable; no
measurability of the vectors themselves is needed. -/
theorem memLp_norm_smul (c : 𝕜) (hsp : MemLp (fun x ↦ ‖s x‖) p μ) :
    MemLp (fun x ↦ ‖c • s x‖) p μ := by
  simpa only [norm_smul] using hsp.const_mul ‖c‖

theorem memLp_norm_sub (hs : AEStronglyMeasurableSection 𝕜 F μ s)
    (hsp : MemLp (fun x ↦ ‖s x‖) p μ) (ht : AEStronglyMeasurableSection 𝕜 F μ t)
    (htp : MemLp (fun x ↦ ‖t x‖) p μ) : MemLp (fun x ↦ ‖s x - t x‖) p μ :=
  (mem_memLpSections_iff.1 ((memLpSections 𝕜 F E p μ).sub_mem
    (mem_memLpSections_iff.2 ⟨hs, hsp⟩) (mem_memLpSections_iff.2 ⟨ht, htp⟩))).2

variable (𝕜 F E p μ) in
/-- The sections in `memLpSections 𝕜 F E p μ` vanishing `μ`-almost everywhere. -/
def aeZeroSections : Submodule 𝕜 (memLpSections 𝕜 F E p μ) where
  carrier := {s | ∀ᵐ x ∂μ, (s : ∀ x, E x) x = 0}
  add_mem' {s t} hs ht := by
    simp only [Set.mem_ofPred_eq, Submodule.coe_add, Pi.add_apply] at hs ht ⊢
    filter_upwards [hs, ht] with x hsx htx
    rw [hsx, htx, add_zero]
  zero_mem' := by simp
  smul_mem' c s hs := by
    simp only [Set.mem_ofPred_eq, Submodule.coe_smul, Pi.smul_apply] at hs ⊢
    exact hs.mono fun x hx ↦ by rw [hx, smul_zero]

theorem mem_aeZeroSections_iff {s : memLpSections 𝕜 F E p μ} :
    s ∈ aeZeroSections 𝕜 F E p μ ↔ ∀ᵐ x ∂μ, (s : ∀ x, E x) x = 0 := by
  unfold aeZeroSections
  rfl

variable (𝕜 F E p μ) in
/-- The space `Lᵖ(E, μ)` of sections of the vector bundle `E` with model fibre `F`: the
a.e.-strongly measurable sections whose fibre norm lies in `Lᵖ(μ)`, modulo equality
`μ`-almost everywhere. -/
@[expose] def LpSection : Type _ :=
  memLpSections 𝕜 F E p μ ⧸ aeZeroSections 𝕜 F E p μ

namespace LpSection

instance : AddCommGroup (LpSection 𝕜 F E p μ) :=
  Submodule.Quotient.addCommGroup _

instance : Module 𝕜 (LpSection 𝕜 F E p μ) :=
  Submodule.Quotient.module _

/-- The class in `Lᵖ(E, μ)` of an a.e.-strongly measurable section with `p`-integrable fibre
norm. -/
def mk (s : ∀ x, E x) (hs : AEStronglyMeasurableSection 𝕜 F μ s)
    (hsp : MemLp (fun x ↦ ‖s x‖) p μ) : LpSection 𝕜 F E p μ :=
  Submodule.Quotient.mk ⟨s, hs, hsp⟩

/-- A representative section of a class in `Lᵖ(E, μ)`. -/
instance : CoeFun (LpSection 𝕜 F E p μ) (fun _ ↦ ∀ x, E x) :=
  ⟨fun f ↦ (Quotient.out f : memLpSections 𝕜 F E p μ).1⟩

variable (f g : LpSection 𝕜 F E p μ)

theorem aestronglyMeasurableSection : AEStronglyMeasurableSection 𝕜 F μ f :=
  (Quotient.out f : memLpSections 𝕜 F E p μ).2.1

theorem memLp_norm : MemLp (fun x ↦ ‖f x‖) p μ :=
  (Quotient.out f : memLpSections 𝕜 F E p μ).2.2

theorem aestronglyMeasurable_norm : AEStronglyMeasurable (fun x ↦ ‖f x‖) μ :=
  (memLp_norm f).aestronglyMeasurable

@[simp]
theorem mk_coeFn : mk (f : ∀ x, E x) f.aestronglyMeasurableSection f.memLp_norm = f :=
  Quotient.out_eq f

theorem mk_eq_mk_iff {hs : AEStronglyMeasurableSection 𝕜 F μ s}
    {hsp : MemLp (fun x ↦ ‖s x‖) p μ} {ht : AEStronglyMeasurableSection 𝕜 F μ t}
    {htp : MemLp (fun x ↦ ‖t x‖) p μ} :
    mk s hs hsp = mk t ht htp ↔ ∀ᵐ x ∂μ, s x = t x := by
  refine (Submodule.Quotient.eq _).trans ?_
  simp only [mem_aeZeroSections_iff, Submodule.coe_sub, Pi.sub_apply, sub_eq_zero]

/-- Two classes in `Lᵖ(E, μ)` are equal exactly when their representatives agree almost
everywhere. -/
theorem ext_iff : f = g ↔ ∀ᵐ x ∂μ, f x = g x := by
  conv_lhs => rw [← mk_coeFn f, ← mk_coeFn g]
  exact mk_eq_mk_iff

@[ext]
theorem ext (h : ∀ᵐ x ∂μ, f x = g x) : f = g :=
  (ext_iff f g).2 h

/-- The representative of the class of `s` agrees with `s` almost everywhere. -/
theorem coeFn_mk (hs : AEStronglyMeasurableSection 𝕜 F μ s) (hsp : MemLp (fun x ↦ ‖s x‖) p μ) :
    ∀ᵐ x ∂μ, mk s hs hsp x = s x :=
  mk_eq_mk_iff.1 (mk_coeFn (mk s hs hsp))

@[simp]
theorem mk_add (hs : AEStronglyMeasurableSection 𝕜 F μ s) (hsp : MemLp (fun x ↦ ‖s x‖) p μ)
    (ht : AEStronglyMeasurableSection 𝕜 F μ t) (htp : MemLp (fun x ↦ ‖t x‖) p μ) :
    mk s hs hsp + mk t ht htp =
      mk (fun x ↦ s x + t x) (hs.add ht) (memLp_norm_add hs hsp ht htp) :=
  (rfl)

@[simp]
theorem mk_smul (c : 𝕜) (hs : AEStronglyMeasurableSection 𝕜 F μ s)
    (hsp : MemLp (fun x ↦ ‖s x‖) p μ) :
    c • mk s hs hsp = mk (fun x ↦ c • s x) (hs.const_smul c) (memLp_norm_smul c hsp) :=
  (rfl)

@[simp]
theorem mk_zero : mk (0 : ∀ x, E x) (.zero 𝕜 F E μ) (by simp) = (0 : LpSection 𝕜 F E p μ) :=
  (rfl)

@[simp]
theorem mk_neg (hs : AEStronglyMeasurableSection 𝕜 F μ s) (hsp : MemLp (fun x ↦ ‖s x‖) p μ) :
    -mk s hs hsp = mk (fun x ↦ -s x) hs.neg (by simpa only [norm_neg] using hsp) :=
  (rfl)

@[simp]
theorem mk_sub (hs : AEStronglyMeasurableSection 𝕜 F μ s) (hsp : MemLp (fun x ↦ ‖s x‖) p μ)
    (ht : AEStronglyMeasurableSection 𝕜 F μ t) (htp : MemLp (fun x ↦ ‖t x‖) p μ) :
    mk s hs hsp - mk t ht htp =
      mk (fun x ↦ s x - t x) (hs.sub ht) (memLp_norm_sub hs hsp ht htp) :=
  (rfl)

theorem coeFn_add : ∀ᵐ x ∂μ, (f + g) x = f x + g x := by
  have e : f + g = mk (fun x ↦ f x + g x)
      (f.aestronglyMeasurableSection.add g.aestronglyMeasurableSection)
      (memLp_norm_add f.aestronglyMeasurableSection f.memLp_norm g.aestronglyMeasurableSection
        g.memLp_norm) := by
    conv_lhs => rw [← mk_coeFn f, ← mk_coeFn g, mk_add]
  rw [e]
  exact coeFn_mk _ _

theorem coeFn_smul (c : 𝕜) : ∀ᵐ x ∂μ, (c • f) x = c • f x := by
  have e : c • f = mk (fun x ↦ c • f x) (f.aestronglyMeasurableSection.const_smul c)
      (memLp_norm_smul c f.memLp_norm) := by
    conv_lhs => rw [← mk_coeFn f, mk_smul]
  rw [e]
  exact coeFn_mk _ _

theorem coeFn_zero : ∀ᵐ x ∂μ, (0 : LpSection 𝕜 F E p μ) x = 0 := by
  rw [← mk_zero]
  exact coeFn_mk (F := F) _ _

theorem coeFn_neg : ∀ᵐ x ∂μ, (-f) x = -f x := by
  have e : -f = mk (fun x ↦ -f x) f.aestronglyMeasurableSection.neg
      (by simpa only [norm_neg] using f.memLp_norm) := by
    conv_lhs => rw [← mk_coeFn f, mk_neg]
  rw [e]
  exact coeFn_mk _ _

theorem coeFn_sub : ∀ᵐ x ∂μ, (f - g) x = f x - g x := by
  have e : f - g = mk (fun x ↦ f x - g x)
      (f.aestronglyMeasurableSection.sub g.aestronglyMeasurableSection)
      (memLp_norm_sub f.aestronglyMeasurableSection f.memLp_norm g.aestronglyMeasurableSection
        g.memLp_norm) := by
    conv_lhs => rw [← mk_coeFn f, ← mk_coeFn g, mk_sub]
  rw [e]
  exact coeFn_mk _ _

/-- The `Lᵖ` norm of the fibre norm of a representative. -/
instance : Norm (LpSection 𝕜 F E p μ) :=
  ⟨fun f ↦ (eLpNorm (fun x ↦ ‖f x‖) p μ).toReal⟩

theorem norm_def : ‖f‖ = (eLpNorm (fun x ↦ ‖f x‖) p μ).toReal :=
  rfl

@[simp]
theorem norm_mk (hs : AEStronglyMeasurableSection 𝕜 F μ s) (hsp : MemLp (fun x ↦ ‖s x‖) p μ) :
    ‖mk s hs hsp‖ = (eLpNorm (fun x ↦ ‖s x‖) p μ).toReal := by
  rw [norm_def, eLpNorm_congr_ae (g := fun x ↦ ‖s x‖)
    ((coeFn_mk hs hsp).mono fun x hx ↦ by simp only [hx])]

/-- The norm of a class in `Lᵖ(E, μ)` is the `Lp` norm of the fibre norm of a representative. -/
theorem norm_eq_norm_toLp : ‖f‖ = ‖f.memLp_norm.toLp _‖ := by
  rw [Lp.norm_toLp, norm_def]

theorem norm_mk_eq_norm_toLp (hs : AEStronglyMeasurableSection 𝕜 F μ s)
    (hsp : MemLp (fun x ↦ ‖s x‖) p μ) : ‖mk s hs hsp‖ = ‖hsp.toLp _‖ := by
  rw [norm_mk, Lp.norm_toLp]

/-- For finite `p ≠ 0`, the norm in `Lᵖ(E, μ)` is `(∫ ‖s x‖ ^ p ∂μ) ^ (1 / p)`. -/
theorem norm_mk_eq_integral (hp0 : p ≠ 0) (hp : p ≠ ∞) (hs : AEStronglyMeasurableSection 𝕜 F μ s)
    (hsp : MemLp (fun x ↦ ‖s x‖) p μ) :
    ‖mk s hs hsp‖ = (∫ x, ‖s x‖ ^ p.toReal ∂μ) ^ p.toReal⁻¹ := by
  rw [norm_mk, hsp.eLpNorm_eq_integral_rpow_norm hp0 hp, ENNReal.toReal_ofReal (by positivity)]
  simp only [norm_norm]

theorem norm_eq_integral (hp0 : p ≠ 0) (hp : p ≠ ∞) :
    ‖f‖ = (∫ x, ‖f x‖ ^ p.toReal ∂μ) ^ p.toReal⁻¹ := by
  conv_lhs => rw [← mk_coeFn f]
  exact norm_mk_eq_integral hp0 hp _ _

variable [hp : Fact (1 ≤ p)]

instance : NormedAddCommGroup (LpSection 𝕜 F E p μ) :=
  { AddGroupNorm.toNormedAddCommGroup {
  toFun := norm
  map_zero' := by
    rw [norm_def, eLpNorm_congr_ae (g := 0) ((coeFn_zero (𝕜 := 𝕜) (F := F) (E := E)
      (p := p) (μ := μ)).mono fun x hx ↦ by simp [hx])]
    simp
  add_le' f g := by
    simp only [norm_def]
    rw [← ENNReal.toReal_add (memLp_norm f).eLpNorm_ne_top (memLp_norm g).eLpNorm_ne_top]
    refine ENNReal.toReal_mono (ENNReal.add_ne_top.2
      ⟨(memLp_norm f).eLpNorm_ne_top, (memLp_norm g).eLpNorm_ne_top⟩) ?_
    calc eLpNorm (fun x ↦ ‖(f + g) x‖) p μ ≤ eLpNorm (fun x ↦ ‖f x‖ + ‖g x‖) p μ := by
          refine eLpNorm_mono_ae (aestronglyMeasurable_norm _) ?_
          filter_upwards [coeFn_add f g] with x hx
          rw [hx, norm_norm, Real.norm_of_nonneg (by positivity)]
          exact norm_add_le _ _
      _ ≤ _ := eLpNorm_add_le (f := fun x ↦ ‖f x‖) (g := fun x ↦ ‖g x‖) hp.out
  neg' f := by
    simp only [norm_def]
    rw [eLpNorm_congr_ae (g := fun x ↦ ‖f x‖)
      ((coeFn_neg f).mono fun x hx ↦ by simp only [hx, norm_neg])]
  eq_zero_of_map_eq_zero' f hf := by
    rw [norm_def, ENNReal.toReal_eq_zero_iff, or_iff_left (memLp_norm f).eLpNorm_ne_top,
      eLpNorm_eq_zero_iff (zero_lt_one.trans_le hp.out).ne'] at hf
    refine ext _ _ ?_
    filter_upwards [hf, coeFn_zero (𝕜 := 𝕜) (F := F) (E := E) (p := p) (μ := μ)] with x hx h0
    rw [h0]
    simpa using hx } with }

instance : NormedSpace 𝕜 (LpSection 𝕜 F E p μ) where
  norm_smul_le c f := by
    refine le_of_eq ?_
    rw [norm_def, norm_def, eLpNorm_congr_ae (g := ‖c‖ • fun x ↦ ‖f x‖)
      ((coeFn_smul f c).mono fun x hx ↦ by simp [hx, norm_smul]), eLpNorm_const_smul,
      ENNReal.toReal_mul]
    simp

end LpSection

end Normed

section Inner

variable [∀ x, NormedAddCommGroup (E x)] [∀ x, InnerProductSpace 𝕜 (E x)] [FiberBundle F E]
  [VectorBundle 𝕜 F E] [ContinuousFiberNorm F E] {s t : ∀ x, E x}

namespace LpSection

variable (f g h : LpSection 𝕜 F E 2 μ)

/-- The fibre inner product of two `L²` sections is integrable. -/
theorem integrable_inner : Integrable (fun x ↦ ⟪f x, g x⟫_𝕜) μ := by
  refine Integrable.mono' ((memLp_norm f).integrable_mul (memLp_norm g))
    (f.aestronglyMeasurableSection.aestronglyMeasurable_inner g.aestronglyMeasurableSection)
    (.of_forall fun x ↦ norm_inner_le_norm _ _)

/-- The `L²` inner product `⟪s, t⟫ = ∫ ⟪s x, t x⟫ ∂μ`. -/
instance : Inner 𝕜 (LpSection 𝕜 F E 2 μ) :=
  ⟨fun f g ↦ ∫ x, ⟪f x, g x⟫_𝕜 ∂μ⟩

theorem inner_def : ⟪f, g⟫_𝕜 = ∫ x, ⟪f x, g x⟫_𝕜 ∂μ :=
  rfl

@[simp]
theorem inner_mk (hs : AEStronglyMeasurableSection 𝕜 F μ s) (hsp : MemLp (fun x ↦ ‖s x‖) 2 μ)
    (ht : AEStronglyMeasurableSection 𝕜 F μ t) (htp : MemLp (fun x ↦ ‖t x‖) 2 μ) :
    ⟪mk s hs hsp, mk t ht htp⟫_𝕜 = ∫ x, ⟪s x, t x⟫_𝕜 ∂μ := by
  rw [inner_def]
  refine integral_congr_ae ?_
  filter_upwards [coeFn_mk hs hsp, coeFn_mk ht htp] with x hsx htx
  rw [hsx, htx]

/-- The square of the `L²` norm is the integral of the squared fibre norm. -/
theorem norm_sq_eq_integral : ‖f‖ ^ 2 = ∫ x, ‖f x‖ ^ 2 ∂μ := by
  rw [norm_eq_integral f two_ne_zero ENNReal.ofNat_ne_top]
  simp only [ENNReal.toReal_ofNat, Real.rpow_two]
  exact Real.rpow_inv_natCast_pow (n := 2) (integral_nonneg fun _ ↦ by positivity) two_ne_zero

instance : InnerProductSpace 𝕜 (LpSection 𝕜 F E 2 μ) where
  norm_sq_eq_re_inner f := by
    rw [norm_sq_eq_integral, inner_def, ← integral_re (integrable_inner f f)]
    simp only [inner_self_eq_norm_sq]
  conj_inner_symm f g := by
    simp only [inner_def, ← integral_conj, inner_conj_symm]
  add_left f g h := by
    rw [inner_def, inner_def, inner_def, ← integral_add (integrable_inner f h)
      (integrable_inner g h)]
    refine integral_congr_ae ?_
    filter_upwards [coeFn_add f g] with x hx
    rw [hx, inner_add_left]
  smul_left f g c := by
    rw [inner_def, inner_def, ← integral_const_mul]
    refine integral_congr_ae ?_
    filter_upwards [coeFn_smul f c] with x hx
    rw [hx, inner_smul_left]

end LpSection

end Inner

section IsometricFrame

variable [∀ x, NormedAddCommGroup (E x)] [∀ x, NormedSpace 𝕜 (E x)] [FiberBundle F E]
  [VectorBundle 𝕜 F E] [ContinuousFiberNorm F E] {V : Type*} [NormedAddCommGroup V]
  [NormedSpace 𝕜 V] {Φ : ∀ x, V ≃ₗᵢ[𝕜] E x}

namespace IsMeasurableIsometricFrame

variable (hΦ : IsMeasurableIsometricFrame F μ Φ)
include hΦ

theorem memLp_symm_apply (f : LpSection 𝕜 F E p μ) :
    MemLp (fun x ↦ (Φ x).symm (f x)) p μ :=
  (memLp_norm_iff (hΦ.aestronglyMeasurable_symm_apply f.aestronglyMeasurableSection)).1
    (by simpa only [LinearIsometryEquiv.norm_map] using f.memLp_norm)

variable (p) [Fact (1 ≤ p)]

/-- A measurable isometric frame `Φ` identifies `Lᵖ(E, μ)` with `Lᵖ(μ; V)`: a section is sent to
its coordinates `x ↦ (Φ x).symm (s x)` in the frame. -/
def lpSectionEquiv : LpSection 𝕜 F E p μ ≃ₗᵢ[𝕜] Lp V p μ where
  toFun f := (hΦ.memLp_symm_apply f).toLp _
  invFun g := LpSection.mk (fun x ↦ Φ x (g x))
    (hΦ.aestronglyMeasurableSection_apply (Lp.aestronglyMeasurable g))
    (Lp.memLp_norm_linearIsometryEquiv_apply g Φ)
  map_add' f g := by
    rw [← MemLp.toLp_add]
    refine MemLp.toLp_congr _ _ ?_
    filter_upwards [LpSection.coeFn_add f g] with x hx
    simp [hx]
  map_smul' c f := by
    rw [RingHom.id_apply, ← MemLp.toLp_const_smul]
    refine MemLp.toLp_congr _ _ ?_
    filter_upwards [LpSection.coeFn_smul f c] with x hx
    simp [hx]
  left_inv f := by
    refine LpSection.ext _ _ ?_
    filter_upwards [LpSection.coeFn_mk
      (hΦ.aestronglyMeasurableSection_apply (Lp.aestronglyMeasurable _))
      (Lp.memLp_norm_linearIsometryEquiv_apply _ Φ),
      MemLp.coeFn_toLp (hΦ.memLp_symm_apply f)] with x h1 h2
    rw [h1, h2, LinearIsometryEquiv.apply_symm_apply]
  right_inv g := by
    refine Lp.ext ?_
    filter_upwards [MemLp.coeFn_toLp (hΦ.memLp_symm_apply _), LpSection.coeFn_mk
      (hΦ.aestronglyMeasurableSection_apply (Lp.aestronglyMeasurable g))
      (Lp.memLp_norm_linearIsometryEquiv_apply g Φ)] with x h1 h2
    rw [h1, h2, LinearIsometryEquiv.symm_apply_apply]
  norm_map' f := by
    rw [LinearEquiv.coe_mk, LinearMap.coe_mk, AddHom.coe_mk, Lp.norm_toLp, LpSection.norm_def,
      ← eLpNorm_norm _ (hΦ.memLp_symm_apply f).aestronglyMeasurable]
    simp only [LinearIsometryEquiv.norm_map]

theorem coeFn_lpSectionEquiv (f : LpSection 𝕜 F E p μ) :
    ∀ᵐ x ∂μ, hΦ.lpSectionEquiv p f x = (Φ x).symm (f x) :=
  MemLp.coeFn_toLp (hΦ.memLp_symm_apply f)

theorem coeFn_lpSectionEquiv_symm (g : Lp V p μ) :
    ∀ᵐ x ∂μ, (hΦ.lpSectionEquiv p).symm g x = Φ x (g x) :=
  LpSection.coeFn_mk (hΦ.aestronglyMeasurableSection_apply (Lp.aestronglyMeasurable g))
    (Lp.memLp_norm_linearIsometryEquiv_apply g Φ)

end IsMeasurableIsometricFrame

end IsometricFrame

section Complete

variable [∀ x, NormedAddCommGroup (E x)] [∀ x, InnerProductSpace 𝕜 (E x)] [FiberBundle F E]
  [VectorBundle 𝕜 F E] [ContinuousFiberNorm F E]

namespace LpSection

/-- **Completeness.** For a finite-rank bundle with continuous fibre metric over a second-countable
base, `Lᵖ(E, μ)` is complete for every measure `μ` on the Borel sets of the base. -/
instance instCompleteSpace [FiniteDimensional 𝕜 F] [Fact (1 ≤ p)] :
    CompleteSpace (LpSection 𝕜 F E p μ) := by
  obtain ⟨Φ, hΦ⟩ := exists_isMeasurableIsometricFrame F E (EuclideanSpace 𝕜 (Fin (finrank 𝕜 F)))
    (finrank_euclideanSpace_fin)
  exact ((hΦ μ).lpSectionEquiv p).toIsometryEquiv.completeSpace

end LpSection

end Complete

end TauCeti
