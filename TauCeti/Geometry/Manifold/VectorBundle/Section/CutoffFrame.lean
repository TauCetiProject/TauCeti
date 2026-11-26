/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Distribution.TestFunction.Schwartz
public import TauCeti.Geometry.Manifold.ContMDiffMap.Basic
public import TauCeti.Geometry.Manifold.DifferentialOperator.ChartCompression.Basic
public import TauCeti.Geometry.Manifold.VectorBundle.Section.ComplexModule
public import TauCeti.Geometry.Manifold.VectorBundle.Section.TestFunction
import TauCeti.Geometry.Manifold.ContMDiffMap.Extension
import TauCeti.Geometry.Manifold.PartitionOfUnity.Compact

/-!
# Cut-off frames of a vector bundle

A trivialization `t` of a smooth vector bundle `V → M` gives a frame of `V` only over its base set.
Multiplying by a smooth function `ψ` supported in the base set turns it into global data:

* the **cut-off frame section** `x ↦ ψ(x) t⁻¹ₓ v` of `V`, for a vector `v` of the model fibre
  (`Bundle.Trivialization.cutoffFrameSection`), is a smooth section of `V` on all of `M`;
* for a complex bundle over a real manifold, the **cut-off frame coefficient**
  `x ↦ χ(x) ℓ(tₓ (h x))` of a smooth section `h`, for a complex-linear functional `ℓ` on the model
  fibre (`Bundle.Trivialization.cutoffFrameCoeff`), is a smooth complex-valued function on `M`,
  complex-linear in `h`.

For a basis `(bᵢ)` of the model fibre and `ψ = 1` on the support of `ρ`, the cut-off frame sections
`ψ t⁻¹ bᵢ` with the coefficients `ρ bᵢ*(t h)` add up to `ρ h`
(`Bundle.Trivialization.sum_cutoffFrameCoeff_smul_cutoffFrameSection_apply`). Over a compact set
`K` finitely many trivializations and a partition of unity then write every section as a finite
sum of cut-off frame sections with cut-off frame coefficients
(`IsCompact.exists_sum_sum_cutoffFrameCoeff_smul_cutoffFrameSection_apply`). This is how an
operator out of the sections of a bundle is split into its matrix entries near `K`.

These read operators between sections of bundles as matrices of operators on functions, without
restricting to the base set of a trivialization: the entries of an operator `P` are the operators
`f ↦ χ ℓ(t' (P (f ψ t⁻¹ v)))` on functions on `M`.

Conversely, cut-off frames recover sections: if `tᵢ` are finitely many trivializations, `gᵢ`
functions supported in their base sets with `∑ᵢ gᵢ² = 1` wherever a section `h` does not vanish,
and `(bⱼ)` a basis of the model fibre, then `h = ∑ᵢ ∑ⱼ gᵢ bⱼ*(tᵢ h) · gᵢ tᵢ⁻¹ bⱼ`
(`ContMDiffSection.eq_sum_cutoffFrameCoeff_smul_cutoffFrameSection`). This is what composes the
matrices of two operators.

Cut-off frames also change frames. Where a cutoff `ρ` equals `1` inside the base set of a second
trivialization `t₀`, a cut-off frame coefficient is a combination of the coefficients in `t₀`
(`Bundle.Trivialization.cutoffFrameCoeff_apply_eq_sum`). For a cutoff `θ` supported where `ρ = 1`,
every section `s` is `∑ᵢ θ ρ bᵢ*(t₀ s) ρ t₀⁻¹ bᵢ + (1 - θ) s`
(`Bundle.Trivialization.smul_eq_sum_smul_cutoffFrameSection_add`).

In a chart `e` whose source lies in the base set of `t`, a Schwartz function `u` on the model space
and a cutoff `ψ` with compact support in the chart target give the **chart cut-off section**
`x ↦ t⁻¹ₓ (ψ(e x) u(e x))` (`Bundle.Trivialization.chartCutoffSection`), on which chart
compressions of operators between bundles are evaluated. In terms of cut-off frames, it is the sum
of the cut-off frame sections `ρ t⁻¹ bᵢ` with the pulled back coefficients `(ψ bᵢ*(u)) ∘ e`
(`Bundle.Trivialization.chartCutoffSection_eq_sum`). Likewise, a section `u` multiplied by a
function `Ψ` is the sum of the cut-off frame sections `ρ t⁻¹ bᵢ` with the coefficients
`Ψ · ρ bᵢ*(t u)`, when `ρ = 1` wherever `Ψ ≠ 0`
(`Bundle.Trivialization.smul_eq_sum_cutoffFrameCoeff_smul_cutoffFrameSection`).

On a compact manifold, finitely many chart cutoffs `ψᵢ` whose pullbacks add up to `1` can be
chosen with each `(chartAt cᵢ)⁻¹(supp ψᵢ)` inside the base set of the trivialization at `cᵢ`,
together with smooth functions `ρᵢ` supported in these base sets and equal to `1` on
`(chartAt cᵢ)⁻¹(supp ψᵢ)` (`TauCeti.exists_sum_cutoffPullback_eq_one_and_baseSet_cutoff`). These
are the data through which sections of a bundle are read in charts and frames, as in Sobolev
norms of sections on a compact manifold.
-/

public section

noncomputable section

open Bundle Set
open scoped ContDiff Distributions Manifold SchwartzMap Topology

universe u

namespace Bundle.Trivialization

section Section

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {EM : Type*} [NormedAddCommGroup EM]
  [NormedSpace 𝕜 EM] {HM : Type*} [TopologicalSpace HM] {I : ModelWithCorners 𝕜 EM HM}
  {M : Type*} [TopologicalSpace M] [ChartedSpace HM M] {n : ℕ∞ω}
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {V : M → Type*} [TopologicalSpace (TotalSpace F V)] [∀ x, AddCommGroup (V x)]
  [∀ x, Module 𝕜 (V x)] [∀ x, TopologicalSpace (V x)] [FiberBundle F V] [VectorBundle 𝕜 F V]
  [ContMDiffVectorBundle n F V I]
  (t : Trivialization F (π F V)) [MemTrivializationAtlas t]

/-- The **cut-off frame section** `x ↦ ψ(x) t⁻¹ₓ v` of `V`, for a trivialization `t` of `V` in its
atlas, a `C^n` function `ψ` whose support lies in the base set of `t` and a vector `v` of the model
fibre. It is a `C^n` section of `V` on all of `M`, vanishing outside the support of `ψ`. -/
def cutoffFrameSection (ψ : C^n⟮I, M; 𝕜⟯) (hψ : tsupport ψ ⊆ t.baseSet) (v : F) :
    Cₛ^n⟮I; F, V⟯ where
  toFun x := ψ x • t.symm x v
  contMDiff_toFun := by
    refine ContMDiffOn.smul_section_of_tsupport ψ.contMDiff.contMDiffOn t.open_baseSet hψ ?_
    refine (contMDiffOn_section_iff t t.open_baseSet subset_rfl).2 ?_
    exact contMDiffOn_const.congr fun x hx ↦ by rw [t.apply_mk_symm hx]

@[simp]
theorem cutoffFrameSection_apply (ψ : C^n⟮I, M; 𝕜⟯) (hψ : tsupport ψ ⊆ t.baseSet) (v : F)
    (x : M) : t.cutoffFrameSection ψ hψ v x = ψ x • t.symm x v :=
  (rfl)

end Section

section Coeff

variable {EM : Type*} [NormedAddCommGroup EM] [NormedSpace ℝ EM] {HM : Type*} [TopologicalSpace HM]
  {I : ModelWithCorners ℝ EM HM} {M : Type*} [TopologicalSpace M] [ChartedSpace HM M] {n : ℕ∞ω}
  {W : Type*} [NormedAddCommGroup W] [NormedSpace ℂ W]
  {F : M → Type*} [TopologicalSpace (TotalSpace W F)] [∀ x, AddCommGroup (F x)]
  [∀ x, Module ℝ (F x)] [∀ x, Module ℂ (F x)] [∀ x, TopologicalSpace (F x)] [FiberBundle W F]
  [VectorBundle ℝ W F] [VectorBundle ℂ W F] [ContMDiffVectorBundle n W F I]
  (t : Trivialization W (π W F)) [MemTrivializationAtlas t]

/-- The cut-off frame coefficients `χ(x) ℓ(tₓ (h x))` of a `C^n` section `h` are `C^n`. -/
private theorem contMDiff_cutoffFrameCoeffFun (χ : C^n⟮I, M; ℝ⟯) (hχ : tsupport χ ⊆ t.baseSet)
    (ℓ : W →L[ℂ] ℂ) (h : Cₛ^n⟮I; W, F⟯) :
    ContMDiff I 𝓘(ℝ, ℂ) n fun x ↦ χ x • ℓ (t.continuousLinearMapAt ℂ x (h x)) := by
  refine ContMDiffOn.contMDiff_smul_of_tsupport_subset ?_ t.open_baseSet
    χ.contMDiff.contMDiffOn hχ
  have hs := (contMDiffOn_section_iff t t.open_baseSet subset_rfl).1 h.contMDiff.contMDiffOn
  refine ((ℓ.restrictScalars ℝ).contMDiff.comp_contMDiffOn hs).congr fun x hx ↦ ?_
  simp [continuousLinearMapAt_apply_of_mem ℂ t hx]

/-- The cut-off frame coefficients `χ(x) ℓ(tₓ (h x))` of a `C^n` section `h`, as a `C^n`
function. -/
private def cutoffFrameCoeffFun (χ : C^n⟮I, M; ℝ⟯) (hχ : tsupport χ ⊆ t.baseSet) (ℓ : W →L[ℂ] ℂ)
    (h : Cₛ^n⟮I; W, F⟯) : C^n⟮I, M; 𝓘(ℝ, ℂ), ℂ⟯ :=
  ⟨_, contMDiff_cutoffFrameCoeffFun t χ hχ ℓ h⟩

private theorem cutoffFrameCoeffFun_apply (χ : C^n⟮I, M; ℝ⟯) (hχ : tsupport χ ⊆ t.baseSet)
    (ℓ : W →L[ℂ] ℂ) (h : Cₛ^n⟮I; W, F⟯) (x : M) :
    cutoffFrameCoeffFun t χ hχ ℓ h x = χ x • ℓ (t.continuousLinearMapAt ℂ x (h x)) :=
  (rfl)

/-- The **cut-off frame coefficient** `x ↦ χ(x) ℓ(tₓ (h x))` of a section `h` of a complex vector
bundle `F` over a real manifold, for a trivialization `t` of `F` in its atlas, a real `C^n`
function `χ` whose support lies in the base set of `t` and a complex-linear functional `ℓ` on the
model fibre, as a complex-linear map from the `C^n` sections of `F` to the complex-valued `C^n`
functions. -/
def cutoffFrameCoeff (χ : C^n⟮I, M; ℝ⟯) (hχ : tsupport χ ⊆ t.baseSet) (ℓ : W →L[ℂ] ℂ) :
    Cₛ^n⟮I; W, F⟯ →ₗ[ℂ] C^n⟮I, M; 𝓘(ℝ, ℂ), ℂ⟯ where
  toFun := cutoffFrameCoeffFun t χ hχ ℓ
  map_add' g h := by
    ext x
    simp [cutoffFrameCoeffFun_apply, smul_add]
  map_smul' c h := by
    ext x
    simp only [cutoffFrameCoeffFun_apply, ContMDiffMap.complex_smul_apply,
      ContMDiffSection.coe_smul_of_normedAlgebra, Pi.smul_apply, map_smul, Complex.real_smul,
      smul_eq_mul, RingHom.id_apply]
    ring

@[simp]
theorem cutoffFrameCoeff_apply (χ : C^n⟮I, M; ℝ⟯) (hχ : tsupport χ ⊆ t.baseSet) (ℓ : W →L[ℂ] ℂ)
    (h : Cₛ^n⟮I; W, F⟯) (x : M) :
    t.cutoffFrameCoeff χ hχ ℓ h x = χ x • ℓ (t.continuousLinearMapAt ℂ x (h x)) :=
  (rfl)

/-- The cut-off frame coefficients are linear over the complex-valued functions: the coefficient
of `g • h` is `g` times that of `h`. -/
theorem cutoffFrameCoeff_smul_function (χ : C^n⟮I, M; ℝ⟯) (hχ : tsupport χ ⊆ t.baseSet)
    (ℓ : W →L[ℂ] ℂ) (g : C^n⟮I, M; 𝓘(ℝ, ℂ), ℂ⟯) (h : Cₛ^n⟮I; W, F⟯) :
    t.cutoffFrameCoeff χ hχ ℓ (g • h) = g * t.cutoffFrameCoeff χ hχ ℓ h := by
  ext x
  simp only [cutoffFrameCoeff_apply, ContMDiffSection.smul_apply_of_normedAlgebra, map_smul,
    smul_eq_mul, ContMDiffMap.coe_mul, Pi.mul_apply, Complex.real_smul]
  ring

/-- On the base set of `t`, a real cut-off frame section `g t⁻¹ v` is the complex-linear inverse
`t⁻¹ₓ` applied to `(g x : ℂ) • v`. -/
theorem cutoffFrameSection_apply_eq_symmL (g : C^n⟮I, M; ℝ⟯) (hg : tsupport g ⊆ t.baseSet) (v : W)
    {x : M} (hx : x ∈ t.baseSet) :
    t.cutoffFrameSection g hg v x = t.symmL ℂ x ((g x : ℂ) • v) := by
  rw [cutoffFrameSection_apply, ← t.symmL_apply (R := ℝ) hx, ← map_smul, ← Complex.coe_smul,
    t.symmL_apply (R := ℝ) hx, t.symmL_apply (R := ℂ) hx]

/-- In one trivialization `t`, with the same function `g` cutting off the frame and the
coefficients, the cut-off frame sections `g t⁻¹ bⱼ` multiplied by the cut-off frame coefficients
`g bⱼ*(t h)` add up to `g² h`. -/
private theorem sum_cutoffFrameCoeff_smul_cutoffFrameSection_apply_sq [FiniteDimensional ℂ W]
    (g : C^n⟮I, M; ℝ⟯) (hg : tsupport g ⊆ t.baseSet) {κ : Type*} [Fintype κ]
    (b : Module.Basis κ ℂ W) (h : Cₛ^n⟮I; W, F⟯) (x : M) :
    ∑ j, t.cutoffFrameCoeff g hg (b.coord j).toContinuousLinearMap h x •
      t.cutoffFrameSection g hg (b j) x = ((g x ^ 2 : ℝ) : ℂ) • h x := by
  by_cases hx : x ∈ t.baseSet
  · -- On the base set, `t⁻¹ₓ` is linear over `ℝ` and over `ℂ`, and the real and complex actions
    -- of `g x` on the model fibre agree, so each term is `t⁻¹ₓ (g x ^ 2 • bⱼ*(tₓ h) • bⱼ)`.
    have hterm (j : κ) : t.cutoffFrameCoeff g hg (b.coord j).toContinuousLinearMap h x •
        t.cutoffFrameSection g hg (b j) x = t.symmL ℂ x (((g x ^ 2 : ℝ) : ℂ) •
          (b.coord j).toContinuousLinearMap (t.continuousLinearMapAt ℂ x (h x)) • b j) := by
      rw [cutoffFrameCoeff_apply, t.cutoffFrameSection_apply_eq_symmL g hg _ hx, ← map_smul]
      congr 1
      simp only [smul_smul, Complex.real_smul, Complex.ofReal_pow]
      congr 1
      ring
    rw [Finset.sum_congr rfl fun j _ ↦ hterm j, ← map_sum, ← Finset.smul_sum]
    simp only [LinearMap.coe_toContinuousLinearMap', Module.Basis.coord_apply, b.sum_repr,
      map_smul, t.symmL_continuousLinearMapAt hx]
  · have hgx : g x = 0 := image_eq_zero_of_notMem_tsupport fun h ↦ hx (hg h)
    simp [hgx]


/-- **A section in a cut-off frame.** Let `ρ` be a real `C^n` function supported in the base set of
`t`, `ψ` one supported there and equal to `1` on the support of `ρ`, and `(bᵢ)` a basis of the
model fibre `W` with coordinate functionals `bᵢ*`. For every `C^n` section `h` of `F`, the cut-off
frame sections `ψ t⁻¹ bᵢ` multiplied by the cut-off frame coefficients `ρ bᵢ*(t h)` add up to
`ρ h`. -/
theorem sum_cutoffFrameCoeff_smul_cutoffFrameSection_apply [FiniteDimensional ℂ W]
    (ρ : C^n⟮I, M; ℝ⟯) (hρ : tsupport ρ ⊆ t.baseSet) (ψ : C^n⟮I, M; ℝ⟯)
    (hψ : tsupport ψ ⊆ t.baseSet) (hψρ : ∀ x ∈ tsupport ρ, ψ x = 1) {ι : Type*} [Fintype ι]
    (b : Module.Basis ι ℂ W) (h : Cₛ^n⟮I; W, F⟯) (x : M) :
    (∑ i, t.cutoffFrameCoeff ρ hρ (b.coord i).toContinuousLinearMap h •
      t.cutoffFrameSection ψ hψ (b i)) x = (ρ x : ℂ) • h x := by
  rw [ContMDiffSection.coe_sum, Finset.sum_apply]
  by_cases hx : ρ x = 0
  · simp [hx]
  have hxt : x ∈ t.baseSet := hρ (subset_tsupport _ hx)
  conv_rhs => rw [← t.symmL_continuousLinearMapAt (R := ℂ) hxt (h x),
    ← b.sum_repr (t.continuousLinearMapAt ℂ x (h x)), map_sum, Finset.smul_sum]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  simp [hψρ x (subset_tsupport _ hx), ← t.symmL_apply (R := ℂ) hxt, mul_smul, Complex.real_smul]

/-- **A cut-off frame coefficient in another frame.** Let `(bⱼ)` be a basis of the model fibre
with coordinate functionals `bⱼ*`, and `ρ` a cutoff supported in the base set of a trivialization
`t₀`. At a point `y` of the base set of `t₀` where `ρ y = 1`, the cut-off frame coefficient
`χ ℓ(t h)` of a section `h` is the combination of its coefficients `ρ bⱼ*(t₀ h)` in `t₀` with the
coefficients `χ ℓ(t ρ t₀⁻¹ bⱼ)` of the cut-off frame sections of `t₀`. -/
theorem cutoffFrameCoeff_apply_eq_sum [FiniteDimensional ℂ W] (χ : C^n⟮I, M; ℝ⟯)
    (hχ : tsupport χ ⊆ t.baseSet) (ℓ : W →L[ℂ] ℂ) (t₀ : Trivialization W (π W F))
    [MemTrivializationAtlas t₀] (ρ : C^n⟮I, M; ℝ⟯) (hρ : tsupport ρ ⊆ t₀.baseSet) {ι : Type*}
    [Fintype ι] (b : Module.Basis ι ℂ W) {y : M} (hy : y ∈ t₀.baseSet) (hρy : ρ y = 1)
    (h : Cₛ^n⟮I; W, F⟯) :
    t.cutoffFrameCoeff χ hχ ℓ h y = ∑ j, t.cutoffFrameCoeff χ hχ ℓ
      (t₀.cutoffFrameSection ρ hρ (b j)) y *
        t₀.cutoffFrameCoeff ρ hρ (b.coord j).toContinuousLinearMap h y := by
  simp only [cutoffFrameCoeff_apply, cutoffFrameSection_apply, hρy, one_smul]
  conv_lhs => rw [← t₀.sum_repr_smul_symmL b hy (h y)]
  simp only [map_sum, map_smul, Finset.smul_sum, t₀.symmL_apply hy,
    LinearMap.coe_toContinuousLinearMap', smul_eq_mul, Complex.real_smul, Module.Basis.coord_apply]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  ring

/-- **A section split along a cut-off frame.** Let `(bᵢ)` be a basis of the model fibre with
coordinate functionals `bᵢ*`, `ρ` a cutoff supported in the base set of `t`, and `θ` a cutoff
supported where `ρ = 1` inside that base set. Every section `s` splits as
`∑ᵢ θ kᵢ ρ t⁻¹ bᵢ + (1 - θ) s` with the coefficients `kᵢ = ρ bᵢ*(t s)`, also after multiplication
by any complex function `f`. -/
theorem smul_eq_sum_smul_cutoffFrameSection_add [FiniteDimensional ℂ W] (ρ : C^n⟮I, M; ℝ⟯)
    (hρ : tsupport ρ ⊆ t.baseSet) {ι : Type*} [Fintype ι] (b : Module.Basis ι ℂ W)
    (θ : C^n⟮I, M; ℝ⟯) (hθ : tsupport θ ⊆ {y | ρ y = 1} ∩ t.baseSet) (s : Cₛ^n⟮I; W, F⟯)
    (f : C^n⟮I, M; 𝓘(ℝ, ℂ), ℂ⟯) :
    f • s = ∑ i, (ContMDiffMap.ofReal θ *
        t.cutoffFrameCoeff ρ hρ (b.coord i).toContinuousLinearMap s * f) •
          t.cutoffFrameSection ρ hρ (b i) +
      ((1 - ContMDiffMap.ofReal θ) * f) • s := by
  ext y
  simp only [ContMDiffSection.coe_add, ContMDiffSection.coe_sum, Pi.add_apply, Finset.sum_apply,
    ContMDiffSection.smul_apply_of_normedAlgebra]
  by_cases hθy : θ y = 0
  · simp [hθy]
  obtain ⟨hρy, hy⟩ := hθ (subset_tsupport _ hθy)
  have hρy' : ρ y = 1 := hρy
  -- Each term is `θ(y) f(y) bᵢ*(t s(y)) t⁻¹ bᵢ`, and these add up to `θ(y) f(y) s(y)`.
  have hterm (i : ι) :
      (ContMDiffMap.ofReal θ *
          t.cutoffFrameCoeff ρ hρ (b.coord i).toContinuousLinearMap s * f) y •
        t.cutoffFrameSection ρ hρ (b i) y =
      ((θ y : ℂ) * f y) • (b.repr (t.continuousLinearMapAt ℂ y (s y)) i •
        t.symmL ℂ y (b i)) := by
    rw [cutoffFrameSection_apply, hρy', one_smul, t.symmL_apply (R := ℂ) hy, smul_smul]
    congr 1
    simp only [ContMDiffMap.coe_mul, Pi.mul_apply, ContMDiffMap.ofReal_apply,
      cutoffFrameCoeff_apply, hρy', one_smul, LinearMap.coe_toContinuousLinearMap',
      Module.Basis.coord_apply]
    ring
  rw [Finset.sum_congr rfl fun i _ ↦ hterm i, ← Finset.smul_sum, t.sum_repr_smul_symmL b hy,
    ← add_smul]
  congr 1
  simp only [ContMDiffMap.coe_mul, ContMDiffMap.coe_sub, ContMDiffMap.coe_one, Pi.mul_apply,
    Pi.sub_apply, Pi.one_apply, ContMDiffMap.ofReal_apply]
  ring

end Coeff

/-- **Expansion of a section in cut-off frames.** Let `tᵢ` be finitely many trivializations of a
complex vector bundle `F` in its atlas and `gᵢ` real `C^n` functions supported in their base sets,
and let `(bⱼ)` be a basis of the model fibre with coordinate functionals `bⱼ*`. If `∑ᵢ gᵢ² = 1` at
every point where the section `h` does not vanish, then `h` is the sum of the cut-off frame
sections `gᵢ tᵢ⁻¹ bⱼ` multiplied by the cut-off frame coefficients `gᵢ bⱼ*(tᵢ h)`. -/
theorem _root_.ContMDiffSection.eq_sum_cutoffFrameCoeff_smul_cutoffFrameSection
    {EM : Type*} [NormedAddCommGroup EM] [NormedSpace ℝ EM] {HM : Type*} [TopologicalSpace HM]
    {I : ModelWithCorners ℝ EM HM} {M : Type*} [TopologicalSpace M] [ChartedSpace HM M] {n : ℕ∞ω}
    {W : Type*} [NormedAddCommGroup W] [NormedSpace ℂ W] [FiniteDimensional ℂ W]
    {F : M → Type*} [TopologicalSpace (TotalSpace W F)] [∀ x, AddCommGroup (F x)]
    [∀ x, Module ℝ (F x)] [∀ x, Module ℂ (F x)] [∀ x, TopologicalSpace (F x)] [FiberBundle W F]
    [VectorBundle ℝ W F] [VectorBundle ℂ W F] [ContMDiffVectorBundle n W F I]
    (h : Cₛ^n⟮I; W, F⟯) {ι κ : Type*} [Fintype ι] [Fintype κ]
    (t : ι → Trivialization W (π W F)) [∀ i, MemTrivializationAtlas (t i)]
    (g : ι → C^n⟮I, M; ℝ⟯) (hg : ∀ i, tsupport (g i) ⊆ (t i).baseSet)
    (hh : ∀ x, h x ≠ 0 → ∑ i, g i x ^ 2 = 1) (b : Module.Basis κ ℂ W) :
    h = ∑ i, ∑ j, (t i).cutoffFrameCoeff (g i) (hg i) (b.coord j).toContinuousLinearMap h •
      (t i).cutoffFrameSection (g i) (hg i) (b j) := by
  ext x
  simp only [ContMDiffSection.coe_sum, Finset.sum_apply,
    ContMDiffSection.smul_apply_of_normedAlgebra,
    sum_cutoffFrameCoeff_smul_cutoffFrameSection_apply_sq, ← Finset.sum_smul]
  by_cases hx : h x = 0
  · simp [hx]
  rw [← Complex.ofReal_sum, hh x hx, Complex.ofReal_one, one_smul]

section Compact

variable {EM : Type*} [NormedAddCommGroup EM] [NormedSpace ℝ EM] [FiniteDimensional ℝ EM]
  {HM : Type*} [TopologicalSpace HM] {I : ModelWithCorners ℝ EM HM} {M : Type u}
  [TopologicalSpace M] [ChartedSpace HM M] [T2Space M] [IsManifold I ∞ M]
  {W : Type*} [NormedAddCommGroup W] [NormedSpace ℂ W] [FiniteDimensional ℂ W]
  {F : M → Type*} [TopologicalSpace (TotalSpace W F)] [∀ x, AddCommGroup (F x)]
  [∀ x, Module ℝ (F x)] [∀ x, Module ℂ (F x)] [∀ x, TopologicalSpace (F x)] [FiberBundle W F]
  [VectorBundle ℝ W F] [VectorBundle ℂ W F] [ContMDiffVectorBundle ∞ W F I]

/-- **Cut-off frames over a compact set.** Let `K` be a compact subset of `M` and `(bⱼ)` a basis of
the model fibre `W` with coordinate functionals `bⱼ*`. There are finitely many points `cᵢ` and
smooth real functions `ρᵢ`, `ψᵢ` supported in the base sets of the trivializations `tᵢ` of `F` at
`cᵢ`, such that every smooth section `h` of `F` agrees on `K` with the finite sum of the cut-off
frame sections `ψᵢ tᵢ⁻¹ bⱼ` multiplied by the cut-off frame coefficients `ρᵢ bⱼ*(tᵢ h)`. -/
theorem _root_.IsCompact.exists_sum_sum_cutoffFrameCoeff_smul_cutoffFrameSection_apply
    {K : Set M} (hK : IsCompact K) {ι' : Type*} [Fintype ι'] (b : Module.Basis ι' ℂ W) :
    ∃ (ι : Type u) (_ : Fintype ι) (c : ι → M) (ρ ψ : ι → C^∞⟮I, M; ℝ⟯)
      (hρ : ∀ i, tsupport (ρ i) ⊆ (trivializationAt W F (c i)).baseSet)
      (hψ : ∀ i, tsupport (ψ i) ⊆ (trivializationAt W F (c i)).baseSet),
      ∀ (h : Cₛ^∞⟮I; W, F⟯), ∀ x ∈ K,
        (∑ i, ∑ j, (trivializationAt W F (c i)).cutoffFrameCoeff (ρ i) (hρ i)
          (b.coord j).toContinuousLinearMap h •
            (trivializationAt W F (c i)).cutoffFrameSection (ψ i) (hψ i) (b j)) x = h x := by
  -- A finite partition of unity `ρᵢ` on `K` subordinate to the base sets of trivializations, and
  -- cutoffs `ψᵢ` equal to `1` near the compact supports of the `ρᵢ`.
  obtain ⟨ι, _, f, hf⟩ := hK.exists_smoothBumpCovering_isSubordinate I
    (U := fun x ↦ (trivializationAt W F x).baseSet) fun x _ ↦
      (trivializationAt W F x).open_baseSet.mem_nhds
        (FiberBundle.mem_baseSet_trivializationAt W F x)
  set ρ := f.toSmoothPartitionOfUnity
  have hρ (i : ι) : tsupport (ρ i) ⊆ (trivializationAt W F (f.c i)).baseSet :=
    hf.toSmoothPartitionOfUnity i
  have hρc (i : ι) : IsCompact (tsupport (ρ i)) :=
    (f i).hasCompactSupport.isCompact.of_isClosed_subset (isClosed_tsupport _)
      (closure_mono (f.support_toSmoothPartitionOfUnity_subset i))
  choose ψ hψ hψ1 _ hψt _ using fun i ↦ (hρc i).exists_contMDiff_one_nhds_tsupport_subset I
    (trivializationAt W F (f.c i)).open_baseSet (hρ i)
  set ψ' : ι → C^∞⟮I, M; ℝ⟯ := fun i ↦ ⟨ψ i, hψ i⟩
  refine ⟨ι, inferInstance, f.c, fun i ↦ ρ i, ψ', hρ, hψt, fun h x hx ↦ ?_⟩
  have hsum (i : ι) :=
    (trivializationAt W F (f.c i)).sum_cutoffFrameCoeff_smul_cutoffFrameSection_apply
      (ρ i) (hρ i) (ψ' i) (hψt i) (fun y hy ↦ (hψ1 i).self_of_nhdsSet y hy) b h x
  rw [ContMDiffSection.coe_sum, Finset.sum_apply, Finset.sum_congr rfl fun i _ ↦ hsum i,
    ← Finset.sum_smul, ← Complex.ofReal_sum, ← finsum_eq_sum_of_fintype, ρ.sum_eq_one hx,
    Complex.ofReal_one, one_smul]

end Compact

section ChartCutoff

variable {EM : Type*} [NormedAddCommGroup EM] [NormedSpace ℝ EM] {M : Type*} [TopologicalSpace M]
  [ChartedSpace EM M] [T2Space M] {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
  {V : M → Type*} [TopologicalSpace (TotalSpace F V)] [∀ x, AddCommGroup (V x)]
  [∀ x, Module ℝ (V x)] [∀ x, Module ℂ (V x)] [∀ x, TopologicalSpace (V x)] [FiberBundle F V]
  [VectorBundle ℝ F V] [VectorBundle ℂ F V] [ContMDiffVectorBundle ∞ F V 𝓘(ℝ, EM)]
  (t : Trivialization F (π F V)) [MemTrivializationAtlas t] {e : OpenPartialHomeomorph M EM}
  (he : e ∈ IsManifold.maximalAtlas 𝓘(ℝ, EM) ∞ M) (hE : e.source ⊆ t.baseSet)

/-- The **chart cut-off section** of a Schwartz function `u : EM → F`: for a chart `e` whose
source lies in the base set of the trivialization `t` and a cutoff `ψ` with compact support in the
chart target, the smooth section `x ↦ t⁻¹ₓ (ψ(e x) u(e x))` of `V` on the chart source, extended
by zero. Its frame coefficients in `t`, read in the chart, are `ψ u`. -/
def chartCutoffSection (ψ : 𝓓(⟨e.target, e.open_target⟩, ℝ)) (u : 𝓢(EM, F)) :
    Cₛ^∞⟮𝓘(ℝ, EM); F, V⟯ :=
  (t.chartTestSection (n := ⊤) e (contMDiffOn_of_mem_maximalAtlas he) hE
    (ψ.smulSchwartzMap u)).val

omit [∀ x, Module ℂ (V x)] [VectorBundle ℂ F V] in
theorem chartCutoffSection_apply_of_mem (ψ : 𝓓(⟨e.target, e.open_target⟩, ℝ)) (u : 𝓢(EM, F))
    {x : M} (hx : x ∈ e.source) :
    t.chartCutoffSection he hE ψ u x = t.symm x (ψ (e x) • u (e x)) := by
  rw [chartCutoffSection, t.chartTestSection_apply_of_mem (n := ⊤) e _ hE _ hx,
    t.symmL_apply (hE hx), TestFunction.smulSchwartzMap_apply]

omit [∀ x, Module ℂ (V x)] [VectorBundle ℂ F V] in
theorem chartCutoffSection_apply_of_notMem (ψ : 𝓓(⟨e.target, e.open_target⟩, ℝ))
    (u : 𝓢(EM, F)) {x : M} (hx : x ∉ e.source) :
    t.chartCutoffSection he hE ψ u x = 0 :=
  t.chartTestSection_apply_of_notMem (n := ⊤) e _ hE _ hx

/-- **A chart cut-off section in a frame.** Let `ρ` be a real smooth function on `M`, supported in
the base set of `t`, which equals `1` on `e⁻¹(supp ψ)`, and `(bᵢ)` a basis of the model fibre `F`
with coordinate functionals `bᵢ*`. Then the chart cut-off section of `u` is the sum over `i` of the
cut-off frame sections `ρ t⁻¹ bᵢ` multiplied by the complex pullbacks `(ψ bᵢ*(u)) ∘ e`. -/
theorem chartCutoffSection_eq_sum [FiniteDimensional ℂ F]
    (ψ : 𝓓(⟨e.target, e.open_target⟩, ℝ)) (u : 𝓢(EM, F))
    (ρ : C^∞⟮𝓘(ℝ, EM), M; ℝ⟯) (hρ : tsupport ρ ⊆ t.baseSet)
    (hρψ : ∀ y ∈ tsupport ψ, ρ (e.symm y) = 1) {ι : Type*} [Fintype ι] (b : Module.Basis ι ℂ F) :
    t.chartCutoffSection he hE ψ u = ∑ i, e.complexCutoffPullback he ψ
      (ContMDiffMap.ofContDiff (u.postcompCLM (b.coord i).toContinuousLinearMap)
        ((u.postcompCLM (b.coord i).toContinuousLinearMap).smooth ⊤)) •
          t.cutoffFrameSection ρ hρ (b i) := by
  ext x
  rw [ContMDiffSection.coe_sum, Finset.sum_apply]
  by_cases hx : x ∈ e.source
  · simp only [t.chartCutoffSection_apply_of_mem he hE _ _ hx,
      ContMDiffSection.smul_apply_of_normedAlgebra,
      e.complexCutoffPullback_apply_of_mem he _ _ hx, t.cutoffFrameSection_apply,
      ContMDiffMap.coe_ofContDiff, SchwartzMap.postcompCLM_apply]
    by_cases hψx : ψ (e x) = 0
    · simp [hψx, ← t.symmL_apply (R := ℂ) (hE hx)]
    have hρx : ρ x = 1 := by
      simpa [e.left_inv hx] using hρψ (e x) (subset_tsupport _ hψx)
    simp only [hρx, one_smul, ← t.symmL_apply (R := ℂ) (hE hx), ← map_smul, ← map_sum]
    congr 1
    conv_lhs => rw [← b.sum_repr (u (e x)), Finset.smul_sum]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    simp [← smul_assoc, Complex.real_smul]
  · simp [t.chartCutoffSection_apply_of_notMem he hE _ _ hx,
      e.complexCutoffPullback_apply_of_notMem he _ _ hx]

end ChartCutoff

section Decomposition

variable {EM : Type*} [NormedAddCommGroup EM] [NormedSpace ℝ EM] {HM : Type*} [TopologicalSpace HM]
  {I : ModelWithCorners ℝ EM HM} {M : Type*} [TopologicalSpace M] [ChartedSpace HM M] {n : ℕ∞ω}
  {W : Type*} [NormedAddCommGroup W] [NormedSpace ℂ W] [FiniteDimensional ℂ W]
  {F : M → Type*} [TopologicalSpace (TotalSpace W F)] [∀ x, AddCommGroup (F x)]
  [∀ x, Module ℝ (F x)] [∀ x, Module ℂ (F x)] [∀ x, TopologicalSpace (F x)] [FiberBundle W F]
  [VectorBundle ℝ W F] [VectorBundle ℂ W F] [ContMDiffVectorBundle n W F I]
  (t : Trivialization W (π W F)) [MemTrivializationAtlas t]

/-- **A cut-off section in a frame.** Let `ρ` be a real `C^n` function on `M`, supported in the
base set of `t`, and `Ψ` a real `C^n` function with `ρ = 1` wherever `Ψ ≠ 0`. For a basis `(b_k)`
of the model fibre with coordinate functionals `b_k*`, the section `Ψ u` is the sum over `k` of the
cut-off frame sections `ρ t⁻¹ b_k` multiplied by the coefficients `Ψ · ρ b_k*(t u)`. -/
theorem smul_eq_sum_cutoffFrameCoeff_smul_cutoffFrameSection (ρ : C^n⟮I, M; ℝ⟯)
    (hρ : tsupport ρ ⊆ t.baseSet) (Ψ : C^n⟮I, M; ℝ⟯) (hΨρ : ∀ x, Ψ x ≠ 0 → ρ x = 1)
    {ι : Type*} [Fintype ι] (b : Module.Basis ι ℂ W) (u : Cₛ^n⟮I; W, F⟯) :
    ContMDiffMap.ofReal Ψ • u = ∑ k, LinearMap.mulLeft ℂ (ContMDiffMap.ofReal Ψ)
      (t.cutoffFrameCoeff ρ hρ (b.coord k).toContinuousLinearMap u) •
        t.cutoffFrameSection ρ hρ (b k) := by
  ext x
  rw [ContMDiffSection.coe_sum, Finset.sum_apply]
  by_cases hx : Ψ x = 0
  · simp [hx]
  have hρx := hΨρ x hx
  have hxt : x ∈ t.baseSet := hρ (subset_tsupport _ (by simp [Function.mem_support, hρx]))
  conv_lhs => rw [ContMDiffSection.smul_apply_of_normedAlgebra,
    ← t.symmL_continuousLinearMapAt (R := ℂ) hxt (u x),
    ← b.sum_repr (t.continuousLinearMapAt ℂ x (u x)), map_sum, Finset.smul_sum]
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  simp [hρx, ← t.symmL_apply (R := ℂ) hxt, mul_smul]

end Decomposition

end Bundle.Trivialization

namespace TauCeti

section Partition

variable {EM : Type*} [NormedAddCommGroup EM] [NormedSpace ℝ EM] [FiniteDimensional ℝ EM]
  {M : Type*} [TopologicalSpace M] [ChartedSpace EM M] [T2Space M] [CompactSpace M]
  [IsManifold 𝓘(ℝ, EM) ∞ M] {F : Type*} [TopologicalSpace F] {V : M → Type*}
  [TopologicalSpace (TotalSpace F V)] [∀ x, TopologicalSpace (V x)] [FiberBundle F V]

/-- **Chart cutoffs adapted to a vector bundle.** On a compact Hausdorff manifold, a fibre bundle
`V` has finitely many points `cᵢ` and cutoffs `ψᵢ` with compact supports in the targets of the
preferred charts at the `cᵢ`, whose pullbacks `ψᵢ ∘ chartAt cᵢ`, extended by `0`, add up to `1`,
together with smooth functions `ρᵢ` supported in the base set of the trivialization of `V` at `cᵢ`
and equal to `1` on `(chartAt cᵢ)⁻¹(supp ψᵢ)`. So `ρᵢ` cuts off frame sections and frame
coefficients of `V` in that trivialization (`Bundle.Trivialization.cutoffFrameSection`,
`Bundle.Trivialization.cutoffFrameCoeff`) without changing them over the support of the `i`-th
cutoff. -/
theorem exists_sum_cutoffPullback_eq_one_and_baseSet_cutoff :
    ∃ (N : ℕ) (c : Fin N → M)
      (ψ : ∀ i, 𝓓(⟨(chartAt EM (c i)).target, (chartAt EM (c i)).open_target⟩, ℝ))
      (ρ : Fin N → C^∞⟮𝓘(ℝ, EM), M; ℝ⟯),
      (∀ x, ∑ i, (chartAt EM (c i)).cutoffPullback (IsManifold.chart_mem_maximalAtlas (c i))
        (ψ i) 1 x = 1) ∧ (∀ i, tsupport (ρ i) ⊆ (trivializationAt F V (c i)).baseSet) ∧
        ∀ i, ∀ y ∈ tsupport (ψ i), ρ i ((chartAt EM (c i)).symm y) = 1 := by
  obtain ⟨N, c, ψ, hψU, hψ⟩ := isCompact_univ.exists_sum_cutoffPullback_eq_one_of_mem_nhds
    (E := EM) (M := M) (U := fun x ↦ (trivializationAt F V x).baseSet)
    fun x _ ↦ (trivializationAt F V x).open_baseSet.mem_nhds (mem_baseSet_trivializationAt F V x)
  -- For each `i`, a smooth `ρᵢ` equal to `1` near the compact set `Kᵢ = (chartAt cᵢ)⁻¹(supp ψᵢ)`
  -- and supported in the base set.
  have hK (i : Fin N) : IsCompact ((chartAt EM (c i)).symm '' tsupport (ψ i)) :=
    (ψ i).hasCompactSupport.isCompact.image_of_continuousOn
      ((chartAt EM (c i)).continuousOn_symm.mono (ψ i).tsupport_subset)
  choose σ hσ hσ1 _ hσt _ using fun i ↦ (hK i).exists_contMDiff_one_nhds_tsupport_subset
    𝓘(ℝ, EM) (trivializationAt F V (c i)).open_baseSet (hψU i).2
  exact ⟨N, c, ψ, fun i ↦ ⟨σ i, hσ i⟩, fun x ↦ hψ x (mem_univ x), hσt, fun i y hy ↦
    (hσ1 i).self_of_nhdsSet _ (mem_image_of_mem _ hy)⟩

end Partition

end TauCeti
