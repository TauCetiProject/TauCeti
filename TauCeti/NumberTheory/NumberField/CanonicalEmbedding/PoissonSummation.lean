/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.NumberField.CanonicalEmbedding.Basic
public import TauCeti.Algebra.Module.ZLattice.Covolume
public import TauCeti.Analysis.Fourier.PoissonSummation

/-!
# Poisson summation on the mixed space of a number field

The mixed space `mixedSpace K = ℝ^r₁ × ℂ^r₂` of a number field `K` carries Mathlib's product sup
norm, so it is not an inner product space and Poisson summation for a lattice in a Euclidean
space does not apply to it as it stands. This file fixes the Euclidean structure on it once:

`mixedInner K x y = ∑_{w real} x_w y_w + ∑_{w complex} Re (x_w * conj y_w)`,

in which a complex coordinate counts once. It is the inner product of Mathlib's Euclidean model
`NumberField.mixedEmbedding.euclidean.mixedSpace K`, carried to the mixed space by the continuous
linear equivalence `euclidean.toMixed` (`mixedInner_toMixed`). That equivalence also carries
`volume` to `volume` (Mathlib's `euclidean.volumePreserving_toMixed`), so every Euclidean notion
can be read on the mixed space:

* the Fourier transform `mixedFourier K f w = ∫ x, 𝐞 (-mixedInner K x w) • f x`, with Mathlib's
  additive character `Real.fourierChar`, Mathlib's sign convention and the measure `volume`, is
  Mathlib's `𝓕` read through `euclidean.toMixed` (`mixedFourier_toMixed`);
* the dual `mixedDual K L` of a `ℤ`-submodule `L` of the mixed space, the points pairing
  integrally with every point of `L` under `mixedInner`, is the dual lattice `ZLattice.dual` of
  the pulled-back lattice (`comap_mixedDual`). Hence the dual of a full lattice is a full
  lattice, the dual of the dual is the lattice, and the covolume of the dual is the inverse
  covolume.

Poisson summation for a full lattice of a Euclidean space (`SchwartzMap.tsum_eq_tsum_dual_fourier`)
then reads, for a full lattice `L` of the mixed space, a Schwartz function `f` and `v` in the mixed
space (`tsum_eq_tsum_mixedDual_mixedFourier`),

`∑' ℓ : L, f (v + ℓ) = (covolume L)⁻¹ * ∑' m : L^∨, mixedFourier K f m * exp (2πi ⟨v, m⟩)`,

where `L^∨ = mixedDual K L` and `⟨v, m⟩ = mixedInner K v m`. Its instance at the lattice
`σ(I) = mixedEmbedding.idealLattice K I` of a fractional ideal `I` is the form of Poisson summation
behind the theta transformation of Hecke's proof of the functional equation of the Dedekind zeta
function (`tsum_idealLattice_eq_tsum_mixedDual_mixedFourier`); the covolume of `σ(I)` is
evaluated by Mathlib's `NumberField.mixedEmbedding.covolume_idealLattice`.

The Euclidean pairing rather than the trace form is used because the trace form is not positive
at a complex place (`Tr (i * i) = -2` over `ℚ(i)`), so it carries no Gaussian.

## Main definitions

* `TauCeti.NumberField.mixedEmbedding.mixedInner`: the Euclidean pairing of the mixed space.
* `TauCeti.NumberField.mixedEmbedding.mixedInnerBilin`: the same pairing as a bilinear form.
* `TauCeti.NumberField.mixedEmbedding.mixedFourier`: the Fourier transform of the mixed space.
* `TauCeti.NumberField.mixedEmbedding.mixedDual`: the dual of a `ℤ`-submodule of the mixed space.

## Main statements

* `TauCeti.NumberField.mixedEmbedding.mixedInner_def`: the coordinate formula for `mixedInner`.
* `TauCeti.NumberField.mixedEmbedding.mixedInner_toMixed`: `euclidean.toMixed` carries the inner
  product to `mixedInner`.
* `TauCeti.NumberField.mixedEmbedding.mixedFourier_toMixed`: `mixedFourier` is Mathlib's `𝓕` in
  the Euclidean model.
* `TauCeti.NumberField.mixedEmbedding.mixedDual_mixedDual`,
  `TauCeti.NumberField.mixedEmbedding.covolume_mixedDual`: biduality and the covolume of the dual
  of a full lattice.
* `TauCeti.NumberField.mixedEmbedding.tsum_eq_tsum_mixedDual_mixedFourier`: Poisson summation
  over a full lattice of the mixed space.

## References

* J. Neukirch, *Algebraic Number Theory*, Chapter VII, §3.
-/

public section

open Complex MeasureTheory NumberField NumberField.mixedEmbedding
open LinearMap (BilinForm)
open scoped Real RealInnerProductSpace SchwartzMap FourierTransform nonZeroDivisors

namespace TauCeti.NumberField.mixedEmbedding

variable (K : Type*) [Field K] [NumberField K]

/-! ### The Euclidean pairing -/

open scoped Classical in
/-- The Euclidean pairing of the mixed space,
`∑_{w real} x_w y_w + ∑_{w complex} Re (x_w * conj y_w)`, in which a complex coordinate counts
once. It is the inner product of Mathlib's Euclidean model of the mixed space
(`mixedInner_toMixed`). -/
noncomputable def mixedInner (x y : mixedSpace K) : ℝ :=
  ∑ w : {w : InfinitePlace K // w.IsReal}, x.1 w * y.1 w +
    ∑ w : {w : InfinitePlace K // w.IsComplex}, (x.2 w * (starRingEnd ℂ) (y.2 w)).re

open scoped Classical in
/-- The coordinate formula for the Euclidean pairing: the sum of the products of the real
coordinates plus the sum of the real parts `Re (x_w * conj y_w)` over the complex coordinates. -/
theorem mixedInner_def (x y : mixedSpace K) :
    mixedInner K x y = ∑ w : {w : InfinitePlace K // w.IsReal}, x.1 w * y.1 w +
      ∑ w : {w : InfinitePlace K // w.IsComplex}, (x.2 w * (starRingEnd ℂ) (y.2 w)).re := by
  rw [mixedInner]

/-- The Euclidean pairing is symmetric. -/
theorem mixedInner_comm (x y : mixedSpace K) : mixedInner K x y = mixedInner K y x := by
  simp only [mixedInner, mul_comm (x.1 _), Complex.mul_re, Complex.conj_re, Complex.conj_im]
  congr 1
  exact Finset.sum_congr rfl fun _ _ ↦ by ring

open scoped Classical in
/-- **The Euclidean model carries `mixedInner`**: Mathlib's continuous linear equivalence
`euclidean.toMixed` carries the inner product of `euclidean.mixedSpace K` to `mixedInner`. -/
@[simp]
theorem mixedInner_toMixed (x y : euclidean.mixedSpace K) :
    mixedInner K (euclidean.toMixed K x) (euclidean.toMixed K y) = ⟪x, y⟫ := by
  -- `euclidean.toMixed` only forgets the `WithLp` wrappers of the Euclidean model.
  have h (z : euclidean.mixedSpace K) :
      euclidean.toMixed K z = ((WithLp.ofLp z).1.ofLp, (WithLp.ofLp z).2.ofLp) := rfl
  simp only [mixedInner, h, WithLp.prod_inner_apply, PiLp.inner_apply, real_inner_eq_re_inner ℂ,
    RCLike.inner_apply, conj_trivial, RCLike.re_to_complex, Complex.mul_re, Complex.conj_re,
    Complex.conj_im]
  congr 1 <;> exact Finset.sum_congr rfl fun _ _ ↦ by ring

open scoped Classical in
/-- The Euclidean pairing `mixedInner` as a bilinear form: the inner product of Mathlib's
Euclidean model of the mixed space, read through `euclidean.toMixed`. -/
noncomputable def mixedInnerBilin : mixedSpace K →ₗ[ℝ] mixedSpace K →ₗ[ℝ] ℝ :=
  (innerₗ (euclidean.mixedSpace K)).compl₁₂ (euclidean.toMixed K).symm.toLinearMap
    (euclidean.toMixed K).symm.toLinearMap

@[simp]
theorem mixedInnerBilin_apply (x y : mixedSpace K) :
    mixedInnerBilin K x y = mixedInner K x y := by
  classical
  obtain ⟨x, rfl⟩ := (euclidean.toMixed K).surjective x
  obtain ⟨y, rfl⟩ := (euclidean.toMixed K).surjective y
  simp [mixedInnerBilin]

/-! ### The Fourier transform -/

open scoped Classical in
/-- **The Fourier transform of the mixed space**,
`mixedFourier K f w = ∫ x, 𝐞 (-mixedInner K x w) • f x`, taken with Mathlib's additive character
`Real.fourierChar`, the Euclidean pairing `mixedInner` and the measure `volume`. It is Mathlib's
`𝓕` in the Euclidean model (`mixedFourier_toMixed`). -/
noncomputable def mixedFourier (f : mixedSpace K → ℂ) : mixedSpace K → ℂ :=
  VectorFourier.fourierIntegral Real.fourierChar volume (mixedInnerBilin K) f

open scoped Classical in
theorem mixedFourier_apply (f : mixedSpace K → ℂ) (w : mixedSpace K) :
    mixedFourier K f w = ∫ x, 𝐞 (-mixedInner K x w) • f x := by
  simp [mixedFourier, VectorFourier.fourierIntegral]

open scoped Classical in
/-- **The Fourier transform transports along the change of model**: read through
`euclidean.toMixed`, which carries `mixedInner` to the inner product (`mixedInner_toMixed`) and
`volume` to `volume` (`euclidean.volumePreserving_toMixed`), `mixedFourier` is Mathlib's `𝓕`. -/
theorem mixedFourier_toMixed (f : mixedSpace K → ℂ) (y : euclidean.mixedSpace K) :
    mixedFourier K f (euclidean.toMixed K y) = 𝓕 (fun x ↦ f (euclidean.toMixed K x)) y := by
  rw [mixedFourier_apply, Real.fourier_eq,
    ← (euclidean.volumePreserving_toMixed K).integral_comp
      (euclidean.toMixed K).toHomeomorph.measurableEmbedding]
  simp

/-! ### The dual of a lattice -/

open scoped Classical in
/-- The dual of a `ℤ`-submodule `L` of the mixed space for the Euclidean pairing: the points `y`
with `mixedInner K x y ∈ ℤ` for every `x ∈ L` (`mem_mixedDual`). It is Mathlib's
`BilinForm.dualSubmodule` of `mixedInnerBilin`, and the dual lattice `ZLattice.dual` read on the
mixed space (`comap_mixedDual`). -/
noncomputable def mixedDual (L : Submodule ℤ (mixedSpace K)) : Submodule ℤ (mixedSpace K) :=
  BilinForm.dualSubmodule (mixedInnerBilin K) L

variable {K} in
@[simp]
theorem mem_mixedDual {L : Submodule ℤ (mixedSpace K)} {y : mixedSpace K} :
    y ∈ mixedDual K L ↔ ∀ x ∈ L, ∃ n : ℤ, mixedInner K x y = n := by
  simp only [mixedDual, BilinForm.mem_dualSubmodule, Submodule.mem_one, mixedInnerBilin_apply,
    algebraMap_int_eq, eq_intCast, eq_comm, mixedInner_comm K y]

open scoped Classical in
/-- **The dual on the mixed space is the Euclidean dual lattice**: pulled back along
`euclidean.toMixed`, the dual `mixedDual K L` is the dual lattice of the pulled-back lattice. -/
theorem comap_mixedDual (L : Submodule ℤ (mixedSpace K)) :
    ZLattice.comap ℝ (mixedDual K L) (euclidean.toMixed K).toLinearMap =
      ZLattice.dual (ZLattice.comap ℝ L (euclidean.toMixed K).toLinearMap) := by
  ext y
  simp only [ZLattice.mem_comap, ZLattice.mem_dual, mem_mixedDual, LinearEquiv.coe_coe,
    ContinuousLinearEquiv.coe_toLinearEquiv]
  refine ⟨fun h x hx ↦ ?_, fun h x hx ↦ ?_⟩
  · obtain ⟨n, hn⟩ := h _ hx
    exact ⟨n, by rw [← mixedInner_toMixed, mixedInner_comm, hn]⟩
  · obtain ⟨x, rfl⟩ := (euclidean.toMixed K).surjective x
    obtain ⟨n, hn⟩ := h x hx
    exact ⟨n, by rw [mixedInner_toMixed, real_inner_comm, hn]⟩

open scoped Classical in
/-- The dual on the mixed space is the image of the Euclidean dual lattice of the pulled-back
lattice under `euclidean.toMixed`. -/
theorem mixedDual_eq_comap (L : Submodule ℤ (mixedSpace K)) :
    mixedDual K L = ZLattice.comap ℝ
      (ZLattice.dual (ZLattice.comap ℝ L (euclidean.toMixed K).toLinearMap))
      (euclidean.toMixed K).symm.toLinearMap := by
  rw [← comap_mixedDual, ZLattice.comap_comp]
  ext
  simp

open scoped Classical in
instance (L : Submodule ℤ (mixedSpace K)) [DiscreteTopology L] [IsZLattice ℝ L] :
    DiscreteTopology (mixedDual K L) := by
  rw [mixedDual_eq_comap]
  infer_instance

open scoped Classical in
instance (L : Submodule ℤ (mixedSpace K)) [DiscreteTopology L] [IsZLattice ℝ L] :
    IsZLattice ℝ (mixedDual K L) where
  span_top := by
    rw [mixedDual_eq_comap]
    exact IsZLattice.span_top

open scoped Classical in
/-- **Biduality**: the dual of the dual of a full lattice of the mixed space is the lattice. -/
@[simp]
theorem mixedDual_mixedDual (L : Submodule ℤ (mixedSpace K)) [DiscreteTopology L]
    [IsZLattice ℝ L] : mixedDual K (mixedDual K L) = L := by
  rw [mixedDual_eq_comap, comap_mixedDual, ZLattice.dual_dual, ZLattice.comap_comp]
  ext
  simp

open scoped Classical in
/-- The covolume of the dual of a full lattice of the mixed space is the inverse covolume. -/
@[simp]
theorem covolume_mixedDual (L : Submodule ℤ (mixedSpace K)) [DiscreteTopology L]
    [IsZLattice ℝ L] : ZLattice.covolume (mixedDual K L) = (ZLattice.covolume L)⁻¹ := by
  have he := euclidean.volumePreserving_toMixed K
  rw [← ZLattice.covolume_comap _ _ _ he, comap_mixedDual, ZLattice.covolume_dual,
    ZLattice.covolume_comap _ _ _ he]

/-! ### Poisson summation -/

open scoped Classical in
/-- **Poisson summation over a full lattice of the mixed space**: for a Schwartz function `f` and
`v` in the mixed space,
`∑' ℓ : L, f (v + ℓ) = (covolume L)⁻¹ * ∑' m : L^∨, mixedFourier K f m * exp (2πi ⟨v, m⟩)`,
with `L^∨ = mixedDual K L` and `⟨v, m⟩ = mixedInner K v m`.
It is `SchwartzMap.tsum_eq_tsum_dual_fourier` in Mathlib's Euclidean model, read back through
`mixedFourier_toMixed` and `euclidean.volumePreserving_toMixed`. -/
theorem tsum_eq_tsum_mixedDual_mixedFourier (L : Submodule ℤ (mixedSpace K)) [DiscreteTopology L]
    [IsZLattice ℝ L] (f : 𝓢(mixedSpace K, ℂ)) (v : mixedSpace K) :
    ∑' ℓ : L, f (v + ℓ) = (ZLattice.covolume L : ℂ)⁻¹ *
      ∑' m : mixedDual K L,
        mixedFourier K f m * cexp (2 * π * I * mixedInner K v m) := by
  let e := euclidean.toMixed K
  let L' := ZLattice.comap ℝ L e.toLinearMap
  let g := SchwartzMap.compCLMOfContinuousLinearEquiv ℂ e f
  -- `e` identifies `L'` with `L`, and the dual of `L'` with `mixedDual K L`.
  let eL : L' ≃ L := e.toEquiv.subtypeEquiv fun x ↦ ZLattice.mem_comap ℝ L e.toLinearMap
  let eD : ZLattice.dual L' ≃ mixedDual K L :=
    e.toEquiv.subtypeEquiv fun m ↦ by
      rw [← comap_mixedDual]
      exact ZLattice.mem_comap ℝ _ e.toLinearMap
  have hcov : ZLattice.covolume L' = ZLattice.covolume L :=
    ZLattice.covolume_comap _ _ _ (euclidean.volumePreserving_toMixed K)
  have h := SchwartzMap.tsum_eq_tsum_dual_fourier g L' (e.symm v)
  rw [hcov] at h
  rw [← eL.tsum_eq, ← eD.tsum_eq]
  convert h using 3 with ℓ m
  · simp [eL, g, e, Equiv.subtypeEquiv_apply, LinearEquiv.coe_toEquiv]
  · ext m
    simp only [eD, Equiv.subtypeEquiv_apply, LinearEquiv.coe_toEquiv,
      ContinuousLinearEquiv.coe_toLinearEquiv]
    rw [mixedFourier_toMixed, ← mixedInner_toMixed, e.apply_symm_apply]
    simp [g, e, Function.comp_def]

open scoped Classical in
/-- **Poisson summation over an ideal lattice**: the lattice `σ(I)` of a fractional ideal `I` in
the mixed space, at `v = 0`. Its covolume `ZLattice.covolume (idealLattice K I)` is
`N(I) * 2 ^ (-r₂) * √|d_K|` by Mathlib's `NumberField.mixedEmbedding.covolume_idealLattice`. -/
theorem tsum_idealLattice_eq_tsum_mixedDual_mixedFourier (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    (f : 𝓢(mixedSpace K, ℂ)) :
    ∑' x : idealLattice K I, f x = (ZLattice.covolume (idealLattice K I) : ℂ)⁻¹ *
      ∑' m : mixedDual K (idealLattice K I), mixedFourier K f m := by
  simpa [← mixedInnerBilin_apply] using tsum_eq_tsum_mixedDual_mixedFourier K (idealLattice K I) f 0

end TauCeti.NumberField.mixedEmbedding
