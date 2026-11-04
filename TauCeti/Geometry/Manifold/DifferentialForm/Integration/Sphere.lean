/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.DifferentialForm.Closed
public import TauCeti.Geometry.Manifold.DifferentialForm.Integration.Homotopy
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import TauCeti.Analysis.Calculus.DifferentialForm.Stokes
import TauCeti.Geometry.Manifold.DifferentialForm.Naturality
import TauCeti.Geometry.Manifold.DifferentialForm.Pullback.Smooth
import TauCeti.Geometry.Manifold.DifferentialForm.Regularity

/-!
# Integrals of two-forms over spheres and caps, and weakly exact forms

A two-form `φ` on a manifold `M` is integrated over maps `u : ℝ × ℝ → M` of the unit square
(`TauCeti.rectangleIntegral φ u (0, 0) (1, 1)`). Two kinds of maps occur in Floer theory.

* A **smooth sphere** (`TauCeti.IsSmoothSphere`) is a smooth map `w` for which, on the square,
  every `t ↦ w (s, t)` is a loop and the boundary loops `s = 0` and `s = 1` are constant. Collapsing
  these two loops to points turns the cylinder `[0, 1] × ℝ/ℤ` into a two-sphere, through which `w`
  factors.
* A **smooth cap** of a loop `γ` (`TauCeti.IsSmoothCap`) is a smooth map `u` which restricts to `γ`
  on the line `s = 0` and is, on the square, a cylinder of loops from `γ` to the constant loop
  `s = 1`.

A two-form is **weakly exact** (`TauCeti.SmoothForm.IsWeaklyExact`) when its integral over every
smooth sphere vanishes. For a symplectic form this is the area half of symplectic asphericity,
`[ω]|π₂ = 0`. Its point is that the area of a cap does not depend on the cap: for a closed weakly
exact form, any two smooth caps of the same loop have the same integral
(`TauCeti.SmoothForm.IsWeaklyExact.rectangleIntegral_eq`). The cap area of a loop
(`TauCeti.SmoothForm.capArea`) is therefore well defined; it is the area term of the Hamiltonian
action functional on contractible loops.

The proof glues the two caps into a sphere. After a reparametrization of the first coordinate that
is constant near the loop, which does not change the integrals by homotopy invariance
(`TauCeti.rectangleIntegral_eq_of_homotopy`), the first cap traversed backwards and the second
traversed forwards agree near the seam, so they glue to a smooth sphere. Its integral is the
difference of the two cap areas.

Exact forms are weakly exact (`TauCeti.SmoothForm.isWeaklyExact_of_mextDeriv_eq`): by Stokes'
formula on the square, the integral of `dα` over a sphere is the integral of `α` around the
boundary of the square, where the constant loops contribute nothing and the edges `t = 0` and
`t = 1` cancel. This covers the exact symplectic forms of Liouville domains and cotangent bundles.
Weak exactness is natural under pullback by smooth maps
(`TauCeti.SmoothForm.IsWeaklyExact.mpullback`).

## Main definitions

* `TauCeti.IsSmoothSphere`: a smooth sphere, presented as a cylinder between constant loops.
* `TauCeti.IsSmoothCap`: a smooth cap of a loop.
* `TauCeti.SmoothForm.IsWeaklyExact`: the integral over every smooth sphere vanishes.
* `TauCeti.SmoothForm.capArea`: the integral over a smooth cap of a loop.

## Main results

* `TauCeti.SmoothForm.IsWeaklyExact.rectangleIntegral_eq`: for a closed weakly exact form, any two
  smooth caps of a loop have the same integral.
* `TauCeti.SmoothForm.IsWeaklyExact.capArea_eq`: the cap area is the integral over any smooth cap.
* `TauCeti.SmoothForm.isWeaklyExact_of_mextDeriv_eq`: exact forms are weakly exact.

## References

* A. Floer, *Symplectic fixed points and holomorphic spheres*, Comm. Math. Phys. 120 (1989),
  575–611 (weakly exact symplectic manifolds).
* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, 2nd ed., AMS, 2012,
  the chapter on Floer homology.
* D. Salamon, *Lectures on Floer homology*, in *Symplectic geometry and topology*, IAS/Park City
  Math. Ser. 7 (1999), Lecture 1 (the action functional on contractible loops).
-/

public section

noncomputable section

open Set MeasureTheory
open scoped Manifold Interval ContDiff Topology

namespace TauCeti

variable {E H M F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

variable (I) in
/-- A smooth sphere in `M`, presented as a cylinder between two constant loops: a smooth map
`w : ℝ × ℝ → M` such that, on the square `[0, 1] × [0, 1]`, every `t ↦ w (s, t)` is a loop and the
two boundary loops `s = 0` and `s = 1` are constant. Collapsing these two loops to points turns the
cylinder `[0, 1] × ℝ/ℤ` into a sphere, through which `w` factors. -/
structure IsSmoothSphere (w : ℝ × ℝ → M) : Prop where
  /-- A smooth sphere is smooth on the whole plane. -/
  contMDiff : ContMDiff 𝓘(ℝ, ℝ × ℝ) I ∞ w
  /-- The boundary loop `s = 0` is constant. -/
  apply_zero_fst : ∀ t ∈ Icc (0 : ℝ) 1, w (0, t) = w (0, 0)
  /-- The boundary loop `s = 1` is constant. -/
  apply_one_fst : ∀ t ∈ Icc (0 : ℝ) 1, w (1, t) = w (1, 0)
  /-- Every `t ↦ w (s, t)` is a loop on `[0, 1]`. -/
  apply_one_snd : ∀ s ∈ Icc (0 : ℝ) 1, w (s, 1) = w (s, 0)

variable (I) in
/-- A smooth cap of a loop `γ : ℝ → M`: a smooth map `u : ℝ × ℝ → M` which restricts to `γ` on the
line `s = 0` and which, on the square `[0, 1] × [0, 1]`, is a cylinder of loops `t ↦ u (s, t)` from
`γ` to the constant loop `s = 1`. This orientation, from the loop to the constant loop, is that of
the cylinder in the Hamiltonian action functional. The cap agrees with `γ` on the whole line
`s = 0`, not only for `t ∈ [0, 1]`, so that two caps of `γ` can be glued along that line into a
smooth sphere. -/
structure IsSmoothCap (u : ℝ × ℝ → M) (γ : ℝ → M) : Prop where
  /-- A smooth cap is smooth on the whole plane. -/
  contMDiff : ContMDiff 𝓘(ℝ, ℝ × ℝ) I ∞ u
  /-- A cap of `γ` restricts to `γ` on the line `s = 0`. -/
  apply_zero_fst : ∀ t, u (0, t) = γ t
  /-- The boundary loop `s = 1` of a cap is constant. -/
  apply_one_fst : ∀ t ∈ Icc (0 : ℝ) 1, u (1, t) = u (1, 0)
  /-- Every `t ↦ u (s, t)` is a loop on `[0, 1]`. -/
  apply_one_snd : ∀ s ∈ Icc (0 : ℝ) 1, u (s, 1) = u (s, 0)

/-- The image of a smooth sphere under a smooth map is a smooth sphere. -/
theorem IsSmoothSphere.comp {E' H' M' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
    [TopologicalSpace H'] {I' : ModelWithCorners ℝ E' H'} [TopologicalSpace M']
    [ChartedSpace H' M'] {w : ℝ × ℝ → M} (hw : IsSmoothSphere I w) {f : M → M'}
    (hf : ContMDiff I I' ∞ f) : IsSmoothSphere I' (f ∘ w) where
  contMDiff := hf.comp hw.contMDiff
  apply_zero_fst t ht := congrArg f (hw.apply_zero_fst t ht)
  apply_one_fst t ht := congrArg f (hw.apply_one_fst t ht)
  apply_one_snd s hs := congrArg f (hw.apply_one_snd s hs)

/-- The constant map is a smooth cap of the constant loop. -/
theorem isSmoothCap_const (x : M) : IsSmoothCap I (fun _ ↦ x) (fun _ ↦ x) where
  contMDiff := contMDiff_const
  apply_zero_fst _ := rfl
  apply_one_fst _ _ := rfl
  apply_one_snd _ _ := rfl

namespace IsSmoothCap

variable {u v : ℝ × ℝ → M} {γ : ℝ → M}

/-- The map `u` reparametrized in the first coordinate by `ρ(s) = smoothTransition (2 s - 1)`,
which vanishes for `s ≤ 1/2`, fixes `0` and `1`, and maps `[0, 1]` to itself. For a cap, this
flattened cap is constant in `s` near the loop. -/
private def flatten (u : ℝ × ℝ → M) (z : ℝ × ℝ) : M :=
  u (Real.smoothTransition (2 * z.1 - 1), z.2)

private theorem contDiff_flattenParam :
    ContDiff ℝ ∞ fun z : ℝ × ℝ ↦ (Real.smoothTransition (2 * z.1 - 1), z.2) :=
  ((Real.smoothTransition.contDiff (n := ⊤)).comp (by fun_prop)).prodMk contDiff_snd

private theorem contMDiff_flatten (hu : IsSmoothCap I u γ) :
    ContMDiff 𝓘(ℝ, ℝ × ℝ) I ∞ (flatten u) :=
  hu.contMDiff.comp contDiff_flattenParam.contMDiff

private theorem flatten_of_le (hu : IsSmoothCap I u γ) {s : ℝ} (hs : s ≤ 1 / 2) (t : ℝ) :
    flatten u (s, t) = γ t := by
  rw [flatten, Real.smoothTransition.zero_of_nonpos (by linarith), hu.apply_zero_fst]

omit [TopologicalSpace M] in
private theorem flatten_one (u : ℝ × ℝ → M) (t : ℝ) : flatten u (1, t) = u (1, t) := by
  norm_num [flatten]

private theorem flatten_apply_one_snd (hu : IsSmoothCap I u γ) (s : ℝ) :
    flatten u (s, 1) = flatten u (s, 0) :=
  hu.apply_one_snd _ ⟨Real.smoothTransition.nonneg _, Real.smoothTransition.le_one _⟩

variable [IsManifold I 2 M] [CompleteSpace F]

/-- Flattening a cap near its loop does not change its area: the straight-line homotopy from the
identity to `ρ` in the first coordinate is a homotopy of cylinders fixing both boundary loops. -/
private theorem rectangleIntegral_flatten {φ : RoughForm I M F 2} (hφ : IsSmoothForm I 1 φ)
    (hdφ : mextDeriv φ = 0) (hu : IsSmoothCap I u γ) :
    rectangleIntegral φ (flatten u) (0, 0) (1, 1) = rectangleIntegral φ u (0, 0) (1, 1) := by
  let σ : (ℝ × ℝ) × ℝ → ℝ := fun p ↦
    (1 - p.2) * p.1.1 + p.2 * Real.smoothTransition (2 * p.1.1 - 1)
  have hσ : ContDiff ℝ ∞ σ := by fun_prop
  have hσI {p : (ℝ × ℝ) × ℝ} (hs : p.1.1 ∈ Icc (0 : ℝ) 1) (hc : p.2 ∈ Icc (0 : ℝ) 1) :
      σ p ∈ Icc (0 : ℝ) 1 := by
    have h₀ := Real.smoothTransition.nonneg (2 * p.1.1 - 1)
    have h₁ := Real.smoothTransition.le_one (2 * p.1.1 - 1)
    simp only [σ, mem_Icc] at hs hc ⊢
    constructor <;> nlinarith
  let Φ : (ℝ × ℝ) × ℝ → M := fun p ↦ u (σ p, p.1.2)
  have hΦ : ContMDiff 𝓘(ℝ, (ℝ × ℝ) × ℝ) I 2 Φ :=
    (hu.contMDiff.comp (hσ.prodMk (contDiff_snd.comp contDiff_fst)).contMDiff).of_le
      (by simp)
  have h₀ : Real.smoothTransition (-1) = 0 := Real.smoothTransition.zero_of_nonpos (by norm_num)
  have h := rectangleIntegral_eq_of_homotopy hφ hdφ hΦ (a := (0, 0)) (b := (1, 1))
    (Or.inl fun t _ c _ ↦ by norm_num [Φ, σ, h₀])
    (Or.inl fun t _ c _ ↦ by norm_num [Φ, σ])
    (fun s hs c hc ↦ hu.apply_one_snd _ (hσI (p := ((s, 1), c))
      (by simpa using hs) hc))
  have e : flatten u = fun z ↦ u (Real.smoothTransition (2 * z.1 - 1), z.2) := rfl
  rw [e]
  simpa [Φ, σ] using h

/-- The sphere glued from two caps `u` and `v` of the same loop, both flattened near the loop: the
first cap runs backwards on `[0, 1/2]`, from its constant loop to the loop, and the second runs
forwards on `[1/2, 1]`, from the loop to its constant loop. -/
private def glue (u v : ℝ × ℝ → M) (z : ℝ × ℝ) : M :=
  if z.1 ≤ 1 / 2 then flatten u (-2 * z.1 + 1, z.2) else flatten v (2 * z.1 + -1, z.2)

omit [IsManifold I 2 M] in
/-- Near the seam `s = 1/2` the glued sphere is the common loop. -/
private theorem glue_of_mem (hu : IsSmoothCap I u γ) (hv : IsSmoothCap I v γ) {z : ℝ × ℝ}
    (hz : z.1 ∈ Icc (1 / 4 : ℝ) (3 / 4)) : glue u v z = γ z.2 := by
  by_cases h : z.1 ≤ 1 / 2
  · simp only [glue, h, ↓reduceIte]
    rw [hu.flatten_of_le (by linarith [hz.1])]
  · simp only [glue, h, ↓reduceIte]
    rw [hv.flatten_of_le (by linarith [hz.2])]

omit [IsManifold I 2 M] in
private theorem contMDiff_glue (hu : IsSmoothCap I u γ) (hv : IsSmoothCap I v γ) :
    ContMDiff 𝓘(ℝ, ℝ × ℝ) I ∞ (glue u v) := by
  have hL (c d : ℝ) : ContMDiff 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, ℝ × ℝ) ∞
      (fun z : ℝ × ℝ ↦ (c * z.1 + d, z.2)) :=
    (by fun_prop : ContDiff ℝ ∞ fun z : ℝ × ℝ ↦ (c * z.1 + d, z.2)).contMDiff
  refine (hu.contMDiff_flatten.comp (hL (-2) 1)).piecewise (s := {z | z.1 ≤ 1 / 2})
    (hv.contMDiff_flatten.comp (hL 2 (-1))) fun z hz ↦ ?_
  have hz' : z.1 = 1 / 2 := frontier_le_subset_eq continuous_fst continuous_const hz
  filter_upwards [continuous_fst.continuousAt.preimage_mem_nhds
    (Ioo_mem_nhds (a := 1 / 4) (b := 3 / 4) (by linarith) (by linarith))] with y hy
  rw [Function.comp_apply, Function.comp_apply, hu.flatten_of_le (by linarith [hy.1]),
    hv.flatten_of_le (by linarith [hy.2])]

omit [IsManifold I 2 M] in
private theorem isSmoothSphere_glue (hu : IsSmoothCap I u γ) (hv : IsSmoothCap I v γ) :
    IsSmoothSphere I (glue u v) where
  contMDiff := contMDiff_glue hu hv
  apply_zero_fst t ht := by
    norm_num [glue, flatten_one, hu.apply_one_fst t ht]
  apply_one_fst t ht := by
    norm_num [glue, flatten_one, hv.apply_one_fst t ht]
  apply_one_snd s _ := by
    by_cases h : s ≤ 1 / 2
    · simp only [glue, h, ↓reduceIte, hu.flatten_apply_one_snd]
    · simp only [glue, h, ↓reduceIte, hv.flatten_apply_one_snd]

omit [CompleteSpace F] in
/-- The integral over the glued sphere is the difference of the integrals over the two flattened
caps. -/
private theorem rectangleIntegral_glue {φ : RoughForm I M F 2} (hφ : IsSmoothForm I 0 φ)
    (hu : IsSmoothCap I u γ) (hv : IsSmoothCap I v γ) :
    rectangleIntegral φ (glue u v) (0, 0) (1, 1) =
      rectangleIntegral φ (flatten v) (0, 0) (1, 1) -
        rectangleIntegral φ (flatten u) (0, 0) (1, 1) := by
  rw [← rectangleIntegral_add_adjacent_fst hφ
    ((contMDiff_glue hu hv).of_le (by simp)) (0, 0) (1, 1) (1 / 2)]
  have h₁ : rectangleIntegral φ (glue u v) (0, 0) (1 / 2, 1) =
      rectangleIntegral φ (fun z ↦ flatten u (-2 * z.1 + 1, z.2)) (0, 0) (1 / 2, 1) := by
    refine rectangleIntegral_congr fun z hz ↦ ?_
    have hz₁ : z.1 ≤ 1 / 2 := by
      have := hz.1
      rw [uIcc_of_le (by norm_num)] at this
      exact this.2
    simp only [glue, hz₁, ↓reduceIte]
  have h₂ : rectangleIntegral φ (glue u v) (1 / 2, 0) (1, 1) =
      rectangleIntegral φ (fun z ↦ flatten v (2 * z.1 + -1, z.2)) (1 / 2, 0) (1, 1) := by
    refine rectangleIntegral_congr fun z hz ↦ ?_
    have hz₁ : 1 / 2 ≤ z.1 := by
      have := hz.1
      rw [uIcc_of_le (by norm_num)] at this
      exact this.1
    rcases hz₁.eq_or_lt with h | h
    · rw [glue_of_mem hu hv (by rw [← h]; norm_num), hv.flatten_of_le (by linarith)]
    · simp only [glue, not_le.mpr h, ↓reduceIte]
  rw [h₁, h₂, rectangleIntegral_comp_mul_add_fst, rectangleIntegral_comp_mul_add_fst]
  norm_num [rectangleIntegral_symm_fst φ (flatten u) 0 0 1 1]
  abel

end IsSmoothCap

namespace SmoothForm

variable [IsManifold I 1 M]

/-- A two-form is **weakly exact** when its integral over every smooth sphere vanishes, the
spheres being presented as cylinders between constant loops (`TauCeti.IsSmoothSphere`). For a
closed real two-form this is the vanishing of its cohomology class on the image of `π₂`, the area
part of symplectic asphericity. It makes the action functional on contractible loops independent of
the cap (`TauCeti.SmoothForm.IsWeaklyExact.rectangleIntegral_eq`). -/
def IsWeaklyExact (φ : SmoothForm I M F 2) : Prop :=
  ∀ w, IsSmoothSphere I w → rectangleIntegral φ.1 w (0, 0) (1, 1) = 0

/-- Unfolding `TauCeti.SmoothForm.IsWeaklyExact`. -/
theorem isWeaklyExact_def (φ : SmoothForm I M F 2) :
    φ.IsWeaklyExact ↔ ∀ w, IsSmoothSphere I w → rectangleIntegral φ.1 w (0, 0) (1, 1) = 0 :=
  Iff.rfl

/-- **Weak exactness is natural**: the pullback of a weakly exact form by a smooth map is weakly
exact, since the image of a smooth sphere is a smooth sphere. -/
theorem IsWeaklyExact.mpullback {E' H' M' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
    [TopologicalSpace H'] {I' : ModelWithCorners ℝ E' H'} [TopologicalSpace M']
    [ChartedSpace H' M'] [IsManifold I' 1 M'] {φ : SmoothForm I' M' F 2} (hφ : φ.IsWeaklyExact)
    {f : M → M'} (hf : ContMDiff I I' ∞ f) : (mpullback f hf φ).IsWeaklyExact := by
  intro w hw
  rw [coe_mpullback, rectangleIntegral_mpullback φ.1
    (fun z _ ↦ (hf.mdifferentiable (by simp)) (w z))
    (fun z _ ↦ (hw.contMDiff.mdifferentiable (by simp)) z)]
  exact hφ _ (hw.comp hf)

variable [IsManifold I 2 M] [CompleteSpace F] {φ : SmoothForm I M F 2} {u v : ℝ × ℝ → M}
  {γ : ℝ → M}

/-- **The area of a cap does not depend on the cap.** For a closed weakly exact two-form, any two
smooth caps of the same loop have the same integral. -/
theorem IsWeaklyExact.rectangleIntegral_eq (hφ : φ.IsWeaklyExact) (hc : φ.IsClosed)
    (hu : IsSmoothCap I u γ) (hv : IsSmoothCap I v γ) :
    rectangleIntegral φ.1 u (0, 0) (1, 1) = rectangleIntegral φ.1 v (0, 0) (1, 1) := by
  have h₁ := φ.isSmoothForm.of_le (n := ∞) (m := 1) (by simp)
  rw [SmoothForm.isClosed_def] at hc
  have h := hφ _ (IsSmoothCap.isSmoothSphere_glue hu hv)
  rw [IsSmoothCap.rectangleIntegral_glue (φ.isSmoothForm.of_le (by simp)) hu hv,
    IsSmoothCap.rectangleIntegral_flatten h₁ hc hu,
    IsSmoothCap.rectangleIntegral_flatten h₁ hc hv, sub_eq_zero] at h
  exact h.symm

omit [CompleteSpace F] in
/-- **Exact forms are weakly exact.** By Stokes' formula the integral of `dα` over a sphere is the
integral of `α` around the boundary of the square: the two constant boundary loops contribute
nothing, and the two edges `t = 0` and `t = 1` are the same path. -/
theorem isWeaklyExact_of_mextDeriv_eq {φ : SmoothForm I M F 2} {α : RoughForm I M F 1}
    (hα : IsSmoothForm I 1 α) (h : mextDeriv α = φ.1) : φ.IsWeaklyExact := by
  intro w hw
  have hwd : MDifferentiable 𝓘(ℝ, ℝ × ℝ) I w := hw.contMDiff.mdifferentiable (by simp)
  let ψ : ℝ × ℝ → (ℝ × ℝ) [⋀^Fin 1]→L[ℝ] F := TauCeti.mpullback 𝓘(ℝ, ℝ × ℝ) I w α
  have hψ : ContDiff ℝ 1 ψ :=
    isSmoothForm_modelSpace_iff.mp (hα.mpullback (f := w) (hw.contMDiff.of_le (by simp)))
  have hpull : TauCeti.mpullback 𝓘(ℝ, ℝ × ℝ) I w φ.1 = mextDeriv ψ := by
    rw [← h]
    exact TauCeti.mpullback_mextDeriv (hw.contMDiff.of_le (by simp))
      ((isSmoothBundleForm_def _ _).mpr hα.contMDiff)
  have hint : rectangleIntegral φ.1 w (0, 0) (1, 1) =
      ∫ s in (0 : ℝ)..1, ∫ t in (0 : ℝ)..1, extDeriv ψ (s, t) ![(1, 0), (0, 1)] := by
    have hd : mextDeriv ψ = extDeriv ψ := funext fun x ↦ mextDeriv_eq_extDeriv ψ x
    rw [rectangleIntegral_def, hpull, hd]
    rfl
  rw [hint, integral2_extDeriv fun z _ ↦ hψ.contDiffAt]
  -- The boundary loops `s = 0` and `s = 1` are constant, so `α` vanishes along them.
  have hconst {x : ℝ} (hx : ∀ t ∈ Icc (0 : ℝ) 1, w (x, t) = w (x, 0)) :
      ∫ t in (0 : ℝ)..1, ψ (x, t) (fun _ ↦ (0, 1)) = 0 := by
    refine (intervalIntegral.integral_congr_Ioo_of_le (g := fun _ ↦ 0) zero_le_one
      fun t ht ↦ ?_).trans intervalIntegral.integral_zero
    have hev : (fun t ↦ w (x, t)) =ᶠ[𝓝 t] fun _ ↦ w (x, 0) := by
      filter_upwards [Ioo_mem_nhds ht.1 ht.2] with t' ht'
      exact hx t' (Ioo_subset_Icc_self ht')
    refine (mpullback_apply_inr α (hwd _)).trans ?_
    rw [hev.mpullback_eq α, TauCeti.mpullback_apply]
    simp only [mfderiv_const, zero_apply]
    exact (α _).map_coord_zero (0 : Fin 1) rfl
  -- The edges `t = 0` and `t = 1` are the same path.
  have hedge : ∫ s in (0 : ℝ)..1, ψ (s, 1) (fun _ ↦ (1, 0)) =
      ∫ s in (0 : ℝ)..1, ψ (s, 0) (fun _ ↦ (1, 0)) := by
    refine intervalIntegral.integral_congr_Ioo_of_le zero_le_one fun s hs ↦ ?_
    have hev : (fun s ↦ w (s, 1)) =ᶠ[𝓝 s] fun s ↦ w (s, 0) := by
      filter_upwards [Ioo_mem_nhds hs.1 hs.2] with s' hs'
      exact hw.apply_one_snd s' (Ioo_subset_Icc_self hs')
    refine (mpullback_apply_inl α (hwd _)).trans
      (Eq.trans ?_ (mpullback_apply_inl α (hwd _)).symm)
    rw [hev.mpullback_eq α]
  rw [hconst hw.apply_zero_fst, hconst hw.apply_one_fst, hedge]
  simp

variable (φ) in
/-- The integral of a two-form over a smooth cap of the loop `γ`, for a cap chosen once and for
all; it is `0` when `γ` has no smooth cap. For a closed weakly exact form it is the integral over
every smooth cap (`TauCeti.SmoothForm.IsWeaklyExact.capArea_eq`). -/
def capArea (γ : ℝ → M) : F :=
  open Classical in
  if h : ∃ u, IsSmoothCap I u γ then rectangleIntegral φ.1 h.choose (0, 0) (1, 1) else 0

omit [IsManifold I 2 M] [CompleteSpace F] in
open Classical in
/-- Unfolding `TauCeti.SmoothForm.capArea`. -/
theorem capArea_def (γ : ℝ → M) : φ.capArea γ =
    if h : ∃ u, IsSmoothCap I u γ then rectangleIntegral φ.1 h.choose (0, 0) (1, 1) else 0 := by
  rw [capArea]

omit [IsManifold I 2 M] [CompleteSpace F] in
/-- A loop without a smooth cap has zero cap area. -/
@[simp]
theorem capArea_eq_zero_of_not_exists (h : ¬ ∃ u, IsSmoothCap I u γ) : φ.capArea γ = 0 := by
  simp [capArea_def, h]

/-- For a closed weakly exact form, `capArea` is the integral over any smooth cap. -/
theorem IsWeaklyExact.capArea_eq (hφ : φ.IsWeaklyExact) (hc : φ.IsClosed)
    (hu : IsSmoothCap I u γ) : φ.capArea γ = rectangleIntegral φ.1 u (0, 0) (1, 1) := by
  unfold capArea
  split_ifs with h
  · exact hφ.rectangleIntegral_eq hc h.choose_spec hu
  · exact absurd ⟨u, hu⟩ h

/-- For a closed weakly exact form, a constant loop has zero cap area. -/
theorem IsWeaklyExact.capArea_const (hφ : φ.IsWeaklyExact) (hc : φ.IsClosed) (x : M) :
    φ.capArea (fun _ ↦ x) = 0 := by
  rw [hφ.capArea_eq hc (isSmoothCap_const x)]
  exact rectangleIntegral_comp_fst φ.1 (fun _ ↦ x) _ _

end SmoothForm

end TauCeti
