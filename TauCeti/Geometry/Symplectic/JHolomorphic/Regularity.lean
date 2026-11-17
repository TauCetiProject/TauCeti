/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import TauCeti.Geometry.Symplectic.Complex.Module.Basic
public import TauCeti.Geometry.Symplectic.JHolomorphic.Varying
import TauCeti.Analysis.Complex.CauchyRiemann.Bootstrap

/-!
# Regularity of `C¹` `J`-holomorphic maps on finite-dimensional real normed spaces

Let `V` be a finite-dimensional real normed space equipped with a point-dependent almost complex
structure `J : V → AlmostComplexStructure V`, and let `u : ℂ → V` be a `C¹` map on an open set
`s ⊆ ℂ` mapping `s` into an open set `W ⊆ V` where
`x ↦ LinearMap.toContinuousLinearMap (J x).toLinearMap` is `C^n` (`n : ℕ∞`). If `u` is
`J`-holomorphic with respect to the standard complex structure
`AlmostComplexStructure.ofComplexModule ℂ` on `ℂ` (`TauCeti.IsJHolomorphicOn`), then `u` is `C^n`
on `s` (McDuff–Salamon, Theorem B.4.1 and Remark B.4.3).

The proof converts the pointwise complex-linearity condition `du_z ∘ i = J(u z) ∘ du_z` into the
homogeneous nonlinear weak Cauchy–Riemann equation `∂_s u + J(u) ∂_t u = 0` at exponent `p = 3`
(`TauCeti.isWeakCauchyRiemannOn_of_contDiffOn`) and invokes interior elliptic bootstrapping
(`TauCeti.IsWeakCauchyRiemannOn.contDiffOn` in `TauCeti.Analysis.Complex.CauchyRiemann.Bootstrap`).
The manifold-level smoothness corollaries for `TauCeti.IsPseudoholomorphicOn` and
`TauCeti.IsPseudoholomorphic` live in
`TauCeti.Geometry.Symplectic.Manifold.JHolomorphic.Regularity`.

## Main results

* `TauCeti.IsJHolomorphicOn.contDiffOn`: a `C¹` `J`-holomorphic map on an open subset `s ⊆ ℂ` into
  an open subset `W ⊆ V` where `J` is `C^n` is itself `C^n` on `s`.
* `TauCeti.IsJHolomorphic.contDiff`: the global specialization for `C¹` `J`-holomorphic maps
  `u : ℂ → V` with globally `C^n` structure `J`.

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, second edition,
  Appendix B.4 (Theorem B.4.1 and Remark B.4.3).
-/

public section

open Complex Set TopologicalSpace
open scoped ContDiff

namespace TauCeti

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- **Local `C^n` regularity of `C¹` `J`-holomorphic maps on planar open sets.** Let `V` be a
finite-dimensional real normed space, let `W ⊆ V` be an open set on which
`x ↦ LinearMap.toContinuousLinearMap (J x).toLinearMap` is `C^n`, and let `u : ℂ → V` be a `C¹` map
on an open set `s ⊆ ℂ` mapping `s` into `W` and satisfying
`IsJHolomorphicOn (fun _ => AlmostComplexStructure.ofComplexModule ℂ) J u s`. Then `u` is `C^n` on
`s` (McDuff–Salamon, Theorem B.4.1 and Remark B.4.3). -/
theorem IsJHolomorphicOn.contDiffOn [FiniteDimensional ℝ V] {n : ℕ∞} {s : Set ℂ} {W : Set V}
    {J : V → AlmostComplexStructure V} {u : ℂ → V}
    (h : IsJHolomorphicOn (fun _ => AlmostComplexStructure.ofComplexModule ℂ) J u s)
    (hs : IsOpen s) (hW : IsOpen W)
    (hJ : ContDiffOn ℝ n (fun x => LinearMap.toContinuousLinearMap (J x).toLinearMap) W)
    (hu : ContDiffOn ℝ 1 u s) (huW : MapsTo u s W) :
    ContDiffOn ℝ n u s := by
  have : CompleteSpace V := FiniteDimensional.completeSpace ℝ V
  let Ω : Opens ℂ := ⟨s, hs⟩
  let J₀ : ℂ → V → V →L[ℝ] V := fun _ x => LinearMap.toContinuousLinearMap (J x).toLinearMap
  have hw : IsWeakCauchyRiemannOn 3 Ω J₀ (fun _ _ => 0) u := by
    refine isWeakCauchyRiemannOn_of_contDiffOn (Ω := Ω) hu fun z hz => ?_
    have hz_hol := (h.isJHolomorphicWithinAt hz).isJHolomorphicAt_of_mem_nhds (hs.mem_nhds hz)
    have hcomm : fderiv ℝ u z I = (J (u z)).toLinearMap (fderiv ℝ u z 1) := by
      have h1 := LinearMap.congr_fun hz_hol.fderiv_isComplexLinear 1
      simpa only [LinearMap.comp_apply, ContinuousLinearMap.coe_coe,
        AlmostComplexStructure.ofComplexModule_apply, smul_eq_mul, mul_one] using h1
    have hsq :
        (J (u z)).toLinearMap ((J (u z)).toLinearMap (fderiv ℝ u z 1)) = -fderiv ℝ u z 1 :=
      (J (u z)).apply_apply (fderiv ℝ u z 1)
    simp only [J₀, LinearMap.coe_toContinuousLinearMap', hcomm, hsq, add_neg_cancel]
  have hJ_cd : ContDiffOn ℝ n (Function.uncurry J₀) (univ ×ˢ W) :=
    hJ.comp contDiffOn_snd fun _ hp => hp.2
  have hJsq : ∀ z ∈ (Ω : Set ℂ), (J₀ z (u z)).comp (J₀ z (u z)) = -ContinuousLinearMap.id ℝ V :=
    fun z _ => ContinuousLinearMap.ext fun v => (J (u z)).apply_apply v
  exact hw.contDiffOn (by exact_mod_cast (by norm_num : 2 < 3)) (isOpen_univ.prod hW) hJ_cd hJsq
    contDiffOn_const fun z hz => ⟨trivial, huW hz⟩

/-- **Global `C^n` regularity of `C¹` `J`-holomorphic maps from `ℂ`.** If `V` is a
finite-dimensional real normed space, `x ↦ LinearMap.toContinuousLinearMap (J x).toLinearMap` is
`C^n`, and `u : ℂ → V` is `C¹` and `J`-holomorphic, then `u` is `C^n`. -/
theorem IsJHolomorphic.contDiff [FiniteDimensional ℝ V] {n : ℕ∞}
    {J : V → AlmostComplexStructure V} {u : ℂ → V}
    (h : IsJHolomorphic (fun _ => AlmostComplexStructure.ofComplexModule ℂ) J u)
    (hJ : ContDiff ℝ n (fun x => LinearMap.toContinuousLinearMap (J x).toLinearMap))
    (hu : ContDiff ℝ 1 u) :
    ContDiff ℝ n u :=
  contDiffOn_univ.1 <| (h.isJHolomorphicOn univ).contDiffOn isOpen_univ isOpen_univ
    hJ.contDiffOn hu.contDiffOn (mapsTo_univ u univ)

end TauCeti
