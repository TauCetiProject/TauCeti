/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.DifferentialForm.Squared
public import TauCeti.Geometry.Symplectic.Lagrangian.Manifold

/-!
# Exact Lagrangian maps

Let `σ` be a nondegenerate two-form on `M` with a chosen primitive one-form `θ`, `σ = -dθ`, so
that `(M, σ, θ)` is an exact symplectic manifold. A Lagrangian map `f : N → M` is **exact**, with
primitive `h : N → ℝ`, when `h` is smooth and `f^*θ = dh`
(`TauCeti.SmoothTwoForm.IsNondegenerate.IsExactLagrangianMap`). The primitive is part of the
data: in Floer theory it is the function from which actions of intersection points are computed.
The predicate applies to embedded and immersed Lagrangians alike, through any parametrization.

The main facts are:

* **Exactness forces isotropy.** If `σ = -dθ` and `f^*θ = dh` for a smooth `f`, then
  `f^*σ = -d(dh) = 0`, so `f` is isotropic. Hence a smooth map with injective differentials
  from a manifold of half the dimension is an exact Lagrangian map exactly when `f^*θ` is the
  differential of a smooth function
  (`TauCeti.SmoothTwoForm.IsNondegenerate.isExactLagrangianMap_iff_of_finrank`).
* **Uniqueness of primitives.** Two primitives of the same exact Lagrangian map differ by a
  locally constant function, and every such modification is again a primitive
  (`IsExactLagrangianMap.isExactLagrangianMap_iff_isLocallyConstant_sub`). On a preconnected
  source they differ by a constant.
* **Change of primitive.** Replacing `θ` by `θ + dg` keeps `f` exact, with primitive
  `h + g ∘ f`.
* **Transport by exact symplectomorphisms.** A diffeomorphism `ψ : M → M₂` with `ψ^*σ₂ = σ` and
  `ψ^*θ₂ = θ + dg` carries exact Lagrangian maps `f` with primitive `h` to exact Lagrangian maps
  `ψ ∘ f` with primitive `h + g ∘ f`, and conversely.

The cotangent examples, the zero section and the graphs of exact one-forms, are in
`TauCeti.Geometry.Symplectic.Cotangent.Bundle.Graph`.

## Main declarations

* `TauCeti.SmoothTwoForm.IsNondegenerate.IsExactLagrangianMap`: exact Lagrangian maps with a
  specified primitive.
* `TauCeti.SmoothTwoForm.IsNondegenerate.isIsotropicMap_of_mpullback_eq_mextDeriv`: exactness
  forces isotropy.
* `IsExactLagrangianMap.isExactLagrangianMap_iff_isLocallyConstant_sub`,
  `IsExactLagrangianMap.exists_eq_add_const`: uniqueness of primitives, in the namespace
  `TauCeti.SmoothTwoForm.IsNondegenerate`.
* `TauCeti.SmoothTwoForm.IsNondegenerate.isExactLagrangianMap_add_mextDeriv_iff`: change of
  primitive one-form.
* `Diffeomorph.isExactLagrangianMap_comp_iff`: transport by exact symplectomorphisms.

## References

* D. McDuff, D. Salamon, *Introduction to Symplectic Topology*, 3rd ed., Oxford, 2017,
  Sections 3.4 and 9.2.
* P. Seidel, *Fukaya categories and Picard–Lefschetz theory*, Zurich Lectures in Advanced
  Mathematics, EMS, 2008, Section 7a.
-/

public section

noncomputable section

open Manifold Module
open scoped Manifold ContDiff

namespace TauCeti

namespace SmoothTwoForm

namespace IsNondegenerate

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M]
  {E' H' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [TopologicalSpace H']
  {J : ModelWithCorners ℝ E' H'} {N : Type*} [TopologicalSpace N] [ChartedSpace H' N]
  {σ : SmoothTwoForm I M} {hσ : σ.IsNondegenerate} {θ θ' : SmoothForm I M ℝ 1} {f : N → M}
  {h h' : N → ℝ}

variable (J hσ) in
/-- A map `f : N → M` is an **exact Lagrangian map** for the nondegenerate two-form `σ` and the
one-form `θ`, with **primitive** `h : N → ℝ`, when it is a Lagrangian map, `h` is smooth, and
`f` pulls `θ` back to `dh`. It is meant for a primitive `θ` of `σ`, `σ = -dθ`; for such a `θ`
the isotropy of `f` follows from `f^*θ = dh`
(`TauCeti.SmoothTwoForm.IsNondegenerate.isIsotropicMap_of_mpullback_eq_mextDeriv`). -/
structure IsExactLagrangianMap (θ : SmoothForm I M ℝ 1) (f : N → M) (h : N → ℝ) : Prop where
  /-- An exact Lagrangian map is a Lagrangian map. -/
  isLagrangianMap : hσ.IsLagrangianMap J f
  /-- The primitive of an exact Lagrangian map is smooth. -/
  contMDiff_primitive : ContMDiff J 𝓘(ℝ) ∞ h
  /-- An exact Lagrangian map pulls the one-form back to the differential of its primitive. -/
  mpullback_eq : mpullback J I f θ.1 = mextDeriv (RoughForm.ofFunction J h)

/-- An exact Lagrangian map is a Lagrangian map with a smooth primitive `h` of the pulled-back
one-form, `f^*θ = dh`. -/
theorem isExactLagrangianMap_iff :
    hσ.IsExactLagrangianMap J θ f h ↔ hσ.IsLagrangianMap J f ∧ ContMDiff J 𝓘(ℝ) ∞ h ∧
      mpullback J I f θ.1 = mextDeriv (RoughForm.ofFunction J h) :=
  ⟨fun hL ↦ ⟨hL.1, hL.2, hL.3⟩, fun hL ↦ ⟨hL.1, hL.2.1, hL.2.2⟩⟩

/-! ### Exactness forces isotropy -/

section Isotropy

variable [IsManifold J ∞ N]

/-- **Exact maps are isotropic.** If `σ = -dθ` and a smooth map `f` pulls `θ` back to the
differential of a `C²` function `h`, then `f^*σ = -d(dh) = 0`, so `f` is isotropic for `σ`. -/
theorem isIsotropicMap_of_mpullback_eq_mextDeriv (hθ : σ = -mextDerivₗ I 1 θ)
    (hf : ContMDiff J I ∞ f) (hh : ContMDiff J 𝓘(ℝ) 2 h)
    (hfh : mpullback J I f θ.1 = mextDeriv (RoughForm.ofFunction J h)) :
    hσ.IsIsotropicMap J f := by
  rw [isIsotropicMap_iff_mpullback_eq_zero hf, hθ, map_neg, ← SmoothForm.mextDerivₗ_mpullback,
    neg_eq_zero]
  apply Subtype.ext
  rw [mextDerivₗ_apply, SmoothForm.coe_mpullback, hfh, mextDeriv_mextDeriv_ofFunction hh,
    ZeroMemClass.coe_zero]

variable [FiniteDimensional ℝ E]

/-- **Exact Lagrangian maps from half-dimensional manifolds.** For a primitive `θ` of `σ`, a
smooth map with injective differentials from a manifold of half the dimension is an exact
Lagrangian map with primitive `h` exactly when `h` is smooth and `f^*θ = dh`. -/
theorem isExactLagrangianMap_iff_of_finrank (hθ : σ = -mextDerivₗ I 1 θ)
    (hf : ContMDiff J I ∞ f) (hinj : ∀ x, Function.Injective (mfderiv J I f x))
    (hdim : 2 * finrank ℝ E' = finrank ℝ E) :
    hσ.IsExactLagrangianMap J θ f h ↔
      ContMDiff J 𝓘(ℝ) ∞ h ∧ mpullback J I f θ.1 = mextDeriv (RoughForm.ofFunction J h) :=
  isExactLagrangianMap_iff.trans ⟨fun hL ↦ hL.2, fun ⟨hh, hfh⟩ ↦
    ⟨(isIsotropicMap_of_mpullback_eq_mextDeriv hθ hf (hh.of_le (by simp)) hfh
      |>.isLagrangianMap_of_finrank hinj hdim), hh, hfh⟩⟩

end Isotropy

/-! ### Uniqueness of primitives -/

namespace IsExactLagrangianMap

variable [IsManifold J 1 N]

/-- **Primitives are unique up to locally constant functions.** Given an exact Lagrangian map with
primitive `h`, a function `h'` is another primitive exactly when `h' - h` is locally constant. -/
theorem isExactLagrangianMap_iff_isLocallyConstant_sub (hL : hσ.IsExactLagrangianMap J θ f h) :
    hσ.IsExactLagrangianMap J θ f h' ↔ IsLocallyConstant (h' - h) := by
  have hhd : MDifferentiable J 𝓘(ℝ) h := hL.contMDiff_primitive.mdifferentiable (by simp)
  refine ⟨fun hL' ↦ ?_, fun hc ↦ ?_⟩
  · have hh'd : MDifferentiable J 𝓘(ℝ) h' := hL'.contMDiff_primitive.mdifferentiable (by simp)
    rw [← mextDeriv_ofFunction_eq_zero_iff (hh'd.sub hhd)]
    -- `dh' = d(h' - h) + dh`, and `dh' = f^*θ = dh`.
    have hsum := mextDeriv_ofFunction_add (I := J) (hh'd.sub hhd) hhd
    rw [sub_add_cancel, ← hL.mpullback_eq, ← hL'.mpullback_eq] at hsum
    exact add_eq_right.mp hsum.symm
  · -- A locally constant function is smooth, and its differential vanishes.
    have hcs : ContMDiff J 𝓘(ℝ) ∞ (h' - h) := hc.contMDiff
    have hcd : MDifferentiable J 𝓘(ℝ) (h' - h) := hcs.mdifferentiable (by simp)
    have hh' : h' = h + (h' - h) := by abel
    refine ⟨hL.isLagrangianMap, hh' ▸ hL.contMDiff_primitive.add hcs, ?_⟩
    rw [hh', mextDeriv_ofFunction_add hhd hcd, (mextDeriv_ofFunction_eq_zero_iff hcd).mpr hc,
      add_zero, hL.mpullback_eq]

/-- Adding a constant to the primitive of an exact Lagrangian map gives another primitive. -/
theorem add_const (hL : hσ.IsExactLagrangianMap J θ f h) (c : ℝ) :
    hσ.IsExactLagrangianMap J θ f (fun x ↦ h x + c) :=
  hL.isExactLagrangianMap_iff_isLocallyConstant_sub.mpr <| by
    have hsub : (fun x ↦ h x + c) - h = fun _ ↦ c := by
      funext x
      simp
    rw [hsub]
    exact IsLocallyConstant.const c

/-- **Primitives differ by a constant on a connected source.** Two primitives of the same exact
Lagrangian map from a preconnected manifold differ by a constant. -/
theorem exists_eq_add_const [PreconnectedSpace N] (hL : hσ.IsExactLagrangianMap J θ f h)
    (hL' : hσ.IsExactLagrangianMap J θ f h') : ∃ c : ℝ, h' = fun x ↦ h x + c := by
  obtain ⟨c, hc⟩ := (hL.isExactLagrangianMap_iff_isLocallyConstant_sub.mp hL').exists_eq_const
  refine ⟨c, funext fun x ↦ ?_⟩
  have := congrFun hc x
  simp only [Pi.sub_apply, Function.const_apply] at this
  linarith

end IsExactLagrangianMap

/-! ### Change of primitive one-form -/

/-- **Changing the primitive one-form by an exact form.** If `θ' = θ + dg` for a smooth function
`g` on `M`, then a smooth map `f` is an exact Lagrangian map for `θ'` with primitive `h + g ∘ f`
exactly when it is one for `θ` with primitive `h`. -/
theorem isExactLagrangianMap_add_mextDeriv_iff (hf : ContMDiff J I ∞ f)
    {g : M → ℝ} (hg : ContMDiff I 𝓘(ℝ) ∞ g)
    (hθ' : θ'.1 = θ.1 + mextDeriv (RoughForm.ofFunction I g)) :
    hσ.IsExactLagrangianMap J θ' f (h + g ∘ f) ↔ hσ.IsExactLagrangianMap J θ f h := by
  have hgf : ContMDiff J 𝓘(ℝ) ∞ (g ∘ f) := hg.comp hf
  have hgfd : MDifferentiable J 𝓘(ℝ) (g ∘ f) := hgf.mdifferentiable (by simp)
  -- `f^*θ' = f^*θ + d(g ∘ f)`.
  have hpull : mpullback J I f θ'.1 =
      mpullback J I f θ.1 + mextDeriv (RoughForm.ofFunction J (g ∘ f)) := by
    rw [hθ', mpullback_add, mpullback_mextDeriv_ofFunction (hf.mdifferentiable (by simp))
      (hg.mdifferentiable (by simp))]
  -- The primitive `h + g ∘ f` is smooth exactly when `h` is.
  have hsmooth : ContMDiff J 𝓘(ℝ) ∞ (h + g ∘ f) ↔ ContMDiff J 𝓘(ℝ) ∞ h :=
    ⟨fun hs ↦ by simpa using hs.sub hgf, fun hs ↦ hs.add hgf⟩
  simp only [isExactLagrangianMap_iff, hsmooth, hpull, and_congr_right_iff]
  intro _ hh
  rw [mextDeriv_ofFunction_add (hh.mdifferentiable (by simp)) hgfd, add_left_inj]

/-! ### Transport by exact symplectomorphisms -/

section Transport

variable {E₂ H₂ : Type*} [NormedAddCommGroup E₂] [NormedSpace ℝ E₂] [TopologicalSpace H₂]
  {I₂ : ModelWithCorners ℝ E₂ H₂} {M₂ : Type*} [TopologicalSpace M₂] [ChartedSpace H₂ M₂]
  [IsManifold I₂ ∞ M₂] {σ₂ : SmoothTwoForm I₂ M₂} {hσ₂ : σ₂.IsNondegenerate}
  {θ₂ : SmoothForm I₂ M₂ ℝ 1}

/-- A symplectomorphism `ψ` with `ψ^*σ₂ = σ` carries exact Lagrangian maps for `θ` to exact
Lagrangian maps for `θ₂`, with the same primitive, when it pulls `θ₂` back to `θ`. -/
theorem _root_.Diffeomorph.isExactLagrangianMap_comp_iff_of_mpullback_eq (ψ : M ≃ₘ⟮I, I₂⟯ M₂)
    (hψ : SmoothForm.mpullback ψ ψ.contMDiff σ₂ = σ)
    (hψθ : SmoothForm.mpullback ψ ψ.contMDiff θ₂ = θ) (hf : MDifferentiable J I f) :
    hσ₂.IsExactLagrangianMap J θ₂ (ψ ∘ f) h ↔ hσ.IsExactLagrangianMap J θ f h := by
  have hpull : mpullback J I₂ (ψ ∘ f) θ₂.1 = mpullback J I f θ.1 := by
    rw [mpullback_comp hf (ψ.mdifferentiable (by simp)), ← SmoothForm.coe_mpullback ψ ψ.contMDiff,
      hψθ]
  rw [isExactLagrangianMap_iff, isExactLagrangianMap_iff,
    isLagrangianMap_diffeomorph_comp_iff (hσ := hσ) ψ hψ, hpull]

/-- **Transport by exact symplectomorphisms.** Let `ψ : M → M₂` be a diffeomorphism with
`ψ^*σ₂ = σ` and `ψ^*θ₂ = θ + dg` for a smooth function `g` on `M`. Then `ψ ∘ f` is an exact
Lagrangian map for `θ₂` with primitive `h + g ∘ f` exactly when `f` is an exact Lagrangian map for
`θ` with primitive `h`. -/
theorem _root_.Diffeomorph.isExactLagrangianMap_comp_iff (ψ : M ≃ₘ⟮I, I₂⟯ M₂)
    (hψ : SmoothForm.mpullback ψ ψ.contMDiff σ₂ = σ) {g : M → ℝ} (hg : ContMDiff I 𝓘(ℝ) ∞ g)
    (hψθ : mpullback I I₂ ψ θ₂.1 = θ.1 + mextDeriv (RoughForm.ofFunction I g))
    (hf : ContMDiff J I ∞ f) :
    hσ₂.IsExactLagrangianMap J θ₂ (ψ ∘ f) (h + g ∘ f) ↔ hσ.IsExactLagrangianMap J θ f h := by
  rw [ψ.isExactLagrangianMap_comp_iff_of_mpullback_eq hψ rfl
      (hf.mdifferentiable (by simp)),
    isExactLagrangianMap_add_mextDeriv_iff (θ' := SmoothForm.mpullback ψ ψ.contMDiff θ₂) hf hg
      ((SmoothForm.coe_mpullback ..).trans hψθ)]

end Transport

end IsNondegenerate

end SmoothTwoForm

end TauCeti
