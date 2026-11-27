/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.MFDeriv.Basic
import Mathlib.Geometry.Manifold.MFDeriv.Atlas
import Mathlib.Geometry.Manifold.MFDeriv.SpecificFunctions

/-!
# Basic facts about manifold derivatives

This file collects general facts about `mfderiv` that need nothing beyond Mathlib's basic
manifold-derivative API and the derivatives of extended charts.

## Main results

* `TauCeti.mfderiv_comp_of_apply_eq_self`: the chain rule at a fixed point `f x = x` of the
  inner map, with both derivatives taken at `x`, so no cast between `T_(f x) M` and `T_x M` is
  needed.
* `TauCeti.mfderiv_apply_mfderiv_of_apply_eq_self_of_eventuallyEq`: if `f ∘ φ = R ∘ f` near a
  fixed point `x` of `φ`, with `R` continuous linear, then `df_x ∘ dφ_x = R ∘ df_x`.
* `HasMFDerivAt.iterate`: the chain rule for iterates at a fixed point, `d(f^[n])_x = (df_x) ^ n`.
* `TauCeti.mdifferentiableAt_iterate`: if `f` is differentiable at the first `n` points of the
  orbit of `x`, then `f^[n]` is differentiable at `x`.
* `TauCeti.mfderiv_injective_of_leftInverse`: a map with a left inverse differentiable along its
  image has injective derivative.
* `TauCeti.mfderiv_apply_mfderiv_of_eventuallyEq_comp`: if `Φ ∘ Ψ = κ` near `x`, then `dΦ` takes
  `dΨ(u)` to `dκ(u)`.
* `TauCeti.surjective_mfderiv_of_comp_eq`: a map `k` with `i₂ ∘ k = π ∘ j` along immersions `i₁`,
  `i₂` has surjective derivative when `dπ` is surjective and every tangent vector whose image under
  `dπ` is tangent to the image of `i₂` is carried by `di₁` into the image of `d(i₁ ∘ j)`.
* `TauCeti.mfderiv_comp_const_add_smul_apply`: the chain rule for the affine reparametrization
  `w ↦ c + ε • w` of a map from a normed space, `d(u(c + ε •))_w = ε • du_(c + ε • w)`, with no
  differentiability hypothesis.
* `TauCeti.finiteDimensional_of_injective_mfderiv`: a map into a finite-dimensional manifold
  whose differential is injective at some point has a finite-dimensional source model.
* `TauCeti.injective_mfderiv_of_injective_mfderiv_comp`: if `d(g ∘ f)_x` is injective and `f`, `g`
  are differentiable at `x`, `f x`, then `df_x` is injective.
* `TauCeti.injective_mfderiv_comp`: if `df_x` and `dg_(f x)` are injective, and `f`, `g` are
  differentiable at `x`, `f x`, then `d(g ∘ f)_x` is injective.
* `TauCeti.mfderiv_ne_zero_of_injective`: an injective differential out of a manifold with a
  nontrivial model space is nonzero.
* `TauCeti.injective_mfderiv_of_eventuallyEq_comp_extChartAt`: a map agreeing near `x` with
  `g ∘ extChartAt I x` has injective differential at `x` when `g` does at the chart image of `x`.
-/

public section

open scoped Manifold Topology

namespace TauCeti

variable {𝕜 E H M : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup E]
  [NormedSpace 𝕜 E] [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H} [TopologicalSpace M]
  [ChartedSpace H M] {x : M}

variable {E' H' N : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E'] [TopologicalSpace H']
  {J : ModelWithCorners 𝕜 E' H'} [TopologicalSpace N] [ChartedSpace H' N] in
/-- The chain rule at a fixed point: if `f x = x`, the derivative of `g ∘ f` at `x` is the
composite of the derivatives of `g` and `f` at `x`, the tangent space at `f x` being that at `x`. -/
theorem mfderiv_comp_of_apply_eq_self {f : M → M} {g : M → N} (hg : MDifferentiableAt I J g x)
    (hf : MDifferentiableAt I I f x) (hfx : f x = x) :
    mfderiv I J (g ∘ f) x = (mfderiv I J g x).comp (mfderiv I I f x) := by
  have h := mfderiv_comp_of_eq hg hf hfx
  -- `mfderiv_comp_of_eq` takes the derivative of `g` at `f x`; replace that point by `x`.
  generalize hz : f x = z at h
  obtain rfl : z = x := hz.symm.trans hfx
  exact h

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F] in
/-- **Linearizing a conjugacy at a fixed point.** If `f ∘ φ = R ∘ f` near a fixed point `x` of
`φ`, for a map `f` into a normed space and a continuous linear map `R`, then the differential of
`f` at `x` intertwines the differential of `φ` at `x` with `R`. -/
theorem mfderiv_apply_mfderiv_of_apply_eq_self_of_eventuallyEq {φ : M → M} {f : M → F}
    {R : F →L[𝕜] F} (hf : MDifferentiableAt I 𝓘(𝕜, F) f x) (hφ : MDifferentiableAt I I φ x)
    (hx : φ x = x) (hfφ : f ∘ φ =ᶠ[𝓝 x] R ∘ f) (v : TangentSpace I x) :
    mfderiv I 𝓘(𝕜, F) f x (mfderiv I I φ x v) = R (mfderiv I 𝓘(𝕜, F) f x v) := by
  have h := congr($(hfφ.mfderiv_eq (I := I) (I' := 𝓘(𝕜, F))) v)
  rwa [mfderiv_comp_of_apply_eq_self hf hφ hx, ContinuousLinearMap.comp_apply,
    mfderiv_comp_apply x R.mdifferentiableAt hf, R.mfderiv_eq] at h

/-- **The chain rule for iterates at a fixed point.** If `f x = x` and `f` has differential `f'`
at `x`, an endomorphism of `T_x M`, then `f^[n]` has differential `f' ^ n` at `x`. This is the
manifold version of `HasFDerivAt.iterate`. -/
theorem _root_.HasMFDerivAt.iterate {f : M → M} {f' : TangentSpace I x →L[𝕜] TangentSpace I x}
    (hf : HasMFDerivAt I I f x f') (hx : f x = x) (n : ℕ) :
    HasMFDerivAt I I f^[n] x (f' ^ n) := by
  induction n with
  | zero => exact hasMFDerivAt_id x
  | succ n ihn =>
    rw [Function.iterate_succ, pow_succ]
    -- Move the derivative of `f^[n]` to the point `f x`, where the chain rule evaluates it.
    have ihn' : HasMFDerivAt I I f^[n] (f x) (f' ^ n) := by rw [hx]; exact ihn
    exact ihn'.comp x hf

/-- **Iterates of a map differentiable along an orbit.** If `f` is differentiable at the points
`f^[m] x`, `m < n`, of the orbit of `x`, then `f^[n]` is differentiable at `x`. -/
theorem mdifferentiableAt_iterate {f : M → M} {n : ℕ}
    (hf : ∀ m < n, MDifferentiableAt I I f (f^[m] x)) : MDifferentiableAt I I f^[n] x := by
  induction n with
  | zero => exact mdifferentiableAt_id
  | succ n ih =>
    rw [Function.iterate_succ']
    exact (hf n n.lt_succ_self).comp x (ih fun m hm ↦ hf m (hm.trans n.lt_succ_self))

variable {E' H' N : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E'] [TopologicalSpace H']
  {J : ModelWithCorners 𝕜 E' H'} [TopologicalSpace N] [ChartedSpace H' N] in
/-- A map `f` with a left inverse `g` has injective derivative at every point `x` where `f` is
differentiable and `g` is differentiable at `f x`: by the chain rule, `dg_(f x)` is a left inverse
of `df_x`. -/
theorem mfderiv_injective_of_leftInverse {f : M → N} {g : N → M}
    (hg : MDifferentiableAt J I g (f x)) (hf : MDifferentiableAt I J f x)
    (hgf : Function.LeftInverse g f) : Function.Injective (mfderiv I J f x) := by
  have h := mfderiv_comp x hg hf
  rw [hgf.comp_eq_id, mfderiv_id] at h
  exact Function.LeftInverse.injective (g := mfderiv J I g (f x)) fun v ↦
    (DFunLike.congr_fun h v).symm

variable {E' H' N E'' H'' P : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
  [TopologicalSpace H'] {J : ModelWithCorners 𝕜 E' H'} [TopologicalSpace N] [ChartedSpace H' N]
  [NormedAddCommGroup E''] [NormedSpace 𝕜 E''] [TopologicalSpace H'']
  {K : ModelWithCorners 𝕜 E'' H''} [TopologicalSpace P] [ChartedSpace H'' P] in
/-- If `Φ ∘ Ψ = κ` on a neighbourhood of `x`, the differential of `Φ` at `Ψ x` takes `dΨ(u)` to
`dκ(u)`. -/
theorem mfderiv_apply_mfderiv_of_eventuallyEq_comp {Ψ : M → N} {Φ : N → P} {κ : M → P}
    (hΦΨ : Φ ∘ Ψ =ᶠ[𝓝 x] κ) (hΦ : MDifferentiableAt J K Φ (Ψ x))
    (hΨ : MDifferentiableAt I J Ψ x) (u : TangentSpace I x) :
    mfderiv J K Φ (Ψ x) (mfderiv I J Ψ x u) = mfderiv I K κ x u := by
  rw [← mfderiv_comp_apply x hΦ hΨ, hΦΨ.mfderiv_eq]
  -- The cast between the tangent spaces at `(Φ ∘ Ψ) x` and `κ x` is definitionally the identity.
  rfl

variable {E₁ H₁ M₁ E₂ H₂ M₂ F H' N F₂ H₂' N₂ : Type*}
  [NormedAddCommGroup E₁] [NormedSpace 𝕜 E₁] [TopologicalSpace H₁] {I₁ : ModelWithCorners 𝕜 E₁ H₁}
  [TopologicalSpace M₁] [ChartedSpace H₁ M₁]
  [NormedAddCommGroup E₂] [NormedSpace 𝕜 E₂] [TopologicalSpace H₂] {I₂ : ModelWithCorners 𝕜 E₂ H₂}
  [TopologicalSpace M₂] [ChartedSpace H₂ M₂]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F] [TopologicalSpace H'] {J : ModelWithCorners 𝕜 F H'}
  [TopologicalSpace N] [ChartedSpace H' N]
  [NormedAddCommGroup F₂] [NormedSpace 𝕜 F₂] [TopologicalSpace H₂'] {J₂ : ModelWithCorners 𝕜 F₂ H₂'}
  [TopologicalSpace N₂] [ChartedSpace H₂' N₂] in
/-- **Surjectivity of a derivative by a diagram chase.** Let `k : M → M₂` cover `π ∘ j`, for maps
`j : M → M₁` and `π : M₁ → N₂`, along `i₂ : M₂ → N₂`, that is `i₂ ∘ k = π ∘ j`, and let
`i₁ : M₁ → N` and `i₂` have injective derivatives. Suppose `dπ` is surjective at `j x`, and every
tangent vector `v` of `M₁` at `j x` with `dπ v` in the image of `di₂` has `di₁ v` in the image of
`d(i₁ ∘ j)`. Then `dk` is surjective at `x`. -/
theorem surjective_mfderiv_of_comp_eq {i₁ : M₁ → N} {i₂ : M₂ → N₂} {π : M₁ → N₂} {j : M → M₁}
    {k : M → M₂} (hj : MDifferentiableAt I I₁ j x) (hk : MDifferentiableAt I I₂ k x)
    (hi₁ : MDifferentiableAt I₁ J i₁ (j x)) (hi₂ : MDifferentiableAt I₂ J₂ i₂ (k x))
    (hπ : MDifferentiableAt I₁ J₂ π (j x)) (hik : i₂ ∘ k = π ∘ j)
    (hi₁inj : Function.Injective (mfderiv I₁ J i₁ (j x)))
    (hi₂inj : Function.Injective (mfderiv I₂ J₂ i₂ (k x)))
    (hπsurj : Function.Surjective (mfderiv I₁ J₂ π (j x)))
    (hkey : ∀ v w, mfderiv I₂ J₂ i₂ (k x) w = mfderiv I₁ J₂ π (j x) v →
      ∃ u, mfderiv I J (i₁ ∘ j) x u = mfderiv I₁ J i₁ (j x) v) :
    Function.Surjective (mfderiv I I₂ k x) := by
  intro w
  obtain ⟨v, hv⟩ := hπsurj (mfderiv I₂ J₂ i₂ (k x) w)
  obtain ⟨u, hu⟩ := hkey v w hv.symm
  -- `di₁ (dj u) = d(i₁ ∘ j) u = di₁ v`, so `dj u = v`, and then
  -- `di₂ (dk u) = dπ (dj u) = dπ v = di₂ w`.
  have hju : mfderiv I I₁ j x u = v := hi₁inj <| by
    rw [← mfderiv_comp_apply x hi₁ hj]
    exact hu
  refine ⟨u, hi₂inj ?_⟩
  rw [← mfderiv_comp_apply x hi₂ hk, hik, mfderiv_comp_apply x hπ hj, hju, hv]

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F] in
/-- **The derivative of an affine reparametrization.** For a map `u` from a normed space, the
derivative of `w ↦ u (c + ε • w)` at `w` is `ε` times the derivative of `u` at `c + ε • w`. No
differentiability is needed: for `ε ≠ 0` the reparametrization is invertible, so both maps are
differentiable or neither is, and for `ε = 0` the reparametrized map is constant. This is the
manifold version of `fderiv_comp_smul` and `fderiv_comp_add_left`. -/
theorem mfderiv_comp_const_add_smul_apply (u : F → M) (c w : F) (ε : 𝕜) (v : F) :
    mfderiv 𝓘(𝕜, F) I (fun w ↦ u (c + ε • w)) w v =
      ε • mfderiv 𝓘(𝕜, F) I u (c + ε • w) v := by
  rcases eq_or_ne ε 0 with rfl | hε
  · have h : (fun w ↦ u (c + (0 : 𝕜) • w)) = fun _ ↦ u c := by simp
    rw [h, mfderiv_const]
    exact (zero_smul 𝕜 (mfderiv 𝓘(𝕜, F) I u (c + (0 : 𝕜) • w) v)).symm
  have hφ : HasMFDerivAt 𝓘(𝕜, F) 𝓘(𝕜, F) (fun w ↦ c + ε • w) w
      (ε • ContinuousLinearMap.id 𝕜 F) :=
    (((hasFDerivAt_id w).const_smul ε).const_add c).hasMFDerivAt
  by_cases hu : MDifferentiableAt 𝓘(𝕜, F) I u (c + ε • w)
  · have h := (hu.hasMFDerivAt.comp w hφ).mfderiv
    rw [Function.comp_def] at h
    rw [h]
    exact map_smul (mfderiv 𝓘(𝕜, F) I u (c + ε • w)) ε v
  -- Otherwise neither map is differentiable: `u` is the reparametrized map composed with the
  -- inverse affine map `y ↦ ε⁻¹ • (y - c)`.
  have hu' : ¬MDifferentiableAt 𝓘(𝕜, F) I (fun w ↦ u (c + ε • w)) w := fun h ↦ by
    have hψ : MDifferentiableAt 𝓘(𝕜, F) 𝓘(𝕜, F) (fun y ↦ ε⁻¹ • (y - c)) (c + ε • w) :=
      ((differentiableAt_id.sub_const c).const_smul ε⁻¹).mdifferentiableAt
    have h' : MDifferentiableAt 𝓘(𝕜, F) I (fun w ↦ u (c + ε • w))
        (ε⁻¹ • ((c + ε • w) - c)) := by
      simpa [smul_smul, hε] using h
    exact hu (by simpa [Function.comp_def, smul_smul, hε] using h'.comp (c + ε • w) hψ)
  rw [mfderiv_zero_of_not_mdifferentiableAt hu, mfderiv_zero_of_not_mdifferentiableAt hu']
  exact (smul_zero ε).symm

variable {E' H' N : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E'] [FiniteDimensional 𝕜 E']
  [TopologicalSpace H'] {J : ModelWithCorners 𝕜 E' H'} [TopologicalSpace N] [ChartedSpace H' N] in
/-- A map into a finite-dimensional manifold whose differential is injective at some point has a
finite-dimensional model space. -/
theorem finiteDimensional_of_injective_mfderiv {f : M → N}
    (hinj : Function.Injective (mfderiv I J f x)) : FiniteDimensional 𝕜 E := by
  have : FiniteDimensional 𝕜 (TangentSpace I x) :=
    Module.Finite.of_injective (mfderiv I J f x).toLinearMap hinj
  exact (tangentSpaceCastModel I x).toLinearEquiv.finiteDimensional

variable {E' H' N E'' H'' P : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
  [TopologicalSpace H'] {J : ModelWithCorners 𝕜 E' H'} [TopologicalSpace N] [ChartedSpace H' N]
  [NormedAddCommGroup E''] [NormedSpace 𝕜 E''] [TopologicalSpace H'']
  {K : ModelWithCorners 𝕜 E'' H''} [TopologicalSpace P] [ChartedSpace H'' P] in
/-- If `g ∘ f` has injective differential at `x`, where `f` is differentiable at `x` and `g` at
`f x`, then `f` has injective differential at `x`: by the chain rule,
`d(g ∘ f)_x = dg_(f x) ∘ df_x`. -/
theorem injective_mfderiv_of_injective_mfderiv_comp {f : M → N} {g : N → P}
    (hg : MDifferentiableAt J K g (f x)) (hf : MDifferentiableAt I J f x)
    (hinj : Function.Injective (mfderiv I K (g ∘ f) x)) :
    Function.Injective (mfderiv I J f x) := by
  rw [mfderiv_comp x hg hf, ContinuousLinearMap.coe_comp] at hinj
  exact hinj.of_comp

variable {E' H' N E'' H'' P : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
  [TopologicalSpace H'] {J : ModelWithCorners 𝕜 E' H'} [TopologicalSpace N] [ChartedSpace H' N]
  [NormedAddCommGroup E''] [NormedSpace 𝕜 E''] [TopologicalSpace H'']
  {K : ModelWithCorners 𝕜 E'' H''} [TopologicalSpace P] [ChartedSpace H'' P] in
/-- If `f` has injective differential at `x` and `g` has injective differential at `f x`, where
`f` is differentiable at `x` and `g` at `f x`, then `g ∘ f` has injective differential at `x`: by
the chain rule, `d(g ∘ f)_x = dg_(f x) ∘ df_x`. -/
theorem injective_mfderiv_comp {f : M → N} {g : N → P}
    (hg : MDifferentiableAt J K g (f x)) (hf : MDifferentiableAt I J f x)
    (hginj : Function.Injective (mfderiv J K g (f x)))
    (hfinj : Function.Injective (mfderiv I J f x)) :
    Function.Injective (mfderiv I K (g ∘ f) x) := by
  rw [mfderiv_comp x hg hf, ContinuousLinearMap.coe_comp]
  exact hginj.comp hfinj

variable {E' H' N : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E'] [TopologicalSpace H']
  {J : ModelWithCorners 𝕜 E' H'} [TopologicalSpace N] [ChartedSpace H' N] in
/-- A map out of a manifold modelled on a nontrivial space whose differential at `x` is injective
has nonzero differential at `x`. -/
theorem mfderiv_ne_zero_of_injective [Nontrivial E] {f : M → N}
    (hinj : Function.Injective (mfderiv I J f x)) : mfderiv I J f x ≠ 0 := by
  -- The tangent space at `x` is the nontrivial model space, so the zero map is not injective.
  have : Nontrivial (TangentSpace I x) := ‹Nontrivial E›
  exact fun h0 ↦ LinearMap.ne_zero_of_injective hinj
    (by rw [h0, ContinuousLinearMap.toLinearMap_zero])

variable {E' H' N : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E'] [TopologicalSpace H']
  {J : ModelWithCorners 𝕜 E' H'} [TopologicalSpace N] [ChartedSpace H' N] in
/-- A map agreeing near `x` with `g ∘ φ`, for the extended chart `φ` at `x` and a map `g` on the
model space with injective differential at `φ x`, has injective differential at `x`: the
differential of `φ` at `x` is invertible. -/
theorem injective_mfderiv_of_eventuallyEq_comp_extChartAt [IsManifold I 1 M] {f : M → N}
    {g : E → N} (hgd : MDifferentiableAt 𝓘(𝕜, E) J g (extChartAt I x x))
    (hg : Function.Injective (mfderiv 𝓘(𝕜, E) J g (extChartAt I x x)))
    (hev : f =ᶠ[𝓝 x] g ∘ extChartAt I x) : Function.Injective (mfderiv I J f x) := by
  have hφ := (mdifferentiableAt_extChartAt (I := I) (mem_chart_source H x)).hasMFDerivAt
  rw [((hgd.hasMFDerivAt.comp x hφ).congr_of_eventuallyEq hev).mfderiv,
    ContinuousLinearMap.coe_comp, ContinuousLinearMap.coe_comp]
  refine (tangentSpaceCast _ _ _).injective.comp (hg.comp ?_)
  obtain ⟨A, hA⟩ := isInvertible_mfderiv_extChartAt (I := I) (mem_extChartAt_source x)
  rw [← hA]
  exact A.injective

end TauCeti
