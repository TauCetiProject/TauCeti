/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Contact.Contactization
public import TauCeti.Geometry.Contact.Standard
import TauCeti.Geometry.Contact.Slice
import TauCeti.Geometry.Manifold.Diffeomorph.Basic
import TauCeti.Geometry.Manifold.DifferentialForm.Naturality
import TauCeti.Geometry.Manifold.DifferentialForm.Poincare
import TauCeti.Geometry.Manifold.Immersion.Transverse
import TauCeti.Geometry.Manifold.LocalDiffeomorph.Constructions
import TauCeti.Geometry.Manifold.LocalDiffeomorph.MFDeriv
import TauCeti.Geometry.Manifold.LocalDiffeomorph.OpenSubset
import TauCeti.Geometry.Symplectic.Darboux.Standard

/-!
# Darboux's theorem for contact forms, with exact pullback

Let `α` be a contact form on a boundaryless smooth manifold `M` of dimension `2 n + 1`, and let
`α_std = dz - Σᵢ pᵢ dqᵢ` be the standard contact form on `ℝⁿ × ℝⁿ × ℝ`
(`TauCeti.innerProductContactForm`). **Darboux's theorem for the contact form** `α`
(`TauCeti.SmoothForm.IsContactForm.exists_strictDarbouxChart`) gives, around every point `x₀`, a
smooth chart `chart : M → ℝⁿ × ℝⁿ × ℝ` with `chart x₀ = 0` which pulls `α_std` back to `α` itself:

`α_std (chart x) (d chart_x v) = α x v` for every `x ∈ chart.source` and `v : T_x M`.

So `chart` is a strict contactomorphism onto its image. This strengthens the contact Darboux
theorem for contact structures (`TauCeti.SmoothForm.IsContactForm.exists_darbouxChart`), whose chart
only pulls `α_std` back to a positive multiple of `α`.

The proof follows the Reeb flow. Choose a hypersurface `ι : S → M` through `x₀` transverse to the
Reeb vector field `R_α` (`TauCeti.exists_contMDiff_notMem_range_mfderiv`), with `S = ℝ²ⁿ`. The local
Reeb flow map `Φ(s, t) = φₜ(ι s)` is a local diffeomorphism at `(0, 0)` and pulls `α` back to
`dt + β`, where `β = ι^* α` and `dβ` is nondegenerate at `0`
(`TauCeti.SmoothForm.IsContactForm.isLocalDiffeomorphAt_flowOf_reebVectorField_comp`,
`TauCeti.mpullback_flowOf_comp_apply_eq_contactization`). This is the contactization form of `-β`.

It remains to put such a contactization form `dt - θ` on `S × ℝ`, with `dθ` nondegenerate at a
point `y₀`, into standard form; this is
`TauCeti.exists_diffeomorph_eventually_mpullback_innerProductContactForm_eq_contactization`.
Darboux's theorem for the symplectic form `-dθ` gives coordinates `φ = (q, p)` on `S` near `y₀` in
which `-dθ = Σᵢ dqᵢ ∧ dpᵢ`. Then `θ - Σᵢ pᵢ dqᵢ` is closed near `y₀`, hence equal to `dg` for a
smooth function `g` there (`TauCeti.exists_mextDeriv_eq_nhds`), and the diffeomorphism
`(y, t) ↦ (q y, p y, t - g y)` of `S × ℝ` onto `ℝⁿ × ℝⁿ × ℝ` pulls `α_std` back to
`dt - dg - Σᵢ pᵢ dqᵢ = dt - θ` near `y₀`. Composing it with the inverse of the Reeb flow map gives
the chart.

## Main results

* `TauCeti.exists_diffeomorph_eventually_mpullback_innerProductContactForm_eq_contactization`: the
  contactization form `dt - θ` on `S × ℝ`, with `dθ` nondegenerate at `y₀`, is the pullback of the
  standard contact form along a diffeomorphism, near `{y₀} × ℝ`.
* `TauCeti.SmoothForm.IsContactForm.exists_strictDarbouxChart_of_finrank_eq`,
  `TauCeti.SmoothForm.IsContactForm.exists_strictDarbouxChart`: Darboux charts pulling the standard
  contact form back to a given contact form.

## References

* H. Geiges, *An Introduction to Contact Topology*, Cambridge University Press, 2008,
  Theorem 2.5.1 and its proof via the Reeb flow.
* V. I. Arnold, *Mathematical Methods of Classical Mechanics*, second edition, Appendix 4.
-/

public section

noncomputable section

open Set Module Filter Topology
open scoped Manifold ContDiff

namespace TauCeti

/-! ### Darboux coordinates for a contactization form -/

section Contactization

variable {S : Type*} [NormedAddCommGroup S] [NormedSpace ℝ S] {n : ℕ}

variable (n) in
/-- The inclusion `(q, p) ↦ (q, p, 0)` of `ℝⁿ × ℝⁿ` into `ℝⁿ × ℝⁿ × ℝ`. -/
private def zeroLastCLM :
    EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) →L[ℝ]
      EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) × ℝ :=
  (ContinuousLinearEquiv.prodAssoc ℝ (EuclideanSpace ℝ (Fin n)) (EuclideanSpace ℝ (Fin n))
    ℝ).toContinuousLinearMap ∘L ContinuousLinearMap.inl ℝ _ ℝ

variable (n) in
/-- The inclusion `z ↦ (0, 0, z)` of `ℝ` into `ℝⁿ × ℝⁿ × ℝ`. -/
private def lastCLM : ℝ →L[ℝ] EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) × ℝ :=
  (ContinuousLinearEquiv.prodAssoc ℝ (EuclideanSpace ℝ (Fin n)) (EuclideanSpace ℝ (Fin n))
    ℝ).toContinuousLinearMap ∘L ContinuousLinearMap.inr ℝ _ ℝ

private theorem zeroLastCLM_add_lastCLM (a : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n))
    (z : ℝ) : zeroLastCLM n a + lastCLM n z = (a.1, a.2, z) := by
  refine Prod.ext ?_ (Prod.ext ?_ ?_) <;> simp [zeroLastCLM, lastCLM]

/-- The standard contact form at `(q, p, z)` on a vector `(a, 0)` is `-⟪p, a.1⟫`. -/
private theorem innerProductContactForm_zeroLastCLM
    (x a : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)) :
    (innerProductContactForm (EuclideanSpace ℝ (Fin n))).1 (zeroLastCLM n x)
      ![zeroLastCLM n a] = -inner ℝ x.2 a.1 := by
  -- `zeroLastCLM` inserts a zero last coordinate and keeps the first two.
  exact (innerProductContactForm_apply _ _ _).trans (zero_sub (inner ℝ x.2 a.1))

/-- The one-form `-Σᵢ pᵢ dqᵢ` on `S` for coordinates `φ = (q, p) : S ≃ ℝⁿ × ℝⁿ`: the pullback of the
standard contact form along `y ↦ (q y, p y, 0)`. -/
private def coordForm
    (φ : S ≃ₘ⟮𝓘(ℝ, S), 𝓘(ℝ, EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n))⟯
      EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)) : SmoothForm 𝓘(ℝ, S) S ℝ 1 :=
  SmoothForm.mpullback (zeroLastCLM n ∘ φ) ((zeroLastCLM n).contDiff.contMDiff.comp φ.contMDiff)
    (innerProductContactForm (EuclideanSpace ℝ (Fin n)))

private theorem mfderiv_zeroLastCLM_comp
    (φ : S ≃ₘ⟮𝓘(ℝ, S), 𝓘(ℝ, EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n))⟯
      EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)) (y u : S) :
    mfderiv 𝓘(ℝ, S) 𝓘(ℝ, EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) × ℝ)
      (zeroLastCLM n ∘ φ) y u = zeroLastCLM n (fderiv ℝ φ y u) := by
  rw [mfderiv_eq_fderiv, ((zeroLastCLM n).hasFDerivAt.comp y
    ((contMDiff_iff_contDiff.1 φ.contMDiff).differentiable (by simp) y).hasFDerivAt).fderiv]
  -- The remaining `NormedSpace.fromTangentSpace` identifications are identities.
  rfl

private theorem coordForm_apply
    (φ : S ≃ₘ⟮𝓘(ℝ, S), 𝓘(ℝ, EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n))⟯
      EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)) (y u : S) :
    (coordForm φ).1 y ![u] = -inner ℝ (φ y).2 (fderiv ℝ φ y u).1 := by
  rw [coordForm, SmoothForm.mpullback_apply_one _ _ _ y u, Function.comp_apply,
    mfderiv_zeroLastCLM_comp]
  exact innerProductContactForm_zeroLastCLM (φ y) _

/-- The exterior derivative of `-Σᵢ pᵢ dqᵢ` is `Σᵢ dqᵢ ∧ dpᵢ`, read through `dφ`. -/
private theorem mextDeriv_coordForm_apply
    (φ : S ≃ₘ⟮𝓘(ℝ, S), 𝓘(ℝ, EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n))⟯
      EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)) (y u w : S) :
    mextDeriv (coordForm φ).1 y ![u, w] =
      stdSymplecticForm (fderiv ℝ φ y u) (fderiv ℝ φ y w) := by
  rw [coordForm, SmoothForm.mextDeriv_mpullback_apply_two _ _ _ y u w,
    mextDeriv_innerProductContactForm_apply, Function.comp_apply, mfderiv_zeroLastCLM_comp,
    mfderiv_zeroLastCLM_comp]
  -- `zeroLastCLM` keeps the first two coordinates.
  rfl

variable [FiniteDimensional ℝ S]

/-- **Darboux coordinates with a primitive.** Let `θ` be a smooth one-form on a vector space `S`
of dimension `2 n` whose exterior derivative is nondegenerate at `y₀`. There are coordinates
`φ = (q, p) : S ≃ ℝⁿ × ℝⁿ` centred at `y₀` and a smooth function `g` with `g y₀ = 0` such that
`θ = dg + Σᵢ pᵢ dqᵢ` near `y₀`. -/
private theorem exists_diffeomorph_eventually_fderiv_eq (hS : finrank ℝ S = 2 * n)
    (θ : SmoothForm 𝓘(ℝ, S) S ℝ 1) {y₀ : S}
    (hθ : ((-mextDerivₗ 𝓘(ℝ, S) 1 θ).bilinFormAt y₀).Nondegenerate) :
    ∃ (φ : S ≃ₘ⟮𝓘(ℝ, S), 𝓘(ℝ, EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n))⟯
        EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)) (g : S → ℝ),
      φ y₀ = 0 ∧ g y₀ = 0 ∧ ContDiff ℝ ∞ g ∧ ∀ᶠ y in 𝓝 y₀, ∀ u : S,
        fderiv ℝ g y u = θ.1 y ![u] - inner ℝ (φ y).2 (fderiv ℝ φ y u).1 := by
  -- Darboux's theorem for the symplectic form `ϖ = -dθ`.
  set ϖ : S → S [⋀^Fin 2]→L[ℝ] ℝ := extDeriv (E := S) (F := ℝ) (-θ).1
  have hθs : ContDiff ℝ ∞ (E := S) (F := S [⋀^Fin 1]→L[ℝ] ℝ) (-θ).1 :=
    isSmoothForm_modelSpace_iff.1 (-θ).isSmoothForm
  have hϖθ (y : S) : ϖ y = ((-mextDerivₗ 𝓘(ℝ, S) 1 θ : SmoothForm 𝓘(ℝ, S) S ℝ 2) :
      RoughForm 𝓘(ℝ, S) S ℝ 2) y := by
    rw [← map_neg, mextDerivₗ_apply, mextDeriv_eq_extDeriv]
  obtain ⟨φ, hφ0, hφ⟩ := exists_diffeomorph_eventually_stdSymplecticForm_fderiv_eq (V := S)
    (n := n) (r := ⊤) hS le_top isOpen_univ (mem_univ y₀)
    (contDiffOn_extDeriv hθs.contDiffOn isOpen_univ (by simp))
    (fun y _ ↦ by rw [extDeriv_extDeriv hθs (by simp)]; rfl)
    (fun u hu ↦ hθ.1 u fun w ↦ (SmoothForm.bilinFormAt_apply _ y₀ u w).trans
      ((SmoothBundleForm.eval₂_apply _ y₀ u w).trans ((congrArg (· ![u, w]) (hϖθ y₀)).symm.trans
        (hu w))))
  -- The one-form `γ = θ + coordForm φ = θ - Σᵢ pᵢ dqᵢ` is closed near `y₀`, since
  -- `d(coordForm φ) = φ^* (Σᵢ dqᵢ ∧ dpᵢ) = ϖ = -dθ` there.
  set γ : SmoothForm 𝓘(ℝ, S) S ℝ 1 := θ + coordForm φ
  have hγc : ∀ᶠ y in 𝓝 y₀, mextDeriv γ.1 y = 0 := by
    filter_upwards [hφ] with y hy
    have h := congrArg (fun ψ : SmoothForm 𝓘(ℝ, S) S ℝ 2 ↦ (ψ : RoughForm 𝓘(ℝ, S) S ℝ 2) y)
      (map_add (mextDerivₗ 𝓘(ℝ, S) 1) θ (coordForm φ))
    simp only [mextDerivₗ_apply] at h
    ext m
    have hm : m = ![m 0, m 1] := by
      funext i
      fin_cases i <;> rfl
    have hϖ := (hy.2 (m 0) (m 1)).trans (congrArg (· ![m 0, m 1]) (hϖθ y))
    simp only [Submodule.coe_neg, Pi.neg_apply, mextDerivₗ_apply] at hϖ
    rw [hm, _root_.ContinuousAlternatingMap.coe_zero, Pi.zero_apply]
    refine (congrArg (· ![m 0, m 1]) h).trans ?_
    rw [Submodule.coe_add, Pi.add_apply, ContinuousAlternatingMap.add_apply, mextDerivₗ_apply,
      mextDerivₗ_apply, mextDeriv_coordForm_apply φ y (m 0) (m 1)]
    exact (add_eq_zero_iff_neg_eq).2 hϖ.symm
  -- A smooth primitive of `γ` near `y₀`, normalized to vanish at `y₀`.
  obtain ⟨U, hU, ψ, hψs, hψ⟩ := exists_mextDeriv_eq_nhds (r := ⊤) le_top γ.isSmoothForm hγc
  rw [RoughForm.eq_ofFunction ψ, isSmoothForm_ofFunction_iff] at hψs
  set g : S → ℝ := fun y ↦ ψ y 0 - ψ y₀ 0
  have hg : ContDiff ℝ ∞ g := contMDiff_iff_contDiff.1 (hψs.sub contMDiff_const)
  refine ⟨φ, g, hφ0, sub_self _, hg, ?_⟩
  filter_upwards [hU] with y hy u
  have h := congrArg (· ![u]) (hψ y hy)
  rw [RoughForm.eq_ofFunction ψ, mextDeriv_ofFunction_apply (fun x ↦ ψ x 0) y u, Submodule.coe_add,
    Pi.add_apply, ContinuousAlternatingMap.add_apply, coordForm_apply, ← sub_eq_add_neg] at h
  have hgy : HasFDerivAt g (fderiv ℝ (fun x ↦ ψ x 0) y) y :=
    ((contMDiff_iff_contDiff.1 hψs).differentiable (by simp) y).hasFDerivAt.sub_const (ψ y₀ 0)
  rw [← h, hgy.fderiv, mfderiv_eq_fderiv]
  -- The remaining `NormedSpace.fromTangentSpace` identifications are identities.
  rfl

omit [FiniteDimensional ℝ S] in
/-- The diffeomorphism `(y, t) ↦ (q y, p y, t - g y)` of `S × ℝ` onto `ℝⁿ × ℝⁿ × ℝ`, for
coordinates `φ = (q, p)` on `S` and a smooth function `g`. -/
private def shiftDiffeomorph
    (φ : S ≃ₘ⟮𝓘(ℝ, S), 𝓘(ℝ, EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n))⟯
      EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)) {g : S → ℝ} (hg : ContDiff ℝ ∞ g) :
    (S × ℝ) ≃ₘ⟮𝓘(ℝ, S).prod 𝓘(ℝ), 𝓘(ℝ, EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) × ℝ)⟯
      EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) × ℝ where
  toFun p := zeroLastCLM n (φ p.1) + lastCLM n (p.2 - g p.1)
  invFun z := (φ.symm (z.1, z.2.1), z.2.2 + g (φ.symm (z.1, z.2.1)))
  left_inv p := by simp [zeroLastCLM_add_lastCLM, -map_sub]
  right_inv z := by simp [zeroLastCLM_add_lastCLM]
  contMDiff_toFun := ((zeroLastCLM n).contDiff.contMDiff.comp (φ.contMDiff.comp contMDiff_fst)).add
    ((lastCLM n).contDiff.contMDiff.comp (contMDiff_snd.sub (hg.contMDiff.comp contMDiff_fst)))
  contMDiff_invFun := by
    have h : ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) × ℝ) 𝓘(ℝ, S) ∞
        fun z : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) × ℝ ↦ φ.symm (z.1, z.2.1) :=
      φ.symm.contMDiff.comp (contDiff_fst.prodMk (contDiff_fst.comp contDiff_snd)).contMDiff
    exact h.prodMk ((contDiff_snd.comp contDiff_snd).contMDiff.add (hg.contMDiff.comp h))

omit [FiniteDimensional ℝ S] in
private theorem shiftDiffeomorph_apply
    (φ : S ≃ₘ⟮𝓘(ℝ, S), 𝓘(ℝ, EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n))⟯
      EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)) {g : S → ℝ} (hg : ContDiff ℝ ∞ g)
    (p : S × ℝ) : shiftDiffeomorph φ hg p = ((φ p.1).1, (φ p.1).2, p.2 - g p.1) :=
  zeroLastCLM_add_lastCLM _ _

omit [FiniteDimensional ℝ S] in
/-- The shift diffeomorphism pulls the standard contact form back to `dt - dg - Σᵢ pᵢ dqᵢ`. -/
private theorem innerProductContactForm_shiftDiffeomorph
    (φ : S ≃ₘ⟮𝓘(ℝ, S), 𝓘(ℝ, EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n))⟯
      EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)) {g : S → ℝ} (hg : ContDiff ℝ ∞ g)
    (p : S × ℝ) (w : TangentSpace (𝓘(ℝ, S).prod 𝓘(ℝ)) p) :
    (innerProductContactForm (EuclideanSpace ℝ (Fin n))).1 (shiftDiffeomorph φ hg p)
      ![mfderiv (𝓘(ℝ, S).prod 𝓘(ℝ))
        𝓘(ℝ, EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) × ℝ) (shiftDiffeomorph φ hg) p w] =
      w.2 - fderiv ℝ g p.1 w.1 - inner ℝ (φ p.1).2 (fderiv ℝ φ p.1 w.1).1 := by
  have hφd : ContDiff ℝ ∞ φ := contMDiff_iff_contDiff.1 φ.contMDiff
  -- The differential of the shift, as a sum of the two summands of its definition.
  have h1 : HasMFDerivAt (𝓘(ℝ, S).prod 𝓘(ℝ))
      𝓘(ℝ, EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) × ℝ)
      (fun p : S × ℝ ↦ zeroLastCLM n (φ p.1)) p
      (zeroLastCLM n ∘L fderiv ℝ φ p.1 ∘L ContinuousLinearMap.fst ℝ S ℝ) :=
    (zeroLastCLM n).hasMFDerivAt.comp p
      ((((hφd.differentiable (by simp)) p.1).hasFDerivAt.hasMFDerivAt).comp p (hasMFDerivAt_fst p))
  have h2 : HasMFDerivAt (𝓘(ℝ, S).prod 𝓘(ℝ))
      𝓘(ℝ, EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) × ℝ)
      (fun p : S × ℝ ↦ lastCLM n (p.2 - g p.1)) p
      (lastCLM n ∘L
        (ContinuousLinearMap.snd ℝ S ℝ - fderiv ℝ g p.1 ∘L ContinuousLinearMap.fst ℝ S ℝ)) :=
    (lastCLM n).hasMFDerivAt.comp p ((hasMFDerivAt_snd p).sub
      ((((hg.differentiable (by simp)) p.1).hasFDerivAt.hasMFDerivAt).comp p (hasMFDerivAt_fst p)))
  have hG : HasMFDerivAt (𝓘(ℝ, S).prod 𝓘(ℝ))
      𝓘(ℝ, EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) × ℝ) (shiftDiffeomorph φ hg) p _ :=
    h1.add h2
  rw [hG.mfderiv, innerProductContactForm_apply, shiftDiffeomorph_apply]
  -- The differential sends `w` to `(dφ w.1, w.2 - dg w.1)`.
  have hw := zeroLastCLM_add_lastCLM (fderiv ℝ φ p.1 w.1) (w.2 - fderiv ℝ g p.1 w.1)
  exact congrArg (fun z ↦ z.2.2 - inner ℝ (φ p.1).2 z.1) hw

/-- **Darboux coordinates for a contactization.** Let `θ` be a smooth one-form on a vector space
`S` of dimension `2 n` whose exterior derivative is nondegenerate at `y₀`, so that the
contactization form `dt - θ` on `S × ℝ` (`TauCeti.SmoothForm.contactization`) is a contact form
along `{y₀} × ℝ`. Then some diffeomorphism `G : S × ℝ ≃ ℝⁿ × ℝⁿ × ℝ` with `G (y₀, 0) = 0` pulls the
standard contact form `dz - Σᵢ pᵢ dqᵢ` back to `dt - θ` at every point `(y, t)` with `y` near
`y₀`. -/
theorem exists_diffeomorph_eventually_mpullback_innerProductContactForm_eq_contactization
    (hS : finrank ℝ S = 2 * n) (θ : SmoothForm 𝓘(ℝ, S) S ℝ 1) {y₀ : S}
    (hθ : ((-mextDerivₗ 𝓘(ℝ, S) 1 θ).bilinFormAt y₀).Nondegenerate) :
    ∃ G : (S × ℝ) ≃ₘ⟮𝓘(ℝ, S).prod 𝓘(ℝ),
        𝓘(ℝ, EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) × ℝ)⟯
        EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) × ℝ,
      G (y₀, 0) = 0 ∧ ∀ᶠ y in 𝓝 y₀, ∀ t : ℝ,
        mpullback (𝓘(ℝ, S).prod 𝓘(ℝ)) 𝓘(ℝ, EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) × ℝ)
          G (innerProductContactForm (EuclideanSpace ℝ (Fin n))).1 (y, t) =
          θ.contactization.1 (y, t) := by
  obtain ⟨φ, g, hφ0, hg0, hg, hdg⟩ := exists_diffeomorph_eventually_fderiv_eq hS θ hθ
  refine ⟨shiftDiffeomorph φ hg, by simp [shiftDiffeomorph_apply, hφ0, hg0], ?_⟩
  filter_upwards [hdg] with y hy t
  ext m
  have hm : m = ![m 0] := by
    funext i
    fin_cases i
    rfl
  rw [hm, mpullback_apply, SmoothForm.contactization_apply]
  have hvec : (fun i ↦ mfderiv (𝓘(ℝ, S).prod 𝓘(ℝ))
      𝓘(ℝ, EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) × ℝ) (shiftDiffeomorph φ hg) (y, t)
        ((![m 0] : Fin 1 → TangentSpace (𝓘(ℝ, S).prod 𝓘(ℝ)) (y, t)) i)) =
      ![mfderiv (𝓘(ℝ, S).prod 𝓘(ℝ))
        𝓘(ℝ, EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) × ℝ) (shiftDiffeomorph φ hg) (y, t)
          (m 0)] := by
    funext i
    fin_cases i
    rfl
  rw [hvec, innerProductContactForm_shiftDiffeomorph, hy,
    Manifold.tangentSpaceProdEquiv_apply (y, t) (m 0), NormedSpace.fromTangentSpace_apply]
  ring

end Contactization

/-! ### Darboux charts for contact forms on manifolds -/

section Manifold

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]

/-- Let `Φ : N → M` be a local diffeomorphism at `p₀` and `G : N ≃ F` a diffeomorphism onto a
normed space. If, on an open neighbourhood `O` of `p₀`, `Φ` is differentiable and `G` and `Φ` pull
the one-forms `σ` on `F` and `α` on `M` back to the same form, then `G ∘ Φ⁻¹` is a chart near
`Φ p₀` pulling `σ` back to `α`. -/
private theorem exists_partialDiffeomorph_apply_mvfderiv_eq {E' H' N F : Type*}
    [NormedAddCommGroup E'] [NormedSpace ℝ E'] [TopologicalSpace H'] {J : ModelWithCorners ℝ E' H'}
    [TopologicalSpace N] [ChartedSpace H' N] [NormedAddCommGroup F]
    [NormedSpace ℝ F] {Φ : N → M} {p₀ : N} (hΦ : IsLocalDiffeomorphAt J I ∞ Φ p₀)
    (G : N ≃ₘ⟮J, 𝓘(ℝ, F)⟯ F) {α : RoughForm I M ℝ 1} {σ : RoughForm 𝓘(ℝ, F) F ℝ 1} {O : Set N}
    (hO : IsOpen O) (hp₀ : p₀ ∈ O) (hΦd : ∀ p ∈ O, MDifferentiableAt J I Φ p)
    (h : ∀ p ∈ O, mpullback J 𝓘(ℝ, F) G σ p = mpullback J I Φ α p) :
    ∃ chart : PartialDiffeomorph I 𝓘(ℝ, F) M F ∞, Φ p₀ ∈ chart.source ∧ chart (Φ p₀) = G p₀ ∧
      ∀ x ∈ chart.source, ∀ v : TangentSpace I x,
        σ (chart x) ![mvfderiv I chart x v] = α x ![v] := by
  set Ψ := hΦ.localInverse
  set s : Set M := Ψ.source ∩ Ψ ⁻¹' O
  have hs : IsOpen s := Ψ.contMDiffOn_toFun.continuousOn.isOpen_inter_preimage Ψ.open_source hO
  have hΨp₀ : Ψ (Φ p₀) = p₀ := hΦ.localInverse_left_inv hΦ.localInverse_mem_target
  have hcoe : ⇑((Ψ.restrOpen s hs).trans G.toPartialDiffeomorph) = G ∘ Ψ := by
    rw [PartialDiffeomorph.coe_trans, PartialDiffeomorph.coe_restrOpen,
      Diffeomorph.toPartialDiffeomorph_toPartialEquiv, Equiv.toPartialEquiv_apply,
      Diffeomorph.coe_toEquiv]
  refine ⟨(Ψ.restrOpen s hs).trans G.toPartialDiffeomorph, ?_, by simp [hΨp₀],
    fun x hx v ↦ ?_⟩
  · rw [PartialDiffeomorph.trans_source, PartialDiffeomorph.restrOpen_source]
    refine ⟨⟨hΦ.localInverse_mem_source, hΦ.localInverse_mem_source, ?_⟩, ?_⟩
    · rwa [mem_preimage, hΨp₀]
    · simp [Diffeomorph.toPartialDiffeomorph_toPartialEquiv]
  rw [PartialDiffeomorph.trans_source, PartialDiffeomorph.restrOpen_source] at hx
  obtain ⟨⟨hxΨ, -, hxO⟩, -⟩ := hx
  have hΨd : MDifferentiableAt I J Ψ x := Ψ.mdifferentiableAt (by simp) hxΨ
  -- `dΦ ∘ dΨ = id` at `x`, since `Φ ∘ Ψ = id` on the source of `Ψ`.
  have hinv : mfderiv J I Φ (Ψ x) (mfderiv I J Ψ x v) = v := by
    have hev : Φ ∘ Ψ =ᶠ[𝓝 x] id :=
      Filter.eventuallyEq_of_mem (Ψ.open_source.mem_nhds hxΨ) hΦ.localInverse_eqOn_right
    have h' := hev.mfderiv_eq (I := I) (I' := I)
    rw [mfderiv_comp x (hΦd _ hxO) hΨd, mfderiv_id] at h'
    exact congrArg (· v) h'
  have key := congrArg (· ![mfderiv I J Ψ x v]) (h (Ψ x) hxO)
  simp only [TauCeti.mpullback_apply] at key
  have hvecG : (fun i ↦ mfderiv J 𝓘(ℝ, F) G (Ψ x)
      ((![mfderiv I J Ψ x v] : Fin 1 → TangentSpace J (Ψ x)) i)) =
      ![mfderiv J 𝓘(ℝ, F) G (Ψ x) (mfderiv I J Ψ x v)] := by
    funext i
    fin_cases i
    rfl
  have hvecΦ : (fun i ↦ mfderiv J I Φ (Ψ x)
      ((![mfderiv I J Ψ x v] : Fin 1 → TangentSpace J (Ψ x)) i)) = ![v] := by
    funext i
    fin_cases i
    exact hinv
  rw [hvecG, hvecΦ, hΦ.localInverse_right_inv hxΨ] at key
  rw [hcoe, mvfderiv, ContinuousLinearMap.comp_apply,
    mfderiv_comp x (G.contMDiff.mdifferentiableAt (by simp)) hΨd]
  exact key

variable [FiniteDimensional ℝ E] [I.Boundaryless] [T2Space M] [IsManifold I ∞ M]

/-- **Darboux's theorem for contact forms, with exact pullback**, in dimension `2 n + 1`. Let `α`
be a smooth contact form on a boundaryless manifold of dimension `2 n + 1`. Around every point
`x₀` there is a smooth chart `chart : M → ℝⁿ × ℝⁿ × ℝ` with `chart x₀ = 0` which pulls the standard
contact form `dz - Σᵢ pᵢ dqᵢ` back to `α` on `chart.source`. -/
theorem SmoothForm.IsContactForm.exists_strictDarbouxChart_of_finrank_eq
    {α : SmoothForm I M ℝ 1} (hα : α.IsContactForm) {n : ℕ} (hn : finrank ℝ E = 2 * n + 1)
    (x₀ : M) :
    ∃ chart : PartialDiffeomorph I
        𝓘(ℝ, EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) × ℝ) M
        (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) × ℝ) ∞,
      x₀ ∈ chart.source ∧ chart x₀ = 0 ∧ ∀ x ∈ chart.source, ∀ v : TangentSpace I x,
        (innerProductContactForm (EuclideanSpace ℝ (Fin n))).1 (chart x)
          ![mvfderiv I chart x v] = α.1 x ![v] := by
  set S := EuclideanSpace ℝ (Fin (2 * n))
  set R := α.reebVectorField
  have hRs := hα.contMDiff_reebVectorField
  -- A slice `ι : S → M` through `x₀` transverse to the Reeb vector field.
  have hR0 : R x₀ ≠ 0 := fun h ↦ by
    have h1 := hα.apply_reebVectorField x₀
    rw [show α.reebVectorField x₀ = 0 from h, (α.1 x₀).map_coord_zero (m := ![0]) 0 rfl] at h1
    exact zero_ne_one h1
  obtain ⟨ι, hι, hι0, hιinj, hιR⟩ := exists_contMDiff_notMem_range_mfderiv (m := 2 * n)
    (by omega) (BoundarylessManifold.isInteriorPoint (I := I) (x := x₀)) hR0
  have hdimS : finrank ℝ S + 1 = finrank ℝ E := by simp [S, hn]
  -- The local Reeb flow map `Φ (s, t) = φₜ (ι s)` is a local diffeomorphism at `(0, 0)` and pulls
  -- `α` back to the contactization form `dt + β` of `-β`, where `β = ι^* α` and `dβ` is
  -- nondegenerate at `0`.
  set Φ : S × ℝ → M := fun q ↦ flowOf R q.2 (ι q.1)
  have hdom0 : ((0 : ℝ), ι 0) ∈ flowDomain R := mem_flowDomain_zero (hRs.of_le (by simp)) _
  have hΦ := hα.isLocalDiffeomorphAt_flowOf_reebVectorField_comp hι hdimS
    (p := (0 : S × ℝ)) hιinj (by rw [Prod.fst_zero, hι0]; exact hιR) hdom0
  set β := SmoothForm.mpullback ι hι α
  have hnd : ((-mextDerivₗ 𝓘(ℝ, S) 1 (-β)).bilinFormAt 0).Nondegenerate := by
    rw [map_neg, neg_neg]
    exact hα.nondegenerate_bilinFormAt_mextDerivₗ_mpullback hι hdimS hιinj (by rwa [hι0])
  -- Darboux coordinates `G` for `dt + β`, valid over an open neighbourhood `U` of `0`.
  obtain ⟨G, hG0, hG⟩ :=
    exists_diffeomorph_eventually_mpullback_innerProductContactForm_eq_contactization (n := n)
      (by simp) (-β) hnd
  obtain ⟨U, hUG, hUo, hU0⟩ := eventually_nhds_iff.1 hG
  -- On the open set `O` of points over `U` in the flow domain, `G^* α_std = dt + β = Φ^* α`.
  have hO : IsOpen {p : S × ℝ | p.1 ∈ U ∧ (p.2, ι p.1) ∈ flowDomain R} :=
    (hUo.preimage continuous_fst).inter (isOpen_setOf_mem_flowDomain (hRs.of_le (by simp))
      continuous_snd (hι.continuous.comp continuous_fst))
  obtain ⟨chart, hsrc, hchart, hpull⟩ := exists_partialDiffeomorph_apply_mvfderiv_eq hΦ G
    (σ := (innerProductContactForm (EuclideanSpace ℝ (Fin n))).1) (α := α.1) hO ⟨hU0, hdom0⟩
    (fun p hp ↦ (contMDiffAt_flowOf_comp (n := 1) le_rfl (hRs.of_le (by simp)) contMDiffAt_snd
      ((hι.contMDiffAt.of_le (by simp)).comp _ contMDiffAt_fst) hp.2).mdifferentiableAt
        one_ne_zero)
    (fun p hp ↦ (hUG p.1 hp.1 p.2).trans (mpullback_flowOf_comp_apply_eq_contactization hRs hι
      hα.apply_reebVectorField hα.interior_mextDeriv_reebVectorField hp.2).symm)
  have hΦ0 : Φ 0 = x₀ := by simp [Φ, hι0]
  exact ⟨chart, hΦ0 ▸ hsrc, by rw [← hΦ0, hchart]; exact hG0, hpull⟩

/-- **Darboux's theorem for contact forms, with exact pullback.** Let `α` be a smooth contact form
on a boundaryless manifold. Then `M` has dimension `2 n + 1` for some `n`, and around every point
`x₀` there is a smooth chart `chart : M → ℝⁿ × ℝⁿ × ℝ` with `chart x₀ = 0` which pulls the standard
contact form `dz - Σᵢ pᵢ dqᵢ` back to `α` on `chart.source`. -/
theorem SmoothForm.IsContactForm.exists_strictDarbouxChart {α : SmoothForm I M ℝ 1}
    (hα : α.IsContactForm) (x₀ : M) :
    ∃ (n : ℕ) (chart : PartialDiffeomorph I
        𝓘(ℝ, EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) × ℝ) M
        (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) × ℝ) ∞),
      finrank ℝ E = 2 * n + 1 ∧ x₀ ∈ chart.source ∧ chart x₀ = 0 ∧
      ∀ x ∈ chart.source, ∀ v : TangentSpace I x,
        (innerProductContactForm (EuclideanSpace ℝ (Fin n))).1 (chart x)
          ![mvfderiv I chart x v] = α.1 x ![v] := by
  obtain ⟨n, hn⟩ := hα.odd_finrank x₀
  obtain ⟨chart, h⟩ := hα.exists_strictDarbouxChart_of_finrank_eq hn x₀
  exact ⟨n, chart, hn, h⟩

end Manifold

end TauCeti
