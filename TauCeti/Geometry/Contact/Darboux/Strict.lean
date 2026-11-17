/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Contact.Slice
public import TauCeti.Geometry.Contact.Standard
import TauCeti.Geometry.Symplectic.Darboux.Standard
import TauCeti.Geometry.Manifold.ContMDiff.Parametrization
import TauCeti.Geometry.Manifold.Diffeomorph.Basic
import TauCeti.Geometry.Manifold.DifferentialForm.Poincare
import TauCeti.Geometry.Manifold.DifferentialForm.Naturality
import TauCeti.Geometry.Manifold.LocalDiffeomorph.MFDeriv
import TauCeti.Geometry.Manifold.LocalDiffeomorph.OpenSubset
import TauCeti.Geometry.Manifold.MFDeriv.NormedSpace

/-!
# Darboux's theorem for contact forms

Let `α` be a smooth contact form on a boundaryless manifold `M` of dimension `2 n + 1`. **Darboux's
theorem for contact forms** (`TauCeti.SmoothForm.IsContactForm.exists_strictDarbouxChart` and
`TauCeti.SmoothForm.IsContactForm.exists_strictDarbouxChart_of_finrank_eq`) gives, around every
point `x₀`, a smooth partial diffeomorphism `chart` onto an open subset of `ℝⁿ × ℝⁿ × ℝ` with
`chart x₀ = 0` such that for every `x ∈ chart.source` and `v : T_x M`,

`α_std (chart x) (d chart_x v) = α x v`,

where `α_std = dz - Σᵢ pᵢ dqᵢ` is the standard contact form (`TauCeti.innerProductContactForm`).
So `chart` is a strict contactomorphism onto its image: it pulls `α_std` back to `α` itself, not
merely to a positive multiple of `α` as the Darboux theorem for contact structures
(`TauCeti.SmoothForm.IsContactForm.exists_darbouxChart`) does.

The proof follows the Reeb flow. Through `x₀` choose a hypersurface `ι : S → M` transverse to the
Reeb vector field `R_α`. The local Reeb flow map `Φ (s, t) = φₜ (ι s)` is a local diffeomorphism
near `(0, 0)` which pulls `α` back to the contactization form `dt + β` of `S × ℝ`, with
`β = ι^* α` a one-form whose exterior derivative is nondegenerate at `0`
(`TauCeti.Geometry.Contact.Slice`). It remains to put `dt + β` into standard form
(`TauCeti.exists_diffeomorph_mpullback_innerProductContactForm_eq_contactization`): symplectic
Darboux coordinates `φ : S → ℝⁿ × ℝⁿ` for `dβ` make `β + φ^* (Σᵢ pᵢ dqᵢ)` closed near `0`, hence
equal to `dh` for a function `h` by the Poincaré lemma, and then `(s, t) ↦ (φ s, t + h s)` pulls
`α_std` back to `dt + β`.

## Main results

* `TauCeti.exists_diffeomorph_mpullback_innerProductContactForm_eq_contactization`: the
  contactization form `dt + β` of a one-form `β` on a `2 n`-dimensional normed space, with `dβ`
  nondegenerate at `s₀`, is the pullback of the standard contact form near `{s₀} × ℝ`.
* `TauCeti.SmoothForm.IsContactForm.exists_strictDarbouxChart_of_finrank_eq`: Darboux charts for a
  contact form on a manifold of dimension `2 n + 1`, pulling `α_std` back to `α`.
* `TauCeti.SmoothForm.IsContactForm.exists_strictDarbouxChart`: the same, with the dimension `n`
  provided by the theorem.

## References

* H. Geiges, *An Introduction to Contact Topology*, Cambridge University Press, 2008,
  Theorem 2.5.1.
-/

public section

noncomputable section

open Set Filter Bundle Module
open scoped Manifold ContDiff Topology InnerProductSpace

namespace TauCeti

section Contactization

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  {S : Type*} [NormedAddCommGroup S] [NormedSpace ℝ S] [FiniteDimensional ℝ S]

variable (V) in
/-- The linear embedding `(q, p) ↦ (q, p, 0)` of the `(q, p)` coordinates into `V × V × ℝ`. -/
private def qpIncl : V × V →L[ℝ] V × V × ℝ :=
  (ContinuousLinearEquiv.prodAssoc ℝ V V ℝ : (V × V) × ℝ →L[ℝ] V × V × ℝ).comp
    (ContinuousLinearMap.inl ℝ (V × V) ℝ)

variable (V) in
/-- The linear embedding `r ↦ (0, 0, r)` of the `z` coordinate into `V × V × ℝ`. -/
private def zIncl : ℝ →L[ℝ] V × V × ℝ :=
  (ContinuousLinearMap.inr ℝ V (V × ℝ)).comp (ContinuousLinearMap.inr ℝ V ℝ)

private theorem qpIncl_apply (y : V × V) : qpIncl V y = (y.1, y.2, 0) :=
  (rfl)

private theorem zIncl_apply (r : ℝ) : zIncl V r = (0, 0, r) :=
  (rfl)

omit [FiniteDimensional ℝ S] in
/-- The pullback of the standard contact form along `s ↦ (φ s, 0)` is `-⟪p, dq⟫` read through
`φ`. -/
private theorem mpullback_qpIncl_comp_innerProductContactForm_apply {φ : S → V × V}
    (hφ : ContDiff ℝ ∞ φ) (hj : ContMDiff 𝓘(ℝ, S) 𝓘(ℝ, V × V × ℝ) ∞ (qpIncl V ∘ φ)) (x : S)
    (u : TangentSpace 𝓘(ℝ, S) x) :
    (SmoothForm.mpullback _ hj (innerProductContactForm V)).1 x ![u] =
      -⟪(φ x).2, (fderiv ℝ φ x u).1⟫_ℝ := by
  have hjd := (qpIncl V).hasFDerivAt.comp x (hφ.differentiable (by simp) x).hasFDerivAt
  rw [SmoothForm.mpullback_apply_one, hjd.hasMFDerivAt.mfderiv]
  exact (innerProductContactForm_apply _ _ _).trans (zero_sub _)

omit [FiniteDimensional ℝ S] in
/-- The exterior derivative of the pullback of the standard contact form along `s ↦ (φ s, 0)` is
the pullback of the standard symplectic form along `φ`. -/
private theorem mextDeriv_mpullback_qpIncl_comp_innerProductContactForm_apply {φ : S → V × V}
    (hφ : ContDiff ℝ ∞ φ) (hj : ContMDiff 𝓘(ℝ, S) 𝓘(ℝ, V × V × ℝ) ∞ (qpIncl V ∘ φ)) (x : S)
    (u v : TangentSpace 𝓘(ℝ, S) x) :
    mextDeriv (SmoothForm.mpullback _ hj (innerProductContactForm V)).1 x ![u, v] =
      stdSymplecticForm (fderiv ℝ φ x u) (fderiv ℝ φ x v) := by
  have hjd := (qpIncl V).hasFDerivAt.comp x (hφ.differentiable (by simp) x).hasFDerivAt
  have h := congrArg (fun σ : SmoothForm 𝓘(ℝ, S) S ℝ 2 ↦ σ.1 x ![u, v])
    (SmoothForm.mextDerivₗ_mpullback _ hj 1 (innerProductContactForm V))
  simp only [mextDerivₗ_apply, SmoothForm.mpullback_apply] at h
  rw [h]
  have hvec : (fun i ↦ mfderiv 𝓘(ℝ, S) 𝓘(ℝ, V × V × ℝ) (qpIncl V ∘ φ) x (![u, v] i)) =
      ![qpIncl V (fderiv ℝ φ x u), qpIncl V (fderiv ℝ φ x v)] := by
    ext i : 1
    fin_cases i <;> simp only [hjd.hasMFDerivAt.mfderiv] <;> rfl
  rw [hvec]
  exact mextDeriv_innerProductContactForm_apply _ _ _ _

/-- **Exact symplectic Darboux coordinates for a primitive.** If `dβ` is nondegenerate at `s₀`, then
in standard symplectic coordinates `φ` for `dβ` centred at `s₀`, the one-form `β + φ^* ⟪p, dq⟫` is
the differential of a smooth function `h` vanishing at `s₀`, on a neighbourhood of `s₀`. -/
private theorem exists_darboux_fderiv_eq_add_inner {n : ℕ} (hS : finrank ℝ S = 2 * n)
    (β : SmoothForm 𝓘(ℝ, S) S ℝ 1) {s₀ : S}
    (hβ : ((mextDerivₗ 𝓘(ℝ, S) 1 β).bilinFormAt s₀).Nondegenerate) :
    ∃ (φ : S ≃ₘ⟮𝓘(ℝ, S), 𝓘(ℝ, EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n))⟯
        EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)) (h : S → ℝ) (U : Set S),
      φ s₀ = 0 ∧ ContDiff ℝ ∞ h ∧ h s₀ = 0 ∧ U ∈ 𝓝 s₀ ∧
      ∀ y ∈ U, ∀ u : TangentSpace 𝓘(ℝ, S) y,
        fderiv ℝ h y u = β.1 y ![u] + ⟪(φ y).2, (fderiv ℝ φ y u).1⟫_ℝ := by
  set V := EuclideanSpace ℝ (Fin n)
  -- The flat exterior derivative of `β` is smooth, closed and nondegenerate at `s₀`.
  have hβc : ContDiff ℝ ∞ β.1 := isSmoothForm_modelSpace_iff.1 β.isSmoothForm
  have hnd : ∀ v, (∀ w, extDeriv β.1 s₀ ![v, w] = 0) → v = 0 := fun v hv ↦
    hβ.1 v fun w ↦ (SmoothForm.bilinFormAt_apply _ s₀ v w).trans <|
      (SmoothBundleForm.eval₂_apply _ s₀ v w).trans <|
        (congrArg (fun A ↦ A ![v, w]) (congrFun (mextDerivₗ_apply 𝓘(ℝ, S) 1 β) s₀)).trans <|
          (congrArg (fun A ↦ A ![v, w]) (mextDeriv_eq_extDeriv β.1 s₀)).trans (hv w)
  obtain ⟨φ, hφ₀, hφω⟩ := exists_diffeomorph_eventually_stdSymplecticForm_fderiv_eq (r := ⊤)
    hS le_top isOpen_univ (mem_univ s₀) (contDiff_extDeriv hβc (by simp)).contDiffOn
    (fun x _ ↦ extDeriv_extDeriv_apply hβc.contDiffAt (by simp)) hnd
  have hφc : ContDiff ℝ ∞ φ := contMDiff_iff_contDiff.1 φ.contMDiff
  have hj : ContMDiff 𝓘(ℝ, S) 𝓘(ℝ, V × V × ℝ) ∞ (qpIncl V ∘ φ) :=
    contMDiff_iff_contDiff.2 ((qpIncl V).contDiff.comp hφc)
  set κ := SmoothForm.mpullback _ hj (innerProductContactForm V)
  -- The one-form `γ = β - κ` is closed near `s₀`, so it has a primitive `ψ` there.
  set γ := β - κ
  have hγ : ∀ᶠ y in 𝓝 s₀, mextDeriv γ.1 y = 0 := by
    filter_upwards [hφω] with y hy
    have hsub : mextDeriv γ.1 y = mextDeriv β.1 y - mextDeriv κ.1 y := by
      rw [← mextDerivₗ_apply, ← mextDerivₗ_apply, ← mextDerivₗ_apply, map_sub]
      rfl
    rw [hsub]
    refine ContinuousAlternatingMap.ext fun v ↦ ?_
    obtain ⟨a, b, rfl⟩ : ∃ a b : TangentSpace 𝓘(ℝ, S) y, v = ![a, b] :=
      ⟨v 0, v 1, funext fun i ↦ by fin_cases i <;> rfl⟩
    calc (mextDeriv β.1 y - mextDeriv κ.1 y) ![a, b]
        = mextDeriv β.1 y ![a, b] - mextDeriv κ.1 y ![a, b] := rfl
      _ = 0 := by
        rw [mextDeriv_mpullback_qpIncl_comp_innerProductContactForm_apply hφc,
          mextDeriv_eq_extDeriv]
        exact sub_eq_zero.2 (hy.2 a b).symm
  obtain ⟨U, hU, ψ, hψ, hdψ⟩ := exists_mextDeriv_eq_nhds (r := ⊤) le_top γ.isSmoothForm hγ
  have hψh : ψ = RoughForm.ofFunction 𝓘(ℝ, S) fun s ↦ ψ s 0 := RoughForm.eq_ofFunction ψ
  have hh : ContDiff ℝ ∞ fun s ↦ ψ s 0 := by
    rw [hψh] at hψ
    exact contMDiff_iff_contDiff.1 (isSmoothForm_ofFunction_iff.1 hψ)
  refine ⟨φ, fun s ↦ ψ s 0 - ψ s₀ 0, U, hφ₀, hh.sub contDiff_const, sub_self _, hU,
    fun y hy u ↦ ?_⟩
  have h1 := mextDeriv_ofFunction_apply (I := 𝓘(ℝ, S)) (fun s ↦ ψ s 0) y u
  rw [← hψh, hdψ y hy, (hh.differentiable (by simp) y).hasFDerivAt.hasMFDerivAt.mfderiv] at h1
  rw [fderiv_sub_const]
  refine h1.symm.trans ?_
  calc γ.1 y ![u] = β.1 y ![u] - κ.1 y ![u] := rfl
    _ = _ := by rw [mpullback_qpIncl_comp_innerProductContactForm_apply hφc, sub_neg_eq_add]

/-- The diffeomorphism `(s, t) ↦ (φ s, t + g s)` from `S × ℝ` onto `V × V × ℝ`, for a
diffeomorphism `φ : S → V × V` and a smooth function `g` on `S`. -/
private def prodShiftDiffeomorph (φ : S ≃ₘ⟮𝓘(ℝ, S), 𝓘(ℝ, V × V)⟯ V × V) {g : S → ℝ}
    (hg : ContDiff ℝ ∞ g) : (S × ℝ) ≃ₘ⟮𝓘(ℝ, S).prod 𝓘(ℝ), 𝓘(ℝ, V × V × ℝ)⟯ (V × V × ℝ) where
  toFun q := qpIncl V (φ q.1) + zIncl V (q.2 + g q.1)
  invFun y := (φ.symm (y.1, y.2.1), y.2.2 - g (φ.symm (y.1, y.2.1)))
  left_inv q := by simp [qpIncl_apply, zIncl_apply]
  right_inv y := by simp [qpIncl_apply, zIncl_apply]
  contMDiff_toFun :=
    ((contMDiff_iff_contDiff.2 ((qpIncl V).contDiff.comp
      (contMDiff_iff_contDiff.1 φ.contMDiff))).comp contMDiff_fst).add
      ((contMDiff_iff_contDiff.2 (zIncl V).contDiff).comp
        (contMDiff_snd.add ((contMDiff_iff_contDiff.2 hg).comp contMDiff_fst)))
  contMDiff_invFun := by
    have hA : ContDiff ℝ ∞ fun y : V × V × ℝ ↦ φ.symm (y.1, y.2.1) :=
      (contMDiff_iff_contDiff.1 φ.symm.contMDiff).comp
        (contDiff_fst.prodMk (contDiff_fst.comp contDiff_snd))
    exact (contMDiff_iff_contDiff.2 hA).prodMk
      (contMDiff_iff_contDiff.2 ((contDiff_snd.comp contDiff_snd).sub (hg.comp hA)))

omit [FiniteDimensional ℝ S] in
private theorem prodShiftDiffeomorph_apply (φ : S ≃ₘ⟮𝓘(ℝ, S), 𝓘(ℝ, V × V)⟯ V × V) {g : S → ℝ}
    (hg : ContDiff ℝ ∞ g) (q : S × ℝ) :
    prodShiftDiffeomorph φ hg q = qpIncl V (φ q.1) + zIncl V (q.2 + g q.1) :=
  (rfl)

omit [FiniteDimensional ℝ S] in
/-- The pullback of the standard contact form along `(s, t) ↦ (φ s, t + g s)` sends a tangent
vector `(u, τ)` to `τ + dg(u) - ⟪p, dq(u)⟫`, read through `φ`. -/
private theorem mpullback_prodShiftDiffeomorph_innerProductContactForm_apply
    (φ : S ≃ₘ⟮𝓘(ℝ, S), 𝓘(ℝ, V × V)⟯ V × V) {g : S → ℝ} (hg : ContDiff ℝ ∞ g) (p : S × ℝ)
    (w : TangentSpace (𝓘(ℝ, S).prod 𝓘(ℝ)) p) :
    mpullback (𝓘(ℝ, S).prod 𝓘(ℝ)) 𝓘(ℝ, V × V × ℝ) (prodShiftDiffeomorph φ hg)
        (innerProductContactForm V).1 p ![w] =
      w.2 + fderiv ℝ g p.1 w.1 - ⟪(φ p.1).2, (fderiv ℝ φ p.1 w.1).1⟫_ℝ := by
  set F := prodShiftDiffeomorph φ hg
  have hφd := ((contMDiff_iff_contDiff.1 φ.contMDiff).differentiable (by simp) p.1).hasFDerivAt
  have hgd := (hg.differentiable (by simp) p.1).hasFDerivAt
  -- The partial derivatives of `F` in the two factors.
  have h1 : mfderiv 𝓘(ℝ, S) 𝓘(ℝ, V × V × ℝ) (fun z ↦ F (z, p.2)) p.1 =
      (qpIncl V).comp (fderiv ℝ φ p.1) + (zIncl V).comp (fderiv ℝ g p.1) :=
    (((qpIncl V).hasFDerivAt.comp p.1 hφd).add
      ((zIncl V).hasFDerivAt.comp p.1 (hgd.const_add p.2))).hasMFDerivAt.mfderiv
  have h2 : mfderiv 𝓘(ℝ) 𝓘(ℝ, V × V × ℝ) (fun r ↦ F (p.1, r)) p.2 = zIncl V :=
    (((zIncl V).hasFDerivAt.comp p.2 ((hasFDerivAt_id p.2).add_const (g p.1))).const_add
      (qpIncl V (φ p.1))).hasMFDerivAt.mfderiv
  rw [mpullback_apply]
  have hvec : (fun i ↦ mfderiv (𝓘(ℝ, S).prod 𝓘(ℝ)) 𝓘(ℝ, V × V × ℝ) F p (![w] i)) =
      ![qpIncl V (fderiv ℝ φ p.1 w.1) + zIncl V (fderiv ℝ g p.1 w.1) + zIncl V w.2] := by
    ext i : 1
    fin_cases i
    simp only [Fin.zero_eta, Fin.isValue, Matrix.cons_val_zero]
    rw [mfderiv_prod_eq_add_apply (F.contMDiff.mdifferentiableAt (by simp)), h1, h2]
    rfl
  rw [hvec]
  refine (innerProductContactForm_apply _ _ _).trans ?_
  simp only [F, prodShiftDiffeomorph_apply, qpIncl_apply, zIncl_apply, Prod.fst_add, Prod.snd_add,
    add_zero, zero_add]
  ring

/-- **Darboux's theorem for contactization forms.** Let `β` be a smooth one-form on a normed space
`S` of dimension `2 n` whose exterior derivative is nondegenerate at `s₀`. Then there are a
diffeomorphism `F` from `S × ℝ` onto `ℝⁿ × ℝⁿ × ℝ` sending `(s₀, 0)` to `0` and a neighbourhood
`U` of `s₀` such that `F` pulls the standard contact form `dz - Σᵢ pᵢ dqᵢ` back to the
contactization form `dt + β` at every point of `U × ℝ`. -/
theorem exists_diffeomorph_mpullback_innerProductContactForm_eq_contactization {n : ℕ}
    (hS : finrank ℝ S = 2 * n) (β : SmoothForm 𝓘(ℝ, S) S ℝ 1) {s₀ : S}
    (hβ : ((mextDerivₗ 𝓘(ℝ, S) 1 β).bilinFormAt s₀).Nondegenerate) :
    ∃ (F : (S × ℝ) ≃ₘ⟮𝓘(ℝ, S).prod 𝓘(ℝ),
        𝓘(ℝ, EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) × ℝ)⟯
        (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) × ℝ)) (U : Set S),
      U ∈ 𝓝 s₀ ∧ F (s₀, 0) = 0 ∧ ∀ p : S × ℝ, p.1 ∈ U →
        mpullback (𝓘(ℝ, S).prod 𝓘(ℝ))
          𝓘(ℝ, EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) × ℝ) F
          (innerProductContactForm (EuclideanSpace ℝ (Fin n))).1 p = (-β).contactization.1 p := by
  obtain ⟨φ, h, U, hφ₀, hh, hh₀, hU, hdh⟩ := exists_darboux_fderiv_eq_add_inner hS β hβ
  refine ⟨prodShiftDiffeomorph φ hh, U, hU,
    by simp [prodShiftDiffeomorph_apply, qpIncl_apply, zIncl_apply, hφ₀, hh₀], fun p hp ↦ ?_⟩
  refine ContinuousAlternatingMap.ext fun v ↦ ?_
  obtain ⟨w, rfl⟩ : ∃ w, v = ![w] := ⟨v 0, funext fun i ↦ by fin_cases i; rfl⟩
  rw [mpullback_prodShiftDiffeomorph_innerProductContactForm_apply]
  refine Eq.trans ?_ (SmoothForm.contactization_apply _ _ _).symm
  simp only [Manifold.tangentSpaceProdEquiv_apply, NormedSpace.fromTangentSpace_apply]
  have hneg : (-β).1 p.1 ![w.1] = -β.1 p.1 ![w.1] := rfl
  erw [hdh p.1 hp, hneg]
  ring

end Contactization

section Darboux

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless] [TopologicalSpace M]
  [ChartedSpace H M] [IsManifold I ∞ M]

/-- Through every point `x₀` of a boundaryless manifold of dimension `m + 1` there is a smooth map
`ι : ℝᵐ → M` sending `0` to `x₀`, with injective differential at `0` whose image does not contain a
prescribed nonzero tangent vector at `x₀`. It is a global parametrization of a neighbourhood of `x₀`
by Euclidean space, restricted to a complementary hyperplane. -/
private theorem exists_slice {m : ℕ} (hm : m + 1 = finrank ℝ E) {x₀ : M}
    {v₀ : TangentSpace I x₀} (hv₀ : v₀ ≠ 0) :
    ∃ ι : EuclideanSpace ℝ (Fin m) → M, ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) I ∞ ι ∧
      ι 0 = x₀ ∧ Function.Injective (mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) I ι 0) ∧
      v₀ ∉ (mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) I ι 0).range := by
  set G := EuclideanSpace ℝ (Fin (finrank ℝ E))
  obtain ⟨U, hx₀U, ⟨Ψ⟩⟩ := exists_opens_diffeomorph_euclideanSpace (n := ⊤)
    (BoundarylessManifold.isInteriorPoint (I := I) (x := x₀))
  -- The global parametrization `P` of `U`, and the preimage `u` of `v₀` under `dP`.
  set P : G → M := Subtype.val ∘ Ψ.symm
  set y₀ := Ψ ⟨x₀, hx₀U⟩
  have hP : ContMDiff 𝓘(ℝ, G) I ∞ P := contMDiff_subtype_val.comp Ψ.symm.contMDiff
  have hPinv : (mfderiv 𝓘(ℝ, G) I P y₀).IsInvertible :=
    ((Ψ.symm.isLocalDiffeomorph y₀).comp
      (hg := isLocalDiffeomorph_subtype_val _)).isInvertible_mfderiv (by simp)
  obtain ⟨(u : G), hu⟩ := hPinv.surjective v₀
  have hu0 : u ≠ 0 := by
    rintro rfl
    exact hv₀ (hu.symm.trans (map_zero _))
  -- A complement `K` of the line through `u`, identified with `ℝᵐ` by `L`.
  obtain ⟨K, hK⟩ := Submodule.exists_isCompl (ℝ ∙ u)
  have hdim : finrank ℝ (EuclideanSpace ℝ (Fin m)) = finrank ℝ K := by
    have h := Submodule.finrank_add_eq_of_isCompl hK
    rw [finrank_span_singleton hu0, finrank_euclideanSpace_fin] at h
    rw [finrank_euclideanSpace_fin]
    omega
  have huK : u ∉ K := fun h ↦ hu0 <| by
    simpa using hK.disjoint.le_bot ⟨Submodule.mem_span_singleton_self u, h⟩
  set A : EuclideanSpace ℝ (Fin m) →L[ℝ] G :=
    K.subtypeL.comp (ContinuousLinearEquiv.ofFinrankEq hdim).toContinuousLinearMap
  have hA : Function.Injective A :=
    Subtype.val_injective.comp (ContinuousLinearEquiv.ofFinrankEq hdim).injective
  have ha : HasFDerivAt (fun w ↦ y₀ + A w) A 0 := A.hasFDerivAt.const_add y₀
  have hd : mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) I (fun w ↦ P (y₀ + A w)) 0 =
      (mfderiv 𝓘(ℝ, G) I P y₀).comp A := by
    rw [show (fun w ↦ P (y₀ + A w)) = P ∘ fun w ↦ y₀ + A w from rfl,
      mfderiv_comp_of_eq ((hP.contMDiffAt (x := y₀)).mdifferentiableAt (by simp))
        ha.hasMFDerivAt.mdifferentiableAt (by simp), ha.hasMFDerivAt.mfderiv, map_zero, add_zero]
    rfl
  refine ⟨fun w ↦ P (y₀ + A w), hP.comp (contMDiff_iff_contDiff.2 (contDiff_const.add A.contDiff)),
    by simp [P, y₀], ?_, ?_⟩ <;> rw [hd]
  · exact hPinv.injective.comp hA
  · rintro ⟨w, hw⟩
    have huw : u = A w := hPinv.injective (hu.trans hw.symm)
    exact huK (huw ▸ (ContinuousLinearEquiv.ofFinrankEq hdim w).2)

variable [T2Space M]

/-- Along a local inverse `Λ` of the local Reeb flow map `Φ (s, t) = φₜ (ι s)` out of a smooth map
`ι : S → M`, the contactization form `dt + ι^* α` pulls back to `α`, at every point `x` of the
source of `Λ` whose image lies in the domain of `Φ`. -/
private theorem contactization_apply_mfderiv_localInverse {S : Type*} [NormedAddCommGroup S]
    [NormedSpace ℝ S] {α : SmoothForm I M ℝ 1} (hα : α.IsContactForm)
    {ι : S → M} (hι : ContMDiff 𝓘(ℝ, S) I ∞ ι) {p : S × ℝ}
    (hloc : IsLocalDiffeomorphAt (𝓘(ℝ, S).prod 𝓘(ℝ)) I ∞
      (fun q : S × ℝ ↦ flowOf α.reebVectorField q.2 (ι q.1)) p)
    {x : M} (hx : x ∈ hloc.localInverse.source)
    (hxD : ((hloc.localInverse x).2, ι (hloc.localInverse x).1) ∈ flowDomain α.reebVectorField)
    (v : TangentSpace I x) :
    (-SmoothForm.mpullback ι hι α).contactization.1 (hloc.localInverse x)
      ![mfderiv I (𝓘(ℝ, S).prod 𝓘(ℝ)) hloc.localInverse x v] = α.1 x ![v] := by
  set Φ : S × ℝ → M := fun q ↦ flowOf α.reebVectorField q.2 (ι q.1)
  set Λ := hloc.localInverse
  have hΛd : MDifferentiableAt I (𝓘(ℝ, S).prod 𝓘(ℝ)) Λ x := Λ.mdifferentiableAt (by simp) hx
  have hΦd : MDifferentiableAt (𝓘(ℝ, S).prod 𝓘(ℝ)) I Φ (Λ x) :=
    (contMDiffAt_flowOf_comp le_rfl (hα.contMDiff_reebVectorField.of_le (by simp)) contMDiffAt_snd
      ((hι.of_le (by simp)).contMDiffAt.comp _ contMDiffAt_fst) hxD).mdifferentiableAt
      one_ne_zero
  -- `Φ` undoes `Λ` near `x`, so `dΦ` undoes `dΛ`.
  have hΦw : mfderiv (𝓘(ℝ, S).prod 𝓘(ℝ)) I Φ (Λ x) (mfderiv I (𝓘(ℝ, S).prod 𝓘(ℝ)) Λ x v) = v := by
    have heq : Φ ∘ Λ =ᶠ[𝓝 x] id :=
      eventually_of_mem (Λ.open_source.mem_nhds hx) hloc.localInverse_eqOn_right
    have h := (mfderiv_comp x hΦd hΛd).symm.trans heq.mfderiv_eq
    rw [mfderiv_id] at h
    exact congrArg (fun L ↦ L v) h
  have hpt : ∀ y, y = x → ∀ u : TangentSpace I y, (u : E) = (v : E) →
      α.1 y ![u] = α.1 x ![v] := by
    rintro y rfl u rfl
    rfl
  calc (-SmoothForm.mpullback ι hι α).contactization.1 (Λ x)
        ![mfderiv I (𝓘(ℝ, S).prod 𝓘(ℝ)) Λ x v]
      = TauCeti.mpullback (𝓘(ℝ, S).prod 𝓘(ℝ)) I Φ α.1 (Λ x)
          ![mfderiv I (𝓘(ℝ, S).prod 𝓘(ℝ)) Λ x v] := by
        rw [mpullback_flowOf_comp_apply_eq_contactization hα.contMDiff_reebVectorField hι
          hα.apply_reebVectorField hα.interior_mextDeriv_reebVectorField hxD]
    _ = α.1 (Φ (Λ x)) ![mfderiv _ _ Φ (Λ x) (mfderiv I (𝓘(ℝ, S).prod 𝓘(ℝ)) Λ x v)] := by
        rw [TauCeti.mpullback_apply]
        congr 1
        ext i
        fin_cases i
        rfl
    _ = α.1 x ![v] := hpt _ (hloc.localInverse_right_inv hx) _ hΦw

/-- **The Reeb flow box.** Around every point `x₀` of a boundaryless manifold of dimension
`2 n + 1` with a contact form `α`, there is a smooth partial diffeomorphism `Λ` onto an open subset
of `ℝ²ⁿ × ℝ` with `Λ x₀ = (0, 0)`, which carries `α` to the contactization form `dt + β` of a
one-form `β` on `ℝ²ⁿ` whose exterior derivative is nondegenerate at `0`. Its inverse is the local
Reeb flow out of a hypersurface through `x₀` transverse to the Reeb field. -/
private theorem exists_reebFlowChart {α : SmoothForm I M ℝ 1} (hα : α.IsContactForm) {n : ℕ}
    (hn : finrank ℝ E = 2 * n + 1) (x₀ : M) :
    ∃ (β : SmoothForm 𝓘(ℝ, EuclideanSpace ℝ (Fin (2 * n))) (EuclideanSpace ℝ (Fin (2 * n))) ℝ 1)
      (Λ : PartialDiffeomorph I (𝓘(ℝ, EuclideanSpace ℝ (Fin (2 * n))).prod 𝓘(ℝ)) M
        (EuclideanSpace ℝ (Fin (2 * n)) × ℝ) ∞),
      ((mextDerivₗ 𝓘(ℝ, EuclideanSpace ℝ (Fin (2 * n))) 1 β).bilinFormAt 0).Nondegenerate ∧
      x₀ ∈ Λ.source ∧ Λ x₀ = (0, 0) ∧ ∀ x ∈ Λ.source, ∀ v : TangentSpace I x,
        (-β).contactization.1 (Λ x)
          ![mfderiv I (𝓘(ℝ, EuclideanSpace ℝ (Fin (2 * n))).prod 𝓘(ℝ)) Λ x v] = α.1 x ![v] := by
  have hR1 : ContMDiff I I.tangent 1 (T% α.reebVectorField) :=
    hα.contMDiff_reebVectorField.of_le (by simp)
  have hdim : finrank ℝ (EuclideanSpace ℝ (Fin (2 * n))) + 1 = finrank ℝ E := by simp [hn]
  obtain ⟨ι, hι, hι0, hinj, hrange₀⟩ :=
    exists_slice (m := 2 * n) (by omega) (hα.reebVectorField_ne_zero x₀)
  have hrange : α.reebVectorField (ι 0) ∉
      (mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin (2 * n))) I ι 0).range := by
    have key : ∀ y, ι 0 = y →
        α.reebVectorField y ∉ (mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin (2 * n))) I ι 0).range →
        α.reebVectorField (ι 0) ∉ (mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin (2 * n))) I ι 0).range := by
      rintro y rfl h
      exact h
    exact key x₀ hι0 hrange₀
  -- The local Reeb flow map `(s, t) ↦ φₜ (ι s)` on its open domain `D`, and a local inverse `Λ`.
  set D : Set (EuclideanSpace ℝ (Fin (2 * n)) × ℝ) :=
    {q | (q.2, ι q.1) ∈ flowDomain α.reebVectorField}
  have hD : IsOpen D :=
    (isOpen_flowDomain hR1).preimage (continuous_snd.prodMk (hι.continuous.comp continuous_fst))
  have hD₀ : ((0 : EuclideanSpace ℝ (Fin (2 * n))), (0 : ℝ)) ∈ D := mem_flowDomain_zero hR1 _
  have hloc := hα.isLocalDiffeomorphAt_flowOf_reebVectorField_comp (p := (0, 0)) hι hdim hinj
    hrange hD₀
  set Λ := hloc.localInverse
  have hΛ₀ : Λ x₀ = (0, 0) := hι0 ▸ (flowOf_zero α.reebVectorField (ι 0)) ▸
    hloc.localInverse_left_inv hloc.localInverse_mem_target
  have hs : x₀ ∈ Λ.source := hι0 ▸ (flowOf_zero α.reebVectorField (ι 0)) ▸
    hloc.localInverse_mem_source
  have hW : IsOpen (Λ.source ∩ Λ ⁻¹' D) :=
    Λ.contMDiffOn.continuousOn.isOpen_inter_preimage Λ.open_source hD
  refine ⟨SmoothForm.mpullback ι hι α, Λ.restrOpen _ hW,
    hα.nondegenerate_bilinFormAt_mextDerivₗ_mpullback (s := 0) hι hdim hinj hrange,
    by
      rw [PartialDiffeomorph.restrOpen_source]
      exact ⟨hs, hs, by rw [mem_preimage, hΛ₀]; exact hD₀⟩,
    by rw [PartialDiffeomorph.coe_restrOpen]; exact hΛ₀, fun x hx v ↦ ?_⟩
  rw [PartialDiffeomorph.restrOpen_source] at hx
  rw [PartialDiffeomorph.coe_restrOpen]
  exact contactization_apply_mfderiv_localInverse hα hι hloc hx.1 hx.2.2 v

/-- **Darboux's theorem for contact forms, in dimension `2 n + 1`.** Let `α` be a smooth contact
form on a boundaryless manifold of dimension `2 n + 1`. Around every point `x₀` there is a smooth
partial diffeomorphism `chart` onto an open subset of `ℝⁿ × ℝⁿ × ℝ` with `chart x₀ = 0` which
pulls the standard contact form `dz - Σᵢ pᵢ dqᵢ` back to `α` itself on `chart.source`. -/
theorem SmoothForm.IsContactForm.exists_strictDarbouxChart_of_finrank_eq
    {α : SmoothForm I M ℝ 1} (hα : α.IsContactForm) {n : ℕ} (hn : finrank ℝ E = 2 * n + 1)
    (x₀ : M) :
    ∃ chart : PartialDiffeomorph I
        𝓘(ℝ, EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) × ℝ) M
        (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) × ℝ) ∞,
      x₀ ∈ chart.source ∧ chart x₀ = 0 ∧
      ∀ x ∈ chart.source, ∀ v : TangentSpace I x,
        (innerProductContactForm (EuclideanSpace ℝ (Fin n))).1 (chart x)
          ![mvfderiv I chart x v] = α.1 x ![v] := by
  set V := EuclideanSpace ℝ (Fin n)
  obtain ⟨β, Λ, hβ, hx₀, hΛ₀, hΛ⟩ := exists_reebFlowChart hα hn x₀
  obtain ⟨F, U, hU, hF₀, hFβ⟩ :=
    exists_diffeomorph_mpullback_innerProductContactForm_eq_contactization (n := n) (by simp) β hβ
  -- Restrict `Λ` to the points it sends into `U × ℝ`, then apply `F`.
  set W : Set M := Λ.source ∩ Λ ⁻¹' (interior U ×ˢ univ)
  have hW : IsOpen W := Λ.contMDiffOn.continuousOn.isOpen_inter_preimage Λ.open_source
    (isOpen_interior.prod isOpen_univ)
  obtain ⟨chart, hchart⟩ : ∃ chart : PartialDiffeomorph I 𝓘(ℝ, V × V × ℝ) M (V × V × ℝ) ∞,
      chart = (Λ.restrOpen W hW).trans F.toPartialDiffeomorph := ⟨_, rfl⟩
  have hcoe (y : M) : chart y = F (Λ y) := by simp [hchart]
  have hsrc : chart.source = W := by simp [hchart, W]
  refine ⟨chart, ?_, by rw [hcoe, hΛ₀, hF₀], fun x hx v ↦ ?_⟩
  · rw [hsrc]
    exact ⟨hx₀, by rw [mem_preimage, hΛ₀]; exact ⟨mem_interior_iff_mem_nhds.2 hU, mem_univ _⟩⟩
  rw [hsrc] at hx
  obtain ⟨hxΛ, hqU, -⟩ := hx
  have hΛd : MDifferentiableAt I (𝓘(ℝ, EuclideanSpace ℝ (Fin (2 * n))).prod 𝓘(ℝ)) Λ x :=
    Λ.mdifferentiableAt (by simp) hxΛ
  have hchart : mvfderiv I chart x v =
      mfderiv (𝓘(ℝ, EuclideanSpace ℝ (Fin (2 * n))).prod 𝓘(ℝ)) 𝓘(ℝ, V × V × ℝ) F (Λ x)
      (mfderiv I (𝓘(ℝ, EuclideanSpace ℝ (Fin (2 * n))).prod 𝓘(ℝ)) Λ x v) := by
    have hfun : (chart : M → V × V × ℝ) = F ∘ Λ := funext hcoe
    exact (congrArg (fun f : M → V × V × ℝ ↦ mvfderiv I f x v) hfun).trans
      ((mvfderiv_comp_apply x (F.contMDiff.mdifferentiableAt (by simp)) hΛd v).trans
        (mvfderiv_apply_eq_mfderiv_apply _ _ _))
  -- Move from the chart to `F ∘ Λ`, a dependent change of base point.
  have e₁ : ∀ y, y = F (Λ x) → ∀ u : V × V × ℝ, u = mvfderiv I chart x v →
      (innerProductContactForm V).1 y ![u] =
        (innerProductContactForm V).1 (chart x) ![mvfderiv I chart x v] := by
    rintro y rfl u rfl
    rw [hcoe]
  have h := (congrArg (fun A : RoughForm _ _ ℝ 1 ↦ A (Λ x))
    (SmoothForm.coe_mpullback F F.contMDiff (innerProductContactForm V))).trans
      (hFβ _ (interior_subset hqU))
  have e₂ : (innerProductContactForm V).1 (F (Λ x))
      ![mfderiv (𝓘(ℝ, EuclideanSpace ℝ (Fin (2 * n))).prod 𝓘(ℝ)) 𝓘(ℝ, V × V × ℝ) F (Λ x)
        (mfderiv I (𝓘(ℝ, EuclideanSpace ℝ (Fin (2 * n))).prod 𝓘(ℝ)) Λ x v)] =
        (-β).contactization.1 (Λ x)
          ![mfderiv I (𝓘(ℝ, EuclideanSpace ℝ (Fin (2 * n))).prod 𝓘(ℝ)) Λ x v] :=
    (SmoothForm.mpullback_apply_one _ F.contMDiff _ (Λ x) _).symm.trans
      (congrArg (fun A ↦ A ![mfderiv I (𝓘(ℝ, EuclideanSpace ℝ (Fin (2 * n))).prod 𝓘(ℝ)) Λ x v]) h)
  exact (e₁ _ rfl _ hchart.symm).symm.trans (e₂.trans (hΛ x hxΛ v))

/-- **Darboux's theorem for contact forms.** Let `α` be a smooth contact form on a boundaryless
manifold. Around every point `x₀` there are `n` with `dim M = 2 n + 1` and a smooth partial
diffeomorphism `chart` onto an open subset of `ℝⁿ × ℝⁿ × ℝ` with `chart x₀ = 0` which pulls the
standard contact form `dz - Σᵢ pᵢ dqᵢ` back to `α` itself on `chart.source`. -/
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

end Darboux

end TauCeti
