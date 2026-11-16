/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Contact.Slice
public import TauCeti.Geometry.Contact.Standard
-- Access the body of `IsLocalDiffeomorphAt` to extract its partial diffeomorphism.
import all Mathlib.Geometry.Manifold.LocalDiffeomorph
import TauCeti.Geometry.Manifold.Diffeomorph.Prod
import TauCeti.Geometry.Manifold.DifferentialForm.Poincare
import TauCeti.Geometry.Manifold.LocalDiffeomorph.Constructions
import TauCeti.Geometry.Manifold.LocalDiffeomorph.MFDeriv
import TauCeti.Geometry.Manifold.LocalDiffeomorph.OpenSubset
import TauCeti.Geometry.Manifold.MFDeriv.NormedSpace
import TauCeti.Geometry.Manifold.VectorField.Transverse
import TauCeti.Geometry.Symplectic.ContinuousAlternatingMap
import TauCeti.Geometry.Symplectic.Darboux.Standard
import TauCeti.Geometry.Symplectic.ExistsCompatible

/-!
# The Darboux theorem for contact forms

Let `α` be a smooth contact form on a boundaryless manifold `M` of dimension `2 n + 1`. **Darboux's
theorem for contact forms** (`TauCeti.SmoothForm.IsContactForm.exists_strictDarbouxChart`) gives,
around every point `x₀`, a smooth partial diffeomorphism `chart` from `M` to `ℝⁿ × ℝⁿ × ℝ` with
`chart x₀ = 0` which pulls the standard contact form `α_std = dz - Σᵢ pᵢ dqᵢ`
(`TauCeti.innerProductContactForm`) back to `α` itself:

`α_std (chart x) (d chart_x v) = α x v`.

So the chart is a strict contactomorphism onto an open subset of the standard contact space.
`TauCeti.SmoothForm.IsContactForm.exists_darbouxChart` gives such a chart only up to a positive
conformal factor `g`.

The proof reduces to the symplectic Darboux theorem along the Reeb flow:

* Choose a hypersurface `ι : K → M` through `x₀` transverse to the Reeb vector field `R_α`
  (`TauCeti.exists_hypersurface_notMem_range_mfderiv`). The local Reeb flow map
  `(s, t) ↦ φₜ(ι s)` is then a local diffeomorphism near `(0, 0)` pulling `α` back to the
  contactization form `dt + β`, where `β = ι^* α` has nondegenerate exterior derivative at `0`
  (`TauCeti.Geometry.Contact.Slice`).
* By the symplectic Darboux theorem there are coordinates `ψ` on `K` in which `dβ` is the standard
  symplectic form `Σᵢ dqᵢ ∧ dpᵢ`, whose primitive is `-Σᵢ pᵢ dqᵢ`. So `β + ψ^* ⟪p, dq⟫` is closed
  near `0`, and by the Poincaré lemma it is the differential `df` of a smooth function `f`.
* The shear `(s, t) ↦ (ψ s, t + f s)` (`Diffeomorph.prodShear`) pulls `α_std` back to `dt + β`
  near `0`
  (`TauCeti.exists_diffeomorph_mpullback_innerProductContactForm_eq_contactization`), and the chart
  is this shear composed with the inverse of the local Reeb flow map.

## Main results

* `TauCeti.exists_diffeomorph_mpullback_innerProductContactForm_eq_contactization`: Darboux
  coordinates for the contactization form `dt + β` of a one-form `β` with nondegenerate
  differential.
* `TauCeti.SmoothForm.IsContactForm.exists_strictDarbouxChart`: Darboux's theorem for contact
  forms.

## References

* H. Geiges, *An Introduction to Contact Topology*, Cambridge University Press, 2008,
  Section 2.5 (Darboux's theorem for contact forms).
-/

public section

open Set Filter Module
open scoped Manifold ContDiff Topology InnerProductSpace

namespace TauCeti

section Contactization

variable {K : Type*} [NormedAddCommGroup K] [NormedSpace ℝ K] [FiniteDimensional ℝ K]

omit [FiniteDimensional ℝ K] in
/-- **The primitive `-⟪p, dq⟫` in coordinates.** For a smooth map `ψ : K → V × V`, the one-form
`a ↦ -⟪(ψ x).2, (dψ a).1⟫` is smooth, with exterior derivative the pullback of the standard
symplectic form along `ψ`. It is the pullback of the standard contact form along
`s ↦ (ψ s, 0)`. -/
private theorem exists_smoothForm_apply_eq_neg_inner {V : Type*} [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] {ψ : K → V × V} (hψ : ContDiff ℝ ∞ ψ) :
    ∃ θ : SmoothForm 𝓘(ℝ, K) K ℝ 1,
      (∀ x (a : TangentSpace 𝓘(ℝ, K) x), θ.1 x ![a] = -⟪(ψ x).2, (fderiv ℝ ψ x a).1⟫_ℝ) ∧
      ∀ x (a b : TangentSpace 𝓘(ℝ, K) x),
        mextDeriv θ.1 x ![a, b] = stdSymplecticForm (fderiv ℝ ψ x a) (fderiv ℝ ψ x b) := by
  have hψD (x : K) : DifferentiableAt ℝ ψ x := hψ.differentiable (by simp) x
  set L : V × V →L[ℝ] V × V × ℝ :=
    (ContinuousLinearMap.fst ℝ V V).prod ((ContinuousLinearMap.snd ℝ V V).prod 0)
  have hG₀ : ContMDiff 𝓘(ℝ, K) 𝓘(ℝ, V × V × ℝ) ∞ (L ∘ ψ) :=
    contMDiff_iff_contDiff.2 (L.contDiff.comp hψ)
  refine ⟨SmoothForm.mpullback (L ∘ ψ) hG₀ (innerProductContactForm V), fun x a ↦ ?_,
    fun x a b ↦ ?_⟩
  · rw [SmoothForm.mpullback_apply_one, innerProductContactForm_apply, mfderiv_eq_fderiv,
      fderiv_comp x L.differentiableAt (hψD x)]
    simp only [Function.comp_apply, ContinuousLinearMap.fderiv, ContinuousLinearMap.comp_apply,
      ContinuousLinearEquiv.coe_coe]
    -- The last coordinate of `L z` is `0`, by definition of `L`.
    exact zero_sub _
  · rw [← mextDerivₗ_apply, SmoothForm.mextDerivₗ_mpullback, SmoothForm.coe_mpullback,
      TauCeti.mpullback_apply_pair, mextDerivₗ_apply, mextDeriv_innerProductContactForm_apply,
      mfderiv_eq_fderiv, fderiv_comp x L.differentiableAt (hψD x)]
    simp only [Function.comp_apply, ContinuousLinearMap.fderiv, ContinuousLinearMap.comp_apply,
      ContinuousLinearEquiv.coe_coe, NormedSpace.fromTangentSpace_apply,
      ContinuousLinearMap.coe_comp, NormedSpace.fromTangentSpace_symm_apply,
      stdSymplecticForm_apply]
    -- The `(q, p)` coordinates of `L z` are those of `z`, by definition of `L`.
    rfl

/-- **A Darboux primitive.** If `dβ` is nondegenerate at `s₀`, then near `s₀` the one-form `β` is
the pullback of the primitive `-⟪p, dq⟫` of the standard symplectic form along Darboux coordinates
`ψ`, plus the differential of a smooth function `f`. -/
private theorem exists_diffeomorph_fderiv_eq_add_inner {n : ℕ} (hK : finrank ℝ K = 2 * n)
    (β : SmoothForm 𝓘(ℝ, K) K ℝ 1) {s₀ : K}
    (hβ : ((mextDerivₗ 𝓘(ℝ, K) 1 β).bilinFormAt s₀).Nondegenerate) :
    ∃ (ψ : K ≃ₘ⟮𝓘(ℝ, K), 𝓘(ℝ, EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n))⟯
        (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n))) (f : K → ℝ),
      ψ s₀ = 0 ∧ f s₀ = 0 ∧ ContDiff ℝ ∞ f ∧ ∀ᶠ x in 𝓝 s₀, ∀ a : TangentSpace 𝓘(ℝ, K) x,
        fderiv ℝ f x a = β.1 x ![a] + ⟪(ψ x).2, (fderiv ℝ ψ x a).1⟫_ℝ := by
  -- The exterior derivative `σ = dβ`, read as a function on the model space.
  set σ : K → K [⋀^Fin 2]→L[ℝ] ℝ := mextDeriv β.1
  have hσs : ContDiff ℝ ∞ σ := by
    have := (mextDerivₗ 𝓘(ℝ, K) 1 β).isSmoothForm
    rw [mextDerivₗ_apply] at this
    exact isSmoothForm_modelSpace_iff.1 this
  have hdσ (x : K) : extDeriv σ x = 0 := by
    rw [← mextDeriv_eq_extDeriv]
    exact congrFun (SmoothForm.mextDeriv_mextDeriv β) x
  obtain ⟨ψ, hψ₀, hψ⟩ := exists_diffeomorph_eventually_stdSymplecticForm_fderiv_eq (r := ⊤) hK
    le_top isOpen_univ (mem_univ s₀) hσs.contDiffOn (fun x _ ↦ hdσ x)
    fun _ ↦ SmoothForm.eq_zero_of_forall_mextDeriv_eq_zero hβ
  have hψd : ContDiff ℝ ∞ ψ := contMDiff_iff_contDiff.1 ψ.contMDiff
  -- The primitive `θ = -⟪p, dq⟫` of the standard symplectic form, read in the coordinates `ψ`.
  obtain ⟨θ, hθ, hdθ⟩ := exists_smoothForm_apply_eq_neg_inner hψd
  -- So `β - θ` is closed near `s₀`, and has a smooth primitive `f` there.
  have hclosed : ∀ᶠ x in 𝓝 s₀, mextDeriv (β - θ).1 x = 0 := by
    filter_upwards [hψ] with x hx
    rw [← mextDerivₗ_apply, map_sub, Submodule.coe_sub, Pi.sub_apply, mextDerivₗ_apply,
      mextDerivₗ_apply, sub_eq_zero]
    refine ContinuousAlternatingMap.ext fun v ↦ ?_
    obtain ⟨a, b, rfl⟩ : ∃ a b, v = ![a, b] := ⟨v 0, v 1, funext fun i ↦ by fin_cases i <;> rfl⟩
    exact (hx.2 a b).symm.trans (hdθ x a b).symm
  obtain ⟨U₀, hU₀, φ, hφ, hdφ⟩ := exists_mextDeriv_eq_nhds (k := 0) (r := ⊤) le_top
    (β - θ).isSmoothForm hclosed
  rw [RoughForm.eq_ofFunction φ] at hφ hdφ
  set f₀ : K → ℝ := fun x ↦ φ x 0
  have hf₀ : ContDiff ℝ ∞ f₀ := contMDiff_iff_contDiff.1 (isSmoothForm_ofFunction_iff.1 hφ)
  refine ⟨ψ, fun x ↦ f₀ x - f₀ s₀, hψ₀, sub_self _, hf₀.sub contDiff_const, ?_⟩
  filter_upwards [hU₀] with x hx a
  have h := congrArg (fun A ↦ A ![a]) (hdφ x hx)
  simp only [mextDeriv_ofFunction_apply, mfderiv_eq_fderiv] at h
  rw [Submodule.coe_sub, Pi.sub_apply, ContinuousAlternatingMap.sub_apply, hθ, sub_neg_eq_add]
    at h
  rw [fderiv_sub_const]
  exact h

/-- **Darboux coordinates for a contactization form.** Let `β` be a smooth one-form on a
finite-dimensional real normed space `K` of dimension `2 n` whose exterior derivative is
nondegenerate at `s₀`. Then there is a diffeomorphism `G : K × ℝ ≃ ℝⁿ × ℝⁿ × ℝ` with `G (s₀, 0) = 0`
which, on `U × ℝ` for an open neighbourhood `U` of `s₀`, pulls the standard contact form
`dz - Σᵢ pᵢ dqᵢ` back exactly to the contactization form `dt + β`. -/
theorem exists_diffeomorph_mpullback_innerProductContactForm_eq_contactization {n : ℕ}
    (hK : finrank ℝ K = 2 * n) (β : SmoothForm 𝓘(ℝ, K) K ℝ 1) {s₀ : K}
    (hβ : ((mextDerivₗ 𝓘(ℝ, K) 1 β).bilinFormAt s₀).Nondegenerate) :
    ∃ (G : (K × ℝ) ≃ₘ⟮𝓘(ℝ, K).prod 𝓘(ℝ),
        𝓘(ℝ, EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) × ℝ)⟯
        (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) × ℝ)) (U : Set K),
      IsOpen U ∧ s₀ ∈ U ∧ G (s₀, 0) = 0 ∧ ∀ p ∈ U ×ˢ (univ : Set ℝ),
        mpullback (𝓘(ℝ, K).prod 𝓘(ℝ))
          𝓘(ℝ, EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) × ℝ) G
          (innerProductContactForm (EuclideanSpace ℝ (Fin n))).1 p =
        (-β).contactization.1 p := by
  obtain ⟨ψ, f, hψ₀, hf₀, hf, hdf⟩ := exists_diffeomorph_fderiv_eq_add_inner hK β hβ
  set V := EuclideanSpace ℝ (Fin n)
  -- The shear `(s, t) ↦ (ψ s, t + f s)`, reassociated into `V × V × ℝ`.
  set G := (ψ.prodShear (contMDiff_iff_contDiff.2 hf)).trans
    (ContinuousLinearEquiv.prodAssoc ℝ V V ℝ).toDiffeomorph
  have hG (p : K × ℝ) : G p = ((ψ p.1).1, (ψ p.1).2, p.2 + f p.1) := by simp [G]
  have hdG (p : K × ℝ) (w : TangentSpace (𝓘(ℝ, K).prod 𝓘(ℝ)) p) :
      mfderiv (𝓘(ℝ, K).prod 𝓘(ℝ)) 𝓘(ℝ, V × V × ℝ) G p w =
        ((fderiv ℝ ψ p.1 (Manifold.tangentSpaceProdEquiv p w).1).1,
          (fderiv ℝ ψ p.1 (Manifold.tangentSpaceProdEquiv p w).1).2,
          NormedSpace.fromTangentSpace p.2 (Manifold.tangentSpaceProdEquiv p w).2 +
            fderiv ℝ f p.1 (Manifold.tangentSpaceProdEquiv p w).1) := by
    rw [Diffeomorph.coe_trans, mfderiv_comp_apply p
      ((ContinuousLinearEquiv.prodAssoc ℝ V V ℝ).toDiffeomorph.mdifferentiable (by simp) _)
      ((ψ.prodShear _).mdifferentiable (by simp) p), mfderiv_eq_fderiv,
      ContinuousLinearEquiv.coe_toDiffeomorph, ContinuousLinearEquiv.fderiv,
      Diffeomorph.mfderiv_prodShear_apply _ _ (by simp), mvfderiv_eq_fderiv_apply,
      mvfderiv_eq_fderiv_apply]
    -- The tangent-space identifications of the model spaces are the identity.
    rfl
  obtain ⟨U, hUf, hU, hs₀U⟩ := eventually_nhds_iff.1 hdf
  refine ⟨G, U, hU, hs₀U, by simp [hG, hψ₀, hf₀], fun p hp ↦ ?_⟩
  refine ContinuousAlternatingMap.ext fun v ↦ ?_
  obtain ⟨w, rfl⟩ : ∃ w, v = ![w] := ⟨v 0, funext fun i ↦ by fin_cases i; rfl⟩
  rw [mpullback_apply_one, innerProductContactForm_apply, hdG, SmoothForm.contactization_apply,
    hUf p.1 hp.1, Submodule.coe_neg, Pi.neg_apply, ContinuousAlternatingMap.neg_apply, hG]
  ring

end Contactization

/-! ### Darboux charts on manifolds -/

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless] [TopologicalSpace M]
  [ChartedSpace H M] [T2Space M] [IsManifold I ∞ M] {α : SmoothForm I M ℝ 1}

omit [FiniteDimensional ℝ E] [I.Boundaryless] [T2Space M] in
/-- A one-form takes equal values at equal points on equal vectors. The vectors lie in the tangent
spaces at the two points, which are both the model space. -/
private theorem apply_eq_of_eq (α : SmoothForm I M ℝ 1) {y y' : M} (h : y = y')
    {u : TangentSpace I y} {u' : TangentSpace I y'} (hu : (u : E) = u') :
    α.1 y ![u] = α.1 y' ![u'] := by
  subst h
  exact congrArg (fun z ↦ α.1 y ![z]) hu

/-- **The local Reeb flow chart.** Let `ι : F → M` be a hypersurface transverse at `0` to the Reeb
vector field of a contact form `α`. Then the local Reeb flow map `(s, t) ↦ φₜ(ι s)` restricts to a
partial diffeomorphism `Φ` from a neighbourhood of `(0, 0)` inside a prescribed `U × ℝ`, which pulls
`α` back to the contactization form `dt + ι^* α`. -/
private theorem exists_partialDiffeomorph_reebFlow (hα : α.IsContactForm)
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F] {ι : F → M}
    (hι : ContMDiff 𝓘(ℝ, F) I ∞ ι) (hdim : finrank ℝ F + 1 = finrank ℝ E)
    (hιinj : Function.Injective (mfderiv 𝓘(ℝ, F) I ι 0))
    (hR : α.reebVectorField (ι 0) ∉ (mfderiv 𝓘(ℝ, F) I ι 0).range) {U : Set F} (hU : IsOpen U)
    (h0U : (0 : F) ∈ U) :
    ∃ Φ : PartialDiffeomorph (𝓘(ℝ, F).prod 𝓘(ℝ)) I (F × ℝ) M ∞,
      ((0 : F), (0 : ℝ)) ∈ Φ.source ∧ Φ (0, 0) = ι 0 ∧ Φ.source ⊆ U ×ˢ univ ∧
      ∀ q ∈ Φ.source, ∀ w : TangentSpace (𝓘(ℝ, F).prod 𝓘(ℝ)) q,
        α.1 (Φ q) ![mfderiv (𝓘(ℝ, F).prod 𝓘(ℝ)) I Φ q w] =
          (-SmoothForm.mpullback ι hι α).contactization.1 q ![w] := by
  set R := α.reebVectorField
  have hR1 : ContMDiff I I.tangent 1 (T% R) := hα.contMDiff_reebVectorField.of_le (by simp)
  have hp₀ : ((0 : ℝ), ι 0) ∈ flowDomain R := mem_flowDomain_zero hR1 _
  obtain ⟨Φ₀, hΦ₀, hΦ₀eq⟩ := hα.isLocalDiffeomorphAt_flowOf_reebVectorField_comp hι hdim
    (p := ((0 : F), (0 : ℝ))) hιinj hR hp₀
  -- Restrict to the flow domain over `U`, where the flow map pulls `α` back to `dt + ι^* α`.
  set D : Set (F × ℝ) := {q | (q.2, ι q.1) ∈ flowDomain R} ∩ U ×ˢ univ
  have hD : IsOpen D := (isOpen_setOf_mem_flowDomain hR1 continuous_snd
    (hι.continuous.comp continuous_fst)).inter (hU.prod isOpen_univ)
  refine ⟨Φ₀.restrOpen D hD, ?_, ?_, fun q hq ↦ ?_, fun q hq w ↦ ?_⟩
  · rw [PartialDiffeomorph.restrOpen_source]
    exact ⟨hΦ₀, hp₀, h0U, mem_univ _⟩
  · rw [PartialDiffeomorph.coe_restrOpen, ← hΦ₀eq hΦ₀]
    exact flowOf_zero R (ι 0)
  · rw [PartialDiffeomorph.restrOpen_source] at hq
    exact hq.2.2
  rw [PartialDiffeomorph.restrOpen_source] at hq
  have hΦ : (fun q : F × ℝ ↦ flowOf R q.2 (ι q.1)) =ᶠ[𝓝 q] Φ₀.restrOpen D hD := by
    rw [PartialDiffeomorph.coe_restrOpen]
    exact Filter.eventuallyEq_of_mem (Φ₀.open_source.mem_nhds hq.1) hΦ₀eq
  have h := congrArg (fun A ↦ A ![w]) (mpullback_flowOf_comp_apply_eq_contactization
    hα.contMDiff_reebVectorField hι hα.apply_reebVectorField
    hα.interior_mextDeriv_reebVectorField hq.2.1)
  rw [TauCeti.mpullback_apply_one] at h
  rw [← h]
  -- The flow map and `Φ` agree near `q`; `tangentSpaceCast` is the identity on vectors.
  exact apply_eq_of_eq α hΦ.eq_of_nhds.symm (by rw [hΦ.mfderiv_eq]; rfl)

/-- **The Darboux theorem for contact forms.** Around every point `x₀` of a boundaryless manifold
with a smooth contact form `α`, there are `n` with `dim M = 2 n + 1` and a smooth partial
diffeomorphism `chart` from `M` to `ℝⁿ × ℝⁿ × ℝ` with `chart x₀ = 0` which pulls the standard
contact form `dz - Σᵢ pᵢ dqᵢ` back exactly to `α` on its source. So `chart` is a strict
contactomorphism onto an open subset of the standard contact space, not merely one up to a
positive conformal factor as in `TauCeti.SmoothForm.IsContactForm.exists_darbouxChart`. -/
theorem SmoothForm.IsContactForm.exists_strictDarbouxChart (hα : α.IsContactForm) (x₀ : M) :
    ∃ (n : ℕ) (chart : PartialDiffeomorph I
        𝓘(ℝ, EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) × ℝ) M
        (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) × ℝ) ∞),
      finrank ℝ E = 2 * n + 1 ∧ x₀ ∈ chart.source ∧ chart x₀ = 0 ∧
      ∀ x ∈ chart.source, ∀ v : TangentSpace I x,
        (innerProductContactForm (EuclideanSpace ℝ (Fin n))).1 (chart x)
          ![mvfderiv I chart x v] = α.1 x ![v] := by
  -- A hypersurface `ι : K → M` through `x₀` transverse to the Reeb vector field.
  obtain ⟨K, ι, hι, rfl, hιinj, hRι, hdimK⟩ :=
    exists_hypersurface_notMem_range_mfderiv (n := ⊤) le_top (hα.reebVectorField_ne_zero x₀)
  set β := SmoothForm.mpullback ι hι α
  have hβ := hα.nondegenerate_bilinFormAt_mextDerivₗ_mpullback hι hdimK hιinj hRι
  -- `dβ` is symplectic at `0`, so `K` has even dimension `2 n`.
  obtain ⟨n, hn⟩ : ∃ n, finrank ℝ K = 2 * n := by
    obtain ⟨m, hm⟩ := (SymplecticForm.ofContinuousAlternatingMap (mextDeriv β.1 0)
      fun _ ↦ SmoothForm.eq_zero_of_forall_mextDeriv_eq_zero hβ).even_finrank
    exact ⟨m, hm.trans (two_mul m).symm⟩
  set V := EuclideanSpace ℝ (Fin n)
  -- Darboux coordinates `G` for `dt + β` on `K × ℝ`, and the Reeb flow chart `Φ` pulling `α` back
  -- to `dt + β`. The chart is `G ∘ Φ⁻¹`.
  obtain ⟨G, U, hU, h0U, hG0, hGβ⟩ :=
    exists_diffeomorph_mpullback_innerProductContactForm_eq_contactization hn β hβ
  obtain ⟨Φ, h0, hΦ0, hΦU, hΦα⟩ := exists_partialDiffeomorph_reebFlow hα hι hdimK hιinj hRι hU h0U
  set G' := G.toPartialDiffeomorph
  have hG' : (⇑G' : K × ℝ → V × V × ℝ) = G := rfl
  have hsrc (x : M) : x ∈ (Φ.symm.trans G').source ↔ x ∈ Φ.target := by
    simp [G']
  refine ⟨n, Φ.symm.trans G', by omega, (hsrc _).2 (hΦ0 ▸ Φ.map_source h0), ?_, ?_⟩
  · rw [PartialDiffeomorph.coe_trans, Function.comp_apply, ← hΦ0]
    simp only [PartialDiffeomorph.symm_toPartialEquiv]
    rw [PartialEquiv.left_inv _ h0]
    exact hG0
  intro x hx v
  have hxt : x ∈ Φ.target := (hsrc x).1 hx
  set q := Φ.symm x
  have hq : q ∈ Φ.source := Φ.symm.map_source hxt
  set w := mfderiv I (𝓘(ℝ, K).prod 𝓘(ℝ)) Φ.symm x v
  -- The differential of the chart is that of `G` after that of `Φ⁻¹`.
  have hd : mvfderiv I (Φ.symm.trans G') x v =
      mfderiv (𝓘(ℝ, K).prod 𝓘(ℝ)) 𝓘(ℝ, V × V × ℝ) G q w := by
    rw [mvfderiv_apply_eq_mfderiv_apply, PartialDiffeomorph.coe_trans, hG',
      mfderiv_comp_apply x (G.mdifferentiable (by simp) _) (Φ.symm.mdifferentiableAt (by simp) hxt)]
  have hcx : (Φ.symm.trans G') x = G q := rfl
  have hG := congrArg (fun A ↦ A ![w]) (hGβ q (hΦU hq))
  rw [TauCeti.mpullback_apply_one] at hG
  rw [hd, hcx, hG, ← hΦα q hq w]
  -- `Φ` undoes `Φ⁻¹`, on points and on tangent vectors.
  exact apply_eq_of_eq α (Φ.right_inv hxt) (Φ.mfderiv_apply_mfderiv_symm_apply (by simp) hxt v)

end TauCeti
