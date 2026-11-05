/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Contact.Symplectization
public import TauCeti.Geometry.Symplectic.Liouville.Scaling
import TauCeti.Geometry.Manifold.DifferentialForm.Naturality

/-!
# The cylindrical end of a completion is a symplectization

Let `α` be a smooth one-form on a boundaryless manifold `M` whose Liouville field `Z`,
`ι_Z dα = α`, is smooth and complete, with flow `ψ`. The **Liouville flow map**
`Ψ : ℝ × M → M`, `Ψ(t, x) = ψₜ(x)`, pulls `α` back to the symplectization form `eᵗ α` of
`TauCeti.SmoothForm.symplectization` (`TauCeti.mpullback_globalFlow_uncurry_eq_symplectization`):

`Ψ^* α = eᵗ α`.

Indeed `dΨ(s, w) = s Z + dψₜ(w)` at `(t, x)`. The primitive vanishes on its Liouville field,
`α(Z) = dα(Z, Z) = 0`, and the flow rescales the primitive, `ψₜ^* α = eᵗ α`
(`TauCeti.mpullback_globalFlow_eq_exp_smul_of_interior_eq`). Taking exterior derivatives, `Ψ`
also pulls `dα` back to `d(eᵗ α)` (`TauCeti.mpullback_globalFlow_uncurry_mextDerivₗ`).

The identity is natural: for a smooth map `ι : S → M`, the map `(t, s) ↦ ψₜ(ι s)` pulls `α` back
to the symplectization form `eᵗ ι^* α` of the restricted form
(`TauCeti.mpullback_globalFlow_comp_eq_symplectization`). The case of interest is the inclusion
`ι` of the boundary `∂W` of a Liouville domain `W ⊆ M` (`TauCeti.IsLiouvilleDomain`), a regular
level of a defining function; there `ι^* α` is a contact form
(`TauCeti.IsContactType.isContactForm_mpullback`), so `d(eᵗ ι^* α)` is symplectic. When `M` is a
completion of `W` (`TauCeti.IsLiouvilleCompletion`), the map `(t, y) ↦ ψₜ(y)` restricts to a
bijection from `(0, ∞) × ∂W` onto the complement of `W`
(`TauCeti.IsLiouvilleCompletion.bijOn_flowOf_Ioi_prod_frontier`), and from `[0, ∞) × ∂W` onto
the complement of its interior (`TauCeti.IsLiouvilleCompletion.bijOn_flowOf_Ici_prod_frontier`),
and the radial coordinate of the point `ψₜ(y)` is `r = eᵗ`
(`TauCeti.IsLiouvilleCompletion.liouvilleRadialCoordinate_flowOf`). Together these describe the
cylindrical end of the completion in the coordinates `(r, y) ∈ (1, ∞) × ∂W` of its model
`W ∪ (∂W × [1, ∞))`: the primitive there is `r α|∂W`, the positive half of the symplectization of
the contact manifold `(∂W, α|∂W)`. That the inverse of this parametrization is smooth is not
treated here.

## Main results

* `TauCeti.mpullback_globalFlow_uncurry_eq_symplectization`: the Liouville flow map pulls the
  primitive back to the symplectization form, `Ψ^* α = eᵗ α`.
* `TauCeti.mpullback_globalFlow_uncurry_mextDerivₗ`: it pulls `dα` back to `d(eᵗ α)`.
* `TauCeti.mpullback_globalFlow_comp_eq_symplectization`,
  `TauCeti.mpullback_globalFlow_comp_mextDerivₗ`: the same along a smooth map `ι : S → M`, with
  `ι^* α` in place of `α`.

## References

* P. Seidel, *A biased view of symplectic cohomology*, Current Developments in Mathematics 2006,
  Section 3 (Liouville domains and their completions).
* K. Cieliebak, Y. Eliashberg, *From Stein to Weinstein and Back*, AMS Colloquium Publications 59,
  2012, Section 11.1.
* D. McDuff, D. Salamon, *Introduction to Symplectic Topology*, 3rd ed., Oxford, 2017,
  Section 3.5 (hypersurfaces of contact type and their symplectizations).
-/

public section

open Set
open scoped Manifold

namespace TauCeti

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless] [TopologicalSpace M]
  [ChartedSpace H M] [T2Space M] [IsManifold I (⊤ : ℕ∞) M] {Z : (x : M) → TangentSpace I x}

section Flow

open scoped ContDiff

variable {E' H' S : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [TopologicalSpace H']
  {J : ModelWithCorners ℝ E' H'} [TopologicalSpace S] [ChartedSpace H' S] [IsManifold J ∞ S]
  (hc : IsCompleteVectorField Z) (hZ : ContMDiff I I.tangent ∞ (T% Z))
  {α : SmoothForm I M ℝ 1}
include hc hZ

/-- **The Liouville flow map pulls the primitive back to the symplectization form.** Let the
smooth complete vector field `Z` be the Liouville field of the one-form `α`, `ι_Z dα = α`, with
flow `ψ`. Then the map `(t, x) ↦ ψₜ(x)` from `ℝ × M` to `M` pulls `α` back to `eᵗ α`. -/
theorem mpullback_globalFlow_uncurry_eq_symplectization
    (hZα : (mextDeriv α.1).interior Z = α.1) :
    SmoothForm.mpullback (fun p : ℝ × M ↦ globalFlow Z (hZ.of_le (by simp)) hc p.1 p.2)
      (contMDiff_globalFlow_uncurry hc le_top hZ) α = α.symplectization := by
  have hψ := contMDiff_globalFlow_uncurry hc le_top hZ
  -- The primitive vanishes on its Liouville field: `α(Z) = dα(Z, Z) = 0`.
  have hαZ (y : M) : SmoothForm.degreeOneEquiv α y (Z y) = 0 := by
    have h := congrArg (fun β ↦ β y ![]) (RoughForm.interior_self Z (mextDeriv α.1))
    simpa only [hZα, RoughForm.interior_apply, Pi.zero_apply, ContinuousAlternatingMap.coe_zero,
      SmoothForm.degreeOneEquiv_apply_apply_vec] using h
  apply Subtype.ext
  funext p
  refine ContinuousAlternatingMap.ext fun v ↦ ?_
  obtain ⟨w, rfl⟩ : ∃ w, v = ![w] := ⟨v 0, funext fun i ↦ by fin_cases i; rfl⟩
  -- The flow rescales the primitive: `ψₜ^* α = eᵗ α`.
  have hscale : SmoothForm.degreeOneEquiv α (globalFlow Z (hZ.of_le (by simp)) hc p.1 p.2)
      (mfderiv I I (globalFlow Z (hZ.of_le (by simp)) hc p.1) p.2
        (Manifold.tangentSpaceProdEquiv p w).2) =
      Real.exp p.1 * SmoothForm.degreeOneEquiv α p.2 (Manifold.tangentSpaceProdEquiv p w).2 := by
    have h := congrArg (fun β ↦ β p.2 fun _ ↦ (Manifold.tangentSpaceProdEquiv p w).2)
      (mpullback_globalFlow_eq_exp_smul_of_interior_eq hc (hZ.of_le (by simp)) α.mdifferentiable
        rfl hZα p.1)
    simpa only [SmoothForm.degreeOneEquiv_apply_apply, mpullback_apply, Pi.smul_apply,
      ContinuousAlternatingMap.smul_apply, smul_eq_mul] using h
  -- The differential of `(t, x) ↦ ψₜ x` sends `(s, u)` to `s Z + dψₜ u`.
  have hd : mfderiv (𝓘(ℝ).prod I) I
      (fun p : ℝ × M ↦ globalFlow Z (hZ.of_le (by simp)) hc p.1 p.2) p w =
      w.1 • Z (globalFlow Z (hZ.of_le (by simp)) hc p.1 p.2) +
        mfderiv I I (globalFlow Z (hZ.of_le (by simp)) hc p.1) p.2
          (Manifold.tangentSpaceProdEquiv p w).2 := by
    rw [mfderiv_prod_eq_add_apply ((hψ p).mdifferentiableAt (by simp)),
      (isMIntegralCurve_globalFlow (hZ.of_le (by simp)) hc p.2 p.1).mfderiv,
      Manifold.tangentSpaceProdEquiv_apply]
    -- `smulRight 1 Z` sends `s` to `s • Z`, reading `TangentSpace 𝓘(ℝ) t` as `ℝ`.
    rfl
  rw [SmoothForm.mpullback_apply, SmoothForm.symplectization_apply,
    ← SmoothForm.degreeOneEquiv_apply_apply_vec]
  simp only [Matrix.cons_val_fin_one]
  rw [← SmoothForm.degreeOneEquiv_apply_apply, hd, map_add, map_smul, hαZ, smul_zero, zero_add,
    hscale]

/-- **The Liouville flow map pulls `dα` back to `d(eᵗ α)`.** Let the smooth complete vector
field `Z` be the Liouville field of the one-form `α`, `ι_Z dα = α`, with flow `ψ`. Then the map
`(t, x) ↦ ψₜ(x)` from `ℝ × M` to `M` pulls `dα` back to `d(eᵗ α)`. -/
theorem mpullback_globalFlow_uncurry_mextDerivₗ (hZα : (mextDeriv α.1).interior Z = α.1) :
    SmoothForm.mpullback (fun p : ℝ × M ↦ globalFlow Z (hZ.of_le (by simp)) hc p.1 p.2)
      (contMDiff_globalFlow_uncurry hc le_top hZ) (mextDerivₗ I 1 α) =
      mextDerivₗ (𝓘(ℝ).prod I) 1 α.symplectization := by
  rw [← SmoothForm.mextDerivₗ_mpullback, mpullback_globalFlow_uncurry_eq_symplectization hc hZ hZα]

/-- **The Liouville flow out of a submanifold.** Let the smooth complete vector field `Z` be the
Liouville field of the one-form `α`, `ι_Z dα = α`, with flow `ψ`, and let `ι : S → M` be smooth.
Then the map `(t, s) ↦ ψₜ(ι s)` from `ℝ × S` to `M` pulls `α` back to the symplectization form
`eᵗ ι^* α` of the restricted form. For the inclusion of the boundary of a Liouville domain, this
identifies the flow-out of the boundary with the symplectization of the boundary. -/
theorem mpullback_globalFlow_comp_eq_symplectization (hZα : (mextDeriv α.1).interior Z = α.1)
    {ι : S → M} (hι : ContMDiff J I ∞ ι) :
    SmoothForm.mpullback (fun p : ℝ × S ↦ globalFlow Z (hZ.of_le (by simp)) hc p.1 (ι p.2))
      ((contMDiff_globalFlow_uncurry hc le_top hZ).comp
        (contMDiff_fst.prodMk (hι.comp contMDiff_snd))) α =
      (SmoothForm.mpullback ι hι α).symplectization := by
  have hlift : ContMDiff (𝓘(ℝ).prod J) (𝓘(ℝ).prod I) ∞ (fun p : ℝ × S ↦ (p.1, ι p.2)) :=
    contMDiff_fst.prodMk (hι.comp contMDiff_snd)
  -- The map `(t, s) ↦ (t, ι s)` is the lift of `ι` along the constant function `1`, so it pulls
  -- `eᵗ α` back to `eᵗ ι^* α`.
  have hsymp : SmoothForm.mpullback (fun p : ℝ × S ↦ (p.1, ι p.2)) hlift α.symplectization =
      (SmoothForm.mpullback ι hι α).symplectization := by
    have hfun : symplectizationLift ι (fun _ ↦ (1 : ℝ)) = fun p : ℝ × S ↦ (p.1, ι p.2) :=
      funext fun p ↦ by simp
    have key := SmoothForm.mpullback_symplectizationLift_symplectization hι contMDiff_const
      (fun _ ↦ one_pos) (α := SmoothForm.mpullback ι hι α) (α' := α) fun x ↦ by rw [one_smul]
    have hcongr : ∀ {f g : ℝ × S → ℝ × M} (hfg : f = g) (hf : ContMDiff (𝓘(ℝ).prod J)
        (𝓘(ℝ).prod I) ∞ f) (hg : ContMDiff (𝓘(ℝ).prod J) (𝓘(ℝ).prod I) ∞ g),
        SmoothForm.mpullback (F := ℝ) (k := 1) f hf = SmoothForm.mpullback g hg := by
      rintro f g rfl hf hg
      rfl
    rwa [hcongr hfun] at key
  have hcomp := SmoothForm.mpullback_comp (F := ℝ) (k := 1) _ _ hlift
    (contMDiff_globalFlow_uncurry hc le_top hZ)
  rw [LinearMap.ext_iff] at hcomp
  refine (hcomp α).trans ?_
  rw [LinearMap.comp_apply, mpullback_globalFlow_uncurry_eq_symplectization hc hZ hZα, hsymp]

/-- **The Liouville flow out of a submanifold pulls `dα` back to `d(eᵗ ι^* α)`.** Let the smooth
complete vector field `Z` be the Liouville field of the one-form `α`, `ι_Z dα = α`, with flow
`ψ`, and let `ι : S → M` be smooth. Then the map `(t, s) ↦ ψₜ(ι s)` from `ℝ × S` to `M` pulls
`dα` back to `d(eᵗ ι^* α)`, which is symplectic exactly when `ι^* α` is a contact form
(`TauCeti.SmoothForm.isSymplectic_mextDerivₗ_symplectization_iff`). -/
theorem mpullback_globalFlow_comp_mextDerivₗ (hZα : (mextDeriv α.1).interior Z = α.1)
    {ι : S → M} (hι : ContMDiff J I ∞ ι) :
    SmoothForm.mpullback (fun p : ℝ × S ↦ globalFlow Z (hZ.of_le (by simp)) hc p.1 (ι p.2))
      ((contMDiff_globalFlow_uncurry hc le_top hZ).comp
        (contMDiff_fst.prodMk (hι.comp contMDiff_snd))) (mextDerivₗ I 1 α) =
      mextDerivₗ (𝓘(ℝ).prod J) 1 (SmoothForm.mpullback ι hι α).symplectization := by
  rw [← SmoothForm.mextDerivₗ_mpullback,
    mpullback_globalFlow_comp_eq_symplectization hc hZ hZα hι]

end Flow

end TauCeti
