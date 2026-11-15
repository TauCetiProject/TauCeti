/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.DifferentialForm.Flow.Family
public import TauCeti.Geometry.Symplectic.Hamiltonian.SymplecticVectorField
public import TauCeti.Geometry.Symplectic.Manifold.Family

/-!
# Moser's stability theorem

A smooth family of two-forms on a manifold `M` is a smooth two-form `σ` on `ℝ × M`, whose slice
at time `t` is the form `σ_t = ι_t^* σ` on `M`, pulled back along the inclusion `ι_t : x ↦ (t, x)`.
Its velocity is the slice `ι_t^* L_{∂_t} σ` of the Lie derivative along the time coordinate field
(`TauCeti.hasDerivAt_mpullback_prodMk`). Let every `σ_t` be symplectic, and let the family be
*exact* in time: there is a smooth family of one-forms `α_t` with `ι_t^* L_{∂_t} σ = dα_t`.

**Moser's trick** solves `ι_{X_t} σ_t = -α_t` for a time-dependent vector field, the
**Moser vector field** `X_t = (σ_t♭)⁻¹ (-α_t)`, by inverting the flat maps of the slices
(`TauCeti.SmoothTwoForm.IsNondegenerate.interiorEquiv`). Two facts make it work.

* The vector field `X_t` depends smoothly on `(t, x)`, because the flat maps of the slices and
  their inverses do (`TauCeti.SmoothTwoForm.contMDiff_interiorEquiv_symm_mpullback_prodMk`).
* For a single symplectic form `τ` on `M`, Cartan's formula gives `L_X τ = d(ι_X τ)`; so the
  field `X = (τ♭)⁻¹ β` has `L_X τ = dβ`
  (`TauCeti.SmoothTwoForm.IsSymplectic.mlieDerivForm_interiorEquiv_symm`). Hence the rate
  `ι_t^* L_{∂_t} σ + L_{X_t} σ_t = dα_t - dα_t` vanishes.

By Moser's principle for families of forms
(`TauCeti.mpullback_timeDependentFlowOf_mpullback_prodMk_eq`), the time-dependent flow `φ_{s,t}`
of any vector field with `ι_{X_t} σ_t = -α_t` then satisfies `φ_{s,t}^* σ_t = σ_s`, as soon as
its suspension is complete (`TauCeti.SmoothTwoForm.mpullback_timeDependentFlowOf_eq`).

The suspension is complete when every `α_t` vanishes outside one fixed compact set, since `X_t`
vanishes where `α_t` does. This gives **Moser's stability theorem** with support control
(`TauCeti.SmoothTwoForm.exists_isotopy_mpullback_eq_of_isCompact`): there is an isotopy `ψ_t`,
jointly smooth in `(t, x)`, with `ψ_0 = id` and `ψ_t^* σ_t = σ_0`, which fixes every point at
which `α_t` vanishes for all `t`, and in particular every point outside the compact set. On a
compact manifold no support condition is needed
(`TauCeti.SmoothTwoForm.exists_isotopy_mpullback_eq`).

The families are parametrized by the whole real line, and the primitives `α_t` are part of the
data. Equality of the de Rham classes of the slices alone does not provide them: it is the
exactness of the velocity which the theorem uses.

## Main results

* `TauCeti.SmoothTwoForm.mpullback_timeDependentFlowOf_eq`: a complete Moser flow pulls `σ_t`
  back to `σ_s`.
* `TauCeti.SmoothTwoForm.exists_isotopy_mpullback_eq_of_isCompact`: Moser's stability theorem for
  primitives supported in a fixed compact set.
* `TauCeti.SmoothTwoForm.exists_isotopy_mpullback_eq`: Moser's stability theorem on a compact
  manifold.

## References

* J. Moser, *On the volume elements on a manifold*, Transactions of the American Mathematical
  Society 120 (1965), 286–294.
* D. McDuff, D. Salamon, *Introduction to Symplectic Topology*, 3rd ed., Oxford, 2017,
  Section 3.2 (Moser isotopy and Moser stability).
* A. Cannas da Silva, *Lectures on Symplectic Geometry*, Lecture Notes in Mathematics 1764,
  Springer, 2001, Lecture 7 (Moser's theorems and Moser's trick).

## Acknowledgements

The isotopy assembly here (completeness of the suspension, the flow diffeomorphisms
`TauCeti.timeDependentFlowDiffeomorph`, and Moser's principle for families of forms) follows the
same skeleton as the Gray stability proof for contact forms in Tau Ceti pull request
https://github.com/TauCetiProject/TauCeti/pull/35119.
-/

public section

noncomputable section

open Bundle Set Function
open scoped ContDiff Manifold Topology

namespace TauCeti

namespace SmoothTwoForm

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M]

/-! ### Moser's stability theorem -/

variable [I.Boundaryless] [T2Space M]

/-- **Moser's isotopy lemma.** Let `σ` be a smooth two-form on `ℝ × M` whose slices
`σ_t = ι_t^* σ` are symplectic, and let `α` be a smooth one-form on `ℝ × M` whose slices are
primitives of the velocity, `ι_t^* L_{∂_t} σ = dα_t`. If a time-dependent vector field `X` solves
Moser's equation `ι_{X_t} σ_t = -α_t` and its suspension is complete, then its time-dependent flow
`φ_{s,t}` pulls `σ_t` back to `σ_s`, for all times `s` and `t`. -/
theorem mpullback_timeDependentFlowOf_eq (σ : SmoothForm (𝓘(ℝ, ℝ).prod I) (ℝ × M) ℝ 2)
    (α : SmoothForm (𝓘(ℝ, ℝ).prod I) (ℝ × M) ℝ 1)
    (hσ : ∀ t, IsSymplectic
      (SmoothForm.mpullback (Prod.mk t) (contMDiff_const.prodMk contMDiff_id) σ))
    (hα : ∀ t, TauCeti.mpullback I (𝓘(ℝ, ℝ).prod I) (Prod.mk t)
        (mlieDerivForm (fun _ ↦ ((1 : ℝ), (0 : E))) σ.1) =
      mextDeriv (SmoothForm.mpullback (Prod.mk t) (contMDiff_const.prodMk contMDiff_id) α).1)
    {X : ℝ → (x : M) → TangentSpace I x}
    (hX : ∀ t, RoughForm.interior (X t)
        (SmoothForm.mpullback (Prod.mk t) (contMDiff_const.prodMk contMDiff_id) σ).1 =
      -(SmoothForm.mpullback (Prod.mk t) (contMDiff_const.prodMk contMDiff_id) α).1)
    (hc : IsCompleteVectorField (timeDependentSuspensionField X)) (s t : ℝ) :
    TauCeti.mpullback I I (timeDependentFlowOf X s t)
        (SmoothForm.mpullback (Prod.mk t) (contMDiff_const.prodMk contMDiff_id) σ).1 =
      (SmoothForm.mpullback (Prod.mk s) (contMDiff_const.prodMk contMDiff_id) σ).1 := by
  -- Moser's equation determines `X_t` as the inverse flat map of `-α_t`.
  have hXeq (t : ℝ) : X t = (hσ t).isNondegenerate.interiorEquiv.symm
      (-SmoothForm.mpullback (Prod.mk t) (contMDiff_const.prodMk contMDiff_id) α) := by
    refine (hσ t).isNondegenerate.interior_injective ?_
    beta_reduce
    rw [hX t, IsNondegenerate.interior_interiorEquiv_symm, Submodule.coe_neg]
  have hXs : ContMDiff (𝓘(ℝ, ℝ).prod I) I.tangent ∞
      (fun p : ℝ × M ↦ (⟨p.2, X p.1 p.2⟩ : TangentBundle I M)) := by
    simpa only [hXeq, map_neg] using
      contMDiff_interiorEquiv_symm_mpullback_prodMk σ (fun t ↦ (hσ t).isNondegenerate) (-α)
  -- The rate `ι_t^* L_{∂_t} σ + L_{X_t} σ_t = dα_t - dα_t` vanishes.
  have hL (t : ℝ) : TauCeti.mpullback I (𝓘(ℝ, ℝ).prod I) (Prod.mk t)
        (mlieDerivForm (fun _ ↦ ((1 : ℝ), (0 : E))) σ.1) +
      mlieDerivForm (X t) (TauCeti.mpullback I (𝓘(ℝ, ℝ).prod I) (Prod.mk t) σ.1) = 0 := by
    have h := (hσ t).mlieDerivForm_interiorEquiv_symm
      (-SmoothForm.mpullback (Prod.mk t) (contMDiff_const.prodMk contMDiff_id) α)
    rw [← hXeq, Submodule.coe_neg, mextDeriv_neg, SmoothForm.coe_mpullback _ _ σ] at h
    rw [hα t, h, add_neg_cancel]
  simp only [SmoothForm.coe_mpullback]
  exact mpullback_timeDependentFlowOf_mpullback_prodMk_eq (hXs.of_le (by simp)) hc
    (σ.contMDiff.of_le (by simp)) hL s t

/-- **Moser's stability theorem**, with support control. Let `σ` be a smooth two-form on `ℝ × M`
whose slices `σ_t = ι_t^* σ` are symplectic, and let `α` be a smooth one-form on `ℝ × M` whose
slices are primitives of the velocity, `ι_t^* L_{∂_t} σ = dα_t`, and all vanish outside a fixed
compact set `K`. Then there is an isotopy `ψ_t` of `M`, jointly smooth in `(t, x)`, with
`ψ_0 = id` and `ψ_t^* σ_t = σ_0` for every `t`, which fixes every point at which `α_t` vanishes
for all `t`. In particular it fixes every point outside `K`. -/
theorem exists_isotopy_mpullback_eq_of_isCompact (σ : SmoothForm (𝓘(ℝ, ℝ).prod I) (ℝ × M) ℝ 2)
    (α : SmoothForm (𝓘(ℝ, ℝ).prod I) (ℝ × M) ℝ 1)
    (hσ : ∀ t, IsSymplectic
      (SmoothForm.mpullback (Prod.mk t) (contMDiff_const.prodMk contMDiff_id) σ))
    (hα : ∀ t, TauCeti.mpullback I (𝓘(ℝ, ℝ).prod I) (Prod.mk t)
        (mlieDerivForm (fun _ ↦ ((1 : ℝ), (0 : E))) σ.1) =
      mextDeriv (SmoothForm.mpullback (Prod.mk t) (contMDiff_const.prodMk contMDiff_id) α).1)
    {K : Set M} (hK : IsCompact K) (hαK : ∀ t, ∀ x ∉ K,
      (SmoothForm.mpullback (Prod.mk t) (contMDiff_const.prodMk contMDiff_id) α).1 x = 0) :
    ∃ ψ : ℝ → M ≃ₘ⟮I, I⟯ M, ContMDiff (𝓘(ℝ, ℝ).prod I) I ∞ (fun p : ℝ × M ↦ ψ p.1 p.2) ∧
      (∀ x, ψ 0 x = x) ∧
      (∀ t x, (∀ u,
        (SmoothForm.mpullback (Prod.mk u) (contMDiff_const.prodMk contMDiff_id) α).1 x = 0) →
        ψ t x = x) ∧
      ∀ t, SmoothForm.mpullback (ψ t) (ψ t).contMDiff
          (SmoothForm.mpullback (Prod.mk t) (contMDiff_const.prodMk contMDiff_id) σ) =
        SmoothForm.mpullback (Prod.mk 0) (contMDiff_const.prodMk contMDiff_id) σ := by
  -- The Moser vector field `X_t = (σ_t♭)⁻¹ (-α_t)`.
  obtain ⟨X, hXdef⟩ : ∃ X : ℝ → (x : M) → TangentSpace I x, ∀ t, X t =
      (hσ t).isNondegenerate.interiorEquiv.symm
        (-SmoothForm.mpullback (Prod.mk t) (contMDiff_const.prodMk contMDiff_id) α) :=
    ⟨_, fun _ ↦ rfl⟩
  have hX : ContMDiff (𝓘(ℝ, ℝ).prod I) I.tangent ∞
      (fun p : ℝ × M ↦ (⟨p.2, X p.1 p.2⟩ : TangentBundle I M)) := by
    simpa only [hXdef, map_neg] using
      contMDiff_interiorEquiv_symm_mpullback_prodMk σ (fun t ↦ (hσ t).isNondegenerate) (-α)
  have hX₁ := hX.of_le (m := 1) (by simp)
  -- `X_t` vanishes exactly where `α_t` does, so outside `K`.
  have hX0 (t : ℝ) (x : M) : X t x = 0 ↔
      (SmoothForm.mpullback (Prod.mk t) (contMDiff_const.prodMk contMDiff_id) α).1 x = 0 := by
    rw [hXdef t, IsNondegenerate.interiorEquiv_symm_apply_eq_zero_iff, Submodule.coe_neg,
      Pi.neg_apply, neg_eq_zero]
  have hc : IsCompleteVectorField (timeDependentSuspensionField X) :=
    isCompleteVectorField_timeDependentSuspensionField hX₁ hK fun u y hy ↦ (hX0 u y).2 (hαK u y hy)
  refine ⟨fun t ↦ timeDependentFlowDiffeomorph hc (n := ⊤) le_top hX 0 t, ?_, fun x ↦ ?_,
    fun t x hx ↦ ?_, fun t ↦ Subtype.ext ?_⟩
  · simp only [timeDependentFlowDiffeomorph_apply]
    exact (contMDiff_timeDependentFlowOf hc (n := ⊤) le_top hX).comp
      ((contMDiff_const.prodMk contMDiff_fst).prodMk contMDiff_snd)
  · rw [timeDependentFlowDiffeomorph_apply]
    exact timeDependentFlowOf_self X 0 x
  · rw [timeDependentFlowDiffeomorph_apply]
    exact timeDependentFlowOf_eq_self_of_forall_eq_zero hX₁ (fun u ↦ (hX0 u x).2 (hx u)) 0 t
  · have hψ : ⇑(timeDependentFlowDiffeomorph hc (n := ⊤) le_top hX 0 t) =
        timeDependentFlowOf X 0 t :=
      funext (timeDependentFlowDiffeomorph_apply hc le_top hX 0 t)
    rw [SmoothForm.coe_mpullback _ _
      (SmoothForm.mpullback (Prod.mk t) (contMDiff_const.prodMk contMDiff_id) σ), hψ]
    refine mpullback_timeDependentFlowOf_eq σ α hσ hα (fun u ↦ ?_) hc 0 t
    rw [hXdef u, IsNondegenerate.interior_interiorEquiv_symm, Submodule.coe_neg]

/-- **Moser's stability theorem.** Let `σ` be a smooth two-form on `ℝ × M`, for a compact
boundaryless manifold `M`, whose slices `σ_t = ι_t^* σ` are symplectic, and let `α` be a smooth
one-form on `ℝ × M` whose slices are primitives of the velocity, `ι_t^* L_{∂_t} σ = dα_t`. Then
there is an isotopy `ψ_t` of `M`, jointly smooth in `(t, x)`, with `ψ_0 = id` and
`ψ_t^* σ_t = σ_0` for every `t`, which fixes every point at which `α_t` vanishes for all `t`. -/
theorem exists_isotopy_mpullback_eq [CompactSpace M]
    (σ : SmoothForm (𝓘(ℝ, ℝ).prod I) (ℝ × M) ℝ 2) (α : SmoothForm (𝓘(ℝ, ℝ).prod I) (ℝ × M) ℝ 1)
    (hσ : ∀ t, IsSymplectic
      (SmoothForm.mpullback (Prod.mk t) (contMDiff_const.prodMk contMDiff_id) σ))
    (hα : ∀ t, TauCeti.mpullback I (𝓘(ℝ, ℝ).prod I) (Prod.mk t)
        (mlieDerivForm (fun _ ↦ ((1 : ℝ), (0 : E))) σ.1) =
      mextDeriv (SmoothForm.mpullback (Prod.mk t) (contMDiff_const.prodMk contMDiff_id) α).1) :
    ∃ ψ : ℝ → M ≃ₘ⟮I, I⟯ M, ContMDiff (𝓘(ℝ, ℝ).prod I) I ∞ (fun p : ℝ × M ↦ ψ p.1 p.2) ∧
      (∀ x, ψ 0 x = x) ∧
      (∀ t x, (∀ u,
        (SmoothForm.mpullback (Prod.mk u) (contMDiff_const.prodMk contMDiff_id) α).1 x = 0) →
        ψ t x = x) ∧
      ∀ t, SmoothForm.mpullback (ψ t) (ψ t).contMDiff
          (SmoothForm.mpullback (Prod.mk t) (contMDiff_const.prodMk contMDiff_id) σ) =
        SmoothForm.mpullback (Prod.mk 0) (contMDiff_const.prodMk contMDiff_id) σ :=
  exists_isotopy_mpullback_eq_of_isCompact σ α hσ hα isCompact_univ fun _ _ hx ↦
    (hx (mem_univ _)).elim

end SmoothTwoForm

end TauCeti
