/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Manifold.Moser
public import TauCeti.Geometry.Symplectic.Manifold.Opens
public import TauCeti.Geometry.Manifold.TubularNeighborhood.RelativePoincare
import TauCeti.Geometry.Manifold.DifferentialForm.Flow.Family.Closed

/-!
# Moser's lemma relative to a submanifold

Let `σ` be a smooth two-form on `ℝ × M` whose slices `σ_t = ι_t^* σ` are symplectic, and let
`f : Q → M` be a smooth embedding along which the family does not move: the velocity
`∂_t σ_t = ι_t^* L_{∂_t} σ` pulls back to zero along `f`, that is, `f^* σ_t` does not depend on
`t`. This file proves Moser's lemma for this family relative to the image of `f`
(`TauCeti.SmoothTwoForm.exists_opens_mpullback_timeDependentFlowOf_apply_eq`). Every open
neighbourhood `O` of `f(Q)` contains an open neighbourhood `W` of `f(Q)` carrying a smooth
time-dependent vector field `X` with these properties:

* `X_t` vanishes at every point of `f(Q)`, at every time, so the time-dependent flow `φ_{s,t}` of
  `X` is defined at every point of `f(Q)` for all times and fixes it;
* wherever the flow `φ_{s,t}` is defined, it pulls the restriction of `σ_t` to `W` back to the
  restriction of `σ_s`: `(φ_{s,t}^* σ_t)ₓ = (σ_s)ₓ`.

No compactness of `Q` or of `M`, and no completeness of the flow, is assumed: the conclusion holds
along the domain of the flow, which is open and contains every `((s, t), f q)`. The parent module
`TauCeti.Geometry.Symplectic.Manifold.RelativeMoser` treats instead the affine path between two
forms near a compact submanifold.

The proof feeds relative primitives of the velocity into Moser's field. The slices of the
velocity are closed, since the slices of `σ` are
(`TauCeti.SmoothForm.isClosed_mpullback_prodMk_timeDeriv`), and they pull back to zero along `f`.
By the relative Poincaré lemma for families near an embedded submanifold
(`TauCeti.SmoothEmbedding.exists_isSmoothForm_family_relative_primitive`), on a tubular
neighbourhood `W ⊆ O` of `f(Q)` they are the exterior derivatives `dβ_t` of the slices of a
smooth one-form `β` on `ℝ × W` which vanishes at every point `(t, f q)`. Moser's lemma along the
domain of the flow
(`TauCeti.SmoothTwoForm.exists_contMDiff_mpullback_timeDependentFlowOf_apply_eq`), applied to
the restriction of `σ` to `ℝ × W` and the primitives `β_t`, gives the Moser field
`X_t = (σ_t♭)⁻¹ (-β_t)` on `W`: it is smooth in `(t, x)`, its flow pulls `σ_t` back to `σ_s`
wherever it is defined, and it vanishes where `β_t` does, on `f(Q)`.

## Main results

* `TauCeti.SmoothTwoForm.exists_opens_mpullback_timeDependentFlowOf_apply_eq`: Moser's lemma for a
  family of symplectic forms which does not move along an embedded submanifold, with a Moser
  flow fixing the submanifold.

## References

* A. Cannas da Silva, *Lectures on Symplectic Geometry*, Lecture Notes in Mathematics 1764,
  Springer, 2001, Proposition 6.8 and Theorem 7.4 (the relative Poincaré lemma and the relative
  Moser theorem).
* D. McDuff, D. Salamon, *Introduction to Symplectic Topology*, 3rd ed., Oxford, 2017,
  Section 3.2 (Moser isotopy).
-/

public section

noncomputable section

open Bundle Set Function TopologicalSpace
open scoped ContDiff Manifold

namespace TauCeti

namespace SmoothTwoForm

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  [SecondCountableTopology M]
  {EQ HQ Q : Type*} [NormedAddCommGroup EQ] [NormedSpace ℝ EQ] [FiniteDimensional ℝ EQ]
  [TopologicalSpace HQ] {IQ : ModelWithCorners ℝ EQ HQ} [IQ.Boundaryless]
  [TopologicalSpace Q] [ChartedSpace HQ Q] [IsManifold IQ ∞ Q]

/-- **Moser's lemma relative to a submanifold.** Let `σ` be a smooth two-form on `ℝ × M` whose
slices `σ_t` are symplectic, and let `f : Q → M` be a smooth embedding along which the velocity of
the slices pulls back to zero, `f^* (ι_t^* L_{∂_t} σ) = 0` for every `t`. Then every open
neighbourhood `O` of `f(Q)` contains an open neighbourhood `W` of `f(Q)` with a smooth
time-dependent vector field `X` on `W` that vanishes on `f(Q)` at all times, whose time-dependent
flow `φ_{s,t}` is defined on `f(Q)` and fixes it, and which pulls the restriction of `σ_t` to `W`
back to that of `σ_s` at every point `x` of `W` where `φ_{s,t} x` is defined. -/
theorem exists_opens_mpullback_timeDependentFlowOf_apply_eq (f : SmoothEmbedding IQ I ∞ Q M)
    (σ : SmoothForm (𝓘(ℝ, ℝ).prod I) (ℝ × M) ℝ 2)
    (hσ : ∀ t, IsSymplectic
      (SmoothForm.mpullback (Prod.mk t) (contMDiff_const.prodMk contMDiff_id) σ))
    (hf : ∀ t, TauCeti.mpullback IQ I f
      (SmoothForm.mpullback (Prod.mk t) (contMDiff_const.prodMk contMDiff_id) σ.timeDeriv).val =
        0)
    {O : Set M} (hO : IsOpen O) (hfO : range f ⊆ O) :
    ∃ W : Opens M, (W : Set M) ⊆ O ∧ ∃ hfW : range f ⊆ W,
      ∃ X : ℝ → (x : W) → TangentSpace I x,
        ContMDiff (𝓘(ℝ, ℝ).prod I) I.tangent ∞
          (fun p : ℝ × W ↦ (⟨p.2, X p.1 p.2⟩ : TangentBundle I W)) ∧
        (∀ t q, X t ⟨f q, hfW (mem_range_self q)⟩ = 0) ∧
        (∀ s t q, ((s, t), ⟨f q, hfW (mem_range_self q)⟩) ∈ timeDependentFlowDomain X ∧
          timeDependentFlowOf X s t ⟨f q, hfW (mem_range_self q)⟩ =
            ⟨f q, hfW (mem_range_self q)⟩) ∧
        ∀ s t (x : W), ((s, t), x) ∈ timeDependentFlowDomain X →
          TauCeti.mpullback I I (timeDependentFlowOf X s t)
              (SmoothForm.mpullback (Subtype.val : W → M) contMDiff_subtypeVal
                (SmoothForm.mpullback (Prod.mk t) (contMDiff_const.prodMk contMDiff_id) σ)).val x =
            (SmoothForm.mpullback (Subtype.val : W → M) contMDiff_subtypeVal
              (SmoothForm.mpullback (Prod.mk s) (contMDiff_const.prodMk contMDiff_id) σ)).val x
    := by
  have hι (t : ℝ) : ContMDiff I (𝓘(ℝ, ℝ).prod I) ∞ (Prod.mk t : M → ℝ × M) :=
    contMDiff_const.prodMk contMDiff_id
  -- Relative primitives of the velocity, on a tubular neighbourhood `W` of `f(Q)`.
  obtain ⟨W, hWO, hfW, hprim⟩ :=
    f.exists_isSmoothForm_family_relative_primitive (IP := 𝓘(ℝ, ℝ)) (P := ℝ) (F := ℝ) hO hfO
  obtain ⟨β, hβ, hdβ, hβ₀⟩ := hprim (k := 1) le_top σ.timeDeriv.isSmoothForm
    (fun t ↦ by
      simpa only [SmoothForm.coe_mpullback] using (SmoothForm.isClosed_def _).mp
        (SmoothForm.isClosed_mpullback_prodMk_timeDeriv σ (fun u ↦ (hσ u).isClosed) t))
    (fun t ↦ by simpa only [SmoothForm.coe_mpullback] using hf t)
  let β' : SmoothForm (𝓘(ℝ, ℝ).prod I) (ℝ × W) ℝ 1 := ⟨β, hβ.mem_smoothBundleForms⟩
  -- The restriction `σ_W` of the family to `ℝ × W`, whose slices are the restrictions of the
  -- slices of `σ`.
  set σW := SmoothForm.mpullback (Prod.map id (Subtype.val : W → M))
    (contMDiff_id.prodMap contMDiff_subtypeVal) σ with hσW_def
  have hslice (t : ℝ) : SmoothForm.mpullback (Prod.mk t) (contMDiff_const.prodMk contMDiff_id) σW =
      SmoothForm.mpullback (Subtype.val : W → M) contMDiff_subtypeVal
        (SmoothForm.mpullback (Prod.mk t) (hι t) σ) :=
    SmoothForm.mpullback_prodMk_mpullback_prodMap (Subtype.val : W → M) contMDiff_subtypeVal σ t
  have hσW (t : ℝ) : IsSymplectic
      (SmoothForm.mpullback (Prod.mk t) (contMDiff_const.prodMk contMDiff_id) σW) := by
    rw [hslice]
    exact (hσ t).mpullback_subtype_val W
  -- The slices of `β` are primitives of the velocity of `σ_W`.
  have hvel (t : ℝ) : TauCeti.mpullback I (𝓘(ℝ, ℝ).prod I) (Prod.mk t)
      (mlieDerivForm (fun _ ↦ ((1 : ℝ), (0 : E))) σW.val) =
      mextDeriv (SmoothForm.mpullback (Prod.mk t) (contMDiff_const.prodMk contMDiff_id) β').val
      := by
    have h := congrArg Subtype.val
      (SmoothForm.mpullback_prodMk_timeDeriv_mpullback_prodMap (Subtype.val : W → M)
        contMDiff_subtypeVal σ t)
    rw [← hσW_def] at h
    simp only [SmoothForm.coe_mpullback, SmoothForm.coe_timeDeriv] at h
    rw [h, SmoothForm.coe_mpullback, hdβ t, SmoothForm.coe_timeDeriv]
  -- The Moser field `X_t = (σ_t♭)⁻¹ (-β_t)` on `W` vanishes on `f(Q)`, where `β` does.
  obtain ⟨X, hX, -, hX0, hXσ⟩ :=
    exists_contMDiff_mpullback_timeDependentFlowOf_apply_eq σW β' hσW hvel
  have hX₀ (t : ℝ) (q : Q) : X t ⟨f q, hfW (mem_range_self q)⟩ = 0 := by
    rw [hX0, SmoothForm.coe_mpullback]
    exact mpullback_apply_eq_zero (hβ₀ t q)
  refine ⟨W, hWO, hfW, X, hX, hX₀, fun s t q ↦ ⟨mem_timeDependentFlowDomain_of_forall_eq_zero
    (fun u ↦ hX₀ u q) s t, timeDependentFlowOf_eq_self_of_forall_eq_zero (hX.of_le (by simp))
    (fun u ↦ hX₀ u q) s t⟩, fun s t x hx ↦ ?_⟩
  rw [← hslice t, ← hslice s]
  exact hXσ s t x hx

end SmoothTwoForm

end TauCeti
