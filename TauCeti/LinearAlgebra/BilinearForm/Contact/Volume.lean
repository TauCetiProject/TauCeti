/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Volume
public import TauCeti.LinearAlgebra.BilinearForm.Contact
import TauCeti.LinearAlgebra.Basis.Fin
import TauCeti.Topology.Algebra.Module.Alternating.TopDegree

/-!
# The volume criterion for contact covectors

Let `V` be a real vector space of dimension `2 * n + 1`, let `a` be a covector on `V` and let `ω`
be an alternating two-form on `V`. Then `a` is a contact covector for `ω`, that is `a ≠ 0` and `ω`
is nondegenerate on `ker a`, exactly when the top-degree form `a ∧ ωⁿ` is nonzero
(`ContinuousLinearMap.isContact_iff_pairedWedge_wedgePow_ne_zero`).

For `a ≠ 0` choose `r` with `a r = 1` and a basis `w` of the hyperplane `ker a`. Since `a` kills
every vector of `w`, expanding the wedge along `r`
(`ContinuousAlternatingMap.pairedWedge_apply_vecCons_of_forall`) gives
`(a ∧ ωⁿ)(r, w) = a r · ωⁿ(w)`, the value
on `w` of the `n`-th wedge power of the restriction of `ω` to `ker a`. By the volume criterion for
two-forms (`ContinuousAlternatingMap.wedgePow_ne_zero_iff_nondegenerate`), it is nonzero exactly
when that restriction is nondegenerate.

This is the pointwise form of the classical description of contact forms on a
`(2n + 1)`-dimensional manifold by the nonvanishing of `α ∧ (dα)ⁿ`.

## Main results

* `ContinuousLinearMap.isContact_iff_pairedWedge_wedgePow_ne_zero`: in dimension `2 * n + 1`, a
  covector `a` is contact for `ω` exactly when `a ∧ ωⁿ ≠ 0`.

## References

* H. Geiges, *An Introduction to Contact Topology*, Cambridge University Press, 2008,
  Section 1.1 (the contact condition `α ∧ (dα)ⁿ ≠ 0`).
-/

public section

open Module ContinuousAlternatingMap TauCeti

namespace ContinuousLinearMap

variable {V : Type*} [AddCommGroup V] [Module ℝ V] [TopologicalSpace V] [FiniteDimensional ℝ V]

/-- **The volume criterion for contact covectors.** On a real vector space of dimension
`2 * n + 1`, a covector `a` is contact for an alternating two-form `ω`, that is `a ≠ 0` and `ω` is
nondegenerate on `ker a`, exactly when the top-degree form `a ∧ ωⁿ` is nonzero. -/
theorem isContact_iff_pairedWedge_wedgePow_ne_zero (a : V →L[ℝ] ℝ) (ω : V [⋀^Fin 2]→L[ℝ] ℝ)
    {n : ℕ} (hn : finrank ℝ V = 2 * n + 1) :
    Module.Dual.IsContact (a : V →ₗ[ℝ] ℝ) ω.toMultilinearMap.toBilinMap ↔
      pairedWedge (ContinuousLinearMap.mul ℝ ℝ) (ContinuousLinearMap.mul ℝ ℝ).continuous₂
        (ofSubsingleton ℝ V ℝ (0 : Fin 1) a) (wedgePow ω n) ≠ 0 := by
  by_cases ha : a = 0
  · subst ha
    have h0 : ofSubsingleton ℝ V ℝ (0 : Fin 1) 0 = 0 := by
      ext v
      rfl
    simp only [Module.Dual.isContact_def, ContinuousLinearMap.toLinearMap_zero, ne_eq,
      not_true_eq_false, false_and, h0, pairedWedge_zero_left]
  -- Split `V` as `ℝ r ⊕ ker a` with `a r = 1`, and evaluate `a ∧ ωⁿ` on an adapted basis.
  obtain ⟨v, hv⟩ : ∃ v, a v ≠ 0 := by
    by_contra! h
    exact ha (ContinuousLinearMap.ext h)
  set r := (a v)⁻¹ • v
  have hr : a r = 1 := by rw [map_smul, smul_eq_mul, inv_mul_cancel₀ hv]
  set W := LinearMap.ker (a : V →ₗ[ℝ] ℝ)
  have hrW : r ∉ W := by simp [W, hr]
  have hW : finrank ℝ W = 2 * n := by
    have hrange : LinearMap.range (a : V →ₗ[ℝ] ℝ) = ⊤ :=
      LinearMap.range_eq_top.mpr fun t ↦ ⟨t • r, by simp [hr]⟩
    have := LinearMap.finrank_range_add_finrank_ker (a : V →ₗ[ℝ] ℝ)
    rw [hrange, finrank_top, finrank_self] at this
    have h : 1 + finrank ℝ W = finrank ℝ V := this
    omega
  let b := finBasisOfFinrankEq ℝ W hW
  let c := (Basis.mkFinConsOfNotMem r b hrW hn).reindex (finCongr (Nat.add_comm (2 * n) 1))
  have hc : ⇑c = Matrix.vecCons r (W.subtype ∘ b) ∘ Fin.cast (Nat.add_comm 1 (2 * n)) := by
    funext i
    simp [c, Basis.reindex_apply, Matrix.vecCons]
  let ωW := ω.compContinuousLinearMap W.subtypeL
  have hωW : ωW.toMultilinearMap.toBilinMap =
      LinearMap.BilinForm.restrict ω.toMultilinearMap.toBilinMap W := by
    ext x y
    simp only [ωW, MultilinearMap.toBilinMap_apply, LinearMap.BilinForm.restrict_apply,
      LinearMap.domRestrict_apply]
    exact (compContinuousLinearMap_apply ω W.subtypeL ![x, y]).trans
      (congrArg ω (by ext i; fin_cases i <;> rfl))
  have hval : pairedWedge (ContinuousLinearMap.mul ℝ ℝ)
      (ContinuousLinearMap.mul ℝ ℝ).continuous₂ (ofSubsingleton ℝ V ℝ (0 : Fin 1) a)
      (wedgePow ω n) c = wedgePow ωW n b := by
    rw [hc, pairedWedge_apply_vecCons_of_forall _ _ (ofSubsingleton ℝ V ℝ (0 : Fin 1) a) _ r
        (W.subtype ∘ b) fun i ↦ (b i).2, ContinuousLinearMap.mul_apply',
      ofSubsingleton_apply_apply, Matrix.cons_val_zero, hr, one_mul,
      ← wedgePow_compContinuousLinearMap]
    -- `W.subtype` and `W.subtypeL` have the same underlying function.
    exact (compContinuousLinearMap_apply (wedgePow ω n) W.subtypeL b).symm
  rw [Module.Dual.isContact_def, ← map_basis_ne_zero_iff _ c, hval, map_basis_ne_zero_iff,
    wedgePow_ne_zero_iff_nondegenerate ωW hW, hωW]
  exact and_iff_right fun h ↦ ha (ContinuousLinearMap.coe_injective h)

end ContinuousLinearMap
