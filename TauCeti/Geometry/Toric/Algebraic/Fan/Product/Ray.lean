/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Toric.Algebraic.Fan.Product.Basic
public import TauCeti.Geometry.Toric.Algebraic.Fan.Ray

/-!
# Rays of a product fan

A ray of the product of two fans is the product of a ray of one factor with the zero cone of the
other. Both factors must be nonempty for this to be a bijection: if one of them is empty, so is
their product, while the other may still have rays.

This is the fan-level form of `TauCeti.Toric.ToricRay.prodSplit`, and indexes the boundary
components of a product of toric varieties by the boundary components of the two factors.

## Main declarations

* `TauCeti.Toric.Fan.prodRayEquiv`: the rays of a product of nonempty fans are the rays of the
  two factors.
* `TauCeti.Toric.Fan.coe_toCone_prodRayEquiv_symm_inl` and
  `TauCeti.Toric.Fan.coe_toCone_prodRayEquiv_symm_inr`: the cones of the corresponding product
  rays.

## References

* W. Fulton, *Introduction to Toric Varieties*, §§1.4 and 3.1.
* D. Cox, J. Little and H. Schenck, *Toric Varieties*, §§3.1 and 4.1.
-/

public section

namespace TauCeti.Toric.Fan

variable {N N' V V' : Type*} [AddCommGroup N] [AddCommGroup N'] [AddCommGroup V]
  [AddCommGroup V'] [Module ℝ V] [Module ℝ V'] {i : N →+ V} {i' : N' →+ V'}
  (Φ : Fan i) (Ψ : Fan i')

/-- The product rays of the rays of the two factors: a ray of one factor times the zero cone of
the other. -/
private def prodRayOfSum (hΦ0 : Nonempty Φ.cones) (hΨ0 : Nonempty Ψ.cones) :
    Φ.Ray ⊕ Ψ.Ray → (Φ.prod Ψ).Ray
  | .inl ρ => ⟨Φ.prodCone Ψ ρ.toCone ⟨⊥, Ψ.bot_mem hΨ0.some.2⟩,
      (PointedCone.finrank_span_coe_prod_bot ρ.toCone.1).trans ρ.2⟩
  | .inr ρ => ⟨Φ.prodCone Ψ ⟨⊥, Φ.bot_mem hΦ0.some.2⟩ ρ.toCone,
      (PointedCone.finrank_span_coe_bot_prod ρ.toCone.1).trans ρ.2⟩

private theorem coe_toCone_prodRayOfSum_inl (hΦ0 : Nonempty Φ.cones) (hΨ0 : Nonempty Ψ.cones)
    (ρ : Φ.Ray) :
    (prodRayOfSum Φ Ψ hΦ0 hΨ0 (.inl ρ)).toCone.1 = ρ.toCone.1.prod ⊥ :=
  rfl

private theorem coe_toCone_prodRayOfSum_inr (hΦ0 : Nonempty Φ.cones) (hΨ0 : Nonempty Ψ.cones)
    (ρ : Ψ.Ray) :
    (prodRayOfSum Φ Ψ hΦ0 hΨ0 (.inr ρ)).toCone.1 = (⊥ : PointedCone ℝ V).prod ρ.toCone.1 :=
  rfl

private theorem prodRayOfSum_injective (hΦ0 : Nonempty Φ.cones) (hΨ0 : Nonempty Ψ.cones) :
    Function.Injective (prodRayOfSum Φ Ψ hΦ0 hΨ0) := by
  have hcone {a b : Φ.Ray ⊕ Ψ.Ray} (h : prodRayOfSum Φ Ψ hΦ0 hΨ0 a =
      prodRayOfSum Φ Ψ hΦ0 hΨ0 b) :
      (prodRayOfSum Φ Ψ hΦ0 hΨ0 a).toCone.1 = (prodRayOfSum Φ Ψ hΦ0 hΨ0 b).toCone.1 := by
    rw [h]
  -- Compare the product cones on the two coordinate axes.
  rintro (ρ | ρ) (ρ' | ρ') h <;> have h' := SetLike.ext_iff.1 (hcone h)
  · refine congrArg Sum.inl (Subtype.ext (Subtype.ext (SetLike.ext fun x ↦ ?_)))
    simpa [coe_toCone_prodRayOfSum_inl] using h' (x, 0)
  · refine (Ray.toCone_ne_bot Φ ρ (SetLike.ext fun x ↦ ?_)).elim
    simpa [coe_toCone_prodRayOfSum_inl, coe_toCone_prodRayOfSum_inr] using h' (x, 0)
  · refine (Ray.toCone_ne_bot Φ ρ' (SetLike.ext fun x ↦ ?_)).elim
    simpa [coe_toCone_prodRayOfSum_inl, coe_toCone_prodRayOfSum_inr] using (h' (x, 0)).symm
  · refine congrArg Sum.inr (Subtype.ext (Subtype.ext (SetLike.ext fun x ↦ ?_)))
    simpa [coe_toCone_prodRayOfSum_inr] using h' (0, x)

private theorem prodRayOfSum_surjective (hΦ0 : Nonempty Φ.cones) (hΨ0 : Nonempty Ψ.cones) :
    Function.Surjective (prodRayOfSum Φ Ψ hΦ0 hΨ0) := by
  intro ξ
  obtain ⟨σ, τ, hξ⟩ := Φ.exists_prodCone_eq Ψ ξ.toCone
  have hξ' : (ξ.1.1 : PointedCone ℝ (V × V')) = σ.1.prod τ.1 := congrArg Subtype.val hξ.symm
  -- View `ξ` as a ray of the cone `σ × τ`, whose projections are `σ` and `τ`.
  let G : ToricRay (σ.1.prod τ.1) :=
    ⟨⟨ξ.1.1, hξ' ▸ PointedCone.IsFaceOf.refl _⟩, ξ.2⟩
  have hG : (G.toPointedCone : ConvexCone ℝ (V × V')).Salient :=
    ((Φ.prod Ψ).isToricCone ξ.toCone.2).salient
  -- By construction, the cone of `G` is `ξ.1.1`.
  have hGfst : PointedCone.map (LinearMap.fst ℝ V V') G.toPointedCone = σ.1 := by
    change PointedCone.map _ ξ.1.1 = _
    rw [hξ']
    exact Submodule.prod_map_fst ..
  have hGsnd : PointedCone.map (LinearMap.snd ℝ V V') G.toPointedCone = τ.1 := by
    change PointedCone.map _ ξ.1.1 = _
    rw [hξ']
    exact Submodule.prod_map_snd ..
  by_cases hτ : τ.1 = ⊥
  · have hσ := ToricRay.finrank_span_map_fst_eq_one G hG (hGsnd.trans hτ)
    rw [hGfst] at hσ
    refine ⟨.inl ⟨σ, hσ⟩, Subtype.ext (Subtype.ext ?_)⟩
    rw [coe_toCone_prodRayOfSum_inl, hξ', hτ]
  · have hσ : σ.1 = ⊥ := hGfst.symm.trans
      (ToricRay.map_fst_eq_bot_of_map_snd_ne_bot G hG (hGsnd.trans_ne hτ))
    have hτ' := ToricRay.finrank_span_map_snd_eq_one G hG (hGsnd.trans_ne hτ)
    rw [hGsnd] at hτ'
    refine ⟨.inr ⟨τ, hτ'⟩, Subtype.ext (Subtype.ext ?_)⟩
    rw [coe_toCone_prodRayOfSum_inr, hξ', hσ]

/-- The rays of a product of nonempty fans are exactly the rays of the two factors. A ray of the
product projects to a ray of one factor and to the zero cone of the other; conversely, a ray of
a factor gives the product ray with the zero cone of the other factor. Both factors must be
nonempty, since the product of an empty fan with any fan is empty. -/
noncomputable def prodRayEquiv (hΦ0 : Nonempty Φ.cones) (hΨ0 : Nonempty Ψ.cones) :
    (Φ.prod Ψ).Ray ≃ Φ.Ray ⊕ Ψ.Ray :=
  (Equiv.ofBijective (prodRayOfSum Φ Ψ hΦ0 hΨ0)
    ⟨prodRayOfSum_injective Φ Ψ hΦ0 hΨ0, prodRayOfSum_surjective Φ Ψ hΦ0 hΨ0⟩).symm

/-- The product ray of a ray of the first factor is its product with the zero cone. -/
@[simp]
theorem coe_toCone_prodRayEquiv_symm_inl (hΦ0 : Nonempty Φ.cones) (hΨ0 : Nonempty Ψ.cones)
    (ρ : Φ.Ray) :
    ((Φ.prodRayEquiv Ψ hΦ0 hΨ0).symm (.inl ρ)).toCone.1 = ρ.toCone.1.prod ⊥ := by
  rw [prodRayEquiv, Equiv.symm_symm]
  exact coe_toCone_prodRayOfSum_inl Φ Ψ hΦ0 hΨ0 ρ

/-- The product ray of a ray of the second factor is the product of the zero cone with it. -/
@[simp]
theorem coe_toCone_prodRayEquiv_symm_inr (hΦ0 : Nonempty Φ.cones) (hΨ0 : Nonempty Ψ.cones)
    (ρ : Ψ.Ray) :
    ((Φ.prodRayEquiv Ψ hΦ0 hΨ0).symm (.inr ρ)).toCone.1 =
      (⊥ : PointedCone ℝ V).prod ρ.toCone.1 := by
  rw [prodRayEquiv, Equiv.symm_symm]
  exact coe_toCone_prodRayOfSum_inr Φ Ψ hΦ0 hΨ0 ρ

end TauCeti.Toric.Fan
