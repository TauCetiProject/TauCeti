/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Toric.Analytic.Cone.Product
public import TauCeti.Geometry.Toric.Analytic.Fan.Product.Basic
public import TauCeti.Geometry.Toric.Analytic.Fan.Map.Holomorphic

/-!
# The biholomorphism of analytic toric products

The canonical product homeomorphism of regular fan realizations is holomorphic in both
directions. Its forward map is the pair of toric projection maps. Locally, its inverse is
the inverse affine product comparison, which multiplies monomial values, followed by a
product-cone chart inclusion. Both conclusions hold for the existing complex structures,
without changing any extending basis or generating family, and include empty fans.

## Main declarations

* `TauCeti.Toric.Fan.analyticProdDiffeomorph`: the canonical biholomorphism from the realization
  of a product fan to the product of the factor realizations.
* `TauCeti.Toric.Fan.contMDiff_analyticProdHomeomorph_symm`: holomorphy of the inverse product
  homeomorphism.

## References

* W. Fulton, *Introduction to Toric Varieties*, §1.4.
* D. Cox, J. Little and H. Schenck, *Toric Varieties*, §§3.1 and 3.3.
-/

public section

open Set Topology
open scoped ContDiff Manifold

namespace TauCeti.Toric.Fan

universe u

variable {N N' V V' : Type u} [AddCommGroup N] [AddCommGroup N']
  [AddCommGroup V] [AddCommGroup V'] [Module ℝ V] [Module ℝ V']
  {i : N →+ V} {i' : N' →+ V'} (Φ : Fan i) (Ψ : Fan i')
  (hΦ : Φ.IsRegular) (hΨ : Ψ.IsRegular)

/-- The product homeomorphism is holomorphic for the complex manifold structures of the
product-fan realization and the two factor realizations. -/
theorem contMDiff_analyticProdHomeomorph (n : ℕ∞ω) :
    letI := (Φ.prod Ψ).analyticChartedSpace (IsRegular.prod Φ Ψ hΦ hΨ)
    letI := Φ.analyticChartedSpace hΦ
    letI := Ψ.analyticChartedSpace hΨ
    ContMDiff 𝓘(ℂ, Fin (Module.finrank ℤ (N × N')) → ℂ)
      (𝓘(ℂ, Fin (Module.finrank ℤ N) → ℂ).prod
        𝓘(ℂ, Fin (Module.finrank ℤ N') → ℂ)) n
      (Φ.analyticProdHomeomorph Ψ hΦ hΨ) := by
  let _ := (Φ.prod Ψ).analyticChartedSpace (IsRegular.prod Φ Ψ hΦ hΨ)
  let _ := Φ.analyticChartedSpace hΦ
  let _ := Ψ.analyticChartedSpace hΨ
  refine (((FanHom.fst Φ Ψ).contMDiff_analyticMap (IsRegular.prod Φ Ψ hΦ hΨ) hΦ n).prodMk
    ((FanHom.snd Φ Ψ).contMDiff_analyticMap (IsRegular.prod Φ Ψ hΦ hΨ) hΨ n)).congr ?_
  intro x
  rw [coe_analyticProdHomeomorph, analyticProdComparison_apply]

/-- The inverse product comparison followed by the product-cone inclusion is holomorphic
on the pair of affine charts, for arbitrary extending bases of the factors. -/
private theorem contMDiff_productChart (σ : Φ.cones) (τ : Ψ.cones) {k l k' l' : ℕ}
    {B : Module.Basis (ToricRay σ.1 ⊕ Fin l) ℤ N}
    {C : Module.Basis (ToricRay τ.1 ⊕ Fin l') ℤ N'}
    (hB : ∀ ρ, IsPrimitiveGenerator i ρ (B (Sum.inl ρ)))
    (hC : ∀ ρ, IsPrimitiveGenerator i' ρ (C (Sum.inl ρ)))
    (κ : ToricRay σ.1 ≃ Fin k) (κ' : ToricRay τ.1 ≃ Fin k') (n : ℕ∞ω) :
    letI := affinePointTopology (Φ.analyticChartGenerators σ).2
    letI := coneChartedSpace Φ.lattice ((isRegular_iff.mp hΦ) σ.1 σ.2).toIsToricCone
      hB κ (Φ.analyticChartGenerators σ).2
    letI := affinePointTopology (Ψ.analyticChartGenerators τ).2
    letI := coneChartedSpace Ψ.lattice ((isRegular_iff.mp hΨ) τ.1 τ.2).toIsToricCone
      hC κ' (Ψ.analyticChartGenerators τ).2
    letI := (Φ.prod Ψ).analyticChartedSpace (IsRegular.prod Φ Ψ hΦ hΨ)
    ContMDiff
      (𝓘(ℂ, (Fin k → ℂ) × (Fin l → ℂ)).prod
        𝓘(ℂ, (Fin k' → ℂ) × (Fin l' → ℂ)))
      𝓘(ℂ, Fin (Module.finrank ℤ (N × N')) → ℂ) n
      (fun p : AffineSemigroupComplexPoint (dualSemigroup Φ.lattice σ.1) ×
          AffineSemigroupComplexPoint (dualSemigroup Ψ.lattice τ.1) ↦
        (Φ.prod Ψ).analyticAffineChartι (IsRegular.prod Φ Ψ hΦ hΨ) (Φ.prodCone Ψ σ τ)
          ((AffineSemigroupComplexPoint.prodEquiv
            (dualSemigroupProdEquiv Φ.lattice Ψ.lattice σ.1 τ.1)).symm p)) := by
  let _ := affinePointTopology (Φ.analyticChartGenerators σ).2
  let _ := coneChartedSpace Φ.lattice ((isRegular_iff.mp hΦ) σ.1 σ.2).toIsToricCone
    hB κ (Φ.analyticChartGenerators σ).2
  let _ := affinePointTopology (Ψ.analyticChartGenerators τ).2
  let _ := coneChartedSpace Ψ.lattice ((isRegular_iff.mp hΨ) τ.1 τ.2).toIsToricCone
    hC κ' (Ψ.analyticChartGenerators τ).2
  let _ := (Φ.prod Ψ).analyticChartedSpace (IsRegular.prod Φ Ψ hΦ hΨ)
  have hσ := (isRegular_iff.mp hΦ) σ.1 σ.2
  have hτ := (isRegular_iff.mp hΨ) τ.1 τ.2
  have hστ := (isRegular_iff.mp (IsRegular.prod Φ Ψ hΦ hΨ))
    (Φ.prodCone Ψ σ τ).1 (Φ.prodCone Ψ σ τ).2
  obtain ⟨l'', D, hD⟩ := hστ.exists_basis_sum
  have : Finite (ToricRay (σ.1.prod τ.1)) := ToricRay.finite_of_fg hστ.fg
  let κ'' := Finite.equivFin (ToricRay (σ.1.prod τ.1))
  let g'' := ((Φ.prod Ψ).analyticChartGenerators (Φ.prodCone Ψ σ τ)).2
  let _ := affinePointTopology g''
  let _ := coneChartedSpace (Φ.lattice.prod Ψ.lattice) (hσ.toIsToricCone.prod hτ.toIsToricCone)
    hD κ'' g''
  have hinv := AffineSemigroupComplexPoint.contMDiff_prodEquiv_symm Φ.lattice Ψ.lattice
    hσ.toIsToricCone hτ.toIsToricCone hB hC hD κ κ' κ''
    (Φ.analyticChartGenerators σ).2 (Ψ.analyticChartGenerators τ).2 g'' n
  simpa only [Function.comp_def] using
    ((Φ.prod Ψ).contMDiff_analyticAffineChartι (IsRegular.prod Φ Ψ hΦ hΨ)
      (Φ.prodCone Ψ σ τ) hD κ'' g'' n).comp hinv

/-- The inverse product homeomorphism is holomorphic: on a product of cone opens it is the
inverse affine product comparison conjugated by the two chart inclusions. -/
theorem contMDiff_analyticProdHomeomorph_symm (n : ℕ∞ω) :
    letI := (Φ.prod Ψ).analyticChartedSpace (IsRegular.prod Φ Ψ hΦ hΨ)
    letI := Φ.analyticChartedSpace hΦ
    letI := Ψ.analyticChartedSpace hΨ
    ContMDiff
      (𝓘(ℂ, Fin (Module.finrank ℤ N) → ℂ).prod
        𝓘(ℂ, Fin (Module.finrank ℤ N') → ℂ))
      𝓘(ℂ, Fin (Module.finrank ℤ (N × N')) → ℂ) n
      (Φ.analyticProdHomeomorph Ψ hΦ hΨ).symm := by
  let _ := (Φ.prod Ψ).analyticChartedSpace (IsRegular.prod Φ Ψ hΦ hΨ)
  let _ := Φ.analyticChartedSpace hΦ
  let _ := Ψ.analyticChartedSpace hΨ
  intro p
  -- Choose factor charts and arbitrary extending bases near the two components of `p`.
  obtain ⟨σ, a, ha⟩ := Φ.exists_analyticAffineChartι_apply_eq hΦ p.1
  obtain ⟨τ, b, hb⟩ := Ψ.exists_analyticAffineChartι_apply_eq hΨ p.2
  have hσ := (isRegular_iff.mp hΦ) σ.1 σ.2
  have hτ := (isRegular_iff.mp hΨ) τ.1 τ.2
  obtain ⟨l, B, hB⟩ := hσ.exists_basis_sum
  obtain ⟨l', C, hC⟩ := hτ.exists_basis_sum
  have : Finite (ToricRay σ.1) := ToricRay.finite_of_fg hσ.fg
  have : Finite (ToricRay τ.1) := ToricRay.finite_of_fg hτ.fg
  let κ := Finite.equivFin (ToricRay σ.1)
  let κ' := Finite.equivFin (ToricRay τ.1)
  let g := (Φ.analyticChartGenerators σ).2
  let g' := (Ψ.analyticChartGenerators τ).2
  let _ := affinePointTopology g
  let _ := coneChartedSpace Φ.lattice hσ.toIsToricCone hB κ g
  let _ := affinePointTopology g'
  let _ := coneChartedSpace Ψ.lattice hτ.toIsToricCone hC κ' g'
  let P := Φ.analyticAffineChartPartialDiffeomorph hΦ σ hB κ g n
  let Q := Ψ.analyticAffineChartPartialDiffeomorph hΨ τ hC κ' g' n
  have hP := Φ.analyticAffineChartPartialDiffeomorph_target hΦ σ hB κ g n
  have hQ := Ψ.analyticAffineChartPartialDiffeomorph_target hΨ τ hC κ' g' n
  -- Invert the two chart inclusions on their open images, then combine the affine points.
  have hsymm : ContMDiffOn
      (𝓘(ℂ, Fin (Module.finrank ℤ N) → ℂ).prod
        𝓘(ℂ, Fin (Module.finrank ℤ N') → ℂ))
      (𝓘(ℂ, (Fin _ → ℂ) × (Fin l → ℂ)).prod
        𝓘(ℂ, (Fin _ → ℂ) × (Fin l' → ℂ))) n
      (fun q : Φ.analyticRealization hΦ × Ψ.analyticRealization hΨ ↦
        (P.symm q.1, Q.symm q.2)) (P.target ×ˢ Q.target) :=
    (P.symm.contMDiffOn.comp contMDiffOn_fst fun _ hz ↦ hz.1).prodMk
      (Q.symm.contMDiffOn.comp contMDiffOn_snd fun _ hz ↦ hz.2)
  have hlocal := (Φ.contMDiff_productChart Ψ hΦ hΨ σ τ hB hC κ κ' n).comp_contMDiffOn hsymm
  have hmem : P.target ×ˢ Q.target ∈ 𝓝 p :=
    (P.open_target.prod Q.open_target).mem_nhds ⟨hP ▸ ⟨a, ha⟩, hQ ▸ ⟨b, hb⟩⟩
  refine (hlocal.contMDiffAt hmem).congr_of_eventuallyEq ?_
  -- The known affine-chart formula identifies this local holomorphic map with the inverse.
  filter_upwards [hmem] with z hz
  obtain ⟨x, hx⟩ := hP ▸ hz.1
  obtain ⟨y, hy⟩ := hQ ▸ hz.2
  have hPx : P.symm (Φ.analyticAffineChartι hΦ σ x) = x := by
    rw [← Φ.analyticAffineChartPartialDiffeomorph_apply hΦ σ hB κ g n x]
    exact P.left_inv ((Φ.analyticAffineChartPartialDiffeomorph_source hΦ σ hB κ g n).symm ▸
      mem_univ x)
  have hQy : Q.symm (Ψ.analyticAffineChartι hΨ τ y) = y := by
    rw [← Ψ.analyticAffineChartPartialDiffeomorph_apply hΨ τ hC κ' g' n y]
    exact Q.left_inv ((Ψ.analyticAffineChartPartialDiffeomorph_source hΨ τ hC κ' g' n).symm ▸
      mem_univ y)
  rw [← Prod.eta z, ← hx, ← hy]
  simp only [Function.comp_apply, hPx, hQy, analyticProdHomeomorph_symm_analyticAffineChartι,
    coe_analyticAffineChartProdHomeomorph_symm]
  -- The remaining wrappers only identify bundled chart points with affine complex points.
  rfl

/-- The canonical biholomorphism between the realization of a product of regular fans and
the product of their realizations. Both directions are `C^n` over `ℂ` for every order `n`. -/
noncomputable def analyticProdDiffeomorph (n : ℕ∞ω) :
    letI := (Φ.prod Ψ).analyticChartedSpace (IsRegular.prod Φ Ψ hΦ hΨ)
    letI := Φ.analyticChartedSpace hΦ
    letI := Ψ.analyticChartedSpace hΨ
    Diffeomorph 𝓘(ℂ, Fin (Module.finrank ℤ (N × N')) → ℂ)
      (𝓘(ℂ, Fin (Module.finrank ℤ N) → ℂ).prod
        𝓘(ℂ, Fin (Module.finrank ℤ N') → ℂ))
      ((Φ.prod Ψ).analyticRealization (IsRegular.prod Φ Ψ hΦ hΨ))
      (Φ.analyticRealization hΦ × Ψ.analyticRealization hΨ) n :=
  letI := (Φ.prod Ψ).analyticChartedSpace (IsRegular.prod Φ Ψ hΦ hΨ)
  letI := Φ.analyticChartedSpace hΦ
  letI := Ψ.analyticChartedSpace hΨ
  { toEquiv := (Φ.analyticProdHomeomorph Ψ hΦ hΨ).toEquiv
    contMDiff_toFun := Φ.contMDiff_analyticProdHomeomorph Ψ hΦ hΨ n
    contMDiff_invFun := Φ.contMDiff_analyticProdHomeomorph_symm Ψ hΦ hΨ n }

/-- The product biholomorphism has the existing product homeomorphism as its underlying map. -/
@[simp]
theorem coe_analyticProdDiffeomorph (n : ℕ∞ω) :
    ⇑(Φ.analyticProdDiffeomorph Ψ hΦ hΨ n) = Φ.analyticProdHomeomorph Ψ hΦ hΨ := (rfl)

/-- The inverse product biholomorphism is the inverse of the existing product homeomorphism. -/
@[simp]
theorem coe_analyticProdDiffeomorph_symm (n : ℕ∞ω) :
    letI := (Φ.prod Ψ).analyticChartedSpace (IsRegular.prod Φ Ψ hΦ hΨ)
    letI := Φ.analyticChartedSpace hΦ
    letI := Ψ.analyticChartedSpace hΨ
    ⇑(Φ.analyticProdDiffeomorph Ψ hΦ hΨ n).symm =
      (Φ.analyticProdHomeomorph Ψ hΦ hΨ).symm := (rfl)

end TauCeti.Toric.Fan
