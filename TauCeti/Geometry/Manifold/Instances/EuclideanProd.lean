/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Geometry.Manifold.Diffeomorph
public import Mathlib.Geometry.Manifold.HasGroupoid

/-!
# Euclidean charts on products

Mathlib charts a product `M × N` of spaces charted on `H` and `H'` on the type synonym
`ModelProd H H'`. For spaces charted on Euclidean spaces this file reads those product charts on a
single Euclidean space: `TauCeti.prodEuclideanChartedSpace` charts `M × N` on
`EuclideanSpace 𝕜 (Fin (n + m))` when `M` and `N` are charted on `EuclideanSpace 𝕜 (Fin n)` and
`EuclideanSpace 𝕜 (Fin m)`, by composing the product charts with
`EuclideanSpace.finAddEquivProd`. `TauCeti.prodEuclideanChartedSpace_chartAt` describes its charts.

When `M` and `N` are `C^r` manifolds, these composite charts make `M × N` a `C^r` manifold
modelled on `EuclideanSpace 𝕜 (Fin (n + m))` (`TauCeti.isManifold_prodEuclideanChartedSpace`), and
the identity map is a `C^r` diffeomorphism between `TauCeti.prodEuclideanChartedSpace` and the
native product charted space (`TauCeti.prodEuclideanDiffeomorph`).

`TauCeti.prodEuclideanChartedSpace` is a definition rather than an instance, so that the Euclidean
model can be chosen explicitly alongside Mathlib's product model.
-/

public section

open scoped ContDiff Manifold Topology

namespace TauCeti

variable {𝕜 : Type*} [RCLike 𝕜] {n m : ℕ} {M N : Type*} [TopologicalSpace M] [TopologicalSpace N]
  [ChartedSpace (EuclideanSpace 𝕜 (Fin n)) M] [ChartedSpace (EuclideanSpace 𝕜 (Fin m)) N]

/-- The product `M × N` of spaces charted on `𝕜ⁿ` and `𝕜ᵐ`, charted on `𝕜ⁿ⁺ᵐ`: the product of
charts of `M` and `N`, followed by the identification `EuclideanSpace.finAddEquivProd` of
`𝕜ⁿ × 𝕜ᵐ` with `𝕜ⁿ⁺ᵐ`. -/
@[instance_reducible]
noncomputable def prodEuclideanChartedSpace :
    ChartedSpace (EuclideanSpace 𝕜 (Fin (n + m))) (M × N) :=
  letI : ChartedSpace (EuclideanSpace 𝕜 (Fin (n + m)))
      (ModelProd (EuclideanSpace 𝕜 (Fin n)) (EuclideanSpace 𝕜 (Fin m))) :=
    (EuclideanSpace.finAddEquivProd (𝕜 := 𝕜)).symm.toHomeomorph.toOpenPartialHomeomorph
      |>.singletonChartedSpace (by simp)
  ChartedSpace.comp _ (ModelProd (EuclideanSpace 𝕜 (Fin n)) (EuclideanSpace 𝕜 (Fin m))) _

/-- The chart of `TauCeti.prodEuclideanChartedSpace` at `x` is the product of the charts of the
factors at `x.1` and `x.2`, followed by `EuclideanSpace.finAddEquivProd.symm`. -/
@[simp, mfld_simps]
theorem prodEuclideanChartedSpace_chartAt (x : M × N) :
    @chartAt _ _ _ _ (prodEuclideanChartedSpace (𝕜 := 𝕜)) x =
      ((chartAt (EuclideanSpace 𝕜 (Fin n)) x.1).prod (chartAt (EuclideanSpace 𝕜 (Fin m)) x.2)).trans
        (EuclideanSpace.finAddEquivProd (𝕜 := 𝕜)).symm.toHomeomorph.toOpenPartialHomeomorph :=
  (rfl)

/-- When `M` and `N` are `C^r` manifolds modelled on `𝕜ⁿ` and `𝕜ᵐ`,
`TauCeti.prodEuclideanChartedSpace` makes `M × N` a `C^r` manifold modelled on `𝕜ⁿ⁺ᵐ`. -/
theorem isManifold_prodEuclideanChartedSpace (r : ℕ∞ω)
    [IsManifold 𝓘(𝕜, EuclideanSpace 𝕜 (Fin n)) r M]
    [IsManifold 𝓘(𝕜, EuclideanSpace 𝕜 (Fin m)) r N] :
    letI := prodEuclideanChartedSpace (𝕜 := 𝕜) (n := n) (m := m) (M := M) (N := N)
    IsManifold 𝓘(𝕜, EuclideanSpace 𝕜 (Fin (n + m))) r (M × N) := by
  let := prodEuclideanChartedSpace (𝕜 := 𝕜) (n := n) (m := m) (M := M) (N := N)
  refine { compatible := ?_ }
  rintro _ _ ⟨_, ⟨c₁, hc₁, c₂, hc₂, rfl⟩, φ, hφ, rfl⟩
    ⟨_, ⟨c₁', hc₁', c₂', hc₂', rfl⟩, φ', hφ', rfl⟩
  obtain rfl := OpenPartialHomeomorph.singletonChartedSpace_mem_atlas_eq _ _ φ hφ
  obtain rfl := OpenPartialHomeomorph.singletonChartedSpace_mem_atlas_eq _ _ φ' hφ'
  rw [OpenPartialHomeomorph.trans_symm_eq_symm_trans_symm, OpenPartialHomeomorph.trans_assoc,
    ← OpenPartialHomeomorph.trans_assoc (c₁.prod c₂).symm]
  have hcomp : (c₁.prod c₂).symm ≫ₕ (c₁'.prod c₂') ∈ contDiffGroupoid r
      (𝓘(𝕜, EuclideanSpace 𝕜 (Fin n)).prod 𝓘(𝕜, EuclideanSpace 𝕜 (Fin m))) := by
    rw [OpenPartialHomeomorph.prod_symm, OpenPartialHomeomorph.prod_trans]
    exact contDiffGroupoid_prod (HasGroupoid.compatible (G := contDiffGroupoid r _) hc₁ hc₁')
      (HasGroupoid.compatible (G := contDiffGroupoid r _) hc₂ hc₂')
  set ψ := (EuclideanSpace.finAddEquivProd (𝕜 := 𝕜) (n := n) (m := m)).symm.toHomeomorph
    |>.toOpenPartialHomeomorph
  let I₁₂ := 𝓘(𝕜, EuclideanSpace 𝕜 (Fin n)).prod 𝓘(𝕜, EuclideanSpace 𝕜 (Fin m))
  have hψ : ∀ {e : OpenPartialHomeomorph (ModelProd (EuclideanSpace 𝕜 (Fin n))
        (EuclideanSpace 𝕜 (Fin m))) (ModelProd (EuclideanSpace 𝕜 (Fin n))
        (EuclideanSpace 𝕜 (Fin m)))},
      e ∈ contDiffGroupoid r I₁₂ →
      ψ.symm ≫ₕ (e ≫ₕ ψ) ∈ contDiffGroupoid r 𝓘(𝕜, EuclideanSpace 𝕜 (Fin (n + m))) := by
    have hstep : ∀ {f : OpenPartialHomeomorph (ModelProd (EuclideanSpace 𝕜 (Fin n))
          (EuclideanSpace 𝕜 (Fin m))) (ModelProd (EuclideanSpace 𝕜 (Fin n))
          (EuclideanSpace 𝕜 (Fin m)))},
        f ∈ contDiffGroupoid r I₁₂ →
        ContDiffOn 𝕜 r (ψ ∘ f ∘ ψ.symm)
          (ψ.symm ⁻¹' (f.source ∩ ↑f ⁻¹' ψ.source) ∩ ψ.symm ⁻¹' ψ.source) := by
      intro f hf
      have hf1 : ContDiffOn 𝕜 r (I₁₂ ∘ f ∘ I₁₂.symm) (I₁₂.symm ⁻¹' f.source ∩ Set.range I₁₂) :=
        hf.1
      refine (EuclideanSpace.finAddEquivProd (𝕜 := 𝕜) (n := n) (m := m)).symm.contDiff.contDiffOn
        |>.comp (hf1.comp ((EuclideanSpace.finAddEquivProd (𝕜 := 𝕜) (n := n) (m := m)).contDiff
          |>.contDiffOn) fun x hx ↦ ?_) fun x _ ↦ Set.mem_univ _
      simpa [I₁₂, ψ] using hx.1.1
    intro e he
    constructor
    · refine (hstep he).congr_mono (fun x _ ↦ ?_) fun x hx ↦ ?_
      · simp [OpenPartialHomeomorph.coe_trans]
      · simpa [OpenPartialHomeomorph.trans_source, ψ] using hx
    · refine (hstep ((contDiffGroupoid r I₁₂).symm he)).congr_mono (fun x _ ↦ ?_) fun x hx ↦ ?_
      · simp [OpenPartialHomeomorph.coe_trans, OpenPartialHomeomorph.trans_symm_eq_symm_trans_symm]
      · simpa [OpenPartialHomeomorph.trans_source,
          OpenPartialHomeomorph.trans_symm_eq_symm_trans_symm, ψ] using hx
  exact hψ hcomp

/-- The identity map of `M × N` as a `C^r` diffeomorphism between
`TauCeti.prodEuclideanChartedSpace` (modelled on `𝕜ⁿ⁺ᵐ`) and the product charted space (modelled
on `𝕜ⁿ × 𝕜ᵐ`). -/
noncomputable def prodEuclideanDiffeomorph (r : ℕ∞ω) :
    letI := prodEuclideanChartedSpace (𝕜 := 𝕜) (n := n) (m := m) (M := M) (N := N)
    (M × N) ≃ₘ^r⟮𝓘(𝕜, EuclideanSpace 𝕜 (Fin (n + m))),
      𝓘(𝕜, EuclideanSpace 𝕜 (Fin n)).prod 𝓘(𝕜, EuclideanSpace 𝕜 (Fin m))⟯ (M × N) :=
  letI := prodEuclideanChartedSpace (𝕜 := 𝕜) (n := n) (m := m) (M := M) (N := N)
  { toEquiv := Equiv.refl _
    contMDiff_toFun := fun x ↦ by
      rw [contMDiffAt_iff]
      refine ⟨continuousAt_id, ?_⟩
      let c := (chartAt (EuclideanSpace 𝕜 (Fin n)) x.1).prod
        (chartAt (EuclideanSpace 𝕜 (Fin m)) x.2)
      have hev : (extChartAt (𝓘(𝕜, EuclideanSpace 𝕜 (Fin n)).prod
            𝓘(𝕜, EuclideanSpace 𝕜 (Fin m))) x ∘
          id ∘ (extChartAt 𝓘(𝕜, EuclideanSpace 𝕜 (Fin (n + m))) x).symm) =ᶠ[
            𝓝 (extChartAt 𝓘(𝕜, EuclideanSpace 𝕜 (Fin (n + m))) x x)]
          (EuclideanSpace.finAddEquivProd (𝕜 := 𝕜) :
            EuclideanSpace 𝕜 (Fin (n + m)) →
              EuclideanSpace 𝕜 (Fin n) × EuclideanSpace 𝕜 (Fin m)) := by
        filter_upwards [extChartAt_target_mem_nhds
          (I := 𝓘(𝕜, EuclideanSpace 𝕜 (Fin (n + m)))) x] with z hz
        have hz' : EuclideanSpace.finAddEquivProd (𝕜 := 𝕜) z ∈ c.target := by
          simpa [c, extChartAt_target, prodEuclideanChartedSpace_chartAt] using hz
        simp only [Function.comp_apply, id_eq, extChartAt_prod, extChartAt_coe_symm,
          modelWithCornersSelf_coe_symm, prodEuclideanChartedSpace_chartAt,
          OpenPartialHomeomorph.coe_trans_symm, Homeomorph.toOpenPartialHomeomorph_symm_apply]
        simpa [c, extChartAt_coe, Prod.ext_iff] using c.right_inv hz'
      exact (EuclideanSpace.finAddEquivProd (𝕜 := 𝕜)).contDiff.contDiffWithinAt
        |>.congr_of_eventuallyEq (hev.filter_mono nhdsWithin_le_nhds) hev.self_of_nhds
    contMDiff_invFun := fun x ↦ by
      rw [contMDiffAt_iff]
      refine ⟨continuousAt_id, ?_⟩
      have hev : (extChartAt 𝓘(𝕜, EuclideanSpace 𝕜 (Fin (n + m))) x ∘
          id ∘ (extChartAt (𝓘(𝕜, EuclideanSpace 𝕜 (Fin n)).prod
            𝓘(𝕜, EuclideanSpace 𝕜 (Fin m))) x).symm) =ᶠ[
            𝓝 (extChartAt (𝓘(𝕜, EuclideanSpace 𝕜 (Fin n)).prod
              𝓘(𝕜, EuclideanSpace 𝕜 (Fin m))) x x)]
          ((EuclideanSpace.finAddEquivProd (𝕜 := 𝕜)).symm :
            EuclideanSpace 𝕜 (Fin n) × EuclideanSpace 𝕜 (Fin m) →
              EuclideanSpace 𝕜 (Fin (n + m))) := by
        filter_upwards [extChartAt_target_mem_nhds
          (I := 𝓘(𝕜, EuclideanSpace 𝕜 (Fin n)).prod 𝓘(𝕜, EuclideanSpace 𝕜 (Fin m))) x] with z hz
        rw [extChartAt_prod] at hz
        have hz' : z.1 ∈ (extChartAt 𝓘(𝕜, EuclideanSpace 𝕜 (Fin n)) x.1).target ∧
            z.2 ∈ (extChartAt 𝓘(𝕜, EuclideanSpace 𝕜 (Fin m)) x.2).target :=
          ⟨hz.1, hz.2⟩
        have h1 : chartAt (EuclideanSpace 𝕜 (Fin n)) x.1
            ((extChartAt 𝓘(𝕜, EuclideanSpace 𝕜 (Fin n)) x.1).symm z.1) = z.1 := by
          simpa [extChartAt_coe] using
            (extChartAt 𝓘(𝕜, EuclideanSpace 𝕜 (Fin n)) x.1).right_inv hz'.1
        have h2 : chartAt (EuclideanSpace 𝕜 (Fin m)) x.2
            ((extChartAt 𝓘(𝕜, EuclideanSpace 𝕜 (Fin m)) x.2).symm z.2) = z.2 := by
          simpa [extChartAt_coe] using
            (extChartAt 𝓘(𝕜, EuclideanSpace 𝕜 (Fin m)) x.2).right_inv hz'.2
        simp only [Function.comp_apply, id_eq, extChartAt_coe, extChartAt_prod,
          modelWithCornersSelf_coe, prodEuclideanChartedSpace_chartAt,
          OpenPartialHomeomorph.coe_trans, Homeomorph.toOpenPartialHomeomorph_apply,
          ContinuousLinearEquiv.coe_toHomeomorph]
        -- Expose the inner chart applications so `h1` and `h2` apply.
        change (EuclideanSpace.finAddEquivProd (𝕜 := 𝕜)).symm
          (chartAt (EuclideanSpace 𝕜 (Fin n)) x.1
            ((extChartAt 𝓘(𝕜, EuclideanSpace 𝕜 (Fin n)) x.1).symm z.1),
          chartAt (EuclideanSpace 𝕜 (Fin m)) x.2
            ((extChartAt 𝓘(𝕜, EuclideanSpace 𝕜 (Fin m)) x.2).symm z.2)) = _
        rw [h1, h2]
      exact (EuclideanSpace.finAddEquivProd (𝕜 := 𝕜)).symm.contDiff.contDiffWithinAt
        |>.congr_of_eventuallyEq (hev.filter_mono nhdsWithin_le_nhds) hev.self_of_nhds }

@[simp]
theorem coe_prodEuclideanDiffeomorph (r : ℕ∞ω) :
    letI := prodEuclideanChartedSpace (𝕜 := 𝕜) (n := n) (m := m) (M := M) (N := N)
    ⇑(prodEuclideanDiffeomorph (𝕜 := 𝕜) (n := n) (m := m) (M := M) (N := N) r) = id :=
  (rfl)

@[simp]
theorem coe_prodEuclideanDiffeomorph_symm (r : ℕ∞ω) :
    letI := prodEuclideanChartedSpace (𝕜 := 𝕜) (n := n) (m := m) (M := M) (N := N)
    ⇑(prodEuclideanDiffeomorph (𝕜 := 𝕜) (n := n) (m := m) (M := M) (N := N) r).symm = id :=
  (rfl)

end TauCeti
