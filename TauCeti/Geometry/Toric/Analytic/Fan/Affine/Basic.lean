/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Toric.Analytic.Fan.Manifold
public import TauCeti.Geometry.Toric.Analytic.Fan.DenseTorus

/-!
# Analytic realizations of affine fans

The fan consisting of the faces of a regular cone realizes as the affine analytic chart of
that cone. The identification is the canonical chart inclusion, so every face chart becomes
its usual face-localization map. This identification is a biholomorphism for any extending
basis and any finite generating family of the dual semigroup.

The zero-cone fan is canonically homeomorphic to the coordinate-free complex torus via its
torus inclusion.

## References

* W. Fulton, *Introduction to Toric Varieties*, §§1.2 and 1.4.
* D. Cox, J. Little and H. Schenck, *Toric Varieties*, §§1.2 and 3.1.
-/

public section

open CategoryTheory Set
open scoped ContDiff Manifold

namespace TauCeti.Toric.Fan

universe u

variable {N V : Type u} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V} {σ : PointedCone ℝ V} (hi : IsIntegralLattice i) (hσ : IsRegularCone i σ)

local notation "σₜ" => (Subtype.mk σ
  (Iff.mpr (mem_ofCone_cones hi (IsRegularCone.toIsToricCone hσ))
    (PointedCone.IsFaceOf.refl σ)) : Fan.cones (ofCone hi (IsRegularCone.toIsToricCone hσ)))

/-- The maximal cone chart covers the realization of the fan of a regular cone. -/
theorem analyticAffineChartι_ofCone_surjective :
    Function.Surjective ((ofCone hi hσ.toIsToricCone).analyticAffineChartι
      (isRegular_ofCone hi hσ) σₜ) := by
  intro x
  obtain ⟨τ, y, rfl⟩ := (ofCone hi hσ.toIsToricCone).exists_analyticAffineChartι_apply_eq
    (isRegular_ofCone hi hσ) x
  exact ⟨_, (ofCone hi hσ.toIsToricCone).analyticAffineChartι_faceAffinePointMap
    (isRegular_ofCone hi hσ) (τ := τ) (σ := σₜ)
    ((mem_ofCone_cones hi hσ.toIsToricCone).1 τ.2).le y⟩

/-- The canonical homeomorphism from the maximal affine chart to the analytic realization of
the fan of a regular cone. -/
noncomputable def analyticOfConeHomeomorph :
    (ofCone hi hσ.toIsToricCone).analyticAffineChartDiagram.obj σₜ ≃ₜ
      (ofCone hi hσ.toIsToricCone).analyticRealization (isRegular_ofCone hi hσ) :=
  ((ofCone hi hσ.toIsToricCone).isOpenEmbedding_analyticAffineChartι
    (isRegular_ofCone hi hσ) σₜ).isEmbedding.toHomeomorphOfSurjective
      (analyticAffineChartι_ofCone_surjective hi hσ)

/-- The affine-fan identification is the canonical inclusion of the maximal chart. -/
@[simp]
theorem analyticOfConeHomeomorph_apply
    (x : (ofCone hi hσ.toIsToricCone).analyticAffineChartDiagram.obj σₜ) :
    analyticOfConeHomeomorph hi hσ x = (ofCone hi hσ.toIsToricCone).analyticAffineChartι
      (isRegular_ofCone hi hσ) σₜ x := (rfl)

/-- Every face chart becomes its face-localization map under the affine-fan identification. -/
theorem analyticOfConeHomeomorph_symm_analyticAffineChartι
    (τ : (ofCone hi hσ.toIsToricCone).cones)
    (x : (ofCone hi hσ.toIsToricCone).analyticAffineChartDiagram.obj τ) :
    (analyticOfConeHomeomorph hi hσ).symm
      ((ofCone hi hσ.toIsToricCone).analyticAffineChartι (isRegular_ofCone hi hσ) τ x) =
        faceAffinePointMap hi ((mem_ofCone_cones hi hσ.toIsToricCone).1 τ.2) x := by
  rw [← (ofCone hi hσ.toIsToricCone).analyticAffineChartι_faceAffinePointMap
      (isRegular_ofCone hi hσ) (τ := τ) (σ := σₜ)
      ((mem_ofCone_cones hi hσ.toIsToricCone).1 τ.2).le x,
    ← analyticOfConeHomeomorph_apply hi hσ
      (faceAffinePointMap hi ((mem_ofCone_cones hi hσ.toIsToricCone).1 τ.2) x)]
  exact (analyticOfConeHomeomorph hi hσ).symm_apply_apply _

section Manifold

variable {k l s : ℕ} {B : Module.Basis (ToricRay σ ⊕ Fin l) ℤ N}
  (hB : ∀ ρ, IsPrimitiveGenerator i ρ (B (Sum.inl ρ))) (κ : ToricRay σ ≃ Fin k)
  (g : AddGeneratingFamily (dualSemigroup hi σ) s)

/-- The affine-fan identification is a biholomorphism for any extending basis and any
generating family of the dual semigroup. -/
noncomputable def analyticOfConeDiffeomorph (n : ℕ∞ω) :
    let _ := affinePointTopology g
    let _ := coneChartedSpace hi hσ.toIsToricCone hB κ g
    letI := (ofCone hi hσ.toIsToricCone).analyticChartedSpace (isRegular_ofCone hi hσ)
    Diffeomorph 𝓘(ℂ, (Fin k → ℂ) × (Fin l → ℂ)) 𝓘(ℂ, Fin (Module.finrank ℤ N) → ℂ)
      (AffineSemigroupComplexPoint (dualSemigroup hi σ))
      ((ofCone hi hσ.toIsToricCone).analyticRealization (isRegular_ofCone hi hσ)) n :=
  let _ := affinePointTopology g
  let _ := coneChartedSpace hi hσ.toIsToricCone hB κ g
  letI := (ofCone hi hσ.toIsToricCone).analyticChartedSpace (isRegular_ofCone hi hσ)
  let P := (ofCone hi hσ.toIsToricCone).analyticAffineChartPartialDiffeomorph
    (isRegular_ofCone hi hσ) σₜ hB κ g n
  let hs : P.source = univ :=
    (ofCone hi hσ.toIsToricCone).analyticAffineChartPartialDiffeomorph_source _ _ _ _ _ _
  let ht : P.target = univ := by
    rw [analyticAffineChartPartialDiffeomorph_target,
      range_eq_univ.mpr (analyticAffineChartι_ofCone_surjective hi hσ)]
  let hf : ContMDiff 𝓘(ℂ, (Fin k → ℂ) × (Fin l → ℂ))
      𝓘(ℂ, Fin (Module.finrank ℤ N) → ℂ) n P := by
    simpa only [hs, contMDiffOn_univ] using P.contMDiffOn_toFun
  let hi' : ContMDiff 𝓘(ℂ, Fin (Module.finrank ℤ N) → ℂ)
      𝓘(ℂ, (Fin k → ℂ) × (Fin l → ℂ)) n P.invFun := by
    simpa only [ht, contMDiffOn_univ] using P.contMDiffOn_invFun
  { toEquiv :=
      { toFun := P
        invFun := P.invFun
        left_inv := fun x ↦ P.left_inv (hs.symm ▸ mem_univ x)
        right_inv := fun x ↦ P.right_inv (ht.symm ▸ mem_univ x) }
    contMDiff_toFun := hf
    contMDiff_invFun := hi' }

/-- The biholomorphism of an affine fan is its maximal chart inclusion. -/
@[simp]
theorem analyticOfConeDiffeomorph_apply (n : ℕ∞ω)
    (x : AffineSemigroupComplexPoint (dualSemigroup hi σ)) :
    analyticOfConeDiffeomorph hi hσ hB κ g n x =
      (ofCone hi hσ.toIsToricCone).analyticAffineChartι (isRegular_ofCone hi hσ)
        σₜ x :=
  (ofCone hi hσ.toIsToricCone).analyticAffineChartPartialDiffeomorph_apply
    (isRegular_ofCone hi hσ) σₜ hB κ g n x

/-- The inverse biholomorphism recovers a point from its maximal-chart inclusion. -/
@[simp]
theorem analyticOfConeDiffeomorph_symm_analyticAffineChartι_top (n : ℕ∞ω)
    (x : AffineSemigroupComplexPoint (dualSemigroup hi σ)) :
    let _ := affinePointTopology g
    let _ := coneChartedSpace hi hσ.toIsToricCone hB κ g
    letI := (ofCone hi hσ.toIsToricCone).analyticChartedSpace (isRegular_ofCone hi hσ)
    (analyticOfConeDiffeomorph hi hσ hB κ g n).symm
      ((ofCone hi hσ.toIsToricCone).analyticAffineChartι (isRegular_ofCone hi hσ)
        σₜ x) = x := by
  intro _ _
  let _ := (ofCone hi hσ.toIsToricCone).analyticChartedSpace (isRegular_ofCone hi hσ)
  rw [← analyticOfConeDiffeomorph_apply hi hσ hB κ g n x]
  exact (analyticOfConeDiffeomorph hi hσ hB κ g n).symm_apply_apply x

/-- Every face chart becomes its face-localization map under the affine-fan biholomorphism. -/
theorem analyticOfConeDiffeomorph_symm_analyticAffineChartι (n : ℕ∞ω)
    (τ : (ofCone hi hσ.toIsToricCone).cones)
    (x : (ofCone hi hσ.toIsToricCone).analyticAffineChartDiagram.obj τ) :
    let _ := affinePointTopology g
    let _ := coneChartedSpace hi hσ.toIsToricCone hB κ g
    letI := (ofCone hi hσ.toIsToricCone).analyticChartedSpace (isRegular_ofCone hi hσ)
    (analyticOfConeDiffeomorph hi hσ hB κ g n).symm
      ((ofCone hi hσ.toIsToricCone).analyticAffineChartι (isRegular_ofCone hi hσ) τ x) =
        faceAffinePointMap hi ((mem_ofCone_cones hi hσ.toIsToricCone).1 τ.2) x := by
  intro _ _
  let _ := (ofCone hi hσ.toIsToricCone).analyticChartedSpace (isRegular_ofCone hi hσ)
  rw [← (ofCone hi hσ.toIsToricCone).analyticAffineChartι_faceAffinePointMap
      (isRegular_ofCone hi hσ) (τ := τ) (σ := σₜ)
      ((mem_ofCone_cones hi hσ.toIsToricCone).1 τ.2).le x,
    ← analyticOfConeDiffeomorph_apply hi hσ hB κ g n]
  exact (analyticOfConeDiffeomorph hi hσ hB κ g n).symm_apply_apply _

end Manifold

section ZeroCone

local notation "Φ₀" => ofCone hi (isToricCone_bot i)
local notation "h₀" => isRegular_ofCone hi (isRegularCone_bot hi)
local notation "z₀" => (Subtype.mk (⊥ : PointedCone ℝ V)
  (Iff.mpr (mem_ofCone_cones hi (isToricCone_bot i))
    (PointedCone.IsFaceOf.refl ⊥)) : Fan.cones Φ₀)

private noncomputable def zeroConeChartHomeomorph :
    ComplexTorus N ≃ₜ (Φ₀).analyticAffineChartDiagram.obj z₀ :=
  zeroConeChartHomeomorphOfBasis hi
    (isRegularCone_bot hi).exists_basis_sum.choose_spec.choose_spec
    ((Φ₀).analyticChartGenerators z₀).2

private theorem zeroConeChartHomeomorph_apply (t : ComplexTorus N) :
    zeroConeChartHomeomorph hi t =
      t • (default : AffineSemigroupComplexPoint (dualSemigroup hi (⊥ : PointedCone ℝ V))) :=
  zeroConeChartHomeomorphOfBasis_apply hi _ _ t

/-- The analytic realization of the fan of the zero cone is the coordinate-free complex torus.
The forward map is its canonical torus inclusion. -/
noncomputable def analyticZeroConeHomeomorph :
    ComplexTorus N ≃ₜ (Φ₀).analyticRealization h₀ :=
  (zeroConeChartHomeomorph hi).trans (analyticOfConeHomeomorph hi (isRegularCone_bot hi))

/-- The zero-cone identification is the canonical torus parametrization of the realization. -/
@[simp]
theorem analyticZeroConeHomeomorph_apply (t : ComplexTorus N) :
    analyticZeroConeHomeomorph hi t = (Φ₀).analyticTorusι h₀ ⟨z₀⟩ t := by
  rw [analyticZeroConeHomeomorph, Homeomorph.trans_apply,
    analyticOfConeHomeomorph_apply, zeroConeChartHomeomorph_apply]
  exact ((Φ₀).analyticTorusι_eq_analyticAffineChartι h₀ ⟨z₀⟩ z₀ t).symm

/-- The inverse zero-cone identification recovers the torus point from its canonical inclusion. -/
@[simp]
theorem analyticZeroConeHomeomorph_symm_analyticTorusι (t : ComplexTorus N) :
    (analyticZeroConeHomeomorph hi).symm ((Φ₀).analyticTorusι h₀ ⟨z₀⟩ t) = t := by
  rw [← analyticZeroConeHomeomorph_apply]
  exact (analyticZeroConeHomeomorph hi).symm_apply_apply t

end ZeroCone

end TauCeti.Toric.Fan
