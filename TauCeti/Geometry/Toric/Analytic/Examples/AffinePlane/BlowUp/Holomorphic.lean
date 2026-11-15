/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Diffeomorph.Basic
public import TauCeti.Geometry.Toric.Analytic.Examples.AffinePlane.BlowUp.Basic

/-!
# Biholomorphic charts of the toric blow-up of the plane

The explicit upper and lower affine coordinates on the diagonal subdivision are holomorphic in
both directions. Composing these affine-chart coordinates with the canonical inclusions into the
analytic realization gives two biholomorphic parametrizations by `ℂ × ℂ`. Their open images cover
the toric blow-up.

The inverse coordinate maps are holomorphic because every character monomial pulls back to a
product of natural powers of the two coordinates. This uses the intrinsic monomial criterion for
holomorphy on a regular affine toric chart, so the result is independent of the extending bases
chosen to define the charted spaces.

## References

* W. Fulton, *Introduction to Toric Varieties*, §§1.4 and 2.4.
* D. Cox, J. Little and H. Schenck, *Toric Varieties*, §§3.1 and 3.3.
-/

public section

open Set
open scoped ContDiff Manifold

namespace TauCeti.Toric

private abbrev PlaneLattice := (Fin 1 → ℤ) × (Fin 1 → ℤ)

private noncomputable def pointDiffeomorph
    {σ : PointedCone ℝ ((Fin 1 → ℝ) × (Fin 1 → ℝ))}
    (hσ : IsRegularCone
      (((Int.castAddHom ℝ).compLeft (Fin 1)).prodMap
        ((Int.castAddHom ℝ).compLeft (Fin 1))) σ)
    {l k s : ℕ} {B : Module.Basis (ToricRay σ ⊕ Fin l) ℤ PlaneLattice}
    (hB : ∀ ρ, IsPrimitiveGenerator
      (((Int.castAddHom ℝ).compLeft (Fin 1)).prodMap
        ((Int.castAddHom ℝ).compLeft (Fin 1))) ρ (B (Sum.inl ρ)))
    (κ : ToricRay σ ≃ Fin k) (g : AddGeneratingFamily (dualSemigroup affinePlaneFan.lattice σ) s)
    (e : AffineSemigroupComplexPoint (dualSemigroup affinePlaneFan.lattice σ) ≃ ℂ × ℂ)
    (m₁ m₂ : dualSemigroup affinePlaneFan.lattice σ)
    (he : ∀ x, e x =
      (x (MonoidAlgebra.single (.ofAdd m₁) 1), x (MonoidAlgebra.single (.ofAdd m₂) 1)))
    (p q : dualSemigroup affinePlaneFan.lattice σ → ℕ)
    (he_symm : ∀ z m, e.symm z (MonoidAlgebra.single (.ofAdd m) 1) =
      z.1 ^ p m * z.2 ^ q m) (n : ℕ∞ω) :
    let _ := affinePointTopology g
    let _ := coneChartedSpace affinePlaneFan.lattice hσ.toIsToricCone hB κ g
    Diffeomorph 𝓘(ℂ, (Fin k → ℂ) × (Fin l → ℂ)) (𝓘(ℂ, ℂ).prod 𝓘(ℂ, ℂ))
      (AffineSemigroupComplexPoint (dualSemigroup affinePlaneFan.lattice σ)) (ℂ × ℂ) n := by
  let _ := affinePointTopology g
  let _ := coneChartedSpace affinePlaneFan.lattice hσ.toIsToricCone hB κ g
  refine ⟨e, ?_, ?_⟩
  · exact ((contMDiff_apply_single affinePlaneFan.lattice hσ.toIsToricCone hB κ g m₁ n).prodMk
      (contMDiff_apply_single affinePlaneFan.lattice hσ.toIsToricCone hB κ g m₂ n)).congr he
  · refine (contMDiff_iff_forall_contMDiff_apply_single affinePlaneFan.lattice
      hσ.toIsToricCone hB κ g).2 fun m ↦ ?_
    exact (((contMDiff_fst.pow _).mul (contMDiff_snd.pow _)).congr fun z ↦ he_symm z m)

private noncomputable def upperComplementDim : ℕ :=
  isRegularCone_affinePlaneBlowUpUpperCone.exists_basis_sum.choose

private noncomputable def upperBasis :
    Module.Basis (ToricRay affinePlaneBlowUpUpperCone ⊕ Fin upperComplementDim) ℤ PlaneLattice :=
  isRegularCone_affinePlaneBlowUpUpperCone.exists_basis_sum.choose_spec.choose

private theorem upperBasis_extends (ρ : ToricRay affinePlaneBlowUpUpperCone) :
    IsPrimitiveGenerator
      (((Int.castAddHom ℝ).compLeft (Fin 1)).prodMap
        ((Int.castAddHom ℝ).compLeft (Fin 1))) ρ (upperBasis (Sum.inl ρ)) :=
  isRegularCone_affinePlaneBlowUpUpperCone.exists_basis_sum.choose_spec.choose_spec ρ

private noncomputable def upperRayNumbering :
    ToricRay affinePlaneBlowUpUpperCone ≃ Fin (Nat.card (ToricRay affinePlaneBlowUpUpperCone)) := by
  letI := ToricRay.finite_of_fg isRegularCone_affinePlaneBlowUpUpperCone.fg
  exact Finite.equivFin _

private noncomputable abbrev upperGenerators :=
  (affinePlaneBlowUpFan.analyticChartGenerators
    ⟨affinePlaneBlowUpUpperCone, mem_affinePlaneBlowUpFan_cones.2 (Or.inr (.refl _))⟩).2

private noncomputable abbrev upperChartedSpace :=
  coneChartedSpace affinePlaneFan.lattice
    isRegularCone_affinePlaneBlowUpUpperCone.toIsToricCone upperBasis_extends
      upperRayNumbering upperGenerators

private noncomputable def upperPointDiffeomorph (n : ℕ∞ω) :
    let _ := affinePointTopology upperGenerators
    let _ := upperChartedSpace
    Diffeomorph
      𝓘(ℂ, (Fin (Nat.card (ToricRay affinePlaneBlowUpUpperCone)) → ℂ) ×
        (Fin upperComplementDim → ℂ))
      (𝓘(ℂ, ℂ).prod 𝓘(ℂ, ℂ))
      (AffineSemigroupComplexPoint
        (dualSemigroup affinePlaneFan.lattice affinePlaneBlowUpUpperCone)) (ℂ × ℂ) n := by
  exact pointDiffeomorph isRegularCone_affinePlaneBlowUpUpperCone upperBasis_extends
    upperRayNumbering upperGenerators affinePlaneBlowUpUpperPointHomeomorph.toEquiv
    affinePlaneBlowUpUpperCharacter₁ affinePlaneBlowUpUpperCharacter₂
    affinePlaneBlowUpUpperPointHomeomorph_apply
    (fun m ↦ ((m : PlaneLattice →+ ℤ) (1, 1)).toNat)
    (fun m ↦ ((m : PlaneLattice →+ ℤ) (0, 1)).toNat)
    affinePlaneBlowUpUpperPointHomeomorph_symm_apply_single n

private noncomputable def lowerComplementDim : ℕ :=
  isRegularCone_affinePlaneBlowUpLowerCone.exists_basis_sum.choose

private noncomputable def lowerBasis :
    Module.Basis (ToricRay affinePlaneBlowUpLowerCone ⊕ Fin lowerComplementDim) ℤ PlaneLattice :=
  isRegularCone_affinePlaneBlowUpLowerCone.exists_basis_sum.choose_spec.choose

private theorem lowerBasis_extends (ρ : ToricRay affinePlaneBlowUpLowerCone) :
    IsPrimitiveGenerator
      (((Int.castAddHom ℝ).compLeft (Fin 1)).prodMap
        ((Int.castAddHom ℝ).compLeft (Fin 1))) ρ (lowerBasis (Sum.inl ρ)) :=
  isRegularCone_affinePlaneBlowUpLowerCone.exists_basis_sum.choose_spec.choose_spec ρ

private noncomputable def lowerRayNumbering :
    ToricRay affinePlaneBlowUpLowerCone ≃ Fin (Nat.card (ToricRay affinePlaneBlowUpLowerCone)) := by
  letI := ToricRay.finite_of_fg isRegularCone_affinePlaneBlowUpLowerCone.fg
  exact Finite.equivFin _

private noncomputable abbrev lowerGenerators :=
  (affinePlaneBlowUpFan.analyticChartGenerators
    ⟨affinePlaneBlowUpLowerCone, mem_affinePlaneBlowUpFan_cones.2 (Or.inl (.refl _))⟩).2

private noncomputable abbrev lowerChartedSpace :=
  coneChartedSpace affinePlaneFan.lattice
    isRegularCone_affinePlaneBlowUpLowerCone.toIsToricCone lowerBasis_extends
      lowerRayNumbering lowerGenerators

private noncomputable def lowerPointDiffeomorph (n : ℕ∞ω) :
    let _ := affinePointTopology lowerGenerators
    let _ := lowerChartedSpace
    Diffeomorph
      𝓘(ℂ, (Fin (Nat.card (ToricRay affinePlaneBlowUpLowerCone)) → ℂ) ×
        (Fin lowerComplementDim → ℂ))
      (𝓘(ℂ, ℂ).prod 𝓘(ℂ, ℂ))
      (AffineSemigroupComplexPoint
        (dualSemigroup affinePlaneFan.lattice affinePlaneBlowUpLowerCone)) (ℂ × ℂ) n := by
  exact pointDiffeomorph isRegularCone_affinePlaneBlowUpLowerCone lowerBasis_extends
    lowerRayNumbering lowerGenerators affinePlaneBlowUpLowerPointHomeomorph.toEquiv
    affinePlaneBlowUpLowerCharacter₁ affinePlaneBlowUpLowerCharacter₂
    affinePlaneBlowUpLowerPointHomeomorph_apply
    (fun m ↦ ((m : PlaneLattice →+ ℤ) (1, 0)).toNat)
    (fun m ↦ ((m : PlaneLattice →+ ℤ) (1, 1)).toNat)
    affinePlaneBlowUpLowerPointHomeomorph_symm_apply_single n

/-- The upper affine coordinate map is a biholomorphism from `ℂ × ℂ` onto the upper-cone open
of the analytic toric blow-up. -/
noncomputable def affinePlaneBlowUpUpperPartialDiffeomorph (n : ℕ∞ω) :
    letI := affinePlaneBlowUpFan.analyticChartedSpace isRegular_affinePlaneBlowUpFan
    PartialDiffeomorph (𝓘(ℂ, ℂ).prod 𝓘(ℂ, ℂ))
      𝓘(ℂ, Fin (Module.finrank ℤ ((Fin 1 → ℤ) × (Fin 1 → ℤ))) → ℂ)
      (ℂ × ℂ) (affinePlaneBlowUpFan.analyticRealization isRegular_affinePlaneBlowUpFan) n := by
  let _ := affinePlaneBlowUpFan.analyticChartedSpace isRegular_affinePlaneBlowUpFan
  let _ := affinePointTopology upperGenerators
  let _ := upperChartedSpace
  exact (upperPointDiffeomorph n).symm.toPartialDiffeomorph.trans
    (affinePlaneBlowUpFan.analyticAffineChartPartialDiffeomorph
      isRegular_affinePlaneBlowUpFan
      ⟨affinePlaneBlowUpUpperCone, mem_affinePlaneBlowUpFan_cones.2 (Or.inr (.refl _))⟩
      upperBasis_extends upperRayNumbering upperGenerators n)

/-- The lower affine coordinate map is a biholomorphism from `ℂ × ℂ` onto the lower-cone open
of the analytic toric blow-up. -/
noncomputable def affinePlaneBlowUpLowerPartialDiffeomorph (n : ℕ∞ω) :
    letI := affinePlaneBlowUpFan.analyticChartedSpace isRegular_affinePlaneBlowUpFan
    PartialDiffeomorph (𝓘(ℂ, ℂ).prod 𝓘(ℂ, ℂ))
      𝓘(ℂ, Fin (Module.finrank ℤ ((Fin 1 → ℤ) × (Fin 1 → ℤ))) → ℂ)
      (ℂ × ℂ) (affinePlaneBlowUpFan.analyticRealization isRegular_affinePlaneBlowUpFan) n := by
  let _ := affinePlaneBlowUpFan.analyticChartedSpace isRegular_affinePlaneBlowUpFan
  let _ := affinePointTopology lowerGenerators
  let _ := lowerChartedSpace
  exact (lowerPointDiffeomorph n).symm.toPartialDiffeomorph.trans
    (affinePlaneBlowUpFan.analyticAffineChartPartialDiffeomorph
      isRegular_affinePlaneBlowUpFan
      ⟨affinePlaneBlowUpLowerCone, mem_affinePlaneBlowUpFan_cones.2 (Or.inl (.refl _))⟩
      lowerBasis_extends lowerRayNumbering lowerGenerators n)

/-- The upper biholomorphic parametrization is defined on all of `ℂ × ℂ`. -/
@[simp]
theorem affinePlaneBlowUpUpperPartialDiffeomorph_source (n : ℕ∞ω) :
    (affinePlaneBlowUpUpperPartialDiffeomorph n).source = univ := by
  simp [affinePlaneBlowUpUpperPartialDiffeomorph, PartialDiffeomorph.trans_toPartialEquiv,
    Diffeomorph.toPartialDiffeomorph_toPartialEquiv, PartialEquiv.trans_source]

/-- The lower biholomorphic parametrization is defined on all of `ℂ × ℂ`. -/
@[simp]
theorem affinePlaneBlowUpLowerPartialDiffeomorph_source (n : ℕ∞ω) :
    (affinePlaneBlowUpLowerPartialDiffeomorph n).source = univ := by
  simp [affinePlaneBlowUpLowerPartialDiffeomorph, PartialDiffeomorph.trans_toPartialEquiv,
    Diffeomorph.toPartialDiffeomorph_toPartialEquiv, PartialEquiv.trans_source]

/-- The upper biholomorphic parametrization maps onto exactly the upper-cone open. -/
@[simp]
theorem affinePlaneBlowUpUpperPartialDiffeomorph_target (n : ℕ∞ω) :
    (affinePlaneBlowUpUpperPartialDiffeomorph n).target =
      range (affinePlaneBlowUpFan.analyticAffineChartι isRegular_affinePlaneBlowUpFan
        ⟨affinePlaneBlowUpUpperCone,
          mem_affinePlaneBlowUpFan_cones.2 (Or.inr (.refl _))⟩) := by
  simp [affinePlaneBlowUpUpperPartialDiffeomorph, PartialDiffeomorph.trans_toPartialEquiv,
    Diffeomorph.toPartialDiffeomorph_toPartialEquiv, PartialEquiv.trans_target]

/-- The lower biholomorphic parametrization maps onto exactly the lower-cone open. -/
@[simp]
theorem affinePlaneBlowUpLowerPartialDiffeomorph_target (n : ℕ∞ω) :
    (affinePlaneBlowUpLowerPartialDiffeomorph n).target =
      range (affinePlaneBlowUpFan.analyticAffineChartι isRegular_affinePlaneBlowUpFan
        ⟨affinePlaneBlowUpLowerCone,
          mem_affinePlaneBlowUpFan_cones.2 (Or.inl (.refl _))⟩) := by
  simp [affinePlaneBlowUpLowerPartialDiffeomorph, PartialDiffeomorph.trans_toPartialEquiv,
    Diffeomorph.toPartialDiffeomorph_toPartialEquiv, PartialEquiv.trans_target]

/-- The upper partial diffeomorphism is the existing explicit upper affine chart. -/
@[simp]
theorem affinePlaneBlowUpUpperPartialDiffeomorph_apply (n : ℕ∞ω) (z : ℂ × ℂ) :
    affinePlaneBlowUpUpperPartialDiffeomorph n z = affinePlaneBlowUpUpperChart z := by
  rw [affinePlaneBlowUpUpperChart_def]
  simp [affinePlaneBlowUpUpperPartialDiffeomorph, upperPointDiffeomorph,
    PartialDiffeomorph.trans_toPartialEquiv, Diffeomorph.toPartialDiffeomorph_toPartialEquiv,
    PartialEquiv.trans_apply]
  congr

/-- The lower partial diffeomorphism is the existing explicit lower affine chart. -/
@[simp]
theorem affinePlaneBlowUpLowerPartialDiffeomorph_apply (n : ℕ∞ω) (z : ℂ × ℂ) :
    affinePlaneBlowUpLowerPartialDiffeomorph n z = affinePlaneBlowUpLowerChart z := by
  rw [affinePlaneBlowUpLowerChart_def]
  simp [affinePlaneBlowUpLowerPartialDiffeomorph, lowerPointDiffeomorph,
    PartialDiffeomorph.trans_toPartialEquiv, Diffeomorph.toPartialDiffeomorph_toPartialEquiv,
    PartialEquiv.trans_apply]
  congr

/-- The inverse upper coordinate map recovers the coordinates of an upper-chart point. -/
@[simp]
theorem affinePlaneBlowUpUpperPartialDiffeomorph_symm_apply (n : ℕ∞ω) (z : ℂ × ℂ) :
    letI := affinePlaneBlowUpFan.analyticChartedSpace isRegular_affinePlaneBlowUpFan
    (affinePlaneBlowUpUpperPartialDiffeomorph n).toPartialEquiv.symm
      (affinePlaneBlowUpUpperChart z) = z := by
  let _ := affinePlaneBlowUpFan.analyticChartedSpace isRegular_affinePlaneBlowUpFan
  rw [← affinePlaneBlowUpUpperPartialDiffeomorph_apply n z]
  exact (affinePlaneBlowUpUpperPartialDiffeomorph n).left_inv
    (affinePlaneBlowUpUpperPartialDiffeomorph_source n ▸ mem_univ z)

/-- The inverse lower coordinate map recovers the coordinates of a lower-chart point. -/
@[simp]
theorem affinePlaneBlowUpLowerPartialDiffeomorph_symm_apply (n : ℕ∞ω) (z : ℂ × ℂ) :
    letI := affinePlaneBlowUpFan.analyticChartedSpace isRegular_affinePlaneBlowUpFan
    (affinePlaneBlowUpLowerPartialDiffeomorph n).toPartialEquiv.symm
      (affinePlaneBlowUpLowerChart z) = z := by
  let _ := affinePlaneBlowUpFan.analyticChartedSpace isRegular_affinePlaneBlowUpFan
  rw [← affinePlaneBlowUpLowerPartialDiffeomorph_apply n z]
  exact (affinePlaneBlowUpLowerPartialDiffeomorph n).left_inv
    (affinePlaneBlowUpLowerPartialDiffeomorph_source n ▸ mem_univ z)

/-- The upper affine parametrization is a local biholomorphism at every point. -/
theorem isLocalDiffeomorph_affinePlaneBlowUpUpperPartialDiffeomorph (n : ℕ∞ω) :
    letI := affinePlaneBlowUpFan.analyticChartedSpace isRegular_affinePlaneBlowUpFan
    IsLocalDiffeomorph (𝓘(ℂ, ℂ).prod 𝓘(ℂ, ℂ))
      𝓘(ℂ, Fin (Module.finrank ℤ ((Fin 1 → ℤ) × (Fin 1 → ℤ))) → ℂ) n
      (affinePlaneBlowUpUpperPartialDiffeomorph n) := by
  let _ := affinePlaneBlowUpFan.analyticChartedSpace isRegular_affinePlaneBlowUpFan
  intro z
  exact (affinePlaneBlowUpUpperPartialDiffeomorph n).isLocalDiffeomorphAt _ _ _ (by simp)

/-- The lower affine parametrization is a local biholomorphism at every point. -/
theorem isLocalDiffeomorph_affinePlaneBlowUpLowerPartialDiffeomorph (n : ℕ∞ω) :
    letI := affinePlaneBlowUpFan.analyticChartedSpace isRegular_affinePlaneBlowUpFan
    IsLocalDiffeomorph (𝓘(ℂ, ℂ).prod 𝓘(ℂ, ℂ))
      𝓘(ℂ, Fin (Module.finrank ℤ ((Fin 1 → ℤ) × (Fin 1 → ℤ))) → ℂ) n
      (affinePlaneBlowUpLowerPartialDiffeomorph n) := by
  let _ := affinePlaneBlowUpFan.analyticChartedSpace isRegular_affinePlaneBlowUpFan
  intro z
  exact (affinePlaneBlowUpLowerPartialDiffeomorph n).isLocalDiffeomorphAt _ _ _ (by simp)

/-- The two biholomorphic affine parametrizations cover the analytic toric blow-up. -/
theorem affinePlaneBlowUpPartialDiffeomorph_target_cover (n : ℕ∞ω) :
    (affinePlaneBlowUpUpperPartialDiffeomorph n).target ∪
      (affinePlaneBlowUpLowerPartialDiffeomorph n).target = univ := by
  ext x
  simp only [mem_union, affinePlaneBlowUpUpperPartialDiffeomorph_target,
    affinePlaneBlowUpLowerPartialDiffeomorph_target, mem_range, mem_univ, iff_true]
  rcases exists_affinePlaneBlowUpUpperChart_eq_or_exists_affinePlaneBlowUpLowerChart_eq x with
    ⟨z, hz⟩ | ⟨z, hz⟩
  · exact Or.inl ⟨affinePlaneBlowUpUpperPointHomeomorph.symm z,
      affinePlaneBlowUpUpperChart_def z ▸ hz⟩
  · exact Or.inr ⟨affinePlaneBlowUpLowerPointHomeomorph.symm z,
      affinePlaneBlowUpLowerChart_def z ▸ hz⟩

end TauCeti.Toric
