/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Toric.Algebraic.Fan.ProjectiveSpace.Coordinates
public import TauCeti.Geometry.Toric.Analytic.Cone.Manifold
public import Mathlib.Geometry.Manifold.Diffeomorph

/-!
# Homogeneous coordinates on affine charts of toric projective space

The maximal cone omitting the ray `k` has a complex-point chart homeomorphic to `ℂ^n`.
The coordinate indexed by `j ≠ k` is evaluation of the character of `X_j / X_k`.
Conversely every character monomial is the product of these coordinates with exponents given
by its pairings with the rays. This description holds on the whole affine chart, including
its coordinate hyperplanes, and for any finite semigroup generating family. The identification
is biholomorphic for the cone complex structure of any extending basis.

These explicit affine coordinates are needed to compare the gluing of the projective-space fan
with the usual homogeneous-coordinate construction of complex projective space.

The homeomorphisms specialize `TauCeti.Toric.regularAffinePointHomeomorph` using the explicit
homogeneous-coordinate splitting of the dual semigroup.

## References

* W. Fulton, *Introduction to Toric Varieties*, §1.4.
* D. Cox, J. Little and H. Schenck, *Toric Varieties*, §§3.1 and 3.4.
-/

public section

open Multiplicative Set
open scoped ContDiff Manifold

namespace TauCeti.Toric

variable {N V ι : Type*} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  [Fintype ι] (b : Module.Basis ι ℤ N) {i : N →+ V} (hi : IsIntegralLattice i)

private noncomputable def projectiveSpaceMixedSemigroupEquiv (k : Option ι) :
    dualSemigroup hi (projectiveSpaceCone b i {k}ᶜ) ≃+
      (({j : Option ι // j ≠ k} →₀ ℕ) × (PEmpty.{1} →₀ ℤ)) :=
  ((projectiveSpaceDualSemigroupEquiv b hi k).trans
    (Finsupp.linearEquivFunOnFinite ℕ ℕ _).toAddEquiv.symm).trans AddEquiv.prodUnique.symm

private theorem projectiveSpaceMixedSemigroupEquiv_chartCharacter (k : Option ι)
    (j : {j : Option ι // j ≠ k}) :
    projectiveSpaceMixedSemigroupEquiv b hi k (projectiveSpaceChartCharacter b hi k j) =
      (Finsupp.single j 1, 0) := by
  classical
  simp [projectiveSpaceMixedSemigroupEquiv]

/-- The complex-point chart omitting the ray `k`, in the homogeneous ratios `X_j / X_k`.
The topology may be defined using any finite generating family of its dual semigroup. -/
noncomputable def projectiveSpacePointHomeomorph (k : Option ι) {r : ℕ}
    (g : AddGeneratingFamily (dualSemigroup hi (projectiveSpaceCone b i {k}ᶜ)) r) :
    @Homeomorph (AffineSemigroupComplexPoint (dualSemigroup hi (projectiveSpaceCone b i {k}ᶜ)))
      ({j : Option ι // j ≠ k} → ℂ) (affinePointTopology g) inferInstance := by
  let _ := affinePointTopology g
  exact (regularAffinePointHomeomorph g (projectiveSpaceMixedSemigroupEquiv b hi k)).trans
    (Homeomorph.prodUnique _ (PEmpty.{1} → ℂˣ))

/-- Each affine coordinate evaluates the monomial of the corresponding homogeneous ratio. -/
@[simp]
theorem projectiveSpacePointHomeomorph_apply (k : Option ι) {r : ℕ}
    (g : AddGeneratingFamily (dualSemigroup hi (projectiveSpaceCone b i {k}ᶜ)) r)
    (x : AffineSemigroupComplexPoint (dualSemigroup hi (projectiveSpaceCone b i {k}ᶜ)))
    (j : {j : Option ι // j ≠ k}) :
    projectiveSpacePointHomeomorph b hi k g x j =
      x (MonoidAlgebra.single (ofAdd (projectiveSpaceChartCharacter b hi k j)) 1) := by
  have hj := projectiveSpaceMixedSemigroupEquiv_chartCharacter b hi k j
  have hinv := (projectiveSpaceMixedSemigroupEquiv b hi k).symm_apply_apply
    (projectiveSpaceChartCharacter b hi k j)
  rw [hj] at hinv
  simp only [projectiveSpacePointHomeomorph, Homeomorph.trans_apply, Homeomorph.coe_prodUnique,
    coe_regularAffinePointHomeomorph, regularAffinePointEquiv_fst_apply, hinv]

open Classical in
/-- The point with prescribed homogeneous ratios evaluates every character by the associated
ordinary monomial. All exponents are nonnegative; coordinates may vanish. -/
@[simp]
theorem projectiveSpacePointHomeomorph_symm_apply_single (k : Option ι) {r : ℕ}
    (g : AddGeneratingFamily (dualSemigroup hi (projectiveSpaceCone b i {k}ᶜ)) r)
    (z : {j : Option ι // j ≠ k} → ℂ)
    (m : dualSemigroup hi (projectiveSpaceCone b i {k}ᶜ)) :
    let _ := affinePointTopology g
    (projectiveSpacePointHomeomorph b hi k g).symm z (MonoidAlgebra.single (ofAdd m) 1) =
      ∏ j : {j : Option ι // j ≠ k}, z j ^ ((m : N →+ ℤ) (projectiveSpaceGenerator b j)).toNat := by
  classical
  let _ := affinePointTopology g
  simp only [projectiveSpacePointHomeomorph, Homeomorph.symm_trans_apply,
    coe_regularAffinePointHomeomorph_symm, regularAffinePointEquiv_symm_apply_single]
  have hz := (Homeomorph.prodUnique ({j : Option ι // j ≠ k} → ℂ)
    (PEmpty.{1} → ℂˣ)).symm_apply_apply (z, default)
  rw [Homeomorph.coe_prodUnique] at hz
  rw [hz]
  simp [projectiveSpaceMixedSemigroupEquiv, Finsupp.prod_fintype]

section Manifold

variable (k : Option ι) {p q r : ℕ}
  {B : Module.Basis (ToricRay (projectiveSpaceCone b i {k}ᶜ) ⊕ Fin q) ℤ N}
  (hB : ∀ ρ, IsPrimitiveGenerator i ρ (B (Sum.inl ρ)))
  (κ : ToricRay (projectiveSpaceCone b i {k}ᶜ) ≃ Fin p)
  (g : AddGeneratingFamily (dualSemigroup hi (projectiveSpaceCone b i {k}ᶜ)) r)

open Classical in
/-- Homogeneous ratios identify the maximal affine chart biholomorphically with complex affine
space, for the regular-cone complex structure of any extending integral basis. -/
noncomputable def projectiveSpacePointDiffeomorph (n : ℕ∞ω) :
    let _ := affinePointTopology g
    let _ := coneChartedSpace hi
      (isRegularCone_projectiveSpaceCone b hi (by simp)).toIsToricCone hB κ g
    Diffeomorph 𝓘(ℂ, (Fin p → ℂ) × (Fin q → ℂ))
      𝓘(ℂ, {j : Option ι // j ≠ k} → ℂ)
      (AffineSemigroupComplexPoint (dualSemigroup hi (projectiveSpaceCone b i {k}ᶜ)))
      ({j : Option ι // j ≠ k} → ℂ) n := by
  let _ := affinePointTopology g
  let hσ := (isRegularCone_projectiveSpaceCone b hi (by simp : {k}ᶜ ≠ univ)).toIsToricCone
  let _ := coneChartedSpace hi hσ hB κ g
  refine ⟨(projectiveSpacePointHomeomorph b hi k g).toEquiv, ?_, ?_⟩
  · rw [contMDiff_pi_module_iff]
    intro j
    exact (contMDiff_apply_single hi hσ hB κ g
      (projectiveSpaceChartCharacter b hi k j) n).congr fun x ↦
        projectiveSpacePointHomeomorph_apply b hi k g x j
  · apply (contMDiff_iff_forall_contMDiff_apply_single hi hσ hB κ g).2
    intro m
    simp only [Homeomorph.coe_symm_toEquiv, projectiveSpacePointHomeomorph_symm_apply_single]
    exact (contDiff_prod fun j _ ↦ (contDiff_apply ℂ (fun _ ↦ ℂ) j).pow _).contMDiff

open Classical in
/-- The biholomorphic homogeneous-coordinate chart has the specified underlying homeomorphism. -/
@[simp]
theorem projectiveSpacePointDiffeomorph_toHomeomorph (n : ℕ∞ω) :
    let _ := affinePointTopology g
    let _ := coneChartedSpace hi
      (isRegularCone_projectiveSpaceCone b hi (by simp)).toIsToricCone hB κ g
    (projectiveSpacePointDiffeomorph b hi k hB κ g n).toHomeomorph =
      projectiveSpacePointHomeomorph b hi k g := by
  let _ := affinePointTopology g
  let _ := coneChartedSpace hi
    (isRegularCone_projectiveSpaceCone b hi (by simp)).toIsToricCone hB κ g
  rfl

end Manifold

end TauCeti.Toric
