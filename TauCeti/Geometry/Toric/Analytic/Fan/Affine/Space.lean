/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Toric.Algebraic.Fan.AffineSpace.Basic
public import TauCeti.Geometry.Toric.Analytic.Fan.Affine.Basic
public import TauCeti.Geometry.Toric.Analytic.Fan.Character
public import TauCeti.Geometry.Toric.Analytic.Fan.ProjectiveSpace.Charts

/-!
# The analytic realization of affine space

For an integral basis `b` indexed by a finite type `ι`, the analytic realization of the fan of
affine space is complex affine space `ι → ℂ`. The coordinate indexed by `j` is the holomorphic
character function of the coordinate character `b.coord j`, and in these coordinates every
character monomial is the ordinary monomial whose exponents are its pairings with the basis
vectors. The identification is a biholomorphism, for the complex structure glued from the
affine charts of the fan, and torus translation scales each coordinate by the corresponding
character value.

The comparison factors through the maximal affine chart of the orthant, whose coordinates are
the homogeneous ratios of the corresponding chart of projective space.

## Main declarations

* `TauCeti.Toric.Fan.affineSpaceHomeomorph`: the analytic realization of the fan of affine space
  is homeomorphic to `ι → ℂ`, with the character functions of `b.coord j` as coordinates.
* `TauCeti.Toric.Fan.analyticCharacter_affineSpaceHomeomorph_symm`: in these coordinates,
  character functions are ordinary monomials.
* `TauCeti.Toric.Fan.affineSpaceHomeomorph_smul`: the torus acts by scaling coordinates.
* `TauCeti.Toric.Fan.affineSpaceDiffeomorph`: the identification is a biholomorphism.

## References

* W. Fulton, *Introduction to Toric Varieties*, §§1.1, 1.3 and 1.4.
* D. Cox, J. Little and H. Schenck, *Toric Varieties*, §§1.2 and 3.1.
-/

public section

open Multiplicative Set
open scoped ContDiff Manifold

namespace TauCeti.Toric.Fan

universe u

variable {N V : Type u} {ι : Type*} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  [Fintype ι] (b : Module.Basis ι ℤ N) {i : N →+ V} (hi : IsIntegralLattice i)

include hi in
private theorem isRegularCone_orthant : IsRegularCone i (projectiveSpaceCone b i {none}ᶜ) :=
  isRegularCone_projectiveSpaceCone b hi (by simp)

/-- The coordinates of the chart of the orthant, as homogeneous ratios `X_j / X_none`. -/
private noncomputable abbrev orthantCoordinates :
    (affineSpace b hi).analyticAffineChartDiagram.obj (affineSpaceMaximalCone b hi) ≃ₜ
      ({k : Option ι // k ≠ none} → ℂ) :=
  projectiveSpacePointHomeomorph b hi none ((affineSpace b hi).analyticChartGenerators
    (affineSpaceMaximalCone b hi)).2

open Classical in
variable (ι) in
/-- The coordinates of the orthant chart, indexed by `{k : Option ι // k ≠ none}`, are indexed
by `ι`. -/
private noncomputable abbrev orthantIndexEquiv : ι ≃ {k : Option ι // k ≠ none} :=
  Equiv.optionSubtype none ⟨Equiv.refl (Option ι), rfl⟩

open Classical in
/-- The analytic realization of the fan of affine space is homeomorphic to `ι → ℂ`. The
coordinate indexed by `j` is the character function of `b.coord j`, by
`affineSpaceHomeomorph_apply`. -/
noncomputable def affineSpaceHomeomorph :
    (affineSpace b hi).analyticRealization (isRegular_affineSpace b hi) ≃ₜ (ι → ℂ) :=
  ((analyticOfConeHomeomorph hi (isRegularCone_orthant b hi)).symm.trans
    (orthantCoordinates b hi)).trans
    (Homeomorph.piCongrLeft (Y := fun _ ↦ ℂ) (orthantIndexEquiv ι)).symm

private theorem affineSpaceHomeomorph_analyticAffineChartι
    (x : (affineSpace b hi).analyticAffineChartDiagram.obj (affineSpaceMaximalCone b hi)) (j : ι) :
    affineSpaceHomeomorph b hi
        ((affineSpace b hi).analyticAffineChartι (isRegular_affineSpace b hi)
          (affineSpaceMaximalCone b hi) x) j =
      DFunLike.coe (F := AffineSemigroupComplexPoint
          (dualSemigroup hi (projectiveSpaceCone b i {none}ᶜ))) x
        (MonoidAlgebra.single (ofAdd (projectiveSpaceChartCharacter b hi none
          ⟨some j, Option.some_ne_none j⟩)) 1) := by
  have h := (analyticOfConeHomeomorph hi (isRegularCone_orthant b hi)).symm_apply_apply x
  rw [analyticOfConeHomeomorph_apply] at h
  rw [affineSpaceHomeomorph, Homeomorph.trans_apply, Homeomorph.trans_apply, h,
    Homeomorph.piCongrLeft_symm_apply]
  exact projectiveSpacePointHomeomorph_apply b hi none _ x _

open Classical in
/-- The inverse of `affineSpaceHomeomorph`, through the maximal affine chart of the orthant. -/
private theorem affineSpaceHomeomorph_symm_apply (z : ι → ℂ) :
    (affineSpaceHomeomorph b hi).symm z =
      (affineSpace b hi).analyticAffineChartι (isRegular_affineSpace b hi)
        (affineSpaceMaximalCone b hi)
        ((orthantCoordinates b hi).symm fun k ↦ z ((orthantIndexEquiv ι).symm k)) := by
  rw [affineSpaceHomeomorph, Homeomorph.symm_trans_apply, Homeomorph.symm_trans_apply,
    Homeomorph.symm_symm, analyticOfConeHomeomorph_apply]
  congr 2
  funext k
  obtain ⟨j, rfl⟩ := (orthantIndexEquiv ι).surjective k
  simp [Homeomorph.piCongrLeft_apply_apply]

/-- The coordinates of the analytic realization of the fan of affine space are the character
functions of the coordinate characters `b.coord j`. -/
@[simp]
theorem affineSpaceHomeomorph_apply
    (x : (affineSpace b hi).analyticRealization (isRegular_affineSpace b hi)) (j : ι) :
    affineSpaceHomeomorph b hi x j =
      (affineSpace b hi).analyticCharacter (isRegular_affineSpace b hi)
        (b.coord j).toAddMonoidHom (coord_mem_dualSemigroup_affineSpace b hi j) x := by
  obtain ⟨y, rfl⟩ := analyticAffineChartι_ofCone_surjective hi (isRegularCone_orthant b hi) x
  refine (affineSpaceHomeomorph_analyticAffineChartι b hi y j).trans ?_
  rw [analyticCharacter_analyticAffineChartι]
  congr 3
  exact Subtype.ext (by simp)

/-- In the coordinates of `affineSpaceHomeomorph`, the character function of a character
nonnegative on the orthant is the ordinary monomial whose exponents are the pairings of the
character with the basis vectors. -/
theorem analyticCharacter_affineSpaceHomeomorph_symm (m : IntegralCharacter N)
    (hm : ∀ σ : (affineSpace b hi).cones, m ∈ dualSemigroup (affineSpace b hi).lattice σ.1)
    (z : ι → ℂ) :
    (affineSpace b hi).analyticCharacter (isRegular_affineSpace b hi) m hm
        ((affineSpaceHomeomorph b hi).symm z) =
      ∏ j, z j ^ (m (b j)).toNat := by
  classical
  rw [affineSpaceHomeomorph_symm_apply, analyticCharacter_analyticAffineChartι]
  refine (projectiveSpacePointHomeomorph_symm_apply_single b hi none _ _ _).trans ?_
  exact (Fintype.prod_equiv (orthantIndexEquiv ι) _ _ fun j ↦ by simp).symm

/-- Torus translation scales each coordinate of affine space by the corresponding character
value. -/
theorem affineSpaceHomeomorph_smul (t : ComplexTorus N)
    (x : (affineSpace b hi).analyticRealization (isRegular_affineSpace b hi)) (j : ι) :
    affineSpaceHomeomorph b hi (t • x) j =
      (t (b.coord j).toAddMonoidHom : ℂ) * affineSpaceHomeomorph b hi x j := by
  simp only [affineSpaceHomeomorph_apply, analyticCharacter_smul]

/-- The identification of affine space with `ι → ℂ` is holomorphic: its coordinates are
holomorphic character functions. -/
theorem contMDiff_affineSpaceHomeomorph (n : ℕ∞ω) :
    let _ := (affineSpace b hi).analyticChartedSpace (isRegular_affineSpace b hi)
    ContMDiff 𝓘(ℂ, Fin (Module.finrank ℤ N) → ℂ) 𝓘(ℂ, ι → ℂ) n (affineSpaceHomeomorph b hi) := by
  intro _
  rw [contMDiff_pi_module_iff]
  intro j
  exact ((affineSpace b hi).contMDiff_analyticCharacter (isRegular_affineSpace b hi) _
    (coord_mem_dualSemigroup_affineSpace b hi j) n).congr fun x ↦
      affineSpaceHomeomorph_apply b hi x j

/-- The inverse of the identification of affine space with `ι → ℂ` is holomorphic. -/
theorem contMDiff_affineSpaceHomeomorph_symm (n : ℕ∞ω) :
    let _ := (affineSpace b hi).analyticChartedSpace (isRegular_affineSpace b hi)
    ContMDiff 𝓘(ℂ, ι → ℂ) 𝓘(ℂ, Fin (Module.finrank ℤ N) → ℂ) n
      (affineSpaceHomeomorph b hi).symm := by
  intro _
  classical
  obtain ⟨l, B, hB⟩ := (isRegularCone_orthant b hi).exists_basis_sum
  have : Finite (ToricRay (projectiveSpaceCone b i {none}ᶜ)) :=
    ToricRay.finite_of_fg (isRegularCone_orthant b hi).fg
  let κ := Finite.equivFin (ToricRay (projectiveSpaceCone b i {none}ᶜ))
  let g := ((affineSpace b hi).analyticChartGenerators (affineSpaceMaximalCone b hi)).2
  let _ := affinePointTopology g
  let _ := coneChartedSpace hi (isRegularCone_orthant b hi).toIsToricCone hB κ g
  have hre : ContMDiff 𝓘(ℂ, ι → ℂ) 𝓘(ℂ, {k : Option ι // k ≠ none} → ℂ) n
      fun (z : ι → ℂ) (k : {k : Option ι // k ≠ none}) ↦
        z ((orthantIndexEquiv ι).symm k) :=
    contMDiff_pi_module_iff.2 fun k ↦ (contDiff_apply ℂ (fun _ : ι ↦ ℂ) _).contMDiff
  refine ((analyticOfConeDiffeomorph hi (isRegularCone_orthant b hi) hB κ g n).contMDiff.comp
    ((projectiveSpacePointDiffeomorph b hi none hB κ g n).symm.contMDiff.comp hre)).congr
      fun z ↦ ?_
  rw [Function.comp_apply, Function.comp_apply, analyticOfConeDiffeomorph_apply,
    affineSpaceHomeomorph_symm_apply, ← Diffeomorph.coe_toHomeomorph_symm,
    projectiveSpacePointDiffeomorph_toHomeomorph]
  -- Closes definitionally: `affineSpace` and `affineSpaceMaximalCone` are abbrevs for `ofCone`
  -- and its maximal cone, and `orthantCoordinates` is `projectiveSpacePointHomeomorph b hi none g`,
  -- whose inverse has the same underlying function under `affinePointTopology g` as under the
  -- chart topology.
  rfl

/-- The analytic realization of the fan of affine space is biholomorphic to `ι → ℂ`, for the
complex structure glued from its affine charts. The underlying homeomorphism is
`affineSpaceHomeomorph`. -/
noncomputable def affineSpaceDiffeomorph (n : ℕ∞ω) :
    let _ := (affineSpace b hi).analyticChartedSpace (isRegular_affineSpace b hi)
    Diffeomorph 𝓘(ℂ, Fin (Module.finrank ℤ N) → ℂ) 𝓘(ℂ, ι → ℂ)
      ((affineSpace b hi).analyticRealization (isRegular_affineSpace b hi)) (ι → ℂ) n :=
  let _ := (affineSpace b hi).analyticChartedSpace (isRegular_affineSpace b hi)
  { toEquiv := (affineSpaceHomeomorph b hi).toEquiv
    contMDiff_toFun := contMDiff_affineSpaceHomeomorph b hi n
    contMDiff_invFun := contMDiff_affineSpaceHomeomorph_symm b hi n }

/-- The affine-space biholomorphism has `affineSpaceHomeomorph` as its underlying
homeomorphism. -/
@[simp]
theorem affineSpaceDiffeomorph_toHomeomorph (n : ℕ∞ω) :
    let _ := (affineSpace b hi).analyticChartedSpace (isRegular_affineSpace b hi)
    (affineSpaceDiffeomorph b hi n).toHomeomorph = affineSpaceHomeomorph b hi := by
  let _ := (affineSpace b hi).analyticChartedSpace (isRegular_affineSpace b hi)
  rfl

/-- The affine-space biholomorphism is `affineSpaceHomeomorph`. -/
@[simp]
theorem affineSpaceDiffeomorph_apply (n : ℕ∞ω)
    (x : (affineSpace b hi).analyticRealization (isRegular_affineSpace b hi)) :
    affineSpaceDiffeomorph b hi n x = affineSpaceHomeomorph b hi x := by
  let _ := (affineSpace b hi).analyticChartedSpace (isRegular_affineSpace b hi)
  rfl

end TauCeti.Toric.Fan
