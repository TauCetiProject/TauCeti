/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Toric.Algebraic.Fan.ProjectiveSpace.Proj
public import TauCeti.Geometry.Toric.Analytic.Fan.Comparison.Manifold
public import TauCeti.Geometry.Toric.Analytic.Fan.ProjectiveSpace.Manifold

/-!
# Projective space and the algebraic–analytic toric comparison

Let `b` be an integral basis of `N` indexed by `Fin n`. The toric scheme of the fan of projective
space is identified with `Proj ℂ[X_j]`, the homogeneous coordinates `X_j` indexed by
`j : Option (Fin n)`, by the isomorphism `TauCeti.Toric.Fan.projectiveSpaceToProj` over `Spec ℂ`.
On the analytic side, `TauCeti.Toric.projectiveSpaceHomeomorph` identifies the analytic
realization of the same fan with complex projective space `ℂℙⁿ`, the circle quotient of the unit
sphere, by homogeneous coordinates. Composing with the algebraic–analytic comparison
`TauCeti.Toric.Fan.algebraicAnalyticHomeomorph`, the complex points of the toric scheme, its
morphisms `Spec ℂ ⟶ X` over `Spec ℂ`, are homeomorphic and biholomorphic to `ℂℙⁿ`.

This file shows that the resulting identification respects homogeneous coordinates in the sense
of `Proj`. A complex point `p` of the toric scheme lands, under `projectiveSpaceToProj`, in the
standard open `D₊(X_k)` exactly when `p.1 ≫ projectiveSpaceToProj` is `Spec` of a `ℂ`-algebra
homomorphism `φ` from the ring of `D₊(X_k)`, the degree-zero part of `ℂ[X_j]` localized away from
`X_k`, followed by the inclusion of `D₊(X_k)`. This happens exactly when the corresponding point of
`ℂℙⁿ` lies in the standard affine open where the homogeneous coordinate `k` does not vanish, and
then the homogeneous ratio `X_j / X_k` of that point of `ℂℙⁿ` is the value of `φ` at the fraction
`X_j / X_k`. On the toric side, the locus is the chart of the maximal cone omitting the ray `k`.

Under the correspondence between `Fin (n + 1)` and `Option (Fin n)` given by `finSuccEquiv n`,
the homogeneous coordinate `none` of `Proj` is coordinate `0` of `ℂℙⁿ`.

## Main declarations

* `TauCeti.Toric.Fan.coe_ofAffinePoint_projectiveSpaceMaximalCone_comp_projectiveSpaceToProj`: on
  the chart of the maximal cone omitting `k`, the morphism to `Proj` is the point of `D₊(X_k)`
  given by the chart isomorphism `TauCeti.Toric.projectiveSpaceAwayEquiv`.
* `TauCeti.Toric.Fan.projectiveSpaceAlgebraicComplexPointHomeomorph` and
  `TauCeti.Toric.Fan.projectiveSpaceAlgebraicComplexPointDiffeomorph`: the complex points of the
  toric scheme of the fan of projective space are homeomorphic and biholomorphic to `ℂℙⁿ`.
* `TauCeti.Toric.Fan.projectiveSpaceAlgebraicComplexPointHomeomorph_mem_affineOpen_iff`: the
  standard affine open `X_k ≠ 0` of `ℂℙⁿ` consists of the complex points whose image in `Proj`
  lies in `D₊(X_k)`.
* `TauCeti.Toric.Fan.ratio_projectiveSpaceAlgebraicComplexPointHomeomorph_of_comp_eq`: the
  homogeneous ratios of the point of `ℂℙⁿ` are the values of the corresponding point of `D₊(X_k)`
  at the fractions `X_j / X_k`.

## References

* W. Fulton, *Introduction to Toric Varieties*, §§1.4 and 2.1.
* D. Cox, J. Little and H. Schenck, *Toric Varieties*, §§3.1 and 3.4.
* R. Hartshorne, *Algebraic Geometry*, GTM 52, Springer, 1977, Proposition II.2.5.
-/

public section

open AlgebraicGeometry CategoryTheory HomogeneousLocalization
open scoped ContDiff Manifold

namespace TauCeti.Toric.Fan

variable {N V : Type} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {n : ℕ} (b : Module.Basis (Fin n) ℤ N) {i : N →+ V} (hi : IsIntegralLattice i)

local notation "𝒜" => SymmetricAlgebra.homogeneousSubmodule ℂ (Option (Fin n) → ℂ)
local notation "X" j => _root_.SymmetricAlgebra.ι ℂ (Option (Fin n) → ℂ) (Pi.single j 1)

open AlgebraicComplexPoint

/-! ### Complex points of the charts in `Proj` -/

/-- On the chart of the maximal cone omitting `k`, the complex point of a chart point `x`, followed
by the isomorphism to `Proj`, is the complex point of the standard open `D₊(X_k)` whose value at a
fraction `a / X_kᵈ` is the value of `x` at the homogeneous polynomial `a` evaluated at the
homogeneous coordinates with `X_k = 1`. -/
theorem coe_ofAffinePoint_projectiveSpaceMaximalCone_comp_projectiveSpaceToProj
    (k : Option (Fin n))
    (x : AffineSemigroupComplexPoint (dualSemigroup hi (projectiveSpaceCone b i {k}ᶜ))) :
    (ofAffinePoint (projectiveSpaceMaximalCone b hi k) x).1 ≫ projectiveSpaceToProj b hi =
      Spec.map (CommRingCat.ofHom
          (x.comp (projectiveSpaceAwayEquiv b hi k).toAlgHom).toRingHom) ≫
        Proj.awayι 𝒜 (X k) (SymmetricAlgebra.ι_mem_homogeneousSubmodule ℂ _ _) one_pos := by
  rw [coe_ofAffinePoint, Category.assoc,
    affineToricChartι_comp_projectiveSpaceToProj (projectiveSpaceMaximalCone b hi k) le_rfl,
    projectiveSpaceChartToProj_self, ← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  -- The two ring homomorphisms agree by `AlgHom.comp_toRingHom`, which holds by definition; the
  -- coercion of `projectiveSpaceAwayEquiv` appears here as `AlgHom.toRingHom`, so `rw` cannot
  -- match that lemma.
  rfl

/-- A complex point of the toric scheme of the fan of projective space whose image in `Proj` is
the complex point of `D₊(X_k)` given by `φ` is the point of the chart of the maximal cone omitting
`k` corresponding to `φ` under the chart isomorphism `projectiveSpaceAwayEquiv`. -/
theorem eq_ofAffinePoint_of_comp_projectiveSpaceToProj_eq
    {p : (projectiveSpace b hi).AlgebraicComplexPoint} {k : Option (Fin n)}
    (φ : Away 𝒜 (X k) →ₐ[ℂ] ℂ)
    (h : p.1 ≫ projectiveSpaceToProj b hi =
      Spec.map (CommRingCat.ofHom φ.toRingHom) ≫
        Proj.awayι 𝒜 (X k) (SymmetricAlgebra.ι_mem_homogeneousSubmodule ℂ _ _) one_pos) :
    p = ofAffinePoint (projectiveSpaceMaximalCone b hi k)
      (φ.comp (projectiveSpaceAwayEquiv b hi k).symm.toAlgHom) := by
  refine Subtype.ext ((cancel_mono (projectiveSpaceToProj b hi)).1 ?_)
  rw [h, coe_ofAffinePoint_projectiveSpaceMaximalCone_comp_projectiveSpaceToProj,
    AlgHom.comp_assoc, AlgEquiv.symm_comp, AlgHom.comp_id]

/-- A complex point of the toric scheme of the fan of projective space lies in the chart of the
maximal cone omitting `k` exactly when its image in `Proj` is a complex point of `D₊(X_k)`. -/
theorem mem_range_ofAffinePoint_projectiveSpaceMaximalCone_iff
    (p : (projectiveSpace b hi).AlgebraicComplexPoint) (k : Option (Fin n)) :
    p ∈ Set.range (ofAffinePoint (projectiveSpaceMaximalCone b hi k)) ↔
      ∃ φ : Away 𝒜 (X k) →ₐ[ℂ] ℂ, p.1 ≫ projectiveSpaceToProj b hi =
        Spec.map (CommRingCat.ofHom φ.toRingHom) ≫
          Proj.awayι 𝒜 (X k) (SymmetricAlgebra.ι_mem_homogeneousSubmodule ℂ _ _) one_pos := by
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨_, coe_ofAffinePoint_projectiveSpaceMaximalCone_comp_projectiveSpaceToProj b hi k x⟩
  · rintro ⟨φ, h⟩
    exact ⟨_, (eq_ofAffinePoint_of_comp_projectiveSpaceToProj_eq b hi φ h).symm⟩

/-! ### The comparison with complex projective space -/

/-- The complex points of the toric scheme of the fan of projective space are homeomorphic to
complex projective space, through the algebraic–analytic comparison and the homogeneous
coordinates of the analytic realization. -/
noncomputable def projectiveSpaceAlgebraicComplexPointHomeomorph :
    (projectiveSpace b hi).AlgebraicComplexPoint ≃ₜ ComplexProjectiveSpace n :=
  (algebraicAnalyticHomeomorph (isRegular_projectiveSpace b hi)).trans
    (projectiveSpaceHomeomorph b hi)

/-- The homeomorphism is the algebraic–analytic comparison followed by the homogeneous
coordinates of the analytic realization. -/
theorem projectiveSpaceAlgebraicComplexPointHomeomorph_apply
    (p : (projectiveSpace b hi).AlgebraicComplexPoint) :
    projectiveSpaceAlgebraicComplexPointHomeomorph b hi p =
      projectiveSpaceHomeomorph b hi
        (algebraicAnalyticEquiv (isRegular_projectiveSpace b hi) p) := by
  rw [projectiveSpaceAlgebraicComplexPointHomeomorph, Homeomorph.trans_apply,
    coe_algebraicAnalyticHomeomorph]

/-- On the chart of the maximal cone omitting `k`, the homogeneous ratio `X_j / X_k` of the point
of `ℂℙⁿ` corresponding to a chart point `x` is the value of `x` at the monomial of the ratio. -/
@[simp]
theorem ratio_projectiveSpaceAlgebraicComplexPointHomeomorph_ofAffinePoint (k : Option (Fin n))
    (x : AffineSemigroupComplexPoint (dualSemigroup hi (projectiveSpaceCone b i {k}ᶜ)))
    (j : Fin (n + 1)) :
    ComplexProjectiveSpace.ratio ((finSuccEquiv n).symm k) j
        (projectiveSpaceAlgebraicComplexPointHomeomorph b hi
          (ofAffinePoint (projectiveSpaceMaximalCone b hi k) x)) =
      x (projectiveSpaceRatioMonomial b hi le_rfl (finSuccEquiv n j)) := by
  have hx : algebraicAnalyticEquiv (isRegular_projectiveSpace b hi)
      (ofAffinePoint (projectiveSpaceMaximalCone b hi k) x) =
        (projectiveSpace b hi).analyticAffineChartι (isRegular_projectiveSpace b hi)
          (projectiveSpaceMaximalCone b hi k) x :=
    algebraicAnalyticEquiv_ofAffinePoint (isRegular_projectiveSpace b hi)
      (projectiveSpaceMaximalCone b hi k) x
  rw [projectiveSpaceAlgebraicComplexPointHomeomorph_apply, hx,
    ratio_projectiveSpaceHomeomorph_analyticAffineChartι, projectiveSpaceHomogeneousCoordinate_def,
    projectiveSpaceRatioMonomial_def]

/-- The standard affine open of `ℂℙⁿ` where the homogeneous coordinate `k` does not vanish
corresponds to the chart of the maximal cone omitting the ray `k`. -/
theorem preimage_projectiveSpaceAlgebraicComplexPointHomeomorph_affineOpen (k : Option (Fin n)) :
    projectiveSpaceAlgebraicComplexPointHomeomorph b hi ⁻¹'
        ComplexProjectiveSpace.affineOpen ((finSuccEquiv n).symm k) =
      Set.range (ofAffinePoint (projectiveSpaceMaximalCone b hi k)) := by
  ext p
  rw [Set.mem_preimage, projectiveSpaceAlgebraicComplexPointHomeomorph_apply, ← Set.mem_preimage,
    preimage_projectiveSpaceHomeomorph_affineOpen]
  constructor
  · rintro ⟨x, hx⟩
    refine ⟨x, ?_⟩
    rw [← algebraicAnalyticEquiv_symm_analyticAffineChartι (isRegular_projectiveSpace b hi), hx,
      Equiv.symm_apply_apply]
  · rintro ⟨x, rfl⟩
    exact ⟨x, (algebraicAnalyticEquiv_ofAffinePoint (isRegular_projectiveSpace b hi)
      (projectiveSpaceMaximalCone b hi k) x).symm⟩

/-- **The standard affine opens agree.** A complex point of the toric scheme of the fan of
projective space corresponds to a point of `ℂℙⁿ` whose homogeneous coordinate `k` does not vanish
exactly when its image in `Proj` is a complex point of the standard open `D₊(X_k)`. -/
theorem projectiveSpaceAlgebraicComplexPointHomeomorph_mem_affineOpen_iff
    (p : (projectiveSpace b hi).AlgebraicComplexPoint) (k : Option (Fin n)) :
    projectiveSpaceAlgebraicComplexPointHomeomorph b hi p ∈
        ComplexProjectiveSpace.affineOpen ((finSuccEquiv n).symm k) ↔
      ∃ φ : Away 𝒜 (X k) →ₐ[ℂ] ℂ, p.1 ≫ projectiveSpaceToProj b hi =
        Spec.map (CommRingCat.ofHom φ.toRingHom) ≫
          Proj.awayι 𝒜 (X k) (SymmetricAlgebra.ι_mem_homogeneousSubmodule ℂ _ _) one_pos := by
  rw [← Set.mem_preimage, preimage_projectiveSpaceAlgebraicComplexPointHomeomorph_affineOpen,
    mem_range_ofAffinePoint_projectiveSpaceMaximalCone_iff]

/-- **The comparison respects homogeneous coordinates.** If the image in `Proj` of a complex point
of the toric scheme of the fan of projective space is the complex point of `D₊(X_k)` given by `φ`,
then the homogeneous ratio `X_j / X_k` of the corresponding point of `ℂℙⁿ` is the value of `φ` at
the fraction `X_j / X_k`. -/
theorem ratio_projectiveSpaceAlgebraicComplexPointHomeomorph_of_comp_eq
    {p : (projectiveSpace b hi).AlgebraicComplexPoint} {k : Option (Fin n)}
    (φ : Away 𝒜 (X k) →ₐ[ℂ] ℂ)
    (h : p.1 ≫ projectiveSpaceToProj b hi =
      Spec.map (CommRingCat.ofHom φ.toRingHom) ≫
        Proj.awayι 𝒜 (X k) (SymmetricAlgebra.ι_mem_homogeneousSubmodule ℂ _ _) one_pos)
    (j : Fin (n + 1)) :
    ComplexProjectiveSpace.ratio ((finSuccEquiv n).symm k) j
        (projectiveSpaceAlgebraicComplexPointHomeomorph b hi p) =
      φ (Away.mk 𝒜 (SymmetricAlgebra.ι_mem_homogeneousSubmodule ℂ _ _) 1 (X (finSuccEquiv n j))
        (by simp)) := by
  rw [eq_ofAffinePoint_of_comp_projectiveSpaceToProj_eq b hi φ h,
    ratio_projectiveSpaceAlgebraicComplexPointHomeomorph_ofAffinePoint, AlgHom.comp_apply,
    AlgEquiv.coe_toAlgHom, projectiveSpaceAwayEquiv_symm_projectiveSpaceRatioMonomial]

/-- The complex points of the toric scheme of the fan of projective space are biholomorphic to
complex projective space, for the complex structure pulled back from the analytic realization and
the homogeneous-ratio atlas of `ℂℙⁿ`, at every smoothness order. -/
noncomputable def projectiveSpaceAlgebraicComplexPointDiffeomorph (r : ℕ∞ω) :
    letI := algebraicComplexPointChartedSpace (isRegular_projectiveSpace b hi)
    (projectiveSpace b hi).AlgebraicComplexPoint ≃ₘ^r⟮𝓘(ℂ, Fin (Module.finrank ℤ N) → ℂ),
      𝓘(ℂ, Fin n → ℂ)⟯ ComplexProjectiveSpace n :=
  letI := (projectiveSpace b hi).analyticChartedSpace (isRegular_projectiveSpace b hi)
  letI := algebraicComplexPointChartedSpace (isRegular_projectiveSpace b hi)
  (algebraicAnalyticDiffeomorph (isRegular_projectiveSpace b hi) r).trans
    (projectiveSpaceDiffeomorph b hi r)

/-- The biholomorphism is the homeomorphism `projectiveSpaceAlgebraicComplexPointHomeomorph`. -/
@[simp]
theorem coe_projectiveSpaceAlgebraicComplexPointDiffeomorph (r : ℕ∞ω) :
    letI := algebraicComplexPointChartedSpace (isRegular_projectiveSpace b hi)
    ⇑(projectiveSpaceAlgebraicComplexPointDiffeomorph b hi r) =
      projectiveSpaceAlgebraicComplexPointHomeomorph b hi := by
  let := (projectiveSpace b hi).analyticChartedSpace (isRegular_projectiveSpace b hi)
  let := algebraicComplexPointChartedSpace (isRegular_projectiveSpace b hi)
  funext p
  rw [projectiveSpaceAlgebraicComplexPointDiffeomorph, Diffeomorph.coe_trans, Function.comp_apply,
    coe_algebraicAnalyticDiffeomorph, coe_projectiveSpaceDiffeomorph,
    projectiveSpaceAlgebraicComplexPointHomeomorph_apply]

end TauCeti.Toric.Fan
