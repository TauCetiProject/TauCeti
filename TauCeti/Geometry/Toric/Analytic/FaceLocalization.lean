/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Toric.Algebraic.FaceLocalization
public import TauCeti.Geometry.Toric.Analytic.AffinePoint

/-!
# Complex points of toric face localizations

A face inclusion `τ ≼ σ` restricts integral characters from the dual semigroup of `σ` to that
of `τ`.  Precomposition with the resulting coordinate-ring map sends a complex point of the
affine chart of `τ` to one of the affine chart of `σ`.  This is the same coordinate-ring map whose
spectrum defines the algebraic face morphism.  The comparison with morphisms from `Spec ℂ` is not
formalized here.

When `σ` is regular, every face is cut out by one character `m`.  The coordinate ring of the face
is the localization of the coordinate ring of `σ` away from the monomial of `m`; consequently its
complex points identify with the open locus where that monomial does not vanish.  This file makes
that identification topological for the generator-independent monomial-embedding topologies.  It
is the open-subspace input for gluing regular affine toric charts.

## Main declarations

* `TauCeti.Toric.faceAffinePointMap`: the complex-point map of a face inclusion, with
  `TauCeti.Toric.faceAffinePointMap_apply` giving its coordinate-ring characterization.
* `TauCeti.Toric.faceAffinePointMap_id` and
  `TauCeti.Toric.faceAffinePointMap_comp`: identity and composition laws.
* `TauCeti.Toric.faceAffinePointInfKerLift`, `TauCeti.Toric.faceAffinePointInfKerEquiv`, and
  `TauCeti.Toric.faceAffinePointInfKerHomeomorph`: the inverse map, equivalence, and
  homeomorphism for a character face of a finitely generated cone.
* `TauCeti.Toric.range_faceAffinePointMap_inf_ker` and
  `TauCeti.Toric.isOpenEmbedding_faceAffinePointMap_inf_ker`: the exact range and open-embedding
  theorem for a character face of a finitely generated cone.
* `TauCeti.Toric.range_faceAffinePointMap_of_eq` and
  `TauCeti.Toric.IsRegularCone.exists_range_faceAffinePointMap`: its image is the nonvanishing
  locus of a specified character cutting out an arbitrary face of a regular cone.
* `TauCeti.Toric.IsRegularCone.isOpenEmbedding_faceAffinePointMap`: a regular face chart
  is an open subspace of its ambient affine complex-point chart.

## References

* W. Fulton, *Introduction to Toric Varieties*, §§1.2--1.3.
* D. Cox, J. Little and H. Schenck, *Toric Varieties*, §§1.2--1.3 and §3.1.
-/

public section

open Multiplicative Set Topology

namespace TauCeti.Toric

variable {N V : Type*} [AddCommGroup N] [AddCommGroup V] [Module ℝ V] {i : N →+ V}
  {σ τ υ : PointedCone ℝ V} {r r' : ℕ}

/-- The map on affine complex points induced by a face inclusion.  It is precomposition with the
same coordinate-ring restriction whose spectrum is `faceAffineToricSchemeMap`. -/
noncomputable def faceAffinePointMap (hi : IsIntegralLattice i)
    (hτσ : τ.IsFaceOf σ) :
    AffineSemigroupComplexPoint (dualSemigroup hi τ) →
      AffineSemigroupComplexPoint (dualSemigroup hi σ) :=
  fun x ↦ x.comp (faceAffineCoordinateRingMap hi hτσ)

/-- Applying the complex-point face map is precomposition with `faceAffineCoordinateRingMap`,
whose spectrum is `faceAffineToricSchemeMap` by `faceAffineToricSchemeMap_def`.  The comparison
with morphisms from `Spec ℂ` is not formalized here. -/
@[simp]
theorem faceAffinePointMap_apply (hi : IsIntegralLattice i) (hτσ : τ.IsFaceOf σ)
    (x : AffineSemigroupComplexPoint (dualSemigroup hi τ))
    (a : affineCoordinateRing hi σ) :
    faceAffinePointMap hi hτσ x a = x (faceAffineCoordinateRingMap hi hτσ a) :=
  by rw [faceAffinePointMap]; rfl

/-- The complex-point map of a cone viewed as its own face is the identity. -/
@[simp]
theorem faceAffinePointMap_id (hi : IsIntegralLattice i) :
    faceAffinePointMap hi (PointedCone.IsFaceOf.refl σ) = id := by
  funext x
  apply AlgHom.ext
  intro a
  rw [faceAffinePointMap_apply, faceAffineCoordinateRingMap_id]
  rfl

/-- Successive face restrictions compose contravariantly on coordinate rings and covariantly on
complex points. -/
theorem faceAffinePointMap_comp (hi : IsIntegralLattice i)
    (hυτ : υ.IsFaceOf τ) (hτσ : τ.IsFaceOf σ) :
    faceAffinePointMap hi hτσ ∘ faceAffinePointMap hi hυτ =
      faceAffinePointMap hi (hυτ.trans hτσ) := by
  funext x
  apply AlgHom.ext
  intro a
  rw [Function.comp_apply, faceAffinePointMap_apply,
    faceAffinePointMap_apply, faceAffinePointMap_apply]
  apply congrArg x
  exact DFunLike.congr_fun (faceAffineCoordinateRingMap_comp hi hυτ hτσ) a

/-- Applying two successive face restrictions is the same as applying their composite. -/
@[simp]
theorem faceAffinePointMap_comp_apply (hi : IsIntegralLattice i)
    (hυτ : υ.IsFaceOf τ) (hτσ : τ.IsFaceOf σ)
    (x : AffineSemigroupComplexPoint (dualSemigroup hi υ)) :
    faceAffinePointMap hi hτσ (faceAffinePointMap hi hυτ x) =
      faceAffinePointMap hi (hυτ.trans hτσ) x :=
  congrFun (faceAffinePointMap_comp hi hυτ hτσ) x

/-- The complex-point face map is the general pullback of affine semigroup points along the
inclusion of dual semigroups. -/
theorem faceAffinePointMap_eq_comap (hi : IsIntegralLattice i)
    (hτσ : τ.IsFaceOf σ) :
    faceAffinePointMap hi hτσ = AffineSemigroupComplexPoint.comap
      (dualSemigroupMap hi hi (AddMonoidHom.id N) LinearMap.id (fun _ ↦ rfl)
        fun _ hx ↦ hτσ.le hx) := by
  funext x
  apply AffineSemigroupComplexPoint.ext
  intro m
  rw [faceAffinePointMap_apply, faceAffineCoordinateRingMap_single,
    AffineSemigroupComplexPoint.comap_apply_single]
  congr 2
  apply Subtype.ext
  exact (coe_dualSemigroupMap_id hi (fun _ hx ↦ hτσ.le hx) m).symm

/-- The complex-point map of a face inclusion is continuous for arbitrary finite generating
families on the two dual semigroups. -/
theorem continuous_faceAffinePointMap (hi : IsIntegralLattice i)
    (hτσ : τ.IsFaceOf σ) (gσ : AddGeneratingFamily (dualSemigroup hi σ) r)
    (gτ : AddGeneratingFamily (dualSemigroup hi τ) r') :
    Continuous[affinePointTopology gτ, affinePointTopology gσ]
      (faceAffinePointMap hi hτσ) := by
  rw [faceAffinePointMap_eq_comap]
  exact AffineSemigroupComplexPoint.continuous_comap gσ gτ _

/-! ### A face cut out by one character -/

section CharacterNonzero

variable (hi : IsIntegralLattice i) (m : dualSemigroup hi σ)

/-- The image of a point of the character face lies in the locus where the cutting character
does not vanish. -/
theorem faceAffinePointMap_inf_ker_apply_single_ne_zero
    (x : AffineSemigroupComplexPoint (dualSemigroup hi
      (σ ⊓ PointedCone.ofSubmodule (LinearMap.ker (hi.realCharacter m))))) :
    faceAffinePointMap hi
        (PointedCone.isFaceOf_inf_ker ((mem_dualSemigroup hi m).1 m.2)) x
        (MonoidAlgebra.single (ofAdd m) 1) ≠ 0 := by
  rw [faceAffinePointMap_apply, faceAffineCoordinateRingMap_single]
  apply IsUnit.ne_zero
  apply IsUnit.map x
  refine IsUnit.of_mul_eq_one
    (MonoidAlgebra.single
      (ofAdd ⟨-(m : N →+ ℤ), neg_mem_dualSemigroup_inf_ker hi σ m⟩) 1) ?_
  exact single_ofAdd_mul_single_ofAdd_neg_inf_ker hi σ m

end CharacterNonzero

private theorem faceAffinePoint_apply_mem_powers_ne_zero
    (hi : IsIntegralLattice i) (m : dualSemigroup hi σ)
    (x : {x : AffineSemigroupComplexPoint (dualSemigroup hi σ) //
      x (MonoidAlgebra.single (ofAdd m) 1) ≠ 0})
    (y : Submonoid.powers (MonoidAlgebra.single (ofAdd m) (1 : ℂ))) :
    x.1 y.1 ≠ 0 := by
  obtain ⟨n, hn⟩ := y.2
  rw [← hn, map_pow]
  exact pow_ne_zero n x.2

variable (hi : IsIntegralLattice i) (hσ : σ.FG) (m : dualSemigroup hi σ)

include hσ

private noncomputable abbrev faceAffinePointInfKerAlgebra :
    Algebra (affineCoordinateRing hi σ)
      (affineCoordinateRing hi
        (σ ⊓ PointedCone.ofSubmodule (LinearMap.ker (hi.realCharacter m)))) :=
  (faceAffineCoordinateRingMap hi
    (PointedCone.isFaceOf_inf_ker ((mem_dualSemigroup hi m).1 m.2))).toRingHom.toAlgebra

/-- A complex point on the nonvanishing locus of a character extends uniquely across the
localization defining the corresponding face. -/
noncomputable def faceAffinePointInfKerLift
    (hi : IsIntegralLattice i) (hσ : σ.FG) (m : dualSemigroup hi σ)
    (x : {x : AffineSemigroupComplexPoint (dualSemigroup hi σ) //
      x (MonoidAlgebra.single (ofAdd m) 1) ≠ 0}) :
    AffineSemigroupComplexPoint (dualSemigroup hi
      (σ ⊓ PointedCone.ofSubmodule (LinearMap.ker (hi.realCharacter m)))) := by
  let _ := faceAffinePointInfKerAlgebra hi m
  have := isLocalization_away_faceAffineCoordinateRingMap_inf_ker hi hσ m
  exact IsLocalization.Away.liftAlgHom (MonoidAlgebra.single (ofAdd m) (1 : ℂ))
    (isUnit_iff_ne_zero.mpr x.2)

private theorem faceAffinePointInfKerLift_toRingHom
    (x : {x : AffineSemigroupComplexPoint (dualSemigroup hi σ) //
      x (MonoidAlgebra.single (ofAdd m) 1) ≠ 0}) :
    letI := faceAffinePointInfKerAlgebra hi m
    letI := isLocalization_away_faceAffineCoordinateRingMap_inf_ker hi hσ m
    (faceAffinePointInfKerLift hi hσ m x).toRingHom =
      IsLocalization.Away.lift (MonoidAlgebra.single (ofAdd m) (1 : ℂ))
        (isUnit_iff_ne_zero.mpr x.2) := by
  -- `liftAlgHom` exposes its underlying `Away.lift` only by definitional reduction.
  rw [faceAffinePointInfKerLift]
  rfl

private theorem faceAffinePointInfKerLift_apply
    (x : {x : AffineSemigroupComplexPoint (dualSemigroup hi σ) //
      x (MonoidAlgebra.single (ofAdd m) 1) ≠ 0})
    (a : affineCoordinateRing hi
      (σ ⊓ PointedCone.ofSubmodule (LinearMap.ker (hi.realCharacter m)))) :
    letI := faceAffinePointInfKerAlgebra hi m
    letI := isLocalization_away_faceAffineCoordinateRingMap_inf_ker hi hσ m
    faceAffinePointInfKerLift hi hσ m x a =
      IsLocalization.Away.lift (MonoidAlgebra.single (ofAdd m) (1 : ℂ))
        (isUnit_iff_ne_zero.mpr x.2) a := by
  exact DFunLike.congr_fun (faceAffinePointInfKerLift_toRingHom hi hσ m x) a

/-- Pulling a lifted point back to the ambient chart recovers the original point. -/
@[simp]
theorem faceAffinePointMap_inf_ker_lift
    (x : {x : AffineSemigroupComplexPoint (dualSemigroup hi σ) //
      x (MonoidAlgebra.single (ofAdd m) 1) ≠ 0}) :
    faceAffinePointMap hi
      (PointedCone.isFaceOf_inf_ker ((mem_dualSemigroup hi m).1 m.2))
      (faceAffinePointInfKerLift hi hσ m x) = x := by
  apply AlgHom.ext
  intro a
  rw [faceAffinePointMap_apply]
  let _ := faceAffinePointInfKerAlgebra hi m
  have := isLocalization_away_faceAffineCoordinateRingMap_inf_ker hi hσ m
  rw [faceAffinePointInfKerLift_apply]
  have hmap : algebraMap _ _ a = faceAffineCoordinateRingMap hi
      (PointedCone.isFaceOf_inf_ker ((mem_dualSemigroup hi m).1 m.2)) a :=
    DFunLike.congr_fun (RingHom.algebraMap_toAlgebra (faceAffineCoordinateRingMap hi
      (PointedCone.isFaceOf_inf_ker ((mem_dualSemigroup hi m).1 m.2))).toRingHom) a
  rw [← hmap]
  exact IsLocalization.Away.lift_eq (MonoidAlgebra.single (ofAdd m) (1 : ℂ))
    (isUnit_iff_ne_zero.mpr x.2) a

/-- The localization lift agrees with the original point on monomials coming from the ambient
cone. -/
@[simp]
theorem faceAffinePointInfKerLift_apply_single
    (x : {x : AffineSemigroupComplexPoint (dualSemigroup hi σ) //
      x (MonoidAlgebra.single (ofAdd m) 1) ≠ 0}) (u : dualSemigroup hi σ) :
    faceAffinePointInfKerLift hi hσ m x
        (MonoidAlgebra.single
          (ofAdd ⟨u, dualSemigroup_anti hi inf_le_left u.2⟩) 1) =
      x.1 (MonoidAlgebra.single (ofAdd u) 1) := by
  have hu := DFunLike.congr_fun (faceAffinePointMap_inf_ker_lift hi hσ m x)
    (MonoidAlgebra.single (ofAdd u) 1)
  simpa only [faceAffinePointMap_apply, faceAffineCoordinateRingMap_single] using hu

/-- Extending the restriction of a point of the face recovers that point. -/
@[simp]
theorem faceAffinePointInfKerLift_map
    (x : AffineSemigroupComplexPoint (dualSemigroup hi
      (σ ⊓ PointedCone.ofSubmodule (LinearMap.ker (hi.realCharacter m))))) :
    faceAffinePointInfKerLift hi hσ m
      ⟨faceAffinePointMap hi
          (PointedCone.isFaceOf_inf_ker ((mem_dualSemigroup hi m).1 m.2)) x,
        faceAffinePointMap_inf_ker_apply_single_ne_zero hi m x
      ⟩ = x := by
  let _ := faceAffinePointInfKerAlgebra hi m
  have := isLocalization_away_faceAffineCoordinateRingMap_inf_ker hi hσ m
  apply AlgHom.coe_ringHom_injective
  exact (faceAffinePointInfKerLift_toRingHom hi hσ m _).trans
    (IsLocalization.lift_of_comp
      (M := Submonoid.powers (MonoidAlgebra.single (ofAdd m) (1 : ℂ))) x.toRingHom)

/-- The localization lift evaluates a fraction as the numerator times the reciprocal of its
denominator. -/
theorem faceAffinePointInfKerLift_mk'
    (x : {x : AffineSemigroupComplexPoint (dualSemigroup hi σ) //
      x (MonoidAlgebra.single (ofAdd m) 1) ≠ 0})
    (a : affineCoordinateRing hi σ)
    (y : Submonoid.powers (MonoidAlgebra.single (ofAdd m) (1 : ℂ))) :
    letI := (faceAffineCoordinateRingMap hi
      (PointedCone.isFaceOf_inf_ker ((mem_dualSemigroup hi m).1 m.2))).toRingHom.toAlgebra
    letI := isLocalization_away_faceAffineCoordinateRingMap_inf_ker hi hσ m
    faceAffinePointInfKerLift hi hσ m x (IsLocalization.mk' _ a y) =
      x.1 a * (x.1 y.1)⁻¹ := by
  let _ := faceAffinePointInfKerAlgebra hi m
  have := isLocalization_away_faceAffineCoordinateRingMap_inf_ker hi hσ m
  rw [faceAffinePointInfKerLift_apply]
  rw [IsLocalization.Away.lift]
  apply (IsLocalization.lift_mk'_spec _ a (x.1 a * (x.1 y.1)⁻¹) y).2
  rw [AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom]
  rw [mul_left_comm, mul_inv_cancel₀, mul_one]
  exact faceAffinePoint_apply_mem_powers_ne_zero hi m x y

/-- The localization lift sends the inverse character on the face to the reciprocal of the
cutting character. -/
@[simp]
theorem faceAffinePointInfKerLift_apply_single_neg
    (x : {x : AffineSemigroupComplexPoint (dualSemigroup hi σ) //
      x (MonoidAlgebra.single (ofAdd m) 1) ≠ 0}) :
    faceAffinePointInfKerLift hi hσ m x
        (MonoidAlgebra.single
          (ofAdd ⟨-(m : N →+ ℤ), neg_mem_dualSemigroup_inf_ker hi σ m⟩) 1) =
      (x.1 (MonoidAlgebra.single (ofAdd m) 1))⁻¹ := by
  let hface := PointedCone.isFaceOf_inf_ker ((mem_dualSemigroup hi m).1 m.2)
  let _ := faceAffinePointInfKerAlgebra hi m
  have := isLocalization_away_faceAffineCoordinateRingMap_inf_ker hi hσ m
  let y : Submonoid.powers (MonoidAlgebra.single (ofAdd m) (1 : ℂ)) :=
    ⟨MonoidAlgebra.single (ofAdd m) 1, Submonoid.mem_powers _⟩
  have hy :
      MonoidAlgebra.single
          (ofAdd ⟨-(m : N →+ ℤ), neg_mem_dualSemigroup_inf_ker hi σ m⟩) (1 : ℂ) =
        IsLocalization.mk'
          (affineCoordinateRing hi
            (σ ⊓ PointedCone.ofSubmodule (LinearMap.ker (hi.realCharacter m))))
          (1 : affineCoordinateRing hi σ) y := by
    apply IsLocalization.eq_mk'_iff_mul_eq.mpr
    rw [RingHom.algebraMap_toAlgebra, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom]
    simp only [y]
    rw [map_one, faceAffineCoordinateRingMap_single, mul_comm,
      single_ofAdd_mul_single_ofAdd_neg_inf_ker (R := ℂ) hi σ m]
  rw [hy, faceAffinePointInfKerLift_mk', map_one, one_mul]

/-- The complex points of the face cut out by `m` are in bijection with the locus of the ambient
chart where the monomial of `m` does not vanish. -/
noncomputable def faceAffinePointInfKerEquiv
    (hi : IsIntegralLattice i) (hσ : σ.FG) (m : dualSemigroup hi σ) :
    AffineSemigroupComplexPoint (dualSemigroup hi
      (σ ⊓ PointedCone.ofSubmodule (LinearMap.ker (hi.realCharacter m)))) ≃
      {x : AffineSemigroupComplexPoint (dualSemigroup hi σ) //
        x (MonoidAlgebra.single (ofAdd m) 1) ≠ 0} where
  toFun x := ⟨faceAffinePointMap hi
    (PointedCone.isFaceOf_inf_ker ((mem_dualSemigroup hi m).1 m.2)) x,
      faceAffinePointMap_inf_ker_apply_single_ne_zero hi m x⟩
  invFun := faceAffinePointInfKerLift hi hσ m
  left_inv := faceAffinePointInfKerLift_map hi hσ m
  right_inv x := Subtype.ext (faceAffinePointMap_inf_ker_lift hi hσ m x)

@[simp]
theorem coe_faceAffinePointInfKerEquiv :
    ⇑(faceAffinePointInfKerEquiv hi hσ m) = fun x ↦
      ⟨faceAffinePointMap hi
        (PointedCone.isFaceOf_inf_ker ((mem_dualSemigroup hi m).1 m.2)) x,
        faceAffinePointMap_inf_ker_apply_single_ne_zero hi m x⟩ :=
  by rw [faceAffinePointInfKerEquiv]; rfl

@[simp]
theorem faceAffinePointInfKerEquiv_symm_apply
    (x : {x : AffineSemigroupComplexPoint (dualSemigroup hi σ) //
      x (MonoidAlgebra.single (ofAdd m) 1) ≠ 0}) :
    (faceAffinePointInfKerEquiv hi hσ m).symm x =
      faceAffinePointInfKerLift hi hσ m x :=
  by rw [faceAffinePointInfKerEquiv]; rfl

/-- Extending a complex point across a localization varies continuously on the nonvanishing
locus, for arbitrary finite generating families on the ambient cone and its face. -/
theorem continuous_faceAffinePointInfKerLift
    (gσ : AddGeneratingFamily (dualSemigroup hi σ) r)
    (gF : AddGeneratingFamily (dualSemigroup hi
      (σ ⊓ PointedCone.ofSubmodule (LinearMap.ker (hi.realCharacter m)))) r') :
    @Continuous
      {x : AffineSemigroupComplexPoint (dualSemigroup hi σ) //
        x (MonoidAlgebra.single (ofAdd m) 1) ≠ 0}
      (AffineSemigroupComplexPoint (dualSemigroup hi
        (σ ⊓ PointedCone.ofSubmodule (LinearMap.ker (hi.realCharacter m)))))
      (@instTopologicalSpaceSubtype _ _ (affinePointTopology gσ))
      (affinePointTopology gF) (faceAffinePointInfKerLift hi hσ m) := by
  let _ := affinePointTopology gσ
  rw [affinePointTopology_eq_iInf gF, continuous_iInf_rng]
  intro t
  rw [continuous_induced_rng]
  simp only [Function.comp_def]
  let _ := faceAffinePointInfKerAlgebra hi m
  have := isLocalization_away_faceAffineCoordinateRingMap_inf_ker hi hσ m
  obtain ⟨⟨a, y⟩, hy⟩ := IsLocalization.mk'_surjective
    (Submonoid.powers (MonoidAlgebra.single (ofAdd m) (1 : ℂ)))
    (MonoidAlgebra.single (ofAdd t) (1 : ℂ))
  rw [← hy]
  have ha : Continuous fun x : {x : AffineSemigroupComplexPoint (dualSemigroup hi σ) //
      x (MonoidAlgebra.single (ofAdd m) 1) ≠ 0} ↦ x.1 a :=
    (continuous_eval_const gσ a).comp continuous_subtype_val
  have hay : Continuous fun x : {x : AffineSemigroupComplexPoint (dualSemigroup hi σ) //
      x (MonoidAlgebra.single (ofAdd m) 1) ≠ 0} ↦ x.1 y.1 :=
    (continuous_eval_const gσ y.1).comp continuous_subtype_val
  have hay0 : ∀ x : {x : AffineSemigroupComplexPoint (dualSemigroup hi σ) //
      x (MonoidAlgebra.single (ofAdd m) 1) ≠ 0}, x.1 y.1 ≠ 0 := by
    rintro x
    exact faceAffinePoint_apply_mem_powers_ne_zero hi m x y
  convert ha.mul (hay.inv₀ hay0) using 1
  funext x
  exact faceAffinePointInfKerLift_mk' hi hσ m x a y

/-- The algebraic bijection between the complex points of a character face and its nonvanishing
locus is a homeomorphism for arbitrary finite generating families. -/
noncomputable def faceAffinePointInfKerHomeomorph
    (hi : IsIntegralLattice i) (hσ : σ.FG) (m : dualSemigroup hi σ)
    (gσ : AddGeneratingFamily (dualSemigroup hi σ) r)
    (gF : AddGeneratingFamily (dualSemigroup hi
      (σ ⊓ PointedCone.ofSubmodule (LinearMap.ker (hi.realCharacter m)))) r') :
    @Homeomorph
      (AffineSemigroupComplexPoint (dualSemigroup hi
        (σ ⊓ PointedCone.ofSubmodule (LinearMap.ker (hi.realCharacter m)))))
      {x : AffineSemigroupComplexPoint (dualSemigroup hi σ) //
        x (MonoidAlgebra.single (ofAdd m) 1) ≠ 0}
      (affinePointTopology gF)
      (@instTopologicalSpaceSubtype _ _ (affinePointTopology gσ)) := by
  let _ := affinePointTopology gσ
  let _ := affinePointTopology gF
  exact
    { toEquiv := faceAffinePointInfKerEquiv hi hσ m
      continuous_toFun := Continuous.subtype_mk
        (continuous_faceAffinePointMap hi
          (PointedCone.isFaceOf_inf_ker ((mem_dualSemigroup hi m).1 m.2)) gσ gF) _
      continuous_invFun := continuous_faceAffinePointInfKerLift hi hσ m gσ gF }

@[simp]
theorem coe_faceAffinePointInfKerHomeomorph
    (gσ : AddGeneratingFamily (dualSemigroup hi σ) r)
    (gF : AddGeneratingFamily (dualSemigroup hi
      (σ ⊓ PointedCone.ofSubmodule (LinearMap.ker (hi.realCharacter m)))) r') :
    ⇑(faceAffinePointInfKerHomeomorph (hσ := hσ) hi m gσ gF) =
      ⇑(faceAffinePointInfKerEquiv hi hσ m) :=
  by rw [faceAffinePointInfKerHomeomorph]; rfl

/-- The inverse of the localization homeomorphism is the inverse of its underlying equivalence. -/
@[simp]
theorem coe_faceAffinePointInfKerHomeomorph_symm
    (gσ : AddGeneratingFamily (dualSemigroup hi σ) r)
    (gF : AddGeneratingFamily (dualSemigroup hi
      (σ ⊓ PointedCone.ofSubmodule (LinearMap.ker (hi.realCharacter m)))) r') :
    ⇑(@Homeomorph.symm _ _ (affinePointTopology gF)
      (@instTopologicalSpaceSubtype _ _ (affinePointTopology gσ))
      (faceAffinePointInfKerHomeomorph (hσ := hσ) hi m gσ gF)) =
      ⇑(faceAffinePointInfKerEquiv hi hσ m).symm :=
  by rw [faceAffinePointInfKerHomeomorph]; rfl

/-- The image of the complex-point map for the face cut out by `m` is exactly the locus where the
monomial of `m` does not vanish. -/
theorem range_faceAffinePointMap_inf_ker :
    Set.range (faceAffinePointMap hi
      (PointedCone.isFaceOf_inf_ker ((mem_dualSemigroup hi m).1 m.2))) =
      {x : AffineSemigroupComplexPoint (dualSemigroup hi σ) |
        x (MonoidAlgebra.single (ofAdd m) 1) ≠ 0} := by
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    exact faceAffinePointMap_inf_ker_apply_single_ne_zero hi m y
  · intro hx
    exact ⟨faceAffinePointInfKerLift hi hσ m ⟨x, hx⟩,
      faceAffinePointMap_inf_ker_lift hi hσ m ⟨x, hx⟩⟩

omit hσ

/-- If a specified character cuts out a face of a finitely generated cone, the image of the
complex-point face map is its nonvanishing locus. -/
theorem range_faceAffinePointMap_of_eq (hi : IsIntegralLattice i) (hσ : σ.FG)
    (hτσ : τ.IsFaceOf σ) (m : dualSemigroup hi σ)
    (hm : σ ⊓ PointedCone.ofSubmodule (LinearMap.ker (hi.realCharacter m)) = τ) :
    Set.range (faceAffinePointMap hi hτσ) =
      {x : AffineSemigroupComplexPoint (dualSemigroup hi σ) |
        x (MonoidAlgebra.single (ofAdd m) 1) ≠ 0} := by
  subst τ
  have heq : hτσ = PointedCone.isFaceOf_inf_ker
      ((mem_dualSemigroup hi m).1 m.2) := Subsingleton.elim _ _
  subst hτσ
  exact range_faceAffinePointMap_inf_ker hi hσ m

include hσ

/-- The complex-point map for a face cut out by one character is an open embedding for arbitrary
finite generating families. -/
theorem isOpenEmbedding_faceAffinePointMap_inf_ker
    (gσ : AddGeneratingFamily (dualSemigroup hi σ) r)
    (gF : AddGeneratingFamily (dualSemigroup hi
      (σ ⊓ PointedCone.ofSubmodule (LinearMap.ker (hi.realCharacter m)))) r') :
    @IsOpenEmbedding
      (AffineSemigroupComplexPoint (dualSemigroup hi
        (σ ⊓ PointedCone.ofSubmodule (LinearMap.ker (hi.realCharacter m)))))
      (AffineSemigroupComplexPoint (dualSemigroup hi σ))
      (affinePointTopology gF) (affinePointTopology gσ)
      (faceAffinePointMap hi
        (PointedCone.isFaceOf_inf_ker ((mem_dualSemigroup hi m).1 m.2))) := by
  let _ := affinePointTopology gσ
  let _ := affinePointTopology gF
  have hopen : @IsOpen (AffineSemigroupComplexPoint (dualSemigroup hi σ))
      (affinePointTopology gσ) {x |
      x (MonoidAlgebra.single (ofAdd m) 1) ≠ 0} :=
    isOpen_ne.preimage (continuous_eval_const gσ (MonoidAlgebra.single (ofAdd m) 1))
  have hsub : @IsOpenEmbedding
      {x : AffineSemigroupComplexPoint (dualSemigroup hi σ) //
        x (MonoidAlgebra.single (ofAdd m) 1) ≠ 0}
      (AffineSemigroupComplexPoint (dualSemigroup hi σ))
      (@instTopologicalSpaceSubtype _ _ (affinePointTopology gσ)) (affinePointTopology gσ)
      ((↑) : {x : AffineSemigroupComplexPoint (dualSemigroup hi σ) //
        x (MonoidAlgebra.single (ofAdd m) 1) ≠ 0} →
          AffineSemigroupComplexPoint (dualSemigroup hi σ)) :=
    hopen.isOpenEmbedding_subtypeVal
  have hcomp := hsub.comp
    (faceAffinePointInfKerHomeomorph (hσ := hσ) hi m gσ gF).isOpenEmbedding
  convert hcomp using 1
  simp [Function.comp_def, coe_faceAffinePointInfKerHomeomorph,
    coe_faceAffinePointInfKerEquiv]

omit hσ

namespace IsRegularCone

variable {τ : PointedCone ℝ V}

/-- For a face of a regular cone, some character cutting out that face identifies the range of the
complex-point map with its nonvanishing locus. -/
theorem exists_range_faceAffinePointMap (hreg : IsRegularCone i σ)
    (hτ : τ.IsFaceOf σ) :
    ∃ m : dualSemigroup hi σ,
      σ ⊓ PointedCone.ofSubmodule (LinearMap.ker (hi.realCharacter m)) = τ ∧
      Set.range (faceAffinePointMap hi hτ) =
        {x : AffineSemigroupComplexPoint (dualSemigroup hi σ) |
          x (MonoidAlgebra.single (ofAdd m) 1) ≠ 0} := by
  obtain ⟨m, hm, hface⟩ := hreg.exists_mem_dualSemigroup_inf_ker_eq hi hτ
  exact ⟨⟨m, hm⟩, hface,
    range_faceAffinePointMap_of_eq hi hreg.fg hτ ⟨m, hm⟩ hface⟩

/-- The complex-point map of every face inclusion into a regular cone is an open embedding for
arbitrary finite generating families.  Thus face localization is an open subspace at the
topological level. -/
theorem isOpenEmbedding_faceAffinePointMap (hreg : IsRegularCone i σ)
    (hτ : τ.IsFaceOf σ) (gσ : AddGeneratingFamily (dualSemigroup hi σ) r)
    (gτ : AddGeneratingFamily (dualSemigroup hi τ) r') :
    @IsOpenEmbedding
      (AffineSemigroupComplexPoint (dualSemigroup hi τ))
      (AffineSemigroupComplexPoint (dualSemigroup hi σ))
      (affinePointTopology gτ) (affinePointTopology gσ)
      (faceAffinePointMap hi hτ) := by
  obtain ⟨m, hm, hface⟩ := hreg.exists_mem_dualSemigroup_inf_ker_eq hi hτ
  subst τ
  have heq : hτ = PointedCone.isFaceOf_inf_ker
      ((mem_dualSemigroup hi (⟨m, hm⟩ : dualSemigroup hi σ)).1 hm) := Subsingleton.elim _ _
  subst hτ
  exact isOpenEmbedding_faceAffinePointMap_inf_ker hi hreg.fg ⟨m, hm⟩ gσ gτ

end IsRegularCone


end TauCeti.Toric
