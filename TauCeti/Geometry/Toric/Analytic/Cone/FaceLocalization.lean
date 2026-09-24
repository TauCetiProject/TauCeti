/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Toric.Algebraic.FaceLocalization
public import TauCeti.Geometry.Toric.Analytic.Character.Action
public import TauCeti.Geometry.Toric.Analytic.Character.Basic

/-!
# Face localizations of affine complex points

A face `τ` of a cone `σ` has the larger dual semigroup, so a complex point of the affine chart of
`τ` restricts to a complex point of the affine chart of `σ`. This restriction
`TauCeti.Toric.faceAffinePointMap` is the map on complex points induced by the algebraic face
restriction `TauCeti.Toric.faceAffineCoordinateRingMap`; it is functorial in face inclusions and
equivariant for the coordinate-free complex torus.

When `σ` is finitely generated and `τ = σ ⊓ ker m` is cut out by a character `m` of the dual
semigroup of `σ`, the coordinate ring of `τ` is the localization of that of `σ` away from the
monomial of `m`. On complex points this becomes the analytic statement that the face map is an
open embedding onto the locus where the monomial of `m` does not vanish: a point of `τ` is
recovered from its restriction because every character nonnegative on `τ` becomes nonnegative on
`σ` after adding a multiple of `m`, and the monomial of `m` is invertible on `τ`. The topologies
are the monomial-embedding topologies of arbitrary finite generating families, so the statement
involves no choice of coordinates.

Every face of a regular cone is cut out in this way. For a regular cone the image of the face map
is therefore described intrinsically, as the locus where every monomial of a character vanishing
on the face is nonzero, and the image of the intersection of two faces is the intersection of
their images. These open embeddings and their overlaps are the topological input for gluing the
affine charts of a fan.

## Main declarations

* `TauCeti.Toric.faceAffinePointMap`: restriction of complex points along a face inclusion, with
  `TauCeti.Toric.faceAffinePointMap_eq_comp` identifying it with the complex points of the
  algebraic face restriction, and `TauCeti.Toric.faceAffinePointMap_id`,
  `TauCeti.Toric.faceAffinePointMap_comp` and `TauCeti.Toric.faceAffinePointMap_smul` its
  functoriality and torus equivariance.
* `TauCeti.Toric.continuous_faceAffinePointMap`: the face map is continuous.
* `TauCeti.Toric.faceAffinePointMap_apply_single_ne_zero`: a restricted point does not vanish on
  the monomial of a character vanishing on the face.
* `TauCeti.Toric.injective_faceAffinePointMap_of_inf_ker_eq`,
  `TauCeti.Toric.range_faceAffinePointMap_of_inf_ker_eq` and
  `TauCeti.Toric.isOpenEmbedding_faceAffinePointMap_of_inf_ker_eq`: for a face cut out by a
  character `m` of a finitely generated cone, the face map is an open embedding onto the locus
  where the monomial of `m` does not vanish.
* `TauCeti.Toric.IsRegularCone.range_faceAffinePointMap`,
  `TauCeti.Toric.IsRegularCone.isOpenEmbedding_faceAffinePointMap` and
  `TauCeti.Toric.IsRegularCone.range_faceAffinePointMap_inf`: the same for every face of a regular
  cone, with an intrinsic description of the image and its behaviour on intersections of faces.

## References

* W. Fulton, *Introduction to Toric Varieties*, §§1.3 and 2.1.
* D. Cox, J. Little and H. Schenck, *Toric Varieties*, §§1.3 and 3.1.
-/

public section

open Multiplicative Topology

namespace TauCeti.Toric

open AffineSemigroupComplexPoint

variable {N V : Type*} [AddCommGroup N] [AddCommGroup V] [Module ℝ V] {i : N →+ V}
  {σ τ υ : PointedCone ℝ V} {r r' : ℕ}

/-! ### The face map on complex points -/

/-- The map on complex points induced by a face inclusion `τ ≼ σ`: the dual semigroup of `σ` is
contained in that of `τ`, so a complex point of the affine chart of `τ` restricts to a complex
point of the affine chart of `σ`. -/
noncomputable def faceAffinePointMap (hi : IsIntegralLattice i) (hτσ : τ.IsFaceOf σ) :
    AffineSemigroupComplexPoint (dualSemigroup hi τ) →
      AffineSemigroupComplexPoint (dualSemigroup hi σ) :=
  comap (AddSubmonoid.inclusion (dualSemigroup_anti hi hτσ.le))

/-- The face map is the pullback of complex points along the inclusion of dual semigroups. -/
theorem faceAffinePointMap_def (hi : IsIntegralLattice i) (hτσ : τ.IsFaceOf σ) :
    faceAffinePointMap hi hτσ = comap (AddSubmonoid.inclusion (dualSemigroup_anti hi hτσ.le)) :=
  (rfl)

/-- The restriction of a point takes the same value on the monomial of a character. -/
@[simp]
theorem faceAffinePointMap_apply_single (hi : IsIntegralLattice i) (hτσ : τ.IsFaceOf σ)
    (x : AffineSemigroupComplexPoint (dualSemigroup hi τ)) (m : dualSemigroup hi σ) :
    faceAffinePointMap hi hτσ x (MonoidAlgebra.single (ofAdd m) 1) =
      x (MonoidAlgebra.single (ofAdd ⟨m, dualSemigroup_anti hi hτσ.le m.2⟩) 1) :=
  comap_apply_single _ x m

/-- The face map on complex points is precomposition with the algebraic restriction of
coordinate rings along the face inclusion. -/
theorem faceAffinePointMap_eq_comp (hi : IsIntegralLattice i) (hτσ : τ.IsFaceOf σ)
    (x : AffineSemigroupComplexPoint (dualSemigroup hi τ)) :
    faceAffinePointMap hi hτσ x = x.comp (faceAffineCoordinateRingMap hi hτσ) :=
  AffineSemigroupComplexPoint.ext fun m ↦ by simp

/-- The face map of a cone viewed as its own face is the identity. -/
@[simp]
theorem faceAffinePointMap_id (hi : IsIntegralLattice i) :
    faceAffinePointMap hi (PointedCone.IsFaceOf.refl σ) = id :=
  funext fun _ ↦ AffineSemigroupComplexPoint.ext fun _ ↦ by simp

/-- Restricting along two successive face inclusions is restricting along the composite face
inclusion. -/
@[simp]
theorem faceAffinePointMap_faceAffinePointMap (hi : IsIntegralLattice i) (hυτ : υ.IsFaceOf τ)
    (hτσ : τ.IsFaceOf σ) (x : AffineSemigroupComplexPoint (dualSemigroup hi υ)) :
    faceAffinePointMap hi hτσ (faceAffinePointMap hi hυτ x) =
      faceAffinePointMap hi (hυτ.trans hτσ) x :=
  AffineSemigroupComplexPoint.ext fun _ ↦ by simp

/-- The face maps compose along composite face inclusions. -/
theorem faceAffinePointMap_comp (hi : IsIntegralLattice i) (hυτ : υ.IsFaceOf τ)
    (hτσ : τ.IsFaceOf σ) :
    faceAffinePointMap hi hτσ ∘ faceAffinePointMap hi hυτ =
      faceAffinePointMap hi (hυτ.trans hτσ) :=
  funext (faceAffinePointMap_faceAffinePointMap hi hυτ hτσ)

/-- The face map is equivariant for the coordinate-free complex torus. -/
@[simp]
theorem faceAffinePointMap_smul (hi : IsIntegralLattice i) (hτσ : τ.IsFaceOf σ)
    (t : ComplexTorus N) (x : AffineSemigroupComplexPoint (dualSemigroup hi τ)) :
    faceAffinePointMap hi hτσ (t • x) = t • faceAffinePointMap hi hτσ x :=
  comap_inclusion_smul _ t x

/-- The face map is continuous for the monomial-embedding topologies of arbitrary finite
generating families. -/
theorem continuous_faceAffinePointMap (hi : IsIntegralLattice i) (hτσ : τ.IsFaceOf σ)
    (g : AddGeneratingFamily (dualSemigroup hi σ) r)
    (h : AddGeneratingFamily (dualSemigroup hi τ) r') :
    Continuous[affinePointTopology h, affinePointTopology g] (faceAffinePointMap hi hτσ) :=
  continuous_comap g h _

/-! ### Nonvanishing and recovery from the restriction -/

/-- A restricted point does not vanish on the monomial of a character of the dual semigroup of
`σ` that vanishes on the face `τ`: the negative of such a character is nonnegative on `τ`, so its
monomial is invertible on the chart of `τ`. -/
theorem faceAffinePointMap_apply_single_ne_zero (hi : IsIntegralLattice i) (hτσ : τ.IsFaceOf σ)
    (x : AffineSemigroupComplexPoint (dualSemigroup hi τ)) {m : dualSemigroup hi σ}
    (hm : ∀ v ∈ τ, hi.realCharacter m v = 0) :
    faceAffinePointMap hi hτσ x (MonoidAlgebra.single (ofAdd m) 1) ≠ 0 := by
  have hneg : -(m : N →+ ℤ) ∈ dualSemigroup hi τ := (mem_dualSemigroup hi _).2 fun v hv ↦ by
    simp [hm v hv]
  have h0 : (⟨m, dualSemigroup_anti hi hτσ.le m.2⟩ : dualSemigroup hi τ) + ⟨_, hneg⟩ = 0 :=
    Subtype.ext (add_neg_cancel _)
  refine left_ne_zero_of_mul_eq_one (b := x (MonoidAlgebra.single (ofAdd ⟨_, hneg⟩) 1)) ?_
  rw [faceAffinePointMap_apply_single, ← apply_single_add, h0, ofAdd_zero,
    ← MonoidAlgebra.one_def, map_one]

/-- A point of the chart of the face `τ` is recovered from its restriction: if `u + n • m` lies in
the dual semigroup of `σ` for a character `m` vanishing on `τ`, the value on the monomial of `u` is
the value of the restriction on the monomial of `u + n • m` divided by its `n`-th power on the
monomial of `m`. -/
private theorem apply_single_eq_div (hi : IsIntegralLattice i) (hτσ : τ.IsFaceOf σ)
    (x : AffineSemigroupComplexPoint (dualSemigroup hi τ)) {m : dualSemigroup hi σ}
    (hm : ∀ v ∈ τ, hi.realCharacter m v = 0) (u : dualSemigroup hi τ) {n : ℕ}
    (hn : (u : N →+ ℤ) + n • (m : N →+ ℤ) ∈ dualSemigroup hi σ) :
    x (MonoidAlgebra.single (ofAdd u) 1) =
      faceAffinePointMap hi hτσ x (MonoidAlgebra.single (ofAdd ⟨_, hn⟩) 1) /
        faceAffinePointMap hi hτσ x (MonoidAlgebra.single (ofAdd m) 1) ^ n := by
  rw [eq_div_iff (pow_ne_zero _ (faceAffinePointMap_apply_single_ne_zero hi hτσ x hm)),
    faceAffinePointMap_apply_single, faceAffinePointMap_apply_single, ← apply_single_nsmul,
    ← apply_single_add]
  exact congrArg (fun s ↦ x (MonoidAlgebra.single (ofAdd s) 1)) (Subtype.ext (by simp))

/-! ### Faces cut out by a character -/

section InfKer

variable (hi : IsIntegralLattice i)

/-- A character `m` of the dual semigroup of `σ` vanishes on the face `σ ⊓ ker m` it cuts out. -/
private theorem realCharacter_eq_zero_of_inf_ker_eq {m : dualSemigroup hi σ}
    (hm : σ ⊓ PointedCone.ofSubmodule (LinearMap.ker (hi.realCharacter m)) = τ) :
    ∀ v ∈ τ, hi.realCharacter m v = 0 := by
  subst hm
  exact fun _ hv ↦ hv.2

/-- For a face `τ` cut out by a character `m` of the dual semigroup of a finitely generated cone
`σ`, a complex point of the chart of `τ` is determined by its restriction to the chart of
`σ`. -/
theorem injective_faceAffinePointMap_of_inf_ker_eq (hσ : σ.FG) (hτσ : τ.IsFaceOf σ)
    (m : dualSemigroup hi σ)
    (hm : σ ⊓ PointedCone.ofSubmodule (LinearMap.ker (hi.realCharacter m)) = τ) :
    Function.Injective (faceAffinePointMap hi hτσ) := by
  intro x y hxy
  refine AffineSemigroupComplexPoint.ext fun u ↦ ?_
  have hm₀ := realCharacter_eq_zero_of_inf_ker_eq hi hm
  obtain ⟨n, hn⟩ := exists_add_nsmul_mem_dualSemigroup hi hσ m.2 (by rw [hm]; exact u.2)
  rw [apply_single_eq_div hi hτσ x hm₀ u hn, apply_single_eq_div hi hτσ y hm₀ u hn, hxy]

/-- For a face `τ` cut out by a character `m` of the dual semigroup of a finitely generated cone
`σ`, the image of the chart of `τ` in the chart of `σ` is the locus where the monomial of `m`
does not vanish. -/
theorem range_faceAffinePointMap_of_inf_ker_eq (hσ : σ.FG) (hτσ : τ.IsFaceOf σ)
    (m : dualSemigroup hi σ)
    (hm : σ ⊓ PointedCone.ofSubmodule (LinearMap.ker (hi.realCharacter m)) = τ) :
    Set.range (faceAffinePointMap hi hτσ) = {x | x (MonoidAlgebra.single (ofAdd m) 1) ≠ 0} := by
  refine Set.Subset.antisymm ?_ fun x hx ↦ ?_
  · rintro _ ⟨y, rfl⟩
    exact faceAffinePointMap_apply_single_ne_zero hi hτσ y
      (realCharacter_eq_zero_of_inf_ker_eq hi hm)
  subst hm
  -- The coordinate ring of the face is the localization of that of `σ` away from the monomial of
  -- `m`, so `x`, which inverts that monomial, extends uniquely to it.
  let φ := affineCoordinateRingMap
    (σ := σ ⊓ PointedCone.ofSubmodule (LinearMap.ker (hi.realCharacter m))) (τ := σ) hi hi
    (AddMonoidHom.id N) LinearMap.id (fun _ ↦ rfl) (fun _ hx ↦ hx.1)
  let := φ.toRingHom.toAlgebra
  have := isLocalization_away_affineCoordinateRingMap_inf_ker hi hσ m
  let y := IsLocalization.Away.lift (MonoidAlgebra.single (ofAdd m) (1 : ℂ))
    (S := affineCoordinateRing hi
      (σ ⊓ PointedCone.ofSubmodule (LinearMap.ker (hi.realCharacter m))))
    (g := (x : MonoidAlgebra ℂ (Multiplicative (dualSemigroup hi σ)) →+* ℂ)) (Ne.isUnit hx)
  have hy : ∀ a, y (φ a) = x a := IsLocalization.Away.lift_eq _ _
  refine ⟨{ y with commutes' := fun c ↦ ?_ }, AffineSemigroupComplexPoint.ext fun s ↦ ?_⟩
  · exact (congrArg y (φ.commutes c)).symm.trans ((hy _).trans (x.commutes c))
  · have hφ : φ (MonoidAlgebra.single (ofAdd s) 1) =
        MonoidAlgebra.single (ofAdd ⟨s, dualSemigroup_anti hi hτσ.le s.2⟩) 1 := by
      refine (affineCoordinateRingMap_single
        (σ := σ ⊓ PointedCone.ofSubmodule (LinearMap.ker (hi.realCharacter m))) (τ := σ) hi hi
        (AddMonoidHom.id N) LinearMap.id (fun _ ↦ rfl) (fun _ hx ↦ hx.1) s 1).trans ?_
      congr 2
      exact Subtype.ext (coe_dualSemigroupMap_id hi _ s)
    rw [faceAffinePointMap_apply_single, AlgHom.coe_mk, ← hy, hφ]

/-- For a face `τ` cut out by a character `m` of the dual semigroup of a finitely generated cone
`σ`, the face map is an open embedding of the chart of `τ` into the chart of `σ`, for the
monomial-embedding topologies of arbitrary finite generating families. -/
theorem isOpenEmbedding_faceAffinePointMap_of_inf_ker_eq (hσ : σ.FG) (hτσ : τ.IsFaceOf σ)
    (m : dualSemigroup hi σ)
    (hm : σ ⊓ PointedCone.ofSubmodule (LinearMap.ker (hi.realCharacter m)) = τ)
    (g : AddGeneratingFamily (dualSemigroup hi σ) r)
    (h : AddGeneratingFamily (dualSemigroup hi τ) r') :
    @IsOpenEmbedding _ _ (affinePointTopology h) (affinePointTopology g)
      (faceAffinePointMap hi hτσ) := by
  let := affinePointTopology g
  let := affinePointTopology h
  have hm₀ := realCharacter_eq_zero_of_inf_ker_eq hi hm
  -- The topology induced from the chart of `σ` already makes every monomial of `τ` continuous.
  have hind : IsInducing (faceAffinePointMap hi hτσ) := by
    refine ⟨le_antisymm (continuous_faceAffinePointMap hi hτσ g h).le_induced ?_⟩
    let _ : TopologicalSpace (AffineSemigroupComplexPoint (dualSemigroup hi τ)) :=
      TopologicalSpace.induced (faceAffinePointMap hi hτσ) (affinePointTopology g)
    refine continuous_id_iff_le.1 ((continuous_iff_forall_continuous_apply_single h id).2
      fun u ↦ ?_)
    obtain ⟨n, hn⟩ := exists_add_nsmul_mem_dualSemigroup hi hσ m.2 (by rw [hm]; exact u.2)
    simp only [id, apply_single_eq_div hi hτσ _ hm₀ u hn]
    have hdiv : ContinuousOn (fun x : AffineSemigroupComplexPoint (dualSemigroup hi σ) ↦
        x (MonoidAlgebra.single (ofAdd ⟨(u : N →+ ℤ) + n • (m : N →+ ℤ), hn⟩) 1) /
          x (MonoidAlgebra.single (ofAdd m) 1) ^ n)
        {x | x (MonoidAlgebra.single (ofAdd m) 1) ≠ 0} :=
      (continuous_apply_single g _).continuousOn.div
        ((continuous_apply_single g m).pow n).continuousOn fun _ hx ↦ pow_ne_zero n hx
    exact hdiv.comp_continuous continuous_induced_dom
      fun y ↦ faceAffinePointMap_apply_single_ne_zero hi hτσ y hm₀
  refine ⟨⟨hind, injective_faceAffinePointMap_of_inf_ker_eq hi hσ hτσ m hm⟩, ?_⟩
  rw [range_faceAffinePointMap_of_inf_ker_eq hi hσ hτσ m hm]
  exact isOpen_ne_fun (continuous_apply_single g m) continuous_const

end InfKer

/-- For a face `τ` of a finitely generated cone `σ` cut out by a character, the image of the
chart of `τ` in the chart of `σ` is intrinsically the locus where every monomial of a character
vanishing on `τ` is nonzero. -/
theorem range_faceAffinePointMap_of_exists_inf_ker_eq (hi : IsIntegralLattice i) (hσ : σ.FG)
    (hτσ : τ.IsFaceOf σ)
    (hτ : ∃ m : dualSemigroup hi σ,
      σ ⊓ PointedCone.ofSubmodule (LinearMap.ker (hi.realCharacter m)) = τ) :
    Set.range (faceAffinePointMap hi hτσ) =
      {x | ∀ m : dualSemigroup hi σ, (∀ v ∈ τ, hi.realCharacter m v = 0) →
        x (MonoidAlgebra.single (ofAdd m) 1) ≠ 0} := by
  refine Set.Subset.antisymm ?_ fun x hx ↦ ?_
  · rintro _ ⟨y, rfl⟩ m hm
    exact faceAffinePointMap_apply_single_ne_zero hi hτσ y hm
  obtain ⟨m, hm⟩ := hτ
  rw [range_faceAffinePointMap_of_inf_ker_eq hi hσ hτσ m hm]
  exact hx m (realCharacter_eq_zero_of_inf_ker_eq hi hm)

/-- If two faces of a finitely generated cone are cut out by characters, the image of their
intersection is the intersection of their images. -/
theorem range_faceAffinePointMap_inf_of_inf_ker_eq (hi : IsIntegralLattice i) (hσ : σ.FG)
    (hτσ : τ.IsFaceOf σ) (hυσ : υ.IsFaceOf σ) (m₁ : dualSemigroup hi σ)
    (h₁ : σ ⊓ PointedCone.ofSubmodule (LinearMap.ker (hi.realCharacter m₁)) = τ)
    (m₂ : dualSemigroup hi σ)
    (h₂ : σ ⊓ PointedCone.ofSubmodule (LinearMap.ker (hi.realCharacter m₂)) = υ) :
    Set.range (faceAffinePointMap hi (hτσ.inf_left hυσ)) =
      Set.range (faceAffinePointMap hi hτσ) ∩ Set.range (faceAffinePointMap hi hυσ) := by
  have h₁₂ : σ ⊓ PointedCone.ofSubmodule (LinearMap.ker (hi.realCharacter (m₁ + m₂))) = τ ⊓ υ := by
    rw [map_add, PointedCone.inf_ker_add
      ((mem_dualSemigroup hi m₁).1 m₁.2) ((mem_dualSemigroup hi m₂).1 m₂.2), h₁, h₂]
  refine Set.Subset.antisymm ?_ fun x ⟨hxτ, hxυ⟩ ↦ ?_
  · rintro x hx
    rw [range_faceAffinePointMap_of_exists_inf_ker_eq hi hσ (hτσ.inf_left hυσ)
      ⟨m₁ + m₂, h₁₂⟩] at hx
    rw [range_faceAffinePointMap_of_exists_inf_ker_eq hi hσ hτσ ⟨m₁, h₁⟩,
      range_faceAffinePointMap_of_exists_inf_ker_eq hi hσ hυσ ⟨m₂, h₂⟩]
    exact ⟨fun m hm ↦ hx m fun v hv ↦ hm v hv.1, fun m hm ↦ hx m fun v hv ↦ hm v hv.2⟩
  rw [range_faceAffinePointMap_of_inf_ker_eq hi hσ _ (m₁ + m₂) h₁₂,
    Set.mem_ofPred_eq, apply_single_add]
  rw [range_faceAffinePointMap_of_inf_ker_eq hi hσ hτσ m₁ h₁] at hxτ
  rw [range_faceAffinePointMap_of_inf_ker_eq hi hσ hυσ m₂ h₂] at hxυ
  exact mul_ne_zero hxτ hxυ

/-! ### Faces of regular cones -/

namespace IsRegularCone

variable (hi : IsIntegralLattice i)

/-- For a face `τ` of a regular cone `σ`, the image of the chart of `τ` in the chart of `σ` is the
locus where the monomial of every character of the dual semigroup of `σ` vanishing on `τ` is
nonzero. -/
theorem range_faceAffinePointMap (hσ : IsRegularCone i σ) (hτσ : τ.IsFaceOf σ) :
    Set.range (faceAffinePointMap hi hτσ) =
      {x | ∀ m : dualSemigroup hi σ, (∀ v ∈ τ, hi.realCharacter m v = 0) →
        x (MonoidAlgebra.single (ofAdd m) 1) ≠ 0} := by
  obtain ⟨m, hm, hmτ⟩ := hσ.exists_mem_dualSemigroup_inf_ker_eq hi hτσ
  exact range_faceAffinePointMap_of_exists_inf_ker_eq hi hσ.fg hτσ ⟨⟨m, hm⟩, hmτ⟩

/-- For a face `τ` of a regular cone `σ`, the face map is an open embedding of the chart of `τ`
into the chart of `σ`, for the monomial-embedding topologies of arbitrary finite generating
families. -/
theorem isOpenEmbedding_faceAffinePointMap (hσ : IsRegularCone i σ) (hτσ : τ.IsFaceOf σ)
    (g : AddGeneratingFamily (dualSemigroup hi σ) r)
    (h : AddGeneratingFamily (dualSemigroup hi τ) r') :
    @IsOpenEmbedding _ _ (affinePointTopology h) (affinePointTopology g)
      (faceAffinePointMap hi hτσ) := by
  obtain ⟨m, hm, hmτ⟩ := hσ.exists_mem_dualSemigroup_inf_ker_eq hi hτσ
  exact isOpenEmbedding_faceAffinePointMap_of_inf_ker_eq hi hσ.fg hτσ ⟨m, hm⟩ hmτ g h

/-- For two faces `τ` and `υ` of a regular cone `σ`, the image of the chart of `τ ⊓ υ` in the
chart of `σ` is the intersection of the images of the charts of `τ` and of `υ`. -/
theorem range_faceAffinePointMap_inf (hσ : IsRegularCone i σ) (hτσ : τ.IsFaceOf σ)
    (hυσ : υ.IsFaceOf σ) :
    Set.range (faceAffinePointMap hi (hτσ.inf_left hυσ)) =
      Set.range (faceAffinePointMap hi hτσ) ∩ Set.range (faceAffinePointMap hi hυσ) := by
  obtain ⟨m₁, hm₁, h₁⟩ := hσ.exists_mem_dualSemigroup_inf_ker_eq hi hτσ
  obtain ⟨m₂, hm₂, h₂⟩ := hσ.exists_mem_dualSemigroup_inf_ker_eq hi hυσ
  exact range_faceAffinePointMap_inf_of_inf_ker_eq hi hσ.fg hτσ hυσ ⟨m₁, hm₁⟩ h₁ ⟨m₂, hm₂⟩ h₂

end IsRegularCone

end TauCeti.Toric
