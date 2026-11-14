/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.AffineSpace
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.RingTheory.AlgebraicIndependent.Defs

/-!
# Algebra evaluation morphisms into affine space

For a commutative ring `R`, an `R`-algebra `A`, and a coordinate family `x : n → A`,
`AlgebraicGeometry.AffineSpace.homOfAlgebra R x` is the canonical `Spec (.of R)`-morphism
`Spec (.of A) ⟶ 𝔸(n; Spec (.of R))` corresponding to polynomial evaluation `MvPolynomial.aeval x`.

* `isClosedImmersion_homOfAlgebra_iff`: `homOfAlgebra R x` is a closed immersion if and only if
  `x` generates `A` as an `R`-algebra (`Algebra.adjoin R (Set.range x) = ⊤`).
* `isFinite_homOfAlgebra_iff`: `homOfAlgebra R y` is a finite morphism of schemes if and only if
  `MvPolynomial.aeval y` is module-finite.
* `surjective_homOfAlgebra`: `homOfAlgebra R y` is surjective when `y` is algebraically independent
  over `R` and makes `A` integral over `MvPolynomial n R`.

## Main declarations

* `AlgebraicGeometry.AffineSpace.homOfAlgebra`: the evaluation morphism
  `Spec (.of A) ⟶ 𝔸(n; Spec (.of R))` attached to a coordinate tuple `x : n → A`.
-/

public section

open CategoryTheory MvPolynomial

namespace AlgebraicGeometry.AffineSpace

universe u

noncomputable section

variable {R A : Type u} [CommRing R] [CommRing A] [Algebra R A] {m n : Type u}

variable (R) in
/-- The `Spec R`-morphism `Spec (.of A) ⟶ 𝔸(n; Spec (.of R))` corresponding to the `R`-algebra
evaluation homomorphism `MvPolynomial.aeval x : MvPolynomial n R →ₐ[R] A`. -/
def homOfAlgebra (x : n → A) : Spec (.of A) ⟶ 𝔸(n; Spec (.of R)) :=
  Spec.map (CommRingCat.ofHom (MvPolynomial.aeval (R := R) x).toRingHom) ≫
    (SpecIso n (.of R)).inv

/-- Explicit unfolding of `homOfAlgebra` in terms of `Spec.map` and `SpecIso`. -/
lemma homOfAlgebra_def (x : n → A) :
    homOfAlgebra R x =
      Spec.map (CommRingCat.ofHom (MvPolynomial.aeval (R := R) x).toRingHom) ≫
        (SpecIso n (.of R)).inv :=
  (rfl)

/-- Composing `homOfAlgebra R x` with `(SpecIso n (.of R)).hom` recovers `Spec.map (aeval x)`. -/
@[reassoc (attr := simp)]
lemma homOfAlgebra_specIso_hom (x : n → A) :
    homOfAlgebra R x ≫ (SpecIso n (.of R)).hom =
      Spec.map (CommRingCat.ofHom (MvPolynomial.aeval (R := R) x).toRingHom) := by
  simp [homOfAlgebra_def]

/-- `homOfAlgebra R x` lies over `Spec (.of R)` via `Spec.map (algebraMap R A)`. -/
@[reassoc (attr := simp)]
lemma homOfAlgebra_over (x : n → A) :
    homOfAlgebra R x ≫ 𝔸(n; Spec (.of R)) ↘ Spec (.of R) =
      Spec.map (CommRingCat.ofHom (algebraMap R A)) := by
  rw [homOfAlgebra_def, Category.assoc, SpecIso_inv_over, ← Spec.map_comp,
    ← CommRingCat.ofHom_comp]
  congr 2
  ext r
  simp

/-- Pulling back the `i`-th coordinate of `𝔸(n; Spec (.of R))` along `homOfAlgebra R x` gives the
global section corresponding to `x i`. -/
@[simp]
lemma homOfAlgebra_appTop_coord (x : n → A) (i : n) :
    (homOfAlgebra R x).appTop (coord (Spec (.of R)) i) =
      (Scheme.ΓSpecIso (.of A)).inv (x i) := by
  rw [homOfAlgebra_def, Scheme.Hom.comp_appTop, CommRingCat.comp_apply, SpecIso_inv_appTop_coord,
    ← CommRingCat.comp_apply, ← Scheme.ΓSpecIso_inv_naturality, CommRingCat.comp_apply,
    ConcreteCategory.hom_ofHom]
  simp

/-- `homOfAlgebra R` is injective in the coordinate tuple `x : n → A`. -/
@[simp]
lemma homOfAlgebra_inj {x y : n → A} :
    homOfAlgebra R x = homOfAlgebra R y ↔ x = y := by
  refine ⟨fun h ↦ funext fun i ↦ ?_, fun h ↦ h ▸ rfl⟩
  simpa using congrArg (Scheme.ΓSpecIso (.of A)).hom
    (congrArg (fun f ↦ f.appTop (coord (Spec (.of R)) i)) h)

/-- Evaluating at the standard indeterminates `MvPolynomial.X` yields `(SpecIso n (.of R)).inv`. -/
@[simp]
lemma homOfAlgebra_X :
    homOfAlgebra R (MvPolynomial.X : n → MvPolynomial n R) = (SpecIso n (.of R)).inv := by
  simp [homOfAlgebra_def]

/-- `homOfAlgebra R x` agrees with `homOfVector` applied to the global sections corresponding to
`x`. -/
lemma homOfAlgebra_eq_homOfVector (x : n → A) :
    homOfAlgebra R x =
      homOfVector (Spec.map (CommRingCat.ofHom (algebraMap R A)))
        ((Scheme.ΓSpecIso (.of A)).inv ∘ x) := by
  refine hom_ext (by simp) fun i ↦ ?_
  simp

/-- Postcomposing `homOfAlgebra R x` with `reindex g (Spec (.of R))` reindexes the coordinates `x`
along `g`. -/
@[reassoc (attr := simp)]
lemma homOfAlgebra_reindex (x : n → A) (g : m → n) :
    homOfAlgebra R x ≫ reindex g (Spec (.of R)) = homOfAlgebra R (x ∘ g) := by
  refine hom_ext (by simp) fun _ ↦ ?_
  simp only [Scheme.Hom.comp_appTop, CommRingCat.comp_apply, reindex_appTop_coord,
    homOfAlgebra_appTop_coord, Function.comp_apply]

/-- Precomposing `homOfAlgebra R x` with `Spec.map` of an `R`-algebra morphism `f : A →ₐ[R] B`
applies `f` to the coordinates `x`. -/
@[reassoc]
lemma specMap_homOfAlgebra {B : Type u} [CommRing B] [Algebra R B] (f : A →ₐ[R] B) (x : n → A) :
    Spec.map (CommRingCat.ofHom f.toRingHom) ≫ homOfAlgebra R x =
      homOfAlgebra R (f ∘ x) := by
  have hcomp : f.comp (MvPolynomial.aeval (R := R) x) = MvPolynomial.aeval (R := R) (f ∘ x) :=
    MvPolynomial.algHom_ext fun i ↦ by simp
  simp only [homOfAlgebra_def, ← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
    AlgHom.toRingHom_eq_coe, ← AlgHom.comp_toRingHom, hcomp]

/-- `homOfAlgebra R x : Spec (.of A) ⟶ 𝔸(n; Spec (.of R))` is a closed immersion if and only if
`x` generates `A` as an `R`-algebra. -/
@[simp]
theorem isClosedImmersion_homOfAlgebra_iff {x : n → A} :
    IsClosedImmersion (homOfAlgebra R x) ↔ Algebra.adjoin R (Set.range x) = ⊤ := by
  rw [homOfAlgebra_def, MorphismProperty.cancel_right_of_respectsIso @IsClosedImmersion _
    (SpecIso n (.of R)).inv,
    IsClosedImmersion.hasAffineProperty.SpecMap_iff_of_affineAnd RingHom.surjective_respectsIso,
    CommRingCat.hom_ofHom, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, ← AlgHom.range_eq_top,
    ← Algebra.adjoin_range_eq_range_aeval]

/-- `homOfAlgebra R y : Spec (.of A) ⟶ 𝔸(n; Spec (.of R))` is a finite morphism of schemes if and
only if `MvPolynomial.aeval y` is module-finite. -/
@[simp]
theorem isFinite_homOfAlgebra_iff {y : n → A} :
    IsFinite (homOfAlgebra R y) ↔ (MvPolynomial.aeval (R := R) y).Finite := by
  refine ⟨fun _ ↦ ?_, fun hfin ↦ ?_⟩
  · rw [AlgHom.Finite, ← CommRingCat.hom_ofHom (MvPolynomial.aeval (R := R) y).toRingHom,
      ← IsFinite.SpecMap_iff, ← homOfAlgebra_specIso_hom]
    infer_instance
  · have : IsFinite (Spec.map (CommRingCat.ofHom (MvPolynomial.aeval (R := R) y).toRingHom)) :=
      (IsFinite.SpecMap_iff _).mpr hfin
    rw [homOfAlgebra_def]
    infer_instance

/-- If `y : n → A` is algebraically independent over `R` and makes `A` integral over
`MvPolynomial n R`, then `homOfAlgebra R y : Spec (.of A) ⟶ 𝔸(n; Spec (.of R))` is surjective. -/
theorem surjective_homOfAlgebra {y : n → A}
    (hind : AlgebraicIndependent R y)
    (hint : (MvPolynomial.aeval (R := R) y).toRingHom.IsIntegral) :
    Surjective (homOfAlgebra R y) := by
  have : Surjective (Spec.map (CommRingCat.ofHom (MvPolynomial.aeval (R := R) y).toRingHom)) := by
    rw [surjective_iff]
    -- `Spec_carrier` identifies the carrier of `Spec (.of _)` with `PrimeSpectrum _` (no carrier
    -- equivalence exists in `Mathlib.AlgebraicGeometry.Scheme`); `Spec.map_apply` and
    -- `CommRingCat.hom_ofHom` then identify the underlying map with `PrimeSpectrum.comap`.
    intro q
    obtain ⟨p, hp⟩ := hint.comap_surjective (algebraicIndependent_iff_injective_aeval.mp hind) q
    exact ⟨p, (Spec.map_apply (CommRingCat.ofHom (MvPolynomial.aeval (R := R) y).toRingHom) p).trans
      (by rwa [CommRingCat.hom_ofHom])⟩
  rw [homOfAlgebra_def]
  infer_instance

end

end AlgebraicGeometry.AffineSpace
