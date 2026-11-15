/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.AffineSpace
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.Data.Matrix.Mul
public import Mathlib.RingTheory.AlgebraicIndependent.Defs
public import Mathlib.RingTheory.KrullDimension.Basic
import TauCeti.RingTheory.NoetherNormalization

/-!
# Linear projections of affine space and geometric Noether normalization

Given a matrix `C : Matrix m n Γ(S, ⊤)` of global functions on a base scheme `S` with `n` finite,
`AlgebraicGeometry.AffineSpace.linearMap S C : 𝔸(n; S) ⟶ 𝔸(m; S)` is the `S`-morphism pulling back
the `i`-th coordinate on `𝔸(m; S)` to `∑ j, (𝔸(n; S) ↘ S).appTop (C i j) * coord S j`. Formation of
`linearMap` is contravariant in matrix multiplication (`linearMap S (C * D) = linearMap S D ≫
linearMap S C`) and commutes with base change along `g : S' ⟶ S`.

Over an affine base `Spec R`, an `n`-tuple `x : n → A` in an `R`-algebra `A` induces the
`Spec R`-morphism `AlgebraicGeometry.AffineSpace.homOfTuple R x : Spec A ⟶ 𝔸(n; Spec R)`. It is a
closed immersion whenever `x` generates `A` over `R`
(`AlgebraicGeometry.AffineSpace.isClosedImmersion_homOfTuple_of_adjoin_eq_top`), finite if and only
if `MvPolynomial.aeval x` is module-finite, and surjective whenever `x` is algebraically independent
over `R` and `A` is integral over `R[x]`. Composing `homOfTuple R x` with `linearMap (Spec R)` for a
matrix `C` over `R` gives `homOfTuple R (fun i ↦ ∑ j, C i j • x j)`.

Combining this affine-space calculus with `TauCeti.exists_linear_normalization_of_fintype` yields
geometric linear Noether normalization over an infinite field `k`: for every nonempty closed
subscheme `ι : Z ⟶ 𝔸(n; Spec k)` with `n` finite, there exist `d ≤ Fintype.card n` and a matrix
`C : Matrix (ULift (Fin d)) n k` whose induced linear projection
`𝔸(n; Spec k) ⟶ 𝔸(ULift (Fin d); Spec k)` restricts on `Z` to a finite surjective morphism onto
`𝔸(ULift (Fin d); Spec k)` with `topologicalKrullDim Z = d`.

## Main declarations

* `AlgebraicGeometry.AffineSpace.linearMap`: the `S`-morphism `𝔸(n; S) ⟶ 𝔸(m; S)` induced by a
  matrix `C : Matrix m n Γ(S, ⊤)`.
* `AlgebraicGeometry.AffineSpace.homOfTuple`: the `Spec R`-morphism `Spec A ⟶ 𝔸(n; Spec R)`
  associated to a tuple `x : n → A` in an `R`-algebra `A`.
* `AlgebraicGeometry.AffineSpace.homOfTuple_linearMap`: composing `homOfTuple R x` with the linear
  morphism of `C` produces `homOfTuple R (fun i ↦ ∑ j, C i j • x j)`.
* `TauCeti.AlgebraicGeometry.exists_linear_normalization_homOfTuple`: geometric linear Noether
  normalization for a prescribed affine presentation `x : n → A` over an infinite field `k`.
* `TauCeti.AlgebraicGeometry.exists_linear_normalization_of_isClosedImmersion`: geometric linear
  Noether normalization for an arbitrary nonempty closed subscheme `ι : Z ⟶ 𝔸(n; Spec k)`.

## References

* [Stacks Project, Tag 00OW](https://stacks.math.columbia.edu/tag/00OW)
* J. S. Milne, *Algebraic Geometry*, v6.10, Proposition 2.42–Remark 2.47
-/

public section

open CategoryTheory Limits MvPolynomial

noncomputable section

namespace AlgebraicGeometry.AffineSpace

universe u

section LinearMap

variable {l m n : Type u} [Fintype n] (S : Scheme.{u})

/-- The `S`-morphism `𝔸(n; S) ⟶ 𝔸(m; S)` of affine spaces induced by a matrix
`C : Matrix m n Γ(S, ⊤)` of global sections on `S`, pulling back `coord S i` to
`∑ j, (𝔸(n; S) ↘ S).appTop (C i j) * coord S j`. -/
def linearMap (C : Matrix m n Γ(S, ⊤)) : 𝔸(n; S) ⟶ 𝔸(m; S) :=
  homOfVector (𝔸(n; S) ↘ S) fun i ↦ ∑ j, (𝔸(n; S) ↘ S).appTop (C i j) * coord S j

/-- Defining expression of `linearMap` in terms of `homOfVector`. -/
lemma linearMap_def (C : Matrix m n Γ(S, ⊤)) :
    linearMap S C =
      homOfVector (𝔸(n; S) ↘ S) fun i ↦ ∑ j, (𝔸(n; S) ↘ S).appTop (C i j) * coord S j :=
  (rfl)

instance (C : Matrix m n Γ(S, ⊤)) : (linearMap S C).IsOver S := by
  rw [linearMap_def]
  infer_instance

@[reassoc]
lemma linearMap_over (C : Matrix m n Γ(S, ⊤)) :
    linearMap S C ≫ 𝔸(m; S) ↘ S = 𝔸(n; S) ↘ S :=
  homOfVector_over _ _

@[simp]
lemma linearMap_appTop_coord (C : Matrix m n Γ(S, ⊤)) (i : m) :
    (linearMap S C).appTop (coord S i) = ∑ j, (𝔸(n; S) ↘ S).appTop (C i j) * coord S j :=
  homOfVector_appTop_coord _ _ i

variable {S}

/-- Composing a point `homOfVector f v : X ⟶ 𝔸(n; S)` with `linearMap S C` transforms its
coordinates by the pulled-back matrix `C.map f.appTop`. -/
@[reassoc]
lemma homOfVector_linearMap {X : Scheme.{u}} (f : X ⟶ S) (v : n → Γ(X, ⊤))
    (C : Matrix m n Γ(S, ⊤)) :
    homOfVector f v ≫ linearMap S C =
      homOfVector f fun i ↦ ∑ j, f.appTop (C i j) * v j := by
  apply hom_ext
  · simp
  · intro i
    have hcoeff : ∀ j, (homOfVector f v).appTop ((𝔸(n; S) ↘ S).appTop (C i j)) =
        f.appTop (C i j) := fun j ↦ by
      rw [← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop, homOfVector_over]
    simp only [Scheme.Hom.comp_appTop, CommRingCat.comp_apply, linearMap_appTop_coord,
      homOfVector_appTop_coord, map_sum, map_mul, hcoeff]

@[simp]
lemma linearMap_zero :
    linearMap S (0 : Matrix m n Γ(S, ⊤)) = homOfVector (𝔸(n; S) ↘ S) 0 := by
  apply hom_ext <;> simp

@[simp]
lemma linearMap_one [DecidableEq n] :
    linearMap S (1 : Matrix n n Γ(S, ⊤)) = 𝟙 𝔸(n; S) := by
  apply hom_ext <;> simp [Matrix.one_apply]

/-- `linearMap` is contravariantly functorial with respect to matrix multiplication. -/
@[reassoc]
lemma linearMap_mul [Fintype m] (C : Matrix l m Γ(S, ⊤)) (D : Matrix m n Γ(S, ⊤)) :
    linearMap S (C * D) = linearMap S D ≫ linearMap S C := by
  apply hom_ext
  · simp
  · intro i
    have hcoeff : ∀ k, (linearMap S D).appTop ((𝔸(m; S) ↘ S).appTop (C i k)) =
        (𝔸(n; S) ↘ S).appTop (C i k) := fun k ↦ by
      rw [← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop, linearMap_over]
    simp only [Scheme.Hom.comp_appTop, CommRingCat.comp_apply, linearMap_appTop_coord,
      Matrix.mul_apply, map_sum, map_mul, hcoeff, Finset.sum_mul, Finset.mul_sum, mul_assoc]
    exact Finset.sum_comm

/-- Formation of `linearMap` commutes with base change along `g : S' ⟶ S`. -/
@[reassoc]
lemma map_linearMap {S' : Scheme.{u}} (g : S' ⟶ S) (C : Matrix m n Γ(S, ⊤)) :
    map n g ≫ linearMap S C = linearMap S' (C.map g.appTop) ≫ map m g := by
  apply hom_ext
  · simp
  · intro i
    have hcoeff : ∀ j, (map n g).appTop ((𝔸(n; S) ↘ S).appTop (C i j)) =
        (𝔸(n; S') ↘ S').appTop (g.appTop (C i j)) := fun j ↦ by
      rw [← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop, map_over,
        Scheme.Hom.comp_appTop, CommRingCat.comp_apply]
    simp only [Scheme.Hom.comp_appTop, CommRingCat.comp_apply, linearMap_appTop_coord,
      map_appTop_coord, Matrix.map_apply, map_sum, map_mul, hcoeff]

/-- Over an affine base `Spec R`, `linearMap` corresponds under `SpecIso` to `Spec.map` of the
`R`-algebra homomorphism sending `X i` to `∑ j, C i j • X j`. -/
lemma linearMap_Spec (R : CommRingCat.{u}) (C : Matrix m n R) :
    linearMap (Spec R) (C.map (Scheme.ΓSpecIso R).inv) =
      (SpecIso n R).hom ≫
        Spec.map (CommRingCat.ofHom
          (MvPolynomial.aeval (fun i ↦ ∑ j, MvPolynomial.C (C i j) * MvPolynomial.X j)).toRingHom) ≫
        (SpecIso m R).inv := by
  rw [← Iso.inv_comp_eq]
  apply hom_ext
  · simp only [linearMap_over, Category.assoc, SpecIso_inv_over, ← Spec.map_comp,
      ← CommRingCat.ofHom_comp]
    congr 2
    ext r
    simp
  · intro i
    have hC : ∀ j,
        (SpecIso n R).inv.appTop
          ((𝔸(n; Spec R) ↘ Spec R).appTop ((Scheme.ΓSpecIso R).inv (C i j))) =
          (Scheme.ΓSpecIso (.of (MvPolynomial n R))).inv (MvPolynomial.C (C i j)) := fun j ↦ by
      rw [← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop, SpecIso_inv_over,
        ← CommRingCat.comp_apply, ← Scheme.ΓSpecIso_inv_naturality]
      rfl
    have hsum :
        (Spec.map (CommRingCat.ofHom
          (MvPolynomial.aeval
            (fun i ↦ ∑ j, MvPolynomial.C (C i j) * MvPolynomial.X j)).toRingHom)).appTop
          ((SpecIso m R).inv.appTop (coord (Spec R) i)) =
          (Scheme.ΓSpecIso (.of (MvPolynomial n R))).inv
            (∑ j, MvPolynomial.C (C i j) * MvPolynomial.X j) := by
      rw [SpecIso_inv_appTop_coord, ← CommRingCat.comp_apply, ← Scheme.ΓSpecIso_inv_naturality,
        CommRingCat.comp_apply]
      simp
    rw [Scheme.Hom.comp_appTop, CommRingCat.comp_apply, Scheme.Hom.comp_appTop,
      CommRingCat.comp_apply, hsum]
    simp only [linearMap_appTop_coord, Matrix.map_apply, map_sum, map_mul,
      SpecIso_inv_appTop_coord, hC]

end LinearMap

section HomOfTuple

variable (R : Type u) [CommRing R] {A m n : Type u} [CommRing A] [Algebra R A]

/-- For an `R`-algebra `A` and an `n`-tuple `x : n → A`, `homOfTuple R x` is the induced
`Spec (.of R)`-morphism `Spec (.of A) ⟶ 𝔸(n; Spec (.of R))` corresponding under `SpecIso` to
`MvPolynomial.aeval x : MvPolynomial n R →ₐ[R] A`. -/
def homOfTuple (x : n → A) : Spec (.of A) ⟶ 𝔸(n; Spec (.of R)) :=
  Spec.map (CommRingCat.ofHom (MvPolynomial.aeval (R := R) x).toRingHom) ≫
    (SpecIso n (.of R)).inv

/-- Defining expression of `homOfTuple` via `Spec.map` and `(SpecIso n (.of R)).inv`. -/
lemma homOfTuple_def (x : n → A) :
    homOfTuple R x =
      Spec.map (CommRingCat.ofHom (MvPolynomial.aeval (R := R) x).toRingHom) ≫
        (SpecIso n (.of R)).inv :=
  (rfl)

@[reassoc (attr := simp)]
lemma homOfTuple_SpecIso_hom (x : n → A) :
    homOfTuple R x ≫ (SpecIso n (.of R)).hom =
      Spec.map (CommRingCat.ofHom (MvPolynomial.aeval (R := R) x).toRingHom) := by
  simp [homOfTuple_def]

@[reassoc (attr := simp)]
lemma homOfTuple_over (x : n → A) :
    homOfTuple R x ≫ 𝔸(n; Spec (.of R)) ↘ Spec (.of R) =
      Spec.map (CommRingCat.ofHom (algebraMap R A)) := by
  rw [homOfTuple_def, Category.assoc, SpecIso_inv_over, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  congr 2
  ext r
  simp

@[simp]
lemma homOfTuple_appTop_coord (x : n → A) (j : n) :
    (homOfTuple R x).appTop (coord (Spec (.of R)) j) =
      (Scheme.ΓSpecIso (.of A)).inv (x j) := by
  rw [homOfTuple_def, Scheme.Hom.comp_appTop, CommRingCat.comp_apply, SpecIso_inv_appTop_coord,
    ← CommRingCat.comp_apply, ← Scheme.ΓSpecIso_inv_naturality, CommRingCat.comp_apply]
  simp

/-- `homOfTuple R x` agrees with `homOfVector` applied to the structure morphism
`Spec (.of A) ⟶ Spec (.of R)` and the global sections corresponding to `x`. -/
lemma homOfTuple_eq_homOfVector (x : n → A) :
    homOfTuple R x =
      homOfVector (Spec.map (CommRingCat.ofHom (algebraMap R A)))
        fun j ↦ (Scheme.ΓSpecIso (.of A)).inv (x j) := by
  apply hom_ext <;> simp

/-- Composing `homOfTuple R x` with the linear projection defined by `C : Matrix m n R` yields
`homOfTuple R` for the transformed tuple `fun i ↦ ∑ j, C i j • x j`. -/
@[reassoc]
lemma homOfTuple_linearMap [Fintype n] (x : n → A) (C : Matrix m n R) :
    homOfTuple R x ≫ linearMap (Spec (.of R)) (C.map (Scheme.ΓSpecIso (.of R)).inv) =
      homOfTuple R fun i ↦ ∑ j, C i j • x j := by
  rw [homOfTuple_eq_homOfVector, homOfVector_linearMap, homOfTuple_eq_homOfVector]
  congr 1
  ext i
  simp only [Matrix.map_apply, map_sum]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  have halg :
      (Spec.map (CommRingCat.ofHom (algebraMap R A))).appTop
        ((Scheme.ΓSpecIso (.of R)).inv (C i j)) =
        (Scheme.ΓSpecIso (.of A)).inv (algebraMap R A (C i j)) := by
    rw [← CommRingCat.comp_apply, ← Scheme.ΓSpecIso_inv_naturality]
    rfl
  rw [halg, Algebra.smul_def, map_mul]

variable {R}

/-- When `x : n → A` generates `A` as an `R`-algebra,
`homOfTuple R x : Spec (.of A) ⟶ 𝔸(n; Spec (.of R))` is a closed immersion. -/
theorem isClosedImmersion_homOfTuple_of_adjoin_eq_top {x : n → A}
    (hx : Algebra.adjoin R (Set.range x) = ⊤) :
    IsClosedImmersion (homOfTuple R x) := by
  have hsurj : Function.Surjective (MvPolynomial.aeval (R := R) x) := by
    rwa [← AlgHom.range_eq_top, MvPolynomial.aeval_range]
  have := IsClosedImmersion.spec_of_surjective
    (CommRingCat.ofHom (MvPolynomial.aeval (R := R) x).toRingHom) fun b ↦ hsurj b
  rw [homOfTuple_def]
  infer_instance

/-- `homOfTuple R x` is a finite morphism of schemes if and only if `MvPolynomial.aeval x` is a
module-finite ring homomorphism. -/
theorem isFinite_homOfTuple_iff {x : n → A} :
    IsFinite (homOfTuple R x) ↔ (MvPolynomial.aeval (R := R) x).Finite := by
  constructor
  · intro h
    have hcomp : IsFinite (homOfTuple R x ≫ (SpecIso n (.of R)).hom) := inferInstance
    rwa [homOfTuple_SpecIso_hom, IsFinite.SpecMap_iff] at hcomp
  · intro h
    have : IsFinite (Spec.map (CommRingCat.ofHom (MvPolynomial.aeval (R := R) x).toRingHom)) :=
      (IsFinite.SpecMap_iff _).mpr h
    rw [homOfTuple_def]
    infer_instance

/-- When `x : n → A` is algebraically independent over `R` and `A` is integral over `R[x]`,
`homOfTuple R x : Spec (.of A) ⟶ 𝔸(n; Spec (.of R))` is surjective. -/
theorem surjective_homOfTuple_of_algebraicIndependent_of_isIntegral {x : n → A}
    (hind : AlgebraicIndependent R x)
    (hint : (MvPolynomial.aeval (R := R) x).toRingHom.IsIntegral) :
    Surjective (homOfTuple R x) := by
  rw [homOfTuple_def, MorphismProperty.cancel_right_of_respectsIso (P := @Surjective)]
  exact ⟨hint.comap_surjective hind⟩

end HomOfTuple

end AlgebraicGeometry.AffineSpace

namespace TauCeti.AlgebraicGeometry

open _root_.AlgebraicGeometry

universe u

/-- **Geometric linear Noether normalization for a prescribed affine presentation.** Let `A` be a
nontrivial algebra over an infinite field `k`, generated as a `k`-algebra by a finite tuple
`x : n → A`. Then there exist `d ≤ Fintype.card n` and `C : Matrix (ULift.{u} (Fin d)) n k` such
that `AffineSpace.homOfTuple k x` composed with `AffineSpace.linearMap` of `C` is finite and
surjective onto `𝔸(ULift.{u} (Fin d); Spec (.of k))` and
`topologicalKrullDim (Spec (.of A)) = d`. -/
@[stacks 00OW]
theorem exists_linear_normalization_homOfTuple {k A n : Type u} [Field k] [Infinite k]
    [CommRing A] [Nontrivial A] [Algebra k A] [Fintype n]
    (x : n → A) (hx : Algebra.adjoin k (Set.range x) = ⊤) :
    ∃ (d : ℕ) (_ : d ≤ Fintype.card n) (C : Matrix (ULift.{u} (Fin d)) n k),
      let π := AffineSpace.homOfTuple k x ≫
        AffineSpace.linearMap (Spec (.of k)) (C.map (Scheme.ΓSpecIso (.of k)).inv)
      IsFinite π ∧ Surjective π ∧ topologicalKrullDim (Spec (.of A)) = (d : WithBot ℕ∞) := by
  obtain ⟨d, hd, C₀, hind₀, hfin₀, hdim⟩ := TauCeti.exists_linear_normalization_of_fintype x hx
  let e : ULift.{u} (Fin d) ≃ Fin d := Equiv.ulift
  let C : Matrix (ULift.{u} (Fin d)) n k := C₀.submatrix e id
  refine ⟨d, hd, C, ?_⟩
  set y₀ : Fin d → A := fun i ↦ ∑ j, C₀ i j • x j
  set y : ULift.{u} (Fin d) → A := fun i ↦ ∑ j, C i j • x j
  have hy : y = y₀ ∘ e := rfl
  have hind : AlgebraicIndependent k y := (algebraicIndependent_equiv' e hy.symm).mpr hind₀
  have haeval : MvPolynomial.aeval (R := k) y =
      (MvPolynomial.aeval (R := k) y₀).comp (MvPolynomial.renameEquiv k e).toAlgHom := by
    ext i
    simp [hy]
  have hfin : (MvPolynomial.aeval (R := k) y).Finite := by
    rw [AlgHom.Finite, haeval, AlgHom.toRingHom_eq_coe, AlgHom.comp_toRingHom]
    exact RingHom.Finite.comp hfin₀ (MvPolynomial.renameEquiv k e).toRingEquiv.finite
  dsimp only
  rw [AffineSpace.homOfTuple_linearMap]
  refine ⟨AffineSpace.isFinite_homOfTuple_iff.mpr hfin,
    AffineSpace.surjective_homOfTuple_of_algebraicIndependent_of_isIntegral hind hfin.to_isIntegral,
    ?_⟩
  exact (PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim A).trans hdim

/-- **Geometric linear Noether normalization for a closed subscheme of affine space.** Let `Z` be a
nonempty scheme equipped with a closed immersion `ι : Z ⟶ 𝔸(n; Spec (.of k))` over an infinite
field `k`, with `n` finite. Then there exist `d ≤ Fintype.card n` and a matrix
`C : Matrix (ULift.{u} (Fin d)) n k` such that `ι` composed with the linear projection
`AffineSpace.linearMap` of `C` is finite and surjective onto `𝔸(ULift.{u} (Fin d); Spec (.of k))`,
and `topologicalKrullDim Z = d`. -/
@[stacks 00OW]
theorem exists_linear_normalization_of_isClosedImmersion {k n : Type u} [Field k] [Infinite k]
    [Fintype n] {Z : Scheme.{u}} [Nonempty Z] (ι : Z ⟶ 𝔸(n; Spec (.of k)))
    [IsClosedImmersion ι] :
    ∃ (d : ℕ) (_ : d ≤ Fintype.card n) (C : Matrix (ULift.{u} (Fin d)) n k),
      let π := ι ≫ AffineSpace.linearMap (Spec (.of k)) (C.map (Scheme.ΓSpecIso (.of k)).inv)
      IsFinite π ∧ Surjective π ∧ topologicalKrullDim Z = (d : WithBot ℕ∞) := by
  obtain ⟨I, e, he⟩ :=
    (IsClosedImmersion.Spec_iff (f := ι ≫ (AffineSpace.SpecIso n (.of k)).hom)).mp inferInstance
  set A := MvPolynomial n k ⧸ I
  have hSpec_nonempty : Nonempty (Spec (.of A)) := Nonempty.map e.hom ‹Nonempty Z›
  have : Nontrivial A := by
    by_contra hsub
    rw [not_nontrivial_iff_subsingleton] at hsub
    exact isEmpty_iff.mp (inferInstance : IsEmpty (PrimeSpectrum A)) hSpec_nonempty.some
  let x : n → A := fun j ↦ Ideal.Quotient.mk I (MvPolynomial.X j)
  have haeval : MvPolynomial.aeval (R := k) x = Ideal.Quotient.mkₐ k I := by
    ext j
    exact MvPolynomial.aeval_X x j
  have hx : Algebra.adjoin k (Set.range x) = ⊤ := by
    rw [← MvPolynomial.aeval_range, haeval, AlgHom.range_eq_top]
    exact Ideal.Quotient.mk_surjective
  have hι : ι = e.hom ≫ AffineSpace.homOfTuple k x := by
    rw [← Iso.eq_comp_inv] at he
    rw [he, Category.assoc, AffineSpace.homOfTuple_def, haeval]
    rfl
  obtain ⟨d, hd, C, hfin, hsurj, hdim⟩ := exists_linear_normalization_homOfTuple x hx
  refine ⟨d, hd, C, ?_⟩
  dsimp only
  rw [hι, Category.assoc]
  exact ⟨inferInstance, inferInstance,
    e.hom.homeomorph.isHomeomorph.topologicalKrullDim_eq.trans hdim⟩

end TauCeti.AlgebraicGeometry
