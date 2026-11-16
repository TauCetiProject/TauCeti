/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import TauCeti.AlgebraicGeometry.RationalPoint.Count
import TauCeti.RingTheory.FiniteType.AlgHom

/-!
# Finiteness of the points of a scheme of finite type with values in a finite field

Let `k` be a commutative ring and `a : X ⟶ Spec k` a quasi-compact morphism locally of finite
type, for instance a scheme of finite type over a finite field. For every finite field `L` over
`k`, the set of `L`-valued points of `X` over `Spec k` is finite
(`AlgebraicGeometry.Scheme.Hom.finite_points`). In particular the point count
`AlgebraicGeometry.Scheme.Hom.numberOfRationalPoints` of a scheme of finite type over a finite
field `k` is the honest number of its points over every finite extension of `k`, rather than the
value `0` that `Nat.card` assigns to an infinite set.

On an affine scheme `Spec R` over `Spec k` the `L`-valued points are the `k`-algebra maps
`R →ₐ[k] L` (`AlgebraicGeometry.Spec.homEquivAlgHom`). There are finitely many of them when `R` is
of finite type over `k`, since such a map is determined by its values on finitely many generators
(`Algebra.FiniteType.finite_algHom`). In general `X` is covered by finitely many affine opens, and
since `Spec L` has a single point, every `L`-valued point factors through one of them.

## Main results

* `AlgebraicGeometry.Scheme.Hom.finite_points`: a quasi-compact scheme locally of finite type over
  `Spec k` has finitely many points with values in a finite field.
* `AlgebraicGeometry.Scheme.Hom.numberOfRationalPoints_pos_iff`: under the same hypotheses the
  point count is positive exactly when some point exists.

## References

* P. Deligne, *Cohomologie étale (SGA 4½)*, Rapport, §1, for the count of rational points of a
  scheme of finite type over a finite field.
-/

public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Scheme.Hom

variable {k : Type u} [CommRing k] {L : Type u} [Field L] [Algebra k L] [Finite L]

/-- An affine scheme locally of finite type over `Spec k` has finitely many points with values in
a finite field: they are the `k`-algebra maps out of its coordinate ring. -/
private theorem finite_points_of_isAffine {Y : Scheme.{u}} [IsAffine Y] (b : Y ⟶ Spec (.of k))
    [LocallyOfFiniteType b] :
    Finite {y : Spec (.of L) ⟶ Y // y ≫ b = Spec.map (CommRingCat.ofHom (algebraMap k L))} := by
  -- Read `Y` as `Spec Γ(Y, ⊤)`, with the `k`-algebra structure given by `b`.
  let φ := Spec.preimage (Y.isoSpec.inv ≫ b)
  let _ : Algebra k Γ(Y, ⊤) := φ.hom.toAlgebra
  have hb : Y.isoSpec.inv ≫ b = Spec.algebraMap k Γ(Y, ⊤) := (Spec.map_preimage _).symm
  have : Algebra.FiniteType k Γ(Y, ⊤) := by
    have : LocallyOfFiniteType (Spec.map φ) := by
      rw [Spec.map_preimage]
      infer_instance
    exact HasRingHomProperty.Spec_iff.mp this
  refine Finite.of_injective
    (fun y ↦ Spec.homEquivAlgHom ⟨y.1 ≫ Y.isoSpec.hom, by rw [Category.assoc, ← hb,
      Iso.hom_inv_id_assoc, y.2]⟩) fun y y' h ↦ ?_
  have := congrArg Subtype.val (Spec.homEquivAlgHom.injective h)
  exact Subtype.ext ((cancel_mono Y.isoSpec.hom).mp this)

/-- **A scheme of finite type has finitely many points with values in a finite field.** Let
`a : X ⟶ Spec k` be quasi-compact and locally of finite type, and let `L` be a finite field over
`k`. Then `X` has only finitely many `L`-valued points over `Spec k`. -/
theorem finite_points {X : Scheme.{u}} (a : X ⟶ Spec (.of k)) [QuasiCompact a]
    [LocallyOfFiniteType a] :
    Finite {x : Spec (.of L) ⟶ X // x ≫ a = Spec.map (CommRingCat.ofHom (algebraMap k L))} := by
  have := QuasiCompact.compactSpace_of_compactSpace a
  let 𝒰 : X.OpenCover := X.affineCover.finiteSubcover
  -- the points factoring through the `i`-th affine open of the finite cover
  let g (i : 𝒰.I₀)
      (y : {y : Spec (.of L) ⟶ 𝒰.X i //
        y ≫ 𝒰.f i ≫ a = Spec.map (CommRingCat.ofHom (algebraMap k L))}) :
      {x : Spec (.of L) ⟶ X // x ≫ a = Spec.map (CommRingCat.ofHom (algebraMap k L))} :=
    ⟨y.1 ≫ 𝒰.f i, by rw [Category.assoc, y.2]⟩
  have (i : 𝒰.I₀) := finite_points_of_isAffine (L := L) (𝒰.f i ≫ a)
  refine Set.finite_univ_iff.mp <| (Set.finite_iUnion fun i ↦ Set.finite_range (g i)).subset
    fun x _ ↦ ?_
  -- `Spec L` has a single point, so `x` factors through the open containing its image.
  let i := 𝒰.idx (x.1 default)
  have hx : Set.range x.1 ⊆ Set.range (𝒰.f i) := by
    rintro _ ⟨p, rfl⟩
    rw [Subsingleton.elim p default]
    exact 𝒰.covers _
  refine Set.mem_iUnion.mpr ⟨i, ⟨IsOpenImmersion.lift (𝒰.f i) x.1 hx, ?_⟩, ?_⟩
  · rw [IsOpenImmersion.lift_fac_assoc, x.2]
  · exact Subtype.ext (IsOpenImmersion.lift_fac _ _ _)

/-- For a quasi-compact scheme locally of finite type over `Spec k` and a finite field `L` over
`k`, the number of `L`-valued points is positive exactly when there is an `L`-valued point. -/
theorem numberOfRationalPoints_pos_iff {X : Scheme.{u}} (a : X ⟶ Spec (.of k)) [QuasiCompact a]
    [LocallyOfFiniteType a] :
    0 < a.numberOfRationalPoints L ↔
      ∃ x : Spec (.of L) ⟶ X, x ≫ a = Spec.map (CommRingCat.ofHom (algebraMap k L)) := by
  have := finite_points (L := L) a
  rw [numberOfRationalPoints_def, Nat.card_pos_iff, nonempty_subtype]
  exact and_iff_left this

end AlgebraicGeometry.Scheme.Hom
