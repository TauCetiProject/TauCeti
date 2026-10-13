/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.Scheme.Geom.MulBy.Rank

/-!
# Transition maps between elliptic torsion schemes

Multiplication by `m` restricts to a homomorphism `E[mn] ⟶ E[n]`. This map is the base change
of `[m] : E ⟶ E` along `E[n] ⟶ E`, so for `m ≠ 0` it is finite locally free and surjective,
of rank `m²`. Its scheme-theoretic kernel is `E[m]`, included in `E[mn]` by the usual inclusion.
These statements hold over arbitrary bases, including in characteristics dividing `m` or `n`.

The case `m = p`, `n = p^r` supplies the faithfully flat transitions in the elliptic
`p`-divisible group. Both the inclusions and the transition maps commute with arbitrary base
change of the elliptic curve.

## References

* N. M. Katz and B. Mazur, *Arithmetic Moduli of Elliptic Curves*, 2.3.1 and Chapter 5.
-/

public section

open CategoryTheory Limits AlgebraicGeometry MonObj

universe u

namespace TauCeti.AlgebraicGeometry.EllipticCurveGeom

variable {S : Scheme.{u}} (E : EllipticCurveGeom S) (m n : ℤ)

/-- Multiplication by `m` restricted to `E[mn]`, with values in `E[n]`. -/
noncomputable def torsionMulBy : (E.torsion (m * n)).X ⟶ (E.torsion n).X :=
  torsionLift (E.torsionι (m * n) ≫ E.mulBy m) (by
    rw [Category.assoc, ← mulBy_mul, mul_comm n m, torsionι_mulBy])

/-- The transition `E[mn] ⟶ E[n]` sends a torsion point to its multiple by `m`. -/
@[reassoc (attr := simp)]
theorem torsionMulBy_torsionι :
    E.torsionMulBy m n ≫ E.torsionι n = E.torsionι (m * n) ≫ E.mulBy m :=
  torsionLift_torsionι _ _

/-- The torsion transition is a homomorphism of group schemes. -/
instance isMonHom_torsionMulBy : IsMonHom (E.torsionMulBy m n) where
  one_hom := torsion_hom_ext (by simp [-comp_mulBy])
  mul_hom := torsion_hom_ext (by simp [IsMonHom.mul_hom, -comp_mulBy])

/-- The inclusion of `E[m]` in `E[mn]`. -/
noncomputable def torsionInclusion : (E.torsion m).X ⟶ (E.torsion (m * n)).X :=
  torsionLift (E.torsionι m) (by
    rw [mul_comm m n, mulBy_mul, torsionι_mulBy_assoc, one_comp])

/-- The inclusion between torsion levels preserves the underlying point of `E`. -/
@[reassoc (attr := simp)]
theorem torsionInclusion_torsionι :
    E.torsionInclusion m n ≫ E.torsionι (m * n) = E.torsionι m :=
  torsionLift_torsionι _ _

/-- The inclusion between torsion levels is a homomorphism of group schemes. -/
instance isMonHom_torsionInclusion : IsMonHom (E.torsionInclusion m n) where
  one_hom := torsion_hom_ext (by simp [-comp_mulBy])
  mul_hom := torsion_hom_ext (by simp [IsMonHom.mul_hom, -comp_mulBy])

/-- The transition kills the included `m`-torsion. -/
@[reassoc (attr := simp)]
theorem torsionInclusion_torsionMulBy :
    E.torsionInclusion m n ≫ E.torsionMulBy m n = 1 :=
  torsion_hom_ext (by simp [torsionι_mulBy, -comp_mulBy])

/-- On schemes, the torsion transition is the restriction of multiplication by `m`. -/
@[reassoc (attr := simp)]
theorem torsionMulBy_left_torsionι :
    (E.torsionMulBy m n).left ≫ (E.torsionι n).left =
      (E.torsionι (m * n)).left ≫ (E.mulBy m).left :=
  congrArg Over.Hom.left (E.torsionMulBy_torsionι m n)

/-- On schemes, inclusions between torsion levels preserve the point of `E`. -/
@[reassoc (attr := simp)]
theorem torsionInclusion_left_torsionι :
    (E.torsionInclusion m n).left ≫ (E.torsionι (m * n)).left = (E.torsionι m).left :=
  congrArg Over.Hom.left (E.torsionInclusion_torsionι m n)

/-- The torsion transition is the base change of multiplication by `m` on `E`. -/
theorem isPullback_torsionMulBy :
    IsPullback (E.torsionι (m * n)).left (E.torsionMulBy m n).left
      (E.mulBy m).left (E.torsionι n).left := by
  refine (IsPullback.of_right ?_ ?_ (E.isPullback_torsion n).flip).flip
  · simpa only [← Over.comp_left, ← mulBy_mul, mul_comm n m, Over.w] using
      (E.isPullback_torsion (m * n)).flip
  · exact congrArg Over.Hom.left (E.torsionMulBy_torsionι m n)

/-- The kernel of `E[mn] ⟶ E[n]` is precisely the included `E[m]`, scheme-theoretically. -/
theorem isPullback_torsionInclusion :
    IsPullback (E.torsionInclusion m n).left (E.torsion m).X.hom
      (E.torsionMulBy m n).left (1 : Over.mk (𝟙 S) ⟶ (E.torsion n).X).left := by
  refine IsPullback.of_right ?_ ?_ (E.isPullback_torsionMulBy m n)
  · simpa only [← Over.comp_left, torsionInclusion_torsionι, one_comp,
      hom_one_left, Over.mk_hom, Category.id_comp, Category.id_comp E.zero] using
      E.isPullback_torsion m
  · rw [← Over.comp_left, torsionInclusion_torsionMulBy]
    simp [Hom.one_def]

/-- The inclusion between torsion levels is a closed immersion. -/
instance isClosedImmersion_torsionInclusion_left :
    IsClosedImmersion (E.torsionInclusion m n).left := by
  have : IsClosedImmersion
      ((E.torsionInclusion m n).left ≫ (E.torsionι (m * n)).left) := by
    rw [← Over.comp_left, torsionInclusion_torsionι]
    infer_instance
  exact .of_comp _ (E.torsionι (m * n)).left

/-- For `m ≠ 0`, the torsion transition is finite. -/
theorem isFinite_torsionMulBy_left (hm : m ≠ 0) :
    IsFinite (E.torsionMulBy m n).left :=
  MorphismProperty.of_isPullback (E.isPullback_torsionMulBy m n) (E.isFinite_mulBy_left hm)

/-- For `m ≠ 0`, the torsion transition is flat. -/
theorem flat_torsionMulBy_left (hm : m ≠ 0) : Flat (E.torsionMulBy m n).left :=
  MorphismProperty.of_isPullback (E.isPullback_torsionMulBy m n) (E.flat_mulBy_left hm)

/-- The torsion transition is locally of finite presentation, even when `m = 0`. -/
instance locallyOfFinitePresentation_torsionMulBy_left :
    LocallyOfFinitePresentation (E.torsionMulBy m n).left :=
  MorphismProperty.of_isPullback (E.isPullback_torsionMulBy m n) inferInstance

/-- For `m ≠ 0`, the torsion transition is surjective, without a characteristic restriction. -/
theorem surjective_torsionMulBy_left (hm : m ≠ 0) :
    Surjective (E.torsionMulBy m n).left :=
  MorphismProperty.of_isPullback (E.isPullback_torsionMulBy m n) (E.surjective_mulBy_left hm)

/-- Every fibre of the transition `E[mn] ⟶ E[n]` has length `m²`, for `m ≠ 0`. -/
@[simp]
theorem finrank_torsionMulBy_left (hm : m ≠ 0) (x : (E.torsion n).X.left) :
    (E.torsionMulBy m n).left.finrank x = m.natAbs ^ 2 := by
  have := E.isFinite_mulBy_left hm
  have := E.flat_mulBy_left hm
  rw [Scheme.Hom.finrank_of_isPullback _ _ _ _ (E.isPullback_torsionMulBy m n),
    E.finrank_mulBy_left hm]

section BaseChange

variable {S' : Scheme.{u}} {E} {E' : EllipticCurveGeom S'} {g : E'.carrier ⟶ E.carrier}
  {f : S' ⟶ S} (hg : IsPullback g E'.structureMap E.structureMap f)
  (h0 : E'.zero ≫ g = f ≫ E.zero)

/-- Inclusions between torsion levels commute with arbitrary base change. -/
@[reassoc]
theorem torsionInclusion_left_comp_torsionMap :
    (E'.torsionInclusion m n).left ≫ torsionMap (m * n) hg h0 =
      torsionMap m hg h0 ≫ (E.torsionInclusion m n).left := by
  apply (E.isPullback_torsion (m * n)).hom_ext
  · simp
  · simp [Over.w]

/-- Torsion transitions commute with arbitrary base change. -/
@[reassoc]
theorem torsionMulBy_left_comp_torsionMap :
    (E'.torsionMulBy m n).left ≫ torsionMap n hg h0 =
      torsionMap (m * n) hg h0 ≫ (E.torsionMulBy m n).left := by
  apply (E.isPullback_torsion n).hom_ext
  · simp [mulBy_left_comp_of_isPullback hg h0]
  · simp [Over.w]

end BaseChange

end TauCeti.AlgebraicGeometry.EllipticCurveGeom
