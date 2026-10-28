/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Frobenius.AffineSpace
public import TauCeti.AlgebraicGeometry.Morphisms.Smooth.EtaleCoordinates

/-!
# The relative Frobenius of a smooth morphism is finite locally free

Let `p` be a prime, `S` a scheme in which `p` vanishes and `π : X ⟶ S` a smooth morphism. The
relative Frobenius `F_{X/S} : X ⟶ X^{(p)} = X ×_{S, F_S} S` is finite, flat and locally of finite
presentation, that is, finite locally free. If `π` is smooth of relative dimension `n`, then
`F_{X/S}` has constant rank `p ^ n`. For the affine line this is the basis `1, t, …, t ^ (p - 1)`
of `𝒪_S[t]` over `𝒪_S[t ^ p]`; in particular the rank is `p`, not `1`, even though `F_{X/S}` is a
homeomorphism.

Near every point, a smooth morphism is étale over an affine space `𝔸(Fin n; S)`
(`AlgebraicGeometry.Smooth.exists_etale_affineSpace`). The open subschemes `V` of `X` carrying
such étale coordinates cover `X`, and their Frobenius twists `V^{(p)}` cover `X^{(p)}`. Over
`V^{(p)}` the relative Frobenius of `X` is that of `V`, because `V ⟶ X` is étale
(`AlgebraicGeometry.Scheme.Hom.isPullback_relativeFrobenius_of_etale`), and the relative Frobenius
of a scheme étale over `𝔸(Fin n; S)` is finite locally free of rank `p ^ n`
(`AlgebraicGeometry.AffineSpace.finrank_relativeFrobenius_of_etale`).

## Main results

* `AlgebraicGeometry.Scheme.Hom.flat_relativeFrobenius_of_smooth`,
  `AlgebraicGeometry.Scheme.Hom.isFinite_relativeFrobenius_of_smooth` and
  `AlgebraicGeometry.Scheme.Hom.locallyOfFinitePresentation_relativeFrobenius_of_smooth`: for
  smooth `π`, the relative Frobenius is flat, finite and locally of finite presentation.
* `AlgebraicGeometry.Scheme.Hom.finrank_relativeFrobenius_of_smoothOfRelativeDimension`: for `π`
  smooth of relative dimension `n`, the relative Frobenius has constant rank `p ^ n`.

## References

* The Stacks Project, [Tag 0CC6](https://stacks.math.columbia.edu/tag/0CC6), Frobenii.
* The Stacks Project, [Tag 054L](https://stacks.math.columbia.edu/tag/054L), étale coordinates
  on smooth morphisms.
-/

public section

open CategoryTheory Limits

universe u

namespace AlgebraicGeometry.Scheme.Hom

variable {X S : Scheme.{u}} (π : X ⟶ S) {p : ℕ} [Fact p.Prime] (hS : (p : Γ(S, ⊤)) = 0)

/-- A property of morphisms that is local on the target holds for the relative Frobenius of `X`
once it holds for the relative Frobenius of every member of an open cover `𝒰` of `X`: the
Frobenius twists of the members of `𝒰` cover `X^{(p)}`, and over the twist of `𝒰.X i` the relative
Frobenius of `X` is that of `𝒰.X i`. -/
private theorem of_openCover_relativeFrobenius (P : MorphismProperty Scheme.{u})
    [IsZariskiLocalAtTarget P] (𝒰 : X.OpenCover)
    (H : ∀ i, P ((𝒰.f i ≫ π).relativeFrobenius p hS)) : P (π.relativeFrobenius p hS) := by
  have key (i : 𝒰.I₀) : P (pullback.snd (π.relativeFrobenius p hS)
      (pullback.map (𝒰.f i ≫ π) (S.frobenius p hS) π (S.frobenius p hS) (𝒰.f i) (𝟙 S) (𝟙 S)
        (by simp) (by simp))) := by
    have h := (isPullback_relativeFrobenius_of_etale hS π (𝒰.f i) rfl).flip
    rw [← h.isoPullback_inv_snd, P.cancel_left_of_respectsIso]
    exact H i
  exact IsZariskiLocalAtTarget.of_openCover
    (Scheme.Pullback.openCoverOfLeft 𝒰 π (S.frobenius p hS)) fun i ↦ key i

/-- If an open cover `𝒰` of `X` carries étale coordinates `𝒰.X i ⟶ 𝔸(Fin n; S)` over `S`, all in
the same number `n` of variables, then the relative Frobenius of `X` has constant rank `p ^ n`. -/
private theorem finrank_relativeFrobenius_of_openCover [Flat (π.relativeFrobenius p hS)]
    [IsFinite (π.relativeFrobenius p hS)] (𝒰 : X.OpenCover) (n : ℕ)
    (g : ∀ i, 𝒰.X i ⟶ 𝔸(ULift.{u} (Fin n); S))
    (hg : ∀ i, Etale (g i) ∧ g i ≫ 𝔸(ULift.{u} (Fin n); S) ↘ S = 𝒰.f i ≫ π) :
    (π.relativeFrobenius p hS).finrank = fun _ ↦ p ^ n := by
  -- the rank at a point in the Frobenius twist of `𝒰.X i` is that of the relative Frobenius of
  -- `𝒰.X i`
  have key (i : 𝒰.I₀) (y : (pullback (𝒰.f i ≫ π) (S.frobenius p hS) : Scheme.{u})) :
      (π.relativeFrobenius p hS).finrank
        (pullback.map (𝒰.f i ≫ π) (S.frobenius p hS) π (S.frobenius p hS) (𝒰.f i) (𝟙 S) (𝟙 S)
        (by simp) (by simp) y) = p ^ n := by
    have := (hg i).1
    rw [← finrank_of_isPullback _ _ _ _
      (isPullback_relativeFrobenius_of_etale hS π (𝒰.f i) rfl).flip,
      AffineSpace.finrank_relativeFrobenius_of_etale hS (g i) (hg i).2, Nat.card_ulift,
      Nat.card_eq_fintype_card, Fintype.card_fin]
  ext y
  obtain ⟨i, y, rfl⟩ := (Scheme.Pullback.openCoverOfLeft 𝒰 π (S.frobenius p hS)).exists_eq y
  exact key i y

variable [Smooth π]

/-- A property of morphisms that is local on the target holds for the relative Frobenius of a
smooth morphism once it holds for the relative Frobenius of every scheme étale over an affine
space over `S`. -/
private theorem of_smooth_relativeFrobenius (P : MorphismProperty Scheme.{u})
    [IsZariskiLocalAtTarget P]
    (H : ∀ {V : Scheme.{u}} (πV : V ⟶ S) (n : ℕ) (g : V ⟶ 𝔸(ULift.{u} (Fin n); S)) [Etale g],
      g ≫ 𝔸(ULift.{u} (Fin n); S) ↘ S = πV → P (πV.relativeFrobenius p hS)) :
    P (π.relativeFrobenius p hS) := by
  choose V _ hxV n g hg using Smooth.exists_etale_affineSpace π
  refine of_openCover_relativeFrobenius π hS P (X.openCoverOfIsOpenCover V
    (top_le_iff.mp fun x _ ↦ TopologicalSpace.Opens.mem_iSup.mpr ⟨x, hxV x⟩)) fun x ↦
    @H _ _ _ (g x) (hg x).1 (hg x).2

/-- **The relative Frobenius of a smooth morphism is flat.** -/
instance flat_relativeFrobenius_of_smooth : Flat (π.relativeFrobenius p hS) :=
  have : IsZariskiLocalAtTarget @Flat.{u} :=
    HasRingHomProperty.instIsZariskiLocalAtTarget _ (Q := @RingHom.Flat)
  of_smooth_relativeFrobenius π hS @Flat fun _ _ g _ hg ↦
    AffineSpace.flat_relativeFrobenius_of_etale hS g hg

/-- **The relative Frobenius of a smooth morphism is finite.** -/
instance isFinite_relativeFrobenius_of_smooth : IsFinite (π.relativeFrobenius p hS) := by
  observe h : HasAffineProperty @IsFinite.{u}
    (fun X _ f _ ↦ IsAffine X ∧ RingHom.Finite (f.appTop).hom)
  have : IsZariskiLocalAtTarget @IsFinite.{u} := @HasAffineProperty.instIsZariskiLocalAtTarget _ _ h
  exact of_smooth_relativeFrobenius π hS @IsFinite fun _ _ g _ hg ↦
    AffineSpace.isFinite_relativeFrobenius_of_etale hS g hg

/-- **The relative Frobenius of a smooth morphism is locally of finite presentation.** -/
instance locallyOfFinitePresentation_relativeFrobenius_of_smooth :
    LocallyOfFinitePresentation (π.relativeFrobenius p hS) :=
  have : IsZariskiLocalAtTarget @LocallyOfFinitePresentation.{u} :=
    HasRingHomProperty.instIsZariskiLocalAtTarget _ (Q := @RingHom.FinitePresentation)
  of_smooth_relativeFrobenius π hS @LocallyOfFinitePresentation fun _ _ g _ hg ↦
    AffineSpace.locallyOfFinitePresentation_relativeFrobenius_of_etale hS g hg

omit [Smooth π] in
/-- **The relative Frobenius of a smooth morphism of relative dimension `n` has rank `p ^ n`.**
If `π : X ⟶ S` is smooth of relative dimension `n` over a scheme `S` in which `p` vanishes, then
its relative Frobenius `X ⟶ X^{(p)}`, which is finite locally free, has constant rank `p ^ n`. -/
theorem finrank_relativeFrobenius_of_smoothOfRelativeDimension (n : ℕ)
    [SmoothOfRelativeDimension n π] :
    (π.relativeFrobenius p hS).finrank = fun _ ↦ p ^ n := by
  have : Smooth π := SmoothOfRelativeDimension.smooth n π
  choose V _ hxV g hg using SmoothOfRelativeDimension.exists_etale_affineSpace π n
  exact finrank_relativeFrobenius_of_openCover π hS (X.openCoverOfIsOpenCover V
    (top_le_iff.mp fun x _ ↦ TopologicalSpace.Opens.mem_iSup.mpr ⟨x, hxV x⟩)) n g hg

end AlgebraicGeometry.Scheme.Hom
