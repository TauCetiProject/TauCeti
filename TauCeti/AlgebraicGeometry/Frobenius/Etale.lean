/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import TauCeti.AlgebraicGeometry.Frobenius.UniversalHomeomorphism
import TauCeti.AlgebraicGeometry.Morphisms.Etale

/-!
# The relative Frobenius of an étale morphism is an isomorphism

Let `p` be a prime, `S` a scheme in which `p` vanishes and `π : X ⟶ S` a morphism. The relative
Frobenius `F_{X/S} : X ⟶ X^{(p)} = X ×_{S, F_S} S` is always a universal homeomorphism, but in
general not an isomorphism: for the affine line it is `t ↦ t ^ p`. When `π` is étale, it is an
isomorphism, with no hypothesis on `S`; in particular `F_S` itself need not be an isomorphism.
Equivalently, the square formed by the absolute Frobenii of `X` and `S` and two copies of `π` is
cartesian. The same holds for the iterated relative Frobenius `F^n_{X/S}`.

The relative Frobenius of an étale morphism is a morphism between schemes étale over `S`, so it is
étale, and it is universally injective and surjective as a universal homeomorphism; an étale
universally injective surjective morphism is an isomorphism.

## Main results

* `AlgebraicGeometry.Scheme.Hom.isIso_iterateRelativeFrobenius_iff_isPullback` and
  `AlgebraicGeometry.Scheme.Hom.isIso_relativeFrobenius_iff_isPullback`: the (iterated) relative
  Frobenius of `π` is an isomorphism exactly when the square of absolute Frobenii over `π` is
  cartesian.
* Instances: for `π` étale, the relative Frobenius and its iterates are étale and isomorphisms.
* `AlgebraicGeometry.Scheme.Hom.isPullback_iterateFrobenius_of_etale` and
  `AlgebraicGeometry.Scheme.Hom.isPullback_frobenius_of_etale`: for `π` étale, the square of
  (iterated) absolute Frobenii over `π` is cartesian.
* `AlgebraicGeometry.Scheme.Hom.isPullback_relativeFrobenius_of_etale`: for an étale morphism
  `g : X ⟶ Y` over `S`, the relative Frobenius of `X` is the base change of that of `Y` along
  `g^{(p)} : X^{(p)} ⟶ Y^{(p)}`. This reduces properties of the relative Frobenius of a scheme
  étale over affine space to the affine space itself.
* `AlgebraicGeometry.Scheme.Hom.of_openCover_relativeFrobenius`: a property local on the target
  holds for the relative Frobenius of `X` once it holds for that of each member of an open cover.

## References

* The Stacks Project, [Tag 0EBS](https://stacks.math.columbia.edu/tag/0EBS): the relative
  Frobenius of an étale morphism is an isomorphism.
-/

public section

open CategoryTheory Limits

universe u

namespace AlgebraicGeometry.Scheme.Hom

variable {X S : Scheme.{u}} (π : X ⟶ S) (p : ℕ) [Fact p.Prime] (hS : (p : Γ(S, ⊤)) = 0)

/-- The iterated relative Frobenius `F^n_{X/S}` of `π` is an isomorphism exactly when the square
formed by the `n`-fold absolute Frobenii `F_X^n` and `F_S^n` and two copies of `π` is cartesian. -/
theorem isIso_iterateRelativeFrobenius_iff_isPullback (n : ℕ) :
    IsIso (π.iterateRelativeFrobenius p hS n) ↔
      IsPullback (X.iterateFrobenius p (natCast_eq_zero_of_hom π hS) n) π π
        (S.iterateFrobenius p hS n) := by
  have hsq : CommSq (X.iterateFrobenius p (natCast_eq_zero_of_hom π hS) n) π π
      (S.iterateFrobenius p hS n) := ⟨iterateFrobenius_naturality _ hS π n⟩
  refine ⟨fun _ ↦ .of_iso_pullback hsq (asIso (π.iterateRelativeFrobenius p hS n)) (by simp)
    (by simp), fun h ↦ ?_⟩
  -- the comparison isomorphism of `h` with the Frobenius twist is the iterated relative Frobenius
  convert (h.isoPullback.isIso_hom : IsIso h.isoPullback.hom)
  ext <;> simp

/-- The relative Frobenius `F_{X/S}` of `π` is an isomorphism exactly when the square formed by
the absolute Frobenii `F_X` and `F_S` and two copies of `π` is cartesian. -/
theorem isIso_relativeFrobenius_iff_isPullback :
    IsIso (π.relativeFrobenius p hS) ↔
      IsPullback (X.frobenius p (natCast_eq_zero_of_hom π hS)) π π (S.frobenius p hS) := by
  have hsq : CommSq (X.frobenius p (natCast_eq_zero_of_hom π hS)) π π (S.frobenius p hS) :=
    ⟨frobenius_naturality _ hS π⟩
  refine ⟨fun _ ↦ .of_iso_pullback hsq (asIso (π.relativeFrobenius p hS)) (by simp) (by simp),
    fun h ↦ ?_⟩
  -- the comparison isomorphism of `h` with the Frobenius twist is the relative Frobenius
  convert (h.isoPullback.isIso_hom : IsIso h.isoPullback.hom)
  ext <;> simp

variable [Etale π]

/-- The iterated relative Frobenius of an étale morphism is étale. -/
instance etale_iterateRelativeFrobenius (n : ℕ) : Etale (π.iterateRelativeFrobenius p hS n) :=
  -- its composite with the étale projection `X^{(p^n)} ⟶ S` is the étale morphism `π`
  have : Etale (π.iterateRelativeFrobenius p hS n ≫ pullback.snd _ _) := by
    rw [iterateRelativeFrobenius_snd]; infer_instance
  Etale.of_comp _ (pullback.snd _ _)

/-- The relative Frobenius of an étale morphism is étale. -/
instance etale_relativeFrobenius : Etale (π.relativeFrobenius p hS) :=
  -- its composite with the étale projection `X^{(p)} ⟶ S` is the étale morphism `π`
  have : Etale (π.relativeFrobenius p hS ≫ pullback.snd _ _) := by
    rw [relativeFrobenius_snd]; infer_instance
  Etale.of_comp _ (pullback.snd _ _)

/-- **The iterated relative Frobenius of an étale morphism is an isomorphism.** -/
instance isIso_iterateRelativeFrobenius (n : ℕ) : IsIso (π.iterateRelativeFrobenius p hS n) :=
  isIso_of_etale_of_universallyInjective_of_surjective _

/-- **The relative Frobenius of an étale morphism is an isomorphism.** Stacks, Tag 0EBS. -/
instance isIso_relativeFrobenius : IsIso (π.relativeFrobenius p hS) :=
  isIso_of_etale_of_universallyInjective_of_surjective _

/-- For `π : X ⟶ S` étale, the square formed by the `n`-fold absolute Frobenii `F_X^n` and `F_S^n`
and two copies of `π` is cartesian. -/
theorem isPullback_iterateFrobenius_of_etale (n : ℕ) :
    IsPullback (X.iterateFrobenius p (natCast_eq_zero_of_hom π hS) n) π π
      (S.iterateFrobenius p hS n) :=
  (π.isIso_iterateRelativeFrobenius_iff_isPullback p hS n).1 inferInstance

/-- For `π : X ⟶ S` étale, the square formed by the absolute Frobenii `F_X` and `F_S` and two
copies of `π` is cartesian. -/
theorem isPullback_frobenius_of_etale :
    IsPullback (X.frobenius p (natCast_eq_zero_of_hom π hS)) π π (S.frobenius p hS) :=
  (π.isIso_relativeFrobenius_iff_isPullback p hS).1 inferInstance

omit [Etale π]

variable {Y : Scheme.{u}} {π p}

/-- **The relative Frobenius is compatible with étale morphisms.** For an étale morphism
`g : X ⟶ Y` of schemes over `S`, the relative Frobenius of `X` is the base change of the relative
Frobenius of `Y` along the morphism `X^{(p)} ⟶ Y^{(p)}` induced by `g`. -/
theorem isPullback_relativeFrobenius_of_etale (πY : Y ⟶ S) (g : X ⟶ Y) [Etale g]
    (hg : g ≫ πY = π) :
    IsPullback (π.relativeFrobenius p hS) g
      (pullback.map π _ πY _ g (𝟙 S) (𝟙 S) (by simp [hg]) (by simp))
      (πY.relativeFrobenius p hS) := by
  -- the projections `X^{(p)} ⟶ X` and `Y^{(p)} ⟶ Y` form a cartesian square over `g`
  have hfst : IsPullback (pullback.fst π (S.frobenius p hS))
      (pullback.map π _ πY _ g (𝟙 S) (𝟙 S) (by simp [hg]) (by simp)) g
      (pullback.fst πY (S.frobenius p hS)) := by
    refine IsPullback.of_bot ?_ (by simp) (IsPullback.of_hasPullback πY (S.frobenius p hS))
    simpa [hg] using IsPullback.of_hasPullback π (S.frobenius p hS)
  -- composed with it, the square is the cartesian square of absolute Frobenii over `g`
  refine IsPullback.of_right ?_ (relativeFrobenius_naturality hS πY g hg) hfst
  simpa using isPullback_frobenius_of_etale g p (natCast_eq_zero_of_hom πY hS)

variable (π) in
/-- A property of morphisms that is local on the target holds for the relative Frobenius of `X`
once it holds for the relative Frobenius of every member of an open cover `𝒰` of `X`: the
Frobenius twists of the members of `𝒰` cover `X^{(p)}`, and over the twist of `𝒰.X i` the relative
Frobenius of `X` is that of `𝒰.X i`. -/
theorem of_openCover_relativeFrobenius (P : MorphismProperty Scheme.{u})
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

end AlgebraicGeometry.Scheme.Hom
