/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.AffineSpace
public import Mathlib.AlgebraicGeometry.Morphisms.FlatRank
public import TauCeti.AlgebraicGeometry.Frobenius.Etale
import Mathlib.Algebra.Field.ULift
import TauCeti.AlgebraicGeometry.Frobenius.Iterate
import TauCeti.RingTheory.MvPolynomial.Expand

/-!
# The relative Frobenius of affine space is finite locally free

Let `p` be a prime and `S` a scheme in which `p` vanishes. The relative Frobenius
`F : 𝔸(σ; S) ⟶ 𝔸(σ; S)^{(p)}` of affine space over `S` is, in coordinates, `X_i ↦ X_i ^ p`. This
file proves that it is finite locally free of rank `p ^ n` when `σ` has `n` elements: it is
finite, flat and locally of finite presentation, and its rank is `p ^ n` at every point. It is
flat for an arbitrary set of variables `σ`.

The same holds for every `S`-scheme `X` with an étale morphism `X ⟶ 𝔸(σ; S)` over `S`, since the
relative Frobenius of `X` is a base change of that of `𝔸(σ; S)`
(`AlgebraicGeometry.Scheme.Hom.isPullback_relativeFrobenius_of_etale`). A smooth morphism of
relative dimension `n` is locally of this form, so this is the local computation of the rank of
the relative Frobenius of a smooth morphism.

Over `𝔽_p` the Frobenius of `𝔽_p` is the identity, the Frobenius twist of `𝔸(σ; 𝔽_p)` is
`𝔸(σ; 𝔽_p)` itself and the relative Frobenius is `Spec` of `MvPolynomial.expand p`, which is
free of rank `p ^ n` (`TauCeti.MvPolynomial.finrank_expand`). For a general `S`, the relative
Frobenius of `𝔸(σ; S)` is the base change of that of `𝔸(σ; 𝔽_p)` along `S ⟶ Spec 𝔽_p`
(`AlgebraicGeometry.Scheme.Hom.isPullback_relativeFrobenius_of_isPullback`).

## Main results

* `AlgebraicGeometry.AffineSpace.flat_relativeFrobenius`,
  `AlgebraicGeometry.AffineSpace.isFinite_relativeFrobenius` and
  `AlgebraicGeometry.AffineSpace.locallyOfFinitePresentation_relativeFrobenius`: the relative
  Frobenius of `𝔸(σ; S)` is flat, and finite and locally of finite presentation for finite `σ`.
* `AlgebraicGeometry.AffineSpace.finrank_relativeFrobenius`: its rank is `p ^ Nat.card σ`.
* `AlgebraicGeometry.AffineSpace.finrank_relativeFrobenius_of_etale` and its companions: the same
  for the relative Frobenius of an `S`-scheme étale over `𝔸(σ; S)`.

## References

* The Stacks Project, [Tag 0CC6](https://stacks.math.columbia.edu/tag/0CC6), Frobenii.
-/

public section

open CategoryTheory Limits MorphismProperty

universe u

namespace AlgebraicGeometry.AffineSpace

open Scheme

variable (σ : Type u) {S : Scheme.{u}} {p : ℕ} [Fact p.Prime]

/-- The structure morphism `S ⟶ Spec 𝔽_p` of a scheme in which `p` vanishes. -/
private noncomputable def toSpecPrimeField (hS : (p : Γ(S, ⊤)) = 0) :
    S ⟶ Spec (.of (ULift.{u} (ZMod p))) :=
  S.toSpecΓ ≫ Spec.map (CommRingCat.ofHom <|
    (ZMod.castHom (ringChar.dvd hS) Γ(S, ⊤)).comp ULift.ringEquiv.toRingHom)

/-- The absolute Frobenius of `Spec 𝔽_p` is the identity. -/
private theorem frobenius_spec_primeField :
    (Spec (.of (ULift.{u} (ZMod p)))).frobenius p (natCast_spec_eq_zero _) = 𝟙 _ := by
  rw [← Spec_map_powRingHom _ (CharP.cast_eq_zero _ p)]
  convert Spec.map_id (CommRingCat.of (ULift.{u} (ZMod p)))
  ext x
  simp [TauCeti.powRingHom_apply, ZMod.pow_card]

/-- The absolute Frobenius of `Spec 𝔽_p[X_i]` is `Spec` of `expand p`. -/
private theorem frobenius_spec_mvPolynomial :
    (Spec (.of (MvPolynomial σ (ULift.{u} (ZMod p))))).frobenius p (natCast_spec_eq_zero _) =
      Spec.map (CommRingCat.ofHom
        (MvPolynomial.expand p : MvPolynomial σ (ULift.{u} (ZMod p)) →ₐ[_] _).toRingHom) := by
  rw [← Spec_map_powRingHom _ (CharP.cast_eq_zero _ p)]
  congr 2
  refine RingHom.ext fun f ↦ ?_
  have := FiniteField.MvPolynomial.expand_card (σ := σ) (K := ULift.{u} (ZMod p)) f
  rw [Fintype.card_ulift, ZMod.card] at this
  simp [TauCeti.powRingHom_apply, this]

/-- Over `𝔽_p`, the relative Frobenius of affine space is `Spec` of `expand p`, up to the
identifications of `𝔸(σ; Spec 𝔽_p)` and of its Frobenius twist with `Spec 𝔽_p[X_i]`. -/
private theorem isPullback_relativeFrobenius_spec_primeField :
    IsPullback
      ((𝔸(σ; Spec (.of (ULift.{u} (ZMod p)))) ↘ Spec (.of (ULift.{u} (ZMod p)))).relativeFrobenius
        p (natCast_spec_eq_zero _))
      (SpecIso σ (.of (ULift.{u} (ZMod p)))).hom
      (pullback.fst _ _ ≫ (SpecIso σ (.of (ULift.{u} (ZMod p)))).hom)
      (Spec.map (CommRingCat.ofHom
        (MvPolynomial.expand p : MvPolynomial σ (ULift.{u} (ZMod p)) →ₐ[_] _).toRingHom)) := by
  -- the projection from the Frobenius twist is an isomorphism, as the Frobenius of `𝔽_p` is
  have : IsIso ((Spec (.of (ULift.{u} (ZMod p)))).frobenius p (natCast_spec_eq_zero _)) := by
    rw [frobenius_spec_primeField]; infer_instance
  refine IsPullback.of_vert_isIso ⟨?_⟩
  rw [Hom.relativeFrobenius_fst_assoc, frobenius_naturality _ (natCast_spec_eq_zero _),
    frobenius_spec_mvPolynomial]

variable (hS : (p : Γ(S, ⊤)) = 0)

/-- The relative Frobenius of `𝔸(σ; S)` over `S` is a base change of `Spec` of `expand p` on
`𝔽_p[X_i]`. -/
private theorem exists_isPullback_relativeFrobenius :
    ∃ (a : 𝔸(σ; S) ⟶ Spec (.of (MvPolynomial σ (ULift.{u} (ZMod p)))))
      (b : pullback (𝔸(σ; S) ↘ S) (S.frobenius p hS) ⟶
        Spec (.of (MvPolynomial σ (ULift.{u} (ZMod p))))),
      IsPullback a ((𝔸(σ; S) ↘ S).relativeFrobenius p hS)
        (Spec.map (CommRingCat.ofHom
          (MvPolynomial.expand p : MvPolynomial σ (ULift.{u} (ZMod p)) →ₐ[_] _).toRingHom)) b :=
  ⟨_, _, (Hom.isPullback_relativeFrobenius_of_isPullback (natCast_spec_eq_zero _)
    (isPullback_map (n := σ) (toSpecPrimeField hS))).paste_vert
      (isPullback_relativeFrobenius_spec_primeField σ) |>.flip⟩

/-- **The relative Frobenius of affine space is flat.** -/
instance flat_relativeFrobenius : Flat ((𝔸(σ; S) ↘ S).relativeFrobenius p hS) := by
  obtain ⟨a, b, h⟩ := exists_isPullback_relativeFrobenius σ hS
  refine of_isPullback h ?_
  rw [Flat.SpecMap_iff, CommRingCat.hom_ofHom]
  exact TauCeti.MvPolynomial.flat_expand (Fact.out : p.Prime).pos

variable [Finite σ]

/-- **The relative Frobenius of affine space in finitely many variables is finite.** -/
instance isFinite_relativeFrobenius : IsFinite ((𝔸(σ; S) ↘ S).relativeFrobenius p hS) := by
  obtain ⟨a, b, h⟩ := exists_isPullback_relativeFrobenius σ hS
  refine of_isPullback h ?_
  rw [IsFinite.SpecMap_iff, CommRingCat.hom_ofHom]
  exact TauCeti.MvPolynomial.finite_expand (Fact.out : p.Prime).pos

/-- The relative Frobenius of affine space in finitely many variables is locally of finite
presentation. -/
instance locallyOfFinitePresentation_relativeFrobenius :
    LocallyOfFinitePresentation ((𝔸(σ; S) ↘ S).relativeFrobenius p hS) := by
  obtain ⟨a, b, h⟩ := exists_isPullback_relativeFrobenius σ hS
  refine of_isPullback h ?_
  rw [HasRingHomProperty.Spec_iff (P := @LocallyOfFinitePresentation), CommRingCat.hom_ofHom]
  exact TauCeti.MvPolynomial.finitePresentation_expand p

/-- **The relative Frobenius of affine space has rank `p ^ n`.** The relative Frobenius of the
affine space `𝔸(σ; S)` in finitely many variables over a scheme `S` in which `p` vanishes is
finite locally free of constant rank `p ^ Nat.card σ`. -/
@[simp]
theorem finrank_relativeFrobenius :
    ((𝔸(σ; S) ↘ S).relativeFrobenius p hS).finrank = fun _ ↦ p ^ Nat.card σ := by
  obtain ⟨a, b, h⟩ := exists_isPullback_relativeFrobenius σ hS
  have hp := (Fact.out : p.Prime).pos
  have hfin := TauCeti.MvPolynomial.finite_expand (σ := σ) (R := ULift.{u} (ZMod p)) hp
  have hflat := TauCeti.MvPolynomial.flat_expand (σ := σ) (R := ULift.{u} (ZMod p)) hp
  have : IsFinite (Spec.map (CommRingCat.ofHom
      (MvPolynomial.expand p : MvPolynomial σ (ULift.{u} (ZMod p)) →ₐ[_] _).toRingHom)) :=
    (IsFinite.SpecMap_iff _).2 hfin
  have : Flat (Spec.map (CommRingCat.ofHom
      (MvPolynomial.expand p : MvPolynomial σ (ULift.{u} (ZMod p)) →ₐ[_] _).toRingHom)) :=
    Flat.SpecMap_iff.2 hflat
  ext x
  rw [Hom.finrank_of_isPullback _ _ _ _ h, Hom.finrank_SpecMap_eq_finrank hfin hflat,
    CommRingCat.hom_ofHom, TauCeti.MvPolynomial.finrank_expand hp]

section Etale

variable {σ} {X : Scheme.{u}} {π : X ⟶ S} (g : X ⟶ 𝔸(σ; S)) [Etale g] (hg : g ≫ 𝔸(σ; S) ↘ S = π)

include hg

omit [Finite σ] in
/-- The relative Frobenius of a scheme étale over affine space is flat. -/
theorem flat_relativeFrobenius_of_etale : Flat (π.relativeFrobenius p hS) :=
  of_isPullback (Hom.isPullback_relativeFrobenius_of_etale hS _ g hg).flip inferInstance

/-- The relative Frobenius of a scheme étale over affine space in finitely many variables is
finite. -/
theorem isFinite_relativeFrobenius_of_etale : IsFinite (π.relativeFrobenius p hS) :=
  of_isPullback (Hom.isPullback_relativeFrobenius_of_etale hS _ g hg).flip inferInstance

/-- The relative Frobenius of a scheme étale over affine space in finitely many variables is
locally of finite presentation. -/
theorem locallyOfFinitePresentation_relativeFrobenius_of_etale :
    LocallyOfFinitePresentation (π.relativeFrobenius p hS) :=
  of_isPullback (Hom.isPullback_relativeFrobenius_of_etale hS _ g hg).flip inferInstance

/-- **The relative Frobenius in étale coordinates has rank `p ^ n`.** If `X` is étale over the
affine space `𝔸(σ; S)` in finitely many variables over `S`, then its relative Frobenius over `S`
is finite locally free of constant rank `p ^ Nat.card σ`. -/
theorem finrank_relativeFrobenius_of_etale :
    (π.relativeFrobenius p hS).finrank = fun _ ↦ p ^ Nat.card σ := by
  ext x
  rw [Hom.finrank_of_isPullback _ _ _ _
    (Hom.isPullback_relativeFrobenius_of_etale hS _ g hg).flip, finrank_relativeFrobenius]

end Etale

end AlgebraicGeometry.AffineSpace
