/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.GroupScheme.Diagonalizable
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import TauCeti.AlgebraicGeometry.Scheme.CoefficientInvertibility
import Mathlib.AlgebraicGeometry.Morphisms.SmoothFiber
import TauCeti.Algebra.AlgebraicGroup.DiagonalizableGroup.Scheme.Smooth
import TauCeti.Algebra.MonoidAlgebra.Etale
import TauCeti.GroupTheory.Torsion

/-!
# Smooth and étale diagonalizable group schemes over a base

For a finitely generated abelian group `M` and a scheme `S`, the diagonalizable group scheme
`D_S(M)` is smooth over `S` exactly when the order of the torsion subgroup of `M` is invertible on
`S`, and étale exactly when the order of `M` itself is invertible on `S`. Invertibility on `S` is
`AlgebraicGeometry.Scheme.IsInvertibleOn`: being a unit in `Γ(S, ⊤)`, equivalently nonzero in
every residue field of `S`. Since the order of an infinite group is `0`, over a nonempty base an
étale `D_S(M)` has `M` finite. For example `𝔾_m = D_S(ℤ)` is smooth over every base and étale
over no nonempty base, while `D_S(ℤ/6)` is smooth, and étale, exactly where `6` is invertible.

Smoothness is checked on fibres: `D_S(M)` is flat and locally of finite presentation over `S`, so
by Mathlib's `AlgebraicGeometry.Smooth.of_smooth_fiberToSpecResidueField` it is smooth when every
fibre is, and the fibre at `s` is `Spec κ(s)[M]`, which is smooth exactly when `M` has no
`p`-torsion for the exponential characteristic `p` of `κ(s)`
(`TauCeti.DiagonalizableGroup.smooth_groupScheme_iff`). Étaleness of the fibres is
`TauCeti.MonoidAlgebra.etale_iff_isUnit_card`; conversely, when the order of `M` is a unit of
`Γ(S, ⊤)`, `D_S(M)` is the base change along `S ⟶ Spec Γ(S, ⊤)` of the spectrum of the group
algebra `Γ(S, ⊤)[M]`, which is étale by `TauCeti.MonoidAlgebra.etale_of_isUnit_card`.

## Main declarations

* `TauCeti.GroupScheme.smooth_diagonalizable_iff`: `D_S(M)` is smooth over `S` iff the order of
  the torsion subgroup of `M` is invertible on `S`.
* `TauCeti.GroupScheme.smooth_diagonalizable`: for torsion-free `M`, such as `ℤⁿ`, `D_S(M)` is
  smooth over every base.
* `TauCeti.GroupScheme.etale_diagonalizable_iff`: `D_S(M)` is étale over `S` iff the order of `M`
  is invertible on `S`.
* `TauCeti.GroupScheme.finite_of_etale_diagonalizable`: over a nonempty base, if `D_S(M)` is étale
  then `M` is finite.

## References

* M. Demazure, A. Grothendieck et al., *Schémas en groupes* (SGA 3), Exp. VIII, 2.1 c) and e).
-/

public section

open CategoryTheory Limits AlgebraicGeometry

namespace TauCeti.GroupScheme

universe u

variable {S : Scheme.{u}} (M : Type u) [AddCommGroup M] [AddGroup.FG M]

/-- The diagonalizable group scheme `Spec R[G]` is étale over `R` exactly when the group algebra
`R[G]` is an étale `R`-algebra. -/
private theorem etale_groupScheme_iff (R : Type u) [CommRing R] (G : FGCommGrpCat.{u}) :
    Etale (DiagonalizableGroup.groupScheme R G).X.hom ↔ Algebra.Etale R (MonoidAlgebra R G) := by
  rw [DiagonalizableGroup.groupScheme_def,
    morphismProperty_hopfSpec_obj_X_hom_iff (P := @Etale) R,
    HasRingHomProperty.Spec_iff (P := @Etale)]
  exact RingHom.etale_algebraMap

/-- The fibre of `D_S(M)` at `s` is smooth exactly when the order of the torsion subgroup of `M`
is invertible in the residue field `κ(s)`. -/
private theorem smooth_fiberToSpecResidueField_diagonalizable_iff (s : S) :
    Smooth ((diagonalizable S M).X.hom.fiberToSpecResidueField s) ↔
      (Nat.card (AddCommGroup.torsion M) : S.residueField s) ≠ 0 := by
  obtain ⟨p, _⟩ := ExpChar.exists (S.residueField s)
  -- Instance search does not find `RespectsIso @Smooth` at the current Mathlib pin.
  have : MorphismProperty.RespectsIso (@Smooth : MorphismProperty Scheme.{u}) :=
    MorphismProperty.IsStableUnderBaseChange.respectsIso
  -- The fibre is the base change of `D_S(M)` to `Spec κ(s)`, which is `Spec κ(s)[M]`.
  refine (MorphismProperty.over_iso_iff (@Smooth)
    ((Grp.forget _).mapIso (diagonalizableFiberIso M s))).trans <|
      (DiagonalizableGroup.smooth_groupScheme_iff _ p _).trans ?_
  -- `κ(s)[M]` is smooth iff `M` has no `p`-torsion, iff `p` does not divide `#M_tors`.
  rcases ‹ExpChar (S.residueField s) p› with _ | ⟨hp⟩
  · simpa using Nat.card_pos.ne'
  · rw [ne_eq, CharP.cast_eq_zero_iff _ p, AddCommGroup.prime_dvd_natCard_torsion_iff hp]
    -- The character group is `Multiplicative M`, where `g ^ p = 1` is `p • g = 0` in `M`.
    exact ⟨fun h ⟨g, hg0, hg⟩ ↦ hg0 (h g hg), fun h g hg ↦ by_contra fun hg0 ↦ h ⟨g, hg0, hg⟩⟩

/-- **Smoothness of diagonalizable group schemes** (SGA 3, Exp. VIII, 2.1 e)). For a finitely
generated abelian group `M`, the diagonalizable group scheme `D_S(M)` is smooth over `S` exactly
when the order of the torsion subgroup of `M` is invertible on `S`, that is, nonzero in every
residue field of `S`. For instance `𝔾_m = D_S(ℤ)` is smooth over every base, while for `n ≥ 1`
the group `μ_n = D_S(ℤ/n)` is smooth exactly where `n` is invertible. -/
theorem smooth_diagonalizable_iff :
    Smooth (diagonalizable S M).X.hom ↔ S.IsInvertibleOn (Nat.card (AddCommGroup.torsion M)) := by
  simp_rw [Scheme.isInvertibleOn_iff_forall_residueField_ne_zero,
    ← smooth_fiberToSpecResidueField_diagonalizable_iff]
  exact ⟨fun _ s ↦ inferInstanceAs (Smooth (pullback.snd _ (S.fromSpecResidueField s))),
    Smooth.of_smooth_fiberToSpecResidueField _⟩

/-- For a torsion-free finitely generated abelian group `M`, such as `ℤⁿ`, the diagonalizable
group scheme `D_S(M)` is smooth over every base `S`. In particular `𝔾_m = D_S(ℤ)` is smooth. -/
instance smooth_diagonalizable [IsAddTorsionFree M] : Smooth (diagonalizable S M).X.hom := by
  rw [smooth_diagonalizable_iff, (AddCommGroup.isAddTorsionFree_iff_torsion_eq_bot).mp ‹_›,
    AddSubgroup.card_bot]
  infer_instance

/-- **Étale diagonalizable group schemes** (SGA 3, Exp. VIII, 2.1 c)). For a finitely generated
abelian group `M`, the diagonalizable group scheme `D_S(M)` is étale over `S` exactly when the
order of `M` is invertible on `S`, that is, nonzero in every residue field of `S`. For infinite `M`
the order `Nat.card M` is `0`, so over a nonempty base `D_S(M)` is étale only if `M` is finite
(`finite_of_etale_diagonalizable`). -/
theorem etale_diagonalizable_iff :
    Etale (diagonalizable S M).X.hom ↔ S.IsInvertibleOn (Nat.card M) := by
  -- Instance search does not find `RespectsIso @Etale` at the current Mathlib pin.
  have : MorphismProperty.RespectsIso (@Etale : MorphismProperty Scheme.{u}) :=
    MorphismProperty.IsStableUnderBaseChange.respectsIso
  refine ⟨fun _ ↦ (Scheme.isInvertibleOn_iff_forall_residueField_ne_zero _ S).mpr fun s ↦ ?_,
    fun h ↦ ?_⟩
  · -- The fibre at `s` is étale, and it is `Spec κ(s)[M]`.
    have : Etale ((Over.pullback (S.fromSpecResidueField s)).mapGrp.obj
        (diagonalizable S M)).X.hom :=
      inferInstanceAs (Etale (pullback.snd _ (S.fromSpecResidueField s)))
    exact ((MonoidAlgebra.etale_iff_isUnit_card _ _).mp <| (etale_groupScheme_iff _ _).mp <|
      (MorphismProperty.over_iso_iff (@Etale)
        ((Grp.forget _).mapIso (diagonalizableFiberIso M s))).mp this).ne_zero
  · -- `D_S(M)` is the base change of `Spec Γ(S, ⊤)[M]` along `S ⟶ Spec Γ(S, ⊤)`, and the order
    -- of `M` is a unit in `Γ(S, ⊤)`.
    have hu : IsUnit (Nat.card M : Γ(S, ⊤)) := (Scheme.isInvertibleOn_iff_isUnit _ S).mp h
    have : Etale (diagonalizable (Spec Γ(S, ⊤)) M).X.hom :=
      (MorphismProperty.over_iso_iff (@Etale)
        ((Grp.forget _).mapIso (diagonalizableSpecIso M Γ(S, ⊤)))).mpr <|
          (etale_groupScheme_iff _ _).mpr (MonoidAlgebra.etale_of_isUnit_card _ _ hu)
    have : Etale ((Over.pullback S.toSpecΓ).mapGrp.obj (diagonalizable (Spec Γ(S, ⊤)) M)).X.hom :=
      inferInstanceAs (Etale (pullback.snd _ S.toSpecΓ))
    exact (MorphismProperty.over_iso_iff (@Etale)
      ((Grp.forget _).mapIso (diagonalizableBaseChangeIso M S.toSpecΓ))).mp this

/-- Over a nonempty base, an étale diagonalizable group scheme `D_S(M)` has finite character
group `M`. -/
theorem finite_of_etale_diagonalizable [Nonempty S] [Etale (diagonalizable S M).X.hom] :
    Finite M := by
  have := (etale_diagonalizable_iff M).mp ‹_›
  refine Nat.finite_of_card_ne_zero fun h ↦ ?_
  rw [h, Scheme.isInvertibleOn_zero_iff] at this
  exact not_isEmpty_of_nonempty S this

end TauCeti.GroupScheme
