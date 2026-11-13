/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Morphisms.StalkMap
public import Mathlib.RingTheory.RegularLocalRing.Defs
import TauCeti.AlgebraicGeometry.Morphisms.ElementaryEtale.Stalk
import TauCeti.AlgebraicGeometry.Morphisms.Etale.Ramification
import TauCeti.AlgebraicGeometry.Morphisms.Etale.Normal
import TauCeti.AlgebraicGeometry.Morphisms.LocalSpectrum
import TauCeti.AlgebraicGeometry.Scheme.Regular.LocalRing
import TauCeti.RingTheory.KrullDimension.Integral
import TauCeti.RingTheory.RegularLocalRing.Basic
import TauCeti.RingTheory.RegularLocalRing.Purity

/-!
# Purity of the branch locus in local dimension at most two

A morphism of locally Noetherian schemes, locally of finite type and quasi-finite at `x`,
is étale near `x` if its source stalk is normal, its target stalk is regular of dimension
between one and two and at most that of the source stalk, and it is unramified at every
codimension-one generization of `x`. This is the small-dimensional case of Zariski–Nagata purity
(Stacks, Lemma 58.21.4).
No global finiteness, dominance, normality or regularity is imposed.

The finite-stalk version applies purity for finite normal algebras over regular local rings
of dimension at most two. The target stalk having dimension at most that of the source stalk
makes the finite stalk map injective, hence its normal-domain target is torsion free. The general
case uses an elementary étale neighbourhood isolating the chosen point: its finite horizontal
map has a singleton fibre,
so its stalk map really is finite. Étale invariance transports normality, regularity,
dimension and the codimension-one unramifiedness hypothesis to this local model.

## References

* The Stacks Project, Lemma 58.21.4 (0BMB), purity of the branch locus.
* The Stacks Project, Lemma 58.21.3 (0BMA), local purity in dimension two.
-/

public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Scheme.Hom

variable {X Y : Scheme.{u}}

/-- Purity in local dimension one or two when the map on the chosen stalks is finite.
Finiteness of the scheme morphism alone does not imply this stalkwise finiteness. -/
theorem exists_etale_of_finite_stalkMap_of_ringKrullDim_le_two (f : X ⟶ Y)
    [LocallyOfFinitePresentation f] (x : X) [IsDomain (X.presheaf.stalk x)]
    [IsIntegrallyClosed (X.presheaf.stalk x)] [IsRegularLocalRing (Y.presheaf.stalk (f x))]
    (hfin : (f.stalkMap x).hom.Finite)
    (hdim : ringKrullDim (Y.presheaf.stalk (f x)) ≤ ringKrullDim (X.presheaf.stalk x))
    (hdim₁ : 1 ≤ ringKrullDim (Y.presheaf.stalk (f x)))
    (hdim₂ : ringKrullDim (Y.presheaf.stalk (f x)) ≤ 2)
    (hunram : ∀ z : X, z ⤳ x → ringKrullDim (X.presheaf.stalk z) = 1 →
      (f.stalkMap z).hom.FormallyUnramified) :
    ∃ U : X.Opens, x ∈ U ∧ Etale (U.ι ≫ f) := by
  let := (f.stalkMap x).hom.toAlgebra
  have : Module.Finite (Y.presheaf.stalk (f x)) (X.presheaf.stalk x) := hfin
  have hinj := (f.stalkMap x).hom.injective_of_isIntegral_of_ringKrullDim_le
    hfin.to_isIntegral hdim
  have : Module.IsTorsionFree (Y.presheaf.stalk (f x)) (X.presheaf.stalk x) :=
    Module.isTorsionFree_iff_algebraMap_injective.mpr hinj
  have het := TauCeti.Algebra.etale_of_isUnramifiedAt_height_eq_one_of_ringKrullDim_le_two
    (A := Y.presheaf.stalk (f x)) (B := X.presheaf.stalk x) hdim₁ hdim₂
    (fun q _ ↦ ⟨IsLocalization.isDomain_localization q.primeCompl_le_nonZeroDivisors,
      isIntegrallyClosed_of_isLocalization _ q.primeCompl q.primeCompl_le_nonZeroDivisors⟩)
    ((f.formallyUnramified_stalk_codimOne_iff_isUnramifiedAt x).mp hunram)
  exact (f.etaleAt_iff_stalkMap x).mpr
    ⟨RingHom.flat_algebraMap_iff.mpr inferInstance,
      RingHom.formallyUnramified_algebraMap.mpr inferInstance⟩

/-- **Purity of the branch locus in local dimension one or two.** If a quasi-finite point `x`
has normal source stalk and regular target stalk of positive dimension at most two and at most
that of the source stalk, and every codimension-one generization is unramified, then `f` is
étale on an open neighbourhood of `x`. -/
@[stacks 0BMB "in local dimension one or two"]
theorem exists_etale_of_formallyUnramified_stalk_codimOne_of_ringKrullDim_le_two
    (f : X ⟶ Y) [IsLocallyNoetherian Y] [LocallyOfFiniteType f] (x : X)
    [IsDomain (X.presheaf.stalk x)]
    [IsIntegrallyClosed (X.presheaf.stalk x)] [IsRegularLocalRing (Y.presheaf.stalk (f x))]
    (hx : f.QuasiFiniteAt x)
    (hdim : ringKrullDim (Y.presheaf.stalk (f x)) ≤ ringKrullDim (X.presheaf.stalk x))
    (hdim₁ : 1 ≤ ringKrullDim (Y.presheaf.stalk (f x)))
    (hdim₂ : ringKrullDim (Y.presheaf.stalk (f x)) ≤ 2)
    (hunram : ∀ z : X, z ⤳ x → ringKrullDim (X.presheaf.stalk z) = 1 →
      (f.stalkMap z).hom.FormallyUnramified) :
    ∃ U : X.Opens, x ∈ U ∧ Etale (U.ι ≫ f) := by
  obtain ⟨X', Y', e, b, f', x', he, hb, hex, hw, hfin, hstalk, hetale⟩ :=
    f.exists_etale_square_finite_stalkMap hx
  have hbx : b (f' x') = f x := by
    simpa only [Scheme.Hom.comp_apply, hex] using congrArg (fun g : X' ⟶ Y ↦ g x') hw.symm
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  have : IsLocallyNoetherian X' := LocallyOfFiniteType.isLocallyNoetherian e
  have : IsLocallyNoetherian Y' := LocallyOfFiniteType.isLocallyNoetherian b
  have hnormal := (e.isDomain_and_isIntegrallyClosed_stalk_iff_of_etale x').mp
    (hex ▸ ⟨inferInstance, inferInstance⟩)
  obtain ⟨hdom, hclosed⟩ := hnormal
  have hregular : IsRegularLocalRing (Y'.presheaf.stalk (f' x')) :=
    (b.isRegularLocalRing_stalk_iff_of_flat_of_formallyUnramified (f' x')).mp
      (hbx ▸ inferInstance)
  have hedim := e.ringKrullDim_stalk_eq_of_etale x'
  have hbdim := b.ringKrullDim_stalk_eq_of_etale (f' x')
  rw [hex] at hedim
  rw [hbx] at hbdim
  apply hetale.mpr
  exact f'.exists_etale_of_finite_stalkMap_of_ringKrullDim_le_two x' hstalk
    (hedim ▸ hbdim ▸ hdim) (hbdim ▸ hdim₁) (hbdim ▸ hdim₂)
    ((formallyUnramified_stalk_codimOne_iff_of_etale_square f f' e b hw x').mp
      (hex ▸ hunram))

end AlgebraicGeometry.Scheme.Hom
