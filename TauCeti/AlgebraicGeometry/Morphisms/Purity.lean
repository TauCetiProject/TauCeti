/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.RegularLocalRing.Defs
public import TauCeti.AlgebraicGeometry.FiniteEtale.PuncturedSpectrum
public import TauCeti.AlgebraicGeometry.Morphisms.StalkMap
import TauCeti.AlgebraicGeometry.FiniteEtale.BranchPurity
import TauCeti.AlgebraicGeometry.FiniteEtale.Purity
import TauCeti.AlgebraicGeometry.Morphisms.ElementaryEtale.Stalk
import TauCeti.AlgebraicGeometry.Morphisms.Etale.Normal
import TauCeti.AlgebraicGeometry.Morphisms.Etale.Ramification
import TauCeti.AlgebraicGeometry.Morphisms.LocalSpectrum
import TauCeti.AlgebraicGeometry.Scheme.Regular.LocalRing
import TauCeti.RingTheory.KrullDimension.Integral
import TauCeti.RingTheory.RegularLocalRing.Normal
import TauCeti.RingTheory.RegularLocalRing.ProjectiveDimension
import TauCeti.RingTheory.RegularLocalRing.Purity

/-!
# Purity of the branch locus for morphisms of schemes

Let `f : X ⟶ Y` be locally of finite type over a locally Noetherian scheme `Y`, and let `x : X`
be a point at which `f` is quasi-finite, the local ring `𝒪_{X,x}` is a normal domain and the
local ring `𝒪_{Y,f x}` is a regular local ring of dimension `d ≥ 1`, at most that of `𝒪_{X,x}`.
If `f` is unramified at every codimension-one generization of `x`, then `f` is étale on an open
neighbourhood of `x`. This is purity of the branch locus (Stacks, Lemma 58.21.4 (0BMB); SGA 1,
Exposé X, Théorème 3.1), stated here for the stalk forms of "unramified" and "étale at `x`".
No global finiteness, dominance, normality or regularity is imposed.

The local input is purity for regular local rings (Stacks, Lemma 58.21.3 (0BMA)): every finite
étale cover of the punctured spectrum of a regular local ring of dimension at least two extends
across the closed point (`TauCeti.IsLocalRing.PurityHolds`). The main theorem
`AlgebraicGeometry.Scheme.Hom.exists_etale_of_formallyUnramified_stalk_codimOne_of_purityHolds`
takes it as a hypothesis, for regular local rings of dimension between `2` and `d`, and reduces
purity of the branch locus to it. Purity for regular local rings is known in dimension two
(`TauCeti.IsLocalRing.purityHolds_of_ringKrullDim_eq_two`), which gives purity of the branch
locus unconditionally when `d ≤ 2`.

The finite-stalk versions apply purity for finite normal algebras over the target stalk. The
target stalk having dimension at most that of the source stalk makes the finite stalk map
injective, hence its normal-domain target is torsion free. The general case uses an elementary
étale neighbourhood isolating the chosen point
(`AlgebraicGeometry.Scheme.Hom.exists_etale_square_finite_stalkMap`, Stacks 02LK): its finite
horizontal map has a singleton fibre, so its stalk map really is finite. Étale invariance
transports normality, regularity, dimension and the codimension-one unramifiedness hypothesis to
this local model.

## Main results

* `Scheme.Hom.exists_etale_of_formallyUnramified_stalk_codimOne_of_purityHolds`:
  purity of the branch locus at `x`, assuming purity for regular local rings of dimension between
  two and the dimension of `𝒪_{Y,f x}`.
* `Scheme.Hom.exists_etale_of_formallyUnramified_stalk_codimOne_of_ringKrullDim_le_two`:
  purity of the branch locus at `x` when `𝒪_{Y,f x}` has dimension one or two.

## References

* [The Stacks Project, Lemma 58.21.4](https://stacks.math.columbia.edu/tag/0BMB), purity of the
  branch locus.
* [The Stacks Project, Lemma 58.21.3](https://stacks.math.columbia.edu/tag/0BMA), purity for
  regular local rings.
* A. Grothendieck, *Revêtements étales et groupe fondamental* (SGA 1), Exposé X, Théorème 3.1.
-/

public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Scheme.Hom

variable {X Y : Scheme.{u}}

/-- Purity of the branch locus at a point where the stalk map is finite, from purity of the
localizations of the target stalk at primes of height at least two. -/
theorem exists_etale_of_finite_stalkMap_of_purityHolds (f : X ⟶ Y)
    [LocallyOfFinitePresentation f] (x : X) [IsDomain (X.presheaf.stalk x)]
    [IsIntegrallyClosed (X.presheaf.stalk x)] [IsRegularLocalRing (Y.presheaf.stalk (f x))]
    (hfin : (f.stalkMap x).hom.Finite)
    (hdim : ringKrullDim (Y.presheaf.stalk (f x)) ≤ ringKrullDim (X.presheaf.stalk x))
    (hpos : 1 ≤ ringKrullDim (Y.presheaf.stalk (f x)))
    (hpurity : ∀ (𝔭 : Ideal (Y.presheaf.stalk (f x))) [𝔭.IsPrime], 2 ≤ 𝔭.height →
      TauCeti.IsLocalRing.PurityHolds (Localization.AtPrime 𝔭))
    (hunram : ∀ z : X, z ⤳ x → ringKrullDim (X.presheaf.stalk z) = 1 →
      (f.stalkMap z).hom.FormallyUnramified) :
    ∃ U : X.Opens, x ∈ U ∧ Etale (U.ι ≫ f) := by
  let := (f.stalkMap x).hom.toAlgebra
  have : Module.Finite (Y.presheaf.stalk (f x)) (X.presheaf.stalk x) := hfin
  have hinj := (f.stalkMap x).hom.injective_of_isIntegral_of_ringKrullDim_le
    hfin.to_isIntegral hdim
  have : Module.IsTorsionFree (Y.presheaf.stalk (f x)) (X.presheaf.stalk x) :=
    Module.isTorsionFree_iff_algebraMap_injective.mpr hinj
  have hA : ¬IsField (Y.presheaf.stalk (f x)) := fun h ↦
    absurd (ringKrullDim_eq_zero_of_isField h ▸ hpos) (by decide)
  have het := TauCeti.Algebra.etale_of_isUnramifiedAt_height_eq_one_of_purityHolds
    (A := Y.presheaf.stalk (f x)) (B := X.presheaf.stalk x) hA hpurity
    (fun q _ ↦ ⟨IsLocalization.isDomain_localization q.primeCompl_le_nonZeroDivisors,
      isIntegrallyClosed_of_isLocalization _ q.primeCompl q.primeCompl_le_nonZeroDivisors⟩)
    ((f.formallyUnramified_stalk_codimOne_iff_isUnramifiedAt x).mp hunram)
  exact (f.etaleAt_iff_stalkMap x).mpr
    ⟨RingHom.flat_algebraMap_iff.mpr inferInstance,
      RingHom.formallyUnramified_algebraMap.mpr inferInstance⟩

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
  refine f.exists_etale_of_finite_stalkMap_of_purityHolds x hfin hdim hdim₁ (fun 𝔭 _ h𝔭 ↦ ?_)
    hunram
  -- A localization at a prime of height at least two has dimension exactly two.
  have hloc := IsLocalization.AtPrime.ringKrullDim_eq_height 𝔭 (Localization.AtPrime 𝔭)
  refine TauCeti.IsLocalRing.purityHolds_of_ringKrullDim_eq_two (le_antisymm ?_ ?_)
  · rw [hloc]
    exact Ideal.height_le_ringKrullDim_of_isPrime.trans hdim₂
  · rw [hloc]
    exact WithBot.coe_le_coe.mpr h𝔭

/-- **Purity of the branch locus, from purity for regular local rings.** Let `f : X ⟶ Y` be
locally of finite type over a locally Noetherian scheme, and `x : X` a point at which `f` is
quasi-finite, `𝒪_{X,x}` is a normal domain and `𝒪_{Y,f x}` is a regular local ring of dimension
`d ≥ 1`, at most the dimension of `𝒪_{X,x}`. Suppose purity holds for every regular local ring
of dimension between `2` and `d`. If the stalk map of `f` is formally unramified at every
codimension-one generization of `x`, then `f` is étale on an open neighbourhood of `x`. -/
@[stacks 0BMB "stalk form, from purity for regular local rings of dimension at most that of the
target stalk"]
theorem exists_etale_of_formallyUnramified_stalk_codimOne_of_purityHolds (f : X ⟶ Y)
    [IsLocallyNoetherian Y] [LocallyOfFiniteType f] (x : X)
    [IsDomain (X.presheaf.stalk x)] [IsIntegrallyClosed (X.presheaf.stalk x)]
    [IsRegularLocalRing (Y.presheaf.stalk (f x))] (hx : f.QuasiFiniteAt x)
    (hdim : ringKrullDim (Y.presheaf.stalk (f x)) ≤ ringKrullDim (X.presheaf.stalk x))
    (hpos : 1 ≤ ringKrullDim (Y.presheaf.stalk (f x)))
    (hpurity : ∀ (A : Type u) [CommRing A] [IsRegularLocalRing A], 2 ≤ ringKrullDim A →
      ringKrullDim A ≤ ringKrullDim (Y.presheaf.stalk (f x)) → TauCeti.IsLocalRing.PurityHolds A)
    (hunram : ∀ z : X, z ⤳ x → ringKrullDim (X.presheaf.stalk z) = 1 →
      (f.stalkMap z).hom.FormallyUnramified) :
    ∃ U : X.Opens, x ∈ U ∧ Etale (U.ι ≫ f) := by
  have := LocallyOfFiniteType.isLocallyNoetherian f
  -- Pass to an étale-local model in which the stalk map is finite.
  obtain ⟨X', Y', e, b, f', x', _, _, rfl, hw, _, hfin, hiff⟩ :=
    f.exists_etale_square_finite_stalkMap hx
  rw [hiff]
  have := LocallyOfFiniteType.isLocallyNoetherian b
  have hbx : b (f' x') = f (e x') := by
    rw [← Scheme.Hom.comp_apply, ← hw, Scheme.Hom.comp_apply]
  -- Normality, regularity and dimension of the stalks are unchanged by the étale maps.
  obtain ⟨_, _⟩ := (e.isDomain_and_isIntegrallyClosed_stalk_iff_of_etale x').mp
    ⟨inferInstance, inferInstance⟩
  have : IsRegularLocalRing (Y.presheaf.stalk (b (f' x'))) := by
    rw [hbx]
    infer_instance
  have : IsRegularLocalRing (Y'.presheaf.stalk (f' x')) :=
    (b.isRegularLocalRing_stalk_iff_of_flat_of_formallyUnramified (f' x')).mp ‹_›
  have hYdim : ringKrullDim (Y'.presheaf.stalk (f' x')) =
      ringKrullDim (Y.presheaf.stalk (f (e x'))) := by
    rw [← b.ringKrullDim_stalk_eq_of_etale (f' x'), hbx]
  have hXdim := e.ringKrullDim_stalk_eq_of_etale x'
  refine f'.exists_etale_of_finite_stalkMap_of_purityHolds x' hfin
    (by rw [hYdim, ← hXdim]; exact hdim) (hYdim ▸ hpos) (fun 𝔭 _ h𝔭 ↦ ?_)
    ((formallyUnramified_stalk_codimOne_iff_of_etale_square f f' e b hw x').mp hunram)
  -- The localizations of the new target stalk are regular local rings of bounded dimension.
  have hloc := IsLocalization.AtPrime.ringKrullDim_eq_height 𝔭 (Localization.AtPrime 𝔭)
  refine hpurity _ (by rw [hloc]; exact WithBot.coe_le_coe.mpr h𝔭) ?_
  rw [hloc, ← hYdim]
  exact Ideal.height_le_ringKrullDim_of_isPrime

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
    ∃ U : X.Opens, x ∈ U ∧ Etale (U.ι ≫ f) :=
  f.exists_etale_of_formallyUnramified_stalk_codimOne_of_purityHolds x hx hdim hdim₁
    (fun _ _ _ h₂ hle ↦ TauCeti.IsLocalRing.purityHolds_of_ringKrullDim_eq_two
      (le_antisymm (hle.trans hdim₂) h₂)) hunram

end AlgebraicGeometry.Scheme.Hom
