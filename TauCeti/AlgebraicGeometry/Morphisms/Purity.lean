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

/-!
# Purity of the branch locus for morphisms of schemes

Let `f : X ⟶ Y` be locally of finite type over a locally Noetherian scheme `Y`, and let `x : X`
be a point at which `f` is quasi-finite, the local ring `𝒪_{X,x}` is a normal domain and the
local ring `𝒪_{Y,f x}` is a regular local ring of dimension `d ≥ 1`, at most that of `𝒪_{X,x}`.
If `f` is unramified at every codimension-one generization of `x`, then `f` is étale on an open
neighbourhood of `x`. This is purity of the branch locus (Stacks, Lemma 58.21.4 (0BMB); SGA 1,
Exposé X, Théorème 3.1), stated here for the stalk forms of "unramified" and "étale at `x`".

The local input is purity for regular local rings (Stacks, Lemma 58.21.3 (0BMA)): every finite
étale cover of the punctured spectrum of a regular local ring of dimension at least two extends
across the closed point (`TauCeti.IsLocalRing.PurityHolds`). The main theorem
`AlgebraicGeometry.Scheme.Hom.exists_etale_of_formallyUnramified_stalk_codimOne_of_purityHolds`
takes it as a hypothesis, for regular local rings of dimension between `2` and `d`, and reduces
purity of the branch locus to it. Purity for regular local rings is known in dimension two
(`TauCeti.IsLocalRing.purityHolds_of_ringKrullDim_eq_two`), which gives purity of the branch
locus unconditionally when `d ≤ 2`.

The reduction follows Stacks' proof of 0BMB. An elementary étale neighbourhood of `f x` makes
the stalk map at a point over `x` finite without changing the étaleness problem
(`AlgebraicGeometry.Scheme.Hom.exists_etale_square_finite_stalkMap`, Stacks 02LK). Normality,
regularity, dimension and unramifiedness in codimension one are all unchanged by this étale
localization. The source stalk is then a finite algebra over the target stalk, injective because
it has the same dimension, hence torsion free; its height-one primes are the codimension-one
generizations of the point. Purity for finite algebras over a normal base
(`TauCeti.Algebra.etale_of_isUnramifiedAt_height_eq_one_of_purityHolds`), applied to the regular
local localizations of the target stalk, makes the stalk map étale.

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
private theorem exists_etale_of_formallyUnramified_stalk_codimOne_of_finite_stalkMap
    (f : X ⟶ Y) [IsLocallyNoetherian Y] [LocallyOfFiniteType f] (x : X)
    [IsDomain (X.presheaf.stalk x)] [IsIntegrallyClosed (X.presheaf.stalk x)]
    [IsRegularLocalRing (Y.presheaf.stalk (f x))] (hfin : (f.stalkMap x).hom.Finite)
    (hdim : ringKrullDim (Y.presheaf.stalk (f x)) ≤ ringKrullDim (X.presheaf.stalk x))
    (hpos : 1 ≤ ringKrullDim (Y.presheaf.stalk (f x)))
    (hpurity : ∀ (𝔭 : Ideal (Y.presheaf.stalk (f x))) [𝔭.IsPrime], 2 ≤ 𝔭.height →
      TauCeti.IsLocalRing.PurityHolds (Localization.AtPrime 𝔭))
    (hunram : ∀ z : X, z ⤳ x → ringKrullDim (X.presheaf.stalk z) = 1 →
      (f.stalkMap z).hom.FormallyUnramified) :
    ∃ U : X.Opens, x ∈ U ∧ Etale (U.ι ≫ f) := by
  have hunram' := (f.formallyUnramified_stalk_codimOne_iff_isUnramifiedAt x).mp hunram
  algebraize [(f.stalkMap x).hom]
  -- The stalk at `x` is finite over the stalk at `f x` and has the same dimension, so the stalk
  -- map is injective and the stalk at `x` is torsion free.
  have : FaithfulSMul (Y.presheaf.stalk (f x)) (X.presheaf.stalk x) :=
    TauCeti.faithfulSMul_of_isIntegral_of_ringKrullDim_le ringKrullDim_ne_top hdim
  have hA : ¬IsField (Y.presheaf.stalk (f x)) := fun h ↦
    absurd (ringKrullDim_eq_zero_of_isField h ▸ hpos) (by decide)
  -- The localizations of the stalk at `x` at its maximal ideal are normal domains.
  have hnormal (𝔮 : Ideal (X.presheaf.stalk x)) [𝔮.IsMaximal] :
      IsDomain (Localization.AtPrime 𝔮) ∧ IsIntegrallyClosed (Localization.AtPrime 𝔮) :=
    ⟨IsLocalization.isDomain_localization 𝔮.primeCompl_le_nonZeroDivisors,
      isIntegrallyClosed_of_isLocalization _ _ 𝔮.primeCompl_le_nonZeroDivisors⟩
  have : Algebra.Etale (Y.presheaf.stalk (f x)) (X.presheaf.stalk x) :=
    TauCeti.Algebra.etale_of_isUnramifiedAt_height_eq_one_of_purityHolds hA hpurity hnormal
      fun q _ hq ↦ hunram' q ‹_› hq
  exact (etaleAt_iff_stalkMap f x).mpr
    ⟨RingHom.flat_algebraMap_iff.mpr inferInstance,
      RingHom.formallyUnramified_algebraMap.mpr inferInstance⟩

/-- **Purity of the branch locus, from purity for regular local rings.** Let `f : X ⟶ Y` be
locally of finite type over a locally Noetherian scheme, and `x : X` a point at which `f` is
quasi-finite, `𝒪_{X,x}` is a normal domain and `𝒪_{Y,f x}` is a regular local ring of dimension
`d ≥ 1`, at most the dimension of `𝒪_{X,x}`. Suppose purity holds for every regular local ring
of dimension between `2` and `d`. If the stalk map of `f` is formally unramified at every
codimension-one generization of `x`, then `f` is étale on an open neighbourhood of `x`. -/
@[stacks 0BMB "stalk form, from purity for regular local rings of dimension at most that of the
target stalk"]
theorem exists_etale_of_formallyUnramified_stalk_codimOne_of_purityHolds (f : X ⟶ Y)
    [IsLocallyNoetherian Y] [LocallyOfFiniteType f] {x : X}
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
  refine exists_etale_of_formallyUnramified_stalk_codimOne_of_finite_stalkMap f' x' hfin
    (by rw [hYdim, ← hXdim]; exact hdim) (hYdim ▸ hpos) (fun 𝔭 _ h𝔭 ↦ ?_)
    ((formallyUnramified_stalk_codimOne_iff_of_etale_square f f' e b hw x').mp hunram)
  -- The localizations of the new target stalk are regular local rings of bounded dimension.
  have hloc := IsLocalization.AtPrime.ringKrullDim_eq_height 𝔭 (Localization.AtPrime 𝔭)
  refine hpurity _ (by rw [hloc]; exact WithBot.coe_le_coe.mpr h𝔭) ?_
  rw [hloc, ← hYdim]
  exact Ideal.height_le_ringKrullDim_of_isPrime

/-- **Purity of the branch locus in dimension at most two.** Let `f : X ⟶ Y` be locally of finite
type over a locally Noetherian scheme, and `x : X` a point at which `f` is quasi-finite,
`𝒪_{X,x}` is a normal domain and `𝒪_{Y,f x}` is a regular local ring of dimension one or two,
at most the dimension of `𝒪_{X,x}`. If the stalk map of `f` is formally unramified at every
codimension-one generization of `x`, then `f` is étale on an open neighbourhood of `x`. -/
@[stacks 0BMB "stalk form, when the target stalk has dimension at most two"]
theorem exists_etale_of_formallyUnramified_stalk_codimOne_of_ringKrullDim_le_two (f : X ⟶ Y)
    [IsLocallyNoetherian Y] [LocallyOfFiniteType f] {x : X}
    [IsDomain (X.presheaf.stalk x)] [IsIntegrallyClosed (X.presheaf.stalk x)]
    [IsRegularLocalRing (Y.presheaf.stalk (f x))] (hx : f.QuasiFiniteAt x)
    (hdim : ringKrullDim (Y.presheaf.stalk (f x)) ≤ ringKrullDim (X.presheaf.stalk x))
    (hpos : 1 ≤ ringKrullDim (Y.presheaf.stalk (f x)))
    (hdim₂ : ringKrullDim (Y.presheaf.stalk (f x)) ≤ 2)
    (hunram : ∀ z : X, z ⤳ x → ringKrullDim (X.presheaf.stalk z) = 1 →
      (f.stalkMap z).hom.FormallyUnramified) :
    ∃ U : X.Opens, x ∈ U ∧ Etale (U.ι ≫ f) :=
  f.exists_etale_of_formallyUnramified_stalk_codimOne_of_purityHolds hx hdim hpos
    (fun _ _ _ h₂ hle ↦ TauCeti.IsLocalRing.purityHolds_of_ringKrullDim_eq_two
      (le_antisymm (hle.trans hdim₂) h₂)) hunram

end AlgebraicGeometry.Scheme.Hom
