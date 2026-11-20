/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.RegularLocalRing.Defs
public import TauCeti.AlgebraicGeometry.FiniteEtale.PuncturedSpectrum
public import TauCeti.AlgebraicGeometry.Morphisms.BranchLocus
public import TauCeti.AlgebraicGeometry.Morphisms.StalkMap
public import TauCeti.AlgebraicGeometry.Scheme.Regular.Scheme
import TauCeti.Topology.Sober
import TauCeti.AlgebraicGeometry.FiniteEtale.BranchPurity
import TauCeti.AlgebraicGeometry.FiniteEtale.Purity
import TauCeti.AlgebraicGeometry.Morphisms.ElementaryEtale.Stalk
import TauCeti.AlgebraicGeometry.Morphisms.Etale.Normal
import TauCeti.AlgebraicGeometry.Morphisms.Etale.Ramification
import TauCeti.AlgebraicGeometry.Morphisms.LocalSpectrum
import TauCeti.AlgebraicGeometry.Scheme.Regular.LocalRing
import TauCeti.RingTheory.KrullDimension.Integral
import TauCeti.RingTheory.RegularLocalRing.Basic
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

Purity of the branch locus at every point yields the classical global forms (SGA 1, Exposé X,
Théorème 3.1). Let `f : X ⟶ Y` be a dominant, locally quasi-finite morphism, locally of finite
type, from a normal integral scheme to a regular scheme. Then the local rings at corresponding
points have the same dimension, so at a ramified point `z` with no proper generization in the
ramification locus every codimension-one generization of `z` is unramified. Purity at `z` would
make `f` étale at `z`, so `𝒪_{X,z}` has dimension at most one, and it has dimension exactly one
unless `z` is the generic point of `X`. Thus if the ramification locus of `f` is not all of `X`,
each of its irreducible components has codimension one, and the same holds for the branch
locus, whose maximal points lift to maximal points of the ramification locus. In particular, if
`f` is étale at the generic point of `X`, it is étale as soon as it is unramified at every
codimension-one point. The assumption that the ramification locus is not everything cannot be
dropped: the relative Frobenius of the affine line in characteristic `p` is ramified everywhere.

## Main results

* `Scheme.Hom.exists_etale_of_formallyUnramified_stalk_codimOne_of_purityHolds`:
  purity of the branch locus at `x`, assuming purity for regular local rings of dimension between
  two and the dimension of `𝒪_{Y,f x}`.
* `Scheme.Hom.exists_etale_of_formallyUnramified_stalk_codimOne_of_ringKrullDim_le_two`:
  purity of the branch locus at `x` when `𝒪_{Y,f x}` has dimension one or two.
* `Scheme.Hom.ringKrullDim_stalk_eq_one_of_maximal_ramificationLocus_of_purityHolds` and
  `Scheme.Hom.ringKrullDim_stalk_eq_one_of_maximal_branchLocus_of_purityHolds`: the maximal points
  of the ramification and branch loci have local dimension one, assuming purity for regular local
  rings; the `_of_ringKrullDim_le_two` forms are unconditional in local dimension at most two.
* `Scheme.Hom.etale_iff_formallyUnramified_stalk_codimOne_of_purityHolds`: a morphism étale at
  the generic point is étale iff it is unramified in codimension one, assuming purity for regular
  local rings; `Scheme.Hom.etale_iff_formallyUnramified_stalk_codimOne_of_ringKrullDim_le_two` is
  the unconditional form over a regular scheme of dimension at most two.

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

section Loci

open TauCeti.AlgebraicGeometry

variable (f : X ⟶ Y) [IsIntegral X] [IsNormalScheme X] [IsRegular Y] [IsDominant f]
  [LocallyOfFiniteType f] [LocallyQuasiFinite f]

/-- **Purity of the ramification locus, from purity for regular local rings.** Let `f : X ⟶ Y` be
a dominant, locally quasi-finite morphism, locally of finite type, from a normal integral scheme
to a regular scheme, whose ramification locus is not all of `X`. Let `z` be a ramified point with
no proper generization in the ramification locus, that is, the generic point of an irreducible
component of this closed set. If purity holds for every regular local ring of dimension between
`2` and that of `𝒪_{Y,f z}`, then `𝒪_{X,z}` has dimension one. -/
theorem ringKrullDim_stalk_eq_one_of_maximal_ramificationLocus_of_purityHolds
    (hR : f.ramificationLocus ≠ Set.univ) {z : X} (hz : z ∈ f.ramificationLocus)
    (hmax : ∀ z' ∈ f.ramificationLocus, z' ⤳ z → z' = z)
    (hpurity : ∀ (A : Type u) [CommRing A] [IsRegularLocalRing A], 2 ≤ ringKrullDim A →
      ringKrullDim A ≤ ringKrullDim (Y.presheaf.stalk (f z)) →
        TauCeti.IsLocalRing.PurityHolds A) :
    ringKrullDim (X.presheaf.stalk z) = 1 := by
  have hdim := f.ringKrullDim_stalk_eq_of_locallyQuasiFinite z
  -- The closed ramification locus is not dense, so `z` is a proper specialization of the
  -- generic point of `X`.
  have hpos : 1 ≤ ringKrullDim (X.presheaf.stalk z) := by
    have hlt := QuasiSober.val_lt_genericPoint_of_closure_ne_univ
      (by rwa [f.isClosed_ramificationLocus.closure_eq]) ⟨z, hz⟩
    rw [ringKrullDim_stalk_eq_coheight]
    exact_mod_cast Order.one_le_iff_pos.mpr (Order.coheight_pos.mpr (not_isMax_of_lt hlt))
  by_contra hne
  -- A codimension-one generization of `z` is proper, hence unramified by maximality of `z`.
  have hunram (z' : X) (hz'z : z' ⤳ z) (hz' : ringKrullDim (X.presheaf.stalk z') = 1) :
      (f.stalkMap z').hom.FormallyUnramified := by
    by_contra hram
    rw [hmax z' (mem_ramificationLocus_iff.mpr hram) hz'z] at hz'
    exact hne hz'
  obtain ⟨U, hzU, hU⟩ := f.exists_etale_of_formallyUnramified_stalk_codimOne_of_purityHolds z
    (f.quasiFiniteAt z) hdim.ge (hdim ▸ hpos) hpurity hunram
  exact mem_nonEtaleLocus_iff.mp (f.ramificationLocus_subset_nonEtaleLocus hz) ⟨U, hzU, hU⟩

/-- **Purity of the ramification locus in local dimension at most two.** The maximal points of
the ramification locus of `f`, if it is not all of `X`, have local dimension one, provided the
local ring of `Y` at the image point has dimension at most two. -/
theorem ringKrullDim_stalk_eq_one_of_maximal_ramificationLocus_of_ringKrullDim_le_two
    (hR : f.ramificationLocus ≠ Set.univ) {z : X} (hz : z ∈ f.ramificationLocus)
    (hmax : ∀ z' ∈ f.ramificationLocus, z' ⤳ z → z' = z)
    (hdim₂ : ringKrullDim (Y.presheaf.stalk (f z)) ≤ 2) :
    ringKrullDim (X.presheaf.stalk z) = 1 :=
  f.ringKrullDim_stalk_eq_one_of_maximal_ramificationLocus_of_purityHolds hR hz hmax
    fun _ _ _ h₂ hle ↦ TauCeti.IsLocalRing.purityHolds_of_ringKrullDim_eq_two
      (le_antisymm (hle.trans hdim₂) h₂)

/-- **Purity of the branch locus, from purity for regular local rings.** Let `f : X ⟶ Y` be a
dominant, locally quasi-finite morphism, locally of finite type, from a normal integral scheme to
a regular scheme, whose ramification locus is not all of `X`. Let `w` be a point of the branch
locus with no proper generization in the branch locus. If purity holds for every regular local
ring of dimension between `2` and that of `𝒪_{Y,w}`, then `𝒪_{Y,w}` has dimension one. -/
theorem ringKrullDim_stalk_eq_one_of_maximal_branchLocus_of_purityHolds
    (hR : f.ramificationLocus ≠ Set.univ) {w : Y} (hw : w ∈ f.branchLocus)
    (hmax : ∀ w' ∈ f.branchLocus, w' ⤳ w → w' = w)
    (hpurity : ∀ (A : Type u) [CommRing A] [IsRegularLocalRing A], 2 ≤ ringKrullDim A →
      ringKrullDim A ≤ ringKrullDim (Y.presheaf.stalk w) → TauCeti.IsLocalRing.PurityHolds A) :
    ringKrullDim (Y.presheaf.stalk w) = 1 := by
  obtain ⟨x, hx, hxw⟩ := mem_branchLocus_iff.mp hw
  obtain ⟨z, hz, -, rfl, hzmax⟩ :=
    f.exists_maximal_ramificationLocus_over_of_maximal_branchLocus hmax hx hxw
  rw [← f.ringKrullDim_stalk_eq_of_locallyQuasiFinite z]
  exact f.ringKrullDim_stalk_eq_one_of_maximal_ramificationLocus_of_purityHolds hR hz hzmax
    hpurity

/-- **Purity of the branch locus in local dimension at most two.** The maximal points of the
branch locus of `f`, if the ramification locus is not all of `X`, have local dimension one,
provided their local rings have dimension at most two. -/
theorem ringKrullDim_stalk_eq_one_of_maximal_branchLocus_of_ringKrullDim_le_two
    (hR : f.ramificationLocus ≠ Set.univ) {w : Y} (hw : w ∈ f.branchLocus)
    (hmax : ∀ w' ∈ f.branchLocus, w' ⤳ w → w' = w)
    (hdim₂ : ringKrullDim (Y.presheaf.stalk w) ≤ 2) :
    ringKrullDim (Y.presheaf.stalk w) = 1 :=
  f.ringKrullDim_stalk_eq_one_of_maximal_branchLocus_of_purityHolds hR hw hmax
    fun _ _ _ h₂ hle ↦ TauCeti.IsLocalRing.purityHolds_of_ringKrullDim_eq_two
      (le_antisymm (hle.trans hdim₂) h₂)

/-- **Étaleness in codimension one, from purity for regular local rings.** Let `f : X ⟶ Y` be a
dominant, locally quasi-finite morphism, locally of finite type, from a normal integral scheme to
a regular scheme, and suppose `f` is étale at the generic point of `X`. If purity holds for every
regular local ring of dimension between `2` and that of some local ring of `Y`, then `f` is étale
iff its stalk map is formally unramified at every point `x` with `dim 𝒪_{X,x} = 1`. -/
theorem etale_iff_formallyUnramified_stalk_codimOne_of_purityHolds
    (hgen : ∃ U : X.Opens, genericPoint X ∈ U ∧ Etale (U.ι ≫ f))
    (hpurity : ∀ (y : Y) (A : Type u) [CommRing A] [IsRegularLocalRing A],
      2 ≤ ringKrullDim A → ringKrullDim A ≤ ringKrullDim (Y.presheaf.stalk y) →
        TauCeti.IsLocalRing.PurityHolds A) :
    Etale f ↔ ∀ x : X, ringKrullDim (X.presheaf.stalk x) = 1 →
      (f.stalkMap x).hom.FormallyUnramified := by
  have := f.irreducibleSpace_of_isDominant
  have : IsIntegral Y := isIntegral_of_irreducibleSpace_of_isReduced Y
  rw [← nonEtaleLocus_eq_empty_iff, ← ramificationLocus_eq_nonEtaleLocus]
  refine ⟨fun h x _ ↦ not_not.mp fun hx ↦ h.subset (mem_ramificationLocus_iff.mpr hx),
    fun hunram ↦ ?_⟩
  -- The generic point is unramified, so the ramification locus is not all of `X`; a ramified
  -- point would then specialize from a maximal ramified point, of local dimension one.
  have hR : f.ramificationLocus ≠ Set.univ := fun h ↦ mem_nonEtaleLocus_iff.mp
    (f.ramificationLocus_subset_nonEtaleLocus (h ▸ Set.mem_univ (genericPoint X))) hgen
  refine Set.eq_empty_of_forall_notMem fun x hx ↦ ?_
  obtain ⟨z, hz, -, hmax⟩ := f.isClosed_ramificationLocus.exists_maximal_specializes hx
  exact mem_ramificationLocus_iff.mp hz (hunram z
    (f.ringKrullDim_stalk_eq_one_of_maximal_ramificationLocus_of_purityHolds hR hz hmax
      (hpurity (f z))))

/-- **Étaleness in codimension one over a regular scheme of dimension at most two.** Let
`f : X ⟶ Y` be a dominant, locally quasi-finite morphism, locally of finite type, from a normal
integral scheme to a regular scheme whose local rings have dimension at most two, and suppose `f`
is étale at the generic point of `X`. Then `f` is étale iff its stalk map is formally unramified
at every point `x` with `dim 𝒪_{X,x} = 1`. -/
theorem etale_iff_formallyUnramified_stalk_codimOne_of_ringKrullDim_le_two
    (hgen : ∃ U : X.Opens, genericPoint X ∈ U ∧ Etale (U.ι ≫ f))
    (hdim₂ : ∀ y : Y, ringKrullDim (Y.presheaf.stalk y) ≤ 2) :
    Etale f ↔ ∀ x : X, ringKrullDim (X.presheaf.stalk x) = 1 →
      (f.stalkMap x).hom.FormallyUnramified :=
  f.etale_iff_formallyUnramified_stalk_codimOne_of_purityHolds hgen
    fun y _ _ _ h₂ hle ↦ TauCeti.IsLocalRing.purityHolds_of_ringKrullDim_eq_two
      (le_antisymm (hle.trans (hdim₂ y)) h₂)

end Loci

end AlgebraicGeometry.Scheme.Hom
