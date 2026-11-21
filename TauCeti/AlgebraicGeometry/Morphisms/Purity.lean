/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.RegularLocalRing.Defs
public import TauCeti.AlgebraicGeometry.FiniteEtale.PuncturedSpectrum
public import TauCeti.AlgebraicGeometry.Morphisms.RamificationLocus
public import TauCeti.AlgebraicGeometry.Morphisms.StalkMap
public import TauCeti.AlgebraicGeometry.Scheme.Regular.Scheme
import TauCeti.AlgebraicGeometry.FiniteEtale.BranchPurity
import TauCeti.AlgebraicGeometry.Morphisms.BranchLocus
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

Under the global hypotheses of SGA 1, Exposé X, Théorème 3.1, purity of the branch locus becomes a
statement about loci. Let `f : X ⟶ Y` be a dominant morphism of integral schemes, locally of
finite type and locally quasi-finite, with `X` normal and `Y` regular, and suppose the
ramification locus of `f` is not all of `X`. Then every point `z` of the ramification locus with
no proper generization in it has `dim 𝒪_{X,z} = 1`: as the locus is closed and misses the
generic point, `dim 𝒪_{X,z} ≥ 1`, and if it were at least two, every codimension-one
generization of `z` would be unramified, so purity of the branch locus would make `f` étale at
`z`. Since `dim 𝒪_{X,z} = dim 𝒪_{Y,f z}` for such morphisms, the maximal points of the branch locus
have codimension one as well. The hypothesis on the ramification locus cannot be dropped: the
relative Frobenius of the affine line in characteristic `p` is ramified everywhere. As a global
consequence, such a morphism, unramified at the generic point of `X`, is étale as soon as it is
unramified at every point of codimension one, since a ramified point would generize to a maximal
one, of codimension one. All these statements assume purity for regular local rings in the
relevant dimensions, and hold unconditionally when the local rings of `Y` have dimension at most
two.

## Main results

* `Scheme.Hom.exists_etale_of_formallyUnramified_stalk_codimOne_of_purityHolds`:
  purity of the branch locus at `x`, assuming purity for regular local rings of dimension between
  two and the dimension of `𝒪_{Y,f x}`.
* `Scheme.Hom.exists_etale_of_formallyUnramified_stalk_codimOne_of_ringKrullDim_le_two`:
  purity of the branch locus at `x` when `𝒪_{Y,f x}` has dimension one or two.
* `Scheme.Hom.ringKrullDim_stalk_eq_one_of_maximal_ramificationLocus_of_purityHolds`,
  `Scheme.Hom.ringKrullDim_stalk_eq_one_of_maximal_branchLocus_of_purityHolds`: the maximal
  points of the ramification and branch loci have codimension one, assuming purity for regular
  local rings, and their unconditional forms `..._of_ringKrullDim_le_two` when the local ring of
  `Y` at the image has dimension at most two.
* `Scheme.Hom.etale_iff_formallyUnramified_stalk_codimOne_of_purityHolds`: a morphism as above,
  unramified at the generic point, is étale iff it is unramified at every point of codimension
  one, assuming purity for regular local rings, and its unconditional form
  `Scheme.Hom.etale_iff_formallyUnramified_stalk_codimOne_of_ringKrullDim_le_two` when the local
  rings of `Y` have dimension at most two.

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
    (TauCeti.IsLocalRing.purityHolds_of_two_le_of_le hdim₂) hunram

variable (f : X ⟶ Y)

/-- **Purity of the ramification locus, from purity for regular local rings.** Let `f : X ⟶ Y` be
a dominant morphism of integral schemes, locally of finite type over a locally Noetherian scheme,
whose ramification locus is not all of `X`. Let `z` be a point of the ramification locus with no
proper generization in it, at which `f` is quasi-finite, `𝒪_{X,z}` is integrally closed and
`𝒪_{Y,f z}` is a regular local ring. If purity holds for every regular local ring of dimension
between `2` and that of `𝒪_{Y,f z}`, then `𝒪_{X,z}` has dimension one. -/
@[stacks 0BMB "consequence: the maximal points of the ramification locus have codimension one,
from purity for regular local rings; SGA 1, Exposé X, Théorème 3.1"]
theorem ringKrullDim_stalk_eq_one_of_maximal_ramificationLocus_of_purityHolds
    [IsLocallyNoetherian Y] [IsIntegral X] [IsIntegral Y] [IsDominant f] [LocallyOfFiniteType f]
    (hR : f.ramificationLocus ≠ Set.univ) {z : X} (hz : z ∈ f.ramificationLocus)
    (hmax : ∀ z' ∈ f.ramificationLocus, z' ⤳ z → z' = z) (hqf : f.QuasiFiniteAt z)
    [IsIntegrallyClosed (X.presheaf.stalk z)] [IsRegularLocalRing (Y.presheaf.stalk (f z))]
    (hpurity : ∀ (A : Type u) [CommRing A] [IsRegularLocalRing A], 2 ≤ ringKrullDim A →
      ringKrullDim A ≤ ringKrullDim (Y.presheaf.stalk (f z)) →
        TauCeti.IsLocalRing.PurityHolds A) :
    ringKrullDim (X.presheaf.stalk z) = 1 := by
  have hclosed := f.isClosed_ramificationLocus
  -- The ramification locus is closed and proper, so it misses the generic point of `X`. Hence
  -- `z` has a proper generization, and `𝒪_{X,z}` has positive dimension.
  have hgen : ¬IsMax z := fun h ↦ hR <| Set.eq_univ_of_forall fun x ↦
    (genericPoint_specializes x).mem_closed hclosed <|
      ((Scheme.le_iff_specializes).mp
        (h ((Scheme.le_iff_specializes).mpr (genericPoint_specializes z)))).mem_closed
        hclosed hz
  have h₁ : 1 ≤ ringKrullDim (X.presheaf.stalk z) := by
    rw [ringKrullDim_stalk_eq_coheight]
    exact mod_cast Order.one_le_iff_ne_zero.mpr (Order.coheight_eq_zero.not.mpr hgen)
  have hdim := f.ringKrullDim_stalk_eq_of_quasiFiniteAt hqf
  refine le_antisymm (not_lt.mp fun h₂ ↦ ?_) h₁
  -- In dimension at least two, every codimension-one generization of `z` is a proper
  -- generization, hence unramified, and purity of the branch locus makes `f` étale at `z`.
  obtain ⟨U, hzU, hU⟩ := f.exists_etale_of_formallyUnramified_stalk_codimOne_of_purityHolds z hqf
    hdim.ge (hdim ▸ h₁) hpurity fun x hxz hx ↦ not_not.mp fun hxR ↦ by
      rw [hmax x (mem_ramificationLocus_iff.mpr hxR) hxz] at hx
      exact h₂.ne' hx
  exact mem_nonEtaleLocus_iff.mp (f.ramificationLocus_subset_nonEtaleLocus hz) ⟨U, hzU, hU⟩

/-- **Purity of the ramification locus in dimension at most two.** Under the hypotheses of
`ringKrullDim_stalk_eq_one_of_maximal_ramificationLocus_of_purityHolds`, if `𝒪_{Y,f z}` has
dimension at most two, then `𝒪_{X,z}` has dimension one. -/
theorem ringKrullDim_stalk_eq_one_of_maximal_ramificationLocus_of_ringKrullDim_le_two
    [IsLocallyNoetherian Y] [IsIntegral X] [IsIntegral Y] [IsDominant f] [LocallyOfFiniteType f]
    (hR : f.ramificationLocus ≠ Set.univ) {z : X} (hz : z ∈ f.ramificationLocus)
    (hmax : ∀ z' ∈ f.ramificationLocus, z' ⤳ z → z' = z) (hqf : f.QuasiFiniteAt z)
    [IsIntegrallyClosed (X.presheaf.stalk z)] [IsRegularLocalRing (Y.presheaf.stalk (f z))]
    (hdim₂ : ringKrullDim (Y.presheaf.stalk (f z)) ≤ 2) :
    ringKrullDim (X.presheaf.stalk z) = 1 :=
  f.ringKrullDim_stalk_eq_one_of_maximal_ramificationLocus_of_purityHolds hR hz hmax hqf
    (TauCeti.IsLocalRing.purityHolds_of_two_le_of_le hdim₂)

/-- **Purity of the branch locus as a locus, from purity for regular local rings.** Let
`f : X ⟶ Y` be a dominant morphism of integral schemes, locally of finite type and locally
quasi-finite over a locally Noetherian scheme, with `X` normal, whose ramification locus is not
all of `X`. Let `y` be a point of the branch locus with no proper generization in it, at which
`𝒪_{Y,y}` is a regular local ring. If purity holds for every regular local ring of dimension
between `2` and that of `𝒪_{Y,y}`, then `𝒪_{Y,y}` has dimension one. -/
@[stacks 0BMB "consequence: the maximal points of the branch locus have codimension one, from
purity for regular local rings; SGA 1, Exposé X, Théorème 3.1"]
theorem ringKrullDim_stalk_eq_one_of_maximal_branchLocus_of_purityHolds
    [IsLocallyNoetherian Y] [IsIntegral X] [IsIntegral Y] [IsDominant f] [LocallyOfFiniteType f]
    [LocallyQuasiFinite f] [TauCeti.AlgebraicGeometry.IsNormalScheme X]
    (hR : f.ramificationLocus ≠ Set.univ) {y : Y} (hy : y ∈ f.branchLocus)
    (hmax : ∀ y' ∈ f.branchLocus, y' ⤳ y → y' = y) [IsRegularLocalRing (Y.presheaf.stalk y)]
    (hpurity : ∀ (A : Type u) [CommRing A] [IsRegularLocalRing A], 2 ≤ ringKrullDim A →
      ringKrullDim A ≤ ringKrullDim (Y.presheaf.stalk y) → TauCeti.IsLocalRing.PurityHolds A) :
    ringKrullDim (Y.presheaf.stalk y) = 1 := by
  obtain ⟨x, hx, hxy⟩ := mem_branchLocus_iff.mp hy
  obtain ⟨z, hz, -, rfl, hzmax⟩ :=
    f.exists_maximal_ramificationLocus_over_of_maximal_branchLocus hmax hx hxy
  rw [← f.ringKrullDim_stalk_eq_of_quasiFiniteAt (f.quasiFiniteAt z)]
  exact f.ringKrullDim_stalk_eq_one_of_maximal_ramificationLocus_of_purityHolds hR hz hzmax
    (f.quasiFiniteAt z) hpurity

/-- **Purity of the branch locus as a locus, in dimension at most two.** Under the hypotheses of
`ringKrullDim_stalk_eq_one_of_maximal_branchLocus_of_purityHolds`, if `𝒪_{Y,y}` has dimension at
most two, then it has dimension one. -/
theorem ringKrullDim_stalk_eq_one_of_maximal_branchLocus_of_ringKrullDim_le_two
    [IsLocallyNoetherian Y] [IsIntegral X] [IsIntegral Y] [IsDominant f] [LocallyOfFiniteType f]
    [LocallyQuasiFinite f] [TauCeti.AlgebraicGeometry.IsNormalScheme X]
    (hR : f.ramificationLocus ≠ Set.univ) {y : Y} (hy : y ∈ f.branchLocus)
    (hmax : ∀ y' ∈ f.branchLocus, y' ⤳ y → y' = y) [IsRegularLocalRing (Y.presheaf.stalk y)]
    (hdim₂ : ringKrullDim (Y.presheaf.stalk y) ≤ 2) :
    ringKrullDim (Y.presheaf.stalk y) = 1 :=
  f.ringKrullDim_stalk_eq_one_of_maximal_branchLocus_of_purityHolds hR hy hmax
    (TauCeti.IsLocalRing.purityHolds_of_two_le_of_le hdim₂)

/-- **Étaleness is detected in codimension one, from purity for regular local rings.** Let
`f : X ⟶ Y` be a dominant morphism, locally of finite type and locally quasi-finite, from a normal
integral scheme to a regular scheme, unramified at the generic point of `X` (equivalently, étale
there). If purity holds for every regular local ring of dimension at least `2` and at most that of
some local ring of `Y`, then `f` is étale iff its stalk map is formally unramified at every point
of `X` whose local ring has dimension one. Finite dominant morphisms are an instance. -/
theorem etale_iff_formallyUnramified_stalk_codimOne_of_purityHolds
    [IsIntegral X] [IsDominant f] [LocallyOfFiniteType f] [LocallyQuasiFinite f]
    [TauCeti.AlgebraicGeometry.IsNormalScheme X] [TauCeti.AlgebraicGeometry.IsRegular Y]
    (hgen : (f.stalkMap (genericPoint X)).hom.FormallyUnramified)
    (hpurity : ∀ (y : Y) (A : Type u) [CommRing A] [IsRegularLocalRing A], 2 ≤ ringKrullDim A →
      ringKrullDim A ≤ ringKrullDim (Y.presheaf.stalk y) → TauCeti.IsLocalRing.PurityHolds A) :
    Etale f ↔ ∀ x : X, ringKrullDim (X.presheaf.stalk x) = 1 →
      (f.stalkMap x).hom.FormallyUnramified := by
  have := f.irreducibleSpace_of_isDominant
  have : IsIntegral Y := isIntegral_of_irreducibleSpace_of_isReduced Y
  rw [← nonEtaleLocus_eq_empty_iff, ← ramificationLocus_eq_nonEtaleLocus]
  refine ⟨fun h x _ ↦ not_not.mp fun hx ↦ (h ▸ mem_ramificationLocus_iff.mpr hx :
    x ∈ (∅ : Set X)), fun h ↦ ?_⟩
  refine Set.eq_empty_of_forall_notMem fun x hx ↦ ?_
  -- A ramified point generizes to a maximal one, which has local dimension one by purity.
  obtain ⟨z, hz, -, hzmax⟩ := f.exists_maximal_ramificationLocus_specializes hx
  have hR : f.ramificationLocus ≠ Set.univ := fun hR ↦
    mem_ramificationLocus_iff.mp (hR ▸ Set.mem_univ (genericPoint X)) hgen
  exact mem_ramificationLocus_iff.mp hz (h z
    (f.ringKrullDim_stalk_eq_one_of_maximal_ramificationLocus_of_purityHolds hR hz hzmax
      (f.quasiFiniteAt z) (hpurity (f z))))

/-- **Étaleness is detected in codimension one, over a base of dimension at most two.** Under the
hypotheses of `etale_iff_formallyUnramified_stalk_codimOne_of_purityHolds`, if every local ring of
`Y` has dimension at most two, then `f` is étale iff its stalk map is formally unramified at every
point of `X` whose local ring has dimension one. -/
theorem etale_iff_formallyUnramified_stalk_codimOne_of_ringKrullDim_le_two
    [IsIntegral X] [IsDominant f] [LocallyOfFiniteType f] [LocallyQuasiFinite f]
    [TauCeti.AlgebraicGeometry.IsNormalScheme X] [TauCeti.AlgebraicGeometry.IsRegular Y]
    (hgen : (f.stalkMap (genericPoint X)).hom.FormallyUnramified)
    (hdim₂ : ∀ y : Y, ringKrullDim (Y.presheaf.stalk y) ≤ 2) :
    Etale f ↔ ∀ x : X, ringKrullDim (X.presheaf.stalk x) = 1 →
      (f.stalkMap x).hom.FormallyUnramified :=
  f.etale_iff_formallyUnramified_stalk_codimOne_of_purityHolds hgen
    fun y ↦ TauCeti.IsLocalRing.purityHolds_of_two_le_of_le (hdim₂ y)

end AlgebraicGeometry.Scheme.Hom
