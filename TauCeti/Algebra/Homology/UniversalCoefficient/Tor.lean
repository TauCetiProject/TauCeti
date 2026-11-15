/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Symmetric
public import Mathlib.Algebra.Homology.Double
public import Mathlib.CategoryTheory.Monoidal.Closed.Braided
public import Mathlib.Data.ZMod.Basic
public import Mathlib.RingTheory.Finiteness.Basic
public import TauCeti.Algebra.Category.ModuleCat.ChangeOfRings
public import TauCeti.Algebra.Category.ModuleCat.Monoidal.Tor
public import TauCeti.Algebra.Category.ModuleCat.Projective.Dimension
public import TauCeti.Algebra.Homology.Boundaries
public import TauCeti.Algebra.Homology.HomologicalComplex.Projective.Dimension
public import TauCeti.Algebra.Homology.HomotopyCategory.Bounded.Basic
public import TauCeti.Algebra.Homology.ShortComplex.PreservesHomology
public import TauCeti.Algebra.Homology.ShortComplex.ShortExact

/-!
# The universal coefficient sequence for right-exact functors and tensor products

Let `K` be a homological complex of arbitrary shape `c` in an abelian category `C` with projective
resolutions, and let `F : C ⥤ D` be a right-exact additive functor into an abelian category `D`.
For any relation `hij : c.Rel i j`, write `Zₖ = K.cycles k`, `Hₖ(K) = K.homology k`, and
`Bⱼ = ker(Zⱼ ⟶ Hⱼ(K))` for the boundaries in degree `j`.

Since `F` preserves cokernels, `F(Hᵢ(K))` is the cokernel of `F(K_{prev i}) ⟶ F(Zᵢ)` and admits a
canonical comparison morphism `K.mapHomologyComparison F i : F(Hᵢ(K)) ⟶ Hᵢ(F(K))`, natural in
both `K` and `F`. When `Zᵢ ⟶ Kᵢ` is a split monomorphism, choosing a retraction induces a
retraction `K.mapHomologyRetraction F i : Hᵢ(F(K)) ⟶ F(Hᵢ(K))`, natural in `F`.

Assume now that `Bⱼ` and `Zⱼ` are projective and `Zⱼ ⟶ Kⱼ` is a split monomorphism (all three hold
automatically when every object of `C` has projective dimension at most one and `Kⱼ` and
`K_{next j}` are projective, in particular for complexes of projective modules over a principal
ideal domain). Then `0 ⟶ Bⱼ ⟶ Zⱼ ⟶ Hⱼ(K) ⟶ 0` (`K.boundariesShortComplex j`) is a length-one
projective presentation of `Hⱼ(K)`, so `L₁F(Hⱼ(K)) ≅ ker(F(Bⱼ) ⟶ F(Zⱼ))` by
`CategoryTheory.ShortComplex.ShortExact.leftDerivedOneIsoKernel`. Corestricting the differential to
`F(Kᵢ) ⟶ F(Bⱼ)` sends cycles of `F(K)` into `ker(F(Bⱼ) ⟶ F(Zⱼ))` (because `F(Zⱼ) ⟶ F(Kⱼ)` is a
split monomorphism) and kills boundaries of `F(K)`, yielding the connecting morphism
`K.homologyToLeftDerivedOne F hij : Hᵢ(F(K)) ⟶ (F.leftDerived 1).obj (K.homology j)`. Moreover,
projectivity of `Bⱼ` splits `0 ⟶ Zᵢ ⟶ Kᵢ ⟶ Bⱼ ⟶ 0`, and applying `F` to that splitting produces a
`ShortComplex.Splitting` (hence short exactness) of

`0 ⟶ F(Hᵢ(K)) ⟶ Hᵢ(F(K)) ⟶ (L₁F)(Hⱼ(K)) ⟶ 0`.

Specializing `F = tensorRight M` over a commutative ring `R` of projective dimension at most one
and composing with the balancing isomorphism `ModuleCat.tor'OneIsoTorOne R : Tor'₁^R ≅ Tor₁^R`
yields the balanced Tor universal coefficient short exact sequence

`0 ⟶ Hᵢ(K) ⊗[R] M ⟶ Hᵢ(K ⊗[R] M) ⟶ Tor₁^R(Hⱼ(K), M) ⟶ 0`,

split over `R` and natural in both `K` and `M`.

When `f : R →+* S` is a homomorphism of commutative rings, functoriality in the second variable
equips `Torₙ^R(X, S)` with an `S`-module structure (`ModuleCat.torExtendScalars f n`), naturally
isomorphic for `n = 1` in `ModuleCat S` to `((ModuleCat.extendScalars f).leftDerived 1).obj X`
(`ModuleCat.extendScalarsLeftDerivedOneIsoTor`). Transporting the `extendScalars f` sequence along
this isomorphism gives the `S`-linear universal coefficient short exact sequence and `S`-linear
splitting for `S ⊗[R] K`.

Finally, using the chain map from `0 ⟶ ℤ ⟶[·2] ℤ ⟶ 0` to `0 ⟶ ℤ ⟶ 0` with `ℤ/2ℤ` coefficients,
we prove that the universal coefficient sequence admits neither a family of retractions nor a
family of sections natural in all chain maps between bounded degreewise finitely generated free
cochain complexes over `ℤ`.

## References

* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Section 3A, Theorem 3A.3.
* C. A. Weibel, *An Introduction to Homological Algebra*, Cambridge Studies in Advanced
  Mathematics 38, Cambridge University Press (1994), Theorem 3.6.1.
-/

public section

noncomputable section

open CategoryTheory Limits MonoidalCategory

namespace HomologicalComplex

section RightExactFunctor

variable {C D ι : Type*} [Category* C] [Abelian C] [Category* D] [Abelian D]
  {c : ComplexShape ι}

private def descHomologyAux {E : Type*} [Category* E] [Abelian E] (L : HomologicalComplex E c)
    {i : ι} {A : E} (k : L.cycles i ⟶ A) (hk : L.toCycles (c.prev i) i ≫ k = 0) :
    L.homology i ⟶ A :=
  Cofork.IsColimit.desc (L.homologyIsCokernel (c.prev i) i rfl) k (by rw [hk, zero_comp])

@[reassoc (attr := simp)]
private lemma homologyπ_descHomologyAux {E : Type*} [Category* E] [Abelian E]
    (L : HomologicalComplex E c) {i : ι} {A : E} (k : L.cycles i ⟶ A)
    (hk : L.toCycles (c.prev i) i ≫ k = 0) :
    L.homologyπ i ≫ descHomologyAux L k hk = k :=
  Cofork.IsColimit.π_desc (L.homologyIsCokernel (c.prev i) i rfl)

/-- When `F` preserves cokernels, `F.map (K.homologyπ i)` exhibits `F.obj (K.homology i)` as the
cokernel of `F.map (K.toCycles (c.prev i) i)`. -/
def mapHomologyIsCokernel (K : HomologicalComplex C c) (F : C ⥤ D) [F.Additive]
    [PreservesColimitsOfShape WalkingParallelPair F] (i : ι) :
    IsColimit (CokernelCofork.ofπ (F.map (K.homologyπ i))
      (by rw [← F.map_comp, K.toCycles_comp_homologyπ (c.prev i), F.map_zero]) :
      Cofork (F.map (K.toCycles (c.prev i) i)) 0) :=
  isColimitCoforkMapOfIsColimit' F _ (K.homologyIsCokernel (c.prev i) i rfl)

/-- Morphisms out of `F(Hᵢ(K))` are determined by precomposition with `F.map (K.homologyπ i)`
whenever `F` preserves cokernels. -/
lemma map_homologyπ_ext (K : HomologicalComplex C c) (F : C ⥤ D) [F.Additive]
    [PreservesColimitsOfShape WalkingParallelPair F] (i : ι) {A : D}
    {f g : F.obj (K.homology i) ⟶ A}
    (h : F.map (K.homologyπ i) ≫ f = F.map (K.homologyπ i) ≫ g) : f = g :=
  Cofork.IsColimit.hom_ext (K.mapHomologyIsCokernel F i) h

/-- The canonical comparison `F(Zᵢ(K)) ⟶ Zᵢ(F(K))` induced by `F.map (K.iCycles i)`. -/
def mapCyclesComparison (K : HomologicalComplex C c) (F : C ⥤ D) [F.Additive] (i : ι) :
    F.obj (K.cycles i) ⟶ ((F.mapHomologicalComplex c).obj K).cycles i :=
  ((F.mapHomologicalComplex c).obj K).liftCycles (F.map (K.iCycles i)) (c.next i) rfl
    (by simp [← F.map_comp])

/-- `mapCyclesComparison` intertwines the cycle inclusions into `F(Kᵢ)`. -/
@[reassoc (attr := simp)]
lemma mapCyclesComparison_iCycles (K : HomologicalComplex C c) (F : C ⥤ D) [F.Additive] (i : ι) :
    K.mapCyclesComparison F i ≫ ((F.mapHomologicalComplex c).obj K).iCycles i =
      F.map (K.iCycles i) :=
  liftCycles_i _ _ _ _ _

@[reassoc]
private lemma map_toCycles_mapCyclesComparison (K : HomologicalComplex C c) (F : C ⥤ D)
    [F.Additive] (j i : ι) :
    F.map (K.toCycles j i) ≫ K.mapCyclesComparison F i =
      ((F.mapHomologicalComplex c).obj K).toCycles j i := by
  rw [← cancel_mono (((F.mapHomologicalComplex c).obj K).iCycles i), Category.assoc,
    mapCyclesComparison_iCycles, toCycles_i, ← F.map_comp, toCycles_i]
  rfl

/-- **Canonical homology comparison for a right-exact additive functor.** Because `F` preserves the
cokernel presentation `K_{prev i} ⟶ Zᵢ(K) ⟶ Hᵢ(K) ⟶ 0`, `mapCyclesComparison` descends to a
canonical morphism `F(Hᵢ(K)) ⟶ Hᵢ(F(K))`. -/
def mapHomologyComparison (K : HomologicalComplex C c) (F : C ⥤ D) [F.Additive]
    [PreservesColimitsOfShape WalkingParallelPair F] (i : ι) :
    F.obj (K.homology i) ⟶ ((F.mapHomologicalComplex c).obj K).homology i :=
  Cofork.IsColimit.desc (K.mapHomologyIsCokernel F i)
    (K.mapCyclesComparison F i ≫ ((F.mapHomologicalComplex c).obj K).homologyπ i)
    (by rw [map_toCycles_mapCyclesComparison_assoc,
      ((F.mapHomologicalComplex c).obj K).toCycles_comp_homologyπ (c.prev i), zero_comp])

/-- `mapHomologyComparison` sends the image of a cycle class to the class of the mapped cycle. -/
@[reassoc (attr := simp)]
lemma map_homologyπ_mapHomologyComparison (K : HomologicalComplex C c) (F : C ⥤ D) [F.Additive]
    [PreservesColimitsOfShape WalkingParallelPair F] (i : ι) :
    F.map (K.homologyπ i) ≫ K.mapHomologyComparison F i =
      K.mapCyclesComparison F i ≫ ((F.mapHomologicalComplex c).obj K).homologyπ i :=
  Cofork.IsColimit.π_desc (K.mapHomologyIsCokernel F i)

/-- `mapHomologyComparison` is natural in chain maps `φ : K ⟶ L`. -/
@[reassoc]
lemma mapHomologyComparison_naturality {K L : HomologicalComplex C c} (φ : K ⟶ L) (F : C ⥤ D)
    [F.Additive] [PreservesColimitsOfShape WalkingParallelPair F] (i : ι) :
    F.map (homologyMap φ i) ≫ L.mapHomologyComparison F i =
      K.mapHomologyComparison F i ≫ homologyMap ((F.mapHomologicalComplex c).map φ) i := by
  refine K.map_homologyπ_ext F i ?_
  rw [← F.map_comp_assoc, homologyπ_naturality, F.map_comp_assoc,
    map_homologyπ_mapHomologyComparison, map_homologyπ_mapHomologyComparison_assoc,
    homologyπ_naturality, ← Category.assoc, ← Category.assoc]
  congr 1
  rw [← cancel_mono (((F.mapHomologicalComplex c).obj L).iCycles i), Category.assoc, Category.assoc,
    mapCyclesComparison_iCycles, cyclesMap_i, mapCyclesComparison_iCycles_assoc,
    Functor.mapHomologicalComplex_map_f, ← F.map_comp, ← F.map_comp, cyclesMap_i]

/-- `mapHomologyComparison` is natural in natural transformations `α : F ⟶ G`. -/
@[reassoc]
lemma mapHomologyComparison_naturality_functor (K : HomologicalComplex C c) {F G : C ⥤ D}
    [F.Additive] [G.Additive] [PreservesColimitsOfShape WalkingParallelPair F]
    [PreservesColimitsOfShape WalkingParallelPair G] (α : F ⟶ G) (i : ι) :
    α.app (K.homology i) ≫ K.mapHomologyComparison G i =
      K.mapHomologyComparison F i ≫
        homologyMap ((NatTrans.mapHomologicalComplex α c).app K) i := by
  refine K.map_homologyπ_ext F i ?_
  rw [α.naturality_assoc, map_homologyπ_mapHomologyComparison,
    map_homologyπ_mapHomologyComparison_assoc, homologyπ_naturality,
    ← Category.assoc, ← Category.assoc]
  congr 1
  rw [← cancel_mono (((G.mapHomologicalComplex c).obj K).iCycles i), Category.assoc, Category.assoc,
    mapCyclesComparison_iCycles, cyclesMap_i, mapCyclesComparison_iCycles_assoc,
    NatTrans.mapHomologicalComplex_app_f, α.naturality]

/-- When `F` is exact (`[F.PreservesHomology]`), `mapHomologyComparison` is the inverse of
`(K.sc i).mapHomologyIso F` and is therefore an isomorphism. -/
lemma mapHomologyComparison_eq_of_preservesHomology (K : HomologicalComplex C c) (F : C ⥤ D)
    [F.Additive] [PreservesColimitsOfShape WalkingParallelPair F] [F.PreservesHomology] (i : ι) :
    K.mapHomologyComparison F i = ((K.sc i).mapHomologyIso F).inv := by
  have hc : K.mapCyclesComparison F i = ((K.sc i).mapCyclesIso F).inv := by
    rw [← cancel_mono (((F.mapHomologicalComplex c).obj K).iCycles i), mapCyclesComparison_iCycles]
    exact ((K.sc i).mapCyclesIso_inv_comp_iCycles F).symm
  refine K.map_homologyπ_ext F i ?_
  rw [map_homologyπ_mapHomologyComparison, hc, ← cancel_mono ((K.sc i).mapHomologyIso F).hom,
    Category.assoc, Category.assoc, Iso.inv_hom_id, Category.comp_id]
  exact (congrArg (((K.sc i).mapCyclesIso F).inv ≫ ·)
    ((K.sc i).homologyπ_comp_mapHomologyIso_hom F)).trans
    (Iso.inv_hom_id_assoc ((K.sc i).mapCyclesIso F) (F.map (K.sc i).homologyπ))

instance isIso_mapHomologyComparison_of_preservesHomology (K : HomologicalComplex C c) (F : C ⥤ D)
    [F.Additive] [PreservesColimitsOfShape WalkingParallelPair F] [F.PreservesHomology] (i : ι) :
    IsIso (K.mapHomologyComparison F i) := by
  rw [K.mapHomologyComparison_eq_of_preservesHomology F i]
  infer_instance

/-- Given any retraction `r : K.X i ⟶ K.cycles i` of `K.iCycles i`, `F.map (r ≫ K.homologyπ i)`
vanishes on incoming boundaries of `F(K)` and therefore descends to a retraction
`Hᵢ(F(K)) ⟶ F(Hᵢ(K))` of `mapHomologyComparison`. -/
def mapHomologyRetractionOf (K : HomologicalComplex C c) (F : C ⥤ D) [F.Additive] {i : ι}
    (r : K.X i ⟶ K.cycles i) (hr : K.iCycles i ≫ r = 𝟙 (K.cycles i)) :
    ((F.mapHomologicalComplex c).obj K).homology i ⟶ F.obj (K.homology i) :=
  descHomologyAux ((F.mapHomologicalComplex c).obj K)
    (((F.mapHomologicalComplex c).obj K).iCycles i ≫ F.map (r ≫ K.homologyπ i))
    (by
      rw [toCycles_i_assoc, Functor.mapHomologicalComplex_obj_d, ← F.map_comp,
        ← K.toCycles_i_assoc, reassoc_of% hr, K.toCycles_comp_homologyπ (c.prev i), F.map_zero])

/-- `mapHomologyRetractionOf` evaluates on `homologyπ` via the chosen retraction `r`. -/
@[reassoc (attr := simp)]
lemma homologyπ_mapHomologyRetractionOf (K : HomologicalComplex C c) (F : C ⥤ D) [F.Additive]
    {i : ι} (r : K.X i ⟶ K.cycles i) (hr : K.iCycles i ≫ r = 𝟙 (K.cycles i)) :
    ((F.mapHomologicalComplex c).obj K).homologyπ i ≫ K.mapHomologyRetractionOf F r hr =
      ((F.mapHomologicalComplex c).obj K).iCycles i ≫ F.map (r ≫ K.homologyπ i) :=
  homologyπ_descHomologyAux _ _ _

/-- `mapHomologyRetractionOf F r hr` is a retraction of `mapHomologyComparison F i`. -/
@[reassoc (attr := simp)]
lemma mapHomologyComparison_mapHomologyRetractionOf (K : HomologicalComplex C c) (F : C ⥤ D)
    [F.Additive] [PreservesColimitsOfShape WalkingParallelPair F] {i : ι}
    (r : K.X i ⟶ K.cycles i) (hr : K.iCycles i ≫ r = 𝟙 (K.cycles i)) :
    K.mapHomologyComparison F i ≫ K.mapHomologyRetractionOf F r hr = 𝟙 (F.obj (K.homology i)) := by
  refine K.map_homologyπ_ext F i ?_
  rw [map_homologyπ_mapHomologyComparison_assoc, homologyπ_mapHomologyRetractionOf,
    mapCyclesComparison_iCycles_assoc, ← F.map_comp, reassoc_of% hr, Category.comp_id]

/-- For fixed `r : K.X i ⟶ K.cycles i`, `mapHomologyRetractionOf` is natural in `F`. -/
@[reassoc]
lemma mapHomologyRetractionOf_naturality_functor (K : HomologicalComplex C c) {F G : C ⥤ D}
    [F.Additive] [G.Additive] {i : ι} (r : K.X i ⟶ K.cycles i)
    (hr : K.iCycles i ≫ r = 𝟙 (K.cycles i)) (α : F ⟶ G) :
    K.mapHomologyRetractionOf F r hr ≫ α.app (K.homology i) =
      homologyMap ((NatTrans.mapHomologicalComplex α c).app K) i ≫
        K.mapHomologyRetractionOf G r hr := by
  rw [← cancel_epi (((F.mapHomologicalComplex c).obj K).homologyπ i),
    homologyπ_mapHomologyRetractionOf_assoc, homologyπ_naturality_assoc,
    homologyπ_mapHomologyRetractionOf, cyclesMap_i_assoc, NatTrans.mapHomologicalComplex_app_f,
    α.naturality]

/-- The retraction `Hᵢ(F(K)) ⟶ F(Hᵢ(K))` associated to `[IsSplitMono (K.iCycles i)]`. -/
def mapHomologyRetraction (K : HomologicalComplex C c) (F : C ⥤ D) [F.Additive] (i : ι)
    [IsSplitMono (K.iCycles i)] :
    ((F.mapHomologicalComplex c).obj K).homology i ⟶ F.obj (K.homology i) :=
  K.mapHomologyRetractionOf F (retraction (K.iCycles i)) (IsSplitMono.id _)

/-- `mapHomologyRetraction F i` is a retraction of `mapHomologyComparison F i`. -/
@[reassoc (attr := simp)]
lemma mapHomologyComparison_mapHomologyRetraction (K : HomologicalComplex C c) (F : C ⥤ D)
    [F.Additive] [PreservesColimitsOfShape WalkingParallelPair F] (i : ι)
    [IsSplitMono (K.iCycles i)] :
    K.mapHomologyComparison F i ≫ K.mapHomologyRetraction F i = 𝟙 (F.obj (K.homology i)) :=
  K.mapHomologyComparison_mapHomologyRetractionOf F _ _

instance isSplitMono_mapHomologyComparison (K : HomologicalComplex C c) (F : C ⥤ D) [F.Additive]
    [PreservesColimitsOfShape WalkingParallelPair F] (i : ι) [IsSplitMono (K.iCycles i)] :
    IsSplitMono (K.mapHomologyComparison F i) :=
  IsSplitMono.mk' { retraction := K.mapHomologyRetraction F i }

/-! ### The connecting morphism `Hᵢ(F(K)) ⟶ (L₁F)(Hⱼ(K))` and short exactness -/

/-- The canonical short exact presentation `0 ⟶ Bⱼ(K) ⟶ Zⱼ(K) ⟶ Hⱼ(K) ⟶ 0` of `K.homology j` by
boundaries and cycles. -/
abbrev boundariesShortComplex (K : HomologicalComplex C c) (j : ι) : ShortComplex C :=
  ShortComplex.mk (kernel.ι (K.homologyπ j)) (K.homologyπ j) (kernel.condition _)

/-- The presentation `0 ⟶ Bⱼ(K) ⟶ Zⱼ(K) ⟶ Hⱼ(K) ⟶ 0` is short exact. -/
lemma boundariesShortComplex_shortExact (K : HomologicalComplex C c) (j : ι) :
    (K.boundariesShortComplex j).ShortExact :=
  TauCeti.kernelSequence_shortExact (K.homologyπ j)

private def cyclesToKernelBoundaries (K : HomologicalComplex C c) (F : C ⥤ D) [F.Additive]
    (i j : ι) [IsSplitMono (K.iCycles j)] :
    ((F.mapHomologicalComplex c).obj K).cycles i ⟶ kernel (F.map (kernel.ι (K.homologyπ j))) :=
  have : IsSplitMono (F.map (K.iCycles j)) := inferInstance
  kernel.lift (F.map (kernel.ι (K.homologyπ j)))
    (((F.mapHomologicalComplex c).obj K).iCycles i ≫ F.map (K.toBoundaries i j))
    (by
      rw [← cancel_mono (F.map (K.iCycles j)), zero_comp, Category.assoc, Category.assoc,
        ← F.map_comp, ← F.map_comp, K.toBoundaries_ι_assoc, K.toCycles_i,
        ← Functor.mapHomologicalComplex_obj_d, iCycles_d])

@[reassoc (attr := simp)]
private lemma cyclesToKernelBoundaries_ι (K : HomologicalComplex C c) (F : C ⥤ D) [F.Additive]
    (i j : ι) [IsSplitMono (K.iCycles j)] :
    K.cyclesToKernelBoundaries F i j ≫ kernel.ι (F.map (kernel.ι (K.homologyπ j))) =
      ((F.mapHomologicalComplex c).obj K).iCycles i ≫ F.map (K.toBoundaries i j) :=
  kernel.lift_ι _ _ _

private def homologyToKernelBoundaries (K : HomologicalComplex C c) (F : C ⥤ D) [F.Additive]
    (i j : ι) [IsSplitMono (K.iCycles j)] :
    ((F.mapHomologicalComplex c).obj K).homology i ⟶ kernel (F.map (kernel.ι (K.homologyπ j))) :=
  descHomologyAux ((F.mapHomologicalComplex c).obj K) (K.cyclesToKernelBoundaries F i j)
    (by
      rw [← cancel_mono (kernel.ι (F.map (kernel.ι (K.homologyπ j)))), zero_comp, Category.assoc,
        cyclesToKernelBoundaries_ι, toCycles_i_assoc, Functor.mapHomologicalComplex_obj_d,
        ← F.map_comp, K.d_toBoundaries, F.map_zero])

@[reassoc (attr := simp)]
private lemma homologyπ_homologyToKernelBoundaries (K : HomologicalComplex C c) (F : C ⥤ D)
    [F.Additive] (i j : ι) [IsSplitMono (K.iCycles j)] :
    ((F.mapHomologicalComplex c).obj K).homologyπ i ≫ K.homologyToKernelBoundaries F i j =
      K.cyclesToKernelBoundaries F i j :=
  homologyπ_descHomologyAux _ _ _

@[reassoc]
private lemma homologyπ_homologyToKernelBoundaries_ι (K : HomologicalComplex C c) (F : C ⥤ D)
    [F.Additive] (i j : ι) [IsSplitMono (K.iCycles j)] :
    ((F.mapHomologicalComplex c).obj K).homologyπ i ≫ K.homologyToKernelBoundaries F i j ≫
      kernel.ι (F.map (kernel.ι (K.homologyπ j))) =
      ((F.mapHomologicalComplex c).obj K).iCycles i ≫ F.map (K.toBoundaries i j) := by
  rw [homologyπ_homologyToKernelBoundaries_assoc, cyclesToKernelBoundaries_ι]

private abbrev universalCoefficientKernelShortComplex (K : HomologicalComplex C c) (F : C ⥤ D)
    [F.Additive] [PreservesColimitsOfShape WalkingParallelPair F] (i j : ι)
    [IsSplitMono (K.iCycles j)] : ShortComplex D :=
  ShortComplex.mk (K.mapHomologyComparison F i) (K.homologyToKernelBoundaries F i j)
    (by
      refine K.map_homologyπ_ext F i ?_
      rw [comp_zero, ← cancel_mono (kernel.ι (F.map (kernel.ι (K.homologyπ j)))), zero_comp]
      simp only [Category.assoc]
      rw [map_homologyπ_mapHomologyComparison_assoc, homologyπ_homologyToKernelBoundaries_ι,
        mapCyclesComparison_iCycles_assoc, ← F.map_comp, K.iCycles_toBoundaries, F.map_zero])

private def universalCoefficientKernelSplitting (K : HomologicalComplex C c) (F : C ⥤ D)
    [F.Additive] [PreservesColimitsOfShape WalkingParallelPair F] {i j : ι} (hij : c.Rel i j)
    [Projective (kernel (K.homologyπ j))] [IsSplitMono (K.iCycles j)] :
    (K.universalCoefficientKernelShortComplex F i j).Splitting := by
  let B₀ : ShortComplex C :=
    ShortComplex.mk (K.iCycles i) (K.toBoundaries i j) (K.iCycles_toBoundaries i j)
  have := K.epi_toBoundaries hij
  let σ : B₀.Splitting := ShortComplex.Splitting.ofExactOfSection B₀
    (ShortComplex.exact_of_g_is_cokernel B₀ (K.toBoundariesIsCokernel hij))
    (Projective.factorThru (𝟙 _) (K.toBoundaries i j)) (Projective.factorThru_comp _ _)
    inferInstance
  let scyc : kernel (F.map (kernel.ι (K.homologyπ j))) ⟶
      ((F.mapHomologicalComplex c).obj K).cycles i :=
    ((F.mapHomologicalComplex c).obj K).liftCycles (kernel.ι _ ≫ F.map σ.s) j (c.next_eq' hij) (by
      have hsg : σ.s ≫ K.toBoundaries i j = 𝟙 _ := σ.s_g
      rw [Functor.mapHomologicalComplex_obj_d, Category.assoc, ← F.map_comp, ← K.toCycles_i,
        ← K.toBoundaries_ι_assoc, ← Category.assoc σ.s, hsg, Category.id_comp, F.map_comp,
        ← Category.assoc, kernel.condition, zero_comp])
  refine
    { r := K.mapHomologyRetractionOf F σ.r σ.f_r
      s := scyc ≫ ((F.mapHomologicalComplex c).obj K).homologyπ i
      f_r := K.mapHomologyComparison_mapHomologyRetractionOf F σ.r σ.f_r
      s_g := ?_
      id := ?_ }
  · have hsg : σ.s ≫ K.toBoundaries i j = 𝟙 _ := σ.s_g
    dsimp only [universalCoefficientKernelShortComplex]
    rw [← cancel_mono (kernel.ι (F.map (kernel.ι (K.homologyπ j)))), Category.id_comp,
      Category.assoc, Category.assoc, homologyπ_homologyToKernelBoundaries_ι,
      liftCycles_i_assoc, Category.assoc, ← F.map_comp, hsg, F.map_id, Category.comp_id]
  · have hid : σ.r ≫ K.iCycles i + K.toBoundaries i j ≫ σ.s = 𝟙 (K.X i) := σ.id
    dsimp only [universalCoefficientKernelShortComplex]
    rw [← cancel_epi (((F.mapHomologicalComplex c).obj K).homologyπ i), Category.comp_id,
      Preadditive.comp_add, homologyπ_mapHomologyRetractionOf_assoc, F.map_comp, Category.assoc,
      map_homologyπ_mapHomologyComparison, homologyπ_homologyToKernelBoundaries_assoc,
      ← Category.assoc, ← Category.assoc, ← Category.assoc, ← Preadditive.add_comp]
    suffices h : ((F.mapHomologicalComplex c).obj K).iCycles i ≫ F.map σ.r ≫
        K.mapCyclesComparison F i + K.cyclesToKernelBoundaries F i j ≫ scyc =
        𝟙 (((F.mapHomologicalComplex c).obj K).cycles i) by
      rw [Category.assoc, h, Category.id_comp]
    rw [← cancel_mono (((F.mapHomologicalComplex c).obj K).iCycles i), Category.id_comp,
      Preadditive.add_comp, Category.assoc, Category.assoc, mapCyclesComparison_iCycles,
      Category.assoc, liftCycles_i, cyclesToKernelBoundaries_ι_assoc, ← F.map_comp, ← F.map_comp,
      ← Preadditive.comp_add, ← F.map_add, hid, F.map_id]
    exact Category.comp_id _

section Connecting

variable [HasProjectiveResolutions C]

/-- **The connecting morphism `Hᵢ(F(K)) ⟶ (L₁F)(Hⱼ(K))`** of the universal coefficient sequence for
`hij : c.Rel i j`, induced on cycles of `F(K)` by `F.map (K.toBoundaries i j)` and the kernel
identification of `L₁F(Hⱼ(K))` from `0 ⟶ Bⱼ ⟶ Zⱼ ⟶ Hⱼ(K) ⟶ 0`. -/
def homologyToLeftDerivedOne (K : HomologicalComplex C c) (F : C ⥤ D) [F.Additive]
    {i j : ι} (_ : c.Rel i j) [Projective (kernel (K.homologyπ j))] [Projective (K.cycles j)]
    [IsSplitMono (K.iCycles j)] :
    ((F.mapHomologicalComplex c).obj K).homology i ⟶ (F.leftDerived 1).obj (K.homology j) :=
  K.homologyToKernelBoundaries F i j ≫
    ((K.boundariesShortComplex_shortExact j).leftDerivedOneIsoKernel F).inv

/-- `homologyToLeftDerivedOne` followed by the kernel embedding into `F(Bⱼ)` sends the class of a
cycle of `F(K)` to its image under `F.map (K.toBoundaries i j)`. -/
@[reassoc (attr := simp)]
lemma homologyπ_homologyToLeftDerivedOne_leftDerivedOneIsoKernel_hom_ι
    (K : HomologicalComplex C c) (F : C ⥤ D) [F.Additive] {i j : ι} (hij : c.Rel i j)
    [Projective (kernel (K.homologyπ j))] [Projective (K.cycles j)] [IsSplitMono (K.iCycles j)] :
    ((F.mapHomologicalComplex c).obj K).homologyπ i ≫ K.homologyToLeftDerivedOne F hij ≫
      ((K.boundariesShortComplex_shortExact j).leftDerivedOneIsoKernel F).hom ≫
        kernel.ι (F.map (kernel.ι (K.homologyπ j))) =
      ((F.mapHomologicalComplex c).obj K).iCycles i ≫ F.map (K.toBoundaries i j) := by
  simp [homologyToLeftDerivedOne]

/-- `mapHomologyComparison` and `homologyToLeftDerivedOne` compose to zero. -/
@[reassoc (attr := simp)]
lemma mapHomologyComparison_homologyToLeftDerivedOne (K : HomologicalComplex C c) (F : C ⥤ D)
    [F.Additive] [PreservesColimitsOfShape WalkingParallelPair F] {i j : ι} (hij : c.Rel i j)
    [Projective (kernel (K.homologyπ j))] [Projective (K.cycles j)] [IsSplitMono (K.iCycles j)] :
    K.mapHomologyComparison F i ≫ K.homologyToLeftDerivedOne F hij = 0 := by
  refine K.map_homologyπ_ext F i ?_
  rw [comp_zero,
    ← cancel_mono (((K.boundariesShortComplex_shortExact j).leftDerivedOneIsoKernel F).hom),
    ← cancel_mono (kernel.ι (F.map (kernel.ι (K.homologyπ j)))), zero_comp, zero_comp]
  simp only [Category.assoc]
  rw [map_homologyπ_mapHomologyComparison_assoc,
    homologyπ_homologyToLeftDerivedOne_leftDerivedOneIsoKernel_hom_ι,
    mapCyclesComparison_iCycles_assoc, ← F.map_comp, K.iCycles_toBoundaries, F.map_zero]

/-- `homologyToLeftDerivedOne` is natural in chain maps `φ : K ⟶ L`. -/
@[reassoc]
lemma homologyToLeftDerivedOne_naturality {K L : HomologicalComplex C c} (φ : K ⟶ L) (F : C ⥤ D)
    [F.Additive] {i j : ι} (hij : c.Rel i j)
    [Projective (kernel (K.homologyπ j))] [Projective (K.cycles j)] [IsSplitMono (K.iCycles j)]
    [Projective (kernel (L.homologyπ j))] [Projective (L.cycles j)] [IsSplitMono (L.iCycles j)] :
    homologyMap ((F.mapHomologicalComplex c).map φ) i ≫ L.homologyToLeftDerivedOne F hij =
      K.homologyToLeftDerivedOne F hij ≫ (F.leftDerived 1).map (homologyMap φ j) := by
  let b : kernel (K.homologyπ j) ⟶ kernel (L.homologyπ j) :=
    kernel.map (K.homologyπ j) (L.homologyπ j) (cyclesMap φ j) (homologyMap φ j)
      (homologyπ_naturality φ j)
  let ψ : K.boundariesShortComplex j ⟶ L.boundariesShortComplex j :=
    { τ₁ := b
      τ₂ := cyclesMap φ j
      τ₃ := homologyMap φ j
      comm₁₂ := kernel.lift_ι _ _ _
      comm₂₃ := (homologyπ_naturality φ j).symm }
  rw [← cancel_mono (((L.boundariesShortComplex_shortExact j).leftDerivedOneIsoKernel F).hom),
    ← cancel_mono (kernel.ι (F.map (kernel.ι (L.homologyπ j)))),
    ← cancel_epi (((F.mapHomologicalComplex c).obj K).homologyπ i)]
  have hnat := ShortComplex.ShortExact.leftDerived_map_comp_leftDerivedOneIsoKernel_hom
    (hS := K.boundariesShortComplex_shortExact j) F (L.boundariesShortComplex_shortExact j) ψ
  dsimp only [boundariesShortComplex, ψ] at hnat
  rw [Category.assoc, Category.assoc, Category.assoc, Category.assoc, reassoc_of% hnat,
    kernel.lift_ι, homologyπ_homologyToLeftDerivedOne_leftDerivedOneIsoKernel_hom_ι_assoc,
    homologyπ_naturality_assoc, homologyπ_homologyToLeftDerivedOne_leftDerivedOneIsoKernel_hom_ι,
    cyclesMap_i_assoc, Functor.mapHomologicalComplex_map_f, ← F.map_comp, ← F.map_comp]
  congr 2
  rw [← cancel_mono (kernel.ι (L.homologyπ j)), ← cancel_mono (L.iCycles j)]
  dsimp only [b]
  simp only [Category.assoc, kernel.lift_ι, toBoundaries_ι_assoc, cyclesMap_i, toCycles_i,
    toCycles_i_assoc]
  exact φ.comm i j

/-- `homologyToLeftDerivedOne` is natural in natural transformations `α : F ⟶ G`. -/
@[reassoc]
lemma homologyToLeftDerivedOne_naturality_functor (K : HomologicalComplex C c) {F G : C ⥤ D}
    [F.Additive] [G.Additive] {i j : ι} (hij : c.Rel i j)
    [Projective (kernel (K.homologyπ j))] [Projective (K.cycles j)] [IsSplitMono (K.iCycles j)]
    (α : F ⟶ G) :
    homologyMap ((NatTrans.mapHomologicalComplex α c).app K) i ≫ K.homologyToLeftDerivedOne G hij =
      K.homologyToLeftDerivedOne F hij ≫ (NatTrans.leftDerived α 1).app (K.homology j) := by
  rw [← cancel_mono (((K.boundariesShortComplex_shortExact j).leftDerivedOneIsoKernel G).hom),
    ← cancel_mono (kernel.ι (G.map (kernel.ι (K.homologyπ j)))),
    ← cancel_epi (((F.mapHomologicalComplex c).obj K).homologyπ i)]
  have hnat := ShortComplex.ShortExact.leftDerived_app_comp_leftDerivedOneIsoKernel_hom F
    (K.boundariesShortComplex_shortExact j) α
  dsimp only [boundariesShortComplex] at hnat
  rw [Category.assoc, Category.assoc, Category.assoc, Category.assoc, reassoc_of% hnat,
    kernel.lift_ι, homologyπ_homologyToLeftDerivedOne_leftDerivedOneIsoKernel_hom_ι_assoc,
    homologyπ_naturality_assoc, homologyπ_homologyToLeftDerivedOne_leftDerivedOneIsoKernel_hom_ι,
    cyclesMap_i_assoc, NatTrans.mapHomologicalComplex_app_f, α.naturality]

/-- **The universal coefficient short complex**
`F(Hᵢ(K)) ⟶ Hᵢ(F(K)) ⟶ (L₁F)(Hⱼ(K))` for a right-exact additive functor `F : C ⥤ D` and
`hij : c.Rel i j`. -/
@[expose, simps]
def universalCoefficientShortComplex (K : HomologicalComplex C c) (F : C ⥤ D) [F.Additive]
    [PreservesColimitsOfShape WalkingParallelPair F] {i j : ι} (hij : c.Rel i j)
    [Projective (kernel (K.homologyπ j))] [Projective (K.cycles j)] [IsSplitMono (K.iCycles j)] :
    ShortComplex D :=
  ShortComplex.mk (K.mapHomologyComparison F i) (K.homologyToLeftDerivedOne F hij)
    (K.mapHomologyComparison_homologyToLeftDerivedOne F hij)

/-- Splitting `0 ⟶ Zᵢ(K) ⟶ Kᵢ ⟶ Bⱼ(K) ⟶ 0` produces a `ShortComplex.Splitting` of the universal
coefficient short complex `0 ⟶ F(Hᵢ(K)) ⟶ Hᵢ(F(K)) ⟶ (L₁F)(Hⱼ(K)) ⟶ 0`. -/
def universalCoefficientSplitting (K : HomologicalComplex C c) (F : C ⥤ D) [F.Additive]
    [PreservesColimitsOfShape WalkingParallelPair F] {i j : ι} (hij : c.Rel i j)
    [Projective (kernel (K.homologyπ j))] [Projective (K.cycles j)] [IsSplitMono (K.iCycles j)] :
    (K.universalCoefficientShortComplex F hij).Splitting :=
  ShortComplex.Splitting.ofIso (K.universalCoefficientKernelSplitting F hij)
    (ShortComplex.isoMk (Iso.refl _) (Iso.refl _)
      ((K.boundariesShortComplex_shortExact j).leftDerivedOneIsoKernel F).symm
      (by
        dsimp [universalCoefficientShortComplex, universalCoefficientKernelShortComplex]
        rw [Category.id_comp, Category.comp_id])
      (by
        dsimp [universalCoefficientShortComplex, universalCoefficientKernelShortComplex,
          homologyToLeftDerivedOne]
        rw [Category.id_comp]))

/-- **The universal coefficient theorem for a right-exact additive functor.** The sequence
`0 ⟶ F(Hᵢ(K)) ⟶ Hᵢ(F(K)) ⟶ (L₁F)(Hⱼ(K)) ⟶ 0` is short exact. -/
theorem shortExact_universalCoefficientShortComplex (K : HomologicalComplex C c) (F : C ⥤ D)
    [F.Additive] [PreservesColimitsOfShape WalkingParallelPair F] {i j : ι} (hij : c.Rel i j)
    [Projective (kernel (K.homologyπ j))] [Projective (K.cycles j)] [IsSplitMono (K.iCycles j)] :
    (K.universalCoefficientShortComplex F hij).ShortExact :=
  (K.universalCoefficientSplitting F hij).shortExact

/-- `F(K)` has homology isomorphic to `F(Hᵢ(K)) ⊞ (L₁F)(Hⱼ(K))` in degree `i`. -/
def mapHomologyIsoBiprod (K : HomologicalComplex C c) (F : C ⥤ D) [F.Additive]
    [PreservesColimitsOfShape WalkingParallelPair F] {i j : ι} (hij : c.Rel i j)
    [Projective (kernel (K.homologyπ j))] [Projective (K.cycles j)] [IsSplitMono (K.iCycles j)] :
    ((F.mapHomologicalComplex c).obj K).homology i ≅
      F.obj (K.homology i) ⊞ (F.leftDerived 1).obj (K.homology j) :=
  (K.universalCoefficientSplitting F hij).isoBinaryBiproduct

/-- When `Hⱼ(K)` is projective, `(L₁F)(Hⱼ(K))` vanishes and `mapHomologyComparison` in degree `i`
is an isomorphism. -/
theorem isIso_mapHomologyComparison_of_projective_homology (K : HomologicalComplex C c) (F : C ⥤ D)
    [F.Additive] [PreservesColimitsOfShape WalkingParallelPair F] {i j : ι} (hij : c.Rel i j)
    [Projective (kernel (K.homologyπ j))] [Projective (K.cycles j)] [IsSplitMono (K.iCycles j)]
    [Projective (K.homology j)] :
    IsIso (K.mapHomologyComparison F i) := by
  have hS := K.shortExact_universalCoefficientShortComplex F hij
  have h0 : IsZero ((F.leftDerived 1).obj (K.homology j)) :=
    Functor.isZero_leftDerived_obj_projective_succ F 0 (K.homology j)
  have hg : (K.universalCoefficientShortComplex F hij).g = 0 := h0.eq_of_tgt _ _
  have : Mono (K.universalCoefficientShortComplex F hij).f := hS.mono_f
  have : Epi (K.universalCoefficientShortComplex F hij).f := hS.exact.epi_f_iff.2 hg
  exact (isIso_of_mono_of_epi (K.universalCoefficientShortComplex F hij).f :
    IsIso (K.mapHomologyComparison F i))

end Connecting

end RightExactFunctor

/-! ### Balanced `Tor` universal coefficient sequence over modules -/

section TensorProduct

universe u

variable {R : Type u} [CommRing R] [∀ X : ModuleCat.{u} R, HasProjectiveDimensionLE X 1]
  {ι : Type*} {c : ComplexShape ι}

/-- Auxiliary wrapper identifying `((tensorRight M).leftDerived 1).obj X` with
`((Tor (ModuleCat R) 1).obj X).obj M` via `ModuleCat.tor'OneIsoTorOne` without unfolding `Tor'`. -/
private def leftDerivedTensorRightIsoTor (X M : ModuleCat.{u} R) :
    ((tensorRight M).leftDerived 1).obj X ≅ ((Tor (ModuleCat.{u} R) 1).obj X).obj M :=
  ((ModuleCat.tor'OneIsoTorOne R).app X).app M

@[reassoc]
private lemma leftDerivedTensorRightIsoTor_hom_naturality_left {X Y : ModuleCat.{u} R} (f : X ⟶ Y)
    (M : ModuleCat.{u} R) :
    ((tensorRight M).leftDerived 1).map f ≫ (leftDerivedTensorRightIsoTor Y M).hom =
      (leftDerivedTensorRightIsoTor X M).hom ≫ ((Tor (ModuleCat.{u} R) 1).map f).app M :=
  NatTrans.congr_app ((ModuleCat.tor'OneIsoTorOne R).hom.naturality f) M

@[reassoc]
private lemma leftDerivedTensorRightIsoTor_hom_naturality_right (X : ModuleCat.{u} R)
    {M N : ModuleCat.{u} R} (g : M ⟶ N) :
    (NatTrans.leftDerived ((tensoringRight _).map g) 1).app X ≫
        (leftDerivedTensorRightIsoTor X N).hom =
      (leftDerivedTensorRightIsoTor X M).hom ≫ ((Tor (ModuleCat.{u} R) 1).obj X).map g :=
  ((ModuleCat.tor'OneIsoTorOne R).hom.app X).naturality g

/-- **The connecting morphism `Hᵢ(K ⊗ M) ⟶ Tor₁^R(Hⱼ(K), M)`**, balanced into `CategoryTheory.Tor`
via `ModuleCat.tor'OneIsoTorOne`. -/
def homologyToTorOne (K : HomologicalComplex (ModuleCat.{u} R) c) (M : ModuleCat.{u} R)
    {i j : ι} (hij : c.Rel i j) [Projective (kernel (K.homologyπ j))] [Projective (K.cycles j)]
    [IsSplitMono (K.iCycles j)] :
    (((tensorRight M).mapHomologicalComplex c).obj K).homology i ⟶
      ((Tor (ModuleCat.{u} R) 1).obj (K.homology j)).obj M :=
  K.homologyToLeftDerivedOne (tensorRight M) hij ≫
    (leftDerivedTensorRightIsoTor (K.homology j) M).hom

/-- `homologyToTorOne` is natural in chain maps `φ : K ⟶ L`. -/
@[reassoc]
lemma homologyToTorOne_naturality {K L : HomologicalComplex (ModuleCat.{u} R) c} (φ : K ⟶ L)
    (M : ModuleCat.{u} R) {i j : ι} (hij : c.Rel i j)
    [Projective (kernel (K.homologyπ j))] [Projective (K.cycles j)] [IsSplitMono (K.iCycles j)]
    [Projective (kernel (L.homologyπ j))] [Projective (L.cycles j)] [IsSplitMono (L.iCycles j)] :
    homologyMap (((tensorRight M).mapHomologicalComplex c).map φ) i ≫ L.homologyToTorOne M hij =
      K.homologyToTorOne M hij ≫ (((Tor (ModuleCat.{u} R) 1).map (homologyMap φ j)).app M) := by
  rw [homologyToTorOne, homologyToTorOne,
    homologyToLeftDerivedOne_naturality_assoc φ (tensorRight M) hij,
    leftDerivedTensorRightIsoTor_hom_naturality_left, Category.assoc]

/-- `homologyToTorOne` is natural in coefficient module morphisms `g : M ⟶ N`. -/
@[reassoc]
lemma homologyToTorOne_naturality_right (K : HomologicalComplex (ModuleCat.{u} R) c)
    {M N : ModuleCat.{u} R} (g : M ⟶ N) {i j : ι} (hij : c.Rel i j)
    [Projective (kernel (K.homologyπ j))] [Projective (K.cycles j)] [IsSplitMono (K.iCycles j)] :
    homologyMap ((NatTrans.mapHomologicalComplex ((tensoringRight _).map g) c).app K) i ≫
        K.homologyToTorOne N hij =
      K.homologyToTorOne M hij ≫ ((Tor (ModuleCat.{u} R) 1).obj (K.homology j)).map g := by
  rw [homologyToTorOne, homologyToTorOne,
    homologyToLeftDerivedOne_naturality_functor_assoc K hij ((tensoringRight _).map g),
    leftDerivedTensorRightIsoTor_hom_naturality_right, Category.assoc]

/-- **The balanced `Tor` universal coefficient short complex**
`Hᵢ(K) ⊗[R] M ⟶ Hᵢ(K ⊗[R] M) ⟶ Tor₁^R(Hⱼ(K), M)`. -/
@[expose, simps]
def torUniversalCoefficientShortComplex (K : HomologicalComplex (ModuleCat.{u} R) c)
    (M : ModuleCat.{u} R) {i j : ι} (hij : c.Rel i j)
    [Projective (kernel (K.homologyπ j))] [Projective (K.cycles j)] [IsSplitMono (K.iCycles j)] :
    ShortComplex (ModuleCat.{u} R) :=
  ShortComplex.mk (K.mapHomologyComparison (tensorRight M) i) (K.homologyToTorOne M hij)
    (by simp [homologyToTorOne])

/-- `R`-linear splitting of `torUniversalCoefficientShortComplex`. -/
def torUniversalCoefficientSplitting (K : HomologicalComplex (ModuleCat.{u} R) c)
    (M : ModuleCat.{u} R) {i j : ι} (hij : c.Rel i j)
    [Projective (kernel (K.homologyπ j))] [Projective (K.cycles j)] [IsSplitMono (K.iCycles j)] :
    (K.torUniversalCoefficientShortComplex M hij).Splitting :=
  ShortComplex.Splitting.ofIso (K.universalCoefficientSplitting (tensorRight M) hij)
    (ShortComplex.isoMk (Iso.refl _) (Iso.refl _) (leftDerivedTensorRightIsoTor (K.homology j) M)
      (by
        dsimp [torUniversalCoefficientShortComplex, universalCoefficientShortComplex]
        rw [Category.id_comp, Category.comp_id])
      (by
        dsimp [torUniversalCoefficientShortComplex, universalCoefficientShortComplex,
          homologyToTorOne]
        rw [Category.id_comp]))

/-- **The universal coefficient theorem for tensor products of modules.** The sequence
`0 ⟶ Hᵢ(K) ⊗[R] M ⟶ Hᵢ(K ⊗[R] M) ⟶ Tor₁^R(Hⱼ(K), M) ⟶ 0` is short exact. -/
theorem shortExact_torUniversalCoefficientShortComplex (K : HomologicalComplex (ModuleCat.{u} R) c)
    (M : ModuleCat.{u} R) {i j : ι} (hij : c.Rel i j)
    [Projective (kernel (K.homologyπ j))] [Projective (K.cycles j)] [IsSplitMono (K.iCycles j)] :
    (K.torUniversalCoefficientShortComplex M hij).ShortExact :=
  (K.torUniversalCoefficientSplitting M hij).shortExact

end TensorProduct

end HomologicalComplex

/-! ### Coefficient ring action on `Tor` and `S`-linear universal coefficient sequence -/

namespace CategoryTheory

universe u

section LiftModuleCat

variable {R S : Type u} [CommRing R] [CommRing S]

/-- Any additive functor `G : ModuleCat.{u} S ⥤ ModuleCat.{u} R` lifts to `ModuleCat.{u} S` by
letting `s : S` act on `G.obj N` through `G.map (s • 𝟙 N)`. -/
private def moduleActionRingHom (G : ModuleCat.{u} S ⥤ ModuleCat.{u} R) [G.Additive]
    (N : ModuleCat.{u} S) : S →+* AddMonoid.End (G.obj N) where
  toFun s := (G.map (s • 𝟙 N)).hom.toAddMonoidHom
  map_one' := by
    ext x
    rw [one_smul, G.map_id]
    rfl
  map_mul' s₁ s₂ := by
    ext x
    have hmul : (s₁ * s₂) • 𝟙 N = (s₂ • 𝟙 N) ≫ (s₁ • 𝟙 N) := by
      rw [Linear.smul_comp, Linear.comp_smul, Category.id_comp, mul_comm s₁ s₂, mul_smul]
    rw [hmul, G.map_comp]
    rfl
  map_zero' := by
    ext x
    rw [zero_smul, G.map_zero]
    rfl
  map_add' s₁ s₂ := by
    ext x
    rw [add_smul, G.map_add]
    rfl

/-- Lift an additive functor `G : ModuleCat.{u} S ⥤ ModuleCat.{u} R` to `ModuleCat.{u} S` via the
functorial `S`-action on its input. -/
def Functor.liftModuleCat (G : ModuleCat.{u} S ⥤ ModuleCat.{u} R) [G.Additive] :
    ModuleCat.{u} S ⥤ ModuleCat.{u} S where
  obj N :=
    @ModuleCat.of S _ (G.obj N) inferInstance (Module.compHom (G.obj N) (moduleActionRingHom G N))
  map {N₁ N₂} g :=
    letI : Module S (G.obj N₁) := Module.compHom (G.obj N₁) (moduleActionRingHom G N₁)
    letI : Module S (G.obj N₂) := Module.compHom (G.obj N₂) (moduleActionRingHom G N₂)
    ModuleCat.ofHom
      { toAddHom := (G.map g).hom.toAddHom
        map_smul' s x := by
          have hcomm : (s • 𝟙 N₁) ≫ g = g ≫ (s • 𝟙 N₂) := by
            rw [Linear.smul_comp, Linear.comp_smul, Category.id_comp, Category.comp_id]
          exact ConcreteCategory.congr_hom ((G.map_comp _ _).symm.trans
            ((congrArg G.map hcomm).trans (G.map_comp _ _))) x }
  map_id N := by
    ext x
    exact congrArg (fun h ↦ h.hom (x : G.obj N)) (G.map_id N)
  map_comp {N₁ N₂ N₃} g₁ g₂ := by
    ext x
    exact congrArg (fun h ↦ h.hom (x : G.obj N₁)) (G.map_comp g₁ g₂)

/-- Every natural transformation `α : G₁ ⟶ G₂` between additive functors
`ModuleCat S ⥤ ModuleCat R` automatically intertwines the induced `S`-actions, lifting to
`G₁.liftModuleCat ⟶ G₂.liftModuleCat`. -/
def NatTrans.liftModuleCat {G₁ G₂ : ModuleCat.{u} S ⥤ ModuleCat.{u} R} [G₁.Additive] [G₂.Additive]
    (α : G₁ ⟶ G₂) : G₁.liftModuleCat ⟶ G₂.liftModuleCat where
  app N :=
    letI : Module S (G₁.obj N) := Module.compHom (G₁.obj N) (moduleActionRingHom G₁ N)
    letI : Module S (G₂.obj N) := Module.compHom (G₂.obj N) (moduleActionRingHom G₂ N)
    ModuleCat.ofHom
      { toAddHom := (α.app N).hom.toAddHom
        map_smul' s x := ConcreteCategory.congr_hom (α.naturality (s • 𝟙 N)) x }
  naturality {N₁ N₂} g := by
    ext x
    dsimp [Functor.liftModuleCat]
    exact congrArg (fun h ↦ h.hom (x : G₁.obj N₁)) (α.naturality g)

/-- Lift an `R`-linear isomorphism `(restrictScalars f).obj M ≅ G.obj N` intertwining the `S`-action
to an `S`-linear isomorphism `M ≅ G.liftModuleCat.obj N` in `ModuleCat S`. -/
private def Functor.liftModuleCatIsoOfRestrictScalars
    {G : ModuleCat.{u} S ⥤ ModuleCat.{u} R} [G.Additive] (f : R →+* S) {M N : ModuleCat.{u} S}
    (e : (ModuleCat.restrictScalars f).obj M ≅ G.obj N)
    (he : ∀ s : S,
      (ModuleCat.restrictScalars f).map (s • 𝟙 M) ≫ e.hom = e.hom ≫ G.map (s • 𝟙 N)) :
    M ≅ G.liftModuleCat.obj N := by
  letI : Module S (G.obj N) := Module.compHom (G.obj N) (moduleActionRingHom G N)
  refine
    { hom := ModuleCat.ofHom
        { toAddHom := e.hom.hom.toAddHom
          map_smul' s x := ConcreteCategory.congr_hom (he s) x }
      inv := ModuleCat.ofHom
        { toAddHom := e.inv.hom.toAddHom
          map_smul' s x := by
            have h' : e.inv ≫ (ModuleCat.restrictScalars f).map (s • 𝟙 M) =
                G.map (s • 𝟙 N) ≫ e.inv := by
              rw [← cancel_mono e.hom, Category.assoc, Category.assoc, he s, Iso.inv_hom_id_assoc,
                Iso.inv_hom_id, Category.comp_id]
            exact (ConcreteCategory.congr_hom h' x).symm }
      hom_inv_id := ?_
      inv_hom_id := ?_ }
  · ext x
    exact congrArg (fun h ↦ h.hom x) e.hom_inv_id
  · ext x
    exact congrArg (fun h ↦ h.hom (x : G.obj N)) e.inv_hom_id

@[simp]
private lemma Functor.liftModuleCatIsoOfRestrictScalars_hom_apply
    {G : ModuleCat.{u} S ⥤ ModuleCat.{u} R} [G.Additive] (f : R →+* S) {M N : ModuleCat.{u} S}
    (e : (ModuleCat.restrictScalars f).obj M ≅ G.obj N)
    (he : ∀ s : S,
      (ModuleCat.restrictScalars f).map (s • 𝟙 M) ≫ e.hom = e.hom ≫ G.map (s • 𝟙 N))
    (x : M) :
    ((Functor.liftModuleCatIsoOfRestrictScalars f e he).hom x : G.obj N) = e.hom x :=
  rfl

end LiftModuleCat

end CategoryTheory

namespace ModuleCat

open CategoryTheory Limits MonoidalCategory
open scoped TensorProduct

universe u

section CoefficientAction

variable {R S : Type u} [CommRing R] [CommRing S]

/-- **`Torₙ^R(X, N)` as an `S`-module** for an `S`-module `N` via `f : R →+* S`, where `s : S` acts
by functoriality of `Tor` in the second (coefficient) variable. -/
def torModuleCat (f : R →+* S) (n : ℕ) : ModuleCat.{u} R ⥤ ModuleCat.{u} S ⥤ ModuleCat.{u} S where
  obj X := (restrictScalars f ⋙ (Tor (ModuleCat.{u} R) n).obj X).liftModuleCat
  map g := NatTrans.liftModuleCat
    (Functor.whiskerLeft (restrictScalars f) ((Tor (ModuleCat.{u} R) n).map g))
  map_id X := by
    ext N x
    dsimp [Functor.liftModuleCat, NatTrans.liftModuleCat]
    exact congrArg (fun h ↦ (h.app ((restrictScalars f).obj N)).hom
      (x : ((Tor (ModuleCat.{u} R) n).obj X).obj ((restrictScalars f).obj N)))
      ((Tor (ModuleCat.{u} R) n).map_id X)
  map_comp {X Y Z} g₁ g₂ := by
    ext N x
    dsimp [Functor.liftModuleCat, NatTrans.liftModuleCat]
    exact congrArg (fun h ↦ (h.app ((restrictScalars f).obj N)).hom
      (x : ((Tor (ModuleCat.{u} R) n).obj X).obj ((restrictScalars f).obj N)))
      ((Tor (ModuleCat.{u} R) n).map_comp g₁ g₂)

/-- **`Torₙ^R(X, S)` as an `S`-module** for `f : R →+* S`, obtained by evaluating `torModuleCat` at
the coefficient ring `S` itself. -/
def torExtendScalars (f : R →+* S) (n : ℕ) : ModuleCat.{u} R ⥤ ModuleCat.{u} S :=
  (torModuleCat f n).flip.obj (of S S)

/-- `extendScalars f ⋙ restrictScalars f` is naturally isomorphic to `tensorRight S` via
`TensorProduct.comm`, sending `s ⊗ₜ[R, f] x ↦ x ⊗ₜ[R] s`. -/
private def extendScalarsRestrictIsoTensorRight (f : R →+* S) :
    extendScalars.{u, u, u} f ⋙ restrictScalars.{u} f ≅
      tensorRight ((restrictScalars f).obj (of S S)) :=
  NatIso.ofComponents
    (fun X ↦ (TensorProduct.comm R ((restrictScalars f).obj (of S S)) X).toModuleIso)
    fun _ ↦ by
      apply hom_ext
      apply TensorProduct.ext'
      intros
      rfl

@[reassoc]
private lemma smul_extendScalarsRestrictIsoTensorRight (f : R →+* S) (s : S)
    (X : ModuleCat.{u} R) :
    (restrictScalars f).map (s • 𝟙 ((extendScalars f).obj X)) ≫
        (extendScalarsRestrictIsoTensorRight f).hom.app X =
      (extendScalarsRestrictIsoTensorRight f).hom.app X ≫
        (X ◁ (restrictScalars f).map (s • 𝟙 (of S S))) := by
  apply hom_ext
  apply TensorProduct.ext'
  intros
  rfl

private lemma exists_hom_of_projective_X₂' {P P' : ShortComplex (ModuleCat.{u} R)}
    [Projective P.X₂] (hP' : P'.ShortExact) (g : P.X₃ ⟶ P'.X₃) :
    ∃ φ : P ⟶ P', φ.τ₃ = g := by
  have := hP'.epi_g
  let τ₂ : P.X₂ ⟶ P'.X₂ := Projective.factorThru (P.g ≫ g) P'.g
  have hτ₂ : τ₂ ≫ P'.g = P.g ≫ g := Projective.factorThru_comp _ _
  obtain ⟨τ₁, hτ₁⟩ := KernelFork.IsLimit.lift' hP'.fIsKernel (P.f ≫ τ₂)
    (by rw [Category.assoc, hτ₂, P.zero_assoc, zero_comp])
  exact ⟨{ τ₁ := τ₁, τ₂ := τ₂, τ₃ := g, comm₁₂ := hτ₁, comm₂₃ := hτ₂ }, rfl⟩

/-- On a length-one projective presentation `P : 0 ⟶ P₁ ⟶ P₀ ⟶ X ⟶ 0`, the underlying `R`-linear
identification `L₁(extendScalars f)(X) ≅ Tor₁^R(X, S)` via `kernel (P.f ▷ S)`. -/
private def extendScalarsLeftDerivedOneIsoTorPresentationR (f : R →+* S)
    {P : ShortComplex (ModuleCat.{u} R)} (hP : P.ShortExact) [Projective P.X₁] [Projective P.X₂] :
    (restrictScalars f).obj (((extendScalars f).leftDerived 1).obj P.X₃) ≅
      ((Tor (ModuleCat.{u} R) 1).obj P.X₃).obj ((restrictScalars f).obj (of S S)) :=
  have : Module.Flat R P.X₂ := Module.Flat.of_projective
  let S₀ := (restrictScalars f).obj (of S S)
  (restrictScalars f).mapIso (hP.leftDerivedOneIsoKernel (extendScalars f)) ≪≫
    PreservesKernel.iso (restrictScalars f) ((extendScalars f).map P.f) ≪≫
    kernel.mapIso ((extendScalars f ⋙ restrictScalars f).map P.f) (P.f ▷ S₀)
      ((extendScalarsRestrictIsoTensorRight f).app P.X₁)
      ((extendScalarsRestrictIsoTensorRight f).app P.X₂)
      ((extendScalarsRestrictIsoTensorRight f).hom.naturality P.f) ≪≫
    (hP.torOneIsoKernelRight S₀).symm

@[reassoc]
private lemma extendScalarsLeftDerivedOneIsoTorPresentationR_hom_ι (f : R →+* S)
    {P : ShortComplex (ModuleCat.{u} R)} (hP : P.ShortExact) [Projective P.X₁] [Projective P.X₂] :
    have : Module.Flat R P.X₂ := Module.Flat.of_projective
    (extendScalarsLeftDerivedOneIsoTorPresentationR f hP).hom ≫
      (hP.torOneIsoKernelRight ((restrictScalars f).obj (of S S))).hom ≫
        kernel.ι (P.f ▷ (restrictScalars f).obj (of S S)) =
      (restrictScalars f).map
        ((hP.leftDerivedOneIsoKernel (extendScalars f)).hom ≫
          kernel.ι ((extendScalars f).map P.f)) ≫
        (extendScalarsRestrictIsoTensorRight f).hom.app P.X₁ := by
  simp [extendScalarsLeftDerivedOneIsoTorPresentationR, PreservesKernel.iso_hom]

private lemma extendScalarsLeftDerivedOneIsoTorPresentationR_smul (f : R →+* S)
    {P : ShortComplex (ModuleCat.{u} R)} (hP : P.ShortExact) [Projective P.X₁] [Projective P.X₂]
    (s : S) :
    (restrictScalars f).map (s • 𝟙 (((extendScalars f).leftDerived 1).obj P.X₃)) ≫
        (extendScalarsLeftDerivedOneIsoTorPresentationR f hP).hom =
      (extendScalarsLeftDerivedOneIsoTorPresentationR f hP).hom ≫
        ((Tor (ModuleCat.{u} R) 1).obj P.X₃).map ((restrictScalars f).map (s • 𝟙 (of S S))) := by
  have : Module.Flat R P.X₂ := Module.Flat.of_projective
  let S₀ := (restrictScalars f).obj (of S S)
  rw [← cancel_mono (hP.torOneIsoKernelRight S₀).hom, ← cancel_mono (kernel.ι (P.f ▷ S₀))]
  simp only [Category.assoc]
  rw [reassoc_of% (hP.Tor_obj_map_comp_torOneIsoKernelRight_hom
      (g := (restrictScalars f).map (s • 𝟙 (of S S)))),
    kernel.lift_ι, extendScalarsLeftDerivedOneIsoTorPresentationR_hom_ι_assoc,
    extendScalarsLeftDerivedOneIsoTorPresentationR_hom_ι,
    ← (restrictScalars f).map_comp_assoc]
  have hS : (s • 𝟙 (((extendScalars f).leftDerived 1).obj P.X₃)) ≫
      ((hP.leftDerivedOneIsoKernel (extendScalars f)).hom ≫
        kernel.ι ((extendScalars f).map P.f)) =
      ((hP.leftDerivedOneIsoKernel (extendScalars f)).hom ≫
        kernel.ι ((extendScalars f).map P.f)) ≫ (s • 𝟙 ((extendScalars f).obj P.X₁)) := by
    rw [Linear.smul_comp, Linear.comp_smul, Category.id_comp, Category.comp_id]
  rw [hS, (restrictScalars f).map_comp_assoc, smul_extendScalarsRestrictIsoTensorRight]

private lemma extendScalarsLeftDerivedOneIsoTorPresentationR_naturality (f : R →+* S)
    {P P' : ShortComplex (ModuleCat.{u} R)} (hP : P.ShortExact) (hP' : P'.ShortExact)
    [Projective P.X₁] [Projective P.X₂] [Projective P'.X₁] [Projective P'.X₂]
    (g : P.X₃ ⟶ P'.X₃) :
    (restrictScalars f).map (((extendScalars f).leftDerived 1).map g) ≫
        (extendScalarsLeftDerivedOneIsoTorPresentationR f hP').hom =
      (extendScalarsLeftDerivedOneIsoTorPresentationR f hP).hom ≫
        (((Tor (ModuleCat.{u} R) 1).map g).app ((restrictScalars f).obj (of S S))) := by
  have : Module.Flat R P.X₂ := Module.Flat.of_projective
  have : Module.Flat R P'.X₂ := Module.Flat.of_projective
  let S₀ := (restrictScalars f).obj (of S S)
  obtain ⟨φ, rfl⟩ := exists_hom_of_projective_X₂' hP' g
  rw [← cancel_mono (hP'.torOneIsoKernelRight S₀).hom, ← cancel_mono (kernel.ι (P'.f ▷ S₀))]
  simp only [Category.assoc]
  rw [reassoc_of% (ShortComplex.ShortExact.Tor_map_app_comp_torOneIsoKernelRight_hom
      (hS := hP) hP' S₀ φ),
    kernel.lift_ι, extendScalarsLeftDerivedOneIsoTorPresentationR_hom_ι_assoc,
    extendScalarsLeftDerivedOneIsoTorPresentationR_hom_ι,
    ← (restrictScalars f).map_comp_assoc,
    reassoc_of% (ShortComplex.ShortExact.leftDerived_map_comp_leftDerivedOneIsoKernel_hom
      (hS := hP) (extendScalars f) hP' φ),
    kernel.lift_ι]
  simp only [Functor.map_comp, Category.assoc]
  congr 2
  exact (extendScalarsRestrictIsoTensorRight f).hom.naturality φ.τ₁

/-- On any length-one projective presentation `P : 0 ⟶ P₁ ⟶ P₀ ⟶ X ⟶ 0`, `L₁(extendScalars f)(X)`
is `S`-linearly isomorphic to `Tor₁^R(X, S)` equipped with its coefficient `S`-action. -/
def extendScalarsLeftDerivedOneIsoTorPresentation (f : R →+* S)
    {P : ShortComplex (ModuleCat.{u} R)} (hP : P.ShortExact) [Projective P.X₁] [Projective P.X₂] :
    ((extendScalars f).leftDerived 1).obj P.X₃ ≅ (torExtendScalars f 1).obj P.X₃ :=
  Functor.liftModuleCatIsoOfRestrictScalars
    (G := restrictScalars f ⋙ (Tor (ModuleCat.{u} R) 1).obj P.X₃) f
    (extendScalarsLeftDerivedOneIsoTorPresentationR f hP)
    (extendScalarsLeftDerivedOneIsoTorPresentationR_smul f hP)

section ProjectiveDimensionOne

variable [∀ X : ModuleCat.{u} R, HasProjectiveDimensionLE X 1]

private instance projective_kernelShortComplex_X₁' (X : ModuleCat.{u} R) :
    Projective (Projective.kernelShortComplex X).X₁ :=
  projective_of_mono_of_hasProjectiveDimensionLE_one (kernel.ι (Projective.π X))

/-- **Comparison of `L₁(extendScalars f)` and `Tor₁^R(-, S)` in `ModuleCat S`.** Over a ring `R` of
projective dimension at most one, the first left-derived functor of extension of scalars along
`f : R →+* S` is naturally `S`-linearly isomorphic to `Tor₁^R(-, S)` equipped with the `S`-module
structure induced by `S`-multiplication on the second variable. -/
def extendScalarsLeftDerivedOneIsoTor (f : R →+* S) :
    (extendScalars.{u, u, u} f).leftDerived 1 ≅ torExtendScalars f 1 :=
  NatIso.ofComponents
    (fun X ↦ extendScalarsLeftDerivedOneIsoTorPresentation f
      (Projective.kernelShortComplex_shortExact X))
    fun {X Y} g ↦ by
      ext x
      dsimp [extendScalarsLeftDerivedOneIsoTorPresentation,
        Functor.liftModuleCatIsoOfRestrictScalars, torExtendScalars, torModuleCat,
        Functor.liftModuleCat, NatTrans.liftModuleCat]
      exact congrArg (fun h ↦ h.hom x)
        (extendScalarsLeftDerivedOneIsoTorPresentationR_naturality f
          (Projective.kernelShortComplex_shortExact X)
          (Projective.kernelShortComplex_shortExact Y) g)

end ProjectiveDimensionOne

end CoefficientAction

end ModuleCat

namespace HomologicalComplex

section ExtendScalars

open ModuleCat

universe u

variable {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S)
  [∀ X : ModuleCat.{u} R, HasProjectiveDimensionLE X 1]
  {ι : Type*} {c : ComplexShape ι}

/-- **The `S`-linear connecting morphism `Hᵢ(S ⊗[R] K) ⟶ Tor₁^R(Hⱼ(K), S)`** in `ModuleCat S`. -/
def homologyExtendScalarsToTorOne (K : HomologicalComplex (ModuleCat.{u} R) c)
    {i j : ι} (hij : c.Rel i j) [Projective (kernel (K.homologyπ j))] [Projective (K.cycles j)]
    [IsSplitMono (K.iCycles j)] :
    (((extendScalars f).mapHomologicalComplex c).obj K).homology i ⟶
      (torExtendScalars f 1).obj (K.homology j) :=
  K.homologyToLeftDerivedOne (extendScalars f) hij ≫
    (extendScalarsLeftDerivedOneIsoTor f).hom.app (K.homology j)

/-- `homologyExtendScalarsToTorOne` is natural in chain maps `φ : K ⟶ L`. -/
@[reassoc]
lemma homologyExtendScalarsToTorOne_naturality {K L : HomologicalComplex (ModuleCat.{u} R) c}
    (φ : K ⟶ L) {i j : ι} (hij : c.Rel i j)
    [Projective (kernel (K.homologyπ j))] [Projective (K.cycles j)] [IsSplitMono (K.iCycles j)]
    [Projective (kernel (L.homologyπ j))] [Projective (L.cycles j)] [IsSplitMono (L.iCycles j)] :
    homologyMap (((extendScalars f).mapHomologicalComplex c).map φ) i ≫
        L.homologyExtendScalarsToTorOne f hij =
      K.homologyExtendScalarsToTorOne f hij ≫ (torExtendScalars f 1).map (homologyMap φ j) := by
  rw [homologyExtendScalarsToTorOne, homologyExtendScalarsToTorOne,
    homologyToLeftDerivedOne_naturality_assoc φ (extendScalars f) hij,
    (extendScalarsLeftDerivedOneIsoTor f).hom.naturality, Category.assoc]

/-- **The `S`-linear universal coefficient short complex**
`(S ⊗[R] Hᵢ(K)) ⟶ Hᵢ(S ⊗[R] K) ⟶ Tor₁^R(Hⱼ(K), S)` in `ModuleCat S`. -/
@[expose, simps]
def extendScalarsUniversalCoefficientShortComplex (K : HomologicalComplex (ModuleCat.{u} R) c)
    {i j : ι} (hij : c.Rel i j) [Projective (kernel (K.homologyπ j))] [Projective (K.cycles j)]
    [IsSplitMono (K.iCycles j)] :
    ShortComplex (ModuleCat.{u} S) :=
  ShortComplex.mk (K.mapHomologyComparison (extendScalars f) i)
    (K.homologyExtendScalarsToTorOne f hij) (by simp [homologyExtendScalarsToTorOne])

/-- `S`-linear splitting of `extendScalarsUniversalCoefficientShortComplex`. -/
def extendScalarsUniversalCoefficientSplitting (K : HomologicalComplex (ModuleCat.{u} R) c)
    {i j : ι} (hij : c.Rel i j) [Projective (kernel (K.homologyπ j))] [Projective (K.cycles j)]
    [IsSplitMono (K.iCycles j)] :
    (K.extendScalarsUniversalCoefficientShortComplex f hij).Splitting :=
  ShortComplex.Splitting.ofIso (K.universalCoefficientSplitting (extendScalars f) hij)
    (ShortComplex.isoMk (Iso.refl _) (Iso.refl _)
      ((extendScalarsLeftDerivedOneIsoTor f).app (K.homology j))
      (by
        dsimp [extendScalarsUniversalCoefficientShortComplex, universalCoefficientShortComplex]
        rw [Category.id_comp, Category.comp_id])
      (by
        dsimp [extendScalarsUniversalCoefficientShortComplex, universalCoefficientShortComplex,
          homologyExtendScalarsToTorOne]
        rw [Category.id_comp]))

/-- **The `S`-linear universal coefficient theorem for extension of scalars.** The sequence
`0 ⟶ S ⊗[R] Hᵢ(K) ⟶ Hᵢ(S ⊗[R] K) ⟶ Tor₁^R(Hⱼ(K), S) ⟶ 0` in `ModuleCat S` is short exact. -/
theorem shortExact_extendScalarsUniversalCoefficientShortComplex
    (K : HomologicalComplex (ModuleCat.{u} R) c) {i j : ι} (hij : c.Rel i j)
    [Projective (kernel (K.homologyπ j))] [Projective (K.cycles j)] [IsSplitMono (K.iCycles j)] :
    (K.extendScalarsUniversalCoefficientShortComplex f hij).ShortExact :=
  (K.extendScalarsUniversalCoefficientSplitting f hij).shortExact

end ExtendScalars

end HomologicalComplex

/-! ### Non-naturality of the universal coefficient splitting -/

namespace CochainComplex

open HomologicalComplex

private lemma rel_zero_one : (ComplexShape.up ℤ).Rel 0 1 := rfl

private abbrev doubleTwo : CochainComplex (ModuleCat.{0} ℤ) ℤ :=
  double ((2 : ℕ) • 𝟙 (ModuleCat.of ℤ ℤ)) rel_zero_one

private abbrev singleZeroInt : CochainComplex (ModuleCat.{0} ℤ) ℤ :=
  (single (ModuleCat.{0} ℤ) (ComplexShape.up ℤ) 0).obj (ModuleCat.of ℤ ℤ)

private instance free_and_finite_doubleTwo (n : ℤ) :
    Module.Free ℤ (doubleTwo.X n) := by
  by_cases h0 : n = 0
  · subst h0
    exact .of_equiv (doubleXIso₀ ((2 : ℕ) • 𝟙 (ModuleCat.of ℤ ℤ)) rel_zero_one).toLinearEquiv.symm
  · by_cases h1 : n = 1
    · subst h1
      exact .of_equiv
        (doubleXIso₁ ((2 : ℕ) • 𝟙 (ModuleCat.of ℤ ℤ)) rel_zero_one (by decide)).toLinearEquiv.symm
    · have : Subsingleton (doubleTwo.X n) :=
        ModuleCat.subsingleton_of_isZero (R := ℤ) (isZero_double_X _ rel_zero_one n h0 h1)
      infer_instance

private instance finite_doubleTwo (n : ℤ) :
    Module.Finite ℤ (doubleTwo.X n) := by
  by_cases h0 : n = 0
  · subst h0
    exact .equiv (doubleXIso₀ ((2 : ℕ) • 𝟙 (ModuleCat.of ℤ ℤ)) rel_zero_one).toLinearEquiv.symm
  · by_cases h1 : n = 1
    · subst h1
      exact .equiv
        (doubleXIso₁ ((2 : ℕ) • 𝟙 (ModuleCat.of ℤ ℤ)) rel_zero_one (by decide)).toLinearEquiv.symm
    · have : Subsingleton (doubleTwo.X n) :=
        ModuleCat.subsingleton_of_isZero (R := ℤ) (isZero_double_X _ rel_zero_one n h0 h1)
      infer_instance

private instance free_singleZeroInt (n : ℤ) :
    Module.Free ℤ (singleZeroInt.X n) := by
  by_cases h0 : n = 0
  · subst h0
    exact .of_equiv
      (singleObjXSelf (ComplexShape.up ℤ) 0 (ModuleCat.of ℤ ℤ)).toLinearEquiv.symm
  · have : Subsingleton (singleZeroInt.X n) :=
      ModuleCat.subsingleton_of_isZero (R := ℤ)
        (isZero_single_obj_X (.up ℤ) 0 (ModuleCat.of ℤ ℤ) n h0)
    infer_instance

private instance finite_singleZeroInt (n : ℤ) :
    Module.Finite ℤ (singleZeroInt.X n) := by
  by_cases h0 : n = 0
  · subst h0
    exact .equiv (singleObjXSelf (ComplexShape.up ℤ) 0 (ModuleCat.of ℤ ℤ)).toLinearEquiv.symm
  · have : Subsingleton (singleZeroInt.X n) :=
      ModuleCat.subsingleton_of_isZero (R := ℤ)
        (isZero_single_obj_X (.up ℤ) 0 (ModuleCat.of ℤ ℤ) n h0)
    infer_instance

private lemma isZero_homology_zero_doubleTwo : IsZero (doubleTwo.homology 0) := by
  have hmono2 : Mono ((2 : ℕ) • 𝟙 (ModuleCat.of ℤ ℤ)) :=
    (ModuleCat.mono_iff_injective _).2 fun (a : ℤ) (b : ℤ) hxy ↦ by
      -- Multiplication by `2` on `ℤ` is `(2 : ℤ) * a = (2 : ℤ) * b`, hence injective.
      have hxy' : @Eq ℤ ((2 : ℤ) * a) ((2 : ℤ) * b) := by simpa [two_nsmul, two_mul] using hxy
      exact mul_left_cancel₀ (by decide : (2 : ℤ) ≠ 0) hxy'
  have hd : Mono (doubleTwo.d 0 1) := by
    rw [double_d ((2 : ℕ) • 𝟙 (ModuleCat.of ℤ ℤ)) rel_zero_one (by decide)]
    infer_instance
  have hi : doubleTwo.iCycles 0 = 0 := by
    rw [← cancel_mono (doubleTwo.d 0 1), iCycles_d, zero_comp]
  have hZ0 : IsZero (doubleTwo.cycles 0) := by
    rw [IsZero.iff_id_eq_zero, ← cancel_mono (doubleTwo.iCycles 0), Category.id_comp, zero_comp, hi]
  rw [IsZero.iff_id_eq_zero, ← cancel_epi (doubleTwo.homologyπ 0), Category.comp_id,
    hZ0.eq_of_src (doubleTwo.homologyπ 0) 0, zero_comp]

private def doubleTwoToSingleZeroInt : doubleTwo ⟶ singleZeroInt :=
  mkHomFromDouble rel_zero_one (by decide)
    (singleObjXSelf (.up ℤ) 0 (ModuleCat.of ℤ ℤ)).inv 0
    (by
      rw [comp_zero]
      exact (isZero_single_obj_X (.up ℤ) 0 (ModuleCat.of ℤ ℤ) 1 (by decide)).eq_of_tgt _ _)
    (fun _ _ ↦ zero_comp)

private def singleZeroIntModTwoDesc :
    (((tensorRight (ModuleCat.of ℤ (ZMod 2))).mapHomologicalComplex (.up ℤ)).obj
      singleZeroInt).homology 0 ⟶
      ModuleCat.of ℤ ℤ ⊗ ModuleCat.of ℤ (ZMod 2) :=
  let Z := ModuleCat.of ℤ ℤ
  let M := ModuleCat.of ℤ (ZMod 2)
  let PM := ((tensorRight M).mapHomologicalComplex (.up ℤ)).obj singleZeroInt
  descHomologyAux PM (PM.iCycles 0 ≫ ((singleObjXSelf (.up ℤ) 0 Z).hom ▷ M)) (by
    rw [toCycles_i_assoc]
    have hprev : (ComplexShape.up ℤ).prev 0 ≠ 0 := by
      intro hp
      have hrel : ¬ (ComplexShape.up ℤ).Rel (-1) 0 := fun h ↦ by
        have := (ComplexShape.up ℤ).prev_eq' h
        omega
      exact hrel (by simp [ComplexShape.up_Rel])
    have hd0 : singleZeroInt.d ((ComplexShape.up ℤ).prev 0) 0 = 0 :=
      (isZero_single_obj_X (.up ℤ) 0 Z _ hprev).eq_of_src _ _
    -- Unfold `PM.d` as the whiskered differential `singleZeroInt.d (prev 0) 0 ▷ M`.
    change (singleZeroInt.d ((ComplexShape.up ℤ).prev 0) 0 ▷ M) ≫ _ = 0
    rw [hd0, MonoidalPreadditive.zero_whiskerRight, zero_comp])

private lemma homologyMap_doubleTwoToSingleZeroInt_modTwo_ne_zero :
    homologyMap (((tensorRight (ModuleCat.of ℤ (ZMod 2))).mapHomologicalComplex (.up ℤ)).map
      doubleTwoToSingleZeroInt) 0 ≠ 0 := by
  intro hψM
  let Z := ModuleCat.of ℤ ℤ
  let M := ModuleCat.of ℤ (ZMod 2)
  let KM := ((tensorRight M).mapHomologicalComplex (.up ℤ)).obj doubleTwo
  have h2M : ((2 : ℕ) • 𝟙 Z) ▷ M = 0 := by
    have hM2 : (𝟙 M + 𝟙 M : M ⟶ M) = 0 := by
      ext (x : ZMod 2)
      fin_cases x <;> rfl
    rw [two_nsmul, MonoidalPreadditive.add_whiskerRight, id_whiskerRight,
      ← whiskerLeft_id Z M, ← MonoidalPreadditive.whiskerLeft_add, hM2,
      MonoidalPreadditive.whiskerLeft_zero]
  let c₀ : Z ⊗ M ⟶ KM.cycles 0 := KM.liftCycles
    ((doubleXIso₀ ((2 : ℕ) • 𝟙 Z) rel_zero_one).inv ▷ M) 1 (by simp) (by
      -- Whiskering the differential of `doubleTwo` with `ℤ/2ℤ` gives `2 • 𝟙`, hence `0`.
      change ((doubleXIso₀ ((2 : ℕ) • 𝟙 Z) rel_zero_one).inv ▷ M) ≫ (doubleTwo.d 0 1 ▷ M) = 0
      rw [double_d ((2 : ℕ) • 𝟙 Z) rel_zero_one (by decide),
        comp_whiskerRight, comp_whiskerRight, h2M, zero_comp, comp_zero, comp_zero])
  have hid : c₀ ≫ KM.homologyπ 0 ≫
      homologyMap (((tensorRight M).mapHomologicalComplex (.up ℤ)).map doubleTwoToSingleZeroInt) 0
        ≫ singleZeroIntModTwoDesc = 𝟙 (Z ⊗ M) := by
    rw [homologyπ_naturality_assoc, singleZeroIntModTwoDesc, homologyπ_descHomologyAux,
      cyclesMap_i_assoc, liftCycles_i_assoc]
    -- On `0`-cochains, `doubleTwoToSingleZeroInt` is the identity of `ℤ` across the degree-`0`
    -- isomorphisms.
    change ((doubleXIso₀ ((2 : ℕ) • 𝟙 Z) rel_zero_one).inv ▷ M) ≫
      (doubleTwoToSingleZeroInt.f 0 ▷ M) ≫ ((singleObjXSelf (.up ℤ) 0 Z).hom ▷ M) = _
    rw [doubleTwoToSingleZeroInt, mkHomFromDouble_f₀, ← comp_whiskerRight, ← comp_whiskerRight]
    dsimp only [Z]
    simp only [Category.assoc, Iso.inv_hom_id_assoc, Iso.inv_hom_id, id_whiskerRight]
  rw [hψM, zero_comp, comp_zero, comp_zero] at hid
  have h10 : (1 : ZMod 2) = 0 := by
    have htmul := congrArg (TensorProduct.lid ℤ (ZMod 2))
      (ConcreteCategory.congr_hom hid ((1 : ℤ) ⊗ₜ[ℤ] (1 : ZMod 2)))
    simpa using htmul.symm
  exact absurd h10 (by decide)

/-- **Non-naturality of universal coefficient retractions.** Over `ℤ` with `ℤ/2ℤ` coefficients,
there is no family of retractions `H⁰(K ⊗ ℤ/2ℤ) ⟶ H⁰(K) ⊗ ℤ/2ℤ` of `mapHomologyComparison` that
is natural in all chain maps between bounded degreewise finitely generated free cochain
complexes. -/
theorem not_exists_natural_retraction_mapHomologyComparison :
    ¬ ∃ r : ∀ (K : CochainComplex (ModuleCat.{0} ℤ) ℤ)
        [∀ n, Module.Free ℤ (K.X n)] [∀ n, Module.Finite ℤ (K.X n)]
        (_ : CochainComplex.bounded (ModuleCat.{0} ℤ) K),
        (((tensorRight (ModuleCat.of ℤ (ZMod 2))).mapHomologicalComplex (.up ℤ)).obj K).homology 0
          ⟶ K.homology 0 ⊗ ModuleCat.of ℤ (ZMod 2),
      (∀ (K : CochainComplex (ModuleCat.{0} ℤ) ℤ)
          [∀ n, Module.Free ℤ (K.X n)] [∀ n, Module.Finite ℤ (K.X n)]
          (hK : CochainComplex.bounded (ModuleCat.{0} ℤ) K),
        K.mapHomologyComparison (tensorRight (ModuleCat.of ℤ (ZMod 2))) 0 ≫ r K hK = 𝟙 _) ∧
      (∀ {K L : CochainComplex (ModuleCat.{0} ℤ) ℤ}
          [∀ n, Module.Free ℤ (K.X n)] [∀ n, Module.Finite ℤ (K.X n)]
          [∀ n, Module.Free ℤ (L.X n)] [∀ n, Module.Finite ℤ (L.X n)]
          (hK : CochainComplex.bounded (ModuleCat.{0} ℤ) K)
          (hL : CochainComplex.bounded (ModuleCat.{0} ℤ) L) (φ : K ⟶ L),
        homologyMap
            (((tensorRight (ModuleCat.of ℤ (ZMod 2))).mapHomologicalComplex (.up ℤ)).map φ) 0
          ≫ r L hL = r K hK ≫ (homologyMap φ 0 ▷ ModuleCat.of ℤ (ZMod 2))) := by
  rintro ⟨r, hret, hnat⟩
  let M := ModuleCat.of ℤ (ZMod 2)
  have hK : CochainComplex.bounded (ModuleCat.{0} ℤ) doubleTwo :=
    CochainComplex.bounded_double _ rel_zero_one
  have hP : CochainComplex.bounded (ModuleCat.{0} ℤ) singleZeroInt :=
    CochainComplex.bounded_single 0 (ModuleCat.of ℤ ℤ)
  have hP1 : IsZero (singleZeroInt.homology 1) := by
    have hX1 : IsZero (singleZeroInt.X 1) := isZero_single_obj_X (.up ℤ) 0 _ 1 (by decide)
    have hi1 : singleZeroInt.iCycles 1 = 0 := hX1.eq_of_tgt _ _
    have hC1 : IsZero (singleZeroInt.cycles 1) := by
      rw [IsZero.iff_id_eq_zero, ← cancel_mono (singleZeroInt.iCycles 1), Category.id_comp,
        zero_comp, hi1]
    have hπ1 : singleZeroInt.homologyπ 1 = 0 := hC1.eq_of_src _ _
    rw [IsZero.iff_id_eq_zero, ← cancel_epi (singleZeroInt.homologyπ 1), Category.comp_id,
      hπ1, zero_comp]
  have : Projective (singleZeroInt.homology 1) := Projective.of_iso hP1.isoZero.symm inferInstance
  have : IsIso (singleZeroInt.mapHomologyComparison (tensorRight M) 0) :=
    singleZeroInt.isIso_mapHomologyComparison_of_projective_homology (tensorRight M) rel_zero_one
  have hrK : r doubleTwo hK = 0 :=
    ((tensorRight M).map_isZero isZero_homology_zero_doubleTwo).eq_of_tgt _ _
  have hψM_comp :
      homologyMap (((tensorRight M).mapHomologicalComplex (.up ℤ)).map doubleTwoToSingleZeroInt) 0
        ≫ r singleZeroInt hP = 0 := by
    rw [hnat hK hP doubleTwoToSingleZeroInt, hrK, zero_comp]
  have hrP_iso :
      r singleZeroInt hP = inv (singleZeroInt.mapHomologyComparison (tensorRight M) 0) := by
    rw [← cancel_epi (singleZeroInt.mapHomologyComparison (tensorRight M) 0),
      hret singleZeroInt hP, IsIso.hom_inv_id]
  rw [hrP_iso, ← cancel_mono (singleZeroInt.mapHomologyComparison (tensorRight M) 0), zero_comp,
    Category.assoc, IsIso.inv_hom_id, Category.comp_id] at hψM_comp
  exact homologyMap_doubleTwoToSingleZeroInt_modTwo_ne_zero hψM_comp

/-- **Non-naturality of universal coefficient sections.** Over `ℤ` with `ℤ/2ℤ` coefficients,
there is no family of sections `Tor₁^ℤ(H¹(K), ℤ/2ℤ) ⟶ H⁰(K ⊗ ℤ/2ℤ)` of `homologyToTorOne` that is
natural in all chain maps between bounded degreewise finitely generated free cochain
complexes. -/
theorem not_exists_natural_section_homologyToTorOne :
    ¬ ∃ s : ∀ (K : CochainComplex (ModuleCat.{0} ℤ) ℤ)
        [∀ n, Module.Free ℤ (K.X n)] [∀ n, Module.Finite ℤ (K.X n)]
        (_ : CochainComplex.bounded (ModuleCat.{0} ℤ) K),
        ((Tor (ModuleCat.{0} ℤ) 1).obj (K.homology 1)).obj (ModuleCat.of ℤ (ZMod 2)) ⟶
          (((tensorRight (ModuleCat.of ℤ (ZMod 2))).mapHomologicalComplex (.up ℤ)).obj K).homology
            0,
      (∀ (K : CochainComplex (ModuleCat.{0} ℤ) ℤ)
          [∀ n, Module.Free ℤ (K.X n)] [∀ n, Module.Finite ℤ (K.X n)]
          (hK : CochainComplex.bounded (ModuleCat.{0} ℤ) K),
        s K hK ≫ K.homologyToTorOne (ModuleCat.of ℤ (ZMod 2))
          (rfl : (ComplexShape.up ℤ).Rel 0 1) = 𝟙 _) ∧
      (∀ {K L : CochainComplex (ModuleCat.{0} ℤ) ℤ}
          [∀ n, Module.Free ℤ (K.X n)] [∀ n, Module.Finite ℤ (K.X n)]
          [∀ n, Module.Free ℤ (L.X n)] [∀ n, Module.Finite ℤ (L.X n)]
          (hK : CochainComplex.bounded (ModuleCat.{0} ℤ) K)
          (hL : CochainComplex.bounded (ModuleCat.{0} ℤ) L) (φ : K ⟶ L),
        (((Tor (ModuleCat.{0} ℤ) 1).map (homologyMap φ 1)).app (ModuleCat.of ℤ (ZMod 2))) ≫
            s L hL =
          s K hK ≫
            homologyMap
              (((tensorRight (ModuleCat.of ℤ (ZMod 2))).mapHomologicalComplex (.up ℤ)).map φ) 0) :=
  by
  rintro ⟨s, hsec, hnat⟩
  apply not_exists_natural_retraction_mapHomologyComparison
  let M := ModuleCat.of ℤ (ZMod 2)
  let σ (K : CochainComplex (ModuleCat.{0} ℤ) ℤ)
      [∀ n, Module.Free ℤ (K.X n)] [∀ n, Module.Finite ℤ (K.X n)]
      (hK : CochainComplex.bounded (ModuleCat.{0} ℤ) K) :
      (K.torUniversalCoefficientShortComplex M rel_zero_one).Splitting :=
    have hSK := K.shortExact_torUniversalCoefficientShortComplex M rel_zero_one
    ShortComplex.Splitting.ofExactOfSection _ hSK.exact (s K hK) (hsec K hK) hSK.mono_f
  let r' (K : CochainComplex (ModuleCat.{0} ℤ) ℤ)
      [∀ n, Module.Free ℤ (K.X n)] [∀ n, Module.Finite ℤ (K.X n)]
      (hK : CochainComplex.bounded (ModuleCat.{0} ℤ) K) :
      (((tensorRight M).mapHomologicalComplex (.up ℤ)).obj K).homology 0 ⟶ K.homology 0 ⊗ M :=
    (σ K hK).r
  refine ⟨fun K _ _ hK ↦ r' K hK, fun K _ _ hK ↦ (σ K hK).f_r, fun {K L} _ _ _ _ hK hL φ ↦ ?_⟩
  dsimp only
  have hSL := L.shortExact_torUniversalCoefficientShortComplex M rel_zero_one
  have : Mono (L.mapHomologyComparison (tensorRight M) 0) := hSL.mono_f
  have hidL : r' L hL ≫ L.mapHomologyComparison (tensorRight M) 0 +
      L.homologyToTorOne M rel_zero_one ≫ s L hL = 𝟙 _ := (σ L hL).id
  have hidK : r' K hK ≫ K.mapHomologyComparison (tensorRight M) 0 +
      K.homologyToTorOne M rel_zero_one ≫ s K hK = 𝟙 _ := (σ K hK).id
  have hnat₀ : (homologyMap φ 0 ▷ M) ≫ L.mapHomologyComparison (tensorRight M) 0 =
      K.mapHomologyComparison (tensorRight M) 0 ≫
        homologyMap (((tensorRight M).mapHomologicalComplex (.up ℤ)).map φ) 0 :=
    mapHomologyComparison_naturality φ (tensorRight M) 0
  rw [← cancel_mono (L.mapHomologyComparison (tensorRight M) 0), Category.assoc, Category.assoc,
    eq_sub_of_add_eq hidL, Preadditive.comp_sub, Category.comp_id, ← Category.assoc,
    homologyToTorOne_naturality φ M rel_zero_one, Category.assoc, hnat hK hL φ, hnat₀,
    reassoc_of% (eq_sub_of_add_eq hidK), Preadditive.sub_comp, Category.id_comp, Category.assoc]

end CochainComplex
