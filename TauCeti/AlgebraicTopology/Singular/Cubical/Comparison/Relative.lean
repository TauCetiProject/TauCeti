/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.HomologySequenceLemmas
public import Mathlib.Algebra.Homology.HomologicalComplexAbelian
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import TauCeti.AlgebraicTopology.Singular.Homotopy.Invariance
public import TauCeti.AlgebraicTopology.Singular.Relative
public import TauCeti.AlgebraicTopology.Singular.Cubical.Comparison.HomotopyInvariance

/-!
# The relative comparison of cubical and simplicial singular chains

For a topological pair `P = (X, A)`, the **relative normalized cubical chain complex**
`P.cubicalChainComplex k` is the cokernel of the map of normalized cubical chains induced by the
inclusion `A → X`.  This inclusion is injective on normalized chains
(`NormalizedCubicalChain.map_injective`), so the sequence `0 ⟶ N(A) ⟶ N(X) ⟶ N(X, A) ⟶ 0` is
short exact (`TopPair.shortExact_cubicalChainComplexShortComplex`).

The comparison maps of `TauCeti.cubicalSingularHomotopyEquiv` are natural, so they carry the
chains of `A` into those of `A` and induce maps of relative chain complexes in both directions
(`TopPair.singularToCubicalRel`, `TopPair.cubicalToSingularRel`).  By the five lemma, applied to
the long exact homology sequences, both are quasi-isomorphisms, so relative cubical homology is
relative singular homology (`TopPair.singularCubicalHomologyIso`), naturally in the pair.  The
relative homotopy invariance of cubical homology is transported from the simplicial one
(`TopPair.Homotopy.congr_homologyMap_cubicalChainComplexMap`).

## Main definitions

* `TopPair.cubicalChainComplex k P`: the relative normalized cubical chain complex of a pair.
* `TopPair.cubicalChainComplexMap k f`: the chain map induced by a map of pairs.
* `TopPair.singularToCubicalRel k P`, `TopPair.cubicalToSingularRel k P`: the relative comparison
  maps.
* `TopPair.singularCubicalHomologyIso k P n`: relative cubical homology is relative singular
  homology.

## Main results

* `TopPair.quasiIso_singularToCubicalRel`, `TopPair.quasiIso_cubicalToSingularRel`: the relative
  comparison maps are quasi-isomorphisms.
* `TopPair.Homotopy.congr_homologyMap_cubicalChainComplexMap`: homotopic maps of pairs induce the
  same map on relative cubical homology.
-/

public section

noncomputable section

open CategoryTheory Limits AlgebraicTopology TauCeti

universe u

namespace TauCeti

section Injective

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] (R : Type*) [Ring R]

theorem CubicalChain.map_eq_mapDomain (f : C(X, Y)) {n : ℕ} (c : CubicalChain X R n) :
    CubicalChain.map R f n c = Finsupp.mapDomain f.comp c := by
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c d hc hd => rw [map_add, hc, hd, Finsupp.mapDomain_add]
  | single c a => rw [CubicalChain.map_single, Finsupp.mapDomain_single]

/-- The push-forward of normalized cubical chains along an injective map is injective. -/
theorem NormalizedCubicalChain.map_injective {f : C(X, Y)} (hf : Function.Injective f)
    (n : ℕ) : Function.Injective (NormalizedCubicalChain.map R f n) := by
  intro x y h
  have h' := congrArg (NormalizedCubicalChain.toCubicalChain Y R n) h
  rw [NormalizedCubicalChain.toCubicalChain_map, NormalizedCubicalChain.toCubicalChain_map,
    CubicalChain.map_eq_mapDomain, CubicalChain.map_eq_mapDomain] at h'
  have hinj : Function.Injective (f.comp : SingularCube X n → SingularCube Y n) :=
    fun c c' hcc' ↦ ContinuousMap.ext fun t ↦ hf (DFunLike.congr_fun hcc' t)
  rw [← NormalizedCubicalChain.mk_toCubicalChain R x,
    ← NormalizedCubicalChain.mk_toCubicalChain R y, Finsupp.mapDomain_injective hinj h']

end Injective

end TauCeti

namespace TopPair

variable (k : Type u) [Ring k]

instance mono_normalizedCubicalChainComplex_map (P : TopPair.{u}) :
    Mono ((normalizedCubicalChainComplex k).map P.map) :=
  HomologicalComplex.mono_of_mono_f _ fun n ↦ (ModuleCat.mono_iff_injective _).2
    (NormalizedCubicalChain.map_injective k P.isEmbedding_map.injective n)

/-- The **relative normalized cubical chain complex** of a topological pair `(X, A)`: the
cokernel of the map of normalized cubical chains induced by the inclusion `A → X`. -/
abbrev cubicalChainComplex (P : TopPair.{u}) : ChainComplex (ModuleCat.{u} k) ℕ :=
  cokernel ((normalizedCubicalChainComplex k).map P.map)

/-- The sequence `N(A) ⟶ N(X) ⟶ N(X, A)` of normalized cubical chain complexes of a pair. -/
abbrev cubicalChainComplexShortComplex (P : TopPair.{u}) :
    ShortComplex (ChainComplex (ModuleCat.{u} k) ℕ) :=
  ShortComplex.mk _ _ (cokernel.condition ((normalizedCubicalChainComplex k).map P.map))

/-- The normalized cubical chain sequence of a pair is short exact. -/
theorem shortExact_cubicalChainComplexShortComplex (P : TopPair.{u}) :
    (P.cubicalChainComplexShortComplex k).ShortExact :=
  ShortComplex.ShortExact.mk' (ShortComplex.exact_of_g_is_cokernel _ (cokernelIsCokernel _))
    (mono_normalizedCubicalChainComplex_map k P) (by dsimp; infer_instance)

/-- The map of relative normalized cubical chains induced by a map of pairs. -/
def cubicalChainComplexMap {P P' : TopPair.{u}} (f : P ⟶ P') :
    P.cubicalChainComplex k ⟶ P'.cubicalChainComplex k :=
  cokernel.map _ _ ((normalizedCubicalChainComplex k).map (Hom.snd f))
    ((normalizedCubicalChainComplex k).map (Hom.fst f)) (by
      rw [← Functor.map_comp, ← Functor.map_comp, Hom.w])

@[reassoc (attr := simp)]
theorem π_cubicalChainComplexMap {P P' : TopPair.{u}} (f : P ⟶ P') :
    cokernel.π _ ≫ cubicalChainComplexMap k f =
      (normalizedCubicalChainComplex k).map (Hom.fst f) ≫ cokernel.π _ := by
  simp [cubicalChainComplexMap]

/-! ### The relative comparison maps -/

/-- The quotient map from the simplicial singular chains of the ambient space to the relative
singular chains, with its source written as `(singularChains k).obj P.fst`. -/
def singularRelπ (P : TopPair.{u}) :
    (singularChains k).obj P.fst ⟶ P.singularChainComplex (ModuleCat.of k k) :=
  P.singularChainComplexπ _

@[reassoc]
theorem singularRelπ_naturality {P P' : TopPair.{u}} (f : P ⟶ P') :
    (singularChains k).map (Hom.fst f) ≫ singularRelπ k P' =
      singularRelπ k P ≫ P.singularChainComplexMap f (ModuleCat.of k k) :=
  singularChainComplexπ_pair_naturality f _

theorem singularRelπ_hom_ext {P : TopPair.{u}} {T : ChainComplex (ModuleCat.{u} k) ℕ}
    {g g' : P.singularChainComplex (ModuleCat.of k k) ⟶ T}
    (h : singularRelπ k P ≫ g = singularRelπ k P ≫ g') : g = g' :=
  Cofork.IsColimit.hom_ext (P.isColimitCokernelCoforkSingularChainComplex _) h

/-- The comparison map from relative simplicial to relative cubical chains, induced by
`singularToCubical`. -/
def singularToCubicalRel (P : TopPair.{u}) :
    P.singularChainComplex (ModuleCat.of k k) ⟶ P.cubicalChainComplex k :=
  (P.isColimitCokernelCoforkSingularChainComplex (ModuleCat.of k k)).desc
    (CokernelCofork.ofπ ((singularToCubical k).app P.fst ≫ cokernel.π _)
      (((singularToCubical k).naturality_assoc P.map _).trans
        ((congrArg (_ ≫ ·) (cokernel.condition _)).trans comp_zero)))

@[reassoc (attr := simp)]
theorem singularRelπ_singularToCubicalRel (P : TopPair.{u}) :
    singularRelπ k P ≫ singularToCubicalRel k P =
      (singularToCubical k).app P.fst ≫ cokernel.π _ :=
  (P.isColimitCokernelCoforkSingularChainComplex (ModuleCat.of k k)).fac _
    WalkingParallelPair.one

/-- The comparison map from relative cubical to relative simplicial chains, induced by
`cubicalToSingular`. -/
def cubicalToSingularRel (P : TopPair.{u}) :
    P.cubicalChainComplex k ⟶ P.singularChainComplex (ModuleCat.of k k) :=
  cokernel.desc _ ((cubicalToSingular k).app P.fst ≫ P.singularChainComplexπ (ModuleCat.of k k))
    (((cubicalToSingular k).naturality_assoc P.map _).trans
      ((congrArg (_ ≫ ·) (P.chainComplexMap_comp_singularChainComplexπ (ModuleCat.of k k))).trans
        comp_zero))

@[reassoc (attr := simp)]
theorem π_cubicalToSingularRel (P : TopPair.{u}) :
    cokernel.π _ ≫ cubicalToSingularRel k P =
      (cubicalToSingular k).app P.fst ≫ P.singularChainComplexπ (ModuleCat.of k k) :=
  cokernel.π_desc _ _ _

/-- The comparison maps as a morphism of short complexes from the simplicial chain sequence of a
pair to the cubical one. -/
def singularToCubicalShortComplex (P : TopPair.{u}) :
    P.singularChainComplexShortComplex (ModuleCat.of k k) ⟶ P.cubicalChainComplexShortComplex k
    where
  τ₁ := (singularToCubical k).app P.snd
  τ₂ := (singularToCubical k).app P.fst
  τ₃ := singularToCubicalRel k P
  comm₁₂ := ((singularToCubical k).naturality P.map).symm
  comm₂₃ := (singularRelπ_singularToCubicalRel k P).symm

/-- The comparison maps as a morphism of short complexes from the cubical chain sequence of a
pair to the simplicial one. -/
def cubicalToSingularShortComplex (P : TopPair.{u}) :
    P.cubicalChainComplexShortComplex k ⟶ P.singularChainComplexShortComplex (ModuleCat.of k k)
    where
  τ₁ := (cubicalToSingular k).app P.snd
  τ₂ := (cubicalToSingular k).app P.fst
  τ₃ := cubicalToSingularRel k P
  comm₁₂ := ((cubicalToSingular k).naturality P.map).symm
  comm₂₃ := (π_cubicalToSingularRel k P).symm

instance (X : TopCat.{u}) : QuasiIso ((singularToCubical k).app X) := by
  rw [← cubicalSingularHomotopyEquiv_hom]
  infer_instance

instance (X : TopCat.{u}) : QuasiIso ((cubicalToSingular k).app X) := by
  rw [← cubicalSingularHomotopyEquiv_inv]
  infer_instance

/-- **The relative comparison map to cubical chains is a quasi-isomorphism.** -/
instance quasiIso_singularToCubicalRel (P : TopPair.{u}) : QuasiIso (singularToCubicalRel k P) :=
  HomologicalComplex.HomologySequence.quasiIso_τ₃ (singularToCubicalShortComplex k P)
    (P.shortExact_singularChainComplexShortComplex _)
    (shortExact_cubicalChainComplexShortComplex k P)
    (inferInstanceAs (QuasiIso ((singularToCubical k).app P.snd)))
    (inferInstanceAs (QuasiIso ((singularToCubical k).app P.fst)))

/-- **The relative comparison map to simplicial chains is a quasi-isomorphism.** -/
instance quasiIso_cubicalToSingularRel (P : TopPair.{u}) : QuasiIso (cubicalToSingularRel k P) :=
  HomologicalComplex.HomologySequence.quasiIso_τ₃ (cubicalToSingularShortComplex k P)
    (shortExact_cubicalChainComplexShortComplex k P)
    (P.shortExact_singularChainComplexShortComplex _)
    (inferInstanceAs (QuasiIso ((cubicalToSingular k).app P.snd)))
    (inferInstanceAs (QuasiIso ((cubicalToSingular k).app P.fst)))

/-- The relative comparison map to cubical chains is natural in the pair. -/
@[reassoc]
theorem singularToCubicalRel_naturality {P P' : TopPair.{u}} (f : P ⟶ P') :
    singularToCubicalRel k P ≫ cubicalChainComplexMap k f =
      P.singularChainComplexMap f (ModuleCat.of k k) ≫ singularToCubicalRel k P' := by
  refine singularRelπ_hom_ext k ?_
  rw [singularRelπ_singularToCubicalRel_assoc, π_cubicalChainComplexMap,
    ← (singularToCubical k).naturality_assoc, ← singularRelπ_singularToCubicalRel,
    singularRelπ_naturality_assoc]

/-- **Relative cubical singular homology is relative singular homology.** -/
def singularCubicalHomologyIso (P : TopPair.{u}) (n : ℕ) :
    P.singularHomology (ModuleCat.of k k) n ≅ (P.cubicalChainComplex k).homology n :=
  asIso (HomologicalComplex.homologyMap (singularToCubicalRel k P) n)

/-- The relative comparison isomorphism on homology is natural in the pair. -/
@[reassoc]
theorem singularCubicalHomologyIso_hom_naturality {P P' : TopPair.{u}} (f : P ⟶ P') (n : ℕ) :
    (singularCubicalHomologyIso k P n).hom ≫
        HomologicalComplex.homologyMap (cubicalChainComplexMap k f) n =
      P.singularHomologyMap f (ModuleCat.of k k) n ≫ (singularCubicalHomologyIso k P' n).hom := by
  simp only [singularCubicalHomologyIso, asIso_hom, ← HomologicalComplex.homologyMap_comp,
    singularToCubicalRel_naturality]

end TopPair

namespace TopPair.Homotopy

variable {k : Type u} [Ring k] {P P' : TopPair.{u}} {f g : P ⟶ P'}

/-- **Homotopic maps of pairs induce the same map on relative cubical homology**, transported
from relative singular homology through the relative comparison. -/
theorem congr_homologyMap_cubicalChainComplexMap (H : TopPair.Homotopy f g) (n : ℕ) :
    HomologicalComplex.homologyMap (cubicalChainComplexMap k f) n =
      HomologicalComplex.homologyMap (cubicalChainComplexMap k g) n := by
  rw [← cancel_epi (singularCubicalHomologyIso k P n).hom,
    singularCubicalHomologyIso_hom_naturality, singularCubicalHomologyIso_hom_naturality,
    H.congr_singularHomologyMap]

end TopPair.Homotopy
