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
public import TauCeti.AlgebraicTopology.Singular.Cubical.Comparison.Basic

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
relative singular homology (`TopPair.singularCubicalHomologyIso`), naturally in the pair.  Its
inverse is induced by `TopPair.cubicalToSingularRel`, because the natural homotopy between the
composite on simplicial chains and the identity descends to relative chains
(`TopPair.singularToCubicalRelCompHomotopy`).  The
relative homotopy invariance of cubical homology is transported from the simplicial one
(`TopPair.Homotopy.congr_homologyMap_cubicalChainComplexMap`).

## Main definitions

* `TopPair.cubicalChainComplex k P`: the relative normalized cubical chain complex of a pair.
* `TopPair.cubicalChainComplexMap k f`: the chain map induced by a map of pairs.
* `TopPair.cubicalChainOfCube k c`, `TopPair.cubicalCycleOfCube k c hc`: a singular cube as a
  relative chain, and as a relative cycle when it sends the boundary of the cube into the subspace.
* `TopPair.cubicalChainComplexMap_f_cubicalChainOfCube`, `TopPair.cyclesMap_cubicalCycleOfCube`:
  their naturality in maps of pairs.
* `TopPair.singularToCubicalRel k P`, `TopPair.cubicalToSingularRel k P`: the relative comparison
  maps.
* `TopPair.singularCubicalHomologyIso k P n`: relative cubical homology is relative singular
  homology.
* `TopPair.singularToCubicalRelCompHomotopy k P`: the relative comparison maps compose to a map
  homotopic to the identity on relative simplicial chains.

## Main results

* `TopPair.quasiIso_singularToCubicalRel`, `TopPair.quasiIso_cubicalToSingularRel`: the relative
  comparison maps are quasi-isomorphisms.
* `TopPair.Homotopy.congr_homologyMap_cubicalChainComplexMap`: homotopic maps of pairs induce the
  same map on relative cubical homology.

## References

* W. S. Massey, *Singular Homology Theory*, GTM 70, Springer, 1980, Chapter VII.
* S. Eilenberg and N. Steenrod, *Foundations of Algebraic Topology*, Princeton, 1952,
  Chapters I–III.
-/

public section

noncomputable section

open CategoryTheory Limits AlgebraicTopology TauCeti

universe u


namespace TopPair

variable (k : Type u) [Ring k]

/-- The inclusion of a subspace induces a monomorphism of normalized cubical chains. -/
instance mono_normalizedCubicalChainComplex_map (P : TopPair.{u}) :
    Mono ((normalizedCubicalChainComplex k).map P.map) :=
  HomologicalComplex.mono_of_mono_f _ fun n ↦ (ModuleCat.mono_iff_injective _).2
    (NormalizedCubicalChain.map_injective k P.map.hom P.isEmbedding_map.injective n)

/-- The **relative normalized cubical chain complex** of a topological pair `(X, A)`: the
cokernel of the map of normalized cubical chains induced by the inclusion `A → X`. -/
abbrev cubicalChainComplex (P : TopPair.{u}) : ChainComplex (ModuleCat.{u} k) ℕ :=
  cokernel ((normalizedCubicalChainComplex k).map P.map)

/-- The chains of the subspace vanish degreewise in the relative normalized cubical chains of a
pair. -/
@[reassoc (attr := simp)]
theorem cubicalChainComplex_condition_f (P : TopPair.{u}) (n : ℕ) :
    ((normalizedCubicalChainComplex k).map P.map).f n ≫
      (cokernel.π ((normalizedCubicalChainComplex k).map P.map)).f n = 0 := by
  simp [← HomologicalComplex.comp_f]

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

@[simp]
theorem cubicalChainComplexMap_id (P : TopPair.{u}) :
    cubicalChainComplexMap k (𝟙 P) = 𝟙 (P.cubicalChainComplex k) :=
  coequalizer.hom_ext (by simp)

@[simp]
theorem cubicalChainComplexMap_comp {P P' P'' : TopPair.{u}} (f : P ⟶ P') (g : P' ⟶ P'') :
    cubicalChainComplexMap k (f ≫ g) = cubicalChainComplexMap k f ≫ cubicalChainComplexMap k g :=
  coequalizer.hom_ext (by simp)

/-! ### Singular cubes as relative chains -/

/-- A singular cube of the ambient space of `P`, as a relative normalized cubical chain of `P`. -/
def cubicalChainOfCube {P : TopPair.{u}} {m : ℕ} (c : SingularCube P.fst m) :
    (P.cubicalChainComplex k).X m :=
  (cokernel.π ((normalizedCubicalChainComplex k).map P.map)).f m
    ((normalizedCubicalChainComplexXEquiv P.fst m).symm (NormalizedCubicalChain.ofCube P.fst k c))

theorem cubicalChainOfCube_def {P : TopPair.{u}} {m : ℕ} (c : SingularCube P.fst m) :
    cubicalChainOfCube k c =
      (cokernel.π ((normalizedCubicalChainComplex k).map P.map)).f m
        ((normalizedCubicalChainComplexXEquiv P.fst m).symm
          (NormalizedCubicalChain.ofCube P.fst k c)) :=
  (rfl)

/-- The chain map induced by a map of pairs `f` sends the relative chain of a cube `c` to that of
`f ∘ c`. -/
@[simp]
theorem cubicalChainComplexMap_f_cubicalChainOfCube {P P' : TopPair.{u}} (f : P ⟶ P') {m : ℕ}
    (c : SingularCube P.fst m) :
    (cubicalChainComplexMap k f).f m (cubicalChainOfCube k c) =
      cubicalChainOfCube k ((Hom.fst f).hom.comp c) := by
  rw [cubicalChainOfCube_def, cubicalChainOfCube_def, ← ModuleCat.comp_apply,
    ← HomologicalComplex.comp_f, π_cubicalChainComplexMap, HomologicalComplex.comp_f,
    ModuleCat.comp_apply]
  simp [NormalizedCubicalChain.map_ofCube]

/-- A singular cube sending the boundary of the cube into the subspace is a relative cycle. -/
theorem d_cubicalChainOfCube {P : TopPair.{u}} {m : ℕ} {c : SingularCube P.fst (m + 1)}
    (hc : Set.MapsTo c (Cube.boundary (Fin (m + 1))) (Set.range P.map)) :
    (P.cubicalChainComplex k).d (m + 1) m (cubicalChainOfCube k c) = 0 := by
  -- The boundary of `c` is a chain of the subspace, which vanishes in the relative chains.
  obtain ⟨a, ha⟩ :
      NormalizedCubicalChain.boundary P.fst k m (NormalizedCubicalChain.ofCube P.fst k c) ∈
        LinearMap.range (NormalizedCubicalChain.map k P.map.hom m) := by
    rw [NormalizedCubicalChain.boundary_ofCube]
    refine Submodule.sum_mem _ fun i _ ↦ Submodule.smul_mem _ _ (Submodule.sub_mem _ ?_ ?_) <;>
      refine NormalizedCubicalChain.ofCube_mem_range_map k P.isEmbedding_map.isInducing ?_ <;>
      rintro _ ⟨y, rfl⟩ <;>
      rw [SingularCube.face_apply] <;>
      exact hc ⟨i, by simp⟩
  have hd : ((normalizedCubicalChainComplex k).obj P.fst).d (m + 1) m
      ((normalizedCubicalChainComplexXEquiv P.fst (m + 1)).symm
        (NormalizedCubicalChain.ofCube P.fst k c)) =
        ((normalizedCubicalChainComplex k).map P.map).f m
          ((normalizedCubicalChainComplexXEquiv P.snd m).symm a) :=
    (normalizedCubicalChainComplex_obj_d_apply P.fst m _).trans
      (ha.symm.trans (normalizedCubicalChainComplex_map_f_apply P.map m a).symm)
  rw [cubicalChainOfCube, HomologicalComplex.Hom.comm_apply, hd]
  exact congr(ModuleCat.Hom.hom $(cubicalChainComplex_condition_f k P m) _)

/-- A singular cube sending the boundary of the cube into the subspace, as a relative cycle of the
normalized cubical chains of `P`. -/
def cubicalCycleOfCube {P : TopPair.{u}} {m : ℕ} (c : SingularCube P.fst (m + 1))
    (hc : Set.MapsTo c (Cube.boundary (Fin (m + 1))) (Set.range P.map)) :
    (P.cubicalChainComplex k).cycles (m + 1) :=
  HomologicalComplex.moduleCatCyclesMk _ (cubicalChainOfCube k c) m (by simp)
    (d_cubicalChainOfCube k hc)

@[simp]
theorem iCycles_cubicalCycleOfCube {P : TopPair.{u}} {m : ℕ} (c : SingularCube P.fst (m + 1))
    (hc : Set.MapsTo c (Cube.boundary (Fin (m + 1))) (Set.range P.map)) :
    (P.cubicalChainComplex k).iCycles (m + 1) (cubicalCycleOfCube k c hc) =
      cubicalChainOfCube k c :=
  HomologicalComplex.iCycles_moduleCatCyclesMk ..

/-- The map on cycles induced by a map of pairs `f` sends the relative cycle of a cube `c` to that
of `f ∘ c`. -/
theorem cyclesMap_cubicalCycleOfCube {P P' : TopPair.{u}} (f : P ⟶ P') {m : ℕ}
    (c : SingularCube P.fst (m + 1))
    (hc : Set.MapsTo c (Cube.boundary (Fin (m + 1))) (Set.range P.map))
    (hfc : Set.MapsTo ((Hom.fst f).hom.comp c) (Cube.boundary (Fin (m + 1))) (Set.range P'.map)) :
    HomologicalComplex.cyclesMap (cubicalChainComplexMap k f) (m + 1) (cubicalCycleOfCube k c hc) =
      cubicalCycleOfCube k ((Hom.fst f).hom.comp c) hfc := by
  apply (P'.cubicalChainComplex k).moduleCat_iCycles_injective
  rw [← ModuleCat.comp_apply, HomologicalComplex.cyclesMap_i, ModuleCat.comp_apply]
  simp

/-! ### The relative comparison maps -/

/-- The quotient map from the simplicial singular chains of the ambient space to the relative
singular chains, with its source written as `(singularChains k).obj P.fst`. -/
def singularRelπ (P : TopPair.{u}) :
    (singularChains k).obj P.fst ⟶ P.singularChainComplex (ModuleCat.of k k) :=
  P.singularChainComplexπ _

instance (P : TopPair.{u}) : Epi (singularRelπ k P) :=
  epi_of_isColimit_cofork (P.isColimitCokernelCoforkSingularChainComplex _)

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
      (cubicalToSingular k).app P.fst ≫ singularRelπ k P :=
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

@[simp]
theorem singularToCubicalShortComplex_τ₁ (P : TopPair.{u}) :
    (singularToCubicalShortComplex k P).τ₁ = (singularToCubical k).app P.snd :=
  (rfl)

@[simp]
theorem singularToCubicalShortComplex_τ₂ (P : TopPair.{u}) :
    (singularToCubicalShortComplex k P).τ₂ = (singularToCubical k).app P.fst :=
  (rfl)

@[simp]
theorem singularToCubicalShortComplex_τ₃ (P : TopPair.{u}) :
    (singularToCubicalShortComplex k P).τ₃ = singularToCubicalRel k P :=
  (rfl)

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

/-- The relative comparison maps compose, on relative simplicial chains, to a map chain
homotopic to the identity: the natural homotopy `singularToCubicalCompHomotopy` descends to the
quotient by the chains of the subspace. -/
def singularToCubicalRelCompHomotopy (P : TopPair.{u}) :
    _root_.Homotopy (singularToCubicalRel k P ≫ cubicalToSingularRel k P) (𝟙 _) :=
  _root_.Homotopy.descCokernel (singularToCubicalCompHomotopy k P.fst)
    ((singularChains k).map P.map)
    (singularRelπ k P) (singularRelπ k P)
    (fun n ↦ (toSSetPair.obj P).chainComplex_condition_f (ModuleCat.of k k) n)
    (fun n ↦ (toSSetPair.obj P).isColimitCokernelCoforkChainComplexX (ModuleCat.of k k) n)
    (fun i j ↦ by
      have h : (singularChains k).map P.map ≫ singularRelπ k P = 0 :=
        P.chainComplexMap_comp_singularChainComplexπ _
      rw [← Category.assoc, singularToCubicalCompHomotopy_hom_naturality, Category.assoc,
        ← HomologicalComplex.comp_f, h, HomologicalComplex.zero_f, comp_zero])
    (by
      rw [singularRelπ_singularToCubicalRel_assoc, π_cubicalToSingularRel, Category.assoc])
    (by simp)

/-- The quotient equation for the homotopy operator on relative simplicial chains. -/
@[reassoc (attr := simp)]
theorem singularRelπ_singularToCubicalRelCompHomotopy_hom (P : TopPair.{u}) (i j : ℕ) :
    (singularRelπ k P).f i ≫ (singularToCubicalRelCompHomotopy k P).hom i j =
      (singularToCubicalCompHomotopy k P.fst).hom i j ≫ (singularRelπ k P).f j := by
  unfold singularToCubicalRelCompHomotopy
  apply _root_.Homotopy.π_descCokernel_hom

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

@[simp]
theorem singularCubicalHomologyIso_hom (P : TopPair.{u}) (n : ℕ) :
    (singularCubicalHomologyIso k P n).hom =
      HomologicalComplex.homologyMap (singularToCubicalRel k P) n :=
  (rfl)

@[simp]
theorem singularCubicalHomologyIso_inv (P : TopPair.{u}) (n : ℕ) :
    (singularCubicalHomologyIso k P n).inv =
      HomologicalComplex.homologyMap (cubicalToSingularRel k P) n := by
  refine (IsIso.inv_eq_of_hom_inv_id ?_).trans rfl
  rw [← HomologicalComplex.homologyMap_comp, (singularToCubicalRelCompHomotopy k P).homologyMap_eq,
    HomologicalComplex.homologyMap_id]

/-- The relative comparison isomorphism on homology is natural in the pair. -/
@[reassoc]
theorem singularCubicalHomologyIso_hom_naturality {P P' : TopPair.{u}} (f : P ⟶ P') (n : ℕ) :
    (singularCubicalHomologyIso k P n).hom ≫
        HomologicalComplex.homologyMap (cubicalChainComplexMap k f) n =
      P.singularHomologyMap f (ModuleCat.of k k) n ≫ (singularCubicalHomologyIso k P' n).hom := by
  simp only [singularCubicalHomologyIso, asIso_hom, ← HomologicalComplex.homologyMap_comp,
    singularToCubicalRel_naturality]

/-- The inverse of the relative comparison isomorphism on homology is natural in the pair. -/
@[reassoc]
theorem singularCubicalHomologyIso_inv_naturality {P P' : TopPair.{u}} (f : P ⟶ P') (n : ℕ) :
    HomologicalComplex.homologyMap (cubicalChainComplexMap k f) n ≫
        (singularCubicalHomologyIso k P' n).inv =
      (singularCubicalHomologyIso k P n).inv ≫ P.singularHomologyMap f (ModuleCat.of k k) n := by
  rw [Iso.eq_inv_comp, singularCubicalHomologyIso_hom_naturality_assoc, Iso.hom_inv_id,
    Category.comp_id]

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
