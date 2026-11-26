/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.HomologySequenceLemmas
public import Mathlib.Algebra.Homology.HomologicalComplexAbelian
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import TauCeti.Algebra.Homology.ModuleCat.QuasiIso
public import TauCeti.AlgebraicTopology.Singular.Homotopy.Invariance
public import TauCeti.AlgebraicTopology.Singular.Relative
public import TauCeti.AlgebraicTopology.Singular.Cubical.Comparison.Basic
public import TauCeti.AlgebraicTopology.Singular.Cubical.Relative
import TauCeti.Algebra.Homology.ComplexShape.Basic
import TauCeti.Algebra.Homology.ModuleCat.Cokernel

/-!
# The relative comparison of cubical and simplicial singular chains

For a topological pair `P = (X, A)`, the **relative normalized cubical chain complex**
`P.cubicalChainComplex k` is the cokernel of the map of normalized cubical chains induced by the
inclusion `A → X`.  This inclusion is injective on normalized chains
(`NormalizedCubicalChain.map_injective`), so the sequence `0 ⟶ N(A) ⟶ N(X) ⟶ N(X, A) ⟶ 0` is
short exact (`TopPair.shortExact_cubicalChainComplexShortComplex`). In each degree it splits, since
the push-forward along the inclusion `A → X` has a left inverse
(`NormalizedCubicalChain.exists_comp_map_eq_id`), so the relative chains are projective modules.

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
* `TopPair.IsCubicalRepresentative k c μ`: a normalized cubical chain of the ambient space is a
  relative cycle with relative class `μ`; every class has one
  (`TopPair.exists_isCubicalRepresentative`).
* `TopPair.cubicalChainComplexXDesc k g hg`: a linear map out of the chains of the ambient space,
  vanishing on the chains of the subspace, descended to the relative chains.
* `TopPair.cubicalChainOfCube k c`, `TopPair.cubicalCycleOfCube k c hc`: a singular cube as a
  relative chain, and as a relative cycle when it sends the boundary of the cube into the subspace.
  Linear maps out of the relative chains are determined by their values on these
  (`TopPair.cubicalChainComplexX_linearMap_ext`).
* `TopPair.cubicalChainComplexMap_f_cubicalChainOfCube`, `TopPair.cyclesMap_cubicalCycleOfCube`:
  their naturality in maps of pairs, and `TopPair.d_cubicalChainOfCube_eq_sum`: the relative
  boundary of a cube is the signed sum of its faces.
* `TopPair.cubicalBoundaryChainOfCube k c hc`, `TopPair.cubicalBoundaryCycleOfCube k c hc`: the
  boundary of a cube sending the boundary of the cube into the subspace, as a chain and as a cycle
  of the subspace (`TopPair.map_cubicalBoundaryChainOfCube`).
* `TopPair.singularToCubicalRel k P`, `TopPair.cubicalToSingularRel k P`: the relative comparison
  maps. Under the identification `TopPair.cokernelSingularChainComplexIso` of relative singular
  chains with a cokernel, the latter is the map of cokernels induced by `TauCeti.cubicalToSingular`
  (`TopPair.cokernel_map_cubicalToSingular_comp`).
* `TopPair.singularCubicalHomologyIso k P n`: relative cubical homology is relative singular
  homology.
* `TopPair.singularToCubicalRelCompHomotopy k P`: the relative comparison maps compose to a map
  homotopic to the identity on relative simplicial chains.

## Main results

* The terms of `TopPair.cubicalChainComplex k P` are projective `k`-modules (an instance), and in
  each degree the chains of the subspace split off those of the ambient space
  (`TopPair.isSplitMono_normalizedCubicalChainComplex_map_f`).
* `TopPair.cokernel_π_f_map_eq_zero_of_range_subset`: a chain pushed forward along a map with
  values in the subspace vanishes in the relative chains.
* `TopPair.quasiIso_singularToCubicalRel`, `TopPair.quasiIso_cubicalToSingularRel`: the relative
  comparison maps are quasi-isomorphisms.
* `TopPair.cubicalChainComplexMap_eq_zero_of_fac`: a map of pairs whose ambient map factors
  through the target subspace induces the zero map on relative cubical chains.
* `TopPair.homologyMap_cubicalChainComplexMap_eq`: on relative cubical homology, a map of pairs
  induces its relative singular homology map, conjugated by the comparison isomorphisms.
* `TopPair.Homotopy.congr_homologyMap_cubicalChainComplexMap`: homotopic maps of pairs induce the
  same map on relative cubical homology.
* `TopPair.IsCubicalRepresentative.map`: a map of pairs carries a representative of a relative
  class to a representative of its image.
* `TopPair.exists_isCubicalRepresentative_of_d_mem`, `TopPair.IsCubicalRepresentative.eq_zero_iff`:
  relative cycles represent relative classes, and represent the zero class exactly when they are
  relative boundaries.
* `TopPair.exists_isCubicalRepresentative_of_dim_zero`: every chain of dimension `0` represents a
  relative class.
* `TopPair.exists_isCubicalRepresentative_ofCube`: a cube sending the boundary of the cube into the
  subspace represents a relative class.
* `TopPair.isCubicalRepresentative_d`: a boundary represents the zero class.
* `TopPair.IsCubicalRepresentative.sum`, `TopPair.IsCubicalRepresentative.neg`,
  `TopPair.IsCubicalRepresentative.smul`, `TopPair.IsCubicalRepresentative.zsmul`,
  `TopPair.IsCubicalRepresentative.unique`:
  representatives are linear and determine their class.
* `TopPair.quasiIsoAt_cubicalChainComplexMap_iff`: a map of pairs induces a quasi-isomorphism of
  relative chains in a degree exactly when, on chains of the ambient spaces, every relative cycle
  of the target is the image of a relative cycle up to a boundary and the chains of the subspace,
  and every relative cycle whose image bounds modulo the subspace bounds modulo the subspace.
* `TopPair.exists_boundary_eq_sub_add_map_of_injective`: when `Hₙ(X) → Hₙ(X, A)` is injective
  and `s`, `s'` are relative cycles representing the same class, any cycle `s - s' + a` with `a` a
  chain of `A` is a boundary.

* `TopPair.boundary_ofCube_comp`: compute the boundary of a cube mapped out of a pair, from
  the map on its subspace.

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

/-- In each degree, the inclusion of the normalized cubical chains of the subspace of a pair into
those of the ambient space is a split monomorphism
(`TauCeti.NormalizedCubicalChain.exists_comp_map_eq_id`). -/
instance isSplitMono_normalizedCubicalChainComplex_map_f (P : TopPair.{u}) (n : ℕ) :
    IsSplitMono (((normalizedCubicalChainComplex k).map P.map).f n) := by
  obtain ⟨r, hr⟩ := NormalizedCubicalChain.exists_comp_map_eq_id k P.isEmbedding_map.injective n
  exact .mk' ⟨ModuleCat.ofHom r, ModuleCat.hom_ext hr⟩

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

/-- A chain pushed forward along a map with values in the subspace of a pair vanishes in the
relative normalized cubical chains of the pair. -/
theorem cokernel_π_f_map_eq_zero_of_range_subset (P : TopPair.{u}) {Z : TopCat.{u}}
    (g : Z ⟶ P.fst) (hg : Set.range g ⊆ Set.range P.map) {n : ℕ}
    (b : NormalizedCubicalChain Z k n) :
    ((cokernel.π ((normalizedCubicalChainComplex k).map P.map)).f n).hom
      (NormalizedCubicalChain.map k g.hom n b) = 0 := by
  -- `g` factors through the embedding of the subspace.
  have hg' : g.hom = P.map.hom.comp (P.liftSnd g.hom fun z ↦ hg ⟨z, rfl⟩) := by
    ext z
    exact (TopPair.map_liftSnd _ _ z).symm
  rw [hg', ← NormalizedCubicalChain.map_map]
  exact ConcreteCategory.congr_hom (cubicalChainComplex_condition_f k P n) _

/-- The sequence `N(A) ⟶ N(X) ⟶ N(X, A)` of normalized cubical chain complexes of a pair. -/
abbrev cubicalChainComplexShortComplex (P : TopPair.{u}) :
    ShortComplex (ChainComplex (ModuleCat.{u} k) ℕ) :=
  ShortComplex.mk _ _ (cokernel.condition ((normalizedCubicalChainComplex k).map P.map))

/-- The normalized cubical chain sequence of a pair is short exact. -/
theorem shortExact_cubicalChainComplexShortComplex (P : TopPair.{u}) :
    (P.cubicalChainComplexShortComplex k).ShortExact :=
  ShortComplex.ShortExact.mk' (ShortComplex.exact_of_g_is_cokernel _ (cokernelIsCokernel _))
    (mono_normalizedCubicalChainComplex_map k P) (by dsimp; infer_instance)

/-- In each degree, the normalized cubical chain sequence `0 ⟶ N(A) ⟶ N(X) ⟶ N(X, A) ⟶ 0` of a
pair is short exact. -/
private theorem shortExact_cubicalChainComplexShortComplex_map_eval (P : TopPair.{u}) (n : ℕ) :
    ((P.cubicalChainComplexShortComplex k).map (HomologicalComplex.eval _ _ n)).ShortExact :=
  (HomologicalComplex.shortExact_iff_degreewise_shortExact _).1
    (shortExact_cubicalChainComplexShortComplex k P) n

/-- The terms of the relative normalized cubical chain complex of a pair are projective: the
chains of the subspace split off the chains of the ambient space
(`TauCeti.NormalizedCubicalChain.exists_comp_map_eq_id`), so the relative chains are a direct
summand of the projective chains of the ambient space. -/
instance (P : TopPair.{u}) (n : ℕ) : Module.Projective k ((P.cubicalChainComplex k).X n) := by
  have hS := shortExact_cubicalChainComplexShortComplex_map_eval k P n
  obtain ⟨r, hr⟩ := NormalizedCubicalChain.exists_comp_map_eq_id k P.isEmbedding_map.injective n
  let σ := ShortComplex.Splitting.ofExactOfRetraction _ hS.exact (ModuleCat.ofHom r)
    (ModuleCat.hom_ext hr) hS.epi_g
  exact Module.Projective.of_split (M := ((normalizedCubicalChainComplex k).obj P.fst).X n)
    σ.s.hom ((cokernel.π ((normalizedCubicalChainComplex k).map P.map)).f n).hom
    (congrArg ModuleCat.Hom.hom σ.s_g)

/-- A normalized cubical `n`-chain `c` of the ambient space of a pair `(X, A)` **represents** the
class `μ` of the relative cubical homology `Hₙ(X, A)` when its image in the relative chains is a
relative cycle whose class is `μ`. -/
def IsCubicalRepresentative (P : TopPair.{u}) {n : ℕ} (c : NormalizedCubicalChain P.fst k n)
    (μ : (P.cubicalChainComplex k).homology n) : Prop :=
  ∃ r : (P.cubicalChainComplex k).cycles n,
    ((cokernel.π ((normalizedCubicalChainComplex k).map P.map)).f n).hom c =
        ((P.cubicalChainComplex k).iCycles n).hom r ∧
      ((P.cubicalChainComplex k).homologyπ n).hom r = μ

variable {k} in
theorem isCubicalRepresentative_iff {P : TopPair.{u}} {n : ℕ}
    (c : NormalizedCubicalChain P.fst k n) (μ : (P.cubicalChainComplex k).homology n) :
    P.IsCubicalRepresentative k c μ ↔ ∃ r : (P.cubicalChainComplex k).cycles n,
      ((cokernel.π ((normalizedCubicalChainComplex k).map P.map)).f n).hom c =
          ((P.cubicalChainComplex k).iCycles n).hom r ∧
        ((P.cubicalChainComplex k).homologyπ n).hom r = μ :=
  Iff.rfl

/-- Every class of the relative cubical homology of a pair is represented by a chain of the
ambient space. -/
theorem exists_isCubicalRepresentative (P : TopPair.{u}) {n : ℕ}
    (μ : (P.cubicalChainComplex k).homology n) :
    ∃ c : NormalizedCubicalChain P.fst k n, P.IsCubicalRepresentative k c μ := by
  obtain ⟨r, rfl⟩ := (ModuleCat.epi_iff_surjective _).1
    (inferInstance : Epi ((P.cubicalChainComplex k).homologyπ n)) μ
  obtain ⟨c, hc⟩ := HomologicalComplex.cokernel_π_f_surjective _ n
    (((P.cubicalChainComplex k).iCycles n).hom r)
  exact ⟨c, r, hc, rfl⟩

/-- **The relative class of a cycle is represented by any chain agreeing with it modulo the
subspace.** Let `z` be an `n`-cycle of the ambient space `X` of a pair `(X, A)`, and `c` an
`n`-chain of `X` whose difference with `z` is a chain of `A`. If `c` represents the relative class
`μ ∈ Hₙ(X, A)`, then `μ` is the image of the class of `z` under `Hₙ(X) → Hₙ(X, A)`. -/
theorem homologyMap_homologyπ_eq_of_isCubicalRepresentative (P : TopPair.{u}) {n : ℕ}
    (z : ((normalizedCubicalChainComplex k).obj P.fst).cycles n)
    {c : NormalizedCubicalChain P.fst k n} {μ : (P.cubicalChainComplex k).homology n}
    (hc : P.IsCubicalRepresentative k c μ)
    (hzc : normalizedCubicalChainComplexXEquiv P.fst n
        ((((normalizedCubicalChainComplex k).obj P.fst).iCycles n).hom z) - c ∈
      LinearMap.range (NormalizedCubicalChain.map k P.map.hom n)) :
    (HomologicalComplex.homologyMap (cokernel.π ((normalizedCubicalChainComplex k).map P.map))
      n).hom ((((normalizedCubicalChainComplex k).obj P.fst).homologyπ n).hom z) = μ := by
  obtain ⟨r, hcr, rfl⟩ := hc
  obtain ⟨a, ha⟩ := hzc
  rw [HomologicalComplex.moduleCat_homologyMap_homologyπ]
  congr 1
  -- The images of `z` and `c` in the relative chains differ by the image of a chain of `A`.
  have h₀ : ((cokernel.π ((normalizedCubicalChainComplex k).map P.map)).f n).hom
      ((normalizedCubicalChainComplexXEquiv P.fst n).symm
        (NormalizedCubicalChain.map k P.map.hom n a)) = 0 := by
    rw [normalizedCubicalChainComplexXEquiv_symm_apply, ← normalizedCubicalChainComplex_map_f_apply]
    exact congr(ModuleCat.Hom.hom $(cubicalChainComplex_condition_f k P n) _)
  rw [ha, map_sub, LinearEquiv.symm_apply_apply, map_sub,
    normalizedCubicalChainComplexXEquiv_symm_apply, sub_eq_zero] at h₀
  refine (P.cubicalChainComplex k).moduleCat_iCycles_injective n ?_
  rw [HomologicalComplex.moduleCat_iCycles_cyclesMap_apply, ← hcr]
  exact h₀

/-- **A cycle with vanishing relative class is a boundary when relative classes determine
absolute ones.** Let `s, s'` be normalized cubical `n`-chains of `X` which are relative cycles
representing the same class of `Hₙ(X, A)`, and `a` an `n`-chain of `A` such that `s - s' + a` is
a cycle of `X`. If the map `Hₙ(X) → Hₙ(X, A)` is injective, as it is when `Hₙ(A) = 0`, then
`s - s' + a` is a boundary: its relative class, that of `s - s'`, vanishes. -/
theorem exists_boundary_eq_sub_add_map_of_injective (P : TopPair.{u}) (n : ℕ)
    (s s' : NormalizedCubicalChain P.fst k n) (a : NormalizedCubicalChain P.snd k n)
    (hd : ((normalizedCubicalChainComplex k).obj P.fst).d n (n - 1)
      (s - s' + NormalizedCubicalChain.map k P.map.hom n a) = 0)
    (r r' : (P.cubicalChainComplex k).cycles n)
    (hs : ((cokernel.π ((normalizedCubicalChainComplex k).map P.map)).f n).hom s =
      ((P.cubicalChainComplex k).iCycles n).hom r)
    (hs' : ((cokernel.π ((normalizedCubicalChainComplex k).map P.map)).f n).hom s' =
      ((P.cubicalChainComplex k).iCycles n).hom r')
    (hr : ((P.cubicalChainComplex k).homologyπ n).hom r =
      ((P.cubicalChainComplex k).homologyπ n).hom r')
    (hinj : Function.Injective (HomologicalComplex.homologyMap
      (cokernel.π ((normalizedCubicalChainComplex k).map P.map)) n).hom) :
    ∃ b : NormalizedCubicalChain P.fst k (n + 1),
      NormalizedCubicalChain.boundary P.fst k n b =
        s - s' + NormalizedCubicalChain.map k P.map.hom n a := by
  set K := (normalizedCubicalChainComplex k).obj P.fst
  set π := cokernel.π ((normalizedCubicalChainComplex k).map P.map)
  obtain ⟨w, hw⟩ : ∃ w : K.cycles n, K.iCycles n w =
      (normalizedCubicalChainComplexXEquiv P.fst n).symm
        (s - s' + NormalizedCubicalChain.map k P.map.hom n a) :=
    ⟨_, K.iCycles_moduleCatCyclesMk n _ _ (ChainComplex.next_nat n) hd⟩
  -- The relative class of the cycle `w` is that of `s - s'`, which vanishes.
  have hπw : HomologicalComplex.cyclesMap π n w = r - r' := by
    refine (P.cubicalChainComplex k).moduleCat_iCycles_injective n ?_
    have ha : π.f n (NormalizedCubicalChain.map k P.map.hom n a) = 0 :=
      congrArg (fun f ↦ f.hom a) (cubicalChainComplex_condition_f k P n)
    rw [HomologicalComplex.moduleCat_iCycles_cyclesMap_apply, hw]
    simp only [map_add, map_sub]
    simp only [normalizedCubicalChainComplexXEquiv_symm_apply, ha, add_zero, hs, hs']
  have hw₀ : K.homologyπ n w = 0 := hinj (by
    rw [HomologicalComplex.moduleCat_homologyMap_homologyπ π n w, hπw, map_sub, hr, sub_self,
      map_zero])
  obtain ⟨b, hb⟩ := (K.moduleCat_homologyπ_eq_zero_iff (m := n + 1) (by simp) w).1 hw₀
  refine ⟨normalizedCubicalChainComplexXEquiv P.fst (n + 1) b, ?_⟩
  rw [← normalizedCubicalChainComplexXEquiv_d_apply, normalizedCubicalChainComplexXEquiv_apply,
    ← HomologicalComplex.moduleCat_iCycles_toCycles_apply, hb, hw,
    normalizedCubicalChainComplexXEquiv_symm_apply]

/-- A linear map out of the normalized cubical `n`-chains of the ambient space of a pair which
vanishes on the chains of the subspace, descended to the relative chains
(`TopPair.cubicalChainComplexXDesc_π`). -/
def cubicalChainComplexXDesc {P : TopPair.{u}} {n : ℕ} {M : Type*} [AddCommGroup M] [Module k M]
    (g : NormalizedCubicalChain P.fst k n →ₗ[k] M)
    (hg : g ∘ₗ NormalizedCubicalChain.map k P.map.hom n = 0) :
    (P.cubicalChainComplex k).X n →ₗ[k] M :=
  (LinearMap.ker ((cokernel.π ((normalizedCubicalChainComplex k).map P.map)).f n).hom).liftQ g
      (fun x hx ↦ by
        obtain ⟨y, rfl⟩ := (shortExact_cubicalChainComplexShortComplex_map_eval k P n).exact
          |>.moduleCat_range_eq_ker.ge hx
        exact LinearMap.congr_fun hg y) ∘ₗ
    (LinearMap.quotKerEquivOfSurjective _
      (HomologicalComplex.cokernel_π_f_surjective _ n)).symm.toLinearMap

@[simp]
theorem cubicalChainComplexXDesc_π {P : TopPair.{u}} {n : ℕ} {M : Type*} [AddCommGroup M]
    [Module k M] (g : NormalizedCubicalChain P.fst k n →ₗ[k] M)
    (hg : g ∘ₗ NormalizedCubicalChain.map k P.map.hom n = 0)
    (x : ((normalizedCubicalChainComplex k).obj P.fst).X n) :
    cubicalChainComplexXDesc k g hg
        ((cokernel.π ((normalizedCubicalChainComplex k).map P.map)).f n x) = g x := by
  rw [cubicalChainComplexXDesc, LinearMap.comp_apply, LinearEquiv.coe_coe,
    LinearMap.quotKerEquivOfSurjective_symm_apply]
  exact Submodule.liftQ_apply _ g x

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

/-- Element-wise form of `TopPair.π_cubicalChainComplexMap`: a map of pairs sends the class of a
chain of the ambient space to the class of its push-forward along the map of ambient spaces. -/
@[simp]
theorem π_cubicalChainComplexMap_f_apply {P P' : TopPair.{u}} (f : P ⟶ P') (n : ℕ)
    (x : ((normalizedCubicalChainComplex k).obj P.fst).X n) :
    (cubicalChainComplexMap k f).f n
        ((cokernel.π ((normalizedCubicalChainComplex k).map P.map)).f n x) =
      (cokernel.π ((normalizedCubicalChainComplex k).map P'.map)).f n
        (NormalizedCubicalChain.map k (Hom.fst f).hom n x) :=
  ConcreteCategory.congr_hom (congrArg (fun φ ↦ φ.f n) (π_cubicalChainComplexMap k f)) x

variable {k} in
/-- A map of pairs sends a representative of a relative class to a representative of its image:
the push-forward of the chain along the map of ambient spaces. -/
theorem IsCubicalRepresentative.map {P P' : TopPair.{u}} (f : P ⟶ P') {n : ℕ}
    {c : NormalizedCubicalChain P.fst k n} {μ : (P.cubicalChainComplex k).homology n}
    (h : P.IsCubicalRepresentative k c μ) :
    P'.IsCubicalRepresentative k (NormalizedCubicalChain.map k (Hom.fst f).hom n c)
      (HomologicalComplex.homologyMap (cubicalChainComplexMap k f) n μ) := by
  obtain ⟨r, hc, rfl⟩ := h
  refine ⟨(HomologicalComplex.cyclesMap (cubicalChainComplexMap k f) n).hom r, ?_, ?_⟩
  · refine (π_cubicalChainComplexMap_f_apply k f n c).symm.trans ?_
    rw [hc, ← ModuleCat.comp_apply, ← HomologicalComplex.cyclesMap_i, ModuleCat.comp_apply]
  · rw [← ModuleCat.comp_apply, ← HomologicalComplex.homologyπ_naturality, ModuleCat.comp_apply]

@[simp]
theorem cubicalChainComplexMap_id (P : TopPair.{u}) :
    cubicalChainComplexMap k (𝟙 P) = 𝟙 (P.cubicalChainComplex k) :=
  coequalizer.hom_ext (by simp)

@[simp]
theorem cubicalChainComplexMap_comp {P P' P'' : TopPair.{u}} (f : P ⟶ P') (g : P' ⟶ P'') :
    cubicalChainComplexMap k (f ≫ g) = cubicalChainComplexMap k f ≫ cubicalChainComplexMap k g :=
  coequalizer.hom_ext (by simp)

/-- An isomorphism of pairs induces an isomorphism of relative normalized cubical chains. -/
instance isIso_cubicalChainComplexMap {P P' : TopPair.{u}} (f : P ⟶ P') [IsIso f] :
    IsIso (cubicalChainComplexMap k f) :=
  ⟨cubicalChainComplexMap k (inv f), by
    rw [← cubicalChainComplexMap_comp, IsIso.hom_inv_id, cubicalChainComplexMap_id], by
    rw [← cubicalChainComplexMap_comp, IsIso.inv_hom_id, cubicalChainComplexMap_id]⟩

/-! ### Quasi-isomorphisms on chains of the ambient spaces -/

/-- In each degree, the chains of the subspace of a pair are the chains of the ambient space
supported in it. -/
theorem mem_range_normalizedCubicalChainComplex_map_f_iff (P : TopPair.{u}) {n : ℕ}
    (c : ((normalizedCubicalChainComplex k).obj P.fst).X n) :
    c ∈ LinearMap.range (((normalizedCubicalChainComplex k).map P.map).f n).hom ↔
      normalizedCubicalChainComplexXEquiv P.fst n c ∈
        NormalizedCubicalChain.supportedIn k (Set.range P.map) n := by
  rw [← NormalizedCubicalChain.range_map_eq_supportedIn_range k P.isEmbedding_map.isInducing n]
  -- `normalizedCubicalChainComplexXEquiv` intertwines the two push-forwards along `P.map`.
  constructor
  · rintro ⟨a, rfl⟩
    exact ⟨normalizedCubicalChainComplexXEquiv _ n a,
      (normalizedCubicalChainComplexXEquiv_map_f_apply P.map n a).symm⟩
  · rintro ⟨a, ha⟩
    refine ⟨(normalizedCubicalChainComplexXEquiv _ n).symm a,
      (normalizedCubicalChainComplexXEquiv _ n).injective ?_⟩
    rw [normalizedCubicalChainComplexXEquiv_map_f_apply, LinearEquiv.apply_symm_apply, ha]

/-- **Quasi-isomorphisms of relative cubical chains, on chains of the ambient spaces.** A map of
pairs `f : (X, A) ⟶ (X', A')` induces a quasi-isomorphism of relative normalized cubical chains in
degree `n` exactly when

* every chain `y` of `X'` whose boundary lies in `A'` is, up to the boundary of a chain and a chain
  of `A'`, the image of a chain `x` of `X` whose boundary lies in `A`, and
* every chain `x` of `X` whose boundary lies in `A` and whose image is, up to a chain of `A'`, the
  boundary of a chain of `X'` is, up to a chain of `A`, the boundary of a chain of `X`.

These are surjectivity and injectivity on relative homology, written on representatives
(`HomologicalComplex.moduleCat_quasiIsoAt_iff`). Here `m` is the degree below `n`. -/
theorem quasiIsoAt_cubicalChainComplexMap_iff {P P' : TopPair.{u}} (f : P ⟶ P') {n m : ℕ}
    (hm : (ComplexShape.down ℕ).next n = m) :
    QuasiIsoAt (cubicalChainComplexMap k f) n ↔
      (∀ y : ((normalizedCubicalChainComplex k).obj P'.fst).X n,
        ((normalizedCubicalChainComplex k).obj P'.fst).d n m y ∈
            LinearMap.range (((normalizedCubicalChainComplex k).map P'.map).f m).hom →
          ∃ x : ((normalizedCubicalChainComplex k).obj P.fst).X n,
            ((normalizedCubicalChainComplex k).obj P.fst).d n m x ∈
                LinearMap.range (((normalizedCubicalChainComplex k).map P.map).f m).hom ∧
              ∃ b : ((normalizedCubicalChainComplex k).obj P'.fst).X (n + 1),
                y - ((normalizedCubicalChainComplex k).map (Hom.fst f)).f n x -
                    ((normalizedCubicalChainComplex k).obj P'.fst).d (n + 1) n b ∈
                  LinearMap.range (((normalizedCubicalChainComplex k).map P'.map).f n).hom) ∧
        ∀ x : ((normalizedCubicalChainComplex k).obj P.fst).X n,
          ((normalizedCubicalChainComplex k).obj P.fst).d n m x ∈
              LinearMap.range (((normalizedCubicalChainComplex k).map P.map).f m).hom →
            ∀ b : ((normalizedCubicalChainComplex k).obj P'.fst).X (n + 1),
              ((normalizedCubicalChainComplex k).map (Hom.fst f)).f n x -
                  ((normalizedCubicalChainComplex k).obj P'.fst).d (n + 1) n b ∈
                LinearMap.range (((normalizedCubicalChainComplex k).map P'.map).f n).hom →
              ∃ a : ((normalizedCubicalChainComplex k).obj P.fst).X (n + 1),
                x - ((normalizedCubicalChainComplex k).obj P.fst).d (n + 1) n a ∈
                  LinearMap.range (((normalizedCubicalChainComplex k).map P.map).f n).hom := by
  -- Chains of the subspace are the kernel of the projection, which commutes with `d` and `f`.
  have hπ (i : ℕ) := HomologicalComplex.cokernel_π_f_apply_eq_zero_iff
    ((normalizedCubicalChainComplex k).map P.map) i
  have hπ' (i : ℕ) := HomologicalComplex.cokernel_π_f_apply_eq_zero_iff
    ((normalizedCubicalChainComplex k).map P'.map) i
  have hφ : ∀ (i : ℕ) (c : ((normalizedCubicalChainComplex k).obj P.fst).X i),
      (cubicalChainComplexMap k f).f i
          ((cokernel.π ((normalizedCubicalChainComplex k).map P.map)).f i c) =
        (cokernel.π ((normalizedCubicalChainComplex k).map P'.map)).f i
          (((normalizedCubicalChainComplex k).map (Hom.fst f)).f i c) :=
    π_cubicalChainComplexMap_f_apply k f
  rw [HomologicalComplex.moduleCat_quasiIsoAt_iff _ (ChainComplex.prev ℕ n) hm]
  refine and_congr ⟨fun H y hy ↦ ?_, fun H y' hy' ↦ ?_⟩
    ⟨fun H x hx b hxb ↦ ?_, fun H x' hx' b' hb' ↦ ?_⟩
  · obtain ⟨x', hx', b', hb'⟩ :=
      H ((cokernel.π ((normalizedCubicalChainComplex k).map P'.map)).f n y)
        (by rw [HomologicalComplex.Hom.comm_apply, hπ']; exact hy)
    obtain ⟨x, rfl⟩ := HomologicalComplex.cokernel_π_f_surjective _ n x'
    obtain ⟨b, rfl⟩ := HomologicalComplex.cokernel_π_f_surjective _ (n + 1) b'
    rw [HomologicalComplex.Hom.comm_apply] at hx'
    rw [HomologicalComplex.Hom.comm_apply, hφ] at hb'
    refine ⟨x, (hπ _ _).1 hx', b, (hπ' _ _).1 ?_⟩
    rw [map_sub, map_sub, ← hb', sub_self]
  · obtain ⟨y, rfl⟩ := HomologicalComplex.cokernel_π_f_surjective _ n y'
    rw [HomologicalComplex.Hom.comm_apply, hπ'] at hy'
    obtain ⟨x, hx, b, hb⟩ := H y hy'
    refine ⟨(cokernel.π ((normalizedCubicalChainComplex k).map P.map)).f n x,
      by rw [HomologicalComplex.Hom.comm_apply, hπ]; exact hx,
      (cokernel.π ((normalizedCubicalChainComplex k).map P'.map)).f (n + 1) b, ?_⟩
    rw [← hπ', map_sub, map_sub, sub_eq_zero] at hb
    rw [HomologicalComplex.Hom.comm_apply, ← hb, hφ]
  · rw [← hπ', map_sub, sub_eq_zero] at hxb
    obtain ⟨a', ha'⟩ := H ((cokernel.π ((normalizedCubicalChainComplex k).map P.map)).f n x)
      (by rw [HomologicalComplex.Hom.comm_apply, hπ]; exact hx)
      ((cokernel.π ((normalizedCubicalChainComplex k).map P'.map)).f (n + 1) b)
      (by rw [HomologicalComplex.Hom.comm_apply, ← hxb, hφ])
    obtain ⟨a, rfl⟩ := HomologicalComplex.cokernel_π_f_surjective _ (n + 1) a'
    rw [HomologicalComplex.Hom.comm_apply] at ha'
    exact ⟨a, (hπ _ _).1 (by rw [map_sub, ha', sub_self])⟩
  · obtain ⟨x, rfl⟩ := HomologicalComplex.cokernel_π_f_surjective _ n x'
    obtain ⟨b, rfl⟩ := HomologicalComplex.cokernel_π_f_surjective _ (n + 1) b'
    rw [HomologicalComplex.Hom.comm_apply] at hx'
    rw [HomologicalComplex.Hom.comm_apply, hφ] at hb'
    obtain ⟨a, ha⟩ := H x ((hπ _ _).1 hx') b ((hπ' _ _).1 (by rw [map_sub, hb', sub_self]))
    rw [← hπ, map_sub, sub_eq_zero] at ha
    exact ⟨(cokernel.π ((normalizedCubicalChainComplex k).map P.map)).f (n + 1) a,
      by rw [HomologicalComplex.Hom.comm_apply, ha]⟩

/-! ### Representatives of relative classes -/

section Representative

variable {k} {P : TopPair.{u}} {n : ℕ}

/-- The zero chain represents the zero class. -/
theorem isCubicalRepresentative_zero :
    P.IsCubicalRepresentative k (0 : ((normalizedCubicalChainComplex k).obj P.fst).X n) 0 :=
  ⟨0, (map_zero _).trans (map_zero _).symm, map_zero _⟩

/-- Representatives of relative classes add. -/
theorem IsCubicalRepresentative.add {c c' : ((normalizedCubicalChainComplex k).obj P.fst).X n}
    {μ μ' : (P.cubicalChainComplex k).homology n} (h : P.IsCubicalRepresentative k c μ)
    (h' : P.IsCubicalRepresentative k c' μ') : P.IsCubicalRepresentative k (c + c') (μ + μ') := by
  obtain ⟨r, hr, rfl⟩ := h
  obtain ⟨r', hr', rfl⟩ := h'
  exact ⟨r + r', by rw [map_add, map_add, hr, hr'], map_add _ _ _⟩

/-- Representatives of relative classes subtract. -/
theorem IsCubicalRepresentative.sub {c c' : ((normalizedCubicalChainComplex k).obj P.fst).X n}
    {μ μ' : (P.cubicalChainComplex k).homology n} (h : P.IsCubicalRepresentative k c μ)
    (h' : P.IsCubicalRepresentative k c' μ') : P.IsCubicalRepresentative k (c - c') (μ - μ') := by
  obtain ⟨r, hr, rfl⟩ := h
  obtain ⟨r', hr', rfl⟩ := h'
  exact ⟨r - r', by rw [map_sub, map_sub, hr, hr'], map_sub _ _ _⟩

/-- Representatives of relative classes are compatible with finite sums. -/
theorem IsCubicalRepresentative.sum {ι : Type*} {s : Finset ι}
    {c : ι → ((normalizedCubicalChainComplex k).obj P.fst).X n}
    {μ : ι → (P.cubicalChainComplex k).homology n}
    (h : ∀ i ∈ s, P.IsCubicalRepresentative k (c i) (μ i)) :
    P.IsCubicalRepresentative k (∑ i ∈ s, c i : ((normalizedCubicalChainComplex k).obj P.fst).X n)
      (∑ i ∈ s, μ i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using isCubicalRepresentative_zero
  | insert i s hi ih =>
    rw [Finset.sum_insert hi, Finset.sum_insert hi]
    exact (h i (Finset.mem_insert_self i s)).add (ih fun j hj ↦ h j (Finset.mem_insert_of_mem hj))

/-- Representatives of relative classes negate. -/
theorem IsCubicalRepresentative.neg {c : ((normalizedCubicalChainComplex k).obj P.fst).X n}
    {μ : (P.cubicalChainComplex k).homology n} (h : P.IsCubicalRepresentative k c μ) :
    P.IsCubicalRepresentative k (-c) (-μ) := by
  obtain ⟨r, hr, rfl⟩ := h
  exact ⟨-r, by rw [map_neg, map_neg, hr], map_neg _ _⟩

/-- Representatives of relative classes are compatible with scalar multiplication. -/
theorem IsCubicalRepresentative.smul {c : ((normalizedCubicalChainComplex k).obj P.fst).X n}
    {μ : (P.cubicalChainComplex k).homology n} (h : P.IsCubicalRepresentative k c μ) (r : k) :
    P.IsCubicalRepresentative k (r • c) (r • μ) := by
  obtain ⟨z, hz, rfl⟩ := h
  exact ⟨r • z, by rw [map_smul, map_smul, hz], map_smul _ _ _⟩

/-- Representatives of relative classes are compatible with integer multiples. -/
theorem IsCubicalRepresentative.zsmul {c : ((normalizedCubicalChainComplex k).obj P.fst).X n}
    {μ : (P.cubicalChainComplex k).homology n} (h : P.IsCubicalRepresentative k c μ) (m : ℤ) :
    P.IsCubicalRepresentative k (m • c) (m • μ) := by
  simpa only [Int.cast_smul_eq_zsmul] using h.smul (m : k)

/-- A chain represents at most one relative class. -/
theorem IsCubicalRepresentative.unique {c : ((normalizedCubicalChainComplex k).obj P.fst).X n}
    {μ μ' : (P.cubicalChainComplex k).homology n} (h : P.IsCubicalRepresentative k c μ)
    (h' : P.IsCubicalRepresentative k c μ') : μ = μ' := by
  obtain ⟨r, hr, rfl⟩ := h
  obtain ⟨r', hr', rfl⟩ := h'
  rw [(P.cubicalChainComplex k).moduleCat_iCycles_injective n (hr.symm.trans hr')]

/-- **Relative cycles represent relative classes**: a chain of the ambient space of a pair whose
boundary is a chain of the subspace represents a class of the relative homology. -/
theorem exists_isCubicalRepresentative_of_d_mem
    (c : ((normalizedCubicalChainComplex k).obj P.fst).X n)
    (hc : ((normalizedCubicalChainComplex k).obj P.fst).d n (n - 1) c ∈
      LinearMap.range (((normalizedCubicalChainComplex k).map P.map).f (n - 1)).hom) :
    ∃ μ, P.IsCubicalRepresentative k c μ := by
  have hd : (P.cubicalChainComplex k).d n (n - 1)
      ((cokernel.π ((normalizedCubicalChainComplex k).map P.map)).f n c) = 0 := by
    rw [HomologicalComplex.Hom.comm_apply, HomologicalComplex.cokernel_π_f_apply_eq_zero_iff]
    exact hc
  exact ⟨_, _, ((P.cubicalChainComplex k).iCycles_moduleCatCyclesMk n _ _
    (ChainComplex.next_nat n) hd).symm, rfl⟩

/-- Every chain of dimension `0` of the ambient space of a pair is a relative cycle, so it
represents a relative class. -/
theorem exists_isCubicalRepresentative_of_dim_zero
    (c : ((normalizedCubicalChainComplex k).obj P.fst).X 0) :
    ∃ μ, P.IsCubicalRepresentative k c μ :=
  exists_isCubicalRepresentative_of_d_mem c <| by
    rw [HomologicalComplex.shape _ 0 (0 - 1) (by simp)]
    exact zero_mem _

/-- **A representative of the zero class is a relative boundary**: a chain represents the zero
class of the relative homology of a pair exactly when it is the boundary of a chain of the ambient
space up to a chain of the subspace. -/
theorem IsCubicalRepresentative.eq_zero_iff {c : ((normalizedCubicalChainComplex k).obj P.fst).X n}
    {μ : (P.cubicalChainComplex k).homology n} (h : P.IsCubicalRepresentative k c μ) :
    μ = 0 ↔ ∃ a : ((normalizedCubicalChainComplex k).obj P.fst).X (n + 1),
      c - ((normalizedCubicalChainComplex k).obj P.fst).d (n + 1) n a ∈
        LinearMap.range (((normalizedCubicalChainComplex k).map P.map).f n).hom := by
  obtain ⟨r, hr, rfl⟩ := h
  have hπ (a : ((normalizedCubicalChainComplex k).obj P.fst).X (n + 1)) :
      c - ((normalizedCubicalChainComplex k).obj P.fst).d (n + 1) n a ∈
          LinearMap.range (((normalizedCubicalChainComplex k).map P.map).f n).hom ↔
        (P.cubicalChainComplex k).iCycles n r = (P.cubicalChainComplex k).iCycles n
          ((P.cubicalChainComplex k).toCycles (n + 1) n
            ((cokernel.π ((normalizedCubicalChainComplex k).map P.map)).f (n + 1) a)) := by
    rw [← HomologicalComplex.cokernel_π_f_apply_eq_zero_iff,
      HomologicalComplex.moduleCat_iCycles_toCycles_apply, HomologicalComplex.Hom.comm_apply,
      map_sub, hr, sub_eq_zero]
  simp_rw [hπ]
  refine ⟨fun h0 ↦ ?_, fun ⟨a, ha⟩ ↦ ?_⟩
  · obtain ⟨b, rfl⟩ :=
      ((P.cubicalChainComplex k).moduleCat_homologyπ_eq_zero_iff (m := n + 1) (by simp) r).1 h0
    obtain ⟨a, rfl⟩ := HomologicalComplex.cokernel_π_f_surjective _ (n + 1) b
    exact ⟨a, rfl⟩
  · rw [(P.cubicalChainComplex k).moduleCat_iCycles_injective n ha]
    exact ((P.cubicalChainComplex k).moduleCat_homologyπ_eq_zero_iff (m := n + 1) (by simp)
      _).2 ⟨_, rfl⟩

/-- **Relative cycles bound when the relative homology vanishes**: if `Hₙ(X, A) = 0`, every
`n`-chain of `X` whose boundary is a chain of `A` is the boundary of a chain of `X` up to a chain of
`A`. -/
theorem exists_d_sub_mem_range_of_isZero
    (hP : Limits.IsZero ((P.cubicalChainComplex k).homology n))
    (c : ((normalizedCubicalChainComplex k).obj P.fst).X n)
    (hc : ((normalizedCubicalChainComplex k).obj P.fst).d n (n - 1) c ∈
      LinearMap.range (((normalizedCubicalChainComplex k).map P.map).f (n - 1)).hom) :
    ∃ a : ((normalizedCubicalChainComplex k).obj P.fst).X (n + 1),
      c - ((normalizedCubicalChainComplex k).obj P.fst).d (n + 1) n a ∈
        LinearMap.range (((normalizedCubicalChainComplex k).map P.map).f n).hom := by
  obtain ⟨μ, h⟩ := exists_isCubicalRepresentative_of_d_mem c hc
  exact h.eq_zero_iff.1 ((ModuleCat.subsingleton_of_isZero hP).elim _ _)

/-- **Boundaries represent the zero class**: the boundary of a chain of the ambient space of a pair
represents the zero class of the relative homology. -/
theorem isCubicalRepresentative_d (a : ((normalizedCubicalChainComplex k).obj P.fst).X (n + 1)) :
    P.IsCubicalRepresentative k
      (((normalizedCubicalChainComplex k).obj P.fst).d (n + 1) n a) 0 := by
  obtain ⟨μ, hμ⟩ := exists_isCubicalRepresentative_of_d_mem
    (((normalizedCubicalChainComplex k).obj P.fst).d (n + 1) n a) (by
      have h := ConcreteCategory.congr_hom
        (((normalizedCubicalChainComplex k).obj P.fst).d_comp_d (n + 1) n (n - 1)) a
      exact ((ConcreteCategory.comp_apply _ _ _).symm.trans h) ▸ zero_mem _)
  rwa [hμ.eq_zero_iff.2 ⟨a, by rw [sub_self]; exact zero_mem _⟩] at hμ

end Representative

/-- A map of pairs `f : (X, A) ⟶ (X', A')` whose map of ambient spaces factors through the
subspace `A'` induces the zero map on relative cubical chains. -/
theorem cubicalChainComplexMap_eq_zero_of_fac {P P' : TopPair.{u}} (f : P ⟶ P')
    (g : P.fst ⟶ P'.snd) (hg : g ≫ P'.map = Hom.fst f) : cubicalChainComplexMap k f = 0 := by
  rw [← cancel_epi (cokernel.π _), π_cubicalChainComplexMap, comp_zero, ← hg, Functor.map_comp,
    Category.assoc, cokernel.condition, comp_zero]

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

/-- A degenerate cube vanishes as a relative chain. -/
@[simp]
theorem cubicalChainOfCube_eq_zero {P : TopPair.{u}} {m : ℕ} {c : SingularCube P.fst m}
    (hc : SingularCube.IsDegenerate c) : cubicalChainOfCube k c = 0 := by
  rw [cubicalChainOfCube_def, normalizedCubicalChainComplexXEquiv_symm_apply,
    NormalizedCubicalChain.ofCube_eq_zero k hc]
  exact map_zero ((cokernel.π ((normalizedCubicalChainComplex k).map P.map)).f m).hom

/-- A cube of the subspace vanishes as a relative chain. -/
@[simp]
theorem cubicalChainOfCube_map_comp_eq_zero {P : TopPair.{u}} {m : ℕ} (c : SingularCube P.snd m) :
    cubicalChainOfCube k (P.map.hom.comp c) = 0 := by
  rw [cubicalChainOfCube_def, normalizedCubicalChainComplexXEquiv_symm_apply,
    ← NormalizedCubicalChain.map_ofCube, ← normalizedCubicalChainComplex_map_f_apply]
  exact congr(ModuleCat.Hom.hom $(cubicalChainComplex_condition_f k P m) _)

/-- The relative boundary of a cube is the signed sum of the relative chains of its faces. -/
theorem d_cubicalChainOfCube_eq_sum {P : TopPair.{u}} {m : ℕ} (c : SingularCube P.fst (m + 1)) :
    (P.cubicalChainComplex k).d (m + 1) m (cubicalChainOfCube k c) =
      ∑ i : Fin (m + 1), (-1 : k) ^ (i : ℕ) •
        (cubicalChainOfCube k (SingularCube.face i 0 c) -
          cubicalChainOfCube k (SingularCube.face i 1 c)) := by
  rw [cubicalChainOfCube_def, HomologicalComplex.Hom.comm_apply]
  simp only [cubicalChainOfCube_def, ← map_sub, ← map_smul, ← map_sum]
  congr 1
  apply (normalizedCubicalChainComplexXEquiv P.fst m).injective
  rw [normalizedCubicalChainComplexXEquiv_d_apply, LinearEquiv.apply_symm_apply,
    LinearEquiv.apply_symm_apply, NormalizedCubicalChain.boundary_ofCube]

variable {k} in
/-- Two linear maps out of the relative normalized cubical `n`-chains of a pair agree if they agree
on the relative chain of every cube. -/
@[ext]
theorem cubicalChainComplexX_linearMap_ext {P : TopPair.{u}} {n : ℕ} {M : Type*} [AddCommGroup M]
    [Module k M] {f₁ f₂ : (P.cubicalChainComplex k).X n →ₗ[k] M}
    (h : ∀ c : SingularCube P.fst n, f₁ (cubicalChainOfCube k c) = f₂ (cubicalChainOfCube k c)) :
    f₁ = f₂ := by
  have h' : f₁ ∘ₗ ((cokernel.π ((normalizedCubicalChainComplex k).map P.map)).f n).hom ∘ₗ
        (normalizedCubicalChainComplexXEquiv P.fst n).symm.toLinearMap =
      f₂ ∘ₗ ((cokernel.π ((normalizedCubicalChainComplex k).map P.map)).f n).hom ∘ₗ
        (normalizedCubicalChainComplexXEquiv P.fst n).symm.toLinearMap :=
    NormalizedCubicalChain.linearMap_ext fun c ↦ h c
  refine LinearMap.ext fun x ↦ ?_
  obtain ⟨y, rfl⟩ := HomologicalComplex.cokernel_π_f_surjective _ n x
  obtain ⟨z, rfl⟩ := (normalizedCubicalChainComplexXEquiv P.fst n).symm.surjective y
  exact LinearMap.congr_fun h' z

/-- The descent of a linear map `g` to the relative chains takes the relative chain of a cube `c`
to the value of `g` on the class of `c`. -/
@[simp]
theorem cubicalChainComplexXDesc_cubicalChainOfCube {P : TopPair.{u}} {n : ℕ} {M : Type*}
    [AddCommGroup M] [Module k M] (g : NormalizedCubicalChain P.fst k n →ₗ[k] M)
    (hg : g ∘ₗ NormalizedCubicalChain.map k P.map.hom n = 0) (c : SingularCube P.fst n) :
    cubicalChainComplexXDesc k g hg (cubicalChainOfCube k c) =
      g (NormalizedCubicalChain.ofCube P.fst k c) := by
  rw [cubicalChainOfCube_def, cubicalChainComplexXDesc_π,
    normalizedCubicalChainComplexXEquiv_symm_apply]

/-- The chain map induced by a map of pairs `f` sends the relative chain of a cube `c` to that of
`f ∘ c`. -/
@[simp]
theorem cubicalChainComplexMap_f_cubicalChainOfCube {P P' : TopPair.{u}} (f : P ⟶ P') {m : ℕ}
    (c : SingularCube P.fst m) :
    (cubicalChainComplexMap k f).f m (cubicalChainOfCube k c) =
      cubicalChainOfCube k ((Hom.fst f).hom.comp c) := by
  rw [cubicalChainOfCube_def, cubicalChainOfCube_def, π_cubicalChainComplexMap_f_apply]
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
  rw [HomologicalComplex.moduleCat_iCycles_cyclesMap_apply]
  simp

/-- **A relative cube represents a relative class**: a singular cube of the ambient space of a pair
sending the boundary of the cube into the subspace represents a class of the relative cubical
homology of the pair. In positive dimension it is the class of `TopPair.cubicalCycleOfCube`. -/
theorem exists_isCubicalRepresentative_ofCube {P : TopPair.{u}} {n : ℕ} (c : SingularCube P.fst n)
    (hc : Set.MapsTo c (Cube.boundary (Fin n)) (Set.range P.map)) :
    ∃ μ, P.IsCubicalRepresentative k (NormalizedCubicalChain.ofCube P.fst k c) μ := by
  cases n with
  | zero => exact exists_isCubicalRepresentative_of_dim_zero _
  | succ m =>
    exact ⟨_, (isCubicalRepresentative_iff _ _).2 ⟨cubicalCycleOfCube k c hc, by
      rw [iCycles_cubicalCycleOfCube, cubicalChainOfCube_def,
        normalizedCubicalChainComplexXEquiv_symm_apply], rfl⟩⟩

/-! ### The boundary of a relative cube -/

section BoundaryOfCube

variable {P : TopPair.{u}}

/-- The faces of a cube sending the boundary of the cube into the subspace take values in the
subspace. -/
theorem face_mem_range_map {m : ℕ} {c : SingularCube P.fst (m + 1)}
    (hc : Set.MapsTo c (Cube.boundary (Fin (m + 1))) (Set.range P.map)) (i : Fin (m + 1))
    {t : unitInterval} (ht : t = 0 ∨ t = 1) (x : Fin m → unitInterval) :
    SingularCube.face i t c x ∈ Set.range P.map := by
  rw [SingularCube.face_apply]
  exact hc ⟨i, by simpa using ht⟩

/-- The **boundary of a relative cube**, read in the subspace. A singular cube `c` of `X` sending
the boundary of the cube into `A` has its faces in `A`, and this is the signed sum
`∑ᵢ (-1)ⁱ (cᵢ⁰ - cᵢ¹)` of these faces as a normalized cubical chain of `A`. Its image in `X` is
the boundary of `c` (`TopPair.map_cubicalBoundaryChainOfCube`). -/
def cubicalBoundaryChainOfCube {m : ℕ} (c : SingularCube P.fst (m + 1))
    (hc : Set.MapsTo c (Cube.boundary (Fin (m + 1))) (Set.range P.map)) :
    NormalizedCubicalChain P.snd k m :=
  ∑ i : Fin (m + 1), (-1 : k) ^ (i : ℕ) •
    (NormalizedCubicalChain.ofCube P.snd k
        (P.liftSnd (SingularCube.face i 0 c) (face_mem_range_map hc i (.inl rfl))) -
      NormalizedCubicalChain.ofCube P.snd k
        (P.liftSnd (SingularCube.face i 1 c) (face_mem_range_map hc i (.inr rfl))))

/-- The boundary of a relative cube is the signed sum `∑ᵢ (-1)ⁱ (cᵢ⁰ - cᵢ¹)` of its faces, lifted
to the subspace. -/
theorem cubicalBoundaryChainOfCube_def {m : ℕ} (c : SingularCube P.fst (m + 1))
    (hc : Set.MapsTo c (Cube.boundary (Fin (m + 1))) (Set.range P.map)) :
    cubicalBoundaryChainOfCube k c hc =
      ∑ i : Fin (m + 1), (-1 : k) ^ (i : ℕ) •
        (NormalizedCubicalChain.ofCube P.snd k (P.liftSnd (SingularCube.face i 0 c) fun x ↦ by
            rw [SingularCube.face_apply]; exact hc ⟨i, by simp⟩) -
          NormalizedCubicalChain.ofCube P.snd k (P.liftSnd (SingularCube.face i 1 c) fun x ↦ by
            rw [SingularCube.face_apply]; exact hc ⟨i, by simp⟩)) :=
  (rfl)

/-- The boundary of a relative cube, read in the subspace, is carried to the boundary of the cube
by the inclusion of the subspace. -/
@[simp]
theorem map_cubicalBoundaryChainOfCube {m : ℕ} (c : SingularCube P.fst (m + 1))
    (hc : Set.MapsTo c (Cube.boundary (Fin (m + 1))) (Set.range P.map)) :
    NormalizedCubicalChain.map k P.map.hom m (cubicalBoundaryChainOfCube k c hc) =
      NormalizedCubicalChain.boundary P.fst k m (NormalizedCubicalChain.ofCube P.fst k c) := by
  have h (g : SingularCube P.fst m) (hg : ∀ x, g x ∈ Set.range P.map) :
      P.map.hom.comp (P.liftSnd g hg) = g := ContinuousMap.ext (map_liftSnd g hg)
  simp [cubicalBoundaryChainOfCube, NormalizedCubicalChain.boundary_ofCube,
    NormalizedCubicalChain.map_ofCube, h]

/-- The boundary of a mapped cube is the pushforward of its lifted boundary in the subspace
of a pair. -/
theorem boundary_ofCube_comp {Y : Type*} [TopologicalSpace Y] (P : TopPair.{u})
    {m : ℕ} (c : SingularCube P.fst (m + 1))
    (hc : Set.MapsTo c (Cube.boundary (Fin (m + 1))) (Set.range P.map))
    (q : C(P.fst, Y)) :
    NormalizedCubicalChain.boundary Y k m
      (NormalizedCubicalChain.ofCube Y k (q.comp c)) =
      NormalizedCubicalChain.map k (q.comp P.map.hom) m
        (P.cubicalBoundaryChainOfCube k c hc) := by
  rw [NormalizedCubicalChain.map_comp, LinearMap.comp_apply, map_cubicalBoundaryChainOfCube,
    NormalizedCubicalChain.map_boundary_apply, NormalizedCubicalChain.map_ofCube]

/-- The boundary of a relative cube, read in the subspace, is a cycle. -/
@[simp]
theorem boundary_cubicalBoundaryChainOfCube {m : ℕ} (c : SingularCube P.fst (m + 2))
    (hc : Set.MapsTo c (Cube.boundary (Fin (m + 2))) (Set.range P.map)) :
    NormalizedCubicalChain.boundary P.snd k m (cubicalBoundaryChainOfCube k c hc) = 0 := by
  -- The inclusion of the subspace is injective on normalized chains and carries the chain to the
  -- boundary of `c`, whose boundary vanishes.
  apply NormalizedCubicalChain.map_injective k P.map.hom P.isEmbedding_map.injective m
  rw [← LinearMap.comp_apply, NormalizedCubicalChain.map_boundary, LinearMap.comp_apply,
    map_cubicalBoundaryChainOfCube, map_zero]
  rw [← LinearMap.comp_apply, NormalizedCubicalChain.boundary_boundary, LinearMap.zero_apply]

/-- The boundary of a relative cube, read in the subspace, is killed by every differential of the
normalized cubical chain complex of the subspace. -/
@[simp]
theorem d_cubicalBoundaryChainOfCube {m : ℕ} (c : SingularCube P.fst (m + 1))
    (hc : Set.MapsTo c (Cube.boundary (Fin (m + 1))) (Set.range P.map)) (j : ℕ) :
    ((normalizedCubicalChainComplex k).obj P.snd).d m j (cubicalBoundaryChainOfCube k c hc) =
      0 := by
  -- Only `d (m + 1) m` can be nonzero; it is the cubical boundary.
  rcases m with _ | m
  · rw [HomologicalComplex.shape _ _ _ (by simp)]
    exact LinearMap.zero_apply _
  · by_cases hj : j = m
    · subst hj
      rw [normalizedCubicalChainComplex_obj_d_apply]
      exact boundary_cubicalBoundaryChainOfCube k c hc
    · rw [HomologicalComplex.shape _ _ _ (by simpa using hj)]
      exact LinearMap.zero_apply _

/-- The boundary of a singular cube `c` of `X` sending the boundary of the cube into `A`, as a
normalized cubical cycle of `A`. -/
def cubicalBoundaryCycleOfCube {m : ℕ} (c : SingularCube P.fst (m + 1))
    (hc : Set.MapsTo c (Cube.boundary (Fin (m + 1))) (Set.range P.map)) :
    ((normalizedCubicalChainComplex k).obj P.snd).cycles m :=
  HomologicalComplex.moduleCatCyclesMk _ (cubicalBoundaryChainOfCube k c hc) _ rfl
    (d_cubicalBoundaryChainOfCube k c hc _)

@[simp]
theorem iCycles_cubicalBoundaryCycleOfCube {m : ℕ} (c : SingularCube P.fst (m + 1))
    (hc : Set.MapsTo c (Cube.boundary (Fin (m + 1))) (Set.range P.map)) :
    (((normalizedCubicalChainComplex k).obj P.snd).iCycles m).hom
        (cubicalBoundaryCycleOfCube k c hc) = cubicalBoundaryChainOfCube k c hc :=
  HomologicalComplex.iCycles_moduleCatCyclesMk ..

end BoundaryOfCube

/-! ### The relative comparison maps -/

/-- The quotient map from the simplicial singular chains of the ambient space to the relative
singular chains, with its source written as `(singularChains k).obj P.fst`. -/
def singularRelπ (P : TopPair.{u}) :
    (singularChains k).obj P.fst ⟶ P.singularChainComplex (ModuleCat.of k k) :=
  P.singularChainComplexπ _

/-- The quotient map `TopPair.singularRelπ` is the quotient map `TopPair.singularChainComplexπ`
onto the relative singular chains. -/
lemma singularRelπ_eq (P : TopPair.{u}) :
    singularRelπ k P = P.singularChainComplexπ (ModuleCat.of k k) := by
  rw [singularRelπ]

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

/-- On the cokernel of the map of chains of a pair, the map induced by `TauCeti.cubicalToSingular`
is the relative comparison map `TopPair.cubicalToSingularRel`, under the identification
`TopPair.cokernelSingularChainComplexIso` of that cokernel with the relative singular chains. -/
@[reassoc]
theorem cokernel_map_cubicalToSingular_comp (P : TopPair.{u}) :
    cokernel.map _ _ ((cubicalToSingular k).app _) ((cubicalToSingular k).app _)
        ((cubicalToSingular k).naturality P.map).symm ≫
        (P.cokernelSingularChainComplexIso (ModuleCat.of k k)).hom =
      cubicalToSingularRel k P := by
  -- The cokernel of the map of singular chains is written through `TauCeti.singularChains` on one
  -- side and through simplicial chains on the other, so the composites are formed with terms.
  exact (cancel_epi (cokernel.π _)).1 <| (cokernel.π_desc_assoc _ _ _ _).trans <|
    (Category.assoc _ _ _).trans <|
      ((congrArg (_ ≫ ·) (π_cokernelSingularChainComplexIso_hom P _)).trans <|
        congrArg (_ ≫ ·) (singularRelπ_eq k P).symm).trans
          (π_cubicalToSingularRel k P).symm

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

/-- On relative cubical homology, a map of pairs induces its relative singular homology map,
conjugated by the comparison isomorphisms. -/
theorem homologyMap_cubicalChainComplexMap_eq {P P' : TopPair.{u}} (f : P ⟶ P') (n : ℕ) :
    HomologicalComplex.homologyMap (cubicalChainComplexMap k f) n =
      (singularCubicalHomologyIso k P n).inv ≫ P.singularHomologyMap f (ModuleCat.of k k) n ≫
        (singularCubicalHomologyIso k P' n).hom := by
  rw [Iso.eq_inv_comp, singularCubicalHomologyIso_hom_naturality]

/-- The inverse comparison isomorphisms of absolute and relative homology commute with the maps
from absolute to relative homology: an absolute cubical class, read in relative cubical homology
and then in relative singular homology, is its image in absolute singular homology read in
relative singular homology. -/
@[reassoc]
theorem homologyMap_π_comp_singularCubicalHomologyIso_inv (P : TopPair.{u}) (n : ℕ) :
    HomologicalComplex.homologyMap (cokernel.π ((normalizedCubicalChainComplex k).map P.map)) n ≫
        (TopPair.singularCubicalHomologyIso k P n).inv =
      (TauCeti.singularCubicalHomologyIso k P.fst n).inv ≫
        P.singularHomologyπ (ModuleCat.of k k) n := by
  rw [TopPair.singularCubicalHomologyIso_inv, TauCeti.singularCubicalHomologyIso_inv,
    ← HomologicalComplex.homologyMap_comp, π_cubicalToSingularRel,
    HomologicalComplex.homologyMap_comp, singularRelπ]
  -- `P.singularHomologyπ` is, by definition, the map on homology induced by
  -- `P.singularChainComplexπ`.
  rfl

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
