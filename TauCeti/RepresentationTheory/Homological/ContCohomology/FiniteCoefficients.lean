/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.FiniteAbelian.Basic
public import TauCeti.Algebra.Category.ModuleCat.Topology.Homology
public import TauCeti.RepresentationTheory.Homological.ContCohomology.CohomologicalDimension.Basic
public import TauCeti.RepresentationTheory.Homological.ContCohomology.Functoriality
public import TauCeti.Topology.Algebra.GroupAction.QuotientAddGroup

/-!
# Continuous cohomology of a discrete module is detected on finite sets of values

Let `G` be a compact group and `X` a discrete topological representation of `G`. Mathlib's
continuous cohomology `Hⁿ(G, X)` is the homology of the homogeneous cochain complex, whose degree
`n` term consists of the `G`-invariant elements of the iterated function space
`C(G, C(G, …, C(G, X)))` with `n + 1` arguments. Because `G` is compact and `X` is discrete, every
such cochain takes only finitely many values in `X` once all its arguments are evaluated. This
file records that fact and its consequence for cohomology: every class of `Hⁿ(G, X)` is the image
of a class of `Hⁿ(G, Y)` for any subrepresentation `Y ⊆ X` containing those finitely many values.
Without further hypotheses `Y` may be infinite, since the values need not generate a finite
subgroup.

For a discrete **torsion** `G`-module `M` with continuous action, the values of a cocycle generate
a finite `G`-stable subgroup `N ≤ M`, so every class of `Hⁿ(G, M)` comes from `Hⁿ(G, N)` for a
finite `N`. In particular the vanishing of `Hⁿ(G, -)` on all finite `p`-primary discrete modules
implies its vanishing on all `p`-primary discrete modules, which lets the `p`-cohomological
dimension be tested on finite coefficient modules alone. This is the coefficient half of the
dévissage of NSW (3.3.2), the other half being the reduction of the degree through dimension
shifting.

## Main definitions

* `TauCeti.ContinuousCohomology.resolutionValues`: the set of values in `X` of an element of the
  `n`-th term of the coinduced resolution of `X`.

## Main results

* `TauCeti.ContinuousCohomology.finite_resolutionValues`: over a compact group, an element of the
  resolution of a discrete representation takes finitely many values.
* `TauCeti.ContinuousCohomology.exists_resolutionMap_eq_of_resolutionValues_subset`: an element
  of the resolution of `X` whose values lie in the range of an injective morphism `Y ⟶ X` comes
  from the resolution of `Y`.
* `TauCeti.ContinuousCohomology.exists_finite_forall_mem_range_coeffMap`: each class of
  `Hⁿ(G, X)` has a finite set of values `S ⊆ X` such that it lies in the range of `coeffMap ι n`
  for every injective `ι : Y ⟶ X` whose range contains `S`.
* `TauCeti.ContinuousCohomology.exists_finite_addSubgroup_coeffMap_eq`: each class of `Hⁿ(G, M)`,
  for a discrete torsion `G`-module `M`, comes from a finite `G`-stable subgroup of `M`.
* `TauCeti.ContinuousCohomology.subsingleton_continuousCohomology_of_forall_finite_addSubgroup`:
  `Hⁿ(G, M)` vanishes as soon as `Hⁿ(G, N)` vanishes for every finite `G`-stable subgroup `N`.
* `TauCeti.cohomologicalDimensionLE_iff_forall_finite`,
  `TauCeti.cohomologicalDimensionAt_le_iff_forall_finite`: the `p`-cohomological dimension of a
  compact group is at most `n` exactly when `Hⁱ(G, M)` vanishes for every `i > n` and every
  **finite** discrete `p`-primary `G`-module `M`.

## References

* J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, 2nd ed., (3.3.2).
* J.-P. Serre, *Galois Cohomology*, Ch. I §3.1.
-/

public section

namespace TauCeti

open CategoryTheory Topology TopRep

universe u v w

namespace ContinuousCohomology

open _root_.ContinuousCohomology

variable {k : Type u} {G : Type v} [Ring k] [TopologicalSpace k] [Group G] [TopologicalSpace G]
  [IsTopologicalGroup G]

/-! ### The values of an element of the coinduced resolution -/

section Values

variable (X : TopRep.{max v w} k G)

/-- The set of values in `X` of an element of the `n`-th term `C(G, C(G, …, X))` of the coinduced
resolution of `X`: the values obtained by evaluating all `n` function arguments. -/
def resolutionValues : (n : ℕ) → (resolutionX X n).V → Set X.V
  | 0, x => {x}
  | n + 1, f => ⋃ g : G, resolutionValues n ((f : C(G, (resolutionX X n).V)) g)

@[simp]
theorem resolutionValues_zero (x : X.V) : resolutionValues X 0 x = {x} := by
  rw [resolutionValues]

@[simp]
theorem resolutionValues_succ (n : ℕ) (f : (resolutionX X (n + 1)).V) :
    resolutionValues X (n + 1) f =
      ⋃ g : G, resolutionValues X n ((f : C(G, (resolutionX X n).V)) g) := by
  rw [resolutionValues]

/-- Evaluating the outermost argument of an element of the resolution does not enlarge its set of
values. -/
theorem resolutionValues_apply_subset (n : ℕ) (f : (resolutionX X (n + 1)).V) (g : G) :
    resolutionValues X n ((f : C(G, (resolutionX X n).V)) g) ⊆ resolutionValues X (n + 1) f := by
  rw [resolutionValues_succ]
  exact Set.subset_iUnion (fun g : G ↦ resolutionValues X n ((f : C(G, (resolutionX X n).V)) g)) g

/-- Over a compact group, an element of the coinduced resolution of a discrete representation takes
only finitely many values: each of its function arguments ranges over a compact space and lands in
a discrete one. -/
theorem finite_resolutionValues [CompactSpace G] [DiscreteTopology X.V] :
    ∀ (n : ℕ) (x : (resolutionX X n).V), (resolutionValues X n x).Finite
  | 0, x => Set.finite_singleton x
  | n + 1, f => by
    rw [resolutionValues_succ, ← Set.biUnion_range]
    exact (isCompact_range (map_continuous (f : C(G, (resolutionX X n).V)))).finite_of_discrete
      |>.biUnion fun y _ ↦ finite_resolutionValues n y

end Values

/-! ### Lifting along an injective morphism of coefficients -/

section Lift

variable {Y X : TopRep.{max v w} k G} (ι : Y ⟶ X)

/-- The maps induced on the coinduced resolutions by an injective morphism of representations are
injective in every degree. -/
theorem resolutionMap_injective (hι : Function.Injective ι.hom) :
    ∀ n : ℕ, Function.Injective (resolutionMap (ContinuousMonoidHom.id G) ι n).hom
  | 0 => hι
  | n + 1 => fun F F' h ↦ by
    ext g
    -- in degree `n + 1` the map is `F ↦ (resolutionMap _ ι n) ∘ F`, by definition
    exact resolutionMap_injective hι n (DFunLike.congr_fun h g)

/-- The cochain maps induced by an injective morphism of representations are injective in every
degree. -/
theorem cochainsMap_f_injective (hι : Function.Injective ι.hom) (n : ℕ) :
    Function.Injective ((cochainsMap (ContinuousMonoidHom.id G) ι).f n) := fun _ _ h ↦
  Subtype.ext (resolutionMap_injective ι hι (n + 1) (congrArg Subtype.val h))

/-- The maps induced on the coinduced resolutions by an inducing morphism of representations are
inducing in every degree: each term of the resolution of `Y` carries the topology induced from the
corresponding term of the resolution of `X`. -/
theorem resolutionMap_isInducing (hι : IsInducing ι.hom) :
    ∀ n : ℕ, IsInducing (resolutionMap (ContinuousMonoidHom.id G) ι n).hom
  | 0 => hι
  | n + 1 =>
    -- in degree `n + 1` the map is `F ↦ (resolutionMap _ ι n) ∘ F`, by definition
    ContinuousMap.isInducing_postcomp
      ⟨_, map_continuous (resolutionMap (ContinuousMonoidHom.id G) ι n).hom⟩
      (resolutionMap_isInducing hι n)

variable [DiscreteTopology X.V] [DiscreteTopology Y.V]

/-- An element of the coinduced resolution of `X` all of whose values lie in the range of an
injective morphism `ι : Y ⟶ X` comes from the coinduced resolution of `Y`. -/
theorem exists_resolutionMap_eq_of_resolutionValues_subset (hι : Function.Injective ι.hom) :
    ∀ (n : ℕ) (x : (resolutionX X n).V), resolutionValues X n x ⊆ Set.range ι.hom →
      ∃ y : (resolutionX Y n).V, (resolutionMap (ContinuousMonoidHom.id G) ι n).hom y = x
  | 0, x, hx => hx rfl
  | n + 1, F, hF => by
    -- lift each value `F g` separately, then check that the lifts vary continuously
    have h : ∀ g : G, ∃ y : (resolutionX Y n).V,
        (resolutionMap (ContinuousMonoidHom.id G) ι n).hom y =
          (F : C(G, (resolutionX X n).V)) g := fun g ↦
      exists_resolutionMap_eq_of_resolutionValues_subset hι n _
        ((resolutionValues_apply_subset X n F g).trans hF)
    choose y hy using h
    -- an injective map between discrete spaces is inducing
    have hind : IsInducing ι.hom := isInducing_iff_nhds.2 fun y ↦ by
      simp only [nhds_discrete, Filter.comap_pure, ← Set.image_singleton, hι.preimage_image,
        Filter.principal_singleton]
    have hcont : Continuous y :=
      (resolutionMap_isInducing ι hind n).continuous_iff.2 <|
        (map_continuous (F : C(G, (resolutionX X n).V))).congr fun g ↦ (hy g).symm
    refine ⟨⟨y, hcont⟩, ?_⟩
    ext g
    -- in degree `n + 1` the map is `F ↦ (resolutionMap _ ι n) ∘ F`, by definition
    exact hy g

/-- An invariant element of the coinduced resolution of `X`, that is a homogeneous cochain, all
of whose values lie in the range of an injective morphism `ι : Y ⟶ X` is the image of a
homogeneous cochain of `Y` under the induced cochain map. -/
theorem exists_cochainsMap_f_eq_of_resolutionValues_subset (hι : Function.Injective ι.hom) (n : ℕ)
    (c : (homogeneousCochains X).X n)
    (hc : resolutionValues X (n + 1) c.1 ⊆ Set.range ι.hom) :
    ∃ c' : (homogeneousCochains Y).X n, (cochainsMap (ContinuousMonoidHom.id G) ι).f n c' = c := by
  obtain ⟨y, hy⟩ := exists_resolutionMap_eq_of_resolutionValues_subset ι hι (n + 1) c.1 hc
  -- `y` is invariant because its image `c.1` is and the map is injective and equivariant
  have hyinv : y ∈ (resolutionX Y (n + 1)).ρ.invariants := fun g ↦
    resolutionMap_injective ι hι (n + 1) <|
      (TopRep.hom_comm_apply (resolutionMap (X := Y) (ContinuousMonoidHom.id G) ι (n + 1))
        g y).trans (by rw [hy]; exact c.2 g)
  exact ⟨⟨y, hyinv⟩, Subtype.ext hy⟩

end Lift

/-! ### Every cohomology class comes from a finite set of values -/

section Cohomology

variable [CompactSpace G] {X : TopRep.{max v w} k G} [DiscreteTopology X.V]

/-- **Every continuous cohomology class of a discrete representation of a compact group comes
from finitely many values.** For each class `x ∈ Hⁿ(G, X)` there is a finite set `S ⊆ X` such that
`x` lies in the image of `Hⁿ(G, Y)` under `coeffMap ι n` for every injective morphism `ι : Y ⟶ X`
from a discrete representation whose range contains `S`. -/
theorem exists_finite_forall_mem_range_coeffMap (n : ℕ) (x : continuousCohomology n X) :
    ∃ S : Set X.V, S.Finite ∧ ∀ (Y : TopRep.{max v w} k G) [DiscreteTopology Y.V] (ι : Y ⟶ X),
      Function.Injective ι.hom → S ⊆ Set.range ι.hom → x ∈ Set.range (coeffMap ι n).hom := by
  set K := homogeneousCochains X
  obtain ⟨c, rfl⟩ := K.homologyπ_surjective n x
  refine ⟨resolutionValues X (n + 1) (K.iCycles n c).1, finite_resolutionValues X _ _,
    fun Y _ ι hι hS ↦ ?_⟩
  set L := homogeneousCochains Y
  obtain ⟨c', hc'⟩ := exists_cochainsMap_f_eq_of_resolutionValues_subset ι hι n (K.iCycles n c) hS
  -- `c'` is a cocycle, because its image `c` is and the cochain map is injective
  have hd : (L.sc n).g c' = 0 := by
    have h₁ := ConcreteCategory.congr_hom
      ((cochainsMap (ContinuousMonoidHom.id G) ι).comm n ((ComplexShape.up ℕ).next n)) c'
    have h₂ := ConcreteCategory.congr_hom (K.sc n).iCycles_g c
    simp only [ConcreteCategory.comp_apply] at h₁ h₂
    refine cochainsMap_f_injective ι hι ((ComplexShape.up ℕ).next n) ?_
    -- `(L.sc n).g` and `(K.sc n).g` are the differentials out of degree `n`, by definition of `sc`
    exact (h₁.symm.trans (by rw [hc']; exact h₂)).trans (map_zero _).symm
  -- the cycle of `L` lifting `c`
  let z : L.cycles n :=
    ((L.sc n).isoCyclesOfIsLimit (TopModuleCat.isLimitKer (L.sc n).g)).hom ⟨c', hd⟩
  have hz : L.iCycles n z = c' := by
    have := ConcreteCategory.congr_hom
      ((L.sc n).isoCyclesOfIsLimit_hom_iCycles (TopModuleCat.isLimitKer (L.sc n).g)) ⟨c', hd⟩
    simp only [ConcreteCategory.comp_apply, Limits.KernelFork.ι_ofι] at this
    -- `L.iCycles n` is `(L.sc n).iCycles` and `kerι` is the subtype inclusion, by definition
    exact this
  have hzc : HomologicalComplex.cyclesMap (cochainsMap (ContinuousMonoidHom.id G) ι) n z = c := by
    refine K.iCycles_injective n ?_
    have h := ConcreteCategory.congr_hom
      (HomologicalComplex.cyclesMap_i (cochainsMap (ContinuousMonoidHom.id G) ι) n) z
    simp only [ConcreteCategory.comp_apply] at h
    rw [h, hz, hc']
  refine ⟨L.homologyπ n z, ?_⟩
  have h := ConcreteCategory.congr_hom (π_map (ContinuousMonoidHom.id G) ι n) z
  simp only [ConcreteCategory.comp_apply] at h
  rw [coeffMap_def]
  exact h.trans (congrArg _ hzc)

end Cohomology

/-! ### Discrete torsion modules: every class comes from a finite stable subgroup -/

section DiscreteModule

variable [CompactSpace G] {M : Type (max v w)} [AddCommGroup M] [TopologicalSpace M]
  [DiscreteTopology M] [DistribMulAction G M] [ContinuousSMul G M]

/-- **Every class of `Hⁿ(G, M)` comes from a finite `G`-stable subgroup.** Let `G` be a compact
group and `M` a discrete torsion `G`-module with continuous action. Every class of `Hⁿ(G, M)` is
the image of a class of `Hⁿ(G, N)` for some finite `G`-stable additive subgroup `N ≤ M`, under the
coefficient map of the inclusion. The subgroup is generated by the finitely many values of a
representing cocycle and their `G`-translates; it is finite because each orbit is finite and `M`
is torsion. -/
theorem exists_finite_addSubgroup_coeffMap_eq (hM : IsAddTorsion M) (n : ℕ)
    (x : continuousCohomology n (ofDiscreteModule ℤ G M)) :
    ∃ (N : AddSubgroup M) (hN : ∀ g : G, ∀ m ∈ N, g • m ∈ N), Finite N ∧
      letI := N.restrictDistribMulAction hN
      ∃ y : continuousCohomology n (ofDiscreteModule ℤ G N),
        coeffMap (ofDiscreteModuleMap N.subtype.toIntLinearMap
          (N.restrictDistribMulAction_coe_smul hN)) n y = x := by
  obtain ⟨S, hS, h⟩ := exists_finite_forall_mem_range_coeffMap n x
  -- the values, read in `M` itself rather than in the underlying type of the representation
  let S' : Set M := S
  have hS' : S'.Finite := hS
  -- the `G`-translates of the values, a finite `G`-stable set
  set T : Set M := ⋃ s ∈ S', Set.range fun g : G ↦ g • s
  have hTfin : T.Finite := hS'.biUnion fun s _ ↦
    (isCompact_range (continuous_id.smul continuous_const)).finite_of_discrete
  have hTstab : ∀ g : G, ∀ m ∈ T, g • m ∈ T := by
    intro g m hm
    obtain ⟨s, hs, g', rfl⟩ := Set.mem_iUnion₂.1 hm
    exact Set.mem_iUnion₂.2 ⟨s, hs, g * g', mul_smul g g' s⟩
  set N : AddSubgroup M := AddSubgroup.closure T
  have hN : ∀ g : G, ∀ m ∈ N, g • m ∈ N := by
    intro g m hm
    induction hm using AddSubgroup.closure_induction with
    | mem m hm => exact AddSubgroup.subset_closure (hTstab g m hm)
    | zero => simpa only [smul_zero] using N.zero_mem
    | add m m' _ _ hm hm' => simpa only [smul_add] using N.add_mem hm hm'
    | neg m _ hm => simpa only [smul_neg] using N.neg_mem hm
  have : AddGroup.FG N :=
    (AddGroup.fg_iff_addSubgroup_fg N).2 ((AddSubgroup.fg_iff N).2 ⟨T, rfl, hTfin⟩)
  refine ⟨N, hN, AddCommGroup.finite_of_fg_isAddTorsion N (hM.addSubgroup N), ?_⟩
  let := N.restrictDistribMulAction hN
  refine h (ofDiscreteModule ℤ G N)
    (ofDiscreteModuleMap N.subtype.toIntLinearMap (N.restrictDistribMulAction_coe_smul hN))
    (fun a b hab ↦ Subtype.ext hab) fun s hs ↦ ?_
  exact ⟨⟨s, AddSubgroup.subset_closure (Set.mem_iUnion₂.2 ⟨s, hs, 1, one_smul G _⟩)⟩, rfl⟩

/-- **Vanishing of continuous cohomology is detected on finite stable subgroups.** Let `G` be a
compact group and `M` a discrete torsion `G`-module with continuous action. If `Hⁿ(G, N)` vanishes
for every finite `G`-stable additive subgroup `N ≤ M`, then `Hⁿ(G, M)` vanishes. -/
theorem subsingleton_continuousCohomology_of_forall_finite_addSubgroup (hM : IsAddTorsion M)
    (n : ℕ)
    (h : ∀ (N : AddSubgroup M) (hN : ∀ g : G, ∀ m ∈ N, g • m ∈ N), Finite N →
      letI := N.restrictDistribMulAction hN
      Subsingleton (continuousCohomology n (ofDiscreteModule ℤ G N))) :
    Subsingleton (continuousCohomology n (ofDiscreteModule ℤ G M)) := by
  refine subsingleton_of_forall_eq 0 fun x ↦ ?_
  obtain ⟨N, hN, hfin, y, rfl⟩ := exists_finite_addSubgroup_coeffMap_eq hM n x
  have := h N hN hfin
  rw [Subsingleton.elim y 0, map_zero]

end DiscreteModule

end ContinuousCohomology

/-! ### Cohomological dimension is detected on finite coefficient modules -/

section CohomologicalDimension

variable {p : ℕ} {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G]

/-- **The finite-coefficient test for the vanishing predicate of cohomological dimension**
(NSW (3.3.2), coefficient reduction). For a compact group `G` and `p ≠ 0`, the predicate
`CohomologicalDimensionLE p G n` holds exactly when `Hⁱ(G, M)` vanishes for every `i > n` and
every **finite** discrete `p`-primary `G`-module `M`. -/
theorem cohomologicalDimensionLE_iff_forall_finite (hp : p ≠ 0) {n : ℕ} :
    CohomologicalDimensionLE.{v} p G n ↔
      ∀ (M : Type (max u v)) [AddCommGroup M] [TopologicalSpace M] [DiscreteTopology M]
        [DistribMulAction G M] [ContinuousSMul G M] [Finite M], IsPPrimaryTorsion p M →
        ∀ i : ℕ, n < i → Subsingleton (continuousCohomology i (ofDiscreteModule ℤ G M)) := by
  rw [cohomologicalDimensionLE_iff]
  refine ⟨fun h M _ _ _ _ _ _ hM i hi ↦ h M hM i hi, fun h M _ _ _ _ _ hM i hi ↦ ?_⟩
  refine ContinuousCohomology.subsingleton_continuousCohomology_of_forall_finite_addSubgroup
    (hM.isAddTorsion hp) i fun N hN hfin ↦ ?_
  let := N.restrictDistribMulAction hN
  have : ContinuousSMul G N := N.restrictDistribMulAction_continuousSMul hN
  exact h N (hM.of_injective N.subtype N.subtype_injective) i hi

/-- **The `p`-cohomological dimension of a compact group is detected on finite coefficients**
(NSW (3.3.2), coefficient reduction). For `p ≠ 0`, `cd_p G ≤ n` exactly when `Hⁱ(G, M)` vanishes
for every `i > n` and every **finite** discrete `p`-primary `G`-module `M`. -/
theorem cohomologicalDimensionAt_le_iff_forall_finite (hp : p ≠ 0) (n : ℕ) :
    cohomologicalDimensionAt.{v} p G ≤ n ↔
      ∀ (M : Type (max u v)) [AddCommGroup M] [TopologicalSpace M] [DiscreteTopology M]
        [DistribMulAction G M] [ContinuousSMul G M] [Finite M], IsPPrimaryTorsion p M →
        ∀ i : ℕ, n < i → Subsingleton (continuousCohomology i (ofDiscreteModule ℤ G M)) := by
  rw [cohomologicalDimensionAt_le_iff, cohomologicalDimensionLE_iff_forall_finite hp]

end CohomologicalDimension

end TauCeti
