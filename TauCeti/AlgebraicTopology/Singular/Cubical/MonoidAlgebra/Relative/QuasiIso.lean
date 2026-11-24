/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Singular.Cubical.Comparison.Relative.Basic
public import TauCeti.AlgebraicTopology.Singular.Cubical.MonoidAlgebra.Support
import TauCeti.Algebra.Homology.ComplexShape.Basic

/-!
# Quasi-isomorphisms of relative cubical chains, on the chains of other spaces

Let `f : P ⟶ P'` be a map of pairs inducing a quasi-isomorphism of relative normalized cubical
chains. This file reads the quasi-isomorphism on the module `TauCeti.cubicalChainModule` of chains
of spaces related to the pairs: a space `Z` homeomorphic to the ambient space of `P`, and a space
`Y` in which the ambient space of `P'` embeds. The relative chains of `P` become the chains of `Z`
modulo those supported in the preimage of the subspace, and the relative chains of `P'` become the
chains of `Y` supported in the range of the embedding modulo those supported in the image of the
subspace. In this form every relative cycle is a relative boundary
(`TauCeti.exists_add_differential_sub_mem_cubicalChainModuleSupportedIn_of_quasiIso`).

This is how a quasi-isomorphism of relative chains of pullbacks is transported to the quotients of
a filtration of the chains of a space by supports, as for the skeletal filtration of the chains on
the based path space.

The proof reads the quasi-isomorphism on chains with
`TauCeti.TopPair.quasiIsoAt_cubicalChainComplexMap_iff`. Injectivity on relative homology in
dimension `m` and surjectivity in dimension `m + 1` together bound the relative cycles of
dimensions `m` and `m + 1`, and the statement for all chains follows by splitting them into
homogeneous components (`TauCeti.exists_relative_boundary_of_forall_homogeneous`).

## Main results

* `TauCeti.exists_add_differential_sub_mem_cubicalChainModuleSupportedIn_of_quasiIso`: a
  quasi-isomorphism of relative cubical chains, read on the chains of `Z` and `Y`, makes every
  relative cycle a relative boundary.
-/

public section

noncomputable section

open CategoryTheory Limits Topology

namespace TauCeti

universe u

variable {R : Type u} [CommRing R]

/-! ### Chains of the ambient space of a pair and `cubicalChainModule` -/

variable (H : Type*)

open NormalizedCubicalChain in
/-- The differential of a chain of the ambient space of a pair is a chain of the subspace exactly
when the differential of its push-forward along an embedding `ι` is supported in the image of the
subspace. -/
private theorem d_mem_range_map_f_iff (P : TopPair.{u}) {Y : Type u} [TopologicalSpace Y]
    {ι : C(P.fst, Y)} (hι : IsEmbedding ι) {m : ℕ}
    (c : ((normalizedCubicalChainComplex R).obj P.fst).X m) :
    ((normalizedCubicalChainComplex R).obj P.fst).d m (m - 1) c ∈
        LinearMap.range (((normalizedCubicalChainComplex R).map P.map).f (m - 1)).hom ↔
      cubicalChainModuleDifferential Y H R (cubicalChainModuleLof Y H R m
          (map R ι m (normalizedCubicalChainComplexXEquiv P.fst m c))) ∈
        cubicalChainModuleSupportedIn H R (ι '' Set.range P.map) := by
  cases m with
  | zero =>
    rw [HomologicalComplex.shape _ 0 (0 - 1) (by simp), cubicalChainModuleDifferential_lof_zero]
    exact iff_of_true (zero_mem _) (zero_mem _)
  | succ k =>
    rw [Nat.add_sub_cancel, TopPair.mem_range_normalizedCubicalChainComplex_map_f_iff,
      normalizedCubicalChainComplexXEquiv_d_apply,
      cubicalChainModuleDifferential_lof_succ,
      cubicalChainModuleLof_mem_cubicalChainModuleSupportedIn_iff, ← map_boundary_apply,
      map_mem_supportedIn_image_iff R hι]

/-! ### Quasi-isomorphisms of relative chains, read on chains of other spaces

Throughout, `f : P ⟶ P'` is a map of pairs, `e : Z ≃ₜ P.fst` identifies a space `Z` with the
ambient space of `P`, `ι : P'.fst → Y` embeds the ambient space of `P'` in a space `Y`, and
`Φ : Z → Y` is the composite of `e`, the map of ambient spaces and `ι`. A quasi-isomorphism of
relative chains `N(P) ⟶ N(P')` is read on the chains of `Z` and `Y`: the subspace of `P` becomes
its preimage under `e`, and the relative chains of `P'` become the chains of `Y` supported in the
range of `ι` modulo those supported in the image of the subspace of `P'`. -/

section QuasiIsoAt

variable {P P' : TopPair.{u}} (f : P ⟶ P') {Z Y : Type u} [TopologicalSpace Z]
  [TopologicalSpace Y] (e : Z ≃ₜ P.fst) {ι : C(P'.fst, Y)} (hι : IsEmbedding ι) (Φ : C(Z, Y))
  (hΦ : ∀ z, Φ z = ι (TopPair.Hom.fst f (e z)))

include hΦ in
/-- The map `Φ` is the composite of `e`, the map of ambient spaces and `ι`, on chains. -/
private theorem map_map_homeomorph_symm (m : ℕ) (x : NormalizedCubicalChain P.fst R m) :
    NormalizedCubicalChain.map R Φ m
        (NormalizedCubicalChain.map R (e.symm : C(P.fst, Z)) m x) =
      NormalizedCubicalChain.map R ι m
        (NormalizedCubicalChain.map R (TopPair.Hom.fst f).hom m x) := by
  have h : Φ.comp (e.symm : C(P.fst, Z)) = ι.comp (TopPair.Hom.fst f).hom :=
    ContinuousMap.ext fun z ↦ by simp [hΦ]
  rw [NormalizedCubicalChain.map_map, h, ← NormalizedCubicalChain.map_map]

include hΦ in
/-- The map `Φ` on chains, through the ambient spaces of the pairs. -/
private theorem map_eq_map_map (m : ℕ) (a : NormalizedCubicalChain Z R m) :
    NormalizedCubicalChain.map R Φ m a = NormalizedCubicalChain.map R ι m
      (NormalizedCubicalChain.map R (TopPair.Hom.fst f).hom m
        (NormalizedCubicalChain.map R (e : C(Z, P.fst)) m a)) := by
  rw [← map_map_homeomorph_symm f e Φ hΦ, NormalizedCubicalChain.map_symm_map_apply]

include hΦ hι in
open NormalizedCubicalChain in
/-- **Surjectivity on relative homology, read in `Z` and `Y`.** -/
private theorem exists_sub_sub_mem_supportedIn {m : ℕ}
    [QuasiIsoAt (TopPair.cubicalChainComplexMap R f) m] (y : NormalizedCubicalChain Y R m)
    (hy : y ∈ supportedIn R (Set.range ι) m)
    (hdy : cubicalChainModuleDifferential Y H R (cubicalChainModuleLof Y H R m y) ∈
      cubicalChainModuleSupportedIn H R (ι '' Set.range P'.map)) :
    ∃ x : NormalizedCubicalChain Z R m,
      cubicalChainModuleDifferential Z H R (cubicalChainModuleLof Z H R m x) ∈
          cubicalChainModuleSupportedIn H R ((e.symm : C(P.fst, Z)) '' Set.range P.map) ∧
        ∃ c : NormalizedCubicalChain Y R (m + 1), c ∈ supportedIn R (Set.range ι) (m + 1) ∧
          y - map R Φ m x - boundary Y R m c ∈ supportedIn R (ι '' Set.range P'.map) m := by
  obtain ⟨hsurj, -⟩ := (TopPair.quasiIsoAt_cubicalChainComplexMap_iff R f
    (ChainComplex.next_nat m)).1 ‹_›
  rw [← range_map_eq_supportedIn_range R hι.isInducing] at hy
  obtain ⟨y, rfl⟩ := hy
  obtain ⟨x, hx, c, hc⟩ := hsurj ((normalizedCubicalChainComplexXEquiv P'.fst m).symm y)
    ((d_mem_range_map_f_iff H P' hι _).2 (by rwa [LinearEquiv.apply_symm_apply]))
  refine ⟨map R (e.symm : C(P.fst, Z)) m (normalizedCubicalChainComplexXEquiv P.fst m x),
    (d_mem_range_map_f_iff H P e.symm.isEmbedding x).1 hx,
    map R ι (m + 1) (normalizedCubicalChainComplexXEquiv P'.fst (m + 1) c),
    by rw [← range_map_eq_supportedIn_range R hι.isInducing]; exact LinearMap.mem_range_self _ _,
    ?_⟩
  have hc := (map_mem_supportedIn_image_iff R hι _ _).2
    ((TopPair.mem_range_normalizedCubicalChainComplex_map_f_iff R P' _).1 hc)
  convert hc using 1
  simp only [map_sub, LinearEquiv.apply_symm_apply, normalizedCubicalChainComplexXEquiv_d_apply,
    normalizedCubicalChainComplexXEquiv_map_f_apply, map_map_homeomorph_symm f e Φ hΦ,
    map_boundary_apply]

include hΦ hι in
open NormalizedCubicalChain in
/-- **Injectivity on relative homology, read in `Z` and `Y`.** -/
private theorem exists_sub_boundary_mem_supportedIn {m : ℕ}
    [QuasiIsoAt (TopPair.cubicalChainComplexMap R f) m] (x : NormalizedCubicalChain Z R m)
    (hx : cubicalChainModuleDifferential Z H R (cubicalChainModuleLof Z H R m x) ∈
      cubicalChainModuleSupportedIn H R ((e.symm : C(P.fst, Z)) '' Set.range P.map))
    (c : NormalizedCubicalChain Y R (m + 1)) (hc : c ∈ supportedIn R (Set.range ι) (m + 1))
    (hxc : map R Φ m x - boundary Y R m c ∈ supportedIn R (ι '' Set.range P'.map) m) :
    ∃ a : NormalizedCubicalChain Z R (m + 1),
      x - boundary Z R m a ∈ supportedIn R ((e.symm : C(P.fst, Z)) '' Set.range P.map) m := by
  obtain ⟨-, hinj⟩ := (TopPair.quasiIsoAt_cubicalChainComplexMap_iff R f
    (ChainComplex.next_nat m)).1 ‹_›
  rw [← range_map_eq_supportedIn_range R hι.isInducing] at hc
  obtain ⟨c, rfl⟩ := hc
  -- The chain `x` of `Z`, as a chain of the ambient space of `P`.
  obtain ⟨a, ha⟩ := hinj ((normalizedCubicalChainComplexXEquiv P.fst m).symm (map R e m x))
    ((d_mem_range_map_f_iff H P e.symm.isEmbedding _).2
      (by rwa [LinearEquiv.apply_symm_apply, map_symm_map_apply]))
    ((normalizedCubicalChainComplexXEquiv P'.fst (m + 1)).symm c)
    ((TopPair.mem_range_normalizedCubicalChainComplex_map_f_iff R P' _).2
      ((map_mem_supportedIn_image_iff R hι _ _).1 (by
      convert hxc using 1
      simp only [map_sub, LinearEquiv.apply_symm_apply,
        normalizedCubicalChainComplexXEquiv_d_apply,
        normalizedCubicalChainComplexXEquiv_map_f_apply, map_eq_map_map f e Φ hΦ,
        map_boundary_apply])))
  refine ⟨map R (e.symm : C(P.fst, Z)) (m + 1)
    (normalizedCubicalChainComplexXEquiv P.fst (m + 1) a), ?_⟩
  have ha := (map_mem_supportedIn_image_iff R (ι := (e.symm : C(P.fst, Z))) e.symm.isEmbedding _
    _).2 ((TopPair.mem_range_normalizedCubicalChainComplex_map_f_iff R P _).1 ha)
  convert ha using 1
  simp only [map_sub, LinearEquiv.apply_symm_apply, map_symm_map_apply,
    normalizedCubicalChainComplexXEquiv_d_apply, map_boundary_apply]

include hΦ hι in
open NormalizedCubicalChain in
/-- The map `Φ` takes values in the range of `ι`. -/
private theorem map_mem_supportedIn_range {m : ℕ} (a : NormalizedCubicalChain Z R m) :
    map R Φ m a ∈ supportedIn R (Set.range ι) m := by
  rw [map_eq_map_map f e Φ hΦ, ← range_map_eq_supportedIn_range R hι.isInducing]
  exact LinearMap.mem_range_self _ _

include hΦ in
open NormalizedCubicalChain in
/-- The map `Φ` sends chains of `e⁻¹(A)` to chains of `ι(A')`, since `f` is a map of pairs. -/
private theorem map_mem_supportedIn_image {m : ℕ} {a : NormalizedCubicalChain Z R m}
    (ha : a ∈ supportedIn R ((e.symm : C(P.fst, Z)) '' Set.range P.map) m) :
    map R Φ m a ∈ supportedIn R (ι '' Set.range P'.map) m := by
  refine map_mem_supportedIn R ?_ ha
  rintro _ ⟨_, ⟨z, rfl⟩, rfl⟩
  refine ⟨P'.map (TopPair.Hom.snd f z), ⟨_, rfl⟩, ?_⟩
  rw [hΦ, ContinuousMap.coe_ofClass, Homeomorph.apply_symm_apply, ← ConcreteCategory.comp_apply,
    TopPair.Hom.w, ConcreteCategory.comp_apply]

include hΦ hι in
open NormalizedCubicalChain in
/-- **Relative cycles are relative boundaries, for chains of dimensions `m` and `m + 1`.** This
combines injectivity on relative homology in dimension `m` with surjectivity in dimension
`m + 1`. -/
private theorem exists_of_lof {m : ℕ} [QuasiIsoAt (TopPair.cubicalChainComplexMap R f) m]
    [QuasiIsoAt (TopPair.cubicalChainComplexMap R f) (m + 1)] (x : NormalizedCubicalChain Z R m)
    (y : NormalizedCubicalChain Y R (m + 1))
    (hx : cubicalChainModuleDifferential Z H R (cubicalChainModuleLof Z H R m x) ∈
      cubicalChainModuleSupportedIn H R ((e.symm : C(P.fst, Z)) '' Set.range P.map))
    (hy : cubicalChainModuleLof Y H R (m + 1) y ∈ cubicalChainModuleSupportedIn H R (Set.range ι))
    (hxy : cubicalChainModuleLinearMap R Φ (cubicalChainModuleLof Z H R m x) -
        cubicalChainModuleDifferential Y H R (cubicalChainModuleLof Y H R (m + 1) y) ∈
      cubicalChainModuleSupportedIn H R (ι '' Set.range P'.map)) :
    ∃ (u : cubicalChainModule Z H R) (v : cubicalChainModule Y H R),
      v ∈ cubicalChainModuleSupportedIn H R (Set.range ι) ∧
        cubicalChainModuleDifferential Z H R u - cubicalChainModuleLof Z H R m x ∈
          cubicalChainModuleSupportedIn H R ((e.symm : C(P.fst, Z)) '' Set.range P.map) ∧
        cubicalChainModuleLinearMap R Φ u + cubicalChainModuleDifferential Y H R v -
            cubicalChainModuleLof Y H R (m + 1) y ∈
          cubicalChainModuleSupportedIn H R (ι '' Set.range P'.map) := by
  rw [cubicalChainModuleLof_mem_cubicalChainModuleSupportedIn_iff] at hy
  rw [cubicalChainModuleLinearMap_lof, cubicalChainModuleDifferential_lof_succ, ← map_sub,
    cubicalChainModuleLof_mem_cubicalChainModuleSupportedIn_iff] at hxy
  -- Injectivity in dimension `m` bounds `x` modulo the subspace.
  obtain ⟨a, ha⟩ := exists_sub_boundary_mem_supportedIn H f e hι Φ hΦ x hx y hy hxy
  -- Then `y - Φ a` is a relative cycle, which surjectivity in dimension `m + 1` realizes.
  obtain ⟨x₁, hx₁, c, hc, hyc⟩ := exists_sub_sub_mem_supportedIn H f e hι Φ hΦ
    (y - map R Φ (m + 1) a) (sub_mem hy (map_mem_supportedIn_range f e hι Φ hΦ a)) (by
      rw [cubicalChainModuleDifferential_lof_succ,
        cubicalChainModuleLof_mem_cubicalChainModuleSupportedIn_iff, map_sub,
        ← map_boundary_apply]
      convert sub_mem (map_mem_supportedIn_image f e Φ hΦ ha) hxy using 1
      rw [map_sub]
      abel)
  refine ⟨cubicalChainModuleLof Z H R (m + 1) (a + x₁), cubicalChainModuleLof Y H R (m + 2) c,
    cubicalChainModuleLof_mem_cubicalChainModuleSupportedIn hc, ?_, ?_⟩
  · rw [map_add, map_add, cubicalChainModuleDifferential_lof_succ]
    convert add_mem (neg_mem (cubicalChainModuleLof_mem_cubicalChainModuleSupportedIn ha)) hx₁
      using 1
    rw [map_sub]
    abel
  · rw [cubicalChainModuleLinearMap_lof, cubicalChainModuleDifferential_lof_succ, ← map_add,
      ← map_sub, cubicalChainModuleLof_mem_cubicalChainModuleSupportedIn_iff]
    convert neg_mem hyc using 1
    rw [map_add]
    abel

include hΦ hι in
open NormalizedCubicalChain in
/-- **Relative cycles are relative boundaries, in dimension `0`.** Every chain of dimension `0` is
a relative cycle; surjectivity on relative homology in dimension `0` realizes it. -/
private theorem exists_of_lof_zero [QuasiIsoAt (TopPair.cubicalChainComplexMap R f) 0]
    (y : NormalizedCubicalChain Y R 0)
    (hy : cubicalChainModuleLof Y H R 0 y ∈ cubicalChainModuleSupportedIn H R (Set.range ι)) :
    ∃ (u : cubicalChainModule Z H R) (v : cubicalChainModule Y H R),
      v ∈ cubicalChainModuleSupportedIn H R (Set.range ι) ∧
        cubicalChainModuleDifferential Z H R u - 0 ∈
          cubicalChainModuleSupportedIn H R ((e.symm : C(P.fst, Z)) '' Set.range P.map) ∧
        cubicalChainModuleLinearMap R Φ u + cubicalChainModuleDifferential Y H R v -
            cubicalChainModuleLof Y H R 0 y ∈
          cubicalChainModuleSupportedIn H R (ι '' Set.range P'.map) := by
  rw [cubicalChainModuleLof_mem_cubicalChainModuleSupportedIn_iff] at hy
  obtain ⟨x, -, c, hc, hyc⟩ := exists_sub_sub_mem_supportedIn H f e hι Φ hΦ y hy (by
    rw [cubicalChainModuleDifferential_lof_zero]
    exact zero_mem _)
  refine ⟨cubicalChainModuleLof Z H R 0 x, cubicalChainModuleLof Y H R 1 c,
    cubicalChainModuleLof_mem_cubicalChainModuleSupportedIn hc, ?_, ?_⟩
  · rw [cubicalChainModuleDifferential_lof_zero, sub_zero]
    exact zero_mem _
  · rw [cubicalChainModuleLinearMap_lof, cubicalChainModuleDifferential_lof_succ, ← map_add,
      ← map_sub, cubicalChainModuleLof_mem_cubicalChainModuleSupportedIn_iff]
    convert neg_mem hyc using 1
    abel

include hΦ hι in
/-- **Quasi-isomorphisms of relative chains, read on chains of other spaces.** If a map of pairs
`f : P ⟶ P'` induces a quasi-isomorphism of relative normalized cubical chains, then relative cycles
are relative boundaries, for all chains of `Z` and `Y`: if `x` is a chain of `Z` whose boundary is
supported in the preimage `A` of the subspace of `P`, and `y` a chain of `Y` supported in the range
`T` of `ι` such that `Φ x - ∂y` is supported in the image `S` of the subspace of `P'`, then `x` is
the boundary of a chain `u` modulo `A`, and `y` is `Φ u` plus the boundary of a chain `v` supported
in `T`, modulo `S`. -/
theorem exists_add_differential_sub_mem_cubicalChainModuleSupportedIn_of_quasiIso
    [QuasiIso (TopPair.cubicalChainComplexMap R f)]
    {A : Set Z} {S T : Set Y} (hA : (e.symm : C(P.fst, Z)) '' Set.range P.map = A)
    (hT : Set.range ι = T) (hS : ι '' Set.range P'.map = S)
    {x : cubicalChainModule Z H R} {y : cubicalChainModule Y H R}
    (hx : cubicalChainModuleDifferential Z H R x ∈ cubicalChainModuleSupportedIn H R A)
    (hy : y ∈ cubicalChainModuleSupportedIn H R T)
    (hxy : cubicalChainModuleLinearMap R Φ x - cubicalChainModuleDifferential Y H R y ∈
      cubicalChainModuleSupportedIn H R S) :
    ∃ (u : cubicalChainModule Z H R) (v : cubicalChainModule Y H R),
      v ∈ cubicalChainModuleSupportedIn H R T ∧
        cubicalChainModuleDifferential Z H R u - x ∈ cubicalChainModuleSupportedIn H R A ∧
        cubicalChainModuleLinearMap R Φ u + cubicalChainModuleDifferential Y H R v - y ∈
          cubicalChainModuleSupportedIn H R S := by
  subst hA hT hS
  refine exists_relative_boundary_of_forall_homogeneous
    (cubicalChainModuleDifferential_isHomogeneous Z H R)
    (cubicalChainModuleDifferential_isHomogeneous Y H R)
    (LinearMap.isHomogeneous_def.mpr fun _ _ hx ↦ by
      rw [add_zero]
      exact cubicalChainModuleLinearMap_mem Φ hx)
    (isHomogeneous_cubicalChainModuleSupportedIn _) (isHomogeneous_cubicalChainModuleSupportedIn _)
    (isHomogeneous_cubicalChainModuleSupportedIn _) (fun i x hx y hy hdx hyT hxy ↦ ?_) hx hy hxy
  rcases le_or_gt i 0 with hi | hi
  · obtain ⟨x, rfl⟩ := exists_cubicalChainModuleLof_eq hx (-i).toNat (by omega)
    obtain ⟨y, rfl⟩ := exists_cubicalChainModuleLof_eq hy ((-i).toNat + 1) (by omega)
    exact exists_of_lof H f e hι Φ hΦ x y hdx hyT hxy
  · obtain rfl := eq_zero_of_mem_cubicalChainModuleGrading hx hi
    rcases eq_or_lt_of_le (show 1 ≤ i by omega) with rfl | hi₁
    · obtain ⟨y, rfl⟩ := exists_cubicalChainModuleLof_eq hy 0 (by omega)
      exact exists_of_lof_zero H f e hι Φ hΦ y hyT
    · obtain rfl := eq_zero_of_mem_cubicalChainModuleGrading hy (by omega)
      exact ⟨0, 0, zero_mem _, by simp, by simp⟩

end QuasiIsoAt

end TauCeti
