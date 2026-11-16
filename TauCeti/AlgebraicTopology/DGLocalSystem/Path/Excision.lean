/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.DGLocalSystem.Path.Skeleton
public import TauCeti.AlgebraicTopology.Singular.Fibration.CubicalCells
public import TauCeti.Topology.PathSpace.Moore.Replacement.Basic

/-!
# The quotients of the skeletal filtration of the chains on the based path space

Let `C ⊆ B` be a relative CW complex with skeleta `Xⁿ = skeletonLT C (n + 1)`, and `b ∈ B`. The
normalized cubical chains `C_*(P_b B; R)` on the Moore paths starting at `b` are filtered by the
chains supported over the preimages of the skeleta under the end point map
(`TauCeti.pathFromChainSkeleton`). This file computes the quotients of consecutive stages cell by
cell. Let `P` be the pullback of the end point map along the characteristic maps of the `n`-cells,
`MoorePathPullback (sigmaCellMap C n) b`, and `∂P` its part over their boundary spheres. Pushing
chains forward along `P → P_b B` is a quasi-isomorphism from the relative chains `C_*(P, ∂P)` onto
the quotient of the `n`-th stage by the `(n - 1)`-th
(`TauCeti.exists_add_differential_sub_mem_pathFromChainSkeleton`).

The statement is written on chains, as for `TauCeti.DGRightModuleHom.isQuasiIso_iff_forall_exists`:
every relative cycle is a relative boundary. A relative cycle is a pair `(x, y)` of a chain `x` of
`P` whose boundary lies over the spheres and a chain `y` of the `n`-th stage with
`x - ∂y` in the `(n - 1)`-th stage; it is a relative boundary when it is `(∂u, u + ∂v)`, with `v` in
the `n`-th stage, modulo the chains over the spheres and the `(n - 1)`-th stage. This is the form in
which a quotient of the filtration is compared with free generators attached over the cells in
`TauCeti.RowFiniteTwistingCocycle.exists_attach_of_forall_exists`, in Brown's construction of a
semi-free model of `C_*(P_b B; R)` over the chains on the loop space, one skeleton at a time.

The end point map of the based path space is a Hurewicz fibration
(`TauCeti.MoorePathFrom.isHurewiczFibration_endpoint`), so the projection of relative cubical
chain complexes `N(P, ∂P) ⟶ N(p⁻¹(Xⁿ), p⁻¹(Xⁿ⁻¹))` is a quasi-isomorphism
(`TauCeti.TopCat.quasiIso_cubicalChainComplexMap_cellPullbackPairMap`). The proof reads this
quasi-isomorphism on chains: `TopPair.quasiIsoAt_cubicalChainComplexMap_iff` states it on chains of
the ambient spaces in each dimension, and the chains of `p⁻¹(Xⁿ)` and `p⁻¹(Xⁿ⁻¹)` are the chains of
`P_b B` supported in them. Injectivity on relative homology in dimension `m` and surjectivity in
dimension `m + 1` together bound the relative cycles of dimensions `m` and `m + 1`, and the
statement for all chains follows by splitting them into homogeneous components.

## Main results

* `TauCeti.exists_add_differential_sub_mem_pathFromChainSkeleton`: the push-forward from the
  pullback to the `n`-cells, relative to the boundary spheres, is a quasi-isomorphism onto the
  quotient of the `n`-th stage of the skeletal filtration of `C_*(P_b B; R)` by the `(n - 1)`-th.

## References

* E. H. Brown, *Twisted tensor products, I*, Ann. of Math. (2) 69 (1959), 223–246.
* J.-P. Serre, *Homologie singulière des espaces fibrés. Applications*, Ann. of Math. 54 (1951),
  425–505, Chapter II.
* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Morse homology with differential graded
  coefficients*, Progress in Mathematics 360, Birkhäuser, 2025, Chapters 3--4 and §7.1.
-/

public section

noncomputable section

open CategoryTheory Limits Metric Set Topology Topology.RelCWComplex

namespace TauCeti

universe u

variable {R : Type u} [CommRing R]

/-! ### Splitting relative cycles into homogeneous components -/

open _root_.DirectSum in
/-- **Relative cycles are relative boundaries once homogeneous ones are.** For maps of graded
modules `Φ : M → N`, of degree `0`, and differentials `dM`, `dN` of degree `1`, and homogeneous
submodules `A` of `M` and `S`, `T` of `N`: if every homogeneous pair `(x, y)` with `dM x ∈ A`,
`y ∈ T` and `Φ x - dN y ∈ S` is `(dM u, Φ u + dN v)` modulo `A` and `S`, with `v ∈ T`, then so is
every pair. -/
private theorem exists_of_forall_homogeneous {M N : Type*} [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] {𝒢 : ℤ → Submodule R M} {𝒩 : ℤ → Submodule R N}
    [_root_.DirectSum.Decomposition 𝒢] [_root_.DirectSum.Decomposition 𝒩] {dM : M →ₗ[R] M}
    {dN : N →ₗ[R] N} {Φ : M →ₗ[R] N}
    (hdM : LinearMap.IsHomogeneous dM 𝒢 𝒢 1) (hdN : LinearMap.IsHomogeneous dN 𝒩 𝒩 1)
    (hΦ : LinearMap.IsHomogeneous Φ 𝒢 𝒩 0) {A : Submodule R M} {S T : Submodule R N}
    (hA : A.IsHomogeneous 𝒢) (hS : S.IsHomogeneous 𝒩) (hT : T.IsHomogeneous 𝒩)
    (H : ∀ i, ∀ x ∈ 𝒢 i, ∀ y ∈ 𝒩 (i - 1), dM x ∈ A → y ∈ T → Φ x - dN y ∈ S →
      ∃ u v, v ∈ T ∧ dM u - x ∈ A ∧ Φ u + dN v - y ∈ S)
    {x : M} {y : N} (hx : dM x ∈ A) (hy : y ∈ T) (hxy : Φ x - dN y ∈ S) :
    ∃ u v, v ∈ T ∧ dM u - x ∈ A ∧ Φ u + dN v - y ∈ S := by
  classical
  -- The pair `(x, y)` splits into the homogeneous pairs `(xᵢ, yᵢ₋₁)`.
  have key (i : ℤ) : ∃ u v, v ∈ T ∧ dM u - (decompose 𝒢 x i : M) ∈ A ∧
      Φ u + dN v - (decompose 𝒩 y (i - 1) : N) ∈ S := by
    refine H i _ (SetLike.coe_mem _) _ (SetLike.coe_mem _) ?_
      ((Submodule.IsHomogeneous.mem_iff 𝒩 hT).1 hy _) ?_
    · rw [hdM.map_decompose]
      exact (Submodule.IsHomogeneous.mem_iff 𝒢 hA).1 hx _
    · rw [hΦ.map_decompose, hdN.map_decompose, add_zero, sub_add_cancel, ← Submodule.coe_sub,
        ← DirectSum.sub_apply, ← decompose_sub]
      exact (Submodule.IsHomogeneous.mem_iff 𝒩 hS).1 hxy _
  choose u v hv hu huv using key
  let F : Finset ℤ := (decompose 𝒢 x).support ∪ (decompose 𝒩 y).support.image (· + 1)
  have hx' : ∑ i ∈ F, (decompose 𝒢 x i : M) = x := by
    rw [← Finset.sum_subset Finset.subset_union_left fun i _ hi ↦ by
      rw [DFinsupp.notMem_support_iff.1 hi, ZeroMemClass.coe_zero]]
    exact sum_support_decompose 𝒢 x
  have hy' : ∑ i ∈ F, (decompose 𝒩 y (i - 1) : N) = y := by
    rw [← Finset.sum_subset Finset.subset_union_right fun i _ hi ↦ by
        rw [DFinsupp.notMem_support_iff.1 fun h ↦
          hi (Finset.mem_image.2 ⟨_, h, sub_add_cancel i 1⟩), ZeroMemClass.coe_zero],
      Finset.sum_image fun _ _ _ _ h ↦ add_right_cancel h]
    exact (Finset.sum_congr rfl fun i _ ↦ by rw [add_sub_cancel_right]).trans
      (sum_support_decompose 𝒩 y)
  refine ⟨∑ i ∈ F, u i, ∑ i ∈ F, v i, sum_mem fun i _ ↦ hv i, ?_, ?_⟩
  · rw [map_sum, ← hx', ← Finset.sum_sub_distrib]
    exact sum_mem fun i _ ↦ hu i
  · rw [map_sum, map_sum, ← Finset.sum_add_distrib, ← hy', ← Finset.sum_sub_distrib]
    exact sum_mem fun i _ ↦ huv i

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
      cubicalChainModuleLof_mem_cubicalChainModuleSupportedIn_iff, ← LinearMap.comp_apply,
      ← map_boundary, LinearMap.comp_apply, map_mem_supportedIn_image_iff R hι]

/-- A homogeneous element of `cubicalChainModule` of degree `-m` is a chain of dimension `m`. -/
private theorem exists_cubicalChainModuleLof_eq {Y : Type*} [TopologicalSpace Y] {i : ℤ}
    {x : cubicalChainModule Y H R} (hx : x ∈ cubicalChainModuleGrading Y H R i) (m : ℕ)
    (hm : (m : ℤ) = -i) : ∃ c, cubicalChainModuleLof Y H R m c = x := by
  rcases mem_cubicalChainModuleGrading_iff.1 hx with rfl | ⟨n, c, hn, rfl⟩
  · exact ⟨0, map_zero _⟩
  · obtain rfl : n = m := by omega
    exact ⟨c, rfl⟩

/-- `cubicalChainModule` vanishes in positive degrees. -/
private theorem eq_zero_of_mem_cubicalChainModuleGrading {Y : Type*} [TopologicalSpace Y]
    {i : ℤ} {x : cubicalChainModule Y H R} (hx : x ∈ cubicalChainModuleGrading Y H R i)
    (hi : 0 < i) : x = 0 := by
  rcases mem_cubicalChainModuleGrading_iff.1 hx with rfl | ⟨n, c, hn, rfl⟩
  · rfl
  · omega

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
  rw [← LinearMap.comp_apply, ← NormalizedCubicalChain.map_comp, h,
    NormalizedCubicalChain.map_comp, LinearMap.comp_apply]

include hΦ in
/-- The map `Φ` on chains, through the ambient spaces of the pairs. -/
private theorem map_eq_map_map (m : ℕ) (a : NormalizedCubicalChain Z R m) :
    NormalizedCubicalChain.map R Φ m a = NormalizedCubicalChain.map R ι m
      (NormalizedCubicalChain.map R (TopPair.Hom.fst f).hom m
        (NormalizedCubicalChain.map R (e : C(Z, P.fst)) m a)) := by
  have h : NormalizedCubicalChain.map R (e.symm : C(P.fst, Z)) m
      (NormalizedCubicalChain.map R (e : C(Z, P.fst)) m a) = a := by
    rw [← LinearMap.comp_apply, ← NormalizedCubicalChain.map_comp]
    simp
  rw [← map_map_homeomorph_symm f e Φ hΦ, h]

private theorem next_eq_sub_one (m : ℕ) : (ComplexShape.down ℕ).next m = m - 1 := by
  cases m with
  | zero => exact ChainComplex.next_nat_zero
  | succ k => exact ChainComplex.next_nat_succ k

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
    (next_eq_sub_one m)).1 ‹_›
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
  rw [map_map_homeomorph_symm f e Φ hΦ, ← LinearMap.comp_apply (boundary Y R m),
    ← map_boundary, LinearMap.comp_apply, ← normalizedCubicalChainComplexXEquiv_d_apply,
    ← normalizedCubicalChainComplexXEquiv_map_f_apply, map_sub, map_sub, map_sub, map_sub,
    LinearEquiv.apply_symm_apply]

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
    (next_eq_sub_one m)).1 ‹_›
  rw [← range_map_eq_supportedIn_range R hι.isInducing] at hc
  obtain ⟨c, rfl⟩ := hc
  -- The chain `x` of `Z`, as a chain of the ambient space of `P`.
  have hx' : map R (e.symm : C(P.fst, Z)) m (map R (e : C(Z, P.fst)) m x) = x := by
    rw [← LinearMap.comp_apply, ← map_comp]
    simp
  obtain ⟨a, ha⟩ := hinj ((normalizedCubicalChainComplexXEquiv P.fst m).symm (map R e m x))
    ((d_mem_range_map_f_iff H P e.symm.isEmbedding _).2
      (by rwa [LinearEquiv.apply_symm_apply, hx']))
    ((normalizedCubicalChainComplexXEquiv P'.fst (m + 1)).symm c)
    ((TopPair.mem_range_normalizedCubicalChainComplex_map_f_iff R P' _).2
      ((map_mem_supportedIn_image_iff R hι _ _).1 (by
      convert hxc using 1
      rw [map_sub, normalizedCubicalChainComplexXEquiv_map_f_apply,
        normalizedCubicalChainComplexXEquiv_d_apply, LinearEquiv.apply_symm_apply,
        LinearEquiv.apply_symm_apply, map_sub, map_eq_map_map f e Φ hΦ,
        ← LinearMap.comp_apply (boundary Y R m),
        ← map_boundary, LinearMap.comp_apply])))
  refine ⟨map R (e.symm : C(P.fst, Z)) (m + 1)
    (normalizedCubicalChainComplexXEquiv P.fst (m + 1) a), ?_⟩
  have ha := (map_mem_supportedIn_image_iff R (ι := (e.symm : C(P.fst, Z))) e.symm.isEmbedding _
    _).2 ((TopPair.mem_range_normalizedCubicalChainComplex_map_f_iff R P _).1 ha)
  convert ha using 1
  rw [map_sub, map_sub, LinearEquiv.apply_symm_apply, hx',
    normalizedCubicalChainComplexXEquiv_d_apply, ← LinearMap.comp_apply, ← map_boundary,
    LinearMap.comp_apply]

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
        ← LinearMap.comp_apply (boundary Y R m), ← map_boundary, LinearMap.comp_apply]
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
/-- **Relative cycles are relative boundaries**, for all chains: the form taken by a
quasi-isomorphism of relative chains, read on the chains of `Z` and `Y`. -/
private theorem exists_of_quasiIso [QuasiIso (TopPair.cubicalChainComplexMap R f)]
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
  refine exists_of_forall_homogeneous (cubicalChainModuleDifferential_isHomogeneous Z H R)
    (cubicalChainModuleDifferential_isHomogeneous Y H R)
    (LinearMap.isHomogeneous_def.mpr fun _ _ hx ↦ by
      rw [add_zero]
      exact cubicalChainModuleLinearMap_mem Φ hx)
    (isHomogeneous_cubicalChainModuleSupportedIn _) (isHomogeneous_cubicalChainModuleSupportedIn _)
    (isHomogeneous_cubicalChainModuleSupportedIn _) (fun i x hx y hy hdx hyT hxy ↦ ?_) hx hy hxy
  rcases le_or_gt i 0 with hi | hi
  · obtain ⟨x, rfl⟩ := exists_cubicalChainModuleLof_eq H hx (-i).toNat (by omega)
    obtain ⟨y, rfl⟩ := exists_cubicalChainModuleLof_eq H hy ((-i).toNat + 1) (by omega)
    exact exists_of_lof H f e hι Φ hΦ x y hdx hyT hxy
  · obtain rfl := eq_zero_of_mem_cubicalChainModuleGrading H hx hi
    rcases eq_or_lt_of_le (show 1 ≤ i by omega) with rfl | hi₁
    · obtain ⟨y, rfl⟩ := exists_cubicalChainModuleLof_eq H hy 0 (by omega)
      exact exists_of_lof_zero H f e hι Φ hΦ y hyT
    · obtain rfl := eq_zero_of_mem_cubicalChainModuleGrading H hy (by omega)
      exact ⟨0, 0, zero_mem _, by simp, by simp⟩

end QuasiIsoAt

/-! ### The based path fibration over the cells -/

variable {B : Type u} [TopologicalSpace B] [T2Space B] {b : B} {C D : Set B} [RelCWComplex C D]

/-- The based path fibration `P_b B → B`, as a morphism of topological spaces. -/
private abbrev pathFromEndpoint (B : Type u) [TopologicalSpace B] (b : B) :
    _root_.TopCat.of (MoorePathFrom B b) ⟶ _root_.TopCat.of B :=
  _root_.TopCat.ofHom (MoorePathFrom.endpoint B b)

variable (b C) in
/-- The pullback of the based path fibration to the disks of the `n`-cells, as the pullback
`TauCeti.TopCat.cellPullback` of a map in `TopCat`. -/
private def cellPullbackHomeomorph (n : ℕ) :
    MoorePathPullback (sigmaCellMap C n) b ≃ₜ TopCat.cellPullback (pathFromEndpoint B b) C n :=
  Homeomorph.subtype (Homeomorph.refl _) fun _ ↦ by
    simp [MoorePathFrom.endpoint_apply, eq_comm]

variable (b C) in
/-- The preimage of `Xⁿ` is the `n`-th stage of the skeletal filtration. -/
private theorem preimage_skeletonLT_succ_eq (n : ℕ) :
    (pathFromEndpoint B b) ⁻¹' (skeletonLT C ((n + 1 : ℕ) : ℕ∞)) =
      preimageSkeleton C (MoorePathFrom.endpoint B b) n := by
  ext x
  simp [MoorePathFrom.endpoint_apply]

variable (b C) in
/-- The preimage of `Xⁿ⁻¹` is the `(n - 1)`-th stage of the skeletal filtration. -/
private theorem preimage_skeletonLT_eq (n : ℕ) :
    (pathFromEndpoint B b) ⁻¹' (skeletonLT C n) =
      preimageSkeleton C (MoorePathFrom.endpoint B b) (n - 1) := by
  ext x
  simp [MoorePathFrom.endpoint_apply]

variable (b C) in
/-- The projection of the pullback to the `n`-cells to `P_b B` is the projection to the preimage
of `Xⁿ`, followed by the inclusion. -/
private theorem toMoorePathFrom_eq (n : ℕ) (z : MoorePathPullback (sigmaCellMap C n) b) :
    MoorePathPullback.toMoorePathFrom z = ContinuousMap.subtypeVal _
      (TopPair.Hom.fst (TopCat.cellPullbackPairMap (pathFromEndpoint B b) C n)
        (cellPullbackHomeomorph b C n z)) := by
  obtain ⟨⟨d, γ⟩, h⟩ := z
  refine MoorePathFrom.ext ?_
  rw [MoorePathPullback.toMoorePathFrom_toMoorePath, MoorePathPullback.path_mk]
  exact (congrArg MoorePathFrom.toMoorePath
    (TopCat.coe_cellPullbackPairMap_fst_apply n (cellPullbackHomeomorph b C n ⟨(d, γ), h⟩))).symm

omit [T2Space B] in
variable (b C) in
/-- The part of the pullback over the boundary spheres. -/
private theorem image_symm_range_cellPullbackPair_map (n : ℕ) :
    ((cellPullbackHomeomorph b C n).symm : C(TopCat.cellPullback (pathFromEndpoint B b) C n,
        MoorePathPullback (sigmaCellMap C n) b)) ''
        Set.range (TopCat.cellPullbackPair (pathFromEndpoint B b) C n).map =
      MoorePathPullback.proj (sigmaCellMap C n) b ⁻¹' {q | ‖(q.2 : Fin n → ℝ)‖ = 1} := by
  ext ⟨⟨d, γ⟩, h⟩
  rw [Set.mem_preimage, MoorePathPullback.proj_apply, MoorePathPullback.point_mk,
    Set.mem_ofPred_eq]
  refine ⟨?_, fun hd ↦ ⟨_, ⟨⟨cellPullbackHomeomorph b C n ⟨(d, γ), h⟩, hd⟩, rfl⟩, rfl⟩⟩
  rintro ⟨_, ⟨v, rfl⟩, hv⟩
  have hd : v.1.1.1 = d := congrArg (fun z ↦ z.1.1) hv
  rw [← hd]
  exact v.2

variable (b C) in
/-- The preimage of `Xⁿ⁻¹`, as a subset of `P_b B`. -/
private theorem image_range_preimageSkeletonPair_map (n : ℕ) :
    ContinuousMap.subtypeVal ((pathFromEndpoint B b) ⁻¹' (skeletonLT C ((n + 1 : ℕ) : ℕ∞))) ''
        Set.range (TopCat.preimageSkeletonPair (pathFromEndpoint B b) C n).map =
      preimageSkeleton C (MoorePathFrom.endpoint B b) (n - 1) := by
  refine Set.ext fun γ ↦ ⟨?_, fun hγ ↦ ?_⟩
  · rintro ⟨_, ⟨w, rfl⟩, rfl⟩
    rw [← preimage_skeletonLT_eq]
    exact w.2
  · rw [← preimage_skeletonLT_eq] at hγ
    exact ⟨_, ⟨⟨γ, hγ⟩, rfl⟩, rfl⟩

variable {H} in
/-- **The quotients of the skeletal filtration of the chains on the based path space are computed
over the cells.** Let `P` be the pullback of the based path fibration `P_b B → B` along the
characteristic maps of the `n`-cells and `∂P` its part over the boundary spheres. Pushing chains
forward along `P → P_b B` is a quasi-isomorphism from the relative chains `C_*(P, ∂P)` onto the
quotient of the `n`-th stage of the skeletal filtration of `C_*(P_b B)` by the `(n - 1)`-th, in the
following form: if `x` is a chain of `P` whose boundary lies over the spheres and `y` a chain of the
`n`-th stage such that the push-forward of `x` minus the boundary of `y` lies in the `(n - 1)`-th
stage, then `x` is the boundary of a chain `u` modulo the chains over the spheres, and `y` is the
push-forward of `u` plus the boundary of a chain `v` of the `n`-th stage modulo the `(n - 1)`-th
stage. -/
theorem exists_add_differential_sub_mem_pathFromChainSkeleton {n : ℕ}
    {x : cubicalChainModule (MoorePathPullback (sigmaCellMap C n) b) H R}
    {y : cubicalChainModule (MoorePathFrom B b) H R}
    (hx : cubicalChainModuleDifferential _ H R x ∈ cubicalChainModuleSupportedIn H R
      (MoorePathPullback.proj (sigmaCellMap C n) b ⁻¹' {q | ‖(q.2 : Fin n → ℝ)‖ = 1}))
    (hy : y ∈ pathFromChainSkeleton b C H R n)
    (hxy : cubicalChainModuleLinearMap R MoorePathPullback.toMoorePathFrom x -
        cubicalChainModuleDifferential _ H R y ∈ pathFromChainSkeleton b C H R (n - 1)) :
    ∃ (u : cubicalChainModule (MoorePathPullback (sigmaCellMap C n) b) H R)
      (v : cubicalChainModule (MoorePathFrom B b) H R),
      v ∈ pathFromChainSkeleton b C H R n ∧
        cubicalChainModuleDifferential _ H R u - x ∈ cubicalChainModuleSupportedIn H R
          (MoorePathPullback.proj (sigmaCellMap C n) b ⁻¹' {q | ‖(q.2 : Fin n → ℝ)‖ = 1}) ∧
        cubicalChainModuleLinearMap R MoorePathPullback.toMoorePathFrom u +
            cubicalChainModuleDifferential _ H R v - y ∈ pathFromChainSkeleton b C H R (n - 1) := by
  have := TopCat.quasiIso_cubicalChainComplexMap_cellPullbackPairMap (C := C)
    (IsHurewiczFibration.mem_serreFibrations (p := pathFromEndpoint B b)
      (MoorePathFrom.isHurewiczFibration_endpoint.{0} B b)) R n
  simp only [mem_pathFromChainSkeleton] at hy hxy ⊢
  exact exists_of_quasiIso H (TopCat.cellPullbackPairMap (pathFromEndpoint B b) C n)
    (Y := MoorePathFrom B b) (cellPullbackHomeomorph b C n)
    (ι := ContinuousMap.subtypeVal ((pathFromEndpoint B b) ⁻¹' (skeletonLT C ((n + 1 : ℕ) : ℕ∞))))
    IsEmbedding.subtypeVal _ (toMoorePathFrom_eq b C n)
    (image_symm_range_cellPullbackPair_map b C n)
    (Subtype.range_coe.trans (preimage_skeletonLT_succ_eq b C n))
    (image_range_preimageSkeletonPair_map b C n) hx hy hxy

end TauCeti
