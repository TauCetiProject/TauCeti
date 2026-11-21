/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.RootSystem.Component.Base
public import TauCeti.LinearAlgebra.RootSystem.InvariantForm.Hom
public import TauCeti.LinearAlgebra.RootSystem.OrbitSum.Basic

import TauCeti.LinearAlgebra.FixedSubmodule

/-!
# Component cycles of a root-pairing automorphism and their return maps

An automorphism `σ` of a finite root system `P` over a field permutes its irreducible components
(`RootPairing.Equiv.componentEquiv`). Let `C` be a component and `c` the length of its cycle
`C, σC, …, σᶜ⁻¹C`, the minimal period of `C`. Then `σᶜ` maps `C` to itself and restricts to an
automorphism `τ` of the component pairing of `C`, the **return map**
`RootPairing.Equiv.componentReturn σ C`. When `σ` permutes the simple roots of a base `b`, so does
`τ` for the base `b.componentBase C` of the component.

The cycle sum `D x = ∑_{r < c} σʳ x` (`RootPairing.Equiv.componentCycleSum`) is the map through
which folding by `σ` is compared with folding the component `C` by its return map. It carries
`τ`-fixed vectors of the component space of `C` to `σ`-fixed vectors, and each `τ`-orbit sum of a
root of `C` to the corresponding `σ`-orbit sum: the `σ`-orbit of a root of `C` is the disjoint union
of the images under `σʳ`, `r < c`, of its `τ`-orbit, which lie in the distinct components `σʳC`.
In particular a `τ`-orbit of size `d` gives a `σ`-orbit of size `c * d`. Projection onto the
component space of `C` is a left inverse of `D` and carries `σ`-fixed vectors to `τ`-fixed vectors;
applied after it, `D` sends a `σ`-fixed vector to the sum of its projections onto the components
of the cycle. Finally `D` multiplies every `σ`-invariant invariant form, for instance the canonical
root form, by `c` on the component space of `C`.

## Main definitions

* `RootPairing.Equiv.restrictComponent`: the restriction of an automorphism mapping a component to
  itself to an automorphism of the component pairing.
* `RootPairing.Equiv.componentReturn`: the return map of a component under an automorphism.
* `RootPairing.Equiv.componentCycleSum`: the sum of the iterates `σʳ`, `r` below the length of the
  cycle of a component.
* `RootPairing.Equiv.componentCycleMap`: the cycle sum as a linear map from the fixed space of the
  return map to the fixed space of `σ`.

## Main results

* `RootPairing.Equiv.componentEquiv_pow`: the components are permuted by a group action.
* `RootPairing.Base.indexEquiv_componentReturn_mem_support`: the return map of an automorphism
  permuting the simple roots of `b` permutes the simple roots of the component base.
* `RootPairing.Equiv.orbitIndices_eq_biUnion`, `RootPairing.Equiv.card_orbitIndices_eq_mul`: the
  `σ`-orbit of a root of `C` is the disjoint union of the `σʳ`-images of its orbit under the return
  map, so its size is `c` times the size of that orbit.
* `RootPairing.Equiv.componentCycleSum_orbitSum`: the cycle sum carries orbit sums of the return
  map to orbit sums of `σ`.
* `RootPairing.Equiv.componentProj_componentCycleSum`,
  `RootPairing.Equiv.componentProj_mem_fixedSubmodule`,
  `RootPairing.Equiv.componentCycleSum_componentProj`: projection onto the component space of `C`
  is a left inverse of the cycle sum, carries `σ`-fixed vectors to vectors fixed by the return map,
  and is followed by the cycle sum to the sum of the projections onto the components of the cycle.
* `RootPairing.Equiv.componentCycleMap_orbitSum`, `RootPairing.Equiv.componentCycleMap_injective`:
  the cycle sum on fixed vectors carries orbit sums to orbit sums and is injective.
* `RootPairing.Equiv.form_componentCycleSum`, `RootPairing.Equiv.rootForm_componentCycleSum`: the
  cycle sum multiplies a `σ`-invariant invariant form by the length of the cycle.

## References

* J. R. Stembridge, *Folding by automorphisms*, note of 20 August 2008, p. 1.
* N. Bourbaki, *Lie Groups and Lie Algebras, Chapters 4-6*, Ch. VI §1, no. 2.
-/

public section

namespace RootPairing

open Finset Function

/-! ### Automorphisms permute the components -/

section Action

variable {ι R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  {P : RootPairing ι R M N}

namespace Equiv

/-- The identity automorphism fixes every component. -/
@[simp]
theorem componentEquiv_one : (1 : P.Aut).componentEquiv = 1 :=
  _root_.Equiv.ext fun C ↦ C.ind fun i ↦ componentEquiv_componentOf 1 i

/-- The permutation of the components induced by a product of automorphisms is the product of the
induced permutations. Not a `simp` lemma: `RootPairing.Equiv.mul_eq_comp` rewrites its left-hand
side. -/
theorem componentEquiv_mul (σ τ : P.Aut) :
    (σ * τ).componentEquiv = σ.componentEquiv * τ.componentEquiv :=
  _root_.Equiv.ext fun C ↦ C.ind fun i ↦ by
    rw [Equiv.Perm.mul_apply, componentEquiv_componentOf, componentEquiv_componentOf,
      componentEquiv_componentOf, ← indexHom_apply, map_mul, Equiv.Perm.mul_apply, indexHom_apply,
      indexHom_apply]

/-- **Automorphisms permute the irreducible components by a group action.** -/
@[simp]
theorem componentEquiv_pow (σ : P.Aut) (n : ℕ) :
    (σ ^ n).componentEquiv = σ.componentEquiv ^ n := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ, componentEquiv_mul, ih, pow_succ]

/-- The index permutation of a power of an automorphism is the power of its index permutation. -/
@[simp]
theorem indexEquiv_pow (σ : P.Aut) (n : ℕ) : (σ ^ n).indexEquiv = σ.indexEquiv ^ n := by
  rw [← indexHom_apply, map_pow, indexHom_apply]

/-- The weight map of a product of automorphisms is the composite of their weight maps. -/
theorem weightMap_mul_apply (σ τ : P.Aut) (x : M) :
    (σ * τ).toHom.weightMap x = σ.toHom.weightMap (τ.toHom.weightMap x) :=
  (rfl)

/-- The weight map of a power of an automorphism is the power of its weight map. -/
theorem weightMap_pow (σ : P.Aut) (n : ℕ) : (σ ^ n).toHom.weightMap = σ.toHom.weightMap ^ n := by
  induction n with
  | zero => rfl
  | succ n ih => ext x; rw [pow_succ', weightMap_mul_apply, ih, pow_succ', mul_apply_eq_comp]

/-- An equivalence of root pairings carries the component space of `C` into that of the
corresponding component. -/
theorem weightMap_mem_componentSpace {ι₂ M₂ N₂ : Type*} [AddCommGroup M₂] [Module R M₂]
    [AddCommGroup N₂] [Module R N₂] {Q : RootPairing ι₂ R M₂ N₂} (e : P.Equiv Q)
    {C : P.Component} {x : M} (hx : x ∈ P.componentSpace C) :
    e.toHom.weightMap x ∈ Q.componentSpace (e.componentEquiv C) := by
  rw [← e.map_componentSpace C]
  exact Submodule.mem_map_of_mem hx

/-- An automorphism mapping the component `C` to itself maps a root index into `C` exactly when that
index lies in `C`. -/
theorem indexEquiv_mem_supp_iff_of_componentEquiv_eq {σ : P.Aut} {C : P.Component}
    (hC : σ.componentEquiv C = C) {i : ι} : σ.indexEquiv i ∈ C.supp ↔ i ∈ C.supp := by
  conv_lhs => rw [← hC]
  exact σ.indexEquiv_mem_supp_iff

/-- The power `σᶜ`, for `c` the length of the cycle of `C`, maps `C` to itself. -/
theorem componentEquiv_pow_minimalPeriod (σ : P.Aut) (C : P.Component) :
    (σ ^ minimalPeriod σ.componentEquiv C).componentEquiv C = C := by
  rw [componentEquiv_pow, Equiv.Perm.coe_pow]
  exact isPeriodicPt_minimalPeriod _ _

/-- The cycle of a component has positive length. -/
theorem minimalPeriod_componentEquiv_pos [Finite ι] (σ : P.Aut) (C : P.Component) :
    0 < minimalPeriod σ.componentEquiv C :=
  minimalPeriod_pos_of_mem_periodicPts (σ.componentEquiv.injective.mem_periodicPts C)

/-- The components `σʳC`, `r` below the length of the cycle of `C`, are distinct. -/
theorem componentEquiv_pow_injOn (σ : P.Aut) (C : P.Component) :
    (Set.Iio (minimalPeriod σ.componentEquiv C)).InjOn fun r ↦ (σ ^ r).componentEquiv C := by
  simpa only [componentEquiv_pow, Equiv.Perm.coe_pow] using iterate_injOn_Iio_minimalPeriod

end Equiv

end Action

/-! ### The cycle sum -/

section CycleSum

variable {ι R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  {P : RootPairing ι R M N}

namespace Equiv

variable (σ : P.Aut) (C : P.Component)

/-- The **cycle sum** of the component `C` under `σ`: the linear map `x ↦ ∑_{r < c} σʳ x`, where
`c` is the length of the cycle of `C` under the permutation of the components induced by `σ`. -/
noncomputable def componentCycleSum : M →ₗ[R] M :=
  ∑ r ∈ range (minimalPeriod σ.componentEquiv C), (σ ^ r).toHom.weightMap

theorem componentCycleSum_apply (x : M) :
    σ.componentCycleSum C x =
      ∑ r ∈ range (minimalPeriod σ.componentEquiv C), (σ ^ r).toHom.weightMap x := by
  rw [componentCycleSum, LinearMap.sum_apply]

variable {σ C}

/-- The cycle sum of a vector fixed by `σᶜ` is fixed by `σ`. -/
theorem componentCycleSum_mem_fixedSubmodule {x : M}
    (hx : (σ ^ minimalPeriod σ.componentEquiv C).toHom.weightMap x = x) :
    σ.componentCycleSum C x ∈ LinearMap.fixedSubmodule σ.weightMap := by
  rw [LinearMap.mem_fixedSubmodule_iff, componentCycleSum_apply, map_sum]
  simp_rw [← weightMap_mul_apply, ← pow_succ']
  have h := sum_range_succ' (fun r ↦ (σ ^ r).toHom.weightMap x) (minimalPeriod σ.componentEquiv C)
  rw [sum_range_succ, hx, pow_zero, toHom_one, Hom.weightMap_one, LinearMap.id_apply] at h
  exact (add_right_cancel h).symm

/-- **Projection inverts the cycle sum on the component.** The projection onto the component space
of `C` of the cycle sum of a vector of that component space is the vector itself. -/
theorem componentProj_componentCycleSum [Finite ι] [P.IsRootSystem] {x : M}
    (hx : x ∈ P.componentSpace C) :
    P.componentProj C (σ.componentCycleSum C x) = ⟨x, hx⟩ := by
  rw [componentCycleSum_apply, map_sum,
    Finset.sum_eq_single_of_mem 0 (mem_range.mpr (minimalPeriod_componentEquiv_pos σ C))]
  · simp [componentProj_apply_of_mem hx]
  · intro r hr hr0
    refine componentProj_apply_of_ne (fun h ↦ hr0 ?_) (weightMap_mem_componentSpace _ hx)
    exact componentEquiv_pow_injOn σ C (mem_range.mp hr)
      (minimalPeriod_componentEquiv_pos σ C) (by simpa using h)

/-- **The cycle sum scales invariant forms by the length of the cycle.** For an invariant form `B`
preserved by `σ`, the cycle sums of two vectors of the component space of `C` pair under `B` to
`c` times their pairing, where `c` is the length of the cycle of `C`. -/
theorem form_componentCycleSum [IsDomain R] [NeZero (2 : R)] (B : P.InvariantForm)
    (hB : ∀ x y, B.form (σ.weightMap x) (σ.weightMap y) = B.form x y) {x y : M}
    (hx : x ∈ P.componentSpace C) (hy : y ∈ P.componentSpace C) :
    B.form (σ.componentCycleSum C x) (σ.componentCycleSum C y) =
      minimalPeriod σ.componentEquiv C * B.form x y := by
  have hpow (r : ℕ) : B.form ((σ ^ r).weightMap x) ((σ ^ r).weightMap y) = B.form x y := by
    induction r with
    | zero => rfl
    | succ r ih => rw [pow_succ', weightMap_mul_apply, weightMap_mul_apply, hB, ih]
  simp_rw [componentCycleSum_apply, map_sum, LinearMap.sum_apply]
  trans ∑ _r ∈ range (minimalPeriod σ.componentEquiv C), B.form x y
  · refine sum_congr rfl fun r hr ↦ ?_
    rw [sum_eq_single_of_mem r hr, hpow]
    intro s hs hsr
    refine B.apply_eq_zero_of_mem_componentSpace (fun h ↦ hsr ?_)
      (weightMap_mem_componentSpace _ hx) (weightMap_mem_componentSpace _ hy)
    exact componentEquiv_pow_injOn σ C (mem_range.mp hs) (mem_range.mp hr) h
  · rw [sum_const, card_range, nsmul_eq_mul]

/-- The cycle sums of two vectors of the component space of `C` pair under the canonical root form
to `c` times their pairing, where `c` is the length of the cycle of `C`. -/
theorem rootForm_componentCycleSum [Fintype ι] [IsDomain R] [NeZero (2 : R)] [P.IsAnisotropic]
    {x y : M} (hx : x ∈ P.componentSpace C) (hy : y ∈ P.componentSpace C) :
    P.RootForm (σ.componentCycleSum C x) (σ.componentCycleSum C y) =
      minimalPeriod σ.componentEquiv C * P.RootForm x y :=
  form_componentCycleSum P.toInvariantForm (Hom.rootForm_weightMap σ.toHom) hx hy

end Equiv

end CycleSum

/-! ### Restriction to a stable component -/

variable {ι K M N : Type*} [Field K] [AddCommGroup M] [Module K M] [AddCommGroup N] [Module K N]
  {P : RootPairing ι K M N} [Finite ι] [P.IsRootSystem]

namespace Equiv

/-- The **restriction of an automorphism** `σ` of `P` mapping the component `C` to itself: the
automorphism of the component pairing of `C` given by the restrictions of the weight and coweight
maps of `σ` to the component spaces of `C` and its index permutation on the roots of `C`. -/
noncomputable def restrictComponent (σ : P.Aut) (C : P.Component) (hC : σ.componentEquiv C = C) :
    (P.componentPairing C).Aut where
  weightMap := (σ.weightEquiv.submoduleMap (P.componentSpace C)).trans
    (LinearEquiv.ofEq _ _ ((σ.map_componentSpace C).trans (congrArg P.componentSpace hC)))
  coweightMap := ((σ.coweightEquiv.submoduleMap (P.corootComponentSpace C)).trans
    (LinearEquiv.ofEq _ _ ((congrArg (fun D ↦ (P.corootComponentSpace D).map
      σ.coweightEquiv.toLinearMap) hC.symm).trans (σ.map_corootComponentSpace C)))).toLinearMap
  indexEquiv := Equiv.Perm.subtypePerm σ.indexEquiv fun _ ↦
    indexEquiv_mem_supp_iff_of_componentEquiv_eq hC
  weight_coweight_transpose := by
    ext y x
    simpa using σ.toLinearMap_weightEquiv x.val y.val
  root_weightMap := by
    ext i
    simp [Hom.root_weightMap_apply]
  coroot_coweightMap := by
    ext i
    simp [Hom.coroot_coweightMap_apply, ← Equiv.Perm.inv_def]
  bijective_weightMap := LinearEquiv.bijective _
  bijective_coweightMap := LinearEquiv.bijective _

variable (σ : P.Aut) (C : P.Component)

@[simp]
theorem coe_restrictComponent_weightMap_apply (hC : σ.componentEquiv C = C)
    (x : P.componentSpace C) :
    ((σ.restrictComponent C hC).toHom.weightMap x : M) = σ.toHom.weightMap x :=
  (rfl)

@[simp]
theorem coe_restrictComponent_coweightMap_apply (hC : σ.componentEquiv C = C)
    (y : P.corootComponentSpace C) :
    ((σ.restrictComponent C hC).toHom.coweightMap y : N) = σ.toHom.coweightMap y :=
  (rfl)

@[simp]
theorem coe_restrictComponent_indexEquiv_apply (hC : σ.componentEquiv C = C) (i : C.supp) :
    ((σ.restrictComponent C hC).indexEquiv i : ι) = σ.indexEquiv i :=
  (rfl)

/-- The powers of the index permutation of the restriction are the restrictions of the powers. -/
theorem restrictComponent_indexEquiv_pow (hC : σ.componentEquiv C = C) (n : ℕ) (i : C.supp) :
    (((σ.restrictComponent C hC).indexEquiv ^ n) i : ι) = (σ.indexEquiv ^ n) i := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [pow_succ', Equiv.Perm.mul_apply, coe_restrictComponent_indexEquiv_apply, ih, pow_succ',
      Equiv.Perm.mul_apply]

/-! ### The return map of a component cycle -/

/-- The **return map** of the component `C` under `σ`: the restriction to the component pairing of
`C` of `σᶜ`, where `c` is the length of the cycle of `C` under the permutation of the components
induced by `σ`. -/
noncomputable def componentReturn : (P.componentPairing C).Aut :=
  (σ ^ minimalPeriod σ.componentEquiv C).restrictComponent C (componentEquiv_pow_minimalPeriod σ C)

@[simp]
theorem coe_componentReturn_weightMap_apply (x : P.componentSpace C) :
    ((σ.componentReturn C).toHom.weightMap x : M) =
      (σ ^ minimalPeriod σ.componentEquiv C).toHom.weightMap x :=
  (rfl)

@[simp]
theorem coe_componentReturn_coweightMap_apply (y : P.corootComponentSpace C) :
    ((σ.componentReturn C).toHom.coweightMap y : N) =
      (σ ^ minimalPeriod σ.componentEquiv C).toHom.coweightMap y :=
  (rfl)

@[simp]
theorem coe_componentReturn_indexEquiv_apply (i : C.supp) :
    ((σ.componentReturn C).indexEquiv i : ι) =
      (σ.indexEquiv ^ minimalPeriod σ.componentEquiv C) i := by
  rw [componentReturn, coe_restrictComponent_indexEquiv_apply, indexEquiv_pow]

/-- The `k`-th power of the return map moves a root of `C` by `σᶜᵏ`. -/
theorem coe_componentReturn_indexEquiv_pow_apply (k : ℕ) (i : C.supp) :
    (((σ.componentReturn C).indexEquiv ^ k) i : ι) =
      (σ.indexEquiv ^ (minimalPeriod σ.componentEquiv C * k)) i := by
  rw [componentReturn, restrictComponent_indexEquiv_pow, indexEquiv_pow, pow_mul]

/-- The members of the orbit of a root of `C` under the return map are the iterates `σᶜᵏ` of that
root. -/
theorem mem_orbitIndices_componentReturn_iff {i j : C.supp} :
    j ∈ (P.componentPairing C).orbitIndices (σ.componentReturn C) i ↔
      ∃ k : ℕ, (σ.indexEquiv ^ (minimalPeriod σ.componentEquiv C * k)) i = j := by
  rw [mem_orbitIndices_iff_exists_pow]
  exact exists_congr fun k ↦ by rw [← Subtype.coe_inj, coe_componentReturn_indexEquiv_pow_apply]

/-! ### Orbits and orbit sums along a component cycle -/

/-- The images under `σʳ`, `r` below the length of the cycle of `C`, of the orbit of a root of `C`
under the return map are pairwise disjoint: they lie in the distinct components `σʳC`. -/
theorem pairwiseDisjoint_map_orbitIndices_componentReturn (i : C.supp) :
    (range (minimalPeriod σ.componentEquiv C) : Set ℕ).PairwiseDisjoint fun r ↦
      (((P.componentPairing C).orbitIndices (σ.componentReturn C) i).map
        (Embedding.subtype _)).map (σ ^ r).indexEquiv.toEmbedding := by
  intro r hr s hs hrs
  refine disjoint_left.mpr fun j hjr hjs ↦ hrs ?_
  simp only [mem_map, Embedding.coe_subtype, _root_.Equiv.coe_toEmbedding] at hjr hjs
  obtain ⟨_, ⟨t, -, rfl⟩, rfl⟩ := hjr
  obtain ⟨_, ⟨t', -, rfl⟩, ht'⟩ := hjs
  have hmem {u : C.supp} {n : ℕ} : (σ ^ n).indexEquiv u ∈ ((σ ^ n).componentEquiv C).supp :=
    (σ ^ n).indexEquiv_mem_supp_iff.mpr u.prop
  refine componentEquiv_pow_injOn σ C (mem_range.mp hr) (mem_range.mp hs) ?_
  dsimp only
  rw [← (SimpleGraph.ConnectedComponent.mem_supp_iff _ _).mp (hmem (u := t) (n := r)), ← ht',
    (SimpleGraph.ConnectedComponent.mem_supp_iff _ _).mp (hmem (u := t') (n := s))]

/-- **The `σ`-orbit of a root of `C` is the union of the `σʳ`-images of its orbit under the return
map**, for `r` below the length of the cycle of `C`; the union is disjoint by
`RootPairing.Equiv.pairwiseDisjoint_map_orbitIndices_componentReturn`. -/
theorem orbitIndices_eq_biUnion [DecidableEq ι] (i : C.supp) :
    P.orbitIndices σ i = (range (minimalPeriod σ.componentEquiv C)).biUnion fun r ↦
      (((P.componentPairing C).orbitIndices (σ.componentReturn C) i).map
        (Embedding.subtype _)).map (σ ^ r).indexEquiv.toEmbedding := by
  ext j
  simp only [mem_biUnion, mem_range, mem_map, Embedding.coe_subtype,
    _root_.Equiv.coe_toEmbedding, indexEquiv_pow, mem_orbitIndices_iff_exists_pow]
  constructor
  · rintro ⟨n, rfl⟩
    refine ⟨n % minimalPeriod σ.componentEquiv C,
      Nat.mod_lt _ (minimalPeriod_componentEquiv_pos σ C), _,
      ⟨_, ⟨n / minimalPeriod σ.componentEquiv C, rfl⟩, rfl⟩, ?_⟩
    rw [coe_componentReturn_indexEquiv_pow_apply, ← Equiv.Perm.mul_apply, ← pow_add,
      Nat.mod_add_div]
  · rintro ⟨r, -, _, ⟨_, ⟨k, rfl⟩, rfl⟩, rfl⟩
    exact ⟨r + minimalPeriod σ.componentEquiv C * k, by
      rw [coe_componentReturn_indexEquiv_pow_apply, pow_add, Equiv.Perm.mul_apply]⟩

/-- **Orbit sizes along a component cycle.** The `σ`-orbit of a root of `C` has `c` times as many
members as its orbit under the return map, where `c` is the length of the cycle of `C`. -/
theorem card_orbitIndices_eq_mul (i : C.supp) :
    #(P.orbitIndices σ i) = minimalPeriod σ.componentEquiv C *
      #((P.componentPairing C).orbitIndices (σ.componentReturn C) i) := by
  classical
  rw [orbitIndices_eq_biUnion,
    card_biUnion (pairwiseDisjoint_map_orbitIndices_componentReturn σ C i)]
  simp

/-- **The cycle sum carries orbit sums of the return map to orbit sums of `σ`.** For a root of `C`,
the cycle sum of its orbit sum under the return map is its orbit sum under `σ`. -/
theorem componentCycleSum_orbitSum (i : C.supp) :
    σ.componentCycleSum C ((P.componentPairing C).orbitSum (σ.componentReturn C) i) =
      P.orbitSum σ i := by
  classical
  rw [orbitSum_def P σ, orbitIndices_eq_biUnion,
    sum_biUnion (pairwiseDisjoint_map_orbitIndices_componentReturn σ C i), componentCycleSum_apply]
  refine sum_congr rfl fun r _ ↦ ?_
  rw [sum_map, sum_map, orbitSum_def, Submodule.coe_sum, map_sum]
  refine sum_congr rfl fun t _ ↦ ?_
  rw [coe_componentPairing_root]
  exact Hom.root_weightMap_apply P P t (σ ^ r).toHom

/-- The cycle sum of a vector fixed by `σ` projected onto the component space of `C` is the sum of
the projections of that vector onto the component spaces `σʳC` of the cycle of `C`. -/
theorem componentCycleSum_componentProj {x : M} (hx : x ∈ LinearMap.fixedSubmodule σ.weightMap) :
    σ.componentCycleSum C (P.componentProj C x) =
      ∑ r ∈ range (minimalPeriod σ.componentEquiv C),
        (P.componentProj ((σ ^ r).componentEquiv C) x : M) := by
  rw [componentCycleSum_apply]
  refine sum_congr rfl fun r _ ↦ ?_
  rw [← coe_componentPairingEquiv_weightMap_apply, componentPairingEquiv_weightMap_componentProj,
    weightMap_pow, LinearMap.pow_apply_of_mem_fixedSubmodule _ hx]

/-- The projection onto the component space of `C` of a vector fixed by `σ` is fixed by the return
map of `C`. -/
theorem componentProj_mem_fixedSubmodule {x : M}
    (hx : x ∈ LinearMap.fixedSubmodule σ.weightMap) :
    P.componentProj C x ∈ LinearMap.fixedSubmodule (σ.componentReturn C).toHom.weightMap := by
  rw [LinearMap.mem_fixedSubmodule_iff, Subtype.ext_iff, coe_componentReturn_weightMap_apply,
    ← coe_componentPairingEquiv_weightMap_apply, componentPairingEquiv_weightMap_componentProj,
    weightMap_pow, LinearMap.pow_apply_of_mem_fixedSubmodule _ hx]
  exact congrArg (fun D ↦ (P.componentProj D x : M)) (componentEquiv_pow_minimalPeriod σ C)

/-! ### The cycle sum on fixed vectors -/

/-- The **cycle sum on fixed vectors**: the cycle sum `x ↦ ∑_{r < c} σʳ x` of the component `C`,
`c` the length of its cycle, as a linear map from the vectors of the component space of `C` fixed
by the return map to the vectors fixed by `σ`. -/
noncomputable def componentCycleMap :
    LinearMap.fixedSubmodule (σ.componentReturn C).toHom.weightMap →ₗ[K]
      LinearMap.fixedSubmodule σ.toHom.weightMap :=
  ((σ.componentCycleSum C).comp ((P.componentSpace C).subtype.comp
    (LinearMap.fixedSubmodule _).subtype)).codRestrict _ fun u ↦
      componentCycleSum_mem_fixedSubmodule <| by
        simpa using congrArg Subtype.val (LinearMap.mem_fixedSubmodule_iff.mp u.prop)

@[simp]
theorem coe_componentCycleMap_apply
    (u : LinearMap.fixedSubmodule (σ.componentReturn C).toHom.weightMap) :
    (σ.componentCycleMap C u : M) = σ.componentCycleSum C (u : P.componentSpace C) :=
  (rfl)

/-- The cycle sum on fixed vectors carries the orbit sum of a root of `C` under the return map to
its orbit sum under `σ`. -/
theorem componentCycleMap_orbitSum (i : C.supp) :
    σ.componentCycleMap C ⟨_, (P.componentPairing C).orbitSum_mem_fixedSubmodule _ i⟩ =
      ⟨_, P.orbitSum_mem_fixedSubmodule σ i⟩ :=
  Subtype.ext (componentCycleSum_orbitSum σ C i)

/-- Projection onto the component space of `C` is a left inverse of the cycle sum on fixed
vectors. -/
theorem componentProj_componentCycleMap
    (u : LinearMap.fixedSubmodule (σ.componentReturn C).toHom.weightMap) :
    P.componentProj C (σ.componentCycleMap C u) = u :=
  componentProj_componentCycleSum (u : P.componentSpace C).prop

/-- The cycle sum on fixed vectors is injective. -/
theorem componentCycleMap_injective : Injective (σ.componentCycleMap C) :=
  fun u v h ↦ Subtype.ext <| by
    rw [← componentProj_componentCycleMap σ C u, h, componentProj_componentCycleMap]

end Equiv

namespace Base

variable (b : P.Base) {σ : P.Aut} {C : P.Component}

/-- The restriction of an automorphism permuting the simple roots of `b` permutes the simple roots
of the base of the component. -/
theorem indexEquiv_restrictComponent_mem_support
    (hσ : ∀ i ∈ b.support, σ.indexEquiv i ∈ b.support) (hC : σ.componentEquiv C = C)
    {i : C.supp} (hi : i ∈ (b.componentBase C).support) :
    (σ.restrictComponent C hC).indexEquiv i ∈ (b.componentBase C).support := by
  rw [mem_support_componentBase] at hi ⊢
  exact hσ _ hi

/-- **The return map is based.** The return map of a component under an automorphism permuting the
simple roots of `b` permutes the simple roots of the base of the component. -/
theorem indexEquiv_componentReturn_mem_support
    (hσ : ∀ i ∈ b.support, σ.indexEquiv i ∈ b.support) {i : C.supp}
    (hi : i ∈ (b.componentBase C).support) :
    (σ.componentReturn C).indexEquiv i ∈ (b.componentBase C).support :=
  b.indexEquiv_restrictComponent_mem_support (fun j hj ↦ by
    rw [Equiv.indexEquiv_pow]
    exact (P.mem_support_iff_of_mem_orbitIndices hσ
      (mem_orbitIndices_iff_exists_pow.mpr ⟨_, rfl⟩)).mpr hj) _ hi

end Base

end RootPairing
