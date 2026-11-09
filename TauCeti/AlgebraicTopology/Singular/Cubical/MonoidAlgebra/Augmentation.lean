/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Singular.Cubical.Cone
public import TauCeti.AlgebraicTopology.Singular.Cubical.MonoidAlgebra.Bimodule
public import TauCeti.AlgebraicTopology.Singular.Cubical.MonoidAlgebra.Hom

/-!
# The augmentation of the module of cubical chains of a space

The module `⨁ n, C^□_n(Y; R)` of normalized cubical chains of a space `Y`
(`TauCeti.cubicalChainModule`) has the **augmentation** `ε : ⨁ n, C^□_n(Y; R) → R`: the augmentation
of `0`-chains, extended by zero to the chains of positive dimension. It vanishes on boundaries, so
it is a chain map to `R` placed in degree zero with zero differential.

When a topological monoid `G` acts on `Y` from the left, the augmentation is linear over the
augmentation of the DG algebra `C^□_*(G; R)` (`TauCeti.cubicalChainModuleAugmentation_smul`):
`ε (a · m) = ε(a) ε(m)`. In other words, `ε` is linear for the action of `C^□_*(G; R)` on `R`
through its augmentation.

A homotopy `H` from a constant map at `v` to the identity of `Y` gives, through the cone on cubical
chains (`TauCeti.NormalizedCubicalChain.cone`), an `R`-linear contracting homotopy `K` of the
augmented module (`TauCeti.cubicalChainModuleCone`):

`d (K m) + K (d m) = ε(m) • [v] - m`.

The homotopy `K` is only `R`-linear: a contraction of `Y` need not commute with the action of `G`.
It still shows that for a contractible space `Y` a cycle of augmentation zero is a boundary
(`TauCeti.exists_cubicalChainModuleDifferential_eq_of_augmentation_eq_zero`). Together with the
vanishing on boundaries and the surjectivity of `ε`, this says that the augmentation induces an
isomorphism from the cohomology of `⨁ n, C^□_n(Y; R)` onto `R` in degree zero: it is a
quasi-isomorphism.

The chain homotopy of a homotopy equivalence (`TauCeti.cubicalChainModuleHomotopy`) is stated for
spaces with a right monoid action and in a single universe. The cone is explicit and needs neither,
so it also applies to the chains of a space with a left action alone.

## Main definitions

* `TauCeti.cubicalChainModuleAugmentation Y G R`: the augmentation `⨁ n, C^□_n(Y; R) → R`.
* `TauCeti.cubicalChainModuleCone R H`: the contracting homotopy of the module given by a homotopy
  `H` from a constant map to the identity.

## Main results

* `TauCeti.cubicalChainModuleAugmentation_differential`: `ε ∘ d = 0`.
* `TauCeti.cubicalChainModuleAugmentation_smul`: `ε (a · m) = ε(a) ε(m)` for a left action.
* `TauCeti.cubicalChainModuleAugmentation_surjective`: `ε` is onto when `Y` has a point.
* `TauCeti.cubicalChainModuleDifferential_cone_add_cone_differential`:
  `d (K m) + K (d m) = ε(m) • [v] - m`.
* `TauCeti.exists_cubicalChainModuleDifferential_eq_of_augmentation_eq_zero`: for a contractible
  space, a cycle of augmentation zero is a boundary.

## References

* W. S. Massey, *Singular Homology Theory*, GTM 70, Springer, 1980, Chapters II and VII.
-/

public section

noncomputable section

namespace TauCeti

open NormalizedCubicalChain

section Augmentation

variable (Y G : Type*) [TopologicalSpace Y] (R : Type*) [CommRing R]

/-- The **augmentation of the module of cubical chains**: the augmentation of `0`-chains, and zero
on the chains of positive dimension. -/
def cubicalChainModuleAugmentation : cubicalChainModule Y G R →ₗ[R] R :=
  cubicalChainModuleDesc (cubicalChainAugmentLof Y R)

variable {Y G R}

/-- The augmentation on the chains of dimension `n`. -/
theorem cubicalChainModuleAugmentation_lof (n : ℕ) (c : NormalizedCubicalChain Y R n) :
    cubicalChainModuleAugmentation Y G R (cubicalChainModuleLof Y G R n c) =
      cubicalChainAugmentLof Y R n c :=
  cubicalChainModuleDesc_lof _ c

/-- The augmentation of a `0`-chain. -/
@[simp]
theorem cubicalChainModuleAugmentation_lof_zero (c : NormalizedCubicalChain Y R 0) :
    cubicalChainModuleAugmentation Y G R (cubicalChainModuleLof Y G R 0 c) = augment Y R c := by
  rw [cubicalChainModuleAugmentation_lof, cubicalChainAugmentLof_zero]

/-- The augmentation vanishes on the chains of positive dimension. -/
@[simp]
theorem cubicalChainModuleAugmentation_lof_succ (k : ℕ) (c : NormalizedCubicalChain Y R (k + 1)) :
    cubicalChainModuleAugmentation Y G R (cubicalChainModuleLof Y G R (k + 1) c) = 0 := by
  rw [cubicalChainModuleAugmentation_lof, cubicalChainAugmentLof_of_ne_zero (Nat.succ_ne_zero k)]

/-- **The augmentation vanishes on boundaries.** -/
@[simp]
theorem cubicalChainModuleAugmentation_differential (m : cubicalChainModule Y G R) :
    cubicalChainModuleAugmentation Y G R (cubicalChainModuleDifferential Y G R m) = 0 := by
  induction m using cubicalChainModule.induction_on with
  | zero => simp
  | add m m' hm hm' => rw [map_add, map_add, hm, hm', add_zero]
  | lof n c =>
    rcases n with _ | k
    · rw [cubicalChainModuleDifferential_lof_zero, map_zero]
    · rw [cubicalChainModuleDifferential_lof_succ]
      rcases k with _ | j
      · rw [cubicalChainModuleAugmentation_lof_zero, ← LinearMap.comp_apply, augment_boundary,
          LinearMap.zero_apply]
      · rw [cubicalChainModuleAugmentation_lof_succ]

/-- The augmentation is onto as soon as the space has a point. -/
theorem cubicalChainModuleAugmentation_surjective (y : Y) :
    Function.Surjective (cubicalChainModuleAugmentation Y G R) := fun r ↦
  ⟨cubicalChainModuleLof Y G R 0 (r • ofCube Y R (SingularCube.point y)), by
    rw [cubicalChainModuleAugmentation_lof_zero, map_smul, augment_ofCube, smul_eq_mul,
      _root_.mul_one]⟩

end Augmentation

section LeftAction

variable {G Y H : Type*} [Monoid G] [TopologicalSpace G] [ContinuousMul G] [TopologicalSpace Y]
  [MulAction G Y] [ContinuousSMul G Y] {R : Type*} [CommRing R]

/-- **The augmentation is linear over the augmentation of the chain algebra**: for the left action
of the chains of `G`, `ε (a · m) = ε(a) ε(m)`. -/
theorem cubicalChainModuleAugmentation_smul (a : normalizedCubicalChainAlgebra G R)
    (m : cubicalChainModule Y H R) :
    cubicalChainModuleAugmentation Y H R (a • m) =
      cubicalChainAugmentation G R a * cubicalChainModuleAugmentation Y H R m := by
  induction m using cubicalChainModule.induction_on with
  | zero => rw [smul_zero, map_zero, mul_zero]
  | add m m' hm hm' => rw [smul_add, map_add, hm, hm', map_add, mul_add]
  | lof q c =>
    induction a using DirectSum.induction_on with
    | zero => rw [zero_smul, map_zero, map_zero, zero_mul]
    | add a a' ha ha' => rw [add_smul, map_add, ha, ha', map_add, add_mul]
    | of p x =>
      rw [← DirectSum.lof_eq_of R, lof_smul_cubicalChainModuleLof,
        cubicalChainModuleAugmentation_lof, cubicalChainModuleAugmentation_lof,
        cubicalChainAugmentation_lof]
      rcases p with _ | p
      · rcases q with _ | q
        · rw [cubicalChainAugmentLof_zero, cubicalChainAugmentLof_zero,
            cubicalChainAugmentLof_zero, augment_leftAct]
        · rw [cubicalChainAugmentLof_of_ne_zero (Nat.succ_ne_zero q),
            cubicalChainAugmentLof_of_ne_zero (by omega), mul_zero]
      · rw [cubicalChainAugmentLof_of_ne_zero (Nat.succ_ne_zero p),
          cubicalChainAugmentLof_of_ne_zero (by omega), zero_mul]

end LeftAction

section Cone

variable {Y G : Type*} [TopologicalSpace Y] (R : Type*) [CommRing R] {v : Y}

/-- The **contracting homotopy of the module of chains** given by a homotopy `H` from the constant
map at `v` to the identity of `Y`: the cone on chains of each dimension along `H`, raising the
dimension by one. It is `R`-linear but need not be linear over any monoid acting on `Y`. -/
def cubicalChainModuleCone (H : (ContinuousMap.const Y v).Homotopy (ContinuousMap.id Y)) :
    cubicalChainModule Y G R →ₗ[R] cubicalChainModule Y G R :=
  cubicalChainModuleDesc fun n ↦ cubicalChainModuleLof Y G R (n + 1) ∘ₗ cone R H n

variable {R}

/-- The contracting homotopy on a chain of dimension `n` is its cone, of dimension `n + 1`. -/
@[simp]
theorem cubicalChainModuleCone_lof (H : (ContinuousMap.const Y v).Homotopy (ContinuousMap.id Y))
    (n : ℕ) (c : NormalizedCubicalChain Y R n) :
    cubicalChainModuleCone (G := G) R H (cubicalChainModuleLof Y G R n c) =
      cubicalChainModuleLof Y G R (n + 1) (cone R H n c) :=
  cubicalChainModuleDesc_lof _ c

/-- **The cone is a contracting homotopy of the augmented module**:
`d (K m) + K (d m) = ε(m) • [v] - m`, where `[v]` is the `0`-chain of the point `v`. -/
theorem cubicalChainModuleDifferential_cone_add_cone_differential
    (H : (ContinuousMap.const Y v).Homotopy (ContinuousMap.id Y)) (m : cubicalChainModule Y G R) :
    cubicalChainModuleDifferential Y G R (cubicalChainModuleCone R H m) +
        cubicalChainModuleCone R H (cubicalChainModuleDifferential Y G R m) =
      cubicalChainModuleAugmentation Y G R m •
          cubicalChainModuleLof Y G R 0 (ofCube Y R (SingularCube.point v)) - m := by
  induction m using cubicalChainModule.induction_on with
  | zero => simp
  | add m m' hm hm' =>
    simp only [map_add, add_smul]
    rw [add_add_add_comm, hm, hm']
    abel
  | lof n c =>
    rcases n with _ | k
    · rw [cubicalChainModuleCone_lof, cubicalChainModuleDifferential_lof_succ,
        cubicalChainModuleDifferential_lof_zero, map_zero, add_zero, boundary_cone_zero,
        map_sub, map_smul, cubicalChainModuleAugmentation_lof_zero]
    · rw [cubicalChainModuleCone_lof, cubicalChainModuleDifferential_lof_succ,
        cubicalChainModuleDifferential_lof_succ, cubicalChainModuleCone_lof, ← map_add,
        boundary_cone_add_cone_boundary, map_neg, cubicalChainModuleAugmentation_lof_succ,
        zero_smul, zero_sub]

/-- **Acyclicity of the augmented chains of a contractible space**: a cycle of augmentation zero in
the module of cubical chains of a contractible space is a boundary. -/
theorem exists_cubicalChainModuleDifferential_eq_of_augmentation_eq_zero [ContractibleSpace Y]
    {m : cubicalChainModule Y G R} (hd : cubicalChainModuleDifferential Y G R m = 0)
    (hε : cubicalChainModuleAugmentation Y G R m = 0) :
    ∃ n, cubicalChainModuleDifferential Y G R n = m := by
  obtain ⟨v, ⟨H⟩⟩ := (contractible_iff_id_nullhomotopic Y).1 ‹_›
  refine ⟨-cubicalChainModuleCone R H.symm m, ?_⟩
  have key := cubicalChainModuleDifferential_cone_add_cone_differential H.symm m
  rw [hd, map_zero, add_zero, hε, zero_smul, zero_sub] at key
  rw [map_neg, key, neg_neg]

end Cone

end TauCeti
