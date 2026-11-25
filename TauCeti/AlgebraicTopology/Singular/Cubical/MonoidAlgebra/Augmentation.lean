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
through its augmentation. More generally, pushing chains forward along a map `f : Y → Y'` that is
constant on the orbits is linear over the augmentation
(`TauCeti.cubicalChainModuleLinearMap_smul_of_apply_smul`): `f_* (a · m) = ε(a) f_* m`, since a
chain of positive dimension of `G` acts by families of translates, which `f` collapses to degenerate
cubes. For `Y'` a point this is the multiplicativity of `ε`.

The point chain `[y]` of a point `y` (`TauCeti.cubicalChainModulePoint`) is a cycle of augmentation
`1` in degree `0`, and for a left action the point chain of `g` takes it to `[g • y]`
(`TauCeti.cubicalChainPoint_smul_cubicalChainModulePoint`); for a right action it takes it to
`[y · g]` (`TauCeti.op_cubicalChainPoint_smul_cubicalChainModulePoint`).

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
* `TauCeti.cubicalChainModulePoint Y G R y`: the point chain `[y]`, a cycle of augmentation `1`.
* `TauCeti.cubicalChainModuleCone R H`: the contracting homotopy of the module given by a homotopy
  `H` from a constant map to the identity.

## Main results

* `TauCeti.cubicalChainModuleAugmentation_differential`: `ε ∘ d = 0`.
* `TauCeti.cubicalChainModuleAugmentation_mem`: `ε` preserves degrees, so it vanishes on the
  chains of positive dimension.
* `TauCeti.cubicalChainModuleLinearMap_smul_of_apply_smul`: pushing forward along a map constant on
  the orbits is linear over the augmentation.
* `TauCeti.cubicalChainModuleAugmentation_smul`: `ε (a · m) = ε(a) ε(m)` for a left action.
* `TauCeti.cubicalChainModuleAugmentation_surjective`: `ε` is onto when `Y` has a point.
* `TauCeti.cubicalChainPoint_smul_cubicalChainModulePoint`: for a left action,
  `[g] · [y] = [g • y]`.
* `TauCeti.op_cubicalChainPoint_smul_cubicalChainModulePoint`: for a right action,
  `[y] · [g] = [y · g]`.
* `TauCeti.cubicalChainModuleDifferential_cone_add_cone_differential`:
  `d (K m) + K (d m) = ε(m) • [v] - m`.
* `TauCeti.cubicalChainModuleDifferential_cone_cubicalChainModulePoint`: `d (K [y]) = [v] - [y]`.
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
  | add m m' hm hm' => rw [map_add, map_add, hm, hm', add_zero]
  | lof n c =>
    rcases n with _ | k
    · rw [cubicalChainModuleDifferential_lof_zero, map_zero]
    · rw [cubicalChainModuleDifferential_lof_succ]
      rcases k with _ | j
      · rw [cubicalChainModuleAugmentation_lof_zero, ← LinearMap.comp_apply, augment_boundary,
          LinearMap.zero_apply]
      · rw [cubicalChainModuleAugmentation_lof_succ]

/-- **The augmentation preserves degrees**: it sends the chains of cohomological degree `i` to the
degree-`i` part of the trivially graded ground ring, so it vanishes outside degree zero. -/
theorem cubicalChainModuleAugmentation_mem {i : ℤ} {m : cubicalChainModule Y G R}
    (hm : m ∈ cubicalChainModuleGrading Y G R i) :
    cubicalChainModuleAugmentation Y G R m ∈ trivialGrading R R i := by
  rcases mem_cubicalChainModuleGrading_iff.1 hm with rfl | ⟨n, c, hn, rfl⟩
  · rw [map_zero]
    exact zero_mem _
  · rw [cubicalChainModuleAugmentation_lof, mem_trivialGrading_iff]
    rcases Nat.eq_zero_or_pos n with rfl | hn'
    · exact Or.inl (by omega)
    · exact Or.inr (cubicalChainAugmentLof_of_ne_zero (by omega) c)

/-- The augmentation is onto as soon as the space has a point. -/
theorem cubicalChainModuleAugmentation_surjective (y : Y) :
    Function.Surjective (cubicalChainModuleAugmentation Y G R) := fun r ↦
  ⟨cubicalChainModuleLof Y G R 0 (r • ofCube Y R (SingularCube.point y)), by
    rw [cubicalChainModuleAugmentation_lof_zero, map_smul, augment_ofCube, smul_eq_mul,
      _root_.mul_one]⟩

end Augmentation

section PointChain

variable (Y G : Type*) [TopologicalSpace Y] (R : Type*) [CommRing R]

/-- The **point chain** `[y]` of a point `y`: the `0`-chain of the singular point at `y`, in the
module of cubical chains of `Y`. -/
def cubicalChainModulePoint (y : Y) : cubicalChainModule Y G R :=
  cubicalChainModuleLof Y G R 0 (ofCube Y R (SingularCube.point y))

variable {Y G R}

/-- Unfold `TauCeti.cubicalChainModulePoint`. -/
theorem cubicalChainModulePoint_def (y : Y) :
    cubicalChainModulePoint Y G R y =
      cubicalChainModuleLof Y G R 0 (ofCube Y R (SingularCube.point y)) :=
  (rfl)

/-- The point chain `[y]` lies in degree `0`. -/
theorem cubicalChainModulePoint_mem (y : Y) :
    cubicalChainModulePoint Y G R y ∈ cubicalChainModuleGrading Y G R 0 :=
  mem_cubicalChainModuleGrading_iff.2 (Or.inr ⟨0, _, by simp, rfl⟩)

/-- The point chain `[y]` is a cycle. -/
@[simp]
theorem cubicalChainModuleDifferential_cubicalChainModulePoint (y : Y) :
    cubicalChainModuleDifferential Y G R (cubicalChainModulePoint Y G R y) = 0 :=
  cubicalChainModuleDifferential_lof_zero _

/-- The augmentation of the point chain `[y]` is `1`. -/
@[simp]
theorem cubicalChainModuleAugmentation_cubicalChainModulePoint (y : Y) :
    cubicalChainModuleAugmentation Y G R (cubicalChainModulePoint Y G R y) = 1 := by
  simp [cubicalChainModulePoint_def]

end PointChain

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

/-- **Points act on point chains through the action**: the point chain of `g` takes the point chain
`[y]` to `[g • y]`. -/
@[simp]
theorem cubicalChainPoint_smul_cubicalChainModulePoint (g : G) (y : Y) :
    cubicalChainPoint G R g • cubicalChainModulePoint Y H R y =
      cubicalChainModulePoint Y H R (g • y) := by
  rw [cubicalChainPoint_def, cubicalChainModulePoint_def, cubicalChainModulePoint_def,
    lof_smul_cubicalChainModuleLof, leftAct_ofCube_point]

omit [ContinuousMul G] in
/-- Pushing the left action forward along a map that is constant on the orbits only sees the chain
of `G` through its push-forward to the unit: if `f (g • y) = f y`, then
`f_* (a · c) = f_* ((1)_* a · c)`. -/
theorem map_leftAct_eq_map_leftAct_map_const_one {Y' : Type*} [TopologicalSpace Y']
    (f : C(Y, Y')) (hf : ∀ (g : G) (y : Y), f (g • y) = f y) {p q : ℕ}
    (a : NormalizedCubicalChain G R p)
    (c : NormalizedCubicalChain Y R q) :
    map R f (p + q) (leftAct G Y R p q a c) =
      map R f (p + q) (leftAct G Y R p q (map R (ContinuousMap.const G 1) p a) c) := by
  have key : f.comp (leftActMap G Y) =
      (f.comp (leftActMap G Y)).comp ((ContinuousMap.const G (1 : G)).prodMap (.id Y)) := by
    ext x
    simp [hf]
  rw [leftAct_def, leftAct_def, ← LinearMap.comp_apply (map R f (p + q)), ← map_comp, key,
    map_comp, LinearMap.comp_apply, map_crossProduct, map_id, LinearMap.id_apply, map_comp,
    LinearMap.comp_apply]

/-- **Pushing forward along a map constant on the orbits is linear over the augmentation**: if
`f (g • y) = f y` for all `g` and `y`, then `f_* (a · m) = ε(a) f_* m`. A chain of positive
dimension of `G` acts by families of translates, which `f` collapses to degenerate cubes, and a
`0`-chain acts through the sum of its coefficients. -/
theorem cubicalChainModuleLinearMap_smul_of_apply_smul {Y' H' : Type*} [TopologicalSpace Y']
    (f : C(Y, Y')) (hf : ∀ (g : G) (y : Y), f (g • y) = f y)
    (a : normalizedCubicalChainAlgebra G R) (m : cubicalChainModule Y H R) :
    cubicalChainModuleLinearMap (G' := H') R f (a • m) =
      cubicalChainAugmentation G R a • cubicalChainModuleLinearMap R f m := by
  induction m using cubicalChainModule.induction_on with
  | add m m' hm hm' => rw [smul_add, map_add, hm, hm', map_add, smul_add]
  | lof q c =>
    induction a using DirectSum.induction_on with
    | zero => rw [zero_smul, map_zero, map_zero, zero_smul]
    | add a a' ha ha' => rw [add_smul, map_add, ha, ha', map_add, add_smul]
    | of p z =>
      rw [← DirectSum.lof_eq_of R, lof_smul_cubicalChainModuleLof,
        cubicalChainModuleLinearMap_lof, cubicalChainModuleLinearMap_lof,
        cubicalChainAugmentation_lof, map_leftAct_eq_map_leftAct_map_const_one f hf]
      rcases p with _ | p
      · -- A `0`-chain is pushed to the unit as its augmentation times the unit.
        rw [map_const_zero, ← one_def, map_smul, LinearMap.smul_apply, map_smul, map_smul,
          cubicalChainAugmentLof_zero, ← cubicalChainModuleLof_cast (Nat.zero_add q),
          ← map_cast, one_leftAct]
      · rw [map_const_succ, LinearMap.zero_apply, map_zero, LinearMap.zero_apply, map_zero,
          map_zero, cubicalChainAugmentLof_of_ne_zero (Nat.succ_ne_zero p), zero_smul]

end LeftAction

section RightAction

open MulOpposite

variable {G Y : Type*} [Monoid G] [TopologicalSpace G] [ContinuousMul G] [TopologicalSpace Y]
  [MulAction Gᵐᵒᵖ Y] [ContinuousSMul Gᵐᵒᵖ Y] {R : Type*} [CommRing R]

/-- **Points act on point chains through the action, on the right**: the point chain of `g` takes
the point chain `[y]` to `[y · g]`. -/
@[simp]
theorem op_cubicalChainPoint_smul_cubicalChainModulePoint (g : G) (y : Y) :
    op (cubicalChainPoint G R g) • cubicalChainModulePoint Y G R y =
      cubicalChainModulePoint Y G R (op g • y) := by
  rw [cubicalChainPoint_def, cubicalChainModulePoint_def, cubicalChainModulePoint_def,
    op_lof_smul_cubicalChainModuleLof, act_ofCube_point]

end RightAction

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
      cubicalChainModuleAugmentation Y G R m • cubicalChainModulePoint Y G R v - m := by
  induction m using cubicalChainModule.induction_on with
  | add m m' hm hm' =>
    simp only [map_add, add_smul]
    rw [add_add_add_comm, hm, hm']
    abel
  | lof n c =>
    rcases n with _ | k
    · rw [cubicalChainModuleCone_lof, cubicalChainModuleDifferential_lof_succ,
        cubicalChainModuleDifferential_lof_zero, map_zero, add_zero, boundary_cone_zero,
        map_sub, map_smul, cubicalChainModuleAugmentation_lof_zero, cubicalChainModulePoint_def]
    · rw [cubicalChainModuleCone_lof, cubicalChainModuleDifferential_lof_succ,
        cubicalChainModuleDifferential_lof_succ, cubicalChainModuleCone_lof, ← map_add,
        boundary_cone_add_cone_boundary, map_neg, cubicalChainModuleAugmentation_lof_succ,
        zero_smul, zero_sub]

/-- **The cone on a point chain bounds it to the cone point**: `d (K [y]) = [v] - [y]`. -/
@[simp]
theorem cubicalChainModuleDifferential_cone_cubicalChainModulePoint
    (H : (ContinuousMap.const Y v).Homotopy (ContinuousMap.id Y)) (y : Y) :
    cubicalChainModuleDifferential Y G R
        (cubicalChainModuleCone R H (cubicalChainModulePoint Y G R y)) =
      cubicalChainModulePoint Y G R v - cubicalChainModulePoint Y G R y := by
  simpa using
    cubicalChainModuleDifferential_cone_add_cone_differential H (cubicalChainModulePoint Y G R y)

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
