/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.ContinuousMonoidHom
public import Mathlib.Topology.Algebra.OpenSubgroup
public import TauCeti.Topology.Algebra.RestrictedProduct.Box

/-!
# Principal-level product decomposition of restricted products

For any finite set `T : Finset ι` and submonoid-like reference sets `B : ∀ i, K i` in topological
monoids `G i`, the principal stage `Πʳ i, [G i, B i]_[𝓟 (T : Set ι)ᶜ]` splits via a topological
monoid isomorphism `TauCeti.prodContinuousMulEquivPrincipal` from
`(Π i : T, G i) × (Π i : {i // i ∉ T}, B i)`. Composing with the principal inclusion into
`Πʳ i, [G i, B i]` yields `TauCeti.levelMonoidHom`, which is always a topological embedding and is
an open embedding when `B i` is open for every `i ∉ T`. When `G i` are groups and `B i` are
subgroups open outside `S`, the range of `levelMonoidHom B S` is the level open subgroup
`TauCeti.levelOpenSubgroup`, identified as a topological group with
`(Π i : S, G i) × (Π i : {i // i ∉ S}, B i)` via `TauCeti.levelOpenSubgroupEquiv`. Every
declaration has an additive counterpart via `@[to_additive]`.

## Main definitions and results

* `TauCeti.prodContinuousMulEquivPrincipal`: topological monoid isomorphism
  `((Π i : T, G i) × (Π i : {i // i ∉ T}, B i)) ≃ₜ* Πʳ i, [G i, B i]_[𝓟 (T : Set ι)ᶜ]`, with
  coordinate and `.symm` projection lemmas.
* `TauCeti.levelMonoidHom`, `TauCeti.range_levelMonoidHom`: canonical monoid homomorphism into
  `Πʳ i, [G i, B i]` and its range `{x | ∀ i ∉ T, x i ∈ B i}`.
* `TauCeti.isEmbedding_levelMonoidHom`, `TauCeti.isOpenEmbedding_levelMonoidHom_of_isOpen`,
  `TauCeti.isOpenEmbedding_levelMonoidHom`: topological and open embedding properties of
  `levelMonoidHom`; openness of `B i` is only needed outside `T`.
* `TauCeti.image_levelMonoidHom_pi_prod_univ`, `TauCeti.preimage_levelMonoidHom_box`: image and
  box-preimage formulas for `levelMonoidHom`.
* `TauCeti.levelOpenSubgroup`, `TauCeti.levelOpenSubgroupEquiv`,
  `TauCeti.coe_comp_levelOpenSubgroupEquiv`, `TauCeti.preimage_coe_comp_levelOpenSubgroupEquiv_box`:
  level open subgroup of elements integral outside `S`, its topological group chart, inclusion
  identity, and box-preimage formula.

## References

* N. Bourbaki, *General Topology*.
* A. Weil, *Basic Number Theory*.
-/

public section

noncomputable section

open Filter RestrictedProduct Set Topology
open scoped RestrictedProduct

namespace TauCeti

variable {ι : Type*} {G : ι → Type*} {K : ι → Type*} [∀ i, SetLike (K i) (G i)]
  [∀ i, TopologicalSpace (G i)]

section Monoid

variable [∀ i, Monoid (G i)] [∀ i, SubmonoidClass (K i) (G i)]
variable (B : ∀ i, K i) (T : Finset ι)

/-- For any finite index set `T : Finset ι`, the principal stage `Πʳ i, [G i, B i]_[𝓟 (T : Set ι)ᶜ]`
is isomorphic as a topological monoid to `(Π i : T, G i) × (Π i : {i // i ∉ T}, B i)`. -/
@[to_additive prodContinuousAddEquivPrincipal
/-- For any finite index set `T : Finset ι`, the principal stage
`Πʳ i, [G i, B i]_[𝓟 (T : Set ι)ᶜ]` is isomorphic as a topological additive monoid to
`(Π i : T, G i) × (Π i : {i // i ∉ T}, B i)`. -/]
def prodContinuousMulEquivPrincipal :
    ((Π i : T, G i) × (Π i : {i // i ∉ T}, B i)) ≃ₜ* Πʳ i, [G i, B i]_[𝓟 (T : Set ι)ᶜ] :=
  open Classical in
  { toFun p := mk (fun i ↦ if hi : i ∈ T then p.1 ⟨i, hi⟩ else (p.2 ⟨i, hi⟩ : G i)) <|
      eventually_principal.mpr fun i hi ↦ by simp [Finset.mem_coe.not.mp hi]
    invFun x :=
      ((fun i : T ↦ x i.val),
        fun i : {i // i ∉ T} ↦ ⟨x i.val,
          eventually_principal.mp x.eventually i.val (Finset.mem_coe.not.mpr i.property)⟩)
    left_inv p := by ext i <;> simp [i.property]
    right_inv x := by ext i; simp only [mk_apply]; split_ifs <;> rfl
    map_mul' p q := by ext i; by_cases hi : i ∈ T <;> simp [hi]
    continuous_toFun := by
      refine isEmbedding_coe_of_principal.continuous_iff.mpr (continuous_pi fun i ↦ ?_)
      by_cases hi : i ∈ T <;> simp only [Function.comp_def, mk_apply, hi, ↓reduceDIte] <;> fun_prop
    continuous_invFun := Continuous.prodMk
      (continuous_pi fun i ↦ (continuous_apply i.val).comp continuous_coe)
      (continuous_pi fun i ↦ Continuous.subtype_mk ((continuous_apply i.val).comp continuous_coe) _)
          }

/-- Coordinate formula for `prodContinuousMulEquivPrincipal B T` at `i ∈ T`. -/
@[to_additive (attr := simp) prodContinuousAddEquivPrincipal_apply_of_mem
/-- Coordinate formula for `prodContinuousAddEquivPrincipal B T` at `i ∈ T`. -/]
theorem prodContinuousMulEquivPrincipal_apply_of_mem
    (p : (Π i : T, G i) × (Π i : {i // i ∉ T}, B i)) {i : ι} (hi : i ∈ T) :
    prodContinuousMulEquivPrincipal B T p i = p.1 ⟨i, hi⟩ := by
  simp [prodContinuousMulEquivPrincipal, hi]

/-- Coordinate formula for `prodContinuousMulEquivPrincipal B T` at `i ∉ T`. -/
@[to_additive (attr := simp) prodContinuousAddEquivPrincipal_apply_of_notMem
/-- Coordinate formula for `prodContinuousAddEquivPrincipal B T` at `i ∉ T`. -/]
theorem prodContinuousMulEquivPrincipal_apply_of_notMem
    (p : (Π i : T, G i) × (Π i : {i // i ∉ T}, B i)) {i : ι} (hi : i ∉ T) :
    prodContinuousMulEquivPrincipal B T p i = (p.2 ⟨i, hi⟩ : G i) := by
  simp [prodContinuousMulEquivPrincipal, hi]

/-- First projection of `(prodContinuousMulEquivPrincipal B T).symm`. -/
@[to_additive (attr := simp) prodContinuousAddEquivPrincipal_symm_fst
/-- First projection of `(prodContinuousAddEquivPrincipal B T).symm`. -/]
theorem prodContinuousMulEquivPrincipal_symm_fst (x : Πʳ i, [G i, B i]_[𝓟 (T : Set ι)ᶜ]) :
    ((prodContinuousMulEquivPrincipal B T).symm x).1 = fun i : T ↦ x i.val := by rfl

/-- Second projection of `(prodContinuousMulEquivPrincipal B T).symm`. -/
@[to_additive (attr := simp) prodContinuousAddEquivPrincipal_symm_snd
/-- Second projection of `(prodContinuousAddEquivPrincipal B T).symm`. -/]
theorem prodContinuousMulEquivPrincipal_symm_snd (x : Πʳ i, [G i, B i]_[𝓟 (T : Set ι)ᶜ]) :
    ((prodContinuousMulEquivPrincipal B T).symm x).2 =
      fun i : {i // i ∉ T} ↦
        ⟨x i.val, eventually_principal.mp x.eventually i.val (Finset.mem_coe.not.mpr i.property)⟩
            := by rfl

/-- The canonical monoid homomorphism
`(Π i : T, G i) × (Π i : {i // i ∉ T}, B i) →* Πʳ i, [G i, B i]`, factoring through
`Πʳ i, [G i, B i]_[𝓟 (T : Set ι)ᶜ]`. It is a topological embedding (`isEmbedding_levelMonoidHom`),
and an open embedding when each `B i` is open (`isOpenEmbedding_levelMonoidHom`). -/
@[to_additive
/-- The canonical additive monoid homomorphism
`(Π i : T, G i) × (Π i : {i // i ∉ T}, B i) →+ Πʳ i, [G i, B i]`, factoring through
`Πʳ i, [G i, B i]_[𝓟 (T : Set ι)ᶜ]`. It is a topological embedding
(`isEmbedding_levelAddMonoidHom`), and an open embedding when each `B i` is open
(`isOpenEmbedding_levelAddMonoidHom`). -/]
def levelMonoidHom : ((Π i : T, G i) × (Π i : {i // i ∉ T}, B i)) →* Πʳ i, [G i, B i] where
  toFun p := inclusion G (fun i ↦ (B i : Set (G i)))
    (le_principal_iff.mpr T.finite_toSet.compl_mem_cofinite) (prodContinuousMulEquivPrincipal B T p)
  map_one' := by
    ext i
    by_cases hi : i ∈ T <;> simp [prodContinuousMulEquivPrincipal, hi]
  map_mul' p q := by
    ext i
    simpa only [inclusion_apply, mul_apply] using
      congr_arg (fun x ↦ x i) (map_mul (prodContinuousMulEquivPrincipal B T) p q)

/-- `levelMonoidHom B T` is the composition of `prodContinuousMulEquivPrincipal B T` with the
principal inclusion into `Πʳ i, [G i, B i]`. -/
@[to_additive (attr := simp) inclusion_prodContinuousAddEquivPrincipal
/-- `levelAddMonoidHom B T` is the composition of `prodContinuousAddEquivPrincipal B T` with the
principal inclusion into `Πʳ i, [G i, B i]`. -/]
theorem inclusion_prodContinuousMulEquivPrincipal
    (p : (Π i : T, G i) × (Π i : {i // i ∉ T}, B i)) :
    inclusion G (fun i ↦ (B i : Set (G i)))
      (le_principal_iff.mpr T.finite_toSet.compl_mem_cofinite)
      (prodContinuousMulEquivPrincipal B T p) = levelMonoidHom B T p := by rfl

/-- Coordinate formula for `levelMonoidHom B T` at `i ∈ T`. -/
@[to_additive (attr := simp) /-- Coordinate formula for `levelAddMonoidHom B T` at `i ∈ T`. -/]
theorem levelMonoidHom_apply_of_mem (p : (Π i : T, G i) × (Π i : {i // i ∉ T}, B i)) {i : ι}
    (hi : i ∈ T) : levelMonoidHom B T p i = p.1 ⟨i, hi⟩ := by
  simp [← inclusion_prodContinuousMulEquivPrincipal, hi]

/-- Coordinate formula for `levelMonoidHom B T` at `i ∉ T`. -/
@[to_additive (attr := simp) /-- Coordinate formula for `levelAddMonoidHom B T` at `i ∉ T`. -/]
theorem levelMonoidHom_apply_of_notMem (p : (Π i : T, G i) × (Π i : {i // i ∉ T}, B i)) {i : ι}
    (hi : i ∉ T) : levelMonoidHom B T p i = (p.2 ⟨i, hi⟩ : G i) := by
  simp [← inclusion_prodContinuousMulEquivPrincipal, hi]

/-- The range of `levelMonoidHom B T` consists of all restricted-product elements whose coordinates
outside `T` lie in `B i`. -/
@[to_additive /-- The range of `levelAddMonoidHom B T` consists of all restricted-product elements
whose coordinates outside `T` lie in `B i`. -/]
theorem range_levelMonoidHom :
    Set.range (levelMonoidHom B T) = {x : Πʳ i, [G i, B i] | ∀ i ∉ T, x i ∈ B i} := by
  ext x
  simp only [mem_range, Set.mem_ofPred_eq]
  refine
    ⟨fun ⟨p, hp⟩ i hi ↦ hp ▸ (levelMonoidHom_apply_of_notMem B T p hi ▸ (p.2 ⟨i, hi⟩).property),
    fun hx ↦ ⟨((fun i : T ↦ x i.val), fun i : {i // i ∉ T} ↦ ⟨x i.val, hx i.val i.property⟩), ?_⟩⟩
  ext i
  by_cases hi : i ∈ T <;> simp [hi]

/-- `levelMonoidHom B T` is a topological embedding into `Πʳ i, [G i, B i]`. -/
@[to_additive /-- `levelAddMonoidHom B T` is a topological embedding into `Πʳ i, [G i, B i]`. -/]
theorem isEmbedding_levelMonoidHom : IsEmbedding (levelMonoidHom B T) :=
  (isEmbedding_inclusion_principal
    (le_principal_iff.mpr T.finite_toSet.compl_mem_cofinite)).comp
    (prodContinuousMulEquivPrincipal B T).toHomeomorph.isEmbedding

/-- The homomorphism `levelMonoidHom B T` is continuous. -/
@[to_additive (attr := continuity, fun_prop)
/-- The homomorphism `levelAddMonoidHom B T` is continuous. -/]
theorem continuous_levelMonoidHom : Continuous (levelMonoidHom B T) :=
  (isEmbedding_levelMonoidHom B T).continuous

/-- When the reference subobjects `B i` are open for every `i ∉ T`, `levelMonoidHom B T` is an
open topological embedding into `Πʳ i, [G i, B i]`; no openness is needed at the indices in `T`. -/
@[to_additive /-- When the reference additive subobjects `B i` are open for every `i ∉ T`,
`levelAddMonoidHom B T` is an open topological embedding into `Πʳ i, [G i, B i]`; no openness is
needed at the indices in `T`. -/]
theorem isOpenEmbedding_levelMonoidHom_of_isOpen (hB : ∀ i ∉ T, IsOpen (B i : Set (G i))) :
    IsOpenEmbedding (levelMonoidHom B T) :=
  (isOpenEmbedding_inclusion_principal_of_forall_mem
    (le_principal_iff.mpr T.finite_toSet.compl_mem_cofinite)
    fun i hi ↦ hB i (Finset.mem_coe.not.mp hi)).comp
    (prodContinuousMulEquivPrincipal B T).toHomeomorph.isOpenEmbedding

/-- When each reference subobject `B i` is open, `levelMonoidHom B T` is an open topological
embedding into `Πʳ i, [G i, B i]`. -/
@[to_additive /-- When each reference additive subobject `B i` is open, `levelAddMonoidHom B T` is
an open topological embedding into `Πʳ i, [G i, B i]`. -/]
theorem isOpenEmbedding_levelMonoidHom [hBopen : Fact (∀ i, IsOpen (B i : Set (G i)))] :
    IsOpenEmbedding (levelMonoidHom B T) :=
  isOpenEmbedding_levelMonoidHom_of_isOpen B T fun i _ ↦ hBopen.out i

/-- For any family of sets `C : ∀ i, Set (G i)` agreeing with `B i` outside `T`, the image of
`(Set.univ.pi fun i : T ↦ C i.1) ×ˢ Set.univ` under `levelMonoidHom B T` is `box C`. -/
@[to_additive image_levelAddMonoidHom_pi_prod_univ /-- For any family of sets `C : ∀ i, Set (G i)`
agreeing with `B i` outside `T`, the image of `(Set.univ.pi fun i : T ↦ C i.1) ×ˢ Set.univ` under
`levelAddMonoidHom B T` is `box C`. -/]
theorem image_levelMonoidHom_pi_prod_univ {C : ∀ i, Set (G i)} (hCB : ∀ i ∉ T, C i = B i) :
    levelMonoidHom B T '' ((univ.pi fun i : T ↦ C i.val) ×ˢ univ) =
      (box C : Set (Πʳ i, [G i, B i])) := by
  ext x
  simp only [mem_image, mem_prod, Set.mem_pi, mem_univ, forall_true_left, and_true, mem_box]
  refine ⟨?_, fun hx ↦
    ⟨((fun i : T ↦ x i.val), fun i ↦ ⟨x i.val, by simpa [hCB i.val i.property] using hx i.val⟩),
    fun i ↦ hx i.val, by ext i; by_cases hi : i ∈ T <;> simp [hi]⟩⟩
  rintro ⟨p, hp, rfl⟩ i
  by_cases hi : i ∈ T
  · simpa [hi] using hp ⟨i, hi⟩
  · rw [levelMonoidHom_apply_of_notMem B T p hi, hCB i hi]; exact (p.2 ⟨i, hi⟩).property

/-- The preimage of a coordinate box `box C` under `levelMonoidHom B T` is the product of the
finite box over `T` and the tail box outside `T`. -/
@[to_additive /-- The preimage of a coordinate box `box C` under `levelAddMonoidHom B T` is the
product of the finite box over `T` and the tail box outside `T`. -/]
theorem preimage_levelMonoidHom_box (C : ∀ i, Set (G i)) :
    levelMonoidHom B T ⁻¹' (box C : Set (Πʳ i, [G i, B i])) =
      (univ.pi fun i : T ↦ C i.val) ×ˢ
        (univ.pi fun j : {i // i ∉ T} ↦ ((↑) : B j.val → G j.val) ⁻¹' C j.val) := by
  classical
  have hcomp : ((↑) : Πʳ i, [G i, B i] → Π i, G i) ∘ levelMonoidHom B T =
      (Equiv.piEquivPiSubtypeProd (· ∈ T) G).symm ∘
        Prod.map id (fun g (j : {i // i ∉ T}) ↦ (g j : G j.val)) := by
    ext p i
    by_cases hi : i ∈ T <;> simp [hi]
  rw [← preimage_coe_univ_pi, ← Set.preimage_comp, hcomp, Set.preimage_comp,
    Equiv.preimage_piEquivPiSubtypeProd_symm_pi, Set.preimage_prod_map_prod,
    Set.preimage_id, Set.preimage_pi]

end Monoid

section OpenSubgroup

variable [∀ i, Group (G i)] [∀ i, SubgroupClass (K i) (G i)]

/-- For a finite set `S` of indices, the open subgroup `{x | ∀ i ∉ S, x i ∈ B i}` of
`Πʳ i, [G i, B i]` consisting of elements integral outside `S`. Only the reference subgroups
outside `S` need be open. -/
@[to_additive /-- For a finite set `S` of indices, the open additive subgroup
`{x | ∀ i ∉ S, x i ∈ B i}` of `Πʳ i, [G i, B i]` consisting of elements integral outside `S`. Only
the reference subgroups outside `S` need be open. -/]
def levelOpenSubgroup (B : ∀ i, K i) (S : Finset ι)
    (hB : ∀ i ∉ S, IsOpen (B i : Set (G i))) :
    OpenSubgroup (Πʳ i, [G i, B i]) where
  toSubgroup := (levelMonoidHom B S).range
  isOpen' := (isOpenEmbedding_levelMonoidHom_of_isOpen B S hB).isOpen_range

/-- The underlying set of `levelOpenSubgroup B S hB` is `{x | ∀ i ∉ S, x i ∈ B i}`. -/
@[to_additive (attr := simp) /-- The underlying set of `levelOpenAddSubgroup B S hB` is
`{x | ∀ i ∉ S, x i ∈ B i}`. -/]
theorem coe_levelOpenSubgroup (B : ∀ i, K i) (S : Finset ι)
    (hB : ∀ i ∉ S, IsOpen (B i : Set (G i))) :
    (levelOpenSubgroup B S hB : Set (Πʳ i, [G i, B i])) = {x | ∀ i ∉ S, x i ∈ B i} :=
  (MonoidHom.coe_range (levelMonoidHom B S)).trans (range_levelMonoidHom B S)

/-- Membership in `levelOpenSubgroup B S hB` means integrality at every index outside `S`. -/
@[to_additive (attr := simp) /-- Membership in `levelOpenAddSubgroup B S hB` means integrality at
every index outside `S`. -/]
theorem mem_levelOpenSubgroup (B : ∀ i, K i) (S : Finset ι)
    (hB : ∀ i ∉ S, IsOpen (B i : Set (G i))) (x : Πʳ i, [G i, B i]) :
    x ∈ levelOpenSubgroup B S hB ↔ ∀ i ∉ S, x i ∈ B i := by
  rw [← SetLike.mem_coe, coe_levelOpenSubgroup]
  rfl

/-- Enlarging the finite set `S` enlarges the level open subgroup. -/
@[to_additive /-- Enlarging the finite set `S` enlarges the level open additive subgroup. -/]
theorem levelOpenSubgroup_mono (B : ∀ i, K i) {S T : Finset ι} (hST : S ⊆ T)
    (hBS : ∀ i ∉ S, IsOpen (B i : Set (G i)))
    (hBT : ∀ i ∉ T, IsOpen (B i : Set (G i)) := fun i hi ↦ hBS i fun h ↦ hi (hST h)) :
    levelOpenSubgroup B S hBS ≤ levelOpenSubgroup B T hBT :=
  fun x hx ↦ (mem_levelOpenSubgroup B T hBT x).mpr fun i hi ↦
    (mem_levelOpenSubgroup B S hBS x).mp hx i fun h ↦ hi (hST h)

/-- At `S = ∅`, the level open subgroup consists of the everywhere-integral elements. -/
@[to_additive /-- At `S = ∅`, the level open additive subgroup consists of the everywhere-integral
elements. -/]
theorem coe_levelOpenSubgroup_empty (B : ∀ i, K i)
    (hB : ∀ i ∉ (∅ : Finset ι), IsOpen (B i : Set (G i))) :
    (levelOpenSubgroup B ∅ hB : Set (Πʳ i, [G i, B i])) = {x | ∀ i, x i ∈ B i} := by
  ext x
  simp

/-- The topological group isomorphism identifying the product
`(Π i : S, G i) × (Π j : {i // i ∉ S}, B j.val)` with the level open subgroup
`levelOpenSubgroup B S hB`. -/
@[to_additive /-- The topological additive group isomorphism identifying the product
`(Π i : S, G i) × (Π j : {i // i ∉ S}, B j.val)` with the level open additive subgroup
`levelOpenAddSubgroup B S hB`. -/]
def levelOpenSubgroupEquiv (B : ∀ i, K i) (S : Finset ι)
    (hB : ∀ i ∉ S, IsOpen (B i : Set (G i))) :
    ((Π i : S, G i) × (Π j : {i // i ∉ S}, B j.val)) ≃ₜ* levelOpenSubgroup B S hB :=
  let φ := (levelMonoidHom B S).rangeRestrict
  ContinuousMulEquiv.mk'
    (((Topology.IsEmbedding.of_comp_iff (f := φ) .subtypeVal).mp
      (isEmbedding_levelMonoidHom B S)).toHomeomorphOfSurjective
      (levelMonoidHom B S).rangeRestrict_surjective)
    (map_mul φ)

/-- Composing `levelOpenSubgroupEquiv B S hB` with the subtype inclusion into `Πʳ i, [G i, B i]`
recovers `levelMonoidHom B S`. -/
@[to_additive /-- Composing `levelOpenAddSubgroupEquiv B S hB` with the subtype inclusion into
`Πʳ i, [G i, B i]` recovers `levelAddMonoidHom B S`. -/]
theorem coe_comp_levelOpenSubgroupEquiv (B : ∀ i, K i) (S : Finset ι)
    (hB : ∀ i ∉ S, IsOpen (B i : Set (G i))) :
    ((↑) : levelOpenSubgroup B S hB → Πʳ i, [G i, B i]) ∘ levelOpenSubgroupEquiv B S hB =
      levelMonoidHom B S := by
  rfl

/-- Applying `levelOpenSubgroupEquiv B S hB` and coercing to `Πʳ i, [G i, B i]` agrees with
`levelMonoidHom B S`. -/
@[to_additive /-- Applying `levelOpenAddSubgroupEquiv B S hB` and coercing to `Πʳ i, [G i, B i]`
agrees with `levelAddMonoidHom B S`. -/]
theorem coe_levelOpenSubgroupEquiv (B : ∀ i, K i) (S : Finset ι)
    (hB : ∀ i ∉ S, IsOpen (B i : Set (G i)))
    (p : (Π i : S, G i) × (Π j : {i // i ∉ S}, B j.val)) :
    (levelOpenSubgroupEquiv B S hB p : Πʳ i, [G i, B i]) = levelMonoidHom B S p := by
  rfl

/-- On an index `i ∈ S`, `levelOpenSubgroupEquiv` reads from the first factor. -/
@[to_additive (attr := simp) /-- On an index `i ∈ S`, `levelOpenAddSubgroupEquiv` reads from the
first factor. -/]
theorem levelOpenSubgroupEquiv_apply_of_mem (B : ∀ i, K i) (S : Finset ι)
    (hB : ∀ i ∉ S, IsOpen (B i : Set (G i)))
    (p : (Π i : S, G i) × (Π j : {i // i ∉ S}, B j.val)) {i : ι} (hi : i ∈ S) :
    (levelOpenSubgroupEquiv B S hB p : Πʳ j, [G j, B j]) i = p.1 ⟨i, hi⟩ :=
  levelMonoidHom_apply_of_mem B S p hi

/-- On an index `i ∉ S`, `levelOpenSubgroupEquiv` reads from the second factor. -/
@[to_additive (attr := simp) /-- On an index `i ∉ S`, `levelOpenAddSubgroupEquiv` reads from the
second factor. -/]
theorem levelOpenSubgroupEquiv_apply_of_notMem (B : ∀ i, K i) (S : Finset ι)
    (hB : ∀ i ∉ S, IsOpen (B i : Set (G i)))
    (p : (Π i : S, G i) × (Π j : {i // i ∉ S}, B j.val)) {i : ι} (hi : i ∉ S) :
    (levelOpenSubgroupEquiv B S hB p : Πʳ j, [G j, B j]) i = (p.2 ⟨i, hi⟩ : G i) :=
  levelMonoidHom_apply_of_notMem B S p hi

/-- The first coordinate of `(levelOpenSubgroupEquiv B S hB).symm` evaluates on `S`. -/
@[to_additive (attr := simp) /-- The first coordinate of `(levelOpenAddSubgroupEquiv B S hB).symm`
evaluates on `S`. -/]
theorem levelOpenSubgroupEquiv_symm_fst (B : ∀ i, K i) (S : Finset ι)
    (hB : ∀ i ∉ S, IsOpen (B i : Set (G i))) (u : levelOpenSubgroup B S hB) (i : S) :
    ((levelOpenSubgroupEquiv B S hB).symm u).1 i = (u : Πʳ j, [G j, B j]) i.val := by
  rw [← levelOpenSubgroupEquiv_apply_of_mem B S hB _ i.property,
    (levelOpenSubgroupEquiv B S hB).apply_symm_apply]

/-- The second coordinate of `(levelOpenSubgroupEquiv B S hB).symm` evaluates outside `S`. -/
@[to_additive (attr := simp) /-- The second coordinate of `(levelOpenAddSubgroupEquiv B S hB).symm`
evaluates outside `S`. -/]
theorem levelOpenSubgroupEquiv_symm_snd (B : ∀ i, K i) (S : Finset ι)
    (hB : ∀ i ∉ S, IsOpen (B i : Set (G i))) (u : levelOpenSubgroup B S hB)
    (j : {i // i ∉ S}) :
    (((levelOpenSubgroupEquiv B S hB).symm u).2 j : G j.val) =
      (u : Πʳ k, [G k, B k]) j.val := by
  rw [← levelOpenSubgroupEquiv_apply_of_notMem B S hB _ j.property,
    (levelOpenSubgroupEquiv B S hB).apply_symm_apply]

/-- The preimage of a coordinate box `box C` under the inclusion of a level open subgroup composed
with `levelOpenSubgroupEquiv` is the product of the finite box over `S` and the tail box outside
`S`. -/
@[to_additive /-- The preimage of a coordinate box `box C` under the inclusion of a level open
additive subgroup composed with `levelOpenAddSubgroupEquiv` is the product of the finite box over
`S` and the tail box outside `S`. -/]
theorem preimage_coe_comp_levelOpenSubgroupEquiv_box (B : ∀ i, K i) (S : Finset ι)
    (hB : ∀ i ∉ S, IsOpen (B i : Set (G i))) (C : ∀ i, Set (G i)) :
    (((↑) : levelOpenSubgroup B S hB → Πʳ i, [G i, B i]) ∘ levelOpenSubgroupEquiv B S hB) ⁻¹'
      (box C : Set (Πʳ i, [G i, B i])) =
      (univ.pi fun i : S ↦ C i.val) ×ˢ
        (univ.pi fun j : {i // i ∉ S} ↦ ((↑) : B j.val → G j.val) ⁻¹' C j.val) := by
  rw [coe_comp_levelOpenSubgroupEquiv, preimage_levelMonoidHom_box]

end OpenSubgroup

end TauCeti
