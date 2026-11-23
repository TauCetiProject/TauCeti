/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.ContinuousMonoidHom
public import TauCeti.Topology.Algebra.RestrictedProduct.Box

/-!
# Principal-level product decomposition of restricted products

For any finite set `T : Finset ι` and submonoid-like reference sets `B : ∀ i, K i` in topological
monoids `G i`, the principal stage `Πʳ i, [G i, B i]_[𝓟 (T : Set ι)ᶜ]` splits via a topological
monoid isomorphism `TauCeti.prodContinuousMulEquivPrincipal` from
`(Π i : T, G i) × (Π i : {i // i ∉ T}, B i)`. Composing with the principal inclusion into
`Πʳ i, [G i, B i]` yields `TauCeti.levelMonoidHom`, which is always a topological embedding and is
an open embedding when `B i` is open for every `i ∉ T`. Every declaration has an additive
counterpart via `@[to_additive]`.

## Main definitions and results

* `TauCeti.prodContinuousMulEquivPrincipal`: topological monoid isomorphism
  `((Π i : T, G i) × (Π i : {i // i ∉ T}, B i)) ≃ₜ* Πʳ i, [G i, B i]_[𝓟 (T : Set ι)ᶜ]`, with
  coordinate and `.symm` projection lemmas.
* `TauCeti.levelMonoidHom`, `TauCeti.range_levelMonoidHom`: canonical monoid homomorphism into
  `Πʳ i, [G i, B i]` and its range `{x | ∀ i ∉ T, x i ∈ B i}`.
* `TauCeti.isEmbedding_levelMonoidHom`, `TauCeti.isOpenEmbedding_levelMonoidHom_of_isOpen`,
  `TauCeti.isOpenEmbedding_levelMonoidHom`: topological and open embedding properties of
  `levelMonoidHom`; openness of `B i` is only needed outside `T`.
* `TauCeti.image_levelMonoidHom_pi_prod_univ`: image of `(Set.univ.pi ...) ×ˢ Set.univ` under
  `levelMonoidHom B T` is `RestrictedProduct.box C` when `C i = B i` outside `T`.
-/

public section

noncomputable section

open Filter RestrictedProduct Set Topology
open scoped RestrictedProduct

namespace TauCeti

variable {ι : Type*} {G : ι → Type*} {K : ι → Type*} [∀ i, SetLike (K i) (G i)]
variable [∀ i, Monoid (G i)] [∀ i, SubmonoidClass (K i) (G i)] [∀ i, TopologicalSpace (G i)]
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

end TauCeti
