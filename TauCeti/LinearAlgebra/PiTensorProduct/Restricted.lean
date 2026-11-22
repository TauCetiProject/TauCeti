/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Colimit.Module
public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.LinearAlgebra.PiTensorProduct.Basic

/-!
# Restricted tensor products of modules with reference vectors

Let `W i` be modules over a commutative semiring `R`, indexed by a possibly infinite type `ι`, and
let `w i ∈ W i` be reference vectors. For finite sets `S ⊆ T` of indices, adjoining the reference
vectors at the places of `T \ S` is a linear map

```text
⨂_{i ∈ S} W i → ⨂_{i ∈ T} W i,     ⨂ₜ f ↦ ⨂ₜ (f on S, w on T \ S).
```

These maps form a directed system over the finite subsets of `ι`, and the restricted tensor
product `TauCeti.RestrictedTensor R W w` is its direct limit. A family `f` of vectors with
`f i = w i` for all but finitely many `i` has a pure tensor
`TauCeti.RestrictedTensor.tprod R w f hf`; a family differing from the references at infinitely
many places has no such tensor.

The references are given at every place. Restricting to the cofinal stages containing a fixed
finite set `S₀` does not change the direct limit, and the transitions between those stages never
use the references at `S₀`; so arbitrary vectors may serve as references on a finite exceptional
set of places, where a distinguished vector need not exist. When the references
are nonzero vectors of vector spaces, or more generally are sent to `1` by linear forms, the
transition maps are injective (`TauCeti.RestrictedTensor.stageMap_injective`), so every finite
stage embeds in the restricted tensor product (`TauCeti.RestrictedTensor.ofFinite_injective`).
Without this hypothesis transitions can kill nonzero tensors: if `w j = 0`, adjoining the place
`j` is the zero map. For a finite index type the restricted tensor product is the ordinary tensor
product (`TauCeti.RestrictedTensor.finiteEquiv`).

## Main definitions

* `TauCeti.RestrictedTensor.stageMap`: the transition map adjoining reference vectors.
* `TauCeti.RestrictedTensor`: the restricted tensor product.
* `TauCeti.RestrictedTensor.ofFinite`: the inclusion of the tensor product over a finite stage.
* `TauCeti.RestrictedTensor.tprod`: the pure tensor of a family equal to the references at all
  but finitely many places.
* `TauCeti.RestrictedTensor.map`: the map induced by factorwise linear maps preserving the
  references.
* `TauCeti.RestrictedTensor.finiteEquiv`: for a finite index type, the restricted tensor product
  is the tensor product of all the factors.

## Main results

* `TauCeti.RestrictedTensor.exists_ofFinite`: every element comes from a finite stage.
* `TauCeti.RestrictedTensor.ofFinite_injective`: with nonzero references in vector spaces, the
  finite stages embed.
* `TauCeti.RestrictedTensor.tprod_eq_ofFinite`: a pure tensor computed at any finite stage
  containing the places where the family differs from the references.
* `TauCeti.RestrictedTensor.map_id`, `TauCeti.RestrictedTensor.map_comp`: the induced maps are
  functorial.
* `TauCeti.RestrictedTensor.finiteEquiv_apply_ofFinite`,
  `TauCeti.RestrictedTensor.finiteEquiv_symm_apply`: the identification for a finite index type,
  on finite stages and in the inverse direction.

## References

* D. Flath, *Decomposition of representations into tensor products*, in *Automorphic forms,
  representations and L-functions*, Proc. Sympos. Pure Math. **33**, Part 1 (1979), §2.
* J. R. Getz, *An introduction to automorphic representations*, §7.1.
-/

public noncomputable section

open scoped TensorProduct

namespace TauCeti

namespace RestrictedTensor

variable {ι : Type*} [DecidableEq ι] {W : ι → Type*}

/-- The family on `T` that agrees with `f` on `S` and with the reference vectors elsewhere. -/
def extendFamily (w : ∀ i, W i) {S : Finset ι} (T : Finset ι) (f : ∀ i : S, W i) :
    ∀ i : T, W i :=
  fun i ↦ if h : i.val ∈ S then f ⟨i.val, h⟩ else w i.val

/-- On `S`, the extended family is the original family. -/
theorem extendFamily_apply_of_mem (w : ∀ i, W i) {S : Finset ι} (T : Finset ι)
    (f : ∀ i : S, W i) (i : T) (h : i.val ∈ S) : extendFamily w T f i = f ⟨i.val, h⟩ :=
  by simp [extendFamily, h]

/-- Off `S`, the extended family is the reference family. -/
theorem extendFamily_apply_of_notMem (w : ∀ i, W i) {S : Finset ι} (T : Finset ι)
    (f : ∀ i : S, W i) (i : T) (h : i.val ∉ S) : extendFamily w T f i = w i.val :=
  by simp [extendFamily, h]

/-- Extending a family to its own index set does nothing. -/
theorem extendFamily_self (w : ∀ i, W i) (S : Finset ι) (f : ∀ i : S, W i) :
    extendFamily w S f = f :=
  funext fun i ↦ extendFamily_apply_of_mem w S f i i.property

/-- Extending by references in two steps is extending in one step. -/
theorem extendFamily_extendFamily (w : ∀ i, W i) {S T : Finset ι} (U : Finset ι) (h : S ⊆ T)
    (f : ∀ i : S, W i) : extendFamily w U (extendFamily w T f) = extendFamily w U f := by
  funext i
  by_cases hS : i.val ∈ S
  · rw [extendFamily_apply_of_mem w U _ i (h hS), extendFamily_apply_of_mem w T f _ hS,
      extendFamily_apply_of_mem w U f i hS]
  · rw [extendFamily_apply_of_notMem w U f i hS]
    by_cases hT : i.val ∈ T
    · rw [extendFamily_apply_of_mem w U _ i hT, extendFamily_apply_of_notMem w T f _ hS]
    · rw [extendFamily_apply_of_notMem w U _ i hT]

/-- Extending by references commutes with changing one entry of the family. -/
theorem extendFamily_update (w : ∀ i, W i) {S T : Finset ι} [DecidableEq S] [DecidableEq T]
    (h : S ⊆ T) (f : ∀ i : S, W i) (j : S) (x : W j) :
    extendFamily w T (Function.update f j x) =
      Function.update (extendFamily w T f) ⟨j.val, h j.property⟩ x := by
  funext i
  by_cases hij : i.val = j.val
  · obtain ⟨i, hi⟩ := i
    obtain ⟨j, hj⟩ := j
    subst hij
    simp [extendFamily, hj]
  · have hne : i ≠ ⟨j.val, h j.property⟩ := fun h' ↦ hij (congrArg Subtype.val h')
    rw [Function.update_of_ne hne]
    by_cases hS : i.val ∈ S
    · rw [extendFamily_apply_of_mem w T _ i hS, extendFamily_apply_of_mem w T f i hS,
        Function.update_of_ne fun h' ↦ hij (congrArg Subtype.val h')]
    · rw [extendFamily_apply_of_notMem w T _ i hS, extendFamily_apply_of_notMem w T f i hS]

/-- Extending by references commutes with factorwise maps sending references to references. -/
theorem extendFamily_comp {W' : ι → Type*} (w : ∀ i, W i) (w' : ∀ i, W' i)
    (f : ∀ i, W i → W' i) (hf : ∀ i, f i (w i) = w' i) {S : Finset ι} (T : Finset ι)
    (g : ∀ i : S, W i) :
    extendFamily w' T (fun i : S ↦ f i (g i)) = fun i : T ↦ f i (extendFamily w T g i) := by
  funext i
  by_cases hi : i.val ∈ S
  · rw [extendFamily_apply_of_mem w' T _ i hi, extendFamily_apply_of_mem w T g i hi]
  · rw [extendFamily_apply_of_notMem w' T _ i hi, extendFamily_apply_of_notMem w T g i hi, hf]

variable (R : Type*) [CommSemiring R] [∀ i, AddCommMonoid (W i)] [∀ i, Module R (W i)]

/-- Adjoining reference vectors, as a multilinear map. -/
def stageMultilinear (w : ∀ i, W i) {S T : Finset ι} (h : S ⊆ T) :
    (Π i : S, W i) →ₘₗ[R] ⨂[R] i : T, W i where
  toFun f := PiTensorProduct.tprod R (extendFamily w T f)
  map_update_add' f j x y := by
    simp only [extendFamily_update w h, MultilinearMap.map_update_add]
  map_update_smul' f j c x := by
    simp only [extendFamily_update w h, MultilinearMap.map_update_smul]

/-- Adjoining reference vectors to a family of vectors. -/
@[simp]
theorem stageMultilinear_apply (w : ∀ i, W i) {S T : Finset ι} (h : S ⊆ T) (f : ∀ i : S, W i) :
    stageMultilinear R w h f = PiTensorProduct.tprod R (extendFamily w T f) :=
  (rfl)

/-- The transition map `⨂_{i ∈ S} W i → ⨂_{i ∈ T} W i` adjoining the reference vectors at the
places of `T \ S`. -/
def stageMap (w : ∀ i, W i) {S T : Finset ι} (h : S ⊆ T) :
    (⨂[R] i : S, W i) →ₗ[R] ⨂[R] i : T, W i :=
  PiTensorProduct.lift (stageMultilinear R w h)

variable {R}

/-- The transition map on pure tensors. -/
@[simp]
theorem stageMap_tprod (w : ∀ i, W i) {S T : Finset ι} (h : S ⊆ T) (f : ∀ i : S, W i) :
    stageMap R w h (PiTensorProduct.tprod R f) = PiTensorProduct.tprod R (extendFamily w T f) :=
  PiTensorProduct.lift.tprod f

/-- The transition map from a stage to itself is the identity. -/
theorem stageMap_self (w : ∀ i, W i) (S : Finset ι) (x : ⨂[R] i : S, W i) :
    stageMap R w (subset_refl S) x = x := by
  induction x using PiTensorProduct.induction_on with
  | smul_tprod r f => rw [map_smul, stageMap_tprod, extendFamily_self]
  | add x y hx hy => rw [map_add, hx, hy]

/-- Transition maps compose. -/
theorem stageMap_stageMap (w : ∀ i, W i) {S T U : Finset ι} (hST : S ⊆ T) (hTU : T ⊆ U)
    (x : ⨂[R] i : S, W i) :
    stageMap R w hTU (stageMap R w hST x) = stageMap R w (hST.trans hTU) x := by
  induction x using PiTensorProduct.induction_on with
  | smul_tprod r f => simp only [map_smul, stageMap_tprod, extendFamily_extendFamily w U hST]
  | add x y hx hy => rw [map_add, map_add, hx, hy, map_add]

/-- The finite tensor products, with the transition maps adjoining references, form a directed
system. -/
instance directedSystem (w : ∀ i, W i) :
    DirectedSystem (fun S : Finset ι ↦ ⨂[R] i : S, W i)
      (fun _ _ h ↦ stageMap R w h) where
  map_self S x := stageMap_self w S x
  map_map _ _ _ hST hTU x := stageMap_stageMap w hST hTU x

section contract

variable {S T : Finset ι} (h : S ⊆ T)

/-- Changing an entry of the family at a place of `S` changes the contraction only in its tensor
factor. -/
private theorem contract_update_of_mem [DecidableEq T] (φ : ∀ i, Module.Dual R (W i))
    (g : ∀ i : T, W i) (j : T) (hj : j.val ∈ S) (z : W j) :
    (∏ i ∈ Finset.univ.filter (fun i : T ↦ i.val ∉ S), φ i (Function.update g j z i)) •
        PiTensorProduct.tprod R (fun i : S ↦ Function.update g j z ⟨i.val, h i.property⟩) =
      (∏ i ∈ Finset.univ.filter (fun i : T ↦ i.val ∉ S), φ i (g i)) •
        PiTensorProduct.tprod R
          (Function.update (fun i : S ↦ g ⟨i.val, h i.property⟩) ⟨j.val, hj⟩ z) := by
  have hres : (fun i : S ↦ Function.update g j z ⟨i.val, h i.property⟩) =
      Function.update (fun i : S ↦ g ⟨i.val, h i.property⟩) ⟨j.val, hj⟩ z :=
    Function.update_comp_eq_of_injective' g (f := fun i : S ↦ (⟨i.val, h i.property⟩ : T))
      (fun _ _ hab ↦ Subtype.ext (by simpa using hab)) ⟨j.val, hj⟩ z
  have hprod : ∏ i ∈ Finset.univ.filter (fun i : T ↦ i.val ∉ S), φ i (Function.update g j z i) =
      ∏ i ∈ Finset.univ.filter (fun i : T ↦ i.val ∉ S), φ i (g i) := by
    rw [Finset.prod_congr rfl fun i _ ↦ Function.apply_update (fun i : T ↦ ⇑(φ i)) g j z i]
    exact Finset.prod_update_of_notMem (by simp [hj]) _ _
  rw [hres, hprod]

/-- Changing an entry of the family at a place of `T \ S` changes the contraction only in its
scalar factor. -/
private theorem contract_update_of_notMem [DecidableEq T] (φ : ∀ i, Module.Dual R (W i))
    (g : ∀ i : T, W i) (j : T) (hj : j.val ∉ S) (z : W j) :
    (∏ i ∈ Finset.univ.filter (fun i : T ↦ i.val ∉ S), φ i (Function.update g j z i)) •
        PiTensorProduct.tprod R (fun i : S ↦ Function.update g j z ⟨i.val, h i.property⟩) =
      φ j z • (∏ i ∈ Finset.univ.filter (fun i : T ↦ i.val ∉ S) \ {j}, φ i (g i)) •
        PiTensorProduct.tprod R (fun i : S ↦ g ⟨i.val, h i.property⟩) := by
  have hres : (fun i : S ↦ Function.update g j z ⟨i.val, h i.property⟩) =
      fun i : S ↦ g ⟨i.val, h i.property⟩ :=
    Function.update_comp_eq_of_forall_ne' g z fun i hi ↦ hj (hi ▸ i.property)
  have hprod : ∏ i ∈ Finset.univ.filter (fun i : T ↦ i.val ∉ S), φ i (Function.update g j z i) =
      φ j z * ∏ i ∈ Finset.univ.filter (fun i : T ↦ i.val ∉ S) \ {j}, φ i (g i) := by
    rw [Finset.prod_congr rfl fun i _ ↦ Function.apply_update (fun i : T ↦ ⇑(φ i)) g j z i]
    exact Finset.prod_update_of_mem (by simp [hj]) _ _
  rw [hres, hprod, mul_smul]

variable (R) in
/-- Contracting the places of `T \ S` against linear forms, as a multilinear map. -/
def contractMultilinear (φ : ∀ i, Module.Dual R (W i)) :
    (Π i : T, W i) →ₘₗ[R] ⨂[R] i : S, W i where
  toFun g := (∏ i ∈ Finset.univ.filter (fun i : T ↦ i.val ∉ S), φ i (g i)) •
    PiTensorProduct.tprod R (fun i : S ↦ g ⟨i.val, h i.property⟩)
  map_update_add' g j x y := by
    by_cases hj : j.val ∈ S
    · simp only [contract_update_of_mem h φ g j hj, MultilinearMap.map_update_add, smul_add]
    · simp only [contract_update_of_notMem h φ g j hj, map_add, add_smul]
  map_update_smul' g j c x := by
    by_cases hj : j.val ∈ S
    · simp only [contract_update_of_mem h φ g j hj, MultilinearMap.map_update_smul]
      rw [smul_comm]
    · simp only [contract_update_of_notMem h φ g j hj, map_smul, smul_eq_mul, mul_smul,
        RingHom.id_apply]

/-- The contraction on a family of vectors. -/
theorem contractMultilinear_apply (φ : ∀ i, Module.Dual R (W i)) (g : ∀ i : T, W i) :
    contractMultilinear R h φ g = (∏ i ∈ Finset.univ.filter (fun i : T ↦ i.val ∉ S), φ i (g i)) •
      PiTensorProduct.tprod R (fun i : S ↦ g ⟨i.val, h i.property⟩) :=
  (rfl)

end contract

/-- If linear forms send the references at the places of `T \ S` to `1`, adjoining those
references is injective. -/
theorem stageMap_injective (w : ∀ i, W i) {S T : Finset ι} (h : S ⊆ T)
    (hw : ∀ i ∈ T, i ∉ S → ∃ φ : Module.Dual R (W i), φ (w i) = 1) :
    Function.Injective (stageMap R w h) := by
  choose! φ hφ using hw
  refine Function.LeftInverse.injective (g := PiTensorProduct.lift (contractMultilinear R h φ))
    fun x ↦ ?_
  induction x using PiTensorProduct.induction_on with
  | smul_tprod r f =>
    rw [map_smul, map_smul, stageMap_tprod, PiTensorProduct.lift.tprod]
    rw [contractMultilinear_apply, Finset.prod_eq_one, one_smul]
    · congr 2
      funext i
      exact extendFamily_apply_of_mem w T f ⟨i.val, h i.property⟩ i.property
    · intro i hi
      have hiS := (Finset.mem_filter.mp hi).2
      rw [extendFamily_apply_of_notMem w T f i hiS, hφ i i.property hiS]
  | add x y hx hy => rw [map_add, map_add, hx, hy]

end RestrictedTensor

variable {ι : Type*} [DecidableEq ι] (R : Type*) [CommSemiring R] (W : ι → Type*)
  [∀ i, AddCommMonoid (W i)] [∀ i, Module R (W i)]

/-- The **restricted tensor product** of modules `W i` with respect to reference vectors `w i`:
the direct limit, over finite sets `S` of indices, of the tensor products `⨂_{i ∈ S} W i`, along
the maps adjoining reference vectors. Its body is exposed so that the module structure of the direct
limit transfers to it. -/
@[expose]
def RestrictedTensor (w : ∀ i, W i) : Type _ :=
  Module.DirectLimit (fun S : Finset ι ↦ ⨂[R] i : S, W i)
    (fun _ _ h ↦ RestrictedTensor.stageMap R w h)

namespace RestrictedTensor

variable (w : ∀ i, W i)

/-- The restricted tensor product is a commutative monoid, as a direct limit. -/
instance instAddCommMonoid : AddCommMonoid (RestrictedTensor R W w) :=
  inferInstanceAs (AddCommMonoid (Module.DirectLimit _ _))

/-- The restricted tensor product is a module, as a direct limit. -/
instance instModule : Module R (RestrictedTensor R W w) :=
  inferInstanceAs (Module R (Module.DirectLimit _ _))

/-- The restricted tensor product of additive groups is an additive group. -/
instance instAddCommGroup {R : Type*} [CommRing R] {W : ι → Type*} [∀ i, AddCommGroup (W i)]
    [∀ i, Module R (W i)] (w : ∀ i, W i) : AddCommGroup (RestrictedTensor R W w) :=
  inferInstanceAs (AddCommGroup (Module.DirectLimit _ _))

/-- The inclusion of the tensor product over a finite stage into the restricted tensor
product. -/
def ofFinite (S : Finset ι) : (⨂[R] i : S, W i) →ₗ[R] RestrictedTensor R W w :=
  Module.DirectLimit.of R (Finset ι) (fun S : Finset ι ↦ ⨂[R] i : S, W i)
    (fun _ _ h ↦ stageMap R w h) S

variable {R W w}

/-- The finite-stage inclusions are compatible with the transition maps. -/
@[simp]
theorem ofFinite_stageMap {S T : Finset ι} (h : S ⊆ T) (x : ⨂[R] i : S, W i) :
    ofFinite R W w T (stageMap R w h x) = ofFinite R W w S x :=
  Module.DirectLimit.of_f

/-- Every element of the restricted tensor product comes from a finite stage. -/
theorem exists_ofFinite (z : RestrictedTensor R W w) :
    ∃ (S : Finset ι) (x : ⨂[R] i : S, W i), ofFinite R W w S x = z :=
  Module.DirectLimit.exists_of z

/-- Two linear maps out of the restricted tensor product agreeing on every finite stage are
equal. -/
@[ext]
theorem hom_ext {P : Type*} [AddCommMonoid P] [Module R P]
    {g₁ g₂ : RestrictedTensor R W w →ₗ[R] P}
    (h : ∀ S, g₁ ∘ₗ ofFinite R W w S = g₂ ∘ₗ ofFinite R W w S) : g₁ = g₂ :=
  Module.DirectLimit.hom_ext h

/-- The linear map out of the restricted tensor product induced by compatible linear maps out of
the finite stages. -/
def lift {P : Type*} [AddCommMonoid P] [Module R P]
    (g : ∀ S : Finset ι, (⨂[R] i : S, W i) →ₗ[R] P)
    (hg : ∀ (S T : Finset ι) (h : S ⊆ T) x, g T (stageMap R w h x) = g S x) :
    RestrictedTensor R W w →ₗ[R] P :=
  Module.DirectLimit.lift R (Finset ι) _ _ g hg

/-- The induced map on a finite stage. -/
@[simp]
theorem lift_ofFinite {P : Type*} [AddCommMonoid P] [Module R P]
    (g : ∀ S : Finset ι, (⨂[R] i : S, W i) →ₗ[R] P)
    (hg : ∀ (S T : Finset ι) (h : S ⊆ T) x, g T (stageMap R w h x) = g S x)
    (S : Finset ι) (x : ⨂[R] i : S, W i) : lift g hg (ofFinite R W w S x) = g S x :=
  Module.DirectLimit.lift_of _ _ _

/-- If linear forms send the references outside a finite set `S` to `1`, the tensor product over
`S` embeds in the restricted tensor product. -/
theorem ofFinite_injective' (S : Finset ι)
    (hw : ∀ i ∉ S, ∃ φ : Module.Dual R (W i), φ (w i) = 1) :
    Function.Injective (ofFinite R W w S) := by
  intro x y hxy
  obtain ⟨T, hST, hT⟩ := Module.DirectLimit.exists_eq_of_of_eq hxy
  exact stageMap_injective w hST (fun i _ hi ↦ hw i hi) hT

/-- With nonzero references outside a finite set `S` of places, the tensor product of vector
spaces over `S` embeds in the restricted tensor product. -/
theorem ofFinite_injective {K : Type*} [Field K] {V : ι → Type*} [∀ i, AddCommGroup (V i)]
    [∀ i, Module K (V i)] {v : ∀ i, V i} (S : Finset ι) (hv : ∀ i ∉ S, v i ≠ 0) :
    Function.Injective (ofFinite K V v S) :=
  ofFinite_injective' S fun i hi ↦ Module.Projective.exists_dual_eq_one K (hv i hi)

variable (R w) in
/-- The pure tensor `⨂ₜ f` of a family `f` equal to the references at all but finitely many
places, computed at the finite stage of the places where `f` differs from the references. -/
def tprod (f : ∀ i, W i) (hf : {i | f i ≠ w i}.Finite) : RestrictedTensor R W w :=
  ofFinite R W w hf.toFinset (PiTensorProduct.tprod R fun i ↦ f i)

/-- A pure tensor of the restricted tensor product can be computed at any finite stage containing
the places where the family differs from the references. -/
theorem tprod_eq_ofFinite (f : ∀ i, W i) (hf : {i | f i ≠ w i}.Finite) (S : Finset ι)
    (hS : ∀ i ∉ S, f i = w i) :
    tprod R w f hf = ofFinite R W w S (PiTensorProduct.tprod R fun i ↦ f i) := by
  have hsub : hf.toFinset ⊆ S := fun i hi ↦ by
    by_contra h
    exact (hf.mem_toFinset.mp hi) (hS i h)
  have key : ∀ U (h : U ⊆ S), (∀ i ∉ U, f i = w i) →
      stageMap R w h (PiTensorProduct.tprod R fun i : U ↦ f i) =
        PiTensorProduct.tprod R fun i : S ↦ f i := by
    intro U h hU
    rw [stageMap_tprod]
    congr 1
    funext i
    by_cases hi : i.val ∈ U
    · exact extendFamily_apply_of_mem w S _ i hi
    · rw [extendFamily_apply_of_notMem w S _ i hi, hU i hi]
  rw [tprod, ← key hf.toFinset hsub fun i hi ↦ ?_, ofFinite_stageMap]
  by_contra h
  exact hi (hf.mem_toFinset.mpr h)

/-- The pure tensor of the reference family is the image of the empty pure tensor at the empty
stage. -/
theorem tprod_ref : tprod R w w (by simp) =
    ofFinite R W w ∅ (PiTensorProduct.tprod R fun i ↦ w i) :=
  tprod_eq_ofFinite w _ ∅ fun _ _ ↦ rfl

section map

variable {W' : ι → Type*} [∀ i, AddCommMonoid (W' i)] [∀ i, Module R (W' i)] {w' : ∀ i, W' i}

/-- Linear maps `f i : W i → W' i` sending the references to the references induce a linear map
of restricted tensor products, `⨂ₜ g ↦ ⨂ₜ (f i (g i))`. -/
def map (f : ∀ i, W i →ₗ[R] W' i) (hf : ∀ i, f i (w i) = w' i) :
    RestrictedTensor R W w →ₗ[R] RestrictedTensor R W' w' :=
  lift (fun S ↦ ofFinite R W' w' S ∘ₗ PiTensorProduct.map fun i : S ↦ f i) fun S T h x ↦ by
    induction x using PiTensorProduct.induction_on with
    | smul_tprod r g =>
      simp only [map_smul, LinearMap.comp_apply, stageMap_tprod, PiTensorProduct.map_tprod]
      rw [← extendFamily_comp w w' (fun i ↦ f i) hf, ← stageMap_tprod w' h, ofFinite_stageMap]
    | add x y hx hy => rw [map_add, map_add, hx, hy, map_add]

/-- The induced map on a finite stage is the tensor map of the factors. -/
@[simp]
theorem map_ofFinite (f : ∀ i, W i →ₗ[R] W' i) (hf : ∀ i, f i (w i) = w' i) (S : Finset ι)
    (x : ⨂[R] i : S, W i) :
    map f hf (ofFinite R W w S x) =
      ofFinite R W' w' S (PiTensorProduct.map (fun i : S ↦ f i) x) :=
  lift_ofFinite _ _ S x

/-- The induced map on pure tensors. -/
theorem map_tprod (f : ∀ i, W i →ₗ[R] W' i) (hf : ∀ i, f i (w i) = w' i) (g : ∀ i, W i)
    (hg : {i | g i ≠ w i}.Finite) :
    map f hf (tprod R w g hg) = tprod R w' (fun i ↦ f i (g i))
      (hg.subset fun i hi h ↦ hi (by rw [h, hf])) := by
  rw [tprod, map_ofFinite, PiTensorProduct.map_tprod,
    tprod_eq_ofFinite _ _ hg.toFinset fun i hi ↦ ?_]
  rw [Set.Finite.mem_toFinset, Set.mem_ofPred_eq, not_not] at hi
  rw [hi, hf]

variable (w) in
/-- The identity maps of the factors induce the identity. -/
@[simp]
theorem map_id :
    map (w := w) (fun i ↦ (LinearMap.id : W i →ₗ[R] W i)) (fun _ ↦ rfl) = LinearMap.id :=
  hom_ext fun S ↦ LinearMap.ext fun x ↦ by simp [PiTensorProduct.map_id]

/-- The map induced by composites of factorwise maps is the composite of the induced maps. -/
theorem map_comp {W'' : ι → Type*} [∀ i, AddCommMonoid (W'' i)] [∀ i, Module R (W'' i)]
    {w'' : ∀ i, W'' i} (g : ∀ i, W' i →ₗ[R] W'' i) (hg : ∀ i, g i (w' i) = w'' i)
    (f : ∀ i, W i →ₗ[R] W' i) (hf : ∀ i, f i (w i) = w' i) :
    map (fun i ↦ g i ∘ₗ f i) (fun i ↦ by rw [LinearMap.comp_apply, hf, hg]) =
      map g hg ∘ₗ map f hf :=
  hom_ext fun S ↦ LinearMap.ext fun x ↦ by simp [PiTensorProduct.map_comp]

/-- Applying two induced maps in turn is applying the map induced by the composites. -/
@[simp]
theorem map_map {W'' : ι → Type*} [∀ i, AddCommMonoid (W'' i)] [∀ i, Module R (W'' i)]
    {w'' : ∀ i, W'' i} (g : ∀ i, W' i →ₗ[R] W'' i) (hg : ∀ i, g i (w' i) = w'' i)
    (f : ∀ i, W i →ₗ[R] W' i) (hf : ∀ i, f i (w i) = w' i) (x : RestrictedTensor R W w) :
    map g hg (map f hf x) =
      map (fun i ↦ g i ∘ₗ f i) (fun i ↦ by rw [LinearMap.comp_apply, hf, hg]) x := by
  rw [map_comp, LinearMap.comp_apply]

end map

variable (R W w) in
/-- For a finite index type, the restricted tensor product is the tensor product of all the
factors: every finite stage maps to the full stage by adjoining reference vectors. -/
def finiteEquiv [Fintype ι] : RestrictedTensor R W w ≃ₗ[R] ⨂[R] i, W i :=
  LinearEquiv.trans
    { lift (fun S ↦ stageMap R w (Finset.subset_univ S))
        (fun S T h x ↦ stageMap_stageMap w h (Finset.subset_univ T) x) with
      invFun := ofFinite R W w Finset.univ
      left_inv z := by
        obtain ⟨S, x, rfl⟩ := exists_ofFinite z
        simp
      right_inv x := by simp [stageMap_self] }
    (PiTensorProduct.reindex R (fun i : (Finset.univ : Finset ι) ↦ W i)
      (Equiv.subtypeUnivEquiv Finset.mem_univ))

/-- For a finite index type, an element of a stage `S` is sent to the full stage by adjoining
references, then reindexed by `Finset.univ ≃ ι`. -/
theorem finiteEquiv_apply_ofFinite [Fintype ι] (S : Finset ι) (x : ⨂[R] i : S, W i) :
    finiteEquiv R W w (ofFinite R W w S x) =
      PiTensorProduct.reindex R (fun i : (Finset.univ : Finset ι) ↦ W i)
        (Equiv.subtypeUnivEquiv Finset.mem_univ) (stageMap R w (Finset.subset_univ S) x) :=
  congrArg (PiTensorProduct.reindex R _ _)
    (lift_ofFinite (fun S ↦ stageMap R w (Finset.subset_univ S))
      (fun _ T h x ↦ stageMap_stageMap w h (Finset.subset_univ T) x) S x)

/-- For a finite index type, the inverse of `finiteEquiv` reindexes by `ι ≃ Finset.univ` and
includes the full stage. -/
theorem finiteEquiv_symm_apply [Fintype ι] (x : ⨂[R] i, W i) :
    (finiteEquiv R W w).symm x = ofFinite R W w Finset.univ
      ((PiTensorProduct.reindex R (fun i : (Finset.univ : Finset ι) ↦ W i)
        (Equiv.subtypeUnivEquiv Finset.mem_univ)).symm x) :=
  (rfl)

/-- For a finite index type, a pure tensor at a stage `S` corresponds to the pure tensor of the
family extended by references. -/
theorem finiteEquiv_ofFinite [Fintype ι] (S : Finset ι) (f : ∀ i : S, W i) :
    finiteEquiv R W w (ofFinite R W w S (PiTensorProduct.tprod R f)) =
      PiTensorProduct.tprod R fun i ↦ extendFamily w Finset.univ f ⟨i, Finset.mem_univ i⟩ := by
  rw [finiteEquiv_apply_ofFinite, stageMap_tprod, PiTensorProduct.reindex_tprod]
  rfl

end RestrictedTensor

end TauCeti
