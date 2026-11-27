/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Colimit.Module
public import Mathlib.LinearAlgebra.Dual.Lemmas
public import TauCeti.Data.Finset.Update
public import TauCeti.LinearAlgebra.PiTensorProduct.Contraction

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
* `TauCeti.RestrictedTensor.congr`: the equivalence induced by factorwise linear equivalences
  preserving the references.
* `TauCeti.RestrictedTensor.univStageEquiv`: for a finite index type, the restricted tensor
  product is the tensor product over the full stage `Finset.univ`.
* `TauCeti.RestrictedTensor.finiteEquiv`: for a finite index type, the restricted tensor product
  is the tensor product of all the factors.

## Main results

* `TauCeti.RestrictedTensor.exists_ofFinite`: every element comes from a finite stage.
* `TauCeti.RestrictedTensor.ofFinite_eq_ofFinite_iff`: two elements of finite stages have the same
  image exactly when they agree at a common larger stage.
* `TauCeti.RestrictedTensor.ofFinite_injective`: with nonzero references in vector spaces, the
  finite stages embed.
* `TauCeti.RestrictedTensor.tprod_eq_ofFinite`: a pure tensor computed at any finite stage
  containing the places where the family differs from the references.
* `TauCeti.RestrictedTensor.tprod_update_add`, `TauCeti.RestrictedTensor.tprod_update_smul`,
  `TauCeti.RestrictedTensor.tprod_coord_zero`: pure tensors are multilinear in the entries.
* `TauCeti.RestrictedTensor.map_id`, `TauCeti.RestrictedTensor.map_comp`: the induced maps are
  functorial.
* `TauCeti.RestrictedTensor.congr_symm`, `TauCeti.RestrictedTensor.congr_refl`,
  `TauCeti.RestrictedTensor.congr_trans`: the induced equivalences are functorial.
* `TauCeti.RestrictedTensor.finiteEquiv_apply_ofFinite`,
  `TauCeti.RestrictedTensor.finiteEquiv_symm_apply`: the identification for a finite index type,
  on finite stages and in the inverse direction.
* `TauCeti.RestrictedTensor.finiteEquiv_tprod`, `TauCeti.RestrictedTensor.finiteEquiv_symm_tprod`:
  the identification matches the pure tensors of the same family.

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

variable (R : Type*) [CommSemiring R] [∀ i, AddCommMonoid (W i)] [∀ i, Module R (W i)]

/-- Adjoining reference vectors, as a multilinear map: the pure tensor over `T` with the slots of
`T \ S` fixed to the references, reindexed by `S`. -/
def stageMultilinear (w : ∀ i, W i) {S T : Finset ι} (h : S ⊆ T) :
    (Π i : S, W i) →ₘₗ[R] ⨂[R] i : T, W i :=
  MultilinearMap.domDomCongrLinearEquiv' R (RingHom.id R) (fun i : {a : T // a.val ∈ S} ↦ W i)
    _ (Equiv.subtypeSubtypeEquivSubtype (p := (· ∈ T)) (q := (· ∈ S)) (h ·))
    ((PiTensorProduct.tprod R (s := fun i : T ↦ W i)).domDomRestrict (fun i : T ↦ i.val ∈ S)
      fun i ↦ w i)

/-- Adjoining reference vectors to a family of vectors. -/
@[simp]
theorem stageMultilinear_apply (w : ∀ i, W i) {S T : Finset ι} (h : S ⊆ T) (f : ∀ i : S, W i) :
    stageMultilinear R w h f =
      PiTensorProduct.tprod R (T.restrict (Function.updateFinset w S f)) := by
  refine congrArg (PiTensorProduct.tprod R) (funext fun i ↦ ?_)
  by_cases hi : i.val ∈ S
  · simp only [Finset.restrict, Function.updateFinset_apply_of_mem hi, dite_eq_left hi]
    -- The inverse of `Equiv.subtypeSubtypeEquivSubtype` sends `⟨i, hi⟩` to `⟨i, hi⟩` by
    -- definition, so the reindexed entry is `f ⟨i, hi⟩`; the dependent type of the entry
    -- blocks rewriting with `Equiv.piCongrLeft'_symm_apply_apply`.
    rfl
  · simp [hi]

/-- The transition map `⨂_{i ∈ S} W i → ⨂_{i ∈ T} W i` adjoining the reference vectors at the
places of `T \ S`. -/
def stageMap (w : ∀ i, W i) {S T : Finset ι} (h : S ⊆ T) :
    (⨂[R] i : S, W i) →ₗ[R] ⨂[R] i : T, W i :=
  PiTensorProduct.lift (stageMultilinear R w h)

variable {R}

/-- The transition map on pure tensors. -/
@[simp]
theorem stageMap_tprod (w : ∀ i, W i) {S T : Finset ι} (h : S ⊆ T) (f : ∀ i : S, W i) :
    stageMap R w h (PiTensorProduct.tprod R f) =
      PiTensorProduct.tprod R (T.restrict (Function.updateFinset w S f)) := by
  rw [stageMap, PiTensorProduct.lift.tprod, stageMultilinear_apply]

/-- The transition map from a stage to itself is the identity. -/
@[simp]
theorem stageMap_self (w : ∀ i, W i) (S : Finset ι) (x : ⨂[R] i : S, W i) :
    stageMap R w (subset_refl S) x = x :=
  LinearMap.congr_fun (g := LinearMap.id) (PiTensorProduct.ext <| MultilinearMap.ext fun f ↦ by
    simp [Function.restrict_updateFinset]) x

/-- Transition maps compose. -/
@[simp]
theorem stageMap_stageMap (w : ∀ i, W i) {S T U : Finset ι} (hST : S ⊆ T) (hTU : T ⊆ U)
    (x : ⨂[R] i : S, W i) :
    stageMap R w hTU (stageMap R w hST x) = stageMap R w (hST.trans hTU) x :=
  LinearMap.congr_fun (f := stageMap R w hTU ∘ₗ stageMap R w hST)
    (PiTensorProduct.ext <| MultilinearMap.ext fun f ↦ by
      simp [← Function.updateFinset_updateFinset_of_subset hST w f]) x

/-- The finite tensor products, with the transition maps adjoining references, form a directed
system. -/
instance directedSystem (w : ∀ i, W i) :
    DirectedSystem (fun S : Finset ι ↦ ⨂[R] i : S, W i)
      (fun _ _ h ↦ stageMap R w h) where
  map_self S x := stageMap_self w S x
  map_map _ _ _ hST hTU x := stageMap_stageMap w hST hTU x

/-- If linear forms send the references at the places of `T \ S` to `1`, adjoining those
references is injective. -/
theorem stageMap_injective (w : ∀ i, W i) {S T : Finset ι} (h : S ⊆ T)
    (hw : ∀ i ∈ T, i ∉ S → ∃ φ : Module.Dual R (W i), φ (w i) = 1) :
    Function.Injective (stageMap R w h) := by
  choose! φ hφ using hw
  have hinv :
      PiTensorProduct.lift (PiTensorProduct.contractMultilinear R h φ) ∘ₗ stageMap R w h =
        LinearMap.id := by
    refine PiTensorProduct.ext <| MultilinearMap.ext fun f ↦ ?_
    have hprod : ∏ i : {i : T // i.val ∉ S}, φ i (Function.updateFinset w S f i) = 1 :=
      Fintype.prod_eq_one _ fun i ↦ by
        simp [Function.updateFinset_apply_of_notMem i.property, hφ i i.val.property i.property]
    simp only [LinearMap.compMultilinearMap_apply, LinearMap.coe_comp, Function.comp_apply,
      stageMap_tprod, PiTensorProduct.lift.tprod, LinearMap.id_compMultilinearMap,
      PiTensorProduct.contractMultilinear_apply, Finset.restrict, hprod, one_smul]
    -- The remaining family `fun i : S ↦ Function.updateFinset w S f i` is
    -- `S.restrict (Function.updateFinset w S f)` by definition of `Finset.restrict`.
    exact congrArg _ (Function.restrict_updateFinset w f)
  exact Function.LeftInverse.injective (LinearMap.congr_fun hinv)

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

/-- Two elements of finite stages have the same image in the restricted tensor product exactly
when they agree after adjoining references up to a common larger stage. -/
theorem ofFinite_eq_ofFinite_iff {S T : Finset ι} (x : ⨂[R] i : S, W i) (y : ⨂[R] i : T, W i) :
    ofFinite R W w S x = ofFinite R W w T y ↔
      ∃ (U : Finset ι) (hSU : S ⊆ U) (hTU : T ⊆ U), stageMap R w hSU x = stageMap R w hTU y := by
  refine ⟨fun hxy ↦ ?_, fun ⟨U, hSU, hTU, hU⟩ ↦ ?_⟩
  · rw [← ofFinite_stageMap Finset.subset_union_left x,
      ← ofFinite_stageMap Finset.subset_union_right y] at hxy
    obtain ⟨U, hU, hxyU⟩ := Module.DirectLimit.exists_eq_of_of_eq hxy
    refine ⟨U, Finset.subset_union_left.trans hU, Finset.subset_union_right.trans hU, ?_⟩
    rwa [stageMap_stageMap, stageMap_stageMap] at hxyU
  · rw [← ofFinite_stageMap hSU, hU, ofFinite_stageMap]

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
  have hsub : hf.toFinset ⊆ S := fun i hi ↦ by_contra fun h ↦ by simp [hS i h] at hi
  have key : ∀ U (h : U ⊆ S), (∀ i ∉ U, f i = w i) →
      stageMap R w h (PiTensorProduct.tprod R fun i : U ↦ f i) =
        PiTensorProduct.tprod R fun i : S ↦ f i := by
    intro U h hU
    rw [stageMap_tprod]
    congr 1
    funext i
    by_cases hi : i.val ∈ U
    · simp [Function.updateFinset_apply_of_mem hi]
    · simp [Function.updateFinset_apply_of_notMem hi, hU i hi]
  rw [tprod, ← key hf.toFinset hsub fun i hi ↦ by simpa using hi, ofFinite_stageMap]

/-- The pure tensor of the reference family is the image of the empty pure tensor at the empty
stage. -/
theorem tprod_ref : tprod R w w (by simp) =
    ofFinite R W w ∅ (PiTensorProduct.tprod R fun i ↦ w i) :=
  tprod_eq_ofFinite w _ ∅ fun _ _ ↦ rfl

/-- A finite stage on which the pure tensors of all the families `Function.update f j z`
can be computed, as pure tensors of the corresponding updates of the restriction of `f`. -/
private theorem exists_tprod_update (f : ∀ i, W i) (j : ι) {z₀ : W j}
    (h₀ : {i | Function.update f j z₀ i ≠ w i}.Finite) :
    ∃ (S : Finset ι) (hj : j ∈ S), ∀ (z : W j) (hz : {i | Function.update f j z i ≠ w i}.Finite),
      tprod R w (Function.update f j z) hz = ofFinite R W w S
        (PiTensorProduct.tprod R (Function.update (fun i : S ↦ f i) ⟨j, hj⟩ z)) := by
  refine ⟨insert j h₀.toFinset, Finset.mem_insert_self j _, fun z hz ↦ ?_⟩
  rw [tprod_eq_ofFinite _ hz _ fun i hi ↦ ?_,
    ← Function.update_comp_eq_of_injective' f Subtype.val_injective]
  obtain ⟨hij, hi⟩ := not_or.mp (Finset.mem_insert.not.mp hi)
  rw [Function.update_of_ne hij, ← Function.update_of_ne hij z₀ f]
  simpa using hi

/-- A pure tensor is additive in each entry. -/
theorem tprod_update_add (f : ∀ i, W i) (j : ι) (x y : W j)
    (hxy : {i | Function.update f j (x + y) i ≠ w i}.Finite)
    (hx : {i | Function.update f j x i ≠ w i}.Finite)
    (hy : {i | Function.update f j y i ≠ w i}.Finite) :
    tprod R w (Function.update f j (x + y)) hxy =
      tprod R w (Function.update f j x) hx + tprod R w (Function.update f j y) hy := by
  obtain ⟨S, hj, hS⟩ := exists_tprod_update (R := R) f j hxy
  rw [hS, hS, hS, MultilinearMap.map_update_add, map_add]

/-- A pure tensor is homogeneous in each entry. -/
theorem tprod_update_smul (f : ∀ i, W i) (j : ι) (c : R) (x : W j)
    (hcx : {i | Function.update f j (c • x) i ≠ w i}.Finite)
    (hx : {i | Function.update f j x i ≠ w i}.Finite) :
    tprod R w (Function.update f j (c • x)) hcx = c • tprod R w (Function.update f j x) hx := by
  obtain ⟨S, hj, hS⟩ := exists_tprod_update (R := R) f j hcx
  rw [hS, hS, MultilinearMap.map_update_smul, map_smul, RingHom.id_apply]

/-- A pure tensor with a zero entry vanishes. -/
theorem tprod_coord_zero (f : ∀ i, W i) (hf : {i | f i ≠ w i}.Finite) (j : ι) (hj : f j = 0) :
    tprod R w f hf = 0 := by
  rw [tprod_eq_ofFinite f hf (insert j hf.toFinset) fun i hi ↦ ?_,
    MultilinearMap.map_coord_zero _ ⟨j, Finset.mem_insert_self j _⟩ hj, map_zero]
  simpa using (not_or.mp (Finset.mem_insert.not.mp hi)).2

section map

variable {W' : ι → Type*} [∀ i, AddCommMonoid (W' i)] [∀ i, Module R (W' i)] {w' : ∀ i, W' i}

/-- The tensor maps of factorwise maps sending the references to the references commute with the
transition maps. -/
private theorem map_comp_stageMap (f : ∀ i, W i →ₗ[R] W' i) (hf : ∀ i, f i (w i) = w' i)
    (S T : Finset ι) (h : S ⊆ T) :
    PiTensorProduct.map (fun i : T ↦ f i) ∘ₗ stageMap R w h =
      stageMap R w' h ∘ₗ PiTensorProduct.map fun i : S ↦ f i :=
  PiTensorProduct.ext <| MultilinearMap.ext fun g ↦ by
    simp only [LinearMap.compMultilinearMap_apply, LinearMap.coe_comp, Function.comp_apply,
      stageMap_tprod, PiTensorProduct.map_tprod]
    congr 1
    funext i
    by_cases hi : i.val ∈ S
    · simp [Function.updateFinset_apply_of_mem hi]
    · simp [Function.updateFinset_apply_of_notMem hi, hf]

/-- Linear maps `f i : W i → W' i` sending the references to the references induce a linear map
of restricted tensor products, `⨂ₜ g ↦ ⨂ₜ (f i (g i))`. -/
def map (f : ∀ i, W i →ₗ[R] W' i) (hf : ∀ i, f i (w i) = w' i) :
    RestrictedTensor R W w →ₗ[R] RestrictedTensor R W' w' :=
  Module.DirectLimit.map (fun S : Finset ι ↦ PiTensorProduct.map fun i : S ↦ f i)
    (map_comp_stageMap f hf)

/-- The induced map on a finite stage is the tensor map of the factors. -/
@[simp]
theorem map_ofFinite (f : ∀ i, W i →ₗ[R] W' i) (hf : ∀ i, f i (w i) = w' i) (S : Finset ι)
    (x : ⨂[R] i : S, W i) :
    map f hf (ofFinite R W w S x) =
      ofFinite R W' w' S (PiTensorProduct.map (fun i : S ↦ f i) x) :=
  Module.DirectLimit.map_apply_of (fun S : Finset ι ↦ PiTensorProduct.map fun i : S ↦ f i)
    (map_comp_stageMap f hf) x

/-- The induced map on pure tensors. -/
@[simp]
theorem map_tprod (f : ∀ i, W i →ₗ[R] W' i) (hf : ∀ i, f i (w i) = w' i) (g : ∀ i, W i)
    (hg : {i | g i ≠ w i}.Finite) :
    map f hf (tprod R w g hg) = tprod R w' (fun i ↦ f i (g i))
      (hg.subset fun i hi h ↦ hi (by rw [h, hf])) := by
  rw [tprod, map_ofFinite, PiTensorProduct.map_tprod,
    tprod_eq_ofFinite _ _ hg.toFinset fun i hi ↦ ?_]
  rw [show g i = w i by simpa using hi, hf]

variable (w) in
/-- The identity maps of the factors induce the identity. -/
@[simp]
theorem map_id :
    map (w := w) (fun i ↦ (LinearMap.id : W i →ₗ[R] W i)) (fun _ ↦ rfl) = LinearMap.id := by
  simp only [map, PiTensorProduct.map_id]
  exact Module.DirectLimit.map_id

/-- The map induced by composites of factorwise maps is the composite of the induced maps. -/
theorem map_comp {W'' : ι → Type*} [∀ i, AddCommMonoid (W'' i)] [∀ i, Module R (W'' i)]
    {w'' : ∀ i, W'' i} (g : ∀ i, W' i →ₗ[R] W'' i) (hg : ∀ i, g i (w' i) = w'' i)
    (f : ∀ i, W i →ₗ[R] W' i) (hf : ∀ i, f i (w i) = w' i) :
    map (fun i ↦ g i ∘ₗ f i) (fun i ↦ by rw [LinearMap.comp_apply, hf, hg]) =
      map g hg ∘ₗ map f hf := by
  simp only [map, PiTensorProduct.map_comp]
  exact (Module.DirectLimit.map_comp _ _ _ _).symm

/-- Applying two induced maps in turn is applying the map induced by the composites. -/
@[simp]
theorem map_map {W'' : ι → Type*} [∀ i, AddCommMonoid (W'' i)] [∀ i, Module R (W'' i)]
    {w'' : ∀ i, W'' i} (g : ∀ i, W' i →ₗ[R] W'' i) (hg : ∀ i, g i (w' i) = w'' i)
    (f : ∀ i, W i →ₗ[R] W' i) (hf : ∀ i, f i (w i) = w' i) (x : RestrictedTensor R W w) :
    map g hg (map f hf x) =
      map (fun i ↦ g i ∘ₗ f i) (fun i ↦ by rw [LinearMap.comp_apply, hf, hg]) x := by
  rw [map_comp, LinearMap.comp_apply]

/-- Linear equivalences `e i : W i ≃ W' i` sending the references to the references induce a
linear equivalence of restricted tensor products, `⨂ₜ g ↦ ⨂ₜ (e i (g i))`. -/
def congr (e : ∀ i, W i ≃ₗ[R] W' i) (he : ∀ i, e i (w i) = w' i) :
    RestrictedTensor R W w ≃ₗ[R] RestrictedTensor R W' w' :=
  LinearEquiv.ofLinearMap (map (fun i ↦ (e i : W i →ₗ[R] W' i)) he)
    (map (fun i ↦ ((e i).symm : W' i →ₗ[R] W i)) fun i ↦ by
      rw [LinearEquiv.coe_coe, ← he, LinearEquiv.symm_apply_apply])
    (by rw [← map_comp, ← map_id w']; congr 1; ext i x; simp)
    (by rw [← map_comp, ← map_id w]; congr 1; ext i x; simp)

/-- The underlying linear map of `congr e he` is the map induced by the `e i`. -/
theorem toLinearMap_congr (e : ∀ i, W i ≃ₗ[R] W' i) (he : ∀ i, e i (w i) = w' i) :
    (congr e he : RestrictedTensor R W w →ₗ[R] RestrictedTensor R W' w') =
      map (fun i ↦ (e i : W i →ₗ[R] W' i)) he := by
  rw [RestrictedTensor.congr, LinearEquiv.toLinearMap_ofLinearMap]

/-- The induced equivalence on a finite stage is the tensor map of the factors. -/
@[simp]
theorem congr_ofFinite (e : ∀ i, W i ≃ₗ[R] W' i) (he : ∀ i, e i (w i) = w' i) (S : Finset ι)
    (x : ⨂[R] i : S, W i) :
    congr e he (ofFinite R W w S x) =
      ofFinite R W' w' S (PiTensorProduct.map (fun i : S ↦ (e i : W i →ₗ[R] W' i)) x) := by
  rw [← LinearEquiv.coe_coe, toLinearMap_congr, map_ofFinite]

/-- The induced equivalence on pure tensors. -/
@[simp]
theorem congr_tprod (e : ∀ i, W i ≃ₗ[R] W' i) (he : ∀ i, e i (w i) = w' i) (g : ∀ i, W i)
    (hg : {i | g i ≠ w i}.Finite) :
    congr e he (tprod R w g hg) = tprod R w' (fun i ↦ e i (g i))
      (hg.subset fun i hi h ↦ hi (by rw [h, he])) := by
  rw [← LinearEquiv.coe_coe, toLinearMap_congr, map_tprod]
  simp only [LinearEquiv.coe_coe]

/-- The inverse of the equivalence induced by the `e i` is induced by their inverses. -/
@[simp]
theorem congr_symm (e : ∀ i, W i ≃ₗ[R] W' i) (he : ∀ i, e i (w i) = w' i) :
    (congr e he).symm =
      congr (fun i ↦ (e i).symm) fun i ↦ by rw [← he, LinearEquiv.symm_apply_apply] := by
  refine LinearEquiv.toLinearMap_injective ?_
  rw [toLinearMap_congr, RestrictedTensor.congr, LinearEquiv.symm_ofLinearMap,
    LinearEquiv.toLinearMap_ofLinearMap]

variable (w) in
/-- The identity equivalences of the factors induce the identity. -/
@[simp]
theorem congr_refl :
    congr (w := w) (fun i ↦ LinearEquiv.refl R (W i)) (fun _ ↦ rfl) = LinearEquiv.refl R _ :=
  LinearEquiv.toLinearMap_injective <| by
    simp only [toLinearMap_congr, LinearEquiv.refl_toLinearMap]
    exact map_id w

/-- The equivalence induced by composites of factorwise equivalences is the composite of the
induced equivalences. -/
@[simp]
theorem congr_trans {W'' : ι → Type*} [∀ i, AddCommMonoid (W'' i)] [∀ i, Module R (W'' i)]
    {w'' : ∀ i, W'' i} (e : ∀ i, W i ≃ₗ[R] W' i) (he : ∀ i, e i (w i) = w' i)
    (e' : ∀ i, W' i ≃ₗ[R] W'' i) (he' : ∀ i, e' i (w' i) = w'' i) :
    (congr e he).trans (congr e' he') =
      congr (fun i ↦ (e i).trans (e' i)) fun i ↦ by rw [LinearEquiv.trans_apply, he, he'] :=
  LinearEquiv.toLinearMap_injective <| by
    simp only [LinearEquiv.coe_trans, toLinearMap_congr]
    exact (map_comp _ he' _ he).symm

end map

section finite

variable [Fintype ι]

variable (R W w) in
/-- For a finite index type, the restricted tensor product is the tensor product over the full
stage `Finset.univ`: every finite stage maps to it by adjoining reference vectors. -/
def univStageEquiv : RestrictedTensor R W w ≃ₗ[R] ⨂[R] i : (Finset.univ : Finset ι), W i :=
  { lift (fun S ↦ stageMap R w (Finset.subset_univ S))
      (fun S T h x ↦ stageMap_stageMap w h (Finset.subset_univ T) x) with
    invFun := ofFinite R W w Finset.univ
    left_inv z := by
      obtain ⟨S, x, rfl⟩ := exists_ofFinite z
      simp
    right_inv x := by simp }

/-- For a finite index type, an element of a stage `S` is sent to the full stage by adjoining
references. -/
@[simp]
theorem univStageEquiv_ofFinite (S : Finset ι) (x : ⨂[R] i : S, W i) :
    univStageEquiv R W w (ofFinite R W w S x) = stageMap R w (Finset.subset_univ S) x :=
  lift_ofFinite (fun S ↦ stageMap R w (Finset.subset_univ S))
    (fun _ T h x ↦ stageMap_stageMap w h (Finset.subset_univ T) x) S x

/-- For a finite index type, the inverse of `univStageEquiv` includes the full stage. -/
@[simp]
theorem univStageEquiv_symm_apply (x : ⨂[R] i : (Finset.univ : Finset ι), W i) :
    (univStageEquiv R W w).symm x = ofFinite R W w Finset.univ x :=
  (rfl)

variable (R W w) in
/-- For a finite index type, the restricted tensor product is the tensor product of all the
factors: the full stage `Finset.univ`, reindexed by `Finset.univ ≃ ι`. -/
def finiteEquiv : RestrictedTensor R W w ≃ₗ[R] ⨂[R] i, W i :=
  (univStageEquiv R W w).trans
    (PiTensorProduct.reindex R (fun i : (Finset.univ : Finset ι) ↦ W i)
      (Equiv.subtypeUnivEquiv Finset.mem_univ))

/-- For a finite index type, an element of a stage `S` is sent to the full stage by adjoining
references, then reindexed by `Finset.univ ≃ ι`. -/
theorem finiteEquiv_apply_ofFinite (S : Finset ι) (x : ⨂[R] i : S, W i) :
    finiteEquiv R W w (ofFinite R W w S x) =
      PiTensorProduct.reindex R (fun i : (Finset.univ : Finset ι) ↦ W i)
        (Equiv.subtypeUnivEquiv Finset.mem_univ) (stageMap R w (Finset.subset_univ S) x) :=
  (LinearEquiv.trans_apply _).trans (congrArg _ (univStageEquiv_ofFinite S x))

/-- For a finite index type, the inverse of `finiteEquiv` reindexes by `ι ≃ Finset.univ` and
includes the full stage. -/
theorem finiteEquiv_symm_apply (x : ⨂[R] i, W i) :
    (finiteEquiv R W w).symm x = ofFinite R W w Finset.univ
      ((PiTensorProduct.reindex R (fun i : (Finset.univ : Finset ι) ↦ W i)
        (Equiv.subtypeUnivEquiv Finset.mem_univ)).symm x) :=
  (LinearEquiv.symm_trans_apply x).trans (univStageEquiv_symm_apply _)

/-- For a finite index type, a pure tensor at a stage `S` corresponds to the pure tensor of the
family extended by references. -/
@[simp]
theorem finiteEquiv_ofFinite_tprod (S : Finset ι) (f : ∀ i : S, W i) :
    finiteEquiv R W w (ofFinite R W w S (PiTensorProduct.tprod R f)) =
      PiTensorProduct.tprod R (Function.updateFinset w S f) := by
  rw [finiteEquiv_apply_ofFinite, stageMap_tprod, PiTensorProduct.reindex_tprod]
  -- `(Equiv.subtypeUnivEquiv _).symm i` is `⟨i, _⟩` by definition, and `Finset.restrict` is
  -- evaluation at the underlying index; the dependent type of the entry blocks rewriting with
  -- `Equiv.subtypeUnivEquiv_symm_apply` under the binder.
  rfl

/-- For a finite index type, a pure tensor of the restricted tensor product is the pure tensor
of the same family. -/
@[simp]
theorem finiteEquiv_tprod (f : ∀ i, W i) (hf : {i | f i ≠ w i}.Finite) :
    finiteEquiv R W w (tprod R w f hf) = PiTensorProduct.tprod R f := by
  rw [tprod_eq_ofFinite f hf Finset.univ fun i hi ↦ absurd (Finset.mem_univ i) hi,
    finiteEquiv_ofFinite_tprod, Function.updateFinset_univ]

/-- For a finite index type, the inverse of `finiteEquiv` sends a pure tensor to the pure tensor
of the same family. -/
@[simp]
theorem finiteEquiv_symm_tprod (f : ∀ i, W i) :
    (finiteEquiv R W w).symm (PiTensorProduct.tprod R f) = tprod R w f (Set.toFinite _) := by
  rw [LinearEquiv.symm_apply_eq, finiteEquiv_tprod]

end finite

end RestrictedTensor

end TauCeti
