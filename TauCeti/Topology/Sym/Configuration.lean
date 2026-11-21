/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Covering.Quotient
public import TauCeti.Topology.Sym.Basic
import Mathlib.Topology.LocalAtTarget
import TauCeti.Topology.Constructions.Pi

/-!
# Topological configuration spaces

The ordered configurations of `n` points in `X` are the injective tuples in `Fin n → X`.
Unordered configurations are the elements of `Sym X n` with no repetitions. Forgetting the
order is an open quotient map for every `X`, and for Hausdorff `X` it is a quotient covering
map for the left action by inverse coordinate permutations. Embeddings of ambient spaces
induce embeddings of both spaces, commuting with this projection.

For the configuration cover of the open disc and the plane, see Ellenberg–Venkatesh–Westerland,
*Homological stability for Hurwitz spaces and the Cohen–Lenstra conjecture over function
fields*, §2.1. The quotient here uses `Sym.ofFn` and `Sym.instTopologicalSpace`.
-/

public section

open Function Set Topology

namespace TauCeti

/-- The subspace of injective `n`-tuples in `X`. -/
abbrev OrderedConfiguration (X : Type*) (n : ℕ) := {x : Fin n → X // Injective x}

/-- The subspace of `Sym X n` consisting of tuples without repetitions. -/
abbrev UnorderedConfiguration (X : Type*) (n : ℕ) := {s : Sym X n // (s : Multiset X).Nodup}

namespace OrderedConfiguration

variable {X Y Z : Type*} {n : ℕ}

/-- Two ordered configurations are equal if they agree in every coordinate. -/
@[ext] theorem ext {x y : OrderedConfiguration X n} (h : ∀ i, x.val i = y.val i) : x = y :=
  Subtype.ext (funext h)

/-- Permutations act on tuples by precomposition with the inverse. -/
instance : MulAction (Equiv.Perm (Fin n)) (OrderedConfiguration X n) where
  smul σ x := ⟨x.val ∘ ⇑(σ⁻¹), x.property.comp (σ⁻¹).injective⟩
  one_smul _ := ext fun _ ↦ rfl
  mul_smul _ _ _ := ext fun _ ↦ rfl

/-- The permutation action reindexes each coordinate by the inverse permutation. -/
@[simp] theorem smul_apply (σ : Equiv.Perm (Fin n)) (x : OrderedConfiguration X n) (i : Fin n) :
    (σ • x).val i = x.val (σ⁻¹ i) := (rfl)

/-- No two distinct permutations act in the same way on an ordered configuration. -/
instance : IsCancelSMul (Equiv.Perm (Fin n)) (OrderedConfiguration X n) where
  right_cancel' σ τ x h := inv_injective <| Equiv.ext fun i ↦ by
    apply x.property
    simpa only [smul_apply] using congrArg (fun y : OrderedConfiguration X n ↦ y.val i) h

/-- Postcomposition by an injection takes ordered configurations to ordered configurations. -/
def map (f : X → Y) (hf : Injective f) (x : OrderedConfiguration X n) :
    OrderedConfiguration Y n :=
  ⟨f ∘ x.val, hf.comp x.property⟩

/-- Mapping an ordered configuration applies the injection to each entry. -/
@[simp] theorem map_apply (f : X → Y) (hf : Injective f) (x : OrderedConfiguration X n)
    (i : Fin n) : (map f hf x).val i = f (x.val i) := (rfl)

/-- The identity leaves an ordered configuration unchanged. -/
@[simp] theorem map_id (x : OrderedConfiguration X n) : map id injective_id x = x :=
  ext fun _ ↦ rfl

/-- Mapping an ordered configuration twice is mapping by the composite. -/
@[simp] theorem map_map (f : X → Y) (hf : Injective f) (g : Y → Z) (hg : Injective g)
    (x : OrderedConfiguration X n) : map g hg (map f hf x) = map (g ∘ f) (hg.comp hf) x :=
  ext fun _ ↦ rfl

/-- Mapping an ordered configuration commutes with relabeling. -/
@[simp] theorem map_smul (f : X → Y) (hf : Injective f) (σ : Equiv.Perm (Fin n))
    (x : OrderedConfiguration X n) : map f hf (σ • x) = σ • map f hf x :=
  ext fun _ ↦ rfl

/-- Forgetting labels records an ordered configuration in the symmetric power. -/
def toUnordered (x : OrderedConfiguration X n) : UnorderedConfiguration X n :=
  ⟨Sym.ofFn x.val, by
    simpa only [Sym.coe_ofFn, Multiset.coe_nodup, List.nodup_ofFn] using x.property⟩

/-- The underlying symmetric tuple is obtained by applying `Sym.ofFn`. -/
@[simp] theorem val_toUnordered (x : OrderedConfiguration X n) :
    x.toUnordered.val = Sym.ofFn x.val := (rfl)

/-- Two ordered configurations give the same unordered configuration exactly when they differ
by a permutation of the labels. -/
theorem toUnordered_eq_iff {x y : OrderedConfiguration X n} :
    x.toUnordered = y.toUnordered ↔ ∃ σ : Equiv.Perm (Fin n), σ • y = x := by
  rw [← Subtype.val_inj, val_toUnordered, val_toUnordered, Sym.ofFn_eq_ofFn_iff]
  refine ⟨fun ⟨σ, h⟩ ↦ ⟨σ, ext fun i ↦ ?_⟩, fun ⟨σ, h⟩ ↦ ⟨σ, funext fun i ↦ ?_⟩⟩
  · simpa only [smul_apply, comp_apply, Equiv.Perm.coe_inv, Equiv.apply_symm_apply] using
      (congrFun h (σ⁻¹ i)).symm
  · simpa only [smul_apply, comp_apply, Equiv.Perm.coe_inv, Equiv.symm_apply_apply] using
      (congrArg (fun z : OrderedConfiguration X n ↦ z.val (σ i)) h).symm

/-- Forgetting labels is invariant under the permutation action. -/
@[simp] theorem toUnordered_smul (σ : Equiv.Perm (Fin n)) (x : OrderedConfiguration X n) :
    (σ • x).toUnordered = x.toUnordered :=
  toUnordered_eq_iff.mpr ⟨σ, rfl⟩

variable [TopologicalSpace X] [TopologicalSpace Y]

/-- Each permutation acts continuously for the subspace topology. -/
instance : ContinuousConstSMul (Equiv.Perm (Fin n)) (OrderedConfiguration X n) where
  continuous_const_smul σ := IsEmbedding.subtypeVal.isInducing.continuous_iff.mpr <|
    continuous_pi fun i ↦ by
      simpa only [Function.comp_def, smul_apply] using
        (continuous_apply (σ⁻¹ i)).comp (continuous_subtypeVal (p := Injective))

/-- An ambient embedding induces an embedding of ordered configurations. -/
theorem isEmbedding_map {f : X → Y} (hf : IsEmbedding f) :
    IsEmbedding (map f hf.injective : OrderedConfiguration X n → OrderedConfiguration Y n) :=
  IsEmbedding.subtypeVal.of_comp_iff.mp <| by
    convert (IsEmbedding.piMap fun _ : Fin n ↦ hf).comp
      (IsEmbedding.subtypeVal (p := Injective)) using 1
    exact funext fun x ↦ funext fun i ↦ map_apply f hf.injective x i

/-- Ordered configurations form an open subspace of the product when `X` is Hausdorff. -/
theorem isOpenEmbedding_val [T2Space X] :
    IsOpenEmbedding (Subtype.val : OrderedConfiguration X n → (Fin n → X)) :=
  (TauCeti.isOpen_setOf_injective (X := X) (κ := Fin n)).isOpenEmbedding_subtypeVal

/-- Forgetting labels presents unordered configurations as the topological quotient of ordered
configurations. The projection is open even when the ambient space is not Hausdorff. -/
theorem isOpenQuotientMap_toUnordered :
    IsOpenQuotientMap (toUnordered : OrderedConfiguration X n → UnorderedConfiguration X n) := by
  let s : Set (Sym X n) := {w | (w : Multiset X).Nodup}
  have h : Sym.ofFn ⁻¹' s = {x : Fin n → X | Injective x} := by
    ext x
    simp [s, List.nodup_ofFn]
  -- The preimage of the repetition-free locus is precisely the injective-tuples subspace.
  let e := Homeomorph.setCongr h.symm
  convert (Sym.isOpenQuotientMap_ofFn.restrictPreimage s).comp e.isOpenQuotientMap using 1
  exact funext fun x ↦ Subtype.ext <| by rw [val_toUnordered]; rfl

/-- Over a Hausdorff space the order-forgetting projection is a quotient covering map, with
a free and transitive permutation action on each fibre. -/
theorem isQuotientCoveringMap_toUnordered [T2Space X] :
    IsQuotientCoveringMap (toUnordered : OrderedConfiguration X n → UnorderedConfiguration X n)
      (Equiv.Perm (Fin n)) where
  toIsQuotientMap := isOpenQuotientMap_toUnordered.isQuotientMap
  toContinuousConstSMul := inferInstance
  apply_eq_iff_mem_orbit := toUnordered_eq_iff
  disjoint x := by
    obtain ⟨U, hU, hdisj⟩ := (finite_range x.val).t2_separation
    let W := (Subtype.val : OrderedConfiguration X n → (Fin n → X)) ⁻¹'
      (univ.pi fun i ↦ U (x.val i))
    have ho : IsOpen W :=
      (isOpen_set_pi finite_univ fun i _ ↦ (hU (x.val i)).2).preimage continuous_subtypeVal
    refine ⟨W, ho.mem_nhds (fun i _ ↦ (hU (x.val i)).1), fun σ hσ ↦ ?_⟩
    obtain ⟨_, ⟨y, hy, rfl⟩, hsy⟩ := hσ
    -- A point of a translated box would lie in both neighbourhoods at each permuted index.
    apply inv_injective
    refine Equiv.ext fun i ↦ ?_
    by_contra hi
    have hd := hdisj (mem_range_self (σ⁻¹ i)) (mem_range_self i) (fun h ↦ hi (x.property h))
    exact Set.disjoint_left.1 hd (hy (σ⁻¹ i) (mem_univ _))
      (by simpa only [smul_apply] using hsy i (mem_univ i))

end OrderedConfiguration

namespace UnorderedConfiguration

variable {X Y Z : Type*} {n : ℕ}

/-- Applying an injection to the points of an unordered configuration preserves distinctness. -/
def map (f : X → Y) (hf : Injective f) (x : UnorderedConfiguration X n) :
    UnorderedConfiguration Y n :=
  ⟨Sym.map f x.val, by
    rw [Sym.coe_map, Multiset.nodup_map_iff_of_injective hf]
    exact x.property⟩

/-- Mapping an unordered configuration applies the injection to its underlying symmetric tuple. -/
@[simp] theorem val_map (f : X → Y) (hf : Injective f) (x : UnorderedConfiguration X n) :
    (map f hf x).val = Sym.map f x.val := (rfl)

/-- The identity leaves an unordered configuration unchanged. -/
@[simp] theorem map_id (x : UnorderedConfiguration X n) : map id injective_id x = x :=
  Subtype.ext (Sym.map_id _)

/-- Mapping an unordered configuration twice is mapping by the composite. -/
@[simp] theorem map_map (f : X → Y) (hf : Injective f) (g : Y → Z) (hg : Injective g)
    (x : UnorderedConfiguration X n) : map g hg (map f hf x) = map (g ∘ f) (hg.comp hf) x :=
  Subtype.ext (Sym.map_map _ _ _)

/-- Mapping the points commutes with forgetting their labels. -/
@[simp] theorem _root_.TauCeti.OrderedConfiguration.toUnordered_map (f : X → Y) (hf : Injective f)
    (x : OrderedConfiguration X n) :
    (OrderedConfiguration.map f hf x).toUnordered = map f hf x.toUnordered :=
  Subtype.ext (Sym.map_ofFn f x.val).symm

variable [TopologicalSpace X] [TopologicalSpace Y]

/-- An ambient embedding induces an embedding of unordered configurations. -/
theorem isEmbedding_map {f : X → Y} (hf : IsEmbedding f) :
    IsEmbedding (map f hf.injective : UnorderedConfiguration X n → UnorderedConfiguration Y n) :=
  IsEmbedding.subtypeVal.of_comp_iff.mp <| by
    simpa only [Function.comp_def, val_map] using
      (Sym.isEmbedding_map hf).comp (IsEmbedding.subtypeVal (p := fun s : Sym X n ↦
        (s : Multiset X).Nodup))

/-- Unordered configurations form an open subspace of the symmetric power when `X` is Hausdorff. -/
theorem isOpenEmbedding_val [T2Space X] :
    IsOpenEmbedding (Subtype.val : UnorderedConfiguration X n → Sym X n) := by
  refine IsOpen.isOpenEmbedding_subtypeVal (s := {s : Sym X n | (s : Multiset X).Nodup}) ?_
  rw [← Sym.isQuotientMap_ofFn.isOpen_preimage]
  simpa [Set.preimage, List.nodup_ofFn] using TauCeti.isOpen_setOf_injective (X := X) (κ := Fin n)

end UnorderedConfiguration

end TauCeti
