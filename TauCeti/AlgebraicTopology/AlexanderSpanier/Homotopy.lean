/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicTopology.SimplicialObject.ChainHomotopy
public import Mathlib.Topology.Homotopy.Equiv
public import TauCeti.AlgebraicTopology.AlexanderSpanier.Relative
import TauCeti.Data.Fin.Basic

/-!
# Homotopy invariance of Alexander–Spanier cohomology

Homotopic maps `f₀ ≃ f₁ : X → Y` out of a compact space `X` induce the same map
`H^n(Y; M) ⟶ H^n(X; M)` in Alexander–Spanier cohomology
(`TauCeti.AlexanderSpanier.cohomologyMap_eq_of_homotopic`). Consequently a homotopy equivalence
between compact spaces induces isomorphisms in Alexander–Spanier cohomology
(`TauCeti.AlexanderSpanier.cohomologyIsoOfHomotopyEquiv`).

The same holds for relative cohomology and maps of pairs. Let `X` be compact and `A` closed in `Y`.
Maps of pairs `f₀ f₁ : (X, B) → (Y, A)` that are homotopic through maps of pairs, that is, by a
homotopy `F` with `F_t(B) ⊆ A` for every `t` (Mathlib's `ContinuousMap.HomotopicWith`), induce the
same map `H^n(Y, A; M) ⟶ H^n(X, B; M)`
(`TauCeti.AlexanderSpanier.homologyMap_relativeCochainComplexMap_eq_of_homotopicWith`). So a
homotopy equivalence of pairs between compact spaces with closed subspaces induces isomorphisms in
relative cohomology (`TauCeti.AlexanderSpanier.relativeCohomologyIsoOfHomotopicWith`).

## The prism operator

For arbitrary functions `f g : X → Y`, the **prism operator**
(`TauCeti.AlexanderSpanier.prism`) sends a function `ψ` on `(n + 2)`-tuples of `Y` to the function
on `(n + 1)`-tuples of `X`

`(P ψ)(x₀, …, xₙ) = ∑ₖ (-1)ᵏ ψ(f x₀, …, f xₖ, g xₖ, …, g xₙ)`.

It is a chain homotopy between the pullbacks of all functions along `f` and `g`: writing `δ` for
the Alexander–Spanier coboundary, `ψ ∘ g - ψ ∘ f` is `P (δ ψ)` in degree `0`
(`TauCeti.AlexanderSpanier.prism_zero_apply_coboundary`) and `δ (P ψ) + P (δ ψ)` in higher degrees
(`TauCeti.AlexanderSpanier.coboundary_prism_add_prism_coboundary_apply`). These identities come from
Mathlib's simplicial homotopy `CategoryTheory.SimplicialObject.Homotopy.toChainHomotopy`, applied to
the maps of tuples `(x₀, …, xₙ) ↦ (f x₀, …, f xₙ)` and `(g x₀, …, g xₙ)`, which are simplicially
homotopic for every pair of functions `f`, `g`.

The prism operator does not preserve locally zero functions in general. It does on the functions
`ψ` that vanish on all tuples of points of `f(V) ∪ g(V)`, for some neighbourhood `V` of each point
of `X` (`TauCeti.AlexanderSpanier.isLocallyZero_prism`). So two maps `f`, `g` induce the same map on
the class of a cocycle `φ` as soon as they are close relative to the coboundary of `φ`: every point
of `X` has a neighbourhood `V` such that `δ φ` vanishes on all tuples of points of `f(V) ∪ g(V)`
(`TauCeti.AlexanderSpanier.cohomologyMap_homologyπ_eq_of_forall_nhds`). On cochains, the pullbacks
of the class of `φ` along `f` and `g` then differ by the coboundary of the class of `P φ`
(`TauCeti.AlexanderSpanier.cochainComplexMap_f_succ_cochainClass_eq_add_of_forall_nhds`), and agree
in degree `0` (`TauCeti.AlexanderSpanier.cochainComplexMap_f_zero_cochainClass_eq_of_forall_nhds`).

For maps of pairs `f g : (X, B) → (Y, A)` and a relative cocycle represented by a function `φ`
that vanishes on all tuples of points of `A`, the prism `P φ` vanishes on all tuples of points of
`B`, since the entries of its prism tuples lie in `f(B) ∪ g(B) ⊆ A`
(`TauCeti.AlexanderSpanier.prism_apply_eq_zero_of_mapsTo`). So `P φ` is a relative cochain
of `(X, B)`, and the same closeness condition makes `f` and `g` induce the same map on the relative
class
(`TauCeti.AlexanderSpanier.homologyMap_relativeCochainComplexMap_homologyπ_eq_of_forall_nhds`).
When `A` is closed every relative cochain of `(Y, A)` has such a representative
(`TauCeti.AlexanderSpanier.exists_relativeCochainComplexι_f_eq_cochainClass_of_isClosed`), which is
where closedness of `A` enters.

## Implementation notes

The simplicial homotopy between the pullbacks along `f` and `g`, and the local tactic
`prism_tuple_ext` that checks its simplicial identities case by case, are adapted from
`CategoryTheory.Arrow.mapCechNerveHomotopy` and its local tactic `cech_nerve_homotopy_ext` in
`TauCeti.AlgebraicTopology.CechNerve`.

Let `F` be a homotopy from `f₀` to `f₁` and fix a cocycle `φ` on `Y`. Its coboundary is locally
zero, so each point of `Y` has a neighbourhood on whose tuples `δ φ` vanishes. By continuity of
`F` and compactness of `X` (the tube lemma `IsCompact.eventually_forall_of_forall_eventually`), the
maps `F_s` and `F_t` are close relative to `δ φ` for all `s` near `t`. So `t ↦ F_t^* [φ]` is locally
constant on the unit interval, hence constant since the interval is connected. The same argument
applies to a homotopy through maps of pairs and a relative cocycle.

The compactness of `X` is what makes the subdivision of the homotopy uniform. Spanier proves the
homotopy axiom for Alexander–Spanier cohomology on arbitrary spaces by a different argument; the
compact case is the one used for the cohomology of compact pairs.

## References

* E. H. Spanier, *Algebraic Topology*, McGraw–Hill, 1966, Chapter 6, Sections 6.4 and 6.5.
-/

public section

noncomputable section

open CategoryTheory Opposite AlgebraicTopology Topology
open scoped Simplicial

universe w u v

namespace TauCeti.AlexanderSpanier

section Prism

variable {R : Type w} [Ring R] {M : Type v} [AddCommGroup M] [Module R M] {X Y : Type u}

/-- The `k`-th prism tuple of an `(n + 1)`-tuple `x` of points of `X` for functions `f g : X → Y`:
the `(n + 2)`-tuple `(f x₀, …, f xₖ, g xₖ, …, g xₙ)` of points of `Y`. -/
def prismTuple (f g : X → Y) {n : ℕ} (k : Fin (n + 1)) (x : Fin (n + 1) → X) : Fin (n + 2) → Y :=
  fun j ↦ (if j ≤ k.castSucc then f else g) (x (k.predAbove j))

lemma prismTuple_apply (f g : X → Y) {n : ℕ} (k : Fin (n + 1)) (x : Fin (n + 1) → X)
    (j : Fin (n + 2)) :
    prismTuple f g k x j = (if j ≤ k.castSucc then f else g) (x (k.predAbove j)) :=
  (rfl)

/-- Every entry of a prism tuple of `x` is the image under `f` or under `g` of an entry of `x`. -/
lemma prismTuple_mem (f g : X → Y) {n : ℕ} (k : Fin (n + 1)) (x : Fin (n + 1) → X)
    (j : Fin (n + 2)) :
    prismTuple f g k x j ∈ f '' Set.range x ∪ g '' Set.range x := by
  rw [prismTuple_apply]
  split_ifs
  · exact Or.inl ⟨_, Set.mem_range_self _, rfl⟩
  · exact Or.inr ⟨_, Set.mem_range_self _, rfl⟩

variable (R M) in
/-- The **prism operator** of functions `f g : X → Y`, from functions on `(n + 2)`-tuples of `Y` to
functions on `(n + 1)`-tuples of `X`: `(P ψ)(x) = ∑ₖ (-1)ᵏ ψ(f x₀, …, f xₖ, g xₖ, …, g xₙ)`. -/
def prism (f g : X → Y) (n : ℕ) : ((Fin (n + 2) → Y) → M) →ₗ[R] ((Fin (n + 1) → X) → M) :=
  ∑ k : Fin (n + 1), ((-1 : ℤ) ^ (k : ℕ)) • LinearMap.funLeft R M (prismTuple f g k)

@[simp]
lemma prism_apply (f g : X → Y) {n : ℕ} (ψ : (Fin (n + 2) → Y) → M) (x : Fin (n + 1) → X) :
    prism R M f g n ψ x = ∑ k : Fin (n + 1), (-1 : ℤ) ^ (k : ℕ) • ψ (prismTuple f g k x) := by
  simp [prism, Finset.sum_apply]

/-! ### The prism identities

The cochains of all functions on tuples form a cosimplicial module. We read it as a simplicial
object in the opposite category of modules, in which pulling back along `f` and along `g` are
simplicially homotopic, with the prism tuples as the components of the homotopy. Mathlib turns the
simplicial homotopy into a chain homotopy, whose components are the negated prism operators. -/

variable (R M) in
/-- Precomposition with a function `g : α → β`, as a morphism `(α → M) ⟶ (β → M)` of the opposite
category of modules. -/
private abbrev opFunLeft {α β : Type u} (g : α → β) :
    op (ModuleCat.of.{max u v} R (α → M)) ⟶ op (ModuleCat.of.{max u v} R (β → M)) :=
  (ModuleCat.ofHom (LinearMap.funLeft R M g)).op

private lemma opFunLeft_comp_eq {α β γ : Type u} {g₁ : α → β} {g₂ : β → γ} {g : α → γ}
    (h : ∀ a, g₂ (g₁ a) = g a) :
    opFunLeft R M g₁ ≫ opFunLeft R M g₂ = opFunLeft R M g := by
  rw [show g = g₂ ∘ g₁ from (funext h).symm]
  -- Composition in the opposite category is composition of the `LinearMap.funLeft` maps in the
  -- reverse order, and `LinearMap.funLeft` of `g₂ ∘ g₁` is that composite by definition.
  rfl

variable (R M) in
/-- The functions on tuples of points of `X`, as a simplicial object in the opposite category of
modules: a map `θ` of the simplex category acts by precomposing tuples with `θ`. -/
private def tupleFunctions (X : Type u) : SimplicialObject (ModuleCat.{max u v} R)ᵒᵖ where
  obj n := op (ModuleCat.of R ((Fin (n.unop.len + 1) → X) → M))
  map θ := opFunLeft R M fun x : Fin _ → X ↦ x ∘ ⇑θ.unop.toOrderHom
  map_id _ := rfl
  map_comp _ _ := rfl

variable (R M) in
/-- Pulling back functions on tuples along `f : X → Y`, as a map of simplicial objects. -/
private def tupleFunctionsMap (f : X → Y) : tupleFunctions R M X ⟶ tupleFunctions R M Y where
  app _ := opFunLeft R M fun x ↦ f ∘ x
  naturality _ _ _ := rfl

/-- Proves an identity between precomposition with prism tuples and with faces or degeneracies,
in the shape `prismTuple f g k (x ∘ θ) j = prismTuple f g k' x j'`: both sides apply the same
function to the same entry, which reduces the identity to arithmetic of the indices. -/
local macro "prism_tuple_ext" : tactic => `(tactic| (
  simp only [SimplexCategory.δ, SimplexCategory.σ, SimplexCategory.mkHom, Quiver.Hom.unop_op,
    SimplexCategory.Hom.toOrderHom_mk, OrderEmbedding.toOrderHom_coe, Fin.succAboveOrderEmb_apply,
    Fin.predAboveOrderHom_coe, prismTuple, Function.comp_apply]
  refine congr (if_congr ?_ rfl rfl) (congrArg _ ?_) <;>
    simp only [Fin.ext_iff, Fin.le_def, Fin.lt_def, Fin.val_succAbove, Fin.val_predAbove,
      Fin.val_castSucc, Fin.val_succ] at * <;>
    split_ifs at * <;> omega))

variable (R M) in
/-- Pulling back along any two functions `f g : X → Y` gives simplicially homotopic maps of
functions on tuples, with the prism tuples as the components of the homotopy. -/
private def tupleFunctionsHomotopy (f g : X → Y) :
    SimplicialObject.Homotopy (tupleFunctionsMap R M f) (tupleFunctionsMap R M g) where
  h k := opFunLeft R M (prismTuple f g k)
  h_zero_comp_δ_zero n := opFunLeft_comp_eq fun x ↦ funext fun j ↦ by
    simp [SimplexCategory.δ, prismTuple, Fin.succAbove_zero]
  h_last_comp_δ_last n := opFunLeft_comp_eq fun x ↦ funext fun j ↦ by
    simp [SimplexCategory.δ, prismTuple, Fin.le_castSucc_iff]
  h_succ_comp_δ_castSucc_of_lt i j hij := opFunLeft_comp_eq fun x ↦ funext fun k ↦ by
    prism_tuple_ext
  h_succ_comp_δ_castSucc_succ j := opFunLeft_comp_eq fun x ↦ funext fun k ↦ by
    prism_tuple_ext
  h_castSucc_comp_δ_succ_of_lt i j hji := opFunLeft_comp_eq fun x ↦ funext fun k ↦ by
    prism_tuple_ext
  h_comp_σ_castSucc_of_le i j hij := opFunLeft_comp_eq fun x ↦ funext fun k ↦ by
    prism_tuple_ext
  h_comp_σ_succ_of_lt i j hji := opFunLeft_comp_eq fun x ↦ funext fun k ↦ by
    prism_tuple_ext

/-- The components of the chain homotopy induced by `tupleFunctionsHomotopy` are the negated prism
operators. -/
private lemma unop_hom_toChainHomotopy_hom (f g : X → Y) (n : ℕ) :
    ((tupleFunctionsHomotopy R M f g).toChainHomotopy.hom n (n + 1)).unop.hom =
      -prism R M f g n := by
  simp [SimplicialObject.Homotopy.toChainHomotopy, prism]
  -- The `k`-th component of `tupleFunctionsHomotopy` is by definition `opFunLeft` of the `k`-th
  -- prism tuple, whose underlying linear map is `LinearMap.funLeft` of that tuple.
  rfl

/-- The differential of the alternating face map complex of `tupleFunctions` is the
Alexander–Spanier coboundary of functions. -/
private lemma unop_hom_d (n : ℕ) :
    (((alternatingFaceMapComplex _).obj (tupleFunctions R M X)).d (n + 1) n).unop.hom =
      ∑ i : Fin (n + 2), ((-1 : ℤ) ^ (i : ℕ)) •
        LinearMap.funLeft R M fun y : Fin (n + 2) → X ↦ y ∘ Fin.succAbove i := by
  rw [alternatingFaceMapComplex_obj_d, AlternatingFaceMapComplex.objD, unop_sum,
    ModuleCat.hom_sum]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [unop_zsmul, ModuleCat.hom_zsmul]
  -- The `i`-th face map of `tupleFunctions` is by definition `opFunLeft` of precomposition with
  -- `SimplexCategory.δ i`, whose underlying order map is `Fin.succAbove i`.
  rfl

private lemma unop_hom_map_f (f : X → Y) (n : ℕ) :
    (((alternatingFaceMapComplex _).map (tupleFunctionsMap R M f)).f n).unop.hom =
      LinearMap.funLeft R M fun x : Fin (n + 1) → X ↦ f ∘ x :=
  rfl

/-- The Alexander–Spanier coboundary, as the alternating sum of the precompositions with the faces,
evaluated at a function `ψ` on `(n + 1)`-tuples. -/
private lemma coboundary_apply {Z : Type u} (n : ℕ) (ψ : (Fin (n + 1) → Z) → M) :
    (∑ i : Fin (n + 2), ((-1 : ℤ) ^ (i : ℕ)) •
        LinearMap.funLeft R M fun y : Fin (n + 2) → Z ↦ y ∘ i.succAbove) ψ =
      fun y ↦ ∑ i : Fin (n + 2), (-1 : ℤ) ^ (i : ℕ) • ψ (y ∘ Fin.succAbove i) := by
  funext y
  simp [Finset.sum_apply]

variable (R M) in
/-- The chain-homotopy identity of `tupleFunctionsHomotopy` in degree `n`, read as an equation of
linear maps on functions: pulling back along `f` is `D`, plus minus the prism of the coboundary,
plus pulling back along `g`, where `D` is the `dNext` term of the chain homotopy. -/
private lemma funLeft_comp_eq_add (f g : X → Y) (n : ℕ)
    (D : ((Fin (n + 1) → Y) → M) →ₗ[R] ((Fin (n + 1) → X) → M))
    (hD : (dNext n (tupleFunctionsHomotopy R M f g).toChainHomotopy.hom).unop.hom = D) :
    LinearMap.funLeft R M (fun x : Fin (n + 1) → X ↦ f ∘ x) =
      D + (-prism R M f g n) ∘ₗ (∑ i : Fin (n + 2), ((-1 : ℤ) ^ (i : ℕ)) •
          LinearMap.funLeft R M fun y : Fin (n + 2) → Y ↦ y ∘ i.succAbove) +
        LinearMap.funLeft R M (fun x : Fin (n + 1) → X ↦ g ∘ x) := by
  have h := congrArg (fun φ ↦ φ.unop.hom) ((tupleFunctionsHomotopy R M f g).toChainHomotopy.comm n)
  rw [prevD_eq _ (j' := n + 1) (by simp)] at h
  simp only [unop_add, unop_comp, ModuleCat.hom_add, ModuleCat.hom_comp] at h
  rw [unop_hom_map_f, unop_hom_map_f, unop_hom_d, unop_hom_toChainHomotopy_hom, hD] at h
  exact h

/-- **The prism identity in degree zero.** For functions `f g : X → Y` and `ψ : Y → M`, read as a
function on one-element tuples, the prism operator applied to the coboundary
`(y₀, y₁) ↦ ψ(y₁) - ψ(y₀)` of `ψ` is `ψ ∘ g - ψ ∘ f`. -/
theorem prism_zero_apply_coboundary (f g : X → Y) (ψ : (Fin 1 → Y) → M) (x : Fin 1 → X) :
    prism R M f g 0 (fun y ↦ ∑ i : Fin 2, (-1 : ℤ) ^ (i : ℕ) • ψ (y ∘ Fin.succAbove i)) x =
      ψ (g ∘ x) - ψ (f ∘ x) := by
  have h := funLeft_comp_eq_add R M f g 0 0 <| by
    rw [dNext_eq_zero _ _ (by simp), Limits.unop_zero, ModuleCat.hom_zero]
    -- The two zero maps differ only in writing the cochain module of the complex in degree `0`
    -- as its definition, the module of functions on one-element tuples.
    rfl
  have := congrFun (LinearMap.congr_fun h ψ) x
  simp only [LinearMap.add_apply, zero_add, LinearMap.comp_apply,
    LinearMap.neg_apply, LinearMap.funLeft_apply, Pi.add_apply, Pi.neg_apply,
    coboundary_apply] at this
  rw [this]
  abel

/-- **The prism identity.** For functions `f g : X → Y` and `ψ` on `(n + 2)`-tuples of `Y`, the
coboundary of the prism `P ψ` plus the prism of the coboundary `δ ψ` is `ψ ∘ g - ψ ∘ f`:
`δ (P ψ) + P (δ ψ) = g^* ψ - f^* ψ`. -/
theorem coboundary_prism_add_prism_coboundary_apply (f g : X → Y) {n : ℕ}
    (ψ : (Fin (n + 2) → Y) → M) (x : Fin (n + 2) → X) :
    (∑ i : Fin (n + 2), (-1 : ℤ) ^ (i : ℕ) • prism R M f g n ψ (x ∘ Fin.succAbove i)) +
        prism R M f g (n + 1)
          (fun y ↦ ∑ i : Fin (n + 3), (-1 : ℤ) ^ (i : ℕ) • ψ (y ∘ Fin.succAbove i)) x =
      ψ (g ∘ x) - ψ (f ∘ x) := by
  have h := funLeft_comp_eq_add R M f g (n + 1)
    ((∑ i : Fin (n + 2), ((-1 : ℤ) ^ (i : ℕ)) •
      LinearMap.funLeft R M fun y : Fin (n + 2) → X ↦ y ∘ i.succAbove) ∘ₗ (-prism R M f g n)) <| by
    rw [dNext_eq _ (i' := n) (by simp), unop_comp, ModuleCat.hom_comp, unop_hom_d,
      unop_hom_toChainHomotopy_hom]
    -- The two sides differ only in writing the cochain modules of the complexes as their
    -- definitions, the modules of functions on tuples.
    rfl
  have := congrFun (LinearMap.congr_fun h ψ) x
  simp only [LinearMap.add_apply, LinearMap.comp_apply, LinearMap.neg_apply, map_neg,
    LinearMap.funLeft_apply, Pi.add_apply, Pi.neg_apply, coboundary_apply] at this
  rw [this]
  abel

/-- If `f` and `g` map `B` into `A` and `ψ` vanishes on all tuples of points of `A`, then the prism
`P ψ` vanishes on all tuples of points of `B`. -/
lemma prism_apply_eq_zero_of_mapsTo {f g : X → Y} {B : Set X} {A : Set Y} (hf : Set.MapsTo f B A)
    (hg : Set.MapsTo g B A) {n : ℕ} {ψ : (Fin (n + 2) → Y) → M}
    (hψ : ∀ y : Fin (n + 2) → Y, (∀ i, y i ∈ A) → ψ y = 0) {x : Fin (n + 1) → X}
    (hx : ∀ i, x i ∈ B) : prism R M f g n ψ x = 0 := by
  rw [prism_apply]
  refine Finset.sum_eq_zero fun k _ ↦ ?_
  rw [hψ _ fun j ↦ ?_, smul_zero]
  obtain h | h := prismTuple_mem f g k x j <;> obtain ⟨_, ⟨i, rfl⟩, h⟩ := h
  exacts [h ▸ hf (hx i), h ▸ hg (hx i)]

variable [TopologicalSpace X]

/-- The prism of a function `ψ` is locally zero when every point of `X` has a neighbourhood `V`
such that `ψ` vanishes on all tuples of points of `f(V) ∪ g(V)`. -/
theorem isLocallyZero_prism {f g : X → Y} {n : ℕ} {ψ : (Fin (n + 2) → Y) → M}
    (h : ∀ x, ∃ V ∈ 𝓝 x, ∀ y : Fin (n + 2) → Y, (∀ i, y i ∈ f '' V ∪ g '' V) → ψ y = 0) :
    IsLocallyZero (prism R M f g n ψ) := by
  refine isLocallyZero_iff.2 fun x ↦ ?_
  obtain ⟨V, hV, hψ⟩ := h x
  refine ⟨V, hV, fun z hz ↦ ?_⟩
  rw [prism_apply]
  refine Finset.sum_eq_zero fun k _ ↦ ?_
  rw [hψ _ fun j ↦ ?_, smul_zero]
  obtain h | h := prismTuple_mem f g k z j <;> obtain ⟨_, ⟨i, rfl⟩, h⟩ := h
  exacts [Or.inl ⟨_, hz i, h⟩, Or.inr ⟨_, hz i, h⟩]

end Prism

section Homotopy

variable {R : Type w} [Ring R] {M : Type v} [AddCommGroup M] [Module R M] {X Y : Type u}
  [TopologicalSpace X] [TopologicalSpace Y]

variable (R M) in
/-- **Maps close relative to a function, in degree zero.** Let `φ` be a function on points of `Y`.
If every point of `X` has a neighbourhood `V` such that the coboundary of `φ` vanishes on all pairs
of points of `f(V) ∪ g(V)`, then the continuous maps `f g : X → Y` pull the class of `φ` back to the
same Alexander–Spanier `0`-cochain. -/
theorem cochainComplexMap_f_zero_cochainClass_eq_of_forall_nhds {f g : C(X, Y)}
    {φ : (Fin 1 → Y) → M}
    (h : ∀ x, ∃ V ∈ 𝓝 x, ∀ y : Fin 2 → Y, (∀ i, y i ∈ f '' V ∪ g '' V) →
      ∑ i : Fin 2, (-1 : ℤ) ^ (i : ℕ) • φ (y ∘ Fin.succAbove i) = 0) :
    ((cochainComplexMap R M f).f 0).hom (cochainClass R Y M 0 φ) =
      ((cochainComplexMap R M g).f 0).hom (cochainClass R Y M 0 φ) := by
  rw [cochainComplexMap_f_cochainClass, cochainComplexMap_f_cochainClass,
    cochainClass_eq_cochainClass_iff]
  convert (isLocallyZero_prism (R := R) h).smul (-1 : ℤ) using 1
  funext x
  rw [Pi.sub_apply, Pi.smul_apply, prism_zero_apply_coboundary]
  abel

variable (R M) in
/-- **Maps close relative to a function, in positive degree.** Let `φ` be a function on
`(n + 2)`-tuples of `Y`. If every point of `X` has a neighbourhood `V` such that the coboundary of
`φ` vanishes on all tuples of points of `f(V) ∪ g(V)`, then the pullbacks of the class of `φ` along
the continuous maps `f g : X → Y` differ by the coboundary of the class of the prism `P φ`. -/
theorem cochainComplexMap_f_succ_cochainClass_eq_add_of_forall_nhds {f g : C(X, Y)} {n : ℕ}
    {φ : (Fin (n + 2) → Y) → M}
    (h : ∀ x, ∃ V ∈ 𝓝 x, ∀ y : Fin (n + 3) → Y, (∀ i, y i ∈ f '' V ∪ g '' V) →
      ∑ i : Fin (n + 3), (-1 : ℤ) ^ (i : ℕ) • φ (y ∘ Fin.succAbove i) = 0) :
    ((cochainComplexMap R M g).f (n + 1)).hom (cochainClass R Y M (n + 1) φ) =
      ((cochainComplexMap R M f).f (n + 1)).hom (cochainClass R Y M (n + 1) φ) +
        ((cochainComplex R X M).d n (n + 1)).hom (cochainClass R X M n (prism R M f g n φ)) := by
  rw [cochainComplexMap_f_cochainClass, cochainComplexMap_f_cochainClass,
    cochainComplex_d_cochainClass, ← map_add, cochainClass_eq_cochainClass_iff]
  convert isLocallyZero_prism (R := R) h using 1
  funext x
  rw [Pi.sub_apply, Pi.add_apply, sub_add_eq_sub_sub,
    ← coboundary_prism_add_prism_coboundary_apply (R := R)]
  abel

variable (R M) in
/-- **Maps close relative to a cocycle induce the same class.** Let `z` be an Alexander–Spanier
`n`-cocycle of `Y`, represented by `φ`. If every point of `X` has a neighbourhood `V` such that the
coboundary of `φ` vanishes on all tuples of points of `f(V) ∪ g(V)`, then the continuous maps
`f g : X → Y` send the class of `z` to the same class in `H^n(X; M)`. -/
theorem cohomologyMap_homologyπ_eq_of_forall_nhds {f g : C(X, Y)} {n : ℕ}
    (z : (cochainComplex R Y M).cycles n) {φ : (Fin (n + 1) → Y) → M}
    (hz : ((cochainComplex R Y M).iCycles n).hom z = cochainClass R Y M n φ)
    (h : ∀ x, ∃ V ∈ 𝓝 x, ∀ y : Fin (n + 2) → Y, (∀ i, y i ∈ f '' V ∪ g '' V) →
      ∑ i : Fin (n + 2), (-1 : ℤ) ^ (i : ℕ) • φ (y ∘ Fin.succAbove i) = 0) :
    (cohomologyMap R M f n).hom (((cochainComplex R Y M).homologyπ n).hom z) =
      (cohomologyMap R M g n).hom (((cochainComplex R Y M).homologyπ n).hom z) := by
  have hnat (k : C(X, Y)) :
      (cohomologyMap R M k n).hom (((cochainComplex R Y M).homologyπ n).hom z) =
        ((cochainComplex R X M).homologyπ n).hom
          ((HomologicalComplex.cyclesMap (cochainComplexMap R M k) n).hom z) :=
    (ConcreteCategory.congr_hom
      (HomologicalComplex.homologyπ_naturality (cochainComplexMap R M k) n) z)
  rw [hnat, hnat]
  have hinj := (ModuleCat.mono_iff_injective ((cochainComplex R X M).iCycles n)).1 inferInstance
  have hi (k : C(X, Y)) : ((cochainComplex R X M).iCycles n).hom
      ((HomologicalComplex.cyclesMap (cochainComplexMap R M k) n).hom z) =
        ((cochainComplexMap R M k).f n).hom (cochainClass R Y M n φ) := by
    rw [← ConcreteCategory.comp_apply, HomologicalComplex.cyclesMap_i, ConcreteCategory.comp_apply,
      hz]
  cases n with
  | zero =>
    -- In degree zero the pullbacks of `φ` along `f` and `g` agree.
    congr 1
    refine hinj ?_
    rw [hi, hi]
    exact cochainComplexMap_f_zero_cochainClass_eq_of_forall_nhds R M h
  | succ m =>
    -- In positive degree they differ by the coboundary of the prism of `φ`.
    have key : (HomologicalComplex.cyclesMap (cochainComplexMap R M g) (m + 1)).hom z =
        (HomologicalComplex.cyclesMap (cochainComplexMap R M f) (m + 1)).hom z +
          ((cochainComplex R X M).toCycles m (m + 1)).hom
            (cochainClass R X M m (prism R M f g m φ)) := by
      refine hinj ?_
      rw [map_add, hi, hi, ← ConcreteCategory.comp_apply, HomologicalComplex.toCycles_i]
      exact cochainComplexMap_f_succ_cochainClass_eq_add_of_forall_nhds R M h
    have h0 : ((cochainComplex R X M).homologyπ (m + 1)).hom
        (((cochainComplex R X M).toCycles m (m + 1)).hom
          (cochainClass R X M m (prism R M f g m φ))) = 0 := by
      rw [← ConcreteCategory.comp_apply, HomologicalComplex.toCycles_comp_homologyπ]
      simp
    rw [key, map_add, h0, add_zero]

/-- **The tube lemma for homotopies.** Let `F` be a homotopy of maps out of a compact space `X`,
and `ψ` a locally zero function on tuples of points of `Y`. For all `s` near `t`, the maps `F_s` and
`F_t` are close relative to `ψ`: every point of `X` has a neighbourhood `V` such that `ψ` vanishes
on all tuples of points of `F_s(V) ∪ F_t(V)`. -/
private lemma eventually_forall_exists_nhds_of_isLocallyZero [CompactSpace X] {ι : Type*}
    {f₀ f₁ : C(X, Y)} (F : f₀.Homotopy f₁) {ψ : (ι → Y) → M} (hψ : IsLocallyZero ψ)
    (t : unitInterval) :
    ∀ᶠ s in 𝓝 t, ∀ x, ∃ V ∈ 𝓝 x, ∀ y : ι → Y,
      (∀ i, y i ∈ F.curry s '' V ∪ F.curry t '' V) → ψ y = 0 := by
  have hclose : ∀ᶠ s in 𝓝 t, ∀ x ∈ Set.univ, ∃ V ∈ 𝓝 x, ∀ y : ι → Y,
      (∀ i, y i ∈ F.curry s '' V ∪ F.curry t '' V) → ψ y = 0 := by
    refine isCompact_univ.eventually_forall_of_forall_eventually fun x _ ↦ ?_
    obtain ⟨U, hU, hψU⟩ := isLocallyZero_iff.1 hψ (F (t, x))
    obtain ⟨A, hA, B, hB, hAB⟩ :=
      mem_nhds_prod_iff.1 (F.continuous.continuousAt.preimage_mem_nhds hU)
    obtain ⟨B', hB'B, hB'o, hxB'⟩ := mem_nhds_iff.1 hB
    filter_upwards [prod_mem_nhds hA (hB'o.mem_nhds hxB')] with p hp
    refine ⟨B', hB'o.mem_nhds hp.2, fun y hy ↦ hψU y fun i ↦ ?_⟩
    rcases hy i with ⟨b, hb, hby⟩ | ⟨b, hb, hby⟩
    · rw [← hby, F.curry_apply]
      exact hAB ⟨hp.1, hB'B hb⟩
    · rw [← hby, F.curry_apply]
      exact hAB ⟨mem_of_mem_nhds hA, hB'B hb⟩
  filter_upwards [hclose] with s hs x using hs x trivial

variable (R M) in
/-- **Homotopy invariance of Alexander–Spanier cohomology.** Homotopic continuous maps
`f₀ f₁ : X → Y` out of a compact space induce the same map `H^n(Y; M) ⟶ H^n(X; M)`. -/
theorem cohomologyMap_eq_of_homotopic [CompactSpace X] {f₀ f₁ : C(X, Y)}
    (h : f₀.Homotopic f₁) (n : ℕ) : cohomologyMap R M f₀ n = cohomologyMap R M f₁ n := by
  obtain ⟨F⟩ := h
  ext c
  obtain ⟨z, rfl⟩ := (ModuleCat.epi_iff_surjective ((cochainComplex R Y M).homologyπ n)).1
    inferInstance c
  obtain ⟨φ, hφ⟩ := cochainClass_surjective (R := R) n (((cochainComplex R Y M).iCycles n).hom z)
  -- The coboundary of the cocycle `φ` is locally zero.
  have hδ : IsLocallyZero fun y : Fin (n + 2) → Y ↦
      ∑ i : Fin (n + 2), (-1 : ℤ) ^ (i : ℕ) • φ (y ∘ Fin.succAbove i) := by
    rw [← cochainClass_eq_zero_iff (R := R), ← cochainComplex_d_cochainClass, hφ,
      ← ConcreteCategory.comp_apply, HomologicalComplex.iCycles_d]
    simp
  -- The class `F_t^* [φ]` is a locally constant function of `t`, since `F_s` and `F_t` are close
  -- relative to the coboundary of `φ` for all `s` near `t`.
  have hT : IsLocallyConstant fun t : unitInterval ↦
      (cohomologyMap R M (F.curry t) n).hom (((cochainComplex R Y M).homologyπ n).hom z) := by
    refine (IsLocallyConstant.iff_eventually_eq _).2 fun t ↦ ?_
    filter_upwards [eventually_forall_exists_nhds_of_isLocallyZero F hδ t] with s hs
    exact cohomologyMap_homologyπ_eq_of_forall_nhds R M z hφ.symm hs
  have h01 := hT.apply_eq_of_preconnectedSpace 0 1
  rwa [F.curry_zero, F.curry_one] at h01

variable (R M) in
/-- A homotopy equivalence `e : X ≃ₕ Y` between compact spaces induces isomorphisms
`H^n(Y; M) ≅ H^n(X; M)` in Alexander–Spanier cohomology, given by pulling back along `e` and along
its homotopy inverse. -/
def cohomologyIsoOfHomotopyEquiv [CompactSpace X] [CompactSpace Y]
    (e : ContinuousMap.HomotopyEquiv X Y) (n : ℕ) :
    cohomology R Y M n ≅ cohomology R X M n where
  hom := cohomologyMap R M e.toFun n
  inv := cohomologyMap R M e.invFun n
  hom_inv_id := by
    rw [← cohomologyMap_comp, cohomologyMap_eq_of_homotopic R M e.right_inv, cohomologyMap_id]
  inv_hom_id := by
    rw [← cohomologyMap_comp, cohomologyMap_eq_of_homotopic R M e.left_inv, cohomologyMap_id]

/-- The isomorphism induced by a homotopy equivalence `e` is pullback along `e`. -/
@[simp]
lemma cohomologyIsoOfHomotopyEquiv_hom [CompactSpace X] [CompactSpace Y]
    (e : ContinuousMap.HomotopyEquiv X Y) (n : ℕ) :
    (cohomologyIsoOfHomotopyEquiv R M e n).hom = cohomologyMap R M e.toFun n :=
  (rfl)

/-- The inverse of the isomorphism induced by a homotopy equivalence `e` is pullback along the
homotopy inverse of `e`. -/
@[simp]
lemma cohomologyIsoOfHomotopyEquiv_inv [CompactSpace X] [CompactSpace Y]
    (e : ContinuousMap.HomotopyEquiv X Y) (n : ℕ) :
    (cohomologyIsoOfHomotopyEquiv R M e n).inv = cohomologyMap R M e.invFun n :=
  (rfl)

end Homotopy

section Pairs

variable {R : Type w} [Ring R] {M : Type v} [AddCommGroup M] [Module R M] {X Y : Type u}
  [TopologicalSpace X] [TopologicalSpace Y] {B : Set X} {A : Set Y}

variable (R M) in
/-- **Maps of pairs close relative to a cocycle induce the same relative class.** Let `f g : X → Y`
be maps of pairs `(X, B) → (Y, A)`, and let `z` be a relative Alexander–Spanier `n`-cocycle of
`(Y, A)`, represented by a function `φ` that vanishes on all tuples of points of `A`. If every point
of `X` has a neighbourhood `V` such that the coboundary of `φ` vanishes on all tuples of points of
`f(V) ∪ g(V)`, then `f` and `g` send the class of `z` to the same class in `H^n(X, B; M)`. -/
theorem homologyMap_relativeCochainComplexMap_homologyπ_eq_of_forall_nhds {f g : C(X, Y)}
    (hf : Set.MapsTo f B A) (hg : Set.MapsTo g B A) {n : ℕ}
    (z : (relativeCochainComplex R M A).cycles n) {φ : (Fin (n + 1) → Y) → M}
    (hz : ((relativeCochainComplexι R M A).f n).hom
      (((relativeCochainComplex R M A).iCycles n).hom z) = cochainClass R Y M n φ)
    (hφA : ∀ y : Fin (n + 1) → Y, (∀ i, y i ∈ A) → φ y = 0)
    (h : ∀ x, ∃ V ∈ 𝓝 x, ∀ y : Fin (n + 2) → Y, (∀ i, y i ∈ f '' V ∪ g '' V) →
      ∑ i : Fin (n + 2), (-1 : ℤ) ^ (i : ℕ) • φ (y ∘ Fin.succAbove i) = 0) :
    (HomologicalComplex.homologyMap (relativeCochainComplexMap R M A B f hf) n).hom
        (((relativeCochainComplex R M A).homologyπ n).hom z) =
      (HomologicalComplex.homologyMap (relativeCochainComplexMap R M A B g hg) n).hom
        (((relativeCochainComplex R M A).homologyπ n).hom z) := by
  rw [HomologicalComplex.moduleCat_homologyMap_homologyπ,
    HomologicalComplex.moduleCat_homologyMap_homologyπ]
  -- A relative cocycle of `(X, B)` is determined by the underlying absolute cochain of `X`.
  have hinj : Function.Injective fun c : (relativeCochainComplex R M B).cycles n ↦
      (relativeCochainComplexι R M B).f n ((relativeCochainComplex R M B).iCycles n c) :=
    (relativeCochainComplexι_f_injective R M B n).comp
      ((relativeCochainComplex R M B).moduleCat_iCycles_injective n)
  have hi (k : C(X, Y)) (hk : Set.MapsTo k B A) :
      (relativeCochainComplexι R M B).f n ((relativeCochainComplex R M B).iCycles n
        (HomologicalComplex.cyclesMap (relativeCochainComplexMap R M A B k hk) n z)) =
        (cochainComplexMap R M k).f n (cochainClass R Y M n φ) := by
    rw [HomologicalComplex.moduleCat_iCycles_cyclesMap_apply,
      relativeCochainComplexι_f_relativeCochainComplexMap_f_apply, hz]
  cases n with
  | zero =>
    -- In degree zero the pullbacks of `φ` along `f` and `g` agree.
    congr 1
    refine hinj ?_
    simp only
    rw [hi, hi]
    exact cochainComplexMap_f_zero_cochainClass_eq_of_forall_nhds R M h
  | succ m =>
    -- In positive degree they differ by the coboundary of the prism of `φ`. The prism is a
    -- relative cochain of `(X, B)`: it vanishes on tuples of points of `B`, since every entry of
    -- its prism tuples then lies in `f(B) ∪ g(B) ⊆ A`.
    obtain ⟨c, hc⟩ : cochainClass R X M m (prism R M f g m φ) ∈
        LinearMap.range ((relativeCochainComplexι R M B).f m).hom := by
      exact mem_range_relativeCochainComplexι_f_iff.2 <| isLocallyZero_iff.2 fun _ ↦
        ⟨Set.univ, Filter.univ_mem, fun y _ ↦
          prism_apply_eq_zero_of_mapsTo hf hg hφA fun i ↦ (y i).prop⟩
    have key : (HomologicalComplex.cyclesMap (relativeCochainComplexMap R M A B g hg)
          (m + 1)).hom z =
        (HomologicalComplex.cyclesMap (relativeCochainComplexMap R M A B f hf) (m + 1)).hom z +
          ((relativeCochainComplex R M B).toCycles m (m + 1)).hom c := by
      refine hinj ?_
      simp only
      rw [map_add, map_add, hi, hi, HomologicalComplex.moduleCat_iCycles_toCycles_apply,
        ← HomologicalComplex.Hom.comm_apply, hc]
      exact cochainComplexMap_f_succ_cochainClass_eq_add_of_forall_nhds R M h
    have h0 : (relativeCochainComplex R M B).homologyπ (m + 1)
        ((relativeCochainComplex R M B).toCycles m (m + 1) c) = 0 :=
      (HomologicalComplex.moduleCat_homologyπ_eq_zero_iff _ (by simp) _).2 ⟨c, rfl⟩
    rw [key, map_add, h0, add_zero]

variable (R M) in
/-- **Homotopy invariance of relative Alexander–Spanier cohomology.** Let `X` be compact and `A`
closed in `Y`. Maps of pairs `f₀ f₁ : (X, B) → (Y, A)` that are homotopic through maps of pairs
induce the same map `H^n(Y, A; M) ⟶ H^n(X, B; M)`. -/
theorem homologyMap_relativeCochainComplexMap_eq_of_homotopicWith [CompactSpace X]
    (hA : IsClosed A) {f₀ f₁ : C(X, Y)} (h₀ : Set.MapsTo f₀ B A) (h₁ : Set.MapsTo f₁ B A)
    (h : f₀.HomotopicWith f₁ fun f ↦ Set.MapsTo f B A) (n : ℕ) :
    HomologicalComplex.homologyMap (relativeCochainComplexMap R M A B f₀ h₀) n =
      HomologicalComplex.homologyMap (relativeCochainComplexMap R M A B f₁ h₁) n := by
  obtain ⟨F⟩ := h
  ext c
  obtain ⟨z, rfl⟩ := (relativeCochainComplex R M A).moduleCat_homologyπ_surjective n c
  -- Since `A` is closed, the cocycle `z` is represented by a function vanishing on `A`.
  obtain ⟨φ, hφ, hφA⟩ := exists_relativeCochainComplexι_f_eq_cochainClass_of_isClosed hA
    (((relativeCochainComplex R M A).iCycles n).hom z)
  -- The coboundary of `φ` is locally zero.
  have hδ : IsLocallyZero fun y : Fin (n + 2) → Y ↦
      ∑ i : Fin (n + 2), (-1 : ℤ) ^ (i : ℕ) • φ (y ∘ Fin.succAbove i) := by
    rw [← cochainClass_eq_zero_iff (R := R), ← cochainComplex_d_cochainClass, ← hφ,
      HomologicalComplex.Hom.comm_apply, HomologicalComplex.moduleCat_d_iCycles_apply, map_zero]
  -- The class `F_t^* [z]` is a locally constant function of `t`.
  have hT : IsLocallyConstant fun t : unitInterval ↦
      (HomologicalComplex.homologyMap (relativeCochainComplexMap R M A B _ (F.prop t)) n).hom
        (((relativeCochainComplex R M A).homologyπ n).hom z) := by
    refine (IsLocallyConstant.iff_eventually_eq _).2 fun t ↦ ?_
    filter_upwards [eventually_forall_exists_nhds_of_isLocallyZero F.toHomotopy hδ t] with s hs
    exact homologyMap_relativeCochainComplexMap_homologyπ_eq_of_forall_nhds R M _ _ z hφ hφA hs
  have h01 := hT.apply_eq_of_preconnectedSpace 0 1
  simp only [F.toHomotopy.curry_zero, F.toHomotopy.curry_one] at h01
  exact h01

variable (R M) in
/-- A homotopy equivalence of pairs `f : (X, B) → (Y, A)`, with homotopy inverse
`g : (Y, A) → (X, B)` and both composites homotopic to the identity through maps of pairs, between
compact spaces with closed subspaces, induces isomorphisms `H^n(Y, A; M) ≅ H^n(X, B; M)` in
relative Alexander–Spanier cohomology, given by pulling back along `f` and along `g`. -/
def relativeCohomologyIsoOfHomotopicWith [CompactSpace X] [CompactSpace Y] (hB : IsClosed B)
    (hA : IsClosed A) {f : C(X, Y)} {g : C(Y, X)} (hf : Set.MapsTo f B A)
    (hg : Set.MapsTo g A B)
    (hgf : (g.comp f).HomotopicWith (ContinuousMap.id X) fun k ↦ Set.MapsTo k B B)
    (hfg : (f.comp g).HomotopicWith (ContinuousMap.id Y) fun k ↦ Set.MapsTo k A A) (n : ℕ) :
    relativeCohomology R M A n ≅ relativeCohomology R M B n where
  hom := HomologicalComplex.homologyMap (relativeCochainComplexMap R M A B f hf) n
  inv := HomologicalComplex.homologyMap (relativeCochainComplexMap R M B A g hg) n
  hom_inv_id := by
    have hid : Set.MapsTo (ContinuousMap.id Y) A A := Set.mapsTo_id A
    rw [← HomologicalComplex.homologyMap_comp, ← relativeCochainComplexMap_comp,
      homologyMap_relativeCochainComplexMap_eq_of_homotopicWith R M hA _ hid hfg,
      relativeCochainComplexMap_id, HomologicalComplex.homologyMap_id]
  inv_hom_id := by
    have hid : Set.MapsTo (ContinuousMap.id X) B B := Set.mapsTo_id B
    rw [← HomologicalComplex.homologyMap_comp, ← relativeCochainComplexMap_comp,
      homologyMap_relativeCochainComplexMap_eq_of_homotopicWith R M hB _ hid hgf,
      relativeCochainComplexMap_id, HomologicalComplex.homologyMap_id]

/-- The isomorphism induced by a homotopy equivalence of pairs `f` is pullback along `f`. -/
@[simp]
lemma relativeCohomologyIsoOfHomotopicWith_hom [CompactSpace X] [CompactSpace Y]
    (hB : IsClosed B) (hA : IsClosed A) {f : C(X, Y)} {g : C(Y, X)} (hf : Set.MapsTo f B A)
    (hg : Set.MapsTo g A B)
    (hgf : (g.comp f).HomotopicWith (ContinuousMap.id X) fun k ↦ Set.MapsTo k B B)
    (hfg : (f.comp g).HomotopicWith (ContinuousMap.id Y) fun k ↦ Set.MapsTo k A A) (n : ℕ) :
    (relativeCohomologyIsoOfHomotopicWith R M hB hA hf hg hgf hfg n).hom =
      HomologicalComplex.homologyMap (relativeCochainComplexMap R M A B f hf) n :=
  (rfl)

/-- The inverse of the isomorphism induced by a homotopy equivalence of pairs is pullback along the
homotopy inverse `g`. -/
@[simp]
lemma relativeCohomologyIsoOfHomotopicWith_inv [CompactSpace X] [CompactSpace Y]
    (hB : IsClosed B) (hA : IsClosed A) {f : C(X, Y)} {g : C(Y, X)} (hf : Set.MapsTo f B A)
    (hg : Set.MapsTo g A B)
    (hgf : (g.comp f).HomotopicWith (ContinuousMap.id X) fun k ↦ Set.MapsTo k B B)
    (hfg : (f.comp g).HomotopicWith (ContinuousMap.id Y) fun k ↦ Set.MapsTo k A A) (n : ℕ) :
    (relativeCohomologyIsoOfHomotopicWith R M hB hA hf hg hgf hfg n).inv =
      HomologicalComplex.homologyMap (relativeCochainComplexMap R M B A g hg) n :=
  (rfl)

end Pairs

end TauCeti.AlexanderSpanier
