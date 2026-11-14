/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.PresentedGroup
public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Stable
import Mathlib.Data.Fintype.EquivFin

/-!
# Steinberg groups over a ring

For an associative unital ring `R` and an index type `ι`, the **Steinberg group**
`TauCeti.IndexedSteinbergGroup ι R` is the group presented on generators `x_{ij}(a)` for pairs of
distinct indices `i ≠ j` in `ι` and elements `a : R`, subject to the relations satisfied universally
by elementary transvections:

* additivity in the parameter: `x_{ij}(a) * x_{ij}(b) = x_{ij}(a + b)`;
* distant commutation: `⁅x_{ij}(a), x_{kl}(b)⁆ = 1` whenever `j ≠ k` and `i ≠ l`;
* the Chevalley commutator relation: `⁅x_{ij}(a), x_{jk}(b)⁆ = x_{ik}(a * b)` for pairwise
  distinct indices `i, j, k`.

The opposite-pair commutator `⁅x_{ij}(a), x_{ji}(b)⁆` is intentionally omitted: in size two there
are no three distinct indices, so `St₂(R)` is isomorphic to the free product of two copies of the
additive group `(R, +)`. As soon as every pair of distinct indices admits a third index distinct
from both—in particular when `ι` is finite of cardinality at least three or when `ι` is
infinite—each generator `x_{ij}(a) = ⁅x_{ik}(a), x_{kj}(1)⁆` is a commutator and the Steinberg
group is perfect.

Taking `ι = Fin n` yields the finite-rank Steinberg groups `Stₙ(R)`, with surjective canonical
homomorphisms onto the elementary subgroups `Eₙ(R) ≤ GLₙ(R)`. Taking `ι = ℕ` yields the **stable
Steinberg group** `TauCeti.SteinbergGroup R`, which is canonically isomorphic to the direct limit of
the finite-rank groups `Stₙ(R)` along the index inclusions `Fin m ↪ Fin n`.

## Main definitions

* `TauCeti.steinbergIndexedRels`: the Steinberg relation set on
  `FreeGroup ({p : ι × ι // p.1 ≠ p.2} × R)`.
* `TauCeti.IndexedSteinbergGroup`: the Steinberg group over `R` indexed by `ι`.
* `TauCeti.IndexedSteinbergGroup.x`: the Steinberg generator `x_{ij}(a)` for `i ≠ j`.
* `TauCeti.IndexedSteinbergGroup.xHom`: the root subgroup homomorphism
  `Multiplicative R →* St_ι(R)`.
* `TauCeti.IndexedSteinbergGroup.lift`: the universal property of `St_ι(R)` for families of
  elements satisfying the Steinberg relations.
* `TauCeti.IndexedSteinbergGroup.map`, `TauCeti.IndexedSteinbergGroup.mapEquiv`: functoriality in
  ring homomorphisms and ring isomorphisms.
* `TauCeti.IndexedSteinbergGroup.mapIndex`, `TauCeti.IndexedSteinbergGroup.congrIndex`:
  functoriality along injective maps and equivalences of index types.
* `TauCeti.IndexedSteinbergGroup.toGL`, `TauCeti.IndexedSteinbergGroup.toElementarySubgroup`:
  the homomorphisms `St_ι(R) →* GL ι R` and `St_ι(R) →* E_ι(R)` sending `x_{ij}(a)` to
  `TauCeti.transvectionUnit hij a`.
* `TauCeti.IndexedSteinbergGroup.finTwoEquivCoprod`: the isomorphism
  `St₂(R) ≃* Multiplicative R ∗ Multiplicative R`.
* `TauCeti.steinbergRels`, `TauCeti.SteinbergGroup`: the stable Steinberg presentation and group on
  `ℕ`, together with `TauCeti.SteinbergGroup.ofFin`, `TauCeti.SteinbergGroup.liftFin`, and
  `TauCeti.SteinbergGroup.directLimitEquiv`.

## Main results

* `TauCeti.IndexedSteinbergGroup.x_add`, `TauCeti.IndexedSteinbergGroup.x_zero`,
  `TauCeti.IndexedSteinbergGroup.x_inv`, `TauCeti.IndexedSteinbergGroup.commute_x`,
  `TauCeti.IndexedSteinbergGroup.commutatorElement_x`,
  `TauCeti.IndexedSteinbergGroup.commutatorElement_x_reverse`: the Steinberg relations and their
  consequences.
* `TauCeti.IndexedSteinbergGroup.isPerfect_of_three_le_card`,
  `TauCeti.IndexedSteinbergGroup.instIsPerfectOfInfinite`: perfectness in rank at least two
  (`|ι| ≥ 3` or `Infinite ι`).
* `TauCeti.IndexedSteinbergGroup.range_toGL`: the image of `St_ι(R)` in `GL ι R` is
  `TauCeti.elementarySubgroup ι R`.
* `TauCeti.SteinbergGroup.directLimitEquiv`: `St(R)` is isomorphic to the direct limit of
  `Stₙ(R)` over `n : ℕ`.

## References

* J. Milnor, *Introduction to Algebraic K-Theory*, Annals of Mathematics Studies 72 (1971), §5.
* C. A. Weibel, *The K-book: An Introduction to Algebraic K-Theory*, Graduate Studies in
  Mathematics 145 (2013), Chapter III, §5, Definition 5.1.
-/

public section

noncomputable section

open Matrix

open scoped commutatorElement

namespace TauCeti

/-! ## Indexed Steinberg presentations and groups -/

/-- The Steinberg relations on the generators `x_{ij}(a)` indexed by pairs of distinct elements of
`ι` and coefficients `a : R`: additivity `x_{ij}(a) * x_{ij}(b) = x_{ij}(a + b)`, distant
commutation `⁅x_{ij}(a), x_{kl}(b)⁆ = 1` when `j ≠ k` and `i ≠ l`, and the Chevalley commutator
relation `⁅x_{ij}(a), x_{jk}(b)⁆ = x_{ik}(a * b)` for pairwise distinct `i, j, k`, keeping the
order `a * b`. -/
def steinbergIndexedRels (ι : Type*) (R : Type*) [Ring R] :
    Set (FreeGroup ({p : ι × ι // p.1 ≠ p.2} × R)) :=
  {r | (∃ (p : {p : ι × ι // p.1 ≠ p.2}) (a b : R),
          r = FreeGroup.of (p, a) * FreeGroup.of (p, b) * (FreeGroup.of (p, a + b))⁻¹) ∨
       (∃ (p q : {p : ι × ι // p.1 ≠ p.2}) (a b : R), p.1.2 ≠ q.1.1 ∧ p.1.1 ≠ q.1.2 ∧
          r = FreeGroup.of (p, a) * FreeGroup.of (q, b) * (FreeGroup.of (p, a))⁻¹ *
            (FreeGroup.of (q, b))⁻¹) ∨
       (∃ (i j k : ι) (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k) (a b : R),
          r = FreeGroup.of (⟨(i, j), hij⟩, a) * FreeGroup.of (⟨(j, k), hjk⟩, b) *
            (FreeGroup.of (⟨(i, j), hij⟩, a))⁻¹ * (FreeGroup.of (⟨(j, k), hjk⟩, b))⁻¹ *
            (FreeGroup.of (⟨(i, k), hik⟩, a * b))⁻¹)}

/-- The **Steinberg group** indexed by `ι` over an associative unital ring `R`, presented on
generators `x_{ij}(a)` (`i ≠ j` in `ι`, `a : R`) subject to `TauCeti.steinbergIndexedRels ι R`. -/
abbrev IndexedSteinbergGroup (ι : Type*) (R : Type*) [Ring R] : Type _ :=
  PresentedGroup (steinbergIndexedRels ι R)

namespace IndexedSteinbergGroup

variable {ι κ μ R S T : Type*} [Ring R] [Ring S] [Ring T]

/-- The Steinberg generator `x_{ij}(a)` in `IndexedSteinbergGroup ι R` attached to a pair of
distinct indices `i ≠ j` and a ring element `a : R`. -/
def x {i j : ι} (hij : i ≠ j) (a : R) : IndexedSteinbergGroup ι R :=
  PresentedGroup.of (⟨(i, j), hij⟩, a)

/-- Each raw presentation generator `PresentedGroup.of (p, a)` is `x p.2 a`. -/
theorem of_eq_x (p : {p : ι × ι // p.1 ≠ p.2}) (a : R) :
    (PresentedGroup.of (p, a) : IndexedSteinbergGroup ι R) = x p.2 a :=
  (rfl)

/-! ### Defining relations and algebraic consequences -/

/-- Additivity of Steinberg generators in the parameter:
`x_{ij}(a + b) = x_{ij}(a) * x_{ij}(b)`. -/
@[simp]
theorem x_add {i j : ι} (hij : i ≠ j) (a b : R) :
    x hij (a + b) = x hij a * x hij b := by
  symm
  apply eq_of_mul_inv_eq_one
  have hmem : FreeGroup.of (⟨(i, j), hij⟩, a) * FreeGroup.of (⟨(i, j), hij⟩, b) *
      (FreeGroup.of (⟨(i, j), hij⟩, a + b))⁻¹ ∈ steinbergIndexedRels ι R :=
    Or.inl ⟨⟨(i, j), hij⟩, a, b, rfl⟩
  simpa only [x, PresentedGroup.of, ← map_inv, ← map_mul] using PresentedGroup.one_of_mem hmem

/-- The Steinberg generator with parameter zero is the identity. -/
@[simp]
theorem x_zero {i j : ι} (hij : i ≠ j) : x hij (0 : R) = 1 := by
  apply mul_left_cancel (a := x hij (0 : R))
  rw [← x_add, add_zero, mul_one]

/-- Inverting a Steinberg generator negates its ring parameter. -/
@[simp]
theorem x_inv {i j : ι} (hij : i ≠ j) (a : R) : (x hij a)⁻¹ = x hij (-a) :=
  inv_eq_of_mul_eq_one_right (by rw [← x_add, add_neg_cancel, x_zero])

/-- Subtraction in the parameter corresponds to multiplying by the inverse generator. -/
theorem x_sub {i j : ι} (hij : i ≠ j) (a b : R) : x hij (a - b) = x hij a * (x hij b)⁻¹ := by
  rw [sub_eq_add_neg, x_add, x_inv]

/-- The root subgroup homomorphism `Multiplicative R →* IndexedSteinbergGroup ι R` sending `a` to
`x_{ij}(a)`. -/
def xHom {i j : ι} (hij : i ≠ j) : Multiplicative R →* IndexedSteinbergGroup ι R where
  toFun a := x hij a.toAdd
  map_one' := x_zero hij
  map_mul' a b := x_add hij a.toAdd b.toAdd

@[simp]
theorem xHom_apply {i j : ι} (hij : i ≠ j) (a : Multiplicative R) :
    xHom hij a = x hij a.toAdd :=
  (rfl)

/-- Steinberg generators at non-chaining index pairs (`j ≠ k` and `l ≠ i`) commute. -/
theorem commute_x {i j k l : ι} (hij : i ≠ j) (hkl : k ≠ l) (hjk : j ≠ k) (hli : l ≠ i)
    (a b : R) : Commute (x hij a) (x hkl b) := by
  rw [← commutatorElement_eq_one_iff_commute, commutatorElement_def]
  have hmem : FreeGroup.of (⟨(i, j), hij⟩, a) * FreeGroup.of (⟨(k, l), hkl⟩, b) *
      (FreeGroup.of (⟨(i, j), hij⟩, a))⁻¹ * (FreeGroup.of (⟨(k, l), hkl⟩, b))⁻¹ ∈
      steinbergIndexedRels ι R :=
    Or.inr (Or.inl ⟨⟨(i, j), hij⟩, ⟨(k, l), hkl⟩, a, b, hjk, hli.symm, rfl⟩)
  simpa only [x, PresentedGroup.of, ← map_inv, ← map_mul] using PresentedGroup.one_of_mem hmem

/-- Steinberg generators at the same pair of indices commute. -/
theorem commute_x_self {i j : ι} (hij : i ≠ j) (a b : R) : Commute (x hij a) (x hij b) :=
  commute_x hij hij hij.symm hij.symm a b

/-- **The Chevalley commutator relation** in the Steinberg group: for pairwise distinct indices
`i, j, k`, `⁅x_{ij}(a), x_{jk}(b)⁆ = x_{ik}(a * b)`. -/
theorem commutatorElement_x {i j k : ι} (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k) (a b : R) :
    ⁅x hij a, x hjk b⁆ = x hik (a * b) := by
  apply eq_of_mul_inv_eq_one
  have hmem : FreeGroup.of (⟨(i, j), hij⟩, a) * FreeGroup.of (⟨(j, k), hjk⟩, b) *
      (FreeGroup.of (⟨(i, j), hij⟩, a))⁻¹ * (FreeGroup.of (⟨(j, k), hjk⟩, b))⁻¹ *
      (FreeGroup.of (⟨(i, k), hik⟩, a * b))⁻¹ ∈ steinbergIndexedRels ι R :=
    Or.inr (Or.inr ⟨i, j, k, hij, hjk, hik, a, b, rfl⟩)
  simpa only [commutatorElement_def, x, PresentedGroup.of, ← map_inv, ← map_mul] using
    PresentedGroup.one_of_mem hmem

/-- The reverse-chained commutator relation `⁅x_{ij}(a), x_{ki}(b)⁆ = x_{kj}(-(b * a))` for
pairwise distinct indices `i, j, k`, obtained from `commutatorElement_x` by inversion. -/
theorem commutatorElement_x_reverse {i j k : ι} (hij : i ≠ j) (hki : k ≠ i) (hkj : k ≠ j)
    (a b : R) : ⁅x hij a, x hki b⁆ = x hkj (-(b * a)) := by
  rw [← commutatorElement_inv, commutatorElement_x hki hij hkj, x_inv]

/-- Conjugating `x_{jk}(b)` by `x_{ij}(a)` for pairwise distinct `i, j, k` multiplies on the left by
`x_{ik}(a * b)`. -/
theorem mul_x_mul_inv {i j k : ι} (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k) (a b : R) :
    x hij a * x hjk b * (x hij a)⁻¹ = x hik (a * b) * x hjk b := by
  rw [← MulAut.conj_apply, conj_eq_commutatorElement_mul, commutatorElement_x hij hjk hik]

/-- Conjugating `x_{ki}(b)` by `x_{ij}(a)` for pairwise distinct `i, j, k` multiplies on the left by
`x_{kj}(-(b * a))`. -/
theorem mul_x_mul_inv_reverse {i j k : ι} (hij : i ≠ j) (hki : k ≠ i) (hkj : k ≠ j) (a b : R) :
    x hij a * x hki b * (x hij a)⁻¹ = x hkj (-(b * a)) * x hki b := by
  rw [← MulAut.conj_apply, conj_eq_commutatorElement_mul, commutatorElement_x_reverse hij hki hkj]

/-! ### Universal property and generation -/

/-- Two homomorphisms out of `IndexedSteinbergGroup ι R` agree when they agree on every generator
`x hij a`. -/
@[ext]
theorem hom_ext {G : Type*} [Group G] {φ ψ : IndexedSteinbergGroup ι R →* G}
    (h : ∀ ⦃i j : ι⦄ (hij : i ≠ j) (a : R), φ (x hij a) = ψ (x hij a)) : φ = ψ :=
  PresentedGroup.ext fun ⟨⟨_, _⟩, a⟩ ↦ h _ a

/-- A subgroup of `IndexedSteinbergGroup ι R` is the whole group if and only if it contains every
Steinberg generator `x hij a`. -/
theorem subgroup_eq_top_iff {H : Subgroup (IndexedSteinbergGroup ι R)} :
    H = ⊤ ↔ ∀ ⦃i j : ι⦄ (hij : i ≠ j) (a : R), x hij a ∈ H :=
  ⟨fun h _ _ _ _ ↦ h ▸ Subgroup.mem_top _,
    fun h ↦ top_unique fun z _ ↦ PresentedGroup.generated_by _ H (fun ⟨_, a⟩ ↦ h _ a) z⟩

private theorem lift_rels {G : Type*} [Group G] (f : ∀ ⦃i j : ι⦄, i ≠ j → R → G)
    (hadd : ∀ ⦃i j : ι⦄ (hij : i ≠ j) (a b : R), f hij (a + b) = f hij a * f hij b)
    (hcomm : ∀ ⦃i j k l : ι⦄ (hij : i ≠ j) (hkl : k ≠ l), j ≠ k → l ≠ i →
      ∀ a b : R, Commute (f hij a) (f hkl b))
    (hchain : ∀ ⦃i j k : ι⦄ (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k) (a b : R),
      ⁅f hij a, f hjk b⁆ = f hik (a * b)) :
    ∀ r ∈ steinbergIndexedRels ι R,
      FreeGroup.lift (fun pa : {p : ι × ι // p.1 ≠ p.2} × R ↦ f pa.1.2 pa.2) r = 1 := by
  rintro r (⟨⟨⟨i, j⟩, hij⟩, a, b, rfl⟩ | ⟨⟨⟨i, j⟩, hij⟩, ⟨⟨k, l⟩, hkl⟩, a, b, hjk, hik, rfl⟩ |
    ⟨i, j, k, hij, hjk, hik, a, b, rfl⟩)
  · simp [hadd hij a b]
  · simpa [commutatorElement_def] using
      commutatorElement_eq_one_iff_commute.mpr (hcomm hij hkl hjk hik.symm a b)
  · simpa [commutatorElement_def] using mul_inv_eq_one.mpr (hchain hij hjk hik a b)

/-- **Universal property of the Steinberg group**: a family of elements `f hij a : G` satisfying
additivity, distant commutation, and the Chevalley commutator relation extends uniquely to a group
homomorphism `IndexedSteinbergGroup ι R →* G`. -/
def lift {G : Type*} [Group G] (f : ∀ ⦃i j : ι⦄, i ≠ j → R → G)
    (hadd : ∀ ⦃i j : ι⦄ (hij : i ≠ j) (a b : R), f hij (a + b) = f hij a * f hij b)
    (hcomm : ∀ ⦃i j k l : ι⦄ (hij : i ≠ j) (hkl : k ≠ l), j ≠ k → l ≠ i →
      ∀ a b : R, Commute (f hij a) (f hkl b))
    (hchain : ∀ ⦃i j k : ι⦄ (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k) (a b : R),
      ⁅f hij a, f hjk b⁆ = f hik (a * b)) :
    IndexedSteinbergGroup ι R →* G :=
  PresentedGroup.toGroup (lift_rels f hadd hcomm hchain)

@[simp]
theorem lift_x {G : Type*} [Group G] (f : ∀ ⦃i j : ι⦄, i ≠ j → R → G)
    (hadd : ∀ ⦃i j : ι⦄ (hij : i ≠ j) (a b : R), f hij (a + b) = f hij a * f hij b)
    (hcomm : ∀ ⦃i j k l : ι⦄ (hij : i ≠ j) (hkl : k ≠ l), j ≠ k → l ≠ i →
      ∀ a b : R, Commute (f hij a) (f hkl b))
    (hchain : ∀ ⦃i j k : ι⦄ (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k) (a b : R),
      ⁅f hij a, f hjk b⁆ = f hik (a * b))
    {i j : ι} (hij : i ≠ j) (a : R) :
    lift f hadd hcomm hchain (x hij a) = f hij a :=
  PresentedGroup.toGroup.of _

/-! ### Functoriality in the ring and in the index type -/

/-- The homomorphism of Steinberg groups induced by a unital ring homomorphism `f : R →+* S`,
sending `x_{ij}(a)` to `x_{ij}(f a)`. -/
def map (f : R →+* S) : IndexedSteinbergGroup ι R →* IndexedSteinbergGroup ι S :=
  lift (fun _ _ hij a ↦ x hij (f a))
    (fun _ _ hij a b ↦ by rw [map_add, x_add])
    (fun _ _ _ _ hij hkl hjk hli a b ↦ commute_x hij hkl hjk hli (f a) (f b))
    (fun _ _ _ hij hjk hik a b ↦ by rw [commutatorElement_x hij hjk hik, map_mul])

@[simp]
theorem map_x (f : R →+* S) {i j : ι} (hij : i ≠ j) (a : R) :
    map f (x hij a) = x hij (f a) :=
  lift_x _ _ _ _ hij a

@[simp]
theorem map_id : map (RingHom.id R) = MonoidHom.id (IndexedSteinbergGroup ι R) := by
  ext i j hij a
  simp

theorem map_comp (g : S →+* T) (f : R →+* S) :
    map (ι := ι) (g.comp f) = (map g).comp (map f) := by
  ext i j hij a
  simp

@[simp]
theorem map_map (g : S →+* T) (f : R →+* S) (z : IndexedSteinbergGroup ι R) :
    map g (map f z) = map (g.comp f) z :=
  DFunLike.congr_fun (map_comp g f).symm z

/-- A ring isomorphism induces an isomorphism of Steinberg groups. -/
def mapEquiv (e : R ≃+* S) : IndexedSteinbergGroup ι R ≃* IndexedSteinbergGroup ι S :=
  MonoidHom.toMulEquiv (map e.toRingHom) (map e.symm.toRingHom)
    (by rw [← map_comp, e.symm_toRingHom_comp_toRingHom, map_id])
    (by rw [← map_comp, e.toRingHom_comp_symm_toRingHom, map_id])

@[simp]
theorem mapEquiv_x (e : R ≃+* S) {i j : ι} (hij : i ≠ j) (a : R) :
    mapEquiv e (x hij a) = x hij (e a) :=
  map_x e.toRingHom hij a

@[simp]
theorem mapEquiv_symm (e : R ≃+* S) :
    (mapEquiv (ι := ι) e).symm = mapEquiv e.symm :=
  MulEquiv.ext fun _ ↦ rfl

/-- An injective map of index types `e : ι ↪ κ` induces a homomorphism of Steinberg groups sending
`x_{ij}(a)` to `x_{e(i), e(j)}(a)`. -/
def mapIndex (e : ι ↪ κ) : IndexedSteinbergGroup ι R →* IndexedSteinbergGroup κ R :=
  lift (fun _ _ hij a ↦ x (e.injective.ne hij) a)
    (fun _ _ hij a b ↦ x_add (e.injective.ne hij) a b)
    (fun _ _ _ _ hij hkl hjk hli a b ↦
      commute_x (e.injective.ne hij) (e.injective.ne hkl) (e.injective.ne hjk)
        (e.injective.ne hli) a b)
    (fun _ _ _ hij hjk hik a b ↦
      commutatorElement_x (e.injective.ne hij) (e.injective.ne hjk) (e.injective.ne hik) a b)

@[simp]
theorem mapIndex_x (e : ι ↪ κ) {i j : ι} (hij : i ≠ j) (a : R) :
    mapIndex e (x hij a) = x (e.injective.ne hij) a :=
  lift_x _ _ _ _ hij a

@[simp]
theorem mapIndex_refl :
    mapIndex (Function.Embedding.refl ι) = MonoidHom.id (IndexedSteinbergGroup ι R) := by
  ext i j hij a
  simp

theorem mapIndex_trans (e₁ : ι ↪ κ) (e₂ : κ ↪ μ) :
    mapIndex (R := R) (e₁.trans e₂) = (mapIndex e₂).comp (mapIndex e₁) := by
  ext i j hij a
  simp

@[simp]
theorem mapIndex_mapIndex (e₁ : ι ↪ κ) (e₂ : κ ↪ μ) (z : IndexedSteinbergGroup ι R) :
    mapIndex e₂ (mapIndex e₁ z) = mapIndex (e₁.trans e₂) z :=
  DFunLike.congr_fun (mapIndex_trans e₁ e₂).symm z

/-- Coefficient functoriality and index functoriality commute. -/
theorem map_comp_mapIndex (f : R →+* S) (e : ι ↪ κ) :
    (map f).comp (mapIndex e) = (mapIndex e).comp (map f) := by
  ext i j hij a
  simp

/-- An equivalence of index types `e : ι ≃ κ` induces an isomorphism of Steinberg groups. -/
def congrIndex (e : ι ≃ κ) : IndexedSteinbergGroup ι R ≃* IndexedSteinbergGroup κ R :=
  MonoidHom.toMulEquiv (mapIndex e.toEmbedding) (mapIndex e.symm.toEmbedding)
    (by ext i j hij a; simp)
    (by ext i j hij a; simp)

@[simp]
theorem congrIndex_x (e : ι ≃ κ) {i j : ι} (hij : i ≠ j) (a : R) :
    congrIndex e (x hij a) = x (e.injective.ne hij) a :=
  mapIndex_x e.toEmbedding hij a

@[simp]
theorem congrIndex_symm (e : ι ≃ κ) :
    (congrIndex (R := R) e).symm = congrIndex e.symm :=
  MulEquiv.ext fun _ ↦ rfl

/-! ### Degenerate cases and `St₂(R)` as a free product -/

/-- Over a trivial ring every Steinberg generator is `x_{ij}(0) = 1`, so the Steinberg group is
trivial. -/
instance [Subsingleton R] : Subsingleton (IndexedSteinbergGroup ι R) := by
  have htop : (⊥ : Subgroup (IndexedSteinbergGroup ι R)) = ⊤ :=
    subgroup_eq_top_iff.mpr fun _ _ hij a ↦ by
      rw [Subsingleton.elim a 0, x_zero]
      exact Subgroup.one_mem _
  exact subsingleton_of_forall_eq 1 fun u ↦ Subgroup.mem_bot.mp (htop.symm ▸ Subgroup.mem_top u)

/-- When the index type has at most one element there are no distinct index pairs, so the Steinberg
group is trivial. -/
instance [Subsingleton ι] : Subsingleton (IndexedSteinbergGroup ι R) := by
  have htop : (⊥ : Subgroup (IndexedSteinbergGroup ι R)) = ⊤ :=
    subgroup_eq_top_iff.mpr fun i j hij _ ↦ (hij (Subsingleton.elim i j)).elim
  exact subsingleton_of_forall_eq 1 fun u ↦ Subgroup.mem_bot.mp (htop.symm ▸ Subgroup.mem_top u)

private def finTwoGenToCoprod ⦃i j : Fin 2⦄ (_ : i ≠ j) (a : R) :
    Monoid.Coprod (Multiplicative R) (Multiplicative R) :=
  if i = 0 then Monoid.Coprod.inl (Multiplicative.ofAdd a)
  else Monoid.Coprod.inr (Multiplicative.ofAdd a)

private def finTwoToCoprod :
    IndexedSteinbergGroup (Fin 2) R →*
      Monoid.Coprod (Multiplicative R) (Multiplicative R) :=
  lift finTwoGenToCoprod
    (fun i _ _ a b ↦ by
      dsimp only [finTwoGenToCoprod]
      split_ifs <;> rw [ofAdd_add, map_mul])
    (fun i j k _ hij _ hjk _ a b ↦ by
      have hik : i = k := by omega
      subst hik
      dsimp only [finTwoGenToCoprod]
      split_ifs <;> exact (Commute.all _ _).map _)
    (fun i j k hij hjk hik _ _ ↦ by omega)

/-- **In size two, `St₂(R)` is the free product `(R, +) ∗ (R, +)`.** Because `Fin 2` has no three
pairwise distinct indices, only additivity on `(0, 1)` and on `(1, 0)` holds, with no relation
between the two root subgroups. -/
def finTwoEquivCoprod :
    IndexedSteinbergGroup (Fin 2) R ≃*
      Monoid.Coprod (Multiplicative R) (Multiplicative R) := by
  let fromCoprod : Monoid.Coprod (Multiplicative R) (Multiplicative R) →*
      IndexedSteinbergGroup (Fin 2) R :=
    Monoid.Coprod.lift (xHom (i := (0 : Fin 2)) (j := 1) (by decide))
      (xHom (i := (1 : Fin 2)) (j := 0) (by decide))
  refine MonoidHom.toMulEquiv finTwoToCoprod fromCoprod ?_ ?_
  · ext i j hij a
    fin_cases i <;> fin_cases j
    · exact (hij rfl).elim
    · simp [finTwoToCoprod, fromCoprod, finTwoGenToCoprod]
    · simp [finTwoToCoprod, fromCoprod, finTwoGenToCoprod]
    · exact (hij rfl).elim
  · refine Monoid.Coprod.hom_ext (MonoidHom.ext fun a ↦ ?_) (MonoidHom.ext fun a ↦ ?_) <;>
      simp [finTwoToCoprod, fromCoprod, finTwoGenToCoprod]

@[simp]
theorem finTwoEquivCoprod_x_zero_one (a : R) :
    finTwoEquivCoprod (x (i := (0 : Fin 2)) (j := 1) (by decide) a) =
      Monoid.Coprod.inl (Multiplicative.ofAdd a) := by
  simp [finTwoEquivCoprod, finTwoToCoprod, finTwoGenToCoprod]

@[simp]
theorem finTwoEquivCoprod_x_one_zero (a : R) :
    finTwoEquivCoprod (x (i := (1 : Fin 2)) (j := 0) (by decide) a) =
      Monoid.Coprod.inr (Multiplicative.ofAdd a) := by
  simp [finTwoEquivCoprod, finTwoToCoprod, finTwoGenToCoprod]

/-! ### Perfectness -/

/-- When every pair of distinct indices in `ι` admits a third index distinct from both, every
Steinberg generator `x_{ij}(a) = ⁅x_{ik}(a), x_{kj}(1)⁆` is a commutator, so the Steinberg group is
perfect. -/
theorem isPerfect_of_forall_exists_ne
    (h : ∀ i j : ι, i ≠ j → ∃ k : ι, k ≠ i ∧ k ≠ j) :
    Group.IsPerfect (IndexedSteinbergGroup ι R) := by
  rw [Group.isPerfect_def, subgroup_eq_top_iff]
  intro i j hij a
  obtain ⟨k, hki, hkj⟩ := h i j hij
  rw [← mul_one a, ← commutatorElement_x hki.symm hkj hij]
  exact Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)

/-- For a finite index type of cardinality at least three, `IndexedSteinbergGroup ι R` is
perfect. -/
theorem isPerfect_of_three_le_card [Fintype ι] (h : 3 ≤ Fintype.card ι) :
    Group.IsPerfect (IndexedSteinbergGroup ι R) := by
  classical
  refine isPerfect_of_forall_exists_ne fun i j _ ↦ ?_
  obtain ⟨k, -, hk⟩ := Finset.exists_mem_notMem_of_card_lt_card (s := ({i, j} : Finset ι))
    (t := Finset.univ) (Finset.card_le_two.trans_lt (by rw [Finset.card_univ]; omega))
  exact ⟨k, by simpa [not_or] using hk⟩

/-- Over an infinite index type (such as `ℕ`), `IndexedSteinbergGroup ι R` is perfect. -/
instance instIsPerfectOfInfinite [Infinite ι] :
    Group.IsPerfect (IndexedSteinbergGroup ι R) := by
  classical
  refine isPerfect_of_forall_exists_ne fun i j _ ↦ ?_
  obtain ⟨k, hk⟩ := Infinite.exists_notMem_finset ({i, j} : Finset ι)
  exact ⟨k, by simpa [not_or] using hk⟩

/-! ### Projection onto the elementary subgroup of `GL ι R` -/

section FiniteIndex

variable [Fintype ι] [DecidableEq ι]

/-- The canonical homomorphism `St_ι(R) →* GL ι R` sending each generator `x_{ij}(a)` to the
elementary transvection `TauCeti.transvectionUnit hij a`. -/
def toGL : IndexedSteinbergGroup ι R →* GL ι R :=
  lift (fun _ _ hij a ↦ transvectionUnit hij a)
    (fun _ _ ↦ transvectionUnit_add)
    (fun _ _ _ _ ↦ commute_transvectionUnit)
    (fun _ _ _ ↦ commutatorElement_transvectionUnit)

@[simp]
theorem toGL_x {i j : ι} (hij : i ≠ j) (a : R) :
    toGL (x hij a) = transvectionUnit hij a :=
  lift_x _ _ _ _ hij a

/-- The image of `IndexedSteinbergGroup.toGL` in `GL ι R` is the elementary subgroup
`TauCeti.elementarySubgroup ι R`. -/
theorem range_toGL :
    (toGL (ι := ι) (R := R)).range = TauCeti.elementarySubgroup ι R := by
  refine le_antisymm ?_ (elementarySubgroup_le_iff.2 fun i j hij a ↦ ⟨x hij a, toGL_x hij a⟩)
  rintro _ ⟨z, rfl⟩
  have htop : z ∈ (TauCeti.elementarySubgroup ι R).comap toGL := by
    have : (TauCeti.elementarySubgroup ι R).comap (toGL (ι := ι) (R := R)) = ⊤ :=
      subgroup_eq_top_iff.mpr fun i j hij a ↦ by
        rw [Subgroup.mem_comap, toGL_x]
        exact transvectionUnit_mem_elementarySubgroup hij a
    rw [this]
    exact Subgroup.mem_top z
  exact htop

/-- The canonical surjective homomorphism `St_ι(R) →* E_ι(R)` onto the elementary subgroup. -/
def toElementarySubgroup :
    IndexedSteinbergGroup ι R →* TauCeti.elementarySubgroup ι R :=
  toGL.codRestrict (TauCeti.elementarySubgroup ι R) fun z ↦
    range_toGL (ι := ι) (R := R) ▸ ⟨z, rfl⟩

@[simp]
theorem coe_toElementarySubgroup (z : IndexedSteinbergGroup ι R) :
    (toElementarySubgroup z : GL ι R) = toGL z :=
  (rfl)

/-- The canonical homomorphism `St_ι(R) →* E_ι(R)` is surjective. -/
theorem toElementarySubgroup_surjective :
    Function.Surjective (toElementarySubgroup (ι := ι) (R := R)) := by
  rintro ⟨y, hy⟩
  rw [← range_toGL] at hy
  obtain ⟨z, rfl⟩ := hy
  exact ⟨z, rfl⟩

@[simp]
theorem ker_toElementarySubgroup :
    (toElementarySubgroup (ι := ι) (R := R)).ker = (toGL (ι := ι) (R := R)).ker := by
  ext z
  simp [MonoidHom.mem_ker, Subtype.ext_iff]

/-- Reindexing the Steinberg group along `e : ι ≃ κ` corresponds under `toGL` to `e.reindexGL R`. -/
theorem toGL_congrIndex [Fintype κ] [DecidableEq κ] (e : ι ≃ κ)
    (z : IndexedSteinbergGroup ι R) :
    toGL (congrIndex e z) = e.reindexGL R (toGL z) := by
  have hhom : (toGL (ι := κ) (R := R)).comp (congrIndex e).toMonoidHom =
      (e.reindexGL R).toMonoidHom.comp toGL := by
    ext i j hij a
    simp [Equiv.reindexGL_transvectionUnit]
  exact DFunLike.congr_fun hhom z

end FiniteIndex

/-- Along the standard inclusion `Fin m ↪ Fin n` (`m ≤ n`), `toGL` commutes with matrix
stabilization `TauCeti.stabilizeGL`. -/
theorem toGL_mapIndex_castLE {m n : ℕ} (h : m ≤ n) (z : IndexedSteinbergGroup (Fin m) R) :
    toGL (mapIndex (Fin.castLEEmb h) z) = stabilizeGL R h (toGL z) := by
  have hhom : (toGL (ι := Fin n) (R := R)).comp (mapIndex (Fin.castLEEmb h)) =
      (stabilizeGL R h).comp toGL := by
    ext i j hij a
    simp [stabilizeGL_transvectionUnit]
  exact DFunLike.congr_fun hhom z

end IndexedSteinbergGroup

/-! ## The stable Steinberg group and its colimit presentation -/

/-- The Steinberg relations on generators `x_{ij}(a)` indexed by all pairs of distinct natural
numbers `i ≠ j` and ring elements `a : R`. -/
abbrev steinbergRels (R : Type*) [Ring R] :
    Set (FreeGroup ({p : ℕ × ℕ // p.1 ≠ p.2} × R)) :=
  steinbergIndexedRels ℕ R

/-- The **stable Steinberg group** `St(R)` over an associative unital ring `R`, presented on
generators `x_{ij}(a)` indexed by all pairs of distinct natural numbers `i, j : ℕ` and `a : R`. -/
abbrev SteinbergGroup (R : Type*) [Ring R] : Type _ :=
  PresentedGroup (steinbergRels R)

namespace SteinbergGroup

variable {R S : Type*} [Ring R] [Ring S]

/-- Stabilization `Stₘ(R) →* Stₙ(R)` for `m ≤ n`, induced by `Fin.castLEEmb h : Fin m ↪ Fin n`. -/
abbrev stabilize {m n : ℕ} (h : m ≤ n) :
    IndexedSteinbergGroup (Fin m) R →* IndexedSteinbergGroup (Fin n) R :=
  IndexedSteinbergGroup.mapIndex (Fin.castLEEmb h)

/-- The finite-rank Steinberg groups `Stₙ(R)` with transition maps `stabilize` form a directed
system of groups indexed by `ℕ`. -/
instance : DirectedSystem (fun n : ℕ ↦ IndexedSteinbergGroup (Fin n) R)
    (fun _ _ h ↦ stabilize h) where
  map_self n u := by
    have hemb : Fin.castLEEmb (le_refl n) = Function.Embedding.refl (Fin n) := by ext; rfl
    simp [stabilize, hemb]
  map_map _ _ _ hij hjk u := by
    have hemb : (Fin.castLEEmb hij).trans (Fin.castLEEmb hjk) = Fin.castLEEmb (hij.trans hjk) := by
      ext; rfl
    simp [stabilize, hemb]

variable (R) in
/-- The canonical homomorphism `Stₙ(R) →* St(R)` induced by `Fin.valEmbedding : Fin n ↪ ℕ`. -/
def ofFin (n : ℕ) : IndexedSteinbergGroup (Fin n) R →* SteinbergGroup R :=
  IndexedSteinbergGroup.mapIndex Fin.valEmbedding

@[simp]
theorem ofFin_x {n : ℕ} {i j : Fin n} (hij : i ≠ j) (a : R) :
    ofFin R n (IndexedSteinbergGroup.x hij a) =
      IndexedSteinbergGroup.x (Fin.val_ne_of_ne hij) a :=
  IndexedSteinbergGroup.mapIndex_x Fin.valEmbedding hij a

@[simp]
theorem ofFin_stabilize {m n : ℕ} (h : m ≤ n) (u : IndexedSteinbergGroup (Fin m) R) :
    ofFin R n (stabilize h u) = ofFin R m u := by
  have hemb : (Fin.castLEEmb h).trans Fin.valEmbedding = Fin.valEmbedding := by ext; rfl
  simp [ofFin, stabilize, hemb]

theorem ofFin_comp_stabilize {m n : ℕ} (h : m ≤ n) :
    (ofFin R n).comp (stabilize h) = ofFin R m :=
  MonoidHom.ext (ofFin_stabilize h)

/-- The images of `Stₙ(R)` in `St(R)` increase monotonically with `n`. -/
private theorem monotone_range_ofFin : Monotone fun n ↦ (ofFin R n).range := by
  intro m n h
  dsimp only
  rw [← ofFin_comp_stabilize h, MonoidHom.range_comp]
  exact Subgroup.map_le_range _ _

/-- Every element of the stable Steinberg group `St(R)` lies in the image of `Stₙ(R)` for some
finite `n`. -/
theorem exists_ofFin (z : SteinbergGroup R) : ∃ n u, ofFin R n u = z := by
  have htop : (⨆ n, (ofFin R n).range) = ⊤ := by
    rw [IndexedSteinbergGroup.subgroup_eq_top_iff]
    intro i j hij a
    refine Subgroup.mem_iSup_of_mem (max i j + 1) ?_
    refine ⟨IndexedSteinbergGroup.x (i := ⟨i, by omega⟩) (j := ⟨j, by omega⟩)
      (fun h ↦ hij (congrArg Fin.val h)) a, ?_⟩
    exact ofFin_x _ a
  have hz : z ∈ ⨆ n, (ofFin R n).range := htop ▸ Subgroup.mem_top z
  rwa [Subgroup.mem_iSup_of_directed monotone_range_ofFin.directed_le] at hz

/-- Homomorphisms out of `St(R)` agree when their restrictions along `ofFin R n` agree for all
`n`. -/
theorem hom_ext_ofFin {G : Type*} [Group G] {φ ψ : SteinbergGroup R →* G}
    (h : ∀ n, φ.comp (ofFin R n) = ψ.comp (ofFin R n)) : φ = ψ := by
  refine MonoidHom.ext fun z ↦ ?_
  obtain ⟨n, u, rfl⟩ := exists_ofFin z
  exact DFunLike.congr_fun (h n) u

private theorem liftFin_apply_eq {G : Type*} [Group G]
    (f : ∀ n, IndexedSteinbergGroup (Fin n) R →* G)
    (hf : ∀ m n (h : m ≤ n) u, f n (stabilize h u) = f m u)
    {i j : ℕ} (hij : i ≠ j) (a : R) {N : ℕ} (hi : i < N) (hj : j < N) :
    f (max i j + 1) (IndexedSteinbergGroup.x (i := ⟨i, by omega⟩) (j := ⟨j, by omega⟩)
      (fun h ↦ hij (congrArg Fin.val h)) a) =
    f N (IndexedSteinbergGroup.x (i := ⟨i, hi⟩) (j := ⟨j, hj⟩)
      (fun h ↦ hij (congrArg Fin.val h)) a) := by
  have hle : max i j + 1 ≤ N := by omega
  rw [← hf (max i j + 1) N hle, IndexedSteinbergGroup.mapIndex_x]
  rfl

/-- **Colimit universal property of `St(R)`**: a compatible family of homomorphisms out of the
finite-rank Steinberg groups `Stₙ(R)` induces a homomorphism out of `St(R)`. -/
def liftFin {G : Type*} [Group G] (f : ∀ n, IndexedSteinbergGroup (Fin n) R →* G)
    (hf : ∀ m n (h : m ≤ n) u, f n (stabilize h u) = f m u) : SteinbergGroup R →* G :=
  IndexedSteinbergGroup.lift
    (fun i j hij a ↦ f (max i j + 1)
      (IndexedSteinbergGroup.x (i := ⟨i, by omega⟩) (j := ⟨j, by omega⟩)
        (fun h ↦ hij (congrArg Fin.val h)) a))
    (fun _ _ _ a b ↦ by rw [IndexedSteinbergGroup.x_add, map_mul])
    (fun i j k l hij hkl hjk hli a b ↦ by
      let N := max (max i j) (max k l) + 1
      rw [liftFin_apply_eq f hf hij a (N := N) (by omega) (by omega),
        liftFin_apply_eq f hf hkl b (N := N) (by omega) (by omega)]
      exact (IndexedSteinbergGroup.commute_x
        (i := (⟨i, by omega⟩ : Fin N)) (j := ⟨j, by omega⟩)
        (k := ⟨k, by omega⟩) (l := ⟨l, by omega⟩)
        (fun h ↦ hij (congrArg Fin.val h)) (fun h ↦ hkl (congrArg Fin.val h))
        (fun h ↦ hjk (congrArg Fin.val h)) (fun h ↦ hli (congrArg Fin.val h)) a b).map (f N))
    (fun i j k hij hjk hik a b ↦ by
      let N := max (max i j) k + 1
      rw [liftFin_apply_eq f hf hij a (N := N) (by omega) (by omega),
        liftFin_apply_eq f hf hjk b (N := N) (by omega) (by omega),
        liftFin_apply_eq f hf hik (a * b) (N := N) (by omega) (by omega),
        ← map_commutatorElement, IndexedSteinbergGroup.commutatorElement_x])

@[simp]
theorem liftFin_ofFin {G : Type*} [Group G] (f : ∀ n, IndexedSteinbergGroup (Fin n) R →* G)
    (hf : ∀ m n (h : m ≤ n) u, f n (stabilize h u) = f m u)
    (n : ℕ) (u : IndexedSteinbergGroup (Fin n) R) :
    liftFin f hf (ofFin R n u) = f n u := by
  have hhom : (liftFin f hf).comp (ofFin R n) = f n := by
    ext i j hij a
    simp only [MonoidHom.comp_apply, ofFin_x, liftFin, IndexedSteinbergGroup.lift_x]
    exact liftFin_apply_eq f hf (Fin.val_ne_of_ne hij) a i.2 j.2
  exact DFunLike.congr_fun hhom u

variable (R) in
/-- **The stable Steinberg group `St(R)` is canonically isomorphic to the direct limit of the
finite-rank Steinberg groups `Stₙ(R)`** along `stabilize`. -/
def directLimitEquiv :
    DirectLimit (fun n : ℕ ↦ IndexedSteinbergGroup (Fin n) R) (fun _ _ h ↦ stabilize h) ≃*
      SteinbergGroup R :=
  MonoidHom.toMulEquiv
    (DirectLimit.Monoid.lift _ (fun _ _ h ↦ stabilize h) (ofFin R)
      (fun _ _ h u ↦ ofFin_stabilize h u))
    (liftFin (DirectLimit.Monoid.of (fun n : ℕ ↦ IndexedSteinbergGroup (Fin n) R)
        (fun _ _ h ↦ stabilize h))
      (fun _ _ h u ↦ DirectLimit.Monoid.of_f
        (G := fun n : ℕ ↦ IndexedSteinbergGroup (Fin n) R) (f := fun _ _ h ↦ stabilize h) h u))
    (DirectLimit.Monoid.hom_ext fun n ↦ MonoidHom.ext fun u ↦ by simp)
    (hom_ext_ofFin fun n ↦ MonoidHom.ext fun u ↦ by simp)

theorem directLimitEquiv_of (n : ℕ) (u : IndexedSteinbergGroup (Fin n) R) :
    directLimitEquiv R (DirectLimit.Monoid.of (fun n : ℕ ↦ IndexedSteinbergGroup (Fin n) R)
      (fun _ _ h ↦ stabilize h) n u) = ofFin R n u :=
  DirectLimit.Monoid.lift_of (ofFin R) (fun _ _ h v ↦ ofFin_stabilize h v) n u

@[simp]
theorem directLimitEquiv_mk (n : ℕ) (u : IndexedSteinbergGroup (Fin n) R) :
    directLimitEquiv R ⟦⟨n, u⟩⟧ = ofFin R n u := by
  rw [← DirectLimit.Monoid.of_apply, directLimitEquiv_of]

@[simp]
theorem directLimitEquiv_symm_ofFin (n : ℕ) (u : IndexedSteinbergGroup (Fin n) R) :
    (directLimitEquiv R).symm (ofFin R n u) = ⟦⟨n, u⟩⟧ :=
  (directLimitEquiv R).symm_apply_eq.mpr (directLimitEquiv_mk n u).symm

end SteinbergGroup

end TauCeti
