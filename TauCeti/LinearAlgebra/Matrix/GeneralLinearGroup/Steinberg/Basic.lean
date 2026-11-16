/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.Coprod.Basic
public import Mathlib.GroupTheory.IsPerfect
public import Mathlib.GroupTheory.PresentedGroup
public import Mathlib.Order.DirectedInverseSystem
public import Mathlib.SetTheory.Cardinal.NatCard
public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Elementary
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Tactic.Group
import TauCeti.GroupTheory.PresentedGroup

/-!
# Steinberg groups over a ring

For an associative unital ring `R` and an index type `ι`, the **Steinberg group**
`SteinbergGroup ι R` is presented on generators `xᵢⱼ(a)` for distinct indices `i ≠ j` in `ι` and
`a ∈ R`, subject to the Steinberg relations:

* additivity: `xᵢⱼ(a) xᵢⱼ(b) = xᵢⱼ(a + b)`;
* distant commutation: `⁅xᵢⱼ(a), xₖₗ(b)⁆ = 1` whenever `j ≠ k` and `i ≠ l`;
* chaining commutator: `⁅xᵢⱼ(a), xⱼₖ(b)⁆ = xᵢₖ(a * b)` for pairwise distinct `i, j, k`.

No relation is imposed between opposite roots `xᵢⱼ(a)` and `xⱼᵢ(b)`. The reverse chaining relation
`⁅xᵢⱼ(a), xₖᵢ(b)⁆ = xₖⱼ(-(b * a))` follows from the forward relation by inverting the commutator.
In particular, when `ι = Fin 2` there are no triples of distinct indices and
`SteinbergGroup (Fin 2) R` is the free product of two copies of the additive group of `R`; when
`ι` has at least three elements, `SteinbergGroup ι R` is perfect.

When `ι` is finite, sending `xᵢⱼ(a)` to the elementary matrix `TauCeti.transvectionUnit hij a`
gives a homomorphism `toGL : SteinbergGroup ι R →* GL ι R` whose image is
`TauCeti.elementarySubgroup ι R`.

## Main definitions

* `TauCeti.steinbergRels`: the Steinberg relator set in the free group on distinct index pairs
  times `R`.
* `TauCeti.SteinbergGroup`: the Steinberg group `PresentedGroup (steinbergRels ι R)`.
* `TauCeti.SteinbergGroup.of`, `TauCeti.SteinbergGroup.ofHom`: the root generators `xᵢⱼ(a)` and
  their one-parameter subgroups `Multiplicative R →* SteinbergGroup ι R`.
* `TauCeti.SteinbergGroup.lift`: the universal property of `SteinbergGroup ι R`.
* `TauCeti.SteinbergGroup.map`, `TauCeti.SteinbergGroup.reindex`, `TauCeti.SteinbergGroup.congr`,
  `TauCeti.SteinbergGroup.stabilize`: functoriality in rings and injective index maps.
* `TauCeti.SteinbergGroup.finTwoEquivCoprod`: `St₂(R)` is the free product of two copies of
  `Multiplicative R`.
* `TauCeti.SteinbergGroup.prodEquiv`: `SteinbergGroup ι` preserves binary products of rings when
  every distinct index pair admits a third index.
* `TauCeti.SteinbergGroup.toGL`, `TauCeti.SteinbergGroup.toElementary`: the canonical homomorphisms
  onto `TauCeti.elementarySubgroup ι R`.

## Main results

* `TauCeti.SteinbergGroup.commutatorElement_of_reverse`: `⁅xᵢⱼ(a), xₖᵢ(b)⁆ = xₖⱼ(-(b * a))`.
* `TauCeti.SteinbergGroup.isPerfect`, `TauCeti.SteinbergGroup.isPerfect_of_three_le_enatCard`:
  `SteinbergGroup ι R` is perfect whenever every distinct pair admits a third index.
* `TauCeti.SteinbergGroup.range_toGL`: the image of `toGL` is `TauCeti.elementarySubgroup ι R`.

## References

* J. Milnor, *Introduction to Algebraic K-Theory*, Annals of Mathematics Studies 72 (1971), §5.
* C. A. Weibel, *The K-book: An Introduction to Algebraic K-Theory*, Graduate Studies in
  Mathematics 145 (2013), Chapter III, §5, Definition 5.1.
-/

public section

open Matrix

open scoped commutatorElement

namespace TauCeti

universe w u v

/-! ## Definition and defining relations -/

/-- The Steinberg relators on the generators `xᵢⱼ(a)` for distinct indices `i ≠ j` in `ι` and
`a ∈ R`: additivity `xᵢⱼ(a) xᵢⱼ(b) = xᵢⱼ(a + b)`, distant commutation `⁅xᵢⱼ(a), xₖₗ(b)⁆ = 1`
when `j ≠ k` and `i ≠ l`, and the chaining commutator `⁅xᵢⱼ(a), xⱼₖ(b)⁆ = xᵢₖ(a * b)` for
pairwise distinct `i, j, k`. Opposite roots have no imposed relation. -/
def steinbergRels (ι : Type w) (R : Type u) [Ring R] :
    Set (FreeGroup ({p : ι × ι // p.1 ≠ p.2} × R)) :=
  {r | (∃ (p : {p : ι × ι // p.1 ≠ p.2}) (a b : R),
          r = FreeGroup.of (p, a) * FreeGroup.of (p, b) * (FreeGroup.of (p, a + b))⁻¹) ∨
       (∃ (p q : {p : ι × ι // p.1 ≠ p.2}) (a b : R), p.1.2 ≠ q.1.1 ∧ p.1.1 ≠ q.1.2 ∧
          r = ⁅FreeGroup.of (p, a), FreeGroup.of (q, b)⁆) ∨
       (∃ (i j k : ι) (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k) (a b : R),
          r = ⁅FreeGroup.of ((⟨(i, j), hij⟩ : {p : ι × ι // p.1 ≠ p.2}), a),
                FreeGroup.of ((⟨(j, k), hjk⟩ : {p : ι × ι // p.1 ≠ p.2}), b)⁆ *
            (FreeGroup.of ((⟨(i, k), hik⟩ : {p : ι × ι // p.1 ≠ p.2}), a * b))⁻¹)}

/-- The **Steinberg group** `St_ι(R)` of an associative unital ring `R` over an index type `ι`,
presented by the Steinberg relations on root generators `xᵢⱼ(a)` (`i ≠ j`). -/
abbrev SteinbergGroup (ι : Type w) (R : Type u) [Ring R] : Type (max w u) :=
  PresentedGroup (steinbergRels ι R)

namespace SteinbergGroup

variable {ι : Type w} {R : Type u} [Ring R]

/-- The root generator `xᵢⱼ(a)` of `SteinbergGroup ι R` for distinct indices `i ≠ j` and `a ∈ R`.
-/
def of {i j : ι} (hij : i ≠ j) (a : R) : SteinbergGroup ι R :=
  PresentedGroup.of ((⟨(i, j), hij⟩ : {p : ι × ι // p.1 ≠ p.2}), a)

/-- Additivity of root generators: `xᵢⱼ(a) xᵢⱼ(b) = xᵢⱼ(a + b)`. -/
@[simp]
theorem of_mul_of {i j : ι} (hij : i ≠ j) (a b : R) :
    of hij a * of hij b = of hij (a + b) := by
  let p : {p : ι × ι // p.1 ≠ p.2} := ⟨(i, j), hij⟩
  have hr : FreeGroup.of (p, a) * FreeGroup.of (p, b) * (FreeGroup.of (p, a + b))⁻¹ ∈
      steinbergRels ι R :=
    Or.inl ⟨p, a, b, rfl⟩
  have h := PresentedGroup.mk_eq_mk_of_mul_inv_mem hr
  simpa only [map_mul, PresentedGroup.of, of, p] using h

/-- The root generator with parameter zero is the identity. -/
@[simp]
theorem of_zero {i j : ι} (hij : i ≠ j) : of hij (0 : R) = 1 :=
  mul_left_cancel (a := of hij (0 : R)) (by rw [of_mul_of, add_zero, mul_one])

/-- The inverse of a root generator negates its parameter. -/
@[simp]
theorem of_inv {i j : ι} (hij : i ≠ j) (a : R) : (of hij a)⁻¹ = of hij (-a) :=
  inv_eq_of_mul_eq_one_right (by rw [of_mul_of, add_neg_cancel, of_zero])

/-- The one-parameter root subgroup homomorphism `Multiplicative R →* SteinbergGroup ι R`
associated to a distinct index pair `i ≠ j`. -/
def ofHom {i j : ι} (hij : i ≠ j) : Multiplicative R →* SteinbergGroup ι R where
  toFun a := of hij a.toAdd
  map_one' := of_zero hij
  map_mul' a b := (of_mul_of hij a.toAdd b.toAdd).symm

/-- Evaluating `ofHom` yields the corresponding root generator. -/
@[simp]
theorem ofHom_apply {i j : ι} (hij : i ≠ j) (a : Multiplicative R) :
    ofHom hij a = of hij a.toAdd :=
  (rfl)

/-- Distant root generators commute: `xᵢⱼ(a)` commutes with `xₖₗ(b)` when `j ≠ k` and `i ≠ l`. -/
theorem commute_of {i j k l : ι} (hij : i ≠ j) (hkl : k ≠ l) (hjk : j ≠ k) (hil : i ≠ l)
    (a b : R) : Commute (of hij a) (of hkl b) := by
  let p : {p : ι × ι // p.1 ≠ p.2} := ⟨(i, j), hij⟩
  let q : {p : ι × ι // p.1 ≠ p.2} := ⟨(k, l), hkl⟩
  have hr : ⁅FreeGroup.of (p, a), FreeGroup.of (q, b)⁆ ∈ steinbergRels ι R :=
    Or.inr (Or.inl ⟨p, q, a, b, hjk, hil, rfl⟩)
  have h := PresentedGroup.one_of_mem hr
  rw [map_commutatorElement] at h
  exact commutatorElement_eq_one_iff_commute.mp h

/-- The forward chaining commutator relation: `⁅xᵢⱼ(a), xⱼₖ(b)⁆ = xᵢₖ(a * b)`. -/
theorem commutatorElement_of {i j k : ι} (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k) (a b : R) :
    ⁅of hij a, of hjk b⁆ = of hik (a * b) := by
  have hr : ⁅FreeGroup.of ((⟨(i, j), hij⟩ : {p : ι × ι // p.1 ≠ p.2}), a),
      FreeGroup.of ((⟨(j, k), hjk⟩ : {p : ι × ι // p.1 ≠ p.2}), b)⁆ *
      (FreeGroup.of ((⟨(i, k), hik⟩ : {p : ι × ι // p.1 ≠ p.2}), a * b))⁻¹ ∈
      steinbergRels ι R :=
    Or.inr (Or.inr ⟨i, j, k, hij, hjk, hik, a, b, rfl⟩)
  have h := PresentedGroup.mk_eq_mk_of_mul_inv_mem hr
  simpa only [map_commutatorElement, PresentedGroup.of, of] using h

/-- The reverse chaining commutator relation: `⁅xᵢⱼ(a), xₖᵢ(b)⁆ = xₖⱼ(-(b * a))`, obtained from
the forward relation by inverting the commutator. -/
theorem commutatorElement_of_reverse {i j k : ι} (hij : i ≠ j) (hki : k ≠ i) (hkj : k ≠ j)
    (a b : R) : ⁅of hij a, of hki b⁆ = of hkj (-(b * a)) := by
  calc
    ⁅of hij a, of hki b⁆ = ⁅of hki b, of hij a⁆⁻¹ := (commutatorElement_inv _ _).symm
    _ = (of hkj (b * a))⁻¹ := by rw [commutatorElement_of hki hij hkj]
    _ = of hkj (-(b * a)) := of_inv hkj (b * a)

/-- Conjugating `xⱼₖ(b)` by `xᵢⱼ(a)` multiplies it on the left by `xᵢₖ(a * b)`. -/
theorem conj_of_right {i j k : ι} (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k) (a b : R) :
    of hij a * of hjk b * (of hij a)⁻¹ = of hik (a * b) * of hjk b := by
  rw [← MulAut.conj_apply, conj_eq_commutatorElement_mul, commutatorElement_of hij hjk hik]

/-- Conjugating `xₖᵢ(b)` by `xᵢⱼ(a)` multiplies it on the left by `xₖⱼ(-(b * a))`. -/
theorem conj_of_left {i j k : ι} (hij : i ≠ j) (hki : k ≠ i) (hkj : k ≠ j) (a b : R) :
    of hij a * of hki b * (of hij a)⁻¹ = of hkj (-(b * a)) * of hki b := by
  rw [← MulAut.conj_apply, conj_eq_commutatorElement_mul, commutatorElement_of_reverse hij hki hkj]

/-! ## Universal property and induction -/

/-- **Universal property of the Steinberg group**: any assignment `(i ≠ j, a) ↦ f hij a` into a
group `G` satisfying the three Steinberg relations extends uniquely to a homomorphism
`SteinbergGroup ι R →* G`. -/
def lift {G : Type*} [Group G] (f : ∀ {i j : ι}, i ≠ j → R → G)
    (hadd : ∀ {i j : ι} (hij : i ≠ j) (a b : R), f hij a * f hij b = f hij (a + b))
    (hcomm : ∀ {i j k l : ι} (hij : i ≠ j) (hkl : k ≠ l),
      j ≠ k → i ≠ l → ∀ a b : R, Commute (f hij a) (f hkl b))
    (hrel : ∀ {i j k : ι} (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k) (a b : R),
      ⁅f hij a, f hjk b⁆ = f hik (a * b)) :
    SteinbergGroup ι R →* G :=
  PresentedGroup.toGroup (f := fun x => f x.1.2 x.2) <| by
    rintro r (⟨p, a, b, rfl⟩ | ⟨p, q, a, b, hjk, hil, rfl⟩ | ⟨i, j, k, hij, hjk, hik, a, b, rfl⟩)
    · simp only [map_mul, map_inv, FreeGroup.lift_apply_of, hadd, mul_inv_cancel]
    · simp only [map_commutatorElement, FreeGroup.lift_apply_of]
      exact commutatorElement_eq_one_iff_commute.mpr (hcomm p.2 q.2 hjk hil a b)
    · simp only [map_mul, map_inv, map_commutatorElement, FreeGroup.lift_apply_of]
      rw [hrel hij hjk hik, mul_inv_cancel]

/-- The lifted homomorphism agrees with `f` on every root generator. -/
@[simp]
theorem lift_of {G : Type*} [Group G] (f : ∀ {i j : ι}, i ≠ j → R → G)
    (hadd : ∀ {i j : ι} (hij : i ≠ j) (a b : R), f hij a * f hij b = f hij (a + b))
    (hcomm : ∀ {i j k l : ι} (hij : i ≠ j) (hkl : k ≠ l),
      j ≠ k → i ≠ l → ∀ a b : R, Commute (f hij a) (f hkl b))
    (hrel : ∀ {i j k : ι} (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k) (a b : R),
      ⁅f hij a, f hjk b⁆ = f hik (a * b))
    {i j : ι} (hij : i ≠ j) (a : R) :
    lift f hadd hcomm hrel (of hij a) = f hij a :=
  PresentedGroup.toGroup.of _

/-- Two homomorphisms out of `SteinbergGroup ι R` agree when they agree on every root generator. -/
@[ext]
theorem hom_ext {G : Type*} [Group G] {f g : SteinbergGroup ι R →* G}
    (h : ∀ {i j : ι} (hij : i ≠ j) (a : R), f (of hij a) = g (of hij a)) : f = g :=
  PresentedGroup.ext fun ⟨⟨⟨_, _⟩, hij⟩, a⟩ => h hij a

/-- Induction on `SteinbergGroup ι R`: every element is a finite product of root generators
(since `(of hij a)⁻¹ = of hij (-a)`, no inverse case is needed). -/
@[elab_as_elim]
theorem induction {motive : SteinbergGroup ι R → Prop} (one : motive 1)
    (of : ∀ {i j : ι} (hij : i ≠ j) (a : R), motive (of hij a))
    (mul : ∀ x y, motive x → motive y → motive (x * y)) (x : SteinbergGroup ι R) : motive x := by
  refine QuotientGroup.induction_on x fun w => ?_
  induction w using FreeGroup.induction_on with
  | one => exact one
  | of a => exact of a.1.2 a.2
  | inv_of a =>
    have hinv : (QuotientGroup.mk (FreeGroup.of a) : SteinbergGroup ι R)⁻¹ =
        SteinbergGroup.of a.1.2 (-a.2) := of_inv a.1.2 a.2
    rw [QuotientGroup.mk_inv, hinv]
    exact of a.1.2 (-a.2)
  | mul u v ihu ihv => exact mul _ _ ihu ihv

/-! ## Triviality and perfectness -/

/-- Over a subsingleton ring, `SteinbergGroup ι R` is trivial. -/
instance [Subsingleton R] : Subsingleton (SteinbergGroup ι R) := by
  refine subsingleton_iff.mpr fun x y => ?_
  have h1 : ∀ z : SteinbergGroup ι R, z = 1 := fun z => by
    induction z using SteinbergGroup.induction with
    | one => rfl
    | of hij a => rw [Subsingleton.elim a 0, of_zero]
    | mul a b ha hb => rw [ha, hb, mul_one]
  rw [h1 x, h1 y]

/-- Over a subsingleton index type, `SteinbergGroup ι R` has no generators and is trivial. -/
instance [Subsingleton ι] : Subsingleton (SteinbergGroup ι R) := by
  refine subsingleton_iff.mpr fun x y => ?_
  have h1 : ∀ z : SteinbergGroup ι R, z = 1 := fun z => by
    induction z using SteinbergGroup.induction with
    | one => rfl
    | of hij _ => exact absurd (Subsingleton.elim _ _) hij
    | mul a b ha hb => rw [ha, hb, mul_one]
  rw [h1 x, h1 y]

/-- `SteinbergGroup ι R` is perfect whenever every pair of distinct indices admits a third index:
each generator `xᵢⱼ(a)` equals `⁅xᵢₖ(a), xₖⱼ(1)⁆`. -/
theorem isPerfect (hι : ∀ i j : ι, i ≠ j → ∃ k : ι, k ≠ i ∧ k ≠ j) :
    Group.IsPerfect (SteinbergGroup ι R) := by
  rw [Group.isPerfect_def, eq_top_iff]
  have hmem : ∀ x : SteinbergGroup ι R, x ∈ commutator (SteinbergGroup ι R) := fun x => by
    induction x using SteinbergGroup.induction with
    | one => exact one_mem _
    | of hij a =>
      obtain ⟨k, hki, hkj⟩ := hι _ _ hij
      have h : of hij a = ⁅of hki.symm a, of hkj 1⁆ := by
        rw [commutatorElement_of hki.symm hkj hij, mul_one]
      rw [h]
      exact Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)
    | mul _ _ hx hy => exact mul_mem hx hy
  exact fun x _ => hmem x

/-- If `ι` has at least three elements, every pair of distinct indices admits a third index, so
`SteinbergGroup ι R` is perfect. -/
theorem isPerfect_of_three_le_enatCard (hι : 3 ≤ ENat.card ι) :
    Group.IsPerfect (SteinbergGroup ι R) :=
  isPerfect fun i j _ => ENat.exists_ne_ne_of_three_le hι i j

/-- The stable Steinberg group `SteinbergGroup ℕ R` is perfect. -/
instance : Group.IsPerfect (SteinbergGroup ℕ R) :=
  isPerfect_of_three_le_enatCard (by simp)

/-! ## Functoriality in rings and index sets -/

section Map

variable {S T : Type*} [Ring S] [Ring T]

/-- The homomorphism `SteinbergGroup ι R →* SteinbergGroup ι S` induced by a ring homomorphism
`f : R →+* S`, applying `f` to generator parameters. -/
def map (f : R →+* S) : SteinbergGroup ι R →* SteinbergGroup ι S :=
  lift (fun hij a => of hij (f a))
    (fun hij a b => by rw [of_mul_of, map_add])
    (fun hij hkl hjk hil a b => commute_of hij hkl hjk hil (f a) (f b))
    (fun hij hjk hik a b => by rw [commutatorElement_of, map_mul])

/-- `map f` applies `f` to the parameter of a root generator. -/
@[simp]
theorem map_of (f : R →+* S) {i j : ι} (hij : i ≠ j) (a : R) :
    map f (of hij a) = of hij (f a) :=
  FreeGroup.lift_apply_of

/-- The identity ring homomorphism induces the identity on `SteinbergGroup ι R`. -/
@[simp]
theorem map_id : map (ι := ι) (RingHom.id R) = MonoidHom.id (SteinbergGroup ι R) := by
  ext i j hij a
  simp

/-- Functoriality of `SteinbergGroup` with respect to ring homomorphisms. -/
theorem map_comp (f : R →+* S) (g : S →+* T) :
    map (ι := ι) (g.comp f) = (map g).comp (map f) := by
  ext i j hij a
  simp

/-- Applying `map f` and then `map g` is applying `map (g.comp f)`. -/
@[simp]
theorem map_map (f : R →+* S) (g : S →+* T) (x : SteinbergGroup ι R) :
    map g (map f x) = map (g.comp f) x := by
  rw [map_comp, MonoidHom.comp_apply]

/-- A surjective ring homomorphism induces a surjective homomorphism of Steinberg groups. -/
theorem map_surjective {f : R →+* S} (hf : Function.Surjective f) :
    Function.Surjective (map (ι := ι) f) := by
  intro y
  induction y using SteinbergGroup.induction with
  | one => exact ⟨1, map_one _⟩
  | of hij b =>
    obtain ⟨a, rfl⟩ := hf b
    exact ⟨of hij a, map_of f hij a⟩
  | mul x y hx hy =>
    obtain ⟨a, rfl⟩ := hx
    obtain ⟨b, rfl⟩ := hy
    exact ⟨a * b, map_mul _ _ _⟩

end Map

section Reindex

variable {κ μ : Type*}

variable (R) in
/-- The homomorphism `SteinbergGroup ι R →* SteinbergGroup κ R` induced by an injective map of
index types `e : ι → κ`. -/
def reindex (e : ι → κ) (he : Function.Injective e) : SteinbergGroup ι R →* SteinbergGroup κ R :=
  lift (fun hij a => of (he.ne hij) a)
    (fun hij a b => of_mul_of (he.ne hij) a b)
    (fun hij hkl hjk hil a b => commute_of (he.ne hij) (he.ne hkl) (he.ne hjk) (he.ne hil) a b)
    (fun hij hjk hik a b => commutatorElement_of (he.ne hij) (he.ne hjk) (he.ne hik) a b)

/-- `reindex` relabels the indices of a root generator. -/
@[simp]
theorem reindex_of (e : ι → κ) (he : Function.Injective e) {i j : ι} (hij : i ≠ j) (a : R) :
    reindex R e he (of hij a) = of (he.ne hij) a :=
  FreeGroup.lift_apply_of

/-- Reindexing along the identity map is the identity homomorphism. -/
@[simp]
theorem reindex_id : reindex R (id : ι → ι) Function.injective_id = MonoidHom.id _ := by
  ext i j hij a
  simp

/-- Reindexing composes along injective maps of index types. -/
theorem reindex_comp (e₁ : ι → κ) (he₁ : Function.Injective e₁)
    (e₂ : κ → μ) (he₂ : Function.Injective e₂) :
    reindex R (e₂ ∘ e₁) (he₂.comp he₁) = (reindex R e₂ he₂).comp (reindex R e₁ he₁) := by
  ext i j hij a
  simp

/-- Applying two reindexings in sequence is reindexing along the composite map. -/
@[simp]
theorem reindex_reindex (e₁ : ι → κ) (he₁ : Function.Injective e₁)
    (e₂ : κ → μ) (he₂ : Function.Injective e₂) (x : SteinbergGroup ι R) :
    reindex R e₂ he₂ (reindex R e₁ he₁ x) = reindex R (e₂ ∘ e₁) (he₂.comp he₁) x := by
  rw [reindex_comp, MonoidHom.comp_apply]

/-- Reindexing commutes with coefficient ring homomorphisms. -/
theorem reindex_map {S : Type*} [Ring S] (e : ι → κ) (he : Function.Injective e)
    (f : R →+* S) (x : SteinbergGroup ι R) :
    reindex S e he (map f x) = map f (reindex R e he x) := by
  induction x using SteinbergGroup.induction with
  | one => simp
  | of hij a => simp
  | mul x y hx hy => simp [hx, hy]

variable (R) in
/-- A bijection of index types induces an isomorphism of Steinberg groups. -/
def congr (e : ι ≃ κ) : SteinbergGroup ι R ≃* SteinbergGroup κ R :=
  (reindex R e e.injective).toMulEquiv (reindex R e.symm e.symm.injective)
    (by ext i j hij a; simp)
    (by ext i j hij a; simp)

/-- `congr e` relabels root generators by `e`. -/
@[simp]
theorem congr_of (e : ι ≃ κ) {i j : ι} (hij : i ≠ j) (a : R) :
    congr R e (of hij a) = of (e.injective.ne hij) a :=
  reindex_of e e.injective hij a

/-- `(congr e).symm` relabels root generators by `e.symm`. -/
@[simp]
theorem congr_symm_of (e : ι ≃ κ) {i j : κ} (hij : i ≠ j) (a : R) :
    (congr R e).symm (of hij a) = of (e.symm.injective.ne hij) a :=
  reindex_of e.symm e.symm.injective hij a

end Reindex

/-! ## Stabilization of finite-rank Steinberg groups -/

section Stabilize

variable (R) in
/-- The stabilization homomorphism `St_m(R) →* St_n(R)` for `m ≤ n`, embedding `Fin m` into
`Fin n` via `Fin.castLE`. -/
def stabilize {m n : ℕ} (h : m ≤ n) : SteinbergGroup (Fin m) R →* SteinbergGroup (Fin n) R :=
  reindex R (Fin.castLE h) (Fin.castLE_injective h)

/-- Stabilization keeps the generator parameter and casts the indices along `Fin.castLE`. -/
@[simp]
theorem stabilize_of {m n : ℕ} (h : m ≤ n) {i j : Fin m} (hij : i ≠ j) (a : R) :
    stabilize R h (of hij a) = of ((Fin.castLE_injective h).ne hij) a :=
  reindex_of _ _ hij a

/-- Stabilization to the same rank is the identity. -/
@[simp]
theorem stabilize_refl (n : ℕ) :
    stabilize R (le_refl n) = MonoidHom.id (SteinbergGroup (Fin n) R) := by
  ext i j hij a
  simp

/-- Stabilizations compose. -/
@[simp]
theorem stabilize_stabilize {k m n : ℕ} (hkm : k ≤ m) (hmn : m ≤ n)
    (x : SteinbergGroup (Fin k) R) :
    stabilize R hmn (stabilize R hkm x) = stabilize R (hkm.trans hmn) x := by
  rw [stabilize, stabilize, reindex_reindex]
  rfl

/-- Stabilization commutes with ring homomorphisms. -/
theorem stabilize_map {S : Type*} [Ring S] {m n : ℕ} (h : m ≤ n) (f : R →+* S)
    (x : SteinbergGroup (Fin m) R) :
    stabilize S h (map f x) = map f (stabilize R h x) :=
  reindex_map _ _ f x

/-- The finite-rank Steinberg groups form a directed system along stabilization. -/
instance : DirectedSystem (fun n : ℕ => SteinbergGroup (Fin n) R) fun _ _ h => stabilize R h where
  map_self x := by simp
  map_map _ _ _ hij hjk x := stabilize_stabilize hij hjk x

end Stabilize

/-! ## Rank two as a free product -/

variable (R) in
/-- **Rank-two Steinberg group**: in rank two there are no triples of distinct indices and no
relations between the two opposite roots, so `SteinbergGroup (Fin 2) R` is the free product of two
copies of the additive group of `R`. -/
def finTwoEquivCoprod :
    SteinbergGroup (Fin 2) R ≃* Monoid.Coprod (Multiplicative R) (Multiplicative R) :=
  let toCoprod : SteinbergGroup (Fin 2) R →*
      Monoid.Coprod (Multiplicative R) (Multiplicative R) :=
    lift (fun {i _} _ a =>
        if i = 0 then Monoid.Coprod.inl (Multiplicative.ofAdd a)
        else Monoid.Coprod.inr (Multiplicative.ofAdd a))
      (fun _ a b => by
        split_ifs <;> simp [← map_mul, ← ofAdd_add])
      (fun {i j k l} _ _ hjk hil a b => by
        have hik : i = k := by omega
        subst hik
        split_ifs
        · exact (Commute.all _ _).map Monoid.Coprod.inl
        · exact (Commute.all _ _).map Monoid.Coprod.inr)
      (fun {i j k} hij hjk hik _ _ => by omega)
  let ofCoprod : Monoid.Coprod (Multiplicative R) (Multiplicative R) →*
      SteinbergGroup (Fin 2) R :=
    Monoid.Coprod.lift (ofHom (i := (0 : Fin 2)) (j := 1) (by decide))
      (ofHom (i := (1 : Fin 2)) (j := 0) (by decide))
  toCoprod.toMulEquiv ofCoprod
    (by
      ext i j hij a
      fin_cases i <;> fin_cases j <;> simp [toCoprod, ofCoprod] at hij ⊢)
    (Monoid.Coprod.hom_ext
      (by ext a; simp [toCoprod, ofCoprod])
      (by ext a; simp [toCoprod, ofCoprod]))

/-- `(finTwoEquivCoprod R).symm` maps the left free-product summand to the `(0, 1)` root
subgroup. -/
@[simp]
theorem finTwoEquivCoprod_symm_inl (a : R) :
    (finTwoEquivCoprod R).symm (Monoid.Coprod.inl (Multiplicative.ofAdd a)) =
      of (i := (0 : Fin 2)) (j := 1) (by decide) a := by
  simp [finTwoEquivCoprod]

/-- `(finTwoEquivCoprod R).symm` maps the right free-product summand to the `(1, 0)` root
subgroup. -/
@[simp]
theorem finTwoEquivCoprod_symm_inr (a : R) :
    (finTwoEquivCoprod R).symm (Monoid.Coprod.inr (Multiplicative.ofAdd a)) =
      of (i := (1 : Fin 2)) (j := 0) (by decide) a := by
  simp [finTwoEquivCoprod]

/-- `finTwoEquivCoprod R` maps the `(0, 1)` root generator to the left free-product summand. -/
@[simp]
theorem finTwoEquivCoprod_of_zero_one (a : R) :
    finTwoEquivCoprod R (of (i := (0 : Fin 2)) (j := 1) (by decide) a) =
      Monoid.Coprod.inl (Multiplicative.ofAdd a) := by
  rw [← finTwoEquivCoprod_symm_inl, MulEquiv.apply_symm_apply]

/-- `finTwoEquivCoprod R` maps the `(1, 0)` root generator to the right free-product summand. -/
@[simp]
theorem finTwoEquivCoprod_of_one_zero (a : R) :
    finTwoEquivCoprod R (of (i := (1 : Fin 2)) (j := 0) (by decide) a) =
      Monoid.Coprod.inr (Multiplicative.ofAdd a) := by
  rw [← finTwoEquivCoprod_symm_inr, MulEquiv.apply_symm_apply]

/-! ## Binary products -/

private theorem commute_of_prod_zero {S : Type*} [Ring S]
    (hι : ∀ i j : ι, i ≠ j → ∃ k : ι, k ≠ i ∧ k ≠ j)
    {i j k l : ι} (hij : i ≠ j) (hkl : k ≠ l) (r : R) (s : S) :
    Commute (of hij (r, (0 : S))) (of hkl ((0 : R), s)) := by
  by_cases hjk : j = k
  · subst hjk
    by_cases hil : i = l
    · subst hil
      obtain ⟨m, hmi, hmj⟩ := hι i j hij
      have hrepr : of hij (r, (0 : S)) =
          ⁅of hmi.symm (r, (0 : S)), of hmj ((1 : R), (0 : S))⁆ := by
        rw [commutatorElement_of hmi.symm hmj hij]
        simp
      have hc₁ : Commute (of hmi.symm (r, (0 : S))) (of hkl ((0 : R), s)) := by
        rw [← commutatorElement_eq_one_iff_commute,
          commutatorElement_of_reverse hmi.symm hkl hmj.symm]
        simp [← Prod.zero_eq_mk]
      have hc₂ : Commute (of hmj ((1 : R), (0 : S))) (of hkl ((0 : R), s)) := by
        rw [← commutatorElement_eq_one_iff_commute, commutatorElement_of hmj hkl hmi]
        simp [← Prod.zero_eq_mk]
      rw [hrepr, commutatorElement_def]
      exact ((hc₁.mul_left hc₂).mul_left hc₁.inv_left).mul_left hc₂.inv_left
    · rw [← commutatorElement_eq_one_iff_commute, commutatorElement_of hij hkl hil]
      simp [← Prod.zero_eq_mk]
  · by_cases hil : i = l
    · subst hil
      rw [← commutatorElement_eq_one_iff_commute,
        commutatorElement_of_reverse hij hkl (Ne.symm hjk)]
      simp [← Prod.zero_eq_mk]
    · exact commute_of hij hkl hjk hil _ _

/-- When every pair of distinct indices admits a third index, `SteinbergGroup ι` preserves binary
products of rings. -/
def prodEquiv {S : Type*} [Ring S] (hι : ∀ i j : ι, i ≠ j → ∃ k : ι, k ≠ i ∧ k ≠ j) :
    SteinbergGroup ι (R × S) ≃* SteinbergGroup ι R × SteinbergGroup ι S :=
  let fwd : SteinbergGroup ι (R × S) →* SteinbergGroup ι R × SteinbergGroup ι S :=
    (map (RingHom.fst R S)).prod (map (RingHom.snd R S))
  let inl : SteinbergGroup ι R →* SteinbergGroup ι (R × S) :=
    lift (fun hij r => of hij (r, (0 : S)))
      (fun hij r₁ r₂ => by simp)
      (fun hij hkl hjk hil r₁ r₂ => commute_of hij hkl hjk hil _ _)
      (fun hij hjk hik r₁ r₂ => by
        rw [commutatorElement_of hij hjk hik]
        simp only [Prod.mk_mul_mk, mul_zero])
  let inr : SteinbergGroup ι S →* SteinbergGroup ι (R × S) :=
    lift (fun hij s => of hij ((0 : R), s))
      (fun hij s₁ s₂ => by simp)
      (fun hij hkl hjk hil s₁ s₂ => commute_of hij hkl hjk hil _ _)
      (fun hij hjk hik s₁ s₂ => by
        rw [commutatorElement_of hij hjk hik]
        simp only [Prod.mk_mul_mk, zero_mul])
  have hcomm : ∀ (x : SteinbergGroup ι R) (y : SteinbergGroup ι S), Commute (inl x) (inr y) := by
    intro x y
    induction x using SteinbergGroup.induction with
    | one => simp
    | of hij r =>
      induction y using SteinbergGroup.induction with
      | one => simp
      | of hkl s => simpa [inl, inr] using commute_of_prod_zero hι hij hkl r s
      | mul y₁ y₂ hy₁ hy₂ =>
        rw [map_mul]
        exact hy₁.mul_right hy₂
    | mul x₁ x₂ hx₁ hx₂ =>
      rw [map_mul]
      exact hx₁.mul_left hx₂
  let bwd : SteinbergGroup ι R × SteinbergGroup ι S →* SteinbergGroup ι (R × S) :=
    inl.noncommCoprod inr hcomm
  fwd.toMulEquiv bwd
    (by
      ext i j hij p
      rcases p with ⟨r, s⟩
      simp [fwd, bwd, inl, inr])
    (by
      have hl : fwd.comp inl = MonoidHom.inl (SteinbergGroup ι R) (SteinbergGroup ι S) := by
        refine hom_ext fun hij r => ?_
        simp [fwd, inl]
      have hr : fwd.comp inr = MonoidHom.inr (SteinbergGroup ι R) (SteinbergGroup ι S) := by
        refine hom_ext fun hij s => ?_
        simp [fwd, inr]
      refine MonoidHom.ext fun ⟨x, y⟩ => ?_
      simp only [MonoidHom.comp_apply, MonoidHom.id_apply, bwd, MonoidHom.noncommCoprod_apply,
        map_mul]
      have hxl : fwd (inl x) = (x, 1) := DFunLike.congr_fun hl x
      have hyr : fwd (inr y) = (1, y) := DFunLike.congr_fun hr y
      rw [hxl, hyr, Prod.mk_mul_mk, mul_one, one_mul])

/-- `prodEquiv` applies the two projection homomorphisms `map fst` and `map snd`. -/
@[simp]
theorem prodEquiv_apply {S : Type*} [Ring S]
    (hι : ∀ i j : ι, i ≠ j → ∃ k : ι, k ≠ i ∧ k ≠ j) (x : SteinbergGroup ι (R × S)) :
    prodEquiv hι x = (map (RingHom.fst R S) x, map (RingHom.snd R S) x) :=
  (rfl)

/-! ## The canonical homomorphism to `GL ι R` -/

section ToGL

variable [Fintype ι] [DecidableEq ι]

variable (ι R) in
/-- The canonical homomorphism `St_ι(R) →* GL ι R` sending each root generator `xᵢⱼ(a)` to the
elementary matrix `eᵢⱼ(a) = 1 + a Eᵢⱼ`. -/
def toGL : SteinbergGroup ι R →* GL ι R :=
  lift (fun hij a => transvectionUnit hij a)
    (fun hij a b => (transvectionUnit_add hij a b).symm)
    (fun hij hkl hjk hil a b => commute_transvectionUnit hij hkl hjk hil.symm a b)
    (fun hij hjk hik a b => commutatorElement_transvectionUnit hij hjk hik a b)

/-- `toGL` sends each root generator to the corresponding transvection. -/
@[simp]
theorem toGL_of {i j : ι} (hij : i ≠ j) (a : R) :
    toGL ι R (of hij a) = transvectionUnit hij a :=
  FreeGroup.lift_apply_of

/-- The image of `toGL : St_ι(R) →* GL ι R` is the elementary subgroup `E_ι(R)`. -/
theorem range_toGL : (toGL ι R).range = elementarySubgroup ι R := by
  refine le_antisymm ?_ ?_
  · rintro _ ⟨x, rfl⟩
    induction x using SteinbergGroup.induction with
    | one =>
      rw [map_one]
      exact one_mem _
    | of hij a =>
      rw [toGL_of]
      exact transvectionUnit_mem_elementarySubgroup hij a
    | mul x y hx hy =>
      rw [map_mul]
      exact mul_mem hx hy
  · refine elementarySubgroup_le_iff.mpr fun i j hij a => ⟨of hij a, toGL_of hij a⟩

variable (ι R) in
/-- The canonical surjection `St_ι(R) →* E_ι(R)` obtained by corestricting `toGL` to the
elementary subgroup. -/
def toElementary : SteinbergGroup ι R →* elementarySubgroup ι R :=
  (toGL ι R).codRestrict (elementarySubgroup ι R) fun x =>
    range_toGL (ι := ι) (R := R) ▸ ⟨x, rfl⟩

/-- The underlying matrix of `toElementary x` is `toGL x`. -/
@[simp]
theorem coe_toElementary (x : SteinbergGroup ι R) :
    (toElementary ι R x : GL ι R) = toGL ι R x :=
  (rfl)

/-- `toElementary : St_ι(R) →* E_ι(R)` is surjective. -/
theorem toElementary_surjective : Function.Surjective (toElementary ι R) := by
  rintro ⟨g, hg⟩
  rw [← range_toGL] at hg
  obtain ⟨x, rfl⟩ := hg
  exact ⟨x, rfl⟩

/-- The kernel of `toElementary` equals the kernel of `toGL`. -/
theorem ker_toElementary : (toElementary ι R).ker = (toGL ι R).ker := by
  ext x
  simp [Subtype.ext_iff]

/-- `toGL` commutes with entrywise application of a ring homomorphism. -/
theorem toGL_map {S : Type*} [Ring S] (f : R →+* S) (x : SteinbergGroup ι R) :
    toGL ι S (map f x) = Units.map (f.mapMatrix (m := ι)).toMonoidHom (toGL ι R x) := by
  induction x using SteinbergGroup.induction with
  | one => simp
  | of hij a =>
    simp only [map_of, toGL_of]
    ext p q
    simp [coe_transvectionUnit_eq_one_add_single, Matrix.one_apply, single_apply]
  | mul x y hx hy => simp [hx, hy]

/-- `toGL` commutes with index bijections. -/
theorem toGL_congr {κ : Type*} [Fintype κ] [DecidableEq κ] (e : ι ≃ κ) (x : SteinbergGroup ι R) :
    toGL κ R (congr R e x) = e.reindexGL R (toGL ι R x) := by
  induction x using SteinbergGroup.induction with
  | one => simp
  | of hij a =>
    rw [congr_of, toGL_of, toGL_of, Equiv.reindexGL_transvectionUnit]
  | mul x y hx hy => simp [hx, hy]

end ToGL

end SteinbergGroup

end TauCeti
