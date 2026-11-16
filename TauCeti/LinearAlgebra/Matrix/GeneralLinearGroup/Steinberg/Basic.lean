/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.PresentedGroup
public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Stable

/-!
# Steinberg groups over a ring

For a possibly noncommutative ring `R` and an index type `n`, the **Steinberg group**
`SteinbergGroup n R` is the group presented by generators `xᵢⱼ(a)` indexed by pairs of distinct
elements `i ≠ j` of `n` and coefficients `a ∈ R`, subject to the Steinberg relations:

* additivity: `xᵢⱼ(a) xᵢⱼ(b) = xᵢⱼ(a + b)`;
* distant commutation: `⁅xᵢⱼ(a), xₖₗ(b)⁆ = 1` whenever `j ≠ k` and `l ≠ i`;
* Chevalley commutator relation: `⁅xᵢⱼ(a), xⱼₖ(b)⁆ = xᵢₖ(ab)` whenever `i`, `j`, `k` are
  distinct.

For `n = Fin m` this is the finite-rank Steinberg group `Stₘ(R)`, mapping onto the elementary
subgroup `Eₘ(R) ≤ GLₘ(R)` by sending `xᵢⱼ(a)` to the transvection `1 + a Eᵢⱼ`. For `n = ℕ`
this is the **stable Steinberg group** `St(R)`, canonically isomorphic to the direct limit of the
groups `Stₘ(R)` along the index inclusions `Fin m ↪ Fin k`, and mapping onto the stable
elementary subgroup `E_∞(R) ≤ GL_∞(R)` by sending `xᵢⱼ(a)` to the stabilized transvection
`eᵢⱼ(a)`.

Whenever every distinct pair of indices admits a third index distinct from both (in particular
for finite `n` with `3 ≤ card n` and for every infinite `n`, including `ℕ`), every generator is a
commutator `xᵢⱼ(a) = ⁅xᵢₖ(a), xₖⱼ(1)⁆`, so `SteinbergGroup n R` is perfect.

## Main definitions

* `TauCeti.steinbergRels`: the set of defining Steinberg relators in the free group on distinct
  index pairs times `R`.
* `TauCeti.SteinbergGroup`: the Steinberg group `PresentedGroup (steinbergRels n R)`.
* `TauCeti.SteinbergGroup.gen`: the generator `xᵢⱼ(a)` of `SteinbergGroup n R`.
* `TauCeti.SteinbergGroup.genHom`: the one-parameter subgroup `Multiplicative R →* St`.
* `TauCeti.SteinbergGroup.lift`: the universal property of `SteinbergGroup n R`.
* `TauCeti.SteinbergGroup.map`: the homomorphism induced by a ring homomorphism `R →+* S`.
* `TauCeti.SteinbergGroup.mapIndex`: the homomorphism induced by an injection of index types.
* `TauCeti.SteinbergGroup.reindex`: the isomorphism induced by an equivalence of index types.
* `TauCeti.SteinbergGroup.toGL`: the canonical homomorphism `St n R →* GL n R` for finite `n`.
* `TauCeti.SteinbergGroup.stabilize`: the stabilization map `St (Fin m) R →* St (Fin k) R`.
* `TauCeti.SteinbergGroup.directLimitEquiv`: `DirectLimit (St (Fin ·) R) ≃* St ℕ R`.
* `TauCeti.stableTransvection`: the elementary matrix `eᵢⱼ(a)` viewed in `GL_∞(R)`.
* `TauCeti.SteinbergGroup.toStableGL`: the canonical homomorphism `St ℕ R →* GL_∞(R)`.
* `TauCeti.SteinbergGroup.toElementarySubgroup`: the canonical surjection `St ℕ R →* E_∞(R)`.

## Main results

* `TauCeti.SteinbergGroup.gen_zero`, `TauCeti.SteinbergGroup.gen_add`,
  `TauCeti.SteinbergGroup.gen_inv`, `TauCeti.SteinbergGroup.commute_gen`,
  `TauCeti.SteinbergGroup.commutatorElement_gen`,
  `TauCeti.SteinbergGroup.commutatorElement_gen_reverse`: the Steinberg relations.
* `TauCeti.SteinbergGroup.isPerfect_of_exists_ne`, `TauCeti.SteinbergGroup.isPerfect_of_infinite`,
  `TauCeti.SteinbergGroup.isPerfect_of_three_le_card`: perfectness of Steinberg groups.
* `TauCeti.SteinbergGroup.range_toGL`, `TauCeti.SteinbergGroup.range_toStableGL`: the images of
  the canonical homomorphisms are the finite and stable elementary subgroups.
* `TauCeti.SteinbergGroup.exists_mapIndex_fin`: every element of `St ℕ R` comes from some
  finite stage `St (Fin m) R`.

## References

* J. Milnor, *Introduction to Algebraic K-Theory*, Annals of Mathematics Studies 72 (1971), §5.
* C. A. Weibel, *The K-book: An Introduction to Algebraic K-Theory*, Graduate Studies in
  Mathematics 145 (2013), Chapter III, §5, Definition 5.1.
-/

public section

open Matrix

open scoped commutatorElement

namespace TauCeti

/-! ## Presentation of Steinberg groups -/

/-- The defining Steinberg relators on generators `xᵢⱼ(a)` indexed by distinct pairs `i ≠ j` in
`n` and coefficients `a ∈ R`:
* additivity `xᵢⱼ(a) xᵢⱼ(b) xᵢⱼ(a + b)⁻¹`;
* distant commutation `⁅xᵢⱼ(a), xₖₗ(b)⁆` for `j ≠ k` and `l ≠ i`;
* Chevalley commutator `⁅xᵢⱼ(a), xⱼₖ(b)⁆ xᵢₖ(a * b)⁻¹` for distinct `i, j, k`. -/
def steinbergRels (n : Type*) (R : Type*) [Ring R] :
    Set (FreeGroup ({p : n × n // p.1 ≠ p.2} × R)) :=
  {r | (∃ (p : {p : n × n // p.1 ≠ p.2}) (a b : R),
          r = FreeGroup.of (p, a) * FreeGroup.of (p, b) * (FreeGroup.of (p, a + b))⁻¹) ∨
       (∃ (p q : {p : n × n // p.1 ≠ p.2}) (a b : R), p.1.2 ≠ q.1.1 ∧ q.1.2 ≠ p.1.1 ∧
          r = ⁅FreeGroup.of (p, a), FreeGroup.of (q, b)⁆) ∨
       (∃ (i j k : n) (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k) (a b : R),
          r = ⁅FreeGroup.of ((⟨(i, j), hij⟩ : {p : n × n // p.1 ≠ p.2}), a),
               FreeGroup.of ((⟨(j, k), hjk⟩ : {p : n × n // p.1 ≠ p.2}), b)⁆ *
            (FreeGroup.of ((⟨(i, k), hik⟩ : {p : n × n // p.1 ≠ p.2}), a * b))⁻¹)}

/-- The **Steinberg group** on an index type `n` over a ring `R`: the group presented by
generators `xᵢⱼ(a)` (`i ≠ j` in `n`, `a ∈ R`) and the Steinberg relations
`TauCeti.steinbergRels n R`. For `n = Fin m` this is `Stₘ(R)`; for `n = ℕ` this is the stable
Steinberg group `St(R)`. -/
abbrev SteinbergGroup (n : Type*) (R : Type*) [Ring R] : Type _ :=
  PresentedGroup (steinbergRels n R)

namespace SteinbergGroup

variable {n : Type*} {R : Type*} [Ring R]

/-! ## Generators and relations -/

/-- The Steinberg generator `xᵢⱼ(a)` for distinct indices `i ≠ j` and coefficient `a ∈ R`. -/
def gen {i j : n} (hij : i ≠ j) (a : R) : SteinbergGroup n R :=
  PresentedGroup.of (⟨(i, j), hij⟩, a)

/-- `gen hij a` is the presented-group generator `(⟨(i, j), hij⟩, a)`. -/
theorem gen_def {i j : n} (hij : i ≠ j) (a : R) :
    gen hij a = PresentedGroup.of (⟨(i, j), hij⟩, a) :=
  (rfl)

/-- Additivity of Steinberg generators: `xᵢⱼ(a + b) = xᵢⱼ(a) xᵢⱼ(b)`. -/
@[simp]
theorem gen_add {i j : n} (hij : i ≠ j) (a b : R) :
    gen hij (a + b) = gen hij a * gen hij b := by
  let p : {p : n × n // p.1 ≠ p.2} := ⟨(i, j), hij⟩
  have hrel : FreeGroup.of (p, a) * FreeGroup.of (p, b) * (FreeGroup.of (p, a + b))⁻¹ ∈
      steinbergRels n R :=
    Or.inl ⟨p, a, b, rfl⟩
  have h := PresentedGroup.mk_eq_mk_of_mul_inv_mem hrel
  simpa only [map_mul, gen_def, PresentedGroup.of] using h.symm

/-- The Steinberg generator of parameter zero is the identity: `xᵢⱼ(0) = 1`. -/
@[simp]
theorem gen_zero {i j : n} (hij : i ≠ j) : gen hij (0 : R) = 1 := by
  have h := gen_add hij (0 : R) 0
  rw [add_zero] at h
  exact mul_left_cancel (h.symm.trans (mul_one _).symm)

/-- The inverse of a Steinberg generator negates its parameter: `xᵢⱼ(a)⁻¹ = xᵢⱼ(-a)`. -/
@[simp]
theorem gen_inv {i j : n} (hij : i ≠ j) (a : R) : (gen hij a)⁻¹ = gen hij (-a) := by
  refine inv_eq_of_mul_eq_one_right ?_
  rw [← gen_add, add_neg_cancel, gen_zero]

/-- The one-parameter subgroup `a ↦ xᵢⱼ(a)` of `SteinbergGroup n R` attached to `i ≠ j`. -/
def genHom {i j : n} (hij : i ≠ j) : Multiplicative R →* SteinbergGroup n R where
  toFun a := gen hij (Multiplicative.toAdd a)
  map_one' := gen_zero hij
  map_mul' a b := gen_add hij (Multiplicative.toAdd a) (Multiplicative.toAdd b)

/-- Evaluation of the one-parameter subgroup homomorphism `genHom`. -/
@[simp]
theorem genHom_apply {i j : n} (hij : i ≠ j) (a : Multiplicative R) :
    genHom hij a = gen hij (Multiplicative.toAdd a) :=
  (rfl)

/-- Distant Steinberg generators commute: `xᵢⱼ(a)` and `xₖₗ(b)` commute whenever `j ≠ k` and
`l ≠ i`. -/
theorem commute_gen {i j p q : n} (hij : i ≠ j) (hpq : p ≠ q) (hjp : j ≠ p) (hqi : q ≠ i)
    (a b : R) : Commute (gen hij a) (gen hpq b) := by
  let u : {p : n × n // p.1 ≠ p.2} := ⟨(i, j), hij⟩
  let v : {p : n × n // p.1 ≠ p.2} := ⟨(p, q), hpq⟩
  have hrel : ⁅FreeGroup.of (u, a), FreeGroup.of (v, b)⁆ ∈ steinbergRels n R :=
    Or.inr (Or.inl ⟨u, v, a, b, hjp, hqi, rfl⟩)
  have h := PresentedGroup.one_of_mem hrel
  rw [map_commutatorElement] at h
  exact commutatorElement_eq_one_iff_commute.mp h

/-- The Chevalley commutator relation in `SteinbergGroup n R`: `⁅xᵢⱼ(a), xⱼₖ(b)⁆ = xᵢₖ(a * b)`
for distinct `i, j, k`. -/
theorem commutatorElement_gen {i j l : n} (hij : i ≠ j) (hjl : j ≠ l) (hil : i ≠ l) (a b : R) :
    ⁅gen hij a, gen hjl b⁆ = gen hil (a * b) := by
  let u : {p : n × n // p.1 ≠ p.2} := ⟨(i, j), hij⟩
  let v : {p : n × n // p.1 ≠ p.2} := ⟨(j, l), hjl⟩
  let w : {p : n × n // p.1 ≠ p.2} := ⟨(i, l), hil⟩
  have hrel : ⁅FreeGroup.of (u, a), FreeGroup.of (v, b)⁆ * (FreeGroup.of (w, a * b))⁻¹ ∈
      steinbergRels n R :=
    Or.inr (Or.inr ⟨i, j, l, hij, hjl, hil, a, b, rfl⟩)
  have h := PresentedGroup.mk_eq_mk_of_mul_inv_mem hrel
  simpa only [map_commutatorElement, gen_def, PresentedGroup.of] using h

/-- Reverse orientation of the Chevalley commutator relation: `⁅xᵢⱼ(a), xₗᵢ(b)⁆ = xₗⱼ(-(b * a))`
for distinct `i, j, l`. -/
theorem commutatorElement_gen_reverse {i j l : n} (hij : i ≠ j) (hli : l ≠ i) (hlj : l ≠ j)
    (a b : R) : ⁅gen hij a, gen hli b⁆ = gen hlj (-(b * a)) := by
  calc
    ⁅gen hij a, gen hli b⁆ = ⁅gen hli b, gen hij a⁆⁻¹ := (commutatorElement_inv _ _).symm
    _ = (gen hlj (b * a))⁻¹ := by rw [commutatorElement_gen hli hij hlj]
    _ = gen hlj (-(b * a)) := gen_inv hlj (b * a)

/-! ## Generation and universal property -/

variable (n R) in
/-- The Steinberg generators generate `SteinbergGroup n R`. -/
theorem closure_gen_eq_top :
    Subgroup.closure
        {x : SteinbergGroup n R | ∃ (i j : n) (hij : i ≠ j) (a : R), gen hij a = x} = ⊤ := by
  rw [← PresentedGroup.closure_range_of (steinbergRels n R)]
  congr 1
  ext x
  constructor
  · rintro ⟨i, j, hij, a, rfl⟩
    exact ⟨(⟨(i, j), hij⟩, a), rfl⟩
  · rintro ⟨⟨⟨⟨i, j⟩, hij⟩, a⟩, rfl⟩
    exact ⟨i, j, hij, a, rfl⟩

/-- Two homomorphisms out of `SteinbergGroup n R` agree when they agree on every generator
`xᵢⱼ(a)`. -/
@[ext]
theorem hom_ext {G : Type*} [Group G] {φ ψ : SteinbergGroup n R →* G}
    (h : ∀ {i j : n} (hij : i ≠ j) (a : R), φ (gen hij a) = ψ (gen hij a)) : φ = ψ :=
  PresentedGroup.ext fun ⟨⟨⟨_, _⟩, hij⟩, a⟩ ↦ h hij a

/-- **Universal property of `SteinbergGroup n R`**: a family of elements `f hij a : G` satisfying
additivity, distant commutation, and the Chevalley commutator relation extends uniquely to a
group homomorphism `SteinbergGroup n R →* G`. -/
def lift {G : Type*} [Group G] (f : ∀ {i j : n}, i ≠ j → R → G)
    (hadd : ∀ {i j : n} (hij : i ≠ j) (a b : R), f hij (a + b) = f hij a * f hij b)
    (hcomm : ∀ {i j p q : n} (hij : i ≠ j) (hpq : p ≠ q), j ≠ p → q ≠ i →
      ∀ a b : R, Commute (f hij a) (f hpq b))
    (hrel : ∀ {i j l : n} (hij : i ≠ j) (hjl : j ≠ l) (hil : i ≠ l) (a b : R),
      ⁅f hij a, f hjl b⁆ = f hil (a * b)) :
    SteinbergGroup n R →* G :=
  PresentedGroup.toGroup (f := fun x ↦ f x.1.2 x.2) <| by
    rintro r (⟨⟨⟨i, j⟩, hij⟩, a, b, rfl⟩ |
      ⟨⟨⟨i, j⟩, hij⟩, ⟨⟨p, q⟩, hpq⟩, a, b, hjp, hqi, rfl⟩ |
      ⟨i, j, l, hij, hjl, hil, a, b, rfl⟩)
    · simp only [map_mul, map_inv, FreeGroup.lift_apply_of, hadd, mul_inv_cancel]
    · simp only [map_commutatorElement, FreeGroup.lift_apply_of]
      exact (hcomm hij hpq hjp hqi a b).commutator_eq
    · simp only [map_mul, map_inv, map_commutatorElement, FreeGroup.lift_apply_of]
      rw [hrel hij hjl hil, mul_inv_cancel]

/-- The lifted homomorphism sends each Steinberg generator `xᵢⱼ(a)` to `f hij a`. -/
@[simp]
theorem lift_gen {G : Type*} [Group G] (f : ∀ {i j : n}, i ≠ j → R → G)
    (hadd : ∀ {i j : n} (hij : i ≠ j) (a b : R), f hij (a + b) = f hij a * f hij b)
    (hcomm : ∀ {i j p q : n} (hij : i ≠ j) (hpq : p ≠ q), j ≠ p → q ≠ i →
      ∀ a b : R, Commute (f hij a) (f hpq b))
    (hrel : ∀ {i j l : n} (hij : i ≠ j) (hjl : j ≠ l) (hil : i ≠ l) (a b : R),
      ⁅f hij a, f hjl b⁆ = f hil (a * b))
    {i j : n} (hij : i ≠ j) (a : R) :
    lift @f hadd hcomm hrel (gen hij a) = f hij a :=
  PresentedGroup.toGroup.of _

/-! ## Perfectness and degenerate cases -/

/-- **Perfectness of Steinberg groups**: whenever every distinct pair of indices admits a third
index distinct from both, `SteinbergGroup n R` is perfect, because each generator is the
commutator `xᵢⱼ(a) = ⁅xᵢₖ(a), xₖⱼ(1)⁆`. -/
theorem isPerfect_of_exists_ne (h : ∀ i j : n, i ≠ j → ∃ l : n, i ≠ l ∧ l ≠ j) :
    Group.IsPerfect (SteinbergGroup n R) := by
  rw [Group.isPerfect_def, eq_top_iff, ← closure_gen_eq_top n R, Subgroup.closure_le]
  rintro _ ⟨i, j, hij, a, rfl⟩
  obtain ⟨l, hil, hlj⟩ := h i j hij
  rw [← mul_one a, ← commutatorElement_gen hil hlj hij]
  exact Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)

/-- The Steinberg group on an infinite index type (in particular `SteinbergGroup ℕ R`) is
perfect. -/
instance isPerfect_of_infinite [Infinite n] : Group.IsPerfect (SteinbergGroup n R) :=
  isPerfect_of_exists_ne fun i j _ ↦ by
    classical
    obtain ⟨l, hl⟩ := Infinite.exists_notMem_finset ({i, j} : Finset n)
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hl
    exact ⟨l, Ne.symm hl.1, hl.2⟩

/-- For a finite index type of cardinality at least three, `SteinbergGroup n R` is perfect. -/
theorem isPerfect_of_three_le_card [Fintype n] (hn : 3 ≤ Fintype.card n) :
    Group.IsPerfect (SteinbergGroup n R) :=
  isPerfect_of_exists_ne fun i j _ ↦ by
    classical
    obtain ⟨l, -, hl⟩ := Finset.exists_mem_notMem_of_card_lt_card (s := {i, j})
      (t := Finset.univ) (Finset.card_le_two.trans_lt (by rw [Finset.card_univ]; omega))
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hl
    exact ⟨l, Ne.symm hl.1, hl.2⟩

/-- Over a subsingleton (zero) ring, every Steinberg group is trivial. -/
instance subsingleton_of_subsingleton [Subsingleton R] : Subsingleton (SteinbergGroup n R) := by
  refine subsingleton_iff.mpr fun x y ↦ ?_
  have h1 : ∀ z : SteinbergGroup n R, z = 1 := fun z ↦ by
    have hz : z ∈ (⊥ : Subgroup (SteinbergGroup n R)) := by
      have htop : (⊤ : Subgroup (SteinbergGroup n R)) ≤ ⊥ := by
        rw [← closure_gen_eq_top n R, Subgroup.closure_le]
        rintro _ ⟨i, j, hij, a, rfl⟩
        rw [Subsingleton.elim a 0, gen_zero]
        exact Subgroup.one_mem _
      exact htop (Subgroup.mem_top z)
    exact Subgroup.mem_bot.mp hz
  rw [h1 x, h1 y]

/-! ## Functoriality in ring homomorphisms and index maps -/

section Functoriality

variable {m k : Type*} {S T : Type*} [Ring S] [Ring T]

/-- The homomorphism `SteinbergGroup n R →* SteinbergGroup n S` induced by a ring homomorphism
`f : R →+* S`, applying `f` to generator coefficients. -/
def map (f : R →+* S) : SteinbergGroup n R →* SteinbergGroup n S :=
  lift (fun hij a ↦ gen hij (f a))
    (fun hij a b ↦ by rw [map_add, gen_add])
    (fun hij hpq hjp hqi a b ↦ commute_gen hij hpq hjp hqi (f a) (f b))
    (fun hij hjl hil a b ↦ by rw [map_mul, commutatorElement_gen hij hjl hil])

/-- `map f` applies `f` to the parameter of each Steinberg generator. -/
@[simp]
theorem map_gen (f : R →+* S) {i j : n} (hij : i ≠ j) (a : R) :
    map f (gen hij a) = gen hij (f a) := by
  simp [map, lift, gen]

/-- The identity ring homomorphism induces the identity of `SteinbergGroup n R`. -/
@[simp]
theorem map_id : map (n := n) (RingHom.id R) = MonoidHom.id (SteinbergGroup n R) := by
  ext i j hij a
  simp

/-- `SteinbergGroup n` is functorial in ring homomorphisms. -/
theorem map_comp (f : R →+* S) (g : S →+* T) :
    map (n := n) (g.comp f) = (map g).comp (map f) := by
  ext i j hij a
  simp

/-- Applying `map f` followed by `map g` equals `map (g.comp f)`. -/
@[simp]
theorem map_map (f : R →+* S) (g : S →+* T) (x : SteinbergGroup n R) :
    map g (map f x) = map (g.comp f) x := by
  rw [map_comp, MonoidHom.comp_apply]

/-- A surjective ring homomorphism induces a surjective homomorphism of Steinberg groups. -/
theorem map_surjective {f : R →+* S} (hf : Function.Surjective f) :
    Function.Surjective (map (n := n) f) := by
  rw [← MonoidHom.range_eq_top, eq_top_iff, ← closure_gen_eq_top n S, Subgroup.closure_le]
  rintro _ ⟨i, j, hij, b, rfl⟩
  obtain ⟨a, rfl⟩ := hf b
  exact ⟨gen hij a, map_gen f hij a⟩

/-- The homomorphism `SteinbergGroup m R →* SteinbergGroup n R` induced by an injection of index
types `e : m ↪ n`, relabelling the indices of each generator. -/
def mapIndex (e : m ↪ n) : SteinbergGroup m R →* SteinbergGroup n R :=
  lift (fun hij a ↦ gen (e.injective.ne hij) a)
    (fun hij a b ↦ gen_add (e.injective.ne hij) a b)
    (fun hij hpq hjp hqi a b ↦
      commute_gen (e.injective.ne hij) (e.injective.ne hpq) (e.injective.ne hjp)
        (e.injective.ne hqi) a b)
    (fun hij hjl hil a b ↦
      commutatorElement_gen (e.injective.ne hij) (e.injective.ne hjl) (e.injective.ne hil) a b)

/-- `mapIndex e` relabels the indices of a Steinberg generator along `e`. -/
@[simp]
theorem mapIndex_gen (e : m ↪ n) {i j : m} (hij : i ≠ j) (a : R) :
    mapIndex e (gen hij a) = gen (e.injective.ne hij) a := by
  simp [mapIndex, lift, gen]

/-- The identity index embedding induces the identity of `SteinbergGroup n R`. -/
@[simp]
theorem mapIndex_refl :
    mapIndex (R := R) (Function.Embedding.refl n) = MonoidHom.id (SteinbergGroup n R) := by
  ext i j hij a
  simp

/-- `mapIndex` respects composition of embeddings. -/
theorem mapIndex_trans (e₁ : m ↪ n) (e₂ : n ↪ k) :
    mapIndex (R := R) (e₁.trans e₂) = (mapIndex e₂).comp (mapIndex e₁) := by
  ext i j hij a
  simp

/-- Applying `mapIndex e₁` followed by `mapIndex e₂` equals `mapIndex (e₁.trans e₂)`. -/
@[simp]
theorem mapIndex_mapIndex (e₁ : m ↪ n) (e₂ : n ↪ k) (x : SteinbergGroup m R) :
    mapIndex e₂ (mapIndex e₁ x) = mapIndex (e₁.trans e₂) x := by
  rw [mapIndex_trans, MonoidHom.comp_apply]

/-- Ring homomorphisms commute with index embeddings on Steinberg groups. -/
theorem map_comp_mapIndex (f : R →+* S) (e : m ↪ n) :
    (map f).comp (mapIndex e) = (mapIndex e).comp (map f) := by
  ext i j hij a
  simp

/-- The isomorphism `SteinbergGroup m R ≃* SteinbergGroup n R` induced by a bijection of index
types `e : m ≃ n`. -/
def reindex (e : m ≃ n) : SteinbergGroup m R ≃* SteinbergGroup n R :=
  (mapIndex e.toEmbedding).toMulEquiv (mapIndex e.symm.toEmbedding)
    (by
      rw [← mapIndex_trans]
      convert mapIndex_refl
      ext i
      simp)
    (by
      rw [← mapIndex_trans]
      convert mapIndex_refl
      ext i
      simp)

/-- `reindex e` relabels the indices of each Steinberg generator along `e`. -/
@[simp]
theorem reindex_gen (e : m ≃ n) {i j : m} (hij : i ≠ j) (a : R) :
    reindex e (gen hij a) = gen (e.injective.ne hij) a :=
  mapIndex_gen e.toEmbedding hij a

/-- `(reindex e).symm` relabels the indices of each Steinberg generator along `e.symm`. -/
@[simp]
theorem reindex_symm_gen (e : m ≃ n) {i j : n} (hij : i ≠ j) (a : R) :
    (reindex e).symm (gen hij a) = gen (e.symm.injective.ne hij) a :=
  mapIndex_gen e.symm.toEmbedding hij a

/-! ## Canonical homomorphism to `GL n R` -/

section Finite

variable [Fintype n] [DecidableEq n]

variable (n R) in
/-- The canonical homomorphism `SteinbergGroup n R →* GL n R`, sending each Steinberg generator
`xᵢⱼ(a)` to the transvection `1 + a Eᵢⱼ`. -/
def toGL : SteinbergGroup n R →* GL n R :=
  lift (fun hij a ↦ transvectionUnit hij a)
    (fun hij a b ↦ transvectionUnit_add hij a b)
    (fun hij hpq hjp hqi a b ↦ commute_transvectionUnit hij hpq hjp hqi a b)
    (fun hij hjl hil a b ↦ commutatorElement_transvectionUnit hij hjl hil a b)

/-- `toGL` sends the Steinberg generator `xᵢⱼ(a)` to the transvection `transvectionUnit hij a`. -/
@[simp]
theorem toGL_gen {i j : n} (hij : i ≠ j) (a : R) :
    toGL n R (gen hij a) = transvectionUnit hij a := by
  simp [toGL]

/-- The image of `toGL : SteinbergGroup n R →* GL n R` is the elementary subgroup `E n R`. -/
@[simp]
theorem range_toGL : (toGL n R).range = elementarySubgroup n R := by
  refine le_antisymm ?_ ?_
  · rw [MonoidHom.range_eq_map, ← closure_gen_eq_top n R, MonoidHom.map_closure,
      Subgroup.closure_le]
    rintro _ ⟨_, ⟨i, j, hij, a, rfl⟩, rfl⟩
    rw [toGL_gen]
    exact transvectionUnit_mem_elementarySubgroup hij a
  · rw [elementarySubgroup_le_iff]
    exact fun _ _ hij a ↦ ⟨gen hij a, toGL_gen hij a⟩

/-- `toGL` is natural in ring homomorphisms. -/
theorem toGL_map (f : R →+* S) (x : SteinbergGroup n R) :
    toGL n S (map f x) = Units.map (f.mapMatrix (m := n)).toMonoidHom (toGL n R x) := by
  suffices (toGL n S).comp (map f) =
      (Units.map (f.mapMatrix (m := n)).toMonoidHom).comp (toGL n R) from
    DFunLike.congr_fun this x
  ext i j hij a
  simp

/-- `toGL` is equivariant for reindexing along an equivalence of finite index types. -/
theorem toGL_reindex [Fintype m] [DecidableEq m] (e : m ≃ n) (x : SteinbergGroup m R) :
    toGL n R (reindex e x) = e.reindexGL R (toGL m R x) := by
  suffices (toGL n R).comp (reindex e).toMonoidHom =
      (e.reindexGL R).toMonoidHom.comp (toGL m R) from
    DFunLike.congr_fun this x
  ext i j hij a
  simp [Equiv.reindexGL_transvectionUnit]

end Finite

end Functoriality

/-! ## Stabilization and the direct limit `St_∞(R)` -/

variable (R) in
/-- The stabilization homomorphism `St (Fin m) R →* St (Fin k) R` for `m ≤ k`, induced by the
canonical inclusion `Fin.castLEEmb h : Fin m ↪ Fin k`. -/
def stabilize {m k : ℕ} (h : m ≤ k) : SteinbergGroup (Fin m) R →* SteinbergGroup (Fin k) R :=
  mapIndex (Fin.castLEEmb h)

/-- Stabilization sends `xᵢⱼ(a)` to the generator at the cast indices. -/
@[simp]
theorem stabilize_gen {m k : ℕ} (h : m ≤ k) {i j : Fin m} (hij : i ≠ j) (a : R) :
    stabilize R h (gen hij a) = gen ((Fin.castLE_injective h).ne hij) a :=
  mapIndex_gen (Fin.castLEEmb h) hij a

/-- Stabilization to the same size is the identity. -/
@[simp]
theorem stabilize_refl (m : ℕ) :
    stabilize R (le_refl m) = MonoidHom.id (SteinbergGroup (Fin m) R) := by
  ext i j hij a
  simp

/-- Stabilizations of Steinberg groups compose. -/
@[simp]
theorem stabilize_stabilize {m k l : ℕ} (hmk : m ≤ k) (hkl : k ≤ l)
    (x : SteinbergGroup (Fin m) R) :
    stabilize R hkl (stabilize R hmk x) = stabilize R (hmk.trans hkl) x := by
  suffices (stabilize R hkl).comp (stabilize R hmk) = stabilize R (hmk.trans hkl) from
    DFunLike.congr_fun this x
  ext i j hij a
  simp

/-- The finite-rank Steinberg groups `St (Fin m) R` form a directed system along stabilization. -/
instance : DirectedSystem (fun m : ℕ ↦ SteinbergGroup (Fin m) R) (fun _ _ h ↦ stabilize R h) where
  map_self x := by simp
  map_map _ _ _ hij hjk x := stabilize_stabilize hij hjk x

/-- Stabilization of Steinberg groups commutes with stabilization of general linear groups along
`toGL`. -/
theorem toGL_stabilize {m k : ℕ} (h : m ≤ k) (x : SteinbergGroup (Fin m) R) :
    toGL (Fin k) R (stabilize R h x) = stabilizeGL R h (toGL (Fin m) R x) := by
  suffices (toGL (Fin k) R).comp (stabilize R h) = (stabilizeGL R h).comp (toGL (Fin m) R) from
    DFunLike.congr_fun this x
  ext i j hij a
  simp [stabilizeGL_transvectionUnit]

/-- Mapping from `St (Fin m) R` to `St ℕ R` is compatible with stabilization `stabilize R h`. -/
@[simp]
theorem mapIndex_valEmbedding_stabilize {m k : ℕ} (h : m ≤ k) (x : SteinbergGroup (Fin m) R) :
    mapIndex Fin.valEmbedding (stabilize R h x) = mapIndex Fin.valEmbedding x := by
  suffices (mapIndex (R := R) Fin.valEmbedding).comp (stabilize R h) =
      mapIndex (R := R) Fin.valEmbedding from
    DFunLike.congr_fun this x
  ext i j hij a
  simp

/-- Auxiliary map from `St ℕ R` to `DirectLimit (St (Fin ·) R)` sending each generator `xᵢⱼ(a)`
into stage `max i j + 1`. -/
private noncomputable def toDirectLimit (R : Type*) [Ring R] :
    SteinbergGroup ℕ R →*
      DirectLimit (fun m : ℕ ↦ SteinbergGroup (Fin m) R) (fun _ _ h ↦ stabilize R h) := by
  let ofLim := DirectLimit.Monoid.of (fun m : ℕ ↦ SteinbergGroup (Fin m) R)
    (fun _ _ h ↦ stabilize R h)
  let f : ∀ {i j : ℕ}, i ≠ j → R →
      DirectLimit (fun m : ℕ ↦ SteinbergGroup (Fin m) R) (fun _ _ h ↦ stabilize R h) :=
    fun {i j} hij a ↦
      ofLim (max i j + 1)
        (gen (i := ⟨i, by omega⟩) (j := ⟨j, by omega⟩) (by simpa [Fin.ext_iff] using hij) a)
  have hf_eq : ∀ {i j m : ℕ} (hij : i ≠ j) (hi : i < m) (hj : j < m) (a : R),
      f hij a =
        ofLim m (gen (i := ⟨i, hi⟩) (j := ⟨j, hj⟩) (by simpa [Fin.ext_iff] using hij) a) := by
    intro i j m hij hi hj a
    have hm : max i j + 1 ≤ m := by omega
    dsimp only [f, ofLim]
    rw [← DirectLimit.Monoid.of_f (f := fun _ _ h ↦ stabilize R h) hm, stabilize_gen]
  refine lift f ?_ ?_ ?_
  · intro i j hij a b
    simp only [f, ← map_mul, gen_add]
  · intro i j p q hij hpq hjp hqi a b
    let N := max (max i j) (max p q) + 1
    rw [hf_eq hij (by omega : i < N) (by omega : j < N),
      hf_eq hpq (by omega : p < N) (by omega : q < N)]
    exact (commute_gen _ _ (by simpa [Fin.ext_iff] using hjp) (by simpa [Fin.ext_iff] using hqi)
      a b).map (ofLim N)
  · intro i j l hij hjl hil a b
    let N := max (max i j) l + 1
    rw [hf_eq hij (by omega : i < N) (by omega : j < N),
      hf_eq hjl (by omega : j < N) (by omega : l < N),
      hf_eq hil (by omega : i < N) (by omega : l < N), ← map_commutatorElement]
    exact congrArg (ofLim N) (commutatorElement_gen _ _ _ a b)

private theorem toDirectLimit_gen {i j : ℕ} (hij : i ≠ j) (a : R) :
    toDirectLimit R (gen hij a) =
      DirectLimit.Monoid.of _ (fun _ _ h ↦ stabilize R h) (max i j + 1)
        (gen (i := ⟨i, by omega⟩) (j := ⟨j, by omega⟩) (by simpa [Fin.ext_iff] using hij) a) := by
  simp [toDirectLimit, lift, gen]

variable (R) in
/-- **Colimit presentation of the stable Steinberg group**: the direct limit of the finite-rank
Steinberg groups `St (Fin m) R` along stabilization is canonically isomorphic to
`SteinbergGroup ℕ R`. -/
noncomputable def directLimitEquiv :
    DirectLimit (fun m : ℕ ↦ SteinbergGroup (Fin m) R) (fun _ _ h ↦ stabilize R h) ≃*
      SteinbergGroup ℕ R :=
  MonoidHom.toMulEquiv
    (DirectLimit.Monoid.lift _ (fun _ _ h ↦ stabilize R h)
      (fun _ ↦ mapIndex Fin.valEmbedding) fun _ _ h x ↦ mapIndex_valEmbedding_stabilize h x)
    (toDirectLimit R)
    (by
      refine DirectLimit.Monoid.hom_ext fun m ↦ ?_
      ext i j hij a
      have hm : max i.1 j.1 + 1 ≤ m := by omega
      simp only [MonoidHom.comp_apply, MonoidHom.id_apply, DirectLimit.Monoid.lift_of,
        mapIndex_gen, toDirectLimit_gen, Fin.valEmbedding_apply]
      rw [← DirectLimit.Monoid.of_f (f := fun _ _ h ↦ stabilize R h) hm, stabilize_gen])
    (by
      ext i j hij a
      simp only [MonoidHom.comp_apply, MonoidHom.id_apply, toDirectLimit_gen,
        DirectLimit.Monoid.lift_of, mapIndex_gen]
      rfl)

/-- `directLimitEquiv` sends a quotient representative `⟦⟨m, x⟩⟧` to `mapIndex Fin.valEmbedding x`.
-/
@[simp]
theorem directLimitEquiv_mk (m : ℕ) (x : SteinbergGroup (Fin m) R) :
    directLimitEquiv R ⟦⟨m, x⟩⟧ = mapIndex Fin.valEmbedding x :=
  DirectLimit.Monoid.lift_mk ..

/-- `directLimitEquiv` sends an element of stage `m` to its image under `mapIndex Fin.valEmbedding`.
-/
theorem directLimitEquiv_of (m : ℕ) (x : SteinbergGroup (Fin m) R) :
    directLimitEquiv R (DirectLimit.Monoid.of _ (fun _ _ h ↦ stabilize R h) m x) =
      mapIndex Fin.valEmbedding x :=
  DirectLimit.Monoid.lift_of ..

/-- `(directLimitEquiv R).symm` sends the generator `xᵢⱼ(a)` into stage `max i j + 1`. -/
@[simp]
theorem directLimitEquiv_symm_gen {i j : ℕ} (hij : i ≠ j) (a : R) :
    (directLimitEquiv R).symm (gen hij a) =
      DirectLimit.Monoid.of _ (fun _ _ h ↦ stabilize R h) (max i j + 1)
        (gen (i := ⟨i, by omega⟩) (j := ⟨j, by omega⟩) (by simpa [Fin.ext_iff] using hij) a) :=
  toDirectLimit_gen hij a

/-- Every element of the stable Steinberg group `SteinbergGroup ℕ R` comes from a finite stage
`SteinbergGroup (Fin m) R`. -/
theorem exists_mapIndex_fin (x : SteinbergGroup ℕ R) :
    ∃ (m : ℕ) (y : SteinbergGroup (Fin m) R), mapIndex Fin.valEmbedding y = x := by
  obtain ⟨m, y, hy⟩ :=
    DirectLimit.exists_eq_mk (fun _ _ h ↦ stabilize R h) ((directLimitEquiv R).symm x)
  refine ⟨m, y, ?_⟩
  rw [← directLimitEquiv_mk, ← hy, MulEquiv.apply_symm_apply]

end SteinbergGroup

/-! ## Stable transvections and `St ℕ R →* GL_∞(R)` -/

section StableTransvection

variable {R S : Type*} [Ring R] [Ring S]

/-- The elementary matrix `eᵢⱼ(a) = 1 + a Eᵢⱼ` viewed as an element of `GL_∞(R)`: the
transvection formed at size `max i j + 1` and mapped into `StableGeneralLinearGroup R`. -/
noncomputable def stableTransvection {i j : ℕ} (hij : i ≠ j) (a : R) :
    StableGeneralLinearGroup R :=
  StableGeneralLinearGroup.of R (max i j + 1)
    (transvectionUnit (i := ⟨i, by omega⟩) (j := ⟨j, by omega⟩)
      (by simpa [Fin.ext_iff] using hij) a)

/-- `stableTransvection hij a` is represented by the transvection at `(i, j)` in any matrix size
`m` strictly greater than `i` and `j`. -/
theorem stableTransvection_eq_of {i j m : ℕ} (hij : i ≠ j) (hi : i < m) (hj : j < m) (a : R) :
    stableTransvection hij a =
      StableGeneralLinearGroup.of R m
        (transvectionUnit (i := ⟨i, hi⟩) (j := ⟨j, hj⟩) (by simpa [Fin.ext_iff] using hij) a) := by
  have hm : max i j + 1 ≤ m := by omega
  rw [stableTransvection, ← StableGeneralLinearGroup.of_stabilizeGL hm,
    stabilizeGL_transvectionUnit]

/-- The stable transvection of parameter zero is the identity. -/
@[simp]
theorem stableTransvection_zero {i j : ℕ} (hij : i ≠ j) :
    stableTransvection hij (0 : R) = 1 := by
  simp [stableTransvection]

/-- Stable transvections at the same pair of indices are additive in their parameter. -/
@[simp]
theorem stableTransvection_add {i j : ℕ} (hij : i ≠ j) (a b : R) :
    stableTransvection hij (a + b) = stableTransvection hij a * stableTransvection hij b := by
  simp [stableTransvection, ← map_mul]

/-- The inverse of a stable transvection negates its parameter. -/
@[simp]
theorem stableTransvection_inv {i j : ℕ} (hij : i ≠ j) (a : R) :
    (stableTransvection hij a)⁻¹ = stableTransvection hij (-a) := by
  simp [stableTransvection, ← map_inv]

/-- Distant stable transvections commute: `eᵢⱼ(a)` and `e_{p,q}(b)` commute whenever `j ≠ p` and
`q ≠ i`. -/
theorem commute_stableTransvection {i j p q : ℕ} (hij : i ≠ j) (hpq : p ≠ q) (hjp : j ≠ p)
    (hqi : q ≠ i) (a b : R) :
    Commute (stableTransvection hij a) (stableTransvection hpq b) := by
  let N := max (max i j) (max p q) + 1
  rw [stableTransvection_eq_of hij (by omega : i < N) (by omega : j < N),
    stableTransvection_eq_of hpq (by omega : p < N) (by omega : q < N)]
  exact (commute_transvectionUnit _ _ (by simpa [Fin.ext_iff] using hjp)
    (by simpa [Fin.ext_iff] using hqi) a b).map (StableGeneralLinearGroup.of R N)

/-- The Chevalley commutator relation for stable transvections:
`⁅eᵢⱼ(a), eⱼₗ(b)⁆ = eᵢₗ(a * b)` for distinct `i, j, l`. -/
theorem commutatorElement_stableTransvection {i j l : ℕ} (hij : i ≠ j) (hjl : j ≠ l) (hil : i ≠ l)
    (a b : R) :
    ⁅stableTransvection hij a, stableTransvection hjl b⁆ = stableTransvection hil (a * b) := by
  let N := max (max i j) l + 1
  rw [stableTransvection_eq_of hij (by omega : i < N) (by omega : j < N),
    stableTransvection_eq_of hjl (by omega : j < N) (by omega : l < N),
    stableTransvection_eq_of hil (by omega : i < N) (by omega : l < N), ← map_commutatorElement]
  exact congrArg (StableGeneralLinearGroup.of R N) (commutatorElement_transvectionUnit _ _ _ a b)

/-- Every stable transvection lies in the stable elementary subgroup `E_∞(R)`. -/
theorem stableTransvection_mem_elementarySubgroup {i j : ℕ} (hij : i ≠ j) (a : R) :
    stableTransvection hij a ∈ StableGeneralLinearGroup.elementarySubgroup R :=
  StableGeneralLinearGroup.of_mem_elementarySubgroup (transvectionUnit_mem_elementarySubgroup _ _)

/-- A ring homomorphism applies to the coefficient of a stable transvection. -/
@[simp]
theorem StableGeneralLinearGroup.map_stableTransvection (f : R →+* S) {i j : ℕ} (hij : i ≠ j)
    (a : R) :
    StableGeneralLinearGroup.map f (stableTransvection hij a) = stableTransvection hij (f a) := by
  simp [stableTransvection]

namespace SteinbergGroup

variable (R) in
/-- The canonical homomorphism `φ : St(R) →* GL_∞(R)` sending each Steinberg generator `xᵢⱼ(a)`
to the stable transvection `eᵢⱼ(a)`. -/
noncomputable def toStableGL : SteinbergGroup ℕ R →* StableGeneralLinearGroup R :=
  lift (fun hij a ↦ stableTransvection hij a)
    (fun hij a b ↦ stableTransvection_add hij a b)
    (fun hij hpq hjp hqi a b ↦ commute_stableTransvection hij hpq hjp hqi a b)
    (fun hij hjl hil a b ↦ commutatorElement_stableTransvection hij hjl hil a b)

/-- `toStableGL` sends the generator `xᵢⱼ(a)` to the stable transvection `eᵢⱼ(a)`. -/
@[simp]
theorem toStableGL_gen {i j : ℕ} (hij : i ≠ j) (a : R) :
    toStableGL R (gen hij a) = stableTransvection hij a := by
  simp [toStableGL]

/-- On elements coming from a finite stage `St (Fin m) R`, `toStableGL` agrees with `toGL`
followed by `StableGeneralLinearGroup.of`. -/
@[simp]
theorem toStableGL_mapIndex_fin (m : ℕ) (x : SteinbergGroup (Fin m) R) :
    toStableGL R (mapIndex Fin.valEmbedding x) =
      StableGeneralLinearGroup.of R m (toGL (Fin m) R x) := by
  suffices (toStableGL R).comp (mapIndex Fin.valEmbedding) =
      (StableGeneralLinearGroup.of R m).comp (toGL (Fin m) R) from
    DFunLike.congr_fun this x
  ext i j hij a
  simp only [MonoidHom.comp_apply, mapIndex_gen, toStableGL_gen, toGL_gen]
  exact stableTransvection_eq_of (Fin.val_ne_of_ne hij) i.2 j.2 a

/-- The image of `toStableGL : St(R) →* GL_∞(R)` is the stable elementary subgroup `E_∞(R)`. -/
@[simp]
theorem range_toStableGL :
    (toStableGL R).range = StableGeneralLinearGroup.elementarySubgroup R := by
  refine le_antisymm ?_ ?_
  · rw [MonoidHom.range_eq_map, ← closure_gen_eq_top ℕ R, MonoidHom.map_closure,
      Subgroup.closure_le]
    rintro _ ⟨_, ⟨i, j, hij, a, rfl⟩, rfl⟩
    rw [toStableGL_gen]
    exact stableTransvection_mem_elementarySubgroup hij a
  · intro x hx
    obtain ⟨m, u, hu, rfl⟩ := StableGeneralLinearGroup.mem_elementarySubgroup_iff.1 hx
    rw [← range_toGL] at hu
    obtain ⟨y, rfl⟩ := hu
    exact ⟨mapIndex Fin.valEmbedding y, toStableGL_mapIndex_fin m y⟩

/-- `toStableGL` is natural in ring homomorphisms. -/
theorem toStableGL_map (f : R →+* S) (x : SteinbergGroup ℕ R) :
    toStableGL S (map f x) = StableGeneralLinearGroup.map f (toStableGL R x) := by
  suffices (toStableGL S).comp (map f) = (StableGeneralLinearGroup.map f).comp (toStableGL R) from
    DFunLike.congr_fun this x
  ext i j hij a
  simp

variable (R) in
/-- The canonical surjection `St(R) →* E_∞(R)` obtained by restricting the codomain of
`toStableGL R` to the stable elementary subgroup. -/
noncomputable def toElementarySubgroup :
    SteinbergGroup ℕ R →* StableGeneralLinearGroup.elementarySubgroup R :=
  (toStableGL R).codRestrict (StableGeneralLinearGroup.elementarySubgroup R) fun x ↦
    range_toStableGL (R := R) ▸ ⟨x, rfl⟩

/-- The underlying element of `GL_∞(R)` of `toElementarySubgroup R x` is `toStableGL R x`. -/
@[simp]
theorem coe_toElementarySubgroup (x : SteinbergGroup ℕ R) :
    (toElementarySubgroup R x : StableGeneralLinearGroup R) = toStableGL R x :=
  (rfl)

/-- `toElementarySubgroup R : St(R) →* E_∞(R)` is surjective. -/
theorem toElementarySubgroup_surjective : Function.Surjective (toElementarySubgroup R) := by
  rintro ⟨x, hx⟩
  rw [← range_toStableGL] at hx
  obtain ⟨y, rfl⟩ := hx
  exact ⟨y, rfl⟩

/-- The kernel of `toElementarySubgroup R : St(R) →* E_∞(R)` coincides with the kernel of
`toStableGL R : St(R) →* GL_∞(R)`. -/
@[simp]
theorem ker_toElementarySubgroup : (toElementarySubgroup R).ker = (toStableGL R).ker := by
  ext x
  simp [MonoidHom.mem_ker, Subtype.ext_iff]

end SteinbergGroup

end StableTransvection

end TauCeti
