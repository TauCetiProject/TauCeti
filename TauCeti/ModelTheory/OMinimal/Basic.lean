/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Logic.Equiv.Fin.Basic
public import Mathlib.MeasureTheory.SetAlgebra
public import Mathlib.Order.WithBot

/-!
# O-minimal structures

An *o-minimal structure* on a linearly ordered type `R` singles out, for every `n`, a family of
*definable* subsets of `Rⁿ = Fin n → R`: each family is an algebra of sets, the families are
closed under cylinders and under forgetting the coordinate `0`, they contain the diagonals and the
strict order, and the definable subsets of `R¹` are exactly the finite unions of points and open
intervals. These are the tame sets of o-minimal geometry: cell decomposition, dimension theory and
definable choice are developed on top of them, and the semialgebraic sets over a real closed field
are the basic example.

Coordinate `0` is the fibre coordinate of a cylinder: the point of `Rⁿ⁺¹` at height `t` over
`x : Rⁿ` is `Fin.cons t x`, and `Fin.tail` forgets the height. Products, graphs and fibres over a
first factor are read in `Fin.append` coordinates.

## Main definitions

* `TauCeti.OMinimalStructure R`: an o-minimal structure on `R`.
* `TauCeti.OMinimalStructure.DefinableMapOn`: a map `Rᵐ → Rᵏ` is definable on `A` when its graph
  over `A`, read in `Fin.append` coordinates, is definable.

## Main results

* `TauCeti.OMinimalStructure.Definable.preimage_comp`,
  `TauCeti.OMinimalStructure.Definable.image_comp`: definable sets are closed under preimages and
  images by every coordinate map `x ↦ x ∘ ι`, for `ι : Fin m → Fin n`. These maps include the
  permutations of coordinates, the coordinate projections and the diagonal embeddings.
* `TauCeti.OMinimalStructure.Definable.image_appendEquiv_prod`: products of definable sets are
  definable.
* `TauCeti.OMinimalStructure.Definable.preimage_append`: the fibre `{y | Fin.append x y ∈ A}` of a
  definable set over a point `x` is definable.
* `TauCeti.OMinimalStructure.definable_singleton`, `TauCeti.OMinimalStructure.definable_of_finite`:
  points, hence finite sets, are definable, so definability allows parameters from `R`.
* `TauCeti.OMinimalStructure.DefinableMapOn.definable_image`,
  `TauCeti.OMinimalStructure.DefinableMapOn.definable_inter_preimage`,
  `TauCeti.OMinimalStructure.DefinableMapOn.comp`: images and preimages of definable sets under
  definable maps are definable, and definable maps compose.

## Implementation notes

The definable sets are stored as the field `Definable'` and read through the definition
`TauCeti.OMinimalStructure.Definable`, so that dot notation such as `hs.inter ht` works on proofs
of definability. The other fields are restated as theorems about `Definable`.

## References

L. van den Dries, *Tame Topology and o-minimal Structures*, London Mathematical Society Lecture
Note Series 248, Cambridge University Press, 1998, Chapter 1, §§2–3.
-/

public section

open Set

namespace TauCeti

/-- An **o-minimal structure** on a linearly ordered type `R` (van den Dries, *Tame Topology and
o-minimal Structures*, Chapter 1, §§2–3). For each `n` it singles out the definable subsets of
`Fin n → R`; coordinate `0` is the fibre coordinate of a cylinder. The one-variable condition makes
every point definable, so definability is definability with parameters from `R`. -/
structure OMinimalStructure (R : Type*) [LinearOrder R] where
  /-- The definable subsets of `Fin n → R`. Use `TauCeti.OMinimalStructure.Definable` instead. -/
  Definable' : (n : ℕ) → Set (Fin n → R) → Prop
  /-- The definable subsets of each `Fin n → R` form an algebra of sets. -/
  isSetAlgebra' (n : ℕ) : MeasureTheory.IsSetAlgebra {s | Definable' n s}
  /-- The cylinder `R × A`, with the new coordinate `0`, over a definable `A` is definable. -/
  definable_setOf_tail_mem' {n : ℕ} {s : Set (Fin n → R)} :
    Definable' n s → Definable' (n + 1) {x | Fin.tail x ∈ s}
  /-- The cylinder `A × R`, with the new last coordinate, over a definable `A` is definable. -/
  definable_setOf_init_mem' {n : ℕ} {s : Set (Fin n → R)} :
    Definable' n s → Definable' (n + 1) {x | Fin.init x ∈ s}
  /-- Every diagonal is definable. -/
  definable_setOf_eq' (n : ℕ) (i j : Fin n) : Definable' n {x | x i = x j}
  /-- The strict order is definable. -/
  definable_setOf_lt' : Definable' 2 {x | x 0 < x 1}
  /-- Forgetting coordinate `0` maps definable sets to definable sets. -/
  definable_image_tail' {n : ℕ} {s : Set (Fin (n + 1) → R)} :
    Definable' (n + 1) s → Definable' n (Fin.tail '' s)
  /-- The definable subsets of `Fin 1 → R` are exactly the finite unions of points and open
  intervals with endpoints in `R ∪ {−∞}` and `R ∪ {+∞}`. -/
  definable_one_iff' {s : Set (Fin 1 → R)} :
    Definable' 1 s ↔ ∃ (F : Finset R) (J : Finset (WithBot R × WithTop R)),
      s = {x | x 0 ∈ F ∨ ∃ p ∈ J, p.1 < (x 0 : WithBot R) ∧ (x 0 : WithTop R) < p.2}

namespace OMinimalStructure

variable {R : Type*} [LinearOrder R] (S : OMinimalStructure R) {m n k : ℕ}

/-- A subset of `Fin n → R` is **definable** in the o-minimal structure `S`. -/
def Definable (n : ℕ) (s : Set (Fin n → R)) : Prop :=
  S.Definable' n s

/-- Definability in `S` is the field `Definable'` of `S`; use this to build or unfold a concrete
o-minimal structure. -/
theorem definable_def {s : Set (Fin n → R)} : S.Definable n s ↔ S.Definable' n s :=
  Iff.rfl

/-- Two o-minimal structures with the same definable sets are equal. -/
@[ext]
theorem ext {S T : OMinimalStructure R} (h : ∀ n s, S.Definable n s ↔ T.Definable n s) :
    S = T := by
  cases S
  cases T
  congr
  funext n s
  exact propext (h n s)

/-! ### The axioms -/

/-- The definable subsets of each `Fin n → R` form an algebra of sets. -/
theorem isSetAlgebra (n : ℕ) : MeasureTheory.IsSetAlgebra {s | S.Definable n s} :=
  S.isSetAlgebra' n

variable {S} in
/-- The cylinder `R × A`, with the new coordinate `0`, over a definable `A` is definable. -/
theorem Definable.setOf_tail_mem {s : Set (Fin n → R)} (hs : S.Definable n s) :
    S.Definable (n + 1) {x | Fin.tail x ∈ s} :=
  S.definable_setOf_tail_mem' hs

variable {S} in
/-- The cylinder `A × R`, with the new last coordinate, over a definable `A` is definable. -/
theorem Definable.setOf_init_mem {s : Set (Fin n → R)} (hs : S.Definable n s) :
    S.Definable (n + 1) {x | Fin.init x ∈ s} :=
  S.definable_setOf_init_mem' hs

/-- Every diagonal is definable. -/
@[simp]
theorem definable_setOf_eq (n : ℕ) (i j : Fin n) : S.Definable n {x | x i = x j} :=
  S.definable_setOf_eq' n i j

variable {S} in
/-- Forgetting coordinate `0` maps definable sets to definable sets. -/
theorem Definable.image_tail {s : Set (Fin (n + 1) → R)} (hs : S.Definable (n + 1) s) :
    S.Definable n (Fin.tail '' s) :=
  S.definable_image_tail' hs

/-- The definable subsets of `Fin 1 → R` are exactly the finite unions of points and open
intervals with endpoints in `R ∪ {−∞}` and `R ∪ {+∞}`. -/
theorem definable_one_iff {s : Set (Fin 1 → R)} :
    S.Definable 1 s ↔ ∃ (F : Finset R) (J : Finset (WithBot R × WithTop R)),
      s = {x | x 0 ∈ F ∨ ∃ p ∈ J, p.1 < (x 0 : WithBot R) ∧ (x 0 : WithTop R) < p.2} :=
  S.definable_one_iff'

/-! ### Boolean operations -/

section Boolean

variable {S} {s t : Set (Fin n → R)}

variable (S n) in
/-- The empty set is definable. -/
@[simp]
theorem definable_empty : S.Definable n ∅ :=
  (S.isSetAlgebra n).empty_mem

variable (S n) in
/-- The whole space is definable. -/
@[simp]
theorem definable_univ : S.Definable n univ :=
  (S.isSetAlgebra n).univ_mem

/-- The complement of a definable set is definable. -/
theorem Definable.compl (hs : S.Definable n s) : S.Definable n sᶜ :=
  (S.isSetAlgebra n).compl_mem hs

/-- A set whose complement is definable is definable. -/
theorem Definable.of_compl (hs : S.Definable n sᶜ) : S.Definable n s :=
  compl_compl s ▸ hs.compl

/-- The complement of a set is definable if and only if the set is. -/
@[simp]
theorem definable_compl_iff : S.Definable n sᶜ ↔ S.Definable n s :=
  ⟨.of_compl, .compl⟩

/-- The union of two definable sets is definable. -/
theorem Definable.union (hs : S.Definable n s) (ht : S.Definable n t) :
    S.Definable n (s ∪ t) :=
  (S.isSetAlgebra n).union_mem hs ht

/-- The intersection of two definable sets is definable. -/
theorem Definable.inter (hs : S.Definable n s) (ht : S.Definable n t) :
    S.Definable n (s ∩ t) :=
  (S.isSetAlgebra n).inter_mem hs ht

/-- The difference of two definable sets is definable. -/
theorem Definable.diff (hs : S.Definable n s) (ht : S.Definable n t) :
    S.Definable n (s \ t) :=
  (S.isSetAlgebra n).sdiff_mem hs ht

/-- A finite union of definable sets is definable. -/
theorem Definable.biUnion {ι : Type*} {I : Set ι} (hI : I.Finite) {s : ι → Set (Fin n → R)}
    (hs : ∀ i ∈ I, S.Definable n (s i)) : S.Definable n (⋃ i ∈ I, s i) := by
  simpa using (S.isSetAlgebra n).biUnion_mem hI.toFinset (by simpa using hs)

/-- A finite intersection of definable sets is definable. -/
theorem Definable.biInter {ι : Type*} {I : Set ι} (hI : I.Finite) {s : ι → Set (Fin n → R)}
    (hs : ∀ i ∈ I, S.Definable n (s i)) : S.Definable n (⋂ i ∈ I, s i) := by
  simpa using (S.isSetAlgebra n).biInter_mem hI.toFinset (by simpa using hs)

/-- A union of finitely many definable sets is definable. -/
theorem Definable.iUnion {ι : Type*} [Finite ι] {s : ι → Set (Fin n → R)}
    (hs : ∀ i, S.Definable n (s i)) : S.Definable n (⋃ i, s i) := by
  simpa using Definable.biUnion finite_univ fun i _ => hs i

/-- An intersection of finitely many definable sets is definable. -/
theorem Definable.iInter {ι : Type*} [Finite ι] {s : ι → Set (Fin n → R)}
    (hs : ∀ i, S.Definable n (s i)) : S.Definable n (⋂ i, s i) := by
  simpa using Definable.biInter finite_univ fun i _ => hs i

end Boolean

/-! ### Coordinate maps -/

section Coordinate

variable {S}

/-- Cylinders over the first `n` coordinates of `Fin N → R`, `n ≤ N`, are definable. -/
private theorem Definable.preimage_comp_castLE {s : Set (Fin n → R)} (hs : S.Definable n s) :
    ∀ {N : ℕ} (h : n ≤ N), S.Definable N ((· ∘ Fin.castLE h) ⁻¹' s) := by
  intro N h
  induction N, h using Nat.le_induction with
  | base => simpa [preimage] using hs
  | succ N hN ih =>
    have : ((· ∘ Fin.castLE (hN.trans N.le_succ)) ⁻¹' s : Set (Fin (N + 1) → R)) =
        {x : Fin (N + 1) → R | Fin.init x ∈ (· ∘ Fin.castLE hN) ⁻¹' s} := by
      ext x
      simp [Fin.init_def, Function.comp_def]
    exact this ▸ ih.setOf_init_mem

/-- Cylinders over the last `n` coordinates of `Fin (n + k) → R` are definable. -/
private theorem Definable.preimage_comp_addNat {s : Set (Fin n → R)} (hs : S.Definable n s) :
    ∀ k : ℕ, S.Definable (n + k) ((· ∘ (Fin.addNat · k)) ⁻¹' s)
  | 0 => hs
  | k + 1 => (hs.preimage_comp_addNat k).setOf_tail_mem

/-- Forgetting the first `k` coordinates of `Fin (n + k) → R` maps definable sets to definable
sets. -/
private theorem Definable.image_comp_addNat :
    ∀ {k : ℕ} {s : Set (Fin (n + k) → R)}, S.Definable (n + k) s →
      S.Definable n ((· ∘ (Fin.addNat · k)) '' s)
  | 0, s, hs => by simpa [Function.comp_def] using hs
  | k + 1, s, hs => by
    have : ((· ∘ (Fin.addNat · (k + 1))) '' s : Set (Fin n → R)) =
        (· ∘ (Fin.addNat · k)) '' (Fin.tail '' s) := by
      rw [image_image]
      exact image_congr fun x _ => funext fun i => congrArg x (Fin.ext (by simp; omega))
    exact this ▸ hs.image_tail.image_comp_addNat

omit [LinearOrder R] in
/-- A point of `Fin n → R` and a point of `Fin m → R` are the two blocks of a point of
`Fin (m + n) → R`: the first `n` coordinates and the last `m` coordinates. -/
private theorem exists_comp_castLE_eq_and_comp_addNat_eq (x : Fin n → R) (y : Fin m → R) :
    ∃ z : Fin (m + n) → R, z ∘ Fin.castLE (n.le_add_left m) = x ∧
      z ∘ (Fin.addNat · n) = y := by
  refine ⟨fun i => if h : (i : ℕ) < n then x ⟨i, h⟩ else y ⟨i - n, by omega⟩, ?_, ?_⟩
  · funext i
    simp
  · funext j
    simp

/-- The preimage of a definable set under a coordinate map `x ↦ x ∘ ι` is definable. -/
theorem Definable.preimage_comp {s : Set (Fin n → R)} (hs : S.Definable n s)
    (ι : Fin n → Fin m) : S.Definable m ((· ∘ ι) ⁻¹' s) := by
  have h : n ≤ m + n := n.le_add_left m
  have : ((· ∘ ι) ⁻¹' s : Set (Fin m → R)) = (· ∘ (Fin.addNat · n)) ''
      ((· ∘ Fin.castLE h) ⁻¹' s ∩ ⋂ i, {z | z (Fin.castLE h i) = z ((ι i).addNat n)}) := by
    ext y
    constructor
    · intro hy
      obtain ⟨z, hzx, hzy⟩ := exists_comp_castLE_eq_and_comp_addNat_eq (y ∘ ι) y
      refine ⟨z, ⟨by simpa [preimage, hzx] using hy, mem_iInter.2 fun i => ?_⟩, hzy⟩
      simpa using (congrFun hzx i).trans (congrFun hzy (ι i)).symm
    · rintro ⟨z, ⟨hz, hzι⟩, rfl⟩
      have : (z ∘ Fin.castLE h) = (z ∘ (Fin.addNat · n)) ∘ ι :=
        funext fun i => mem_iInter.1 hzι i
      simpa [preimage, this] using hz
  rw [this]
  exact ((hs.preimage_comp_castLE h).inter
    (Definable.iInter fun i => S.definable_setOf_eq _ _ _)).image_comp_addNat

/-- The image of a definable set under a coordinate map `x ↦ x ∘ ι` is definable. -/
theorem Definable.image_comp {s : Set (Fin n → R)} (hs : S.Definable n s)
    (ι : Fin m → Fin n) : S.Definable m ((· ∘ ι) '' s) := by
  have h : n ≤ m + n := n.le_add_left m
  have : ((· ∘ ι) '' s : Set (Fin m → R)) = (· ∘ (Fin.addNat · n)) ''
      ((· ∘ Fin.castLE h) ⁻¹' s ∩ ⋂ j, {z | z (j.addNat n) = z (Fin.castLE h (ι j))}) := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      obtain ⟨z, hzx, hzy⟩ := exists_comp_castLE_eq_and_comp_addNat_eq x (x ∘ ι)
      refine ⟨z, ⟨by simpa [preimage, hzx] using hx, mem_iInter.2 fun j => ?_⟩, hzy⟩
      simpa using (congrFun hzy j).trans (congrFun hzx (ι j)).symm
    · rintro ⟨z, ⟨hz, hzι⟩, rfl⟩
      exact ⟨_, hz, funext fun j => (mem_iInter.1 hzι j).symm⟩
  rw [this]
  exact ((hs.preimage_comp_castLE h).inter
    (Definable.iInter fun j => S.definable_setOf_eq _ _ _)).image_comp_addNat

/-- A set is definable if and only if its preimage under a permutation of coordinates is. -/
theorem definable_preimage_comp_equiv_iff {s : Set (Fin n → R)} (e : Fin n ≃ Fin m) :
    S.Definable m ((· ∘ e) ⁻¹' s) ↔ S.Definable n s := by
  refine ⟨fun hs => ?_, fun hs => hs.preimage_comp e⟩
  convert hs.preimage_comp e.symm using 1
  ext x
  simp [Function.comp_assoc]

/-- The product of definable sets, read in `Fin.append` coordinates, is definable. -/
theorem Definable.image_appendEquiv_prod {s : Set (Fin m → R)} {t : Set (Fin n → R)}
    (hs : S.Definable m s) (ht : S.Definable n t) :
    S.Definable (m + n) (Fin.appendEquiv m n '' s ×ˢ t) := by
  rw [Equiv.image_eq_preimage_symm]
  exact (hs.preimage_comp (Fin.castAdd n)).inter (ht.preimage_comp (Fin.natAdd m))

end Coordinate

/-! ### Points, order and fibres -/

section Points

variable {S}

variable (S) in
/-- The set where a coordinate takes a prescribed value is definable. -/
@[simp]
theorem definable_setOf_eq_const (i : Fin n) (c : R) : S.Definable n {x | x i = c} := by
  have h : S.Definable 1 {y | y 0 = c} := S.definable_one_iff.2 ⟨{c}, ∅, by ext; simp⟩
  simpa [preimage] using h.preimage_comp fun _ => i

variable (S) in
/-- The set where one coordinate is smaller than another is definable. -/
@[simp]
theorem definable_setOf_lt (i j : Fin n) : S.Definable n {x | x i < x j} := by
  have h : S.Definable 2 {x | x 0 < x 1} := S.definable_setOf_lt'
  simpa [preimage] using h.preimage_comp ![i, j]

variable (S) in
/-- The set where one coordinate is at most another is definable. -/
@[simp]
theorem definable_setOf_le (i j : Fin n) : S.Definable n {x | x i ≤ x j} := by
  simpa [le_iff_lt_or_eq, ofPred_or] using
    (S.definable_setOf_lt i j).union (S.definable_setOf_eq n i j)

variable (S) in
/-- A point is definable. -/
@[simp]
theorem definable_singleton (a : Fin n → R) : S.Definable n {a} := by
  have : ({a} : Set (Fin n → R)) = ⋂ i, {x | x i = a i} := by
    ext x
    simp [funext_iff]
  exact this ▸ Definable.iInter fun i => S.definable_setOf_eq_const i (a i)

variable (S) in
/-- A finite set is definable. -/
theorem definable_of_finite {s : Set (Fin n → R)} (hs : s.Finite) : S.Definable n s := by
  simpa using Definable.biUnion hs fun a _ => S.definable_singleton a

/-- The fibre `{y | Fin.append x y ∈ s}` of a definable set over a point `x` is definable. -/
theorem Definable.preimage_append {s : Set (Fin (m + n) → R)} (hs : S.Definable (m + n) s)
    (x : Fin m → R) : S.Definable n {y | Fin.append x y ∈ s} := by
  have : {y | Fin.append x y ∈ s} = (· ∘ Fin.natAdd m) '' (s ∩ (· ∘ Fin.castAdd n) ⁻¹' {x}) := by
    ext y
    constructor
    · intro hy
      exact ⟨_, ⟨hy, by simp [Function.comp_def]⟩, by simp [Function.comp_def]⟩
    · rintro ⟨z, ⟨hz, rfl : z ∘ Fin.castAdd n = x⟩, rfl⟩
      simpa [Function.comp_def, Fin.append_castAdd_natAdd] using hz
  exact this ▸ (hs.inter ((S.definable_singleton x).preimage_comp _)).image_comp _

end Points

/-! ### Definable maps -/

/-- A map `f : Rᵐ → Rᵏ` is **definable on** `A` when its graph `{Fin.append x (f x) | x ∈ A}` is a
definable subset of `Rᵐ⁺ᵏ`. -/
def DefinableMapOn (f : (Fin m → R) → Fin k → R) (A : Set (Fin m → R)) : Prop :=
  S.Definable (m + k) ((fun x => Fin.append x (f x)) '' A)

namespace DefinableMapOn

variable {S} {f g : (Fin m → R) → Fin k → R} {A B : Set (Fin m → R)}

/-- A map is definable on `A` exactly when its graph over `A` is definable. -/
theorem _root_.TauCeti.OMinimalStructure.definableMapOn_def :
    S.DefinableMapOn f A ↔ S.Definable (m + k) ((fun x => Fin.append x (f x)) '' A) :=
  Iff.rfl

/-- The graph of a map definable on `A` is definable. -/
theorem definable_graph (hf : S.DefinableMapOn f A) :
    S.Definable (m + k) ((fun x => Fin.append x (f x)) '' A) :=
  hf

/-- Maps that agree on `A` are definable on `A` together. -/
theorem congr (hf : S.DefinableMapOn f A) (hfg : EqOn f g A) : S.DefinableMapOn g A := by
  rw [definableMapOn_def, ← image_congr fun x hx => congrArg (Fin.append x) (hfg hx)]
  exact hf

/-- The domain of a definable map is definable. -/
theorem definable (hf : S.DefinableMapOn f A) : S.Definable m A := by
  convert hf.image_comp (Fin.castAdd k) using 1
  rw [image_image]
  simp [Function.comp_def]

/-- The image of the domain of a definable map is definable. -/
theorem definable_image (hf : S.DefinableMapOn f A) : S.Definable k (f '' A) := by
  convert hf.image_comp (Fin.natAdd m) using 1
  rw [image_image]
  simp [Function.comp_def]

/-- The preimage of a definable set under a definable map is definable. -/
theorem definable_inter_preimage (hf : S.DefinableMapOn f A) {B : Set (Fin k → R)}
    (hB : S.Definable k B) : S.Definable m (A ∩ f ⁻¹' B) := by
  convert (hf.inter (hB.preimage_comp (Fin.natAdd m))).image_comp (Fin.castAdd k) using 1
  ext x
  simp [Function.comp_def, and_comm]

/-- A map definable on `A` is definable on every definable subset of `A`. -/
theorem mono (hf : S.DefinableMapOn f A) (hB : S.Definable m B) (hBA : B ⊆ A) :
    S.DefinableMapOn f B := by
  rw [definableMapOn_def]
  convert hf.inter (hB.preimage_comp (Fin.castAdd k)) using 1
  ext z
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨⟨x, hBA hx, rfl⟩, by simpa [Function.comp_def] using hx⟩
  · rintro ⟨⟨x, -, rfl⟩, hx⟩
    exact ⟨x, by simpa [Function.comp_def] using hx, rfl⟩

end DefinableMapOn

section Maps

variable {S} {A : Set (Fin m → R)}

/-- Every map is definable on the empty set. -/
@[simp]
theorem definableMapOn_empty (f : (Fin m → R) → Fin k → R) : S.DefinableMapOn f ∅ := by
  simp [definableMapOn_def]

/-- A coordinate map `x ↦ x ∘ ι` is definable on every definable set. This includes the identity,
the coordinate projections and the diagonal embeddings. -/
theorem definableMapOn_comp (hA : S.Definable m A) (ι : Fin k → Fin m) :
    S.DefinableMapOn (· ∘ ι) A := by
  rw [definableMapOn_def]
  convert (hA.preimage_comp (Fin.castAdd k)).inter
    (Definable.iInter fun j => S.definable_setOf_eq _ (Fin.natAdd m j) (Fin.castAdd k (ι j)))
    using 1
  ext z
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨by simpa [Function.comp_def] using hx, mem_iInter.2 fun j => by simp⟩
  · rintro ⟨hz, hzι⟩
    refine ⟨_, hz, funext fun j => ?_⟩
    refine Fin.addCases (fun i => ?_) (fun j => ?_) j
    · simp
    · simpa using (mem_iInter.1 hzι j).symm

/-- A constant map is definable on every definable set. -/
theorem definableMapOn_const (hA : S.Definable m A) (c : Fin k → R) :
    S.DefinableMapOn (fun _ => c) A := by
  rw [definableMapOn_def]
  convert hA.image_appendEquiv_prod (S.definable_singleton c) using 1
  rw [prod_singleton, image_image]
  simp [Fin.appendEquiv]

end Maps

/-- The composite of definable maps is definable. -/
theorem DefinableMapOn.comp {l : ℕ} {S : OMinimalStructure R} {g : (Fin k → R) → Fin l → R}
    {f : (Fin m → R) → Fin k → R} {A : Set (Fin m → R)} {B : Set (Fin k → R)}
    (hg : S.DefinableMapOn g B) (hf : S.DefinableMapOn f A) (hfA : MapsTo f A B) :
    S.DefinableMapOn (g ∘ f) A := by
  -- The graph of `g ∘ f` is the image of `{(x, y, w) | (x, y) ∈ Γ f, (y, w) ∈ Γ g}` under the
  -- coordinate map forgetting the middle block `y`.
  let ι₁₂ : Fin (m + k) → Fin (m + k + l) := Fin.castAdd l
  let ι₂₃ : Fin (k + l) → Fin (m + k + l) := Fin.append (fun j => ι₁₂ (Fin.natAdd m j))
    (Fin.natAdd (m + k))
  let ι₁₃ : Fin (m + l) → Fin (m + k + l) := Fin.append (fun i => ι₁₂ (Fin.castAdd k i))
    (Fin.natAdd (m + k))
  rw [definableMapOn_def]
  convert ((hf.definable_graph.preimage_comp ι₁₂).inter
    (hg.definable_graph.preimage_comp ι₂₃)).image_comp ι₁₃ using 1
  ext z
  constructor
  · rintro ⟨x, hx, rfl⟩
    refine ⟨Fin.append (Fin.append x (f x)) (g (f x)), ⟨?_, ?_⟩, ?_⟩
    · exact ⟨x, hx, by funext i; simp [ι₁₂]⟩
    · refine ⟨f x, hfA hx, funext fun j => ?_⟩
      refine Fin.addCases (fun j => ?_) (fun j => ?_) j <;> simp [ι₂₃, ι₁₂]
    · funext j
      refine Fin.addCases (fun j => ?_) (fun j => ?_) j <;> simp [ι₁₃, ι₁₂]
  · rintro ⟨w, ⟨⟨x, hx, hw₁⟩, ⟨y, -, hw₂⟩⟩, rfl⟩
    have hx' : ∀ i, w (ι₁₂ (Fin.castAdd k i)) = x i := fun i => by
      simpa using (congrFun hw₁ (Fin.castAdd k i)).symm
    have hfx : ∀ j, w (ι₁₂ (Fin.natAdd m j)) = f x j := fun j => by
      simpa using (congrFun hw₁ (Fin.natAdd m j)).symm
    have hy' : ∀ j, w (ι₁₂ (Fin.natAdd m j)) = y j := fun j => by
      simpa [ι₂₃] using (congrFun hw₂ (Fin.castAdd l j)).symm
    have hgy : ∀ j, w (Fin.natAdd (m + k) j) = g y j := fun j => by
      simpa [ι₂₃] using (congrFun hw₂ (Fin.natAdd k j)).symm
    have hxy : f x = y := funext fun j => (hfx j).symm.trans (hy' j)
    refine ⟨x, hx, funext fun j => ?_⟩
    refine Fin.addCases (fun j => ?_) (fun j => ?_) j
    · simp [ι₁₃, hx']
    · simp [ι₁₃, hgy, hxy]

end OMinimalStructure

end TauCeti
