/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.GraphOfGroups.Presentation
public import Mathlib.Combinatorics.Quiver.Path.Weight

/-!
# Paths in a graph of groups and the fundamental group at a vertex

An `𝔸`-path in a graph of groups `𝔸` over a Serre graph `Γ` is a word whose letters are elements
of vertex groups and darts of `Γ`, composable along `Γ`: a letter `g ∈ A_a` goes from `a` to `a`,
and a dart `e` goes from its source to its target. The `𝔸`-paths are the paths of the quiver
`GraphOfGroups.LetterVertex 𝔸` of letters, so Mathlib's `Quiver.Path` supplies concatenation and
reversal. Two `𝔸`-paths are *homotopic* when they are related by the elementary moves

* `g, h ~ g h` for consecutive elements of a vertex group, and `1 ~` the empty word;
* `e, rev e ~` the empty word for every dart `e`;
* `e, ω_e(c) ~ α_e(c), e` for every dart `e` and `c ∈ A_e`,

in any context. Read along a path, these are the defining relations of `π₁(𝔸, T)` for `T = ∅`;
for a general set `T` of darts, `π₁(𝔸, T)` additionally imposes `e = 1` for `e ∈ T`. The alternating
paths `g₀, e₁, g₁, …, e_k, g_k` of Kapovich, Weidmann and Myasnikov are the words in which vertex
group letters and darts alternate. Merging consecutive vertex group letters and inserting the
letter `1` turns any word into an alternating one, and their elementary equivalence
`g, e, ω_e(c), rev e, g' ~ g α_e(c) g'` and the moves above generate the same relation.

The closed `𝔸`-paths at a vertex `a` modulo homotopy form the fundamental group `π₁(𝔸, a)`,
with concatenation as multiplication and reversal (inverting the vertex group letters) as
inversion. An `𝔸`-path `p` from `a` to `b` conjugates the vertex group `A_b` into `π₁(𝔸, a)`, and
reading the letters of a path as elements of `π₁(𝔸, T)` gives a homomorphism
`π₁(𝔸, a) →* π₁(𝔸, T)` for every set `T` of darts. Over a graph without edges `π₁(𝔸, a)` is the
vertex group `A_a`.

## Main definitions

* `TauCeti.GraphOfGroups.Letter`: the letters of `𝔸`-paths.
* `TauCeti.GraphOfGroups.Path`: `𝔸`-paths.
* `TauCeti.GraphOfGroups.Path.Homotopic`: homotopy of `𝔸`-paths.
* `TauCeti.GraphOfGroups.π₁`: the fundamental group `π₁(𝔸, a)` of closed `𝔸`-paths.
* `TauCeti.GraphOfGroups.π₁.vertexHom`: the homomorphism `A_b →* π₁(𝔸, a)`, `g ↦ p g p⁻¹`.
* `TauCeti.GraphOfGroups.π₁.toπ₁Tree`: the homomorphism `π₁(𝔸, a) →* π₁(𝔸, T)`.

## Main results

* `TauCeti.GraphOfGroups.π₁.mk_eq_mk_iff`: closed paths give the same element of `π₁(𝔸, a)`
  exactly when they are homotopic.
* `TauCeti.GraphOfGroups.π₁.toπ₁Tree_vertexHom`: the image of `p g p⁻¹` in `π₁(𝔸, T)`.
* `TauCeti.GraphOfGroups.π₁.vertexEquivOfIsEmpty`: over a graph without edges,
  `A_a ≃* π₁(𝔸, a)`.

## References

* I. Kapovich, R. Weidmann, A. Myasnikov, *Foldings, graphs of groups and the membership problem*,
  Internat. J. Algebra Comput. 15 (2005), §2, Definitions 2.2–2.3.
* J.-P. Serre, *Trees*, Chapter I, §5.1.
-/

public section

universe u v w x

namespace TauCeti

namespace GraphOfGroups

variable {Γ : SerreGraph.{u, v}} (𝔸 : GraphOfGroups.{u, v, w, x} Γ)

/-- The vertices of `Γ`, as the vertices of the quiver whose arrows are the letters of
`𝔸`-paths. A separate type keeps this quiver apart from the quiver of darts of `Γ`. -/
structure LetterVertex (_ : GraphOfGroups.{u, v, w, x} Γ) : Type u where
  /-- The vertex of `Γ` underlying a vertex of the quiver of letters. -/
  as : Γ.V

/-- The letters of `𝔸`-paths: an element of the vertex group `A_a` is a letter from `a` to `a`,
and a dart of `Γ` from `a` to `b` is a letter from `a` to `b`. -/
inductive Letter : 𝔸.LetterVertex → 𝔸.LetterVertex → Type (max u v w)
  /-- An element of a vertex group. -/
  | vertex {a : Γ.V} (g : 𝔸.vertexGroup a) : Letter ⟨a⟩ ⟨a⟩
  /-- A dart of the underlying graph. -/
  | dart {a b : Γ.V} (e : a ⟶ b) : Letter ⟨a⟩ ⟨b⟩

instance : Quiver 𝔸.LetterVertex := ⟨𝔸.Letter⟩

variable {𝔸} in
/-- The reverse of a letter: the inverse of a vertex group element, or the reverse dart. -/
def Letter.reverse : ∀ {x y : 𝔸.LetterVertex}, 𝔸.Letter x y → 𝔸.Letter y x
  | _, _, .vertex g => .vertex g⁻¹
  | _, _, .dart e => .dart (Quiver.reverse e)

variable {𝔸} in
/-- Reversing a letter twice gives the letter back. -/
theorem Letter.reverse_reverse {x y : 𝔸.LetterVertex} (l : 𝔸.Letter x y) :
    l.reverse.reverse = l := by
  cases l with
  | vertex g => simp only [Letter.reverse, inv_inv]
  | dart e => simp only [Letter.reverse, Quiver.reverse_reverse]

instance : Quiver.HasInvolutiveReverse 𝔸.LetterVertex where
  reverse' := Letter.reverse
  inv' := Letter.reverse_reverse

@[simp] theorem Letter.reverse_vertex {a : Γ.V} (g : 𝔸.vertexGroup a) :
    Quiver.reverse (V := 𝔸.LetterVertex) (Letter.vertex g) = Letter.vertex g⁻¹ :=
  (rfl)

@[simp] theorem Letter.reverse_dart {a b : Γ.V} (e : a ⟶ b) :
    Quiver.reverse (V := 𝔸.LetterVertex) (Letter.dart (𝔸 := 𝔸) e) =
      Letter.dart (Quiver.reverse e) :=
  (rfl)

/-- An `𝔸`-path: a composable word in vertex group elements and darts. -/
abbrev Path (x y : 𝔸.LetterVertex) : Type (max u v w) := Quiver.Path x y

namespace Path

variable {𝔸}

/-- The `𝔸`-path of length one given by an element of a vertex group. -/
def ofVertex {a : Γ.V} (g : 𝔸.vertexGroup a) : 𝔸.Path ⟨a⟩ ⟨a⟩ :=
  Quiver.Hom.toPath (Letter.vertex g)

/-- The `𝔸`-path of length one given by a dart. -/
def ofDart {a b : Γ.V} (e : a ⟶ b) : 𝔸.Path ⟨a⟩ ⟨b⟩ :=
  Quiver.Hom.toPath (Letter.dart e)

@[simp] theorem comp_ofVertex {x : 𝔸.LetterVertex} {a : Γ.V} (p : 𝔸.Path x ⟨a⟩)
    (g : 𝔸.vertexGroup a) : p.comp (ofVertex g) = p.cons (Letter.vertex g) :=
  Quiver.Path.comp_toPath_eq_cons ..

@[simp] theorem comp_ofDart {x : 𝔸.LetterVertex} {a b : Γ.V} (p : 𝔸.Path x ⟨a⟩) (e : a ⟶ b) :
    p.comp (ofDart e) = p.cons (Letter.dart e) :=
  Quiver.Path.comp_toPath_eq_cons ..

@[simp] theorem reverse_ofVertex {a : Γ.V} (g : 𝔸.vertexGroup a) :
    (ofVertex g).reverse = ofVertex g⁻¹ :=
  (rfl)

@[simp] theorem reverse_ofDart {a b : Γ.V} (e : a ⟶ b) :
    (ofDart (𝔸 := 𝔸) e).reverse = ofDart (Quiver.reverse e) :=
  (rfl)

/-- Homotopy of `𝔸`-paths with fixed endpoints: the congruence generated by merging consecutive
vertex group letters `g, h ~ g h`, deleting the letter `1`, deleting a dart followed by its
reverse, and moving edge group elements across darts, `e, ω_e(c) ~ α_e(c), e`. -/
inductive Homotopic {x : 𝔸.LetterVertex} : ∀ {y : 𝔸.LetterVertex}, 𝔸.Path x y → 𝔸.Path x y → Prop
  | refl {y} (p : 𝔸.Path x y) : Homotopic p p
  | symm {y} {p q : 𝔸.Path x y} : Homotopic p q → Homotopic q p
  | trans {y} {p q r : 𝔸.Path x y} : Homotopic p q → Homotopic q r → Homotopic p r
  | cons {y z} {p q : 𝔸.Path x y} (h : Homotopic p q) (l : 𝔸.Letter y z) :
      Homotopic (p.cons l) (q.cons l)
  | mul {a : Γ.V} (p : 𝔸.Path x ⟨a⟩) (g h : 𝔸.vertexGroup a) :
      Homotopic ((p.cons (Letter.vertex g)).cons (Letter.vertex h))
        (p.cons (Letter.vertex (g * h)))
  | one {a : Γ.V} (p : 𝔸.Path x ⟨a⟩) : Homotopic (p.cons (Letter.vertex 1)) p
  | dart_reverse {a b : Γ.V} (p : 𝔸.Path x ⟨a⟩) (e : a ⟶ b) :
      Homotopic ((p.cons (Letter.dart e)).cons (Letter.dart (Quiver.reverse e))) p
  | dart_ω (e : Γ.E) (c : 𝔸.edgeGroup (Γ.toGeomEdge e)) (p : 𝔸.Path x ⟨Γ.src e⟩) :
      Homotopic ((p.cons (Letter.dart (Γ.dart e))).cons (Letter.vertex (𝔸.ω e c)))
        ((p.cons (Letter.vertex (𝔸.α e c))).cons (Letter.dart (Γ.dart e)))

namespace Homotopic

variable {x y z : 𝔸.LetterVertex}

theorem equivalence : Equivalence (Homotopic (𝔸 := 𝔸) (x := x) (y := y)) :=
  ⟨refl, symm, trans⟩

/-- Homotopy is preserved by placing a fixed path before the paths being compared. -/
theorem comp_left {q r : 𝔸.Path y z} (h : Homotopic q r) (p : 𝔸.Path x y) :
    Homotopic (p.comp q) (p.comp r) := by
  induction h with
  | refl => exact .refl _
  | symm _ ih => exact ih.symm
  | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂
  | cons _ l ih => exact ih.cons l
  | mul q g h => exact .mul (p.comp q) g h
  | one q => exact .one (p.comp q)
  | dart_reverse q e => exact .dart_reverse (p.comp q) e
  | dart_ω e c q => exact .dart_ω e c (p.comp q)

/-- Homotopy is preserved by appending a fixed path. -/
theorem comp_right {p q : 𝔸.Path x y} (h : Homotopic p q) (r : 𝔸.Path y z) :
    Homotopic (p.comp r) (q.comp r) := by
  induction r with
  | nil => exact h
  | cons r l ih => exact ih.cons l

/-- Concatenating homotopic paths gives homotopic paths. -/
theorem comp {p q : 𝔸.Path x y} {r s : 𝔸.Path y z} (h : Homotopic p q) (k : Homotopic r s) :
    Homotopic (p.comp r) (q.comp s) :=
  (h.comp_right r).trans (k.comp_left q)

/-- A letter followed by its reverse cancels. -/
theorem cons_cons_reverse (p : 𝔸.Path x y) (l : 𝔸.Letter y z) :
    Homotopic ((p.cons l).cons (Quiver.reverse l)) p := by
  cases l with
  | vertex g =>
    refine (Homotopic.mul p g g⁻¹).trans ?_
    rw [mul_inv_cancel]
    exact .one p
  | dart e => exact .dart_reverse p e

/-- A path followed by its reverse is homotopic to the empty path. -/
theorem comp_reverse (p : 𝔸.Path x y) : Homotopic (p.comp p.reverse) Quiver.Path.nil := by
  induction p with
  | nil => exact .refl _
  | cons p l ih =>
    rw [Quiver.Path.reverse, ← Quiver.Path.comp_assoc, Quiver.Path.comp_toPath_eq_cons]
    exact ((cons_cons_reverse p l).comp_right p.reverse).trans ih

/-- The reverse of a path followed by that path is homotopic to the empty path. -/
theorem reverse_comp (p : 𝔸.Path x y) : Homotopic (p.reverse.comp p) Quiver.Path.nil := by
  simpa only [Quiver.Path.reverse_reverse] using comp_reverse p.reverse

/-- Inserting `p⁻¹ p` between two paths does not change the homotopy class. -/
theorem comp_reverse_comp_comp {w : 𝔸.LetterVertex} (q : 𝔸.Path x y) (p : 𝔸.Path z y)
    (r : 𝔸.Path y w) : Homotopic ((q.comp p.reverse).comp (p.comp r)) (q.comp r) := by
  rw [Quiver.Path.comp_assoc, ← Quiver.Path.comp_assoc p.reverse]
  simpa only [Quiver.Path.nil_comp] using ((reverse_comp p).comp_right r).comp_left q

/-- Reversing homotopic paths gives homotopic paths. -/
theorem reverse {p q : 𝔸.Path x y} (h : Homotopic p q) : Homotopic p.reverse q.reverse := by
  -- `p⁻¹ ~ p⁻¹ (q q⁻¹) = (p⁻¹ q) q⁻¹ ~ (p⁻¹ p) q⁻¹ ~ q⁻¹`.
  have h₁ := ((comp_reverse q).comp_left p.reverse).symm
  rw [Quiver.Path.comp_nil, ← Quiver.Path.comp_assoc] at h₁
  have h₂ := ((h.symm.comp_left p.reverse).trans (reverse_comp p)).comp_right q.reverse
  rw [Quiver.Path.nil_comp] at h₂
  exact h₁.trans h₂

end Homotopic

variable (𝔸) in
/-- Homotopy of `𝔸`-paths as a setoid. -/
instance setoid (x y : 𝔸.LetterVertex) : Setoid (𝔸.Path x y) :=
  ⟨Homotopic, Homotopic.equivalence⟩

end Path

/-- The fundamental group `π₁(𝔸, a)` of a graph of groups at a vertex `a`: the closed `𝔸`-paths
at `a` modulo homotopy, with concatenation as multiplication. -/
def π₁ (a : Γ.V) : Type (max u v w) := Quotient (Path.setoid 𝔸 ⟨a⟩ ⟨a⟩)

namespace π₁

variable {𝔸} {a b : Γ.V}

/-- The element of `π₁(𝔸, a)` represented by a closed `𝔸`-path. -/
def mk (p : 𝔸.Path ⟨a⟩ ⟨a⟩) : π₁ 𝔸 a := Quotient.mk _ p

theorem mk_surjective : Function.Surjective (mk : 𝔸.Path ⟨a⟩ ⟨a⟩ → π₁ 𝔸 a) :=
  Quotient.mk_surjective

/-- Prove a property of elements of `π₁(𝔸, a)` by checking it on closed paths. -/
@[elab_as_elim] theorem induction_on {P : π₁ 𝔸 a → Prop} (g : π₁ 𝔸 a)
    (h : ∀ p : 𝔸.Path ⟨a⟩ ⟨a⟩, P (mk p)) : P g :=
  Quotient.ind h g

/-- Two closed paths represent the same element of `π₁(𝔸, a)` exactly when they are
homotopic. -/
theorem mk_eq_mk_iff {p q : 𝔸.Path ⟨a⟩ ⟨a⟩} : mk p = mk q ↔ p.Homotopic q :=
  Quotient.eq

/-- A function on closed paths at `a` that is constant on homotopy classes descends to
`π₁(𝔸, a)`. -/
def lift {β : Sort*} (f : 𝔸.Path ⟨a⟩ ⟨a⟩ → β) (hf : ∀ p q, p.Homotopic q → f p = f q) :
    π₁ 𝔸 a → β :=
  Quotient.lift f hf

@[simp] theorem lift_mk {β : Sort*} (f : 𝔸.Path ⟨a⟩ ⟨a⟩ → β)
    (hf : ∀ p q, p.Homotopic q → f p = f q) (p : 𝔸.Path ⟨a⟩ ⟨a⟩) : lift f hf (mk p) = f p :=
  (rfl)

instance : Mul (π₁ 𝔸 a) where
  mul := lift (fun p => lift (fun q => mk (p.comp q))
      fun _ _ h => mk_eq_mk_iff.2 ((Path.Homotopic.refl p).comp h))
    fun _ _ h => funext fun g => induction_on g fun q => by
      rw [lift_mk, lift_mk]
      exact mk_eq_mk_iff.2 (h.comp (.refl q))

instance : One (π₁ 𝔸 a) := ⟨mk Quiver.Path.nil⟩

instance : Inv (π₁ 𝔸 a) where
  inv := lift (fun p => mk p.reverse) fun _ _ h => mk_eq_mk_iff.2 h.reverse

@[simp] theorem mk_comp (p q : 𝔸.Path ⟨a⟩ ⟨a⟩) : mk (p.comp q) = mk p * mk q :=
  (rfl)

@[simp] theorem mk_nil : mk (Quiver.Path.nil : 𝔸.Path ⟨a⟩ ⟨a⟩) = 1 :=
  (rfl)

@[simp] theorem mk_reverse (p : 𝔸.Path ⟨a⟩ ⟨a⟩) : mk p.reverse = (mk p)⁻¹ :=
  (rfl)

instance : Group (π₁ 𝔸 a) where
  mul_assoc g h k := induction_on g fun p => induction_on h fun q => induction_on k fun r => by
    simp only [← mk_comp, Quiver.Path.comp_assoc]
  one_mul g := induction_on g fun p => by simp only [← mk_nil, ← mk_comp, Quiver.Path.nil_comp]
  mul_one g := induction_on g fun p => by simp only [← mk_nil, ← mk_comp, Quiver.Path.comp_nil]
  inv_mul_cancel g := induction_on g fun p => by
    rw [← mk_reverse, ← mk_comp, ← mk_nil, mk_eq_mk_iff]
    exact Path.Homotopic.reverse_comp p

/-- The homomorphism `A_b →* π₁(𝔸, a)`, `g ↦ p g p⁻¹`, given by an `𝔸`-path `p` from `a` to
`b`. -/
def vertexHom (p : 𝔸.Path ⟨a⟩ ⟨b⟩) : 𝔸.vertexGroup b →* π₁ 𝔸 a where
  toFun g := mk ((p.comp (Path.ofVertex g)).comp p.reverse)
  map_one' := Quotient.sound <|
    ((Path.Homotopic.one p).comp_right p.reverse).trans (Path.Homotopic.comp_reverse p)
  map_mul' g h := by
    refine Quotient.sound (Path.Homotopic.symm ?_)
    -- `(p g p⁻¹) (p h p⁻¹) ~ (p g) (h p⁻¹) = ((p g) h) p⁻¹ ~ (p (g h)) p⁻¹`.
    rw [Quiver.Path.comp_assoc p (Path.ofVertex h)]
    refine (Path.Homotopic.comp_reverse_comp_comp _ p _).trans ?_
    rw [← Quiver.Path.comp_assoc, Path.comp_ofVertex, Path.comp_ofVertex, Path.comp_ofVertex]
    exact (Path.Homotopic.mul p g h).comp_right p.reverse

theorem vertexHom_apply (p : 𝔸.Path ⟨a⟩ ⟨b⟩) (g : 𝔸.vertexGroup b) :
    vertexHom p g = mk ((p.comp (Path.ofVertex g)).comp p.reverse) :=
  (rfl)

@[simp] theorem vertexHom_nil_apply (g : 𝔸.vertexGroup a) :
    vertexHom Quiver.Path.nil g = mk (Path.ofVertex g) :=
  (rfl)

/-- Homotopic paths give the same homomorphism of the vertex group into `π₁(𝔸, a)`. -/
theorem vertexHom_congr {p q : 𝔸.Path ⟨a⟩ ⟨b⟩} (h : p.Homotopic q) :
    vertexHom p = vertexHom q :=
  MonoidHom.ext fun _ => Quotient.sound <|
    (h.comp_right (Path.ofVertex _)).comp h.reverse

end π₁

/-! ### Reading paths in `π₁(𝔸, T)` -/

variable {𝔸}

/-- The element of `π₁(𝔸, T)` given by a letter: `of g` for a vertex group element and the dart
generator for a dart. -/
def Letter.toπ₁Tree (T : Set Γ.E) : ∀ {x y : 𝔸.LetterVertex}, 𝔸.Letter x y → π₁Tree 𝔸 T
  | _, _, .vertex g => π₁Tree.of T _ g
  | _, _, .dart e => π₁Tree.edge T e.1

@[simp] theorem Letter.toπ₁Tree_vertex (T : Set Γ.E) {a : Γ.V} (g : 𝔸.vertexGroup a) :
    (Letter.vertex g).toπ₁Tree T = π₁Tree.of T a g :=
  (rfl)

@[simp] theorem Letter.toπ₁Tree_dart (T : Set Γ.E) {a b : Γ.V} (e : a ⟶ b) :
    (Letter.dart (𝔸 := 𝔸) e).toπ₁Tree T = π₁Tree.edge T e.1 :=
  (rfl)

/-- The image of a reversed letter in `π₁(𝔸, T)` is the inverse of the image of the letter. -/
@[simp] theorem Letter.toπ₁Tree_reverse (T : Set Γ.E) {x y : 𝔸.LetterVertex} (l : 𝔸.Letter x y) :
    Letter.toπ₁Tree T (Quiver.reverse (V := 𝔸.LetterVertex) l) = (l.toπ₁Tree T)⁻¹ := by
  cases l <;> simp

/-- The element of `π₁(𝔸, T)` read off an `𝔸`-path: the product of the images of its letters. -/
def Path.toπ₁Tree (T : Set Γ.E) {x y : 𝔸.LetterVertex} (p : 𝔸.Path x y) : π₁Tree 𝔸 T :=
  p.weight fun l => Letter.toπ₁Tree T l

namespace Path

variable (T : Set Γ.E) {x y z : 𝔸.LetterVertex}

@[simp] theorem toπ₁Tree_nil : toπ₁Tree T (Quiver.Path.nil : 𝔸.Path x x) = 1 :=
  Quiver.Path.weight_nil ..

@[simp] theorem toπ₁Tree_cons (p : 𝔸.Path x y) (l : 𝔸.Letter y z) :
    toπ₁Tree T (p.cons l) = p.toπ₁Tree T * l.toπ₁Tree T :=
  Quiver.Path.weight_cons ..

@[simp] theorem toπ₁Tree_comp (p : 𝔸.Path x y) (q : 𝔸.Path y z) :
    toπ₁Tree T (p.comp q) = p.toπ₁Tree T * q.toπ₁Tree T :=
  Quiver.Path.weight_comp ..

@[simp] theorem toπ₁Tree_ofVertex {a : Γ.V} (g : 𝔸.vertexGroup a) :
    toπ₁Tree T (ofVertex g) = π₁Tree.of T a g := by
  simp [ofVertex, Quiver.Hom.toPath]

@[simp] theorem toπ₁Tree_ofDart {a b : Γ.V} (e : a ⟶ b) :
    toπ₁Tree T (ofDart (𝔸 := 𝔸) e) = π₁Tree.edge T e.1 := by
  simp [ofDart, Quiver.Hom.toPath]

@[simp] theorem toπ₁Tree_reverse (p : 𝔸.Path x y) :
    toπ₁Tree T p.reverse = (p.toπ₁Tree T)⁻¹ := by
  induction p with
  | nil => simp
  | cons p l ih => simp [Quiver.Path.reverse, ih, Quiver.Hom.toPath]

/-- Homotopic paths have the same image in `π₁(𝔸, T)`. -/
theorem Homotopic.toπ₁Tree_eq {p q : 𝔸.Path x y} (h : p.Homotopic q) :
    p.toπ₁Tree T = q.toπ₁Tree T := by
  induction h with
  | refl => rfl
  | symm _ ih => exact ih.symm
  | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂
  | cons _ l ih => simp [ih]
  | mul p g h => simp [mul_assoc]
  | one p => simp
  | dart_reverse p e => simp [mul_assoc]
  | dart_ω e c p => simp [mul_assoc, π₁Tree.edge_mul_of_ω]

end Path

namespace π₁

variable {a b : Γ.V}

variable (𝔸) in
/-- Reading the letters of closed `𝔸`-paths at `a` in `π₁(𝔸, T)` gives a homomorphism
`π₁(𝔸, a) →* π₁(𝔸, T)`, for every set `T` of darts. -/
def toπ₁Tree (a : Γ.V) (T : Set Γ.E) : π₁ 𝔸 a →* π₁Tree 𝔸 T where
  toFun := lift (Path.toπ₁Tree T) fun _ _ h => Path.Homotopic.toπ₁Tree_eq T h
  map_one' := Path.toπ₁Tree_nil T
  map_mul' g h := by
    induction g using Quotient.ind
    induction h using Quotient.ind
    exact Path.toπ₁Tree_comp T _ _

@[simp] theorem toπ₁Tree_mk (T : Set Γ.E) (p : 𝔸.Path ⟨a⟩ ⟨a⟩) :
    toπ₁Tree 𝔸 a T (mk p) = p.toπ₁Tree T :=
  (rfl)

/-- The image of `p g p⁻¹` in `π₁(𝔸, T)` is the conjugate of `g` by the image of `p`. -/
@[simp] theorem toπ₁Tree_vertexHom (T : Set Γ.E) (p : 𝔸.Path ⟨a⟩ ⟨b⟩) (g : 𝔸.vertexGroup b) :
    toπ₁Tree 𝔸 a T (vertexHom p g) = p.toπ₁Tree T * π₁Tree.of T b g * (p.toπ₁Tree T)⁻¹ := by
  simp [vertexHom_apply]

/-! ### Graphs without edges -/

section isEmpty

variable [IsEmpty Γ.E]

/-- Over a graph without edges, every `𝔸`-path from `a` ends at `a` and is homotopic to a single
vertex group letter. -/
private theorem exists_homotopic_ofVertex_aux :
    ∀ {y : 𝔸.LetterVertex} (p : 𝔸.Path ⟨a⟩ y), ∃ h : y = ⟨a⟩, ∃ g : 𝔸.vertexGroup a,
      p.Homotopic (cast (congrArg (𝔸.Path ⟨a⟩) h).symm (Path.ofVertex g))
  | _, .nil => ⟨rfl, 1, (Path.Homotopic.one _).symm⟩
  | _, .cons p (.vertex g) => by
    obtain ⟨h, g', hg'⟩ := exists_homotopic_ofVertex_aux p
    cases h
    exact ⟨rfl, g' * g, (hg'.cons _).trans (Path.Homotopic.mul _ g' g)⟩
  | _, .cons _ (.dart e) => isEmptyElim e.1

/-- Over a graph without edges, every closed `𝔸`-path is homotopic to a single vertex group
letter. -/
theorem exists_homotopic_ofVertex_of_isEmpty (p : 𝔸.Path ⟨a⟩ ⟨a⟩) :
    ∃ g : 𝔸.vertexGroup a, p.Homotopic (Path.ofVertex g) := by
  obtain ⟨_, g, hg⟩ := exists_homotopic_ofVertex_aux p
  exact ⟨g, hg⟩

variable (𝔸) in
/-- Over a graph without edges, `π₁(𝔸, a)` is the vertex group `A_a`. -/
noncomputable def vertexEquivOfIsEmpty (a : Γ.V) : 𝔸.vertexGroup a ≃* π₁ 𝔸 a :=
  MulEquiv.ofBijective (vertexHom Quiver.Path.nil)
    ⟨fun g h hgh => π₁Tree.of_injective_of_isEmpty (T := ∅) a <| by
        simpa using congrArg (toπ₁Tree 𝔸 a ∅) hgh,
      fun g => induction_on g fun p => by
        obtain ⟨g, hg⟩ := exists_homotopic_ofVertex_of_isEmpty p
        exact ⟨g, (mk_eq_mk_iff.2 hg).symm⟩⟩

@[simp] theorem vertexEquivOfIsEmpty_apply (g : 𝔸.vertexGroup a) :
    vertexEquivOfIsEmpty 𝔸 a g = mk (Path.ofVertex g) :=
  (rfl)

end isEmpty

end π₁

end GraphOfGroups

end TauCeti
