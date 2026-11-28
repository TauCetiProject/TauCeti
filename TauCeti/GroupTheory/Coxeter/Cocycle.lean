/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.Coxeter.Length
public import TauCeti.GroupTheory.Coxeter.BraidEquivalence
import TauCeti.GroupTheory.Coxeter.Matsumoto

/-!
# Cayley-graph 1-cocycles on Coxeter groups

A 1-cochain on the right Cayley graph of a Coxeter system `cs : CoxeterSystem M W` with values in
a group `G` assigns an element `u w i : G` to each directed edge `w ⟶ w * cs.simple i`. Along a
word `ω : List B` starting from `w`, multiplying these edge labels step by step yields the path
product `CoxeterSystem.wordCocycleProd cs u w ω`.

When `u` is invariant under braid moves at every basepoint, Matsumoto's theorem
(`TauCeti.braidEquivalent_of_isReduced_wordProd_eq`) implies that the path product along a reduced
word depends only on the group element represented by that word. If `u` also satisfies the
involution condition `u (w * cs.simple i) i = (u w i)⁻¹` on every undirected edge, then evaluating
the path product from `1` along reduced words produces the unique potential `f : W → G` with
`f 1 = 1` and `(f w)⁻¹ * f (w * cs.simple i) = u w i`. In topological terms, the Cayley 2-complex
of a Coxeter presentation is simply connected, so every 1-cocycle is a coboundary.

## Main definitions

* `CoxeterSystem.wordCocycleProd`: the ordered product of edge labels along a word starting at `w`.

## Main results

* `CoxeterSystem.wordCocycleProd_append`: path products multiply under word concatenation.
* `CoxeterSystem.BraidEquivalent.wordCocycleProd_eq`: braid-equivalent words have equal path
  products whenever the braid relations hold at every vertex.
* `CoxeterSystem.wordCocycleProd_eq_of_isReduced`: reduced words representing the same element have
  equal path products.
* `CoxeterSystem.fun_eq_const_of_mul_simple_eq`: a function invariant under right multiplication by
  all simple reflections is constant.
* `CoxeterSystem.existsUnique_cocycle_eq_inv_mul`: every Cayley-graph 1-cocycle satisfying the
  involution and braid relations is uniquely a coboundary normalized at `1`.

## References

* J. E. Humphreys, *Reflection Groups and Coxeter Groups*, CUP (1990), Section 1.9.
* A. Björner and F. Brenti, *Combinatorics of Coxeter Groups*, Springer GTM 231 (2005),
  Section 3.3.
-/

public section

namespace CoxeterSystem

section Monoid

variable {B W G : Type*} {M : CoxeterMatrix B} [Group W] [Monoid G]

/-- The product of a Cayley-graph 1-cochain `u : W → B → G` along the path starting at `w` and
following the simple reflections in `ω`. -/
def wordCocycleProd (cs : CoxeterSystem M W) (u : W → B → G) : W → List B → G
  | _, [] => 1
  | w, i :: ω => u w i * wordCocycleProd cs u (w * cs.simple i) ω

/-- The path product along the empty word is `1`. -/
@[simp]
theorem wordCocycleProd_nil (cs : CoxeterSystem M W) (u : W → B → G) (w : W) :
    cs.wordCocycleProd u w [] = 1 := (rfl)

/-- The path product along a nonempty word multiplies the first edge label by the path product from
the next vertex. -/
@[simp]
theorem wordCocycleProd_cons (cs : CoxeterSystem M W) (u : W → B → G) (w : W) (i : B)
    (ω : List B) :
    cs.wordCocycleProd u w (i :: ω) = u w i * cs.wordCocycleProd u (w * cs.simple i) ω := (rfl)

/-- The path product along a one-letter word is the single edge label. -/
theorem wordCocycleProd_singleton (cs : CoxeterSystem M W) (u : W → B → G) (w : W) (i : B) :
    cs.wordCocycleProd u w [i] = u w i := mul_one (u w i)

/-- Path products multiply under word concatenation, advancing the basepoint by the prefix word. -/
theorem wordCocycleProd_append (cs : CoxeterSystem M W) (u : W → B → G) (w : W)
    (ω₁ ω₂ : List B) :
    cs.wordCocycleProd u w (ω₁ ++ ω₂) =
      cs.wordCocycleProd u w ω₁ * cs.wordCocycleProd u (w * cs.wordProd ω₁) ω₂ := by
  induction ω₁ generalizing w with
  | nil => simp
  | cons i ω₁ ih => simp [wordCocycleProd_cons, wordProd_cons, ih, mul_assoc]

/-- A single braid move preserves the path product whenever the 1-cochain satisfies the braid
relations at every vertex. -/
theorem IsBraidMove.wordCocycleProd_eq (cs : CoxeterSystem M W) {u : W → B → G}
    (hbraid : ∀ w i j,
      cs.wordCocycleProd u w (braidWord M i j) = cs.wordCocycleProd u w (braidWord M j i))
    {ω ω' : List B} (h : IsBraidMove M ω ω') (w : W) :
    cs.wordCocycleProd u w ω = cs.wordCocycleProd u w ω' := by
  cases h with
  | mk _ _ i j => simp [wordCocycleProd_append, hbraid, cs.wordProd_braidWord_eq]

/-- Braid-equivalent words have equal path products whenever the 1-cochain satisfies the braid
relations at every vertex. -/
theorem BraidEquivalent.wordCocycleProd_eq (cs : CoxeterSystem M W) {u : W → B → G}
    (hbraid : ∀ w i j,
      cs.wordCocycleProd u w (CoxeterSystem.braidWord M i j) =
        cs.wordCocycleProd u w (CoxeterSystem.braidWord M j i))
    {ω ω' : List B} (h : BraidEquivalent M ω ω') (w : W) :
    cs.wordCocycleProd u w ω = cs.wordCocycleProd u w ω' :=
  h.induction_on (fun hm => hm.wordCocycleProd_eq cs hbraid w) (fun _ => rfl) Eq.symm Eq.trans

/-- Two reduced words representing the same Coxeter group element have equal path products from
every basepoint whenever the 1-cochain satisfies the braid relations. -/
theorem wordCocycleProd_eq_of_isReduced (cs : CoxeterSystem M W) {u : W → B → G}
    (hbraid : ∀ w i j,
      cs.wordCocycleProd u w (braidWord M i j) = cs.wordCocycleProd u w (braidWord M j i))
    {ω ω' : List B} (hω : cs.IsReduced ω) (hω' : cs.IsReduced ω')
    (hprod : cs.wordProd ω = cs.wordProd ω') (w : W) :
    cs.wordCocycleProd u w ω = cs.wordCocycleProd u w ω' :=
  (TauCeti.braidEquivalent_of_isReduced_wordProd_eq cs hω hω' hprod).wordCocycleProd_eq cs hbraid w

end Monoid

section Connected

variable {B W α : Type*} {M : CoxeterMatrix B} [Group W]

/-- A function on a Coxeter group that is invariant under right multiplication by every simple
reflection is constant. -/
theorem fun_eq_const_of_mul_simple_eq (cs : CoxeterSystem M W) {f : W → α}
    (hf : ∀ w i, f (w * cs.simple i) = f w) (w : W) : f w = f 1 :=
  cs.simple_induction_right (p := fun w => f w = f 1) w rfl fun w i h => (hf w i).trans h

end Connected

section Group

variable {B W G : Type*} {M : CoxeterMatrix B} [Group W] [Group G]

/-- Along any word, a coboundary multiplies the initial value of its potential by the path
product. -/
theorem apply_mul_wordProd_eq_mul_wordCocycleProd (cs : CoxeterSystem M W) {u : W → B → G}
    {f : W → G} (hf : ∀ w i, (f w)⁻¹ * f (w * cs.simple i) = u w i) (w : W) (ω : List B) :
    f (w * cs.wordProd ω) = f w * cs.wordCocycleProd u w ω := by
  induction ω generalizing w with
  | nil => simp
  | cons i ω ih =>
    rw [wordProd_cons, ← mul_assoc, ih, wordCocycleProd_cons, ← mul_assoc,
      eq_mul_of_inv_mul_eq (hf w i)]

/-- **Simply connectedness of the Coxeter Cayley 2-complex.** Every 1-cocycle `u : W → B → G` on
the right Cayley graph of a Coxeter system that satisfies the involution relation along edges and
the braid relations at every vertex is uniquely a coboundary `u w i = (f w)⁻¹ * f (w * s i)`
normalized by `f 1 = 1`. -/
theorem existsUnique_cocycle_eq_inv_mul (cs : CoxeterSystem M W) {u : W → B → G}
    (hinv : ∀ w i, u (w * cs.simple i) i = (u w i)⁻¹)
    (hbraid : ∀ w i j,
      cs.wordCocycleProd u w (braidWord M i j) = cs.wordCocycleProd u w (braidWord M j i)) :
    ∃! f : W → G, f 1 = 1 ∧ ∀ w i, (f w)⁻¹ * f (w * cs.simple i) = u w i := by
  classical
  let f : W → G := fun w => cs.wordCocycleProd u 1 (cs.exists_isReduced w).choose
  have hf_eq : ∀ {ω : List B}, cs.IsReduced ω → f (cs.wordProd ω) = cs.wordCocycleProd u 1 ω :=
    fun hω =>
      let hspec := (cs.exists_isReduced _).choose_spec
      cs.wordCocycleProd_eq_of_isReduced hbraid hspec.1 hω hspec.2.symm 1
  have hf_one : f 1 = 1 := by simpa [wordProd_nil] using hf_eq (ω := []) (by simp [IsReduced])
  have hf_asc : ∀ w i, cs.length (w * cs.simple i) = cs.length w + 1 →
      (f w)⁻¹ * f (w * cs.simple i) = u w i := fun w i hlen => by
    obtain ⟨ω, hω, rfl⟩ := cs.exists_isReduced w
    have hred : cs.IsReduced (ω ++ [i]) := by
      rw [IsReduced, wordProd_append, wordProd_singleton, hlen, List.length_append,
        List.length_singleton, hω.eq]
    rw [← wordProd_singleton, ← wordProd_append, hf_eq hred, wordCocycleProd_append, one_mul,
      wordCocycleProd_singleton, ← hf_eq hω, inv_mul_cancel_left]
  have hf_step : ∀ w i, (f w)⁻¹ * f (w * cs.simple i) = u w i := fun w i => by
    rcases cs.length_mul_simple w i with hlen | hlen
    · exact hf_asc w i hlen
    · have hback := hf_asc (w * cs.simple i) i (by rw [cs.simple_mul_simple_cancel_right, hlen])
      rw [cs.simple_mul_simple_cancel_right, hinv w i] at hback
      simpa [mul_inv_rev] using congrArg Inv.inv hback
  refine ⟨f, ⟨hf_one, hf_step⟩, fun g ⟨hg_one, hg⟩ => funext fun w => ?_⟩
  obtain ⟨ω, rfl⟩ := cs.wordProd_surjective w
  rw [← one_mul (cs.wordProd ω), cs.apply_mul_wordProd_eq_mul_wordCocycleProd hg,
    cs.apply_mul_wordProd_eq_mul_wordCocycleProd hf_step, hg_one, hf_one]

/-- Every Cayley-graph 1-cocycle on a Coxeter system satisfying the involution and braid relations
is a coboundary. -/
theorem exists_cocycle_eq_inv_mul (cs : CoxeterSystem M W) {u : W → B → G}
    (hinv : ∀ w i, u (w * cs.simple i) i = (u w i)⁻¹)
    (hbraid : ∀ w i j,
      cs.wordCocycleProd u w (braidWord M i j) = cs.wordCocycleProd u w (braidWord M j i)) :
    ∃ f : W → G, ∀ w i, (f w)⁻¹ * f (w * cs.simple i) = u w i :=
  let ⟨f, hf, _⟩ := cs.existsUnique_cocycle_eq_inv_mul hinv hbraid
  ⟨f, hf.2⟩

end Group

end CoxeterSystem
