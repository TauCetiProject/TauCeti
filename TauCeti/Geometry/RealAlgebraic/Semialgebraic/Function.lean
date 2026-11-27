/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.AffineSpace.AffineMap
public import TauCeti.Geometry.RealAlgebraic.Semialgebraic.Basic
import Mathlib.LinearAlgebra.AffineSpace.AffineEquiv
import TauCeti.LinearAlgebra.AffineSpace.AffineMap

/-!
# Semialgebraic functions

A function between coordinate spaces is semialgebraic on a set when its domain and graph are
semialgebraic.  The graph is regarded as a subset of the coordinate space indexed by the disjoint
union of the input and output coordinates.  Requiring the specified domain to be semialgebraic is
useful before projection closure is available: semialgebraicity of a graph alone does not yet let
us recover its projection onto the input coordinates.

This file gives the graph predicate its basic API.  It proves restriction, congruence, and
piecewise-gluing laws and shows that polynomial maps, affine maps on finite-dimensional coordinate
spaces (`AffineMap.isSemialgebraicOn`, `AffineMap.isSemialgebraicMap`,
`TauCeti.IsSemialgebraic.preimage_affineMap`, `AffineMap.isSemialgebraic_pos`), coordinatewise
rational maps over a linearly ordered field (`TauCeti.isSemialgebraicOn_eval_div`,
`TauCeti.isSemialgebraicMap_eval_div`), and more generally functions whose graph over a
semialgebraic domain is cut out by polynomial equations
(`TauCeti.isSemialgebraicOn_of_forall_eq_iff`), are semialgebraic.  It also proves the operations
whose graphs are inverse images of the given graphs, so that no coordinate has to be eliminated:
pairing two functions on the same domain (`TauCeti.IsSemialgebraicOn.sumElim`), assembling a
function from its coordinates (`TauCeti.IsSemialgebraicOn.pi`), precomposition with a polynomial
map (`TauCeti.IsSemialgebraicOn.comp_eval`), constant fibers and their complements
(`TauCeti.IsSemialgebraicOn.isSemialgebraic_inter_setOf_eq_const`,
`TauCeti.IsSemialgebraicOn.isSemialgebraic_inter_setOf_ne_const`), pointwise negation
(`TauCeti.IsSemialgebraicOn.neg`), coordinatewise reciprocal over a field
(`TauCeti.isSemialgebraicOn_inv`, `TauCeti.isSemialgebraicMap_inv`), and bijective changes of the
input or output coordinates (`TauCeti.isSemialgebraicOn_preimage_comp_equiv_iff`,
`TauCeti.isSemialgebraicOn_comp_equiv_iff`).  It deliberately does not assert closure under
arbitrary composition, whose graph generally requires eliminating the intermediate coordinates;
images, inverse images, composition, and pointwise sums, products, differences, reciprocals, and
quotients are derived from projection closure in
`TauCeti.Geometry.RealAlgebraic.Semialgebraic.Image`.

## References

S. Basu, R. Pollack, and M.-F. Roy,
[Algorithms in Real Algebraic Geometry](https://doi.org/10.1007/3-540-33099-2),
second edition, Chapter 2.

`TauCeti.isSemialgebraicOn_of_forall_eq_iff` is adapted from its complex-coordinate counterpart
`TauCeti.isSemialgebraicOn_complexToRealPi_of_forall_eq_iff` in
`TauCeti.Geometry.RealAlgebraic.Semialgebraic.Complex`.
-/

public section

open MvPolynomial Set

namespace TauCeti

variable {σ τ R : Type*} [CommRing R] [LinearOrder R]

/-- A function `f : (σ → R) → (τ → R)` is semialgebraic on `s` if `s` is semialgebraic and the
graph of `f` over `s`, encoded in the coordinate space `σ ⊕ τ → R`, is semialgebraic. -/
def IsSemialgebraicOn (f : (σ → R) → (τ → R)) (s : Set (σ → R)) : Prop :=
  IsSemialgebraic s ∧
    IsSemialgebraic (Equiv.sumArrowEquivProdArrow σ τ R ⁻¹' s.graphOn f)

/-- A function between coordinate spaces is semialgebraic if its graph over the whole input space
is semialgebraic. -/
def IsSemialgebraicMap (f : (σ → R) → (τ → R)) : Prop :=
  IsSemialgebraicOn f univ

/-- Semialgebraicity on the whole domain is semialgebraicity as a map. -/
@[simp]
theorem isSemialgebraicOn_univ {f : (σ → R) → (τ → R)} :
    IsSemialgebraicOn f univ ↔ IsSemialgebraicMap f :=
  Iff.rfl

/-- Characterization of a function being semialgebraic on a specified domain. -/
theorem isSemialgebraicOn_def {f : (σ → R) → (τ → R)} {s : Set (σ → R)} :
    IsSemialgebraicOn f s ↔ IsSemialgebraic s ∧
      IsSemialgebraic (Equiv.sumArrowEquivProdArrow σ τ R ⁻¹' s.graphOn f) :=
  Iff.rfl

/-- Characterization of a semialgebraic map by its graph. -/
theorem isSemialgebraicMap_def {f : (σ → R) → (τ → R)} :
    IsSemialgebraicMap f ↔
      IsSemialgebraic (Equiv.sumArrowEquivProdArrow σ τ R ⁻¹' univ.graphOn f) := by
  simp [IsSemialgebraicMap, IsSemialgebraicOn]

omit [CommRing R] [LinearOrder R] in
/-- A point of `σ ⊕ τ → R` lies on the encoded graph of `f` over `s` exactly when its input
coordinates lie in `s` and `f` sends them to its output coordinates. -/
theorem mem_preimage_sumArrowEquivProdArrow_graphOn {f : (σ → R) → (τ → R)} {s : Set (σ → R)}
    {z : σ ⊕ τ → R} :
    z ∈ Equiv.sumArrowEquivProdArrow σ τ R ⁻¹' s.graphOn f ↔
      z ∘ Sum.inl ∈ s ∧ f (z ∘ Sum.inl) = z ∘ Sum.inr := by
  rw [mem_preimage, mem_graphOn]
  -- `Equiv.sumArrowEquivProdArrow σ τ R z` is `(z ∘ Sum.inl, z ∘ Sum.inr)` by definition.
  rfl

omit [CommRing R] [LinearOrder R] in
/-- Membership in a scalar graph encoded using `Unit` output coordinates is given by the
input-domain condition and equality of the scalar output coordinate. -/
theorem mem_preimage_sumArrowEquivProdArrow_scalar_graphOn {f : (σ → R) → R}
    {s : Set (σ → R)} {z : σ ⊕ Unit → R} :
    z ∈ Equiv.sumArrowEquivProdArrow σ Unit R ⁻¹' s.graphOn (fun x _ ↦ f x) ↔
      z ∘ Sum.inl ∈ s ∧ f (z ∘ Sum.inl) = z (Sum.inr ()) := by
  rw [mem_preimage_sumArrowEquivProdArrow_graphOn]
  simp only [funext_iff, Function.comp_apply, Unique.forall_iff]

/-- The domain of a function semialgebraic on a set is semialgebraic. -/
theorem IsSemialgebraicOn.isSemialgebraic {f : (σ → R) → (τ → R)} {s : Set (σ → R)}
    (hf : IsSemialgebraicOn f s) : IsSemialgebraic s :=
  hf.1

/-- The graph of a function semialgebraic on a set is semialgebraic. -/
theorem IsSemialgebraicOn.graph {f : (σ → R) → (τ → R)} {s : Set (σ → R)}
    (hf : IsSemialgebraicOn f s) :
    IsSemialgebraic (Equiv.sumArrowEquivProdArrow σ τ R ⁻¹' s.graphOn f) :=
  hf.2

/-- Restricting a semialgebraic function to a semialgebraic subset preserves
semialgebraicity. -/
theorem IsSemialgebraicOn.mono {f : (σ → R) → (τ → R)} {s t : Set (σ → R)}
    (hf : IsSemialgebraicOn f s) (ht : IsSemialgebraic t) (h : t ⊆ s) :
    IsSemialgebraicOn f t := by
  refine ⟨ht, ?_⟩
  have hgraph : Equiv.sumArrowEquivProdArrow σ τ R ⁻¹' t.graphOn f =
      (Equiv.sumArrowEquivProdArrow σ τ R ⁻¹' s.graphOn f) ∩
        (fun z : σ ⊕ τ → R => z ∘ Sum.inl) ⁻¹' t := by
    ext z
    have hfst : (Equiv.sumArrowEquivProdArrow σ τ R z).1 = z ∘ Sum.inl := by
      funext i
      exact Equiv.sumArrowEquivProdArrow_apply_fst z i
    simp only [mem_preimage, mem_graphOn, mem_inter_iff, hfst]
    constructor
    · intro hz
      exact ⟨⟨h hz.1, hz.2⟩, hz.1⟩
    · intro hz
      exact ⟨hz.2, hz.1.2⟩
  rw [hgraph]
  exact hf.graph.inter (ht.preimage_comp Sum.inl)

/-- A semialgebraic map is semialgebraic on every semialgebraic domain. -/
theorem IsSemialgebraicMap.isSemialgebraicOn {f : (σ → R) → (τ → R)}
    (hf : IsSemialgebraicMap f) {s : Set (σ → R)} (hs : IsSemialgebraic s) :
    IsSemialgebraicOn f s :=
  hf.mono hs (subset_univ s)

/-- Semialgebraicity on a set depends only on the values of the function on that set. -/
theorem IsSemialgebraicOn.congr {f g : (σ → R) → (τ → R)} {s : Set (σ → R)}
    (hf : IsSemialgebraicOn f s) (h : s.EqOn f g) : IsSemialgebraicOn g s := by
  refine ⟨hf.isSemialgebraic, ?_⟩
  rw [← Set.graphOn_inj.2 h]
  exact hf.graph

/-- Semialgebraicity of a map depends only on its pointwise values. -/
theorem IsSemialgebraicMap.congr {f g : (σ → R) → (τ → R)} (hf : IsSemialgebraicMap f)
    (h : ∀ x, f x = g x) : IsSemialgebraicMap g :=
  funext h ▸ hf

/-- Every function is semialgebraic on the empty set. -/
@[simp]
theorem isSemialgebraicOn_empty (f : (σ → R) → (τ → R)) :
    IsSemialgebraicOn f ∅ := by
  simp [IsSemialgebraicOn]

/-- Semialgebraic functions on two semialgebraic pieces glue to a semialgebraic function. -/
theorem IsSemialgebraicOn.glue {f g h : (σ → R) → (τ → R)} {s t : Set (σ → R)}
    (hf : IsSemialgebraicOn f (s ∩ t)) (hg : IsSemialgebraicOn g (s \ t))
    (hft : (s ∩ t).EqOn h f) (hgt : (s \ t).EqOn h g) : IsSemialgebraicOn h s := by
  have hhst := hf.congr hft.symm
  have hhst' := hg.congr hgt.symm
  have hst : s = (s ∩ t) ∪ (s \ t) := by
    ext x
    simp
  have hs : IsSemialgebraic s := by
    rw [hst]
    exact hf.isSemialgebraic.union hg.isSemialgebraic
  refine ⟨hs, ?_⟩
  rw [hst, Set.graphOn_union, preimage_union]
  exact hhst.graph.union hhst'.graph

section PolynomialMap

/-- A function is semialgebraic on a semialgebraic domain `s` when its graph over `s` is cut out
by finitely many polynomial equations in the input and output coordinates: for `x ∈ s`, `f x = y`
exactly when every `p k` vanishes at `Sum.elim x y`. -/
theorem isSemialgebraicOn_of_forall_eq_iff {ι : Type*} [Finite ι] {f : (σ → R) → (τ → R)}
    {s : Set (σ → R)} (hs : IsSemialgebraic s) (p : ι → MvPolynomial (σ ⊕ τ) R)
    (hp : ∀ x ∈ s, ∀ y, f x = y ↔ ∀ k, eval (Sum.elim x y) (p k) = 0) :
    IsSemialgebraicOn f s := by
  refine isSemialgebraicOn_def.2 ⟨hs, ?_⟩
  convert (hs.preimage_comp Sum.inl).inter
    (IsSemialgebraic.iInter fun k ↦ isSemialgebraic_eval_eq_zero (p k)) using 1
  ext z
  rw [mem_preimage_sumArrowEquivProdArrow_graphOn]
  simp only [mem_inter_iff, mem_iInter, mem_preimage, mem_ofPred_eq]
  refine and_congr_right fun hz ↦ ?_
  rw [hp _ hz, Sum.elim_comp_inl_inr]

/-- A map whose output coordinates are polynomials in the input coordinates is semialgebraic on
every semialgebraic domain. -/
theorem isSemialgebraicOn_eval [Finite τ] (p : τ → MvPolynomial σ R)
    {s : Set (σ → R)} (hs : IsSemialgebraic s) :
    IsSemialgebraicOn (fun x i => eval x (p i)) s :=
  isSemialgebraicOn_of_forall_eq_iff hs (fun i => X (Sum.inr i) - rename Sum.inl (p i))
    fun x _ y => by simp [funext_iff, sub_eq_zero, eval_rename, eq_comm (a := y _)]

/-- A polynomial map between coordinate spaces is semialgebraic. -/
theorem isSemialgebraicMap_eval [Finite τ] (p : τ → MvPolynomial σ R) :
    IsSemialgebraicMap (fun x i => eval x (p i)) := by
  rw [← isSemialgebraicOn_univ]
  exact isSemialgebraicOn_eval p isSemialgebraic_univ

/-- Over a linearly ordered field, a coordinatewise rational map
`x ↦ (eval x (N i) / eval x (D i))` (with Lean's total division `a / 0 = 0`) into a
finite-dimensional coordinate space is semialgebraic on every semialgebraic domain. -/
theorem isSemialgebraicOn_eval_div {K : Type*} [Field K] [LinearOrder K] [Finite τ]
    (N D : τ → MvPolynomial σ K) {s : Set (σ → K)} (hs : IsSemialgebraic s) :
    IsSemialgebraicOn (fun x i ↦ eval x (N i) / eval x (D i)) s := by
  refine isSemialgebraicOn_def.2 ⟨hs, ?_⟩
  convert (hs.preimage_comp Sum.inl).inter
    (IsSemialgebraic.iInter fun i ↦
      ((isSemialgebraic_eval_eq_zero (rename Sum.inl (D i))).inter
        (isSemialgebraic_eval_eq_zero (X (Sum.inr i)))).union
      ((isSemialgebraic_eval_ne_zero (rename Sum.inl (D i))).inter
        (isSemialgebraic_eval_eq_zero
          (rename Sum.inl (D i) * X (Sum.inr i) - rename Sum.inl (N i))))) using 1
  ext z
  rw [mem_preimage_sumArrowEquivProdArrow_graphOn]
  simp only [mem_inter_iff, mem_preimage, mem_iInter, mem_union, mem_ofPred_eq, map_sub, map_mul,
    eval_rename, eval_X, Function.comp_apply, funext_iff, sub_eq_zero]
  refine and_congr_right fun _ ↦ forall_congr' fun i ↦ ?_
  by_cases hD : eval (z ∘ Sum.inl) (D i) = 0
  · simp [hD, eq_comm]
  · simp only [hD, false_and, true_and, false_or, ne_eq, not_false_eq_true]
    rw [div_eq_iff hD, mul_comm, eq_comm]

/-- Over a linearly ordered field, a coordinatewise rational map
`x ↦ (eval x (N i) / eval x (D i))` into a finite-dimensional coordinate space is semialgebraic. -/
theorem isSemialgebraicMap_eval_div {K : Type*} [Field K] [LinearOrder K] [Finite τ]
    (N D : τ → MvPolynomial σ K) :
    IsSemialgebraicMap (fun x i ↦ eval x (N i) / eval x (D i)) := by
  rw [← isSemialgebraicOn_univ]
  exact isSemialgebraicOn_eval_div N D isSemialgebraic_univ

/-- A constant map into a finite-dimensional coordinate space is semialgebraic on every
semialgebraic domain. -/
theorem isSemialgebraicOn_const [Finite τ] (c : τ → R) {s : Set (σ → R)}
    (hs : IsSemialgebraic s) : IsSemialgebraicOn (fun _ => c) s := by
  simpa using isSemialgebraicOn_eval (fun i : τ => C (c i)) hs

/-- A constant map into a finite-dimensional coordinate space is semialgebraic. -/
@[simp]
theorem isSemialgebraicMap_const [Finite τ] (c : τ → R) :
    IsSemialgebraicMap (fun _ : σ → R => c) := by
  rw [← isSemialgebraicOn_univ]
  exact isSemialgebraicOn_const c isSemialgebraic_univ

/-- The identity map on a finite-dimensional coordinate space is semialgebraic. -/
@[simp]
theorem isSemialgebraicMap_id [Finite σ] :
    IsSemialgebraicMap (id : (σ → R) → (σ → R)) := by
  rw [← isSemialgebraicOn_univ]
  apply IsSemialgebraicOn.congr <|
    (isSemialgebraicMap_eval (R := R) (σ := σ) (τ := σ) (fun i : σ => X i)).isSemialgebraicOn
      isSemialgebraic_univ
  intro x _
  funext i
  simp

end PolynomialMap

section AffineMap

/-- An affine map between finite-dimensional coordinate spaces is semialgebraic on every
semialgebraic domain. -/
theorem _root_.AffineMap.isSemialgebraicOn [Finite σ] [Finite τ] (A : (σ → R) →ᵃ[R] (τ → R))
    {s : Set (σ → R)} (hs : IsSemialgebraic s) : IsSemialgebraicOn A s := by
  obtain ⟨p, hp⟩ := A.exists_mvPolynomial_eval_eq
  exact (isSemialgebraicOn_eval p hs).congr fun x _ => (hp x).symm

/-- An affine map between finite-dimensional coordinate spaces is semialgebraic. -/
theorem _root_.AffineMap.isSemialgebraicMap [Finite σ] [Finite τ] (A : (σ → R) →ᵃ[R] (τ → R)) :
    IsSemialgebraicMap A :=
  isSemialgebraicOn_univ.1 (A.isSemialgebraicOn isSemialgebraic_univ)

/-- The inverse image of a semialgebraic set under an affine map out of a finite-dimensional
coordinate space is semialgebraic, without assuming projection closure. -/
theorem IsSemialgebraic.preimage_affineMap [Finite σ] {s : Set (τ → R)}
    (hs : IsSemialgebraic s) (A : (σ → R) →ᵃ[R] (τ → R)) :
    IsSemialgebraic (A ⁻¹' s) := by
  obtain ⟨p, hp⟩ := A.exists_mvPolynomial_eval_eq
  have hfun : (A : (σ → R) → τ → R) = fun x i => eval x (p i) := funext hp
  rw [hfun]
  exact hs.preimage_eval p

/-- Strict scalar affine positivity conditions on `σ → R` (`Finite σ`) cut out semialgebraic open
half-spaces. -/
theorem _root_.AffineMap.isSemialgebraic_pos [Finite σ] (f : (σ → R) →ᵃ[R] R) :
    IsSemialgebraic {x : σ → R | 0 < f x} := by
  simpa using (isSemialgebraic_eval_pos (X () : MvPolynomial Unit R)).preimage_affineMap
    ((LinearEquiv.funUnique Unit R R).symm.toAffineEquiv.toAffineMap.comp f)

end AffineMap

section Operations

variable {σ' τ' : Type*}

/-- Pairing two semialgebraic functions on the same domain gives a semialgebraic function into
the coordinate space indexed by the disjoint union of their output coordinates.  No projection is
needed: the graph of the pair is the intersection of the inverse images of the two graphs. -/
theorem IsSemialgebraicOn.sumElim {f : (σ → R) → (τ → R)} {g : (σ → R) → (τ' → R)}
    {s : Set (σ → R)} (hf : IsSemialgebraicOn f s) (hg : IsSemialgebraicOn g s) :
    IsSemialgebraicOn (fun x => Sum.elim (f x) (g x)) s := by
  refine ⟨hf.isSemialgebraic, ?_⟩
  convert (hf.graph.preimage_comp (Sum.elim Sum.inl (Sum.inr ∘ Sum.inl))).inter
    (hg.graph.preimage_comp (Sum.elim Sum.inl (Sum.inr ∘ Sum.inr))) using 1
  ext z
  simp only [mem_inter_iff, mem_preimage_sumArrowEquivProdArrow_graphOn,
    mem_preimage (f := fun x : σ ⊕ τ ⊕ τ' → R => x ∘ Sum.elim Sum.inl (Sum.inr ∘ Sum.inl)),
    mem_preimage (f := fun x : σ ⊕ τ ⊕ τ' → R => x ∘ Sum.elim Sum.inl (Sum.inr ∘ Sum.inr)),
    Function.comp_assoc, Sum.elim_comp_inl, Sum.elim_comp_inr]
  rw [← Sum.elim_comp_inl_inr (z ∘ Sum.inr), Sum.elim_eq_iff]
  tauto

/-- Pairing two semialgebraic maps gives a semialgebraic map. -/
theorem IsSemialgebraicMap.sumElim {f : (σ → R) → (τ → R)} {g : (σ → R) → (τ' → R)}
    (hf : IsSemialgebraicMap f) (hg : IsSemialgebraicMap g) :
    IsSemialgebraicMap fun x => Sum.elim (f x) (g x) :=
  isSemialgebraicOn_univ.1 <| (isSemialgebraicOn_univ.2 hf).sumElim (isSemialgebraicOn_univ.2 hg)

/-- A function with finitely many output coordinates is semialgebraic on a semialgebraic domain if
each of its coordinates is.  No projection is needed: the graph is the intersection of the inverse
images of the graphs of the coordinates. -/
theorem IsSemialgebraicOn.pi [Finite τ] {f : (σ → R) → (τ → R)} {s : Set (σ → R)}
    (hs : IsSemialgebraic s) (hf : ∀ i, IsSemialgebraicOn (fun x (_ : Unit) => f x i) s) :
    IsSemialgebraicOn f s := by
  refine ⟨hs, ?_⟩
  convert (hs.preimage_comp Sum.inl).inter
    (.iInter fun i => (hf i).graph.preimage_comp (Sum.elim Sum.inl fun _ => Sum.inr i)) using 1
  ext z
  simp only [mem_inter_iff, mem_iInter, mem_preimage_sumArrowEquivProdArrow_graphOn,
    mem_preimage (f := fun x : σ ⊕ τ → R => x ∘ Sum.inl),
    mem_preimage (f := fun x : σ ⊕ τ → R => x ∘ Sum.elim Sum.inl fun _ => Sum.inr _),
    Function.comp_assoc, Sum.elim_comp_inl, Function.comp_apply, Sum.elim_inr, funext_iff,
    forall_const]
  exact and_congr_right fun hz => by simp [hz]

/-- Precomposing a semialgebraic function with a polynomial map gives a semialgebraic function on
the inverse image of its domain.  No projection is needed: the new graph is the inverse image of
the old one under a polynomial map. -/
theorem IsSemialgebraicOn.comp_eval {f : (σ → R) → (τ → R)} {s : Set (σ → R)}
    (hf : IsSemialgebraicOn f s) (p : σ → MvPolynomial σ' R) :
    IsSemialgebraicOn (f ∘ fun x i => eval x (p i)) ((fun x i => eval x (p i)) ⁻¹' s) := by
  refine ⟨hf.isSemialgebraic.preimage_eval p, ?_⟩
  convert hf.graph.preimage_eval (Sum.elim (fun i => rename Sum.inl (p i)) fun j => X (Sum.inr j))
    using 1
  ext z
  simp only [mem_preimage_sumArrowEquivProdArrow_graphOn,
    mem_preimage (f := fun (x : σ' ⊕ τ → R) (_ : σ ⊕ τ) => eval x _), Function.comp_def,
    Sum.elim_inl, Sum.elim_inr, eval_rename, eval_X]
  simp only [mem_preimage]

/-- Precomposing a semialgebraic map with a polynomial map gives a semialgebraic map. -/
theorem IsSemialgebraicMap.comp_eval {f : (σ → R) → (τ → R)} (hf : IsSemialgebraicMap f)
    (p : σ → MvPolynomial σ' R) : IsSemialgebraicMap (f ∘ fun x i => eval x (p i)) := by
  simpa using (isSemialgebraicOn_univ.2 hf).comp_eval p

/-- The fiber of a semialgebraic function over a constant value `c` inside its domain is
semialgebraic. No projection is needed: the fiber is the inverse image of the graph under the
polynomial slice `x ↦ (x, c)`. -/
theorem IsSemialgebraicOn.isSemialgebraic_inter_setOf_eq_const {f : (σ → R) → (τ → R)}
    {s : Set (σ → R)} (hf : IsSemialgebraicOn f s) (c : τ → R) :
    IsSemialgebraic (s ∩ {x | f x = c}) := by
  convert hf.graph.preimage_eval (Sum.elim X fun j ↦ C (c j)) using 1
  ext x
  rw [mem_inter_iff, mem_preimage, mem_preimage_sumArrowEquivProdArrow_graphOn]
  simp only [Function.comp_def, Sum.elim_inl, Sum.elim_inr, eval_X, eval_C]
  rfl

/-- The complement of a constant fiber of a semialgebraic function inside its domain is
semialgebraic. -/
theorem IsSemialgebraicOn.isSemialgebraic_inter_setOf_ne_const {f : (σ → R) → (τ → R)}
    {s : Set (σ → R)} (hf : IsSemialgebraicOn f s) (c : τ → R) :
    IsSemialgebraic (s ∩ {x | f x ≠ c}) := by
  convert hf.isSemialgebraic.sdiff (hf.isSemialgebraic_inter_setOf_eq_const c) using 1
  ext x
  simp only [mem_inter_iff, mem_ofPred_eq, mem_sdiff]
  tauto

/-- The pointwise negation of a semialgebraic function is semialgebraic.  No projection is needed:
the new graph is the inverse image of the old one under negation of the output coordinates. -/
theorem IsSemialgebraicOn.neg {f : (σ → R) → (τ → R)} {s : Set (σ → R)}
    (hf : IsSemialgebraicOn f s) : IsSemialgebraicOn (-f) s := by
  refine ⟨hf.isSemialgebraic, ?_⟩
  convert hf.graph.preimage_eval (Sum.elim (fun i => X (Sum.inl i)) fun j => -X (Sum.inr j))
    using 1
  ext z
  simp only [mem_preimage_sumArrowEquivProdArrow_graphOn,
    mem_preimage (f := fun (x : σ ⊕ τ → R) (_ : σ ⊕ τ) => eval x _), Function.comp_def,
    Sum.elim_inl, Sum.elim_inr, eval_X, map_neg]
  rw [Pi.neg_apply, neg_eq_iff_eq_neg]
  rfl

/-- The pointwise negation of a semialgebraic map is semialgebraic. -/
theorem IsSemialgebraicMap.neg {f : (σ → R) → (τ → R)} (hf : IsSemialgebraicMap f) :
    IsSemialgebraicMap (-f) :=
  isSemialgebraicOn_univ.1 (isSemialgebraicOn_univ.2 hf).neg

/-- Semialgebraicity of a function is invariant under a bijective change of input coordinates,
such as a permutation, applied to both the function and its domain. -/
@[simp]
theorem isSemialgebraicOn_preimage_comp_equiv_iff {f : (σ → R) → (τ → R)} {s : Set (σ → R)}
    (e : σ ≃ σ') :
    IsSemialgebraicOn (fun x : σ' → R => f (x ∘ e)) ((fun x : σ' → R => x ∘ e) ⁻¹' s) ↔
      IsSemialgebraicOn f s := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · simpa [Function.comp_def, preimage_preimage] using h.comp_eval fun i => X (e.symm i)
  · simpa [Function.comp_def] using h.comp_eval fun i => X (e i)

/-- Changing the output coordinates of a semialgebraic function by a bijection preserves
semialgebraicity. -/
private theorem IsSemialgebraicOn.comp_equiv {f : (σ → R) → (τ → R)} {s : Set (σ → R)}
    (hf : IsSemialgebraicOn f s) (e : τ' ≃ τ) : IsSemialgebraicOn (fun x => f x ∘ e) s := by
  refine ⟨hf.isSemialgebraic, ?_⟩
  convert hf.graph.preimage_comp (Sum.elim Sum.inl (Sum.inr ∘ e.symm)) using 1
  ext z
  simp only [mem_preimage_sumArrowEquivProdArrow_graphOn,
    mem_preimage (f := fun x : σ ⊕ τ' → R => x ∘ Sum.elim Sum.inl (Sum.inr ∘ e.symm)),
    Function.comp_assoc, Sum.elim_comp_inl, Sum.elim_comp_inr]
  rw [← Function.comp_assoc z Sum.inr, Equiv.eq_comp_symm]

/-- Semialgebraicity of a function is invariant under a bijective change of output coordinates,
such as a permutation. -/
@[simp]
theorem isSemialgebraicOn_comp_equiv_iff {f : (σ → R) → (τ → R)} {s : Set (σ → R)}
    (e : τ' ≃ τ) :
    IsSemialgebraicOn (fun x => f x ∘ e) s ↔ IsSemialgebraicOn f s := by
  refine ⟨fun h => ?_, fun h => h.comp_equiv e⟩
  simpa [Function.comp_assoc] using h.comp_equiv e.symm

end Operations

section Reciprocal

/-- Over a linearly ordered field, the coordinatewise reciprocal map `x ↦ x⁻¹` (with `0⁻¹ = 0`) is
semialgebraic on every semialgebraic domain. No projection closure or nonvanishing hypothesis is
needed: it is the coordinatewise rational map `x ↦ 1 / x`. -/
theorem isSemialgebraicOn_inv {K : Type*} [Field K] [LinearOrder K] [Finite τ]
    {s : Set (τ → K)} (hs : IsSemialgebraic s) :
    IsSemialgebraicOn (Inv.inv : (τ → K) → (τ → K)) s :=
  (isSemialgebraicOn_eval_div (fun _ ↦ 1) X hs).congr fun x _ ↦ by ext i; simp [one_div]

/-- Over a linearly ordered field, the coordinatewise reciprocal map `x ↦ x⁻¹` (with `0⁻¹ = 0`) is
a semialgebraic map. -/
theorem isSemialgebraicMap_inv {K : Type*} [Field K] [LinearOrder K] [Finite τ] :
    IsSemialgebraicMap (Inv.inv : (τ → K) → (τ → K)) :=
  isSemialgebraicOn_univ.1 (isSemialgebraicOn_inv isSemialgebraic_univ)

end Reciprocal

end TauCeti
