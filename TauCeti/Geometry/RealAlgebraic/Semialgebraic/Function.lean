/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.RealAlgebraic.Semialgebraic.Basic

/-!
# Semialgebraic functions

A function between coordinate spaces is semialgebraic on a set when its domain and graph are
semialgebraic.  The graph is regarded as a subset of the coordinate space indexed by the disjoint
union of the input and output coordinates.  Requiring the specified domain to be semialgebraic is
useful before projection closure is available: semialgebraicity of a graph alone does not yet let
us recover its projection onto the input coordinates.

This file gives the graph predicate its basic API.  It proves restriction, congruence, and
piecewise-gluing laws and shows that polynomial maps are semialgebraic.  It deliberately does not
assert closure under arbitrary composition, whose graph generally requires eliminating the
intermediate coordinates.

## References

S. Basu, R. Pollack, and M.-F. Roy,
[Algorithms in Real Algebraic Geometry](https://doi.org/10.1007/3-540-33099-2),
second edition, Chapter 2.
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
  have hs : IsSemialgebraic s := by
    rw [show s = (s ∩ t) ∪ (s \ t) by ext; simp]
    exact hf.isSemialgebraic.union hg.isSemialgebraic
  refine ⟨hs, ?_⟩
  have hgraph : Equiv.sumArrowEquivProdArrow σ τ R ⁻¹' s.graphOn h =
      (Equiv.sumArrowEquivProdArrow σ τ R ⁻¹' (s ∩ t).graphOn h) ∪
        (Equiv.sumArrowEquivProdArrow σ τ R ⁻¹' (s \ t).graphOn h) := by
    ext z
    have hfst : (Equiv.sumArrowEquivProdArrow σ τ R z).1 = z ∘ Sum.inl := by
      funext i
      exact Equiv.sumArrowEquivProdArrow_apply_fst z i
    simp only [mem_preimage, mem_graphOn, mem_union, mem_inter_iff, mem_sdiff, hfst]
    by_cases hz : z ∘ Sum.inl ∈ t <;> simp [hz]
  rw [hgraph]
  exact hhst.graph.union hhst'.graph

section PolynomialMap

/-- A map whose output coordinates are polynomials in the input coordinates is semialgebraic on
every semialgebraic domain. -/
theorem isSemialgebraicOn_eval [Finite τ] (p : τ → MvPolynomial σ R)
    {s : Set (σ → R)} (hs : IsSemialgebraic s) :
    IsSemialgebraicOn (fun x i => eval x (p i)) s := by
  refine ⟨hs, ?_⟩
  have hgraph : Equiv.sumArrowEquivProdArrow σ τ R ⁻¹'
      s.graphOn (fun x i => eval x (p i)) =
      ((fun z : σ ⊕ τ → R => z ∘ Sum.inl) ⁻¹' s) ∩
        ⋂ i, {z | eval z (X (Sum.inr i) - rename Sum.inl (p i)) = 0} := by
    ext z
    have hfst : (Equiv.sumArrowEquivProdArrow σ τ R z).1 = z ∘ Sum.inl := by
      funext i
      exact Equiv.sumArrowEquivProdArrow_apply_fst z i
    have hsnd : (Equiv.sumArrowEquivProdArrow σ τ R z).2 = z ∘ Sum.inr := by
      funext i
      exact Equiv.sumArrowEquivProdArrow_apply_snd z i
    simp only [mem_preimage, mem_graphOn, mem_inter_iff, mem_iInter, mem_ofPred_eq, hfst, hsnd]
    constructor
    · rintro ⟨hz, hp⟩
      refine ⟨hz, fun i => ?_⟩
      simpa [sub_eq_zero, MvPolynomial.eval_rename] using (congrFun hp i).symm
    · rintro ⟨hz, hp⟩
      refine ⟨hz, funext fun i => ?_⟩
      have hi := hp i
      have hi' : z (Sum.inr i) = eval (z ∘ Sum.inl) (p i) := by
        simpa [sub_eq_zero, MvPolynomial.eval_rename] using hi
      exact hi'.symm
  rw [hgraph]
  exact (hs.preimage_comp Sum.inl).inter <|
    .iInter fun i => isSemialgebraic_eval_eq_zero (X (Sum.inr i) - rename Sum.inl (p i))

/-- A polynomial map between coordinate spaces is semialgebraic. -/
theorem isSemialgebraicMap_eval [Finite τ] (p : τ → MvPolynomial σ R) :
    IsSemialgebraicMap (fun x i => eval x (p i)) :=
  isSemialgebraicOn_eval p isSemialgebraic_univ

/-- A constant map into a finite-dimensional coordinate space is semialgebraic on every
semialgebraic domain. -/
theorem isSemialgebraicOn_const [Finite τ] (c : τ → R) {s : Set (σ → R)}
    (hs : IsSemialgebraic s) : IsSemialgebraicOn (fun _ => c) s := by
  simpa using isSemialgebraicOn_eval (fun i : τ => C (c i)) hs

/-- A constant map into a finite-dimensional coordinate space is semialgebraic. -/
@[simp]
theorem isSemialgebraicMap_const [Finite τ] (c : τ → R) :
    IsSemialgebraicMap (fun _ : σ → R => c) :=
  isSemialgebraicOn_const c isSemialgebraic_univ

/-- The identity map on a finite-dimensional coordinate space is semialgebraic. -/
@[simp]
theorem isSemialgebraicMap_id [Finite σ] :
    IsSemialgebraicMap (id : (σ → R) → (σ → R)) := by
  apply IsSemialgebraicOn.congr <|
    isSemialgebraicMap_eval (R := R) (σ := σ) (τ := σ) (fun i : σ => X i)
  intro x _
  funext i
  simp

end PolynomialMap

end TauCeti
