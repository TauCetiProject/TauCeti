/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

-- The coordinates of a joint eigenvector against a diagonalizing basis.
public import TauCeti.LinearAlgebra.Eigenspace.DiagonalBasis
-- `TauCeti.weightSpace` and the independence of weight spaces; this module also re-exports
-- `TauCeti.diagGL` and the characters `TauCeti.weightChar` of the diagonal torus.
public import TauCeti.RepresentationTheory.ClassicalGroups.Weight.Basic

/-!
# Weight spaces read off a basis of weight vectors

A representation of `GL n k` that has a basis of weight vectors has no weights other than the ones
that basis exhibits, and no weight multiplicities other than the ones it counts.  This file proves
that, once and for all: given a basis `b : Module.Basis ι k W` together with an assignment
`wt : ι → Fin n → ℤ` making `b i` a vector of weight `wt i`, the weight spaces of `ρ` span `W`, the
weight-`wt i` space is the coordinate line `k ∙ b i`, and every other weight space vanishes.

This is the pattern every concrete computation of the weight spaces of a `GL n k`-representation
follows — the coordinate lines of the standard representation, the wedges of standard basis vectors
in an exterior power, the unordered tuples in a symmetric power — and the only thing that varies
between them is the basis and the combinatorial label `wt`.  Isolating it here keeps those
computations to the one step that is genuinely about the representation, namely that each basis
vector is a weight vector.

Two hypotheses recur and are not interchangeable.  The **separation hypothesis**
`Function.Injective (weightChar k)`, standing throughout the weight theory of
`TauCeti.RepresentationTheory.ClassicalGroups.Weight.Basic`, says that distinct weights give
distinct characters of the torus; `TauCeti.weightChar_injective` supplies it over an infinite
field, and without it every weight space of every representation is everything over `𝔽₂`.  The
**injectivity of the labelling** `Function.Injective wt` is a separate, combinatorial condition: it
says the basis vectors have pairwise distinct weights, which is what makes each weight space a
single line rather than a larger coordinate subspace.  The spanning statement needs neither, and
the vanishing statement needs only the first.

## Main results

* `TauCeti.iSup_weightSpace_eq_top_of_basis`: **a representation with a basis of weight vectors is
  spanned by its weight spaces.**
* `TauCeti.repr_eq_zero_of_mem_weightSpace_of_basis`: a weight vector has no coordinate on a basis
  vector of a different weight.
* `TauCeti.weightSpace_eq_span_of_basis`: **the weight spaces are the coordinate lines of the
  basis**, when the labelling is injective.
* `TauCeti.weightSpace_eq_bot_of_basis` and `TauCeti.weightSpace_ne_bot_iff_of_basis`: the weights
  are exactly the labels `wt i`.
* `TauCeti.isInternal_weightSpace_of_basis`: **a representation with a basis of weight vectors is
  the internal direct sum of its weight spaces.**
* `TauCeti.finrank_weightSpace_eq_one_of_basis`: each such weight has multiplicity one.

## References

* [Classical groups roadmap](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/RepresentationTheory/ClassicalGroups/README.md),
  Layer 3, "The maximal torus and weight spaces".
* W. Fulton and J. Harris, *Representation Theory: A First Course* (1991), Lecture 15.
-/

public section

open Matrix

universe u v w

namespace TauCeti

section CommRing

variable {k : Type u} [CommRing k] {n : ℕ} {ι : Type v}
variable {W : Type w} [AddCommGroup W] [Module k W]
variable {ρ : Representation k (GL (Fin n) k) W} {wt : ι → Fin n → ℤ}

/-- **A representation with a basis of weight vectors is spanned by its weight spaces.**  Each
basis vector lies in one of them, and the basis spans. -/
theorem iSup_weightSpace_eq_top_of_basis (b : Module.Basis ι k W)
    (hb : ∀ i, b i ∈ weightSpace ρ (wt i)) :
    ⨆ l : Fin n → ℤ, weightSpace ρ l = ⊤ := by
  refine top_le_iff.mp ?_
  rw [← b.span_eq, Submodule.span_le]
  rintro _ ⟨i, rfl⟩
  exact le_iSup (fun l : Fin n → ℤ => weightSpace ρ l) (wt i) (hb i)

end CommRing

/-! ### Pinning the weight spaces down

Here the coefficients must separate weights, in the sense that `l ↦ weightChar k l` is injective;
`TauCeti.weightChar_injective` supplies that over an infinite field. -/

section Domain

variable {k : Type u} [CommRing k] [IsDomain k] {n : ℕ} {ι : Type v}
variable {W : Type w} [AddCommGroup W] [Module k W]
variable {ρ : Representation k (GL (Fin n) k) W} {wt : ι → Fin n → ℤ}

/-- **A weight vector has no coordinate on a basis vector of a different weight.**  The torus acts
on the coordinate of index `i` through the character of `wt i` and on the whole vector through the
character of its own weight, so a nonzero coordinate would equate the two characters. -/
theorem repr_eq_zero_of_mem_weightSpace_of_basis (b : Module.Basis ι k W)
    (hb : ∀ i, b i ∈ weightSpace ρ (wt i))
    (hchar : Function.Injective (weightChar k (κ := Fin n))) {l : Fin n → ℤ} {w : W}
    (hw : w ∈ weightSpace ρ l) {i : ι} (hi : wt i ≠ l) : b.repr w i = 0 :=
  b.repr_eq_zero_of_weight_ne (f := fun t : Fin n → kˣ => ρ (diagGL t))
    (a := fun (j : ι) (t : Fin n → kˣ) => ((weightChar k (wt j) t : kˣ) : k))
    (fun j t => apply_of_mem_weightSpace (hb j) t) (apply_of_mem_weightSpace hw)
    fun heq => hi (hchar (MonoidHom.ext fun t => Units.ext (congrFun heq t)))

/-- **The weight spaces of a representation with a basis of weight vectors are the coordinate lines
of that basis.**  The labelling must be injective: two basis vectors of the same weight span a
plane inside a single weight space. -/
theorem weightSpace_eq_span_of_basis (b : Module.Basis ι k W)
    (hb : ∀ i, b i ∈ weightSpace ρ (wt i))
    (hchar : Function.Injective (weightChar k (κ := Fin n))) (hwt : Function.Injective wt)
    (i : ι) : weightSpace ρ (wt i) = Submodule.span k {b i} := by
  refine le_antisymm (fun w hw => ?_) ?_
  · have hrepr : b.repr w = Finsupp.single i (b.repr w i) := by
      ext j
      by_cases h : j = i
      · rw [h, Finsupp.single_eq_same]
      · rw [Finsupp.single_eq_of_ne h]
        exact repr_eq_zero_of_mem_weightSpace_of_basis b hb hchar hw fun hcon => h (hwt hcon)
    rw [Submodule.mem_span_singleton]
    refine ⟨b.repr w i, ?_⟩
    conv_rhs => rw [← b.repr.symm_apply_apply w, hrepr]
    rw [Module.Basis.repr_symm_single]
  · rw [Submodule.span_le, Set.singleton_subset_iff]
    exact hb i

/-- **Only the labels are weights**: a weight carried by no basis vector has no weight vector at
all. -/
theorem weightSpace_eq_bot_of_basis (b : Module.Basis ι k W)
    (hb : ∀ i, b i ∈ weightSpace ρ (wt i))
    (hchar : Function.Injective (weightChar k (κ := Fin n))) {l : Fin n → ℤ}
    (hl : ∀ i, l ≠ wt i) : weightSpace ρ l = ⊥ := by
  refine (Submodule.eq_bot_iff _).mpr fun w hw => ?_
  refine (Module.Basis.forall_coord_eq_zero_iff b).mp fun i => ?_
  rw [Module.Basis.coord_apply]
  exact repr_eq_zero_of_mem_weightSpace_of_basis b hb hchar hw fun hcon => hl i hcon.symm

/-- **The weights of a representation with a basis of weight vectors are exactly the labels of that
basis.** -/
theorem weightSpace_ne_bot_iff_of_basis (b : Module.Basis ι k W)
    (hb : ∀ i, b i ∈ weightSpace ρ (wt i))
    (hchar : Function.Injective (weightChar k (κ := Fin n))) (hwt : Function.Injective wt)
    (l : Fin n → ℤ) : weightSpace ρ l ≠ ⊥ ↔ ∃ i, l = wt i := by
  refine ⟨fun h => ?_, ?_⟩
  · by_contra hcon
    exact h (weightSpace_eq_bot_of_basis b hb hchar (by simpa using hcon))
  · rintro ⟨i, rfl⟩
    rw [weightSpace_eq_span_of_basis b hb hchar hwt i, Ne, Submodule.span_singleton_eq_bot]
    exact b.ne_zero i

end Domain

section Field

variable {k : Type u} [Field k] {n : ℕ} {ι : Type v}
variable {W : Type w} [AddCommGroup W] [Module k W]
variable {ρ : Representation k (GL (Fin n) k) W} {wt : ι → Fin n → ℤ}

/-- **A representation with a basis of weight vectors is the internal direct sum of its weight
spaces.** -/
theorem isInternal_weightSpace_of_basis (b : Module.Basis ι k W)
    (hb : ∀ i, b i ∈ weightSpace ρ (wt i))
    (hchar : Function.Injective (weightChar k (κ := Fin n))) :
    DirectSum.IsInternal fun l : Fin n → ℤ => weightSpace ρ l :=
  isInternal_weightSpace_of_iSup_eq_top hchar (iSup_weightSpace_eq_top_of_basis b hb)

/-- **Distinctly labelled basis weights have multiplicity one.** -/
theorem finrank_weightSpace_eq_one_of_basis (b : Module.Basis ι k W)
    (hb : ∀ i, b i ∈ weightSpace ρ (wt i))
    (hchar : Function.Injective (weightChar k (κ := Fin n))) (hwt : Function.Injective wt)
    (i : ι) : Module.finrank k (weightSpace ρ (wt i)) = 1 := by
  rw [weightSpace_eq_span_of_basis b hb hchar hwt i]
  exact finrank_span_singleton (b.ne_zero i)

end Field

end TauCeti
