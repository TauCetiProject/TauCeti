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
weight-`l` space is spanned by the basis vectors labelled `l`, and every weight space carrying no
label at all vanishes.  When the labelling is injective that coordinate subspace is the single
line `k ∙ b i` on the one basis vector labelled `l = wt i`; without injectivity it is not, two
basis vectors of the same weight spanning a plane inside one weight space.

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
single line rather than a larger coordinate subspace.  The spanning statement needs neither; the
vanishing statement, and with it the description of which weights occur at all, needs only the
first.

## Main results

* `Module.Basis.iSup_weightSpace_eq_top`: **a representation with a basis of weight vectors is
  spanned by its weight spaces.**
* `Module.Basis.repr_eq_zero_of_mem_weightSpace`: a weight vector has no coordinate on a basis
  vector of a different weight.
* `Module.Basis.weightSpace_eq_span_image`: **the weight spaces are the coordinate subspaces of the
  basis**, the weight-`l` space being spanned by the basis vectors labelled `l`;
  `Module.Basis.weightSpace_eq_span` reads that as a single line when the labelling is injective.
* `Module.Basis.weightSpace_eq_bot` and `Module.Basis.weightSpace_ne_bot_iff`: the weights are
  exactly the labels `wt i`.
* `Module.Basis.isInternal_weightSpace`: **a representation with a basis of weight vectors is the
  internal direct sum of its weight spaces.**
* `Module.Basis.finrank_weightSpace_eq_one`: each distinctly labelled weight has multiplicity one.

These are stated in the `Module.Basis` namespace, so that they read as `b.weightSpace_eq_span` on a
basis `b`, like the coordinate lemmas of `TauCeti/LinearAlgebra/Eigenspace/DiagonalBasis.lean` they
are built on.

## References

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
theorem _root_.Module.Basis.iSup_weightSpace_eq_top (b : Module.Basis ι k W)
    (hb : ∀ i, b i ∈ weightSpace ρ (wt i)) :
    ⨆ l : Fin n → ℤ, weightSpace ρ l = ⊤ := by
  refine top_le_iff.mp ?_
  rw [← b.span_eq, Submodule.span_le]
  rintro _ ⟨i, rfl⟩
  exact le_iSup (fun l : Fin n → ℤ => weightSpace ρ l) (wt i) (hb i)

end CommRing

/-! ### Pinning the weight spaces down

Here the coefficients must separate weights, in the sense that `l ↦ weightChar k l` is injective;
`TauCeti.weightChar_injective` supplies that over an infinite field.  Only cancellation of nonzero
factors is needed of the ring itself: the argument compares two eigenvalues on a single nonzero
coordinate. -/

section IsCancelMulZero

variable {k : Type u} [CommRing k] [IsCancelMulZero k] {n : ℕ} {ι : Type v}
variable {W : Type w} [AddCommGroup W] [Module k W]
variable {ρ : Representation k (GL (Fin n) k) W} {wt : ι → Fin n → ℤ}

/-- **A weight vector has no coordinate on a basis vector of a different weight.**  The torus acts
on the coordinate of index `i` through the character of `wt i` and on the whole vector through the
character of its own weight, so a nonzero coordinate would equate the two characters. -/
theorem _root_.Module.Basis.repr_eq_zero_of_mem_weightSpace (b : Module.Basis ι k W)
    (hb : ∀ i, b i ∈ weightSpace ρ (wt i))
    (hchar : Function.Injective (weightChar k (κ := Fin n))) {l : Fin n → ℤ} {w : W}
    (hw : w ∈ weightSpace ρ l) {i : ι} (hi : wt i ≠ l) : b.repr w i = 0 :=
  b.repr_eq_zero_of_weight_ne (f := fun t : Fin n → kˣ => ρ (diagGL t))
    (a := fun (j : ι) (t : Fin n → kˣ) => ((weightChar k (wt j) t : kˣ) : k))
    (fun j t => apply_of_mem_weightSpace (hb j) t) (apply_of_mem_weightSpace hw)
    fun heq => hi (hchar (MonoidHom.ext fun t => Units.ext (congrFun heq t)))

/-- **The weight spaces of a representation with a basis of weight vectors are the coordinate
subspaces of that basis**: the weight-`l` space is spanned by the basis vectors labelled `l`.  No
injectivity of the labelling is needed; with it the span collapses to a single line, which is
`Module.Basis.weightSpace_eq_span`. -/
theorem _root_.Module.Basis.weightSpace_eq_span_image (b : Module.Basis ι k W)
    (hb : ∀ i, b i ∈ weightSpace ρ (wt i))
    (hchar : Function.Injective (weightChar k (κ := Fin n))) (l : Fin n → ℤ) :
    weightSpace ρ l = Submodule.span k (b '' {i | wt i = l}) := by
  refine le_antisymm (fun w hw => ?_) (Submodule.span_le.mpr ?_)
  · refine b.mem_span_image.mpr fun i hi => ?_
    by_contra hne
    exact Finsupp.mem_support_iff.mp hi (b.repr_eq_zero_of_mem_weightSpace hb hchar hw hne)
  · rintro _ ⟨i, hi, rfl⟩
    exact hi ▸ hb i

/-- **The weight spaces of a representation with a basis of weight vectors are the coordinate lines
of that basis.**  The labelling must be injective: two basis vectors of the same weight span a
plane inside a single weight space. -/
theorem _root_.Module.Basis.weightSpace_eq_span (b : Module.Basis ι k W)
    (hb : ∀ i, b i ∈ weightSpace ρ (wt i))
    (hchar : Function.Injective (weightChar k (κ := Fin n))) (hwt : Function.Injective wt)
    (i : ι) : weightSpace ρ (wt i) = Submodule.span k {b i} := by
  have hfib : {j | wt j = wt i} = ({i} : Set ι) :=
    Set.eq_singleton_iff_unique_mem.mpr ⟨rfl, fun _ hj => hwt hj⟩
  rw [b.weightSpace_eq_span_image hb hchar (wt i), hfib, Set.image_singleton]

/-- **Only the labels are weights**: a weight carried by no basis vector has no weight vector at
all. -/
theorem _root_.Module.Basis.weightSpace_eq_bot (b : Module.Basis ι k W)
    (hb : ∀ i, b i ∈ weightSpace ρ (wt i))
    (hchar : Function.Injective (weightChar k (κ := Fin n))) {l : Fin n → ℤ}
    (hl : ∀ i, l ≠ wt i) : weightSpace ρ l = ⊥ := by
  have hfib : {i | wt i = l} = (∅ : Set ι) :=
    Set.eq_empty_iff_forall_notMem.mpr fun i hi => hl i hi.symm
  rw [b.weightSpace_eq_span_image hb hchar l, hfib, Set.image_empty, Submodule.span_empty]

/-- **The weights of a representation with a basis of weight vectors are exactly the labels of that
basis.**  The labelling need not be injective here: a label occurring at all already makes its
weight space nonzero, since it contains a nonzero basis vector. -/
theorem _root_.Module.Basis.weightSpace_ne_bot_iff [Nontrivial k] (b : Module.Basis ι k W)
    (hb : ∀ i, b i ∈ weightSpace ρ (wt i))
    (hchar : Function.Injective (weightChar k (κ := Fin n)))
    (l : Fin n → ℤ) : weightSpace ρ l ≠ ⊥ ↔ ∃ i, l = wt i := by
  refine ⟨fun h => ?_, ?_⟩
  · by_contra hcon
    exact h (b.weightSpace_eq_bot hb hchar (by simpa using hcon))
  · rintro ⟨i, rfl⟩
    exact fun hbot => b.ne_zero i ((Submodule.eq_bot_iff _).mp hbot _ (hb i))

end IsCancelMulZero

section Field

variable {k : Type u} [Field k] {n : ℕ} {ι : Type v}
variable {W : Type w} [AddCommGroup W] [Module k W]
variable {ρ : Representation k (GL (Fin n) k) W} {wt : ι → Fin n → ℤ}

/-- **A representation with a basis of weight vectors is the internal direct sum of its weight
spaces.** -/
theorem _root_.Module.Basis.isInternal_weightSpace (b : Module.Basis ι k W)
    (hb : ∀ i, b i ∈ weightSpace ρ (wt i))
    (hchar : Function.Injective (weightChar k (κ := Fin n))) :
    DirectSum.IsInternal fun l : Fin n → ℤ => weightSpace ρ l :=
  isInternal_weightSpace_of_iSup_eq_top hchar (b.iSup_weightSpace_eq_top hb)

/-- **Distinctly labelled basis weights have multiplicity one.** -/
theorem _root_.Module.Basis.finrank_weightSpace_eq_one (b : Module.Basis ι k W)
    (hb : ∀ i, b i ∈ weightSpace ρ (wt i))
    (hchar : Function.Injective (weightChar k (κ := Fin n))) (hwt : Function.Injective wt)
    (i : ι) : Module.finrank k (weightSpace ρ (wt i)) = 1 := by
  rw [b.weightSpace_eq_span hb hchar hwt i]
  exact finrank_span_singleton (b.ne_zero i)

end Field

end TauCeti
