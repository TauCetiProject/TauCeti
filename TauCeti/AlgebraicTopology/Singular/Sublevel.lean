/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Singular.Empty
public import TauCeti.AlgebraicTopology.Singular.Triple.Finrank
public import TauCeti.Topology.Order.Sublevel

/-!
# Singular homology of a sublevel pair covering the whole space

Let `f : X → β` be any function to a preorder. If `a < f ≤ b` everywhere, the sublevel pair
`TauCeti.sublevelPair f : ({f ≤ b}, {f ≤ a})` is `(X, ∅)`, so its relative singular homology is
the singular homology of `X` (`TauCeti.singularHomologyIsoSublevelPair`). No continuity
or regularity of `f` is needed. Since the subspace is empty, the comparison is the quotient map
`TopPair.singularHomologyπ`, an isomorphism by `TauCeti.AlgebraicTopology.Singular.Empty`.

Consequently the homology of `X` is controlled by any finite filtration of `X` by sublevels. Let
`s 0 ≤ s 1 ≤ ⋯ ≤ s (N + 1)` with `s 0 < f ≤ s (N + 1)` everywhere, let `V` be a module over a
division ring `k`, and suppose that every step `Hᵢ({f ≤ s (j + 1)}, {f ≤ s j}; V)` is
finite-dimensional. Write `bᵢ = dim Hᵢ(X; V)` and `cᵢ = ∑ⱼ dim Hᵢ({f ≤ s (j + 1)}, {f ≤ s j}; V)`.
Then `b` and `c` satisfy the Morse inequalities: `bᵢ ≤ cᵢ`
(`TauCeti.finrank_singularHomology_le_sum_sublevelPair`),
`bₙ - bₙ₋₁ + ⋯ ± b₀ ≤ cₙ - cₙ₋₁ + ⋯ ± c₀`
(`TauCeti.sum_range_neg_one_pow_mul_finrank_singularHomology_le_sum_sublevelPair`), Euler's
equality and the polynomial identity `∑ᵢ₌₀ⁿ cᵢ tⁱ = ∑ᵢ₌₀ⁿ bᵢ tⁱ + (1 + t) Q(t)`, with `Q` having
natural number coefficients, when no step has homology in degree `n + 1`
(`TauCeti.sum_range_neg_one_pow_mul_finrank_singularHomology_eq_sum_sublevelPair` and
`TauCeti.exists_sum_range_monomial_sum_sublevelPair_eq_add_mul`), and the
lacunary principle `b = c` when of any two consecutive `cᵢ` one vanishes
(`TauCeti.finrank_singularHomology_eq_sum_sublevelPair`). These are the filtration statements of
`TauCeti.AlgebraicTopology.Singular.Triple.Finrank` for the sublevels, read through the
identification above.

When `f` is a smooth function on a compact manifold cut at regular values between its critical
values, each step is the relative homology of one critical level, which does not depend on the
cut (`TauCeti.singularHomologySublevelPairIsoOfCriticalValue`). For a Morse function it is free on
the critical points of the level
(`TauCeti.IsMorse.nonempty_singularHomology_sublevelPair_iso_sigma`), which gives the Morse
inequalities. For a Morse–Bott function, Bott's attachment theorem identifies
it with the homology of the critical submanifolds of the level, shifted by their indices and with
coefficients twisted by the orientations of their negative normal bundles; the statements here then
become the Morse–Bott inequalities.

## References

* J. Milnor, *Morse Theory*, Annals of Mathematics Studies 51, Princeton University Press, 1963,
  Section 5.
* R. Bott, *Nondegenerate critical manifolds*, Annals of Mathematics 60 (1954), 248--261.
-/

public section

noncomputable section

open CategoryTheory Limits Module Set
open Polynomial (monomial)
open scoped Polynomial

universe u v w

namespace TauCeti

variable {X : Type u} [TopologicalSpace X] {β : Type*} [Preorder β] {f : X → β} {a b : β}
  {C : Type v} [Category.{w} C] [HasCoproducts.{u} C] [Preadditive C] [CategoryWithHomology C]

/-- If `a < f` everywhere, the subspace `{f ≤ a}` is empty, so the quotient map from the homology of
`{f ≤ b}` to the relative homology of the sublevel pair is an isomorphism. -/
private theorem isIso_singularHomologyπ_sublevelPair (hab : a ≤ b) (ha : ∀ x, a < f x) (R : C)
    (n : ℕ) : IsIso ((sublevelPair f hab).singularHomologyπ R n) := by
  have : IsEmpty (sublevelPair f hab).snd := ⟨fun (x : {x : X | f x ≤ a}) ↦ (ha x).not_ge x.2⟩
  infer_instance

/-- **The sublevel pair of a band covering `X`.** If `a < f ≤ b` everywhere, the relative singular
homology of `({f ≤ b}, {f ≤ a}) = (X, ∅)` is the singular homology of `X`. The isomorphism is the
map induced by the homeomorphism `X ≃ {f ≤ b}`, followed by the quotient map
`TopPair.singularHomologyπ`
(`TauCeti.singularHomologyπ_comp_singularHomologyIsoSublevelPair_inv`). -/
def singularHomologyIsoSublevelPair (hab : a ≤ b) (ha : ∀ x, a < f x) (hb : ∀ x, f x ≤ b)
    (R : C) (n : ℕ) :
    ((AlgebraicTopology.singularHomologyFunctor C n).obj R).obj (TopCat.of X) ≅
      (sublevelPair f hab).singularHomology R n :=
  ((AlgebraicTopology.singularHomologyFunctor C n).obj R).mapIso
    (TopCat.isoOfHomeo ((Homeomorph.setCongr (eq_univ_of_forall hb)).trans
      (Homeomorph.Set.univ X))).symm ≪≫
    @asIso _ _ _ _ _ (isIso_singularHomologyπ_sublevelPair hab ha R n)

/-- The inverse of `TauCeti.singularHomologyIsoSublevelPair`, after the quotient map from the
homology of `{f ≤ b}`, is the map induced by the inclusion `{f ≤ b} → X`. -/
@[reassoc]
theorem singularHomologyπ_comp_singularHomologyIsoSublevelPair_inv (hab : a ≤ b)
    (ha : ∀ x, a < f x) (hb : ∀ x, f x ≤ b) (R : C) (n : ℕ) :
    (sublevelPair f hab).singularHomologyπ R n ≫
        (singularHomologyIsoSublevelPair hab ha hb R n).inv =
      ((AlgebraicTopology.singularHomologyFunctor C n).obj R).map
        (TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩) := by
  rw [singularHomologyIsoSublevelPair, Iso.trans_inv]
  exact (@asIso _ _ _ _ _ (isIso_singularHomologyπ_sublevelPair hab ha R n)).hom_inv_id_assoc _

/-! ### The Morse inequalities of a sublevel filtration -/

section Filtration

variable {s : ℕ → β} (hs : Monotone s) {N : ℕ} (hs₀ : ∀ x, s 0 < f x) (hsN : ∀ x, f x ≤ s (N + 1))
  {k : Type*} [DivisionRing k] (V : ModuleCat.{u} k)

include hs in
/-- The sublevels `{f ≤ s j}` of a monotone sequence `s`, as a monotone sequence of subsets. -/
private lemma monotone_sublevel :
    Monotone fun j ↦ ({x | f x ≤ s j} : Set (TopCat.of X)) :=
  fun _ _ h ↦ sublevel_mono f (hs h)

include hs₀ hsN

/-- The singular homology of `X` has the dimension of the relative homology of the sublevel pair
`({f ≤ s (N + 1)}, {f ≤ s 0}) = (X, ∅)`. -/
private lemma finrank_singularHomology_eq_finrank_sublevelPair (n : ℕ) :
    finrank k (((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{u} k) n).obj V).obj
        (TopCat.of X)) =
      finrank k ((sublevelPair f (hs (Nat.zero_le (N + 1)))).singularHomology V n :
        ModuleCat k) :=
  (singularHomologyIsoSublevelPair (hs (Nat.zero_le (N + 1))) hs₀ hsN V n).toLinearEquiv.finrank_eq

/-- **The weak Morse inequalities of a sublevel filtration.** Let `s 0 ≤ ⋯ ≤ s (N + 1)` with
`s 0 < f ≤ s (N + 1)` everywhere. If the steps `Hᵢ({f ≤ s (j + 1)}, {f ≤ s j}; V)` are
finite-dimensional, then `dim Hᵢ(X; V)` is at most the sum of their dimensions. -/
theorem finrank_singularHomology_le_sum_sublevelPair (i : ℕ)
    (hfin : ∀ j ≤ N, Module.Finite k
      ((sublevelPair f (hs j.le_succ)).singularHomology V i : ModuleCat k)) :
    finrank k (((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{u} k) i).obj V).obj
        (TopCat.of X)) ≤
      ∑ j ∈ Finset.range (N + 1),
        finrank k ((sublevelPair f (hs j.le_succ)).singularHomology V i : ModuleCat k) := by
  rw [finrank_singularHomology_eq_finrank_sublevelPair hs hs₀ hsN]
  exact finrank_singularHomology_ofInclusion_le_sum_of_monotone (monotone_sublevel hs) V i hfin

/-- **The strong Morse inequalities of a sublevel filtration.** Let `s 0 ≤ ⋯ ≤ s (N + 1)` with
`s 0 < f ≤ s (N + 1)` everywhere, and suppose the steps `Hᵢ({f ≤ s (j + 1)}, {f ≤ s j}; V)` are
finite-dimensional in every degree. Write `bᵢ = dim Hᵢ(X; V)` and `cᵢ` for the sum of the
dimensions of the steps in degree `i`. Then `bₙ - bₙ₋₁ + ⋯ ± b₀ ≤ cₙ - cₙ₋₁ + ⋯ ± c₀`. -/
theorem sum_range_neg_one_pow_mul_finrank_singularHomology_le_sum_sublevelPair
    (hfin : ∀ j ≤ N, ∀ i, Module.Finite k
      ((sublevelPair f (hs j.le_succ)).singularHomology V i : ModuleCat k)) (n : ℕ) :
    ∑ i ∈ Finset.range (n + 1), (-1 : ℤ) ^ (n - i) *
        finrank k (((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{u} k) i).obj V).obj
          (TopCat.of X)) ≤
      ∑ i ∈ Finset.range (n + 1), (-1 : ℤ) ^ (n - i) * ((∑ j ∈ Finset.range (N + 1),
        finrank k ((sublevelPair f (hs j.le_succ)).singularHomology V i : ModuleCat k) : ℕ) :
          ℤ) := by
  simp only [finrank_singularHomology_eq_finrank_sublevelPair hs hs₀ hsN, Nat.cast_sum,
    Finset.mul_sum]
  rw [Finset.sum_comm]
  exact sum_range_neg_one_pow_mul_finrank_singularHomology_ofInclusion_le_of_monotone
    (monotone_sublevel hs) V hfin n

/-- **Euler's equality for a sublevel filtration.** Let `s 0 ≤ ⋯ ≤ s (N + 1)` with
`s 0 < f ≤ s (N + 1)` everywhere, and suppose the steps `Hᵢ({f ≤ s (j + 1)}, {f ≤ s j}; V)` are
finite-dimensional in every degree and vanish in degree `n + 1`. Write `bᵢ = dim Hᵢ(X; V)` and `cᵢ`
for the sum of the dimensions of the steps in degree `i`. Then
`∑ᵢ₌₀ⁿ (-1)ⁱ bᵢ = ∑ᵢ₌₀ⁿ (-1)ⁱ cᵢ`. -/
theorem sum_range_neg_one_pow_mul_finrank_singularHomology_eq_sum_sublevelPair
    (hfin : ∀ j ≤ N, ∀ i, Module.Finite k
      ((sublevelPair f (hs j.le_succ)).singularHomology V i : ModuleCat k)) {n : ℕ}
    (hzero : ∀ j ≤ N, IsZero ((sublevelPair f (hs j.le_succ)).singularHomology V (n + 1))) :
    ∑ i ∈ Finset.range (n + 1), (-1 : ℤ) ^ i *
        finrank k (((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{u} k) i).obj V).obj
          (TopCat.of X)) =
      ∑ i ∈ Finset.range (n + 1), (-1 : ℤ) ^ i * ((∑ j ∈ Finset.range (N + 1),
        finrank k ((sublevelPair f (hs j.le_succ)).singularHomology V i : ModuleCat k) : ℕ) :
          ℤ) := by
  simp only [finrank_singularHomology_eq_finrank_sublevelPair hs hs₀ hsN, Nat.cast_sum,
    Finset.mul_sum]
  rw [Finset.sum_comm]
  exact sum_range_neg_one_pow_mul_finrank_singularHomology_ofInclusion_eq_of_monotone
    (monotone_sublevel hs) V hfin hzero

/-- **The Morse polynomial identity of a sublevel filtration.** Let `s 0 ≤ ⋯ ≤ s (N + 1)` with
`s 0 < f ≤ s (N + 1)` everywhere, and suppose the steps `Hᵢ({f ≤ s (j + 1)}, {f ≤ s j}; V)` are
finite-dimensional in every degree and vanish in degree `n + 1`. Write `bᵢ = dim Hᵢ(X; V)` and `cᵢ`
for the sum of the dimensions of the steps in degree `i`. Then
`∑ᵢ₌₀ⁿ cᵢ tⁱ = ∑ᵢ₌₀ⁿ bᵢ tⁱ + (1 + t) Q(t)` for a polynomial `Q` with natural number coefficients.
For `i < n` the coefficient of `tⁱ` in `Q` is the sum over `j < N` of the ranks of the connecting
maps `Hᵢ₊₁({f ≤ s (j + 2)}, {f ≤ s (j + 1)}) ⟶ Hᵢ({f ≤ s (j + 1)}, {f ≤ s 0})` of the triples of
sublevels, and for `i ≥ n` it is zero. -/
theorem exists_sum_range_monomial_sum_sublevelPair_eq_add_mul
    (hfin : ∀ j ≤ N, ∀ i, Module.Finite k
      ((sublevelPair f (hs j.le_succ)).singularHomology V i : ModuleCat k)) {n : ℕ}
    (hzero : ∀ j ≤ N, IsZero ((sublevelPair f (hs j.le_succ)).singularHomology V (n + 1))) :
    ∃ Q : ℕ[X], ∑ i ∈ Finset.range (n + 1), monomial i (∑ j ∈ Finset.range (N + 1),
          finrank k ((sublevelPair f (hs j.le_succ)).singularHomology V i : ModuleCat k)) =
        ∑ i ∈ Finset.range (n + 1), monomial i
          (finrank k (((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{u} k) i).obj V).obj
            (TopCat.of X))) + (1 + Polynomial.X) * Q ∧
      (∀ i < n, Q.coeff i = ∑ j ∈ Finset.range N, finrank k (LinearMap.range
        ((TopTriple.ofInclusions (X := TopCat.of X) (sublevel_mono f (hs (Nat.zero_le (j + 1))))
          (sublevel_mono f (hs (j + 1).le_succ))).singularHomologyδ V (i + 1) i rfl).hom)) ∧
      ∀ i, n ≤ i → Q.coeff i = 0 := by
  simp only [finrank_singularHomology_eq_finrank_sublevelPair hs hs₀ hsN]
  exact exists_sum_range_monomial_singularHomology_ofInclusion_eq_add_mul_of_monotone
    (monotone_sublevel hs) V hfin hzero

/-- **The lacunary principle for a sublevel filtration.** Let `s 0 ≤ ⋯ ≤ s (N + 1)` with
`s 0 < f ≤ s (N + 1)` everywhere, and suppose the steps `Hᵢ({f ≤ s (j + 1)}, {f ≤ s j}; V)` are
finite-dimensional in every degree. Write `cᵢ` for the sum of the dimensions of the steps in
degree `i`. If of any two consecutive `cᵢ` one vanishes, then `dim Hₙ(X; V) = cₙ` for every `n`. -/
theorem finrank_singularHomology_eq_sum_sublevelPair
    (hfin : ∀ j ≤ N, ∀ i, Module.Finite k
      ((sublevelPair f (hs j.le_succ)).singularHomology V i : ModuleCat k))
    (hc : ∀ i, ∑ j ∈ Finset.range (N + 1),
        finrank k ((sublevelPair f (hs j.le_succ)).singularHomology V i : ModuleCat k) = 0 ∨
      ∑ j ∈ Finset.range (N + 1),
        finrank k ((sublevelPair f (hs j.le_succ)).singularHomology V (i + 1) : ModuleCat k) = 0)
    (n : ℕ) :
    finrank k (((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{u} k) n).obj V).obj
        (TopCat.of X)) =
      ∑ j ∈ Finset.range (N + 1),
        finrank k ((sublevelPair f (hs j.le_succ)).singularHomology V n : ModuleCat k) := by
  rw [finrank_singularHomology_eq_finrank_sublevelPair hs hs₀ hsN]
  exact finrank_singularHomology_ofInclusion_eq_sum_of_monotone (monotone_sublevel hs) V hfin hc n

end Filtration

end TauCeti
