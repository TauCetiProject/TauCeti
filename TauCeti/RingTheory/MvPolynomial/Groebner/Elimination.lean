/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.MvPolynomial.Groebner.Basic
public import TauCeti.Data.Finsupp.MapDomain

/-!
# The elimination theorem

Let `e : τ → σ` identify the variables `τ` with some of the variables `σ`, and let `I` be an
ideal of `MvPolynomial σ R`. The *elimination ideal* of `I` is `I.comap (rename e)`, the set of
polynomials in the variables `τ` which lie in `I` once their variables are renamed by `e`: it
consists of the consequences of the equations in `I` from which the remaining variables have been
eliminated.

Suppose the monomial order `m` on `σ` is an *elimination order* for `τ`: every monomial below a
monomial in the variables `e τ` is again a monomial in those variables. If `G` is a Gröbner basis
of `I` for `m`, then the members of `G` which only involve the variables `e τ` form a Gröbner
basis of the elimination ideal, for any monomial order `m'` on `τ` which `e` carries to `m`. When
the coefficients form a commutative ring, they in particular generate the elimination ideal, so a
single Gröbner basis of `I` computes the elimination ideal.

The lexicographic order is an elimination order for every upper set of variables: with the
antitone variable convention, the variables of an upper set are the smallest ones. The transport
of leading data along a relabeling, the description of polynomials whose leading monomial only
involves the variables `e τ` for an elimination order, and this property of the lexicographic
order are in `TauCeti.RingTheory.MvPolynomial.MonomialOrder`.

## Main results

* `MonomialOrder.IsGroebnerBasis.comap_rename`: **the elimination theorem**, the members of a
  Gröbner basis in the variables `e τ` form a Gröbner basis of the elimination ideal.
* `MonomialOrder.IsGroebnerBasis.comap_rename_eq_span`: over a commutative ring, they generate the
  elimination ideal.
* `MonomialOrder.IsGroebnerBasis.comap_rename_lex`: the elimination theorem for the
  lexicographic order and a strictly monotone embedding onto an upper set of variables.

None of these results assume that the coefficients form a field.

## References

* D. Cox, J. Little, D. O'Shea, *Ideals, Varieties, and Algorithms*, Chapter 3, §1, Theorem 2
  (the elimination theorem), and the exercises of that section on elimination orders.
-/

public section

namespace MonomialOrder

open MvPolynomial

variable {σ τ R : Type*} [CommSemiring R] {m : MonomialOrder σ} {m' : MonomialOrder τ}
  {e : τ → σ}

section Elimination

variable {G : Set (MvPolynomial σ R)} {I : Ideal (MvPolynomial σ R)}

/-- **The elimination theorem.** Let `m` be an elimination order for the variables `e τ`: every
monomial below a monomial in these variables is again a monomial in these variables. If `G` is a
Gröbner basis of `I` for `m`, then the members of `G` in the variables `e τ` form a Gröbner basis
of the elimination ideal `I.comap (rename e)` for every monomial order `m'` on `τ` which `e`
carries to `m`. -/
theorem IsGroebnerBasis.comap_rename (h : m.IsGroebnerBasis G I)
    (hm : ∀ a b : τ →₀ ℕ, a ≼[m'] b ↔ a.mapDomain e ≼[m] b.mapDomain e)
    (helim : ∀ a b : σ →₀ ℕ, a ≼[m] b → ↑b.support ⊆ Set.range e → ↑a.support ⊆ Set.range e) :
    m'.IsGroebnerBasis (rename e ⁻¹' G) (I.comap (rename e)) := by
  classical
  have he := injective_of_forall_toSyn_le_iff hm
  refine .mk (fun g hg ↦ h.subset hg) (le_antisymm ?_ (Ideal.span_mono (Set.image_mono
    fun g hg ↦ h.subset hg)))
  -- Killing the variables outside `e τ` maps the leading term of each `g ∈ G` either to `0` or,
  -- when `g` is a renamed polynomial `rename e g'`, to the leading term of `g'`.
  have hkill : Ideal.map (killCompl he) (Ideal.span (m.leadingTerm '' G)) ≤
      Ideal.span (m'.leadingTerm '' (rename e ⁻¹' G)) := by
    rw [Ideal.map_span, Ideal.span_le, ← Set.image_comp, Set.image_subset_iff]
    intro g hg
    by_cases hdeg : ↑(m.degree g).support ⊆ Set.range e
    · obtain ⟨g', rfl⟩ := exists_rename_eq_of_coe_support_degree_subset helim he hdeg
      rw [Set.mem_preimage, Function.comp_apply, leadingTerm_rename hm, killCompl_rename_app]
      exact Ideal.subset_span ⟨g', hg, rfl⟩
    · rw [Set.mem_preimage, Function.comp_apply, leadingTerm,
        killCompl_monomial_eq_zero_of_not_subset he _ hdeg]
      exact Ideal.zero_mem _
  -- The leading term of `f` in the elimination ideal is recovered from that of `rename e f`.
  rw [Ideal.span_le, Set.image_subset_iff]
  intro f hf
  have hmem : m.leadingTerm (rename e f) ∈ Ideal.span (m.leadingTerm '' G) :=
    h.span_leadingTerm_image ▸ Ideal.subset_span ⟨rename e f, hf, rfl⟩
  have := hkill (Ideal.mem_map_of_mem _ hmem)
  rwa [leadingTerm_rename hm, killCompl_rename_app] at this

/-- In the elimination theorem over a commutative ring, the members of the Gröbner basis in the
variables `e τ` generate the elimination ideal. -/
theorem IsGroebnerBasis.comap_rename_eq_span {R : Type*} [CommRing R] {G : Set (MvPolynomial σ R)}
    {I : Ideal (MvPolynomial σ R)} (h : m.IsGroebnerBasis G I)
    (hm : ∀ a b : τ →₀ ℕ, a ≼[m'] b ↔ a.mapDomain e ≼[m] b.mapDomain e)
    (helim : ∀ a b : σ →₀ ℕ, a ≼[m] b → ↑b.support ⊆ Set.range e → ↑a.support ⊆ Set.range e) :
    I.comap (rename e) = Ideal.span (rename e ⁻¹' G) :=
  (h.comap_rename hm helim).ideal_eq_span

end Elimination

section Lex

/-- **The elimination theorem for the lexicographic order.** If `e : τ → σ` is strictly monotone
with image an upper set of variables, then the members of a lexicographic Gröbner basis of `I` in
the variables `e τ` form a lexicographic Gröbner basis of the elimination ideal. -/
theorem IsGroebnerBasis.comap_rename_lex [LinearOrder σ] [WellFoundedGT σ] [LinearOrder τ]
    [WellFoundedGT τ] {G : Set (MvPolynomial σ R)} {I : Ideal (MvPolynomial σ R)}
    (h : lex.IsGroebnerBasis G I) (he : StrictMono e) (hup : IsUpperSet (Set.range e)) :
    lex.IsGroebnerBasis (rename e ⁻¹' G) (I.comap (rename e)) :=
  h.comap_rename
    (fun _ _ ↦ by simp only [lex_le_iff, Finsupp.toLex_mapDomain_le_toLex_mapDomain_iff he])
    fun _ _ hab hb ↦ coe_support_subset_of_lex_le hup hab hb

end Lex

end MonomialOrder
