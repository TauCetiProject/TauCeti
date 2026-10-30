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
basis of the elimination ideal, for any monomial order `m'` on `τ` which `e` carries to `m`. In
particular, when the leading coefficients are units, they generate the elimination ideal, so a
single Gröbner basis of `I` computes the elimination ideal.

The lexicographic order is an elimination order for every upper set of variables: with the
antitone variable convention, the variables of an upper set are the smallest ones.

## Main results

* `MonomialOrder.degree_rename`, `MonomialOrder.leadingCoeff_rename` and
  `MonomialOrder.leadingTerm_rename`: renaming the variables along an embedding of monomial
  orders commutes with leading monomials, coefficients and terms.
* `MonomialOrder.IsGroebnerBasis.comap_rename`: **the elimination theorem**, the members of a
  Gröbner basis in the variables `e τ` form a Gröbner basis of the elimination ideal.
* `MonomialOrder.IsGroebnerBasis.comap_rename_eq_span`: they generate the elimination ideal.
* `MonomialOrder.coe_support_subset_of_lex_le`: monomials supported in an upper set of variables
  form a lower set for the lexicographic order.
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

section Rename

/-- A relabeling of variables which carries the monomial order `m'` to `m` is injective. -/
private theorem injective_of_forall_toSyn_le_iff
    (hm : ∀ a b : τ →₀ ℕ, a ≼[m'] b ↔ a.mapDomain e ≼[m] b.mapDomain e) :
    Function.Injective e := by
  intro i j hij
  -- The two variables `X i`, `X j` are renamed to the same variable, so neither exceeds the other.
  have hsingle : m.toSyn ((Finsupp.single i 1).mapDomain e) =
      m.toSyn ((Finsupp.single j 1).mapDomain e) := by
    simp [hij]
  have h := m'.toSyn.injective <| le_antisymm ((hm _ _).2 hsingle.le) ((hm _ _).2 hsingle.ge)
  simpa [Finsupp.single_left_inj] using h

/-- Renaming the variables along a relabeling which carries the monomial order `m'` to `m` renames
the leading monomial. -/
theorem degree_rename (hm : ∀ a b : τ →₀ ℕ, a ≼[m'] b ↔ a.mapDomain e ≼[m] b.mapDomain e)
    (p : MvPolynomial τ R) : m.degree (rename e p) = (m'.degree p).mapDomain e := by
  classical
  have he := injective_of_forall_toSyn_le_iff hm
  rcases eq_or_ne p 0 with rfl | hp
  · simp
  refine m.toSyn.injective (le_antisymm (m.degree_le_iff.2 fun c hc ↦ ?_) (m.le_degree ?_))
  · rw [support_rename_of_injective he, Finset.mem_image] at hc
    obtain ⟨a, ha, rfl⟩ := hc
    exact (hm _ _).1 (m'.le_degree ha)
  · rw [support_rename_of_injective he]
    exact Finset.mem_image_of_mem _ (m'.degree_mem_support hp)

/-- Renaming the variables along a relabeling which carries the monomial order `m'` to `m`
preserves the leading coefficient. -/
theorem leadingCoeff_rename (hm : ∀ a b : τ →₀ ℕ, a ≼[m'] b ↔ a.mapDomain e ≼[m] b.mapDomain e)
    (p : MvPolynomial τ R) : m.leadingCoeff (rename e p) = m'.leadingCoeff p := by
  rw [leadingCoeff, degree_rename hm,
    coeff_rename_mapDomain _ (injective_of_forall_toSyn_le_iff hm), leadingCoeff]

/-- Renaming the variables along a relabeling which carries the monomial order `m'` to `m`
renames the leading term. -/
theorem leadingTerm_rename (hm : ∀ a b : τ →₀ ℕ, a ≼[m'] b ↔ a.mapDomain e ≼[m] b.mapDomain e)
    (p : MvPolynomial τ R) : m.leadingTerm (rename e p) = rename e (m'.leadingTerm p) := by
  rw [leadingTerm, leadingTerm, degree_rename hm, leadingCoeff_rename hm, rename_monomial]

end Rename

section Elimination

variable {G : Set (MvPolynomial σ R)} {I : Ideal (MvPolynomial σ R)}

/-- For an elimination order, a polynomial whose leading monomial only involves the variables
`e τ` is the renaming of a polynomial in the variables `τ`. -/
private theorem exists_rename_eq_of_coe_support_degree_subset
    (helim : ∀ a b : σ →₀ ℕ, a ≼[m] b → ↑b.support ⊆ Set.range e → ↑a.support ⊆ Set.range e)
    (he : Function.Injective e) {g : MvPolynomial σ R}
    (hg : ↑(m.degree g).support ⊆ Set.range e) : ∃ g' : MvPolynomial τ R, rename e g' = g := by
  classical
  refine exists_rename_eq_of_vars_subset_range g e he fun i hi ↦ ?_
  obtain ⟨d, hd, hid⟩ := (mem_vars_iff_mem_support i).1 hi
  exact helim d _ (m.le_degree hd) hg hid

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

/-- In the elimination theorem, if the nonzero members of the Gröbner basis have unit leading
coefficients (for instance over a field), then the members in the variables `e τ` generate the
elimination ideal. -/
theorem IsGroebnerBasis.comap_rename_eq_span {R : Type*} [CommRing R] {G : Set (MvPolynomial σ R)}
    {I : Ideal (MvPolynomial σ R)} (h : m.IsGroebnerBasis G I)
    (hG : ∀ g ∈ G, g ≠ 0 → IsUnit (m.leadingCoeff g))
    (hm : ∀ a b : τ →₀ ℕ, a ≼[m'] b ↔ a.mapDomain e ≼[m] b.mapDomain e)
    (helim : ∀ a b : σ →₀ ℕ, a ≼[m] b → ↑b.support ⊆ Set.range e → ↑a.support ⊆ Set.range e) :
    I.comap (rename e) = Ideal.span (rename e ⁻¹' G) := by
  refine (h.comap_rename hm helim).ideal_eq_span fun g hg hg0 ↦ ?_
  rw [← leadingCoeff_rename hm]
  exact hG _ hg <| by
    rwa [Ne, map_eq_zero_iff _ (rename_injective _ (injective_of_forall_toSyn_le_iff hm))]

end Elimination

section Lex

/-- For the lexicographic order, the monomials supported in an upper set of variables form a
lower set: with the antitone variable convention these are the smallest variables. -/
theorem coe_support_subset_of_lex_le [LinearOrder σ] [WellFoundedGT σ] {s : Set σ}
    (hs : IsUpperSet s) {a b : σ →₀ ℕ} (hab : a ≼[lex] b) (hb : ↑b.support ⊆ s) :
    ↑a.support ⊆ s := by
  intro j hj
  by_contra hjs
  rcases eq_or_ne a b with rfl | hne
  · exact hjs (hb hj)
  -- `a < b` first differs from `b` at some `i` with `0 ≤ a i < b i`, so `i ∈ s`; since `j ∉ s`,
  -- `j < i`, and then `a j = b j = 0`.
  obtain ⟨i, hi, hlt⟩ := Finsupp.Lex.lt_iff.1 <| lex_lt_iff.1 <|
    lt_of_le_of_ne hab (lex.toSyn.injective.ne hne)
  have hbi : i ∈ s := hb (Finsupp.mem_support_iff.2 (Nat.zero_lt_of_lt hlt).ne')
  have hji : j < i := lt_of_not_ge fun hij ↦ hjs (hs hij hbi)
  have hbj : b j = 0 := Finsupp.notMem_support_iff.1 fun h ↦ hjs (hb h)
  exact (Finsupp.mem_support_iff.1 hj) ((hi j hji).trans hbj)

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
