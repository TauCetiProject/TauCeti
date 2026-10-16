/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Algebra.Group.Profinite.Demushkin.Character.Image
public import TauCeti.Topology.Algebra.Group.Profinite.Demushkin.NormalForm.Two.Even.Exact
public import TauCeti.Topology.Algebra.Group.Profinite.Demushkin.NormalForm.Two.Even.PadicExponent.Character

/-!
# Labute's normal form for the dyadic Demushkin groups of even rank with image `{±1}`

Let `G` be a Demushkin group at `p = 2` of even rank `n` whose canonical character has image
`{±1}`. This is the endpoint `f = ∞` of the even-rank dyadic family of Labute's classification:
`G` is presented on `n` generators by the single relator

  `x₁² (x₁, x₂)(x₃, x₄) ⋯ (x_{n-1}, x_n)`,

the normal-form word `TauCeti.demushkinWordNeTwo 2 n`; in particular two such groups of the same
rank are topologically isomorphic. This file proves it.

Since `-1` is a value of the canonical character and `-1 ∉ 1 + 4ℤ₂`, the `q`-invariant of `G` is
`2` (`TauCeti.demushkinQ_eq_two_of_neg_one_mem_range_demushkinCharacter`), so Labute's Theorem 3
for `q = 2` and even rank,
`IsDemushkin.exists_continuousMulEquiv_apply_eq_padicPow_mul_labuteComm_mul_demushkinWordNeTwo`,
carries a relator `r ∈ Φ(F)` of `G` to `x₁^{2+α} (x₁, x₂) x₃^{q} (x₃, x₄) ⋯ (x_{n-1}, x_n)` with
`α ∈ 4ℤ₂` and `q ∈ {0} ∪ {2^f : f ≥ 2}`. The character table of that word
(`TauCeti.IsDemushkin.eq_zero_and_eq_zero_of_range_demushkinCharacter_eq_zpowers_neg_one`) shows
that the image `{±1}` forces `α = 0`, and `q = 0` as soon as the factor `x₃^q` is present, which
leaves exactly the endpoint word.

## Main results

* `freeProP.exists_continuousMulEquiv_apply_eq_demushkinWordNeTwo_of_range_eq_zpowers_neg_one`: a
  relator in `Φ(F)` of the free pro-`2` group on an even number of generators presenting a
  Demushkin group with image `{±1}` is carried to `x₁² (x₁, x₂) ⋯ (x_{n-1}, x_n)` by a continuous
  automorphism of `F`.
* `TauCeti.freeProP.exists_continuousMulEquiv_apply_eq_of_range_eq_zpowers_neg_one`: **Labute's
  Theorem 2 at the endpoint**, two such relators are carried to each other by a continuous
  automorphism of `F`.
* `nonempty_continuousMulEquiv_presentedProP_demushkinWordNeTwo_of_range_eq_zpowers_neg_one`, in
  the namespace `TauCeti.IsDemushkin`: the intrinsic form, such a Demushkin group is topologically
  isomorphic to `⟨x₁, …, x_n ∣ x₁² (x₁, x₂) ⋯ (x_{n-1}, x_n)⟩` on `n = demushkinRank hG` generators.
* `IsDemushkin.nonempty_continuousMulEquiv_of_even_demushkinRank_of_range_eq_zpowers_neg_one`:
  **uniqueness**, two Demushkin groups at `p = 2` of the same even rank whose canonical characters
  have image `{±1}` are topologically isomorphic.

## References

* J. P. Labute, *Classification of Demushkin groups*, Canad. J. Math. 19 (1967), 106–132, §3,
  Theorems 2, 3 and 4 and the corollary to Theorem 4.
* J. Neukirch, A. Schmidt and K. Wingberg, *Cohomology of Number Fields*, 2nd ed., (3.9.19).
-/

public section

namespace TauCeti

open Subgroup

universe u v

variable {n : ℕ}

/-- At `α = 0`, the even dyadic word on the generators of the free pro-`2` group on `n ≥ 2`
generators is the endpoint word `x₁² (x₁, x₂)(x₃, x₄) ⋯ (x_{n-1}, x_n)` as soon as `q = 0` whenever
the factor `x₃^q` is present; at `n = 2` that factor is `1`. -/
private theorem demushkinWordTwoEvenPadic_zero_freeProPGen (hn : 2 ≤ n) {q : ℕ}
    (hq : 2 < n → q = 0) :
    demushkinWordTwoEvenPadic (isProP_freeProP 2 (Fin n)) 0 q n (freeProPGen 2 n) =
      demushkinWordNeTwo 2 n (freeProPGen 2 n) := by
  rcases hn.lt_or_eq with hn₂ | rfl
  · rw [hq hn₂, demushkinWordTwoEvenPadic_zero_zero _ _ _ hn]
  · have hx : freeProPGen 2 2 2 = 1 := freeProPGen_eq_one_of_le 2 le_rfl
    rw [demushkinWordTwoEvenPadic_two _ _ _ _ hx, ← demushkinWordTwoEvenPadic_two _ 0 0 _ hx,
      demushkinWordTwoEvenPadic_zero_zero _ _ _ le_rfl]

namespace freeProP

/-- **Labute's normal form for the dyadic Demushkin groups of even rank with image `{±1}`**
(Labute, Theorem 3 and the corollary to Theorem 4). Let `r ∈ Φ(F)` be a relator of the free
pro-`2` group on an even number `n` of generators presenting a Demushkin group
`G = ⟨x₁, …, x_n ∣ r⟩` whose canonical character has image `{±1}`. Then a continuous automorphism
of `F` carries `r` to `x₁² (x₁, x₂)(x₃, x₄) ⋯ (x_{n-1}, x_n)`. -/
theorem exists_continuousMulEquiv_apply_eq_demushkinWordNeTwo_of_range_eq_zpowers_neg_one
    (hn : Even n) {r : freeProP 2 (Fin n)} (hr : r ∈ proPFrattini 2 (freeProP 2 (Fin n)))
    (hG : IsDemushkin 2 (presentedProP 2 (Fin n) {r}))
    (hA : (demushkinCharacter hG).toMonoidHom.range = zpowers (-1 : ℤ_[2]ˣ)) :
    ∃ e : freeProP 2 (Fin n) ≃ₜ* freeProP 2 (Fin n),
      e r = demushkinWordNeTwo 2 n (freeProPGen 2 n) := by
  have hn0 : 0 < n := by simpa using hG.card_pos_presentedProP
  have hn2 : 2 ≤ n := by
    obtain ⟨m, hm⟩ := hn
    omega
  obtain ⟨e, α, q, hα, hq, he⟩ :=
    IsDemushkin.exists_continuousMulEquiv_apply_eq_padicPow_mul_labuteComm_mul_demushkinWordNeTwo
      hn hr hG
      (demushkinQ_eq_two_of_neg_one_mem_range_demushkinCharacter hG (hA ▸ mem_zpowers _))
  rw [← demushkinWordTwoEvenPadic_eq_padicPow_mul_labuteComm_mul _ _ _ _ _ hn2] at he
  -- The image `{±1}` pins `α = 0`, and `q = 0` when the factor `x₃^q` is present.
  obtain ⟨rfl, hq₀⟩ := hG.eq_zero_and_eq_zero_of_range_demushkinCharacter_eq_zpowers_neg_one hα
    (fun _ ↦ hq) hn (by omega) (presentedProP.congrSingleton e he) hA
  exact ⟨e, he.trans (demushkinWordTwoEvenPadic_zero_freeProPGen hn2 hq₀)⟩

/-- **Labute's Theorem 2 at the even-rank dyadic endpoint.** Let `r, r' ∈ Φ(F)` be relators of the
free pro-`2` group on an even number `n` of generators presenting Demushkin groups whose canonical
characters both have image `{±1}`. Then a continuous automorphism of `F` carries `r` to `r'`; in
particular the closed normal closures of `r` and `r'` are carried to each other. -/
theorem exists_continuousMulEquiv_apply_eq_of_range_eq_zpowers_neg_one (hn : Even n)
    {r r' : freeProP 2 (Fin n)} (hr : r ∈ proPFrattini 2 (freeProP 2 (Fin n)))
    (hr' : r' ∈ proPFrattini 2 (freeProP 2 (Fin n)))
    (hG : IsDemushkin 2 (presentedProP 2 (Fin n) {r}))
    (hG' : IsDemushkin 2 (presentedProP 2 (Fin n) {r'}))
    (hA : (demushkinCharacter hG).toMonoidHom.range = zpowers (-1 : ℤ_[2]ˣ))
    (hA' : (demushkinCharacter hG').toMonoidHom.range = zpowers (-1 : ℤ_[2]ˣ)) :
    ∃ e : freeProP 2 (Fin n) ≃ₜ* freeProP 2 (Fin n), e r = r' := by
  obtain ⟨e, he⟩ :=
    exists_continuousMulEquiv_apply_eq_demushkinWordNeTwo_of_range_eq_zpowers_neg_one hn hr hG hA
  obtain ⟨e', he'⟩ :=
    exists_continuousMulEquiv_apply_eq_demushkinWordNeTwo_of_range_eq_zpowers_neg_one hn hr' hG' hA'
  exact ⟨e.trans e'.symm, by rw [ContinuousMulEquiv.trans_apply, he, ← he', e'.symm_apply_apply]⟩

end freeProP

namespace IsDemushkin

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  [TotallyDisconnectedSpace G]

/-- **Labute's normal form for a dyadic Demushkin group of even rank with image `{±1}`, intrinsic
form.** A Demushkin group `G` at `p = 2` of even rank whose canonical character has image `{±1}`
is topologically isomorphic to `⟨x₁, …, x_n ∣ x₁² (x₁, x₂)(x₃, x₄) ⋯ (x_{n-1}, x_n)⟩` on
`n = demushkinRank hG` generators. -/
theorem nonempty_continuousMulEquiv_presentedProP_demushkinWordNeTwo_of_range_eq_zpowers_neg_one
    (hG : IsDemushkin 2 G) (hn : Even (demushkinRank hG))
    (hA : (demushkinCharacter hG).toMonoidHom.range = zpowers (-1 : ℤ_[2]ˣ)) :
    Nonempty (G ≃ₜ* presentedProP 2 (Fin (demushkinRank hG))
      {demushkinWordNeTwo 2 (demushkinRank hG) (freeProPGen 2 (demushkinRank hG))}) := by
  obtain ⟨r, hr, ⟨e⟩⟩ := hG.exists_mem_proPFrattini_continuousMulEquiv_presentedProP_fin
  have : Nonempty (Fin (demushkinRank hG)) := ⟨⟨0, hG.demushkinRank_pos⟩⟩
  have hG' : IsDemushkin 2 (presentedProP 2 (Fin (demushkinRank hG)) {r}) :=
    isDemushkin_of_nondegenerate_degreeOneForm hr (ContinuousMulEquiv.refl _)
      (hG.nondegenerate_degreeOneForm hr e)
  have hA' : (demushkinCharacter hG').toMonoidHom.range = zpowers (-1 : ℤ_[2]ˣ) := by
    rw [range_demushkinCharacter_of_equiv hG hG' e.symm, hA]
  obtain ⟨e', he'⟩ :=
    freeProP.exists_continuousMulEquiv_apply_eq_demushkinWordNeTwo_of_range_eq_zpowers_neg_one hn
      hr hG' hA'
  exact ⟨e.symm.trans (presentedProP.congrSingleton e' he')⟩

/-- **Uniqueness of the dyadic Demushkin groups of even rank with image `{±1}`** (Labute,
Theorems 2 and 3). Two Demushkin groups at `p = 2` of the same even rank whose canonical
characters both have image `{±1}` are topologically isomorphic. -/
theorem nonempty_continuousMulEquiv_of_even_demushkinRank_of_range_eq_zpowers_neg_one
    {H : Type v} [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [CompactSpace H]
    [TotallyDisconnectedSpace H] (hG : IsDemushkin 2 G) (hH : IsDemushkin 2 H)
    (hn : demushkinRank hG = demushkinRank hH) (heven : Even (demushkinRank hG))
    (hA : (demushkinCharacter hG).toMonoidHom.range = zpowers (-1 : ℤ_[2]ˣ))
    (hB : (demushkinCharacter hH).toMonoidHom.range = zpowers (-1 : ℤ_[2]ˣ)) :
    Nonempty (G ≃ₜ* H) := by
  obtain ⟨e⟩ :=
    hG.nonempty_continuousMulEquiv_presentedProP_demushkinWordNeTwo_of_range_eq_zpowers_neg_one
      heven hA
  obtain ⟨e'⟩ :=
    hH.nonempty_continuousMulEquiv_presentedProP_demushkinWordNeTwo_of_range_eq_zpowers_neg_one
      (hn ▸ heven) hB
  rw [hn] at e
  exact ⟨e.trans e'.symm⟩

end IsDemushkin

end TauCeti
