/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.FieldTheory.FunctionField.Place.Approximation
public import TauCeti.FieldTheory.FunctionField.Repartition.IndexOfSpecialty
public import TauCeti.FieldTheory.FunctionField.HolomorphyRing.Basic
public import TauCeti.FieldTheory.FunctionField.Place.Completion.Basic
public import TauCeti.Topology.Algebra.Module.DenseBaseChange
import TauCeti.Topology.Constructions.Pi

/-!
# Strong approximation for an algebraic function field

Weak approximation (`TauCeti.Place.exists_forall_mem_ord_sub_eq`) prescribes the behaviour of a
function at finitely many places of `F / k` and says nothing whatever about the remaining ones.
**Strong approximation** keeps that prescription and adds regularity at every place of a set `S`
which misses at least one place of `F / k`: given such an `S`, a finite subset `s ⊆ S`, targets
`f P` and prescribed orders `r P`, there is a single `x : F` with

`ord_P (x - f P) = r P` for every `P ∈ s`, and `x ∈ 𝒪_P` for every `P ∈ S` outside `s`.

Some freedom is what pays for the extra control, and the properness of `S` is exactly that
freedom: for `S` the set of *all* places the statement is false, because a function regular at
every place is a constant (`TauCeti.Place.coe_algebraicClosure_eq_iInter_integers`).

This is Stichtenoth, *Algebraic Function Fields and Codes*, 2nd ed., Theorem 1.6.5.  Unlike weak
approximation it is a consequence of Riemann's theorem, and it is the form of approximation that
consumers working inside a holomorphy ring `𝒪_S` want.

The same holds in the completions, and there it is a density statement: for disjoint sets `S`
and `T` of places which together miss a place of `F / k`, the holomorphy ring `𝒪_S` is dense in
the product of the completions `F̂_P` over `P ∈ T`. It then passes to every finite
`𝒪_S`-module `M`, which is dense in the product of its scalar extensions `F̂_P ⊗ M`
(`DenseRange.pi_one_tmul`). This is the form in which approximation enters the construction of
integral points on curves: global sections of a vector bundle on an affine curve are approximated
at finitely many places outside it.

## Main results

* `TauCeti.Place.exists_forall_mem_valuation_sub_le_and_forall_mem_integers`: strong
  approximation in the inequality form, `ord_P (x - f P) ≥ r P` on `s` and integrality on the
  rest of `S`.
* `TauCeti.Place.exists_forall_mem_ord_sub_eq_and_forall_mem_integers`: **strong approximation**
  (Stichtenoth, Theorem 1.6.5), with the orders on `s` prescribed exactly.
* `TauCeti.Place.denseRange_completionEmbedding_holomorphyRing_pi`: strong approximation in the
  completions, the density of `𝒪_S` in `∏_{P ∈ T} F̂_P`.
* `TauCeti.Place.denseRange_one_tmul_holomorphyRing_pi`: the density of a finite `𝒪_S`-module in
  the product of its scalar extensions to the completions at `T`.

## Implementation notes

The proof is the repartition-space argument.  Take a place `Q ∉ S` and let `E` be the divisor
with coefficient `-r P` at each `P ∈ s` and `n` copies of `Q`, with `n` large enough that `E` is
nonspecial; the enlargement happens at `Q` alone, so it disturbs no coefficient of `E` at a place
of `S`.  Then `A_F(E) + F = A_F`
(`TauCeti.adeleFiltration_sup_diagonalRepartitions_eq_repartitionSpace_iff`), so the repartition
carrying `f P` at each `P ∈ s` and `0` elsewhere differs from a *constant* `x` by a repartition
bounded by `E`.  Reading that bound off place by place gives both conclusions at once: at `P ∈ s`
it is the approximation `ord_P (x - f P) ≥ r P`, and at the other places of `S`, where `E` has
coefficient `0` and the repartition has entry `0`, it is the integrality of `x`.

The inequality form is stated multiplicatively, as `v_P (x - f P) ≤ exp (-r P)`, for the reason
recorded in `TauCeti/FieldTheory/FunctionField/Repartition/Basic.lean`: the additive reading
`r P ≤ ord_P (x - f P)` is wrong at `x = f P`, where the junk value `ord_P 0 = 0` would exclude
an exact hit whenever `r P > 0`.  No such guard is needed in the equality form, whose conclusion
`ord_P (x - f P) = r P` already forces `x ≠ f P` when `r P ≠ 0`.

## References

* H. Stichtenoth, *Algebraic Function Fields and Codes*, 2nd ed., GTM 254, Springer, 2009,
  Section I.6 (Theorem 1.6.5).
* L. Moret-Bailly, *Groupes de Picard et problèmes de Skolem II*, Ann. Sci. ÉNS 22 (1989),
  proof of Lemme 3.8, for approximation in finite projective modules over `𝒪_S`.
-/

public section

open scoped WithZero

namespace TauCeti

open AlgebraicGeometry

variable {k F : Type*} [Field k] [Field F] [Algebra k F]

namespace Place

variable (hF : IsFunctionField k F) (hex : IsIntegrallyClosedIn k F)
    {S : Set (Place k F)} (hS : S ≠ Set.univ) {s : Finset (Place k F)} (hsS : ↑s ⊆ S)
    (f : Place k F → F) (r : Place k F → ℤ)

include hF hex hS hsS

/-- **Strong approximation, in the inequality form** (Stichtenoth, Theorem 1.6.5): for a set `S`
of places of `F / k` that is not all of them and a finite subset `s ⊆ S`, some `x : F`
approximates the target `f P` to order `r P` at every `P ∈ s` and is regular at every place of
`S` outside `s`.

The approximation is the multiplicative bound `v_P (x - f P) ≤ exp (-r P)`, which reads
`ord_P (x - f P) ≥ r P` at every place where `x ≠ f P` and is satisfied outright where
`x = f P`. -/
theorem exists_forall_mem_valuation_sub_le_and_forall_mem_integers :
    ∃ x : F, (∀ P ∈ s, P.valuation (x - f P) ≤ WithZero.exp (-r P)) ∧
      ∀ P ∈ S, P ∉ s → x ∈ P.integers := by
  obtain ⟨Q, hQ⟩ := (Set.ne_univ_iff_exists_notMem S).mp hS
  obtain ⟨c, hc⟩ := exists_forall_indexOfSpecialty_eq_zero hF hex
  obtain ⟨n, hn⟩ := Divisor.exists_le_degree_add_nsmul_ofPoint hF
    (Finsupp.indicator s fun P _ ↦ -r P) Q c
  set E : Divisor k F := Finsupp.indicator s (fun P _ ↦ -r P) + n • WeilDivisor.ofPoint Q with hE
  -- no place of `S`, and no place of `s`, is the place `Q` at which `E` was enlarged
  have hne : ∀ P : Place k F, P ∈ S ∨ P ∈ s →
      WeilDivisor.coeff (n • WeilDivisor.ofPoint Q) P = 0 := by
    rintro P hP
    have hPQ : P ≠ Q := by
      rintro rfl
      exact hQ (hP.elim id fun h ↦ hsS (Finset.mem_coe.mpr h))
    simp [WeilDivisor.coeff_ofPoint_of_ne hPQ]
  have hEs : ∀ P ∈ s, WeilDivisor.coeff E P = -r P := fun P hP ↦ by
    rw [hE, WeilDivisor.coeff_add, hne P (Or.inr hP), add_zero]
    simp [WeilDivisor.coeff, Finsupp.indicator_of_mem hP]
  have hEout : ∀ P ∈ S, P ∉ s → WeilDivisor.coeff E P = 0 := fun P hPS hPs ↦ by
    rw [hE, WeilDivisor.coeff_add, hne P (Or.inl hPS), add_zero]
    simp [WeilDivisor.coeff, Finsupp.indicator_of_notMem hPs]
  -- the repartition carrying the targets on `s` differs from a constant by one bounded by `E`
  have hmem : Set.indicator (↑s : Set (Place k F)) f ∈
      adeleFiltration E ⊔ diagonalRepartitions k F := by
    rw [(adeleFiltration_sup_diagonalRepartitions_eq_repartitionSpace_iff hF hex E).mpr (hc E hn),
      mem_repartitionSpace_iff_finite]
    refine s.finite_toSet.subset fun P hP ↦ ?_
    by_contra hPs
    exact hP (by simp [Set.indicator_of_notMem hPs])
  obtain ⟨x, hx⟩ := mem_adeleFiltration_sup_diagonalRepartitions_iff.mp hmem
  refine ⟨x, fun P hP ↦ ?_, fun P hPS hPs ↦ ?_⟩
  · have := mem_adeleFiltration_iff.mp hx P
    rw [Set.indicator_of_mem hP, hEs P hP] at this
    rwa [P.valuation.map_sub_swap]
  · have := mem_adeleFiltration_iff.mp hx P
    rw [Set.indicator_of_notMem hPs, hEout P hPS hPs, zero_sub, Valuation.map_neg,
      WithZero.exp_zero] at this
    exact P.mem_integers_iff.mpr this

/-- **Strong approximation** (Stichtenoth, Theorem 1.6.5): for a set `S` of places of `F / k`
that is not all of them and a finite subset `s ⊆ S`, some `x : F` satisfies
`ord_P (x - f P) = r P` at every `P ∈ s` and is regular at every place of `S` outside `s`.

The orders on `s` are prescribed exactly, as in weak approximation
(`TauCeti.Place.exists_forall_mem_ord_sub_eq`); what strong approximation adds is the regularity
of `x` at the remaining places of `S`, at the price of requiring `S` to be proper. -/
theorem exists_forall_mem_ord_sub_eq_and_forall_mem_integers :
    ∃ x : F, (∀ P ∈ s, P.ord (x - f P) = r P) ∧ ∀ P ∈ S, P ∉ s → x ∈ P.integers := by
  -- a single `t` with `ord_P t = r P` on `s`: approximating `f P + t` to order `r P + 1`
  -- leaves an error of order exactly `r P`
  obtain ⟨t, ht0, ht⟩ := exists_ne_zero_forall_mem_ord_eq s r
  obtain ⟨x, hx, hint⟩ := exists_forall_mem_valuation_sub_le_and_forall_mem_integers hF hex hS hsS
    (fun P ↦ f P + t) fun P ↦ r P + 1
  refine ⟨x, fun P hP ↦ ?_, hint⟩
  have hsum : x - f P = t + (x - (f P + t)) := by ring
  rcases eq_or_ne (x - (f P + t)) 0 with h0 | h0
  · rw [hsum, h0, add_zero]
    exact ht P hP
  · have hlt : P.ord t < P.ord (x - (f P + t)) := by
      have hb := hx P hP
      rw [P.valuation_eq_exp_neg_ord h0, WithZero.exp_le_exp] at hb
      rw [ht P hP]
      omega
    rw [hsum, P.ord_add_eq_min_of_ord_ne ht0 h0 hlt.ne, min_eq_left hlt.le, ht P hP]

end Place

/-! ### Strong approximation in the completions -/

namespace Place

open scoped PlaceCompletionExtension TensorProduct

variable (hF : IsFunctionField k F) (hex : IsIntegrallyClosedIn k F)

include hF hex in
/-- **Strong approximation in the completions.** Let `S` and `T` be disjoint sets of places of
`F / k` which together miss at least one place. Then the holomorphy ring `𝒪_S` is dense in the
product of the completions `F̂_P` over `P ∈ T`.

Some place must be missed: for the rational function field and `T` a single place `P`, the ring
of functions regular away from `P` is a polynomial ring, which is discrete in `F̂_P`. -/
theorem denseRange_completionEmbedding_holomorphyRing_pi {S T : Set (Place k F)}
    (hST : Disjoint S T) (hSTu : S ∪ T ≠ Set.univ) :
    DenseRange fun x : holomorphyRing S ↦ fun P : T ↦ P.val.completionEmbedding x := by
  classical
  refine denseRange_pi_subtype_of_forall_finset fun J hJT u hu ↦ ?_
  -- Each `u P` with `P ∈ J` contains a filtration coset of some order `b P` around some point
  -- `g P`; choose `z P ∈ F` within that order of `g P`.
  have hb (P : T) : ∃ (g : P.val.Completion) (b : ℤ), P.val ∈ J →
      ∀ y, y - g ∈ P.val.completionPlace.filtration b → y ∈ u P := by
    by_cases hP : P.val ∈ J
    · obtain ⟨g, hg⟩ := (hu P hP).2
      obtain ⟨b, hb⟩ := P.val.exists_forall_sub_mem_completionPlace_filtration_mem
        ((hu P hP).1.mem_nhds hg)
      exact ⟨g, b, fun _ ↦ hb⟩
    · exact ⟨0, 0, fun h ↦ (hP h).elim⟩
  choose g b hb using hb
  choose z hz using fun P : T ↦ P.val.exists_sub_completionEmbedding_mem_filtration (g P) (b P)
  -- Strong approximation of the `z P` to order `b P` on `J`, regular on `S`.
  have hSJ : S ∪ J ≠ Set.univ := fun h ↦
    hSTu (Set.eq_univ_of_univ_subset (h ▸ Set.union_subset_union_right S hJT))
  obtain ⟨x, hxJ, hxS⟩ := exists_forall_mem_valuation_sub_le_and_forall_mem_integers hF hex hSJ
    Set.subset_union_right (fun Q ↦ if h : Q ∈ T then z ⟨Q, h⟩ else 0)
    (fun Q ↦ if h : Q ∈ T then b ⟨Q, h⟩ else 0)
  have hxO : x ∈ holomorphyRing S := mem_holomorphyRing_iff.2 fun Q hQ ↦
    hxS Q (Or.inl hQ) fun h ↦ hST.notMem_of_mem_left hQ (hJT h)
  refine ⟨⟨x, hxO⟩, fun P hP ↦ hb P hP _ ?_⟩
  -- `x - z P` and `z P - g P` both have order at least `b P` at `P`.
  have hxz := hxJ P.val hP
  simp only [P.property, ↓reduceDIte] at hxz
  have hxz' : P.val.completionEmbedding (x - z P) ∈ P.val.completionPlace.filtration (b P) :=
    P.val.completionEmbedding_mem_filtration_iff.2 (P.val.mem_filtration_iff.2 hxz)
  have h := add_mem hxz' (neg_mem (hz P))
  rwa [map_sub, neg_sub, sub_add_sub_cancel] at h

include hF hex in
/-- **Strong approximation for finite modules over a holomorphy ring.** Let `S` and `T` be
disjoint sets of places of `F / k` which together miss at least one place. Then a finite module
`M` over the holomorphy ring `𝒪_S` is dense in the product of its scalar extensions `F̂_P ⊗ M`
over `P ∈ T`, each with its module topology. -/
theorem denseRange_one_tmul_holomorphyRing_pi {S T : Set (Place k F)}
    (hST : Disjoint S T) (hSTu : S ∪ T ≠ Set.univ) (M : Type*) [AddCommMonoid M]
    [Module (holomorphyRing S) M] [Module.Finite (holomorphyRing S) M]
    [∀ P : T, TopologicalSpace (P.val.Completion ⊗[holomorphyRing S] M)]
    [∀ P : T, IsModuleTopology P.val.Completion (P.val.Completion ⊗[holomorphyRing S] M)] :
    DenseRange fun m : M ↦ fun P : T ↦ (1 : P.val.Completion) ⊗ₜ[holomorphyRing S] m :=
  DenseRange.pi_one_tmul (A := fun P : T ↦ P.val.Completion)
    (by simpa only [Subalgebra.algebraMap_eq, RingHom.comp_apply, AlgHom.coe_toRingHom,
        Subalgebra.coe_val, algebraMap_completion] using
      denseRange_completionEmbedding_holomorphyRing_pi hF hex hST hSTu) M

end Place

end TauCeti
