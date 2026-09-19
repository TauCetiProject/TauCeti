/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import TauCeti.AlgebraicGeometry.AdicSpace.Spa.RationalSubset.Basic
public import TauCeti.AlgebraicGeometry.AdicSpace.Spa.Support

import TauCeti.AlgebraicGeometry.AdicSpace.Spa.RationalSubset.Basis
import TauCeti.RingTheory.Huber.OpenIdeal
import TauCeti.RingTheory.Valuation.ValuativeRel.BigOperators

/-!
# Standard rational refinements of covers of the adic spectrum

**Wedhorn, *Adic Spaces* (arXiv:1910.05934v1), Lemma 7.54**, which is Huber's Lemma 2.6.

A finite set `S` generating the unit ideal gives the *standard rational cover* `(R(S/f))_{f ∈ S}` of
`Spa (A, A⁺)` (Corollary 7.53). Lemma 7.54 says that an open cover of the adic spectrum has a
standard rational refinement: some `S` generating the unit ideal with every `R(S/f)` inside a member
of the cover.

Huber's proof multiplies presentations together. Let rational subsets `R(Tᵢ/sᵢ)` cover
`Spa (A, A⁺)`; since `Spa (A, A⁺)` is quasi-compact, finitely many of them suffice. Let `S` consist
of the products `∏ᵢ tᵢ` with `tᵢ ∈ Tᵢ ∪ {sᵢ}` for every `i` and `tₖ = sₖ` for at least one `k`. For
such a product, `R(S/∏ᵢ tᵢ) ⊆ R(Tₖ/sₖ)`. A point `v` of the left-hand side lies in some
`R(Tₗ/sₗ)`, so putting `sₗ` in the `l`-th slot does not lower the value of the product at `v`. Once
`sₗ` is in the `l`-th slot, the `k`-th slot may hold any `t ∈ Tₖ`, and comparing with `∏ᵢ tᵢ`
bounds `v(t)` by `v(sₖ)`. No point kills all of `S`, so `S` generates the unit ideal by Corollary
7.53.

That last step uses, at each point, an element of every `Tᵢ` that the point does not kill, which is
automatic when every `Tᵢ` generates the unit ideal. In a Tate ring every open ideal is the unit
ideal, so every rational subset has such a presentation.

## Main results

* `TauCeti.ValuationSpectrum.exists_span_eq_top_forall_rationalSubset_subset` : a cover of
  `Spa (A, A⁺)` by rational subsets `R(Tᵢ/sᵢ)`, each `Tᵢ` generating the unit ideal, has a standard
  rational refinement.
* `TauCeti.ValuationSpectrum.exists_span_eq_top_forall_rationalSubset_subset_of_isTateRing` :
  **Wedhorn Lemma 7.54** over a complete Hausdorff Tate ring, for an arbitrary open cover.

## References

* [T. Wedhorn, *Adic Spaces*][wedhorn_adic] (arXiv:1910.05934v1), Corollary 7.53 and Lemma 7.54.
* R. Huber, *A generalization of formal schemes and rigid analytic varieties*, Math. Z. 217 (1994),
  Lemma 2.6.
* [AINTLIB](https://github.com/CBirkbeck/AINTLIB), branch `dev/adic-spaces`, at commit `37bbdaeb9`,
  `projects/AdicSpaces/Adic spaces/WedhornCechAcyclicity.lean`, section "Lemma 7.54".

## Provenance

AINTLIB (`github.com/CBirkbeck/AINTLIB` @ `37bbdaeb9`, Apache-2.0) carries out Huber's construction
as `distinguishedProducts`, over a list of presentations each containing `1` among its numerators,
and proves the refinement through the identity `R(P/∏ᵢ tᵢ) = ⋂ᵢ R(Tᵢ/tᵢ)` for the set `P` of all
products. Here the presentations form an arbitrary family, cut down to a finite one by
quasi-compactness, each numerator set is only assumed to generate the unit ideal, and the
containment is proved directly by the two slot replacements described above; no AINTLIB code is
copied.
-/

public section

namespace TauCeti.ValuationSpectrum

open TauCeti.Huber

variable {A : Type*} [CommRing A]

section Products

variable {ι : Type*} [DecidableEq A] [Fintype ι] [DecidableEq ι]

/- The products `∏ i, σ i` with `σ i ∈ insert (s i) (T i)` for all `i` and some `σ k = s k`. -/
private def refinementProducts (T : ι → Finset A) (s : ι → A) : Finset A :=
  {σ ∈ Fintype.piFinset fun i ↦ insert (s i) (T i) | ∃ i, σ i = s i}.image fun σ ↦ ∏ i, σ i

private theorem mem_refinementProducts {T : ι → Finset A} {s : ι → A} {f : A} :
    f ∈ refinementProducts T s ↔ ∃ σ : ι → A, (∀ i, σ i ∈ insert (s i) (T i)) ∧ (∃ i, σ i = s i) ∧
      ∏ i, σ i = f := by
  simp [refinementProducts, and_assoc]

private theorem prod_update_update_mem_refinementProducts {T : ι → Finset A} {s : ι → A} {σ : ι → A}
    (hσ : ∀ i, σ i ∈ insert (s i) (T i)) {l k : ι} (hlk : l ≠ k) {t : A} (ht : t ∈ T k) :
    ∏ i, Function.update (Function.update σ l (s l)) k t i ∈ refinementProducts T s :=
  mem_refinementProducts.mpr ⟨_, fun i ↦ by grind, ⟨l, by simp [hlk]⟩, rfl⟩

private theorem rationalSubset_refinementProducts_subset [TopologicalSpace A] (Aplus : Subring A)
    {T : ι → Finset A} {s : ι → A} (hcov : spa Aplus ⊆ ⋃ i, rationalSubset Aplus (T i) (s i))
    {σ : ι → A} (hσ : ∀ i, σ i ∈ insert (s i) (T i)) {k : ι} (hk : σ k = s k) :
    rationalSubset Aplus (refinementProducts T s) (∏ i, σ i) ⊆
      rationalSubset Aplus (T k) (s k) := by
  intro v hv
  let _ := v.toValuativeRel
  obtain ⟨hvspa, hvle, hv0 : 0 <ᵥ ∏ i, σ i⟩ := (mem_rationalSubset_iff _ _ _ v).mp hv
  obtain ⟨l, hl⟩ := Set.mem_iUnion.mp (hcov hvspa)
  rcases eq_or_ne l k with rfl | hlk
  · exact hl
  -- putting `s l` in the `l`-th slot does not lower the value of the product
  have hle := ValuativeRel.prod_vle_prod_update (s := Finset.univ) <|
    (Finset.mem_insert.mp (hσ l)).elim (· ▸ .rfl) (((mem_rationalSubset_iff _ _ _ v).mp hl).2.1 _)
  refine (mem_rationalSubset_iff _ _ _ v).mpr ⟨hvspa, fun t ht ↦ ?_,
    hk ▸ ValuativeRel.zero_vlt_prod_iff.mp hv0 k (Finset.mem_univ k)⟩
  -- with `s l` in the `l`-th slot, the `k`-th slot may hold any `t ∈ T k`
  simpa [hk, hlk.symm] using (ValuativeRel.prod_update_vle_prod_iff (fun i hi _ ↦
    ValuativeRel.zero_vlt_prod_iff.mp (hv0.trans_vle hle) i hi) (Finset.mem_univ k)).mp
    ((hvle _ (prod_update_update_mem_refinementProducts hσ hlk ht)).trans hle)

end Products

variable [UniformSpace A] [T2Space A] [CompleteSpace A] [IsTopologicalRing A] [IsUniformAddGroup A]

private theorem span_refinementProducts_eq_top [IsHuberRing A] [DecidableEq A] {ι : Type*}
    [Fintype ι] [DecidableEq ι] (Aplus : Subring A) (hplus : IsRingOfIntegralElements Aplus)
    {T : ι → Finset A} {s : ι → A} (hT : ∀ i, Ideal.span (T i : Set A) = ⊤)
    (hcov : spa Aplus ⊆ ⋃ i, rationalSubset Aplus (T i) (s i)) :
    Ideal.span (refinementProducts T s : Set A) = ⊤ := by
  refine (span_eq_top_iff_forall_mem_spa_exists_notMem_supp Aplus hplus).mpr fun v hv ↦ ?_
  let _ := v.toValuativeRel
  obtain ⟨l, hl⟩ := Set.mem_iUnion.mp (hcov hv)
  -- in every other slot, an element of `T i` that `v` does not kill
  choose r hrT hr using fun i ↦ mem_rationalSubset_of_span_eq_top_of_mem_spa Aplus (hT i) hv
  refine ⟨_, mem_refinementProducts.mpr ⟨Function.update r l (s l), fun i ↦ by grind, ⟨l, by simp⟩,
    rfl⟩, mt (mem_supp_iff v _).mp <| ValuativeRel.zero_vlt_prod_iff.mpr fun i _ ↦ ?_⟩
  grind [mem_rationalSubset_iff]

/-- **A standard rational refinement of a rational cover.** This is Wedhorn Lemma 7.54 (Huber
Lemma 2.6) for a cover of `Spa (A, A⁺)` by rational subsets `R(Tᵢ/sᵢ)` whose numerator sets `Tᵢ`
generate the unit ideal: some finite `S` generating the unit ideal has every `R(S/f)`, `f ∈ S`,
inside one of the `R(Tᵢ/sᵢ)`. The cover may be infinite, since `Spa (A, A⁺)` is quasi-compact. The
`R(S/f)` cover `Spa (A, A⁺)` by `spa_eq_biUnion_rationalSubset_of_span_eq_top`, so they form a
standard rational cover refining the given one.

Wedhorn's rational subsets only ask the numerator ideals `Tᵢ · A` to be open, which is weaker. Over
a Tate ring an open ideal is the unit ideal, and
`exists_span_eq_top_forall_rationalSubset_subset_of_isTateRing` uses this to refine an arbitrary
open cover of `spa Aplus` when `A` is a complete Hausdorff Tate ring. -/
theorem exists_span_eq_top_forall_rationalSubset_subset [IsHuberRing A] (Aplus : Subring A)
    (hplus : IsRingOfIntegralElements Aplus) {ι : Type*} {T : ι → Finset A} {s : ι → A}
    (hT : ∀ i, Ideal.span (T i : Set A) = ⊤)
    (hcov : spa Aplus ⊆ ⋃ i, rationalSubset Aplus (T i) (s i)) :
    ∃ S : Finset A, Ideal.span (S : Set A) = ⊤ ∧
      ∀ f ∈ S, ∃ i, rationalSubset Aplus S f ⊆ rationalSubset Aplus (T i) (s i) := by
  classical
  -- finitely many of the `R(Tᵢ/sᵢ)` already cover, since `Spa (A, A⁺)` is quasi-compact
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover
    (fun i ↦ Subtype.val ⁻¹' rationalSubset Aplus (T i) (s i))
    (fun i ↦ isOpen_val_preimage_rationalSubset Aplus (T i) (s i)) fun v _ ↦
      (Set.mem_iUnion.mp (hcov v.2)).elim fun i hi ↦ Set.mem_iUnion_of_mem i hi
  have hcov' : spa Aplus ⊆ ⋃ i : t, rationalSubset Aplus (T i) (s i) := fun v hv ↦ by
    obtain ⟨i, hi, hvi⟩ := Set.mem_iUnion₂.mp (ht (Set.mem_univ ⟨v, hv⟩))
    exact Set.mem_iUnion.mpr ⟨⟨i, hi⟩, hvi⟩
  -- Huber's products over the finite subcover
  refine ⟨refinementProducts (fun i : t ↦ T i) (fun i ↦ s i),
    span_refinementProducts_eq_top Aplus hplus (fun i ↦ hT i) hcov', fun f hf ↦ ?_⟩
  obtain ⟨σ, hσ, ⟨k, hk⟩, rfl⟩ := mem_refinementProducts.mp hf
  exact ⟨k, rationalSubset_refinementProducts_subset Aplus hcov' hσ hk⟩

/-- **Wedhorn Lemma 7.54** over a complete Hausdorff Tate ring: every open cover of `Spa (A, A⁺)`
has a standard rational refinement, a finite `S` generating the unit ideal with every `R(S/f)`,
`f ∈ S`, inside a member of the cover. The `R(S/f)` cover `Spa (A, A⁺)` by
`spa_eq_biUnion_rationalSubset_of_span_eq_top`. Over any complete Hausdorff Huber ring,
`exists_span_eq_top_forall_rationalSubset_subset` gives such a refinement of a cover by rational
subsets whose numerator sets generate the unit ideal. -/
theorem exists_span_eq_top_forall_rationalSubset_subset_of_isTateRing [IsTateRing A]
    (Aplus : Subring A) (hplus : IsRingOfIntegralElements Aplus) {ι : Type*}
    (V : ι → Set (spa Aplus)) (hV : ∀ i, IsOpen (V i)) (hcov : ⋃ i, V i = Set.univ) :
    ∃ S : Finset A, Ideal.span (S : Set A) = ⊤ ∧
      ∀ f ∈ S, ∃ i, Subtype.val ⁻¹' rationalSubset Aplus S f ⊆ V i := by
  -- each point `x` has a rational neighbourhood `W x`, presented as `R(T x/s x)`, inside a member
  -- `V (j x)` of the cover
  choose j W hW hxW hWV using fun x ↦ (Set.iUnion_eq_univ_iff.mp hcov x).imp fun i hi ↦
    (isTopologicalBasis_spaRationalFamily Aplus).exists_subset_of_mem_open hi (hV i)
  choose T s hT hWT using fun x ↦ mem_spaRationalFamily_iff.mp (hW x)
  obtain rfl := funext hWT
  -- in a Tate ring an open ideal is the unit ideal, so these rational neighbourhoods meet the
  -- hypothesis of `exists_span_eq_top_forall_rationalSubset_subset`
  obtain ⟨S, hS, hsub⟩ := exists_span_eq_top_forall_rationalSubset_subset Aplus hplus
    (fun x ↦ IsTateRing.eq_top_of_isOpen (hT x)) fun v hv ↦ Set.mem_iUnion_of_mem _ (hxW ⟨v, hv⟩)
  exact ⟨S, hS, fun f hf ↦ (hsub f hf).imp' j fun x hx ↦ (Set.preimage_mono hx).trans (hWV x)⟩

end TauCeti.ValuationSpectrum
