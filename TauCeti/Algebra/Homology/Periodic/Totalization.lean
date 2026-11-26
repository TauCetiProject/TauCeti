/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.ComplexShape.ZMod
public import TauCeti.Algebra.Homology.HomotopyCategory.Bounded.Generation
public import TauCeti.Algebra.Homology.Periodic.Acyclic
public import TauCeti.Algebra.Homology.TotalComplex.AcyclicAssembly
public import TauCeti.Algebra.Homology.TotalComplex.Additive

/-!
# Totalization of periodic double complexes

Let `K` be a double complex `X^(p,q)` with `p ∈ ℤ` and `q ∈ ZMod n`, that is, a cochain complex
`HomologicalComplex₂ C (ComplexShape.up ℤ) (ComplexShape.up (ZMod n))` whose terms `K.X p` are
`n`-periodic complexes `X^(p,•)` and whose differentials `d_h : X^(p,q) ⟶ X^(p+1,q)` are maps of
periodic complexes. With the total complex shape
`ComplexShape.totalComplexShapeUpIntUpZMod`, its total complex is the `n`-periodic complex with
`Tot^r = ⨁_(p + q = r) X^(p,q)` and differential `d_h + (-1)^p d_v` on `X^(p,q)`. When only
finitely many of the periodic complexes `K.X p` are nonzero, each of these sums is finite, so the
total complex exists in any category with finite coproducts
(`HomologicalComplex₂.hasTotal_zmod_of_bounded`). Such double complexes are the bounded cochain
complexes `CochainComplex.Bounded (CochainComplex C (ZMod n))`, and totalization is an additive
functor on them (`TauCeti.PeriodicComplex.totalizationFunctor`).

In an abelian category, a bounded double complex whose periodic complexes `K.X p` are all acyclic
has an acyclic total complex (`HomologicalComplex₂.acyclic_total_zmod_of_bounded`). As for
double complexes indexed by `ℤ × ℤ` (`HomologicalComplex₂.acyclic_total_of_finite_antidiagonals`),
the proof splits off one column at a time by the degreewise split short exact sequences
`σ^{≥ a + 1} K ⟶ K ⟶ σ^{≤ a} K` of brutal truncations, and uses that a double complex
concentrated in the column `c` has as total complex that column shifted by `-c`
(`HomologicalComplex₂.shiftIsoTotalZModOfIsZero`), for the shift of periodic complexes.

## Main definitions and results

* `HomologicalComplex₂.hasTotal_zmod_of_bounded`: a double complex of periodic complexes with
  finitely many nonzero columns has a total complex.
* `HomologicalComplex₂.shiftIsoTotalZModOfIsZero`: the total complex of a double complex
  concentrated in the column `c` is that column shifted by `-c`.
* `HomologicalComplex₂.acyclic_total_zmod_of_bounded`: the totalization of a bounded double
  complex of acyclic periodic complexes is acyclic.
* `TauCeti.PeriodicComplex.totalizationFunctor`: totalization as an additive functor from bounded
  double complexes of periodic complexes to periodic complexes.

## References

* T. Stai, *The triangulated hull of periodic complexes*, Mathematical Research Letters **25**
  (2018), 199–236, Sections 3.1–3.4.
* C. A. Weibel, *An Introduction to Homological Algebra*, Cambridge University Press, 1994,
  Section 2.7, for the acyclic assembly lemma.
-/

public section

noncomputable section

open CategoryTheory Limits

namespace HomologicalComplex₂

variable {C : Type*} [Category* C] {n : ℕ}

section HasFiniteCoproducts

variable [Preadditive C] [HasFiniteCoproducts C]

/-- A double complex of `n`-periodic complexes with only finitely many nonzero columns `K.X p`
has a total complex: each degree `r` meets each column in the single term `(p, r - p)`. -/
lemma hasTotal_zmod_of_bounded
    {K : HomologicalComplex₂ C (ComplexShape.up ℤ) (ComplexShape.up (ZMod n))}
    (hK : CochainComplex.bounded _ K) : K.HasTotal (ComplexShape.up (ZMod n)) := fun r ↦ by
  obtain ⟨s, hs⟩ := (CochainComplex.bounded_iff_exists_finset_isZero_X _ K).1 hK
  refine TauCeti.hasCoproduct_of_finite_setOf_not_isZero _
    ((s.finite_toSet.preimage (f := fun x : ComplexShape.π (ComplexShape.up ℤ)
      (ComplexShape.up (ZMod n)) (ComplexShape.up (ZMod n)) ⁻¹' {r} ↦ x.val.fst) ?_).subset ?_)
  · rintro ⟨⟨p, q⟩, hpq⟩ - ⟨⟨p', q'⟩, hpq'⟩ - (rfl : p = p')
    simp only [Set.mem_preimage, Set.mem_singleton_iff, ComplexShape.π_up_int_up_zmod] at hpq hpq'
    obtain rfl : q = q' := add_left_cancel (hpq.trans hpq'.symm)
    rfl
  · rintro ⟨⟨p, q⟩, hpq⟩ h
    by_contra hp
    exact h ((HomologicalComplex.eval C _ q).map_isZero (hs p hp))

/-- A double complex of `n`-periodic complexes whose columns vanish outside `[a, b]` has a total
complex. -/
lemma hasTotal_zmod_of_isZero_X
    (L : HomologicalComplex₂ C (ComplexShape.up ℤ) (ComplexShape.up (ZMod n))) (a b : ℤ)
    (hL : ∀ p, p < a ∨ b < p → IsZero (L.X p)) : L.HasTotal (ComplexShape.up (ZMod n)) :=
  hasTotal_zmod_of_bounded <| (CochainComplex.bounded_iff_exists_finset_isZero_X _ L).2
    ⟨Finset.Icc a b, fun p hp ↦ hL p (by
      simp only [Finset.mem_Icc, not_and_or, not_le] at hp
      omega)⟩

end HasFiniteCoproducts

section Preadditive

variable [Preadditive C]
  (L : HomologicalComplex₂ C (ComplexShape.up ℤ) (ComplexShape.up (ZMod n)))
  [L.HasTotal (ComplexShape.up (ZMod n))] (c : ℤ) (hL : ∀ p, p ≠ c → IsZero (L.X p))

/-- On the term `(p, q)`, the differential of the total complex of a double complex of
`n`-periodic complexes is `d_h + (-1)^p d_v`. -/
lemma ιTotal_zmod_d (p : ℤ) (q r r' : ZMod n)
    (h : ComplexShape.π (ComplexShape.up ℤ) (ComplexShape.up (ZMod n)) (ComplexShape.up (ZMod n))
      (p, q) = r) (h' : r + 1 = r') :
    L.ιTotal (ComplexShape.up (ZMod n)) p q r h ≫ (L.total (ComplexShape.up (ZMod n))).d r r' =
      (L.d p (p + 1)).f q ≫ L.ιTotal (ComplexShape.up (ZMod n)) (p + 1) q r' (by
        subst h h'
        simp only [ComplexShape.π_up_int_up_zmod, Int.cast_add, Int.cast_one]
        abel) +
      p.negOnePow • ((L.X p).d q (q + 1) ≫ L.ιTotal (ComplexShape.up (ZMod n)) p (q + 1) r' (by
        subst h h'
        simp only [ComplexShape.π_up_int_up_zmod]
        abel)) := by
  simp [total_d, d₁_eq L (ComplexShape.up (ZMod n)) (rfl : (ComplexShape.up ℤ).Rel p (p + 1)) q r'
    (by subst h h'; simp only [ComplexShape.π_up_int_up_zmod, Int.cast_add, Int.cast_one]; abel),
    d₂_eq L (ComplexShape.up (ZMod n)) p (rfl : (ComplexShape.up (ZMod n)).Rel q (q + 1)) r'
    (by subst h h'; simp only [ComplexShape.π_up_int_up_zmod]; abel)]

include hL in
/-- In a double complex of `n`-periodic complexes concentrated in the column `c`, the inclusion of
the term `(c, q)` into the total complex in degree `c + q` is an isomorphism. -/
lemma isIso_ιTotal_zmod_of_isZero {q r : ZMod n}
    (h : ComplexShape.π (ComplexShape.up ℤ) (ComplexShape.up (ZMod n)) (ComplexShape.up (ZMod n))
      (c, q) = r) :
    IsIso (L.ιTotal (ComplexShape.up (ZMod n)) c q r h) :=
  Cofan.IsColimit.isIso_inj_of_isInitial (L.toGradedObject.isColimitCofanMapObj _ r) _
    fun ⟨⟨p, q'⟩, hpq⟩ hne ↦ by
      have hp : p ≠ c := by
        rintro rfl
        simp only [Set.mem_preimage, Set.mem_singleton_iff, ComplexShape.π_up_int_up_zmod]
          at h hpq
        exact hne (Subtype.ext (Prod.ext rfl (add_left_cancel (hpq.trans h.symm))))
      exact ((HomologicalComplex.eval C _ q').map_isZero (hL p hp)).isInitial

/-- The total complex of a double complex of `n`-periodic complexes concentrated in the column `c`
is that column shifted by `-c`: in degree `r` the isomorphism is the inclusion of the term
`(c, r - c)`. The sign `(-1)ᶜ` of the total differential on the column `c` is the sign of the
differential of the shift by `-c`. -/
def shiftIsoTotalZModOfIsZero :
    (L.X c)⟦-c⟧ ≅ L.total (ComplexShape.up (ZMod n)) :=
  HomologicalComplex.Hom.isoOfComponents
    (fun r ↦
      have := L.isIso_ιTotal_zmod_of_isZero c hL (q := r + ((-c : ℤ) : ZMod n)) (r := r)
        (by simp)
      asIso (L.ιTotal (ComplexShape.up (ZMod n)) c (r + ((-c : ℤ) : ZMod n)) r _))
    (by
      rintro r _ rfl
      have hc : IsZero ((L.X (c + 1)).X (r + ((-c : ℤ) : ZMod n))) :=
        (HomologicalComplex.eval C _ _).map_isZero (hL _ (by omega))
      have h₁ : (ComplexShape.up ℤ).Rel c (c + 1) := rfl
      have h₁' : ComplexShape.π (ComplexShape.up ℤ) (ComplexShape.up (ZMod n))
          (ComplexShape.up (ZMod n)) (c + 1, r + ((-c : ℤ) : ZMod n)) = r + 1 := by
        simp only [ComplexShape.π_up_int_up_zmod, Int.cast_add, Int.cast_one, Int.cast_neg]
        abel
      have h₂ : (ComplexShape.up (ZMod n)).Rel (r + ((-c : ℤ) : ZMod n))
          (r + 1 + ((-c : ℤ) : ZMod n)) := by
        simp only [ComplexShape.up_Rel]
        abel
      have h₂' : ComplexShape.π (ComplexShape.up ℤ) (ComplexShape.up (ZMod n))
          (ComplexShape.up (ZMod n)) (c, r + 1 + ((-c : ℤ) : ZMod n)) = r + 1 := by
        simp only [ComplexShape.π_up_int_up_zmod, Int.cast_neg]
        abel
      simp [total_d, d₁_eq L _ h₁ _ _ h₁', hc.eq_of_tgt ((L.d c (c + 1)).f _) 0,
        d₂_eq L _ c h₂ _ h₂', Int.negOnePow_neg])

/-- In degree `r`, the isomorphism `shiftIsoTotalZModOfIsZero` is the inclusion of the term
`(c, r - c)` into the total complex. -/
@[simp]
lemma shiftIsoTotalZModOfIsZero_hom_f (r : ZMod n) :
    (L.shiftIsoTotalZModOfIsZero c hL).hom.f r =
      L.ιTotal (ComplexShape.up (ZMod n)) c (r + ((-c : ℤ) : ZMod n)) r (by simp) := by
  simp [shiftIsoTotalZModOfIsZero]

include hL in
/-- The total complex of a double complex of `n`-periodic complexes concentrated in the column `c`
is acyclic when that column is. -/
lemma acyclic_total_zmod_of_isZero (hc : (L.X c).Acyclic) :
    (L.total (ComplexShape.up (ZMod n))).Acyclic := fun r ↦
  (((TauCeti.PeriodicComplex.shift_acyclic_iff C n _ (-c)).2 hc) r).of_iso
    (L.shiftIsoTotalZModOfIsZero c hL)

end Preadditive

section Abelian

variable [Abelian C]

/-- **Totalization of acyclic periodic complexes.** In an abelian category, let `K` be a double
complex of `n`-periodic complexes `K.X p`, only finitely many of them nonzero. If every `K.X p` is
acyclic, then the total complex of `K` is acyclic. -/
theorem acyclic_total_zmod_of_bounded
    (K : HomologicalComplex₂ C (ComplexShape.up ℤ) (ComplexShape.up (ZMod n)))
    [K.HasTotal (ComplexShape.up (ZMod n))] (hK : CochainComplex.bounded _ K)
    (hc : ∀ p, (K.X p).Acyclic) : (K.total (ComplexShape.up (ZMod n))).Acyclic := by
  refine CochainComplex.bounded_induction
    (motive := fun (L : HomologicalComplex₂ C (ComplexShape.up ℤ) (ComplexShape.up (ZMod n))) ↦
      ∀ [L.HasTotal (ComplexShape.up (ZMod n))], (∀ p, (L.X p).Acyclic) →
        (L.total (ComplexShape.up (ZMod n))).Acyclic)
    ?_ ?_ K hK hc
  · intro L hL _ _ r
    refine ShortComplex.exact_of_isZero_X₂ _ ?_
    rw [IsZero.iff_id_eq_zero]
    exact total.hom_ext _ fun p q h ↦ ((HomologicalComplex.eval C _ q).map_isZero
      ((HomologicalComplex.eval _ _ p).map_isZero hL)).eq_of_src _ _
  · -- Split off the top column `b + 1` by the short exact sequence `σ^{≥ b + 1} L ⟶ L ⟶ σ^{≤ b} L`.
    intro L b hL _ ih _ hc
    have h₁ : ∀ p, p ≠ b + 1 →
        IsZero ((L.stupidTrunc (ComplexShape.embeddingUpIntGE (b + 1))).X p) := by
      intro p hp
      rcases lt_or_gt_of_ne hp with hp | hp
      · exact CochainComplex.isZero_stupidTrunc_embeddingUpIntGE_X L (b + 1) hp
      · exact L.isZero_stupidTrunc_X_of_isZero _ (CochainComplex.isZero_of_isStrictlyLE L _ p hp)
    have := hasTotal_zmod_of_isZero_X _ (b + 1) (b + 1) fun p hp ↦ h₁ p (by omega)
    have := hasTotal_zmod_of_bounded (CochainComplex.bounded_stupidTrunc_embeddingUpIntLE hL b)
    exact (totalShortComplex_shortExact (ComplexShape.up (ZMod n))
      (CochainComplex.stupidTruncShortComplex L b)
      fun p q ↦ (CochainComplex.stupidTruncShortComplexSplitting L b p).map _).acyclic_X₂
      (acyclic_total_zmod_of_isZero _ (b + 1) h₁ (L.acyclic_stupidTrunc_X _ hc (b + 1)))
      (ih (L.acyclic_stupidTrunc_X _ hc))

end Abelian

end HomologicalComplex₂

namespace TauCeti.PeriodicComplex

variable (C : Type*) [Category* C] [Preadditive C] [HasFiniteCoproducts C] (n : ℕ)

instance (K : CochainComplex.Bounded (CochainComplex C (ZMod n))) :
    HomologicalComplex₂.HasTotal K.obj (ComplexShape.up (ZMod n)) :=
  HomologicalComplex₂.hasTotal_zmod_of_bounded K.property

/-- The totalization of bounded double complexes of `n`-periodic complexes: a cochain complex
`K` of `n`-periodic complexes with finitely many nonzero terms is sent to the `n`-periodic complex
with `⨁_(p + q = r) (K.X p).X q` in degree `r` and differential `d_h + (-1)^p d_v` on
`(K.X p).X q`. -/
def totalizationFunctor :
    CochainComplex.Bounded (CochainComplex C (ZMod n)) ⥤ CochainComplex C (ZMod n) where
  obj K := HomologicalComplex₂.total K.obj (ComplexShape.up (ZMod n))
  map f := HomologicalComplex₂.total.map f.hom _
  map_id K := HomologicalComplex₂.total.map_id K.obj _
  map_comp f g := HomologicalComplex₂.total.map_comp f.hom g.hom _

/-- The totalization functor sends a bounded double complex to its total complex. -/
@[simp]
lemma totalizationFunctor_obj (K : CochainComplex.Bounded (CochainComplex C (ZMod n))) :
    (totalizationFunctor C n).obj K = HomologicalComplex₂.total K.obj (ComplexShape.up (ZMod n)) :=
  (rfl)

/-- The totalization functor acts on a morphism of bounded double complexes by the induced map of
total complexes, after transporting along the object equations. -/
@[simp]
lemma totalizationFunctor_map {K L : CochainComplex.Bounded (CochainComplex C (ZMod n))}
    (f : K ⟶ L) :
    (totalizationFunctor C n).map f =
      eqToHom (totalizationFunctor_obj C n K) ≫
        HomologicalComplex₂.total.map f.hom (ComplexShape.up (ZMod n)) ≫
          eqToHom (totalizationFunctor_obj C n L).symm := by
  -- Unfold the map field and identify the transports along its definitional object equations
  -- with identities. Simplification alone cannot eliminate the opaque equality proofs.
  change HomologicalComplex₂.total.map f.hom _ =
    𝟙 _ ≫ HomologicalComplex₂.total.map f.hom _ ≫ 𝟙 _
  simp

instance : (totalizationFunctor C n).Additive where
  map_add {_ _ f g} := HomologicalComplex₂.total.map_add f.hom g.hom _

end TauCeti.PeriodicComplex
