/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.RealAlgebraic.CAD.Existence
public import TauCeti.Geometry.RealAlgebraic.Semialgebraic.Image
public import TauCeti.Geometry.RealAnalytic.Semianalytic.PartiallySemialgebraic

/-!
# Projections of partially semialgebraic sets

A set `s ⊆ E × (ι → ℝ)` is partially semialgebraic when, over a neighbourhood `U` of every base
point, it is a finite Boolean combination of sign conditions on functions `(u, x) ↦ ∑ₘ aₘ(u) xᵐ`
that are polynomial in the fibre coordinates `x`, with coefficients `aₘ` analytic on `U`
(`TauCeti.IsPartiallySemialgebraic`). This file proves that the class is closed under projection
along finitely many fibre coordinates, and that projecting away all fibre coordinates gives a
semianalytic subset of the base.

The proof separates the coefficients from the polynomials. Replacing every coefficient `aₘ` by a
new variable turns a presentation into a semialgebraic set `S`, and the original set is recovered
as the set of points `(u, x)` such that `(a(u), x) ∈ S`. The projection of `S` along the forgotten
coordinates is semialgebraic by the Tarski–Seidenberg theorem, and substituting the same analytic
coefficients `a(u)` into it describes the projection of the original set. So a single
semialgebraic set, chosen once for the whole neighbourhood, describes the projection there; no
choice is made base point by base point.

## Main results

* `TauCeti.IsAnalyticCoeffBooleanCombination.image_prodMap_comp_inl`: the projection forgetting
  finitely many fibre coordinates of a Boolean combination of analytic-coefficient polynomial sign
  conditions on `U` is again one.
* `TauCeti.PartiallySemialgebraicAt.image_prodMap_comp_inl` and
  `TauCeti.IsPartiallySemialgebraic.image_prodMap_comp_inl`: projections of partially
  semialgebraic sets along finitely many fibre coordinates are partially semialgebraic.
* `TauCeti.PartiallySemialgebraicAt.semianalyticAt_image_fst` and
  `TauCeti.IsPartiallySemialgebraic.isSemianalytic_image_fst`: the projection to the base of a
  partially semialgebraic set with finitely many fibre coordinates is semianalytic.

## References

S. Łojasiewicz, *Triangulation of semi-analytic sets*, Annali della Scuola Normale Superiore di Pisa
(3) 18 (1964), 449–474, §1, for partially semialgebraic sets and their projections.
-/

public section

open MvPolynomial Set

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {ι κ : Type*}

/-- **Separating the coefficients.** A Boolean combination `t` of analytic-coefficient polynomial
sign conditions on `U` is the set of points `(u, x)` such that `(c u, x)` lies in a semialgebraic
set `S`, for some functions `c · a` analytic on `U`. The coordinates `a = (i, d)` index the
coefficient of the monomial `d` in the `i`-th polynomial of a sign-condition presentation of `t`. -/
private theorem IsAnalyticCoeffBooleanCombination.exists_eq_setOf_sumElim_mem {U : Set E}
    {t : Set (E × (ι → ℝ))} (ht : IsAnalyticCoeffBooleanCombination U t) :
    ∃ (m : ℕ) (c : E → Fin m × (ι →₀ ℕ) → ℝ), (∀ a, AnalyticOnNhd ℝ (c · a) U) ∧
      ∃ S : Set (Fin m × (ι →₀ ℕ) ⊕ ι → ℝ), IsSemialgebraic S ∧
        t = {p | Sum.elim (c p.1) p.2 ∈ S} := by
  classical
  obtain ⟨m, f, hf, Φ, rfl⟩ := ht.exists_eq_setOf_sign
  have hf' := fun i => isAnalyticCoeffPolynomialOn_def.1 (hf i)
  choose P hP hfP using hf'
  -- The polynomial `P i` with each coefficient `(P i).coeff d` replaced by the variable
  -- `Sum.inl (i, d)`.
  let Q : Fin m → MvPolynomial (Fin m × (ι →₀ ℕ) ⊕ ι) ℝ := fun i =>
    ∑ d ∈ (P i).support, X (Sum.inl (i, d)) * rename Sum.inr (monomial d 1)
  refine ⟨m, fun u a => (P a.1).coeff a.2 u, fun a => hP a.1 a.2, _,
    isSemialgebraic_setOf_sign_eval Q Φ, ?_⟩
  ext p
  have hQ (i : Fin m) :
      f i p = eval (Sum.elim (fun a => (P a.1).coeff a.2 p.1) p.2) (Q i) := by
    simp [Q, hfP, eval₂_eq, eval_rename, eval_monomial, Finsupp.prod]
  simp only [mem_ofPred_eq, hQ]

/-- **Projection along the fibre.** If `t ⊆ E × (ι ⊕ κ → ℝ)` is a Boolean combination of
analytic-coefficient polynomial sign conditions on `U`, then so is its projection to
`E × (ι → ℝ)` forgetting the finitely many fibre coordinates `κ`. -/
theorem IsAnalyticCoeffBooleanCombination.image_prodMap_comp_inl [Finite κ] {U : Set E}
    {t : Set (E × (ι ⊕ κ → ℝ))} (ht : IsAnalyticCoeffBooleanCombination U t) :
    IsAnalyticCoeffBooleanCombination U (Prod.map id (fun x : ι ⊕ κ → ℝ => x ∘ Sum.inl) '' t) := by
  obtain ⟨m, c, hc, S, hS, rfl⟩ := ht.exists_eq_setOf_sumElim_mem
  -- Regroup the coordinates `A ⊕ (ι ⊕ κ)` of `S` as `(A ⊕ ι) ⊕ κ`, and forget `κ`.
  have hS' := (hS.preimage_comp (Equiv.sumAssoc _ ι κ).symm).image_comp_inl
  convert hS'.isAnalyticCoeffBooleanCombination_preimage_sumElim hc using 1
  ext ⟨u, y⟩
  simp only [mem_image, mem_ofPred_eq, mem_preimage, Prod.exists, Prod.map_apply, id_eq,
    Prod.mk.injEq]
  constructor
  · rintro ⟨u', x, hx, hu, rfl⟩
    rw [hu] at hx
    refine ⟨Sum.elim (Sum.elim (c u) (x ∘ Sum.inl)) (x ∘ Sum.inr), ?_, rfl⟩
    convert hx using 1
    ext (a | i | k) <;> rfl
  · rintro ⟨v, hv, hvy⟩
    refine ⟨u, fun j => v ((Equiv.sumAssoc _ ι κ).symm (Sum.inr j)), ?_, rfl, ?_⟩
    · convert hv using 1
      ext (a | j)
      · exact (congrFun hvy (Sum.inl a)).symm
      · rfl
    · ext i
      exact congrFun hvy (Sum.inr i)

/-- **Projection along the fibre.** If `s ⊆ E × (ι ⊕ κ → ℝ)` is partially semialgebraic over `u`,
then so is its projection to `E × (ι → ℝ)` forgetting the finitely many fibre coordinates `κ`. -/
theorem PartiallySemialgebraicAt.image_prodMap_comp_inl [Finite κ] {s : Set (E × (ι ⊕ κ → ℝ))}
    {u : E} (hs : PartiallySemialgebraicAt s u) :
    PartiallySemialgebraicAt (Prod.map id (fun x : ι ⊕ κ → ℝ => x ∘ Sum.inl) '' s) u := by
  obtain ⟨U, hU, t, ht, hst⟩ := partiallySemialgebraicAt_def.1 hs
  refine partiallySemialgebraicAt_def.2 ⟨U, hU, _, ht.image_prodMap_comp_inl, ?_⟩
  -- The projection does not move base points, so it commutes with restricting to `U`.
  have h (r : Set (E × (ι ⊕ κ → ℝ))) :
      Prod.map id (fun x : ι ⊕ κ → ℝ => x ∘ Sum.inl) '' r ∩ Prod.fst ⁻¹' U =
        Prod.map id (fun x : ι ⊕ κ → ℝ => x ∘ Sum.inl) '' (r ∩ Prod.fst ⁻¹' U) :=
    (image_inter_preimage _ _ _).symm
  rw [h, h, hst]

/-- **Projection along the fibre.** The projection of a partially semialgebraic set
`s ⊆ E × (ι ⊕ κ → ℝ)` to `E × (ι → ℝ)`, forgetting the finitely many fibre coordinates `κ`, is
partially semialgebraic. -/
theorem IsPartiallySemialgebraic.image_prodMap_comp_inl [Finite κ] {s : Set (E × (ι ⊕ κ → ℝ))}
    (hs : IsPartiallySemialgebraic s) :
    IsPartiallySemialgebraic (Prod.map id (fun x : ι ⊕ κ → ℝ => x ∘ Sum.inl) '' s) :=
  isPartiallySemialgebraic_iff.2 fun u => (hs.partiallySemialgebraicAt u).image_prodMap_comp_inl

/-- **Projection to the base.** If `s ⊆ E × (κ → ℝ)`, with finitely many fibre coordinates, is
partially semialgebraic over `u`, then its projection `Prod.fst '' s` to the base is semianalytic
at `u`. -/
theorem PartiallySemialgebraicAt.semianalyticAt_image_fst [Finite κ] {s : Set (E × (κ → ℝ))}
    {u : E} (hs : PartiallySemialgebraicAt s u) : SemianalyticAt (Prod.fst '' s) u := by
  obtain ⟨U, hU, t, ht, hst⟩ := partiallySemialgebraicAt_def.1 hs
  obtain ⟨m, c, hc, S, hS, rfl⟩ := ht.exists_eq_setOf_sumElim_mem
  refine semianalyticAt_def.2
    ⟨U, hU, _, hS.image_comp_inl.isAnalyticBooleanCombination_preimage hc, ?_⟩
  have h : Prod.fst '' {p : E × (κ → ℝ) | Sum.elim (c p.1) p.2 ∈ S} =
      c ⁻¹' ((fun z => z ∘ Sum.inl) '' S) := by
    ext v
    simp only [mem_image, mem_ofPred_eq, mem_preimage, Prod.exists, exists_and_right,
      exists_eq_right]
    constructor
    · rintro ⟨x, hx⟩
      exact ⟨_, hx, rfl⟩
    · rintro ⟨z, hz, hzc⟩
      refine ⟨z ∘ Sum.inr, ?_⟩
      convert hz using 1
      ext (a | k)
      · exact (congrFun hzc a).symm
      · rfl
  rw [← h, ← image_inter_preimage, hst, image_inter_preimage]

/-- **Projection to the base.** The projection `Prod.fst '' s` to the base of a partially
semialgebraic set `s ⊆ E × (κ → ℝ)`, with finitely many fibre coordinates, is semianalytic. -/
theorem IsPartiallySemialgebraic.isSemianalytic_image_fst [Finite κ] {s : Set (E × (κ → ℝ))}
    (hs : IsPartiallySemialgebraic s) : IsSemianalytic (Prod.fst '' s) :=
  isSemianalytic_iff.2 fun u => (hs.partiallySemialgebraicAt u).semianalyticAt_image_fst

end TauCeti
