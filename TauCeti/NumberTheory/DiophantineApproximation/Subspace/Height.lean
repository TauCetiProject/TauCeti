/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.DiophantineApproximation.Subspace.Span
public import Mathlib.NumberTheory.Height.NumberField
public import TauCeti.NumberTheory.Height.Subspace.Basic
import TauCeti.Analysis.ExteriorPower.Plucker
import TauCeti.LinearAlgebra.Dual.AbsoluteValue
import TauCeti.LinearAlgebra.Matrix.AbsoluteValue
import TauCeti.NumberTheory.DiophantineApproximation.Subspace.Volume
import TauCeti.NumberTheory.Height.NumberField

/-!
# The height of the span of an approximation domain

Let `K` be a number field, and let `V(Q) = approxSpan S₀ L c Q` be the span of the approximation
domain `approxDomain S₀ L c Q`, for forms `L v` linearly independent at every infinite place and
at every place of `S₀`. Write `cMax v = ⨆ i, c v i` for the largest exponent at the place `v`, and

```text
W = ∑ v | ∞, mult v · cMax v + ∑ v ∈ S₀, cMax v.
```

The height of `V(Q)` grows at most like a power of the level: there is `C > 0`, depending only on
`K`, `S₀` and the forms, such that for every exponent family `c` and every `Q ≥ 1`

```text
relativeSubspaceHeight V(Q) ≤ C · Q ^ (dim V(Q) · W).
```

The argument: `V(Q)` has a basis `y` drawn from the domain. At an infinite place, or at a place
of `S₀`, the coordinates of each `y b` are bounded by a constant times `Q ^ cMax v`, because the
forms there are independent; so every Plücker coordinate of `y`, a minor of order `dim V(Q)`, is
bounded by a constant times `Q ^ (dim V(Q) · cMax v)`. At the other finite places the `y b` are
integral, hence so are their Plücker coordinates, and the height of the Plücker point is at most
the product of its local sup norms over the infinite places and `S₀`.

In the proof of the Subspace Theorem this bound holds at every level, without any hypothesis on
the weight of `c`. It is the upper half of the two-sided estimate for the height of a hyperplane
`V(Q)` (`dim V(Q) = #ι - 1`). For exponent families whose weight `W` stays bounded (for instance a
fixed `c`), together with Northcott's theorem for subspaces, it leaves only finitely many candidate
subspaces `V(Q)` at bounded levels. The constant does not depend on `c`, so the bound is uniform
over families of exponents moving with the level.

## Main results

* `TauCeti.NumberField.exists_forall_relativeSubspaceHeight_approxSpan_le`: the bound above.

Its logarithmic form, `h(V(Q)) ≤ dim V(Q) · W · log Q + C`, is
`TauCeti.NumberField.exists_forall_relativeSubspaceLogHeight_approxSpan_le` in
`TauCeti.NumberTheory.DiophantineApproximation.Subspace.Exceptional`.

## References

* E. Bombieri and W. Gubler, *Heights in Diophantine Geometry*, Cambridge University Press (2006),
  Lemma 7.5.21, upper bound.
* J.-H. Evertse and H. P. Schlickewei, *A quantitative version of the absolute subspace theorem*,
  J. reine angew. Math. 548 (2002), Lemma 12.3.
* A version of this bound is formalized in Ralf Stephan's
  `DiophantineApproximation/SubspaceHeightBounds.lean` in `rwst/Subspace-Theorems`, snapshot
  `09835cb` (Apache 2.0).
-/

public section

open Module NumberField Height Submodule

namespace TauCeti.NumberField

variable {K : Type*} [Field K] [NumberField K] {ι : Type*} [LinearOrder ι]

/-- The height of the Plücker point of `p` linearly independent points of an approximation domain
at a level `Q ≥ 1` is at most `C * Q ^ (p * W)`, where `p * W` is the weight of the exponents
`cMax v` repeated `p` times and `C` is assembled from constants `D v` bounding the coordinates by
the values of the forms at the infinite places and at `S₀`. -/
private theorem mulHeight_plucker_le [Fintype ι] {S₀ : Finset (FinitePlace K)}
    {L : AbsoluteValue K ℝ → ι → Dual K (ι → K)}
    (hLInf : ∀ v : InfinitePlace K, LinearIndependent K (L v.val))
    (hLFin : ∀ v ∈ S₀, LinearIndependent K (L v.val)) {D : AbsoluteValue K ℝ → ℝ}
    (hD0 : ∀ v, 0 ≤ D v) (hD : ∀ v, LinearIndependent K (L v) →
      ∀ (x : ι → K) (M : ℝ), (∀ i, v (L v i x) ≤ M) → ∀ j, v (x j) ≤ D v * M)
    {c : AbsoluteValue K ℝ → ι → ℝ} {Q : ℝ} (hQ : 1 ≤ Q) {p : ℕ} (hp : p ≤ Fintype.card ι)
    {y : Fin p → ι → K} (hy : LinearIndependent K y)
    (hyD : ∀ k, y k ∈ approxDomain S₀ L c Q) :
    mulHeight (plucker y) ≤
      ((∏ v : InfinitePlace K,
          ((Fintype.card ι).factorial * max 1 (D v.val) ^ Fintype.card ι) ^ v.mult) *
        ∏ v ∈ S₀, (Fintype.card ι).factorial * max 1 (D v.val) ^ Fintype.card ι) *
        Q ^ approxWeight S₀ (fun v (_ : Fin p) ↦ ⨆ i, c v i) := by
  set E : AbsoluteValue K ℝ → ℝ :=
    fun v ↦ (Fintype.card ι).factorial * max 1 (D v) ^ Fintype.card ι
  have hQ0 : 0 < Q := zero_lt_one.trans_le hQ
  rw [rpow_approxWeight S₀ _ hQ0]
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  -- Local bounds on the Plücker coordinates at the infinite places and at `S₀`.
  have hloc (v : AbsoluteValue K ℝ) (hv : LinearIndependent K (L v))
      (hyv : ∀ k i, v (L v i (y k)) ≤ Q ^ c v i) :
      ⨆ s, v (plucker y s) ≤ E v * (Q ^ ⨆ i, c v i) ^ p := by
    refine Real.iSup_le (fun s ↦ ?_) (by positivity)
    refine (v.plucker_le_factorial_mul_prod_of_row_le (b := fun _ ↦ D v * Q ^ ⨆ i, c v i)
      (fun k j ↦ hD v hv (y k) _ (fun i ↦ (hyv k i).trans <|
        Real.rpow_le_rpow_of_exponent_le hQ (le_ciSup (Finite.bddAbove_range _) i)) j) s).trans ?_
    rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin, mul_pow, ← mul_assoc]
    simp only [E]
    have := hD0 v
    gcongr ?_ * ?_ * _
    · exact_mod_cast Nat.factorial_le hp
    · exact (pow_le_pow_left₀ (hD0 v) (le_max_right 1 _) p).trans
        (pow_le_pow_right₀ (le_max_left 1 _) hp)
  have hinf (v : InfinitePlace K) : ⨆ s, v (plucker y s) ≤ E v.val * (Q ^ ⨆ i, c v.val i) ^ p :=
    hloc v.val (hLInf v) fun k i ↦ (mem_approxDomain.1 (hyD k)).1 v i
  have hfin (v : FinitePlace K) (hv : v ∈ S₀) :
      ⨆ s, v (plucker y s) ≤ E v.val * (Q ^ ⨆ i, c v.val i) ^ p :=
    hloc v.val (hLFin v hv) fun k i ↦ (mem_approxDomain.1 (hyD k)).2.1 v hv i
  -- Off `S₀` the Plücker coordinates are integral.
  have hout (v : FinitePlace K) (hv : v ∉ S₀) (s : Set.powersetCard ι p) :
      v (plucker y s) ≤ 1 := by
    rw [plucker_apply]
    exact Matrix.abv_det_le_one_of_isNonarchimedean (abv := v.val) (FinitePlace.add_le v)
      fun k j ↦ (mem_approxDomain.1 (hyD k)).2.2 v hv _
  have hnn (v : AbsoluteValue K ℝ) : 0 ≤ ⨆ s, v (plucker y s) :=
    Real.iSup_nonneg fun s ↦ apply_nonneg _ _
  calc mulHeight (plucker y)
      ≤ (∏ v : InfinitePlace K, (⨆ s, v (plucker y s)) ^ v.mult) *
          ∏ v ∈ S₀, ⨆ s, v (plucker y s) :=
        mulHeight_le_prod_of_forall_le_one S₀ ((plucker_ne_zero_iff y).2 hy) hout
    _ ≤ (∏ v : InfinitePlace K, (E v.val * (Q ^ ⨆ i, c v.val i) ^ p) ^ v.mult) *
          ∏ v ∈ S₀, E v.val * (Q ^ ⨆ i, c v.val i) ^ p :=
        mul_le_mul (Finset.prod_le_prod₀ (fun v _ ↦ pow_nonneg (hnn v.val) _)
            fun v _ ↦ pow_le_pow_left₀ (hnn v.val) (hinf v) _)
          (Finset.prod_le_prod₀ (fun v _ ↦ hnn v.val) hfin)
          (Finset.prod_nonneg fun v _ ↦ hnn v.val) (Finset.prod_nonneg fun v _ ↦ by positivity)
    _ = _ := by
        simp only [E, mul_pow, Finset.prod_mul_distrib]
        ring

/-- **The height of the span of an approximation domain** (Bombieri–Gubler, Lemma 7.5.21, upper
bound). For forms linearly independent at every infinite place and at every place of `S₀`, there
is `C > 0`, depending only on `K`, `S₀` and the forms, such that for every exponent family `c` and
every level `Q ≥ 1` the relative height of `V(Q) = approxSpan S₀ L c Q` is at most
`C * Q ^ (dim V(Q) * W)`, where `W = ∑ v | ∞, mult v · cMax v + ∑ v ∈ S₀, cMax v` and
`cMax v = ⨆ i, c v i`. -/
theorem exists_forall_relativeSubspaceHeight_approxSpan_le [Finite ι]
    {S₀ : Finset (FinitePlace K)}
    {L : AbsoluteValue K ℝ → ι → Dual K (ι → K)}
    (hLInf : ∀ v : InfinitePlace K, LinearIndependent K (L v.val))
    (hLFin : ∀ v ∈ S₀, LinearIndependent K (L v.val)) :
    ∃ C : ℝ, 0 < C ∧ ∀ (c : AbsoluteValue K ℝ → ι → ℝ) {Q : ℝ}, 1 ≤ Q →
      relativeSubspaceHeight (approxSpan S₀ L c Q) ≤
        C * Q ^ ((finrank K (approxSpan S₀ L c Q) : ℝ) *
          (∑ v : InfinitePlace K, (v.mult : ℝ) * (⨆ i, c v.val i) + ∑ v ∈ S₀, ⨆ i, c v.val i)) := by
  classical
  let _ := Fintype.ofFinite ι
  -- At a place with independent forms, coordinates are bounded by the values of the forms.
  have hcoord (v : AbsoluteValue K ℝ) : ∃ D : ℝ, 0 ≤ D ∧ (LinearIndependent K (L v) →
      ∀ (x : ι → K) (M : ℝ), (∀ i, v (L v i x) ≤ M) → ∀ j, v (x j) ≤ D * M) := by
    by_cases hv : LinearIndependent K (L v)
    · obtain ⟨D, hD0, hD⟩ := hv.exists_forall_abv_apply_le_mul v
      exact ⟨D, hD0, fun _ ↦ hD⟩
    · exact ⟨0, le_rfl, fun h ↦ (hv h).elim⟩
  choose D hD0 hD using hcoord
  refine ⟨(∏ v : InfinitePlace K,
      ((Fintype.card ι).factorial * max 1 (D v.val) ^ Fintype.card ι) ^ v.mult) *
    ∏ v ∈ S₀, (Fintype.card ι).factorial * max 1 (D v.val) ^ Fintype.card ι, by positivity,
    fun c Q hQ ↦ ?_⟩
  -- A basis `y` of `V(Q)` drawn from the domain.
  obtain ⟨b, hbD, hbspan, hbli⟩ := exists_linearIndependent K (approxDomain S₀ L c Q)
  have : Finite b := hbli.setFinite.to_subtype
  obtain ⟨p, ⟨e⟩⟩ := Finite.exists_equiv_fin b
  set y : Fin p → ι → K := Subtype.val ∘ e.symm with hy_def
  have hy : LinearIndependent K y := hbli.comp _ e.symm.injective
  have hrange : Set.range y = b := by
    rw [hy_def, Set.range_comp, e.symm.range_eq_univ, Set.image_univ, Subtype.range_coe]
  have hV : approxSpan S₀ L c Q = span K (Set.range y) := by
    rw [approxSpan_eq_span, ← hbspan, hrange]
  -- The exponent is the weight of the exponents `cMax v`, repeated `p` times.
  have hW : (p : ℝ) * (∑ v : InfinitePlace K, (v.mult : ℝ) * (⨆ i, c v.val i) +
      ∑ v ∈ S₀, ⨆ i, c v.val i) = approxWeight S₀ (fun v (_ : Fin p) ↦ ⨆ i, c v i) := by
    simp only [approxWeight_def, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul, mul_add, Finset.mul_sum, mul_left_comm]
  rw [hV, relativeSubspaceHeight_span_range hy, finrank_span_eq_card hy, Fintype.card_fin, hW]
  exact mulHeight_plucker_le hLInf hLFin hD0 hD hQ (by simpa using hy.fintype_card_le_finrank) hy
    fun k ↦ hbD (e.symm k).property

end TauCeti.NumberField
