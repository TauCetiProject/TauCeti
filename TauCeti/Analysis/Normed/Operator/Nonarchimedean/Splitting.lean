/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Normed.Operator.Nonarchimedean.Idempotent
public import TauCeti.Analysis.Normed.Operator.Nonarchimedean.PrModule

/-!
# Fredholm series on split Banach modules

The Fredholm series of row-compact operators on modules with property (Pr) is
multiplicative along a bounded upper triangular splitting. The factors are the Fredholm
series of the operators on the actual summands, independently of their retract
presentations. A finite summand contributes its finite projective characteristic
determinant; neither freeness nor constant rank is required.

The basic identity is `H_(u + v) = H_u H_v` for row-compact operators with
`u ∘ v = 0`. It descends from the model-space identity by extending both operators
through one common retract. Cyclicity then identifies each extended factor with
the series on its summand.

## References

* J.-P. Serre, *Endomorphismes complètement continus des espaces de Banach
  p-adiques*, Publ. Math. IHÉS **12** (1962), 69–85, §§5–7.
* C. Johansson and J. Newton, *Extended eigenvarieties for overconvergent
  cohomology*, arXiv:1604.07739, §2.1.
-/

public section

open ContinuousLinearMap
universe u

namespace TauCeti

variable {R : Type*} [NormedCommRing R] [NormOneClass R] [IsUltrametricDist R]
  [CompleteSpace R] [NormedRing.IsTate R]
  {M N P : Type*} [SeminormedAddCommGroup M] [Module R M]
  [SeminormedAddCommGroup N] [Module R N] [SeminormedAddCommGroup P] [Module R P]

/-- Fredholm series multiply under addition of row-compact operators that annihilate
in one order. The operators need not commute. -/
theorem charPowerSeries_add_of_comp_eq_zero {u v : M →L[R] M}
    (hu : u.IsPrCompact) (hv : v.IsPrCompact) (huv : u.comp v = 0) :
    (u + v).charPowerSeries = u.charPowerSeries * v.charPowerSeries := by
  classical
  obtain ⟨I, _, _, i, r, hri⟩ := (hasPr_def R M).1 hu.hasPr_source
  have hri' (x : M) : r (i x) = x := by
    simpa using DFunLike.congr_fun hri x
  have hmul : i.comp (u.comp r) * i.comp (v.comp r) = 0 := by
    ext x
    have hx : u (v (r x)) = 0 := DFunLike.congr_fun huv (r x)
    simp [hri', hx]
  rw [(hu.add hv).charPowerSeries_eq hri, hu.charPowerSeries_eq hri,
    hv.charPowerSeries_eq hri, add_comp, comp_add]
  exact (hu.isRowCompact_comp i r).charPowerSeries_matrixCoeff_add_of_mul_eq_zero
    (hv.isRowCompact_comp i r) hmul

/-- The finite pairwise-annihilating-family formula on (Pr) modules, including
the empty family. -/
theorem charPowerSeries_sum_of_comp_eq_zero {ι : Type*} {S : Finset ι}
    {v : ι → M →L[R] M} (hv : ∀ k ∈ S, (v k).IsPrCompact)
    (h : ∀ k ∈ S, ∀ l ∈ S, k ≠ l → (v k).comp (v l) = 0) :
    (∑ k ∈ S, v k).charPowerSeries = ∏ k ∈ S, (v k).charPowerSeries := by
  classical
  obtain rfl | ⟨k, hk⟩ := S.eq_empty_or_nonempty
  · simp
  have hM := (hv k hk).hasPr_source
  obtain ⟨I, _, _, i, r, hri⟩ := (hasPr_def R M).1 hM
  have hri' (x : M) : r (i x) = x := by
    simpa using DFunLike.congr_fun hri x
  have hsum : (∑ k ∈ S, v k).IsPrCompact :=
    Finset.sum_induction v (fun w : M →L[R] M ↦ w.IsPrCompact)
      (fun _ _ ↦ IsPrCompact.add) (isPrCompact_zero_iff.2 ⟨hM, hM⟩) hv
  rw [hsum.charPowerSeries_eq hri, finsetSum_comp, comp_finsetSum]
  calc
    _ = ∏ k ∈ S, (i.comp ((v k).comp r)).matrixCoeff.charPowerSeries := by
      apply charPowerSeries_matrixCoeff_sum_of_mul_eq_zero
        (fun k hk ↦ (hv k hk).isRowCompact_comp i r)
      intro k hk l hl hkl
      ext x
      have hx : v k (v l (r x)) = 0 := DFunLike.congr_fun (h k hk l hl hkl) (r x)
      simp [hri', hx]
    _ = _ := Finset.prod_congr rfl fun k hk ↦ ((hv k hk).charPowerSeries_eq hri).symm

/-- The Fredholm series factors over a complete family of orthogonal bounded
idempotents commuting with the operator, on any module with property (Pr). -/
theorem charPowerSeries_eq_prod_of_commute {ι : Type*} [Fintype ι]
    {u : M →L[R] M} (hu : u.IsPrCompact) {e : ι → M →L[R] M}
    (he : CompleteOrthogonalIdempotents e) (hue : ∀ k, Commute u (e k)) :
    u.charPowerSeries = ∏ k, (u * e k).charPowerSeries := by
  conv_lhs => rw [← mul_one u, ← he.complete, Finset.mul_sum (R := M →L[R] M)]
  refine charPowerSeries_sum_of_comp_eq_zero
    (fun k _ ↦ hu.comp_clm (e k) hu.hasPr_source) fun k _ l _ hkl ↦ ?_
  -- Move the commuting operator past the first idempotent, then use orthogonality.
  rw [← mul_def, mul_assoc, ← mul_assoc (e k), ← (hue k).eq, mul_assoc u (e k),
    he.ortho hkl, mul_zero, mul_zero]

/-- A bounded splitting with invariant summands gives the product of their Fredholm
series. The inclusions and retractions need not be isometries. Only one cross
composite is needed to make the two extended operators annihilate. -/
theorem charPowerSeries_add_eq_mul_of_retracts {u : M →L[R] M} {v : N →L[R] N}
    (hu : u.IsPrCompact) (hv : v.IsPrCompact) (hP : HasPr R P)
    (i : M →L[R] P) (r : P →L[R] M) (j : N →L[R] P) (s : P →L[R] N)
    (hri : r.comp i = .id R M) (hsj : s.comp j = .id R N) (hrj : r.comp j = 0) :
    (i.comp (u.comp r) + j.comp (v.comp s)).charPowerSeries =
      u.charPowerSeries * v.charPowerSeries := by
  have hi := (hu.comp_clm r hP).clm_comp i hP
  have hj := (hv.comp_clm s hP).clm_comp j hP
  have hzero : (i.comp (u.comp r)).comp (j.comp (v.comp s)) = 0 := by
    have h (x : N) : r (j x) = 0 := DFunLike.congr_fun hrj x
    ext x
    simp [h]
  rw [charPowerSeries_add_of_comp_eq_zero hi hj hzero,
    ← (hu.comp_clm r hP).charPowerSeries_comp_comm i,
    ← (hv.comp_clm s hP).charPowerSeries_comp_comm j]
  simp only [comp_assoc, hri, hsj, comp_id]

/-- The Fredholm series of a block diagonal operator on a product of (Pr) modules
is the product of the Fredholm series of its two blocks. -/
theorem charPowerSeries_prodMap {M N : Type u} [SeminormedAddCommGroup M] [Module R M]
    [SeminormedAddCommGroup N] [Module R N]
    {u : M →L[R] M} {v : N →L[R] N}
    (hu : u.IsPrCompact) (hv : v.IsPrCompact) :
    (u.prodMap v).charPowerSeries = u.charPowerSeries * v.charPowerSeries := by
  have h : u.prodMap v =
      (inl R M N).comp (u.comp (fst R M N)) +
        (inr R M N).comp (v.comp (snd R M N)) := by
    ext x <;> simp
  rw [h]
  exact charPowerSeries_add_eq_mul_of_retracts hu hv
    (hu.hasPr_source.prod hv.hasPr_source) _ _ _ _
    fst_comp_inl snd_comp_inr fst_comp_inr

/-- An upper triangular operator with respect to a bounded splitting has the product
of the Fredholm series of its diagonal blocks. More generally, an identity
decomposition `i r + j s = id` and the vanishing lower block `s w i = 0` suffice;
the summands need only have property (Pr). -/
theorem charPowerSeries_eq_mul_of_split {w : P →L[R] P} (hw : w.IsPrCompact)
    (hM : HasPr R M) (hN : HasPr R N)
    (i : M →L[R] P) (r : P →L[R] M) (j : N →L[R] P) (s : P →L[R] N)
    (hsplit : i.comp r + j.comp s = .id R P) (htri : s.comp (w.comp i) = 0) :
    w.charPowerSeries = (r.comp (w.comp i)).charPowerSeries *
      (s.comp (w.comp j)).charPowerSeries := by
  have hi := (hw.comp_clm i hM).comp_clm r hw.hasPr_source
  have hj := (hw.comp_clm j hN).comp_clm s hw.hasPr_source
  have hsum : w.comp (j.comp s) + w.comp (i.comp r) = w := by
    rw [add_comm, ← comp_add, hsplit, comp_id]
  have hzero : ((w.comp j).comp s).comp ((w.comp i).comp r) = 0 := by
    rw [comp_assoc, comp_assoc, ← comp_assoc s, htri, zero_comp, comp_zero, comp_zero]
  calc
    w.charPowerSeries = ((w.comp j).comp s + (w.comp i).comp r).charPowerSeries := by
      rw [comp_assoc, comp_assoc, hsum]
    _ = _ := by
      rw [charPowerSeries_add_of_comp_eq_zero hj hi hzero,
        (hw.comp_clm j hN).charPowerSeries_comp_comm s,
        (hw.comp_clm i hM).charPowerSeries_comp_comm r, mul_comm]

/-- On a product, vanishing of the lower-left block gives the upper-triangular
Fredholm determinant formula, even when the off-diagonal block is nonzero. -/
theorem charPowerSeries_eq_mul_of_fst_snd {M N : Type u}
    [SeminormedAddCommGroup M] [Module R M] [SeminormedAddCommGroup N] [Module R N]
    {w : M × N →L[R] M × N} (hw : w.IsPrCompact)
    (htri : (snd R M N).comp (w.comp (inl R M N)) = 0) :
    w.charPowerSeries = ((fst R M N).comp (w.comp (inl R M N))).charPowerSeries *
      ((snd R M N).comp (w.comp (inr R M N))).charPowerSeries := by
  exact charPowerSeries_eq_mul_of_split hw
    (hw.hasPr_source.of_retract (inl R M N) (fst R M N) fst_comp_inl)
    (hw.hasPr_source.of_retract (inr R M N) (snd R M N) snd_comp_inr)
    _ _ _ _ (by ext x <;> simp) htri

/-- A finite (Pr) summand in a bounded triangular splitting contributes its
finite projective characteristic determinant as a polynomial factor. This does
not require a free summand, a constant rank, or a unit leading coefficient. -/
theorem charPowerSeries_eq_projectiveCharpolyRev_mul_of_split
    {M : Type*} [NormedAddCommGroup M] [Module R M] [IsBoundedSMul R M]
    [Module.Finite R M] {w : P →L[R] P} (hw : w.IsPrCompact)
    (hM : HasPr R M) (hN : HasPr R N)
    (i : M →L[R] P) (r : P →L[R] M) (j : N →L[R] P) (s : P →L[R] N)
    (hsplit : i.comp r + j.comp s = .id R P) (htri : s.comp (w.comp i) = 0) :
    haveI := hM.projective
    w.charPowerSeries =
      (((r.comp (w.comp i)) : M →ₗ[R] M).projectiveCharpolyRev : PowerSeries R) *
        (s.comp (w.comp j)).charPowerSeries := by
  have := hM.projective
  rw [charPowerSeries_eq_mul_of_split hw hM hN i r j s hsplit htri,
    charPowerSeries_eq_projectiveCharpolyRev hM]

end TauCeti
