/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Normed.Operator.Nonarchimedean.PrModule.Basic
public import TauCeti.Analysis.Normed.Operator.Nonarchimedean.RieszProjection.Basic
public import TauCeti.RingTheory.PowerSeries.Entire.GoodZero
public import TauCeti.Topology.Algebra.Module.ContinuousLinearMap.Intertwining

/-!
# Riesz projections on modules with property (Pr)

Let `r ∘ i = id` be a continuous linear retract `M →ⁱ N →ʳ M` of a seminormed module `M` through a
normed module `N`, and `u` an endomorphism of `M`. A Riesz projection `E` of the extension
`i ∘ u ∘ r` at `a` of order `h` compresses to the Riesz projection `r ∘ E ∘ i` of `u` at `a` of
the same order (`ContinuousLinearMap.IsRieszProjection.comp_comp_of_retract`). The idempotent
`e = i ∘ r` commutes with `i ∘ u ∘ r`, hence with the operator-norm closure of its polynomials,
which contains `E` and its complementary inverse. On that closure the compression `X ↦ r ∘ X ∘ i`
is multiplicative and sends `i ∘ u ∘ r` to `u`, and it is continuous in operator norm, so it
carries the defining identities and the closure condition of a Riesz projection to `M`.

Over a complete ultrametric norm-one Tate ring, a module with property (Pr) is such a retract of a
model space `C₀(J, R)`, and the Fredholm series `H_u` of a row-compact `u` is that of its
extension (`ContinuousLinearMap.IsPrCompact.charPowerSeries_eq`). Hence a good zero `a` of order
`h` of `H_u` gives a Riesz projection of `u` at `a` of order `h`
(`ContinuousLinearMap.IsPrCompact.exists_isRieszProjection`), and it is unique
(`ContinuousLinearMap.IsRieszProjection.unique`). Its range is the generalised eigenspace
`ker (1 - a • u) ^ h` (`ContinuousLinearMap.IsRieszProjection.range_eq_ker`). A Riesz projection
of a row-compact operator is row compact (`ContinuousLinearMap.IsRieszProjection.isPrCompact`), so
the generalised eigenspace is finitely generated and projective
(`ContinuousLinearMap.IsRieszProjection.finite_ker_pow_of_isPrCompact`,
`ContinuousLinearMap.IsRieszProjection.projective_ker_pow_of_isPrCompact`). As on model spaces, the
coefficient ring may have nilpotents and the eigenspace need not be free.

## Main results

* `ContinuousLinearMap.IsRieszProjection.comp_comp_of_retract`: Riesz projections compress along
  continuous linear retracts.
* `ContinuousLinearMap.IsPrCompact.exists_isRieszProjection`: the Riesz projection of a row-compact
  operator on a module with property (Pr) at a good zero of its Fredholm series.
* `ContinuousLinearMap.IsRieszProjection.isPrCompact`: Riesz projections of row-compact operators
  are row compact.
* `ContinuousLinearMap.IsRieszProjection.finite_ker_pow_of_isPrCompact`,
  `ContinuousLinearMap.IsRieszProjection.projective_ker_pow_of_isPrCompact`: the generalised
  eigenspace is a finitely generated projective module.

## References

* J.-P. Serre, *Endomorphismes complètement continus des espaces de Banach p-adiques*,
  Publ. Math. IHÉS **12** (1962), 69–85, §7.
* R. Coleman, *p-adic Banach spaces and families of modular forms*, Invent. Math. **127**
  (1997), 417–479, Appendix A, A4.
* C. Johansson and J. Newton, *Extended eigenvarieties for overconvergent cohomology*,
  arXiv:1604.07739, §2.2.
-/

public section

open scoped ZeroAtInfty TauCeti.RingOpNorm

namespace ContinuousLinearMap

section Retract

variable {R : Type*} [NormedCommRing R] [TauCeti.NormedRing.IsTate R]
  {M N : Type*} [SeminormedAddCommGroup M] [Module R M] [IsBoundedSMul R M]
  [NormedAddCommGroup N] [Module R N] [IsBoundedSMul R N]

variable {i : M →L[R] N} {r : N →L[R] M} {u : M →L[R] M}

omit [IsBoundedSMul R M] in
/-- Every operator-norm limit of polynomials in the extension `i ∘ u ∘ r` commutes with the
idempotent `i ∘ r`. -/
private theorem apply_comp_apply_of_mem_closure_adjoin (hri : r.comp i = .id R M) {X : N →L[R] N}
    (hX : X ∈ closure (Algebra.adjoin R {i.comp (u.comp r)} : Set (N →L[R] N))) (y : N) :
    i (r (X y)) = X (i (r y)) := by
  have hri' (x : M) : r (i x) = x := by simpa using DFunLike.congr_fun hri x
  have he : i.comp r ∈ Subalgebra.centralizer R {i.comp (u.comp r)} :=
    (Subalgebra.mem_centralizer_iff R).2 fun _ hm ↦ by
      rw [Set.mem_singleton_iff.1 hm]
      ext y
      simp [hri']
  have : IsTopologicalSemiring (N →L[R] N) := inferInstance
  rw [← Subalgebra.topologicalClosure_coe] at hX
  have hX' := (Subalgebra.mem_centralizer_iff R).1
    (Subalgebra.topologicalClosure_adjoin_le_centralizer_centralizer R _ hX) _ he
  exact congr($hX' y)

/-- Compression `X ↦ r ∘ X ∘ i` sends the operator-norm closure of the polynomials in the
extension `i ∘ u ∘ r` into the closure of the polynomials in `u`. On the polynomials it is
multiplicative, since they commute with the idempotent `i ∘ r`. -/
private theorem comp_comp_mem_closure_adjoin (hri : r.comp i = .id R M) {X : N →L[R] N}
    (hX : X ∈ closure (Algebra.adjoin R {i.comp (u.comp r)} : Set (N →L[R] N))) :
    r.comp (X.comp i) ∈ closure (Algebra.adjoin R {u} : Set (M →L[R] M)) := by
  have hri' (x : M) : r (i x) = x := by simpa using DFunLike.congr_fun hri x
  refine map_mem_closure (f := fun X : N →L[R] N ↦ r.comp (X.comp i))
    (lipschitzWith_comp_comp r i).continuous hX fun Y hY ↦ ?_
  -- Strengthen the induction by the commutation with `i ∘ r`, needed for products.
  suffices (∀ y, i (r (Y y)) = Y (i (r y))) ∧ r.comp (Y.comp i) ∈ Algebra.adjoin R {u} from
    this.2
  induction hY using Algebra.adjoin_induction with
  | mem x hx =>
    rw [Set.mem_singleton_iff.1 hx]
    refine ⟨fun y ↦ by simp [hri'], ?_⟩
    convert Algebra.self_mem_adjoin_singleton R u using 1
    ext x
    simp [hri']
  | algebraMap c =>
    refine ⟨fun y ↦ by simp [Algebra.algebraMap_eq_smul_one], ?_⟩
    convert Subalgebra.algebraMap_mem (Algebra.adjoin R {u}) c using 1
    ext x
    simp [Algebra.algebraMap_eq_smul_one, hri']
  | add x y _ _ hx hy =>
    refine ⟨fun z ↦ by simp [hx.1, hy.1], ?_⟩
    rw [add_comp, comp_add]
    exact add_mem hx.2 hy.2
  | mul x y _ _ hx hy =>
    refine ⟨fun z ↦ by simp [hx.1, hy.1], ?_⟩
    convert mul_mem hx.2 hy.2 using 1
    ext z
    simp [hy.1, hri']

/-- **Compression of Riesz projections along a retract.** Let `r ∘ i = id` present `M` as a
retract of a normed module `N`. If `E` is a Riesz projection of the extension `i ∘ u ∘ r` at `a`
of order `h`, then `r ∘ E ∘ i` is a Riesz projection of `u` at `a` of order `h`. -/
theorem IsRieszProjection.comp_comp_of_retract (hri : r.comp i = .id R M) {a : R} {h : ℕ}
    {E : N →L[R] N} (hE : IsRieszProjection (i.comp (u.comp r)) a h E) :
    IsRieszProjection u a h (r.comp (E.comp i)) := by
  have hri' (x : M) : r (i x) = x := by simpa using DFunLike.congr_fun hri x
  -- `r` intertwines the extension `i ∘ u ∘ r` with `u`.
  have hr : Function.Semiconj (r : N →ₗ[R] M) (i.comp (u.comp r)) u := fun y ↦ by simp [hri']
  obtain ⟨w, hw₁, hw₂, hw₃, hw₄, hw⟩ := hE.exists_inverse
  have hE' := apply_comp_apply_of_mem_closure_adjoin hri hE.mem_closure_adjoin
  have hw' := apply_comp_apply_of_mem_closure_adjoin hri hw
  have hEE (y : N) : E (E y) = E y := congr($hE.isIdempotentElem.eq y)
  have hEv (y : N) : E (i (u (r y))) = i (u (r (E y))) := congr($hE.commute.eq y).symm
  have hpow (y : N) : ((1 - a • i.comp (u.comp r)) ^ h) (E y) = 0 :=
    congr($hE.pow_mul_eq_zero y)
  refine ⟨?_, ?_, comp_comp_mem_closure_adjoin hri hE.mem_closure_adjoin, ?_,
    ⟨r.comp (w.comp i), ?_, ?_, ?_, ?_, comp_comp_mem_closure_adjoin hri hw⟩⟩
  · ext x
    simp [hE', hri', hEE]
  · ext x
    simpa [hri'] using congr(r $(hEv (i x))).symm
  · ext x
    simpa [hpow] using (hr.one_sub_smul_pow a h (E (i x))).symm
  · ext x
    simpa [hri'] using
      (hr.one_sub_smul a (w (i x))).symm.trans congr(r $(DFunLike.congr_fun hw₁ (i x)))
  · ext x
    simpa [hri'] using congr(r $(DFunLike.congr_fun hw₂ (i x)))
  · ext x
    simpa [hw', hri'] using congr(r $(DFunLike.congr_fun hw₃ (i x)))
  · ext x
    simpa [hE', hri'] using congr(r $(DFunLike.congr_fun hw₄ (i x)))

end Retract

section PrModule

variable {R : Type*} [NormedCommRing R] [IsUltrametricDist R] [CompleteSpace R]
  [TauCeti.NormedRing.IsTate R] {M : Type*} [SeminormedAddCommGroup M] [Module R M]
  [IsBoundedSMul R M] {u E : M →L[R] M} {a : R} {h : ℕ}

/-- **The Riesz projection at a good zero on a module with property (Pr).** Let `u` be a
row-compact endomorphism of a module with property (Pr), and `a` a good zero of order `h` of its
Fredholm series `H_u`: `ΔʲH_u(a) = 0` for `j < h` and `ΔʰH_u(a)` is a unit. Then `u` has a Riesz
projection at `a` of order `h`. -/
theorem IsPrCompact.exists_isRieszProjection [NormOneClass R]
    (hu : u.IsPrCompact) (ha : u.charPowerSeries.IsGoodZero a h) :
    ∃ E, IsRieszProjection u a h E := by
  classical
  obtain ⟨J, _, _, i, r, hri⟩ := (TauCeti.hasPr_def R M).1 hu.hasPr_source
  rw [hu.charPowerSeries_eq hri] at ha
  obtain ⟨hH, hc⟩ := PowerSeries.isGoodZero_iff.1 ha
  exact ⟨_, ((hu.isRowCompact_comp i r).isRieszProjection_rieszProjection hH hc)
    |>.comp_comp_of_retract hri⟩

omit [CompleteSpace R] in
/-- A Riesz projection of a row-compact endomorphism of a module with property (Pr) is row
compact, including when its nilpotence bound is zero. -/
theorem IsRieszProjection.isPrCompact (hE : IsRieszProjection u a h E) (hu : u.IsPrCompact) :
    E.IsPrCompact := by
  let C : M →L[R] M := 1 - a • u
  -- The geometric sum expresses `E` as the row-compact factor `a • u` followed by bounded maps.
  have hEq : E = (1 - C) * (∑ i ∈ Finset.range h, C ^ i) * E := by
    rw [mul_neg_geom_sum C h]
    simp only [C, sub_mul (α := M →L[R] M), one_mul, hE.pow_mul_eq_zero,
      sub_zero (G := M →L[R] M)]
  have hc : (1 - C).IsPrCompact := by
    simpa only [C, sub_sub_cancel (1 : M →L[R] M) (a • u)] using hu.smul a
  rw [hEq]
  simpa only [mul_def] using
    ((hc.comp_clm _ hu.hasPr_source).comp_clm E hu.hasPr_source)

/-- The stabilised generalised eigenspace `ker (1 - a • u) ^ n`, `n ≥ h`, of a row-compact
endomorphism of a module with property (Pr) is finitely generated. -/
theorem IsRieszProjection.finite_ker_pow_of_isPrCompact (hE : IsRieszProjection u a h E)
    (hu : u.IsPrCompact) {n : ℕ} (hn : h ≤ n) :
    Module.Finite R (LinearMap.ker (((1 - a • u) ^ n : M →L[R] M) : M →ₗ[R] M)) := by
  rw [← (hE.of_le hn).range_eq_ker]
  exact (hE.isPrCompact hu).finite_range_of_isIdempotentElem hE.isIdempotentElem

/-- The stabilised generalised eigenspace `ker (1 - a • u) ^ n`, `n ≥ h`, of a row-compact
endomorphism of a module with property (Pr) is projective over the coefficient ring. -/
theorem IsRieszProjection.projective_ker_pow_of_isPrCompact (hE : IsRieszProjection u a h E)
    (hu : u.IsPrCompact) {n : ℕ} (hn : h ≤ n) :
    Module.Projective R (LinearMap.ker (((1 - a • u) ^ n : M →L[R] M) : M →ₗ[R] M)) := by
  rw [← (hE.of_le hn).range_eq_ker]
  exact (hE.isPrCompact hu).projective_range_of_isIdempotentElem hE.isIdempotentElem

end PrModule

end ContinuousLinearMap
