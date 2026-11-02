/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Derivation.Determinant
public import TauCeti.RingTheory.NovikovSeries.Derivation
public import TauCeti.RingTheory.NovikovSeries.ExpLog
public import TauCeti.RingTheory.NovikovSeries.FiniteIndex
public import TauCeti.RingTheory.NovikovSeries.Matrix
public import Mathlib.RingTheory.Norm.Defs

/-!
# Period estimates for finite-cover Novikov norms

For a finite-index subgroup `K ≤ H`, the norm of Novikov series is Mathlib's
`Algebra.norm`, computed in the finite monomial basis of cosets. Its matrix entries
have period shifts given by the chosen coset representatives. Those shifts cancel
in every determinant term. Consequently the norm multiplies a lower support bound
by the index, preserves the nonnegative subring, and is continuous in the period
topology. A perturbation of `1` above a nonnegative cutoff has norm congruent to `1`
above the same cutoff. In particular, the norm preserves principal units with
strictly positive nonconstant support.

These estimates apply to arbitrary finite-index subgroups, not only cyclic
quotients, and allow dense periods, noninjective period maps and torsion in `H`.
They give the support control needed to compare norms with convergent logarithms
and with limits of finite-cover orbit products; no extension to total quotient rings
is asserted here.

For an abelian covering with deck group `H`, the norm is the one from the intermediate finite
abelian covering with deck group `H ⧸ K`. Over a `ℚ`-algebra, the logarithm converts the norm
of a principal unit into the trace of its logarithm
(`TauCeti.NovikovSeries.log_normNonnegSubring`):

`log (Norm u) = Tr (log u)`.

This is the identity that compares the dynamical zeta functions of the two coverings. The proof
differentiates both sides along the degree derivations `f ∘ N` of
`TauCeti/RingTheory/NovikovSeries/Derivation.lean`. The logarithmic derivative of the norm is the
trace of the logarithmic derivative (`Derivation.leibniz_norm`), and a continuous derivation
differentiates the logarithm logarithmically (`IsTopologicallyNilpotent.mul_derivation_log`). So
the difference of the two sides is killed by every degree derivation along the period. It is
supported in strictly positive periods, so it vanishes.

## References

* M. Hutchings, *Reidemeister torsion in generalized Morse theory*,
  Forum Math. 14 (2002), Section 2.
* M. Hutchings and Y.-J. Lee, *Circle-valued Morse theory and Reidemeister torsion*,
  Geom. Topol. 3 (1999), Section 2.
-/

public section

noncomputable section

namespace TauCeti.NovikovSeries

variable {R H : Type*} [CommRing R] [AddCommGroup H] {N : H →+ ℝ}
  (K : AddSubgroup H) [K.FiniteIndex]

section Matrix

variable [Fintype (H ⧸ K)] [DecidableEq (H ⧸ K)]

/-- An input cutoff shifts each multiplication-matrix entry by the difference of the
periods of the column and row representatives. -/
theorem leftMulMatrix_cosetBasis_mem_periodFiltration (s : H ⧸ K → H)
    (hs : ∀ q, (s q : H ⧸ K) = q) {a : NovikovSeries R H N} {D : ℝ}
    (ha : a ∈ periodFiltration R N D) (i j : H ⧸ K) :
    Algebra.leftMulMatrix (cosetBasis K s hs) a i j ∈
      periodFiltration R (N.comp K.subtype) (D + N (s j) - N (s i)) := by
  refine mem_periodFiltration.2 fun k hk => ?_
  rw [coeff_leftMulMatrix_cosetBasis]
  apply mem_periodFiltration.1 ha
  simp only [AddMonoidHom.comp_apply, AddSubgroup.subtype_apply] at hk
  rw [map_sub, map_add]
  linarith

end Matrix

/-- The norm multiplies a support lower bound by the index. This bound includes all
coefficients tied at a period. -/
theorem algebraNorm_mem_periodFiltration {a : NovikovSeries R H N} {D : ℝ}
    (ha : a ∈ periodFiltration R N D) :
    Algebra.norm (NovikovSeries R K (N.comp K.subtype)) a ∈
      periodFiltration R (N.comp K.subtype) (K.index * D) := by
  classical
  let := Fintype.ofFinite (H ⧸ K)
  rw [Algebra.norm_eq_matrix_det (cosetBasis K Quotient.out QuotientAddGroup.out_eq'),
    AddSubgroup.index_eq_card, Nat.card_eq_fintype_card]
  exact Matrix.det_mem_periodFiltration_of_weights (n := H ⧸ K) _
    (fun q => N (Quotient.out q))
    (leftMulMatrix_cosetBasis_mem_periodFiltration K _ _ ha)

/-- Norms of two series supported above `D` agree above `C + [H : K] * D` if the
series agree above `C + D`. Unlike an estimate at `1`, this permits negative `D`. -/
theorem algebraNorm_sub_algebraNorm_mem_periodFiltration {a b : NovikovSeries R H N} {C D : ℝ}
    (ha : a ∈ periodFiltration R N D) (hb : b ∈ periodFiltration R N D)
    (hab : a - b ∈ periodFiltration R N (C + D)) :
    Algebra.norm (NovikovSeries R K (N.comp K.subtype)) a -
      Algebra.norm (NovikovSeries R K (N.comp K.subtype)) b ∈
        periodFiltration R (N.comp K.subtype) (C + K.index * D) := by
  classical
  let := Fintype.ofFinite (H ⧸ K)
  let e := cosetBasis (R := R) (N := N) K Quotient.out QuotientAddGroup.out_eq'
  rw [Algebra.norm_eq_matrix_det e, Algebra.norm_eq_matrix_det e,
    AddSubgroup.index_eq_card, Nat.card_eq_fintype_card]
  have hAB : ∀ i j, Algebra.leftMulMatrix e a i j - Algebra.leftMulMatrix e b i j ∈
      periodFiltration R (N.comp K.subtype)
        (C + (D + N (Quotient.out j) - N (Quotient.out i))) := by
    intro i j
    have h := leftMulMatrix_cosetBasis_mem_periodFiltration K Quotient.out
      QuotientAddGroup.out_eq' hab i j
    simpa [map_sub, e, sub_eq_add_neg, add_assoc] using h
  exact Matrix.det_sub_det_mem_periodFiltration_of_weights (n := H ⧸ K) _ _
      (fun q => N (Quotient.out q))
      (leftMulMatrix_cosetBasis_mem_periodFiltration K _ _ ha)
      (leftMulMatrix_cosetBasis_mem_periodFiltration K _ _ hb) hAB

/-- The finite-cover norm is continuous for the period topologies. -/
@[fun_prop]
theorem continuous_algebraNorm :
    Continuous (Algebra.norm (NovikovSeries R K (N.comp K.subtype)) :
      NovikovSeries R H N → NovikovSeries R K (N.comp K.subtype)) := by
  rw [continuous_iff_continuousAt]
  intro a
  obtain ⟨D, ha⟩ := exists_mem_periodFiltration a
  refine ((hasBasis_nhds a).tendsto_iff (hasBasis_nhds _)).2 fun C _ =>
    ⟨max D (C - K.index * D + D), trivial, fun b hb => ?_⟩
  have hba := antitone_periodFiltration (le_max_left _ _) hb
  have hbD : b ∈ periodFiltration R N D := by
    simpa using (periodFiltration R N D).add_mem hba ha
  have h := algebraNorm_sub_algebraNorm_mem_periodFiltration K hbD ha
    (antitone_periodFiltration (le_max_right _ _) hb)
  simpa using h

/-- The finite-cover norm preserves nonnegative support, as a multiplicative map.
It is not asserted to preserve addition. -/
def normNonnegSubring : nonnegSubring R N →* nonnegSubring R (N.comp K.subtype) where
  toFun a := ⟨Algebra.norm (NovikovSeries R K (N.comp K.subtype)) (a : NovikovSeries R H N),
    mem_nonnegSubring.2 <| mem_periodFiltration.1 <| by
      simpa using algebraNorm_mem_periodFiltration K
        (mem_periodFiltration.2 (mem_nonnegSubring.1 a.2))⟩
  map_one' := Subtype.ext (_root_.map_one _)
  map_mul' a b := Subtype.ext (_root_.map_mul _ _ _)

@[simp]
theorem coe_normNonnegSubring (a : nonnegSubring R N) :
    (normNonnegSubring K a : NovikovSeries R K (N.comp K.subtype)) =
      Algebra.norm (NovikovSeries R K (N.comp K.subtype)) (a : NovikovSeries R H N) :=
  (rfl)

/-- The restricted norm is continuous for the subspace period topologies. -/
@[fun_prop]
theorem continuous_normNonnegSubring : Continuous (normNonnegSubring (R := R) (N := N) K) := by
  apply Continuous.subtype_mk
  exact (continuous_algebraNorm K).comp continuous_subtype_val

/-- A perturbation of `1` above a nonnegative cutoff has norm congruent to `1` above
that same cutoff, without losing a constant depending on coset representatives. -/
theorem algebraNorm_one_add_sub_one_mem_periodFiltration {a : NovikovSeries R H N} {C : ℝ}
    (hC : 0 ≤ C) (ha : a ∈ periodFiltration R N C) :
    Algebra.norm (NovikovSeries R K (N.comp K.subtype)) (1 + a) - 1 ∈
      periodFiltration R (N.comp K.subtype) C := by
  have ha0 := antitone_periodFiltration hC ha
  have h := algebraNorm_sub_algebraNorm_mem_periodFiltration K
    (add_mem one_mem_periodFiltration_zero ha0) one_mem_periodFiltration_zero
    (C := C) (D := 0) (by simpa using ha)
  simpa using h

/-- The norm maps a principal unit with strictly positive nonconstant support to
another such principal unit. -/
theorem normNonnegSubring_one_add_sub_one_mem_posIdeal {a : nonnegSubring R N}
    (ha : a ∈ posIdeal R N) :
    normNonnegSubring K (1 + a) - 1 ∈ posIdeal R (N.comp K.subtype) := by
  obtain ⟨C, hC, haC⟩ := exists_pos_mem_periodFiltration_iff.2 (mem_posIdeal.1 ha)
  apply mem_posIdeal.2
  apply exists_pos_mem_periodFiltration_iff.1
  exact ⟨C, hC, by simpa using algebraNorm_one_add_sub_one_mem_periodFiltration K hC.le haC⟩

/-- **The logarithm of the norm is the trace of the logarithm.** Over a `ℚ`-algebra, for a
principal unit `u` of the nonnegative subring of `Nov(R, H, N)`, the logarithm of its norm over
the Novikov series on a finite-index subgroup `K` is the trace of its logarithm:
`log (Norm u) = Tr (log u)`. -/
theorem log_normNonnegSubring [Algebra ℚ R] {u : nonnegSubring R N}
    (hu : u - 1 ∈ posIdeal R N) :
    ((NormedSpace.log (normNonnegSubring K u) : nonnegSubring R (N.comp K.subtype)) :
      NovikovSeries R K (N.comp K.subtype)) =
      Algebra.trace (NovikovSeries R K (N.comp K.subtype)) (NovikovSeries R H N)
        (NormedSpace.log u : nonnegSubring R N) := by
  set A := NovikovSeries R H N
  set B := NovikovSeries R K (N.comp K.subtype)
  have hφ := exists_period_rescale_subtype (N := N) K
  have hker : (K.subtype.ker : Set K).Finite := by simp
  have hnil := isTopologicallyNilpotent_of_mem_posIdeal' hu
  have hu' : normNonnegSubring K u - 1 ∈ posIdeal R (N.comp K.subtype) := by
    simpa using normNonnegSubring_one_add_sub_one_mem_posIdeal K hu
  -- `u` is a unit, being `1 - (1 - u)` with `1 - u` in the positive ideal.
  have h1u : 1 - u ∈ posIdeal R N := by simpa using neg_mem hu
  let U : Aˣ := (Units.map (nonnegSubring R N).subtype.toMonoidHom (unitsOneSub h1u))
  have hU : (U : A) = u := by simp [U]
  have hunit : IsUnit (normNonnegSubring K u : B) := by
    rw [coe_normNonnegSubring, ← hU]
    exact U.isUnit.map _
  rw [← sub_eq_zero]
  ext k
  rw [coeff_zero]
  by_cases hk : N k ≤ 0
  · -- Both sides lie in the positive ideal.
    have hlogB := hnil.log_mem (I := posIdeal R N) hu
    rw [coeff_sub, trace_eq_index_smul_comap hφ hker, coeff_smul, coeff_comap,
      mem_posIdeal.1 ((isTopologicallyNilpotent_of_mem_posIdeal' hu').log_mem hu') k hk,
      mem_posIdeal.1 hlogB (K.subtype k) hk, smul_zero, sub_zero]
  -- Away from period zero, the coefficient is detected by the degree derivations along `N`.
  refine coeff_eq_zero_of_forall_degreeDerivation_eq_zero (fun f => ?_) (not_le.1 hk).ne'
  set ℓ : H →+ R := ((algebraMap ℚ R).toAddMonoidHom.comp f.toAddMonoidHom).comp N
  have hℓ : ((algebraMap ℚ R).toAddMonoidHom.comp f.toAddMonoidHom).comp (N.comp K.subtype) =
      ℓ.comp K.subtype :=
    (AddMonoidHom.comp_assoc _ _ _).symm
  -- The degree derivations commute with the trace, which is restriction to `K` times the index.
  have htrace (y : A) : degreeDerivation (ℓ.comp K.subtype) (Algebra.trace B A y) =
      Algebra.trace B A (degreeDerivation ℓ y) := by
    rw [trace_eq_index_smul_comap hφ hker, trace_eq_index_smul_comap hφ hker, map_nsmul,
      comap_degreeDerivation]
  rw [hℓ, ← hunit.mul_right_eq_zero, map_sub, mul_sub, mul_degreeDerivation_log _ hu',
    coe_normNonnegSubring, ← hU, Derivation.leibniz_norm (degreeDerivation (ℓ.comp K.subtype))
      (degreeDerivation ℓ) (degreeDerivation_algebraMap_addSubgroup ℓ), htrace,
    hU, ← mul_degreeDerivation_log ℓ hu, ← hU, ← mul_assoc, Units.inv_mul, one_mul, sub_self]

end TauCeti.NovikovSeries
