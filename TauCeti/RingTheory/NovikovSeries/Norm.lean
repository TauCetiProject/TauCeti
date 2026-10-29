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

/-!
# The norm of Novikov series over a finite-index subgroup

Let `K` be a finite-index subgroup of the exponent group `H`, so that `Nov(R, H, N)` is a finite
free algebra over `Nov(R, K, N|K)` (`TauCeti.NovikovSeries.cosetBasis`), with Mathlib's norm
`Algebra.norm` and trace `Algebra.trace`. For an abelian covering with deck group `H`, this is the
norm from the intermediate finite abelian covering with deck group `H ⧸ K`, and the identity
`log Norm (1 + x) = Tr log (1 + x)` proved here is the one that compares the dynamical zeta
functions of the two coverings.

The norm does not lower periods: if `a - 1` lies in `U_C` with `C ≥ 0`, then so does
`Norm a - 1` (`TauCeti.NovikovSeries.norm_sub_one_mem_periodFiltration`). In the coset basis of
monomials `e^(s q)`, the matrix of multiplication by `a - 1` has its `(p, q)` entry in
`U_(C + N (s q) - N (s p))`, and these weights cancel along every permutation in the Leibniz
expansion of the determinant (`Matrix.det_one_add_sub_one_mem_periodFiltration`). Hence the norm
restricts to the nonnegative subrings (`TauCeti.NovikovSeries.normNonnegSubring`) and maps the
principal units `1 + x`, `x` in the positive ideal, to principal units.

Over a `ℚ`-algebra, the logarithm converts the norm of a principal unit into the trace of its
logarithm (`TauCeti.NovikovSeries.log_normNonnegSubring`):

`log (Norm u) = Tr (log u)`.

The proof differentiates both sides along the degree derivations `f ∘ N` of
`TauCeti/RingTheory/NovikovSeries/Derivation.lean`. The logarithmic derivative of the norm is the
trace of the logarithmic derivative (`Derivation.leibniz_norm`), and a continuous derivation
differentiates the logarithm logarithmically (`IsTopologicallyNilpotent.mul_derivation_log`). So
the difference of the two sides is killed by every degree derivation along the period. It is
supported in strictly positive periods, so it vanishes.

## Main definitions

* `TauCeti.NovikovSeries.normNonnegSubring K`: the norm, restricted to the nonnegative subrings.

## Main results

* `TauCeti.NovikovSeries.norm_sub_one_mem_periodFiltration`: the norm of `1 + x`, `x ∈ U_C`,
  `C ≥ 0`, is `1` modulo `U_C`.
* `TauCeti.NovikovSeries.normNonnegSubring_sub_one_mem_posIdeal`: the norm maps principal units
  to principal units.
* `TauCeti.NovikovSeries.log_normNonnegSubring`: `log (Norm u) = Tr (log u)` for principal units
  `u` over a `ℚ`-algebra.

## References

* M. Hutchings, *Reidemeister torsion in generalized Morse theory*, Forum Math. 14 (2002),
  Section 2.
* M. Hutchings and Y.-J. Lee, *Circle-valued Morse theory and Reidemeister torsion*,
  Geom. Topol. 3 (1999), Section 2.
-/

public section

noncomputable section

namespace TauCeti

namespace NovikovSeries

variable {R H : Type*} [CommRing R] [AddCommGroup H] {N : H →+ ℝ} {K : AddSubgroup H}
  [K.FiniteIndex] {C : ℝ}

/-- In the coset basis, the `(p, q)` entry of the matrix of multiplication by `x ∈ U_C` lies in
`U_(C + N (s q) - N (s p))`. -/
private theorem leftMulMatrix_cosetBasis_mem_periodFiltration [Fintype (H ⧸ K)]
    [DecidableEq (H ⧸ K)] {x : NovikovSeries R H N}
    (hx : x ∈ periodFiltration R N C) (p q : H ⧸ K) :
    Algebra.leftMulMatrix (cosetBasis K Quotient.out QuotientAddGroup.out_eq') x p q ∈
      periodFiltration R (N.comp K.subtype) (C + N q.out - N p.out) := by
  refine mem_periodFiltration.2 fun k hk => ?_
  rw [Algebra.leftMulMatrix_eq_repr_mul, coeff_cosetBasis_repr, cosetBasis_apply,
    coeff_mul_single, mul_one]
  refine mem_periodFiltration.1 hx _ ?_
  simp only [AddMonoidHom.coe_comp, AddSubgroup.coe_subtype, Function.comp_apply] at hk
  rw [map_sub, map_add]
  linarith

/-- The norm does not lower periods: if `a - 1 ∈ U_C` with `C ≥ 0`, then the norm of `a` over
the Novikov series on a finite-index subgroup `K` is `1` modulo `U_C`. -/
theorem norm_sub_one_mem_periodFiltration (hC : 0 ≤ C) {a : NovikovSeries R H N}
    (ha : a - 1 ∈ periodFiltration R N C) :
    Algebra.norm (NovikovSeries R K (N.comp K.subtype)) a - 1 ∈
      periodFiltration R (N.comp K.subtype) C := by
  classical
  have := Fintype.ofFinite (H ⧸ K)
  rw [Algebra.norm_eq_matrix_det (cosetBasis K Quotient.out QuotientAddGroup.out_eq'),
    ← sub_add_cancel a 1, map_add, map_one, add_comm]
  exact Matrix.det_one_add_sub_one_mem_periodFiltration hC (fun q => N q.out)
    (leftMulMatrix_cosetBasis_mem_periodFiltration ha)

/-- The norm over the Novikov series on a finite-index subgroup maps the nonnegative subring into
the nonnegative subring. -/
theorem norm_mem_nonnegSubring {a : NovikovSeries R H N} (ha : a ∈ nonnegSubring R N) :
    Algebra.norm (NovikovSeries R K (N.comp K.subtype)) a ∈
      nonnegSubring R (N.comp K.subtype) := by
  have h := norm_sub_one_mem_periodFiltration (K := K) le_rfl
    (mem_periodFiltration.2 (mem_nonnegSubring.1 (sub_mem ha (one_mem (nonnegSubring R N)))))
  exact mem_nonnegSubring.2 (mem_periodFiltration.1 (by
    simpa using add_mem h (one_mem_periodFiltration_zero (R := R) (N := N.comp K.subtype))))

variable (K) in
/-- The norm over the Novikov series on a finite-index subgroup `K`, as a monoid homomorphism of
the nonnegative subrings. -/
def normNonnegSubring : nonnegSubring R N →* nonnegSubring R (N.comp K.subtype) :=
  ((Algebra.norm (NovikovSeries R K (N.comp K.subtype)) :
      NovikovSeries R H N →* NovikovSeries R K (N.comp K.subtype)).comp
    (nonnegSubring R N).subtype.toMonoidHom).codRestrict _ fun a => norm_mem_nonnegSubring a.2

@[simp]
theorem coe_normNonnegSubring (a : nonnegSubring R N) :
    (normNonnegSubring K a : NovikovSeries R K (N.comp K.subtype)) =
      Algebra.norm (NovikovSeries R K (N.comp K.subtype)) (a : NovikovSeries R H N) :=
  (rfl)

/-- The norm maps principal units to principal units: if `u - 1` lies in the positive ideal, so
does `normNonnegSubring K u - 1`. -/
theorem normNonnegSubring_sub_one_mem_posIdeal {u : nonnegSubring R N}
    (hu : u - 1 ∈ posIdeal R N) :
    normNonnegSubring K u - 1 ∈ posIdeal R (N.comp K.subtype) := by
  obtain ⟨C, hC, huC⟩ := exists_pos_mem_periodFiltration_iff.2 (mem_posIdeal.1 hu)
  rw [mem_posIdeal, AddSubgroupClass.coe_sub, OneMemClass.coe_one, coe_normNonnegSubring]
  exact exists_pos_mem_periodFiltration_iff.1
    ⟨C, hC, norm_sub_one_mem_periodFiltration hC.le (by simpa using huC)⟩

/-! ### The logarithm of the norm -/

section Log

variable {H' : Type*} [AddCommMonoid H'] {N' : H' →+ ℝ}

/-- The degree derivation along `ℓ`, restricted to the nonnegative subring. -/
private def nonnegDegreeDerivation (ℓ : H' →+ R) :
    Derivation ℤ (nonnegSubring R N') (nonnegSubring R N') :=
  Derivation.mk'
    { toFun a := ⟨degreeDerivation ℓ a, degreeDerivation_mem_nonnegSubring ℓ a.2⟩
      map_add' a b := Subtype.ext (map_add (degreeDerivation ℓ) _ _)
      map_smul' n a := Subtype.ext (by simp) }
    fun a b => Subtype.ext (by simp [Derivation.leibniz, smul_eq_mul])

private theorem coe_nonnegDegreeDerivation (ℓ : H' →+ R) (a : nonnegSubring R N') :
    (nonnegDegreeDerivation ℓ a : NovikovSeries R H' N') = degreeDerivation ℓ a :=
  rfl

private theorem continuous_nonnegDegreeDerivation (ℓ : H' →+ R) :
    Continuous (nonnegDegreeDerivation (N' := N') ℓ) :=
  ((continuous_degreeDerivation ℓ).comp continuous_subtype_val).subtype_mk _

/-- A degree derivation differentiates the logarithm of a principal unit of the nonnegative
subring logarithmically: `u * D (log u) = D u`, read in the Novikov series. -/
private theorem mul_degreeDerivation_log [Algebra ℚ R] (ℓ : H' →+ R) {u : nonnegSubring R N'}
    (hu : u - 1 ∈ posIdeal R N') :
    (u : NovikovSeries R H' N') * degreeDerivation ℓ (NormedSpace.log u : nonnegSubring R N') =
      degreeDerivation ℓ (u : NovikovSeries R H' N') := by
  have := congrArg Subtype.val
    ((isTopologicallyNilpotent_of_mem_posIdeal' hu).mul_derivation_log
      (nonnegDegreeDerivation ℓ) (continuous_nonnegDegreeDerivation ℓ))
  simpa only [Subring.coe_mul, coe_nonnegDegreeDerivation] using this

end Log

variable [Algebra ℚ R]

/-- **The logarithm of the norm is the trace of the logarithm.** Over a `ℚ`-algebra, for a
principal unit `u` of the nonnegative subring of `Nov(R, H, N)`, the logarithm of its norm over
the Novikov series on a finite-index subgroup `K` is the trace of its logarithm:
`log (Norm u) = Tr (log u)`. -/
theorem log_normNonnegSubring {u : nonnegSubring R N} (hu : u - 1 ∈ posIdeal R N) :
    ((NormedSpace.log (normNonnegSubring K u) : nonnegSubring R (N.comp K.subtype)) :
      NovikovSeries R K (N.comp K.subtype)) =
      Algebra.trace (NovikovSeries R K (N.comp K.subtype)) (NovikovSeries R H N)
        (NormedSpace.log u : nonnegSubring R N) := by
  set A := NovikovSeries R H N
  set B := NovikovSeries R K (N.comp K.subtype)
  have hφ := exists_period_rescale_subtype (N := N) K
  have hker : (K.subtype.ker : Set K).Finite := by simp
  have hnil := isTopologicallyNilpotent_of_mem_posIdeal' hu
  have hu' := normNonnegSubring_sub_one_mem_posIdeal (K := K) hu
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

end NovikovSeries

end TauCeti
