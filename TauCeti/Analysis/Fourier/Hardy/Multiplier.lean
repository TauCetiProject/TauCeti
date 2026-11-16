/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Fourier.Hardy.BrownHalmos
public import TauCeti.Analysis.Fourier.Hardy.Hankel.Basic

/-!
# Bounded analytic multipliers of boundary Hardy space

The boundary realization of H∞ is the subalgebra of essentially bounded circle symbols
whose negative Fourier coefficients vanish. Its elements preserve Hardy space under
multiplication. Restriction of multiplication is an isometric algebra homomorphism, and its
image is exactly the commutant of the forward shift. Thus a bounded operator commuting with
the shift has a unique analytic multiplier symbol, with the same norm.

This comparison concerns boundary symbols and operators; it does not identify all bounded
holomorphic disk functions with boundary symbols.

## References

* A. Brown and P. R. Halmos, *Algebraic properties of Toeplitz operators*,
  J. Reine Angew. Math. 213 (1964), 89–102.
* J. B. Conway, *A Course in Functional Analysis*, second edition, the unilateral shift
  and its analytic multipliers.
-/

public section

noncomputable section

open MeasureTheory
open scoped ENNReal InnerProductSpace

namespace TauCeti

/-- A bounded symbol preserves Hardy space under multiplication exactly when its negative
Fourier coefficients vanish. -/
theorem mapsTo_multiplicationOperator_hardySubmodule_iff
    (a : Lp ℂ ∞ (AddCircle.haarAddCircle (T := 1))) :
    Set.MapsTo (Lp.multiplicationOperator (E := ℂ) a)
      (hardySubmodule : Set _) (hardySubmodule : Set _) ↔
      ∀ n : ℤ, n < 0 → fourierCoeff a n = 0 := by
  rw [← hankel_eq_zero_iff]
  constructor
  · intro ha
    ext f : 1
    rw [hankel_apply]
    simp only [ContinuousLinearMap.comp_apply, Submodule.subtypeL_apply,
      Submodule.orthogonalProjectionOnto_eq_zero_iff, Submodule.orthogonal_orthogonal,
      zero_apply]
    exact ha f.property
  · intro ha f hf
    have h := coe_toeplitz_add_coe_hankel a ⟨f, hf⟩
    simp only [ha, zero_apply, Submodule.coe_zero, add_zero] at h
    rw [Lp.multiplicationOperator_apply, ← h]
    exact (toeplitz a ⟨f, hf⟩).property

/-- The boundary H∞ algebra: the essentially bounded symbols preserving Hardy space under
multiplication. Equivalently, these are the symbols with no negative Fourier coefficients. -/
def hardyMultiplierAlgebra : Subalgebra ℂ (Lp ℂ ∞ (AddCircle.haarAddCircle (T := 1))) where
  carrier := {a | Set.MapsTo (Lp.multiplicationOperator (E := ℂ) a)
    (hardySubmodule : Set _) (hardySubmodule : Set _)}
  add_mem' ha hb f hf := by
    simpa only [Lp.multiplicationOperator_add, add_apply, SetLike.mem_coe] using
      hardySubmodule.add_mem (ha hf) (hb hf)
  mul_mem' ha hb f hf := by
    rw [← Lp.multiplicationOperator_comp_multiplicationOperator,
      ContinuousLinearMap.comp_apply]
    exact ha (hb hf)
  algebraMap_mem' c := by
    intro f hf
    simpa only [Lp.multiplicationOperator_algebraMap, smul_apply, ContinuousLinearMap.id_apply,
      SetLike.mem_coe] using hardySubmodule.smul_mem c hf

/-- Membership in boundary H∞ is characterized by vanishing negative Fourier coefficients. -/
@[simp]
theorem mem_hardyMultiplierAlgebra_iff
    (a : Lp ℂ ∞ (AddCircle.haarAddCircle (T := 1))) :
    a ∈ hardyMultiplierAlgebra ↔ ∀ n : ℤ, n < 0 → fourierCoeff a n = 0 :=
  mapsTo_multiplicationOperator_hardySubmodule_iff a

/-- Boundary H∞ is a closed subalgebra of L∞. -/
theorem isClosed_hardyMultiplierAlgebra :
    IsClosed (hardyMultiplierAlgebra : Set (Lp ℂ ∞ (AddCircle.haarAddCircle (T := 1)))) := by
  have h : (hardyMultiplierAlgebra : Set (Lp ℂ ∞ (AddCircle.haarAddCircle (T := 1)))) =
      {a | hankel a = 0} := by
    ext a
    exact (mem_hardyMultiplierAlgebra_iff a).trans (hankel_eq_zero_iff a).symm
  rw [h]
  exact isClosed_eq hankel.continuous continuous_const

/-- The boundary H∞ algebra is complete in its essential supremum norm. -/
instance : CompleteSpace hardyMultiplierAlgebra :=
  isClosed_hardyMultiplierAlgebra.completeSpace_coe

/-- A Fourier monomial is an analytic multiplier exactly when its degree is nonnegative. -/
theorem fourierLp_mem_hardyMultiplierAlgebra_iff (k : ℤ) :
    fourierLp (T := 1) ∞ k ∈ hardyMultiplierAlgebra ↔ 0 ≤ k := by
  rw [mem_hardyMultiplierAlgebra_iff]
  constructor
  · intro h
    by_contra hk
    have hzero := h k (by omega)
    rw [fourierCoeff_fourierLp, ite_eq_left rfl] at hzero
    exact one_ne_zero hzero
  · intro hk n hn
    rw [fourierCoeff_fourierLp, ite_eq_right (by omega)]

/-- For an analytic symbol, Toeplitz compression is actual multiplication. -/
theorem coe_toeplitz_apply_of_mem_hardyMultiplierAlgebra
    {a : Lp ℂ ∞ (AddCircle.haarAddCircle (T := 1))}
    (ha : a ∈ hardyMultiplierAlgebra) (f : HardySpace) :
    (toeplitz a f : Lp ℂ 2 (AddCircle.haarAddCircle (T := 1))) =
      Lp.multiplicationOperator a f := by
  rw [coe_toeplitz_apply, ← Lp.multiplicationOperator_apply]
  exact Submodule.starProjection_eq_self_iff.mpr (ha f.property)

/-- A Toeplitz operator commutes with the forward shift exactly when its symbol is analytic. -/
theorem commute_toeplitz_fourierLp_one_iff
    (a : Lp ℂ ∞ (AddCircle.haarAddCircle (T := 1))) :
    Commute (toeplitz a) (toeplitz (fourierLp (T := 1) ∞ 1)) ↔
      a ∈ hardyMultiplierAlgebra := by
  constructor
  · intro h
    apply (mem_hardyMultiplierAlgebra_iff a).mpr
    intro n hn
    obtain ⟨j, hj⟩ := Int.eq_ofNat_of_zero_le (by omega : 0 ≤ -n - 1)
    have heq := congrArg (fun T : HardySpace →L[ℂ] HardySpace ↦
      ⟪hardyBasis 0, T (hardyBasis j)⟫_ℂ) h.eq
    simp only [mul_apply_eq_comp, toeplitz_fourierLp_one_hardyBasis] at heq
    have hz : ⟪hardyBasis 0, toeplitz (fourierLp (T := 1) ∞ 1)
        (toeplitz a (hardyBasis j))⟫_ℂ = 0 := by
      rw [← HilbertBasis.repr_apply_apply, hardyBasis_repr_toeplitz_apply,
        fourierCoeff_fourierLp_smul]
      exact HardySpace.fourierCoeff_eq_zero _ (by norm_num)
    rw [hz, inner_hardyBasis_toeplitz_hardyBasis] at heq
    have hjn : (↑(0 : ℕ) : ℤ) - (j + 1 : ℕ) = n := by omega
    rwa [hjn] at heq
  · intro ha
    have hz := (mem_hardyMultiplierAlgebra_iff (fourierLp (T := 1) ∞ 1)).mp
      ((fourierLp_mem_hardyMultiplierAlgebra_iff 1).mpr (by norm_num))
    exact (toeplitz_comp_of_analytic a _ hz).trans
      ((congrArg toeplitz (mul_comm a _)).trans
        (toeplitz_comp_of_analytic _ a ((mem_hardyMultiplierAlgebra_iff a).mp ha)).symm)

/-- Every bounded operator commuting with the forward shift is multiplication by a unique
boundary H∞ symbol. -/
theorem existsUnique_toeplitz_eq_iff_commute (T : HardySpace →L[ℂ] HardySpace) :
    (∃! a : hardyMultiplierAlgebra, toeplitz a = T) ↔
      Commute T (toeplitz (fourierLp (T := 1) ∞ 1)) := by
  constructor
  · rintro ⟨a, rfl, _⟩
    exact (commute_toeplitz_fourierLp_one_iff a).mpr a.property
  · intro hT
    have hS : ContinuousLinearMap.adjoint (toeplitz (fourierLp (T := 1) ∞ 1)) ∘L
        toeplitz (fourierLp (T := 1) ∞ 1) = 1 :=
      (ContinuousLinearMap.isometry_iff_adjoint_comp_self _).mp (by
        simpa only [Nat.cast_one] using isometry_toeplitz_fourierLp_natCast 1)
    have hcomm : T ∘L toeplitz (fourierLp (T := 1) ∞ 1) =
        toeplitz (fourierLp (T := 1) ∞ 1) ∘L T := by
      simpa only [ContinuousLinearMap.mul_def] using hT.eq
    obtain ⟨a, ha, hunique⟩ :=
      (existsUnique_toeplitz_eq_iff_adjoint_comp_comp_eq T).mpr (by
        rw [hcomm, ← ContinuousLinearMap.comp_assoc, hS]
        simp only [ContinuousLinearMap.one_def, ContinuousLinearMap.id_comp])
    have ha' : a ∈ hardyMultiplierAlgebra :=
      (commute_toeplitz_fourierLp_one_iff a).mp (ha.symm ▸ hT)
    exact ⟨⟨a, ha'⟩, ha, fun b hb ↦ Subtype.ext (hunique b hb)⟩

/-- Restriction of multiplication gives an algebra homomorphism from boundary H∞ to bounded
operators on Hardy space. Multiplication in the target is operator composition. -/
def hardyMultiplierHom : hardyMultiplierAlgebra →ₐ[ℂ] (HardySpace →L[ℂ] HardySpace) where
  toFun a := toeplitz a
  map_zero' := map_zero toeplitz
  map_add' a b := map_add toeplitz a.val b.val
  map_one' := by
    simpa only [map_one, Subalgebra.coe_one, one_smul, ContinuousLinearMap.one_def] using
      toeplitz_algebraMap 1
  map_mul' a b :=
    (toeplitz_comp_of_analytic a b ((mem_hardyMultiplierAlgebra_iff b).mp b.property)).symm
  commutes' c := by
    rw [Subalgebra.coe_algebraMap, toeplitz_algebraMap]
    simp only [Algebra.algebraMap_eq_smul_one, ContinuousLinearMap.one_def]

/-- The multiplier homomorphism acts by the Toeplitz operator of its symbol. -/
@[simp]
theorem hardyMultiplierHom_apply (a : hardyMultiplierAlgebra) :
    hardyMultiplierHom a = toeplitz a := (rfl)

/-- Boundary H∞ is represented isometrically on Hardy space. -/
theorem isometry_hardyMultiplierHom : Isometry hardyMultiplierHom :=
  AddMonoidHomClass.isometry_of_norm hardyMultiplierHom (fun a ↦ norm_toeplitz a)

/-- The multiplier operators are precisely the commutant of the forward shift. -/
theorem range_hardyMultiplierHom :
    hardyMultiplierHom.range = Subalgebra.centralizer ℂ
      ({toeplitz (fourierLp (T := 1) ∞ 1)} : Set (HardySpace →L[ℂ] HardySpace)) := by
  ext T
  simp only [AlgHom.mem_range, Subalgebra.mem_centralizer_iff, Set.mem_singleton_iff,
    forall_eq]
  constructor
  · rintro ⟨a, rfl⟩
    exact ((commute_toeplitz_fourierLp_one_iff a).mpr a.property).eq.symm
  · intro h
    obtain ⟨a, ha, _⟩ := (existsUnique_toeplitz_eq_iff_commute T).mpr h.symm
    exact ⟨a, ha⟩

end TauCeti
