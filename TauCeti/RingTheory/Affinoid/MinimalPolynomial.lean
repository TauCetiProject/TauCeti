/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Affinoid.SupSeminorm
public import TauCeti.FieldTheory.Minpoly.TorsionFree

import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.RingTheory.Ideal.GoingUp

/-!
# Minimal polynomials and the supremum seminorm

Let `B` be an affinoid algebra over a complete nonarchimedean field `K`, integral over a
`K`-algebra `A`, and let `f : B` be a root of a monic polynomial
`p = X ^ d + ∑_{i < d} aᵢ X ^ i` over `A` which divides every polynomial over `A` vanishing
at `f`. Then the supremum seminorm of `f` is the spectral value of `p` for the supremum
seminorm of `A`:

`|f|sup = max_{i < d} |aᵢ|sup ^ (1 / (d - i))`.

For `d = 0` both sides vanish, since then `B = 0`.

The inequality `≤` holds for every monic equation of `f`, by
`TauCeti.IsAffinoidAlgebra.supSeminorm_le_iSup_coeff_rpow_of_eval_eq_zero`. For `≥`, fix a
classical point `x` of `A` and a root `α` of the reduction of `p` in an algebraic closure of
`A ⧸ x`. Evaluation at `α` factors through `A[f] ≅ A[X] ⧸ (p)`, and its kernel is a maximal
ideal of `A[f]` lying under a classical point `y` of `B`, at which `|f(y)| = |α|`. Hence every
root of the reduction of `p` at `x` has absolute value at most `|f|sup`, and so do the
coefficients `|aᵢ(x)| ^ (1 / (d - i))` of the reduction.

When `A` is an integrally closed domain and `B` is a torsion-free algebra, the minimal polynomial
of `f` over `A` satisfies these hypotheses. This applies to a finite injective map from a Tate
algebra into an affinoid domain, as in a Noether normalisation, since Tate algebras are unique
factorisation domains and hence integrally closed. The statement with a divisibility hypothesis
also applies without torsion-freeness when an annihilating polynomial with the required
divisibility property is supplied. Nilpotents in `B` are retained throughout.

## Main results

* `TauCeti.IsAffinoidAlgebra.supSeminorm_eq_iSup_coeff_rpow_of_dvd`: `|f|sup` is the spectral
  value of a monic polynomial generating the annihilator of `f`.
* `TauCeti.IsAffinoidAlgebra.supSeminorm_eq_iSup_minpoly_coeff_rpow`: `|f|sup` is the spectral
  value of the minimal polynomial of `f` over an integrally closed domain.

## References

* [Bosch, Güntzer, Remmert, *Non-Archimedean Analysis*][bosch-guntzer-remmert], §3.8.1,
  Proposition 7.
-/

public section

namespace TauCeti.IsAffinoidAlgebra

open Polynomial

variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {A : Type*} [CommRing A] [Algebra K A] {B : Type*} [CommRing B] [Algebra K B]
  [Algebra A B] [IsScalarTower K A B]

/-- A root `α` of `p` in a field `Ω` over `A`, whose kernel on `A` is maximal, is the value of
`f` at a classical point of `B`, provided `p` divides every polynomial vanishing at `f`. -/
private theorem exists_pointNorm_eq_spectralNorm (hB : IsAffinoidAlgebra K B)
    [Algebra.IsIntegral A B] {f : B} {p : A[X]} (hdvd : ∀ q : A[X], aeval f q = 0 → p ∣ q)
    {Ω : Type*} [Field Ω] [Algebra A Ω] [Algebra K Ω] [IsScalarTower K A Ω]
    (hΩ : (RingHom.ker (algebraMap A Ω)).IsMaximal) {α : Ω} (hα : aeval α p = 0) :
    ∃ y : MaximalSpectrum B, pointNorm K y f = spectralNorm K Ω α := by
  -- Evaluation at `α` factors through `S = A[f]`, a quotient of `A[X]` by the annihilator of `f`.
  let S := (aeval (R := A) f).range
  let g : A[X] →ₐ[A] S := (aeval f).rangeRestrict
  have hg : Function.Surjective g := AlgHom.rangeRestrict_surjective _
  have hgval (q : A[X]) : (g q : B) = aeval f q := AlgHom.coe_codRestrict _ _ _ q
  have hker (q : A[X]) (hq : q ∈ RingHom.ker g) : aeval α q = 0 := by
    have hfq : aeval f q = 0 := by
      rw [← hgval, RingHom.mem_ker.mp hq, ZeroMemClass.coe_zero]
    obtain ⟨r, rfl⟩ := hdvd q hfq
    rw [map_mul, hα, zero_mul]
  let χ : S →ₐ[A] Ω := (Ideal.Quotient.liftₐ (RingHom.ker g) (aeval α) hker).comp
    (Ideal.quotientKerAlgEquivOfSurjective hg).symm.toAlgHom
  have hχ (q : A[X]) : χ (g q) = aeval α q := by
    have : (Ideal.quotientKerAlgEquivOfSurjective hg).symm (g q) = Ideal.Quotient.mk _ q := by
      rw [AlgEquiv.symm_apply_eq, Ideal.quotientKerAlgEquivOfSurjective_mk]
    simp only [χ, AlgHom.comp_apply, AlgEquiv.coe_toAlgHom, this]
    exact Ideal.Quotient.lift_mk _ _ _
  -- The kernel of `χ` is a maximal ideal of `S`, since `S` is integral over `A`.
  have : Algebra.IsIntegral A S := ⟨fun s ↦ (isIntegral_algHom_iff S.val Subtype.val_injective).mp
    (Algebra.IsIntegral.isIntegral (R := A) (s : B))⟩
  have hcomap : (RingHom.ker χ).comap (algebraMap A S) = RingHom.ker (algebraMap A Ω) := by
    ext a
    simp [RingHom.mem_ker]
  have := RingHom.ker_isPrime χ
  have hmax : (RingHom.ker χ).IsMaximal :=
    Ideal.isMaximal_of_isIntegral_of_isMaximal_comap (algebraMap A S)
      (fun s ↦ Algebra.IsIntegral.isIntegral (R := A) s) _ (hcomap ▸ hΩ)
  -- It lies under a classical point of `B`, which is integral over `S`.
  have : Algebra.IsIntegral S B := Algebra.IsIntegral.tower_top A
  obtain ⟨y, hy⟩ := hB.maximalSpectrumComap_surjective (S.val.restrictScalars K)
    (fun b ↦ Algebra.IsIntegral.isIntegral (R := S) b) Subtype.val_injective ⟨_, hmax⟩
  refine ⟨y, ?_⟩
  have hfS : f ∈ S := (AlgHom.mem_range _).mpr ⟨X, aeval_X f⟩
  have hfα : χ ⟨f, hfS⟩ = α := by
    rw [← aeval_X (R := A) α, ← hχ X]
    exact congrArg χ (Subtype.ext (by rw [hgval, aeval_X]))
  rw [← hfα, ← AlgHom.restrictScalars_apply K χ,
    ← pointNorm_eq_spectralNorm (x := ⟨_, hmax⟩) le_rfl, ← hy,
    hB.pointNorm_maximalSpectrumComap]
  simp only [AlgHom.restrictScalars_apply, Subalgebra.coe_val]

/-- At a classical point `x` of `A`, each coefficient of `p` satisfies
`|aᵢ(x)| ≤ |f|sup ^ (d - i)`, provided `p` divides every polynomial vanishing at `f`. -/
private theorem pointNorm_coeff_le_supSeminorm_pow (hB : IsAffinoidAlgebra K B)
    [Algebra.IsIntegral A B] [FaithfulSMul A B] {f : B} {p : A[X]} (hp : p.Monic)
    (hdvd : ∀ q : A[X], aeval f q = 0 → p ∣ q) (x : MaximalSpectrum A) (i : ℕ) :
    pointNorm K x (p.coeff i) ≤ supSeminorm K f ^ (p.natDegree - i) := by
  -- Compute the point norms at `x` in an algebraic closure `Ω` of the residue field.
  let := Ideal.Quotient.field x.asIdeal
  have := hB.finite_quotient_of_isIntegral (IsScalarTower.toAlgHom K A B)
    (fun b ↦ Algebra.IsIntegral.isIntegral (R := A) b) (FaithfulSMul.algebraMap_injective A B)
    x.asIdeal
  let Ω := AlgebraicClosure (A ⧸ x.asIdeal)
  have : Algebra.IsAlgebraic K Ω := Algebra.IsAlgebraic.trans K (A ⧸ x.asIdeal) Ω
  have hker : RingHom.ker (algebraMap A Ω) = x.asIdeal := by
    rw [IsScalarTower.algebraMap_eq A (A ⧸ x.asIdeal) Ω,
      RingHom.ker_comp_of_injective _ (algebraMap (A ⧸ x.asIdeal) Ω).injective,
      Ideal.Quotient.algebraMap_eq, Ideal.mk_ker]
  rw [pointNorm_eq_spectralNorm (ψ := IsScalarTower.toAlgHom K A Ω) hker.ge]
  -- The roots of `p` in `Ω` are values of `f` at classical points of `B`.
  set P := p.map (algebraMap A Ω)
  have hP : P.Monic := hp.map _
  have hM (α : Ω) (hα : α ∈ P.roots) : spectralMulAlgNorm K Ω α ≤ supSeminorm K f := by
    rw [mem_roots hP.ne_zero, IsRoot, eval_map_algebraMap] at hα
    obtain ⟨y, hy⟩ := hB.exists_pointNorm_eq_spectralNorm hdvd (hker.symm ▸ x.isMaximal) hα
    rw [spectralMulAlgNorm_def, ← hy]
    exact hB.pointNorm_le_supSeminorm y f
  have h := hP.apply_coeff_le_pow_of_card_roots (map_one _).le
    (fun a b ↦ by simpa only [spectralMulAlgNorm_def] using isNonarchimedean_spectralNorm a b)
    (IsAlgClosed.splits P).natDegree_eq_card_roots.symm hM i
  rwa [spectralMulAlgNorm_def, coeff_map, hp.natDegree_map] at h

/-- **The supremum seminorm is the spectral value of a minimal equation.** Let `B` be an
affinoid algebra integral over `A`, and let `f : B` be a root of a monic polynomial
`p = X ^ d + ∑_{i < d} aᵢ X ^ i` over `A` dividing every polynomial over `A` which vanishes at
`f`. Then `|f|sup = max_{i < d} |aᵢ|sup ^ (1 / (d - i))`. -/
theorem supSeminorm_eq_iSup_coeff_rpow_of_dvd (hB : IsAffinoidAlgebra K B)
    [Algebra.IsIntegral A B] {p : A[X]} (hp : p.Monic) {f : B} (hf : aeval f p = 0)
    (hdvd : ∀ q : A[X], aeval f q = 0 → p ∣ q) :
    supSeminorm K f =
      ⨆ i : Fin p.natDegree, supSeminorm K (p.coeff i) ^ (1 / (p.natDegree - i : ℝ)) := by
  rcases Nat.eq_zero_or_pos p.natDegree with h0 | hpos
  · -- A monic equation of degree zero forces `B = 0`.
    have : Subsingleton B := by
      rw [hp.natDegree_eq_zero.mp h0, map_one] at hf
      exact subsingleton_of_zero_eq_one hf.symm
    have : IsEmpty (Fin p.natDegree) := h0 ▸ Fin.isEmpty'
    rw [supSeminorm_eq_zero_of_subsingleton, Real.iSup_of_isEmpty]
  -- A nonzero element of `A` is not divisible by `p`, so `A` embeds into `B`.
  have : FaithfulSMul A B := by
    rw [faithfulSMul_iff_algebraMap_injective, injective_iff_map_eq_zero]
    intro a ha
    by_contra ha0
    exact hp.not_dvd_of_natDegree_lt (C_ne_zero.mpr ha0) (by rwa [natDegree_C])
      (hdvd _ (by rwa [aeval_C]))
  have hcoeff (a : A) : supSeminorm K (algebraMap A B a) = supSeminorm K a :=
    hB.supSeminorm_map_of_isIntegral (IsScalarTower.toAlgHom K A B)
      (fun b ↦ Algebra.IsIntegral.isIntegral (R := A) b) (FaithfulSMul.algebraMap_injective A B) a
  refine le_antisymm ?_ (Real.iSup_le (fun i ↦ ?_) (supSeminorm_nonneg f))
  · have h := hB.supSeminorm_le_iSup_coeff_rpow_of_eval_eq_zero (hp.map (algebraMap A B))
      (f := f) (by rwa [eval_map_algebraMap])
    rw [natDegree_map_eq_of_injective (FaithfulSMul.algebraMap_injective A B)] at h
    simpa only [coeff_map, hcoeff] using h
  · have hi : (p.natDegree - i : ℝ) = ((p.natDegree - i : ℕ) : ℝ) := by
      rw [Nat.cast_sub i.2.le]
    have hle : supSeminorm K (p.coeff i) ≤ supSeminorm K f ^ (p.natDegree - i : ℕ) :=
      supSeminorm_le (pow_nonneg (supSeminorm_nonneg f) _) fun x ↦
        hB.pointNorm_coeff_le_supSeminorm_pow hp hdvd x i
    rw [hi, one_div, Real.rpow_inv_le_iff_of_pos (supSeminorm_nonneg _) (supSeminorm_nonneg f)
      (by exact_mod_cast Nat.sub_pos_of_lt i.2), Real.rpow_natCast]
    exact hle

/-- **The supremum seminorm is the spectral value of the minimal polynomial.** Let `B` be an
affinoid algebra which is integral and torsion-free over an integrally closed domain `A`. For
`f : B` with minimal polynomial `X ^ d + ∑_{i < d} aᵢ X ^ i` over `A`,
`|f|sup = max_{i < d} |aᵢ|sup ^ (1 / (d - i))`. -/
theorem supSeminorm_eq_iSup_minpoly_coeff_rpow (hB : IsAffinoidAlgebra K B) [IsDomain A]
    [IsIntegrallyClosed A] [Module.IsTorsionFree A B] [Algebra.IsIntegral A B]
    (f : B) :
    supSeminorm K f = ⨆ i : Fin (minpoly A f).natDegree,
      supSeminorm K ((minpoly A f).coeff i) ^ (1 / ((minpoly A f).natDegree - i : ℝ)) :=
  have hf := Algebra.IsIntegral.isIntegral (R := A) f
  hB.supSeminorm_eq_iSup_coeff_rpow_of_dvd (minpoly.monic hf) (minpoly.aeval A f)
    fun _ ↦ minpoly.isIntegrallyClosed_dvd_of_isTorsionFree hf

end TauCeti.IsAffinoidAlgebra
