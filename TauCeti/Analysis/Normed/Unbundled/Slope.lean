/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Unbundled.SpectralNorm
public import Mathlib.RingTheory.Spectrum.Maximal.Defs

import Mathlib.RingTheory.AdjoinRoot
import Mathlib.RingTheory.Ideal.GoingUp

/-!
# Numerical slopes of polynomials

Let `K` be a nonarchimedean field and `A` a `K`-algebra. A polynomial `Q : A[X]` has *slope at
most `r`*, for a real cutoff `r > 0`, if for every `K`-algebra map `χ : A → L` into an algebraic
extension `L` of `K` in the universe of `A`, every root of `χ(Q)` has absolute value at least
`r`. The absolute value of a root is its spectral norm over `K`, which is the unique extension of
the norm of `K` when `K` is complete; no embedding into a chosen algebraic closure is involved. For
`r = |p| ^ h` this says that every root has valuation at most `h`. The condition concerns roots of
an annihilating polynomial, not of a Fredholm series `det (1 - T U)`, whose roots are the
reciprocals.

For an affinoid algebra `A` the condition can be tested at all classical points, using finite
residue-field extensions and their finite splitting extensions together with the nonvanishing of
each reduction `Q mod x`, and then holds for algebraic extensions in every universe; see
`TauCeti.IsAffinoidAlgebra.isSlopeLE_iff_splittingField` and
`TauCeti.IsAffinoidAlgebra.le_spectralNorm_of_isSlopeLE`.

## Main definitions

* `Polynomial.IsSlopeLE K r Q`: every root of `Q` at every algebraic point, with values in the
  universe of `A`, has absolute value at least `r > 0`.

## Main results

* `Polynomial.le_spectralNorm_of_forall_splittingField`: if, for every maximal ideal `x`, the
  reduction `Q mod x` is nonzero and its roots in a splitting field over `A ⧸ x` have spectral norm
  at least `r`, then so do the roots of `χ(Q)` for every `K`-algebra map `χ` into an algebraic
  extension, in any universe.

## References

* E. Urban, *Eigenvarieties for reductive groups*, Ann. of Math. 174 (2011), 1685–1784, §2.3.
-/

public section

open Polynomial

universe v

namespace Polynomial

variable (K : Type*) [NormedField K] {A : Type v} [CommRing A] [Algebra K A]

/-- A polynomial `Q : A[X]` has slope at most `r` over `K` if `r > 0` and, for every `K`-algebra
map `χ : A → L` into an algebraic extension `L` of `K` in the universe of `A`, every root of
`χ(Q)` has spectral norm at least `r`. For `r = |p| ^ h` this says that every root has valuation
at most `h`. Over an affinoid algebra the bound then holds in every universe, by
`TauCeti.IsAffinoidAlgebra.le_spectralNorm_of_isSlopeLE`. -/
def IsSlopeLE (r : ℝ) (Q : A[X]) : Prop :=
  0 < r ∧ ∀ (L : Type v) [Field L] [Algebra K L] [Algebra.IsAlgebraic K L] (χ : A →ₐ[K] L) (α : L),
    (Q.map (χ : A →+* L)).IsRoot α → r ≤ spectralNorm K L α

variable {K} {r s : ℝ} {P Q : A[X]}

/-- The defining property of `Polynomial.IsSlopeLE`. -/
theorem isSlopeLE_iff : Q.IsSlopeLE K r ↔
    0 < r ∧ ∀ (L : Type v) [Field L] [Algebra K L] [Algebra.IsAlgebraic K L] (χ : A →ₐ[K] L)
      (α : L), (Q.map (χ : A →+* L)).IsRoot α → r ≤ spectralNorm K L α :=
  Iff.rfl

/-- The cutoff of the slope condition is positive. -/
theorem IsSlopeLE.pos (hQ : Q.IsSlopeLE K r) : 0 < r :=
  hQ.1

/-- Under the slope condition, every root of `χ(Q)` in an algebraic extension has spectral norm
at least the cutoff. -/
theorem IsSlopeLE.le_spectralNorm (hQ : Q.IsSlopeLE K r) {L : Type v} [Field L] [Algebra K L]
    [Algebra.IsAlgebraic K L] (χ : A →ₐ[K] L) {α : L} (hα : (Q.map (χ : A →+* L)).IsRoot α) :
    r ≤ spectralNorm K L α :=
  hQ.2 L χ α hα

/-- Lowering a positive cutoff preserves the slope condition. -/
theorem IsSlopeLE.mono (hQ : Q.IsSlopeLE K r) (hs : 0 < s) (hsr : s ≤ r) : Q.IsSlopeLE K s :=
  ⟨hs, fun _ _ _ _ χ _ hα ↦ hsr.trans (hQ.le_spectralNorm χ hα)⟩

/-- The constant polynomial `1` has no roots, so it has slope at most every positive cutoff. -/
@[simp]
theorem isSlopeLE_one_iff : (1 : A[X]).IsSlopeLE K r ↔ 0 < r := by
  simp [isSlopeLE_iff]

/-- `P * Q` has slope at most `r` if and only if both `P` and `Q` do, since the roots of a
product are the roots of its factors. -/
@[simp]
theorem isSlopeLE_mul_iff : (P * Q).IsSlopeLE K r ↔ P.IsSlopeLE K r ∧ Q.IsSlopeLE K r := by
  simp only [isSlopeLE_iff, Polynomial.map_mul, IsRoot, eval_mul, mul_eq_zero]
  exact ⟨fun h ↦ ⟨⟨h.1, fun L _ _ _ χ α hα ↦ h.2 L χ α (.inl hα)⟩,
    ⟨h.1, fun L _ _ _ χ α hα ↦ h.2 L χ α (.inr hα)⟩⟩,
    fun h ↦ ⟨h.1.1, fun L _ _ _ χ α hα ↦ hα.elim (h.1.2 L χ α) (h.2.2 L χ α)⟩⟩

/-- The linear polynomial `X - c` has slope at most `r` when `0 < r ≤ |c|`. -/
theorem isSlopeLE_X_sub_C_algebraMap {c : K} (hr : 0 < r) (hrc : r ≤ ‖c‖) :
    (X - C (algebraMap K A c)).IsSlopeLE K r := by
  refine ⟨hr, fun L _ _ _ χ α hα ↦ ?_⟩
  obtain rfl : α = algebraMap K L c := by simpa [sub_eq_zero] using hα
  rwa [spectralNorm_extends]

/-- The polynomial `1 - c X`, whose root `c⁻¹` is the reciprocal of that of `X - c`, has slope
at most `r` when `0 < r ≤ |c|⁻¹`. -/
theorem isSlopeLE_one_sub_C_mul_X_algebraMap {c : K} (hr : 0 < r)
    (hrc : r ≤ ‖c‖⁻¹) : (1 - C (algebraMap K A c) * X).IsSlopeLE K r := by
  refine ⟨hr, fun L _ _ _ χ α hα ↦ ?_⟩
  have hα : 1 - algebraMap K L c * α = 0 := by simpa using hα
  rwa [eq_inv_of_mul_eq_one_right (sub_eq_zero.1 hα).symm, ← map_inv₀, spectralNorm_extends,
    norm_inv]

/-- If, at every maximal ideal `x`, the reduction `Q mod x` is nonzero and its roots in a
splitting field over `A ⧸ x` have spectral norm at least `r`, then so does every root `α` of
`χ(Q)` in an algebraic extension `L` of `K`, in any universe. Indeed `α` lies over the maximal
ideal `ker χ`, and its minimal polynomial over `A ⧸ ker χ` has a root `β` in the splitting field;
`α` and `β` are then conjugate over `K`. -/
theorem le_spectralNorm_of_forall_splittingField
    (h : ∀ x : MaximalSpectrum A,
      letI := Ideal.Quotient.field x.asIdeal
      Q.map (Ideal.Quotient.mk x.asIdeal) ≠ 0 ∧
        ∀ β ∈ (Q.map (Ideal.Quotient.mk x.asIdeal)).rootSet
          (Q.map (Ideal.Quotient.mk x.asIdeal)).SplittingField,
          r ≤ spectralNorm K _ β)
    {L : Type*} [Field L] [Algebra K L] [Algebra.IsAlgebraic K L] (χ : A →ₐ[K] L) {α : L}
    (hα : (Q.map (χ : A →+* L)).IsRoot α) : r ≤ spectralNorm K L α := by
  -- `L` is integral over `A` along `χ`, so the kernel of `χ` is maximal.
  let : Algebra A L := (χ : A →+* L).toAlgebra
  have : IsScalarTower K A L := .of_algebraMap_eq fun c ↦ (χ.commutes c).symm
  have : Algebra.IsIntegral A L := .tower_top K
  set I := RingHom.ker χ
  have hI : I.IsMaximal := Ideal.isMaximal_comap_of_isIntegral_of_isMaximal (χ : A →+* L)
    (fun y ↦ Algebra.IsIntegral.isIntegral (R := A) y) ⊥
  let := Ideal.Quotient.field I
  let F := A ⧸ I
  let Q' : F[X] := Q.map (Ideal.Quotient.mk I)
  obtain ⟨hQ', hroots⟩ := h ⟨I, hI⟩
  -- Make `L` an algebra over the residue field `F` through the injection `F → L` induced by `χ`.
  let : Algebra F L := (Ideal.kerLiftAlg χ : F →+* L).toAlgebra
  have : IsScalarTower K F L :=
    .of_algebraMap_eq fun c ↦ ((Ideal.kerLiftAlg χ).commutes c).symm
  have hmk : (algebraMap F L).comp (Ideal.Quotient.mk I) = (χ : A →+* L) :=
    RingHom.ext (Ideal.kerLiftAlg_mk χ)
  have hint : IsIntegral F α := (Algebra.IsIntegral.isIntegral (R := K) α).tower_top
  have hQα : aeval α Q' = 0 := by
    rwa [aeval_def, eval₂_map, hmk, ← eval_map]
  -- The minimal polynomial of `α` over `F` divides `Q mod x`, so it has a root in the splitting
  -- field of `Q mod x`.
  let S := Q'.SplittingField
  let q := minpoly F α
  have hdvd : q ∣ Q' := minpoly.dvd F α hQα
  obtain ⟨β, hβ⟩ := (SplittingField.splits Q').of_dvd (Polynomial.map_ne_zero hQ')
    (Polynomial.map_dvd _ hdvd) |>.exists_eval_eq_zero
      (by rw [degree_map]; exact (minpoly.degree_pos hint).ne')
  rw [eval_map_algebraMap] at hβ
  have hβQ : β ∈ Q'.rootSet S :=
    (mem_rootSet' (S := S)).2
      ⟨Polynomial.map_ne_zero hQ', aeval_eq_zero_of_dvd_aeval_eq_zero hdvd hβ⟩
  -- `α` and `β` are both images of the root of `q` under `K`-algebra maps of fields, so they have
  -- the same minimal polynomial over `K`, hence the same spectral norm.
  have : Fact (Irreducible q) := ⟨minpoly.irreducible hint⟩
  let ψL : AdjoinRoot q →ₐ[K] L :=
    AdjoinRoot.liftAlgHom q (IsScalarTower.toAlgHom K F L) α (minpoly.aeval F α)
  let ψS : AdjoinRoot q →ₐ[K] S := AdjoinRoot.liftAlgHom q (IsScalarTower.toAlgHom K F S) β hβ
  have hψS : ψS (AdjoinRoot.root q) = β := AdjoinRoot.liftAlgHom_root q _ β hβ
  have hψL : ψL (AdjoinRoot.root q) = α := AdjoinRoot.liftAlgHom_root q _ α _
  have hmin : minpoly K β = minpoly K α := by
    rw [← hψS, ← hψL, minpoly.algHom_eq ψS ψS.toRingHom.injective,
      minpoly.algHom_eq ψL ψL.toRingHom.injective]
  calc r ≤ spectralNorm K S β := hroots β hβQ
    _ = spectralNorm K L α := by simp only [spectralNorm, hmin]

end Polynomial
