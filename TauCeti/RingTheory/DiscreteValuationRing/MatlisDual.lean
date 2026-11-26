/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.RingTheory.OrderOfVanishing.Noetherian
public import TauCeti.Algebra.Module.Injective.Cogenerator
public import TauCeti.LinearAlgebra.Pi.Orthogonal
public import TauCeti.RingTheory.DiscreteValuationRing.Length
import TauCeti.Algebra.Module.Injective.PrincipalIdealRing

/-!
# Matlis duality over a discrete valuation ring and lengths of orthogonals in `(K/O)ⁿ`

Let `O` be a discrete valuation ring with fraction field `K`. The module `K/O` is injective
over `O`, and `Hom_O(O/𝔪, K/O)` is simple, so `Hom_O(-, K/O)` preserves lengths
(`TauCeti.length_linearMap_of_forall_isMaximal`). Applied to quotients of `Oⁿ`, this computes
the length of the orthogonal in `(K/O)ⁿ` of a submodule `R ⊆ Oⁿ` under the pairing
`⟨v, u⟩ = ∑ i, v i • u i` (`Submodule.orthogonalPi`): it is the colength of `R`. For the span of
the rows of a square matrix `M` the orthogonal is the kernel of `M` acting on `(K/O)ⁿ`, and its
length is the valuation of `det M`, both infinite when `det M = 0`.

## Main definitions

* `IsDiscreteValuationRing.divQuotient`: division by `a`, the map `O/a → K/O`, `t ↦ t/a`.
* `IsDiscreteValuationRing.quotientEquivTorsionBySet`: for `a ≠ 0`, the identification of `O/a`
  with the elements of `K/O` killed by `a`.

## Main results

* `IsDiscreteValuationRing.length_linearMap_quotient_span_singleton`: for `a ≠ 0`,
  `Hom_O(O/a, K/O)` has length `v(a)`.
* `IsDiscreteValuationRing.length_linearMap_fractionRing_quotient`: `Hom_O(M, K/O)` has the
  length of `M`, for every `O`-module `M` (Matlis duality over a discrete valuation ring).
* `IsDiscreteValuationRing.length_orthogonalPi`: the orthogonal of `R ⊆ Oⁿ` in `(K/O)ⁿ` has
  length `length_O (Oⁿ/R)`.
* `Matrix.length_ker_eq_addVal_det`: the kernel of a square matrix `M` acting on `(K/O)ⁿ` has
  length `v(det M)`.

## Provenance

The kernel bound `length ker ≤ v(det M)` on `(O/p)ⁿ` is `New.length_ker_le_addVal_det` in
grh-lean (https://github.com/lsernau/grh-lean, file
`src/Lib/General/Algebra/FittingIdealsAndLengths.lean`, Apache 2.0, Copyright 2026 Anthropic,
PBC), proved there by Smith normal form. The equality `length ker = v(det M)` on `(K/O)ⁿ`, with
`K = FractionRing O`, is `Formalism.NG.lenKer` in L. Alpöge's Lean formalization of the
Riemann hypothesis project (https://github.com/leanprover-community/riemann-hypothesis, file
`src/Formalism/CharacterColumnKernels/IdempotentNormalForms/LengthKerOfDetEqZero.lean`); the
statement `Matrix.length_ker_eq_addVal_det` follows it, for any fraction field `K`. The proof here
goes through Matlis duality and the cokernel length formula
`Matrix.length_quotient_range_mulVecLin_eq_ord_det`.

## References

* E. Matlis, *Injective modules over Noetherian rings*, Pacific J. Math. 8 (1958).
* The Stacks Project, Section 47.7, Matlis duality, Tag 08Z1.
-/

public section

open IsLocalRing LinearMap

namespace IsDiscreteValuationRing

universe u v

variable {O : Type u} {K : Type v} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [Field K] [Algebra O K] [IsFractionRing O K]

/-- Division by `a`, the functional `O/a → K/O` sending the class of `t` to the class of `t/a`.
For `a ≠ 0` it identifies `O/a` with the elements of `K/O` killed by `a`
(`IsDiscreteValuationRing.quotientEquivTorsionBySet`). -/
noncomputable def divQuotient (a : O) :
    O ⧸ Ideal.span {a} →ₗ[O] K ⧸ range (Algebra.linearMap O K) :=
  (Ideal.span {a}).liftQ
    ((range (Algebra.linearMap O K)).mkQ ∘ₗ toSpanSingleton O K (algebraMap O K a)⁻¹)
    (by
      rw [Ideal.span_singleton_le_iff_mem, mem_ker, comp_apply, Submodule.mkQ_apply,
        Submodule.Quotient.mk_eq_zero]
      rcases eq_or_ne a 0 with rfl | ha
      · simp
      · exact ⟨1, by simp [Algebra.smul_def, IsFractionRing.to_map_eq_zero_iff.not.2 ha]⟩)

omit [IsDomain O] [IsDiscreteValuationRing O] in
@[simp]
theorem divQuotient_mk (a t : O) :
    divQuotient (K := K) a (Ideal.Quotient.mk (Ideal.span {a}) t) =
      Submodule.Quotient.mk (t • (algebraMap O K a)⁻¹) := by
  rw [← Ideal.Quotient.mk_eq_mk, divQuotient, Submodule.liftQ_apply, comp_apply,
    toSpanSingleton_apply, Submodule.mkQ_apply]

omit [IsDiscreteValuationRing O] in
/-- For `a ≠ 0`, `divQuotient a` identifies `O/a` with the elements of `K/O` killed by `a`. -/
noncomputable def quotientEquivTorsionBySet {a : O} (ha : a ≠ 0) :
    (O ⧸ Ideal.span {a}) ≃ₗ[O]
      Submodule.torsionBySet O (K ⧸ range (Algebra.linearMap O K)) (Ideal.span {a}) := by
  have ha' : algebraMap O K a ≠ 0 := IsFractionRing.to_map_eq_zero_iff.not.2 ha
  have htors : Submodule.torsionBySet O (K ⧸ range (Algebra.linearMap O K)) (Ideal.span {a}) =
      Submodule.torsionBy O _ a :=
    Submodule.torsionBySet_span_singleton_eq a
  refine LinearEquiv.ofBijective ((divQuotient a).codRestrict _ fun x ↦ ?_) ⟨?_, ?_⟩
  · rw [htors, Submodule.mem_torsionBy_iff]
    induction x using Submodule.Quotient.induction_on with | _ t =>
    rw [Ideal.Quotient.mk_eq_mk, divQuotient_mk, ← Submodule.Quotient.mk_smul,
      Submodule.Quotient.mk_eq_zero]
    exact ⟨t, by rw [Algebra.linearMap_apply, Algebra.smul_def, Algebra.smul_def,
      mul_left_comm, mul_inv_cancel₀ ha', mul_one]⟩
  · rw [← LinearMap.ker_eq_bot, LinearMap.ker_codRestrict, eq_bot_iff]
    intro r hr
    induction r using Submodule.Quotient.induction_on with | _ r =>
    rw [mem_ker, Ideal.Quotient.mk_eq_mk, divQuotient_mk, Submodule.Quotient.mk_eq_zero] at hr
    obtain ⟨s, hs⟩ := hr
    rw [Submodule.mem_bot, Submodule.Quotient.mk_eq_zero, Ideal.mem_span_singleton]
    refine ⟨s, IsFractionRing.injective O K ?_⟩
    rw [Algebra.linearMap_apply] at hs
    rw [map_mul, hs, Algebra.smul_def, mul_left_comm, mul_inv_cancel₀ ha', mul_one]
  · rintro ⟨x, hx⟩
    rw [htors, Submodule.mem_torsionBy_iff] at hx
    obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero] at hx
    obtain ⟨r, hr⟩ := hx
    rw [Algebra.linearMap_apply] at hr
    refine ⟨Submodule.Quotient.mk r, Subtype.ext ?_⟩
    rw [LinearMap.codRestrict_apply, Ideal.Quotient.mk_eq_mk, divQuotient_mk, Algebra.smul_def, hr,
      Algebra.smul_def, mul_comm, ← mul_assoc, inv_mul_cancel₀ ha', one_mul]

omit [IsDomain O] [IsDiscreteValuationRing O] in
@[simp]
theorem coe_quotientEquivTorsionBySet_apply_mk {a : O} (ha : a ≠ 0) (t : O) :
    (quotientEquivTorsionBySet (K := K) ha (Ideal.Quotient.mk (Ideal.span {a}) t) :
      K ⧸ range (Algebra.linearMap O K)) =
      Submodule.Quotient.mk (t • (algebraMap O K a)⁻¹) :=
  divQuotient_mk a t

/-- For `a ≠ 0`, `Hom_O(O/a, K/O)` has length `v(a)`. -/
theorem length_linearMap_quotient_span_singleton {a : O} (ha : a ≠ 0) :
    Module.length O (O ⧸ Ideal.span {a} →ₗ[O] K ⧸ range (Algebra.linearMap O K)) =
      addVal O a := by
  rw [((Ideal.span {a}).quotientLinearMapEquivTorsionBySet _).length_eq,
    ← (quotientEquivTorsionBySet ha).length_eq, ← Ring.ord, Ring.ord_eq_addVal]

/-- `Hom_O(O/𝔪, K/O)` is simple: `K/O` is an injective hull of the residue field. -/
theorem length_linearMap_quotient_maximalIdeal :
    Module.length O
      (O ⧸ IsLocalRing.maximalIdeal O →ₗ[O] K ⧸ range (Algebra.linearMap O K)) = 1 := by
  obtain ⟨ϖ, hϖ⟩ := exists_irreducible O
  rw [hϖ.maximalIdeal_eq, length_linearMap_quotient_span_singleton hϖ.ne_zero,
    addVal_uniformizer hϖ]

/-- **Matlis duality over a discrete valuation ring.** `Hom_O(M, K/O)` has the length of `M`,
for every `O`-module `M`: `K/O` is injective, and `Hom_O(O/𝔪, K/O)` has length one. -/
theorem length_linearMap_fractionRing_quotient (M : Type*) [AddCommGroup M] [Module O M] :
    Module.length O (M →ₗ[O] K ⧸ range (Algebra.linearMap O K)) = Module.length O M := by
  have : FaithfulSMul O K := (faithfulSMul_iff_algebraMap_injective O K).2
    (IsFractionRing.injective O K)
  have : Small.{v} O := small_of_injective (IsFractionRing.injective O K)
  refine TauCeti.length_linearMap_of_forall_isMaximal (fun 𝔪 h𝔪 ↦ ?_) M
  rw [IsLocalRing.eq_maximalIdeal h𝔪]
  exact length_linearMap_quotient_maximalIdeal

variable {ι : Type*} [Fintype ι]

/-- **The orthogonal in `(K/O)^ι` of a submodule `R ⊆ O^ι` has the colength of `R`.** The
orthogonal is `Hom_O(O^ι / R, K/O)`, and Matlis duality preserves lengths. -/
theorem length_orthogonalPi (R : Submodule O (ι → O)) :
    Module.length O (R.orthogonalPi (K ⧸ range (Algebra.linearMap O K))) =
      Module.length O ((ι → O) ⧸ R) := by
  classical
  rw [(R.orthogonalPiEquiv _).length_eq, length_linearMap_fractionRing_quotient]

end IsDiscreteValuationRing

namespace Matrix

open IsDiscreteValuationRing

variable {ι : Type*} {O K : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [Field K] [Algebra O K] [IsFractionRing O K] [Fintype ι] [DecidableEq ι]

/-- **The kernel of a square matrix on `(K/O)^ι` has length `v(det M)`.** The kernel of `M`
acting on `(K/O)^ι`, the orthogonal of the rows of `M`, has length the valuation of `det M`, both
sides infinite when `det M = 0`. -/
theorem length_ker_eq_addVal_det (M : Matrix ι ι O) :
    Module.length O (LinearMap.ker (LinearMap.pi fun i ↦ ∑ j, M i j •
        LinearMap.proj j : (ι → K ⧸ range (Algebra.linearMap O K)) →ₗ[O] _)) =
      addVal O M.det := by
  have hker : LinearMap.ker (LinearMap.pi fun i ↦ ∑ j, M i j •
        LinearMap.proj j : (ι → K ⧸ range (Algebra.linearMap O K)) →ₗ[O] _) =
      (Submodule.span O (Set.range M.row)).orthogonalPi _ := by
    ext u
    rw [LinearMap.mem_ker, Submodule.mem_orthogonalPi_span, Set.forall_mem_range, funext_iff]
    simp [Matrix.row]
  rw [hker, length_orthogonalPi, length_quotient_span_range_eq_addVal_det]

end Matrix
