/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Finsupp.LinearCombination
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.RingTheory.OrderOfVanishing.Noetherian
public import TauCeti.Algebra.Module.Injective.Cogenerator
public import TauCeti.RingTheory.Length.Determinant
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
import TauCeti.Algebra.Module.Injective.PrincipalIdealRing

/-!
# Lengths of orthogonals in `(K/O)ⁿ` over a discrete valuation ring

Let `O` be a discrete valuation ring with fraction field `K`. The module `K/O` is injective
over `O`, and `Hom_O(O/𝔪, K/O)` is simple, so `Hom_O(-, K/O)` preserves lengths
(`TauCeti.length_linearMap_of_forall_isMaximal`). Applied to quotients of `Oⁿ`, this computes
the length of the orthogonal in `(K/O)ⁿ` of a submodule `R ⊆ Oⁿ` under the pairing
`⟨v, u⟩ = ∑ i, v i • u i`: it is the colength of `R`. For the span of the rows of a square matrix
`M` the orthogonal is the kernel of `M` acting on `(K/O)ⁿ`, and its length is the valuation of
`det M` (both infinite when `det M = 0`); this is the linear algebra in the length formula of
`SelmerLengthBoundsAndLocalLifting` §3.23 and in the determinant lemma of
`LengthBoundsInPadicFamilies` §1.8b.

## Main definitions

* `Submodule.orthogonalPi`: the orthogonal `R^⊥ ⊆ Eⁿ` of a submodule `R ⊆ Oⁿ` under the pairing
  `∑ i, v i • u i`, for any `O`-module `E`.

## Main results

* `IsDiscreteValuationRing.length_linearMap_quotient_span_singleton`: for `a ≠ 0`,
  `Hom_O(O/a, K/O)` has length `v(a)`.
* `IsDiscreteValuationRing.length_linearMap_fractionRing_quotient`: `Hom_O(M, K/O)` has the
  length of `M`, for every `O`-module `M` (Matlis duality over a discrete valuation ring).
* `IsDiscreteValuationRing.length_orthogonalPi`: the orthogonal of `R ⊆ Oⁿ` in `(K/O)ⁿ` has
  length `length_O (Oⁿ/R)`.
* `Matrix.length_quotient_span_range_eq_addVal_det`: the rows of a square matrix `M` span a
  submodule of colength `v(det M)`, infinite when `det M = 0`.
* `Matrix.length_ker_eq_addVal_det`: the kernel of a square matrix `M` acting on `(K/O)ⁿ` has
  length `v(det M)`.

## Provenance

The kernel bound `length ker ≤ v(det M)` on `(O/p)ⁿ` is `New.length_ker_le_addVal_det` in
grh-lean (https://github.com/lsernau/grh-lean, file
`src/Lib/General/Algebra/FittingIdealsAndLengths.lean`, Apache 2.0, Copyright 2026 Anthropic,
PBC), proved there by Smith normal form. Here the equality on `(K/O)ⁿ` is derived instead from
Matlis duality and the cokernel length formula
`Matrix.length_quotient_range_mulVecLin_eq_ord_det`.

## References

* E. Matlis, *Injective modules over Noetherian rings*, Pacific J. Math. 8 (1958).
* The Stacks Project, Section 47.7, Matlis duality, Tag 08Z1.
-/

@[expose] public section

open IsLocalRing LinearMap

namespace Submodule

variable {O E ι : Type*} [CommRing O] [AddCommGroup E] [Module O E] [Fintype ι]

/-- The orthogonal of a submodule `R ⊆ O^ι` in `E^ι` under the pairing `⟨v, u⟩ = ∑ i, v i • u i`:
the vectors `u` with `⟨v, u⟩ = 0` for every `v ∈ R`. For `E = K/O` it is the Pontryagin dual of
`O^ι / R` (`IsDiscreteValuationRing.length_orthogonalPi`). -/
def orthogonalPi (E : Type*) [AddCommGroup E] [Module O E] (R : Submodule O (ι → O)) :
    Submodule O (ι → E) where
  carrier := {u | ∀ v ∈ R, ∑ i, v i • u i = 0}
  add_mem' {u w} hu hw v hv := by
    simp only [Pi.add_apply, smul_add, Finset.sum_add_distrib, hu v hv, hw v hv, add_zero]
  zero_mem' v _ := by simp
  smul_mem' c u hu v hv := by
    simp only [Pi.smul_apply, smul_comm (v _) c, ← Finset.smul_sum, hu v hv, smul_zero]

theorem mem_orthogonalPi {R : Submodule O (ι → O)} {u : ι → E} :
    u ∈ R.orthogonalPi E ↔ ∀ v ∈ R, ∑ i, v i • u i = 0 :=
  Iff.rfl

/-- The orthogonal of a span is cut out by the spanning vectors. -/
theorem mem_orthogonalPi_span {S : Set (ι → O)} {u : ι → E} :
    u ∈ (span O S).orthogonalPi E ↔ ∀ v ∈ S, ∑ i, v i • u i = 0 := by
  refine ⟨fun h v hv ↦ h v (subset_span hv), fun h v hv ↦ ?_⟩
  induction hv using span_induction with
  | mem v hv => exact h v hv
  | zero => simp
  | add v w _ _ hv hw => simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib, hv, hw,
      add_zero]
  | smul c v _ hv => simp only [Pi.smul_apply, smul_eq_mul, mul_smul, ← Finset.smul_sum, hv,
      smul_zero]

/-- Taking orthogonals reverses inclusions. -/
theorem orthogonalPi_anti {R R' : Submodule O (ι → O)} (h : R ≤ R') :
    R'.orthogonalPi E ≤ R.orthogonalPi E :=
  fun _ hu v hv ↦ hu v (h hv)

variable [DecidableEq ι]

/-- The orthogonal of `R ⊆ O^ι` in `E^ι` is `Hom_O(O^ι / R, E)`: a vector `u` corresponds to the
functional `v ↦ ∑ i, v i • u i`, which vanishes on `R`. -/
noncomputable def orthogonalPiEquiv (E : Type*) [AddCommGroup E] [Module O E]
    (R : Submodule O (ι → O)) : R.orthogonalPi E ≃ₗ[O] ((ι → O) ⧸ R →ₗ[O] E) where
  toFun u := R.liftQ (Fintype.linearCombination O u.val) fun v hv ↦ by
    simpa [Fintype.linearCombination_apply] using u.property v hv
  map_add' u w := by ext; simp [Fintype.linearCombination_apply, smul_add, Finset.sum_add_distrib]
  map_smul' c u := by
    ext; simp [Fintype.linearCombination_apply]
  invFun f := ⟨fun i ↦ f (R.mkQ (Pi.single i 1)), fun v hv ↦ by
    have hv' : v = ∑ i, v i • Pi.single i (1 : O) := by ext j; simp [Pi.single_apply]
    calc ∑ i, v i • f (R.mkQ (Pi.single i 1)) = f (R.mkQ v) := by
          conv_rhs => rw [hv']
          simp only [map_sum, map_smul]
      _ = 0 := by rw [mkQ_apply, (Quotient.mk_eq_zero R).2 hv, map_zero]⟩
  left_inv u := by ext i; simp [Fintype.linearCombination_apply, Pi.single_apply]
  right_inv f := by
    ext v
    simp [Fintype.linearCombination_apply]

end Submodule

namespace IsDiscreteValuationRing

universe u v

variable {O : Type u} {K : Type v} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [Field K] [Algebra O K] [IsFractionRing O K]

/-- A module containing an element with trivial annihilator, here the image of an injective map
`O → M`, has infinite length over a discrete valuation ring. -/
theorem length_eq_top_of_injective {M : Type*} [AddCommGroup M] [Module O M] {f : O →ₗ[O] M}
    (hf : Function.Injective f) : Module.length O M = ⊤ :=
  top_le_iff.1 (TauCeti.length_self_eq_top_of_ringKrullDim_pos
    (by rw [ringKrullDim_eq_one O]; exact zero_lt_one) ▸ Module.length_le_of_injective f hf)

/-- A module of finite length over a discrete valuation ring is torsion. -/
theorem isTorsion_of_length_ne_top {M : Type*} [AddCommGroup M] [Module O M]
    (hM : Module.length O M ≠ ⊤) : Module.IsTorsion O M := by
  intro x
  by_contra hx
  refine hM (length_eq_top_of_injective (f := LinearMap.toSpanSingleton O M x) fun r s h ↦ ?_)
  rw [← sub_eq_zero]
  by_contra hrs
  exact hx ⟨⟨r - s, mem_nonZeroDivisors_of_ne_zero hrs⟩, by simpa [sub_smul, sub_eq_zero] using h⟩

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
theorem divQuotient_mk (a t : O) :
    divQuotient (K := K) a (Submodule.Quotient.mk t) =
      Submodule.Quotient.mk (t • (algebraMap O K a)⁻¹) :=
  rfl

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
    rw [divQuotient_mk, ← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
    exact ⟨t, by rw [Algebra.linearMap_apply, Algebra.smul_def, Algebra.smul_def,
      mul_left_comm, mul_inv_cancel₀ ha', mul_one]⟩
  · rw [← LinearMap.ker_eq_bot, LinearMap.ker_codRestrict, eq_bot_iff]
    intro r hr
    induction r using Submodule.Quotient.induction_on with | _ r =>
    rw [mem_ker, divQuotient_mk, Submodule.Quotient.mk_eq_zero] at hr
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
    rw [LinearMap.codRestrict_apply, divQuotient_mk, Algebra.smul_def, hr, Algebra.smul_def,
      mul_comm, ← mul_assoc, inv_mul_cancel₀ ha', one_mul]

/-- For `a ≠ 0`, `Hom_O(O/a, K/O)` has length `v(a)`. -/
theorem length_linearMap_quotient_span_singleton {a : O} (ha : a ≠ 0) :
    Module.length O (O ⧸ Ideal.span {a} →ₗ[O] K ⧸ range (Algebra.linearMap O K)) =
      addVal O a := by
  rw [((Ideal.span {a}).quotientLinearMapEquivTorsionBySet _).length_eq,
    ← (quotientEquivTorsionBySet ha).length_eq, ← Ring.ord_eq_addVal]
  rfl

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

omit [IsFractionRing O K] [Fintype ι] in
/-- A submodule of finite colength in `O^ι` is spanned by the rows of a square matrix: it is free
(`O` is a principal ideal domain) and contains `c • O^ι` for some `c ≠ 0`, so it has rank
`card ι`. -/
theorem exists_matrix_span_range_row_eq [Finite ι] (R : Submodule O (ι → O))
    (hR : Module.length O ((ι → O) ⧸ R) ≠ ⊤) :
    ∃ M : Matrix ι ι O, Submodule.span O (Set.range M.row) = R := by
  have := Fintype.ofFinite ι
  obtain ⟨c, hc_ann, hc⟩ :=
    Submodule.annihilator_top_inter_nonZeroDivisors (isTorsion_of_length_ne_top hR)
  have hcR : ∀ v : ι → O, c • v ∈ R := fun v ↦ by
    have := Submodule.mem_annihilator.1 hc_ann (R.mkQ v) Submodule.mem_top
    rwa [← map_smul, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at this
  have hc0 : c ≠ 0 := nonZeroDivisors.ne_zero hc
  have hfin : Module.finrank O R = Fintype.card ι := by
    refine le_antisymm ((Submodule.finrank_le R).trans_eq (Module.finrank_fintype_fun_eq_card O)) ?_
    let g : (ι → O) →ₗ[O] R := (LinearMap.lsmul O _ c).codRestrict R hcR
    have hg : Function.Injective g := fun v w h ↦
      smul_right_injective _ hc0 (congrArg Subtype.val h)
    simpa using LinearMap.finrank_le_finrank_of_injective hg
  obtain ⟨k, b₀⟩ := Submodule.basisOfPid (Pi.basisFun O ι) R
  have hk : Fintype.card (Fin k) = Fintype.card ι := by
    rw [← hfin, Module.finrank_eq_card_basis b₀]
  let b : Module.Basis ι O R := b₀.reindex (Fintype.equivOfCardEq hk)
  refine ⟨fun i ↦ b i, ?_⟩
  change Submodule.span O (Set.range (R.subtype ∘ b)) = R
  rw [Set.range_comp, Submodule.span_image, b.span_eq, Submodule.map_top, Submodule.range_subtype]

end IsDiscreteValuationRing

namespace Matrix

open IsDiscreteValuationRing

variable {ι : Type*} {O K : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [Field K] [Algebra O K] [IsFractionRing O K] [Fintype ι] [DecidableEq ι]

/-- The rows of a singular square matrix over a discrete valuation ring span a submodule of
infinite colength: a nonzero vector `y` with `M y = 0` gives a functional vanishing on the rows,
and a coordinate on which `y` does not vanish embeds `O` in the quotient. -/
theorem length_quotient_span_range_eq_top {M : Matrix ι ι O} (hM : M.det = 0) :
    Module.length O ((ι → O) ⧸ Submodule.span O (Set.range M.row)) = ⊤ := by
  obtain ⟨y, hy, hMy⟩ := M.exists_mulVec_eq_zero_iff.2 hM
  obtain ⟨i, hi⟩ := Function.ne_iff.1 hy
  set S := Submodule.span O (Set.range M.row)
  have hS : ∀ v ∈ S, v ⬝ᵥ y = 0 := fun v hv ↦ by
    induction hv using Submodule.span_induction with
    | mem v hv =>
      obtain ⟨j, rfl⟩ := hv
      exact congrFun hMy j
    | zero => simp
    | add v w _ _ hv hw => rw [add_dotProduct, hv, hw, add_zero]
    | smul c v _ hv => rw [smul_dotProduct, hv, smul_zero]
  refine length_eq_top_of_injective (f := toSpanSingleton O _ (S.mkQ (Pi.single i 1)))
    fun r s h ↦ ?_
  rw [toSpanSingleton_apply, toSpanSingleton_apply, ← map_smul, ← map_smul,
    Submodule.mkQ_apply, Submodule.mkQ_apply, Submodule.Quotient.eq, ← sub_smul] at h
  have := hS _ h
  rw [smul_dotProduct, single_dotProduct, one_mul, smul_eq_mul, mul_eq_zero, sub_eq_zero] at this
  exact this.resolve_right (by simpa using hi)

/-- **Cokernel length and determinant for rows.** The rows of a square matrix `M` over a discrete
valuation ring span a submodule of `O^ι` of colength `v(det M)`, both sides infinite when
`det M = 0`. -/
theorem length_quotient_span_range_eq_addVal_det (M : Matrix ι ι O) :
    Module.length O ((ι → O) ⧸ Submodule.span O (Set.range M.row)) = addVal O M.det := by
  rcases eq_or_ne M.det 0 with hM | hM
  · rw [length_quotient_span_range_eq_top hM, hM, AddValuation.map_zero]
  have hrange : Submodule.span O (Set.range M.row) = LinearMap.range Mᵀ.mulVecLin := by
    rw [range_mulVecLin, col_transpose]
  rw [hrange, length_quotient_range_mulVecLin_eq_ord_det _ (by rwa [det_transpose]),
    det_transpose, Ring.ord_eq_addVal]

/-- **The kernel of a square matrix on `(K/O)^ι` has length `v(det M)`.** The kernel of `M`
acting on `(K/O)^ι`, the orthogonal of the rows of `M`, has length the valuation of `det M`, both
sides infinite when `det M = 0`. This is the linear algebra of
`SelmerLengthBoundsAndLocalLifting` §3.23. -/
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
