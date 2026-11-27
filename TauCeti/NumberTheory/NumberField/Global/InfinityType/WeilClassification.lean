/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.NumberField.Norm
public import TauCeti.NumberTheory.NumberField.ComplexConjugation.MaximalRealOrCMSubfield
public import TauCeti.NumberTheory.NumberField.Global.InfinityType.BaseChange

import Mathlib.NumberTheory.NumberField.Units.DirichletTheorem
import TauCeti.NumberTheory.NumberField.ComplexEmbedding.Extension
import TauCeti.NumberTheory.NumberField.TotallyPositive

/-!
# Weil's classification of algebraic infinity types on units

For a totally imaginary number field, the embedding monomial of an algebraic infinity type
is trivial on a finite-index subgroup of the integer units exactly when the type is a norm
pullback of parallel conjugate weight from the maximal CM subfield, or is constant when no
CM subfield exists. The logarithmic unit lattice gives the weight relation, and the Artin–Weil
factorization descends the exponents.

## References

* A. Weil, *On a certain type of characters of the idèle-class group of an algebraic
  number-field*, Tokyo–Nikko, 1955.
* G. Kings and J. Sprang, *Eisenstein–Kronecker classes, integrality of critical values of
  Hecke L-functions and p-adic interpolation*, §1.1.
-/

public noncomputable section

open NumberField NumberField.InfinitePlace NumberField.ComplexEmbedding
open scoped NumberField

namespace TauCeti.GlobalNumberFields.AlgebraicInfinityType

variable {K : Type*} [Field K] [NumberField K]

/-- The embedding monomial restricted to the units of the ring of integers. -/
def unitCharacter (n : AlgebraicInfinityType K) : (𝓞 K)ˣ →* ℂˣ :=
  n.embeddingCharacter.comp (Units.map (algebraMap (𝓞 K) K).toMonoidHom)

/-- The unit character is obtained by restricting the embedding character along the inclusion
of the integer units into the field units. -/
theorem unitCharacter_def (n : AlgebraicInfinityType K) :
    n.unitCharacter =
      n.embeddingCharacter.comp (Units.map (algebraMap (𝓞 K) K).toMonoidHom) :=
  (rfl)

/-- Evaluate the unit character as the product of the individual embedding powers. -/
@[simp]
theorem coe_unitCharacter_apply (n : AlgebraicInfinityType K) (u : (𝓞 K)ˣ) :
    (n.unitCharacter u : ℂ) = ∏ σ : K →+* ℂ, σ (u : K) ^ n σ := by
  simp [unitCharacter_def, coe_embeddingCharacter_apply]

section Weight

variable [IsTotallyComplex K]

private theorem log_norm_unitCharacter (n : AlgebraicInfinityType K) (u : (𝓞 K)ˣ) :
    Real.log ‖(n.unitCharacter u : ℂ)‖ =
      ∑ w : InfinitePlace K, ((n w.embedding + n (conjugate w.embedding) : ℤ) : ℝ) *
        Real.log (w (u : K)) := by
  classical
  rw [coe_unitCharacter_apply, norm_prod, Real.log_prod (fun σ _ ↦
    norm_ne_zero_iff.mpr (zpow_ne_zero _ ((map_ne_zero σ).mpr (NumberField.Units.coe_ne_zero u))))]
  simp_rw [norm_zpow, Real.log_zpow]
  rw [← Finset.sum_fiberwise Finset.univ InfinitePlace.mk]
  refine Finset.sum_congr rfl fun w _ ↦ ?_
  have hfiber : (Finset.univ.filter fun σ : K →+* ℂ ↦ InfinitePlace.mk σ = w) =
      {w.embedding, conjugate w.embedding} := by
    ext σ
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
      Finset.mem_singleton]
    have hmk := InfinitePlace.mk_eq_iff (φ := w.embedding) (ψ := σ)
    simpa only [mk_embedding, eq_comm] using hmk
  have hne : w.embedding ≠ conjugate w.embedding := fun h ↦
    IsTotallyComplex.complexEmbedding_not_isReal w.embedding
      (ComplexEmbedding.isReal_iff.mpr h.symm)
  rw [hfiber, Finset.sum_pair hne, ← InfinitePlace.apply, mk_embedding,
    ← InfinitePlace.apply, mk_conjugate_eq, mk_embedding, Int.cast_add, add_mul]

open NumberField.Units NumberField.Units.dirichletUnitTheorem in
private theorem exists_weight_of_log_sum_eq_zero (n : AlgebraicInfinityType K)
    (h : ∀ u : (𝓞 K)ˣ, Real.log ‖(n.unitCharacter u : ℂ)‖ = 0) :
    ∃ m : ℤ, ∀ σ : K →+* ℂ, n σ + n (conjugate σ) = m := by
  classical
  let a (w : InfinitePlace K) := n w.embedding + n (conjugate w.embedding)
  -- Work in the log coordinates with the distinguished place omitted.
  let f : logSpace K →ₗ[ℝ] ℝ := ∑ w, ((a w.val - a w₀ : ℤ) : ℝ) • LinearMap.proj w
  have hf (u : (𝓞 K)ˣ) : f (logEmbedding K (Additive.ofMul u)) = 0 := by
    have hw (w : InfinitePlace K) : mult w = 2 :=
      mult_isComplex ⟨w, IsTotallyComplex.isComplex w⟩
    have hu : ∑ w : InfinitePlace K, (a w : ℝ) * (mult w * Real.log (w (u : K))) = 0 := by
      simp_rw [hw, Nat.cast_ofNat, mul_left_comm _ (2 : ℝ), ← Finset.mul_sum]
      rw [← log_norm_unitCharacter, h u, mul_zero]
    rw [Fintype.sum_eq_add_sum_subtype_ne _ w₀] at hu
    simp only [f, LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.proj_apply,
      smul_eq_mul, Int.cast_sub, sub_mul, Finset.sum_sub_distrib, ← Finset.mul_sum]
    rw [sum_logEmbedding_component]
    simp only [logEmbedding_component]
    linarith
  have hfzero : f = 0 := by
    refine LinearMap.ext_on (unitLattice_span_eq_top K) ?_
    intro x hx
    have hx' : x ∈ unitLattice K := hx
    obtain ⟨u, -, rfl⟩ := Submodule.mem_map.mp hx'
    simpa using hf u.toMul
  refine ⟨a w₀, fun σ ↦ ?_⟩
  have ha (w : InfinitePlace K) : a w = a w₀ := by
    by_cases hw : w = w₀
    · simp [hw]
    · have hs := LinearMap.congr_fun hfzero (Pi.single ⟨w, hw⟩ 1)
      simpa [f, Pi.single_apply, Finset.sum_ite_eq', sub_eq_zero] using hs
  rcases embedding_mk_eq σ with hσ | hσ
  · simpa [a, hσ] using ha (InfinitePlace.mk σ)
  · simpa [a, hσ, add_comm] using ha (InfinitePlace.mk σ)

/-- If the unit character has finite-index kernel, its exponents have parallel conjugate sum. -/
theorem exists_weight_of_finiteIndex_ker_unitCharacter (n : AlgebraicInfinityType K)
    (h : n.unitCharacter.ker.FiniteIndex) :
    ∃ m : ℤ, ∀ σ : K →+* ℂ, n σ + n (conjugate σ) = m := by
  refine exists_weight_of_log_sum_eq_zero n fun u ↦ ?_
  have hu := n.unitCharacter.ker.pow_index_mem u
  rw [MonoidHom.mem_ker, map_pow] at hu
  have hn := congrArg (fun z : ℂˣ ↦ Real.log ‖(z : ℂ)‖) hu
  simp only [Units.val_pow_eq_pow_val, norm_pow, Real.log_pow, Units.val_one, norm_one,
    Real.log_one] at hn
  exact (mul_eq_zero.mp hn).resolve_left (Nat.cast_ne_zero.mpr h.index_ne_zero)

end Weight

private def complexEmbeddingsEquiv (ι : AlgebraicClosure ℚ →+* ℂ) :
    (K →+* AlgebraicClosure ℚ) ≃ (K →+* ℂ) := by
  let := ι.toAlgebra
  let : IsScalarTower ℚ (AlgebraicClosure ℚ) ℂ := .of_algebraMap_eq fun _ ↦ by simp
  exact (RingHom.equivRatAlgHom K _).trans <|
    (Algebra.IsAlgebraic.algHomEquivAlgHomOfSplits ℂ (AlgebraicClosure ℚ)
      (fun _ : K ↦ IsAlgClosed.splits _)).trans (RingHom.equivRatAlgHom K ℂ).symm

private theorem complexEmbeddingsEquiv_apply (ι : AlgebraicClosure ℚ →+* ℂ)
    (σ : K →+* AlgebraicClosure ℚ) :
    complexEmbeddingsEquiv ι σ = ι.comp σ :=
  (rfl)

private theorem card_mul_weight (n : AlgebraicInfinityType K) {w : ℤ}
    (h : ∀ σ, n σ + n (conjugate σ) = w) :
    (Fintype.card (K →+* ℂ) : ℤ) * w = 2 * ∑ σ, n σ := by
  calc
    _ = ∑ σ : K →+* ℂ, (n σ + n (conjugate σ)) := by simp [h]
    _ = _ := by
      rw [Finset.sum_add_distrib, ← Equiv.sum_comp (involutive_conjugate K).toPerm n, two_mul]
      rfl

private theorem exists_weight_for_complexConjugations [IsTotallyComplex K]
    (n : AlgebraicInfinityType K)
    (h : n.unitCharacter.ker.FiniteIndex) (ι₀ : AlgebraicClosure ℚ →+* ℂ) :
    ∃ w : ℤ, ∀ c ∈ TauCeti.NumberField.complexConjugations (AlgebraicClosure ℚ),
      ∀ σ : K →+* AlgebraicClosure ℚ,
        n (ι₀.comp ((c : _ →+* _).comp σ)) + n (ι₀.comp σ) = w := by
  obtain ⟨w₀, hw₀⟩ := n.exists_weight_of_finiteIndex_ker_unitCharacter h
  refine ⟨w₀, fun c hc σ ↦ ?_⟩
  obtain ⟨ι, hι⟩ := TauCeti.NumberField.mem_complexConjugations_iff.mp hc
  let e₀ : (K →+* AlgebraicClosure ℚ) ≃ (K →+* ℂ) := complexEmbeddingsEquiv ι₀
  let e : (K →+* AlgebraicClosure ℚ) ≃ (K →+* ℂ) := complexEmbeddingsEquiv ι
  let n' : AlgebraicInfinityType K := n ∘ e₀ ∘ e.symm
  -- Both evaluations are images of the same algebraic monomial.
  have hker : n.unitCharacter.ker ≤ n'.unitCharacter.ker := by
    intro u hu
    rw [MonoidHom.mem_ker] at hu ⊢
    let z : AlgebraicClosure ℚ := ∏ τ : K →+* AlgebraicClosure ℚ, τ (u : K) ^ n (e₀ τ)
    have heval (j : AlgebraicClosure ℚ →+* ℂ) :
        j z = ∏ τ : K →+* AlgebraicClosure ℚ, (j.comp τ) (u : K) ^ n (e₀ τ) := by
      simp [z, map_prod]
    have hz : z = 1 := ι₀.injective <| calc
      ι₀ z = (n.unitCharacter u : ℂ) := by
        rw [heval, coe_unitCharacter_apply]
        exact Fintype.prod_equiv e₀ _ _ fun _ ↦ rfl
      _ = ι₀ 1 := by simp [hu]
    apply Units.ext
    rw [coe_unitCharacter_apply, Units.val_one, ← map_one ι, ← hz, heval]
    exact (Fintype.prod_equiv e _ _ fun τ ↦ by
      simp only [n', Function.comp_apply, Equiv.symm_apply_apply]
      rfl).symm
  let := h
  obtain ⟨w, hw⟩ := n'.exists_weight_of_finiteIndex_ker_unitCharacter
    (Subgroup.finiteIndex_of_le hker)
  have hsum : ∑ τ, n' τ = ∑ τ, n τ :=
    Equiv.sum_comp (e.symm.trans e₀) n
  -- Permuting embeddings leaves the sum of the exponents unchanged.
  have hweight : w = w₀ := by
    have hcard : (Fintype.card (K →+* ℂ) : ℤ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
    exact mul_left_cancel₀ hcard ((card_mul_weight n' hw).trans
      (hsum ▸ (card_mul_weight n hw₀).symm))
  have hcomp : conjugate (e σ) = e ((c : _ →+* _).comp σ) := by
    exact RingHom.ext fun x ↦ (hι.eq (σ x)).symm
  have hwσ := hw (e σ)
  rw [hcomp, hweight] at hwσ
  simpa [n', e₀, complexEmbeddingsEquiv_apply, add_comm] using hwσ

open TauCeti.NumberField in
/-- A finite-index kernel forces an algebraic infinity type to descend to the maximal CM
subfield, with parallel conjugate sum. In the absence of a CM subfield the type is constant. -/
private theorem exists_baseChange_or_constant_of_finiteIndex_ker_unitCharacter [IsTotallyComplex K]
    (n : AlgebraicInfinityType K) (h : n.unitCharacter.ker.FiniteIndex) :
    (IsCMField (maximalRealOrCMSubfield K) ∧
      ∃ n₀ : AlgebraicInfinityType (maximalRealOrCMSubfield K),
        n₀.baseChange K = n ∧ ∃ w : ℤ, ∀ τ, n₀ τ + n₀ (conjugate τ) = w) ∨
    (¬ IsCMField (maximalRealOrCMSubfield K) ∧ ∃ a : ℤ, ∀ σ, n σ = a) := by
  let ι : AlgebraicClosure ℚ →+* ℂ := (IsAlgClosed.lift (R := ℚ)).toRingHom
  let e : (K →+* AlgebraicClosure ℚ) ≃ (K →+* ℂ) := complexEmbeddingsEquiv ι
  obtain ⟨w, hw⟩ := exists_weight_for_complexConjugations n h ι
  let E := maximalRealOrCMSubfield K
  by_cases hE : IsCMField E
  · refine Or.inl ⟨hE, ?_⟩
    let n₀ : AlgebraicInfinityType E := fun τ ↦ n (ComplexEmbedding.lift K τ)
    have hdesc (σ : K →+* ℂ) : n₀ (σ.comp (algebraMap E K)) = n σ := by
      let τ := ComplexEmbedding.lift K (σ.comp (algebraMap E K))
      have hτ : τ.comp (algebraMap E K) = σ.comp (algebraMap E K) :=
        ComplexEmbedding.lift_comp_algebraMap _ _
      have hval := apply_eq_apply_of_eqOn_maximalRealOrCMSubfield
        (m := fun ρ : K →+* AlgebraicClosure ℚ ↦ n (e ρ)) hw
        (τ := e.symm τ) (τ' := e.symm σ) (fun x hx ↦ by
          apply ι.injective
          have hx' : algebraMap E K (⟨x, hx⟩ : E) = x := rfl
          calc
            ι (e.symm τ x) = τ x := DFunLike.congr_fun (e.apply_symm_apply τ) x
            _ = σ x := by simpa only [RingHom.comp_apply, hx'] using
              RingHom.congr_fun hτ (⟨x, hx⟩ : E)
            _ = ι (e.symm σ x) := DFunLike.congr_fun (e.apply_symm_apply σ).symm x)
      simpa only [Equiv.apply_symm_apply] using hval
    obtain ⟨m, hm⟩ := n.exists_weight_of_finiteIndex_ker_unitCharacter h
    refine ⟨n₀, ?_, m, fun τ ↦ ?_⟩
    · exact funext fun σ ↦ (baseChange_apply n₀ σ).trans (hdesc σ)
    · let σ := ComplexEmbedding.lift K τ
      have hσ : σ.comp (algebraMap E K) = τ := ComplexEmbedding.lift_comp_algebraMap K τ
      have hσbar : (conjugate σ).comp (algebraMap E K) = conjugate τ := by
        rw [conjugate_comp, hσ]
      have hmσ := hm σ
      rwa [← hdesc σ, ← hdesc (conjugate σ), hσ, hσbar] at hmσ
  · refine Or.inr ⟨hE, ?_⟩
    obtain ⟨σ₀⟩ := (inferInstance : Nonempty (K →+* ℂ))
    refine ⟨n σ₀, fun σ ↦ ?_⟩
    have hnone (F : Subfield K) (hF : IsCMField F) : False :=
      hE (isCMField_maximalRealOrCMSubfield_iff_exists.mpr ⟨F, hF⟩)
    have hhalf (ρ : K →+* ℂ) : 2 • n ρ = w := by
      simpa only [Equiv.apply_symm_apply] using two_nsmul_eq_of_forall_not_isCMField hnone
        (m := fun ρ : K →+* AlgebraicClosure ℚ ↦ n (e ρ)) hw (e.symm ρ)
    have h₁ := hhalf σ
    have h₂ := hhalf σ₀
    simp only [two_nsmul] at h₁ h₂
    omega

section Norm

variable {F : Type*} [Field F] [NumberField F] [Algebra F K]

/-- The embedding monomial of a norm-pulled infinity type at an integer unit is the original
monomial at the relative norm of the unit. -/
@[simp]
theorem unitCharacter_baseChange (n : AlgebraicInfinityType F) (u : (𝓞 K)ˣ) :
    (n.baseChange K).unitCharacter u =
      n.unitCharacter (Units.map (NumberField.RingOfIntegers.norm F) u) := by
  classical
  apply Units.ext
  simp only [coe_unitCharacter_apply, baseChange_apply, Units.coe_map]
  have hcoe : algebraMap (𝓞 F) F (NumberField.RingOfIntegers.norm F (u : 𝓞 K)) =
      Algebra.norm F (u : K) := NumberField.RingOfIntegers.coe_norm F _
  rw [hcoe]
  rw [← Finset.prod_fiberwise Finset.univ (fun σ : K →+* ℂ ↦ σ.comp (algebraMap F K))]
  refine Finset.prod_congr rfl fun τ _ ↦ ?_
  have : FiniteDimensional F K := Module.Finite.of_restrictScalars_finite ℚ F K
  have : IsAlgClosed (Codomain τ) := Complex.isAlgClosed
  have hnorm : (∏ σ : ComplexEmbedding.Extension K τ, σ.val (u : K)) =
      τ (Algebra.norm F (u : K)) := by
    rw [← Fintype.prod_equiv (ComplexEmbedding.Extension.equivAlgHom K τ).symm
        (fun σ ↦ Codomain.equiv τ (σ (u : K))) _
        (fun σ ↦ (ComplexEmbedding.Extension.equivAlgHom_symm_apply σ _).symm),
      ← map_prod, ← Algebra.norm_eq_prod_embeddings, Codomain.equiv_algebraMap]
  calc
    _ = (∏ σ : K →+* ℂ with σ.comp (algebraMap F K) = τ, σ (u : K)) ^ n τ := by
      rw [← Finset.prod_zpow]
      exact Finset.prod_congr rfl fun σ hσ ↦ by rw [(Finset.mem_filter.mp hσ).2]
    _ = _ := by
      rw [← hnorm]
      congr 1
      refine Finset.prod_subtype _ (fun σ ↦ ?_) _
      simp [ComplexEmbedding.liesOver_iff]

end Norm

/-- Constant algebraic infinity types are trivial on the integer units of a totally imaginary
field. -/
theorem unitCharacter_eq_one_of_constant [IsTotallyComplex K] (n : AlgebraicInfinityType K)
    {a : ℤ} (hn : ∀ σ, n σ = a) : n.unitCharacter = 1 := by
  ext u
  have hpos := norm_pos_of_isTotallyPositive (NumberField.Units.coe_ne_zero u) (by simp)
  have hnorm := (abs_of_pos hpos).symm.trans (NumberField.Units.norm K u)
  simp only [coe_unitCharacter_apply, hn, MonoidHom.one_apply, Units.val_one]
  have hprod : (∏ σ : K →+* ℂ, σ (u : K)) = 1 := calc
    _ = ∏ σ : K →ₐ[ℚ] ℂ, σ (u : K) :=
      Fintype.prod_equiv (RingHom.equivRatAlgHom K ℂ) _ _ (fun _ ↦ rfl)
    _ = 1 := by rw [← Algebra.norm_eq_prod_embeddings, hnorm, map_one]
  rw [Finset.prod_zpow, hprod, one_zpow]

private theorem unitCharacter_mul_unitsComplexConj [IsCMField K] (n : AlgebraicInfinityType K)
    {w : ℤ} (hn : ∀ σ, n σ + n (conjugate σ) = w) (u : (𝓞 K)ˣ) :
    n.unitCharacter (u * IsCMField.unitsComplexConj K u) = 1 := by
  let m : AlgebraicInfinityType K := fun _ ↦ w
  have hm : m.unitCharacter = 1 := m.unitCharacter_eq_one_of_constant fun _ ↦ rfl
  rw [← MonoidHom.one_apply (M := (𝓞 K)ˣ) (N := ℂˣ) u, ← hm]
  apply Units.ext
  rw [map_mul, Units.val_mul, coe_unitCharacter_apply, coe_unitCharacter_apply,
    coe_unitCharacter_apply]
  have hconj (σ : K →+* ℂ) :
      σ (IsCMField.unitsComplexConj K u : K) = conjugate σ (u : K) := by simp
  simp only [hconj]
  have hprod : (∏ σ : K →+* ℂ, conjugate σ (u : K) ^ n σ) =
      ∏ σ : K →+* ℂ, σ (u : K) ^ n (conjugate σ) :=
    Fintype.prod_equiv (involutive_conjugate K).toPerm _ _ fun σ ↦ by simp
  rw [hprod, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun σ _ ↦ ?_
  rw [← zpow_add₀ ((map_ne_zero σ).mpr (NumberField.Units.coe_ne_zero u)), hn]

/-- An algebraic infinity type with parallel conjugate sum on a CM field is trivial on a
finite-index subgroup of its integer units. -/
theorem finiteIndex_ker_unitCharacter_of_isCMField [IsCMField K] (n : AlgebraicInfinityType K)
    {w : ℤ} (hn : ∀ σ, n σ + n (conjugate σ) = w) :
    n.unitCharacter.ker.FiniteIndex := by
  let c := IsCMField.unitsComplexConj K
  let r := NumberField.Units.torsionOrder K
  have hpow (u : (𝓞 K)ˣ) : c (u ^ r) = u ^ r := by
    have ht := NumberField.Units.pow_torsionOrder_eq_one K
      (IsCMField.unitsMulComplexConjInv K u).property
    rwa [IsCMField.unitsMulComplexConjInv_apply, mul_pow, inv_pow, mul_inv_eq_one, ← map_pow,
      eq_comm] at ht
  have hroots : n.unitCharacter.range ≤ rootsOfUnity (r * 2) ℂ := by
    rintro _ ⟨u, rfl⟩
    rw [mem_rootsOfUnity, pow_mul, ← map_pow, ← map_pow, pow_two]
    calc
      _ = n.unitCharacter (u ^ r * c (u ^ r)) := by rw [hpow u]
      _ = 1 := unitCharacter_mul_unitsComplexConj n hn (u ^ r)
  have : NeZero (r * 2) := ⟨mul_ne_zero (NumberField.Units.torsionOrder_ne_zero K) two_ne_zero⟩
  have : Finite n.unitCharacter.range :=
    Finite.of_injective (Subgroup.inclusion hroots) (Subgroup.inclusion_injective hroots)
  exact Subgroup.finiteIndex_ker _

open TauCeti.NumberField in
/-- **Weil's classification.** For a totally imaginary field, the algebraic infinity types
trivial on a finite-index subgroup of the integer units are exactly the norm pullbacks of
parallel conjugate weight from its maximal CM subfield, or the constant types if there is no
CM subfield. -/
theorem finiteIndex_ker_unitCharacter_iff [IsTotallyComplex K] (n : AlgebraicInfinityType K) :
    n.unitCharacter.ker.FiniteIndex ↔
      (IsCMField (maximalRealOrCMSubfield K) ∧
        ∃ n₀ : AlgebraicInfinityType (maximalRealOrCMSubfield K),
          n₀.baseChange K = n ∧ ∃ w : ℤ, ∀ τ, n₀ τ + n₀ (conjugate τ) = w) ∨
      (¬ IsCMField (maximalRealOrCMSubfield K) ∧ ∃ a : ℤ, ∀ σ, n σ = a) := by
  refine ⟨n.exists_baseChange_or_constant_of_finiteIndex_ker_unitCharacter, ?_⟩
  rintro (⟨hE, n₀, rfl, w, hw⟩ | ⟨_, a, ha⟩)
  · have : n₀.unitCharacter.ker.FiniteIndex := n₀.finiteIndex_ker_unitCharacter_of_isCMField hw
    let norm := Units.map (NumberField.RingOfIntegers.norm (L := K) (maximalRealOrCMSubfield K))
    have hker : (n₀.baseChange K).unitCharacter.ker = n₀.unitCharacter.ker.comap norm := by
      ext u
      simp [norm]
    refine ⟨?_⟩
    rw [hker, Subgroup.index_comap]
    exact mt Subgroup.index_eq_zero_of_relIndex_eq_zero Subgroup.index_ne_zero
  · rw [n.unitCharacter_eq_one_of_constant ha, MonoidHom.ker_one]
    infer_instance

end TauCeti.GlobalNumberFields.AlgebraicInfinityType
