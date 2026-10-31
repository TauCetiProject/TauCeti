/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.Eigenspace.DiagonalBasis
public import TauCeti.QuantumGroups.UqSl2.LocallyFinite
public import TauCeti.QuantumGroups.UqSl2.TensorProduct
public import TauCeti.QuantumGroups.UqSl2.TypeOne

/-!
# Formal characters of `U_q(sl₂)`-modules

The **formal character**, or weight character, of a finite-dimensional `UqSl2 q`-module `V` is
the element

`ch V = ∑_μ dim V_μ · [μ]`

of the integral monoid algebra `ℤ[ℂ]` of the multiplicative monoid of `ℂ`, where `V_μ` is the
eigenspace of `K` for the eigenvalue `μ`. The weights are recorded as the actual eigenvalues of
`K`, with no choice of a logarithm of `q`, so that the definition makes sense for every module
and every parameter. Since `K` is invertible the coefficient at `0` always vanishes.

The character is an isomorphism invariant, adds over finite products, and is multiplicative on
weight modules for the coproduct `ΔK = K ⊗ K`: if `K` acts diagonalizably on `V` and on `W`, then
`ch (V ⊗ W) = ch V · ch W`. The signed ladder module `L_m^ε` has character
`∑_(j=0)^m [ε q^(m-2j)]`.

At a generic parameter `q` (nonzero and not a root of unity), every finite-dimensional module is
a finite direct sum of signed ladder modules, so `K` acts diagonalizably and the character is
multiplicative on all finite-dimensional modules. Moreover the character then determines the
module. The multiplicity `dim Hom_U(L_m^ε, V)` of `L_m^ε` in `V` is the difference of the
coefficients of `ch V` at `ε q^m` and at `ε q^(m+2)`: a summand `L_n^δ` contributes to the
coefficient at `ε q^m` exactly when `δ = ε`, `m ≤ n` and `n - m` is even, and the difference
retains only `n = m`. Hence two finite-dimensional modules are isomorphic exactly when their
characters agree.

The definition and the weight-basis computations parallel `TauCeti.Comodule.formalCharacter`, the
formal character of a comodule over a monoid algebra, in
`TauCeti.Algebra.Coalgebra.Comodule.MonoidAlgebra.Character`.

## Main definitions

* `TauCeti.UqSl2.formalCharacter`: the formal character `∑_μ dim V_μ · [μ] ∈ ℤ[ℂ]`.

## Main results

* `Module.Basis.uqSl2FormalCharacter_eq_sum`: the character is the sum of the weights of a basis
  of weight vectors.
* `TauCeti.UqSl2.formalCharacter_congr` and `TauCeti.UqSl2.formalCharacter_pi`: invariance under
  isomorphism and additivity over finite products.
* `TauCeti.UqSl2.formalCharacter_tensor_of_isWeightModule` and
  `TauCeti.UqSl2.formalCharacter_tensor`: the character of a tensor product of weight modules,
  in particular of any two finite-dimensional modules at a generic parameter, is the product of
  the characters.
* `TauCeti.UqSl2.formalCharacter_ladderModule`: `ch L_m^ε = ∑_(j=0)^m [ε q^(m-2j)]`.
* `TauCeti.UqSl2.finrank_linearMap_ladderModule_eq_formalCharacter_coeff_sub`: at a generic
  parameter, the multiplicity of `L_m^ε` is read off the character.
* `TauCeti.UqSl2.nonempty_linearEquiv_iff_formalCharacter_eq`: at a generic parameter,
  finite-dimensional modules are isomorphic exactly when their characters agree.

## References

* A. Virelizier, *Quantum groups*, Sections 2.3--2.4, for the rank-one conventions.
* J. C. Jantzen, *Lectures on Quantum Groups*, Chapter 2, for the finite-dimensional
  representations of `U_q(sl₂)`. The multiplicity formula is the usual highest-weight count,
  developed directly here.
-/

public section

open Module

namespace TauCeti.UqSl2

variable {q : ℂ} {V W : Type*} [AddCommGroup V] [Module ℂ V] [Module (UqSl2 q) V]
  [IsScalarTower ℂ (UqSl2 q) V] [AddCommGroup W] [Module ℂ W] [Module (UqSl2 q) W]
  [IsScalarTower ℂ (UqSl2 q) W]

/-! ### The formal character -/

section Character

variable [FiniteDimensional ℂ V] [FiniteDimensional ℂ W]

variable (q V) in
/-- **The formal character** of a finite-dimensional `UqSl2 q`-module: the element of the
integral monoid algebra `ℤ[ℂ]` of the multiplicative monoid of `ℂ` whose coefficient at `μ` is
the dimension of the `μ`-weight space, the eigenspace of `K` for the eigenvalue `μ`. -/
noncomputable def formalCharacter : MonoidAlgebra ℤ ℂ :=
  .ofCoeff (Finsupp.ofSupportFinite (fun μ ↦ (finrank ℂ (weightSpace q V μ) : ℤ))
    ((finite_setOf_weightSpace_ne_bot q V).subset fun μ hμ hbot ↦ hμ (by simp [hbot])))

/-- The coefficient of the character at `μ` is the dimension of the `μ`-weight space. -/
@[simp]
theorem formalCharacter_coeff (μ : ℂ) :
    (formalCharacter q V).coeff μ = (finrank ℂ (weightSpace q V μ) : ℤ) := by
  rw [formalCharacter, MonoidAlgebra.coeff_ofCoeff, Finsupp.ofSupportFinite_coe]

/-- **The character as a sum over a weight basis.** Each vector of a basis of weight vectors
contributes its weight. -/
theorem _root_.Module.Basis.uqSl2FormalCharacter_eq_sum {ι : Type*} [Fintype ι] (b : Basis ι ℂ V)
    (wt : ι → ℂ) (hb : ∀ i, b i ∈ weightSpace q V (wt i)) :
    formalCharacter q V = ∑ i, MonoidAlgebra.single (wt i) 1 := by
  classical
  refine MonoidAlgebra.coeff_injective (Finsupp.ext fun μ ↦ ?_)
  have hf (i : ι) : Algebra.lsmul ℂ ℂ V (k q) (b i) = wt i • b i := mem_weightSpace_iff.mp (hb i)
  rw [formalCharacter_coeff, weightSpace_def, b.finrank_eigenspace_eq_card hf μ,
    MonoidAlgebra.coeff_sum, Finsupp.finsetSum_apply, Nat.card_eq_fintype_card,
    Fintype.card_subtype]
  simp [MonoidAlgebra.coeff_single, Finsupp.single_apply]

/-- Isomorphic modules have equal characters. -/
theorem formalCharacter_congr (e : V ≃ₗ[UqSl2 q] W) :
    formalCharacter q V = formalCharacter q W := by
  refine MonoidAlgebra.coeff_injective (Finsupp.ext fun μ ↦ ?_)
  have h : (weightSpace q V μ).map (e.restrictScalars ℂ : V →ₗ[ℂ] W) = weightSpace q W μ := by
    refine le_antisymm (map_weightSpace_le e.toLinearMap μ) fun w hw ↦ ⟨e.symm w, ?_, by simp⟩
    exact map_weightSpace_le e.symm.toLinearMap μ ⟨w, hw, rfl⟩
  rw [formalCharacter_coeff, formalCharacter_coeff, ← h, LinearEquiv.finrank_map_eq]

/-- **The character adds over finite products.** -/
theorem formalCharacter_pi {ι : Type*} [Fintype ι] {N : ι → Type*} [∀ i, AddCommGroup (N i)]
    [∀ i, Module ℂ (N i)] [∀ i, Module (UqSl2 q) (N i)] [∀ i, IsScalarTower ℂ (UqSl2 q) (N i)]
    [∀ i, FiniteDimensional ℂ (N i)] :
    formalCharacter q (∀ i, N i) = ∑ i, formalCharacter q (N i) := by
  refine MonoidAlgebra.coeff_injective (Finsupp.ext fun μ ↦ ?_)
  rw [formalCharacter_coeff, MonoidAlgebra.coeff_sum, Finsupp.finsetSum_apply]
  simp only [formalCharacter_coeff]
  -- The weight space of the product is the product of the weight spaces.
  let e : weightSpace q (∀ i, N i) μ ≃ₗ[ℂ] ∀ i, weightSpace q (N i) μ :=
    { toFun x i := ⟨x.1 i, mem_weightSpace_iff.mpr (congrFun (mem_weightSpace_iff.mp x.2) i)⟩
      invFun y := ⟨fun i ↦ (y i).1, mem_weightSpace_iff.mpr
        (funext fun i ↦ mem_weightSpace_iff.mp (y i).2)⟩
      map_add' _ _ := rfl
      map_smul' _ _ := rfl
      left_inv _ := rfl
      right_inv _ := rfl }
  rw [e.finrank_eq, Module.finrank_pi_fintype, Nat.cast_sum]

/-- **The character is multiplicative on weight modules.** If `K` acts diagonalizably on `V`
and on `W`, the character of `V ⊗ W`, with `UqSl2 q` acting through the coproduct, is the
product of the characters. -/
theorem formalCharacter_tensor_of_isWeightModule [Fact (q ≠ 0)] {S T : Set ℂ}
    (hV : IsWeightModule q V S) (hW : IsWeightModule q W T) :
    formalCharacter q (BialgebraModule.Tensor ℂ (UqSl2 q) V W) =
      formalCharacter q V * formalCharacter q W := by
  obtain ⟨b, wt, hb⟩ := hV.exists_basis_mem_weightSpace
  obtain ⟨c, wt', hc⟩ := hW.exists_basis_mem_weightSpace
  -- The pure tensors of the two weight bases form a weight basis of the tensor product.
  let bc := (b.tensorProduct c).map (BialgebraModule.tensorEquiv ℂ (UqSl2 q) V W).symm
  have hbc (p : Fin (finrank ℂ V) × Fin (finrank ℂ W)) :
      bc p ∈ weightSpace q _ (wt p.1 * wt' p.2) := by
    obtain ⟨i, j⟩ := p
    simp only [bc, mem_weightSpace_iff, Basis.map_apply, Basis.tensorProduct_apply,
      BialgebraModule.tensorEquiv_symm_tmul, k_smul_tmul, mem_weightSpace_iff.mp (hb i),
      mem_weightSpace_iff.mp (hc j), BialgebraModule.tmul_smul, ← BialgebraModule.smul_tmul']
    rw [mul_comm, mul_smul]
  rw [bc.uqSl2FormalCharacter_eq_sum _ hbc, b.uqSl2FormalCharacter_eq_sum wt hb,
    c.uqSl2FormalCharacter_eq_sum wt' hc, Finset.sum_mul_sum, ← Finset.univ_product_univ,
    Finset.sum_product]
  simp

/-- **The character is multiplicative.** At a generic parameter, the character of the tensor
product of two finite-dimensional modules, with `UqSl2 q` acting through the coproduct, is the
product of their characters. -/
theorem formalCharacter_tensor [Fact (q ≠ 0)] (hq : IsGenericQuantumParameter q) :
    formalCharacter q (BialgebraModule.Tensor ℂ (UqSl2 q) V W) =
      formalCharacter q V * formalCharacter q W :=
  -- Finite-dimensional modules are locally finite, hence of signed type 1.
  formalCharacter_tensor_of_isWeightModule
    ((isSignedTypeOne_and_forall_exists_pow_smul_eq_zero_iff_isLocallyFiniteModule hq).mpr
      inferInstance).1
    ((isSignedTypeOne_and_forall_exists_pow_smul_eq_zero_iff_isLocallyFiniteModule hq).mpr
      inferInstance).1

end Character

/-! ### Characters of the signed ladder modules -/

section LadderModule

variable [Fact (q ≠ 0)]

/-- **The character of a signed ladder module**: `ch L_m^ε = ∑_(j=0)^m [ε q^(m-2j)]`. -/
theorem formalCharacter_ladderModule (m : ℕ) (ε : ℤˣ) :
    formalCharacter q (LadderModule q m ε) =
      ∑ j ∈ Finset.range (m + 1), MonoidAlgebra.single ((ε : ℂ) * q ^ ((m : ℤ) - 2 * j)) 1 := by
  rw [(LadderModule.basis q m ε).uqSl2FormalCharacter_eq_sum
    (fun j ↦ (ε : ℂ) * q ^ ((m : ℤ) - 2 * j)) fun j ↦ by
      rw [← LadderModule.vec_coe, mem_weightSpace_iff, LadderModule.k_smul_vec]]
  exact Fin.sum_univ_eq_sum_range (fun j ↦ MonoidAlgebra.single ((ε : ℂ) * q ^ ((m : ℤ) - 2 * j)) 1)
    (m + 1)

/-- At a generic parameter, the coefficient of `ch L_n^δ` at a signed power `ε q^c` counts the
indices `j ≤ n` with `δ = ε` and `n - 2j = c`. -/
private theorem formalCharacter_ladderModule_coeff_units_mul_zpow (hq : IsGenericQuantumParameter q)
    (n : ℕ) (δ ε : ℤˣ) (c : ℤ) :
    (formalCharacter q (LadderModule q n δ)).coeff ((ε : ℂ) * q ^ c) =
      ∑ j ∈ Finset.range (n + 1), if δ = ε ∧ (n : ℤ) - 2 * j = c then 1 else 0 := by
  classical
  rw [formalCharacter_ladderModule, MonoidAlgebra.coeff_sum, Finsupp.finsetSum_apply]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  rw [MonoidAlgebra.coeff_single, Finsupp.single_apply]
  exact if_congr (hq.units_mul_zpow_inj (K := ℂ)) rfl rfl

/-- At a generic parameter, the coefficients of `ch L_n^δ` at `ε q^m` and `ε q^(m+2)` differ
by one when `L_n^δ = L_m^ε`, and agree otherwise. -/
private theorem formalCharacter_ladderModule_coeff_sub (hq : IsGenericQuantumParameter q) (n m : ℕ)
    (δ ε : ℤˣ) :
    (formalCharacter q (LadderModule q n δ)).coeff (ε * q ^ m) -
        (formalCharacter q (LadderModule q n δ)).coeff (ε * q ^ (m + 2)) =
      if m = n ∧ ε = δ then 1 else 0 := by
  rw [← zpow_natCast, ← zpow_natCast, formalCharacter_ladderModule_coeff_units_mul_zpow hq,
    formalCharacter_ladderModule_coeff_units_mul_zpow hq]
  by_cases hδ : δ = ε
  · -- The difference telescopes: `v_j` has weight `ε q^(m+2)` exactly when `v_(j+1)` has
    -- weight `ε q^m`, so only `v_0` and the vector `v_(n+1) = 0` survive.
    subst hδ
    simp only [true_and, and_true]
    rw [← Finset.sum_sub_distrib]
    convert Finset.sum_range_sub' (fun j : ℕ ↦ if (n : ℤ) - 2 * j = m then (1 : ℤ) else 0)
      (n + 1) using 1
    · refine Finset.sum_congr rfl fun j _ ↦ ?_
      congr 1
      exact if_congr (by push_cast; omega) rfl rfl
    · have h0 : (n : ℤ) - 2 * ((0 : ℕ) : ℤ) = m ↔ m = n := by push_cast; omega
      have h1 : ¬(n : ℤ) - 2 * ((n + 1 : ℕ) : ℤ) = m := by push_cast; omega
      simp only [h0, h1, ite_false, sub_zero]
  · simp [hδ, Ne.symm hδ]

/-! ### The character determines the module -/

variable [FiniteDimensional ℂ V] [FiniteDimensional ℂ W]

/-- **Multiplicities from the character.** At a generic parameter, the multiplicity
`dim Hom_U(L_m^ε, V)` of the signed ladder module `L_m^ε` in a finite-dimensional module `V` is
the coefficient of the character of `V` at `ε q^m` minus its coefficient at `ε q^(m+2)`. -/
theorem finrank_linearMap_ladderModule_eq_formalCharacter_coeff_sub
    (hq : IsGenericQuantumParameter q) (m : ℕ) (ε : ℤˣ) :
    (finrank ℂ (LadderModule q m ε →ₗ[UqSl2 q] V) : ℤ) =
      (formalCharacter q V).coeff (ε * q ^ m) - (formalCharacter q V).coeff (ε * q ^ (m + 2)) := by
  classical
  have := isSemisimpleModule_of_finiteDimensional hq (V := V)
  have : Module.Finite (UqSl2 q) V := Module.Finite.of_restrictScalars_finite ℂ _ _
  obtain ⟨n, S, e, hS⟩ := IsSemisimpleModule.exists_linearEquiv_fin_dfinsupp (UqSl2 q) V
  -- Each simple summand is finite-dimensional, hence isomorphic to a signed ladder module.
  have h (i : Fin n) : ∃ (m : ℕ) (ε : ℤˣ), Nonempty (LadderModule q m ε ≃ₗ[UqSl2 q] S i) := by
    have := hS i
    have := IsLocallyFiniteModule.finite_of_isSimpleModule (k := ℂ) (S i)
    exact exists_linearEquiv_ladderModule hq
  choose m' ε' e' using h
  have := LadderModule.isSimpleModule hq (q := q) (m := m) (ε := ε)
  have (i : Fin n) := LadderModule.isSimpleModule hq (q := q) (m := m' i) (ε := ε' i)
  let e'' : V ≃ₗ[UqSl2 q] ∀ i, LadderModule q (m' i) (ε' i) :=
    e.trans (DFinsupp.linearEquivFunOnFintype.trans
      (LinearEquiv.piCongrRight fun i ↦ (e' i).some.symm))
  rw [finrank_linearMap_eq_natCard_of_linearEquiv_pi (k := ℂ) e'', formalCharacter_congr e'',
    formalCharacter_pi, MonoidAlgebra.coeff_sum, Finsupp.finsetSum_apply, Finsupp.finsetSum_apply,
    ← Finset.sum_sub_distrib]
  simp only [formalCharacter_ladderModule_coeff_sub hq, LadderModule.nonempty_linearEquiv_iff hq,
    Nat.card_eq_fintype_card, Fintype.card_subtype, Finset.sum_boole]

/-- **The character determines the module.** At a generic parameter, two finite-dimensional
modules are isomorphic exactly when they have the same character. -/
theorem nonempty_linearEquiv_iff_formalCharacter_eq (hq : IsGenericQuantumParameter q) :
    Nonempty (V ≃ₗ[UqSl2 q] W) ↔ formalCharacter q V = formalCharacter q W := by
  refine ⟨fun ⟨e⟩ ↦ formalCharacter_congr e, fun h ↦ ?_⟩
  -- Equal characters give multiplicity spaces of equal dimensions, and the evaluation
  -- isomorphisms assemble linear isomorphisms between them into a module isomorphism.
  have hdim (p : ℕ × ℤˣ) : finrank ℂ (LadderModule q p.1 p.2 →ₗ[UqSl2 q] V) =
      finrank ℂ (LadderModule q p.1 p.2 →ₗ[UqSl2 q] W) := by
    have hV := finrank_linearMap_ladderModule_eq_formalCharacter_coeff_sub hq (V := V) p.1 p.2
    rw [h, ← finrank_linearMap_ladderModule_eq_formalCharacter_coeff_sub hq] at hV
    exact_mod_cast hV
  have (p : ℕ × ℤˣ) := LadderModule.isSimpleModule hq (q := q) (m := p.1) (ε := p.2)
  -- A space of `UqSl2 q`-linear maps embeds in the finite-dimensional space of linear maps.
  have (p : ℕ × ℤˣ) : FiniteDimensional ℂ (LadderModule q p.1 p.2 →ₗ[UqSl2 q] V) :=
    .of_injective (LinearMap.restrictScalarsₗ (R := ℂ) (S := UqSl2 q) (R₁ := ℂ)
      (M := LadderModule q p.1 p.2) (N := V)) (LinearMap.restrictScalars_injective ℂ)
  have (p : ℕ × ℤˣ) : FiniteDimensional ℂ (LadderModule q p.1 p.2 →ₗ[UqSl2 q] W) :=
    .of_injective (LinearMap.restrictScalarsₗ (R := ℂ) (S := UqSl2 q) (R₁ := ℂ)
      (M := LadderModule q p.1 p.2) (N := W)) (LinearMap.restrictScalars_injective ℂ)
  exact ⟨(ladderModuleTensorHomEquiv hq).symm.trans ((DFinsupp.mapRange.linearEquiv fun p ↦
    TensorProduct.AlgebraTensorModule.congr (LinearEquiv.refl _ _)
      (LinearEquiv.ofFinrankEq _ _ (hdim p))).trans (ladderModuleTensorHomEquiv hq))⟩

end LadderModule

end TauCeti.UqSl2
