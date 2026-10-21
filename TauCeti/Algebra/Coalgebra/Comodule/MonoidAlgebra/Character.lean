/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Dual.Basis
public import Mathlib.LinearAlgebra.TensorProduct.Basis
public import Mathlib.RingTheory.HopfAlgebra.MonoidAlgebra
public import TauCeti.Algebra.Coalgebra.Comodule.Dual
public import TauCeti.Algebra.Coalgebra.Comodule.MonoidAlgebra.Basic
public import TauCeti.Algebra.Coalgebra.Comodule.Product
public import TauCeti.Algebra.Coalgebra.Comodule.TensorProduct

/-!
# Formal characters of comodules over a monoid algebra

Let `V` be a finite-dimensional right comodule over the monoid algebra `k[G]` of a type `G` over a
field `k`. By `TauCeti.Comodule.isInternal_weightSpace`, `V` is the internal direct sum of its
weight spaces `V_g = {v | ρ v = v ⊗ g}`, and only finitely many of them are nonzero. The
**formal character** of `V` is the element `∑ g, dim V_g · g` of the integral monoid algebra
`ℤ[G]`.

When `G = X` is a commutative group, `k[X]` is the coordinate Hopf algebra of the diagonalizable
group `D(X)`, a split torus when `X` is free of finite rank, and the comodules over `k[X]` are the
rational representations of `D(X)`. The formal character then records the weight multiplicities
of a representation, labelled by the actual character lattice `X`. This file proves that it turns
the operations on representations into operations in `ℤ[X]`: direct sums into sums, tensor
products into products (weights add), and duals into the inversion `g ↦ g⁻¹` (weights negate).

The computations go through bases of weight vectors. Every finite-dimensional comodule has one
(`TauCeti.Comodule.exists_basis_mem_weightSpace`), the dimension of each weight space counts the
basis vectors of that weight (`TauCeti.Comodule.finrank_weightSpace_eq_card`), and the formal
character is the sum of the weights of the basis vectors
(`TauCeti.Comodule.formalCharacter_eq_sum_of_basis`). Tensor products, products and duals of
weight bases are again weight bases. The underlying statements about weight vectors,
`TauCeti.Comodule.tmul_mem_weightSpace_tensor` and `TauCeti.Comodule.mem_weightSpace_dual_iff`,
hold over every commutative semiring.

## Main definitions

* `TauCeti.Comodule.formalCharacter`: the formal character `∑ g, dim V_g · g ∈ ℤ[G]`.

## Main results

* `TauCeti.Comodule.tmul_mem_weightSpace_tensor`: a tensor product of weight vectors of weights
  `g` and `h` is a weight vector of weight `g * h`.
* `TauCeti.Comodule.mem_weightSpace_dual_iff`: a functional has weight `g` on the dual comodule
  exactly when it kills every weight space other than that of `g⁻¹`.
* `TauCeti.Comodule.formalCharacter_coeff`: the coefficients of the formal character are the
  weight multiplicities.
* `TauCeti.Comodule.sum_formalCharacter_coeff_eq_finrank`: the multiplicities add up to `dim V`.
* `TauCeti.Comodule.formalCharacter_congr`: isomorphic comodules have the same formal character.
* `TauCeti.Comodule.formalCharacter_prod`: **additivity on direct sums.**
* `TauCeti.Comodule.formalCharacter_tensor`: **multiplicativity on tensor products.**
* `TauCeti.Comodule.formalCharacter_dual`: **the dual has the inverted character.**

## References

* J. C. Jantzen, *Representations of Algebraic Groups*, 2nd ed. (2003), Part I, §2.11 (weight
  decompositions for diagonalizable groups) and Part II, §5.1 (formal characters).
-/

public section

open Module TensorProduct

namespace TauCeti.Comodule

universe u v w x

/-! ### Weights of tensor products and duals -/

section Tensor

variable {R : Type u} {G : Type v} [CommSemiring R] [Monoid G]
variable {V : Type w} [AddCommMonoid V] [Module R V] [Comodule R (MonoidAlgebra R G) V]
variable {W : Type x} [AddCommMonoid W] [Module R W] [Comodule R (MonoidAlgebra R G) W]

attribute [local instance] Comodule.tensor

/-- **Weights add in a tensor product.** For the diagonal coaction on `V ⊗ W`, the tensor product
of a vector of weight `g` and a vector of weight `h` has weight `g * h`. -/
theorem tmul_mem_weightSpace_tensor {g h : G} {v : V} {w : W}
    (hv : v ∈ weightSpace R G V g) (hw : w ∈ weightSpace R G W h) :
    v ⊗ₜ[R] w ∈ weightSpace R G (V ⊗[R] W) (g * h) := by
  rw [mem_weightSpace, tensor_coact, tensorCoact_tmul, mem_weightSpace.mp hv,
    mem_weightSpace.mp hw, tensorCombine_tmul_tmul, MonoidAlgebra.single_mul_single, one_mul]

end Tensor

section Dual

variable {R : Type u} {G : Type v} [CommSemiring R]
variable {V : Type w} [AddCommMonoid V] [Module R V] [Comodule R (MonoidAlgebra R G) V]

/-- The matrix coefficients of a vector of weight `g` are multiples of `g`. -/
theorem matrixCoefficient_of_mem_weightSpace {g : G} {v : V} (hv : v ∈ weightSpace R G V g)
    (φ : Module.Dual R V) :
    matrixCoefficient (C := MonoidAlgebra R G) φ v = MonoidAlgebra.single g (φ v) := by
  rw [matrixCoefficient_def, mem_weightSpace.mp hv, TensorProduct.map_tmul, LinearMap.id_apply,
    TensorProduct.lid_tmul, MonoidAlgebra.smul_single', mul_one]

variable [Group G] [Module.Finite R V] [Module.Projective R V]

attribute [local instance] Comodule.dual

/-- On a vector of weight `h`, the coaction of a functional on the dual comodule evaluates to a
multiple of `h⁻¹`. -/
private theorem dualTensorHom_coact_of_mem_weightSpace (φ : Module.Dual R V) {h : G} {v : V}
    (hv : v ∈ weightSpace R G V h) :
    dualTensorHom R V (MonoidAlgebra R G)
        (coact (R := R) (C := MonoidAlgebra R G) (M := Module.Dual R V) φ) v =
      MonoidAlgebra.single h⁻¹ (φ v) := by
  rw [dual_coact, dualTensorHom_dualCoact_apply, matrixCoefficient_of_mem_weightSpace hv,
    MonoidAlgebra.antipode_single]
  simp

/-- **Weights negate in the dual.** A functional on a finite projective comodule over `R[G]` has
weight `g` for the dual coaction exactly when it vanishes on every weight space of `V` other than
the `g⁻¹`-weight space. -/
theorem mem_weightSpace_dual_iff {φ : Module.Dual R V} {g : G} :
    φ ∈ weightSpace R G (Module.Dual R V) g ↔
      ∀ h : G, h ≠ g⁻¹ → ∀ v ∈ weightSpace R G V h, φ v = 0 := by
  constructor
  · intro hφ h hne v hv
    have key := dualTensorHom_coact_of_mem_weightSpace φ hv
    rw [mem_weightSpace.mp hφ, dualTensorHom_apply, MonoidAlgebra.smul_single', mul_one,
      MonoidAlgebra.single_inj] at key
    rcases key with ⟨hg, -⟩ | ⟨h0, -⟩
    · exact absurd (inv_eq_iff_eq_inv.mp hg.symm) hne
    · exact h0
  · intro hφ
    rw [mem_weightSpace]
    apply (dualTensorHomEquiv R V (MonoidAlgebra R G)).injective
    refine LinearMap.ext fun v ↦ ?_
    have hv : v ∈ ⨆ h : G, weightSpace R G V h := by
      rw [iSup_weightSpace_eq_top]
      exact Submodule.mem_top
    induction hv using Submodule.iSup_induction' with
    | mem h v hv =>
      rw [← LinearEquiv.coe_toLinearMap, toLinearMap_dualTensorHomEquiv,
        dualTensorHom_coact_of_mem_weightSpace φ hv, dualTensorHom_apply,
        MonoidAlgebra.smul_single', mul_one]
      by_cases hh : h = g⁻¹
      · rw [hh, inv_inv]
      · rw [hφ h hh v hv, MonoidAlgebra.single_zero, MonoidAlgebra.single_zero]
    | zero => simp
    | add v₁ v₂ _ _ h₁ h₂ => rw [map_add, map_add, h₁, h₂]

end Dual

/-! ### Weight bases -/

section WeightBasis

section Semiring

variable {R : Type u} {G : Type v} [CommSemiring R]
variable {V : Type w} [AddCommMonoid V] [Module R V] [Comodule R (MonoidAlgebra R G) V]
variable {ι : Type*} (b : Basis ι R V) (wt : ι → G) (hb : ∀ i, b i ∈ weightSpace R G V (wt i))
include hb

/-- In a basis of weight vectors, the basis vectors of weight `g` span the `g`-weight space. -/
theorem weightSpace_eq_span_of_basis (g : G) :
    weightSpace R G V g = Submodule.span R (b '' {i | wt i = g}) := by
  classical
  refine le_antisymm (fun v hv ↦ ?_) (Submodule.span_le.mpr ?_)
  · rw [← weightProj_of_mem hv, ← b.linearCombination_repr v, Finsupp.linearCombination_apply,
      Finsupp.sum, map_sum]
    refine Submodule.sum_mem _ fun i _ ↦ ?_
    rw [map_smul]
    refine Submodule.smul_mem _ _ ?_
    by_cases hi : wt i = g
    · rw [← hi, weightProj_of_mem (hb i)]
      exact Submodule.subset_span ⟨i, rfl, rfl⟩
    · rw [weightProj_of_mem_of_ne (Ne.symm hi) (hb i)]
      exact Submodule.zero_mem _
  · rintro _ ⟨i, hi, rfl⟩
    exact (show wt i = g from hi) ▸ hb i

end Semiring

variable {k : Type u} {G : Type v} [Field k]
variable {V : Type w} [AddCommGroup V] [Module k V] [Comodule k (MonoidAlgebra k G) V]

variable (k G V) in
/-- **Every finite-dimensional comodule over `k[G]` has a basis of weight vectors.** -/
theorem exists_basis_mem_weightSpace [FiniteDimensional k V] :
    ∃ (ι : Type (max v w)) (_ : Fintype ι) (b : Basis ι k V) (wt : ι → G),
      ∀ i, b i ∈ weightSpace k G V (wt i) := by
  classical
  let b := (isInternal_weightSpace k G V).collectedBasis fun g ↦
    Module.Free.chooseBasis k (weightSpace k G V g)
  exact ⟨_, FiniteDimensional.fintypeBasisIndex b, b, Sigma.fst,
    (isInternal_weightSpace k G V).collectedBasis_mem _⟩

variable {ι : Type*} (b : Basis ι k V) (wt : ι → G) (hb : ∀ i, b i ∈ weightSpace k G V (wt i))
include hb

/-- **Weight multiplicities count weight basis vectors.** In a basis of weight vectors, the
dimension of the `g`-weight space is the number of basis vectors of weight `g`. -/
theorem finrank_weightSpace_eq_card [Finite ι] (g : G) :
    finrank k (weightSpace k G V g) = Nat.card {i // wt i = g} := by
  have := Fintype.ofFinite ι
  have := Fintype.ofFinite {i // wt i = g}
  rw [weightSpace_eq_span_of_basis b wt hb g, ← Subtype.range_coe_subtype, ← Set.range_comp,
    finrank_span_eq_card (b.linearIndependent.comp _ Subtype.val_injective),
    Nat.card_eq_fintype_card]

section Dual

variable [Group G] [FiniteDimensional k V]

attribute [local instance] Comodule.dual

/-- **The dual basis of a weight basis is a weight basis, with inverted weights.** -/
theorem dualBasis_mem_weightSpace [Finite ι] [DecidableEq ι] (i : ι) :
    b.dualBasis i ∈ weightSpace k G (Module.Dual k V) (wt i)⁻¹ := by
  rw [mem_weightSpace_dual_iff, inv_inv]
  intro h hne v hv
  have hle : weightSpace k G V h ≤ LinearMap.ker (b.dualBasis i) := by
    rw [weightSpace_eq_span_of_basis b wt hb h, Submodule.span_le]
    rintro _ ⟨j, hj, rfl⟩
    have hji : j ≠ i := fun hji ↦ hne (hji ▸ hj).symm
    simp [hji]
  exact hle hv

end Dual

end WeightBasis

/-! ### The formal character -/

section Character

variable (k : Type u) (G : Type v) [Field k]
variable (V : Type w) [AddCommGroup V] [Module k V] [Comodule k (MonoidAlgebra k G) V]
  [FiniteDimensional k V]

/-- **The formal character** of a finite-dimensional comodule over `k[G]`: the element of the
integral monoid algebra `ℤ[G]` whose coefficient at `g` is the dimension of the `g`-weight
space. -/
noncomputable def formalCharacter : MonoidAlgebra ℤ G :=
  .ofCoeff (Finsupp.ofSupportFinite (fun g ↦ (finrank k (weightSpace k G V g) : ℤ))
    ((finite_setOf_weightSpace_ne_bot k G V).subset fun g hg hbot ↦ hg (by simp [hbot])))

variable {k G V}

/-- The coefficient of the formal character at `g` is the dimension of the `g`-weight space. -/
@[simp]
theorem formalCharacter_coeff (g : G) :
    (formalCharacter k G V).coeff g = (finrank k (weightSpace k G V g) : ℤ) := by
  rw [formalCharacter, Finsupp.ofSupportFinite_coe]

/-- **The formal character as a sum over a weight basis.** Each vector of a basis of weight
vectors contributes its weight. -/
theorem formalCharacter_eq_sum_of_basis {ι : Type*} [Fintype ι] (b : Basis ι k V) (wt : ι → G)
    (hb : ∀ i, b i ∈ weightSpace k G V (wt i)) :
    formalCharacter k G V = ∑ i, MonoidAlgebra.single (wt i) 1 := by
  classical
  refine MonoidAlgebra.coeff_injective (Finsupp.ext fun g ↦ ?_)
  rw [formalCharacter_coeff, finrank_weightSpace_eq_card b wt hb, MonoidAlgebra.coeff_sum,
    Finsupp.finsetSum_apply, Nat.card_eq_fintype_card, Fintype.card_subtype]
  simp [Finsupp.single_apply]

variable (k G V) in
/-- **The weight multiplicities add up to the dimension.** -/
theorem sum_formalCharacter_coeff_eq_finrank :
    ((formalCharacter k G V).coeff.sum fun _ n ↦ n) = (finrank k V : ℤ) := by
  obtain ⟨ι, _, b, wt, hb⟩ := exists_basis_mem_weightSpace k G V
  rw [formalCharacter_eq_sum_of_basis b wt hb, MonoidAlgebra.coeff_sum,
    ← Finsupp.sum_finsetSum_index (fun _ ↦ rfl) fun _ _ _ ↦ rfl, finrank_eq_card_basis b]
  simp

variable {W : Type x} [AddCommGroup W] [Module k W] [Comodule k (MonoidAlgebra k G) W]
  [FiniteDimensional k W]

/-- **The formal character is an isomorphism invariant.** -/
theorem formalCharacter_congr (f : Hom k (MonoidAlgebra k G) V W) (hf : Function.Bijective f) :
    formalCharacter k G V = formalCharacter k G W := by
  obtain ⟨ι, _, b, wt, hb⟩ := exists_basis_mem_weightSpace k G V
  rw [formalCharacter_eq_sum_of_basis b wt hb,
    formalCharacter_eq_sum_of_basis (b.map (LinearEquiv.ofBijective f.toLinearMap hf)) wt
      fun i ↦ by simpa using f.map_mem_weightSpace (hb i)]

section Prod

attribute [local instance] Comodule.Prod

/-- **The formal character is additive on direct sums.** -/
theorem formalCharacter_prod :
    formalCharacter k G (V × W) = formalCharacter k G V + formalCharacter k G W := by
  obtain ⟨ι, _, b, wt, hb⟩ := exists_basis_mem_weightSpace k G V
  obtain ⟨κ, _, c, wt', hc⟩ := exists_basis_mem_weightSpace k G W
  rw [formalCharacter_eq_sum_of_basis b wt hb, formalCharacter_eq_sum_of_basis c wt' hc,
    formalCharacter_eq_sum_of_basis (b.prod c) (Sum.elim wt wt') ?_, Fintype.sum_sum_type]
  · simp only [Sum.elim_inl, Sum.elim_inr]
  rintro (i | j)
  · simpa [Basis.prod_apply] using (prodInl (C := MonoidAlgebra k G) (N := W)).map_mem_weightSpace
      (hb i)
  · simpa [Basis.prod_apply] using (prodInr (C := MonoidAlgebra k G) (M := V)).map_mem_weightSpace
      (hc j)

end Prod

section Tensor

variable [Monoid G]

attribute [local instance] Comodule.tensor

/-- **The formal character is multiplicative on tensor products.** -/
theorem formalCharacter_tensor :
    formalCharacter k G (V ⊗[k] W) = formalCharacter k G V * formalCharacter k G W := by
  obtain ⟨ι, _, b, wt, hb⟩ := exists_basis_mem_weightSpace k G V
  obtain ⟨κ, _, c, wt', hc⟩ := exists_basis_mem_weightSpace k G W
  rw [formalCharacter_eq_sum_of_basis b wt hb, formalCharacter_eq_sum_of_basis c wt' hc,
    formalCharacter_eq_sum_of_basis (b.tensorProduct c) (fun p ↦ wt p.1 * wt' p.2)
      fun p ↦ by
        rw [Basis.tensorProduct_apply']
        exact tmul_mem_weightSpace_tensor (hb p.1) (hc p.2),
    Finset.sum_mul_sum, ← Finset.univ_product_univ, Finset.sum_product]
  simp [MonoidAlgebra.single_mul_single]

end Tensor

section Dual

variable [Group G]

attribute [local instance] Comodule.dual

/-- **Weights negate in the dual.** The multiplicity of `g` in the dual comodule is the
multiplicity of `g⁻¹` in `V`. -/
theorem finrank_weightSpace_dual (g : G) :
    finrank k (weightSpace k G (Module.Dual k V) g) = finrank k (weightSpace k G V g⁻¹) := by
  classical
  obtain ⟨ι, _, b, wt, hb⟩ := exists_basis_mem_weightSpace k G V
  rw [finrank_weightSpace_eq_card b.dualBasis (fun i ↦ (wt i)⁻¹)
      (dualBasis_mem_weightSpace b wt hb) g, finrank_weightSpace_eq_card b wt hb g⁻¹]
  exact Nat.card_congr (Equiv.subtypeEquivRight fun _ ↦ inv_eq_iff_eq_inv)

/-- **The formal character of the dual is the inverted character.** -/
theorem formalCharacter_dual :
    formalCharacter k G (Module.Dual k V) =
      MonoidAlgebra.mapDomain (fun g : G ↦ g⁻¹) (formalCharacter k G V) := by
  refine MonoidAlgebra.coeff_injective (Finsupp.ext fun g ↦ ?_)
  rw [formalCharacter_coeff, finrank_weightSpace_dual, MonoidAlgebra.coeff_mapDomain,
    ← inv_inv g, Finsupp.mapDomain_apply_of_injective inv_injective, inv_inv, formalCharacter_coeff]

end Dual

end Character

end TauCeti.Comodule
