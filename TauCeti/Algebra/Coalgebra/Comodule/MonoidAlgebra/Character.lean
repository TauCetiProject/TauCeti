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
basis vectors of that weight (`Module.Basis.finrank_comoduleWeightSpace_eq_card`), and the formal
character is the sum of the weights of the basis vectors
(`Module.Basis.comoduleFormalCharacter_eq_sum`). Tensor products, products and duals of
weight bases are again weight bases. Tensor products of weight vectors are handled by
`TauCeti.Comodule.tmul_mem_weightSpace_tensor` in
`TauCeti.Algebra.Coalgebra.Comodule.MonoidAlgebra.Basic`. The underlying statements about dual
weight vectors, `TauCeti.Comodule.mem_weightSpace_dual_iff` and
`Module.Basis.dualBasis_mem_comoduleWeightSpace`, hold over every commutative semiring.

## Main definitions

* `TauCeti.Comodule.formalCharacter`: the formal character `∑ g, dim V_g · g ∈ ℤ[G]`.

## Main results

* `TauCeti.Comodule.mem_weightSpace_dual_iff`: a functional has weight `g` on the dual comodule
  exactly when it kills every weight space other than that of `g⁻¹`.
* `TauCeti.Comodule.formalCharacter_coeff`: the coefficients of the formal character are the
  weight multiplicities.
* `TauCeti.Comodule.formalCharacter_coeff_eq_zero_iff`: the formal character is supported on the
  weights.
* `TauCeti.Comodule.sum_formalCharacter_coeff_eq_finrank`: the multiplicities add up to `dim V`.
* `TauCeti.Comodule.formalCharacter_eq_zero_iff`: the formal character vanishes only for the zero
  comodule.
* `TauCeti.Comodule.formalCharacter_congr`: isomorphic comodules have the same formal character.
* `TauCeti.Comodule.formalCharacter_prod`: **additivity on direct sums.**
* `TauCeti.Comodule.formalCharacter_tensor`: **multiplicativity on tensor products.**
* `TauCeti.Comodule.formalCharacter_dual`: **the dual has the inverted character.**
* `TauCeti.Comodule.formalCharacter_groupLike` and `TauCeti.Comodule.formalCharacter_trivial`:
  the comodule with coaction `v ↦ v ⊗ g` has formal character `dim V · g`; for `g = 1`, the
  trivial comodule, this is `dim V`.

## References

* J. C. Jantzen, *Representations of Algebraic Groups*, 2nd ed. (2003), Part I, §2.11 (weight
  decompositions for diagonalizable groups) and Part II, §5.1 (formal characters).
-/

public section

open Module TensorProduct

namespace TauCeti.Comodule

universe u v w x

/-! ### Weights of duals -/

section Dual

variable {R : Type u} {G : Type v} [CommSemiring R]
variable {V : Type w} [AddCommMonoid V] [Module R V] [Comodule R (MonoidAlgebra R G) V]
variable [Group G] [Module.Finite R V] [Module.Projective R V]

attribute [local instance] Comodule.dual

/-- On a vector of weight `h`, the coaction of a functional on the dual comodule evaluates to a
multiple of `h⁻¹`. -/
private theorem dualTensorHom_coact_of_mem_weightSpace (φ : Module.Dual R V) {h : G} {v : V}
    (hv : v ∈ weightSpace R G V h) :
    dualTensorHom R V (MonoidAlgebra R G)
        (coact (R := R) (C := MonoidAlgebra R G) (M := Module.Dual R V) φ) v =
      MonoidAlgebra.single h⁻¹ (φ v) := by
  rw [dual_coact, dualTensorHom_dualCoact_apply, matrixCoefficient_of_mem_weightSpace hv]
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
    rw [mem_weightSpace.mp hφ] at key
    simpa [MonoidAlgebra.single_inj, ← inv_eq_iff_eq_inv, hne.symm] using key
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
        dualTensorHom_coact_of_mem_weightSpace φ hv]
      by_cases hh : h = g⁻¹
      · simp [hh]
      · simp [hφ h hh v hv]
    | zero => simp
    | add v₁ v₂ _ _ h₁ h₂ => rw [map_add, map_add, h₁, h₂]

/-- **The dual basis of a weight basis is a weight basis, with inverted weights.** -/
theorem _root_.Module.Basis.dualBasis_mem_comoduleWeightSpace {ι : Type*} [Finite ι]
    [DecidableEq ι] (b : Basis ι R V) (wt : ι → G) (hb : ∀ i, b i ∈ weightSpace R G V (wt i))
    (i : ι) : b.dualBasis i ∈ weightSpace R G (Module.Dual R V) (wt i)⁻¹ := by
  rw [mem_weightSpace_dual_iff, inv_inv]
  intro h hne v hv
  have hle : weightSpace R G V h ≤ LinearMap.ker (b.dualBasis i) := by
    rw [b.comoduleWeightSpace_eq_span wt hb h, Submodule.span_le]
    rintro _ ⟨j, hj, rfl⟩
    have hji : j ≠ i := fun hji ↦ hne (hji ▸ hj).symm
    simp [hji]
  exact hle hv

end Dual

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

/-- A coefficient of the formal character vanishes exactly at an element that is not a weight. -/
theorem formalCharacter_coeff_eq_zero_iff {g : G} :
    (formalCharacter k G V).coeff g = 0 ↔ weightSpace k G V g = ⊥ := by
  rw [formalCharacter_coeff, Int.natCast_eq_zero, Submodule.finrank_eq_zero]

/-- **The formal character as a sum over a weight basis.** Each vector of a basis of weight
vectors contributes its weight. -/
theorem _root_.Module.Basis.comoduleFormalCharacter_eq_sum {ι : Type*} [Fintype ι]
    (b : Basis ι k V) (wt : ι → G) (hb : ∀ i, b i ∈ weightSpace k G V (wt i)) :
    formalCharacter k G V = ∑ i, MonoidAlgebra.single (wt i) 1 := by
  classical
  refine MonoidAlgebra.coeff_injective (Finsupp.ext fun g ↦ ?_)
  rw [formalCharacter_coeff, b.finrank_comoduleWeightSpace_eq_card wt hb, MonoidAlgebra.coeff_sum,
    Finsupp.finsetSum_apply, Nat.card_eq_fintype_card, Fintype.card_subtype]
  simp [Finsupp.single_apply]

variable (k G V) in
/-- **The weight multiplicities add up to the dimension.** -/
theorem sum_formalCharacter_coeff_eq_finrank :
    ((formalCharacter k G V).coeff.sum fun _ n ↦ n) = (finrank k V : ℤ) := by
  obtain ⟨ι, _, b, wt, hb⟩ := exists_basis_mem_weightSpace k G V
  rw [b.comoduleFormalCharacter_eq_sum wt hb, MonoidAlgebra.coeff_sum,
    ← Finsupp.sum_finsetSum_index (fun _ ↦ rfl) fun _ _ _ ↦ rfl, finrank_eq_card_basis b]
  simp

variable (k G V) in
/-- **The formal character vanishes only for the zero comodule.** -/
@[simp]
theorem formalCharacter_eq_zero_iff : formalCharacter k G V = 0 ↔ finrank k V = 0 := by
  refine ⟨fun h ↦ ?_, fun h ↦ MonoidAlgebra.coeff_injective (Finsupp.ext fun g ↦ ?_)⟩
  · simpa [h] using (sum_formalCharacter_coeff_eq_finrank k G V).symm
  · rw [MonoidAlgebra.coeff_zero, Finsupp.zero_apply, formalCharacter_coeff_eq_zero_iff,
      ← Submodule.finrank_eq_zero]
    exact Nat.le_zero.mp (h ▸ Submodule.finrank_le _)

variable {W : Type x} [AddCommGroup W] [Module k W] [Comodule k (MonoidAlgebra k G) W]
  [FiniteDimensional k W]

/-- **The formal character is an isomorphism invariant.** -/
theorem formalCharacter_congr (f : Hom k (MonoidAlgebra k G) V W) (hf : Function.Bijective f) :
    formalCharacter k G V = formalCharacter k G W := by
  obtain ⟨ι, _, b, wt, hb⟩ := exists_basis_mem_weightSpace k G V
  rw [b.comoduleFormalCharacter_eq_sum wt hb,
    (b.map (LinearEquiv.ofBijective f.toLinearMap hf)).comoduleFormalCharacter_eq_sum wt
      fun i ↦ by simpa using f.map_mem_weightSpace (hb i)]

section Prod

attribute [local instance] Comodule.Prod

/-- **The formal character is additive on direct sums.** -/
@[simp]
theorem formalCharacter_prod :
    formalCharacter k G (V × W) = formalCharacter k G V + formalCharacter k G W := by
  obtain ⟨ι, _, b, wt, hb⟩ := exists_basis_mem_weightSpace k G V
  obtain ⟨κ, _, c, wt', hc⟩ := exists_basis_mem_weightSpace k G W
  rw [b.comoduleFormalCharacter_eq_sum wt hb, c.comoduleFormalCharacter_eq_sum wt' hc,
    (b.prod c).comoduleFormalCharacter_eq_sum (Sum.elim wt wt') ?_, Fintype.sum_sum_type]
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
@[simp]
theorem formalCharacter_tensor :
    formalCharacter k G (V ⊗[k] W) = formalCharacter k G V * formalCharacter k G W := by
  obtain ⟨ι, _, b, wt, hb⟩ := exists_basis_mem_weightSpace k G V
  obtain ⟨κ, _, c, wt', hc⟩ := exists_basis_mem_weightSpace k G W
  rw [b.comoduleFormalCharacter_eq_sum wt hb, c.comoduleFormalCharacter_eq_sum wt' hc,
    (b.tensorProduct c).comoduleFormalCharacter_eq_sum (fun p ↦ wt p.1 * wt' p.2)
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
  rw [b.dualBasis.finrank_comoduleWeightSpace_eq_card (fun i ↦ (wt i)⁻¹)
      (b.dualBasis_mem_comoduleWeightSpace wt hb) g,
    b.finrank_comoduleWeightSpace_eq_card wt hb g⁻¹]
  exact Nat.card_congr (Equiv.subtypeEquivRight fun _ ↦ inv_eq_iff_eq_inv)

/-- **The formal character of the dual is the inverted character.** -/
@[simp]
theorem formalCharacter_dual :
    formalCharacter k G (Module.Dual k V) =
      MonoidAlgebra.mapDomain (fun g : G ↦ g⁻¹) (formalCharacter k G V) := by
  refine MonoidAlgebra.coeff_injective (Finsupp.ext fun g ↦ ?_)
  simpa [finrank_weightSpace_dual] using
    (Finsupp.mapDomain_equiv_apply (f := Equiv.inv G) (formalCharacter k G V).coeff g).symm

end Dual

end Character

/-! ### Group-like and trivial comodules -/

section GroupLike

variable {k : Type u} {G : Type v} [Field k]
variable {V : Type w} [AddCommGroup V] [Module k V] [FiniteDimensional k V]

/-- **The formal character of a group-like comodule.** If the coaction is `v ↦ v ⊗ g`, every
vector has weight `g`, so the formal character is `dim V · g`. -/
@[simp]
theorem formalCharacter_groupLike (g : G) :
    letI : Comodule k (MonoidAlgebra k G) V := groupLike (R := k) (M := V)
      ⟨MonoidAlgebra.single g 1, MonoidAlgebra.isGroupLikeElem_single_one g⟩
    formalCharacter k G V = MonoidAlgebra.single g (finrank k V : ℤ) := by
  let _ : Comodule k (MonoidAlgebra k G) V := groupLike (R := k) (M := V)
    ⟨MonoidAlgebra.single g 1, MonoidAlgebra.isGroupLikeElem_single_one g⟩
  let b := Module.finBasis k V
  rw [b.comoduleFormalCharacter_eq_sum (fun _ ↦ g) fun i ↦ mem_weightSpace.mpr rfl]
  simp

/-- **The formal character of the trivial comodule** is its dimension: every vector has
weight `1`. Not a simp lemma: `formalCharacter_groupLike` already rewrites the left-hand side,
to `single 1 (dim V)`. -/
theorem formalCharacter_trivial [Monoid G] :
    letI : Comodule k (MonoidAlgebra k G) V := trivial (R := k) (M := V)
    formalCharacter k G V = finrank k V :=
  formalCharacter_groupLike (k := k) (V := V) (1 : G)

end GroupLike

end TauCeti.Comodule
