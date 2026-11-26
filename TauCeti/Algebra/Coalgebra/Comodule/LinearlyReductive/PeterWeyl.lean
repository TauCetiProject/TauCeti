/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Coalgebra.Comodule.LinearlyReductive.Cosemisimple
public import TauCeti.Algebra.Coalgebra.Comodule.MatrixCoefficient.DirectSum
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Dual.Lemmas
import TauCeti.Algebra.Coalgebra.Subcomodule.Finite

/-!
# The algebraic Peter–Weyl theorem

Let `C` be a linearly reductive coalgebra over a field `k`, for instance the coordinate Hopf
algebra `O(G)` of a linearly reductive affine group. Let `(Vᵢ)` be a family of simple comodules
containing exactly one copy of each simple comodule up to isomorphism: there is no nonzero
morphism between distinct members, and every simple right coideal of `C` admits a nonzero
morphism to some member. Over an algebraically closed field the coefficient maps
`φ ⊗ v ↦ (φ ⊗ id) ρ(v)` then identify

```text
⨁ᵢ Vᵢ* ⊗ Vᵢ ≃ C
```

(`TauCeti.Coalgebra.IsLinearlyReductive.peterWeylEquiv`). For `C = O(G)`, the element `φ ⊗ v` of
the summand of `Vᵢ` goes to the regular function `g ↦ φ(g v)`. Surjectivity holds over every
field, since a linearly reductive coalgebra is spanned by the coefficient spaces of its simple
right coideals; injectivity is `TauCeti.Comodule.directSumMatrixCoefficientTensor_injective` and
uses only that `k` is algebraically closed. In particular, a finite family gives
`dim C = ∑ᵢ (dim Vᵢ)²` (`TauCeti.Coalgebra.IsLinearlyReductive.finrank_eq_sum_sq`).

The coaction of `C` on itself by comultiplication corresponds to the coaction on the right
factors `Vᵢ` (`TauCeti.Comodule.comul_matrixCoefficient`), and for a Hopf algebra the left regular
coaction corresponds to the dual coaction on the left factors `Vᵢ*`
(`TauCeti.Comodule.leftRegularCoact_matrixCoefficient`).

Over a field which is not algebraically closed the summand `Vᵢ* ⊗ Vᵢ` is larger than the
coefficient space of `Vᵢ` as soon as `Vᵢ` has endomorphisms other than scalars; there the
decomposition into the actual simple coefficient spaces is
`TauCeti.Coalgebra.IsLinearlyReductive.isInternal_simpleCoefficientSubmodules`.

## Main declarations

* `TauCeti.Coalgebra.IsLinearlyReductive.directSumMatrixCoefficientTensor_surjective`: the
  coefficient maps of a complete family of simple comodules are jointly surjective.
* `TauCeti.Coalgebra.IsLinearlyReductive.peterWeylEquiv`: the algebraic Peter–Weyl isomorphism.
* `TauCeti.Coalgebra.IsLinearlyReductive.peterWeylEquiv_symm_matrixCoefficient`: its inverse on a
  matrix coefficient.
* `TauCeti.Coalgebra.IsLinearlyReductive.exists_peterWeylEquiv`: such an isomorphism exists for
  some family of simple comodules.
* `TauCeti.Coalgebra.IsLinearlyReductive.finrank_eq_sum_sq`: the dimension formula.

## References

* M. Sweedler, *Hopf Algebras* (1969), Chapter XIV, cosemisimple coalgebras.
* J. S. Milne, *Algebraic Groups* (2017), Chapter 12, the regular representation of a linearly
  reductive group.
-/

public noncomputable section

open scoped TensorProduct DirectSum

namespace TauCeti.Coalgebra.IsLinearlyReductive

universe u v

variable {k : Type u} [Field k]
  {C : Type v} [AddCommGroup C] [Module k C] [Coalgebra k C]
  {ι : Type*} [DecidableEq ι] (V : ι → Type*) [∀ i, AddCommGroup (V i)] [∀ i, Module k (V i)]
  [∀ i, Comodule k C (V i)] [∀ i, IsSimpleOrder (Subcomodule k C (V i))]

/-- For a linearly reductive coalgebra over any field, the coefficient maps of a family of simple
comodules to which every simple right coideal admits a nonzero morphism are jointly
surjective. -/
theorem directSumMatrixCoefficientTensor_surjective (hC : IsLinearlyReductive.{u, v, u} k C)
    (hV : ∀ S : Subcomodule k C C, IsAtom S → ∃ i, ∃ f : Comodule.Hom k C S (V i), f ≠ 0) :
    Function.Surjective (Comodule.directSumMatrixCoefficientTensor (R := k) (C := C) V) := by
  rw [← LinearMap.range_eq_top, Comodule.range_directSumMatrixCoefficientTensor, eq_top_iff,
    ← hC.iSup_matrixCoefficientSubmodule_eq_top]
  refine iSup₂_le fun S hS ↦ ?_
  have := Subcomodule.isSimpleOrder_of_isAtom hS
  obtain ⟨i, f, hf⟩ := hV S hS
  rw [Comodule.matrixCoefficientSubmodule_eq_of_ne_zero hf]
  exact le_iSup (fun i ↦ Comodule.matrixCoefficientSubmodule (R := k) (C := C) (M := V i)) i

/-- **The algebraic Peter–Weyl theorem.** Over an algebraically closed field, a linearly reductive
coalgebra `C` is the direct sum of the spaces `Vᵢ* ⊗ Vᵢ`, for any family `(Vᵢ)` of pairwise
non-isomorphic simple comodules to one of which every simple right coideal admits a nonzero
morphism. The isomorphism sends `φ ⊗ v` in the summand of `Vᵢ` to the matrix coefficient
`(φ ⊗ id) ρ(v)`. -/
def peterWeylEquiv [IsAlgClosed k] (hC : IsLinearlyReductive.{u, v, u} k C)
    (hV : Pairwise fun i j ↦ ∀ f : Comodule.Hom k C (V i) (V j), f = 0)
    (hV' : ∀ S : Subcomodule k C C, IsAtom S → ∃ i, ∃ f : Comodule.Hom k C S (V i), f ≠ 0) :
    (⨁ i, Module.Dual k (V i) ⊗[k] V i) ≃ₗ[k] C :=
  LinearEquiv.ofBijective (Comodule.directSumMatrixCoefficientTensor (R := k) (C := C) V)
    ⟨Comodule.directSumMatrixCoefficientTensor_injective V hV,
      directSumMatrixCoefficientTensor_surjective V hC hV'⟩

/-- The Peter–Weyl isomorphism is the assembled coefficient map. -/
@[simp]
theorem coe_peterWeylEquiv [IsAlgClosed k] (hC : IsLinearlyReductive.{u, v, u} k C)
    (hV : Pairwise fun i j ↦ ∀ f : Comodule.Hom k C (V i) (V j), f = 0)
    (hV' : ∀ S : Subcomodule k C C, IsAtom S → ∃ i, ∃ f : Comodule.Hom k C S (V i), f ≠ 0) :
    ⇑(peterWeylEquiv V hC hV hV') = Comodule.directSumMatrixCoefficientTensor (R := k) (C := C) V :=
  (rfl)

/-- The inverse Peter–Weyl isomorphism sends the matrix coefficient of `φ ⊗ v` to `φ ⊗ v` in the
summand of `Vᵢ`. -/
@[simp]
theorem peterWeylEquiv_symm_matrixCoefficient [IsAlgClosed k]
    (hC : IsLinearlyReductive.{u, v, u} k C)
    (hV : Pairwise fun i j ↦ ∀ f : Comodule.Hom k C (V i) (V j), f = 0)
    (hV' : ∀ S : Subcomodule k C C, IsAtom S → ∃ i, ∃ f : Comodule.Hom k C S (V i), f ≠ 0)
    (i : ι) (φ : Module.Dual k (V i)) (v : V i) :
    (peterWeylEquiv V hC hV hV').symm (Comodule.matrixCoefficient (C := C) φ v) =
      DirectSum.lof k ι (fun i ↦ Module.Dual k (V i) ⊗[k] V i) i (φ ⊗ₜ v) := by
  rw [LinearEquiv.symm_apply_eq, coe_peterWeylEquiv,
    Comodule.directSumMatrixCoefficientTensor_lof, Comodule.matrixCoefficientTensor_tmul]

omit [DecidableEq ι] in
/-- **Dimension formula.** Over an algebraically closed field, the dimension of a linearly
reductive coalgebra is the sum of the squares of the dimensions of a finite family of
representatives of its simple comodules. -/
theorem finrank_eq_sum_sq [IsAlgClosed k] [Fintype ι] (hC : IsLinearlyReductive.{u, v, u} k C)
    (hV : Pairwise fun i j ↦ ∀ f : Comodule.Hom k C (V i) (V j), f = 0)
    (hV' : ∀ S : Subcomodule k C C, IsAtom S → ∃ i, ∃ f : Comodule.Hom k C S (V i), f ≠ 0) :
    Module.finrank k C = ∑ i, Module.finrank k (V i) ^ 2 := by
  classical
  have (i : ι) : Module.Finite k (V i) := Comodule.finite_of_isSimpleOrder (C := C)
  rw [← (peterWeylEquiv V hC hV hV').finrank_eq, Module.finrank_directSum]
  simp [Module.finrank_tensorProduct, Subspace.dual_finrank_eq, sq]

/-- Over an algebraically closed field, every linearly reductive coalgebra is isomorphic to
`⨁ᵢ Vᵢ* ⊗ Vᵢ` for some family of simple comodules, by the assembled coefficient map. -/
theorem exists_peterWeylEquiv [IsAlgClosed k] (hC : IsLinearlyReductive.{u, v, u} k C) :
    ∃ (ι : Type v) (_ : DecidableEq ι) (V : ι → ComoduleCat.{u, v, v} k C)
      (_ : ∀ i, IsSimpleOrder (Subcomodule k C (V i)))
      (e : (⨁ i, Module.Dual k (V i) ⊗[k] V i) ≃ₗ[k] C),
      ⇑e = Comodule.directSumMatrixCoefficientTensor (R := k) (C := C) (fun i ↦ V i) := by
  classical
  obtain ⟨ι, V, hsimple, hV, hV'⟩ :=
    Comodule.exists_simple_family_pairwise_complete (k := k) (C := C)
  exact ⟨ι, inferInstance, V, hsimple, peterWeylEquiv _ hC hV hV', coe_peterWeylEquiv _ hC hV hV'⟩

end TauCeti.Coalgebra.IsLinearlyReductive
