/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Sum.Order
public import Mathlib.LinearAlgebra.Basis.Prod
public import Mathlib.LinearAlgebra.Basis.VectorSpace
public import Mathlib.LinearAlgebra.TensorProduct.Basis
public import TauCeti.Algebra.Lie.UniversalEnveloping.Functoriality
public import TauCeti.Algebra.Lie.UniversalEnveloping.PBW.Basis
public import TauCeti.Data.Multiset.Sort

/-!
# PBW decomposition relative to a Lie subalgebra

An ordered basis of a complement of a Lie subalgebra, followed by an ordered basis of the
subalgebra, gives a PBW basis whose monomials factor in that order. If the complement is itself
a Lie subalgebra, multiplication identifies the tensor product of the two enveloping algebras
with the enveloping algebra of the ambient Lie algebra as modules. The subalgebras need not
commute, so this is a linear equivalence. This is the algebraic input to triangular decomposition
and to induced highest weight modules.

## References

* J. E. Humphreys, *Introduction to Lie Algebras and Representation Theory*, §17.4 and §20.3.
-/

public section

namespace TauCeti.UniversalEnvelopingAlgebra

open LieAlgebra Module

universe u v w₁ w₂

variable {R : Type u} {L : Type v} [CommRing R] [LieRing L] [LieAlgebra R L]

section Adapted

variable (B : LieSubalgebra R L) {A : Submodule R L} (hA : IsCompl A (B : Submodule R L))
  {ιA : Type w₁} {ιB : Type w₂} (bA : Basis ιA R A) (bB : Basis ιB R B)

/-- The basis of `L` listing the basis `bA` of the complement before the basis `bB` of `B`. -/
private noncomputable def adaptedBasis : Basis (ιA ⊕ₗ ιB) R L :=
  ((bA.prod bB).map (Submodule.prodEquivOfIsCompl A (B : Submodule R L) hA)).reindex toLex

private theorem adaptedBasis_inl (i : ιA) :
    adaptedBasis B hA bA bB (Sum.inlₗ i) = (bA i : L) := by
  simp only [adaptedBasis, Basis.coe_reindex, toLex_symm_eq, Function.comp_apply, ofLex_toLex,
    Basis.map_apply, Basis.prod_apply, LinearMap.coe_inl, Sum.elim_inl]
  rw [Submodule.coe_prodEquivOfIsCompl', ZeroMemClass.coe_zero, add_zero]

private theorem adaptedBasis_inr (j : ιB) :
    adaptedBasis B hA bA bB (Sum.inrₗ j) = (bB j : L) := by
  simp only [adaptedBasis, Basis.coe_reindex, toLex_symm_eq, Function.comp_apply, ofLex_toLex,
    Basis.map_apply, Basis.prod_apply, LinearMap.coe_inr, Sum.elim_inr]
  rw [Submodule.coe_prodEquivOfIsCompl', ZeroMemClass.coe_zero, zero_add]

/-- Exponent vectors over the ordered sum, split into their two halves. -/
private noncomputable def sumExponentEquiv : ((ιA →₀ ℕ) × (ιB →₀ ℕ)) ≃ (ιA ⊕ₗ ιB →₀ ℕ) :=
  Finsupp.sumFinsuppEquivProdFinsupp.symm.trans (Finsupp.domCongr toLex).toEquiv

private theorem sumExponentEquiv_apply (α : ιA →₀ ℕ) (β : ιB →₀ ℕ) :
    sumExponentEquiv (α, β) = α.mapDomain Sum.inlₗ + β.mapDomain Sum.inrₗ := by
  ext x
  obtain ⟨i | j, rfl⟩ := toLex.surjective x
  · simp only [sumExponentEquiv, Equiv.trans_apply, Finsupp.coe_add, Pi.add_apply]
    simp [Finsupp.mapDomain_of_notMem_range,
      Finsupp.mapDomain_apply_of_injective (f := Sum.inlₗ (β := ιB))
        (toLex.injective.comp Sum.inl_injective) α i]
  · simp only [sumExponentEquiv, Equiv.trans_apply, Finsupp.coe_add, Pi.add_apply]
    simp [Finsupp.mapDomain_of_notMem_range,
      Finsupp.mapDomain_apply_of_injective (f := Sum.inrₗ (α := ιA))
        (toLex.injective.comp Sum.inr_injective) β j]

end Adapted

end TauCeti.UniversalEnvelopingAlgebra

namespace LieSubalgebra

open LieAlgebra Module TauCeti TauCeti.UniversalEnvelopingAlgebra
open scoped TensorProduct

attribute [local instance 100] LieRing.ofAssociativeRing

universe u v w₁ w₂

variable {R : Type u} {L : Type v} [CommRing R] [LieRing L] [LieAlgebra R L]

local notation "U" => UniversalEnvelopingAlgebra R L

section Adapted

variable (B : LieSubalgebra R L) {A : Submodule R L} (hA : IsCompl A (B : Submodule R L))
  {ιA : Type w₁} {ιB : Type w₂} (bA : Basis ιA R A) (bB : Basis ιB R B)
  [LinearOrder ιA] [LinearOrder ιB]

/-- The PBW basis indexed separately by the exponents on a complement and on the subalgebra.
Its values are the products described by `relativePBWBasis_apply`. -/
noncomputable def relativePBWBasis :
    Basis ((ιA →₀ ℕ) × (ιB →₀ ℕ)) R U :=
  (adaptedBasis B hA bA bB).pbwBasis.reindex sumExponentEquiv.symm

/-- A relative PBW basis vector is an ordered complement monomial times a subalgebra monomial. -/
theorem relativePBWBasis_apply
    (α : ιA →₀ ℕ) (β : ιB →₀ ℕ) :
    relativePBWBasis B hA bA bB (α, β) =
      pbwMonomial R L (fun i ↦ (bA i : L)) (α.toMultiset.sort (· ≤ ·)) *
        UniversalEnvelopingAlgebra.map R B.incl (bB.pbwBasis β) := by
  -- The exponent vector of `(α, β)` is the sum of the two halves, pushed into `ιA ⊕ₗ ιB`.
  have hexp : (sumExponentEquiv (α, β)).toMultiset =
      α.toMultiset.map Sum.inlₗ + β.toMultiset.map Sum.inrₗ := by
    rw [sumExponentEquiv_apply, Finsupp.toMultiset_add, Finsupp.toMultiset_map,
      Finsupp.toMultiset_map]
  -- Every complement index precedes every index of `B`, so the sorted list splits in two.
  have hle : ∀ a ∈ α.toMultiset.map Sum.inlₗ, ∀ b ∈ β.toMultiset.map (Sum.inrₗ (α := ιA)),
      a ≤ b := by
    simp only [Multiset.mem_map]
    rintro _ ⟨i, -, rfl⟩ _ ⟨j, -, rfl⟩
    exact Sum.Lex.inl_le_inr i j
  have hsort : (sumExponentEquiv (α, β)).toMultiset.sort (· ≤ ·) =
      (α.toMultiset.sort (· ≤ ·)).map Sum.inlₗ ++ (β.toMultiset.sort (· ≤ ·)).map Sum.inrₗ := by
    rw [hexp, Multiset.sort_add _ hle,
      Multiset.map_sort Sum.inlₗ α.toMultiset (fun a b : ιA ↦ a ≤ b)
        (fun a b : ιA ⊕ₗ ιB ↦ a ≤ b) (fun _ _ _ _ ↦ Sum.Lex.inl_le_inl_iff.symm),
      Multiset.map_sort Sum.inrₗ β.toMultiset (fun a b : ιB ↦ a ≤ b)
        (fun a b : ιA ⊕ₗ ιB ↦ a ≤ b) (fun _ _ _ _ ↦ Sum.Lex.inr_le_inr_iff.symm)]
  -- The monomial of the concatenation is the product of the two monomials.
  rw [relativePBWBasis, Basis.reindex_apply, Equiv.symm_symm, Basis.pbwBasis_apply,
    Basis.pbwBasis_apply, map_pbwMonomial, hsort, pbwMonomial_append]
  simp only [pbwMonomial_def, List.map_map, Function.comp_def, adaptedBasis_inl, adaptedBasis_inr,
    LieSubalgebra.coe_incl]

end Adapted

section Subalgebras

variable (A B : LieSubalgebra R L)

/-- Multiply the images of two enveloping algebras inside the ambient enveloping algebra. -/
noncomputable def mulMap :
    UniversalEnvelopingAlgebra R A ⊗[R] UniversalEnvelopingAlgebra R B →ₗ[R] U :=
  (TensorProduct.lift (LinearMap.mul R U)).comp
    (TensorProduct.map (UniversalEnvelopingAlgebra.map R A.incl).toLinearMap
      (UniversalEnvelopingAlgebra.map R B.incl).toLinearMap)

/-- On pure tensors the multiplication map is multiplication in the ambient algebra. -/
@[simp]
theorem mulMap_tmul (a : UniversalEnvelopingAlgebra R A)
    (b : UniversalEnvelopingAlgebra R B) :
    mulMap A B (a ⊗ₜ b) =
      UniversalEnvelopingAlgebra.map R A.incl a * UniversalEnvelopingAlgebra.map R B.incl b := by
  simp [mulMap]

private theorem mulMap_bijective_of_basis
    (h : IsCompl (A : Submodule R L) (B : Submodule R L))
    {ιA : Type w₁} {ιB : Type w₂} [LinearOrder ιA] [LinearOrder ιB]
    (bA : Basis ιA R A) (bB : Basis ιB R B) : Function.Bijective (mulMap A B) := by
  let e := (bA.pbwBasis.tensorProduct bB.pbwBasis).equiv
    (relativePBWBasis B h bA bB) (Equiv.refl _)
  have he : e.toLinearMap = mulMap A B := by
    apply (bA.pbwBasis.tensorProduct bB.pbwBasis).ext
    rintro ⟨α, β⟩
    dsimp only [e]
    rw [LinearEquiv.coe_toLinearMap, Basis.equiv_apply, Equiv.refl_apply]
    simp only [relativePBWBasis_apply, Basis.tensorProduct_apply, mulMap_tmul,
      Basis.pbwBasis_apply, map_pbwMonomial, LieSubalgebra.coe_incl]
  exact he ▸ e.bijective

/-- Multiplication is bijective when two free Lie subalgebras complement each other as modules.
There are no characteristic or finite-dimensionality assumptions. -/
theorem mulMap_bijective (h : IsCompl (A : Submodule R L) (B : Submodule R L))
    [Module.Free R A] [Module.Free R B] : Function.Bijective (mulMap A B) := by
  let _ : LinearOrder (Module.Free.ChooseBasisIndex R A) := IsWellOrder.linearOrder WellOrderingRel
  let _ : LinearOrder (Module.Free.ChooseBasisIndex R B) := IsWellOrder.linearOrder WellOrderingRel
  exact mulMap_bijective_of_basis A B h (Module.Free.chooseBasis R A) (Module.Free.chooseBasis R B)

/-- The relative PBW decomposition: multiplication identifies the tensor product of the enveloping
algebras of complementary free Lie subalgebras with the ambient enveloping algebra. -/
noncomputable def mulEquiv (h : IsCompl (A : Submodule R L) (B : Submodule R L))
    [Module.Free R A] [Module.Free R B] :
    UniversalEnvelopingAlgebra R A ⊗[R] UniversalEnvelopingAlgebra R B ≃ₗ[R] U :=
  LinearEquiv.ofBijective (mulMap A B) (mulMap_bijective A B h)

/-- The relative PBW equivalence is normalized by multiplication of the two factors. -/
@[simp]
theorem mulEquiv_tmul (h : IsCompl (A : Submodule R L) (B : Submodule R L))
    [Module.Free R A] [Module.Free R B] (a : UniversalEnvelopingAlgebra R A)
    (b : UniversalEnvelopingAlgebra R B) :
    mulEquiv A B h (a ⊗ₜ b) =
      UniversalEnvelopingAlgebra.map R A.incl a * UniversalEnvelopingAlgebra.map R B.incl b :=
  mulMap_tmul A B a b

/-- The inverse relative PBW equivalence recovers the tensor factors of a product. -/
@[simp]
theorem mulEquiv_symm_mul (h : IsCompl (A : Submodule R L) (B : Submodule R L))
    [Module.Free R A] [Module.Free R B] (a : UniversalEnvelopingAlgebra R A)
    (b : UniversalEnvelopingAlgebra R B) :
    (mulEquiv A B h).symm
        (UniversalEnvelopingAlgebra.map R A.incl a * UniversalEnvelopingAlgebra.map R B.incl b) =
      a ⊗ₜ b := by
  rw [← mulEquiv_tmul A B h, LinearEquiv.symm_apply_apply]

end Subalgebras

end LieSubalgebra
