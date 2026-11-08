/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.KummerPolynomial
public import TauCeti.FieldTheory.FunctionField.Place.RatFunc.Basic
public import TauCeti.RingTheory.AdjoinRoot.Length
import TauCeti.RingTheory.AdjoinRoot.Basic
import TauCeti.Algebra.Polynomial.XPowSubC
import TauCeti.Algebra.Module.Equiv.Length
import TauCeti.RingTheory.Polynomial.Truncated.Basic

/-!
# The nonreduced fibre of an inseparable constant extension

Let `k` have characteristic `p`, let `a` not be a `p`-th power in `k`, and suppose
`α ^ p = a` in an extension field `K`. At the place `P` of `k(t)` defined by `t ^ p - a`,
the constant-extension fibre `K ⊗[k] κ(P)` is `K[T]/((T - α)^p)`.
It is a local Artinian ring of length `p`, with a nonzero nilpotent. Thus its local
multiplicity is `p`, not the multiplicity `1` of its reduced point. This agrees with
the ramification index and conorm computed in
`TauCeti.FieldTheory.FunctionField.ConstantExtension.PurelyInseparable`.

The residue field is the existing `Place.ResidueField`, not a replacement quotient.
Its polynomial presentation is transported using `adicOfIrreducibleResidueFieldEquiv`
and the base-change equivalence `AdjoinRoot.algebraTensorAlgEquiv`.

## References

* H. Stichtenoth, *Algebraic Function Fields and Codes*, Section III.6.
* Q. Liu, *Algebraic Geometry and Arithmetic Curves*, Section 7.1 (fibre multiplicities).
-/

public section

open Polynomial
open scoped TensorProduct

namespace TauCeti.Place

variable {k K : Type*} [Field k] [Field K] [Algebra k K]
    {p : ℕ} [Fact p.Prime] [CharP k p] {a : k} {α : K}

/-- The fibre at `t ^ p - a` after adjoining a `p`-th root `α` of `a` is the
thickened point `K[T]/((T - α)^p)`, as a `K`-algebra. -/
noncomputable def inseparableFibreEquiv (ha : ∀ c : k, c ^ p ≠ a)
    (hα : α ^ p = algebraMap k K a) :
    K ⊗[k] (adicOfIrreducible (irreducible_X_pow_sub_C_of_prime Fact.out ha)).ResidueField ≃ₐ[K]
      AdjoinRoot ((X - C α) ^ p) := by
  let e := adicOfIrreducibleResidueFieldEquiv
    (irreducible_X_pow_sub_C_of_prime Fact.out ha)
  -- Repackage the quotient presentation on the `AdjoinRoot` type synonym, with its
  -- own inherited algebra instances, before applying tensor-product functoriality.
  let e' : AdjoinRoot (X ^ p - C a) ≃ₐ[k]
      (adicOfIrreducible (irreducible_X_pow_sub_C_of_prime Fact.out ha)).ResidueField :=
    { toFun := e
      invFun := e.symm
      left_inv := e.left_inv
      right_inv := e.right_inv
      map_mul' := e.map_mul
      map_add' := e.map_add
      commutes' := e.commutes }
  exact (Algebra.TensorProduct.congr (AlgEquiv.refl (R := K) (A₁ := K)) e'.symm).trans
    ((AdjoinRoot.algebraTensorAlgEquiv K (X ^ p - C a)).trans
      (AdjoinRoot.algEquivOfEq K _ _ (by
        have := expChar_of_injective_algebraMap (algebraMap k K).injective p
        exact map_X_pow_sub_C_eq_X_sub_C_pow p hα)))

/-- On the residue of the polynomial coordinate, the fibre presentation sends `t` to `T`. -/
@[simp]
theorem inseparableFibreEquiv_tmul_root (ha : ∀ c : k, c ^ p ≠ a)
    (hα : α ^ p = algebraMap k K a) :
    inseparableFibreEquiv ha hα
      (1 ⊗ₜ[k] adicOfIrreducibleResidueFieldEquiv
        (irreducible_X_pow_sub_C_of_prime Fact.out ha) (AdjoinRoot.root (X ^ p - C a))) =
      AdjoinRoot.root ((X - C α) ^ p) := by
  unfold inseparableFibreEquiv
  extract_lets e e'
  -- `e'` is the residue presentation repackaged on `AdjoinRoot`.
  have he : e' (AdjoinRoot.root (X ^ p - C a)) = e (AdjoinRoot.root (X ^ p - C a)) := rfl
  rw [← he]
  simp [AlgEquiv.trans_apply, AdjoinRoot.algebraTensorAlgEquiv_one_tmul_root,
    AdjoinRoot.algEquivOfEq_root]

/-- The inseparable constant-extension fibre is local, despite being nonreduced. -/
theorem isLocalRing_inseparableFibre (ha : ∀ c : k, c ^ p ≠ a)
    (hα : α ^ p = algebraMap k K a) :
    IsLocalRing
      (K ⊗[k] (adicOfIrreducible (irreducible_X_pow_sub_C_of_prime Fact.out ha)).ResidueField) := by
  have := isLocalRing_adjoinRoot_X_sub_C_pow α p
  exact (inseparableFibreEquiv ha hα).toRingEquiv.symm.isLocalRing

/-- The local length of the actual residue-field tensor product is `p`.
In particular one must not replace this fibre by its reduced field factor. -/
theorem length_inseparableFibre (ha : ∀ c : k, c ^ p ≠ a)
    (hα : α ^ p = algebraMap k K a) :
    let B := K ⊗[k]
      (adicOfIrreducible (irreducible_X_pow_sub_C_of_prime Fact.out ha)).ResidueField
    Module.length B B = p := by
  dsimp only
  rw [(inseparableFibreEquiv ha hα).toRingEquiv.length_self_eq,
    AdjoinRoot.length_pow (irreducible_X_sub_C α)]

/-- The inseparable fibre is Artinian; its length is finite even though it is nonreduced. -/
theorem isArtinianRing_inseparableFibre (ha : ∀ c : k, c ^ p ≠ a)
    (hα : α ^ p = algebraMap k K a) :
    IsArtinianRing
      (K ⊗[k] (adicOfIrreducible (irreducible_X_pow_sub_C_of_prime Fact.out ha)).ResidueField) := by
  have h := length_inseparableFibre ha hα
  have : IsFiniteLength
      (K ⊗[k] (adicOfIrreducible (irreducible_X_pow_sub_C_of_prime Fact.out ha)).ResidueField)
      (K ⊗[k] (adicOfIrreducible (irreducible_X_pow_sub_C_of_prime Fact.out ha)).ResidueField) :=
    Module.length_ne_top_iff.mp (by rw [h]; exact ENat.natCast_ne_top p)
  exact (isFiniteLength_iff_isNoetherian_isArtinian.mp this).2

/-- The thickened fibre has a nonzero element whose `p`-th power vanishes. -/
theorem exists_ne_zero_pow_eq_zero_inseparableFibre (ha : ∀ c : k, c ^ p ≠ a)
    (hα : α ^ p = algebraMap k K a) :
    ∃ z : K ⊗[k]
      (adicOfIrreducible (irreducible_X_pow_sub_C_of_prime Fact.out ha)).ResidueField,
      z ≠ 0 ∧ z ^ p = 0 := by
  let e := inseparableFibreEquiv ha hα
  let q : K[X] := X - C α
  let z : AdjoinRoot (q ^ p) := AdjoinRoot.mk (q ^ p) q
  have hz : z ≠ 0 := by
    apply AdjoinRoot.mk_ne_zero_of_natDegree_lt ((monic_X_sub_C α).pow p)
      (X_sub_C_ne_zero α)
    simpa [q, natDegree_pow] using (Fact.out : p.Prime).one_lt
  refine ⟨e.symm z, (map_ne_zero_iff e.symm e.symm.injective).mpr hz, ?_⟩
  apply e.injective
  simp only [map_pow, AlgEquiv.apply_symm_apply, map_zero]
  exact (map_pow (AdjoinRoot.mk (q ^ p)) q p).symm.trans AdjoinRoot.mk_self

end TauCeti.Place
