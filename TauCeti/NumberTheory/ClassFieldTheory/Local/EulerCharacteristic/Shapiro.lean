/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Field.ZMod
public import Mathlib.Topology.Algebra.OpenSubgroup
public import TauCeti.FieldTheory.Galois.AbsoluteGaloisGroup.Basic
public import TauCeti.RepresentationTheory.Induction.FiniteDimensional.Basic

/-!
# The fixed field in the finite-quotient Shapiro argument

Let `V` be an open normal subgroup of the absolute Galois group `G_F` and let `C` be a subgroup of
the finite quotient `G_F / V`. The subgroup of `G_F` relevant to Shapiro's lemma is the preimage
of `C`. This file constructs its fixed field `shapiroField F V C` and proves

```text
[shapiroField F V C : F] = [G_F / V : C].
```

Consequently, induction from `C` multiplies both dimension and the exponent in the cardinality of
a finite-vector-space coefficient module by this field degree. The degree formula in a scalar
tower gives the arithmetic factor used in the local Euler-characteristic argument.

The cohomological comparison itself is
`ContinuousCohomology.indInflationShapiroIso`; this file supplies its fixed-field and coefficient-
size interpretation.

## Main definitions

* `shapiroOpenSubgroup`: the preimage of `C` in `G_F`.
* `shapiroField`: the fixed field of that preimage in an algebraic closure of `F`.

## Main results

* `finrank_shapiroField`: the fixed-field degree is the index of `C`.
* `finrank_ind_eq_finrank_shapiroField_mul`: induction scales coefficient dimension by that degree.
* `natCard_ind_eq_pow_finrank_shapiroField_mul`: the corresponding coefficient-cardinality
  formula over a prime field.
* `finrank_base_shapiroField`: the degree formula in a finite scalar tower.
* `finrank_base_mul_finrank_ind_eq_shapiroField`: the equality of arithmetic exponents on the two
  sides of Shapiro's lemma.

## References

* J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, §VII.3,
  proof of (7.3.1).
* J. S. Milne, *Arithmetic Duality Theorems*, I, proof of Theorem 2.8.
-/

public section

namespace TauCeti.ClassFieldTheory

universe u v w

variable (F : Type u) [Field F]
  (V : OpenNormalSubgroup (Field.absoluteGaloisGroup F))
  (C : Subgroup (Field.absoluteGaloisGroup F ⧸ V.toSubgroup))

/-- The open subgroup of `G_F` obtained as the preimage of `C ≤ G_F / V`. -/
noncomputable def shapiroOpenSubgroup : OpenSubgroup (Field.absoluteGaloisGroup F) :=
  (⟨C, by exact isOpen_discrete _⟩ : OpenSubgroup _).comap
    (QuotientGroup.mk' V.toSubgroup)
    QuotientGroup.continuous_mk

@[simp]
theorem shapiroOpenSubgroup_toSubgroup :
    (shapiroOpenSubgroup F V C).toSubgroup =
      C.comap (QuotientGroup.mk' V.toSubgroup) :=
  OpenSubgroup.toSubgroup_comap _ _ _

/-- The fixed field in an algebraic closure of the subgroup used by finite-quotient Shapiro. -/
noncomputable def shapiroField : IntermediateField F (AlgebraicClosure F) :=
  IntermediateField.fixedField (shapiroOpenSubgroup F V C).toSubgroup

/-- `shapiroField F V C` is the fixed field of `shapiroOpenSubgroup F V C`. -/
theorem shapiroField_def :
    shapiroField F V C = IntermediateField.fixedField (shapiroOpenSubgroup F V C).toSubgroup := by
  rw [shapiroField]

/-- An element lies in the Shapiro fixed field iff it is fixed by every element of `G_F` whose
image in `G_F / V` lies in `C`. -/
@[simp]
theorem mem_shapiroField {x : AlgebraicClosure F} :
    x ∈ shapiroField F V C ↔
      ∀ σ : AlgebraicClosure F ≃ₐ[F] AlgebraicClosure F,
        (QuotientGroup.mk (σ : Field.absoluteGaloisGroup F) :
          Field.absoluteGaloisGroup F ⧸ V.toSubgroup) ∈ C → σ x = x := by
  rw [shapiroField_def]
  -- `Gal(AlgebraicClosure F/F)` and `G_F` carry different (defeq) group instances, so the
  -- membership condition cannot be rewritten by `simp`; it holds by `Subgroup.mem_comap`.
  exact IntermediateField.mem_fixedField_iff _ x

/-- The index of the preimage of `C` in `G_F` is the index of `C` in the finite quotient. -/
theorem shapiroOpenSubgroup_index :
    (shapiroOpenSubgroup F V C).toSubgroup.index = C.index := by
  rw [shapiroOpenSubgroup_toSubgroup]
  exact C.index_comap_of_surjective (QuotientGroup.mk'_surjective V.toSubgroup)

/-- The degree of the Shapiro fixed field over `F` is the index of `C` in `G_F / V`. -/
theorem finrank_shapiroField [IsGalois F (AlgebraicClosure F)] :
    Module.finrank F (shapiroField F V C) = C.index := by
  rw [IntermediateField.finrank_eq_fixingSubgroup_index, shapiroField_def]
  have hfix : (IntermediateField.fixedField
      (shapiroOpenSubgroup F V C).toSubgroup).fixingSubgroup =
        (shapiroOpenSubgroup F V C).toSubgroup := by
    exact InfiniteGalois.fixingSubgroup_fixedField
      (⟨(shapiroOpenSubgroup F V C).toSubgroup,
        (shapiroOpenSubgroup F V C).isClosed⟩ :
          ClosedSubgroup (AlgebraicClosure F ≃ₐ[F] AlgebraicClosure F))
  rw [hfix]
  exact shapiroOpenSubgroup_index F V C

variable {R : Type v} [Field R]

/-- Induction from `C` scales dimension by the degree of the associated fixed field. -/
theorem finrank_ind_eq_finrank_shapiroField_mul [IsGalois F (AlgebraicClosure F)]
    (B : Rep.{max u v} R C) [FiniteDimensional R B] :
    Module.finrank R (Rep.ind C.subtype B) =
      Module.finrank F (shapiroField F V C) * Module.finrank R B := by
  rw [Rep.finrank_ind, finrank_shapiroField]

/-- Over a prime field, the cardinality of an induced coefficient module is the prime raised to
the fixed-field degree times the dimension of the original module. -/
theorem natCard_ind_eq_pow_finrank_shapiroField_mul (p : ℕ) [Fact p.Prime]
    [IsGalois F (AlgebraicClosure F)] (B : Rep.{u} (ZMod p) C)
    [FiniteDimensional (ZMod p) B] :
    Nat.card (Rep.ind C.subtype B) =
      p ^ (Module.finrank F (shapiroField F V C) * Module.finrank (ZMod p) B) := by
  rw [Module.natCard_eq_pow_finrank (K := ZMod p)
      (V := (Rep.ind C.subtype B).V), Nat.card_zmod,
    finrank_ind_eq_finrank_shapiroField_mul]

variable {k : Type w} [Field k]

/-- The Shapiro fixed-field degree satisfies the tower formula over any scalar subfield. -/
theorem finrank_base_shapiroField [Algebra k F] :
    Module.finrank k (shapiroField F V C) =
      Module.finrank F (shapiroField F V C) * Module.finrank k F := by
  rw [← Module.finrank_mul_finrank k F (shapiroField F V C), mul_comm]

/-- The arithmetic exponents on the two sides of finite-quotient Shapiro agree: induction scales
coefficient dimension by the same index by which passage to the fixed field scales base degree. -/
theorem finrank_base_mul_finrank_ind_eq_shapiroField
    [IsGalois F (AlgebraicClosure F)] [Algebra k F]
    (B : Rep.{max u v} R C) [FiniteDimensional R B] :
    Module.finrank k F * Module.finrank R (Rep.ind C.subtype B) =
      Module.finrank k (shapiroField F V C) * Module.finrank R B := by
  rw [finrank_ind_eq_finrank_shapiroField_mul,
    finrank_base_shapiroField (k := k) F V C]
  ac_rfl

end TauCeti.ClassFieldTheory
