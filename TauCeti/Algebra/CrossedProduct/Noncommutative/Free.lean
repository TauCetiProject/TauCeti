/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.CrossedProduct.Noncommutative.Restriction
public import TauCeti.GroupTheory.Coset.Basic
public import Mathlib.LinearAlgebra.FreeModule.Finite.Basic
import Mathlib.Data.Finsupp.ToDFinsupp
import Mathlib.Algebra.Module.Opposite
import Mathlib.Algebra.Ring.AddAut

/-!
# Crossed products as right modules over subgroup crossed products

For a subgroup `H` of the index group of a crossed system `c`, its crossed product is a
free right module over the restricted crossed product. A basis is given by `[t]`, with
`t` chosen in each left coset of `H`. Right modules are expressed as left modules over
the opposite ring; install `rightSubgroupModule c H` locally to use this action.
No centrality of the coefficients or finiteness of the group is needed.

This decomposition supplies the algebraic finiteness input for extension of scalars
from a subgroup crossed product. The coordinate change retains both the coefficient
automorphism and the unit factor in `[t](d[h]) = σ_t(d)a(t,h)[th]`.

The construction uses Mathlib's `Subgroup.groupEquivQuotientProdSubgroup` and finite-support
coordinate equivalences, and the actual subgroup algebra map `comapHom`. It extends the coset
regrouping argument of `TauCeti.MonoidAlgebra.basisCosets` to twisted noncommutative coefficients.

## References

* G. Karpilovsky, *Projective Representations of Finite Groups* (1985).
-/

public section

namespace TauCeti.CrossedSystem.Algebra

open MulOpposite

variable {k D G : Type*} [CommSemiring k] [Semiring D] [_root_.Algebra k D]
  [Group G] (c : CrossedSystem k D G) (H : Subgroup G)

/-- Right multiplication through the subgroup crossed-product inclusion, expressed as
a left module over the opposite of the restricted crossed product. -/
noncomputable abbrev rightSubgroupModule : Module (Algebra (c.comap H.subtype))ᵐᵒᵖ (Algebra c) :=
  Module.compHom _ (comapHom c H.subtype).toRingHom.op

attribute [local instance] rightSubgroupModule

/-- The opposite scalar acts by right multiplication by its image in the ambient algebra. -/
theorem rightSubgroupModule_smul (a : (Algebra (c.comap H.subtype))ᵐᵒᵖ) (x : Algebra c) :
    a • x = x * comapHom c H.subtype (unop a) := (rfl)

private noncomputable def coefficientTwist (q : G ⧸ H) (h : H) : D ≃+ D :=
  (c.action q.out).toAddEquiv.trans (AddAut.mulRight (c.factor q.out h))

private noncomputable def twistCoordinates : ((G ⧸ H) × H →₀ D) ≃+
    ((G ⧸ H) × H →₀ D) := by
  classical
  exact finsuppAddEquivDFinsupp.trans
    ((DFinsupp.mapRange.addEquiv fun p => coefficientTwist c H p.1 p.2).trans
      finsuppAddEquivDFinsupp.symm)

private theorem twistCoordinates_single (q : G ⧸ H) (h : H) (d : D) :
    twistCoordinates c H (Finsupp.single (q, h) d) =
      Finsupp.single (q, h) (c.action q.out d * c.factor q.out h) := by
  classical
  simp [twistCoordinates, coefficientTwist, DFinsupp.mapRange_single]

private noncomputable def cosetAddEquiv :
    (G ⧸ H →₀ (Algebra (c.comap H.subtype))ᵐᵒᵖ) ≃+ Algebra c :=
  (Finsupp.mapRange.addEquiv
      (opAddEquiv.symm.trans (basis (c.comap H.subtype)).repr.toAddEquiv)).trans
    (Finsupp.curryAddEquiv.symm.trans
      ((twistCoordinates c H).trans
        ((Finsupp.domCongr H.groupEquivQuotientProdSubgroup.symm).trans
          (basis c).repr.toAddEquiv.symm)))

private theorem cosetAddEquiv_single_smul_basis (q : G ⧸ H) (h : H) (d : D) :
    cosetAddEquiv c H (Finsupp.single q (op (d • basis (c.comap H.subtype) h))) =
      (c.action q.out d * c.factor q.out h) • basis c (q.out * h) := by
  classical
  apply (basis c).repr.injective
  simp [cosetAddEquiv, Finsupp.domCongr, twistCoordinates_single,
    Subgroup.groupEquivQuotientProdSubgroup_symm_apply, Finsupp.smul_single]

private theorem cosetAddEquiv_single (q : G ⧸ H)
    (a : (Algebra (c.comap H.subtype))ᵐᵒᵖ) :
    cosetAddEquiv c H (Finsupp.single q a) = basis c q.out * comapHom c H.subtype (unop a) := by
  have ha : a = op (unop a) := rfl
  rw [ha]
  induction unop a using induction_on with
  | zero => simp
  | add a b ha hb => simp [Finsupp.single_add, ha, hb, mul_add]
  | smul_basis h d =>
    rw [cosetAddEquiv_single_smul_basis]
    simp only [unop_op, comapHom_smul, comapHom_basis]
    rw [← one_smul D (basis c q.out), smul_basis_mul_smul_basis, one_mul]
    rfl

private theorem cosetAddEquiv_smul (a : (Algebra (c.comap H.subtype))ᵐᵒᵖ)
    (f : G ⧸ H →₀ (Algebra (c.comap H.subtype))ᵐᵒᵖ) :
    cosetAddEquiv c H (a • f) = a • cosetAddEquiv c H f := by
  induction f using Finsupp.induction_linear with
  | zero => simp
  | add f g hf hg => simp [smul_add, hf, hg]
  | single q b =>
    simp [Finsupp.smul_single, cosetAddEquiv_single, rightSubgroupModule_smul,
      smul_eq_mul, mul_assoc]

private noncomputable def cosetLinearEquiv :
    (G ⧸ H →₀ (Algebra (c.comap H.subtype))ᵐᵒᵖ) ≃ₗ[(Algebra (c.comap H.subtype))ᵐᵒᵖ]
      Algebra c :=
  { cosetAddEquiv c H with map_smul' := cosetAddEquiv_smul c H }

/-- The right subgroup basis consists of the crossed-product basis elements at the chosen
representatives of the left cosets. It is valid for arbitrary index and noncommutative
coefficients. -/
noncomputable def rightSubgroupBasis :
    Module.Basis (G ⧸ H) (Algebra (c.comap H.subtype))ᵐᵒᵖ (Algebra c) :=
  .ofRepr (cosetLinearEquiv c H).symm

/-- The vector at a left coset is `[t]` for its chosen representative `t`. -/
@[simp]
theorem rightSubgroupBasis_apply (q : G ⧸ H) :
    rightSubgroupBasis c H q = basis c q.out := by
  simp [rightSubgroupBasis, Module.Basis.coe_ofRepr, cosetLinearEquiv,
    cosetAddEquiv_single]

/-- A chosen coset representative has the corresponding unit coordinate. -/
@[simp]
theorem rightSubgroupBasis_repr_basis (q : G ⧸ H) :
    (rightSubgroupBasis c H).repr (basis c q.out) = Finsupp.single q 1 := by
  rw [← rightSubgroupBasis_apply c H q, Module.Basis.repr_self]

/-- Right subgroup coordinates of `[t]a`, with `t` the chosen representative, are supported
at its coset and have value `a`. -/
@[simp]
theorem rightSubgroupBasis_repr_mul (q : G ⧸ H) (a : Algebra (c.comap H.subtype)) :
    (rightSubgroupBasis c H).repr (basis c q.out * comapHom c H.subtype a) =
      Finsupp.single q (op a) := by
  have hs := rightSubgroupModule_smul c H (op a) (rightSubgroupBasis c H q)
  rw [unop_op, rightSubgroupBasis_apply] at hs
  rw [← hs, map_smul]
  rw [← rightSubgroupBasis_apply c H q]
  simp only [Module.Basis.repr_self, Finsupp.smul_single, smul_eq_mul, mul_one]

/-- The right subgroup coordinates of a coefficient multiple of a basis element.
The inverse coefficient automorphism and inverse unit factor undo the crossed multiplication. -/
@[simp]
theorem rightSubgroupBasis_repr_smul_basis (q : G ⧸ H) (h : H) (d : D) :
    (rightSubgroupBasis c H).repr (d • basis c (q.out * h)) =
      Finsupp.single q (op ((c.action q.out).symm (d * ↑(c.factor q.out h)⁻¹) •
        basis (c.comap H.subtype) h)) := by
  have hmul : basis c q.out * comapHom c H.subtype
      ((c.action q.out).symm (d * ↑(c.factor q.out h)⁻¹) •
        basis (c.comap H.subtype) h) = d • basis c (q.out * h) := by
    rw [comapHom_smul, comapHom_basis, ← one_smul D (basis c q.out),
      smul_basis_mul_smul_basis]
    simp [mul_assoc]
  rw [← hmul, rightSubgroupBasis_repr_mul]

/-- The ambient crossed product is free as a right module over every subgroup crossed product. -/
instance moduleFree_rightSubgroup :
    Module.Free (Algebra (c.comap H.subtype))ᵐᵒᵖ (Algebra c) :=
  Module.Free.of_basis (rightSubgroupBasis c H)

/-- Finite subgroup index makes the ambient crossed product finite as a right module over
the restricted crossed product; the ambient group itself may be infinite. -/
instance moduleFinite_rightSubgroup [H.FiniteIndex] :
    Module.Finite (Algebra (c.comap H.subtype))ᵐᵒᵖ (Algebra c) :=
  Module.Finite.of_basis (rightSubgroupBasis c H)

end TauCeti.CrossedSystem.Algebra
