/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.FieldTheory.Galois.Quotient

/-!
# Quotients of the absolute Galois group

`TauCeti.quotientFixingSubgroupEquiv` identifies the quotient of the Galois group of a normal
extension `E/F` by the fixing subgroup of an intermediate field `M` normal over `F` with the Galois
group `Gal(M/F)`, as topological groups. This file reads that comparison at
`E = AlgebraicClosure K`, where the quotient is a quotient of `Field.absoluteGaloisGroup K`:

```
Field.absoluteGaloisGroup K ⧸ M.fixingSubgroup ≃ₜ* Gal(M/K).
```

The comparison is restated here rather than left to the reading at `Gal(AlgebraicClosure K/K)`:
`Field.absoluteGaloisGroup K` is a definition carrying its own derived group and topology
instances, so a statement about `Gal(AlgebraicClosure K/K)` is not available to `rw` at a quotient
of `Field.absoluteGaloisGroup K`. The same reason is recorded for the transported instances in
`TauCeti.FieldTheory.Galois.AbsoluteGaloisGroup.Basic`.

## Main results

* `TauCeti.absoluteGaloisGroupQuotientEquiv`: the isomorphism of topological groups comparing a
  quotient of `Field.absoluteGaloisGroup K` with the Galois group of a normal subextension of an
  algebraic closure of `K`.
* `TauCeti.absoluteGaloisGroupQuotientEquivOfEq`: the same isomorphism for the quotient by a
  subgroup of `Field.absoluteGaloisGroup K` that is equal to the fixing subgroup of `M`.
-/

public section

noncomputable section

namespace TauCeti

variable (K : Type*) [Field K] (M : IntermediateField K (AlgebraicClosure K)) [Normal K M]

/-- **The Galois group of a normal subextension of an algebraic closure is a quotient of the
absolute Galois group**: `Field.absoluteGaloisGroup K ⧸ M.fixingSubgroup ≃ₜ* Gal(M/K)`.

This is `quotientFixingSubgroupEquiv` read at `E = AlgebraicClosure K`. -/
def absoluteGaloisGroupQuotientEquiv :
    Field.absoluteGaloisGroup K ⧸ M.fixingSubgroup ≃ₜ* Gal(↥M/K) :=
  quotientFixingSubgroupEquiv K (AlgebraicClosure K) M

variable {K M}

/-- The comparison isomorphism sends the class of `σ` to its restriction to `M`, whose value at a
point of `M` is `σ` evaluated there, by `AlgEquiv.restrictNormalHom_apply`. -/
@[simp]
theorem absoluteGaloisGroupQuotientEquiv_mk (σ : Gal(AlgebraicClosure K/K)) :
    absoluteGaloisGroupQuotientEquiv K M (σ : Field.absoluteGaloisGroup K ⧸ M.fixingSubgroup) =
      AlgEquiv.restrictNormalHom M σ :=
  quotientFixingSubgroupEquiv_mk σ

/-- The inverse of the comparison isomorphism sends the restriction of `σ` back to the class of
`σ`; with `AlgEquiv.restrictNormalHom_surjective` this computes it on every element. -/
@[simp]
theorem absoluteGaloisGroupQuotientEquiv_symm_restrictNormalHom (σ : Gal(AlgebraicClosure K/K)) :
    (absoluteGaloisGroupQuotientEquiv K M).symm (AlgEquiv.restrictNormalHom M σ) =
      (σ : Field.absoluteGaloisGroup K ⧸ M.fixingSubgroup) :=
  quotientFixingSubgroupEquiv_symm_restrictNormalHom σ

variable {H : Subgroup (Field.absoluteGaloisGroup K)} [H.Normal]

/-- The comparison isomorphism `absoluteGaloisGroupQuotientEquiv` for the quotient by a subgroup
`H` of `Field.absoluteGaloisGroup K` equal to `M.fixingSubgroup`:
`Field.absoluteGaloisGroup K ⧸ H ≃ₜ* Gal(M/K)`. -/
def absoluteGaloisGroupQuotientEquivOfEq (h : H = M.fixingSubgroup) :
    Field.absoluteGaloisGroup K ⧸ H ≃ₜ* Gal(↥M/K) :=
  -- Specify both carriers: the fixing subgroup uses the automorphism group instances, while the
  -- source quotient uses the derived absolute Galois group instances.
  ((show Field.absoluteGaloisGroup K ≃ₜ* Gal(AlgebraicClosure K/K) from
      ContinuousMulEquiv.refl _).quotientCongr H M.fixingSubgroup
    (by
      -- `change` exposes the identity homomorphism underlying `ContinuousMulEquiv.refl`.
      change H.map (MonoidHom.id _) = _
      rw [Subgroup.map_id]
      exact h)).trans
    (absoluteGaloisGroupQuotientEquiv K M)

/-- The comparison isomorphism `absoluteGaloisGroupQuotientEquivOfEq` sends the class of `σ` to
its restriction to `M`. -/
@[simp]
theorem absoluteGaloisGroupQuotientEquivOfEq_mk (h : H = M.fixingSubgroup)
    (σ : Field.absoluteGaloisGroup K) :
    absoluteGaloisGroupQuotientEquivOfEq h (σ : Field.absoluteGaloisGroup K ⧸ H) =
      AlgEquiv.restrictNormalHom M σ := by
  -- The same carrier annotation as in `absoluteGaloisGroupQuotientEquivOfEq`, so that
  -- `quotientCongr_mk` matches the definition.
  rw [absoluteGaloisGroupQuotientEquivOfEq, ContinuousMulEquiv.trans_apply,
    ContinuousMulEquiv.quotientCongr_mk
      (show Field.absoluteGaloisGroup K ≃ₜ* Gal(AlgebraicClosure K/K) from
        ContinuousMulEquiv.refl _)]
  exact absoluteGaloisGroupQuotientEquiv_mk σ

/-- The inverse of `absoluteGaloisGroupQuotientEquivOfEq` sends the restriction of `σ` to `M`
back to the class of `σ`; with `AlgEquiv.restrictNormalHom_surjective` this computes it on every
element. -/
@[simp]
theorem absoluteGaloisGroupQuotientEquivOfEq_symm_restrictNormalHom (h : H = M.fixingSubgroup)
    (σ : Field.absoluteGaloisGroup K) :
    (absoluteGaloisGroupQuotientEquivOfEq h).symm (AlgEquiv.restrictNormalHom M σ) =
      (σ : Field.absoluteGaloisGroup K ⧸ H) :=
  (absoluteGaloisGroupQuotientEquivOfEq h).symm_apply_eq.2
    (absoluteGaloisGroupQuotientEquivOfEq_mk h σ).symm

end TauCeti
