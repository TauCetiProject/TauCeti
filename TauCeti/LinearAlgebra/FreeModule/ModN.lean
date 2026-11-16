/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.FreeModule.ModN

/-!
# Coordinates and product equivalences for `G / nG`

For a `ℤ`-basis `b` of a free `ℤ`-module `G` and `n ≠ 0`, Mathlib's `ModN.basis b` is the basis of
`ModN G n = G / nG` over `ℤ / n` formed by the classes of the vectors of `b`. This file records
that the coordinates of the class of `v` in this basis are the coordinates of `v` in `b`, reduced
modulo `n`, and shows that `ModN · n` commutes `ZMod n`-linearly with binary and arbitrary indexed
products of additive commutative groups.

## Main definitions and statements

* `ModN.basis_repr_mkQ`, `ModN.basis_repr_mk`: `(ModN.basis b).repr [v] i = (b.repr v i : ℤ / n)`.
* `ModN.prodLinearEquiv`: `ModN (G × H) n ≃ₗ[ZMod n] ModN G n × ModN H n`.
* `ModN.piLinearEquiv`: `ModN (∀ i, G i) n ≃ₗ[ZMod n] ∀ i, ModN (G i) n`.
-/

@[expose] public section

open Module

namespace ModN

variable {G ι : Type*} [AddCommGroup G] {n : ℕ} [NeZero n]

/-- The coordinates of the class of `v` in `ModN.basis b` are the coordinates of `v` in `b`,
reduced modulo `n`. -/
@[simp]
theorem basis_repr_mkQ (b : Basis ι ℤ G) (v : G) (i : ι) :
    (basis b).repr (mkQ n v) i = (b.repr v i : ZMod n) := by
  -- Both sides are additive in `v` and agree on the vectors of `b`, by `basis_apply_eq_mkQ`.
  let f : G →+ ZMod n :=
    (Finsupp.applyAddHom i).comp ((basis b).repr.toAddMonoidHom.comp (mkQ n))
  let g : G →+ ZMod n :=
    (Int.castAddHom _).comp ((Finsupp.applyAddHom i).comp b.repr.toAddMonoidHom)
  refine DFunLike.congr_fun (AddMonoidHom.toIntLinearMap_injective
    (b.ext (f₁ := f.toIntLinearMap) (f₂ := g.toIntLinearMap) fun j ↦ ?_)) v
  obtain rfl | hji := eq_or_ne j i <;> simp [f, g, ← basis_apply_eq_mkQ, *]

/-- The coordinates of the class of `v` in `ModN.basis b` are the coordinates of `v` in `b`,
reduced modulo `n`: the form of `ModN.basis_repr_mkQ` for `Submodule.Quotient.mk`. -/
@[simp]
theorem basis_repr_mk (b : Basis ι ℤ G) (v : G) (i : ι) :
    (basis b).repr (Submodule.Quotient.mk v : ModN G n) i = (b.repr v i : ZMod n) :=
  basis_repr_mkQ b v i

end ModN

end

public section

namespace ModN

/-- `ModN.mkQ n` sends `x` to its quotient class `Submodule.Quotient.mk x`. -/
theorem mkQ_apply {G : Type*} [AddCommGroup G] (n : ℕ) (x : G) :
    mkQ n x = (Submodule.Quotient.mk x : ModN G n) :=
  Submodule.mkQ_apply _ x

/-- The quotient map `ModN.mkQ n : G →+ ModN G n` is surjective. -/
theorem mkQ_surjective {G : Type*} [AddCommGroup G] (n : ℕ) :
    Function.Surjective (mkQ (G := G) n) :=
  Submodule.mkQ_surjective _

private theorem range_lsmul_toAddSubgroup_eq_range_nsmul (G : Type*) [AddCommGroup G] (n : ℕ) :
    (LinearMap.range (LinearMap.lsmul ℤ G (n : ℤ))).toAddSubgroup =
      (nsmulAddMonoidHom (α := G) n).range := by
  ext x
  simp [natCast_zsmul]

private noncomputable def bridgeModRangeNSMul (G : Type*) [AddCommGroup G] (n : ℕ) :
    ModN G n ≃+ G ⧸ (nsmulAddMonoidHom (α := G) n).range :=
  QuotientAddGroup.quotientAddEquivOfEq (range_lsmul_toAddSubgroup_eq_range_nsmul G n)

private theorem bridgeModRangeNSMul_mk (G : Type*) [AddCommGroup G] (n : ℕ) (x : G) :
    bridgeModRangeNSMul G n (mkQ n x) = (x : G ⧸ (nsmulAddMonoidHom (α := G) n).range) := by
  rw [mkQ_apply]
  exact QuotientAddGroup.quotientAddEquivOfEq_mk (range_lsmul_toAddSubgroup_eq_range_nsmul G n) x

private theorem bridgeModRangeNSMul_symm_mk (G : Type*) [AddCommGroup G] (n : ℕ) (x : G) :
    (bridgeModRangeNSMul G n).symm (x : G ⧸ (nsmulAddMonoidHom (α := G) n).range) = mkQ n x := by
  rw [AddEquiv.symm_apply_eq, bridgeModRangeNSMul_mk]

private theorem range_nsmul_prod_eq (G H : Type*) [AddCommGroup G] [AddCommGroup H] (n : ℕ) :
    (nsmulAddMonoidHom (α := G × H) n).range =
      (nsmulAddMonoidHom (α := G) n).range.prod (nsmulAddMonoidHom (α := H) n).range := by
  ext ⟨a, b⟩
  simp [AddSubgroup.mem_prod, Prod.exists, exists_and_left, exists_and_right]

private noncomputable def prodAddEquiv (G H : Type*) [AddCommGroup G] [AddCommGroup H] (n : ℕ) :
    ModN (G × H) n ≃+ ModN G n × ModN H n :=
  (bridgeModRangeNSMul (G × H) n).trans <|
    (QuotientAddGroup.quotientAddEquivOfEq (range_nsmul_prod_eq G H n)).trans <|
      (QuotientAddGroup.prodAddEquiv _ _).trans
        ((bridgeModRangeNSMul G n).symm.prodCongr (bridgeModRangeNSMul H n).symm)

/-- `ModN · n` distributes `ZMod n`-linearly over binary products of additive commutative groups. -/
noncomputable def prodLinearEquiv (G H : Type*) [AddCommGroup G] [AddCommGroup H] (n : ℕ) :
    ModN (G × H) n ≃ₗ[ZMod n] ModN G n × ModN H n :=
  { prodAddEquiv G H n with
    map_smul' := fun c x ↦ ZMod.map_smul (prodAddEquiv G H n) c x }

/-- `ModN.prodLinearEquiv` sends the class of `x` to `(mkQ n x.1, mkQ n x.2)`. -/
@[simp]
theorem prodLinearEquiv_mkQ (G H : Type*) [AddCommGroup G] [AddCommGroup H] (n : ℕ) (x : G × H) :
    prodLinearEquiv G H n (mkQ n x) = (mkQ n x.1, mkQ n x.2) := by
  change prodAddEquiv G H n (mkQ n x) = _
  rw [prodAddEquiv, AddEquiv.trans_apply, AddEquiv.trans_apply, AddEquiv.trans_apply,
    bridgeModRangeNSMul_mk, QuotientAddGroup.quotientAddEquivOfEq_mk,
    QuotientAddGroup.prodAddEquiv_apply]
  simp only [Quotient.liftOn'_mk'', AddEquiv.prodCongr, AddEquiv.coe_mk, Equiv.prodCongr_apply,
    Prod.map_apply, AddEquiv.toEquiv_eq_coe, EquivLike.coe_coe, bridgeModRangeNSMul_symm_mk]

/-- The inverse of `ModN.prodLinearEquiv` sends `(mkQ n x, mkQ n y)` to `mkQ n (x, y)`. -/
@[simp]
theorem prodLinearEquiv_symm_mkQ (G H : Type*) [AddCommGroup G] [AddCommGroup H] (n : ℕ)
    (x : G) (y : H) :
    (prodLinearEquiv G H n).symm (mkQ n x, mkQ n y) = mkQ n (x, y) := by
  rw [LinearEquiv.symm_apply_eq, prodLinearEquiv_mkQ]

private noncomputable def piAddEquiv {ι : Type*} (G : ι → Type*) [∀ i, AddCommGroup (G i)]
    (n : ℕ) :
    ModN (∀ i, G i) n ≃+ ∀ i, ModN (G i) n :=
  (bridgeModRangeNSMul (∀ i, G i) n).trans <|
    (QuotientAddGroup.addEquivPiModRangeNSMulAddMonoidHom G n).trans
      (AddEquiv.piCongrRight fun i ↦ (bridgeModRangeNSMul (G i) n).symm)

/-- `ModN · n` distributes `ZMod n`-linearly over indexed products of additive commutative
groups. -/
noncomputable def piLinearEquiv {ι : Type*} (G : ι → Type*) [∀ i, AddCommGroup (G i)] (n : ℕ) :
    ModN (∀ i, G i) n ≃ₗ[ZMod n] ∀ i, ModN (G i) n :=
  { piAddEquiv G n with
    map_smul' := fun c x ↦ ZMod.map_smul (piAddEquiv G n) c x }

/-- `ModN.piLinearEquiv` sends the class of `x` to `fun i ↦ mkQ n (x i)`. -/
@[simp]
theorem piLinearEquiv_mkQ {ι : Type*} (G : ι → Type*) [∀ i, AddCommGroup (G i)] (n : ℕ)
    (x : ∀ i, G i) :
    piLinearEquiv G n (mkQ n x) = fun i ↦ mkQ n (x i) := by
  change piAddEquiv G n (mkQ n x) = _
  rw [piAddEquiv, AddEquiv.trans_apply, AddEquiv.trans_apply, bridgeModRangeNSMul_mk,
    QuotientAddGroup.addEquivPiModRangeNSMulAddMonoidHom_apply]
  ext i
  exact bridgeModRangeNSMul_symm_mk (G i) n (x i)

/-- The inverse of `ModN.piLinearEquiv` sends `fun i ↦ mkQ n (x i)` to `mkQ n x`. -/
@[simp]
theorem piLinearEquiv_symm_mkQ {ι : Type*} (G : ι → Type*) [∀ i, AddCommGroup (G i)] (n : ℕ)
    (x : ∀ i, G i) :
    (piLinearEquiv G n).symm (fun i ↦ mkQ n (x i)) = mkQ n x := by
  rw [LinearEquiv.symm_apply_eq, piLinearEquiv_mkQ]

end ModN

end
