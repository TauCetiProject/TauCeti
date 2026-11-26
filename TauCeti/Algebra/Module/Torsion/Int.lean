/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.FiniteAbelian.Basic
public import Mathlib.Algebra.Module.ZMod
public import Mathlib.RingTheory.QuotSMulTop
public import TauCeti.Algebra.Module.Torsion.Basic
public import TauCeti.RingTheory.QuotSMulTop
import Mathlib.Algebra.Field.ZMod
import Mathlib.Data.ZMod.QuotientRing
import Mathlib.FieldTheory.Finiteness

/-!
# Torsion and reduction of abelian groups

For an integer `n ≠ 0`, the `n`-torsion of a torsion-free abelian group `M`, such as `ℤ`, is zero,
and the reduction `M ⧸ nM = QuotSMulTop n M` of a finitely generated abelian group is finite. These
are recorded as instances, so that such groups meet the finiteness hypotheses of constructions that
take both the `n`-torsion and the reduction mod `n` of a `ℤ`-module. The reduction `M ⧸ 2M` is
moreover a vector space over `ZMod 2`, whose dimension is the rank of `M` when `M` is finite free;
quadratic forms reduced modulo two live on it.

## Main results

* `TauCeti.natCard_ker_nsmulAddMonoidHom_eq_natCard_torsionBy`: the kernel of multiplication
  by `n` has the same order as the `n`-torsion submodule.
* `TauCeti.subsingleton_torsionBy_int`: the `n`-torsion of a torsion-free abelian group is zero for
  `n ≠ 0`.
* `TauCeti.finite_quotSMulTop_int`: `M ⧸ nM` is finite for `n ≠ 0` and `M` finitely generated.
* `TauCeti.instModuleZModTwoQuotSMulTop`: `M ⧸ 2M` is a vector space over `ZMod 2`.
* `TauCeti.finrank_zmod_quotSMulTop_two`: its dimension is the rank of a finite free `M`.
* `AddEquiv.isTorsion'_iff`: for a submonoid `S` of `ℤ`, being `S`-torsion is invariant under
  additive equivalences.
* `TauCeti.span_range_mk_ofMul_eq_top_iff`: a family generates a commutative group modulo torsion
  exactly when its classes span the torsion-free quotient of the associated `ℤ`-module.
-/

public section

namespace TauCeti

/-- The kernel of multiplication by `n` on an abelian group has the same order as its
`n`-torsion submodule. No finiteness or nonzero hypothesis is needed. -/
theorem natCard_ker_nsmulAddMonoidHom_eq_natCard_torsionBy (M : Type*) [AddCommGroup M]
    (n : ℕ) :
    Nat.card (nsmulAddMonoidHom (α := M) n).ker =
      Nat.card (Submodule.torsionBy ℤ M n) :=
  Nat.card_congr (Equiv.subtypeEquivRight fun x ↦ by
    rw [AddMonoidHom.mem_ker, nsmulAddMonoidHom_apply, Submodule.mem_torsionBy_iff,
      natCast_zsmul])

variable (n : ℤ) [NeZero n] (M : Type*) [AddCommGroup M]

/-- A torsion-free abelian group, such as `ℤ`, has no nonzero `n`-torsion for `n ≠ 0`. -/
instance subsingleton_torsionBy_int [HasUniqueDiv M] :
    Subsingleton (Submodule.torsionBy ℤ M n) :=
  Submodule.subsingleton_iff_eq_bot.mpr <|
    (isSMulRegular_iff_torsionBy_eq_bot M n).mp (.of_ne_zero (NeZero.ne n))

/-- The reduction `M ⧸ nM` of a finitely generated abelian group, such as `ℤ ⧸ nℤ`, is finite for
`n ≠ 0`. -/
instance finite_quotSMulTop_int [Module.Finite ℤ M] : Finite (QuotSMulTop n M) :=
  Module.finite_of_fg_torsion _ fun x ↦
    ⟨⟨n, mem_nonZeroDivisors_of_ne_zero (NeZero.ne n)⟩,
      Module.mem_annihilator.mp (QuotSMulTop.mem_annihilator M n) x⟩

/-- The reduction `M ⧸ 2M` of an abelian group is a vector space over `ZMod 2`, since twice each
of its elements vanishes. Like every `ZMod 2`-module structure on an abelian group, it is unique,
and it restricts to the `ℤ`-module structure of the quotient. -/
instance instModuleZModTwoQuotSMulTop : Module (ZMod 2) (QuotSMulTop (2 : ℤ) M) :=
  AddCommGroup.zmodModule fun x ↦ by
    rw [two_nsmul]
    nth_rewrite 1 [← QuotSMulTop.neg_eq_self x]
    exact neg_add_cancel x

/-- **The dimension of `M ⧸ 2M`.** For a finite free abelian group `M`, the `ZMod 2`-vector space
`M ⧸ 2M` has dimension the rank of `M`. -/
theorem finrank_zmod_quotSMulTop_two [Module.Free ℤ M] [Module.Finite ℤ M] :
    Module.finrank (ZMod 2) (QuotSMulTop (2 : ℤ) M) = Module.finrank ℤ M := by
  have h := QuotSMulTop.natCard_eq_pow_finrank (2 : ℤ) M
  have h2 : Nat.card (ℤ ⧸ Ideal.span {(2 : ℤ)}) = 2 := by
    rw [Nat.card_congr (Int.quotientSpanEquivZMod 2).toEquiv]
    simp
  rw [h2, Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod] at h
  exact Nat.pow_right_injective le_rfl h

/-- An element of a commutative group `G` lies in the torsion submodule of the `ℤ`-module
`Additive G` exactly when it lies in the torsion subgroup of `G`. -/
theorem ofMul_mem_torsion_int_iff {G : Type*} [CommGroup G] {x : G} :
    Additive.ofMul x ∈ Submodule.torsion ℤ (Additive G) ↔ x ∈ CommGroup.torsion G := by
  rw [← Submodule.mem_toAddSubgroup, Submodule.torsion_int, AddCommGroup.mem_torsion,
    isOfFinAddOrder_ofMul_iff, CommGroup.mem_torsion]

/-- A family `ε` in a commutative group `G` generates `G` together with the torsion subgroup
exactly when its classes span the `ℤ`-module `Additive G` modulo its torsion submodule. -/
theorem span_range_mk_ofMul_eq_top_iff {G ι : Type*} [CommGroup G] (ε : ι → G) :
    Submodule.span ℤ (Set.range fun i ↦
        (Submodule.Quotient.mk (Additive.ofMul (ε i)) :
          Additive G ⧸ Submodule.torsion ℤ (Additive G))) = ⊤ ↔
      Subgroup.closure (Set.range ε) ⊔ CommGroup.torsion G = ⊤ := by
  set T := Submodule.torsion ℤ (Additive G)
  set N := Submodule.span ℤ (Set.range fun i ↦ Additive.ofMul (ε i))
  -- Subgroups of `G` are the `ℤ`-submodules of `Additive G`.
  let e : Subgroup G ≃o Submodule ℤ (Additive G) :=
    Subgroup.toAddSubgroup.trans AddSubgroup.toIntSubmodule
  -- `e` sends the subgroup generated by `ε` to `N`, and the torsion subgroup to `T`.
  have hclosure : e (Subgroup.closure (Set.range ε)) = N := by
    simp [e, N, Subgroup.toAddSubgroup_closure, AddSubgroup.toIntSubmodule_closure,
      ← Equiv.image_symm_eq_preimage, ← Set.range_comp, Function.comp_def]
  have htors : e (CommGroup.torsion G) = T := by
    ext x
    rw [← Submodule.mem_toAddSubgroup, OrderIso.trans_apply,
      AddSubgroup.toIntSubmodule_toAddSubgroup, Additive.mem_toAddSubgroup,
      ← ofMul_mem_torsion_int_iff, ofMul_toMul]
  -- So both sides say that `N ⊔ T` is everything.
  calc _ ↔ N.map T.mkQ = ⊤ := by
        simp [N, Submodule.map_span, ← Set.range_comp, Function.comp_def]
    _ ↔ N ⊔ T = ⊤ := by rw [Submodule.map_mkQ_eq_top, sup_comm]
    _ ↔ e (Subgroup.closure (Set.range ε) ⊔ CommGroup.torsion G) = e ⊤ := by
        rw [map_sup, hclosure, htors, map_top]
    _ ↔ _ := e.injective.eq_iff

/-- For a submonoid `S` of `ℤ`, being `S`-torsion, every element killed by an element of `S`, is
invariant under additive equivalences of abelian groups, for the canonical action of `ℤ`. This is
`LinearEquiv.isTorsion'_iff` for the induced `ℤ`-linear equivalence. -/
theorem _root_.AddEquiv.isTorsion'_iff {G H : Type*} [AddCommGroup G] [AddCommGroup H]
    (e : G ≃+ H) {S : Submonoid ℤ} : Module.IsTorsion' G S ↔ Module.IsTorsion' H S :=
  e.toIntLinearEquiv.isTorsion'_iff

end TauCeti
