/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.IndexNSmul

import Mathlib.GroupTheory.FiniteAbelian.Basic
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Dimension.Torsion.Finite

/-!
# The index of `n • G` in a finitely generated commutative group

Mathlib's `Mathlib/GroupTheory/IndexNSmul.lean` computes the index of the image of the
multiplication-by-`n` map `nsmulAddMonoidHom n` on a group that is **free** and finitely generated
as a `ℤ`-module: `AddSubgroup.index_range_nsmul` gives `n ^ finrank ℤ M`. This file drops freeness.

## Main results

* `AddSubgroup.index_range_nsmul_of_fg`: **the index of `n • G` in a finitely generated commutative
  group** `G` is `n ^ finrank ℤ G * Nat.card G[n]`, where `G[n]` is the `n`-torsion subgroup. Over a
  free group the torsion factor is `1` and this is Mathlib's `AddSubgroup.index_range_nsmul`; the
  extra factor is exactly what torsion contributes. The proof runs the structure theorem
  `AddCommGroup.equiv_free_prod_directSum_zmod` and reduces to the free case on the free part and
  to a counting argument on the finite part.
* `Subgroup.index_range_powMonoidHom_of_fg`: the same count for a group written multiplicatively,
  `(G : Gⁿ) = n ^ finrank ℤ (Additive G) * #G[n]`, the form that applies to unit groups such as the
  `S`-units of a number field.
* `Subgroup.index_range_pow_mul_card_ker` and its additive form
  `AddSubgroup.index_range_nsmul_mul_card_ker`: for a subgroup `U ≤ G` of finite index,
  `(G : nG) * #U[n] = #G[n] * (U : nU)`. It is stated multiplicatively as well so that it applies
  to unit groups such as `Kˣ`, whose `n`-th power classes it counts. This is the cross-multiplied
  form of "`(G : nG) / #G[n]` is unchanged on passing to a finite-index subgroup", and only the
  cross-multiplied form is asserted: nothing here forces `G[n]` finite or the indices nonzero, and
  `Nat.card` and `Subgroup.index` are both `0` on infinite arguments, so neither ratio need be
  defined.
* `AddEquiv.map_ker_nsmulAddMonoidHom` and `AddEquiv.index_range_nsmulAddMonoidHom`: an additive
  equivalence carries `G[n]` to `H[n]` and preserves the index of `n • G`. The first is the kernel
  counterpart of Mathlib's `AddEquiv.map_range_nsmulAddMonoidHom`.
* `MulEquiv.injective_pow_iff` and its additive form `AddEquiv.injective_nsmul_iff`: taking `n`-th
  powers is injective on one side of an equivalence exactly when it is injective on the other.

The exact count, not merely finiteness of the index, is what turns an index computation into a rank
computation: solved for the rank, `(G : nG) = n ^ finrank ℤ G * Nat.card G[n]` converts a bound on
`(G : nG)` (for instance one coming from the cardinality of a Selmer group in an `n`-descent) into a
bound on `finrank ℤ G`. Finiteness of the index alone, which Mathlib's
`Subgroup.finiteIndex_range_powMonoidHom_of_fg` supplies, carries no rank information, and the free
case does not apply to groups with torsion such as the `S`-units of a number field.

The declarations whose comments name a source are adapted from Michael Stoll's elliptic-curves
formalisation (`github.com/MichaelStollBayreuth/EllipticCurves`,
`EllipticCurves/Mathlib/SelmerGroup.lean` at commit `66889eada51a`, Apache 2.0, by Michael Stoll).
Following this repository's convention for adapted material, the upstream authorship is credited
here rather than in the copyright header.

**Not ported from that file**, because Mathlib or this repository already has them: its
`Module.finite_int_additive` and `Group.fg_of_module_finite_int` (Mathlib's
`AddMonoid.FG.to_moduleFinite_int` and `Module.Finite.iff_addGroup_fg` composed with
`AddGroup.fg_iff_mul_fg`), `finite_of_fg_of_pow_eq_one` (`CommGroup.finite_of_fg_isMulTorsion`),
`finite_modPow` (`Subgroup.finiteIndex_range_powMonoidHom_of_fg`), `card_ker_mul_card_range` and
`index_range_eq_card_ker` (`AddSubgroup.index_range`, which needs only `FiniteIndex` on the kernel
rather than a finite ambient group, so the counting lemma that derived it is unnecessary),
`ker_nsmulAddMonoidHom` (`AddSubgroup.nsmulAddMonoidHom_injective_of_isTorsionFree` through
`AddMonoidHom.ker_eq_bot_iff`), its `nsmulAddMonoidHom_range_prod` and `nsmulAddMonoidHom_ker_prod`
(`AddMonoidHom.range_prodMap` and `AddMonoidHom.ker_prodMap`, which apply once multiplication by
`n` on a product is identified with the componentwise `AddMonoidHom.prodMap`, a step the proof
below takes directly), and its `Subgroup.fg_of_commGroup_fg` and
`Group.fg_of_fg_ker_of_fg_range` (both in `TauCeti/GroupTheory/Finiteness.lean`). Its
`Module.rank_eq_zero_of_finite` is replaced by Mathlib's `Module.IsTorsion.rank_eq_zero` applied
to `isAddTorsion_of_finite`.
-/

public section

open Module

namespace Subgroup

variable {G : Type*} [CommGroup G]

/-- The second isomorphism theorem applied to `G[n]` and `U`: `(U : G[n] ⊔ U) * #U[n] = #G[n]`.
A step of `index_range_pow_mul_card_ker`. -/
-- Adapted from the private `relIndex_sup_ker_mul_card_ker` in Michael Stoll's `EllipticCurves`
-- (`EllipticCurves/Mathlib/SelmerGroup.lean`, pin `66889eada51a`).
@[to_additive]
private lemma relIndex_sup_ker_mul_card_ker (U : Subgroup G) (n : ℕ) :
    U.relIndex ((powMonoidHom (α := G) n).ker ⊔ U) *
        Nat.card (powMonoidHom (α := U) n).ker =
      Nat.card (powMonoidHom (α := G) n).ker := by
  set φG := powMonoidHom (α := G) n
  set φU := powMonoidHom (α := U) n
  have h2 : Nat.card (φG.ker ⧸ U.subgroupOf φG.ker) = U.relIndex (φG.ker ⊔ U) :=
    Nat.card_congr (QuotientGroup.quotientInfEquivProdNormalQuotient φG.ker U).toEquiv
  have h3 : Nat.card (U.subgroupOf φG.ker) = Nat.card φU.ker :=
    Nat.card_congr
      ⟨fun x ↦ ⟨⟨(x : G), x.2⟩, Subtype.ext (x : φG.ker).2⟩,
        fun y ↦ ⟨⟨(y : U), congrArg Subtype.val y.2⟩, (y : U).2⟩,
        fun x ↦ rfl, fun y ↦ rfl⟩
  rw [← h2, ← h3, ← card_eq_card_quotient_mul_card_subgroup]

/-- **For a subgroup `U` of finite index in a commutative group `G` and any `n`,
`(G : Gⁿ) * #U[n] = #G[n] * (U : Uⁿ)`,** where `Gⁿ` is the subgroup of `n`-th powers and `G[n]`
the `n`-torsion subgroup. This is the cross-multiplied form of "`(G : Gⁿ) / #G[n]` is unchanged
on passing to a finite-index subgroup"; it is the product, not the quotient statement, that holds
at this generality, since with `G[n]` not assumed finite `Nat.card` and `Subgroup.index` may both
be `0` and neither ratio need be defined. -/
-- Adapted from `AddSubgroup.index_range_nsmul_mul_card_ker` in Michael Stoll's `EllipticCurves`
-- (`EllipticCurves/Mathlib/SelmerGroup.lean`, pin `66889eada51a`), stated here multiplicatively.
-- The step `hBA` is the source's private `relIndex_range_comp_subtype`, proved here by Mathlib's
-- `Subgroup.relIndex_map_map` rather than the source's surjection `G → nG ⧸ nU`.
@[to_additive /-- **For a subgroup `U` of finite index in a commutative group `G` and any `n`,
`(G : nG) * #U[n] = #G[n] * (U : nU)`.** This is the cross-multiplied form of "`(G : nG) / #G[n]`
is unchanged on passing to a finite-index subgroup"; it is the product, not the quotient
statement, that holds at this generality, since with `G[n]` not assumed finite `Nat.card` and
`AddSubgroup.index` may both be `0` and neither ratio need be defined. -/]
theorem index_range_pow_mul_card_ker (U : Subgroup G) [U.FiniteIndex] (n : ℕ) :
    (powMonoidHom (α := G) n).range.index * Nat.card (powMonoidHom (α := U) n).ker =
      Nat.card (powMonoidHom (α := G) n).ker * (powMonoidHom (α := U) n).range.index := by
  set φG := powMonoidHom (α := G) n
  set φU := powMonoidHom (α := U) n
  set C : Subgroup G := φG.ker ⊔ U
  have hUC : U ≤ C := le_sup_right
  have hCne : C.index ≠ 0 := (finiteIndex_of_le hUC).index_ne_zero
  -- `Uⁿ = φG(U)` sits in both `Gⁿ = φG(⊤)` and `U`. Its index in `Gⁿ` is `(G : C)` by
  -- `relIndex_map_map`, and its index in `U` is `(U : Uⁿ)`.
  have hBU : U.map φG ≤ U := by
    rintro _ ⟨u, hu, rfl⟩
    exact U.pow_mem hu n
  have hBA : (U.map φG).relIndex φG.range = C.index := by
    rw [φG.range_eq_map, relIndex_map_map, top_sup_eq, relIndex_top_right, sup_comm]
  have hrBU : (U.map φG).relIndex U = φU.range.index := by
    have h : (U.map φG).subgroupOf U = φU.range := by
      ext u
      constructor
      · rintro ⟨w, hw, hwu⟩
        exact ⟨⟨w, hw⟩, Subtype.ext hwu⟩
      · rintro ⟨w, rfl⟩
        exact ⟨w, w.2, rfl⟩
    rw [relIndex, h]
  -- compute the index of `Uⁿ` in `G` through `Gⁿ` and through `U ≤ C`, then cancel `(G : C)`
  have hA : φG.range.index = φU.range.index * U.relIndex C := by
    refine mul_left_cancel₀ hCne ?_
    calc C.index * φG.range.index = (U.map φG).index := by
          rw [← hBA, relIndex_mul_index (map_le_range φG U)]
      _ = C.index * (φU.range.index * U.relIndex C) := by
          rw [← relIndex_mul_index hBU, hrBU, ← relIndex_mul_index hUC]
          ring
  rw [hA, mul_assoc, relIndex_sup_ker_mul_card_ker U n, mul_comm]

end Subgroup

namespace MulEquiv

/-- Taking `n`-th powers is injective on `M` exactly when it is injective on `N`, for a
multiplicative equivalence `M ≃* N`, since the equivalence commutes with it. -/
@[to_additive /-- Multiplication by `n` is injective on `M` exactly when it is injective on `N`,
for an additive equivalence `M ≃+ N`, since the equivalence commutes with it. -/]
theorem injective_pow_iff {M N : Type*} [Monoid M] [Monoid N] (e : M ≃* N) (n : ℕ) :
    Function.Injective (fun x : M ↦ x ^ n) ↔ Function.Injective (fun y : N ↦ y ^ n) := by
  have h : (fun y : N ↦ y ^ n) = e ∘ (fun x : M ↦ x ^ n) ∘ e.symm := by
    ext y
    simp
  rw [h, EquivLike.comp_injective, EquivLike.injective_comp]

end MulEquiv

namespace AddEquiv

variable {M N : Type*} [AddCommGroup M] [AddCommGroup N]

/-- An additive equivalence maps `M[n]` to `N[n]`. This is the kernel counterpart of Mathlib's
`AddEquiv.map_range_nsmulAddMonoidHom`. -/
-- Adapted from `AddEquiv.map_ker_nsmulAddMonoidHom` in Michael Stoll's `EllipticCurves`
-- (`EllipticCurves/Mathlib/SelmerGroup.lean`, pin `66889eada51a`).
lemma map_ker_nsmulAddMonoidHom (e : M ≃+ N) (n : ℕ) :
    ((nsmulAddMonoidHom (α := M) n).ker).map e.toAddMonoidHom =
      (nsmulAddMonoidHom (α := N) n).ker := by
  ext x
  rw [AddSubgroup.mem_map_equiv]
  simp only [AddMonoidHom.mem_ker, nsmulAddMonoidHom_apply]
  rw [← map_nsmul, EmbeddingLike.map_eq_zero_iff]

/-- The index of `n • M` is invariant under additive equivalence. -/
-- Adapted from `AddEquiv.index_range_nsmulAddMonoidHom` in Michael Stoll's `EllipticCurves`
-- (`EllipticCurves/Mathlib/SelmerGroup.lean`, pin `66889eada51a`).
lemma index_range_nsmulAddMonoidHom (e : M ≃+ N) (n : ℕ) :
    (nsmulAddMonoidHom (α := M) n).range.index = (nsmulAddMonoidHom (α := N) n).range.index := by
  simpa [AddEquiv.map_range_nsmulAddMonoidHom]
    using (AddSubgroup.index_map_equiv (nsmulAddMonoidHom (α := M) n).range e).symm

end AddEquiv

namespace AddSubgroup

open Module in
/-- The case `n = 0` of `AddSubgroup.index_range_nsmul_of_fg`: the range is trivial and the kernel
is everything, so both sides are `Nat.card G` (for finite `G` the rank is `0`, and for infinite `G`
both sides vanish). -/
private theorem index_range_zero_nsmul (G : Type*) [AddCommGroup G] :
    (nsmulAddMonoidHom (α := G) 0).range.index =
      0 ^ finrank ℤ G * Nat.card (nsmulAddMonoidHom (α := G) 0).ker := by
  have h0 : nsmulAddMonoidHom (α := G) 0 = 0 := by ext; simp
  rw [h0, AddMonoidHom.range_zero, AddMonoidHom.ker_zero, AddSubgroup.index_bot,
    Nat.card_congr AddSubgroup.topEquiv.toEquiv]
  rcases finite_or_infinite G with hG | hG
  · simp [Module.IsTorsion.finrank_eq_zero
    (isAddTorsion_iff_isTorsion_int.mp (isAddTorsion_of_finite (G := G)))]
  · simp [Nat.card_eq_zero_of_infinite]

open scoped DirectSum in
/-- **The index of `n • G` in a finitely generated commutative group** `G` is
`n ^ finrank ℤ G * #G[n]`, where `G[n]` is the `n`-torsion subgroup.

This extends Mathlib's `AddSubgroup.index_range_nsmul`, which is the free case: there the torsion
subgroup is trivial and the second factor is `1`. -/
-- Adapted from `AddSubgroup.index_range_nsmul_of_fg` in Michael Stoll's `EllipticCurves`
-- (`EllipticCurves/Mathlib/SelmerGroup.lean`, pin `66889eada51a`). Two steps are discharged from
-- Mathlib rather than from the source's own helpers: `AddSubgroup.index_range` replaces its
-- `AddMonoidHom.index_range_eq_card_ker`, and `Module.IsTorsion.rank_eq_zero` replaces its
-- `Module.rank_eq_zero_of_finite`.
theorem index_range_nsmul_of_fg (G : Type*) [AddCommGroup G] [AddGroup.FG G] (n : ℕ) :
    (nsmulAddMonoidHom (α := G) n).range.index =
      n ^ finrank ℤ G * Nat.card (nsmulAddMonoidHom (α := G) n).ker := by
  rcases eq_or_ne n 0 with rfl | hn
  · exact index_range_zero_nsmul G
  obtain ⟨r, ι, fι, p, hp, e, ⟨eqv⟩⟩ := AddCommGroup.equiv_free_prod_directSum_zmod G
  have hne (i : ι) : NeZero (p i ^ e i) := ⟨pow_ne_zero _ (hp i).pos.ne'⟩
  have hTfin : Finite (⨁ i, ZMod (p i ^ e i)) := Finite.of_equiv _ DFinsupp.equivFunOnFintype.symm
  have hidx : (nsmulAddMonoidHom (α := G) n).range.index
      = (nsmulAddMonoidHom (α := (Fin r →₀ ℤ) × ⨁ i, ZMod (p i ^ e i)) n).range.index :=
    AddEquiv.index_range_nsmulAddMonoidHom eqv n
  have hker : Nat.card (nsmulAddMonoidHom (α := G) n).ker
      = Nat.card (nsmulAddMonoidHom (α := (Fin r →₀ ℤ) × ⨁ i, ZMod (p i ^ e i)) n).ker := by
    rw [← eqv.map_ker_nsmulAddMonoidHom n, card_map_of_injective eqv.injective]
  have hrk : finrank ℤ G = r := by
    have h1 : Module.rank ℤ ((Fin r →₀ ℤ) × ⨁ i, ZMod (p i ^ e i)) = r := by
      set π := LinearMap.fst ℤ (Fin r →₀ ℤ) (⨁ i, ZMod (p i ^ e i))
      have h0 : Module.rank ℤ (LinearMap.ker π) = 0 := by
        rw [LinearMap.ker_fst, rank_range_of_injective _ LinearMap.inr_injective]
        exact Module.IsTorsion.rank_eq_zero
          (isAddTorsion_iff_isTorsion_int.mp isAddTorsion_of_finite)
      rw [← π.rank_range_add_rank_ker, LinearMap.range_eq_top.mpr Prod.fst_surjective, rank_top,
        rank_finsupp_self', Cardinal.mk_fin, h0, add_zero]
    rw [eqv.toIntLinearEquiv.finrank_eq]
    exact finrank_eq_of_rank_eq h1
  have hkerF : (nsmulAddMonoidHom (α := Fin r →₀ ℤ) n).ker = ⊥ :=
    (AddMonoidHom.ker_eq_bot_iff _).mpr
      (AddSubgroup.nsmulAddMonoidHom_injective_of_isTorsionFree hn)
  -- multiplication by `n` on a product is componentwise, so it is `AddMonoidHom.prodMap`
  have hprod : nsmulAddMonoidHom (α := (Fin r →₀ ℤ) × ⨁ i, ZMod (p i ^ e i)) n =
      (nsmulAddMonoidHom (α := Fin r →₀ ℤ) n).prodMap
        (nsmulAddMonoidHom (α := ⨁ i, ZMod (p i ^ e i)) n) := by
    ext x <;> simp
  rw [hidx, hker, hrk, hprod, AddMonoidHom.range_prodMap, AddSubgroup.index_prod,
    AddSubgroup.index_range_nsmul, AddSubgroup.index_range,
    AddMonoidHom.ker_prodMap, Nat.card_congr (AddSubgroup.prodEquiv _ _).toEquiv,
    Nat.card_prod, hkerF]
  simp

end AddSubgroup

namespace Subgroup

/-- **The index of the `n`-th powers in a finitely generated commutative group** `G` is
`n ^ finrank ℤ (Additive G) * #G[n]`, where `G[n]` is the `n`-torsion subgroup. This is
`AddSubgroup.index_range_nsmul_of_fg` read in `Additive G`. -/
theorem index_range_powMonoidHom_of_fg (G : Type*) [CommGroup G] [Group.FG G] (n : ℕ) :
    (powMonoidHom (α := G) n).range.index =
      n ^ finrank ℤ (Additive G) * Nat.card (powMonoidHom (α := G) n).ker := by
  have h : (powMonoidHom (α := G) n).toAdditive = nsmulAddMonoidHom n := by
    ext x
    simp
  have := AddSubgroup.index_range_nsmul_of_fg (Additive G) n
  rwa [← h, MonoidHom.coe_toAdditive_range, MonoidHom.coe_toAdditive_ker,
    index_toAddSubgroup] at this

end Subgroup

end
