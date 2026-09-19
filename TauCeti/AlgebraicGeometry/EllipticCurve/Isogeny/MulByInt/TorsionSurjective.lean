/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.MulByInt.KernelCard
-- Proof-only: a homomorphism of finite groups is onto once its kernel is no larger than the
-- quotient of the two orders.
import Mathlib.GroupTheory.Index

/-!
# `[n]` carries `E[n ²]` onto `E[n]`

Multiplication by `n` sends an `n ²`-torsion point to an `n`-torsion point, and over an
algebraically closed field in which `n` is invertible that map is **onto**: every `n`-torsion point
is `n` times an `n ²`-torsion point.

The argument is counting, not geometry. `#E[m] = m ²` for every invertible `m`, so `#E[n ²] = n ⁴`
and `#E[n] = n ²`; the kernel of `[n] : E[n ²] → E[n]` consists of `n`-torsion points, so it has at
most `n ²` elements, which is exactly `#E[n ²] / #E[n]`. A homomorphism of finite groups whose
kernel is that small is surjective.

## Main results

* `TauCeti.Isogeny.natCard_torsionBy`: `#E[n] = n ²`, the kernel count read on the intrinsic
  torsion subgroup.
* `TauCeti.Isogeny.torsionSqHom_surjective`: `[n] : E[n ²] → E[n]` is onto.
* `TauCeti.Isogeny.exists_zsmul_eq_of_zsmul_eq_zero`: hence every `n`-torsion point is `n • P` for
  some `P` killed by `n ²`.

## References

* [J. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], III.6.4 and III.8.

## Provenance

The counting argument is adapted from the AINTLIB `HasseWeil` project
(`github.com/CBirkbeck/AINTLIB`, Apache-2.0) pinned at
`a302aeacd86053f9d5f991fbbf664e1cc1051d08`, `HasseWeil/HasseBound/WeilPairing/Pairing.lean`,
declarations `mulByEllTorsionHom_surjective` and `exists_preimage_of_torsion`: the same three
steps — the two torsion orders, the kernel's injection into `E[n]`, and
`AddMonoidHom.surjective_of_card_ker_le_div`. The orders come from this repository's own
`card_ker_mulByIntIsogeny` rather than from that project's separable-kernel torsor, and the
statement is on `AddSubgroup.torsionBy` rather than on a bespoke torsion subgroup.
-/

public section

namespace TauCeti.Isogeny

open WeierstrassCurve.Affine

variable {F : Type*} [Field F] [DecidableEq F] (W : WeierstrassCurve.Affine F) [W.IsElliptic]

/-- **`#E[n] = n ²`** over an algebraically closed field in which `n` is invertible: the count of
`ker [n]` read on Mathlib's intrinsic torsion subgroup. -/
theorem natCard_torsionBy [IsAlgClosed F] {n : ℤ} (hchar : (n : F) ≠ 0) :
    Nat.card (AddSubgroup.torsionBy ((W⁄F).toAffine.Point) n) = n.natAbs ^ 2 := by
  rw [← ker_mulByIntIsogeny_eq_torsionBy W (psiFunctionField_ne_zero W hchar),
    card_ker_mulByIntIsogeny W hchar]

/-- The `n`-torsion is finite, its order being `n ²`. -/
theorem finite_torsionBy [IsAlgClosed F] {n : ℤ} (hchar : (n : F) ≠ 0) :
    Finite (AddSubgroup.torsionBy ((W⁄F).toAffine.Point) n) := by
  refine Nat.finite_of_card_ne_zero ?_
  rw [natCard_torsionBy W hchar]
  exact pow_ne_zero 2 (Int.natAbs_ne_zero.mpr (by rintro rfl; exact hchar (by simp)))

/-- **`[n]` as a map `E[n ²] → E[n]`**: an `n ²`-torsion point is carried to an `n`-torsion one,
since `n • (n • P) = n ² • P`. -/
def torsionSqHom (n : ℤ) :
    AddSubgroup.torsionBy ((W⁄F).toAffine.Point) (n ^ 2) →+
      AddSubgroup.torsionBy ((W⁄F).toAffine.Point) n where
  toFun P := ⟨n • P.val, (Submodule.mem_torsionBy_iff _ _).mpr <| by
    rw [smul_smul, ← sq]
    exact (Submodule.mem_torsionBy_iff _ _).mp P.2⟩
  map_zero' := by ext; simp
  map_add' _ _ := by ext; simp [smul_add]

/-- The kernel of `[n] : E[n ²] → E[n]` consists of `n`-torsion points, so it is no larger than
`E[n]`. -/
private theorem natCard_ker_torsionSqHom_le [IsAlgClosed F] {n : ℤ} (hchar : (n : F) ≠ 0) :
    Nat.card (torsionSqHom W n).ker ≤
      Nat.card (AddSubgroup.torsionBy ((W⁄F).toAffine.Point) n) := by
  have hfin : Finite (AddSubgroup.torsionBy ((W⁄F).toAffine.Point) n) := finite_torsionBy W hchar
  refine Nat.card_le_card_of_injective
    (fun P ↦ (⟨P.val.val, (Submodule.mem_torsionBy_iff _ _).mpr
      (congrArg Subtype.val (AddMonoidHom.mem_ker.mp P.2))⟩ :
        AddSubgroup.torsionBy ((W⁄F).toAffine.Point) n)) ?_
  intro a b h
  have h' := Subtype.ext_iff.mp h
  exact Subtype.ext (Subtype.ext h')

/-- **`[n]` carries `E[n ²]` onto `E[n]`** over an algebraically closed field in which `n` is
invertible. The kernel is `n`-torsion, so it has at most `n ²` elements, and that is exactly
`#E[n ²] / #E[n]`. -/
theorem torsionSqHom_surjective [IsAlgClosed F] {n : ℤ} (hchar : (n : F) ≠ 0) :
    Function.Surjective (torsionSqHom W n) := by
  have hne : n.natAbs ≠ 0 := Int.natAbs_ne_zero.mpr (by rintro rfl; exact hchar (by simp))
  have hn2 : ((n ^ 2 : ℤ) : F) ≠ 0 := by push_cast; exact pow_ne_zero 2 hchar
  have hfin : Finite (AddSubgroup.torsionBy ((W⁄F).toAffine.Point) n) := finite_torsionBy W hchar
  have hfin2 : Finite (AddSubgroup.torsionBy ((W⁄F).toAffine.Point) (n ^ 2)) :=
    finite_torsionBy W hn2
  refine AddMonoidHom.surjective_of_card_ker_le_div _ ?_
  have hdiv : Nat.card (AddSubgroup.torsionBy ((W⁄F).toAffine.Point) (n ^ 2)) /
      Nat.card (AddSubgroup.torsionBy ((W⁄F).toAffine.Point) n) = n.natAbs ^ 2 := by
    rw [natCard_torsionBy W hchar, natCard_torsionBy W hn2, Int.natAbs_pow,
      show (n.natAbs ^ 2) ^ 2 = n.natAbs ^ 2 * n.natAbs ^ 2 by ring]
    exact Nat.mul_div_cancel _ (Nat.pos_of_ne_zero (pow_ne_zero 2 hne))
  rw [hdiv, ← natCard_torsionBy W hchar]
  exact natCard_ker_torsionSqHom_le W hchar

/-- **Every `n`-torsion point is `n` times an `n ²`-torsion point**, over an algebraically closed
field in which `n` is invertible: the consumer-facing reading of `torsionSqHom_surjective`. -/
theorem exists_zsmul_eq_of_zsmul_eq_zero [IsAlgClosed F] {n : ℤ} (hchar : (n : F) ≠ 0)
    {T : (W⁄F).toAffine.Point} (hT : n • T = 0) :
    ∃ P : (W⁄F).toAffine.Point, n • P = T ∧ (n ^ 2 : ℤ) • P = 0 := by
  obtain ⟨P, hP⟩ := torsionSqHom_surjective W hchar
    ⟨T, (Submodule.mem_torsionBy_iff _ _).mpr hT⟩
  exact ⟨P.val, congrArg Subtype.val hP, (Submodule.mem_torsionBy_iff _ _).mp P.2⟩

end TauCeti.Isogeny

end
