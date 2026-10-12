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

Multiplication by `n` sends an `n ²`-torsion point to an `n`-torsion point, and once `n` is
invertible in the base field and the geometric `n ²`-torsion is rational that map is **onto**:
every `n`-torsion point is `n` times an `n ²`-torsion point.

The argument is counting, not geometry. `#E[m] = m ²` for every invertible `m`, so `#E[n ²] = n ⁴`
and `#E[n] = n ²`; the kernel of `[n] : E[n ²] → E[n]` consists of `n`-torsion points, so it has at
most `n ²` elements, which is exactly `#E[n ²] / #E[n]`. A homomorphism of finite groups whose
kernel is that small is surjective.

## Main results

* `WeierstrassCurve.Affine.zsmulTorsionSqHom_surjective_of_torsion_rational`:
  `[n] : E[n ²] → E[n]` is onto.
* `WeierstrassCurve.Affine.exists_zsmul_eq_of_zsmul_eq_zero_of_torsion_rational`: hence every
  `n`-torsion point is `n • P` for some `P` killed by `n ²`.

## References

* [J. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], III.6.4 and III.8.

## Provenance

The counting argument is adapted from the AINTLIB `HasseWeil` project
(`github.com/CBirkbeck/AINTLIB`, Apache-2.0) pinned at
`a302aeacd86053f9d5f991fbbf664e1cc1051d08`, `HasseWeil/HasseBound/WeilPairing/Pairing.lean`,
declarations `mulByEllTorsionHom_surjective` and `exists_preimage_of_torsion`: the same three
steps — the two torsion orders, the kernel's injection into `E[n]`, and
`AddMonoidHom.surjective_of_card_ker_le_div`. The orders come from this repository's own
`card_ker_mulByIntIsogeny_of_torsion_rational` rather than from that project's separable-kernel
torsor, and the statement is on `AddSubgroup.torsionBy` rather than on a bespoke torsion
subgroup.
-/

public section

namespace WeierstrassCurve.Affine

variable {F : Type*} [Field F] [DecidableEq F] (W : Affine F) [W.IsElliptic]

/-- **`[n]` as a map `E[n ²] → E[n]`**: an `n ²`-torsion point is carried to an `n`-torsion one,
since `n • (n • P) = n ² • P`. -/
def zsmulTorsionSqHom (n : ℤ) :
    AddSubgroup.torsionBy ((W⁄F).toAffine.Point) (n ^ 2) →+
      AddSubgroup.torsionBy ((W⁄F).toAffine.Point) n :=
  ((zsmulAddGroupHom (α := (W⁄F).toAffine.Point) n).domRestrict
    (AddSubgroup.torsionBy ((W⁄F).toAffine.Point) (n ^ 2))).codRestrict
      (AddSubgroup.torsionBy ((W⁄F).toAffine.Point) n) fun P ↦
    (Submodule.mem_torsionBy_iff _ _).mpr <| by
    have hP : (n ^ 2 : ℤ) • (P : (W⁄F).toAffine.Point) = 0 :=
      (Submodule.mem_torsionBy_iff _ _).mp P.2
    have hnn : n • (n • (P : (W⁄F).toAffine.Point)) = 0 := by
      simpa only [smul_smul, sq] using hP
    exact hnn

omit [W.IsElliptic] in
/-- The restricted multiplication homomorphism sends `P` to `n • P`. -/
@[simp]
theorem zsmulTorsionSqHom_apply (n : ℤ)
    (P : AddSubgroup.torsionBy ((W⁄F).toAffine.Point) (n ^ 2)) :
    ((zsmulTorsionSqHom W n P : AddSubgroup.torsionBy ((W⁄F).toAffine.Point) n) :
      (W⁄F).toAffine.Point) = n • (P : (W⁄F).toAffine.Point) := by
  simp only [zsmulTorsionSqHom, AddMonoidHom.codRestrict_apply,
    AddMonoidHom.domRestrict_apply, zsmulAddGroupHom_apply]

open scoped Classical in
/-- The kernel of `[n] : E[n ²] → E[n]` consists of `n`-torsion points, so it is no larger than
`E[n]`. -/
private theorem natCard_ker_zsmulTorsionSqHom_le {n : ℤ}
    (hn : n ≠ 0) :
    Nat.card (zsmulTorsionSqHom W n).ker ≤
      Nat.card (AddSubgroup.torsionBy ((W⁄F).toAffine.Point) n) := by
  have hfin : Finite (AddSubgroup.torsionBy ((W⁄F).toAffine.Point) n) :=
    finite_torsionBy W hn
  refine Nat.card_le_card_of_injective
    (fun P ↦ (⟨P.val.val, (Submodule.mem_torsionBy_iff _ _).mpr
      (by
        have hP := congrArg Subtype.val (AddMonoidHom.mem_ker.mp P.2)
        rw [zsmulTorsionSqHom_apply] at hP
        exact hP)⟩ :
        AddSubgroup.torsionBy ((W⁄F).toAffine.Point) n)) ?_
  intro a b h
  have h' := Subtype.ext_iff.mp h
  exact Subtype.ext (Subtype.ext h')

open scoped Classical in
/-- **`[n]` carries `E[n ²]` onto `E[n]`** when the geometric `n ²`-torsion is rational and `n`
is invertible. The kernel is `n`-torsion, so it has at most `n ²` elements, and that is exactly
`#E[n ²] / #E[n]`. -/
theorem zsmulTorsionSqHom_surjective_of_torsion_rational {n : ℤ}
    (hrat : ∀ P : (W.baseChange (AlgebraicClosure W.FunctionField)).toAffine.Point,
      (n ^ 2 : ℤ) • P = 0 →
        P ∈ Set.range (Point.baseChange (W' := W) F (AlgebraicClosure W.FunctionField)))
    (hchar : (n : F) ≠ 0) :
    Function.Surjective (zsmulTorsionSqHom W n) := by
  have hne : n.natAbs ≠ 0 := Int.natAbs_ne_zero.mpr (by rintro rfl; exact hchar (by simp))
  have hn2 : ((n ^ 2 : ℤ) : F) ≠ 0 := by push_cast; exact pow_ne_zero 2 hchar
  have hratn : ∀ P : (W.baseChange (AlgebraicClosure W.FunctionField)).toAffine.Point,
      n • P = 0 →
        P ∈ Set.range (Point.baseChange (W' := W) F (AlgebraicClosure W.FunctionField)) := by
    intro P hP
    apply hrat P
    rw [pow_two, mul_smul, hP]
    exact zsmul_zero n
  have hfin : Finite (AddSubgroup.torsionBy ((W⁄F).toAffine.Point) n) :=
    finite_torsionBy W (by rintro rfl; exact hchar (by simp))
  have hfin2 : Finite (AddSubgroup.torsionBy ((W⁄F).toAffine.Point) (n ^ 2)) :=
    finite_torsionBy W (pow_ne_zero 2 (by rintro rfl; exact hchar (by simp)))
  refine AddMonoidHom.surjective_of_card_ker_le_div _ ?_
  have hdiv : Nat.card (AddSubgroup.torsionBy ((W⁄F).toAffine.Point) (n ^ 2)) /
      Nat.card (AddSubgroup.torsionBy ((W⁄F).toAffine.Point) n) = n.natAbs ^ 2 := by
    rw [natCard_torsionBy_of_torsion_rational W hratn hchar,
      natCard_torsionBy_of_torsion_rational W hrat hn2, Int.natAbs_pow, pow_two]
    exact Nat.mul_div_cancel _ (Nat.pos_of_ne_zero (pow_ne_zero 2 hne))
  rw [hdiv, ← natCard_torsionBy_of_torsion_rational W hratn hchar]
  exact natCard_ker_zsmulTorsionSqHom_le W (by rintro rfl; exact hchar (by simp))

open scoped Classical in
/-- **Every `n`-torsion point is `n` times an `n ²`-torsion point** when the geometric `n ²`-torsion
is rational and `n` is invertible: the consumer-facing reading of
`zsmulTorsionSqHom_surjective_of_torsion_rational`. -/
theorem exists_zsmul_eq_of_zsmul_eq_zero_of_torsion_rational {n : ℤ}
    (hrat : ∀ P : (W.baseChange (AlgebraicClosure W.FunctionField)).toAffine.Point,
      (n ^ 2 : ℤ) • P = 0 →
        P ∈ Set.range (Point.baseChange (W' := W) F (AlgebraicClosure W.FunctionField)))
    (hchar : (n : F) ≠ 0) {T : (W⁄F).toAffine.Point} (hT : n • T = 0) :
    ∃ P : (W⁄F).toAffine.Point, n • P = T ∧ (n ^ 2 : ℤ) • P = 0 := by
  obtain ⟨P, hP⟩ := zsmulTorsionSqHom_surjective_of_torsion_rational W hrat hchar
    ⟨T, (Submodule.mem_torsionBy_iff _ _).mpr hT⟩
  have hPval := congrArg Subtype.val hP
  rw [zsmulTorsionSqHom_apply] at hPval
  exact ⟨P.val, hPval, (Submodule.mem_torsionBy_iff _ _).mp P.2⟩

end WeierstrassCurve.Affine

end
