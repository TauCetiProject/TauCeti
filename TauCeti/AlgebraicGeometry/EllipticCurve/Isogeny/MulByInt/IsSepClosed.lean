/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Torsion.IsSepClosed
public import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.MulByInt.Torsion.Rank
public import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.MulByInt.Torsion.Surjective

/-!
# Torsion over a separably closed field

Rationality of geometric torsion over a separably closed field is the hypothesis the counts of
`MulByInt/` take of the base field, so each of them holds here and the algebraically closed
hypothesis they carried weakens to a separably closed one. The rationality theorem itself lives
with the division-polynomial torsion theory in `DivisionPolynomial.Torsion.IsSepClosed`.

## Main results

* `TauCeti.Isogeny.card_ker_mulByIntIsogeny` and `WeierstrassCurve.Affine.natCard_torsionBy`:
  `#E[n] = n ²`, in the kernel and the torsion-subgroup forms.
* `WeierstrassCurve.natCard_torsionBy`: the same count read on `W.toAffine.Point` itself,
  rather than on the trivial base change `W⁄K`.
* `TauCeti.Isogeny.card_ker_mulByPrimeIsogeny`,
  `TauCeti.Isogeny.finrank_ker_mulByPrimeIsogeny` and
  `TauCeti.Isogeny.nonempty_linearEquiv_ker_mulByPrimeIsogeny`: `E[ℓ] ≅ (ZMod ℓ) ²` at a prime.
* `WeierstrassCurve.Affine.zsmulTorsionSqHom_surjective` and
  `WeierstrassCurve.Affine.exists_zsmul_eq_of_zsmul_eq_zero`: `[n]` carries `E[n ²]` onto `E[n]`.
* `WeierstrassCurve.Affine.exists_point_zsmul_eq_of_zsmul_eq_zero` and
  `WeierstrassCurve.Affine.natCard_setOf_zsmul_eq_zero`: the same two facts on the points of `W`
  itself rather than of `W⁄F`.

## References

* [J. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], III.6.4(b).
-/

public section

namespace TauCeti.Isogeny

open WeierstrassCurve.Affine

variable {F : Type*} [Field F] [DecidableEq F] [IsSepClosed F] (W : WeierstrassCurve.Affine F)
  [W.IsElliptic]

open scoped Classical in
/-- **`#ker [n] = n ²`** over a separably closed field, for `n` invertible there: the geometric
`n`-torsion is then rational, which is the only thing the count asks of the base field. -/
theorem card_ker_mulByIntIsogeny {n : ℤ} {hn : psiFunctionField W n ≠ 0} (hchar : (n : F) ≠ 0) :
    Nat.card (mulByIntIsogeny W hn).ker = n.natAbs ^ 2 :=
  card_ker_mulByIntIsogeny_of_torsion_rational W
    (fun _ hP ↦ W.mem_range_baseChange_of_zsmul_eq_zero_of_isSepClosed hchar hP) hchar

-- Not `@[simp]`: `mulByPrimeIsogeny` is an `abbrev`, so `simp` sees through it to
-- `card_ker_mulByIntIsogeny` and `simpNF` rejects the pair as duplicates.
/-- **`#E[ℓ] = ℓ ²`**, for a prime `ℓ` invertible in a separably closed base field. -/
theorem card_ker_mulByPrimeIsogeny {l : ℕ} [hl : Fact l.Prime] (hchar : (l : F) ≠ 0) :
    Nat.card (mulByPrimeIsogeny W l).ker = l ^ 2 := by
  rw [card_ker_mulByIntIsogeny W (by simpa using hchar), Int.natAbs_natCast]

open scoped Classical in
/-- **`E[ℓ]` is two-dimensional over `ZMod ℓ`** for a prime `ℓ` invertible in a separably closed
base field, where the geometric `ℓ`-torsion is rational. -/
@[simp]
theorem finrank_ker_mulByPrimeIsogeny {l : ℕ} [hl : Fact l.Prime] (hchar : (l : F) ≠ 0) :
    Module.finrank (ZMod l) (mulByPrimeIsogeny W l).ker = 2 :=
  finrank_ker_mulByPrimeIsogeny_of_torsion_rational W
    (fun _ hP ↦ W.mem_range_baseChange_of_zsmul_eq_zero_of_isSepClosed
      (by simpa using hchar) hP) hchar

open scoped Classical in
/-- **`E[ℓ] ≅ (ZMod ℓ)²`** for a prime `ℓ` invertible in a separably closed base field. -/
theorem nonempty_linearEquiv_ker_mulByPrimeIsogeny {l : ℕ} [hl : Fact l.Prime]
    (hchar : (l : F) ≠ 0) :
    Nonempty ((mulByPrimeIsogeny W l).ker ≃ₗ[ZMod l] (Fin 2 → ZMod l)) :=
  nonempty_linearEquiv_ker_mulByPrimeIsogeny_of_torsion_rational W
    (fun _ hP ↦ W.mem_range_baseChange_of_zsmul_eq_zero_of_isSepClosed
      (by simpa using hchar) hP) hchar

end TauCeti.Isogeny

namespace WeierstrassCurve.Affine

variable {F : Type*} [Field F] [DecidableEq F] [IsSepClosed F] (W : Affine F) [W.IsElliptic]

open scoped Classical in
/-- **`#E[n] = n ²`** over a separably closed field in which `n` is invertible, read on Mathlib's
intrinsic torsion subgroup. -/
theorem natCard_torsionBy {n : ℤ} (hchar : (n : F) ≠ 0) :
    Nat.card (AddSubgroup.torsionBy ((W⁄F).toAffine.Point) n) = n.natAbs ^ 2 :=
  natCard_torsionBy_of_torsion_rational W
    (fun _ hP ↦ W.mem_range_baseChange_of_zsmul_eq_zero_of_isSepClosed hchar hP) hchar

open scoped Classical in
/-- **`[n]` carries `E[n ²]` onto `E[n]`** over a separably closed field in which `n` is
invertible. -/
theorem zsmulTorsionSqHom_surjective {n : ℤ} (hchar : (n : F) ≠ 0) :
    Function.Surjective (zsmulTorsionSqHom W n) :=
  zsmulTorsionSqHom_surjective_of_torsion_rational W
    (fun _ hP ↦ W.mem_range_baseChange_of_zsmul_eq_zero_of_isSepClosed
      (by push_cast; exact pow_ne_zero 2 hchar) hP) hchar

open scoped Classical in
/-- **Every `n`-torsion point is `n` times an `n ²`-torsion point**, over a separably closed field
in which `n` is invertible. -/
theorem exists_zsmul_eq_of_zsmul_eq_zero {n : ℤ} (hchar : (n : F) ≠ 0)
    {T : (W⁄F).toAffine.Point} (hT : n • T = 0) :
    ∃ P : (W⁄F).toAffine.Point, n • P = T ∧ (n ^ 2 : ℤ) • P = 0 :=
  exists_zsmul_eq_of_zsmul_eq_zero_of_torsion_rational W
    (fun _ hP ↦ W.mem_range_baseChange_of_zsmul_eq_zero_of_isSepClosed
      (by push_cast; exact pow_ne_zero 2 hchar) hP) hchar hT

/-- **Every `n`-torsion point of `W` is `n` times a point of `W`**, over a separably closed field
in which `n` is invertible. -/
theorem exists_point_zsmul_eq_of_zsmul_eq_zero {n : ℤ} (hchar : (n : F) ≠ 0) {T : W.Point}
    (hT : n • T = 0) : ∃ R : W.Point, n • R = T := by
  obtain ⟨P, hP, -⟩ := W.exists_zsmul_eq_of_zsmul_eq_zero hchar
    (T := Point.equivBaseChangeSelf W T) (by rw [← map_zsmul, hT, map_zero])
  exact ⟨(Point.equivBaseChangeSelf W).symm P, by rw [← map_zsmul, hP, AddEquiv.symm_apply_apply]⟩

open scoped Classical in
/-- **`#E[n] = n ²`** over a separably closed field in which `n` is invertible, counted on the
points of `W` themselves. -/
theorem natCard_setOf_zsmul_eq_zero {n : ℤ} (hchar : (n : F) ≠ 0) :
    Nat.card {R : W.Point | n • R = 0} = n.natAbs ^ 2 := by
  rw [← W.natCard_torsionBy hchar]
  refine Nat.card_congr ((Point.equivBaseChangeSelf W).toEquiv.subtypeEquiv fun R ↦ ?_)
  simp only [Set.mem_ofPred_eq, AddEquiv.toEquiv_eq_coe, EquivLike.coe_coe]
  refine ⟨fun h ↦ (Submodule.mem_torsionBy_iff _ _).mpr ?_, fun h ↦ ?_⟩
  · rw [← map_zsmul, h, map_zero]
  · have := (Submodule.mem_torsionBy_iff _ _).mp h
    rwa [← map_zsmul, AddEquiv.map_eq_zero_iff] at this

end WeierstrassCurve.Affine

namespace WeierstrassCurve

variable {K : Type*} [Field K] [IsSepClosed K] (W : WeierstrassCurve K) [W.IsElliptic]

open scoped Classical in
/-- The `n`-torsion read on `W.toAffine.Point` itself, rather than on the trivial base change
`W⁄K`, has order `n.natAbs ^ 2` when `n` is invertible in `K`. -/
theorem natCard_torsionBy {n : ℤ} (hn : (n : K) ≠ 0) :
    Nat.card (AddSubgroup.torsionBy W.toAffine.Point n) = n.natAbs ^ 2 := by
  have h := W.toAffine.natCard_torsionBy hn
  rwa [Affine.baseChange_self] at h

end WeierstrassCurve

end
