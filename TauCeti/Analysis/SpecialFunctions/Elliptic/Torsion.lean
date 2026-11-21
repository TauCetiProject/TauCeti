/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.SpecialFunctions.Elliptic.AdditionTheorem
public import TauCeti.Algebra.Module.Torsion.Snake
public import TauCeti.LinearAlgebra.FreeModule.ModN
import TauCeti.AlgebraicGeometry.EllipticCurve.Affine.Point.TwoTorsion

/-!
# Division points under complex uniformization

For a period lattice `Λ` and a positive integer `N`, the Weierstrass point map identifies
`Λ / NΛ` with the `N`-torsion of its elliptic curve: the class of `l` maps to the point of
`l / N`. In the basis of the two periods this gives explicit coordinates in `(ℤ/Nℤ)²`.
These coordinates retain the actual division points, including the point of `1/N` for
the period pair `(τ, 1)`, rather than just an abstract classification of the torsion group.
In particular the zeros of `℘'` are the half-periods (`PeriodPair.derivWeierstrassP_eq_zero_iff`).

The lattice-quotient identification uses `TauCeti.torsionByδEquiv`, the connecting
isomorphism for multiplication by `N` on the exact sequence
`0 → Λ → ℂ → E_Λ(ℂ) → 0`. The coordinate identification uses Mathlib's `ModN.basis`.

## References

* J. S. Milne, *Modular Functions and Modular Forms*, Proposition 3.12 and §8.
* J. H. Silverman, *The Arithmetic of Elliptic Curves*, VI.3 and VI.5.
-/

public noncomputable section

open scoped Pointwise

namespace PeriodPair

variable (L : PeriodPair) (N : ℕ) [NeZero N]

/-- A Weierstrass point is killed by `n` exactly when `n` times its argument is a period.
This includes `n = 0`. -/
theorem nsmul_weierstrassPoint_eq_zero_iff (n : ℕ) (z : ℂ) :
    n • L.weierstrassPoint z = 0 ↔ n • z ∈ L.lattice := by
  rw [← L.weierstrassPoint_nsmul, L.weierstrassPoint_eq_zero_iff]

omit [NeZero N] in
/-- Division points depend only on their coordinates modulo `N`: if `m ≡ m'` and `n ≡ n'`
modulo `N`, then `(m ω₁ + n ω₂) / N` and `(m' ω₁ + n' ω₂) / N` give the same point. At `N = 0`,
both arguments are `0` by Lean’s division-by-zero convention. -/
theorem weierstrassPoint_div_eq_of_intCast_eq {m n m' n' : ℤ} (hm : (m : ZMod N) = m')
    (hn : (n : ZMod N) = n') :
    L.weierstrassPoint ((m * L.ω₁ + n * L.ω₂) / N) =
      L.weierstrassPoint ((m' * L.ω₁ + n' * L.ω₂) / N) := by
  obtain ⟨k, hk⟩ := (ZMod.intCast_eq_intCast_iff_dvd_sub m m' N).mp hm
  obtain ⟨l, hl⟩ := (ZMod.intCast_eq_intCast_iff_dvd_sub n n' N).mp hn
  rcases eq_or_ne (N : ℂ) 0 with hN | hN
  · rw [hN, div_zero, div_zero]
  rw [weierstrassPoint_eq_weierstrassPoint_iff]
  convert neg_mem (add_mem (zsmul_mem L.ω₁_mem_lattice k) (zsmul_mem L.ω₂_mem_lattice l)) using 1
  have hk' : (m' : ℂ) = m + N * k := by exact_mod_cast (by linarith : m' = m + N * k)
  have hl' : (n' : ℂ) = n + N * l := by exact_mod_cast (by linarith : n' = n + N * l)
  rw [hk', hl', zsmul_eq_mul, zsmul_eq_mul]
  field_simp
  ring

/-- **The zeros of `℘'` are the half-periods**: `℘'(z) = 0` exactly when `2 z ∈ Λ`. This includes
the periods themselves, where Mathlib's `℘'` takes the value `0`. -/
theorem derivWeierstrassP_eq_zero_iff (z : ℂ) : ℘'[L] z = 0 ↔ 2 * z ∈ L.lattice := by
  rw [two_mul, ← two_nsmul, ← L.nsmul_weierstrassPoint_eq_zero_iff, two_nsmul]
  by_cases hz : z ∈ L.lattice
  · simp [L.weierstrassPoint_of_mem hz, L.derivWeierstrassP_coe ⟨z, hz⟩]
  · rw [L.weierstrassPoint_of_notMem hz, WeierstrassCurve.Affine.Point.some_add_self_eq_zero_iff]
    simp [WeierstrassCurve.Affine.evalEval_polynomialY]

private theorem exact_lattice_weierstrassPoint :
    Function.Exact L.lattice.subtype L.weierstrassPointHom.toIntLinearMap := by
  intro z
  constructor
  · intro hz
    have hz' : L.weierstrassPoint z = 0 := by
      simpa only [AddMonoidHom.coe_toIntLinearMap, weierstrassPointHom_apply] using hz
    exact ⟨⟨z, L.weierstrassPoint_eq_zero_iff.mp hz'⟩, rfl⟩
  · rintro ⟨l, rfl⟩
    simpa only [AddMonoidHom.coe_toIntLinearMap, weierstrassPointHom_apply,
      Submodule.subtype_apply] using
      L.weierstrassPoint_coe l

/-- The `N`-torsion of the lattice curve is `Λ/NΛ`. The inverse sends the class of a
period `l` to the point of `l/N`. -/
def torsionEquivLatticeQuotient :
    AddSubgroup.torsionBy L.weierstrassCurve.toAffine.Point (N : ℤ) ≃ₗ[ℤ]
      QuotSMulTop (N : ℤ) L.lattice :=
  TauCeti.torsionByδEquiv (N : ℤ) L.exact_lattice_weierstrassPoint
    L.lattice.injective_subtype (by
      simpa only [Function.Surjective, AddMonoidHom.coe_toIntLinearMap,
        weierstrassPointHom_apply] using L.weierstrassPoint_surjective) (by
      simpa only [zsmul_eq_mul, Int.cast_natCast] using
        (mulLeft_bijective₀ (N : ℂ) (Nat.cast_ne_zero.mpr (NeZero.ne N))))

/-- The inverse lattice-quotient identification sends `[l]` to the point of `l/N`. -/
@[simp]
theorem coe_torsionEquivLatticeQuotient_symm_mk (l : L.lattice) :
    ((L.torsionEquivLatticeQuotient N).symm (Submodule.Quotient.mk l) :
      L.weierstrassCurve.toAffine.Point) = L.weierstrassPoint ((l : ℂ) / N) := by
  have hmul : (N : ℤ) • ((l : ℂ) / N) = l := by
    rw [zsmul_eq_mul, Int.cast_natCast, mul_div_cancel₀ _ (Nat.cast_ne_zero.mpr (NeZero.ne N))]
  let P : AddSubgroup.torsionBy L.weierstrassCurve.toAffine.Point (N : ℤ) :=
    ⟨L.weierstrassPoint ((l : ℂ) / N), AddSubgroup.torsionBy.nsmul_iff.mpr <| by
      rw [L.nsmul_weierstrassPoint_eq_zero_iff]
      rw [← natCast_zsmul, hmul]
      exact l.property⟩
  have hP : L.torsionEquivLatticeQuotient N P = Submodule.Quotient.mk l := by
    rw [torsionEquivLatticeQuotient, TauCeti.torsionByδEquiv_apply]
    exact TauCeti.torsionByδ_eq L.exact_lattice_weierstrassPoint L.lattice.injective_subtype
      (by simpa only [Function.Surjective, AddMonoidHom.coe_toIntLinearMap,
        weierstrassPointHom_apply] using L.weierstrassPoint_surjective)
      P (by simp [P]) hmul.symm
  exact congrArg Subtype.val ((L.torsionEquivLatticeQuotient N).symm_apply_eq.mpr hP.symm)

/-- Every `N`-torsion point is the point of `l/N` for some lattice period `l`. -/
theorem exists_weierstrassPoint_div_eq_of_nsmul_eq_zero
    {P : L.weierstrassCurve.toAffine.Point} (hP : N • P = 0) :
    ∃ l : L.lattice, L.weierstrassPoint ((l : ℂ) / N) = P := by
  let T : AddSubgroup.torsionBy L.weierstrassCurve.toAffine.Point (N : ℤ) :=
    ⟨P, AddSubgroup.torsionBy.nsmul_iff.mpr hP⟩
  obtain ⟨l, hl⟩ := Submodule.Quotient.mk_surjective _ (L.torsionEquivLatticeQuotient N T)
  refine ⟨l, ?_⟩
  rw [← coe_torsionEquivLatticeQuotient_symm_mk, hl, LinearEquiv.symm_apply_apply]

/-- Coordinates in the two periods identify the `N`-torsion of the lattice curve with
`(ℤ/Nℤ)²`. The inverse sends `(a,b)` to the point of `(a ω₁ + b ω₂)/N`. -/
def torsionEquivCoordinates :
    AddSubgroup.torsionBy L.weierstrassCurve.toAffine.Point (N : ℤ) ≃ₗ[ℤ]
      (Fin 2 → ZMod N) :=
  (L.torsionEquivLatticeQuotient N).trans
    ((Submodule.quotEquivOfEq _ _ (by
      rw [Submodule.pointwise_smul_def, Submodule.map_top]
      rfl)).trans ((ModN.basis L.latticeBasis).equivFun.restrictScalars ℤ))

/-- The coordinates of the division point of `l/N` are the coordinates of `l` in the
lattice basis, reduced modulo `N`. -/
@[simp]
theorem torsionEquivCoordinates_apply_symm_mk
    (l : L.lattice) (i : Fin 2) :
    L.torsionEquivCoordinates N
      ((L.torsionEquivLatticeQuotient N).symm (Submodule.Quotient.mk l)) i =
        (L.latticeBasis.repr l i : ZMod N) := by
  simp [torsionEquivCoordinates, Module.Basis.equivFun_apply]

/-- Computing a division point from residues uses their least nonnegative representatives.
Changing these representatives by multiples of `N` adds lattice periods. -/
@[simp]
theorem coe_torsionEquivCoordinates_symm (x : Fin 2 → ZMod N) :
    ((L.torsionEquivCoordinates N).symm x : L.weierstrassCurve.toAffine.Point) =
      L.weierstrassPoint (((x 0).val * L.ω₁ + (x 1).val * L.ω₂) / N) := by
  let l : L.lattice := ∑ i : Fin 2, ((x i).val : ℤ) • L.latticeBasis i
  have hl : L.torsionEquivCoordinates N
      ((L.torsionEquivLatticeQuotient N).symm (Submodule.Quotient.mk l)) = x := by
    ext i
    rw [torsionEquivCoordinates_apply_symm_mk]
    simp only [l, Module.Basis.repr_sum_self, Int.cast_natCast, ZMod.natCast_zmod_val]
  have hs := (L.torsionEquivCoordinates N).symm_apply_eq.mpr hl.symm
  rw [hs, coe_torsionEquivLatticeQuotient_symm_mk]
  congr 2
  simp [l, Fin.sum_univ_two, zsmul_eq_mul]

/-- Dividing either basis period by `N` gives a point of exact order `N`. In particular,
for the period pair `(τ,1)`, the point of `1/N` has exact order `N`. -/
theorem addOrderOf_weierstrassPoint_latticeBasis_div (i : Fin 2) :
    addOrderOf (L.weierstrassPoint ((L.latticeBasis i : ℂ) / N)) = N := by
  let T := (L.torsionEquivLatticeQuotient N).symm
    (Submodule.Quotient.mk (L.latticeBasis i))
  have hT : L.torsionEquivCoordinates N T = Pi.single i 1 := by
    ext j
    simp [T, Finsupp.single_apply, Pi.single_apply, eq_comm]
  calc
    _ = addOrderOf (T : L.weierstrassCurve.toAffine.Point) := by
      rw [coe_torsionEquivLatticeQuotient_symm_mk]
    _ = addOrderOf T := AddSubgroup.addOrderOf_coe T
    _ = addOrderOf (L.torsionEquivCoordinates N T) :=
      ((L.torsionEquivCoordinates N).toAddEquiv.addOrderOf_eq T).symm
    _ = N := by
      rw [hT]
      exact (addOrderOf_injective (LinearMap.single ℤ (fun _ : Fin 2 ↦ ZMod N) i).toAddMonoidHom
        (fun x y h ↦ by simpa [LinearMap.single_apply] using congrFun h i) 1).trans
        (ZMod.addOrderOf_one N)

end PeriodPair
