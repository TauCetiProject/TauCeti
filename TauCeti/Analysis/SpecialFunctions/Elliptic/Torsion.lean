/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.SpecialFunctions.Elliptic.AdditionTheorem
public import TauCeti.Algebra.Module.Torsion.Snake
public import TauCeti.LinearAlgebra.FreeModule.ModN

/-!
# Division points under complex uniformization

For a period lattice `Λ` and a positive integer `N`, the Weierstrass point map identifies
`Λ / NΛ` with the `N`-torsion of its elliptic curve: the class of `l` maps to the point of
`l / N`. In the basis of the two periods this gives explicit coordinates in `(ℤ/Nℤ)²`.
These coordinates retain the actual division points, including the point of `1/N` for
the period pair `(τ, 1)`, rather than just an abstract classification of the torsion group.

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
@[simp]
theorem nsmul_weierstrassPoint_eq_zero_iff (n : ℕ) (z : ℂ) :
    n • L.weierstrassPoint z = 0 ↔ n • z ∈ L.lattice := by
  rw [← L.weierstrassPoint_nsmul, L.weierstrassPoint_eq_zero_iff]

/-- A Weierstrass point is killed by an integer exactly when that multiple of its
argument is a period. -/
@[simp]
theorem zsmul_weierstrassPoint_eq_zero_iff (n : ℤ) (z : ℂ) :
    n • L.weierstrassPoint z = 0 ↔ n • z ∈ L.lattice := by
  rw [← L.weierstrassPoint_zsmul, L.weierstrassPoint_eq_zero_iff]

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

/-- The lattice class of a torsion point is represented by `N` times any lift to `ℂ`. -/
theorem torsionEquivLatticeQuotient_eq
    (P : AddSubgroup.torsionBy L.weierstrassCurve.toAffine.Point (N : ℤ))
    {z : ℂ} {l : L.lattice} (hz : L.weierstrassPoint z = P) (hl : (l : ℂ) = N • z) :
    L.torsionEquivLatticeQuotient N P = Submodule.Quotient.mk l := by
  rw [torsionEquivLatticeQuotient, TauCeti.torsionByδEquiv_apply]
  exact TauCeti.torsionByδ_eq L.exact_lattice_weierstrassPoint L.lattice.injective_subtype
    (by simpa only [Function.Surjective, AddMonoidHom.coe_toIntLinearMap,
      weierstrassPointHom_apply] using L.weierstrassPoint_surjective)
    P (by simpa only [AddMonoidHom.coe_toIntLinearMap, weierstrassPointHom_apply] using hz)
    (by simpa only [Submodule.subtype_apply, natCast_zsmul] using hl)

/-- The lattice class of the division point of `l/N` is `[l]`. -/
@[simp]
theorem torsionEquivLatticeQuotient_weierstrassPoint_div (l : L.lattice)
    (hP : L.weierstrassPoint ((l : ℂ) / N) ∈
      AddSubgroup.torsionBy L.weierstrassCurve.toAffine.Point (N : ℤ)) :
    L.torsionEquivLatticeQuotient N ⟨L.weierstrassPoint ((l : ℂ) / N), hP⟩ =
      Submodule.Quotient.mk l := by
  apply L.torsionEquivLatticeQuotient_eq N _ rfl
  rw [nsmul_eq_mul, mul_div_cancel₀ _ (Nat.cast_ne_zero.mpr (NeZero.ne N))]

/-- The inverse lattice-quotient identification sends `[l]` to the point of `l/N`. -/
@[simp]
theorem coe_torsionEquivLatticeQuotient_symm_mk (l : L.lattice) :
    ((L.torsionEquivLatticeQuotient N).symm (Submodule.Quotient.mk l) :
      L.weierstrassCurve.toAffine.Point) = L.weierstrassPoint ((l : ℂ) / N) := by
  have hmul : N • ((l : ℂ) / N) = l := by
    rw [nsmul_eq_mul, mul_div_cancel₀ _ (Nat.cast_ne_zero.mpr (NeZero.ne N))]
  let P : AddSubgroup.torsionBy L.weierstrassCurve.toAffine.Point (N : ℤ) :=
    ⟨L.weierstrassPoint ((l : ℂ) / N), AddSubgroup.torsionBy.nsmul_iff.mpr <| by
      rw [L.nsmul_weierstrassPoint_eq_zero_iff, hmul]
      exact l.2⟩
  have hP : L.torsionEquivLatticeQuotient N P = Submodule.Quotient.mk l :=
    L.torsionEquivLatticeQuotient_eq N P rfl hmul.symm
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
      rw [Submodule.pointwise_smul_def, Submodule.map_top,
        LinearMap.lsmul_eq_distribSMulToLinearMap])).trans
      ((ModN.basis L.latticeBasis).equivFun.restrictScalars ℤ))

/-- The coordinates of the division point of `l/N` are the coordinates of `l` in the
lattice basis, reduced modulo `N`. -/
@[simp]
theorem torsionEquivCoordinates_torsionEquivLatticeQuotient_symm_mk
    (l : L.lattice) (i : Fin 2) :
    L.torsionEquivCoordinates N
      ((L.torsionEquivLatticeQuotient N).symm (Submodule.Quotient.mk l)) i =
        (L.latticeBasis.repr l i : ZMod N) := by
  simp [torsionEquivCoordinates, Module.Basis.equivFun_apply]

/-- The residue coordinates of a torsion point are the lattice coordinates of `N` times
a lift, reduced modulo `N`. -/
theorem torsionEquivCoordinates_eq
    (P : AddSubgroup.torsionBy L.weierstrassCurve.toAffine.Point (N : ℤ))
    {z : ℂ} {l : L.lattice} (hz : L.weierstrassPoint z = P) (hl : (l : ℂ) = N • z)
    (i : Fin 2) :
    L.torsionEquivCoordinates N P i = (L.latticeBasis.repr l i : ZMod N) := by
  have h := L.torsionEquivLatticeQuotient_eq N P hz hl
  rw [← (L.torsionEquivLatticeQuotient N).symm_apply_apply P, h]
  exact L.torsionEquivCoordinates_torsionEquivLatticeQuotient_symm_mk N l i

/-- The coordinates of the division point of `l/N` are those of `l` modulo `N`. -/
@[simp]
theorem torsionEquivCoordinates_weierstrassPoint_div (l : L.lattice)
    (hP : L.weierstrassPoint ((l : ℂ) / N) ∈
      AddSubgroup.torsionBy L.weierstrassCurve.toAffine.Point (N : ℤ)) (i : Fin 2) :
    L.torsionEquivCoordinates N ⟨L.weierstrassPoint ((l : ℂ) / N), hP⟩ i =
      (L.latticeBasis.repr l i : ZMod N) := by
  apply L.torsionEquivCoordinates_eq N _ rfl
  rw [nsmul_eq_mul, mul_div_cancel₀ _ (Nat.cast_ne_zero.mpr (NeZero.ne N))]

/-- Integer coefficients of `N` times a lift give the two residue coordinates. -/
theorem torsionEquivCoordinates_eq_of_int
    (P : AddSubgroup.torsionBy L.weierstrassCurve.toAffine.Point (N : ℤ))
    {z : ℂ} (a b : ℤ) (hz : L.weierstrassPoint z = P)
    (hab : (a : ℂ) * L.ω₁ + (b : ℂ) * L.ω₂ = N • z) :
    L.torsionEquivCoordinates N P = ![(a : ZMod N), (b : ZMod N)] := by
  let l : L.lattice := a • L.latticeBasis 0 + b • L.latticeBasis 1
  have hl : (l : ℂ) = N • z := by simpa [l, zsmul_eq_mul] using hab
  ext i
  rw [L.torsionEquivCoordinates_eq N P hz hl]
  fin_cases i <;> simp [l]

/-- Signed integer representatives give the division point with those residue coordinates. -/
theorem coe_torsionEquivCoordinates_symm_apply_int (a b : ℤ) :
    ((L.torsionEquivCoordinates N).symm ![(a : ZMod N), (b : ZMod N)] :
      L.weierstrassCurve.toAffine.Point) =
      L.weierstrassPoint (((a : ℂ) * L.ω₁ + (b : ℂ) * L.ω₂) / N) := by
  let l : L.lattice := a • L.latticeBasis 0 + b • L.latticeBasis 1
  have hl : (l : ℂ) = (a : ℂ) * L.ω₁ + (b : ℂ) * L.ω₂ := by simp [l, zsmul_eq_mul]
  have h := L.torsionEquivCoordinates_eq_of_int N
    ((L.torsionEquivLatticeQuotient N).symm (Submodule.Quotient.mk l)) a b
    (L.coe_torsionEquivLatticeQuotient_symm_mk N l).symm (by
      rw [← hl, nsmul_eq_mul, mul_div_cancel₀ _ (Nat.cast_ne_zero.mpr (NeZero.ne N))])
  rw [← h, LinearEquiv.symm_apply_apply, coe_torsionEquivLatticeQuotient_symm_mk, hl]

/-- Computing a division point from residues uses their least nonnegative representatives.
Changing these representatives by multiples of `N` adds lattice periods. -/
@[simp]
theorem coe_torsionEquivCoordinates_symm_apply (x : Fin 2 → ZMod N) :
    ((L.torsionEquivCoordinates N).symm x : L.weierstrassCurve.toAffine.Point) =
      L.weierstrassPoint (((x 0).val * L.ω₁ + (x 1).val * L.ω₂) / N) := by
  let l : L.lattice := ∑ i : Fin 2, ((x i).val : ℤ) • L.latticeBasis i
  have hl : L.torsionEquivCoordinates N
      ((L.torsionEquivLatticeQuotient N).symm (Submodule.Quotient.mk l)) = x := by
    ext i
    rw [torsionEquivCoordinates_torsionEquivLatticeQuotient_symm_mk]
    simp only [l, Module.Basis.repr_sum_self, Int.cast_natCast, ZMod.natCast_zmod_val]
  have hs := (L.torsionEquivCoordinates N).symm_apply_eq.mpr hl.symm
  rw [hs, coe_torsionEquivLatticeQuotient_symm_mk]
  congr 2
  simp [l, Fin.sum_univ_two, zsmul_eq_mul]

/-- Dividing either basis period by `N` gives a point of exact order `N`. In particular,
for the period pair `(τ,1)`, the point of `1/N` has exact order `N`. -/
@[simp]
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
      simpa only [AddMonoidHom.single_apply, ZMod.addOrderOf_one] using
        addOrderOf_injective (AddMonoidHom.single (fun _ : Fin 2 ↦ ZMod N) i)
          (by simpa only [AddMonoidHom.coe_single] using
            Pi.single_injective (M := fun _ : Fin 2 ↦ ZMod N) i) (1 : ZMod N)

/-- Dividing the first period by `N` gives a point of exact order `N`. -/
@[simp]
theorem addOrderOf_weierstrassPoint_ω₁_div :
    addOrderOf (L.weierstrassPoint (L.ω₁ / N)) = N := by
  simpa only [latticeBasis_zero] using L.addOrderOf_weierstrassPoint_latticeBasis_div N 0

/-- Dividing the second period by `N` gives a point of exact order `N`. -/
@[simp]
theorem addOrderOf_weierstrassPoint_ω₂_div :
    addOrderOf (L.weierstrassPoint (L.ω₂ / N)) = N := by
  simpa only [latticeBasis_one] using L.addOrderOf_weierstrassPoint_latticeBasis_div N 1


end PeriodPair
