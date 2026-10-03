/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ClassFieldTheory.Brauer.Invariant
public import TauCeti.NumberTheory.ClassFieldTheory.Brauer.Torsion

/-!
# The local invariant on roots-of-unity cohomology

For a nonarchimedean local field `F` and an exponent `n` invertible in `F`, the Kummer
coefficient map identifies `H²(F, μₙ)` with the `n`-torsion of the Brauer group. The local
invariant `invMap F`, normalized by arithmetic Frobenius, therefore identifies it with the
`n`-torsion of `ℚ/ℤ`. The class of invariant `1/n` determines the normalized equivalence
`h2MuEquivZMod F hn : H²(F, μₙ) ≃+ ZMod n`.

The normalization is characterized by `toRatAddCircle_h2MuEquivZMod`: a class whose image in the
Brauer group has invariant `k/n` maps to `k`. In particular, the inverse image of `1` has
Brauer invariant `1/n`. This is the degree-two identification used after taking the cup product
of two Kummer classes in the cohomological local symbol.

Only invertibility in the field is required, not in its valuation ring. Thus in characteristic
zero the construction works for every nonzero `n`, including exponents divisible by the residue
characteristic (`h2MuEquivZMod_mixed`).

## Main definitions

* `h2MuEquivZMod`: the normalized identification `H²(F, μₙ) ≃+ ZMod n`.

## Main results

* `range_invMap_comp_h2MuToBr`: the Kummer classes have precisely the `n`-torsion invariants.
* `toRatAddCircle_h2MuEquivZMod`: the forward identification respects the Brauer invariant.
* `invMap_h2MuToBr_h2MuEquivZMod_symm`: the inverse has the prescribed Brauer invariant.
* `h2MuEquivZMod_eq_iff`: the invariant characterizes each residue.
* `h2MuEquivZMod_mixed`: the identification exists for every nonzero exponent in
  characteristic zero.

## References

* J.-P. Serre, *Local Fields*, Chapter XIII, §3 and Chapter XIV, §2.
* J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, 2nd ed., (6.2.1).
-/

public section
noncomputable section

namespace TauCeti.ClassFieldTheory

variable (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F] {n : ℕ}

/-- The local invariants of roots-of-unity cohomology are exactly the `n`-torsion of `ℚ/ℤ`,
when `n` is invertible in the field. -/
theorem range_invMap_comp_h2MuToBr (hn : IsUnit (n : F)) :
    ((invMap F).toAddMonoidHom.comp (h2MuToBr n F)).range =
      AddSubgroup.torsionBy (AddCircle (1 : ℚ)) (n : ℤ) := by
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    rw [AddSubgroup.torsionBy.nsmul_iff, AddMonoidHom.comp_apply, AddEquiv.coe_toAddMonoidHom,
      ← map_nsmul, (h2MuToBr_range n F hn _).mp ⟨y, rfl⟩, map_zero]
  · intro hx
    have hz : n • (invMap F).symm x = 0 := by
      rw [← map_nsmul, AddSubgroup.torsionBy.nsmul_iff.mp hx, map_zero]
    obtain ⟨y, hy⟩ := (h2MuToBr_range n F hn _).mpr hz
    exact ⟨y, by simp [hy]⟩

/-- The normalized local invariant `H²(F, μₙ) ≃+ ℤ/n`, for `n` invertible in the field.
It sends a class of Brauer invariant `k/n` to `k`. -/
def h2MuEquivZMod (hn : IsUnit (n : F)) :
    continuousCohomology 2 (muNRep n F) ≃+ ZMod n :=
  letI : NeZero (n : F) := ⟨hn.ne_zero⟩
  let f := (invMap F).toAddMonoidHom.comp (h2MuToBr n F)
  let hf : Function.Injective f := (invMap F).injective.comp (h2MuToBr_injective n F hn)
  let hr : Set.range f = (AddSubgroup.torsionBy (AddCircle (1 : ℚ)) (n : ℤ) : Set _) := by
    rw [← AddMonoidHom.coe_range, range_invMap_comp_h2MuToBr F hn]
  let hu := (AddCircle.existsUnique_apply_eq_coe_period_div (1 : ℚ) hf hr).exists
  (AddCircle.zmodAddEquivOfInjectiveOfRangeEqTorsionBy (1 : ℚ)
    (NeZero.pos_of_neZero_natCast F) hf hr hu.choose_spec).symm

/-- The degree-two invariant followed by `k ↦ k/n` is the Brauer invariant of the Kummer
coefficient image. This characterizes its arithmetic normalization. -/
@[simp]
theorem toRatAddCircle_h2MuEquivZMod (hn : IsUnit (n : F))
    (x : continuousCohomology 2 (muNRep n F)) :
    ZMod.toRatAddCircle n (h2MuEquivZMod F hn x) = invMap F (h2MuToBr n F x) := by
  have : NeZero (n : F) := ⟨hn.ne_zero⟩
  let f := (invMap F).toAddMonoidHom.comp (h2MuToBr n F)
  have hf : Function.Injective f := (invMap F).injective.comp (h2MuToBr_injective n F hn)
  have hr : Set.range f = (AddSubgroup.torsionBy (AddCircle (1 : ℚ)) (n : ℤ) : Set _) := by
    rw [← AddMonoidHom.coe_range, range_invMap_comp_h2MuToBr F hn]
  let hu := (AddCircle.existsUnique_apply_eq_coe_period_div (1 : ℚ) hf hr).exists
  let e := AddCircle.zmodAddEquivOfInjectiveOfRangeEqTorsionBy (1 : ℚ)
    (NeZero.pos_of_neZero_natCast F) hf hr hu.choose_spec
  have hgen : invMap F (h2MuToBr n F hu.choose) = ((1 / n : ℚ) : AddCircle (1 : ℚ)) := by
    simpa only [f, AddMonoidHom.comp_apply, AddEquiv.coe_toAddMonoidHom] using hu.choose_spec
  have he (z : ZMod n) :
      invMap F (h2MuToBr n F (e z)) = ZMod.toRatAddCircle n z := by
    obtain ⟨i, rfl⟩ := ZMod.intCast_surjective z
    rw [AddCircle.zmodAddEquivOfInjectiveOfRangeEqTorsionBy_apply_intCast,
      map_zsmul, map_zsmul]
    rw [hgen, ZMod.toRatAddCircle_intCast, ← AddCircle.coe_zsmul]
    congr 1
    simp [zsmul_eq_mul, div_eq_mul_inv]
  simpa only [AddEquiv.apply_symm_apply, h2MuEquivZMod, e, f] using (he (e.symm x)).symm

/-- The inverse degree-two identification has the prescribed Brauer invariant. For an integer
residue `k`, the right side is the class of `k/n` in `ℚ/ℤ`. -/
@[simp]
theorem invMap_h2MuToBr_h2MuEquivZMod_symm (hn : IsUnit (n : F)) (z : ZMod n) :
    invMap F (h2MuToBr n F ((h2MuEquivZMod F hn).symm z)) = ZMod.toRatAddCircle n z := by
  rw [← toRatAddCircle_h2MuEquivZMod F hn, AddEquiv.apply_symm_apply]

/-- A roots-of-unity cohomology class maps to a residue exactly when its Brauer invariant is
that residue's rational-circle image. -/
theorem h2MuEquivZMod_eq_iff (hn : IsUnit (n : F))
    (x : continuousCohomology 2 (muNRep n F)) (z : ZMod n) :
    h2MuEquivZMod F hn x = z ↔ invMap F (h2MuToBr n F x) = ZMod.toRatAddCircle n z := by
  have : NeZero (n : F) := ⟨hn.ne_zero⟩
  have : NeZero n := NeZero.of_neZero_natCast F
  rw [← (ZMod.toRatAddCircle_injective n).eq_iff, toRatAddCircle_h2MuEquivZMod]

/-- Roots-of-unity cohomology in degree two is `ℤ/n` in characteristic zero, for every nonzero
exponent. In particular this applies to finite extensions of `ℚ_p`, including `n` divisible
by `p`. The witness is the normalized equivalence `h2MuEquivZMod`. -/
theorem h2MuEquivZMod_mixed [CharZero F] (n : ℕ) (hn : n ≠ 0) :
    Nonempty (continuousCohomology 2 (muNRep n F) ≃+ ZMod n) :=
  ⟨h2MuEquivZMod F (Nat.cast_ne_zero.mpr hn).isUnit⟩

end TauCeti.ClassFieldTheory
