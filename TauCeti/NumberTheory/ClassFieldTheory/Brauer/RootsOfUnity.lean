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

An isomorphism of coefficient objects `e : μₙ ≅ T` transports the invariant to
`h2EquivZModOfMuNRepIso F hn e : H²(F, T) ≃+ ZMod n`. When `F` contains a primitive `n`th root of
unity `ζ`, the root identifies the trivial coefficients `ℤ/n` with `μₙ`, and
`h2FpEquivZMod hζ : H²(F, ℤ/n) ≃+ ZMod n` is the transported invariant. In particular
`H²(F, ℤ/n)` then has exactly `n` elements.

## Main definitions

* `h2MuEquivZMod`: the normalized identification `H²(F, μₙ) ≃+ ZMod n`.
* `h2EquivZModOfMuNRepIso`: its transport `H²(F, T) ≃+ ZMod n` along a coefficient isomorphism
  `μₙ ≅ T`.
* `h2FpEquivZMod`: the normalized identification `H²(F, ℤ/n) ≃+ ZMod n` with trivial
  coefficients, given a primitive `n`th root of unity in `F`.

## Main results

* `range_invMap_comp_h2MuToBr`: the Kummer classes have precisely the `n`-torsion invariants.
* `toRatAddCircle_h2MuEquivZMod`: the forward identification respects the Brauer invariant.
* `invMap_h2MuToBr_h2MuEquivZMod_symm`: the inverse has the prescribed Brauer invariant.
* `h2MuEquivZMod_eq_iff`: the invariant characterizes each residue.
* `h2MuEquivZMod_mixed`: the identification exists for every nonzero exponent in
  characteristic zero.
* `toRatAddCircle_h2FpEquivZMod`, `h2FpEquivZMod_eq_iff`: the normalization with trivial
  coefficients.
* `natCard_cohomFp_two_absoluteGaloisGroup_of_isPrimitiveRoot`: `H²(F, ℤ/n)` has `n` elements.

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

/-! ### Coefficients identified with roots of unity -/

open CategoryTheory in
/-- **The local invariant on `H²` with coefficients identified with `μₙ`**: an isomorphism of
coefficient objects `e : μₙ ≅ T` transports `h2MuEquivZMod` to `H²(F, T)`. The identification of
coefficients is essential: an arbitrary coefficient object, such as the zero module, need not have
`H²` isomorphic to `ℤ/n`. -/
def h2EquivZModOfMuNRepIso (hn : IsUnit (n : F)) {T : GalRep n F} (e : muNRep n F ≅ T) :
    continuousCohomology 2 T ≃+ ZMod n :=
  ((TauCeti.ContinuousCohomology.continuousCohomologyFunctor (ZMod n) _ 2).mapIso
    e).toContinuousLinearEquiv.toLinearEquiv.toAddEquiv.symm.trans (h2MuEquivZMod F hn)

open CategoryTheory in
/-- The transported invariant of the image of a roots-of-unity class under the coefficient
isomorphism is its roots-of-unity invariant. -/
@[simp]
theorem h2EquivZModOfMuNRepIso_coeffMap (hn : IsUnit (n : F)) {T : GalRep n F}
    (e : muNRep n F ≅ T) (x : continuousCohomology 2 (muNRep n F)) :
    h2EquivZModOfMuNRepIso F hn e (TauCeti.ContinuousCohomology.coeffMap e.hom 2 x) =
      h2MuEquivZMod F hn x :=
  (h2MuEquivZMod F hn).congr_arg
    (((TauCeti.ContinuousCohomology.continuousCohomologyFunctor (ZMod n) _ 2).mapIso
      e).toContinuousLinearEquiv.toLinearEquiv.symm_apply_apply x)

open CategoryTheory in
/-- The inverse transported invariant is the image under the coefficient isomorphism of the
inverse roots-of-unity invariant. -/
@[simp]
theorem h2EquivZModOfMuNRepIso_symm_apply (hn : IsUnit (n : F)) {T : GalRep n F}
    (e : muNRep n F ≅ T) (z : ZMod n) :
    (h2EquivZModOfMuNRepIso F hn e).symm z =
      TauCeti.ContinuousCohomology.coeffMap e.hom 2 ((h2MuEquivZMod F hn).symm z) := by
  rw [AddEquiv.symm_apply_eq, h2EquivZModOfMuNRepIso_coeffMap, AddEquiv.apply_symm_apply]

/-! ### Trivial coefficients -/

section TrivialFp

variable {F} [NeZero n]

/-- **The local invariant on `H²(F, ℤ/n)` with trivial coefficients**, for `F` containing a
primitive `n`th root of unity `ζ`. The root identifies the trivial coefficients `ℤ/n` with `μₙ`
(`muNRepIsoTrivialFp`), and `h2FpEquivZMod` is the specialization of `h2EquivZModOfMuNRepIso`
to that identification. -/
def h2FpEquivZMod {ζ : F} (hζ : IsPrimitiveRoot ζ n) :
    cohomFp n (Field.absoluteGaloisGroup F) 2 ≃+ ZMod n :=
  h2EquivZModOfMuNRepIso F hζ.neZero'.out.isUnit (muNRepIsoTrivialFp n F hζ)

/-- The trivial-coefficient invariant of the transport of a roots-of-unity class is its
roots-of-unity invariant. -/
@[simp]
theorem h2FpEquivZMod_muNRepCohomologyEquivTrivialFp {ζ : F} (hζ : IsPrimitiveRoot ζ n)
    (x : continuousCohomology 2 (muNRep n F)) :
    h2FpEquivZMod hζ (muNRepCohomologyEquivTrivialFp n F hζ 2 x) =
      h2MuEquivZMod F hζ.neZero'.out.isUnit x := by
  rw [muNRepCohomologyEquivTrivialFp_apply]
  exact h2EquivZModOfMuNRepIso_coeffMap F _ (muNRepIsoTrivialFp n F hζ) x

/-- The inverse trivial-coefficient invariant is the transport of the inverse roots-of-unity
invariant. -/
@[simp]
theorem h2FpEquivZMod_symm_apply {ζ : F} (hζ : IsPrimitiveRoot ζ n) (z : ZMod n) :
    (h2FpEquivZMod hζ).symm z =
      muNRepCohomologyEquivTrivialFp n F hζ 2
        ((h2MuEquivZMod F hζ.neZero'.out.isUnit).symm z) := by
  rw [muNRepCohomologyEquivTrivialFp_apply]
  exact h2EquivZModOfMuNRepIso_symm_apply F _ (muNRepIsoTrivialFp n F hζ) z

/-- **The arithmetic normalization with trivial coefficients**: a class of `H²(F, ℤ/n)` maps to
`k` exactly when the corresponding class of `H²(F, μₙ)` has Brauer invariant `k/n`. -/
@[simp]
theorem toRatAddCircle_h2FpEquivZMod {ζ : F} (hζ : IsPrimitiveRoot ζ n)
    (x : cohomFp n (Field.absoluteGaloisGroup F) 2) :
    ZMod.toRatAddCircle n (h2FpEquivZMod hζ x) =
      invMap F (h2MuToBr n F ((muNRepCohomologyEquivTrivialFp n F hζ 2).symm x)) := by
  rw [← toRatAddCircle_h2MuEquivZMod F hζ.neZero'.out.isUnit,
    ← h2FpEquivZMod_muNRepCohomologyEquivTrivialFp hζ, LinearEquiv.apply_symm_apply]

/-- A class of `H²(F, ℤ/n)` maps to a residue exactly when the Brauer invariant of the
corresponding class of `H²(F, μₙ)` is that residue's rational-circle image. -/
theorem h2FpEquivZMod_eq_iff {ζ : F} (hζ : IsPrimitiveRoot ζ n)
    (x : cohomFp n (Field.absoluteGaloisGroup F) 2) (z : ZMod n) :
    h2FpEquivZMod hζ x = z ↔
      invMap F (h2MuToBr n F ((muNRepCohomologyEquivTrivialFp n F hζ 2).symm x)) =
        ZMod.toRatAddCircle n z := by
  rw [← (ZMod.toRatAddCircle_injective n).eq_iff, toRatAddCircle_h2FpEquivZMod]

/-- If `F` contains a primitive `n`th root of unity, then `H²(F, ℤ/n)` with trivial coefficients
has exactly `n` elements. -/
theorem natCard_cohomFp_two_absoluteGaloisGroup_of_isPrimitiveRoot {ζ : F}
    (hζ : IsPrimitiveRoot ζ n) :
    Nat.card (cohomFp n (Field.absoluteGaloisGroup F) 2) = n :=
  (Nat.card_congr (h2FpEquivZMod hζ).toEquiv).trans (Nat.card_zmod n)

end TrivialFp

end TauCeti.ClassFieldTheory
