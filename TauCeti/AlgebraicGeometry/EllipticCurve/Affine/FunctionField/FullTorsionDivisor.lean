/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.Affine.FunctionField.Divisor.Sum
public import TauCeti.AlgebraicGeometry.EllipticCurve.Affine.FunctionField.Map.Place
-- Proof-only: `F` is the exact constant field of `F(W)`.
import TauCeti.AlgebraicGeometry.EllipticCurve.Affine.FunctionField.Genus

/-!
# Bloch's function with divisor `(C² - 1)(O) - ∑_{0 ≠ a ∈ E[C]} (a)`

Let `E` be an elliptic curve over a field `F` whose `C`-torsion `E[C]` is rational and isomorphic
to `(ℤ/C)²`. Then the divisor

`∑_{a ∈ E[C]} ((O) - (a)) = (C² - 1)(O) - ∑_{0 ≠ a ∈ E[C]} (a)`

is principal: it has degree zero, and its sum in the group law is `-∑_{a ∈ E[C]} a = 0`, because
the elements of `(ℤ/C)²` sum to zero. A function `ρ` with this divisor, together with the
functions `f_a` with divisor `C(a) - C(O)`
(`WeierstrassCurve.Affine.exists_principal_eq_zsmul_ofPoint_sub_infinity`), is the input of
Bloch's construction of elements of `K₂` of the function field from torsion points: the symbol
`{ρ, f_a}` has nontrivial tame symbols only at the points of `E[C]`, and adding symbols
`{f_P, c_P}` with constants `c_P` to `C{ρ, f_a}` puts it in the kernel of the tame symbol.

The function `ρ` is determined only up to a nonzero constant of `F`, `F` being the exact constant
field of `F(E)`. Its divisor is supported on rational points, so after a change of coefficient
field `f : F →+* K` the image of `ρ` has the transported divisor, and agrees with the function
chosen over `K` up to a nonzero constant of `K`.

## Main definitions

* `WeierstrassCurve.Affine.blochRho`: a choice of function with divisor
  `∑_{a ∈ E[C]} ((O) - (a))`.

## Main results

* `WeierstrassCurve.Affine.principal_blochRho`: when `E[C] ≅ (ℤ/C)²`, the divisor of `ρ` is
  `∑_{a ∈ E[C]} ((O) - (a))`, and `principal_blochRho_eq_sub` restates it as
  `(C² - 1)(O) - ∑_{0 ≠ a ∈ E[C]} (a)`.
* `WeierstrassCurve.Affine.principal_eq_sum_iff_exists_eq_algebraMap_mul_blochRho`: the functions
  with this divisor are exactly the nonzero constant multiples of `ρ`.
* `WeierstrassCurve.Affine.principal_map_blochRho` and
  `WeierstrassCurve.Affine.exists_map_blochRho_eq_algebraMap_mul`: after a change of coefficient
  field, `ρ` has the transported divisor and is a constant multiple of the new choice.

## References

* S. Bloch, *Algebraic K-theory and zeta functions of elliptic curves*, Proceedings of the
  International Congress of Mathematicians (Helsinki, 1978), vol. 2, 1980, p. 514.
* [J. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], III.3.5.
-/

public section

namespace WeierstrassCurve.Affine

open TauCeti AlgebraicGeometry

variable {F : Type*} [Field F] (W : WeierstrassCurve.Affine F) [DecidableEq F] [W.IsElliptic]

section Torsion

variable (C : ℕ) [Fintype (AddSubgroup.torsionBy W.Point (C : ℤ))]

open scoped Classical in
/-- **Bloch's function `ρ` for the `C`-torsion**: a function with divisor
`∑_{a ∈ E[C]} ((O) - (a))`, which is `(C² - 1)(O) - ∑_{0 ≠ a ∈ E[C]} (a)` when `E[C] ≅ (ℤ/C)²`
(`principal_blochRho`, `principal_blochRho_eq_sub`). It is chosen, and is determined up to a nonzero
constant (`principal_eq_sum_iff_exists_eq_algebraMap_mul_blochRho`). When no function has this
divisor it is `1`. -/
noncomputable def blochRho : W.FunctionFieldˣ :=
  if h : ∃ z : W.FunctionFieldˣ, Divisor.principal W.isFunctionField z =
      ∑ a : AddSubgroup.torsionBy W.Point (C : ℤ),
        (WeilDivisor.ofPoint (Place.infinity W) -
          WeilDivisor.ofPoint (W.pointEquivDegreeOnePlace a).val) then h.choose else 1

variable {W C}

/-- **The divisor of Bloch's function**: when `E[C] ≅ (ℤ/C)²`, the divisor of `ρ` is
`∑_{a ∈ E[C]} ((O) - (a))`. -/
theorem principal_blochRho
    (h : Nonempty (AddSubgroup.torsionBy W.Point (C : ℤ) ≃+ ZMod C × ZMod C)) :
    Divisor.principal W.isFunctionField (W.blochRho C) =
      ∑ a : AddSubgroup.torsionBy W.Point (C : ℤ),
        (WeilDivisor.ofPoint (Place.infinity W) -
          WeilDivisor.ofPoint (W.pointEquivDegreeOnePlace a).val) := by
  obtain ⟨e⟩ := h
  -- `E[C]` is finite and `(ℤ/0)² = ℤ²` is not, so `C ≠ 0`
  have : NeZero C := ⟨by
    rintro rfl
    have := Finite.of_equiv _ e.toEquiv
    exact not_finite (ZMod 0 × ZMod 0)⟩
  -- the elements of `(ℤ/C)²` sum to zero, each coordinate appearing `C` times
  have hprod : ∑ b : ZMod C × ZMod C, b = 0 := by
    ext <;> simp [Prod.fst_sum, Prod.snd_sum, Fintype.sum_prod_type]
  have hsum : ∑ a : AddSubgroup.torsionBy W.Point (C : ℤ), (a : W.Point) = 0 := by
    rw [← e.symm.toEquiv.sum_comp]
    simpa [map_sum] using congrArg (fun b ↦ (e.symm b : W.Point)) hprod
  have hex := (W.exists_principal_eq_sum_zsmul_iff Finset.univ (fun _ ↦ -1)
    (fun a : AddSubgroup.torsionBy W.Point (C : ℤ) ↦ (a : W.Point))).2
    (by simp only [neg_one_zsmul, Finset.sum_neg_distrib, hsum, neg_zero])
  simp only [neg_one_zsmul, neg_sub] at hex
  rw [blochRho, dite_eq_left hex]
  exact hex.choose_spec

/-- **The divisor of Bloch's function, in Bloch's form**: when `E[C] ≅ (ℤ/C)²`, the divisor of `ρ`
is `(C² - 1)(O) - ∑_{0 ≠ a ∈ E[C]} (a)`. -/
theorem principal_blochRho_eq_sub
    (h : Nonempty (AddSubgroup.torsionBy W.Point (C : ℤ) ≃+ ZMod C × ZMod C)) :
    Divisor.principal W.isFunctionField (W.blochRho C) =
      ((C : ℤ) ^ 2 - 1) • WeilDivisor.ofPoint (Place.infinity W) -
        ∑ a : AddSubgroup.torsionBy W.Point (C : ℤ) with a ≠ 0,
          WeilDivisor.ofPoint (W.pointEquivDegreeOnePlace a).val := by
  obtain ⟨e⟩ := h
  have hcard : Fintype.card (AddSubgroup.torsionBy W.Point (C : ℤ)) = C ^ 2 := by
    rw [← Nat.card_eq_fintype_card, Nat.card_congr e.toEquiv, Nat.card_prod, Nat.card_zmod, sq]
  -- the `a = 0` term of `∑_{a ∈ E[C]} (a)` is `(O)`
  have h0 : (W.pointEquivDegreeOnePlace
      ((0 : AddSubgroup.torsionBy W.Point (C : ℤ)) : W.Point)).val = Place.infinity W :=
    coe_pointEquivDegreeOnePlace_zero W
  rw [principal_blochRho ⟨e⟩, Finset.sum_sub_distrib, Finset.filter_ne',
    ← Finset.add_sum_erase _ (fun a : AddSubgroup.torsionBy W.Point (C : ℤ) ↦
      WeilDivisor.ofPoint (W.pointEquivDegreeOnePlace a).val) (Finset.mem_univ 0), h0]
  simp [hcard, sub_smul, ← natCast_zsmul]
  abel

/-- **Bloch's function is determined up to a constant**: when `E[C] ≅ (ℤ/C)²`, the functions with
divisor `∑_{a ∈ E[C]} ((O) - (a))` are exactly the nonzero constant multiples of `ρ`, since `F` is
the exact constant field of `F(E)`. -/
theorem principal_eq_sum_iff_exists_eq_algebraMap_mul_blochRho
    (h : Nonempty (AddSubgroup.torsionBy W.Point (C : ℤ) ≃+ ZMod C × ZMod C))
    (z : W.FunctionFieldˣ) :
    Divisor.principal W.isFunctionField z =
        ∑ a : AddSubgroup.torsionBy W.Point (C : ℤ),
          (WeilDivisor.ofPoint (Place.infinity W) -
            WeilDivisor.ofPoint (W.pointEquivDegreeOnePlace a).val) ↔
      ∃ c : Fˣ, (z : W.FunctionField) = algebraMap F W.FunctionField c * W.blochRho C := by
  rw [← principal_blochRho h]
  refine ⟨Divisor.exists_units_algebraMap_mul_of_principal_eq W.isFunctionField
    W.isIntegrallyClosedIn_functionField, fun ⟨c, hc⟩ ↦ ?_⟩
  have hz : z = Units.map (algebraMap F W.FunctionField).toMonoidHom c * W.blochRho C :=
    Units.ext (by simpa using hc)
  rw [hz, Divisor.principal_mul, Divisor.principal_eq_zero_of_isAlgebraic W.isFunctionField
    (isAlgebraic_algebraMap (c : F)), zero_add]

section Map

variable {K : Type*} [Field K] (f : F →+* K)

/-- **The divisor of Bloch's function after a change of coefficient field**: when
`E[C] ≅ (ℤ/C)²` over `F`, the image of `ρ` in `K(E)` has divisor `∑_{a ∈ E[C]} ((O) - (f a))`. -/
theorem principal_map_blochRho
    (h : Nonempty (AddSubgroup.torsionBy W.Point (C : ℤ) ≃+ ZMod C × ZMod C)) :
    Divisor.principal (W.map f).isFunctionField
        (Units.map (FunctionField.map W f).toMonoidHom (W.blochRho C)) =
      ∑ a : AddSubgroup.torsionBy W.Point (C : ℤ),
        (WeilDivisor.ofPoint (Place.infinity (W.map f)) -
          WeilDivisor.ofPoint ((W.map f).pointEquivDegreeOnePlace
            ((a : W.Point).mapAlong f f.injective)).val) := by
  have hρ := principal_blochRho h
  rw [← coe_pointEquivDegreeOnePlace_zero, ← Point.zero_def] at hρ
  have hρ' := FunctionField.principal_map_eq_pushforward W f
    (D := ∑ a : AddSubgroup.torsionBy W.Point (C : ℤ),
      (WeilDivisor.ofPoint 0 - WeilDivisor.ofPoint (a : W.Point)))
    (by simpa only [map_sum, map_sub, WeilDivisor.pushforward_ofPoint] using hρ)
  simp only [map_sum, map_sub, WeilDivisor.pushforward_ofPoint] at hρ'
  rwa [Point.mapAlong_zero, Point.zero_def, coe_pointEquivDegreeOnePlace_zero] at hρ'

/-- **Bloch's function is compatible with a change of coefficient field**: when the `C`-torsion is
`(ℤ/C)²` both over `F` and over `K`, the image of `ρ` in `K(E)` is a nonzero constant multiple of
the function `ρ` chosen over `K`. -/
theorem exists_map_blochRho_eq_algebraMap_mul [DecidableEq K]
    [Fintype (AddSubgroup.torsionBy (W.map f).Point (C : ℤ))]
    (h : Nonempty (AddSubgroup.torsionBy W.Point (C : ℤ) ≃+ ZMod C × ZMod C))
    (hK : Nonempty (AddSubgroup.torsionBy (W.map f).Point (C : ℤ) ≃+ ZMod C × ZMod C)) :
    ∃ c : Kˣ, FunctionField.map W f (W.blochRho C) =
      algebraMap K (W.map f).FunctionField c * (W.map f).blochRho C := by
  obtain ⟨e⟩ := h
  obtain ⟨eK⟩ := hK
  -- the torsion map `E[C](F) → E[C](K)` is injective between sets of `C²` elements
  let g : AddSubgroup.torsionBy W.Point (C : ℤ) → AddSubgroup.torsionBy (W.map f).Point (C : ℤ) :=
    WeierstrassCurve.torsionMapAlong W f C
  have hg : Function.Bijective g := by
    refine (Fintype.bijective_iff_injective_and_card g).2
      ⟨WeierstrassCurve.torsionMapAlong_injective W f C, ?_⟩
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, Nat.card_congr e.toEquiv,
      Nat.card_congr eK.toEquiv]
  have hdiv := principal_map_blochRho f ⟨e⟩
  rw [Fintype.sum_bijective g hg _ (fun b ↦ WeilDivisor.ofPoint (Place.infinity (W.map f)) -
    WeilDivisor.ofPoint ((W.map f).pointEquivDegreeOnePlace (b : (W.map f).Point)).val)
    fun _ ↦ by rw [WeierstrassCurve.coe_torsionMapAlong_apply], ← principal_blochRho ⟨eK⟩] at hdiv
  simpa using Divisor.exists_units_algebraMap_mul_of_principal_eq (W.map f).isFunctionField
    (W.map f).isIntegrallyClosedIn_functionField hdiv

end Map

end Torsion

end WeierstrassCurve.Affine

end
