/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.GaloisCohomology.WeilPairing.Cohomology
public import TauCeti.AlgebraicGeometry.EllipticCurve.GaloisCohomology.Descent
public import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.MulByInt.WeilPairing.Galois
public import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.MulByInt.Surjective
public import TauCeti.AlgebraicGeometry.EllipticCurve.Affine.FunctionField.Translation.Place
public import TauCeti.FieldTheory.GaloisCohomology.BrauerTorsion
import TauCeti.AlgebraicGeometry.EllipticCurve.Affine.FunctionField.Genus
import TauCeti.FieldTheory.FunctionField.Divisor.Automorphism

/-!
# Kummer classes are isotropic for the Weil cup product

Let `E` be an elliptic curve over a field `K` and `m` an integer invertible in `K`. The Kummer map
`δ : E(K) → H¹(K, E[m])` and the cup product along the Weil pairing
`e_m : E[m] × E[m] → μ_m` combine into a pairing `E(K) × E(K) → H²(K, μ_m)`. This file proves
that it vanishes: the image of the Kummer map is isotropic for the Weil cup product,

`δ P ∪ δ Q = 0` for all `P, Q ∈ E(K)`

(`WeierstrassCurve.torsionH1WeilPairing_kummerMap_kummerMap_eq_zero`). Over a nonarchimedean local
field it says that the local condition `δ(E(K))` of the `m`-Selmer group is isotropic for local
Tate duality (`WeierstrassCurve.localTateWeilPairing_kummerMap_kummerMap_eq_zero`); there it is
half of the statement that this local condition is its own annihilator.

## Main results

* `WeierstrassCurve.torsionH1WeilPairing_kummerMap_kummerMap_eq_zero`: the cup product of two
  Kummer classes along the Weil pairing vanishes in `H²(K, μ_m)`.

## Implementation notes

Write `Kˢ` for the separable closure of `K`, `G_K` for its Galois group, `[m]^*` for pullback of
divisors along multiplication by `m`, and `τ_S^*` for translation by `S` on functions. The Weil
pairing is `e_m(S, T) = τ_S^* g / g` for any `g` with divisor `[m]^* (T) - [m]^* (O)`
(`TauCeti.Isogeny.weilPairing`).

For a point `R` of `E(Kˢ)` with `m² R ∈ E(K)`, fix a function `f` with divisor
`[m]^* (-m R) - [m]^* (O) - ((-m² R) - (O))`. Then `g(σ) = τ_{-R}^* (σ f / f)` has divisor
`[m]^* (-m a(σ)) - [m]^* (O)`, where `a(σ) = σ R - R`, and
`g(σ τ) = g(σ) · τ_{a(σ)}^* σ(g(τ))`. Read in the group of pairs `(S, g)` with
`div g = [m]^* (-m S) - [m]^* (O)`, multiplied by `(S, g) (S', g') = (S + S', g · τ_S^* g')`, this
says that `σ ↦ (a(σ), g(σ))` is a cocycle lifting `a`; and the commutator of `(S, c)` and
`(S', g')` for `S ∈ E[m]` is the Weil pairing value `τ_S^* g' / g'`.

Let `P' ∈ E(Kˢ)` with `m P' = P`, let `Q' ∈ E(Kˢ)` with `m Q' = Q`, and let `R ∈ E(Kˢ)` with
`m R = -Q'`. The lifts `g₁`, `g₂`, `g₃` attached to `P'`, `R` and `P' + R` lift the Kummer
cocycles of `m P`, `-Q` and `m P - Q` for multiplication by `m²`. The lift `g₁` is constant, and
`g₁ g₂ = c · g₃` for a cochain `c : G_K → (Kˢ)ˣ`; comparing the cocycle identities shows that the
coboundary of `c` is the cup cocycle `(σ, τ) ↦ e_m(σ P' - P', σ (τ Q' - Q'))`. The cochain `c` is
continuous, being constant on the cosets of the open subgroup fixing finitely many elements of
`Kˢ`. So the cup product vanishes in `H²(K, (Kˢ)ˣ)`, hence in `H²(K, μ_m)`, which injects into it
by Hilbert's theorem 90.

This is the theta-group argument: the obstruction to lifting a class of `H¹(K, E[m])` to a Mumford
theta group is a quadratic refinement of the Weil cup product, and it vanishes on Kummer classes.

## References

* Yu. G. Zarhin, *Noncommutative cohomology and Mumford groups*, Math. Notes 15 (1974), 241–244.
* B. Poonen and E. Rains, *Self cup products and the theta characteristic torsor*, Math. Res.
  Lett. 18 (2011), 1305–1318, §4.
* J. S. Milne, *Arithmetic Duality Theorems*, 2nd ed., I §3.
* [J. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], III.8 and X.1.
-/

public section

noncomputable section

open TauCeti TauCeti.Isogeny TauCeti.ContCohomology AlgebraicGeometry
open scoped WeierstrassCurve Pointwise

namespace WeierstrassCurve

open WeierstrassCurve.Affine

section Lift

variable {F K : Type*} [Field F] [Field K] [DecidableEq K] [Algebra F K] [IsSepClosed K]
  (W : WeierstrassCurve F) [W.IsElliptic]

attribute [local instance] WeierstrassCurve.Affine.isIntegrallyClosedIn_functionField

variable {n : ℤ} (hn : (n : K) ≠ 0)

/-- **The translate of a difference of Weil-pairing divisors.** -/
private theorem translation_smul_weilPairingDivisor_sub (X T₁ T₂ : (W⁄K).toAffine.Point) :
    Affine.translation (W⁄K).toAffine (Affine.Point.equivBaseChangeSelf _ X) •
        (weilPairingDivisor (W⁄K) (psiFunctionField_ne_zero (W⁄K) hn) T₁ -
          weilPairingDivisor (W⁄K) (psiFunctionField_ne_zero (W⁄K) hn) T₂) =
      weilPairingDivisor (W⁄K) (psiFunctionField_ne_zero (W⁄K) hn) (T₁ - n • X) -
        weilPairingDivisor (W⁄K) (psiFunctionField_ne_zero (W⁄K) hn) (T₂ - n • X) := by
  obtain ⟨R₁, hR₁⟩ := (W⁄K).toAffine.zsmul_surjective hn T₁
  obtain ⟨R₂, hR₂⟩ := (W⁄K).toAffine.zsmul_surjective hn T₂
  have h₁ : n • (R₁ - X) = T₁ - n • X := by rw [smul_sub]; exact congrArg (· - n • X) hR₁
  have h₂ : n • (R₂ - X) = T₂ - n • X := by rw [smul_sub]; exact congrArg (· - n • X) hR₂
  rw [weilPairingDivisor_eq_sum (W⁄K) hn hR₁, weilPairingDivisor_eq_sum (W⁄K) hn hR₂,
    weilPairingDivisor_eq_sum (W⁄K) hn h₁, weilPairingDivisor_eq_sum (W⁄K) hn h₂,
    ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib, Finset.smul_sum]
  refine Finset.sum_congr rfl fun S _ ↦ ?_
  simp only [sub_sub_sub_cancel_right, smul_sub, WeilDivisor.smul_ofPoint,
    translation_smul_pointEquivDegreeOnePlace, sub_add_eq_add_sub]

/-- The divisor of the auxiliary function of the lift attached to `R`. -/
private abbrev liftDivisor (R : (W⁄K).toAffine.Point) : Divisor K (W⁄K).toAffine.FunctionField :=
  weilPairingDivisor (W⁄K) (psiFunctionField_ne_zero (W⁄K) hn) (-(n • R)) -
    (WeilDivisor.ofPoint ((W⁄K).toAffine.pointEquivDegreeOnePlace (-(n • n • R))).1 -
      WeilDivisor.ofPoint ((W⁄K).toAffine.pointEquivDegreeOnePlace 0).1)

/-- `[n]^* (-n R) - [n]^* (O) - ((-n² R) - (O))` is principal: its sum is `n² (-R) + n² R = O`. -/
private theorem exists_principal_eq_liftDivisor (R : (W⁄K).toAffine.Point) :
    ∃ f : (W⁄K).toAffine.FunctionFieldˣ,
      Divisor.principal (W⁄K).toAffine.isFunctionField f = liftDivisor W hn R := by
  have hR : n • -R = -(n • R) := smul_neg n R
  rw [liftDivisor, weilPairingDivisor_eq_sum (W⁄K) hn hR]
  set s₀ := (finite_setOf_zsmul_eq (W⁄K) (psiFunctionField_ne_zero (W⁄K) hn) 0).toFinset with hs₀
  let D : (Divisor.degree (k := K) (F := (W⁄K).toAffine.FunctionField)).ker :=
    ∑ S ∈ s₀, ⟨_, (W⁄K).toAffine.ofPoint_sub_ofPoint_mem_ker_degree (-R + S) S⟩ -
      ⟨_, (W⁄K).toAffine.ofPoint_sub_ofPoint_mem_ker_degree (-(n • n • R)) 0⟩
  have hσ : (W⁄K).toAffine.divisorSum D = 0 := by
    simp only [D, map_sub, map_sum, divisorSum_ofPoint_sub_ofPoint, add_sub_cancel_right,
      Finset.sum_const, sub_zero, sub_neg_eq_add]
    rw [hs₀, ← Nat.card_eq_card_finite_toFinset, (W⁄K).toAffine.natCard_setOf_zsmul_eq_zero hn,
      ← natCast_zsmul, Nat.cast_pow, Int.natAbs_sq, sq, mul_smul, smul_neg, smul_neg,
      neg_add_cancel]
  obtain ⟨z, hz⟩ := (W⁄K).toAffine.divisorSum_eq_zero_iff.mp hσ
  exact ⟨z, hz.trans (by simp [D])⟩

/-- **The lift of a Kummer cocycle to functions**: `σ ↦ τ_{-R}^* (σ f / f)`. -/
private def lift (f : (W⁄K).toAffine.FunctionFieldˣ) (R : (W⁄K).toAffine.Point) (σ : K ≃ₐ[F] K) :
    (W⁄K).toAffine.FunctionFieldˣ :=
  Units.map (Affine.translation (W⁄K).toAffine (Affine.Point.equivBaseChangeSelf _ (-R)) :
      (W⁄K).toAffine.FunctionField →* (W⁄K).toAffine.FunctionField)
    (Units.map (MonoidHom.ofClass (W.functionFieldGaloisAction σ)) f / f)

omit [IsSepClosed K] in
private theorem coe_lift (f : (W⁄K).toAffine.FunctionFieldˣ) (R : (W⁄K).toAffine.Point)
    (σ : K ≃ₐ[F] K) :
    (lift W f R σ : (W⁄K).toAffine.FunctionField) =
      Affine.translation (W⁄K).toAffine (Affine.Point.equivBaseChangeSelf _ (-R))
        (W.functionFieldGaloisAction σ f / f) := by
  simp [lift]

/-- **The divisor of the lift** is `[n]^* (-n (σ R - R)) - [n]^* (O)`, when `σ` fixes `n² R`. -/
private theorem principal_lift {f : (W⁄K).toAffine.FunctionFieldˣ} {R : (W⁄K).toAffine.Point}
    (hf : Divisor.principal (W⁄K).toAffine.isFunctionField f = liftDivisor W hn R)
    {σ : K ≃ₐ[F] K}
    (hσ : Multiplicative.toAdd (W.pointGaloisAction σ) (n • n • R) = n • n • R) :
    Divisor.principal (W⁄K).toAffine.isFunctionField (lift W f R σ) =
      weilPairingDivisor (W⁄K) (psiFunctionField_ne_zero (W⁄K) hn)
        (-(n • (Multiplicative.toAdd (W.pointGaloisAction σ) R - R))) := by
  have h0 : Multiplicative.toAdd (W.pointGaloisAction σ) 0 = 0 := map_zero _
  have hgal : Multiplicative.toAdd (W.divisorGaloisAction σ) (liftDivisor W hn R) =
      weilPairingDivisor (W⁄K) (psiFunctionField_ne_zero (W⁄K) hn)
          (Multiplicative.toAdd (W.pointGaloisAction σ) (-(n • R))) -
        (WeilDivisor.ofPoint ((W⁄K).toAffine.pointEquivDegreeOnePlace (-(n • n • R))).1 -
          WeilDivisor.ofPoint ((W⁄K).toAffine.pointEquivDegreeOnePlace 0).1) := by
    rw [liftDivisor, map_sub, map_sub, divisorGaloisAction_weilPairingDivisor W σ hn,
      divisorGaloisAction_ofPoint, divisorGaloisAction_ofPoint,
      placeGaloisAction_pointEquivDegreeOnePlace, placeGaloisAction_pointEquivDegreeOnePlace,
      map_neg (Multiplicative.toAdd (W.pointGaloisAction σ)) (n • n • R), hσ, h0]
  have h₁ : Multiplicative.toAdd (W.pointGaloisAction σ) (-(n • R)) - n • -R =
      -(n • (Multiplicative.toAdd (W.pointGaloisAction σ) R - R)) := by
    rw [map_neg, map_zsmul, smul_neg, smul_sub]
    abel
  have h₂ : -(n • R) - n • -R = 0 := by
    rw [smul_neg, sub_neg_eq_add, neg_add_cancel]
  rw [lift, Divisor.principal_smul, Divisor.principal_div, divisorGaloisAction_principal, hf, hgal,
    liftDivisor, sub_sub_sub_cancel_right, translation_smul_weilPairingDivisor_sub W hn, h₁, h₂,
    weilPairingDivisor_zero, sub_zero]

omit [IsSepClosed K] in
/-- **The lift is a cocycle** for the multiplication `(a, g) (b, h) = (a + b, g τ_a^* h)`. -/
private theorem lift_mul (f : (W⁄K).toAffine.FunctionFieldˣ) (R : (W⁄K).toAffine.Point)
    (σ τ : K ≃ₐ[F] K) :
    (lift W f R (σ * τ) : (W⁄K).toAffine.FunctionField) =
      lift W f R σ * Affine.translation (W⁄K).toAffine (Affine.Point.equivBaseChangeSelf _
        (Multiplicative.toAdd (W.pointGaloisAction σ) R - R))
          (W.functionFieldGaloisAction σ (lift W f R τ)) := by
  have hf : (f : (W⁄K).toAffine.FunctionField) ≠ 0 := f.ne_zero
  have hσf : W.functionFieldGaloisAction σ f ≠ 0 := by simp
  -- translating by `σ R - R` after the conjugate translation by `-σ R` is translating by `-R`
  have key (z : (W⁄K).toAffine.FunctionField) :
      Affine.translation (W⁄K).toAffine (Affine.Point.equivBaseChangeSelf _
          (Multiplicative.toAdd (W.pointGaloisAction σ) R - R))
        (Affine.translation (W⁄K).toAffine (Affine.Point.equivBaseChangeSelf _
          (Multiplicative.toAdd (W.pointGaloisAction σ) (-R))) z) =
        Affine.translation (W⁄K).toAffine (Affine.Point.equivBaseChangeSelf _ (-R)) z := by
    have h : Multiplicative.toAdd (W.pointGaloisAction σ) (-R) +
        (Multiplicative.toAdd (W.pointGaloisAction σ) R - R) = -R := by
      rw [map_neg]
      abel
    rw [← AlgEquiv.trans_apply, ← Affine.translation_add, ← map_add, h]
  rw [coe_lift, coe_lift, coe_lift, functionFieldGaloisAction_translation, key, map_mul,
    RingAut.mul_apply, ← map_mul,
    map_div₀ (W.functionFieldGaloisAction σ)]
  congr 1
  field_simp

omit [IsSepClosed K] in
/-- The lift is trivial at an automorphism fixing both `f` and `R`. -/
private theorem lift_eq_one {f : (W⁄K).toAffine.FunctionFieldˣ} {R : (W⁄K).toAffine.Point}
    {σ : K ≃ₐ[F] K} (hf : W.functionFieldGaloisAction σ f = f) : lift W f R σ = 1 :=
  Units.ext (by rw [coe_lift, hf, div_self f.ne_zero, map_one, Units.val_one])

end Lift

section Cochain

variable {F K : Type*} [Field F] [Field K] [DecidableEq K] [Algebra F K] [IsSepClosed K]
  (W : WeierstrassCurve F) [W.IsElliptic] (N : ℕ) [NeZero N] (hN : (N : K) ≠ 0)

attribute [local instance] WeierstrassCurve.Affine.isIntegrallyClosedIn_functionField

/-- **The cup cocycle of two Kummer cocycles is a coboundary in `Kˣ`.** If `N • P` and `N • Q` are
fixed by every automorphism, there is a cochain `c` with
`c(σ) · σ(c(τ)) = c(σ τ) · e_N(σ P - P, σ (τ Q - Q))`, constant on the cosets of the subgroup
fixing some finite set. -/
private theorem exists_cochain (P Q : (W⁄K).toAffine.Point)
    (hP : ∀ σ : K ≃ₐ[F] K, Multiplicative.toAdd (W.pointGaloisAction σ) (N • P) = N • P)
    (hQ : ∀ σ : K ≃ₐ[F] K, Multiplicative.toAdd (W.pointGaloisAction σ) (N • Q) = N • Q) :
    ∃ c : (K ≃ₐ[F] K) → Kˣ,
      (∀ (σ τ : K ≃ₐ[F] K) (S T : Submodule.torsionBy ℤ (W⁄K).toAffine.Point (N : ℤ)),
        (S : (W⁄K).toAffine.Point) = Multiplicative.toAdd (W.pointGaloisAction σ) P - P →
        (T : (W⁄K).toAffine.Point) = Multiplicative.toAdd (W.pointGaloisAction σ)
          (Multiplicative.toAdd (W.pointGaloisAction τ) Q - Q) →
        (c σ : K) * σ (c τ) =
          (c (σ * τ) : K) * (((weilPairing (W⁄K) N hN S T).toMul : Kˣ) : K)) ∧
      ∃ s : Finset K, ∀ σ u : K ≃ₐ[F] K, (∀ x ∈ s, u x = x) → c (σ * u) = c σ := by
  -- Structure: lift the points `P`, `R` (with `N R = -Q`) and `P + R` to functions `g₁, g₂, g₃`
  -- (`lift`), compute their divisors, define `c` by `g₁ g₂ = c g₃`, derive the cocycle identity
  -- `hid` from the three `lift_mul` identities, and finally show `c` is locally constant.
  classical
  have hn : ((N : ℤ) : K) ≠ 0 := by exact_mod_cast hN
  set e : (K ≃ₐ[F] K) → (W⁄K).toAffine.Point ≃+ (W⁄K).toAffine.Point :=
    fun σ ↦ Multiplicative.toAdd (W.pointGaloisAction σ) with he
  set n : ℤ := (N : ℤ) with hn_def
  have hP' (σ : K ≃ₐ[F] K) : e σ (n • P) = n • P := by
    rw [hn_def, natCast_zsmul]; exact hP σ
  have hQ' (σ : K ≃ₐ[F] K) : e σ (n • Q) = n • Q := by
    rw [hn_def, natCast_zsmul]; exact hQ σ
  obtain ⟨R, hR⟩ := (W⁄K).toAffine.zsmul_surjective hn (-Q)
  replace hR : n • R = -Q := hR
  have hfix₁ (σ : K ≃ₐ[F] K) : e σ (n • n • P) = n • n • P := by rw [map_zsmul, hP']
  have hfix₂ (σ : K ≃ₐ[F] K) : e σ (n • n • R) = n • n • R := by
    rw [hR, smul_neg, map_neg, hQ']
  have hfix₃ (σ : K ≃ₐ[F] K) : e σ (n • n • (P + R)) = n • n • (P + R) := by
    rw [smul_add, smul_add, map_add, hfix₁, hfix₂]
  obtain ⟨f₁, hf₁⟩ := exists_principal_eq_liftDivisor W hn P
  obtain ⟨f₂, hf₂⟩ := exists_principal_eq_liftDivisor W hn R
  obtain ⟨f₃, hf₃⟩ := exists_principal_eq_liftDivisor W hn (P + R)
  have ha₁ (σ : K ≃ₐ[F] K) : -(n • (e σ P - P)) = 0 := by
    rw [smul_sub, ← map_zsmul, hP', sub_self, neg_zero]
  have ha₂ (σ : K ≃ₐ[F] K) : -(n • (e σ R - R)) = e σ Q - Q := by
    rw [smul_sub, ← map_zsmul, hR, map_neg]
    abel
  have ha₃ (σ : K ≃ₐ[F] K) : -(n • (e σ (P + R) - (P + R))) = e σ Q - Q := by
    rw [map_add, add_sub_add_comm, smul_add, neg_add, ha₁, ha₂, zero_add]
  have hd₁ (σ : K ≃ₐ[F] K) :
      Divisor.principal (W⁄K).toAffine.isFunctionField (lift W f₁ P σ) = 0 := by
    rw [principal_lift W hn hf₁ (hfix₁ σ)]
    exact (congrArg _ (ha₁ σ)).trans (weilPairingDivisor_zero _ _)
  have hd₂ (σ : K ≃ₐ[F] K) :
      Divisor.principal (W⁄K).toAffine.isFunctionField (lift W f₂ R σ) =
        weilPairingDivisor (W⁄K) (psiFunctionField_ne_zero (W⁄K) hn) (e σ Q - Q) := by
    rw [principal_lift W hn hf₂ (hfix₂ σ)]
    exact congrArg _ (ha₂ σ)
  have hd₃ (σ : K ≃ₐ[F] K) :
      Divisor.principal (W⁄K).toAffine.isFunctionField (lift W f₃ (P + R) σ) =
        weilPairingDivisor (W⁄K) (psiFunctionField_ne_zero (W⁄K) hn) (e σ Q - Q) := by
    rw [principal_lift W hn hf₃ (hfix₃ σ)]
    exact congrArg _ (ha₃ σ)
  -- the first lift is constant, and the product of the first two differs from the third by a
  -- constant
  have hc₁ (σ : K ≃ₐ[F] K) : ∃ c : Kˣ,
      (lift W f₁ P σ : (W⁄K).toAffine.FunctionField) =
        algebraMap K (W⁄K).toAffine.FunctionField c := by
    obtain ⟨c, hc⟩ := Divisor.exists_units_algebraMap_mul_of_principal_eq
      (W⁄K).toAffine.isFunctionField inferInstance (y := lift W f₁ P σ) (z := 1)
      (by rw [hd₁, Divisor.principal_one])
    exact ⟨c, by rw [hc, Units.val_one, mul_one]⟩
  have hc (σ : K ≃ₐ[F] K) : ∃ c : Kˣ,
      (lift W f₁ P σ * lift W f₂ R σ : (W⁄K).toAffine.FunctionField) =
        algebraMap K (W⁄K).toAffine.FunctionField c * lift W f₃ (P + R) σ := by
    obtain ⟨c, hc⟩ := Divisor.exists_units_algebraMap_mul_of_principal_eq
      (W⁄K).toAffine.isFunctionField inferInstance
      (y := lift W f₁ P σ * lift W f₂ R σ) (z := lift W f₃ (P + R) σ)
      (by rw [Divisor.principal_mul, hd₁, hd₂, hd₃, zero_add])
    exact ⟨c, by rw [← hc, Units.val_mul]⟩
  choose c₁ hc₁ using hc₁
  choose c hc using hc
  have hid (σ τ : K ≃ₐ[F] K) (S T : Submodule.torsionBy ℤ (W⁄K).toAffine.Point (N : ℤ))
      (hS : (S : (W⁄K).toAffine.Point) = e σ P - P)
      (hT : (T : (W⁄K).toAffine.Point) = e σ (e τ Q - Q)) :
      (c σ : K) * σ (c τ) =
        (c (σ * τ) : K) * (((weilPairing (W⁄K) N hN S T).toMul : Kˣ) : K) := by
    have hcommute (Z : (W⁄K).toAffine.Point) (x : K) :
        Affine.translation (W⁄K).toAffine (Affine.Point.equivBaseChangeSelf _ Z)
          (algebraMap K (W⁄K).toAffine.FunctionField x) =
          algebraMap K (W⁄K).toAffine.FunctionField x :=
      (Affine.translation (W⁄K).toAffine _).commutes x
    -- the conjugate `H` of the second lift at `τ` has divisor `[N]^* (T) - [N]^* (O)`
    set Hu := Units.map (MonoidHom.ofClass (W.functionFieldGaloisAction σ)) (lift W f₂ R τ)
    have hHu : Divisor.principal (W⁄K).toAffine.isFunctionField Hu =
        weilPairingDivisor (W⁄K) (psiFunctionField_ne_zero (W⁄K) hn) T := by
      rw [divisorGaloisAction_principal, hd₂, divisorGaloisAction_weilPairingDivisor W σ hn, hT]
    set E := algebraMap K (W⁄K).toAffine.FunctionField
      (((weilPairing (W⁄K) N hN S T).toMul : Kˣ) : K) with hE_def
    have hSH : Affine.translation (W⁄K).toAffine (Affine.Point.equivBaseChangeSelf _ S)
        (W.functionFieldGaloisAction σ (lift W f₂ R τ)) =
        E * W.functionFieldGaloisAction σ (lift W f₂ R τ) := by
      have hE := algebraMap_weilPairing (W⁄K) N hN hHu (S := S)
      rw [← hE_def, eq_div_iff (Units.ne_zero Hu)] at hE
      exact hE.symm
    -- `X` is the translate by `σ R - R` of `H`
    have hX : Affine.translation (W⁄K).toAffine (Affine.Point.equivBaseChangeSelf _ (e σ R - R))
        (W.functionFieldGaloisAction σ (lift W f₂ R τ)) ≠ 0 := by simp
    have h3H : Affine.translation (W⁄K).toAffine
        (Affine.Point.equivBaseChangeSelf _ (e σ (P + R) - (P + R)))
          (W.functionFieldGaloisAction σ (lift W f₂ R τ)) =
        E * Affine.translation (W⁄K).toAffine (Affine.Point.equivBaseChangeSelf _ (e σ R - R))
          (W.functionFieldGaloisAction σ (lift W f₂ R τ)) := by
      have hS' : e σ (P + R) - (P + R) = S + (e σ R - R) := by
        rw [hS, map_add]
        abel
      rw [hS', map_add, Affine.translation_add, AlgEquiv.trans_apply, hSH, map_mul, hE_def,
        hcommute]
    -- the three cocycle identities at `(σ, τ)`
    have m₁ : (lift W f₁ P (σ * τ) : (W⁄K).toAffine.FunctionField) =
        lift W f₁ P σ * algebraMap K (W⁄K).toAffine.FunctionField (σ (c₁ τ)) := by
      rw [lift_mul, hc₁ τ, functionFieldGaloisAction_algebraMap, hcommute]
    have m₂ : (lift W f₂ R (σ * τ) : (W⁄K).toAffine.FunctionField) =
        lift W f₂ R σ * Affine.translation (W⁄K).toAffine
          (Affine.Point.equivBaseChangeSelf _ (e σ R - R))
            (W.functionFieldGaloisAction σ (lift W f₂ R τ)) :=
      lift_mul W f₂ R σ τ
    have m₃ : (lift W f₃ (P + R) (σ * τ) : (W⁄K).toAffine.FunctionField) *
          algebraMap K (W⁄K).toAffine.FunctionField (σ (c τ)) =
        lift W f₃ (P + R) σ * (algebraMap K (W⁄K).toAffine.FunctionField (σ (c₁ τ)) * E *
          Affine.translation (W⁄K).toAffine (Affine.Point.equivBaseChangeSelf _ (e σ R - R))
            (W.functionFieldGaloisAction σ (lift W f₂ R τ))) := by
      -- conjugate and translate `c₁(τ) g₂(τ) = c(τ) g₃(τ)`
      have h := congrArg (fun z ↦ Affine.translation (W⁄K).toAffine
        (Affine.Point.equivBaseChangeSelf _ (e σ (P + R) - (P + R)))
          (W.functionFieldGaloisAction σ z)) (hc τ)
      simp only [map_mul, hc₁ τ, functionFieldGaloisAction_algebraMap, hcommute, h3H] at h
      rw [lift_mul, mul_assoc, mul_comm (Affine.translation _ _ _), ← h]
      ring
    have key := hc (σ * τ)
    rw [m₁, m₂] at key
    apply (algebraMap K (W⁄K).toAffine.FunctionField).injective
    simp only [map_mul]
    have hG : (lift W f₃ (P + R) σ : (W⁄K).toAffine.FunctionField) ≠ 0 := Units.ne_zero _
    have hD : algebraMap K (W⁄K).toAffine.FunctionField (σ (c₁ τ)) ≠ 0 := by simp
    have hzero : (algebraMap K (W⁄K).toAffine.FunctionField (c σ) *
          algebraMap K (W⁄K).toAffine.FunctionField (σ (c τ)) -
        algebraMap K (W⁄K).toAffine.FunctionField (c (σ * τ)) * E) *
        ((lift W f₃ (P + R) σ : (W⁄K).toAffine.FunctionField) *
          algebraMap K (W⁄K).toAffine.FunctionField (σ (c₁ τ)) *
          Affine.translation (W⁄K).toAffine (Affine.Point.equivBaseChangeSelf _ (e σ R - R))
            (W.functionFieldGaloisAction σ (lift W f₂ R τ))) = 0 := by
      linear_combination (-(algebraMap K (W⁄K).toAffine.FunctionField (σ (c₁ τ)) *
          Affine.translation (W⁄K).toAffine (Affine.Point.equivBaseChangeSelf _ (e σ R - R))
            (W.functionFieldGaloisAction σ (lift W f₂ R τ)) *
          algebraMap K (W⁄K).toAffine.FunctionField (σ (c τ)))) * hc σ +
        algebraMap K (W⁄K).toAffine.FunctionField (σ (c τ)) * key +
        algebraMap K (W⁄K).toAffine.FunctionField (c (σ * τ)) * m₃
    rcases mul_eq_zero.1 hzero with h | h
    · exact sub_eq_zero.1 h
    · exact absurd h (mul_ne_zero (mul_ne_zero hG hD) hX)
  refine ⟨c, hid, ?_⟩
  -- `c` is trivial on the automorphisms fixing `P`, `Q`, `R` and the three auxiliary functions,
  -- and the cocycle identity then makes it constant on their cosets
  obtain ⟨sP, hsP⟩ := W.exists_finset_pointGaloisAction_eq_self P
  obtain ⟨sQ, hsQ⟩ := W.exists_finset_pointGaloisAction_eq_self Q
  obtain ⟨s₁, hs₁⟩ :=
    W.exists_finset_functionFieldGaloisAction_eq_self (f₁ : (W⁄K).toAffine.FunctionField)
  obtain ⟨s₂, hs₂⟩ :=
    W.exists_finset_functionFieldGaloisAction_eq_self (f₂ : (W⁄K).toAffine.FunctionField)
  obtain ⟨s₃, hs₃⟩ :=
    W.exists_finset_functionFieldGaloisAction_eq_self (f₃ : (W⁄K).toAffine.FunctionField)
  refine ⟨sP ∪ sQ ∪ s₁ ∪ s₂ ∪ s₃, fun σ u hu ↦ ?_⟩
  simp only [Finset.mem_union, or_imp, forall_and] at hu
  obtain ⟨⟨⟨⟨huP, huQ⟩, hu₁⟩, hu₂⟩, hu₃⟩ := hu
  have hcu : c u = 1 := by
    have h := hc u
    rw [lift_eq_one W (hs₁ u hu₁), lift_eq_one W (hs₂ u hu₂), lift_eq_one W (hs₃ u hu₃),
      Units.val_one, mul_one, mul_one, eq_comm, ← map_one (algebraMap K _)] at h
    exact Units.ext ((algebraMap K _).injective h)
  have hS : N • (e σ P - P) = 0 := by
    rw [smul_sub, ← map_nsmul, hP, sub_self]
  have h := hid σ u ⟨e σ P - P, (Submodule.mem_torsionBy_iff _ _).2 (by
      rw [natCast_zsmul]; exact hS)⟩ 0 rfl (by
      rw [Submodule.coe_zero, hsQ u huQ, sub_self, map_zero])
  rw [hcu, Units.val_one, map_one, mul_one, map_zero, toMul_zero, OneMemClass.coe_one,
    Units.val_one, mul_one] at h
  exact Units.ext h.symm

end Cochain

section Isotropy

variable {K : Type*} [Field K] [DecidableEq K] (W : WeierstrassCurve K) [W.IsElliptic] (m : ℕ)
  (hm : IsUnit (m : K))

/-- **Kummer classes are isotropic for the Weil cup product**: for all points `P` and `Q` of
`E(K)`, the cup product of their Kummer classes along the Weil pairing vanishes in `H²(K, μ_m)`,
for every `m` invertible in `K`. -/
theorem torsionH1WeilPairing_kummerMap_kummerMap_eq_zero (P Q : W.toAffine.Point) :
    W.torsionH1WeilPairing m hm (W.kummerMap m hm P) (W.kummerMap m hm Q) = 0 := by
  classical
  have := hm.neZero_natCast
  have hm' : (m : SeparableClosure K) ≠ 0 := hm.natCast_ne_zero_of_algebra
  -- the `m`-division points of `P` and `Q` over the separable closure
  obtain ⟨P₁, hP₁⟩ := (W⁄(SeparableClosure K)).toAffine.nsmul_surjective hm'
    (W.pointCoeffEquiv.symm (W.basePointCoeff P))
  obtain ⟨Q₁, hQ₁⟩ := (W⁄(SeparableClosure K)).toAffine.nsmul_surjective hm'
    (W.pointCoeffEquiv.symm (W.basePointCoeff Q))
  replace hP₁ : m • P₁ = W.pointCoeffEquiv.symm (W.basePointCoeff P) := hP₁
  replace hQ₁ : m • Q₁ = W.pointCoeffEquiv.symm (W.basePointCoeff Q) := hQ₁
  have hP₁' : m • W.pointCoeffEquiv P₁ = W.basePointCoeff P := by
    rw [← map_nsmul, hP₁, AddEquiv.apply_symm_apply]
  have hQ₁' : m • W.pointCoeffEquiv Q₁ = W.basePointCoeff Q := by
    rw [← map_nsmul, hQ₁, AddEquiv.apply_symm_apply]
  have hfix (R : W.toAffine.Point) (σ : AbsoluteGaloisGroup K) :
      Multiplicative.toAdd (W.pointGaloisAction σ) (W.pointCoeffEquiv.symm (W.basePointCoeff R)) =
        W.pointCoeffEquiv.symm (W.basePointCoeff R) := by
    rw [pointGaloisAction_apply_eq_smul, AddEquiv.apply_symm_apply, smul_basePointCoeff]
  obtain ⟨c, hc, s, hs⟩ := exists_cochain W m hm' P₁ Q₁ (fun σ ↦ hP₁ ▸ hfix P σ)
    (fun σ ↦ hQ₁ ▸ hfix Q σ)
  rw [kummerMap_eq_H1pi hm hP₁', kummerMap_eq_H1pi hm hQ₁', torsionH1WeilPairing_eq_explicitCup11,
    QuotientAddGroup.mk'_apply, QuotientAddGroup.mk'_apply, explicitCup11_mk]
  -- the cup product becomes a coboundary in `(Kˢ)ˣ`, which detects the zero class
  apply explicitCoeff2_kummerShortExact_incl_injective K hm
  rw [map_zero, explicitCoeff2_mk, H2pi_eq_zero_iff, mem_B2_iff']
  refine ⟨fun σ ↦ Additive.ofMul (c σ), ?_, fun σ τ ↦ ?_⟩
  · -- `c` is constant on the cosets of the open subgroup fixing the finite set `s`
    refine continuous_discrete_rng.2 fun b ↦ isOpen_iff_forall_mem_open.2 fun σ hσ ↦ ?_
    let V : Set (AbsoluteGaloisGroup K) :=
      ⋂ x ∈ s, (MulAction.stabilizer (AbsoluteGaloisGroup K) x : Set (AbsoluteGaloisGroup K))
    have hV : IsOpen V := isOpen_biInter_finset fun x _ ↦ stabilizer_isOpen_of_isIntegral x
    refine ⟨σ • V, ?_, hV.leftCoset σ, ⟨1, by simp [V], mul_one σ⟩⟩
    rintro _ ⟨u, hu, rfl⟩
    simp only [V, Set.mem_iInter, SetLike.mem_coe, MulAction.mem_stabilizer_iff,
      AlgEquiv.smul_def] at hu
    simpa [smul_eq_mul, hs σ u hu] using hσ
  · have h := hc σ τ
      ((AddEquiv.torsionByCongr W.pointCoeffEquiv m).symm (kummerCocycle hP₁' σ))
      ((AddEquiv.torsionByCongr W.pointCoeffEquiv m).symm (σ • kummerCocycle hQ₁' τ))
      (by rw [AddEquiv.torsionByCongr_symm_apply_coe, coe_kummerCocycle, map_sub,
        pointCoeffEquiv_symm_smul, AddEquiv.symm_apply_apply, pointGaloisAction_apply])
      (by rw [AddEquiv.torsionByCongr_symm_apply_coe, coe_smul_torsionCoeff, coe_kummerCocycle,
        pointCoeffEquiv_symm_smul, map_sub, pointCoeffEquiv_symm_smul,
        AddEquiv.symm_apply_apply, pointGaloisAction_apply, pointGaloisAction_apply, map_sub])
    rw [← torsionCoeffWeilPairing_apply W m hm hm'] at h
    apply Additive.toMul.injective
    apply Units.ext
    simp only [toMul_add, toMul_sub, toMul_ofMul, Units.val_mul, Units.val_div_eq_div_val,
      cocyclesMap2_apply, ContinuousMonoidHom.coe_id, id_eq,
      TauCeti.kummerShortExact_inclDistribMulActionHom, DistribMulActionHom.coe_fn_coe,
      kummerCoeffInclHom_apply, toMul_kummerCoeffIncl, Additive.toMul_smul,
      AlgEquiv.smul_units_def, Units.coe_map]
    rw [div_mul_eq_mul_div, div_eq_iff (Units.ne_zero _)]
    linear_combination h

end Isotropy

end WeierstrassCurve
