/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.Dual.Separable
public import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.Hom.PointMap
public import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.MulByInt.Commute
import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.MulByInt.Comp
import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.MulByInt.Degree
-- Proof-only: every isogeny is a separable isogeny after a Frobenius power, `p ^ r` divides the
-- inseparable degree of `[p ^ r]`, and base change preserves degrees and `[n]`.
import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.RelativeFrobenius.Factorisation
import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.MulByInt.Separability
import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.BaseChange.Degree
import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.MulByInt.BaseChange

/-!
# The dual isogeny

Let `φ : W₁ → W₂` be an isogeny of elliptic curves over a field `F`. Then `[deg φ]` factors
through `φ` by a unique isogeny. This factor is the **dual isogeny** `φ̂ : W₂ → W₁`
(Silverman III.6.1), and this file names it and proves its basic properties
(Silverman III.6.2(a), (c), (d), (e), (f)):

* `φ̂ ∘ φ = [deg φ]` on `W₁`, and `φ̂` is the only isogeny with this property;
* `φ ∘ φ̂ = [deg φ]` on `W₂`;
* `deg φ̂ = deg φ`;
* `(ψ ∘ φ)^ = φ̂ ∘ ψ̂`;
* `φ̂̂ = φ`;
* `[n]̂ = [n]`;
* `φ̂` commutes with base change along any homomorphism of fields.

No separability, perfectness or closure hypothesis is made. The separable case is
`TauCeti.Isogeny.existsUnique_comp_eq_mulByIntIsogenyOfNeZero_degree_of_isSeparable`, and the
general case reduces to it through Frobenius, as in the proof of Silverman III.6.1. Let `p` be
the exponential characteristic of `F` and `p ^ r` the inseparable degree of `φ`. Then
`φ = φₛ ∘ F^r` with `F^r : W₁ → W₁⁽ᵖʳ⁾` the `r`-fold relative Frobenius and `φₛ` separable
(Silverman II.2.12, `TauCeti.Isogeny.exists_isSeparable_comp_iterateRelativeFrobeniusIsogeny_eq`).
Then `p ^ r` divides the inseparable degree of `[p ^ r] = [p] ^ r`: when `p > 1` this is because
`[p]` is inseparable, and when `p = 1` (characteristic zero) it is trivial, with `r = 0` and
`F^0` the identity. So `[p ^ r]` factors through `F^r` as `V ∘ F^r`. With `φ̂ₛ ∘ φₛ = [deg φₛ]` and
`[deg φₛ] ∘ F^r = F^r ∘ [deg φₛ]`,
`V ∘ φ̂ₛ ∘ φ = V ∘ F^r ∘ [deg φₛ] = [p ^ r · deg φₛ] = [deg φ]`.

The identity `φ ∘ φ̂ = [deg φ]` needs `φ ∘ [n] = [n] ∘ φ`
(`TauCeti.Isogeny.comp_mulByIntIsogenyOfNeZero`). Precomposing with `φ` is injective, so it cancels
from `φ ∘ φ̂ ∘ φ = φ ∘ [deg φ] = [deg φ] ∘ φ`.

## Main definitions

* `TauCeti.Isogeny.dual`: the dual `φ̂` of an isogeny `φ`.

## Main results

* `TauCeti.Isogeny.existsUnique_comp_eq_mulByIntIsogenyOfNeZero_degree`: `[deg φ]` factors
  uniquely through every isogeny `φ`, over any field.
* `TauCeti.Isogeny.dual_comp` and `TauCeti.Isogeny.eq_dual_iff_comp_eq`: `φ̂ ∘ φ = [deg φ]`, and
  this characterises `φ̂`.
* `TauCeti.Isogeny.comp_dual`: `φ ∘ φ̂ = [deg φ]`.
* `TauCeti.Isogeny.degree_dual`: `deg φ̂ = deg φ`.
* `TauCeti.Isogeny.ofIsogeny_dual_comp_ofIsogeny` and
  `TauCeti.Isogeny.ofIsogeny_comp_ofIsogeny_dual`: the two composites are `deg φ • 1` in the
  additive groups of morphisms.
* `TauCeti.Isogeny.pointMap_dual_pointMap` and `TauCeti.Isogeny.pointMap_pointMap_dual`: on points,
  `φ̂ (φ P) = deg φ • P` and `φ (φ̂ Q) = deg φ • Q`.
* `TauCeti.Isogeny.dual_comp_dual`: `(ψ ∘ φ)^ = φ̂ ∘ ψ̂`.
* `TauCeti.Isogeny.dual_dual`: `φ̂̂ = φ`.
* `TauCeti.Isogeny.dual_mulByIntIsogeny`: `[n]` is self-dual.
* `TauCeti.Isogeny.dual_map`: the dual of the base change is the base change of the dual.

## References

* [J. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], II.2.12, III.6.1 and III.6.2.
-/

public section

namespace TauCeti.Isogeny

open WeierstrassCurve.Affine

variable {F : Type*} [Field F] {W₁ W₂ : WeierstrassCurve.Affine F} [W₁.IsElliptic]
  [W₂.IsElliptic] (φ : Isogeny W₁ W₂)

/-- **`[deg φ]` factors uniquely through every isogeny `φ`**, over any field
(Silverman III.6.1). -/
theorem existsUnique_comp_eq_mulByIntIsogenyOfNeZero_degree :
    ∃! χ : Isogeny W₂ W₁,
      χ.comp φ = mulByIntIsogenyOfNeZero W₁ (n := φ.degree) (mod_cast φ.degree_ne_zero) := by
  refine existsUnique_of_exists_of_unique ?_ fun χ χ' h h' ↦
    comp_right_injective φ (h.trans h'.symm)
  obtain ⟨p, _⟩ : ∃ p, ExpChar F p := ⟨_, ringExpChar.expChar F⟩
  -- `φ = φₛ ∘ F^r` with `φₛ` separable
  obtain ⟨r, φₛ, _, hφ⟩ := exists_isSeparable_comp_iterateRelativeFrobeniusIsogeny_eq p φ
  set Fr := iterateRelativeFrobeniusIsogeny p W₁ r
  have hp : (p : ℤ) ^ r ≠ 0 := pow_ne_zero r (mod_cast expChar_ne_zero F p)
  have hs : (φₛ.degree : ℤ) ≠ 0 := mod_cast φₛ.degree_ne_zero
  -- `[p ^ r] = V ∘ F^r`, and `χ ∘ φₛ = [deg φₛ]`
  obtain ⟨V, hV, -⟩ := (existsUnique_comp_iterateRelativeFrobeniusIsogeny_eq_iff p
    (mulByIntIsogenyOfNeZero W₁ hp)).2
    (pow_dvd_inseparableDegree_mulByIntIsogenyOfNeZero_pow W₁ p r)
  obtain ⟨χ, hχ, -⟩ := existsUnique_comp_eq_mulByIntIsogenyOfNeZero_degree_of_isSeparable φₛ
  refine ⟨V.comp χ, ?_⟩
  calc (V.comp χ).comp φ = V.comp ((χ.comp φₛ).comp Fr) := by
        rw [← hφ, comp_assoc, comp_assoc]
    _ = (V.comp Fr).comp (mulByIntIsogenyOfNeZero W₁ hs) := by
        rw [hχ, ← comp_mulByIntIsogenyOfNeZero, comp_assoc]
    _ = mulByIntIsogenyOfNeZero W₁ (n := φ.degree) (mod_cast φ.degree_ne_zero) := by
        rw [hV, mulByIntIsogenyOfNeZero_comp_mulByIntIsogenyOfNeZero, mulByIntIsogeny_inj, ← hφ,
          degree_comp, degree_iterateRelativeFrobeniusIsogeny]
        push_cast
        ring

/-- **The dual isogeny** `φ̂ : W₂ → W₁` of an isogeny `φ : W₁ → W₂`: the unique isogeny with
`φ̂ ∘ φ = [deg φ]` (Silverman III.6.1). -/
noncomputable def dual : Isogeny W₂ W₁ :=
  (existsUnique_comp_eq_mulByIntIsogenyOfNeZero_degree φ).exists.choose

/-- **The dual of `φ` composed with `φ` is multiplication by `deg φ`** on `W₁`
(Silverman III.6.1, III.6.2(a)). -/
@[simp]
theorem dual_comp :
    φ.dual.comp φ = mulByIntIsogenyOfNeZero W₁ (n := φ.degree) (mod_cast φ.degree_ne_zero) :=
  (existsUnique_comp_eq_mulByIntIsogenyOfNeZero_degree φ).exists.choose_spec

/-- **`φ̂` is the only isogeny `χ` with `χ ∘ φ = [deg φ]`.** -/
theorem eq_dual_iff_comp_eq {χ : Isogeny W₂ W₁} :
    χ = φ.dual ↔
      χ.comp φ = mulByIntIsogenyOfNeZero W₁ (n := φ.degree) (mod_cast φ.degree_ne_zero) :=
  ⟨fun h ↦ h ▸ φ.dual_comp, fun h ↦ comp_right_injective φ (h.trans φ.dual_comp.symm)⟩

/-- **The dual has the same degree** (Silverman III.6.2(e)). -/
@[simp]
theorem degree_dual : φ.dual.degree = φ.degree :=
  degree_eq_of_comp_eq_mulByIntIsogenyOfNeZero_degree φ.dual_comp

/-- **`φ` composed with its dual is multiplication by `deg φ`** on `W₂` (Silverman III.6.2(a)). -/
@[simp]
theorem comp_dual :
    φ.comp φ.dual = mulByIntIsogenyOfNeZero W₂ (n := φ.degree) (mod_cast φ.degree_ne_zero) :=
  comp_right_inj.mp <| by rw [comp_assoc, dual_comp, comp_mulByIntIsogenyOfNeZero]

/-- **`φ̂ ∘ φ = deg φ • 1`** in the additive group of morphisms of `W₁`. -/
theorem ofIsogeny_dual_comp_ofIsogeny :
    (Hom.ofIsogeny φ.dual).comp (Hom.ofIsogeny φ) = φ.degree • Hom.id W₁ := by
  rw [Hom.ofIsogeny_comp_ofIsogeny, dual_comp, ofIsogeny_mulByIntIsogeny, natCast_zsmul]

/-- **`φ ∘ φ̂ = deg φ • 1`** in the additive group of morphisms of `W₂`. -/
theorem ofIsogeny_comp_ofIsogeny_dual :
    (Hom.ofIsogeny φ).comp (Hom.ofIsogeny φ.dual) = φ.degree • Hom.id W₂ := by
  rw [Hom.ofIsogeny_comp_ofIsogeny, comp_dual, ofIsogeny_mulByIntIsogeny, natCast_zsmul]

/-- **On points, `φ̂ (φ P) = deg φ • P`.** -/
@[simp]
theorem pointMap_dual_pointMap [DecidableEq F] (P : W₁.Point) :
    (Hom.ofIsogeny φ.dual).pointMap ((Hom.ofIsogeny φ).pointMap P) = φ.degree • P := by
  rw [← Hom.comp_pointMap, ofIsogeny_dual_comp_ofIsogeny, Hom.nsmul_pointMap, Hom.id_pointMap]

/-- **On points, `φ (φ̂ Q) = deg φ • Q`.** -/
@[simp]
theorem pointMap_pointMap_dual [DecidableEq F] (Q : W₂.Point) :
    (Hom.ofIsogeny φ).pointMap ((Hom.ofIsogeny φ.dual).pointMap Q) = φ.degree • Q := by
  rw [← Hom.comp_pointMap, ofIsogeny_comp_ofIsogeny_dual, Hom.nsmul_pointMap, Hom.id_pointMap]

/-- **The dual of the dual is the original isogeny** (Silverman III.6.2(f)). -/
@[simp]
theorem dual_dual : φ.dual.dual = φ :=
  ((eq_dual_iff_comp_eq φ.dual).mpr <| by
    rw [comp_dual, mulByIntIsogeny_inj, degree_dual]).symm

variable {W₃ : WeierstrassCurve.Affine F} [W₃.IsElliptic] (ψ : Isogeny W₂ W₃)

/-- **The dual of a composite is the composite of the duals in the opposite order**:
`(ψ ∘ φ)^ = φ̂ ∘ ψ̂` (Silverman III.6.2(c)). -/
theorem dual_comp_dual : φ.dual.comp ψ.dual = (ψ.comp φ).dual := by
  have hφ : (φ.degree : ℤ) ≠ 0 := mod_cast φ.degree_ne_zero
  have hψ : (ψ.degree : ℤ) ≠ 0 := mod_cast ψ.degree_ne_zero
  -- `φ̂ ∘ ψ̂` composed with `ψ ∘ φ` cancels `ψ̂ ∘ ψ` to `[deg ψ]`, then `φ̂ ∘ φ` to `[deg φ]`
  refine (eq_dual_iff_comp_eq (ψ.comp φ)).mpr ?_
  calc (φ.dual.comp ψ.dual).comp (ψ.comp φ)
      = φ.dual.comp ((ψ.dual.comp ψ).comp φ) := by rw [comp_assoc, comp_assoc]
    _ = (φ.dual.comp φ).comp (mulByIntIsogenyOfNeZero W₁ hψ) := by
        rw [dual_comp ψ, ← comp_mulByIntIsogenyOfNeZero φ, comp_assoc]
    _ = mulByIntIsogenyOfNeZero W₁ (mul_ne_zero hφ hψ) := by
        rw [dual_comp φ, mulByIntIsogenyOfNeZero_comp_mulByIntIsogenyOfNeZero]
    _ = mulByIntIsogenyOfNeZero W₁ (n := (ψ.comp φ).degree)
          (mod_cast (ψ.comp φ).degree_ne_zero) := by
        rw [mulByIntIsogeny_inj, degree_comp, Nat.cast_mul, mul_comm]

variable (W : WeierstrassCurve.Affine F) [W.IsElliptic]

/-- **Multiplication by `n` is self-dual** (Silverman III.6.2(d)). -/
@[simp]
theorem dual_mulByIntIsogeny {n : ℤ} (hn : psiFunctionField W n ≠ 0) :
    (mulByIntIsogeny W hn).dual = mulByIntIsogeny W hn :=
  ((eq_dual_iff_comp_eq _).mpr <| by
    -- `[n]` has degree `n²`, which is nonzero, so `n ≠ 0`
    have hn₀ : n ≠ 0 := by
      have h := (mulByIntIsogeny W hn).degree_ne_zero
      rwa [degree_mulByIntIsogeny, pow_ne_zero_iff two_ne_zero, Int.natAbs_ne_zero] at h
    rw [mulByIntIsogeny_comp_mulByIntIsogeny W hn hn
        (psiFunctionField_ne_zero_of_Δ_ne_zero W W.isUnit_Δ.ne_zero (mul_ne_zero hn₀ hn₀)),
      mulByIntIsogeny_inj, degree_mulByIntIsogeny, Nat.cast_pow, Int.natAbs_sq, sq]).symm

variable {K : Type*} [Field K]

/-- **The dual commutes with base change**: along any homomorphism of fields `f`, the base change
of `φ̂` is the dual of the base change of `φ`. -/
@[simp]
theorem dual_map (f : F →+* K) : φ.dual.map f = (φ.map f).dual :=
  (eq_dual_iff_comp_eq _).mpr <| by
    rw [← comp_map, dual_comp, mulByIntIsogeny_map, mulByIntIsogeny_inj, degree_map]

end TauCeti.Isogeny

end
