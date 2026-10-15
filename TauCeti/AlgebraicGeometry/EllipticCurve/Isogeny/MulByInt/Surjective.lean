/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.Hom.PointMap
public import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.MulByInt.Hom
public import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.PointHom.Fiber
-- Proof-only: `[n]` is separable when `n` is invertible in the base field.
import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.MulByInt.Separability

/-!
# Multiplication by `n` is surjective over a separably closed field

Let `W` be an elliptic curve over a separably closed field `F`, and `n` an integer invertible in
`F`. Then every point of `W` is divisible by `n`: the map `P ↦ n • P` on `W(F)` is surjective
(Silverman III.4.2(a) with III.5.4). This is the right-exactness of the sequence
`0 → E[n] → E(Kˢ) → E(Kˢ) → 0` on which the Galois-cohomological `n`-descent rests.

The proof goes through the isogeny `[n]`. It is separable because `n` is invertible
(`TauCeti.Isogeny.isSeparable_mulByIntIsogeny_iff`), a separable isogeny is surjective on points
over a separably closed field (`TauCeti.Isogeny.toPointHom_surjective`), and its action on points
is multiplication by `n` (`TauCeti.Isogeny.ofIsogeny_mulByIntIsogeny`).

The invertibility hypothesis cannot be dropped. Over a separably closed field of characteristic
`p` that is not perfect, the fibres of the inseparable isogeny `[p]` live in a purely inseparable
extension, so `[p]` need not be surjective on points.

## Main results

* `WeierstrassCurve.Affine.zsmul_surjective`: `P ↦ n • P` is surjective for `n : ℤ` invertible in
  the base field.
* `WeierstrassCurve.Affine.nsmul_surjective`: the same for `n : ℕ`.

## References

* [J. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], III.4.2(a) and III.5.4.
-/

public section

namespace WeierstrassCurve.Affine

open TauCeti TauCeti.Isogeny

variable {F : Type*} [Field F] [DecidableEq F] [IsSepClosed F] (W : WeierstrassCurve.Affine F)
  [W.IsElliptic]

/-- **Multiplication by `n` is surjective on the points of an elliptic curve over a separably
closed field**, for `n` invertible in the field (Silverman III.4.2(a), III.5.4). -/
theorem zsmul_surjective {n : ℤ} (hn : (n : F) ≠ 0) :
    Function.Surjective fun P : W.Point ↦ n • P := by
  have hψ : psiFunctionField W n ≠ 0 :=
    psiFunctionField_ne_zero_of_Δ_ne_zero W W.isUnit_Δ.ne_zero fun h ↦ hn (by simp [h])
  have := (isSeparable_mulByIntIsogeny_iff W hψ).2 hn
  intro Q
  obtain ⟨P, rfl⟩ := (mulByIntIsogeny W hψ).toPointHom_surjective Q
  refine ⟨P, ?_⟩
  rw [← Hom.pointMap_ofIsogeny_eq_toPointHom, ofIsogeny_mulByIntIsogeny, Hom.zsmul_pointMap,
    Hom.id_pointMap]

/-- **Multiplication by a natural number `n` is surjective on the points of an elliptic curve over
a separably closed field**, for `n` invertible in the field. -/
theorem nsmul_surjective {n : ℕ} (hn : (n : F) ≠ 0) :
    Function.Surjective fun P : W.Point ↦ n • P := by
  simpa only [natCast_zsmul] using W.zsmul_surjective (n := n) (by exact_mod_cast hn)

end WeierstrassCurve.Affine

end
