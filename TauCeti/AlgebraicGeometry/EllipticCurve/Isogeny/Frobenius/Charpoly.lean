/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.Frobenius.Dual
public import TauCeti.AlgebraicGeometry.EllipticCurve.PointCount
-- Proof-only: `deg (id - π) = #E(𝔽_q)` and the determinants of the Frobenius pencil on torsion.
import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.Frobenius.Trace
-- Proof-only: base change of morphisms is an injective ring map.
import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.Hom.BaseChange
-- Proof-only: the pencil determinant of a `2 × 2` matrix.
import TauCeti.LinearAlgebra.Matrix.CharpolyFinTwo
-- Proof-only: the Cayley–Hamilton theorem for `2 × 2` matrices.
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff

/-!
# The characteristic polynomial of Frobenius

Let `W` be an elliptic curve over a finite field `F` with `q` elements, `π = π_q` its Frobenius
endomorphism, `π̂` the dual of `π`, and `a_q = q + 1 - #E(𝔽_q)` the trace of Frobenius. This file
proves the Frobenius identities

`π ∘ π = [a_q] ∘ π - [q]` and `π + π̂ = [a_q]`

in the endomorphisms of `W` (Silverman V.2.3.1). The first says that `π` is a root of
`X² - a_q X + q`; the second, with `π ∘ π̂ = [q]`, says that `π` and `π̂` are the two roots.

The proof works on torsion over a separably closed algebraic extension `K` of `F`. For a prime
`ℓ ≠ char F`, the base-changed Frobenius acts on `E[ℓ]` by a `2 × 2` matrix over `ZMod ℓ` of
determinant `q`, through the Weil pairing, and with `det (1 - M) = deg (id - π) = #E(𝔽_q)`; so its
trace is `a_q` modulo `ℓ`, and the Cayley–Hamilton theorem kills `π² - a_q π + q` on `E[ℓ]`. An
endomorphism killing the `ℓ`-torsion for every such `ℓ` is zero, by rigidity. Base change of
morphisms is injective, so the identity descends to `F`, and cancelling `π`, which is nonzero in
the domain of endomorphisms, against `π̂ ∘ π = [q]` gives `π̂ = [a_q] - π`.

## Main results

* `TauCeti.Isogeny.ofIsogeny_frobeniusIsogeny_comp_ofIsogeny_frobeniusIsogeny`: `π ∘ π = a_q π - q`.
* `TauCeti.Isogeny.ofIsogeny_dualFrobeniusIsogeny`: `π̂ = a_q - π`.
* `TauCeti.Isogeny.ofIsogeny_frobeniusIsogeny_add_ofIsogeny_dualFrobeniusIsogeny`: `π + π̂ = a_q`.
* `TauCeti.Isogeny.pointMap_frobeniusIsogeny_add_pointMap_dualFrobeniusIsogeny`: on points,
  `π P + π̂ P = a_q • P`.

## References

* [J. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], III.8.6, V.2.3.1 and
  V.2.3.2.
-/

public section

open WeierstrassCurve WeierstrassCurve.Affine

namespace TauCeti.Isogeny

variable {F : Type*} [Field F] [Finite F] (W : WeierstrassCurve.Affine F) [W.IsElliptic]

namespace Hom

variable {K : Type*} [Field K] [Algebra F K] [IsSepClosed K] [Algebra.IsAlgebraic F K]

/-- Over a separably closed algebraic extension, `π ∘ π` and `a_q π - q` act alike on `E[ℓ]` for
every prime `ℓ` invertible in the field: the matrix of `π` there has determinant `q` and trace
`a_q`, and satisfies its characteristic polynomial. -/
private theorem torsionLinearMap_baseChangeFrobenius_comp [DecidableEq K] {ℓ : ℕ}
    (hℓ : ℓ.Prime) (hℓK : (ℓ : K) ≠ 0) :
    ((ofIsogeny (baseChangeFrobenius K W)).comp
        (ofIsogeny (baseChangeFrobenius K W))).torsionLinearMap ℓ =
      (W.frobeniusTrace • ofIsogeny (baseChangeFrobenius K W) -
        Nat.card F • id (W⁄K).toAffine).torsionLinearMap ℓ := by
  have : Fact ℓ.Prime := ⟨hℓ⟩
  obtain ⟨b⟩ := WeierstrassCurve.nonempty_basis_torsionBy (W⁄K) ℓ hℓK
  set π := ofIsogeny (baseChangeFrobenius K W)
  set M := LinearMap.toMatrix b b (π.torsionLinearMap ℓ)
  have hdet : M.det = (Nat.card F : ZMod ℓ) := by
    rw [LinearMap.det_toMatrix]
    exact det_torsionLinearMap_ofIsogeny_baseChangeFrobenius W hℓK
  -- `id - π` is the separable pencil at `r = s = -1`, so its determinant is its degree `#E(𝔽_q)`
  have hdetOneSub : (1 - M).det = (W.pointCount : ZMod ℓ) := by
    have h := det_torsionLinearMap_zsmul_ofIsogeny_baseChangeFrobenius_sub_zsmul_id W hℓK
      (-1) (-1) (by simp)
    rw [neg_one_zsmul, neg_one_zsmul, neg_sub_neg,
      degree_id_sub_ofIsogeny_baseChangeFrobenius_eq_pointCount] at h
    rw [← h, ← LinearMap.det_toMatrix b, torsionLinearMap_sub, torsionLinearMap_id,
      _root_.map_sub, LinearMap.toMatrix_id]
  -- so the trace of `M` is `q + 1 - #E(𝔽_q) = a_q`
  have htrace : M.trace = (W.frobeniusTrace : ZMod ℓ) := by
    have h := TauCeti.Matrix.det_smul_sub_smul_one_fin_two M (-1) (-1)
    rw [neg_one_smul, neg_one_smul, neg_sub_neg, hdetOneSub, hdet] at h
    rw [frobeniusTrace_def]
    push_cast
    linear_combination h
  -- the Cayley–Hamilton theorem for `M`
  have hcayley : M * M - M.trace • M + M.det • (1 : Matrix (Fin 2) (Fin 2) (ZMod ℓ)) = 0 := by
    simpa [Matrix.charpoly_fin_two, sq, Algebra.smul_def] using Matrix.aeval_self_charpoly M
  apply (LinearMap.toMatrix b b).injective
  rw [htrace, hdet, Int.cast_smul_eq_zsmul, Nat.cast_smul_eq_nsmul] at hcayley
  rw [torsionLinearMap_comp, torsionLinearMap_sub, torsionLinearMap_zsmul, torsionLinearMap_nsmul,
    torsionLinearMap_id, LinearMap.toMatrix_comp b b b, _root_.map_sub, _root_.map_zsmul,
    _root_.map_nsmul, LinearMap.toMatrix_id b, ← sub_eq_zero, ← hcayley]
  abel

/-- Over a separably closed algebraic extension, the base-changed Frobenius satisfies
`π ∘ π = a_q π - q`, by rigidity on prime torsion. -/
private theorem baseChangeFrobenius_comp_baseChangeFrobenius :
    (ofIsogeny (baseChangeFrobenius K W)).comp (ofIsogeny (baseChangeFrobenius K W)) =
      W.frobeniusTrace • ofIsogeny (baseChangeFrobenius K W) - Nat.card F • id (W⁄K).toAffine := by
  classical
  refine ext_pointMap_of_prime_zsmul_eq_zero fun ℓ hℓ hℓK P hP ↦ ?_
  rw [← torsionLinearMap_apply _ ℓ ⟨P, hP⟩, ← torsionLinearMap_apply _ ℓ ⟨P, hP⟩,
    torsionLinearMap_baseChangeFrobenius_comp W hℓ hℓK]

end Hom

/-- **Frobenius is a root of `X² - a_q X + q`**: `π ∘ π = a_q π - q` in the endomorphisms of an
elliptic curve over a finite field with `q` elements, where `a_q` is the trace of Frobenius
(Silverman V.2.3.1). -/
theorem ofIsogeny_frobeniusIsogeny_comp_ofIsogeny_frobeniusIsogeny :
    (Hom.ofIsogeny (frobeniusIsogeny W)).comp (Hom.ofIsogeny (frobeniusIsogeny W)) =
      W.frobeniusTrace • Hom.ofIsogeny (frobeniusIsogeny W) - Nat.card F • Hom.id W := by
  classical
  -- base change to an algebraic closure, where the identity holds by the torsion argument
  have h := Hom.baseChangeFrobenius_comp_baseChangeFrobenius W (K := AlgebraicClosure F)
  rw [baseChangeFrobenius_def] at h
  rw [← Hom.map_inj (algebraMap F (AlgebraicClosure F))]
  simp only [Hom.map_sub, Hom.map_zsmul, Hom.map_nsmul, Hom.comp_map, Hom.id_map,
    Hom.ofIsogeny_map]
  -- `h` is stated on `W⁄K`, the goal on `W.map (algebraMap F K)`; these are the same curve, but
  -- `WeierstrassCurve.baseChange` is semireducible, so only `exact` sees through it
  exact h

/-- **The dual of Frobenius is `a_q - π`** in the endomorphisms of an elliptic curve over a finite
field, where `a_q` is the trace of Frobenius (Silverman V.2.3.1). -/
theorem ofIsogeny_dualFrobeniusIsogeny :
    Hom.ofIsogeny (dualFrobeniusIsogeny W) =
      W.frobeniusTrace • Hom.id W - Hom.ofIsogeny (frobeniusIsogeny W) := by
  -- both sides give `q` when composed with `π` on the right, and `π` is not a zero divisor
  refine mul_right_cancel₀ (Hom.ofIsogeny_ne_zero (frobeniusIsogeny W)) ?_
  rw [Hom.mul_def, Hom.mul_def, ofIsogeny_dualFrobeniusIsogeny_comp_ofIsogeny_frobeniusIsogeny,
    Hom.sub_comp, Hom.zsmul_comp, Hom.id_comp,
    ofIsogeny_frobeniusIsogeny_comp_ofIsogeny_frobeniusIsogeny, sub_sub_cancel]

/-- **`π + π̂ = a_q`**: Frobenius and its dual sum to multiplication by the trace of Frobenius, in
the endomorphisms of an elliptic curve over a finite field (Silverman V.2.3.1). -/
theorem ofIsogeny_frobeniusIsogeny_add_ofIsogeny_dualFrobeniusIsogeny :
    Hom.ofIsogeny (frobeniusIsogeny W) + Hom.ofIsogeny (dualFrobeniusIsogeny W) =
      W.frobeniusTrace • Hom.id W := by
  rw [ofIsogeny_dualFrobeniusIsogeny, add_sub_cancel]

/-- **On points, `π P + π̂ P = a_q • P`**, where `a_q` is the trace of Frobenius. -/
theorem pointMap_frobeniusIsogeny_add_pointMap_dualFrobeniusIsogeny [DecidableEq F]
    (P : W.Point) :
    (Hom.ofIsogeny (frobeniusIsogeny W)).pointMap P +
        (Hom.ofIsogeny (dualFrobeniusIsogeny W)).pointMap P = W.frobeniusTrace • P := by
  rw [← Hom.add_pointMap, ofIsogeny_frobeniusIsogeny_add_ofIsogeny_dualFrobeniusIsogeny,
    Hom.zsmul_pointMap, Hom.id_pointMap]

end TauCeti.Isogeny

end
