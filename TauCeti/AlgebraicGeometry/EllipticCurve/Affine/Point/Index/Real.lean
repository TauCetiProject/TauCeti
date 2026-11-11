/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.Hom.Cokernel
import TauCeti.Algebra.Module.Torsion.Int
-- Proof-only: `|c| Ω(W₁) · [W₂(ℝ) : φ(W₁(ℝ))] = #ker φ(ℝ) · Ω(W₂)`.
import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.RealPeriod
-- Proof-only: `[n]` is `n • id`, it pulls `ω` back to `n ω`, and `deg (n • f) = n² deg f`
-- (`MulByInt.Separability` re-exports `MulByInt.Hom`).
import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.MulByInt.Separability
-- Proof-only: `E[n]` is finite for `n ≠ 0`.
import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.MulByInt.KernelCard

/-!
# The cokernel of an isogeny on real points

Let `E` be an elliptic curve over `ℝ`. For a natural number `n ≠ 0`,

`n · #(E(ℝ) ⧸ n E(ℝ)) = #E(ℝ)[n]`.

So the local factor `#(E(ℝ) ⧸ n E(ℝ)) / #E(ℝ)[n]` of multiplication by `n` at a real place is
`1 / n`, the inverse of the absolute value `|n| = n`. This is the archimedean counterpart of
`WeierstrassCurve.index_range_nsmul_eq_natCard_torsionBy_mul`, where the local factor at a finite
place `u` is `#(O_u ⧸ n O_u)`, the inverse of the normalised absolute value of `n` at `u`. It
reflects `E(ℝ) ≅ ℝ/ℤ × (ℤ/2ℤ)^ε`, but the proof does not use that structure. It reads the equality
off the real period: `[n]` pulls the invariant differential back to `n ω`, so the transformation
formula `|c| Ω(W₁) · [W₂(ℝ) : φ(W₁(ℝ))] = #ker φ(ℝ) · Ω(W₂)`
(`TauCeti.Isogeny.abs_mul_realPeriod_mul_index_eq_card_ker_mul`) gives
`n Ω(E) · [E(ℝ) : n E(ℝ)] = #E(ℝ)[n] · Ω(E)`, and `Ω(E) > 0`.

Consequently, for a nonzero morphism `f : E₁ → E₂` over `ℝ` of degree `n`, the local factors
`#(E₂(ℝ) ⧸ f E₁(ℝ)) / #E₁(ℝ)[f]` of `f` and of its dual `f̂` multiply to `1 / n`:

`n · #(E₂(ℝ) ⧸ f E₁(ℝ)) · #(E₁(ℝ) ⧸ f̂ E₂(ℝ)) = #E₁(ℝ)[f] · #E₂(ℝ)[f̂]`,

since `f̂ ∘ f = [n]` (`TauCeti.Isogeny.Hom.index_range_nsmul_mul_card_ker_mul_card_ker_dual`).
This is the archimedean counterpart of
`TauCeti.Isogeny.Hom.index_range_mul_index_range_dual_eq_card_ker_mul_card_ker_dual_mul`. Together
with it and the product formula for `n`, the local factors of `f` and `f̂` multiply to `1` over all
places of `ℚ`, which is how they enter Cassels' proof that the Birch–Swinnerton-Dyer quotient is
an isogeny invariant.

## Main results

* `WeierstrassCurve.mul_index_range_nsmul_eq_natCard_torsionBy`:
  `n · #(E(ℝ) ⧸ n E(ℝ)) = #E(ℝ)[n]` for `n ≠ 0`.
* `TauCeti.Isogeny.Hom.degree_mul_index_range_mul_index_range_dual_eq_card_ker_mul_card_ker_dual`:
  the local cokernel/kernel ratios over `ℝ` of a nonzero morphism and of its dual multiply to the
  inverse of its degree.

## References

* [J. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], III.5 and III.6.
* J. W. S. Cassels, *Arithmetic on curves of genus 1. VIII. On conjectures of Birch and
  Swinnerton-Dyer*, J. Reine Angew. Math. 217 (1965), 180–199.
-/

public section

open WeierstrassCurve.Affine

namespace WeierstrassCurve

variable (W : WeierstrassCurve ℝ) [W.IsElliptic] {n : ℕ}

/-- **The index of `n E(ℝ)`**: for an elliptic curve over `ℝ` and a natural number `n ≠ 0`,

`n · #(E(ℝ) ⧸ n E(ℝ)) = #E(ℝ)[n]`.

So the local factor `#(E(ℝ) ⧸ n E(ℝ)) / #E(ℝ)[n]` of multiplication by `n` is the inverse of the
absolute value of `n`. -/
theorem mul_index_range_nsmul_eq_natCard_torsionBy (hn : n ≠ 0) :
    n * (nsmulAddMonoidHom (α := W.toAffine.Point) n).range.index =
      Nat.card (Submodule.torsionBy ℤ W.toAffine.Point n) := by
  have hnR : ((n : ℤ) : ℝ) ≠ 0 := by exact_mod_cast hn
  let φ := TauCeti.Isogeny.mulByIntIsogeny W.toAffine
    (TauCeti.Isogeny.psiFunctionField_ne_zero W.toAffine hnR)
  have hφ : (TauCeti.Isogeny.Hom.ofIsogeny φ).pointMapHom = nsmulAddMonoidHom n := by
    ext P
    rw [TauCeti.Isogeny.Hom.pointMapHom_apply, TauCeti.Isogeny.ofIsogeny_mulByIntIsogeny,
      TauCeti.Isogeny.Hom.zsmul_pointMap, TauCeti.Isogeny.Hom.id_pointMap, natCast_zsmul,
      nsmulAddMonoidHom_apply]
  have hc : φ.pullbackDifferential (invariantDifferential W.toAffine) =
      (n : ℝ) • invariantDifferential W.toAffine := by
    rw [TauCeti.Isogeny.pullbackDifferential_mulByIntIsogeny_invariantDifferential,
      natCast_zsmul, Nat.cast_smul_eq_nsmul]
  -- `n Ω · [E(ℝ) : n E(ℝ)] = #E(ℝ)[n] · Ω`, and `Ω ≠ 0`
  have h := TauCeti.Isogeny.abs_mul_realPeriod_mul_index_eq_card_ker_mul φ hc
  rw [hφ, TauCeti.natCard_ker_nsmulAddMonoidHom_eq_natCard_torsionBy, Nat.abs_cast] at h
  have h' : (n * (nsmulAddMonoidHom (α := W.toAffine.Point) n).range.index : ℝ) * W.realPeriod =
      Nat.card (Submodule.torsionBy ℤ W.toAffine.Point n) * W.realPeriod := by
    linear_combination h
  exact_mod_cast mul_right_cancel₀ W.realPeriod_pos.ne' h'

end WeierstrassCurve

namespace TauCeti.Isogeny.Hom

variable {W₁ W₂ : WeierstrassCurve ℝ} [W₁.IsElliptic] [W₂.IsElliptic]
  (f : Hom W₁.toAffine W₂.toAffine)

/-- **The local cokernel/kernel ratios over `ℝ` of a morphism and of its dual multiply to the
inverse of its degree**: for a nonzero morphism `f` of degree `n` of elliptic curves over `ℝ`,

`n · #(E₂(ℝ) ⧸ f E₁(ℝ)) · #(E₁(ℝ) ⧸ f̂ E₂(ℝ)) = #E₁(ℝ)[f] · #E₂(ℝ)[f̂]`,

all four orders being finite. -/
theorem degree_mul_index_range_mul_index_range_dual_eq_card_ker_mul_card_ker_dual (hf : f ≠ 0) :
    f.degree * (f.pointMapHom.range.index * f.dual.pointMapHom.range.index) =
      Nat.card f.pointMapHom.ker * Nat.card f.dual.pointMapHom.ker := by
  have hn : f.degree ≠ 0 := f.degree_eq_zero_iff.not.mpr hf
  have hidx := W₁.mul_index_range_nsmul_eq_natCard_torsionBy hn
  have : Finite (Submodule.torsionBy ℤ W₁.toAffine.Point f.degree) :=
    W₁.finite_torsionBy (Int.natCast_ne_zero.mpr hn)
  have hT : Nat.card (Submodule.torsionBy ℤ W₁.toAffine.Point f.degree) ≠ 0 :=
    Nat.card_pos.ne'
  -- `z(f̂) · z(f) = z([n])`, and `z([n]) = 1 / n`
  have h := f.index_range_nsmul_mul_card_ker_mul_card_ker_dual
  rw [TauCeti.natCard_ker_nsmulAddMonoidHom_eq_natCard_torsionBy] at h
  refine Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hT) ?_
  linear_combination f.degree * h.symm +
    (Nat.card f.pointMapHom.ker * Nat.card f.dual.pointMapHom.ker) * hidx

end TauCeti.Isogeny.Hom
