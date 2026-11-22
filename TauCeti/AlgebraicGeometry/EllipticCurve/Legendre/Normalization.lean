/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.Legendre.Equation
public import TauCeti.AlgebraicGeometry.EllipticCurve.MordellWeil.TwoTorsion
import Mathlib.FieldTheory.Separable
import TauCeti.AlgebraicGeometry.EllipticCurve.Affine.Point.TwoTorsion
import TauCeti.AlgebraicGeometry.EllipticCurve.Affine.Point.VariableChange
import TauCeti.AlgebraicGeometry.EllipticCurve.FreyCurve.Translation

/-!
# Scaled Legendre normalization over the base field

An elliptic curve with full rational `2`-torsion admits an equation
`y² = x(x - d)(x - dλ)` over its base field. Full rational `2`-torsion forces characteristic
different from `2`. Completing the square gives a split monic cubic. Translating by its first
root gives the scaled Legendre equation `TauCeti.scaledLegendre d λ`. The scale `d` is a difference
of roots; it need not be a square, so this does not assert an isomorphism to the unscaled
Legendre curve.

See Bennett–Siksek, *A conjecture of Erdős, supersingular primes and short character sums*, §6,
and Silverman, *The Arithmetic of Elliptic Curves*, second edition, §§III.1–III.2. We use
`WeierstrassCurve.Affine.card_ker_nsmul_two` to connect the point-group hypothesis to the cubic.
-/

public section

open Polynomial TauCeti

namespace WeierstrassCurve

/-- An elliptic curve whose native point group has four points killed by doubling is isomorphic
over the base field to a scaled Legendre equation `y² = x(x - d)(x - dλ)`, with `d` nonzero
and `λ` different from `0` and `1`. The base field necessarily has characteristic different
from two. -/
theorem exists_scaledLegendre_of_full_two_torsion {K : Type*} [Field K] [DecidableEq K]
    (W : WeierstrassCurve K) [W.IsElliptic]
    (h : Nat.card (nsmulAddMonoidHom (α := W.toAffine.Point) 2).ker = 4) :
    (2 : K) ≠ 0 ∧ ∃ (D : VariableChange K) (d : Kˣ) (l : K), l ≠ 0 ∧ l ≠ 1 ∧
      D • W = scaledLegendre (d : K) l := by
  let S : Set W.toAffine.Point := (nsmulAddMonoidHom (α := W.toAffine.Point) 2).ker
  have hS : S.ncard = 4 := (Nat.card_coe_set_eq S).symm.trans h
  have hfin : S.Finite := Set.finite_of_ncard_ne_zero (by rw [hS]; decide)
  have h₂ : (2 : K) ≠ 0 := by
    refine Affine.Point.two_ne_zero_of_two_lt_card (S := hfin.toFinset) (fun P hP ↦ ?_) ?_
    · rw [neg_eq_iff_add_eq_zero, ← two_nsmul]
      exact AddMonoidHom.mem_ker.mp (hfin.mem_toFinset.mp hP)
    · rw [← Set.ncard_eq_toFinset_card S hfin, hS]
      decide
  let := invertibleOfNonzero h₂
  let N := W.toCharNeTwoNF
  let V := N • W
  let E := Affine.Point.addEquivVariableChange W N
  have e : (nsmulAddMonoidHom (α := V.toAffine.Point) 2).ker ≃
      (nsmulAddMonoidHom (α := W.toAffine.Point) 2).ker :=
    E.toEquiv.subtypeEquiv fun P ↦ by
      simp only [AddMonoidHom.mem_ker, nsmulAddMonoidHom_apply]
      -- The subtype equivalence applies the underlying equivalence of the point-group map.
      change (2 : ℕ) • P = 0 ↔ (2 : ℕ) • E P = 0
      rw [← map_nsmul, map_eq_zero_iff E E.injective]
  have hs := V.toAffine.splits_f_iff_card_ker_nsmul_two_eq_four.mpr ((Nat.card_congr e).trans h)
  have hc : V.toAffine.f.roots.card = 3 := by rw [← hs.natDegree_eq_card_roots, Affine.natDegree_f]
  obtain ⟨e₀, e₁, e₂, he⟩ := Multiset.card_eq_three.mp hc
  have hdist := nodup_roots V.toAffine.separable_f
  rw [he] at hdist
  have ⟨⟨h01, h02⟩, h12⟩ : (e₀ ≠ e₁ ∧ e₀ ≠ e₂) ∧ e₁ ≠ e₂ := by
    simpa [Multiset.nodup_cons] using hdist
  have hf := hs.eq_prod_roots_of_monic V.toAffine.monic_f
  rw [he] at hf
  let d := Units.mk0 (e₁ - e₀) (sub_ne_zero.mpr h01.symm)
  let l := (e₂ - e₀) / (e₁ - e₀)
  have hl₀ : l ≠ 0 := div_ne_zero (sub_ne_zero.mpr h02.symm) d.ne_zero
  have hl₁ : l ≠ 1 := by
    intro hl
    have hh := (div_eq_iff d.ne_zero).mp hl
    exact h12.symm (by simpa [d] using hh)
  have hd : -(d.val * l) = e₀ - e₂ := calc
    -(d.val * l) = -(e₂ - e₀) := by
      dsimp [d, l]
      rw [mul_comm (e₁ - e₀), div_mul_cancel₀ _ (sub_ne_zero.mpr h01.symm)]
    _ = e₀ - e₂ := neg_sub ..
  refine ⟨h₂, ⟨1, e₀, 0, 0⟩ * N, d, l, hl₀, hl₁, ?_⟩
  rw [mul_smul, scaledLegendre_eq_freyCurve, hd]
  exact V.translate_smul_eq_freyCurve_of_f_eq_prod (by simpa [mul_assoc] using hf)

end WeierstrassCurve
