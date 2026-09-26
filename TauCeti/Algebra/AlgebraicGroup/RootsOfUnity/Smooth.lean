/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.AlgebraicGroup.RootsOfUnity.Scheme
public import TauCeti.Algebra.MonoidAlgebra.Smooth
public import TauCeti.AlgebraicGeometry.AffineGroupScheme.Smooth

/-!
# Smoothness of roots-of-unity group schemes

For positive `n`, the coordinate algebra of `μ_n` is the group algebra of the cyclic group
`ℤ/n`. It is smooth over a field exactly when `n` is nonzero in that field. In particular,
`μ_p` is non-smooth in characteristic `p`, even though its points over an algebraically closed
field form the trivial group. This example keeps smoothness separate from the finite-type
affine-group-scheme definition.

## References

* J. S. Milne, *Algebraic Groups* (2017), §12.
-/

public section

open AlgebraicGeometry CategoryTheory

namespace TauCeti.RootsOfUnityGroup

universe u

variable {k : Type u} [Field k]

/-- For positive `n`, the coordinate algebra of `μ_n` is smooth exactly when `n` is a unit in
the ground field. -/
-- Not `@[simp]`: `simp` already proves this from `MonoidAlgebra.smooth_iff_isUnit_card`.
theorem coordinateRing_smooth_iff (n : ℕ) [NeZero n] :
    Algebra.Smooth k (MonoidAlgebra k (Multiplicative (ZMod n))) ↔ IsUnit (n : k) := by
  have hcard : Nat.card (Multiplicative (ZMod n)) = n :=
    (Nat.card_congr (Multiplicative.ofAdd : ZMod n ≃ Multiplicative (ZMod n))).trans
      (Nat.card_zmod n)
  simpa only [hcard] using
    (MonoidAlgebra.smooth_iff_isUnit_card k (Multiplicative (ZMod n)))

/-- In characteristic `p`, the coordinate algebra of `μ_p` is not smooth. -/
theorem coordinateRing_not_smooth (p : ℕ) [Fact p.Prime] [CharP k p] :
    ¬ Algebra.Smooth k (MonoidAlgebra k (Multiplicative (ZMod p))) := by
  let : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  intro hs
  have hu := (coordinateRing_smooth_iff (k := k) p).mp hs
  exact (isUnit_iff_ne_zero.mp hu) (CharP.cast_eq_zero k p)

/-- The structural morphism of the group scheme `μ_n` is smooth exactly when `n` is a unit in
the ground field. -/
-- Not `@[simp]`: `simp` unfolds the left-hand side via `DiagonalizableGroup.groupScheme_X_hom`.
theorem groupScheme_smooth_iff (n : ℕ) [NeZero n] :
    Smooth (groupScheme k n).X.hom ↔ IsUnit (n : k) := by
  rw [groupScheme, DiagonalizableGroup.groupScheme_def]
  have hsmooth : Smooth (((hopfSpec (CommRingCat.of k)).obj
      (Opposite.op (DiagonalizableGroup.coordinateRing k (characterGroup n)).obj)).X.hom) ↔
      Algebra.Smooth k (MonoidAlgebra k (ULift.{u} (Multiplicative (ZMod n)))) := by
    have h := (algebraSmooth_iff_smooth_hopfSpec k
      (DiagonalizableGroup.coordinateRing k (characterGroup n)).obj).symm
    rw [smoothAffineGroupSchemeProperty_iff, smoothCommHopfAlgProperty_iff] at h
    -- `DiagonalizableGroup.coordinateRing`, `FiniteTypeCommHopfAlgCat.of` and `characterGroup`
    -- are abbreviations, so the carrier of this coordinate ring is by definition the group
    -- algebra `MonoidAlgebra k (ULift (Multiplicative (ZMod n)))`, and `h` applies as stated.
    exact h
  rw [hsmooth]
  have hcard : Nat.card (ULift.{u} (Multiplicative (ZMod n))) = n :=
    (Nat.card_congr (Equiv.ulift : ULift.{u} (Multiplicative (ZMod n)) ≃
      Multiplicative (ZMod n))).trans <|
      (Nat.card_congr (Multiplicative.ofAdd : ZMod n ≃ Multiplicative (ZMod n))).trans
        (Nat.card_zmod n)
  simpa only [hcard] using
    (MonoidAlgebra.smooth_iff_isUnit_card k (ULift.{u} (Multiplicative (ZMod n))))

/-- The roots-of-unity group scheme `μ_p` is not smooth in characteristic `p`. -/
theorem groupScheme_not_smooth (p : ℕ) [Fact p.Prime] [CharP k p] :
    ¬ Smooth (groupScheme k p).X.hom := by
  let : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  intro hs
  exact (isUnit_iff_ne_zero.mp ((groupScheme_smooth_iff (k := k) p).mp hs))
    (CharP.cast_eq_zero k p)

end TauCeti.RootsOfUnityGroup
