/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.DeligneTorus.MumfordTate.Basic
public import TauCeti.Algebra.AlgebraicGroup.GeneralLinear.ScalarTorus

/-!
# Scalars in the Mumford–Tate group

Let `V = ℚⁿ` and let `h : S → GL(V)_ℝ` be a homomorphism from the Deligne torus. If `V` is pure of
weight `m ≠ 0`, its weight cocharacter `w_h = h ∘ w` is `t ↦ t ^ m • 1`, defined over `ℚ`. This
file shows that if `t ↦ t ^ m • 1` factors through `h`, the Mumford–Tate group contains the scalar
subgroup of `GL(V)`, which is its center, a copy of `𝔾ₘ` when `0 < n`. The factorization is a
hypothesis of the theorem here; for a Hodge structure pure of weight `m` it holds with `g` the
weight morphism `w : 𝔾ₘ → S`.

The proof is on coordinate rings. The cocharacter `t ↦ t ^ m • 1` is the weight cocharacter
`TauCeti.GeneralLinear.weightCocharacter (fun _ ↦ m)`, and it lands in `MT(h)`
(`TauCeti.DeligneTorus.mumfordTateHopfIdeal_toIdeal_le_ker`), so the Mumford–Tate ideal lies in
the kernel of its comorphism. For `m ≠ 0` that kernel is the center ideal
(`TauCeti.GeneralLinear.ker_weightCocharacter_const`).
Scheme-theoretically, the image of `t ↦ t ^ m • 1` is the whole scalar subgroup, not a finite
subgroup `μ_k`.

The hypothesis `m ≠ 0` is needed: for the trivial Hodge structure on `ℚ`, of weight zero, the
Mumford–Tate group is trivial (`TauCeti.DeligneTorus.mumfordTateHopfIdeal_eq_augmentation_iff`),
while the scalar subgroup of `GL₁` is all of `GL₁`.

## Main declarations

* `TauCeti.DeligneTorus.mumfordTateHopfIdeal_le_centerDefiningIdeal`: if `t ↦ t ^ m • 1`,
  `m ≠ 0`, factors through `h` after extending scalars to `ℝ`, then `MT(h)` contains the scalars,
  the center of `GLₙ`.

## References

* J. S. Milne, *Introduction to Shimura varieties*, §2, p. 31 (the aside after Definition 2.16).
* P. Deligne, *Hodge cycles on abelian varieties* (notes by J. S. Milne), §3, pp. 24–25.
-/

public section

open CategoryTheory _root_.CommHopfAlgCat TauCeti.CommHopfAlgCat
open scoped LaurentPolynomial

namespace TauCeti.DeligneTorus

/-- **The Mumford–Tate group contains the scalars when the weight is nonzero.** Let
`h : S → GL_{n,ℝ}` and `m ≠ 0`, and suppose that the cocharacter `t ↦ t ^ m • 1` of `GLₙ` over `ℚ`
(the weight cocharacter `TauCeti.GeneralLinear.weightCocharacter (fun _ ↦ m)`) factors through `h`
after extending scalars to `ℝ`, as `𝔾_{m,ℝ} → S → GL_{n,ℝ}`. For a rational Hodge structure pure
of weight `m`, this is the weight cocharacter `w_h = h ∘ w`; the factorization is a hypothesis
here. Then the Mumford–Tate group contains the scalar subgroup of `GLₙ`, its center, a copy of
`𝔾ₘ` when `0 < n`. -/
theorem mumfordTateHopfIdeal_le_centerDefiningIdeal {n : ℕ}
    {h : baseChange (K := ℝ) (GeneralLinear.coordinateHopfAlgebra ℚ n) ⟶
      _root_.CommHopfAlgCat.of ℝ S} {m : ℤ} (hm : m ≠ 0)
    (g : _root_.CommHopfAlgCat.of ℝ S ⟶
      baseChange (K := ℝ) (_root_.CommHopfAlgCat.of ℚ ℚ[T;T⁻¹]))
    (hg : h ≫ g = baseChangeMap (K := ℝ) (_root_.CommHopfAlgCat.ofHom
      (GeneralLinear.weightCocharacter (R := ℚ) (N := n) (fun _ ↦ m)))) :
    mumfordTateHopfIdeal h ≤ centerDefiningIdeal (GeneralLinear.coordinateHopfAlgebra ℚ n) := by
  intro x hx
  have hker := BialgHom.mem_ker_toAlgHom_toRingHom.mp
    (mumfordTateHopfIdeal_toIdeal_le_ker _ g hg (HopfIdeal.mem_toIdeal.mpr hx))
  rw [_root_.CommHopfAlgCat.hom_ofHom] at hker
  rw [← GeneralLinear.ker_weightCocharacter_const n ℚ hm]
  exact (HopfIdeal.mem_ker _).mpr hker

end TauCeti.DeligneTorus
