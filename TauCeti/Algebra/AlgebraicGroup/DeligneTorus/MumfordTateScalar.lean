/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.DeligneTorus.MumfordTate
public import TauCeti.Algebra.AlgebraicGroup.GeneralLinear.ScalarTorus

/-!
# Scalars in the Mumford–Tate group

Let `V = ℚⁿ` and let `h : S → GL(V)_ℝ` be a homomorphism from the Deligne torus. If `V` is pure of
weight `m ≠ 0`, its weight cocharacter `w_h = h ∘ w` is `t ↦ t ^ m • 1`, defined over `ℚ`. This
file shows that if `t ↦ t ^ m • 1` factors through `h`, the Mumford–Tate group contains the scalar
subgroup of `GL(V)`, a copy of `𝔾ₘ` when `0 < n`. The factorization is a hypothesis of the
theorems here: deriving it from purity needs the weight morphism `w : 𝔾ₘ → S`, which is not yet in
Tau Ceti.

The proof is on coordinate rings. The cocharacter `t ↦ t ^ m • 1` lands in `MT(h)`
(`TauCeti.DeligneTorus.mumfordTateHopfIdeal_toIdeal_le_ker`), so the Mumford–Tate ideal lies in
the kernel of its comorphism `k[GLₙ] → k[T, T⁻¹] → k[T, T⁻¹]`, the scalar comorphism followed by
`T ↦ T ^ m`. For `m ≠ 0` the second map is injective, so that kernel is the scalar ideal
`TauCeti.GeneralLinear.scalarHopfIdeal`. Scheme-theoretically, the image of `t ↦ t ^ m • 1` is the
whole scalar subgroup, not a finite subgroup `μ_k`.

The hypothesis `m ≠ 0` is needed: for the trivial Hodge structure on `ℚ`, of weight zero, the
Mumford–Tate group is trivial (`TauCeti.DeligneTorus.mumfordTateHopfIdeal_eq_augmentation_iff`),
while the scalar subgroup of `GL₁` is all of `GL₁`.

## Main declarations

* `TauCeti.DeligneTorus.mumfordTateHopfIdeal_le_scalarHopfIdeal`: if `t ↦ t ^ m • 1`, `m ≠ 0`,
  factors through `h` after extending scalars to `ℝ`, then `MT(h)` contains the scalars.
* `TauCeti.DeligneTorus.mumfordTateHopfIdeal_le_centerDefiningIdeal`: the same conclusion,
  phrased with the center of `GLₙ`.

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
factors through `h` after extending scalars to `ℝ`, as `𝔾_{m,ℝ} → S → GL_{n,ℝ}`. For a rational
Hodge structure pure of weight `m`, this is the weight cocharacter `w_h = h ∘ w`; the
factorization is a hypothesis here. Then the Mumford–Tate group contains the scalar subgroup of
`GLₙ`, a copy of `𝔾ₘ` when `0 < n`. -/
theorem mumfordTateHopfIdeal_le_scalarHopfIdeal {n : ℕ}
    {h : baseChange (K := ℝ) (GeneralLinear.coordinateHopfAlgebra ℚ n) ⟶
      _root_.CommHopfAlgCat.of ℝ S} {m : ℤ} (hm : m ≠ 0)
    (g : _root_.CommHopfAlgCat.of ℝ S ⟶
      baseChange (K := ℝ) (_root_.CommHopfAlgCat.of ℚ ℚ[T;T⁻¹]))
    (hg : h ≫ g = baseChangeMap (K := ℝ) (GeneralLinear.scalarTorusCoordinateMap n ≫
      _root_.CommHopfAlgCat.ofHom
        (AddMonoidAlgebra.mapDomainBialgHom ℚ (AddMonoidHom.mulRight m)))) :
    mumfordTateHopfIdeal h ≤ GeneralLinear.scalarHopfIdeal n ℚ := by
  intro x hx
  have hker := BialgHom.mem_ker_toAlgHom_toRingHom.mp
    (mumfordTateHopfIdeal_toIdeal_le_ker _ g hg (HopfIdeal.mem_toIdeal.mpr hx))
  rw [_root_.CommHopfAlgCat.hom_comp, BialgHom.comp_apply, _root_.CommHopfAlgCat.hom_ofHom]
    at hker
  rw [GeneralLinear.mem_scalarHopfIdeal]
  exact AddMonoidAlgebra.mapDomain_injective (R := ℚ) (mul_left_injective₀ hm)
    (hker.trans (AddMonoidAlgebra.mapDomain_zero _).symm)

/-- **The Mumford–Tate group contains the center of `GLₙ` when the weight is nonzero**: the form
of `TauCeti.DeligneTorus.mumfordTateHopfIdeal_le_scalarHopfIdeal` with the center of `GLₙ`,
which is its scalar subgroup. -/
theorem mumfordTateHopfIdeal_le_centerDefiningIdeal {n : ℕ}
    {h : baseChange (K := ℝ) (GeneralLinear.coordinateHopfAlgebra ℚ n) ⟶
      _root_.CommHopfAlgCat.of ℝ S} {m : ℤ} (hm : m ≠ 0)
    (g : _root_.CommHopfAlgCat.of ℝ S ⟶
      baseChange (K := ℝ) (_root_.CommHopfAlgCat.of ℚ ℚ[T;T⁻¹]))
    (hg : h ≫ g = baseChangeMap (K := ℝ) (GeneralLinear.scalarTorusCoordinateMap n ≫
      _root_.CommHopfAlgCat.ofHom
        (AddMonoidAlgebra.mapDomainBialgHom ℚ (AddMonoidHom.mulRight m)))) :
    mumfordTateHopfIdeal h ≤ centerDefiningIdeal (GeneralLinear.coordinateHopfAlgebra ℚ n) :=
  GeneralLinear.scalarHopfIdeal_eq_centerDefiningIdeal n ℚ ▸
    mumfordTateHopfIdeal_le_scalarHopfIdeal hm g hg

end TauCeti.DeligneTorus
