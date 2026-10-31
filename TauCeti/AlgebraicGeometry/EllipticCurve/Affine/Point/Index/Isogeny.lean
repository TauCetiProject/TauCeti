/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.Affine.Point.Index.NSmul
public import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.Hom.Cokernel

import TauCeti.GroupTheory.Index.PrimaryComponent

/-!
# The local cokernel of an isogeny at a place prime to its degree

Let `A` be a Dedekind domain with fraction field `F`, let `u` be a height-one prime of `A` with
finite residue field, and let `f : E₁ → E₂` be a morphism of elliptic curves over the completion
`F_u` whose degree is prime to `u`. The local factor of `f` in Cassels' proof that the
Birch–Swinnerton-Dyer quotient is an isogeny invariant is the ratio

`z(f) = #(E₂(F_u) ⧸ f E₁(F_u)) / #E₁(F_u)[f]`.

This file shows that it is defined, and that the local factor of the dual isogeny `f̂` is its
inverse:

`#(E₂(F_u) ⧸ f E₁(F_u)) · #(E₁(F_u) ⧸ f̂ E₂(F_u)) = #E₁(F_u)[f] · #E₂(F_u)[f̂]`.

Since `f̂ ∘ f` is multiplication by `deg f`, the ratios satisfy `z(f̂) · z(f) = z([deg f])`
(`TauCeti.Isogeny.Hom.index_range_nsmul_mul_card_ker_mul_card_ker_dual`), and `z([deg f]) = 1` at a
place prime to `deg f` (`WeierstrassCurve.index_range_nsmul_eq_natCard_torsionBy`). Finiteness of
the cokernel comes from the same composite: the image of `f` contains `deg f · E₂(F_u)`, which has
finite index.

The ratio itself is carried by finite torsion. Write `n = deg f` and `E(F_u)[n^∞]` for the
`n`-primary component of `E(F_u)`, the points killed by a power of `n`, which is finite. Then

`z(f) = #E₂(F_u)[n^∞] / #E₁(F_u)[n^∞]`.

Indeed `E₂(F_u)` has a subgroup of finite index on which `n` is bijective (the kernel of reduction
of a minimal model), so every point of `E₂(F_u)` is divisible by `n`, hence lies in the image of
`f`, up to an element of `E₂(F_u)[n^∞]`; and the inverse image of `E₂(F_u)[n^∞]` under `f` is
`E₁(F_u)[n^∞]`, since `f̂ ∘ f = [n]`.

## Main results

* `TauCeti.Isogeny.Hom.finiteIndex_range_pointMapHom_of_degree_notMem`: the image of
  `E₁(F_u)` has finite index in `E₂(F_u)`.
* `TauCeti.Isogeny.Hom.index_range_mul_index_range_dual_eq_card_ker_mul_card_ker_dual`: the local
  cokernel/kernel ratios of `f` and of `f̂` are inverse.
* `TauCeti.Isogeny.Hom.index_range_mul_card_primaryComponent_of_degree_notMem` and
  `TauCeti.Isogeny.Hom.index_range_div_card_ker_of_degree_notMem`: the local cokernel/kernel ratio
  of `f` is the ratio of the orders of the `deg f`-primary components.

## References

* [J. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], III.6, VII.6 and X.4.
* J. W. S. Cassels, *Arithmetic on curves of genus 1. VIII. On conjectures of Birch and
  Swinnerton-Dyer*, J. Reine Angew. Math. 217 (1965), 180–199.
-/

public section

open IsDedekindDomain

namespace TauCeti.Isogeny.Hom

variable {A : Type*} [CommRing A] [IsDedekindDomain A]
  {F : Type*} [Field F] [Algebra A F] [IsFractionRing A F]
  (u : HeightOneSpectrum A) [Finite (A ⧸ u.asIdeal)] [DecidableEq (u.adicCompletion F)]
  {W₁ W₂ : WeierstrassCurve (u.adicCompletion F)} [W₁.IsElliptic] [W₂.IsElliptic]
  {f : Hom W₁.toAffine W₂.toAffine}

/-- **The local cokernel of a morphism of degree prime to `u` is finite**: the image of
`E₁(F_u)` has finite index in `E₂(F_u)`, since it contains `deg f · E₂(F_u)`. -/
theorem finiteIndex_range_pointMapHom_of_degree_notMem (hf : (f.degree : A) ∉ u.asIdeal) :
    f.pointMapHom.range.FiniteIndex := by
  have := WeierstrassCurve.finiteIndex_range_nsmul u W₂ hf
  refine AddSubgroup.finiteIndex_of_le (H := (nsmulAddMonoidHom f.degree).range) ?_
  rintro P ⟨Q, rfl⟩
  exact ⟨f.dual.pointMap Q, by simp [pointMap_dual_pointMap]⟩

/-- **The local cokernel/kernel ratios of a morphism and of its dual are inverse** at a place
prime to the degree:
`#(E₂(F_u) ⧸ f E₁(F_u)) · #(E₁(F_u) ⧸ f̂ E₂(F_u)) = #E₁(F_u)[f] · #E₂(F_u)[f̂]`, all four orders
being finite. -/
theorem index_range_mul_index_range_dual_eq_card_ker_mul_card_ker_dual
    (hf : (f.degree : A) ∉ u.asIdeal) :
    f.pointMapHom.range.index * f.dual.pointMapHom.range.index =
      Nat.card f.pointMapHom.ker * Nat.card f.dual.pointMapHom.ker := by
  have hidx := WeierstrassCurve.index_range_nsmul_eq_natCard_torsionBy u W₁ hf
  have hker : Nat.card (nsmulAddMonoidHom (α := W₁.toAffine.Point) f.degree).ker =
      Nat.card (Submodule.torsionBy ℤ W₁.toAffine.Point f.degree) :=
    Nat.card_congr (Equiv.subtypeEquivRight fun P ↦ by
      rw [AddMonoidHom.mem_ker, nsmulAddMonoidHom_apply, Submodule.mem_torsionBy_iff,
        natCast_zsmul])
  have hne : (nsmulAddMonoidHom (α := W₁.toAffine.Point) f.degree).range.index ≠ 0 :=
    (WeierstrassCurve.finiteIndex_range_nsmul u W₁ hf).index_ne_zero
  -- `z(f̂) · z(f) = z([deg f])`, and the ratio for `[deg f]` is `1`
  have h := f.index_range_nsmul_mul_card_ker_mul_card_ker_dual
  rw [hker, ← hidx] at h
  refine (Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hne) ?_).symm
  rw [h]
  ring

/-- **The local cokernel of a morphism of degree prime to `u`, through `deg f`-primary torsion**:
with `n = deg f`,

`#(E₂(F_u) ⧸ f E₁(F_u)) · #E₁(F_u)[n^∞] = #E₂(F_u)[n^∞] · #E₁(F_u)[f]`,

where `E(F_u)[n^∞]` is the `n`-primary component, the finite group of points killed by a power of
`n`. -/
theorem index_range_mul_card_primaryComponent_of_degree_notMem
    (hf : (f.degree : A) ∉ u.asIdeal) :
    f.pointMapHom.range.index *
        Nat.card (AddCommGroup.primaryComponent W₁.toAffine.Point f.degree) =
      Nat.card (AddCommGroup.primaryComponent W₂.toAffine.Point f.degree) *
        Nat.card f.pointMapHom.ker := by
  obtain ⟨U, _, hbij⟩ := W₂.exists_finiteIndex_bijective_nsmul u hf
  exact f.pointMapHom.index_range_mul_card_primaryComponent f.dual.pointMapHom
    (fun P ↦ by simp [dual_pointMap_pointMap]) (fun Q ↦ by simp [pointMap_dual_pointMap]) U hbij.2

/-- **The local cokernel/kernel ratio of a morphism of degree prime to `u`**: with `n = deg f`,

`#(E₂(F_u) ⧸ f E₁(F_u)) / #E₁(F_u)[f] = #E₂(F_u)[n^∞] / #E₁(F_u)[n^∞]`,

the ratio of the orders of the `n`-primary components, all four orders being finite. -/
theorem index_range_div_card_ker_of_degree_notMem (hf : (f.degree : A) ∉ u.asIdeal) :
    (f.pointMapHom.range.index : ℚ) / Nat.card f.pointMapHom.ker =
      Nat.card (AddCommGroup.primaryComponent W₂.toAffine.Point f.degree) /
        Nat.card (AddCommGroup.primaryComponent W₁.toAffine.Point f.degree) := by
  have hf0 : f ≠ 0 := by
    rintro rfl
    exact hf (by simp [degree_zero])
  have := f.finite_ker_pointMapHom hf0
  have := W₁.finite_primaryComponent u hf
  have hT : (Nat.card (AddCommGroup.primaryComponent W₁.toAffine.Point f.degree) : ℚ) ≠ 0 :=
    Nat.cast_ne_zero.mpr Nat.card_pos.ne'
  have hK : (Nat.card f.pointMapHom.ker : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr Nat.card_pos.ne'
  rw [div_eq_div_iff hK hT]
  exact_mod_cast index_range_mul_card_primaryComponent_of_degree_notMem u hf

end TauCeti.Isogeny.Hom
