/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.Affine.Point.Index.NSmul
public import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.Hom.Cokernel

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

## Main results

* `TauCeti.Isogeny.Hom.finiteIndex_range_pointMapHom_of_degree_notMem`: the image of
  `E₁(F_u)` has finite index in `E₂(F_u)`.
* `TauCeti.Isogeny.Hom.index_range_mul_index_range_dual_eq_card_ker_mul_card_ker_dual`: the local
  cokernel/kernel ratios of `f` and of `f̂` are inverse.

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

end TauCeti.Isogeny.Hom
