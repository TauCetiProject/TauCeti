/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.Hom.Cokernel
public import TauCeti.NumberTheory.LocalField.MaximalPrime
-- Proof-only: the index of `n E(F_u)` over the completion of a Dedekind domain.
import TauCeti.AlgebraicGeometry.EllipticCurve.Affine.Point.Index.NSmul
-- Proof-only: a local field is its own completion at its maximal ideal.
import TauCeti.NumberTheory.LocalField.AdicCompletion
import TauCeti.AlgebraicGeometry.EllipticCurve.Affine.Point.MapAlong
import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.MulByInt.KernelCard
import TauCeti.Algebra.Module.Torsion.Int
import TauCeti.GroupTheory.Index.NSmul

/-!
# The index of `n E(K)` over a nonarchimedean local field

Let `K` be a nonarchimedean local field with valuation ring `𝒪[K]`, and let `E` be an elliptic
curve over `K`. For a natural number `n` nonzero in `K`,

`#(E(K) ⧸ n E(K)) = #E(K)[n] · #(𝒪[K] ⧸ n 𝒪[K])`,

and for a morphism `f : E₁ → E₂` over `K` whose degree `n` is nonzero in `K`, the local
cokernel/kernel ratios of `f` and of its dual `f̂` multiply to the same factor:

`#(E₂(K) ⧸ f E₁(K)) · #(E₁(K) ⧸ f̂ E₂(K)) = #E₁(K)[f] · #E₂(K)[f̂] · #(𝒪[K] ⧸ n 𝒪[K])`.

The last factor is the inverse of the normalized absolute value of `n`
(`TauCeti.natCard_quotient_span_natCast`). Both identities are already known over the completion
`F_u` of the fraction field of a Dedekind domain at a height-one prime with finite residue field
(`WeierstrassCurve.index_range_nsmul_eq_natCard_torsionBy_mul`). A nonarchimedean local field is
such a completion of itself, at the maximal ideal of `𝒪[K]`
(`TauCeti.bijective_algebraMap_adicCompletion_maximalPrime`), and the points of `E` move along
that identification (`WeierstrassCurve.Affine.Point.mapAlongAddEquiv`). This puts the local
factors of Cassels' comparison of the Selmer groups of an isogeny and of its dual in the setting of
local Tate duality, which is stated over nonarchimedean local fields.

## Main results

* `WeierstrassCurve.index_range_nsmul_eq_natCard_torsionBy_mul_of_localField`: the index of
  `n E(K)` is `#E(K)[n] · #(𝒪[K] ⧸ n 𝒪[K])`.
* `index_range_mul_index_range_dual_eq_card_ker_mul_card_ker_dual_mul_of_localField`, in the
  namespace `TauCeti.Isogeny.Hom`: the cokernel/kernel ratios of `f` and `f̂` multiply to
  `#(𝒪[K] ⧸ deg f · 𝒪[K])`.

## References

* [J. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], VII.6 and X.4.
* J. W. S. Cassels, *Arithmetic on curves of genus 1. VIII. On conjectures of Birch and
  Swinnerton-Dyer*, J. Reine Angew. Math. 217 (1965), 180–199.
-/

public section

open ValuativeRel

namespace WeierstrassCurve

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] [DecidableEq K] (W : WeierstrassCurve K) [W.IsElliptic] {n : ℕ}

/-- **The local Kummer index over a nonarchimedean local field**: for an elliptic curve `E` over
`K` and a natural number `n` nonzero in `K`,

`#(E(K) ⧸ n E(K)) = #E(K)[n] · #(𝒪[K] ⧸ n 𝒪[K])`.

The residue characteristic may divide `n`; when it does not, the last factor is `1`. -/
theorem index_range_nsmul_eq_natCard_torsionBy_mul_of_localField (hn : (n : K) ≠ 0) :
    (nsmulAddMonoidHom (α := W.toAffine.Point) n).range.index =
      Nat.card (Submodule.torsionBy ℤ W.toAffine.Point n) *
        Nat.card (𝒪[K] ⧸ Ideal.span {(n : 𝒪[K])}) := by
  classical
  let u := TauCeti.maximalPrime K
  have : Finite ((valuation K).valuationSubring ⧸ u.asIdeal) := inferInstanceAs (Finite 𝓀[K])
  let i := algebraMap K (u.adicCompletion K)
  -- `K` is its own completion at `u`, so `E(K)` is the group of points of `E` over `K_u`
  let eqv := Affine.Point.mapAlongAddEquiv (W := W) i
    (TauCeti.bijective_algebraMap_adicCompletion_maximalPrime K)
  have hn' : (n : (valuation K).valuationSubring) ≠ 0 := fun h ↦ hn (by
    simpa using congrArg (fun x : (valuation K).valuationSubring ↦ (x : K)) h)
  -- and `𝒪[K]` is the ring of integers of `K_u`
  let e := RingEquiv.ofBijective _
    (TauCeti.bijective_algebraMap_adicCompletionIntegers_maximalPrime K)
  rw [eqv.index_range_nsmulAddMonoidHom n,
    (W.map i).index_range_nsmul_eq_natCard_torsionBy_mul u hn',
    ← TauCeti.natCard_ker_nsmulAddMonoidHom_eq_natCard_torsionBy,
    ← TauCeti.natCard_ker_nsmulAddMonoidHom_eq_natCard_torsionBy, eqv.card_ker_nsmulAddMonoidHom]
  refine congrArg _ (Nat.card_congr (Ideal.quotientEquiv _ _ e ?_).toEquiv).symm
  rw [Ideal.map_span, Set.image_singleton, map_natCast]

end WeierstrassCurve

namespace TauCeti.Isogeny.Hom

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] [DecidableEq K]
  {W₁ W₂ : WeierstrassCurve K} [W₁.IsElliptic] [W₂.IsElliptic] (f : Hom W₁.toAffine W₂.toAffine)

/-- **The local cokernel/kernel ratios of a morphism and of its dual over a nonarchimedean local
field**: if the degree `n` of `f` is nonzero in `K`, then

`#(E₂(K) ⧸ f E₁(K)) · #(E₁(K) ⧸ f̂ E₂(K)) = #E₁(K)[f] · #E₂(K)[f̂] · #(𝒪[K] ⧸ n 𝒪[K])`,

all orders being finite. The residue characteristic may divide `n`. -/
theorem index_range_mul_index_range_dual_eq_card_ker_mul_card_ker_dual_mul_of_localField
    (hf : (f.degree : K) ≠ 0) :
    f.pointMapHom.range.index * f.dual.pointMapHom.range.index =
      Nat.card f.pointMapHom.ker * Nat.card f.dual.pointMapHom.ker *
        Nat.card (𝒪[K] ⧸ Ideal.span {(f.degree : 𝒪[K])}) := by
  have hidx := W₁.index_range_nsmul_eq_natCard_torsionBy_mul_of_localField hf
  have : Finite (AddSubgroup.torsionBy W₁.toAffine.Point (f.degree : ℤ)) :=
    W₁.finite_torsionBy (by exact_mod_cast fun h ↦ hf (by simp [h]))
  have hT : 0 < Nat.card (Submodule.torsionBy ℤ W₁.toAffine.Point f.degree) := Nat.card_pos
  -- `z(f̂) · z(f) = z([n])` for the cokernel/kernel ratios `z`
  have h := f.index_range_nsmul_mul_card_ker_mul_card_ker_dual
  rw [TauCeti.natCard_ker_nsmulAddMonoidHom_eq_natCard_torsionBy, hidx] at h
  refine Nat.eq_of_mul_eq_mul_left hT ?_
  linear_combination h.symm

end TauCeti.Isogeny.Hom
