/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.Affine.Point.Index.NSmul
public import TauCeti.AlgebraicGeometry.EllipticCurve.Affine.Point.PrimaryReduction
public import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.Hom.Cokernel

import TauCeti.Algebra.Group.Primary.Card
import TauCeti.AlgebraicGeometry.EllipticCurve.Affine.FinitePoint
import TauCeti.AlgebraicGeometry.EllipticCurve.IntegralReduction
import TauCeti.AlgebraicGeometry.EllipticCurve.TateModule.Isogeny
import TauCeti.GroupTheory.Index.PrimaryComponent

/-!
# The local cokernel of an isogeny at a finite place

Let `A` be a Dedekind domain with fraction field `F`, let `u` be a height-one prime of `A` with
finite residue field, and let `f : E₁ → E₂` be a morphism of elliptic curves over the completion
`F_u` whose degree `n` is nonzero in `A`, with `O_u` the ring of integers of `F_u`. The local
factor of `f` in Cassels' proof that the Birch–Swinnerton-Dyer quotient is an isogeny invariant is
the ratio

`z(f) = #(E₂(F_u) ⧸ f E₁(F_u)) / #E₁(F_u)[f]`.

This file shows that it is defined, and that its product with the local factor of the dual
isogeny `f̂` is the inverse of the normalised absolute value of `n` at `u`:

`#(E₂(F_u) ⧸ f E₁(F_u)) · #(E₁(F_u) ⧸ f̂ E₂(F_u)) = #E₁(F_u)[f] · #E₂(F_u)[f̂] · #(O_u ⧸ n O_u)`.

This holds also at the places dividing `n`. Since `f̂ ∘ f` is multiplication by `n`, the ratios
satisfy `z(f̂) · z(f) = z([n])`
(`TauCeti.Isogeny.Hom.index_range_nsmul_mul_card_ker_mul_card_ker_dual`), and
`z([n]) = #(O_u ⧸ n O_u)` (`WeierstrassCurve.index_range_nsmul_eq_natCard_torsionBy_mul`). At a
place prime to `n` the last factor is `1`, so there the local factors of `f` and `f̂` are inverse.
Finiteness of the cokernel comes from the same composite: the image of `f` contains
`n E₂(F_u)`, which has finite index.

At a place prime to `n`, the ratio itself is carried by finite torsion. Write `E(F_u)[n^∞]` for
the `n`-primary component of `E(F_u)`, the points killed by a power of `n`, which is finite. Then

`z(f) = #E₂(F_u)[n^∞] / #E₁(F_u)[n^∞]`.

Indeed `E₂(F_u)` has a subgroup of finite index on which `n` is bijective (the kernel of reduction
of a minimal model), so every point of `E₂(F_u)` is divisible by `n`, hence lies in the image of
`f`, up to an element of `E₂(F_u)[n^∞]`; and the inverse image of `E₂(F_u)[n^∞]` under `f` is
`E₁(F_u)[n^∞]`, since `f̂ ∘ f = [n]`.

At a place of good reduction prime to `n`, the ratio is `1`. Reduction identifies `E(F_u)[n^∞]`
with the `n`-primary component of the reduced curve over the residue field `k`, and isogenous
curves with good reduction have reductions with the same number of points over `k`, because their
Frobenius traces agree. Finite groups of the same order have `n`-primary components of the same
order, so `#(E₂(F_u) ⧸ f E₁(F_u)) = #E₁(F_u)[f]`.

## Main results

* `TauCeti.Isogeny.Hom.finiteIndex_range_pointMapHom_of_degree_ne_zero`: the image of
  `E₁(F_u)` has finite index in `E₂(F_u)`.
* `TauCeti.Isogeny.Hom.index_range_mul_index_range_dual_eq_card_ker_mul_card_ker_dual_mul`: the
  local cokernel/kernel ratios of `f` and of `f̂` multiply to `#(O_u ⧸ n O_u)`.
* `TauCeti.Isogeny.Hom.index_range_mul_index_range_dual_eq_card_ker_mul_card_ker_dual`: at a place
  prime to `n`, they are inverse.
* `TauCeti.Isogeny.Hom.index_range_mul_card_primaryComponent_of_degree_notMem` and
  `TauCeti.Isogeny.Hom.index_range_div_card_ker_of_degree_notMem`: the local cokernel/kernel ratio
  of `f` is the ratio of the orders of the `deg f`-primary components.
* `TauCeti.Isogeny.Hom.index_range_div_card_ker_eq_reduction`: at good reduction prime to `n`,
  compute this ratio using only the primary components of the finite reduced point groups.
* `TauCeti.Isogeny.Hom.index_range_eq_card_ker_of_isElliptic` and
  `TauCeti.Isogeny.Hom.index_range_eq_card_ker_of_isElliptic_integralModel`: at good reduction
  prime to `n`, the ratio is `1`.

## References

* [J. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], III.6, VII.6 and X.4.
* J. W. S. Cassels, *Arithmetic on curves of genus 1. VIII. On conjectures of Birch and
  Swinnerton-Dyer*, J. Reine Angew. Math. 217 (1965), 180–199.
-/

public section

open IsDedekindDomain IsLocalRing

namespace TauCeti.Isogeny.Hom

variable {A : Type*} [CommRing A] [IsDedekindDomain A]
  {F : Type*} [Field F] [Algebra A F] [IsFractionRing A F]
  (u : HeightOneSpectrum A) [Finite (A ⧸ u.asIdeal)] [DecidableEq (u.adicCompletion F)]
  {W₁ W₂ : WeierstrassCurve (u.adicCompletion F)} [W₁.IsElliptic] [W₂.IsElliptic]
  {f : Hom W₁.toAffine W₂.toAffine}

/-- **The local cokernel of a morphism is finite** at a place where its degree is nonzero in `A`:
the image of `E₁(F_u)` has finite index in `E₂(F_u)`, since it contains `deg f · E₂(F_u)`. The
place may divide the degree. -/
theorem finiteIndex_range_pointMapHom_of_degree_ne_zero (hf : (f.degree : A) ≠ 0) :
    f.pointMapHom.range.FiniteIndex := by
  have := WeierstrassCurve.finiteIndex_range_nsmul u W₂ hf
  refine AddSubgroup.finiteIndex_of_le (H := (nsmulAddMonoidHom f.degree).range) ?_
  rintro P ⟨Q, rfl⟩
  exact ⟨f.dual.pointMap Q, by simp [pointMap_dual_pointMap]⟩

/-- **The local cokernel/kernel ratios of a morphism and of its dual multiply to
`#(O_u ⧸ deg f · O_u)`** at a place where `n = deg f` is nonzero in `A`:

`#(E₂(F_u) ⧸ f E₁(F_u)) · #(E₁(F_u) ⧸ f̂ E₂(F_u)) = #E₁(F_u)[f] · #E₂(F_u)[f̂] · #(O_u ⧸ n O_u)`,

all five orders being finite. The last factor is the inverse of the normalised absolute value of
`n` at `u`; it is `1` exactly when `u` is prime to `n`. -/
theorem index_range_mul_index_range_dual_eq_card_ker_mul_card_ker_dual_mul
    (hf : (f.degree : A) ≠ 0) :
    f.pointMapHom.range.index * f.dual.pointMapHom.range.index =
      Nat.card f.pointMapHom.ker * Nat.card f.dual.pointMapHom.ker *
        Nat.card (u.adicCompletionIntegers F ⧸
          Ideal.span {(f.degree : u.adicCompletionIntegers F)}) := by
  have hidx := WeierstrassCurve.index_range_nsmul_eq_natCard_torsionBy_mul u W₁ hf
  have hker : Nat.card (nsmulAddMonoidHom (α := W₁.toAffine.Point) f.degree).ker =
      Nat.card (Submodule.torsionBy ℤ W₁.toAffine.Point f.degree) :=
    Nat.card_congr (Equiv.subtypeEquivRight fun P ↦ by
      rw [AddMonoidHom.mem_ker, nsmulAddMonoidHom_apply, Submodule.mem_torsionBy_iff,
        natCast_zsmul])
  -- `E₁(F_u)[n]` is finite, as `#(E₁(F_u) ⧸ n E₁(F_u)) = #E₁(F_u)[n] · #(O_u ⧸ n O_u)` is nonzero
  have hT : Nat.card (Submodule.torsionBy ℤ W₁.toAffine.Point f.degree) ≠ 0 :=
    left_ne_zero_of_mul <| hidx ▸ (WeierstrassCurve.finiteIndex_range_nsmul u W₁ hf).index_ne_zero
  -- `z(f̂) · z(f) = z([n])`, and `z([n]) = #(O_u ⧸ n O_u)`
  have h := f.index_range_nsmul_mul_card_ker_mul_card_ker_dual
  rw [hker, hidx] at h
  refine Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hT) ?_
  linear_combination h.symm

/-- **The local cokernel/kernel ratios of a morphism and of its dual are inverse** at a place
prime to the degree:
`#(E₂(F_u) ⧸ f E₁(F_u)) · #(E₁(F_u) ⧸ f̂ E₂(F_u)) = #E₁(F_u)[f] · #E₂(F_u)[f̂]`, all four orders
being finite. -/
theorem index_range_mul_index_range_dual_eq_card_ker_mul_card_ker_dual
    (hf : (f.degree : A) ∉ u.asIdeal) :
    f.pointMapHom.range.index * f.dual.pointMapHom.range.index =
      Nat.card f.pointMapHom.ker * Nat.card f.dual.pointMapHom.ker := by
  rw [index_range_mul_index_range_dual_eq_card_ker_mul_card_ker_dual_mul u
      (ne_of_mem_of_not_mem u.asIdeal.zero_mem hf).symm,
    ← map_natCast (algebraMap A (u.adicCompletionIntegers F)),
    u.natCard_quotient_span_algebraMap_adicCompletionIntegers hf, mul_one]

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
  have := W₁.finite_primaryComponent u (ne_of_mem_of_not_mem u.asIdeal.zero_mem hf).symm
  have hT : (Nat.card (AddCommGroup.primaryComponent W₁.toAffine.Point f.degree) : ℚ) ≠ 0 :=
    Nat.cast_ne_zero.mpr Nat.card_pos.ne'
  have hK : (Nat.card f.pointMapHom.ker : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr Nat.card_pos.ne'
  rw [div_eq_div_iff hK hT]
  exact_mod_cast index_range_mul_card_primaryComponent_of_degree_notMem u hf

section GoodReduction

variable {u} {C₁ C₂ : WeierstrassCurve (u.adicCompletionIntegers F)} [C₁.IsElliptic]
  [C₂.IsElliptic]

local notation "R_u" => Valuation.valuationSubring
  (Valued.v : Valuation (u.adicCompletion F) (WithZero (Multiplicative ℤ)))

/-- At good reduction and away from the degree, the local isogeny ratio is computed by the
primary components of the finite reduced point groups. The numerator belongs to the target
curve and the denominator to the source curve. -/
theorem index_range_div_card_ker_eq_reduction [DecidableEq (ResidueField R_u)]
    (f : Hom (C₁.baseChange (u.adicCompletion F)).toAffine
      (C₂.baseChange (u.adicCompletion F)).toAffine)
    (hf : (f.degree : A) ∉ u.asIdeal) :
    (f.pointMapHom.range.index : ℚ) / Nat.card f.pointMapHom.ker =
      Nat.card (AddCommGroup.primaryComponent
        ((WeierstrassCurve.integralModel R_u (C₂.baseChange (u.adicCompletion F))).map
          (residue R_u)).toAffine.Point f.degree) /
      Nat.card (AddCommGroup.primaryComponent
        ((WeierstrassCurve.integralModel R_u (C₁.baseChange (u.adicCompletion F))).map
          (residue R_u)).toAffine.Point f.degree) := by
  rw [index_range_div_card_ker_of_degree_notMem u hf,
    Nat.card_congr (C₁.primaryReductionAddEquiv hf).toEquiv,
    Nat.card_congr (C₂.primaryReductionAddEquiv hf).toEquiv]

/-- **The local cokernel/kernel ratio of a morphism is `1` at good reduction** away from its
degree: if `E₁` and `E₂` have good reduction at `u`, given by elliptic equations over `O_u`, and
`deg f` is prime to `u`, then `#(E₂(F_u) ⧸ f E₁(F_u)) = #E₁(F_u)[f]`. -/
theorem index_range_eq_card_ker_of_isElliptic
    (f : Hom (C₁.baseChange (u.adicCompletion F)).toAffine
      (C₂.baseChange (u.adicCompletion F)).toAffine)
    (hf : (f.degree : A) ∉ u.asIdeal) :
    f.pointMapHom.range.index = Nat.card f.pointMapHom.ker := by
  classical
  have hf0 : f ≠ 0 := by
    rintro rfl
    exact hf (by simp [degree_zero])
  -- the reductions have the same number of points, hence equinumerous primary components
  have hcard := (C₁.natCard_point_reduction_baseChange_adicCompletion).symm.trans
    (((toIsogeny hf0).natCard_point_reduction_eq inferInstance).trans
      C₂.natCard_point_reduction_baseChange_adicCompletion)
  -- `R_u` is `u.adicCompletionIntegers F` by definition
  have : Finite (ResidueField R_u) :=
    inferInstanceAs (Finite (ResidueField (u.adicCompletionIntegers F)))
  have h := index_range_mul_card_primaryComponent_of_degree_notMem u hf
  rw [Nat.card_congr (C₁.primaryReductionAddEquiv hf).toEquiv,
    Nat.card_congr (C₂.primaryReductionAddEquiv hf).toEquiv,
    TauCeti.AddCommGroup.natCard_primaryComponent_eq_of_natCard_eq hcard f.degree, mul_comm] at h
  exact Nat.eq_of_mul_eq_mul_left Nat.card_pos h

open _root_.ValuativeRel WeierstrassCurve in
/-- **The local cokernel/kernel ratio is `1` at good reduction, for the integral model over
`𝒪[F_u]`**: the variant of `index_range_eq_card_ker_of_isElliptic` for curves over `F_u` whose
integral model over the ring of integers `𝒪[F_u]` of the valuative relation is elliptic. This is
the form in which good reduction at almost every place is available
(`TauCeti.eventually_isElliptic_integralModel_adicCompletion`); the model is carried to `O_u`
along `IsDedekindDomain.HeightOneSpectrum.integerEquivAdicCompletionIntegers`. -/
theorem index_range_eq_card_ker_of_isElliptic_integralModel
    {V₁ V₂ : WeierstrassCurve (u.adicCompletion F)} [V₁.IsElliptic] [V₂.IsElliptic]
    [IsIntegral 𝒪[u.adicCompletion F] V₁] [(integralModel 𝒪[u.adicCompletion F] V₁).IsElliptic]
    [IsIntegral 𝒪[u.adicCompletion F] V₂] [(integralModel 𝒪[u.adicCompletion F] V₂).IsElliptic]
    (f : Hom V₁.toAffine V₂.toAffine) (hf : (f.degree : A) ∉ u.asIdeal) :
    f.pointMapHom.range.index = Nat.card f.pointMapHom.ker := by
  -- `C.map e` is an elliptic model over `O_u` with the same base change to `F_u` as `C`
  have model (V : WeierstrassCurve (u.adicCompletion F)) [IsIntegral 𝒪[u.adicCompletion F] V]
      [(integralModel 𝒪[u.adicCompletion F] V).IsElliptic] :
      ∃ C : WeierstrassCurve (u.adicCompletionIntegers F),
        C.IsElliptic ∧ C.baseChange (u.adicCompletion F) = V := by
    refine ⟨(integralModel 𝒪[u.adicCompletion F] V).map
      u.integerEquivAdicCompletionIntegers.toRingHom, inferInstance, ?_⟩
    conv_rhs => rw [← baseChange_integralModel_eq 𝒪[u.adicCompletion F] V]
    rw [WeierstrassCurve.baseChange, WeierstrassCurve.baseChange, WeierstrassCurve.map_map]
    exact congrArg _ (RingHom.ext u.coe_integerEquivAdicCompletionIntegers)
  obtain ⟨C₁, _, rfl⟩ := model V₁
  obtain ⟨C₂, _, rfl⟩ := model V₂
  exact index_range_eq_card_ker_of_isElliptic f hf

end GoodReduction

end TauCeti.Isogeny.Hom
