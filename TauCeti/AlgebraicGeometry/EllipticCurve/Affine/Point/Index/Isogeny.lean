/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.Affine.Point.Index.NSmul
public import TauCeti.AlgebraicGeometry.EllipticCurve.Affine.Point.PrimaryReduction
public import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.Hom.Cokernel
public import TauCeti.AlgebraicGeometry.EllipticCurve.FormalGroup.Point.Depth

import TauCeti.Algebra.Group.Primary.Card
import TauCeti.Algebra.Module.Torsion.Int
import TauCeti.AlgebraicGeometry.EllipticCurve.Affine.FinitePoint
import TauCeti.AlgebraicGeometry.EllipticCurve.IntegralReduction
import TauCeti.AlgebraicGeometry.EllipticCurve.TateModule.Isogeny
import TauCeti.GroupTheory.Index.PrimaryComponent
import TauCeti.GroupTheory.Index.Map
import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.LeadingTerm
import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.Dual.Separability

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

At every finite place, including those dividing `n`, the ratio can be computed on the deep
levels of the formal groups. Let `E₁` and `E₂` be given by integral equations over `O_u`, write
`E_k(F_u)` for the image of the level `Ê(𝔪_u ^ k)` of the formal group, and let `φ` be an isogeny
with `φ^*ω₂ = c ω₁`, over `F_u` with `2 ≠ 0`. Then for all large `k`, with `j = k + ord(c)`,

`φ(E₁,k(F_u)) = E₂,j(F_u)`, `φ` is injective on `E₁,k(F_u)`, and
`[E₂(F_u) : φ E₁(F_u)] · [E₁(F_u) : E₁,k(F_u)] = [E₂(F_u) : E₂,j(F_u)] · #E₁(F_u)[φ]`.

Near the point at infinity `φ` divides the valuation of `x` by `v c ^ 2`
(`TauCeti.Isogeny.exists_valuation_xCoord_pointMap_mul_sq`), and a level is cut out by the
valuation of `x` (`WeierstrassCurve.mem_map_filtration_formalPointHomAdicCompletion_iff`), so
`φ(E₁,k) ⊆ E₂,j`; the dual, whose constant `c'` satisfies `c c' = n`, carries `E₂,j` back into
`E₁,(k+e) = n E₁,k`, where `n O_u = 𝔪_u ^ e`, and the deep levels have no `n`-torsion. This splits
the local factor into the differential constant, through `[E₂,k : E₂,j] = |c|_u⁻¹` when `c` is
integral, and the indices `[E(F_u) : E_k(F_u)]` of the levels, which involve the nonsingular
reduction and the Tamagawa number (Silverman VII.6).

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
* `TauCeti.Isogeny.eventually_map_pointMapHom_map_filtration_eq`: `φ(E₁,k) = E₂,j` for all large
  `k`.
* `TauCeti.Isogeny.eventually_map_filtration_inf_ker_pointMapHom_eq_bot`: `φ` is injective on
  `E₁,k` for all large `k`.
* `TauCeti.Isogeny.eventually_index_range_pointMapHom_mul_index_map_filtration`: the local
  cokernel/kernel ratio of `φ` is `[E₂ : E₂,j] / [E₁ : E₁,k]`.

## References

* [J. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], III.6, IV.4, VII.6 and X.4.
* J. W. S. Cassels, *Arithmetic on curves of genus 1. VIII. On conjectures of Birch and
  Swinnerton-Dyer*, J. Reine Angew. Math. 217 (1965), 180–199.
* E. F. Schaefer, *Class groups and Selmer groups*, J. Number Theory 56 (1996), 79–114,
  Lemma 3.8.
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
  -- `E₁(F_u)[n]` is finite, as `#(E₁(F_u) ⧸ n E₁(F_u)) = #E₁(F_u)[n] · #(O_u ⧸ n O_u)` is nonzero
  have hT : Nat.card (Submodule.torsionBy ℤ W₁.toAffine.Point f.degree) ≠ 0 :=
    left_ne_zero_of_mul <| hidx ▸ (WeierstrassCurve.finiteIndex_range_nsmul u W₁ hf).index_ne_zero
  -- `z(f̂) · z(f) = z([n])`, and `z([n]) = #(O_u ⧸ n O_u)`
  have h := f.index_range_nsmul_mul_card_ker_mul_card_ker_dual
  rw [TauCeti.natCard_ker_nsmulAddMonoidHom_eq_natCard_torsionBy, hidx] at h
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

/-! ### Deep levels of the formal group, at every finite place -/

namespace TauCeti.Isogeny

section FormalLevels

open WeierstrassCurve WithZero Filter

variable {A : Type*} [CommRing A] [IsDedekindDomain A]
  {F : Type*} [Field F] [Algebra A F] [IsFractionRing A F] (u : HeightOneSpectrum A)

local notation "O_u" => u.adicCompletionIntegers F
local notation "F_u" => u.adicCompletion F
local notation "m_u" => maximalIdeal O_u

-- Named: anonymous `local instance`s here get the same generated names as the ones in
-- `FormalGroup/Point/Torsion/Basic.lean`.
local instance isLinearTopology_adicCompletionIntegers_formalLevels :
    IsLinearTopology O_u O_u :=
  u.isAdic_maximalIdeal_adicCompletionIntegers (K := F) ▸ Ideal.isLinearTopology m_u

local instance fact_isAdic_maximalIdeal_formalLevels : Fact (IsAdic m_u) :=
  ⟨u.isAdic_maximalIdeal_adicCompletionIntegers (K := F)⟩

variable {C₁ C₂ : WeierstrassCurve (u.adicCompletionIntegers F)}
  [(C₁.baseChange (u.adicCompletion F)).IsElliptic]
  [(C₂.baseChange (u.adicCompletion F)).IsElliptic]
  {φ : Isogeny (C₁.baseChange (u.adicCompletion F)).toAffine
    (C₂.baseChange (u.adicCompletion F)).toAffine}

open scoped Classical in
/-- **An isogeny carries a deep level into a level**, read off from the `x`-coordinate: if `φ`
multiplies the valuation of `x` by `v c ^ (-2)` on the points with `R < v x`, then it carries
`E_k(F_u)` into `E_j(F_u)` for `v c · exp j = exp k`, as soon as `R < exp k ^ 2`. -/
private theorem map_pointMapHom_map_filtration_le {c : F_u} (hc0 : c ≠ 0) {R : ℤᵐ⁰}
    (hR : ∀ (x y : F_u) (h : (C₁.baseChange F_u).toAffine.Nonsingular x y), R < Valued.v x →
      (Hom.ofIsogeny φ).pointMap (.some x y h) ≠ 0 ∧
        Valued.v (Affine.Point.xCoord ((Hom.ofIsogeny φ).pointMap (.some x y h))) *
          Valued.v c ^ 2 = Valued.v x)
    {k j : ℕ} (hk : k ≠ 0) (hj : j ≠ 0) (hRk : R < exp (k : ℤ) ^ 2)
    (hjk : Valued.v c * exp (j : ℤ) = exp (k : ℤ)) :
    ((FormalGroupPoint.filtration C₁ m_u k).map (C₁.formalPointHomAdicCompletion u)).map
        (Hom.ofIsogeny φ).pointMapHom ≤
      (FormalGroupPoint.filtration C₂ m_u j).map (C₂.formalPointHomAdicCompletion u) := by
  rintro _ ⟨P, hP, rfl⟩
  rw [SetLike.mem_coe, mem_map_filtration_formalPointHomAdicCompletion_iff u C₁ hk] at hP
  rw [mem_map_filtration_formalPointHomAdicCompletion_iff u C₂ hj, Hom.pointMapHom_apply]
  rcases hP with rfl | hP
  · exact Or.inl (Hom.pointMap_zero _)
  have hP0 : P ≠ 0 := by
    rintro rfl
    rw [Affine.Point.xCoord_zero, map_zero] at hP
    exact (pow_ne_zero 2 exp_ne_zero) (le_zero_iff.mp hP)
  obtain ⟨x, y, h, rfl⟩ := Affine.Point.exists_eq_some_of_ne_zero hP0
  rw [Affine.Point.xCoord_some] at hP
  obtain ⟨-, hv⟩ := hR x y h (hRk.trans_le hP)
  -- `exp j ^ 2 · v c ^ 2 = exp k ^ 2 ≤ v x = v (x (φ P)) · v c ^ 2`
  have hc2 : 0 < Valued.v c ^ 2 :=
    pow_pos (zero_lt_iff.mpr ((Valued.v : Valuation F_u ℤᵐ⁰).ne_zero_iff.mpr hc0)) 2
  refine Or.inr (le_of_mul_le_mul_right ?_ hc2)
  rw [hv, ← mul_pow, mul_comm, hjk]
  exact hP

open scoped Classical in
/-- **An isogeny is injective on the deep levels**: if `deg φ` is nonzero in `A`, then for all
large `k` the kernel of `φ` meets `E_k(F_u)` trivially. The kernel is killed by `deg φ`, and the
deep levels have no `deg φ`-torsion. -/
theorem eventually_map_filtration_inf_ker_pointMapHom_eq_bot (hn : (φ.degree : A) ≠ 0) :
    ∀ᶠ k : ℕ in atTop,
      (FormalGroupPoint.filtration C₁ m_u k).map (C₁.formalPointHomAdicCompletion u) ⊓
        (Hom.ofIsogeny φ).pointMapHom.ker = ⊥ := by
  obtain ⟨e, hne⟩ := u.exists_span_algebraMap_adicCompletionIntegers_eq_maximalIdeal_pow (K := F) hn
  rw [map_natCast] at hne
  filter_upwards [eventually_gt_atTop e] with k hek
  refine eq_bot_iff.mpr fun P ⟨hP, hφP⟩ ↦ ?_
  have hφ : (Hom.ofIsogeny φ).pointMap P = 0 := by
    rw [← Hom.pointMapHom_apply]
    exact AddMonoidHom.mem_ker.mp hφP
  -- `deg φ • P = φ̂ (φ P) = 0`
  have h : (⟨P, hP⟩ : (FormalGroupPoint.filtration C₁ m_u k).map
      (C₁.formalPointHomAdicCompletion u)) = 0 :=
    injective_nsmul_map_filtration u C₁ hne hek <| Subtype.ext <| by
      simp only [AddSubgroup.coe_nsmul, smul_zero, ZeroMemClass.coe_zero]
      rw [← pointMap_dual_pointMap, hφ, Hom.pointMap_zero]
  exact (AddSubgroup.mem_bot).mpr (congrArg Subtype.val h)

open scoped Classical in
/-- **An isogeny maps the deep levels onto levels**: let `φ` pull the invariant differential back
as `φ^*ω₂ = c ω₁`, with `2 ≠ 0` in `F_u` and `deg φ` nonzero in `A`. Then for all large `k`,

`φ(E_k(F_u)) = E_j(F_u)`, where `v c · exp j = exp k`,

that is, `j = k + ord(c)`. The inclusion `⊆` is the effect `v(x ∘ φ) = v(x) · v c ^ (-2)` of `φ` on
the `x`-coordinate near the point at infinity
(`TauCeti.Isogeny.exists_valuation_xCoord_pointMap_mul_sq`). For the equality, the same holds for
the dual `φ̂` with its constant `c'`, and `c c' = deg φ`, so `φ̂` carries `E_j(F_u)` into
`E_(k+e)(F_u) = n E_k(F_u)`, where `n = deg φ` and `n O_u = 𝔪_u ^ e`; as `E_j(F_u)` has no
`n`-torsion, `φ(E_k(F_u))` is all of `E_j(F_u)`
(`AddMonoidHom.map_eq_of_map_le_of_map_le_map_nsmul`). -/
theorem eventually_map_pointMapHom_map_filtration_eq {c : F_u}
    (hc : φ.pullbackDifferential (Affine.invariantDifferential _) =
      c • Affine.invariantDifferential _)
    (h2 : (2 : F_u) ≠ 0) (hn : (φ.degree : A) ≠ 0) :
    ∀ᶠ k : ℕ in atTop, ∀ j : ℕ, Valued.v c * exp (j : ℤ) = exp (k : ℤ) →
      ((FormalGroupPoint.filtration C₁ m_u k).map (C₁.formalPointHomAdicCompletion u)).map
          (Hom.ofIsogeny φ).pointMapHom =
        (FormalGroupPoint.filtration C₂ m_u j).map (C₂.formalPointHomAdicCompletion u) := by
  obtain ⟨e, hne⟩ := u.exists_span_algebraMap_adicCompletionIntegers_eq_maximalIdeal_pow (K := F) hn
  rw [map_natCast] at hne
  -- the constant `c'` of the dual, with `v c · v c' = v (deg φ) = exp (-e)`
  obtain ⟨c', hc', -⟩ := φ.dual.existsUnique_pullbackDifferential_invariantDifferential_eq_smul
  have hcc' : Valued.v c * Valued.v c' = exp (-(e : ℤ)) := by
    rw [← map_mul, φ.mul_eq_degree_of_pullbackDifferential_eq_smul hc hc',
      ← u.valued_eq_exp_neg_of_span_eq_maximalIdeal_pow hne]
    simp
  have hvc : Valued.v c ≠ 0 := left_ne_zero_of_mul (hcc' ▸ exp_ne_zero)
  have hvc' : Valued.v c' ≠ 0 := right_ne_zero_of_mul (hcc' ▸ exp_ne_zero)
  have hc0 : c ≠ 0 := (Valued.v : Valuation F_u ℤᵐ⁰).ne_zero_iff.mp hvc
  have hc'0 : c' ≠ 0 := (Valued.v : Valuation F_u ℤᵐ⁰).ne_zero_iff.mp hvc'
  obtain ⟨R₁, hR₁⟩ := exists_valuation_xCoord_pointMap_mul_sq hc hc0 h2
    (Valued.v : Valuation F_u ℤᵐ⁰)
  obtain ⟨R₂, hR₂⟩ := exists_valuation_xCoord_pointMap_mul_sq hc' hc'0 h2
    (Valued.v : Valuation F_u ℤᵐ⁰)
  -- every value of `ℤᵐ⁰` lies below `exp m ^ 2` for all large `m`
  have hexp (R : ℤᵐ⁰) : ∃ N : ℕ, ∀ m : ℕ, N ≤ m → R < exp (m : ℤ) ^ 2 := by
    rcases eq_or_ne R 0 with rfl | hR
    · exact ⟨0, fun m _ ↦ pow_pos (zero_lt_iff.mpr exp_ne_zero) 2⟩
    refine ⟨(log R).toNat + 1, fun m hm ↦ ?_⟩
    rw [← exp_log hR, ← exp_nsmul, exp_lt_exp, nsmul_eq_mul]
    push_cast
    omega
  obtain ⟨N₁, hN₁⟩ := hexp R₁
  obtain ⟨N₂, hN₂⟩ := hexp R₂
  -- in additive terms, `log (v c) + log (v c') = -e`
  have hlog : log (Valued.v c) + log (Valued.v c') = -e := by
    rw [← exp_inj, exp_add, exp_log hvc, exp_log hvc', hcc']
  filter_upwards [eventually_ge_atTop (N₁ + N₂ + e + 1 + (log (Valued.v c)).natAbs)]
    with k hk j hjk
  have hj : (j : ℤ) = k - log (Valued.v c) := by
    rw [← exp_log hvc, ← exp_add, exp_inj] at hjk
    omega
  refine AddMonoidHom.map_eq_of_map_le_of_map_le_map_nsmul _ (Hom.ofIsogeny φ.dual).pointMapHom
    (fun P ↦ by rw [Hom.pointMapHom_apply, Hom.pointMapHom_apply, pointMap_dual_pointMap])
    (fun Q ↦ by rw [Hom.pointMapHom_apply, Hom.pointMapHom_apply, pointMap_pointMap_dual])
    (map_pointMapHom_map_filtration_le u hc0 hR₁ (by omega) (by omega) (hN₁ k (by omega)) hjk)
    ?_ (injective_nsmul_map_filtration u C₂ hne (by omega))
  -- `φ̂ (E_j) ≤ E_(k+e) = n E_k`
  rw [map_nsmulAddMonoidHom_map_filtration u C₁ hne (by omega)]
  refine map_pointMapHom_map_filtration_le u hc'0 hR₂ (by omega) (by omega) (hN₂ j (by omega)) ?_
  rw [← exp_log hvc', ← exp_add, exp_inj]
  push_cast
  omega

open scoped Classical in
/-- **The local cokernel/kernel ratio of an isogeny on deep levels**: let `φ` pull the invariant
differential back as `φ^*ω₂ = c ω₁`, with `2 ≠ 0` in `F_u` and `deg φ` nonzero in `A`. Then for
all large `k`,

`[E₂(F_u) : φ E₁(F_u)] · [E₁(F_u) : E_k(F_u)] = [E₂(F_u) : E_j(F_u)] · #E₁(F_u)[φ]`,

where `v c · exp j = exp k`, that is `j = k + ord(c)`. So the local factor
`[E₂(F_u) : φ E₁(F_u)] / #E₁(F_u)[φ]` of `φ` at `u`, including at a place dividing `deg φ`, is
`[E₂(F_u) : E_j(F_u)] / [E₁(F_u) : E_k(F_u)]`. No finiteness is asserted: indices are read as
`0` when infinite. For minimal models the indices of the levels are finite when the residue field
is, since then the kernel of reduction has finite index
(`WeierstrassCurve.finiteIndex_kerReduction`). -/
theorem eventually_index_range_pointMapHom_mul_index_map_filtration {c : F_u}
    (hc : φ.pullbackDifferential (Affine.invariantDifferential _) =
      c • Affine.invariantDifferential _)
    (h2 : (2 : F_u) ≠ 0) (hn : (φ.degree : A) ≠ 0) :
    ∀ᶠ k : ℕ in atTop, ∀ j : ℕ, Valued.v c * exp (j : ℤ) = exp (k : ℤ) →
      (Hom.ofIsogeny φ).pointMapHom.range.index *
          ((FormalGroupPoint.filtration C₁ m_u k).map (C₁.formalPointHomAdicCompletion u)).index =
        ((FormalGroupPoint.filtration C₂ m_u j).map (C₂.formalPointHomAdicCompletion u)).index *
          Nat.card (Hom.ofIsogeny φ).pointMapHom.ker := by
  filter_upwards [eventually_map_pointMapHom_map_filtration_eq u hc h2 hn,
    eventually_map_filtration_inf_ker_pointMapHom_eq_bot u hn] with k hmap hker j hjk
  have h := (Hom.ofIsogeny φ).pointMapHom.index_range_mul_index_mul_card_inf_ker
    ((FormalGroupPoint.filtration C₁ m_u k).map (C₁.formalPointHomAdicCompletion u))
  rwa [hker, AddSubgroup.card_bot, mul_one, hmap j hjk] at h

end FormalLevels

end TauCeti.Isogeny
