/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Representation.FiniteOrder
public import TauCeti.Algebra.Coalgebra.Comodule.LinearlyReductive
import Mathlib.Data.ZMod.QuotientGroup
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import TauCeti.Algebra.AlgebraicGroup.Hopf.LeftTranslation
import TauCeti.Algebra.AlgebraicGroup.Representation.JordanDecomposition.Basic
import TauCeti.Algebra.AlgebraicGroup.Representation.UnipotentPoint.CharP
import TauCeti.Algebra.Coalgebra.Comodule.MatrixCoefficient.Morphism
import TauCeti.Algebra.Coalgebra.Comodule.LinearlyReductive.Fixed
import TauCeti.RingTheory.Invariant.Free

/-!
# Finite subgroups of linearly reductive groups

Let `H` be the coordinate Hopf algebra of an affine group of finite type over a field `k`. If the
group is linearly reductive, then every finite subgroup `Γ` of its group of rational points has
order invertible in `k`. Consequently every rational point of finite order is semisimple. In
characteristic `p` a nonidentity unipotent rational point would have order a nontrivial power of
`p`, so there is none; over a perfect field of characteristic `p` every rational point of a
linearly reductive group is therefore semisimple.

Left translation by `Γ` is a free action on the coordinate algebra: a translate of a geometric
point is the point itself only for the identity translation. By the theory of free actions of
finite groups, some function `c` has orbit sum `∑ γ ∈ Γ, γ • c = 1`. The orbit sum is the
regular matrix coefficient of the functional `∑ γ ∈ Γ, γ⁻¹`, a comodule endomorphism, so linear
reductivity lifts the invariant `1` in its image to an invariant preimage.
The only invariants of the regular comodule are the constants, and the orbit sum multiplies
constants by the order of `Γ`. Hence that order is nonzero in `k`.

## Main declarations

* `TauCeti.HopfAlgebra.natCast_card_ne_zero_of_isLinearlyReductive`: a finite subgroup of the
  rational points of a linearly reductive group of finite type has order nonzero in the base
  field.
* `TauCeti.HopfAlgebra.natCast_orderOf_ne_zero_of_isLinearlyReductive`: the order of a
  finite-order rational point is nonzero in the base field.
* `TauCeti.HopfAlgebra.isSemisimplePoint_of_isLinearlyReductive_of_isOfFinOrder`: every rational
  point of finite order is semisimple.
* `TauCeti.HopfAlgebra.IsUnipotentPoint.eq_one_of_isLinearlyReductive`: in characteristic `p`,
  the only unipotent rational point is the identity.
* `TauCeti.HopfAlgebra.isSemisimplePoint_of_isLinearlyReductive_of_charP`: over a perfect field
  of characteristic `p`, every rational point is semisimple.

## References

* M. Nagata, *Complete reducibility of rational representations of a matric group*,
  J. Math. Kyoto Univ. **1** (1961), 87–99.
* J. S. Milne, *Algebraic Groups* (2017), §12.g.
* S. U. Chase, D. K. Harrison and A. Rosenberg, *Galois theory and Galois cohomology of
  commutative rings*, Mem. Amer. Math. Soc. **52** (1965), 15–33.
-/

public section

open WithConv

namespace TauCeti.HopfAlgebra

universe u v

variable {k : Type u} {H : Type v} [Field k] [CommRing H] [_root_.HopfAlgebra k H]

/-- A subgroup of rational points acts on the coordinate algebra by pullback along left
translation by the inverse point. -/
private noncomputable def leftTranslationHom (Γ : Subgroup (WithConv (H →ₐ[k] k))) :
    Γ →* (H ≃ₐ[k] H) where
  toFun γ := leftTranslationAlgEquiv ((γ⁻¹ : Γ) : WithConv (H →ₐ[k] k))
  map_one' := by simp
  map_mul' γ δ := by simp

/-- **Finite subgroups of a linearly reductive group have invertible order.** If the affine group
of finite type represented by `H` is linearly reductive, then the order of every finite subgroup
of its group of rational points is nonzero in the base field. -/
theorem natCast_card_ne_zero_of_isLinearlyReductive [Algebra.FiniteType k H]
    (hH : Coalgebra.IsLinearlyReductive.{u, v, u} k H)
    (Γ : Subgroup (WithConv (H →ₐ[k] k))) [Finite Γ] :
    (Nat.card Γ : k) ≠ 0 := by
  classical
  have := Fintype.ofFinite Γ
  let : MulSemiringAction Γ H := MulSemiringAction.compHom H (leftTranslationHom Γ)
  have : SMulCommClass Γ k H := ⟨fun γ r a ↦ map_smul (leftTranslationHom Γ γ) r a⟩
  -- By construction, `γ` acts by pullback along left translation by `γ⁻¹`.
  have hsmul (γ : Γ) (a : H) :
      γ • a = leftTranslationAlgEquiv ((γ⁻¹ : Γ) : WithConv (H →ₐ[k] k)) a :=
    rfl
  -- Translation by `γ ≠ 1` fixes no geometric point, so some function has orbit sum `1`.
  obtain ⟨c, hc⟩ := MulSemiringAction.exists_sum_smul_eq_one
    (G := Γ) fun γ hγ ↦
      (MulSemiringAction.span_range_smul_sub_eq_top_iff (k := k) (K := AlgebraicClosure k)
        γ).mpr fun x hx ↦ hγ <| by
          have hfix : x.comp (leftTranslationAlgEquiv
              ((γ⁻¹ : Γ) : WithConv (H →ₐ[k] k))).toAlgHom = x :=
            AlgHom.ext fun a ↦ by simpa [hsmul] using DFunLike.congr_fun hx a
          simpa using (comp_leftTranslationAlgEquiv_eq_self_iff
            (algebraMap k (AlgebraicClosure k)).injective _ x).mp hfix
  -- The orbit sum is the regular matrix coefficient of the functional `∑ γ, γ⁻¹`.
  let T : Comodule.Hom k H H H := Comodule.matrixCoefficientHom (M := H)
    (∑ γ : Γ, ((γ⁻¹ : Γ) : WithConv (H →ₐ[k] k)).ofConv.toLinearMap)
  have hT (a : H) : T a = ∑ γ : Γ, γ • a := by
    rw [Comodule.matrixCoefficientHom_apply, ← Comodule.matrixCoefficientBilinear_apply_apply,
      map_sum, LinearMap.sum_apply]
    exact Finset.sum_congr rfl fun γ _ ↦ by
      rw [hsmul, leftTranslationAlgEquiv_apply, Comodule.matrixCoefficientBilinear_apply_apply]
      rfl
  have hone : (1 : H) ∈ Comodule.fixedSubcomodule k H H := by
    simp [Comodule.mem_fixedSubcomodule, Algebra.TensorProduct.one_def]
  -- Linear reductivity lifts `1` to an invariant, hence constant, function.
  obtain ⟨m, hm, hTm⟩ :=
    T.exists_fixed_preimage_of_isLinearlyReductive hH hone ⟨c, (hT c).trans hc⟩
  have hmconst : m = Coalgebra.counit (R := k) m • (1 : H) := by
    have h := Coalgebra.rTensor_counit_comul (R := k) m
    rw [← Comodule.instSelf_coact (R := k), (Comodule.mem_fixedSubcomodule).mp hm,
      LinearMap.rTensor_tmul] at h
    simpa using (congrArg (TensorProduct.lid k H) h).symm
  have hT1 : T 1 = (Nat.card Γ : k) • (1 : H) := by
    simp [hT, Nat.card_eq_fintype_card, Finset.card_univ, Nat.cast_smul_eq_nsmul k]
  intro hcard
  rw [hmconst, map_smul, hT1, hcard, zero_smul, smul_zero] at hTm
  simpa using congrArg (Coalgebra.counit (R := k) (A := H)) hTm

/-- The order of a finite-order rational point of a linearly reductive group of finite type is
nonzero in the base field. In characteristic `p`, no rational point has order divisible by
`p`. -/
theorem natCast_orderOf_ne_zero_of_isLinearlyReductive [Algebra.FiniteType k H]
    (hH : Coalgebra.IsLinearlyReductive.{u, v, u} k H)
    {g : WithConv (H →ₐ[k] k)} (hg : IsOfFinOrder g) :
    (orderOf g : k) ≠ 0 := by
  have := finite_zpowers.mpr hg
  simpa [Nat.card_zpowers] using
    natCast_card_ne_zero_of_isLinearlyReductive hH (Subgroup.zpowers g)

/-- Every rational point of finite order of a linearly reductive group of finite type is
semisimple, in every characteristic. -/
theorem isSemisimplePoint_of_isLinearlyReductive_of_isOfFinOrder [Algebra.FiniteType k H]
    (hH : Coalgebra.IsLinearlyReductive.{u, v, u} k H)
    {g : WithConv (H →ₐ[k] k)} (hg : IsOfFinOrder g) :
    IsSemisimplePoint g :=
  isSemisimplePoint_of_pow_eq_one
    (by simpa using natCast_orderOf_ne_zero_of_isLinearlyReductive hH hg) (pow_orderOf_eq_one g)

section CharP

variable {k H : Type u} [Field k] [CommRing H] [_root_.HopfAlgebra k H] [Algebra.FiniteType k H]

/-- In characteristic `p`, a linearly reductive group of finite type has no nonidentity unipotent
rational point: such a point would have order a nontrivial power of `p`. -/
theorem IsUnipotentPoint.eq_one_of_isLinearlyReductive (p : ℕ) [Fact p.Prime] [CharP k p]
    (hH : Coalgebra.IsLinearlyReductive.{u, u, u} k H)
    {g : WithConv (H →ₐ[k] k)} (hg : IsUnipotentPoint g) : g = 1 := by
  obtain ⟨n, hn⟩ := hg.exists_pow_char_pow_eq_one p
  have hprime : p.Prime := Fact.out
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow hprime).mp (orderOf_dvd_of_pow_eq_one hn)
  have hord := natCast_orderOf_ne_zero_of_isLinearlyReductive hH
    (isOfFinOrder_iff_pow_eq_one.mpr ⟨p ^ n, pow_pos hprime.pos n, hn⟩)
  rw [hj, Nat.cast_pow, CharP.cast_eq_zero] at hord
  rcases Nat.eq_zero_or_pos j with rfl | hjpos
  · rwa [pow_zero, orderOf_eq_one_iff] at hj
  · exact absurd (zero_pow hjpos.ne') hord

/-- **Over a perfect field of characteristic `p`, every rational point of a linearly reductive
group of finite type is semisimple.** -/
theorem isSemisimplePoint_of_isLinearlyReductive_of_charP (p : ℕ) [Fact p.Prime] [CharP k p]
    [PerfectField k] (hH : Coalgebra.IsLinearlyReductive.{u, u, u} k H)
    (g : WithConv (H →ₐ[k] k)) : IsSemisimplePoint g := by
  have hu : IsUnipotentPoint (Point.unipotentPart k H k g) :=
    (isUnipotentPoint_def _).mpr fun M ↦ Point.isUnipotent_pointsAction_unipotentPart k H k g M
  rw [← Point.semisimplePart_mul_unipotentPart k H k g,
    hu.eq_one_of_isLinearlyReductive p hH, mul_one, isSemisimplePoint_def]
  exact fun M ↦ Point.isSemisimple_pointsAction_semisimplePart k H k g M

end CharP

end TauCeti.HopfAlgebra
