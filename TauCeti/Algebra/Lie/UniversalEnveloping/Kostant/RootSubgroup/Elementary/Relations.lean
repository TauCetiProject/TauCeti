/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.UniversalEnveloping.ChevalleyCommutator
public import TauCeti.Algebra.Lie.UniversalEnveloping.Kostant.RootSubgroup.Subsystem

/-!
# Steinberg's Chevalley commutator relations for parametrized Kostant root subgroups

Let `U_ℤ = kostantForm e h` preserve an additive subgroup `M ≤ V` of a rational representation `V`.
Over any `A : CommAlgCat ℤ`, `kostantRootSubgroupParam` gives the root subgroups
`xᵢ : Multiplicative A →* GL(A ⊗[ℤ] M)` generating `kostantElementarySubgroup e h ρ M hM hnil A`.
Together with `commute_kostantRootSubgroupParam` and
`commutatorElement_kostantRootSubgroupParam_of_lie_eq` (`RootSubgroup/Subsystem.lean`), this file
completes Steinberg's element-commutator relations (`⁅g, h⁆ = g * h * g⁻¹ * h⁻¹`) directly for
`kostantRootSubgroupParam` across all seven positive rank-two root-string configurations.

## Main results

* `TauCeti.UniversalEnvelopingAlgebra.commutatorElement_kostantRootSubgroupParam_of_lie_lie_eq`,
  `commutatorElement_kostantRootSubgroupParam_of_lie_lie_rev_eq`,
  `commutatorElement_kostantRootSubgroupParam_of_g2_short_pair`,
  `commutatorElement_kostantRootSubgroupParam_of_lie_eq_three_nsmul`, and
  `commutatorElement_kostantRootSubgroupParam_of_lie_eq_three_nsmul_rev`.

## References

* R. Steinberg, *Lectures on Chevalley Groups*, Chapter 3, Lemma 15.
* R. W. Carter, *Simple Groups of Lie Type*, §4.4 and Theorem 5.2.2.
* J. E. Humphreys, *Introduction to Lie Algebras and Representation Theory*, §§25--27.
* J. C. Jantzen, *Representations of Algebraic Groups*, II.1.
-/

public section

open CategoryTheory TensorProduct
open Multiplicative (ofAdd toAdd)
open _root_.UniversalEnvelopingAlgebra (ι)
open scoped commutatorElement

namespace TauCeti.UniversalEnvelopingAlgebra

universe u v w

variable {L : Type u} [LieRing L] [LieAlgebra ℚ L] {I : Type*} {κ : Type*}
variable {V : Type v} [AddCommGroup V] [Module ℚ V] (e : I → L) (h : κ → L)
variable (ρ : _root_.UniversalEnvelopingAlgebra ℚ L →ₐ[ℚ] Module.End ℚ V) (M : AddSubgroup V)
variable (hM : ∀ u ∈ kostantForm e h, ∀ v ∈ M, ρ u v ∈ M)

attribute [local instance high] Algebra.toModule

/-- **Steinberg's multiply-laced Chevalley commutator relation (`α + β, 2α + β`) for parametrized
Kostant root subgroups.** For indices `i, j, k, l` representing `α, β, α + β, 2α + β` with
`⁅e i, e j⁆ = c • e k`, `⁅e i, ⁅e i, e j⁆⁆ = (2 * d) • e l`, and `⁅e i, e l⁆ = ⁅e j, e k⁆ = 0`,
parameters `t, u` satisfy `⁅xᵢ(t), xⱼ(u)⁆ = xₖ(c t u) xₗ(d t² u)`. -/
theorem commutatorElement_kostantRootSubgroupParam_of_lie_lie_eq {i j k l : I} {c d : ℤ}
    (hij : ⁅e i, e j⁆ = c • e k) (hiij : ⁅e i, ⁅e i, e j⁆⁆ = (2 * d) • e l)
    (hil : ⁅e i, e l⁆ = 0) (hjk : ⁅e j, e k⁆ = 0)
    (hi : IsNilpotent (ρ (ι ℚ (e i)))) (hj : IsNilpotent (ρ (ι ℚ (e j))))
    (hk : IsNilpotent (ρ (ι ℚ (e k)))) (hl : IsNilpotent (ρ (ι ℚ (e l))))
    (A : CommAlgCat.{w} ℤ) (t u : Multiplicative A) :
    ⁅kostantRootSubgroupParam e h ρ M hM i hi A t, kostantRootSubgroupParam e h ρ M hM j hj A u⁆ =
      kostantRootSubgroupParam e h ρ M hM k hk A (ofAdd ((c : A) * (toAdd t * toAdd u))) *
        kostantRootSubgroupParam e h ρ M hM l hl A (ofAdd ((d : A) * (toAdd t ^ 2 * toAdd u))) := by
  refine (LinearMap.GeneralLinearGroup.generalLinearEquiv A (A ⊗[ℤ] M)).injective ?_
  simp only [map_commutatorElement, map_mul, generalLinearEquiv_kostantRootSubgroupParam]
  exact commutatorElement_baseChangeExpHom_of_lie_lie_eq ρ M hij hiij hil hjk
    _ _ _ _ hi hj hk hl t u

/-- **Steinberg's reversed multiply-laced Chevalley commutator relation (`α + β, α + 2β`) for
parametrized Kostant root subgroups.** For `i, j, k, l` representing `α, β, α + β, α + 2β` with
`⁅e i, e j⁆ = c • e k`, `⁅e j, ⁅e j, e i⁆⁆ = (2 * d) • e l`, and `⁅e j, e l⁆ = ⁅e i, e k⁆ = 0`,
parameters `t, u` satisfy `⁅xᵢ(t), xⱼ(u)⁆ = xₖ(c t u) xₗ(-d t u²)`. -/
theorem commutatorElement_kostantRootSubgroupParam_of_lie_lie_rev_eq {i j k l : I} {c d : ℤ}
    (hij : ⁅e i, e j⁆ = c • e k) (hjji : ⁅e j, ⁅e j, e i⁆⁆ = (2 * d) • e l)
    (hjl : ⁅e j, e l⁆ = 0) (hik : ⁅e i, e k⁆ = 0)
    (hi : IsNilpotent (ρ (ι ℚ (e i)))) (hj : IsNilpotent (ρ (ι ℚ (e j))))
    (hk : IsNilpotent (ρ (ι ℚ (e k)))) (hl : IsNilpotent (ρ (ι ℚ (e l))))
    (A : CommAlgCat.{w} ℤ) (t u : Multiplicative A) :
    ⁅kostantRootSubgroupParam e h ρ M hM i hi A t, kostantRootSubgroupParam e h ρ M hM j hj A u⁆ =
      kostantRootSubgroupParam e h ρ M hM k hk A (ofAdd ((c : A) * (toAdd t * toAdd u))) *
        kostantRootSubgroupParam e h ρ M hM l hl A
          (ofAdd ((-d : A) * (toAdd t * toAdd u ^ 2))) := by
  refine (LinearMap.GeneralLinearGroup.generalLinearEquiv A (A ⊗[ℤ] M)).injective ?_
  simp only [map_commutatorElement, map_mul, generalLinearEquiv_kostantRootSubgroupParam]
  exact commutatorElement_baseChangeExpHom_of_lie_lie_rev_eq ρ M hij hjji hjl hik
    _ _ _ _ hi hj hk hl t u

/-- **Steinberg's type-`G₂` short-pair Chevalley commutator relation for parametrized Kostant root
subgroups.** For `i, j, k, l, m` representing two short roots `γ, δ` at angle `2π/3` and
`γ + δ, 2γ + δ, γ + 2δ` with `⁅e i, e j⁆ = (2 * c) • e k`, `c • ⁅e i, e k⁆ = (3 * d) • e l`, and
`c • ⁅e k, e j⁆ = (3 * a) • e m`, `⁅xᵢ(t), xⱼ(u)⁆ = xₖ(2c t u) xₗ(3d t² u) xₘ(-3a t u²)`. -/
theorem commutatorElement_kostantRootSubgroupParam_of_g2_short_pair {i j k l m : I} {c d a : ℤ}
    (hij : ⁅e i, e j⁆ = (2 * c) • e k) (hik : c • ⁅e i, e k⁆ = (3 * d) • e l)
    (hkj : c • ⁅e k, e j⁆ = (3 * a) • e m) (hil : ⁅e i, e l⁆ = 0) (him : ⁅e i, e m⁆ = 0)
    (hjm : ⁅e j, e m⁆ = 0) (hkl : ⁅e k, e l⁆ = 0) (hkm : ⁅e k, e m⁆ = 0) (hlm : ⁅e l, e m⁆ = 0)
    (hi : IsNilpotent (ρ (ι ℚ (e i)))) (hj : IsNilpotent (ρ (ι ℚ (e j))))
    (hk : IsNilpotent (ρ (ι ℚ (e k)))) (hl : IsNilpotent (ρ (ι ℚ (e l))))
    (hm : IsNilpotent (ρ (ι ℚ (e m)))) (A : CommAlgCat.{w} ℤ) (t u : Multiplicative A) :
    ⁅kostantRootSubgroupParam e h ρ M hM i hi A t, kostantRootSubgroupParam e h ρ M hM j hj A u⁆ =
      kostantRootSubgroupParam e h ρ M hM k hk A (ofAdd ((c : A) * (2 * toAdd t * toAdd u))) *
        kostantRootSubgroupParam e h ρ M hM l hl A (ofAdd ((d : A) * (3 * toAdd t ^ 2 * toAdd u))) *
        kostantRootSubgroupParam e h ρ M hM m hm A
          (ofAdd ((-a : A) * (3 * toAdd t * toAdd u ^ 2))) := by
  refine (LinearMap.GeneralLinearGroup.generalLinearEquiv A (A ⊗[ℤ] M)).injective ?_
  simp only [map_commutatorElement, map_mul, generalLinearEquiv_kostantRootSubgroupParam]
  exact commutatorElement_baseChangeExpHom_of_g2_short_pair ρ M hij hik hkj hil him hjm hkl hkm hlm
    _ _ _ _ _ hi hj hk hl hm t u

/-- **Steinberg's type-`G₂` Chevalley commutator relation (`α` short, `β` long) for parametrized
Kostant root subgroups.** For `i, j, k, l, m, o` representing `α, β, α + β, 2α + β, 3α + β, 3α + 2β`
with `⁅e i, e j⁆ = c • e k`, `c • ⁅e i, e k⁆ = (2 * d) • e l`, `d • ⁅e i, e l⁆ = (3 * a) • e m`, and
`(d * c) • ⁅e l, e k⁆ = (3 * b) • e o`,
`⁅xᵢ(t), xⱼ(u)⁆ = xₖ(c t u) xₗ(d t² u) xₘ(a t³ u) xₒ(2b t³ u²)`. -/
theorem commutatorElement_kostantRootSubgroupParam_of_lie_eq_three_nsmul
    {i j k l m o : I} {c d a b : ℤ} (hij : ⁅e i, e j⁆ = c • e k)
    (hik : c • ⁅e i, e k⁆ = (2 * d) • e l) (hil : d • ⁅e i, e l⁆ = (3 * a) • e m)
    (hlk : (d * c) • ⁅e l, e k⁆ = (3 * b) • e o) (him : ⁅e i, e m⁆ = 0) (hio : ⁅e i, e o⁆ = 0)
    (hjk : ⁅e j, e k⁆ = 0) (hlm : ⁅e l, e m⁆ = 0) (hko : ⁅e k, e o⁆ = 0) (hlo : ⁅e l, e o⁆ = 0)
    (hmo : ⁅e m, e o⁆ = 0) (hi : IsNilpotent (ρ (ι ℚ (e i)))) (hj : IsNilpotent (ρ (ι ℚ (e j))))
    (hk : IsNilpotent (ρ (ι ℚ (e k)))) (hl : IsNilpotent (ρ (ι ℚ (e l))))
    (hm : IsNilpotent (ρ (ι ℚ (e m)))) (ho : IsNilpotent (ρ (ι ℚ (e o))))
    (A : CommAlgCat.{w} ℤ) (t u : Multiplicative A) :
    ⁅kostantRootSubgroupParam e h ρ M hM i hi A t, kostantRootSubgroupParam e h ρ M hM j hj A u⁆ =
      kostantRootSubgroupParam e h ρ M hM k hk A (ofAdd ((c : A) * (toAdd t * toAdd u))) *
        kostantRootSubgroupParam e h ρ M hM l hl A (ofAdd ((d : A) * (toAdd t ^ 2 * toAdd u))) *
        kostantRootSubgroupParam e h ρ M hM m hm A (ofAdd ((a : A) * (toAdd t ^ 3 * toAdd u))) *
        kostantRootSubgroupParam e h ρ M hM o ho A
          (ofAdd ((2 * (b : A)) * (toAdd t ^ 3 * toAdd u ^ 2))) := by
  refine (LinearMap.GeneralLinearGroup.generalLinearEquiv A (A ⊗[ℤ] M)).injective ?_
  simp only [map_commutatorElement, map_mul, generalLinearEquiv_kostantRootSubgroupParam]
  exact commutatorElement_baseChangeExpHom_of_lie_eq_three_nsmul ρ M
    hij hik hil hlk him hio hjk hlm hko hlo hmo _ _ _ _ _ _ hi hj hk hl hm ho t u

/-- **Steinberg's type-`G₂` Chevalley commutator relation (`α` long, `β` short) for parametrized
Kostant root subgroups.** For `i, j, k, l, m, o` representing `α, β, α + β, α + 2β, α + 3β, 2α + 3β`
with `⁅e i, e j⁆ = c • e k`, `c • ⁅e k, e j⁆ = (2 * d) • e l`, `d • ⁅e j, e l⁆ = (3 * a) • e m`, and
`(d * c) • ⁅e k, e l⁆ = (3 * b) • e o`,
`⁅xᵢ(t), xⱼ(u)⁆ = xₖ(c t u) xₗ(-d t u²) xₘ(-a t u³) xₒ(b t² u³)`. -/
theorem commutatorElement_kostantRootSubgroupParam_of_lie_eq_three_nsmul_rev
    {i j k l m o : I} {c d a b : ℤ} (hij : ⁅e i, e j⁆ = c • e k)
    (hkj : c • ⁅e k, e j⁆ = (2 * d) • e l) (hjl : d • ⁅e j, e l⁆ = (3 * a) • e m)
    (hkl : (d * c) • ⁅e k, e l⁆ = (3 * b) • e o) (hjm : ⁅e j, e m⁆ = 0) (hjo : ⁅e j, e o⁆ = 0)
    (hik : ⁅e i, e k⁆ = 0) (hlm : ⁅e l, e m⁆ = 0) (hko : ⁅e k, e o⁆ = 0) (hlo : ⁅e l, e o⁆ = 0)
    (hmo : ⁅e m, e o⁆ = 0) (hi : IsNilpotent (ρ (ι ℚ (e i)))) (hj : IsNilpotent (ρ (ι ℚ (e j))))
    (hk : IsNilpotent (ρ (ι ℚ (e k)))) (hl : IsNilpotent (ρ (ι ℚ (e l))))
    (hm : IsNilpotent (ρ (ι ℚ (e m)))) (ho : IsNilpotent (ρ (ι ℚ (e o))))
    (A : CommAlgCat.{w} ℤ) (t u : Multiplicative A) :
    ⁅kostantRootSubgroupParam e h ρ M hM i hi A t, kostantRootSubgroupParam e h ρ M hM j hj A u⁆ =
      kostantRootSubgroupParam e h ρ M hM k hk A (ofAdd ((c : A) * (toAdd t * toAdd u))) *
        kostantRootSubgroupParam e h ρ M hM l hl A (ofAdd ((-d : A) * (toAdd t * toAdd u ^ 2))) *
        kostantRootSubgroupParam e h ρ M hM m hm A (ofAdd ((-a : A) * (toAdd t * toAdd u ^ 3))) *
        kostantRootSubgroupParam e h ρ M hM o ho A
          (ofAdd ((b : A) * (toAdd t ^ 2 * toAdd u ^ 3))) := by
  refine (LinearMap.GeneralLinearGroup.generalLinearEquiv A (A ⊗[ℤ] M)).injective ?_
  simp only [map_commutatorElement, map_mul, generalLinearEquiv_kostantRootSubgroupParam]
  exact commutatorElement_baseChangeExpHom_of_lie_eq_three_nsmul_rev ρ M
    hij hkj hjl hkl hjm hjo hik hlm hko hlo hmo _ _ _ _ _ _ hi hj hk hl hm ho t u

end TauCeti.UniversalEnvelopingAlgebra
