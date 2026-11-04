/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.UniversalEnveloping.Kostant.RootSubgroup.MultiplyLacedRelations

/-!
# Type-G₂ Chevalley element-commutator relations for Kostant root subgroups

Let `U_ℤ = kostantForm e h` act on a rational vector space `V` through `ρ`, and let `M ≤ V` be a
`U_ℤ`-stable additive subgroup. Over any commutative ring `A`, this file derives Steinberg's
canonical element-commutator identities (`⁅g, h⁆ = g * h * g⁻¹ * h⁻¹`) for the three exceptional
positive rank-two root-string configurations of type `G₂`, both on divided-power root-subgroup
actions (`kostantRootSubgroupPoints`) and in any finite integral basis
(`kostantRootSubgroupMatrix`):

* **short pair** (`α, α + β, 2α + β, 3α + β, 3α + 2β` with `[eᵢ, eⱼ] = 2c eₖ`,
  `c [eᵢ, eₖ] = 3d eₗ`, `c [eₖ, eⱼ] = 3a eₘ`):
  ```text
  ⁅xᵢ(t), xⱼ(u)⁆ = xₖ(2c t u) xₗ(3d t² u) xₘ(-3a t u²);
  ```
* **short--long simple pair** (`α, β, α + β, 2α + β, 3α + β, 3α + 2β` with `[eᵢ, eⱼ] = c eₖ`,
  `c [eᵢ, eₖ] = 2d eₗ`, `d [eᵢ, eₗ] = 3a eₘ`, `d c [eₗ, eₖ] = 3b eₒ`):
  ```text
  ⁅xᵢ(t), xⱼ(u)⁆ = xₖ(c t u) xₗ(d t² u) xₘ(a t³ u) xₒ(2b t³ u²);
  ```
* **long--short simple pair** (`α, β, α + β, α + 2β, α + 3β, 2α + 3β` with `[eᵢ, eⱼ] = c eₖ`,
  `c [eₖ, eⱼ] = 2d eₗ`, `d [eⱼ, eₗ] = 3a eₘ`, `d c [eₖ, eₗ] = 3b eₒ`):
  ```text
  ⁅xᵢ(t), xⱼ(u)⁆ = xₖ(c t u) xₗ(-d t u²) xₘ(-a t u³) xₒ(b t² u³).
  ```

No integer is inverted in the value ring `A`, so all three relations hold uniformly over `ℤ` and in
characteristics `2` and `3`.

## Main results

* `TauCeti.UniversalEnvelopingAlgebra.
  commutatorElement_kostantRootSubgroupPoints_of_g2_short_pair`,
  `commutatorElement_kostantRootSubgroupPoints_of_lie_eq_three_nsmul`, and
  `commutatorElement_kostantRootSubgroupPoints_of_lie_eq_three_nsmul_rev`: Steinberg's three
  type-`G₂` commutator relations on Kostant root-subgroup points (together with primed explicit
  forms).
* `TauCeti.UniversalEnvelopingAlgebra.
  commutatorElement_kostantRootSubgroupMatrix_of_g2_short_pair`,
  `commutatorElement_kostantRootSubgroupMatrix_of_lie_eq_three_nsmul`, and
  `commutatorElement_kostantRootSubgroupMatrix_of_lie_eq_three_nsmul_rev`: the corresponding matrix
  relations in an arbitrary finite integral basis.

## References

* R. Steinberg, *Lectures on Chevalley Groups*, Chapter 3, Lemma 15.
* R. W. Carter, *Simple Groups of Lie Type*, §4.2 and Theorem 5.2.2.
* J. E. Humphreys, *Introduction to Lie Algebras and Representation Theory*, §§25--27.
* J. C. Jantzen, *Representations of Algebraic Groups*, II.1.
-/

public section

open TensorProduct WithConv
open scoped commutatorElement

namespace TauCeti.UniversalEnvelopingAlgebra

universe u v w

variable {L : Type u} [LieRing L] [LieAlgebra ℚ L]
variable {I : Type w} {κ : Type*}
variable {V : Type v} [AddCommGroup V] [Module ℚ V]

variable (e : I → L) (h : κ → L)
variable (ρ : _root_.UniversalEnvelopingAlgebra ℚ L →ₐ[ℚ] Module.End ℚ V)
variable (M : AddSubgroup V)
variable (hM : ∀ u ∈ kostantForm e h, ∀ v ∈ M, ρ u v ∈ M)

attribute [local instance high] Algebra.toModule

section Points

variable {A : Type*} [CommRing A] [Algebra ℤ A]

/-- **Steinberg's type-`G₂` short-pair Chevalley commutator relation for Kostant root subgroups.**
For indices `i, j, k, l, m` corresponding to `α, α + β, 2α + β, 3α + β, 3α + 2β`, the element
commutator `⁅xᵢ(f), xⱼ(g)⁆` equals `xₖ(p) xₗ(q) xₘ(r)` at parameters `2c t u`, `3d t² u`, and
`-3a t u²`. -/
theorem commutatorElement_kostantRootSubgroupPoints_of_g2_short_pair
    {i j k l m : I} {c d a : ℤ}
    (hij : ⁅e i, e j⁆ = (2 * c) • e k)
    (hik : c • ⁅e i, e k⁆ = (3 * d) • e l)
    (hkj : c • ⁅e k, e j⁆ = (3 * a) • e m)
    (hil : ⁅e i, e l⁆ = 0) (him : ⁅e i, e m⁆ = 0) (hjm : ⁅e j, e m⁆ = 0)
    (hkl : ⁅e k, e l⁆ = 0) (hkm : ⁅e k, e m⁆ = 0) (hlm : ⁅e l, e m⁆ = 0)
    (hi : IsNilpotent (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ (e i))))
    (hj : IsNilpotent (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ (e j))))
    (hk : IsNilpotent (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ (e k))))
    (hl : IsNilpotent (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ (e l))))
    (hm : IsNilpotent (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ (e m))))
    (f g p q r : WithConv (SymmetricAlgebra ℤ ℤ →ₐ[ℤ] A))
    (hp : Multiplicative.toAdd (AdditiveGroup.gaPointsMulEquiv (R := ℤ) (A := A) p) =
      (c : A) * (2 * Multiplicative.toAdd (AdditiveGroup.gaPointsMulEquiv (R := ℤ) (A := A) f) *
        Multiplicative.toAdd (AdditiveGroup.gaPointsMulEquiv (R := ℤ) (A := A) g)))
    (hq : Multiplicative.toAdd (AdditiveGroup.gaPointsMulEquiv (R := ℤ) (A := A) q) =
      (d : A) * (3 * Multiplicative.toAdd (AdditiveGroup.gaPointsMulEquiv (R := ℤ) (A := A) f) ^ 2 *
        Multiplicative.toAdd (AdditiveGroup.gaPointsMulEquiv (R := ℤ) (A := A) g)))
    (hr : Multiplicative.toAdd (AdditiveGroup.gaPointsMulEquiv (R := ℤ) (A := A) r) =
      (-a : A) * (3 * Multiplicative.toAdd (AdditiveGroup.gaPointsMulEquiv (R := ℤ) (A := A) f) *
        Multiplicative.toAdd (AdditiveGroup.gaPointsMulEquiv (R := ℤ) (A := A) g) ^ 2)) :
    ⁅kostantRootSubgroupPoints e h ρ M hM i hi f,
        kostantRootSubgroupPoints e h ρ M hM j hj g⁆ =
      kostantRootSubgroupPoints e h ρ M hM k hk p *
        kostantRootSubgroupPoints e h ρ M hM l hl q *
        kostantRootSubgroupPoints e h ρ M hM m hm r := by
  refine (LinearMap.GeneralLinearGroup.generalLinearEquiv A (A ⊗[ℤ] M)).injective ?_
  simp only [map_commutatorElement, map_mul, generalLinearEquiv_kostantRootSubgroupPoints]
  rw [← ofAdd_toAdd (AdditiveGroup.gaPointsMulEquiv p), hp,
    ← ofAdd_toAdd (AdditiveGroup.gaPointsMulEquiv q), hq,
    ← ofAdd_toAdd (AdditiveGroup.gaPointsMulEquiv r), hr]
  exact commutatorElement_baseChangeExpHom_of_g2_short_pair ρ M
    hij hik hkj hil him hjm hkl hkm hlm
    (fun n _ hv => dividedPower_apply_mem_of_kostantForm_apply_mem e h ρ hM i n hv)
    (fun n _ hv => dividedPower_apply_mem_of_kostantForm_apply_mem e h ρ hM j n hv)
    (fun n _ hv => dividedPower_apply_mem_of_kostantForm_apply_mem e h ρ hM k n hv)
    (fun n _ hv => dividedPower_apply_mem_of_kostantForm_apply_mem e h ρ hM l n hv)
    (fun n _ hv => dividedPower_apply_mem_of_kostantForm_apply_mem e h ρ hM m n hv)
    hi hj hk hl hm _ _

/-- Explicit-parameter form of
`commutatorElement_kostantRootSubgroupPoints_of_g2_short_pair`. -/
theorem commutatorElement_kostantRootSubgroupPoints_of_g2_short_pair'
    {i j k l m : I} {c d a : ℤ}
    (hij : ⁅e i, e j⁆ = (2 * c) • e k)
    (hik : c • ⁅e i, e k⁆ = (3 * d) • e l)
    (hkj : c • ⁅e k, e j⁆ = (3 * a) • e m)
    (hil : ⁅e i, e l⁆ = 0) (him : ⁅e i, e m⁆ = 0) (hjm : ⁅e j, e m⁆ = 0)
    (hkl : ⁅e k, e l⁆ = 0) (hkm : ⁅e k, e m⁆ = 0) (hlm : ⁅e l, e m⁆ = 0)
    (hi : IsNilpotent (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ (e i))))
    (hj : IsNilpotent (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ (e j))))
    (hk : IsNilpotent (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ (e k))))
    (hl : IsNilpotent (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ (e l))))
    (hm : IsNilpotent (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ (e m))))
    (f g : WithConv (SymmetricAlgebra ℤ ℤ →ₐ[ℤ] A)) :
    ⁅kostantRootSubgroupPoints e h ρ M hM i hi f,
        kostantRootSubgroupPoints e h ρ M hM j hj g⁆ =
      kostantRootSubgroupPoints e h ρ M hM k hk
          ((AdditiveGroup.gaPointsMulEquiv (R := ℤ) (A := A)).symm
            (Multiplicative.ofAdd ((c : A) *
              (2 * Multiplicative.toAdd (AdditiveGroup.gaPointsMulEquiv (R := ℤ) (A := A) f) *
                Multiplicative.toAdd (AdditiveGroup.gaPointsMulEquiv (R := ℤ) (A := A) g))))) *
        kostantRootSubgroupPoints e h ρ M hM l hl
          ((AdditiveGroup.gaPointsMulEquiv (R := ℤ) (A := A)).symm
            (Multiplicative.ofAdd ((d : A) *
              (3 * Multiplicative.toAdd (AdditiveGroup.gaPointsMulEquiv (R := ℤ) (A := A) f) ^ 2 *
                Multiplicative.toAdd (AdditiveGroup.gaPointsMulEquiv (R := ℤ) (A := A) g))))) *
        kostantRootSubgroupPoints e h ρ M hM m hm
          ((AdditiveGroup.gaPointsMulEquiv (R := ℤ) (A := A)).symm
            (Multiplicative.ofAdd ((-a : A) *
              (3 * Multiplicative.toAdd (AdditiveGroup.gaPointsMulEquiv (R := ℤ) (A := A) f) *
                Multiplicative.toAdd
                  (AdditiveGroup.gaPointsMulEquiv (R := ℤ) (A := A) g) ^ 2)))) :=
  commutatorElement_kostantRootSubgroupPoints_of_g2_short_pair e h ρ M hM
    hij hik hkj hil him hjm hkl hkm hlm hi hj hk hl hm f g _ _ _
      (congrArg Multiplicative.toAdd
        ((AdditiveGroup.gaPointsMulEquiv (R := ℤ) (A := A)).apply_symm_apply _))
      (congrArg Multiplicative.toAdd
        ((AdditiveGroup.gaPointsMulEquiv (R := ℤ) (A := A)).apply_symm_apply _))
      (congrArg Multiplicative.toAdd
        ((AdditiveGroup.gaPointsMulEquiv (R := ℤ) (A := A)).apply_symm_apply _))

/-- **Steinberg's type-`G₂` Chevalley commutator relation (`α` short, `β` long) for Kostant root
subgroups.** Under the scaled and vanishing bracket hypotheses of the product straightening rule,
`⁅xᵢ(f), xⱼ(g)⁆ = xₖ(p) xₗ(q) xₘ(r) xₒ(s)` at parameters `c t u`, `d t² u`, `a t³ u`, and
`2b t³ u²`. -/
theorem commutatorElement_kostantRootSubgroupPoints_of_lie_eq_three_nsmul
    {i j k l m o : I} {c d a b : ℤ}
    (hij : ⁅e i, e j⁆ = c • e k)
    (hik : c • ⁅e i, e k⁆ = (2 * d) • e l)
    (hil : d • ⁅e i, e l⁆ = (3 * a) • e m)
    (hlk : (d * c) • ⁅e l, e k⁆ = (3 * b) • e o)
    (him : ⁅e i, e m⁆ = 0) (hio : ⁅e i, e o⁆ = 0) (hjk : ⁅e j, e k⁆ = 0)
    (hlm : ⁅e l, e m⁆ = 0) (hko : ⁅e k, e o⁆ = 0) (hlo : ⁅e l, e o⁆ = 0)
    (hmo : ⁅e m, e o⁆ = 0)
    (hi : IsNilpotent (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ (e i))))
    (hj : IsNilpotent (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ (e j))))
    (hk : IsNilpotent (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ (e k))))
    (hl : IsNilpotent (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ (e l))))
    (hm : IsNilpotent (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ (e m))))
    (ho : IsNilpotent (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ (e o))))
    (f g p q r s : WithConv (SymmetricAlgebra ℤ ℤ →ₐ[ℤ] A))
    (hp : Multiplicative.toAdd (AdditiveGroup.gaPointsMulEquiv (R := ℤ) (A := A) p) =
      (c : A) * (Multiplicative.toAdd (AdditiveGroup.gaPointsMulEquiv (R := ℤ) (A := A) f) *
        Multiplicative.toAdd (AdditiveGroup.gaPointsMulEquiv (R := ℤ) (A := A) g)))
    (hq : Multiplicative.toAdd (AdditiveGroup.gaPointsMulEquiv (R := ℤ) (A := A) q) =
      (d : A) * (Multiplicative.toAdd (AdditiveGroup.gaPointsMulEquiv (R := ℤ) (A := A) f) ^ 2 *
        Multiplicative.toAdd (AdditiveGroup.gaPointsMulEquiv (R := ℤ) (A := A) g)))
    (hr : Multiplicative.toAdd (AdditiveGroup.gaPointsMulEquiv (R := ℤ) (A := A) r) =
      (a : A) * (Multiplicative.toAdd (AdditiveGroup.gaPointsMulEquiv (R := ℤ) (A := A) f) ^ 3 *
        Multiplicative.toAdd (AdditiveGroup.gaPointsMulEquiv (R := ℤ) (A := A) g)))
    (hs : Multiplicative.toAdd (AdditiveGroup.gaPointsMulEquiv (R := ℤ) (A := A) s) =
      (2 * (b : A)) *
        (Multiplicative.toAdd (AdditiveGroup.gaPointsMulEquiv (R := ℤ) (A := A) f) ^ 3 *
          Multiplicative.toAdd (AdditiveGroup.gaPointsMulEquiv (R := ℤ) (A := A) g) ^ 2)) :
    ⁅kostantRootSubgroupPoints e h ρ M hM i hi f,
        kostantRootSubgroupPoints e h ρ M hM j hj g⁆ =
      kostantRootSubgroupPoints e h ρ M hM k hk p *
        kostantRootSubgroupPoints e h ρ M hM l hl q *
        kostantRootSubgroupPoints e h ρ M hM m hm r *
        kostantRootSubgroupPoints e h ρ M hM o ho s := by
  refine (LinearMap.GeneralLinearGroup.generalLinearEquiv A (A ⊗[ℤ] M)).injective ?_
  simp only [map_commutatorElement, map_mul, generalLinearEquiv_kostantRootSubgroupPoints]
  have hs' :
      AdditiveGroup.gaPointsMulEquiv (R := ℤ) (A := A) s =
        Multiplicative.ofAdd (((2 * b : ℤ) : A) *
          (Multiplicative.toAdd (AdditiveGroup.gaPointsMulEquiv (R := ℤ) (A := A) f) ^ 3 *
            Multiplicative.toAdd (AdditiveGroup.gaPointsMulEquiv (R := ℤ) (A := A) g) ^ 2)) := by
    rw [← ofAdd_toAdd (AdditiveGroup.gaPointsMulEquiv s), hs]
    exact congrArg Multiplicative.ofAdd (by push_cast; ring)
  rw [← ofAdd_toAdd (AdditiveGroup.gaPointsMulEquiv p), hp,
    ← ofAdd_toAdd (AdditiveGroup.gaPointsMulEquiv q), hq,
    ← ofAdd_toAdd (AdditiveGroup.gaPointsMulEquiv r), hr, hs']
  exact commutatorElement_baseChangeExpHom_of_lie_eq_three_nsmul ρ M
    hij hik hil hlk him hio hjk hlm hko hlo hmo
    (fun n _ hv => dividedPower_apply_mem_of_kostantForm_apply_mem e h ρ hM i n hv)
    (fun n _ hv => dividedPower_apply_mem_of_kostantForm_apply_mem e h ρ hM j n hv)
    (fun n _ hv => dividedPower_apply_mem_of_kostantForm_apply_mem e h ρ hM k n hv)
    (fun n _ hv => dividedPower_apply_mem_of_kostantForm_apply_mem e h ρ hM l n hv)
    (fun n _ hv => dividedPower_apply_mem_of_kostantForm_apply_mem e h ρ hM m n hv)
    (fun n _ hv => dividedPower_apply_mem_of_kostantForm_apply_mem e h ρ hM o n hv)
    hi hj hk hl hm ho _ _

/-- Explicit-parameter form of
`commutatorElement_kostantRootSubgroupPoints_of_lie_eq_three_nsmul`. -/
theorem commutatorElement_kostantRootSubgroupPoints_of_lie_eq_three_nsmul'
    {i j k l m o : I} {c d a b : ℤ}
    (hij : ⁅e i, e j⁆ = c • e k)
    (hik : c • ⁅e i, e k⁆ = (2 * d) • e l)
    (hil : d • ⁅e i, e l⁆ = (3 * a) • e m)
    (hlk : (d * c) • ⁅e l, e k⁆ = (3 * b) • e o)
    (him : ⁅e i, e m⁆ = 0) (hio : ⁅e i, e o⁆ = 0) (hjk : ⁅e j, e k⁆ = 0)
    (hlm : ⁅e l, e m⁆ = 0) (hko : ⁅e k, e o⁆ = 0) (hlo : ⁅e l, e o⁆ = 0)
    (hmo : ⁅e m, e o⁆ = 0)
    (hi : IsNilpotent (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ (e i))))
    (hj : IsNilpotent (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ (e j))))
    (hk : IsNilpotent (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ (e k))))
    (hl : IsNilpotent (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ (e l))))
    (hm : IsNilpotent (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ (e m))))
    (ho : IsNilpotent (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ (e o))))
    (f g : WithConv (SymmetricAlgebra ℤ ℤ →ₐ[ℤ] A)) :
    ⁅kostantRootSubgroupPoints e h ρ M hM i hi f,
        kostantRootSubgroupPoints e h ρ M hM j hj g⁆ =
      kostantRootSubgroupPoints e h ρ M hM k hk
          ((AdditiveGroup.gaPointsMulEquiv (R := ℤ) (A := A)).symm
            (Multiplicative.ofAdd ((c : A) *
              (Multiplicative.toAdd (AdditiveGroup.gaPointsMulEquiv (R := ℤ) (A := A) f) *
                Multiplicative.toAdd (AdditiveGroup.gaPointsMulEquiv (R := ℤ) (A := A) g))))) *
        kostantRootSubgroupPoints e h ρ M hM l hl
          ((AdditiveGroup.gaPointsMulEquiv (R := ℤ) (A := A)).symm
            (Multiplicative.ofAdd ((d : A) *
              (Multiplicative.toAdd (AdditiveGroup.gaPointsMulEquiv (R := ℤ) (A := A) f) ^ 2 *
                Multiplicative.toAdd (AdditiveGroup.gaPointsMulEquiv (R := ℤ) (A := A) g))))) *
        kostantRootSubgroupPoints e h ρ M hM m hm
          ((AdditiveGroup.gaPointsMulEquiv (R := ℤ) (A := A)).symm
            (Multiplicative.ofAdd ((a : A) *
              (Multiplicative.toAdd (AdditiveGroup.gaPointsMulEquiv (R := ℤ) (A := A) f) ^ 3 *
                Multiplicative.toAdd (AdditiveGroup.gaPointsMulEquiv (R := ℤ) (A := A) g))))) *
        kostantRootSubgroupPoints e h ρ M hM o ho
          ((AdditiveGroup.gaPointsMulEquiv (R := ℤ) (A := A)).symm
            (Multiplicative.ofAdd ((2 * (b : A)) *
              (Multiplicative.toAdd (AdditiveGroup.gaPointsMulEquiv (R := ℤ) (A := A) f) ^ 3 *
                Multiplicative.toAdd
                  (AdditiveGroup.gaPointsMulEquiv (R := ℤ) (A := A) g) ^ 2)))) :=
  commutatorElement_kostantRootSubgroupPoints_of_lie_eq_three_nsmul e h ρ M hM
    hij hik hil hlk him hio hjk hlm hko hlo hmo hi hj hk hl hm ho f g _ _ _ _
      (congrArg Multiplicative.toAdd
        ((AdditiveGroup.gaPointsMulEquiv (R := ℤ) (A := A)).apply_symm_apply _))
      (congrArg Multiplicative.toAdd
        ((AdditiveGroup.gaPointsMulEquiv (R := ℤ) (A := A)).apply_symm_apply _))
      (congrArg Multiplicative.toAdd
        ((AdditiveGroup.gaPointsMulEquiv (R := ℤ) (A := A)).apply_symm_apply _))
      (congrArg Multiplicative.toAdd
        ((AdditiveGroup.gaPointsMulEquiv (R := ℤ) (A := A)).apply_symm_apply _))

/-- **Steinberg's type-`G₂` Chevalley commutator relation (`α` long, `β` short) for Kostant root
subgroups.** For indices `i, j, k, l, m, o` corresponding to
`α, β, α + β, α + 2β, α + 3β, 2α + 3β`, the element commutator is
`⁅xᵢ(f), xⱼ(g)⁆ = xₖ(p) xₗ(q) xₘ(r) xₒ(s)` at parameters `c t u`, `-d t u²`, `-a t u³`, and
`b t² u³`. -/
theorem commutatorElement_kostantRootSubgroupPoints_of_lie_eq_three_nsmul_rev
    {i j k l m o : I} {c d a b : ℤ}
    (hij : ⁅e i, e j⁆ = c • e k)
    (hkj : c • ⁅e k, e j⁆ = (2 * d) • e l)
    (hjl : d • ⁅e j, e l⁆ = (3 * a) • e m)
    (hkl : (d * c) • ⁅e k, e l⁆ = (3 * b) • e o)
    (hjm : ⁅e j, e m⁆ = 0) (hjo : ⁅e j, e o⁆ = 0) (hik : ⁅e i, e k⁆ = 0)
    (hlm : ⁅e l, e m⁆ = 0) (hko : ⁅e k, e o⁆ = 0) (hlo : ⁅e l, e o⁆ = 0)
    (hmo : ⁅e m, e o⁆ = 0)
    (hi : IsNilpotent (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ (e i))))
    (hj : IsNilpotent (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ (e j))))
    (hk : IsNilpotent (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ (e k))))
    (hl : IsNilpotent (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ (e l))))
    (hm : IsNilpotent (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ (e m))))
    (ho : IsNilpotent (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ (e o))))
    (f g p q r s : WithConv (SymmetricAlgebra ℤ ℤ →ₐ[ℤ] A))
    (hp : Multiplicative.toAdd (AdditiveGroup.gaPointsMulEquiv (R := ℤ) (A := A) p) =
      (c : A) * (Multiplicative.toAdd (AdditiveGroup.gaPointsMulEquiv (R := ℤ) (A := A) f) *
        Multiplicative.toAdd (AdditiveGroup.gaPointsMulEquiv (R := ℤ) (A := A) g)))
    (hq : Multiplicative.toAdd (AdditiveGroup.gaPointsMulEquiv (R := ℤ) (A := A) q) =
      (-d : A) * (Multiplicative.toAdd (AdditiveGroup.gaPointsMulEquiv (R := ℤ) (A := A) f) *
        Multiplicative.toAdd (AdditiveGroup.gaPointsMulEquiv (R := ℤ) (A := A) g) ^ 2))
    (hr : Multiplicative.toAdd (AdditiveGroup.gaPointsMulEquiv (R := ℤ) (A := A) r) =
      (-a : A) * (Multiplicative.toAdd (AdditiveGroup.gaPointsMulEquiv (R := ℤ) (A := A) f) *
        Multiplicative.toAdd (AdditiveGroup.gaPointsMulEquiv (R := ℤ) (A := A) g) ^ 3))
    (hs : Multiplicative.toAdd (AdditiveGroup.gaPointsMulEquiv (R := ℤ) (A := A) s) =
      (b : A) * (Multiplicative.toAdd (AdditiveGroup.gaPointsMulEquiv (R := ℤ) (A := A) f) ^ 2 *
        Multiplicative.toAdd (AdditiveGroup.gaPointsMulEquiv (R := ℤ) (A := A) g) ^ 3)) :
    ⁅kostantRootSubgroupPoints e h ρ M hM i hi f,
        kostantRootSubgroupPoints e h ρ M hM j hj g⁆ =
      kostantRootSubgroupPoints e h ρ M hM k hk p *
        kostantRootSubgroupPoints e h ρ M hM l hl q *
        kostantRootSubgroupPoints e h ρ M hM m hm r *
        kostantRootSubgroupPoints e h ρ M hM o ho s := by
  refine (LinearMap.GeneralLinearGroup.generalLinearEquiv A (A ⊗[ℤ] M)).injective ?_
  simp only [map_commutatorElement, map_mul, generalLinearEquiv_kostantRootSubgroupPoints]
  rw [← ofAdd_toAdd (AdditiveGroup.gaPointsMulEquiv p), hp,
    ← ofAdd_toAdd (AdditiveGroup.gaPointsMulEquiv q), hq,
    ← ofAdd_toAdd (AdditiveGroup.gaPointsMulEquiv r), hr,
    ← ofAdd_toAdd (AdditiveGroup.gaPointsMulEquiv s), hs]
  exact commutatorElement_baseChangeExpHom_of_lie_eq_three_nsmul_rev ρ M
    hij hkj hjl hkl hjm hjo hik hlm hko hlo hmo
    (fun n _ hv => dividedPower_apply_mem_of_kostantForm_apply_mem e h ρ hM i n hv)
    (fun n _ hv => dividedPower_apply_mem_of_kostantForm_apply_mem e h ρ hM j n hv)
    (fun n _ hv => dividedPower_apply_mem_of_kostantForm_apply_mem e h ρ hM k n hv)
    (fun n _ hv => dividedPower_apply_mem_of_kostantForm_apply_mem e h ρ hM l n hv)
    (fun n _ hv => dividedPower_apply_mem_of_kostantForm_apply_mem e h ρ hM m n hv)
    (fun n _ hv => dividedPower_apply_mem_of_kostantForm_apply_mem e h ρ hM o n hv)
    hi hj hk hl hm ho _ _

/-- Explicit-parameter form of
`commutatorElement_kostantRootSubgroupPoints_of_lie_eq_three_nsmul_rev`. -/
theorem commutatorElement_kostantRootSubgroupPoints_of_lie_eq_three_nsmul_rev'
    {i j k l m o : I} {c d a b : ℤ}
    (hij : ⁅e i, e j⁆ = c • e k)
    (hkj : c • ⁅e k, e j⁆ = (2 * d) • e l)
    (hjl : d • ⁅e j, e l⁆ = (3 * a) • e m)
    (hkl : (d * c) • ⁅e k, e l⁆ = (3 * b) • e o)
    (hjm : ⁅e j, e m⁆ = 0) (hjo : ⁅e j, e o⁆ = 0) (hik : ⁅e i, e k⁆ = 0)
    (hlm : ⁅e l, e m⁆ = 0) (hko : ⁅e k, e o⁆ = 0) (hlo : ⁅e l, e o⁆ = 0)
    (hmo : ⁅e m, e o⁆ = 0)
    (hi : IsNilpotent (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ (e i))))
    (hj : IsNilpotent (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ (e j))))
    (hk : IsNilpotent (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ (e k))))
    (hl : IsNilpotent (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ (e l))))
    (hm : IsNilpotent (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ (e m))))
    (ho : IsNilpotent (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ (e o))))
    (f g : WithConv (SymmetricAlgebra ℤ ℤ →ₐ[ℤ] A)) :
    ⁅kostantRootSubgroupPoints e h ρ M hM i hi f,
        kostantRootSubgroupPoints e h ρ M hM j hj g⁆ =
      kostantRootSubgroupPoints e h ρ M hM k hk
          ((AdditiveGroup.gaPointsMulEquiv (R := ℤ) (A := A)).symm
            (Multiplicative.ofAdd ((c : A) *
              (Multiplicative.toAdd (AdditiveGroup.gaPointsMulEquiv (R := ℤ) (A := A) f) *
                Multiplicative.toAdd (AdditiveGroup.gaPointsMulEquiv (R := ℤ) (A := A) g))))) *
        kostantRootSubgroupPoints e h ρ M hM l hl
          ((AdditiveGroup.gaPointsMulEquiv (R := ℤ) (A := A)).symm
            (Multiplicative.ofAdd ((-d : A) *
              (Multiplicative.toAdd (AdditiveGroup.gaPointsMulEquiv (R := ℤ) (A := A) f) *
                Multiplicative.toAdd (AdditiveGroup.gaPointsMulEquiv (R := ℤ) (A := A) g) ^ 2)))) *
        kostantRootSubgroupPoints e h ρ M hM m hm
          ((AdditiveGroup.gaPointsMulEquiv (R := ℤ) (A := A)).symm
            (Multiplicative.ofAdd ((-a : A) *
              (Multiplicative.toAdd (AdditiveGroup.gaPointsMulEquiv (R := ℤ) (A := A) f) *
                Multiplicative.toAdd (AdditiveGroup.gaPointsMulEquiv (R := ℤ) (A := A) g) ^ 3)))) *
        kostantRootSubgroupPoints e h ρ M hM o ho
          ((AdditiveGroup.gaPointsMulEquiv (R := ℤ) (A := A)).symm
            (Multiplicative.ofAdd ((b : A) *
              (Multiplicative.toAdd (AdditiveGroup.gaPointsMulEquiv (R := ℤ) (A := A) f) ^ 2 *
                Multiplicative.toAdd
                  (AdditiveGroup.gaPointsMulEquiv (R := ℤ) (A := A) g) ^ 3)))) :=
  commutatorElement_kostantRootSubgroupPoints_of_lie_eq_three_nsmul_rev e h ρ M hM
    hij hkj hjl hkl hjm hjo hik hlm hko hlo hmo hi hj hk hl hm ho f g _ _ _ _
      (congrArg Multiplicative.toAdd
        ((AdditiveGroup.gaPointsMulEquiv (R := ℤ) (A := A)).apply_symm_apply _))
      (congrArg Multiplicative.toAdd
        ((AdditiveGroup.gaPointsMulEquiv (R := ℤ) (A := A)).apply_symm_apply _))
      (congrArg Multiplicative.toAdd
        ((AdditiveGroup.gaPointsMulEquiv (R := ℤ) (A := A)).apply_symm_apply _))
      (congrArg Multiplicative.toAdd
        ((AdditiveGroup.gaPointsMulEquiv (R := ℤ) (A := A)).apply_symm_apply _))

end Points

section Matrices

variable {A : Type*} [CommRing A]
variable {η : Type*} [Fintype η] [DecidableEq η] (ℬ : Module.Basis η ℤ M)

/-- **Steinberg's type-`G₂` short-pair Chevalley commutator relation in an integral basis.** -/
theorem commutatorElement_kostantRootSubgroupMatrix_of_g2_short_pair
    {i j k l m : I} {c d a : ℤ}
    (hij : ⁅e i, e j⁆ = (2 * c) • e k)
    (hik : c • ⁅e i, e k⁆ = (3 * d) • e l)
    (hkj : c • ⁅e k, e j⁆ = (3 * a) • e m)
    (hil : ⁅e i, e l⁆ = 0) (him : ⁅e i, e m⁆ = 0) (hjm : ⁅e j, e m⁆ = 0)
    (hkl : ⁅e k, e l⁆ = 0) (hkm : ⁅e k, e m⁆ = 0) (hlm : ⁅e l, e m⁆ = 0)
    (hi : IsNilpotent (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ (e i))))
    (hj : IsNilpotent (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ (e j))))
    (hk : IsNilpotent (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ (e k))))
    (hl : IsNilpotent (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ (e l))))
    (hm : IsNilpotent (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ (e m))))
    (f g p q r : WithConv (SymmetricAlgebra ℤ ℤ →ₐ[ℤ] A))
    (hp : Multiplicative.toAdd (AdditiveGroup.gaPointsMulEquiv (R := ℤ) (A := A) p) =
      (c : A) * (2 * Multiplicative.toAdd (AdditiveGroup.gaPointsMulEquiv (R := ℤ) (A := A) f) *
        Multiplicative.toAdd (AdditiveGroup.gaPointsMulEquiv (R := ℤ) (A := A) g)))
    (hq : Multiplicative.toAdd (AdditiveGroup.gaPointsMulEquiv (R := ℤ) (A := A) q) =
      (d : A) * (3 * Multiplicative.toAdd (AdditiveGroup.gaPointsMulEquiv (R := ℤ) (A := A) f) ^ 2 *
        Multiplicative.toAdd (AdditiveGroup.gaPointsMulEquiv (R := ℤ) (A := A) g)))
    (hr : Multiplicative.toAdd (AdditiveGroup.gaPointsMulEquiv (R := ℤ) (A := A) r) =
      (-a : A) * (3 * Multiplicative.toAdd (AdditiveGroup.gaPointsMulEquiv (R := ℤ) (A := A) f) *
        Multiplicative.toAdd (AdditiveGroup.gaPointsMulEquiv (R := ℤ) (A := A) g) ^ 2)) :
    ⁅kostantRootSubgroupMatrix e h ρ M hM i hi ℬ f,
        kostantRootSubgroupMatrix e h ρ M hM j hj ℬ g⁆ =
      kostantRootSubgroupMatrix e h ρ M hM k hk ℬ p *
        kostantRootSubgroupMatrix e h ρ M hM l hl ℬ q *
        kostantRootSubgroupMatrix e h ρ M hM m hm ℬ r := by
  repeat rw [kostantRootSubgroupMatrix_def]
  simpa only [MonoidHom.comp_apply, map_commutatorElement, map_mul] using
    congrArg (Units.map (LinearMap.toMatrixAlgEquiv (ℬ.baseChange A)).toMonoidHom)
      (commutatorElement_kostantRootSubgroupPoints_of_g2_short_pair e h ρ M hM
        hij hik hkj hil him hjm hkl hkm hlm hi hj hk hl hm f g p q r hp hq hr)

/-- Explicit-parameter form of
`commutatorElement_kostantRootSubgroupMatrix_of_g2_short_pair`. -/
theorem commutatorElement_kostantRootSubgroupMatrix_of_g2_short_pair'
    {i j k l m : I} {c d a : ℤ}
    (hij : ⁅e i, e j⁆ = (2 * c) • e k)
    (hik : c • ⁅e i, e k⁆ = (3 * d) • e l)
    (hkj : c • ⁅e k, e j⁆ = (3 * a) • e m)
    (hil : ⁅e i, e l⁆ = 0) (him : ⁅e i, e m⁆ = 0) (hjm : ⁅e j, e m⁆ = 0)
    (hkl : ⁅e k, e l⁆ = 0) (hkm : ⁅e k, e m⁆ = 0) (hlm : ⁅e l, e m⁆ = 0)
    (hi : IsNilpotent (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ (e i))))
    (hj : IsNilpotent (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ (e j))))
    (hk : IsNilpotent (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ (e k))))
    (hl : IsNilpotent (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ (e l))))
    (hm : IsNilpotent (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ (e m))))
    (f g : WithConv (SymmetricAlgebra ℤ ℤ →ₐ[ℤ] A)) :
    ⁅kostantRootSubgroupMatrix e h ρ M hM i hi ℬ f,
        kostantRootSubgroupMatrix e h ρ M hM j hj ℬ g⁆ =
      kostantRootSubgroupMatrix e h ρ M hM k hk ℬ
          ((AdditiveGroup.gaPointsMulEquiv (R := ℤ) (A := A)).symm
            (Multiplicative.ofAdd ((c : A) *
              (2 * Multiplicative.toAdd (AdditiveGroup.gaPointsMulEquiv (R := ℤ) (A := A) f) *
                Multiplicative.toAdd (AdditiveGroup.gaPointsMulEquiv (R := ℤ) (A := A) g))))) *
        kostantRootSubgroupMatrix e h ρ M hM l hl ℬ
          ((AdditiveGroup.gaPointsMulEquiv (R := ℤ) (A := A)).symm
            (Multiplicative.ofAdd ((d : A) *
              (3 * Multiplicative.toAdd (AdditiveGroup.gaPointsMulEquiv (R := ℤ) (A := A) f) ^ 2 *
                Multiplicative.toAdd (AdditiveGroup.gaPointsMulEquiv (R := ℤ) (A := A) g))))) *
        kostantRootSubgroupMatrix e h ρ M hM m hm ℬ
          ((AdditiveGroup.gaPointsMulEquiv (R := ℤ) (A := A)).symm
            (Multiplicative.ofAdd ((-a : A) *
              (3 * Multiplicative.toAdd (AdditiveGroup.gaPointsMulEquiv (R := ℤ) (A := A) f) *
                Multiplicative.toAdd
                  (AdditiveGroup.gaPointsMulEquiv (R := ℤ) (A := A) g) ^ 2)))) :=
  commutatorElement_kostantRootSubgroupMatrix_of_g2_short_pair e h ρ M hM ℬ
    hij hik hkj hil him hjm hkl hkm hlm hi hj hk hl hm f g _ _ _
      (congrArg Multiplicative.toAdd
        ((AdditiveGroup.gaPointsMulEquiv (R := ℤ) (A := A)).apply_symm_apply _))
      (congrArg Multiplicative.toAdd
        ((AdditiveGroup.gaPointsMulEquiv (R := ℤ) (A := A)).apply_symm_apply _))
      (congrArg Multiplicative.toAdd
        ((AdditiveGroup.gaPointsMulEquiv (R := ℤ) (A := A)).apply_symm_apply _))

/-- **Steinberg's type-`G₂` Chevalley commutator relation (`α` short, `β` long) in an integral
basis.** -/
theorem commutatorElement_kostantRootSubgroupMatrix_of_lie_eq_three_nsmul
    {i j k l m o : I} {c d a b : ℤ}
    (hij : ⁅e i, e j⁆ = c • e k)
    (hik : c • ⁅e i, e k⁆ = (2 * d) • e l)
    (hil : d • ⁅e i, e l⁆ = (3 * a) • e m)
    (hlk : (d * c) • ⁅e l, e k⁆ = (3 * b) • e o)
    (him : ⁅e i, e m⁆ = 0) (hio : ⁅e i, e o⁆ = 0) (hjk : ⁅e j, e k⁆ = 0)
    (hlm : ⁅e l, e m⁆ = 0) (hko : ⁅e k, e o⁆ = 0) (hlo : ⁅e l, e o⁆ = 0)
    (hmo : ⁅e m, e o⁆ = 0)
    (hi : IsNilpotent (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ (e i))))
    (hj : IsNilpotent (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ (e j))))
    (hk : IsNilpotent (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ (e k))))
    (hl : IsNilpotent (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ (e l))))
    (hm : IsNilpotent (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ (e m))))
    (ho : IsNilpotent (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ (e o))))
    (f g p q r s : WithConv (SymmetricAlgebra ℤ ℤ →ₐ[ℤ] A))
    (hp : Multiplicative.toAdd (AdditiveGroup.gaPointsMulEquiv (R := ℤ) (A := A) p) =
      (c : A) * (Multiplicative.toAdd (AdditiveGroup.gaPointsMulEquiv (R := ℤ) (A := A) f) *
        Multiplicative.toAdd (AdditiveGroup.gaPointsMulEquiv (R := ℤ) (A := A) g)))
    (hq : Multiplicative.toAdd (AdditiveGroup.gaPointsMulEquiv (R := ℤ) (A := A) q) =
      (d : A) * (Multiplicative.toAdd (AdditiveGroup.gaPointsMulEquiv (R := ℤ) (A := A) f) ^ 2 *
        Multiplicative.toAdd (AdditiveGroup.gaPointsMulEquiv (R := ℤ) (A := A) g)))
    (hr : Multiplicative.toAdd (AdditiveGroup.gaPointsMulEquiv (R := ℤ) (A := A) r) =
      (a : A) * (Multiplicative.toAdd (AdditiveGroup.gaPointsMulEquiv (R := ℤ) (A := A) f) ^ 3 *
        Multiplicative.toAdd (AdditiveGroup.gaPointsMulEquiv (R := ℤ) (A := A) g)))
    (hs : Multiplicative.toAdd (AdditiveGroup.gaPointsMulEquiv (R := ℤ) (A := A) s) =
      (2 * (b : A)) *
        (Multiplicative.toAdd (AdditiveGroup.gaPointsMulEquiv (R := ℤ) (A := A) f) ^ 3 *
          Multiplicative.toAdd (AdditiveGroup.gaPointsMulEquiv (R := ℤ) (A := A) g) ^ 2)) :
    ⁅kostantRootSubgroupMatrix e h ρ M hM i hi ℬ f,
        kostantRootSubgroupMatrix e h ρ M hM j hj ℬ g⁆ =
      kostantRootSubgroupMatrix e h ρ M hM k hk ℬ p *
        kostantRootSubgroupMatrix e h ρ M hM l hl ℬ q *
        kostantRootSubgroupMatrix e h ρ M hM m hm ℬ r *
        kostantRootSubgroupMatrix e h ρ M hM o ho ℬ s := by
  repeat rw [kostantRootSubgroupMatrix_def]
  simpa only [MonoidHom.comp_apply, map_commutatorElement, map_mul] using
    congrArg (Units.map (LinearMap.toMatrixAlgEquiv (ℬ.baseChange A)).toMonoidHom)
      (commutatorElement_kostantRootSubgroupPoints_of_lie_eq_three_nsmul e h ρ M hM
        hij hik hil hlk him hio hjk hlm hko hlo hmo hi hj hk hl hm ho f g p q r s hp hq hr hs)

/-- Explicit-parameter form of
`commutatorElement_kostantRootSubgroupMatrix_of_lie_eq_three_nsmul`. -/
theorem commutatorElement_kostantRootSubgroupMatrix_of_lie_eq_three_nsmul'
    {i j k l m o : I} {c d a b : ℤ}
    (hij : ⁅e i, e j⁆ = c • e k)
    (hik : c • ⁅e i, e k⁆ = (2 * d) • e l)
    (hil : d • ⁅e i, e l⁆ = (3 * a) • e m)
    (hlk : (d * c) • ⁅e l, e k⁆ = (3 * b) • e o)
    (him : ⁅e i, e m⁆ = 0) (hio : ⁅e i, e o⁆ = 0) (hjk : ⁅e j, e k⁆ = 0)
    (hlm : ⁅e l, e m⁆ = 0) (hko : ⁅e k, e o⁆ = 0) (hlo : ⁅e l, e o⁆ = 0)
    (hmo : ⁅e m, e o⁆ = 0)
    (hi : IsNilpotent (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ (e i))))
    (hj : IsNilpotent (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ (e j))))
    (hk : IsNilpotent (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ (e k))))
    (hl : IsNilpotent (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ (e l))))
    (hm : IsNilpotent (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ (e m))))
    (ho : IsNilpotent (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ (e o))))
    (f g : WithConv (SymmetricAlgebra ℤ ℤ →ₐ[ℤ] A)) :
    ⁅kostantRootSubgroupMatrix e h ρ M hM i hi ℬ f,
        kostantRootSubgroupMatrix e h ρ M hM j hj ℬ g⁆ =
      kostantRootSubgroupMatrix e h ρ M hM k hk ℬ
          ((AdditiveGroup.gaPointsMulEquiv (R := ℤ) (A := A)).symm
            (Multiplicative.ofAdd ((c : A) *
              (Multiplicative.toAdd (AdditiveGroup.gaPointsMulEquiv (R := ℤ) (A := A) f) *
                Multiplicative.toAdd (AdditiveGroup.gaPointsMulEquiv (R := ℤ) (A := A) g))))) *
        kostantRootSubgroupMatrix e h ρ M hM l hl ℬ
          ((AdditiveGroup.gaPointsMulEquiv (R := ℤ) (A := A)).symm
            (Multiplicative.ofAdd ((d : A) *
              (Multiplicative.toAdd (AdditiveGroup.gaPointsMulEquiv (R := ℤ) (A := A) f) ^ 2 *
                Multiplicative.toAdd (AdditiveGroup.gaPointsMulEquiv (R := ℤ) (A := A) g))))) *
        kostantRootSubgroupMatrix e h ρ M hM m hm ℬ
          ((AdditiveGroup.gaPointsMulEquiv (R := ℤ) (A := A)).symm
            (Multiplicative.ofAdd ((a : A) *
              (Multiplicative.toAdd (AdditiveGroup.gaPointsMulEquiv (R := ℤ) (A := A) f) ^ 3 *
                Multiplicative.toAdd (AdditiveGroup.gaPointsMulEquiv (R := ℤ) (A := A) g))))) *
        kostantRootSubgroupMatrix e h ρ M hM o ho ℬ
          ((AdditiveGroup.gaPointsMulEquiv (R := ℤ) (A := A)).symm
            (Multiplicative.ofAdd ((2 * (b : A)) *
              (Multiplicative.toAdd (AdditiveGroup.gaPointsMulEquiv (R := ℤ) (A := A) f) ^ 3 *
                Multiplicative.toAdd
                  (AdditiveGroup.gaPointsMulEquiv (R := ℤ) (A := A) g) ^ 2)))) :=
  commutatorElement_kostantRootSubgroupMatrix_of_lie_eq_three_nsmul e h ρ M hM ℬ
    hij hik hil hlk him hio hjk hlm hko hlo hmo hi hj hk hl hm ho f g _ _ _ _
      (congrArg Multiplicative.toAdd
        ((AdditiveGroup.gaPointsMulEquiv (R := ℤ) (A := A)).apply_symm_apply _))
      (congrArg Multiplicative.toAdd
        ((AdditiveGroup.gaPointsMulEquiv (R := ℤ) (A := A)).apply_symm_apply _))
      (congrArg Multiplicative.toAdd
        ((AdditiveGroup.gaPointsMulEquiv (R := ℤ) (A := A)).apply_symm_apply _))
      (congrArg Multiplicative.toAdd
        ((AdditiveGroup.gaPointsMulEquiv (R := ℤ) (A := A)).apply_symm_apply _))

/-- **Steinberg's type-`G₂` Chevalley commutator relation (`α` long, `β` short) in an integral
basis.** -/
theorem commutatorElement_kostantRootSubgroupMatrix_of_lie_eq_three_nsmul_rev
    {i j k l m o : I} {c d a b : ℤ}
    (hij : ⁅e i, e j⁆ = c • e k)
    (hkj : c • ⁅e k, e j⁆ = (2 * d) • e l)
    (hjl : d • ⁅e j, e l⁆ = (3 * a) • e m)
    (hkl : (d * c) • ⁅e k, e l⁆ = (3 * b) • e o)
    (hjm : ⁅e j, e m⁆ = 0) (hjo : ⁅e j, e o⁆ = 0) (hik : ⁅e i, e k⁆ = 0)
    (hlm : ⁅e l, e m⁆ = 0) (hko : ⁅e k, e o⁆ = 0) (hlo : ⁅e l, e o⁆ = 0)
    (hmo : ⁅e m, e o⁆ = 0)
    (hi : IsNilpotent (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ (e i))))
    (hj : IsNilpotent (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ (e j))))
    (hk : IsNilpotent (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ (e k))))
    (hl : IsNilpotent (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ (e l))))
    (hm : IsNilpotent (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ (e m))))
    (ho : IsNilpotent (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ (e o))))
    (f g p q r s : WithConv (SymmetricAlgebra ℤ ℤ →ₐ[ℤ] A))
    (hp : Multiplicative.toAdd (AdditiveGroup.gaPointsMulEquiv (R := ℤ) (A := A) p) =
      (c : A) * (Multiplicative.toAdd (AdditiveGroup.gaPointsMulEquiv (R := ℤ) (A := A) f) *
        Multiplicative.toAdd (AdditiveGroup.gaPointsMulEquiv (R := ℤ) (A := A) g)))
    (hq : Multiplicative.toAdd (AdditiveGroup.gaPointsMulEquiv (R := ℤ) (A := A) q) =
      (-d : A) * (Multiplicative.toAdd (AdditiveGroup.gaPointsMulEquiv (R := ℤ) (A := A) f) *
        Multiplicative.toAdd (AdditiveGroup.gaPointsMulEquiv (R := ℤ) (A := A) g) ^ 2))
    (hr : Multiplicative.toAdd (AdditiveGroup.gaPointsMulEquiv (R := ℤ) (A := A) r) =
      (-a : A) * (Multiplicative.toAdd (AdditiveGroup.gaPointsMulEquiv (R := ℤ) (A := A) f) *
        Multiplicative.toAdd (AdditiveGroup.gaPointsMulEquiv (R := ℤ) (A := A) g) ^ 3))
    (hs : Multiplicative.toAdd (AdditiveGroup.gaPointsMulEquiv (R := ℤ) (A := A) s) =
      (b : A) * (Multiplicative.toAdd (AdditiveGroup.gaPointsMulEquiv (R := ℤ) (A := A) f) ^ 2 *
        Multiplicative.toAdd (AdditiveGroup.gaPointsMulEquiv (R := ℤ) (A := A) g) ^ 3)) :
    ⁅kostantRootSubgroupMatrix e h ρ M hM i hi ℬ f,
        kostantRootSubgroupMatrix e h ρ M hM j hj ℬ g⁆ =
      kostantRootSubgroupMatrix e h ρ M hM k hk ℬ p *
        kostantRootSubgroupMatrix e h ρ M hM l hl ℬ q *
        kostantRootSubgroupMatrix e h ρ M hM m hm ℬ r *
        kostantRootSubgroupMatrix e h ρ M hM o ho ℬ s := by
  repeat rw [kostantRootSubgroupMatrix_def]
  simpa only [MonoidHom.comp_apply, map_commutatorElement, map_mul] using
    congrArg (Units.map (LinearMap.toMatrixAlgEquiv (ℬ.baseChange A)).toMonoidHom)
      (commutatorElement_kostantRootSubgroupPoints_of_lie_eq_three_nsmul_rev e h ρ M hM
        hij hkj hjl hkl hjm hjo hik hlm hko hlo hmo hi hj hk hl hm ho f g p q r s hp hq hr hs)

/-- Explicit-parameter form of
`commutatorElement_kostantRootSubgroupMatrix_of_lie_eq_three_nsmul_rev`. -/
theorem commutatorElement_kostantRootSubgroupMatrix_of_lie_eq_three_nsmul_rev'
    {i j k l m o : I} {c d a b : ℤ}
    (hij : ⁅e i, e j⁆ = c • e k)
    (hkj : c • ⁅e k, e j⁆ = (2 * d) • e l)
    (hjl : d • ⁅e j, e l⁆ = (3 * a) • e m)
    (hkl : (d * c) • ⁅e k, e l⁆ = (3 * b) • e o)
    (hjm : ⁅e j, e m⁆ = 0) (hjo : ⁅e j, e o⁆ = 0) (hik : ⁅e i, e k⁆ = 0)
    (hlm : ⁅e l, e m⁆ = 0) (hko : ⁅e k, e o⁆ = 0) (hlo : ⁅e l, e o⁆ = 0)
    (hmo : ⁅e m, e o⁆ = 0)
    (hi : IsNilpotent (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ (e i))))
    (hj : IsNilpotent (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ (e j))))
    (hk : IsNilpotent (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ (e k))))
    (hl : IsNilpotent (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ (e l))))
    (hm : IsNilpotent (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ (e m))))
    (ho : IsNilpotent (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ (e o))))
    (f g : WithConv (SymmetricAlgebra ℤ ℤ →ₐ[ℤ] A)) :
    ⁅kostantRootSubgroupMatrix e h ρ M hM i hi ℬ f,
        kostantRootSubgroupMatrix e h ρ M hM j hj ℬ g⁆ =
      kostantRootSubgroupMatrix e h ρ M hM k hk ℬ
          ((AdditiveGroup.gaPointsMulEquiv (R := ℤ) (A := A)).symm
            (Multiplicative.ofAdd ((c : A) *
              (Multiplicative.toAdd (AdditiveGroup.gaPointsMulEquiv (R := ℤ) (A := A) f) *
                Multiplicative.toAdd (AdditiveGroup.gaPointsMulEquiv (R := ℤ) (A := A) g))))) *
        kostantRootSubgroupMatrix e h ρ M hM l hl ℬ
          ((AdditiveGroup.gaPointsMulEquiv (R := ℤ) (A := A)).symm
            (Multiplicative.ofAdd ((-d : A) *
              (Multiplicative.toAdd (AdditiveGroup.gaPointsMulEquiv (R := ℤ) (A := A) f) *
                Multiplicative.toAdd (AdditiveGroup.gaPointsMulEquiv (R := ℤ) (A := A) g) ^ 2)))) *
        kostantRootSubgroupMatrix e h ρ M hM m hm ℬ
          ((AdditiveGroup.gaPointsMulEquiv (R := ℤ) (A := A)).symm
            (Multiplicative.ofAdd ((-a : A) *
              (Multiplicative.toAdd (AdditiveGroup.gaPointsMulEquiv (R := ℤ) (A := A) f) *
                Multiplicative.toAdd (AdditiveGroup.gaPointsMulEquiv (R := ℤ) (A := A) g) ^ 3)))) *
        kostantRootSubgroupMatrix e h ρ M hM o ho ℬ
          ((AdditiveGroup.gaPointsMulEquiv (R := ℤ) (A := A)).symm
            (Multiplicative.ofAdd ((b : A) *
              (Multiplicative.toAdd (AdditiveGroup.gaPointsMulEquiv (R := ℤ) (A := A) f) ^ 2 *
                Multiplicative.toAdd
                  (AdditiveGroup.gaPointsMulEquiv (R := ℤ) (A := A) g) ^ 3)))) :=
  commutatorElement_kostantRootSubgroupMatrix_of_lie_eq_three_nsmul_rev e h ρ M hM ℬ
    hij hkj hjl hkl hjm hjo hik hlm hko hlo hmo hi hj hk hl hm ho f g _ _ _ _
      (congrArg Multiplicative.toAdd
        ((AdditiveGroup.gaPointsMulEquiv (R := ℤ) (A := A)).apply_symm_apply _))
      (congrArg Multiplicative.toAdd
        ((AdditiveGroup.gaPointsMulEquiv (R := ℤ) (A := A)).apply_symm_apply _))
      (congrArg Multiplicative.toAdd
        ((AdditiveGroup.gaPointsMulEquiv (R := ℤ) (A := A)).apply_symm_apply _))
      (congrArg Multiplicative.toAdd
        ((AdditiveGroup.gaPointsMulEquiv (R := ℤ) (A := A)).apply_symm_apply _))

end Matrices

end TauCeti.UniversalEnvelopingAlgebra
