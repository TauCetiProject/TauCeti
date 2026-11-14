/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.UniversalEnveloping.Kostant.RootSubgroup.MultiplyLacedRelations
public import TauCeti.Algebra.Lie.UniversalEnveloping.Kostant.RootSubgroup.Scheme.Basic

/-!
# Multiply-laced Chevalley relations for Kostant root-subgroup scheme morphisms

This file transports conditional multiply-laced Chevalley commutator relations in both root orders
to scheme-valued points of the represented root-subgroup morphisms `xᵢ : 𝔾ₐ → GLₙ`. Under the stated
bracket and nilpotence hypotheses for `{α + β, 2α + β}` and `{α + β, α + 2β}`, the relations are

```text
⁅x_α(t), x_β(u)⁆ = x_{α+β}(c t u) x_{2α+β}(d t² u),
⁅x_α(t), x_β(u)⁆ = x_{α+β}(c t u) x_{α+2β}(-d t u²).
```

It transports the matrix relations from `RootSubgroup/MultiplyLacedRelations.lean` through the
point-comparison theorem for the affine group-scheme morphisms, stating the equations at the
interface used by the generated Chevalley--Demazure carrier.

## Main declarations

* `TauCeti.UniversalEnvelopingAlgebra.
  commutatorElement_schemePointsMulEquiv_kostantRootSubgroup_of_lie_lie_eq` and
  `commutatorElement_schemePointsMulEquiv_kostantRootSubgroup_of_lie_lie_eq'`: the multiply-laced
  relation for `{α + β, 2α + β}` on scheme-valued points.
* `TauCeti.UniversalEnvelopingAlgebra.
  commutatorElement_schemePointsMulEquiv_kostantRootSubgroup_of_lie_lie_rev_eq` and
  `commutatorElement_schemePointsMulEquiv_kostantRootSubgroup_of_lie_lie_rev_eq'`: the reversed
  multiply-laced relation for `{α + β, α + 2β}` on scheme-valued points.

## References

* R. Steinberg, *Lectures on Chevalley Groups*, Chapter 3, Lemma 15.
* R. W. Carter, *Simple Groups of Lie Type*, Theorem 5.2.2.
* J. E. Humphreys, *Introduction to Lie Algebras and Representation Theory*, Sections 26--27.
* J. C. Jantzen, *Representations of Algebraic Groups*, II.1.
-/

public section

open AlgebraicGeometry CategoryTheory TensorProduct WithConv
open scoped CategoryTheory.MonObj commutatorElement

namespace TauCeti.UniversalEnvelopingAlgebra

universe u w

variable {L : Type u} [LieRing L] [LieAlgebra ℚ L]
variable {I : Type w} {κ : Type*}
variable {V : Type} [AddCommGroup V] [Module ℚ V]

variable (e : I → L) (h : κ → L)
variable (ρ : _root_.UniversalEnvelopingAlgebra ℚ L →ₐ[ℚ] Module.End ℚ V)
variable (M : AddSubgroup V)
variable (hM : ∀ u ∈ kostantForm e h, ∀ v ∈ M, ρ u v ∈ M)

-- Match tensor products to the `ℤ`-algebra structure used by scalar extension.
attribute [local instance high] Algebra.toModule

variable {n : ℕ} (b : Module.Basis (Fin n) ℤ M)
variable (A : Type) [CommRing A]

/-- **The multiply-laced Chevalley commutator relation on scheme-valued points.** Suppose the
distinguished root vectors form the chain `β`, `α + β`, `2α + β`, and let `r` and `s` carry
parameters `c t u` and `d t² u`. Then the commutator of the represented `i`- and `j`-root values
is the product of the represented `k`- and `l`-root values. -/
theorem commutatorElement_schemePointsMulEquiv_kostantRootSubgroup_of_lie_lie_eq
    {i j k l : I} {c d : ℤ}
    (hij : ⁅e i, e j⁆ = c • e k) (hiij : ⁅e i, ⁅e i, e j⁆⁆ = (2 * d) • e l)
    (hil : ⁅e i, e l⁆ = 0) (hjk : ⁅e j, e k⁆ = 0)
    (hi : IsNilpotent (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ (e i))))
    (hj : IsNilpotent (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ (e j))))
    (hk : IsNilpotent (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ (e k))))
    (hl : IsNilpotent (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ (e l))))
    (p q r s : (Spec (CommRingCat.of A)).asOver (Spec (CommRingCat.of ℤ)) ⟶
      (AdditiveGroup.groupScheme ℤ).X)
    (hr : Multiplicative.toAdd (AdditiveGroup.schemePointsMulEquiv A r) =
      (c : A) * (Multiplicative.toAdd (AdditiveGroup.schemePointsMulEquiv A p) *
        Multiplicative.toAdd (AdditiveGroup.schemePointsMulEquiv A q)))
    (hs : Multiplicative.toAdd (AdditiveGroup.schemePointsMulEquiv A s) =
      (d : A) * (Multiplicative.toAdd (AdditiveGroup.schemePointsMulEquiv A p) ^ 2 *
        Multiplicative.toAdd (AdditiveGroup.schemePointsMulEquiv A q))) :
    ⁅GeneralLinear.schemePointsMulEquiv n A
        (p ≫ (kostantRootSubgroup e h ρ M hM i hi b).hom.hom),
      GeneralLinear.schemePointsMulEquiv n A
        (q ≫ (kostantRootSubgroup e h ρ M hM j hj b).hom.hom)⁆ =
      GeneralLinear.schemePointsMulEquiv n A
          (r ≫ (kostantRootSubgroup e h ρ M hM k hk b).hom.hom) *
        GeneralLinear.schemePointsMulEquiv n A
          (s ≫ (kostantRootSubgroup e h ρ M hM l hl b).hom.hom) := by
  rw [schemePointsMulEquiv_kostantRootSubgroup,
    schemePointsMulEquiv_kostantRootSubgroup,
    schemePointsMulEquiv_kostantRootSubgroup,
    schemePointsMulEquiv_kostantRootSubgroup]
  apply commutatorElement_kostantRootSubgroupMatrix_of_lie_lie_eq
    e h ρ M hM b hij hiij hil hjk hi hj hk hl
  · simpa only [AdditiveGroup.schemePointsMulEquiv_apply] using hr
  · simpa only [AdditiveGroup.schemePointsMulEquiv_apply] using hs

/-- The multiply-laced Chevalley commutator relation on scheme-valued points with both output
points written out at parameters `c t u` and `d t² u`. -/
theorem commutatorElement_schemePointsMulEquiv_kostantRootSubgroup_of_lie_lie_eq'
    {i j k l : I} {c d : ℤ}
    (hij : ⁅e i, e j⁆ = c • e k) (hiij : ⁅e i, ⁅e i, e j⁆⁆ = (2 * d) • e l)
    (hil : ⁅e i, e l⁆ = 0) (hjk : ⁅e j, e k⁆ = 0)
    (hi : IsNilpotent (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ (e i))))
    (hj : IsNilpotent (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ (e j))))
    (hk : IsNilpotent (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ (e k))))
    (hl : IsNilpotent (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ (e l))))
    (p q : (Spec (CommRingCat.of A)).asOver (Spec (CommRingCat.of ℤ)) ⟶
      (AdditiveGroup.groupScheme ℤ).X) :
    ⁅GeneralLinear.schemePointsMulEquiv n A
        (p ≫ (kostantRootSubgroup e h ρ M hM i hi b).hom.hom),
      GeneralLinear.schemePointsMulEquiv n A
        (q ≫ (kostantRootSubgroup e h ρ M hM j hj b).hom.hom)⁆ =
      GeneralLinear.schemePointsMulEquiv n A
          ((AdditiveGroup.schemePointsMulEquiv A).symm
              (Multiplicative.ofAdd ((c : A) *
                (Multiplicative.toAdd (AdditiveGroup.schemePointsMulEquiv A p) *
                  Multiplicative.toAdd (AdditiveGroup.schemePointsMulEquiv A q)))) ≫
            (kostantRootSubgroup e h ρ M hM k hk b).hom.hom) *
        GeneralLinear.schemePointsMulEquiv n A
          ((AdditiveGroup.schemePointsMulEquiv A).symm
              (Multiplicative.ofAdd ((d : A) *
                (Multiplicative.toAdd (AdditiveGroup.schemePointsMulEquiv A p) ^ 2 *
                  Multiplicative.toAdd (AdditiveGroup.schemePointsMulEquiv A q)))) ≫
            (kostantRootSubgroup e h ρ M hM l hl b).hom.hom) :=
  commutatorElement_schemePointsMulEquiv_kostantRootSubgroup_of_lie_lie_eq
    e h ρ M hM b A hij hiij hil hjk hi hj hk hl p q _ _
      (congrArg Multiplicative.toAdd
        ((AdditiveGroup.schemePointsMulEquiv A).apply_symm_apply _))
      (congrArg Multiplicative.toAdd
        ((AdditiveGroup.schemePointsMulEquiv A).apply_symm_apply _))

/-- **Steinberg's reversed multiply-laced Chevalley commutator relation on scheme-valued points.**
Suppose `e i, e j, e k, e l` correspond to `α, β, α + β, α + 2β` with `⁅e i, e j⁆ = c • e k`,
`⁅e j, ⁅e j, e i⁆⁆ = (2 * d) • e l`, and `⁅e j, e l⁆ = ⁅e i, e k⁆ = 0`, and let `r` and `s` carry
parameters `c t u` and `-d t u²`. Then the commutator of the represented `i`- and `j`-root values is
the product of the represented `k`- and `l`-root values. -/
theorem commutatorElement_schemePointsMulEquiv_kostantRootSubgroup_of_lie_lie_rev_eq
    {i j k l : I} {c d : ℤ}
    (hij : ⁅e i, e j⁆ = c • e k) (hjji : ⁅e j, ⁅e j, e i⁆⁆ = (2 * d) • e l)
    (hjl : ⁅e j, e l⁆ = 0) (hik : ⁅e i, e k⁆ = 0)
    (hi : IsNilpotent (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ (e i))))
    (hj : IsNilpotent (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ (e j))))
    (hk : IsNilpotent (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ (e k))))
    (hl : IsNilpotent (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ (e l))))
    (p q r s : (Spec (CommRingCat.of A)).asOver (Spec (CommRingCat.of ℤ)) ⟶
      (AdditiveGroup.groupScheme ℤ).X)
    (hr : Multiplicative.toAdd (AdditiveGroup.schemePointsMulEquiv A r) =
      (c : A) * (Multiplicative.toAdd (AdditiveGroup.schemePointsMulEquiv A p) *
        Multiplicative.toAdd (AdditiveGroup.schemePointsMulEquiv A q)))
    (hs : Multiplicative.toAdd (AdditiveGroup.schemePointsMulEquiv A s) =
      (-d : A) * (Multiplicative.toAdd (AdditiveGroup.schemePointsMulEquiv A p) *
        Multiplicative.toAdd (AdditiveGroup.schemePointsMulEquiv A q) ^ 2)) :
    ⁅GeneralLinear.schemePointsMulEquiv n A
        (p ≫ (kostantRootSubgroup e h ρ M hM i hi b).hom.hom),
      GeneralLinear.schemePointsMulEquiv n A
        (q ≫ (kostantRootSubgroup e h ρ M hM j hj b).hom.hom)⁆ =
      GeneralLinear.schemePointsMulEquiv n A
          (r ≫ (kostantRootSubgroup e h ρ M hM k hk b).hom.hom) *
        GeneralLinear.schemePointsMulEquiv n A
          (s ≫ (kostantRootSubgroup e h ρ M hM l hl b).hom.hom) := by
  repeat rw [schemePointsMulEquiv_kostantRootSubgroup]
  apply commutatorElement_kostantRootSubgroupMatrix_of_lie_lie_rev_eq
    e h ρ M hM b hij hjji hjl hik hi hj hk hl
  · simpa only [AdditiveGroup.schemePointsMulEquiv_apply] using hr
  · simpa only [AdditiveGroup.schemePointsMulEquiv_apply] using hs

/-- The reversed multiply-laced Chevalley commutator relation on scheme-valued points with both
output points written out at parameters `c t u` and `-d t u²`. -/
theorem commutatorElement_schemePointsMulEquiv_kostantRootSubgroup_of_lie_lie_rev_eq'
    {i j k l : I} {c d : ℤ}
    (hij : ⁅e i, e j⁆ = c • e k) (hjji : ⁅e j, ⁅e j, e i⁆⁆ = (2 * d) • e l)
    (hjl : ⁅e j, e l⁆ = 0) (hik : ⁅e i, e k⁆ = 0)
    (hi : IsNilpotent (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ (e i))))
    (hj : IsNilpotent (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ (e j))))
    (hk : IsNilpotent (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ (e k))))
    (hl : IsNilpotent (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ (e l))))
    (p q : (Spec (CommRingCat.of A)).asOver (Spec (CommRingCat.of ℤ)) ⟶
      (AdditiveGroup.groupScheme ℤ).X) :
    ⁅GeneralLinear.schemePointsMulEquiv n A
        (p ≫ (kostantRootSubgroup e h ρ M hM i hi b).hom.hom),
      GeneralLinear.schemePointsMulEquiv n A
        (q ≫ (kostantRootSubgroup e h ρ M hM j hj b).hom.hom)⁆ =
      GeneralLinear.schemePointsMulEquiv n A
          ((AdditiveGroup.schemePointsMulEquiv A).symm
              (Multiplicative.ofAdd ((c : A) *
                (Multiplicative.toAdd (AdditiveGroup.schemePointsMulEquiv A p) *
                  Multiplicative.toAdd (AdditiveGroup.schemePointsMulEquiv A q)))) ≫
            (kostantRootSubgroup e h ρ M hM k hk b).hom.hom) *
        GeneralLinear.schemePointsMulEquiv n A
          ((AdditiveGroup.schemePointsMulEquiv A).symm
              (Multiplicative.ofAdd ((-d : A) *
                (Multiplicative.toAdd (AdditiveGroup.schemePointsMulEquiv A p) *
                  Multiplicative.toAdd (AdditiveGroup.schemePointsMulEquiv A q) ^ 2))) ≫
            (kostantRootSubgroup e h ρ M hM l hl b).hom.hom) :=
  commutatorElement_schemePointsMulEquiv_kostantRootSubgroup_of_lie_lie_rev_eq
    e h ρ M hM b A hij hjji hjl hik hi hj hk hl p q _ _
      (congrArg Multiplicative.toAdd
        ((AdditiveGroup.schemePointsMulEquiv A).apply_symm_apply _))
      (congrArg Multiplicative.toAdd
        ((AdditiveGroup.schemePointsMulEquiv A).apply_symm_apply _))

end TauCeti.UniversalEnvelopingAlgebra
