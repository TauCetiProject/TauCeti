/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.UniversalEnveloping.Kostant.RootSubgroup.Commutator.Basic
public import TauCeti.Algebra.Lie.UniversalEnveloping.Commutator.G2.ShortPair

/-!
# The G₂ short-pair relation for Kostant root subgroups

For the roots `α`, `α + β`, `2α + β`, `3α + β`, `3α + 2β`, the scaled brackets
`[eᵢ,eⱼ] = 2c eₖ`, `c[eᵢ,eₖ] = 3d eₗ`, and `c[eₖ,eⱼ] = 3a eₘ` give

```text
xᵢ(t) xⱼ(u) = xⱼ(u) xₖ(2ctu) xₗ(3dt²u) xₘ(3atu²) xᵢ(t).
```

The six vanishing brackets are listed explicitly in the theorem. The parameters belong to
an arbitrary commutative ring, so the relation includes characteristics two and three.
The integral coefficients allow different choices of signs for the distinguished root vectors.

This is the Kostant-lattice form of `baseChangeExp_mul_baseChangeExp_of_g2_short_pair`
and the short-pair input for the relations of the represented root-subgroup morphisms.

## References

* R. W. Carter, *Simple Groups of Lie Type*, §4.2 and Theorem 5.2.2.
* J. C. Jantzen, *Representations of Algebraic Groups*, II.1.
-/

public section

open TensorProduct WithConv

namespace TauCeti.UniversalEnvelopingAlgebra

universe u v w

variable {L : Type u} [LieRing L] [LieAlgebra ℚ L]
variable {ι : Type w} {κ : Type*}
variable {V : Type v} [AddCommGroup V] [Module ℚ V]

variable (e : ι → L) (h : κ → L)
variable (ρ : _root_.UniversalEnvelopingAlgebra ℚ L →ₐ[ℚ] Module.End ℚ V)
variable (M : AddSubgroup V)
variable (hM : ∀ x ∈ kostantForm e h, ∀ v ∈ M, ρ x v ∈ M)

-- Match tensor products to the module structure of the parameter algebra.
attribute [local instance high] Algebra.toModule

variable {A : Type*} [CommRing A] [Algebra ℤ A]

/-- The G₂ short-pair product relation on an admissible Kostant lattice, with the three
output points supplied at parameters `2ctu`, `3dt²u`, and `3atu²`. The indices
`i, j, k, l, m` correspond to `α, α + β, 2α + β, 3α + β, 3α + 2β`. -/
theorem kostantRootSubgroupPoints_mul_of_g2_short_pair
    {i j k l m : ι} {c d a : ℤ}
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
      (a : A) * (3 * Multiplicative.toAdd (AdditiveGroup.gaPointsMulEquiv (R := ℤ) (A := A) f) *
        Multiplicative.toAdd (AdditiveGroup.gaPointsMulEquiv (R := ℤ) (A := A) g) ^ 2)) :
    kostantRootSubgroupPoints e h ρ M hM i hi f *
        kostantRootSubgroupPoints e h ρ M hM j hj g =
      kostantRootSubgroupPoints e h ρ M hM j hj g *
        kostantRootSubgroupPoints e h ρ M hM k hk p *
        kostantRootSubgroupPoints e h ρ M hM l hl q *
        kostantRootSubgroupPoints e h ρ M hM m hm r *
        kostantRootSubgroupPoints e h ρ M hM i hi f := by
  refine Units.ext ?_
  simp only [Units.val_mul, kostantRootSubgroupPoints_val]
  rw [hp, hq, hr]
  exact baseChangeExp_mul_baseChangeExp_of_g2_short_pair_lie e ρ M
    hij hik hkj hil him hjm hkl hkm hlm hi hj hk hl hm _ _ _ _ _ _ _

/-- The G₂ short-pair product relation on an admissible Kostant lattice, with the three output
points written explicitly at parameters `2ctu`, `3dt²u`, and `3atu²`. -/
theorem kostantRootSubgroupPoints_mul_of_g2_short_pair'
    {i j k l m : ι} {c d a : ℤ}
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
    kostantRootSubgroupPoints e h ρ M hM i hi f *
        kostantRootSubgroupPoints e h ρ M hM j hj g =
      kostantRootSubgroupPoints e h ρ M hM j hj g *
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
            (Multiplicative.ofAdd ((a : A) *
              (3 * Multiplicative.toAdd (AdditiveGroup.gaPointsMulEquiv (R := ℤ) (A := A) f) *
                Multiplicative.toAdd (AdditiveGroup.gaPointsMulEquiv (R := ℤ) (A := A) g) ^ 2)))) *
        kostantRootSubgroupPoints e h ρ M hM i hi f :=
  kostantRootSubgroupPoints_mul_of_g2_short_pair
    e h ρ M hM hij hik hkj hil him hjm hkl hkm hlm hi hj hk hl hm f g _ _ _
      (congrArg Multiplicative.toAdd
        ((AdditiveGroup.gaPointsMulEquiv (R := ℤ) (A := A)).apply_symm_apply _))
      (congrArg Multiplicative.toAdd
        ((AdditiveGroup.gaPointsMulEquiv (R := ℤ) (A := A)).apply_symm_apply _))
      (congrArg Multiplicative.toAdd
        ((AdditiveGroup.gaPointsMulEquiv (R := ℤ) (A := A)).apply_symm_apply _))

end TauCeti.UniversalEnvelopingAlgebra
