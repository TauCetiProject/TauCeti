/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.Torsion.Basic
public import TauCeti.AlgebraicTopology.Cohomology.UniversalCoefficient

/-!
# The torsion of singular cohomology

Over a hereditary commutative ring `k`, the universal coefficient sequence

`0 → Ext¹(Hₙ(X; R), M) → Hⁿ⁺¹(X; R, M) → Hom(Hₙ₊₁(X; R), M) → 0`

locates the torsion of singular cohomology. If `M` is torsion-free, so is `Hom(Hₙ₊₁(X; R), M)`, so
every torsion class of `Hⁿ⁺¹(X; R, M)` pairs to zero with homology and comes from `Ext¹`. If
moreover `Ext¹(Hₙ(X; R), M)` is a torsion module, its image consists of torsion classes. In that
case the torsion submodule of `Hⁿ⁺¹(X; R, M)` is exactly the image of `Ext¹(Hₙ(X; R), M)`
(`TopCat.torsion_singularCohomology_eq_range_singularExtToCohomology`), and it is isomorphic to
`Ext¹(Hₙ(X; R), M)`, since the `Ext` term of the sequence is injective
(`TopCat.extOneSingularHomologyEquivTorsion`). In particular the two have the same cardinality
(`TopCat.card_torsion_singularCohomology_eq_card_ext`).

For `k = R = M = ℤ` and `Hₙ(X; ℤ)` finitely generated, `Ext¹(Hₙ(X; ℤ), ℤ)` is finite, and this is
the classical statement that the torsion of `Hⁿ⁺¹(X; ℤ)` is that of `Hₙ(X; ℤ)`, up to isomorphism.

## Main results

* `TopCat.torsion_singularCohomology_le_range_singularExtToCohomology`: for torsion-free `M`,
  every torsion class of `Hⁿ⁺¹(X; R, M)` comes from `Ext¹(Hₙ(X; R), M)`.
* `TopCat.torsion_singularCohomology_eq_range_singularExtToCohomology`: if moreover
  `Ext¹(Hₙ(X; R), M)` is a torsion module, the torsion of `Hⁿ⁺¹(X; R, M)` is its image.
* `TopCat.extOneSingularHomologyEquivTorsion`: under the same hypotheses,
  `Ext¹(Hₙ(X; R), M) ≃ₗ[k] torsion (Hⁿ⁺¹(X; R, M))`.
* `TopCat.card_torsion_singularCohomology_eq_card_ext`: the two have the same `Nat.card`.

## References

* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Section 3.1, Theorem 3.2 and Corollary 3.3.
-/

public section

noncomputable section

open CategoryTheory AlgebraicTopology Abelian

universe w

namespace TopCat

variable {k : Type w} [CommRing k]
  [∀ V : ModuleCat.{w} k, HasProjectiveDimensionLE V 1]
  (X : TopCat.{w}) (R M : ModuleCat.{w} k) [Module.Projective k R] [Module.IsTorsionFree k M]

/-- **Torsion classes come from `Ext¹`.** Over a hereditary commutative ring, with a torsion-free
coefficient module `M`, every torsion class of `Hⁿ⁺¹(X; R, M)` pairs to zero with
`Hₙ₊₁(X; R)`, hence lies in the image of `Ext¹(Hₙ(X; R), M)`. -/
theorem torsion_singularCohomology_le_range_singularExtToCohomology (n : ℕ) :
    Submodule.torsion k (X.singularCohomology R k M (n + 1)) ≤
      LinearMap.range (X.singularExtToCohomology R M n) := by
  rintro c ⟨a, hc⟩
  rw [← (X.exact_singularExtToCohomology_singularKronecker R M n).linearMap_ker_eq,
    LinearMap.mem_ker]
  ext x
  have hx := congrArg (fun g ↦ g.hom x)
    (congrArg (X.singularKronecker (R := R) (M := M) k (n + 1)) hc)
  simp only [Submonoid.smul_def, map_smul, map_zero, ModuleCat.hom_smul, LinearMap.smul_apply,
    ModuleCat.hom_zero, LinearMap.zero_apply] at hx
  -- `a` is a non-zero-divisor, so it acts injectively on the torsion-free module `M`.
  simpa using Module.IsTorsionFree.isSMulRegular (isRegular_iff_mem_nonZeroDivisors.2 a.2)
    (hx.trans (smul_zero _).symm)

variable {X R M} in
/-- **The torsion of singular cohomology.** Over a hereditary commutative ring, with a
torsion-free coefficient module `M`, if `Ext¹(Hₙ(X; R), M)` is a torsion module then the torsion
submodule of `Hⁿ⁺¹(X; R, M)` is the image of `Ext¹(Hₙ(X; R), M)` under the universal coefficient
sequence. -/
theorem torsion_singularCohomology_eq_range_singularExtToCohomology {n : ℕ}
    (h : Module.IsTorsion k
      (Ext.{w} (((singularHomologyFunctor (ModuleCat.{w} k) n).obj R).obj X) M 1)) :
    Submodule.torsion k (X.singularCohomology R k M (n + 1)) =
      LinearMap.range (X.singularExtToCohomology R M n) := by
  refine (X.torsion_singularCohomology_le_range_singularExtToCohomology R M n).antisymm ?_
  rintro _ ⟨e, rfl⟩
  obtain ⟨a, ha⟩ := h (x := e)
  exact ⟨a, by rw [Submonoid.smul_def, ← map_smul, ← Submonoid.smul_def, ha, map_zero]⟩

variable {X R M} in
/-- Under the hypotheses of `TopCat.torsion_singularCohomology_eq_range_singularExtToCohomology`,
the `Ext` term of the universal coefficient sequence is an isomorphism
`Ext¹(Hₙ(X; R), M) ≃ₗ[k] torsion (Hⁿ⁺¹(X; R, M))`. -/
def extOneSingularHomologyEquivTorsion {n : ℕ}
    (h : Module.IsTorsion k
      (Ext.{w} (((singularHomologyFunctor (ModuleCat.{w} k) n).obj R).obj X) M 1)) :
    Ext.{w} (((singularHomologyFunctor (ModuleCat.{w} k) n).obj R).obj X) M 1 ≃ₗ[k]
      Submodule.torsion k (X.singularCohomology R k M (n + 1)) :=
  (LinearEquiv.ofInjective _ (X.singularExtToCohomology_injective R M n)).trans
    (LinearEquiv.ofEq _ _ (torsion_singularCohomology_eq_range_singularExtToCohomology h).symm)

variable {X R M} in
/-- The isomorphism `TopCat.extOneSingularHomologyEquivTorsion` is the `Ext` term of the universal
coefficient sequence. -/
@[simp]
theorem coe_extOneSingularHomologyEquivTorsion_apply {n : ℕ}
    (h : Module.IsTorsion k
      (Ext.{w} (((singularHomologyFunctor (ModuleCat.{w} k) n).obj R).obj X) M 1))
    (e : Ext.{w} (((singularHomologyFunctor (ModuleCat.{w} k) n).obj R).obj X) M 1) :
    (extOneSingularHomologyEquivTorsion h e : X.singularCohomology R k M (n + 1)) =
      X.singularExtToCohomology R M n e :=
  (rfl)

variable {X R M} in
/-- Under the hypotheses of `TopCat.torsion_singularCohomology_eq_range_singularExtToCohomology`,
the torsion submodule of `Hⁿ⁺¹(X; R, M)` has the same `Nat.card` as `Ext¹(Hₙ(X; R), M)`. -/
theorem card_torsion_singularCohomology_eq_card_ext {n : ℕ}
    (h : Module.IsTorsion k
      (Ext.{w} (((singularHomologyFunctor (ModuleCat.{w} k) n).obj R).obj X) M 1)) :
    Nat.card (Submodule.torsion k (X.singularCohomology R k M (n + 1))) =
      Nat.card (Ext.{w} (((singularHomologyFunctor (ModuleCat.{w} k) n).obj R).obj X) M 1) :=
  (Nat.card_congr (extOneSingularHomologyEquivTorsion h).toEquiv).symm

end TopCat
