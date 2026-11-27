/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.CharacterModule.Basic
public import TauCeti.RepresentationTheory.Character.Twist
public import TauCeti.Algebra.Module.CharacterModule.Trace.Dual

/-!
# Equivariant trace comparison of finite coefficient duals

A Matlis trace `ℓ : R →+ ℚ/ℤ` identifies the linear dual of an `R`-module with its additive
character dual. For a representation, this identification respects the contragredient action
and every common character twist. Thus the same comparison can be used with the cyclotomic
twist in finite Tate duality. The source module need not be free.

The comparison is the existing `CharacterModule.IsMatlisGenerator.dualEquiv`, bundled as an
equivalence of representations. The underlying linear equivalence retains the existing
naturality and unit-scaling API, so the choice of trace and coefficient maps can be compared
without additional representation-specific formulas.

This file concerns the coefficient representations. Identifying the twisted additive characters
with homomorphisms into roots of unity, and transporting arithmetic cup products, require the
corresponding cyclotomic and cohomological comparisons.

## References

* D. Burns, R. Sakamoto and T. Sano, *On the theory of higher rank Euler, Kolyvagin and Stark
  systems, II*, arXiv:1805.08448v1, §3.1.1 and Theorem 3.1.
-/

public noncomputable section

namespace Representation

variable {R G M : Type*} [CommRing R] [Finite R] [Group G]
  [AddCommGroup M] [Module R M]
  {ℓ : CharacterModule R}

/-- A Matlis trace compares the linear and additive contragredient duals equivariantly,
including any common character twist. -/
def matlisDualEquiv (ρ : Representation R G M) (hℓ : ℓ.IsMatlisGenerator) (χ : G →* Rˣ) :
    (charTwist χ ρ.dual).Equiv (charTwist χ ρ.characterDual) :=
  .mk (hℓ.dualEquiv M) fun g ↦
    (comp_charTwist_eq_charTwist_comp_iff χ _ g).mpr (by
      rw [characterDual_apply, dual_apply]
      exact hℓ.dualEquiv_comp_dualMap (ρ g⁻¹))

/-- The equivariant comparison sends a linear functional to its trace character. -/
@[simp]
theorem matlisDualEquiv_apply (ρ : Representation R G M) (hℓ : ℓ.IsMatlisGenerator)
    (χ : G →* Rˣ) (f : Module.Dual R M) (m : M) :
    ρ.matlisDualEquiv hℓ χ f m = ℓ (f m) :=
  hℓ.dualEquiv_apply f m

/-- The inverse equivariant comparison is the inverse trace comparison on modules. -/
@[simp]
theorem matlisDualEquiv_symm_apply (ρ : Representation R G M) (hℓ : ℓ.IsMatlisGenerator)
    (χ : G →* Rˣ) (η : CharacterModule M) :
    (ρ.matlisDualEquiv hℓ χ).symm η = (hℓ.dualEquiv M).symm η :=
  (rfl)

/-- Forgetting equivariance recovers the module trace comparison, so its naturality and
unit-scaling API apply directly. -/
@[simp]
theorem matlisDualEquiv_toLinearEquiv (ρ : Representation R G M) (hℓ : ℓ.IsMatlisGenerator)
    (χ : G →* Rˣ) :
    (ρ.matlisDualEquiv hℓ χ).toLinearEquiv = hℓ.dualEquiv M :=
  (rfl)

end Representation
