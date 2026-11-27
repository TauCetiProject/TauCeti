/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.Polynomial.Basic
public import Mathlib.FieldTheory.IsSepClosed
public import Mathlib.FieldTheory.KrullTopology
public import TauCeti.AlgebraicGeometry.FiniteEtale.Galois.ModuleSheafStalk
public import TauCeti.FieldTheory.Galois.Basic
public import TauCeti.FieldTheory.Galois.Complex

/-!
# A nonconstant finite lisse `ℤ/3` sheaf on `Spec ℝ`

The quadratic character of `Gal(ℂ/ℝ)`, through which complex conjugation acts by `-1`, makes
`ℤ/3` a representation of `Gal(ℂ/ℝ)`
(`TauCeti.Examples.QuadraticLocalSystem.signRepresentation`). The corresponding étale sheaf of
`ℤ/3`-modules on `Spec ℝ` (`TauCeti.Examples.QuadraticLocalSystem.quadraticLocalSystem`, an
instance of `TauCeti.FiniteEtaleScheme.galoisModuleSheaf`) is finite lisse, because the cover
`Spec ℂ ⟶ Spec ℝ` is finite étale and surjective. It is not constant
(`TauCeti.FiniteEtaleScheme.not_isConstant_galoisModuleSheaf`): its sections over `Spec ℝ`
are the invariants, which vanish
(`TauCeti.Examples.QuadraticLocalSystem.invariants_signRepresentation`), since a vector fixed by
complex conjugation equals its negative and `2` is invertible in `ℤ/3`, so a constant such sheaf
would be zero, while it is nonzero.

Its stalk at the geometric point `Spec ℂ ⟶ Spec ℝ` is `ℤ/3`
(`TauCeti.Examples.QuadraticLocalSystem.etaleStalkQuadraticLocalSystemEquiv`), and complex
conjugation, the nontrivial automorphism of this geometric point, acts on it by `-1`
(`TauCeti.Examples.QuadraticLocalSystem.galoisStalkMap_conjAe_quadraticLocalSystem`).

## Main results

* `TauCeti.Examples.QuadraticLocalSystem.isFiniteLisse_quadraticLocalSystem`: the sheaf is finite
  lisse.
* `TauCeti.Examples.QuadraticLocalSystem.not_isConstant_quadraticLocalSystem`: the sheaf is not
  constant.
* `TauCeti.Examples.QuadraticLocalSystem.etaleStalkQuadraticLocalSystemEquiv` and
  `TauCeti.Examples.QuadraticLocalSystem.galoisStalkMap_conjAe_quadraticLocalSystem`: the stalk at
  `Spec ℂ` is `ℤ/3`, with complex conjugation acting by `-1`.
-/

public section

open CategoryTheory Limits Opposite AlgebraicGeometry FintypeCatDiscrete Complex
  TauCeti.FiniteEtaleScheme ContAction

namespace TauCeti.Examples.QuadraticLocalSystem

/-- The quadratic character of `Gal(ℂ/ℝ)` as a representation on `ℤ/3`: the identity acts
trivially and complex conjugation acts by `-1`. -/
noncomputable def signRepresentation : Representation (ZMod 3) Gal(ℂ/ℝ) (ZMod 3) :=
  (DistribMulAction.toModuleEnd (ZMod 3) (ZMod 3)).comp
    (Algebra.IsQuadraticExtension.quadraticCharacter ℝ ℂ)

/-- Complex conjugation acts on `signRepresentation` by `-1`. -/
theorem signRepresentation_conjAe (m : ZMod 3) : signRepresentation conjAe m = -m := by
  simp [signRepresentation,
    (Algebra.IsQuadraticExtension.quadraticCharacter_eq_neg_one_iff ℝ ℂ).2 TauCeti.conjAe_ne_one]

/-- The étale sheaf of `ℤ/3`-modules on `Spec ℝ` given by the quadratic character of
`Gal(ℂ/ℝ)`. -/
noncomputable def quadraticLocalSystem :
    Sheaf (Scheme.smallEtaleTopology (Spec (.of ℝ))) (ModuleCat.{0} (ZMod 3)) :=
  galoisModuleSheaf ℝ ℂ signRepresentation

/-- **The quadratic local system is finite lisse.** It becomes constant on the finite étale
cover `Spec ℂ ⟶ Spec ℝ`. -/
theorem isFiniteLisse_quadraticLocalSystem : quadraticLocalSystem.IsFiniteLisse :=
  isFiniteLisse_galoisModuleSheaf ℝ ℂ _

/-- `signRepresentation` has no nonzero invariants: an invariant element equals its negative, and
`2` is invertible in `ℤ/3`. -/
theorem invariants_signRepresentation : Representation.invariants signRepresentation = ⊥ := by
  have key : ∀ a : ZMod 3, -a = a → a = 0 := by decide
  refine (Submodule.eq_bot_iff _).2 fun m hm ↦ key m ?_
  exact (signRepresentation_conjAe m).symm.trans ((Representation.mem_invariants _ m).1 hm conjAe)

/-- **The quadratic local system is not constant.** It has no nonzero sections over `Spec ℝ`,
since `signRepresentation` has no nonzero fixed vector, but it is nonzero. -/
theorem not_isConstant_quadraticLocalSystem :
    ¬ quadraticLocalSystem.IsConstant (Scheme.smallEtaleTopology (Spec (.of ℝ))) :=
  not_isConstant_galoisModuleSheaf _ invariants_signRepresentation

/-- **The stalk of the quadratic local system at `Spec ℂ` is `ℤ/3`.** -/
noncomputable def etaleStalkQuadraticLocalSystemEquiv :
    (TauCeti.AlgebraicGeometry.Scheme.etaleStalk (ZMod 3)
      (Spec.map (CommRingCat.ofHom (algebraMap ℝ ℂ)))).obj quadraticLocalSystem ≃ₗ[ZMod 3]
        ZMod 3 :=
  etaleStalkGaloisModuleSheafEquiv ℝ ℂ signRepresentation

/-- **Complex conjugation acts by `-1` on the stalk at `Spec ℂ`** of the quadratic local system. -/
theorem galoisStalkMap_conjAe_quadraticLocalSystem
    (x : (TauCeti.AlgebraicGeometry.Scheme.etaleStalk (ZMod 3)
      (Spec.map (CommRingCat.ofHom (algebraMap ℝ ℂ)))).obj quadraticLocalSystem) :
    (TauCeti.AlgebraicGeometry.Scheme.galoisStalkMap ℝ ℂ (ModuleCat.{0} (ZMod 3)) conjAe).app
      quadraticLocalSystem x = -x := by
  apply etaleStalkQuadraticLocalSystemEquiv.injective
  rw [map_neg]
  exact (etaleStalkGaloisModuleSheafEquiv_galoisStalkMap ℝ ℂ signRepresentation conjAe x).trans
    (signRepresentation_conjAe _)

end TauCeti.Examples.QuadraticLocalSystem
