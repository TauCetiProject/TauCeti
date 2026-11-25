/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.UniversalEnveloping.InfinitesimalCharacter

/-!
# Modules with an infinitesimal character

Let `M` be a module over a Lie algebra `L` over a commutative ring `R`, and `Z = Z(U(L))` the
centre of the universal enveloping algebra. For an algebra character `χ : Z →ₐ[R] R`, the module
**has infinitesimal character `χ`** (`TauCeti.UniversalEnvelopingAlgebra.HasInfinitesimalCharacter`)
when every `z ∈ Z` acts on it by the scalar `χ z`; equivalently the centre eigenspace
`centerEigenspace R L M χ` is everything.

The predicate is preserved by homomorphisms of Lie modules: it passes to Lie submodules and
quotients, and more generally along injective and surjective homomorphisms. It implies generalized
`χ`-finiteness, and the dual module has infinitesimal character `dualCharacter χ`. The zero module
has every infinitesimal character, so uniqueness of the infinitesimal character needs a nonzero
module (`HasInfinitesimalCharacter.eq`, for a module without `R`-torsion).

If `L` acts on `M` through a Lie algebra homomorphism `f : L → R`, that is `⁅y, m⁆ = f y • m`,
then every `u ∈ U(L)` acts by the scalar `lift f u` (`representation_apply_of_lie_eq_smul`), so `M`
has the infinitesimal character `liftCharacter R L f` extending `f`
(`HasInfinitesimalCharacter.of_lie_eq_smul`); the trivial module is the case `f = 0`. The values
of these characters on the trace-form Casimir of `gl n` are computed in
`TauCeti/Algebra/Lie/GeneralLinear/InfinitesimalCharacter.lean`.

## Main definitions

* `TauCeti.UniversalEnvelopingAlgebra.HasInfinitesimalCharacter`: every central element acts by
  the scalar `χ z`.

## Main results

* `TauCeti.UniversalEnvelopingAlgebra.hasInfinitesimalCharacter_iff`,
  `TauCeti.UniversalEnvelopingAlgebra.HasInfinitesimalCharacter.apply`: the defining property.
* `TauCeti.UniversalEnvelopingAlgebra.hasInfinitesimalCharacter_iff_centerEigenspace_eq_top`.
* `TauCeti.UniversalEnvelopingAlgebra.HasInfinitesimalCharacter.of_injective`, `.of_surjective`,
  `.lieSubmodule`, `.quotient`: invariance under homomorphisms of Lie modules.
* `TauCeti.UniversalEnvelopingAlgebra.HasInfinitesimalCharacter.eq`: uniqueness for a nonzero
  torsion-free module.
* `TauCeti.UniversalEnvelopingAlgebra.representation_apply_of_lie_eq_smul`,
  `TauCeti.UniversalEnvelopingAlgebra.HasInfinitesimalCharacter.of_lie_eq_smul`,
  `TauCeti.UniversalEnvelopingAlgebra.hasInfinitesimalCharacter_of_isTrivial`: modules on which
  `L` acts through a character.

## References

* J. Bernstein and B. Krötz, *Smooth Fréchet globalizations of Harish-Chandra modules*, Israel J.
  Math. **199** (2014), §4.1.
-/

public section

namespace TauCeti.UniversalEnvelopingAlgebra

open Module

universe u v w x

variable (R : Type u) (L : Type v) (M : Type w) {N : Type x}
variable [CommRing R] [LieRing L] [LieAlgebra R L]
  [AddCommGroup M] [Module R M] [LieRingModule L M] [LieModule R L M]
  [AddCommGroup N] [Module R N] [LieRingModule L N] [LieModule R L N]

local notation "U" => _root_.UniversalEnvelopingAlgebra R L

/-- A Lie module **has infinitesimal character** `χ` when every element `z` of the centre of the
universal enveloping algebra acts by the scalar `χ z`. -/
def HasInfinitesimalCharacter (χ : Subalgebra.center R U →ₐ[R] R) : Prop :=
  ∀ (z : Subalgebra.center R U) (m : M), centralAction R L M z m = χ z • m

variable {R L M}

/-- The defining property of a module with infinitesimal character `χ`. -/
theorem hasInfinitesimalCharacter_iff {χ : Subalgebra.center R U →ₐ[R] R} :
    HasInfinitesimalCharacter R L M χ ↔
      ∀ (z : Subalgebra.center R U) (m : M), centralAction R L M z m = χ z • m :=
  Iff.rfl

/-- A central element acts on a module with infinitesimal character `χ` by the scalar `χ z`. -/
theorem HasInfinitesimalCharacter.apply {χ : Subalgebra.center R U →ₐ[R] R}
    (h : HasInfinitesimalCharacter R L M χ) (z : Subalgebra.center R U) (m : M) :
    centralAction R L M z m = χ z • m :=
  hasInfinitesimalCharacter_iff.mp h z m

/-- A module has infinitesimal character `χ` if and only if its centre eigenspace for `χ` is the
whole module. -/
theorem hasInfinitesimalCharacter_iff_centerEigenspace_eq_top
    {χ : Subalgebra.center R U →ₐ[R] R} :
    HasInfinitesimalCharacter R L M χ ↔ centerEigenspace R L M χ = ⊤ := by
  rw [centerEigenspace_eq_top_iff, hasInfinitesimalCharacter_iff]
  simp only [centralAction_apply]

/-- The zero module has every infinitesimal character. -/
theorem hasInfinitesimalCharacter_of_subsingleton [Subsingleton M]
    (χ : Subalgebra.center R U →ₐ[R] R) : HasInfinitesimalCharacter R L M χ :=
  hasInfinitesimalCharacter_iff.mpr fun _ _ ↦ Subsingleton.elim _ _

section LiftCharacter

attribute [local instance 100] LieRing.ofAssociativeRing

/-- **On a module where `L` acts through a character `f`, every element `u` of `U(L)` acts by the
scalar `lift f u`.** -/
theorem representation_apply_of_lie_eq_smul (f : LieAlgebra.LieCharacter R L)
    (hf : ∀ (y : L) (m : M), ⁅y, m⁆ = f y • m) (u : U) (m : M) :
    representation R L M u m = _root_.UniversalEnvelopingAlgebra.lift R f u • m := by
  have key : representation R L M =
      (Algebra.ofId R (End R M)).comp (_root_.UniversalEnvelopingAlgebra.lift R f) := by
    refine _root_.UniversalEnvelopingAlgebra.hom_ext R
      (LieHom.ext fun y ↦ LinearMap.ext fun m ↦ ?_)
    simp [hf, Algebra.ofId_apply, Algebra.algebraMap_eq_smul_one]
  simp [key, Algebra.ofId_apply, Algebra.algebraMap_eq_smul_one]

end LiftCharacter

namespace HasInfinitesimalCharacter

/-- **Uniqueness of the infinitesimal character** of a nonzero torsion-free module. -/
theorem eq {χ : Subalgebra.center R U →ₐ[R] R}
    [IsDomain R] [Module.IsTorsionFree R M] [Nontrivial M] {χ' : Subalgebra.center R U →ₐ[R] R}
    (h : HasInfinitesimalCharacter R L M χ) (h' : HasInfinitesimalCharacter R L M χ') :
    χ = χ' := by
  obtain ⟨m, hm⟩ := exists_ne (0 : M)
  ext z
  have := (h.apply z m).symm.trans (h'.apply z m)
  rw [← sub_eq_zero, ← sub_smul, smul_eq_zero, sub_eq_zero] at this
  exact this.resolve_right hm

/-- An infinitesimal character is a generalized one. -/
theorem isGeneralizedCharacterFinite {χ : Subalgebra.center R U →ₐ[R] R}
    (h : HasInfinitesimalCharacter R L M χ) :
    IsGeneralizedCharacterFinite R L M χ :=
  isGeneralizedCharacterFinite_of_centerEigenspace_eq_top
    (hasInfinitesimalCharacter_iff_centerEigenspace_eq_top.mp h)

/-- The infinitesimal character passes along injective homomorphisms of Lie modules. -/
theorem of_injective {χ : Subalgebra.center R U →ₐ[R] R}
    (f : M →ₗ⁅R,L⁆ N) (hf : Function.Injective f)
    (h : HasInfinitesimalCharacter R L N χ) : HasInfinitesimalCharacter R L M χ :=
  hasInfinitesimalCharacter_iff.mpr fun z m ↦ hf (by rw [map_centralAction, h.apply, map_smul])

/-- The infinitesimal character passes along surjective homomorphisms of Lie modules. -/
theorem of_surjective {χ : Subalgebra.center R U →ₐ[R] R}
    (f : M →ₗ⁅R,L⁆ N) (hf : Function.Surjective f)
    (h : HasInfinitesimalCharacter R L M χ) : HasInfinitesimalCharacter R L N χ :=
  hasInfinitesimalCharacter_iff.mpr fun z n ↦ by
    obtain ⟨m, rfl⟩ := hf n
    rw [← map_centralAction, h.apply, map_smul]

/-- A Lie submodule has the infinitesimal character of the module. -/
theorem lieSubmodule {χ : Subalgebra.center R U →ₐ[R] R}
    (h : HasInfinitesimalCharacter R L M χ) (N' : LieSubmodule R L M) :
    HasInfinitesimalCharacter R L N' χ :=
  h.of_injective N'.incl Subtype.val_injective

/-- A quotient has the infinitesimal character of the module. -/
theorem quotient {χ : Subalgebra.center R U →ₐ[R] R}
    (h : HasInfinitesimalCharacter R L M χ) (N' : LieSubmodule R L M) :
    HasInfinitesimalCharacter R L (M ⧸ N') χ :=
  h.of_surjective (LieSubmodule.Quotient.mk' N') (LieSubmodule.Quotient.surjective_mk' N')

/-- The dual of a module with infinitesimal character `χ` has infinitesimal character
`dualCharacter χ`. -/
theorem dual {χ : Subalgebra.center R U →ₐ[R] R}
    (h : HasInfinitesimalCharacter R L M χ) :
    HasInfinitesimalCharacter R L (Dual R M) (dualCharacter χ) :=
  hasInfinitesimalCharacter_iff_centerEigenspace_eq_top.mpr
    (centerEigenspace_dual_eq_top (hasInfinitesimalCharacter_iff_centerEigenspace_eq_top.mp h))

/-- **A module on which `L` acts through a character `f` has infinitesimal character
`liftCharacter R L f`.** A central element `z` acts by the scalar `liftCharacter R L f z`. -/
theorem of_lie_eq_smul (f : LieAlgebra.LieCharacter R L)
    (hf : ∀ (y : L) (m : M), ⁅y, m⁆ = f y • m) :
    HasInfinitesimalCharacter R L M (liftCharacter R L f) :=
  hasInfinitesimalCharacter_iff.mpr fun z m ↦ by
    rw [centralAction_apply, liftCharacter_apply, representation_apply_of_lie_eq_smul f hf]

end HasInfinitesimalCharacter

/-- **The trivial module has infinitesimal character `liftCharacter R L 0`.** -/
theorem hasInfinitesimalCharacter_of_isTrivial [LieModule.IsTrivial L M] :
    HasInfinitesimalCharacter R L M (liftCharacter R L 0) :=
  HasInfinitesimalCharacter.of_lie_eq_smul 0 fun y m ↦ by simp [trivial_lie_zero]

end TauCeti.UniversalEnvelopingAlgebra
