/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.UniversalEnveloping.PBW.Center
public import TauCeti.Algebra.Lie.UniversalEnveloping.PBW.Symmetrization.Equivariance

/-!
# Symmetrization identifies the Lie invariants with the centre

Let `L` be a Lie algebra over a commutative `ℚ`-algebra `R`. PBW symmetrization
`Sym_R(L) ≃ₗ[R] U_R(L)` (`TauCeti.UniversalEnvelopingAlgebra.pbwSymmetrizationEquiv`) intertwines
the adjoint actions, so an element of `Sym(L)` is a Lie invariant exactly when its symmetrization
is central (`TauCeti.UniversalEnvelopingAlgebra.pbwSymmetrizationMap_mem_center_iff`). This file
restricts symmetrization to a **linear** equivalence

`Sym(L)^L ≃ₗ[R] Z(U(L))`

(`TauCeti.UniversalEnvelopingAlgebra.lieInvariantsCenterEquiv`). It averages each product of `m`
generators over all orders with weight `1/m!`, and it carries the word-degree filtration of the
invariants onto the PBW filtration of the centre
(`TauCeti.UniversalEnvelopingAlgebra.lieInvariantsCenterEquiv_mem_centerPBWFiltration_iff`). It is
a linear equivalence only: it is not claimed to be multiplicative on invariant tensors. Compare the
graded identification of the PBW symbols of central elements with the homogeneous invariants
(`TauCeti.UniversalEnvelopingAlgebra.centerPBWGradedInvariantIso`, for free `L`).

No freeness of `L` over `R` is needed, since the symmetrization equivalence exists for every Lie
algebra over a commutative `ℚ`-algebra.

## Main definitions and results

* `TauCeti.UniversalEnvelopingAlgebra.lieInvariantsCenterEquiv`: the linear equivalence
  `Sym(L)^L ≃ₗ[R] Z(U(L))` given by symmetrization.
* `TauCeti.UniversalEnvelopingAlgebra.coe_lieInvariantsCenterEquiv_prod_ι`: the averaging formula.
* `TauCeti.UniversalEnvelopingAlgebra.lieInvariantsCenterEquiv_mem_centerPBWFiltration_iff`: an
  invariant has degree at most `k` exactly when its symmetrization has PBW degree at most `k`.

## References

* J. Dixmier, *Enveloping Algebras*, §2.4.
-/

public section

namespace TauCeti.UniversalEnvelopingAlgebra

open TauCeti.SymmetricAlgebra

universe u v

variable (R : Type u) (L : Type v) [CommRing R] [Algebra ℚ R] [LieRing L] [LieAlgebra R L]

attribute [local instance 100] LieRing.ofAssociativeRing

local notation "U" => _root_.UniversalEnvelopingAlgebra R L
local notation "F" => TauCeti.Algebra.wordFiltration (SymmetricAlgebra.ι R L)

/-- **Symmetrization identifies the Lie invariants with the centre**, as `R`-modules: PBW
symmetrization restricts to a linear equivalence `Sym(L)^L ≃ₗ[R] Z(U(L))`. It is not
multiplicative in general. -/
noncomputable def lieInvariantsCenterEquiv :
    lieInvariants R L L ≃ₗ[R] Subalgebra.center R U :=
  (pbwSymmetrizationEquiv R L).ofSubmodules (Subalgebra.toSubmodule (lieInvariants R L L))
    (Subalgebra.toSubmodule (Subalgebra.center R U)) <| by
      ext z
      rw [Submodule.mem_map_equiv, Subalgebra.mem_toSubmodule, Subalgebra.mem_toSubmodule,
        ← pbwSymmetrizationMap_mem_center_iff, ← pbwSymmetrizationEquiv_apply,
        LinearEquiv.apply_symm_apply]

/-- The equivalence `Sym(L)^L ≃ₗ[R] Z(U(L))` is symmetrization. -/
@[simp]
theorem coe_lieInvariantsCenterEquiv_apply (p : lieInvariants R L L) :
    (lieInvariantsCenterEquiv R L p : U) = pbwSymmetrizationMap R L p :=
  (LinearEquiv.ofSubmodules_apply _ _ _).trans (pbwSymmetrizationEquiv_apply R L _)

/-- The inverse of `Sym(L)^L ≃ₗ[R] Z(U(L))` is the inverse of symmetrization. -/
@[simp]
theorem coe_lieInvariantsCenterEquiv_symm_apply (z : Subalgebra.center R U) :
    ((lieInvariantsCenterEquiv R L).symm z : SymmetricAlgebra R L) =
      (pbwSymmetrizationEquiv R L).symm z :=
  LinearEquiv.ofSubmodules_symm_apply _ _ _

/-- **The averaging formula**: on an invariant written as a product of `m` generators, the
equivalence is `1/m!` times the sum of the products in all `m!` orders. -/
theorem coe_lieInvariantsCenterEquiv_prod_ι (m : ℕ) (x : Fin m → L)
    (hx : ∏ j, SymmetricAlgebra.ι R L (x j) ∈ lieInvariants R L L) :
    (lieInvariantsCenterEquiv R L ⟨_, hx⟩ : U) =
      algebraMap ℚ R (m.factorial : ℚ)⁻¹ • ∑ σ : Equiv.Perm (Fin m),
        (List.ofFn fun j ↦ _root_.UniversalEnvelopingAlgebra.ι R (x (σ j))).prod := by
  rw [coe_lieInvariantsCenterEquiv_apply]
  exact pbwSymmetrizationMap_prod_ι R L m x

/-- The equivalence sends `1` to `1`. -/
@[simp]
theorem lieInvariantsCenterEquiv_one : lieInvariantsCenterEquiv R L 1 = 1 :=
  Subtype.ext ((coe_lieInvariantsCenterEquiv_apply R L 1).trans (pbwSymmetrizationMap_one R L))

/-- **The equivalence is filtered in both directions**: an invariant has word degree at most `k`
exactly when its symmetrization lies in the `k`-th step of the PBW filtration of the centre. -/
theorem lieInvariantsCenterEquiv_mem_centerPBWFiltration_iff {k : ℕ} {p : lieInvariants R L L} :
    lieInvariantsCenterEquiv R L p ∈ centerPBWFiltration R L k ↔
      (p : SymmetricAlgebra R L) ∈ F k := by
  rw [mem_centerPBWFiltration, coe_lieInvariantsCenterEquiv_apply,
    pbwSymmetrizationMap_mem_pbwFiltration_iff]

/-- The inverse equivalence is filtered: a central element has PBW degree at most `k` exactly when
the invariant it comes from has word degree at most `k`. -/
theorem coe_lieInvariantsCenterEquiv_symm_mem_wordFiltration_iff {k : ℕ}
    {z : Subalgebra.center R U} :
    ((lieInvariantsCenterEquiv R L).symm z : SymmetricAlgebra R L) ∈ F k ↔
      z ∈ centerPBWFiltration R L k := by
  rw [← lieInvariantsCenterEquiv_mem_centerPBWFiltration_iff, LinearEquiv.apply_symm_apply]

end TauCeti.UniversalEnvelopingAlgebra
