/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.UniversalEnveloping.PBW.Symmetrization.Coalgebra
public import TauCeti.Algebra.Lie.UniversalEnveloping.PBW.Symmetrization.Injective
public import Mathlib.RingTheory.Coalgebra.Equiv

/-!
# The PBW symmetrization equivalence

For an arbitrary Lie algebra `L` over a commutative `ℚ`-algebra `R`, the symmetrization
`Sym_R(L) → U_R(L)` is a linear equivalence and an equivalence of coalgebras, and it is filtered:
it carries the word-degree filtration of `Sym_R(L)` onto the PBW filtration of `U_R(L)`. Together
with `TauCeti.UniversalEnvelopingAlgebra.pbwSymmetrizationMap_injective` this is the
Poincaré–Birkhoff–Witt theorem over `ℚ`-algebras in its symmetrization form, with no freeness or
flatness assumption on `L`. The scalar ring and the Lie algebra may lie in independent universes.

## Main definitions and results

* `TauCeti.UniversalEnvelopingAlgebra.pbwSymmetrizationEquiv`: the linear equivalence.
* `TauCeti.UniversalEnvelopingAlgebra.pbwSymmetrizationCoalgEquiv`: the coalgebra equivalence.
* `TauCeti.UniversalEnvelopingAlgebra.pbwSymmetrizationEquiv_prod_ι`: the symmetrization formula.
* `TauCeti.UniversalEnvelopingAlgebra.map_wordFiltration_pbwSymmetrizationEquiv`: filteredness.
* `TauCeti.UniversalEnvelopingAlgebra.exists_pbwSymmetrizationEquiv`: the existence statement.

## References

* F. Petracci, *Universal representations of Lie algebras by coderivations*
  (arXiv:math/0303020), Corollary 8.1.
-/

public section

namespace TauCeti.UniversalEnvelopingAlgebra

open TauCeti.SymmetricAlgebra

universe u v

variable (R : Type u) (L : Type v) [CommRing R] [Algebra ℚ R] [LieRing L] [LieAlgebra R L]

attribute [local instance 100] LieRing.ofAssociativeRing

local notation "U" => _root_.UniversalEnvelopingAlgebra R L
local notation "F" => TauCeti.Algebra.wordFiltration (SymmetricAlgebra.ι R L)

/-- PBW symmetrization is bijective for every Lie algebra over a commutative `ℚ`-algebra. -/
theorem pbwSymmetrizationMap_bijective : Function.Bijective (pbwSymmetrizationMap R L) :=
  ⟨pbwSymmetrizationMap_injective R L, pbwSymmetrizationMap_surjective R L⟩

/-- The **PBW symmetrization equivalence** `Sym_R(L) ≃ₗ[R] U_R(L)`. -/
noncomputable def pbwSymmetrizationEquiv : SymmetricAlgebra R L ≃ₗ[R] U :=
  LinearEquiv.ofBijective (pbwSymmetrizationMap R L) (pbwSymmetrizationMap_bijective R L)

/-- The underlying map of `pbwSymmetrizationEquiv` is `pbwSymmetrizationMap`. -/
@[simp]
theorem pbwSymmetrizationEquiv_apply (p : SymmetricAlgebra R L) :
    pbwSymmetrizationEquiv R L p = pbwSymmetrizationMap R L p := (rfl)

/-- The symmetrization equivalence sends a product of `d` elements to `1/d!` times the sum of their
products in all orders. -/
theorem pbwSymmetrizationEquiv_prod_ι (d : ℕ) (x : Fin d → L) :
    pbwSymmetrizationEquiv R L (∏ j, SymmetricAlgebra.ι R L (x j)) =
      algebraMap ℚ R (d.factorial : ℚ)⁻¹ • ∑ σ : Equiv.Perm (Fin d),
        (List.ofFn fun j => UniversalEnvelopingAlgebra.ι R (x (σ j))).prod :=
  pbwSymmetrizationMap_prod_ι R L d x

/-- The symmetrization equivalence is an equivalence of coalgebras. -/
noncomputable def pbwSymmetrizationCoalgEquiv : CoalgEquiv R (SymmetricAlgebra R L) U :=
  CoalgEquiv.ofBijective (f := pbwSymmetrizationCoalgHom R L)
    (by
      have : ⇑(pbwSymmetrizationCoalgHom R L) = ⇑(pbwSymmetrizationMap R L) :=
        funext (pbwSymmetrizationCoalgHom_apply R L)
      rw [this]
      exact pbwSymmetrizationMap_bijective R L)

/-- The underlying map of `pbwSymmetrizationCoalgEquiv` is `pbwSymmetrizationMap`. -/
@[simp]
theorem pbwSymmetrizationCoalgEquiv_apply (p : SymmetricAlgebra R L) :
    pbwSymmetrizationCoalgEquiv R L p = pbwSymmetrizationMap R L p := by
  simp [pbwSymmetrizationCoalgEquiv]

/-- An element of the symmetric algebra has word degree at most `k` exactly when its symmetrization
has PBW degree at most `k`. -/
@[simp]
theorem pbwSymmetrizationMap_mem_pbwFiltration_iff {k : ℕ} {p : SymmetricAlgebra R L} :
    pbwSymmetrizationMap R L p ∈ pbwFiltration R L k ↔ p ∈ F k := by
  refine ⟨fun h => ?_, pbwSymmetrizationMap_mem_pbwFiltration R L⟩
  obtain ⟨q, hq, hqp⟩ := exists_pbwSymmetrizationMap_eq_of_mem R L h
  rwa [← pbwSymmetrizationMap_injective R L hqp]

/-- The symmetrization equivalence is filtered: it carries each word-degree step of the symmetric
algebra onto the corresponding PBW step. -/
theorem map_wordFiltration_pbwSymmetrizationEquiv (k : ℕ) :
    (F k).map (pbwSymmetrizationEquiv R L).toLinearMap = pbwFiltration R L k :=
  map_wordFiltration_pbwSymmetrizationMap R L k

/-- **Symmetrization PBW over commutative `ℚ`-algebras** (Petracci): for an arbitrary Lie algebra
`L` over a commutative `ℚ`-algebra `R`, there is a linear equivalence `Sym_R(L) ≃ U_R(L)` sending a
product of `d` elements to `1/d!` times the sum of their products in all orders. -/
theorem exists_pbwSymmetrizationEquiv :
    ∃ β : SymmetricAlgebra R L ≃ₗ[R] U,
      ∀ (d : ℕ) (x : Fin d → L),
        β (∏ j, SymmetricAlgebra.ι R L (x j)) =
          algebraMap ℚ R (d.factorial : ℚ)⁻¹ • ∑ σ : Equiv.Perm (Fin d),
            (List.ofFn fun j => UniversalEnvelopingAlgebra.ι R (x (σ j))).prod :=
  ⟨pbwSymmetrizationEquiv R L, pbwSymmetrizationEquiv_prod_ι R L⟩

end TauCeti.UniversalEnvelopingAlgebra
