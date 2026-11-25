/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Meromorphic.ZeroFree
public import TauCeti.NumberTheory.DirichletCharacter.LFunction.ChangeLevel
public import TauCeti.NumberTheory.DirichletCharacter.Primitive.CyclicFamily

/-!
# Zero-free half-planes and cyclic families of Dirichlet characters

Raising the level adds Euler factors but does not change the orders in `0 < Re(s)`. Thus
zero-freeness at one modulus can be tested just on primitive characters of conductors dividing
that modulus. Over all moduli it can equivalently be tested on the cyclic families of primitive
characters. This lets a bound proved separately for each such family yield a statement about
all characters, including imprimitive ones.

The reduction at the Riemann hypothesis threshold corresponds to Levent Alpöge's
`Formalism.HC.zeroFreeOn_of_levels` in `ExplicitFormulaErrorOfHostConditions.lean` and
`UpperTheory.Top.imprimitive` in `Imprimitive.lean` in the [published formalization][alpoege].

[alpoege]: https://github.com/leanprover-community/riemann-hypothesis/tree/40e56bab026552e089d7afcfeff08d2defb9c005
-/

public section

open TauCeti

namespace DirichletCharacter

/-- For a nonnegative threshold, lifting a character to a multiple of its level preserves
zero-freeness to the right of that threshold. The pole of a principal character is allowed. -/
@[simp]
theorem zeroFreeRightOf_LFunction_changeLevel_iff {M N : ℕ} [NeZero M] [NeZero N]
    (χ : DirichletCharacter ℂ M) (hMN : M ∣ N) {σ : ℝ} (hσ : 0 ≤ σ) :
    ZeroFreeRightOf σ (changeLevel hMN χ).LFunction ↔ ZeroFreeRightOf σ χ.LFunction := by
  simp only [zeroFreeRightOf_iff]
  exact forall₂_congr fun _ hs ↦ by
    rw [χ.meromorphicOrderAt_LFunction_changeLevel hMN (hσ.trans_lt hs)]

end DirichletCharacter

namespace TauCeti

open DirichletCharacter

/-- Zero-freeness for all characters modulo `N` is equivalent to zero-freeness for the primitive
characters whose conductors divide `N`. -/
theorem forall_zeroFreeRightOf_LFunction_iff_forall_level_dvd {N : ℕ} [NeZero N] {σ : ℝ}
    (hσ : 0 ≤ σ) :
    (∀ χ : DirichletCharacter ℂ N, ZeroFreeRightOf σ χ.LFunction) ↔
      ∀ ψ : PrimitiveDirichletCharacter, (ψ.level : ℕ) ∣ N →
        ZeroFreeRightOf σ ψ.character.LFunction := by
  refine ⟨fun h ψ hψ ↦ ?_, fun h χ ↦ ?_⟩
  · exact (ψ.character.zeroFreeRightOf_LFunction_changeLevel_iff hψ hσ).mp (h _)
  · let ψ := PrimitiveDirichletCharacter.of χ
    have hd : (ψ.level : ℕ) ∣ N := PrimitiveDirichletCharacter.level_of_dvd χ
    simpa only [ψ, PrimitiveDirichletCharacter.changeLevel_character_of] using
      (ψ.character.zeroFreeRightOf_LFunction_changeLevel_iff hd hσ).mpr (h ψ hd)

/-- To rule out zeros to the right of a nonnegative threshold for all Dirichlet characters,
it suffices and is necessary to do so for every member of every primitive cyclic family.
At threshold `1/2` this is the cyclic-family reduction of the generalized Riemann hypothesis. -/
theorem forall_zeroFreeRightOf_LFunction_iff_forall_mem_cyclicFamily {σ : ℝ} (hσ : 0 ≤ σ) :
    (∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N), ZeroFreeRightOf σ χ.LFunction) ↔
      ∀ ψ : PrimitiveDirichletCharacter, ∀ κ ∈ ψ.cyclicFamily,
        ZeroFreeRightOf σ κ.character.LFunction := by
  refine ⟨fun h _ κ _ ↦ h κ.level κ.character, fun h N _ ↦ ?_⟩
  exact (forall_zeroFreeRightOf_LFunction_iff_forall_level_dvd hσ).mpr fun ψ _ ↦
    h ψ ψ ψ.mem_cyclicFamily_self

end TauCeti
