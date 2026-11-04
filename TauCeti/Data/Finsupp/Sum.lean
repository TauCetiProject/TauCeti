/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Finsupp.Basic

/-!
# Finitely supported functions on disjoint unions

`Finsupp.sumElim_inj` characterizes equality of finitely supported functions obtained by
joining functions on two disjoint domains, and `Finsupp.mapDomain_sumElim` pushes a joined
function forward along `Sum.elim`.
-/

public section

namespace Finsupp

/-- Joining finitely supported functions on disjoint domains is injective in both arguments. -/
@[simp]
theorem sumElim_inj {α β γ : Type*} [Zero γ] {a a' : α →₀ γ} {b b' : β →₀ γ} :
    a.sumElim b = a'.sumElim b' ↔ a = a' ∧ b = b' := by
  simpa only [sumFinsuppEquivProdFinsupp_symm_apply] using
    (sumFinsuppEquivProdFinsupp.symm.injective.eq_iff
      (a := (a, b)) (b := (a', b'))).trans Prod.ext_iff

/-- Pushing forward a joined finitely supported function along `Sum.elim f g` adds the pushforwards
of its two parts. -/
@[simp]
theorem mapDomain_sumElim {α β γ M : Type*} [AddCommMonoid M] (f : α → γ) (g : β → γ)
    (a : α →₀ M) (b : β →₀ M) :
    mapDomain (Sum.elim f g) (a.sumElim b) = mapDomain f a + mapDomain g b := by
  simp [sumElim_eq_add, mapDomain_add, ← mapDomain_comp]

end Finsupp
