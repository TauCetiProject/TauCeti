/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.GroupAction.OrbitRelQuotient
public import TauCeti.GroupTheory.CrossedCocycle.Basic

/-!
# Restriction of crossed cocycle gauge classes

The gauge-orbit quotient is the algebraic nonabelian first cohomology set. Its restriction maps
come from the equivariance of restriction and reuse `MulActionHom.orbitRelQuotientMap`.

## References

* L. Fargues, P. Scholze, *Geometrization of the local Langlands correspondence*, §VIII.1.1.
-/

public section

namespace TauCeti.CrossedCocycle

variable {Γ Δ Θ H : Type*} [Monoid Γ] [Monoid Δ] [Monoid Θ] [Group H]
  {α : Γ →* MulAut H}

namespace GaugeClass

/-- Restriction on gauge classes, induced by restricting each representative. -/
def comap (x : GaugeClass α) (f : Δ →* Γ) : GaugeClass (α.comp f) :=
  MulActionHom.orbitRelQuotientMap
    (σ := id) ⟨fun c ↦ c.comap f, fun h c ↦ comap_smul c f h⟩ x

@[simp]
theorem comap_mk (c : CrossedCocycle α) (f : Δ →* Γ) :
    comap (Quotient.mk'' c) f = Quotient.mk'' (c.comap f) := by
  unfold comap
  exact MulActionHom.orbitRelQuotientMap_mk _ c

@[simp]
theorem comap_id (x : GaugeClass α) : x.comap (MonoidHom.id Γ) = x := by
  refine Quotient.inductionOn' x fun c ↦ ?_
  simp only [comap_mk, CrossedCocycle.comap_id]
  -- The quotient indices agree by definitional reduction of composition with the identity.
  rfl

@[simp]
theorem comap_comap (x : GaugeClass α) (f : Δ →* Γ) (g : Θ →* Δ) :
    (x.comap f).comap g = x.comap (f.comp g) := by
  refine Quotient.inductionOn' x fun c ↦ ?_
  simp only [comap_mk, CrossedCocycle.comap_comap]
  -- Composition of the action homomorphisms in the quotient indices is definitionally associative.
  rfl

end GaugeClass

end TauCeti.CrossedCocycle
