/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.GroupAction.OrbitRelQuotient
public import TauCeti.GroupTheory.CrossedCocycle.Splitting

/-!
# Restriction of crossed cocycles

For `f : Δ →* Γ`, restriction pulls back both a crossed cocycle and its action along `f`.
Restriction commutes with gauge and coefficient change. For a cocycle presented as a lift into
a semidirect product, the restricted lift is the composite with `f`.

The gauge-orbit quotient is the algebraic nonabelian first cohomology set. Its restriction maps
come from the equivariance of restriction and reuse `MulActionHom.orbitRelQuotientMap`.

## References

* L. Fargues, P. Scholze, *Geometrization of the local Langlands correspondence*, §VIII.1.1.
-/

public section

namespace TauCeti.CrossedCocycle

variable {Γ Δ Θ H : Type*} [Monoid Γ] [Monoid Δ] [Monoid Θ] [Group H]
  {α : Γ →* MulAut H}

/-- Restriction along `f` gives a crossed cocycle for the pulled-back action. -/
def comap (c : CrossedCocycle α) (f : Δ →* Γ) : CrossedCocycle (α.comp f) where
  toFun δ := c (f δ)
  map_mul' δ ε := by simpa only [map_mul, MonoidHom.comp_apply] using c.apply_mul (f δ) (f ε)

@[simp]
theorem comap_apply (c : CrossedCocycle α) (f : Δ →* Γ) (δ : Δ) :
    c.comap f δ = c (f δ) :=
  (rfl)

@[simp]
theorem comap_id (c : CrossedCocycle α) : c.comap (MonoidHom.id Γ) = c :=
  ext fun δ ↦ by simp

@[simp]
theorem comap_comap (c : CrossedCocycle α) (f : Δ →* Γ) (g : Θ →* Δ) :
    (c.comap f).comap g = c.comap (f.comp g) :=
  ext fun δ ↦ by simp

@[simp]
theorem one_comap (f : Δ →* Γ) : (1 : CrossedCocycle α).comap f = 1 :=
  ext fun δ ↦ by simp

@[simp]
theorem comap_one (c : CrossedCocycle α) : c.comap (1 : Δ →* Γ) = 1 :=
  ext fun δ ↦ by simp

@[simp]
theorem comap_smul (c : CrossedCocycle α) (f : Δ →* Γ) (h : H) :
    (h • c).comap f = h • c.comap f :=
  ext fun δ ↦ by simp

/-- Restriction commutes with equivariant change of coefficients. -/
@[simp]
theorem comap_map {K : Type*} [Group K] {β : Γ →* MulAut K} (c : CrossedCocycle α)
    (f : Δ →* Γ) (u : H →* K) (hu : ∀ γ x, u (α γ x) = β γ (u x)) :
    (c.map u hu).comap f = (c.comap f).map u (fun δ x ↦ hu (f δ) x) :=
  ext fun δ ↦ by simp

section SemidirectProduct

variable {Q : Type*} [Group Q] {β : Q →* MulAut H} {η : Γ →* Q}

/-- Restricting a lift of `η` along `f` gives a lift of `η.comp f`. -/
@[simp]
theorem toSemidirectHom_comap (c : CrossedCocycle (β.comp η)) (f : Δ →* Γ) :
    toSemidirectHom (η := η.comp f) (c.comap f) = c.toSemidirectHom.comp f :=
  MonoidHom.ext fun δ ↦ by ext <;> simp

end SemidirectProduct

/-- Algebraic nonabelian first cohomology, the set of gauge orbits of crossed cocycles. -/
abbrev H1 (α : Γ →* MulAut H) : Type _ :=
  MulAction.orbitRel.Quotient H (CrossedCocycle α)

namespace H1

/-- Restriction on gauge classes, induced by restricting each representative. -/
def comap (x : H1 α) (f : Δ →* Γ) : H1 (α.comp f) :=
  MulActionHom.orbitRelQuotientMap
    (σ := id) ⟨fun c ↦ c.comap f, fun h c ↦ comap_smul c f h⟩ x

@[simp]
theorem comap_mk (c : CrossedCocycle α) (f : Δ →* Γ) :
    comap (Quotient.mk'' c) f = Quotient.mk'' (c.comap f) := by
  unfold comap
  exact MulActionHom.orbitRelQuotientMap_mk _ c

@[simp]
theorem comap_id (x : H1 α) : x.comap (MonoidHom.id Γ) = x := by
  refine Quotient.inductionOn' x fun c ↦ ?_
  simp only [comap_mk, CrossedCocycle.comap_id]
  -- The quotient indices agree by definitional reduction of composition with the identity.
  rfl

@[simp]
theorem comap_comap (x : H1 α) (f : Δ →* Γ) (g : Θ →* Δ) :
    (x.comap f).comap g = x.comap (f.comp g) := by
  refine Quotient.inductionOn' x fun c ↦ ?_
  simp only [comap_mk, CrossedCocycle.comap_comap]
  -- Composition of the action homomorphisms in the quotient indices is definitionally associative.
  rfl

end H1

end TauCeti.CrossedCocycle
