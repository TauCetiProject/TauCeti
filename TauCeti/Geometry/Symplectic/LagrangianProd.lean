/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.Geometry.Symplectic.Lagrangian
public import TauCeti.Geometry.Symplectic.Prod

/-!
# Products of Lagrangian subspaces

The direct-sum symplectic form `ω₁.prod ω₂` on `V × W` has the expected product
orthogonal-complement formula:

`(L₁ × L₂)^(ω₁ ⊕ ω₂) = L₁^ω₁ × L₂^ω₂`.

This file records that linear-algebra calculation and the resulting product rules for
isotropic, coisotropic, and Lagrangian subspaces. These are the pointwise product-boundary
facts used by the analytic Heegaard Floer roadmap before forming product Lagrangians and the
totally real tori that later live inside symmetric products.

## Main declarations

* `TauCeti.SymplecticForm.orthogonal_prod`: the symplectic complement of a product subspace.
* `TauCeti.SymplecticForm.isIsotropic_prod_iff`: product isotropy is factorwise isotropy.
* `TauCeti.SymplecticForm.isCoisotropic_prod_iff`: product coisotropy is factorwise coisotropy.
* `TauCeti.SymplecticForm.isLagrangian_prod_iff`: product Lagrangian-ness is factorwise
  Lagrangian-ness.
* `TauCeti.SymplecticForm.IsLagrangian.prod`: a product of Lagrangian subspaces is Lagrangian.

The conventions follow McDuff--Salamon, *J-holomorphic Curves and Symplectic Topology*,
Section 2.3.
-/

public section

namespace TauCeti

namespace SymplecticForm

variable {V W : Type*} [AddCommGroup V] [Module ℝ V] [AddCommGroup W] [Module ℝ W]
variable {ω₁ : SymplecticForm V} {ω₂ : SymplecticForm W}
variable {L₁ : Submodule ℝ V} {L₂ : Submodule ℝ W}

/-- The symplectic complement of a product subspace is the product of the symplectic
complements for the direct-sum symplectic form. -/
@[simp]
lemma orthogonal_prod :
    (ω₁.prod ω₂).orthogonal (L₁.prod L₂) = (ω₁.orthogonal L₁).prod (ω₂.orthogonal L₂) := by
  ext x
  rw [mem_orthogonal_iff, Submodule.mem_prod, mem_orthogonal_iff, mem_orthogonal_iff]
  constructor
  · intro h
    constructor
    · intro y hy
      have := h (y, 0) (Submodule.mem_prod.2 ⟨hy, Submodule.zero_mem L₂⟩)
      simpa using this
    · intro y hy
      have := h (0, y) (Submodule.mem_prod.2 ⟨Submodule.zero_mem L₁, hy⟩)
      simpa using this
  · rintro ⟨h₁, h₂⟩ y hy
    rw [SymplecticForm.prod_apply]
    rw [h₁ y.1 hy.1, h₂ y.2 hy.2, add_zero]

/-- A product subspace is isotropic for the direct-sum symplectic form exactly when both factors
are isotropic. -/
@[simp]
lemma isIsotropic_prod_iff :
    (ω₁.prod ω₂).IsIsotropic (L₁.prod L₂) ↔ ω₁.IsIsotropic L₁ ∧ ω₂.IsIsotropic L₂ := by
  rw [isIsotropic_iff, isIsotropic_iff, isIsotropic_iff]
  constructor
  · intro h
    constructor
    · intro x hx y hy
      have := h (x, 0) (Submodule.mem_prod.2 ⟨hx, Submodule.zero_mem L₂⟩)
        (y, 0) (Submodule.mem_prod.2 ⟨hy, Submodule.zero_mem L₂⟩)
      simpa using this
    · intro y hy z hz
      have := h (0, y) (Submodule.mem_prod.2 ⟨Submodule.zero_mem L₁, hy⟩)
        (0, z) (Submodule.mem_prod.2 ⟨Submodule.zero_mem L₁, hz⟩)
      simpa using this
  · rintro ⟨h₁, h₂⟩ x hx
    intro y hy
    rw [SymplecticForm.prod_apply, h₁ x.1 hx.1 y.1 hy.1, h₂ x.2 hx.2 y.2 hy.2, add_zero]

/-- The product of two isotropic subspaces is isotropic for the direct-sum symplectic form. -/
lemma IsIsotropic.prod (h₁ : ω₁.IsIsotropic L₁) (h₂ : ω₂.IsIsotropic L₂) :
    (ω₁.prod ω₂).IsIsotropic (L₁.prod L₂) :=
  isIsotropic_prod_iff.2 ⟨h₁, h₂⟩

/-- A product subspace is coisotropic for the direct-sum symplectic form exactly when both
factors are coisotropic. -/
@[simp]
lemma isCoisotropic_prod_iff :
    (ω₁.prod ω₂).IsCoisotropic (L₁.prod L₂) ↔
      ω₁.IsCoisotropic L₁ ∧ ω₂.IsCoisotropic L₂ := by
  rw [isCoisotropic_iff, isCoisotropic_iff, isCoisotropic_iff, orthogonal_prod]
  constructor
  · intro h
    constructor
    · intro x hx
      exact (h (x, 0)
        (Submodule.mem_prod.2 ⟨hx, Submodule.zero_mem (ω₂.orthogonal L₂)⟩)).1
    · intro y hy
      exact (h (0, y)
        (Submodule.mem_prod.2 ⟨Submodule.zero_mem (ω₁.orthogonal L₁), hy⟩)).2
  · rintro ⟨h₁, h₂⟩ x hx
    exact Submodule.mem_prod.2 ⟨h₁ x.1 hx.1, h₂ x.2 hx.2⟩

/-- The product of two coisotropic subspaces is coisotropic for the direct-sum symplectic form. -/
lemma IsCoisotropic.prod (h₁ : ω₁.IsCoisotropic L₁) (h₂ : ω₂.IsCoisotropic L₂) :
    (ω₁.prod ω₂).IsCoisotropic (L₁.prod L₂) :=
  isCoisotropic_prod_iff.2 ⟨h₁, h₂⟩

/-- A product subspace is Lagrangian for the direct-sum symplectic form exactly when both factors
are Lagrangian. -/
@[simp]
lemma isLagrangian_prod_iff :
    (ω₁.prod ω₂).IsLagrangian (L₁.prod L₂) ↔
      ω₁.IsLagrangian L₁ ∧ ω₂.IsLagrangian L₂ := by
  rw [isLagrangian_iff, isIsotropic_prod_iff, isCoisotropic_prod_iff,
    isLagrangian_iff, isLagrangian_iff]
  tauto

/-- The product of two Lagrangian subspaces is Lagrangian for the direct-sum symplectic form. -/
lemma IsLagrangian.prod (h₁ : ω₁.IsLagrangian L₁) (h₂ : ω₂.IsLagrangian L₂) :
    (ω₁.prod ω₂).IsLagrangian (L₁.prod L₂) :=
  isLagrangian_prod_iff.2 ⟨h₁, h₂⟩

end SymplecticForm

end TauCeti
