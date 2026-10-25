/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Module.HomCocycle.Basic

/-!
# Contravariance of Hom cocycles in a presentation

A commutative square between presenting arrows induces precomposition on Hom
cocycles modulo coboundaries. These maps reverse composition of squares and
commute with postcomposition in the coefficient module. They provide the
presentation variable of the cocycle model of `Ext¹`.
-/

public section

namespace LinearMap

variable {k A P₀ P₁ Q₀ Q₁ N : Type*} [CommRing k] [Ring A] [Algebra k A]
  [AddCommGroup P₀] [Module A P₀] [AddCommGroup P₁] [Module A P₁]
  [AddCommGroup Q₀] [Module A Q₀] [AddCommGroup Q₁] [Module A Q₁]
  [AddCommGroup N] [Module A N] [Module k N] [IsScalarTower k A N]
  {p : P₁ →ₗ[A] P₀} {q : Q₁ →ₗ[A] Q₀}

/-- Precomposition by a presentation square on Hom cocycles modulo coboundaries. -/
def homCocycleQuotientPrecomp (f₀ : P₀ →ₗ[A] Q₀) (f₁ : P₁ →ₗ[A] Q₁)
    (hf : f₀.comp p = q.comp f₁) :
    HomCocycleQuotient (k := k) q N →ₗ[k] HomCocycleQuotient (k := k) p N := by
  let Z := ker ((ker p).subtype.lcomp k N)
  let W := ker ((ker q).subtype.lcomp k N)
  have hker (x : ker p) : f₁ x ∈ ker q := by
    rw [mem_ker, ← comp_apply, ← hf, comp_apply, mem_ker.mp x.property, map_zero]
  let F := ((f₁.lcomp k N).comp W.subtype).codRestrict Z fun h ↦ by
    apply mem_ker.mpr
    ext x
    exact congrArg (fun a : ker q →ₗ[A] N ↦ a ⟨f₁ x, hker x⟩) (mem_ker.mp h.property)
  exact ((range (q.lcomp k N)).comap W.subtype).mapQ
    ((range (p.lcomp k N)).comap Z.subtype) F (by
      rintro h ⟨a, ha⟩
      refine ⟨a.comp f₀, ?_⟩
      simpa only [F, codRestrict_apply, comp_apply, Submodule.subtype_apply, lcomp_apply',
        comp_assoc, hf] using congrArg (fun b ↦ b.comp f₁) ha)

/-- Precomposition sends a cocycle class to the class of the composite. -/
@[simp]
theorem homCocycleQuotientPrecomp_mk (f₀ : P₀ →ₗ[A] Q₀) (f₁ : P₁ →ₗ[A] Q₁)
    (hf : f₀.comp p = q.comp f₁) (h : ker ((ker q).subtype.lcomp k N)) :
    homCocycleQuotientPrecomp f₀ f₁ hf (Submodule.Quotient.mk h) =
      Submodule.Quotient.mk
        (⟨h.val.comp f₁, by
          apply mem_ker.mpr
          ext x
          have hx : f₁ x ∈ ker q := by
            rw [mem_ker, ← comp_apply, ← hf, comp_apply, mem_ker.mp x.property, map_zero]
          exact congrArg (fun a : ker q →ₗ[A] N ↦ a ⟨f₁ x, hx⟩) (mem_ker.mp h.property)⟩ :
          ker ((ker p).subtype.lcomp k N)) := by
  simp only [homCocycleQuotientPrecomp, Submodule.mapQ_apply]
  rfl

/-- The identity square preserves Hom cocycle classes. -/
@[simp]
theorem homCocycleQuotientPrecomp_id :
    homCocycleQuotientPrecomp (k := k) (N := N) (p := p) id id (by simp) = id := by
  apply LinearMap.ext
  intro x
  induction x using Submodule.Quotient.induction_on with
  | _ h => simp

/-- Precomposition reverses composition of presentation squares. -/
@[simp]
theorem homCocycleQuotientPrecomp_comp_precomp {R₀ R₁ : Type*}
    [AddCommGroup R₀] [Module A R₀] [AddCommGroup R₁] [Module A R₁]
    {r : R₁ →ₗ[A] R₀} (f₀ : P₀ →ₗ[A] Q₀) (f₁ : P₁ →ₗ[A] Q₁)
    (hf : f₀.comp p = q.comp f₁) (g₀ : Q₀ →ₗ[A] R₀) (g₁ : Q₁ →ₗ[A] R₁)
    (hg : g₀.comp q = r.comp g₁) :
    (homCocycleQuotientPrecomp (k := k) (N := N) f₀ f₁ hf).comp
        (homCocycleQuotientPrecomp g₀ g₁ hg) =
      homCocycleQuotientPrecomp (g₀.comp f₀) (g₁.comp f₁)
        (by rw [comp_assoc, hf, ← comp_assoc, hg, comp_assoc]) := by
  apply LinearMap.ext
  intro x
  induction x using Submodule.Quotient.induction_on with
  | _ h => simp [comp_assoc]

/-- Precomposition in a presentation commutes with postcomposition in the coefficients. -/
@[simp]
theorem homCocycleQuotientPrecomp_map {N' : Type*}
    [AddCommGroup N'] [Module A N'] [Module k N'] [IsScalarTower k A N']
    (f₀ : P₀ →ₗ[A] Q₀) (f₁ : P₁ →ₗ[A] Q₁) (hf : f₀.comp p = q.comp f₁)
    (g : N →ₗ[A] N') (x : HomCocycleQuotient (k := k) q N) :
    homCocycleQuotientPrecomp f₀ f₁ hf (homCocycleQuotientMap q g x) =
      homCocycleQuotientMap p g (homCocycleQuotientPrecomp f₀ f₁ hf x) := by
  induction x using Submodule.Quotient.induction_on with
  | _ h => simp [comp_assoc]

end LinearMap
