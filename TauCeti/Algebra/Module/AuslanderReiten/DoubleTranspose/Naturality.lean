/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Module.AuslanderReiten.DoubleTranspose.Basic
public import TauCeti.Algebra.Module.AuslanderReiten.Morphism

/-!
# Naturality of double-transpose recovery

Transposing a square between finite-projective presenting maps twice gives a covariant
map. The canonical recovery of their cokernels commutes with this map. For augmented
presentations, recovery therefore identifies the twice-transposed square with the
original map of presented modules.

These identities make the double-transpose recovery compatible with morphisms, as
required for the Auslander–Bridger stable duality. They hold for arbitrary, possibly
noncommutative rings and do not require minimal presentations. Scalars on the second
transpose are identified with the original scalars through the double-opposite equivalence.

## References

* M. Auslander, M. Bridger, *Stable module theory*, Mem. Amer. Math. Soc. 94 (1969), Section 2.1.
-/

public section

namespace TauCeti

open LinearMap

variable (A : Type*) [Ring A]
variable {P₀ P₁ Q₀ Q₁ : Type*}
  [AddCommGroup P₀] [Module A P₀] [AddCommGroup P₁] [Module A P₁]
  [AddCommGroup Q₀] [Module A Q₀] [AddCommGroup Q₁] [Module A Q₁]
  [Module.Finite A P₀] [Module.Projective A P₀]
  [Module.Finite A P₁] [Module.Projective A P₁]
  [Module.Finite A Q₀] [Module.Projective A Q₀]
  [Module.Finite A Q₁] [Module.Projective A Q₁]
  {p : P₁ →ₗ[A] P₀} {q : Q₁ →ₗ[A] Q₀}

/-- Double transposition carries the recovered class of a presenting vector to the recovered
class of its image under the original presentation square. -/
theorem doubleTransposeCokernelEquiv_symm_mk_naturality
    (f₀ : P₀ →ₗ[A] Q₀) (f₁ : P₁ →ₗ[A] Q₁) (hf : f₀ ∘ₗ p = q ∘ₗ f₁) (x : P₀) :
    AuslanderReitenTranspose.map (f₁.lcomp Aᵐᵒᵖ A) (f₀.lcomp Aᵐᵒᵖ A)
      (by ext φ y; exact congrArg φ (LinearMap.congr_fun hf y).symm)
      ((doubleTransposeCokernelEquiv A p).symm (Submodule.Quotient.mk x)) =
        (doubleTransposeCokernelEquiv A q).symm (Submodule.Quotient.mk (f₀ x)) := by
  rw [doubleTransposeCokernelEquiv_symm_mk, AuslanderReitenTranspose.map_mk,
    doubleTransposeCokernelEquiv_symm_mk]
  congr 1
  ext φ
  simp

/-- The canonical double-transpose recovery commutes with the map on cokernels induced by a
presentation square. -/
theorem doubleTransposeCokernelEquiv_naturality
    (f₀ : P₀ →ₗ[A] Q₀) (f₁ : P₁ →ₗ[A] Q₁) (hf : f₀ ∘ₗ p = q ∘ₗ f₁)
    (z : AuslanderReitenTranspose (p.lcomp Aᵐᵒᵖ A)) :
    doubleTransposeCokernelEquiv A q
      (AuslanderReitenTranspose.map (f₁.lcomp Aᵐᵒᵖ A) (f₀.lcomp Aᵐᵒᵖ A)
        (by ext φ y; exact congrArg φ (LinearMap.congr_fun hf y).symm) z) =
      (LinearMap.range p).mapQ (LinearMap.range q) f₀
        (by
          rintro _ ⟨x, rfl⟩
          exact ⟨f₁ x, (LinearMap.congr_fun hf x).symm⟩)
        (doubleTransposeCokernelEquiv A p z) := by
  obtain ⟨x, hx⟩ := Submodule.mkQ_surjective (LinearMap.range p)
    (doubleTransposeCokernelEquiv A p z)
  rw [Submodule.mkQ_apply] at hx
  have hz : z = (doubleTransposeCokernelEquiv A p).symm (Submodule.Quotient.mk x) := by
    rw [hx, LinearEquiv.symm_apply_apply]
  rw [hz, doubleTransposeCokernelEquiv_symm_mk_naturality A f₀ f₁ hf,
    LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply, Submodule.mapQ_apply]

variable {M N : Type*} [AddCommGroup M] [Module A M] [AddCommGroup N] [Module A N]
  {π : P₀ →ₗ[A] M} {ρ : Q₀ →ₗ[A] N}

/-- Inverse double-transpose recovery commutes with a lift of a module map. -/
theorem doubleTransposePresentationEquiv_symm_naturality
    (hp : Function.Exact p π) (hπ : Function.Surjective π)
    (hq : Function.Exact q ρ) (hρ : Function.Surjective ρ)
    (f : M →ₗ[A] N) (f₀ : P₀ →ₗ[A] Q₀) (f₁ : P₁ →ₗ[A] Q₁)
    (hf₀ : ρ ∘ₗ f₀ = f ∘ₗ π) (hf₁ : f₀ ∘ₗ p = q ∘ₗ f₁) (y : M) :
    AuslanderReitenTranspose.map (f₁.lcomp Aᵐᵒᵖ A) (f₀.lcomp Aᵐᵒᵖ A)
      (by ext φ y; exact congrArg φ (LinearMap.congr_fun hf₁ y).symm)
      ((doubleTransposePresentationEquiv A p π hp hπ).symm y) =
        (doubleTransposePresentationEquiv A q ρ hq hρ).symm (f y) := by
  obtain ⟨x, rfl⟩ := hπ y
  rw [← LinearMap.comp_apply f π, ← hf₀, LinearMap.comp_apply,
    doubleTransposePresentationEquiv_symm_apply, doubleTransposePresentationEquiv_symm_apply,
    AuslanderReitenTranspose.map_mk]
  congr 1
  ext φ
  simp

/-- Double-transpose recovery identifies a twice-transposed lift with its original module map.
In particular, the recovered map depends only on the module map, not on its presentation lifts. -/
theorem doubleTransposePresentationEquiv_naturality
    (hp : Function.Exact p π) (hπ : Function.Surjective π)
    (hq : Function.Exact q ρ) (hρ : Function.Surjective ρ)
    (f : M →ₗ[A] N) (f₀ : P₀ →ₗ[A] Q₀) (f₁ : P₁ →ₗ[A] Q₁)
    (hf₀ : ρ ∘ₗ f₀ = f ∘ₗ π) (hf₁ : f₀ ∘ₗ p = q ∘ₗ f₁)
    (z : AuslanderReitenTranspose (p.lcomp Aᵐᵒᵖ A)) :
    doubleTransposePresentationEquiv A q ρ hq hρ
      (AuslanderReitenTranspose.map (f₁.lcomp Aᵐᵒᵖ A) (f₀.lcomp Aᵐᵒᵖ A)
        (by ext φ y; exact congrArg φ (LinearMap.congr_fun hf₁ y).symm) z) =
      f (doubleTransposePresentationEquiv A p π hp hπ z) := by
  have h := doubleTransposePresentationEquiv_symm_naturality A hp hπ hq hρ f f₀ f₁
    hf₀ hf₁ (doubleTransposePresentationEquiv A p π hp hπ z)
  simpa only [LinearEquiv.symm_apply_apply, LinearEquiv.apply_symm_apply] using
    congrArg (doubleTransposePresentationEquiv A q ρ hq hρ) h

end TauCeti
