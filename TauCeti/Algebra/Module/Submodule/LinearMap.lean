/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.Submodule.LinearMap

/-!
# Linear maps and inclusions for submodules

The inclusion maps `Submodule.inclusion` between nested submodules compose along the composite
inequality (`Submodule.inclusion_comp_inclusion`), as `Set.inclusion_comp_inclusion` does for sets.

When every `A`-linear map `S →ₗ[A] M` lands inside an `A`-submodule `p`, postcomposition with
`p.subtype` identifies `S →ₗ[A] p` with `S →ₗ[A] M` as `k`-modules
(`Submodule.linearMapSubtypeEquiv`).
-/

public section

namespace Submodule

section Inclusion

variable {R M : Type*} [Semiring R] [AddCommMonoid M] [Module R M]

/-- Composing two inclusions of submodules gives the inclusion along the composite inequality. -/
@[simp]
theorem inclusion_comp_inclusion {p q r : Submodule R M} (h : p ≤ q) (h' : q ≤ r) :
    inclusion h' ∘ₗ inclusion h = inclusion (h.trans h') :=
  LinearMap.ext fun _ ↦ Subtype.ext rfl

end Inclusion

section LinearMapSubtypeEquiv

variable (k : Type*) {A S M : Type*} [Semiring k] [Semiring A] [SMul k A]
  [AddCommMonoid S] [Module A S]
  [AddCommMonoid M] [Module k M] [Module A M] [IsScalarTower k A M] [SMulCommClass A k M]

/-- Postcomposition with `p.subtype` identifies `S →ₗ[A] p` with `S →ₗ[A] M` whenever every
`A`-linear map from `S` to `M` lands inside the `A`-submodule `p`. -/
def linearMapSubtypeEquiv (p : Submodule A M) (hp : ∀ (f : S →ₗ[A] M) (s : S), f s ∈ p) :
    (S →ₗ[A] p) ≃ₗ[k] (S →ₗ[A] M) where
  toFun g := p.subtype.comp g
  invFun f := f.codRestrict p (hp f)
  map_add' g₁ g₂ := by
    ext s
    simp
  map_smul' c g := by
    ext s
    simp
  left_inv g := by
    ext s
    rfl
  right_inv f := by
    ext s
    rfl

/-- Applying `p.linearMapSubtypeEquiv` postcomposes with `p.subtype`. -/
@[simp]
theorem linearMapSubtypeEquiv_apply (p : Submodule A M)
    (hp : ∀ (f : S →ₗ[A] M) (s : S), f s ∈ p) (g : S →ₗ[A] p) :
    p.linearMapSubtypeEquiv k hp g = p.subtype.comp g :=
  (rfl)

/-- Applying the inverse of `p.linearMapSubtypeEquiv` restricts the codomain to `p`. -/
@[simp]
theorem coe_linearMapSubtypeEquiv_symm_apply (p : Submodule A M)
    (hp : ∀ (f : S →ₗ[A] M) (s : S), f s ∈ p) (f : S →ₗ[A] M) (s : S) :
    ((p.linearMapSubtypeEquiv k hp).symm f s : M) = f s :=
  (rfl)

end LinearMapSubtypeEquiv

end Submodule
