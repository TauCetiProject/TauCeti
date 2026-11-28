/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors, Axel Delaval, Zhiyuan Zhang, Leheng Chen
-/
module

public import Mathlib.Geometry.Manifold.LocalDiffeomorph
import TauCeti.Geometry.Manifold.ContMDiff.Subtype

/-!
# Restricting diffeomorphisms to open subsets

A diffeomorphism restricts to open subsets that it maps onto each other. The restriction and
its inverse retain the ambient diffeomorphism's pointwise values.
-/

public section

open scoped Manifold

namespace Diffeomorph

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners 𝕜 E H} {n : WithTop ℕ∞}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]

section Subtype

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F] {G : Type*} [TopologicalSpace G]
  {J : ModelWithCorners 𝕜 F G} {N : Type*} [TopologicalSpace N] [ChartedSpace G N]
  {U : TopologicalSpace.Opens M} {V : TopologicalSpace.Opens N}

/-- A diffeomorphism `g : M ≃ₘ N` restricts to a diffeomorphism between open subsets `U` and `V`
that it maps onto each other, each carrying the charts Mathlib restricts to it. This is the smooth
form of Mathlib's `Homeomorph.subtype`. -/
def subtype (g : M ≃ₘ^n⟮I, J⟯ N) (h_iff : ∀ x, x ∈ U ↔ g x ∈ V) : U ≃ₘ^n⟮I, J⟯ V where
  toEquiv := g.toEquiv.subtypeEquiv h_iff
  contMDiff_toFun := (TauCeti.ContMDiff.subtypeVal_comp_iff _ _).1
    (g.contMDiff.comp contMDiff_subtypeVal)
  contMDiff_invFun := (TauCeti.ContMDiff.subtypeVal_comp_iff _ _).1
    (g.symm.contMDiff.comp contMDiff_subtypeVal)

/-- The restriction `Diffeomorph.subtype` evaluates as the diffeomorphism. -/
@[simp]
theorem subtype_apply_coe (g : M ≃ₘ^n⟮I, J⟯ N) (h_iff : ∀ x, x ∈ U ↔ g x ∈ V) (x : U) :
    (g.subtype h_iff x : N) = g x :=
  (rfl)

/-- The inverse of the restriction `Diffeomorph.subtype` evaluates as the inverse
diffeomorphism. -/
@[simp]
theorem subtype_symm_apply_coe (g : M ≃ₘ^n⟮I, J⟯ N) (h_iff : ∀ x, x ∈ U ↔ g x ∈ V) (y : V) :
    ((g.subtype h_iff).symm y : M) = g.symm y :=
  (rfl)

end Subtype

end Diffeomorph
