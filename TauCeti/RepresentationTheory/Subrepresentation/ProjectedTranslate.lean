/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RepresentationTheory.Intertwining
public import TauCeti.LinearAlgebra.Spreading

/-!
# Normalized translates in a projected representation

Suppose a group acts on an ambient target space and the target of interest is the image of a
central projection. Translate a source map, apply the projection, and then rescale. These maps
have codomain the image subrepresentation, where the dimension used in the spreading condition
is the dimension of the projected space, not that of the ambient space. Normalization by a
nonzero scalar preserves spreading and the images of every subspace of the source.

The construction is the linear-algebra part of `New.Data.normalizedPoincare` in
`New/Reduction/ShortAndEnough.lean` of lsernau/grh-lean (`72fead1`). For a central group-algebra
idempotent, use Mathlib's `Representation.IntertwiningMap.centralAlgebraMul` as the projection.
-/

public section

open TauCeti

namespace Representation.IntertwiningMap

section Semiring

variable {A G V W : Type*} [CommSemiring A] [Monoid G]
  [AddCommMonoid V] [Module A V] [AddCommMonoid W] [Module A W]
  {ρ : Representation A G W}

/-- Translate `P` by `g`, apply the intertwining endomorphism `e`, and scale by `c`.
For a central projection `e`, this maps into the projected target representation. -/
def normalizedProjectedTranslate (e : ρ.IntertwiningMap ρ) (P : V →ₗ[A] W) (c : A) (g : G) :
    V →ₗ[A] e.range.toSubmodule :=
  c • (LinearMap.codRestrict e.range.toSubmodule (e.toLinearMap ∘ₗ ρ g ∘ₗ P)
    (fun v ↦ (mem_range ρ ρ e _).2 ⟨ρ g (P v), rfl⟩))

/-- In the ambient space the normalized translate is `c • e (ρ g (P v))`. -/
@[simp] theorem coe_normalizedProjectedTranslate_apply (e : ρ.IntertwiningMap ρ)
    (P : V →ₗ[A] W) (c : A) (g : G) (v : V) :
    (normalizedProjectedTranslate e P c g v : W) = c • e (ρ g (P v)) := (rfl)

/-- The normalization is scalar multiplication of the projected translate at scale `1`. -/
theorem normalizedProjectedTranslate_eq_smul (e : ρ.IntertwiningMap ρ) (P : V →ₗ[A] W)
    (c : A) (g : G) :
    e.normalizedProjectedTranslate P c g = c • e.normalizedProjectedTranslate P 1 g := by
  simp only [normalizedProjectedTranslate, one_smul]

/-- The normalized maps at `g * h` are obtained by translating the normalized maps at `h`
in the image representation. In particular the whole family is obtained from the map at `1`. -/
theorem normalizedProjectedTranslate_mul (e : ρ.IntertwiningMap ρ) (P : V →ₗ[A] W)
    (c : A) (g h : G) :
    normalizedProjectedTranslate e P c (g * h) =
      e.range.toRepresentation g ∘ₗ normalizedProjectedTranslate e P c h := by
  apply LinearMap.ext
  intro v
  symm
  rw [LinearMap.comp_apply, Subrepresentation.toRepresentation_apply_coe]
  simp only [coe_normalizedProjectedTranslate_apply, map_mul, mul_apply_eq_comp, map_smul,
    isIntertwining]

end Semiring

/-- Normalization does not change the image of any source subspace. This also applies to the
whole source, and to the sum of images for any fixed selection of translates. -/
theorem map_normalizedProjectedTranslate_eq {K G V W : Type*} [Semifield K] [Monoid G]
    [AddCommMonoid V] [Module K V] [AddCommMonoid W] [Module K W]
    {ρ : Representation K G W} (e : ρ.IntertwiningMap ρ) (P : V →ₗ[K] W)
    {c : K} (hc : c ≠ 0) (g : G) (U : Submodule K V) :
    U.map (normalizedProjectedTranslate e P c g) =
      U.map (normalizedProjectedTranslate e P 1 g) := by
  rw [e.normalizedProjectedTranslate_eq_smul, Submodule.map_smul _ _ _ hc]

section Field

variable {K G V W : Type*} [Field K] [Monoid G]
  [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
  {ρ : Representation K G W}

/-- The projected translates spread with the same error before and after nonzero rescaling.
Both spreading conditions are measured in the projected target. -/
theorem isSpread_normalizedProjectedTranslate_iff (e : ρ.IntertwiningMap ρ) (P : V →ₗ[K] W)
    {c : K} (hc : c ≠ 0) {η : ℝ} :
    IsSpread (normalizedProjectedTranslate e P c) η ↔
      IsSpread (normalizedProjectedTranslate e P 1) η := by
  have hcomap (F : Submodule K e.range.toSubmodule) (g : G) :
      F.comap (normalizedProjectedTranslate e P c g) =
        F.comap (normalizedProjectedTranslate e P 1 g) := by
    rw [e.normalizedProjectedTranslate_eq_smul, Submodule.comap_smul _ _ _ hc]
  rw [isSpread_iff, isSpread_iff]
  constructor
  · intro h F
    obtain ⟨g, hg⟩ := h F
    exact ⟨g, hcomap F g ▸ hg⟩
  · intro h F
    obtain ⟨g, hg⟩ := h F
    exact ⟨g, (hcomap F g).symm ▸ hg⟩

end Field

end Representation.IntertwiningMap
