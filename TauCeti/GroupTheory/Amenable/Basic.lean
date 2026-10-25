/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.Amenable.Mean
public import TauCeti.Topology.Algebra.Group.UCB.CompRight

/-!
# Amenable topological groups

A mean `m` on `TauCeti.UCB G` is *left invariant* when `m (L_g f) = m f` for every `g : G` and
every `f`, where `(L_g f)(x) = f (g⁻¹ * x)` is the left translation. A topological group is
*amenable* when `UCB G` carries a left-invariant mean. No separation, local compactness,
countability or generation hypothesis is part of the definition.

A mean `m` on `UCB G` pushes forward along a continuous homomorphism `φ : G →ₜ* H` to the mean
`f ↦ m (f ∘ φ)` on `UCB H`. Since `(L_(φ g) f) ∘ φ = L_g (f ∘ φ)`, the pushforward of a
left-invariant mean along a surjective homomorphism is left invariant. Hence amenability passes to
images under surjective continuous homomorphisms, and is invariant under isomorphisms of
topological groups.

## Main definitions

* `TauCeti.Mean.IsLeftInvariant`: `m (L_g f) = m f` for all `g` and `f`.
* `TauCeti.Mean.map φ`: the pushforward of means along a continuous homomorphism `φ`.
* `TauCeti.Amenable G`: `UCB G` carries a left-invariant mean.

## Main results

* `TauCeti.Mean.convex_toContinuousLinearMap_image_setOf_isLeftInvariant`: the left-invariant
  means form a convex set.
* `TauCeti.Mean.IsLeftInvariant.map`: pushforward along a surjective continuous homomorphism
  preserves left invariance.
* `TauCeti.Amenable.of_surjective`: amenability passes to images under surjective continuous
  homomorphisms.
* `ContinuousMulEquiv.amenable_iff`: amenability is invariant under isomorphisms of topological
  groups.

## References

* B. Bekka, P. de la Harpe, A. Valette, *Kazhdan's Property (T)*, Appendix G.1, and
  Proposition G.2.2 for quotients.
-/

public section

noncomputable section

open scoped BoundedContinuousFunction

namespace TauCeti

variable {G H K : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
  [Group K] [TopologicalSpace K] [IsTopologicalGroup K]

namespace Mean

/-- A mean `m` on `UCB G` is left invariant when `m (L_g f) = m f` for every `g` and `f`, where
`(L_g f)(x) = f (g⁻¹ * x)`. -/
def IsLeftInvariant (m : Mean G) : Prop :=
  ∀ (g : G) (f : UCB G), m (UCB.leftTranslation g f) = m f

/-- The defining property of a left-invariant mean. -/
theorem isLeftInvariant_iff {m : Mean G} :
    m.IsLeftInvariant ↔ ∀ (g : G) (f : UCB G), m (UCB.leftTranslation g f) = m f :=
  Iff.rfl

/-- A left-invariant mean takes the same value at a function and at its left translates. -/
@[simp]
theorem IsLeftInvariant.apply_leftTranslation {m : Mean G} (hm : m.IsLeftInvariant) (g : G)
    (f : UCB G) : m (UCB.leftTranslation g f) = m f :=
  hm g f

/-- The left-invariant means on `UCB G` form a convex set of continuous linear functionals. -/
theorem convex_toContinuousLinearMap_image_setOf_isLeftInvariant :
    Convex ℝ (toContinuousLinearMap '' {m : Mean G | m.IsLeftInvariant}) := by
  rintro _ ⟨m, hm, rfl⟩ _ ⟨n, hn, rfl⟩ a b ha hb hab
  obtain ⟨k, hk⟩ := convex_range_toContinuousLinearMap ⟨m, rfl⟩ ⟨n, rfl⟩ ha hb hab
  refine ⟨k, fun g f => ?_, hk⟩
  have h := congr($hk (UCB.leftTranslation g f) - $hk f)
  simp only [coe_toContinuousLinearMap, add_apply, smul_apply, smul_eq_mul, hm g f, hn g f,
    sub_self] at h
  exact sub_eq_zero.1 h

/-- The pushforward `f ↦ m (f ∘ φ)` of a mean `m` on `UCB G` along a continuous homomorphism
`φ : G →ₜ* H`, as a mean on `UCB H`. -/
def map (φ : G →ₜ* H) (m : Mean G) : Mean H :=
  mk₀ (m.toPositiveLinearMap.toLinearMap ∘ₗ (UCB.compRightAlgHom φ).toLinearMap)
    (fun f hf => map_nonneg m (by simpa using UCB.monotone_compRightAlgHom φ hf)) (by simp)

@[simp]
theorem map_apply (φ : G →ₜ* H) (m : Mean G) (f : UCB H) :
    m.map φ f = m (UCB.compRightAlgHom φ f) :=
  mk₀_apply _ _ _ f

/-- The pushforward along the identity is the identity. -/
@[simp]
theorem map_id (m : Mean G) : m.map (ContinuousMonoidHom.id G) = m :=
  ext fun f => by simp

/-- Pushing forward along `φ` and then along `ψ` is pushing forward along `ψ ∘ φ`. -/
@[simp]
theorem map_map (ψ : H →ₜ* K) (φ : G →ₜ* H) (m : Mean G) :
    (m.map φ).map ψ = m.map (ψ.comp φ) :=
  ext fun f => by simp [UCB.compRightAlgHom_comp]

/-- The pushforward of a left-invariant mean along a continuous homomorphism `φ` is invariant under
left translation by the elements `φ g` of the range of `φ`. -/
theorem IsLeftInvariant.map_apply_leftTranslation {m : Mean G} (hm : m.IsLeftInvariant)
    (φ : G →ₜ* H) (g : G) (f : UCB H) :
    m.map φ (UCB.leftTranslation (φ g) f) = m.map φ f := by
  rw [map_apply, map_apply, UCB.compRightAlgHom_leftTranslation, hm]

/-- The pushforward of a left-invariant mean along a surjective continuous homomorphism is left
invariant. -/
theorem IsLeftInvariant.map {m : Mean G} (hm : m.IsLeftInvariant) {φ : G →ₜ* H}
    (hφ : Function.Surjective φ) : (m.map φ).IsLeftInvariant := by
  intro h f
  obtain ⟨g, rfl⟩ := hφ h
  exact hm.map_apply_leftTranslation φ g f

end Mean

variable (G) in
/-- A topological group `G` is amenable when `UCB G` carries a left-invariant mean. -/
class Amenable : Prop where
  /-- An amenable group has a left-invariant mean on `UCB G`. -/
  exists_isLeftInvariant : ∃ m : Mean G, m.IsLeftInvariant

variable (G) in
/-- A topological group is amenable exactly when `UCB G` carries a left-invariant mean. -/
theorem amenable_iff : Amenable G ↔ ∃ m : Mean G, m.IsLeftInvariant :=
  ⟨fun h => h.1, fun h => ⟨h⟩⟩

/-- The image of an amenable topological group under a surjective continuous homomorphism is
amenable. -/
theorem Amenable.of_surjective [Amenable G] (φ : G →ₜ* H) (hφ : Function.Surjective φ) :
    Amenable H :=
  have ⟨m, hm⟩ := Amenable.exists_isLeftInvariant (G := G)
  ⟨⟨m.map φ, hm.map hφ⟩⟩

end TauCeti

namespace ContinuousMulEquiv

open TauCeti

variable {G H : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [Group H] [TopologicalSpace H] [IsTopologicalGroup H]

/-- Amenability is invariant under isomorphisms of topological groups. -/
theorem amenable_iff (e : G ≃ₜ* H) : Amenable G ↔ Amenable H :=
  ⟨fun _ => .of_surjective (e : G →ₜ* H) e.surjective,
    fun _ => .of_surjective (e.symm : H →ₜ* G) e.symm.surjective⟩

end ContinuousMulEquiv
