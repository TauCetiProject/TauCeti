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
left-invariant mean is invariant under translation by the range of `φ`, and, by continuity of
`k ↦ m ((L_k f) ∘ φ)`, by its closure. So the pushforward along a homomorphism with dense range is
left invariant. Hence amenability passes to the target of a continuous homomorphism with dense
range, in particular to images under surjective continuous homomorphisms, and is invariant under
isomorphisms of topological groups.

## Main definitions

* `TauCeti.Mean.IsLeftInvariant`, `TauCeti.AddMean.IsLeftInvariant`: left translation invariance
  of a multiplicative or additive mean.
* `TauCeti.Mean.map φ`, `TauCeti.AddMean.map φ`: pushforward of means along a continuous
  homomorphism `φ`.
* `TauCeti.Amenable G`, `TauCeti.AddAmenable A`: `UCB G` (respectively `AddUCB A`) carries a
  left-invariant mean.

## Main results

* `TauCeti.Mean.convex_toContinuousLinearMap_image_setOf_isLeftInvariant`: the left-invariant
  means form a convex set.
* `TauCeti.Mean.IsLeftInvariant.map`, `TauCeti.AddMean.IsLeftInvariant.map`: pushforward along a
  continuous homomorphism with dense range preserves left invariance.
* `TauCeti.amenable_multiplicative_iff`, `TauCeti.addAmenable_additive_iff`: `AddAmenable` and
  `Amenable` correspond under `Multiplicative` and `Additive`.
* `TauCeti.Amenable.of_denseRange`, `TauCeti.AddAmenable.of_denseRange`: amenability passes to
  the target of a continuous homomorphism with dense range, in particular to images under
  surjective continuous homomorphisms.
* `TauCeti.AddAmenable.quotient`: quotients of amenable additive topological groups are amenable.
* `TauCeti.Amenable.of_le`, `TauCeti.AddAmenable.of_le`: amenability passes from a finer to a
  coarser group topology.
* `ContinuousMulEquiv.amenable_iff`, `ContinuousAddEquiv.addAmenable_iff`: amenability is
  invariant under isomorphisms of topological groups.

## References

* B. Bekka, P. de la Harpe, A. Valette, *Kazhdan's Property (T)*, Appendix G.1, and
  Proposition G.2.2 for quotients.
-/

public section

noncomputable section

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

/-- The pushforward of a left-invariant mean along a continuous homomorphism with dense range is
left invariant. -/
theorem IsLeftInvariant.map {m : Mean G} (hm : m.IsLeftInvariant) {φ : G →ₜ* H}
    (hφ : DenseRange φ) : (m.map φ).IsLeftInvariant := by
  -- the pushforward is invariant under translation by the range, and
  -- `k ↦ m.map φ (L_k f)` is continuous
  intro h f
  have hc : Continuous fun k : H => m.map φ (UCB.leftTranslation k f) :=
    (map_continuous (m.map φ)).comp (UCB.continuous_leftTranslation_apply f)
  exact hφ.induction_on (p := fun k => m.map φ (UCB.leftTranslation k f) = m.map φ f) h
    (isClosed_eq hc continuous_const) fun g => hm.map_apply_leftTranslation φ g f

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

/-- The target of a continuous homomorphism with dense range from an amenable topological group
is amenable; in particular, so is the image under a surjective continuous homomorphism. -/
theorem Amenable.of_denseRange [Amenable G] (φ : G →ₜ* H) (hφ : DenseRange φ) :
    Amenable H :=
  have ⟨m, hm⟩ := Amenable.exists_isLeftInvariant (G := G)
  ⟨⟨m.map φ, hm.map hφ⟩⟩

omit [TopologicalSpace G] [IsTopologicalGroup G] in
/-- Amenability passes from a finer group topology to a coarser group topology. -/
theorem Amenable.of_le {t₁ t₂ : TopologicalSpace G}
    [@IsTopologicalGroup G t₁ _] [@IsTopologicalGroup G t₂ _] (h : t₁ ≤ t₂)
    (ha : @Amenable G _ t₁ _) : @Amenable G _ t₂ _ := by
  -- The source and target share a carrier but have different topologies.
  let φ : @ContinuousMonoidHom G G _ _ t₁ t₂ :=
    @ContinuousMonoidHom.mk G G _ _ t₁ t₂ (MonoidHom.id G) (continuous_id_of_le h)
  exact @Amenable.of_denseRange G G _ t₁ _ _ t₂ _ ha φ
    (@Function.Surjective.denseRange G t₂ G _ fun x => ⟨x, MonoidHom.id_apply G x⟩)

end TauCeti

namespace ContinuousMulEquiv

open TauCeti

variable {G H : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [Group H] [TopologicalSpace H] [IsTopologicalGroup H]

/-- Amenability is invariant under isomorphisms of topological groups. -/
theorem amenable_iff (e : G ≃ₜ* H) : Amenable G ↔ Amenable H :=
  ⟨fun _ => .of_denseRange (e : G →ₜ* H) e.surjective.denseRange,
    fun _ => .of_denseRange (e.symm : H →ₜ* G) e.symm.surjective.denseRange⟩

end ContinuousMulEquiv

namespace TauCeti

section Additive

variable {A : Type*} [AddGroup A] [TopologicalSpace A] [IsTopologicalAddGroup A]

namespace AddMean

/-- A mean `m` on `AddUCB A` is left invariant when `m (L_a f) = m f` for every `a : A` and `f`,
where `(L_a f)(x) = f (-a + x)`. -/
def IsLeftInvariant (m : AddMean A) : Prop :=
  ∀ (a : A) (f : AddUCB A), m (AddUCB.leftTranslation a f) = m f

/-- The defining property of a left-invariant additive mean. -/
theorem isLeftInvariant_iff {m : AddMean A} :
    m.IsLeftInvariant ↔ ∀ (a : A) (f : AddUCB A), m (AddUCB.leftTranslation a f) = m f :=
  Iff.rfl

/-- A left-invariant additive mean takes the same value at a function and at its left translates. -/
@[simp]
theorem IsLeftInvariant.apply_leftTranslation {m : AddMean A} (hm : m.IsLeftInvariant) (a : A)
    (f : AddUCB A) : m (AddUCB.leftTranslation a f) = m f :=
  hm a f

section Map

variable {B : Type*} [AddGroup B] [TopologicalSpace B] [IsTopologicalAddGroup B]

/-- Pushforward `f ↦ m (f ∘ φ)` of a mean on `AddUCB A` along a continuous additive homomorphism
`φ : A →ₜ+ B`. -/
def map (φ : A →ₜ+ B) (m : AddMean A) : AddMean B :=
  mk₀ (m.toPositiveLinearMap.toLinearMap ∘ₗ (AddUCB.compRightAlgHom φ).toLinearMap)
    (fun f hf => map_nonneg m (by simpa using AddUCB.monotone_compRightAlgHom φ hf)) (by simp)

@[simp]
theorem map_apply (φ : A →ₜ+ B) (m : AddMean A) (f : AddUCB B) :
    m.map φ f = m (AddUCB.compRightAlgHom φ f) :=
  mk₀_apply _ _ _ f

/-- The pushforward along the identity is the identity. -/
@[simp]
theorem map_id (m : AddMean A) : m.map (ContinuousAddMonoidHom.id A) = m :=
  ext fun _ => by simp

/-- Pushing forward along `φ` and then along `ψ` is pushing forward along `ψ ∘ φ`. -/
@[simp]
theorem map_map {C : Type*} [AddGroup C] [TopologicalSpace C] [IsTopologicalAddGroup C]
    (ψ : B →ₜ+ C) (φ : A →ₜ+ B) (m : AddMean A) :
    (m.map φ).map ψ = m.map (ψ.comp φ) :=
  ext fun _ => by simp [AddUCB.compRightAlgHom_comp]

/-- The pushforward of a left-invariant additive mean along `φ` is invariant under left translation
by elements in the range of `φ`. -/
theorem IsLeftInvariant.map_apply_leftTranslation {m : AddMean A} (hm : m.IsLeftInvariant)
    (φ : A →ₜ+ B) (a : A) (f : AddUCB B) :
    m.map φ (AddUCB.leftTranslation (φ a) f) = m.map φ f := by
  rw [map_apply, map_apply, AddUCB.compRightAlgHom_leftTranslation, hm]

/-- Pushforward along a continuous additive homomorphism with dense range preserves left
invariance. -/
theorem IsLeftInvariant.map {m : AddMean A} (hm : m.IsLeftInvariant) {φ : A →ₜ+ B}
    (hφ : DenseRange φ) : (m.map φ).IsLeftInvariant := by
  intro b f
  have hc : Continuous fun k : B => m.map φ (AddUCB.leftTranslation k f) :=
    (map_continuous (m.map φ)).comp (AddUCB.continuous_leftTranslation_apply f)
  exact hφ.induction_on (p := fun k => m.map φ (AddUCB.leftTranslation k f) = m.map φ f) b
    (isClosed_eq hc continuous_const) fun a => hm.map_apply_leftTranslation φ a f

end Map

/-- `toMultiplicativeEquiv` preserves and reflects left invariance. -/
@[simp]
theorem isLeftInvariant_toMultiplicativeEquiv_iff {m : AddMean A} :
    (toMultiplicativeEquiv A m).IsLeftInvariant ↔ m.IsLeftInvariant := by
  rw [Mean.isLeftInvariant_iff, isLeftInvariant_iff]
  constructor
  · intro hm a f
    simpa using hm (Multiplicative.ofAdd a) (AddUCB.toMultiplicativeAlgEquiv A f)
  · intro hm g f
    simpa using hm g.toAdd ((AddUCB.toMultiplicativeAlgEquiv A).symm f)

end AddMean

/-- `toAdditiveEquiv` preserves and reflects left invariance. -/
@[simp]
theorem Mean.isLeftInvariant_toAdditiveEquiv_iff {G : Type*} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] {m : Mean G} :
    (toAdditiveEquiv G m).IsLeftInvariant ↔ m.IsLeftInvariant := by
  rw [AddMean.isLeftInvariant_iff, isLeftInvariant_iff]
  constructor
  · intro hm g f
    have htr : (UCB.toAdditiveAlgEquiv G).symm
        (AddUCB.leftTranslation (Additive.ofMul g) (UCB.toAdditiveAlgEquiv G f)) =
        UCB.leftTranslation g f := by
      apply (UCB.toAdditiveAlgEquiv G).injective
      simp
    simpa [htr] using hm (Additive.ofMul g) (UCB.toAdditiveAlgEquiv G f)
  · intro hm a f
    have htr : (UCB.toAdditiveAlgEquiv G).symm (AddUCB.leftTranslation a f) =
        UCB.leftTranslation a.toMul ((UCB.toAdditiveAlgEquiv G).symm f) := by
      apply (UCB.toAdditiveAlgEquiv G).injective
      simp
    simpa [htr] using hm a.toMul ((UCB.toAdditiveAlgEquiv G).symm f)

variable (A) in
/-- An additive topological group `A` is amenable when `AddUCB A` carries a left-invariant mean. -/
class AddAmenable : Prop where
  /-- An amenable additive group has a left-invariant mean on `AddUCB A`. -/
  exists_isLeftInvariant : ∃ m : AddMean A, m.IsLeftInvariant

variable (A) in
/-- An additive topological group is amenable exactly when `AddUCB A` carries a left-invariant
mean. -/
theorem addAmenable_iff : AddAmenable A ↔ ∃ m : AddMean A, m.IsLeftInvariant :=
  ⟨fun h => h.1, fun h => ⟨h⟩⟩

/-- `Multiplicative A` is amenable if and only if the additive topological group `A` is
amenable. -/
@[simp]
theorem amenable_multiplicative_iff : Amenable (Multiplicative A) ↔ AddAmenable A := by
  rw [amenable_iff, addAmenable_iff]
  exact ((AddMean.toMultiplicativeEquiv A).exists_congr
    fun _ => AddMean.isLeftInvariant_toMultiplicativeEquiv_iff.symm).symm

/-- `Additive G` is amenable if and only if the topological group `G` is amenable. -/
@[simp]
theorem addAmenable_additive_iff {G : Type*} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] : AddAmenable (Additive G) ↔ Amenable G := by
  rw [addAmenable_iff, amenable_iff]
  exact ((Mean.toAdditiveEquiv G).exists_congr
    fun _ => Mean.isLeftInvariant_toAdditiveEquiv_iff.symm).symm

instance [AddAmenable A] : Amenable (Multiplicative A) :=
  amenable_multiplicative_iff.2 ‹_›

instance {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [Amenable G] :
    AddAmenable (Additive G) :=
  addAmenable_additive_iff.2 ‹_›

/-- The target of a continuous additive homomorphism with dense range from an amenable additive
topological group is amenable; in particular, so is the image under a surjective continuous
additive homomorphism. -/
theorem AddAmenable.of_denseRange {B : Type*} [AddGroup B] [TopologicalSpace B]
    [IsTopologicalAddGroup B] [AddAmenable A] (φ : A →ₜ+ B) (hφ : DenseRange φ) :
    AddAmenable B :=
  have ⟨m, hm⟩ := AddAmenable.exists_isLeftInvariant (A := A)
  ⟨⟨m.map φ, hm.map hφ⟩⟩

/-- Every quotient of an amenable additive topological group by a normal additive subgroup is
amenable. -/
instance AddAmenable.quotient [AddAmenable A] (N : AddSubgroup A) [N.Normal] :
    AddAmenable (A ⧸ N) :=
  .of_denseRange ⟨QuotientAddGroup.mk' N, continuous_quot_mk⟩
    (QuotientAddGroup.mk'_surjective N).denseRange

omit [TopologicalSpace A] [IsTopologicalAddGroup A] in
/-- Additive amenability passes from a finer additive group topology to a coarser one. -/
theorem AddAmenable.of_le {t₁ t₂ : TopologicalSpace A}
    [@IsTopologicalAddGroup A t₁ _] [@IsTopologicalAddGroup A t₂ _] (h : t₁ ≤ t₂)
    (ha : @AddAmenable A _ t₁ _) : @AddAmenable A _ t₂ _ := by
  let φ : @ContinuousAddMonoidHom A A _ _ t₁ t₂ :=
    @ContinuousAddMonoidHom.mk A A _ _ t₁ t₂ (AddMonoidHom.id A) (continuous_id_of_le h)
  exact @AddAmenable.of_denseRange A _ t₁ _ A _ t₂ _ ha φ
    (@Function.Surjective.denseRange A t₂ A _ fun x => ⟨x, AddMonoidHom.id_apply A x⟩)

end Additive

end TauCeti

namespace ContinuousAddEquiv

open TauCeti

variable {A B : Type*}
  [AddGroup A] [TopologicalSpace A] [IsTopologicalAddGroup A]
  [AddGroup B] [TopologicalSpace B] [IsTopologicalAddGroup B]

/-- Additive amenability is invariant under topological additive group isomorphisms. -/
theorem addAmenable_iff (e : A ≃ₜ+ B) : AddAmenable A ↔ AddAmenable B :=
  ⟨fun _ => .of_denseRange (e : A →ₜ+ B) e.surjective.denseRange,
    fun _ => .of_denseRange (e.symm : B →ₜ+ A) e.symm.surjective.denseRange⟩

end ContinuousAddEquiv
