/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.Amenable.Mean
public import TauCeti.Topology.Algebra.Group.UCB.Additive

/-!
# Amenable topological groups

A mean `m` on `TauCeti.UCB G` is *left invariant* when `m (L_g f) = m f` for every `g : G` and
every `f`, where `(L_g f)(x) = f (g⁻¹ * x)` is the left translation. A topological group is
*amenable* when `UCB G` carries a left-invariant mean. No separation, local compactness,
countability or generation hypothesis is part of the definition. Left invariance, pushforward, and
type-tag transport also apply to additive means `TauCeti.AddMean A` on `TauCeti.AddUCB A` for a
topological additive group `A`; `TauCeti.AddAmenable A` is defined via
`TauCeti.Amenable (Multiplicative A)`.

A mean `m` on `UCB G` pushes forward along a continuous homomorphism `φ : G →ₜ* H` to the mean
`f ↦ m (f ∘ φ)` on `UCB H`. Since `(L_(φ g) f) ∘ φ = L_g (f ∘ φ)`, the pushforward of a
left-invariant mean is invariant under translation by the range of `φ`, and, by continuity of
`k ↦ m ((L_k f) ∘ φ)`, by its closure. So the pushforward along a homomorphism with dense range is
left invariant. Hence amenability passes to the target of a continuous homomorphism with dense
range, in particular to images under surjective continuous homomorphisms and quotients, and is
invariant under isomorphisms of topological groups.

## Main definitions

* `TauCeti.Mean.IsLeftInvariant`, `TauCeti.AddMean.IsLeftInvariant`: `m (L_g f) = m f` for all `g`
  and `f`.
* `TauCeti.Mean.map φ`, `TauCeti.AddMean.map φ`: the pushforward of means along a continuous
  homomorphism `φ`.
* `TauCeti.AddMean.equivMultiplicative`: the bijection `AddMean A ≃ Mean (Multiplicative A)`.
* `TauCeti.Mean.equivAdditive`: the bijection `Mean G ≃ AddMean (Additive G)`.
* `TauCeti.Amenable G`: `UCB G` carries a left-invariant mean.
* `TauCeti.AddAmenable A`: `A` is an amenable additive topological group, defined via
  `TauCeti.Amenable (Multiplicative A)` and paired with `TauCeti.Amenable` via `@[to_additive]`.

## Main results

* `TauCeti.Mean.convex_toContinuousLinearMap_image_setOf_isLeftInvariant`: the left-invariant
  means form a convex set.
* `TauCeti.Mean.IsLeftInvariant.map`, `TauCeti.AddMean.IsLeftInvariant.map`: pushforward along a
  continuous homomorphism with dense range preserves left invariance.
* `TauCeti.AddMean.isLeftInvariant_equivMultiplicative_iff`,
  `TauCeti.Mean.isLeftInvariant_equivAdditive_iff`: the type-tag bijections preserve and reflect
  left invariance.
* `TauCeti.Amenable.of_denseRange`, `TauCeti.AddAmenable.of_denseRange`: amenability passes to the
  target of a continuous homomorphism with dense range, in particular to images under surjective
  continuous homomorphisms, ranges of continuous homomorphisms, and quotients.
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

variable {A B : Type*} [AddGroup A] [TopologicalSpace A] [IsTopologicalAddGroup A]
  [AddGroup B] [TopologicalSpace B] [IsTopologicalAddGroup B]
variable {G H K : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
  [Group K] [TopologicalSpace K] [IsTopologicalGroup K]

namespace AddMean

/-- An additive mean `m` on `AddUCB A` is left invariant when `m (L_a f) = m f` for every `a` and
`f`, where `(L_a f)(x) = f (-a + x)`. -/
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

end AddMean

namespace Mean

/-- A mean `m` on `UCB G` is left invariant when `m (L_g f) = m f` for every `g` and `f`, where
`(L_g f)(x) = f (g⁻¹ * x)`. -/
@[to_additive existing]
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
@[to_additive
  /-- The pushforward `f ↦ m (f ∘ φ)` of an additive mean `m` on `AddUCB G` along a continuous
  additive homomorphism `φ : G →ₜ+ H`, as an additive mean on `AddUCB H`. -/]
def map (φ : G →ₜ* H) (m : Mean G) : Mean H :=
  mk₀ (m.toPositiveLinearMap.toLinearMap ∘ₗ (UCB.compRightAlgHom φ).toLinearMap)
    (fun f hf => map_nonneg m (by simpa using UCB.monotone_compRightAlgHom φ hf)) (by simp)

@[to_additive (attr := simp)]
theorem map_apply (φ : G →ₜ* H) (m : Mean G) (f : UCB H) :
    m.map φ f = m (UCB.compRightAlgHom φ f) :=
  mk₀_apply _ _ _ f

/-- The pushforward along the identity is the identity. -/
@[to_additive (attr := simp) /-- The pushforward along the identity is the identity. -/]
theorem map_id (m : Mean G) : m.map (ContinuousMonoidHom.id G) = m :=
  ext fun f => by simp

/-- Pushing forward along `φ` and then along `ψ` is pushing forward along `ψ ∘ φ`. -/
@[to_additive (attr := simp)
  /-- Pushing forward along `φ` and then along `ψ` is pushing forward along `ψ ∘ φ`. -/]
theorem map_map (ψ : H →ₜ* K) (φ : G →ₜ* H) (m : Mean G) :
    (m.map φ).map ψ = m.map (ψ.comp φ) :=
  ext fun f => by simp [UCB.compRightAlgHom_comp]

/-- Pushing forward along a topological group isomorphism and then along its inverse is the
identity. -/
@[to_additive
  /-- Pushing forward along a topological additive-group isomorphism and then along its inverse is
  the identity. -/]
theorem map_symm_map (e : G ≃ₜ* H) (m : Mean G) :
    (m.map (e : G →ₜ* H)).map (e.symm : H →ₜ* G) = m := by
  rw [map_map, show ((e.symm : H →ₜ* G).comp (e : G →ₜ* H)) = ContinuousMonoidHom.id G from
    ContinuousMonoidHom.ext fun x => e.symm_apply_apply x, map_id]

end Mean

namespace AddMean

/-- The pushforward of a left-invariant additive mean along `φ` is invariant under left translation
by elements in the range of `φ`. -/
theorem IsLeftInvariant.map_apply_leftTranslation {m : AddMean A} (hm : m.IsLeftInvariant)
    (φ : A →ₜ+ B) (a : A) (f : AddUCB B) :
    m.map φ (AddUCB.leftTranslation (φ a) f) = m.map φ f := by
  rw [map_apply, map_apply, AddUCB.compRightAlgHom_leftTranslation, hm]

/-- The pushforward of a left-invariant additive mean along a continuous additive homomorphism with
dense range is left invariant. -/
theorem IsLeftInvariant.map {m : AddMean A} (hm : m.IsLeftInvariant) {φ : A →ₜ+ B}
    (hφ : DenseRange φ) : (m.map φ).IsLeftInvariant := by
  intro b f
  have hc : Continuous fun k : B => m.map φ (AddUCB.leftTranslation k f) :=
    (map_continuous (m.map φ)).comp (AddUCB.continuous_leftTranslation_apply f)
  exact hφ.induction_on (p := fun k => m.map φ (AddUCB.leftTranslation k f) = m.map φ f) b
    (isClosed_eq hc continuous_const) fun a => hm.map_apply_leftTranslation φ a f

end AddMean

namespace Mean

/-- The pushforward of a left-invariant mean along a continuous homomorphism `φ` is invariant under
left translation by the elements `φ g` of the range of `φ`. -/
theorem IsLeftInvariant.map_apply_leftTranslation {m : Mean G} (hm : m.IsLeftInvariant)
    (φ : G →ₜ* H) (g : G) (f : UCB H) :
    m.map φ (UCB.leftTranslation (φ g) f) = m.map φ f := by
  rw [map_apply, map_apply, UCB.compRightAlgHom_leftTranslation, hm]

/-- The pushforward of a left-invariant mean along a continuous homomorphism with dense range is
left invariant. -/
@[to_additive existing]
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
  ⟨fun h => h.exists_isLeftInvariant, fun h => ⟨h⟩⟩

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

section TypeTags

open Multiplicative Additive

namespace AddMean

variable {A : Type*} [AddGroup A] [TopologicalSpace A] [IsTopologicalAddGroup A]

/-- Precomposition with `AddUCB.equivMultiplicative.symm` (and its inverse
`AddUCB.equivMultiplicative`) identifies additive means on `AddUCB A` with means on
`UCB (Multiplicative A)`. -/
def equivMultiplicative : AddMean A ≃ Mean (Multiplicative A) :=
  ((equivNormalizedPositiveLinearMap A).trans
    (PositiveLinearMap.normalizedEquivOfAlgEquiv AddUCB.equivMultiplicative
      AddUCB.equivMultiplicative_symm_le_equivMultiplicative_symm_iff)).trans
    (Mean.equivNormalizedPositiveLinearMap (Multiplicative A)).symm

@[simp]
theorem equivMultiplicative_apply (m : AddMean A) (f : UCB (Multiplicative A)) :
    equivMultiplicative m f = m (AddUCB.equivMultiplicative.symm f) := by
  simp [equivMultiplicative]

@[simp]
theorem equivMultiplicative_symm_apply (m : Mean (Multiplicative A)) (f : AddUCB A) :
    equivMultiplicative.symm m f = m (AddUCB.equivMultiplicative f) := by
  simp [equivMultiplicative]

/-- `equivMultiplicative` preserves and reflects left invariance. -/
@[simp]
theorem isLeftInvariant_equivMultiplicative_iff {m : AddMean A} :
    (equivMultiplicative m).IsLeftInvariant ↔ m.IsLeftInvariant := by
  simp only [Mean.isLeftInvariant_iff, isLeftInvariant_iff, equivMultiplicative_apply,
    AddUCB.equivMultiplicative_symm_leftTranslation]
  exact ⟨fun h a f => by simpa using h (ofAdd a) (AddUCB.equivMultiplicative f),
    fun h g f => h g.toAdd (AddUCB.equivMultiplicative.symm f)⟩

/-- `equivMultiplicative.symm` preserves and reflects left invariance. -/
@[simp]
theorem isLeftInvariant_equivMultiplicative_symm_iff {m : Mean (Multiplicative A)} :
    (equivMultiplicative.symm m).IsLeftInvariant ↔ m.IsLeftInvariant := by
  rw [← isLeftInvariant_equivMultiplicative_iff, Equiv.apply_symm_apply]

/-- `equivMultiplicative` intertwines pushforward along `φ` and
`ContinuousAddMonoidHom.toMultiplicative φ`. -/
@[simp]
theorem equivMultiplicative_map {B : Type*} [AddGroup B] [TopologicalSpace B]
    [IsTopologicalAddGroup B] (φ : A →ₜ+ B) (m : AddMean A) :
    equivMultiplicative (m.map φ) =
      (equivMultiplicative m).map (ContinuousAddMonoidHom.toMultiplicative φ) :=
  Mean.ext fun _ => by simp

/-- `equivMultiplicative.symm` intertwines pushforward along
`ContinuousAddMonoidHom.toMultiplicative φ` and `φ`. -/
@[simp]
theorem equivMultiplicative_symm_map {B : Type*} [AddGroup B] [TopologicalSpace B]
    [IsTopologicalAddGroup B] (φ : A →ₜ+ B) (m : Mean (Multiplicative A)) :
    equivMultiplicative.symm (m.map (ContinuousAddMonoidHom.toMultiplicative φ)) =
      (equivMultiplicative.symm m).map φ := by
  rw [Equiv.symm_apply_eq, equivMultiplicative_map, Equiv.apply_symm_apply]

/-- `equivMultiplicative` sends additive evaluation at `a` to evaluation at `ofAdd a`. -/
@[simp]
theorem equivMultiplicative_eval (a : A) :
    equivMultiplicative (eval A a) = Mean.eval (Multiplicative A) (ofAdd a) :=
  Mean.ext fun _ => by simp

/-- `equivMultiplicative.symm` sends evaluation at `x` to additive evaluation at `x.toAdd`. -/
@[simp]
theorem equivMultiplicative_symm_eval (x : Multiplicative A) :
    equivMultiplicative.symm (Mean.eval (Multiplicative A) x) = eval A x.toAdd := by
  rw [Equiv.symm_apply_eq, equivMultiplicative_eval, ofAdd_toAdd]

end AddMean

namespace Mean

section Additive

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

variable (G) in
private def equivMultiplicativeAdditive : Mean G ≃ Mean (Multiplicative (Additive G)) where
  toFun m := m.map ((ContinuousMulEquiv.multiplicativeAdditive G).symm :
    G →ₜ* Multiplicative (Additive G))
  invFun m := m.map (ContinuousMulEquiv.multiplicativeAdditive G :
    Multiplicative (Additive G) →ₜ* G)
  left_inv m := map_symm_map (ContinuousMulEquiv.multiplicativeAdditive G).symm m
  right_inv m := map_symm_map (ContinuousMulEquiv.multiplicativeAdditive G) m

private theorem equivMultiplicativeAdditive_apply (m : Mean G) :
    equivMultiplicativeAdditive G m =
      m.map ((ContinuousMulEquiv.multiplicativeAdditive G).symm :
        G →ₜ* Multiplicative (Additive G)) :=
  (rfl)

private theorem equivMultiplicativeAdditive_symm_apply (m : Mean (Multiplicative (Additive G))) :
    (equivMultiplicativeAdditive G).symm m =
      m.map (ContinuousMulEquiv.multiplicativeAdditive G :
        Multiplicative (Additive G) →ₜ* G) :=
  (rfl)

/-- Precomposition with `UCB.equivAdditive.symm` (and its inverse `UCB.equivAdditive`) identifies
means on `UCB G` with additive means on `AddUCB (Additive G)`. -/
def equivAdditive : Mean G ≃ AddMean (Additive G) :=
  (equivMultiplicativeAdditive G).trans (AddMean.equivMultiplicative (A := Additive G)).symm

@[simp]
theorem equivAdditive_apply (m : Mean G) (f : AddUCB (Additive G)) :
    equivAdditive m f = m (UCB.equivAdditive.symm f) := by
  simp only [equivAdditive, Equiv.trans_apply, equivMultiplicativeAdditive_apply,
    AddMean.equivMultiplicative_symm_apply, map_apply]
  congr 1
  ext x
  simp

@[simp]
theorem equivAdditive_symm_apply (m : AddMean (Additive G)) (f : UCB G) :
    equivAdditive.symm m f = m (UCB.equivAdditive f) := by
  simp only [equivAdditive, Equiv.symm_trans_apply, equivMultiplicativeAdditive_symm_apply,
    map_apply, Equiv.symm_symm, AddMean.equivMultiplicative_apply]
  congr 1
  ext x
  simp

/-- `equivAdditive` preserves and reflects left invariance. -/
@[simp]
theorem isLeftInvariant_equivAdditive_iff {m : Mean G} :
    (equivAdditive m).IsLeftInvariant ↔ m.IsLeftInvariant := by
  let e := ContinuousMulEquiv.multiplicativeAdditive G
  simp only [equivAdditive, Equiv.trans_apply,
    AddMean.isLeftInvariant_equivMultiplicative_symm_iff]
  refine ⟨fun hm => ?_, fun hm =>
    hm.map (φ := (e.symm : G →ₜ* Multiplicative (Additive G))) e.symm.surjective.denseRange⟩
  have h := hm.map (φ := (e : Multiplicative (Additive G) →ₜ* G)) e.surjective.denseRange
  rwa [← equivMultiplicativeAdditive_symm_apply, Equiv.symm_apply_apply] at h

/-- `equivAdditive.symm` preserves and reflects left invariance. -/
@[simp]
theorem isLeftInvariant_equivAdditive_symm_iff {m : AddMean (Additive G)} :
    (equivAdditive.symm m).IsLeftInvariant ↔ m.IsLeftInvariant := by
  rw [← isLeftInvariant_equivAdditive_iff, Equiv.apply_symm_apply]

/-- `equivAdditive` intertwines pushforward along `φ` and `ContinuousMonoidHom.toAdditive φ`. -/
@[simp]
theorem equivAdditive_map {H : Type*} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    (φ : G →ₜ* H) (m : Mean G) :
    equivAdditive (m.map φ) = (equivAdditive m).map (ContinuousMonoidHom.toAdditive φ) :=
  AddMean.ext fun _ => by simp

/-- `equivAdditive.symm` intertwines pushforward along `ContinuousMonoidHom.toAdditive φ` and
`φ`. -/
@[simp]
theorem equivAdditive_symm_map {H : Type*} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    (φ : G →ₜ* H) (m : AddMean (Additive G)) :
    equivAdditive.symm (m.map (ContinuousMonoidHom.toAdditive φ)) =
      (equivAdditive.symm m).map φ := by
  rw [Equiv.symm_apply_eq, equivAdditive_map, Equiv.apply_symm_apply]

/-- `equivAdditive` sends evaluation at `g` to additive evaluation at `ofMul g`. -/
@[simp]
theorem equivAdditive_eval (g : G) :
    equivAdditive (eval G g) = AddMean.eval (Additive G) (ofMul g) :=
  AddMean.ext fun _ => by simp

/-- `equivAdditive.symm` sends additive evaluation at `x` to evaluation at `x.toMul`. -/
@[simp]
theorem equivAdditive_symm_eval (x : Additive G) :
    equivAdditive.symm (AddMean.eval (Additive G) x) = eval G x.toMul := by
  rw [Equiv.symm_apply_eq, equivAdditive_eval, ofMul_toMul]

end Additive

end Mean

end TypeTags

section AddAmenable

variable {A B : Type*} [AddGroup A] [TopologicalSpace A] [IsTopologicalAddGroup A]
  [AddGroup B] [TopologicalSpace B] [IsTopologicalAddGroup B]

variable (A) in
/-- An additive topological group `A` is amenable when the topological group `Multiplicative A` is
amenable. -/
class AddAmenable : Prop where
  /-- `Multiplicative A` is amenable when `A` is additively amenable. -/
  amenable_multiplicative : Amenable (Multiplicative A)

insert_to_additive_translation TauCeti.Amenable TauCeti.AddAmenable

instance [AddAmenable A] : Amenable (Multiplicative A) :=
  AddAmenable.amenable_multiplicative

instance {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [Amenable G] :
    AddAmenable (Additive G) :=
  ⟨(ContinuousMulEquiv.multiplicativeAdditive G).amenable_iff.2 ‹_›⟩

/-- `Multiplicative A` is amenable if and only if `A` is additively amenable. -/
@[simp]
theorem amenable_multiplicative_iff : Amenable (Multiplicative A) ↔ AddAmenable A :=
  ⟨fun h => ⟨h⟩, fun h => h.amenable_multiplicative⟩

/-- `Additive G` is additively amenable if and only if `G` is amenable. -/
@[simp]
theorem addAmenable_additive_iff {G : Type*} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] : AddAmenable (Additive G) ↔ Amenable G :=
  ⟨fun _ => (ContinuousMulEquiv.multiplicativeAdditive G).amenable_iff.1 inferInstance,
    fun _ => inferInstance⟩

variable (A) in
/-- An additive topological group is amenable exactly when `AddUCB A` carries a left-invariant
additive mean. -/
theorem addAmenable_iff : AddAmenable A ↔ ∃ m : AddMean A, m.IsLeftInvariant := by
  rw [← amenable_multiplicative_iff, amenable_iff]
  exact ⟨fun ⟨m, hm⟩ => ⟨AddMean.equivMultiplicative.symm m, by simpa using hm⟩,
    fun ⟨m, hm⟩ => ⟨AddMean.equivMultiplicative m, by simpa using hm⟩⟩

attribute [to_additive existing addAmenable_iff] amenable_iff

/-- An amenable additive topological group carries a left-invariant additive mean on
`AddUCB A`. -/
theorem AddAmenable.exists_isLeftInvariant [AddAmenable A] :
    ∃ m : AddMean A, m.IsLeftInvariant :=
  (addAmenable_iff A).1 ‹_›

attribute [to_additive existing] Amenable.exists_isLeftInvariant

/-- The target of a continuous additive homomorphism with dense range from an amenable additive
topological group is amenable; in particular, so is the image under a surjective continuous
additive homomorphism. -/
theorem AddAmenable.of_denseRange [AddAmenable A] (φ : A →ₜ+ B) (hφ : DenseRange φ) :
    AddAmenable B :=
  ⟨.of_denseRange φ.toMultiplicative (φ.denseRange_toMultiplicative_iff.2 hφ)⟩

attribute [to_additive existing] Amenable.of_denseRange

omit [TopologicalSpace A] [IsTopologicalAddGroup A] in
/-- Additive amenability passes from a finer additive-group topology to a coarser one. -/
theorem AddAmenable.of_le {t₁ t₂ : TopologicalSpace A}
    [@IsTopologicalAddGroup A t₁ _] [@IsTopologicalAddGroup A t₂ _] (h : t₁ ≤ t₂)
    (ha : @AddAmenable A _ t₁ _) : @AddAmenable A _ t₂ _ := by
  let φ : @ContinuousAddMonoidHom A A _ _ t₁ t₂ :=
    @ContinuousAddMonoidHom.mk A A _ _ t₁ t₂ (AddMonoidHom.id A) (continuous_id_of_le h)
  exact @AddAmenable.of_denseRange A A _ t₁ _ _ t₂ _ ha φ
    (@Function.Surjective.denseRange A t₂ A _ fun x => ⟨x, AddMonoidHom.id_apply A x⟩)

attribute [to_additive existing] Amenable.of_le

end AddAmenable

end TauCeti

namespace ContinuousAddEquiv

open TauCeti

variable {A B : Type*} [AddGroup A] [TopologicalSpace A] [IsTopologicalAddGroup A]
  [AddGroup B] [TopologicalSpace B] [IsTopologicalAddGroup B]

/-- Additive amenability is invariant under topological additive-group isomorphisms. -/
theorem addAmenable_iff (e : A ≃ₜ+ B) : AddAmenable A ↔ AddAmenable B := by
  rw [← amenable_multiplicative_iff, ← amenable_multiplicative_iff, e.toMultiplicative.amenable_iff]

attribute [to_additive existing ContinuousAddEquiv.addAmenable_iff] ContinuousMulEquiv.amenable_iff

end ContinuousAddEquiv
