/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Chevalley.Elementary
public import TauCeti.Algebra.AlgebraicGroup.Chevalley.Torus.Equivariance
public import TauCeti.GroupTheory.Subgroup.NormalizedJoin

/-!
# Extending elementary Chevalley comparisons by the actual torus

Let `D` and `E` be Chevalley data with `Λ(E) ≤ Λ(D)`. A homomorphism from the elementary
subgroup of `D` to the points of `E` matching all root parameters automatically intertwines
torus conjugation. It extends uniquely to the root-and-torus-generated group, with the torus
map given by restriction of characters, exactly when these maps agree on the intersection
of the elementary subgroup and the actual torus.

`extendElementaryHom` performs this extension. Its value on an elementary element followed
by a torus point is the product of the prescribed images, independently of the chosen
factorization. Its image lies in the extended elementary subgroup of `E`.

This is the gluing step in comparison of admissible lattices. Neither existence of the
initial elementary homomorphism nor a description of the elementary–torus intersection is
assumed to have been proved here. No identification with all scheme points, or surjectivity
of restriction on torus points, is used. In particular the construction works over arbitrary
commutative rings, with the actual character lattices rather than the full-weight torus image.

The construction combines `Subgroup.liftSupOfRightLeNormalizer` with
`ChevalleyDatum.comp_rootGeneratedTorusAction` and `ChevalleyDatum.torusRestriction`.

## References

* R. Steinberg, *Lectures on Chevalley Groups*, Chapter 3, Lemma 28(c) and Corollary 5 to
  Theorem 4′.
* J. C. Jantzen, *Representations of Algebraic Groups*, II.1.
-/

public section

namespace TauCeti.DynkinType.ChevalleyDatum

noncomputable section

variable {t : DynkinType} {ht : t.Valid} (D E : ChevalleyDatum t ht)
  {A : Type*} [CommRing A] (h : E.weightLattice ≤ D.weightLattice)
  (f : D.elementarySubgroup A →* E.points A)
  (hf : ∀ γ u, f ⟨D.rootSubgroupPoints γ A u,
    D.rootSubgroupPoints_mem_elementarySubgroup A γ u⟩ = E.rootSubgroupPoints γ A u)

include hf

/-- A root-preserving elementary comparison extends uniquely with the prescribed actual torus
map if it agrees with that map wherever an actual torus point is elementary. -/
theorem existsUnique_extendElementaryHom
    (hcompat : ∀ s (hs : D.torusPoints A s ∈ D.elementarySubgroup A),
      f ⟨D.torusPoints A s, hs⟩ = E.torusPoints A (D.torusRestriction E h s)) :
    ∃! F : D.extendedElementarySubgroup A →* E.points A,
      (∀ e : D.elementarySubgroup A,
        F ⟨e, D.elementarySubgroup_le_extendedElementarySubgroup A e.property⟩ = f e) ∧
      ∀ s, F ⟨D.torusPoints A s, D.torusPoints_mem_extendedElementarySubgroup A s⟩ =
        E.torusPoints A (D.torusRestriction E h s) := by
  -- Identify the actual torus image with its parameters, then use lattice restriction.
  let e := MonoidHom.ofInjective (D.torusPoints_injective A)
  let g := (E.torusPoints A).comp ((D.torusRestriction E h).comp e.symm.toMonoidHom)
  have hg (s : Fin t.rank → Aˣ) :
      g ⟨D.torusPoints A s, ⟨s, rfl⟩⟩ = E.torusPoints A (D.torusRestriction E h s) := by
    exact congrArg ((E.torusPoints A).comp (D.torusRestriction E h)) (e.symm_apply_apply s)
  have hconj (b : (D.torusPoints A).range) :
      f.comp (((D.elementarySubgroup A).normalizerMonoidHom.comp
        (Subgroup.inclusion (D.range_torusPoints_le_normalizer_elementarySubgroup A)))
          b).toMonoidHom = (MulAut.conj (g b)).toMonoidHom.comp f := by
    obtain ⟨s, hs⟩ := b.property
    have hb : b = ⟨D.torusPoints A s, ⟨s, rfl⟩⟩ := Subtype.ext hs.symm
    subst b
    apply MonoidHom.ext
    intro a
    let i := MulEquiv.subgroupCongr (D.elementarySubgroup_def A)
    have hi : ∀ γ u, (f.comp i.symm.toMonoidHom)
        ⟨D.rootSubgroupPoints γ A u,
          Subgroup.subset_closure (Set.mem_iUnion.mpr ⟨γ, u, rfl⟩)⟩ =
        E.rootSubgroupPoints γ A u := fun γ u => hf γ u
    have hact := D.map_rootGeneratedTorusAction E A h (f.comp i.symm.toMonoidHom) hi s (i a)
    -- The subgroup equivalence changes membership proofs, not ambient conjugation.
    have harg : i.symm (D.rootGeneratedTorusAction A s (i a)) =
        (((D.elementarySubgroup A).normalizerMonoidHom.comp
          (Subgroup.inclusion (D.range_torusPoints_le_normalizer_elementarySubgroup A)))
            ⟨D.torusPoints A s, ⟨s, rfl⟩⟩) a := by
      apply Subtype.ext
      exact D.coe_rootGeneratedTorusAction A s (i a)
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, harg] at hact
    exact hact.trans (congrArg (fun z => z * f a * z⁻¹) (hg s).symm)
  have hagree (a : ↥(D.elementarySubgroup A ⊓ (D.torusPoints A).range)) :
      f ⟨a, a.property.1⟩ = g ⟨a, a.property.2⟩ := by
    obtain ⟨s, hs⟩ := a.property.2
    have ha : (a : D.points A) = D.torusPoints A s := hs.symm
    simpa only [ha, hg] using hcompat s (ha ▸ a.property.1)
  -- Descend the two equivariant maps to their join and transport to the named group.
  let q := MulEquiv.subgroupCongr (D.extendedElementarySubgroup_def A)
  let l := Subgroup.liftSupOfRightLeNormalizer _ _
    (D.range_torusPoints_le_normalizer_elementarySubgroup A) f g hconj hagree
  let F := l.comp q.toMonoidHom
  refine ⟨F, ⟨?_, ?_⟩, ?_⟩
  · intro a
    exact Subgroup.liftSupOfRightLeNormalizer_left _ _ _ f g hconj hagree a
  · intro s
    exact (Subgroup.liftSupOfRightLeNormalizer_right _ _ _ f g hconj hagree
      ⟨D.torusPoints A s, ⟨s, rfl⟩⟩).trans (hg s)
  · rintro F' ⟨hleft, hright⟩
    have heq : F'.comp q.symm.toMonoidHom = l := by
      apply Subgroup.eq_liftSupOfRightLeNormalizer _ _ _ f g hconj hagree
      · exact MonoidHom.ext fun a => hleft a
      · apply MonoidHom.ext
        intro b
        obtain ⟨s, hs⟩ := b.property
        have hb : b = ⟨D.torusPoints A s, ⟨s, rfl⟩⟩ := Subtype.ext hs.symm
        subst b
        exact (hright s).trans (hg s).symm
    exact MonoidHom.ext fun x => DFunLike.congr_fun heq (q x)

variable
  (hcompat : ∀ s (hs : D.torusPoints A s ∈ D.elementarySubgroup A),
    f ⟨D.torusPoints A s, hs⟩ = E.torusPoints A (D.torusRestriction E h s))

/-- Extend a root-preserving elementary comparison by restriction on the actual torus.
Agreement on the elementary–torus intersection is the only additional compatibility required. -/
def extendElementaryHom : D.extendedElementarySubgroup A →* E.points A :=
  (D.existsUnique_extendElementaryHom E h f hf hcompat).exists.choose

/-- The extended comparison agrees with the original elementary homomorphism. -/
@[simp]
theorem extendElementaryHom_elementary (e : D.elementarySubgroup A) :
    D.extendElementaryHom E h f hf hcompat
      ⟨e, D.elementarySubgroup_le_extendedElementarySubgroup A e.property⟩ = f e :=
  (D.existsUnique_extendElementaryHom E h f hf hcompat).exists.choose_spec.1 e

/-- The extended comparison maps the actual torus by restriction of characters. -/
@[simp]
theorem extendElementaryHom_torusPoints (s : Fin t.rank → Aˣ) :
    D.extendElementaryHom E h f hf hcompat
      ⟨D.torusPoints A s, D.torusPoints_mem_extendedElementarySubgroup A s⟩ =
      E.torusPoints A (D.torusRestriction E h s) :=
  (D.existsUnique_extendElementaryHom E h f hf hcompat).exists.choose_spec.2 s

/-- On any elementary–torus factorization, the extension is the product of the prescribed
images. The formula does not depend on the factorization. -/
@[simp]
theorem extendElementaryHom_mul_torusPoints (e : D.elementarySubgroup A)
    (s : Fin t.rank → Aˣ) :
    D.extendElementaryHom E h f hf hcompat
      ⟨(e : D.points A) * D.torusPoints A s,
        (D.extendedElementarySubgroup A).mul_mem
          (D.elementarySubgroup_le_extendedElementarySubgroup A e.property)
          (D.torusPoints_mem_extendedElementarySubgroup A s)⟩ =
      f e * E.torusPoints A (D.torusRestriction E h s) := by
  exact (map_mul (D.extendElementaryHom E h f hf hcompat)
    ⟨e, D.elementarySubgroup_le_extendedElementarySubgroup A e.property⟩
    ⟨D.torusPoints A s, D.torusPoints_mem_extendedElementarySubgroup A s⟩).trans
      (congrArg₂ (· * ·) (D.extendElementaryHom_elementary E h f hf hcompat e)
        (D.extendElementaryHom_torusPoints E h f hf hcompat s))

/-- The extension preserves every root parameter. -/
@[simp]
theorem extendElementaryHom_rootSubgroupPoints (γ : Fin t.numRoots) (u : Multiplicative A) :
    D.extendElementaryHom E h f hf hcompat
      ⟨D.rootSubgroupPoints γ A u,
        D.elementarySubgroup_le_extendedElementarySubgroup A
          (D.rootSubgroupPoints_mem_elementarySubgroup A γ u)⟩ =
      E.rootSubgroupPoints γ A u :=
  (D.extendElementaryHom_elementary E h f hf hcompat _).trans (hf γ u)

/-- The prescribed elementary and torus restrictions characterize the extension. -/
theorem eq_extendElementaryHom (F : D.extendedElementarySubgroup A →* E.points A)
    (he : ∀ e : D.elementarySubgroup A,
      F ⟨e, D.elementarySubgroup_le_extendedElementarySubgroup A e.property⟩ = f e)
    (hs : ∀ s, F ⟨D.torusPoints A s, D.torusPoints_mem_extendedElementarySubgroup A s⟩ =
      E.torusPoints A (D.torusRestriction E h s)) :
    F = D.extendElementaryHom E h f hf hcompat :=
  (D.existsUnique_extendElementaryHom E h f hf hcompat).unique ⟨he, hs⟩
    ⟨D.extendElementaryHom_elementary E h f hf hcompat,
      D.extendElementaryHom_torusPoints E h f hf hcompat⟩

/-- Agreement on the elementary–torus intersection is necessary as well as sufficient for
an extension with the prescribed restrictions. -/
theorem exists_extendElementaryHom_iff :
    (∃ F : D.extendedElementarySubgroup A →* E.points A,
      (∀ e : D.elementarySubgroup A,
        F ⟨e, D.elementarySubgroup_le_extendedElementarySubgroup A e.property⟩ = f e) ∧
      ∀ s, F ⟨D.torusPoints A s, D.torusPoints_mem_extendedElementarySubgroup A s⟩ =
        E.torusPoints A (D.torusRestriction E h s)) ↔
      ∀ s (hs : D.torusPoints A s ∈ D.elementarySubgroup A),
        f ⟨D.torusPoints A s, hs⟩ = E.torusPoints A (D.torusRestriction E h s) := by
  constructor
  · rintro ⟨F, he, hs⟩ s hmem
    exact (he ⟨D.torusPoints A s, hmem⟩).symm.trans (hs s)
  · intro hc
    exact (D.existsUnique_extendElementaryHom E h f hf hc).exists

/-- The extension takes values in the target's root-and-actual-torus-generated subgroup,
not merely in its ambient point group. -/
theorem range_extendElementaryHom_le :
    (D.extendElementaryHom E h f hf hcompat).range ≤ E.extendedElementarySubgroup A := by
  rintro _ ⟨x, rfl⟩
  obtain ⟨a, ha, s, has⟩ := (D.mem_extendedElementarySubgroup_iff A x).mp x.property
  have hx : x = ⟨a * D.torusPoints A s,
      (D.extendedElementarySubgroup A).mul_mem
        (D.elementarySubgroup_le_extendedElementarySubgroup A ha)
        (D.torusPoints_mem_extendedElementarySubgroup A s)⟩ := Subtype.ext has.symm
  rw [hx, D.extendElementaryHom_mul_torusPoints E h f hf hcompat ⟨a, ha⟩ s]
  apply (E.extendedElementarySubgroup A).mul_mem
  · have hmap : D.elementarySubgroup A ≤
        ((E.extendedElementarySubgroup A).comap f).map (D.elementarySubgroup A).subtype := by
      rw [D.elementarySubgroup_le_iff]
      intro γ u
      exact ⟨⟨D.rootSubgroupPoints γ A u,
        D.rootSubgroupPoints_mem_elementarySubgroup A γ u⟩,
        by simpa only [SetLike.mem_coe, Subgroup.mem_comap, hf] using
          E.elementarySubgroup_le_extendedElementarySubgroup A
            (E.rootSubgroupPoints_mem_elementarySubgroup A γ u), rfl⟩
    obtain ⟨b, hb, hab⟩ := hmap ha
    have : b = (⟨a, ha⟩ : D.elementarySubgroup A) := Subtype.ext hab
    exact this ▸ hb
  · exact E.torusPoints_mem_extendedElementarySubgroup A _

end

end TauCeti.DynkinType.ChevalleyDatum
