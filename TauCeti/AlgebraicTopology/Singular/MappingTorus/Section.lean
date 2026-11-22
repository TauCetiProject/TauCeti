/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Singular.MappingTorus.Wang
public import TauCeti.Topology.MappingTorus.Section

/-!
# The Wang boundary of the classes swept by a family of sections

Let `φ : F ≃ₜ F` be a homeomorphism and let `s : K × UnitAddCircle → T_φ` be a family of sections
of the mapping torus, `s (k, θ)` lying over `θ`. Read on the mapping torus of the identity of `K`,
which is `K × UnitAddCircle` (`TauCeti.MappingTorus.reflHomeomorph`), it is a map
`s' : T_{𝟙_K} → T_φ`, and it sweeps out the classes `s'_* z ∈ Hₙ₊₁(T_φ)`. For a loop of
sections, `K` is a circle and `s'` is a torus in `T_φ`.

The Wang connecting morphism `∂ : Hₙ₊₁(T_φ) ⟶ Hₙ(F)` of these classes is carried by the points
where the sections cross the fibre at height zero:

`∂ (s'_* z) = g_* (∂ z)`,

where `g : K → F` is the family of fibre coordinates at height zero, `mk φ (g k) 0 = s (k, 0)`, and
`∂ z ∈ Hₙ(K)` is the Wang connecting morphism of the mapping torus of the identity
(`TauCeti.MappingTorus.singularHomologyMap_comp_wangδ_of_section`). The monodromy `φ` enters only
through `s`. For a family of seamed paths `ℓ : K → SeamedPath φ`, whose sections are
`TauCeti.SeamedPath.sectionFamily`, the map `g` takes `k` to the start point of `ℓ k`
(`TauCeti.SeamedPath.singularHomologyMap_sectionFamily_comp_wangδ`), so `∂ (s'_* z) = g_* (∂ z)`
for every class `z` of `T_{𝟙_K} = K × S¹`. For a loop of seamed paths `u ↦ γ_u`, `K` is a circle,
and the formula `∂ (im [γ_u]) = [u ↦ γ_u(0)]` for the class of the torus swept by the loop in the
Floer–Novikov theory of a symplectomorphism follows once the Wang boundary `∂` of the oriented torus
class of `K × S¹` is identified with the class of the circle `K`, which is not proved here.

The proof is naturality of the Wang connecting morphism for maps of infinite cyclic covers
(`TauCeti.MappingTorus.singularHomologyMap_descend_comp_wangδ`). Read on the cylinders through the
fibre coordinates, the family of sections is a map `K × ℝ → F × ℝ` intertwining the deck
transformations (`TauCeti.MappingTorus.semiconj_sectionCylinderMap_deck`), from which `s'`
descends (`TauCeti.MappingTorus.descend_sectionCylinderMap`), and at height zero it is `g`.

## Main results

* `TauCeti.MappingTorus.singularHomologyMap_comp_wangδ_of_section`: the Wang connecting morphism
  of a class swept by a family of sections is carried by the fibre coordinates at height zero.
* `TauCeti.SeamedPath.singularHomologyMap_sectionFamily_comp_wangδ`: for a family of seamed paths,
  by their start points.

## References

* A. Hatcher, *Algebraic Topology*, Section 2.2, Example 2.48, for the Wang sequence of a mapping
  torus.
* J. Milnor, *Infinite cyclic coverings*, Conference on the Topology of Manifolds (1968),
  Section 1.
* Y.-J. Lee, *Reidemeister torsion in Floer–Novikov theory and counting pseudo-holomorphic tori,
  I*, arXiv:math/0111313, Section 3.1, for the classes swept by loops of sections of a mapping
  torus.
-/

public section

noncomputable section

open CategoryTheory Limits AlgebraicTopology

universe w v u

namespace TauCeti

variable {F K : Type w} [TopologicalSpace F] [TopologicalSpace K] (φ : F ≃ₜ F)
  {A : Type u} [Category.{v} A] [HasCoproducts.{w} A] [Abelian A] (R : A)

namespace MappingTorus

/-- **The Wang boundary of a class swept by a family of sections.** Let
`s : K × UnitAddCircle → T_φ` be a family of sections, `s (k, θ)` over `θ`, read on
`T_{𝟙_K} = K × UnitAddCircle`, and let `g : K → F` be its fibre coordinates at height zero,
`mk φ (g k) 0 = s (k, 0)`. Then the Wang connecting morphism of `T_φ` on the classes swept by `s`
is `g_*` of the Wang connecting morphism of `T_{𝟙_K}`. -/
@[reassoc]
theorem singularHomologyMap_comp_wangδ_of_section (s : C(K × UnitAddCircle, MappingTorus φ))
    (hs : ∀ k θ, proj φ (s (k, θ)) = θ) (g : C(K, F)) (hg : ∀ k, mk φ (g k) 0 = s (k, 0))
    (n : ℕ) :
    ((singularHomologyFunctor A (n + 1)).obj R).map (TopCat.ofHom (s.comp
        (reflHomeomorph (F := K) : C(MappingTorus (Homeomorph.refl K), K × UnitAddCircle)))) ≫
        wangδ φ R n =
      wangδ (Homeomorph.refl K) R n ≫
        ((singularHomologyFunctor A n).obj R).map (TopCat.ofHom g) := by
  rw [← descend_sectionCylinderMap φ s hs]
  refine singularHomologyMap_descend_comp_wangδ _ R φ _ _ g (fun k ↦ ?_) n
  rw [sectionCylinderMap_apply, fiberCoord_eq_iff φ (hs k _)]
  simpa using hg k

end MappingTorus

namespace SeamedPath

open MappingTorus

/-- **The Wang boundary of a class swept by a family of seamed paths.** For a family of seamed
paths `ℓ : K → SeamedPath φ`, read through their sections on `T_{𝟙_K} = K × UnitAddCircle`, the
Wang connecting morphism of `T_φ` on the swept classes is `g_*` of the Wang connecting morphism of
`T_{𝟙_K}`, where `g k` is the start point of `ℓ k`. With `K` a circle, this reduces the Wang
boundary of the torus swept by a loop of seamed paths `u ↦ γ_u` to `g_*` of the Wang boundary of
the torus class of `K × S¹`. -/
@[reassoc]
theorem singularHomologyMap_sectionFamily_comp_wangδ (ℓ : C(K, SeamedPath φ)) (g : C(K, F))
    (hg : ∀ k, (ℓ k).val 0 = g k) (n : ℕ) :
    ((singularHomologyFunctor A (n + 1)).obj R).map (TopCat.ofHom ((sectionFamily φ ℓ).comp
        (reflHomeomorph (F := K) : C(MappingTorus (Homeomorph.refl K), K × UnitAddCircle)))) ≫
        wangδ φ R n =
      wangδ (Homeomorph.refl K) R n ≫
        ((singularHomologyFunctor A n).obj R).map (TopCat.ofHom g) :=
  singularHomologyMap_comp_wangδ_of_section φ R _ (proj_sectionFamily φ ℓ) g
    (fun k ↦ by rw [sectionFamily_zero, hg]) n

end SeamedPath

end TauCeti
