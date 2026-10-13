/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Homological.ContCohomology.Evens.IndexTwoNorm

/-!
# Naturality of the index-two graph class

Let `U` be an open subgroup of index two in a topological group `G`, and `α : U → 𝔽₂` a
continuous homomorphism, with graph class `N^{Ev}[α] ∈ H²(G, 𝔽₂)`
(`TauCeti.ContCohomology.graphClass`). A continuous homomorphism `φ : H → G` pulls `U` back to
the open subgroup `φ⁻¹(U)` of `H` and `α` back to `α ∘ φ` on it. When `φ⁻¹(U)` again has index
two, pulling the graph class back along `φ` gives the graph class of the pulled-back data:

```text
φ^* N^{Ev}_U[α] = N^{Ev}_{φ⁻¹(U)}[α ∘ φ]      in H²(H, 𝔽₂).
```

On cochains this is `TauCeti.ContCohomology.evensGraphCochain_comap`, the graph cochain at an
element `s` of `H` outside `φ⁻¹(U)` being the graph cochain at `φ s`, composed with `φ × φ`.

Since inner automorphisms of `G` act trivially on `H²(G, 𝔽₂)`, the case of conjugation by an
element `g` of `G` says that the graph class is unchanged when `U` and `α` are transported by
conjugation. This is the input for showing that the index-two norm attached to a quadratic
extension of fields does not depend on the chosen embedding into a separable closure: two
embeddings identify the absolute Galois group of the extension with its fixing subgroup by maps
that differ by an inner automorphism of the absolute Galois group of the base.

## Main results

* `TauCeti.ContCohomology.trivialF2Map_graphClass`: pullback of the graph class along a continuous
  homomorphism is the graph class of the pulled-back subgroup and homomorphism.
* `TauCeti.ContCohomology.graphClass_comp_of_conj`: the graph class is invariant under conjugation.
* `TauCeti.ContCohomology.trivialF2Map_evensNormIndexTwo`: the index-two norm is natural under
  pullback when the inverse-image subgroup still has index two.
* `TauCeti.ContCohomology.evensNormIndexTwo_comp_of_conj`: the index-two norm is invariant under
  conjugation of the subgroup and its input class.

## References

* L. Evens, *A generalization of the transfer map in the cohomology of groups*, Trans. Amer.
  Math. Soc. **108** (1963), 54–65.
-/

public section

open CategoryTheory

namespace TauCeti.ContCohomology

universe u

variable {G H : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [LocallyCompactSpace G] [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
  [LocallyCompactSpace H]

attribute [local instance] TopRep.distribMulAction TopRep.smulCommClass

/-- A group acts continuously on its trivial coefficients `𝔽₂`, which are smooth discrete. -/
local instance continuousSMul_trivialF2_naturality (K : Type u) [Group K] [TopologicalSpace K]
    [IsTopologicalGroup K] : ContinuousSMul K (trivialF2 K).V :=
  (isSmoothDiscrete_trivialF2 K).continuousSMul

/-- **Naturality of the graph class.** For a continuous homomorphism `φ : H → G`, an open
subgroup `U` of index two in `G` whose preimage `φ⁻¹(U)` also has index two, and a continuous
homomorphism `α : U → 𝔽₂`, pulling the graph class of `α` back along `φ` gives the graph class of
`α ∘ φ` on `φ⁻¹(U)`. -/
theorem trivialF2Map_graphClass (φ : H →ₜ* G) (U : OpenSubgroup G)
    (hU : U.toSubgroup.index = 2) (hφU : (U.comap (φ : H →* G) φ.continuous).toSubgroup.index = 2)
    (α : U.toSubgroup →* Multiplicative (ZMod 2)) (hα : Continuous α) :
    trivialF2Map φ 2 (graphClass U hU α hα) =
      graphClass (U.comap (φ : H →* G) φ.continuous) hφU
        (α.comp ((φ : H →* G).subgroupComap U.toSubgroup))
        (hα.comp (φ.continuous.subtype_map fun _ hx => hx)) := by
  obtain ⟨s, hs, -⟩ := Subgroup.index_eq_two_iff_exists_notMem_and.mp hφU
  have hφs : φ s ∉ U := fun h => hs (OpenSubgroup.mem_comap.2 h)
  rw [graphClass_eq_evensGraphCochainClass U hU (φ s) hφs α hα,
    graphClass_eq_evensGraphCochainClass _ hφU s hs, evensGraphCochainClass_def U,
    evensGraphCochainClass_def (U.comap (φ : H →* G) φ.continuous)]
  have hmap := eqToHom_comp_trivialF2Map φ (ofDiscreteModule_trivialF2 G)
    (ofDiscreteModule_trivialF2 H) trivialF2CoeffHom (trivialF2CoeffHom_smul (φ : H →* G))
    (fun m ↦ by
      simp [eqToHom_ofDiscreteModule_trivialF2_apply]) 2
  have happ := ConcreteCategory.congr_hom hmap
    (explicitH2AddEquivContinuousCohomology G (trivialF2 G).V
      (evensGraphCocycle U (φ s) α hU hφs hα))
  rw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply,
    explicitH2AddEquivContinuousCohomology_map G (trivialF2 G).V H (trivialF2 H).V φ
      trivialF2CoeffHom (trivialF2CoeffHom_smul (φ : H →* G)), explicitMap2_mk] at happ
  rw [happ]
  congr 3
  ext ⟨h, k⟩
  simp only [cocyclesMap2_apply, coe_evensGraphCocycle, trivialF2CoeffHom_apply,
    AddEquiv.apply_symm_apply]
  exact congrArg _ (evensGraphCochain_comap (φ : H →* G) U.toSubgroup s α h k).symm

/-- **The graph class is invariant under conjugation.** For `g : G`, open subgroups `U` and `V` of
index two with `V = gUg⁻¹`, and a continuous `κ : V → U` with `κ v = g⁻¹ v g`, the graph class of
`α ∘ κ` on `V` is the graph class of `α` on `U`. The equality `V = gUg⁻¹` is not a hypothesis: `κ`
places `V` inside `gUg⁻¹`, and both have index two. -/
theorem graphClass_comp_of_conj (U V : OpenSubgroup G) (hU : U.toSubgroup.index = 2)
    (hV : V.toSubgroup.index = 2) (g : G) (κ : V.toSubgroup →ₜ* U.toSubgroup)
    (hκ : ∀ v : V.toSubgroup, (κ v : G) = g⁻¹ * v * g)
    (α : U.toSubgroup →* Multiplicative (ZMod 2)) (hα : Continuous α) :
    graphClass V hV (α.comp κ) (hα.comp κ.continuous) = graphClass U hU α hα := by
  -- Conjugation `x ↦ g⁻¹ x g` is inner, so it acts trivially on `H²(G, 𝔽₂)`; by naturality the
  -- graph class of `α` is therefore that of its pullback to `U.comap c`, which is `V`.
  let c : G →ₜ* G := ContinuousMonoidHom.toContinuousMonoidHom (ContinuousAut.conj g⁻¹)
  have hc (x : G) : (c : G →* G) x = g⁻¹ * x * g := by simp [c]
  have hcid : trivialF2Map c 2 = 𝟙 _ := by
    rw [trivialF2Map_eq_of_conj (ContinuousMonoidHom.id G) c g⁻¹ (fun x => (hc x).trans (by simp)),
      trivialF2Map_id]
  have hVW : V = U.comap (c : G →* G) c.continuous := by
    have hle : V.toSubgroup ≤ (U.comap (c : G →* G) c.continuous).toSubgroup := fun v hv =>
      Subgroup.mem_comap.2 (by rw [hc, ← hκ ⟨v, hv⟩]; exact (κ ⟨v, hv⟩).2)
    have hW : (U.comap (c : G →* G) c.continuous).toSubgroup.index = 2 := by
      rw [OpenSubgroup.toSubgroup_comap, Subgroup.index_comap_of_surjective U.toSubgroup
        fun y => ⟨g * y * g⁻¹, by rw [hc]; group⟩, hU]
    refine OpenSubgroup.toSubgroup_injective (le_antisymm hle (Subgroup.relIndex_eq_one.1 ?_))
    have h := Subgroup.relIndex_mul_index hle
    rw [hV, hW] at h
    omega
  subst hVW
  calc graphClass _ hV (α.comp κ) (hα.comp κ.continuous)
      = graphClass _ hV (α.comp ((c : G →* G).subgroupComap U.toSubgroup))
          (hα.comp (c.continuous.subtype_map fun _ hx => hx)) := by
        congr 1
        exact MonoidHom.ext fun v => congrArg α <| Subtype.ext (a1 := κ v)
          (a2 := (c : G →* G).subgroupComap U.toSubgroup v) ((hκ v).trans (hc v).symm)
    _ = trivialF2Map c 2 (graphClass U hU α hα) := (trivialF2Map_graphClass c U hU hV α hα).symm
    _ = graphClass U hU α hα := by rw [hcid, ConcreteCategory.id_apply]

/-- **Naturality of the index-two Evens norm.** If `φ : H → G` pulls an index-two open subgroup
`U` back to another index-two subgroup, then pulling the norm back along `φ` is the norm of the
pulled-back degree-one class. -/
@[simp]
theorem trivialF2Map_evensNormIndexTwo (φ : H →ₜ* G) (U : OpenSubgroup G)
    (hU : U.toSubgroup.index = 2)
    (hφU : (U.comap (φ : H →* G) φ.continuous).toSubgroup.index = 2)
    (x : continuousCohomology 1 (trivialF2 U.toSubgroup)) :
    trivialF2Map φ 2 (evensNormIndexTwo U hU x) =
      evensNormIndexTwo (U.comap (φ : H →* G) φ.continuous) hφU
        (trivialF2Map
          (⟨(φ : H →* G).subgroupComap U.toSubgroup,
            φ.continuous.subtype_map fun _ hx => hx⟩ :
            (U.comap (φ : H →* G) φ.continuous).toSubgroup →ₜ* U.toSubgroup) 1 x) := by
  obtain ⟨α, hα, rfl⟩ := homClass_surjective U.toSubgroup x
  rw [evensNormIndexTwo_homClass, trivialF2Map_homClass,
    evensNormIndexTwo_homClass]
  convert trivialF2Map_graphClass φ U hU hφU α hα using 1

/-- **The index-two Evens norm is invariant under conjugation.** Suppose `κ : V → U` is
conjugation by `g⁻¹` between two index-two open subgroups. Pulling a degree-one class from `U`
along `κ` and taking its norm from `V` gives the original norm from `U`. -/
theorem evensNormIndexTwo_comp_of_conj (U V : OpenSubgroup G)
    (hU : U.toSubgroup.index = 2) (hV : V.toSubgroup.index = 2) (g : G)
    (κ : V.toSubgroup →ₜ* U.toSubgroup) (hκ : ∀ v : V.toSubgroup, (κ v : G) = g⁻¹ * v * g)
    (x : continuousCohomology 1 (trivialF2 U.toSubgroup)) :
    evensNormIndexTwo V hV (trivialF2Map κ 1 x) = evensNormIndexTwo U hU x := by
  obtain ⟨α, hα, rfl⟩ := homClass_surjective U.toSubgroup x
  rw [trivialF2Map_homClass, evensNormIndexTwo_homClass, evensNormIndexTwo_homClass,
    graphClass_comp_of_conj U V hU hV g κ hκ]

end TauCeti.ContCohomology
