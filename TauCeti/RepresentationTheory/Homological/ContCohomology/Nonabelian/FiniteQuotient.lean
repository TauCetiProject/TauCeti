/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Limits.Types.Filtered
public import TauCeti.RepresentationTheory.Homological.ContCohomology.Nonabelian.Inflation

/-!
# Continuous nonabelian first cohomology as a colimit over finite quotients

Let a group `G` with a topology act on a group `A` with a topology by group automorphisms. For
normal subgroups `M ≤ N` of `G`, the quotient homomorphism `G ⧸ M → G ⧸ N` and the inclusion of
fixed points `Aᴺ ↪ Aᴹ` induce the **transition map**

`H¹(G ⧸ N, Aᴺ) → H¹(G ⧸ M, Aᴹ)`,

which sends the class of a cocycle `d` to the class of `gM ↦ d(gN)`. It is the inflation along
`G ⧸ M → G ⧸ N`, and it is compatible with inflation to `G`: inflating from `G ⧸ N` through
`G ⧸ M` is inflating from `G ⧸ N` directly. Since inflation `H¹(G ⧸ M, Aᴹ) → H¹(G, A)` is
injective, so is every transition map, and the transitions satisfy the identity and composition
laws. None of this needs compactness, openness of the subgroups, discreteness of `A` or
continuity of the action.

Over the open normal subgroups, ordered by reverse inclusion, the sets `H¹(G ⧸ N, Aᴺ)` and the
transition maps form a diagram of types, and the inflation maps form a cocone on it with apex
`H¹(G, A)`. For `G` a compact topological group and `A` discrete this cocone is a colimit: every
class is inflated from some finite quotient `G ⧸ N`
(`TauCeti.NonabelianH1.exists_mem_range_infl`), and two finite-level classes with the same
inflation already agree at the intersection of their levels. For a profinite Galois group this is
the description of continuous nonabelian Galois cohomology as the colimit of the cohomology of the
finite Galois extensions.

## Main definitions

* `TauCeti.NonabelianH1.Cocycle.inflOfLE` and `TauCeti.NonabelianH1.inflOfLE`: the transition
  `Z¹(G ⧸ N, Aᴺ) → Z¹(G ⧸ M, Aᴹ)` and `H¹(G ⧸ N, Aᴺ) → H¹(G ⧸ M, Aᴹ)` for `M ≤ N`.
* `TauCeti.NonabelianH1.finiteQuotientDiagram G A`: the diagram `N ↦ H¹(G ⧸ N, Aᴺ)` of types
  over the open normal subgroups of `G`, ordered by reverse inclusion.
* `TauCeti.NonabelianH1.inflCocone G A`: the cocone on that diagram with apex `H¹(G, A)` whose
  legs are the inflation maps.
* `TauCeti.NonabelianH1.isColimitInflCocone`: for `G` compact and `A` discrete, the inflation
  cocone is a colimit.

## Main results

* `TauCeti.NonabelianH1.infl_inflOfLE`: inflation to `G` commutes with the transition maps.
* `TauCeti.NonabelianH1.inflOfLE_refl` and `TauCeti.NonabelianH1.inflOfLE_inflOfLE`: the identity
  and composition laws.
* `TauCeti.NonabelianH1.inflOfLE_injective`: every transition map is injective.

## References

* J.-P. Serre, *Galois Cohomology*, Springer, 1997, I.2.2 and I.5.8.
* M. Kim, *The motivic fundamental group of `P¹ ∖ {0, 1, ∞}` and the theorem of Siegel*,
  Invent. Math. 161 (2005), §1.
-/

public section

universe u v

namespace TauCeti

namespace NonabelianH1

open CategoryTheory

variable {G : Type u} {A : Type v} [Group G] [TopologicalSpace G] [Group A] [TopologicalSpace A]
  [MulDistribMulAction G A]

section Transition

variable {M N P : Subgroup G} [M.Normal] [N.Normal] [P.Normal]

namespace Cocycle

/-- The **transition** `Z¹(G ⧸ N, Aᴺ) → Z¹(G ⧸ M, Aᴹ)` for normal subgroups `M ≤ N`: the cocycle
`gM ↦ d(gN)`. It is the descent to `G ⧸ M` of the inflation of `d` to `G`, which is trivial on
`N` and hence on `M`. -/
def inflOfLE (hMN : M ≤ N) (d : Cocycle (G ⧸ N) (FixedPoints.subgroup N A)) :
    Cocycle (G ⧸ M) (FixedPoints.subgroup M A) :=
  (d.map (Subgroup.quotientMkContinuousMonoidHom N) (ContinuousMonoidHom.subgroupSubtype _)
    (subgroupSubtype_quotientMk_smul N)).descend M fun m hm ↦ by
      simp [(QuotientGroup.eq_one_iff m).mpr (hMN hm)]

/-- The value of a transitioned cocycle at the class of `g` modulo `M` is the value of the
cocycle at the class of `g` modulo `N`. -/
@[simp]
theorem coe_inflOfLE_apply (hMN : M ≤ N) (d : Cocycle (G ⧸ N) (FixedPoints.subgroup N A))
    (g : G) : (d.inflOfLE hMN (g : G ⧸ M) : A) = d (g : G ⧸ N) := by
  simp [inflOfLE]

/-- The transition of the trivial cocycle is the trivial cocycle. -/
@[simp]
theorem inflOfLE_one (hMN : M ≤ N) :
    (1 : Cocycle (G ⧸ N) (FixedPoints.subgroup N A)).inflOfLE hMN = 1 :=
  ext_quotientMk fun g ↦ by simp

/-- The transition from a normal subgroup to itself is the identity. -/
@[simp]
theorem inflOfLE_refl (d : Cocycle (G ⧸ N) (FixedPoints.subgroup N A)) :
    d.inflOfLE (le_refl N) = d :=
  ext_quotientMk fun g ↦ by simp

/-- For `P ≤ M ≤ N`, the transition from `N` to `P` is the composite of the transitions through
`M`. -/
@[simp]
theorem inflOfLE_inflOfLE (hPM : P ≤ M) (hMN : M ≤ N)
    (d : Cocycle (G ⧸ N) (FixedPoints.subgroup N A)) :
    (d.inflOfLE hMN).inflOfLE hPM = d.inflOfLE (hPM.trans hMN) :=
  ext_quotientMk fun g ↦ by simp

/-- Inflation to `G` commutes with the transitions: inflating a cocycle of `G ⧸ N` through
`G ⧸ M` is inflating it directly. -/
@[simp]
theorem map_inflOfLE (hMN : M ≤ N) (d : Cocycle (G ⧸ N) (FixedPoints.subgroup N A)) :
    (d.inflOfLE hMN).map (Subgroup.quotientMkContinuousMonoidHom M)
        (ContinuousMonoidHom.subgroupSubtype _) (subgroupSubtype_quotientMk_smul M) =
      d.map (Subgroup.quotientMkContinuousMonoidHom N) (ContinuousMonoidHom.subgroupSubtype _)
        (subgroupSubtype_quotientMk_smul N) :=
  map_descend _ _

/-- The transition of cocycles is injective. -/
theorem inflOfLE_injective (hMN : M ≤ N) :
    Function.Injective (inflOfLE (A := A) hMN) := fun d d' h ↦
  ext_quotientMk fun g ↦ by simpa using congrArg (fun e ↦ (e (g : G ⧸ M) : A)) h

end Cocycle

/-- The **transition** `H¹(G ⧸ N, Aᴺ) → H¹(G ⧸ M, Aᴹ)` for normal subgroups `M ≤ N`: the map
induced by the projection `G ⧸ M → G ⧸ N` and the inclusion `Aᴺ ↪ Aᴹ`. It is the inflation along
`G ⧸ M → G ⧸ N`. -/
def inflOfLE (hMN : M ≤ N) :
    NonabelianH1 (G ⧸ N) (FixedPoints.subgroup N A) →
      NonabelianH1 (G ⧸ M) (FixedPoints.subgroup M A) :=
  lift (fun d ↦ mk (d.inflOfLE hMN)) fun _ _ ⟨a, ha⟩ ↦ mk_eq_mk_iff.mpr
    -- The gauge witness `a ∈ Aᴺ` is also a witness in `Aᴹ`.
    ⟨⟨a, fun m ↦ a.property ⟨m, hMN m.property⟩⟩, fun q ↦ by
      induction q using QuotientGroup.induction_on with | H g =>
      exact Subtype.ext (by simp [ha])⟩

/-- The transition sends the class of a cocycle to the class of its transition. -/
theorem inflOfLE_mk (hMN : M ≤ N) (d : Cocycle (G ⧸ N) (FixedPoints.subgroup N A)) :
    inflOfLE hMN (mk d) = mk (d.inflOfLE hMN) :=
  lift_mk _ _ d

/-- The transition preserves the base point. -/
@[simp]
theorem inflOfLE_one (hMN : M ≤ N) :
    inflOfLE hMN (1 : NonabelianH1 (G ⧸ N) (FixedPoints.subgroup N A)) = 1 := by
  rw [one_def, inflOfLE_mk, Cocycle.inflOfLE_one, mk_one]

/-- **Inflation commutes with the transitions**: inflating a class of `H¹(G ⧸ N, Aᴺ)` to
`H¹(G, A)` through `H¹(G ⧸ M, Aᴹ)` is inflating it directly. -/
@[simp]
theorem infl_inflOfLE (hMN : M ≤ N) (c : NonabelianH1 (G ⧸ N) (FixedPoints.subgroup N A)) :
    infl M (inflOfLE hMN c) = infl N c := by
  induction c using induction_on with | mk d =>
  rw [inflOfLE_mk, infl_mk, infl_mk, Cocycle.map_inflOfLE]

/-- The transition from a normal subgroup to itself is the identity. -/
@[simp]
theorem inflOfLE_refl (c : NonabelianH1 (G ⧸ N) (FixedPoints.subgroup N A)) :
    inflOfLE (le_refl N) c = c := by
  induction c using induction_on with | mk d =>
  rw [inflOfLE_mk, Cocycle.inflOfLE_refl]

/-- For `P ≤ M ≤ N`, the transition from `N` to `P` is the composite of the transitions through
`M`. -/
@[simp]
theorem inflOfLE_inflOfLE (hPM : P ≤ M) (hMN : M ≤ N)
    (c : NonabelianH1 (G ⧸ N) (FixedPoints.subgroup N A)) :
    inflOfLE hPM (inflOfLE hMN c) = inflOfLE (hPM.trans hMN) c := by
  induction c using induction_on with | mk d =>
  rw [inflOfLE_mk, inflOfLE_mk, inflOfLE_mk, Cocycle.inflOfLE_inflOfLE]

/-- Every transition map is injective, because inflation to `G` is. -/
theorem inflOfLE_injective (hMN : M ≤ N) : Function.Injective (inflOfLE (A := A) hMN) :=
  fun c c' h ↦ infl_injective N (by rw [← infl_inflOfLE hMN, h, infl_inflOfLE])

/-- A class is sent to the base point by a transition map exactly when it is the base point. -/
@[simp]
theorem inflOfLE_eq_one_iff (hMN : M ≤ N)
    {c : NonabelianH1 (G ⧸ N) (FixedPoints.subgroup N A)} : inflOfLE hMN c = 1 ↔ c = 1 :=
  (inflOfLE_injective hMN).eq_iff' (inflOfLE_one hMN)

end Transition

section Colimit

variable (G A)

/-- The **finite-quotient diagram** of `H¹(G, A)`: the sets `H¹(G ⧸ N, Aᴺ)` over the open normal
subgroups `N` of `G`, ordered by reverse inclusion, with the transition maps. -/
-- The body is exposed so that the objects and maps of the diagram reduce outside this module:
-- the cocone legs and every map out of a cocone are typed by them.
@[expose] def finiteQuotientDiagram : (OpenNormalSubgroup G)ᵒᵖ ⥤ Type (max u v) where
  obj N := NonabelianH1 (G ⧸ N.unop.toSubgroup) (FixedPoints.subgroup N.unop.toSubgroup A)
  map f := ↾(inflOfLE (leOfHom f.unop))
  map_id N := by
    ext c
    exact inflOfLE_refl c
  map_comp f g := by
    ext c
    exact (inflOfLE_inflOfLE _ _ c).symm

/-- The maps of the finite-quotient diagram are the transition maps. -/
@[simp]
theorem finiteQuotientDiagram_map_apply {N M : (OpenNormalSubgroup G)ᵒᵖ} (f : N ⟶ M)
    (c : (finiteQuotientDiagram G A).obj N) :
    (finiteQuotientDiagram G A).map f c = inflOfLE (leOfHom f.unop) c :=
  (rfl)

/-- The **inflation cocone** on the finite-quotient diagram: its apex is `H¹(G, A)` and its leg
at `N` is inflation `H¹(G ⧸ N, Aᴺ) → H¹(G, A)`. -/
@[expose] def inflCocone : Limits.Cocone (finiteQuotientDiagram G A) where
  pt := NonabelianH1 G A
  ι :=
    { app N := ↾(infl N.unop.toSubgroup)
      naturality N M f := by
        ext c
        exact infl_inflOfLE (leOfHom f.unop) c }

/-- The apex of the inflation cocone is `H¹(G, A)`. -/
@[simp]
theorem inflCocone_pt : (inflCocone G A).pt = NonabelianH1 G A :=
  (rfl)

/-- The leg of the inflation cocone at `N` is inflation from `H¹(G ⧸ N, Aᴺ)`. -/
@[simp]
theorem inflCocone_ι_app (N : (OpenNormalSubgroup G)ᵒᵖ) :
    (inflCocone G A).ι.app N = ↾(infl N.unop.toSubgroup) :=
  (rfl)

/-- The legs of the inflation cocone are the inflation maps, pointwise. -/
-- Not `@[simp]`: `simp` rewrites the codomain `((Functor.const _).obj _).obj N` of the leg, which
-- occurs in the coercion of the left-hand side, to the apex, so the left-hand side is not in simp
-- normal form.
theorem inflCocone_ι_app_apply (N : (OpenNormalSubgroup G)ᵒᵖ)
    (c : (finiteQuotientDiagram G A).obj N) :
    (inflCocone G A).ι.app N c = infl N.unop.toSubgroup c :=
  (rfl)

variable {G A}

/-- **The finite-quotient colimit theorem**: for a compact topological group `G` acting on a
discrete group `A`, the continuous nonabelian cohomology `H¹(G, A)` is the colimit of the sets
`H¹(G ⧸ N, Aᴺ)` over the open normal subgroups `N`, through the inflation maps. The coefficient
group `A` need not be finite or commutative. -/
noncomputable def isColimitInflCocone [IsTopologicalGroup G] [CompactSpace G]
    [DiscreteTopology A] : Limits.IsColimit (inflCocone G A) :=
  Limits.Types.FilteredColimit.isColimitOf _ _
    (fun c ↦ by
      obtain ⟨N, d, rfl⟩ := exists_mem_range_infl c
      exact ⟨Opposite.op N, d, (inflCocone_ι_app_apply G A _ d).symm⟩)
    fun N M d e h ↦ by
      -- Two classes with the same inflation agree at the intersection of their levels, where
      -- inflation is injective.
      refine ⟨Opposite.op (N.unop ⊓ M.unop), (homOfLE inf_le_left).op, (homOfLE inf_le_right).op,
        ?_⟩
      rw [inflCocone_ι_app_apply, inflCocone_ι_app_apply] at h
      rw [finiteQuotientDiagram_map_apply, finiteQuotientDiagram_map_apply]
      exact infl_injective _ <| (infl_inflOfLE _ d).trans <| h.trans (infl_inflOfLE _ e).symm

end Colimit

end NonabelianH1

end TauCeti
