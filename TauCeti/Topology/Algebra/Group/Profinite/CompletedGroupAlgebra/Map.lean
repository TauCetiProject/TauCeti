/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Compactness.Compact
public import TauCeti.Algebra.MonoidAlgebra.MapDomain
public import TauCeti.Topology.Algebra.Group.OpenNormalSubgroup
public import TauCeti.Topology.Algebra.Group.Profinite.CompletedGroupAlgebra.Basic

/-!
# Functoriality of the completed group algebra

A continuous group homomorphism `f : Γ →* Δ` induces an `R`-algebra homomorphism
`completedGroupAlgebra.map R f hf : R[[Γ]] →ₐ[R] R[[Δ]]` between the completed group algebras.
At the level `V` of `R[[Δ]]` it is the map `R[Γ ⧸ f⁻¹(V)] → R[Δ ⧸ V]` induced by `f` on the
quotients, applied to the level `f⁻¹(V)` of `R[[Γ]]` (`proj_map`); the same description holds
at every level `U ≤ f⁻¹(V)` of `R[[Γ]]` (`proj_map_of_le`), which is how the levels of a
composite are compared. The map sends group elements to group elements (`map_of`) and satisfies
the two functor laws `map_id` and `map_comp`. A topological isomorphism `e : Γ ≃ₜ* Δ` therefore
induces an isomorphism of `R`-algebras `completedGroupAlgebra.domCongr R e : R[[Γ]] ≃ₐ[R] R[[Δ]]`.

When the open normal quotients of `Γ` are finite, `map` is continuous for the inverse-limit
topologies (`continuous_map`). When moreover the coefficient ring is compact Hausdorff and `f`
is surjective, `map` is surjective (`map_surjective`); the compactness is what lets the levelwise
preimages be assembled into one element. For `R = ℤ_[p]` and profinite `Γ`, `Δ` these hypotheses
are all instances, so a continuous surjection of profinite groups induces a surjection of Iwasawa
algebras.

## Main definitions

* `TauCeti.completedGroupAlgebra.map R f hf`: the `R`-algebra homomorphism `R[[Γ]] →ₐ[R] R[[Δ]]`
  induced by a continuous homomorphism `f : Γ →* Δ`.
* `TauCeti.completedGroupAlgebra.domCongr R e`: the `R`-algebra isomorphism `R[[Γ]] ≃ₐ[R] R[[Δ]]`
  induced by a topological isomorphism `e : Γ ≃ₜ* Δ`.

## Main results

* `TauCeti.completedGroupAlgebra.proj_map`, `TauCeti.completedGroupAlgebra.proj_map_of_le`: the
  levelwise description of `map`; `TauCeti.completedGroupAlgebra.mapDomain_map_proj_of_le` is the
  compatibility between the levels of `R[[Γ]]` behind it.
* `TauCeti.completedGroupAlgebra.map_of`: `map` sends the group element `γ` to the group element
  `f γ`.
* `TauCeti.completedGroupAlgebra.map_id`, `TauCeti.completedGroupAlgebra.map_comp`: the functor
  laws.
* `TauCeti.completedGroupAlgebra.continuous_map`: `map` is continuous when the open normal
  quotients of `Γ` are finite.
* `TauCeti.completedGroupAlgebra.map_surjective`: `map` is surjective when `f` is, for a compact
  Hausdorff coefficient ring.

## References

* L. Ribes and P. Zalesskii, *Profinite Groups*, Section 5.3.
* J. P. Labute, *Classification of Demushkin groups*, Canad. J. Math. 19 (1967), Section 1.5.
-/

public section

namespace TauCeti

universe u v w

variable (R : Type u) [CommRing R] {Γ : Type v} [Group Γ] [TopologicalSpace Γ]
  {Δ : Type w} [Group Δ] [TopologicalSpace Δ]

namespace completedGroupAlgebra

variable (f : Γ →* Δ) (hf : Continuous f)

omit [TopologicalSpace Δ] in
/-- The image of the projection of `x` at the level `U'` of `R[[Γ]]` under the map
`R[Γ ⧸ U'] → R[Δ ⧸ V]` induced by `f` can be read from any level `U ≤ U'`: it is the image of the
projection of `x` at `U` under the map `R[Γ ⧸ U] → R[Δ ⧸ V]` induced by `f`. This is the
compatibility between the levels of `R[[Γ]]` that the levelwise description of `map` rests on. -/
theorem mapDomain_map_proj_of_le {U U' : OpenNormalSubgroup Γ} (hUU' : U ≤ U') (V : Subgroup Δ)
    [V.Normal] (h : U'.toSubgroup ≤ V.comap f) (x : completedGroupAlgebra R Γ) :
    MonoidAlgebra.mapDomain (QuotientGroup.map U'.toSubgroup V f h) (proj R Γ U' x) =
      MonoidAlgebra.mapDomain (QuotientGroup.map U.toSubgroup V f fun _ hg ↦ h (hUU' hg))
        (proj R Γ U x) := by
  rw [← mapDomain_mapOfLE_proj hUU', MonoidAlgebra.mapDomain_mapDomain, ← MonoidHom.coe_comp,
    QuotientGroup.map_comp_mapOfLE]

/-- The `R`-algebra homomorphism `R[[Γ]] →ₐ[R] R[[Δ]]` induced by a continuous group
homomorphism `f : Γ →* Δ`: at the level `V` of `R[[Δ]]` it applies the map
`R[Γ ⧸ f⁻¹(V)] → R[Δ ⧸ V]` induced by `f` to the level `f⁻¹(V)` of `R[[Γ]]` (`proj_map`). It sends
group elements to group elements (`map_of`) and satisfies the functor laws `map_id` and
`map_comp`. -/
noncomputable def map : completedGroupAlgebra R Γ →ₐ[R] completedGroupAlgebra R Δ :=
  lift R Δ
    (fun V ↦ (MonoidAlgebra.mapDomainAlgHom R R (QuotientGroup.map (V.comap f hf).toSubgroup
      V.toSubgroup f (V.toSubgroup_comap f hf).le)).comp (proj R Γ (V.comap f hf)))
    fun V W hVW x ↦ by
      have h : V.comap f hf ≤ W.comap f hf := fun _ hg ↦
        OpenNormalSubgroup.mem_comap.mpr (hVW (OpenNormalSubgroup.mem_comap.mp hg))
      simp only [AlgHom.comp_apply, MonoidAlgebra.mapDomainAlgHom_apply]
      rw [MonoidAlgebra.mapDomain_mapDomain, ← MonoidHom.coe_comp, QuotientGroup.mapOfLE_comp_map,
        mapDomain_map_proj_of_le R f h]

/-- The projection of `map R f hf x` at the level `V` of `R[[Δ]]` is the image of the projection
of `x` at the level `f⁻¹(V)` of `R[[Γ]]` under the map induced by `f` on the quotients. -/
@[simp]
theorem proj_map (V : OpenNormalSubgroup Δ) (x : completedGroupAlgebra R Γ) :
    proj R Δ V (map R f hf x) =
      MonoidAlgebra.mapDomain (QuotientGroup.map (V.comap f hf).toSubgroup V.toSubgroup f
        (V.toSubgroup_comap f hf).le) (proj R Γ (V.comap f hf) x) := by
  rw [map, proj_lift, AlgHom.comp_apply, MonoidAlgebra.mapDomainAlgHom_apply]

/-- The composite of `map R f hf` with the projection at the level `V` of `R[[Δ]]` is the
projection at the level `f⁻¹(V)` of `R[[Γ]]` followed by the map induced by `f` on the
quotients. -/
@[simp]
theorem proj_comp_map (V : OpenNormalSubgroup Δ) :
    (proj R Δ V).comp (map R f hf) =
      (MonoidAlgebra.mapDomainAlgHom R R (QuotientGroup.map (V.comap f hf).toSubgroup V.toSubgroup
        f (V.toSubgroup_comap f hf).le)).comp (proj R Γ (V.comap f hf)) := by
  rw [map, proj_comp_lift]

/-- The projection of `map R f hf x` at the level `V` of `R[[Δ]]` can be read from any level
`U` of `R[[Γ]]` that `f` maps into `V`: it is the image of the projection of `x` at `U` under
the map `R[Γ ⧸ U] → R[Δ ⧸ V]` induced by `f`. -/
theorem proj_map_of_le (U : OpenNormalSubgroup Γ) (V : OpenNormalSubgroup Δ)
    (h : U.toSubgroup ≤ V.toSubgroup.comap f) (x : completedGroupAlgebra R Γ) :
    proj R Δ V (map R f hf x) =
      MonoidAlgebra.mapDomain (QuotientGroup.map U.toSubgroup V.toSubgroup f h) (proj R Γ U x) := by
  have hU : U ≤ V.comap f hf := fun _ hg ↦ OpenNormalSubgroup.mem_comap.mpr (h hg)
  rw [proj_map, mapDomain_map_proj_of_le R f hU]

/-- The induced map sends the group element `γ` to the group element `f γ`. -/
@[simp]
theorem map_of (γ : Γ) : map R f hf (of R Γ γ) = of R Δ (f γ) :=
  ext fun V ↦ by
    rw [proj_map, proj_of, proj_of, MonoidAlgebra.mapDomain_single, QuotientGroup.map_mk]

/-- The map induced by the identity is the identity. -/
@[simp]
theorem map_id : map R (MonoidHom.id Γ) continuous_id = AlgHom.id R (completedGroupAlgebra R Γ) :=
  algHom_ext fun U ↦ AlgHom.ext fun x ↦ by
    rw [AlgHom.comp_apply, AlgHom.comp_apply, AlgHom.id_apply,
      proj_map_of_le R _ _ U U (Subgroup.comap_id U.toSubgroup).ge]
    simp

/-- The map induced by a composite is the composite of the induced maps. -/
@[simp]
theorem map_comp {E : Type*} [Group E] [TopologicalSpace E] (g : Δ →* E) (hg : Continuous g) :
    map R (g.comp f) (hg.comp hf) = (map R g hg).comp (map R f hf) :=
  algHom_ext fun W ↦ AlgHom.ext fun x ↦ by
    have h : ((W.comap g hg).comap f hf).toSubgroup ≤ W.toSubgroup.comap (g.comp f) := by
      rw [OpenNormalSubgroup.toSubgroup_comap, OpenNormalSubgroup.toSubgroup_comap,
        Subgroup.comap_comap]
    rw [AlgHom.comp_apply, AlgHom.comp_apply, AlgHom.comp_apply, proj_map_of_le R _ _ _ W h,
      proj_map, proj_map, MonoidAlgebra.mapDomain_mapDomain, ← MonoidHom.coe_comp]
    congr 2
    exact (QuotientGroup.map_comp_map _ _ _ f g _ _ h).symm

/-- The `R`-algebra isomorphism `R[[Γ]] ≃ₐ[R] R[[Δ]]` induced by a topological isomorphism
`e : Γ ≃ₜ* Δ`; its underlying map is `map R e (map_continuous e)`, and its inverse is
induced by `e.symm`. -/
noncomputable def domCongr (e : Γ ≃ₜ* Δ) :
    completedGroupAlgebra R Γ ≃ₐ[R] completedGroupAlgebra R Δ :=
  AlgEquiv.ofAlgHom (map R (e : Γ →* Δ) (map_continuous e))
    (map R (e.symm : Δ →* Γ) (map_continuous e.symm))
    ((map_comp R (e.symm : Δ →* Γ) (map_continuous e.symm) (e : Γ →* Δ)
      (map_continuous e)).symm.trans <| by
      convert map_id R using 2
      exact MonoidHom.ext fun x ↦ by simp)
    ((map_comp R (e : Γ →* Δ) (map_continuous e) (e.symm : Δ →* Γ)
      (map_continuous e.symm)).symm.trans <| by
      convert map_id R using 2
      exact MonoidHom.ext fun x ↦ by simp)

@[simp]
theorem coe_domCongr (e : Γ ≃ₜ* Δ) :
    ⇑(domCongr R e) = map R (e : Γ →* Δ) (map_continuous e) :=
  (rfl)

@[simp]
theorem domCongr_symm (e : Γ ≃ₜ* Δ) : (domCongr R e).symm = domCongr R e.symm :=
  (rfl)

/-- The isomorphism induced by `e` sends the group element `γ` to the group element `e γ`. -/
@[simp]
theorem domCongr_of (e : Γ ≃ₜ* Δ) (γ : Γ) : domCongr R e (of R Γ γ) = of R Δ (e γ) :=
  map_of R (e : Γ →* Δ) (map_continuous e) γ

section TopologicalSpace

variable [TopologicalSpace R] [ContinuousAdd R]
  [∀ U : OpenNormalSubgroup Γ, Finite (Γ ⧸ U.toSubgroup)]

/-- When the open normal quotients of `Γ` are finite, the induced map between the completed
group algebras is continuous for the inverse-limit topologies. -/
theorem continuous_map : Continuous (map R f hf) := by
  classical
  refine continuous_iff.mpr fun V g ↦ ?_
  let _ := Fintype.ofFinite (Γ ⧸ (V.comap f hf).toSubgroup)
  simp only [proj_map, MonoidAlgebra.coeff_mapDomain, Finsupp.mapDomain_fintype,
    Finsupp.finsetSum_apply, Finsupp.single_apply]
  exact continuous_finsetSum _ fun h _ ↦ by
    split_ifs
    · exact continuous_coeff_proj R Γ _ h
    · exact continuous_const

/-- When the open normal quotients of `Γ` are finite and the coefficient ring is compact
Hausdorff, the map induced by a continuous surjection `f : Γ →* Δ` between the completed group
algebras is surjective. For `R = ℤ_[p]` and profinite `Γ` all the hypotheses on `R` and `Γ` are
instances. -/
theorem map_surjective [T2Space R] [CompactSpace R] (hs : Function.Surjective f) :
    Function.Surjective (map R f hf) := fun y ↦ by
  have : Nonempty (OpenNormalSubgroup Δ) := ⟨openNormalSubgroupTop Δ⟩
  -- `C V` is the set of elements whose image agrees with `y` at the level `V`. These sets are
  -- closed, nonempty (the level `V` is reached from the level `f⁻¹(V)`) and decrease along the
  -- levels, so compactness of `R[[Γ]]` gives an element in all of them, which maps to `y`.
  let C : OpenNormalSubgroup Δ → Set (completedGroupAlgebra R Γ) :=
    fun V ↦ {x | proj R Δ V (map R f hf x) = proj R Δ V y}
  have hclosed : ∀ V, IsClosed (C V) := fun V ↦ by
    have : C V = ⋂ g, {x | (proj R Δ V (map R f hf x)).coeff g = (proj R Δ V y).coeff g} := by
      ext x
      simp only [C, Set.mem_iInter, Set.mem_ofPred_eq, ← MonoidAlgebra.coeff_inj, Finsupp.ext_iff]
    rw [this]
    exact isClosed_iInter fun g ↦
      isClosed_eq ((continuous_coeff_proj R Δ V g).comp (continuous_map R f hf)) continuous_const
  have hne : ∀ V, (C V).Nonempty := fun V ↦ by
    obtain ⟨z, hz⟩ := MonoidAlgebra.mapDomain_surjective
      (QuotientGroup.map_surjective_of_surjective (V.comap f hf).toSubgroup V.toSubgroup f
        (QuotientGroup.mk_surjective.comp hs) (V.toSubgroup_comap f hf).le) (proj R Δ V y)
    obtain ⟨x, rfl⟩ := proj_surjective R Γ (V.comap f hf) z
    exact ⟨x, by rw [Set.mem_ofPred_eq, proj_map, hz]⟩
  have hmono : ∀ ⦃V W : OpenNormalSubgroup Δ⦄, V ≤ W → C V ⊆ C W := fun V W hVW x hx ↦ by
    rw [Set.mem_ofPred_eq] at hx ⊢
    rw [← mapDomain_mapOfLE_proj hVW, hx, mapDomain_mapOfLE_proj]
  obtain ⟨x, hx⟩ := IsCompact.nonempty_iInter_of_directed_nonempty_isCompact_isClosed C
    (directed_of_isDirected_ge fun _ _ hVW ↦ hmono hVW) hne (fun V ↦ (hclosed V).isCompact) hclosed
  exact ⟨x, ext fun V ↦ Set.mem_iInter.mp hx V⟩

end TopologicalSpace

end completedGroupAlgebra

end TauCeti
