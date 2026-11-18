/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.GroupAlgGeom.AlgebraicSet
public import TauCeti.GroupTheory.GroupAlgGeom.Discrimination
import TauCeti.GroupTheory.GroupAlgGeom.Separated

/-!
# Coordinate groups under a change of the coefficient group

Let `f : G →* G'` be a homomorphism of coefficient groups and `ι : G' →* H`. A system `S ⊆ G[X]`
has the same solutions in `H` through `ι ∘ f` as its image `f(S) ⊆ G'[X]` through `ι`, so the
map `G[X] → G'[X]` induced by `f` passes to an injective homomorphism of coordinate groups
`CoordGroup.mapCoeff f ι S : G_{R(S)} → G'_{R(f(S))}`.

If `H` is separated by `G` over `G` through an injective `ι : G →* H`, the radical of a system over
`G` does not change when its solutions are taken in `H`. If `G'` is separated by `G` over `G`
through `f`, the coordinate group of `f(S)` over `G'` is separated, over the coordinate group of
`S` with solutions in `G'`, by that group: a retraction of `G'` onto `G` over `G` keeping a given
element nontrivial induces a retraction of the coordinate groups.

## Main definitions

* `TauCeti.GroupAlgGeom.CoordGroup.mapCoeff`: the homomorphism of coordinate groups induced by a
  change of the coefficient group.

## Main results

* `TauCeti.GroupAlgGeom.V_image_map`: the solutions of the image of a system under a change of
  coefficients are those of the system.
* `TauCeti.GroupAlgGeom.CoordGroup.mapCoeff_injective`: the homomorphism of coordinate groups
  induced by a change of coefficients is injective; it sends the generic point to the generic
  point (`TauCeti.GroupAlgGeom.CoordGroup.mapCoeff_comp_genericPoint`).
* `TauCeti.GroupAlgGeom.Rad_eq_of_isSeparatedBy`: over a coefficient extension `ι : G →* H` by
  which `H` is separated, the radicals of a system over `H` and over `G` agree.
* `TauCeti.GroupAlgGeom.CoordGroup.isSeparatedBy_mapCoeff`: the coordinate group over the larger
  coefficient group is separated by the one over the smaller group.

## References

* O. Kharlampovich, A. Myasnikov, *Implicit function theorem over free groups*, J. Algebra 290
  (2005), §6, Lemma 37 (homomorphisms of coordinate groups induced by homomorphisms of the
  groups, and radicals over separated groups; here the coefficient group itself changes).
-/

public section

namespace TauCeti.GroupAlgGeom

variable {G G' H X : Type*} [Group G] [Group G'] [Group H]

variable (f : G →* G') (ι : G' →* H) (S : Set (GX G X))

/-- The solutions of `S` through `ι ∘ f` are those of its image under the change of
coefficients `f`. -/
theorem V_image_map : V ι (Monoid.Coprod.map f (FreeGroup.map id) '' S) = V (ι.comp f) S := by
  ext v
  simp [eval_map]

namespace CoordGroup

/-- The homomorphism `G_{R(S)} → G'_{R(f(S))}` of coordinate groups induced by a change of
coefficients `f : G →* G'`, the solutions being taken in `H` through `ι`. -/
noncomputable def mapCoeff :
    GHom (coeff (ι.comp f) S) ((coeff ι (Monoid.Coprod.map f (FreeGroup.map id) '' S)).comp f) :=
  { toMonoidHom := QuotientGroup.map _ _ (Monoid.Coprod.map f (FreeGroup.map id)) (by
      intro w hw
      rw [Subgroup.mem_comap, mem_Rad]
      intro v hv
      rw [V_image_map] at hv
      simpa using (mem_Rad.1 hw) v hv)
    map_coeff' := fun g => by simp [coeff_apply] }

variable {f ι S}

/-- The class of a word `w` is sent to the class of its image `f(w)`. -/
@[simp]
theorem mapCoeff_mk (w : GX G X) :
    mapCoeff f ι S (w : CoordGroup (ι.comp f) S) =
      (Monoid.Coprod.map f (FreeGroup.map id) w :
        CoordGroup ι (Monoid.Coprod.map f (FreeGroup.map id) '' S)) := (rfl)

/-- The homomorphism of coordinate groups sends each coordinate of the generic point of `S` to
that of the generic point of `f(S)`. -/
@[simp]
theorem mapCoeff_genericPoint (x : X) :
    mapCoeff f ι S (genericPoint (ι.comp f) S x) =
      genericPoint ι (Monoid.Coprod.map f (FreeGroup.map id) '' S) x := by
  simp [genericPoint_apply]

/-- The homomorphism of coordinate groups sends the generic point of `S` to that of `f(S)`. -/
@[simp]
theorem mapCoeff_comp_genericPoint :
    ⇑(mapCoeff f ι S) ∘ genericPoint (ι.comp f) S =
      genericPoint ι (Monoid.Coprod.map f (FreeGroup.map id) '' S) :=
  funext mapCoeff_genericPoint

/-- The homomorphism of coordinate groups induced by a change of coefficients is injective: a
word over `G` vanishes at every solution of `f(S)` in `H` exactly when it vanishes at every
solution of `S` through `ι ∘ f`, these being the same points. -/
theorem mapCoeff_injective : Function.Injective (mapCoeff f ι S) := by
  refine (injective_iff_map_eq_one _).2 fun c hc => ?_
  induction c using QuotientGroup.induction_on with | H w => ?_
  rw [mapCoeff_mk, QuotientGroup.eq_one_iff, mem_Rad, V_image_map] at hc
  exact (QuotientGroup.eq_one_iff w).2 (mem_Rad.2 fun v hv => by simpa using hc v hv)

end CoordGroup

section Separated

/-- If `H` is separated by `G` over `G` through an injective `ι : G →* H`, the radical of a
system `S` over `G` is its radical with solutions in `H`. -/
theorem Rad_eq_of_isSeparatedBy {ι : G →* H} (hι : Function.Injective ι)
    (hH : IsSeparatedBy ι (.id G)) (S : Set (GX G X)) : Rad ι S = Rad (.id G) S := by
  refine le_antisymm (fun w hw => mem_Rad.2 fun v hv => hι ?_) (hH.Rad_le S)
  -- a solution `v` over `G` gives the solution `ι ∘ v` in `H`
  have := mem_Rad.1 hw _ ((GHom.mk ι fun _ => rfl : GHom (.id G) ι).comp_mem_V hv)
  rw [← map_eval] at this
  rwa [map_one]

namespace CoordGroup

variable {f : G →* G'} {S : Set (GX G X)}

/-- Changing the coefficients along a retraction `ψ : G' → G` of `f` over `G` maps the radical of
`f(S)` over `G'` into the radical of `S` over `G`. -/
private theorem Rad_image_map_le_comap (ψ : GHom f (.id G)) :
    Rad (.id G') (Monoid.Coprod.map f (FreeGroup.map id) '' S) ≤
      (Rad (.id G) S).comap (Monoid.Coprod.map (ψ : G' →* G) (FreeGroup.map id)) := by
  intro u hu
  rw [Subgroup.mem_comap, mem_Rad]
  intro p hp
  -- `f ∘ p` solves `f(S)` in `G'`, and `ψ ∘ f ∘ p = p`
  have hfp : f ∘ p ∈ V (.id G') (Monoid.Coprod.map f (FreeGroup.map id) '' S) := by
    rw [V_image_map]
    exact (GHom.mk f fun _ => rfl : GHom (.id G) ((MonoidHom.id G').comp f)).comp_mem_V hp
  have hψp : ψ ∘ f ∘ p = p := funext fun x => ψ.map_coeff (p x)
  simpa [hom_eval, hψp] using congrArg ψ (mem_Rad.1 hu _ hfp)

/-- If `G'` is separated by `G` over `G` through `f`, the coordinate group over `G'` of the image
`f(S)` of a system `S` over `G` is separated by the coordinate group `G[X] ⧸ Rad(S)` of `S` with
solutions in `G'`, over the latter, through the change of coefficients. When `f` is injective
(for instance when `G'` is nontrivial), the latter is the coordinate group of `S` over `G`, by
`TauCeti.GroupAlgGeom.Rad_eq_of_isSeparatedBy`. -/
theorem isSeparatedBy_mapCoeff (hf : IsSeparatedBy f (.id G)) :
    IsSeparatedBy (mapCoeff f (.id G') S : CoordGroup ((MonoidHom.id G').comp f) S →*
        CoordGroup (.id G') (Monoid.Coprod.map f (FreeGroup.map id) '' S))
      (MonoidHom.id (CoordGroup ((MonoidHom.id G').comp f) S)) := by
  refine (isSeparatedBy_def _ _).2 fun c hc => ?_
  induction c using QuotientGroup.induction_on with | H w => ?_
  -- a solution `v` of `f(S)` in `G'` at which `w` survives, and a retraction `ψ : G' → G` over
  -- `G` keeping `w(v)` nontrivial
  obtain ⟨v, hv, hwv⟩ : ∃ v ∈ V (.id G') (Monoid.Coprod.map f (FreeGroup.map id) '' S),
      eval (.id G') v w ≠ 1 := by
    simpa [QuotientGroup.eq_one_iff, mem_Rad] using hc
  obtain ⟨ψ, hψ⟩ := (isSeparatedBy_def _ _).1 hf _ hwv
  have hRad : Rad ((MonoidHom.id G').comp f) S = Rad (.id G) S :=
    Rad_eq_of_isSeparatedBy (Function.LeftInverse.injective ψ.map_coeff) (by simpa using hf) S
  -- changing the coefficients along `ψ` induces a retraction of the coordinate groups
  have hψf : (Monoid.Coprod.map (ψ : G' →* G) (FreeGroup.map id)).comp
      (Monoid.Coprod.map f (FreeGroup.map (id : X → X))) = .id _ := by
    ext <;> simp
  refine ⟨⟨QuotientGroup.map _ _ (Monoid.Coprod.map (ψ : G' →* G) (FreeGroup.map id))
    (hRad ▸ Rad_image_map_le_comap ψ), fun c => ?_⟩, ?_⟩
  · induction c using QuotientGroup.induction_on with | H w₀ => ?_
    simp only [OneHom.toFun_eq_coe, MonoidHom.toOneHom_coe, MonoidHom.coe_ofClass, mapCoeff_mk,
      QuotientGroup.map_mk, MonoidHom.id_apply]
    rw [← MonoidHom.comp_apply, hψf, MonoidHom.id_apply]
  · -- `w` survives at the solution `ψ ∘ v` of `S` over `G`
    rw [V_image_map, MonoidHom.id_comp] at hv
    rw [GHom.coe_mk, Ne, QuotientGroup.map_mk, QuotientGroup.eq_one_iff, hRad, mem_Rad]
    push Not
    exact ⟨ψ ∘ v, ψ.comp_mem_V hv, by simpa [hom_eval] using hψ⟩

end CoordGroup

end Separated

end TauCeti.GroupAlgGeom
