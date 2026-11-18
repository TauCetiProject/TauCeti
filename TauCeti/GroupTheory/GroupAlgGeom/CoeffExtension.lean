/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.GroupAlgGeom.AlgebraicSet
import Mathlib.Data.Finset.Union

/-!
# Coordinate groups under a change of the coefficient group

Let `f : G →* G'` be a homomorphism of coefficient groups and `ι : G' →* H`. A system `S ⊆ G[X]`
has the same solutions in `H` through `ι ∘ f` as its image `f(S) ⊆ G'[X]` through `ι`, so the
map `G[X] → G'[X]` induced by `f` passes to an injective homomorphism of coordinate groups
`CoordGroup.mapCoeff f ι S : G_{R(S)} → G'_{R(f(S))}`.

Finitely many words over a free group `F(A)` involve only finitely many letters of `A`, and
finitely many words in `G[X ⊔ Y]` involve only finitely many of the further variables `Y`. These
finiteness facts, and the change of coefficients along the inclusion of a free factor, are the
first steps in reducing statements about systems over a free group of arbitrary rank, in
arbitrarily many further variables, to a free factor of finite rank and finitely many further
variables.

## Main definitions

* `TauCeti.GroupAlgGeom.CoordGroup.mapCoeff`: the homomorphism of coordinate groups induced by a
  change of the coefficient group.

## Main results

* `TauCeti.GroupAlgGeom.V_image_map`: the solutions of the image of a system under a change of
  coefficients are those of the system.
* `TauCeti.GroupAlgGeom.CoordGroup.mapCoeff_injective`: the homomorphism of coordinate groups
  induced by a change of coefficients is injective; it sends the generic point to the generic
  point (`TauCeti.GroupAlgGeom.CoordGroup.mapCoeff_comp_genericPoint`).
* `TauCeti.GroupAlgGeom.GX.exists_finset_forall_mem_range_map_sumMap`,
  `TauCeti.GroupAlgGeom.GX.exists_finset_forall_mem_range_map_freeGroupMap`: finitely many words
  involve finitely many further variables and finitely many letters of a free coefficient group.

## References

* O. Kharlampovich, A. Myasnikov, *Implicit function theorem over free groups*, J. Algebra 290
  (2005), §6, Lemma 37 (homomorphisms of coordinate groups induced by homomorphisms of the
  groups; here the coefficient group itself changes).
-/

public section

namespace TauCeti.GroupAlgGeom

open Monoid.Coprod

variable {G G' H X Y : Type*} [Group G] [Group G'] [Group H]

section MapCoeff

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

end MapCoeff

namespace GX

/-- Finitely many words in `G[X ⊕ Y]` involve only finitely many of the variables `Y`. -/
theorem exists_finset_forall_mem_range_map_sumMap (s : Finset (GX G (X ⊕ Y))) :
    ∃ Z : Finset Y, ∀ w ∈ s,
      w ∈ (Monoid.Coprod.map (.id G) (FreeGroup.map (Sum.map id ((↑) : Z → Y)))).range := by
  classical
  -- the subgroups generated by the coefficients, the variables `X` and finitely many variables
  -- `Z ⊆ Y`; they form a directed family generating `G[X ⊔ Y]`
  let K (Z : Finset Y) : Subgroup (GX G (X ⊕ Y)) := Subgroup.closure (Set.range inl ∪
    (Set.range fun x => inr (FreeGroup.of (Sum.inl x))) ∪
      (fun y => inr (FreeGroup.of (Sum.inr y))) '' (Z : Set Y))
  have hK : Monotone K := fun _ _ h =>
    Subgroup.closure_mono (Set.union_subset_union_right _ (Set.image_mono (by exact_mod_cast h)))
  have htop : ⨆ Z, K Z = ⊤ := by
    rw [eq_top_iff, ← closure_image_inl_union_range_inr_of Subgroup.closure_univ,
      Subgroup.closure_le]
    rintro _ (⟨g, -, rfl⟩ | ⟨x | y, rfl⟩)
    · exact Subgroup.mem_iSup_of_mem ∅ (Subgroup.subset_closure (.inl (.inl ⟨g, rfl⟩)))
    · exact Subgroup.mem_iSup_of_mem ∅ (Subgroup.subset_closure (.inl (.inr ⟨x, rfl⟩)))
    · exact Subgroup.mem_iSup_of_mem {y} (Subgroup.subset_closure (.inr ⟨y, by simp, rfl⟩))
  choose Z hZ using fun w => (Subgroup.mem_iSup_of_directed hK.directed_le).1
    (htop ▸ Subgroup.mem_top w)
  refine ⟨s.biUnion Z, fun w hw => ?_⟩
  refine (Subgroup.closure_le _).2 ?_ (hK (Finset.subset_biUnion_of_mem Z hw) (hZ w))
  rintro _ ((⟨g, rfl⟩ | ⟨x, rfl⟩) | ⟨y, hy, rfl⟩)
  exacts [⟨inl g, rfl⟩, ⟨inr (FreeGroup.of (Sum.inl x)), rfl⟩,
    ⟨inr (FreeGroup.of (Sum.inr ⟨y, hy⟩)), rfl⟩]

/-- Finitely many words over a free group `F(A)` involve only finitely many letters of `A`. -/
theorem exists_finset_forall_mem_range_map_freeGroupMap {A : Type*}
    (s : Finset (GX (FreeGroup A) X)) :
    ∃ A₀ : Finset A, ∀ w ∈ s,
      w ∈ (Monoid.Coprod.map (FreeGroup.map ((↑) : A₀ → A)) (FreeGroup.map id)).range := by
  classical
  -- the subgroups generated by finitely many letters `A₀ ⊆ A` and the variables; they form a
  -- directed family generating `F(A)[X]`
  let K (A₀ : Finset A) : Subgroup (GX (FreeGroup A) X) := Subgroup.closure
    ((fun a => inl (FreeGroup.of a)) '' (A₀ : Set A) ∪ Set.range fun x => inr (FreeGroup.of x))
  have hK : Monotone K := fun _ _ h =>
    Subgroup.closure_mono (Set.union_subset_union_left _ (Set.image_mono (by exact_mod_cast h)))
  have htop : ⨆ A₀, K A₀ = ⊤ := by
    rw [eq_top_iff, ← closure_image_inl_union_range_inr_of (FreeGroup.closure_range_of A),
      Subgroup.closure_le]
    rintro _ (⟨_, ⟨a, rfl⟩, rfl⟩ | ⟨x, rfl⟩)
    · exact Subgroup.mem_iSup_of_mem {a} (Subgroup.subset_closure (.inl ⟨a, by simp, rfl⟩))
    · exact Subgroup.mem_iSup_of_mem ∅ (Subgroup.subset_closure (.inr ⟨x, rfl⟩))
  choose A₀ hA₀ using fun w => (Subgroup.mem_iSup_of_directed hK.directed_le).1
    (htop ▸ Subgroup.mem_top w)
  refine ⟨s.biUnion A₀, fun w hw => ?_⟩
  refine (Subgroup.closure_le _).2 ?_ (hK (Finset.subset_biUnion_of_mem A₀ hw) (hA₀ w))
  rintro _ (⟨a, ha, rfl⟩ | ⟨x, rfl⟩)
  exacts [⟨inl (FreeGroup.of ⟨a, ha⟩), rfl⟩, ⟨inr (FreeGroup.of x), rfl⟩]

end GX

end TauCeti.GroupAlgGeom
