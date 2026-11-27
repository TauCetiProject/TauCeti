/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Quasicategory.Limit
public import TauCeti.AlgebraicTopology.SimplicialSet.ULift

/-!
# Small limits and colimits in quasicategories

A quasicategory `C` *has limits of size `w`* (`SSet.HasLimitsOfSize.{w} C`) if every diagram in
`C` indexed by a simplicial set of the universe `w` has a limit cone (`SSet.slice.IsLimit`), a
terminal vertex of the slice `C_{/p}`; dually it *has colimits of size `w`*
(`SSet.HasColimitsOfSize.{w} C`) if every such diagram has a colimit cocone
(`SSet.coslice.IsColimit`). A map `F : C ⟶ D` *preserves limits of size `w`*
(`SSet.PreservesLimitsOfSize.{w} F`) if pushing cones forward along `F` (`SSet.slice.map`) sends
the limit cones over such diagrams to limit cones, and dually *preserves colimits of size `w`*
(`SSet.PreservesColimitsOfSize.{w} F`) through `SSet.coslice.map`. These are the small limits
and colimits of a quasicategory, through which complete, cocomplete and presentable
quasicategories and continuous and cocontinuous functors are defined.

Slices and coslices are only formed for a diagram and a simplicial set in one universe. A diagram
indexed by a simplicial set `K` of the universe `w` is therefore a map from the universe lift
`SSet.uliftFunctor.obj K` to `C`, and `C` lives in the universe `max w u`. For `C : SSet.{u}`,
`C.HasLimitsOfSize.{u}` asks for limits of all diagrams indexed by simplicial sets of the universe
of `C`, and `C.HasLimitsOfSize.{0}` for limits of diagrams indexed by simplicial sets of the
lowest universe. When the indexing universe is the universe of `C`, the universe lift is
isomorphic to the identity (`SSet.uliftFunctorTrivial`), so the four properties can be stated and
used on ordinary diagrams `p : K ⟶ C` (`SSet.hasLimitsOfSize_iff_forall_exists_isLimit` and its
analogues). Each property passes to smaller indexing universes (`SSet.hasLimitsOfSize_shrink` and
its analogues), since iterated universe lifts collapse to a single lift
(`SSet.uliftFunctorCompIso`). For the same reason the auxiliary universe can be normalized: the
sizes `.{w, u}` and `.{w, max w u}` give the same properties (`SSet.hasLimitsOfSize_max_iff` and
its analogues).

Having limits or colimits of size `w` is invariant under isomorphism, and isomorphisms, in
particular identities, as well as composites of maps preserving limits or colimits of size `w`
preserve them. Colimits in `C` are limits in the opposite simplicial set `Cᵒᵖ`
(`SSet.coslice.isColimit_iff_isLimit_op`), so `Cᵒᵖ` has limits of size `w` exactly when `C` has
colimits of size `w` (`SSet.hasLimitsOfSize_op_iff`), and the opposite of a map preserves limits
of size `w` exactly when the map preserves colimits of size `w`
(`SSet.preservesLimitsOfSize_op_iff`). These duality statements are simp lemmas removing an
opposite. The limit of the empty diagram is a terminal vertex, so a quasicategory with limits of
size `w` has a terminal vertex (`SSet.HasLimitsOfSize.exists_isTerminalVertex`), and a map
preserving limits of size `w` sends terminal vertices to terminal vertices
(`SSet.PreservesLimitsOfSize.isTerminalVertex_map`); dually for colimits and initial vertices. In
particular an empty simplicial set has neither limits nor colimits. In a terminal simplicial set,
such as `Δ[0]`, every cone is a limit cone and every cocone a colimit cocone, so `Δ[0]` has limits
and colimits of every size, and every map to `Δ[0]` preserves them.

## Main definitions

* `SSet.HasLimitsOfSize.{w} C`, `SSet.HasColimitsOfSize.{w} C`: the simplicial set `C` has limits,
  respectively colimits, indexed by simplicial sets of the universe `w`.
* `SSet.PreservesLimitsOfSize.{w} F`, `SSet.PreservesColimitsOfSize.{w} F`: the map `F` preserves
  these limits, respectively colimits.

## Main results

* `SSet.HasLimitsOfSize.of_iso`, `SSet.HasColimitsOfSize.of_iso`: invariance under isomorphism.
* `SSet.hasLimitsOfSize_op_iff`, `SSet.hasColimitsOfSize_op_iff`: the duality between limits and
  colimits.
* `SSet.PreservesLimitsOfSize.of_isIso`, `SSet.PreservesLimitsOfSize.id`,
  `SSet.PreservesLimitsOfSize.comp`, and the same for colimits: isomorphisms, identities and
  composites.
* `SSet.preservesLimitsOfSize_op_iff`, `SSet.preservesColimitsOfSize_op_iff`: the duality for
  preservation.
* `SSet.hasLimitsOfSize_iff_forall_exists_isLimit`,
  `SSet.preservesLimitsOfSize_iff_forall_isLimit_map`, and their duals: the properties for diagrams
  indexed by simplicial sets of the universe of `C`.
* `SSet.hasLimitsOfSize_shrink`, `SSet.preservesLimitsOfSize_shrink`, and their duals: passing to
  smaller indexing universes.
* `SSet.hasLimitsOfSize_max_iff`, `SSet.preservesLimitsOfSize_max_iff`, and their duals: the sizes
  `.{w, u}` and `.{w, max w u}` agree.
* `SSet.hasLimitsOfSize_stdSimplex_zero`, `SSet.hasColimitsOfSize_stdSimplex_zero`: `Δ[0]` has
  limits and colimits of every size.
* `SSet.HasLimitsOfSize.exists_isTerminalVertex`, `SSet.PreservesLimitsOfSize.isTerminalVertex_map`,
  and their duals for initial vertices.
* `SSet.not_hasLimitsOfSize_of_not_nonempty`, `SSet.not_hasColimitsOfSize_of_not_nonempty`: an
  empty simplicial set has neither limits nor colimits.

## References

* J. Lurie, *Higher Topos Theory*, §1.2.13.
-/

public section

universe w w' u

open CategoryTheory Limits Simplicial

namespace SSet

/-- A simplicial set `C`, typically a quasicategory, *has limits of size `w`* if every diagram
`p : K ⟶ C` indexed by the universe lift `SSet.uliftFunctor.obj K` of a simplicial set `K` in the
universe `w` has a limit cone. -/
class HasLimitsOfSize (C : SSet.{max w u}) : Prop where
  exists_isLimit ⦃K : SSet.{w}⦄ (p : uliftFunctor.{u}.obj K ⟶ C) : ∃ c, slice.IsLimit p c

/-- A simplicial set `C`, typically a quasicategory, *has colimits of size `w`* if every diagram
`p : K ⟶ C` indexed by the universe lift `SSet.uliftFunctor.obj K` of a simplicial set `K` in the
universe `w` has a colimit cocone. -/
class HasColimitsOfSize (C : SSet.{max w u}) : Prop where
  exists_isColimit ⦃K : SSet.{w}⦄ (p : uliftFunctor.{u}.obj K ⟶ C) : ∃ c, coslice.IsColimit p c

/-- A map `F : C ⟶ D` *preserves limits of size `w`* if, for every diagram `p` in `C` indexed by
the universe lift of a simplicial set in the universe `w`, pushing cones forward along `F`
(`SSet.slice.map`) sends limit cones over `p` to limit cones over `p ≫ F`. The diagram
`q = p ≫ F` is allowed up to equality. -/
class PreservesLimitsOfSize {C D : SSet.{max w u}} (F : C ⟶ D) : Prop where
  isLimit_map ⦃K : SSet.{w}⦄ ⦃p : uliftFunctor.{u}.obj K ⟶ C⦄ ⦃q : uliftFunctor.{u}.obj K ⟶ D⦄
    (h : 𝟙 _ ≫ p ≫ F = q) ⦃c : (slice p) _⦋0⦌⦄ (hc : slice.IsLimit p c) :
    slice.IsLimit q ((slice.map (𝟙 _) F h).app _ c)

/-- A map `F : C ⟶ D` *preserves colimits of size `w`* if, for every diagram `p` in `C` indexed by
the universe lift of a simplicial set in the universe `w`, pushing cocones forward along `F`
(`SSet.coslice.map`) sends colimit cocones under `p` to colimit cocones under `p ≫ F`. The
diagram `q = p ≫ F` is allowed up to equality. -/
class PreservesColimitsOfSize {C D : SSet.{max w u}} (F : C ⟶ D) : Prop where
  isColimit_map ⦃K : SSet.{w}⦄ ⦃p : uliftFunctor.{u}.obj K ⟶ C⦄ ⦃q : uliftFunctor.{u}.obj K ⟶ D⦄
    (h : 𝟙 _ ≫ p ≫ F = q) ⦃c : (coslice p) _⦋0⦌⦄ (hc : coslice.IsColimit p c) :
    coslice.IsColimit q ((coslice.map (𝟙 _) F h).app _ c)

variable {C D E : SSet.{max w u}}

namespace HasLimitsOfSize

/-- Having limits of size `w` is invariant under isomorphism. -/
lemma of_iso [C.HasLimitsOfSize.{w}] (e : C ≅ D) : D.HasLimitsOfSize.{w} where
  exists_isLimit _ p := (slice.exists_isLimit_iff_of_isIso (𝟙 _) e.hom (by simp)).2
    (exists_isLimit (p ≫ e.inv))

/-- A simplicial set with limits of size `w` has a terminal vertex, the limit of the empty
diagram. -/
lemma exists_isTerminalVertex [C.HasLimitsOfSize.{w}] :
    ∃ x, C.IsTerminalVertex x := by
  -- The empty diagram is indexed by the universe lift of the empty subcomplex of `Δ[0]`.
  have hK : ¬ (uliftFunctor.{u}.obj ((⊥ : (Δ[0] : SSet.{w}).Subcomplex) : SSet.{w})).Nonempty := by
    simp
  have ⟨c, hc⟩ := exists_isLimit ((isInitialOfNotNonempty hK).to C)
  exact ⟨_, (slice.isLimit_iff_isTerminalVertex_π _ hK c).1 hc⟩

end HasLimitsOfSize

/-- An empty simplicial set has no limits of any size: it has no terminal vertex. -/
lemma not_hasLimitsOfSize_of_not_nonempty (hC : ¬ C.Nonempty) : ¬ C.HasLimitsOfSize.{w} :=
  fun _ ↦ (HasLimitsOfSize.exists_isTerminalVertex.{w, u} (C := C)).elim fun x _ ↦ hC ⟨x⟩

namespace HasColimitsOfSize

/-- Having colimits of size `w` is invariant under isomorphism. -/
lemma of_iso [C.HasColimitsOfSize.{w}] (e : C ≅ D) : D.HasColimitsOfSize.{w} where
  exists_isColimit _ p := (coslice.exists_isColimit_iff_of_isIso (𝟙 _) e.hom (by simp)).2
    (exists_isColimit (p ≫ e.inv))

/-- A simplicial set with colimits of size `w` has an initial vertex, the colimit of the empty
diagram. -/
lemma exists_isInitialVertex [C.HasColimitsOfSize.{w}] :
    ∃ x, C.IsInitialVertex x := by
  -- The empty diagram is indexed by the universe lift of the empty subcomplex of `Δ[0]`.
  have hK : ¬ (uliftFunctor.{u}.obj ((⊥ : (Δ[0] : SSet.{w}).Subcomplex) : SSet.{w})).Nonempty := by
    simp
  have ⟨c, hc⟩ := exists_isColimit ((isInitialOfNotNonempty hK).to C)
  exact ⟨_, (coslice.isColimit_iff_isInitialVertex_π _ hK c).1 hc⟩

end HasColimitsOfSize

/-- An empty simplicial set has no colimits of any size: it has no initial vertex. -/
lemma not_hasColimitsOfSize_of_not_nonempty (hC : ¬ C.Nonempty) : ¬ C.HasColimitsOfSize.{w} :=
  fun _ ↦ (HasColimitsOfSize.exists_isInitialVertex.{w, u} (C := C)).elim fun x _ ↦ hC ⟨x⟩

/-- The opposite of a simplicial set has limits of size `w` exactly when the simplicial set has
colimits of size `w`. -/
@[simp]
theorem hasLimitsOfSize_op_iff : C.op.HasLimitsOfSize.{w} ↔ C.HasColimitsOfSize.{w} := by
  rw [Iff.comm]
  refine ⟨fun _ ↦ ⟨fun K p ↦ ?_⟩, fun _ ↦ ⟨fun K p ↦ ?_⟩⟩
  · -- The diagram `p` in `Cᵒᵖ` is, up to the isomorphism `f`, the opposite of a diagram in `C`
    -- indexed by the universe lift of `Kᵒᵖ`, whose colimit cocone gives a limit cone over `p`.
    let f : (uliftFunctor.{u}.obj K.op).op ≅ uliftFunctor.{u}.obj K :=
      (opFunctorCompUliftFunctorIso.app K.op).symm ≪≫
        uliftFunctor.mapIso (opFunctorCompOpFunctorIso.app K)
    have := (coslice.exists_isColimit_iff_exists_isLimit_op _).1
      (HasColimitsOfSize.exists_isColimit (opFunctor.preimage (f.hom ≫ p)))
    rw [Functor.map_preimage] at this
    exact (slice.exists_isLimit_iff_of_isIso f.hom (𝟙 _) (by simp)).1 this
  · -- The opposite of `p` is, up to isomorphism, indexed by the universe lift of `Kᵒᵖ`.
    have := HasLimitsOfSize.exists_isLimit
      ((opFunctorCompUliftFunctorIso.app K).hom ≫ opFunctor.map p)
    exact (coslice.exists_isColimit_iff_exists_isLimit_op p).2
      ((slice.exists_isLimit_iff_of_isIso (opFunctorCompUliftFunctorIso.app K).hom (𝟙 _)
        (by simp)).1 this)

/-- The opposite of a simplicial set has colimits of size `w` exactly when the simplicial set has
limits of size `w`. -/
@[simp]
theorem hasColimitsOfSize_op_iff : C.op.HasColimitsOfSize.{w} ↔ C.HasLimitsOfSize.{w} := by
  rw [← hasLimitsOfSize_op_iff, Iff.comm]
  -- The double opposite `Cᵒᵖᵒᵖ` is isomorphic to `C`.
  exact ⟨fun _ ↦ .of_iso (C := C) (D := C.op.op) (opFunctorCompOpFunctorIso.app C).symm,
    fun _ ↦ .of_iso (C := C.op.op) (D := C) (opFunctorCompOpFunctorIso.app C)⟩

/-- The opposite of a simplicial set with colimits of size `w` has limits of size `w`. -/
instance hasLimitsOfSize_op [C.HasColimitsOfSize.{w}] : C.op.HasLimitsOfSize.{w} :=
  hasLimitsOfSize_op_iff.2 ‹_›

/-- The opposite of a simplicial set with limits of size `w` has colimits of size `w`. -/
instance hasColimitsOfSize_op [C.HasLimitsOfSize.{w}] : C.op.HasColimitsOfSize.{w} :=
  hasColimitsOfSize_op_iff.2 ‹_›

/-- A terminal simplicial set, such as `Δ[0]`, has limits of every size: every cone in it is a
limit cone. -/
lemma hasLimitsOfSize_of_isTerminal (hC : IsTerminal C) : C.HasLimitsOfSize.{w} where
  exists_isLimit _ p :=
    ⟨yonedaEquiv ((slice.isTerminal p hC).from Δ[0]), slice.isLimit_of_isTerminal p hC _⟩

/-- A terminal simplicial set, such as `Δ[0]`, has colimits of every size: every cocone in it is a
colimit cocone. -/
lemma hasColimitsOfSize_of_isTerminal (hC : IsTerminal C) : C.HasColimitsOfSize.{w} where
  exists_isColimit _ p :=
    ⟨yonedaEquiv ((coslice.isTerminal p hC).from Δ[0]), coslice.isColimit_of_isTerminal p hC _⟩

/-- The standard `0`-simplex has limits of every size. -/
instance hasLimitsOfSize_stdSimplex_zero : (Δ[0] : SSet.{max w u}).HasLimitsOfSize.{w} :=
  hasLimitsOfSize_of_isTerminal stdSimplex.isTerminalObj₀

/-- The standard `0`-simplex has colimits of every size. -/
instance hasColimitsOfSize_stdSimplex_zero : (Δ[0] : SSet.{max w u}).HasColimitsOfSize.{w} :=
  hasColimitsOfSize_of_isTerminal stdSimplex.isTerminalObj₀

namespace PreservesLimitsOfSize

/-- Isomorphisms preserve limits of every size. -/
instance of_isIso (F : C ⟶ D) [IsIso F] : PreservesLimitsOfSize.{w} F where
  isLimit_map _ _ _ h _ hc := (slice.isLimit_iff _).2
    ((isTerminalVertex_iff_of_iso (asIso (slice.map (𝟙 _) F h)) _).2 ((slice.isLimit_iff _).1 hc))

/-- The identity preserves limits of every size. -/
instance id : PreservesLimitsOfSize.{w} (𝟙 C) :=
  of_isIso _

/-- A composite of maps preserving limits of size `w` preserves limits of size `w`. -/
instance comp (F : C ⟶ D) (G : D ⟶ E) [PreservesLimitsOfSize.{w} F]
    [PreservesLimitsOfSize.{w} G] : PreservesLimitsOfSize.{w} (F ≫ G) where
  isLimit_map _ p q h c hc := by
    have h' : 𝟙 _ ≫ (p ≫ F) ≫ G = q := by simpa using h
    -- Pushing cones forward along `F ≫ G` is pushing them forward along `F`, then along `G`.
    have e : slice.map (𝟙 _) (F ≫ G) h =
        slice.map (𝟙 _) F (Category.id_comp _) ≫ slice.map (𝟙 _) G h' := by
      simp
    rw [e, comp_app, ConcreteCategory.comp_apply]
    exact isLimit_map h' (isLimit_map (Category.id_comp _) hc)

/-- Every map to a terminal simplicial set, such as `Δ[0]`, preserves limits of every size. -/
lemma of_isTerminal (F : C ⟶ D) (hD : IsTerminal D) : PreservesLimitsOfSize.{w} F where
  isLimit_map _ _ q _ _ _ := slice.isLimit_of_isTerminal q hD _

/-- A map preserving limits of size `w` sends terminal vertices to terminal vertices: they are the
cone points of the limit cones over the empty diagram. -/
lemma isTerminalVertex_map (F : C ⟶ D) [PreservesLimitsOfSize.{w} F] {x : C _⦋0⦌}
    (hx : C.IsTerminalVertex x) : D.IsTerminalVertex (F.app _ x) := by
  -- The empty diagram `p` is indexed by the universe lift of the empty subcomplex of `Δ[0]`.
  have hK : ¬ (uliftFunctor.{u}.obj ((⊥ : (Δ[0] : SSet.{w}).Subcomplex) : SSet.{w})).Nonempty := by
    simp
  let p := (isInitialOfNotNonempty hK).to C
  -- Over the empty diagram `p`, cones are their cone points, and limit cones are the cones whose
  -- cone point is terminal.
  have := slice.isIso_π p hK
  obtain ⟨c, rfl⟩ : ∃ c, (slice.π p).app _ c = x := ⟨(inv (slice.π p)).app _ x, by simp⟩
  have hc := isLimit_map (F := F) rfl ((slice.isLimit_iff_isTerminalVertex_π p hK c).2 hx)
  rw [slice.isLimit_iff_isTerminalVertex_π _ hK] at hc
  have hπ := congr_arg (fun f ↦ f.app _ c) (slice.map_π (𝟙 _) F (q := 𝟙 _ ≫ p ≫ F) rfl)
  simp only [NatTrans.comp_app, ConcreteCategory.comp_apply] at hπ
  rwa [← hπ]

end PreservesLimitsOfSize

namespace PreservesColimitsOfSize

/-- Isomorphisms preserve colimits of every size. -/
instance of_isIso (F : C ⟶ D) [IsIso F] : PreservesColimitsOfSize.{w} F where
  isColimit_map _ _ _ h _ hc := (coslice.isColimit_iff _).2
    ((isInitialVertex_iff_of_iso (asIso (coslice.map (𝟙 _) F h)) _).2
      ((coslice.isColimit_iff _).1 hc))

/-- The identity preserves colimits of every size. -/
instance id : PreservesColimitsOfSize.{w} (𝟙 C) :=
  of_isIso _

/-- A composite of maps preserving colimits of size `w` preserves colimits of size `w`. -/
instance comp (F : C ⟶ D) (G : D ⟶ E) [PreservesColimitsOfSize.{w} F]
    [PreservesColimitsOfSize.{w} G] : PreservesColimitsOfSize.{w} (F ≫ G) where
  isColimit_map _ p q h c hc := by
    have h' : 𝟙 _ ≫ (p ≫ F) ≫ G = q := by simpa using h
    -- Pushing cocones forward along `F ≫ G` is pushing them forward along `F`, then along `G`.
    have e : coslice.map (𝟙 _) (F ≫ G) h =
        coslice.map (𝟙 _) F (Category.id_comp _) ≫ coslice.map (𝟙 _) G h' := by
      rw [coslice.map_comp]
      simp only [Category.comp_id]
    rw [e, comp_app, ConcreteCategory.comp_apply]
    exact isColimit_map h' (isColimit_map (Category.id_comp _) hc)

/-- Every map to a terminal simplicial set, such as `Δ[0]`, preserves colimits of every size. -/
lemma of_isTerminal (F : C ⟶ D) (hD : IsTerminal D) : PreservesColimitsOfSize.{w} F where
  isColimit_map _ _ q _ _ _ := coslice.isColimit_of_isTerminal q hD _

/-- A map preserving colimits of size `w` sends initial vertices to initial vertices: they are the
cone points of the colimit cocones under the empty diagram. -/
lemma isInitialVertex_map (F : C ⟶ D) [PreservesColimitsOfSize.{w} F] {x : C _⦋0⦌}
    (hx : C.IsInitialVertex x) : D.IsInitialVertex (F.app _ x) := by
  -- The empty diagram `p` is indexed by the universe lift of the empty subcomplex of `Δ[0]`.
  have hK : ¬ (uliftFunctor.{u}.obj ((⊥ : (Δ[0] : SSet.{w}).Subcomplex) : SSet.{w})).Nonempty := by
    simp
  let p := (isInitialOfNotNonempty hK).to C
  -- Under the empty diagram `p`, cocones are their cone points, and colimit cocones are the
  -- cocones whose cone point is initial.
  have := coslice.isIso_π p hK
  obtain ⟨c, rfl⟩ : ∃ c, (coslice.π p).app _ c = x := ⟨(inv (coslice.π p)).app _ x, by simp⟩
  have hc := isColimit_map (F := F) rfl ((coslice.isColimit_iff_isInitialVertex_π p hK c).2 hx)
  rw [coslice.isColimit_iff_isInitialVertex_π _ hK] at hc
  have hπ := congr_arg (fun f ↦ f.app _ c) (coslice.map_π (𝟙 _) F (q := 𝟙 _ ≫ p ≫ F) rfl)
  simp only [NatTrans.comp_app, ConcreteCategory.comp_apply] at hπ
  rwa [← hπ]

end PreservesColimitsOfSize

/-- The opposite of a map preserves limits of size `w` exactly when the map preserves colimits of
size `w`. -/
@[simp]
theorem preservesLimitsOfSize_op_iff (F : C ⟶ D) :
    PreservesLimitsOfSize.{w} (opFunctor.map F) ↔ PreservesColimitsOfSize.{w} F := by
  rw [Iff.comm]
  refine ⟨fun _ ↦ ⟨fun K p q h c hc ↦ ?_⟩, fun _ ↦ ⟨fun K p q h c hc ↦ ?_⟩⟩
  · -- Up to the isomorphism `f`, the diagram `p` in `Cᵒᵖ` is the opposite of a diagram `p₀` in
    -- `C`. Restricting `c` along `f` gives a limit cone over `p₀ᵒᵖ`, that is a colimit cocone
    -- `c₀` under `p₀`, which `F` preserves.
    let f : (uliftFunctor.{u}.obj K.op).op ≅ uliftFunctor.{u}.obj K :=
      (opFunctorCompUliftFunctorIso.app K.op).symm ≪≫
        uliftFunctor.mapIso (opFunctorCompOpFunctorIso.app K)
    let p₀ : uliftFunctor.{u}.obj K.op ⟶ C := opFunctor.preimage (f.hom ≫ p)
    have hp₀ : f.hom ≫ p ≫ 𝟙 _ = opFunctor.map p₀ := by simp [p₀]
    let v := (slice.map f.hom (𝟙 _) hp₀).app _ c
    have hv : slice.IsLimit (opFunctor.map p₀) v := (slice.isLimit_iff _).2
      ((isTerminalVertex_iff_of_iso (asIso (slice.map f.hom (𝟙 _) hp₀)) c).2
        ((slice.isLimit_iff _).1 hc))
    let c₀ : (coslice p₀) _⦋0⦌ :=
      (coslice.opSliceIso p₀).inv.app _ ((slice (opFunctor.map p₀)).opObjEquiv.symm v)
    have hc₀ : coslice.IsColimit p₀ c₀ :=
      (coslice.isColimit_iff_isLimit_op c₀).2 (by simpa [c₀] using hv)
    have hF := (coslice.isColimit_map_iff_isLimit_op (𝟙 _) F rfl
      (CategoryTheory.Functor.map_id _ _) rfl c₀).1 (PreservesColimitsOfSize.isColimit_map rfl hc₀)
    simp only [c₀, Iso.inv_hom_id_app_apply, Equiv.apply_symm_apply] at hF
    exact (slice.isLimit_map_map_iff f.hom (opFunctor.map F) hp₀ h (by simp) c).1 hF
  · -- The colimit cocone `c` is a limit cone over `pᵒᵖ`, which after restriction along the
    -- isomorphism `e` is indexed by the universe lift of `Kᵒᵖ`, so that `Fᵒᵖ` preserves it.
    let e : uliftFunctor.{u}.obj K.op ⟶ (uliftFunctor.{u}.obj K).op :=
      (opFunctorCompUliftFunctorIso.app K).hom
    have hv := (coslice.isColimit_iff_isLimit_op c).1 hc
    have hv' := (slice.isLimit_iff _).2 ((isTerminalVertex_iff_of_iso
      (asIso (slice.map e (𝟙 _) (q := e ≫ opFunctor.map p) (by simp))) _).2
        ((slice.isLimit_iff _).1 hv))
    rw [coslice.isColimit_map_iff_isLimit_op (𝟙 _) F h (CategoryTheory.Functor.map_id _ _) rfl,
      ← slice.isLimit_map_map_iff e (opFunctor.map F) (p' := e ≫ opFunctor.map p) (by simp) _
        (q' := e ≫ opFunctor.map q) (by simp [← h])]
    exact PreservesLimitsOfSize.isLimit_map _ hv'

/-- The opposite of a map preserves colimits of size `w` exactly when the map preserves limits of
size `w`. -/
@[simp]
theorem preservesColimitsOfSize_op_iff (F : C ⟶ D) :
    PreservesColimitsOfSize.{w} (opFunctor.map F) ↔ PreservesLimitsOfSize.{w} F := by
  rw [← preservesLimitsOfSize_op_iff, Iff.comm]
  -- The double opposite of `F` is `F`, up to the isomorphisms `Cᵒᵖᵒᵖ ≅ C` and `Dᵒᵖᵒᵖ ≅ D`.
  let eC : C.op.op ≅ C := opFunctorCompOpFunctorIso.app C
  let eD : D.op.op ≅ D := opFunctorCompOpFunctorIso.app D
  have hF : opFunctor.map (opFunctor.map F) = eC.hom ≫ F ≫ eD.inv := by
    rw [← Category.assoc, Iso.eq_comp_inv]
    -- This is the naturality of `opFunctorCompOpFunctorIso`, whose source functor
    -- `opFunctor ⋙ opFunctor` sends `F` to `opFunctor.map (opFunctor.map F)` by definition.
    exact opFunctorCompOpFunctorIso.hom.naturality F
  refine ⟨fun _ ↦ ?_, fun _ ↦ ?_⟩
  · rw [hF]
    exact PreservesLimitsOfSize.comp _ _
  · have hF' : F = eC.inv ≫ opFunctor.map (opFunctor.map F) ≫ eD.hom := by simp [hF]
    rw [hF']
    exact PreservesLimitsOfSize.comp _ _

/-! ### Diagrams in the universe of `C` and smaller indexing universes -/

/-- For a simplicial set `C` in the universe `max w u`, having limits indexed by simplicial sets of
this universe means that every diagram `p : K ⟶ C` indexed by a simplicial set `K` of the universe
of `C` has a limit cone: the universe lift of such a `K` is isomorphic to `K`
(`SSet.uliftFunctorTrivial`). -/
theorem hasLimitsOfSize_iff_forall_exists_isLimit :
    C.HasLimitsOfSize.{max w u, u} ↔
      ∀ ⦃K : SSet.{max w u}⦄ (p : K ⟶ C), ∃ c, slice.IsLimit p c :=
  ⟨fun _ _ _ ↦ (slice.exists_isLimit_iff_of_isIso (uliftFunctorTrivial.{w, u}.hom.app _) (𝟙 C)
    rfl).1 (HasLimitsOfSize.exists_isLimit _), fun h ↦ ⟨fun _ p ↦ h p⟩⟩

/-- For a simplicial set `C` in the universe `max w u`, having colimits indexed by simplicial sets
of this universe means that every diagram `p : K ⟶ C` indexed by a simplicial set `K` of the
universe of `C` has a colimit cocone. -/
theorem hasColimitsOfSize_iff_forall_exists_isColimit :
    C.HasColimitsOfSize.{max w u, u} ↔
      ∀ ⦃K : SSet.{max w u}⦄ (p : K ⟶ C), ∃ c, coslice.IsColimit p c :=
  ⟨fun _ _ _ ↦ (coslice.exists_isColimit_iff_of_isIso (uliftFunctorTrivial.{w, u}.hom.app _)
    (𝟙 C) rfl).1 (HasColimitsOfSize.exists_isColimit _), fun h ↦ ⟨fun _ p ↦ h p⟩⟩

/-- For a map `F : C ⟶ D` in the universe `max w u`, preserving limits indexed by simplicial sets
of this universe means that `F` sends limit cones over every diagram `p : K ⟶ C`, indexed by a
simplicial set `K` of this universe, to limit cones over `p ≫ F`. -/
theorem preservesLimitsOfSize_iff_forall_isLimit_map (F : C ⟶ D) :
    PreservesLimitsOfSize.{max w u, u} F ↔
      ∀ ⦃K : SSet.{max w u}⦄ ⦃p : K ⟶ C⦄ ⦃q : K ⟶ D⦄ (h : 𝟙 _ ≫ p ≫ F = q)
        ⦃c : (slice p) _⦋0⦌⦄, slice.IsLimit p c →
          slice.IsLimit q ((slice.map (𝟙 _) F h).app _ c) := by
  refine ⟨fun _ K p q h c hc ↦ ?_, fun H ↦ ⟨fun _ _ _ h _ hc ↦ H h hc⟩⟩
  -- Restrict `c` along the isomorphism `i` from the universe lift of `K` to `K`.
  let i : uliftFunctor.{u}.obj K ⟶ K := uliftFunctorTrivial.{w, u}.hom.app K
  have hp : i ≫ p ≫ 𝟙 C = i ≫ p := by simp
  rw [← slice.isLimit_map_map_iff i F hp h (q' := i ≫ q) (by simp [← h])]
  exact PreservesLimitsOfSize.isLimit_map _ ((slice.isLimit_iff _).2
    ((isTerminalVertex_iff_of_iso (asIso (slice.map i (𝟙 C) hp)) c).2 ((slice.isLimit_iff _).1 hc)))

/-- For a map `F : C ⟶ D` in the universe `max w u`, preserving colimits indexed by simplicial
sets of this universe means that `F` sends colimit cocones under every diagram `p : K ⟶ C`,
indexed by a simplicial set `K` of this universe, to colimit cocones under `p ≫ F`. -/
theorem preservesColimitsOfSize_iff_forall_isColimit_map (F : C ⟶ D) :
    PreservesColimitsOfSize.{max w u, u} F ↔
      ∀ ⦃K : SSet.{max w u}⦄ ⦃p : K ⟶ C⦄ ⦃q : K ⟶ D⦄ (h : 𝟙 _ ≫ p ≫ F = q)
        ⦃c : (coslice p) _⦋0⦌⦄, coslice.IsColimit p c →
          coslice.IsColimit q ((coslice.map (𝟙 _) F h).app _ c) := by
  refine ⟨fun hF K p q h c hc ↦ ?_, fun H ↦ ⟨fun _ _ _ h _ hc ↦ H h hc⟩⟩
  -- Pass to the opposite: `Fᵒᵖ` preserves the limit cone over `pᵒᵖ` corresponding to `c`.
  rw [← preservesLimitsOfSize_op_iff, preservesLimitsOfSize_iff_forall_isLimit_map] at hF
  rw [coslice.isColimit_map_iff_isLimit_op (𝟙 _) F h (CategoryTheory.Functor.map_id _ _) rfl]
  exact hF _ ((coslice.isColimit_iff_isLimit_op c).1 hc)

section shrink

variable {C D : SSet.{max w w' u}}

/-- Having limits of size `max w w'` implies having limits of the smaller size `w`: the universe
lift of a simplicial set of the universe `w` is, up to isomorphism, the universe lift of a
simplicial set of the universe `max w w'` (`SSet.uliftFunctorCompIso`). -/
theorem hasLimitsOfSize_shrink [C.HasLimitsOfSize.{max w w', u}] :
    C.HasLimitsOfSize.{w, max w' u} where
  exists_isLimit K _ := (slice.exists_isLimit_iff_of_isIso
    (uliftFunctorCompIso.{w, w', u}.hom.app K) (𝟙 C) rfl).1 (HasLimitsOfSize.exists_isLimit _)

/-- Having colimits of size `max w w'` implies having colimits of the smaller size `w`. -/
theorem hasColimitsOfSize_shrink [C.HasColimitsOfSize.{max w w', u}] :
    C.HasColimitsOfSize.{w, max w' u} where
  exists_isColimit K _ := (coslice.exists_isColimit_iff_of_isIso
    (uliftFunctorCompIso.{w, w', u}.hom.app K) (𝟙 C) rfl).1 (HasColimitsOfSize.exists_isColimit _)

/-- A map preserving limits of size `max w w'` preserves limits of the smaller size `w`. -/
theorem preservesLimitsOfSize_shrink (F : C ⟶ D) [PreservesLimitsOfSize.{max w w', u} F] :
    PreservesLimitsOfSize.{w, max w' u} F where
  isLimit_map K p q h c hc := by
    -- Restrict `c` along the isomorphism `i` from the iterated universe lift of `K` to its single
    -- universe lift.
    let i := uliftFunctorCompIso.{w, w', u}.hom.app K
    have hp : i ≫ p ≫ 𝟙 C = i ≫ p := by simp
    rw [← slice.isLimit_map_map_iff i F hp h (q' := i ≫ q) (by simp [← h])]
    exact PreservesLimitsOfSize.isLimit_map _ ((slice.isLimit_iff _).2
      ((isTerminalVertex_iff_of_iso (asIso (slice.map i (𝟙 C) hp)) c).2
        ((slice.isLimit_iff _).1 hc)))

/-- A map preserving colimits of size `max w w'` preserves colimits of the smaller size `w`. -/
theorem preservesColimitsOfSize_shrink (F : C ⟶ D) [PreservesColimitsOfSize.{max w w', u} F] :
    PreservesColimitsOfSize.{w, max w' u} F := by
  have := (preservesLimitsOfSize_op_iff.{max w w', u} F).2 ‹_›
  exact (preservesLimitsOfSize_op_iff.{w, max w' u} F).1 (preservesLimitsOfSize_shrink.{w, w', u} _)

end shrink

/-! ### Normalizing the auxiliary universe

For `C : SSet.{max w u}`, the sizes `.{w, u}` and `.{w, max w u}` describe diagrams indexed by
simplicial sets of the same universe `w` in the same ambient universe. The two universe lifts of
such a simplicial set are isomorphic (through `SSet.uliftFunctorCompIso` and
`SSet.uliftFunctorTrivial`), so the two spellings of each property agree. -/

/-- Having limits of size `.{w, max w u}` is having limits of size `.{w, u}`. -/
theorem hasLimitsOfSize_max_iff :
    C.HasLimitsOfSize.{w, max w u} ↔ C.HasLimitsOfSize.{w, u} := by
  refine ⟨fun _ ↦ ⟨fun K _ ↦ ?_⟩, fun _ ↦ hasLimitsOfSize_shrink.{w, w, u}⟩
  -- Transport along the isomorphism between the two universe lifts of `K`.
  exact (slice.exists_isLimit_iff_of_isIso ((uliftFunctorCompIso.{w, u, w}.app K).symm ≪≫
    uliftFunctorTrivial.{u, w}.app _).hom (𝟙 C) rfl).1 (HasLimitsOfSize.exists_isLimit _)

/-- Having colimits of size `.{w, max w u}` is having colimits of size `.{w, u}`. -/
theorem hasColimitsOfSize_max_iff :
    C.HasColimitsOfSize.{w, max w u} ↔ C.HasColimitsOfSize.{w, u} := by
  rw [← hasLimitsOfSize_op_iff.{w, max w u}, ← hasLimitsOfSize_op_iff.{w, u},
    hasLimitsOfSize_max_iff.{w, u}]

/-- Preserving limits of size `.{w, max w u}` is preserving limits of size `.{w, u}`. -/
theorem preservesLimitsOfSize_max_iff (F : C ⟶ D) :
    PreservesLimitsOfSize.{w, max w u} F ↔ PreservesLimitsOfSize.{w, u} F := by
  refine ⟨fun _ ↦ ⟨fun K p q h c hc ↦ ?_⟩, fun _ ↦ preservesLimitsOfSize_shrink.{w, w, u} F⟩
  -- Restrict `c` along the isomorphism `i` between the two universe lifts of `K`.
  let i : uliftFunctor.{max w u}.obj K ⟶ uliftFunctor.{u}.obj K :=
    ((uliftFunctorCompIso.{w, u, w}.app K).symm ≪≫ uliftFunctorTrivial.{u, w}.app _).hom
  have hp : i ≫ p ≫ 𝟙 C = i ≫ p := by simp
  rw [← slice.isLimit_map_map_iff i F hp h (q' := i ≫ q) (by simp [← h])]
  exact PreservesLimitsOfSize.isLimit_map _ ((slice.isLimit_iff _).2
    ((isTerminalVertex_iff_of_iso (asIso (slice.map i (𝟙 C) hp)) c).2 ((slice.isLimit_iff _).1 hc)))

/-- Preserving colimits of size `.{w, max w u}` is preserving colimits of size `.{w, u}`. -/
theorem preservesColimitsOfSize_max_iff (F : C ⟶ D) :
    PreservesColimitsOfSize.{w, max w u} F ↔ PreservesColimitsOfSize.{w, u} F := by
  rw [← preservesLimitsOfSize_op_iff.{w, max w u}, ← preservesLimitsOfSize_op_iff.{w, u},
    preservesLimitsOfSize_max_iff.{w, u}]

end SSet
