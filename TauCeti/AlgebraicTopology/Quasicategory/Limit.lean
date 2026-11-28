/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Quasicategory.Core
public import TauCeti.AlgebraicTopology.Quasicategory.InitialVertex
public import TauCeti.AlgebraicTopology.SimplicialSet.Nerve.Coslice

/-!
# Limits and colimits in simplicial sets

Let `p : K ⟶ C` be a diagram in a simplicial set `C`, typically a quasicategory. The cones over
`p` are the vertices of the slice `C_{/p}` (`SSet.slice`), that is, the maps `Δ[0] ⋆ K ⟶ C`
extending `p`, and the edges of `C_{/p}` are the morphisms of cones. Following Joyal and Lurie, a
cone is a *limit cone* (`SSet.slice.IsLimit`) if it is a terminal vertex of `C_{/p}`. Dually, the
cocones under `p` are the vertices of the coslice `C_{p/}` (`SSet.coslice`), the maps
`K ⋆ Δ[0] ⟶ C` extending `p`, and a cocone is a *colimit cocone* (`SSet.coslice.IsColimit`) if
it is an initial vertex of `C_{p/}`.

Limit cones are unique up to equivalence: every cone has a morphism to a limit cone
(`SSet.slice.IsLimit.nonempty_edge`), and every morphism between limit cones is an equivalence of
`C_{/p}` (`SSet.slice.IsLimit.isEquivalence`), and dually for colimit cocones. Colimits in `C` are
limits in the opposite simplicial set `Cᵒᵖ` (`SSet.coslice.isColimit_iff_isLimit_op`), since the
coslice `C_{p/}` is the opposite of the slice `Cᵒᵖ_{/pᵒᵖ}`; hence a diagram has a colimit cocone
exactly when its opposite has a limit cone (`SSet.coslice.exists_isColimit_iff_exists_isLimit_op`),
and a cocone pushed forward along a map is a colimit cocone exactly when the opposite cone pushed
forward along the opposite map is a limit cone (`SSet.coslice.isColimit_map_iff_isLimit_op`).
Having a limit cone or a colimit cocone is invariant under isomorphisms of diagrams
(`SSet.slice.exists_isLimit_iff_of_isIso`, `SSet.coslice.exists_isColimit_iff_of_isIso`), and
pushing cones forward commutes with restricting them along an isomorphism of indexing simplicial
sets (`SSet.slice.isLimit_map_map_iff`). For the empty diagram, the slice and
the coslice are `C` itself, so that its limits are the terminal vertices of `C`
(`SSet.slice.isLimit_iff_isTerminalVertex_π`) and its colimits the initial vertices
(`SSet.coslice.isColimit_iff_isInitialVertex_π`). In the nerve of a category these are the
terminal and the initial objects (`SSet.slice.isLimit_iff_nonempty_isTerminal`,
`SSet.coslice.isColimit_iff_nonempty_isInitial`). In the nerve of a preorder, a cocone under any
diagram is a colimit cocone exactly when its cone point is a least upper bound of the vertices of
the diagram (`SSet.coslice.isColimit_iff_isLUB`), through the identification of the coslice with
the nerve of the upper bounds (`CategoryTheory.nerve.upperBoundsCosliceIso`). Limit cones and
colimit cocones are invariant under isomorphisms of diagrams
(`SSet.slice.isLimit_map_iff_of_isIso`, `SSet.coslice.isColimit_map_iff_of_isIso`). In a
terminal simplicial set, such as `Δ[0]`, every cone is a limit cone and every cocone a colimit
cocone (`SSet.slice.isLimit_of_isTerminal`, `SSet.coslice.isColimit_of_isTerminal`).

## References

* A. Joyal, *Quasi-categories and Kan complexes*, J. Pure Appl. Algebra 175 (2002), §4.
* J. Lurie, *Higher Topos Theory*, Definition 1.2.13.4.
-/

public section

universe v u u'

open CategoryTheory Limits Opposite Simplicial

namespace SSet

variable {K C : SSet.{u}} (p : K ⟶ C)

namespace slice

/-- A cone `c` over a diagram `p : K ⟶ C`, that is a vertex of the slice `C_{/p}`, is a *limit
cone* if it is a terminal vertex of `C_{/p}`. -/
def IsLimit (c : (slice p) _⦋0⦌) : Prop :=
  (slice p).IsTerminalVertex c

variable {p}

lemma isLimit_iff (c : (slice p) _⦋0⦌) : IsLimit p c ↔ (slice p).IsTerminalVertex c :=
  Iff.rfl

namespace IsLimit

variable {c c' : (slice p) _⦋0⦌}

/-- Every cone has a morphism to a limit cone. -/
lemma nonempty_edge (hc : IsLimit p c) (d : (slice p) _⦋0⦌) : Nonempty ((slice p).Edge d c) :=
  IsTerminalVertex.nonempty_edge hc d

/-- Every morphism between limit cones is an equivalence. Thus limit cones are unique up to
equivalence. -/
lemma isEquivalence (hc : IsLimit p c) (hc' : IsLimit p c') (e : (slice p).Edge c c') :
    e.IsEquivalence :=
  let ⟨I⟩ := IsTerminalVertex.nonempty_invStruct hc hc' e
  I.isEquivalence

end IsLimit

variable (p) in
/-- The limit cones of the empty diagram are the terminal vertices: when `K` is empty, a cone over
`p` is a limit cone exactly when its cone point is a terminal vertex of `C`. -/
lemma isLimit_iff_isTerminalVertex_π (hK : ¬ K.Nonempty) (c : (slice p) _⦋0⦌) :
    IsLimit p c ↔ C.IsTerminalVertex ((π p).app _ c) :=
  have := isIso_π p hK
  (isTerminalVertex_iff_of_iso (asIso (π p)) c).symm

/-- In the nerve of a category `D`, the limit cones of the empty diagram are the cones whose cone
point is a terminal object of `D`. -/
lemma isLimit_iff_nonempty_isTerminal {D : Type u'} [Category.{v} D] {L : SSet.{max u' v}}
    (q : L ⟶ nerve D) (hL : ¬ L.Nonempty) (c : (slice q) _⦋0⦌) :
    IsLimit q c ↔ Nonempty (IsTerminal (nerveEquiv ((π q).app _ c))) := by
  rw [isLimit_iff_isTerminalVertex_π q hL]
  generalize (π q).app _ c = v
  obtain ⟨x, rfl⟩ := nerveEquiv.symm.surjective v
  rw [nerve.isTerminalVertex_iff, Equiv.apply_symm_apply]

/-- Limit cones are invariant under isomorphisms of diagrams: pushing cones forward along
isomorphisms `i` and `g` preserves and reflects limit cones. -/
lemma isLimit_map_iff_of_isIso {L D : SSet.{u}} {q : L ⟶ D} (i : L ⟶ K) [IsIso i] (g : C ⟶ D)
    [IsIso g] (h : i ≫ p ≫ g = q) (c : (slice p) _⦋0⦌) :
    IsLimit q ((map i g h).app _ c) ↔ IsLimit p c :=
  isTerminalVertex_iff_of_iso (asIso (map i g h)) c

variable (p) in
/-- In a terminal simplicial set, such as `Δ[0]`, every cone is a limit cone. -/
lemma isLimit_of_isTerminal (hC : IsTerminal C) (c : (slice p) _⦋0⦌) : IsLimit p c :=
  isTerminalVertex_of_isTerminal (isTerminal p hC) c

/-- Having a limit cone is invariant under isomorphisms of diagrams: if `q` is obtained from `p` by
precomposing and postcomposing with isomorphisms `i` and `g`, then `q` has a limit cone exactly
when `p` has one. -/
lemma exists_isLimit_iff_of_isIso {L D : SSet.{u}} {q : L ⟶ D} (i : L ⟶ K) [IsIso i] (g : C ⟶ D)
    [IsIso g] (h : i ≫ p ≫ g = q) : (∃ c, IsLimit q c) ↔ ∃ c, IsLimit p c :=
  ⟨fun ⟨c, hc⟩ ↦ ⟨(asIso (map i g h)).inv.app _ c,
      (isTerminalVertex_iff_of_iso (asIso (map i g h)).symm c).2 hc⟩,
    fun ⟨c, hc⟩ ↦ ⟨(map i g h).app _ c, (isTerminalVertex_iff_of_iso (asIso (map i g h)) c).2 hc⟩⟩

/-- Pushing cones forward along `g` commutes with restricting them along an isomorphism `i` of
indexing simplicial sets. Hence a cone pushed forward along `g` is a limit cone exactly when its
restriction along `i` is. -/
lemma isLimit_map_map_iff {L D : SSet.{u}} {q : K ⟶ D} {p' : L ⟶ C} {q' : L ⟶ D} (i : L ⟶ K)
    [IsIso i] (g : C ⟶ D) (hp : i ≫ p ≫ 𝟙 C = p') (h : 𝟙 K ≫ p ≫ g = q)
    (h' : 𝟙 L ≫ p' ≫ g = q') (c : (slice p) _⦋0⦌) :
    IsLimit q' ((map (𝟙 L) g h').app _ ((map i (𝟙 C) hp).app _ c)) ↔
      IsLimit q ((map (𝟙 K) g h).app _ c) := by
  have hq : i ≫ q ≫ 𝟙 D = q' := by simp [← h, ← h', ← hp]
  have e : map i (𝟙 C) hp ≫ map (𝟙 L) g h' = map (𝟙 K) g h ≫ map i (𝟙 D) hq := by simp
  rw [← ConcreteCategory.comp_apply, ← NatTrans.comp_app, e, NatTrans.comp_app,
    ConcreteCategory.comp_apply]
  exact isTerminalVertex_iff_of_iso (asIso (map i (𝟙 D) hq)) _

end slice

namespace coslice

/-- A cocone `c` under a diagram `p : K ⟶ C`, that is a vertex of the coslice `C_{p/}`, is a
*colimit cocone* if it is an initial vertex of `C_{p/}`. -/
def IsColimit (c : (coslice p) _⦋0⦌) : Prop :=
  (coslice p).IsInitialVertex c

variable {p}

lemma isColimit_iff (c : (coslice p) _⦋0⦌) : IsColimit p c ↔ (coslice p).IsInitialVertex c :=
  Iff.rfl

/-- Colimit cocones under `p` are the limit cones over the opposite diagram `pᵒᵖ` in the
opposite simplicial set `Cᵒᵖ`, under the identification of `C_{p/}` with `(Cᵒᵖ_{/pᵒᵖ})ᵒᵖ`. -/
lemma isColimit_iff_isLimit_op (c : (coslice p) _⦋0⦌) :
    IsColimit p c ↔ slice.IsLimit (opFunctor.map p)
      ((slice (opFunctor.map p)).opObjEquiv ((opSliceIso p).hom.app _ c)) := by
  have h := isInitialVertex_op_iff
    ((slice (opFunctor.map p)).opObjEquiv ((opSliceIso p).hom.app _ c))
  rw [Equiv.symm_apply_apply] at h
  rw [isColimit_iff, ← isInitialVertex_iff_of_iso (opSliceIso p), h, slice.isLimit_iff]

namespace IsColimit

variable {c c' : (coslice p) _⦋0⦌}

/-- Every cocone has a morphism from a colimit cocone. -/
lemma nonempty_edge (hc : IsColimit p c) (d : (coslice p) _⦋0⦌) :
    Nonempty ((coslice p).Edge c d) :=
  IsInitialVertex.nonempty_edge hc d

/-- Every morphism between colimit cocones is an equivalence. Thus colimit cocones are unique up
to equivalence. -/
lemma isEquivalence (hc : IsColimit p c) (hc' : IsColimit p c') (e : (coslice p).Edge c c') :
    e.IsEquivalence :=
  let ⟨I⟩ := IsInitialVertex.nonempty_invStruct hc hc' e
  I.isEquivalence

end IsColimit

variable (p) in
/-- The colimit cocones of the empty diagram are the initial vertices: when `K` is empty, a cocone
under `p` is a colimit cocone exactly when its cone point is an initial vertex of `C`. -/
lemma isColimit_iff_isInitialVertex_π (hK : ¬ K.Nonempty) (c : (coslice p) _⦋0⦌) :
    IsColimit p c ↔ C.IsInitialVertex ((π p).app _ c) :=
  have := isIso_π p hK
  (isInitialVertex_iff_of_iso (asIso (π p)) c).symm

/-- In the nerve of a category `D`, the colimit cocones of the empty diagram are the cocones whose
cone point is an initial object of `D`. -/
lemma isColimit_iff_nonempty_isInitial {D : Type u'} [Category.{v} D] {L : SSet.{max u' v}}
    (q : L ⟶ nerve D) (hL : ¬ L.Nonempty) (c : (coslice q) _⦋0⦌) :
    IsColimit q c ↔ Nonempty (IsInitial (nerveEquiv ((π q).app _ c))) := by
  rw [isColimit_iff_isInitialVertex_π q hL]
  generalize (π q).app _ c = v
  obtain ⟨x, rfl⟩ := nerveEquiv.symm.surjective v
  rw [nerve.isInitialVertex_iff, Equiv.apply_symm_apply]

/-- Colimit cocones are invariant under isomorphisms of diagrams: restricting cocones along an
isomorphism `i` and pushing them forward along an isomorphism `g` preserves and reflects colimit
cocones. -/
lemma isColimit_map_iff_of_isIso {L D : SSet.{u}} {q : L ⟶ D} (i : L ⟶ K) [IsIso i] (g : C ⟶ D)
    [IsIso g] (h : i ≫ p ≫ g = q) (c : (coslice p) _⦋0⦌) :
    IsColimit q ((map i g h).app _ c) ↔ IsColimit p c :=
  isInitialVertex_iff_of_iso (asIso (map i g h)) c

/-- In the nerve of a preorder `P`, a cocone under a diagram `q` is a colimit cocone exactly when
its cone point is a least upper bound of the vertices of `q`. -/
lemma isColimit_iff_isLUB {P : Type u} [Preorder P] (q : K ⟶ nerve P) (c : (coslice q) _⦋0⦌) :
    IsColimit q c ↔ IsLUB (Set.range fun k : K _⦋0⦌ ↦ nerveEquiv (q.app _ k))
      (nerveEquiv ((π q).app _ c)) := by
  -- Pass to the nerve of the upper bounds of the vertices of `q`, where the cocone is its cone
  -- point, and an initial vertex is an initial object, that is a least element.
  rw [isColimit_iff, ← isInitialVertex_iff_of_iso (nerve.upperBoundsCosliceIso q).symm,
    Iso.symm_hom, ← nerveEquiv.symm_apply_apply ((nerve.upperBoundsCosliceIso q).inv.app _ c),
    nerve.isInitialVertex_iff, ← nerve.nerveEquiv_upperBoundsCosliceIso_inv_app_coe]
  generalize nerveEquiv ((nerve.upperBoundsCosliceIso q).inv.app _ c) = b
  exact ⟨fun ⟨hb⟩ ↦ ⟨b.property, fun x hx ↦ (hb.to ⟨x, hx⟩).le⟩, fun hb ↦
    ⟨IsInitial.ofUniqueHom (fun y ↦ homOfLE (hb.2 y.property)) fun _ _ ↦ Subsingleton.elim _ _⟩⟩

/-- A diagram `q` in the nerve of a preorder has a colimit cocone exactly when its vertices have a
least upper bound. -/
lemma exists_isColimit_iff_exists_isLUB {P : Type u} [Preorder P] (q : K ⟶ nerve P) :
    (∃ c, IsColimit q c) ↔ ∃ b, IsLUB (Set.range fun k : K _⦋0⦌ ↦ nerveEquiv (q.app _ k)) b := by
  refine ⟨fun ⟨c, hc⟩ ↦ ⟨_, (isColimit_iff_isLUB q c).1 hc⟩, fun ⟨b, hb⟩ ↦
    ⟨(nerve.upperBoundsCosliceIso q).hom.app (op ⦋0⦌) (nerveEquiv.symm ⟨b, hb.1⟩), ?_⟩⟩
  -- The cocone given by the upper bound `b` has cone point `b`.
  have h := nerve.nerveEquiv_yonedaEquiv_inr_comp_objEquiv_upperBoundsCosliceIso_hom_app_coe q
    (nerveEquiv.symm ⟨b, hb.1⟩)
  rw [← π_app, Equiv.apply_symm_apply] at h
  exact (isColimit_iff_isLUB q _).2 (h.symm ▸ hb)

variable (p) in
/-- In a terminal simplicial set, such as `Δ[0]`, every cocone is a colimit cocone. -/
lemma isColimit_of_isTerminal (hC : IsTerminal C) (c : (coslice p) _⦋0⦌) : IsColimit p c :=
  isInitialVertex_of_isTerminal (isTerminal p hC) c

variable (p) in
/-- A diagram `p` has a colimit cocone exactly when the opposite diagram `pᵒᵖ` has a limit cone in
`Cᵒᵖ`. -/
lemma exists_isColimit_iff_exists_isLimit_op :
    (∃ c, IsColimit p c) ↔ ∃ c, slice.IsLimit (opFunctor.map p) c :=
  ⟨fun ⟨c, hc⟩ ↦ ⟨_, (isColimit_iff_isLimit_op c).1 hc⟩, fun ⟨c, hc⟩ ↦
    ⟨(opSliceIso p).inv.app _ ((slice (opFunctor.map p)).opObjEquiv.symm c),
      (isColimit_iff_isLimit_op _).2 (by simpa using hc)⟩⟩

/-- Having a colimit cocone is invariant under isomorphisms of diagrams: if `q` is obtained from
`p` by precomposing and postcomposing with isomorphisms `i` and `g`, then `q` has a colimit cocone
exactly when `p` has one. -/
lemma exists_isColimit_iff_of_isIso {L D : SSet.{u}} {q : L ⟶ D} (i : L ⟶ K) [IsIso i]
    (g : C ⟶ D) [IsIso g] (h : i ≫ p ≫ g = q) : (∃ c, IsColimit q c) ↔ ∃ c, IsColimit p c := by
  rw [exists_isColimit_iff_exists_isLimit_op q, exists_isColimit_iff_exists_isLimit_op p]
  exact slice.exists_isLimit_iff_of_isIso (opFunctor.map i) (opFunctor.map g) (by simp [← h])

/-- A cocone pushed forward along maps `i` and `g` is a colimit cocone exactly when the
corresponding cone in `Cᵒᵖ`, pushed forward along `iᵒᵖ` and `gᵒᵖ`, is a limit cone. The maps `i'`
and `g'` are any maps equal to `iᵒᵖ` and `gᵒᵖ`, such as `𝟙 Lᵒᵖ` for `i = 𝟙 L`. -/
lemma isColimit_map_iff_isLimit_op {L D : SSet.{u}} {q : L ⟶ D} (i : L ⟶ K) (g : C ⟶ D)
    (h : i ≫ p ≫ g = q) {i' : L.op ⟶ K.op} {g' : C.op ⟶ D.op} (hi : opFunctor.map i = i')
    (hg : opFunctor.map g = g') (c : (coslice p) _⦋0⦌) :
    IsColimit q ((map i g h).app _ c) ↔ slice.IsLimit (opFunctor.map q)
      ((slice.map i' g' (by simp [← hi, ← hg, ← h])).app _
        ((slice (opFunctor.map p)).opObjEquiv ((opSliceIso p).hom.app _ c))) := by
  rw [isColimit_iff_isLimit_op]
  -- Evaluate the identification of maps of coslices with opposite maps of slices at `c`.
  have e := congr_arg (fun f ↦ f.app _ ((opSliceIso p).hom.app _ c))
    (opSliceIso_inv_comp_map i g h hi hg)
  simp only [NatTrans.comp_app, ConcreteCategory.comp_apply, Iso.hom_inv_id_app_apply] at e
  rw [e, Iso.inv_hom_id_app_apply, opFunctor_map, Equiv.apply_symm_apply]

end coslice

end SSet
