/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Quasicategory.OuterHorn.Parametrized
public import TauCeti.AlgebraicTopology.SimplicialSet.WeaklyContractible

/-!
# The quasicategory of equivalences

For a simplicial set `C`, the vertices of `Fun(Δ[1], C) = (ihom Δ[1]).obj C` are the edges of
`C`. The full enhanced subcategory `SSet.isom C` of `Fun(Δ[1], C)` spanned by the equivalences of
`C` is the quasicategory of equivalences of `C` when `C` is a quasicategory. Its simplices are the
maps `Δ[1] ⊗ Δ[n] ⟶ C` all of whose vertical edges `(0, t) ⟶ (1, t)` are equivalences.

The main result is that, for a quasicategory `C`, evaluation at either vertex of `Δ[1]` is a
trivial fibration `SSet.isom C ⟶ C` (`SSet.isom.rlp_evalAt`). By adjunction, a lifting problem of
a boundary inclusion `∂Δ[n + 1] ⟶ Δ[n + 1]` against evaluation at the vertex `i` is an extension
problem along the prism inclusion `(Λ[1, i] ⊗ Δ[n + 1]) ∪ (Δ[1] ⊗ ∂Δ[n + 1]) ⟶ Δ[1] ⊗ Δ[n + 1]`
with invertible vertical edges, solved by
`SSet.prodStdSimplex.exists_ext_unionProd_horn_one_zero` and
`SSet.prodStdSimplex.exists_ext_unionProd_horn_one_one`. Over `∂Δ[0]`, which is empty, the
identity edges provide the lifts.

This is how natural transformations with invertible components are compared with their source
and target: a natural transformation `F ⟶ G` of maps `X ⟶ C` whose components are equivalences
is a map `X ⟶ SSet.isom C` whose evaluations at the two vertices of `Δ[1]` are `F` and `G`, and
the evaluations, being trivial fibrations, induce weak equivalences of right mapping spaces
(see `TauCeti.AlgebraicTopology.Quasicategory.FullyFaithful`).

## Main definitions

* `SSet.isom C`: the full enhanced subcategory of `Fun(Δ[1], C)` on the equivalences of `C`;
  its vertices are the equivalences (`SSet.mem_isom_obj_zero_iff`), and a map factors through it
  exactly when it sends every vertex to an equivalence (`SSet.range_le_isom_iff`).

## Main results

* `SSet.isom.range_constMaps_le`: the identity edges are equivalences.
* `SSet.isom.rlp_evalAt`: for a quasicategory `C`, evaluation `SSet.isom C ⟶ C` at either vertex
  of `Δ[1]` is a trivial fibration.

## References

* A. Joyal, *Quasi-categories and Kan complexes*, J. Pure Appl. Algebra 175 (2002).
* J. Lurie, *Higher Topos Theory*, Proposition 1.2.4.3.
-/

public section

universe u

open CategoryTheory MonoidalCategory CartesianMonoidalCategory MonoidalClosed Limits
  MorphismProperty Simplicial

namespace SSet

variable {C : SSet.{u}}

variable (C) in
/-- The quasicategory of equivalences of `C`: the full enhanced subcategory of
`Fun(Δ[1], C) = (ihom Δ[1]).obj C` on the vertices whose edge of `C` is an equivalence. -/
def isom : ((ihom Δ[1]).obj C).Subcomplex :=
  ((ihom Δ[1]).obj C).fullEnhancedSubcategory fun v ↦
    (Edge.mk' ((ihomObj₀Equiv _ C v).app _ (stdSimplex.edge 1 0 1 (Fin.zero_le _)))).IsEquivalence

/-- The quasicategory of equivalences is the full enhanced subcategory on equivalence edges. -/
lemma isom_def : isom C = ((ihom Δ[1]).obj C).fullEnhancedSubcategory (fun v ↦
    (Edge.mk' ((ihomObj₀Equiv _ C v).app _
      (stdSimplex.edge 1 0 1 (Fin.zero_le _)))).IsEquivalence) := (rfl)

/-- A simplex lies in the quasicategory of equivalences exactly when each of its vertices
corresponds to an equivalence edge of `C`. -/
lemma mem_isom_obj_iff {n : SimplexCategoryᵒᵖ} (s : ((ihom Δ[1]).obj C).obj n) :
    s ∈ (isom C).obj n ↔ ∀ v : ⦋0⦌ ⟶ n.unop,
      (Edge.mk' ((ihomObj₀Equiv _ C (((ihom Δ[1]).obj C).map v.op s)).app _
        (stdSimplex.edge 1 0 1 (Fin.zero_le _)))).IsEquivalence := by
  rw [isom_def, mem_fullEnhancedSubcategory_obj_iff]

/-- The full enhanced subcategory on equivalence edges of a quasicategory is a quasicategory. -/
instance [Quasicategory C] : Quasicategory (isom C : SSet) := by
  rw [isom_def]
  infer_instance

/-- A vertex of `Fun(Δ[1], C)` lies in the quasicategory of equivalences exactly when its edge of
`C` is an equivalence. -/
@[simp]
lemma mem_isom_obj_zero_iff (v : ((ihom Δ[1]).obj C) _⦋0⦌) :
    v ∈ (isom C).obj (Opposite.op ⦋0⦌) ↔ (Edge.mk' ((ihomObj₀Equiv _ C v).app _
      (stdSimplex.edge 1 0 1 (Fin.zero_le _)))).IsEquivalence :=
  mem_fullEnhancedSubcategory_obj_zero_iff _ v

/-- A map to `Fun(Δ[1], C)` factors through the quasicategory of equivalences exactly when it sends
every vertex to an equivalence of `C`. -/
lemma range_le_isom_iff {Z : SSet.{u}} (f : Z ⟶ (ihom Δ[1]).obj C) :
    Subcomplex.range f ≤ isom C ↔ ∀ z : Z _⦋0⦌, (Edge.mk' ((ihomObj₀Equiv _ C (f.app _ z)).app _
      (stdSimplex.edge 1 0 1 (Fin.zero_le _)))).IsEquivalence :=
  range_le_fullEnhancedSubcategory_iff _ f

namespace isom

/-- The constant maps `C ⟶ Fun(Δ[1], C)` factor through the quasicategory of equivalences: an
identity edge is an equivalence. -/
lemma range_constMaps_le : Subcomplex.range (constMaps Δ[1] C) ≤ isom C := by
  refine (range_le_isom_iff _).2 fun z ↦ ?_
  rw [ihomObj₀Equiv_constMaps_app]
  exact Edge.isEquivalence_mk'_map_of_eq _ _ rfl

/-- A lifting problem of `∂Δ[n + 1] ⟶ Δ[n + 1]` against evaluation `SSet.isom C ⟶ C` at the
vertex `i` of `Δ[1]` has a solution as soon as the prism inclusion
`(Λ[1, i] ⊗ Δ[n + 1]) ∪ (Δ[1] ⊗ ∂Δ[n + 1]) ⟶ Δ[1] ⊗ Δ[n + 1]` has extensions for maps with
invertible vertical edges. Here `j` is the other vertex, so that `Λ[1, i]` is the face
`stdSimplex.δ j`. -/
private lemma hasLift_boundary_succ (i j : Fin 2) (hij : j ≠ i)
    (hδ : stdSimplex.{u}.δ j = yonedaEquiv.symm (stdSimplex.obj₀Equiv.symm i)) {n : ℕ}
    (hext : ∀ a : (Subcomplex.unionProd Λ[1, i] ∂Δ[n + 1] : SSet.{u}) ⟶ C,
      (∀ t : Fin (n + 2), (Edge.mk' (a.app _ ⟨(stdSimplex.edge 1 0 1 (Fin.zero_le _),
        stdSimplex.const (n + 1) t _),
          prodStdSimplex.const_mem_unionProd_boundary _ t _⟩)).IsEquivalence) →
      ∃ b : Δ[1] ⊗ Δ[n + 1] ⟶ C, (Subcomplex.unionProd Λ[1, i] ∂Δ[n + 1]).ι ≫ b = a)
    {t : (∂Δ[n + 1] : SSet.{u}) ⟶ (isom C : SSet.{u})} {b : Δ[n + 1] ⟶ C}
    (sq : CommSq t ∂Δ[n + 1].ι ((isom C).ι ≫ evalAt (stdSimplex.obj₀Equiv.symm i) C) b) :
    sq.HasLift := by
  -- The horn `Λ[1, i]` is the vertex `i` of `Δ[1]`.
  let e : Δ[0] ⟶ (Λ[1, i] : SSet.{u}) := horn.ι i j hij
  have he : e ≫ Λ[1, i].ι = stdSimplex.δ j := horn.ι_ι _ _ _
  have := horn.isIso_ι_one i j hij
  -- By adjunction, the lifting problem is a map on `(Λ[1, i] ⊗ Δ[n + 1]) ∪ (Δ[1] ⊗ ∂Δ[n + 1])`.
  have hw : Λ[1, i].ι ▷ _ ≫ uncurry (t ≫ (isom C).ι) =
      (Λ[1, i] : SSet.{u}) ◁ ∂Δ[n + 1].ι ≫ snd _ _ ≫ b := by
    rw [← cancel_epi (e ▷ _), ← comp_whiskerRight_assoc, he, hδ,
      yonedaEquiv_symm_whiskerRight_uncurry, ← whisker_exchange_assoc, whiskerRight_snd_assoc,
      whiskerLeft_snd_assoc, Category.assoc, sq.w]
  let a := (Subcomplex.unionProd.isPushout Λ[1, i] ∂Δ[n + 1]).desc
    (uncurry (t ≫ (isom C).ι)) (snd _ _ ≫ b) hw
  -- Its vertical edges are the edges of the vertices of `∂Δ[n + 1]` under `t`.
  obtain ⟨L, hL⟩ := hext a fun s ↦ by
    let y : (∂Δ[n + 1] : SSet.{u}) _⦋0⦌ :=
      ⟨stdSimplex.const (n + 1) s _, by rw [boundary_obj_eq_univ 0 (n + 1)]; trivial⟩
    have h₁ := congr($((Subcomplex.unionProd.isPushout Λ[1, i] ∂Δ[n + 1]).inl_desc
      (uncurry (t ≫ (isom C).ι)) (snd _ _ ≫ b) hw).app _
        (stdSimplex.edge 1 0 1 (Fin.zero_le _), (const y : Δ[1] ⟶ _).app _
          (stdSimplex.edge 1 0 1 (Fin.zero_le _))))
    have h₂ := congr($(ihomObj₀Equiv_app (t ≫ (isom C).ι) y).app _
      (stdSimplex.edge 1 0 1 (Fin.zero_le _)))
    have key : a.app _ ⟨(stdSimplex.edge 1 0 1 (Fin.zero_le _), stdSimplex.const (n + 1) s _),
        prodStdSimplex.const_mem_unionProd_boundary _ s _⟩ =
        (ihomObj₀Equiv _ C (t.app _ y).val).app _ (stdSimplex.edge 1 0 1 (Fin.zero_le _)) :=
      h₁.trans h₂.symm
    rw [key]
    exact (mem_isom_obj_zero_iff _).1 (t.app _ y).property
  -- The curried extension restricts to `t` on `∂Δ[n + 1]`, which contains every vertex.
  have hcurry : ∂Δ[n + 1].ι ≫ curry L = t ≫ (isom C).ι := by
    rw [← curry_natural_left, ← Subcomplex.unionProd.ι₁_ι, Category.assoc, hL,
      IsPushout.inl_desc, curry_uncurry]
  have hrange : Subcomplex.range (curry L) ≤ isom C := by
    refine (range_le_isom_iff _).2 fun z ↦ ?_
    have hz : z ∈ (∂Δ[n + 1]).obj _ := by rw [boundary_obj_eq_univ 0 (n + 1)]; trivial
    have h : (curry L).app _ z = (t.app _ ⟨z, hz⟩).val := congr(($hcurry).app _ ⟨z, hz⟩)
    rw [h]
    exact (mem_isom_obj_zero_iff _).1 (t.app _ ⟨z, hz⟩).property
  -- Evaluation at `i` restricts to `Λ[1, i] ⊗ Δ[n + 1]`, where the extension is `b`.
  have hv : (lift (const (stdSimplex.obj₀Equiv.symm i)) (𝟙 _) : Δ[n + 1] ⟶ Δ[1] ⊗ Δ[n + 1]) =
      lift (stdSimplex.isTerminalObj₀.from _ ≫ e) (𝟙 _) ≫ Λ[1, i].ι ▷ _ := by
    ext : 1
    · rw [lift_fst, Category.assoc, whiskerRight_fst, lift_fst_assoc, Category.assoc, he, hδ,
        yonedaEquiv_symm_zero, comp_const]
    · simp
  refine ⟨⟨{ l := Subcomplex.lift _ hrange, fac_left := ?_, fac_right := ?_ }⟩⟩
  · rw [← cancel_mono (isom C).ι, Category.assoc, Subcomplex.lift_ι, hcurry]
  · rw [← Category.assoc, Subcomplex.lift_ι, curry_evalAt, hv, Category.assoc,
      ← Subcomplex.unionProd.ι₂_ι, Category.assoc, hL, IsPushout.inr_desc, lift_snd_assoc,
      Category.id_comp]

/-- **Evaluation on the quasicategory of equivalences is a trivial fibration.** For a
quasicategory `C` and a vertex `i` of `Δ[1]`, evaluation `SSet.isom C ⟶ C` at `i` has the right
lifting property with respect to every monomorphism: a family of equivalences of `C` given over a
simplicial subset of the parameter space extends to the whole parameter space along any extension
of its sources, or of its targets. -/
theorem rlp_evalAt [Quasicategory C] (i : Fin 2) :
    (monomorphisms SSet.{u}).rlp ((isom C).ι ≫ evalAt (stdSimplex.obj₀Equiv.symm i) C) := by
  rw [rlp_monomorphisms]
  rintro _ _ _ ⟨_ | n⟩
  · -- Over `∂Δ[0]`, which is empty, the identity edges lift.
    refine ⟨fun {t b} sq ↦ ?_⟩
    refine ⟨⟨{ l := b ≫ Subcomplex.lift _ range_constMaps_le, fac_left := ?_, fac_right := ?_ }⟩⟩
    · ext
    rw [Category.assoc, ← Category.assoc (Subcomplex.lift _ _), Subcomplex.lift_ι,
      constMaps_evalAt, Category.comp_id]
  · refine ⟨fun sq ↦ ?_⟩
    fin_cases i
    · exact hasLift_boundary_succ 0 1 (by decide)
        (by rw [stdSimplex.δ_one_eq_const, yonedaEquiv_symm_zero])
        (prodStdSimplex.exists_ext_unionProd_horn_one_zero) sq
    · exact hasLift_boundary_succ 1 0 (by decide)
        (by rw [stdSimplex.δ_zero_eq_const, yonedaEquiv_symm_zero])
        (prodStdSimplex.exists_ext_unionProd_horn_one_one) sq

end isom

end SSet
