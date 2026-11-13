/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Descent.OverBaseChange
public import TauCeti.CategoryTheory.EffectiveEpi.Subgroup

/-!
# Effective fpqc descent of closed subgroup schemes

Let `G` be a group scheme over `S` and let `p : S' ⟶ S` be surjective, flat and quasi-compact.
A closed subgroup of `G ×_S S'` stable under the canonical descent datum descends to a closed
subgroup of `G`. The comparison preserves both the descent datum and the group law. If the
subgroup is finite locally free over `S'`, the descended subgroup is finite locally free over
`S`, with its rank pulled back to the original rank.

Effective descent for closed subschemes supplies the carrier and inclusion. Being a subgroup
is then checked after base change, using descent of factorization through a monomorphism.
In particular, compatibility of the local operations with descent is a consequence of the
subgroup inclusion, rather than an additional assumption. The group structure is unique by
`TauCeti.grpObj_eq_of_mono`; uniqueness of the descended carrier with its descent comparison
is `TauCeti.DescentDatum.Hom.descendIso`.

## References

* A. Grothendieck, *Revêtements étales et groupe fondamental* (SGA 1), Exposé VIII, §2.
* N. M. Katz and B. Mazur, *Arithmetic Moduli of Elliptic Curves*, §1.3.
* The Stacks Project, Tag 0245 (effective descent for affine morphisms).
-/

public section

open CategoryTheory Limits AlgebraicGeometry
open scoped MonObj Obj

namespace TauCeti.DescentDatum

universe u

variable {S S' : Scheme.{u}} {p : S' ⟶ S} [Surjective p] [Flat p] [QuasiCompact p]
  {G : Grp (Over S)} {H : Over S'} [GrpObj H] (D : DescentDatum p H)

/-- **Effective fpqc descent of a stable closed subgroup.** A closed subgroup of the base change
of `G`, whose inclusion respects a descent datum, descends to a closed subgroup of `G`.
The comparison is simultaneously an isomorphism of descent data and a group homomorphism. -/
theorem exists_closedSubgroup_baseChange_hom_isIso
    (i : Hom D (baseChange p G.X)) [IsClosedImmersion i.hom.left] [IsMonHom i.hom] :
    ∃ (K : Grp (Over S)) (j : K ⟶ G) (e : Hom (baseChange p K.X) D),
      IsClosedImmersion j.hom.hom.left ∧ IsIso e.hom ∧ IsMonHom e.hom ∧
        i.comp e = baseChangeHom p j.hom.hom := by
  obtain ⟨W, e, he, hfac, hW⟩ := i.exists_baseChange_hom_isIso_of_isClosedImmersion
  let K₀ : Over S := Over.mk (W.hom ≫ G.X.hom)
  let j₀ : K₀ ⟶ G.X := Over.homMk W.hom
  have : IsClosedImmersion j₀.left := hW
  have : Mono j₀ := Over.mono_of_mono_left j₀
  have heq : e.hom ≫ i.hom = (Over.pullback p).map j₀ := by
    simpa only [Hom.comp_hom, baseChangeHom_hom] using congr(Hom.hom $hfac)
  -- Transport the local subgroup structure to the chosen pullback of the descended carrier.
  let hlocal : GrpObj ((Over.pullback p).obj K₀) := GrpObj.ofIso (asIso e.hom).symm
  have hcomp : IsMonHom e.hom := by
    have := isMonHom_ofIso (asIso e.hom).symm
    exact inferInstanceAs (IsMonHom ((asIso e.hom).symm.inv))
  have hjlocal : IsMonHom ((Over.pullback p).map j₀) := by
    rw [← heq]
    infer_instance
  obtain ⟨hK, hj⟩ := (exists_grpObj_isMonHom_pullback_iff p j₀).1 ⟨hlocal, hjlocal⟩
  let := hK
  let := hj
  -- The two group structures on the pullback have the same monic inclusion into `G`.
  have hstructures : Functor.grpObjObj (F := Over.pullback p) (G := K₀) = hlocal :=
    grpObj_eq_of_mono ((Over.pullback p).map j₀) _ _ inferInstance hjlocal
  have hehom : @IsMonHom _ _ _ ((Over.pullback p).obj K₀) H
      (Functor.grpObjObj (F := Over.pullback p) (G := K₀)).toMonObj inferInstance e.hom := by
    rw [hstructures]
    exact hcomp
  exact ⟨Grp.mk K₀, Grp.ofHom j₀, e, hW, he, hehom, hfac⟩

/-- **Effective fpqc descent of finite locally free subgroup schemes, with rank.** A stable
closed subgroup which is finite, flat and locally of finite presentation over the cover descends
with these three properties. Its finite-flat rank is pulled back from the descended subgroup. -/
theorem exists_finiteLocallyFree_closedSubgroup_baseChange_hom_isIso
    [IsFinite H.hom] [Flat H.hom] [LocallyOfFinitePresentation H.hom]
    (i : Hom D (baseChange p G.X)) [IsClosedImmersion i.hom.left] [IsMonHom i.hom] :
    ∃ (K : Grp (Over S)) (j : K ⟶ G) (e : Hom (baseChange p K.X) D),
      IsClosedImmersion j.hom.hom.left ∧ IsIso e.hom ∧ IsMonHom e.hom ∧
        i.comp e = baseChangeHom p j.hom.hom ∧
        IsFinite K.X.hom ∧ Flat K.X.hom ∧ LocallyOfFinitePresentation K.X.hom ∧
        H.hom.finrank = K.X.hom.finrank ∘ p := by
  obtain ⟨K, j, e, hj, he, hehom, hfac⟩ := D.exists_closedSubgroup_baseChange_hom_isIso i
  have : IsFinite K.X.hom := e.mem_of_descendsAlong (P := @IsFinite) inferInstance
  have : Flat K.X.hom := e.mem_of_descendsAlong (P := @Flat) inferInstance
  have : LocallyOfFinitePresentation K.X.hom :=
    e.mem_of_descendsAlong (P := @LocallyOfFinitePresentation) inferInstance
  refine ⟨K, j, e, hj, he, hehom, hfac, inferInstance, inferInstance, inferInstance, ?_⟩
  funext s
  have hw := e.hom.w
  simp only [Over.pullback_obj_hom] at hw
  rw [← Scheme.Hom.finrank_comp_left_of_isIso e.hom.left H.hom, hw]
  exact Scheme.Hom.finrank_pullback_snd _ _ s

end TauCeti.DescentDatum
