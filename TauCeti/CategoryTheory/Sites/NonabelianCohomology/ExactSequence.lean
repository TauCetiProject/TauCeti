/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Sites.NonabelianCohomology.Map

/-!
# The exact sequence of nonabelian cohomology

Let `1 → A → B → Q → 1` be a short exact sequence of sheaves of groups on a site `(C, J)`, given
by `i : A ⟶ B` and `π : B ⟶ Q`. This file proves that the sequence of pointed sets
`1 → A(C) → B(C) → Q(C) → H¹(A) → H¹(B) → H¹(Q)` is exact, where `Q(C) → H¹(A)` is the
connecting map `NonabelianH1.connecting` sending a global section of `Q` to its torsor of lifts.
Exactness at `A(C)` and `B(C)` is `IsGroupExtension.existsUnique_sections_iff` and exactness
at `Q(C)` is `NonabelianH1.connecting_eq_one_iff`; this file adds the other positions.

* At `H¹(A)`: an `A`-torsor `P` becomes trivial as a `B`-torsor if and only if it is a torsor of
  lifts. A trivialisation of `P ×^A B` is an `i`-equivariant morphism `u : P → B`, and `π ∘ u`
  is constant on `P`, so it is a global section `q` of `Q`; then `u` identifies `P` with the
  torsor of lifts of `q`.
* At `H¹(B)`: a `B`-torsor `P` becomes trivial as a `Q`-torsor if and only if it comes from an
  `A`-torsor. A trivialisation of `P ×^B Q` is a `π`-equivariant morphism `u : P → Q`, and the
  fibre `u⁻¹(1)` is an `A`-torsor whose contracted product along `i` is `P`.

## Main declarations

* `CategoryTheory.Sheaf.NonabelianH1.map_eq_one_iff_mem_range_connecting`: exactness at
  `H¹(A)`.
* `CategoryTheory.Sheaf.NonabelianH1.map_eq_one_iff_mem_range_map`: exactness at `H¹(B)`.

## References

* J.-P. Serre, *Galois cohomology*, Chapter I, §5.5, Proposition 38, for the analogous exact
  sequence in the nonabelian cohomology of profinite groups.
* J. Giraud, *Cohomologie non abélienne*, Chapitre III, §3.3, for the exact sequence of an
  extension of sheaves of groups.
-/

public noncomputable section

open CategoryTheory Opposite

universe w v u

namespace CategoryTheory.Sheaf

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  {A B Q : Sheaf J GrpCat.{w}} {i : A ⟶ B} {π : B ⟶ Q}

namespace Torsor

variable {P : Torsor B}

/-- The subpresheaf of a `B`-torsor `P` of the sections `p` with `u p = 1`, for a
`π`-equivariant morphism `u` from `P` to `Q`. -/
private def fibreSubfunctor (u : P.sheaf ⟶ (Torsor.trivial Q).sheaf) :
    Subfunctor P.sheaf.obj where
  obj U := {p | u.hom.app U p = (1 : Q.obj.obj U)}
  map f p hp := Set.mem_preimage.2 <| Set.mem_ofPred.2 <|
    (NatTrans.naturality_apply u.hom f p).trans
      ((congrArg _ (Set.mem_ofPred.1 hp)).trans (map_one (Q.obj.map f).hom))

/-- Membership in the fibre over `1`. -/
private lemma mem_fibreSubfunctor_iff (u : P.sheaf ⟶ (Torsor.trivial Q).sheaf) {U : Cᵒᵖ}
    (p : P.sheaf.obj.obj U) :
    p ∈ (fibreSubfunctor u).obj U ↔ u.hom.app U p = (1 : Q.obj.obj U) :=
  Iff.rfl

/-- The fibre over `1` of a morphism to the sheaf `Q` is a sheaf, because `Q` is separated. -/
private lemma isSheaf_fibreSubfunctor (u : P.sheaf ⟶ (Torsor.trivial Q).sheaf) :
    Presheaf.IsSheaf J (fibreSubfunctor u).toFunctor := by
  have hP := (isSheaf_iff_isSheaf_of_type J _).1 P.sheaf.property
  have hQ := (isSheaf_iff_isSheaf_of_type J _).1 (Torsor.trivial Q).sheaf.property
  refine (isSheaf_iff_isSheaf_of_type J _).2 (((fibreSubfunctor u).isSheaf_iff hP).2 ?_)
  intro U p hp
  refine (hQ.isSeparated _ hp).ext fun V f hf ↦ ?_
  exact (NatTrans.naturality_apply u.hom f.op p).symm.trans
    (hf.trans (map_one (Q.obj.map f.op).hom).symm)

variable (hE : IsGroupExtension i π)

/-- The reduction of a `B`-torsor `P` to an `A`-torsor along a `π`-equivariant morphism
`u : P → Q`: the fibre of `u` over `1`, on which `A` acts through `i`. -/
private def reduction (u : P.sheaf ⟶ (Torsor.trivial Q).sheaf)
    (hu : ∀ (U : Cᵒᵖ) (b : B.obj.obj U) (p : P.sheaf.obj.obj U),
      u.hom.app U (b • p) = π.hom.app U b • u.hom.app U p) : Torsor A where
  sheaf := ⟨(fibreSubfunctor u).toFunctor, isSheaf_fibreSubfunctor u⟩
  mulAction U :=
    { smul a p := ⟨i.hom.app U a • p.1, by
        rw [mem_fibreSubfunctor_iff, hu, trivial_smul, hE.app_app_eq_one,
          (mem_fibreSubfunctor_iff u p.1).1 p.2, mul_one]⟩
      one_smul p := Subtype.ext ((congrArg (· • p.1) (map_one _)).trans (one_smul _ _))
      mul_smul a a' p := Subtype.ext ((congrArg (· • p.1) (map_mul _ a a')).trans
        (mul_smul _ _ _)) }
  map_smul U V f a p := Subtype.ext ((P.map_smul f _ p.1).trans
    (congrArg (· • P.sheaf.obj.map f p.1) (NatTrans.naturality_apply i.hom f a).symm))
  coversTop X := by
    have := hE.isLocallySurjective
    refine J.transitive (P.coversTop X) _ fun V f ⟨j, ⟨g⟩⟩ ↦ ?_
    -- Over `V` the torsor `P` has a section `p`. Locally `(u p)⁻¹ = π b` for a section `b` of
    -- `B`, and then `b • p` lies in the fibre over `1`.
    let p := P.sheaf.obj.map g.op j.2.some
    let q₀ : Q.obj.obj (op V) := u.hom.app (op V) p
    refine J.superset_covering ?_ (Presheaf.imageSieve_mem J π.hom q₀⁻¹)
    rintro W h ⟨b, hb⟩
    refine ⟨⟨W, ⟨⟨b • P.sheaf.obj.map h.op p, ?_⟩⟩⟩, ⟨𝟙 W⟩⟩
    have hnat : @Eq (Q.obj.obj (op W)) (u.hom.app (op W) (P.sheaf.obj.map h.op p))
        (Q.obj.map h.op q₀) :=
      NatTrans.naturality_apply u.hom h.op p
    rw [mem_fibreSubfunctor_iff, hu, trivial_smul, hb, hnat, map_inv, inv_mul_cancel]
  bijective U := by
    refine ⟨fun ⟨a, p⟩ ⟨a', p'⟩ h ↦ ?_, fun ⟨p, p'⟩ ↦ ?_⟩
    · obtain ⟨h₁, rfl⟩ := Prod.ext_iff.1 h
      exact Prod.ext (hE.injective U (P.smul_left_injective p.1 (congrArg Subtype.val h₁))) rfl
    · obtain ⟨b, hb⟩ := MulAction.exists_smul_eq (B.obj.obj U) p'.1 p.1
      -- `u p = π b * u p'`, and `u p = u p' = 1`, so `π b = 1` and `b` comes from `A`.
      have hπb : π.hom.app U b = 1 := by
        have h := (hu U b p'.1).symm.trans (congrArg (u.hom.app U) hb)
        rw [(mem_fibreSubfunctor_iff u p.1).1 p.2] at h
        exact (mul_one _).symm.trans ((congrArg (π.hom.app U b * ·)
          ((mem_fibreSubfunctor_iff u p'.1).1 p'.2).symm).trans h)
      obtain ⟨a, rfl⟩ := hE.exists_app_eq hπb
      exact ⟨(a, p'), Prod.ext (Subtype.ext hb) rfl⟩

end Torsor

namespace NonabelianH1

variable [HasWeakSheafify J (Type w)] [J.WEqualsLocallyBijective (Type w)]
  (hE : IsGroupExtension i π)

/-- Exactness of `Q(C) → H¹(A) → H¹(B)` at `H¹(A)`: an `A`-torsor becomes trivial as a
`B`-torsor if and only if it is isomorphic to the torsor of lifts of a global section of `Q`. -/
theorem map_eq_one_iff_mem_range_connecting (x : NonabelianH1 A) :
    map i x = 1 ↔ x ∈ Set.range (connecting hE) := by
  refine ⟨fun h ↦ ?_, fun ⟨q, hq⟩ ↦ hq ▸ map_connecting hE q⟩
  induction x using ind with | h P => ?_
  obtain ⟨u, hu⟩ := map_mk_eq_mk_iff.1 (h.trans one_def)
  -- `π ∘ u` is `A`-invariant, hence the restriction of a global section `q` of `Q`.
  obtain ⟨q, hq⟩ : ∃ q : (Q.obj ⋙ forget GrpCat).sections,
      ∀ U p, π.hom.app U (u.hom.app U p) = q.1 U :=
    P.exists_sections_eq_of_smul_invariant (u ≫ (sheafCompose J (forget GrpCat.{w})).map π)
      fun U a p ↦ by
        refine (congrArg (π.hom.app U) (hu U a p)).trans ?_
        exact (map_mul (π.hom.app U).hom (i.hom.app U a) (u.hom.app U p)).trans
          ((congrArg (· * _) (hE.app_app_eq_one a)).trans (one_mul _))
  refine ⟨q, (connecting_def hE q).trans (mk_eq_mk_of_hom ⟨ObjectProperty.homMk
    { app U := ↾fun p ↦ (hE.liftsObjEquiv q U).symm ⟨u.hom.app U p, hq U p⟩
      naturality U V f := by
        ext p
        refine (hE.liftsObjEquiv q V).injective (Subtype.ext ?_)
        simp only [Functor.comp_obj, TypeCat.Fun.toFun_apply, comp_apply, TypeCat.hom_ofHom,
          TypeCat.Fun.coe_mk, NatTrans.naturality_apply, Equiv.apply_symm_apply,
          IsGroupExtension.liftsObjEquiv_map]
        -- The restriction maps of the trivial torsor are those of `B`.
        rfl }, fun U a p ↦ ?_⟩).symm⟩
  refine (hE.liftsObjEquiv q U).injective (Subtype.ext ?_)
  rw [hE.liftsObjEquiv_smul]
  simp only [ObjectProperty.homMk_hom, TypeCat.hom_ofHom, TypeCat.Fun.coe_mk,
    Equiv.apply_symm_apply]
  -- The action of `B` on the trivial torsor is multiplication.
  exact hu U a p

include hE in
/-- Exactness of `H¹(A) → H¹(B) → H¹(Q)` at `H¹(B)`: a `B`-torsor becomes trivial as a
`Q`-torsor if and only if it comes from an `A`-torsor. -/
theorem map_eq_one_iff_mem_range_map (y : NonabelianH1 B) :
    map π y = 1 ↔ y ∈ Set.range (map i) := by
  refine ⟨fun h ↦ ?_, fun ⟨x, hx⟩ ↦ hx ▸ (map_map i π x).trans
    (map_eq_one_of_forall_app_eq_one (fun U a ↦ hE.app_app_eq_one a) x)⟩
  induction y using ind with | h P => ?_
  obtain ⟨u, hu⟩ := map_mk_eq_mk_iff.1 (h.trans one_def)
  -- The fibre of `u` over `1` is an `A`-torsor, and its inclusion into `P` is `i`-equivariant.
  exact ⟨mk (Torsor.reduction hE u hu), map_mk_eq_mk (ObjectProperty.homMk
    (Subfunctor.ι (Torsor.fibreSubfunctor u))) fun _ _ _ ↦ rfl⟩

end NonabelianH1

end CategoryTheory.Sheaf
