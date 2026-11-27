/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicTopology.SimplicialSet.CoherentIso
public import Mathlib.AlgebraicTopology.SimplicialSet.NerveCodiscrete
public import TauCeti.AlgebraicTopology.SimplicialSet.AnodyneExtensions.Cylinder

/-!
# The standard edge in the coherent isomorphism

The inclusion of the forward edge into Mathlib's coherent isomorphism is a left anodyne
extension. Compatible contractions to the initial vertex give the lifting property by
`SSet.exists_lift_cylinder_ι₀_of_mono`. This supplies extensions of edges into Kan
complexes without using a model structure on simplicial sets.

## References

* R. Haugseng, [*Introduction to ∞-Categories*]
  (https://www.sas.rochester.edu/mth/sites/doug-ravenel/otherpapers/Haugseng-intro.pdf),
  Lemma 5.5.2, for the left anodyneness of the standard-edge inclusion.
-/

public section

universe u

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory HomotopicalAlgebra
  Simplicial
open SSet.modelCategoryQuillen

namespace SSet.coherentIso

/-- The inclusion of the forward edge into the coherent isomorphism. -/
def edgeInclusion : Δ[1] ⟶ coherentIso.{u} := yonedaEquiv.symm hom.edge

@[simp]
lemma yonedaEquiv_edgeInclusion : yonedaEquiv edgeInclusion = hom.edge :=
  yonedaEquiv.apply_symm_apply _

/-- The vertices of the standard edge are the two objects of the walking isomorphism. -/
@[simp]
lemma edgeInclusion_app_obj {n : ℕ} (s : (Δ[1] : SSet.{u}) _⦋n⦌) (k : Fin (n + 1)) :
    ((edgeInclusion.app _ s).obj k).as = ULift.up (decide (s k = 1)) := by
  -- The nerve operator reindexes the two-object string defining the forward edge.
  change (hom.edge.obj ((stdSimplex.objEquiv s).toOrderHom k)).as = _
  generalize hs : s k = a at *
  fin_cases a <;> rfl

instance : Mono edgeInclusion.{u} := by
  rw [NatTrans.mono_iff_mono_app]
  rintro ⟨⟨n⟩⟩
  rw [mono_iff_injective]
  intro s t h
  apply stdSimplex.ext
  intro k
  have hk := congrArg (fun z ↦ (z.obj k).as) h
  rw [edgeInclusion_app_obj, edgeInclusion_app_obj] at hk
  generalize hs : s k = a at hk ⊢
  generalize ht : t k = b at hk ⊢
  fin_cases a <;> fin_cases b <;> simp_all

/-- Contraction of the coherent isomorphism to its initial vertex. -/
def contraction : Homotopy (const x₀) (𝟙 coherentIso.{u}) where
  h :=
    { app n := ↾fun p ↦ Codiscrete.equivFun.symm fun k ↦
        if stdSimplex.asOrderHom p.2 k = 0 then ULift.up false else (p.1.obj k).as
      naturality n m f := by
        apply ConcreteCategory.hom_ext
        intro p
        apply Codiscrete.equivFun.injective
        rfl }
  h₀ := by
    apply NatTrans.ext
    funext ⟨⟨n⟩⟩
    apply ConcreteCategory.hom_ext
    intro p
    apply Codiscrete.equivFun.injective
    rfl
  h₁ := by
    apply NatTrans.ext
    funext ⟨⟨n⟩⟩
    apply ConcreteCategory.hom_ext
    intro p
    apply Codiscrete.equivFun.injective
    rfl
  rel := by ext _ ⟨⟨_, ⟨⟩⟩, _⟩

/-- On vertex lists the contraction replaces a vertex by the initial object when the
interval coordinate is zero. -/
@[simp]
lemma contraction_h_app_obj {n : ℕ}
    (p : coherentIso.{u} _⦋n⦌ × (Δ[1] : SSet.{u}) _⦋n⦌) (k : Fin (n + 1)) :
    dsimp% ((contraction.h.app _ p).obj k).as =
      if stdSimplex.asOrderHom p.2 k = 0 then ULift.up false else (p.1.obj k).as :=
  (rfl)

/-- The contractions of the standard edge and coherent isomorphism agree on the edge. -/
@[reassoc]
lemma edgeInclusion_contraction :
    edgeInclusion.{u} ▷ Δ[1] ≫ contraction.h =
      (stdSimplex.contraction 1).h ≫ edgeInclusion := by
  apply NatTrans.ext
  funext ⟨⟨n⟩⟩
  apply ConcreteCategory.hom_ext
  rintro ⟨s, t⟩
  apply Codiscrete.equivFun.injective
  funext k
  -- Both contractions replace a vertex by zero when the interval coordinate is zero.
  change (if stdSimplex.asOrderHom t k = 0 then ULift.up false else
      ((edgeInclusion.app _ s).obj k).as) =
    ((edgeInclusion.app _ ((stdSimplex.contraction 1).h.app _ (s, t))).obj k).as
  rw [edgeInclusion_app_obj, edgeInclusion_app_obj]
  -- Retype the component equality before rewriting so the implicit product types agree.
  have hc : (stdSimplex.contraction 1).h.app _ (s, t) k =
      if stdSimplex.asOrderHom t k = 0 then 0 else stdSimplex.asOrderHom s k :=
    stdSimplex.contraction_h_app_apply (s, t) k
  rw [hc]
  split_ifs <;> rfl

/-- The standard edge is a left anodyne subcomplex of the coherent isomorphism. -/
theorem leftAnodyneExtensions_edgeInclusion : leftAnodyneExtensions edgeInclusion.{u} := by
  rw [leftAnodyneExtensions_eq_llp]
  intro E B p hp
  have : LeftFibration p := ⟨hp⟩
  refine ⟨fun {a b} sq ↦ ?_⟩
  have hzero : edgeInclusion.{u}.app _ (stdSimplex.obj₀Equiv.symm 0) = x₀ :=
    hom.yonedaEquiv_symm_edge_app_zero
  obtain ⟨L, _, hL, hLp⟩ := exists_lift_cylinder_ι₀_of_mono edgeInclusion p
    (contraction.h ≫ b) (const (a.app _ (stdSimplex.obj₀Equiv.symm 0)))
    ((stdSimplex.contraction 1).h ≫ a)
    (by
      simp only [const_comp, contraction.h₀_assoc]
      simpa only [NatTrans.comp_app, types_comp_apply, hzero] using
        congrArg (fun f : Δ[1] ⟶ B ↦ const (f.app _ (stdSimplex.obj₀Equiv.symm 0))) sq.w)
    (by simp [sq.w, edgeInclusion_contraction_assoc])
    (by simp)
  refine ⟨⟨{ l := ι₁ ≫ L
             fac_left := ?_
             fac_right := ?_ }⟩⟩
  · rw [← ι₁_comp_assoc, hL, (stdSimplex.contraction 1).h₁_assoc, Category.id_comp]
  · rw [Category.assoc, hLp, contraction.h₁_assoc, Category.id_comp]

/-- The standard edge is an anodyne subcomplex of the coherent isomorphism. -/
theorem anodyneExtensions_edgeInclusion : anodyneExtensions edgeInclusion.{u} :=
  leftAnodyneExtensions_le_anodyneExtensions _ leftAnodyneExtensions_edgeInclusion

end SSet.coherentIso
