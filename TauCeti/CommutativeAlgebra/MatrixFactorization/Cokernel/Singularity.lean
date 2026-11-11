/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CommutativeAlgebra.MatrixFactorization.Cokernel.FullyFaithful
public import TauCeti.Algebra.Homology.TotallyAcyclic.FGModuleCat
public import TauCeti.Algebra.Homology.TotallyAcyclic.Abelian.Singularity

import TauCeti.CategoryTheory.Preadditive.MorphismIdeal.Equivalence

/-!
# The singularity-category cokernel of a matrix factorization

For a commutative ring `S` and `w : S`, reduction modulo `w` and the cokernel of the
even-to-odd differential give a finitely generated `S/(w)`-module. Placing this module in
degree zero and passing to the singularity category kills null-homotopic maps: their
cokernel maps factor through finitely generated projectives. This defines the additive
functor `TauCeti.MatrixFactorization.HomotopyCategory.quotientSingularityCokernel`.
Only the quotient ring is required to be noetherian, so its finitely generated module
category is abelian. The construction also applies to the zero potential.

When `w` is a non-zero-divisor, this functor is fully faithful. The reduced cokernels
are Gorenstein-projective, so Chen's theorem identifies their singularity-category
morphisms with module maps modulo projectives. Lifting module maps to matrix
factorizations, and identifying projective factorizations of cokernel maps with
null-homotopies, gives full faithfulness. No regularity or finite global dimension
of `S` is needed for this embedding. No essential-surjectivity or triangle-functor
assertion is made here.

## References

* D. Eisenbud, *Homological algebra on a complete intersection, with an application to group
  representations*, Trans. Amer. Math. Soc. **260** (1980), Sections 5–6.
* Xiao-Wu Chen, *Relative singularity categories and Gorenstein-projective modules*,
  Math. Nachr. **284** (2011), 199–212.
* D. Orlov, *Triangulated categories of singularities and D-branes in Landau–Ginzburg
  models*, Proc. Steklov Inst. Math. **246** (2004), Section 3.
-/

public section

noncomputable section

universe u v

namespace TauCeti.MatrixFactorization

open CategoryTheory Limits

variable {S : Type u} [CommRing S] {w : S}
  [IsNoetherianRing (S ⧸ Ideal.span {w})]
  [HasDerivedCategory.{v} (FGModuleCat.{u} (S ⧸ Ideal.span {w}))]

/-- The cokernel of a null-homotopic map, reduced modulo the potential and placed in
degree zero, vanishes in the singularity category. No regularity of the potential is needed. -/
theorem quotientCokernel_map_eq_zero_of_mem_nullHomotopic
    {X Y : MatrixFactorization S w} {g : X ⟶ Y}
    (hg : g ∈ (nullHomotopic (S := S) (w := w)).hom X Y) :
    (SingularityCategory.Q (FGModuleCat.{u} (S ⧸ Ideal.span {w}))).map
      ((DerivedCategory.Bounded.singleFunctor _ 0).map
        (cokernelFunctor.map
          ((baseChangeFunctor (Ideal.Quotient.mk (Ideal.span {w}))).map g))) = 0 := by
  have hw : Ideal.Quotient.mk (Ideal.span {w}) w = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self w)
  have h := cokernelFunctor_map_mem_projectiveStableIdeal hw
    (baseChangeFunctor_map_mem_nullHomotopic (Ideal.Quotient.mk (Ideal.span {w})) hg)
  rw [ExactStructure.mem_projectiveStableIdeal_iff, ObjectProperty.factorsThrough_iff] at h
  obtain ⟨P, hP, i, p, hip⟩ := h
  have hP' := (ExactStructure.abelian_isProjective_iff P).1 hP
  rw [hip, Functor.map_comp, Functor.map_comp,
    (SingularityCategory.isZero_Q_obj_singleFunctor_obj hP').eq_of_src
      ((SingularityCategory.Q _).map _) 0, comp_zero]

/-- For a non-zero-divisor potential, the reduced cokernel map vanishes in the singularity
category exactly when the matrix-factorization map is null-homotopic. -/
theorem quotientCokernel_map_eq_zero_iff (hw : w ∈ nonZeroDivisors S)
    {X Y : MatrixFactorization S w} (g : X ⟶ Y) :
    (SingularityCategory.Q (FGModuleCat.{u} (S ⧸ Ideal.span {w}))).map
      ((DerivedCategory.Bounded.singleFunctor _ 0).map
        (cokernelFunctor.map
          ((baseChangeFunctor (Ideal.Quotient.mk (Ideal.span {w}))).map g))) = 0 ↔
      g ∈ (nullHomotopic (S := S) (w := w)).hom X Y := by
  refine ⟨fun hg ↦ ?_, quotientCokernel_map_eq_zero_of_mem_nullHomotopic⟩
  have hG := (FGModuleCat.isGorensteinProjective_iff _).2
    (isGorensteinProjective_cokernelFunctor_obj_baseChangeFunctor_obj hw X)
  rw [SingularityCategory.map_eq_zero_iff_of_isGorensteinProjective hG,
    ObjectProperty.factorsThrough_iff] at hg
  obtain ⟨P, hP, i, p, hip⟩ := hg
  have := FGModuleCat.moduleProjective_of_projective P
  have : Projective P.obj := ModuleCat.projective_of_categoryTheory_projective _
  exact mem_nullHomotopic_of_cokernelFunctor_map_eq_comp hw g i.hom p.hom
    (congrArg (fun f ↦ f.hom) hip)

namespace HomotopyCategory

/-- The **singularity-category cokernel functor** sends a finite-projective matrix
factorization to its reduced cokernel, placed in degree zero in `D_sg(mod-S/(w))`.
Null-homotopic maps vanish because their cokernel maps factor through finite projectives.
The potential need not be a non-zero-divisor for the construction. -/
def quotientSingularityCokernel :
    HomotopyCategory (S := S) (w := w) ⥤
      SingularityCategory (FGModuleCat.{u} (S ⧸ Ideal.span {w})) :=
  (nullHomotopic (S := S) (w := w)).lift
    (baseChangeFunctor (Ideal.Quotient.mk (Ideal.span {w})) ⋙ cokernelFunctor ⋙
      DerivedCategory.Bounded.singleFunctor _ 0 ⋙ SingularityCategory.Q _) (by
      intro X Y g hg
      rw [Functor.mem_kerIdeal_hom]
      exact quotientCokernel_map_eq_zero_of_mem_nullHomotopic hg)

instance : (quotientSingularityCokernel (S := S) (w := w)).Additive := by
  unfold quotientSingularityCokernel
  infer_instance

/-- On matrix factorizations, the singularity functor is reduction, cokernel, the
degree-zero stalk, and the Verdier quotient by perfect complexes. -/
theorem quotientFunctor_comp_quotientSingularityCokernel :
    (nullHomotopic (S := S) (w := w)).quotientFunctor ⋙ quotientSingularityCokernel =
      baseChangeFunctor (Ideal.Quotient.mk (Ideal.span {w})) ⋙ cokernelFunctor ⋙
        DerivedCategory.Bounded.singleFunctor _ 0 ⋙ SingularityCategory.Q _ := by
  unfold quotientSingularityCokernel
  exact CategoryTheory.Quotient.lift_spec _ _ _

/-- On a representative object, the singularity functor is the reduced cokernel in degree zero. -/
@[simp]
theorem quotientSingularityCokernel_obj_quotientFunctor_obj (X : MatrixFactorization S w) :
    quotientSingularityCokernel.obj
        ((nullHomotopic (S := S) (w := w)).quotientFunctor.obj X) =
      (SingularityCategory.Q _).obj ((DerivedCategory.Bounded.singleFunctor _ 0).obj
        (cokernelFunctor.obj
          ((baseChangeFunctor (Ideal.Quotient.mk (Ideal.span {w}))).obj X))) :=
  Functor.congr_obj quotientFunctor_comp_quotientSingularityCokernel X

/-- On a representative morphism, the singularity functor is the map induced on reduced
cokernels, placed in degree zero and mapped to the Verdier quotient. -/
theorem quotientSingularityCokernel_map_quotientFunctor_map
    {X Y : MatrixFactorization S w} (g : X ⟶ Y) :
    quotientSingularityCokernel.map
        ((nullHomotopic (S := S) (w := w)).quotientFunctor.map g) =
      eqToHom (quotientSingularityCokernel_obj_quotientFunctor_obj X) ≫
        (SingularityCategory.Q _).map ((DerivedCategory.Bounded.singleFunctor _ 0).map
          (cokernelFunctor.map
            ((baseChangeFunctor (Ideal.Quotient.mk (Ideal.span {w}))).map g))) ≫
        eqToHom (quotientSingularityCokernel_obj_quotientFunctor_obj Y).symm :=
  Functor.congr_hom quotientFunctor_comp_quotientSingularityCokernel g

/-- For a non-zero-divisor potential, every singularity-category morphism between reduced
cokernels is induced by a morphism in the matrix-factorization homotopy category. -/
theorem quotientSingularityCokernel_full (hw : w ∈ nonZeroDivisors S) :
    (quotientSingularityCokernel (S := S) (w := w)).Full := by
  have : (baseChangeFunctor (w := w) (Ideal.Quotient.mk (Ideal.span {w})) ⋙
      cokernelFunctor ⋙ DerivedCategory.Bounded.singleFunctor _ 0 ⋙
        SingularityCategory.Q _).Full := by
    refine ⟨fun {X Y} φ ↦ ?_⟩
    have hG := (FGModuleCat.isGorensteinProjective_iff _).2
      (isGorensteinProjective_cokernelFunctor_obj_baseChangeFunctor_obj hw X)
    obtain ⟨f, hf⟩ := SingularityCategory.map_surjective_of_isGorensteinProjective hG
      (cokernelFunctor.obj
        ((baseChangeFunctor (Ideal.Quotient.mk (Ideal.span {w}))).obj Y)) φ
    obtain ⟨g, hg⟩ := exists_cokernelFunctor_map_eq hw f
    exact ⟨g, by simpa only [Functor.comp_map] using
      (congrArg (fun f ↦ (SingularityCategory.Q _).map
        ((DerivedCategory.Bounded.singleFunctor _ 0).map f)) hg).trans hf⟩
  unfold quotientSingularityCokernel
  infer_instance

/-- For a non-zero-divisor potential, equality of singularity-category cokernel maps
detects equality in the matrix-factorization homotopy category. -/
theorem quotientSingularityCokernel_faithful (hw : w ∈ nonZeroDivisors S) :
    (quotientSingularityCokernel (S := S) (w := w)).Faithful := by
  unfold quotientSingularityCokernel
  apply (MorphismIdeal.faithful_lift_iff _ _ _).2
  intro X Y g hg
  rw [Functor.mem_kerIdeal_hom] at hg
  exact (quotientCokernel_map_eq_zero_iff hw g).1 hg

/-- The reduced-cokernel functor `HMF(S,w) ⥤ D_sg(mod-S/(w))` is fully faithful for
a non-zero-divisor `w`, with no finite-global-dimension assumption on the ambient ring. -/
def fullyFaithfulQuotientSingularityCokernel (hw : w ∈ nonZeroDivisors S) :
    (quotientSingularityCokernel (S := S) (w := w)).FullyFaithful :=
  haveI := quotientSingularityCokernel_full hw
  haveI := quotientSingularityCokernel_faithful hw
  .ofFullyFaithful _

end HomotopyCategory

end TauCeti.MatrixFactorization
