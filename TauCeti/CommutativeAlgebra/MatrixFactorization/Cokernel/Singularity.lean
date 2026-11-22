/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CommutativeAlgebra.MatrixFactorization.Cokernel.FullyFaithful
public import TauCeti.CommutativeAlgebra.MatrixFactorization.Cokernel.Triangulated
public import TauCeti.Algebra.Homology.GorensteinProjective.FGModuleCat
public import TauCeti.Algebra.Homology.TotallyAcyclic.FGModuleCat
public import TauCeti.Algebra.Homology.TotallyAcyclic.Abelian.Singularity

import TauCeti.CategoryTheory.Preadditive.MorphismIdeal.Equivalence

/-!
# The singularity-category cokernel of a matrix factorization

For a ring homomorphism `f : S →+* T` killing a potential `w : S`, base change and the
cokernel of the even-to-odd differential give a finitely generated `T`-module. Placing
this module in degree zero and passing to the singularity category kills null-homotopic
maps: their cokernel maps factor through finitely generated projectives. This defines
the additive functor `TauCeti.MatrixFactorization.HomotopyCategory.singularityCokernel`.
Only `T` is required to be noetherian, so its finitely generated module category is abelian.
The specialization to reduction modulo `w` is
`TauCeti.MatrixFactorization.HomotopyCategory.quotientSingularityCokernel`; it requires
only the quotient ring to be noetherian and also applies to the zero potential.

When `w` is a non-zero-divisor, the quotient-ring specialization is a fully faithful triangle
functor. The reduced cokernels are Gorenstein-projective, so `quotientSingularityCokernel`
factors literally as the Gorenstein-projective stable cokernel functor
`quotientGorensteinProjectiveStableCokernel` followed by Chen's functor
`GorensteinProjectiveModuleCat.toSingularityCategory`
(`quotientGorensteinProjectiveStableCokernel_comp_toSingularityCategory`). Both factors are
fully faithful triangle functors—the first for the parity-shift triangulation of `HMF(S,w)`
and Happel's triangulation of the stable category, and the second into the Verdier-quotient
triangulation of `D_sg(mod-S/(w))`—so `quotientSingularityCokernel` inherits shift
compatibility (`quotientSingularityCokernelCommShift`) and preserves distinguished triangles
(`quotientSingularityCokernel_isTriangulated`) with no regularity or finite global dimension
hypothesis on `S`. Essential surjectivity under global-dimension and regularity hypotheses is
proved in `TauCeti.CommutativeAlgebra.MatrixFactorization.Cokernel.Orlov`.

## References

* D. Eisenbud, *Homological algebra on a complete intersection, with an application to group
  representations*, Trans. Amer. Math. Soc. **260** (1980), Sections 5–6.
* R.-O. Buchweitz, *Maximal Cohen–Macaulay Modules and Tate Cohomology*, Mathematical Surveys
  and Monographs **262**, American Mathematical Society (2021), Section 4.
* Xiao-Wu Chen, *Relative singularity categories and Gorenstein-projective modules*,
  Math. Nachr. **284** (2011), 199–212.
* D. Orlov, *Triangulated categories of singularities and D-branes in Landau–Ginzburg
  models*, Proc. Steklov Inst. Math. **246** (2004), Section 3.
-/

public section

noncomputable section

universe v u

namespace TauCeti.MatrixFactorization

open CategoryTheory Limits

variable {S T : Type u} [CommRing S] [CommRing T] {w : S}

/-- For a zero potential, the cokernel of a null-homotopic map, placed in degree zero,
vanishes in the singularity category. -/
theorem singularityCategoryQ_map_singleFunctor_map_cokernelFunctor_map_eq_zero_of_mem_nullHomotopic
    [IsNoetherianRing S] [HasDerivedCategory.{v} (FGModuleCat.{u} S)] (hw : w = 0)
    {X Y : MatrixFactorization S w} {g : X ⟶ Y}
    (hg : g ∈ (nullHomotopic (S := S) (w := w)).hom X Y) :
    (SingularityCategory.Q (FGModuleCat.{u} S)).map
      ((DerivedCategory.Bounded.singleFunctor _ 0).map (cokernelFunctor.map g)) = 0 := by
  have h := cokernelFunctor_map_mem_projectiveStableIdeal hw hg
  rw [ExactStructure.mem_projectiveStableIdeal_iff, ObjectProperty.factorsThrough_iff] at h
  obtain ⟨P, hP, i, p, hip⟩ := h
  have hP' := (ExactStructure.abelian_isProjective_iff P).1 hP
  rw [hip, Functor.map_comp, Functor.map_comp,
    (SingularityCategory.isZero_Q_obj_singleFunctor_obj hP').eq_of_src
      ((SingularityCategory.Q _).map _) 0, comp_zero]

namespace HomotopyCategory

/-- The **singularity-category cokernel functor** along a ring map killing the potential
sends a finite-projective matrix factorization to its base-changed cokernel in degree zero.
Null-homotopic maps vanish because their cokernel maps factor through finite projectives. -/
def singularityCokernel (f : S →+* T) (hw : f w = 0) [IsNoetherianRing T]
    [HasDerivedCategory.{v} (FGModuleCat.{u} T)] :
    HomotopyCategory (S := S) (w := w) ⥤ SingularityCategory (FGModuleCat.{u} T) :=
  (nullHomotopic (S := S) (w := w)).lift
    (baseChangeFunctor f ⋙ cokernelFunctor ⋙
      DerivedCategory.Bounded.singleFunctor _ 0 ⋙ SingularityCategory.Q _) (by
      intro X Y g hg
      rw [Functor.mem_kerIdeal_hom]
      exact
        singularityCategoryQ_map_singleFunctor_map_cokernelFunctor_map_eq_zero_of_mem_nullHomotopic
          hw (baseChangeFunctor_map_mem_nullHomotopic f hg))

instance (f : S →+* T) (hw : f w = 0) [IsNoetherianRing T]
    [HasDerivedCategory.{v} (FGModuleCat.{u} T)] : (singularityCokernel f hw).Additive := by
  unfold singularityCokernel
  infer_instance

/-- On matrix factorizations, the singularity functor is base change, cokernel, the
degree-zero stalk, and the Verdier quotient by perfect complexes. -/
theorem quotientFunctor_comp_singularityCokernel (f : S →+* T) (hw : f w = 0)
    [IsNoetherianRing T] [HasDerivedCategory.{v} (FGModuleCat.{u} T)] :
    (nullHomotopic (S := S) (w := w)).quotientFunctor ⋙ singularityCokernel f hw =
      baseChangeFunctor f ⋙ cokernelFunctor ⋙
        DerivedCategory.Bounded.singleFunctor _ 0 ⋙ SingularityCategory.Q _ := by
  unfold singularityCokernel
  exact CategoryTheory.Quotient.lift_spec _ _ _

/-- On a representative object, the singularity functor is the base-changed cokernel in
degree zero. -/
@[simp]
theorem singularityCokernel_obj_quotientFunctor_obj (f : S →+* T) (hw : f w = 0)
    [IsNoetherianRing T] [HasDerivedCategory.{v} (FGModuleCat.{u} T)]
    (X : MatrixFactorization S w) :
    (singularityCokernel f hw).obj
        ((nullHomotopic (S := S) (w := w)).quotientFunctor.obj X) =
      (SingularityCategory.Q _).obj ((DerivedCategory.Bounded.singleFunctor _ 0).obj
        (cokernelFunctor.obj ((baseChangeFunctor f).obj X))) :=
  Functor.congr_obj (quotientFunctor_comp_singularityCokernel f hw) X

/-- On a representative morphism, the singularity functor is the map induced on base-changed
cokernels, placed in degree zero and mapped to the Verdier quotient. -/
@[simp]
theorem singularityCokernel_map_quotientFunctor_map (f : S →+* T) (hw : f w = 0)
    [IsNoetherianRing T] [HasDerivedCategory.{v} (FGModuleCat.{u} T)]
    {X Y : MatrixFactorization S w} (g : X ⟶ Y) :
    (singularityCokernel f hw).map
        ((nullHomotopic (S := S) (w := w)).quotientFunctor.map g) =
      eqToHom (singularityCokernel_obj_quotientFunctor_obj f hw X) ≫
        (SingularityCategory.Q _).map ((DerivedCategory.Bounded.singleFunctor _ 0).map
          (cokernelFunctor.map ((baseChangeFunctor f).map g))) ≫
        eqToHom (singularityCokernel_obj_quotientFunctor_obj f hw Y).symm :=
  Functor.congr_hom (quotientFunctor_comp_singularityCokernel f hw) g

end HomotopyCategory

/-- Forgetting Gorenstein-projectivity into `FGModuleCat` after
`quotientGorensteinProjectiveCokernel` recovers reduction modulo `w` followed by
`cokernelFunctor`. -/
theorem quotientGorensteinProjectiveCokernel_comp_ιOfLE
    (hw : w ∈ nonZeroDivisors S) :
    quotientGorensteinProjectiveCokernel hw ⋙
        ObjectProperty.ιOfLE (fun X hX ↦ (ModuleCat.isFG_iff X).2 hX.finite) =
      baseChangeFunctor (Ideal.Quotient.mk (Ideal.span {w})) ⋙ cokernelFunctor := by
  refine CategoryTheory.Functor.ext (fun X ↦ ObjectProperty.FullSubcategory.ext
    (quotientGorensteinProjectiveCokernel_obj_obj hw X)) fun X Y g ↦ ?_
  apply (forget₂ (FGModuleCat.{u} (S ⧸ Ideal.span {w}))
    (ModuleCat.{u} (S ⧸ Ideal.span {w}))).map_injective
  rw [Functor.comp_map, Functor.comp_map, Functor.map_comp, Functor.map_comp,
    eqToHom_map, eqToHom_map]
  exact Functor.congr_hom (quotientGorensteinProjectiveCokernel_comp_ι hw) g

variable [IsNoetherianRing (S ⧸ Ideal.span {w})]
  [HasDerivedCategory.{v} (FGModuleCat.{u} (S ⧸ Ideal.span {w}))]

/-- For a non-zero-divisor potential, the reduced cokernel map vanishes in the singularity
category exactly when the matrix-factorization map is null-homotopic. -/
theorem singularityCategoryQ_map_singleFunctor_map_quotientCokernel_eq_zero_iff
    (hw : w ∈ nonZeroDivisors S)
    {X Y : MatrixFactorization S w} (g : X ⟶ Y) :
    (SingularityCategory.Q (FGModuleCat.{u} (S ⧸ Ideal.span {w}))).map
      ((DerivedCategory.Bounded.singleFunctor _ 0).map
        (cokernelFunctor.map
          ((baseChangeFunctor (Ideal.Quotient.mk (Ideal.span {w}))).map g))) = 0 ↔
      g ∈ (nullHomotopic (S := S) (w := w)).hom X Y := by
  refine ⟨fun hg ↦ ?_, fun hg ↦
    singularityCategoryQ_map_singleFunctor_map_cokernelFunctor_map_eq_zero_of_mem_nullHomotopic
      (Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self w))
      (baseChangeFunctor_map_mem_nullHomotopic (Ideal.Quotient.mk (Ideal.span {w})) hg)⟩
  have hG := (FGModuleCat.isGorensteinProjective_iff _).2
    (isGorensteinProjective_cokernelFunctor_obj_baseChangeFunctor_obj hw X)
  rw [SingularityCategory.map_eq_zero_iff_of_isGorensteinProjective hG,
    ObjectProperty.factorsThrough_iff] at hg
  obtain ⟨P, hP, i, p, hip⟩ := hg
  have := FGModuleCat.moduleProjective_of_projective P
  have : Projective P.obj := ModuleCat.projective_of_categoryTheory_projective _
  exact mem_nullHomotopic_of_cokernelFunctor_map_baseChangeFunctor_map_eq_comp hw g i.hom p.hom
    (congrArg (fun f ↦ f.hom) hip)

/-- For a non-zero-divisor potential, every singularity-category morphism between reduced
cokernels placed in degree zero is induced by a matrix-factorization morphism. -/
theorem exists_singularityCategoryQ_map_singleFunctor_map_quotientCokernel_eq
    (hw : w ∈ nonZeroDivisors S) {X Y : MatrixFactorization S w}
    (φ : (SingularityCategory.Q (FGModuleCat.{u} (S ⧸ Ideal.span {w}))).obj
        ((DerivedCategory.Bounded.singleFunctor _ 0).obj
          (cokernelFunctor.obj
            ((baseChangeFunctor (Ideal.Quotient.mk (Ideal.span {w}))).obj X))) ⟶
      (SingularityCategory.Q (FGModuleCat.{u} (S ⧸ Ideal.span {w}))).obj
        ((DerivedCategory.Bounded.singleFunctor _ 0).obj
          (cokernelFunctor.obj
            ((baseChangeFunctor (Ideal.Quotient.mk (Ideal.span {w}))).obj Y)))) :
    ∃ g : X ⟶ Y,
      (SingularityCategory.Q (FGModuleCat.{u} (S ⧸ Ideal.span {w}))).map
        ((DerivedCategory.Bounded.singleFunctor _ 0).map
          (cokernelFunctor.map
            ((baseChangeFunctor (Ideal.Quotient.mk (Ideal.span {w}))).map g))) = φ := by
  have hG := (FGModuleCat.isGorensteinProjective_iff _).2
    (isGorensteinProjective_cokernelFunctor_obj_baseChangeFunctor_obj hw X)
  obtain ⟨f, hf⟩ := SingularityCategory.map_surjective_of_isGorensteinProjective hG
    (cokernelFunctor.obj
      ((baseChangeFunctor (Ideal.Quotient.mk (Ideal.span {w}))).obj Y)) φ
  obtain ⟨g, hg⟩ := exists_cokernelFunctor_map_baseChangeFunctor_map_eq hw f
  exact ⟨g, (congrArg (fun f ↦ (SingularityCategory.Q _).map
    ((DerivedCategory.Bounded.singleFunctor _ 0).map f)) hg).trans hf⟩

namespace HomotopyCategory

/-- The **singularity-category cokernel functor** sends a finite-projective matrix
factorization to its reduced cokernel, placed in degree zero in `D_sg(mod-S/(w))`.
Null-homotopic maps vanish because their cokernel maps factor through finite projectives.
The potential need not be a non-zero-divisor for the construction. -/
def quotientSingularityCokernel :
    HomotopyCategory (S := S) (w := w) ⥤
      SingularityCategory (FGModuleCat.{u} (S ⧸ Ideal.span {w})) :=
  singularityCokernel (Ideal.Quotient.mk (Ideal.span {w}))
    (Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self w))

/-- The reduced-cokernel functor is the singularity-category cokernel functor along the
canonical quotient map killing the potential. -/
theorem quotientSingularityCokernel_def :
    quotientSingularityCokernel (S := S) (w := w) =
      singularityCokernel (Ideal.Quotient.mk (Ideal.span {w}))
        (Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self w)) := (rfl)

instance : (quotientSingularityCokernel (S := S) (w := w)).Additive := by
  unfold quotientSingularityCokernel
  infer_instance

/-- On matrix factorizations, the singularity functor is reduction, cokernel, the
degree-zero stalk, and the Verdier quotient by perfect complexes. -/
theorem quotientFunctor_comp_quotientSingularityCokernel :
    (nullHomotopic (S := S) (w := w)).quotientFunctor ⋙ quotientSingularityCokernel =
      baseChangeFunctor (Ideal.Quotient.mk (Ideal.span {w})) ⋙ cokernelFunctor ⋙
        DerivedCategory.Bounded.singleFunctor _ 0 ⋙ SingularityCategory.Q _ :=
  quotientFunctor_comp_singularityCokernel _ _

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
@[simp]
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
    exact exists_singularityCategoryQ_map_singleFunctor_map_quotientCokernel_eq hw φ
  unfold quotientSingularityCokernel singularityCokernel
  infer_instance

/-- For a non-zero-divisor potential, equality of singularity-category cokernel maps
detects equality in the matrix-factorization homotopy category. -/
theorem quotientSingularityCokernel_faithful (hw : w ∈ nonZeroDivisors S) :
    (quotientSingularityCokernel (S := S) (w := w)).Faithful := by
  unfold quotientSingularityCokernel singularityCokernel
  apply (MorphismIdeal.faithful_lift_iff _ _ _).2
  intro X Y g hg
  rw [Functor.mem_kerIdeal_hom] at hg
  exact (singularityCategoryQ_map_singleFunctor_map_quotientCokernel_eq_zero_iff hw g).1 hg

/-- The reduced-cokernel functor `HMF(S,w) ⥤ D_sg(mod-S/(w))` is fully faithful for
a non-zero-divisor `w`, with no finite-global-dimension assumption on the ambient ring. -/
def fullyFaithfulQuotientSingularityCokernel (hw : w ∈ nonZeroDivisors S) :
    (quotientSingularityCokernel (S := S) (w := w)).FullyFaithful :=
  haveI := quotientSingularityCokernel_full hw
  haveI := quotientSingularityCokernel_faithful hw
  .ofFullyFaithful _

/-- **Factorization of the singularity-category cokernel functor.** For a non-zero-divisor `w`,
`quotientSingularityCokernel` is the composite of the Gorenstein-projective stable cokernel
functor `HMF(S,w) ⥤ stable(Gproj-S/(w))` with Chen's functor
`stable(Gproj-S/(w)) ⥤ D_sg(mod-S/(w))`. -/
theorem quotientGorensteinProjectiveStableCokernel_comp_toSingularityCategory
    (hw : w ∈ nonZeroDivisors S) :
    quotientGorensteinProjectiveStableCokernel hw ⋙
        GorensteinProjectiveModuleCat.toSingularityCategory.{v, u} (S ⧸ Ideal.span {w}) =
      quotientSingularityCokernel (S := S) (w := w) := by
  apply Quotient.lift_unique' (nullHomotopic (S := S) (w := w)).rel
  -- `MorphismIdeal.quotientFunctor` is `Quotient.functor` for the underlying relation.
  change ((nullHomotopic (S := S) (w := w)).quotientFunctor ⋙
      quotientGorensteinProjectiveStableCokernel hw) ⋙
      GorensteinProjectiveModuleCat.toSingularityCategory.{v, u} (S ⧸ Ideal.span {w}) =
    (nullHomotopic (S := S) (w := w)).quotientFunctor ⋙
      quotientSingularityCokernel (S := S) (w := w)
  rw [quotientFunctor_comp_quotientGorensteinProjectiveStableCokernel, Functor.assoc,
    GorensteinProjectiveModuleCat.projectiveStableFunctor_comp_toSingularityCategory,
    ← Functor.assoc, quotientGorensteinProjectiveCokernel_comp_ιOfLE hw, Functor.assoc,
    quotientFunctor_comp_quotientSingularityCokernel]

/-- Natural isomorphism exhibiting `quotientSingularityCokernel` as the composite of
`quotientGorensteinProjectiveStableCokernel` and Chen's functor
`GorensteinProjectiveModuleCat.toSingularityCategory`. -/
def quotientGorensteinProjectiveStableCokernelCompToSingularityCategoryIso
    (hw : w ∈ nonZeroDivisors S) :
    quotientGorensteinProjectiveStableCokernel hw ⋙
        GorensteinProjectiveModuleCat.toSingularityCategory.{v, u} (S ⧸ Ideal.span {w}) ≅
      quotientSingularityCokernel (S := S) (w := w) :=
  eqToIso (quotientGorensteinProjectiveStableCokernel_comp_toSingularityCategory hw)

/-- Compatibility of `quotientSingularityCokernel` with the integral shifts: the parity shift on
`HMF(S,w)` and the Verdier-quotient shift on `D_sg(mod-S/(w))`, transported along its
factorization through the stable category of Gorenstein-projective `S/(w)`-modules. -/
@[instance_reducible]
def quotientSingularityCokernelCommShift (hw : w ∈ nonZeroDivisors S) :
    (quotientSingularityCokernel (S := S) (w := w)).CommShift ℤ :=
  letI := (GorensteinProjectiveModuleCat.exactStructure_isFrobenius.{u, u}
    (A := S ⧸ Ideal.span {w})).stableHasShift
  letI := quotientGorensteinProjectiveStableCokernelCommShift hw
  letI := GorensteinProjectiveModuleCat.toSingularityCategoryCommShift.{v, u}
    (S ⧸ Ideal.span {w})
  Functor.CommShift.ofIso
    (quotientGorensteinProjectiveStableCokernelCompToSingularityCategoryIso hw) ℤ

/-- The factorization isomorphism
`quotientGorensteinProjectiveStableCokernelCompToSingularityCategoryIso` commutes with all
integral shifts. -/
theorem quotientGorensteinProjectiveStableCokernelCompToSingularityCategoryIso_commShift
    (hw : w ∈ nonZeroDivisors S) :
    letI := (GorensteinProjectiveModuleCat.exactStructure_isFrobenius.{u, u}
      (A := S ⧸ Ideal.span {w})).stableHasShift
    letI := quotientGorensteinProjectiveStableCokernelCommShift hw
    letI := GorensteinProjectiveModuleCat.toSingularityCategoryCommShift.{v, u}
      (S ⧸ Ideal.span {w})
    letI := quotientSingularityCokernelCommShift.{v, u} hw
    NatTrans.CommShift
      (quotientGorensteinProjectiveStableCokernelCompToSingularityCategoryIso.{v, u}
        hw).hom ℤ := by
  let := (GorensteinProjectiveModuleCat.exactStructure_isFrobenius.{u, u}
    (A := S ⧸ Ideal.span {w})).stableHasShift
  let := quotientGorensteinProjectiveStableCokernelCommShift hw
  let := GorensteinProjectiveModuleCat.toSingularityCategoryCommShift.{v, u}
    (S ⧸ Ideal.span {w})
  exact Functor.CommShift.ofIso_compatibility
    (quotientGorensteinProjectiveStableCokernelCompToSingularityCategoryIso.{v, u} hw) ℤ

/-- **The singularity-category cokernel functor of matrix factorizations is a triangle functor.**
For a non-zero-divisor `w` of a commutative ring `S` with `S/(w)` Noetherian, the functor
`HMF(S,w) ⥤ D_sg(mod-S/(w))` sending a finite-projective matrix factorization to its reduced
cokernel placed in degree zero preserves distinguished triangles. -/
theorem quotientSingularityCokernel_isTriangulated (hw : w ∈ nonZeroDivisors S) :
    letI := quotientSingularityCokernelCommShift.{v, u} hw
    (quotientSingularityCokernel (S := S) (w := w)).IsTriangulated := by
  have hE' := GorensteinProjectiveModuleCat.exactStructure_isFrobenius.{u, u}
    (A := S ⧸ Ideal.span {w})
  let := hE'.stableHasShift
  let := hE'.stableShiftFunctor_additive
  let := hE'.stablePretriangulated
  let := quotientGorensteinProjectiveStableCokernelCommShift hw
  let := GorensteinProjectiveModuleCat.toSingularityCategoryCommShift.{v, u}
    (S ⧸ Ideal.span {w})
  let := quotientSingularityCokernelCommShift.{v, u} hw
  have := quotientGorensteinProjectiveStableCokernel_isTriangulated hw
  have := GorensteinProjectiveModuleCat.toSingularityCategory_isTriangulated.{v, u}
    (S ⧸ Ideal.span {w})
  have := quotientGorensteinProjectiveStableCokernelCompToSingularityCategoryIso_commShift.{v, u}
    hw
  exact Functor.isTriangulated_of_iso
    (quotientGorensteinProjectiveStableCokernelCompToSingularityCategoryIso.{v, u} hw)

end HomotopyCategory

end TauCeti.MatrixFactorization
