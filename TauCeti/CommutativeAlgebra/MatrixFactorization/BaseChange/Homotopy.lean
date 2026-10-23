/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CommutativeAlgebra.MatrixFactorization.BaseChange.Basic

/-!
# Base change of matrix factorizations on homotopy categories

Let `f : S →+* T` carry a potential `w` to zero. Extension of scalars then sends a matrix
factorization of `w` to a square-zero curved duplex over `T`. This functor preserves
null-homotopic maps, so it descends from the matrix-factorization homotopy category first to the
homotopy category of curved duplexes and then, through the canonical equivalence, to Mathlib's
homotopy category of two-periodic complexes.

Without any condition on the image potential, extension of scalars also carries null-homotopic
maps of factorizations of `w` to null-homotopic maps of factorizations of `f w`
(`TauCeti.MatrixFactorization.baseChangeFunctor_map_mem_nullHomotopic`).

The resulting comparison square with the two quotient functors commutes strictly. Thus the
object and morphism formulas established for `MatrixFactorization.toPeriodicComplex` also
describe the descended functor on representatives.

## Main definitions

* `TauCeti.MatrixFactorization.HomotopyCategory.baseChangeToCurvedDuplex`: base change into the
  homotopy category of square-zero curved duplexes.
* `TauCeti.MatrixFactorization.HomotopyCategory.baseChangeToPeriodicComplex`: base change into
  the homotopy category of two-periodic complexes.
* `TauCeti.MatrixFactorization.HomotopyCategory.quotientPeriodicComplex`: the specialization to
  the hypersurface quotient `S/(w)`.

## References

* D. Eisenbud, *Homological algebra on a complete intersection, with an application to group
  representations*, Trans. Amer. Math. Soc. **260** (1980), Section 5.
-/

public section

universe u

namespace TauCeti.MatrixFactorization

open CategoryTheory

variable {S T : Type u} [CommRing S] [CommRing T] {w : S}

/-- Base change along a ring map killing the potential carries a null-homotopic
matrix-factorization map to a null-homotopic map of square-zero curved duplexes. -/
theorem baseChangeToCurvedDuplex_map_mem_nullHomotopic (f : S →+* T) (hw : f w = 0)
    {X Y : MatrixFactorization S w} {g : X ⟶ Y}
    (hg : g ∈ (nullHomotopic (S := S) (w := w)).hom X Y) :
    (baseChangeToCurvedDuplex f hw).map g ∈
      (CurvedDuplex.nullHomotopic (ModuleCat.{u} T) (0 : T)).hom _ _ := by
  obtain ⟨h₀, h₁, hh⟩ := (mem_nullHomotopic_iff g).1 hg
  rw [CurvedDuplex.mem_nullHomotopic_iff]
  let F := forget₂ (FGModuleCat.{u} S) (ModuleCat.{u} S) ⋙ ModuleCat.extendScalars f
  let h₀' : ((baseChangeToCurvedDuplex f hw).obj X).X₀ ⟶
      ((baseChangeToCurvedDuplex f hw).obj Y).X₁ := F.map h₀
  let h₁' : ((baseChangeToCurvedDuplex f hw).obj X).X₁ ⟶
      ((baseChangeToCurvedDuplex f hw).obj Y).X₀ := F.map h₁
  refine ⟨h₀', h₁', ?_⟩
  apply CurvedDuplex.hom_ext
  · rw [CurvedDuplex.nullHomotopicMap_f₀, baseChangeToCurvedDuplex_map_f₀,
      baseChangeToCurvedDuplex_obj_d₀, baseChangeToCurvedDuplex_obj_d₁]
    -- The component lemmas rewrite the maps but cannot transport their dependent `Hom`
    -- endpoints; definitional reduction to `F.map` avoids introducing `Eq.rec` casts.
    change F.map X.obj.d₀ ≫ F.map h₁ + F.map h₀ ≫ F.map Y.obj.d₁ = F.map g.hom.f₀
    have hEq₀ := congrArg F.map (congrArg CurvedDuplex.Hom.f₀ hh)
    simpa only [CurvedDuplex.nullHomotopicMap_f₀, Functor.map_add, Functor.map_comp] using hEq₀
  · rw [CurvedDuplex.nullHomotopicMap_f₁, baseChangeToCurvedDuplex_map_f₁,
      baseChangeToCurvedDuplex_obj_d₀, baseChangeToCurvedDuplex_obj_d₁]
    -- As above, unfolding the component types definitionally is the cast-free way to expose
    -- the scalar-extension functor on the odd component.
    change F.map X.obj.d₁ ≫ F.map h₀ + F.map h₁ ≫ F.map Y.obj.d₀ = F.map g.hom.f₁
    have hEq₁ := congrArg F.map (congrArg CurvedDuplex.Hom.f₁ hh)
    simpa only [CurvedDuplex.nullHomotopicMap_f₁, Functor.map_add, Functor.map_comp] using hEq₁

/-- Base change along a ring map killing the potential carries the matrix-factorization
null-homotopy ideal into the null-homotopy ideal of square-zero curved duplexes. -/
theorem nullHomotopic_le_comap_baseChangeToCurvedDuplex (f : S →+* T) (hw : f w = 0) :
    nullHomotopic (S := S) (w := w) ≤
      (CurvedDuplex.nullHomotopic (ModuleCat.{u} T) (0 : T)).comap
        (baseChangeToCurvedDuplex f hw) := by
  intro X Y g hg
  rw [MorphismIdeal.mem_comap_hom]
  exact baseChangeToCurvedDuplex_map_mem_nullHomotopic f hw hg

/-- Extension of scalars carries a null-homotopic map of finite-projective matrix factorizations
of `w` to a null-homotopic map of factorizations of `f w`: it applies to the odd homotopy
componentwise. No condition on the image potential is needed. -/
theorem baseChangeFunctor_map_mem_nullHomotopic (f : S →+* T)
    {X Y : MatrixFactorization S w} {g : X ⟶ Y}
    (hg : g ∈ (nullHomotopic (S := S) (w := w)).hom X Y) :
    (baseChangeFunctor f).map g ∈ (nullHomotopic (S := T) (w := f w)).hom _ _ := by
  obtain ⟨h₀, h₁, hh⟩ := (mem_nullHomotopic_iff g).1 hg
  let F := forget₂ (FGModuleCat.{u} T) (ModuleCat.{u} T)
  let G := forget₂ (FGModuleCat.{u} S) (ModuleCat.{u} S) ⋙ ModuleCat.extendScalars f
  rw [mem_nullHomotopic_iff]
  refine ⟨ObjectProperty.homMk (G.map h₀), ObjectProperty.homMk (G.map h₁), ?_⟩
  apply CurvedDuplex.hom_ext
  · apply F.map_injective
    have hEq₀ := congrArg G.map (congrArg CurvedDuplex.Hom.f₀ hh)
    simp only [CurvedDuplex.nullHomotopicMap_f₀, Functor.map_add, Functor.map_comp] at hEq₀ ⊢
    exact hEq₀
  · apply F.map_injective
    have hEq₁ := congrArg G.map (congrArg CurvedDuplex.Hom.f₁ hh)
    simp only [CurvedDuplex.nullHomotopicMap_f₁, Functor.map_add, Functor.map_comp] at hEq₁ ⊢
    exact hEq₁

/-- Extension of scalars carries the null-homotopy ideal of factorizations of `w` into that of
factorizations of `f w`. -/
theorem nullHomotopic_le_comap_baseChangeFunctor (f : S →+* T) :
    nullHomotopic (S := S) (w := w) ≤
      (nullHomotopic (S := T) (w := f w)).comap (baseChangeFunctor f) := by
  intro X Y g hg
  rw [MorphismIdeal.mem_comap_hom]
  exact baseChangeFunctor_map_mem_nullHomotopic f hg

namespace HomotopyCategory

/-- Base change from the matrix-factorization homotopy category to the homotopy category of
square-zero curved duplexes. -/
noncomputable def baseChangeToCurvedDuplex (f : S →+* T) (hw : f w = 0) :
    HomotopyCategory (S := S) (w := w) ⥤
      CurvedDuplex.HomotopyCategory (ModuleCat.{u} T) (0 : T) :=
  (nullHomotopic (S := S) (w := w)).map
    (CurvedDuplex.nullHomotopic (ModuleCat.{u} T) (0 : T))
    (MatrixFactorization.baseChangeToCurvedDuplex f hw)
    (nullHomotopic_le_comap_baseChangeToCurvedDuplex f hw)

instance (f : S →+* T) (hw : f w = 0) : (baseChangeToCurvedDuplex f hw).Additive := by
  unfold baseChangeToCurvedDuplex
  infer_instance

/-- The curved-duplex base-change functor is induced by base change before passing to homotopy
categories. -/
theorem quotientFunctor_comp_baseChangeToCurvedDuplex (f : S →+* T) (hw : f w = 0) :
    (nullHomotopic (S := S) (w := w)).quotientFunctor ⋙ baseChangeToCurvedDuplex f hw =
      MatrixFactorization.baseChangeToCurvedDuplex f hw ⋙
        (CurvedDuplex.nullHomotopic (ModuleCat.{u} T) (0 : T)).quotientFunctor :=
  MorphismIdeal.quotientFunctor_comp_map ..

/-- On a representative, curved-duplex base change applies scalar extension and then passes to
the target homotopy category. -/
@[simp]
theorem baseChangeToCurvedDuplex_obj_quotientFunctor_obj (f : S →+* T) (hw : f w = 0)
    (X : MatrixFactorization S w) :
    (baseChangeToCurvedDuplex f hw).obj
        ((nullHomotopic (S := S) (w := w)).quotientFunctor.obj X) =
      (CurvedDuplex.nullHomotopic (ModuleCat.{u} T) (0 : T)).quotientFunctor.obj
        ((MatrixFactorization.baseChangeToCurvedDuplex f hw).obj X) :=
  MorphismIdeal.map_obj_quotientFunctor_obj ..

/-- On a representative, curved-duplex base change sends a morphism to the homotopy class of
its scalar extension. -/
@[simp]
theorem baseChangeToCurvedDuplex_map_quotientFunctor_map (f : S →+* T) (hw : f w = 0)
    {X Y : MatrixFactorization S w} (g : X ⟶ Y) :
    (baseChangeToCurvedDuplex f hw).map
        ((nullHomotopic (S := S) (w := w)).quotientFunctor.map g) ≫
          eqToHom (baseChangeToCurvedDuplex_obj_quotientFunctor_obj f hw Y) =
      eqToHom (baseChangeToCurvedDuplex_obj_quotientFunctor_obj f hw X) ≫
        (CurvedDuplex.nullHomotopic (ModuleCat.{u} T) (0 : T)).quotientFunctor.map
          ((MatrixFactorization.baseChangeToCurvedDuplex f hw).map g) :=
  MorphismIdeal.map_map_quotientFunctor_map ..

/-- Base change from the matrix-factorization homotopy category to Mathlib's homotopy category
of two-periodic complexes. -/
noncomputable def baseChangeToPeriodicComplex (f : S →+* T) (hw : f w = 0) :
    HomotopyCategory (S := S) (w := w) ⥤
      _root_.HomotopyCategory (ModuleCat.{u} T) (ComplexShape.up (ZMod 2)) :=
  baseChangeToCurvedDuplex f hw ⋙
    (CurvedDuplex.HomotopyCategory.periodicComplexEquivalence (ModuleCat.{u} T) T).functor

instance (f : S →+* T) (hw : f w = 0) : (baseChangeToPeriodicComplex f hw).Additive := by
  dsimp [baseChangeToPeriodicComplex]
  infer_instance

/-- Passing a matrix factorization to the periodic homotopy category either before or after
base change gives the same functor. -/
theorem quotientFunctor_comp_baseChangeToPeriodicComplex (f : S →+* T) (hw : f w = 0) :
    (nullHomotopic (S := S) (w := w)).quotientFunctor ⋙ baseChangeToPeriodicComplex f hw =
      MatrixFactorization.toPeriodicComplex f hw ⋙
        _root_.HomotopyCategory.quotient (ModuleCat.{u} T) (ComplexShape.up (ZMod 2)) := by
  rw [baseChangeToPeriodicComplex, ← Functor.assoc,
    quotientFunctor_comp_baseChangeToCurvedDuplex]
  rw [Functor.assoc,
    CurvedDuplex.HomotopyCategory.quotientFunctor_comp_periodicComplexEquivalence_functor]
  rfl

/-- On a representative, periodic base change applies `toPeriodicComplex` and then passes to
the periodic homotopy category. -/
@[simp]
theorem baseChangeToPeriodicComplex_obj_quotientFunctor_obj (f : S →+* T) (hw : f w = 0)
    (X : MatrixFactorization S w) :
    (baseChangeToPeriodicComplex f hw).obj
        ((nullHomotopic (S := S) (w := w)).quotientFunctor.obj X) =
      (_root_.HomotopyCategory.quotient (ModuleCat.{u} T) (ComplexShape.up (ZMod 2))).obj
        ((MatrixFactorization.toPeriodicComplex f hw).obj X) :=
  Functor.congr_obj (quotientFunctor_comp_baseChangeToPeriodicComplex f hw) X

/-- On a representative, periodic base change sends a morphism to the homotopy class of its
scalar extension. -/
@[simp]
theorem baseChangeToPeriodicComplex_map_quotientFunctor_map (f : S →+* T) (hw : f w = 0)
    {X Y : MatrixFactorization S w} (g : X ⟶ Y) :
    (baseChangeToPeriodicComplex f hw).map
        ((nullHomotopic (S := S) (w := w)).quotientFunctor.map g) =
      eqToHom (baseChangeToPeriodicComplex_obj_quotientFunctor_obj f hw X) ≫
        (_root_.HomotopyCategory.quotient (ModuleCat.{u} T)
          (ComplexShape.up (ZMod 2))).map ((MatrixFactorization.toPeriodicComplex f hw).map g) ≫
        eqToHom (baseChangeToPeriodicComplex_obj_quotientFunctor_obj f hw Y).symm :=
  Functor.congr_hom (quotientFunctor_comp_baseChangeToPeriodicComplex f hw) g

/-- Base change from matrix factorizations to two-periodic complexes over the hypersurface
quotient, descended to homotopy categories. -/
noncomputable def quotientPeriodicComplex :
    HomotopyCategory (S := S) (w := w) ⥤
      _root_.HomotopyCategory (ModuleCat.{u} (S ⧸ Ideal.span {w}))
        (ComplexShape.up (ZMod 2)) :=
  baseChangeToPeriodicComplex (Ideal.Quotient.mk (Ideal.span {w}))
    (Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self w))

/-- The hypersurface-quotient specialization commutes with passage to homotopy categories. -/
theorem quotientFunctor_comp_quotientPeriodicComplex :
    (nullHomotopic (S := S) (w := w)).quotientFunctor ⋙
        quotientPeriodicComplex (S := S) (w := w) =
      MatrixFactorization.quotientPeriodicComplex (S := S) (w := w) ⋙
        _root_.HomotopyCategory.quotient (ModuleCat.{u} (S ⧸ Ideal.span {w}))
          (ComplexShape.up (ZMod 2)) := by
  unfold quotientPeriodicComplex MatrixFactorization.quotientPeriodicComplex
  exact quotientFunctor_comp_baseChangeToPeriodicComplex _ _

instance : (quotientPeriodicComplex (S := S) (w := w)).Additive := by
  dsimp [quotientPeriodicComplex]
  infer_instance

end HomotopyCategory

end TauCeti.MatrixFactorization
