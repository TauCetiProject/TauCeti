/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.LineBundle.Basic
public import TauCeti.AlgebraicGeometry.Modules.RationalFunctions

/-!
# Rational functions represented by line-bundle sections

An invertible sheaf on an irreducible scheme becomes trivial on a dense open subset. A chosen
trivialization there identifies every local section with a rational function and hence gives a
morphism from the line bundle to the sheaf of rational functions. This is the map underlying the
rational embedding used to associate a Weil divisor to a line bundle.

## Main declarations

* `InvertibleSheaf.rationalFunction` reads a local section as an element of the function field.
* `InvertibleSheaf.rationalFunction_smul` and `InvertibleSheaf.rationalFunction_map` describe its
  compatibility with scalar multiplication and restriction.
* `InvertibleSheaf.rationalTrivializationHom` is the resulting morphism to the rational-function
  sheaf, and `InvertibleSheaf.rationalFunctionsEquiv_rationalTrivializationHom_app` computes it on
  every nonempty open subset.

The construction follows Hartshorne, *Algebraic Geometry*, II.6. No formalization is vendored.
-/

public section

open AlgebraicGeometry CategoryTheory Opposite Set TopologicalSpace

namespace TauCeti

namespace AlgebraicGeometry

universe u

noncomputable section

namespace InvertibleSheaf

variable {X : Scheme.{u}} [IrreducibleSpace X]

private def coordinateHom (L : InvertibleSheaf X) {U : X.Opens}
    (e : SheafOfModules.free (R := X.ringCatSheaf.over U) PUnit ≅ L.obj.over U) :
    L.obj.over U ⟶ SheafOfModules.unit (X.ringCatSheaf.over U) :=
  e.inv ≫ (TauCeti.SheafOfModules.freePUnitIsoUnit (X.ringCatSheaf.over U)).hom

/-- The rational function represented by a local section of a line bundle after choosing a
trivialization on a dense open subset. -/
def rationalFunction (L : InvertibleSheaf X) {U : X.Opens}
    (e : SheafOfModules.free (R := X.ringCatSheaf.over U) PUnit ≅ L.obj.over U)
    (hU : Dense (U : Set X)) (V : X.Opens) [Nonempty V] :
    Γ(L.obj, V) →+ X.functionField := by
  let W : X.Opens := V ⊓ U
  let _ : Nonempty W := Opens.nonempty_coeSort.mpr
    (hU.inter_open_nonempty V V.isOpen (Opens.nonempty_coeSort.mp ‹_›))
  let A : Over U := Over.mk (homOfLE (show W ≤ U from inf_le_right))
  exact (X.germToFunctionField W).hom.toAddMonoidHom.comp
    (((coordinateHom L e).val.app (op A)).hom.toAddMonoidHom.comp
      (L.obj.presheaf.map (homOfLE inf_le_left).op).hom)

/-- Unfolding lemma for `rationalFunction`: restrict to `V ⊓ U`, read the section in the chosen
basis, and take the germ at the generic point. -/
private lemma rationalFunction_apply (L : InvertibleSheaf X) {U : X.Opens}
    (e : SheafOfModules.free (R := X.ringCatSheaf.over U) PUnit ≅ L.obj.over U)
    (hU : Dense (U : Set X)) (V : X.Opens) [Nonempty V] [Nonempty (V ⊓ U : X.Opens)]
    (s : Γ(L.obj, V)) :
    rationalFunction L e hU V s = X.germToFunctionField (V ⊓ U)
      ((coordinateHom L e).val.app (op (Over.mk (homOfLE (inf_le_right : V ⊓ U ≤ U))))
        (L.obj.presheaf.map (homOfLE (inf_le_left : V ⊓ U ≤ V)).op s)) :=
  rfl

/-- Multiplying a line-bundle section by a regular function multiplies its rational function by
the image of that regular function in the function field. -/
@[simp]
theorem rationalFunction_smul (L : InvertibleSheaf X) {U : X.Opens}
    (e : SheafOfModules.free (R := X.ringCatSheaf.over U) PUnit ≅ L.obj.over U)
    (hU : Dense (U : Set X)) (V : X.Opens) [Nonempty V] (r : Γ(X, V)) (s : Γ(L.obj, V)) :
    rationalFunction L e hU V (r • s) =
      X.germToFunctionField V r * rationalFunction L e hU V s := by
  have : Nonempty (V ⊓ U : X.Opens) := Opens.nonempty_coeSort.mpr
    (hU.inter_open_nonempty V V.isOpen (Opens.nonempty_coeSort.mp ‹_›))
  let i : V ⊓ U ⟶ V := homOfLE inf_le_left
  let c := (coordinateHom L e).val.app (op (Over.mk (homOfLE (inf_le_right : V ⊓ U ≤ U))))
  have hc := c.hom.map_smul (X.presheaf.map i.op r) (L.obj.presheaf.map i.op s)
  rw [rationalFunction_apply, rationalFunction_apply, L.obj.map_smul]
  refine (congrArg (X.germToFunctionField (V ⊓ U)) hc).trans ?_
  -- Over each open, the unit sheaf of modules is the ring of sections as a module over itself,
  -- so its scalar action is multiplication by definition; Mathlib has no rewrite lemma for this.
  let b : Γ(X, V ⊓ U) := c (L.obj.presheaf.map i.op s)
  change X.germToFunctionField (V ⊓ U) (X.presheaf.map i.op r * b) = _
  rw [map_mul, X.presheaf.germ_res_apply i (genericPoint X)]

/-- Rational functions represented by line-bundle sections are unchanged by restriction to a
nonempty open subset. -/
@[simp]
theorem rationalFunction_map (L : InvertibleSheaf X) {U V T : X.Opens}
    (e : SheafOfModules.free (R := X.ringCatSheaf.over U) PUnit ≅ L.obj.over U)
    (hU : Dense (U : Set X)) (i : V ⟶ T) [Nonempty V] [Nonempty T] (s : Γ(L.obj, T)) :
    rationalFunction L e hU V (L.obj.presheaf.map i.op s) = rationalFunction L e hU T s := by
  have : Nonempty (T ⊓ U : X.Opens) := Opens.nonempty_coeSort.mpr
    (hU.inter_open_nonempty T T.isOpen (Opens.nonempty_coeSort.mp ‹_›))
  have : Nonempty (V ⊓ U : X.Opens) := Opens.nonempty_coeSort.mpr
    (hU.inter_open_nonempty V V.isOpen (Opens.nonempty_coeSort.mp ‹_›))
  let j : V ⊓ U ⟶ T ⊓ U := homOfLE (inf_le_inf i.le le_rfl)
  let f : Over.mk (homOfLE (inf_le_right : V ⊓ U ≤ U)) ⟶
      Over.mk (homOfLE (inf_le_right : T ⊓ U ≤ U)) := Over.homMk j
  let c' : (L.obj.over U).val.presheaf ⟶
      (SheafOfModules.unit (X.ringCatSheaf.over U)).val.presheaf :=
    (SheafOfModules.forget _ ⋙ PresheafOfModules.toPresheaf _).map (coordinateHom L e)
  have hL : (L.obj.over U).val.presheaf.map f.op
      (L.obj.presheaf.map (homOfLE (inf_le_left : T ⊓ U ≤ T)).op s) =
        L.obj.presheaf.map (homOfLE (inf_le_left : V ⊓ U ≤ V)).op (L.obj.presheaf.map i.op s) := by
    -- Restriction in `L.obj.over U` along a morphism of `Over U` is, by definition of the
    -- pushforward along `Over.forget U`, restriction in `L.obj` along the underlying inclusion.
    change L.obj.presheaf.map j.op _ = _
    simp only [← ConcreteCategory.comp_apply, ← Functor.map_comp]
    congr 2
  have h := c'.naturality_apply f.op (L.obj.presheaf.map (homOfLE inf_le_left).op s)
  rw [hL] at h
  rw [rationalFunction_apply, rationalFunction_apply]
  refine (congrArg (X.germToFunctionField (V ⊓ U)) h).trans ?_
  exact X.presheaf.germ_res_apply j (genericPoint X) (Scheme.genericPoint_mem _) _

private def rationalApp (L : InvertibleSheaf X) {U : X.Opens}
    (e : SheafOfModules.free (R := X.ringCatSheaf.over U) PUnit ≅ L.obj.over U)
    (hU : Dense (U : Set X)) (V : X.Opens) [Nonempty V] :
    L.obj.val.obj (op V) ⟶ (Scheme.rationalFunctions X).val.obj (op V) :=
  ModuleCat.ofHom
    { toFun := fun s ↦ (Scheme.rationalFunctionsEquiv V).symm (rationalFunction L e hU V s)
      map_add' := fun s t ↦ by
        calc
          _ = (Scheme.rationalFunctionsEquiv V).symm
              (rationalFunction L e hU V s + rationalFunction L e hU V t) :=
            congrArg _ (map_add (rationalFunction L e hU V) s t)
          _ = _ := map_add _ _ _
      map_smul' := fun r s ↦ by
        have hs := rationalFunction_smul L e hU V (id r : Γ(X, V)) (id s : Γ(L.obj, V))
        calc
          _ = (Scheme.rationalFunctionsEquiv V).symm
              (X.germToFunctionField V (id r : Γ(X, V)) * rationalFunction L e hU V s) :=
            congrArg _ hs
          _ = (Scheme.rationalFunctionsEquiv V).symm
              ((id r : Γ(X, V)) • rationalFunction L e hU V s) := by
            rw [Algebra.smul_def, RingHom.algebraMap_toAlgebra]
          _ = _ := map_smul _ _ _ }

private lemma rationalApp_naturality (L : InvertibleSheaf X) {U V T : X.Opens}
    (e : SheafOfModules.free (R := X.ringCatSheaf.over U) PUnit ≅ L.obj.over U)
    (hU : Dense (U : Set X)) (i : V ⟶ T) [Nonempty V] [Nonempty T]
    (s : Γ(L.obj, T)) :
    rationalApp L e hU V (L.obj.presheaf.map i.op s) =
      (Scheme.rationalFunctions X).presheaf.map i.op (rationalApp L e hU T s) := by
  apply (Scheme.rationalFunctionsEquiv V).injective
  calc
    _ = rationalFunction L e hU V (L.obj.presheaf.map i.op s) :=
      (Scheme.rationalFunctionsEquiv V).apply_symm_apply _
    _ = rationalFunction L e hU T s := rationalFunction_map L e hU i s
    _ = Scheme.rationalFunctionsEquiv T (rationalApp L e hU T s) :=
      ((Scheme.rationalFunctionsEquiv T).apply_symm_apply _).symm
    _ = _ := (Scheme.rationalFunctionsEquiv_map i (rationalApp L e hU T s)).symm

/-- The morphism from a line bundle to the rational-function sheaf determined by a
trivialization on a dense open subset. -/
def rationalTrivializationHom (L : InvertibleSheaf X) {U : X.Opens}
    (e : SheafOfModules.free (R := X.ringCatSheaf.over U) PUnit ≅ L.obj.over U)
    (hU : Dense (U : Set X)) : L.obj ⟶ Scheme.rationalFunctions X := by
  classical
  exact
    { val :=
      { app := fun V ↦ if hV : Nonempty V.unop then
          letI := hV
          rationalApp L e hU V.unop
        else 0
        naturality := fun {V T} i ↦ by
          by_cases hT : Nonempty T.unop
          · let _ : Nonempty T.unop := hT
            let x : T.unop := Classical.choice hT
            have hV : Nonempty V.unop := ⟨⟨x.1, i.unop.le x.2⟩⟩
            let _ : Nonempty V.unop := hV
            simp only [dite_eq_left hT, dite_eq_left hV]
            ext s
            exact rationalApp_naturality L e hU i.unop s
          · have hbot : T.unop = ⊥ := (Opens.not_nonempty_iff_eq_bot T.unop).mp
              (fun ⟨x, hx⟩ ↦ hT ⟨⟨x, hx⟩⟩)
            let _ : Subsingleton
                ((ModuleCat.restrictScalars (X.ringCatSheaf.obj.map i).hom).obj
                  ((Scheme.rationalFunctions X).val.obj T)) :=
              ⟨fun a b ↦ (Scheme.subsingleton_rationalFunctions T.unop hbot).elim a b⟩
            ext s
            exact Subsingleton.elim _ _ } }

/-- On a nonempty open subset, `rationalTrivializationHom` is the rational function obtained by
restricting to the chosen dense open and reading the section in the chosen basis. -/
@[simp]
theorem rationalFunctionsEquiv_rationalTrivializationHom_app (L : InvertibleSheaf X)
    {U : X.Opens}
    (e : SheafOfModules.free (R := X.ringCatSheaf.over U) PUnit ≅ L.obj.over U)
    (hU : Dense (U : Set X)) (V : X.Opens) [Nonempty V] (s : Γ(L.obj, V)) :
    Scheme.rationalFunctionsEquiv V
        (Scheme.Modules.Hom.app (rationalTrivializationHom L e hU) V s) =
      rationalFunction L e hU V s := by
  simp only [rationalTrivializationHom, Scheme.Modules.Hom.app, dite_eq_left
    (inferInstance : Nonempty V)]
  exact (Scheme.rationalFunctionsEquiv V).apply_symm_apply _

end InvertibleSheaf

end

end AlgebraicGeometry

end TauCeti
