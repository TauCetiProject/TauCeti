/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.LineBundle.Germ
public import TauCeti.AlgebraicGeometry.Modules.RationalFunctions

/-!
# Rational functions represented by generically free rank-one module sections

A sheaf of modules on an irreducible scheme that is free of rank one on a dense open subset has a
rational trivialization. A chosen basis there maps every local section to a rational
function and hence gives a morphism from the sheaf of modules to the sheaf of rational functions.
For an invertible sheaf on an integral scheme this morphism is injective, so it realizes the line
bundle as a subsheaf of the rational functions; this is the embedding from which the divisor of a
line bundle is read off.

## Main declarations

* `Scheme.Modules.rationalFunction` reads a local section as an element of the function field.
* `Scheme.Modules.rationalFunction_smul` and `Scheme.Modules.rationalFunction_map` describe its
  compatibility with scalar multiplication and restriction.
* `Scheme.Modules.rationalTrivializationHom` is the resulting morphism to the rational-function
  sheaf, and `Scheme.Modules.rationalFunctionsEquiv_rationalTrivializationHom_app` computes it on
  every nonempty open subset.
* `Scheme.Modules.rationalFunction_injective` and `Scheme.Modules.mono_rationalTrivializationHom`
  show that, for a line bundle on an integral scheme, this morphism is injective on sections and
  hence a monomorphism.

The construction follows Hartshorne, *Algebraic Geometry*, II.6. No formalization is vendored.
-/

public section

open CategoryTheory Opposite Set TopologicalSpace TauCeti.AlgebraicGeometry

universe u

noncomputable section

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}} [IrreducibleSpace X]

private def coordinateHom (M : X.Modules) {U : X.Opens}
    (e : SheafOfModules.free (R := X.ringCatSheaf.over U) PUnit ≅ M.over U) :
    M.over U ⟶ SheafOfModules.unit (X.ringCatSheaf.over U) :=
  e.inv ≫ (TauCeti.SheafOfModules.freePUnitIsoUnit (X.ringCatSheaf.over U)).hom

/-- The rational function represented by a local section of a sheaf of modules after choosing a
free rank-one trivialization on a dense open subset. -/
def rationalFunction (M : X.Modules) {U : X.Opens}
    (e : SheafOfModules.free (R := X.ringCatSheaf.over U) PUnit ≅ M.over U)
    (hU : Dense (U : Set X)) (V : X.Opens) [Nonempty V] :
    Γ(M, V) →+ X.functionField := by
  let W : X.Opens := V ⊓ U
  let _ : Nonempty W := Opens.nonempty_coeSort.mpr
    (hU.inter_open_nonempty V V.isOpen (Opens.nonempty_coeSort.mp ‹_›))
  let A : Over U := Over.mk (homOfLE (show W ≤ U from inf_le_right))
  exact (X.germToFunctionField W).hom.toAddMonoidHom.comp
    (((coordinateHom M e).val.app (op A)).hom.toAddMonoidHom.comp
      (M.presheaf.map (homOfLE inf_le_left).op).hom)

/-- Unfolding lemma for `rationalFunction`: restrict to `V ⊓ U`, read the section in the chosen
basis, and take the germ at the generic point. -/
private lemma rationalFunction_apply (M : X.Modules) {U : X.Opens}
    (e : SheafOfModules.free (R := X.ringCatSheaf.over U) PUnit ≅ M.over U)
    (hU : Dense (U : Set X)) (V : X.Opens) [Nonempty V] [Nonempty (V ⊓ U : X.Opens)]
    (s : Γ(M, V)) :
    rationalFunction M e hU V s = X.germToFunctionField (V ⊓ U)
      ((coordinateHom M e).val.app (op (Over.mk (homOfLE (inf_le_right : V ⊓ U ≤ U))))
        (M.presheaf.map (homOfLE (inf_le_left : V ⊓ U ≤ V)).op s)) :=
  rfl

/-- Multiplying a module section by a regular function multiplies its rational function by the
image of that regular function in the function field. -/
@[simp]
theorem rationalFunction_smul (M : X.Modules) {U : X.Opens}
    (e : SheafOfModules.free (R := X.ringCatSheaf.over U) PUnit ≅ M.over U)
    (hU : Dense (U : Set X)) (V : X.Opens) [Nonempty V] (r : Γ(X, V)) (s : Γ(M, V)) :
    rationalFunction M e hU V (r • s) =
      X.germToFunctionField V r * rationalFunction M e hU V s := by
  have : Nonempty (V ⊓ U : X.Opens) := Opens.nonempty_coeSort.mpr
    (hU.inter_open_nonempty V V.isOpen (Opens.nonempty_coeSort.mp ‹_›))
  let i : V ⊓ U ⟶ V := homOfLE inf_le_left
  let c := (coordinateHom M e).val.app (op (Over.mk (homOfLE (inf_le_right : V ⊓ U ≤ U))))
  have hc := c.hom.map_smul (X.presheaf.map i.op r) (M.presheaf.map i.op s)
  rw [rationalFunction_apply, rationalFunction_apply, M.map_smul]
  refine (congrArg (X.germToFunctionField (V ⊓ U)) hc).trans ?_
  -- Over each open, the unit sheaf of modules is the ring of sections as a module over itself,
  -- so its scalar action is multiplication by definition; Mathlib has no rewrite lemma for this.
  let b : Γ(X, V ⊓ U) := c (M.presheaf.map i.op s)
  change X.germToFunctionField (V ⊓ U) (X.presheaf.map i.op r * b) = _
  rw [map_mul, X.presheaf.germ_res_apply i (genericPoint X)]

/-- Rational functions represented by module sections are unchanged by restriction to a nonempty
open subset. -/
@[simp]
theorem rationalFunction_map (M : X.Modules) {U V T : X.Opens}
    (e : SheafOfModules.free (R := X.ringCatSheaf.over U) PUnit ≅ M.over U)
    (hU : Dense (U : Set X)) (i : V ⟶ T) [Nonempty V] [Nonempty T] (s : Γ(M, T)) :
    rationalFunction M e hU V (M.presheaf.map i.op s) = rationalFunction M e hU T s := by
  have : Nonempty (T ⊓ U : X.Opens) := Opens.nonempty_coeSort.mpr
    (hU.inter_open_nonempty T T.isOpen (Opens.nonempty_coeSort.mp ‹_›))
  have : Nonempty (V ⊓ U : X.Opens) := Opens.nonempty_coeSort.mpr
    (hU.inter_open_nonempty V V.isOpen (Opens.nonempty_coeSort.mp ‹_›))
  let j : V ⊓ U ⟶ T ⊓ U := homOfLE (inf_le_inf i.le le_rfl)
  let f : Over.mk (homOfLE (inf_le_right : V ⊓ U ≤ U)) ⟶
      Over.mk (homOfLE (inf_le_right : T ⊓ U ≤ U)) := Over.homMk j
  let c' : (M.over U).val.presheaf ⟶
      (SheafOfModules.unit (X.ringCatSheaf.over U)).val.presheaf :=
    (SheafOfModules.forget _ ⋙ PresheafOfModules.toPresheaf _).map (coordinateHom M e)
  have hM : (M.over U).val.presheaf.map f.op
      (M.presheaf.map (homOfLE (inf_le_left : T ⊓ U ≤ T)).op s) =
        M.presheaf.map (homOfLE (inf_le_left : V ⊓ U ≤ V)).op (M.presheaf.map i.op s) := by
    -- Restriction in `M.over U` along a morphism of `Over U` is, by definition of the
    -- pushforward along `Over.forget U`, restriction in `M` along the underlying inclusion.
    change M.presheaf.map j.op _ = _
    simp only [← ConcreteCategory.comp_apply, ← Functor.map_comp]
    congr 2
  have h := c'.naturality_apply f.op (M.presheaf.map (homOfLE inf_le_left).op s)
  rw [hM] at h
  rw [rationalFunction_apply, rationalFunction_apply]
  refine (congrArg (X.germToFunctionField (V ⊓ U)) h).trans ?_
  exact X.presheaf.germ_res_apply j (genericPoint X) (Scheme.genericPoint_mem _) _

private def rationalApp (M : X.Modules) {U : X.Opens}
    (e : SheafOfModules.free (R := X.ringCatSheaf.over U) PUnit ≅ M.over U)
    (hU : Dense (U : Set X)) (V : X.Opens) [Nonempty V] :
    M.val.obj (op V) ⟶ (Scheme.rationalFunctions X).val.obj (op V) :=
  ModuleCat.ofHom
    { toFun := fun s ↦ (Scheme.rationalFunctionsEquiv V).symm (rationalFunction M e hU V s)
      map_add' := fun s t ↦ by
        calc
          _ = (Scheme.rationalFunctionsEquiv V).symm
              (rationalFunction M e hU V s + rationalFunction M e hU V t) :=
            congrArg _ (map_add (rationalFunction M e hU V) s t)
          _ = _ := map_add _ _ _
      map_smul' := fun r s ↦ by
        have hs := rationalFunction_smul M e hU V (id r : Γ(X, V)) (id s : Γ(M, V))
        calc
          _ = (Scheme.rationalFunctionsEquiv V).symm
              (X.germToFunctionField V (id r : Γ(X, V)) * rationalFunction M e hU V s) :=
            congrArg _ hs
          _ = (Scheme.rationalFunctionsEquiv V).symm
              ((id r : Γ(X, V)) • rationalFunction M e hU V s) := by
            rw [Algebra.smul_def, RingHom.algebraMap_toAlgebra]
          _ = _ := _root_.map_smul _ _ _ }

private lemma rationalApp_naturality (M : X.Modules) {U V T : X.Opens}
    (e : SheafOfModules.free (R := X.ringCatSheaf.over U) PUnit ≅ M.over U)
    (hU : Dense (U : Set X)) (i : V ⟶ T) [Nonempty V] [Nonempty T]
    (s : Γ(M, T)) :
    rationalApp M e hU V (M.presheaf.map i.op s) =
      (Scheme.rationalFunctions X).presheaf.map i.op (rationalApp M e hU T s) := by
  apply (Scheme.rationalFunctionsEquiv V).injective
  calc
    _ = rationalFunction M e hU V (M.presheaf.map i.op s) :=
      (Scheme.rationalFunctionsEquiv V).apply_symm_apply _
    _ = rationalFunction M e hU T s := rationalFunction_map M e hU i s
    _ = Scheme.rationalFunctionsEquiv T (rationalApp M e hU T s) :=
      ((Scheme.rationalFunctionsEquiv T).apply_symm_apply _).symm
    _ = _ := (Scheme.rationalFunctionsEquiv_map i (rationalApp M e hU T s)).symm

/-- The morphism from a sheaf of modules to the rational-function sheaf determined by a free
rank-one trivialization on a dense open subset. -/
def rationalTrivializationHom (M : X.Modules) {U : X.Opens}
    (e : SheafOfModules.free (R := X.ringCatSheaf.over U) PUnit ≅ M.over U)
    (hU : Dense (U : Set X)) : M ⟶ Scheme.rationalFunctions X := by
  classical
  exact
    { val :=
      { app := fun V ↦ if hV : Nonempty V.unop then
          letI := hV
          rationalApp M e hU V.unop
        else 0
        naturality := fun {V T} i ↦ by
          by_cases hT : Nonempty T.unop
          · let _ : Nonempty T.unop := hT
            let x : T.unop := Classical.choice hT
            have hV : Nonempty V.unop := ⟨⟨x.1, i.unop.le x.2⟩⟩
            let _ : Nonempty V.unop := hV
            simp only [dite_eq_left hT, dite_eq_left hV]
            ext s
            exact rationalApp_naturality M e hU i.unop s
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
theorem rationalFunctionsEquiv_rationalTrivializationHom_app (M : X.Modules)
    {U : X.Opens}
    (e : SheafOfModules.free (R := X.ringCatSheaf.over U) PUnit ≅ M.over U)
    (hU : Dense (U : Set X)) (V : X.Opens) [Nonempty V] (s : Γ(M, V)) :
    Scheme.rationalFunctionsEquiv V
        (Scheme.Modules.Hom.app (rationalTrivializationHom M e hU) V s) =
      rationalFunction M e hU V s := by
  simp only [rationalTrivializationHom, Scheme.Modules.Hom.app, dite_eq_left
    (inferInstance : Nonempty V)]
  exact (Scheme.rationalFunctionsEquiv V).apply_symm_apply _

omit [IrreducibleSpace X] in
/-- The chosen coordinate of a free rank-one trivialization is injective on sections. -/
private lemma coordinateHom_app_injective (M : X.Modules) {U : X.Opens}
    (e : SheafOfModules.free (R := X.ringCatSheaf.over U) PUnit ≅ M.over U) (A : (Over U)ᵒᵖ) :
    Function.Injective ((coordinateHom M e).val.app A) := by
  let c := (SheafOfModules.forget _ ⋙ PresheafOfModules.toPresheaf _).mapIso
    (e.symm ≪≫ TauCeti.SheafOfModules.freePUnitIsoUnit (X.ringCatSheaf.over U))
  intro a b h
  -- Isolate the definitional reduction through the two forgetful functors and `mapIso`.
  change c.hom.app A a = c.hom.app A b at h
  exact (ConcreteCategory.bijective_of_isIso (c.hom.app A)).injective h

/-- On an integral scheme, the rational function of a local section of a line bundle determines
the section: a line bundle embeds into the rational functions through any rational
trivialization. -/
theorem rationalFunction_injective [IsIntegral X] (M : X.Modules)
    [SheafOfModules.isInvertible X M] {U : X.Opens}
    (e : SheafOfModules.free (R := X.ringCatSheaf.over U) PUnit ≅ M.over U)
    (hU : Dense (U : Set X)) (V : X.Opens) [Nonempty V] :
    Function.Injective (rationalFunction M e hU V) := by
  have : Nonempty (V ⊓ U : X.Opens) := Opens.nonempty_coeSort.mpr
    (hU.inter_open_nonempty V V.isOpen (Opens.nonempty_coeSort.mp ‹_›))
  intro s t h
  rw [rationalFunction_apply, rationalFunction_apply] at h
  exact InvertibleSheaf.map_injective_of_isIntegral ⟨M, ‹_›⟩ (homOfLE inf_le_left)
    (coordinateHom_app_injective M e _ (X.germToFunctionField_injective (V ⊓ U) h))

/-- On an integral scheme, a local section of a line bundle has zero rational function exactly
when it is zero. -/
@[simp]
theorem rationalFunction_eq_zero_iff [IsIntegral X] (M : X.Modules)
    [SheafOfModules.isInvertible X M] {U : X.Opens}
    (e : SheafOfModules.free (R := X.ringCatSheaf.over U) PUnit ≅ M.over U)
    (hU : Dense (U : Set X)) (V : X.Opens) [Nonempty V] (s : Γ(M, V)) :
    rationalFunction M e hU V s = 0 ↔ s = 0 :=
  (injective_iff_map_eq_zero' _).mp (rationalFunction_injective M e hU V) s

/-- On an integral scheme, the morphism from a line bundle to the rational functions determined
by a rational trivialization is injective on sections over every open subset. -/
theorem rationalTrivializationHom_app_injective [IsIntegral X] (M : X.Modules)
    [SheafOfModules.isInvertible X M] {U : X.Opens}
    (e : SheafOfModules.free (R := X.ringCatSheaf.over U) PUnit ≅ M.over U)
    (hU : Dense (U : Set X)) (V : X.Opens) :
    Function.Injective (Scheme.Modules.Hom.app (rationalTrivializationHom M e hU) V) := by
  intro s t h
  by_cases hV : Nonempty V
  · apply rationalFunction_injective M e hU V
    rw [← rationalFunctionsEquiv_rationalTrivializationHom_app,
      ← rationalFunctionsEquiv_rationalTrivializationHom_app, h]
  · exact TopCat.Presheaf.section_ext ⟨M.presheaf, M.isSheaf⟩ V s t
      fun x hx ↦ (hV ⟨⟨x, hx⟩⟩).elim

/-- On an integral scheme, a line bundle is a subsheaf of the sheaf of rational functions: the
morphism determined by any rational trivialization is a monomorphism. -/
instance mono_rationalTrivializationHom [IsIntegral X] (M : X.Modules)
    [SheafOfModules.isInvertible X M] {U : X.Opens}
    (e : SheafOfModules.free (R := X.ringCatSheaf.over U) PUnit ≅ M.over U)
    (hU : Dense (U : Set X)) : Mono (rationalTrivializationHom M e hU) :=
  (SheafOfModules.forget _).mono_of_mono_map
    (PresheafOfModules.mono_of_injective fun V ↦
      rationalTrivializationHom_app_injective M e hU V.unop)

end AlgebraicGeometry.Scheme.Modules

end
