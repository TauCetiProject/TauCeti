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
* `Scheme.Modules.range_rationalFunction` identifies the image of a line bundle in the rational
  functions on any open subset of a rank-one trivializing chart with the regular multiples of the
  rational function represented by the restricted basis section
  `Scheme.Modules.trivializationGenerator` of that chart, and
  `Scheme.Modules.isUnit_rationalFunction_trivializationGenerator` shows that this rational
  function is a unit.

The construction follows Hartshorne, *Algebraic Geometry*, II.6. No formalization is vendored.
-/

public section

open CategoryTheory Opposite Set TopologicalSpace TauCeti.AlgebraicGeometry

universe u

noncomputable section

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}} [IrreducibleSpace X]

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
    (((trivializationCoordinateIso M e).hom.val.app (op A)).hom.toAddMonoidHom.comp
      (M.presheaf.map (homOfLE inf_le_left).op).hom)

/-- Unfolding lemma for `rationalFunction`: restrict to `V ⊓ U`, read the section in the chosen
basis, and take the germ at the generic point. -/
private lemma rationalFunction_apply (M : X.Modules) {U : X.Opens}
    (e : SheafOfModules.free (R := X.ringCatSheaf.over U) PUnit ≅ M.over U)
    (hU : Dense (U : Set X)) (V : X.Opens) [Nonempty V] [Nonempty (V ⊓ U : X.Opens)]
    (s : Γ(M, V)) :
    rationalFunction M e hU V s = X.germToFunctionField (V ⊓ U)
      (trivializationCoordinate M e (homOfLE (inf_le_right : V ⊓ U ≤ U))
        (M.presheaf.map (homOfLE (inf_le_left : V ⊓ U ≤ V)).op s)) := by
  rw [trivializationCoordinate_apply]
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
  rw [rationalFunction_apply, rationalFunction_apply, M.map_smul, LinearEquiv.map_smul,
    smul_eq_mul, map_mul, X.presheaf.germ_res_apply i (genericPoint X)]

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
  have hM : M.presheaf.map (homOfLE (inf_le_left : V ⊓ U ≤ V)).op (M.presheaf.map i.op s) =
      M.presheaf.map j.op (M.presheaf.map (homOfLE (inf_le_left : T ⊓ U ≤ T)).op s) := by
    simp only [← ConcreteCategory.comp_apply, ← Functor.map_comp]
    congr 2
  have hj : (homOfLE (inf_le_right : V ⊓ U ≤ U)) = j ≫ homOfLE inf_le_right :=
    Subsingleton.elim _ _
  rw [rationalFunction_apply, rationalFunction_apply, hM, hj, trivializationCoordinate_map]
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
    ((trivializationCoordinate M e _).injective (X.germToFunctionField_injective (V ⊓ U) h))

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

/-- On an open subset `W` of a rank-one trivializing open subset `V`, the image of the
rational-trivialization morphism consists exactly of the regular-function multiples of the image
of the restricted distinguished basis section. -/
theorem range_rationalTrivializationHom_app (M : X.Modules) {U V W : X.Opens}
    (e : SheafOfModules.free (R := X.ringCatSheaf.over U) PUnit ≅ M.over U)
    (hU : Dense (U : Set X))
    (t : SheafOfModules.free (R := X.ringCatSheaf.over V) PUnit ≅ M.over V) (i : W ⟶ V) :
    Set.range (Scheme.Modules.Hom.app (rationalTrivializationHom M e hU) W) =
      {q | ∃ r : Γ(X, W), q = r • Scheme.Modules.Hom.app (rationalTrivializationHom M e hU) W
        (M.presheaf.map i.op (trivializationGenerator M t))} := by
  ext q
  constructor
  · rintro ⟨s, rfl⟩
    obtain ⟨r, rfl, -⟩ := existsUnique_eq_smul_map_trivializationGenerator M t i s
    exact ⟨r, Scheme.Modules.Hom.app_smul _ _ _⟩
  · rintro ⟨r, rfl⟩
    exact ⟨r • M.presheaf.map i.op (trivializationGenerator M t),
      Scheme.Modules.Hom.app_smul _ _ _⟩

/-- On a nonempty open subset `W` of a rank-one trivializing open subset `V`, the rational
functions represented by sections are exactly the products of regular functions with the rational
function represented by the restricted distinguished basis section. -/
theorem range_rationalFunction (M : X.Modules) {U V W : X.Opens}
    (e : SheafOfModules.free (R := X.ringCatSheaf.over U) PUnit ≅ M.over U)
    (hU : Dense (U : Set X))
    (t : SheafOfModules.free (R := X.ringCatSheaf.over V) PUnit ≅ M.over V) (i : W ⟶ V)
    [Nonempty W] :
    Set.range (rationalFunction M e hU W) =
      {q | ∃ r : Γ(X, W), q = X.germToFunctionField W r *
        rationalFunction M e hU W (M.presheaf.map i.op (trivializationGenerator M t))} := by
  ext q
  constructor
  · rintro ⟨s, rfl⟩
    obtain ⟨r, rfl, -⟩ := existsUnique_eq_smul_map_trivializationGenerator M t i s
    exact ⟨r, rationalFunction_smul M e hU W r _⟩
  · rintro ⟨r, rfl⟩
    exact ⟨r • M.presheaf.map i.op (trivializationGenerator M t),
      rationalFunction_smul M e hU W r _⟩

/-- The rational function represented by the distinguished basis section on a nonempty
rank-one trivializing open subset is a unit of the function field: on the nonempty open subset
where both trivializations are defined, its coordinate is a transition unit. -/
theorem isUnit_rationalFunction_trivializationGenerator (M : X.Modules) {U V : X.Opens}
    (e : SheafOfModules.free (R := X.ringCatSheaf.over U) PUnit ≅ M.over U)
    (hU : Dense (U : Set X))
    (t : SheafOfModules.free (R := X.ringCatSheaf.over V) PUnit ≅ M.over V)
    [Nonempty V] :
    IsUnit (rationalFunction M e hU V (trivializationGenerator M t)) := by
  have : Nonempty (V ⊓ U : X.Opens) := Opens.nonempty_coeSort.mpr
    (hU.inter_open_nonempty V V.isOpen (Opens.nonempty_coeSort.mp ‹_›))
  obtain ⟨u, hu, -⟩ := existsUnique_map_trivializationGenerator_eq_smul M t e
    (homOfLE inf_le_left) (homOfLE inf_le_right)
  rw [rationalFunction_apply, hu, LinearEquiv.map_smul,
    trivializationCoordinate_map_trivializationGenerator, smul_eq_mul, mul_one]
  exact u.isUnit.map _

/-- The rational function represented by the distinguished basis section on a nonempty
trivializing open subset, bundled as a unit of the function field. Its regular multiples are
exactly the image of the module sheaf on that open subset (`range_rationalFunction`). -/
def trivializationGeneratorRationalUnit (M : X.Modules) {U V : X.Opens}
    (e : SheafOfModules.free (R := X.ringCatSheaf.over U) PUnit ≅ M.over U)
    (hU : Dense (U : Set X))
    (t : SheafOfModules.free (R := X.ringCatSheaf.over V) PUnit ≅ M.over V)
    [Nonempty V] : X.functionFieldˣ :=
  (isUnit_rationalFunction_trivializationGenerator M e hU t).unit

/-- The function-field value of the bundled rational coefficient of a local basis section. -/
@[simp]
theorem coe_trivializationGeneratorRationalUnit (M : X.Modules) {U V : X.Opens}
    (e : SheafOfModules.free (R := X.ringCatSheaf.over U) PUnit ≅ M.over U)
    (hU : Dense (U : Set X))
    (t : SheafOfModules.free (R := X.ringCatSheaf.over V) PUnit ≅ M.over V)
    [Nonempty V] :
    (trivializationGeneratorRationalUnit M e hU t : X.functionField) =
      rationalFunction M e hU V (trivializationGenerator M t) :=
  IsUnit.unit_spec _

/-- On a nonempty open subset `W` of the domains `V₁`, `V₂` of two rank-one trivializations, the
rational functions represented by their restricted basis sections differ by a regular unit on
`W`, namely the transition unit of `existsUnique_map_trivializationGenerator_eq_smul`. This is the
transition-unit condition needed to glue the local principal images of `range_rationalFunction`
over overlapping charts into Cartier-divisor data. -/
theorem exists_rationalFunction_trivializationGenerator_eq_mul (M : X.Modules)
    {U V₁ V₂ W : X.Opens}
    (e : SheafOfModules.free (R := X.ringCatSheaf.over U) PUnit ≅ M.over U)
    (hU : Dense (U : Set X))
    (t₁ : SheafOfModules.free (R := X.ringCatSheaf.over V₁) PUnit ≅ M.over V₁)
    (t₂ : SheafOfModules.free (R := X.ringCatSheaf.over V₂) PUnit ≅ M.over V₂)
    (i₁ : W ⟶ V₁) (i₂ : W ⟶ V₂) [Nonempty W] :
    ∃ r : Γ(X, W)ˣ,
      rationalFunction M e hU W (M.presheaf.map i₁.op (trivializationGenerator M t₁)) =
        X.germToFunctionField W (r : Γ(X, W)) *
          rationalFunction M e hU W (M.presheaf.map i₂.op (trivializationGenerator M t₂)) := by
  obtain ⟨r, hr, -⟩ := existsUnique_map_trivializationGenerator_eq_smul M t₁ t₂ i₁ i₂
  exact ⟨r, by rw [hr, rationalFunction_smul]⟩

end AlgebraicGeometry.Scheme.Modules

end
