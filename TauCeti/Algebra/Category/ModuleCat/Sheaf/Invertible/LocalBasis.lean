/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Category.ModuleCat.Sheaf.Free.Basic
public import TauCeti.Algebra.Category.ModuleCat.Sheaf.Invertible.LocalTriviality
public import TauCeti.Algebra.Category.ModuleCat.Sheaf.Over

/-!
# Invertible sheaves from local bases

A sheaf of modules `M` over a sheaf of rings `R` is invertible as soon as it has a *local basis*
on each member `X i` of a cover: a section `s i` of `M` over `X i` such that, over every object
`Y` mapping to `X i`, every section of `M` over `Y` is a unique multiple of the restriction of
`s i` to `Y`. The section `s i` is then a global basis of the restriction `M.over (X i)`, so
multiplication by it is an isomorphism from the structure sheaf of the slice to `M.over (X i)`
(`TauCeti.SheafOfModules.isIso_unitHomEquiv_symm`), and these isomorphisms form a rank-one local
trivialization atlas (`TauCeti.SheafOfModules.LocalTrivializations`).

This is the form in which local frames of a line bundle given by explicit functions, such as the
frames of an automorphy sheaf in the charts of a modular curve, show that the sheaf they
trivialize is invertible.

## Main declarations

* `TauCeti.SheafOfModules.LocalTrivializations.ofBijectiveSMul`: the rank-one local trivialization
  atlas given by local bases.
* `TauCeti.SheafOfModules.IsInvertible.of_bijective_smul`: a sheaf of modules with local bases on
  a cover is invertible.
-/

public section

open CategoryTheory Opposite

namespace TauCeti

universe u v₁ u₁

noncomputable section

namespace SheafOfModules

variable {C : Type u₁} [Category.{v₁} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{u}}
  {M : _root_.SheafOfModules.{u} R}

/-- **A local basis trivializes the restriction.** If `s` is a section of `M` over `X` such that,
over every `f : Y ⟶ X`, multiplying the restriction of `s` along `f` by scalars is a bijection
`R(Y) → M(Y)`, then multiplication by `s` is an isomorphism from the structure sheaf of the slice
over `X` to the restriction `M.over X`. This generalizes the construction
`AlgebraicGeometry.Scheme.IdealSheafData.unitOverIsoOfIdealEqSpan`. -/
def unitOverIsoOfBijectiveSMul {X : C} (s : M.val.obj (op X))
    (hs : ∀ (Y : C) (f : Y ⟶ X),
      Function.Bijective fun r : R.obj.obj (op Y) ↦ r • M.val.map f.op s) :
    _root_.SheafOfModules.unit (R.over X) ≅ M.over X :=
  have : IsIso ((M.over X).unitHomEquiv.symm ((M.overSectionsEquiv X).symm s)) :=
    isIso_unitHomEquiv_symm _ fun Y ↦ by
      induction Y using Opposite.rec with | op Y => ?_
      -- Over `Y ⟶ X`, the sections of `R` and `M` restricted to the slice are those over `Y`,
      -- and the value of the global section of `M.over X` is the restriction of `s`. `rw` cannot
      -- match the evaluation lemma, whose slice coefficient sheaf is elaborated differently.
      erw [_root_.SheafOfModules.overSectionsEquiv_symm_apply_eval]
      exact hs Y.left Y.hom
  asIso ((M.over X).unitHomEquiv.symm ((M.overSectionsEquiv X).symm s))

/-- The trivialization associated to a local basis acts by multiplying its restriction by the
input scalar. -/
@[simp]
theorem unitOverIsoOfBijectiveSMul_hom_val_app {X : C} (s : M.val.obj (op X))
    (hs : ∀ (Y : C) (f : Y ⟶ X),
      Function.Bijective fun r : R.obj.obj (op Y) ↦ r • M.val.map f.op s)
    (Y : Over X) (r : R.obj.obj (op Y.left)) :
    (unitOverIsoOfBijectiveSMul s hs).hom.val.app (op Y) r = r • M.val.map Y.hom.op s := by
  unfold unitOverIsoOfBijectiveSMul
  rw [asIso_hom]
  -- As in the construction, the slice coefficient instances differ syntactically.
  erw [unitHomEquiv_symm_val_app, _root_.SheafOfModules.overSectionsEquiv_symm_apply_eval]
  rfl

variable [∀ Y : C, HasWeakSheafify (J.over Y) AddCommGrpCat.{u}]
  [∀ Y : C, (J.over Y).WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- The rank-one local trivialization atlas given by local bases `s i` on a cover `X i`: over each
`X i`, the free sheaf on one generator is identified with the restriction of `M` by
multiplication by `s i` (`TauCeti.SheafOfModules.unitOverIsoOfBijectiveSMul`). -/
def LocalTrivializations.ofBijectiveSMul {ι : Type u₁} (X : ι → C) (hX : J.CoversTop X)
    (s : ∀ i, M.val.obj (op (X i)))
    (hs : ∀ i (Y : C) (f : Y ⟶ X i),
      Function.Bijective fun r : R.obj.obj (op Y) ↦ r • M.val.map f.op (s i)) :
    LocalTrivializations M where
  I := ι
  X := X
  coversTop := hX
  iso i := freePUnitIsoUnit (R.over (X i)) ≪≫ unitOverIsoOfBijectiveSMul (s i) (hs i)

namespace LocalTrivializations

variable {ι : Type u₁} (X : ι → C) (hX : J.CoversTop X)
  (s : ∀ i, M.val.obj (op (X i)))
  (hs : ∀ i (Y : C) (f : Y ⟶ X i),
    Function.Bijective fun r : R.obj.obj (op Y) ↦ r • M.val.map f.op (s i))

/-- The atlas constructed from local bases uses the given indexing type. -/
@[simp]
theorem ofBijectiveSMul_I : (ofBijectiveSMul X hX s hs).I = ι := (rfl)

/-- The atlas constructed from local bases uses the given covering objects. -/
@[simp]
theorem ofBijectiveSMul_X :
    (ofBijectiveSMul X hX s hs).X = fun i ↦ X ((ofBijectiveSMul_I X hX s hs).mp i) := (rfl)

/-- The local isomorphism of the atlas is the trivialization given by its basis section. -/
@[simp]
theorem ofBijectiveSMul_iso (i : (ofBijectiveSMul X hX s hs).I) :
    (ofBijectiveSMul X hX s hs).iso i =
      cast (by rw [ofBijectiveSMul_X])
        (freePUnitIsoUnit (R.over (X ((ofBijectiveSMul_I X hX s hs).mp i))) ≪≫
          unitOverIsoOfBijectiveSMul (s ((ofBijectiveSMul_I X hX s hs).mp i))
            (hs ((ofBijectiveSMul_I X hX s hs).mp i))) := (rfl)

end LocalTrivializations

/-- **A sheaf of modules with local bases is invertible.** If a cover `X i` carries sections `s i`
of `M` such that over every `f : Y ⟶ X i` every section of `M` over `Y` is a unique scalar multiple
of the restriction of `s i`, then `M` is locally free of rank one. -/
theorem IsInvertible.of_bijective_smul {ι : Type u₁} (X : ι → C) (hX : J.CoversTop X)
    (s : ∀ i, M.val.obj (op (X i)))
    (hs : ∀ i (Y : C) (f : Y ⟶ X i),
      Function.Bijective fun r : R.obj.obj (op Y) ↦ r • M.val.map f.op (s i)) :
    IsInvertible M :=
  (LocalTrivializations.ofBijectiveSMul X hX s hs).isInvertible

end SheafOfModules

end

end TauCeti
