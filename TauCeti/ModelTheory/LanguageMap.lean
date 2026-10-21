/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.ModelTheory.LanguageMap

/-!
# Constants interpreted through a map

For a language `L` and a map `c : A → M`, Mathlib's `constantsOn.structure c` makes `M` an
`L[[A]]`-structure in which the constant symbol of `a : A` is interpreted by `c a`. This file
records that interpretation as a simp lemma, and shows that a homomorphism of `L`-structures
carrying `c` to `d` is a homomorphism of the induced `L[[A]]`-structures.

## Main definitions

* `FirstOrder.Language.withConstantsHom`: an `L`-homomorphism `φ` with `φ ∘ c = d` is a
  homomorphism of `L[[A]]`-structures, for the structures given by `c` and `d`.

## Main results

* `FirstOrder.Language.coe_con_constantsOn`: under `constantsOn.structure c`, the constant symbol
  of `a` denotes `c a`.
-/

public section

namespace FirstOrder.Language

variable {L : Language} {A : Type*} {M : Type*} {N : Type*}

/-- Under the structure `constantsOn.structure c`, the constant symbol of `a : A` in `L[[A]]`
denotes `c a`. -/
@[simp]
theorem coe_con_constantsOn [L.Structure M] (c : A → M) (a : A) :
    letI := constantsOn.structure c
    ((L.con a : L[[A]].Constants) : M) = c a := (rfl)

/-- An `L`-homomorphism `φ` with `φ ∘ c = d` is a homomorphism of `L[[A]]`-structures, for the
structures `constantsOn.structure c` and `constantsOn.structure d`. In particular realizing an
`L[[A]]`-term commutes with `φ`, by `FirstOrder.Language.HomClass.realize_term`. -/
def withConstantsHom [L.Structure M] [L.Structure N] {F : Type*} [FunLike F M N]
    [L.HomClass F M N] (c : A → M) (d : A → N) (φ : F) (h : ∀ a, φ (c a) = d a) :
    letI := constantsOn.structure c
    letI := constantsOn.structure d
    M →[L[[A]]] N :=
  letI := constantsOn.structure c
  letI := constantsOn.structure d
  { toFun := φ
    map_fun' := fun {n} f x => by
      rcases f with f | f
      · simp only [withConstants_funMap_sumInl]
        exact HomClass.map_fun φ f x
      · cases n with
        | zero =>
          -- `f : (constantsOn A).Functions 0` is the constant name `f : A`
          have hM := withConstants_funMap_sumInr (L := L) (α := A) (a := f) (x := x)
          have hN := withConstants_funMap_sumInr (L := L) (α := A) (a := f) (x := φ ∘ x)
          exact (congrArg φ (hM.trans (coe_con_constantsOn c f))).trans
            ((h f).trans (hN.trans (coe_con_constantsOn d f)).symm)
        | succ n => exact isEmptyElim f
    map_rel' := fun {n} r x => by
      rcases r with r | r
      · simp only [withConstants_relMap_sumInl]
        exact HomClass.map_rel φ r x
      · exact isEmptyElim r }

@[simp]
theorem coe_withConstantsHom [L.Structure M] [L.Structure N] {F : Type*} [FunLike F M N]
    [L.HomClass F M N] (c : A → M) (d : A → N) (φ : F) (h : ∀ a, φ (c a) = d a) :
    ⇑(withConstantsHom c d φ h) = φ := (rfl)

end FirstOrder.Language
