/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Adjunctions

/-!
# The forgetful functor from modules to types is lax monoidal

The forgetful functor `forget (ModuleCat R)` is right adjoint to the free module functor
`ModuleCat.free R`, which Mathlib makes monoidal. It is therefore lax monoidal, with the mate
structure of `CategoryTheory.Adjunction.rightAdjointLaxMonoidal`: the unit picks out `1 : R`
(`ModuleCat.forget_ε`) and the tensorator sends a pair `(m, n)` to `m ⊗ₜ n`
(`ModuleCat.forget_μ`). Maps out of the tensor unit `R` correspond to their value at `1`, so
the forgetful functor induces bijections on maps out of the tensor units
(`ModuleCat.bijective_ε_comp_forget_map`).

Postcomposed with simplicial objects, this is the lax monoidal functor taking a simplicial module
to its underlying simplicial set.
-/

public section

open CategoryTheory MonoidalCategory

universe v

namespace ModuleCat

variable (R : Type v) [CommRing R]

/-- The forgetful functor from `R`-modules to types is lax monoidal, as the right adjoint of the
monoidal free module functor. -/
noncomputable instance forgetLaxMonoidal : (forget (ModuleCat.{v} R)).LaxMonoidal :=
  (ModuleCat.adj R).rightAdjointLaxMonoidal

/-- The unit of the lax monoidal forgetful functor picks out `1 : R`. -/
@[simp]
lemma forget_ε :
    Functor.LaxMonoidal.ε (forget (ModuleCat.{v} R)) = TypeCat.ofHom fun _ ↦ (1 : R) := by
  ext ⟨⟩
  simp [Adjunction.rightAdjointLaxMonoidal_ε]

variable {R} in
/-- The tensorator of the lax monoidal forgetful functor sends a pair to its pure tensor. -/
@[simp]
lemma forget_μ (M N : ModuleCat.{v} R) :
    Functor.LaxMonoidal.μ (forget (ModuleCat.{v} R)) M N =
      TypeCat.ofHom fun x : M × N ↦ (x.1 ⊗ₜ x.2 : (M ⊗ N : ModuleCat.{v} R)) := by
  ext x
  simp [Adjunction.rightAdjointLaxMonoidal_μ, ← Adjunction.homEquiv_symm_id]

variable {R} in
/-- Maps of modules out of the tensor unit `R` are determined by, and can take, any value at
`1`: the lax monoidal forgetful functor induces bijections on maps out of the tensor units. -/
lemma bijective_ε_comp_forget_map (M : ModuleCat.{v} R) :
    Function.Bijective fun f : 𝟙_ (ModuleCat.{v} R) ⟶ M ↦
      Functor.LaxMonoidal.ε (forget (ModuleCat.{v} R)) ≫ (forget (ModuleCat.{v} R)).map f := by
  convert ((homEquiv (M := 𝟙_ (ModuleCat.{v} R)) (N := M)).trans <|
    (LinearMap.ringLmapEquivSelf R R M).toEquiv.trans
      (TypeCat.homEquiv.trans (Equiv.funUnique PUnit M)).symm).bijective using 1
  ext f ⟨⟩
  simp [homEquiv]

end ModuleCat
