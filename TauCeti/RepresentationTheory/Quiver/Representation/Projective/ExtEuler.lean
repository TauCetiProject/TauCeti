/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Ext.HasExt
public import Mathlib.CategoryTheory.Preadditive.Projective.Preserves
public import TauCeti.Algebra.Homology.EulerCharacteristic.ExtEuler.Basic
public import TauCeti.CategoryTheory.Linear.FullyFaithful
public import TauCeti.RepresentationTheory.Quiver.Representation.AsModule
public import TauCeti.RepresentationTheory.Quiver.Representation.Projective.EulerForm

/-!
# The Ext-Euler characteristic of a vertex projective is the quiver Euler form

For a finite quiver `Q` over a field `k` the Ext-Euler characteristic

`χ(X, Y) = ∑ n, (-1)ⁿ dim_k Extⁿ(X, Y)`

of `TauCeti.extEuler` is available in the abelian category `ModuleCat (kQ)` of modules over the
path algebra. This file evaluates it on the vertex projective `Pᵢ` and identifies the value with
the combinatorial Euler form `TauCeti.eulerForm` of the two dimension vectors:

`χ(Pᵢ, Y) = ⟨dim Pᵢ, dim Y⟩ = (dim Y)ᵢ`.

Both sides are computed without any acyclicity hypothesis on `Q`: the left-hand side because all
higher `Ext` out of a projective vanishes, the right-hand side because `Pᵢ` represents evaluation
at `i`. What is needed instead is that the paths out of `i` are finite, so that `dim Pᵢ` is an
honest path count, and that `Y` is finite-dimensional over `k`, so that `Hom(Pᵢ, Y)` is and the
pair is Euler-admissible.

The vertex projective enters as a module rather than a representation, because it is the module
category that carries `Ext`. The two are exchanged by the equivalence
`TauCeti.quiverRepFunctor`, which is `k`-linear, hence compares dimensions of morphism spaces;
`TauCeti.indecProjModule` is the `kQ`-module whose representation is `Pᵢ`.

As with `TauCeti.indecProjRep`, indecomposability of the vertex projective is not proved here;
the name follows that of the representation it carries.

## Main definitions

* `TauCeti.indecProjModule k Q i`: the `kQ`-module carrying the vertex projective `Pᵢ`, with
  `TauCeti.indecProjModuleIso` identifying its representation with `Pᵢ`.

## Main results

* `TauCeti.finrank_hom_indecProjModule`: `dim_k Hom(Pᵢ, Y)` is the `i`-th coordinate of the
  dimension vector of `Y`.
* `TauCeti.isEulerAdmissible_indecProjModule`: a vertex projective is Euler-admissible against
  every finite-dimensional module.
* `TauCeti.extEuler_indecProjModule`: `χ(Pᵢ, Y) = (dim Y)ᵢ`, and
  `TauCeti.extEuler_indecProjModule_eq_eulerForm`: that value is the Euler form
  `⟨dim Pᵢ, dim Y⟩`.
* `TauCeti.extEuler_indecProjModule_indecProjModule`: `χ(Pᵢ, Pⱼ)` counts the paths `j → i`, the
  path-counting Cartan matrix of the path algebra.

## References

* Ibrahim Assem, Daniel Simson and Andrzej Skowroński, *Elements of the Representation Theory of
  Associative Algebras I*, Chapter III, Section 3, for the Euler form of a path algebra and its
  homological reading.
* Harm Derksen and Jerzy Weyman, *An Introduction to Quiver Representations*, Chapter 1, for the
  identity `⟨dim M, dim N⟩ = dim Hom(M, N) - dim Ext¹(M, N)`, of which this file proves the case
  needing no `Ext¹`.
-/

public section

namespace TauCeti

open CategoryTheory CategoryTheory.Abelian

open scoped ModuleCat

universe u v w

section Modules

variable (k : Type u) (Q : Type v) [Field k] [Quiver.{w} Q] [Finite Q]

/-! ### The vertex projective as a module over the path algebra -/

/-- **The vertex projective `Pᵢ` as a module over the path algebra.** It is a preimage of the
representation `TauCeti.indecProjRep` under the equivalence `TauCeti.quiverRepFunctor`; under the
usual identification of representations with left modules it is the left ideal `kQ · eᵢ`. -/
noncomputable def indecProjModule (i : Q) : ModuleCat (pathAlgebra k Q) :=
  (quiverRepFunctor k Q).objPreimage (indecProjRep k Q i)

/-- The representation carried by `TauCeti.indecProjModule` is the vertex projective `Pᵢ`. -/
noncomputable def indecProjModuleIso (i : Q) :
    (quiverRepFunctor k Q).obj (indecProjModule k Q i) ≅ indecProjRep k Q i :=
  (quiverRepFunctor k Q).objObjPreimageIso _

instance (i : Q) : Projective ((quiverRepFunctor k Q).obj (indecProjModule k Q i)) :=
  Projective.of_iso (indecProjModuleIso k Q i).symm inferInstance

instance (i : Q) : Projective (indecProjModule k Q i) :=
  Projective.of_iso ((quiverRepFunctor k Q).asEquivalence.unitIso.app (indecProjModule k Q i)).symm
    ((quiverRepFunctor k Q).inv.projective_obj_of_projective
      (inferInstanceAs (Projective ((quiverRepFunctor k Q).obj (indecProjModule k Q i)))))

-- The universal property of `Pᵢ` transported to the module category: a `kQ`-linear map out of
-- `TauCeti.indecProjModule` is an element of the `i`-th vertex space of the target. Private: only
-- its consequences on dimension and finite-dimensionality are used, and its value is a composite
-- of three transports with no usable closed form.
private noncomputable def indecProjModuleHomEquiv (i : Q) (Y : ModuleCat (pathAlgebra k Q)) :
    (indecProjModule k Q i ⟶ Y) ≃ₗ[k] ((quiverRepFunctor k Q).obj Y).obj ((Paths.of Q).obj i) :=
  (((quiverRepFunctor k Q).homLinearEquiv k (indecProjModule k Q i) Y).trans
      (Linear.homCongr k (indecProjModuleIso k Q i) (Iso.refl _))).trans
    (indecProjRepHomEquiv i _)

/-- **The morphisms out of a vertex projective are its vertex space.** The dimension of
`Hom(Pᵢ, Y)` is the `i`-th coordinate of the dimension vector of the representation of `Y`. -/
theorem finrank_hom_indecProjModule (i : Q) (Y : ModuleCat (pathAlgebra k Q)) :
    Module.finrank k (indecProjModule k Q i ⟶ Y)
      = dimVector ((quiverRepFunctor k Q).obj Y) i :=
  (indecProjModuleHomEquiv k Q i Y).finrank_eq.trans (dimVector_apply _ _).symm

instance (i : Q) (Y : ModuleCat (pathAlgebra k Q)) [FiniteDimensional k Y] :
    FiniteDimensional k (indecProjModule k Q i ⟶ Y) := by
  have : FiniteDimensional k (((quiverRepFunctor k Q).obj Y).obj ((Paths.of Q).obj i)) :=
    inferInstanceAs (FiniteDimensional k (vertexComponent k (Y : Type _) i))
  exact Module.Finite.equiv (indecProjModuleHomEquiv k Q i Y).symm

/-- **A vertex projective is Euler-admissible against every finite-dimensional module**: all of
its higher `Ext` vanishes, and its `Hom` space is a vertex space of the target. -/
theorem isEulerAdmissible_indecProjModule (i : Q) (Y : ModuleCat (pathAlgebra k Q))
    [FiniteDimensional k Y] :
    IsEulerAdmissible k (indecProjModule k Q i) Y :=
  isEulerAdmissible_of_projective k _ _

/-- **Projective evaluation in quiver coordinates**: `χ(Pᵢ, Y)` is the `i`-th coordinate of the
dimension vector of `Y`. -/
theorem extEuler_indecProjModule (i : Q) {Y : ModuleCat (pathAlgebra k Q)}
    (h : IsEulerAdmissible k (indecProjModule k Q i) Y) :
    extEuler k h = dimVector ((quiverRepFunctor k Q).obj Y) i := by
  rw [extEuler_projective k h, finrank_hom_indecProjModule]

/-- **The Cartan pairing of two vertex projectives**: `χ(Pᵢ, Pⱼ)` counts the paths `j → i`. -/
theorem extEuler_indecProjModule_indecProjModule (i j : Q)
    (h : IsEulerAdmissible k (indecProjModule k Q i) (indecProjModule k Q j)) :
    extEuler k h = Nat.card (Quiver.Path j i) := by
  rw [extEuler_indecProjModule k Q i h, dimVector_eq_of_iso (indecProjModuleIso k Q j),
    dimVector_indecProjRep]

end Modules

section EulerForm

variable (k : Type u) (Q : Type v) [Field k] [Quiver.{w} Q] [Fintype Q]
  [∀ a b : Q, Fintype (a ⟶ b)]

/-! ### Comparison with the Euler form of the quiver -/

/-- **The Ext-Euler characteristic of a vertex projective is the quiver Euler form.** For every
`kQ`-module `Y`, `χ(Pᵢ, Y)` is the Euler form `⟨dim Pᵢ, dim Y⟩` of the two dimension vectors. -/
theorem extEuler_indecProjModule_eq_eulerForm (i : Q) [∀ a : Q, Finite (Quiver.Path i a)]
    {Y : ModuleCat (pathAlgebra k Q)} (h : IsEulerAdmissible k (indecProjModule k Q i) Y) :
    extEuler k h
      = eulerForm Q (fun a ↦ (dimVector (indecProjRep k Q i) a : ℤ))
          (fun a ↦ (dimVector ((quiverRepFunctor k Q).obj Y) a : ℤ)) := by
  rw [eulerForm_dimVector_indecProjRep, extEuler_indecProjModule]

end EulerForm

end TauCeti
