/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Quiver.FiniteRepType.Basic
public import TauCeti.Algebra.Category.ModuleCat.RepresentationFinite
public import TauCeti.RepresentationTheory.Quiver.Representation.FiniteDimensional
public import TauCeti.RepresentationTheory.Quiver.FiniteRepType.Gabriel
import TauCeti.CategoryTheory.Preadditive.Indecomposable
import Mathlib.CategoryTheory.ObjectProperty.Equivalence

/-!
# Finite representation type of a quiver and of its path algebra

For a quiver with finitely many paths, the quiver has finite representation type
(`TauCeti.IsFiniteRepType`) exactly when its path algebra is representation-finite
(`TauCeti.IsRepresentationFinite`). The equivalence `TauCeti.quiverRepEquivalence` between
representations and path-algebra modules matches pointwise finite-dimensional representations
with finitely generated modules, and preserves indecomposability, so it identifies the two
skeletons of indecomposables.

With Gabriel's theorem (`TauCeti.isFiniteRepType_iff_titsForm_posDef`) this gives the
classification of the representation-finite path algebras: for a connected quiver with finitely
many paths, the path algebra is representation-finite exactly when the Tits form is positive
definite (`TauCeti.isRepresentationFinite_pathAlgebra_iff_titsForm_posDef`).

## References

* I. Assem, D. Simson, A. Skowroński, *Elements of the Representation Theory of Associative
  Algebras*, Vol. I (2006), Chapters III and VII.
* P. Gabriel, *Unzerlegbare Darstellungen I*, Manuscripta Math. **6** (1972), 71--103.
-/

public section

namespace TauCeti

open CategoryTheory
open scoped ModuleCat.Algebra

universe u v w t

variable (k : Type u) (Q : Type v) [Field k] [Quiver.{w} Q] [Finite (Quiver.TotalPath Q)]

/-- A quiver with finitely many paths has finite representation type exactly when its path
algebra is representation-finite. -/
theorem isFiniteRepType_iff_isRepresentationFinite_pathAlgebra :
    IsFiniteRepType.{u, v, w, t} k Q ↔ IsRepresentationFinite.{t} (pathAlgebra k Q) := by
  let E := quiverRepEquivalence.{u, v, w, t} k Q
  let P : ObjectProperty (ModuleCat.{t} (pathAlgebra k Q)) :=
    fun M ↦ Module.Finite (pathAlgebra k Q) M ∧ Indecomposable M
  have : P.IsClosedUnderIsomorphisms :=
    ⟨fun e h ↦ have := h.1; ⟨Module.Finite.equiv e.toLinearEquiv, h.2.of_iso e⟩⟩
  have h : P.inverseImage E.functor = fun M ↦ IsFinDim k Q M ∧ Indecomposable M := by
    funext M
    apply propext
    constructor
    · rintro ⟨hfin, hI⟩
      have : Module.Finite k (E.functor.obj M) := Module.Finite.trans (pathAlgebra k Q) _
      have hF := isFinDim_quiverRepFunctor_obj k Q (E.functor.obj M) inferInstance
      rw [← quiverRepEquivalence_inverse] at hF
      exact ⟨hF.of_iso (E.unitIso.app M).symm,
        (E.inverse.indecomposable_obj_of_map_bijective hI
          (E.fullyFaithfulInverse.map_bijective _ _)).of_iso (E.unitIso.app M).symm⟩
    · rintro ⟨hM, hI⟩
      exact ⟨module_finite_pathAlgebra_quiverRepEquivalenceFunctorObj_of_isFinDim k Q M hM,
        E.functor.indecomposable_obj_of_map_bijective hI
          (E.fullyFaithfulFunctor.map_bijective _ _)⟩
  rw [isFiniteRepType_iff, isRepresentationFinite_iff]
  exact (E.congrFullSubcategory h).skeletonEquiv.finite_iff

/-- **Gabriel's theorem for path algebras.** For a finite connected quiver with finitely many paths,
the path algebra is representation-finite exactly when the Tits form is positive definite. -/
theorem isRepresentationFinite_pathAlgebra_iff_titsForm_posDef [Fintype Q]
    [∀ a b : Q, Fintype (a ⟶ b)] (hconn : (Quiver.underlyingGraph Q).Connected) :
    IsRepresentationFinite.{u} (pathAlgebra k Q) ↔ (titsForm Q).PosDef :=
  (isFiniteRepType_iff_isRepresentationFinite_pathAlgebra.{u, v, w, u} k Q).symm.trans
    (isFiniteRepType_iff_titsForm_posDef hconn)

end TauCeti
