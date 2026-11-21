/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.Algebra.Category.ModuleCat.Ext.HasExt
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.Linear
public import TauCeti.RepresentationTheory.Quiver.AdmissibleIdeal.Basic
public import TauCeti.RepresentationTheory.Quiver.Representation.VertexSimpleModule
public import TauCeti.RingTheory.Semisimple.BasicAlgebra
import Mathlib.Algebra.Category.ModuleCat.Simple
import TauCeti.RepresentationTheory.Quiver.AdmissibleIdeal.Presentation
import TauCeti.RingTheory.Idempotents.Jacobson
import TauCeti.RingTheory.Idempotents.RadicalLayerExt

/-!
# Admissible bound-quiver presentations and the Ext-quiver

Let `A` be a finite-dimensional algebra over a field `k`, with Jacobson radical `J`, equipped with
a complete family of nonzero orthogonal idempotents `e : Q → A` whose classes span `A ⧸ J` over
`k`. Choosing lifts in `eⱼ J eᵢ` of a `k`-basis of each `(j, i)`-corner of `J ⧸ J ^ 2` gives a
quiver structure on `Q` and a surjective algebra homomorphism `f : kQ →ₐ[k] A` with admissible
kernel (`CompleteOrthogonalIdempotents.exists_surjective_pathAlgebra_isAdmissibleIdeal_ker`).

This file identifies the simple modules and the arrow counts of that presentation:

* each top `Sᵢ = A eᵢ / J (A eᵢ)` restricts along any `k`-algebra map `F : kQ →ₐ[k] A` sending
  `vertexIdempotent k i` to `e i` and every loop at `i` into `J` to the vertex simple module
  `TauCeti.vertexSimpleModule k Q i`
  (`TauCeti.PathAlgebra.nonempty_restrictScalars_quotient_smul_top_iso_vertexSimpleModule`);
* the tops `Sᵢ` are pairwise non-isomorphic simple modules exhausting all simple left `A`-modules
  (`CompleteOrthogonalIdempotents.existsUnique_nonempty_linearEquiv_quotient_smul_top`);
* the number of arrows `i ⟶ j` equals `dimₖ Ext¹_A(Sᵢ, Sⱼ)`, identifying `Q` with the Ext-quiver
  of `A` (`CompleteOrthogonalIdempotents.exists_admissible_presentation`).

When `k` is algebraically closed and `A` is basic, the primitive block idempotents of `A ⧸ J` lift
to such a family `e` (`TauCeti.IsBasic.exists_completeOrthogonalIdempotents`), yielding Gabriel's
bound-quiver presentation with the Ext-quiver (`TauCeti.exists_admissible_presentation`).

## Main results

* `TauCeti.PathAlgebra.nonempty_restrictScalars_quotient_smul_top_iso_vertexSimpleModule`: for a
  complete orthogonal idempotent family `e : Q → A` spanning `A ⧸ J` over `k` and a `k`-algebra
  homomorphism `F : kQ →ₐ[k] A` sending `vertexIdempotent k i` to `e i` and every loop at `i`
  into `J`, restricting scalars of `A eᵢ / J (A eᵢ)` along `F` is isomorphic to
  `TauCeti.vertexSimpleModule k Q i`.
* `CompleteOrthogonalIdempotents.exists_admissible_presentation`: bound-quiver presentation with
  the Ext-quiver for a split basic finite-dimensional `k`-algebra given by `e : Q → A` over any
  field `k`.
* `TauCeti.exists_admissible_presentation`: **Gabriel's bound-quiver presentation with the
  Ext-quiver** for a basic finite-dimensional algebra over an algebraically closed field.

## References

* I. Assem, D. Simson, A. Skowroński, *Elements of the Representation Theory of Associative
  Algebras, Vol. 1*, Definition II.2.1, Theorem II.3.7, and Lemma III.2.12 (transposed to left
  modules).
* P. Gabriel, *Indecomposable representations II*, Symposia Mathematica XI (1973), 81--104.
-/

public section

namespace TauCeti

open CategoryTheory CategoryTheory.Abelian PathAlgebra
open scoped ModuleCat Pointwise

namespace PathAlgebra

universe v w

variable {Q : Type v} [Quiver.{w} Q] [Fintype Q]
  {k : Type (max v w)} [Field k] {A : Type (max v w)} [Ring A] [Algebra k A]

/-- **Restricting the simple top `A eᵢ / J (A eᵢ)` along a path-algebra map recovers the vertex
simple `Sᵢ`.** Whenever the classes of `e` span `A ⧸ J` over `k`, `e i ∉ J`, and `F : kQ →ₐ[k] A`
sends `vertexIdempotent k i` to `e i` and every loop at `i` into `J`, restricting scalars of
`A eᵢ / J (A eᵢ)` along `F` gives a `kQ`-module isomorphic to `TauCeti.vertexSimpleModule k Q i`. -/
theorem nonempty_restrictScalars_quotient_smul_top_iso_vertexSimpleModule
    (F : pathAlgebra k Q →ₐ[k] A) (e : Q → A) (he : CompleteOrthogonalIdempotents e)
    (J : Ideal A) [J.IsTwoSided]
    (hquot : Submodule.span k (Set.range fun j ↦ Ideal.Quotient.mk J (e j)) = ⊤)
    (i : Q) (hFi : F (vertexIdempotent k i) = e i)
    (hloops : ∀ a : i ⟶ i, F (ofArrow a) ∈ J) (hi : e i ∉ J) :
    Nonempty ((ModuleCat.restrictScalars F.toRingHom).obj
        (ModuleCat.of A ((Ideal.span {e i} : Ideal A) ⧸
          J • (⊤ : Submodule A (Ideal.span {e i} : Ideal A)))) ≅
      vertexSimpleModule k Q i) := by
  let S := ModuleCat.of A ((Ideal.span {e i} : Ideal A) ⧸
    J • (⊤ : Submodule A (Ideal.span {e i} : Ideal A)))
  let s₀ : S := Submodule.Quotient.mk (spanSingletonGenerator (e i))
  let x₀ : (ModuleCat.restrictScalars F.toRingHom).obj S := s₀
  have htor : Module.IsTorsionBySet A S J := Module.isTorsionBySet_quotient_ideal_smul _ J
  refine nonempty_iso_vertexSimpleModule_of_generator (i := i) x₀
    (mk_spanSingletonGenerator_ne_zero hi) ?_ ?_ ?_
  · rw [ModuleCat.restrictScalars.smul_def, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, hFi]
    exact he.smul_quotient_smul_top_eq_self hquot i s₀
  · intro y
    obtain ⟨c, hc⟩ := (he.equivQuotientSMulTop hquot i hi).surjective y
    refine ⟨c, ?_⟩
    rw [← algebraMap_smul (pathAlgebra k Q) c x₀, ModuleCat.restrictScalars.smul_def,
      AlgHom.toRingHom_eq_coe, RingHom.coe_coe, AlgHom.commutes]
    exact (algebraMap_smul A c s₀).trans
      ((he.equivQuotientSMulTop_apply hquot i hi c).symm.trans hc)
  · intro a
    rw [ModuleCat.restrictScalars.smul_def, AlgHom.toRingHom_eq_coe, RingHom.coe_coe]
    exact @htor s₀ ⟨F (ofArrow a), hloops a⟩

end PathAlgebra

universe u

/-- **Bound-quiver presentation with the Ext-quiver for a split basic finite-dimensional algebra.**
Given a finite-dimensional `k`-algebra `A` over an arbitrary field `k` and a complete family of
nonzero orthogonal idempotents `e : Q → A` whose classes span `A ⧸ J` over `k`, there are a finite
quiver structure on `Q` and a surjective `k`-algebra homomorphism `f : kQ →ₐ[k] A` with admissible
kernel sending each vertex idempotent to `e i`, under which each projective top
`Sᵢ = A eᵢ / J (A eᵢ)` restricts along `f` to `TauCeti.vertexSimpleModule k Q i` and the arrow
counts satisfy `card (i ⟶ j) = dimₖ Ext¹_A(Sᵢ, Sⱼ)`. -/
theorem _root_.CompleteOrthogonalIdempotents.exists_admissible_presentation
    {k A : Type u} [Field k] [Ring A] [Algebra k A] [FiniteDimensional k A]
    {Q : Type u} [Fintype Q] {e : Q → A} (he : CompleteOrthogonalIdempotents e)
    (hne : ∀ i, e i ≠ 0)
    (hquot : Submodule.span k (Set.range fun i ↦ Ideal.Quotient.mk (Ring.jacobson A) (e i)) = ⊤) :
    ∃ (_ : Quiver.{u} Q) (_ : ∀ i j : Q, Fintype (i ⟶ j)) (f : pathAlgebra k Q →ₐ[k] A),
      Function.Surjective f ∧ IsAdmissibleIdeal (RingHom.ker f) ∧
      (∀ i, f (vertexIdempotent k i) = e i) ∧
      (∀ i, Nonempty ((ModuleCat.restrictScalars f.toRingHom).obj
        (ModuleCat.of A ((Ideal.span {e i} : Ideal A) ⧸
          Ring.jacobson A • (⊤ : Submodule A (Ideal.span {e i} : Ideal A)))) ≅
        vertexSimpleModule k Q i)) ∧
      (∀ i j, Fintype.card (i ⟶ j) = Module.finrank k
        (Ext (ModuleCat.of A ((Ideal.span {e i} : Ideal A) ⧸
            Ring.jacobson A • (⊤ : Submodule A (Ideal.span {e i} : Ideal A))))
          (ModuleCat.of A ((Ideal.span {e j} : Ideal A) ⧸
            Ring.jacobson A • (⊤ : Submodule A (Ideal.span {e j} : Ideal A)))) 1)) := by
  obtain ⟨hQ, harr, f, hsurj, hadm, hvert, harrow, hcard⟩ :=
    he.exists_surjective_pathAlgebra_isAdmissibleIdeal_ker hne hquot
  refine ⟨hQ, harr, f, hsurj, hadm, hvert, fun i ↦ ?_, fun i j ↦ ?_⟩
  · exact nonempty_restrictScalars_quotient_smul_top_iso_vertexSimpleModule f e he
      (Ring.jacobson A) hquot i (hvert i) (fun a ↦ harrow a)
      ((he.idem i).mem_jacobson_iff.not.mpr (hne i))
  · exact (hcard i j).trans (he.finrank_ext_quotient_smul_top hquot i j (hne j)).symm

/-- **Gabriel's bound-quiver presentation with the Ext-quiver.** A basic finite-dimensional algebra
`A` over an algebraically closed field `k` admits a finite quiver `Q`, a surjective `k`-algebra
homomorphism `f : kQ →ₐ[k] A` with admissible kernel, and a family `S : Q → ModuleCat A` of simple
modules exhausting the simple left `A`-modules without repetition, restricting along `f` to the
vertex simple `kQ`-modules, and satisfying `card (i ⟶ j) = dimₖ Ext¹_A(Sᵢ, Sⱼ)`. -/
theorem exists_admissible_presentation (k A : Type u) [Field k] [IsAlgClosed k] [Ring A]
    [Algebra k A] [FiniteDimensional k A] (hA : IsBasic A) :
    ∃ (Q : Type u) (_ : Quiver Q) (_ : Fintype Q) (_ : ∀ i j : Q, Fintype (i ⟶ j))
      (f : pathAlgebra k Q →ₐ[k] A) (S : Q → ModuleCat.{u} A),
      Function.Surjective f ∧ IsAdmissibleIdeal (RingHom.ker f) ∧
      (∀ i, Simple (S i)) ∧
      (∀ X : ModuleCat.{u} A, Simple X → ∃! i, Nonempty (S i ≅ X)) ∧
      (∀ i, Nonempty ((ModuleCat.restrictScalars f.toRingHom).obj (S i) ≅
        vertexSimpleModule k Q i)) ∧
      (∀ i j, Fintype.card (i ⟶ j) = Module.finrank k (Ext (S i) (S j) 1)) := by
  obtain ⟨n, e₀, he₀, hne₀, hquot₀⟩ := hA.exists_completeOrthogonalIdempotents (k := k)
  let Q : Type u := ULift.{u} (Fin n)
  let e : Q → A := e₀ ∘ Equiv.ulift
  have he : CompleteOrthogonalIdempotents e :=
    (CompleteOrthogonalIdempotents.equiv Equiv.ulift).mpr he₀
  have hne (i : Q) : e i ≠ 0 := hne₀ i.down
  have hquot : Submodule.span k
      (Set.range fun i ↦ Ideal.Quotient.mk (Ring.jacobson A) (e i)) = ⊤ := by
    have hcomp : (fun i ↦ Ideal.Quotient.mk (Ring.jacobson A) (e i)) =
        (fun i ↦ Ideal.Quotient.mk (Ring.jacobson A) (e₀ i)) ∘ Equiv.ulift := rfl
    rwa [hcomp, Equiv.ulift.surjective.range_comp]
  obtain ⟨hQ, harr, f, hsurj, hadm, -, hres, hext⟩ := he.exists_admissible_presentation hne hquot
  let S (i : Q) : ModuleCat.{u} A := ModuleCat.of A ((Ideal.span {e i} : Ideal A) ⧸
    Ring.jacobson A • (⊤ : Submodule A (Ideal.span {e i} : Ideal A)))
  refine ⟨Q, hQ, inferInstance, harr, f, S, hsurj, hadm, ?_, ?_, hres, hext⟩
  · exact fun i ↦ (simple_iff_isSimpleModule' (S i)).mpr
      (he.isSimpleModule_quotient_smul_top hquot i ((he.idem i).mem_jacobson_iff.not.mpr (hne i)))
  · intro X hX
    have : IsSimpleModule A X := (simple_iff_isSimpleModule' X).mp hX
    obtain ⟨i, ⟨φ⟩, huniq⟩ := he.existsUnique_nonempty_linearEquiv_quotient_smul_top hquot X
      fun m ⟨r, hr⟩ ↦
        Module.mem_annihilator.mp (IsSemisimpleModule.jacobson_le_annihilator A X hr) m
    exact ⟨i, ⟨φ.toModuleIso⟩, fun j ⟨ψ⟩ ↦ huniq j ⟨ψ.toLinearEquiv⟩⟩

end TauCeti
