/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Etale.Kaehler
import TauCeti.RingTheory.Ideal.TensorProduct

/-!
# Injectivity of conormal maps through flat lifts

Let `P` present an `R`-algebra `A` as `R[X] ⧸ I`, and let `Q` present an `A`-algebra `B` as
`A[Y] ⧸ K`. The composite presentation `R[X, Y] → B` has conormal module `J / J²`, and
Jacobi–Zariski gives the exact sequence `B ⊗[A] I/I² → J/J² → K/K² → 0`
(`Algebra.Generators.Cotangent.exact`). This file shows that the first map is injective whenever
`B` lifts to a flat `R[X]`-algebra `C` with `C ⧸ I C ≅ B`
(`Algebra.Generators.liftBaseChange_injective_of_flat_lift`).

The proof goes through Mathlib's `Algebra.Extension.tensorCotangent`. For a map of extensions
`P → E`, with `E` an extension of `B` with kernel `J'`, it identifies `B ⊗[A] I/I²` with `J'/J'²`
provided the canonical map `E.Ring ⊗[P.Ring] I → J'` is bijective. Equality `J' = I E.Ring` with
the extended ideal only makes this map surjective; if moreover `E.Ring` is flat over `P.Ring`, it
is bijective (`Algebra.Extension.Hom.liftBaseChange_mapKer_bijective_of_flat_of_ker_eq_map`). If
the map of extensions into `E` factors through another extension `P'` of `B`, then
`B ⊗[A] I/I² → P'.Cotangent` is injective
(`Algebra.Extension.Hom.liftBaseChange_injective_of_bijective_liftBaseChange_mapKer_of_comp_eq`);
for the flat lift `C → B`, take `P'` to be the composite presentation.

## Main results

* `Algebra.Extension.tensorCotangent_apply`, `Algebra.Extension.tensorCotangent_tmul`: the forward
  map of Mathlib's `tensorCotangent`.
* `Algebra.Extension.Hom.liftBaseChange_mapKer_bijective_of_flat_of_ker_eq_map`: flat extension
  morphisms with extended kernel identify `E.Ring ⊗ I` with the kernel of `E`.
* `Algebra.Extension.Hom.liftBaseChange_injective_of_bijective_liftBaseChange_mapKer_of_comp_eq`:
  conormal maps through a factorization of such a morphism are injective after base change.
* `Algebra.Generators.liftBaseChange_injective_of_flat_lift`: the case of a composite
  presentation and a flat lift.

## References

* [Stacks Project, Tag 00S2](https://stacks.math.columbia.edu/tag/00S2): the Jacobi–Zariski
  sequence of naive cotangent complexes.
-/

public section

open TensorProduct MvPolynomial

namespace Algebra.Extension

universe w w'

variable {R A B : Type*} [CommRing R] [CommRing A] [CommRing B] [Algebra R A] [Algebra R B]
  [Algebra A B] {P : Extension.{w} R A} {P' : Extension R B} {E : Extension.{w} R B}

attribute [local instance] SMulCommClass.of_commMonoid

/-- The forward map of `Algebra.Extension.tensorCotangent` is the base change of the induced map
of conormal modules. -/
theorem tensorCotangent_apply (f : P.Hom E) [Algebra P.Ring E.Ring]
    (halg : algebraMap P.Ring E.Ring = f.toRingHom)
    (H : Function.Bijective ((f.mapKer halg).liftBaseChange E.Ring)) (x : B ⊗[A] P.Cotangent) :
    tensorCotangent f halg H x = (Cotangent.map f).liftBaseChange B x :=
  rfl

/-- The forward map of `Algebra.Extension.tensorCotangent` on a pure tensor. -/
@[simp]
theorem tensorCotangent_tmul (f : P.Hom E) [Algebra P.Ring E.Ring]
    (halg : algebraMap P.Ring E.Ring = f.toRingHom)
    (H : Function.Bijective ((f.mapKer halg).liftBaseChange E.Ring)) (b : B) (x : P.Cotangent) :
    tensorCotangent f halg H (b ⊗ₜ x) = b • Cotangent.map f x :=
  LinearMap.liftBaseChange_tmul _ _ _ _

omit [Algebra R B] in
/-- For a map of extensions `f : P → E` whose ring map is flat and whose target kernel `J'` is the
extension `I E.Ring` of the kernel `I` of `P`, the map `E.Ring ⊗[P.Ring] I → J'` is bijective. -/
theorem Hom.liftBaseChange_mapKer_bijective_of_flat_of_ker_eq_map
    {R' : Type*} [CommRing R'] [Algebra R' B] [Algebra R R']
    {E : Extension.{w'} R' B} (f : P.Hom E)
    [Algebra P.Ring E.Ring] [Module.Flat P.Ring E.Ring]
    (halg : algebraMap P.Ring E.Ring = f.toRingHom)
    (hker : E.ker = P.ker.map (algebraMap P.Ring E.Ring)) :
    Function.Bijective ((f.mapKer halg).liftBaseChange E.Ring) := by
  -- `f.mapKer` is `I → I E.Ring` followed by the identification `I E.Ring = E.ker`.
  have h : f.mapKer halg = ((LinearEquiv.ofEq _ _ hker.symm).toLinearMap.restrictScalars P.Ring)
      ∘ₗ Algebra.idealMap E.Ring P.ker := by
    ext x
    simp [halg]
  rw [h, ← LinearMap.comp_liftBaseChange, LinearMap.coe_comp]
  exact (LinearEquiv.bijective _).comp (Ideal.liftBaseChange_idealMap_bijective E.Ring P.ker)

/-- Let `f : P → E` be a map of extensions such that `E.Ring ⊗[P.Ring] I → J'` is bijective, so
that `B ⊗[A] I/I² ≅ J'/J'²` (`Algebra.Extension.tensorCotangent`). If `f` factors through an
extension `P'` of `B`, then the induced map `B ⊗[A] I/I² → P'.Cotangent` is injective. -/
theorem Hom.liftBaseChange_injective_of_bijective_liftBaseChange_mapKer_of_comp_eq
    (h : P.Hom P') (f : P.Hom E)
    [Algebra P.Ring E.Ring] (halg : algebraMap P.Ring E.Ring = f.toRingHom)
    (H : Function.Bijective ((f.mapKer halg).liftBaseChange E.Ring))
    (g : P'.Hom E) (hgf : g.comp h = f) :
    Function.Injective ((Cotangent.map h).liftBaseChange B) := by
  -- Composing with the map induced by `g` gives Mathlib's isomorphism `tensorCotangent`.
  refine Function.Injective.of_comp (f := Cotangent.map g) ?_
  rw [← LinearMap.coe_comp, LinearMap.comp_liftBaseChange, ← Cotangent.map_comp, hgf]
  exact fun x y hxy ↦ (tensorCotangent f halg H).injective <| by
    rwa [tensorCotangent_apply, tensorCotangent_apply]

end Algebra.Extension

namespace Algebra.Generators

universe u v

variable {R : Type u} {A B : Type*} [CommRing R] [CommRing A] [CommRing B] [Algebra R A]
  [Algebra R B] [Algebra A B] [IsScalarTower R A B] {ι : Type v} {ι' : Type*}
  (Q : Generators A B ι') (P : Generators R A ι)

/-- Suppose that `B` has a flat lift `C` over the polynomial ring `R[X]` of `P`: there is a
surjection `C → B`, compatible with `R[X] → A → B`, whose kernel is `I C` for the kernel `I` of
`R[X] → A`. Then `B ⊗[A] I/I² → J/J²` is injective, where `J` is the kernel of the composite
presentation `R[X, Y] → B`. -/
theorem liftBaseChange_injective_of_flat_lift {C : Type (max u v)} [CommRing C]
    [Algebra P.Ring C] [Module.Flat P.Ring C] (φ : C →+* B) (hφ : Function.Surjective φ)
    (hφalg : ∀ x, φ (algebraMap P.Ring C x) = algebraMap A B (algebraMap P.Ring A x))
    (hker : RingHom.ker φ = P.ker.map (algebraMap P.Ring C)) :
    Function.Injective
      ((Extension.Cotangent.map (Q.toComp P).toExtensionHom).liftBaseChange B) := by
  classical
  let : Algebra R C := ((algebraMap P.Ring C).comp (algebraMap R P.Ring)).toAlgebra
  have : IsScalarTower R P.Ring C := .of_algebraMap_eq' rfl
  let φ' : C →ₐ[R] B :=
    { φ with
      commutes' r := by
        rw [RingHom.toFun_eq_coe, IsScalarTower.algebraMap_apply R P.Ring C, hφalg,
          ← IsScalarTower.algebraMap_apply R P.Ring A, ← IsScalarTower.algebraMap_apply R A B] }
  -- The extension `C → B` of `B`, receiving maps from `R[X] → A` and from `R[X, Y] → B`.
  let E := Extension.ofSurjective φ' hφ
  let f : P.toExtension.Hom E :=
    Extension.Hom.ofAlgHom (IsScalarTower.toAlgHom R P.Ring C) (by ext x; exact hφalg x)
  let v : ι' ⊕ ι → C := Sum.elim (fun i ↦ (hφ (Q.val i)).choose) fun j ↦ algebraMap P.Ring C (X j)
  have hv : φ'.comp (aeval v) = aeval (Q.comp P).val := by
    refine MvPolynomial.algHom_ext fun i ↦ ?_
    rcases i with i | j
    · simp only [AlgHom.comp_apply, aeval_X, Sum.elim_inl, comp, v]
      exact (hφ (Q.val i)).choose_spec
    · simp [φ', hφalg, comp, v]
  let g : (Q.comp P).toExtension.Hom E :=
    Extension.Hom.ofAlgHom (aeval (R := R) v) hv
  let : Algebra P.toExtension.Ring E.Ring := ‹Algebra P.Ring C›
  have halg : algebraMap P.toExtension.Ring E.Ring = f.toRingHom := rfl
  have : Module.Flat P.toExtension.Ring E.Ring := ‹Module.Flat P.Ring C›
  have hgf : g.comp (Q.toComp P).toExtensionHom = f := by
    have key : (aeval v).comp (rename Sum.inr) = IsScalarTower.toAlgHom R P.Ring C :=
      MvPolynomial.algHom_ext fun j ↦ by simp [v]
    ext1
    simp only [Extension.Hom.comp_toRingHom, Hom.toExtensionHom_toRingHom, toComp_toAlgHom, g, f]
    exact congrArg AlgHom.toRingHom key
  exact Extension.Hom.liftBaseChange_injective_of_bijective_liftBaseChange_mapKer_of_comp_eq
    (Q.toComp P).toExtensionHom f halg
    (f.liftBaseChange_mapKer_bijective_of_flat_of_ker_eq_map halg hker) g hgf

end Algebra.Generators
