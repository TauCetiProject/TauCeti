/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Etale.StandardEtale
public import Mathlib.RingTheory.Smooth.StandardSmoothCotangent
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.TensorProduct.Prod
import Mathlib.RingTheory.Etale.Kaehler
import TauCeti.RingTheory.Etale.StandardEtaleQuotient
import TauCeti.RingTheory.Ideal.TensorProduct

/-!
# Conormal modules of presentations through a standard étale algebra

Let `P` present an `R`-algebra `A` as `R[X] ⧸ I`, and let `Q` present an `A`-algebra `B` as
`A[Y] ⧸ K`. The composite presentation `R[X, Y] → B` has conormal module `J / J²`, and
Jacobi–Zariski gives the exact sequence `B ⊗[A] I/I² → J/J² → K/K² → 0`
(`Algebra.Generators.Cotangent.exact`). When `B` is a standard étale `A`-algebra the first map is
injective (`Algebra.Generators.liftBaseChange_injective_of_isStandardEtale`).
If moreover `K/K²` is projective, for instance for a submersive presentation `Q`, the sequence
splits: `J/J² ≃ B ⊗[A] I/I² × K/K²`
(`Algebra.Generators.cotangentCompEquivOfIsStandardEtale`). In particular the fibres of the
conormal modules at a field-valued point of `B` satisfy
`dim F ⊗[B] J/J² = dim F ⊗[A] I/I² + #relations of Q`
(`Algebra.Generators.finrank_tensor_cotangent_comp_of_isStandardEtale`). Thus the number of
equations needed to cut out `B` near a point exceeds the number needed for `A` near its image by
exactly the number of new variables: complete intersections can be detected on étale
neighbourhoods.

Injectivity is the base change of a flatness statement. It holds whenever `B` lifts to a flat
`R[X]`-algebra `C` with `C ⧸ I C ≅ B`
(`Algebra.Generators.liftBaseChange_injective_of_flat`): Mathlib's
`Algebra.Extension.tensorCotangent` then identifies `B ⊗[A] I/I²` with the conormal module of
`C → B`, and that identification factors through `J/J²`. Standard étale algebras lift in this way
(`Algebra.IsStandardEtale.exists_flat_lift`).

## References

* [Stacks Project, Tag 00S2](https://stacks.math.columbia.edu/tag/00S2): the Jacobi–Zariski
  sequence of naive cotangent complexes.
* [Stacks Project, Section 10.135, Tag 00S8](https://stacks.math.columbia.edu/tag/00S8): local
  complete intersections.
-/

public section

open TensorProduct MvPolynomial

namespace Algebra.Generators

universe u v

variable {R : Type u} {A B : Type*} [CommRing R] [CommRing A] [CommRing B] [Algebra R A]
  [Algebra R B] [Algebra A B] [IsScalarTower R A B] {ι : Type v} {ι' : Type*}
  (Q : Generators A B ι') (P : Generators R A ι)

attribute [local instance] SMulCommClass.of_commMonoid

/-- Let `f` be a map of extensions from `R[X] → A` to an extension `E` of `B` with kernel `J'`, such
that `E.Ring ⊗[R[X]] I → J'` is bijective, so that `B ⊗[A] I/I² ≅ J'/J'²`. If `f` factors through
the composite presentation `R[X, Y] → B`, then `B ⊗[A] I/I² → J/J²` is injective. -/
private theorem liftBaseChange_injective_of_comp_eq {E : Extension.{max u v} R B}
    (f : P.toExtension.Hom E) [Algebra P.toExtension.Ring E.Ring]
    (halg : algebraMap P.toExtension.Ring E.Ring = f.toRingHom)
    (H : Function.Bijective ((f.mapKer halg).liftBaseChange E.Ring))
    (g : (Q.comp P).toExtension.Hom E) (hgf : g.comp (Q.toComp P).toExtensionHom = f) :
    Function.Injective
      ((Extension.Cotangent.map (Q.toComp P).toExtensionHom).liftBaseChange B) := by
  -- Composing with the map induced by `g` gives Mathlib's isomorphism `tensorCotangent`.
  intro x y hxy
  apply (Extension.tensorCotangent f halg H).injective
  change (Extension.Cotangent.map f).liftBaseChange B x =
    (Extension.Cotangent.map f).liftBaseChange B y
  rw [← hgf, Extension.Cotangent.map_comp, ← LinearMap.comp_liftBaseChange]
  simp only [LinearMap.comp_apply, hxy]

omit [IsScalarTower R A B] in
/-- For an extension `E` of `B` whose ring is flat over `R[X]`, with kernel `J' = I E.Ring`, the
map `E.Ring ⊗[R[X]] I → J'` is bijective. -/
private theorem bijective_liftBaseChange_mapKer_of_flat {E : Extension.{max u v} R B}
    (f : P.toExtension.Hom E) [Algebra P.toExtension.Ring E.Ring]
    [Module.Flat P.toExtension.Ring E.Ring]
    (halg : algebraMap P.toExtension.Ring E.Ring = f.toRingHom)
    (hker : E.ker = P.toExtension.ker.map (algebraMap P.toExtension.Ring E.Ring)) :
    Function.Bijective ((f.mapKer halg).liftBaseChange E.Ring) := by
  have hbij := Ideal.liftBaseChange_idealMap_bijective E.Ring P.toExtension.ker
  have key : ∀ z, ((f.mapKer halg).liftBaseChange E.Ring z).val =
      ((Algebra.idealMap E.Ring P.toExtension.ker).liftBaseChange E.Ring z).val := by
    intro z
    induction z using TensorProduct.inductionOn with
    | tmul c x => simp [halg]
    | add z w hz hw => simp only [map_add, Submodule.coe_add, hz, hw]
  refine ⟨fun z w hzw ↦ hbij.1 (Subtype.ext ((key z).symm.trans
    ((congrArg Subtype.val hzw).trans (key w)))), fun y ↦ ?_⟩
  obtain ⟨z, hz⟩ := hbij.2 ⟨y.val, hker ▸ y.property⟩
  exact ⟨z, Subtype.ext ((key z).trans congr(($hz).val))⟩

/-- Suppose that `B` lifts to a flat algebra `C` over the polynomial ring `R[X]` of `P`: there is a
surjection `C → B`, compatible with `R[X] → A → B`, whose kernel is `I C` for the kernel `I` of
`R[X] → A`. Then `B ⊗[A] I/I² → J/J²` is injective, where `J` is the kernel of the composite
presentation `R[X, Y] → B`. -/
theorem liftBaseChange_injective_of_flat {C : Type (max u v)} [CommRing C]
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
        change φ (algebraMap P.Ring C (algebraMap R P.Ring r)) = _
        rw [hφalg, ← IsScalarTower.algebraMap_apply R P.Ring A,
          ← IsScalarTower.algebraMap_apply R A B] }
  -- The extension `C → B` of `B`, receiving maps from `R[X] → A` and from `R[X, Y] → B`.
  let E := Extension.ofSurjective φ' hφ
  let f : P.toExtension.Hom E :=
    { toRingHom := algebraMap P.Ring C
      toRingHom_algebraMap _ := rfl
      algebraMap_toRingHom x := hφalg x }
  let v : ι' ⊕ ι → C := Sum.elim (fun i ↦ (hφ (Q.val i)).choose) fun j ↦ algebraMap P.Ring C (X j)
  have hv : φ'.comp (aeval v) = aeval (Q.comp P).val := by
    refine MvPolynomial.algHom_ext fun i ↦ ?_
    rcases i with i | j
    · simp only [AlgHom.comp_apply, aeval_X, Sum.elim_inl, comp, v]
      exact (hφ (Q.val i)).choose_spec
    · simp [φ', hφalg, comp, v]
  let g : (Q.comp P).toExtension.Hom E :=
    { toRingHom := (aeval (R := R) v).toRingHom
      toRingHom_algebraMap x := (aeval _).commutes x
      algebraMap_toRingHom x := (congr($hv x)).trans (Generators.algebraMap_apply _ x).symm }
  let : Algebra P.toExtension.Ring E.Ring := ‹Algebra P.Ring C›
  have halg : algebraMap P.toExtension.Ring E.Ring = f.toRingHom := rfl
  have : Module.Flat P.toExtension.Ring E.Ring := ‹Module.Flat P.Ring C›
  have H := bijective_liftBaseChange_mapKer_of_flat P f halg hker
  have hgf : g.comp (Q.toComp P).toExtensionHom = f := by
    have key : (aeval v).comp (rename Sum.inr) = IsScalarTower.toAlgHom R P.Ring C :=
      MvPolynomial.algHom_ext fun j ↦ by simp [v]
    ext1
    simp only [Extension.Hom.comp_toRingHom, Hom.toExtensionHom_toRingHom, toComp_toAlgHom, g, f]
    exact congrArg AlgHom.toRingHom key
  exact liftBaseChange_injective_of_comp_eq Q P f halg H g hgf

/-- For a standard étale `A`-algebra `B`, the map `B ⊗[A] I/I² → J/J²` from the conormal module of
a presentation of `A` to that of the composite presentation `R[X, Y] → B` is injective. -/
theorem liftBaseChange_injective_of_isStandardEtale
    [Algebra.IsStandardEtale A B] :
    Function.Injective
      ((Extension.Cotangent.map (Q.toComp P).toExtensionHom).liftBaseChange B) := by
  obtain ⟨C, _, _, _, φ, hφ, hφalg, hker⟩ :=
    Algebra.IsStandardEtale.exists_flat_lift (S := P.Ring) (B := B) P.algebraMap_surjective
  exact liftBaseChange_injective_of_flat Q P φ hφ hφalg hker

/-- For a standard étale `A`-algebra `B` presented by `Q` with projective conormal module `K/K²`,
the conormal module `J/J²` of the composite presentation `R[X, Y] → B` splits as
`B ⊗[A] I/I² × K/K²`. -/
noncomputable def cotangentCompEquivOfIsStandardEtale [Algebra.IsStandardEtale A B]
    [Module.Projective B Q.toExtension.Cotangent] :
    (Q.comp P).toExtension.Cotangent ≃ₗ[B]
      B ⊗[A] P.toExtension.Cotangent × Q.toExtension.Cotangent :=
  ((Cotangent.exact Q P).splitSurjectiveEquiv
    (liftBaseChange_injective_of_isStandardEtale Q P)
    ⟨_, (Module.projective_lifting_property _ LinearMap.id
      (Cotangent.surjective_map_ofComp Q P)).choose_spec⟩).val

variable [Algebra.IsStandardEtale A B] [Module.Projective B Q.toExtension.Cotangent]

/-- The splitting restricts to `B ⊗[A] I/I² → J/J²` on the first factor. -/
@[simp]
lemma cotangentCompEquivOfIsStandardEtale_symm_inl (a : B ⊗[A] P.toExtension.Cotangent) :
    (cotangentCompEquivOfIsStandardEtale Q P).symm (a, 0) =
      LinearMap.liftBaseChange B (Extension.Cotangent.map (Q.toComp P).toExtensionHom) a := by
  rw [((Cotangent.exact Q P).splitSurjectiveEquiv
    (liftBaseChange_injective_of_isStandardEtale Q P)
    ⟨_, (Module.projective_lifting_property _ LinearMap.id
      (Cotangent.surjective_map_ofComp Q P)).choose_spec⟩).property.1]
  rfl

/-- The second component of the splitting is the projection `J/J² → K/K²`. -/
@[simp]
lemma snd_cotangentCompEquivOfIsStandardEtale (a : (Q.comp P).toExtension.Cotangent) :
    (cotangentCompEquivOfIsStandardEtale Q P a).2 =
      Extension.Cotangent.map (Q.ofComp P).toExtensionHom a := by
  rw [((Cotangent.exact Q P).splitSurjectiveEquiv
    (liftBaseChange_injective_of_isStandardEtale Q P)
    ⟨_, (Module.projective_lifting_property _ LinearMap.id
      (Cotangent.surjective_map_ofComp Q P)).choose_spec⟩).property.2]
  rfl

omit [Module.Projective B Q.toExtension.Cotangent] in
/-- Through a standard étale `A`-algebra `B` with a submersive presentation `Q`, the fibre at a
field-valued point of `B` of the conormal module of the composite presentation `R[X, Y] → B` has
dimension the dimension of the fibre of the conormal module of `P`, plus the number of relations
of `Q`. -/
theorem finrank_tensor_cotangent_comp_of_isStandardEtale {σ : Type*} [Finite σ]
    (Q : SubmersivePresentation A B ι' σ) (F : Type*) [Field F] [Algebra A F] [Algebra B F]
    [IsScalarTower A B F] [Module.Finite A P.toExtension.Cotangent] :
    Module.finrank F (F ⊗[B] (Q.toGenerators.comp P).toExtension.Cotangent) =
      Module.finrank F (F ⊗[A] P.toExtension.Cotangent) + Nat.card σ := by
  have : Nontrivial B := (algebraMap B F).domain_nontrivial
  have := Fintype.ofFinite σ
  have : Module.Finite B Q.toExtension.Cotangent := .of_basis Q.basisCotangent
  rw [((cotangentCompEquivOfIsStandardEtale Q.toGenerators P).baseChange B F _ _).finrank_eq,
    (_root_.TensorProduct.prodRight B F F _ _).finrank_eq, Module.finrank_prod,
    (AlgebraTensorModule.cancelBaseChange A B F F _).finrank_eq,
    (Q.cotangentEquiv.baseChange B F _ _).finrank_eq,
    Module.finrank_baseChange (R := F) (M' := σ → B), Module.finrank_fintype_fun_eq_card,
    Nat.card_eq_fintype_card]

end Algebra.Generators
