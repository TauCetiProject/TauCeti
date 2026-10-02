/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.LinearAlgebra.TensorProduct.RightExactness
public import Mathlib.RepresentationTheory.Rep.Basic
public import Mathlib.RingTheory.Flat.Basic

/-!
# Tensoring a short exact sequence of representations

Tensoring with a fixed representation `M` is right exact, but not exact in general. This file
records that a short exact sequence of representations which is split as a sequence of
`k`-modules stays short exact after tensoring on the left with `M`: the `k`-linear retraction of
the first map survives tensoring and keeps the tensored first map injective, while right
exactness of the tensor product supplies exactness and the surjectivity of the last map. The
dimension-shifting sequences through the modules induced and coinduced from the trivial subgroup
are of this kind. Tensoring with a representation whose underlying module is flat over `k`
preserves every short exact sequence.

## Main statements

* `Rep.exact_iff_function_exact`: a short complex of representations is exact if and only if the
  underlying linear maps form an exact pair.
* `Rep.exists_leftInverse_of_rightInverse`, `Rep.exists_rightInverse_of_leftInverse`: a short
  exact sequence of representations has a `k`-linear retraction of its first map exactly when it
  has a `k`-linear section of its last map.
* `Rep.shortExact_map_tensorLeft_of_injective`: tensoring on the left preserves a short exact
  sequence as soon as the tensored first map stays injective.
* `Rep.shortExact_map_tensorLeft_of_flat`: tensoring on the left with a representation whose
  underlying module is flat preserves every short exact sequence.
* `Rep.leftInverse_whiskerLeft`: tensoring on the left keeps a `k`-linear retraction.
* `Rep.shortExact_map_tensorLeft_of_leftInverse`,
  `Rep.shortExact_map_tensorLeft_of_rightInverse`: tensoring on the left preserves a short exact
  sequence whose first map has a `k`-linear retraction, or whose last map has a `k`-linear
  section.
-/

public section

universe u v w

open CategoryTheory MonoidalCategory

namespace Rep

variable {k : Type u} {G : Type v} [Monoid G]

section Ring

variable [Ring k]

/-- A short complex of representations is exact if and only if the underlying linear maps form an
exact pair. -/
theorem exact_iff_function_exact (S : ShortComplex (Rep.{w} k G)) :
    S.Exact ↔ Function.Exact S.f.hom S.g.hom := by
  rw [← ShortComplex.exact_map_iff_of_faithful S (forget₂ (Rep.{w} k G) (ModuleCat.{w} k)),
    ShortComplex.ShortExact.moduleCat_exact_iff_function_exact]
  rfl

/-- In a short exact sequence of representations, a `k`-linear section of the last map gives a
`k`-linear retraction of the first map. -/
theorem exists_leftInverse_of_rightInverse {S : ShortComplex (Rep.{w} k G)} (hS : S.Exact)
    [Mono S.f] {s : S.X₃.V →ₗ[k] S.X₂.V} (hs : Function.RightInverse s S.g.hom) :
    ∃ r : S.X₂.V →ₗ[k] S.X₁.V, Function.LeftInverse r S.f.hom := by
  have tfae := ((exact_iff_function_exact S).1 hS).split_tfae
    ((mono_iff_injective S.f).1 inferInstance) hs.surjective
  have key : (∃ l, S.g.hom.toLinearMap ∘ₗ l = LinearMap.id) ↔
      ∃ l, l ∘ₗ S.f.hom.toLinearMap = LinearMap.id := tfae.out 1 2
  obtain ⟨r, hr⟩ := key.1 ⟨s, LinearMap.ext hs⟩
  exact ⟨r, LinearMap.congr_fun hr⟩

/-- In a short exact sequence of representations, a `k`-linear retraction of the first map gives
a `k`-linear section of the last map. -/
theorem exists_rightInverse_of_leftInverse {S : ShortComplex (Rep.{w} k G)} (hS : S.Exact)
    [Epi S.g] {r : S.X₂.V →ₗ[k] S.X₁.V} (hr : Function.LeftInverse r S.f.hom) :
    ∃ s : S.X₃.V →ₗ[k] S.X₂.V, Function.RightInverse s S.g.hom := by
  have tfae := ((exact_iff_function_exact S).1 hS).split_tfae hr.injective
    ((epi_iff_surjective S.g).1 inferInstance)
  have key : (∃ l, S.g.hom.toLinearMap ∘ₗ l = LinearMap.id) ↔
      ∃ l, l ∘ₗ S.f.hom.toLinearMap = LinearMap.id := tfae.out 1 2
  obtain ⟨s, hs⟩ := key.2 ⟨r, LinearMap.ext hr⟩
  exact ⟨s, LinearMap.congr_fun hs⟩

end Ring

variable [CommRing k]

/-- Tensoring on the left with `M` sends an exact sequence ending in an epimorphism to a
short exact sequence when the tensored first map is injective. -/
theorem shortExact_map_tensorLeft_of_injective {S : ShortComplex (Rep.{u} k G)}
    (hS : S.Exact) [Epi S.g]
    (M : Rep k G) (hf : Function.Injective (LinearMap.lTensor M.V S.f.hom.toLinearMap)) :
    (S.map (tensorLeft M)).ShortExact where
  exact := (exact_iff_function_exact _).2 <| lTensor_exact M.V
    ((exact_iff_function_exact S).1 hS) ((epi_iff_surjective S.g).1 inferInstance)
  mono_f := (mono_iff_injective _).2 hf
  epi_g := (epi_iff_surjective _).2 <|
    LinearMap.lTensor_surjective M.V ((epi_iff_surjective S.g).1 inferInstance)

/-- Tensoring on the left with a representation whose underlying module is flat over `k` preserves
short exact sequences. -/
theorem shortExact_map_tensorLeft_of_flat {S : ShortComplex (Rep.{u} k G)} (hS : S.ShortExact)
    (M : Rep k G) [Module.Flat k M.V] : (S.map (tensorLeft M)).ShortExact :=
  have := hS.epi_g
  shortExact_map_tensorLeft_of_injective hS.exact M <|
    Module.Flat.lTensor_preserves_injective_linearMap _ ((mono_iff_injective S.f).1 hS.mono_f)

/-- Tensoring on the left with `M` keeps a `k`-linear retraction `r` of a morphism of
representations: `M ⊗ r` is a retraction of `M ◁ f`. -/
theorem leftInverse_whiskerLeft (M : Rep k G) {A B : Rep.{u} k G} (f : A ⟶ B)
    {r : B.V →ₗ[k] A.V} (hr : Function.LeftInverse r f.hom) :
    Function.LeftInverse (LinearMap.lTensor M.V r) (M ◁ f).hom := fun x ↦ by
  have h : r ∘ₗ f.hom.toLinearMap = LinearMap.id := LinearMap.ext hr
  rw [hom_whiskerLeft, ← Representation.IntertwiningMap.toLinearMap_apply,
    Representation.IntertwiningMap.toLinearMap_lTensor, ← LinearMap.lTensor_comp_apply, h,
    LinearMap.lTensor_id, LinearMap.id_apply]

/-- Tensoring on the left with `M` sends an exact sequence ending in an epimorphism to a
short exact sequence if the first map has a `k`-linear retraction. -/
theorem shortExact_map_tensorLeft_of_leftInverse {S : ShortComplex (Rep.{u} k G)}
    (hS : S.Exact) [Epi S.g]
    (M : Rep k G) {r : S.X₂.V →ₗ[k] S.X₁.V} (hr : Function.LeftInverse r S.f.hom) :
    (S.map (tensorLeft M)).ShortExact :=
  shortExact_map_tensorLeft_of_injective hS M (leftInverse_whiskerLeft M S.f hr).injective

/-- Tensoring on the left with `M` sends an exact sequence starting in a monomorphism to a
short exact sequence if the last map has a `k`-linear section. -/
theorem shortExact_map_tensorLeft_of_rightInverse {S : ShortComplex (Rep.{u} k G)}
    (hS : S.Exact) [Mono S.f]
    (M : Rep k G) {s : S.X₃.V →ₗ[k] S.X₂.V} (hs : Function.RightInverse s S.g.hom) :
    (S.map (tensorLeft M)).ShortExact := by
  have : Epi S.g := (epi_iff_surjective S.g).2 hs.surjective
  obtain ⟨r, hr⟩ := exists_leftInverse_of_rightInverse hS hs
  exact shortExact_map_tensorLeft_of_leftInverse hS M hr

end Rep
