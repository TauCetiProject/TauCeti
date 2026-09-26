/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.LinearAlgebra.TensorProduct.RightExactness
public import Mathlib.RepresentationTheory.Rep.Basic

/-!
# Tensoring a short exact sequence of representations

Tensoring with a fixed representation `M` is right exact, but not exact in general. This file
records that a short exact sequence of representations which is split as a sequence of
`k`-modules stays short exact after tensoring on the left with `M`: the `k`-linear retraction of
the first map survives tensoring and keeps the tensored first map injective, while right
exactness of the tensor product supplies exactness and the surjectivity of the last map. The
dimension-shifting sequences through the modules induced and coinduced from the trivial subgroup
are of this kind.

## Main statements

* `Rep.exact_iff_function_exact`: a short complex of representations is exact if and only if the
  underlying linear maps form an exact pair.
* `Rep.shortExact_map_tensorLeft_of_injective`: tensoring on the left preserves a short exact
  sequence as soon as the tensored first map stays injective.
* `Rep.shortExact_map_tensorLeft_of_leftInverse`,
  `Rep.shortExact_map_tensorLeft_of_rightInverse`: tensoring on the left preserves a short exact
  sequence whose first map has a `k`-linear retraction, or whose last map has a `k`-linear
  section.
-/

public section

universe u

open CategoryTheory MonoidalCategory

namespace Rep

variable {k G : Type u} [CommRing k] [Monoid G]

/-- A short complex of representations is exact if and only if the underlying linear maps form an
exact pair. -/
theorem exact_iff_function_exact (S : ShortComplex (Rep k G)) :
    S.Exact ↔ Function.Exact S.f.hom S.g.hom := by
  rw [← ShortComplex.exact_map_iff_of_faithful S (forget₂ (Rep k G) (ModuleCat k)),
    ShortComplex.ShortExact.moduleCat_exact_iff_function_exact]
  rfl

/-- Tensoring on the left with `M` preserves a short exact sequence of representations as soon as
the tensored first map stays injective: exactness and the surjectivity of the last map come from
right exactness of the tensor product. -/
theorem shortExact_map_tensorLeft_of_injective {S : ShortComplex (Rep k G)} (hS : S.ShortExact)
    (M : Rep k G) (hf : Function.Injective (LinearMap.lTensor M.V S.f.hom.toLinearMap)) :
    (S.map (tensorLeft M)).ShortExact where
  exact := (exact_iff_function_exact _).2 <| lTensor_exact M.V
    ((exact_iff_function_exact S).1 hS.exact) ((epi_iff_surjective S.g).1 hS.epi_g)
  mono_f := (mono_iff_injective _).2 hf
  epi_g := (epi_iff_surjective _).2 <|
    LinearMap.lTensor_surjective M.V ((epi_iff_surjective S.g).1 hS.epi_g)

/-- Tensoring on the left with `M` preserves a short exact sequence of representations whose first
map has a `k`-linear retraction. -/
theorem shortExact_map_tensorLeft_of_leftInverse {S : ShortComplex (Rep k G)} (hS : S.ShortExact)
    (M : Rep k G) (r : S.X₂.V →ₗ[k] S.X₁.V) (hr : Function.LeftInverse r S.f.hom) :
    (S.map (tensorLeft M)).ShortExact := by
  refine shortExact_map_tensorLeft_of_injective hS M
    (Function.LeftInverse.injective (g := LinearMap.lTensor M.V r) fun x ↦ ?_)
  have h : r ∘ₗ S.f.hom.toLinearMap = LinearMap.id := LinearMap.ext hr
  rw [← LinearMap.comp_apply, ← LinearMap.lTensor_comp, h, LinearMap.lTensor_id, LinearMap.id_apply]

/-- Tensoring on the left with `M` preserves a short exact sequence of representations whose last
map has a `k`-linear section. -/
theorem shortExact_map_tensorLeft_of_rightInverse {S : ShortComplex (Rep k G)} (hS : S.ShortExact)
    (M : Rep k G) (s : S.X₃.V →ₗ[k] S.X₂.V) (hs : Function.RightInverse s S.g.hom) :
    (S.map (tensorLeft M)).ShortExact := by
  have h : S.g.hom.toLinearMap ∘ₗ s = LinearMap.id := LinearMap.ext hs
  have tfae := ((exact_iff_function_exact S).1 hS.exact).split_tfae
    ((mono_iff_injective S.f).1 hS.mono_f) ((epi_iff_surjective S.g).1 hS.epi_g)
  have key : (∃ l, S.g.hom.toLinearMap ∘ₗ l = LinearMap.id) ↔
      ∃ l, l ∘ₗ S.f.hom.toLinearMap = LinearMap.id := tfae.out 1 2
  obtain ⟨r, hr⟩ := key.1 ⟨s, h⟩
  exact shortExact_map_tensorLeft_of_leftInverse hS M r (LinearMap.congr_fun hr)

end Rep
