/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axel Delaval, Jie Xu, Shitan Xu
-/
module

public import Mathlib.Algebra.Exact.Basic
public import Mathlib.Algebra.Module.StablyFree.Basic
public import Mathlib.RingTheory.Finiteness.Prod
public import Mathlib.LinearAlgebra.Basis.Prod

/-!
# Stably free modules in split exact sequences

Stable freeness passes from the kernel to a projective quotient when the middle module is
finite free. The proof splits the exact sequence and adjoins a finite free complement.

## References

* [The Stacks Project, Tag 0BC3](https://stacks.math.columbia.edu/tag/0BC3), stable freeness.
-/

public section

universe typeUniverse

namespace Module

variable {ring : Type typeUniverse} [Ring ring] {kernel freeModule quotientModule : Type*}
  [AddCommGroup kernel] [Module ring kernel] [AddCommGroup freeModule]
  [Module ring freeModule] [AddCommGroup quotientModule] [Module ring quotientModule]
  {firstMap : kernel →ₗ[ring] freeModule} {secondMap : freeModule →ₗ[ring] quotientModule}

/-- A short exact sequence with projective quotient splits as a product. -/
theorem nonempty_linearEquiv_prod_of_exact [Projective ring quotientModule]
    (hf : Function.Injective firstMap)
    (hg : Function.Surjective secondMap)
    (compatibility : Function.Exact firstMap secondMap) :
    Nonempty (freeModule ≃ₗ[ring] kernel × quotientModule) := by
  obtain ⟨liftMap, hl⟩ := projective_lifting_property secondMap LinearMap.id hg
  exact ⟨(compatibility.splitSurjectiveEquiv hf ⟨liftMap, hl⟩).val⟩

/-- A kernel of a surjection between projective modules is projective. -/
theorem Projective.of_exact_of_projective [Projective ring freeModule]
    [Projective ring quotientModule]
    (hf : Function.Injective firstMap) (hg : Function.Surjective secondMap)
    (compatibility : Function.Exact firstMap secondMap) :
    Projective ring kernel := by
  obtain ⟨equivalence⟩ := nonempty_linearEquiv_prod_of_exact hf hg compatibility
  exact .of_split (equivalence.symm.toLinearMap ∘ₗ LinearMap.inl ring kernel quotientModule)
    (LinearMap.fst ring kernel quotientModule ∘ₗ equivalence.toLinearMap)
    (LinearMap.ext fun element ↦ by simp)

/-- A kernel of a surjection from a finite module to a projective module is finite. -/
theorem Finite.of_exact_of_projective [Module.Finite ring freeModule]
    [Projective ring quotientModule]
    (hf : Function.Injective firstMap) (hg : Function.Surjective secondMap)
    (compatibility : Function.Exact firstMap secondMap) :
    Module.Finite ring kernel := by
  obtain ⟨equivalence⟩ := nonempty_linearEquiv_prod_of_exact hf hg compatibility
  exact .of_surjective (LinearMap.fst ring kernel quotientModule ∘ₗ equivalence.toLinearMap)
    (Prod.fst_surjective.comp equivalence.surjective)

/-- In a short exact sequence with finite free middle term and projective quotient,
stable freeness of the kernel implies stable freeness of the quotient. -/
theorem IsStablyFree.of_exact [Module.Finite ring freeModule] [Free ring freeModule]
    [IsStablyFree ring kernel] [Projective ring quotientModule]
    (hf : Function.Injective firstMap) (hg : Function.Surjective secondMap)
    (compatibility : Function.Exact firstMap secondMap) :
    IsStablyFree ring quotientModule := by
  obtain ⟨equivalence⟩ := nonempty_linearEquiv_prod_of_exact hf hg compatibility
  have : Module.Finite ring kernel := Finite.of_exact_of_projective hf hg compatibility
  obtain ⟨complement, _, _, _, _, _⟩ := IsStablyFree.exist_free_prod ring kernel
  have : Free ring (quotientModule × (kernel × complement)) := .of_equiv <|
    equivalence.prodCongr (LinearEquiv.refl ring complement) ≪≫ₗ
    (LinearEquiv.prodComm ring kernel quotientModule).prodCongr
      (LinearEquiv.refl ring complement) ≪≫ₗ
    LinearEquiv.prodAssoc ring quotientModule kernel complement
  exact .of_free_prod ring quotientModule (kernel × complement)

end Module
