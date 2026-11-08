/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import Mathlib.Algebra.FiveLemma
public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.LinearAlgebra.Prod

/-!
# Scalar extension of compatible pairs

For `f : M → P` and `g : N → P`, the kernel of `f.coprod (-g)` consists of compatible
pairs. If `N` and `P` are modules over a flat `R`-algebra `S`, projection to `N` induces
a comparison from the scalar extension of this kernel to `N`.

This comparison is injective when the scalar-extension comparison for `f` is injective
and multiplication `S ⊗[R] ker g → ker g` is injective. This separates the linear-algebra
argument from the torsion input used in formal gluing (Stacks, Proposition 15.91.16,
Tag 05ER). The proof uses Mathlib's preservation of exact sequences by flat tensor products.
-/

public section

open Function TensorProduct

namespace LinearMap

variable {R S M N P : Type*} [CommRing R] [CommRing S] [Algebra R S]
  [Module.Flat R S] [AddCommGroup M] [Module R M]
  [AddCommGroup N] [Module R N] [Module S N] [IsScalarTower R S N]
  [AddCommGroup P] [Module R P] [Module S P] [IsScalarTower R S P]

/-- Scalar extension of the projection from compatible pairs to the second factor is
injective if the comparison for the first map and multiplication on the kernel of the
second map are injective. No finiteness or faithful flatness is required. -/
theorem injective_liftBaseChange_snd_ker_coprod (f : M →ₗ[R] P) (g : N →ₗ[S] P)
    (hf : Injective (f.liftBaseChange S))
    (hg : Injective (((LinearMap.id : g.ker →ₗ[S] g.ker).restrictScalars R).liftBaseChange S)) :
    Injective (((LinearMap.snd R M N).domRestrict
      (f.coprod (-g.restrictScalars R)).ker).liftBaseChange S) := by
  let K := (f.coprod (-g.restrictScalars R)).ker
  let a : g.ker →ₗ[R] K :=
    ((LinearMap.inr R M N).comp (g.ker.subtype.restrictScalars R)).codRestrict K
      (fun n ↦ by simp [K, LinearMap.mem_ker])
  let b : K →ₗ[R] M := (LinearMap.fst R M N).domRestrict K
  let c : K →ₗ[R] N := (LinearMap.snd R M N).domRestrict K
  have hK (k : K) : f k.val.1 = g k.val.2 := by
    simpa only [K, LinearMap.mem_ker, LinearMap.coprod_apply,
      LinearMap.neg_apply, LinearMap.coe_restrictScalars, sub_eq_zero, ← sub_eq_add_neg]
      using k.property
  have ha : Injective a := by
    intro n n' h
    exact Subtype.ext (congrArg (fun k : K ↦ k.val.2) h)
  have hab : Exact a b := by
    intro k
    constructor
    · intro hk
      refine ⟨⟨k.val.2, ?_⟩, ?_⟩
      · have hk0 : k.val.1 = 0 := by simpa [b] using hk
        simpa [hk0] using (hK k).symm
      · apply Subtype.ext
        exact Prod.ext hk.symm rfl
    · rintro ⟨n, rfl⟩
      simp [a, b, LinearMap.codRestrict]
  have hfc : (f.liftBaseChange S).restrictScalars R ∘ₗ b.lTensor S =
      (g.restrictScalars R) ∘ₗ (c.liftBaseChange S).restrictScalars R := by
    ext s k
    simp [b, c, hK k]
  let μ := ((LinearMap.id : g.ker →ₗ[S] g.ker).restrictScalars R).liftBaseChange S
  have hca : (c.liftBaseChange S).restrictScalars R ∘ₗ a.lTensor S =
      (g.ker.subtype.restrictScalars R) ∘ₗ μ.restrictScalars R := by
    ext s n
    simp [a, c, μ, LinearMap.codRestrict]
  -- Apply the four lemma to the exact rows starting in zero, with vertical maps
  -- multiplication, the compatible-pairs comparison, and the comparison for `f`.
  exact LinearMap.injective_of_surjective_of_injective_of_injective
    (0 : Unit →ₗ[R] S ⊗[R] g.ker) (a.lTensor S) (b.lTensor S)
    (0 : Unit →ₗ[R] g.ker) (g.ker.subtype.restrictScalars R) (g.restrictScalars R)
    (0 : Unit →ₗ[R] Unit) (μ.restrictScalars R) ((c.liftBaseChange S).restrictScalars R)
    ((f.liftBaseChange S).restrictScalars R) (by simp) hca.symm hfc.symm
    ((LinearMap.exact_zero_iff_injective Unit _).mpr
      (Module.Flat.lTensor_preserves_injective_linearMap a ha))
    (Module.Flat.lTensor_exact S hab)
    ((LinearMap.exact_zero_iff_injective Unit _).mpr g.ker.subtype_injective)
    (fun _ ↦ ⟨(), rfl⟩) hg hf

end LinearMap
