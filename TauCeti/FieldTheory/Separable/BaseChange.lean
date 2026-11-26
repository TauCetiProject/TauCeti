/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.Separable
public import Mathlib.RingTheory.TensorProduct.Basic
import TauCeti.FieldTheory.Separable.Adjoin

/-!
# Separability of quotients of base-changed separable algebras

If `L` is a separable algebra over a field `K₀` and `K / K₀` is a field extension, then every
commutative domain `E` receiving a surjective `K`-algebra homomorphism from `K ⊗[K₀] L` is
separable over `K`. Every generator `φ (1 ⊗ l)` is annihilated by `minpoly K₀ l` and is therefore
separable over `K₀`, hence over `K`, and these generators generate `E` as a `K`-algebra. No
finiteness hypothesis on `L / K₀` is needed.

## Main results

* `AlgHom.isSeparable_of_surjective_of_isSeparable`: a commutative domain receiving a surjective
  `K`-algebra homomorphism from `K ⊗[K₀] L`, where `L` is a separable `K₀`-algebra, is separable
  over `K`.
-/

public section

open scoped TensorProduct

namespace AlgHom

/-- If `L` is a separable algebra over a field `K₀` and `K` is a field extension of `K₀`, then
every commutative domain `E` receiving a surjective `K`-algebra homomorphism from `K ⊗[K₀] L` is
separable over `K`. No finiteness hypothesis on `L / K₀` is needed. -/
theorem isSeparable_of_surjective_of_isSeparable {K₀ L K E : Type*}
    [Field K₀] [Ring L] [Algebra K₀ L] [Algebra.IsSeparable K₀ L]
    [Field K] [Algebra K₀ K] [CommRing E] [IsDomain E] [Algebra K E]
    (φ : K ⊗[K₀] L →ₐ[K] E) (hφ : Function.Surjective φ) :
    Algebra.IsSeparable K E := by
  let : Algebra K₀ E := ((algebraMap K E).comp (algebraMap K₀ K)).toAlgebra
  have : IsScalarTower K₀ K E := .of_algebraMap_eq fun _ ↦ rfl
  let jL : L →ₐ[K₀] E := (φ.restrictScalars K₀).comp Algebra.TensorProduct.includeRight
  let s : Set E := Set.range jL
  -- Every generator `jL l` is annihilated by `minpoly K₀ l`, hence separable over `K₀` and `K`.
  have hsep_s : ∀ x ∈ s, IsSeparable K x := by
    rintro _ ⟨l, rfl⟩
    have hl : IsSeparable K₀ l := Algebra.IsSeparable.isSeparable K₀ l
    have haeval : Polynomial.aeval (jL l) (minpoly K₀ l) = 0 := by
      rw [Polynomial.aeval_algHom_apply, minpoly.aeval, map_zero]
    exact IsSeparable.tower_top K (hl.of_dvd (minpoly.dvd K₀ (jL l) haeval))
  have hsep_adj : Algebra.IsSeparable K (Algebra.adjoin K s) :=
    (Set.Pairwise.isSeparable_adjoin_iff fun _ _ _ _ _ ↦ Commute.all _ _).mpr hsep_s
  -- Because `φ` is surjective and `k ⊗ l = k • (1 ⊗ l)`, `s` generates `E` as a `K`-algebra.
  have htop : Algebra.adjoin K s = ⊤ := by
    refine eq_top_iff.mpr fun y _ ↦ ?_
    obtain ⟨t, rfl⟩ := hφ y
    refine TensorProduct.inductionOn t (fun k l ↦ ?_)
      (fun x y hx hy ↦ by rw [map_add]; exact add_mem hx hy)
    rw [TensorProduct.tmul_eq_smul_one_tmul, map_smul, Algebra.smul_def]
    exact mul_mem (_root_.algebraMap_mem _ k) (Algebra.subset_adjoin ⟨l, rfl⟩)
  exact ⟨fun x ↦ (Subalgebra.isSeparable_iff.mp hsep_adj) x (htop ▸ Algebra.mem_top)⟩

end AlgHom
