/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Etale.Basic
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import TauCeti.RingTheory.Regular.RegularSequence
import TauCeti.LinearAlgebra.BilinearForm.Dual.Lattice
import TauCeti.RingTheory.Etale.Discriminant
import TauCeti.RingTheory.Localization.Integral
import TauCeti.RingTheory.Trace.Regular

/-!
# Finiteness of algebras with étale generic fibre

Let `A` be a Noetherian integrally closed domain with fraction field `K`, and let `R` be a
torsion-free `A`-algebra whose generic fibre `K ⊗[A] R` is étale over `K`. This file shows that
`R` is a finite `A`-module as soon as, for a weakly regular sequence `x, y` of `A`, every element of
`R` becomes integral over `A` after multiplication by a power of `x`, and also after
multiplication by a power of `y`.

The proof bounds `R` inside a trace-dual lattice. The trace of an element of `R` is integral
over `A` after multiplication by a power of `x`, and also by a power of `y`, so it lies in `A`:
`A` is integrally closed, and an element of `K` which lies in `A` after multiplication by a power
of `x`, and also by a power of `y`, lies in `A` by weak regularity. Hence the image of `R` in the
generic fibre lies in its own dual for the trace form, which is nondegenerate because the generic
fibre is étale. Choosing a basis of the generic fibre inside `R`, the image of `R` lies in the
span of the dual basis, a finite `A`-module.

The situation arises for the ring of sections of a finite étale cover `V` of the punctured
spectrum `U` of a Noetherian normal local domain of depth at least two (Stacks, Lemma 58.20.3
(0BM9)): for `z` in the maximal ideal, the localization of `Γ(V, 𝒪_V)` at `z` is the ring of
sections over the preimage of the affine open `D(z) ⊆ U`, which is finite étale over `A_z`.

## Main results

* `TauCeti.Algebra.finite_of_isWeaklyRegular_of_isIntegral_pow_smul`: the finiteness criterion
  above.
* `TauCeti.Algebra.finite_of_isWeaklyRegular_of_isLocalization`: its form for localizations: if
  `R_x` is finite étale over `A_x` and `R_y` is finite over `A_y`, then `R` is finite over `A`.
  The hypotheses are supplied by `TauCeti.exists_isIntegral_pow_smul_of_isLocalization`
  and `TauCeti.Algebra.etale_tensorProduct_of_isLocalization`.

## References

* [Stacks Project, Lemma 58.20.3](https://stacks.math.columbia.edu/tag/0BM9), which identifies a
  finite étale cover of the punctured spectrum with the restriction of the spectrum of a finite
  algebra, its ring of sections.
-/

public section

open scoped TensorProduct

namespace TauCeti.Algebra

variable {A R : Type*} [CommRing A] [CommRing R] [Algebra A R]
  (K : Type*) [Field K] [Algebra A K] [IsFractionRing A K]

/-- **Finiteness from integrality away from a weakly regular pair.** Let `A` be a Noetherian
integrally closed domain with fraction field `K`, and `R` a torsion-free `A`-algebra whose
generic fibre `K ⊗[A] R` is étale over `K`. Let `x, y` be a weakly regular sequence of `A`. If
every element of `R` becomes integral over `A` after multiplication by a power of `x`, and also
after multiplication by a power of `y`, then `R` is a finite `A`-module. -/
theorem finite_of_isWeaklyRegular_of_isIntegral_pow_smul [IsNoetherianRing A]
    [IsIntegrallyClosed A] [Module.IsTorsionFree A R] [Algebra.Etale K (K ⊗[A] R)] {x y : A}
    (hxy : RingTheory.Sequence.IsWeaklyRegular A [x, y])
    (hx : ∀ r : R, ∃ n : ℕ, IsIntegral A (x ^ n • r))
    (hy : ∀ r : R, ∃ n : ℕ, IsIntegral A (y ^ n • r)) :
    Module.Finite A R := by
  let f : R →ₐ[A] K ⊗[A] R := Algebra.TensorProduct.includeRight
  have := Algebra.FormallyUnramified.finite_of_free K (K ⊗[A] R)
  -- `R` embeds in its generic fibre, since it is torsion free.
  have hf : Function.Injective f := fun r s hrs ↦ by
    obtain ⟨⟨c, hc⟩, hc'⟩ := (IsLocalizedModule.eq_iff_exists (nonZeroDivisors A)
      (TensorProduct.mk A K R 1)).1 hrs
    exact (Module.IsTorsionFree.isSMulRegular (isRegular_iff_mem_nonZeroDivisors.2 hc)) hc'
  -- The trace of every element of `R` lies in `A`.
  have htr (r : R) : Algebra.trace K (K ⊗[A] R) (f r) ∈ (algebraMap A K).range := by
    have key (z : A) (hz : ∃ n : ℕ, IsIntegral A (z ^ n • r)) :
        ∃ n : ℕ, algebraMap A K (z ^ n) * Algebra.trace K (K ⊗[A] R) (f r) ∈
          (algebraMap A K).range := by
      obtain ⟨n, hn⟩ := hz
      refine ⟨n, IsIntegrallyClosed.isIntegral_iff.1 ?_⟩
      have := Algebra.isIntegral_trace_lmul (K := K) (hn.map f)
      rwa [← Algebra.trace_apply, map_smul, ← IsScalarTower.algebraMap_smul K, map_smul,
        smul_eq_mul] at this
    obtain ⟨n, hn⟩ := key x (hx r)
    obtain ⟨j, hj⟩ := key y (hy r)
    exact hxy.mem_range_algebraMap_of_pow_mul_mem hn hj
  -- Hence the image of `R` lies in its own trace dual, and is finitely generated.
  let N : Submodule A (K ⊗[A] R) := LinearMap.range f.toLinearMap
  have hspan : Submodule.span K (N : Set (K ⊗[A] R)) = ⊤ := by
    rw [eq_top_iff]
    rintro z -
    induction z using TensorProduct.inductionOn with
    | tmul c r =>
      rw [← mul_one c, ← smul_eq_mul, ← TensorProduct.smul_tmul']
      exact Submodule.smul_mem _ c (Submodule.subset_span ⟨r, rfl⟩)
    | add z w hz hw => exact add_mem hz hw
  have hN : N ≤ (Algebra.traceForm K (K ⊗[A] R)).dualSubmodule N := by
    rintro _ ⟨r, rfl⟩ _ ⟨s, rfl⟩
    simpa [Submodule.mem_one, ← map_mul] using htr (r * s)
  have : Module.Finite A N := .iff_fg.2 <| LinearMap.BilinForm.fg_of_le_dualSubmodule
    ((Algebra.etale_iff_traceForm_nondegenerate K _).1 ‹_›) hspan hN
  exact .equiv (LinearEquiv.ofInjective f.toLinearMap hf).symm

section Localization

variable {x : A} (Ax Rx : Type*) [CommRing Ax] [CommRing Rx] [Algebra A Ax] [Algebra Ax Rx]
  [Algebra A Rx] [Algebra R Rx] [IsScalarTower A Ax Rx] [IsScalarTower A R Rx]
  [IsLocalization.Away x Ax] [IsLocalization.Away (algebraMap A R x) Rx]

/-- If `x` is nonzero and `R_x` is étale over `A_x`, the generic fibre of `R` is étale over the
fraction field `K` of `A`, being the generic fibre of `R_x`. -/
theorem etale_tensorProduct_of_isLocalization [Algebra.Etale Ax Rx] (hx : x ≠ 0) :
    Algebra.Etale K (K ⊗[A] R) := by
  have hxK : IsUnit (algebraMap A K x) :=
    (map_ne_zero_iff _ (IsFractionRing.injective A K)).2 hx |>.isUnit
  let : Algebra Ax K := (IsLocalization.Away.lift x hxK).toAlgebra
  have : IsScalarTower A Ax K := .of_algebraMap_eq fun a ↦
    (IsLocalization.Away.lift_eq x hxK a).symm
  have : IsLocalization (Algebra.algebraMapSubmonoid R (.powers x)) Rx := by
    rwa [Algebra.algebraMapSubmonoid_powers]
  have : Algebra.IsPushout A Ax R Rx :=
    (Algebra.isPushout_of_isLocalization (.powers x) Ax R Rx).symm
  -- `K ⊗[A] R ≃ K ⊗[A_x] (A_x ⊗[A] R) ≃ K ⊗[A_x] R_x`.
  exact .of_equiv <| (Algebra.TensorProduct.congr AlgEquiv.refl
    (Algebra.IsPushout.equiv A Ax R Rx).symm).trans
    (Algebra.TensorProduct.cancelBaseChange A Ax K K R)

variable [IsDomain A] {y : A} (Ay Ry : Type*) [CommRing Ay] [CommRing Ry] [Algebra A Ay]
  [Algebra Ay Ry] [Algebra A Ry] [Algebra R Ry] [IsScalarTower A Ay Ry] [IsScalarTower A R Ry]
  [IsLocalization.Away y Ay] [IsLocalization.Away (algebraMap A R y) Ry]

/-- **Finiteness from finite étale localizations.** Let `A` be a Noetherian integrally closed
domain, `x, y` a weakly regular sequence of `A`, and `R` a torsion-free `A`-algebra. If `R_x` is
finite étale over `A_x` and `R_y` is finite over `A_y`, then `R` is a finite `A`-module. -/
theorem finite_of_isWeaklyRegular_of_isLocalization [IsNoetherianRing A] [IsIntegrallyClosed A]
    [Module.IsTorsionFree A R] (hxy : RingTheory.Sequence.IsWeaklyRegular A [x, y])
    [Module.Finite Ax Rx] [Algebra.Etale Ax Rx] [Module.Finite Ay Ry] :
    Module.Finite A R := by
  have hx0 : x ≠ 0 := fun h ↦ one_ne_zero
    (((RingTheory.Sequence.isWeaklyRegular_cons_iff A x [y]).1 hxy).1 (by simp [h] :
      x • (1 : A) = x • 0))
  have := etale_tensorProduct_of_isLocalization (R := R) (FractionRing A) Ax Rx hx0
  refine finite_of_isWeaklyRegular_of_isIntegral_pow_smul (FractionRing A) hxy
    (TauCeti.exists_isIntegral_pow_smul_of_isLocalization Ax Rx)
    (TauCeti.exists_isIntegral_pow_smul_of_isLocalization Ay Ry)

end Localization

end TauCeti.Algebra
