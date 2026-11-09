/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Etale.Basic
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import TauCeti.RingTheory.Depth.Basic
import Mathlib.RingTheory.Smooth.Flat
import TauCeti.RingTheory.Etale.Discriminant
import TauCeti.RingTheory.NormTrace.BaseChange

/-!
# Finiteness of algebras étale away from the closed point

Let `A` be a Noetherian local domain of depth at least two and `C` a torsion-free `A`-algebra such
that `A_𝔭 ⊗[A] C` is finite étale over `A_𝔭` for every prime `𝔭` other than the maximal ideal.
Then `C` is a finite `A`-module. No normality of `A` is needed.

The proof uses the trace form of the generic fibre `L = K ⊗[A] C`, where `K` is the fraction
field of `A`. This fibre is finite étale over `K`, so its trace form is nondegenerate
(`TauCeti.Algebra.etale_iff_traceForm_nondegenerate`). Choose a `K`-basis `t₁, …, tₙ` of `L` made
of elements of `C`. For `c ∈ C`, the trace of `c tᵢ` lies in `A_𝔭` for every prime `𝔭 ≠ 𝔪`,
because `A_𝔭 ⊗[A] C` is finite free over the local ring `A_𝔭`. As `A` has depth at least two, it
therefore lies in `A` (`IsLocalRing.mem_range_algebraMap_of_two_le_depth`). So
`c ↦ (Tr(c tᵢ))ᵢ` embeds `C` into `Aⁿ`, and `C` is finite because `A` is Noetherian.

The typical `C` is the ring of sections of a finite étale cover of the punctured spectrum of `A`,
which is finite étale over `A_𝔭` at every prime `𝔭 ≠ 𝔪` but not a priori finite over `A`.

## Main results

* `TauCeti.IsLocalRing.finite_of_finiteEtale_localization`: a torsion-free algebra over a
  Noetherian local domain of depth at least two that is finite étale after localizing at every
  prime other than the maximal ideal is finite.

## References

* M. F. Atiyah and I. G. Macdonald, *Introduction to Commutative Algebra*, Proposition 5.17: the
  trace-form argument bounding an integral closure in a separable extension by a dual basis,
  which this file adapts with depth two in place of integral closedness.
* [The Stacks Project, Lemma 58.20.3](https://stacks.math.columbia.edu/tag/0BM9), whose proof
  needs the sections of a finite étale cover of the punctured spectrum to be finite over `A`.
-/

public section

open scoped TensorProduct

open IsLocalRing

namespace TauCeti.IsLocalRing

variable {A : Type*} [CommRing A] [IsLocalRing A] [IsNoetherianRing A] [IsDomain A]

/-- The trace of `1 ⊗ x` in the generic fibre `K ⊗[A] C` lies in `A`, when `A` has depth at least
two and `A_𝔭 ⊗[A] C` is finite étale over `A_𝔭` for every prime `𝔭` other than the maximal ideal. -/
private lemma exists_algebraMap_trace_tmul_eq (hdepth : 2 ≤ depth (ModuleCat.of A A))
    (C : Type*) [CommRing C] [Algebra A C]
    (h : ∀ (p : Ideal A) [p.IsPrime], p ≠ maximalIdeal A →
      Module.Finite (Localization.AtPrime p) (Localization.AtPrime p ⊗[A] C) ∧
        Algebra.Etale (Localization.AtPrime p) (Localization.AtPrime p ⊗[A] C))
    (x : C) :
    ∃ a : A, algebraMap A (FractionRing A) a =
      Algebra.trace (FractionRing A) (FractionRing A ⊗[A] C) (1 ⊗ₜ x) := by
  refine mem_range_algebraMap_of_two_le_depth (FractionRing A) hdepth fun p _ hp ↦ ?_
  obtain ⟨_, _⟩ := h p hp
  have : Module.Free (Localization.AtPrime p) (Localization.AtPrime p ⊗[A] C) :=
    Module.free_of_flat_of_isLocalRing
  obtain ⟨⟨a, s⟩, hs⟩ := IsLocalization.surj p.primeCompl
    (Algebra.trace (Localization.AtPrime p) (Localization.AtPrime p ⊗[A] C) (1 ⊗ₜ x))
  refine ⟨s, s.2, a, ?_⟩
  rw [Algebra.trace_baseChange_tmul_of_isScalarTower (S := Localization.AtPrime p),
    IsScalarTower.algebraMap_apply A (Localization.AtPrime p) (FractionRing A),
    IsScalarTower.algebraMap_apply A (Localization.AtPrime p) (FractionRing A), ← map_mul,
    mul_comm, hs]

/-- Let `A` be a Noetherian local domain of depth at least two and `C` a torsion-free `A`-algebra.
If `A_𝔭 ⊗[A] C` is finite étale over `A_𝔭` for every prime `𝔭` other than the maximal ideal, then
`C` is a finite `A`-module. -/
theorem finite_of_finiteEtale_localization (hdepth : 2 ≤ depth (ModuleCat.of A A))
    (C : Type*) [CommRing C] [Algebra A C] [Module.IsTorsionFree A C]
    (h : ∀ (p : Ideal A) [p.IsPrime], p ≠ maximalIdeal A →
      Module.Finite (Localization.AtPrime p) (Localization.AtPrime p ⊗[A] C) ∧
        Algebra.Etale (Localization.AtPrime p) (Localization.AtPrime p ⊗[A] C)) :
    Module.Finite A C := by
  let K := FractionRing A
  let L := K ⊗[A] C
  let ι := TensorProduct.mk A K C 1
  -- The generic fibre `L` is finite étale over `K`, so its trace form is nondegenerate.
  have hbot : (⊥ : Ideal A) ≠ maximalIdeal A :=
    (maximalIdeal_ne_bot_of_depth_ne_zero (ne_of_gt (lt_of_lt_of_le (by decide) hdepth))).symm
  obtain ⟨_, _⟩ := h ⊥ hbot
  let e₀ := Algebra.TensorProduct.cancelBaseChange A (Localization.AtPrime (⊥ : Ideal A)) K K C
  have : Module.Finite K L := .equiv e₀.toLinearEquiv
  have : Algebra.Etale K L := .of_equiv e₀
  have hnd := (TauCeti.Algebra.etale_iff_traceForm_nondegenerate K L).1 inferInstance
  -- As `C` is torsion free, it embeds into `L`, and its image spans `L` over `K`.
  have hinj : Function.Injective ι := by
    have : IsLocalizedModule (nonZeroDivisors A) ι :=
      (isLocalizedModule_iff_isBaseChange (nonZeroDivisors A) K ι).2
        (TensorProduct.isBaseChange A C K)
    exact (IsLocalizedModule.injective_iff_isRegular (nonZeroDivisors A) ι).2 fun s ↦
      IsSMulRegular.of_ne_zero (nonZeroDivisors.ne_zero s.2)
  have hspan : Submodule.span K (Set.range ι) = ⊤ := by
    rw [← LinearMap.coe_range, ← Submodule.map_top, ← Submodule.baseChange_eq_span,
      Submodule.baseChange_top]
  -- A `K`-basis `b` of `L` made of elements of `C`.
  obtain ⟨b, hbC, hb, hli⟩ := exists_linearIndependent K (Set.range ι)
  have : Fintype b := hli.setFinite.fintype
  rw [hspan] at hb
  -- The traces `c ↦ Tr (c t)` for `t ∈ b` take values in `A`, and so map `C` into `Aᵇ`.
  let ψ : C →ₗ[A] b → K := LinearMap.pi fun t ↦
    ((Algebra.traceForm K L).flip t).restrictScalars A ∘ₗ ι
  let N : Submodule A (b → K) := LinearMap.range (LinearMap.compLeft (Algebra.linearMap A K) b)
  have hval (c : C) (t : b) : ∃ a : A, algebraMap A K a = ψ c t := by
    obtain ⟨d, hd⟩ := hbC t.2
    -- `ψ c t` is by definition the trace of `ι c * t`.
    have hψ : ψ c t = Algebra.trace K L (ι c * t) := rfl
    rw [hψ, ← hd, TensorProduct.mk_apply, TensorProduct.mk_apply,
      Algebra.TensorProduct.tmul_mul_tmul, mul_one]
    exact exists_algebraMap_trace_tmul_eq hdepth C h (c * d)
  have hle : LinearMap.range ψ ≤ N := by
    rintro _ ⟨c, rfl⟩
    choose a ha using hval c
    exact ⟨a, funext ha⟩
  -- The embedding is injective by nondegeneracy of the trace form, so `C` is finite.
  refine Module.Finite.of_injective (ψ.codRestrict N fun c ↦ hle ⟨c, rfl⟩) ?_
  refine (injective_iff_map_eq_zero _).2 fun c hc ↦ hinj ?_
  have hc' (t : b) : Algebra.traceForm K L (ι c) t = 0 :=
    congrFun (congrArg Subtype.val hc) t
  rw [map_zero]
  refine hnd.1 _ fun y ↦ ?_
  have hy : y ∈ Submodule.span K (b : Set L) := hb ▸ Submodule.mem_top
  induction hy using Submodule.span_induction with
  | mem t ht => exact hc' ⟨t, ht⟩
  | zero => exact map_zero _
  | add x y _ _ hx hy => rw [map_add, hx, hy, add_zero]
  | smul k x _ hx => rw [map_smul, hx, smul_zero]

end TauCeti.IsLocalRing
