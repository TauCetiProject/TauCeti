/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Field.ZMod
public import TauCeti.LinearAlgebra.Matrix.SpecialLinearGroup.CongruenceKernel

/-!
# Degenerate congruence kernels

Two boundary cases of `TauCeti.SpecialLinearGroup.congruenceKernel`. In rank one `SL(1, A)` is
trivial, so its congruence kernel is trivial. Every field has finite quotients, and over a
field the only nonzero level is the unit ideal, whose principal congruence subgroup is all of
`SL(n, K)`, so the congruence kernel is the whole profinite completion. In particular the image
of the nontrivial matrix `[[1, 1], [0, 1]]` over `ZMod 2` lies in the congruence kernel, which is
why `etaFn_mem_congruenceKernel_iff_eq_one` excludes fields.
-/

public section

open Matrix Matrix.SpecialLinearGroup TauCeti.SpecialLinearGroup

namespace TauCeti.CongruenceKernelExamples

/-- In rank one the congruence kernel is trivial: `SL(1, A)` itself is trivial. -/
example {A : Type*} [CommRing A] [IsDomain A] [Ring.HasFiniteQuotients A] :
    congruenceKernel (Fin 1) A = ⊥ := by
  refine congruenceKernel_eq_bot_iff.2 fun H _ ↦ ⟨⊤, top_ne_bot, fun γ _ ↦ ?_⟩
  have hγ : γ = 1 := by
    ext i j
    fin_cases i; fin_cases j
    simpa [det_fin_one] using γ.det_coe
  exact hγ ▸ H.one_mem

/-- Over a field the congruence kernel is the whole profinite completion: the only nonzero level
is the unit ideal, whose principal congruence subgroup is all of `SL(n, K)`. -/
theorem congruenceKernel_eq_top_of_field {n : Type*} [Fintype n] [DecidableEq n] {K : Type*}
    [Field K] [Ring.HasFiniteQuotients K] : congruenceKernel n K = ⊤ := by
  refine eq_top_iff.2 fun x _ ↦ mem_congruenceKernel_iff.2 fun I hI ↦ ?_
  obtain ⟨γ, hγ⟩ := QuotientGroup.mk_surjective
    (ProfiniteCompletion.coordinateHom _ (principalCongruenceSubgroup n K hI) x)
  rw [← hγ, QuotientGroup.eq_one_iff, toSubgroup_principalCongruenceSubgroup,
    mem_ker_map_quotientMk_iff]
  simp [(Ideal.eq_bot_or_top I).resolve_left hI]

/-- The upper unipotent matrix `[[1, 1], [0, 1]]` over `ZMod 2`. -/
def upperUnipotent : SpecialLinearGroup (Fin 2) (ZMod 2) :=
  ⟨!![1, 1; 0, 1], by simp [det_fin_two]⟩

/-- Over the field `ZMod 2` a nontrivial matrix has image in the congruence kernel. -/
example : upperUnipotent ≠ 1 ∧
      ProfiniteGrp.ProfiniteCompletion.etaFn _ upperUnipotent ∈
        congruenceKernel (Fin 2) (ZMod 2) := by
  refine ⟨fun h ↦ ?_, ?_⟩
  · have h01 := congrArg
      (fun g : SpecialLinearGroup (Fin 2) (ZMod 2) ↦ (g : Matrix (Fin 2) (Fin 2) (ZMod 2)) 0 1) h
    simp [upperUnipotent] at h01
  · exact (Subgroup.eq_top_iff' _).1
      (congruenceKernel_eq_top_of_field (n := Fin 2) (K := ZMod 2)) _

end TauCeti.CongruenceKernelExamples
