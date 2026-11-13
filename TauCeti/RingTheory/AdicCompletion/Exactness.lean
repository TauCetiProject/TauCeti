/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.AdicCompletion.Exactness
-- Proof-only: identify its ideal-linear quotient map with Mathlib's `reduceModIdeal`.
import all TauCeti.RingTheory.QuotSMulTop

/-!
# Exactness and kernel comparison for adic completion

If `0 → M → N → P → 0` is short exact and multiplication by `r` is injective on `P`, then
completion for `(r)` preserves short exactness. There are no Noetherian or finite-generation
assumptions. In particular, this applies to p-adic completion of a short exact sequence with
p-torsion-free last term.
Surjectivity on the right is already supplied by `AdicCompletion.map_surjective`.

More generally, completion preserves a right exact sequence when the first map is injective
modulo every power of the defining ideal, or satisfies a uniform filtration-shift bound. In
the former case the unique preimages of a compatible family in the kernel are automatically
compatible; in the latter, lifts at shifted levels form a Cauchy sequence. For a principal
ideal, regularity on the last term gives this injectivity for the range inclusion by
`Ideal.mapQSMulTop_span_singleton_injective`.
Surjectivity of completion onto the completed range then gives middle exactness without an
injectivity assumption on the original first map.

`LinearMap.kerAdicCompletionEquiv` packages injectivity of the completed kernel inclusion
and middle exactness as the canonical kernel comparison over the completed ring.

The compatible-residue model of `AdicCompletion` and its residue evaluations are due to
Kenny Lau. Judith Ludwig and Christian Merten refactored the construction and supplied its
completed-ring module structure and functorial maps. The filtration-shift proofs adapt their
`AdicCompletion.map_injective` and `AdicCompletion.map_exact` in
`Mathlib.RingTheory.AdicCompletion.Exactness`, isolating the uniform shift from the Noetherian
Artin–Rees input. The finite-level exactness results are those of
`TauCeti.RingTheory.QuotSMulTop`; no new completion carrier is introduced.
-/

public section

namespace AdicCompletion

variable {R : Type*} [CommRing R] {I : Ideal R}
variable {M N P : Type*} [AddCommGroup M] [Module R M]
  [AddCommGroup N] [Module R N] [AddCommGroup P] [Module R P]
variable {f : M →ₗ[R] N} {g : N →ₗ[R] P}

/-- If a linear map is injective modulo every power of an ideal, its completion is injective. -/
theorem map_injective_of_reduceModIdeal_injective
    (hf : ∀ n : ℕ, Function.Injective (f.reduceModIdeal (I ^ n))) :
    Function.Injective (map I f) := by
  intro x y h
  exact AdicCompletion.ext fun n ↦ hf n (by
    simpa only [map_val_apply] using congrArg (fun z ↦ z.val n) h)

/-- Completion is injective if preimages of ideal powers lie in the source filtration with
a fixed shift. No Noetherianity or finite-generation hypothesis is needed. -/
theorem map_injective_of_comap_pow_smul_le {k : ℕ}
    (hf : ∀ n, (I ^ (n + k) • ⊤ : Submodule R N).comap f ≤ I ^ n • ⊤) :
    Function.Injective (map I f) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro x
  apply AdicCompletion.induction_on I M x
  intro a hx
  exact AdicCompletion.mk_zero_of I M a
    ⟨0, fun n _ ↦ ⟨n + k, Nat.le_add_right n k, n, le_rfl,
      hf n (by simpa using congrArg (fun z ↦ z.val (n + k)) hx)⟩⟩

/-- Completion preserves a right exact sequence if its first map is injective modulo every
power of the defining ideal. No finiteness hypothesis is needed. -/
theorem map_exact_of_reduceModIdeal_injective
    (hfg : Function.Exact f g) (hg : Function.Surjective g)
    (hf : ∀ n : ℕ, Function.Injective (f.reduceModIdeal (I ^ n))) :
    Function.Exact (map I f) (map I g) := by
  classical
  refine LinearMap.exact_of_comp_eq_zero_of_ker_le_range ?_ fun y hy ↦ ?_
  · rw [map_comp, hfg.linearMap_comp_eq_zero, map_zero]
  have hpre (n : ℕ) : ∃ x, f.reduceModIdeal (I ^ n) x = y.val n := by
    -- The ideal-linear reduction and `reduceModIdeal` are the same quotient map.
    apply (Ideal.mapQSMulTop_exact (I ^ n) hfg hg (y.val n)).mp
    have hz : g.reduceModIdeal (I ^ n) (y.val n) = 0 :=
      congrArg (fun z ↦ z.val n) hy
    exact hz
  choose x hx using hpre
  have hcompat {m n : ℕ} (hmn : m ≤ n) : transitionMap I M hmn (x n) = x m := by
    apply hf m
    have hnat := LinearMap.congr_fun (transitionMap_comp_reduceModIdeal I f hmn) (x n)
    simpa only [LinearMap.comp_apply, LinearMap.restrictScalars_apply, hx, y.property hmn]
      using hnat.symm
  exact ⟨⟨x, hcompat⟩, AdicCompletion.ext fun n ↦ hx n⟩

/-- Completion preserves a right exact sequence if preimages of ideal powers lie in the
source filtration with a fixed shift. No finiteness hypothesis is needed. -/
theorem map_exact_of_comap_pow_smul_le {k : ℕ}
    (hfg : Function.Exact f g) (hg : Function.Surjective g)
    (hf : ∀ n, (I ^ (n + k) • ⊤ : Submodule R N).comap f ≤ I ^ n • ⊤) :
    Function.Exact (map I f) (map I g) := by
  classical
  refine LinearMap.exact_of_comp_eq_zero_of_ker_le_range ?_ fun y ↦ ?_
  · rw [map_comp, hfg.linearMap_comp_eq_zero, map_zero]
  apply AdicCompletion.induction_on I N y
  intro b hz
  -- Lift at shifted levels so that the filtration bound makes arbitrary lifts Cauchy.
  have hpre (n : ℕ) : ∃ a : M,
      f a ≡ b (n + k) [SMOD (I ^ (n + k) • ⊤ : Submodule R N)] := by
    obtain ⟨a, ha⟩ := (Ideal.mapQSMulTop_exact (I ^ (n + k)) hfg hg
      (Submodule.Quotient.mk (b (n + k)))).mp
        (by simpa using congrArg (fun z ↦ z.val (n + k)) hz)
    obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective _ a
    exact ⟨a, by simpa only [Ideal.mapQSMulTop_mk, SModEq.def] using ha⟩
  choose a ha using hpre
  have hle (n : ℕ) : (I ^ (n + k) • ⊤ : Submodule R N) ≤ I ^ n • ⊤ :=
    Submodule.smul_mono_left (Ideal.pow_le_pow_right (Nat.le_add_right n k))
  refine ⟨AdicCompletion.mk I M (AdicCauchySequence.mk I M a fun n ↦ ?_), ?_⟩
  · rw [SModEq.sub_mem]
    apply hf n
    rw [Submodule.mem_comap, map_sub, ← SModEq.sub_mem]
    have hs : f (a (n + 1)) ≡ b (n + 1 + k)
        [SMOD (I ^ (n + k) • ⊤ : Submodule R N)] :=
      SModEq.mono (Submodule.smul_mono_left (Ideal.pow_le_pow_right (by lia))) (ha (n + 1))
    exact (ha n).trans ((b.property (by lia)).trans hs.symm)
  · ext n
    simpa [SModEq.def] using
      (SModEq.mono (hle n) (ha n)).trans (b.property (Nat.le_add_right n k)).symm

/-- A short exact sequence whose last term is `r`-torsion-free remains injective on the left
after `(r)`-adic completion. The modules need not be finite. -/
theorem map_span_singleton_injective_of_isSMulRegular {r : R}
    (hf : Function.Injective f) (hfg : Function.Exact f g) (hr : IsSMulRegular P r) :
    Function.Injective (map (Ideal.span {r}) f) := by
  apply map_injective_of_reduceModIdeal_injective
  intro n
  rw [Ideal.span_singleton_pow]
  -- Both reductions are induced by `f` on the quotient by `rⁿ`.
  exact Ideal.mapQSMulTop_span_singleton_injective hfg hf (hr.pow n)

/-- Principal-adic completion preserves a right exact sequence when the parameter acts
injectively on the last term, without any Noetherian or finite-generation assumption. Together
with `map_span_singleton_injective_of_isSMulRegular` and `map_surjective`, this also gives all
three parts of short exactness when the first map is injective. -/
theorem map_span_singleton_exact_of_isSMulRegular {r : R}
    (hfg : Function.Exact f g) (hg : Function.Surjective g) (hr : IsSMulRegular P r) :
    Function.Exact (map (Ideal.span {r}) f) (map (Ideal.span {r}) g) := by
  have hfg' : Function.Exact f.range.subtype g := by
    apply f.surjective_rangeRestrict.comp_exact_iff_exact.mp
    simpa only [LinearMap.subtype_comp_rangeRestrict] using hfg
  rw [← f.subtype_comp_rangeRestrict, ← map_comp]
  apply (map_surjective _ f.surjective_rangeRestrict).comp_exact_iff_exact.mpr
  apply map_exact_of_reduceModIdeal_injective hfg' hg
  intro n
  rw [Ideal.span_singleton_pow]
  -- Regularity of `rⁿ` gives injectivity of the finite-level range inclusion.
  exact Ideal.mapQSMulTop_span_singleton_injective hfg' f.range.injective_subtype (hr.pow n)

end AdicCompletion

namespace LinearMap

variable {R : Type*} [CommRing R] {I : Ideal R}
  {M N : Type*} [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  (g : M →ₗ[R] N)
  (hi : Function.Injective (AdicCompletion.map I g.ker.subtype))
  (hc : Function.Exact (AdicCompletion.map I g.ker.subtype) (AdicCompletion.map I g))

/-- Completion of a kernel is the kernel of the completed map whenever completion preserves
injectivity of its inclusion and exactness at the source. The comparison is induced by the
completed kernel inclusion. -/
noncomputable def kerAdicCompletionEquiv :
    AdicCompletion I g.ker ≃ₗ[AdicCompletion I R] (AdicCompletion.map I g).ker :=
  (LinearEquiv.ofInjective _ hi).trans (LinearEquiv.ofEq _ _ hc.linearMap_ker_eq.symm)

/-- The kernel comparison followed by inclusion is the completion of the kernel inclusion. -/
@[simp]
theorem coe_kerAdicCompletionEquiv_apply (x : AdicCompletion I g.ker) :
    (g.kerAdicCompletionEquiv hi hc x : AdicCompletion I M) =
      AdicCompletion.map I g.ker.subtype x :=
  (rfl)

/-- The inverse kernel comparison lifts an element through the completed kernel inclusion. -/
@[simp]
theorem map_subtype_kerAdicCompletionEquiv_symm (x : (AdicCompletion.map I g).ker) :
    AdicCompletion.map I g.ker.subtype ((g.kerAdicCompletionEquiv hi hc).symm x) = x := by
  rw [← coe_kerAdicCompletionEquiv_apply g hi hc, LinearEquiv.apply_symm_apply]

end LinearMap
