/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.AdicCompletion.Exactness
public import TauCeti.RingTheory.QuotSMulTop

/-!
# Exactness of adic completion from filtration bounds

Completion preserves injectivity and right exactness when a uniform shift bounds the induced
filtration on the first module by its adic filtration. In particular, this applies when the
first map is injective modulo every power of the defining ideal.

For a principal ideal `(r)`, bounded `r`-power torsion in the last term of a short exact
sequence supplies this shift. The modules need not be finite and the ring need not be
Noetherian. The torsion-free last-term criteria are the special case of shift zero.
Surjectivity on the right is already supplied by `AdicCompletion.map_surjective`.
In particular, completion commutes with kernels of maps whose target and cokernel
have bounded `r`-power torsion.

These comparisons are used when completing complexes of sections: bounded torsion in the
next cohomology group controls the discrepancy between reduction of a kernel and the kernel
of reduction. This is the algebraic filtration step in the formal-section comparisons of
Stacks, Lemmas 52.3.2 (0BLD) and 52.12.7 (0EII); no sheaf-cohomology comparison is asserted here.

The proof uses the compatible-residue model of completion due to Judith Ludwig and Christian
Merten in Mathlib. The filtration argument parallels Mathlib's finite-module exactness proof,
replacing its Artin–Rees input with an explicit bound. Finite-level right exactness is supplied
by `TauCeti.RingTheory.QuotSMulTop`; no new completion carrier is introduced.
-/

public section

namespace Ideal

/-- Ideal-linear reduction is Mathlib's `reduceModIdeal`. -/
theorem mapQSMulTop_eq_reduceModIdeal {R : Type*} [CommRing R]
    {M N : Type*} [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (I : Ideal R) (f : M →ₗ[R] N) : I.mapQSMulTop f = f.reduceModIdeal I := by
  ext x
  induction x using Submodule.Quotient.induction_on with | H m =>
    simp only [mapQSMulTop_mk, LinearMap.reduceModIdeal_apply]

end Ideal

namespace LinearMap

/-- Injectivity modulo an ideal bounds the induced filtration by the ideal filtration. -/
theorem comap_smul_top_le_of_reduceModIdeal_injective {R : Type*} [CommRing R]
    {M N : Type*} [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    {I : Ideal R} {f : M →ₗ[R] N} (hf : Function.Injective (f.reduceModIdeal I)) :
    (I • (⊤ : Submodule R N)).comap f ≤ I • (⊤ : Submodule R M) := by
  intro x hx
  apply (Submodule.Quotient.mk_eq_zero _).mp
  apply hf
  rw [reduceModIdeal_apply, map_zero]
  exact (Submodule.Quotient.mk_eq_zero _).mpr (Submodule.mem_comap.mp hx)

end LinearMap

namespace AdicCompletion

variable {R : Type*} [CommRing R] {I : Ideal R}
variable {M N P : Type*} [AddCommGroup M] [Module R M]
  [AddCommGroup N] [Module R N] [AddCommGroup P] [Module R P]
variable {f : M →ₗ[R] N} {g : N →ₗ[R] P}

/-- Completion preserves injectivity whenever the induced filtration is bounded above by a
fixed shift of the adic filtration. The comparison itself also allows a noninjective `f`
whose kernel lies in every power of `I`. -/
theorem map_injective_of_comap_pow_smul_top_le {k : ℕ}
    (hbound : ∀ n, (I ^ (n + k) • (⊤ : Submodule R N)).comap f ≤ I ^ n • ⊤) :
    Function.Injective (map I f) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro x hx
  apply AdicCompletion.ext
  intro n
  obtain ⟨a, ha⟩ := Submodule.Quotient.mk_surjective _ (x.val (n + k))
  have hfa : f a ∈ I ^ (n + k) • (⊤ : Submodule R N) := by
    apply (Submodule.Quotient.mk_eq_zero _).mp
    have hz := congrArg (fun z ↦ z.val (n + k)) hx
    simpa only [map_val_apply, ← ha, LinearMap.reduceModIdeal_apply, val_zero, Pi.zero_apply]
      using hz
  have ha' : a ∈ I ^ n • (⊤ : Submodule R M) := hbound n hfa
  rw [← x.property (Nat.le_add_right n k), ← ha]
  simpa using (Submodule.Quotient.mk_eq_zero _).mpr ha'

/-- Completion preserves a right exact sequence if the induced filtration on the first
module is bounded above by a fixed shift of its adic filtration. No finite-generation or
Noetherian assumption is needed. -/
theorem map_exact_of_comap_pow_smul_top_le {k : ℕ}
    (hfg : Function.Exact f g) (hg : Function.Surjective g)
    (hbound : ∀ n, (I ^ (n + k) • (⊤ : Submodule R N)).comap f ≤ I ^ n • ⊤) :
    Function.Exact (map I f) (map I g) := by
  classical
  refine LinearMap.exact_of_comp_eq_zero_of_ker_le_range ?_ fun y hy ↦ ?_
  · rw [map_comp, hfg.linearMap_comp_eq_zero, map_zero]
  -- Lift the residue at level `n + k` to the first module; the shift makes these lifts Cauchy.
  have hpre (n : ℕ) : ∃ a : M,
      Submodule.Quotient.mk (p := I ^ (n + k) • (⊤ : Submodule R N)) (f a) =
        y.val (n + k) := by
    have hz : g.reduceModIdeal (I ^ (n + k)) (y.val (n + k)) = 0 := by
      simpa only [map_val_apply, val_zero, Pi.zero_apply]
        using congrArg (fun z ↦ z.val (n + k)) hy
    rw [← Ideal.mapQSMulTop_eq_reduceModIdeal] at hz
    obtain ⟨a, ha⟩ := (Ideal.mapQSMulTop_exact (I ^ (n + k)) hfg hg _).mp hz
    obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective _ a
    exact ⟨a, by simpa only [Ideal.mapQSMulTop_mk] using ha⟩
  choose a ha using hpre
  have hres {m n : ℕ} (hmn : m ≤ n) :
      Submodule.Quotient.mk (p := I ^ (m + k) • (⊤ : Submodule R N)) (f (a n)) =
        y.val (m + k) := by
    have h := congrArg (transitionMap I N (Nat.add_le_add_right hmn k)) (ha n)
    simpa only [← Submodule.mkQ_apply, Submodule.factor_mk, y.property] using h
  have hsmall {m n : ℕ} (hmn : m ≤ n) :
      a n - a m ∈ I ^ m • (⊤ : Submodule R M) := by
    apply hbound m
    rw [Submodule.mem_comap]
    apply (Submodule.Quotient.mk_eq_zero _).mp
    simp only [map_sub, Submodule.Quotient.mk_sub, hres hmn, ha m, sub_self]
  let x := AdicCauchySequence.mk I M a fun n ↦ SModEq.symm (SModEq.sub_mem.mpr
    (hsmall (Nat.le_succ n)))
  refine ⟨mk I M x, AdicCompletion.ext fun n ↦ ?_⟩
  have h := congrArg (transitionMap I N (Nat.le_add_right n k)) (ha n)
  simp only [x, map_val_apply, mk_apply_coe, AdicCauchySequence.mk_coe,
    Submodule.mkQ_apply, LinearMap.reduceModIdeal_apply]
  simpa only [← Submodule.mkQ_apply, Submodule.factor_mk, y.property] using h

/-- If a linear map is injective modulo every power of an ideal, its completion is injective. -/
theorem map_injective_of_reduceModIdeal_injective
    (hf : ∀ n : ℕ, Function.Injective (f.reduceModIdeal (I ^ n))) :
    Function.Injective (map I f) := by
  apply map_injective_of_comap_pow_smul_top_le (k := 0)
  simpa only [Nat.add_zero] using
    fun n ↦ LinearMap.comap_smul_top_le_of_reduceModIdeal_injective (hf n)

/-- Completion preserves a right exact sequence if its first map is injective modulo every
power of the defining ideal. No finiteness hypothesis is needed. -/
theorem map_exact_of_reduceModIdeal_injective
    (hfg : Function.Exact f g) (hg : Function.Surjective g)
    (hf : ∀ n : ℕ, Function.Injective (f.reduceModIdeal (I ^ n))) :
    Function.Exact (map I f) (map I g) := by
  apply map_exact_of_comap_pow_smul_top_le (k := 0) hfg hg
  simpa only [Nat.add_zero] using
    fun n ↦ LinearMap.comap_smul_top_le_of_reduceModIdeal_injective (hf n)

end AdicCompletion

namespace AdicCompletion

variable {R : Type*} [CommRing R]
variable {M N P : Type*} [AddCommGroup M] [Module R M]
  [AddCommGroup N] [Module R N] [AddCommGroup P] [Module R P]
variable {f : M →ₗ[R] N} {g : N →ₗ[R] P} {r : R} {k : ℕ}

/-- Principal-adic completion preserves injectivity on the left of an exact sequence when the
last term has bounded `r`-power torsion. Surjectivity of the second map is not required. -/
theorem map_span_singleton_injective_of_bounded_torsion (hf : Function.Injective f)
    (hfg : Function.Exact f g)
    (htors : ∀ (n : ℕ) (x : P), r ^ n • x = 0 → r ^ k • x = 0) :
    Function.Injective (map (Ideal.span {r}) f) :=
  map_injective_of_comap_pow_smul_top_le
    (LinearMap.comap_pow_smul_top_le_of_bounded_torsion hf hfg htors)

/-- Principal-adic completion preserves a right exact sequence whose last term has bounded
`r`-power torsion. Injectivity of the first map is not required. For a short exact sequence,
use `map_span_singleton_injective_of_bounded_torsion` for injectivity on the left and
`map_surjective` for surjectivity on the right. -/
theorem map_span_singleton_exact_of_bounded_torsion
    (hfg : Function.Exact f g) (hg : Function.Surjective g)
    (htors : ∀ (n : ℕ) (x : P), r ^ n • x = 0 → r ^ k • x = 0) :
    Function.Exact (map (Ideal.span {r}) f) (map (Ideal.span {r}) g) := by
  have hfg' : Function.Exact f.range.subtype g := by
    apply f.surjective_rangeRestrict.comp_exact_iff_exact.mp
    rwa [f.subtype_comp_rangeRestrict]
  have he := map_exact_of_comap_pow_smul_top_le hfg' hg
    (LinearMap.comap_pow_smul_top_le_of_bounded_torsion f.range.injective_subtype hfg' htors)
  rw [← f.subtype_comp_rangeRestrict, ← map_comp]
  exact (map_surjective _ f.surjective_rangeRestrict).comp_exact_iff_exact.mpr he

/-- A short exact sequence whose last term is `r`-torsion-free remains injective on the left
after `(r)`-adic completion. The modules need not be finite. -/
theorem map_span_singleton_injective_of_isSMulRegular
    (hf : Function.Injective f) (hfg : Function.Exact f g) (hr : IsSMulRegular P r) :
    Function.Injective (map (Ideal.span {r}) f) :=
  map_span_singleton_injective_of_bounded_torsion (k := 0) hf hfg
    fun n x h ↦ by simpa using (hr.pow n).right_eq_zero_of_smul h

/-- Principal-adic completion preserves a right exact sequence when the parameter acts
injectively on the last term, without any Noetherian or finite-generation assumption. Together
with `map_span_singleton_injective_of_isSMulRegular` and `map_surjective`, this also gives all
three parts of short exactness when the first map is injective. -/
theorem map_span_singleton_exact_of_isSMulRegular
    (hfg : Function.Exact f g) (hg : Function.Surjective g) (hr : IsSMulRegular P r) :
    Function.Exact (map (Ideal.span {r}) f) (map (Ideal.span {r}) g) :=
  map_span_singleton_exact_of_bounded_torsion (k := 0) hfg hg
    fun n x h ↦ by simpa using (hr.pow n).right_eq_zero_of_smul h

/-- Principal-adic completion preserves exactness of the kernel sequence for a map whose
range and cokernel have bounded `r`-power torsion. Every element in the kernel of the
completed map comes from the completion of the original kernel. -/
theorem map_span_singleton_exact_ker_subtype_of_bounded_torsion {j : ℕ}
    (htorsRange : ∀ (n : ℕ) (x : f.range), r ^ n • x = 0 → r ^ j • x = 0)
    (htors : ∀ (n : ℕ) (x : N ⧸ f.range), r ^ n • x = 0 → r ^ k • x = 0) :
    Function.Exact (map (Ideal.span {r}) f.ker.subtype) (map (Ideal.span {r}) f) := by
  have hinj := map_span_singleton_injective_of_bounded_torsion f.range.injective_subtype
    (LinearMap.exact_subtype_mkQ f.range) htors
  have hex : Function.Exact f.ker.subtype f.rangeRestrict :=
    LinearMap.exact_iff.mpr (by simp)
  have he := map_span_singleton_exact_of_bounded_torsion hex f.surjective_rangeRestrict
    htorsRange
  rw [← f.subtype_comp_rangeRestrict, ← map_comp]
  exact hinj.comp_exact_iff_exact.mpr he

end AdicCompletion
