/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.AdicCompletion.Exactness
-- Proof-only: identify the ideal-linear reduction with Mathlib's `reduceModIdeal`.
import all TauCeti.RingTheory.QuotSMulTop

/-!
# Exactness of principal-adic completion with bounded torsion

Let `M → N → P → 0` be exact. If the torsion in `P` killed by powers of `r` is
annihilated by one fixed power of `r`, and the first map is injective, then `(r)`-adic
completion preserves exactness and injectivity. The modules need not be finite and the
ring need not be Noetherian. This extends the torsion-free last-term criterion.

The argument first treats a general ideal: a uniform shift comparing the induced filtration
on `M` with its adic filtration suffices for exactness. For a principal ideal, bounded torsion
in `P` supplies this shift. In particular, completion commutes with kernels of maps into an
`r`-torsion-free module when the cokernel has bounded `r`-power torsion.

These comparisons are used when completing complexes of sections: bounded torsion in the
next cohomology group controls the discrepancy between reduction of a kernel and the kernel
of reduction. This is the algebraic filtration step in the formal-section comparisons of
Stacks, Lemmas 52.3.2 (0BLD) and 52.12.7 (0EII); no sheaf-cohomology comparison is asserted here.

The proof uses the compatible-residue model of completion due to Judith Ludwig and Christian
Merten in Mathlib. The filtration argument parallels Mathlib's finite-module exactness proof,
replacing its Artin–Rees input with an explicit bound.
-/

public section

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
    have hz : g.reduceModIdeal (I ^ (n + k)) (y.val (n + k)) = 0 :=
      congrArg (fun z ↦ z.val (n + k)) hy
    obtain ⟨a, ha⟩ := (Ideal.mapQSMulTop_exact (I ^ (n + k)) hfg hg _).mp hz
    obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective _ a
    exact ⟨a, ha⟩
  choose a ha using hpre
  have hres {m n : ℕ} (hmn : m ≤ n) :
      Submodule.Quotient.mk (p := I ^ (m + k) • (⊤ : Submodule R N)) (f (a n)) =
        y.val (m + k) := by
    have h := congrArg (transitionMap I N (Nat.add_le_add_right hmn k)) (ha n)
    simpa only [Submodule.factor, Submodule.mapQ_apply, LinearMap.id_apply, y.property] using h
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
  simpa only [x, map_val_apply, mk_apply_coe, AdicCauchySequence.mk_coe,
    Submodule.mkQ_apply, LinearMap.reduceModIdeal_apply, Submodule.factor,
    Submodule.mapQ_apply, LinearMap.id_apply, y.property] using h

end AdicCompletion

namespace LinearMap

variable {R : Type*} [CommRing R]
variable {M N P : Type*} [AddCommGroup M] [Module R M]
  [AddCommGroup N] [Module R N] [AddCommGroup P] [Module R P]
variable {f : M →ₗ[R] N} {g : N →ₗ[R] P} {r : R} {k : ℕ}

/-- Bounded `r`-power torsion in the last term of an exact sequence gives a uniform comparison
between the induced filtration on the first term and its `(r)`-adic filtration. -/
theorem comap_pow_smul_top_le_of_bounded_torsion (hf : Function.Injective f)
    (hfg : Function.Exact f g)
    (htors : ∀ (n : ℕ) (x : P), r ^ n • x = 0 → r ^ k • x = 0) (n : ℕ) :
    ((Ideal.span {r}) ^ (n + k) • (⊤ : Submodule R N)).comap f ≤
      (Ideal.span {r}) ^ n • (⊤ : Submodule R M) := by
  intro x hx
  simp only [Submodule.mem_comap, Ideal.span_singleton_pow,
    Submodule.ideal_span_singleton_smul, Submodule.mem_smul_pointwise_iff_exists,
    Submodule.mem_top, true_and] at hx ⊢
  obtain ⟨y, hy⟩ := hx
  have hgy : r ^ (n + k) • g y = 0 := by
    rw [← g.map_smul, hy]
    exact (hfg (f x)).mpr ⟨x, rfl⟩
  obtain ⟨z, hz⟩ := (hfg (r ^ k • y)).mp (by
    rw [g.map_smul]
    exact htors (n + k) (g y) hgy)
  refine ⟨z, hf ?_⟩
  rw [f.map_smul, hz, smul_smul, ← pow_add, hy]

end LinearMap

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
  have hf : map (Ideal.span {r}) f =
      map (Ideal.span {r}) f.range.subtype ∘ₗ map (Ideal.span {r}) f.rangeRestrict := by
    rw [map_comp, f.subtype_comp_rangeRestrict]
  rw [hf]
  exact (map_surjective _ f.surjective_rangeRestrict).comp_exact_iff_exact.mpr he

/-- Principal-adic completion preserves exactness of the kernel sequence for a map into an
`r`-torsion-free module with bounded `r`-power torsion in its cokernel. Every element in the
kernel of the completed map comes from the completion of the original kernel. -/
theorem map_span_singleton_exact_ker_subtype_of_bounded_torsion
    (hr : IsSMulRegular N r)
    (htors : ∀ (n : ℕ) (x : N ⧸ f.range), r ^ n • x = 0 → r ^ k • x = 0) :
    Function.Exact (map (Ideal.span {r}) f.ker.subtype) (map (Ideal.span {r}) f) := by
  have hinj := map_span_singleton_injective_of_bounded_torsion f.range.injective_subtype
    (LinearMap.exact_subtype_mkQ f.range) htors
  have hex : Function.Exact f.ker.subtype f.rangeRestrict :=
    LinearMap.exact_iff.mpr (by simp)
  have he := map_span_singleton_exact_of_isSMulRegular hex f.surjective_rangeRestrict
    (hr.submodule f.range)
  have hf : map (Ideal.span {r}) f =
      map (Ideal.span {r}) f.range.subtype ∘ₗ map (Ideal.span {r}) f.rangeRestrict := by
    rw [map_comp, f.subtype_comp_rangeRestrict]
  rw [hf]
  exact hinj.comp_exact_iff_exact.mpr he

end AdicCompletion
