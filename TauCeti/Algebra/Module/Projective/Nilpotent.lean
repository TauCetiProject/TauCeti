/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.Projective
public import Mathlib.Algebra.Module.Torsion.Basic

import Mathlib.LinearAlgebra.Finsupp.VectorSpace
import Mathlib.LinearAlgebra.Isomorphisms
import Mathlib.RingTheory.Ideal.Quotient.Operations
import TauCeti.Algebra.Module.LinearMap.EndQuotient
import TauCeti.RingTheory.Ideal.Operations

/-!
# Lifting projectivity along a nilpotent element

Let `ϖ` be a nilpotent element of a commutative ring `A` and `M` an `A`-module. If the reduction
`M ⧸ ϖ M` is projective over `A ⧸ ϖ A` and `M` has no `ϖ`-torsion beyond the forced one, that is,
every `x` with `ϖ x = 0` lies in `ann(ϖ) • M`, then `M` is projective over `A`. The torsion
condition says that `Tor₁^A(A ⧸ ϖ A, M)` vanishes, and it holds when `M` is flat over `A`, or, as
for modules over truncated Witt vectors, when `M` is flat over a subring `ℤ ⧸ pⁿ` containing `ϖ`.

No finiteness is assumed. Write `M` as a quotient of a free module `F` with kernel `K`. The
torsion condition gives `K ∩ ϖ F = ϖ K`, so that a splitting of the reduction
`F ⧸ ϖ F → M ⧸ ϖ M` yields a map `r₀ : F → K` that restricts to the identity of `K` modulo `ϖ K`.
Then `r₀|_K` differs from the identity by a nilpotent endomorphism of `K`, so it is invertible,
and composing `r₀` with its inverse retracts `F` onto `K`. Hence `M` is a direct summand of `F`.

## Main results

* `Module.Projective.of_quotient_smul_top`: a module whose reduction modulo a nilpotent element
  `ϖ` is projective and whose `ϖ`-torsion lies in `ann(ϖ) • M` is projective.

## References

* K. S. Kedlaya and R. Liu, *Relative p-adic Hodge theory: foundations*, Astérisque 371 (2015),
  proof of Proposition 3.2.13.
-/

public section

open Submodule

namespace Module.Projective

variable {A M : Type*} [CommRing A] [AddCommGroup M] [Module A M] {ϖ : A}

variable {ι F : Type*} [AddCommGroup F] [Module A F] {π : F →ₗ[A] M}

/-- For a cover `π : F → M`, the torsion condition on `M` gives `K ∩ ϖ F = ϖ K`, where `K` is the
kernel of `π`. -/
private theorem exists_mem_ker_smul_eq (hπ : Function.Surjective π)
    (hM : ∀ x : M, ϖ • x = 0 → x ∈ (Ideal.span {ϖ}).annihilator • (⊤ : Submodule A M))
    (c : F) (hc : π (ϖ • c) = 0) : ∃ k ∈ LinearMap.ker π, ϖ • k = ϖ • c := by
  rw [map_smul] at hc
  have hmem : π c ∈ ((Ideal.span {ϖ}).annihilator • (⊤ : Submodule A F)).map π := by
    rw [map_smul'', Submodule.map_top, LinearMap.range_eq_top.mpr hπ]
    exact hM _ hc
  obtain ⟨d, hd, hdc⟩ := hmem
  have hϖd : ϖ • d = 0 := by
    refine (smul_le (P := LinearMap.ker (LinearMap.lsmul A F ϖ))).mpr (fun r hr y _ ↦ ?_) hd
    have hrϖ : r * ϖ = 0 := (mem_annihilator_span_singleton ϖ r).mp hr
    rw [LinearMap.mem_ker, LinearMap.lsmul_apply, smul_smul, mul_comm, hrϖ, zero_smul]
  exact ⟨c - d, by simp [hdc], by rw [smul_sub, hϖd, sub_zero]⟩

/-- If `M ⧸ ϖ M` is projective, the kernel `K` of a free cover `π : F → M` admits a map
`F → K` that restricts to the identity of `K` modulo `ϖ F`. -/
private theorem exists_linearMap_ker_sub_mem (b : Basis ι A F) (hπ : Function.Surjective π)
    [Projective (A ⧸ Ideal.span {ϖ}) (M ⧸ Ideal.span {ϖ} • (⊤ : Submodule A M))] :
    ∃ r₀ : F →ₗ[A] LinearMap.ker π, ∀ x : LinearMap.ker π,
      (x : F) - r₀ x ∈ Ideal.span {ϖ} • (⊤ : Submodule A F) := by
  set I := Ideal.span {ϖ}
  set K := LinearMap.ker π
  -- A splitting `s` of the reduction of `π` modulo `ϖ`.
  let πbar : (F ⧸ I • (⊤ : Submodule A F)) →ₗ[A ⧸ I] (M ⧸ I • (⊤ : Submodule A M)) :=
    (mapQ _ _ π (smul_top_le_comap_smul_top I π)).extendScalarsOfSurjective
      Ideal.Quotient.mk_surjective
  have hπbar : Function.Surjective πbar := by
    rintro ⟨m⟩
    obtain ⟨c, rfl⟩ := hπ m
    exact ⟨Submodule.Quotient.mk c, rfl⟩
  obtain ⟨s, hs⟩ := projective_lifting_property πbar LinearMap.id hπbar
  -- For each basis vector `b i`, an element `k i ∈ K` with `[b i - k i] = s [π (b i)]`.
  have key : ∀ i, ∃ k : K, (Submodule.Quotient.mk (b i - (k : F)) : F ⧸ I • (⊤ : Submodule A F)) =
      s (Submodule.Quotient.mk (π (b i))) := by
    intro i
    obtain ⟨f, hf⟩ := Submodule.Quotient.mk_surjective _ (s (Submodule.Quotient.mk (π (b i))))
    have hπf : (Submodule.Quotient.mk (π f) : M ⧸ I • (⊤ : Submodule A M)) =
        Submodule.Quotient.mk (π (b i)) := by
      have := LinearMap.congr_fun hs (Submodule.Quotient.mk (π (b i)))
      rwa [LinearMap.comp_apply, ← hf] at this
    obtain ⟨y, hy⟩ := mem_span_singleton_smul_top_iff.mp
      ((Submodule.Quotient.eq _).mp hπf.symm)
    obtain ⟨c, rfl⟩ := hπ y
    refine ⟨⟨b i - f - ϖ • c, ?_⟩, ?_⟩
    · simp [K, ← hy]
    · rw [← hf, Submodule.Quotient.eq]
      exact mem_span_singleton_smul_top_iff.mpr ⟨c, by rw [Submodule.coe_mk]; abel⟩
  choose k hk using key
  -- The map `r₀ : F → K` sending `b i` to `k i` satisfies `[c - r₀ c] = s [π c]`.
  let r₀ : F →ₗ[A] K := b.constr A k
  have hr₀ : (I • (⊤ : Submodule A F)).mkQ ∘ₗ (LinearMap.id - K.subtype ∘ₗ r₀) =
      s.restrictScalars A ∘ₗ (I • (⊤ : Submodule A M)).mkQ ∘ₗ π :=
    b.ext fun i ↦ by simpa [r₀] using hk i
  refine ⟨r₀, fun x ↦ (Submodule.Quotient.mk_eq_zero _).mp ?_⟩
  have := LinearMap.congr_fun hr₀ x
  simp only [LinearMap.comp_apply, LinearMap.sub_apply, LinearMap.id_apply, mkQ_apply,
    Submodule.subtype_apply] at this
  rw [this, LinearMap.mem_ker.mp x.property, Submodule.Quotient.mk_zero, map_zero]

/-- The main argument, for a cover `π : F → M` by a free module `F` with basis `b`. It is stated
for an abstract `F`, rather than for `M →₀ A`, because instance search does not find the ring
structure on the endomorphisms of a submodule of `M →₀ A`. -/
private theorem of_quotient_smul_top_of_surjective (b : Basis ι A F) (hπ : Function.Surjective π)
    (hϖ : IsNilpotent ϖ)
    [Projective (A ⧸ Ideal.span {ϖ}) (M ⧸ Ideal.span {ϖ} • (⊤ : Submodule A M))]
    (hM : ∀ x : M, ϖ • x = 0 → x ∈ (Ideal.span {ϖ}).annihilator • (⊤ : Submodule A M)) :
    Projective A M := by
  set K := LinearMap.ker π
  have := Projective.of_basis b
  have hI : IsNilpotent (Ideal.span {ϖ}) := by
    obtain ⟨n, hn⟩ := hϖ
    exact ⟨n, by simp [Ideal.span_singleton_pow, hn]⟩
  -- A map `r₀ : F → K` which is the identity on `K` modulo `ϖ K` restricts to a unit of `End K`.
  obtain ⟨r₀, hr₀⟩ := exists_linearMap_ker_sub_mem (ϖ := ϖ) b hπ
  have hu : IsUnit (r₀ ∘ₗ K.subtype) := by
    refine Ideal.isUnit_of_endMapQ_eq_one _ K hI
      (Submodule.linearMap_qext _ (LinearMap.ext fun x ↦ ?_))
    simp only [LinearMap.comp_apply, mkQ_apply, Ideal.endMapQ_mk, one_apply_eq_self]
    rw [Submodule.Quotient.eq]
    obtain ⟨c, hc⟩ := mem_span_singleton_smul_top_iff.mp (hr₀ x)
    obtain ⟨y, hyK, hy⟩ := exists_mem_ker_smul_eq hπ hM c (by
      rw [hc, map_sub, LinearMap.mem_ker.mp x.property, LinearMap.mem_ker.mp (r₀ x).property,
        sub_zero])
    refine mem_span_singleton_smul_top_iff.mpr ⟨-⟨y, hyK⟩, Subtype.ext ?_⟩
    simp [hy, hc]
  -- Hence `F` retracts onto `K`, and `π` has a section.
  let r : F →ₗ[A] K := ↑hu.unit⁻¹ ∘ₗ r₀
  have hr : ∀ x : K, r x = x := fun x ↦ by
    have h := LinearMap.congr_fun hu.unit.inv_mul x
    rwa [mul_apply_eq_comp, IsUnit.unit_spec, one_apply_eq_self] at h
  let t : F →ₗ[A] F := LinearMap.id - K.subtype ∘ₗ r
  have ht : K ≤ LinearMap.ker t := fun x hx ↦ by simp [t, hr ⟨x, hx⟩]
  refine Projective.of_split (K.liftQ t ht ∘ₗ (π.quotKerEquivOfSurjective hπ).symm.toLinearMap) π
    (LinearMap.ext fun m ↦ ?_)
  obtain ⟨c, rfl⟩ := hπ m
  have hsymm : (π.quotKerEquivOfSurjective hπ).symm (π c) = K.mkQ c := by
    rw [LinearEquiv.symm_apply_eq, mkQ_apply, LinearMap.quotKerEquivOfSurjective_apply_mk]
  simp [hsymm, t, LinearMap.mem_ker.mp (r c).property]

/-- **Projectivity lifts along a nilpotent element.** Let `ϖ` be nilpotent in `A`. If
`M ⧸ ϖ M` is projective over `A ⧸ ϖ A` and every element of `M` killed by `ϖ` lies in
`ann(ϖ) • M`, then `M` is projective over `A`. -/
theorem of_quotient_smul_top (hϖ : IsNilpotent ϖ)
    [Projective (A ⧸ Ideal.span {ϖ}) (M ⧸ Ideal.span {ϖ} • (⊤ : Submodule A M))]
    (hM : ∀ x : M, ϖ • x = 0 → x ∈ (Ideal.span {ϖ}).annihilator • (⊤ : Submodule A M)) :
    Projective A M :=
  of_quotient_smul_top_of_surjective (Finsupp.basisSingleOne (R := A) (ι := M))
    (Finsupp.linearCombination_id_surjective A M) hϖ hM

end Module.Projective
