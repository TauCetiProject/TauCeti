/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.AdicCompletion.Basic
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic
import TauCeti.RingTheory.LocalRing.AlgHom

/-!
# Adic uniqueness of algebra homomorphisms

We record an elementary adic uniqueness principle for `k`-algebra homomorphisms into an adically
separated commutative ring (`IsHausdorff J S`).

In `AlgHom.sub_mem_pow_of_eqOn`, if `G` generates an ideal modulo which every element of `R` is
represented by a scalar in `k`, and `φ, ψ : R →ₐ[k] S` agree on `G` with `φ` mapping `G` into an
ideal `J` of `S`, then `φ r - ψ r ∈ J ^ n` for every `n : ℕ` and `r : R`, without assuming `R` is
commutative or local. Under the additional separatedness hypothesis `IsHausdorff J S`,
`AlgHom.ext_of_isHausdorff` concludes `φ = ψ`.

Specializing to commutative local `k`-algebras `R` and `S` where
`algebraMap k (IsLocalRing.ResidueField R)` is surjective, `S` is maximal-ideal separated
(`IsHausdorff (IsLocalRing.maximalIdeal S) S`), and one of the homomorphisms (`φ`) is local
(`IsLocalHom φ`), `AlgHom.ext_of_span_eq_maximalIdeal` deduces `φ = ψ` from agreement on any
generating set of `IsLocalRing.maximalIdeal R`, even when `R` is not finitely generated as a
`k`-algebra (as for rings of analytic germs or formal power series).

## Main results

* `AlgHom.sub_mem_pow_of_eqOn`: `φ r - ψ r ∈ J ^ n` for all `n` and `r`, when `G` generates an
  ideal modulo which every element of `R` is represented by a scalar in `k`, `φ` maps `G` into `J`,
  and `φ, ψ` agree on `G`.
* `AlgHom.ext_of_isHausdorff`: `φ = ψ` under the same hypotheses together with `IsHausdorff J S`.
* `AlgHom.ext_of_span_eq_maximalIdeal`: specialization to commutative local `k`-algebras `R` and
  `S`, giving `φ = ψ` from agreement on a generating set of `IsLocalRing.maximalIdeal R` when
  `algebraMap k (IsLocalRing.ResidueField R)` is surjective, `S` is maximal-ideal separated
  (`IsHausdorff`), and `φ` is local.

## References

* H. Grauert and R. Remmert, *Coherent Analytic Sheaves*, Grundlehren der mathematischen
  Wissenschaften 265, Springer, 1984, Chapter 1, §1.
* N. Bourbaki, *Commutative Algebra*, Chapter III, §2 (for `I`-adic congruences and uniqueness of
  homomorphisms into adically separated targets) and §3 (for the local-ring specialization and
  maximal-ideal generators).
-/

public section

namespace AlgHom

/-- **Adic congruences from generators modulo which every element is a scalar.** Suppose `G`
generates an ideal modulo which every element of `R` is represented by a scalar in `k`, and
`φ, ψ : R →ₐ[k] S` agree on `G` and map `G` into an ideal `J` of `S`. Then `φ r - ψ r ∈ J ^ n`
for every `n : ℕ` and `r : R`. -/
theorem sub_mem_pow_of_eqOn {k R S : Type*} [CommSemiring k] [Ring R] [CommRing S]
    [Algebra k R] [Algebra k S] {φ ψ : R →ₐ[k] S} {G : Set R} {J : Ideal S}
    (haug : ∀ r : R, ∃ c : k, r - algebraMap k R c ∈ Ideal.span G)
    (hGJ : ∀ g ∈ G, φ g ∈ J) (hG : Set.EqOn φ ψ G) :
    ∀ (n : ℕ) (r : R), φ r - ψ r ∈ J ^ n
  | 0, _ => by simp
  | n + 1, r => by
    have hψJ : Ideal.span G ≤ J.comap ψ.toRingHom :=
      Ideal.span_le.2 fun g hg ↦ Ideal.mem_comap.2 (hG hg ▸ hGJ g hg)
    obtain ⟨c, hc⟩ := haug r
    have hrc : φ r - ψ r = φ (r - algebraMap k R c) - ψ (r - algebraMap k R c) := by simp
    rw [hrc]
    refine Submodule.span_induction (p := fun x _ ↦ φ x - ψ x ∈ J ^ (n + 1))
      (fun g hg ↦ by simp [hG hg]) (by simp)
      (fun x y _ _ hx hy ↦ by simpa only [map_add, sub_add_sub_comm] using add_mem hx hy)
      (fun a x hx ihx ↦ ?_) hc
    have hsplit : φ (a • x) - ψ (a • x) = φ a * (φ x - ψ x) + (φ a - ψ a) * ψ x := by
      simp only [smul_eq_mul, map_mul, mul_sub, sub_mul, sub_add_sub_cancel]
    rw [hsplit]
    exact add_mem (Ideal.mul_mem_left _ (φ a) ihx)
      (pow_succ J n ▸ Ideal.mul_mem_mul (sub_mem_pow_of_eqOn haug hGJ hG n a) (hψJ hx))

/-- **Uniqueness of `k`-algebra homomorphisms into an adically separated ring.** Suppose `G`
generates an ideal modulo which every element of `R` is represented by a scalar in `k`, and `S` is
`IsHausdorff J S` for an ideal `J` of `S`. If `φ, ψ : R →ₐ[k] S` agree on `G` and map `G` into
`J`, then `φ = ψ`. -/
theorem ext_of_isHausdorff {k R S : Type*} [CommSemiring k] [Ring R] [CommRing S]
    [Algebra k R] [Algebra k S] {φ ψ : R →ₐ[k] S} {G : Set R} (J : Ideal S) [IsHausdorff J S]
    (haug : ∀ r : R, ∃ c : k, r - algebraMap k R c ∈ Ideal.span G)
    (hGJ : ∀ g ∈ G, φ g ∈ J) (hG : Set.EqOn φ ψ G) :
    φ = ψ :=
  AlgHom.coe_fn_injective <| IsHausdorff.funext' J fun n r ↦
    Ideal.Quotient.eq.2 (sub_mem_pow_of_eqOn haug hGJ hG n r)

/-- **Uniqueness of `k`-algebra homomorphisms of local rings from maximal-ideal generators.** Let
`R` and `S` be commutative local `k`-algebras such that `algebraMap k (ResidueField R)` is
surjective and `S` is separated (`IsHausdorff`) with respect to its maximal ideal. If `G` generates
`maximalIdeal R` and `φ, ψ : R →ₐ[k] S` agree on `G` with `φ` local (no locality assumption on `ψ`
is needed), then `φ = ψ`. -/
theorem ext_of_span_eq_maximalIdeal {k R S : Type*} [CommRing k] [CommRing R] [IsLocalRing R]
    [CommRing S] [IsLocalRing S] [Algebra k R] [Algebra k S]
    [IsHausdorff (IsLocalRing.maximalIdeal S) S] {φ ψ : R →ₐ[k] S} [IsLocalHom φ]
    (hres : Function.Surjective (algebraMap k (IsLocalRing.ResidueField R)))
    {G : Set R} (hG_span : Ideal.span G = IsLocalRing.maximalIdeal R)
    (hG : Set.EqOn φ ψ G) :
    φ = ψ := by
  have : IsLocalHom φ.toRingHom := ⟨IsLocalHom.map_nonunit (f := φ)⟩
  refine ext_of_isHausdorff (IsLocalRing.maximalIdeal S) (fun r ↦ ?_) (fun g hg ↦ ?_) hG
  · obtain ⟨c, hc⟩ := hres (IsLocalRing.residue R r)
    refine ⟨c, hG_span.symm ▸ (IsLocalRing.residue_eq_zero_iff _).1 ?_⟩
    rw [map_sub, TauCeti.residue_algebraMap, hc, sub_self]
  · exact map_nonunit φ.toRingHom g (hG_span ▸ Ideal.subset_span hg)

end AlgHom
