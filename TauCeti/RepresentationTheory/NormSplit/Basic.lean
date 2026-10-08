/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.RepresentationTheory.Equiv
public import Mathlib.RepresentationTheory.Rep.Iso
public import TauCeti.RepresentationTheory.RelativeNorm

/-!
# Representations whose identity is a norm

Let `ρ` be a representation of a finite group `G` on a `k`-module `V`. The group acts on
`End_k(V)` by conjugation (`Representation.linHom ρ ρ`), and the norm of this action sends `φ` to
`x ↦ ∑ g, ρ g (φ (ρ g⁻¹ x))`. When the identity of `V` is such a norm, `V` is a direct summand of
the induced module `k[G] ⊗_k V`; if moreover `V` is projective over `k`, then `V` is a
projective `k[G]`-module. This is the easy direction of Higman's criterion, and the way the
theorem of Nakayama and Rim produces projective modules (Serre, *Local Fields*, IX §§3–5).

Whether the identity is a norm can be decided one prime divisor of `|G|` at a time: if for every
such prime `p` some subgroup of index prime to `p` has the identity as a norm, then so does `G`.

## Main statements

* `Representation.norm_linHom_apply`: the norm of the conjugation action on `End_k(V)`.
* `Representation.index_nsmul_id_mem_range_norm_linHom`: if the identity is an `H`-norm, then
  `[G : H]` times the identity is a `G`-norm.
* `Representation.id_mem_range_norm_linHom_of_forall_prime`: if for every prime divisor `p` of
  `|G|` the identity is a norm for a subgroup of index prime to `p`, then it is a `G`-norm.
* `Rep.projective_of_id_mem_range_norm_linHom`,
  `Rep.moduleProjective_of_id_mem_range_norm_linHom`: a representation that is projective over
  `k` and whose identity is a norm is projective, in `Rep k G` and as a `k[G]`-module.

## References

* J.-P. Serre, *Local Fields*, Chapter IX, §§3–5.
* K. S. Brown, *Cohomology of Groups*, Chapter VI, §8.
-/

public section

universe u

namespace Representation

variable {k G V : Type*} [CommRing k] [Group G] [Fintype G] [AddCommGroup V] [Module k V]
  (ρ : Representation k G V)

/-- The norm of the conjugation action of `G` on `End_k(V)` sends `φ` to
`x ↦ ∑ g, ρ g (φ (ρ g⁻¹ x))`. -/
theorem norm_linHom_apply (φ : V →ₗ[k] V) (x : V) :
    (linHom ρ ρ).norm φ x = ∑ g : G, ρ g (φ (ρ g⁻¹ x)) := by
  simp [Representation.norm, linHom_apply]

/-- If the identity of `V` is the norm of `φ` for the conjugation action of a subgroup `H`, then
`[G : H]` times the identity is the norm of `φ` for the conjugation action of `G`. -/
theorem index_nsmul_id_mem_range_norm_linHom (H : Subgroup G) [Fintype H]
    (h : LinearMap.id ∈ LinearMap.range (Representation.norm ((linHom ρ ρ).comp H.subtype))) :
    H.index • LinearMap.id ∈ LinearMap.range (linHom ρ ρ).norm := by
  classical
  obtain ⟨φ, hφ⟩ := h
  refine ⟨φ, ?_⟩
  have := Subgroup.fintypeQuotientOfFiniteIndex (H := H)
  -- The `G`-norm is the relative norm of the `H`-norm, which is `[G : H]` on fixed vectors.
  have hfix (g : G) : linHom ρ ρ g LinearMap.id = LinearMap.id := by
    ext x
    simp [← Module.End.mul_apply, ← map_mul]
  rw [← relNorm_norm_apply (H := H),
    ← relNorm_apply_of_forall_apply_eq (ρ := linHom ρ ρ) (H := H) hfix, ← hφ]
  congr!

/-- **The identity is a norm if it is one at every relevant prime.** If for every prime divisor `p`
of `|G|` the identity of `V` is a norm for the conjugation action of a subgroup of index prime to
`p`, then it is a norm for the conjugation action of `G`. -/
theorem id_mem_range_norm_linHom_of_forall_prime
    (h : ∀ p : ℕ, p.Prime → p ∣ Fintype.card G →
      ∃ (H : Subgroup G) (_ : Fintype H), ¬ p ∣ H.index ∧
      LinearMap.id ∈ LinearMap.range (Representation.norm ((linHom ρ ρ).comp H.subtype))) :
    LinearMap.id ∈ LinearMap.range (linHom ρ ρ).norm := by
  -- The ideal of integers `n` with `n • id` a norm.
  let J : Ideal ℤ := ((LinearMap.range (linHom ρ ρ).norm).restrictScalars ℤ).comap
    (LinearMap.toSpanSingleton ℤ _ (LinearMap.id : V →ₗ[k] V))
  have hJ : ∀ n : ℤ, n ∈ J ↔ n • (LinearMap.id : V →ₗ[k] V) ∈
      LinearMap.range (linHom ρ ρ).norm := fun n ↦ by
    simp [J]
  obtain ⟨n, hn⟩ := (Submodule.IsPrincipal.principal J)
  have hcard : (Fintype.card G : ℤ) ∈ J := by
    rw [hJ, natCast_zsmul]
    simpa [Subgroup.index_bot, Nat.card_eq_fintype_card] using
      index_nsmul_id_mem_range_norm_linHom ρ ⊥
        ⟨LinearMap.id, by ext x; simp [Representation.norm]⟩
  rw [hn, Ideal.submodule_span_eq, Ideal.mem_span_singleton] at hcard
  have hunit : IsUnit n := by
    rw [Int.isUnit_iff_natAbs_eq]
    by_contra hne
    obtain ⟨p, hp, hpn⟩ := Nat.exists_prime_and_dvd hne
    have hpG : p ∣ Fintype.card G :=
      Int.natCast_dvd_natCast.1 ((Int.ofNat_dvd_left.2 hpn).trans hcard)
    obtain ⟨H, _, hpH, hH⟩ := h p hp hpG
    have hmem : (H.index : ℤ) ∈ J := by
      rw [hJ, natCast_zsmul]
      exact index_nsmul_id_mem_range_norm_linHom ρ H hH
    rw [hn, Ideal.submodule_span_eq, Ideal.mem_span_singleton] at hmem
    exact hpH (Int.natCast_dvd_natCast.1 ((Int.ofNat_dvd_left.2 hpn).trans hmem))
  have h1 : (1 : ℤ) ∈ J := by
    rw [hn, Ideal.submodule_span_eq, Ideal.mem_span_singleton]
    exact hunit.dvd
  simpa using (hJ 1).1 h1

end Representation

namespace Rep

open CategoryTheory

/-- **A representation whose identity is a norm is projective.** If `A` is projective over `k` and
`id_A = ∑ g, A.ρ g ∘ φ ∘ A.ρ g⁻¹` for a `k`-linear `φ`, then `A` is projective. -/
theorem projective_of_id_mem_range_norm_linHom {k G : Type u} [CommRing k] [Group G] [Fintype G]
    (A : Rep.{u} k G) [Module.Projective k A.V]
    (h : LinearMap.id ∈ LinearMap.range (Representation.linHom A.ρ A.ρ).norm) : Projective A := by
  classical
  obtain ⟨φ, hφ⟩ := h
  have hφ' (x : A.V) : x = ∑ g : G, A.ρ g (φ (A.ρ g⁻¹ x)) := by
    rw [← Representation.norm_linHom_apply, hφ, LinearMap.id_apply]
  -- `A` is a retract of the free representation on the underlying set of `A`.
  obtain ⟨σ, hσ⟩ := Module.projective_def'.1 (inferInstance : Module.Projective k A.V)
  let ι := A.V
  let r : free k G ι ⟶ A := freeLift (k := k) (G := G) (A := A) id
  -- `e` sends a vector to a `k`-linear splitting of it, placed at `1 ∈ G`; `r` undoes it.
  let e : A.V →ₗ[k] (ι →₀ MonoidAlgebra k G) :=
    Finsupp.mapRange.linearMap (MonoidAlgebra.lsingle 1) ∘ₗ σ
  have he (x : A.V) : r.hom (e x) = x := by
    have : r.hom.toLinearMap ∘ₗ Finsupp.mapRange.linearMap (MonoidAlgebra.lsingle 1) =
        Finsupp.linearCombination k id := Finsupp.lhom_ext fun v c ↦ by
      simp [r]
    calc r.hom (e x) = Finsupp.linearCombination k id (σ x) := LinearMap.congr_fun this (σ x)
      _ = x := LinearMap.congr_fun hσ x
  let ψ₀ : A.V →ₗ[k] (ι →₀ MonoidAlgebra k G) :=
    ∑ g : G, (Representation.free k G ι g) ∘ₗ e ∘ₗ φ ∘ₗ A.ρ g⁻¹
  let s : A ⟶ free k G ι := ofHom <|
    ψ₀.intertwiningMap_of_isIntertwiningMap (ρ := A.ρ) (σ := Representation.free k G ι)
      fun h x ↦ by
        simp only [ψ₀, LinearMap.coe_sum, Finset.sum_apply, LinearMap.comp_apply, map_sum]
        refine Fintype.sum_equiv (Equiv.mulLeft h⁻¹) _ _ fun g ↦ ?_
        simp only [Equiv.coe_mulLeft, ← Module.End.mul_apply, ← map_mul, mul_inv_rev, inv_inv,
          mul_inv_cancel_left]
  refine (Retract.mk s r ?_).projective
  ext x
  -- Expose the underlying linear maps so the formulas for `r` and `ψ₀` can rewrite the retraction.
  change r.hom (ψ₀ x) = x
  conv_rhs => rw [hφ' x]
  simp only [ψ₀, LinearMap.coe_sum, Finset.sum_apply, LinearMap.comp_apply, map_sum]
  refine Finset.sum_congr rfl fun g _ ↦ ?_
  conv_rhs => rw [← he (φ (A.ρ g⁻¹ x))]
  exact LinearMap.congr_fun (r.hom.isIntertwining' g) _

/-- A representation that is projective over `k` and whose identity is a norm is a projective
`k[G]`-module. -/
theorem moduleProjective_of_id_mem_range_norm_linHom {k G : Type u} [CommRing k] [Group G]
    [Fintype G] (A : Rep.{u} k G) [Module.Projective k A.V]
    (h : LinearMap.id ∈ LinearMap.range (Representation.linHom A.ρ A.ρ).norm) :
    Module.Projective (MonoidAlgebra k G) A.ρ.asModule := by
  have := projective_of_id_mem_range_norm_linHom A h
  rwa [← equivalenceModuleMonoidAlgebra.map_projective_iff, ← IsProjective.iff_projective] at this

end Rep
