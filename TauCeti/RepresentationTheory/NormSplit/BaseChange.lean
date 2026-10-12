/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import TauCeti.Algebra.Module.LinearMap.EndQuotient
public import TauCeti.LinearAlgebra.TensorProduct.Quotient
public import TauCeti.RepresentationTheory.BaseChange
public import TauCeti.RepresentationTheory.NormSplit.Basic
import TauCeti.RingTheory.Ideal.Operations

/-!
# Lifting a norm decomposition of the identity from `k/pk`

Let `G` be a finite group of order `p ^ m` acting on a projective `k`-module `V` on which
multiplication by `p` is injective. If the identity of the reduction `(k/pk) ⊗ V` is a norm
`y ↦ ∑ g, ρ g (π (ρ g⁻¹ y))` for the conjugation action of `G`, then so is the identity of `V`
(Serre, *Local Fields*, IX §5). This reduces the identity-norm condition for `p`-groups over `k`
to the same condition over `k/pk`.

## Main statements

* `Representation.id_mem_range_norm_linHom_of_baseChange`: the lifting statement above.

## References

* J.-P. Serre, *Local Fields*, Chapter IX, §5.
-/

public section

open scoped TensorProduct

namespace Representation

variable {k G V : Type*} [CommRing k] [Group G] [Fintype G] [AddCommGroup V] [Module k V]

/-- **Lifting a norm decomposition of the identity from `k/pk`.** Let `G` have order `p ^ m` and
act on a projective `k`-module `V` on which multiplication by `p` is injective. If the identity of
`(k/pk) ⊗ V` is a norm for the conjugation action of `G`, then so is the identity of `V`. -/
theorem id_mem_range_norm_linHom_of_baseChange [Module.Projective k V] (ρ : Representation k G V)
    {p m : ℕ} (hcard : Fintype.card G = p ^ m) (hp : ∀ v : V, (p : k) • v = 0 → v = 0)
    (h : LinearMap.id ∈ LinearMap.range
      (linHom (ρ.baseChange (k ⧸ Ideal.span {(p : k)}))
        (ρ.baseChange (k ⧸ Ideal.span {(p : k)}))).norm) :
    LinearMap.id ∈ LinearMap.range (linHom ρ ρ).norm := by
  classical
  set Q := k ⧸ Ideal.span {(p : k)}
  set ρQ := ρ.baseChange Q
  -- Reduction modulo `p`.
  let red : V →ₗ[k] Q ⊗[k] V := TensorProduct.mk k Q V 1
  have hred_surj : Function.Surjective red :=
    TensorProduct.exists_one_tmul_eq (Ideal.span {(p : k)})
  have hred_eq_zero (v : V) (hv : red v = 0) : ∃ w : V, (p : k) • w = v :=
    (TensorProduct.one_tmul_eq_zero_iff_exists_smul_eq (p : k) v).1 hv
  have hredρ (g : G) (v : V) : ρQ g (red v) = red (ρ g v) := by simp [ρQ, red]
  -- Lift `πQ` to `π`, and write `N π = id + p θ`.
  obtain ⟨πQ, hπQ⟩ := h
  have hπQ' (y : Q ⊗[k] V) : y = ∑ g : G, ρQ g (πQ (ρQ g⁻¹ y)) := by
    rw [← norm_linHom_apply, hπQ, LinearMap.id_apply]
  obtain ⟨π, hπ'⟩ := Module.projective_lifting_property red (πQ.restrictScalars k ∘ₗ red) hred_surj
  have hπ (v : V) : red (π v) = πQ (red v) := LinearMap.congr_fun hπ' v
  have hdiv (δ : V →ₗ[k] V) (hδ : ∀ v, red (δ v) = 0) :
      ∃ θ : V →ₗ[k] V, ∀ v, δ v = (p : k) • θ v := by
    have hker : δ ∈ RingHom.ker (Ideal.endMapQ (Ideal.span {algebraMap k k (p : k)}) V) :=
      (Ideal.mem_ker_endMapQ_iff _ _).2 fun _ ⟨v, hv⟩ ↦ hv ▸
        (Submodule.mem_span_algebraMap_smul_top_iff (p : k)).2 (hred_eq_zero _ (hδ v))
    obtain ⟨θ, rfl⟩ := (Ideal.endMapQ_span_algebraMap_eq_zero_iff (p : k) δ).1 hker
    exact ⟨θ, fun _ ↦ rfl⟩
  obtain ⟨θ, hθ⟩ := hdiv ((linHom ρ ρ).norm π - LinearMap.id) fun v ↦ by
    rw [LinearMap.sub_apply, map_sub, norm_linHom_apply, map_sum, LinearMap.id_apply]
    conv_rhs => rw [← sub_self (red v)]
    congr 1
    conv_rhs => rw [hπQ' (red v)]
    refine Finset.sum_congr rfl fun g _ ↦ ?_
    rw [← hredρ, hπ, ← hredρ]
  -- An equivariant `ψ` with `p • ψ` equivariant-divisible stays equivariant.
  have hcancel {ψ : V →ₗ[k] V} {δ : V →ₗ[k] V} (hδ : ∀ g x, δ (ρ g x) = ρ g (δ x))
      (hψ : ∀ x, δ x = (p : k) • ψ x) (g : G) (x : V) : ψ (ρ g x) = ρ g (ψ x) := by
    refine sub_eq_zero.1 (hp _ ?_)
    rw [smul_sub, ← hψ, ← map_smul, ← hψ, hδ, sub_self]
  have hNπρ (g : G) (x : V) :
      (linHom ρ ρ).norm π (ρ g x) = ρ g ((linHom ρ ρ).norm π x) := by
    have := LinearMap.congr_fun (self_norm_apply (linHom ρ ρ) g π) (ρ g x)
    rw [linHom_apply] at this
    simpa using this.symm
  have hθρ (g : G) (x : V) : θ (ρ g x) = ρ g (θ x) :=
    hcancel (δ := (linHom ρ ρ).norm π - LinearMap.id)
      (fun g x ↦ by simp [hNπρ]) hθ g x
  -- For every `j`, the identity is a norm plus `p ^ j` times an equivariant endomorphism.
  have key (j : ℕ) : ∃ φ ψ : V →ₗ[k] V, (∀ g x, ψ (ρ g x) = ρ g (ψ x)) ∧
      ∀ x, x = (linHom ρ ρ).norm φ x + ((p : k) ^ j) • ψ x := by
    induction j with
    | zero => exact ⟨0, LinearMap.id, fun _ _ ↦ rfl, fun x ↦ by simp⟩
    | succ j ih =>
      obtain ⟨φ, ψ, hψ, hx⟩ := ih
      refine ⟨φ + ((p : k) ^ j) • (ψ ∘ₗ π), -(ψ ∘ₗ θ), fun g x ↦ by simp [hθρ, hψ], fun x ↦ ?_⟩
      have hψπ : (linHom ρ ρ).norm (ψ ∘ₗ π) x = ψ ((linHom ρ ρ).norm π x) := by
        simp only [norm_linHom_apply, LinearMap.comp_apply, map_sum, hψ]
      have hNπ : (linHom ρ ρ).norm π x = x + (p : k) • θ x := by
        rw [← hθ, LinearMap.sub_apply, LinearMap.id_apply, add_sub_cancel]
      conv_lhs => rw [hx x]
      rw [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, hψπ, hNπ, map_add,
        map_smul, pow_succ, LinearMap.neg_apply, LinearMap.comp_apply, smul_neg, mul_smul,
        smul_add]
      abel
  obtain ⟨φ, ψ, hψ, hx⟩ := key m
  refine ⟨φ + ψ, LinearMap.ext fun x ↦ ?_⟩
  rw [LinearMap.id_apply, map_add, LinearMap.add_apply, norm_linHom_apply ρ ψ]
  conv_rhs => rw [hx x]
  congr 1
  have hg (g : G) : ρ g (ψ (ρ g⁻¹ x)) = ψ x := by
    rw [← hψ, ← Module.End.mul_apply (ρ g), ← map_mul, mul_inv_cancel, map_one,
      Module.End.one_apply]
  rw [Finset.sum_congr rfl fun g _ ↦ hg g, Finset.sum_const, Finset.card_univ, hcard,
    ← Nat.cast_smul_eq_nsmul k, Nat.cast_pow]

end Representation
