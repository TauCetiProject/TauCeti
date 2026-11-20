/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.BigOperators
public import Mathlib.Data.Fintype.Perm
public import Mathlib.LinearAlgebra.PiTensorProduct.Basic
import TauCeti.Data.Finset.Basic

/-!
# Polarization for multilinear maps

The diagonal values of a multilinear map of `ι` arguments already determine its symmetrizations.
This file proves the classical polarization identity, an inclusion-exclusion over the subsets of
`ι`: for a multilinear map `f` of `ι` arguments and a family `m` of arguments,
`∑_{S ⊆ ι} (-1)^{#S} f (∑_{i ∉ S} m i, …, ∑_{i ∉ S} m i) = ∑_{σ} f (m (σ ·))`.
Only the diagonal values of `f` appear on the left, and the right side is the full symmetrization
of `f` at `m`.

Expanding each argument by multilinearity turns the left side into a sum over all functions
`g : ι → ι`, weighted by `∑_{S ⊆ (range g)ᶜ} (-1)^{#S}`, which vanishes unless `g` is onto; the
surviving terms are the permutations. Nothing is inverted along the way, so the identity holds
over an arbitrary ring, commutative or not.

The instance for the tensor power `⨂[R] (_ : ι), M` is recorded here too: there the diagonal
values are the pure powers `⨂ₜ i, x`, the tensors with the same vector in every slot.

## Main results

* `MultilinearMap.sum_neg_one_pow_card_smul_apply_sum_compl`: the polarization identity for a
  multilinear map.
* `PiTensorProduct.sum_neg_one_pow_card_smul_tprod_sum_compl`: its tensor-power instance, writing
  the full symmetrization of a pure tensor as an alternating sum of pure powers.
* `TauCeti.map_add_add_sub_map_add_of_map_add`: the explicit three-variable polarization identity
  for an unbundled map `V → V → V → W` additive in each argument, requiring only `[Add V]` and
  `[AddCommGroup W]`.

## References

* W. Fulton and J. Harris, *Representation Theory: A First Course*, Appendix B.1, for the
  polarization argument.
-/

public section

open scoped Finset TensorProduct

universe u v w z

namespace TauCeti

/-- **Three-variable polarization.** For a map `F : V → V → V → W` into an additive commutative
group that is additive in each argument, the alternating combination of its diagonal values on
subsums of `u₁, u₂, u₃` equals the sum of `F` over all six permutations of `(u₁, u₂, u₃)`. -/
theorem map_add_add_sub_map_add_of_map_add {V W : Type*} [Add V] [AddCommGroup W]
    (F : V → V → V → W)
    (h₁ : ∀ a₁ a₂ b c, F (a₁ + a₂) b c = F a₁ b c + F a₂ b c)
    (h₂ : ∀ a b₁ b₂ c, F a (b₁ + b₂) c = F a b₁ c + F a b₂ c)
    (h₃ : ∀ a b c₁ c₂, F a b (c₁ + c₂) = F a b c₁ + F a b c₂) (u₁ u₂ u₃ : V) :
    F (u₁ + u₂ + u₃) (u₁ + u₂ + u₃) (u₁ + u₂ + u₃) -
      F (u₁ + u₂) (u₁ + u₂) (u₁ + u₂) - F (u₁ + u₃) (u₁ + u₃) (u₁ + u₃) -
      F (u₂ + u₃) (u₂ + u₃) (u₂ + u₃) + F u₁ u₁ u₁ + F u₂ u₂ u₂ + F u₃ u₃ u₃ =
      F u₁ u₂ u₃ + F u₁ u₃ u₂ + F u₂ u₁ u₃ + F u₂ u₃ u₁ + F u₃ u₁ u₂ + F u₃ u₂ u₁ := by
  simp only [h₁, h₂, h₃]
  abel

variable {ι : Type w} [DecidableEq ι]

/-- The functions into a fixed finset, as a filter on all functions. -/
private theorem piFinset_const [Fintype ι] (T : Finset ι) :
    (Fintype.piFinset fun _ : ι => T) =
      {g ∈ (Finset.univ : Finset (ι → ι)) | Finset.image g Finset.univ ⊆ T} := by
  ext g
  simp [Fintype.mem_piFinset, Finset.image_subset_iff]

/-- The subsets whose complement contains a fixed finset are the subsets of its complement. -/
private theorem filter_subset_compl [Fintype ι] (A : Finset ι) :
    {S ∈ (Finset.univ : Finset (Finset ι)) | A ⊆ Sᶜ} = Aᶜ.powerset := by
  ext S
  simp [Finset.mem_powerset, Finset.subset_compl_comm]

end TauCeti

namespace MultilinearMap

variable {R : Type u} {M : Type v} {N : Type z} {ι : Type w}
variable [Ring R] [AddCommMonoid M] [Module R M] [AddCommMonoid N] [Module R N]
variable [Fintype ι] [DecidableEq ι]

/-- **Polarization.** For a multilinear map of `ι` arguments, the alternating sum over the subsets
`S ⊆ ι` of its value on the constant family `∑_{i ∉ S} m i` is the full symmetrization of its value
on `m`. Only the diagonal values of `f` appear on the left, so they already determine every
symmetrization; over a ring in which `(#ι)!` is invertible they therefore determine `f` on all
symmetric arguments. -/
theorem sum_neg_one_pow_card_smul_apply_sum_compl
    (f : MultilinearMap (RingHom.id R) (fun _ : ι => M) N) (m : ι → M) :
    ∑ S : Finset ι, (-1 : R) ^ #S • f (fun _ => ∑ i ∈ Sᶜ, m i) =
      ∑ σ : Equiv.Perm ι, f fun i => m (σ i) := by
  classical
  have expand : ∀ S : Finset ι, (-1 : R) ^ #S • f (fun _ => ∑ i ∈ Sᶜ, m i) =
      ∑ g : ι → ι, if Finset.image g Finset.univ ⊆ Sᶜ then
        (-1 : R) ^ #S • f fun i => m (g i) else 0 := by
    intro S
    rw [f.map_sum_finset (fun (_ i : ι) => m i) fun _ => Sᶜ, Finset.smul_sum,
      TauCeti.piFinset_const, Finset.sum_filter]
  have collapse : ∀ g : ι → ι, (∑ S : Finset ι, if Finset.image g Finset.univ ⊆ Sᶜ then
      (-1 : R) ^ #S • f fun i => m (g i) else 0) =
      (if Function.Bijective g then (1 : R) else 0) • f fun i => m (g i) := by
    intro g
    have hiff : (Finset.image g Finset.univ)ᶜ = ∅ ↔ Function.Bijective g := by
      rw [Finset.compl_eq_empty_iff]
      refine Iff.trans ?_ (Finite.surjective_iff_bijective (f := g))
      simp [Finset.eq_univ_iff_forall, Finset.mem_image, Function.Surjective]
    rw [← Finset.sum_filter, TauCeti.filter_subset_compl, ← Finset.sum_smul,
      Finset.sum_powerset_neg_one_pow_card_of_ring]
    exact congrArg (fun r : R => r • f fun i => m (g i)) (if_congr hiff rfl rfl)
  have unweight : ∀ g : ι → ι, (if Function.Bijective g then (1 : R) else 0) •
      f (fun i => m (g i)) = if Function.Bijective g then f (fun i => m (g i)) else 0 := by
    intro g
    split <;> simp
  rw [Finset.sum_congr rfl fun S _ => expand S, Finset.sum_comm,
    Finset.sum_congr rfl fun g _ => (collapse g).trans (unweight g), ← Finset.sum_filter]
  refine (Finset.sum_bij (fun (σ : Equiv.Perm ι) _ => (σ : ι → ι))
    (fun σ _ => Finset.mem_filter.mpr ⟨Finset.mem_univ _, σ.bijective⟩)
    (fun σ _ τ _ h => Equiv.coe_fn_injective h) (fun g hg => ?_) fun σ _ => rfl).symm
  exact ⟨Equiv.ofBijective g (Finset.mem_filter.mp hg).2, Finset.mem_univ _, rfl⟩

end MultilinearMap

namespace PiTensorProduct

variable {R : Type u} {M : Type v} {ι : Type w}
variable [CommRing R] [AddCommMonoid M] [Module R M] [Fintype ι] [DecidableEq ι]

/-- **Polarization for tensor powers.** The full symmetrization of a pure tensor is an alternating
sum of pure powers `⨂ₜ i, x`. -/
theorem sum_neg_one_pow_card_smul_tprod_sum_compl (m : ι → M) :
    ∑ S : Finset ι, (-1 : R) ^ #S • (⨂ₜ[R] (_ : ι), ∑ i ∈ Sᶜ, m i) =
      ∑ σ : Equiv.Perm ι, ⨂ₜ[R] i, m (σ i) :=
  MultilinearMap.sum_neg_one_pow_card_smul_apply_sum_compl (tprod R) m

end PiTensorProduct
