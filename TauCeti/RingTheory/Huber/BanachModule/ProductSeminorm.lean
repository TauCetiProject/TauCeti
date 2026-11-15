/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Normed.Operator.BoundedLinearMaps
public import TauCeti.Analysis.Normed.Ring.PseudoUniformizer
public import TauCeti.RingTheory.Huber.BanachModule.CompletedTensor
import Mathlib.Analysis.Normed.Group.Completion
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.TensorProduct.Finiteness
import Mathlib.Topology.MetricSpace.HausdorffDistance
import TauCeti.Analysis.Normed.Module.Bases.CountableType

/-!
# The product seminorm and Banach norm on completed module tensor products

Let `A` be a commutative ring and `V`, `W` seminormed `A`-modules. The *product seminorm*
`TauCeti.Huber.BanachModule.productSeminorm A V W` of `u : V ⊗[A] W` is the infimum of the
finite-presentation maxima `max_i ‖v_i‖ * ‖w_i‖` over all presentations `u = ∑ i, v_i ⊗ₜ w_i`,
with the empty maximum taken to be zero. Unlike the Archimedean projective seminorm, which sums
the products `‖v_i‖ * ‖w_i‖`, this maximum formula satisfies the ultrametric inequality
`π (u₁ + u₂) ≤ max (π u₁) (π u₂)` and is the largest nonarchimedean additive group seminorm on
`V ⊗[A] W` bounded on pure tensors by `‖v‖ * ‖w‖`.

When `A` is a seminormed commutative ring acting boundedly on `V` (`‖a • v‖ ≤ C * ‖a‖ * ‖v‖`),
the tensor topology `TauCeti.Huber.banachTensorTopology A V W` is finer than the topology of the
product seminorm, so `productSeminorm A V W` extends continuously to a nonarchimedean seminorm
`TauCeti.Huber.BanachModule.CompletedTensor.productNorm A V W` on the completed tensor product
`V ⊗̂_A W`. If `A` moreover has a multiplicative pseudo-uniformiser (`TauCeti.NormedRing.IsTate A`)
and acts boundedly on both `V` and `W`, rescaling elementary tensors by integer powers of the
pseudo-uniformiser balances the norms of their two factors. Consequently the positive-radius open
balls of `productSeminorm A V W` form a neighbourhood basis of zero for `banachTensorTopology A V W`
(`hasBasis_banachTensorTopology`), and `productNorm A V W` is a definite ultrametric norm on
`V ⊗̂_A W` whose open balls form a neighbourhood basis of zero for the completion topology
(`CompletedTensor.productNorm_eq_zero_iff`, `CompletedTensor.hasBasis_nhds_zero_productNorm`).

Over a complete nontrivially normed field `K` and ultrametric normed `K`-spaces `V` and `W`,
approximate Gram–Schmidt orthogonalisation on the finite-dimensional subspaces spanned by tensor
presentations shows without any countable-type or spherical-completeness hypothesis that
`productSeminorm K V W` is already a cross-norm on `V ⊗[K] W`: it satisfies
`productSeminorm K V W (v ⊗ₜ w) = ‖v‖ * ‖w‖` and vanishes only at `0`, so the canonical map
`V ⊗[K] W → V ⊗̂_K W` is injective (`CompletedTensor.injective_tensorProduct_of_field`).

## Main definitions

* `TauCeti.Huber.BanachModule.productSeminorm A V W`: the nonarchimedean product seminorm on
  `V ⊗[A] W`.
* `TauCeti.Huber.BanachModule.CompletedTensor.productNorm A V W`: the continuous extension of
  `productSeminorm A V W` to `V ⊗̂_A W`.
* `TauCeti.Huber.BanachModule.CompletedTensor.productNormAddGroupNorm`: `productNorm` bundled as
  an additive group norm on `V ⊗̂_A W` over a Tate normed commutative ring.
* `TauCeti.Huber.BanachModule.CompletedTensor.productNormedAddCommGroup`: the compatible
  `NormedAddCommGroup` structure on `V ⊗̂_A W` retaining its existing uniformity and topology
  definitionally.

## Main results

* `TauCeti.Huber.BanachModule.isNonarchimedean_productSeminorm`: `productSeminorm` satisfies the
  ultrametric inequality.
* `TauCeti.Huber.BanachModule.apply_le_mul_productSeminorm` and `le_productSeminorm`: universal
  property of `productSeminorm` among nonarchimedean additive group seminorms.
* `TauCeti.Huber.BanachModule.hasBasis_banachTensorTopology`,
  `banachTensorTopology_eq_productSeminorm`, `banachTensorUniformSpace_eq_productSeminorm` and
  `not_discreteTopology_banachTensorTopology`: identification of the tensor topology and uniformity
  with those of `productSeminorm` over a Tate seminormed commutative ring with bounded module
  actions, and nondiscreteness over a nontrivially normed field.
* `TauCeti.Huber.BanachModule.CompletedTensor.productNorm_toCompletion`,
  `productNorm_eq_zero_iff`, `hasBasis_nhds_zero_productNorm`, `norm_lift_le_mul_productNorm` and
  `productNorm_of_hasSum_le`: norm properties on the completed tensor product.
* `TauCeti.Huber.BanachModule.mul_infDist_mul_norm_le_productSeminorm`, `productSeminorm_tmul`,
  `productSeminorm_eq_zero_iff`, `CompletedTensor.injective_tensorProduct_of_field`,
  `CompletedTensor.productNorm_tmul` and `CompletedTensor.productNorm_unitVector`: Gram–Schmidt
  lower bound, cross-norm, and injectivity over a complete nontrivially normed field.

## References

* K. S. Kedlaya and R. Liu, *Relative p-adic Hodge theory: Foundations*, Astérisque 371 (2015),
  Definitions 2.1.10 and 2.2.7, and Lemma 2.2.9(a).
-/

public section

open Filter Topology UniformSpace TensorProduct
open scoped NNReal Uniformity

namespace TauCeti.Huber.BanachModule

section Algebraic

variable (A V W : Type*) [CommRing A] [SeminormedAddCommGroup V] [Module A V]
  [SeminormedAddCommGroup W] [Module A W]

/-- The finite-presentation maxima `max_i ‖v i‖ * ‖w i‖` for `u = ∑ i, v i ⊗ₜ[A] w i`, with the
empty presentation having maximum `0`. -/
private def maxCosts (u : V ⊗[A] W) : Set ℝ :=
  {c | ∃ (n : ℕ) (v : Fin n → V) (w : Fin n → W),
    ∑ i, v i ⊗ₜ[A] w i = u ∧ ((Finset.univ.sup fun i ↦ ‖v i‖₊ * ‖w i‖₊ : ℝ≥0) : ℝ) = c}

variable {A V W}

private theorem maxCosts_nonempty (u : V ⊗[A] W) : (maxCosts A V W u).Nonempty := by
  obtain ⟨n, v, w, hu⟩ := _root_.TensorProduct.exists_sum_tmul_eq u
  exact ⟨_, n, v, w, hu.symm, rfl⟩

private theorem maxCosts_bddBelow (u : V ⊗[A] W) : BddBelow (maxCosts A V W u) := by
  refine ⟨0, ?_⟩
  rintro _ ⟨_, _, _, -, rfl⟩
  exact NNReal.coe_nonneg _

private theorem sInf_maxCosts_le {n : ℕ} (v : Fin n → V) (w : Fin n → W) :
    sInf (maxCosts A V W (∑ i, v i ⊗ₜ[A] w i)) ≤
      ((Finset.univ.sup fun i ↦ ‖v i‖₊ * ‖w i‖₊ : ℝ≥0) : ℝ) :=
  csInf_le (maxCosts_bddBelow _) ⟨n, v, w, rfl, rfl⟩

private theorem sInf_maxCosts_nonneg (u : V ⊗[A] W) : 0 ≤ sInf (maxCosts A V W u) := by
  refine le_csInf (maxCosts_nonempty u) ?_
  rintro _ ⟨_, _, _, -, rfl⟩
  exact NNReal.coe_nonneg _

private theorem sInf_maxCosts_zero : sInf (maxCosts A V W 0) = 0 :=
  le_antisymm
    (by simpa using sInf_maxCosts_le (A := A) (Fin.elim0 : Fin 0 → V) (Fin.elim0 : Fin 0 → W))
    (sInf_maxCosts_nonneg 0)

private theorem sInf_maxCosts_add_le_max (u₁ u₂ : V ⊗[A] W) :
    sInf (maxCosts A V W (u₁ + u₂)) ≤
      max (sInf (maxCosts A V W u₁)) (sInf (maxCosts A V W u₂)) := by
  refine le_of_forall_pos_lt_add fun ε hε ↦ ?_
  set r := max (sInf (maxCosts A V W u₁)) (sInf (maxCosts A V W u₂)) + ε
  have hr₁ : sInf (maxCosts A V W u₁) < r := lt_add_of_le_of_pos (le_max_left _ _) hε
  have hr₂ : sInf (maxCosts A V W u₂) < r := lt_add_of_le_of_pos (le_max_right _ _) hε
  obtain ⟨_, ⟨n, v₁, w₁, rfl, rfl⟩, hc₁⟩ := exists_lt_of_csInf_lt (maxCosts_nonempty u₁) hr₁
  obtain ⟨_, ⟨m, v₂, w₂, rfl, rfl⟩, hc₂⟩ := exists_lt_of_csInf_lt (maxCosts_nonempty u₂) hr₂
  have hsum : ∑ k : Fin (n + m), Fin.append v₁ v₂ k ⊗ₜ[A] Fin.append w₁ w₂ k =
      (∑ i, v₁ i ⊗ₜ[A] w₁ i) + ∑ j, v₂ j ⊗ₜ[A] w₂ j := by
    simpa [Fin.append] using Fin.sum_univ_add fun k ↦ Fin.append v₁ v₂ k ⊗ₜ[A] Fin.append w₁ w₂ k
  rw [← hsum]
  refine (sInf_maxCosts_le (Fin.append v₁ v₂) (Fin.append w₁ w₂)).trans_lt ?_
  refine lt_of_le_of_lt ?_ (max_lt hc₁ hc₂)
  rw [← NNReal.coe_max, NNReal.coe_le_coe]
  refine Finset.sup_le fun k _ ↦ k.addCases (fun i ↦ ?_) (fun j ↦ ?_)
  · simp only [Fin.append_left]
    exact (Finset.le_sup (f := fun i ↦ ‖v₁ i‖₊ * ‖w₁ i‖₊) (Finset.mem_univ i)).trans
      (le_max_left _ _)
  · simp only [Fin.append_right]
    exact (Finset.le_sup (f := fun j ↦ ‖v₂ j‖₊ * ‖w₂ j‖₊) (Finset.mem_univ j)).trans
      (le_max_right _ _)

private theorem sInf_maxCosts_neg_le (u : V ⊗[A] W) :
    sInf (maxCosts A V W (-u)) ≤ sInf (maxCosts A V W u) := by
  refine le_csInf (maxCosts_nonempty u) ?_
  rintro _ ⟨n, v, w, rfl, rfl⟩
  have hneg : ∑ i, (-v i) ⊗ₜ[A] w i = -∑ i, v i ⊗ₜ[A] w i := by
    simp [TensorProduct.neg_tmul, Finset.sum_neg_distrib]
  rw [← hneg]
  simpa [nnNorm_neg] using sInf_maxCosts_le (A := A) (fun i ↦ -v i) w

variable (A V W) in
/-- **The nonarchimedean product seminorm** on `V ⊗[A] W`: the infimum of the finite-presentation
maxima `max_i ‖v i‖ * ‖w i‖` over all decompositions `u = ∑ i, v i ⊗ₜ[A] w i`, with the empty
presentation having maximum `0`. -/
noncomputable def productSeminorm : AddGroupSeminorm (V ⊗[A] W) where
  toFun u := sInf (maxCosts A V W u)
  map_zero' := sInf_maxCosts_zero
  add_le' u₁ u₂ := (sInf_maxCosts_add_le_max u₁ u₂).trans
    (max_le_add_of_nonneg (sInf_maxCosts_nonneg u₁) (sInf_maxCosts_nonneg u₂))
  neg' u := le_antisymm (sInf_maxCosts_neg_le u) (by simpa using sInf_maxCosts_neg_le (-u))

private theorem productSeminorm_apply (u : V ⊗[A] W) :
    productSeminorm A V W u = sInf (maxCosts A V W u) :=
  rfl

/-- **Ultrametric inequality** for the product seminorm. -/
theorem productSeminorm_add_le_max (u₁ u₂ : V ⊗[A] W) :
    productSeminorm A V W (u₁ + u₂) ≤
      max (productSeminorm A V W u₁) (productSeminorm A V W u₂) :=
  sInf_maxCosts_add_le_max u₁ u₂

variable (A V W) in
/-- The product seminorm is nonarchimedean. -/
theorem isNonarchimedean_productSeminorm : IsNonarchimedean (productSeminorm A V W) :=
  productSeminorm_add_le_max

/-- Ultrametric inequality for differences under the product seminorm. -/
theorem productSeminorm_sub_le_max (u₁ u₂ : V ⊗[A] W) :
    productSeminorm A V W (u₁ - u₂) ≤
      max (productSeminorm A V W u₁) (productSeminorm A V W u₂) := by
  simpa [sub_eq_add_neg, map_neg_eq_map] using productSeminorm_add_le_max u₁ (-u₂)

/-- The product seminorm of a finite sum is at most any nonnegative bound on the product seminorms
of its terms. -/
theorem productSeminorm_sum_le {ι : Type*} (s : Finset ι) (f : ι → V ⊗[A] W) {b : ℝ}
    (hb : 0 ≤ b) (hf : ∀ i ∈ s, productSeminorm A V W (f i) ≤ b) :
    productSeminorm A V W (∑ i ∈ s, f i) ≤ b := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using hb
  | insert i s hi ih =>
    rw [Finset.sum_insert hi]
    exact (productSeminorm_add_le_max _ _).trans <|
      max_le (hf i (Finset.mem_insert_self i s))
        (ih fun j hj ↦ hf j (Finset.mem_insert_of_mem hj))

/-- The product seminorm of a finite sum of pure tensors is at most the maximum of the products
`‖v i‖ * ‖w i‖`. -/
theorem productSeminorm_sum_tmul_le {ι : Type*} (s : Finset ι) (v : ι → V) (w : ι → W) :
    productSeminorm A V W (∑ i ∈ s, v i ⊗ₜ[A] w i) ≤
      ((s.sup fun i ↦ ‖v i‖₊ * ‖w i‖₊ : ℝ≥0) : ℝ) := by
  let e := s.equivFin
  rw [productSeminorm_apply]
  have key := sInf_maxCosts_le (A := A) (fun j ↦ v (e.symm j)) (fun j ↦ w (e.symm j))
  have hsum : (∑ j : Fin s.card, v (e.symm j) ⊗ₜ[A] w (e.symm j)) = ∑ i ∈ s, v i ⊗ₜ[A] w i :=
    (e.symm.sum_comp (fun x : s ↦ v x.1 ⊗ₜ[A] w x.1)).trans
      (Finset.sum_coe_sort s (fun x ↦ v x ⊗ₜ[A] w x))
  have hsup : (Finset.univ.sup fun j : Fin s.card ↦ ‖v (e.symm j)‖₊ * ‖w (e.symm j)‖₊) =
      s.sup fun i ↦ ‖v i‖₊ * ‖w i‖₊ := by
    refine le_antisymm (Finset.sup_le fun j _ ↦ ?_) (Finset.sup_le fun i hi ↦ ?_)
    · exact Finset.le_sup (f := fun i ↦ ‖v i‖₊ * ‖w i‖₊) (e.symm j).2
    · simpa using Finset.le_sup (f := fun j : Fin s.card ↦ ‖v (e.symm j)‖₊ * ‖w (e.symm j)‖₊)
        (Finset.mem_univ (e ⟨i, hi⟩))
  rwa [hsum, hsup] at key

/-- If every term of `∑ i ∈ s, v i ⊗ₜ[A] w i` satisfies `‖v i‖ * ‖w i‖ ≤ b` for some `b ≥ 0`,
then the product seminorm of the sum is at most `b`. -/
theorem productSeminorm_sum_tmul_le_of_le {ι : Type*} (s : Finset ι) (v : ι → V) (w : ι → W)
    {b : ℝ} (hb : 0 ≤ b) (h : ∀ i ∈ s, ‖v i‖ * ‖w i‖ ≤ b) :
    productSeminorm A V W (∑ i ∈ s, v i ⊗ₜ[A] w i) ≤ b := by
  refine (productSeminorm_sum_tmul_le s v w).trans ?_
  rw [← Real.coe_toNNReal b hb, NNReal.coe_le_coe]
  exact Finset.sup_le fun i hi ↦ (Real.le_toNNReal_iff_coe_le hb).mpr (by simpa using h i hi)

/-- A strict upper bound on the product seminorm is witnessed by some finite tensor
presentation. -/
theorem exists_sum_tmul_eq_of_productSeminorm_lt {u : V ⊗[A] W} {c : ℝ}
    (h : productSeminorm A V W u < c) :
    ∃ (n : ℕ) (v : Fin n → V) (w : Fin n → W),
      ∑ i, v i ⊗ₜ[A] w i = u ∧ ((Finset.univ.sup fun i ↦ ‖v i‖₊ * ‖w i‖₊ : ℝ≥0) : ℝ) < c := by
  obtain ⟨_, ⟨n, v, w, hu, rfl⟩, hc⟩ := exists_lt_of_csInf_lt (maxCosts_nonempty u) h
  exact ⟨n, v, w, hu, hc⟩

/-- A strict upper bound `productSeminorm A V W u < c` forces `c > 0` and produces a finite
presentation `u = ∑ i, v i ⊗ₜ[A] w i` with `‖v i‖ * ‖w i‖ < c` for every `i`. -/
theorem exists_sum_tmul_eq_forall_lt_of_productSeminorm_lt {u : V ⊗[A] W} {c : ℝ}
    (h : productSeminorm A V W u < c) :
    0 < c ∧ ∃ (n : ℕ) (v : Fin n → V) (w : Fin n → W),
      ∑ i, v i ⊗ₜ[A] w i = u ∧ ∀ i, ‖v i‖ * ‖w i‖ < c := by
  have hc0 : 0 < c := (apply_nonneg (productSeminorm A V W) u).trans_lt h
  obtain ⟨n, v, w, hu, hc⟩ := exists_sum_tmul_eq_of_productSeminorm_lt h
  refine ⟨hc0, n, v, w, hu, fun i ↦ ?_⟩
  have hi : ‖v i‖₊ * ‖w i‖₊ ≤ Finset.univ.sup fun j ↦ ‖v j‖₊ * ‖w j‖₊ :=
    Finset.le_sup (f := fun j ↦ ‖v j‖₊ * ‖w j‖₊) (Finset.mem_univ i)
  exact lt_of_le_of_lt (by exact_mod_cast hi) hc

/-- **Infimum description by upper bounds**: `productSeminorm A V W u` is the infimum of all
`c ≥ 0` bounding the products `‖v i‖ * ‖w i‖` of a finite presentation of `u`. -/
theorem productSeminorm_eq_sInf (u : V ⊗[A] W) :
    productSeminorm A V W u = sInf {c : ℝ | 0 ≤ c ∧
      ∃ (n : ℕ) (v : Fin n → V) (w : Fin n → W),
        ∑ i, v i ⊗ₜ[A] w i = u ∧ ∀ i, ‖v i‖ * ‖w i‖ ≤ c} := by
  let S : Set ℝ := {c : ℝ | 0 ≤ c ∧ ∃ (n : ℕ) (v : Fin n → V) (w : Fin n → W),
    ∑ i, v i ⊗ₜ[A] w i = u ∧ ∀ i, ‖v i‖ * ‖w i‖ ≤ c}
  have hsub : maxCosts A V W u ⊆ S := by
    rintro _ ⟨n, v, w, rfl, rfl⟩
    refine ⟨NNReal.coe_nonneg _, n, v, w, rfl, fun i ↦ ?_⟩
    exact_mod_cast Finset.le_sup (f := fun j ↦ ‖v j‖₊ * ‖w j‖₊) (Finset.mem_univ i)
  refine le_antisymm ?_ (csInf_le_csInf ⟨0, fun _ h ↦ h.1⟩ (maxCosts_nonempty u) hsub)
  refine le_csInf ((maxCosts_nonempty u).mono hsub) ?_
  rintro c ⟨hc0, n, v, w, rfl, hw⟩
  exact productSeminorm_sum_tmul_le_of_le Finset.univ v w hc0 fun i _ ↦ hw i

/-- The product seminorm of a pure tensor is at most the product of the norms. -/
theorem productSeminorm_tmul_le (v : V) (w : W) :
    productSeminorm A V W (v ⊗ₜ[A] w) ≤ ‖v‖ * ‖w‖ := by
  simpa using productSeminorm_sum_tmul_le ({()} : Finset Unit) (fun _ ↦ v) (fun _ ↦ w)

/-- **Universal bound for nonarchimedean seminorms**: a nonarchimedean additive group seminorm `p`
bounded on the images of pure tensors by `C * (‖v‖ * ‖w‖)` (`C ≥ 0`) is bounded on the image of
every tensor by `C` times the product seminorm. -/
theorem apply_le_mul_productSeminorm {M : Type*} [AddCommGroup M] {p : AddGroupSeminorm M}
    (hp : IsNonarchimedean p) {f : V ⊗[A] W →+ M} {C : ℝ} (hC : 0 ≤ C)
    (h : ∀ v w, p (f (v ⊗ₜ[A] w)) ≤ C * (‖v‖ * ‖w‖)) (u : V ⊗[A] W) :
    p (f u) ≤ C * productSeminorm A V W u := by
  rw [productSeminorm_apply, ← smul_eq_mul, ← Real.sInf_smul_of_nonneg hC]
  refine le_csInf (maxCosts_nonempty u).smul_set ?_
  rintro _ ⟨_, ⟨n, v, w, rfl, rfl⟩, rfl⟩
  simp only [smul_eq_mul, map_sum]
  have hb : 0 ≤ C * ((Finset.univ.sup fun i ↦ ‖v i‖₊ * ‖w i‖₊ : ℝ≥0) : ℝ) := by positivity
  have hsum : ∀ s : Finset (Fin n), p (∑ i ∈ s, f (v i ⊗ₜ[A] w i)) ≤
      C * ((Finset.univ.sup fun i ↦ ‖v i‖₊ * ‖w i‖₊ : ℝ≥0) : ℝ) := by
    intro s
    induction s using Finset.induction_on with
    | empty => simpa using hb
    | insert i s hi ih =>
      rw [Finset.sum_insert hi]
      refine (hp _ _).trans (max_le ?_ ih)
      refine (h (v i) (w i)).trans ?_
      gcongr
      exact_mod_cast Finset.le_sup (f := fun j ↦ ‖v j‖₊ * ‖w j‖₊) (Finset.mem_univ i)
  exact hsum Finset.univ

/-- **Extremality of the product seminorm**: `productSeminorm A V W` is the largest
nonarchimedean additive group seminorm on `V ⊗[A] W` bounded on pure tensors by `‖v‖ * ‖w‖`. -/
theorem le_productSeminorm {p : AddGroupSeminorm (V ⊗[A] W)} (hp : IsNonarchimedean p)
    (h : ∀ v w, p (v ⊗ₜ[A] w) ≤ ‖v‖ * ‖w‖) : p ≤ productSeminorm A V W := fun u ↦ by
  simpa using apply_le_mul_productSeminorm hp (f := AddMonoidHom.id _) zero_le_one
    (by simpa using h) u

/-- The linear map on `V ⊗[A] W` induced by a bounded `A`-bilinear map into an ultrametric
seminormed module `M` has norm bounded by `C` times the product seminorm. -/
theorem norm_lift_le_mul_productSeminorm {M : Type*} [SeminormedAddCommGroup M]
    [IsUltrametricDist M] [Module A M] (β : V →ₗ[A] W →ₗ[A] M) {C : ℝ} (hC : 0 ≤ C)
    (hβ : ∀ v w, ‖β v w‖ ≤ C * (‖v‖ * ‖w‖)) (u : V ⊗[A] W) :
    ‖TensorProduct.lift β u‖ ≤ C * productSeminorm A V W u :=
  apply_le_mul_productSeminorm (p := normAddGroupSeminorm M)
    IsUltrametricDist.isNonarchimedean_norm (f := (TensorProduct.lift β).toAddMonoidHom) hC
    (fun v w ↦ by simpa using hβ v w) u

private theorem productSeminorm_comm_le (u : V ⊗[A] W) :
    productSeminorm A W V (TensorProduct.comm A V W u) ≤ productSeminorm A V W u := by
  simpa using apply_le_mul_productSeminorm (isNonarchimedean_productSeminorm A W V)
    (f := (TensorProduct.comm A V W).toLinearMap.toAddMonoidHom) zero_le_one
    (fun v w ↦ by simpa [mul_comm ‖v‖] using productSeminorm_tmul_le w v) u

/-- The product seminorm is symmetric: exchanging the two factors preserves it. -/
@[simp]
theorem productSeminorm_comm (u : V ⊗[A] W) :
    productSeminorm A W V (TensorProduct.comm A V W u) = productSeminorm A V W u :=
  (productSeminorm_comm_le u).antisymm <| by
    simpa using productSeminorm_comm_le (TensorProduct.comm A V W u)

/-- If `a : A` scales norms on `V` by at most `C ≥ 0`, it scales the product seminorm by at most
`C`. -/
theorem productSeminorm_smul_le_of_le_left {a : A} {C : ℝ} (hC : 0 ≤ C)
    (ha : ∀ v : V, ‖a • v‖ ≤ C * ‖v‖) (u : V ⊗[A] W) :
    productSeminorm A V W (a • u) ≤ C * productSeminorm A V W u :=
  apply_le_mul_productSeminorm (isNonarchimedean_productSeminorm A V W)
    (f := (LinearMap.lsmul A (V ⊗[A] W) a).toAddMonoidHom) hC
    (fun v w ↦ by
      simp only [LinearMap.toAddMonoidHom_coe, LinearMap.lsmul_apply, TensorProduct.smul_tmul']
      exact (productSeminorm_tmul_le (a • v) w).trans
        (by rw [← mul_assoc]; gcongr; exact ha v)) u

/-- If `a : A` scales norms on `W` by at most `C ≥ 0`, it scales the product seminorm by at most
`C`. -/
theorem productSeminorm_smul_le_of_le_right {a : A} {C : ℝ} (hC : 0 ≤ C)
    (ha : ∀ w : W, ‖a • w‖ ≤ C * ‖w‖) (u : V ⊗[A] W) :
    productSeminorm A V W (a • u) ≤ C * productSeminorm A V W u := by
  rw [← productSeminorm_comm, map_smul, ← productSeminorm_comm (u := u)]
  exact productSeminorm_smul_le_of_le_left hC ha (TensorProduct.comm A V W u)

/-- Tensoring a zero module on the left gives product seminorm zero everywhere. -/
@[simp]
theorem productSeminorm_eq_zero_of_subsingleton_left [Subsingleton V] (u : V ⊗[A] W) :
    productSeminorm A V W u = 0 := by
  rw [Subsingleton.elim u 0, map_zero]

/-- Tensoring a zero module on the right gives product seminorm zero everywhere. -/
@[simp]
theorem productSeminorm_eq_zero_of_subsingleton_right [Subsingleton W] (u : V ⊗[A] W) :
    productSeminorm A V W u = 0 := by
  rw [Subsingleton.elim u 0, map_zero]

end Algebraic

section SeminormedRing

variable {A V W : Type*} [SeminormedCommRing A] [SeminormedAddCommGroup V] [Module A V]
  [SeminormedAddCommGroup W] [Module A W]

/-- Under a contractive `A`-action on `V`, the product seminorm is submultiplicative for scalar
multiplication. -/
theorem productSeminorm_smul_le [IsBoundedSMul A V] (a : A) (u : V ⊗[A] W) :
    productSeminorm A V W (a • u) ≤ ‖a‖ * productSeminorm A V W u :=
  productSeminorm_smul_le_of_le_left (norm_nonneg a) (norm_smul_le a) u

/-- A unit of `A` scaling the norm of `A` exactly also scales the product seminorm exactly under a
contractive `A`-action on `V`. -/
theorem productSeminorm_units_smul_of_norm_mul [IsBoundedSMul A V] {a : Aˣ}
    (ha : ∀ x : A, ‖(a : A) * x‖ = ‖(a : A)‖ * ‖x‖) (u : V ⊗[A] W) :
    productSeminorm A V W ((a : A) • u) = ‖(a : A)‖ * productSeminorm A V W u := by
  refine le_antisymm (productSeminorm_smul_le (a : A) u) ?_
  rcases (norm_nonneg (a : A)).eq_or_lt with h0 | ha0
  · rw [← h0, zero_mul]
    exact apply_nonneg _ _
  calc ‖(a : A)‖ * productSeminorm A V W u
      = ‖(a : A)‖ * productSeminorm A V W (((a⁻¹ : Aˣ) : A) • (a : A) • u) := by
          simp [smul_smul]
    _ ≤ ‖(a : A)‖ * (‖((a⁻¹ : Aˣ) : A)‖ * productSeminorm A V W ((a : A) • u)) := by
          gcongr; exact productSeminorm_smul_le _ _
    _ = productSeminorm A V W ((a : A) • u) := by
          rw [TauCeti.NormedRing.norm_units_inv_of_norm_mul ha0.ne' ha]
          field_simp

/-- On `A ⊗[A] V` for an ultrametric `A`-module `V` with contractive action over a norm-one
ring `A`, the product seminorm is the norm of the image under `TensorProduct.lid A V`. -/
theorem productSeminorm_eq_norm_lid [NormOneClass A] [IsUltrametricDist V] [IsBoundedSMul A V]
    (u : A ⊗[A] V) : productSeminorm A A V u = ‖TensorProduct.lid A V u‖ := by
  refine le_antisymm ?_ ?_
  · calc productSeminorm A A V u
        = productSeminorm A A V ((1 : A) ⊗ₜ[A] TensorProduct.lid A V u) := by
            rw [← TensorProduct.lid_symm_apply, LinearEquiv.symm_apply_apply]
      _ ≤ ‖(1 : A)‖ * ‖TensorProduct.lid A V u‖ := productSeminorm_tmul_le _ _
      _ = ‖TensorProduct.lid A V u‖ := by rw [norm_one, one_mul]
  · simpa using apply_le_mul_productSeminorm (p := normAddGroupSeminorm V)
      IsUltrametricDist.isNonarchimedean_norm
      (f := (TensorProduct.lid A V).toLinearMap.toAddMonoidHom) zero_le_one
      (fun a v ↦ by simpa using norm_smul_le a v) u

/-- On `V ⊗[A] A` for an ultrametric `A`-module `V` with contractive action over a norm-one
ring `A`, the product seminorm is the norm of the image under `TensorProduct.rid A V`. -/
theorem productSeminorm_eq_norm_rid [NormOneClass A] [IsUltrametricDist V] [IsBoundedSMul A V]
    (u : V ⊗[A] A) : productSeminorm A V A u = ‖TensorProduct.rid A V u‖ := by
  rw [← productSeminorm_comm, productSeminorm_eq_norm_lid, ← TensorProduct.comm_trans_lid,
    LinearEquiv.trans_apply]

end SeminormedRing

section NormedFieldAlgebraic

variable {K V W : Type*} [NormedField K] [SeminormedAddCommGroup V] [NormedSpace K V]
  [SeminormedAddCommGroup W] [NormedSpace K W]

/-- Over a normed field, the product seminorm is homogeneous under scalar multiplication. -/
@[simp]
theorem productSeminorm_smul (c : K) (u : V ⊗[K] W) :
    productSeminorm K V W (c • u) = ‖c‖ * productSeminorm K V W u := by
  rcases eq_or_ne c 0 with rfl | hc
  · simp
  · exact productSeminorm_units_smul_of_norm_mul (a := Units.mk0 c hc) (fun x ↦ norm_mul _ _) u

end NormedFieldAlgebraic

section CompleteFieldAlgebraic

variable {K V W : Type*} [NontriviallyNormedField K] [CompleteSpace K]
  [NormedAddCommGroup V] [NormedSpace K V] [IsUltrametricDist V]
  [NormedAddCommGroup W] [NormedSpace K W] [IsUltrametricDist W]

/-- Approximate Gram–Schmidt step on the sequence listing `w 1, …, w r`, then `w 0`, then
`y 0, …, y (m - 1)` for linearly independent `w : Fin (r + 1) → W`: produces a `t`-orthogonal
family `e` whose `r`-th vector separates `w 0` from the span `D` of `w 1, …, w r`. -/
private theorem exists_tOrthogonal_of_linearIndependent {r m : ℕ} (w : Fin (r + 1) → W)
    (hw : LinearIndependent K w) (y : Fin m → W) {t : ℝ≥0} (ht1 : t < 1) :
    ∃ (e : ℕ → W) (α : K) (d : W),
      TauCeti.IsTOrthogonalFamily K t e ∧
      α ≠ 0 ∧ e r ≠ 0 ∧
      d ∈ Submodule.span K (w '' (Set.univ \ {0})) ∧
      α • e r + d = w 0 ∧
      Metric.infDist (w 0) (Submodule.span K (w '' (Set.univ \ {0})) : Set W) ≤ ‖α • e r‖ ∧
      Submodule.span K (e '' Set.Iio r) = Submodule.span K (w '' (Set.univ \ {0})) ∧
      ∀ k : Fin m, y k ∈ Submodule.span K (e '' Set.Iio (r + 1 + m)) := by
  classical
  set D : Submodule K W := Submodule.span K (w '' (Set.univ \ {0}))
  let z : ℕ → W := fun n ↦
    if h₁ : n < r then w ⟨n + 1, by omega⟩
    else if h₂ : n = r then w 0
    else if h₃ : n < r + 1 + m then y ⟨n - (r + 1), by omega⟩
    else 0
  obtain ⟨e, he, hspan⟩ := TauCeti.exists_isTOrthogonalFamily_span_image_Iio_eq (K := K) z ht1
  have hzD : Submodule.span K (z '' Set.Iio r) = D := by
    refine congrArg (Submodule.span K) (Set.ext fun u ↦ ⟨?_, ?_⟩)
    · rintro ⟨n, hn, rfl⟩
      rw [Set.mem_Iio] at hn
      exact ⟨⟨n + 1, by omega⟩, ⟨Set.mem_univ _, Fin.succ_ne_zero ⟨n, hn⟩⟩, by simp [z, hn]⟩
    · rintro ⟨j, ⟨-, hj0⟩, rfl⟩
      obtain ⟨k, rfl⟩ := Fin.eq_succ_of_ne_zero hj0
      exact ⟨k.1, k.2, by simp [z, k.2]; rfl⟩
  have heD : Submodule.span K (e '' Set.Iio r) = D := (hspan r).trans hzD
  have hw0_notMem : w 0 ∉ D := fun hmem ↦
    linearIndependent_iff_notMem_span.mp hw 0 (by simpa [D] using hmem)
  have hw0_mem : w 0 ∈ (K ∙ e r) ⊔ D := by
    have hz_mem : z r ∈ Submodule.span K (z '' Set.Iio (r + 1)) :=
      Submodule.subset_span ⟨r, Nat.lt_succ_self r, rfl⟩
    rw [← hspan (r + 1), ← Order.succ_eq_add_one, Order.Iio_succ_eq_insert, Set.image_insert_eq,
      Submodule.span_insert, heD] at hz_mem
    simpa [z] using hz_mem
  obtain ⟨u₁, hu₁, d, hd, hud⟩ := Submodule.mem_sup.mp hw0_mem
  obtain ⟨α, rfl⟩ := Submodule.mem_span_singleton.mp hu₁
  have hαer_ne : α • e r ≠ 0 := by
    intro h0
    rw [h0, zero_add] at hud
    exact hw0_notMem (hud ▸ hd)
  have hdist : Metric.infDist (w 0) (D : Set W) ≤ ‖α • e r‖ :=
    (Metric.infDist_le_dist_of_mem hd).trans_eq (by rw [dist_eq_norm, ← hud, add_sub_cancel_right])
  refine ⟨e, α, d, he, left_ne_zero_of_smul hαer_ne, right_ne_zero_of_smul hαer_ne,
    hd, hud, hdist, heD, fun k ↦ ?_⟩
  rw [hspan (r + 1 + m)]
  refine Submodule.subset_span ⟨r + 1 + k.1, Set.mem_Iio.mpr (by omega), ?_⟩
  have h1 : ¬ (r + 1 + k.1 < r) := by omega
  have h2 : r + 1 + k.1 ≠ r := by omega
  have h3 : r + 1 + k.1 < r + 1 + m := by omega
  simp [z, h1, h2, h3]

/-- Finite-dimensional Gram–Schmidt dual functional: given linearly independent
`w : Fin (r + 1) → W` and vectors `y : Fin m → W`, constructs `φ : W →ₗ[K] K` killing
`w 1, …, w r`, sending `w 0` to `1`, and satisfying the `t`-orthogonal bound on each `y k`. -/
private theorem exists_dual_of_linearIndependent {r m : ℕ} (w : Fin (r + 1) → W)
    (hw : LinearIndependent K w) (y : Fin m → W) {t : ℝ≥0} (ht0 : 0 < t) (ht1 : t < 1) :
    ∃ (c : ℝ) (φ : W →ₗ[K] K),
      0 < c ∧
      Metric.infDist (w 0) (Submodule.span K (w '' (Set.univ \ {0})) : Set W) ≤ c ∧
      φ (w 0) = 1 ∧
      (∀ u ∈ Submodule.span K (w '' (Set.univ \ {0})), φ u = 0) ∧
      ∀ k : Fin m, (t : ℝ) * ‖φ (y k)‖ * c ≤ ‖y k‖ := by
  classical
  obtain ⟨e, α, d, he, hα_ne, her_ne, hd, hud, hdist, heD, hy_mem⟩ :=
    exists_tOrthogonal_of_linearIndependent w hw y ht1
  let S := {i : Fin (r + 1 + m) // e i ≠ 0}
  let e' : S → W := fun i ↦ e i.1.1
  have he' : TauCeti.IsTOrthogonalFamily K t e' :=
    he.comp (Fin.val_injective.comp Subtype.val_injective)
  have hli_e' : LinearIndependent K e' := he'.linearIndependent ht0 fun i ↦ i.2
  let E_S : Submodule K W := Submodule.span K (Set.range e')
  have hy_S (k : Fin m) : y k ∈ E_S := by
    refine Submodule.span_le.mpr ?_ (hy_mem k)
    rintro _ ⟨n, hn, rfl⟩
    exact if h0 : e n = 0 then by simp [h0] else Submodule.subset_span ⟨⟨⟨n, hn⟩, h0⟩, rfl⟩
  let bS : Module.Basis S K E_S := Module.Basis.span hli_e'
  let rIdx : S := ⟨⟨r, by omega⟩, her_ne⟩
  obtain ⟨π, hπ⟩ := E_S.subtype.exists_leftInverse_of_injective E_S.ker_subtype
  let φ : W →ₗ[K] K := (α⁻¹ • bS.coord rIdx).comp π
  have hφ_sub (u : E_S) : φ u.1 = α⁻¹ * bS.coord rIdx u := by
    have hπu : π u.1 = u := LinearMap.congr_fun hπ u
    simp [φ, hπu]
  have hφ_e' (i : S) : bS.coord rIdx ⟨e' i, Submodule.subset_span ⟨i, rfl⟩⟩ =
      if i = rIdx then 1 else 0 := by
    rw [(Module.Basis.span_apply hli_e' i).symm, Module.Basis.coord_apply, bS.repr_self,
      Finsupp.single_apply]
  have hφ_D {u : W} (hu : u ∈ Submodule.span K (w '' (Set.univ \ {0}))) : φ u = 0 := by
    rw [← heD] at hu
    refine Submodule.span_induction (p := fun u _ ↦ φ u = 0) ?_ (map_zero φ)
      (fun a b _ _ ha hb ↦ by rw [map_add, ha, hb, add_zero])
      (fun c a _ ha ↦ by rw [map_smul, ha, smul_eq_mul, mul_zero]) hu
    rintro _ ⟨n, hn, rfl⟩
    rw [Set.mem_Iio] at hn
    by_cases h0 : e n = 0
    · simp [h0]
    · let idx : S := ⟨⟨n, by omega⟩, h0⟩
      have hne : idx ≠ rIdx := fun h ↦ hn.ne (congrArg (fun s : S ↦ s.1.1) h)
      rw [hφ_sub ⟨e n, Submodule.subset_span ⟨idx, rfl⟩⟩, hφ_e' idx]
      simp [hne]
  have hφ_w0 : φ (w 0) = 1 := by
    have hφ_er : φ (e r) = α⁻¹ := by
      rw [hφ_sub ⟨e r, Submodule.subset_span ⟨rIdx, rfl⟩⟩, hφ_e' rIdx]
      simp
    rw [← hud, map_add, map_smul, hφ_er, hφ_D hd, smul_eq_mul, mul_inv_cancel₀ hα_ne, add_zero]
  refine ⟨‖α • e r‖, φ, norm_pos_iff.mpr (smul_ne_zero hα_ne her_ne), hdist, hφ_w0,
    fun _ hu ↦ hφ_D hu, fun k ↦ ?_⟩
  let yk' : E_S := ⟨y k, hy_S k⟩
  have hbS (i : S) : ((bS i : E_S) : W) = e' i :=
    congrArg Subtype.val (Module.Basis.span_apply hli_e' i)
  have hexp : ∑ i : S, bS.repr yk' i • e' i = y k := by
    have h := congrArg (E_S.subtype : E_S →ₗ[K] W) (bS.sum_repr yk')
    simpa only [map_sum, map_smul, Submodule.coe_subtype, hbS] using h
  have horth := he'.mul_norm_smul_le (Finset.mem_univ rIdx) (fun i ↦ bS.repr yk' i)
  have hcoeff : bS.repr yk' rIdx • e' rIdx = φ (y k) • (α • e r) := by
    have hsc : φ (y k) * α = bS.repr yk' rIdx := by
      rw [hφ_sub yk', Module.Basis.coord_apply]
      field_simp
    rw [smul_smul, hsc]
  rwa [hexp, hcoeff, norm_smul, ← mul_assoc] at horth

/-- Finite-dimensional Gram–Schmidt estimate for the product seminorm: if `w : Fin (r + 1) → W`
is linearly independent over a complete nontrivially normed field `K`, then for every `0 < t < 1`,
`t * infDist (w 0) (span (w 1, …, w r)) * ‖v 0‖ ≤ productSeminorm K V W (∑ j, v j ⊗ₜ w j)`. -/
theorem mul_infDist_mul_norm_le_productSeminorm {r : ℕ} (v : Fin (r + 1) → V)
    (w : Fin (r + 1) → W) (hw : LinearIndependent K w) {t : ℝ≥0} (ht0 : 0 < t) (ht1 : t < 1) :
    (t : ℝ) * Metric.infDist (w 0) (Submodule.span K (w '' (Set.univ \ {0})) : Set W) * ‖v 0‖ ≤
      productSeminorm K V W (∑ j, v j ⊗ₜ[K] w j) := by
  rw [productSeminorm_apply]
  refine le_csInf (maxCosts_nonempty _) ?_
  rintro _ ⟨m, x, y, hxy, rfl⟩
  obtain ⟨c, φ, hc_pos, hdist, hφ_w0, hφ_D, hφ_yk⟩ :=
    exists_dual_of_linearIndependent w hw y ht0 ht1
  let Φ : V ⊗[K] W →ₗ[K] V := (TensorProduct.rid K V).toLinearMap.comp (φ.lTensor V)
  have hv0_eq : v 0 = ∑ k : Fin m, φ (y k) • x k := by
    have hΦ_rhs : Φ (∑ j, v j ⊗ₜ[K] w j) = v 0 := by
      rw [map_sum, Finset.sum_eq_single 0]
      · simp [Φ, hφ_w0]
      · intro j _ hj
        simp [Φ, hφ_D _ (Submodule.subset_span ⟨j, ⟨Set.mem_univ j, hj⟩, rfl⟩)]
      · simp
    rw [← hΦ_rhs, ← hxy, map_sum]
    simp [Φ]
  have hpos : 0 < (t : ℝ) * c := mul_pos (by exact_mod_cast ht0) hc_pos
  have hle : ‖v 0‖ ≤ (((t : ℝ) * c)⁻¹) *
      ((Finset.univ.sup fun k : Fin m ↦ ‖x k‖₊ * ‖y k‖₊ : ℝ≥0) : ℝ) := by
    rw [hv0_eq]
    refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (by positivity) fun k _ ↦ ?_
    rw [norm_smul, le_inv_mul_iff₀ hpos]
    calc (t : ℝ) * c * (‖φ (y k)‖ * ‖x k‖)
        = ‖x k‖ * ((t : ℝ) * ‖φ (y k)‖ * c) := by ring
      _ ≤ ‖x k‖ * ‖y k‖ := by gcongr; exact hφ_yk k
      _ ≤ ((Finset.univ.sup fun j : Fin m ↦ ‖x j‖₊ * ‖y j‖₊ : ℝ≥0) : ℝ) := by
          exact_mod_cast Finset.le_sup (f := fun j ↦ ‖x j‖₊ * ‖y j‖₊) (Finset.mem_univ k)
  calc (t : ℝ) * Metric.infDist (w 0) (Submodule.span K (w '' (Set.univ \ {0})) : Set W) * ‖v 0‖
      ≤ (t : ℝ) * c * ‖v 0‖ := by gcongr
    _ ≤ ((Finset.univ.sup fun k : Fin m ↦ ‖x k‖₊ * ‖y k‖₊ : ℝ≥0) : ℝ) :=
        (le_inv_mul_iff₀ hpos).mp hle

/-- **Cross-norm on pure tensors** over a complete nontrivially normed field: the product seminorm
of `v ⊗ₜ[K] w` equals `‖v‖ * ‖w‖`. -/
@[simp]
theorem productSeminorm_tmul (v : V) (w : W) :
    productSeminorm K V W (v ⊗ₜ[K] w) = ‖v‖ * ‖w‖ := by
  refine le_antisymm (productSeminorm_tmul_le v w) ?_
  rcases eq_or_ne w 0 with rfl | hw
  · simp
  refine le_of_forall_pos_lt_add fun ε hε ↦ ?_
  rcases eq_or_ne v 0 with rfl | hv
  · simpa using hε
  have hvw : 0 < ‖v‖ * ‖w‖ := mul_pos (norm_pos_iff.mpr hv) (norm_pos_iff.mpr hw)
  obtain ⟨t, ht0, ht1, htε⟩ :
      ∃ t : ℝ≥0, 0 < t ∧ t < 1 ∧ ‖v‖ * ‖w‖ < (t : ℝ) * (‖v‖ * ‖w‖) + ε := by
    let s : ℝ := max (1 / 2) (1 - ε / (2 * (‖v‖ * ‖w‖)))
    have hs0 : 0 < s := lt_of_lt_of_le (by norm_num) (le_max_left _ _)
    have hs1 : s < 1 := max_lt (by norm_num) (sub_lt_self 1 (by positivity))
    let t : ℝ≥0 := ⟨s, hs0.le⟩
    have ht_coe : (t : ℝ) = s := rfl
    refine ⟨t, by exact_mod_cast hs0, by exact_mod_cast hs1, ?_⟩
    have hsub : 1 - ε / (2 * (‖v‖ * ‖w‖)) ≤ s := le_max_right _ _
    have hmul := mul_le_mul_of_nonneg_right hsub hvw.le
    have hsimp : (1 - ε / (2 * (‖v‖ * ‖w‖))) * (‖v‖ * ‖w‖) = ‖v‖ * ‖w‖ - ε / 2 := by
      field_simp
    rw [ht_coe]
    linarith
  have hli : LinearIndependent K (![w] : Fin 1 → W) := linearIndependent_unique_iff.mpr hw
  have hkey := mul_infDist_mul_norm_le_productSeminorm (![v] : Fin 1 → V) (![w] : Fin 1 → W)
    hli ht0 ht1
  have hD : (Submodule.span K ((![w] : Fin 1 → W) '' (Set.univ \ {0})) : Set W) = {0} := by
    have hemp : (Set.univ \ {(0 : Fin 1)}) = ∅ := by
      ext i; fin_cases i; simp
    simp [hemp]
  have hdist : Metric.infDist ((![w] : Fin 1 → W) 0) ({0} : Set W) = ‖w‖ := by
    simp [Metric.infDist_singleton]
  have hsum : (∑ j : Fin 1, (![v] : Fin 1 → V) j ⊗ₜ[K] (![w] : Fin 1 → W) j) = v ⊗ₜ[K] w := by
    simp
  rw [hD, hdist, hsum] at hkey
  simp only [Matrix.cons_val_zero] at hkey
  linarith

/-- **Definiteness of the product seminorm** over a complete nontrivially normed field (KL15,
Lemma 2.2.9(a)): `productSeminorm K V W u = 0` if and only if `u = 0`. -/
@[simp]
theorem productSeminorm_eq_zero_iff {u : V ⊗[K] W} :
    productSeminorm K V W u = 0 ↔ u = 0 := by
  refine ⟨fun h0 ↦ ?_, fun h ↦ h ▸ map_zero _⟩
  by_contra hu
  obtain ⟨n, a, b, hab⟩ := _root_.TensorProduct.exists_sum_tmul_eq u
  let W₁ : Submodule K W := Submodule.span K (Set.range b)
  have : FiniteDimensional K W₁ := FiniteDimensional.span_of_finite K (Set.finite_range b)
  let f := Module.finBasis K W₁
  set d := Module.finrank K W₁
  let b' : Fin n → W₁ := fun i ↦ ⟨b i, Submodule.subset_span ⟨i, rfl⟩⟩
  let v' : Fin d → V := fun j ↦ ∑ i : Fin n, f.repr (b' i) j • a i
  have hu_eq : u = ∑ j : Fin d, v' j ⊗ₜ[K] (f j : W) := by
    rw [hab]
    have hb_eq (i : Fin n) : b i = ∑ j : Fin d, f.repr (b' i) j • (f j : W) := by
      have h := congrArg (W₁.subtype : W₁ →ₗ[K] W) (f.sum_repr (b' i)).symm
      simpa only [map_sum, map_smul, Submodule.coe_subtype] using h
    calc ∑ i : Fin n, a i ⊗ₜ[K] b i
        = ∑ i : Fin n, ∑ j : Fin d, (f.repr (b' i) j • a i) ⊗ₜ[K] (f j : W) := by
            refine Finset.sum_congr rfl fun i _ ↦ ?_
            conv_lhs => rw [hb_eq i]
            simp [TensorProduct.tmul_sum, TensorProduct.tmul_smul, TensorProduct.smul_tmul']
      _ = ∑ j : Fin d, v' j ⊗ₜ[K] (f j : W) := by
            rw [Finset.sum_comm]
            simp [v', TensorProduct.sum_tmul]
  obtain ⟨j₀, hj₀⟩ : ∃ j : Fin d, v' j ≠ 0 := by
    by_contra! hall
    exact hu (by simp [hu_eq, hall])
  obtain ⟨r, hr⟩ : ∃ r : ℕ, d = r + 1 := ⟨d - 1, (Nat.sub_add_cancel (Fin.pos j₀)).symm⟩
  let σ : Fin (r + 1) ≃ Fin d :=
    (Equiv.swap (0 : Fin (r + 1)) (Fin.cast hr j₀)).trans (finCongr hr.symm)
  let v : Fin (r + 1) → V := v' ∘ σ
  let w : Fin (r + 1) → W := fun j ↦ (f (σ j) : W)
  have hu_perm : u = ∑ j : Fin (r + 1), v j ⊗ₜ[K] w j := by
    rw [hu_eq, ← σ.sum_comp]
    rfl
  have hw_li : LinearIndependent K w :=
    (f.linearIndependent.map' W₁.subtype W₁.ker_subtype).comp σ σ.injective
  set D : Submodule K W := Submodule.span K (w '' (Set.univ \ {0}))
  have : FiniteDimensional K D := FiniteDimensional.span_of_finite K (Set.toFinite _)
  have hw0_notMem : w 0 ∉ (D : Set W) := fun hmem ↦
    linearIndependent_iff_notMem_span.mp hw_li 0 (by simpa [D] using hmem)
  have hdist_pos : 0 < Metric.infDist (w 0) (D : Set W) :=
    (D.isClosed_of_finiteDimensional.notMem_iff_infDist_pos ⟨0, D.zero_mem⟩).mp hw0_notMem
  have hv0_pos : 0 < ‖v 0‖ := norm_pos_iff.mpr (by simpa [v, σ] using hj₀)
  have hkey := mul_infDist_mul_norm_le_productSeminorm v w hw_li
    (t := 1 / 2) (by norm_num) (by norm_num)
  rw [← hu_perm, h0] at hkey
  exact (mul_pos (mul_pos (by norm_num) hdist_pos) hv0_pos).not_ge hkey

end CompleteFieldAlgebraic

section TensorTopology

variable {A V W : Type*} [SeminormedCommRing A] [SeminormedAddCommGroup V] [Module A V]
  [SeminormedAddCommGroup W] [Module A W]

/-- When `A` acts boundedly on `V`, the tensor topology `banachTensorTopology A V W` is finer than
the topology of `productSeminorm A V W`. -/
theorem banachTensorTopology_le_productSeminorm_of_left
    (hV : ∃ C : ℝ≥0, ∀ (a : A) (v : V), ‖a • v‖ ≤ C * ‖a‖ * ‖v‖) :
    banachTensorTopology A V W ≤
      (productSeminorm A V W).toSeminormedAddCommGroup.toUniformSpace.toTopologicalSpace := by
  let : SeminormedAddCommGroup (V ⊗[A] W) := (productSeminorm A V W).toSeminormedAddCommGroup
  have : IsUltrametricDist (V ⊗[A] W) :=
    IsUltrametricDist.isUltrametricDist_of_isNonarchimedean_norm
      (isNonarchimedean_productSeminorm A V W)
  obtain ⟨C, hC⟩ := hV
  have : ContinuousSMul A (V ⊗[A] W) :=
    TauCeti.continuousSMul_of_norm_smul_le ⟨C, fun a u ↦
      productSeminorm_smul_le_of_le_left (by positivity) (hC a) u⟩
  have htmul : Continuous fun p : V × W ↦ p.1 ⊗ₜ[A] p.2 :=
    (TensorProduct.mk A V W).continuous₂_of_bound 1 fun v w ↦ by
      rw [one_mul, TensorProduct.mk_apply]
      exact productSeminorm_tmul_le v w
  exact banachTensorTopology_le inferInstance inferInstance htmul

/-- When `A` acts boundedly on `W`, the tensor topology `banachTensorTopology A V W` is finer than
the topology of `productSeminorm A V W`. -/
theorem banachTensorTopology_le_productSeminorm_of_right
    (hW : ∃ C : ℝ≥0, ∀ (a : A) (w : W), ‖a • w‖ ≤ C * ‖a‖ * ‖w‖) :
    banachTensorTopology A V W ≤
      (productSeminorm A V W).toSeminormedAddCommGroup.toUniformSpace.toTopologicalSpace := by
  let : SeminormedAddCommGroup (V ⊗[A] W) := (productSeminorm A V W).toSeminormedAddCommGroup
  have : IsUltrametricDist (V ⊗[A] W) :=
    IsUltrametricDist.isUltrametricDist_of_isNonarchimedean_norm
      (isNonarchimedean_productSeminorm A V W)
  obtain ⟨C, hC⟩ := hW
  have : ContinuousSMul A (V ⊗[A] W) :=
    TauCeti.continuousSMul_of_norm_smul_le ⟨C, fun a u ↦
      productSeminorm_smul_le_of_le_right (by positivity) (hC a) u⟩
  have htmul : Continuous fun p : V × W ↦ p.1 ⊗ₜ[A] p.2 :=
    (TensorProduct.mk A V W).continuous₂_of_bound 1 fun v w ↦ by
      rw [one_mul, TensorProduct.mk_apply]
      exact productSeminorm_tmul_le v w
  exact banachTensorTopology_le inferInstance inferInstance htmul

/-- When `A` acts boundedly on `V`, `productSeminorm A V W` is uniformly continuous for
`banachTensorUniformSpace A V W`. -/
theorem uniformContinuous_productSeminorm
    (hV : ∃ C : ℝ≥0, ∀ (a : A) (v : V), ‖a • v‖ ≤ C * ‖a‖ * ‖v‖) :
    @UniformContinuous (V ⊗[A] W) ℝ (banachTensorUniformSpace A V W) _
      (productSeminorm A V W) := by
  have hcont0 : Filter.Tendsto (productSeminorm A V W)
      (@nhds (V ⊗[A] W)
        (productSeminorm A V W).toSeminormedAddCommGroup.toUniformSpace.toTopologicalSpace 0)
      (𝓝 0) := by
    let : SeminormedAddCommGroup (V ⊗[A] W) :=
      (productSeminorm A V W).toSeminormedAddCommGroup
    have h := continuous_norm.tendsto (0 : V ⊗[A] W)
    rw [norm_zero] at h
    exact h
  let : UniformSpace (V ⊗[A] W) := banachTensorUniformSpace A V W
  have : IsUniformAddGroup (V ⊗[A] W) := isUniformAddGroup_banachTensorUniformSpace A V W
  have hp : Filter.Tendsto (productSeminorm A V W) (𝓝 0) (𝓝 0) := by
    rw [banachTensorUniformSpace_toTopologicalSpace]
    exact hcont0.mono_left (nhds_mono (banachTensorTopology_le_productSeminorm_of_left hV))
  rw [UniformContinuous, uniformity_eq_comap_nhds_zero_swapped,
    Metric.uniformity_eq_comap_nhds_zero, Filter.tendsto_comap_iff]
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
    (hp.comp Filter.tendsto_comap) (fun _ ↦ dist_nonneg) fun xy ↦ by
      simp only [Function.comp_apply, Real.dist_eq]
      exact abs_sub_map_le_sub (productSeminorm A V W) xy.1 xy.2

/-- Balancing a pure tensor `v ⊗ₜ[A] w` by an integer power of a multiplicative pseudo-uniformiser
`ϖ`: when `‖v‖ * ‖w‖` is small enough relative to `δ ^ 2`, rescaling `(v, w)` to
`(ϖ ^ k • v, ϖ ^ (-k) • w)` puts both factors inside the `δ`-ball without changing `v ⊗ₜ[A] w`. -/
private theorem exists_zpow_smul_tmul_lt (ϖ : TauCeti.NormedRing.PseudoUniformizer A)
    {C₁ C₂ : ℝ≥0} (hC₁ : ∀ (a : A) (v : V), ‖a • v‖ ≤ C₁ * ‖a‖ * ‖v‖)
    (hC₂ : ∀ (a : A) (w : W), ‖a • w‖ ≤ C₂ * ‖a‖ * ‖w‖) {δ : ℝ} (hδ : 0 < δ) {v : V} {w : W}
    (hvw : ‖v‖ * ‖w‖ < ‖(ϖ.unit : A)‖ * δ ^ 2 / ((max (C₁ : ℝ) 1) * (max (C₂ : ℝ) 1))) :
    ∃ (v' : V) (w' : W), v' ⊗ₜ[A] w' = v ⊗ₜ[A] w ∧ ‖v'‖ < δ ∧ ‖w'‖ < δ := by
  set q := ‖(ϖ.unit : A)‖
  have hq0 : 0 < q := ϖ.norm_pos
  have hq1 : q < 1 := ϖ.norm_lt_one
  set B₁ : ℝ := max C₁ 1
  set B₂ : ℝ := max C₂ 1
  have hB₁ : 0 < B₁ := lt_of_lt_of_le one_pos (le_max_right _ _)
  have hB₂ : 0 < B₂ := lt_of_lt_of_le one_pos (le_max_right _ _)
  suffices ∃ k : ℤ, B₁ * q ^ k * ‖v‖ < δ ∧ B₂ * q ^ (-k) * ‖w‖ < δ by
    obtain ⟨k, hkv, hkw⟩ := this
    refine ⟨((ϖ.unit ^ k : Aˣ) : A) • v, ((ϖ.unit ^ (-k) : Aˣ) : A) • w, ?_, ?_, ?_⟩
    · rw [TensorProduct.smul_tmul, smul_smul, ← Units.val_mul, zpow_neg, mul_inv_cancel,
        Units.val_one, one_smul]
    · exact (hC₁ _ v).trans_lt (lt_of_le_of_lt (by
        rw [TauCeti.NormedRing.norm_units_zpow_of_norm_mul hq0 ϖ.norm_mul k]
        gcongr; exact le_max_left _ _) hkv)
    · exact (hC₂ _ w).trans_lt (lt_of_le_of_lt (by
        rw [TauCeti.NormedRing.norm_units_zpow_of_norm_mul hq0 ϖ.norm_mul (-k)]
        gcongr; exact le_max_left _ _) hkw)
  rcases (norm_nonneg v).eq_or_lt with hv0 | hv
  · obtain ⟨m, hm⟩ := exists_pow_lt_of_lt_one
      (div_pos hδ (mul_pos hB₂ (lt_of_le_of_lt (norm_nonneg w) (lt_add_one ‖w‖)))) hq1
    refine ⟨-(m : ℤ), by simp [← hv0, hδ], ?_⟩
    rw [neg_neg, zpow_natCast]
    calc B₂ * q ^ m * ‖w‖ = q ^ m * (B₂ * ‖w‖) := by ring
      _ ≤ q ^ m * (B₂ * (‖w‖ + 1)) := by gcongr; exact le_add_of_nonneg_right zero_le_one
      _ < δ := (lt_div_iff₀
          (mul_pos hB₂ (lt_of_le_of_lt (norm_nonneg w) (lt_add_one ‖w‖)))).mp hm
  rcases (norm_nonneg w).eq_or_lt with hw0 | hw
  · obtain ⟨m, hm⟩ := exists_pow_lt_of_lt_one (div_pos hδ (mul_pos hB₁ hv)) hq1
    refine ⟨(m : ℤ), ?_, by simp [← hw0, hδ]⟩
    calc B₁ * q ^ (m : ℤ) * ‖v‖ = q ^ m * (B₁ * ‖v‖) := by rw [zpow_natCast]; ring
      _ < δ := (lt_div_iff₀ (mul_pos hB₁ hv)).mp hm
  · obtain ⟨m, ⟨hm_gt, hm_le⟩, -⟩ :=
      TauCeti.existsUnique_zpow_mul_mem_Ioc hq0 hq1 (div_pos (mul_pos hB₁ hv) hδ)
    have hrew (j : ℤ) : q ^ j * (B₁ * ‖v‖ / δ) = B₁ * q ^ j * ‖v‖ / δ := by ring
    set k : ℤ := if q ^ m * (B₁ * ‖v‖ / δ) = 1 then m + 1 else m
    have hk : B₁ * q ^ k * ‖v‖ < δ ∧ q * δ ≤ B₁ * q ^ k * ‖v‖ := by
      by_cases h_eq : q ^ m * (B₁ * ‖v‖ / δ) = 1 <;> simp only [k, h_eq, ↓reduceIte]
      · have hm1 : B₁ * q ^ (m + 1) * ‖v‖ / δ = q := by
          rw [← hrew, zpow_add_one₀ hq0.ne', mul_right_comm, h_eq, one_mul]
        exact ⟨(div_lt_one hδ).mp (hm1.trans_lt hq1), ((div_eq_iff hδ.ne').mp hm1).ge⟩
      · exact ⟨(div_lt_one hδ).mp (hrew m ▸ hm_le.lt_of_ne h_eq),
          ((lt_div_iff₀ hδ).mp (hrew m ▸ hm_gt)).le⟩
    refine ⟨k, hk.1, lt_of_mul_lt_mul_left ?_ (mul_pos hq0 hδ).le⟩
    have hq_inv : q ^ k * q ^ (-k) = 1 := by
      rw [zpow_neg, mul_inv_cancel₀ (zpow_ne_zero _ hq0.ne')]
    calc (q * δ) * (B₂ * q ^ (-k) * ‖w‖)
        ≤ (B₁ * q ^ k * ‖v‖) * (B₂ * q ^ (-k) * ‖w‖) :=
          mul_le_mul_of_nonneg_right hk.2 (by positivity)
      _ = B₁ * B₂ * (q ^ k * q ^ (-k)) * (‖v‖ * ‖w‖) := by ring
      _ = B₁ * B₂ * (‖v‖ * ‖w‖) := by rw [hq_inv, mul_one]
      _ < B₁ * B₂ * (q * δ ^ 2 / (B₁ * B₂)) := by gcongr
      _ = (q * δ) * δ := by field_simp

section IsTate

variable [TauCeti.NormedRing.IsTate A]

/-- **Equality of uniformities**: over a Tate seminormed commutative ring `A` acting boundedly on
`V` and `W`, `banachTensorUniformSpace A V W` coincides with the uniformity induced by
`productSeminorm A V W`. -/
theorem banachTensorUniformSpace_eq_productSeminorm
    (hV : ∃ C : ℝ≥0, ∀ (a : A) (v : V), ‖a • v‖ ≤ C * ‖a‖ * ‖v‖)
    (hW : ∃ C : ℝ≥0, ∀ (a : A) (w : W), ‖a • w‖ ≤ C * ‖a‖ * ‖w‖) :
    banachTensorUniformSpace A V W =
      (productSeminorm A V W).toSeminormedAddCommGroup.toUniformSpace := by
  refine (isUniformAddGroup_banachTensorUniformSpace A V W).ext
    (productSeminorm A V W).toSeminormedAddCommGroup.to_isUniformAddGroup ?_
  rw [banachTensorUniformSpace_toTopologicalSpace]
  refine le_antisymm (nhds_mono (banachTensorTopology_le_productSeminorm_of_left hV)) ?_
  intro U hU
  let : TopologicalSpace (V ⊗[A] W) := banachTensorTopology A V W
  have : NonarchimedeanAddGroup (V ⊗[A] W) := nonarchimedeanAddGroup_banachTensorTopology A V W
  obtain ⟨G, hGU⟩ := NonarchimedeanAddGroup.is_nonarchimedean U hU
  have hcont := (continuous_tmul_banachTensorTopology A V W).tendsto ((0 : V), (0 : W))
  simp only [TensorProduct.zero_tmul] at hcont
  obtain ⟨U₁, hU₁, U₂, hU₂, hU₁₂⟩ := mem_nhds_prod_iff.mp
    (hcont (G.isOpen.mem_nhds G.zero_mem))
  obtain ⟨δ₁, hδ₁, hδ₁U⟩ := Metric.mem_nhds_iff.mp hU₁
  obtain ⟨δ₂, hδ₂, hδ₂U⟩ := Metric.mem_nhds_iff.mp hU₂
  set δ := min δ₁ δ₂
  have hδ : 0 < δ := lt_min hδ₁ hδ₂
  obtain ⟨ϖ⟩ := ‹TauCeti.NormedRing.IsTate A›.nonempty_pseudoUniformizer
  obtain ⟨C₁, hC₁⟩ := hV
  obtain ⟨C₂, hC₂⟩ := hW
  set r : ℝ := ‖(ϖ.unit : A)‖ * δ ^ 2 / ((max (C₁ : ℝ) 1) * (max (C₂ : ℝ) 1))
  have hr : 0 < r := by
    have := ϖ.norm_pos
    positivity
  refine Filter.mem_of_superset
    (@Metric.ball_mem_nhds _
      (productSeminorm A V W).toSeminormedAddCommGroup.toPseudoMetricSpace 0 r hr) ?_
  intro u hu
  have hlt : productSeminorm A V W u < r := by
    let : SeminormedAddCommGroup (V ⊗[A] W) :=
      (productSeminorm A V W).toSeminormedAddCommGroup
    rwa [Metric.mem_ball, dist_zero_right] at hu
  obtain ⟨-, n, v, w, rfl, hvw⟩ := exists_sum_tmul_eq_forall_lt_of_productSeminorm_lt hlt
  refine hGU (G.sum_mem fun i _ ↦ ?_)
  obtain ⟨v', w', hbal, hv', hw'⟩ := exists_zpow_smul_tmul_lt ϖ hC₁ hC₂ hδ (hvw i)
  rw [← hbal]
  exact @hU₁₂ (v', w') ⟨hδ₁U (mem_ball_zero_iff.mpr (hv'.trans_le (min_le_left _ _))),
    hδ₂U (mem_ball_zero_iff.mpr (hw'.trans_le (min_le_right _ _)))⟩

/-- **Equality of topologies**: over a Tate seminormed commutative ring `A` acting boundedly on
`V` and `W`, `banachTensorTopology A V W` coincides with the topology induced by
`productSeminorm A V W`. -/
theorem banachTensorTopology_eq_productSeminorm
    (hV : ∃ C : ℝ≥0, ∀ (a : A) (v : V), ‖a • v‖ ≤ C * ‖a‖ * ‖v‖)
    (hW : ∃ C : ℝ≥0, ∀ (a : A) (w : W), ‖a • w‖ ≤ C * ‖a‖ * ‖w‖) :
    banachTensorTopology A V W =
      (productSeminorm A V W).toSeminormedAddCommGroup.toUniformSpace.toTopologicalSpace := by
  rw [← banachTensorUniformSpace_toTopologicalSpace]
  exact congrArg (@UniformSpace.toTopologicalSpace (V ⊗[A] W))
    (banachTensorUniformSpace_eq_productSeminorm hV hW)

/-- **Neighbourhood basis of the tensor topology**: over a Tate seminormed commutative ring `A`
acting boundedly on `V` and `W`, the positive-radius open balls of `productSeminorm A V W` form a
neighbourhood basis of `0` for `banachTensorTopology A V W`. -/
theorem hasBasis_banachTensorTopology
    (hV : ∃ C : ℝ≥0, ∀ (a : A) (v : V), ‖a • v‖ ≤ C * ‖a‖ * ‖v‖)
    (hW : ∃ C : ℝ≥0, ∀ (a : A) (w : W), ‖a • w‖ ≤ C * ‖a‖ * ‖w‖) :
    (@nhds (V ⊗[A] W) (banachTensorTopology A V W) 0).HasBasis (0 < ·)
      fun r ↦ {u | productSeminorm A V W u < r} := by
  rw [banachTensorTopology_eq_productSeminorm hV hW]
  let : SeminormedAddCommGroup (V ⊗[A] W) := (productSeminorm A V W).toSeminormedAddCommGroup
  refine (Metric.nhds_basis_ball (x := (0 : V ⊗[A] W))).congr (fun _ ↦ Iff.rfl) fun r _ ↦ ?_
  ext u
  simp only [Metric.mem_ball, dist_zero_right]
  rfl

end IsTate

/-- Over a nontrivially normed field `L`, any nontrivial tensor product `V ⊗[L] W` of seminormed
`L`-spaces has nondiscrete Banach tensor topology. -/
theorem not_discreteTopology_banachTensorTopology {L V W : Type*} [NontriviallyNormedField L]
    [SeminormedAddCommGroup V] [NormedSpace L V] [SeminormedAddCommGroup W] [NormedSpace L W]
    [Nontrivial (V ⊗[L] W)] :
    ¬ @DiscreteTopology (V ⊗[L] W) (banachTensorTopology L V W) := by
  intro hdisc
  have h0 : ({0} : Set (V ⊗[L] W)) ∈ @nhds (V ⊗[L] W) (banachTensorTopology L V W) 0 := by
    let : TopologicalSpace (V ⊗[L] W) := banachTensorTopology L V W
    exact (isOpen_discrete {0}).mem_nhds rfl
  have hbasis := hasBasis_banachTensorTopology (A := L) (V := V) (W := W)
    ⟨1, fun a v ↦ by simpa using norm_smul_le a v⟩
    ⟨1, fun a w ↦ by simpa using norm_smul_le a w⟩
  obtain ⟨r, hr, hsub⟩ := hbasis.mem_iff.mp h0
  obtain ⟨u, hu⟩ := exists_ne (0 : V ⊗[L] W)
  have hden : 0 < productSeminorm L V W u + 1 :=
    lt_of_le_of_lt (apply_nonneg _ _) (lt_add_one _)
  obtain ⟨a, ha0, ha⟩ := NormedField.exists_norm_lt L (div_pos hr hden)
  have hlt : productSeminorm L V W (a • u) < r := by
    rw [productSeminorm_smul]
    calc ‖a‖ * productSeminorm L V W u
        ≤ ‖a‖ * (productSeminorm L V W u + 1) := by
            gcongr; exact le_add_of_nonneg_right zero_le_one
      _ < r := (lt_div_iff₀ hden).mp ha
  exact smul_ne_zero (norm_pos_iff.mp ha0) hu (Set.mem_singleton_iff.mp (hsub hlt))

end TensorTopology

namespace CompletedTensor

section Def

variable (A V W : Type*) [CommRing A] [TopologicalSpace A]
  [SeminormedAddCommGroup V] [Module A V] [SeminormedAddCommGroup W] [Module A W]

/-- **The completed product norm** (or seminorm) on `V ⊗̂_A W`: the continuous extension of
`productSeminorm A V W` along `V ⊗[A] W → V ⊗̂_A W`. Over a Tate seminormed commutative ring `A`
acting boundedly on `V` and `W`, it is a definite ultrametric norm whose open balls generate the
topology of `V ⊗̂_A W`. -/
noncomputable def productNorm (z : CompletedTensor A V W) : ℝ :=
  @Completion.extension (V ⊗[A] W) (banachTensorUniformSpace A V W) ℝ _
    (productSeminorm A V W) (equivCompletion A V W z)

/-- `productNorm A V W` is uniformly continuous on `V ⊗̂_A W`. -/
theorem uniformContinuous_productNorm : UniformContinuous (productNorm A V W) := by
  have hsmul : @ContinuousSMul A (V ⊗[A] W) _ _
      (banachTensorUniformSpace A V W).toTopologicalSpace := by
    rw [banachTensorUniformSpace_toTopologicalSpace]
    exact continuousSMul_banachTensorTopology A V W
  let : UniformSpace (V ⊗[A] W) := banachTensorUniformSpace A V W
  have : IsUniformAddGroup (V ⊗[A] W) := isUniformAddGroup_banachTensorUniformSpace A V W
  have : ContinuousSMul A (V ⊗[A] W) := hsmul
  have : UniformContinuousConstSMul A (V ⊗[A] W) :=
    uniformContinuousConstSMul_of_continuousConstSMul A (V ⊗[A] W)
  have heq : UniformContinuous (equivCompletion A V W) :=
    uniformContinuous_addMonoidHom_of_continuous (equivCompletion A V W).continuous
  exact Completion.uniformContinuous_extension.comp heq

/-- `productNorm A V W` is continuous on `V ⊗̂_A W`. -/
@[continuity, fun_prop]
theorem continuous_productNorm : Continuous (productNorm A V W) :=
  (uniformContinuous_productNorm A V W).continuous

end Def

section BoundedLeft

variable {A V W : Type*} [SeminormedCommRing A] [SeminormedAddCommGroup V] [Module A V]
  [SeminormedAddCommGroup W] [Module A W]

/-- On the image of the algebraic tensor product `V ⊗[A] W`, `productNorm` agrees with
`productSeminorm`. -/
theorem productNorm_toCompletion
    (hV : ∃ C : ℝ≥0, ∀ (a : A) (v : V), ‖a • v‖ ≤ C * ‖a‖ * ‖v‖) (u : V ⊗[A] W) :
    productNorm A V W (toCompletion A V W u) = productSeminorm A V W u := by
  simp only [productNorm, equivCompletion_toCompletion]
  exact @Completion.extension_coe (V ⊗[A] W) (banachTensorUniformSpace A V W) ℝ _ _ _
    (uniformContinuous_productSeminorm hV) u

/-- Under a contractive `A`-action on `V`, `productNorm` agrees with `productSeminorm` on the
algebraic tensor product (`productNorm_coe`). -/
@[simp]
theorem productNorm_coe [IsBoundedSMul A V] (u : V ⊗[A] W) :
    productNorm A V W (toCompletion A V W u) = productSeminorm A V W u :=
  productNorm_toCompletion ⟨1, fun a v ↦ by simpa using norm_smul_le a v⟩ u

/-- `productNorm` vanishes at `0`. -/
theorem productNorm_zero_of_bounded
    (hV : ∃ C : ℝ≥0, ∀ (a : A) (v : V), ‖a • v‖ ≤ C * ‖a‖ * ‖v‖) :
    productNorm A V W 0 = 0 := by
  rw [← map_zero (toCompletion A V W), productNorm_toCompletion hV, map_zero]

/-- Under a contractive `A`-action on `V`, `productNorm A V W 0 = 0`. -/
@[simp]
theorem productNorm_zero [IsBoundedSMul A V] : productNorm A V W 0 = 0 :=
  productNorm_zero_of_bounded ⟨1, fun a v ↦ by simpa using norm_smul_le a v⟩

/-- `productNorm` is nonnegative. -/
theorem productNorm_nonneg_of_bounded
    (hV : ∃ C : ℝ≥0, ∀ (a : A) (v : V), ‖a • v‖ ≤ C * ‖a‖ * ‖v‖)
    (z : CompletedTensor A V W) : 0 ≤ productNorm A V W z := by
  refine (denseRange_toCompletion A V W).induction_on z
    (isClosed_le continuous_const (continuous_productNorm A V W)) fun u ↦ ?_
  rw [productNorm_toCompletion hV]
  exact apply_nonneg _ _

/-- Under a contractive `A`-action on `V`, `productNorm` is nonnegative. -/
theorem productNorm_nonneg [IsBoundedSMul A V] (z : CompletedTensor A V W) :
    0 ≤ productNorm A V W z :=
  productNorm_nonneg_of_bounded ⟨1, fun a v ↦ by simpa using norm_smul_le a v⟩ z

/-- `productNorm` is invariant under negation. -/
theorem productNorm_neg_of_bounded
    (hV : ∃ C : ℝ≥0, ∀ (a : A) (v : V), ‖a • v‖ ≤ C * ‖a‖ * ‖v‖)
    (z : CompletedTensor A V W) : productNorm A V W (-z) = productNorm A V W z := by
  refine (denseRange_toCompletion A V W).induction_on z
    (isClosed_eq ((continuous_productNorm A V W).comp continuous_neg)
      (continuous_productNorm A V W)) fun u ↦ ?_
  rw [← map_neg, productNorm_toCompletion hV, productNorm_toCompletion hV, map_neg_eq_map]

/-- Under a contractive `A`-action on `V`, `productNorm` is invariant under negation. -/
@[simp]
theorem productNorm_neg [IsBoundedSMul A V] (z : CompletedTensor A V W) :
    productNorm A V W (-z) = productNorm A V W z :=
  productNorm_neg_of_bounded ⟨1, fun a v ↦ by simpa using norm_smul_le a v⟩ z

/-- **Ultrametric inequality** for `productNorm` on `V ⊗̂_A W`. -/
theorem productNorm_add_le_max_of_bounded
    (hV : ∃ C : ℝ≥0, ∀ (a : A) (v : V), ‖a • v‖ ≤ C * ‖a‖ * ‖v‖)
    (z₁ z₂ : CompletedTensor A V W) :
    productNorm A V W (z₁ + z₂) ≤ max (productNorm A V W z₁) (productNorm A V W z₂) := by
  have hclosed₁ : ∀ u₁ : V ⊗[A] W,
      productNorm A V W (toCompletion A V W u₁ + z₂) ≤
        max (productNorm A V W (toCompletion A V W u₁)) (productNorm A V W z₂) := fun u₁ ↦ by
    refine (denseRange_toCompletion A V W).induction_on z₂
      (isClosed_le ((continuous_productNorm A V W).comp (continuous_const.add continuous_id))
        (continuous_const.max (continuous_productNorm A V W))) fun u₂ ↦ ?_
    rw [← map_add, productNorm_toCompletion hV, productNorm_toCompletion hV,
      productNorm_toCompletion hV]
    exact productSeminorm_add_le_max u₁ u₂
  exact (denseRange_toCompletion A V W).induction_on z₁
    (isClosed_le ((continuous_productNorm A V W).comp (continuous_id.add continuous_const))
      ((continuous_productNorm A V W).max continuous_const)) hclosed₁

/-- Under a contractive `A`-action on `V`, `productNorm` satisfies the ultrametric inequality. -/
theorem productNorm_add_le_max [IsBoundedSMul A V] (z₁ z₂ : CompletedTensor A V W) :
    productNorm A V W (z₁ + z₂) ≤ max (productNorm A V W z₁) (productNorm A V W z₂) :=
  productNorm_add_le_max_of_bounded ⟨1, fun a v ↦ by simpa using norm_smul_le a v⟩ z₁ z₂

/-- Ultrametric inequality for differences under `productNorm`. -/
theorem productNorm_sub_le_max_of_bounded
    (hV : ∃ C : ℝ≥0, ∀ (a : A) (v : V), ‖a • v‖ ≤ C * ‖a‖ * ‖v‖)
    (z₁ z₂ : CompletedTensor A V W) :
    productNorm A V W (z₁ - z₂) ≤ max (productNorm A V W z₁) (productNorm A V W z₂) := by
  simpa [sub_eq_add_neg, productNorm_neg_of_bounded hV] using
    productNorm_add_le_max_of_bounded hV z₁ (-z₂)

/-- Under a contractive `A`-action on `V`, `productNorm` satisfies the ultrametric inequality on
differences. -/
theorem productNorm_sub_le_max [IsBoundedSMul A V] (z₁ z₂ : CompletedTensor A V W) :
    productNorm A V W (z₁ - z₂) ≤ max (productNorm A V W z₁) (productNorm A V W z₂) :=
  productNorm_sub_le_max_of_bounded ⟨1, fun a v ↦ by simpa using norm_smul_le a v⟩ z₁ z₂

/-- On elementary tensors `v ⊗ w`, `productNorm` is at most `‖v‖ * ‖w‖`. -/
theorem productNorm_tmul_le_of_bounded
    (hV : ∃ C : ℝ≥0, ∀ (a : A) (v : V), ‖a • v‖ ≤ C * ‖a‖ * ‖v‖) (v : V) (w : W) :
    productNorm A V W (tmul A V W v w) ≤ ‖v‖ * ‖w‖ := by
  rw [← toCompletion_tmul, productNorm_toCompletion hV]
  exact productSeminorm_tmul_le v w

/-- Under a contractive `A`-action on `V`, `productNorm A V W (tmul A V W v w) ≤ ‖v‖ * ‖w‖`. -/
theorem productNorm_tmul_le [IsBoundedSMul A V] (v : V) (w : W) :
    productNorm A V W (tmul A V W v w) ≤ ‖v‖ * ‖w‖ :=
  productNorm_tmul_le_of_bounded ⟨1, fun a v ↦ by simpa using norm_smul_le a v⟩ v w

/-- **Infinite-sum bound for `productNorm`**: if `HasSum f z` in `V ⊗̂_A W` and every term has
`productNorm` at most `b ≥ 0`, then `productNorm A V W z ≤ b`. -/
theorem productNorm_of_hasSum_le
    (hV : ∃ C : ℝ≥0, ∀ (a : A) (v : V), ‖a • v‖ ≤ C * ‖a‖ * ‖v‖)
    {ι : Type*} {f : ι → CompletedTensor A V W} {z : CompletedTensor A V W} (hf : HasSum f z)
    {b : ℝ} (hb : 0 ≤ b) (hfb : ∀ i, productNorm A V W (f i) ≤ b) :
    productNorm A V W z ≤ b := by
  have hsum_fin (s : Finset ι) : productNorm A V W (∑ i ∈ s, f i) ≤ b := by
    classical
    induction s using Finset.induction_on with
    | empty => simpa [productNorm_zero_of_bounded hV] using hb
    | insert i s hi ih =>
      rw [Finset.sum_insert hi]
      exact (productNorm_add_le_max_of_bounded hV _ _).trans (max_le (hfb i) ih)
  have hT : Tendsto (fun s : Finset ι ↦ productNorm A V W (∑ i ∈ s, f i))
      atTop (𝓝 (productNorm A V W z)) :=
    ((continuous_productNorm A V W).tendsto z).comp
      (by simpa only [HasSum, SummationFilter.unconditional_filter] using hf)
  exact le_of_tendsto hT (Eventually.of_forall hsum_fin)

/-- If `a : A` scales norms on `V` by at most `C ≥ 0`, it scales `productNorm` on `V ⊗̂_A W` by at
most `C`. -/
theorem productNorm_smul_le_of_le
    (hV : ∃ C₀ : ℝ≥0, ∀ (a : A) (v : V), ‖a • v‖ ≤ C₀ * ‖a‖ * ‖v‖)
    {a : A} {C : ℝ} (hC : 0 ≤ C) (ha : ∀ v : V, ‖a • v‖ ≤ C * ‖v‖)
    (z : CompletedTensor A V W) :
    productNorm A V W (a • z) ≤ C * productNorm A V W z := by
  refine (denseRange_toCompletion A V W).induction_on z
    (isClosed_le ((continuous_productNorm A V W).comp (continuous_const_smul a))
      (continuous_const.mul (continuous_productNorm A V W))) fun u ↦ ?_
  rw [← map_smul, productNorm_toCompletion hV, productNorm_toCompletion hV]
  exact productSeminorm_smul_le_of_le_left hC ha u

/-- Under a contractive `A`-action on `V`, `productNorm` is submultiplicative for scalar
multiplication. -/
theorem productNorm_smul_le [IsBoundedSMul A V] (a : A) (z : CompletedTensor A V W) :
    productNorm A V W (a • z) ≤ ‖a‖ * productNorm A V W z :=
  productNorm_smul_le_of_le ⟨1, fun a v ↦ by simpa using norm_smul_le a v⟩
    (norm_nonneg a) (norm_smul_le a) z

/-- **Universal norm bound on `CompletedTensor.lift`**: for a bounded `A`-bilinear map `β` into a
complete ultrametric normed `A`-module `M` with continuous action, the lifted continuous linear
map satisfies `‖lift β hβ z‖ ≤ C * productNorm A V W z`. -/
theorem norm_lift_le_mul_productNorm
    (hV : ∃ C₀ : ℝ≥0, ∀ (a : A) (v : V), ‖a • v‖ ≤ C₀ * ‖a‖ * ‖v‖)
    {M : Type*} [NormedAddCommGroup M] [IsUltrametricDist M] [CompleteSpace M]
    [Module A M] [ContinuousSMul A M] (β : V →ₗ[A] W →ₗ[A] M)
    (hβ : Continuous fun p : V × W ↦ β p.1 p.2) {C : ℝ} (hC : 0 ≤ C)
    (hbound : ∀ v w, ‖β v w‖ ≤ C * (‖v‖ * ‖w‖)) (z : CompletedTensor A V W) :
    ‖lift β hβ z‖ ≤ C * productNorm A V W z := by
  refine (denseRange_toCompletion A V W).induction_on z
    (isClosed_le (continuous_norm.comp (lift β hβ).continuous)
      (continuous_const.mul (continuous_productNorm A V W))) fun u ↦ ?_
  rw [lift_toCompletion, productNorm_toCompletion hV]
  exact norm_lift_le_mul_productSeminorm β hC hbound u

/-- Exchanging the factors via `CompletedTensor.comm` preserves `productNorm`. -/
theorem productNorm_comm_of_bounded
    (hV : ∃ C : ℝ≥0, ∀ (a : A) (v : V), ‖a • v‖ ≤ C * ‖a‖ * ‖v‖)
    (hW : ∃ C : ℝ≥0, ∀ (a : A) (w : W), ‖a • w‖ ≤ C * ‖a‖ * ‖w‖)
    (z : CompletedTensor A V W) :
    productNorm A W V (comm A V W z) = productNorm A V W z := by
  refine (denseRange_toCompletion A V W).induction_on z
    (isClosed_eq ((continuous_productNorm A W V).comp (comm A V W).continuous)
      (continuous_productNorm A V W)) fun u ↦ ?_
  rw [comm_toCompletion, productNorm_toCompletion hW, productNorm_toCompletion hV,
    productSeminorm_comm]

/-- Under contractive `A`-actions, `CompletedTensor.comm` preserves `productNorm`. -/
@[simp]
theorem productNorm_comm [IsBoundedSMul A V] [IsBoundedSMul A W] (z : CompletedTensor A V W) :
    productNorm A W V (comm A V W z) = productNorm A V W z :=
  productNorm_comm_of_bounded ⟨1, fun a v ↦ by simpa using norm_smul_le a v⟩
    ⟨1, fun a w ↦ by simpa using norm_smul_le a w⟩ z

/-- On `A ⊗̂_A M` for a complete ultrametric normed `A`-module `M` with contractive action over a
norm-one commutative ring `A`, `productNorm` is the norm of the image under `lid A M`. -/
theorem productNorm_eq_norm_lid [NormOneClass A] {M : Type*} [NormedAddCommGroup M]
    [IsUltrametricDist M] [CompleteSpace M] [Module A M] [IsBoundedSMul A M]
    (z : CompletedTensor A A M) : productNorm A A M z = ‖lid A M z‖ := by
  refine (denseRange_toCompletion A A M).induction_on z
    (isClosed_eq (continuous_productNorm A A M) (continuous_norm.comp (lid A M).continuous))
    fun u ↦ ?_
  rw [productNorm_coe, lid_toCompletion, productSeminorm_eq_norm_lid]

/-- On `M ⊗̂_A A` for a complete ultrametric normed `A`-module `M` with contractive action over a
norm-one commutative ring `A`, `productNorm` is the norm of the image under `rid A M`. -/
theorem productNorm_eq_norm_rid [NormOneClass A] {M : Type*} [NormedAddCommGroup M]
    [IsUltrametricDist M] [CompleteSpace M] [Module A M] [IsBoundedSMul A M]
    (z : CompletedTensor A M A) : productNorm A M A z = ‖rid A M z‖ := by
  refine (denseRange_toCompletion A M A).induction_on z
    (isClosed_eq (continuous_productNorm A M A) (continuous_norm.comp (rid A M).continuous))
    fun u ↦ ?_
  rw [productNorm_coe, rid_toCompletion, productSeminorm_eq_norm_rid]

/-- Tensoring a zero module on the left gives `productNorm` zero on the entire completion. -/
@[simp]
theorem productNorm_eq_zero_of_subsingleton_left [IsBoundedSMul A V] [Subsingleton V]
    (z : CompletedTensor A V W) : productNorm A V W z = 0 := by
  refine (denseRange_toCompletion A V W).induction_on z
    (isClosed_eq (continuous_productNorm A V W) continuous_const) fun u ↦ ?_
  simp

/-- Tensoring a zero module on the right gives `productNorm` zero on the entire completion. -/
@[simp]
theorem productNorm_eq_zero_of_subsingleton_right [IsBoundedSMul A V] [Subsingleton W]
    (z : CompletedTensor A V W) : productNorm A V W z = 0 := by
  refine (denseRange_toCompletion A V W).induction_on z
    (isClosed_eq (continuous_productNorm A V W) continuous_const) fun u ↦ ?_
  simp

end BoundedLeft

section IsTateCompletion

/-- When a uniform additive group structure on `V ⊗[A] W` agrees with that of `productSeminorm`,
the open balls of `Completion.extension (productSeminorm A V W)` form a neighbourhood basis of `0`
in `Completion (V ⊗[A] W)`. -/
private theorem hasBasis_nhds_zero_completion_productSeminorm {A V W : Type*} [CommRing A]
    [SeminormedAddCommGroup V] [Module A V] [SeminormedAddCommGroup W] [Module A W]
    [u : UniformSpace (V ⊗[A] W)] [hu_grp : IsUniformAddGroup (V ⊗[A] W)]
    (hu : u = (productSeminorm A V W).toSeminormedAddCommGroup.toUniformSpace) :
    (𝓝 (0 : Completion (V ⊗[A] W))).HasBasis (0 < ·)
      fun r ↦ {w | Completion.extension (productSeminorm A V W) w < r} := by
  subst hu
  have hgrp : hu_grp = @SeminormedAddCommGroup.to_isUniformAddGroup (V ⊗[A] W)
      (productSeminorm A V W).toSeminormedAddCommGroup :=
    Subsingleton.elim _ _
  subst hgrp
  let : SeminormedAddCommGroup (V ⊗[A] W) := (productSeminorm A V W).toSeminormedAddCommGroup
  have hnorm (w : Completion (V ⊗[A] W)) :
      ‖w‖ = Completion.extension (productSeminorm A V W) w := by
    refine Completion.induction_on w
      (isClosed_eq continuous_norm Completion.continuous_extension) fun x ↦ ?_
    have huc : UniformContinuous (productSeminorm A V W) := uniformContinuous_norm
    rw [Completion.norm_coe, Completion.extension_coe huc x]
    rfl
  refine (Metric.nhds_basis_ball (x := (0 : Completion (V ⊗[A] W)))).congr (fun _ ↦ Iff.rfl)
    fun r _ ↦ ?_
  ext w
  simp [Metric.mem_ball, dist_zero_right, hnorm]

variable {A V W : Type*} [SeminormedCommRing A] [TauCeti.NormedRing.IsTate A]
  [SeminormedAddCommGroup V] [Module A V] [SeminormedAddCommGroup W] [Module A W]

/-- **Norm-ball basis of the completion topology**: over a Tate seminormed commutative ring `A`
acting boundedly on `V` and `W`, the positive-radius open balls of `productNorm A V W` form a
neighbourhood basis of `0` in `CompletedTensor A V W`. -/
theorem hasBasis_nhds_zero_productNorm_of_bounded
    (hV : ∃ C : ℝ≥0, ∀ (a : A) (v : V), ‖a • v‖ ≤ C * ‖a‖ * ‖v‖)
    (hW : ∃ C : ℝ≥0, ∀ (a : A) (w : W), ‖a • w‖ ≤ C * ‖a‖ * ‖w‖) :
    (𝓝 (0 : CompletedTensor A V W)).HasBasis (0 < ·)
      fun r ↦ {z | productNorm A V W z < r} := by
  have hsmul : @ContinuousSMul A (V ⊗[A] W) _ _
      (banachTensorUniformSpace A V W).toTopologicalSpace := by
    rw [banachTensorUniformSpace_toTopologicalSpace]
    exact continuousSMul_banachTensorTopology A V W
  let : UniformSpace (V ⊗[A] W) := banachTensorUniformSpace A V W
  have : IsUniformAddGroup (V ⊗[A] W) := isUniformAddGroup_banachTensorUniformSpace A V W
  have : ContinuousSMul A (V ⊗[A] W) := hsmul
  have : UniformContinuousConstSMul A (V ⊗[A] W) :=
    uniformContinuousConstSMul_of_continuousConstSMul A (V ⊗[A] W)
  have hb := hasBasis_nhds_zero_completion_productSeminorm
    (banachTensorUniformSpace_eq_productSeminorm hV hW)
  have hcomap : 𝓝 (0 : CompletedTensor A V W) =
      Filter.comap (equivCompletion A V W) (𝓝 (0 : Completion (V ⊗[A] W))) := by
    simpa [map_zero] using (equivCompletion A V W).toHomeomorph.nhds_eq_comap 0
  rw [hcomap]
  exact hb.comap (equivCompletion A V W)

/-- Under contractive `A`-actions over a Tate seminormed commutative ring `A`, the positive-radius
open balls of `productNorm A V W` form a neighbourhood basis of `0` in `CompletedTensor A V W`. -/
theorem hasBasis_nhds_zero_productNorm [IsBoundedSMul A V] [IsBoundedSMul A W] :
    (𝓝 (0 : CompletedTensor A V W)).HasBasis (0 < ·)
      fun r ↦ {z | productNorm A V W z < r} :=
  hasBasis_nhds_zero_productNorm_of_bounded ⟨1, fun a v ↦ by simpa using norm_smul_le a v⟩
    ⟨1, fun a w ↦ by simpa using norm_smul_le a w⟩

/-- Bundled `AddGroupNorm` on `V ⊗̂_A W` induced by `productNorm` over a Tate seminormed
commutative ring `A` acting boundedly on `V` and `W`. -/
noncomputable def productNormAddGroupNorm
    (hV : ∃ C : ℝ≥0, ∀ (a : A) (v : V), ‖a • v‖ ≤ C * ‖a‖ * ‖v‖)
    (hW : ∃ C : ℝ≥0, ∀ (a : A) (w : W), ‖a • w‖ ≤ C * ‖a‖ * ‖w‖) :
    AddGroupNorm (CompletedTensor A V W) where
  toFun := productNorm A V W
  map_zero' := productNorm_zero_of_bounded hV
  add_le' z₁ z₂ := (productNorm_add_le_max_of_bounded hV z₁ z₂).trans
    (max_le_add_of_nonneg (productNorm_nonneg_of_bounded hV z₁)
      (productNorm_nonneg_of_bounded hV z₂))
  neg' := productNorm_neg_of_bounded hV
  eq_zero_of_map_eq_zero' z hz := by
    by_contra hne
    obtain ⟨r, hr, hsub⟩ := (hasBasis_nhds_zero_productNorm_of_bounded hV hW).mem_iff.mp
      (isOpen_compl_singleton.mem_nhds (Ne.symm hne))
    exact hsub (by simp [hz, hr]) rfl

/-- `productNormAddGroupNorm` evaluates to `productNorm A V W`. -/
@[simp]
theorem productNormAddGroupNorm_apply
    (hV : ∃ C : ℝ≥0, ∀ (a : A) (v : V), ‖a • v‖ ≤ C * ‖a‖ * ‖v‖)
    (hW : ∃ C : ℝ≥0, ∀ (a : A) (w : W), ‖a • w‖ ≤ C * ‖a‖ * ‖w‖)
    (z : CompletedTensor A V W) :
    productNormAddGroupNorm hV hW z = productNorm A V W z :=
  (rfl)

/-- **Definiteness of `productNorm`** on `V ⊗̂_A W` over a Tate seminormed commutative ring with
bounded module actions. -/
theorem productNorm_eq_zero_iff_of_bounded
    (hV : ∃ C : ℝ≥0, ∀ (a : A) (v : V), ‖a • v‖ ≤ C * ‖a‖ * ‖v‖)
    (hW : ∃ C : ℝ≥0, ∀ (a : A) (w : W), ‖a • w‖ ≤ C * ‖a‖ * ‖w‖)
    {z : CompletedTensor A V W} :
    productNorm A V W z = 0 ↔ z = 0 :=
  map_eq_zero_iff_eq_zero (productNormAddGroupNorm hV hW)

/-- Under contractive `A`-actions over a Tate seminormed commutative ring `A`,
`productNorm A V W z = 0 ↔ z = 0`. -/
@[simp]
theorem productNorm_eq_zero_iff [IsBoundedSMul A V] [IsBoundedSMul A W]
    {z : CompletedTensor A V W} : productNorm A V W z = 0 ↔ z = 0 :=
  productNorm_eq_zero_iff_of_bounded ⟨1, fun a v ↦ by simpa using norm_smul_le a v⟩
    ⟨1, fun a w ↦ by simpa using norm_smul_le a w⟩

/-- The uniformity of `CompletedTensor A V W` agrees with that induced by
`productNormAddGroupNorm`. -/
theorem uniformity_eq_productNorm
    (hV : ∃ C : ℝ≥0, ∀ (a : A) (v : V), ‖a • v‖ ≤ C * ‖a‖ * ‖v‖)
    (hW : ∃ C : ℝ≥0, ∀ (a : A) (w : W), ‖a • w‖ ≤ C * ‖a‖ * ‖w‖) :
    𝓤 (CompletedTensor A V W) =
      @uniformity (CompletedTensor A V W)
        (productNormAddGroupNorm hV hW).toNormedAddCommGroup.toUniformSpace := by
  let g := (productNormAddGroupNorm hV hW).toNormedAddCommGroup
  have hd (x y : CompletedTensor A V W) : @dist _ g.toDist x y = productNorm A V W (-x + y) := rfl
  have hb := (hasBasis_nhds_zero_productNorm_of_bounded hV hW).uniformity_of_nhds_zero
  refine hb.eq_of_same_basis
    ((@Metric.uniformity_basis_dist _ g.toPseudoMetricSpace).congr (fun _ ↦ Iff.rfl) ?_)
  intro ε _
  ext ⟨x, y⟩
  simp only [Set.mem_ofPred_eq, hd, sub_eq_add_neg, add_comm y (-x)]

/-- **Compatible `NormedAddCommGroup` structure** on `V ⊗̂_A W` over a Tate seminormed commutative
ring `A` acting boundedly on `V` and `W`, with norm `productNorm A V W` and with the existing
uniformity and topology of `CompletedTensor A V W` retained definitionally. -/
noncomputable abbrev productNormedAddCommGroup
    (hV : ∃ C : ℝ≥0, ∀ (a : A) (v : V), ‖a • v‖ ≤ C * ‖a‖ * ‖v‖)
    (hW : ∃ C : ℝ≥0, ∀ (a : A) (w : W), ‖a • w‖ ≤ C * ‖a‖ * ‖w‖) :
    NormedAddCommGroup (CompletedTensor A V W) :=
  let base := (productNormAddGroupNorm hV hW).toNormedAddCommGroup
  { base with
    toMetricSpace := base.toMetricSpace.replaceUniformity (uniformity_eq_productNorm hV hW) }

/-- The norm of `productNormedAddCommGroup` is `productNorm A V W`. -/
@[simp]
theorem norm_productNormedAddCommGroup
    (hV : ∃ C : ℝ≥0, ∀ (a : A) (v : V), ‖a • v‖ ≤ C * ‖a‖ * ‖v‖)
    (hW : ∃ C : ℝ≥0, ∀ (a : A) (w : W), ‖a • w‖ ≤ C * ‖a‖ * ‖w‖)
    (z : CompletedTensor A V W) :
    @norm (CompletedTensor A V W) (productNormedAddCommGroup hV hW).toNorm z =
      productNorm A V W z :=
  (rfl)

/-- `productNormedAddCommGroup` retains the existing uniform space of `CompletedTensor A V W`. -/
@[simp]
theorem uniformSpace_productNormedAddCommGroup
    (hV : ∃ C : ℝ≥0, ∀ (a : A) (v : V), ‖a • v‖ ≤ C * ‖a‖ * ‖v‖)
    (hW : ∃ C : ℝ≥0, ∀ (a : A) (w : W), ‖a • w‖ ≤ C * ‖a‖ * ‖w‖) :
    (productNormedAddCommGroup hV hW).toUniformSpace =
      (inferInstance : UniformSpace (CompletedTensor A V W)) :=
  (rfl)

/-- `productNormedAddCommGroup` is ultrametric. -/
theorem isUltrametricDist_productNormedAddCommGroup
    (hV : ∃ C : ℝ≥0, ∀ (a : A) (v : V), ‖a • v‖ ≤ C * ‖a‖ * ‖v‖)
    (hW : ∃ C : ℝ≥0, ∀ (a : A) (w : W), ‖a • w‖ ≤ C * ‖a‖ * ‖w‖) :
    letI := productNormedAddCommGroup hV hW
    IsUltrametricDist (CompletedTensor A V W) := by
  have hadd := productNorm_add_le_max_of_bounded hV (W := W)
  let := productNormedAddCommGroup hV hW
  exact IsUltrametricDist.isUltrametricDist_of_isNonarchimedean_norm hadd

end IsTateCompletion

section NormedFieldCompletion

variable {L V W : Type*} [NontriviallyNormedField L] [SeminormedAddCommGroup V] [NormedSpace L V]
  [SeminormedAddCommGroup W] [NormedSpace L W]

/-- Over a nontrivially normed field `L`, `productNorm` is homogeneous under scalar
multiplication. -/
@[simp]
theorem productNorm_smul (a : L) (z : CompletedTensor L V W) :
    productNorm L V W (a • z) = ‖a‖ * productNorm L V W z := by
  refine (denseRange_toCompletion L V W).induction_on z
    (isClosed_eq ((continuous_productNorm L V W).comp (continuous_const_smul a))
      (continuous_const.mul (continuous_productNorm L V W))) fun u ↦ ?_
  rw [← map_smul, productNorm_coe, productNorm_coe, productSeminorm_smul]

/-- Bundled structure theorem for `productNorm` over a nontrivially normed field: nonnegativity,
definiteness, the ultrametric inequality, scalar homogeneity, and the norm-ball neighbourhood basis
of zero. -/
theorem productNorm_structure :
    (∀ z : CompletedTensor L V W, 0 ≤ productNorm L V W z) ∧
      (∀ z : CompletedTensor L V W, productNorm L V W z = 0 ↔ z = 0) ∧
      (∀ z₁ z₂ : CompletedTensor L V W,
        productNorm L V W (z₁ + z₂) ≤ max (productNorm L V W z₁) (productNorm L V W z₂)) ∧
      (∀ (a : L) (z : CompletedTensor L V W),
        productNorm L V W (a • z) = ‖a‖ * productNorm L V W z) ∧
      (𝓝 (0 : CompletedTensor L V W)).HasBasis (0 < ·)
        fun r ↦ {z | productNorm L V W z < r} :=
  ⟨productNorm_nonneg, fun _ ↦ productNorm_eq_zero_iff, productNorm_add_le_max,
    productNorm_smul, hasBasis_nhds_zero_productNorm⟩

end NormedFieldCompletion

section CompleteFieldCompletion

variable {L V W : Type*} [NontriviallyNormedField L] [CompleteSpace L]
  [NormedAddCommGroup V] [NormedSpace L V] [IsUltrametricDist V]
  [NormedAddCommGroup W] [NormedSpace L W] [IsUltrametricDist W]

variable (L V W) in
/-- **Injectivity of the canonical map into the completed tensor product** over a complete
nontrivially normed field (KL15, Lemma 2.2.9(a)): `V ⊗[L] W → V ⊗̂_L W` is injective. -/
theorem injective_tensorProduct_of_field : Function.Injective (toCompletion L V W) := by
  refine (injective_iff_map_eq_zero (toCompletion L V W)).mpr fun u hu ↦ ?_
  have hnorm : productSeminorm L V W u = 0 := by
    rw [← productNorm_coe, hu, productNorm_zero]
  exact productSeminorm_eq_zero_iff.mp hnorm

/-- **Cross-norm on elementary completed tensors** over a complete nontrivially normed field:
`productNorm L V W (tmul L V W v w) = ‖v‖ * ‖w‖`. -/
@[simp]
theorem productNorm_tmul (v : V) (w : W) :
    productNorm L V W (tmul L V W v w) = ‖v‖ * ‖w‖ := by
  rw [← toCompletion_tmul, productNorm_coe, productSeminorm_tmul]

/-- **Unit-vector distance formula** on `V ⊗̂_L W`: when `‖w‖ = 1`, tensoring on the right by `w`
is isometric, `productNorm L V W (tmul L V W v w - tmul L V W v' w) = ‖v - v'‖`. -/
theorem productNorm_unitVector (v v' : V) {w : W} (hw : ‖w‖ = 1) :
    productNorm L V W (tmul L V W v w - tmul L V W v' w) = ‖v - v'‖ := by
  have hsub : tmul L V W v w - tmul L V W v' w = tmul L V W (v - v') w := by
    rw [← LinearMap.sub_apply, map_sub]
  rw [hsub, productNorm_tmul, hw, mul_one]

end CompleteFieldCompletion

end CompletedTensor

end TauCeti.Huber.BanachModule
