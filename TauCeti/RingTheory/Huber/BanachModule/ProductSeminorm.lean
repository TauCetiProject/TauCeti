/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Group.Completion
public import TauCeti.Analysis.Normed.Operator.BoundedLinearMaps
public import TauCeti.Analysis.Normed.Ring.PseudoUniformizer
public import TauCeti.RingTheory.Huber.BanachModule.CompletedTensor
import Mathlib.Algebra.Order.Ring.IsNonarchimedean
import Mathlib.LinearAlgebra.TensorProduct.Finiteness

/-!
# The nonarchimedean product seminorm and the norm on completed tensor products

For seminormed `A`-modules `V` and `W` over a commutative semiring `A`, the *product seminorm*
`TauCeti.Huber.BanachModule.productSeminorm A V W` of `z : V ⊗[A] W` is the infimum, over all
finite presentations `z = ∑ i : Fin n, v i ⊗ₜ w i`, of `max_i ‖v i‖ * ‖w i‖`, with the empty
maximum equal to `0`. Unlike the archimedean projective seminorm (which sums `‖v i‖ * ‖w i‖`), the
maximum formula produces a nonarchimedean additive group seminorm unconditionally, and it is the
largest nonarchimedean group seminorm on `V ⊗[A] W` bounded on elementary tensors by `‖v‖ * ‖w‖`.
Consequently every `A`-bilinear map into an ultrametric seminormed module bounded by
`C * (‖v‖ * ‖w‖)` induces a linear map bounded by `C` times `productSeminorm`.

When `A` is a seminormed Tate commutative ring (`TauCeti.NormedRing.IsTate A`) and the actions of
`A` on `V` and `W` are bounded (`‖a • v‖ ≤ C_V * ‖a‖ * ‖v‖` and `‖a • w‖ ≤ C_W * ‖a‖ * ‖w‖`),
balancing each elementary tensor `v ⊗ₜ w = (ϖⁿ • v) ⊗ₜ (ϖ⁻ⁿ • w)` across integer powers of a
multiplicative pseudo-uniformiser `ϖ` identifies `TauCeti.Huber.banachTensorTopology A V W` and its
uniformity with those induced by `productSeminorm A V W`
(`TauCeti.Huber.banachTensorTopology_eq_productSeminorm`,
`TauCeti.Huber.hasBasis_banachTensorTopology`,
`TauCeti.Huber.banachTensorUniformSpace_eq_productSeminorm`).

Transferring the separated completion norm across `CompletedTensor.equivCompletion` equips the
completed tensor product `TauCeti.Huber.BanachModule.CompletedTensor A V W` with a complete
ultrametric `NormedAddCommGroup` structure whose forgetful additive group, uniformity, and topology
coincide definitionally with the topological ones (`CompletedTensor.normedAddCommGroupOfBound`, and
global instances when `[IsBoundedSMul A V] [IsBoundedSMul A W]`). Over a nontrivially normed field
`K`, bounded bilinear maps into an ultrametric Banach space correspond isometrically to bounded
linear maps out of `CompletedTensor K V W` (`CompletedTensor.liftIsometry`).

## Main definitions

* `TauCeti.Huber.BanachModule.productSeminorm A V W`: the nonarchimedean product seminorm on
  `V ⊗[A] W`.
* `TauCeti.Huber.BanachModule.CompletedTensor.normedAddCommGroupOfBound`: the completed product
  norm on `V ⊗̂_A W` for bounded scalar actions over a Tate ring, registered as a global instance
  when `[IsBoundedSMul A V] [IsBoundedSMul A W]`.
* `TauCeti.Huber.BanachModule.CompletedTensor.liftIsometry`: the isometric universal property of
  `V ⊗̂_K W` over a nontrivially normed field `K`.

## Main results

* `TauCeti.Huber.BanachModule.isNonarchimedean_productSeminorm` and
  `TauCeti.Huber.BanachModule.le_productSeminorm`: `productSeminorm` is the largest nonarchimedean
  group seminorm bounded on pure tensors by `‖v‖ * ‖w‖`.
* `TauCeti.Huber.BanachModule.apply_le_mul_productSeminorm` and
  `TauCeti.Huber.BanachModule.norm_lift_le_mul_productSeminorm`: estimates for additive and
  bilinear maps out of `V ⊗[A] W`.
* `TauCeti.Huber.BanachModule.productSeminorm_comm`,
  `TauCeti.Huber.BanachModule.productSeminorm_eq_norm_lid`, and
  `TauCeti.Huber.BanachModule.productSeminorm_eq_norm_rid`: symmetry and scalar-unit isometry.
* `TauCeti.Huber.hasBasis_banachTensorTopology`,
  `TauCeti.Huber.banachTensorTopology_eq_productSeminorm`, and
  `TauCeti.Huber.banachTensorUniformSpace_eq_productSeminorm`: topological and uniform comparison
  with the tensor topology.
* `TauCeti.Huber.BanachModule.CompletedTensor.norm_toCompletion`,
  `CompletedTensor.norm_tmul_le`, `CompletedTensor.norm_lift_le`, `CompletedTensor.norm_map_le`,
  and `CompletedTensor.norm_lid`: norm formulas and operator estimates on `V ⊗̂_A W`.

## References

* K. S. Kedlaya and R. Liu, *Relative p-adic Hodge theory: Foundations*, Astérisque 371 (2015),
  Definitions 2.1.10 and 2.2.7.
* S. Bosch, U. Güntzer, and R. Remmert, *Non-Archimedean Analysis*, Springer, 1984, §2.1.7.
-/

public section

open scoped NNReal TensorProduct Topology Uniformity
open Set Filter UniformSpace

namespace TauCeti.Huber.BanachModule

section ProductSeminorm

variable (A V W : Type*) [CommSemiring A] [SeminormedAddCommGroup V] [Module A V]
  [SeminormedAddCommGroup W] [Module A W]

/-- The finite-presentation maxima `sup_i ‖v i‖₊ * ‖w i‖₊` of decompositions
`z = ∑ i : Fin n, v i ⊗ₜ w i`; the empty presentation has maximum `0`. -/
private def maxCosts (z : V ⊗[A] W) : Set ℝ :=
  {c | ∃ (n : ℕ) (v : Fin n → V) (w : Fin n → W),
    ∑ i, v i ⊗ₜ[A] w i = z ∧ ↑(Finset.univ.sup fun i ↦ ‖v i‖₊ * ‖w i‖₊) = c}

variable {A V W}

private theorem maxCosts_nonempty (z : V ⊗[A] W) : (maxCosts A V W z).Nonempty := by
  obtain ⟨n, v, w, hz⟩ := TensorProduct.exists_sum_tmul_eq z
  exact ⟨_, n, v, w, hz.symm, rfl⟩

private theorem maxCosts_nonneg {z : V ⊗[A] W} {c : ℝ} (hc : c ∈ maxCosts A V W z) : 0 ≤ c := by
  rcases hc with ⟨_, _, _, -, rfl⟩
  exact NNReal.coe_nonneg _

private theorem maxCosts_bddBelow (z : V ⊗[A] W) : BddBelow (maxCosts A V W z) :=
  ⟨0, fun _ hc ↦ maxCosts_nonneg hc⟩

private theorem sInf_maxCosts_le {n : ℕ} (v : Fin n → V) (w : Fin n → W) :
    sInf (maxCosts A V W (∑ i, v i ⊗ₜ[A] w i)) ≤ ↑(Finset.univ.sup fun i ↦ ‖v i‖₊ * ‖w i‖₊) :=
  csInf_le (maxCosts_bddBelow _) ⟨n, v, w, rfl, rfl⟩

private theorem sInf_maxCosts_nonneg (z : V ⊗[A] W) : 0 ≤ sInf (maxCosts A V W z) :=
  le_csInf (maxCosts_nonempty z) fun _ hc ↦ maxCosts_nonneg hc

private theorem sInf_maxCosts_zero : sInf (maxCosts A V W 0) = 0 := by
  refine le_antisymm ?_ (sInf_maxCosts_nonneg 0)
  simpa using sInf_maxCosts_le (A := A) (Fin.elim0 : Fin 0 → V) (Fin.elim0 : Fin 0 → W)

private theorem sup_finAppend {α : Type*} [SemilatticeSup α] [OrderBot α] {n m : ℕ}
    (f : Fin n → α) (g : Fin m → α) :
    (Finset.univ.sup fun i : Fin (n + m) ↦ Fin.append f g i) =
      Finset.univ.sup f ⊔ Finset.univ.sup g := by
  apply le_antisymm
  · refine Finset.sup_le fun i _ ↦ ?_
    refine Fin.addCases (fun j ↦ ?_) (fun k ↦ ?_) i
    · simpa [Fin.append_left] using le_sup_of_le_left (Finset.le_sup (Finset.mem_univ j))
    · simpa [Fin.append_right] using le_sup_of_le_right (Finset.le_sup (Finset.mem_univ k))
  · refine sup_le (Finset.sup_le fun j _ ↦ ?_) (Finset.sup_le fun k _ ↦ ?_)
    · simpa [Fin.append_left] using
        Finset.le_sup (f := fun i ↦ Fin.append f g i) (Finset.mem_univ (Fin.castAdd m j))
    · simpa [Fin.append_right] using
        Finset.le_sup (f := fun i ↦ Fin.append f g i) (Finset.mem_univ (Fin.natAdd n k))

private theorem sInf_maxCosts_add_le_max (x y : V ⊗[A] W) :
    sInf (maxCosts A V W (x + y)) ≤ max (sInf (maxCosts A V W x)) (sInf (maxCosts A V W y)) := by
  refine le_of_forall_pos_le_add fun ε hε ↦ ?_
  have hε0 : 0 < ε := hε
  obtain ⟨_, ⟨n, v, w, rfl, rfl⟩, hx⟩ :=
    exists_lt_of_csInf_lt (maxCosts_nonempty x) (lt_add_of_pos_right _ hε0)
  obtain ⟨_, ⟨m, v', w', rfl, rfl⟩, hy⟩ :=
    exists_lt_of_csInf_lt (maxCosts_nonempty y) (lt_add_of_pos_right _ hε0)
  have hsum : ∑ i, Fin.append v v' i ⊗ₜ[A] Fin.append w w' i =
      (∑ i, v i ⊗ₜ[A] w i) + ∑ j, v' j ⊗ₜ[A] w' j := by
    simp [Fin.sum_univ_add]
  have hsup : (Finset.univ.sup fun i ↦ ‖Fin.append v v' i‖₊ * ‖Fin.append w w' i‖₊) =
      (Finset.univ.sup fun i ↦ ‖v i‖₊ * ‖w i‖₊) ⊔
        (Finset.univ.sup fun j ↦ ‖v' j‖₊ * ‖w' j‖₊) := by
    rw [← sup_finAppend]
    congr 1; ext i; exact Fin.addCases (fun _ ↦ by simp) (fun _ ↦ by simp) i
  rw [← hsum]
  refine (sInf_maxCosts_le (Fin.append v v') (Fin.append w w')).trans ?_
  rw [hsup, NNReal.coe_max]
  refine max_le (hx.le.trans ?_) (hy.le.trans ?_)
  · gcongr; exact le_max_left _ _
  · gcongr; exact le_max_right _ _

private theorem sInf_maxCosts_neg (z : V ⊗[A] W) :
    sInf (maxCosts A V W (-z)) = sInf (maxCosts A V W z) := by
  suffices ∀ u : V ⊗[A] W, sInf (maxCosts A V W (-u)) ≤ sInf (maxCosts A V W u) from
    le_antisymm (this z) (by simpa using this (-z))
  intro u
  refine le_csInf (maxCosts_nonempty u) ?_
  rintro _ ⟨n, v, w, rfl, rfl⟩
  have hneg : -∑ i, v i ⊗ₜ[A] w i = ∑ i, (-v i) ⊗ₜ[A] w i := by
    rw [← Finset.sum_neg_distrib]
    simp_rw [TensorProduct.neg_tmul]
  rw [hneg]
  simpa using sInf_maxCosts_le (fun i ↦ -v i) w

private theorem le_mul_csInf {S : Set ℝ} (hS : S.Nonempty) (hS0 : ∀ x ∈ S, 0 ≤ x) {a C : ℝ}
    (ha : 0 ≤ a) (h : ∀ x ∈ S, a ≤ C * x) : a ≤ C * sInf S := by
  rcases lt_trichotomy C 0 with hC | rfl | hC
  · obtain ⟨x₀, hx₀⟩ := hS
    have hCx₀ : C * x₀ ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hC.le (hS0 x₀ hx₀)
    have hx₀_zero : x₀ = 0 :=
      (mul_eq_zero.mp (le_antisymm hCx₀ (ha.trans (h x₀ hx₀)))).resolve_left hC.ne
    have hsInf : sInf S = 0 :=
      le_antisymm (csInf_le ⟨0, hS0⟩ (hx₀_zero ▸ hx₀)) (le_csInf ⟨x₀, hx₀⟩ hS0)
    exact (h x₀ hx₀).trans (by simp [hx₀_zero, hsInf])
  · obtain ⟨x₀, hx₀⟩ := hS
    simpa using h x₀ hx₀
  · rw [← div_le_iff₀' hC]
    exact le_csInf hS fun x hx ↦ (div_le_iff₀' hC).mpr (h x hx)

variable (A V W) in
/-- **The nonarchimedean product seminorm** on `V ⊗[A] W`: the infimum, over all finite
decompositions `z = ∑ i : Fin n, v i ⊗ₜ w i`, of `max_i ‖v i‖ * ‖w i‖`, with empty maximum `0`. -/
noncomputable def productSeminorm : AddGroupSeminorm (V ⊗[A] W) where
  toFun z := sInf (maxCosts A V W z)
  map_zero' := sInf_maxCosts_zero
  add_le' x y := (sInf_maxCosts_add_le_max x y).trans <|
    max_le_add_of_nonneg (sInf_maxCosts_nonneg x) (sInf_maxCosts_nonneg y)
  neg' := sInf_maxCosts_neg

private theorem productSeminorm_apply (z : V ⊗[A] W) :
    productSeminorm A V W z = sInf (maxCosts A V W z) :=
  (rfl)

/-- The product seminorm satisfies the strong triangle inequality. -/
theorem productSeminorm_add_le_max (x y : V ⊗[A] W) :
    productSeminorm A V W (x + y) ≤ max (productSeminorm A V W x) (productSeminorm A V W y) :=
  sInf_maxCosts_add_le_max x y

variable (A V W) in
/-- The product seminorm on `V ⊗[A] W` is nonarchimedean. -/
theorem isNonarchimedean_productSeminorm : IsNonarchimedean (productSeminorm A V W) :=
  productSeminorm_add_le_max

/-- The product seminorm of a finite sum of elementary tensors is at most the maximum of the
products of the norms of its terms. -/
theorem productSeminorm_sum_tmul_le {ι : Type*} (s : Finset ι) (v : ι → V) (w : ι → W) :
    productSeminorm A V W (∑ i ∈ s, v i ⊗ₜ[A] w i) ≤ ↑(s.sup fun i ↦ ‖v i‖₊ * ‖w i‖₊) := by
  let e := s.equivFin
  rw [productSeminorm_apply]
  have key := sInf_maxCosts_le (A := A) (fun j ↦ v (e.symm j)) (fun j ↦ w (e.symm j))
  have hsum : (∑ j : Fin s.card, v (e.symm j) ⊗ₜ[A] w (e.symm j)) = ∑ i ∈ s, v i ⊗ₜ[A] w i := by
    rw [← Finset.sum_coe_sort s, ← e.symm.sum_comp]
  have hsup : (Finset.univ.sup fun j : Fin s.card ↦ ‖v (e.symm j)‖₊ * ‖w (e.symm j)‖₊) =
      s.sup fun i ↦ ‖v i‖₊ * ‖w i‖₊ := by
    apply le_antisymm
    · refine Finset.sup_le fun j _ ↦ ?_
      exact Finset.le_sup (f := fun i ↦ ‖v i‖₊ * ‖w i‖₊) (e.symm j).2
    · refine Finset.sup_le fun i hi ↦ ?_
      simpa using Finset.le_sup
        (f := fun j : Fin s.card ↦ ‖v (e.symm j)‖₊ * ‖w (e.symm j)‖₊)
        (Finset.mem_univ (e ⟨i, hi⟩))
  rwa [hsum, hsup] at key

/-- If each term of `∑ i ∈ s, v i ⊗ₜ w i` has `‖v i‖ * ‖w i‖ ≤ b` with `0 ≤ b`, then so does the
product seminorm of the sum. -/
theorem productSeminorm_sum_tmul_le_of_le {ι : Type*} (s : Finset ι) (v : ι → V) (w : ι → W)
    {b : ℝ} (hb : 0 ≤ b) (h : ∀ i ∈ s, ‖v i‖ * ‖w i‖ ≤ b) :
    productSeminorm A V W (∑ i ∈ s, v i ⊗ₜ[A] w i) ≤ b := by
  refine (productSeminorm_sum_tmul_le s v w).trans ?_
  lift b to ℝ≥0 using hb
  exact NNReal.coe_le_coe.mpr <| Finset.sup_le fun i hi ↦ by exact_mod_cast h i hi

/-- Every strict upper bound on `productSeminorm A V W z` is witnessed by a finite presentation
`z = ∑ i : Fin n, v i ⊗ₜ w i`. -/
theorem exists_sum_tmul_eq_of_productSeminorm_lt {z : V ⊗[A] W} {c : ℝ}
    (h : productSeminorm A V W z < c) :
    ∃ (n : ℕ) (v : Fin n → V) (w : Fin n → W),
      ∑ i, v i ⊗ₜ[A] w i = z ∧ ↑(Finset.univ.sup fun i ↦ ‖v i‖₊ * ‖w i‖₊) < c := by
  obtain ⟨_, ⟨n, v, w, hz, rfl⟩, hc⟩ := exists_lt_of_csInf_lt (maxCosts_nonempty z) <| by
    rwa [← productSeminorm_apply]
  exact ⟨n, v, w, hz, hc⟩

/-- The product seminorm equals the infimum of all nonnegative uniform term bounds `c` over finite
presentations `z = ∑ i : Fin n, v i ⊗ₜ w i`. -/
theorem productSeminorm_eq_sInf_bounds (z : V ⊗[A] W) :
    productSeminorm A V W z = sInf {c : ℝ | 0 ≤ c ∧
      ∃ (n : ℕ) (v : Fin n → V) (w : Fin n → W),
        ∑ i, v i ⊗ₜ[A] w i = z ∧ ∀ i, ‖v i‖ * ‖w i‖ ≤ c} := by
  let B : Set ℝ := {c : ℝ | 0 ≤ c ∧ ∃ (n : ℕ) (v : Fin n → V) (w : Fin n → W),
    ∑ i, v i ⊗ₜ[A] w i = z ∧ ∀ i, ‖v i‖ * ‖w i‖ ≤ c}
  have hsub : maxCosts A V W z ⊆ B := by
    rintro _ ⟨n, v, w, rfl, rfl⟩
    refine ⟨NNReal.coe_nonneg _, n, v, w, rfl, fun i ↦ ?_⟩
    exact_mod_cast Finset.le_sup (f := fun j ↦ ‖v j‖₊ * ‖w j‖₊) (Finset.mem_univ i)
  refine le_antisymm (le_csInf ((maxCosts_nonempty z).mono hsub) ?_)
    (csInf_le_csInf ⟨0, fun _ hc ↦ hc.1⟩ (maxCosts_nonempty z) hsub)
  rintro c ⟨hc0, n, v, w, rfl, hvw⟩
  exact productSeminorm_sum_tmul_le_of_le Finset.univ v w hc0 fun i _ ↦ hvw i

/-- The product seminorm of an elementary tensor is at most the product of the norms. -/
theorem productSeminorm_tmul_le (v : V) (w : W) :
    productSeminorm A V W (v ⊗ₜ[A] w) ≤ ‖v‖ * ‖w‖ := by
  simpa using productSeminorm_sum_tmul_le {()} (fun _ ↦ v) (fun _ ↦ w)

/-- **Universal bound for nonarchimedean group seminorms.** If `p` is a nonarchimedean additive
group seminorm on `M` and `f : V ⊗[A] W → M` is an additive homomorphism satisfying
`p (f (v ⊗ₜ w)) ≤ C * (‖v‖ * ‖w‖)` on elementary tensors, then
`p (f z) ≤ C * productSeminorm A V W z` for every `z`. -/
theorem apply_le_mul_productSeminorm {F M : Type*} [AddCommGroup M] [FunLike F (V ⊗[A] W) M]
    [AddMonoidHomClass F (V ⊗[A] W) M] {p : AddGroupSeminorm M} (hp : IsNonarchimedean p) {f : F}
    {C : ℝ} (h : ∀ v w, p (f (v ⊗ₜ[A] w)) ≤ C * (‖v‖ * ‖w‖)) (z : V ⊗[A] W) :
    p (f z) ≤ C * productSeminorm A V W z := by
  rw [productSeminorm_apply]
  refine le_mul_csInf (maxCosts_nonempty z) (fun _ ↦ maxCosts_nonneg) (apply_nonneg p _) ?_
  rintro _ ⟨n, v, w, rfl, rfl⟩
  rw [map_sum]
  rcases (Finset.univ : Finset (Fin n)).eq_empty_or_nonempty with hempty | hne
  · simp [hempty]
  obtain ⟨i, -, hi⟩ := hp.finset_image_add_of_nonempty (fun j : Fin n ↦ f (v j ⊗ₜ[A] w j)) hne
  refine hi.trans ((h (v i) (w i)).trans ?_)
  rcases le_or_gt 0 C with hC | hC
  · refine mul_le_mul_of_nonneg_left ?_ hC
    exact_mod_cast Finset.le_sup (f := fun j ↦ ‖v j‖₊ * ‖w j‖₊) (Finset.mem_univ i)
  · have hzero : ∀ j : Fin n, ‖v j‖ * ‖w j‖ = 0 := fun j ↦ by
      have hj0 : 0 ≤ ‖v j‖ * ‖w j‖ := by positivity
      have hj : C * (‖v j‖ * ‖w j‖) = 0 := le_antisymm
        (mul_nonpos_of_nonpos_of_nonneg hC.le hj0) ((apply_nonneg p _).trans (h (v j) (w j)))
      exact (mul_eq_zero.mp hj).resolve_left hC.ne
    have hzero_nn : ∀ j : Fin n, ‖v j‖₊ * ‖w j‖₊ = 0 := fun j ↦
      NNReal.coe_injective (by simpa using hzero j)
    have hsup0 : (Finset.univ.sup fun j ↦ ‖v j‖₊ * ‖w j‖₊) = 0 :=
      nonpos_iff_eq_zero.mp (Finset.sup_le fun j _ ↦ (hzero_nn j).le)
    simp [hzero, hsup0]

/-- `productSeminorm A V W` is the largest nonarchimedean additive group seminorm on `V ⊗[A] W`
bounded on elementary tensors by `‖v‖ * ‖w‖`. -/
theorem le_productSeminorm {p : AddGroupSeminorm (V ⊗[A] W)} (hp : IsNonarchimedean p)
    (h : ∀ v w, p (v ⊗ₜ[A] w) ≤ ‖v‖ * ‖w‖) : p ≤ productSeminorm A V W := fun z ↦ by
  simpa using apply_le_mul_productSeminorm (f := AddMonoidHom.id (V ⊗[A] W)) (C := 1) hp
    (fun v w ↦ by simpa using h v w) z

/-- An `A`-bilinear map into an ultrametric seminormed `A`-module bounded by `C * (‖v‖ * ‖w‖)`
lifts to a linear map bounded by `C * productSeminorm A V W z`. -/
theorem norm_lift_le_mul_productSeminorm {M : Type*} [SeminormedAddCommGroup M]
    [IsUltrametricDist M] [Module A M] (β : V →ₗ[A] W →ₗ[A] M) {C : ℝ}
    (hβ : ∀ v w, ‖β v w‖ ≤ C * (‖v‖ * ‖w‖)) (z : V ⊗[A] W) :
    ‖TensorProduct.lift β z‖ ≤ C * productSeminorm A V W z :=
  apply_le_mul_productSeminorm (p := normAddGroupSeminorm M)
    IsUltrametricDist.isNonarchimedean_norm (f := TensorProduct.lift β)
    (fun v w ↦ by simpa using hβ v w) z

/-- Scalar multiplication by `s` on the left factor with `‖s • v‖ ≤ C * ‖v‖` scales
`productSeminorm A V W` by at most `C`. -/
theorem productSeminorm_smul_le_of_le {S : Type*} [Monoid S] [DistribMulAction S V]
    [SMulCommClass A S V] {s : S} {C : ℝ} (hs : ∀ v : V, ‖s • v‖ ≤ C * ‖v‖) (z : V ⊗[A] W) :
    productSeminorm A V W (s • z) ≤ C * productSeminorm A V W z := by
  let φ : V ⊗[A] W →+ V ⊗[A] W := ⟨⟨fun u ↦ s • u, smul_zero s⟩, smul_add s⟩
  exact apply_le_mul_productSeminorm (isNonarchimedean_productSeminorm A V W) (f := φ)
    (fun v w ↦ (productSeminorm_tmul_le (s • v) w).trans <| by
      simpa [mul_assoc] using mul_le_mul_of_nonneg_right (hs v) (norm_nonneg w)) z

/-- Under a contractive left action of a seminormed ring `S` commuting with `A`,
`productSeminorm A V W (s • z) ≤ ‖s‖ * productSeminorm A V W z`. -/
theorem productSeminorm_smul_le {S : Type*} [SeminormedRing S] [Module S V] [SMulCommClass A S V]
    [IsBoundedSMul S V] (s : S) (z : V ⊗[A] W) :
    productSeminorm A V W (s • z) ≤ ‖s‖ * productSeminorm A V W z :=
  productSeminorm_smul_le_of_le (norm_smul_le s) z

/-- `TensorProduct.map f g` scales `productSeminorm` by at most `C₁ * C₂` when `‖f v‖ ≤ C₁ * ‖v‖`
and `‖g w‖ ≤ C₂ * ‖w‖`. -/
theorem productSeminorm_map_le {V' W' : Type*} [SeminormedAddCommGroup V'] [Module A V']
    [SeminormedAddCommGroup W'] [Module A W'] (f : V →ₗ[A] V') (g : W →ₗ[A] W') {C₁ C₂ : ℝ}
    (hf : ∀ v, ‖f v‖ ≤ C₁ * ‖v‖) (hg : ∀ w, ‖g w‖ ≤ C₂ * ‖w‖) (z : V ⊗[A] W) :
    productSeminorm A V' W' (TensorProduct.map f g z) ≤ C₁ * C₂ * productSeminorm A V W z := by
  refine apply_le_mul_productSeminorm (isNonarchimedean_productSeminorm A V' W')
    (f := TensorProduct.map f g) (fun v w ↦ ?_) z
  have h1 : 0 ≤ C₁ * ‖v‖ := (norm_nonneg (f v)).trans (hf v)
  calc productSeminorm A V' W' (TensorProduct.map f g (v ⊗ₜ[A] w))
      ≤ ‖f v‖ * ‖g w‖ := by simpa using productSeminorm_tmul_le (A := A) (f v) (g w)
    _ ≤ (C₁ * ‖v‖) * (C₂ * ‖w‖) := mul_le_mul (hf v) (hg w) (norm_nonneg _) h1
    _ = C₁ * C₂ * (‖v‖ * ‖w‖) := by ring

private theorem productSeminorm_comm_le (z : V ⊗[A] W) :
    productSeminorm A W V (TensorProduct.comm A V W z) ≤ productSeminorm A V W z := by
  simpa using apply_le_mul_productSeminorm (isNonarchimedean_productSeminorm A W V)
    (f := TensorProduct.comm A V W) (C := 1)
    (fun v w ↦ by simpa [mul_comm ‖v‖] using productSeminorm_tmul_le (A := A) w v) z

/-- Swapping the tensor factors preserves `productSeminorm`. -/
@[simp]
theorem productSeminorm_comm (z : V ⊗[A] W) :
    productSeminorm A W V (TensorProduct.comm A V W z) = productSeminorm A V W z :=
  (productSeminorm_comm_le z).antisymm <| by
    simpa using productSeminorm_comm_le (TensorProduct.comm A V W z)

end ProductSeminorm

section ScalarUnit

variable {A : Type*} [SeminormedCommRing A] {V : Type*} [SeminormedAddCommGroup V]
  [IsUltrametricDist V] [Module A V] [IsBoundedSMul A V]

/-- Under a contractive action on an ultrametric seminormed module `V`, the unit map
`A ⊗[A] V → V` is contractive for `productSeminorm`. -/
theorem norm_lid_le_productSeminorm (z : A ⊗[A] V) :
    ‖TensorProduct.lid A V z‖ ≤ productSeminorm A A V z := by
  simpa using apply_le_mul_productSeminorm (p := normAddGroupSeminorm V)
    IsUltrametricDist.isNonarchimedean_norm (f := TensorProduct.lid A V) (C := 1)
    (fun a v ↦ by simpa using norm_smul_le a v) z

/-- When `‖(1 : A)‖ ≤ 1`, `productSeminorm A A V` on `A ⊗[A] V` equals the norm of the image under
`TensorProduct.lid A V` (including for the zero ring). -/
theorem productSeminorm_eq_norm_lid_of_norm_one_le (h1 : ‖(1 : A)‖ ≤ 1) (z : A ⊗[A] V) :
    productSeminorm A A V z = ‖TensorProduct.lid A V z‖ := by
  refine le_antisymm ?_ (norm_lid_le_productSeminorm z)
  calc productSeminorm A A V z
      = productSeminorm A A V ((1 : A) ⊗ₜ[A] TensorProduct.lid A V z) := by
        rw [← TensorProduct.lid_symm_apply, LinearEquiv.symm_apply_apply]
    _ ≤ ‖(1 : A)‖ * ‖TensorProduct.lid A V z‖ := productSeminorm_tmul_le _ _
    _ ≤ 1 * ‖TensorProduct.lid A V z‖ := mul_le_mul_of_nonneg_right h1 (norm_nonneg _)
    _ = ‖TensorProduct.lid A V z‖ := one_mul _

/-- On `A ⊗[A] V` with `[NormOneClass A]`, `productSeminorm` is the norm of `TensorProduct.lid`. -/
@[simp]
theorem productSeminorm_eq_norm_lid [NormOneClass A] (z : A ⊗[A] V) :
    productSeminorm A A V z = ‖TensorProduct.lid A V z‖ :=
  productSeminorm_eq_norm_lid_of_norm_one_le norm_one.le z

/-- When `‖(1 : A)‖ ≤ 1`, `productSeminorm A V A` on `V ⊗[A] A` equals the norm of the image under
`TensorProduct.rid A V`. -/
theorem productSeminorm_eq_norm_rid_of_norm_one_le (h1 : ‖(1 : A)‖ ≤ 1) (z : V ⊗[A] A) :
    productSeminorm A V A z = ‖TensorProduct.rid A V z‖ := by
  rw [← productSeminorm_comm, productSeminorm_eq_norm_lid_of_norm_one_le h1, TensorProduct.lid_comm]

/-- On `V ⊗[A] A` with `[NormOneClass A]`, `productSeminorm` is the norm of `TensorProduct.rid`. -/
@[simp]
theorem productSeminorm_eq_norm_rid [NormOneClass A] (z : V ⊗[A] A) :
    productSeminorm A V A z = ‖TensorProduct.rid A V z‖ :=
  productSeminorm_eq_norm_rid_of_norm_one_le norm_one.le z

end ScalarUnit

end TauCeti.Huber.BanachModule

namespace TauCeti.Huber

section TensorTopology

variable {A V W : Type*} [SeminormedCommRing A] [SeminormedAddCommGroup V] [Module A V]
  [SeminormedAddCommGroup W] [Module A W]

/-- When the scalar action of `A` on `V` is bounded, `banachTensorTopology A V W` is finer than
the topology induced by `BanachModule.productSeminorm A V W`. -/
theorem banachTensorTopology_le_productSeminorm
    (hV : ∃ C : ℝ≥0, ∀ (a : A) (v : V), ‖a • v‖ ≤ C * ‖a‖ * ‖v‖) :
    banachTensorTopology A V W ≤
      @UniformSpace.toTopologicalSpace _
        (BanachModule.productSeminorm A V W).toSeminormedAddCommGroup.toUniformSpace := by
  let : SeminormedAddCommGroup (V ⊗[A] W) :=
    (BanachModule.productSeminorm A V W).toSeminormedAddCommGroup
  let : IsUltrametricDist (V ⊗[A] W) :=
    IsUltrametricDist.isUltrametricDist_of_isNonarchimedean_norm
      (BanachModule.isNonarchimedean_productSeminorm A V W)
  obtain ⟨C, hC⟩ := hV
  have hsmul : ContinuousSMul A (V ⊗[A] W) :=
    TauCeti.continuousSMul_of_norm_smul_le ⟨C, fun a z ↦ by
      change BanachModule.productSeminorm A V W (a • z) ≤
        C * ‖a‖ * BanachModule.productSeminorm A V W z
      exact BanachModule.productSeminorm_smul_le_of_le (hC a) z⟩
  have htmul : Continuous fun p : V × W ↦ p.1 ⊗ₜ[A] p.2 :=
    (TensorProduct.mk A V W).continuous₂_of_bound 1 fun v w ↦ by
      change BanachModule.productSeminorm A V W (v ⊗ₜ[A] w) ≤ 1 * ‖v‖ * ‖w‖
      simpa using BanachModule.productSeminorm_tmul_le (A := A) v w
  exact banachTensorTopology_le IsUltrametricDist.nonarchimedeanAddGroup hsmul htmul

private theorem hasBasis_productSeminorm :
    (@nhds (V ⊗[A] W)
      (@UniformSpace.toTopologicalSpace _
        (BanachModule.productSeminorm A V W).toSeminormedAddCommGroup.toUniformSpace) 0).HasBasis
      (0 < ·) fun r ↦ {z | BanachModule.productSeminorm A V W z < r} := by
  let S : SeminormedAddCommGroup (V ⊗[A] W) :=
    (BanachModule.productSeminorm A V W).toSeminormedAddCommGroup
  refine (@Metric.nhds_basis_ball (V ⊗[A] W) S.toPseudoMetricSpace 0).congr
    (fun _ ↦ Iff.rfl) fun r _ ↦ ?_
  ext z
  change BanachModule.productSeminorm A V W (-z + 0) < r ↔
    BanachModule.productSeminorm A V W z < r
  simp

/-- Balancing lemma: using integer powers of a multiplicative pseudo-uniformiser `ϖ`, an elementary
tensor `v ⊗ₜ w` with `‖v‖ * ‖w‖ < ‖ϖ‖ * ε ^ 2 / (M_V * M_W)` can be rewritten as
`(u • v) ⊗ₜ (u' • w)` with `‖u • v‖ < ε` and `‖u' • w‖ < ε`. -/
private theorem exists_balanced_tmul (ϖ : NormedRing.PseudoUniformizer A) {M_V M_W ε : ℝ}
    (hMV : 0 < M_V) (hMW : 0 < M_W) (hε : 0 < ε)
    (hv_smul : ∀ (a : A) (v : V), ‖a • v‖ ≤ M_V * ‖a‖ * ‖v‖)
    (hw_smul : ∀ (a : A) (w : W), ‖a • w‖ ≤ M_W * ‖a‖ * ‖w‖) {v : V} {w : W}
    (hvw : ‖v‖ * ‖w‖ < ‖(ϖ.unit : A)‖ * ε ^ 2 / (M_V * M_W)) :
    ∃ (v' : V) (w' : W), v' ⊗ₜ[A] w' = v ⊗ₜ[A] w ∧ ‖v'‖ < ε ∧ ‖w'‖ < ε := by
  set q : ℝ := ‖(ϖ.unit : A)‖
  have hq0 : 0 < q := ϖ.norm_pos
  have hq1 : q < 1 := ϖ.norm_lt_one
  have hzpow (m : ℤ) : ‖((ϖ.unit ^ m : Aˣ) : A)‖ = q ^ m :=
    NormedRing.norm_units_zpow_of_norm_mul ϖ.norm_pos ϖ.norm_mul m
  have hcancel (m : ℤ) :
      (((ϖ.unit ^ m : Aˣ) : A) • v) ⊗ₜ[A] (((ϖ.unit ^ (-m) : Aˣ) : A) • w) = v ⊗ₜ[A] w := by
    rw [TensorProduct.smul_tmul_smul, ← Units.val_mul, ← zpow_add, add_neg_cancel, zpow_zero,
      Units.val_one, one_smul]
  rcases (norm_nonneg w).eq_or_lt with hw0 | hw_pos
  · have hpos : 0 < ‖v‖ + 1 := by positivity
    obtain ⟨m, hm⟩ := exists_pow_lt_of_lt_one (div_pos hε (mul_pos hMV hpos)) hq1
    refine ⟨((ϖ.unit ^ (m : ℤ) : Aˣ) : A) • v, ((ϖ.unit ^ (-(m : ℤ)) : Aˣ) : A) • w,
      hcancel m, (hv_smul _ _).trans_lt ?_, ?_⟩
    · rw [hzpow, zpow_natCast]
      have hm' := (lt_div_iff₀ (mul_pos hMV hpos)).mp hm
      nlinarith [norm_nonneg v, pow_nonneg hq0.le m]
    · exact (hw_smul _ _).trans_lt (by rw [← hw0, mul_zero]; exact hε)
  · obtain ⟨n, ⟨hn_gt, hn_le⟩, -⟩ :=
      TauCeti.existsUnique_zpow_mul_mem_Ioc hq0 hq1 (by positivity : 0 < q * ε / (M_W * ‖w‖))
    refine ⟨((ϖ.unit ^ n : Aˣ) : A) • v, ((ϖ.unit ^ (-n) : Aˣ) : A) • w, hcancel n, ?_, ?_⟩
    · have hle : q ^ n * (q * ε) ≤ M_W * ‖w‖ := by
        rwa [mul_div_assoc', div_le_one (mul_pos hMW hw_pos)] at hn_le
      have hvw' : M_V * M_W * (‖v‖ * ‖w‖) < q * ε ^ 2 := by
        have := (lt_div_iff₀ (mul_pos hMV hMW)).mp hvw; linarith
      refine (hv_smul _ _).trans_lt (hzpow n ▸ lt_of_mul_lt_mul_right ?_ (mul_pos hq0 hε).le)
      calc M_V * q ^ n * ‖v‖ * (q * ε)
          = M_V * ‖v‖ * (q ^ n * (q * ε)) := by ring
        _ ≤ M_V * ‖v‖ * (M_W * ‖w‖) := by gcongr
        _ = M_V * M_W * (‖v‖ * ‖w‖) := by ring
        _ < ε * (q * ε) := by linarith
    · have hgt : q * (M_W * ‖w‖) < q ^ n * (q * ε) := by
        rwa [mul_div_assoc', lt_div_iff₀ (mul_pos hMW hw_pos)] at hn_gt
      have hqn : q ^ (-n) * q ^ n = 1 := zpow_neg q n ▸ inv_mul_cancel₀ (zpow_ne_zero n hq0.ne')
      refine (hw_smul _ _).trans_lt
        (hzpow (-n) ▸ lt_of_mul_lt_mul_right ?_ (mul_pos (zpow_pos hq0 n) hq0).le)
      calc M_W * q ^ (-n) * ‖w‖ * (q ^ n * q)
          = q * (M_W * ‖w‖) * (q ^ (-n) * q ^ n) := by ring
        _ = q * (M_W * ‖w‖) := by rw [hqn, mul_one]
        _ < ε * (q ^ n * q) := by linarith

section IsTate

variable [NormedRing.IsTate A]

/-- **Neighbourhood basis of `0` for `banachTensorTopology`.** Over a seminormed Tate commutative
ring `A` with bounded scalar actions on `V` and `W`, the open balls
`{z | productSeminorm A V W z < r}` (`r > 0`) form a neighbourhood basis of `0` for
`banachTensorTopology A V W`. -/
theorem hasBasis_banachTensorTopology
    (hV : ∃ C : ℝ≥0, ∀ (a : A) (v : V), ‖a • v‖ ≤ C * ‖a‖ * ‖v‖)
    (hW : ∃ C : ℝ≥0, ∀ (a : A) (w : W), ‖a • w‖ ≤ C * ‖a‖ * ‖w‖) :
    (@nhds (V ⊗[A] W) (banachTensorTopology A V W) 0).HasBasis (0 < ·)
      fun r ↦ {z | BanachModule.productSeminorm A V W z < r} := by
  let S := (BanachModule.productSeminorm A V W).toSeminormedAddCommGroup
  suffices hnhds : @nhds (V ⊗[A] W) (banachTensorTopology A V W) 0 =
      @nhds (V ⊗[A] W) S.toUniformSpace.toTopologicalSpace 0 from
    hnhds ▸ hasBasis_productSeminorm
  refine le_antisymm (nhds_mono (banachTensorTopology_le_productSeminorm hV)) ?_
  intro U hU
  let : TopologicalSpace (V ⊗[A] W) := banachTensorTopology A V W
  have : NonarchimedeanAddGroup (V ⊗[A] W) := nonarchimedeanAddGroup_banachTensorTopology A V W
  obtain ⟨H, hHU⟩ := NonarchimedeanAddGroup.is_nonarchimedean U hU
  have hcont : Continuous fun p : V × W ↦ p.1 ⊗ₜ[A] p.2 :=
    continuous_tmul_banachTensorTopology A V W
  have h0 : (0 : V × W).1 ⊗ₜ[A] (0 : V × W).2 ∈ (H : Set (V ⊗[A] W)) := by simp
  have hpre : (fun p : V × W ↦ p.1 ⊗ₜ[A] p.2) ⁻¹' (H : Set (V ⊗[A] W)) ∈ 𝓝 ((0, 0) : V × W) :=
    hcont.continuousAt.preimage_mem_nhds (H.isOpen.mem_nhds h0)
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hpre
  obtain ⟨ϖ⟩ := NormedRing.IsTate.nonempty_pseudoUniformizer (R := A)
  obtain ⟨CV, hCV⟩ := hV
  obtain ⟨CW, hCW⟩ := hW
  set MV : ℝ := (CV : ℝ) + 1
  set MW : ℝ := (CW : ℝ) + 1
  have hMV : 0 < MV := by positivity
  have hMW : 0 < MW := by positivity
  have hv_smul (a : A) (v : V) : ‖a • v‖ ≤ MV * ‖a‖ * ‖v‖ :=
    (hCV a v).trans (by gcongr; linarith)
  have hw_smul (a : A) (w : W) : ‖a • w‖ ≤ MW * ‖a‖ * ‖w‖ :=
    (hCW a w).trans (by gcongr; linarith)
  set δ : ℝ := ‖(ϖ.unit : A)‖ * ε ^ 2 / (MV * MW)
  have hδ : 0 < δ := by have := ϖ.norm_pos; positivity
  refine hasBasis_productSeminorm.mem_iff.mpr ⟨δ, hδ, ?_⟩
  intro z hz
  obtain ⟨n, v, w, rfl, hsup⟩ := BanachModule.exists_sum_tmul_eq_of_productSeminorm_lt hz
  refine hHU (H.toAddSubgroup.sum_mem fun i _ ↦ ?_)
  have hvw : ‖v i‖ * ‖w i‖ < δ := lt_of_le_of_lt
    (by exact_mod_cast Finset.le_sup (f := fun j ↦ ‖v j‖₊ * ‖w j‖₊) (Finset.mem_univ i)) hsup
  obtain ⟨v', w', heq, hv', hw'⟩ :=
    exists_balanced_tmul ϖ hMV hMW hε hv_smul hw_smul hvw
  rw [← heq]
  have hmem : ((v', w') : V × W) ∈ Metric.ball (0, 0) ε := by
    simp [Metric.mem_ball, Prod.dist_eq, hv', hw']
  exact hball hmem

/-- Over a seminormed Tate commutative ring `A` with bounded scalar actions on `V` and `W`,
`banachTensorUniformSpace A V W` coincides with the uniformity induced by
`BanachModule.productSeminorm A V W`. -/
theorem banachTensorUniformSpace_eq_productSeminorm
    (hV : ∃ C : ℝ≥0, ∀ (a : A) (v : V), ‖a • v‖ ≤ C * ‖a‖ * ‖v‖)
    (hW : ∃ C : ℝ≥0, ∀ (a : A) (w : W), ‖a • w‖ ≤ C * ‖a‖ * ‖w‖) :
    banachTensorUniformSpace A V W =
      (BanachModule.productSeminorm A V W).toSeminormedAddCommGroup.toUniformSpace := by
  let S : SeminormedAddCommGroup (V ⊗[A] W) :=
    (BanachModule.productSeminorm A V W).toSeminormedAddCommGroup
  refine IsUniformAddGroup.ext (isUniformAddGroup_banachTensorUniformSpace A V W)
    inferInstance ?_
  rw [banachTensorUniformSpace_toTopologicalSpace]
  exact (hasBasis_banachTensorTopology hV hW).eq_of_same_basis hasBasis_productSeminorm

/-- Over a seminormed Tate commutative ring `A` with bounded scalar actions on `V` and `W`,
`banachTensorTopology A V W` coincides with the topology induced by
`BanachModule.productSeminorm A V W`. -/
theorem banachTensorTopology_eq_productSeminorm
    (hV : ∃ C : ℝ≥0, ∀ (a : A) (v : V), ‖a • v‖ ≤ C * ‖a‖ * ‖v‖)
    (hW : ∃ C : ℝ≥0, ∀ (a : A) (w : W), ‖a • w‖ ≤ C * ‖a‖ * ‖w‖) :
    banachTensorTopology A V W =
      @UniformSpace.toTopologicalSpace _
        (BanachModule.productSeminorm A V W).toSeminormedAddCommGroup.toUniformSpace := by
  rw [← banachTensorUniformSpace_toTopologicalSpace,
    banachTensorUniformSpace_eq_productSeminorm hV hW]

end IsTate

end TensorTopology

namespace BanachModule.CompletedTensor

section BoundedSMul

variable {A V W : Type*} [SeminormedCommRing A] [NormedRing.IsTate A]
  [SeminormedAddCommGroup V] [Module A V] [SeminormedAddCommGroup W] [Module A W]

/-- **The completed product norm on `CompletedTensor A V W`** for bounded scalar actions over a
seminormed Tate commutative ring `A`. Its underlying `AddCommGroup`, `UniformSpace`, and
`TopologicalSpace` coincide definitionally with the existing instances on `CompletedTensor A V W`,
and its norm depends only on `productSeminorm A V W` (not on the chosen bounds `hV`, `hW`). -/
@[expose, instance_reducible]
noncomputable def normedAddCommGroupOfBound
    (hV : ∃ C : ℝ≥0, ∀ (a : A) (v : V), ‖a • v‖ ≤ C * ‖a‖ * ‖v‖)
    (hW : ∃ C : ℝ≥0, ∀ (a : A) (w : W), ‖a • w‖ ≤ C * ‖a‖ * ‖w‖) :
    NormedAddCommGroup (CompletedTensor A V W) :=
  let S0 := (productSeminorm A V W).toSeminormedAddCommGroup
  letI : SeminormedAddCommGroup (V ⊗[A] W) :=
    { S0 with
      toPseudoMetricSpace := @PseudoMetricSpace.replaceUniformity (V ⊗[A] W)
        (banachTensorUniformSpace A V W) S0.toPseudoMetricSpace
        (by rw [banachTensorUniformSpace_eq_productSeminorm hV hW]) }
  haveI : ContinuousSMul A (V ⊗[A] W) := by
    change @ContinuousSMul A (V ⊗[A] W) _ _ (banachTensorUniformSpace A V W).toTopologicalSpace
    rw [banachTensorUniformSpace_toTopologicalSpace]
    exact continuousSMul_banachTensorTopology A V W
  haveI : UniformContinuousConstSMul A (V ⊗[A] W) :=
    uniformContinuousConstSMul_of_continuousConstSMul A (V ⊗[A] W)
  let he : IsUniformEmbedding (equivCompletion A V W) :=
    AddMonoidHom.isUniformEmbedding_of_isEmbedding
      (f := (equivCompletion A V W).toLinearEquiv.toAddEquiv.toAddMonoidHom)
      (equivCompletion A V W).toHomeomorph.isEmbedding
  { (inferInstance : AddCommGroup (CompletedTensor A V W)),
    he.comapMetricSpace (equivCompletion A V W) with
    norm x := ‖equivCompletion A V W x‖
    dist_eq x y := by
      change dist (equivCompletion A V W x) (equivCompletion A V W y) =
        ‖equivCompletion A V W (-x + y)‖
      rw [map_add, map_neg, dist_eq_norm_neg_add] }

/-- On the image of `V ⊗[A] W`, the completed norm equals `productSeminorm A V W`. -/
theorem norm_toCompletion_of_bound
    (hV : ∃ C : ℝ≥0, ∀ (a : A) (v : V), ‖a • v‖ ≤ C * ‖a‖ * ‖v‖)
    (hW : ∃ C : ℝ≥0, ∀ (a : A) (w : W), ‖a • w‖ ≤ C * ‖a‖ * ‖w‖) (z : V ⊗[A] W) :
    (letI := normedAddCommGroupOfBound hV hW; ‖toCompletion A V W z‖) =
      productSeminorm A V W z := by
  let S0 := (productSeminorm A V W).toSeminormedAddCommGroup
  let : SeminormedAddCommGroup (V ⊗[A] W) :=
    { S0 with
      toPseudoMetricSpace := @PseudoMetricSpace.replaceUniformity (V ⊗[A] W)
        (banachTensorUniformSpace A V W) S0.toPseudoMetricSpace
        (by rw [banachTensorUniformSpace_eq_productSeminorm hV hW]) }
  change ‖equivCompletion A V W (toCompletion A V W z)‖ = productSeminorm A V W z
  rw [equivCompletion_toCompletion]
  exact Completion.norm_coe z

/-- The completed product norm on `CompletedTensor A V W` is ultrametric. -/
theorem isUltrametricDist_normedAddCommGroupOfBound
    (hV : ∃ C : ℝ≥0, ∀ (a : A) (v : V), ‖a • v‖ ≤ C * ‖a‖ * ‖v‖)
    (hW : ∃ C : ℝ≥0, ∀ (a : A) (w : W), ‖a • w‖ ≤ C * ‖a‖ * ‖w‖) :
    letI := normedAddCommGroupOfBound hV hW
    IsUltrametricDist (CompletedTensor A V W) := by
  let := normedAddCommGroupOfBound hV hW
  refine IsUltrametricDist.isUltrametricDist_of_isNonarchimedean_norm fun x y ↦ ?_
  refine (denseRange_toCompletion A V W).induction_on x
    (isClosed_le (continuous_norm.comp (continuous_id.add continuous_const))
      (continuous_norm.max continuous_const)) fun u ↦ ?_
  refine (denseRange_toCompletion A V W).induction_on y
    (isClosed_le (continuous_norm.comp (continuous_const.add continuous_id))
      (continuous_const.max continuous_norm)) fun v ↦ ?_
  rw [← map_add, norm_toCompletion_of_bound, norm_toCompletion_of_bound,
    norm_toCompletion_of_bound]
  exact productSeminorm_add_le_max u v

/-- Elementary tensors in `CompletedTensor A V W` satisfy `‖tmul A V W v w‖ ≤ ‖v‖ * ‖w‖`. -/
theorem norm_tmul_le_of_bound
    (hV : ∃ C : ℝ≥0, ∀ (a : A) (v : V), ‖a • v‖ ≤ C * ‖a‖ * ‖v‖)
    (hW : ∃ C : ℝ≥0, ∀ (a : A) (w : W), ‖a • w‖ ≤ C * ‖a‖ * ‖w‖) (v : V) (w : W) :
    (letI := normedAddCommGroupOfBound hV hW; ‖tmul A V W v w‖) ≤ ‖v‖ * ‖w‖ := by
  let := normedAddCommGroupOfBound hV hW
  rw [← toCompletion_tmul, norm_toCompletion_of_bound]
  exact productSeminorm_tmul_le v w

/-- A continuous `A`-bilinear map `β` into a complete ultrametric `A`-module bounded by
`C * (‖v‖ * ‖w‖)` lifts to a map on `CompletedTensor A V W` of norm bound `C`. -/
theorem norm_lift_le_of_bound
    (hV : ∃ C : ℝ≥0, ∀ (a : A) (v : V), ‖a • v‖ ≤ C * ‖a‖ * ‖v‖)
    (hW : ∃ C : ℝ≥0, ∀ (a : A) (w : W), ‖a • w‖ ≤ C * ‖a‖ * ‖w‖)
    {M : Type*} [NormedAddCommGroup M] [IsUltrametricDist M] [Module A M] [ContinuousSMul A M]
    [CompleteSpace M] (β : V →ₗ[A] W →ₗ[A] M) (hβ : Continuous fun p : V × W ↦ β p.1 p.2)
    {C : ℝ} (hC : ∀ v w, ‖β v w‖ ≤ C * (‖v‖ * ‖w‖)) (x : CompletedTensor A V W) :
    (letI := normedAddCommGroupOfBound hV hW; ‖lift β hβ x‖ ≤ C * ‖x‖) := by
  let := normedAddCommGroupOfBound hV hW
  refine (denseRange_toCompletion A V W).induction_on x
    (isClosed_le (continuous_norm.comp (lift β hβ).continuous)
      (continuous_const.mul continuous_norm)) fun z ↦ ?_
  rw [lift_toCompletion, norm_toCompletion_of_bound]
  exact norm_lift_le_mul_productSeminorm β hC z

/-- Scalar multiplication by `a : A` with `‖a • v‖ ≤ C * ‖v‖` scales the completed norm on
`CompletedTensor A V W` by at most `C`. -/
theorem norm_smul_le_of_bound
    (hV : ∃ C : ℝ≥0, ∀ (a : A) (v : V), ‖a • v‖ ≤ C * ‖a‖ * ‖v‖)
    (hW : ∃ C : ℝ≥0, ∀ (a : A) (w : W), ‖a • w‖ ≤ C * ‖a‖ * ‖w‖)
    {a : A} {C : ℝ} (ha : ∀ v : V, ‖a • v‖ ≤ C * ‖v‖) (x : CompletedTensor A V W) :
    (letI := normedAddCommGroupOfBound hV hW; ‖a • x‖ ≤ C * ‖x‖) := by
  let := normedAddCommGroupOfBound hV hW
  refine (denseRange_toCompletion A V W).induction_on x
    (isClosed_le (continuous_norm.comp (continuous_const_smul a))
      (continuous_const.mul continuous_norm)) fun z ↦ ?_
  rw [← map_smul, norm_toCompletion_of_bound, norm_toCompletion_of_bound]
  exact productSeminorm_smul_le_of_le ha z

end BoundedSMul

section ContractiveSMul

variable {A V W : Type*} [SeminormedCommRing A] [NormedRing.IsTate A]
  [SeminormedAddCommGroup V] [Module A V] [IsBoundedSMul A V]
  [SeminormedAddCommGroup W] [Module A W] [IsBoundedSMul A W]

/-- For modules with contractive scalar action over a seminormed Tate commutative ring `A`,
`CompletedTensor A V W` is a normed additive commutative group for the completed product norm. -/
noncomputable instance instNormedAddCommGroup : NormedAddCommGroup (CompletedTensor A V W) :=
  normedAddCommGroupOfBound ⟨1, fun a v ↦ by simpa using norm_smul_le a v⟩
    ⟨1, fun a w ↦ by simpa using norm_smul_le a w⟩

/-- The completed product norm on `CompletedTensor A V W` is ultrametric. -/
instance instIsUltrametricDist : IsUltrametricDist (CompletedTensor A V W) :=
  isUltrametricDist_normedAddCommGroupOfBound ⟨1, fun a v ↦ by simpa using norm_smul_le a v⟩
    ⟨1, fun a w ↦ by simpa using norm_smul_le a w⟩

/-- The action of `A` on `CompletedTensor A V W` is contractive. -/
instance instIsBoundedSMul : IsBoundedSMul A (CompletedTensor A V W) :=
  .of_norm_smul_le fun a x ↦ norm_smul_le_of_bound
    ⟨1, fun a v ↦ by simpa using norm_smul_le a v⟩
    ⟨1, fun a w ↦ by simpa using norm_smul_le a w⟩ (norm_smul_le a) x

/-- On the image of `V ⊗[A] W`, the norm on `CompletedTensor A V W` is `productSeminorm A V W`. -/
@[simp]
theorem norm_toCompletion (z : V ⊗[A] W) :
    ‖toCompletion A V W z‖ = productSeminorm A V W z :=
  norm_toCompletion_of_bound _ _ z

/-- The norm of an elementary tensor in `CompletedTensor A V W` is at most `‖v‖ * ‖w‖`. -/
theorem norm_tmul_le (v : V) (w : W) : ‖tmul A V W v w‖ ≤ ‖v‖ * ‖w‖ :=
  norm_tmul_le_of_bound _ _ v w

/-- The norm of a finite sum of elementary tensors in `CompletedTensor A V W` is at most the
maximum of `‖v i‖ * ‖w i‖`. -/
theorem norm_sum_tmul_le {ι : Type*} (s : Finset ι) (v : ι → V) (w : ι → W) :
    ‖∑ i ∈ s, tmul A V W (v i) (w i)‖ ≤ ↑(s.sup fun i ↦ ‖v i‖₊ * ‖w i‖₊) := by
  simp_rw [← toCompletion_tmul, ← map_sum, norm_toCompletion]
  exact productSeminorm_sum_tmul_le s v w

/-- If each term of `∑ i ∈ s, tmul A V W (v i) (w i)` satisfies `‖v i‖ * ‖w i‖ ≤ b` with `0 ≤ b`,
then so does the norm of the sum. -/
theorem norm_sum_tmul_le_of_le {ι : Type*} (s : Finset ι) (v : ι → V) (w : ι → W) {b : ℝ}
    (hb : 0 ≤ b) (h : ∀ i ∈ s, ‖v i‖ * ‖w i‖ ≤ b) :
    ‖∑ i ∈ s, tmul A V W (v i) (w i)‖ ≤ b := by
  simp_rw [← toCompletion_tmul, ← map_sum, norm_toCompletion]
  exact productSeminorm_sum_tmul_le_of_le s v w hb h

/-- A continuous `A`-bilinear map `β` into a complete ultrametric `A`-module bounded by
`C * (‖v‖ * ‖w‖)` induces a linear map `lift β hβ` bounded by `C * ‖x‖`. -/
theorem norm_lift_le {M : Type*} [NormedAddCommGroup M] [IsUltrametricDist M] [Module A M]
    [ContinuousSMul A M] [CompleteSpace M] (β : V →ₗ[A] W →ₗ[A] M)
    (hβ : Continuous fun p : V × W ↦ β p.1 p.2) {C : ℝ} (hC : ∀ v w, ‖β v w‖ ≤ C * (‖v‖ * ‖w‖))
    (x : CompletedTensor A V W) : ‖lift β hβ x‖ ≤ C * ‖x‖ :=
  norm_lift_le_of_bound _ _ β hβ hC x

/-- `CompletedTensor.map f g` scales norms by at most `C₁ * C₂` when `‖f v‖ ≤ C₁ * ‖v‖` and
`‖g w‖ ≤ C₂ * ‖w‖`. -/
theorem norm_map_le {V' W' : Type*} [SeminormedAddCommGroup V'] [Module A V'] [IsBoundedSMul A V']
    [SeminormedAddCommGroup W'] [Module A W'] [IsBoundedSMul A W'] (f : V →L[A] V')
    (g : W →L[A] W') {C₁ C₂ : ℝ} (hf : ∀ v, ‖f v‖ ≤ C₁ * ‖v‖) (hg : ∀ w, ‖g w‖ ≤ C₂ * ‖w‖)
    (x : CompletedTensor A V W) : ‖map f g x‖ ≤ C₁ * C₂ * ‖x‖ := by
  refine (denseRange_toCompletion A V W).induction_on x
    (isClosed_le (continuous_norm.comp (map f g).continuous)
      (continuous_const.mul continuous_norm)) fun z ↦ ?_
  have hmap : map f g (toCompletion A V W z) =
      toCompletion A V' W' (TensorProduct.map f.toLinearMap g.toLinearMap z) := by
    induction z using TensorProduct.inductionOn with
    | tmul v w => simp
    | add x y hx hy => simp [map_add, hx, hy]
  rw [hmap, norm_toCompletion, norm_toCompletion]
  exact productSeminorm_map_le f.toLinearMap g.toLinearMap hf hg z

/-- For a complete ultrametric `A`-module `M` with contractive scalar action over a seminormed Tate
commutative ring `A`, the scalar-unit isomorphism `lid A M : A ⊗̂_A M ≃L[A] M` is an isometry. -/
@[simp]
theorem norm_lid {M : Type*} [NormedAddCommGroup M] [IsUltrametricDist M] [Module A M]
    [IsBoundedSMul A M] [CompleteSpace M] (x : CompletedTensor A A M) :
    ‖lid A M x‖ = ‖x‖ := by
  refine (denseRange_toCompletion A A M).induction_on x
    (isClosed_eq (continuous_norm.comp (lid A M).continuous) continuous_norm) fun z ↦ ?_
  rw [lid_toCompletion, norm_toCompletion, productSeminorm_eq_norm_lid]

end ContractiveSMul

section NormedField

variable {K V W V' W' M : Type*} [NontriviallyNormedField K]
  [SeminormedAddCommGroup V] [NormedSpace K V]
  [SeminormedAddCommGroup W] [NormedSpace K W]
  [SeminormedAddCommGroup V'] [NormedSpace K V']
  [SeminormedAddCommGroup W'] [NormedSpace K W']

/-- Over a nontrivially normed field `K`, `CompletedTensor K V W` is a `NormedSpace` over `K`
whose underlying `Module K` instance is definitionally the topological one. -/
noncomputable instance instNormedSpace : NormedSpace K (CompletedTensor K V W) where
  toModule := inferInstance
  norm_smul_le := norm_smul_le

/-- Over a nontrivially normed field `K`, the operator norm of `CompletedTensor.map f g` is at
most `‖f‖ * ‖g‖`. -/
theorem opNorm_map_le (f : V →L[K] V') (g : W →L[K] W') : ‖map f g‖ ≤ ‖f‖ * ‖g‖ :=
  ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun x ↦
    norm_map_le f g f.le_opNorm g.le_opNorm x

section LiftIsometry

variable [NormedAddCommGroup M] [IsUltrametricDist M] [NormedSpace K M] [CompleteSpace M]

variable (K V W M) in
/-- **The isometric universal property of `CompletedTensor K V W`** over a nontrivially normed
field `K`: bounded `K`-bilinear maps `V →L[K] W →L[K] M` into an ultrametric Banach space `M`
correspond isometrically to bounded linear operators `CompletedTensor K V W →L[K] M`. -/
noncomputable def liftIsometry :
    (V →L[K] W →L[K] M) ≃ₗᵢ[K] (CompletedTensor K V W →L[K] M) where
  toFun B := lift B.toLinearMap₁₂ (B.toLinearMap₁₂.continuous₂_of_bound ‖B‖ B.le_opNorm₂)
  map_add' B₁ B₂ := ext fun v w ↦ by simp
  map_smul' c B := ext fun v w ↦ by simp
  invFun f :=
    (LinearMap.mkContinuous₂ ((tmul K V W).compr₂ f.toLinearMap) ‖f‖ fun v w ↦ by
      simpa [mul_assoc] using (f.le_opNorm (tmul K V W v w)).trans
        (mul_le_mul_of_nonneg_left (norm_tmul_le v w) (norm_nonneg f)))
  left_inv B := by ext v w; simp
  right_inv f := ext fun v w ↦ by simp
  norm_map' B := by
    let L : CompletedTensor K V W →L[K] M :=
      lift B.toLinearMap₁₂ (B.toLinearMap₁₂.continuous₂_of_bound ‖B‖ B.le_opNorm₂)
    refine le_antisymm ?_ ?_
    · refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg B) fun x ↦ ?_
      exact norm_lift_le _ _ (fun v w ↦ by simpa [mul_assoc] using B.le_opNorm₂ v w) x
    · refine B.opNorm_le_bound₂ (norm_nonneg L) fun v w ↦ ?_
      have h := L.le_opNorm (tmul K V W v w)
      have hL : L (tmul K V W v w) = B v w := lift_tmul _ _ v w
      rw [hL] at h
      exact h.trans <| by
        simpa [mul_assoc] using mul_le_mul_of_nonneg_left (norm_tmul_le v w) (norm_nonneg L)

/-- `liftIsometry` evaluates on an elementary tensor `v ⊗ w` as `B v w`. -/
@[simp]
theorem liftIsometry_tmul (B : V →L[K] W →L[K] M) (v : V) (w : W) :
    liftIsometry K V W M B (tmul K V W v w) = B v w := by
  simp [liftIsometry]

/-- The inverse of `liftIsometry` sends `f : CompletedTensor K V W →L[K] M` to
`(v, w) ↦ f (tmul K V W v w)`. -/
@[simp]
theorem liftIsometry_symm_apply (f : CompletedTensor K V W →L[K] M) (v : V) (w : W) :
    (liftIsometry K V W M).symm f v w = f (tmul K V W v w) := by
  rw [← liftIsometry_tmul ((liftIsometry K V W M).symm f) v w,
    LinearIsometryEquiv.apply_symm_apply]

end LiftIsometry

end NormedField

end BanachModule.CompletedTensor

end TauCeti.Huber
