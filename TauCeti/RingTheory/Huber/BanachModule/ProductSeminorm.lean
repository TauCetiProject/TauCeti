/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Normed.Module.Bases.CountableType
public import TauCeti.Analysis.Normed.Ring.PseudoUniformizer
public import TauCeti.RingTheory.Huber.BanachModule.CompletedTensor
import Mathlib.Analysis.Normed.Group.Completion
import Mathlib.LinearAlgebra.TensorProduct.Finiteness
import TauCeti.Analysis.Normed.Operator.BoundedLinearMaps

/-!
# The nonarchimedean product seminorm and completed product norm

For seminormed `A`-modules `V` and `W` over a commutative ring `A`, the *nonarchimedean product
seminorm* `TauCeti.Huber.BanachModule.productSeminorm A V W` of `u : V ⊗[A] W` is the infimum of
`maxᵢ ‖v i‖ * ‖w i‖` over all finite presentations `u = ∑ i : Fin n, v i ⊗ₜ[A] w i`, with maximum
`0` on the empty presentation (`n = 0`). Concatenating two presentations shows that
`productSeminorm A V W` satisfies the ultrametric inequality without any ultrametricity hypothesis
on `A`, `V` or `W`; it is the largest ultrametric additive group seminorm on `V ⊗[A] W` bounded by
`‖v‖ * ‖w‖` on elementary tensors (`TauCeti.Huber.BanachModule.le_productSeminorm`).

When `A` is a seminormed commutative ring whose action on `V` is bounded
(`‖a • v‖ ≤ C * ‖a‖ * ‖v‖`), the topology of `productSeminorm A V W` makes `A` act continuously
and `(v, w) ↦ v ⊗ₜ w` continuous, so `banachTensorTopology A V W` is finer than it and
`productSeminorm A V W` is uniformly continuous for `banachTensorUniformSpace A V W`. When `A` is
Tate (`TauCeti.NormedRing.IsTate A`) and both scalar actions are bounded, rescaling elementary
tensors by integer powers of a multiplicative pseudo-uniformiser reverses the comparison: the open
balls `{u | productSeminorm A V W u < r}` (`r > 0`) form a neighbourhood basis of `0` for
`banachTensorTopology A V W` (`TauCeti.Huber.hasBasis_banachTensorTopology`), and the two
uniformities coincide.

Extending `productSeminorm A V W` across `CompletedTensor.toCompletion` gives
`TauCeti.Huber.BanachModule.CompletedTensor.productNorm A V W : CompletedTensor A V W → ℝ`. Keeping
`productNorm` unbundled lets its term take no scalar-action proof arguments, so contractive and
merely bounded actions share the same notation; when `A` is Tate and both actions are bounded,
`productNorm` is definite (`productNorm_eq_zero_iff`), its positive-radius balls form a
neighbourhood basis of `0` on `V ⊗̂_A W` (`hasBasis_nhds_zero_productNorm`), and
`productAddGroupNorm` / `productNormedAddCommGroup` bundle it as a compatible `AddGroupNorm` and
`NormedAddCommGroup` retaining the completion uniformity definitionally (following the pattern of
`TauCeti.adaptedNorm`, `TauCeti.adaptedAddGroupNorm` and `TauCeti.adaptedNormedAddCommGroup`).
The finite-presentation `sInf` setup parallels `TensorProduct.projectiveSeminorm` in
`TauCeti.Analysis.Normed.Module.TensorProduct.ProjectiveSeminorm`, with `Finset.sup` in `ℝ≥0`
replacing `Finset.sum`.

Over a complete nontrivially normed field `L`, for ultrametric normed `L`-spaces `V` and `W`
(neither completeness of `V`, `W` nor spherical completeness of `L` is needed), almost-contractive
projections on finite-dimensional subspaces bound contractions with continuous functionals on
`E₀ ≤ V` (`norm_lid_map_le_productSeminorm`). Combined with almost-norming functionals, this shows
that `productSeminorm L V W` is a cross norm (`productSeminorm_tmul`) and is definite
(`productSeminorm_eq_zero_iff`). Consequently `toCompletion L V W : V ⊗[L] W → V ⊗̂_L W` is
injective (`CompletedTensor.toCompletion_injective`), `productNorm L V W` is a cross norm on
elementary tensors (`CompletedTensor.productNorm_tmul`), and tensoring with a unit vector `w`
preserves distances (`CompletedTensor.productNorm_unitVector`).

## Main definitions

* `TauCeti.Huber.BanachModule.productSeminorm A V W`: the nonarchimedean product seminorm on
  `V ⊗[A] W`.
* `TauCeti.Huber.BanachModule.CompletedTensor.productNorm A V W`: the continuous extension of
  `productSeminorm A V W` to `CompletedTensor A V W`.
* `TauCeti.Huber.BanachModule.CompletedTensor.productAddGroupNorm`: `productNorm` bundled as an
  `AddGroupNorm` over a Tate ring.
* `TauCeti.Huber.BanachModule.CompletedTensor.productNormedAddCommGroup`: the compatible
  `NormedAddCommGroup` structure on `CompletedTensor A V W` retaining its uniformity
  definitionally.

## Main results

* `TauCeti.Huber.BanachModule.productSeminorm_add_le_max`, `productSeminorm_tmul_le`,
  `exists_sum_tmul_eq_of_productSeminorm_lt`, `apply_le_mul_productSeminorm`: ultrametricity,
  finite-presentation characterisation and universal bound for `productSeminorm`.
* `TauCeti.Huber.BanachModule.productSeminorm_eq_norm_lid` and `productSeminorm_eq_norm_rid`:
  compatibility with the algebraic unit maps `A ⊗[A] W ≃ W` and `W ⊗[A] A ≃ W`.
* `TauCeti.Huber.hasBasis_banachTensorTopology_of_norm_smul_le` and
  `TauCeti.Huber.hasBasis_banachTensorTopology`: positive-radius balls of `productSeminorm` form a
  neighbourhood basis of `0` in `banachTensorTopology A V W` over a Tate seminormed ring.
* `TauCeti.Huber.BanachModule.CompletedTensor.productNorm_toCompletion`,
  `productNorm_add_le_max`, `productNorm_smul`, `hasBasis_nhds_zero_productNorm`,
  `productNorm_eq_zero_iff`: structure of the completed product norm.
* `TauCeti.Huber.BanachModule.norm_lid_map_le_productSeminorm`, `productSeminorm_tmul`,
  `productSeminorm_eq_zero_iff`, `CompletedTensor.toCompletion_injective`,
  `CompletedTensor.productNorm_tmul`, `CompletedTensor.productNorm_unitVector`: contraction bound,
  cross-norm property and definiteness over a complete nontrivially normed field.

## References

* K. S. Kedlaya and R. Liu, *Relative p-adic Hodge theory: Foundations*, Astérisque 371 (2015),
  Definitions 2.1.10 and 2.2.7, and Lemma 2.2.9(a).
* S. Bosch, U. Güntzer and R. Remmert, *Non-Archimedean Analysis*, Springer, 1984, §2.1.7.
* C. Perez-Garcia and W. H. Schikhof, *Locally Convex Spaces over Non-Archimedean Valued Fields*,
  Cambridge University Press, 2010, §10.1.
-/

public section

open Filter Set TensorProduct Topology UniformSpace
open scoped NNReal Uniformity

namespace TauCeti.Huber

namespace BanachModule

section Algebraic

variable (A V W : Type*) [CommRing A]
  [SeminormedAddCommGroup V] [Module A V]
  [SeminormedAddCommGroup W] [Module A W]

/-- The presentation costs `maxᵢ ‖v i‖ * ‖w i‖` of finite decompositions `u = ∑ i, v i ⊗ₜ w i`,
computed via `Finset.sup` in `ℝ≥0` so the empty presentation has cost `0`. -/
private def costs (u : V ⊗[A] W) : Set ℝ :=
  {c | ∃ (n : ℕ) (v : Fin n → V) (w : Fin n → W),
    ∑ i, v i ⊗ₜ[A] w i = u ∧
      ((Finset.univ.sup fun i ↦ ‖v i‖₊ * ‖w i‖₊ : ℝ≥0) : ℝ) = c}

variable {A V W}

private theorem costs_nonempty (u : V ⊗[A] W) : (costs A V W u).Nonempty := by
  obtain ⟨n, v, w, hu⟩ := TensorProduct.exists_sum_tmul_eq u
  exact ⟨_, n, v, w, hu.symm, rfl⟩

private theorem costs_bddBelow (u : V ⊗[A] W) : BddBelow (costs A V W u) := by
  refine ⟨0, ?_⟩
  rintro _ ⟨_, _, _, -, rfl⟩
  exact NNReal.coe_nonneg _

private theorem sInf_costs_le {n : ℕ} (v : Fin n → V) (w : Fin n → W) :
    sInf (costs A V W (∑ i, v i ⊗ₜ[A] w i)) ≤
      ((Finset.univ.sup fun i ↦ ‖v i‖₊ * ‖w i‖₊ : ℝ≥0) : ℝ) :=
  csInf_le (costs_bddBelow _) ⟨n, v, w, rfl, rfl⟩

private theorem sInf_costs_nonneg (u : V ⊗[A] W) : 0 ≤ sInf (costs A V W u) := by
  refine le_csInf (costs_nonempty u) ?_
  rintro _ ⟨_, _, _, -, rfl⟩
  exact NNReal.coe_nonneg _

private theorem sInf_costs_zero : sInf (costs A V W 0) = 0 := by
  refine le_antisymm ?_ (sInf_costs_nonneg 0)
  simpa using sInf_costs_le (A := A) (Fin.elim0 : Fin 0 → V) (Fin.elim0 : Fin 0 → W)

private theorem sInf_costs_neg (u : V ⊗[A] W) :
    sInf (costs A V W (-u)) = sInf (costs A V W u) := by
  have hle (x : V ⊗[A] W) : sInf (costs A V W (-x)) ≤ sInf (costs A V W x) := by
    refine le_csInf (costs_nonempty x) ?_
    rintro _ ⟨n, v, w, rfl, rfl⟩
    have hsum : -∑ i, v i ⊗ₜ[A] w i = ∑ i, (-v i) ⊗ₜ[A] w i := by
      simp only [TensorProduct.neg_tmul, Finset.sum_neg_distrib]
    rw [hsum]
    simpa [nnNorm_neg] using sInf_costs_le (A := A) (fun i ↦ -v i) w
  exact (hle u).antisymm (by simpa using hle (-u))

private theorem sInf_costs_add_le_max (u₁ u₂ : V ⊗[A] W) :
    sInf (costs A V W (u₁ + u₂)) ≤ max (sInf (costs A V W u₁)) (sInf (costs A V W u₂)) := by
  refine le_of_forall_pos_lt_add fun ε hε ↦ ?_
  obtain ⟨_, ⟨n, v, w, rfl, rfl⟩, h₁⟩ :=
    exists_lt_of_csInf_lt (costs_nonempty u₁) (lt_add_of_pos_right _ hε)
  obtain ⟨_, ⟨m, v', w', rfl, rfl⟩, h₂⟩ :=
    exists_lt_of_csInf_lt (costs_nonempty u₂) (lt_add_of_pos_right _ hε)
  have hsum : (∑ i, v i ⊗ₜ[A] w i) + (∑ j, v' j ⊗ₜ[A] w' j) =
      ∑ k, Fin.append v v' k ⊗ₜ[A] Fin.append w w' k := by
    simp [Fin.sum_univ_add]
  rw [hsum]
  refine (sInf_costs_le (A := A) (Fin.append v v') (Fin.append w w')).trans_lt ?_
  have hsup : (Finset.univ.sup fun k : Fin (n + m) ↦
        ‖Fin.append v v' k‖₊ * ‖Fin.append w w' k‖₊) ≤
      max (Finset.univ.sup fun i ↦ ‖v i‖₊ * ‖w i‖₊)
        (Finset.univ.sup fun j ↦ ‖v' j‖₊ * ‖w' j‖₊) := by
    refine Finset.sup_le fun k _ ↦ k.addCases (fun i ↦ ?_) (fun j ↦ ?_)
    · simpa using le_max_of_le_left
        (Finset.le_sup (f := fun i ↦ ‖v i‖₊ * ‖w i‖₊) (Finset.mem_univ i))
    · simpa using le_max_of_le_right
        (Finset.le_sup (f := fun j ↦ ‖v' j‖₊ * ‖w' j‖₊) (Finset.mem_univ j))
  calc ((Finset.univ.sup fun k ↦ ‖Fin.append v v' k‖₊ * ‖Fin.append w w' k‖₊ : ℝ≥0) : ℝ)
      ≤ max ((Finset.univ.sup fun i ↦ ‖v i‖₊ * ‖w i‖₊ : ℝ≥0) : ℝ)
          ((Finset.univ.sup fun j ↦ ‖v' j‖₊ * ‖w' j‖₊ : ℝ≥0) : ℝ) := by exact_mod_cast hsup
    _ < max (sInf (costs A V W (∑ i, v i ⊗ₜ[A] w i)) + ε)
          (sInf (costs A V W (∑ j, v' j ⊗ₜ[A] w' j)) + ε) := max_lt_max h₁ h₂
    _ = max (sInf (costs A V W (∑ i, v i ⊗ₜ[A] w i)))
          (sInf (costs A V W (∑ j, v' j ⊗ₜ[A] w' j))) + ε := max_add_add_right _ _ ε

variable (A V W) in
/-- **The nonarchimedean product seminorm** on `V ⊗[A] W`: the infimum of `maxᵢ ‖v i‖ * ‖w i‖` over
all finite presentations `u = ∑ i : Fin n, v i ⊗ₜ[A] w i`, where the empty presentation has maximum
`0`. -/
noncomputable def productSeminorm : AddGroupSeminorm (V ⊗[A] W) where
  toFun u := sInf (costs A V W u)
  map_zero' := sInf_costs_zero
  add_le' u₁ u₂ := (sInf_costs_add_le_max u₁ u₂).trans <|
    max_le_add_of_nonneg (sInf_costs_nonneg u₁) (sInf_costs_nonneg u₂)
  neg' := sInf_costs_neg

private theorem productSeminorm_apply (u : V ⊗[A] W) :
    productSeminorm A V W u = sInf (costs A V W u) :=
  rfl

/-- **Ultrametric inequality** for the product seminorm on `V ⊗[A] W`. -/
theorem productSeminorm_add_le_max (u₁ u₂ : V ⊗[A] W) :
    productSeminorm A V W (u₁ + u₂) ≤
      max (productSeminorm A V W u₁) (productSeminorm A V W u₂) :=
  sInf_costs_add_le_max u₁ u₂

/-- The product seminorm is a nonarchimedean additive group seminorm. -/
theorem isNonarchimedean_productSeminorm : IsNonarchimedean (productSeminorm A V W) :=
  productSeminorm_add_le_max

/-- Ultrametric bound for differences under the product seminorm. -/
theorem productSeminorm_sub_le_max (u₁ u₂ : V ⊗[A] W) :
    productSeminorm A V W (u₁ - u₂) ≤
      max (productSeminorm A V W u₁) (productSeminorm A V W u₂) := by
  simpa [sub_eq_add_neg] using productSeminorm_add_le_max u₁ (-u₂)

/-- The product seminorm of a finite sum of elementary tensors is at most the maximum of the
products of the norms of their factors. -/
theorem productSeminorm_sum_tmul_le {ι : Type*} (s : Finset ι) (v : ι → V) (w : ι → W) :
    productSeminorm A V W (∑ i ∈ s, v i ⊗ₜ[A] w i) ≤
      ((s.sup fun i ↦ ‖v i‖₊ * ‖w i‖₊ : ℝ≥0) : ℝ) := by
  let e := s.equivFin
  rw [productSeminorm_apply]
  have key := sInf_costs_le (A := A) (fun j ↦ v (e.symm j)) (fun j ↦ w (e.symm j))
  rw [← Finset.sum_coe_sort s, ← e.symm.sum_comp]
  refine key.trans_eq ?_
  congr 1
  refine le_antisymm (Finset.sup_le fun j _ ↦
      Finset.le_sup (f := fun i ↦ ‖v i‖₊ * ‖w i‖₊) (e.symm j).2)
    (Finset.sup_le fun i hi ↦ ?_)
  simpa using Finset.le_sup (f := fun j ↦ ‖v (e.symm j)‖₊ * ‖w (e.symm j)‖₊)
    (Finset.mem_univ (e ⟨i, hi⟩))

/-- If `0 ≤ b` bounds `‖v i‖ * ‖w i‖` for every `i ∈ s`, then `b` bounds the product seminorm of
`∑ i ∈ s, v i ⊗ₜ[A] w i`. -/
theorem productSeminorm_sum_tmul_le_of_le {ι : Type*} (s : Finset ι) (v : ι → V) (w : ι → W)
    {b : ℝ} (hb : 0 ≤ b) (h : ∀ i ∈ s, ‖v i‖ * ‖w i‖ ≤ b) :
    productSeminorm A V W (∑ i ∈ s, v i ⊗ₜ[A] w i) ≤ b := by
  refine (productSeminorm_sum_tmul_le s v w).trans ?_
  lift b to ℝ≥0 using hb
  exact_mod_cast Finset.sup_le fun i hi ↦ by exact_mod_cast h i hi

/-- A strict upper bound on `productSeminorm A V W u` is witnessed by some finite presentation
`u = ∑ i : Fin n, v i ⊗ₜ[A] w i` whose maximum term product is strictly below the bound. -/
theorem exists_sum_tmul_eq_of_productSeminorm_lt {u : V ⊗[A] W} {c : ℝ}
    (h : productSeminorm A V W u < c) :
    ∃ (n : ℕ) (v : Fin n → V) (w : Fin n → W),
      ∑ i, v i ⊗ₜ[A] w i = u ∧
        ((Finset.univ.sup fun i ↦ ‖v i‖₊ * ‖w i‖₊ : ℝ≥0) : ℝ) < c ∧
        ∀ i, ‖v i‖ * ‖w i‖ < c := by
  obtain ⟨_, ⟨n, v, w, hu, rfl⟩, hc⟩ := exists_lt_of_csInf_lt (costs_nonempty u) h
  refine ⟨n, v, w, hu, hc, fun i ↦ ?_⟩
  have hi : ‖v i‖₊ * ‖w i‖₊ ≤ Finset.univ.sup fun j ↦ ‖v j‖₊ * ‖w j‖₊ :=
    Finset.le_sup (f := fun j ↦ ‖v j‖₊ * ‖w j‖₊) (Finset.mem_univ i)
  have hi' : ‖v i‖ * ‖w i‖ ≤ ((Finset.univ.sup fun j ↦ ‖v j‖₊ * ‖w j‖₊ : ℝ≥0) : ℝ) := by
    exact_mod_cast hi
  exact hi'.trans_lt hc

/-- The product seminorm of an elementary tensor is at most the product of the norms. -/
theorem productSeminorm_tmul_le (v : V) (w : W) :
    productSeminorm A V W (v ⊗ₜ[A] w) ≤ ‖v‖ * ‖w‖ := by
  simpa using productSeminorm_sum_tmul_le_of_le (A := A) {()} (fun _ ↦ v) (fun _ ↦ w)
    (mul_nonneg (norm_nonneg v) (norm_nonneg w)) (by simp)

/-- **Universal bound for ultrametric seminorms.** A nonarchimedean additive group seminorm bounded
on images of elementary tensors by `C * (‖v‖ * ‖w‖)` (with `0 ≤ C`) is bounded on every tensor by
`C` times `productSeminorm A V W`. -/
theorem apply_le_mul_productSeminorm {G : Type*} [AddCommGroup G]
    {p : AddGroupSeminorm G} (hp : IsNonarchimedean p) {f : V ⊗[A] W →+ G} {C : ℝ} (hC : 0 ≤ C)
    (h : ∀ v w, p (f (v ⊗ₜ[A] w)) ≤ C * (‖v‖ * ‖w‖)) (u : V ⊗[A] W) :
    p (f u) ≤ C * productSeminorm A V W u := by
  rw [productSeminorm_apply, ← smul_eq_mul, ← Real.sInf_smul_of_nonneg hC]
  refine le_csInf (costs_nonempty u).smul_set ?_
  rintro _ ⟨_, ⟨n, v, w, rfl, rfl⟩, rfl⟩
  dsimp only
  rw [map_sum, smul_eq_mul]
  set b : ℝ := ((Finset.univ.sup fun i ↦ ‖v i‖₊ * ‖w i‖₊ : ℝ≥0) : ℝ)
  have hb (i : Fin n) : p (f (v i ⊗ₜ[A] w i)) ≤ C * b := by
    refine (h (v i) (w i)).trans (mul_le_mul_of_nonneg_left ?_ hC)
    exact_mod_cast Finset.le_sup (f := fun j ↦ ‖v j‖₊ * ‖w j‖₊) (Finset.mem_univ i)
  suffices ∀ s : Finset (Fin n), p (∑ i ∈ s, f (v i ⊗ₜ[A] w i)) ≤ C * b from this Finset.univ
  intro s
  induction s using Finset.induction with
  | empty => simpa using mul_nonneg hC (NNReal.coe_nonneg _)
  | insert j s hj ih =>
    rw [Finset.sum_insert hj]
    exact (hp _ _).trans (max_le (hb j) ih)

/-- `productSeminorm A V W` is the largest nonarchimedean additive group seminorm on `V ⊗[A] W`
bounded on elementary tensors by `‖v‖ * ‖w‖`. -/
theorem le_productSeminorm {p : AddGroupSeminorm (V ⊗[A] W)} (hp : IsNonarchimedean p)
    (h : ∀ v w, p (v ⊗ₜ[A] w) ≤ ‖v‖ * ‖w‖) : p ≤ productSeminorm A V W := fun u ↦ by
  simpa using apply_le_mul_productSeminorm hp (f := AddMonoidHom.id _) zero_le_one
    (by simpa using h) u

/-- A linear map induced by an `A`-bilinear map `β : V →ₗ[A] W →ₗ[A] M` into an ultrametric
seminormed `A`-module, bounded by `C * ‖v‖ * ‖w‖` (`0 ≤ C`), has norm at most
`C * productSeminorm A V W u`. -/
theorem norm_lift_le_mul_productSeminorm {M : Type*} [SeminormedAddCommGroup M]
    [IsUltrametricDist M] [Module A M] (β : V →ₗ[A] W →ₗ[A] M) {C : ℝ} (hC : 0 ≤ C)
    (h : ∀ v w, ‖β v w‖ ≤ C * ‖v‖ * ‖w‖) (u : V ⊗[A] W) :
    ‖TensorProduct.lift β u‖ ≤ C * productSeminorm A V W u :=
  apply_le_mul_productSeminorm (p := normAddGroupSeminorm M) IsUltrametricDist.norm_add_le_max
    (f := (TensorProduct.lift β).toAddMonoidHom) hC
    (fun v w ↦ by simpa [mul_assoc] using h v w) u

/-- Functoriality bound for `productSeminorm` under bounded `A`-linear maps. -/
theorem productSeminorm_map_le {V' W' : Type*} [SeminormedAddCommGroup V'] [Module A V']
    [SeminormedAddCommGroup W'] [Module A W'] (f : V →ₗ[A] V') (g : W →ₗ[A] W') {C₁ C₂ : ℝ}
    (hC₁ : 0 ≤ C₁) (hf : ∀ v, ‖f v‖ ≤ C₁ * ‖v‖) (hC₂ : 0 ≤ C₂) (hg : ∀ w, ‖g w‖ ≤ C₂ * ‖w‖)
    (u : V ⊗[A] W) :
    productSeminorm A V' W' (TensorProduct.map f g u) ≤
      C₁ * C₂ * productSeminorm A V W u :=
  apply_le_mul_productSeminorm isNonarchimedean_productSeminorm
    (f := (TensorProduct.map f g).toAddMonoidHom) (mul_nonneg hC₁ hC₂)
    (fun v w ↦ by
      refine (productSeminorm_tmul_le (f v) (g w)).trans ?_
      calc ‖f v‖ * ‖g w‖ ≤ (C₁ * ‖v‖) * (C₂ * ‖w‖) :=
            mul_le_mul (hf v) (hg w) (norm_nonneg _) (mul_nonneg hC₁ (norm_nonneg _))
        _ = C₁ * C₂ * (‖v‖ * ‖w‖) := by ring) u

private theorem productSeminorm_comm_le (u : V ⊗[A] W) :
    productSeminorm A W V (TensorProduct.comm A V W u) ≤ productSeminorm A V W u := by
  simpa using apply_le_mul_productSeminorm isNonarchimedean_productSeminorm
    (f := (TensorProduct.comm A V W).toLinearMap.toAddMonoidHom) zero_le_one
    (fun v w ↦ by simpa [mul_comm ‖v‖] using productSeminorm_tmul_le (A := A) w v) u

/-- Swapping the tensor factors preserves `productSeminorm`. -/
@[simp]
theorem productSeminorm_comm (u : V ⊗[A] W) :
    productSeminorm A W V (TensorProduct.comm A V W u) = productSeminorm A V W u :=
  (productSeminorm_comm_le u).antisymm <| by
    simpa using productSeminorm_comm_le (TensorProduct.comm A V W u)

end Algebraic

section SeminormedRing

variable {A V W : Type*} [SeminormedCommRing A]
  [SeminormedAddCommGroup V] [Module A V]
  [SeminormedAddCommGroup W] [Module A W]

/-- Under a scalar-action bound `‖a • v‖ ≤ C * ‖a‖ * ‖v‖` on `V`, `productSeminorm` satisfies
`productSeminorm A V W (a • u) ≤ C * ‖a‖ * productSeminorm A V W u`. -/
theorem productSeminorm_smul_le_of_norm_smul_le {C : ℝ≥0}
    (hV : ∀ (a : A) (v : V), ‖a • v‖ ≤ C * ‖a‖ * ‖v‖) (a : A) (u : V ⊗[A] W) :
    productSeminorm A V W (a • u) ≤ C * ‖a‖ * productSeminorm A V W u :=
  apply_le_mul_productSeminorm isNonarchimedean_productSeminorm
    (f := AddMonoidHom.mk' (a • ·) (smul_add a)) (mul_nonneg C.coe_nonneg (norm_nonneg a))
    (fun v w ↦ by
      rw [AddMonoidHom.mk'_apply, smul_tmul']
      refine (productSeminorm_tmul_le (a • v) w).trans ?_
      calc ‖a • v‖ * ‖w‖ ≤ (C * ‖a‖ * ‖v‖) * ‖w‖ :=
            mul_le_mul_of_nonneg_right (hV a v) (norm_nonneg w)
        _ = C * ‖a‖ * (‖v‖ * ‖w‖) := by ring) u

/-- Under a contractive scalar action on `V`, `productSeminorm` is submultiplicative for scalar
multiplication. -/
theorem productSeminorm_smul_le [IsBoundedSMul A V] (a : A) (u : V ⊗[A] W) :
    productSeminorm A V W (a • u) ≤ ‖a‖ * productSeminorm A V W u := by
  simpa using productSeminorm_smul_le_of_norm_smul_le (C := 1)
    (fun r v ↦ by simpa using norm_smul_le r v) a u

/-- On `A ⊗[A] W` with `‖1‖ = 1` and ultrametric `W` with contractive `A`-action, the product
seminorm is the norm of the image under `TensorProduct.lid A W`. -/
@[simp]
theorem productSeminorm_eq_norm_lid [NormOneClass A] [IsUltrametricDist W] [IsBoundedSMul A W]
    (u : A ⊗[A] W) :
    productSeminorm A A W u = ‖TensorProduct.lid A W u‖ := by
  refine le_antisymm ?_ ?_
  · calc productSeminorm A A W u
        = productSeminorm A A W (1 ⊗ₜ[A] TensorProduct.lid A W u) := by
          rw [← TensorProduct.lid_symm_apply, LinearEquiv.symm_apply_apply]
      _ ≤ ‖(1 : A)‖ * ‖TensorProduct.lid A W u‖ := productSeminorm_tmul_le _ _
      _ = ‖TensorProduct.lid A W u‖ := by rw [norm_one, one_mul]
  · have h := apply_le_mul_productSeminorm (p := normAddGroupSeminorm W)
      IsUltrametricDist.norm_add_le_max
      (f := (TensorProduct.lid A W).toLinearMap.toAddMonoidHom) zero_le_one
      (fun a w ↦ by simpa using norm_smul_le a w) u
    simpa using h

/-- On `W ⊗[A] A` with `‖1‖ = 1` and ultrametric `W` with contractive `A`-action, the product
seminorm is the norm of the image under `TensorProduct.rid A W`. -/
@[simp]
theorem productSeminorm_eq_norm_rid [NormOneClass A] [IsUltrametricDist W] [IsBoundedSMul A W]
    (u : W ⊗[A] A) :
    productSeminorm A W A u = ‖TensorProduct.rid A W u‖ := by
  rw [← productSeminorm_comm, productSeminorm_eq_norm_lid, ← TensorProduct.comm_trans_lid,
    LinearEquiv.trans_apply]

end SeminormedRing

section NormedField

variable {L V W : Type*} [NormedField L]
  [SeminormedAddCommGroup V] [NormedSpace L V]
  [SeminormedAddCommGroup W] [NormedSpace L W]

/-- Over a normed field, `productSeminorm` is homogeneous under scalar multiplication. -/
@[simp]
theorem productSeminorm_smul (a : L) (u : V ⊗[L] W) :
    productSeminorm L V W (a • u) = ‖a‖ * productSeminorm L V W u := by
  rcases eq_or_ne a 0 with rfl | ha
  · simp
  · refine (productSeminorm_smul_le a u).antisymm ?_
    calc ‖a‖ * productSeminorm L V W u
        = ‖a‖ * productSeminorm L V W (a⁻¹ • a • u) := by rw [inv_smul_smul₀ ha]
      _ ≤ ‖a‖ * (‖a⁻¹‖ * productSeminorm L V W (a • u)) :=
          mul_le_mul_of_nonneg_left (productSeminorm_smul_le a⁻¹ (a • u)) (norm_nonneg a)
      _ = productSeminorm L V W (a • u) := by
          rw [norm_inv, ← mul_assoc, mul_inv_cancel₀ (norm_ne_zero_iff.mpr ha), one_mul]

end NormedField

end BanachModule

section TensorTopology

variable {A V W : Type*} [SeminormedCommRing A]
  [SeminormedAddCommGroup V] [Module A V]
  [SeminormedAddCommGroup W] [Module A W]

/-- When the scalar action of `A` on `V` is bounded (`‖a • v‖ ≤ C * ‖a‖ * ‖v‖`), the tensor
topology on `V ⊗[A] W` is finer than the topology of `productSeminorm A V W`. -/
theorem banachTensorTopology_le_productSeminorm_of_norm_smul_le
    (hV : ∃ C : ℝ≥0, ∀ (a : A) (v : V), ‖a • v‖ ≤ C * ‖a‖ * ‖v‖) :
    banachTensorTopology A V W ≤ @UniformSpace.toTopologicalSpace _
      (BanachModule.productSeminorm A V W).toSeminormedAddCommGroup.toUniformSpace := by
  let _ : SeminormedAddCommGroup (V ⊗[A] W) :=
    (BanachModule.productSeminorm A V W).toSeminormedAddCommGroup
  have : IsUltrametricDist (V ⊗[A] W) :=
    IsUltrametricDist.isUltrametricDist_of_isNonarchimedean_norm
      BanachModule.isNonarchimedean_productSeminorm
  obtain ⟨C, hC⟩ := hV
  have : ContinuousSMul A (V ⊗[A] W) :=
    TauCeti.continuousSMul_of_norm_smul_le
      ⟨C, BanachModule.productSeminorm_smul_le_of_norm_smul_le hC⟩
  have htmul : Continuous fun p : V × W ↦ p.1 ⊗ₜ[A] p.2 :=
    (TensorProduct.mk A V W).continuous₂_of_bound 1 fun v w ↦ by
      rw [TensorProduct.mk_apply, one_mul]
      exact BanachModule.productSeminorm_tmul_le v w
  exact banachTensorTopology_le inferInstance inferInstance htmul

/-- Under a bounded scalar action on `V`, `productSeminorm A V W` is continuous for
`banachTensorTopology A V W`. -/
theorem continuous_productSeminorm_of_norm_smul_le
    (hV : ∃ C : ℝ≥0, ∀ (a : A) (v : V), ‖a • v‖ ≤ C * ‖a‖ * ‖v‖) :
    Continuous[banachTensorTopology A V W, _] (BanachModule.productSeminorm A V W) := by
  let _ : SeminormedAddCommGroup (V ⊗[A] W) :=
    (BanachModule.productSeminorm A V W).toSeminormedAddCommGroup
  exact continuous_iff_le_induced.mpr <|
    (banachTensorTopology_le_productSeminorm_of_norm_smul_le hV).trans
      (continuous_iff_le_induced.mp continuous_norm)

/-- Under a contractive scalar action on `V`, `productSeminorm A V W` is continuous for
`banachTensorTopology A V W`. -/
theorem continuous_productSeminorm [IsBoundedSMul A V] :
    Continuous[banachTensorTopology A V W, _] (BanachModule.productSeminorm A V W) :=
  continuous_productSeminorm_of_norm_smul_le ⟨1, fun a v ↦ by simpa using norm_smul_le a v⟩

/-- Under a bounded scalar action on `V`, `banachTensorUniformSpace A V W` is finer than the
uniformity of `productSeminorm A V W`. -/
theorem banachTensorUniformSpace_le_productSeminorm_of_norm_smul_le
    (hV : ∃ C : ℝ≥0, ∀ (a : A) (v : V), ‖a • v‖ ≤ C * ‖a‖ * ‖v‖) :
    banachTensorUniformSpace A V W ≤
      (BanachModule.productSeminorm A V W).toSeminormedAddCommGroup.toUniformSpace := by
  have hu₁ : @IsUniformAddGroup (V ⊗[A] W) (banachTensorUniformSpace A V W) _ :=
    isUniformAddGroup_banachTensorUniformSpace A V W
  let inst₂ : SeminormedAddCommGroup (V ⊗[A] W) :=
    (BanachModule.productSeminorm A V W).toSeminormedAddCommGroup
  have hu₂ : @IsUniformAddGroup (V ⊗[A] W) inst₂.toUniformSpace _ := inferInstance
  rw [UniformSpace.le_def,
    (letI := banachTensorUniformSpace A V W; haveI := hu₁
     uniformity_eq_comap_nhds_zero (V ⊗[A] W)),
    (letI := inst₂.toUniformSpace; haveI := hu₂; uniformity_eq_comap_nhds_zero (V ⊗[A] W)),
    banachTensorUniformSpace_toTopologicalSpace]
  exact Filter.comap_mono
    (nhds_mono (banachTensorTopology_le_productSeminorm_of_norm_smul_le hV))

/-- Under a bounded scalar action on `V`, `productSeminorm A V W` is uniformly continuous for
`banachTensorUniformSpace A V W`. -/
theorem uniformContinuous_productSeminorm_of_norm_smul_le
    (hV : ∃ C : ℝ≥0, ∀ (a : A) (v : V), ‖a • v‖ ≤ C * ‖a‖ * ‖v‖) :
    UniformContinuous[banachTensorUniformSpace A V W, inferInstance]
      (BanachModule.productSeminorm A V W) := by
  let _ : SeminormedAddCommGroup (V ⊗[A] W) :=
    (BanachModule.productSeminorm A V W).toSeminormedAddCommGroup
  exact uniformContinuous_iff_le_comap.mpr <|
    (banachTensorUniformSpace_le_productSeminorm_of_norm_smul_le hV).trans
      (uniformContinuous_iff_le_comap.mp uniformContinuous_norm)

/-- Under a contractive scalar action on `V`, `productSeminorm A V W` is uniformly continuous for
`banachTensorUniformSpace A V W`. -/
theorem uniformContinuous_productSeminorm [IsBoundedSMul A V] :
    UniformContinuous[banachTensorUniformSpace A V W, inferInstance]
      (BanachModule.productSeminorm A V W) :=
  uniformContinuous_productSeminorm_of_norm_smul_le
    ⟨1, fun a v ↦ by simpa using norm_smul_le a v⟩

/-- Auxiliary rescaling lemma assuming strictly positive scalar-action constants `M₁, M₂ > 0`. -/
private theorem exists_tmul_eq_norm_lt_of_pos [NormedRing.IsTate A] {M₁ M₂ : ℝ}
    (hM₁ : 0 < M₁) (hM₂ : 0 < M₂)
    (hC₁' : ∀ (a : A) (v : V), ‖a • v‖ ≤ M₁ * ‖a‖ * ‖v‖)
    (hC₂' : ∀ (a : A) (w : W), ‖a • w‖ ≤ M₂ * ‖a‖ * ‖w‖)
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ r > 0, ∀ (v : V) (w : W), ‖v‖ * ‖w‖ < r →
      ∃ (v' : V) (w' : W), v' ⊗ₜ[A] w' = v ⊗ₜ[A] w ∧ ‖v'‖ < δ ∧ ‖w'‖ < δ := by
  obtain ⟨ϖ⟩ := NormedRing.IsTate.nonempty_pseudoUniformizer (R := A)
  set q := ‖(ϖ.unit : A)‖
  have hq0 : 0 < q := ϖ.norm_pos
  obtain ⟨k, hk⟩ := exists_pow_lt_of_lt_one (div_pos hδ hM₁) ϖ.norm_lt_one
  have hqk : 0 < q ^ ((k : ℤ) + 1) := zpow_pos hq0 _
  refine ⟨δ * q ^ ((k : ℤ) + 1) / M₂, div_pos (mul_pos hδ hqk) hM₂, fun v w hvw ↦ ?_⟩
  have hbal (n : ℤ) :
      (((ϖ.unit ^ n : Aˣ) : A) • v) ⊗ₜ[A] (((ϖ.unit ^ (-n) : Aˣ) : A) • w) = v ⊗ₜ[A] w := by
    rw [smul_tmul, ← mul_smul, ← Units.val_mul, ← zpow_add, add_neg_cancel, zpow_zero,
      Units.val_one, one_smul]
  rcases eq_or_ne ‖v‖ 0 with hv0 | hv0
  · obtain ⟨m, hm⟩ := exists_pow_lt_of_lt_one
      (div_pos hδ (mul_pos hM₂ (by linarith [norm_nonneg w] : 0 < ‖w‖ + 1))) ϖ.norm_lt_one
    refine ⟨(((ϖ.unit ^ (-(m : ℤ)) : Aˣ) : A)) • v, (((ϖ.unit ^ (m : ℤ) : Aˣ) : A)) • w,
      by simpa only [neg_neg] using hbal (-(m : ℤ)),
      (hC₁' _ v).trans_lt (by simp [hv0, hδ]), ?_⟩
    calc ‖(((ϖ.unit ^ (m : ℤ) : Aˣ) : A)) • w‖
        ≤ M₂ * ‖((ϖ.unit ^ (m : ℤ) : Aˣ) : A)‖ * ‖w‖ := hC₂' _ w
      _ = q ^ m * (M₂ * ‖w‖) := by rw [ϖ.norm_zpow, zpow_natCast]; ring
      _ ≤ q ^ m * (M₂ * (‖w‖ + 1)) :=
          mul_le_mul_of_nonneg_left (by nlinarith) (pow_nonneg hq0.le m)
      _ < δ := (lt_div_iff₀ (mul_pos hM₂ (by linarith [norm_nonneg w]))).mp hm
  · obtain ⟨n, hn₁, hn₂⟩ := ϖ.exists_zpow_mul_norm_lt hv0 (k : ℤ)
      (by simpa only [zpow_natCast] using hk)
    refine ⟨(((ϖ.unit ^ n : Aˣ) : A)) • v, (((ϖ.unit ^ (-n) : Aˣ) : A)) • w, hbal n, ?_, ?_⟩
    · calc ‖(((ϖ.unit ^ n : Aˣ) : A)) • v‖
          ≤ M₁ * (q ^ n * ‖v‖) := by
            simpa only [ϖ.norm_zpow, mul_assoc] using hC₁' ((ϖ.unit ^ n : Aˣ) : A) v
        _ < M₁ * (δ / M₁) := mul_lt_mul_of_pos_left hn₁ hM₁
        _ = δ := mul_div_cancel₀ δ hM₁.ne'
    · calc ‖(((ϖ.unit ^ (-n) : Aˣ) : A)) • w‖
          ≤ M₂ * (q ^ n)⁻¹ * ‖w‖ :=
            (hC₂' ((ϖ.unit ^ (-n) : Aˣ) : A) w).trans_eq (by rw [ϖ.norm_zpow, zpow_neg])
        _ ≤ M₂ * ((q ^ ((k : ℤ) + 1))⁻¹ * ‖v‖) * ‖w‖ :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hn₂ hM₂.le) (norm_nonneg w)
        _ = (‖v‖ * ‖w‖) * (M₂ / q ^ ((k : ℤ) + 1)) := by rw [div_eq_mul_inv]; ring
        _ < (δ * q ^ ((k : ℤ) + 1) / M₂) * (M₂ / q ^ ((k : ℤ) + 1)) :=
            mul_lt_mul_of_pos_right hvw (div_pos hM₂ hqk)
        _ = δ := by field_simp

/-- Key rescaling step over a Tate ring: an elementary tensor `v ⊗ₜ w` with small `‖v‖ * ‖w‖` can
be balanced by an integer power of a multiplicative pseudo-uniformiser so both factors lie in a
given ball around `0`. -/
private theorem exists_tmul_eq_norm_lt [NormedRing.IsTate A] {C₁ C₂ : ℝ≥0}
    (hC₁ : ∀ (a : A) (v : V), ‖a • v‖ ≤ C₁ * ‖a‖ * ‖v‖)
    (hC₂ : ∀ (a : A) (w : W), ‖a • w‖ ≤ C₂ * ‖a‖ * ‖w‖)
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ r > 0, ∀ (v : V) (w : W), ‖v‖ * ‖w‖ < r →
      ∃ (v' : V) (w' : W), v' ⊗ₜ[A] w' = v ⊗ₜ[A] w ∧ ‖v'‖ < δ ∧ ‖w'‖ < δ :=
  exists_tmul_eq_norm_lt_of_pos (M₁ := max C₁ 1) (M₂ := max C₂ 1)
    (lt_max_of_lt_right zero_lt_one) (lt_max_of_lt_right zero_lt_one)
    (fun a v ↦ (hC₁ a v).trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg a)) (norm_nonneg v)))
    (fun a w ↦ (hC₂ a w).trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg a)) (norm_nonneg w)))
    hδ

/-- Over a Tate seminormed commutative ring `A` with bounded scalar actions on `V` and `W`,
`banachTensorTopology A V W` coincides with the topology of `BanachModule.productSeminorm A V W`. -/
theorem banachTensorTopology_eq_productSeminorm_of_norm_smul_le [NormedRing.IsTate A]
    (hV : ∃ C : ℝ≥0, ∀ (a : A) (v : V), ‖a • v‖ ≤ C * ‖a‖ * ‖v‖)
    (hW : ∃ C : ℝ≥0, ∀ (a : A) (w : W), ‖a • w‖ ≤ C * ‖a‖ * ‖w‖) :
    banachTensorTopology A V W = @UniformSpace.toTopologicalSpace _
      (BanachModule.productSeminorm A V W).toSeminormedAddCommGroup.toUniformSpace := by
  let t₁ := banachTensorTopology A V W
  have ht₁ : @NonarchimedeanAddGroup (V ⊗[A] W) _ t₁ :=
    nonarchimedeanAddGroup_banachTensorTopology A V W
  let _ : SeminormedAddCommGroup (V ⊗[A] W) :=
    (BanachModule.productSeminorm A V W).toSeminormedAddCommGroup
  refine IsTopologicalAddGroup.ext ht₁.toIsTopologicalAddGroup inferInstance
    (le_antisymm (nhds_mono (banachTensorTopology_le_productSeminorm_of_norm_smul_le hV)) ?_)
  intro U hU
  obtain ⟨H, hHU⟩ := @NonarchimedeanAddGroup.is_nonarchimedean (V ⊗[A] W) _ t₁ _ U hU
  have htmul : Continuous[_, t₁] fun p : V × W ↦ p.1 ⊗ₜ[A] p.2 :=
    continuous_tmul_banachTensorTopology A V W
  have hpre : {p : V × W | p.1 ⊗ₜ[A] p.2 ∈ H} ∈ 𝓝 (0 : V × W) :=
    htmul.continuousAt.preimage_mem_nhds (by simpa using H.isOpen.mem_nhds H.zero_mem)
  rw [nhds_prod_eq, Filter.mem_prod_iff] at hpre
  obtain ⟨U₁, hU₁, U₂, hU₂, hsub⟩ := hpre
  obtain ⟨δ₁, hδ₁, hB₁⟩ := Metric.mem_nhds_iff.mp hU₁
  obtain ⟨δ₂, hδ₂, hB₂⟩ := Metric.mem_nhds_iff.mp hU₂
  obtain ⟨C₁, hC₁⟩ := hV
  obtain ⟨C₂, hC₂⟩ := hW
  obtain ⟨r, hr, hbal⟩ := exists_tmul_eq_norm_lt hC₁ hC₂ (lt_min hδ₁ hδ₂)
  refine Filter.mem_of_superset (NormedAddGroup.nhds_zero_basis_norm_lt.mem_of_mem hr) ?_
  intro u hu
  obtain ⟨n, v, w, rfl, -, hlt⟩ :=
    BanachModule.exists_sum_tmul_eq_of_productSeminorm_lt (u := u) hu
  refine hHU (H.toAddSubgroup.sum_mem fun i _ ↦ ?_)
  obtain ⟨v', w', heq, hv', hw'⟩ := hbal (v i) (w i) (hlt i)
  rw [← heq]
  exact @hsub (v', w') ⟨hB₁ (by simpa using hv'.trans_le (min_le_left _ _)),
    hB₂ (by simpa using hw'.trans_le (min_le_right _ _))⟩

variable (A V W) in
/-- Over a Tate seminormed commutative ring with contractive scalar actions, `banachTensorTopology`
coincides with the topology of `BanachModule.productSeminorm`. -/
theorem banachTensorTopology_eq_productSeminorm [NormedRing.IsTate A]
    [IsBoundedSMul A V] [IsBoundedSMul A W] :
    banachTensorTopology A V W = @UniformSpace.toTopologicalSpace _
      (BanachModule.productSeminorm A V W).toSeminormedAddCommGroup.toUniformSpace :=
  banachTensorTopology_eq_productSeminorm_of_norm_smul_le
    ⟨1, fun a v ↦ by simpa using norm_smul_le a v⟩
    ⟨1, fun a w ↦ by simpa using norm_smul_le a w⟩

/-- Over a Tate seminormed commutative ring `A` with bounded scalar actions on `V` and `W`,
`banachTensorUniformSpace A V W` coincides with the uniformity of
`BanachModule.productSeminorm A V W`. -/
theorem banachTensorUniformSpace_eq_productSeminorm_of_norm_smul_le [NormedRing.IsTate A]
    (hV : ∃ C : ℝ≥0, ∀ (a : A) (v : V), ‖a • v‖ ≤ C * ‖a‖ * ‖v‖)
    (hW : ∃ C : ℝ≥0, ∀ (a : A) (w : W), ‖a • w‖ ≤ C * ‖a‖ * ‖w‖) :
    banachTensorUniformSpace A V W =
      (BanachModule.productSeminorm A V W).toSeminormedAddCommGroup.toUniformSpace := by
  let _ : SeminormedAddCommGroup (V ⊗[A] W) :=
    (BanachModule.productSeminorm A V W).toSeminormedAddCommGroup
  exact IsUniformAddGroup.ext (isUniformAddGroup_banachTensorUniformSpace A V W) inferInstance
    (by rw [banachTensorUniformSpace_toTopologicalSpace,
          banachTensorTopology_eq_productSeminorm_of_norm_smul_le hV hW])

variable (A V W) in
/-- Over a Tate seminormed commutative ring with contractive scalar actions,
`banachTensorUniformSpace` coincides with the uniformity of `BanachModule.productSeminorm`. -/
theorem banachTensorUniformSpace_eq_productSeminorm [NormedRing.IsTate A]
    [IsBoundedSMul A V] [IsBoundedSMul A W] :
    banachTensorUniformSpace A V W =
      (BanachModule.productSeminorm A V W).toSeminormedAddCommGroup.toUniformSpace :=
  banachTensorUniformSpace_eq_productSeminorm_of_norm_smul_le
    ⟨1, fun a v ↦ by simpa using norm_smul_le a v⟩
    ⟨1, fun a w ↦ by simpa using norm_smul_le a w⟩

/-- **Neighbourhood basis of the tensor topology.** Over a Tate seminormed commutative ring `A`
with bounded scalar actions on `V` and `W`, the positive-radius open balls of
`BanachModule.productSeminorm A V W` form a neighbourhood basis of `0` in
`banachTensorTopology A V W`. -/
theorem hasBasis_banachTensorTopology_of_norm_smul_le [NormedRing.IsTate A]
    (hV : ∃ C : ℝ≥0, ∀ (a : A) (v : V), ‖a • v‖ ≤ C * ‖a‖ * ‖v‖)
    (hW : ∃ C : ℝ≥0, ∀ (a : A) (w : W), ‖a • w‖ ≤ C * ‖a‖ * ‖w‖) :
    (@nhds (V ⊗[A] W) (banachTensorTopology A V W) 0).HasBasis (0 < ·)
      (fun r ↦ {u | BanachModule.productSeminorm A V W u < r}) := by
  let inst : SeminormedAddCommGroup (V ⊗[A] W) :=
    (BanachModule.productSeminorm A V W).toSeminormedAddCommGroup
  rw [banachTensorTopology_eq_productSeminorm_of_norm_smul_le hV hW]
  exact @NormedAddGroup.nhds_zero_basis_norm_lt (V ⊗[A] W) inst.toSeminormedAddGroup

variable (A V W) in
/-- **Neighbourhood basis of the tensor topology** under contractive scalar actions. -/
theorem hasBasis_banachTensorTopology [NormedRing.IsTate A]
    [IsBoundedSMul A V] [IsBoundedSMul A W] :
    (@nhds (V ⊗[A] W) (banachTensorTopology A V W) 0).HasBasis (0 < ·)
      (fun r ↦ {u | BanachModule.productSeminorm A V W u < r}) :=
  hasBasis_banachTensorTopology_of_norm_smul_le
    ⟨1, fun a v ↦ by simpa using norm_smul_le a v⟩
    ⟨1, fun a w ↦ by simpa using norm_smul_le a w⟩

end TensorTopology

namespace BanachModule

namespace CompletedTensor

/-- The uniformity of the tensor topology, registered locally on the algebraic tensor product. -/
noncomputable local instance tensorUniformSpace {A V W : Type*} [CommRing A] [TopologicalSpace A]
    [AddCommGroup V] [Module A V] [TopologicalSpace V]
    [AddCommGroup W] [Module A W] [TopologicalSpace W] :
    UniformSpace (V ⊗[A] W) :=
  banachTensorUniformSpace A V W

local instance {A V W : Type*} [CommRing A] [TopologicalSpace A]
    [AddCommGroup V] [Module A V] [TopologicalSpace V]
    [AddCommGroup W] [Module A W] [TopologicalSpace W] :
    IsUniformAddGroup (V ⊗[A] W) :=
  isUniformAddGroup_banachTensorUniformSpace A V W

local instance {A V W : Type*} [CommRing A] [TopologicalSpace A]
    [AddCommGroup V] [Module A V] [TopologicalSpace V]
    [AddCommGroup W] [Module A W] [TopologicalSpace W] :
    ContinuousSMul A (V ⊗[A] W) := by
  rw [banachTensorUniformSpace_toTopologicalSpace]
  exact continuousSMul_banachTensorTopology A V W

local instance {A V W : Type*} [CommRing A] [TopologicalSpace A]
    [AddCommGroup V] [Module A V] [TopologicalSpace V]
    [AddCommGroup W] [Module A W] [TopologicalSpace W] :
    UniformContinuousConstSMul A (V ⊗[A] W) :=
  uniformContinuousConstSMul_of_continuousConstSMul A (V ⊗[A] W)

section Extension

variable (A V W : Type*) [CommRing A] [TopologicalSpace A]
  [SeminormedAddCommGroup V] [Module A V]
  [SeminormedAddCommGroup W] [Module A W]

/-- **The completed product norm** on `V ⊗̂_A W`: the continuous extension of
`BanachModule.productSeminorm A V W` across `CompletedTensor.toCompletion`. -/
noncomputable def productNorm : CompletedTensor A V W → ℝ :=
  Completion.extension (productSeminorm A V W) ∘ equivCompletion A V W

end Extension

section SeminormedRing

variable {A V W : Type*} [SeminormedCommRing A]
  [SeminormedAddCommGroup V] [Module A V]
  [SeminormedAddCommGroup W] [Module A W]

/-- On the image of `V ⊗[A] W`, `productNorm` agrees with `productSeminorm` whenever the scalar
action on `V` is bounded. -/
theorem productNorm_toCompletion_of_norm_smul_le
    (hV : ∃ C : ℝ≥0, ∀ (a : A) (v : V), ‖a • v‖ ≤ C * ‖a‖ * ‖v‖) (u : V ⊗[A] W) :
    productNorm A V W (toCompletion A V W u) = productSeminorm A V W u := by
  simp only [productNorm, Function.comp_apply, equivCompletion_toCompletion]
  exact Completion.extension_coe (uniformContinuous_productSeminorm_of_norm_smul_le hV) u

/-- On the image of `V ⊗[A] W`, `productNorm` agrees with `productSeminorm`. -/
@[simp]
theorem productNorm_toCompletion [IsBoundedSMul A V] (u : V ⊗[A] W) :
    productNorm A V W (toCompletion A V W u) = productSeminorm A V W u :=
  productNorm_toCompletion_of_norm_smul_le ⟨1, fun a v ↦ by simpa using norm_smul_le a v⟩ u

/-- `productNorm A V W` is uniformly continuous. -/
theorem uniformContinuous_productNorm : UniformContinuous (productNorm A V W) :=
  Completion.uniformContinuous_extension.comp
    (equivCompletion A V W).toContinuousLinearMap.uniformContinuous

/-- `productNorm A V W` is continuous. -/
theorem continuous_productNorm : Continuous (productNorm A V W) :=
  uniformContinuous_productNorm.continuous

/-- `productNorm A V W` is nonnegative under a bounded scalar action on `V`. -/
theorem productNorm_nonneg_of_norm_smul_le
    (hV : ∃ C : ℝ≥0, ∀ (a : A) (v : V), ‖a • v‖ ≤ C * ‖a‖ * ‖v‖)
    (z : CompletedTensor A V W) : 0 ≤ productNorm A V W z :=
  (denseRange_toCompletion A V W).induction_on z
    (isClosed_le continuous_const continuous_productNorm) fun u ↦ by
      rw [productNorm_toCompletion_of_norm_smul_le hV]
      exact apply_nonneg _ u

/-- `productNorm A V W` is nonnegative. -/
theorem productNorm_nonneg [IsBoundedSMul A V] (z : CompletedTensor A V W) :
    0 ≤ productNorm A V W z :=
  productNorm_nonneg_of_norm_smul_le ⟨1, fun a v ↦ by simpa using norm_smul_le a v⟩ z

/-- `productNorm A V W` vanishes at `0` under a bounded scalar action on `V`. -/
theorem productNorm_zero_of_norm_smul_le
    (hV : ∃ C : ℝ≥0, ∀ (a : A) (v : V), ‖a • v‖ ≤ C * ‖a‖ * ‖v‖) :
    productNorm A V W 0 = 0 := by
  simpa using productNorm_toCompletion_of_norm_smul_le (W := W) hV 0

/-- `productNorm A V W` vanishes at `0`. -/
@[simp]
theorem productNorm_zero [IsBoundedSMul A V] : productNorm A V W 0 = 0 :=
  productNorm_zero_of_norm_smul_le ⟨1, fun a v ↦ by simpa using norm_smul_le a v⟩

/-- `productNorm A V W` is invariant under negation under a bounded scalar action on `V`. -/
theorem productNorm_neg_of_norm_smul_le
    (hV : ∃ C : ℝ≥0, ∀ (a : A) (v : V), ‖a • v‖ ≤ C * ‖a‖ * ‖v‖)
    (z : CompletedTensor A V W) :
    productNorm A V W (-z) = productNorm A V W z :=
  (denseRange_toCompletion A V W).induction_on z
    (isClosed_eq (continuous_productNorm.comp continuous_neg) continuous_productNorm) fun u ↦ by
      rw [← map_neg, productNorm_toCompletion_of_norm_smul_le hV,
        productNorm_toCompletion_of_norm_smul_le hV, map_neg_eq_map]

/-- `productNorm A V W` is invariant under negation. -/
@[simp]
theorem productNorm_neg [IsBoundedSMul A V] (z : CompletedTensor A V W) :
    productNorm A V W (-z) = productNorm A V W z :=
  productNorm_neg_of_norm_smul_le ⟨1, fun a v ↦ by simpa using norm_smul_le a v⟩ z

/-- **Ultrametric inequality** for `productNorm` under a bounded scalar action on `V`. -/
theorem productNorm_add_le_max_of_norm_smul_le
    (hV : ∃ C : ℝ≥0, ∀ (a : A) (v : V), ‖a • v‖ ≤ C * ‖a‖ * ‖v‖)
    (z₁ z₂ : CompletedTensor A V W) :
    productNorm A V W (z₁ + z₂) ≤ max (productNorm A V W z₁) (productNorm A V W z₂) := by
  refine (denseRange_toCompletion A V W).induction_on₂
    (p := fun z₁ z₂ ↦
      productNorm A V W (z₁ + z₂) ≤ max (productNorm A V W z₁) (productNorm A V W z₂))
    ?_ (fun u₁ u₂ ↦ ?_) z₁ z₂
  · exact isClosed_le (continuous_productNorm.comp continuous_add)
      ((continuous_productNorm.comp continuous_fst).max
        (continuous_productNorm.comp continuous_snd))
  · rw [← map_add, productNorm_toCompletion_of_norm_smul_le hV,
      productNorm_toCompletion_of_norm_smul_le hV,
      productNorm_toCompletion_of_norm_smul_le hV]
    exact productSeminorm_add_le_max u₁ u₂

/-- **Ultrametric inequality** for `productNorm`. -/
theorem productNorm_add_le_max [IsBoundedSMul A V] (z₁ z₂ : CompletedTensor A V W) :
    productNorm A V W (z₁ + z₂) ≤ max (productNorm A V W z₁) (productNorm A V W z₂) :=
  productNorm_add_le_max_of_norm_smul_le ⟨1, fun a v ↦ by simpa using norm_smul_le a v⟩ z₁ z₂

/-- Triangle inequality for `productNorm` under a bounded scalar action on `V`. -/
theorem productNorm_add_le_of_norm_smul_le
    (hV : ∃ C : ℝ≥0, ∀ (a : A) (v : V), ‖a • v‖ ≤ C * ‖a‖ * ‖v‖)
    (z₁ z₂ : CompletedTensor A V W) :
    productNorm A V W (z₁ + z₂) ≤ productNorm A V W z₁ + productNorm A V W z₂ :=
  (productNorm_add_le_max_of_norm_smul_le hV z₁ z₂).trans <|
    max_le_add_of_nonneg (productNorm_nonneg_of_norm_smul_le hV z₁)
      (productNorm_nonneg_of_norm_smul_le hV z₂)

/-- Triangle inequality for `productNorm`. -/
theorem productNorm_add_le [IsBoundedSMul A V] (z₁ z₂ : CompletedTensor A V W) :
    productNorm A V W (z₁ + z₂) ≤ productNorm A V W z₁ + productNorm A V W z₂ :=
  productNorm_add_le_of_norm_smul_le ⟨1, fun a v ↦ by simpa using norm_smul_le a v⟩ z₁ z₂

/-- Ultrametric bound for differences under `productNorm` under a bounded scalar action on `V`. -/
theorem productNorm_sub_le_max_of_norm_smul_le
    (hV : ∃ C : ℝ≥0, ∀ (a : A) (v : V), ‖a • v‖ ≤ C * ‖a‖ * ‖v‖)
    (z₁ z₂ : CompletedTensor A V W) :
    productNorm A V W (z₁ - z₂) ≤ max (productNorm A V W z₁) (productNorm A V W z₂) := by
  simpa [sub_eq_add_neg, productNorm_neg_of_norm_smul_le hV] using
    productNorm_add_le_max_of_norm_smul_le hV z₁ (-z₂)

/-- Ultrametric bound for differences under `productNorm`. -/
theorem productNorm_sub_le_max [IsBoundedSMul A V] (z₁ z₂ : CompletedTensor A V W) :
    productNorm A V W (z₁ - z₂) ≤ max (productNorm A V W z₁) (productNorm A V W z₂) :=
  productNorm_sub_le_max_of_norm_smul_le ⟨1, fun a v ↦ by simpa using norm_smul_le a v⟩ z₁ z₂

/-- Elementary-tensor bound for `productNorm` under a bounded scalar action on `V`. -/
theorem productNorm_tmul_le_of_norm_smul_le
    (hV : ∃ C : ℝ≥0, ∀ (a : A) (v : V), ‖a • v‖ ≤ C * ‖a‖ * ‖v‖) (v : V) (w : W) :
    productNorm A V W (tmul A V W v w) ≤ ‖v‖ * ‖w‖ := by
  rw [← toCompletion_tmul, productNorm_toCompletion_of_norm_smul_le hV]
  exact productSeminorm_tmul_le v w

/-- Elementary-tensor bound for `productNorm`. -/
theorem productNorm_tmul_le [IsBoundedSMul A V] (v : V) (w : W) :
    productNorm A V W (tmul A V W v w) ≤ ‖v‖ * ‖w‖ :=
  productNorm_tmul_le_of_norm_smul_le ⟨1, fun a v ↦ by simpa using norm_smul_le a v⟩ v w

/-- Scalar-action bound for `productNorm` under `‖a • v‖ ≤ C * ‖a‖ * ‖v‖`. -/
theorem productNorm_smul_le_of_norm_smul_le {C : ℝ≥0}
    (hV : ∀ (a : A) (v : V), ‖a • v‖ ≤ C * ‖a‖ * ‖v‖) (a : A) (z : CompletedTensor A V W) :
    productNorm A V W (a • z) ≤ C * ‖a‖ * productNorm A V W z :=
  (denseRange_toCompletion A V W).induction_on z
    (isClosed_le (continuous_productNorm.comp (continuous_const_smul a))
      (continuous_const.mul continuous_productNorm)) fun u ↦ by
      rw [← map_smul, productNorm_toCompletion_of_norm_smul_le ⟨C, hV⟩,
        productNorm_toCompletion_of_norm_smul_le ⟨C, hV⟩]
      exact productSeminorm_smul_le_of_norm_smul_le hV a u

/-- Scalar-action bound for `productNorm` under a contractive scalar action on `V`. -/
theorem productNorm_smul_le [IsBoundedSMul A V] (a : A) (z : CompletedTensor A V W) :
    productNorm A V W (a • z) ≤ ‖a‖ * productNorm A V W z := by
  simpa using productNorm_smul_le_of_norm_smul_le (C := 1)
    (fun r v ↦ by simpa using norm_smul_le r v) a z

/-- **Universal bound on the completion.** For an `A`-bilinear map `β : V →ₗ[A] W →ₗ[A] M` into a
complete ultrametric normed `A`-module with continuous action, bounded by `C * ‖v‖ * ‖w‖`
(`0 ≤ C`), the induced map `lift β` satisfies `‖lift β _ z‖ ≤ C * productNorm A V W z`. -/
theorem norm_lift_le_mul_productNorm_of_norm_smul_le
    (hV : ∃ C₀ : ℝ≥0, ∀ (a : A) (v : V), ‖a • v‖ ≤ C₀ * ‖a‖ * ‖v‖)
    {M : Type*} [NormedAddCommGroup M] [IsUltrametricDist M] [CompleteSpace M]
    [Module A M] [ContinuousSMul A M] (β : V →ₗ[A] W →ₗ[A] M)
    (hβ : Continuous fun p : V × W ↦ β p.1 p.2) {C : ℝ} (hC : 0 ≤ C)
    (h : ∀ v w, ‖β v w‖ ≤ C * ‖v‖ * ‖w‖) (z : CompletedTensor A V W) :
    ‖lift β hβ z‖ ≤ C * productNorm A V W z :=
  (denseRange_toCompletion A V W).induction_on z
    (isClosed_le (continuous_norm.comp (lift β hβ).continuous)
      (continuous_const.mul continuous_productNorm)) fun u ↦ by
      rw [lift_toCompletion, productNorm_toCompletion_of_norm_smul_le hV]
      exact norm_lift_le_mul_productSeminorm β hC h u

/-- **Universal bound on the completion** under a contractive scalar action on `V`. -/
theorem norm_lift_le_mul_productNorm [IsBoundedSMul A V]
    {M : Type*} [NormedAddCommGroup M] [IsUltrametricDist M] [CompleteSpace M]
    [Module A M] [ContinuousSMul A M] (β : V →ₗ[A] W →ₗ[A] M)
    (hβ : Continuous fun p : V × W ↦ β p.1 p.2) {C : ℝ} (hC : 0 ≤ C)
    (h : ∀ v w, ‖β v w‖ ≤ C * ‖v‖ * ‖w‖) (z : CompletedTensor A V W) :
    ‖lift β hβ z‖ ≤ C * productNorm A V W z :=
  norm_lift_le_mul_productNorm_of_norm_smul_le
    ⟨1, fun a v ↦ by simpa using norm_smul_le a v⟩ β hβ hC h z

/-- `CompletedTensor.map` extends `TensorProduct.map` across `toCompletion`. -/
@[simp]
theorem map_toCompletion {V' W' : Type*} [SeminormedAddCommGroup V'] [Module A V']
    [SeminormedAddCommGroup W'] [Module A W'] (f : V →L[A] V') (g : W →L[A] W')
    (u : V ⊗[A] W) :
    map f g (toCompletion A V W u) =
      toCompletion A V' W' (TensorProduct.map f.toLinearMap g.toLinearMap u) := by
  induction u using TensorProduct.inductionOn with
  | tmul v w => simp
  | add x y hx hy => simp only [map_add, hx, hy]

/-- Functoriality bound for `productNorm` under bounded continuous `A`-linear maps. -/
theorem productNorm_map_le_of_norm_smul_le {V' W' : Type*}
    [SeminormedAddCommGroup V'] [Module A V'] [SeminormedAddCommGroup W'] [Module A W']
    (hV : ∃ C : ℝ≥0, ∀ (a : A) (v : V), ‖a • v‖ ≤ C * ‖a‖ * ‖v‖)
    (hV' : ∃ C : ℝ≥0, ∀ (a : A) (v : V'), ‖a • v‖ ≤ C * ‖a‖ * ‖v‖)
    (f : V →L[A] V') (g : W →L[A] W') {C₁ C₂ : ℝ}
    (hC₁ : 0 ≤ C₁) (hf : ∀ v, ‖f v‖ ≤ C₁ * ‖v‖) (hC₂ : 0 ≤ C₂) (hg : ∀ w, ‖g w‖ ≤ C₂ * ‖w‖)
    (z : CompletedTensor A V W) :
    productNorm A V' W' (map f g z) ≤ C₁ * C₂ * productNorm A V W z :=
  (denseRange_toCompletion A V W).induction_on z
    (isClosed_le (continuous_productNorm.comp (map f g).continuous)
      (continuous_const.mul continuous_productNorm)) fun u ↦ by
      rw [map_toCompletion, productNorm_toCompletion_of_norm_smul_le hV',
        productNorm_toCompletion_of_norm_smul_le hV]
      exact productSeminorm_map_le f.toLinearMap g.toLinearMap hC₁ hf hC₂ hg u

/-- Functoriality bound for `productNorm` under contractive scalar actions on `V` and `V'`. -/
theorem productNorm_map_le {V' W' : Type*}
    [SeminormedAddCommGroup V'] [Module A V'] [IsBoundedSMul A V']
    [SeminormedAddCommGroup W'] [Module A W'] [IsBoundedSMul A V]
    (f : V →L[A] V') (g : W →L[A] W') {C₁ C₂ : ℝ}
    (hC₁ : 0 ≤ C₁) (hf : ∀ v, ‖f v‖ ≤ C₁ * ‖v‖) (hC₂ : 0 ≤ C₂) (hg : ∀ w, ‖g w‖ ≤ C₂ * ‖w‖)
    (z : CompletedTensor A V W) :
    productNorm A V' W' (map f g z) ≤ C₁ * C₂ * productNorm A V W z :=
  productNorm_map_le_of_norm_smul_le
    ⟨1, fun a v ↦ by simpa using norm_smul_le a v⟩
    ⟨1, fun a v ↦ by simpa using norm_smul_le a v⟩ f g hC₁ hf hC₂ hg z

/-- On `A ⊗̂_A W` with `‖1‖ = 1` and complete ultrametric normed `W` with contractive `A`-action,
`productNorm` is the norm of the image under `CompletedTensor.lid A W`. -/
@[simp]
theorem productNorm_eq_norm_lid [NormOneClass A]
    {M : Type*} [NormedAddCommGroup M] [IsUltrametricDist M] [CompleteSpace M]
    [Module A M] [IsBoundedSMul A M] (z : CompletedTensor A A M) :
    productNorm A A M z = ‖lid A M z‖ :=
  (denseRange_toCompletion A A M).induction_on z
    (isClosed_eq continuous_productNorm (continuous_norm.comp (lid A M).continuous)) fun u ↦ by
      rw [productNorm_toCompletion, lid_toCompletion, productSeminorm_eq_norm_lid]

end SeminormedRing

section NormedField

variable {L V W : Type*} [NormedField L]
  [SeminormedAddCommGroup V] [NormedSpace L V]
  [SeminormedAddCommGroup W] [NormedSpace L W]

/-- Over a normed field, `productNorm` is homogeneous under scalar multiplication. -/
@[simp]
theorem productNorm_smul (a : L) (z : CompletedTensor L V W) :
    productNorm L V W (a • z) = ‖a‖ * productNorm L V W z := by
  rcases eq_or_ne a 0 with rfl | ha
  · simp
  · refine (productNorm_smul_le a z).antisymm ?_
    calc ‖a‖ * productNorm L V W z
        = ‖a‖ * productNorm L V W (a⁻¹ • a • z) := by rw [inv_smul_smul₀ ha]
      _ ≤ ‖a‖ * (‖a⁻¹‖ * productNorm L V W (a • z)) :=
          mul_le_mul_of_nonneg_left (productNorm_smul_le a⁻¹ (a • z)) (norm_nonneg a)
      _ = productNorm L V W (a • z) := by
          rw [norm_inv, ← mul_assoc, mul_inv_cancel₀ (norm_ne_zero_iff.mpr ha), one_mul]

end NormedField

section IsTate

variable {A V W : Type*} [SeminormedCommRing A] [NormedRing.IsTate A]
  [SeminormedAddCommGroup V] [Module A V]
  [SeminormedAddCommGroup W] [Module A W]

/-- **Neighbourhood basis on the completion.** Over a Tate seminormed commutative ring `A` with
bounded scalar actions on `V` and `W`, the positive-radius open balls of `productNorm A V W` form a
neighbourhood basis of `0` in `CompletedTensor A V W`. -/
theorem hasBasis_nhds_zero_productNorm_of_norm_smul_le
    (hV : ∃ C : ℝ≥0, ∀ (a : A) (v : V), ‖a • v‖ ≤ C * ‖a‖ * ‖v‖)
    (hW : ∃ C : ℝ≥0, ∀ (a : A) (w : W), ‖a • w‖ ≤ C * ‖a‖ * ‖w‖) :
    (𝓝 (0 : CompletedTensor A V W)).HasBasis (0 < ·)
      (fun r ↦ {z | productNorm A V W z < r}) := by
  have hb_gen : ∀ (u : UniformSpace (V ⊗[A] W)),
      u = (productSeminorm A V W).toSeminormedAddCommGroup.toUniformSpace →
      (@nhds (@Completion (V ⊗[A] W) u)
          (@UniformSpace.toTopologicalSpace _ (@Completion.uniformSpace _ u))
          (@Completion.coe' (V ⊗[A] W) u 0)).HasBasis (0 < ·)
        (fun r ↦ {z | @Completion.extension (V ⊗[A] W) u ℝ _ (productSeminorm A V W) z < r}) := by
    rintro _ rfl
    let _ : SeminormedAddCommGroup (V ⊗[A] W) := (productSeminorm A V W).toSeminormedAddCommGroup
    exact NormedAddGroup.nhds_zero_basis_norm_lt
  have hb := hb_gen (banachTensorUniformSpace A V W)
    (banachTensorUniformSpace_eq_productSeminorm_of_norm_smul_le hV hW)
  have heq : 𝓝 (0 : CompletedTensor A V W) =
      Filter.comap (equivCompletion A V W) (𝓝 (0 : Completion (V ⊗[A] W))) := by
    simpa using (equivCompletion A V W).toHomeomorph.isInducing.nhds_eq_comap 0
  rw [heq]
  exact hb.comap (equivCompletion A V W)

variable (A V W) in
/-- **Neighbourhood basis on the completion** under contractive scalar actions. -/
theorem hasBasis_nhds_zero_productNorm [IsBoundedSMul A V] [IsBoundedSMul A W] :
    (𝓝 (0 : CompletedTensor A V W)).HasBasis (0 < ·)
      (fun r ↦ {z | productNorm A V W z < r}) :=
  hasBasis_nhds_zero_productNorm_of_norm_smul_le
    ⟨1, fun a v ↦ by simpa using norm_smul_le a v⟩
    ⟨1, fun a w ↦ by simpa using norm_smul_le a w⟩

/-- **Definiteness of `productNorm`** over a Tate seminormed commutative ring with bounded scalar
actions. -/
theorem productNorm_eq_zero_iff_of_norm_smul_le
    (hV : ∃ C : ℝ≥0, ∀ (a : A) (v : V), ‖a • v‖ ≤ C * ‖a‖ * ‖v‖)
    (hW : ∃ C : ℝ≥0, ∀ (a : A) (w : W), ‖a • w‖ ≤ C * ‖a‖ * ‖w‖)
    {z : CompletedTensor A V W} :
    productNorm A V W z = 0 ↔ z = 0 := by
  have hdef_gen : ∀ (u : UniformSpace (V ⊗[A] W)),
      u = (productSeminorm A V W).toSeminormedAddCommGroup.toUniformSpace →
      ∀ w : @Completion (V ⊗[A] W) u,
        @Completion.extension (V ⊗[A] W) u ℝ _ (productSeminorm A V W) w = 0 ↔
          w = @Completion.coe' (V ⊗[A] W) u 0 := by
    rintro _ rfl
    let inst : SeminormedAddCommGroup (V ⊗[A] W) :=
      (productSeminorm A V W).toSeminormedAddCommGroup
    exact fun w ↦ @norm_eq_zero (@Completion (V ⊗[A] W) inst.toUniformSpace) inferInstance w
  have hdef := hdef_gen (banachTensorUniformSpace A V W)
    (banachTensorUniformSpace_eq_productSeminorm_of_norm_smul_le hV hW)
    (equivCompletion A V W z)
  simpa only [productNorm, Function.comp_apply, UniformSpace.Completion.coe_zero,
    map_eq_zero_iff _ (equivCompletion A V W).injective] using hdef

/-- **Definiteness of `productNorm`** under contractive scalar actions. -/
@[simp]
theorem productNorm_eq_zero_iff [IsBoundedSMul A V] [IsBoundedSMul A W]
    {z : CompletedTensor A V W} :
    productNorm A V W z = 0 ↔ z = 0 :=
  productNorm_eq_zero_iff_of_norm_smul_le
    ⟨1, fun a v ↦ by simpa using norm_smul_le a v⟩
    ⟨1, fun a w ↦ by simpa using norm_smul_le a w⟩

/-- `productNorm A V W` bundled as an `AddGroupNorm` under bounded scalar actions over a Tate
seminormed commutative ring. -/
noncomputable def productAddGroupNormOfNormSmulLe
    (hV : ∃ C : ℝ≥0, ∀ (a : A) (v : V), ‖a • v‖ ≤ C * ‖a‖ * ‖v‖)
    (hW : ∃ C : ℝ≥0, ∀ (a : A) (w : W), ‖a • w‖ ≤ C * ‖a‖ * ‖w‖) :
    AddGroupNorm (CompletedTensor A V W) where
  toFun := productNorm A V W
  map_zero' := productNorm_zero_of_norm_smul_le hV
  add_le' := productNorm_add_le_of_norm_smul_le hV
  neg' := productNorm_neg_of_norm_smul_le hV
  eq_zero_of_map_eq_zero' _ hz := (productNorm_eq_zero_iff_of_norm_smul_le hV hW).mp hz

/-- Evaluation of `productAddGroupNormOfNormSmulLe`. -/
@[simp]
theorem productAddGroupNormOfNormSmulLe_apply
    (hV : ∃ C : ℝ≥0, ∀ (a : A) (v : V), ‖a • v‖ ≤ C * ‖a‖ * ‖v‖)
    (hW : ∃ C : ℝ≥0, ∀ (a : A) (w : W), ‖a • w‖ ≤ C * ‖a‖ * ‖w‖)
    (z : CompletedTensor A V W) :
    productAddGroupNormOfNormSmulLe hV hW z = productNorm A V W z :=
  (rfl)

variable (A V W) in
/-- `productNorm A V W` bundled as an `AddGroupNorm` under contractive scalar actions over a Tate
seminormed commutative ring. -/
noncomputable def productAddGroupNorm [IsBoundedSMul A V] [IsBoundedSMul A W] :
    AddGroupNorm (CompletedTensor A V W) :=
  productAddGroupNormOfNormSmulLe
    ⟨1, fun a v ↦ by simpa using norm_smul_le a v⟩
    ⟨1, fun a w ↦ by simpa using norm_smul_le a w⟩

/-- Evaluation of `productAddGroupNorm`. -/
@[simp]
theorem productAddGroupNorm_apply [IsBoundedSMul A V] [IsBoundedSMul A W]
    (z : CompletedTensor A V W) :
    productAddGroupNorm A V W z = productNorm A V W z :=
  (rfl)

/-- The uniformity of `CompletedTensor A V W` coincides with that induced by
`productAddGroupNormOfNormSmulLe`. -/
theorem uniformity_eq_productAddGroupNormOfNormSmulLe
    (hV : ∃ C : ℝ≥0, ∀ (a : A) (v : V), ‖a • v‖ ≤ C * ‖a‖ * ‖v‖)
    (hW : ∃ C : ℝ≥0, ∀ (a : A) (w : W), ‖a • w‖ ≤ C * ‖a‖ * ‖w‖) :
    𝓤 (CompletedTensor A V W) =
      @uniformity _
        (productAddGroupNormOfNormSmulLe hV hW).toNormedAddCommGroup.toUniformSpace := by
  let N := productAddGroupNormOfNormSmulLe hV hW
  let u₁ : UniformSpace (CompletedTensor A V W) := inferInstance
  have hu₁ : @IsUniformAddGroup (CompletedTensor A V W) u₁ _ := inferInstance
  have hb₁ := hasBasis_nhds_zero_productNorm_of_norm_smul_le hV hW
  let _ : NormedAddCommGroup (CompletedTensor A V W) := N.toNormedAddCommGroup
  have hu : u₁ = N.toNormedAddCommGroup.toUniformSpace :=
    IsUniformAddGroup.ext hu₁ inferInstance
      (hb₁.eq_of_same_basis NormedAddGroup.nhds_zero_basis_norm_lt)
  exact congrArg (fun u ↦ @uniformity _ u) hu

variable (A V W) in
/-- The uniformity of `CompletedTensor A V W` coincides with that induced by
`productAddGroupNorm` under contractive scalar actions. -/
theorem uniformity_eq_productAddGroupNorm [IsBoundedSMul A V] [IsBoundedSMul A W] :
    𝓤 (CompletedTensor A V W) =
      @uniformity _ (productAddGroupNorm A V W).toNormedAddCommGroup.toUniformSpace :=
  uniformity_eq_productAddGroupNormOfNormSmulLe
    ⟨1, fun a v ↦ by simpa using norm_smul_le a v⟩
    ⟨1, fun a w ↦ by simpa using norm_smul_le a w⟩

/-- Compatible `NormedAddCommGroup` structure on `CompletedTensor A V W` whose norm is
`productNorm A V W` and whose uniformity and topology are definitionally the existing ones. -/
noncomputable abbrev productNormedAddCommGroupOfNormSmulLe
    (hV : ∃ C : ℝ≥0, ∀ (a : A) (v : V), ‖a • v‖ ≤ C * ‖a‖ * ‖v‖)
    (hW : ∃ C : ℝ≥0, ∀ (a : A) (w : W), ‖a • w‖ ≤ C * ‖a‖ * ‖w‖) :
    NormedAddCommGroup (CompletedTensor A V W) :=
  let N := productAddGroupNormOfNormSmulLe hV hW
  { N.toNormedAddCommGroup with
    toMetricSpace := N.toNormedAddCommGroup.toMetricSpace.replaceUniformity
      (uniformity_eq_productAddGroupNormOfNormSmulLe hV hW) }

variable (A V W) in
/-- Compatible `NormedAddCommGroup` structure on `CompletedTensor A V W` under contractive scalar
actions, retaining its uniformity and topology definitionally. -/
noncomputable abbrev productNormedAddCommGroup [IsBoundedSMul A V] [IsBoundedSMul A W] :
    NormedAddCommGroup (CompletedTensor A V W) :=
  productNormedAddCommGroupOfNormSmulLe
    ⟨1, fun a v ↦ by simpa using norm_smul_le a v⟩
    ⟨1, fun a w ↦ by simpa using norm_smul_le a w⟩

end IsTate

end CompletedTensor

section CompleteField

variable {L V W : Type*} [NontriviallyNormedField L] [CompleteSpace L]
  [NormedAddCommGroup V] [IsUltrametricDist V] [NormedSpace L V]
  [NormedAddCommGroup W] [IsUltrametricDist W] [NormedSpace L W]

/-- Any continuous linear functional on a finite-dimensional subspace `E₀ ≤ V` extends to an
`L`-linear functional on `V` whose norm on a given finite set `S ⊆ V` is at most `c * ‖φ₀‖`. -/
private theorem exists_linearMap_comp_subtype_eq_of_finite (E₀ : Submodule L V)
    [FiniteDimensional L E₀] (φ₀ : StrongDual L E₀) {S : Set V} (hS : S.Finite)
    {c : ℝ} (hc : 1 < c) :
    ∃ ψ : V →ₗ[L] L, ψ.comp E₀.subtype = φ₀.toLinearMap ∧
      ∀ x ∈ S, ‖ψ x‖ ≤ c * ‖φ₀‖ * ‖x‖ := by
  let E' : Submodule L V := E₀ ⊔ Submodule.span L S
  have : FiniteDimensional L E' :=
    have := FiniteDimensional.span_of_finite L hS
    Submodule.finiteDimensional_sup E₀ _
  let D : Submodule L E' := E₀.comap E'.subtype
  let e : D ≃ₗ[L] E₀ := Submodule.comapSubtypeEquivOfLe le_sup_left
  obtain ⟨p, hp_id, hp_norm⟩ := D.exists_projection_norm_le hc
  obtain ⟨π, hπ⟩ := E'.subtype.exists_leftInverse_of_injective E'.ker_subtype
  let ψ : V →ₗ[L] L := φ₀.toLinearMap.comp (e.toLinearMap.comp (p.toLinearMap.comp π))
  refine ⟨ψ, ?_, fun x hxS ↦ ?_⟩
  · ext x
    have hxE' : (x : V) ∈ E' := Submodule.mem_sup_left x.2
    have hπx : π (x : V) = ⟨(x : V), hxE'⟩ := LinearMap.congr_fun hπ ⟨(x : V), hxE'⟩
    have hpx : p ⟨(x : V), hxE'⟩ = ⟨⟨(x : V), hxE'⟩, x.2⟩ := hp_id ⟨⟨(x : V), hxE'⟩, x.2⟩
    have hex : e ⟨⟨(x : V), hxE'⟩, x.2⟩ = x := Subtype.ext rfl
    simp [ψ, hπx, hpx, hex]
  · have hxE' : x ∈ E' := Submodule.mem_sup_right (Submodule.subset_span hxS)
    have hπx : π x = ⟨x, hxE'⟩ := LinearMap.congr_fun hπ ⟨x, hxE'⟩
    have hnorm_e : ‖e (p ⟨x, hxE'⟩)‖ = ‖(p ⟨x, hxE'⟩ : E')‖ := rfl
    calc ‖ψ x‖ = ‖φ₀ (e (p ⟨x, hxE'⟩))‖ := by simp [ψ, hπx]
      _ ≤ ‖φ₀‖ * ‖(p ⟨x, hxE'⟩ : E')‖ := hnorm_e ▸ φ₀.le_opNorm _
      _ ≤ ‖φ₀‖ * (c * ‖x‖) := mul_le_mul_of_nonneg_left (hp_norm ⟨x, hxE'⟩) (norm_nonneg φ₀)
      _ = c * ‖φ₀‖ * ‖x‖ := by ring

private theorem norm_lid_map_le_mul_productSeminorm_of_one_lt (E₀ : Submodule L V)
    [FiniteDimensional L E₀] (φ₀ : StrongDual L E₀) (u₀ : E₀ ⊗[L] W) {c : ℝ} (hc : 1 < c) :
    ‖TensorProduct.lid L W (TensorProduct.map φ₀.toLinearMap LinearMap.id u₀)‖ ≤
      c * ‖φ₀‖ * productSeminorm L V W (TensorProduct.map E₀.subtype LinearMap.id u₀) := by
  have hmul0 : 0 ≤ c * ‖φ₀‖ := mul_nonneg (zero_lt_one.trans hc).le (norm_nonneg φ₀)
  set u := TensorProduct.map E₀.subtype LinearMap.id u₀
  rw [productSeminorm_apply, ← smul_eq_mul, ← Real.sInf_smul_of_nonneg hmul0]
  refine le_csInf (costs_nonempty u).smul_set ?_
  rintro _ ⟨_, ⟨n, v, w, hvw, rfl⟩, rfl⟩
  dsimp only
  rw [smul_eq_mul]
  set b : ℝ := ((Finset.univ.sup fun j ↦ ‖v j‖₊ * ‖w j‖₊ : ℝ≥0) : ℝ)
  obtain ⟨ψ, hψ_comp, hψ_norm⟩ :=
    exists_linearMap_comp_subtype_eq_of_finite E₀ φ₀ (Set.finite_range v) hc
  have hmap : TensorProduct.map φ₀.toLinearMap (LinearMap.id : W →ₗ[L] W) u₀ =
      TensorProduct.map ψ LinearMap.id (∑ j, v j ⊗ₜ[L] w j) := by
    rw [hvw, ← LinearMap.comp_apply, ← TensorProduct.map_comp, hψ_comp, LinearMap.id_comp]
  rw [hmap, map_sum, map_sum]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg
    (mul_nonneg hmul0 (NNReal.coe_nonneg _)) fun j _ ↦ ?_
  have hvw_le : ‖v j‖ * ‖w j‖ ≤ b := by
    exact_mod_cast Finset.le_sup (f := fun i ↦ ‖v i‖₊ * ‖w i‖₊) (Finset.mem_univ j)
  simp only [TensorProduct.map_tmul, LinearMap.id_apply, TensorProduct.lid_tmul, norm_smul]
  calc ‖ψ (v j)‖ * ‖w j‖ ≤ (c * ‖φ₀‖ * ‖v j‖) * ‖w j‖ :=
        mul_le_mul_of_nonneg_right (hψ_norm (v j) (Set.mem_range_self j)) (norm_nonneg (w j))
    _ = c * ‖φ₀‖ * (‖v j‖ * ‖w j‖) := by ring
    _ ≤ c * ‖φ₀‖ * b := mul_le_mul_of_nonneg_left hvw_le hmul0

/-- Contracting a tensor in `E₀ ⊗[L] W` (`E₀ ≤ V` finite-dimensional) with a continuous linear
functional `φ₀ : StrongDual L E₀` has norm at most `‖φ₀‖` times the `V ⊗[L] W`-product seminorm of
its image. -/
theorem norm_lid_map_le_productSeminorm (E₀ : Submodule L V) [FiniteDimensional L E₀]
    (φ₀ : StrongDual L E₀) (u₀ : E₀ ⊗[L] W) :
    ‖TensorProduct.lid L W (TensorProduct.map φ₀.toLinearMap LinearMap.id u₀)‖ ≤
      ‖φ₀‖ * productSeminorm L V W (TensorProduct.map E₀.subtype LinearMap.id u₀) := by
  set B := ‖φ₀‖ * productSeminorm L V W (TensorProduct.map E₀.subtype LinearMap.id u₀)
  have hB : 0 ≤ B := mul_nonneg (norm_nonneg φ₀) (apply_nonneg _ _)
  refine le_of_forall_pos_lt_add fun ε hε ↦ ?_
  have hB1 : 0 < B + 1 := add_pos_of_nonneg_of_pos hB zero_lt_one
  have hc : 1 < 1 + ε / (B + 1) := lt_add_of_pos_right 1 (div_pos hε hB1)
  calc ‖TensorProduct.lid L W (TensorProduct.map φ₀.toLinearMap LinearMap.id u₀)‖
      ≤ (1 + ε / (B + 1)) * B := by
        simpa only [B, mul_assoc] using
          norm_lid_map_le_mul_productSeminorm_of_one_lt E₀ φ₀ u₀ hc
    _ = B + ε * (B / (B + 1)) := by ring
    _ < B + ε * 1 := by gcongr; exact (div_lt_one hB1).mpr (lt_add_one B)
    _ = B + ε := by ring

/-- **Cross-norm theorem for `productSeminorm`.** Over a complete nontrivially normed field, on
ultrametric normed spaces `V` and `W`, the product seminorm of an elementary tensor `v ⊗ₜ w` is
`‖v‖ * ‖w‖`. -/
@[simp]
theorem productSeminorm_tmul (v : V) (w : W) :
    productSeminorm L V W (v ⊗ₜ[L] w) = ‖v‖ * ‖w‖ := by
  refine (productSeminorm_tmul_le v w).antisymm ?_
  rcases eq_or_ne v 0 with rfl | hv
  · simp
  set P := productSeminorm L V W (v ⊗ₜ[L] w)
  have hP : 0 ≤ P := apply_nonneg _ _
  refine le_of_forall_pos_lt_add fun ε hε ↦ ?_
  have hP1 : 0 < P + 1 := add_pos_of_nonneg_of_pos hP zero_lt_one
  set c : ℝ := 1 + ε / (P + 1)
  have hc : 1 < c := lt_add_of_pos_right 1 (div_pos hε hP1)
  let E₀ : Submodule L V := L ∙ v
  have : FiniteDimensional L E₀ := FiniteDimensional.span_of_finite L (Set.finite_singleton v)
  let v₀ : E₀ := ⟨v, Submodule.mem_span_singleton_self v⟩
  have hv₀ : v₀ ≠ 0 := fun h0 ↦ hv (congrArg Subtype.val h0)
  obtain ⟨φ₀, hφ₀v, hφ₀⟩ :=
    TauCeti.exists_strongDual_apply_eq_one_of_finiteDimensional (K := L) hv₀ hc
  have hφ₀_norm : ‖φ₀‖ ≤ c / ‖v‖ :=
    φ₀.opNorm_le_bound (div_nonneg (zero_lt_one.trans hc).le (norm_nonneg v)) fun x ↦ by
      rw [div_mul_eq_mul_div, le_div_iff₀ (norm_pos_iff.mpr hv)]
      exact hφ₀ x
  have hle : ‖w‖ ≤ ‖φ₀‖ * P := by
    simpa [P, v₀, hφ₀v] using norm_lid_map_le_productSeminorm E₀ φ₀ (v₀ ⊗ₜ[L] w)
  have hvw : ‖v‖ * ‖w‖ ≤ c * P := by
    have hle' : ‖w‖ ≤ (c / ‖v‖) * P := hle.trans (mul_le_mul_of_nonneg_right hφ₀_norm hP)
    rw [div_mul_eq_mul_div, le_div_iff₀ (norm_pos_iff.mpr hv)] at hle'
    linarith
  calc ‖v‖ * ‖w‖ ≤ (1 + ε / (P + 1)) * P := hvw
    _ = P + ε * (P / (P + 1)) := by ring
    _ < P + ε * 1 := by gcongr; exact (div_lt_one hP1).mpr (lt_add_one P)
    _ = P + ε := by ring

/-- **Definiteness of `productSeminorm`.** Over a complete nontrivially normed field, on
ultrametric normed spaces `V` and `W`, `productSeminorm L V W` vanishes only at `0`. -/
@[simp]
theorem productSeminorm_eq_zero_iff {u : V ⊗[L] W} :
    productSeminorm L V W u = 0 ↔ u = 0 := by
  refine ⟨fun h0 ↦ ?_, fun h ↦ h ▸ map_zero _⟩
  obtain ⟨m, x, y, hxysum⟩ := TensorProduct.exists_sum_tmul_eq u
  let E₀ : Submodule L V := Submodule.span L (Set.range x)
  have : FiniteDimensional L E₀ := FiniteDimensional.span_of_finite L (Set.finite_range x)
  let b₀ := Module.finBasis L E₀
  have hmem (i : Fin m) : x i ∈ E₀ := Submodule.subset_span (Set.mem_range_self i)
  let z : Fin (Module.finrank L E₀) → W := fun k ↦ ∑ i, b₀.repr ⟨x i, hmem i⟩ k • y i
  let u₀ : E₀ ⊗[L] W := ∑ k, b₀ k ⊗ₜ[L] z k
  have hu₀_map : TensorProduct.map E₀.subtype LinearMap.id u₀ = u := by
    rw [hxysum]
    have hxi (i : Fin m) : x i = ∑ k, b₀.repr ⟨x i, hmem i⟩ k • (b₀ k : V) := by
      simpa only [Submodule.coe_subtype, map_sum, map_smul] using
        congrArg E₀.subtype (b₀.sum_repr ⟨x i, hmem i⟩).symm
    simp only [u₀, map_sum, TensorProduct.map_tmul, Submodule.subtype_apply, LinearMap.id_apply]
    simp only [z, TensorProduct.tmul_sum, tmul_smul, smul_tmul']
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [← TensorProduct.sum_tmul, ← hxi i]
  have hz0 (k : Fin (Module.finrank L E₀)) : z k = 0 := by
    have hle := norm_lid_map_le_productSeminorm E₀ (b₀.coord k).toContinuousLinearMap u₀
    rw [hu₀_map, h0, mul_zero] at hle
    have hlhs : TensorProduct.lid L W
        (TensorProduct.map ((b₀.coord k).toContinuousLinearMap).toLinearMap LinearMap.id u₀) =
        z k := by
      simp [u₀, Module.Basis.coord_apply, Finsupp.single_apply, eq_comm]
    rw [hlhs] at hle
    exact norm_le_zero_iff.mp hle
  simp [← hu₀_map, u₀, hz0]

namespace CompletedTensor

variable (L V W) in
/-- **Injectivity of `toCompletion` over a complete nonarchimedean field** (Kedlaya–Liu Lemma
2.2.9(a)): for ultrametric normed `L`-spaces `V` and `W`, the canonical map
`V ⊗[L] W → V ⊗̂_L W` is injective. -/
theorem toCompletion_injective : Function.Injective (toCompletion L V W) :=
  (injective_iff_map_eq_zero (toCompletion L V W)).mpr fun u hu ↦ by
    have h0 : productSeminorm L V W u = 0 := by
      rw [← productNorm_toCompletion, hu, productNorm_zero]
    exact productSeminorm_eq_zero_iff.mp h0

/-- Equality after `toCompletion L V W` over a complete nonarchimedean field reduces to equality in
`V ⊗[L] W`. -/
@[simp]
theorem toCompletion_inj {u u' : V ⊗[L] W} :
    toCompletion L V W u = toCompletion L V W u' ↔ u = u' :=
  (toCompletion_injective L V W).eq_iff

/-- Over a complete nonarchimedean field, `toCompletion L V W u = 0` iff `u = 0`. -/
@[simp]
theorem toCompletion_eq_zero {u : V ⊗[L] W} :
    toCompletion L V W u = 0 ↔ u = 0 :=
  map_eq_zero_iff _ (toCompletion_injective L V W)

/-- **Cross-norm theorem for `productNorm`.** Over a complete nontrivially normed field, on
ultrametric normed `L`-spaces `V` and `W`, the completed product norm of `v ⊗ w` is `‖v‖ * ‖w‖`. -/
@[simp]
theorem productNorm_tmul (v : V) (w : W) :
    productNorm L V W (tmul L V W v w) = ‖v‖ * ‖w‖ := by
  rw [← toCompletion_tmul, productNorm_toCompletion, productSeminorm_tmul]

/-- Distance between elementary tensors sharing the second factor under `productNorm`. -/
theorem productNorm_tmul_sub_tmul_right (v v' : V) (w : W) :
    productNorm L V W (tmul L V W v w - tmul L V W v' w) = ‖v - v'‖ * ‖w‖ := by
  rw [← LinearMap.map_sub₂, productNorm_tmul]

/-- Distance between elementary tensors sharing the first factor under `productNorm`. -/
theorem productNorm_tmul_sub_tmul_left (v : V) (w w' : W) :
    productNorm L V W (tmul L V W v w - tmul L V W v w') = ‖v‖ * ‖w - w'‖ := by
  rw [← map_sub, productNorm_tmul]

/-- Tensoring on the right with a unit vector is isometric for `productNorm`. -/
theorem productNorm_unitVector (v v' : V) {w : W} (hw : ‖w‖ = 1) :
    productNorm L V W (tmul L V W v w - tmul L V W v' w) = ‖v - v'‖ := by
  rw [productNorm_tmul_sub_tmul_right, hw, mul_one]

end CompletedTensor

end CompleteField

end BanachModule

end TauCeti.Huber
