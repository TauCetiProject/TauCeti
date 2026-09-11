/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RepresentationTheory.Subrepresentation
public import TauCeti.RepresentationTheory.ClassicalGroups.BrauerGenerators.Orthogonal
import Mathlib.RepresentationTheory.Submodule
import Mathlib.Tactic.FinCases

/-!
# Contractions and the harmonic tensors

The coordinate dot product on `V = kⁿ` is a cap `V ⊗ V → k`
(`TauCeti.orthogonalCap`).  Applied to two of the `d` slots of `V^{⊗d}` it contracts them away and
leaves a tensor of rank `d - 2`: the **contraction**, or trace, map.  A tensor killed by every one
of them is **harmonic**, or traceless, and the harmonic tensors are the submodule
`TauCeti.harmonicTensors`.  They are the orthogonal-group half of the classical Schur-Weyl
picture over `ℂ`: there the irreducible `O(V)`-modules are cut out of the tensor power by a Young
symmetrizer for a partition with at most `n` boxes in its first two columns *and* the vanishing of
every trace, and the cups rebuild the non-harmonic part from lower tensor powers.  None of that is
proved here; this file builds the traces, the submodule they cut out, and its stability under the
two group actions.

A pair of slots is presented here not as a pair of indices but as an equivalence
`σ : Fin d ≃ Fin m ⊕ Fin 2`: the two slots to be capped are the ones `σ` names `Sum.inr 0` and
`Sum.inr 1`, and the surviving slots are relabelled by `Fin m` in the order `σ` chooses.  This
carries the arithmetic `d = m + 2` in the existence of `σ` rather than in a truncated subtraction,
and it makes the contraction a composite of maps already in Mathlib: reindex along `σ`, split the
tensor power along the sum (`PiTensorProduct.tmulEquiv`), cap the second factor.  Relabelling the
surviving slots and swapping the two capped slots change the contraction by a permutation of the
tensor factors and so do not change its kernel
(`TauCeti.ker_orthogonalContract_trans_sumCongr`), which is why quantifying over all such `σ` —
rather than over the unordered pairs of slots — defines the same submodule.

Two degenerate readings pin the definition.  Below two slots there is nothing to contract, so
every tensor is harmonic (`TauCeti.harmonicTensors_eq_top_of_lt_two`); on the tensor square there
is essentially one contraction, the cap itself, so the harmonic tensors are exactly its kernel
(`TauCeti.harmonicTensors_two`).  The latter is not vacuous: `eᵢ ⊗ eᵢ` has trace `1`, so over a
nontrivial ring the tensor square has non-harmonic vectors in every positive dimension, and the
cup `∑ⱼ eⱼ ⊗ eⱼ` has trace `n`.

Everything except the last section is stated over a commutative semiring, as the cap is: that
includes both invariance statements, under a permutation of the tensor factors and under a matrix
preserving the dot product.  Only the orthogonal group itself needs a commutative ring, so the
statements that mention it — the invariance of the contractions under `O(n)`, and the harmonic
tensors as a subrepresentation of it — are the ones collected in the last section.

## Main definitions

* `TauCeti.orthogonalContract`: the contraction of two slots of a tensor power against the
  coordinate dot product.
* `TauCeti.harmonicTensors`: the harmonic (traceless) tensors, the common kernel of the
  contractions.
* `TauCeti.harmonicPermSubrep`: the harmonic tensors as a subrepresentation of the symmetric-group
  action on the tensor power.
* `TauCeti.harmonicSubrep`: the harmonic tensors as a subrepresentation of the tensor power of the
  standard representation of the orthogonal group.

## Main results

* `TauCeti.orthogonalContract_tprod`: a contraction caps the two named slots of a pure tensor and
  keeps the rest.
* `TauCeti.mem_harmonicTensors_iff`: membership is the vanishing of every contraction.
* `TauCeti.harmonicTensors_eq_top_of_lt_two`, `TauCeti.harmonicTensors_two`: the two degenerate
  cases, everything below two slots and the kernel of the cap on two slots.
* `TauCeti.harmonicTensors_two_ne_top`: in every positive dimension the harmonic tensors are a
  proper submodule of the tensor square, `TauCeti.orthogonalCup_notMem_harmonicTensors`: the cup is
  not harmonic when `n` is nonzero in `k`, and `TauCeti.tprod_single_mem_harmonicTensors`: a pure
  tensor of two distinct basis vectors is harmonic.
* `TauCeti.orthogonalContract_comp_permTensorAction` and
  `TauCeti.permTensorAction_mem_harmonicTensors`: permuting the tensor factors renames the capped
  slots, so the harmonic tensors are stable under the symmetric group, and
  `TauCeti.permTensorActionAlgHom_mem_harmonicTensors` extends that to its group algebra, so a
  Young symmetrizer keeps a harmonic tensor harmonic.
* `TauCeti.orthogonalContract_trans_sumCongr` and
  `TauCeti.ker_orthogonalContract_trans_sumCongr`: relabelling the surviving slots and swapping the
  two capped slots post-compose the contraction with a permutation, so its kernel depends only on
  the unordered pair of capped slots.
* `TauCeti.orthogonalContract_comp_piTensorProductMap`: a matrix preserving the dot product
  commutes with every contraction, and `TauCeti.orthogonalContract_comp_tensorPower` reads that
  off for the orthogonal group.
* `TauCeti.tensorPower_mem_harmonicTensors`: the harmonic tensors are stable under the orthogonal
  group.

## References

* R. Goodman and N. R. Wallach, *Symmetry, Representations, and Invariants*, Springer GTM 255
  (2009), Chapter 10.
* H. Weyl, *The Classical Groups: Their Invariants and Representations*, Princeton (1939).
-/

public section

open Matrix
open scoped TensorProduct

universe u

namespace TauCeti

variable (k : Type u) (n : ℕ)

section CommSemiring

variable [CommSemiring k] {d m : ℕ}

/-- **The contraction of two slots.**  Relabel the slots by `σ`, split the tensor power along the
resulting `Fin m ⊕ Fin 2`, and cap the two-slot factor against the coordinate dot product: the
slots `σ` names `Sum.inr 0` and `Sum.inr 1` are contracted away and the remaining `m` slots
survive, relabelled by `σ`. -/
noncomputable def orthogonalContract (σ : Fin d ≃ Fin m ⊕ Fin 2) :
    (⨂[k]^d (Fin n → k)) →ₗ[k] (⨂[k]^m (Fin n → k)) :=
  (TensorProduct.rid k (⨂[k]^m (Fin n → k))).toLinearMap ∘ₗ
    LinearMap.lTensor (⨂[k]^m (Fin n → k)) (orthogonalCap k n) ∘ₗ
      ((PiTensorProduct.reindex k (fun _ : Fin d => (Fin n → k)) σ).trans
        (PiTensorProduct.tmulEquiv k (Fin n → k)).symm).toLinearMap

/-- A contraction dots the two capped slots of a pure tensor and keeps the others. -/
@[simp]
theorem orthogonalContract_tprod (σ : Fin d ≃ Fin m ⊕ Fin 2) (v : Fin d → (Fin n → k)) :
    orthogonalContract k n σ (PiTensorProduct.tprod k v) =
      (v (σ.symm (Sum.inr 0)) ⬝ᵥ v (σ.symm (Sum.inr 1))) •
        PiTensorProduct.tprod k fun i : Fin m => v (σ.symm (Sum.inl i)) := by
  simp [orthogonalContract]

/-- **The harmonic (traceless) tensors**: the tensors killed by every contraction of a pair of
slots against the coordinate dot product. -/
noncomputable def harmonicTensors (d : ℕ) : Submodule k (⨂[k]^d (Fin n → k)) :=
  ⨅ m : ℕ, ⨅ σ : Fin d ≃ Fin m ⊕ Fin 2, LinearMap.ker (orthogonalContract k n σ)

/-- A tensor is harmonic exactly when every contraction kills it. -/
@[simp]
theorem mem_harmonicTensors_iff {x : ⨂[k]^d (Fin n → k)} :
    x ∈ harmonicTensors k n d ↔
      ∀ (m : ℕ) (σ : Fin d ≃ Fin m ⊕ Fin 2), orthogonalContract k n σ x = 0 := by
  simp [harmonicTensors, Submodule.mem_iInf, LinearMap.mem_ker]

/-- **Below two slots every tensor is harmonic**: there is no pair of slots to contract. -/
theorem harmonicTensors_eq_top_of_lt_two (h : d < 2) : harmonicTensors k n d = ⊤ := by
  refine eq_top_iff.mpr fun x _ => (mem_harmonicTensors_iff k n).mpr fun m σ => ?_
  have hd : d = m + 2 := by simpa using Fintype.card_congr σ
  exact absurd hd (by omega)

/-- Scalars are harmonic. -/
@[simp]
theorem harmonicTensors_zero : harmonicTensors k n 0 = ⊤ :=
  harmonicTensors_eq_top_of_lt_two k n (by norm_num)

/-- Vectors are harmonic. -/
@[simp]
theorem harmonicTensors_one : harmonicTensors k n 1 = ⊤ :=
  harmonicTensors_eq_top_of_lt_two k n (by norm_num)

/-- On the tensor square every contraction is the cap, read through the canonical identification
of the empty tensor power with the scalars. -/
theorem isEmptyEquiv_comp_orthogonalContract (σ : Fin 2 ≃ Fin 0 ⊕ Fin 2) :
    (PiTensorProduct.isEmptyEquiv (R := k) (s := fun _ : Fin 0 => (Fin n → k))
        (Fin 0)).toLinearMap ∘ₗ orthogonalContract k n σ = orthogonalCap k n := by
  refine PiTensorProduct.ext ?_
  ext v
  simp only [LinearMap.compMultilinearMap_apply, LinearMap.coe_comp, Function.comp_apply,
    LinearEquiv.coe_coe, orthogonalContract_tprod, map_smul, smul_eq_mul,
    PiTensorProduct.isEmptyEquiv_apply_tprod, mul_one, orthogonalCap_tprod]
  -- The two capped slots are the two slots of the square, in one order or the other.
  have hne : σ.symm (Sum.inr 0) ≠ σ.symm (Sum.inr 1) := fun h => by simpa using σ.symm.injective h
  revert hne
  generalize σ.symm (Sum.inr 0) = a
  generalize σ.symm (Sum.inr 1) = b
  intro hne
  fin_cases a <;> fin_cases b <;> simp_all [dotProduct_comm]

/-- **On the tensor square the harmonic tensors are the kernel of the cap.** -/
@[simp]
theorem harmonicTensors_two :
    harmonicTensors k n 2 = LinearMap.ker (orthogonalCap k n) := by
  ext x
  rw [mem_harmonicTensors_iff, LinearMap.mem_ker]
  constructor
  · intro h
    have hx := h 0 (Equiv.emptySum (Fin 0) (Fin 2)).symm
    rw [← LinearMap.congr_fun
      (isEmptyEquiv_comp_orthogonalContract k n (Equiv.emptySum (Fin 0) (Fin 2)).symm) x]
    simp [hx]
  · intro hx m σ
    obtain rfl : m = 0 := by
      have hd : 2 = m + 2 := by simpa using Fintype.card_congr σ
      omega
    have h := LinearMap.congr_fun (isEmptyEquiv_comp_orthogonalContract k n σ) x
    simp only [LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe] at h
    rw [hx] at h
    exact (map_eq_zero_iff _ (PiTensorProduct.isEmptyEquiv
      (R := k) (s := fun _ : Fin 0 => (Fin n → k)) (Fin 0)).injective).mp h

/-- **The cup is not harmonic** when `n` is nonzero in `k`: closing it with a cap makes the loop
value `n`.  This is what keeps the harmonic tensors a proper submodule. -/
theorem orthogonalCup_notMem_harmonicTensors (hn : (n : k) ≠ 0) :
    orthogonalCup k n 1 ∉ harmonicTensors k n 2 := by
  rw [harmonicTensors_two, LinearMap.mem_ker, orthogonalCap_comp_orthogonalCup_apply, mul_one]
  exact hn

/-- **The harmonic tensors are a proper submodule of the tensor square** in every positive
dimension: the diagonal tensor `eᵢ ⊗ eᵢ` has trace `1`, which is nonzero over a nontrivial ring.
This needs no assumption on the characteristic, unlike the cup of
`TauCeti.orthogonalCup_notMem_harmonicTensors`. -/
theorem harmonicTensors_two_ne_top [Nontrivial k] (hn : 0 < n) : harmonicTensors k n 2 ≠ ⊤ := by
  intro h
  have hmem : PiTensorProduct.tprod k
      ![Pi.single (⟨0, hn⟩ : Fin n) (1 : k), Pi.single (⟨0, hn⟩ : Fin n) (1 : k)] ∈
      harmonicTensors k n 2 := h ▸ Submodule.mem_top
  rw [harmonicTensors_two, LinearMap.mem_ker, orthogonalCap_tprod] at hmem
  simp at hmem

/-- **A pure tensor of distinct standard basis vectors is harmonic.**  The single contraction on
the tensor square dots the two slots against each other, and `eᵢ ⬝ᵥ eⱼ` vanishes for `i ≠ j`. -/
theorem tprod_single_mem_harmonicTensors {i j : Fin n} (hij : i ≠ j) :
    PiTensorProduct.tprod k ![Pi.single i (1 : k), Pi.single j (1 : k)] ∈
      harmonicTensors k n 2 := by
  rw [harmonicTensors_two, LinearMap.mem_ker, orthogonalCap_tprod]
  simp [Matrix.cons_val_zero, Matrix.cons_val_one, hij]

/-- **Contracting after permuting the tensor factors** is contracting along the composite: the
permutation only renames which slots are capped. -/
theorem orthogonalContract_comp_permTensorAction (τ : Equiv.Perm (Fin d))
    (σ : Fin d ≃ Fin m ⊕ Fin 2) :
    orthogonalContract k n σ ∘ₗ permTensorAction k n d τ =
      orthogonalContract k n (τ.trans σ) := by
  refine PiTensorProduct.ext ?_
  ext v
  simp

/-- **Relabelling the surviving slots and swapping the two capped slots** post-composes the
contraction with a permutation of the tensor factors of the target: the *unordered* pair of capped
slots is all that a contraction records. -/
theorem orthogonalContract_trans_sumCongr (σ : Fin d ≃ Fin m ⊕ Fin 2) (τ : Equiv.Perm (Fin m))
    (υ : Equiv.Perm (Fin 2)) :
    orthogonalContract k n (σ.trans (Equiv.sumCongr τ υ)) =
      permTensorAction k n m τ ∘ₗ orthogonalContract k n σ := by
  refine PiTensorProduct.ext ?_
  ext v
  -- `υ` only swaps the two capped slots, and the dot product is symmetric.
  have hdot : v (σ.symm (Sum.inr (υ.symm 0))) ⬝ᵥ v (σ.symm (Sum.inr (υ.symm 1))) =
      v (σ.symm (Sum.inr 0)) ⬝ᵥ v (σ.symm (Sum.inr 1)) := by
    have hne : υ.symm 0 ≠ υ.symm 1 := by simp
    revert hne
    generalize υ.symm 0 = a
    generalize υ.symm 1 = b
    intro hne
    fin_cases a <;> fin_cases b <;> simp_all [dotProduct_comm]
  simp [hdot]

/-- Relabelling the surviving slots and swapping the two capped slots do not change the kernel of
a contraction, which is why the harmonic tensors may be defined by quantifying over all the
equivalences `σ` rather than over the unordered pairs of slots. -/
theorem ker_orthogonalContract_trans_sumCongr (σ : Fin d ≃ Fin m ⊕ Fin 2)
    (τ : Equiv.Perm (Fin m)) (υ : Equiv.Perm (Fin 2)) :
    LinearMap.ker (orthogonalContract k n (σ.trans (Equiv.sumCongr τ υ))) =
      LinearMap.ker (orthogonalContract k n σ) := by
  rw [orthogonalContract_trans_sumCongr, permTensorAction_apply, LinearEquiv.ker_comp]

/-- **The harmonic tensors are stable under permuting the tensor factors**, so the action of the
symmetric group on the tensor power restricts to them. -/
theorem permTensorAction_mem_harmonicTensors (τ : Equiv.Perm (Fin d))
    {x : ⨂[k]^d (Fin n → k)} (hx : x ∈ harmonicTensors k n d) :
    permTensorAction k n d τ x ∈ harmonicTensors k n d := by
  rw [mem_harmonicTensors_iff] at hx ⊢
  intro m σ
  have h := LinearMap.congr_fun (orthogonalContract_comp_permTensorAction k n τ σ) x
  simp only [LinearMap.coe_comp, Function.comp_apply] at h
  rw [h, hx m (τ.trans σ)]

/-- **The harmonic tensors as a subrepresentation** of the symmetric-group action on the tensor
power: the bundled form of `TauCeti.permTensorAction_mem_harmonicTensors`. -/
noncomputable def harmonicPermSubrep (d : ℕ) : Subrepresentation (permTensorAction k n d) where
  toSubmodule := harmonicTensors k n d
  apply_mem_toSubmodule τ _ hx := permTensorAction_mem_harmonicTensors k n τ hx

/-- The symmetric-group subrepresentation of harmonic tensors carries the submodule of harmonic
tensors. -/
@[simp]
theorem toSubmodule_harmonicPermSubrep :
    (harmonicPermSubrep k n d).toSubmodule = harmonicTensors k n d := (rfl)

/-- Membership in the symmetric-group subrepresentation of harmonic tensors is membership in the
harmonic tensors. -/
@[simp]
theorem mem_harmonicPermSubrep {x : ⨂[k]^d (Fin n → k)} :
    x ∈ harmonicPermSubrep k n d ↔ x ∈ harmonicTensors k n d := Iff.rfl

/-- **The harmonic tensors are stable under the whole group algebra of the symmetric group**, not
just under single permutations: applying a Young symmetrizer to a harmonic tensor leaves it
harmonic. -/
theorem permTensorActionAlgHom_mem_harmonicTensors (a : MonoidAlgebra k (Equiv.Perm (Fin d)))
    {x : ⨂[k]^d (Fin n → k)} (hx : x ∈ harmonicTensors k n d) :
    permTensorActionAlgHom k n d a x ∈ harmonicTensors k n d := by
  rw [permTensorActionAlgHom_def]
  exact (permTensorAction k n d).asAlgebraHom_mem_of_forall_mem _
    (fun τ _ h => permTensorAction_mem_harmonicTensors k n τ h) x hx a

section Invariance

variable {k n}

/-- **Contractions commute with an isometry.**  A matrix `A` with `Aᵀ * A = 1` acts diagonally on
every tensor power, and contracting a pair of slots is unaffected: the cap it contracts against is
exactly what `A` preserves. -/
theorem orthogonalContract_comp_piTensorProductMap {A : Matrix (Fin n) (Fin n) k} (hA : Aᵀ * A = 1)
    (σ : Fin d ≃ Fin m ⊕ Fin 2) :
    orthogonalContract k n σ ∘ₗ PiTensorProduct.map (fun _ : Fin d => Matrix.mulVecLin A) =
      PiTensorProduct.map (fun _ : Fin m => Matrix.mulVecLin A) ∘ₗ orthogonalContract k n σ := by
  refine PiTensorProduct.ext ?_
  ext v
  -- The invariance of the cap, read on the pure tensor of the two capped slots.
  have hv : (A *ᵥ v (σ.symm (Sum.inr 0))) ⬝ᵥ (A *ᵥ v (σ.symm (Sum.inr 1))) =
      v (σ.symm (Sum.inr 0)) ⬝ᵥ v (σ.symm (Sum.inr 1)) := by
    simpa using LinearMap.congr_fun (orthogonalCap_comp_piTensorProductMap hA)
      (PiTensorProduct.tprod k ![v (σ.symm (Sum.inr 0)), v (σ.symm (Sum.inr 1))])
  simp only [LinearMap.compMultilinearMap_apply, LinearMap.coe_comp, Function.comp_apply,
    PiTensorProduct.map_tprod, orthogonalContract_tprod, map_smul, Matrix.mulVecLin_apply]
  rw [hv]

end Invariance

end CommSemiring

section CommRing

variable [CommRing k] {d m : ℕ}

/-- **Contractions commute with the orthogonal group.**  This is the tensor-power form of the
invariance of the cap, and it is what makes the harmonic tensors a subrepresentation. -/
theorem orthogonalContract_comp_tensorPower (g : Matrix.orthogonalGroup (Fin n) k)
    (σ : Fin d ≃ Fin m ⊕ Fin 2) :
    orthogonalContract k n σ ∘ₗ (stdOrthogonalRep k n).tensorPower d g =
      (stdOrthogonalRep k n).tensorPower m g ∘ₗ orthogonalContract k n σ := by
  rw [Representation.tensorPower_apply, Representation.tensorPower_apply]
  simpa only [stdOrthogonalRep_apply] using orthogonalContract_comp_piTensorProductMap
    ((Matrix.mem_orthogonalGroup_iff' (Fin n) k).mp g.prop) σ

/-- **The harmonic tensors are stable under the orthogonal group.** -/
theorem tensorPower_mem_harmonicTensors (g : Matrix.orthogonalGroup (Fin n) k)
    {x : ⨂[k]^d (Fin n → k)} (hx : x ∈ harmonicTensors k n d) :
    (stdOrthogonalRep k n).tensorPower d g x ∈ harmonicTensors k n d := by
  rw [mem_harmonicTensors_iff] at hx ⊢
  intro m σ
  have h := LinearMap.congr_fun (orthogonalContract_comp_tensorPower k n g σ) x
  simp only [LinearMap.coe_comp, Function.comp_apply] at h
  rw [h, hx m σ, map_zero]

/-- **The harmonic tensors as a subrepresentation** of the `d`-fold tensor power of the standard
representation of the orthogonal group. -/
noncomputable def harmonicSubrep (d : ℕ) :
    Subrepresentation ((stdOrthogonalRep k n).tensorPower d) where
  toSubmodule := harmonicTensors k n d
  apply_mem_toSubmodule g _ hv := tensorPower_mem_harmonicTensors k n g hv

/-- The subrepresentation of harmonic tensors carries the submodule of harmonic tensors. -/
@[simp]
theorem toSubmodule_harmonicSubrep :
    (harmonicSubrep k n d).toSubmodule = harmonicTensors k n d := (rfl)

/-- Membership in the harmonic subrepresentation is membership in the harmonic tensors. -/
@[simp]
theorem mem_harmonicSubrep {x : ⨂[k]^d (Fin n → k)} :
    x ∈ harmonicSubrep k n d ↔ x ∈ harmonicTensors k n d := Iff.rfl

end CommRing

end TauCeti
