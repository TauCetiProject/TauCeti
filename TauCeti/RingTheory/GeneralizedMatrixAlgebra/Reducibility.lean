/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.Submodule.Bilinear
public import Mathlib.LinearAlgebra.TensorProduct.Basic
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import TauCeti.RingTheory.GeneralizedMatrixAlgebra.Matrix

/-!
# Reducibility ideals of generalized matrix algebras

Let `E` be GMA data on an `A`-algebra `R`, with entry modules `A_{ij}` and scalar pairing
`φ : A_{ij} × A_{ji} → A`. The *reducibility ideal* `I_{ij} ⊆ A` of two blocks `i, j` is the
ideal `A_{ij} A_{ji}` of products of opposite entries, read as scalars through `φ`; equivalently
it is the image of `A_{ij} ⊗_A A_{ji} → A`. For a partition `P` of the blocks, the reducibility
ideal `I_P` is the sum of the `I_{ij}` over pairs of blocks in different parts.

These ideals measure how far a generalized matrix algebra is from being block triangular. The
diagonal block `x ↦ ψᵢ(eᵢ x eᵢ)` of the block `i` is additive but not multiplicative: the defect
`ψᵢ(eᵢ xy eᵢ) - ψᵢ(eᵢ x eᵢ) ψᵢ(eᵢ y eᵢ)` is the sum over `k ≠ i` of `ψᵢ(eᵢ x eₖ y eᵢ)`, whose
entries lie in `I_{ik}`. Consequently, for an ideal `J` of `A`, the diagonal block reduced modulo
`J` is an `A`-algebra homomorphism `R → M_{dᵢ}(A/J)` exactly when `I_{ik} ⊆ J` for every `k ≠ i`.
This is the quotient representation attached to a singleton part `{i}` of a partition `P` with
`I_P ⊆ J`.

For blocks of size one the diagonal block is the trace coordinate `a(x) = T(eᵢ x)`, and for a
generalized matrix algebra with two blocks `i, j` of size one the defect is Pan's
`x(σ, τ) = a(στ) - a(σ) a(τ) = T(eᵢ σ eⱼ τ)`, the product `b(σ) c(τ)` of the off-diagonal
entries in a matrix realization. If `R` is spanned by a set `G` (for instance the image of a
group), the values `x(σ, τ)` for `σ, τ ∈ G` generate the reducibility ideal `I_{ij}`.

## Main definitions

* `TauCeti.GMAData.reducibilityIdeal`: the reducibility ideal `I_{ij} = A_{ij} A_{ji}`.
* `TauCeti.GMAData.partitionReducibilityIdeal`: the reducibility ideal `I_P` of a partition.
* `TauCeti.GMAData.diagonalBlock`: the diagonal block `x ↦ ψᵢ(eᵢ x eᵢ)`.
* `TauCeti.GMAData.quotientRepresentation`: the diagonal block modulo an ideal `J` containing
  every `I_{ik}`, `k ≠ i`, as an `A`-algebra homomorphism `R → M_{dᵢ}(A/J)`.

## Main results

* `TauCeti.GMAData.range_lift_pairing`: `I_{ij}` is the image of `A_{ij} ⊗_A A_{ji} → A`.
* `TauCeti.GMAData.reducibilityIdeal_comm`, `TauCeti.GMAData.reducibilityIdeal_self`:
  `I_{ij} = I_{ji}` and `I_{ii} = A`.
* `TauCeti.GMAData.diagonalBlock_mul`: the multiplication defect of the diagonal block.
* `TauCeti.GMAData.diagonalBlock_mul_idempotent_mul_apply_mem`: the entries of
  `ψᵢ(eᵢ x eₖ y eᵢ)` lie in `I_{ik}`.
* `TauCeti.GMAData.forall_reducibilityIdeal_le_iff_map_diagonalBlock_mul`: the diagonal block of
  `i` is multiplicative modulo `J` if and only if `I_{ik} ⊆ J` for every `k ≠ i`.
* `TauCeti.GMAData.reducibilityIdeal_eq_span_of_span_eq_top`,
  `TauCeti.GMAData.reducibilityIdeal_eq_span_idempotent_of_span_eq_top`: generators of `I_{ij}`
  from a spanning set of `R`.
* `TauCeti.GMAData.trace_idempotent_mul_mul_sub`,
  `TauCeti.GMAData.reducibilityIdeal_eq_span_trace_sub`: for two blocks, the first of size one,
  `a(στ) - a(σ) a(τ) = T(eᵢ σ eⱼ τ)`, and these values generate `I_{ij}`.
* `Matrix.reducibilityIdeal_scalarGMAData`: in a matrix algebra every reducibility ideal is `A`.

## References

* J. Bellaïche, G. Chenevier, *Families of Galois representations and Selmer groups*,
  Astérisque 324 (2009), §1.5: Proposition 1.5.1 and §1.5.4.
* P. Allen, J. Newton, J. Thorne, *Automorphy lifting for residually reducible l-adic Galois
  representations, II*, Compos. Math. 156 (2020), Proposition 2.5.
* L. Pan, *The Fontaine–Mazur conjecture in the residually reducible case*, J. Amer. Math. Soc.
  35 (2022), §2.1.
-/

public section

open Matrix

namespace TauCeti

namespace GMAData

variable {A R : Type*} [CommSemiring A] [Semiring R] [Algebra A R] {ι : Type*} [Fintype ι]
  {d : ι → ℕ} (E : GMAData A R d)

/-! ### The diagonal blocks -/

/-- The **diagonal block** `ψᵢ(eᵢ x eᵢ)` of an element `x`: its compression to the corner
`eᵢ R eᵢ`, read as a matrix through the corner isomorphism `ψᵢ`. It is `A`-linear and sends `1`
to `1`, but is multiplicative only modulo the reducibility ideals `I_{ik}`, `k ≠ i`
(`TauCeti.GMAData.diagonalBlock_mul`). -/
def diagonalBlock (i : ι) : R →ₗ[A] Matrix (Fin (d i)) (Fin (d i)) A where
  toFun x := E.cornerEquiv i ((E.isIdempotentElem_idempotent i).compress x)
  map_add' x y := by simp
  map_smul' a x := by simp

theorem diagonalBlock_apply (i : ι) (x : R) :
    E.diagonalBlock i x = E.cornerEquiv i ((E.isIdempotentElem_idempotent i).compress x) :=
  (rfl)

/-- On the corner `eᵢ R eᵢ`, the diagonal block is the corner isomorphism `ψᵢ`. -/
@[simp]
theorem diagonalBlock_val (i : ι) (b : (E.isIdempotentElem_idempotent i).Corner) :
    E.diagonalBlock i b.val = E.cornerEquiv i b := by
  rw [diagonalBlock_apply, IsIdempotentElem.compress_val]

@[simp]
theorem diagonalBlock_one (i : ι) : E.diagonalBlock i 1 = 1 := by
  rw [diagonalBlock_apply, IsIdempotentElem.compress_one, map_one]

/-- The trace of a diagonal block is the trace of the cut-down element:
`tr ψᵢ(eᵢ x eᵢ) = T(eᵢ x)`. -/
theorem trace_idempotent_mul (i : ι) (x : R) :
    E.trace (E.idempotent i * x) = (E.diagonalBlock i x).trace := by
  rw [diagonalBlock_apply, ← trace_val, IsIdempotentElem.val_compress,
    E.trace_mul_comm (E.idempotent i * x), ← mul_assoc, (E.isIdempotentElem_idempotent i).eq]

/-- The diagonal block of an element of another block is zero: `ψᵢ(eᵢ x eᵢ) = 0` when
`x ∈ eⱼ R eₖ` with `k ≠ i`. -/
theorem diagonalBlock_eq_zero_of_mem_cornerSubmodule {i j k : ι} (hk : k ≠ i) {x : R}
    (hx : x ∈ TauCeti.cornerSubmodule A (E.idempotent j) (E.idempotent k)) :
    E.diagonalBlock i x = 0 := by
  have h : (E.isIdempotentElem_idempotent i).compress x = 0 := Subtype.ext <| by
    rw [IsIdempotentElem.val_compress, IsIdempotentElem.Corner.val_zero,
      ← TauCeti.mul_eq_self_of_mem_cornerSubmodule_right (E.isIdempotentElem_idempotent k) hx,
      mul_assoc _ _ (E.idempotent i), mul_assoc x, E.idempotent_mul_idempotent_of_ne hk, mul_zero,
      mul_zero]
  rw [diagonalBlock_apply, h, map_zero]

/-- **The multiplication defect of a diagonal block**: inserting `1 = ∑ₖ eₖ` between `x` and `y`,
`ψᵢ(eᵢ xy eᵢ) = ψᵢ(eᵢ x eᵢ) ψᵢ(eᵢ y eᵢ) + ∑_{k ≠ i} ψᵢ(eᵢ x eₖ y eᵢ)`. -/
theorem diagonalBlock_mul [DecidableEq ι] (i : ι) (x y : R) :
    E.diagonalBlock i (x * y) = E.diagonalBlock i x * E.diagonalBlock i y +
      ∑ k ∈ Finset.univ.erase i, E.diagonalBlock i (x * E.idempotent k * y) := by
  have h : x * y = ∑ k, x * E.idempotent k * y := by
    rw [← Finset.sum_mul, ← Finset.mul_sum, E.completeOrthogonalIdempotents.complete, mul_one]
  rw [h, map_sum, ← Finset.add_sum_erase _ _ (Finset.mem_univ i)]
  congr 1
  rw [diagonalBlock_apply, diagonalBlock_apply, diagonalBlock_apply, ← map_mul]
  congr 1
  refine Subtype.ext ?_
  simp only [IsIdempotentElem.val_compress, IsIdempotentElem.Corner.val_mul, mul_assoc,
    (E.isIdempotentElem_idempotent i).mul_self_mul]

/-! ### Blocks of size one and trace coordinates -/

/-- **The multiplication defect of a trace coordinate**: for a block of size one, the trace
coordinate `a(x) = T(eᵢ x)` satisfies `a(xy) = a(x) a(y) + ∑_{k ≠ i} T(eᵢ x eₖ y)`. This is the
trace of `TauCeti.GMAData.diagonalBlock_mul`, as the trace of `1 × 1` matrices is multiplicative. -/
theorem trace_idempotent_mul_mul [DecidableEq ι] {i : ι} (h : d i = 1) (x y : R) :
    E.trace (E.idempotent i * (x * y)) =
      E.trace (E.idempotent i * x) * E.trace (E.idempotent i * y) +
        ∑ k ∈ Finset.univ.erase i, E.trace (E.idempotent i * x * E.idempotent k * y) := by
  have : Subsingleton (Fin (d i)) := Fin.subsingleton_iff_le_one.2 h.le
  let o : Fin (d i) := ⟨0, by omega⟩
  have htr (M N : Matrix (Fin (d i)) (Fin (d i)) A) : (M * N).trace = M.trace * N.trace := by
    simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Fintype.sum_subsingleton _ o]
  rw [trace_idempotent_mul, diagonalBlock_mul, Matrix.trace_add, htr, Matrix.trace_sum]
  simp only [← trace_idempotent_mul, mul_assoc]

/-! ### The reducibility ideal of two blocks -/

variable [∀ i, NeZero (d i)]

/-- The **reducibility ideal** `I_{ij} = A_{ij} A_{ji}` of two blocks of a generalized matrix
algebra: the ideal of `A` spanned by the scalar pairings `φ(x, y)` of opposite entries
`x ∈ A_{ij}`, `y ∈ A_{ji}`. It is the image of `A_{ij} ⊗_A A_{ji} → A`
(`TauCeti.GMAData.range_lift_pairing`). -/
def reducibilityIdeal (i j : ι) : Ideal A :=
  Submodule.map₂ (E.pairing i j) ⊤ ⊤

theorem reducibilityIdeal_def (i j : ι) :
    E.reducibilityIdeal i j = Submodule.map₂ (E.pairing i j) ⊤ ⊤ :=
  (rfl)

theorem pairing_mem_reducibilityIdeal {i j : ι} (x : E.entry i j) (y : E.entry j i) :
    E.pairing i j x y ∈ E.reducibilityIdeal i j :=
  Submodule.apply_mem_map₂ _ Submodule.mem_top Submodule.mem_top

/-- The trace `T(xy) = φ(x, y)` of a product of opposite entries lies in `I_{ij}`. -/
theorem trace_mul_mem_reducibilityIdeal {i j : ι} {x y : R} (hx : x ∈ E.entry i j)
    (hy : y ∈ E.entry j i) : E.trace (x * y) ∈ E.reducibilityIdeal i j := by
  simpa only [pairing_apply] using E.pairing_mem_reducibilityIdeal ⟨x, hx⟩ ⟨y, hy⟩

theorem reducibilityIdeal_le_iff {i j : ι} {J : Ideal A} :
    E.reducibilityIdeal i j ≤ J ↔ ∀ (x : E.entry i j) (y : E.entry j i), E.pairing i j x y ∈ J :=
  Submodule.map₂_le.trans ⟨fun h x y ↦ h x Submodule.mem_top y Submodule.mem_top,
    fun h x _ y _ ↦ h x y⟩

/-- **The reducibility ideal is the image of the tensor product** `A_{ij} ⊗_A A_{ji} → A`
of the scalar pairing. -/
theorem range_lift_pairing (i j : ι) :
    LinearMap.range (TensorProduct.lift (E.pairing i j)) = E.reducibilityIdeal i j := by
  have h : (TensorProduct.mk A _ _).compr₂ (TensorProduct.lift (E.pairing i j)) = E.pairing i j :=
    LinearMap.ext₂ fun x y ↦ TensorProduct.lift.tmul x y
  rw [LinearMap.range_eq_map, ← TensorProduct.map₂_mk_top_top_eq_top, Submodule.map_map₂, h,
    reducibilityIdeal_def]

/-- **The reducibility ideal is symmetric**: `I_{ij} = I_{ji}`. -/
theorem reducibilityIdeal_comm (i j : ι) : E.reducibilityIdeal i j = E.reducibilityIdeal j i := by
  rw [reducibilityIdeal_def, reducibilityIdeal_def, ← E.pairing_flip j i, Submodule.map₂_flip]

/-- The reducibility ideal of a block with itself is the unit ideal, as `φ(Eᵢ, Eᵢ) = 1`. -/
@[simp]
theorem reducibilityIdeal_self (i : ι) : E.reducibilityIdeal i i = ⊤ := by
  refine (Ideal.eq_top_iff_one _).2 ?_
  have h := E.trace_mul_mem_reducibilityIdeal (E.primitiveIdempotent_mem_entry i)
    (E.primitiveIdempotent_mem_entry i)
  rwa [(E.isIdempotentElem_primitiveIdempotent i).eq, trace_primitiveIdempotent] at h

/-! ### The reducibility ideal of a partition -/

/-- The **reducibility ideal of a partition** of the blocks, the partition being given by the
labelling `p : ι → κ` of the blocks by their parts: the sum `I_P` of the reducibility ideals
`I_{ij}` over all pairs of blocks `i, j` in different parts. -/
def partitionReducibilityIdeal {κ : Type*} (p : ι → κ) : Ideal A :=
  ⨆ (i) (j) (_ : p i ≠ p j), E.reducibilityIdeal i j

theorem partitionReducibilityIdeal_def {κ : Type*} (p : ι → κ) :
    E.partitionReducibilityIdeal p = ⨆ (i) (j) (_ : p i ≠ p j), E.reducibilityIdeal i j :=
  (rfl)

theorem reducibilityIdeal_le_partitionReducibilityIdeal {κ : Type*} {p : ι → κ} {i j : ι}
    (h : p i ≠ p j) : E.reducibilityIdeal i j ≤ E.partitionReducibilityIdeal p :=
  le_iSup_of_le i <| le_iSup_of_le j <| le_iSup_of_le h le_rfl

theorem partitionReducibilityIdeal_le_iff {κ : Type*} {p : ι → κ} {J : Ideal A} :
    E.partitionReducibilityIdeal p ≤ J ↔ ∀ i j, p i ≠ p j → E.reducibilityIdeal i j ≤ J := by
  simp only [partitionReducibilityIdeal_def, iSup_le_iff]

/-- If `I_P ⊆ J` and `{i}` is a part of `P`, then `I_{ik} ⊆ J` for every block `k ≠ i`. -/
theorem reducibilityIdeal_le_of_partitionReducibilityIdeal_le {κ : Type*} {p : ι → κ}
    {J : Ideal A} (hJ : E.partitionReducibilityIdeal p ≤ J) {i : ι} (hi : ∀ k, p k = p i → k = i)
    {k : ι} (hk : k ≠ i) : E.reducibilityIdeal i k ≤ J :=
  E.partitionReducibilityIdeal_le_iff.1 hJ i k fun h ↦ hk (hi k h.symm)

/-! ### The entries of the multiplication defect -/

/-- The `(a, c)` entry of the diagonal block `ψᵢ(eᵢ x eᵢ)` is `T(E_i^{0a} x E_i^{c0})`. -/
theorem diagonalBlock_apply_apply (i : ι) (x : R) (a c : Fin (d i)) :
    E.diagonalBlock i x a c = E.trace (E.matrixUnit i 0 a * x * E.matrixUnit i c 0) := by
  rw [E.matrixUnit_mul_mul_matrixUnit i 0 a c 0 x, map_smul, trace_matrixUnit, diagonalBlock_apply]
  simp

/-- For opposite entries `x ∈ A_{ik}` and `y ∈ A_{ki}`, the `(0, 0)` entry of the diagonal block
`ψᵢ(eᵢ xy eᵢ)` is the trace `T(xy) = φ(x, y)`. -/
theorem diagonalBlock_mul_apply_zero_zero_of_mem_entry {i k : ι} {x y : R} (hx : x ∈ E.entry i k)
    (hy : y ∈ E.entry k i) : E.diagonalBlock i (x * y) 0 0 = E.trace (x * y) := by
  rw [diagonalBlock_apply_apply, ← primitiveIdempotent_def, ← mul_assoc,
    E.primitiveIdempotent_mul_of_mem_entry hx, mul_assoc, E.mul_primitiveIdempotent_of_mem_entry hy]

/-- **The entries of `ψᵢ(eᵢ x eₖ y eᵢ)` lie in the reducibility ideal `I_{ik}`**: writing
`eₖ = ∑_b E_k^{b0} E_k^{0b}`, the `(a, c)` entry is the sum over `b` of the scalar pairings
`φ(E_i^{0a} x E_k^{b0}, E_k^{0b} y E_i^{c0})`. -/
theorem diagonalBlock_mul_idempotent_mul_apply_mem (i k : ι) (x y : R) (a c : Fin (d i)) :
    E.diagonalBlock i (x * E.idempotent k * y) a c ∈ E.reducibilityIdeal i k := by
  rw [diagonalBlock_apply_apply, ← E.sum_matrixUnit_self k]
  simp_rw [Finset.mul_sum, Finset.sum_mul]
  rw [Finset.mul_sum, Finset.sum_mul, map_sum]
  refine Submodule.sum_mem _ fun b _ ↦ ?_
  rw [← E.matrixUnit_mul_matrixUnit_same k b 0 b]
  have h : E.matrixUnit i 0 a * (x * (E.matrixUnit k b 0 * E.matrixUnit k 0 b) * y) *
      E.matrixUnit i c 0 = E.matrixUnit i 0 a * x * E.matrixUnit k b 0 *
        (E.matrixUnit k 0 b * y * E.matrixUnit i c 0) := by
    simp only [mul_assoc]
  rw [h]
  exact E.trace_mul_mem_reducibilityIdeal (E.matrixUnit_mul_mul_matrixUnit_mem_entry a b x)
    (E.matrixUnit_mul_mul_matrixUnit_mem_entry b c y)

/-- The trace `T(eᵢ x eₖ y)` lies in the reducibility ideal `I_{ik}`. -/
theorem trace_idempotent_mul_mul_idempotent_mul_mem (i k : ι) (x y : R) :
    E.trace (E.idempotent i * x * E.idempotent k * y) ∈ E.reducibilityIdeal i k := by
  rw [show E.idempotent i * x * E.idempotent k * y = E.idempotent i * (x * E.idempotent k * y) by
    simp only [mul_assoc], trace_idempotent_mul, Matrix.trace]
  exact Submodule.sum_mem _ fun a _ ↦ E.diagonalBlock_mul_idempotent_mul_apply_mem i k x y a a

/-- The trace `T(Eᵢ x Eₖ y)` lies in the reducibility ideal `I_{ik}`: it equals the pairing
`φ(Eᵢ x Eₖ, Eₖ y Eᵢ)` of opposite entries. -/
theorem trace_primitiveIdempotent_mul_mul_primitiveIdempotent_mul_mem (i k : ι) (x y : R) :
    E.trace (E.primitiveIdempotent i * x * E.primitiveIdempotent k * y) ∈
      E.reducibilityIdeal i k := by
  have h := E.trace_mul_mem_reducibilityIdeal (E.primitiveIdempotent_mul_mul_mem_entry i k x)
    (E.primitiveIdempotent_mul_mul_mem_entry k i y)
  rw [← mul_assoc, E.trace_mul_comm _ (E.primitiveIdempotent i)] at h
  simpa only [mul_assoc, (E.isIdempotentElem_primitiveIdempotent i).mul_self_mul,
    (E.isIdempotentElem_primitiveIdempotent k).mul_self_mul] using h

/-! ### Generators of the reducibility ideal -/

/-- The common form of the generators of `I_{ij}` from a spanning set `G` of `R`: if `e, f ∈ R`
are such that `e x f = x` for every `x ∈ A_{ij}` and every `T(e w f w')` lies in `I_{ij}`, then
`I_{ij}` is generated by the traces `T(e σ f τ)` for `σ, τ ∈ G`. -/
private theorem reducibilityIdeal_eq_span_trace_mul_mul_mul {G : Set R}
    (hG : Submodule.span A G = ⊤) {i j : ι} (e f : R) (hx : ∀ x ∈ E.entry i j, e * x * f = x)
    (hmem : ∀ w w', E.trace (e * w * f * w') ∈ E.reducibilityIdeal i j) :
    E.reducibilityIdeal i j =
      Ideal.span {t | ∃ σ ∈ G, ∃ τ ∈ G, E.trace (e * σ * f * τ) = t} := by
  -- the bilinear form `(w, w') ↦ T(e w f w')`
  let B : R →ₗ[A] R →ₗ[A] A :=
    ((LinearMap.mul A R).compl₁₂ (LinearMap.mulLeftRight A (e, f)) LinearMap.id).compr₂ E.trace
  have hB : E.reducibilityIdeal i j = Submodule.map₂ B ⊤ ⊤ := by
    refine le_antisymm (E.reducibilityIdeal_le_iff.2 fun x y ↦ ?_)
      (Submodule.map₂_le.2 fun w _ w' _ ↦ hmem w w')
    rw [pairing_apply, ← hx x x.property]
    exact Submodule.apply_mem_map₂ B Submodule.mem_top Submodule.mem_top
  rw [hB, ← hG, Submodule.map₂_span_span]
  refine congrArg _ (Set.ext fun t ↦ ?_)
  simp only [B, Set.mem_image2, LinearMap.compr₂_apply, LinearMap.compl₁₂_apply,
    LinearMap.mulLeftRight_apply, LinearMap.mul_apply', LinearMap.id_apply, Set.mem_ofPred_eq]

/-- **Generators of the reducibility ideal from a spanning set**: if `R` is spanned over `A` by
`G`, then `I_{ij}` is generated by the traces `T(Eᵢ σ Eⱼ τ)` for `σ, τ ∈ G`. -/
theorem reducibilityIdeal_eq_span_of_span_eq_top {G : Set R} (hG : Submodule.span A G = ⊤)
    (i j : ι) : E.reducibilityIdeal i j = Ideal.span
      {t | ∃ σ ∈ G, ∃ τ ∈ G,
        E.trace (E.primitiveIdempotent i * σ * E.primitiveIdempotent j * τ) = t} :=
  E.reducibilityIdeal_eq_span_trace_mul_mul_mul hG _ _
    (fun _ hx ↦ by
      rw [E.primitiveIdempotent_mul_of_mem_entry hx, E.mul_primitiveIdempotent_of_mem_entry hx])
    (E.trace_primitiveIdempotent_mul_mul_primitiveIdempotent_mul_mem i j)

/-- **Generators of the reducibility ideal from block idempotents**: if `R` is spanned over `A`
by `G`, then `I_{ij}` is generated by the traces `T(eᵢ σ eⱼ τ)` for `σ, τ ∈ G`. -/
theorem reducibilityIdeal_eq_span_idempotent_of_span_eq_top {G : Set R}
    (hG : Submodule.span A G = ⊤) (i j : ι) : E.reducibilityIdeal i j = Ideal.span
      {t | ∃ σ ∈ G, ∃ τ ∈ G, E.trace (E.idempotent i * σ * E.idempotent j * τ) = t} :=
  E.reducibilityIdeal_eq_span_trace_mul_mul_mul hG _ _
    (fun _ hx ↦ (TauCeti.mem_cornerSubmodule_iff A (E.isIdempotentElem_idempotent i)
      (E.isIdempotentElem_idempotent j)).1 (E.entry_le_cornerSubmodule i j hx))
    (E.trace_idempotent_mul_mul_idempotent_mul_mem i j)

end GMAData

/-! ### Coefficients in a commutative ring -/

namespace GMAData

variable {A R : Type*} [CommRing A] [Semiring R] [Algebra A R] {ι : Type*} [Fintype ι]
  {d : ι → ℕ} (E : GMAData A R d)

/-! #### Trace coordinates of two blocks -/

/-- **Pan's trace coordinates for two blocks of size one**: for a generalized matrix algebra with
two blocks `i, j`, the first of size one, the multiplication defect
`x(σ, τ) = a(στ) - a(σ) a(τ)` of the trace coordinate `a(σ) = T(eᵢ σ)` is `T(eᵢ σ eⱼ τ)`, the
trace of the product of the off-diagonal entries `eᵢ σ eⱼ` and `eⱼ τ eᵢ`. -/
theorem trace_idempotent_mul_mul_sub {i j : ι} (hij : i ≠ j) (hk : ∀ k, k = i ∨ k = j)
    (hi : d i = 1) (σ τ : R) :
    E.trace (E.idempotent i * (σ * τ)) -
        E.trace (E.idempotent i * σ) * E.trace (E.idempotent i * τ) =
      E.trace (E.idempotent i * σ * E.idempotent j * τ) := by
  classical
  have h : Finset.univ.erase i = {j} := by
    ext k
    rcases hk k with rfl | rfl <;> simp [hij, Ne.symm hij]
  rw [E.trace_idempotent_mul_mul hi, h, Finset.sum_singleton, add_sub_cancel_left]

variable [∀ i, NeZero (d i)]

/-! #### Reduction modulo an ideal -/

/-- **Reducibility ideals and multiplicativity modulo an ideal**: the diagonal block
`x ↦ ψᵢ(eᵢ x eᵢ)` of the block `i`, reduced modulo an ideal `J` of `A`, is multiplicative if and
only if `J` contains the reducibility ideal `I_{ik}` of every other block `k`. -/
theorem forall_reducibilityIdeal_le_iff_map_diagonalBlock_mul (i : ι) (J : Ideal A) :
    (∀ k, k ≠ i → E.reducibilityIdeal i k ≤ J) ↔ ∀ x y : R,
      (E.diagonalBlock i (x * y)).map (Ideal.Quotient.mk J) =
        (E.diagonalBlock i x).map (Ideal.Quotient.mk J) *
          (E.diagonalBlock i y).map (Ideal.Quotient.mk J) := by
  classical
  constructor
  · intro h x y
    rw [diagonalBlock_mul, Matrix.map_add _ (map_add _), Matrix.map_mul, add_eq_left]
    ext a c
    rw [Matrix.map_apply, Matrix.zero_apply, Ideal.Quotient.eq_zero_iff_mem, Matrix.sum_apply]
    exact Submodule.sum_mem _ fun k hk ↦ h k (Finset.ne_of_mem_erase hk)
      (E.diagonalBlock_mul_idempotent_mul_apply_mem i k x y a c)
  · intro h k hk
    refine E.reducibilityIdeal_le_iff.2 fun x y ↦ ?_
    -- `ψᵢ(eᵢ x eᵢ) = 0` as `x ∈ A_{ik}`, while the `(0, 0)` entry of `ψᵢ(eᵢ xy eᵢ)` is `φ(x, y)`
    have h₀ := congrFun₂ (h x y) 0 0
    rw [E.diagonalBlock_eq_zero_of_mem_cornerSubmodule hk
      (E.entry_le_cornerSubmodule i k x.property), Matrix.map_zero _ (map_zero _), zero_mul,
      Matrix.map_apply, Matrix.zero_apply, Ideal.Quotient.eq_zero_iff_mem,
      E.diagonalBlock_mul_apply_zero_zero_of_mem_entry x.property y.property] at h₀
    rwa [pairing_apply]

/-- The **quotient representation** of a block `i`: when the ideal `J` of `A` contains the
reducibility ideal `I_{ik}` of every other block `k`, the diagonal block `x ↦ ψᵢ(eᵢ x eᵢ)`
reduced modulo `J` is an `A`-algebra homomorphism `R → M_{dᵢ}(A/J)`. This applies to a singleton
part `{i}` of a partition `P` with `I_P ⊆ J`, by
`TauCeti.GMAData.reducibilityIdeal_le_of_partitionReducibilityIdeal_le`. -/
noncomputable def quotientRepresentation (i : ι) (J : Ideal A)
    (hJ : ∀ k, k ≠ i → E.reducibilityIdeal i k ≤ J) :
    R →ₐ[A] Matrix (Fin (d i)) (Fin (d i)) (A ⧸ J) :=
  AlgHom.ofLinearMap ((Ideal.Quotient.mkₐ A J).mapMatrix.toLinearMap ∘ₗ E.diagonalBlock i)
    (by simp) fun x y ↦ by
      simp only [LinearMap.comp_apply, AlgHom.toLinearMap_apply, AlgHom.mapMatrix_apply,
        Ideal.Quotient.mkₐ_eq_mk]
      exact (E.forall_reducibilityIdeal_le_iff_map_diagonalBlock_mul i J).1 hJ x y

@[simp]
theorem quotientRepresentation_apply (i : ι) (J : Ideal A)
    (hJ : ∀ k, k ≠ i → E.reducibilityIdeal i k ≤ J) (x : R) :
    E.quotientRepresentation i J hJ x = (E.diagonalBlock i x).map (Ideal.Quotient.mk J) := by
  simp [quotientRepresentation]

/-! #### Pan's generators -/

/-- **Pan's generators of the reducibility ideal**: for a generalized matrix algebra with two
blocks `i, j`, the first of size one, spanned over `A` by a set `G` (for instance the image of a
group), the reducibility ideal `I_{ij}` is generated by the multiplication defects
`x(σ, τ) = a(στ) - a(σ) a(τ)` of the trace coordinate `a(σ) = T(eᵢ σ)`, for `σ, τ ∈ G`. -/
theorem reducibilityIdeal_eq_span_trace_sub {i j : ι} (hij : i ≠ j) (hk : ∀ k, k = i ∨ k = j)
    (hi : d i = 1) {G : Set R} (hG : Submodule.span A G = ⊤) :
    E.reducibilityIdeal i j = Ideal.span {t | ∃ σ ∈ G, ∃ τ ∈ G,
      E.trace (E.idempotent i * (σ * τ)) -
        E.trace (E.idempotent i * σ) * E.trace (E.idempotent i * τ) = t} := by
  simp_rw [E.reducibilityIdeal_eq_span_idempotent_of_span_eq_top hG,
    E.trace_idempotent_mul_mul_sub hij hk hi]

end GMAData

end TauCeti

/-! ### The matrix algebra -/

namespace Matrix

variable {A n : Type*} [CommSemiring A] [Fintype n] [DecidableEq n]

/-- **The reducibility ideals of a matrix algebra are the unit ideal**: for the scalar-block GMA
data on `Mₙ(A)`, `φ(Eᵢⱼ, Eⱼᵢ) = 1`. -/
@[simp]
theorem reducibilityIdeal_scalarGMAData (i j : n) :
    (scalarGMAData A n).reducibilityIdeal i j = ⊤ := by
  refine (Ideal.eq_top_iff_one _).2 ?_
  have h := (scalarGMAData A n).pairing_mem_reducibilityIdeal
    ⟨single i j 1, single_mem_entry_scalarGMAData i j 1⟩
    ⟨single j i 1, single_mem_entry_scalarGMAData j i 1⟩
  rwa [pairing_scalarGMAData, mul_one] at h

end Matrix
