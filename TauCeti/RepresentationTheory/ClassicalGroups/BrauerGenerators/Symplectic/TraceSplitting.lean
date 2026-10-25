/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.Matrix.Rank
public import TauCeti.RepresentationTheory.ClassicalGroups.BrauerGenerators.Symplectic.Harmonic
public import TauCeti.RepresentationTheory.ClassicalGroups.BrauerGenerators.Symplectic.TensorPower
public import TauCeti.RepresentationTheory.Subrepresentation
-- The entrywise identity `Matrix.sum_sum_J_mul_J` for the loop value.
import TauCeti.LinearAlgebra.SymplecticGroup

/-!
# The trace splitting of the symplectic tensor powers

Let `V = k^{2n}` carry the standard alternating form `ω` of `Matrix.J`. The symplectic harmonic
tensors `TauCeti.symplecticHarmonicTensors k n d` are the common kernel of the contractions
`V^{⊗d} → V^{⊗(d-2)}` of two distinct slots against `ω`. The **trace tensors**
`TauCeti.symplecticTraceTensors k n d` are the sum of the images of the single-arc Brauer
generators `TauCeti.symplecticCupCapAt k n d i j`: the tensors obtained by inserting the
invariant bivector of `-J` into some pair of slots of a tensor of degree `d - 2`. This file proves
that over a star-ordered field, such as `ℚ`, `ℝ` or `ℂ`, the two are complementary
subrepresentations of `V^{⊗d}`
(`TauCeti.isCompl_symplecticHarmonicTensorsSubrep_symplecticTraceTensors`). This is the first
step of the trace filtration of the symplectic tensor powers, the symplectic counterpart of
`TauCeti.isCompl_harmonicTensorsSubrep_orthogonalTraceTensors`.

## The argument

An arc factors as an insertion after a contraction: `e i j` contracts the slots `i` and `j`
against `ω` and then inserts the bivector of `-J` into them
(`TauCeti.symplecticCupCapAt_eq_comp_contractTensorPair`). For `n > 0` the insertion has a left
inverse, the contraction of the same two slots against a coordinate form reading off one
coefficient of `-J` equal to `1`; for `n = 0` the tensor power of the zero module in positive
degree is itself zero. Either way the arc and the contraction have the same kernel for every `n`
and over every commutative ring (`TauCeti.ker_symplecticCupCapAt`); no invertibility of the loop
value `-2n` is needed. Contracting against `ω` itself instead closes a loop, which gives the loop
rule `TauCeti.contractTensorPair_stdSymplecticBilinForm_comp_symplecticCupCapAt` for the
contraction.

The splitting itself is Hermitian rather than combinatorial, exactly as in the orthogonal case. In
the monomial basis the coefficient of `e_w` in the image of `e_u` under an arc is
`-(J (u i) (u j) * J (w i) (w j))` when `u` and `w` agree off the two strands, and `0` otherwise
(`TauCeti.piTensorProduct_repr_symplecticCupCapAt_piTensorProduct`). This is symmetric in `u` and
`w`, and its entries are integers, which every star structure fixes, so every arc is self-adjoint
for the Hermitian form in which the monomial basis is orthonormal. The common kernel of finitely
many such operators complements the sum of their images over a star-ordered field
(`LinearMap.isCompl_iInf_ker_iSup_range_of_isHermitian_toMatrix`). The sign of the alternating
form does not enter: the two sign changes it forces on an arc cancel.

On two strands the trace tensors are the **trace line** `TauCeti.symplecticTraceLine`, the span of
the invariant bivector, on which the symplectic group acts trivially
(`TauCeti.symplecticTraceTensors_two`), and the splitting reads `V ⊗ V = ker (cap) ⊕ k · cup`.
There it needs only the loop value `-2n` to be invertible, `cap ∘ cup` being multiplication by it.
For `n = 1`, where the symplectic group is `SL₂` and the alternating form is the determinant, the
kernel of the cap is the symmetric square of `k²` and the trace line is spanned by
`e₁ ⊗ e₂ - e₂ ⊗ e₁`.

## Main definitions

* `TauCeti.symplecticTraceTensors`: in degree `d`, the sum of the images of the arcs, a
  subrepresentation of `V^{⊗d}`.
* `TauCeti.symplecticTraceLine`: the image of the cup in `V ⊗ V`, a subrepresentation on which
  the symplectic group acts trivially.

## Main results

* `TauCeti.symplecticCupCapAt_eq_comp_contractTensorPair`: an arc is the insertion of the
  bivector of `-J` after the contraction of its two slots.
* `TauCeti.ker_symplecticCupCapAt` and
  `TauCeti.symplecticHarmonicTensors_eq_iInf_ker_symplecticCupCapAt`: an arc and the contraction
  of its slots have the same kernel, so the harmonic tensors are the common kernel of the arcs.
* `TauCeti.isHermitian_toMatrix_symplecticCupCapAt`: the matrix of an arc in the monomial basis
  is Hermitian.
* `TauCeti.isCompl_symplecticHarmonicTensorsSubrep_symplecticTraceTensors`: **the trace
  splitting** of `V^{⊗d}` over a star-ordered field.
* `TauCeti.isCompl_ker_symplecticCap_range_symplecticCup` and
  `TauCeti.isCompl_symplecticHarmonicTensorsSubrep_symplecticTraceLine`: on two strands the same
  splitting holds over every commutative ring in which the loop value `-2n` is invertible.

## References

* R. Goodman and N. R. Wallach, *Symmetry, Representations, and Invariants*, Springer GTM 255
  (2009), Chapter 10, for the harmonic tensors of the symplectic group and the trace filtration.
-/

public section

open Matrix
open scoped TensorProduct

namespace TauCeti

universe u

variable {k : Type u} {n d : ℕ}

section CommRing

variable [CommRing k]

/-! ### An arc is an insertion after a contraction -/

/-- **An arc factors through the contraction of its two slots.** The generator `e i j` contracts
the slots `i` and `j` against the standard alternating form and then inserts the bivector of
`-J`, `∑ₓ ∑_y (-J) x y • eₓ ⊗ e_y`, into the same two slots. -/
theorem symplecticCupCapAt_eq_comp_contractTensorPair {i j : Fin d} (hij : i ≠ j) :
    symplecticCupCapAt k n d i j =
      (∑ x : Fin n ⊕ Fin n, ∑ y : Fin n ⊕ Fin n, (-Matrix.J (Fin n) k x y) •
        PiTensorProduct.insertPair k i j (Pi.single x (1 : k)) (Pi.single y (1 : k))) ∘ₗ
        (stdSymplecticBilinForm k n).contractTensorPair i j hij := by
  refine PiTensorProduct.ext <| MultilinearMap.ext fun v => ?_
  -- inserting into the two slots of the restricted input overwrites those slots of the input
  have hfun (x y : Fin n ⊕ Fin n) :
      (fun a => if h : a ≠ i ∧ a ≠ j then v a else if a = i then Pi.single x (1 : k) else
        Pi.single y (1 : k)) =
        Function.update (Function.update v i (Pi.single x 1)) j (Pi.single y 1) := by
    funext a
    rcases eq_or_ne a j with rfl | haj
    · simp [Ne.symm hij]
    rcases eq_or_ne a i with rfl | hai
    · simp [haj]
    · simp [hai, haj]
  simp only [LinearMap.compMultilinearMap_apply, LinearMap.comp_apply,
    symplecticCupCapAt_tprod hij, LinearMap.contractTensorPair_tprod, map_smul,
    LinearMap.sum_apply, LinearMap.smul_apply, PiTensorProduct.insertPair_tprod, hfun, neg_smul,
    Finset.sum_neg_distrib]

/-- **Contracting the two slots of an arc** against any bilinear form `B` multiplies the
contraction against the alternating form by the pairing of the inserted bivector under `B`,
`∑ₓ ∑_y (-J) x y * B eₓ e_y`. -/
theorem contractTensorPair_comp_symplecticCupCapAt
    (B : LinearMap.BilinForm k ((Fin n ⊕ Fin n) → k)) {i j : Fin d} (hij : i ≠ j) :
    B.contractTensorPair i j hij ∘ₗ symplecticCupCapAt k n d i j =
      (∑ x : Fin n ⊕ Fin n, ∑ y : Fin n ⊕ Fin n,
        -Matrix.J (Fin n) k x y * B (Pi.single x 1) (Pi.single y 1)) •
        (stdSymplecticBilinForm k n).contractTensorPair i j hij := by
  refine LinearMap.ext fun z => ?_
  rw [symplecticCupCapAt_eq_comp_contractTensorPair hij, LinearMap.comp_apply,
    LinearMap.comp_apply]
  simp only [LinearMap.sum_apply, LinearMap.smul_apply, map_sum, map_smul,
    ← LinearMap.comp_apply (B.contractTensorPair i j hij) (PiTensorProduct.insertPair k i j _ _),
    LinearMap.contractTensorPair_comp_insertPair, LinearMap.id_apply, smul_smul,
    ← Finset.sum_smul]

/-- **The loop rule for the contraction.** Contracting the two slots of an arc against the
alternating form closes a loop, which multiplies by the symplectic loop value `-2n`. -/
theorem contractTensorPair_stdSymplecticBilinForm_comp_symplecticCupCapAt {i j : Fin d}
    (hij : i ≠ j) :
    (stdSymplecticBilinForm k n).contractTensorPair i j hij ∘ₗ symplecticCupCapAt k n d i j =
      -(2 * n : k) • (stdSymplecticBilinForm k n).contractTensorPair i j hij := by
  rw [contractTensorPair_comp_symplecticCupCapAt]
  simp only [stdSymplecticBilinForm_single_single, neg_mul, Finset.sum_neg_distrib,
    Matrix.sum_sum_J_mul_J, Fintype.card_fin]

/-- **An arc and the contraction of its two slots have the same kernel**, for every `n` and over
every commutative ring; no invertibility of the loop value `-2n` is needed. -/
theorem ker_symplecticCupCapAt {i j : Fin d} (hij : i ≠ j) :
    LinearMap.ker (symplecticCupCapAt k n d i j) =
      LinearMap.ker ((stdSymplecticBilinForm k n).contractTensorPair i j hij) := by
  -- `⊆`: contracting the same two slots against the coordinate form
  -- `v ⊗ w ↦ v (inl 0) * w (inr 0)` undoes the insertion of the bivector of `-J`, whose
  -- coefficient there is `1`; for `n = 0` the tensor power is zero.
  -- `⊇`: the factorization `TauCeti.symplecticCupCapAt_eq_comp_contractTensorPair`.
  refine le_antisymm (fun z hz => ?_) ?_
  · rw [LinearMap.mem_ker] at hz ⊢
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · -- the tensor power of the zero module in positive degree is zero
      have htprod (v : Fin d → ((Fin 0 ⊕ Fin 0) → k)) : PiTensorProduct.tprod k v = 0 :=
        (PiTensorProduct.tprod k).map_coord_zero i
          (funext fun a => by rcases a with a | a <;> exact a.elim0)
      have hzero (y : ⨂[k]^d ((Fin 0 ⊕ Fin 0) → k)) : y = 0 := by
        induction y using PiTensorProduct.induction_on with
        | smul_tprod c v => rw [htprod, smul_zero]
        | add x y hx hy => rw [hx, hy, add_zero]
      rw [hzero z, map_zero]
    · let x₀ : Fin n ⊕ Fin n := Sum.inl ⟨0, hn⟩
      let y₀ : Fin n ⊕ Fin n := Sum.inr ⟨0, hn⟩
      -- the coordinate form reading off the `(x₀, y₀)` entry
      have h := LinearMap.congr_fun (contractTensorPair_comp_symplecticCupCapAt
        (Matrix.toBilin' (Matrix.single x₀ y₀ (1 : k))) hij) z
      have hsum : ∑ x : Fin n ⊕ Fin n, ∑ y : Fin n ⊕ Fin n, -Matrix.J (Fin n) k x y *
          Matrix.toBilin' (Matrix.single x₀ y₀ (1 : k)) (Pi.single x 1) (Pi.single y 1) = 1 := by
        simp only [Matrix.toBilin'_single, Matrix.single, Matrix.of_apply, mul_ite, mul_one,
          mul_zero, ite_and]
        simp [x₀, y₀, Matrix.J]
      rw [LinearMap.comp_apply, hz, map_zero, hsum, one_smul] at h
      exact h.symm
  · rw [symplecticCupCapAt_eq_comp_contractTensorPair hij]
    exact LinearMap.ker_le_ker_comp _ _

/-- **The harmonic tensors are the common kernel of the arcs**: the arc on two slots kills a
tensor exactly when the contraction of those slots does (`TauCeti.ker_symplecticCupCapAt`). -/
theorem symplecticHarmonicTensors_eq_iInf_ker_symplecticCupCapAt :
    symplecticHarmonicTensors k n d =
      ⨅ (i : Fin d) (j : Fin d) (_ : i ≠ j), LinearMap.ker (symplecticCupCapAt k n d i j) := by
  rw [symplecticHarmonicTensors_def]
  exact iInf_congr fun i => iInf_congr fun j => iInf_congr fun hij =>
    (ker_symplecticCupCapAt hij).symm

/-! ### The matrix of an arc -/

/-- **The matrix coefficients of an arc** in the monomial basis: the coefficient of `e_w` in the
image of `e_u` is `-(J (u i) (u j) * J (w i) (w j))` when `w` agrees with `u` off the two strands,
and `0` otherwise. The cap reads `J` off the two input labels and the cup writes `-J` at the two
output labels. -/
theorem piTensorProduct_repr_symplecticCupCapAt_piTensorProduct {i j : Fin d} (hij : i ≠ j)
    (u w : Fin d → Fin n ⊕ Fin n) :
    (Basis.piTensorProduct fun _ : Fin d => Pi.basisFun k (Fin n ⊕ Fin n)).repr
        (symplecticCupCapAt k n d i j
          (Basis.piTensorProduct (fun _ : Fin d => Pi.basisFun k (Fin n ⊕ Fin n)) u)) w =
      if ∀ t, t ≠ i → t ≠ j → w t = u t then
        -(Matrix.J (Fin n) k (u i) (u j) * Matrix.J (Fin n) k (w i) (w j))
      else 0 := by
  classical
  set b := Basis.piTensorProduct fun _ : Fin d => Pi.basisFun k (Fin n ⊕ Fin n)
  have hb (f : Fin d → Fin n ⊕ Fin n) : b f = PiTensorProduct.tprod k fun t =>
      (Pi.single (f t) (1 : k) : (Fin n ⊕ Fin n) → k) := by
    simp [b, Basis.piTensorProduct_apply]
  -- the basis tensor `e_w` is written by the cup exactly once, at the labels `w i` and `w j`,
  -- when `w` agrees with `u` off the two strands, and not at all otherwise
  have key (x y : Fin n ⊕ Fin n) : Function.update (Function.update u i x) j y = w ↔
      x = w i ∧ y = w j ∧ ∀ t, t ≠ i → t ≠ j → w t = u t := by
    refine ⟨fun h => ?_, fun ⟨hx, hy, h⟩ => funext fun t => ?_⟩
    · subst h
      simp only [Function.update_self, Function.update_of_ne hij, true_and]
      exact fun t hti htj => by simp [Function.update_of_ne hti, Function.update_of_ne htj]
    · rcases eq_or_ne t j with rfl | htj
      · rw [Function.update_self, hy]
      rcases eq_or_ne t i with rfl | hti
      · rw [Function.update_of_ne htj, Function.update_self, hx]
      · rw [Function.update_of_ne htj, Function.update_of_ne hti, h t hti htj]
  rw [hb, symplecticCupCapAt_tprod_single hij]
  simp only [← hb, map_neg, map_smul, map_sum, Finsupp.neg_apply, Finsupp.smul_apply,
    Finsupp.finsetSum_apply, Module.Basis.repr_self, Finsupp.single_apply, key, smul_eq_mul,
    mul_ite, mul_one, mul_zero, ite_and]
  split_ifs <;> simp

/-- **The matrix of an arc in the monomial basis is Hermitian**, for every star structure on `k`:
it is symmetric, by `TauCeti.piTensorProduct_repr_symplecticCupCapAt_piTensorProduct`, and its
entries are integers, which `star` fixes. So an arc is self-adjoint for the Hermitian form in which
the monomial basis is orthonormal. -/
theorem isHermitian_toMatrix_symplecticCupCapAt [StarRing k] {i j : Fin d} (hij : i ≠ j) :
    (LinearMap.toMatrix (Basis.piTensorProduct fun _ : Fin d => Pi.basisFun k (Fin n ⊕ Fin n))
      (Basis.piTensorProduct fun _ : Fin d => Pi.basisFun k (Fin n ⊕ Fin n))
      (symplecticCupCapAt k n d i j)).IsHermitian := by
  refine Matrix.IsHermitian.ext fun w u => ?_
  have hstar (a b : Fin n ⊕ Fin n) : star (Matrix.J (Fin n) k a b) = Matrix.J (Fin n) k a b := by
    rw [← Matrix.map_J (Fin n) (Int.castRingHom k), Matrix.map_apply, eq_intCast, star_intCast]
  have hsymm : (∀ t, t ≠ i → t ≠ j → u t = w t) ↔ (∀ t, t ≠ i → t ≠ j → w t = u t) :=
    ⟨fun h t hti htj => (h t hti htj).symm, fun h t hti htj => (h t hti htj).symm⟩
  rw [LinearMap.toMatrix_apply, LinearMap.toMatrix_apply,
    piTensorProduct_repr_symplecticCupCapAt_piTensorProduct hij,
    piTensorProduct_repr_symplecticCupCapAt_piTensorProduct hij]
  simp only [hsymm]
  split_ifs
  · rw [star_neg, star_mul', hstar, hstar, mul_comm]
  · exact star_zero k

/-! ### The trace tensors -/

section TraceTensors

variable (k n d)

/-- **The trace tensors** of `V^{⊗d}`: the sum of the images of the arcs
`TauCeti.symplecticCupCapAt k n d i j`, that is, of the tensors obtained by inserting the
invariant bivector of `-J` into some pair of distinct slots. It is a subrepresentation because
every arc commutes with the diagonal action of the symplectic group. On two strands it is the
trace line (`TauCeti.symplecticTraceTensors_two`). -/
noncomputable def symplecticTraceTensors :
    Subrepresentation ((stdSymplecticRep k n).tensorPower d) where
  toSubmodule := ⨆ (i : Fin d) (j : Fin d) (_ : i ≠ j),
    LinearMap.range (symplecticCupCapAt k n d i j)
  apply_mem_toSubmodule g := by
    suffices h : (⨆ (i : Fin d) (j : Fin d) (_ : i ≠ j),
        LinearMap.range (symplecticCupCapAt k n d i j)) ≤
        Submodule.comap ((stdSymplecticRep k n).tensorPower d g)
          (⨆ (i : Fin d) (j : Fin d) (_ : i ≠ j), LinearMap.range (symplecticCupCapAt k n d i j))
      from fun x hx => h hx
    refine iSup_le fun i => iSup_le fun j => iSup_le fun hij => ?_
    rintro _ ⟨y, rfl⟩
    have h := LinearMap.congr_fun (commute_symplecticCupCapAt_tensorPower g hij).eq y
    rw [Module.End.mul_apply, Module.End.mul_apply] at h
    rw [Submodule.mem_comap, ← h]
    exact Submodule.mem_iSup_of_mem i <| Submodule.mem_iSup_of_mem j <|
      Submodule.mem_iSup_of_mem hij <| LinearMap.mem_range_self _ _

@[simp]
theorem symplecticTraceTensors_toSubmodule :
    (symplecticTraceTensors k n d).toSubmodule =
      ⨆ (i : Fin d) (j : Fin d) (_ : i ≠ j), LinearMap.range (symplecticCupCapAt k n d i j) :=
  (rfl)

variable {k n d}

/-- The image of every arc consists of trace tensors. -/
theorem range_symplecticCupCapAt_le_symplecticTraceTensors {i j : Fin d} (hij : i ≠ j) :
    LinearMap.range (symplecticCupCapAt k n d i j) ≤ (symplecticTraceTensors k n d).toSubmodule :=
  le_iSup_of_le i <| le_iSup_of_le j <| le_iSup_of_le hij le_rfl

/-- The order-level universal property: the trace tensors lie in a submodule exactly when the
image of every arc does. -/
theorem symplecticTraceTensors_toSubmodule_le_iff
    {p : Submodule k (⨂[k]^d ((Fin n ⊕ Fin n) → k))} :
    (symplecticTraceTensors k n d).toSubmodule ≤ p ↔
      ∀ i j : Fin d, i ≠ j → LinearMap.range (symplecticCupCapAt k n d i j) ≤ p := by
  simp only [symplecticTraceTensors_toSubmodule, iSup_le_iff]

end TraceTensors

end CommRing

/-! ### The trace splitting -/

section StarOrderedField

variable (k n d)
variable [Field k] [PartialOrder k] [StarRing k] [StarOrderedRing k]

/-- **The harmonic tensors complement the images of the arcs** over a star-ordered field, such as
`ℚ`, `ℝ` or `ℂ` (with `ComplexOrder`): `V^{⊗d}` is the direct sum of the common kernel of the
contractions and the sum of the images of the arcs.

Some such hypothesis on `k` is needed: on two strands over a field in which `2n` is a nonzero
multiple of the characteristic, the cap kills the cup, so the trace line is a nonzero subspace of
the harmonic tensors. -/
theorem isCompl_symplecticHarmonicTensors_iSup_range_symplecticCupCapAt :
    IsCompl (symplecticHarmonicTensors k n d)
      (⨆ (i : Fin d) (j : Fin d) (_ : i ≠ j), LinearMap.range (symplecticCupCapAt k n d i j)) := by
  have h := LinearMap.isCompl_iInf_ker_iSup_range_of_isHermitian_toMatrix
    (Basis.piTensorProduct fun _ : Fin d => Pi.basisFun k (Fin n ⊕ Fin n))
    (fun p : {p : Fin d × Fin d // p.1 ≠ p.2} => symplecticCupCapAt k n d p.1.1 p.1.2)
    fun p => isHermitian_toMatrix_symplecticCupCapAt p.2
  simpa only [iInf_subtype, iSup_subtype, iInf_prod, iSup_prod,
    ← symplecticHarmonicTensors_eq_iInf_ker_symplecticCupCapAt] using h

/-- **The trace splitting of the symplectic tensor power.** Over a star-ordered field the
harmonic tensors and the trace tensors are complementary subrepresentations of `V^{⊗d}`, so
`Subrepresentation.equivProdOfIsCompl` presents `V^{⊗d}` as their direct sum. -/
theorem isCompl_symplecticHarmonicTensorsSubrep_symplecticTraceTensors :
    IsCompl (symplecticHarmonicTensorsSubrep k n d) (symplecticTraceTensors k n d) :=
  Subrepresentation.isCompl_toSubmodule.mp <| by
    rw [symplecticHarmonicTensorsSubrep_toSubmodule, symplecticTraceTensors_toSubmodule]
    exact isCompl_symplecticHarmonicTensors_iSup_range_symplecticCupCapAt k n d

end StarOrderedField

/-! ### Two strands -/

section TwoStrands

section CommRing

variable [CommRing k]

variable (k n)

/-- **The trace line** of the tensor square of the standard symplectic representation: the image
of the cup, the span of the invariant bivector `∑ₓ ∑_y (-J) x y • eₓ ⊗ e_y`. It is a
subrepresentation, on which the symplectic group acts trivially
(`TauCeti.tensorPower_apply_of_mem_symplecticTraceLine`), because the cup is invariant. -/
noncomputable def symplecticTraceLine :
    Subrepresentation ((stdSymplecticRep k n).tensorPower 2) where
  toSubmodule := LinearMap.range (symplecticCup k n)
  apply_mem_toSubmodule := by
    rintro g _ ⟨c, rfl⟩
    exact ⟨c, (LinearMap.congr_fun (tensorPower_comp_symplecticCup k n g) c).symm⟩

@[simp]
theorem symplecticTraceLine_toSubmodule :
    (symplecticTraceLine k n).toSubmodule = LinearMap.range (symplecticCup k n) :=
  (rfl)

variable {k n}

/-- A tensor lies on the trace line exactly when it is a scalar multiple of the invariant
bivector. -/
@[simp]
theorem mem_symplecticTraceLine_iff {x : ⨂[k]^2 ((Fin n ⊕ Fin n) → k)} :
    x ∈ symplecticTraceLine k n ↔ ∃ c : k, symplecticCup k n c = x := by
  rw [← Subrepresentation.mem_toSubmodule, symplecticTraceLine_toSubmodule, LinearMap.mem_range]

/-- **The symplectic group fixes the trace line pointwise**: the trace summand of the tensor
square is the trivial representation. -/
theorem tensorPower_apply_of_mem_symplecticTraceLine (g : Matrix.symplecticGroup (Fin n) k)
    {x : ⨂[k]^2 ((Fin n ⊕ Fin n) → k)} (hx : x ∈ symplecticTraceLine k n) :
    (stdSymplecticRep k n).tensorPower 2 g x = x := by
  obtain ⟨c, rfl⟩ := mem_symplecticTraceLine_iff.mp hx
  exact LinearMap.congr_fun (tensorPower_comp_symplecticCup k n g) c

variable (k n)

/-- **On two strands the trace tensors are the trace line**: the only arc is the Brauer generator
`e = cup ∘ cap`, whose image is that of the cup (`TauCeti.range_symplecticCupCap`). -/
theorem symplecticTraceTensors_two : symplecticTraceTensors k n 2 = symplecticTraceLine k n := by
  refine Subrepresentation.toSubmodule_injective (le_antisymm ?_ ?_)
  · rw [symplecticTraceTensors_toSubmodule_le_iff]
    intro i j hij
    rw [symplecticTraceLine_toSubmodule, ← range_symplecticCupCap, ← symplecticCupCapAt_zero_one]
    rcases (by decide : ∀ i j : Fin 2, i ≠ j → i = 0 ∧ j = 1 ∨ i = 1 ∧ j = 0) i j hij with
      ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact le_rfl
    · rw [symplecticCupCapAt_comm]
  · rw [symplecticTraceLine_toSubmodule, ← range_symplecticCupCap, ← symplecticCupCapAt_zero_one]
    exact range_symplecticCupCapAt_le_symplecticTraceTensors (by decide)

/-- **The trace splitting of the symplectic tensor square** when the loop value `-2n` is
invertible in `k`: `V ⊗ V` is the direct sum of the kernel of the cap, the harmonic tensors, and
the image of the cup, the trace line. Some such hypothesis is needed: where `(2n : k) = 0` the cap
kills the cup, so for `n ≠ 0` the trace line lies inside the harmonic tensors instead. -/
theorem isCompl_ker_symplecticCap_range_symplecticCup (hn : IsUnit (2 * n : k)) :
    IsCompl (LinearMap.ker (symplecticCap k n)) (LinearMap.range (symplecticCup k n)) := by
  obtain ⟨u, hu⟩ := hn.neg
  have hloop (c : k) : symplecticCap k n (symplecticCup k n c) = u * c := by
    rw [symplecticCap_comp_symplecticCup_apply, hu]
  refine ⟨Submodule.disjoint_def.mpr fun x hx hx' => ?_,
    Submodule.codisjoint_iff_exists_add_eq.mpr fun x => ?_⟩
  · obtain ⟨c, rfl⟩ := LinearMap.mem_range.mp hx'
    rw [LinearMap.mem_ker, hloop, Units.mul_right_eq_zero] at hx
    rw [hx, map_zero]
  · refine ⟨x - symplecticCup k n (↑u⁻¹ * symplecticCap k n x),
      symplecticCup k n (↑u⁻¹ * symplecticCap k n x), ?_, LinearMap.mem_range_self _ _,
      sub_add_cancel _ _⟩
    rw [LinearMap.mem_ker, map_sub, hloop, Units.mul_inv_cancel_left, sub_self]

/-- **The trace splitting of the symplectic tensor square** as representations: when `2n` is
invertible in `k`, the harmonic tensors and the trace line are complementary subrepresentations of
`V ⊗ V`. -/
theorem isCompl_symplecticHarmonicTensorsSubrep_symplecticTraceLine (hn : IsUnit (2 * n : k)) :
    IsCompl (symplecticHarmonicTensorsSubrep k n 2) (symplecticTraceLine k n) :=
  Subrepresentation.isCompl_toSubmodule.mp <| by
    rw [symplecticHarmonicTensorsSubrep_toSubmodule, symplecticTraceLine_toSubmodule,
      symplecticHarmonicTensors_two_eq_ker_symplecticCap]
    exact isCompl_ker_symplecticCap_range_symplecticCup k n hn

end CommRing

end TwoStrands

end TauCeti
