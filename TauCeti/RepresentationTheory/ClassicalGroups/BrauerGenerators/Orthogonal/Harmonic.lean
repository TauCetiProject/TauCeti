/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.ClassicalGroups.BrauerGenerators.Orthogonal.TensorPower

/-!
# The harmonic (traceless) tensors of a tensor power

Let `V = kⁿ` carry the coordinate dot product. A Brauer diagram with a horizontal arc acts on
`V^{⊗d}` through the single-arc generators `TauCeti.orthogonalCupCapAt k n d i j`, which contract
the slots `i` and `j` against the form and re-expand them against its copairing. The **harmonic**
(traceless) tensors are the tensors annihilated by every one of those arcs:

`TauCeti.harmonicTensors k n d = ⨅_{i ≠ j} ker (orthogonalCupCapAt k n d i j)`.

Because the cup is injective as soon as `V ≠ 0`
(`TauCeti.orthogonalCup_injective`), an arc annihilates a tensor exactly when the cap alone does,
so this is the common kernel of the contraction maps, and on two strands it is literally the
kernel of the cap (`TauCeti.harmonicTensors_two_eq_ker_orthogonalCap`).

## Why this submodule

The arcs are exactly the generators of the Brauer algebra that are not permutations, so the
harmonic tensors are the part of `V^{⊗d}` on which the diagram action factors through the
permutation quotient alone, and they are stable under *both* of the commuting actions: under the
orthogonal group because the arcs commute with it
(`TauCeti.commute_orthogonalCupCapAt_tensorPower`), and under the symmetric group because
permuting strands only renames the arc (`TauCeti.permTensorAction_mul_orthogonalCupCapAt`). The
orthogonal stability is packaged as `TauCeti.harmonicTensorsSubrep`.

Harmonic tensors are not themselves one irreducible. The classical reason to single them out is
the Brauer duality over `ℂ`, where the two actions are each other's centralizers and the
degree-`d` harmonic tensors are cut shape by shape into irreducible orthogonal modules — subject
to the usual constraints tying the partition to `n` — which is why the symmetric-group stability
matters. Those pieces are only the constituents of `V^{⊗d}` that are new in degree `d`: the
others are the constituents of the harmonic tensors of degrees `d - 2`, `d - 4`, ..., re-inserted
by cups, so for `V = ℂ³` and `d = 2` the trivial module spanned by the cup `∑ⱼ eⱼ ⊗ eⱼ` occurs in
`V^{⊗2}` but not in its harmonic part. Neither that duality nor any such decomposition is proved
here, and over the general coefficient rings this file is stated over no such statement is
available.
What is proved here are two bounds on how the harmonic part sits against the part the arcs rebuild
from cups on lower tensor powers. An arc acts on its own image by the loop value `n`, so a
harmonic tensor in the image of an arc vanishes whenever `n` is invertible
(`TauCeti.harmonicTensors_inf_range_orthogonalCupCapAt`); and in the opposite direction, a tensor
on which every transposition of strands acts by `-1` is harmonic when `2` is invertible
(`TauCeti.mem_harmonicTensors_of_forall_swap_eq_neg`), because an arc absorbs the crossing of its
own two strands. On two strands the second statement says that the antisymmetric square sits
inside the traceless tensors, the `⋀²` summand of the decomposition
`(ℂ³)^{⊗2} ≅ Sym²₀ ⊕ ⋀² ⊕ ℂ`.

Nothing here needs subtraction except the two statements that mention `-1` and the orthogonal
group, so the definition and most of its API are stated over a commutative semiring.

## Main definitions

* `TauCeti.harmonicTensors`: the harmonic (traceless) tensors, the common kernel of the single-arc
  Brauer generators.
* `TauCeti.harmonicTensorsSubrep`: the harmonic tensors as a subrepresentation of the diagonal
  action of the orthogonal group on `V^{⊗d}`.

## Main results

* `TauCeti.harmonicTensors_def` and `TauCeti.le_harmonicTensors_iff`: the defining infimum of
  kernels, and the order-level universal property it gives.
* `TauCeti.mem_harmonicTensors` and
  `TauCeti.orthogonalCupCapAt_apply_eq_zero_of_mem_harmonicTensors`: membership is the vanishing
  of every arc.
* `TauCeti.tprod_mem_harmonicTensors`: a pure tensor whose factors are pairwise orthogonal is
  harmonic.
* `TauCeti.harmonicTensors_eq_top_of_le_one`: on at most one strand there is no arc, so every
  tensor is harmonic.
* `TauCeti.harmonicTensors_two_eq_ker_orthogonalCupCap` and
  `TauCeti.harmonicTensors_two_eq_ker_orthogonalCap`: on two strands the harmonic tensors are the
  kernel of the single arc, and hence of the cap alone -- the traceless tensors.
* `TauCeti.permTensorAction_mem_harmonicTensors` and
  `TauCeti.map_permTensorAction_harmonicTensors`: the harmonic tensors are stable under permuting
  the strands.
* `TauCeti.tensorPower_mem_harmonicTensors` and `TauCeti.map_tensorPower_harmonicTensors`: the
  harmonic tensors are stable under the diagonal action of the orthogonal group.
* `TauCeti.harmonicTensors_inf_range_orthogonalCupCapAt`: at an invertible loop value the harmonic
  tensors meet the image of an arc only in zero.
* `TauCeti.mem_harmonicTensors_of_forall_swap_eq_neg`: with `2` invertible, a tensor negated by
  every transposition of strands is harmonic.

## References

* R. Goodman and N. R. Wallach, *Symmetry, Representations, and Invariants*, Springer GTM 255
  (2009), Chapter 10, for the harmonic (traceless) tensors and the trace filtration.
-/

public section

open Matrix
open scoped TensorProduct

universe u

namespace TauCeti

variable (k : Type u) (n d : ℕ)

section CommSemiring

variable [CommSemiring k]

/-- **The harmonic (traceless) tensors** of `V^{⊗d}` for `V = kⁿ` with the coordinate dot product:
the tensors annihilated by every single-arc Brauer generator, that is, by the contraction of each
pair of distinct slots against the form. Coincident slots are excluded because
`TauCeti.orthogonalCupCapAt k n d i i` is not an arc of a Brauer diagram. -/
noncomputable def harmonicTensors : Submodule k (⨂[k]^d (Fin n → k)) :=
  ⨅ i : Fin d, ⨅ j : Fin d, ⨅ _ : i ≠ j, LinearMap.ker (orthogonalCupCapAt k n d i j)

/-- The defining description of the harmonic tensors as an infimum of kernels. -/
theorem harmonicTensors_def :
    harmonicTensors k n d =
      ⨅ i : Fin d, ⨅ j : Fin d, ⨅ _ : i ≠ j, LinearMap.ker (orthogonalCupCapAt k n d i j) :=
  (rfl)

variable {k n d}

/-- The order-level universal property: a submodule is contained in the harmonic tensors exactly
when every arc kills it. -/
theorem le_harmonicTensors_iff {p : Submodule k (⨂[k]^d (Fin n → k))} :
    p ≤ harmonicTensors k n d ↔
      ∀ i j : Fin d, i ≠ j → p ≤ LinearMap.ker (orthogonalCupCapAt k n d i j) := by
  simp only [harmonicTensors_def, le_iInf_iff]

/-- A tensor is harmonic exactly when every arc annihilates it. -/
@[simp]
theorem mem_harmonicTensors {x : ⨂[k]^d (Fin n → k)} :
    x ∈ harmonicTensors k n d ↔
      ∀ i j : Fin d, i ≠ j → orthogonalCupCapAt k n d i j x = 0 := by
  simp only [harmonicTensors_def, Submodule.mem_iInf, LinearMap.mem_ker]

/-- Every arc annihilates a harmonic tensor. -/
theorem orthogonalCupCapAt_apply_eq_zero_of_mem_harmonicTensors
    {x : ⨂[k]^d (Fin n → k)} (hx : x ∈ harmonicTensors k n d) {i j : Fin d} (hij : i ≠ j) :
    orthogonalCupCapAt k n d i j x = 0 :=
  mem_harmonicTensors.mp hx i j hij

/-- **A pure tensor with pairwise orthogonal factors is harmonic**: an arc contracts its two
slots against the form, and that contraction is the scalar the arc multiplies by. In particular
the harmonic tensors are nonzero as soon as some *nonzero* pure tensor of the degree at hand has
pairwise orthogonal factors, which for `d` strands asks for `d` pairwise orthogonal vectors and so
says nothing once `d` exceeds the supply of those in `V`. -/
theorem tprod_mem_harmonicTensors {v : Fin d → (Fin n → k)}
    (hv : ∀ i j : Fin d, i ≠ j → v i ⬝ᵥ v j = 0) :
    PiTensorProduct.tprod k v ∈ harmonicTensors k n d := by
  refine mem_harmonicTensors.mpr fun i j hij => ?_
  rw [orthogonalCupCapAt_tprod hij, hv i j hij, zero_smul]

/-- On at most one strand a Brauer diagram has no arc, so every tensor is harmonic. -/
theorem harmonicTensors_eq_top_of_le_one (hd : d ≤ 1) : harmonicTensors k n d = ⊤ := by
  refine eq_top_iff.mpr fun x _ => mem_harmonicTensors.mpr fun i j hij => absurd ?_ hij
  have hi := i.isLt
  have hj := j.isLt
  exact Fin.ext (by omega)

/-- On two strands there is a single arc, joining the two of them, so the harmonic tensors are
the kernel of the Brauer generator `e`. -/
theorem harmonicTensors_two_eq_ker_orthogonalCupCap :
    harmonicTensors k n 2 = LinearMap.ker (orthogonalCupCap k n) := by
  have hpair : ∀ i j : Fin 2, i ≠ j → i = 0 ∧ j = 1 ∨ i = 1 ∧ j = 0 := by decide
  ext x
  rw [mem_harmonicTensors, LinearMap.mem_ker]
  constructor
  · intro h
    rw [← orthogonalCupCapAt_zero_one]
    exact h 0 1 (by decide)
  · intro h i j hij
    have key : orthogonalCupCapAt k n 2 0 1 x = 0 := by rwa [orthogonalCupCapAt_zero_one]
    rcases hpair i j hij with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact key
    · rw [orthogonalCupCapAt_comm]
      exact key

/-- **On two strands the harmonic tensors are the traceless tensors**: the kernel of the cap, the
contraction of the two slots against the coordinate dot product. The arc is the cap followed by a
cup, and the cup is injective for `V ≠ 0`, so the two kernels agree; in dimension zero the cap is
itself the zero map and both kernels are everything. -/
theorem harmonicTensors_two_eq_ker_orthogonalCap :
    harmonicTensors k n 2 = LinearMap.ker (orthogonalCap k n) := by
  rw [harmonicTensors_two_eq_ker_orthogonalCupCap]
  ext x
  simp only [LinearMap.mem_ker, orthogonalCupCap_apply]
  refine ⟨fun h => ?_, fun h => by rw [h, map_zero]⟩
  rcases eq_zero_or_neZero n with rfl | hn
  · have hcap : orthogonalCap k 0 = 0 := by
      ext v
      simp
    simp [hcap]
  · exact orthogonalCup_injective k n (by rw [h, map_zero])

/-! ### Stability under the two actions -/

/-- Permuting the strands preserves harmonicity: a permutation renames the arc. -/
theorem permTensorAction_mem_harmonicTensors (σ : Equiv.Perm (Fin d))
    {x : ⨂[k]^d (Fin n → k)} (hx : x ∈ harmonicTensors k n d) :
    permTensorAction k n d σ x ∈ harmonicTensors k n d := by
  refine mem_harmonicTensors.mpr fun i j hij => ?_
  have hinv : σ.symm i ≠ σ.symm j := σ.symm.injective.ne hij
  have h := permTensorAction_mul_orthogonalCupCapAt (k := k) (n := n) (d := d) σ
    (σ.symm i) (σ.symm j)
  rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply] at h
  have h2 := LinearMap.congr_fun h x
  rw [Module.End.mul_apply, Module.End.mul_apply] at h2
  rw [← h2, orthogonalCupCapAt_apply_eq_zero_of_mem_harmonicTensors hx hinv, map_zero]

/-- The harmonic tensors are a submodule stable under permutations of the strands. -/
theorem map_permTensorAction_harmonicTensors (σ : Equiv.Perm (Fin d)) :
    Submodule.map (permTensorAction k n d σ) (harmonicTensors k n d) = harmonicTensors k n d := by
  refine le_antisymm ?_ fun x hx => ?_
  · rintro y ⟨z, hz, rfl⟩
    exact permTensorAction_mem_harmonicTensors σ hz
  · refine ⟨permTensorAction k n d σ⁻¹ x, permTensorAction_mem_harmonicTensors σ⁻¹ hx, ?_⟩
    rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]

/-! ### The harmonic tensors against the image of an arc -/

/-- **At an invertible loop value the harmonic tensors avoid the image of an arc.** An arc acts on
its own image by the loop value `n`, so a harmonic tensor in that image is `n⁻¹` times zero. This
is the easy half of the statement that the trace filtration of `V^{⊗d}` splits off its harmonic
part in the semisimple range. -/
theorem harmonicTensors_inf_range_orthogonalCupCapAt [Invertible (n : k)] {i j : Fin d}
    (hij : i ≠ j) :
    harmonicTensors k n d ⊓ LinearMap.range (orthogonalCupCapAt k n d i j) = ⊥ := by
  refine le_antisymm (fun x hx => ?_) bot_le
  obtain ⟨hharm, y, rfl⟩ := hx
  have hself := LinearMap.congr_fun (orthogonalCupCapAt_mul_self (k := k) (n := n) (d := d) hij) y
  rw [Module.End.mul_apply, LinearMap.smul_apply] at hself
  have hzero : (n : k) • orthogonalCupCapAt k n d i j y = 0 := by
    rw [← hself]
    exact orthogonalCupCapAt_apply_eq_zero_of_mem_harmonicTensors hharm hij
  have : orthogonalCupCapAt k n d i j y = 0 := by
    calc orthogonalCupCapAt k n d i j y
        = ⅟(n : k) • ((n : k) • orthogonalCupCapAt k n d i j y) := by
          rw [smul_smul, invOf_mul_self, one_smul]
      _ = 0 := by rw [hzero, smul_zero]
  exact (Submodule.mem_bot k).mpr this

end CommSemiring

section CommRing

variable {k n d} [CommRing k]

/-- **A tensor negated by every transposition of strands is harmonic**, provided `2` is
invertible: an arc absorbs the crossing of its own two strands, so its value on such a tensor `x`
is its value on `-x`, namely minus itself; with `2` invertible that value is therefore zero. On
two strands this says that the antisymmetric square is traceless for the symmetric form. -/
theorem mem_harmonicTensors_of_forall_swap_eq_neg [Invertible (2 : k)]
    {x : ⨂[k]^d (Fin n → k)}
    (hx : ∀ i j : Fin d, i ≠ j → permTensorAction k n d (Equiv.swap i j) x = -x) :
    x ∈ harmonicTensors k n d := by
  refine mem_harmonicTensors.mpr fun i j hij => ?_
  have habsorb := LinearMap.congr_fun
    (orthogonalCupCapAt_mul_permTensorAction_swap (k := k) (n := n) (d := d) i j) x
  rw [Module.End.mul_apply, hx i j hij, map_neg] at habsorb
  have hsum : (2 : k) • orthogonalCupCapAt k n d i j x = 0 := by
    have hdouble : orthogonalCupCapAt k n d i j x + orthogonalCupCapAt k n d i j x = 0 := by
      nth_rewrite 1 [← habsorb]
      exact neg_add_cancel _
    rwa [two_smul]
  calc orthogonalCupCapAt k n d i j x
      = ⅟(2 : k) • ((2 : k) • orthogonalCupCapAt k n d i j x) := by
        rw [smul_smul, invOf_mul_self, one_smul]
    _ = 0 := by rw [hsum, smul_zero]

/-- The diagonal action of the orthogonal group preserves harmonicity: every arc commutes with
that action. -/
theorem tensorPower_mem_harmonicTensors (g : Matrix.orthogonalGroup (Fin n) k)
    {x : ⨂[k]^d (Fin n → k)} (hx : x ∈ harmonicTensors k n d) :
    (stdOrthogonalRep k n).tensorPower d g x ∈ harmonicTensors k n d := by
  refine mem_harmonicTensors.mpr fun i j hij => ?_
  have h := LinearMap.congr_fun
    (commute_orthogonalCupCapAt_tensorPower k n d g hij) x
  rw [Module.End.mul_apply, Module.End.mul_apply] at h
  rw [h, orthogonalCupCapAt_apply_eq_zero_of_mem_harmonicTensors hx hij, map_zero]

/-- The harmonic tensors are a submodule stable under the diagonal action of the orthogonal
group. -/
theorem map_tensorPower_harmonicTensors (g : Matrix.orthogonalGroup (Fin n) k) :
    Submodule.map ((stdOrthogonalRep k n).tensorPower d g) (harmonicTensors k n d) =
      harmonicTensors k n d := by
  refine le_antisymm ?_ fun x hx => ?_
  · rintro y ⟨z, hz, rfl⟩
    exact tensorPower_mem_harmonicTensors g hz
  · refine ⟨(stdOrthogonalRep k n).tensorPower d g⁻¹ x,
      tensorPower_mem_harmonicTensors g⁻¹ hx, ?_⟩
    rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]

variable (k n d)

/-- **The harmonic tensors as an orthogonal subrepresentation of `V^{⊗d}`.** Over `ℂ` this is
classically the module whose shape-`λ` pieces are the irreducible representations of the
orthogonal group that occur in `V^{⊗d}` for the first time in degree `d`; the constituents
inherited from the lower degrees by cup insertion are not among them. That decomposition is not
proved here, and the statement below is only the stability of the submodule under the action. -/
noncomputable def harmonicTensorsSubrep :
    Subrepresentation ((stdOrthogonalRep k n).tensorPower d) where
  toSubmodule := harmonicTensors k n d
  apply_mem_toSubmodule g _ hx := tensorPower_mem_harmonicTensors g hx

@[simp]
theorem harmonicTensorsSubrep_toSubmodule :
    (harmonicTensorsSubrep k n d).toSubmodule = harmonicTensors k n d :=
  (rfl)

end CommRing

end TauCeti
