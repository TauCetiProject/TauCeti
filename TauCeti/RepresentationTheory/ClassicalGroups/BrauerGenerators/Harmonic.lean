/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Projection
public import Mathlib.RepresentationTheory.Subrepresentation
public import TauCeti.RepresentationTheory.ClassicalGroups.BrauerGenerators.Orthogonal

/-!
# Harmonic tensors and the trace line on two strands

The Brauer generator `e = cup ∘ cap` of
`TauCeti/RepresentationTheory/ClassicalGroups/BrauerGenerators/Orthogonal.lean` satisfies
`e * e = n • e` on `V^{⊗2}` for `V = kⁿ` with the coordinate dot product, so as soon as the loop
value `n` is invertible the rescaling `e / n` is idempotent.  Its kernel and its image are the two
pieces of the **trace splitting** of the tensor square,

`V ⊗ V = harmonic ⊕ trace line`,

where the **harmonic** (traceless) tensors are the ones the cap annihilates and the **trace line**
is the image of the cup.  Both are stable under the orthogonal group, because the cap and the cup
are; on the trace line the action is in fact trivial, the invariant bivector spanning it being
fixed.  This is the first, two-strand, instance of the trace filtration of `V^{⊗k}` cut out by the
horizontal arcs of a Brauer diagram, and the trace line is exactly the summand that is absent from
the general-linear decomposition `V^{⊗2} ≅ Sym²V ⊕ ⋀²V` of
`TauCeti/RepresentationTheory/ClassicalGroups/Decomposition.lean`: breaking `GLₙ` to `Oₙ` by
fixing the invariant form is what makes the trace a subrepresentation.

The counting is `1 + (n² - 1) = n²`: the trace line is a line, and the harmonic tensors are a
hyperplane.  Antisymmetric tensors are harmonic
(`TauCeti.tprod_sub_swap_mem_orthogonalHarmonic`), so for `n = 3` the harmonic hyperplane is the
`8`-dimensional sum of the `3`-dimensional antisymmetric and the `5`-dimensional traceless
symmetric parts.  The further splitting of the harmonic tensors into those two pieces needs the
symmetric and exterior squares and is not proved here, and neither is the symplectic mirror, where
the cap and the cup of
`TauCeti/RepresentationTheory/ClassicalGroups/BrauerGenerators/Symplectic.lean` have loop value
`-2n`.

## Main definitions

* `TauCeti.orthogonalHarmonic`: the harmonic (traceless) tensors, the kernel of the cap.
* `TauCeti.orthogonalTraceLine`: the trace line, the image of the cup.
* `TauCeti.orthogonalHarmonicSubrep` and `TauCeti.orthogonalTraceLineSubrep`: the two pieces as
  subrepresentations of the diagonal orthogonal action on the tensor square.
* `TauCeti.orthogonalTraceProj`: the rescaled Brauer generator `e / n`, the projection onto the
  trace line along the harmonic tensors.

## Main results

* `TauCeti.finrank_tensorPower`: the dimension `n ^ d` of `(kⁿ)^{⊗d}`.
* `TauCeti.tensorPower_apply_of_mem_orthogonalTraceLine`: the orthogonal group fixes the trace
  line pointwise.
* `TauCeti.ker_orthogonalCupCap` and `TauCeti.range_orthogonalCupCap`: the diagrammatic reading of
  the two pieces, as the kernel and the image of the generator `e` itself.
* `TauCeti.isCompl_orthogonalTraceLine_orthogonalHarmonic`: **the trace splitting.**
* `TauCeti.finrank_orthogonalTraceLine` and `TauCeti.finrank_orthogonalHarmonic_add_one`: the
  dimensions, `1` and `n² - 1`.
* `TauCeti.finrank_orthogonalHarmonic_three`: the acceptance count `8` for `n = 3`.

## References

* R. Goodman and N. R. Wallach, *Symmetry, Representations, and Invariants*, Springer GTM 255
  (2009), Chapter 10, for harmonic tensors and the trace-free decomposition.
* [Schur--Weyl roadmap](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/RepresentationTheory/SchurWeyl/README.md),
  Layer 9, "Harmonic tensors and the trace maps", and the worked example "Brauer duality on
  `(ℂ³)^{⊗2}` for `O(3)`".
-/

public section

open Matrix
open scoped TensorProduct

universe u

namespace TauCeti

/-- **The dimension of the tensor power `(kⁿ)^{⊗d}` is `n ^ d`**, read off the monomial basis
`TauCeti.tensorPowerBasis`. -/
theorem finrank_tensorPower (k : Type u) [Field k] (n d : ℕ) :
    Module.finrank k (⨂[k]^d (Fin n → k)) = n ^ d := by
  rw [Module.finrank_eq_card_basis (tensorPowerBasis k n d)]
  simp

variable (k : Type u) (n : ℕ)

section CommRing

variable [CommRing k]

/-! ### The two pieces -/

/-- **The harmonic (traceless) tensors** of the tensor square: the tensors the cap annihilates.
On two strands there is only one pair of slots to contract, so this is already the common kernel
of all the contractions, the two-strand case of the harmonic tensors of a general tensor power. -/
noncomputable def orthogonalHarmonic : Submodule k (⨂[k]^2 (Fin n → k)) :=
  LinearMap.ker (orthogonalCap k n)

/-- The harmonic tensors are, by definition, the kernel of the cap. -/
theorem orthogonalHarmonic_def :
    orthogonalHarmonic k n = LinearMap.ker (orthogonalCap k n) :=
  (rfl)

/-- A tensor of the square is harmonic exactly when the cap annihilates it. -/
theorem mem_orthogonalHarmonic_iff {x : ⨂[k]^2 (Fin n → k)} :
    x ∈ orthogonalHarmonic k n ↔ orthogonalCap k n x = 0 :=
  LinearMap.mem_ker

/-- **The trace line** of the tensor square: the image of the cup, spanned by the invariant
bivector `∑ⱼ eⱼ ⊗ eⱼ`.  It is the summand the invariant form contributes, and the one the
general-linear decomposition `V^{⊗2} ≅ Sym²V ⊕ ⋀²V` does not see. -/
noncomputable def orthogonalTraceLine : Submodule k (⨂[k]^2 (Fin n → k)) :=
  LinearMap.range (orthogonalCup k n)

/-- The trace line is, by definition, the image of the cup. -/
theorem orthogonalTraceLine_def :
    orthogonalTraceLine k n = LinearMap.range (orthogonalCup k n) :=
  (rfl)

-- Not a `simp` lemma: `TauCeti.orthogonalCup_apply` rewrites the left-hand side first, expanding
-- the cup into the invariant bivector, so `simpNF` reports this form as not simp-normal.
/-- Every cup lies in the trace line. -/
theorem orthogonalCup_mem_orthogonalTraceLine (c : k) :
    orthogonalCup k n c ∈ orthogonalTraceLine k n :=
  LinearMap.mem_range_self _ c

/-- **An antisymmetric tensor is harmonic.**  The cap is the dot product, which is symmetric, so it
kills every difference `v ⊗ w - w ⊗ v`; this is the inclusion of the exterior square in the
harmonic tensors. -/
theorem tprod_sub_swap_mem_orthogonalHarmonic (v w : Fin n → k) :
    PiTensorProduct.tprod k ![v, w] - PiTensorProduct.tprod k ![w, v] ∈
      orthogonalHarmonic k n := by
  rw [mem_orthogonalHarmonic_iff, map_sub, orthogonalCap_tprod, orthogonalCap_tprod]
  simp [dotProduct_comm v w]

/-! ### The two pieces are subrepresentations -/

/-- **The harmonic tensors are stable** under the diagonal orthogonal action, because the cap
is invariant. -/
theorem tensorPower_apply_mem_orthogonalHarmonic (g : Matrix.orthogonalGroup (Fin n) k)
    {x : ⨂[k]^2 (Fin n → k)} (hx : x ∈ orthogonalHarmonic k n) :
    (stdOrthogonalRep k n).tensorPower 2 g x ∈ orthogonalHarmonic k n := by
  rw [mem_orthogonalHarmonic_iff, ← LinearMap.comp_apply, orthogonalCap_comp_tensorPower]
  exact (mem_orthogonalHarmonic_iff k n).mp hx

/-- **The orthogonal group fixes the trace line pointwise**: the invariant bivector spanning it is
an invariant vector, so the trace summand is a trivial subrepresentation. -/
theorem tensorPower_apply_of_mem_orthogonalTraceLine (g : Matrix.orthogonalGroup (Fin n) k)
    {x : ⨂[k]^2 (Fin n → k)} (hx : x ∈ orthogonalTraceLine k n) :
    (stdOrthogonalRep k n).tensorPower 2 g x = x := by
  obtain ⟨c, rfl⟩ := hx
  rw [← LinearMap.comp_apply, tensorPower_comp_orthogonalCup]

/-- **The trace line is stable** under the diagonal orthogonal action; by
`TauCeti.tensorPower_apply_of_mem_orthogonalTraceLine` it is even fixed pointwise. -/
theorem tensorPower_apply_mem_orthogonalTraceLine (g : Matrix.orthogonalGroup (Fin n) k)
    {x : ⨂[k]^2 (Fin n → k)} (hx : x ∈ orthogonalTraceLine k n) :
    (stdOrthogonalRep k n).tensorPower 2 g x ∈ orthogonalTraceLine k n := by
  rw [tensorPower_apply_of_mem_orthogonalTraceLine k n g hx]
  exact hx

/-- The harmonic tensors as a subrepresentation of the diagonal orthogonal action. -/
noncomputable def orthogonalHarmonicSubrep :
    Subrepresentation ((stdOrthogonalRep k n).tensorPower 2) where
  toSubmodule := orthogonalHarmonic k n
  apply_mem_toSubmodule g _ hx := tensorPower_apply_mem_orthogonalHarmonic k n g hx

/-- The submodule underlying the harmonic subrepresentation. -/
@[simp]
theorem orthogonalHarmonicSubrep_toSubmodule :
    (orthogonalHarmonicSubrep k n).toSubmodule = orthogonalHarmonic k n :=
  (rfl)

/-- The trace line as a subrepresentation of the diagonal orthogonal action. -/
noncomputable def orthogonalTraceLineSubrep :
    Subrepresentation ((stdOrthogonalRep k n).tensorPower 2) where
  toSubmodule := orthogonalTraceLine k n
  apply_mem_toSubmodule g _ hx := tensorPower_apply_mem_orthogonalTraceLine k n g hx

/-- The submodule underlying the trace-line subrepresentation. -/
@[simp]
theorem orthogonalTraceLineSubrep_toSubmodule :
    (orthogonalTraceLineSubrep k n).toSubmodule = orthogonalTraceLine k n :=
  (rfl)

/-! ### The trace projection and the splitting -/

section Invertible

variable [Invertible (n : k)]

/-- **The cup is injective** once the loop value is invertible: capping a cup back off multiplies
by `n`. -/
theorem orthogonalCup_injective : Function.Injective (orthogonalCup k n) := by
  intro c d h
  have h' : ⅟(n : k) * ((n : k) * c) = ⅟(n : k) * ((n : k) * d) := by
    rw [← orthogonalCap_comp_orthogonalCup_apply k n c,
      ← orthogonalCap_comp_orthogonalCup_apply k n d, h]
  rwa [invOf_mul_cancel_left, invOf_mul_cancel_left] at h'

/-- **The cap is surjective** once the loop value is invertible. -/
theorem orthogonalCap_surjective : Function.Surjective (orthogonalCap k n) := fun c =>
  ⟨orthogonalCup k n (⅟(n : k) * c), by
    rw [orthogonalCap_comp_orthogonalCup_apply, mul_invOf_cancel_left]⟩

/-- The kernel of the Brauer generator `e` is the harmonic tensors: the cup is injective, so
capping and cupping back destroys no more information than the cap already does. -/
theorem ker_orthogonalCupCap :
    LinearMap.ker (orthogonalCupCap k n) = orthogonalHarmonic k n := by
  refine le_antisymm (fun x hx => ?_) fun x hx => ?_
  · refine (mem_orthogonalHarmonic_iff k n).mpr (orthogonalCup_injective k n ?_)
    rw [map_zero, ← orthogonalCupCap_apply]
    exact LinearMap.mem_ker.mp hx
  · rw [LinearMap.mem_ker, orthogonalCupCap_apply, (mem_orthogonalHarmonic_iff k n).mp hx, map_zero]

/-- The image of the Brauer generator `e` is the trace line.  Together with
`TauCeti.ker_orthogonalCupCap` this is the diagrammatic reading of the trace splitting: the
horizontal arc of `e` cuts out the trace summand and kills the harmonic one. -/
theorem range_orthogonalCupCap :
    LinearMap.range (orthogonalCupCap k n) = orthogonalTraceLine k n := by
  refine le_antisymm ?_ fun x hx => ?_
  · rintro x ⟨y, rfl⟩
    rw [orthogonalCupCap_apply]
    exact orthogonalCup_mem_orthogonalTraceLine k n _
  · obtain ⟨c, rfl⟩ := hx
    refine ⟨orthogonalCup k n (⅟(n : k) * c), ?_⟩
    rw [orthogonalCupCap_apply, orthogonalCap_comp_orthogonalCup_apply, mul_invOf_cancel_left]

/-- **The trace projection** `e / n`, the Brauer generator rescaled so as to be idempotent.  The
rescaling is where the invertibility of the loop value enters. -/
noncomputable def orthogonalTraceProj : Module.End k (⨂[k]^2 (Fin n → k)) :=
  ⅟(n : k) • orthogonalCupCap k n

/-- The trace projection caps a tensor off, rescales by `⅟n`, and cups the result back. -/
theorem orthogonalTraceProj_apply (x : ⨂[k]^2 (Fin n → k)) :
    orthogonalTraceProj k n x = orthogonalCup k n (⅟(n : k) * orthogonalCap k n x) := by
  rw [orthogonalTraceProj, LinearMap.smul_apply, orthogonalCupCap_apply, ← map_smul, smul_eq_mul]

/-- **The trace projection is idempotent**: this is the Brauer relation `e * e = n • e` divided
by `n ^ 2`. -/
theorem isIdempotentElem_orthogonalTraceProj : IsIdempotentElem (orthogonalTraceProj k n) := by
  have h : orthogonalTraceProj k n * orthogonalTraceProj k n =
      (⅟(n : k) * ⅟(n : k) * (n : k)) • orthogonalCupCap k n := by
    rw [orthogonalTraceProj, smul_mul_assoc, mul_smul_comm, orthogonalCupCap_mul_self, smul_smul,
      smul_smul]
  rw [IsIdempotentElem, h, invOf_mul_cancel_right, orthogonalTraceProj]

/-- The kernel of the trace projection is the harmonic tensors. -/
theorem ker_orthogonalTraceProj :
    LinearMap.ker (orthogonalTraceProj k n) = orthogonalHarmonic k n := by
  refine le_antisymm (fun x hx => ?_) fun x hx => ?_
  · have h : ⅟(n : k) * orthogonalCap k n x = 0 :=
      orthogonalCup_injective k n (by
        rw [map_zero, ← orthogonalTraceProj_apply]
        exact LinearMap.mem_ker.mp hx)
    refine (mem_orthogonalHarmonic_iff k n).mpr ?_
    calc orthogonalCap k n x
        = (n : k) * (⅟(n : k) * orthogonalCap k n x) := (mul_invOf_cancel_left _ _).symm
      _ = 0 := by rw [h, mul_zero]
  · rw [LinearMap.mem_ker, orthogonalTraceProj_apply, (mem_orthogonalHarmonic_iff k n).mp hx,
      mul_zero, map_zero]

/-- The image of the trace projection is the trace line. -/
theorem range_orthogonalTraceProj :
    LinearMap.range (orthogonalTraceProj k n) = orthogonalTraceLine k n := by
  refine le_antisymm ?_ fun x hx => ?_
  · rintro x ⟨y, rfl⟩
    rw [orthogonalTraceProj_apply]
    exact orthogonalCup_mem_orthogonalTraceLine k n _
  · obtain ⟨c, rfl⟩ := hx
    refine ⟨orthogonalCup k n c, ?_⟩
    rw [orthogonalTraceProj_apply, orthogonalCap_comp_orthogonalCup_apply, invOf_mul_cancel_left]

/-- **The trace splitting of the tensor square.**  When the loop value `n` is invertible the tensor
square is the direct sum of the trace line and the harmonic tensors, the two being the image and
the kernel of the idempotent `e / n`. -/
theorem isCompl_orthogonalTraceLine_orthogonalHarmonic :
    IsCompl (orthogonalTraceLine k n) (orthogonalHarmonic k n) := by
  rw [← range_orthogonalTraceProj, ← ker_orthogonalTraceProj]
  exact LinearMap.IsIdempotentElem.isCompl (isIdempotentElem_orthogonalTraceProj k n)

end Invertible

end CommRing

section Field

variable [Field k] [Invertible (n : k)]

/-- **The trace line is a line.** -/
theorem finrank_orthogonalTraceLine : Module.finrank k (orthogonalTraceLine k n) = 1 := by
  rw [orthogonalTraceLine_def,
    ← (LinearEquiv.ofInjective (orthogonalCup k n) (orthogonalCup_injective k n)).finrank_eq,
    Module.finrank_self]

/-- **The harmonic tensors are a hyperplane** of the tensor square, of dimension `n² - 1`, stated
without subtraction. -/
theorem finrank_orthogonalHarmonic_add_one :
    Module.finrank k (orthogonalHarmonic k n) + 1 = n ^ 2 := by
  have h := Submodule.finrank_add_eq_of_isCompl
    (isCompl_orthogonalTraceLine_orthogonalHarmonic k n)
  rw [finrank_orthogonalTraceLine, finrank_tensorPower] at h
  omega

/-- The subtracted form of `TauCeti.finrank_orthogonalHarmonic_add_one`. -/
theorem finrank_orthogonalHarmonic :
    Module.finrank k (orthogonalHarmonic k n) = n ^ 2 - 1 := by
  have h := finrank_orthogonalHarmonic_add_one k n
  omega

end Field

/-- **The acceptance count for `O(3)`.**  On `(k³)^{⊗2}` the trace line is one dimensional and the
harmonic tensors are eight dimensional, `1 + 8 = 9 = 3²`.  Over `ℂ` the eight splits further into
the `5`-dimensional traceless symmetric and the `3`-dimensional antisymmetric tensors. -/
theorem finrank_orthogonalHarmonic_three {k : Type u} [Field k] [Invertible ((3 : ℕ) : k)] :
    Module.finrank k (orthogonalHarmonic k 3) = 8 := by
  have h := finrank_orthogonalHarmonic_add_one k 3
  have h9 : (3 : ℕ) ^ 2 = 9 := by norm_num
  omega

theorem finrank_orthogonalHarmonic_rat_three :
    Module.finrank ℚ (orthogonalHarmonic ℚ 3) = 8 :=
  @finrank_orthogonalHarmonic_three ℚ _ (invertibleOfNonzero (by norm_num))

end TauCeti
