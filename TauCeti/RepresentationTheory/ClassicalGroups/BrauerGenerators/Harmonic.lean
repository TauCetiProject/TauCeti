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
horizontal arcs of a Brauer diagram.  Breaking `GLₙ` to `Oₙ` by fixing the invariant form is what
makes the trace a subrepresentation: the trace line lies inside the symmetric square of the
general-linear decomposition `V^{⊗2} ≅ Sym²V ⊕ ⋀²V` of
`TauCeti/RepresentationTheory/ClassicalGroups/Decomposition.lean`, which needs `2` invertible, but
it is not a `GLₙ`-stable summand there, so the orthogonal splitting refines that decomposition by
splitting the trace line off the symmetric part.

The counting is `1 + (n² - 1) = n²`: the trace line is a line, and the harmonic tensors are a
hyperplane.  About the finer structure of that hyperplane this file proves only one inclusion, that
the antisymmetric tensors are harmonic (`TauCeti.tprod_sub_swap_mem_orthogonalHarmonic`).  When `2`
is invertible the hyperplane is in fact the direct sum of the antisymmetric and the traceless
symmetric tensors, which for `n = 3` is the classical `8 = 3 + 5`; that direct-sum decomposition
needs the symmetric and the exterior square as submodules of the tensor square and is not proved
here, and neither is the symplectic mirror, where the cap and the cup of
`TauCeti/RepresentationTheory/ClassicalGroups/BrauerGenerators/Symplectic.lean` have loop value
`-2n`.

Nothing here needs subtraction, so the two pieces are stated over a commutative semiring.  The
arithmetic input is graded: the injectivity of the cup, the surjectivity of the cap, and hence the
identification of the two pieces as the kernel and the image of `e` need only a positive dimension,
while the rescaling `e / n` asks for the loop value to be invertible.  Three things ask for a
commutative ring: the orthogonal group, the inclusion of the antisymmetric tensors, and the
complementarity of the two pieces, since `LinearMap.IsIdempotentElem.isCompl` splits a module over
a ring.  Only the dimension counts ask for a field.

## Main definitions

* `TauCeti.orthogonalHarmonic`: the harmonic (traceless) tensors, the kernel of the cap.
* `TauCeti.orthogonalTraceLine`: the trace line, the image of the cup.
* `TauCeti.orthogonalHarmonicSubrep` and `TauCeti.orthogonalTraceLineSubrep`: the two pieces as
  subrepresentations of the diagonal orthogonal action on the tensor square.
* `TauCeti.orthogonalTraceProj`: the rescaled Brauer generator `e / n`, the projection onto the
  trace line along the harmonic tensors.

## Main results

* `TauCeti.tensorPower_apply_of_mem_orthogonalTraceLine`: the orthogonal group fixes the trace
  line pointwise.
* `TauCeti.ker_orthogonalCupCap` and `TauCeti.range_orthogonalCupCap`: the diagrammatic reading of
  the two pieces, as the kernel and the image of the generator `e` itself.
* `TauCeti.orthogonalTraceProj_apply_of_mem_orthogonalHarmonic` and
  `TauCeti.orthogonalTraceProj_apply_of_mem_orthogonalTraceLine`: the projection is zero on the
  harmonic tensors and the identity on the trace line.
* `TauCeti.isCompl_orthogonalTraceLine_orthogonalHarmonic`: **the trace splitting.**
* `TauCeti.finrank_orthogonalTraceLine` and `TauCeti.finrank_orthogonalHarmonic_add_one`: the
  dimensions, `1` and `n² - 1`.
* `TauCeti.finrank_orthogonalHarmonic_three`: the acceptance count `8` for `n = 3`.

## References

* R. Goodman and N. R. Wallach, *Symmetry, Representations, and Invariants*, Springer GTM 255
  (2009), Chapter 10, for harmonic tensors and the trace-free decomposition.
-/

public section

open Matrix
open scoped TensorProduct

universe u

namespace TauCeti

variable (k : Type u) (n : ℕ)

section CommSemiring

variable [CommSemiring k]

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
@[simp]
theorem mem_orthogonalHarmonic_iff {x : ⨂[k]^2 (Fin n → k)} :
    x ∈ orthogonalHarmonic k n ↔ orthogonalCap k n x = 0 :=
  LinearMap.mem_ker

/-- **The trace line** of the tensor square: the image of the cup, spanned by the invariant
bivector `∑ⱼ eⱼ ⊗ eⱼ`.  It is the summand the invariant form contributes: it lies inside the
symmetric square of the general-linear decomposition `V^{⊗2} ≅ Sym²V ⊕ ⋀²V`, available when `2` is
invertible, but is not a `GLₙ`-stable summand of it. -/
noncomputable def orthogonalTraceLine : Submodule k (⨂[k]^2 (Fin n → k)) :=
  LinearMap.range (orthogonalCup k n)

/-- The trace line is, by definition, the image of the cup. -/
theorem orthogonalTraceLine_def :
    orthogonalTraceLine k n = LinearMap.range (orthogonalCup k n) :=
  (rfl)

/-- A tensor of the square lies on the trace line exactly when it is a cup; in positive dimension
the coefficient it is the cup of is unique, by `TauCeti.orthogonalCup_injective`. -/
@[simp]
theorem mem_orthogonalTraceLine_iff {x : ⨂[k]^2 (Fin n → k)} :
    x ∈ orthogonalTraceLine k n ↔ ∃ c, orthogonalCup k n c = x :=
  LinearMap.mem_range

-- Not a `simp` lemma: `TauCeti.orthogonalCup_apply` rewrites the left-hand side first, expanding
-- the cup into the invariant bivector, so `simpNF` reports this form as not simp-normal.
/-- Every cup lies in the trace line. -/
theorem orthogonalCup_mem_orthogonalTraceLine (c : k) :
    orthogonalCup k n c ∈ orthogonalTraceLine k n :=
  LinearMap.mem_range_self _ c

/-! ### The cup and the cap in positive dimension -/

/-- **The cup is injective** as soon as the dimension is positive: the coefficient can be read back
off the coordinate of the cup at the monomial `e₀ ⊗ e₀`, with no division by the loop value. -/
theorem orthogonalCup_injective (hn : 0 < n) : Function.Injective (orthogonalCup k n) := by
  have hb : ∀ j : Fin n,
      (tensorPowerBasis k n 2).coord (fun _ => (⟨0, hn⟩ : Fin n))
          (PiTensorProduct.tprod k fun _ : Fin 2 => Pi.single j (1 : k)) =
        if (fun _ : Fin 2 => j) = fun _ => (⟨0, hn⟩ : Fin n) then 1 else 0 := fun j => by
    rw [← tensorPowerBasis_apply, Module.Basis.coord_apply, Module.Basis.repr_self_apply]
  have key : ∀ c : k,
      (tensorPowerBasis k n 2).coord (fun _ => (⟨0, hn⟩ : Fin n)) (orthogonalCup k n c) = c := by
    intro c
    rw [orthogonalCup_apply, map_smul, map_sum, Finset.sum_eq_single (⟨0, hn⟩ : Fin n)]
    · rw [hb]
      simp
    · intro j _ hj
      have hne : (fun _ : Fin 2 => j) ≠ fun _ => (⟨0, hn⟩ : Fin n) := fun h => hj (congrFun h 0)
      rw [hb]
      simp [hne]
    · exact fun h => absurd (Finset.mem_univ _) h
  exact fun c d h => by rw [← key c, ← key d, h]

/-- **The cap is surjective** as soon as the dimension is positive: capping `e₀ ⊗ c e₀` returns
`c`, again with no division by the loop value. -/
theorem orthogonalCap_surjective (hn : 0 < n) : Function.Surjective (orthogonalCap k n) := fun c =>
  ⟨PiTensorProduct.tprod k ![Pi.single ⟨0, hn⟩ (1 : k), Pi.single ⟨0, hn⟩ c], by
    rw [orthogonalCap_tprod]
    simp⟩

/-- The Brauer generator read as the composite it is defined to be, so that the generic kernel and
range lemmas for a composite apply to it. -/
private theorem orthogonalCupCap_eq_comp :
    orthogonalCupCap k n = orthogonalCup k n ∘ₗ orthogonalCap k n :=
  LinearMap.ext (orthogonalCupCap_apply k n)

/-- The kernel of the Brauer generator `e` is the harmonic tensors: in positive dimension the cup
is injective, so capping and cupping back destroys no more information than the cap already
does. -/
theorem ker_orthogonalCupCap (hn : 0 < n) :
    LinearMap.ker (orthogonalCupCap k n) = orthogonalHarmonic k n := by
  rw [orthogonalCupCap_eq_comp, orthogonalHarmonic_def]
  exact LinearMap.ker_comp_of_ker_eq_bot _
    (LinearMap.ker_eq_bot_of_injective (orthogonalCup_injective k n hn))

/-- The image of the Brauer generator `e` is the trace line, the cap being surjective in positive
dimension.  Together with
`TauCeti.ker_orthogonalCupCap` this is the diagrammatic reading of the trace splitting: the
horizontal arc of `e` cuts out the trace summand and kills the harmonic one. -/
theorem range_orthogonalCupCap (hn : 0 < n) :
    LinearMap.range (orthogonalCupCap k n) = orthogonalTraceLine k n := by
  rw [orthogonalCupCap_eq_comp, orthogonalTraceLine_def]
  exact LinearMap.range_comp_of_range_eq_top _
    (LinearMap.range_eq_top_of_surjective _ (orthogonalCap_surjective k n hn))

/-! ### The trace projection -/

section Invertible

variable [Invertible (n : k)]

/-- **The trace projection** `e / n`, the Brauer generator rescaled so as to be idempotent.  The
rescaling is where the invertibility of the loop value enters. -/
noncomputable def orthogonalTraceProj : Module.End k (⨂[k]^2 (Fin n → k)) :=
  ⅟(n : k) • orthogonalCupCap k n

/-- The trace projection caps a tensor off, rescales by `⅟n`, and cups the result back. -/
@[simp]
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

-- The two elimination rules below are deliberately not `simp` lemmas: the `simp` lemma
-- `TauCeti.orthogonalTraceProj_apply` rewrites their left-hand sides first, expanding the
-- projection into a cup, so `simpNF` reports neither as simp-normal.
/-- **The trace projection annihilates the harmonic tensors**: they are what the cap, and hence
`e / n`, kills. -/
theorem orthogonalTraceProj_apply_of_mem_orthogonalHarmonic {x : ⨂[k]^2 (Fin n → k)}
    (hx : x ∈ orthogonalHarmonic k n) : orthogonalTraceProj k n x = 0 := by
  rw [orthogonalTraceProj_apply, (mem_orthogonalHarmonic_iff k n).mp hx, mul_zero, map_zero]

/-- **The trace projection is the identity on the trace line**: on a cup the rescaling by `⅟n`
undoes the loop value.  With
`TauCeti.orthogonalTraceProj_apply_of_mem_orthogonalHarmonic` this is what makes `e / n` the
projection onto the trace line along the harmonic tensors. -/
theorem orthogonalTraceProj_apply_of_mem_orthogonalTraceLine {x : ⨂[k]^2 (Fin n → k)}
    (hx : x ∈ orthogonalTraceLine k n) : orthogonalTraceProj k n x = x := by
  obtain ⟨c, rfl⟩ := hx
  rw [orthogonalTraceProj_apply, orthogonalCap_comp_orthogonalCup_apply, invOf_mul_cancel_left]

/-- The kernel of the trace projection is the harmonic tensors. -/
theorem ker_orthogonalTraceProj :
    LinearMap.ker (orthogonalTraceProj k n) = orthogonalHarmonic k n := by
  refine le_antisymm (fun x hx => ?_) fun x hx =>
    LinearMap.mem_ker.mpr (orthogonalTraceProj_apply_of_mem_orthogonalHarmonic k n hx)
  -- capping the projection back off returns the cap, so a projection-free tensor is traceless
  have h : orthogonalCap k n (orthogonalTraceProj k n x) = orthogonalCap k n x := by
    rw [orthogonalTraceProj_apply, orthogonalCap_comp_orthogonalCup_apply, mul_invOf_cancel_left]
  rw [mem_orthogonalHarmonic_iff, ← h, LinearMap.mem_ker.mp hx, map_zero]

/-- The image of the trace projection is the trace line. -/
theorem range_orthogonalTraceProj :
    LinearMap.range (orthogonalTraceProj k n) = orthogonalTraceLine k n := by
  refine le_antisymm ?_ fun x hx =>
    ⟨x, orthogonalTraceProj_apply_of_mem_orthogonalTraceLine k n hx⟩
  rintro x ⟨y, rfl⟩
  rw [orthogonalTraceProj_apply]
  exact orthogonalCup_mem_orthogonalTraceLine k n _

end Invertible

end CommSemiring

section CommRing

variable [CommRing k]

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

/-! ### The splitting -/

/-- **The trace splitting of the tensor square.**  When the loop value `n` is invertible the tensor
square is the direct sum of the trace line and the harmonic tensors, the two being the image and
the kernel of the idempotent `e / n`.  The complementarity, unlike the idempotent itself, needs the
tensor square to be a module over a ring. -/
theorem isCompl_orthogonalTraceLine_orthogonalHarmonic [Invertible (n : k)] :
    IsCompl (orthogonalTraceLine k n) (orthogonalHarmonic k n) := by
  rw [← range_orthogonalTraceProj, ← ker_orthogonalTraceProj]
  exact LinearMap.IsIdempotentElem.isCompl (isIdempotentElem_orthogonalTraceProj k n)

end CommRing

section Field

variable [Field k]

/-- **The trace line is a line** in every positive dimension: the cup is an isomorphism of `k`
onto it. -/
theorem finrank_orthogonalTraceLine (hn : 0 < n) :
    Module.finrank k (orthogonalTraceLine k n) = 1 := by
  rw [orthogonalTraceLine_def,
    ← (LinearEquiv.ofInjective (orthogonalCup k n) (orthogonalCup_injective k n hn)).finrank_eq,
    Module.finrank_self]

variable [Invertible (n : k)]

/-- **The harmonic tensors are a hyperplane** of the tensor square, of dimension `n² - 1`, stated
without subtraction. -/
theorem finrank_orthogonalHarmonic_add_one :
    Module.finrank k (orthogonalHarmonic k n) + 1 = n ^ 2 := by
  have hn : 0 < n := Nat.pos_of_ne_zero fun h => by
    simpa [h] using Invertible.ne_zero ((n : ℕ) : k)
  have h := Submodule.finrank_add_eq_of_isCompl
    (isCompl_orthogonalTraceLine_orthogonalHarmonic k n)
  rw [finrank_orthogonalTraceLine k n hn, finrank_tensorPower] at h
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

end TauCeti
