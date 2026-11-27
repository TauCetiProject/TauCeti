/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.ZMod.Defs
public import Mathlib.GroupTheory.Perm.Sign
public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

import Mathlib.Data.Fin.Tuple.Sort
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.LinearAlgebra.Matrix.Permutation
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import TauCeti.Algebra.BigOperators.Group.List
import TauCeti.LinearAlgebra.Determinant.Basic
import TauCeti.LinearAlgebra.Matrix.Determinant.Interlacing

/-!
# The share of the Pieri cone in a slab

Vectors `ν` are real functions on pairs `(b, j)`, with `b : Fin k` and `j` a *letter*, an element
of `ZMod N`. Fix `P > 1`, a sign `v j` for each letter (`+` where `v j` is true) and put
`q = P ^ N`.

* The *step map* `TauCeti.pieriStepMap v P 1` sends `ν` to the vector `β` of signed steps
  `β (b, j) = ± (P * ν (b, j + 1) - ν (b, j))`, with the sign `v j`. More generally,
  `TauCeti.pieriStepMap v P σ` twists the step at `j` by a permutation `σ j` of `Fin k`.
* The *Pieri cone* `TauCeti.pieriCone v P` is the set of `ν` satisfying Pieri's inequalities
  `P * ν (b + 1, j + 1) ≤ ν (b, j)` where `v j` is true and `ν (b + 1, j) ≤ P * ν (b, j + 1)`
  where it is false: one half of the interlacing inequalities between `ν` and `P` times its shift
  by one letter.
* The *slab* `TauCeti.degreeSlab k D` of `D : ZMod N → ℝ` is the set of `β ≥ 0` whose degree
  `∑ b, β (b, j)` lies in `[D j - 1, D j]` for every letter `j`.

## Main results

* `TauCeti.prod_mul_volume_real_inter_degreeSlab`: if `Ω` is a set whose preimage under the
  step map is the Pieri cone, then
  `∏ l < k, (q ^ (l + 1) - 1) / (q - 1) * vol (Ω ∩ degreeSlab k D) = vol (degreeSlab k D)`.
  So `Ω` fills the share `∏ l < k, (q - 1) / (q ^ (l + 1) - 1)` of the slab, the inverse of the
  number of complete flags in `𝔽_q ^ k` when `q` is a prime power.
* `TauCeti.volume_real_inter_degreeSlab_eq_signed_sum`: the same share as a signed sum over
  permutations `τ` of `Fin k` of the inverses of `|det (1 - τ / q)|`.
* `TauCeti.det_pieriStepMap_ne_zero`: for `|P| ≠ 1` every twisted step map is invertible.

## The argument

For a vector `ν`, sorting each block `b ↦ ν (b, j)` decreasingly, the interlacing inequalities
between consecutive blocks are a determinant of indicators
(`Matrix.det_interlacing_indicator`). Expanding these determinants over the permutations, the
indicator of the Pieri cone (together with positivity of the steps) becomes a signed sum over
families `σ` of permutations of the indicators that the twisted steps `pieriStepMap v P σ ν` are
all positive. Each of these sets is the preimage of a part of the slab under a linear map, whose
volume is the volume of that part divided by `|det (pieriStepMap v P σ)|`, and this determinant
is `det (1 - σ' / q)` for the product `σ'` of the `σ j`, up to a factor that does not depend on
`σ`. Integrating the pointwise identity gives the share of the cone as a signed sum that depends
only on `k` and `q`. It is then computed for a single letter, where the step map is the homothety
of ratio `q - 1` and the cone in the slab is the preimage of the slab under a triangular map of
determinant `∏ l < k, (q ^ (l + 1) - 1) / (q - 1)`.

The share is used to bound the dimension of forms of bounded defect, where a count of exponents
in a cone becomes a volume.

## Provenance

The definitions, the statements and the route of the proofs are adapted from grh-lean
(https://github.com/lsernau/grh-lean, file `src/New/UpperBound/ElementaryDivisors/PieriCone.lean`,
Apache 2.0, Copyright 2026 Anthropic, PBC): `New.permStep`, `New.pieriCone`, `New.degreeSlab`,
`New.exists_det_permStep_eq`, `New.sum_sign_indicator_pos_eq_indicator_pieriCone`,
`New.volume_real_inter_degreeSlab_eq_signed_sum` and `New.prod_mul_volume_real_inter_degreeSlab`.
Here the Pieri cone is defined by its inequalities rather than through the step map, the
hypothesis on `Ω` is an equality of sets, and the first factor of the signed sum is computed.
As related work on volumes of interlacing regions grh-lean cites P. J. Forrester and J. Zhang,
*Corank-1 projections and the randomised Horn problem* (2021), after A. C. Dixon (1905) and
G. W. Anderson (1991).
-/

public section

open Finset Matrix MeasureTheory Equiv Set LinearMap

namespace TauCeti

variable {k : ℕ}

section Defs

variable {T : Type*}

/-- The step map twisted by permutations `σ j` of `Fin k`, one for each letter `j`: the linear map
`ν ↦ β` with `β (b, j) = ± (P * ν (b, j + 1) - ν (σ j b, j))`, the sign being `+` if `v j` is
true and `-` otherwise. For `σ = 1` it is the step map of the Pieri cone. -/
noncomputable def pieriStepMap [Add T] [One T] (v : T → Bool) (P : ℝ) (σ : T → Perm (Fin k)) :
    Module.End ℝ (Fin k × T → ℝ) :=
  LinearMap.pi fun x : Fin k × T ↦
    (if v x.2 then (1 : ℝ) else -1) • (P • proj (x.1, x.2 + 1) - proj (σ x.2 x.1, x.2))

/-- The entries of the twisted step map. -/
@[simp]
theorem pieriStepMap_apply [Add T] [One T] (v : T → Bool) (P : ℝ) (σ : T → Perm (Fin k))
    (ν : Fin k × T → ℝ) (x : Fin k × T) :
    pieriStepMap v P σ ν x =
      (if v x.2 then 1 else -1) * (P * ν (x.1, x.2 + 1) - ν (σ x.2 x.1, x.2)) := by
  rw [pieriStepMap, LinearMap.pi_apply]
  split_ifs <;> simp

/-- The Pieri cone: the vectors `ν` such that, for every letter `j` and all `b`, `b' = b + 1` in
`Fin k`, `P * ν (b', j + 1) ≤ ν (b, j)` if `v j` is true and `ν (b', j) ≤ P * ν (b, j + 1)`
otherwise. -/
def pieriCone [Add T] [One T] (v : T → Bool) (P : ℝ) : Set (Fin k × T → ℝ) :=
  {ν | ∀ (j : T) (b b' : Fin k), b.val + 1 = b'.val →
    if v j then P * ν (b', j + 1) ≤ ν (b, j) else ν (b', j) ≤ P * ν (b, j + 1)}

/-- Membership in the Pieri cone is Pieri's inequalities. -/
@[simp]
theorem mem_pieriCone [Add T] [One T] {v : T → Bool} {P : ℝ} {ν : Fin k × T → ℝ} :
    ν ∈ pieriCone v P ↔ ∀ (j : T) (b b' : Fin k), b.val + 1 = b'.val →
      if v j then P * ν (b', j + 1) ≤ ν (b, j) else ν (b', j) ≤ P * ν (b, j + 1) :=
  Iff.rfl

/-- The Pieri cone is closed, as an intersection of closed half-spaces. -/
theorem isClosed_pieriCone [Add T] [One T] (v : T → Bool) (P : ℝ) :
    IsClosed (pieriCone (k := k) v P) := by
  simp only [pieriCone, ofPred_forall]
  refine isClosed_iInter fun j ↦ isClosed_iInter fun b ↦ isClosed_iInter fun b' ↦
    isClosed_iInter fun _ ↦ ?_
  split_ifs
  · exact isClosed_le (by fun_prop) (by fun_prop)
  · exact isClosed_le (by fun_prop) (by fun_prop)

/-- The slab: the vectors `β ≥ 0` whose degree `∑ b, β (b, j)` lies in `[D j - 1, D j]` for every
letter `j`. -/
def degreeSlab (k : ℕ) (D : T → ℝ) : Set (Fin k × T → ℝ) :=
  {β | 0 ≤ β ∧ ∀ j : T, ∑ b : Fin k, β (b, j) ∈ Icc (D j - 1) (D j)}

/-- Membership in the slab: nonnegativity and the bounds on the degrees. -/
@[simp]
theorem mem_degreeSlab {D : T → ℝ} {β : Fin k × T → ℝ} :
    β ∈ degreeSlab k D ↔ 0 ≤ β ∧ ∀ j : T, ∑ b : Fin k, β (b, j) ∈ Icc (D j - 1) (D j) :=
  Iff.rfl

/-- The slab is closed. -/
theorem isClosed_degreeSlab (k : ℕ) (D : T → ℝ) : IsClosed (degreeSlab k D) := by
  simp only [degreeSlab, ofPred_and, ofPred_forall]
  exact (isClosed_le continuous_const continuous_id).inter <| isClosed_iInter fun j ↦
    isClosed_Icc.preimage (by fun_prop)

/-- The slab is bounded: a nonnegative entry is at most the degree of its block. -/
theorem isBounded_degreeSlab (k : ℕ) (D : T → ℝ) : Bornology.IsBounded (degreeSlab k D) := by
  refine Bornology.forall_isBounded_image_eval_iff.1 fun x ↦
    (Metric.isBounded_Icc 0 (D x.2)).subset ?_
  rintro _ ⟨β, ⟨h_nonneg, h_deg⟩, rfl⟩
  exact ⟨h_nonneg x,
    (single_le_sum (fun b' _ ↦ h_nonneg (b', x.2)) (Finset.mem_univ x.1)).trans (h_deg x.2).2⟩

end Defs

section StepMap

variable {T : Type*} [AddGroup T] [One T]

/-- For `|P| ≠ 1` every twisted step map `pieriStepMap v P σ` has nonzero determinant. -/
theorem det_pieriStepMap_ne_zero (v : T → Bool) {P : ℝ} (hP : |P| ≠ 1) (σ : T → Perm (Fin k)) :
    LinearMap.det (pieriStepMap v P σ) ≠ 0 := by
  by_cases h_fin : Module.Finite ℝ (Fin k × T → ℝ)
  swap
  · rw [det_eq_one_of_not_module_finite h_fin]
    exact one_ne_zero
  classical
  have : Fintype (Fin k × T) :=
    have : Finite (Fin k × T) := (Pi.linearIndependent_single_one (Fin k × T) ℝ).finite
    Fintype.ofFinite _
  -- On the kernel, multiplication by `P` only rearranges the entries of a vector, so
  -- `|P| * ‖ν‖ = ‖ν‖` forces `ν = 0`.
  intro h_det
  obtain ⟨ν, hν, h_ne⟩ := (Submodule.ne_bot_iff _).1 (bot_lt_ker_of_det_eq_zero h_det).ne'
  have h_step (b : Fin k) (j : T) : P * ν (b, j + 1) = ν (σ j b, j) := by
    have h_entry : pieriStepMap v P σ ν (b, j) = 0 := congrFun (mem_ker.1 hν) (b, j)
    rw [pieriStepMap_apply] at h_entry
    split_ifs at h_entry <;> linarith
  -- Every entry of `P • ν` is an entry of `ν`, and every entry of `ν` is one of `P • ν`.
  have h_up : |P| * ‖ν‖ ≤ ‖ν‖ := by
    rw [← Real.norm_eq_abs, ← norm_smul]
    refine (pi_norm_le_iff_of_nonneg (norm_nonneg ν)).2 fun ⟨b, j⟩ ↦ ?_
    have h := h_step b (j - 1)
    rw [sub_add_cancel] at h
    simpa [h] using norm_le_pi_norm ν (σ (j - 1) b, j - 1)
  have h_down : ‖ν‖ ≤ |P| * ‖ν‖ := by
    refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun ⟨b, j⟩ ↦ ?_
    have h := h_step ((σ j).symm b) j
    rw [Equiv.apply_symm_apply] at h
    rw [← h, norm_mul, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_left (norm_le_pi_norm ν _) (abs_nonneg P)
  exact hP (mul_right_cancel₀ (norm_pos_iff.2 h_ne).ne' (by linarith))

end StepMap

section SignedCount

variable {m : ℕ}

private lemma abs_ne_one_of_one_lt {P : ℝ} (hP : 1 < P) : |P| ≠ 1 := by
  rw [abs_of_pos (zero_lt_one.trans hP)]
  exact hP.ne'

/-- Let `P ≠ 0` and `q = P ^ (m + 1)`. Up to a factor that does not depend on `σ`, the
determinant of `pieriStepMap v P σ` is `det (1 - σ' / q)`, where `σ' = σ 0 * ⋯ * σ m` acts by
permuting coordinates. -/
private lemma exists_det_pieriStepMap_eq (v : Fin (m + 1) → Bool) {P : ℝ} (hP : P ≠ 0) :
    ∃ c : ℝ, ∀ σ : Fin (m + 1) → Perm (Fin k),
      LinearMap.det (pieriStepMap v P σ) =
        c * LinearMap.det (1 - (P ^ (m + 1))⁻¹ • funLeft ℝ ℝ (List.ofFn σ).prod) := by
  -- Factor the step map. `E` is the signed shift `ν_j ↦ ± ν_(j+1)` and `N` the triangular map
  -- `ν_j ↦ P ν_j - ν_(j-1)` with `ν_(-1) = 0`; neither depends on `σ`.
  let E : Module.End ℝ (Fin k × Fin (m + 1) → ℝ) := pieriStepMap v 1 1 - pieriStepMap v 0 1
  let N : Module.End ℝ (Fin k × Fin (m + 1) → ℝ) :=
    P • 1 - .pi fun x : Fin k × Fin (m + 1) ↦
      Fin.cases 0 (fun j : Fin m ↦ proj (x.1, j.castSucc)) x.2
  refine ⟨LinearMap.det E * LinearMap.det N, fun σ ↦ ?_⟩
  -- `G` permutes block `j` by `σ 0 * ⋯ * σ (j - 1)`, which moves all the twist to the last step.
  -- There `A` reads the last block through `σ'`, and `N ∘ B` places a vector in block `0`.
  let π : Perm (Fin k × Fin (m + 1)) := prodCongrLeft fun j ↦ Fin.partialProd σ j.castSucc
  let G : Module.End ℝ (Fin k × Fin (m + 1) → ℝ) := toLin' (π.permMatrix ℝ)
  let A : (Fin k × Fin (m + 1) → ℝ) →ₗ[ℝ] Fin k → ℝ :=
    funLeft ℝ ℝ fun b ↦ (Fin.partialProd σ (Fin.last (m + 1)) b, Fin.last m)
  let B : (Fin k → ℝ) →ₗ[ℝ] Fin k × Fin (m + 1) → ℝ := .pi fun x ↦ P⁻¹ ^ x.2.val.succ • proj x.1
  have h_E (ν : Fin k × Fin (m + 1) → ℝ) (b : Fin k) (j : Fin (m + 1)) :
      E ν (b, j) = (if v j then 1 else -1) * ν (b, j + 1) := by
    cases hv : v j <;> simp [E, hv]
  have h_G (ν : Fin k × Fin (m + 1) → ℝ) (b : Fin k) (j : Fin (m + 1)) :
      G ν (b, j) = ν (Fin.partialProd σ j.castSucc b, j) := by
    simp [G, π, permMatrix_mulVec]
  -- After `1 - B ∘ₗ A`, the map `N` subtracts the preceding block, read cyclically through `σ'`.
  have h_N (ν : Fin k × Fin (m + 1) → ℝ) (b : Fin k) (i : Fin (m + 1)) :
      N ((1 - B ∘ₗ A) ν) (b, i) =
        P * ν (b, i) - Fin.cases (ν (Fin.partialProd σ (Fin.last (m + 1)) b, Fin.last m))
          (fun j : Fin m ↦ ν (b, j.castSucc)) i := by
    cases i using Fin.cases <;>
      simp [N, A, B, mul_sub, hP, pow_succ, mul_assoc]
  have h_factor : pieriStepMap v P σ * G = E * G * N * (1 - B ∘ₗ A) := by
    refine LinearMap.ext fun ν ↦ funext fun ⟨b, j⟩ ↦ ?_
    simp only [mul_apply_eq_comp, pieriStepMap_apply, h_E, h_G, h_N]
    -- Compare the entries by `partialProd σ j.succ = partialProd σ j.castSucc * σ j`.
    cases j using Fin.lastCases <;> simp [← Fin.succ_last, Fin.partialProd_succ]
  have h_AB : (P ^ (m + 1))⁻¹ • funLeft ℝ ℝ (List.ofFn σ).prod = A ∘ₗ B :=
    LinearMap.ext fun x ↦ funext fun b ↦ by
      simp [A, B, Fin.partialProd, List.take_of_length_le]
  -- Cancel `det G = ± 1` and use `det (1 - B A) = det (1 - A B)`.
  have h_det : LinearMap.det (pieriStepMap v P σ) * LinearMap.det G =
      LinearMap.det E * LinearMap.det G * LinearMap.det N * LinearMap.det (1 - B ∘ₗ A) := by
    simp only [← map_mul, h_factor]
  rw [h_AB, det_one_sub_comp_comm A B]
  exact mul_right_cancel₀ (show LinearMap.det G ≠ 0 by simp [G]) (by linear_combination h_det)

variable (v : Fin (m + 1) → Bool) (P : ℝ)

/-- The set of `ν` whose steps `pieriStepMap v P 1 ν` have degrees in `[D j - 1, D j]` and such
that, after block `j` of `ν` is rearranged by `τ j`, the image under `pieriStepMap v P σ` has
positive entries and lies in `Y`. -/
private def positiveStepSet (D : Fin (m + 1) → ℝ) (σ τ : Fin (m + 1) → Perm (Fin k))
    (Y : Set (Fin k × Fin (m + 1) → ℝ)) : Set (Fin k × Fin (m + 1) → ℝ) :=
  {ν | (∀ j, ∑ b : Fin k, pieriStepMap v P 1 ν (b, j) ∈ Icc (D j - 1) (D j)) ∧
    (∀ j b, 0 < pieriStepMap v P σ (ν ∘ prodCongrLeft τ) (b, j)) ∧
      pieriStepMap v P σ (ν ∘ prodCongrLeft τ) ∈ Y}

/-- The linear map `ν ↦ pieriStepMap v P σ (ν ∘ prodCongrLeft τ)`. -/
private noncomputable def twistedStep (σ τ : Fin (m + 1) → Perm (Fin k)) :
    Module.End ℝ (Fin k × Fin (m + 1) → ℝ) :=
  pieriStepMap v P σ * toLin' (Perm.permMatrix ℝ (prodCongrLeft τ))

private lemma twistedStep_apply (σ τ : Fin (m + 1) → Perm (Fin k)) (ν : Fin k × Fin (m + 1) → ℝ) :
    twistedStep v P σ τ ν = pieriStepMap v P σ (ν ∘ prodCongrLeft τ) := by
  simp [twistedStep, permMatrix_mulVec]

/-- The set `positiveStepSet v P D σ τ Y` is the preimage under `twistedStep v P σ τ` of the
part of `Y ∩ degreeSlab k D` off the coordinate hyperplanes: the degrees do not see `σ` and
`τ`. -/
private lemma positiveStepSet_eq_preimage (D : Fin (m + 1) → ℝ)
    (σ τ : Fin (m + 1) → Perm (Fin k)) (Y : Set (Fin k × Fin (m + 1) → ℝ)) :
    positiveStepSet v P D σ τ Y =
      twistedStep v P σ τ ⁻¹' (Y ∩ degreeSlab k D ∩ {β | ∀ x, β x ≠ 0}) := by
  have h_deg (ν : Fin k × Fin (m + 1) → ℝ) (j : Fin (m + 1)) :
      ∑ b : Fin k, twistedStep v P σ τ ν (b, j) = ∑ b : Fin k, pieriStepMap v P 1 ν (b, j) := by
    have h_sum (e : Perm (Fin k)) (i : Fin (m + 1)) : ∑ b, ν (e b, i) = ∑ b, ν (b, i) :=
      Equiv.sum_comp e fun b ↦ ν (b, i)
    have h_sum_mul : ∑ b, ν (τ j (σ j b), j) = ∑ b, ν (b, j) := h_sum (τ j * σ j) j
    cases hv : v j <;> simp [twistedStep_apply, hv, ← mul_sum, h_sum, h_sum_mul]
  ext ν
  simp only [positiveStepSet, Set.mem_preimage, Set.mem_inter_iff, mem_degreeSlab, h_deg,
    Set.mem_ofPred_eq]
  simp only [twistedStep_apply]
  constructor
  · rintro ⟨h_sum, h_pos, h_mem⟩
    exact ⟨⟨h_mem, fun x ↦ (h_pos x.2 x.1).le, h_sum⟩, fun x ↦ (h_pos x.2 x.1).ne'⟩
  · rintro ⟨⟨h_mem, h_nonneg, h_sum⟩, h_ne⟩
    exact ⟨h_sum, fun j b ↦ (h_nonneg (b, j)).lt_of_ne' (h_ne (b, j)), h_mem⟩

/-- Change of variables for `P > 1`: the volume of `positiveStepSet v P D σ τ Y` is the volume of
`Y ∩ degreeSlab k D` divided by `|det (pieriStepMap v P σ)|`. -/
private lemma volume_positiveStepSet (hP : 1 < P) (D : Fin (m + 1) → ℝ)
    (σ τ : Fin (m + 1) → Perm (Fin k)) (Y : Set (Fin k × Fin (m + 1) → ℝ)) :
    volume (positiveStepSet v P D σ τ Y) =
      ENNReal.ofReal |LinearMap.det (pieriStepMap v P σ)|⁻¹ * volume (Y ∩ degreeSlab k D) := by
  have hL_det : LinearMap.det (twistedStep v P σ τ) ≠ 0 := by
    simpa [twistedStep] using det_pieriStepMap_ne_zero v (abs_ne_one_of_one_lt hP) σ
  -- The walls `β x = 0` are null.
  have h_walls : ∀ᵐ β : Fin k × Fin (m + 1) → ℝ, ∀ x, β x ≠ 0 :=
    ae_all_iff.2 fun x ↦ Measure.ae_eval_ne _ x 0
  rw [positiveStepSet_eq_preimage, Measure.addHaar_preimage_linearMap _ hL_det,
    measure_inter_conull h_walls]
  simp [twistedStep, abs_unit_intCast, abs_inv]

open Classical in
/-- The matrix of indicators of positive steps at the letter `j`: its `(b', b)` entry is `1` if
the step at `(b, j)` is positive for a twist sending `b` to `b'` (the transposition serves only
as some permutation sending `b` to `b'`), and `0` otherwise. -/
private noncomputable def positiveStepMatrix (ν : Fin k × Fin (m + 1) → ℝ) (j : Fin (m + 1)) :
    Matrix (Fin k) (Fin k) ℝ :=
  of fun b' b ↦ if 0 < pieriStepMap v P (fun _ ↦ .swap b b') ν (b, j) then 1 else 0

/-- Let `P ≥ 0` and let `τ i` sort block `i` of `ν` decreasingly, giving `ν'`. Reindexed by the
sorting permutations, the matrix of indicators of positive steps at the letter `j` has
determinant `1` if the steps of `ν'` at `j` are positive and `ν'` satisfies Pieri's inequalities
at `j`, and `0` otherwise: an interlacing determinant. -/
private lemma det_reindex_positiveStepMatrix (hP : 0 ≤ P) {ν : Fin k × Fin (m + 1) → ℝ}
    {τ : Fin (m + 1) → Perm (Fin k)}
    (h_anti : ∀ j : Fin (m + 1), Antitone fun b : Fin k ↦ ν (τ j b, j)) (j : Fin (m + 1)) :
    ((positiveStepMatrix v P ν j).reindex (τ j).symm (τ (j + 1)).symm).det =
      if (∀ b : Fin k, 0 < pieriStepMap v P 1 (ν ∘ prodCongrLeft τ) (b, j)) ∧
          ∀ b b' : Fin k, b.val + 1 = b'.val →
            if v j then P * (ν ∘ prodCongrLeft τ) (b', j + 1) ≤ (ν ∘ prodCongrLeft τ) (b, j)
            else (ν ∘ prodCongrLeft τ) (b', j) ≤ P * (ν ∘ prodCongrLeft τ) (b, j + 1)
      then 1 else 0 := by
  have h_anti_mul : Antitone fun b ↦ P * ν (τ (j + 1) b, j + 1) := (h_anti (j + 1)).const_mul hP
  by_cases hv : v j
  · have h_matrix : (positiveStepMatrix v P ν j).reindex (τ j).symm (τ (j + 1)).symm =
        (of fun b c : Fin k ↦
          if ν (τ j c, j) < P * ν (τ (j + 1) b, j + 1) then (1 : ℝ) else 0)ᵀ := by
      simp [positiveStepMatrix, ← ext_iff, hv]
    rw [h_matrix, det_transpose, det_interlacing_indicator h_anti_mul (h_anti j)]
    simp [hv]
  · have h_matrix : (positiveStepMatrix v P ν j).reindex (τ j).symm (τ (j + 1)).symm =
        of fun b c : Fin k ↦ if P * ν (τ (j + 1) c, j + 1) < ν (τ j b, j) then (1 : ℝ) else 0 := by
      simp [positiveStepMatrix, ← ext_iff, hv]
    rw [h_matrix, det_interlacing_indicator (h_anti j) h_anti_mul]
    simp [hv]

open Classical in
/-- Let `P ≥ 0` and let `τ j` sort block `j` of `ν` decreasingly. The signs of
`σ 0 * ⋯ * σ m`, summed over the families `σ` for which all steps `pieriStepMap v P σ ν` are
positive, add up to `1` if the steps of the sorted vector `ν'` are positive and `ν'` lies in the
Pieri cone, and to `0` otherwise. -/
private lemma sum_sign_indicator_pos_eq_indicator_pieriCone (hP : 0 ≤ P)
    {ν : Fin k × Fin (m + 1) → ℝ} {τ : Fin (m + 1) → Perm (Fin k)}
    (h_anti : ∀ j : Fin (m + 1), Antitone fun b : Fin k ↦ ν (τ j b, j)) :
    ∑ σ : Fin (m + 1) → Perm (Fin k),
        (if ∀ j b, 0 < pieriStepMap v P σ ν (b, j) then (Perm.sign (List.ofFn σ).prod : ℝ) else 0) =
      if (∀ j b, 0 < pieriStepMap v P 1 (ν ∘ prodCongrLeft τ) (b, j)) ∧
        ν ∘ prodCongrLeft τ ∈ pieriCone v P then 1 else 0 := by
  -- Both sides are the product over `j` of the determinants of the indicators of positive steps.
  let M := positiveStepMatrix v P ν
  have h_entries (σ : Fin (m + 1) → Perm (Fin k)) : ∏ j, ∏ b, M j (σ j b) b =
      if ∀ j b, 0 < pieriStepMap v P σ ν (b, j) then 1 else 0 := by
    simp [M, positiveStepMatrix, Fintype.prod_ite_zero]
  have h_sign (σ : Fin (m + 1) → Perm (Fin k)) :
      (Perm.sign (List.ofFn σ).prod : ℝ) = ∏ j, (Perm.sign (σ j) : ℝ) := by
    simp [map_list_prod, List.map_ofFn, List.prod_ofFn, Fin.prod_univ_succ]
  -- The signs of the sorting permutations `τ j` occur twice and cancel.
  have h_cancel : ∏ j, (Perm.sign (τ j) : ℝ) * Perm.sign (τ (j + 1)) = 1 := by
    rw [prod_mul_distrib,
      (AddGroup.addRight_bijective 1).prod_comp fun j ↦ (Perm.sign (τ j) : ℝ), ← prod_mul_distrib]
    simp [← Int.cast_mul, ← Units.val_mul]
  calc
    _ = ∑ σ : Fin (m + 1) → Perm (Fin k), ∏ j, (Perm.sign (σ j) : ℝ) * ∏ b, M j (σ j b) b := by
        simp only [prod_mul_distrib, h_entries, h_sign, mul_ite, mul_one, mul_zero]
    _ = ∏ j, (M j).det := by simp only [det_apply', prod_univ_sum, Fintype.piFinset_univ]
    _ = ∏ j, ((Perm.sign (τ j) : ℝ) * Perm.sign (τ (j + 1))) * (M j).det := by
        rw [prod_mul_distrib, h_cancel, one_mul]
    _ = ∏ j, ((M j).reindex (τ j).symm (τ (j + 1)).symm).det :=
        prod_congr rfl fun j _ ↦ by rw [Matrix.det_reindex]; simp
    _ = _ := by
        simp only [M, det_reindex_positiveStepMatrix v P hP h_anti, Fintype.prod_boole,
          mem_pieriCone, forall_and]

private lemma measurableSet_positiveStepSet (D : Fin (m + 1) → ℝ)
    (σ τ : Fin (m + 1) → Perm (Fin k)) {Y : Set (Fin k × Fin (m + 1) → ℝ)}
    (hY : MeasurableSet Y) : MeasurableSet (positiveStepSet v P D σ τ Y) := by
  rw [positiveStepSet_eq_preimage]
  have h_walls : MeasurableSet {β : Fin k × Fin (m + 1) → ℝ | ∀ x, β x ≠ 0} := by
    simp only [Set.ofPred_forall]
    exact MeasurableSet.iInter fun x ↦ (isOpen_ne_fun (continuous_apply x) continuous_const)
      |>.measurableSet
  exact (twistedStep v P σ τ).continuous_of_finiteDimensional.measurable
    ((hY.inter (isClosed_degreeSlab k D).measurableSet).inter h_walls)

/-- Counting in two ways at a point `ν`, for `P ≥ 0` and a set `Ω` whose preimage under the step
map is the Pieri cone: the number of families `τ` with `ν ∈ positiveStepSet v P D 1 τ Ω` equals
the number of families `σ` with `ν ∈ positiveStepSet v P D σ 1 univ`, each counted with the sign
of `σ 0 * ⋯ * σ m`. Only the family `τ` sorting every block of `ν` can count on the left. -/
private lemma sum_indicator_positiveStepSet (hP : 0 ≤ P) (D : Fin (m + 1) → ℝ)
    {Ω : Set (Fin k × Fin (m + 1) → ℝ)} (hΩ : pieriStepMap v P 1 ⁻¹' Ω = pieriCone v P)
    (ν : Fin k × Fin (m + 1) → ℝ) :
    ∑ τ : Fin (m + 1) → Perm (Fin k), (positiveStepSet v P D 1 τ Ω).indicator 1 ν =
      ∑ σ : Fin (m + 1) → Perm (Fin k),
        (positiveStepSet v P D σ 1 univ).indicator
          (fun _ ↦ (Perm.sign (List.ofFn σ).prod : ℝ)) ν := by
  classical
  have hΩ' (ν : Fin k × Fin (m + 1) → ℝ) : pieriStepMap v P 1 ν ∈ Ω ↔ ν ∈ pieriCone v P :=
    Set.ext_iff.1 hΩ ν
  let τ (j : Fin (m + 1)) : Perm (Fin k) := Tuple.sort fun b ↦ -ν (b, j)
  have h_anti (j : Fin (m + 1)) : Antitone fun b : Fin k ↦ ν (τ j b, j) := fun b b' h_le ↦
    neg_le_neg_iff.1 (Tuple.monotone_sort (fun b ↦ -ν (b, j)) h_le)
  have h_sort (τ' : Fin (m + 1) → Perm (Fin k)) (hτ' : ν ∈ positiveStepSet v P D 1 τ' Ω) :
      τ' = τ := by
    obtain ⟨-, h_pos, h_mem⟩ := hτ'
    -- A positive step and Pieri's inequality make every block strictly decreasing.
    have h_desc (j : Fin (m + 1)) (b b' : Fin k) (h_succ : b.val + 1 = b'.val) :
        ν (τ' j b', j) < ν (τ' j b, j) := by
      have h_cone := (hΩ' _).1 h_mem j b b' h_succ
      have h_pos_b := h_pos j b
      have h_pos_b' := h_pos j b'
      simp only [pieriStepMap_apply, Pi.one_apply, Perm.coe_one, id_eq, Function.comp_apply,
        prodCongrLeft_apply] at h_cone h_pos_b h_pos_b'
      cases hv : v j
      · -- `ν (b', j) ≤ P * ν (b, j + 1) < ν (b, j)`, read in the sorted blocks.
        simp only [hv, Bool.false_eq_true, ite_false, neg_mul, one_mul, neg_pos, sub_neg]
          at h_cone h_pos_b
        linarith
      · -- `ν (b', j) < P * ν (b', j + 1) ≤ ν (b, j)`, read in the sorted blocks.
        simp only [hv, ite_true, one_mul, sub_pos] at h_cone h_pos_b'
        linarith
    exact funext fun j ↦ Tuple.eq_sort_iff'.2 ((strictMono_iff_forall_covBy _).2 fun b b' h_cov ↦
      Prod.Lex.left _ _ (neg_lt_neg (h_desc j b b' h_cov.coe_fin.succ_eq)))
  rw [Fintype.sum_eq_single τ fun τ' h_ne ↦ indicator_of_notMem (mt (h_sort τ') h_ne) _]
  by_cases h_deg : ∀ j, ∑ b, pieriStepMap v P 1 ν (b, j) ∈ Icc (D j - 1) (D j)
  · have h_left : ν ∈ positiveStepSet v P D 1 τ Ω ↔
        (∀ j b, 0 < pieriStepMap v P 1 (ν ∘ prodCongrLeft τ) (b, j)) ∧
          ν ∘ prodCongrLeft τ ∈ pieriCone v P := by
      simp only [positiveStepSet, Set.mem_ofPred_eq, h_deg, hΩ', implies_true, true_and]
    have h_right (σ : Fin (m + 1) → Perm (Fin k)) : ν ∈ positiveStepSet v P D σ 1 univ ↔
        ∀ j b, 0 < pieriStepMap v P σ ν (b, j) := by
      simp only [positiveStepSet, Set.mem_ofPred_eq, h_deg, implies_true, true_and,
        Set.mem_univ, and_true]
      -- Rearranging every block by the identity permutation leaves `ν` unchanged.
      have h_id : ν ∘ prodCongrLeft (1 : Fin (m + 1) → Perm (Fin k)) = ν := by
        ext ⟨b, j⟩
        simp [prodCongrLeft_apply]
      rw [h_id]
    simp only [indicator_apply, h_left, h_right, Pi.one_apply]
    exact (sum_sign_indicator_pos_eq_indicator_pieriCone v P hP h_anti).symm
  · simp only [indicator_apply, positiveStepSet, Set.mem_ofPred_eq, h_deg, false_and, ite_false,
      sum_const_zero]

/-- The sets `positiveStepSet v P D σ τ Y` have finite volume, as they lie over the slab. -/
private lemma volume_positiveStepSet_ne_top (hP : 1 < P) (D : Fin (m + 1) → ℝ)
    (σ τ : Fin (m + 1) → Perm (Fin k)) (Y : Set (Fin k × Fin (m + 1) → ℝ)) :
    volume (positiveStepSet v P D σ τ Y) ≠ ⊤ := by
  rw [volume_positiveStepSet v P hP]
  exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top
    ((isBounded_degreeSlab k D).subset inter_subset_right).measure_lt_top.ne

/-- If the preimage of `Ω` under the step map is the Pieri cone, the sets
`positiveStepSet v P D 1 τ Ω` are measurable, whether or not `Ω` is. -/
private lemma measurableSet_positiveStepSet_of_preimage_eq (D : Fin (m + 1) → ℝ)
    (τ : Fin (m + 1) → Perm (Fin k)) {Ω : Set (Fin k × Fin (m + 1) → ℝ)}
    (hΩ : pieriStepMap v P 1 ⁻¹' Ω = pieriCone v P) :
    MeasurableSet (positiveStepSet v P D 1 τ Ω) := by
  have h_eq : positiveStepSet v P D 1 τ Ω = positiveStepSet v P D 1 τ univ ∩
      (fun ν ↦ ν ∘ prodCongrLeft τ) ⁻¹' pieriCone v P := by
    ext ν
    simp only [positiveStepSet, Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_univ,
      and_true, Set.mem_preimage, ← hΩ, and_assoc]
  rw [h_eq]
  exact (measurableSet_positiveStepSet v P D 1 τ MeasurableSet.univ).inter <|
    (isClosed_pieriCone v P).measurableSet.preimage (by fun_prop)

/-- The pointwise count `sum_indicator_positiveStepSet`, integrated over `ν`. -/
private lemma sum_volume_real_positiveStepSet (hP : 1 < P) (D : Fin (m + 1) → ℝ)
    {Ω : Set (Fin k × Fin (m + 1) → ℝ)} (hΩ : pieriStepMap v P 1 ⁻¹' Ω = pieriCone v P) :
    ∑ τ : Fin (m + 1) → Perm (Fin k), volume.real (positiveStepSet v P D 1 τ Ω) =
      ∑ σ : Fin (m + 1) → Perm (Fin k),
        volume.real (positiveStepSet v P D σ 1 univ) * (Perm.sign (List.ofFn σ).prod : ℝ) := by
  have h_meas_univ (σ : Fin (m + 1) → Perm (Fin k)) :
      MeasurableSet (positiveStepSet v P D σ 1 univ) :=
    measurableSet_positiveStepSet v P D σ 1 MeasurableSet.univ
  have h_meas_Ω (τ : Fin (m + 1) → Perm (Fin k)) := measurableSet_positiveStepSet_of_preimage_eq
    v P D τ hΩ
  have h_count := congrArg (fun g : (Fin k × Fin (m + 1) → ℝ) → ℝ ↦ ∫ ν, g ν)
    (funext (sum_indicator_positiveStepSet v P (zero_le_one.trans hP.le) D hΩ))
  rw [integral_finsetSum, integral_finsetSum] at h_count
  · simpa [h_meas_univ, h_meas_Ω, integral_indicator, mul_comm] using h_count
  · exact fun σ _ ↦ (integrableOn_const (volume_positiveStepSet_ne_top v P hP D σ 1 univ))
      |>.integrable_indicator (h_meas_univ σ)
  · exact fun τ _ ↦ (integrableOn_const (volume_positiveStepSet_ne_top v P hP D 1 τ Ω))
      |>.integrable_indicator (h_meas_Ω τ)

/-- The share of `Ω` in the slab as a signed sum, for letters in `Fin (m + 1)`. -/
private lemma volume_real_inter_degreeSlab_eq_signed_sum_aux (hP : 1 < P) (D : Fin (m + 1) → ℝ)
    {Ω : Set (Fin k × Fin (m + 1) → ℝ)} (hΩ : pieriStepMap v P 1 ⁻¹' Ω = pieriCone v P) :
    volume.real (Ω ∩ degreeSlab k D) =
      |LinearMap.det (1 - (P ^ (m + 1))⁻¹ • funLeft ℝ ℝ ⇑(1 : Perm (Fin k)))| / k.factorial *
        (∑ τ : Perm (Fin k),
          (Perm.sign τ : ℝ) / |LinearMap.det (1 - (P ^ (m + 1))⁻¹ • funLeft ℝ ℝ ⇑τ)|) *
          volume.real (degreeSlab k D) := by
  -- Each set in `sum_volume_real_positiveStepSet` is a linear preimage of a part of the slab, and
  -- the determinants are known up to a common factor `c`.
  let Δ (τ : Perm (Fin k)) : ℝ := |LinearMap.det (1 - (P ^ (m + 1))⁻¹ • funLeft ℝ ℝ ⇑τ)|
  -- The goal is stated with `Δ` unfolded; fold it so that `field_simp` below treats each `Δ τ`
  -- as an atom.
  change _ = Δ 1 / k.factorial * (∑ τ : Perm (Fin k), (Perm.sign τ : ℝ) / Δ τ) *
    volume.real (degreeSlab k D)
  obtain ⟨c, hc⟩ := exists_det_pieriStepMap_eq (k := k) v (zero_lt_one.trans hP).ne'
  obtain ⟨hc_ne, hΔ_ne⟩ : c ≠ 0 ∧ Δ 1 ≠ 0 := by
    simpa [hc, Δ] using det_pieriStepMap_ne_zero (k := k) v (abs_ne_one_of_one_lt hP) 1
  have h_vol (σ τ : Fin (m + 1) → Perm (Fin k)) (Y : Set (Fin k × Fin (m + 1) → ℝ)) :
      volume.real (positiveStepSet v P D σ τ Y) =
        (|c| * Δ (List.ofFn σ).prod)⁻¹ * volume.real (Y ∩ degreeSlab k D) := by
    simp [Measure.real, volume_positiveStepSet v P hP, hc, abs_mul, Δ, abs_nonneg]
  have h_eq : (k.factorial : ℝ) ^ (m + 1) * ((|c| * Δ 1)⁻¹ * volume.real (Ω ∩ degreeSlab k D)) =
      k.factorial ^ m * ∑ τ : Perm (Fin k),
        (|c| * Δ τ)⁻¹ * volume.real (degreeSlab k D) * (Perm.sign τ : ℝ) := by
    -- The ordered product `σ 0 * ⋯ * σ m` takes every value `k ! ^ m` times.
    have h_count (f : Perm (Fin k) → ℝ) : ∑ σ : Fin (m + 1) → Perm (Fin k), f (List.ofFn σ).prod =
        k.factorial ^ m * ∑ τ : Perm (Fin k), f τ := by
      rw [List.sum_comp_prod_ofFn, Fintype.card_perm, Fintype.card_fin, nsmul_eq_mul, Nat.cast_pow]
    simpa [← h_count, h_vol, Fintype.card_perm] using
      sum_volume_real_positiveStepSet v P hP D hΩ
  have h_sum : ∑ τ : Perm (Fin k),
      (|c| * Δ τ)⁻¹ * volume.real (degreeSlab k D) * (Perm.sign τ : ℝ) =
      |c|⁻¹ * (∑ τ : Perm (Fin k), (Perm.sign τ : ℝ) / Δ τ) * volume.real (degreeSlab k D) := by
    rw [mul_sum, sum_mul]
    exact sum_congr rfl fun τ _ ↦ by ring
  rw [h_sum, pow_succ] at h_eq
  field_simp at h_eq ⊢
  linear_combination h_eq

end SignedCount

section OneLetter

/-! ### The case of one letter -/

/-- The slab of one letter, the nonnegative vectors of `ℝ ^ k` with sum at most `1`, has positive
volume. -/
private lemma volume_real_degreeSlab_one_pos (k : ℕ) :
    0 < volume.real (degreeSlab k (1 : ZMod 1 → ℝ)) := by
  let a : Fin k × ZMod 1 → ℝ := fun _ ↦ (k : ℝ)⁻¹
  have h_box : Icc 0 a ⊆ degreeSlab k (1 : ZMod 1 → ℝ) := fun β ⟨h_low, h_up⟩ ↦
    ⟨h_low, fun j ↦ ⟨by simpa using sum_nonneg fun b _ ↦ h_low (b, j),
      (sum_le_sum fun b _ ↦ h_up (b, j)).trans (by simp [a, mul_inv_le_one])⟩⟩
  have h_box_pos : 0 < volume.real (Icc 0 a) :=
    ENNReal.toReal_pos (by simp [a, Real.volume_Icc_pi]) measure_Icc_lt_top.ne
  exact h_box_pos.trans_le
    (measureReal_mono h_box (isBounded_degreeSlab k (1 : ZMod 1 → ℝ)).measure_lt_top.ne)

/-- The entry `β (b, 0)` of a vector `β` of one letter, read as `0` for `b ≥ k`. -/
private noncomputable def oneCoord (k b : ℕ) : (Fin k × ZMod 1 → ℝ) →ₗ[ℝ] ℝ :=
  if h : b < k then .proj (⟨b, h⟩, 0) else 0

private lemma oneCoord_apply (b : Fin k) (β : Fin k × ZMod 1 → ℝ) : oneCoord k b β = β (b, 0) := by
  simp [oneCoord]

/-- For `q ≥ 0`, a vector `β` of one letter is nonnegative and satisfies `q * β (b + 1) ≤ β b`
for all `b < k - 1` if and only if `q * β (b + 1) ≤ β b` for all `b < k`, with `β k` read as `0`:
nonnegativity descends from the last entry. -/
private lemma pieri_and_nonneg_iff {q : ℝ} (hq : 0 ≤ q) (β : Fin k × ZMod 1 → ℝ) :
    ((∀ b b' : Fin k, b.val + 1 = b' → q * β (b', 0) ≤ β (b, 0)) ∧ 0 ≤ β) ↔
      ∀ b : Fin k, q * oneCoord k (b + 1) β ≤ β (b, 0) := by
  refine ⟨fun ⟨h_step, hβ⟩ b ↦ ?_, fun h_step ↦
    ⟨fun b b' h_succ ↦ by simpa [h_succ, oneCoord_apply] using h_step b, fun ⟨b, j⟩ ↦ ?_⟩⟩
  · by_cases hb : b.val + 1 < k
    · simpa [oneCoord, hb] using h_step b ⟨b + 1, hb⟩ rfl
    · simpa [oneCoord, hb] using hβ (b, 0)
  · obtain rfl : j = 0 := Subsingleton.elim j 0
    induction b using WellFoundedGT.induction with
    | ind b ih =>
      refine (mul_nonneg hq ?_).trans (h_step b)
      by_cases hb : b.val + 1 < k
      · simpa [oneCoord, hb] using ih ⟨b + 1, hb⟩ (Nat.lt_succ_self b)
      · simp [oneCoord, hb]

/-- For one letter with the sign `+` and `q > 1`, the cone of the vectors with
`q * β (b + 1) ≤ β b` fills the fraction `∏ l < k, (q - 1) / (q ^ (l + 1) - 1)` of the simplex
`degreeSlab k 1` of vectors `β ≥ 0` in `ℝ ^ k` with `∑ b, β b ≤ 1`: on the nonnegative part of the
cone, the rescaled steps `d b * (β b - q * β (b + 1))` with `d b = (q ^ (b + 1) - 1) / (q - 1)`
are triangular coordinates that keep the degree. -/
private lemma volume_real_pieriCone_inter_degreeSlab_one (k : ℕ) {q : ℝ} (hq : 1 < q) :
    volume.real (pieriCone (fun _ : ZMod 1 ↦ true) q ∩ degreeSlab k (1 : ZMod 1 → ℝ)) =
      (∏ l : Fin k, (q ^ (l.val + 1) - 1) / (q - 1))⁻¹ *
        volume.real (degreeSlab k (1 : ZMod 1 → ℝ)) := by
  have h_zero (j : ZMod 1) : j = 0 := Subsingleton.elim _ _
  let d (i : ℕ) : ℝ := (q ^ (i + 1) - 1) / (q - 1)
  have hd_pos (i : ℕ) : 0 < d i := by simp [d, one_lt_pow₀, hq]
  have hd_zero : d 0 = 1 := by simp [d, sub_ne_zero, hq.ne']
  have hd_succ (i : ℕ) : d (i + 1) - 1 = q * d i := by
    simp only [d]; field_simp [sub_ne_zero.2 hq.ne']; ring
  let F : Module.End ℝ (Fin k × ZMod 1 → ℝ) :=
    .pi fun x ↦ d x.1 • (oneCoord k x.1 - q • oneCoord k (x.1 + 1))
  have hF (β : Fin k × ZMod 1 → ℝ) (b : Fin k) :
      F β (b, 0) = d b * (β (b, 0) - q * oneCoord k (b + 1) β) := by simp [F, oneCoord_apply]
  have h_det : LinearMap.det F = ∏ b : Fin k, d b := by
    have h_tri : ((toMatrix' F).reindex (prodUnique _ _) (prodUnique _ _)).IsUpperTriangular := by
      intro b b' h_lt
      have h_ne : b.val ≠ b'.val ∧ b.val + 1 ≠ b'.val :=
        ⟨(Fin.lt_def.1 h_lt).ne', (Nat.lt_succ_of_lt (Fin.lt_def.1 h_lt)).ne'⟩
      simp [Fin.ext_iff, F, oneCoord, DFunLike.dite_apply, h_ne]
    rw [← det_toMatrix', ← det_reindex_self (prodUnique _ _), det_of_isUpperTriangular h_tri]
    simp [Fin.ext_iff, F, oneCoord, DFunLike.dite_apply, h_zero]
  have h_det_pos : 0 < LinearMap.det F := by simp [prod_pos, h_det, hd_pos]
  -- The degree telescopes: `d (b + 1) - 1 = q * d b`.
  have h_deg (β : Fin k × ZMod 1 → ℝ) : ∑ b, F β (b, 0) = ∑ b, β (b, 0) := by
    rw [← sub_eq_zero, ← sum_sub_distrib]
    calc ∑ b : Fin k, (F β (b, 0) - β (b, 0))
        = ∑ b ∈ range k, ((d b - 1) * oneCoord k b β - (d (b + 1) - 1) * oneCoord k (b + 1) β) := by
          rw [sum_range]
          exact sum_congr rfl fun b _ ↦ by rw [hF, hd_succ, oneCoord_apply]; ring
      _ = 0 := by
          rw [sum_range_sub' fun b ↦ (d b - 1) * oneCoord k b β]
          simp [hd_zero, oneCoord]
  have h_pre : pieriCone (fun _ : ZMod 1 ↦ true) q ∩ degreeSlab k 1 = F ⁻¹' degreeSlab k 1 := by
    ext β
    have h_nonneg : 0 ≤ F β ↔ ∀ b : Fin k, q * oneCoord k (b + 1) β ≤ β (b, 0) := by
      simp [Pi.le_def, h_zero, hF, hd_pos]
    simp [mem_pieriCone, mem_degreeSlab, h_zero, h_deg, ← and_assoc, h_nonneg,
      ← pieri_and_nonneg_iff (zero_le_one.trans hq.le)]
  rw [h_pre, Measure.real, Measure.addHaar_preimage_linearMap _ h_det_pos.ne',
    ENNReal.toReal_mul, ENNReal.toReal_ofReal (abs_nonneg _), abs_inv, abs_of_pos h_det_pos,
    h_det, Measure.real]

end OneLetter

/-- The determinant of `1 - c • id` on `ℝ ^ k` is `(1 - c) ^ k`. -/
private lemma det_one_sub_smul_funLeft_one (c : ℝ) :
    LinearMap.det (1 - c • funLeft ℝ ℝ ⇑(1 : Perm (Fin k))) = (1 - c) ^ k := by
  have h_eq : (1 : Module.End ℝ (Fin k → ℝ)) - c • funLeft ℝ ℝ ⇑(1 : Perm (Fin k)) =
      (1 - c) • LinearMap.id := by
    ext x b
    simp [sub_mul]
  rw [h_eq, LinearMap.det_smul, LinearMap.det_id, Module.finrank_fin_fun, mul_one]

/-- **The share of the Pieri cone in a slab, as a signed sum.** Let `P > 1`, `N ≥ 1` and
`q = P ^ N`, and let `Ω` be a set whose preimage under the step map is the Pieri cone. Then `Ω`
fills the fraction `(1 - 1 / q) ^ k / k ! * ∑ τ, sign τ / |det (1 - τ / q)|` of the slab
`degreeSlab k D`, where the permutation `τ` of `Fin k` acts on `ℝ ^ k` by permuting coordinates.
In particular the share depends only on `k` and `q`. -/
theorem volume_real_inter_degreeSlab_eq_signed_sum {N : ℕ} [NeZero N] {v : ZMod N → Bool}
    {P : ℝ} (hP : 1 < P) (D : ZMod N → ℝ) {Ω : Set (Fin k × ZMod N → ℝ)}
    (hΩ : pieriStepMap v P 1 ⁻¹' Ω = pieriCone v P) :
    volume.real (Ω ∩ degreeSlab k D) =
      (1 - (P ^ N)⁻¹) ^ k / k.factorial *
        (∑ τ : Perm (Fin k),
          (Perm.sign τ : ℝ) / |LinearMap.det (1 - (P ^ N)⁻¹ • funLeft ℝ ℝ ⇑τ)|) *
          volume.real (degreeSlab k D) := by
  obtain ⟨m, rfl⟩ : ∃ m : ℕ, N = m + 1 := Nat.exists_eq_succ_of_ne_zero (NeZero.ne N)
  have h_nonneg : 0 ≤ 1 - (P ^ (m + 1))⁻¹ :=
    sub_nonneg.2 (inv_le_one_of_one_le₀ (one_le_pow₀ hP.le))
  have h := volume_real_inter_degreeSlab_eq_signed_sum_aux v P hP D hΩ
  rw [det_one_sub_smul_funLeft_one, abs_of_nonneg (pow_nonneg h_nonneg k)] at h
  exact h

/-- **The share of the Pieri cone in a slab.** Let `P > 1`, `N ≥ 1` and `q = P ^ N`, let
`v j` be a sign for each letter `j : ZMod N`, and let `Ω` be a set whose preimage under the step
map `pieriStepMap v P 1` is the Pieri cone `pieriCone v P`. Then
`∏ l < k, (q ^ (l + 1) - 1) / (q - 1)` times the volume of `Ω ∩ degreeSlab k D` is the volume of
the slab `degreeSlab k D`. -/
theorem prod_mul_volume_real_inter_degreeSlab {N : ℕ} [NeZero N] {v : ZMod N → Bool} {P : ℝ}
    (hP : 1 < P) (D : ZMod N → ℝ) {Ω : Set (Fin k × ZMod N → ℝ)}
    (hΩ : pieriStepMap v P 1 ⁻¹' Ω = pieriCone v P) :
    (∏ l : Fin k, ((P ^ N) ^ (l.val + 1) - 1) / (P ^ N - 1)) * volume.real (Ω ∩ degreeSlab k D) =
      volume.real (degreeSlab k D) := by
  -- By the signed sum, the share `c` of `Ω` in the slab depends only on `k` and `q`. So it can be
  -- computed for one letter with the sign `+` and `q` in place of `P`.
  set q : ℝ := P ^ N
  have hq : 1 < q := one_lt_pow₀ hP (NeZero.ne N)
  let c : ℝ := (1 - q⁻¹) ^ k / k.factorial *
    ∑ τ : Perm (Fin k), (Perm.sign τ : ℝ) / |LinearMap.det (1 - q⁻¹ • funLeft ℝ ℝ ⇑τ)|
  have h_share : volume.real (Ω ∩ degreeSlab k D) = c * volume.real (degreeSlab k D) :=
    volume_real_inter_degreeSlab_eq_signed_sum hP D hΩ
  have h_block : volume.real (pieriCone (fun _ : ZMod 1 ↦ true) q ∩ degreeSlab k (1 : ZMod 1 → ℝ)) =
      c * volume.real (degreeSlab k (1 : ZMod 1 → ℝ)) := by
    -- For one letter the step map is the homothety of ratio `q - 1 > 0`.
    have h_cone : pieriStepMap (fun _ : ZMod 1 ↦ true) q 1 ⁻¹' pieriCone (fun _ ↦ true) q =
        pieriCone (k := k) (fun _ : ZMod 1 ↦ true) q := by
      have h_pos : 0 < q - 1 := sub_pos.2 hq
      have h_zero (j : ZMod 1) : j = 0 := Subsingleton.elim _ _
      ext ν
      simp only [Set.mem_preimage, mem_pieriCone, pieriStepMap_apply, ite_true, one_mul,
        Pi.one_apply, Perm.coe_one, id_eq, h_zero]
      refine forall_congr' fun _ ↦ forall_congr' fun b ↦ forall_congr' fun b' ↦
        imp_congr_right fun _ ↦ ?_
      rw [show q * (q * ν (b', 0) - ν (b', 0)) = (q - 1) * (q * ν (b', 0)) by ring,
        show q * ν (b, 0) - ν (b, 0) = (q - 1) * ν (b, 0) by ring]
      exact mul_le_mul_iff_of_pos_left h_pos
    simpa only [pow_one] using volume_real_inter_degreeSlab_eq_signed_sum (N := 1) hq 1 h_cone
  have hc : (∏ l : Fin k, (q ^ (l.val + 1) - 1) / (q - 1))⁻¹ = c :=
    mul_right_cancel₀ (volume_real_degreeSlab_one_pos k).ne'
      ((volume_real_pieriCone_inter_degreeSlab_one k hq).symm.trans h_block)
  rw [h_share, ← hc, mul_inv_cancel_left₀ (prod_pos fun l _ ↦ by simp [one_lt_pow₀, hq]).ne']

end TauCeti
