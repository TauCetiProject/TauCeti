/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Fintype.Perm
public import Mathlib.Topology.Algebra.Module.Multilinear.Topology

/-!
# Symmetrization of continuous multilinear maps

For a finite index type `ι`, the symmetrization of a continuous multilinear map
`A : (ι → F) → G` is

`symmetrize A v = (1 / |Perm ι|) ∑_σ A (v ∘ σ)`,

the average of `A` over all permutations of its arguments when `|Perm ι|` is invertible in `𝕜`,
as in characteristic zero.

It is a continuous linear map on the space of continuous multilinear maps. Its values are
symmetric, that is, invariant under permuting the arguments, and over a field of characteristic
zero it fixes every symmetric map. So it is a continuous linear projection onto the symmetric
continuous multilinear maps, and it does not change the values on the diagonal. Componentwise,
it is the symmetrization of finite jets `TauCeti.symmetrizeJets`
(`TauCeti.toJets_symmetrizeJets_apply`).

## Main declarations

* `ContinuousMultilinearMap.symmetrize`: the symmetrization, as a continuous linear map.
* `ContinuousMultilinearMap.symmetrize_apply`: its value is `(1 / |Perm ι|)` times the sum over
  permutations.
* `ContinuousMultilinearMap.symmetrize_apply_comp_perm`: its values are symmetric.
* `ContinuousMultilinearMap.symmetrize_eq_self`: it fixes symmetric maps in characteristic zero.
* `ContinuousMultilinearMap.symmetrize_apply_const`: it keeps the values on the diagonal in
  characteristic zero.
-/

public section

noncomputable section

open Equiv

namespace ContinuousMultilinearMap

variable (𝕜 : Type*) [NormedField 𝕜] (ι : Type*) [Fintype ι] [DecidableEq ι]
  (F : Type*) [AddCommGroup F] [Module 𝕜 F] [TopologicalSpace F]
  (G : Type*) [AddCommGroup G] [Module 𝕜 G] [TopologicalSpace G] [IsTopologicalAddGroup G]
  [ContinuousConstSMul 𝕜 G]

/-- The **symmetrization** of continuous multilinear maps: a map `A` is sent to
`(1 / |Perm ι|) ∑_σ A (v ∘ σ)`. When `|Perm ι|` is invertible in `𝕜`, as in characteristic zero,
this is the average of `A` over all permutations of its arguments. -/
def symmetrize :
    ContinuousMultilinearMap 𝕜 (fun _ : ι ↦ F) G →L[𝕜]
      ContinuousMultilinearMap 𝕜 (fun _ : ι ↦ F) G :=
  (Fintype.card (Perm ι) : 𝕜)⁻¹ • ∑ σ : Perm ι, domDomCongrL σ

variable {𝕜 ι F G}

/-- The value of the symmetrization of `A` is `(1 / |Perm ι|)` times the sum of the values of `A`
on the permuted arguments. -/
theorem symmetrize_apply (A : ContinuousMultilinearMap 𝕜 (fun _ : ι ↦ F) G) (v : ι → F) :
    symmetrize 𝕜 ι F G A v = (Fintype.card (Perm ι) : 𝕜)⁻¹ • ∑ σ : Perm ι, A (v ∘ σ) := by
  simp only [symmetrize, _root_.smul_apply, _root_.sum_apply]
  -- `domDomCongrL σ A v` unfolds to `A (v ∘ σ)`; Mathlib states no apply lemma for `domDomCongrL`.
  rfl

/-- **The symmetrization is symmetric**: permuting the arguments does not change its value. -/
theorem symmetrize_apply_comp_perm (A : ContinuousMultilinearMap 𝕜 (fun _ : ι ↦ F) G)
    (v : ι → F) (τ : Perm ι) : symmetrize 𝕜 ι F G A (v ∘ τ) = symmetrize 𝕜 ι F G A v := by
  rw [symmetrize_apply, symmetrize_apply]
  congr 1
  -- Reindex the sum by `σ ↦ τ * σ`.
  exact Fintype.sum_equiv (Equiv.mulLeft τ) _ _ fun σ ↦ rfl

/-- **The symmetrization fixes symmetric maps** over a field of characteristic zero. -/
theorem symmetrize_eq_self [CharZero 𝕜] {A : ContinuousMultilinearMap 𝕜 (fun _ : ι ↦ F) G}
    (hA : ∀ (v : ι → F) (σ : Perm ι), A (v ∘ σ) = A v) : symmetrize 𝕜 ι F G A = A := by
  ext v
  have hcard : (Fintype.card (Perm ι) : 𝕜) ≠ 0 := Nat.cast_ne_zero.2 Fintype.card_ne_zero
  rw [symmetrize_apply, Finset.sum_congr rfl fun σ _ ↦ hA v σ, Finset.sum_const,
    Finset.card_univ, ← Nat.cast_smul_eq_nsmul 𝕜, smul_smul, inv_mul_cancel₀ hcard, one_smul]

/-- **The symmetrization keeps the values on the diagonal** over a field of characteristic
zero. -/
@[simp]
theorem symmetrize_apply_const [CharZero 𝕜] (A : ContinuousMultilinearMap 𝕜 (fun _ : ι ↦ F) G)
    (x : F) : symmetrize 𝕜 ι F G A (fun _ ↦ x) = A (fun _ ↦ x) := by
  have hcard : (Fintype.card (Perm ι) : 𝕜) ≠ 0 := Nat.cast_ne_zero.2 Fintype.card_ne_zero
  -- Permuting the arguments of a constant tuple does not change it.
  rw [symmetrize_apply]
  change (Fintype.card (Perm ι) : 𝕜)⁻¹ • ∑ _σ : Perm ι, A (fun _ ↦ x) = _
  rw [Finset.sum_const, Finset.card_univ, ← Nat.cast_smul_eq_nsmul 𝕜, smul_smul,
    inv_mul_cancel₀ hcard, one_smul]

/-- The symmetrization is idempotent over a field of characteristic zero. -/
@[simp]
theorem symmetrize_symmetrize [CharZero 𝕜] (A : ContinuousMultilinearMap 𝕜 (fun _ : ι ↦ F) G) :
    symmetrize 𝕜 ι F G (symmetrize 𝕜 ι F G A) = symmetrize 𝕜 ι F G A :=
  symmetrize_eq_self (symmetrize_apply_comp_perm A)

end ContinuousMultilinearMap
