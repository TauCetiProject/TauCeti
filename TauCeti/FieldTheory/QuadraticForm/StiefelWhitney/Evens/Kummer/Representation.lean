/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.FieldTheory.GaloisCohomology.MuTwo.EvensNorm
public import TauCeti.FieldTheory.QuadraticForm.StiefelWhitney.Evens.TracePlane
public import TauCeti.LinearAlgebra.Matrix.PinPlusPlane.Basic

/-!
# The Galois action on the transferred plane

Let `L/K` be a quadratic extension, `σ : L → Kˢ` a `K`-embedding, `a ∈ Lˣ` with a square root
`r² = σ(a)`, and `s ∈ G_K` outside `G_L = galoisSubgroup K L σ`. The transferred plane is realized
inside `(Kˢ)²` by the Kummer points `φ(y) = (σ(y) r, s(σ(y) r))` (`TauCeti.kummerPoint`), whose
dot product is the twisted trace pairing (`TauCeti.kummerPoint_dotProduct`).

This file computes the action of `G_K` on these points coordinatewise: it is given by the
transpose of the signed-permutation matrix of `ρ_a = Ind α_a : G_K → C₂ ≀ C₂`
(`TauCeti.kummerInd`), the representation induced from the Kummer character `α_a` of `G_L`:

```text
g(φ(y)) = ρ_a(g)ᵀ φ(y).
```

At `y = 1` this says that the columns of `ρ_a(g)` record the images of the roots `r` and `s r`
of `X² − σ(a)` and `X² − s(σ(a))` under `g`, in the basis `(r, s r)`. The map `g ↦ ρ_a(g)ᵀ` is an
anti-homomorphism, while `ρ_a` itself is a homomorphism. This is the representation through which
the Evens norm of the Kummer class of `a` is computed, by diagonalizing `ρ_a` in an orthogonal
basis of the transferred form.

## Main results

* `TauCeti.kummerPoint_galois`: `g(φ(y)) = ρ_a(g)ᵀ φ(y)`.

## References

* J.-P. Serre, *L'invariant de Witt de la forme Tr(x²)*, Comment. Math. Helv. **59** (1984),
  651–676, second proof of Théorème 1′.
* B. Kahn, *Classes de Stiefel-Whitney de formes quadratiques et de représentations galoisiennes
  réelles*, Invent. Math. **78** (1984), 223–256, Lemme II.2.1.
-/

public section

noncomputable section

open scoped Matrix

namespace TauCeti

open ContCohomology WreathC2

universe u

variable {K : Type u} [Field K] {L : Type u} [Field L] [Algebra K L] [FiniteDimensional K L]

/-- **The Galois action on the transferred plane** is the transpose of the induced Kummer
representation: for `g ∈ G_K`, applying `g` to the coordinates of the Kummer point
`φ(y) = (σ(y) r, s(σ(y) r))` gives `ρ_a(g)ᵀ φ(y)`, where `ρ_a = kummerInd σ hdeg a r hr s hs`
acts on `(Kˢ)²` by signed permutations. -/
theorem kummerPoint_galois (σ : L →ₐ[K] SeparableClosure K) (hdeg : Module.finrank K L = 2)
    (a : Lˣ) (r : SeparableClosure K) (hr : r ^ 2 = σ (a : L)) (s : AbsoluteGaloisGroup K)
    (hs : s ∉ galoisSubgroup K L σ) (y : L) (g : AbsoluteGaloisGroup K) :
    (fun i => g (kummerPoint σ r s y i)) =
      (wreathSignedPerm (kummerInd σ hdeg a r hr s hs g))ᵀ *ᵥ kummerPoint σ r s y := by
  let U := (galoisSubgroup K L σ).toSubgroup
  have hU : U.index = 2 := (galoisSubgroup_index K L σ).trans hdeg
  have hsU : s ∉ U := hs
  let α := galoisKummerCharacter σ a r hr
  have hind : kummerInd σ hdeg a r hr s hs = indexTwoInd U hU s hsU α := kummerInd_def ..
  have hφ {q : AbsoluteGaloisGroup K} (hq : q ∈ U) :=
    apply_mul_eq_neg_one_pow_rootSign_mul σ hr y hq
  rw [hind]
  by_cases hg : g ∈ U
  · -- `g ∈ G_L` preserves the coset of `s`: `ρ_a(g)` is diagonal, with signs `α_a(g)` and
    -- `α_a(s⁻¹ g s)`.
    have hsg : s⁻¹ * g ∉ U := by simp [Subgroup.mul_mem_iff_of_index_two hU, hsU, hg]
    have hsgs : s⁻¹ * g * s ∈ U := by
      rw [Subgroup.mul_mem_iff_of_index_two hU]
      simp [hsg, hsU]
    have hA : coordA (indexTwoInd U hU s hsU α g) = rootSign r g := by
      rw [coordA_indexTwoInd, evensB1_of_mem hg, evensExtend_of_mem hg]
      exact toAdd_galoisKummerCharacter σ a r hr _
    have hB : coordB (indexTwoInd U hU s hsU α g) = rootSign r (s⁻¹ * g * s) := by
      rw [coordB_indexTwoInd, evensBs_apply, evensB1_of_notMem hsg, evensExtend_of_mem hsgs]
      exact toAdd_galoisKummerCharacter σ a r hr _
    have hC : coordC (indexTwoInd U hU s hsU α g) = 0 := by
      rw [coordC_indexTwoInd, Subgroup.toAdd_indexTwoCharacter_of_mem hU hg]
    have h₁ : g (s (σ y * r)) = s ((s⁻¹ * g * s) (σ y * r)) := by
      simp only [← AlgEquiv.mul_apply, ← mul_assoc, mul_inv_cancel, one_mul]
    ext i
    fin_cases i
    · simp only [Fin.zero_eta, kummerPoint_apply_zero]
      rw [hφ hg]
      simp [wreathSignedPerm_apply, hA, hB, hC, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
    · simp only [Fin.mk_one, kummerPoint_apply_one]
      rw [h₁, hφ hsgs]
      simp [wreathSignedPerm_apply, hA, hB, hC, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  · -- `g ∉ G_L` swaps the two cosets: `ρ_a(g)` is anti-diagonal, with signs `α_a(g s)` and
    -- `α_a(s⁻¹ g)`.
    have hgs : g * s ∈ U := by
      rw [Subgroup.mul_mem_iff_of_index_two hU]
      simp [hg, hsU]
    have hsg : s⁻¹ * g ∈ U := by
      rw [Subgroup.mul_mem_iff_of_index_two hU]
      simp [hsU, hg]
    have hA : coordA (indexTwoInd U hU s hsU α g) = rootSign r (g * s) := by
      rw [coordA_indexTwoInd, evensB1_of_notMem hg, evensExtend_of_mem hgs]
      exact toAdd_galoisKummerCharacter σ a r hr _
    have hB : coordB (indexTwoInd U hU s hsU α g) = rootSign r (s⁻¹ * g) := by
      rw [coordB_indexTwoInd, evensBs_apply, evensB1_of_mem hsg, evensExtend_of_mem hsg]
      exact toAdd_galoisKummerCharacter σ a r hr _
    have hC : coordC (indexTwoInd U hU s hsU α g) = 1 := by
      rw [coordC_indexTwoInd, Subgroup.toAdd_indexTwoCharacter_of_notMem hU hg]
    have h₀ : g (σ y * r) = s ((s⁻¹ * g) (σ y * r)) := by
      simp only [← AlgEquiv.mul_apply, ← mul_assoc, mul_inv_cancel, one_mul]
    ext i
    fin_cases i
    · simp only [Fin.zero_eta, kummerPoint_apply_zero]
      rw [h₀, hφ hsg]
      simp [wreathSignedPerm_apply, hA, hB, hC, Matrix.mulVec, Matrix.mul_apply, dotProduct,
        Fin.sum_univ_two, pinE2_def, ZMod.val_one]
    · simp only [Fin.mk_one, kummerPoint_apply_one]
      rw [← AlgEquiv.mul_apply, hφ hgs]
      simp [wreathSignedPerm_apply, hA, hB, hC, Matrix.mulVec, Matrix.mul_apply, dotProduct,
        Fin.sum_univ_two, pinE2_def, ZMod.val_one]

end TauCeti
