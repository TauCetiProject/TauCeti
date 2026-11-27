/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import TauCeti.LinearAlgebra.QuadraticForm.Arf.Classification

/-!
# The Arf invariant over `𝔽₂`: checks

These examples verify the characteristic-two quadratic invariants and normal-form properties on
concrete low-dimensional spaces over `ZMod 2`:

* On the zero-dimensional space `Fin 0 → ZMod 2`, the Arf invariant is `0`, the Gauss sum is `1`,
  and `0` is the unique isotropic vector (`1` zero, whereas substituting `m = 0` into the `m ≥ 1`
  formula with natural subtraction would give `2`).
* On `𝔽₂²`, the hyperbolic plane `[0, 0]` (`x * y`) has Arf invariant `0`, Gauss sum `2`, and a
  totally isotropic polar-Lagrangian coordinate line `(ZMod 2) ∙ ![1, 0]`, whereas the anisotropic
  plane `[1, 1]` (`x ^ 2 + x * y + y ^ 2`) has Arf invariant `1`, Gauss sum `-2`, and no nonzero
  isotropic vector.
* Changing from the standard symplectic basis `![1, 0], ![0, 1]` of `[0, 0]` to the sheared
  symplectic basis `a = ![1, 1], b = ![0, 1]` (`polar [0, 0] a b = 1`) moves the linear sum
  `q a + q b` from `0` to `1`, while the Arf product `q a * q b = 0` remains invariant.
* The orthogonal sum `[1, 1] ⊕ [1, 1]` on `𝔽₂⁴` has Arf invariant `0` (whereas the product of plane
  invariants would give `1`), Gauss sum `4`, `10` isotropic vectors (matching `[0, 0] ⊕ [0, 0]`),
  and a two-dimensional totally isotropic diagonal subspace equal to its own polar orthogonal
  complement.

## References

* C. Arf, *Untersuchungen über quadratische Formen in Körpern der Charakteristik 2 (Teil I)*, J.
  Reine Angew. Math. **183** (1941), 148--167.
* A. Pyronneau, *The Arf and Rohklin's invariant* (January 2024), §2.1, pp. 4--5.
-/

open QuadraticMap

namespace TauCeti

/-- On the zero-dimensional `𝔽₂`-space `Fin 0 → ZMod 2`, the Arf invariant vanishes, the Gauss sum
is `1`, and `0` is the sole isotropic vector. -/
example (Q : QuadraticForm (ZMod 2) (Fin 0 → ZMod 2)) :
    Q.arf = 0 ∧ Q.gaussSum = 1 ∧ Fintype.card {v : Fin 0 → ZMod 2 // Q v = 0} = 1 :=
  ⟨Q.arf_subsingleton, Q.gaussSum_subsingleton, Q.card_subtype_apply_eq_zero_eq_one_of_subsingleton⟩

/-- On `𝔽₂²`, the hyperbolic plane `[0, 0]` has Arf invariant `0`, Gauss sum `2`, and a totally
isotropic coordinate line equal to its own polar orthogonal complement. -/
example :
    (binaryQuadraticForm (ZMod 2) 0 0).arf = 0 ∧
      (binaryQuadraticForm (ZMod 2) 0 0).gaussSum = 2 ∧
      (binaryQuadraticForm (ZMod 2) 0 0).IsTotallyIsotropic ((ZMod 2) ∙ ![(1 : ZMod 2), 0]) ∧
      LinearMap.BilinForm.orthogonal (binaryQuadraticForm (ZMod 2) 0 0).polarBilin
        ((ZMod 2) ∙ ![(1 : ZMod 2), 0]) = (ZMod 2) ∙ ![(1 : ZMod 2), 0] := by
  refine ⟨by simp, by simp, ?_, orthogonal_polarBilin_binaryQuadraticForm_span_one_zero 0 0⟩
  rw [isTotallyIsotropic_span_singleton_iff]
  simp

/-- On `𝔽₂²`, the anisotropic plane `[1, 1]` has Arf invariant `1`, Gauss sum `-2`, and no nonzero
isotropic vector. -/
example :
    (binaryQuadraticForm (ZMod 2) 1 1).arf = 1 ∧
      (binaryQuadraticForm (ZMod 2) 1 1).gaussSum = -2 ∧
      (binaryQuadraticForm (ZMod 2) 1 1).Anisotropic :=
  ⟨by simp, by simp [ZMod.val_one], anisotropic_binaryQuadraticForm_one⟩

/-- On `[0, 0]`, the sheared symplectic pair `a = ![1, 1]`, `b = ![0, 1]` satisfies
`polar [0, 0] a b = 1` and preserves the Arf product `q a * q b = 0`, whereas `q a + q b = 1`
differs from the value `0` on the standard symplectic basis `![1, 0], ![0, 1]`. -/
example :
    let q := binaryQuadraticForm (ZMod 2) 0 0
    let a : Fin 2 → ZMod 2 := ![1, 1]
    let b : Fin 2 → ZMod 2 := ![0, 1]
    polar q a b = 1 ∧ q a * q b = q.arf ∧ q a + q b = 1 ∧
      q ![1, 0] + q ![0, 1] = 0 := by
  simp

/-- Two copies `[1, 1] ⊕ [1, 1]` of the anisotropic plane on `𝔽₂⁴` have Arf invariant `0`, Gauss
sum `4`, `10` isotropic vectors (matching `[0, 0] ⊕ [0, 0]`), and a two-dimensional totally
isotropic diagonal subspace equal to its own polar orthogonal complement. -/
example :
    let Q := binaryQuadraticForm (ZMod 2) 1 1
    let H := binaryQuadraticForm (ZMod 2) 0 0
    let Δ := LinearMap.range
      (LinearMap.inl (ZMod 2) (Fin 2 → ZMod 2) (Fin 2 → ZMod 2) +
        LinearMap.inr (ZMod 2) (Fin 2 → ZMod 2) (Fin 2 → ZMod 2))
    (Q.prod Q).arf = 0 ∧
      (Q.prod Q).gaussSum = 4 ∧
      Fintype.card {v // (Q.prod Q) v = 0} = 10 ∧
      Fintype.card {v // (H.prod H) v = 0} = 10 ∧
      (Q.prod Q).IsTotallyIsotropic Δ ∧
      LinearMap.BilinForm.orthogonal (Q.prod Q).polarBilin Δ = Δ ∧
      Module.finrank (ZMod 2) Δ = 2 := by
  intro Q H Δ
  have hndQ : (Q.prod Q).polarBilin.Nondegenerate :=
    nondegenerate_polarBilin_prod_iff.mpr
      ⟨nondegenerate_polarBilin_binaryQuadraticForm 1 1,
        nondegenerate_polarBilin_binaryQuadraticForm 1 1⟩
  have hndH : (H.prod H).polarBilin.Nondegenerate :=
    nondegenerate_polarBilin_prod_iff.mpr
      ⟨nondegenerate_polarBilin_binaryQuadraticForm 0 0,
        nondegenerate_polarBilin_binaryQuadraticForm 0 0⟩
  have hdim : Module.finrank (ZMod 2) ((Fin 2 → ZMod 2) × (Fin 2 → ZMod 2)) = 2 * 2 := by
    simp [Module.finrank_prod]
  have hcardQ : (Fintype.card {v // (Q.prod Q) v = 0} : ℤ) = 10 := by
    rw [(Q.prod Q).card_subtype_apply_eq_zero_of_pos_of_finrank_eq hndQ (by decide) hdim,
      arf_prod_self]
    norm_num
  have hcardH : (Fintype.card {v // (H.prod H) v = 0} : ℤ) = 10 := by
    rw [(H.prod H).card_subtype_apply_eq_zero_of_pos_of_finrank_eq hndH (by decide) hdim,
      arf_prod_self]
    norm_num
  have hiso : (Q.prod Q).IsTotallyIsotropic Δ := isTotallyIsotropic_range_inl_add_inr_prod_self Q
  have horth : LinearMap.BilinForm.orthogonal (Q.prod Q).polarBilin Δ = Δ :=
    orthogonal_range_inl_add_inr_prod_self (nondegenerate_polarBilin_binaryQuadraticForm 1 1).1
  have hrad : (Q.prod Q).radical = ⊥ :=
    eq_bot_mono (Q.prod Q).radical_le_ker_polarBilin
      (LinearMap.BilinForm.Nondegenerate.ker_eq_bot hndQ)
  have h2Δ : 2 * Module.finrank (ZMod 2) Δ = 4 := by
    have h := (hiso.orthogonal_polarBilin_eq_self_iff hrad).mp horth
    rwa [hdim] at h
  refine ⟨arf_prod_self Q, by simp [Q, ZMod.val_one], by exact_mod_cast hcardQ,
    by exact_mod_cast hcardH, hiso, horth, by omega⟩

/-- Transporting the diagonal Lagrangian of `[1, 1] ⊕ [1, 1]` along
`isometryEquivBinaryQuadraticFormOneProd` gives a totally isotropic polar-self-orthogonal subspace
of `[0, 0] ⊕ [0, 0]`. -/
example :
    let H := binaryQuadraticForm (ZMod 2) 0 0
    let Δ := LinearMap.range
      (LinearMap.inl (ZMod 2) (Fin 2 → ZMod 2) (Fin 2 → ZMod 2) +
        LinearMap.inr (ZMod 2) (Fin 2 → ZMod 2) (Fin 2 → ZMod 2))
    let e := isometryEquivBinaryQuadraticFormOneProd (R := ZMod 2)
    let L := Δ.map e.toLinearMap
    (H.prod H).IsTotallyIsotropic L ∧
      LinearMap.BilinForm.orthogonal (H.prod H).polarBilin L = L := by
  intro H Δ e L
  refine ⟨e.toIsometry.isTotallyIsotropic_map_iff.mpr
    (isTotallyIsotropic_range_inl_add_inr_prod_self (binaryQuadraticForm (ZMod 2) 1 1)), ?_⟩
  dsimp only [H, L]
  rw [← e.map_orthogonal_polarBilin,
    orthogonal_range_inl_add_inr_prod_self (nondegenerate_polarBilin_binaryQuadraticForm 1 1).1]

end TauCeti
