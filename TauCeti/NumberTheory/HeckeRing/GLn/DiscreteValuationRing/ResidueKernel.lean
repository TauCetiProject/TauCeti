/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.DoubleCoset
public import TauCeti.LinearAlgebra.Matrix.ResidueKernel
public import TauCeti.NumberTheory.HeckeRing.GLn.DiscreteValuationRing.Minuscule


/-!
# The single cosets of `GL_n(R) η_j GL_n(R)` and kernels of reductions

Let `R` be a discrete valuation ring with fraction field `K`, uniformizer `ϖ` with image `π` in
`K`, residue field `k`, and `K₀ = GL_n(R)`. For `0 ≤ j ≤ n` let
`η_j = diag(π^{(j)}, 1^{(n - j)})` (`HeckeRing.GLn.minusculeDiag π n j`). This file describes the
double coset `K₀ η_j K₀` and its decomposition into single cosets `K₀ g` by the kernel of the
reduction `kⁿ → kⁿ` of an integral representative of `g`, written `ker g` below:

* `HeckeRing.GLn.mem_doubleCoset_minusculeDiag_iff`: `K₀ η_j K₀` is the set `D_j` of the `g` such
  that `g` and `π g⁻¹` are integral and `det g` has valuation `j`; in terms of an integral matrix
  `A` with image `g`, the conditions are `A * B = ϖ • 1` for an integral `B` and
  `det A ~ ϖ ^ j`. In particular `K₀ g K₀ = D_j` for every `g ∈ D_j`
  (`DoubleCoset.doubleCoset_eq_of_mem`), and `D_j` is empty for `j > n`
  (`Matrix.le_card_of_associated_det`).
* `HeckeRing.GLn.mul_inv_mem_integralGL_iff_residueKer_eq`: two such `g, g'` (of any valuations)
  satisfy `g g'⁻¹ ∈ K₀`, that is `K₀ g = K₀ g'`, exactly when the reductions of their integral
  representatives have the same kernel; that kernel has dimension `j` for `g ∈ D_j`
  (`Matrix.finrank_residueKer_eq_of_associated_det`).
* `HeckeRing.GLn.exists_residueKer_minusculeDiagLift_mul_eq`: every `j`-dimensional subspace of
  `kⁿ` is that kernel for some `η_j u` with `u ∈ K₀`.

Together, `K₀ g ↦ ker g` is a bijection from the single cosets `K₀ g ⊆ K₀ η_j K₀` to the
`j`-dimensional subspaces of `kⁿ`, with representatives `η_j u`. The number of left cosets
`g K₀ ⊆ K₀ η_j K₀`, which index the split-place Hecke operators `T^{(j)}`, is computed by
`HeckeRing.GLn.degree_minusculeCoset`.

## References

* G. Shimura, *Introduction to the arithmetic theory of automorphic functions*, Princeton
  University Press (1971), §3.2, Proposition 3.16.
* I. G. Macdonald, *Symmetric functions and Hall polynomials*, 2nd ed., Oxford (1995),
  Chapter V, §2.

The description of `K₀ η_j K₀` and of its single cosets by the kernel of the reduction is adapted
from grh-lean (<https://github.com/lsernau/grh-lean>, Apache 2.0, Copyright 2026 Anthropic PBC),
`Lib/Weil/Unramified/HeckeGL.lean`, declarations `New.basicDoubleCoset_eq`,
`New.mul_inv_mem_localIntGL_iff`, `New.basicCosetRep` and
`New.basicCosetRep_mem_and_residueKer_eq`.
-/

public section

open Matrix Module IsLocalRing DoubleCoset TauCeti

namespace HeckeRing.GLn

variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  {K : Type*} [Field K] [Algebra R K] {ϖ : R}

/-- **The single cosets `GL_n(R) g` and the kernel of the reduction.** Let `g, g' ∈ GL_n(K)` have
integral representatives `A, A'` with `A * B = ϖ • 1` and `A' * B' = ϖ • 1` for integral `B, B'`,
that is, `g`, `g'`, `π g⁻¹` and `π g'⁻¹` are integral. Then `g g'⁻¹ ∈ GL_n(R)` exactly when the
reductions of `A` and `A'` have the same kernel. -/
theorem mul_inv_mem_integralGL_iff_residueKer_eq {ι : Type*} [Fintype ι] [DecidableEq ι]
    (hϖ : Irreducible ϖ) (hinj : Function.Injective (algebraMap R K)) {g g' : GL ι K}
    {A B A' B' : Matrix ι ι R} (hA : A.map (algebraMap R K) = g) (h : A * B = ϖ • 1)
    (hA' : A'.map (algebraMap R K) = g') (h' : A' * B' = ϖ • 1) :
    g * g'⁻¹ ∈ integralGL R K ι ↔ A.residueKer = A'.residueKer := by
  rw [eq_comm, ← exists_eq_mul_iff_residueKer_eq hϖ h' h]
  rw [MonoidHom.mem_range]
  refine exists_congr fun U ↦ ?_
  rw [eq_mul_inv_iff_mul_eq, eq_comm]
  simp only [Units.ext_iff, Units.val_mul, GeneralLinearGroup.val_map_apply, ← hA, ← hA',
    ← Matrix.map_mul]
  exact (Matrix.map_injective hinj).eq_iff

variable {π : Kˣ} {n : ℕ}

/-- **Representatives of the single cosets of `K₀ η_j K₀`.** For every subspace `W` of `kⁿ` of
dimension `j`, the integral representative `diag(ϖ^{(j)}, 1^{(n - j)}) u` of `η_j u` has
reduction with kernel `W` for some `u ∈ GL_n(R)`. -/
theorem exists_residueKer_minusculeDiagLift_mul_eq (hϖ : Irreducible ϖ) {j : ℕ}
    {W : Submodule (ResidueField R) (Fin n → ResidueField R)}
    (hW : finrank (ResidueField R) W = j) :
    ∃ U : GL (Fin n) R,
      (minusculeDiagLift ϖ n j * (U : Matrix (Fin n) (Fin n) R)).residueKer = W := by
  have hj : j ≤ n := by simpa [hW] using Submodule.finrank_le W
  refine exists_residueKer_mul_eq (minusculeDiagLift ϖ n j) ?_
  rw [hW, finrank_residueKer_eq_of_associated_det hϖ
    (minusculeDiagLift_mul_minusculeDiagLiftCompl ϖ n j) (by rw [det_minusculeDiagLift ϖ hj])]

/-- **The double coset `K₀ η_j K₀`.** For `j ≤ n`, an element `g ∈ GL_n(K)` lies in
`GL_n(R) η_j GL_n(R)` exactly when it is the image of an integral matrix `A` with
`A * B = ϖ • 1` for some integral `B` (so that `π g⁻¹` is integral) and `det A` associated to
`ϖ ^ j`. -/
theorem mem_doubleCoset_minusculeDiag_iff (hϖ : Irreducible ϖ) (hπ : algebraMap R K ϖ = π)
    {j : ℕ} (hj : j ≤ n) (g : GL (Fin n) K) :
    g ∈ doubleCoset (minusculeDiag π n j) (integralGL R K (Fin n)) (integralGL R K (Fin n)) ↔
      ∃ A B : Matrix (Fin n) (Fin n) R,
        A.map (algebraMap R K) = g ∧ A * B = ϖ • 1 ∧ Associated A.det (ϖ ^ j) := by
  set D := minusculeDiagLift ϖ n j
  set D' := minusculeDiagLiftCompl ϖ n j
  have hDD' : D * D' = ϖ • 1 := minusculeDiagLift_mul_minusculeDiagLiftCompl ϖ n j
  -- `g = u η_j v` lifts to `u D v`, and `π g⁻¹ = v⁻¹ (π η_j⁻¹) u⁻¹` to `v⁻¹ D' u⁻¹`
  have hlift (u v : GL (Fin n) R) :
      ((u : Matrix (Fin n) (Fin n) R) * D * v) * ((v⁻¹ : GL (Fin n) R) * D' * (u⁻¹ : GL _ R)) =
        ϖ • 1 := by
    simp [Matrix.mul_assoc, ← Matrix.mul_assoc D, hDD']
  have hmap (u v : GL (Fin n) R) :
      ((u : Matrix (Fin n) (Fin n) R) * D * v).map (algebraMap R K) =
      ((GeneralLinearGroup.map (algebraMap R K) u * minusculeDiag π n j *
        GeneralLinearGroup.map (algebraMap R K) v : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) := by
    simp [D, Matrix.map_mul, map_minusculeDiagLift hπ]
  constructor
  · rintro hg
    obtain ⟨_, ⟨u, rfl⟩, _, ⟨v, rfl⟩, rfl⟩ := mem_doubleCoset.mp hg
    refine ⟨_, _, hmap u v, hlift u v, ?_⟩
    rw [det_mul, det_mul, det_minusculeDiagLift ϖ hj, mul_assoc]
    exact (associated_unit_mul_left _ _ (isUnits_det_units u)).trans
      (associated_mul_unit_left _ _ (isUnits_det_units v))
  · rintro ⟨A, B, hA, h, hdet⟩
    -- `D u` has the kernel of `Ā` for some `u`, and then `A = v (D u)` for some `v`
    obtain ⟨u, hu⟩ := exists_residueKer_minusculeDiagLift_mul_eq hϖ
      (finrank_residueKer_eq_of_associated_det hϖ h hdet)
    have hDu : D * (u : Matrix (Fin n) (Fin n) R) * ((u⁻¹ : GL (Fin n) R) * D') = ϖ • 1 := by
      simp [Matrix.mul_assoc, hDD']
    obtain ⟨v, hv⟩ := (exists_eq_mul_iff_residueKer_eq hϖ hDu h).mpr hu
    refine mem_doubleCoset.mpr ⟨_, ⟨v, rfl⟩, _, ⟨u, rfl⟩, Units.ext ?_⟩
    rw [← hA, hv, ← Matrix.mul_assoc, hmap v u]

end HeckeRing.GLn
