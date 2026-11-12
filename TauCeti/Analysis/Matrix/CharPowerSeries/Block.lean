/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Matrix.FiniteCompression

/-!
# Block-triangular principal-minor series

The principal-minor series of a block-triangular matrix is the product of the series of its
diagonal blocks, provided the defining families of principal minors are summable. This includes
dependent block-diagonal matrices with finitely many blocks. The coordinate index types can be
infinite or empty, and the coefficient ring can have nilpotents.

This factorization separates the determinant on an invariant coordinate summand from the
determinant on its quotient. It follows by passing to the limit in finite coordinate
compressions; no convergence of input truncations in operator norm is required.

## References

* J.-P. Serre, *Endomorphismes complètement continus des espaces de Banach p-adiques*,
  Publ. Math. IHÉS **12** (1962), 69–85, §§4–5.
-/

public section

open Filter Finset Topology
open scoped PowerSeries.WithPiTopology

namespace Matrix

variable {ι κ R : Type*} [DecidableEq ι] [DecidableEq κ]

section TopologicalRing

variable [CommRing R] [TopologicalSpace R] [IsTopologicalRing R] [T2Space R]

/-- The principal-minor series of an upper block-triangular matrix is the product of the
series of its diagonal blocks. Summability is required for the three families of minors;
no norm, completeness, or reducedness assumption on the coefficient ring is needed. -/
@[simp]
theorem charPowerSeries_fromBlocks_zero₂₁
    (A : Matrix ι ι R) (B : Matrix ι κ R) (D : Matrix κ κ R)
    (hA : ∀ n, Summable fun s : {s : Finset ι // s.card = n} ↦ A.principalMinor s)
    (hD : ∀ n, Summable fun s : {s : Finset κ // s.card = n} ↦ D.principalMinor s)
    (hM : ∀ n, Summable fun s : {s : Finset (ι ⊕ κ) // s.card = n} ↦
      (fromBlocks A B 0 D).principalMinor s) :
    (fromBlocks A B 0 D).charPowerSeries = A.charPowerSeries * D.charPowerSeries := by
  have hcofinal : Tendsto (fun p : Finset ι × Finset κ ↦ p.1.disjSum p.2)
      atTop atTop := Finset.sumEquiv.symm.tendsto_atTop
  have hleft := (TauCeti.tendsto_charpolyRev_finiteCompression hM).comp hcofinal
  have hfst : Tendsto (Prod.fst : Finset ι × Finset κ → Finset ι) atTop atTop := by
    rw [← prod_atTop_atTop_eq]
    exact tendsto_fst
  have hsnd : Tendsto (Prod.snd : Finset ι × Finset κ → Finset κ) atTop atTop := by
    rw [← prod_atTop_atTop_eq]
    exact tendsto_snd
  have hright := ((TauCeti.tendsto_charpolyRev_finiteCompression hA).comp hfst).mul
    ((TauCeti.tendsto_charpolyRev_finiteCompression hD).comp hsnd)
  apply tendsto_nhds_unique hleft
  convert hright using 1
  ext p n
  simp only [Function.comp_apply, ← Polynomial.coe_mul]
  rw [charpolyRev_submatrix_fromBlocks_zero₂₁]

/-- The principal-minor series of a lower block-triangular matrix is the product of the
series of its diagonal blocks, whenever the defining families of minors are summable. -/
@[simp]
theorem charPowerSeries_fromBlocks_zero₁₂
    (A : Matrix ι ι R) (C : Matrix κ ι R) (D : Matrix κ κ R)
    (hA : ∀ n, Summable fun s : {s : Finset ι // s.card = n} ↦ A.principalMinor s)
    (hD : ∀ n, Summable fun s : {s : Finset κ // s.card = n} ↦ D.principalMinor s)
    (hM : ∀ n, Summable fun s : {s : Finset (ι ⊕ κ) // s.card = n} ↦
      (fromBlocks A 0 C D).principalMinor s) :
    (fromBlocks A 0 C D).charPowerSeries = A.charPowerSeries * D.charPowerSeries := by
  let e := Equiv.sumComm κ ι
  have hmatrix : (fromBlocks A 0 C D).submatrix e e = fromBlocks D C 0 A := by
    ext i j
    rcases i with i | i <;> rcases j with j | j <;> rfl
  have hsum (n : ℕ) : Summable fun s : {s : Finset (κ ⊕ ι) // s.card = n} ↦
      (fromBlocks D C 0 A).principalMinor s := by
    let E : {s : Finset (κ ⊕ ι) // s.card = n} ≃
        {s : Finset (ι ⊕ κ) // s.card = n} :=
      e.finsetCongr.subtypeEquiv fun s ↦ by simp
    have h := E.summable_iff.mpr (hM n)
    refine h.congr fun s ↦ ?_
    simp only [Function.comp_apply, E, Equiv.subtypeEquiv_apply, Equiv.finsetCongr_apply]
    rw [← principalMinor_submatrix _ e.toEmbedding, Equiv.coe_toEmbedding, hmatrix]
  rw [← charPowerSeries_submatrix_equiv (fromBlocks A 0 C D) e, hmatrix,
    charPowerSeries_fromBlocks_zero₂₁ D C A hD hA hsum, mul_comm]

/-- The principal-minor series of a finite dependent block-diagonal matrix is the product of
the series of its blocks. Summability is required blockwise and for the assembled matrix. -/
@[simp]
theorem charPowerSeries_blockDiagonal' {o : Type*} {m : o → Type*}
    [Fintype o] [DecidableEq o] [∀ i, DecidableEq (m i)] (A : ∀ i, Matrix (m i) (m i) R)
    (hA : ∀ i n, Summable fun s : {s : Finset (m i) // s.card = n} ↦
      (A i).principalMinor s)
    (hM : ∀ n, Summable fun s : {s : Finset (Σ i, m i) // s.card = n} ↦
      (blockDiagonal' A).principalMinor s) :
    (blockDiagonal' A).charPowerSeries = ∏ i, (A i).charPowerSeries := by
  classical
  let F := fun (i : o) (S : Finset (Σ i, m i)) ↦
    (((A i).submatrix
      (Subtype.val : S.preimage (Sigma.mk i) sigma_mk_injective.injOn → m i)
      Subtype.val).charpolyRev : PowerSeries R)
  have hF (i : o) : Tendsto (F i) atTop (𝓝 (A i).charPowerSeries) :=
    (TauCeti.tendsto_charpolyRev_finiteCompression (hA i)).comp
      (tendsto_finset_preimage_atTop_atTop sigma_mk_injective)
  have hright : Tendsto (fun S ↦ ∏ i, F i S) atTop
      (𝓝 (∏ i, (A i).charPowerSeries)) := by
    simpa using tendsto_finsetProd Finset.univ (fun i _ ↦ hF i)
  apply tendsto_nhds_unique (TauCeti.tendsto_charpolyRev_finiteCompression hM)
  apply hright.congr'
  filter_upwards [] with S
  simp only [F]
  rw [charpolyRev_submatrix_blockDiagonal']
  let P := fun i ↦ ((A i).submatrix
    (Subtype.val : S.preimage (Sigma.mk i) sigma_mk_injective.injOn → m i)
    Subtype.val).charpolyRev
  -- Expose the coercion's ring homomorphism so its finite-product law applies directly.
  change (∏ i, (P i : PowerSeries R)) = ((∏ i, P i : Polynomial R) : PowerSeries R)
  exact (map_prod (Polynomial.coeToPowerSeries.ringHom (R := R)) P Finset.univ).symm

end TopologicalRing

section Ultrametric

variable [NormedCommRing R] [NormOneClass R] [IsUltrametricDist R] [CompleteSpace R]

/-- An upper block-triangular matrix with a null row majorant has determinant equal to the
product of its diagonal-block determinants. No decay of the upper-right block along its
input coordinates is required. -/
theorem charPowerSeries_fromBlocks_zero₂₁_of_norm_le
    (A : Matrix ι ι R) (B : Matrix ι κ R) (D : Matrix κ κ R) {r : ι ⊕ κ → ℝ}
    (h : ∀ i j, ‖fromBlocks A B 0 D i j‖ ≤ r i) (hr : Tendsto r cofinite (𝓝 0)) :
    (fromBlocks A B 0 D).charPowerSeries = A.charPowerSeries * D.charPowerSeries := by
  apply charPowerSeries_fromBlocks_zero₂₁ A B D
  · exact fun n ↦ summable_principalMinor
      (fun i j ↦ h (Sum.inl i) (Sum.inl j))
      (hr.comp Sum.inl_injective.tendsto_cofinite) n
  · exact fun n ↦ summable_principalMinor
      (fun i j ↦ h (Sum.inr i) (Sum.inr j))
      (hr.comp Sum.inr_injective.tendsto_cofinite) n
  · exact summable_principalMinor h hr

/-- A lower block-triangular matrix with a null row majorant has determinant equal to the
product of its diagonal-block determinants. -/
theorem charPowerSeries_fromBlocks_zero₁₂_of_norm_le
    (A : Matrix ι ι R) (C : Matrix κ ι R) (D : Matrix κ κ R) {r : ι ⊕ κ → ℝ}
    (h : ∀ i j, ‖fromBlocks A 0 C D i j‖ ≤ r i) (hr : Tendsto r cofinite (𝓝 0)) :
    (fromBlocks A 0 C D).charPowerSeries = A.charPowerSeries * D.charPowerSeries := by
  apply charPowerSeries_fromBlocks_zero₁₂ A C D
  · exact fun n ↦ summable_principalMinor
      (fun i j ↦ h (Sum.inl i) (Sum.inl j))
      (hr.comp Sum.inl_injective.tendsto_cofinite) n
  · exact fun n ↦ summable_principalMinor
      (fun i j ↦ h (Sum.inr i) (Sum.inr j))
      (hr.comp Sum.inr_injective.tendsto_cofinite) n
  · exact summable_principalMinor h hr

/-- A finite dependent block-diagonal matrix with a null row majorant has determinant equal to
the product of its block determinants. Blocks may have infinite or empty coordinate types. -/
theorem charPowerSeries_blockDiagonal'_of_norm_le {o : Type*} {m : o → Type*}
    [Fintype o] [DecidableEq o] [∀ i, DecidableEq (m i)] (A : ∀ i, Matrix (m i) (m i) R)
    {r : (Σ i, m i) → ℝ} (h : ∀ i j, ‖blockDiagonal' A i j‖ ≤ r i)
    (hr : Tendsto r cofinite (𝓝 0)) :
    (blockDiagonal' A).charPowerSeries = ∏ i, (A i).charPowerSeries := by
  apply charPowerSeries_blockDiagonal' A
  · intro i n
    exact summable_principalMinor (fun j k ↦ by simpa using h ⟨i, j⟩ ⟨i, k⟩)
      (hr.comp sigma_mk_injective.tendsto_cofinite) n
  · exact summable_principalMinor h hr

end Ultrametric

end Matrix
