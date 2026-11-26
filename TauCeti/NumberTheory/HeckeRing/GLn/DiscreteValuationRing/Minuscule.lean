/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Diagonal.Basic
public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.SubspaceOrbit
public import TauCeti.NumberTheory.HeckeRing.GLn.FractionRing

import Mathlib.Data.Fintype.Fin
import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Lift
import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Map
import TauCeti.RingTheory.DiscreteValuationRing.Basic

/-!
# The minuscule double cosets of `GL_n` over a discretely valued field

Let `R` be a discrete valuation ring with fraction field `K`, residue field `k` with `q` elements,
and uniformizer `ϖ` with image `π` in `K`. For `0 ≤ j ≤ n` let

```text
η_j = diag(π, …, π, 1, …, 1)        (π in the first j entries)
```

(`HeckeRing.GLn.minusculeDiag π n j`). This file shows that the double coset
`GL_n(R) η_j GL_n(R)` is the union of as many left cosets `g GL_n(R)` as there are
`j`-dimensional subspaces of `kⁿ`, the Gaussian binomial coefficient `[n, j]_q`
(`HeckeRing.GLn.degree_minusculeCoset`). These are the double cosets of the split-place Hecke
operators `T_w^{(j)}`.

The number of left cosets in `K η K` is the relative index `[K : K ∩ η K η⁻¹]`. An element `γ` of
`K = GL_n(R)` lies in `η_j K η_j⁻¹` exactly when `η_j⁻¹ γ η_j` is integral, that is when the
entries `γ_{ab}` with `a < j ≤ b` lie in the maximal ideal: conjugation divides exactly those
entries by `π` (`HeckeRing.GLn.map_mem_conjAct_minusculeDiag_iff`). These are the elements whose
reduction modulo `ϖ` stabilizes the subspace `S_j ⊆ kⁿ` of vectors vanishing in the first `j`
coordinates (`HeckeRing.GLn.zeroPrefixSubspace`). Reduction `GL_n(R) → GL_n(k)` is surjective, so
the index is that of the stabilizer of `S_j` in `GL_n(k)`, which by the orbit-stabilizer theorem
is the number of `(n - j)`-dimensional subspaces of `kⁿ`, namely `[n, n - j]_q = [n, j]_q`.

## Main definitions

* `HeckeRing.GLn.minusculeDiag π n j`: the diagonal matrix `diag(π^{(j)}, 1^{(n - j)})`.
* `HeckeRing.GLn.zeroPrefixSubspace k n j`: the subspace of `kⁿ` of vectors whose first `j`
  coordinates vanish.

## Main results

* `HeckeRing.GLn.mem_stabilizer_zeroPrefixSubspace_iff`: the stabilizer of `S_j` in `GL_n(k)` is
  the block upper triangular group with vanishing block in rows `< j` and columns `≥ j`.
* `HeckeRing.GLn.map_mem_conjAct_minusculeDiag_iff`: the integral points of `η_j GL_n(R) η_j⁻¹`.
* `HeckeRing.GLn.relIndex_conjAct_minusculeDiag`: `[K : K ∩ η_j K η_j⁻¹]` is the index of the
  stabilizer of `S_j` in `GL_n(k)`.
* `HeckeRing.GLn.degree_minusculeCoset`: `K η_j K` is the union of `[n, j]_q` left cosets, and
  `HeckeRing.GLn.degree_minusculeCoset_eq_natCard` identifies this with the number of
  `j`-dimensional subspaces of `kⁿ`.

## References

* G. Shimura, *Introduction to the arithmetic theory of automorphic functions*, Princeton
  University Press (1971), §3.2, Proposition 3.16.
* A. Krieg, *Hecke algebras*, Memoirs of the AMS 435 (1990), Chapter II.
* M. Emerton and T. Gee, *A geometric perspective on the Breuil–Mézard conjecture*, J. Inst.
  Math. Jussieu 13 (2014), §5.3, for the operators `T_w^{(j)}`.

The decomposition of `K η_j K` into left cosets indexed by subspaces of `kⁿ` is adapted from
grh-lean (<https://github.com/lsernau/grh-lean>, Apache 2.0, Copyright 2026 Anthropic PBC),
`Lib/Weil/Unramified/HeckeGL.lean`, declarations `New.basicDoubleCoset_eq`,
`New.heckeGL_eq_sum` and `New.mul_inv_mem_localIntGL_iff`. There the cosets are indexed by the
kernel of the reduction of a representative; here the count is obtained as the index of a
stabilizer.
-/

public section

open Matrix Module IsLocalRing TauCeti
open scoped Pointwise

namespace HeckeRing.GLn

section Subspace

variable (k : Type*) [Field k] (n j : ℕ)

/-- The subspace `S_j` of `kⁿ` of vectors whose first `j` coordinates vanish: the kernel of the
restriction to the coordinates `i < j`. Its stabilizer in `GL_n(k)` is the reduction of
`GL_n(R) ∩ η_j GL_n(R) η_j⁻¹` (`HeckeRing.GLn.map_mem_conjAct_minusculeDiag_iff`). -/
def zeroPrefixSubspace : Submodule k (Fin n → k) :=
  LinearMap.ker (LinearMap.funLeft k k (Subtype.val : {i : Fin n // (i : ℕ) < j} → Fin n))

variable {k n j}

/-- A vector lies in `S_j` exactly when its first `j` coordinates vanish. -/
theorem mem_zeroPrefixSubspace {v : Fin n → k} :
    v ∈ zeroPrefixSubspace k n j ↔ ∀ i : Fin n, (i : ℕ) < j → v i = 0 := by
  simp [zeroPrefixSubspace, funext_iff, LinearMap.funLeft_apply]

/-- The subspace `S_j` has dimension `n - j` (it is `0` for `j ≥ n`). -/
theorem finrank_zeroPrefixSubspace :
    finrank k (zeroPrefixSubspace k n j) = n - j := by
  set f := LinearMap.funLeft k k (Subtype.val : {i : Fin n // (i : ℕ) < j} → Fin n)
  have hf : LinearMap.range f = ⊤ :=
    LinearMap.range_eq_top.mpr
      (LinearMap.funLeft_surjective_of_injective _ _ _ Subtype.val_injective)
  have hcard : Fintype.card {i : Fin n // (i : ℕ) < j} = min n j := by
    rw [Fintype.card_subtype, Fin.card_filter_val_lt]
  have h := f.finrank_range_add_finrank_ker
  rw [hf, finrank_top, finrank_fintype_fun_eq_card, hcard, finrank_fintype_fun_eq_card,
    Fintype.card_fin] at h
  change finrank k (LinearMap.ker f) = n - j
  have := min_le_left n j
  have := min_le_right n j
  rcases le_total n j with h' | h' <;> simp only [min_eq_left, min_eq_right, h'] at h ⊢ <;> omega

/-- `g • S_j ≤ S_j` exactly when the entries `g_{ab}` with `a < j ≤ b` vanish. -/
theorem smul_zeroPrefixSubspace_le_iff (g : GL (Fin n) k) :
    g • zeroPrefixSubspace k n j ≤ zeroPrefixSubspace k n j ↔
      ∀ a b : Fin n, (a : ℕ) < j → j ≤ (b : ℕ) → (g : Matrix (Fin n) (Fin n) k) a b = 0 := by
  constructor
  · intro h a b ha hb
    -- the basis vector `e_b` lies in `S_j`, and `(g e_b)_a = g_{ab}`
    have heb : (Pi.single b 1 : Fin n → k) ∈ zeroPrefixSubspace k n j :=
      mem_zeroPrefixSubspace.mpr fun i hi ↦ Pi.single_eq_of_ne (by omega) _
    have := mem_zeroPrefixSubspace.mp (h (Submodule.smul_mem_pointwise_smul _ g _ heb)) a ha
    rwa [GeneralLinearGroup.smul_vec_eq_mulVec, mulVec_single_one] at this
  · rintro h _ ⟨v, hv, rfl⟩
    refine mem_zeroPrefixSubspace.mpr fun a ha ↦ ?_
    change ((g : Matrix (Fin n) (Fin n) k) *ᵥ v) a = 0
    simp only [mulVec, dotProduct]
    refine Finset.sum_eq_zero fun b _ ↦ ?_
    by_cases hb : (b : ℕ) < j
    · rw [mem_zeroPrefixSubspace.mp hv b hb, mul_zero]
    · rw [h a b ha (by omega), zero_mul]

/-- **The stabilizer of `S_j`** in `GL_n(k)` consists of the matrices whose entries `g_{ab}` with
`a < j ≤ b` vanish. -/
theorem mem_stabilizer_zeroPrefixSubspace_iff (g : GL (Fin n) k) :
    g ∈ MulAction.stabilizer (GL (Fin n) k) (zeroPrefixSubspace k n j) ↔
      ∀ a b : Fin n, (a : ℕ) < j → j ≤ (b : ℕ) → (g : Matrix (Fin n) (Fin n) k) a b = 0 := by
  rw [MulAction.mem_stabilizer_iff, ← smul_zeroPrefixSubspace_le_iff]
  exact ⟨le_of_eq, fun h ↦ Submodule.eq_of_le_of_finrank_eq h
    (GeneralLinearGroup.finrank_smul_submodule g _)⟩

end Subspace

section Minuscule

variable {K : Type*} [Field K]

/-- The diagonal matrix `η_j = diag(π^{(j)}, 1^{(n - j)})`, with `π` in the first `j` entries
and `1` in the others. For a uniformizer `π` its double coset is that of the split-place Hecke
operator `T^{(j)}`. For `j ≥ n` it is the scalar matrix `π`. -/
def minusculeDiag (π : Kˣ) (n j : ℕ) : GL (Fin n) K :=
  diagGL fun i ↦ if (i : ℕ) < j then π else 1

/-- The defining equation of `minusculeDiag`, for modules that import it: the definition is not
exposed. -/
theorem minusculeDiag_def (π : Kˣ) (n j : ℕ) :
    minusculeDiag π n j = diagGL fun i : Fin n ↦ if (i : ℕ) < j then π else 1 :=
  (rfl)

/-- The entries of `η_j⁻¹ M η_j`: conjugation divides the entries `M_{ab}` with `a < j ≤ b` by
`π` and multiplies those with `b < j ≤ a` by `π`. -/
theorem coe_minusculeDiag_inv_mul_mul_apply (π : Kˣ) {n : ℕ} (j : ℕ) (M : GL (Fin n) K)
    (a b : Fin n) :
    (((minusculeDiag π n j)⁻¹ * M * minusculeDiag π n j : GL (Fin n) K) :
        Matrix (Fin n) (Fin n) K) a b =
      ((if (a : ℕ) < j then π else 1 : Kˣ)⁻¹ : K) * (M : Matrix (Fin n) (Fin n) K) a b *
        ((if (b : ℕ) < j then π else 1 : Kˣ) : K) := by
  rw [minusculeDiag, ← map_inv, Units.val_mul, Units.val_mul, diagGL_coe, diagGL_coe,
    mul_diagonal, diagonal_mul, Pi.inv_apply, Units.val_inv_eq_inv_val]

/-- The scalar matrix `π` is `η_j` for every `j ≥ n`. -/
theorem minusculeDiag_of_le (π : Kˣ) {n j : ℕ} (hj : n ≤ j) :
    minusculeDiag π n j = GeneralLinearGroup.scalar (Fin n) π := by
  rw [minusculeDiag, ← diagGL_const]
  congr 1
  funext i
  simp only [show (i : ℕ) < j by omega, ite_true]

/-- `η_0` is the identity. -/
@[simp]
theorem minusculeDiag_zero (π : Kˣ) (n : ℕ) : minusculeDiag π n 0 = 1 := by
  rw [minusculeDiag, ← map_one (diagGL (k := K) (ι := Fin n))]
  simp

end Minuscule

section Cosets

variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  {K : Type*} [Field K] [Algebra R K] {ϖ : R} {π : Kˣ} {n : ℕ}

/-- A uniformizer of `R` mapping to a unit of `K` makes `R → K` injective. -/
private theorem injective_algebraMap (hϖ : Irreducible ϖ) (hπ : algebraMap R K ϖ = π) :
    Function.Injective (algebraMap R K) :=
  TauCeti.IsDiscreteValuationRing.injective_of_map_ne_zero _ hϖ (hπ ▸ π.ne_zero)

/-- **The integral points of `η_j GL_n(R) η_j⁻¹`.** An element `γ` of `GL_n(R)` lies in
`η_j GL_n(R) η_j⁻¹` exactly when its entries `γ_{ab}` with `a < j ≤ b` lie in the maximal
ideal. -/
theorem map_mem_conjAct_minusculeDiag_iff (hϖ : Irreducible ϖ) (hπ : algebraMap R K ϖ = π)
    (j : ℕ) (γ : GL (Fin n) R) :
    GeneralLinearGroup.map (algebraMap R K) γ ∈
        ConjAct.toConjAct (minusculeDiag π n j) • integralGL R K (Fin n) ↔
      ∀ a b : Fin n, (a : ℕ) < j → j ≤ (b : ℕ) →
        (γ : Matrix (Fin n) (Fin n) R) a b ∈ maximalIdeal R := by
  have hπ0 : (π : K) ≠ 0 := π.ne_zero
  rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem, ← ConjAct.toConjAct_inv, ConjAct.smul_def,
    ConjAct.ofConjAct_toConjAct, inv_inv]
  constructor
  · rintro ⟨γ', hγ'⟩ a b ha hb
    have h := congrArg (fun x : GL (Fin n) K ↦ (x : Matrix (Fin n) (Fin n) K) a b) hγ'
    simp only [coe_minusculeDiag_inv_mul_mul_apply, ha, show ¬ (b : ℕ) < j by omega, ite_true,
      ite_false, GeneralLinearGroup.val_map_apply, map_apply, Units.val_one, mul_one] at h
    rw [eq_inv_mul_iff_mul_eq₀ hπ0, ← hπ, ← map_mul] at h
    rw [← injective_algebraMap hϖ hπ h, hϖ.maximalIdeal_eq]
    exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self ϖ)
  · intro h
    -- every entry of `η_j⁻¹ γ η_j` lies in `R`
    have hent (a b : Fin n) : ∃ r : R, algebraMap R K r =
        ((((minusculeDiag π n j)⁻¹ * GeneralLinearGroup.map (algebraMap R K) γ *
          minusculeDiag π n j : GL (Fin n) K)) : Matrix (Fin n) (Fin n) K) a b := by
      rw [coe_minusculeDiag_inv_mul_mul_apply, GeneralLinearGroup.val_map_apply, map_apply]
      by_cases ha : (a : ℕ) < j <;> by_cases hb : (b : ℕ) < j
      · exact ⟨(γ : Matrix (Fin n) (Fin n) R) a b, by simp only [ha, hb, ite_true]; field_simp⟩
      · obtain ⟨x, hx⟩ := Ideal.mem_span_singleton'.mp
          (hϖ.maximalIdeal_eq ▸ h a b ha (by omega))
        refine ⟨x, ?_⟩
        simp only [ha, hb, ite_true, ite_false, Units.val_one, mul_one]
        rw [← hx, map_mul, hπ]
        field_simp
      · exact ⟨(γ : Matrix (Fin n) (Fin n) R) a b * ϖ, by simp [ha, hb, hπ]⟩
      · exact ⟨(γ : Matrix (Fin n) (Fin n) R) a b, by simp [ha, hb]⟩
    choose A hA using hent
    refine mem_integralGL_of_map_eq (injective_algebraMap hϖ hπ) (A := Matrix.of A)
      (u := GeneralLinearGroup.det γ) (by ext a b; exact hA a b) ?_
    rw [Units.val_mul, Units.val_mul, det_mul, det_mul, mul_comm, ← mul_assoc, ← det_mul,
      ← Units.val_mul, mul_inv_cancel, Units.val_one, det_one, one_mul,
      GeneralLinearGroup.val_map_apply, ← RingHom.mapMatrix_apply, ← RingHom.map_det,
      GeneralLinearGroup.val_det_apply]

/-- `GL_n(R) ∩ η_j GL_n(R) η_j⁻¹` is the preimage of the stabilizer of `S_j` under reduction
`GL_n(R) → GL_n(k)`: an entry reduces to zero exactly when it lies in the maximal ideal. -/
theorem map_mem_conjAct_minusculeDiag_iff_mem_stabilizer (hϖ : Irreducible ϖ)
    (hπ : algebraMap R K ϖ = π) (j : ℕ) (γ : GL (Fin n) R) :
    GeneralLinearGroup.map (algebraMap R K) γ ∈
        ConjAct.toConjAct (minusculeDiag π n j) • integralGL R K (Fin n) ↔
      GeneralLinearGroup.map (residue R) γ ∈
        MulAction.stabilizer (GL (Fin n) (ResidueField R))
          (zeroPrefixSubspace (ResidueField R) n j) := by
  rw [map_mem_conjAct_minusculeDiag_iff hϖ hπ, mem_stabilizer_zeroPrefixSubspace_iff]
  simp [residue_eq_zero_iff]

/-- **The number of left cosets in `K η_j K`** is the index in `GL_n(k)` of the stabilizer of
`S_j`: `[K : K ∩ η_j K η_j⁻¹] = [GL_n(k) : Stab(S_j)]`, with `K = GL_n(R)`. -/
theorem relIndex_conjAct_minusculeDiag (hϖ : Irreducible ϖ) (hπ : algebraMap R K ϖ = π)
    (j : ℕ) :
    (ConjAct.toConjAct (minusculeDiag π n j) • integralGL R K (Fin n)).relIndex
        (integralGL R K (Fin n)) =
      (MulAction.stabilizer (GL (Fin n) (ResidueField R))
        (zeroPrefixSubspace (ResidueField R) n j)).index := by
  set φ := GeneralLinearGroup.map (n := Fin n) (algebraMap R K)
  set ρ := GeneralLinearGroup.map (n := Fin n) (residue R)
  set H := ConjAct.toConjAct (minusculeDiag π n j) • integralGL R K (Fin n)
  have hφ : Function.Injective φ :=
    GeneralLinearGroup.map_injective (injective_algebraMap hϖ hπ)
  have hρ : Function.Surjective ρ :=
    GeneralLinearGroup.map_surjective _ residue_surjective
  -- `H ∩ GL_n(R)` is the image of the preimage of the stabilizer
  have hcomap : H.comap φ =
      (MulAction.stabilizer _ (zeroPrefixSubspace (ResidueField R) n j)).comap ρ := by
    ext γ
    exact map_mem_conjAct_minusculeDiag_iff_mem_stabilizer hϖ hπ j γ
  have hmap : H ⊓ φ.range = (H.comap φ).map φ := by rw [Subgroup.map_comap_eq, inf_comm]
  rw [← Subgroup.inf_relIndex_right]
  change (H ⊓ φ.range).relIndex φ.range = _
  rw [hmap, MonoidHom.range_eq_map, Subgroup.relIndex_map_map_of_injective _ _ hφ,
    Subgroup.relIndex_top_right, hcomap, Subgroup.index_comap_of_surjective _ hρ]

variable (R) in
/-- The double coset `GL_n(R) η_j GL_n(R)` of `η_j = diag(π^{(j)}, 1^{(n - j)})`, as a double
coset of the local Hecke pair `(GL_n(K), GL_n(R))`. For a uniformizer `π` it indexes the
split-place Hecke operator `T^{(j)}`. -/
def minusculeCoset (π : Kˣ) (n j : ℕ) :
    HeckeCoset (⊤ : Submonoid (GL (Fin n) K)) (integralGL R K (Fin n)) (integralGL R K (Fin n)) :=
  HeckeCoset.mk _ _ ⟨minusculeDiag π n j, Submonoid.mem_top _⟩

omit [IsDomain R] [IsDiscreteValuationRing R] in
/-- The defining equation of `minusculeCoset`, for modules that import it: the definition is not
exposed. -/
theorem minusculeCoset_def (π : Kˣ) (n j : ℕ) :
    minusculeCoset R π n j = HeckeCoset.mk _ _ ⟨minusculeDiag π n j, Submonoid.mem_top _⟩ :=
  (rfl)

/-- **The coset decomposition of `K η_j K`.** For `j ≤ n` the double coset
`GL_n(R) η_j GL_n(R)` is the union of `[n, j]_q` left cosets `g GL_n(R)`, where `q` is the size
of the residue field. -/
theorem degree_minusculeCoset [Finite (ResidueField R)] (hϖ : Irreducible ϖ)
    (hπ : algebraMap R K ϖ = π) {j : ℕ} (hj : j ≤ n) :
    (minusculeCoset R π n j).degree = gaussianBinomial (Nat.card (ResidueField R)) n j := by
  have := Fintype.ofFinite (ResidueField R)
  rw [minusculeCoset, HeckeCoset.degree_mk, relIndex_conjAct_minusculeDiag hϖ hπ,
    GeneralLinearGroup.index_stabilizer_submodule_eq_gaussianBinomial,
    finrank_zeroPrefixSubspace, Fintype.card_fin, gaussianBinomial_symm _ hj,
    Nat.card_eq_fintype_card]

/-- **`K η_j K` is the union of as many left cosets as there are subspaces of `kⁿ` of codimension
`j`**, where `k` is the residue field: the coset `g GL_n(R)` corresponds to the image of the
lattice `g Rⁿ` in `kⁿ = Rⁿ / ϖ Rⁿ`. There are as many of them as `j`-dimensional subspaces; for a
finite residue field `degree_minusculeCoset` gives their number. -/
theorem degree_minusculeCoset_eq_natCard (hϖ : Irreducible ϖ) (hπ : algebraMap R K ϖ = π)
    (j : ℕ) :
    (minusculeCoset R π n j).degree =
      Nat.card {W : Submodule (ResidueField R) (Fin n → ResidueField R) //
        finrank (ResidueField R) W = n - j} := by
  rw [minusculeCoset, HeckeCoset.degree_mk, relIndex_conjAct_minusculeDiag hϖ hπ,
    GeneralLinearGroup.index_stabilizer_submodule_eq_natCard, finrank_zeroPrefixSubspace]

end Cosets

end HeckeRing.GLn
