/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.DirectSum.Module
public import Mathlib.Algebra.Polynomial.Splits
public import Mathlib.FieldTheory.Separable
public import Mathlib.LinearAlgebra.Charpoly.Basic
public import Mathlib.LinearAlgebra.Dimension.Free
public import Mathlib.LinearAlgebra.Eigenspace.Basic
public import Mathlib.LinearAlgebra.Eigenspace.Minpoly
public import Mathlib.RingTheory.Polynomial.Basic
public import Mathlib.RingTheory.Polynomial.Cyclotomic.Basic
import Mathlib.LinearAlgebra.Charpoly.BaseChange
import Mathlib.RingTheory.Localization.FractionRing
import TauCeti.LinearAlgebra.Eigenspace.DiagonalBasis

/-!
# Diagonalization by a split separable annihilating polynomial

An endomorphism `f` of a vector space over a field `K` that is annihilated by a separable
polynomial splitting over `K` is diagonalizable over `K` itself: the kernel of
`∏_{a ∈ s} (f - a)` is the sum of the eigenspaces `ker (f - a)`, by induction on `s`, because the
factors `X - a` are pairwise coprime. Mathlib states diagonalizability of semisimple
endomorphisms only over an algebraically closed field
(`Module.End.IsSemisimple.iSup_eigenspace_eq_top`); the statement here needs only the roots of
one annihilating polynomial. The main case is `f ^ n = 1` with `n` invertible in `K` and `K`
containing a primitive `n`-th root of unity.

In finite dimension the eigenspaces then give a basis of eigenvectors. Over a domain `O`
containing a primitive `n`-th root of unity, an endomorphism `f` of a finite free module with
`f ^ n = 1` therefore has split characteristic polynomial: over the fraction field `f` is
diagonal with eigenvalues `n`-th roots of unity, which are powers of the primitive root of `O`.

## Main results

* `Module.End.ker_aeval_prod_X_sub_C_le`: the kernel of `∏_{a ∈ s} (f - a)` lies in the sum of
  the eigenspaces of `f` at the points of `s`.
* `Module.End.iSup_eigenspace_eq_top_of_aeval_eq_zero`: an endomorphism annihilated by a split
  separable polynomial has spanning eigenspaces.
* `Module.End.iSup_eigenspace_eq_top_of_pow_eq_one`: so does an endomorphism `f` with
  `f ^ n = 1`, when `K` contains a primitive `n`-th root of unity.
* `Module.End.exists_basis_apply_eq_smul`: in finite dimension, spanning eigenspaces give a basis
  of eigenvectors; `Module.End.exists_basis_apply_eq_smul_of_pow_eq_one` for `f ^ n = 1`.
* `Module.End.splits_charpoly_of_pow_eq_one`: an endomorphism `f` of a finite free module over a
  domain containing a primitive `n`-th root of unity, with `f ^ n = 1`, has split characteristic
  polynomial.
-/

public section

open Polynomial Module

namespace Module.End

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

/-- The kernel of `∏_{a ∈ s} (f - a)` lies in the sum of the eigenspaces of `f` at the points of
`s`: the linear factors are pairwise coprime, so the kernel of the product is the sum of the
kernels. -/
theorem ker_aeval_prod_X_sub_C_le (f : End K V) (s : Finset K) :
    LinearMap.ker (aeval f (∏ a ∈ s, (X - C a))) ≤ ⨆ a ∈ s, f.eigenspace a := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [LinearMap.ker_eq_bot, Function.injective_id]
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, ← sup_ker_aeval_eq_ker_aeval_mul_of_coprime]
    · refine sup_le ?_ (ih.trans (biSup_mono fun b hb ↦ Finset.mem_insert_of_mem hb))
      refine le_trans (le_of_eq ?_) (le_biSup _ (Finset.mem_insert_self a s))
      rw [eigenspace_def, map_sub, aeval_X, aeval_C, Algebra.algebraMap_eq_smul_one]
    · exact IsCoprime.prod_right fun b hb ↦
        isCoprime_X_sub_C_of_isUnit_sub (sub_ne_zero.2 fun h ↦ ha (by rwa [h])).isUnit

/-- **Diagonalization over the field of definition.** An endomorphism annihilated by a separable
polynomial that splits over `K` has eigenspaces spanning the whole space. -/
theorem iSup_eigenspace_eq_top_of_aeval_eq_zero {f : End K V} {P : K[X]} (hP : P.Splits)
    (hsep : P.Separable) (hf : aeval f P = 0) : ⨆ μ : K, f.eigenspace μ = ⊤ := by
  classical
  have h0 : P ≠ 0 := hsep.ne_zero
  have hprod : P = C P.leadingCoeff * ∏ a ∈ P.roots.toFinset, (X - C a) := by
    conv_lhs => rw [hP.eq_prod_roots]
    rw [Finset.prod_eq_multiset_prod, Multiset.toFinset_val,
      Multiset.dedup_eq_self.2 (Polynomial.nodup_roots hsep)]
  have hker : LinearMap.ker (aeval f (∏ a ∈ P.roots.toFinset, (X - C a))) = ⊤ := by
    rw [LinearMap.ker_eq_top]
    have hl : P.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.2 h0
    have := hf
    rw [hprod, map_mul, aeval_C, Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul] at this
    exact (smul_eq_zero.1 this).resolve_left hl
  refine eq_top_iff.2 ((hker.symm.le.trans (ker_aeval_prod_X_sub_C_le f _)).trans ?_)
  exact iSup₂_le fun a _ ↦ le_iSup f.eigenspace a

/-- An endomorphism `f` with `f ^ n = 1`, over a field containing a primitive `n`-th root of
unity, has eigenspaces spanning the whole space: `X ^ n - 1` splits into distinct linear
factors. -/
theorem iSup_eigenspace_eq_top_of_pow_eq_one {f : End K V} {n : ℕ} [NeZero n] {ζ : K}
    (hζ : IsPrimitiveRoot ζ n) (hf : f ^ n = 1) : ⨆ μ : K, f.eigenspace μ = ⊤ := by
  have := hζ.neZero'
  refine iSup_eigenspace_eq_top_of_aeval_eq_zero (X_pow_sub_one_splits hζ)
    (separable_X_pow_sub_C 1 (NeZero.ne _) one_ne_zero) ?_
  simp [hf]

/-- **A basis of eigenvectors.** In finite dimension, if the eigenspaces of `f` span the space,
then `f` is diagonal in some basis indexed by `Fin (finrank K V)`. -/
theorem exists_basis_apply_eq_smul [FiniteDimensional K V] {f : End K V}
    (hf : ⨆ μ : K, f.eigenspace μ = ⊤) :
    ∃ (b : Basis (Fin (finrank K V)) K V) (d : Fin (finrank K V) → K),
      ∀ i, f (b i) = d i • b i := by
  classical
  have hint : DirectSum.IsInternal f.eigenspace :=
    DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top f.eigenspaces_iSupIndep hf
  let b₀ := hint.collectedBasis fun μ ↦ Basis.ofVectorSpace K (f.eigenspace μ)
  let e := b₀.indexEquiv (Module.finBasis K V)
  refine ⟨b₀.reindex e, fun i ↦ (e.symm i).1, fun i ↦ ?_⟩
  rw [Basis.reindex_apply]
  exact mem_eigenspace_iff.1 (hint.collectedBasis_mem _ (e.symm i))

/-- An endomorphism `f` with `f ^ n = 1` of a finite-dimensional space over a field containing a
primitive `n`-th root of unity is diagonal in some basis, with eigenvalues `n`-th roots of
unity. -/
theorem exists_basis_apply_eq_smul_of_pow_eq_one [FiniteDimensional K V] {f : End K V} {n : ℕ}
    [NeZero n] {ζ : K} (hζ : IsPrimitiveRoot ζ n) (hf : f ^ n = 1) :
    ∃ (b : Basis (Fin (finrank K V)) K V) (d : Fin (finrank K V) → K),
      (∀ i, f (b i) = d i • b i) ∧ ∀ i, d i ^ n = 1 := by
  obtain ⟨b, d, hb⟩ := exists_basis_apply_eq_smul (iSup_eigenspace_eq_top_of_pow_eq_one hζ hf)
  refine ⟨b, d, hb, fun i ↦ ?_⟩
  have h := aeval_apply_of_mem_apply_eq_smul (p := X ^ n) (hb i)
  rw [map_pow, aeval_X, hf, one_apply_eq_self, eval_pow, eval_X] at h
  exact smul_left_injective K (b.ne_zero i) (h.symm.trans (one_smul K _).symm)

section Domain

variable {O M : Type*} [CommRing O] [IsDomain O] [AddCommGroup M] [Module O M] [Module.Free O M]
  [Module.Finite O M]

/-- An endomorphism `f` of a finite free module over a domain containing a primitive `n`-th root
of unity, with `f ^ n = 1`, has split characteristic polynomial: over the fraction field `f` is
diagonal with eigenvalues `n`-th roots of unity, which are powers of the primitive root. -/
theorem splits_charpoly_of_pow_eq_one {f : End O M} {n : ℕ} [NeZero n] {ζ : O}
    (hζ : IsPrimitiveRoot ζ n) (hf : f ^ n = 1) : f.charpoly.Splits := by
  let K := FractionRing O
  have hinj : Function.Injective (algebraMap O K) := IsFractionRing.injective O K
  have hζK : IsPrimitiveRoot (algebraMap O K ζ) n := hζ.map_of_injective hinj
  have hfK : f.baseChange K ^ n = 1 := by
    rw [← LinearMap.baseChange_pow, hf, Module.End.one_eq_id, LinearMap.baseChange_id,
      Module.End.one_eq_id]
  obtain ⟨b, d, hb, hd⟩ := exists_basis_apply_eq_smul_of_pow_eq_one hζK hfK
  have hmap : f.charpoly.map (algebraMap O K) = ∏ i, (X - C (d i)) := by
    rw [← LinearMap.charpoly_baseChange, LinearMap.charpoly_eq_prod_of_apply_eq_smul b hb]
  refine Splits.of_splits_map_of_injective hinj ?_ fun a ha ↦ ?_
  · rw [hmap]
    exact Splits.prod fun i _ ↦ Splits.X_sub_C _
  · rw [← LinearMap.charpoly_baseChange, LinearMap.roots_charpoly_of_apply_eq_smul b hb,
      Multiset.mem_map] at ha
    obtain ⟨i, -, rfl⟩ := ha
    obtain ⟨j, -, hj⟩ := hζK.eq_pow_of_pow_eq_one (hd i)
    exact ⟨ζ ^ j, by rw [map_pow, hj]⟩

end Domain

end Module.End
