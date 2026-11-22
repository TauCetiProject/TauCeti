/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.RootSystem.Finite.CanonicalBilinear
public import TauCeti.LinearAlgebra.Matrix.Cartan.Realization.Basic
public import TauCeti.LinearAlgebra.Matrix.Cartan.Symmetrizable
public import TauCeti.LinearAlgebra.RootSystem.AffineCartanMatrix

/-!
# The minimal realization and symmetrizability of an untwisted affine Cartan matrix

For a base `b` of a finite crystallographic root pairing `P` over a characteristic-zero ring with
highest root `θ = b.highestRoot`, the untwisted affine Cartan matrix `b.affineCartanMatrix` has
entries `⟨αₖ, αₗ^∨⟩` with `α₀ = -θ` at `none`. Since `TauCeti.SymmetrizableDatum` and
`TauCeti.CartanRealization` use the row convention `Aₖₗ = αₗ(hₖ)`, this file equips
`b.affineCartanMatrixᵀ` with:

* `RootPairing.Base.affineCartanSymmetrizableDatum`: symmetrizability by root lengths
  `(P.posRootForm ℤ).rootLength (b.affineSimpleRootIndex k)`.
* `RootPairing.Base.affineRealization`: the standard minimal realization on `N × K × K`
  (`𝔥 ⊕ K c ⊕ K d`) with coroots `affineCoroot` and roots `affineRoot`, central element
  `affineCentralElement` (`= (0, 1, 0)`), and null root `affineNullRoot` (`(h, a, t) ↦ t`).

When `P` is a root system, `cartanCenter_affineRealization` shows the Cartan center is `K ∙ c`, so
`b.affineRealization` is minimal (`isMinimal_affineRealization`).

## References

* V. G. Kac, *Infinite-Dimensional Lie Algebras*, 3rd ed., §6.2.
-/

public section

open Matrix

namespace RootPairing.Base

section Symmetrizable

variable {ι R M N : Type*} [CommRing R] [IsDomain R] [CharZero R] [AddCommGroup M] [Module R M]
  [AddCommGroup N] [Module R N] {P : RootPairing ι R M N} [Finite ι] [Nonempty ι]
  [P.IsCrystallographic] (b : P.Base)

/-- **The untwisted affine Cartan matrix is symmetrizable.** Packaged in the row convention
`cartan k l = αₗ(hₖ)` of `TauCeti.SymmetrizableDatum`, the matrix is `b.affineCartanMatrixᵀ` and
the symmetrizer is given by the positive integer root lengths of Mathlib's canonical positive
invariant form `P.posRootForm ℤ`. -/
noncomputable def affineCartanSymmetrizableDatum :
    TauCeti.SymmetrizableDatum (Option b.support) :=
  letI : Fintype ι := Fintype.ofFinite ι
  { cartan := b.affineCartanMatrixᵀ
    diag k := by simp
    offDiag_nonpos k l hkl := b.affineCartanMatrix_le_zero_of_ne hkl.symm
    zero_comm k l := b.affineCartanMatrix_apply_eq_zero_iff_symm
    symmetrizer k := ((P.posRootForm ℤ).rootLength (b.affineSimpleRootIndex k)).toNat
    symmetrizer_pos k := by
      have hpos := (P.posRootForm ℤ).rootLength_pos (b.affineSimpleRootIndex k); omega
    symmetrizes k l := by
      have hk := ((P.posRootForm ℤ).rootLength_pos (b.affineSimpleRootIndex k)).le
      have hl := ((P.posRootForm ℤ).rootLength_pos (b.affineSimpleRootIndex l)).le
      rw [Int.toNat_of_nonneg hk, Int.toNat_of_nonneg hl, Matrix.transpose_apply,
        Matrix.transpose_apply, b.affineCartanMatrix_apply, b.affineCartanMatrix_apply, mul_comm,
        mul_comm ((P.posRootForm ℤ).rootLength _)]
      exact (P.posRootForm ℤ).pairingIn_mul_eq_pairingIn_mul_swap _ _ }

/-- The underlying generalized Cartan matrix of `affineCartanSymmetrizableDatum` is
`b.affineCartanMatrixᵀ`. -/
@[simp]
theorem affineCartanSymmetrizableDatum_cartan :
    b.affineCartanSymmetrizableDatum.cartan = b.affineCartanMatrixᵀ := (rfl)

/-- The symmetrizer of `affineCartanSymmetrizableDatum` is the root length of the corresponding
affine simple root under `P.posRootForm ℤ`. -/
@[simp]
theorem affineCartanSymmetrizableDatum_symmetrizer (k : Option b.support) :
    letI : Fintype ι := Fintype.ofFinite ι
    b.affineCartanSymmetrizableDatum.symmetrizer k =
      ((P.posRootForm ℤ).rootLength (b.affineSimpleRootIndex k)).toNat := (rfl)

end Symmetrizable

section CorootsAndRoots

variable {ι R M N : Type*} [CommRing R] [CharZero R] [AddCommGroup M] [Module R M]
  [AddCommGroup N] [Module R N] {P : RootPairing ι R M N} [Finite ι] [Nonempty ι] (b : P.Base)

/-- The simple coroots in the standard affine realization `N × R × R`: `hᵢ = (αᵢ^∨, 0, 0)` for a
finite simple root `i` and `h₀ = (-θ^∨, 1, 0)` at the affine node. -/
noncomputable def affineCoroot : Option b.support → N × R × R
  | none => (-P.coroot b.highestRoot, 1, 0)
  | some i => (P.coroot i, 0, 0)

/-- The simple roots in the standard affine realization `N × R × R`: `αᵢ(h, a, t) = ⟨αᵢ, h⟩` for a
finite simple root `i` and `α₀(h, a, t) = t - ⟨θ, h⟩` at the affine node. -/
noncomputable def affineRoot : Option b.support → Module.Dual R (N × R × R)
  | none => LinearMap.snd R R R ∘ₗ LinearMap.snd R N (R × R) -
      P.toLinearMap (P.root b.highestRoot) ∘ₗ LinearMap.fst R N (R × R)
  | some i => P.toLinearMap (P.root i) ∘ₗ LinearMap.fst R N (R × R)

end CorootsAndRoots

section Realization

variable {ι K M N : Type*} [Field K] [CharZero K] [AddCommGroup M] [Module K M] [AddCommGroup N]
  [Module K N] {P : RootPairing ι K M N} [Finite ι] [Nonempty ι] (b : P.Base) [P.IsCrystallographic]

/-- **The standard realization of the untwisted affine Cartan matrix** `b.affineCartanMatrixᵀ` on
`N × K × K`, representing `𝔥 ⊕ K c ⊕ K d`. -/
noncomputable def affineRealization :
    TauCeti.CartanRealization (b.affineCartanMatrixᵀ.map (Int.cast : ℤ → K)) (N × K × K) where
  coroot := b.affineCoroot
  root := b.affineRoot
  coroot_linearIndependent := by
    rw [linearIndependent_option]
    refine ⟨b.linearIndepOn_coroot.map' (LinearMap.inl K N (K × K))
      (LinearMap.ker_eq_bot.mpr fun _ _ h ↦ (Prod.ext_iff.mp h).left), fun hmem ↦ ?_⟩
    let πc : N × K × K →ₗ[K] K := LinearMap.fst K K K ∘ₗ LinearMap.snd K N (K × K)
    have hker : Submodule.span K (Set.range (b.affineCoroot ∘ some)) ≤ LinearMap.ker πc :=
      Submodule.span_le.mpr (by rintro _ ⟨i, rfl⟩; simp [πc, affineCoroot])
    simpa [πc, affineCoroot] using LinearMap.mem_ker.mp (hker hmem)
  root_linearIndependent := by
    rw [linearIndependent_option]
    refine ⟨?_, fun hmem ↦ ?_⟩
    · let emb : M →ₗ[K] Module.Dual K (N × K × K) :=
        (LinearMap.fst K N (K × K)).dualMap.comp P.toPerfPair.toLinearMap
      exact b.linearIndepOn_root.map' emb (LinearMap.ker_eq_bot.mpr fun _ _ hxy ↦
        P.toPerfPair.injective <| by ext h; simpa [emb] using LinearMap.congr_fun hxy (h, 0, 0))
    · let ev : Module.Dual K (N × K × K) →ₗ[K] K := Module.Dual.eval K (N × K × K) ((0 : N), 0, 1)
      have hker : Submodule.span K (Set.range (b.affineRoot ∘ some)) ≤ LinearMap.ker ev :=
        Submodule.span_le.mpr (by rintro _ ⟨i, rfl⟩; simp [ev, affineRoot])
      simpa [ev, affineRoot] using LinearMap.mem_ker.mp (hker hmem)
  root_coroot k l := by
    rcases k with _ | i <;> rcases l with _ | j <;>
      simp [affineCoroot, affineRoot, RootPairing.root_coroot_eq_pairing,
        ← P.algebraMap_pairingIn ℤ]

@[simp]
theorem affineRealization_coroot_none :
    b.affineRealization.coroot none = (-P.coroot b.highestRoot, 1, 0) := (rfl)

@[simp]
theorem affineRealization_coroot_some (i : b.support) :
    b.affineRealization.coroot (some i) = (P.coroot i, 0, 0) := (rfl)

@[simp]
theorem affineRealization_root_none (h : N) (a t : K) :
    b.affineRealization.root none (h, a, t) = t - P.toLinearMap (P.root b.highestRoot) h := (rfl)

@[simp]
theorem affineRealization_root_some (i : b.support) (h : N) (a t : K) :
    b.affineRealization.root (some i) (h, a, t) = P.toLinearMap (P.root i) h := (rfl)

/-- The canonical central element `c = ∑ₖ aₖ^∨ hₖ` of `b.affineRealization`. -/
noncomputable def affineCentralElement : N × K × K :=
  ∑ k : Option b.support, (b.affineComarks k : K) • b.affineRealization.coroot k

/-- The defining sum formula `c = ∑ₖ aₖ^∨ hₖ` for `b.affineCentralElement`. -/
theorem affineCentralElement_def :
    b.affineCentralElement =
      ∑ k : Option b.support, (b.affineComarks k : K) • b.affineRealization.coroot k := (rfl)

/-- **The canonical central element evaluates to `(0, 1, 0)`** in `N × K × K`. -/
@[simp]
theorem affineCentralElement_eq : b.affineCentralElement = (0, 1, 0) := by
  unfold affineCentralElement; rw [Fintype.sum_option]
  refine Prod.ext ?_ (Prod.ext (by simp [Prod.snd_sum]) (by simp [Prod.snd_sum]))
  simp only [Prod.fst_add, Prod.smul_fst, Prod.fst_sum, affineRealization_coroot_none,
    affineRealization_coroot_some, affineComarks_none, Int.cast_one, one_smul,
    Int.cast_smul_eq_zsmul, ← b.coroot_highestRoot_eq_sum_affineComarks, neg_add_cancel]

/-- The central element belongs to the coroot span of `b.affineRealization`. -/
theorem affineCentralElement_mem_corootSpan :
    b.affineCentralElement ∈ b.affineRealization.corootSpan :=
  Submodule.sum_mem _ fun k _ ↦ Submodule.smul_mem _ _ (b.affineRealization.coroot_mem_corootSpan k)

/-- The null root `δ = ∑ₖ aₖ αₖ` of `b.affineRealization`. -/
noncomputable def affineNullRoot : Module.Dual K (N × K × K) :=
  ∑ k : Option b.support, (b.affineMarks k : K) • b.affineRealization.root k

/-- The defining sum formula `δ = ∑ₖ aₖ αₖ` for `b.affineNullRoot`. -/
theorem affineNullRoot_def :
    b.affineNullRoot =
      ∑ k : Option b.support, (b.affineMarks k : K) • b.affineRealization.root k := (rfl)

/-- **The null root evaluates to the degree coordinate**: `δ (h, a, t) = t`. -/
@[simp]
theorem affineNullRoot_apply (h : N) (a t : K) : b.affineNullRoot (h, a, t) = t := by
  unfold affineNullRoot; rw [Fintype.sum_option]
  simp only [LinearMap.add_apply, LinearMap.smul_apply, LinearMap.coe_sum, Finset.sum_apply,
    affineMarks_none, Int.cast_one, one_smul, affineRealization_root_none,
    affineRealization_root_some, smul_eq_mul]
  have hθ : P.toLinearMap (P.root b.highestRoot) h =
      ∑ i : b.support, (b.affineMarks (some i) : K) * P.toLinearMap (P.root i) h := by
    rw [b.root_highestRoot_eq_sum_affineMarks, map_sum, LinearMap.coe_sum, Finset.sum_apply]
    exact Finset.sum_congr rfl fun i _ ↦ by rw [map_zsmul, LinearMap.smul_apply, zsmul_eq_mul]
  rw [hθ]; ring

/-- **The Cartan center of the standard affine realization is the line spanned by `c`**,
provided `P` is a root system. -/
theorem cartanCenter_affineRealization [P.IsRootSystem] :
    b.affineRealization.cartanCenter = K ∙ b.affineCentralElement := by
  ext ⟨h, a, t⟩
  rw [TauCeti.CartanRealization.mem_cartanCenter_iff, Submodule.mem_span_singleton,
    b.affineCentralElement_eq]
  refine ⟨fun hzero ↦ ?_, fun ⟨c, hc⟩ k ↦ ?_⟩
  · have hh : h = 0 := P.flip.toPerfPair.injective <| by
      rw [map_zero]; exact b.toWeightBasis.ext fun i ↦ by simpa using hzero (some i)
    exact ⟨a, by simp [hh, show t = 0 from by simpa [hh] using hzero none]⟩
  · have hfst : h = 0 := by simpa using (congrArg Prod.fst hc).symm
    have ht : t = 0 := by simpa using (congrArg (fun v ↦ v.snd.snd) hc).symm
    rcases k with _ | i <;> simp [hfst, ht]

/-- **The standard affine realization on `N × K × K` is minimal** for any finite crystallographic
root system over a field of characteristic zero. -/
theorem isMinimal_affineRealization [P.IsRootSystem] :
    b.affineRealization.IsMinimal := by
  rw [TauCeti.CartanRealization.isMinimal_iff_cartanCenter_le_corootSpan,
    b.cartanCenter_affineRealization, Submodule.span_singleton_le_iff_mem]
  exact b.affineCentralElement_mem_corootSpan

end Realization

end RootPairing.Base
