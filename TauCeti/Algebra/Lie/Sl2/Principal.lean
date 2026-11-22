/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.AdjointAction.Regular
public import TauCeti.Algebra.Lie.Sl2.WeightedDiagram.Finite
public import TauCeti.Algebra.Lie.Weights.Sl2System
public import TauCeti.LinearAlgebra.RootSystem.Weyl.Vector
import Mathlib.Algebra.CharZero.Infinite
import TauCeti.Algebra.Lie.Killing.Regular
import TauCeti.Algebra.Lie.Presentation.Serre.Killing
import TauCeti.Algebra.Lie.Sl2.Centralizer
import TauCeti.Algebra.Lie.Weights.Rank

/-!
# The principal `sl₂` triple

Let `L` be a finite-dimensional Lie algebra with non-degenerate Killing form over a field `K` of
characteristic zero, let `H` be a splitting Cartan subalgebra and let `b` be a base of its root
system, with simple roots `αᵢ` and simple coroots `αᵢ^∨`. The element

`2ρ^∨ = ∑_{α > 0} α^∨ = TauCeti.twoWeylVector (rootSystem H).flip b.flip`

of `H` is the sum of the positive coroots, that is twice the Weyl vector of the dual root system.
Every simple root takes the value `2` at it, and more generally every root `α` takes the value
`2 ht(α)` (`TauCeti.root_apply_twoWeylVector_flip_eq_two_mul_height`).

**The principal triple.** Write `2ρ^∨ = ∑ᵢ cᵢ αᵢ^∨` in the basis of simple coroots. If
`eᵢ ∈ L_{αᵢ}` and `fᵢ ∈ L_{-αᵢ}` satisfy `[eᵢ, fᵢ] = cᵢ αᵢ^∨` for every simple root, then
`(2ρ^∨, ∑ᵢ eᵢ, ∑ᵢ fᵢ)` is an `sl₂` triple (`TauCeti.isSl2Triple_twoWeylVector_flip_sum`). The
relations `[2ρ^∨, eᵢ] = 2 eᵢ` and `[2ρ^∨, fᵢ] = -2 fᵢ` hold because simple roots take the value `2`,
and `[∑ eᵢ, ∑ fⱼ] = ∑ cᵢ αᵢ^∨ = 2ρ^∨` because a difference `αᵢ - αⱼ` of distinct simple roots is
neither zero nor a root, so `[eᵢ, fⱼ] = 0` for `i ≠ j`. Since each root space is a line, every
sum of nonzero simple root vectors is the nilpositive element of an `sl₂` triple with neutral
element `2ρ^∨`, whose nilnegative element lies in the negative nilradical
(`TauCeti.exists_mem_negativeNilradical_isSl2Triple_twoWeylVector_flip`), and dually every sum of
nonzero negative simple root vectors is the nilnegative element of such a triple
(`TauCeti.exists_mem_positiveNilradical_isSl2Triple_twoWeylVector_flip`). These are the principal
`sl₂` triples; the second form, with the nilnegative element `∑ᵢ fᵢ` prescribed, is the
normalization used for opers. Half of the neutral element, `ρ^∨`, acts on the root space of `α`
by the height of `α`, which is the principal grading.

**Weighted Dynkin diagram.** The neutral element `2ρ^∨` is a dominant neutral element for `b`,
and its weighted Dynkin diagram is the constant labelling `2`; conversely this labelling is that of
`2ρ^∨` only (`RootPairing.Base.weightedDynkinDiagram_eq_two_iff`).

**Centralizer dimension.** No root vanishes at `2ρ^∨`, so the centralizer of `2ρ^∨` is `H`
(`LieSubalgebra.ker_ad_eq_toSubmodule_of_forall_root_apply_ne_zero`), and the eigenvalues of
`ad (2ρ^∨)` are even integers (`TauCeti.eigenspace_ad_twoWeylVector_flip_eq_bot`). For any triple
`(2ρ^∨, e, f)` the dimension of the kernel of `ad e` is the number of irreducible summands of `L` as
a module over the triple, `dim L(0) + dim L(1)`, which is therefore `dim H`
(`IsSl2Triple.finrank_ker_ad_e_eq_finrank_cartan`): the principal nilpotent element has a
centralizer whose dimension is the rank of `L`, and `[L, e]` has dimension `dim L - dim H`
(`IsSl2Triple.finrank_range_ad_e_add_finrank_cartan`).

**Regularity.** Since `dim H` is the rank of `L`, the least dimension of a centralizer
(`LieAlgebra.isCentralizerRegular_iff_finrank_ker_ad_eq_rank`), the nilpositive element of a
principal triple is regular in the sense of `LieAlgebra.IsCentralizerRegular`
(`IsSl2Triple.isCentralizerRegular_e`). Conversely, let `(h, e, f)` be any `sl₂` triple with `h`
a dominant neutral element. The centralizer of `e` has dimension `dim L(0) + dim L(1)`, where
`L(n)` is the `n`-eigenspace of `ad h`, and `H ≤ L(0)`. If a simple root took the value `0` or `1`
at `h`, its root space would make `L(0) ⊔ L(1)` larger than `H`. So `e` is regular exactly when
every simple root takes the value `2` at `h`, that is, when `h = 2ρ^∨`
(`IsSl2Triple.isCentralizerRegular_e_iff`): the regular nilpotent elements are the principal ones.

## Main results

* `TauCeti.root_apply_twoWeylVector_flip`: every simple root takes the value `2` at `2ρ^∨`.
* `TauCeti.root_apply_twoWeylVector_flip_eq_two_mul_height`: a root takes the value twice its
  height at `2ρ^∨`.
* `TauCeti.root_apply_twoWeylVector_flip_ne_zero` and
  `TauCeti.eigenspace_ad_twoWeylVector_flip_eq_bot`: no root vanishes at `2ρ^∨`, and the
  eigenvalues of `ad (2ρ^∨)` are even integers.
* `TauCeti.isSl2Triple_twoWeylVector_flip_sum`: the principal `sl₂` triple built from simple root
  vectors.
* `TauCeti.exists_mem_negativeNilradical_isSl2Triple_twoWeylVector_flip` and
  `TauCeti.exists_mem_positiveNilradical_isSl2Triple_twoWeylVector_flip`: a sum of nonzero
  positive, respectively negative, simple root vectors is the nilpositive, respectively
  nilnegative, element of a principal `sl₂` triple.
* `RootPairing.Base.twoWeylVector_flip_mem_dominantNeutralElements` and
  `RootPairing.Base.weightedDynkinDiagram_eq_two_iff`: the weighted Dynkin diagram of the principal
  triple is the constant labelling `2`, and it determines the neutral element `2ρ^∨`.
* `IsSl2Triple.finrank_ker_ad_e_eq_finrank_cartan` and
  `IsSl2Triple.finrank_range_ad_e_add_finrank_cartan`: the nilpositive element of a triple with
  neutral element `2ρ^∨` has a centralizer of dimension `dim H`, and `[L, e]` has dimension
  `dim L - dim H`.
* `IsSl2Triple.isCentralizerRegular_e` and `IsSl2Triple.isCentralizerRegular_e_iff`: the
  nilpositive element of a triple with dominant neutral element `h` is regular exactly when
  `h = 2ρ^∨`.

## References

* B. Kostant, *The principal three-dimensional subgroup and the Betti numbers of a complex simple
  Lie group*, Amer. J. Math. **81** (1959), 973–1032, §5.
* D. H. Collingwood and W. M. McGovern, *Nilpotent Orbits in Semisimple Lie Algebras*, Van
  Nostrand Reinhold, 1993, §3.2 and §4.1.
* N. Bourbaki, *Lie Groups and Lie Algebras*, Chapters 7–9, Chapter VIII, §11, no. 4.
-/

public section

open LieAlgebra LieModule LieAlgebra.IsKilling Module

variable {K L : Type*} [Field K] [CharZero K] [LieRing L] [LieAlgebra K L]
  [FiniteDimensional K L] [IsKilling K L]
  {H : LieSubalgebra K L} [H.IsCartanSubalgebra] [IsTriangularizable K H L]

namespace TauCeti

variable (b : (rootSystem H).Base)

/-! ### The values of the roots at `2ρ^∨` -/

/-- **Every simple root takes the value `2` at `2ρ^∨`**, the sum of the positive coroots. -/
theorem root_apply_twoWeylVector_flip {i : H.root} (hi : i ∈ b.support) :
    (i : Weight K H L) (twoWeylVector (rootSystem H).flip b.flip) = 2 := by
  simpa using coroot'_twoWeylVector (rootSystem H).flip b.flip (i := i) (by simpa using hi)

/-- **A root takes the value twice its height at `2ρ^∨`.** -/
theorem root_apply_twoWeylVector_flip_eq_two_mul_height (i : H.root) :
    (i : Weight K H L) (twoWeylVector (rootSystem H).flip b.flip) = 2 * (b.height i : K) := by
  -- the base `b.flip.flip` of `(rootSystem H).flip.flip` is `b` itself, by structure eta
  have h := coroot'_twoWeylVector_eq_two_mul_height_flip (rootSystem H).flip b.flip i
  simp only [LinearMap.flip_apply, RootPairing.flip_toLinearMap, RootPairing.flip_coroot,
    rootSystem_root_apply, rootSystem_toLinearMap_apply, Weight.toLinear_apply,
    RootPairing.flip_flip] at h
  exact h

/-- **No root vanishes at `2ρ^∨`.** -/
theorem root_apply_twoWeylVector_flip_ne_zero (i : H.root) :
    (i : Weight K H L) (twoWeylVector (rootSystem H).flip b.flip) ≠ 0 := by
  simpa using coroot'_twoWeylVector_ne_zero (rootSystem H).flip b.flip i

/-! ### The eigenvalues of `ad (2ρ^∨)` -/

/-- **The eigenvalues of `ad (2ρ^∨)` are even integers.** Its eigenvalues are `0` on `H` and
`2 ht(α)` on the root space of a root `α`, so every eigenspace for a value that is not twice an
integer vanishes. -/
theorem eigenspace_ad_twoWeylVector_flip_eq_bot {μ : K} (hμ : ∀ n : ℤ, μ ≠ 2 * n) :
    (ad K L ((twoWeylVector (rootSystem H).flip b.flip : H) : L)).eigenspace μ = ⊥ := by
  set h := twoWeylVector (rootSystem H).flip b.flip
  -- no weight takes the value `μ` at `h`
  have hbot : ⨆ (χ : Weight K H L) (_ : χ h = μ), genWeightSpace L χ = ⊥ := by
    refine iSup₂_eq_bot.mpr fun χ hχ ↦ absurd hχ ?_
    by_cases hχ0 : χ.IsZero
    · simpa [hχ0.eq] using (hμ 0).symm
    · have := root_apply_twoWeylVector_flip_eq_two_mul_height b
        ⟨χ, by simpa [LieSubalgebra.root] using hχ0⟩
      exact fun hχμ ↦ hμ _ (hχμ ▸ this)
  refine eq_bot_iff.mpr fun y hy ↦ ?_
  have hy' : y ∈ genWeightSpaceOf L μ h := by
    rw [mem_genWeightSpaceOf]
    refine ⟨1, ?_⟩
    rw [Module.End.mem_eigenspace_iff, ad_apply] at hy
    simp [hy]
  rw [genWeightSpaceOf_eq_iSup_genWeightSpace, hbot] at hy'
  simpa using hy'

/-! ### The principal triple -/

/-- **The principal `sl₂` triple.** Let `cᵢ` be the coordinates of `2ρ^∨` in the basis of simple
coroots `αᵢ^∨`. If `eᵢ ∈ L_{αᵢ}` and `fᵢ ∈ L_{-αᵢ}` satisfy `⁅eᵢ, fᵢ⁆ = cᵢ αᵢ^∨` for every simple
root `αᵢ`, then `(2ρ^∨, ∑ᵢ eᵢ, ∑ᵢ fᵢ)` is an `sl₂` triple. -/
theorem isSl2Triple_twoWeylVector_flip_sum [Nonempty H.root] {e f : b.support → L}
    (he : ∀ i : b.support, e i ∈ rootSpace H ((i : H.root) : Weight K H L))
    (hf : ∀ i : b.support, f i ∈ rootSpace H (-((i : H.root) : Weight K H L)))
    (hef : ∀ i : b.support, ⁅e i, f i⁆ =
      b.toCoweightBasis.repr (twoWeylVector (rootSystem H).flip b.flip) i •
        (((rootSystem H).coroot i : H) : L)) :
    IsSl2Triple ((twoWeylVector (rootSystem H).flip b.flip : H) : L) (∑ i, e i) (∑ i, f i) where
  h_ne_zero := by
    simpa using twoWeylVector_ne_zero (rootSystem H).flip b.flip
  lie_e_f := by
    classical
    -- for `i ≠ j` the difference `αᵢ - αⱼ` is not a root, so `⁅eᵢ, fⱼ⁆ = 0`
    have hne : ∀ i j, j ≠ i → ⁅e i, f j⁆ = 0 := fun i j hji ↦
      lie_eq_zero_of_mem_rootSpace_of_base b hji.symm (he i) (hf j)
    simp_rw [sum_lie, lie_sum]
    rw [Finset.sum_congr rfl fun i _ ↦ Finset.sum_eq_single i (fun j _ hji ↦ hne i j hji)
      (by simp)]
    -- the diagonal terms reassemble `2ρ^∨` from its coordinates in the simple coroots
    conv_rhs => rw [← b.toCoweightBasis.sum_repr (twoWeylVector (rootSystem H).flip b.flip)]
    simp [hef]
  lie_h_e_nsmul := by
    rw [lie_sum, Finset.smul_sum]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [← LieSubalgebra.coe_bracket_of_module, lie_eq_smul_of_mem_rootSpace (he i),
      root_apply_twoWeylVector_flip b i.property, two_smul, two_smul]
  lie_h_f_nsmul := by
    rw [lie_sum, Finset.smul_sum, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [← LieSubalgebra.coe_bracket_of_module, lie_eq_smul_of_mem_rootSpace (hf i), Pi.neg_apply,
      root_apply_twoWeylVector_flip b i.property, neg_smul, two_smul, two_smul]

/-- **A sum of nonzero simple root vectors is a principal nilpositive element.** If `eᵢ` is a
nonzero vector of the root space of the simple root `αᵢ` for every `i`, then `∑ᵢ eᵢ` is the
nilpositive element of an `sl₂` triple with neutral element `2ρ^∨`, whose nilnegative element lies
in the negative nilradical. -/
theorem exists_mem_negativeNilradical_isSl2Triple_twoWeylVector_flip [Nonempty H.root]
    {e : b.support → L} (he : ∀ i : b.support, e i ∈ rootSpace H ((i : H.root) : Weight K H L))
    (he0 : ∀ i : b.support, e i ≠ 0) :
    ∃ f ∈ negativeNilradical H b,
      IsSl2Triple ((twoWeylVector (rootSystem H).flip b.flip : H) : L) (∑ i, e i) f := by
  choose f hf hef using fun i ↦
    exists_mem_rootSpace_neg_lie_eq_coroot (H.isNonZero_coe_root _) (he i) (he0 i)
  set c := b.toCoweightBasis.repr (twoWeylVector (rootSystem H).flip b.flip)
  refine ⟨∑ i, c i • f i, sum_mem fun i _ ↦ Submodule.smul_mem _ _ ?_,
    isSl2Triple_twoWeylVector_flip_sum b he (fun i ↦ Submodule.smul_mem _ _ (hf i))
      fun i ↦ by rw [lie_smul, hef i, rootSystem_coroot_apply]⟩
  refine mem_negativeNilradical_of_mem_rootSpace H b (α := -(i : H.root))
    (neg_mem_negRoots_of_mem_posRoots b (support_subset_posRoots _ b i.property)) ?_
  simpa using hf i

/-- **A sum of nonzero negative simple root vectors is a principal nilnegative element.** If `fᵢ`
is a nonzero vector of the root space of `-αᵢ` for every simple root `αᵢ`, then `∑ᵢ fᵢ` is the
nilnegative element of an `sl₂` triple with neutral element `2ρ^∨`, whose nilpositive element lies
in the positive nilradical. This is the normalization of the principal triple used for opers,
where the nilnegative element is prescribed. -/
theorem exists_mem_positiveNilradical_isSl2Triple_twoWeylVector_flip [Nonempty H.root]
    {f : b.support → L} (hf : ∀ i : b.support, f i ∈ rootSpace H (-((i : H.root) : Weight K H L)))
    (hf0 : ∀ i : b.support, f i ≠ 0) :
    ∃ e ∈ positiveNilradical H b,
      IsSl2Triple ((twoWeylVector (rootSystem H).flip b.flip : H) : L) e (∑ i, f i) := by
  -- a partner `eᵢ ∈ L_{αᵢ}` with `⁅fᵢ, eᵢ⁆ = (-αᵢ)^∨ = -αᵢ^∨`
  choose e he hfe using fun i ↦
    exists_mem_rootSpace_neg_lie_eq_coroot (H.isNonZero_coe_root _).neg (hf i) (hf0 i)
  set c := b.toCoweightBasis.repr (twoWeylVector (rootSystem H).flip b.flip)
  have he' : ∀ i : b.support, e i ∈ rootSpace H ((i : H.root) : Weight K H L) := fun i ↦ by
    simpa using he i
  refine ⟨∑ i, c i • e i, sum_mem fun i _ ↦ Submodule.smul_mem _ _ ?_,
    isSl2Triple_twoWeylVector_flip_sum b (fun i ↦ Submodule.smul_mem _ _ (he' i)) hf
      fun i ↦ ?_⟩
  · exact mem_positiveNilradical_of_mem_rootSpace H b (support_subset_posRoots _ b i.property)
      (he' i)
  · rw [smul_lie, ← lie_skew, hfe i, coroot_neg, rootSystem_coroot_apply]
    simp [c]

/-- **Existence of the principal triple.** When `L` has a root, `2ρ^∨` is the neutral element of
an `sl₂` triple. -/
theorem exists_isSl2Triple_twoWeylVector_flip [Nonempty H.root] :
    ∃ e f : L, IsSl2Triple ((twoWeylVector (rootSystem H).flip b.flip : H) : L) e f := by
  choose e he he0 using fun i : b.support ↦ ((i : H.root) : Weight K H L).exists_ne_zero
  obtain ⟨f, -, t⟩ := exists_mem_negativeNilradical_isSl2Triple_twoWeylVector_flip b he he0
  exact ⟨_, f, t⟩

end TauCeti

namespace IsSl2Triple

variable {b : (rootSystem H).Base} {e f : L}

/-- **`[L, e]` has dimension `dim L - dim H`.** For an `sl₂` triple `(2ρ^∨, e, f)`, the range
`[L, e]` of `ad e`, the would-be tangent space of the adjoint orbit of `e`, has dimension
`dim L - dim H`. -/
theorem finrank_range_ad_e_add_finrank_cartan
    (t : IsSl2Triple ((TauCeti.twoWeylVector (rootSystem H).flip b.flip : H) : L) e f) :
    finrank K (LinearMap.range (ad K L e)) + finrank K H = finrank K L := by
  -- `1` is not an even integer
  have h1 : ∀ n : ℤ, (1 : K) ≠ 2 * n := fun n hn ↦ by
    have : ((1 : ℤ) : K) = ((2 * n : ℤ) : K) := by push_cast; exact hn
    have := Int.cast_injective this
    omega
  -- the Cartan subalgebra and its underlying submodule have the same carrier
  have hH : finrank K H.toSubmodule = finrank K H := rfl
  have h := t.finrank_range_ad_e_add_finrank_eigenspace_zero_add_finrank_eigenspace_one (K := K)
  -- no root vanishes at `2ρ^∨`, so its centralizer is `H`
  rwa [Module.End.eigenspace_zero, H.ker_ad_eq_toSubmodule_of_forall_root_apply_ne_zero
      fun α hα ↦ TauCeti.root_apply_twoWeylVector_flip_ne_zero b ⟨α, hα⟩,
    TauCeti.eigenspace_ad_twoWeylVector_flip_eq_bot b h1, finrank_bot, add_zero, hH] at h

/-- **The centralizer of a principal nilpotent element has dimension `dim H`.** For an `sl₂`
triple `(2ρ^∨, e, f)`, the kernel of `ad e` has the dimension of the Cartan subalgebra, which is
the rank of `L`. -/
theorem finrank_ker_ad_e_eq_finrank_cartan
    (t : IsSl2Triple ((TauCeti.twoWeylVector (rootSystem H).flip b.flip : H) : L) e f) :
    finrank K (LinearMap.ker (ad K L e)) = finrank K H := by
  have h := (ad K L e).finrank_range_add_finrank_ker
  have h' := t.finrank_range_ad_e_add_finrank_cartan
  omega

end IsSl2Triple

namespace RootPairing.Base

variable (b : (rootSystem H).Base)

/-- **`2ρ^∨` is a dominant neutral element**: it is the neutral element of an `sl₂` triple, and
every simple root takes the value `2` at it. -/
theorem twoWeylVector_flip_mem_dominantNeutralElements [Nonempty H.root] :
    TauCeti.twoWeylVector (rootSystem H).flip b.flip ∈ b.dominantNeutralElements :=
  (b.mem_dominantNeutralElements_iff _).mpr ⟨TauCeti.exists_isSl2Triple_twoWeylVector_flip b,
    fun _ hi ↦ ⟨2, by simp [TauCeti.root_apply_twoWeylVector_flip b hi]⟩⟩

/-- **The weighted Dynkin diagram of the principal triple.** A dominant neutral element carries
the constant label `2` on every node of the Dynkin diagram exactly when it is `2ρ^∨`. -/
theorem weightedDynkinDiagram_eq_two_iff (h : b.dominantNeutralElements) :
    b.weightedDynkinDiagram h = (fun _ ↦ 2) ↔
      (h : H) = TauCeti.twoWeylVector (rootSystem H).flip b.flip := by
  have h2 : ∀ h' : b.dominantNeutralElements,
      (h' : H) = TauCeti.twoWeylVector (rootSystem H).flip b.flip →
        b.weightedDynkinDiagram h' = fun _ ↦ 2 := fun h' hh ↦ by
    funext i
    rw [weightedDynkinDiagram_apply_eq_iff, hh, TauCeti.root_apply_twoWeylVector_flip b i.property]
    simp
  refine ⟨fun hd ↦ ?_, h2 h⟩
  -- `h ≠ 0`, so the simple roots, a basis of the dual of `H`, are nonempty
  have : Nontrivial H := ⟨h, 0, fun h0 ↦ b.zero_notMem_dominantNeutralElements (h0 ▸ h.property)⟩
  have : Nonempty H.root := ⟨b.toWeightBasis.index_nonempty.some⟩
  -- weighted Dynkin labels determine a dominant neutral element
  exact congrArg Subtype.val <| b.weightedDynkinDiagram_injective (a₂ :=
    ⟨_, b.twoWeylVector_flip_mem_dominantNeutralElements⟩) (hd.trans (h2 _ rfl).symm)

end RootPairing.Base

namespace IsSl2Triple

variable {b : (rootSystem H).Base} {e f : L}

/-- **A principal nilpotent element is regular.** The nilpositive element of an `sl₂` triple with
neutral element `2ρ^∨` has a centralizer of the least possible dimension, the rank of `L`. -/
theorem isCentralizerRegular_e
    (t : IsSl2Triple ((TauCeti.twoWeylVector (rootSystem H).flip b.flip : H) : L) e f) :
    IsCentralizerRegular K e := by
  rw [isCentralizerRegular_iff_finrank_ker_ad_eq_rank, t.finrank_ker_ad_e_eq_finrank_cartan,
    H.rank_eq_finrank_cartan]

/-- **Regular nilpotent elements are principal.** If the neutral element `h` of an `sl₂` triple
`(h, e, f)` lies in `H` and is dominant for `b`, then `e` is regular exactly when `h = 2ρ^∨`, that
is, when every label of the weighted Dynkin diagram is `2`. -/
theorem isCentralizerRegular_e_iff {h : H} (t : IsSl2Triple (h : L) e f)
    (hh : ∀ i ∈ b.support, ∃ n : ℕ, (i : Weight K H L) h = n) :
    IsCentralizerRegular K e ↔ h = TauCeti.twoWeylVector (rootSystem H).flip b.flip := by
  refine ⟨fun he ↦ ?_, by rintro rfl; exact t.isCentralizerRegular_e⟩
  -- the centralizer of `e` has dimension `dim L(0) + dim L(1)`, and regularity makes it `dim H`
  have hker : finrank K (LinearMap.ker (ad K L e)) =
      finrank K ((ad K L h).eigenspace 0) + finrank K ((ad K L h).eigenspace 1) :=
    t.finrank_ker_toEnd_e_eq_finrank_eigenspace_zero_add_finrank_eigenspace_one (M := L)
  rw [isCentralizerRegular_iff_finrank_ker_ad_eq_rank, H.rank_eq_finrank_cartan] at he
  -- a root with value `0` or `1` at `h` would make `L(0) ⊔ L(1)` strictly larger than `H`
  have key (α : H.root) (hα : (α : Weight K H L) h = 0 ∨ (α : Weight K H L) h = 1) : False := by
    obtain ⟨y, hy, hy0⟩ := (α : Weight K H L).exists_ne_zero
    have hyh (z : H) : ⁅(z : L), y⁆ = (α : Weight K H L) z • y :=
      lie_eq_smul_of_mem_rootSpace hy z
    -- `y ∉ H`, because `H` is abelian and the root `α` is nonzero
    have hyH : y ∉ H.toSubmodule := fun hyH ↦ by
      have hα0 : (α : Weight K H L).IsNonZero := (Finset.mem_filter.mp α.property).2
      refine hα0 (funext fun z ↦ ?_)
      have hz : ⁅(z : L), y⁆ = 0 := congrArg Subtype.val (trivial_lie_zero H H z ⟨y, hyH⟩)
      rw [hyh] at hz
      exact (smul_eq_zero.mp hz).resolve_right hy0
    have hle : H.toSubmodule ⊔ K ∙ y ≤ (ad K L h).eigenspace 0 ⊔ (ad K L h).eigenspace 1 := by
      refine sup_le (fun z hz ↦ Submodule.mem_sup_left ?_)
        ((Submodule.span_singleton_le_iff_mem _ _).mpr ?_)
      · rw [Module.End.mem_eigenspace_iff, zero_smul, ad_apply]
        exact congrArg Subtype.val (trivial_lie_zero H H h ⟨z, hz⟩)
      · rcases hα with hα | hα
        · exact Submodule.mem_sup_left (by rw [Module.End.mem_eigenspace_iff, ad_apply, hyh, hα])
        · exact Submodule.mem_sup_right (by rw [Module.End.mem_eigenspace_iff, ad_apply, hyh, hα])
    have hlt := Submodule.finrank_lt_finrank_of_lt
      (left_lt_sup.mpr (by rwa [Submodule.span_singleton_le_iff_mem]) :
        H.toSubmodule < H.toSubmodule ⊔ K ∙ y)
    have hmono := Submodule.finrank_mono hle
    have hsup := Submodule.finrank_add_le_finrank_add_finrank ((ad K L h).eigenspace 0)
      ((ad K L h).eigenspace 1)
    have hH : finrank K H.toSubmodule = finrank K H := rfl
    omega
  -- so every simple root takes the value `2` at `h`
  refine (b.weightedDynkinDiagram_eq_two_iff
    ⟨h, (b.mem_dominantNeutralElements_iff h).mpr ⟨⟨e, f, t⟩, hh⟩⟩).mp (funext fun i ↦ ?_)
  rw [b.weightedDynkinDiagram_apply_eq_iff]
  rcases t.root_apply_eq_zero_or_eq_one_or_eq_two hh i.property with hi | hi | hi
  · exact (key i (.inl hi)).elim
  · exact (key i (.inr hi)).elim
  · simpa using hi

end IsSl2Triple
