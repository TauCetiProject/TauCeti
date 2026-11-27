/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.AdjointAction.Regular
public import TauCeti.Algebra.Lie.Weights.Borel
public import TauCeti.Algebra.Lie.Weights.Projection
import Mathlib.Algebra.CharZero.Infinite
import TauCeti.Algebra.Lie.Killing.Regular
import TauCeti.Algebra.Lie.Sl2.Principal
import TauCeti.Algebra.Lie.Sl2.Spectrum
import TauCeti.Algebra.Lie.Weights.Dimension
import TauCeti.Algebra.Lie.Weights.Eigenvector
import TauCeti.Algebra.Lie.Weights.Rank
import TauCeti.LinearAlgebra.Graded.Kernel
import TauCeti.LinearAlgebra.RootSystem.Height

/-!
# Regular elements of the positive nilradical

Let `L` be a finite-dimensional Lie algebra with non-degenerate Killing form over a field `K` of
characteristic zero, let `H` be a splitting Cartan subalgebra and let `b` be a base of its root
system, with positive nilradical `n⁺ = ⨁_{α > 0} Lα`. Write an element of `n⁺` as
`x = ∑_{α > 0} xα` with `xα ∈ Lα`. This file proves **Kostant's criterion**: `x` is regular, in
the sense that its centralizer `ker (ad x)` has the least possible dimension `rank L`, exactly when
its component `xα` at every simple root `α` is nonzero
(`TauCeti.isCentralizerRegular_iff_forall_genWeightSpaceProjection_ne_zero`). The component `xα`
is the image of `x` under the projection `TauCeti.genWeightSpaceProjection` of the root-space
decomposition.

Both directions are proved by counting dimensions.

*A vanishing simple component.* If `xα = 0` for a simple root `α`, then `x` lies in the span `u` of
the root spaces of the positive roots other than `α`, which is an ideal of the parabolic subalgebra
`p = H ⊕ L_{-α} ⊕ ⨁_{β > 0} Lβ`: a positive root `β ≠ α` stays positive, and different from
`α`, after adding a positive root or subtracting `α`. So `ad x` maps `p` into `u`, and since `p`
together with the negative root spaces other than `L_{-α}` spans `L`, the range of `ad x` has
dimension at most `2 (#Δ⁺ - 1)`. Hence `dim ker (ad x) ≥ rank L + 2`
(`TauCeti.rank_add_two_le_finrank_ker_ad_of_mem_rootSpaceSpan`).

*Nonzero simple components.* Grade `L` by the eigenvalues of `ad (2ρ^∨)`, which are twice the
heights of the roots. Then `x = e + y` with `e = ∑_{α simple} xα` homogeneous of degree `2` and
`y` of degree at least `4`. By the principal `sl₂` triple, `e` is regular
(`IsSl2Triple.finrank_ker_ad_e_eq_finrank_cartan`), and adding terms of higher degree does not
enlarge the kernel (`LinearMap.IsHomogeneous.finrank_ker_add_le`). So `x` is regular
(`TauCeti.isCentralizerRegular_sum_add`).

## Main results

* `TauCeti.rank_add_two_le_finrank_ker_ad_of_mem_rootSpaceSpan`: an element of `n⁺` with zero
  component at a simple root has a centralizer of dimension at least `rank L + 2`.
* `TauCeti.isCentralizerRegular_sum_add`: a sum of nonzero simple root vectors plus root vectors
  of non-simple positive roots is regular.
* `TauCeti.isCentralizerRegular_iff_forall_genWeightSpaceProjection_ne_zero`: **Kostant's
  criterion**, an element of `n⁺` is regular exactly when its components at all simple roots are
  nonzero.

## References

* B. Kostant, *The principal three-dimensional subgroup and the Betti numbers of a complex simple
  Lie group*, Amer. J. Math. **81** (1959), 973–1032, §5.
* D. H. Collingwood and W. M. McGovern, *Nilpotent Orbits in Semisimple Lie Algebras*, Van
  Nostrand Reinhold, 1993, §4.1.
-/

public section

open LieAlgebra LieModule LieAlgebra.IsKilling Module

variable {K L : Type*} [Field K] [CharZero K] [LieRing L] [LieAlgebra K L]
  [FiniteDimensional K L] [IsKilling K L]
  {H : LieSubalgebra K L} [H.IsCartanSubalgebra] [IsTriangularizable K H L]

namespace TauCeti

/-! ### A vanishing simple component -/

variable (b : (rootSystem H).Base)

/-- Adding a positive root, or subtracting a simple root `αᵢ`, keeps a positive root other than
`αᵢ` positive and different from `αᵢ`: the root spaces of the parabolic subalgebra
`H ⊕ L_{-αᵢ} ⊕ n⁺` move the span of the root spaces of the positive roots other than `αᵢ` into
itself, weight space by weight space. -/
private theorem rootSpace_add_le_rootSpaceSpan_posRoots_sdiff {i : H.root} (hi : i ∈ b.support)
    {χ : H → K}
    (hχ : χ ∈ insert 0 ((fun k : H.root ↦ (k : H → K)) '' insert (-i) (posRoots (rootSystem H) b)))
    {δ : H.root} (hδ : δ ∈ posRoots (rootSystem H) b \ {i}) :
    rootSpace H (χ + (δ : H → K)) ≤ rootSpaceSpan H (posRoots (rootSystem H) b \ {i}) := by
  have hroot_neg (k : H.root) : (rootSystem H).root (-k) = -(rootSystem H).root k := by
    rw [← rootSystem_reflectionPerm_self_eq_neg]
    exact RootPairing.root_reflectionPerm_self (rootSystem H) k
  obtain ⟨hδpos, hδi⟩ := hδ
  rcases hχ with rfl | ⟨γ, hγ, rfl⟩
  · rw [zero_add]
    exact rootSpace_le_rootSpaceSpan ⟨hδpos, hδi⟩
  rcases hγ with rfl | hγ
  · -- `δ - αᵢ` is positive, and it is not `αᵢ`, since `2 αᵢ` is not a root
    refine rootSpace_add_le_rootSpaceSpan_of_forall (fun h ↦ hδi ?_) fun k hk ↦ ⟨?_, ?_⟩
    · rw [hroot_neg, neg_add_eq_zero] at h
      exact (rootSystem H).root.injective h.symm
    · rw [hroot_neg, neg_add_eq_sub] at hk
      exact (mem_posRoots _ b k).mpr <|
        RootPairing.Base.IsPos.sub ((mem_posRoots _ b δ).mp hδpos) hi hk
    · rintro rfl
      rw [hroot_neg, neg_add_eq_sub, eq_sub_iff_add_eq] at hk
      have h2 : ((δ : Weight K H L) : H → K) = 2 • ((k : Weight K H L) : H → K) := by
        funext z
        simpa [two_smul, Weight.toLinear_apply] using (LinearMap.congr_fun hk z).symm
      have hbot : rootSpace H ((δ : Weight K H L) : H → K) = ⊥ := by
        rw [h2]
        exact rootSpace_two_smul (k : Weight K H L) (H.isNonZero_coe_root k)
      exact Weight.genWeightSpace_ne_bot L (δ : Weight K H L) hbot
  · -- `γ + δ` is positive of height at least two, so it is not `αᵢ`
    refine rootSpace_add_le_rootSpaceSpan_of_forall
      (root_add_ne_zero_of_mem_posRoots_of_mem_posRootCone _ b hγ
        (root_mem_posRootCone_of_mem_posRoots _ b hδpos)) fun k hk ↦ ⟨?_, ?_⟩
    · exact (mem_posRoots _ b k).mpr <| RootPairing.Base.IsPos.add
        ((mem_posRoots _ b γ).mp hγ) ((mem_posRoots _ b δ).mp hδpos) hk
    · rintro rfl
      have := b.height_add hk
      have := RootPairing.Base.height_one_of_mem_support hi
      have := one_le_height_of_mem_posRoots (rootSystem H) b hδpos
      have := one_le_height_of_mem_posRoots (rootSystem H) b hγ
      omega

/-- The parabolic subalgebra `p = H ⊕ L_{-αᵢ} ⊕ n⁺` and the root spaces of the negative roots
other than `-αᵢ` together span `L`. -/
private theorem genWeightSpaceSpan_sup_rootSpaceSpan_negRoots_sdiff_eq_top (i : H.root) :
    genWeightSpaceSpan H L
        (insert 0 ((fun k : H.root ↦ (k : H → K)) '' insert (-i) (posRoots (rootSystem H) b))) ⊔
      rootSpaceSpan H (negRoots (rootSystem H) b \ {-i}) = ⊤ := by
  rw [eq_top_iff, ← iSup_genWeightSpace_eq_top' K H L]
  refine iSup_le fun χ ↦ ?_
  by_cases hχ : (χ : H → K) = 0
  · exact le_sup_of_le_left (genWeightSpace_le_genWeightSpaceSpan (by simp [hχ]))
  let k : H.root := ⟨χ, by simpa [LieSubalgebra.root] using hχ⟩
  -- `k` is `χ` with its nonzeroness attached, so its root space is the weight space of `χ`
  change rootSpace H (k : H → K) ≤ _
  by_cases hk : k ∈ insert (-i) (posRoots (rootSystem H) b)
  · exact le_sup_of_le_left (genWeightSpace_le_genWeightSpaceSpan
      (Set.mem_insert_of_mem _ ⟨k, hk, rfl⟩))
  · refine le_sup_of_le_right (rootSpace_le_rootSpaceSpan ⟨?_, fun h ↦ hk (.inl h)⟩)
    exact (not_mem_posRoots_iff_mem_negRoots (rootSystem H) b k).mp fun h ↦ hk (.inr h)

/-- **An element of `n⁺` with zero component at a simple root is far from regular.** If `x` lies
in the span of the root spaces of the positive roots other than the simple root `αᵢ`, then its
centralizer has dimension at least `rank L + 2`. -/
theorem rank_add_two_le_finrank_ker_ad_of_mem_rootSpaceSpan {i : H.root} (hi : i ∈ b.support)
    {x : L} (hx : x ∈ rootSpaceSpan H (posRoots (rootSystem H) b \ {i})) :
    LieAlgebra.rank K L + 2 ≤ finrank K (LinearMap.ker (ad K L x)) := by
  set U := rootSpaceSpan H (posRoots (rootSystem H) b \ {i})
  set N := rootSpaceSpan H (negRoots (rootSystem H) b \ {-i})
  -- `ad x` maps the parabolic subalgebra `p` into `u`, and `p` and `N` together span `L`, so
  -- the range of `ad x` lies in `u ⊔ ad x (N)`
  have hle : LinearMap.range (ad K L x) ≤ U.toSubmodule ⊔ N.toSubmodule.map (ad K L x) := by
    rw [LinearMap.range_eq_map, ← LieSubmodule.top_toSubmodule (R := K) (L := H),
      ← genWeightSpaceSpan_sup_rootSpaceSpan_negRoots_sdiff_eq_top b i,
      LieSubmodule.sup_toSubmodule, Submodule.map_sup]
    refine sup_le_sup_right (Submodule.map_le_iff_le_comap.mpr fun z hz ↦ ?_) _
    rw [Submodule.mem_comap, ad_apply, ← lie_skew]
    -- `u` is stable under the parabolic subalgebra `p = H ⊕ L_{-αᵢ} ⊕ n⁺`
    exact neg_mem (lie_mem_rootSpaceSpan
      (fun _ hχ _ hδ ↦ rootSpace_add_le_rootSpaceSpan_posRoots_sdiff b hi hχ hδ) hz hx)
  have hrange : finrank K (LinearMap.range (ad K L x)) ≤
      (posRoots (rootSystem H) b \ {i}).ncard + (negRoots (rootSystem H) b \ {-i}).ncard := by
    calc finrank K (LinearMap.range (ad K L x))
        ≤ finrank K U.toSubmodule + finrank K (N.toSubmodule.map (ad K L x)) :=
          (Submodule.finrank_mono hle).trans (Submodule.finrank_add_le_finrank_add_finrank _ _)
      _ ≤ finrank K U + finrank K N := by
          rw [LieSubmodule.finrank_toSubmodule, ← LieSubmodule.finrank_toSubmodule N]
          exact Nat.add_le_add_left (Submodule.finrank_map_le _ _) _
      _ = _ := by rw [finrank_rootSpaceSpan, finrank_rootSpaceSpan]
  -- count: `dim L = rank L + 2 #Δ⁺`, and both sets above have `#Δ⁺ - 1` elements
  have hipos : i ∈ posRoots (rootSystem H) b := support_subset_posRoots (rootSystem H) b hi
  have hpos := Set.ncard_sdiff_singleton_of_mem hipos
  have hneg := Set.ncard_sdiff_singleton_of_mem (neg_mem_negRoots_of_mem_posRoots b hipos)
  rw [ncard_negRoots_eq_ncard_posRoots] at hneg
  have hcard : 0 < (posRoots (rootSystem H) b).ncard :=
    (Set.ncard_pos (Set.toFinite _)).mpr ⟨i, hipos⟩
  have hdim := finrank_eq_finrank_cartan_add_two_mul_ncard_posRoots H b
  have hrn := LinearMap.finrank_range_add_finrank_ker (ad K L x)
  rw [H.rank_eq_finrank_cartan]
  omega

/-! ### Nonzero simple components -/

/-- **A principal nilpotent element perturbed by higher root vectors is regular.** If `eᵢ` is a
nonzero vector of the root space of each simple root `αᵢ` and `y` lies in the span of the root
spaces of the non-simple positive roots, then `∑ᵢ eᵢ + y` is regular. -/
theorem isCentralizerRegular_sum_add {e : b.support → L}
    (he : ∀ i : b.support, e i ∈ rootSpace H ((i : H.root) : Weight K H L))
    (he0 : ∀ i : b.support, e i ≠ 0) {y : L}
    (hy : y ∈ rootSpaceSpan H (posRoots (rootSystem H) b \ b.support)) :
    IsCentralizerRegular K (∑ i, e i + y) := by
  rw [isCentralizerRegular_iff_finrank_ker_ad_eq_rank]
  refine le_antisymm ?_ (rank_le_finrank_ker_ad K _)
  rw [H.rank_eq_finrank_cartan]
  rcases isEmpty_or_nonempty H.root with hH | hH
  · -- without roots `L = H`
    have hdim := finrank_eq_finrank_cartan_add_two_mul_ncard_posRoots H b
    rw [Set.eq_empty_of_isEmpty (posRoots (rootSystem H) b), Set.ncard_empty] at hdim
    exact (Submodule.finrank_le _).trans hdim.le
  -- grade `L` by the eigenvalues of `ad (2ρ^∨)`, which are twice the heights of the roots
  obtain ⟨f, -, t⟩ := exists_mem_negativeNilradical_isSl2Triple_twoWeylVector_flip b he he0
  set h₀ : H := twoWeylVector (rootSystem H).flip b.flip
  set 𝒜 : ℤ → Submodule K L := fun n ↦ (ad K L (h₀ : L)).eigenspace (n : K)
  have hind : iSupIndep 𝒜 := (ad K L (h₀ : L)).eigenspaces_iSupIndep.comp Int.cast_injective
  have htop : ⨆ n, 𝒜 n = ⊤ := (isInternal_eigenspace_toEnd_intCast t (M := L)).submodule_iSup_eq_top
  have hT : LinearMap.IsHomogeneous (ad K L (∑ i, e i)) 𝒜 𝒜 2 := by
    refine LinearMap.isHomogeneous_def.mpr fun n v hv ↦ ?_
    have hsum : ∑ i, e i ∈ 𝒜 2 := sum_mem fun i _ ↦ by
      have := mem_eigenspace_ad_twoWeylVector_flip_of_mem_rootSpace b (he i)
      rwa [RootPairing.Base.height_one_of_mem_support i.property, mul_one] at this
    have := lie_mem_eigenspace_toEnd_add hsum hv
    rw [show ((2 : ℤ) : K) + (n : K) = ((n + 2 : ℤ) : K) by push_cast; ring] at this
    exact this
  have hS : ∀ ⦃n : ℤ⦄ ⦃v : L⦄, v ∈ 𝒜 n → ad K L y v ∈ ⨆ (m : ℤ) (_ : n + 2 < m), 𝒜 m := by
    intro n v hv
    rw [rootSpaceSpan_eq_iSup] at hy
    refine LieSubmodule.iSup_induction _ (motive := fun y ↦ ad K L y v ∈ _) hy
      (fun γ z hz ↦ ?_) (by simp) (fun z z' hz hz' ↦ ?_)
    swap
    · rw [map_add, LinearMap.add_apply]
      exact add_mem hz hz'
    -- a non-simple positive root has height at least two
    obtain ⟨hγpos, hγs⟩ := γ.property
    have h1 := one_le_height_of_mem_posRoots (rootSystem H) b hγpos
    have h2 : b.height γ ≠ 1 := fun h ↦ hγs ((RootPairing.Base.height_eq_one_iff b).mp h)
    refine Submodule.mem_iSup_of_mem (2 * b.height γ + n) (Submodule.mem_iSup_of_mem
      (by omega) ?_)
    have := lie_mem_eigenspace_toEnd_add
      (mem_eigenspace_ad_twoWeylVector_flip_of_mem_rootSpace b hz) hv
    rw [← Int.cast_add] at this
    exact this
  calc finrank K (LinearMap.ker (ad K L (∑ i, e i + y)))
      ≤ finrank K (LinearMap.ker (ad K L (∑ i, e i))) := by
        rw [map_add]
        exact hT.finrank_ker_add_le hind htop hS
    _ = finrank K H := t.finrank_ker_ad_e_eq_finrank_cartan

/-! ### Kostant's criterion -/

/-- **Kostant's criterion for regular elements of the positive nilradical.** An element `x` of
`n⁺` is regular exactly when its component `xα` along the root-space decomposition is nonzero at
every simple root `α`. -/
theorem isCentralizerRegular_iff_forall_genWeightSpaceProjection_ne_zero {x : L}
    (hx : x ∈ positiveNilradical H b) :
    IsCentralizerRegular K x ↔
      ∀ i ∈ b.support, genWeightSpaceProjection K H L (i : Weight K H L) x ≠ 0 := by
  classical
  rw [mem_positiveNilradical, mem_rootSpaceSpan_iff] at hx
  refine ⟨fun hreg i hi hxi ↦ ?_, fun hx0 ↦ ?_⟩
  · -- a zero simple component puts `x` in `u`, whose elements have too large a centralizer
    have hu : x ∈ rootSpaceSpan H (posRoots (rootSystem H) b \ {i}) := by
      refine mem_rootSpaceSpan_iff.mpr fun χ hχ ↦ ?_
      obtain ⟨k, hk, rfl⟩ := hx χ hχ
      exact ⟨k, ⟨hk, by rintro rfl; exact hχ hxi⟩, rfl⟩
    have := rank_add_two_le_finrank_ker_ad_of_mem_rootSpaceSpan b hi hu
    rw [isCentralizerRegular_iff_finrank_ker_ad_eq_rank] at hreg
    omega
  · -- split `x` into its simple components and the rest
    set e : b.support → L := fun i ↦ genWeightSpaceProjection K H L ((i : H.root) : Weight K H L) x
    have hy : x - ∑ i, e i ∈ rootSpaceSpan H (posRoots (rootSystem H) b \ b.support) := by
      refine mem_rootSpaceSpan_iff.mpr fun χ hχ ↦ ?_
      by_cases hs : ∃ j : b.support, ((j : H.root) : Weight K H L) = χ
      · obtain ⟨j, rfl⟩ := hs
        refine absurd ?_ hχ
        rw [map_sub, map_sum, Finset.sum_eq_single j (fun i _ hij ↦ ?_) (by simp)]
        · simp [e]
        · exact genWeightSpaceProjection_apply_apply_of_ne
            (fun h ↦ hij (Subtype.val_injective (Subtype.val_injective h))) x
      · simp only [not_exists] at hs
        have hχx : genWeightSpaceProjection K H L χ x ≠ 0 := by
          rwa [map_sub, map_sum, Finset.sum_eq_zero fun i _ ↦
            genWeightSpaceProjection_apply_apply_of_ne (hs i) x, sub_zero] at hχ
        obtain ⟨k, hk, rfl⟩ := hx χ hχx
        exact ⟨k, ⟨hk, fun hks ↦ hs ⟨k, hks⟩ rfl⟩, rfl⟩
    rw [← add_sub_cancel (∑ i, e i) x]
    exact isCentralizerRegular_sum_add b (fun i ↦ genWeightSpaceProjection_apply_mem _ x)
      (fun i ↦ hx0 i i.property) hy

end TauCeti
