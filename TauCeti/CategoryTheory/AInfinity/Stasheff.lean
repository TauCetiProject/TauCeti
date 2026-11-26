/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.AInfinity.Coderivation
public import TauCeti.CategoryTheory.Graded.ComposableWords

/-!
# Stasheff identities of path-compatible operations

Let `m` be a family of operations of degree `2 - n` on the total module of morphisms
`⨁ (X, Y), Hom(X, Y)` of a graded linear quiver. The unsuspended Stasheff sums of `m` are
multilinear in the inputs through the suspended bar construction, so they vanish on all
homogeneous inputs once they vanish on homogeneous morphisms, each lying in a single hom module
(`TauCeti.GradedLinearQuiver.stasheffSum_eq_zero_of_mem_range_homInclusion`).

When moreover every operation of positive arity is path-compatible, so that it sends composable
strings to morphisms between their endpoints and other strings to zero, every term of the
Stasheff sum vanishes on a string of morphisms which is not composable
(`TauCeti.GradedLinearQuiver.stasheffSum_eq_zero_of_not_isComposableString`). The Stasheff
identities of such a family therefore only have to be checked on homogeneous composable strings
`X₀ ⟵ X₁ ⟵ ⋯ ⟵ Xₙ`, in the input order of `A∞` operations
(`TauCeti.GradedLinearQuiver.stasheffSum_eq_zero_of_isPathCompatible`). This is how the
operations of an `A∞` category are constructed from data on composable strings.

## Main results

* `TauCeti.GradedLinearQuiver.stasheffSum_eq_zero_of_mem_range_homInclusion`: the Stasheff
  identities hold as soon as they hold on morphisms in single hom modules.
* `TauCeti.GradedLinearQuiver.stasheffSum_eq_zero_of_not_isComposableString`: the Stasheff sum
  of path-compatible operations vanishes on strings which are not composable.
* `TauCeti.GradedLinearQuiver.stasheffSum_eq_zero_of_isPathCompatible`: the Stasheff identities
  of path-compatible operations hold as soon as they hold on composable strings.

## References

* B. Keller, *Introduction to A-infinity algebras and modules*, Section 7.
-/

public section

namespace TauCeti.GradedLinearQuiver

universe u v w

open AInfinity
open _root_.MultilinearMap (evalNat evalNat_def)

variable {R : Type w} [CommRing R] {C : Type u} [GradedLinearQuiver.{u, v, w} R C]

/-! ### Stasheff identities -/

variable {m : ∀ k : ℕ, MultilinearMap (RingHom.id R) (fun _ : Fin k ↦ TotalHom R C) (TotalHom R C)}

/-- **The Stasheff identities can be checked on morphisms in single hom modules.** For operations
of degree `2 - k` on the total module of morphisms, if the Stasheff sum of arity `n` vanishes on
homogeneous inputs each lying in a single hom module, it vanishes on all homogeneous inputs:
through the suspended bar construction, it is multilinear in its inputs. -/
theorem stasheffSum_eq_zero_of_mem_range_homInclusion
    (hm : ∀ k, 0 < k → MultilinearMap.IsHomogeneous (m k) (fun _ ↦ (totalGrading R C).piece)
      (totalGrading R C).piece (2 - k))
    {n : ℕ} (hn : 0 < n)
    (h : ∀ (d : ℕ → ℤ) (a b : ℕ → C) (y : ℕ → TotalHom R C),
      (∀ i < n, y i ∈ LinearMap.range (homInclusion (R := R) (a i) (b i))) →
        (∀ i < n, y i ∈ (totalGrading R C).piece (d i)) → stasheffSum m d y n = 0)
    (d : ℕ → ℤ) (x : ℕ → TotalHom R C) (hx : ∀ i < n, x i ∈ (totalGrading R C).piece (d i)) :
    stasheffSum m d x n = 0 := by
  set G := totalGrading R C
  have hFm := isSuspension_suspensionTaylor G m
  have hm' (k : ℕ) (hk : 0 < k) (_ : k ≤ n) := hm k hk
  -- The arity-`n` component of the square of the bar coderivation is multilinear and equals the
  -- Stasheff sum up to a sign; it vanishes on morphisms in single hom modules.
  have key : ((ReducedTensorWords.gradedCoderiv (G.shift 1) (suspensionTaylor G m) 1 ∘ₗ
      ReducedTensorWords.gradedCoderiv (G.shift 1) (suspensionTaylor G m) 1).taylorComponent
        ⟨n, hn⟩).compMultilinearMap (PiTensorProduct.tprod R) (fun i : Fin n ↦ x i) ∈
          (⊥ : Submodule R _) := by
    refine multilinearMap_apply_mem_of_mem_totalGrading_piece (d := fun i ↦ d i)
      (fun s t g hg ↦ ?_) fun i ↦ hx i i.isLt
    obtain ⟨a, b, y, hyab, -, -, hy⟩ :=
      exists_natString hn s t fun i ↦ LinearMap.mem_range_self (homInclusion (s i) (t i)) (g i)
    have hyd (i : ℕ) (hi : i < n) : y i ∈ G.piece (d i) := by
      rw [hy ⟨i, hi⟩, homInclusion_mem_totalGrading_piece_iff]
      exact hg ⟨i, hi⟩
    have hyg : (fun i : Fin n ↦ y i) = fun i ↦ homInclusion (s i) (t i) (g i) := funext hy
    rw [LinearMap.compMultilinearMap_apply, ← hyg,
      hFm.taylorComponent_comp_self_eq_smul_stasheffSum hm' hn d y hyd, h d a b y hyab hyd,
      smul_zero]
    exact zero_mem _
  rwa [Submodule.mem_bot, LinearMap.compMultilinearMap_apply,
    hFm.taylorComponent_comp_self_eq_smul_stasheffSum hm' hn d x hx,
    negOnePowCast_smul_eq_zero_iff] at key

/-- **The Stasheff sum of path-compatible operations vanishes on strings which are not
composable.** In each term, either the inner operation is applied to a block which is not
composable, or the outer operation is applied to a string which is not composable. -/
theorem stasheffSum_eq_zero_of_not_isComposableString
    (hm : ∀ k, 0 < k → IsPathCompatible id (m k)) {n : ℕ} {a b : ℕ → C}
    {x : ℕ → TotalHom R C} (hx : ∀ i < n, x i ∈ LinearMap.range (homInclusion (R := R) (a i) (b i)))
    (hab : ¬ IsComposableString a b n) (d : ℕ → ℤ) : stasheffSum m d x n = 0 := by
  rw [stasheffSum_def]
  refine Finset.sum_eq_zero fun p hp ↦ Finset.sum_eq_zero fun s hs ↦ ?_
  rw [Finset.mem_range] at hp
  rw [Finset.mem_Icc] at hs
  have hblock (i : ℕ) (hi : i < s) : x (p + i) ∈
      LinearMap.range (homInclusion (R := R) (a (p + i)) (b (p + i))) := hx _ (by omega)
  rw [stasheffTerm_def]
  rcases not_isComposableString_block_or_replaceBlock (p := p) (s := s) hab with h | h
  · rw [(hm s (by omega)).evalNat_eq_zero_of_not_isComposableString hblock h, evalNat_def,
      (m _).map_coord_zero (⟨p, by omega⟩ : Fin (p + 1 + (n - p - s))) (by simp), smul_zero]
  · -- The inner operation lands in a single hom module.
    have hinner : evalNat (m s) (fun j ↦ x (p + j)) ∈
        LinearMap.range (homInclusion (R := R) (a (p + s - 1)) (b p)) := by
      rw [show p + s - 1 = p + (s - 1) by omega]
      exact (hm s (by omega)).evalNat_mem_range_homInclusion_of_pos (by omega) hblock
    rw [(hm _ (by omega)).evalNat_eq_zero_of_not_isComposableString
      (replaceBlock_mem_range_homInclusion hx hinner (by omega)) h, smul_zero]

/-- **The Stasheff identities of path-compatible operations can be checked on composable
strings.** Let `m` be operations of degree `2 - k` on the total module of morphisms, path-compatible
in positive arity. If the Stasheff sum of arity `n` vanishes on every homogeneous string
`xᵢ : X (i + 1) ⟶ X i`, `i < n`, it vanishes on all homogeneous inputs. -/
theorem stasheffSum_eq_zero_of_isPathCompatible
    (hm : ∀ k, 0 < k → MultilinearMap.IsHomogeneous (m k) (fun _ ↦ (totalGrading R C).piece)
      (totalGrading R C).piece (2 - k))
    (hpc : ∀ k, 0 < k → IsPathCompatible id (m k)) {n : ℕ} (hn : 0 < n)
    (h : ∀ (X : ℕ → C) (d : ℕ → ℤ) (y : ℕ → TotalHom R C),
      (∀ i < n, y i ∈ LinearMap.range (homInclusion (R := R) (X (i + 1)) (X i))) →
        (∀ i < n, y i ∈ (totalGrading R C).piece (d i)) → stasheffSum m d y n = 0)
    (d : ℕ → ℤ) (x : ℕ → TotalHom R C) (hx : ∀ i < n, x i ∈ (totalGrading R C).piece (d i)) :
    stasheffSum m d x n = 0 := by
  refine stasheffSum_eq_zero_of_mem_range_homInclusion hm hn (fun e a b y hy he ↦ ?_) d x hx
  by_cases hab : IsComposableString a b n
  · -- A composable string of morphisms `aᵢ ⟶ bᵢ` runs through the objects `b₀, …, bₙ₋₁, aₙ₋₁`.
    refine h (fun i ↦ if i < n then b i else a (n - 1)) e y (fun i hi ↦ ?_) he
    have hsrc : (if i + 1 < n then b (i + 1) else a (n - 1)) = a i := by
      split_ifs with hi'
      · exact hab.eq i hi'
      · rw [show i = n - 1 by omega]
    rw [hsrc, ite_eq_left hi]
    exact hy i hi
  · exact stasheffSum_eq_zero_of_not_isComposableString hpc hy hab e

end TauCeti.GradedLinearQuiver
