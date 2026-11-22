/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.RootSystem.BaseChange
public import Mathlib.LinearAlgebra.RootSystem.Hom
public import TauCeti.LinearAlgebra.RootSystem.Basic
import TauCeti.LinearAlgebra.RootSystem.HomInvariance

/-!
# Balanced root pairings and projection onto the root span

Let `P` be a root pairing over a commutative ring `R`, with weight module `M` and coweight module
`N`. When `P` is not a root system, `M` can carry central directions outside `P.rootSpan R`, such
as the character or cocharacter directions of the center of a reductive group like `GLₙ`. The
natural candidate complement to `P.rootSpan R` is the **central kernel** `P.corootKer`: the common
kernel `⨅ i, LinearMap.ker (P.coroot' i)` of all coroot functionals, which the perfect pairing
identifies with the dual annihilator of `P.corootSpan R`.

Mathlib's `RootPairing.IsBalanced` says precisely that `P.rootSpan R` and `P.corootSpan R` are
perfectly complementary, which unfolds on the weight side to `IsCompl (P.rootSpan R) P.corootKer`
and on the coweight side to the dual statement for `P.flip`.

When `P` is balanced, the direct-sum decomposition `M = P.rootSpan R ⊕ P.corootKer` yields a linear
projection `P.rootSpanProj : M →ₗ[R] P.rootSpan R` along `P.corootKer`. Subtracting
`P.rootSpanProj x` from `x` changes `x` only by an element of `P.corootKer`, so `P.rootSpanProj`
preserves every coroot evaluation and commutes with root reflections and with equivalences of
balanced root pairings.

## Main definitions

* `RootPairing.rootSpanProj`: the linear projection `M →ₗ[R] P.rootSpan R` along `P.corootKer` for
  a balanced root pairing.

## Main results

* `RootPairing.instFlipIsBalanced`: the dual of a balanced root pairing is balanced.
* `RootPairing.isCompl_rootSpan_corootKer` and `RootPairing.isBalanced_iff_isCompl`: a root pairing
  is balanced if and only if `P.rootSpan R` complements `P.corootKer` and `P.corootSpan R`
  complements `P.flip.corootKer`.
* `RootPairing.coroot'_coe_rootSpanProj`: `P.rootSpanProj` preserves all coroot evaluations.
* `RootPairing.Equiv.coe_rootSpanProj_weightMap`: equivalences of balanced root pairings commute
  with `rootSpanProj`.

## References

* N. Bourbaki, *Lie Groups and Lie Algebras, Chapters 4--6*, Ch. VI, §1.
* M. Demazure, A. Grothendieck (eds.), *Schémas en groupes III* (SGA 3), Exposé XXI, §1.
-/

public section

open Function Module Set Submodule

namespace RootPairing

section IsBalanced

variable {ι R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M]
  [AddCommGroup N] [Module R N] (P : RootPairing ι R M N)

/-- The dual of a balanced root pairing is balanced. -/
instance instFlipIsBalanced [P.IsBalanced] : P.flip.IsBalanced where
  isPerfectCompl := (IsBalanced.isPerfectCompl (P := P)).flip

/-- In a balanced root pairing, the root span and the central kernel are complementary
submodules of the weight space. -/
theorem isCompl_rootSpan_corootKer [P.IsBalanced] :
    IsCompl (P.rootSpan R) P.corootKer := by
  rw [corootKer_def, ← P.corootSpan_dualAnnihilator_map_eq_iInf_ker_coroot']
  exact (IsBalanced.isPerfectCompl (P := P)).isCompl_left

/-- A root pairing is balanced precisely when `P.rootSpan R` complements `P.corootKer` in `M`
and `P.corootSpan R` complements `P.flip.corootKer` in `N`. -/
theorem isBalanced_iff_isCompl :
    P.IsBalanced ↔
      IsCompl (P.rootSpan R) P.corootKer ∧ IsCompl (P.corootSpan R) P.flip.corootKer := by
  refine ⟨fun _ ↦ ⟨P.isCompl_rootSpan_corootKer, P.flip.isCompl_rootSpan_corootKer⟩, ?_⟩
  rintro ⟨h₁, h₂⟩
  rw [corootKer_def] at h₁ h₂
  refine ⟨⟨?_, ?_⟩⟩
  · exact P.corootSpan_dualAnnihilator_map_eq_iInf_ker_coroot'.symm ▸ h₁
  · exact P.rootSpan_dualAnnihilator_map_eq_iInf_ker_root'.symm ▸ h₂

end IsBalanced

section RootSpanProj

variable {ι R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M]
  [AddCommGroup N] [Module R N] (P : RootPairing ι R M N) [P.IsBalanced]

/-- The **root-span projection** of a balanced root pairing: the `R`-linear projection
`M →ₗ[R] P.rootSpan R` along the central kernel `P.corootKer`. -/
noncomputable def rootSpanProj : M →ₗ[R] P.rootSpan R :=
  (P.rootSpan R).projectionOnto P.corootKer P.isCompl_rootSpan_corootKer

/-- `RootPairing.rootSpanProj` acts as the identity on elements of `P.rootSpan R`. -/
@[simp]
theorem rootSpanProj_coe (x : P.rootSpan R) : P.rootSpanProj x = x :=
  Submodule.projectionOnto_apply_left P.isCompl_rootSpan_corootKer x

/-- On a weight belonging to `P.rootSpan R`, `P.rootSpanProj` returns that weight as a subtype
element. -/
theorem rootSpanProj_apply_of_mem {x : M} (hx : x ∈ P.rootSpan R) :
    P.rootSpanProj x = ⟨x, hx⟩ :=
  Submodule.projectionOnto_apply_of_mem_left P.isCompl_rootSpan_corootKer hx

/-- Coercing `P.rootSpanProj x` back to `M` gives `x` whenever `x ∈ P.rootSpan R`. -/
theorem coe_rootSpanProj_of_mem {x : M} (hx : x ∈ P.rootSpan R) :
    (P.rootSpanProj x : M) = x :=
  Submodule.projection_apply_of_mem_left P.isCompl_rootSpan_corootKer hx

/-- `RootPairing.rootSpanProj` sends each root `P.root i` to `P.rootSpanMem R i`. -/
@[simp]
theorem rootSpanProj_root (i : ι) : P.rootSpanProj (P.root i) = P.rootSpanMem R i :=
  P.rootSpanProj_apply_of_mem (subset_span (mem_range_self i))

/-- `P.rootSpanProj x` vanishes if and only if `x` lies in the central kernel `P.corootKer`. -/
@[simp]
theorem rootSpanProj_eq_zero_iff {x : M} : P.rootSpanProj x = 0 ↔ x ∈ P.corootKer :=
  Submodule.projectionOnto_apply_eq_zero_iff P.isCompl_rootSpan_corootKer

/-- The kernel of `P.rootSpanProj` is the central kernel `P.corootKer`. -/
@[simp]
theorem ker_rootSpanProj : LinearMap.ker P.rootSpanProj = P.corootKer :=
  Submodule.ker_projectionOnto P.isCompl_rootSpan_corootKer

/-- `P.rootSpanProj` is surjective onto `P.rootSpan R`. -/
@[simp]
theorem range_rootSpanProj : LinearMap.range P.rootSpanProj = ⊤ :=
  Submodule.range_projectionOnto P.isCompl_rootSpan_corootKer

/-- Every weight differs from its root-span projection by an element of the central kernel. -/
theorem sub_coe_rootSpanProj_mem_corootKer (x : M) :
    x - (P.rootSpanProj x : M) ∈ P.corootKer := by
  rw [← rootSpanProj_eq_zero_iff, map_sub, rootSpanProj_coe, sub_self]

-- Not `@[simp]`: `coroot'` is an `abbrev` for `toLinearMap.flip ∘ coroot`, which `simp` unfolds to
-- `toLinearMap_coe_rootSpanProj_coroot` below (`simpNF`).
/-- Projecting onto the root span leaves every coroot evaluation unchanged. -/
theorem coroot'_coe_rootSpanProj (i : ι) (x : M) :
    P.coroot' i (P.rootSpanProj x : M) = P.coroot' i x := by
  have h := mem_corootKer.mp (P.sub_coe_rootSpanProj_mem_corootKer x) i
  rw [map_sub, sub_eq_zero] at h
  exact h.symm

/-- Pairing `P.rootSpanProj x` with any coroot agrees with pairing `x` with that coroot. -/
@[simp]
theorem toLinearMap_coe_rootSpanProj_coroot (i : ι) (x : M) :
    P.toLinearMap (P.rootSpanProj x : M) (P.coroot i) = P.toLinearMap x (P.coroot i) :=
  P.coroot'_coe_rootSpanProj i x

/-- The root-span projection commutes with every root reflection. -/
@[simp]
theorem coe_rootSpanProj_reflection (i : ι) (x : M) :
    (P.rootSpanProj (P.reflection i x) : M) = P.reflection i (P.rootSpanProj x : M) := by
  rw [reflection_apply, map_sub, map_smul, Submodule.coe_sub, SetLike.val_smul,
    rootSpanProj_root, reflection_apply, coroot'_coe_rootSpanProj]

/-- When two weights differ by an element of the root span, projecting onto the root span
preserves their difference. -/
theorem coe_rootSpanProj_sub_of_sub_mem {x y : M} (h : y - x ∈ P.rootSpan R) :
    ((P.rootSpanProj y - P.rootSpanProj x : P.rootSpan R) : M) = y - x := by
  rw [← map_sub, P.coe_rootSpanProj_of_mem h]

/-- Two weights whose difference lies in the root span have equal root-span projections if and
only if they are equal. -/
theorem rootSpanProj_eq_iff_of_sub_mem {x y : M} (h : y - x ∈ P.rootSpan R) :
    P.rootSpanProj x = P.rootSpanProj y ↔ x = y := by
  refine ⟨fun heq ↦ ?_, fun hxy ↦ hxy ▸ rfl⟩
  have hsub := P.coe_rootSpanProj_sub_of_sub_mem h
  rw [heq, sub_self, ZeroMemClass.coe_zero] at hsub
  exact (sub_eq_zero.mp hsub.symm).symm

end RootSpanProj

section Equiv

variable {ι ι₂ R M N M₂ N₂ : Type*} [CommRing R]
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  [AddCommGroup M₂] [Module R M₂] [AddCommGroup N₂] [Module R N₂]
  {P : RootPairing ι R M N} {Q : RootPairing ι₂ R M₂ N₂}

/-- **Equivalences of balanced root pairings commute with `rootSpanProj`.** -/
theorem Equiv.coe_rootSpanProj_weightMap [P.IsBalanced] [Q.IsBalanced] (e : P.Equiv Q) (x : M) :
    (Q.rootSpanProj (e.weightMap x) : M₂) = e.weightMap (P.rootSpanProj x : M) := by
  have hmem : e.weightMap (P.rootSpanProj x : M) ∈ Q.rootSpan R :=
    e.toHom.weightMap_mem_rootSpan (P.rootSpanProj x).property
  have hker : e.weightMap x - e.weightMap (P.rootSpanProj x : M) ∈ Q.corootKer := by
    rw [← map_sub, e.weightMap_mem_corootKer_iff]
    exact P.sub_coe_rootSpanProj_mem_corootKer x
  have hzero : Q.rootSpanProj (e.weightMap x - e.weightMap (P.rootSpanProj x : M)) = 0 :=
    Q.rootSpanProj_eq_zero_iff.mpr hker
  rw [map_sub, Q.rootSpanProj_apply_of_mem hmem, sub_eq_zero] at hzero
  exact congrArg Subtype.val hzero

/-- Automorphisms of a balanced root pairing commute with `rootSpanProj`. -/
@[simp]
theorem coe_rootSpanProj_smul [P.IsBalanced] (g : P.Aut) (x : M) :
    (P.rootSpanProj (g • x) : M) = g • (P.rootSpanProj x : M) :=
  g.coe_rootSpanProj_weightMap x

end Equiv

end RootPairing
