/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Projection
public import Mathlib.LinearAlgebra.RootSystem.Base
public import Mathlib.LinearAlgebra.RootSystem.Finite.Nondegenerate
import TauCeti.Algebra.Group.Submonoid.Closure
import TauCeti.LinearAlgebra.LinearIndependent.Basic
import TauCeti.LinearAlgebra.RootSystem.Weyl.Group

/-!
# Balanced root pairings, coroot-kernel projection, and base restriction

In a balanced root pairing `P : RootPairing ι R M N`, `P.rootSpan R` and the common coroot kernel
`⨅ i, LinearMap.ker (P.coroot' i)` are complementary
(`RootPairing.isCompl_rootSpan_iInf_ker_coroot'`), giving a `P.Aut`-equivariant linear projection
`RootPairing.rootSpanProj : M →ₗ[R] P.rootSpan R`. It also upgrades balancedness to `[Finite ι]`
and provides pullback and scalar restriction of bases
(`RootPairing.Base.comapOfInjective`, `RootPairing.Base.restrictScalars'`).

## Main definitions

* `RootPairing.rootSpanProj`: linear projection `M →ₗ[R] P.rootSpan R` along the coroot kernel.
* `RootPairing.Base.comapOfInjective` and `RootPairing.Base.restrictScalars'`: pullback of a base
  along injective `R`-linear maps and restriction along `RootPairing.restrictScalars'`.

## Main results

* `RootPairing.instIsBalancedOfIsCrystallographic`: finite crystallographic pairings over
  characteristic-zero fields are balanced.
* `RootPairing.isCompl_rootSpan_iInf_ker_coroot'`, `RootPairing.coroot'_coe_rootSpanProj`,
  `RootPairing.coe_rootSpanProj_smul`, and `RootPairing.restrictScalars'_coroot'_rootSpanProj`:
  complementarity, coroot preservation, and `P.Aut`-equivariance of `rootSpanProj`.

## References

* M. Demazure, A. Grothendieck (eds.), *Schémas en groupes III* (SGA 3), Exposé XXI, §§6.1, 6.7.
* J. S. Milne, *Algebraic Groups*, Cambridge Studies in Advanced Mathematics 170, Appendix C, C.53.
-/

public section

open Function Set

namespace RootPairing

section Balanced

variable {ι R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M]
  [AddCommGroup N] [Module R N] (P : RootPairing ι R M N)

/-- Every finite crystallographic root pairing over a characteristic-zero field is balanced. -/
instance instIsBalancedOfIsCrystallographic {K : Type*} [Field K] [CharZero K]
    [Module K M] [Module K N] [Finite ι] (Q : RootPairing ι K M N) [Q.IsCrystallographic] :
    Q.IsBalanced := by cases nonempty_fintype ι; infer_instance

variable [P.IsBalanced]

/-- **In a balanced root pairing, `P.rootSpan R` and the common coroot kernel
`⨅ i, LinearMap.ker (P.coroot' i)` are complementary submodules of `M`.** -/
theorem isCompl_rootSpan_iInf_ker_coroot' :
    IsCompl (P.rootSpan R) (⨅ i, LinearMap.ker (P.coroot' i)) :=
  P.corootSpan_dualAnnihilator_map_eq_iInf_ker_coroot' ▸ IsBalanced.isPerfectCompl.isCompl_left

/-- **Linear projection onto `P.rootSpan R` along the common coroot kernel
`⨅ i, LinearMap.ker (P.coroot' i)`.** -/
noncomputable def rootSpanProj : M →ₗ[R] P.rootSpan R :=
  (P.rootSpan R).projectionOnto (⨅ i, LinearMap.ker (P.coroot' i))
    P.isCompl_rootSpan_iInf_ker_coroot'

/-- `P.rootSpanProj` acts as the identity on `P.rootSpan R`. -/
@[simp] theorem rootSpanProj_apply_of_mem (x : P.rootSpan R) : P.rootSpanProj x = x :=
  Submodule.projectionOnto_apply_left _ x

/-- The kernel of `P.rootSpanProj` is `⨅ i, LinearMap.ker (P.coroot' i)`. -/
@[simp] theorem ker_rootSpanProj :
    LinearMap.ker P.rootSpanProj = ⨅ i, LinearMap.ker (P.coroot' i) :=
  Submodule.ker_projectionOnto _

/-- `P.rootSpanProj x = 0` if and only if every coroot functional vanishes on `x`. -/
@[simp] theorem rootSpanProj_eq_zero_iff {x : M} :
    P.rootSpanProj x = 0 ↔ ∀ i, P.coroot' i x = 0 := by
  rw [rootSpanProj, Submodule.projectionOnto_apply_eq_zero_iff, Submodule.mem_iInf]
  exact forall_congr' fun _ ↦ LinearMap.mem_ker

/-- Projecting to `P.rootSpan R` along the common coroot kernel preserves pairing with every
coroot. -/
@[simp] theorem toLinearMap_coe_rootSpanProj_coroot (x : M) (i : ι) :
    P.toLinearMap (P.rootSpanProj x : M) (P.coroot i) = P.toLinearMap x (P.coroot i) := by
  have hi : P.coroot' i (x - (P.rootSpanProj x : M)) = 0 :=
    LinearMap.mem_ker.mp ((Submodule.mem_iInf _).mp
      (Submodule.sub_projection_mem P.isCompl_rootSpan_iInf_ker_coroot' x) i)
  rwa [map_sub, sub_eq_zero, eq_comm] at hi

-- Not `@[simp]`: `coroot'` is an `abbrev` for `toLinearMap.flip (coroot i)`, so
-- `toLinearMap_coe_rootSpanProj_coroot` is the `simp`-normal form.
/-- Projecting to `P.rootSpan R` along the common coroot kernel preserves every `P.coroot' i`. -/
theorem coroot'_coe_rootSpanProj (i : ι) (x : M) :
    P.coroot' i (P.rootSpanProj x : M) = P.coroot' i x :=
  P.toLinearMap_coe_rootSpanProj_coroot x i

/-- `P.rootSpanProj` is equivariant for the weight action of `P.Aut`. -/
theorem coe_rootSpanProj_smul (g : P.Aut) (x : M) :
    (P.rootSpanProj (g • x) : M) = g • (P.rootSpanProj x : M) := by
  have hle : P.rootSpan R ≤ (P.rootSpan R).comap g.weightEquiv.toLinearMap :=
    Submodule.span_le.mpr <| range_subset_iff.mpr fun j ↦ by
      simp only [SetLike.mem_coe, Submodule.mem_comap, LinearEquiv.coe_coe,
        Equiv.weightEquiv_apply, Hom.root_weightMap_apply]
      exact Submodule.subset_span (mem_range_self _)
  have hsub_ker : (P.rootSpanProj (g • x) : M) - g • (P.rootSpanProj x : M) ∈
      ⨅ i, LinearMap.ker (P.coroot' i) :=
    (Submodule.mem_iInf _).mpr fun i ↦ LinearMap.mem_ker.mpr <| by
      rw [map_sub, P.coroot'_coe_rootSpanProj, coroot'_smul, coroot'_smul,
        P.coroot'_coe_rootSpanProj, sub_self]
  exact sub_eq_zero.mp <| Submodule.disjoint_def.mp P.isCompl_rootSpan_iInf_ker_coroot'.disjoint _
    (sub_mem (P.rootSpanProj (g • x)).2 (hle (P.rootSpanProj x).2)) hsub_ker

end Balanced

section RestrictScalars

variable {ι K M N : Type*} [Field K] [AddCommGroup M] [Module K M]
  [AddCommGroup N] [Module K N] (P : RootPairing ι K M N) [P.IsBalanced]

/-- Evaluating a coroot functional of `P.restrictScalars' K` on `P.rootSpanProj x` recovers
`P.coroot' i x`. -/
theorem restrictScalars'_coroot'_rootSpanProj (i : ι) (x : M) :
    (P.restrictScalars' K).coroot' i (P.rootSpanProj x) = P.coroot' i x := by
  have h := P.restrictScalars_toLinearMap_apply_apply K (P.rootSpanProj x)
    ((P.restrictScalars' K).coroot i)
  rw [Algebra.algebraMap_self, RingHom.id_apply, P.restrictScalars_coe_coroot] at h
  exact h.trans (P.coroot'_coe_rootSpanProj i x)

end RestrictScalars

section BaseComap

variable {ι R S M₀ N₀ M N : Type*} [CommRing R] [CommRing S] [Algebra R S] [FaithfulSMul R S]
  [AddCommGroup M₀] [Module R M₀] [AddCommGroup N₀] [Module R N₀]
  [AddCommGroup M] [Module S M] [Module R M] [IsScalarTower R S M]
  [AddCommGroup N] [Module S N] [Module R N] [IsScalarTower R S N]

private theorem mem_closure_or_neg_mem_of_injective {s : Set ι} {v₀ : ι → M₀} {v : ι → M}
    {i : ι} (hv : v i ∈ AddSubmonoid.closure (v '' s) ∨ -v i ∈ AddSubmonoid.closure (v '' s))
    (f : M₀ →+ M) (hf : Injective f) (hcomp : ∀ j, f (v₀ j) = v j) :
    v₀ i ∈ AddSubmonoid.closure (v₀ '' s) ∨
      -v₀ i ∈ AddSubmonoid.closure (v₀ '' s) := by
  have himg : v '' s = f '' (v₀ '' s) := by
    rw [← image_comp]; exact congrArg (· '' s) (funext hcomp).symm
  rwa [himg, ← hcomp i, ← map_neg, f.mem_closure_image_iff hf, f.mem_closure_image_iff hf] at hv

variable {P₀ : RootPairing ι R M₀ N₀} {P : RootPairing ι S M N} (b : P.Base)
  (fM : M₀ →ₗ[R] M) (fN : N₀ →ₗ[R] N) (hfM : Injective fM) (hfN : Injective fN)
  (hroot : ∀ i, fM (P₀.root i) = P.root i) (hcoroot : ∀ i, fN (P₀.coroot i) = P.coroot i)

/-- **Pullback of a base `b : P.Base`** along injective `R`-linear maps `fM : M₀ →ₗ[R] M` and
`fN : N₀ →ₗ[R] N` over a faithful `R`-algebra `S` compatible with roots and coroots. -/
noncomputable def Base.comapOfInjective : P₀.Base where
  support := b.support
  linearIndepOn_root :=
    (((funext hroot : fM ∘ P₀.root = P.root).symm ▸
      b.linearIndepOn_root).restrict_scalars' R).of_comp fM
  linearIndepOn_coroot :=
    (((funext hcoroot : fN ∘ P₀.coroot = P.coroot).symm ▸
      b.linearIndepOn_coroot).restrict_scalars' R).of_comp fN
  root_mem_or_neg_mem i :=
    mem_closure_or_neg_mem_of_injective (b.root_mem_or_neg_mem i) fM.toAddMonoidHom hfM hroot
  coroot_mem_or_neg_mem i :=
    mem_closure_or_neg_mem_of_injective (b.coroot_mem_or_neg_mem i) fN.toAddMonoidHom hfN hcoroot

/-- `Base.comapOfInjective` leaves `support` unchanged. -/
@[simp] theorem Base.support_comapOfInjective :
    (b.comapOfInjective fM fN hfM hfN hroot hcoroot).support = b.support := (rfl)

end BaseComap

section RestrictScalarsBase

variable {ι L M N : Type*} [Field L] [AddCommGroup M] [Module L M] [AddCommGroup N] [Module L N]
  {P : RootPairing ι L M N} (b : P.Base) (K : Type*) [Field K] [Algebra K L]
  [Module K M] [Module K N] [IsScalarTower K L M] [IsScalarTower K L N]
  [P.IsBalanced] [P.IsValuedIn K]

/-- **Restriction of scalars of a base** along `RootPairing.restrictScalars'`, keeping the same
simple indices `b.support`. -/
noncomputable def Base.restrictScalars' : (P.restrictScalars' K).Base :=
  b.comapOfInjective (Submodule.span K (range P.root)).subtype
    (Submodule.span K (range P.coroot)).subtype Subtype.val_injective Subtype.val_injective
    (P.restrictScalars_coe_root K) (P.restrictScalars_coe_coroot K)

/-- `Base.restrictScalars'` leaves `support` unchanged. -/
@[simp] theorem Base.support_restrictScalars' : (b.restrictScalars' K).support = b.support := (rfl)

end RestrictScalarsBase

end RootPairing
