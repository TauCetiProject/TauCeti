/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.Torsion.Free
public import Mathlib.LinearAlgebra.Projection
public import Mathlib.LinearAlgebra.RootSystem.BaseChange
public import TauCeti.LinearAlgebra.RootSystem.Weyl.Group
import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.LinearAlgebra.Dimension.Finrank

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
and on the coweight side to the dual statement for `P.flip`. Over a field of characteristic zero,
every root pairing with finitely many roots is balanced (`RootPairing.instIsBalancedOfCharZero`),
with no crystallographic or anisotropy assumption: the Weyl group acts on `P.rootSpan R` through a
finite quotient, and averaging over that quotient kills every root (since each reflection negates
its own root) while fixing `P.corootKer` pointwise, forcing `Disjoint (P.rootSpan R) P.corootKer`.

When `P` is balanced, the direct-sum decomposition `M = P.rootSpan R ⊕ P.corootKer` yields a linear
projection `P.rootSpanProj : M →ₗ[R] P.rootSpan R` along `P.corootKer`. Subtracting
`P.rootSpanProj x` from `x` changes `x` only by an element of `P.corootKer`, so `P.rootSpanProj`
preserves every coroot evaluation and commutes with root reflections and with equivalences of
balanced root pairings.

## Main definitions

* `RootPairing.rootSpanProj`: the linear projection `M →ₗ[R] P.rootSpan R` along `P.corootKer` for
  a balanced root pairing.

## Main results

* `RootPairing.isCompl_rootSpan_corootKer` and `RootPairing.isBalanced_iff_isCompl`: a root pairing
  is balanced if and only if `P.rootSpan R` complements `P.corootKer` and `P.corootSpan R`
  complements `P.flip.corootKer`.
* `RootPairing.disjoint_rootSpan_corootKer` and `RootPairing.instIsBalancedOfCharZero`: every
  finite root pairing over a field of characteristic zero is balanced.
* `RootPairing.coroot'_coe_rootSpanProj`: `P.rootSpanProj` preserves all coroot evaluations.
* `RootPairing.weylGroupToPerm_injective_of_isBalanced`: in a balanced root pairing, the Weyl group
  acts faithfully on root indices.
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

private noncomputable def weylQuotientAct
    (q : P.weylGroup ⧸ P.weylGroupToPerm.ker) (x : P.rootSpan R) : M :=
  Quotient.liftOn' q (fun w ↦ w • (x : M)) fun w₁ w₂ h ↦ by
    have hk : w₁⁻¹ * w₂ ∈ P.weylGroupToPerm.ker := QuotientGroup.leftRel_apply.mp h
    calc
      w₁ • (x : M) = w₁ • ((w₁⁻¹ * w₂) • (x : M)) := by
        rw [smul_eq_self_of_mem_ker_weylGroupToPerm P hk x.property]
      _ = w₂ • (x : M) := by rw [← mul_smul, mul_inv_cancel_left]

private lemma weylQuotientAct_mk (w : P.weylGroup) (x : P.rootSpan R) :
    weylQuotientAct P (QuotientGroup.mk w) x = w • (x : M) :=
  rfl

private lemma sum_weylQuotientAct_eq_zero
    [Fintype (P.weylGroup ⧸ P.weylGroupToPerm.ker)] [HasUniqueDiv M]
    {x : M} (hx : x ∈ P.rootSpan R) :
    ∑ q : P.weylGroup ⧸ P.weylGroupToPerm.ker, weylQuotientAct P q ⟨x, hx⟩ = 0 := by
  let G := P.weylGroup ⧸ P.weylGroupToPerm.ker
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨i, rfl⟩ := hy
    let s : G := QuotientGroup.mk (weylGroup.ofIdx P i)
    let S : M := ∑ q : G, weylQuotientAct P q ⟨P.root i, subset_span (mem_range_self i)⟩
    have hneg : S = -S := by
      calc
        S = ∑ q : G, weylQuotientAct P (q * s) ⟨P.root i, subset_span (mem_range_self i)⟩ :=
          (Fintype.sum_equiv (_root_.Equiv.mulRight s) _ _ fun _ ↦ rfl).symm
        _ = ∑ q : G, -weylQuotientAct P q ⟨P.root i, subset_span (mem_range_self i)⟩ := by
          refine Finset.sum_congr rfl fun q _ ↦ ?_
          induction q using QuotientGroup.induction_on with | _ w => ?_
          rw [← QuotientGroup.mk_mul, weylQuotientAct_mk, weylQuotientAct_mk, mul_smul,
            weylGroup.ofIdx_smul, Equiv.reflection_smul, reflection_apply_self, smul_neg]
        _ = -S := Finset.sum_neg_distrib _
    have htwo : 2 • S = 0 := by
      rw [two_nsmul]
      exact add_eq_zero_iff_eq_neg.mpr hneg
    exact (nsmul_right_inj (M := M) (by decide : 2 ≠ 0)).mp (by simpa only [nsmul_zero] using htwo)
  | zero =>
    refine Finset.sum_eq_zero fun q _ ↦ ?_
    induction q using QuotientGroup.induction_on with | _ w => exact smul_zero w
  | add y z hy hz ihy ihz =>
    have hadd (q : G) : weylQuotientAct P q ⟨y + z, add_mem hy hz⟩ =
        weylQuotientAct P q ⟨y, hy⟩ + weylQuotientAct P q ⟨z, hz⟩ := by
      induction q using QuotientGroup.induction_on with | _ w => exact smul_add w y z
    simp only [hadd, Finset.sum_add_distrib, ihy, ihz, add_zero]
  | smul c y hy ihy =>
    have hsmul (q : G) : weylQuotientAct P q ⟨c • y, smul_mem _ c hy⟩ =
        c • weylQuotientAct P q ⟨y, hy⟩ := by
      induction q using QuotientGroup.induction_on with | _ w => exact smul_comm w c y
    simp only [hsmul, ← Finset.smul_sum, ihy, smul_zero]

/-- For finitely many roots and a torsion-free additive weight group, the root span and the
central kernel intersect trivially. -/
theorem disjoint_rootSpan_corootKer [Finite ι] [HasUniqueDiv M] :
    Disjoint (P.rootSpan R) P.corootKer := by
  let G := P.weylGroup ⧸ P.weylGroupToPerm.ker
  have : Finite G :=
    Finite.of_equiv _ (QuotientGroup.quotientKerEquivRange P.weylGroupToPerm).toEquiv.symm
  let _ : Fintype G := Fintype.ofFinite G
  rw [Submodule.disjoint_def]
  intro x hx₁ hx₂
  have hzero : ∑ q : G, weylQuotientAct P q ⟨x, hx₁⟩ = 0 := P.sum_weylQuotientAct_eq_zero hx₁
  have hfix (q : G) : weylQuotientAct P q ⟨x, hx₁⟩ = x := by
    induction q using QuotientGroup.induction_on with | _ w =>
      exact weylGroup_smul_of_mem_corootKer hx₂ w
  simp only [hfix, Finset.sum_const, Finset.card_univ] at hzero
  exact (nsmul_right_inj (M := M) Fintype.card_ne_zero).mp (by simpa only [nsmul_zero] using hzero)

end IsBalanced

section CharZero

private lemma finrank_add_finrank_corootKer_eq {ι K M N : Type*} [Field K]
    [AddCommGroup M] [Module K M] [AddCommGroup N] [Module K N]
    (Q : RootPairing ι K M N) :
    finrank K (Q.corootSpan K) + finrank K Q.corootKer = finrank K M := by
  have : IsReflexive K M := .of_isPerfPair Q.toLinearMap
  have : IsReflexive K N := .of_isPerfPair Q.flip.toLinearMap
  have hker : finrank K Q.corootKer = finrank K (Q.corootSpan K).dualAnnihilator := by
    rw [corootKer_def, ← Q.corootSpan_dualAnnihilator_map_eq_iInf_ker_coroot']
    exact LinearEquiv.finrank_map_eq _ _
  rw [hker, Q.toPerfPair.finrank_eq, Subspace.dual_finrank_eq,
    Subspace.finrank_add_finrank_dualAnnihilator_eq]

variable {ι K M N : Type*} [Finite ι] [Field K] [CharZero K]
  [AddCommGroup M] [Module K M] [AddCommGroup N] [Module K N]

private lemma finrank_rootSpan_le_finrank_corootSpan (Q : RootPairing ι K M N) :
    finrank K (Q.rootSpan K) ≤ finrank K (Q.corootSpan K) := by
  have : HasUniqueDiv M := .of_isTorsionFree K M
  have : IsReflexive K M := .of_isPerfPair Q.toLinearMap
  have hsup := Submodule.finrank_sup_add_finrank_inf_eq (Q.rootSpan K) Q.corootKer
  rw [Q.disjoint_rootSpan_corootKer.eq_bot, finrank_bot, add_zero] at hsup
  have hle : finrank K (Q.rootSpan K) + finrank K Q.corootKer ≤ finrank K M :=
    hsup ▸ Submodule.finrank_le _
  have hker := finrank_add_finrank_corootKer_eq Q
  omega

private lemma isCompl_rootSpan_corootKer_of_charZero (Q : RootPairing ι K M N) :
    IsCompl (Q.rootSpan K) Q.corootKer := by
  have : HasUniqueDiv M := .of_isTorsionFree K M
  have : IsReflexive K M := .of_isPerfPair Q.toLinearMap
  have hrank : finrank K (Q.rootSpan K) = finrank K (Q.corootSpan K) :=
    le_antisymm (finrank_rootSpan_le_finrank_corootSpan Q)
      (finrank_rootSpan_le_finrank_corootSpan Q.flip)
  refine (Submodule.isCompl_iff_disjoint _ _ ?_).mpr Q.disjoint_rootSpan_corootKer
  rw [hrank, finrank_add_finrank_corootKer_eq]

/-- **Every finite root pairing over a field of characteristic zero is balanced.** Neither
crystallographicity nor nondegeneracy of the trace root form is needed. -/
instance instIsBalancedOfCharZero (Q : RootPairing ι K M N) : Q.IsBalanced :=
  Q.isBalanced_iff_isCompl.mpr
    ⟨isCompl_rootSpan_corootKer_of_charZero Q, isCompl_rootSpan_corootKer_of_charZero Q.flip⟩

end CharZero

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

/-- In a balanced root pairing, the permutation action of the Weyl group on root indices is
faithful. -/
theorem weylGroupToPerm_injective_of_isBalanced : Function.Injective P.weylGroupToPerm := by
  rw [← MonoidHom.ker_eq_bot_iff, Subgroup.eq_bot_iff_forall]
  intro w hw
  refine weylGroup.eq_one_of_smul_eq_self fun x ↦ ?_
  have h1 : w • (P.rootSpanProj x : M) = (P.rootSpanProj x : M) :=
    smul_eq_self_of_mem_ker_weylGroupToPerm P hw (P.rootSpanProj x).property
  have h2 : w • (x - (P.rootSpanProj x : M)) = x - (P.rootSpanProj x : M) :=
    weylGroup_smul_of_mem_corootKer (P.sub_coe_rootSpanProj_mem_corootKer x) w
  have hsum := congrArg₂ (· + ·) h1 h2
  rwa [← smul_add, add_sub_cancel] at hsum

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
