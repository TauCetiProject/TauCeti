/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Depth.Basic
public import Mathlib.RingTheory.Ideal.Height
import Mathlib.RingTheory.KrullDimension.Regular
import Mathlib.RingTheory.Regular.Flat
import TauCeti.Algebra.Category.ModuleCat.Ext.Basic

/-!
# Depth as the supremum of lengths of weakly regular sequences

Mathlib defines the depth `I.depth M` of a module `M` with respect to an ideal `I` through the
vanishing of `Ext (R ⧸ I) M`, and identifies it, for a finite module over a Noetherian ring with
`I M ≠ M`, with the supremum of the lengths of `M`-regular sequences in `I`. Stacks defines the
`I`-depth of a module through regular sequences, and the convenient form with no hypothesis on
`I M` uses *weakly* regular sequences, which do not ask that `M ⧸ (f₁, …, fᵣ) M` be nonzero.

This file proves that, for every finite module `M` over a Noetherian ring and every ideal `I`,
`I.depth M` is the supremum in `ℕ∞` of the lengths of weakly `M`-regular sequences in `I`, and
that the depth is infinite exactly when `I M = M`. Over a Noetherian local ring this says that
`IsLocalRing.depth M` is the supremum of the lengths of weakly `M`-regular sequences in the
maximal ideal, and that it is infinite exactly when `M = 0`.

## Main results

* `Ideal.depth_le_height`: `I.depth M` is at most the height of every prime of the support of `M`
  containing `I`.
* `Ideal.depth_lt_top`: if `I M ≠ M` then `I.depth M` is finite.
* `Ideal.depth_eq_top_iff`: `I.depth M = ⊤` if and only if `I M = M`.
* `Ideal.depth_eq_sSup_length_isWeaklyRegular`: `I.depth M` is the supremum of the lengths of
  weakly `M`-regular sequences in `I`.
* `IsLocalRing.depth_eq_top_iff`: over a Noetherian local ring, `depth M = ⊤` if and only if
  `M = 0`.
* `IsLocalRing.depth_eq_sSup_length_isWeaklyRegular`: over a Noetherian local ring, `depth M` is
  the supremum of the lengths of weakly `M`-regular sequences in the maximal ideal.

## References

* [Stacks Project, Definition 10.72.1](https://stacks.math.columbia.edu/tag/00LI)
-/

public section

universe v u

open IsLocalRing RingTheory.Sequence CategoryTheory Abelian

variable {R : Type u} [CommRing R]

/-- Every finite sequence is weakly regular on a module with at most one element. -/
theorem RingTheory.Sequence.IsWeaklyRegular.of_subsingleton {M : Type*} [AddCommGroup M]
    [Module R M] [Subsingleton M] (rs : List R) : IsWeaklyRegular M rs :=
  ⟨fun _ _ _ _ _ ↦ Subsingleton.elim _ _⟩

namespace Ideal

/-- For a finite module `M`, `I M = M` exactly when `I` and the annihilator of `M` are comaximal. -/
theorem smul_top_eq_top_iff_sup_annihilator_eq_top {M : Type*} [AddCommGroup M] [Module R M]
    [Module.Finite R M] (I : Ideal R) :
    I • (⊤ : Submodule R M) = ⊤ ↔ I ⊔ Module.annihilator R M = ⊤ := by
  refine ⟨fun hI ↦ ?_, fun h ↦ ?_⟩
  · -- Nakayama gives `r ∈ I` acting as the identity, so `1 - r` annihilates `M`.
    obtain ⟨r, hrI, hr⟩ := Submodule.exists_mem_and_smul_eq_self_of_fg_of_le_smul I ⊤
      Module.Finite.fg_top hI.ge
    refine (eq_top_iff_one _).2 <| Submodule.mem_sup.2 ⟨r, hrI, 1 - r, ?_, add_sub_cancel r 1⟩
    exact Module.mem_annihilator.2 fun m ↦ by rw [sub_smul, one_smul, hr m trivial, sub_self]
  · calc I • (⊤ : Submodule R M) = (I ⊔ Module.annihilator R M) • ⊤ := by
          rw [Submodule.sup_smul, ← Submodule.annihilator_top, Submodule.annihilator_smul,
            sup_bot_eq]
      _ = ⊤ := by rw [h, Submodule.top_smul]

variable [Small.{v} R]

/-- If `I M = M` for a finite module `M`, then `Ext (R ⧸ I) M` vanishes in every degree, so the
depth of `M` with respect to `I` is infinite. -/
theorem depth_eq_top_of_smul_top_eq_top (I : Ideal R) (M : ModuleCat.{v} R) [Module.Finite R M]
    (hI : I • (⊤ : Submodule R M) = ⊤) : I.depth M = ⊤ := by
  refine (ModuleCat.depth_eq_top_iff _ M).2 fun n ↦ Ext.subsingleton_of_annihilator_sup_eq_top ?_ n
  rwa [(Shrink.linearEquiv R (R ⧸ I)).annihilator_eq, annihilator_quotient,
    ← smul_top_eq_top_iff_sup_annihilator_eq_top]

variable [IsNoetherianRing R]

/-- Let `M` be a finite module over a Noetherian ring and `p` a prime ideal in the support of `M`
containing `I`. Then the depth of `M` with respect to `I` is at most the height of `p`: an
`M`-regular sequence in `I` stays regular on the localization `M_p`, whose dimension is at most
the height of `p`. -/
theorem depth_le_height (I : Ideal R) (M : ModuleCat.{v} R) [Module.Finite R M] (p : Ideal R)
    [p.IsPrime] (hIp : I ≤ p) (hMp : Module.annihilator R M ≤ p) : I.depth M ≤ p.height := by
  have hI : I • (⊤ : Submodule R M) ≠ ⊤ := fun h ↦ IsPrime.ne_top' <| top_le_iff.1 <|
    (smul_top_eq_top_iff_sup_annihilator_eq_top I).1 h ▸ sup_le hIp hMp
  let Rₚ := Localization.AtPrime p
  let Mₚ := LocalizedModule p.primeCompl M
  have : Nontrivial Mₚ := Module.mem_support_iff.1 <|
    (Module.mem_support_iff_of_finite (p := ⟨p, inferInstance⟩)).2 hMp
  rw [depth_eq_sSup_length_isRegular I M hI.lt_top]
  refine sSup_le ?_
  rintro _ ⟨rs, reg, mem, rfl⟩
  have regₚ := reg.toIsWeaklyRegular.isRegular_of_isLocalizedModule_of_mem Rₚ p
    (LocalizedModule.mkLinearMap p.primeCompl M) fun r hr ↦ hIp (mem r hr)
  -- Dividing `Mₚ` by the regular sequence lowers its dimension by the length of the sequence.
  have hdim := Module.supportDim_add_length_eq_supportDim_of_isRegular _ regₚ
  have : Nontrivial (Mₚ ⧸ ofList (rs.map (algebraMap R Rₚ)) • (⊤ : Submodule Rₚ Mₚ)) :=
    regₚ.quot_ofList_smul_nontrivial ⊤
  obtain ⟨e, he⟩ := WithBot.ne_bot_iff_exists.1 (Module.supportDim_ne_bot_of_nontrivial Rₚ
    (Mₚ ⧸ ofList (rs.map (algebraMap R Rₚ)) • (⊤ : Submodule Rₚ Mₚ)))
  rw [← he, List.length_map] at hdim
  refine WithBot.coe_le_coe.1 <| calc
    ((rs.length : ℕ∞) : WithBot ℕ∞) ≤ (e : WithBot ℕ∞) + rs.length := by
      exact_mod_cast le_add_self
    _ = Module.supportDim Rₚ Mₚ := hdim
    _ ≤ ringKrullDim Rₚ := Module.supportDim_le_ringKrullDim Rₚ Mₚ
    _ = p.height := IsLocalization.AtPrime.ringKrullDim_eq_height p Rₚ

/-- Let `M` be a finite module over a Noetherian ring and `I` an ideal with `I M ≠ M`. Then the
depth of `M` with respect to `I` is finite. -/
theorem depth_lt_top (I : Ideal R) (M : ModuleCat.{v} R) [Module.Finite R M]
    (hI : I • (⊤ : Submodule R M) ≠ ⊤) : I.depth M < ⊤ := by
  obtain ⟨m, hm, hle⟩ :=
    exists_le_maximal _ (mt (smul_top_eq_top_iff_sup_annihilator_eq_top I).2 hI)
  exact (depth_le_height I M m (le_sup_left.trans hle) (le_sup_right.trans hle)).trans_lt
    (height_lt_top hm.ne_top)

/-- For a finite module `M` over a Noetherian ring, the depth of `M` with respect to `I` is
infinite exactly when `I M = M`. -/
theorem depth_eq_top_iff (I : Ideal R) (M : ModuleCat.{v} R) [Module.Finite R M] :
    I.depth M = ⊤ ↔ I • (⊤ : Submodule R M) = ⊤ :=
  ⟨fun h ↦ by_contra fun hI ↦ (depth_lt_top I M hI).ne h, depth_eq_top_of_smul_top_eq_top I M⟩

/-- For a finite module `M` over a Noetherian ring and an ideal `I`, the depth of `M` with respect
to `I` is the supremum of the lengths of weakly `M`-regular sequences in `I`. Unlike
`Ideal.depth_eq_sSup_length_isRegular`, this needs no hypothesis `I M ≠ M`: when `I M = M` both
sides are `⊤`. -/
@[stacks 00LI "Stacks defines the `I`-depth of `M` by regular sequences when `I M ≠ M` and sets it
to `∞` when `I M = M`; weakly regular sequences give both cases at once."]
theorem depth_eq_sSup_length_isWeaklyRegular (I : Ideal R) (M : ModuleCat.{v} R)
    [Module.Finite R M] :
    I.depth M = sSup {(List.length rs : ℕ∞) | (rs : List R)
      (_ : IsWeaklyRegular M rs) (_ : ∀ r ∈ rs, r ∈ I)} := by
  by_cases hI : I • (⊤ : Submodule R M) = ⊤
  · -- For `r ∈ I` acting as the identity on `M`, every sequence `r, …, r` is weakly regular.
    obtain ⟨r, hrI, hr⟩ := Submodule.exists_mem_and_smul_eq_self_of_fg_of_le_smul I ⊤
      Module.Finite.fg_top hI.ge
    have hreg : IsSMulRegular M r := fun x y hxy ↦ by
      simpa only [hr x trivial, hr y trivial] using hxy
    have : Subsingleton (QuotSMulTop r M) := Submodule.Quotient.subsingleton_iff.2 <|
      eq_top_iff.2 fun m _ ↦ hr m trivial ▸ Submodule.smul_mem_pointwise_smul m r ⊤ trivial
    rw [depth_eq_top_of_smul_top_eq_top I M hI, eq_comm, ENat.eq_top_iff_forall_ge]
    intro n
    refine le_trans (by simp) (le_sSup ⟨List.replicate (n + 1) r, ?_,
      fun s hs ↦ List.eq_of_mem_replicate hs ▸ hrI, rfl⟩)
    rw [List.replicate_succ, isWeaklyRegular_cons_iff]
    exact ⟨hreg, IsWeaklyRegular.of_subsingleton _⟩
  · -- When `I M ≠ M`, a weakly regular sequence in `I` is regular.
    rw [depth_eq_sSup_length_isRegular I M (lt_top_iff_ne_top.2 hI)]
    congr 1
    ext n
    refine ⟨fun ⟨rs, reg, mem, h⟩ ↦ ⟨rs, reg.toIsWeaklyRegular, mem, h⟩,
      fun ⟨rs, reg, mem, h⟩ ↦ ⟨rs, ⟨reg, fun htop ↦ hI ?_⟩, mem, h⟩⟩
    exact top_le_iff.1 <| htop.le.trans <| Submodule.smul_mono_left <| span_le.2 mem

end Ideal

namespace IsLocalRing

variable [IsLocalRing R] [IsNoetherianRing R] [Small.{v} R]

/-- A finite module over a Noetherian local ring has infinite depth exactly when it is zero. -/
theorem depth_eq_top_iff (M : ModuleCat.{v} R) [Module.Finite R M] :
    depth M = ⊤ ↔ Subsingleton M := by
  rw [depth, Ideal.depth_eq_top_iff]
  refine ⟨fun h ↦ ?_, fun _ ↦ Subsingleton.elim _ _⟩
  by_contra hM
  rw [not_subsingleton_iff_nontrivial] at hM
  exact Submodule.top_ne_ideal_smul_of_le_jacobson_annihilator (maximalIdeal_le_jacobson _) h.symm

/-- The depth of a finite module over a Noetherian local ring is the supremum of the lengths of
weakly `M`-regular sequences in the maximal ideal. -/
theorem depth_eq_sSup_length_isWeaklyRegular (M : ModuleCat.{v} R) [Module.Finite R M] :
    depth M = sSup {(List.length rs : ℕ∞) | (rs : List R)
      (_ : IsWeaklyRegular M rs) (_ : ∀ r ∈ rs, r ∈ maximalIdeal R)} :=
  (maximalIdeal R).depth_eq_sSup_length_isWeaklyRegular M

end IsLocalRing
