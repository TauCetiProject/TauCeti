/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Group.Quotient
public import Mathlib.Analysis.Normed.Operator.Basic
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Quotient
import TauCeti.Analysis.Normed.Operator.NormedAddGroupHom

/-!
# Norm estimates on quotient modules

Descending a continuous semilinear map through a submodule contained in its kernel preserves its
operator norm. Equivalently, precomposition with the quotient projection preserves operator
norms. These facts apply to seminormed spaces and arbitrary submodules, and supply the metric
part of the duality between a quotient and the annihilator of its defining submodule.
The quotient projection is moreover a metric quotient map: it has norm at most one and lifts
every vector of norm less than `r` to a vector of norm less than `r`.

The quotient module also inherits a contractive action of a possibly noncommutative
seminormed ring. In particular, this applies to quotients of a normed ring by left ideals.

The estimates reuse Mathlib's quotient norm and quotient lift for bounded additive homomorphisms.
-/

public section

namespace Submodule

variable {𝕜 𝕜₂ E F : Type*} [NontriviallyNormedField 𝕜] [NontriviallyNormedField 𝕜₂]
  [SeminormedAddCommGroup E] [NormedSpace 𝕜 E]
  [SeminormedAddCommGroup F] [NormedSpace 𝕜₂ F]
  {σ : 𝕜 →+* 𝕜₂} [RingHomIsometric σ]

/-- Descending through a quotient does not increase the operator norm. -/
theorem norm_liftQL_le (S : Submodule 𝕜 E) (f : E →SL[σ] F) (h : S ≤ f.ker) :
    ‖S.liftQL f h‖ ≤ ‖f‖ := by
  let g := f.toLinearMap.toAddMonoidHom.mkNormedAddGroupHom ‖f‖ f.le_opNorm
  have hg : ∀ x ∈ S.toAddSubgroup, g x = 0 := fun x hx ↦ h hx
  have hnorm := f.norm_eq_normedAddGroupHom g (fun _ ↦ rfl)
  calc
    ‖S.liftQL f h‖ = ‖NormedAddGroupHom.lift S.toAddSubgroup g hg‖ := by
      apply ContinuousLinearMap.norm_eq_normedAddGroupHom
      intro x
      obtain ⟨x, rfl⟩ := S.mkQ_surjective x
      -- Both quotient lifts evaluate to the original map on representatives.
      rfl
    _ ≤ ‖g‖ := NormedAddGroupHom.norm_lift_le _ _ _
    _ = ‖f‖ := hnorm.symm

/-- Precomposition with the quotient projection preserves the operator norm. -/
@[simp]
theorem norm_comp_mkQL (S : Submodule 𝕜 E) (f : E ⧸ S →SL[σ] F) :
    ‖f.comp S.mkQL‖ = ‖f‖ := by
  apply le_antisymm
  · apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg f)
    intro x
    exact (f.le_opNorm (S.mkQ x)).trans
      (mul_le_mul_of_nonneg_left (Submodule.Quotient.norm_mk_le S x) (norm_nonneg f))
  · have h : S ≤ (f.comp S.mkQL).ker := by
      intro x hx
      simp [(Submodule.Quotient.mk_eq_zero S).mpr hx]
    have heq : S.liftQL (f.comp S.mkQL) h = f := by
      ext x
      obtain ⟨x, rfl⟩ := S.mkQ_surjective x
      simp
    simpa only [heq] using S.norm_liftQL_le (f.comp S.mkQL) h

/-- Descending through a quotient preserves the operator norm. -/
@[simp]
theorem norm_liftQL (S : Submodule 𝕜 E) (f : E →SL[σ] F) (h : S ≤ f.ker) :
    ‖S.liftQL f h‖ = ‖f‖ := by
  have heq : (S.liftQL f h).comp S.mkQL = f := by ext x; simp
  rw [← S.norm_comp_mkQL (S.liftQL f h), heq]

/-- The quotient projection has operator norm at most one. -/
theorem norm_mkQL_le (S : Submodule 𝕜 E) : ‖S.mkQL‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun x ↦ by
    simpa using Submodule.Quotient.norm_mk_le S x

/-- The quotient projection lifts every vector of norm less than `r` to a vector of norm less
than `r`. With `Submodule.norm_mkQL_le`, this says that it is a metric quotient map. -/
theorem ball_subset_image_mkQL_ball (S : Submodule 𝕜 E) (r : ℝ) :
    Metric.ball (0 : E ⧸ S) r ⊆ S.mkQL '' Metric.ball 0 r := by
  intro x hx
  have hx' : ‖x‖ < r := mem_ball_zero_iff.1 hx
  obtain ⟨m, rfl, hm⟩ := Submodule.Quotient.norm_mk_lt x (sub_pos.2 hx')
  exact ⟨m, mem_ball_zero_iff.2 (by linarith), by simp⟩

end Submodule

namespace Submodule.Quotient

variable {R E : Type*} [SeminormedRing R] [SeminormedAddCommGroup E]
  [Module R E] [IsBoundedSMul R E]

/-- The quotient action of a seminormed ring is contractive whenever the original action is.
The ring need not be commutative, and the submodule need not be closed. -/
instance isBoundedSMul (S : Submodule R E) : IsBoundedSMul R (E ⧸ S) :=
  .of_norm_smul_le fun r x => by
    have hbound (y : E) :
        ‖r • (Submodule.Quotient.mk y : E ⧸ S)‖ ≤ ‖r‖ * ‖y‖ :=
      (norm_mk_le S (r • y)).trans (norm_smul_le r y)
    by_cases hr : ‖r‖ = 0
    · obtain ⟨y, rfl⟩ := S.mkQ_surjective x
      simpa only [Submodule.mkQ_apply, hr, zero_mul] using hbound y
    · have hrpos : 0 < ‖r‖ := lt_of_le_of_ne (norm_nonneg r) (Ne.symm hr)
      apply (div_le_iff₀' hrpos).mp
      apply QuotientAddGroup.le_norm_iff.mpr
      intro y hy
      exact (div_le_iff₀' hrpos).mpr (hy ▸ hbound y)

end Submodule.Quotient
