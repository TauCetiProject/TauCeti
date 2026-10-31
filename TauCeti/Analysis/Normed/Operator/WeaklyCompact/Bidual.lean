/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Normed.Operator.WeaklyCompact.Basic

/-!
# Norm-controlled bidual factorization

For a weakly compact operator `T : E →L[𝕜] F`, Gantmacher's criterion places `T**` in the
canonical image of `F`. Here we obtain the unique representing vector in `F` and its uniform
norm bound `‖y‖ ≤ ‖T‖ * ‖Φ‖`, retaining the actual transpose pairing. Neither space needs to
be complete or reflexive.

Hahn–Banach then represents a functional on a subspace of `E*`, after composition with `T*`,
by evaluation at a vector of `F`. Its norm is controlled by the same constant that bounds the
original functional. For compact bonding maps this is the factorization used to represent
functionals on projective limits of dual Banach spaces in the next original Banach stage.
The statement allows arbitrary subspaces, not only closed ones.

The proofs use the native bidual isometry `NormedSpace.inclusionInDoubleDualLi`,
`ContinuousLinearMap.isWeaklyCompact_iff_range_subset`, and
`Module.Dual.exists_continuous_extension_of_le_seminorm`.

## References

* R. E. Megginson, *An Introduction to Banach Space Theory*, §3.5.
* H. Komatsu, *Projective and injective limits of weakly compact sequences of locally convex
  spaces*, J. Math. Soc. Japan 19 (1967), 366–383.
-/

public section

open NormedSpace
open scoped NNReal

namespace ContinuousLinearMap.IsWeaklyCompact

variable {𝕜 E F : Type*} [RCLike 𝕜]
  [SeminormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {T : E →L[𝕜] F}

/-- A bidual vector pushed through a weakly compact operator is evaluation at a unique vector
of the original target. Its norm is bounded by the operator norm times the bidual norm. -/
theorem existsUnique_norm_le_forall_apply_eq (hT : T.IsWeaklyCompact)
    (Φ : StrongDual 𝕜 (StrongDual 𝕜 E)) :
    ∃! y : F, ‖y‖ ≤ ‖T‖ * ‖Φ‖ ∧ ∀ f : StrongDual 𝕜 F, f y = Φ (f.comp T) := by
  obtain ⟨y, hy⟩ := isWeaklyCompact_iff_range_subset.1 hT ⟨Φ, rfl⟩
  have hpair (f : StrongDual 𝕜 F) : f y = Φ (f.comp T) :=
    congrArg (fun Ψ ↦ Ψ f) hy
  refine ⟨y, ⟨norm_le_dual_bound 𝕜 y (by positivity) fun f ↦ ?_, hpair⟩, ?_⟩
  · rw [hpair]
    calc
      ‖Φ (f.comp T)‖ ≤ ‖Φ‖ * ‖f.comp T‖ := Φ.le_opNorm _
      _ ≤ ‖Φ‖ * (‖f‖ * ‖T‖) :=
        mul_le_mul_of_nonneg_left (f.opNorm_comp_le T) (norm_nonneg Φ)
      _ = (‖T‖ * ‖Φ‖) * ‖f‖ := by ring
  · intro z hz
    apply (inclusionInDoubleDualLi 𝕜 (E := F)).injective
    -- The native bidual isometry has the canonical inclusion as its underlying map.
    exact ContinuousLinearMap.ext fun f ↦ (hz.2 f).trans (hpair f).symm

/-- Hahn–Banach and weak compactness represent a dominated functional on a subspace of `E*`,
after composition with `T*`, by evaluation at a vector in `F`. The bound is uniform in the
functional and requires no closedness of the subspace. -/
theorem exists_norm_le_forall_apply_eq (hT : T.IsWeaklyCompact)
    (p : Submodule 𝕜 (StrongDual 𝕜 E)) (φ : p →ₗ[𝕜] 𝕜) (C : ℝ≥0)
    (hφ : ∀ f : p, ‖φ f‖ ≤ C * ‖(f : StrongDual 𝕜 E)‖) :
    ∃ y : F, ‖y‖ ≤ ‖T‖ * C ∧
      ∀ (f : StrongDual 𝕜 F) (hf : f.comp T ∈ p), f y = φ ⟨f.comp T, hf⟩ := by
  obtain ⟨Φ, hΦ, hbound⟩ := Module.Dual.exists_continuous_extension_of_le_seminorm p φ
    (show Continuous (C • normSeminorm 𝕜 (StrongDual 𝕜 E)) from
      continuous_norm.const_smul C) hφ
  have hnorm : ‖Φ‖ ≤ C := Φ.opNorm_le_bound C.coe_nonneg hbound
  obtain ⟨y, ⟨hy, hpair⟩, -⟩ := hT.existsUnique_norm_le_forall_apply_eq Φ
  refine ⟨y, hy.trans (mul_le_mul_of_nonneg_left hnorm (norm_nonneg _)), fun f hf ↦ ?_⟩
  exact (hpair f).trans (hΦ ⟨f.comp T, hf⟩)

end ContinuousLinearMap.IsWeaklyCompact
