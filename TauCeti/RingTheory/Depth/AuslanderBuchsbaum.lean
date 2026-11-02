/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Abelian.Projective.Dimension
public import Mathlib.Algebra.Category.ModuleCat.Projective
public import TauCeti.RingTheory.Depth.Basic
import Mathlib.RingTheory.LocalRing.Module
import Mathlib.RingTheory.KrullDimension.Regular
import TauCeti.Algebra.Category.ModuleCat.Projective.Dimension
import TauCeti.Data.ENat.Basic
import TauCeti.RingTheory.Depth.WeaklyRegular
import TauCeti.RingTheory.LocalRing.Module

/-!
# The Auslander–Buchsbaum formula

Let `M` be a nonzero finite module of finite projective dimension over a Noetherian local ring
`R`. The **Auslander–Buchsbaum formula** states
`projectiveDimension M + depth M = depth R`.

Applied to the residue field `κ = R ⧸ 𝔪`, whose depth is zero, it shows that if `κ` has finite
projective dimension, then that dimension is `depth R`, hence at most `dim R`. This is the
upper bound in Serre's characterization of regular local rings by finite global dimension.

## Main results

* `ModuleCat.projectiveDimension_add_depth_eq_depth`: the Auslander–Buchsbaum formula
  (Stacks, Proposition 10.111.1 (090V)).
* `IsLocalRing.projectiveDimension_quotient_maximalIdeal_eq_depth`: a residue field of finite
  projective dimension has projective dimension `depth R`.
* `IsLocalRing.projectiveDimension_quotient_maximalIdeal_le_ringKrullDim`: a residue field of
  finite projective dimension has projective dimension at most `dim R`
  (Stacks, Lemma 10.110.4 (00OB)).

## Proof

Induction on `p = projectiveDimension M`. If `p = 0`, then `M` is projective, hence free, and a
nonzero finite free module has the depth of `R`. If `p > 0`, choose a minimal free presentation
`0 → K → F → M → 0`, with `K ⊆ 𝔪 F`; then `K` has projective dimension `p - 1`, so
`depth K + (p - 1) = depth R` by induction. The depth inequalities for short exact sequences give
`depth K - 1 ≤ depth M`. For the reverse inequality `depth M + 1 ≤ depth K`:

* if `p ≥ 2`, then `depth K < depth R = depth F`, and the depth inequalities suffice;
* if `p = 1`, then `K` is free, and the inclusion `K → F` has image in `𝔪 F`, so it induces zero
  on `Ext (R ⧸ 𝔪) - n`; the long exact sequence then shows that every connecting map
  `Ext (R ⧸ 𝔪) M n → Ext (R ⧸ 𝔪) K (n + 1)` is surjective.

## References

* [Stacks Project, Proposition 10.111.1](https://stacks.math.columbia.edu/tag/090V).
* [Stacks Project, Lemma 10.110.4](https://stacks.math.columbia.edu/tag/00OB).
* W. Bruns, J. Herzog, *Cohen–Macaulay rings*, Theorem 1.3.3.
-/

public section

universe v u

open CategoryTheory Abelian IsLocalRing
open scoped TensorProduct

namespace IsLocalRing

variable {R : Type u} [CommRing R] [IsLocalRing R] [Small.{v} R]

variable [IsNoetherianRing R]

/-- The Auslander–Buchsbaum formula for a module of projective dimension `p : ℕ`, by induction
on `p`. -/
private theorem depth_add_eq_of_projectiveDimension_eq (p : ℕ) (M : Type v) [AddCommGroup M]
    [Module R M] [Module.Finite R M] [Nontrivial M]
    (hp : projectiveDimension (ModuleCat.of R M) = p) :
    depth (ModuleCat.of R M) + p = depth (ModuleCat.of R R) := by
  induction p generalizing M with
  | zero =>
    have : Projective (ModuleCat.of R M) :=
      ((projectiveDimension_eq_zero_iff _).mp (by exact_mod_cast hp)).1
    have : Module.Projective R M := (IsProjective.iff_projective M).mpr this
    have : Module.Free R M := Module.free_of_flat_of_isLocalRing
    simpa using depth_eq_depth_self_of_free M
  | succ p ih =>
    -- A minimal free presentation, with free module transported to the universe of `M`.
    obtain ⟨n, g, hg, hker⟩ : ∃ (n : ℕ) (g : (Fin n → Shrink.{v} R) →ₗ[R] M),
        Function.Surjective g ∧ LinearMap.ker g ≤ maximalIdeal R • ⊤ := by
      obtain ⟨f, hf, hfker⟩ := TauCeti.IsLocalRing.exists_surjective_ker_le_maximalIdeal_smul R M
      let e : (Fin (Module.finrank (ResidueField R) (ResidueField R ⊗[R] M)) → Shrink.{v} R) ≃ₗ[R]
          (Fin (Module.finrank (ResidueField R) (ResidueField R ⊗[R] M)) → R) :=
        LinearEquiv.piCongrRight fun _ ↦ Shrink.linearEquiv R R
      refine ⟨_, f ∘ₗ e.toLinearMap, hf.comp e.surjective, ?_⟩
      rw [LinearMap.ker_comp, Submodule.comap_equiv_eq_map_symm]
      refine (Submodule.map_mono hfker).trans ?_
      rw [Submodule.map_smul'', Submodule.map_top, LinearEquiv.range]
    have hM : ¬ Module.Projective R M := fun h ↦ by
      have := Projective.projectiveDimension_le_zero (ModuleCat.of R M)
      rw [hp] at this
      exact absurd this (by norm_cast)
    have hpK : projectiveDimension (ModuleCat.of R (LinearMap.ker g)) = p := by
      rw [← ENat.WithBot.add_one_cancel, g.projectiveDimension_ker_add_one hg hM, hp]
      norm_cast
    have : Nontrivial (LinearMap.ker g) := by
      by_contra hK
      rw [not_nontrivial_iff_subsingleton] at hK
      have h := (projectiveDimension_eq_bot_iff _).mpr
        (ModuleCat.isZero_of_subsingleton (ModuleCat.of R (LinearMap.ker g)))
      rw [hpK] at h
      exact WithBot.coe_ne_bot h
    have : Module.Finite R (LinearMap.ker g) := Module.IsNoetherian.finite R _
    have : Nontrivial (Fin n → Shrink.{v} R) := hg.nontrivial
    have hK := ih (LinearMap.ker g) hpK
    have hF := depth_eq_depth_self_of_free (R := R) (Fin n → Shrink.{v} R)
    have hKtop : depth (ModuleCat.of R (LinearMap.ker g)) ≠ ⊤ := fun h ↦
      not_subsingleton (LinearMap.ker g) ((depth_eq_top_iff _).mp h)
    have h₁ := depth_min_snd_fst_sub_one_le_trd_of_exact _ g (LinearMap.exact_subtype_ker_map g)
      (LinearMap.ker g).injective_subtype hg
    have h₂ : depth (ModuleCat.of R M) + 1 ≤ depth (ModuleCat.of R (LinearMap.ker g)) := by
      rcases p with _ | q
      · -- `K` is free and lies in `𝔪 F`.
        have : Projective (ModuleCat.of R (LinearMap.ker g)) :=
          ((projectiveDimension_eq_zero_iff _).mp (by exact_mod_cast hpK)).1
        have : Module.Projective R (LinearMap.ker g) := (IsProjective.iff_projective _).mpr this
        have : Module.Free R (LinearMap.ker g) := Module.free_of_flat_of_isLocalRing
        exact depth_add_one_le_depth_ker hg hker
      · -- `depth K < depth R = depth F`.
        have h := depth_min_snd_trd_add_one_le_fst_of_exact _ g
          (LinearMap.exact_subtype_ker_map g) (LinearMap.ker g).injective_subtype hg
        refine (inf_le_iff.mp h).resolve_left fun h' ↦ ?_
        rw [hF, ← hK] at h'
        generalize depth (ModuleCat.of R (LinearMap.ker g)) = b at h' hKtop
        induction b using ENat.recTopCoe with
        | top => exact hKtop rfl
        | coe b => norm_cast at h'; omega
    rw [hF, ← hK] at h₁
    rw [← hK]
    exact ENat.add_succ_eq_of_le_of_le h₁ h₂

end IsLocalRing

variable {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R] [Small.{v} R]

/-- **The Auslander–Buchsbaum formula.** For a nonzero finite module `M` of finite projective
dimension over a Noetherian local ring `R`, `projectiveDimension M + depth M = depth R`.
Stacks, Proposition 10.111.1 (090V). -/
@[stacks 090V]
theorem ModuleCat.projectiveDimension_add_depth_eq_depth (M : ModuleCat.{v} R)
    [Module.Finite R M] [Nontrivial M] (hM : projectiveDimension M ≠ ⊤) :
    projectiveDimension M + (IsLocalRing.depth M : WithBot ℕ∞) =
      IsLocalRing.depth (ModuleCat.of R R) := by
  have hbot : projectiveDimension M ≠ ⊥ := by
    rw [ne_eq, projectiveDimension_eq_bot_iff]
    exact fun h ↦ not_subsingleton M (ModuleCat.subsingleton_of_isZero h)
  obtain ⟨d, hd⟩ := WithBot.ne_bot_iff_exists.mp hbot
  have hdtop : d ≠ ⊤ := fun h ↦ hM (by simp [← hd, h])
  obtain ⟨p, rfl⟩ := ENat.ne_top_iff_exists.mp hdtop
  rw [← hd, ← IsLocalRing.depth_add_eq_of_projectiveDimension_eq p M hd.symm, add_comm]
  norm_cast

namespace IsLocalRing

/-- If the residue field `κ` of a Noetherian local ring `R` has finite projective dimension, that
dimension is `depth R`. -/
theorem projectiveDimension_quotient_maximalIdeal_eq_depth
    (h : projectiveDimension (ModuleCat.of R (Shrink.{v} (R ⧸ maximalIdeal R))) ≠ ⊤) :
    projectiveDimension (ModuleCat.of R (Shrink.{v} (R ⧸ maximalIdeal R))) =
      depth (ModuleCat.of R R) := by
  have : Module.Finite R (Shrink.{v} (R ⧸ maximalIdeal R)) :=
    Module.Finite.equiv (Shrink.linearEquiv R (R ⧸ maximalIdeal R)).symm
  have : Nontrivial (Shrink.{v} (R ⧸ maximalIdeal R)) :=
    (Shrink.linearEquiv R (R ⧸ maximalIdeal R)).nontrivial_congr.mpr inferInstance
  have h0 : depth (ModuleCat.of R (Shrink.{v} (R ⧸ maximalIdeal R))) = 0 :=
    depth_eq_zero_iff_nontrivial_linearMap.mpr
      ⟨(Shrink.linearEquiv R _).symm.toLinearMap, 0, fun h ↦ one_ne_zero
        ((Shrink.linearEquiv R (R ⧸ maximalIdeal R)).symm.map_eq_zero_iff.mp
          (by simpa using congr($h 1)))⟩
  rw [← ModuleCat.projectiveDimension_add_depth_eq_depth _ h, h0]
  simp

/-- If the residue field `κ` of a Noetherian local ring `R` has finite projective dimension, that
dimension is at most the Krull dimension of `R`. Stacks, Lemma 10.110.4 (00OB). -/
@[stacks 00OB]
theorem projectiveDimension_quotient_maximalIdeal_le_ringKrullDim
    (h : projectiveDimension (ModuleCat.of R (Shrink.{v} (R ⧸ maximalIdeal R))) ≠ ⊤) :
    projectiveDimension (ModuleCat.of R (Shrink.{v} (R ⧸ maximalIdeal R))) ≤ ringKrullDim R := by
  rw [projectiveDimension_quotient_maximalIdeal_eq_depth h,
    ← Module.supportDim_self_eq_ringKrullDim]
  exact depth_le_supportDim

end IsLocalRing
