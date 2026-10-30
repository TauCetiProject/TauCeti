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
import TauCeti.Algebra.Category.ModuleCat.Ext.Basic
import TauCeti.Algebra.Category.ModuleCat.Projective.Dimension
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

namespace IsLocalRing

variable {R : Type u} [CommRing R] [IsLocalRing R] [Small.{v} R]

/-- A minimal free presentation of a finite module `M`, by a free module in the universe of `M`:
a surjection `(Fin n → R) → M` whose kernel lies in `𝔪 • ⊤`. -/
private theorem exists_surjective_ker_le_maximalIdeal_smul (M : Type v) [AddCommGroup M]
    [Module R M] [Module.Finite R M] :
    ∃ (n : ℕ) (g : (Fin n → Shrink.{v} R) →ₗ[R] M), Function.Surjective g ∧
      LinearMap.ker g ≤ maximalIdeal R • ⊤ := by
  obtain ⟨n, v, hv, hrel⟩ :=
    TauCeti.IsLocalRing.exists_span_eq_top_forall_mem_maximalIdeal (R := R) (M := M)
  let e : (Fin n → Shrink.{v} R) ≃ₗ[R] (Fin n → R) :=
    LinearEquiv.piCongrRight fun _ ↦ Shrink.linearEquiv R R
  refine ⟨n, Fintype.linearCombination R v ∘ₗ e.toLinearMap, ?_, fun x hx ↦ ?_⟩
  · rw [← LinearMap.range_eq_top, LinearMap.range_comp, LinearEquiv.range, Submodule.map_top,
      Fintype.range_linearCombination, hv]
  · have hx' : e x ∈ maximalIdeal R • (⊤ : Submodule R (Fin n → R)) := by
      rw [pi_eq_sum_univ (e x)]
      exact Submodule.sum_mem _ fun i _ ↦ Submodule.smul_mem_smul
        (hrel (e x) (by simpa [Fintype.linearCombination_apply] using hx) i) trivial
    have : x ∈ (maximalIdeal R • (⊤ : Submodule R (Fin n → R))).map e.symm.toLinearMap := by
      rw [Submodule.mem_map_equiv]
      simpa using hx'
    rwa [Submodule.map_smul'', Submodule.map_top, LinearEquiv.range] at this

/-- If `0 → K → F → M → 0` is a free presentation with `K` finite free and `K ⊆ 𝔪 F`, then
`depth M + 1 ≤ depth K`. -/
private theorem depth_add_one_le_depth_ker {F M : Type v} [AddCommGroup F] [Module R F]
    [AddCommGroup M] [Module R M] {g : F →ₗ[R] M} (hg : Function.Surjective g)
    [Module.Free R (LinearMap.ker g)] [Module.Finite R (LinearMap.ker g)]
    (hker : LinearMap.ker g ≤ maximalIdeal R • ⊤) :
    depth (ModuleCat.of R M) + 1 ≤ depth (ModuleCat.of R (LinearMap.ker g)) := by
  have hI : maximalIdeal R ≤ Module.annihilator R (Shrink.{v} (R ⧸ maximalIdeal R)) := by
    rw [(Shrink.linearEquiv R _).annihilator_eq, Ideal.annihilator_quotient]
  have hrange : LinearMap.range (LinearMap.ker g).subtype ≤ maximalIdeal R • ⊤ := by
    rwa [Submodule.range_subtype]
  have key (n : ℕ) (x : Ext (ModuleCat.of R (Shrink.{v} (R ⧸ maximalIdeal R)))
      (ModuleCat.of R (LinearMap.ker g)) n) :
      x.comp (Ext.mk₀ (ModuleCat.ofHom (LinearMap.ker g).subtype)) (add_zero n) = 0 :=
    Ext.comp_mk₀_eq_zero_of_range_le_smul_top hI _ hrange x
  have h := ModuleCat.depth_trd_add_one_le_fst_of_comp_mk₀_eq_zero
    (ModuleCat.of R (Shrink.{v} (R ⧸ maximalIdeal R))) (LinearMap.shortExact_shortComplexKer hg) key
  -- `h` is the goal, with `IsLocalRing.depth` unfolded to `ModuleCat.depth`.
  exact h

/-- The arithmetic of the inductive step: if `depth K = b` is finite, `depth M = a`, and
`b + p = depth R`, then `b - 1 ≤ a` and `a + 1 ≤ b` give `a + (p + 1) = b + p`. -/
private theorem add_succ_eq_of_le_of_le {a b : ℕ∞} {p : ℕ} (hb : b ≠ ⊤)
    (h₁ : (b + p) ⊓ (b - 1) ≤ a) (h₂ : a + 1 ≤ b) : a + (p + 1 : ℕ) = b + p := by
  induction b using ENat.recTopCoe with
  | top => exact absurd rfl hb
  | coe b =>
    induction a using ENat.recTopCoe with
    | top => simp at h₂
    | coe a =>
      norm_cast at h₂ ⊢
      rcases min_le_iff.mp h₁ with h | h <;> norm_cast at h <;> omega

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
    obtain ⟨n, g, hg, hker⟩ := exists_surjective_ker_le_maximalIdeal_smul (R := R) M
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
    exact add_succ_eq_of_le_of_le hKtop h₁ h₂

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
