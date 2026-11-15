/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Module.PseudoCoherent.TwoOutOfThree

/-!
# Pseudocoherence along a pseudocoherent ring map

Let `S` be a ring with an `R`-module structure compatible with its multiplication, for instance an
`R`-algebra, and let `N` be an `S`-module, regarded also as an `R`-module by restriction of
scalars. When `S` is pseudocoherent as an `R`-module, in particular finite over `R`, an `S`-module
is pseudocoherent over `S` exactly when it is pseudocoherent over `R`, degree by degree. The
typical case is a quotient `S = R ⧸ I` for which `R ⧸ I` is pseudocoherent over `R`, such as the
quotient by a non-zero-divisor; then pseudocoherence of an `R ⧸ I`-module can be tested over `R`.

The two directions need different hypotheses on `S`. Pseudocoherence in degree `m` descends from
`S` to `R` when `S` is `m`-pseudocoherent over `R`, and ascends from `R` to `S` already when `S` is
`(m - 1)`-pseudocoherent over `R`; in degree `0` the ascent asks nothing of `S`.

The hypotheses on `S` cannot be dropped in either direction. For a field `k` and
`S = k[y₁, y₂, …]` acting on `N = k` through `yᵢ ↦ 0`, the module `N` is finitely presented over
`k` but not over `S`. For `S = R ⧸ I` with `I` not finitely generated, `N = S` is free over `S` but
not finitely presented over `R`.

## Main results

* `TauCeti.Huber.IsPseudoCoherentOver.trans`: an `m`-pseudocoherent `S`-module is
  `m`-pseudocoherent over `R` when `S` is `m`-pseudocoherent over `R`.
* `TauCeti.Huber.IsPseudoCoherentOver.of_restrictScalars`: an `S`-module that is
  `m`-pseudocoherent over `R` is `m`-pseudocoherent over `S` when `S` is `(m - 1)`-pseudocoherent
  over `R`.
* `TauCeti.Huber.isPseudoCoherentOver_restrictScalars_iff`: when `S` is `m`-pseudocoherent over
  `R`, an `S`-module is `m`-pseudocoherent over `R` exactly when it is `m`-pseudocoherent over `S`.

## References

* The Stacks Project, Lemma 15.66.11, Tag 064Z (with the index negated).
* K. S. Kedlaya and R. Liu, *Relative p-adic Hodge theory, II: Imperfect period rings*, §1.1,
  Remark 1.1.13.
-/

public section

namespace TauCeti.Huber

open LinearMap

universe u

variable {R : Type*} {S : Type u} {N : Type*} [Ring R] [Ring S] [Module R S] [IsScalarTower R S S]
  [AddCommGroup N] [Module R N] [Module S N] [IsScalarTower R S N] {m : ℕ∞}

namespace IsPseudoCoherentOver

/- Both directions are proved by induction on the degree, comparing a surjection `π : Sᵏ → K` of
`S`-modules with the short exact sequence `0 → ker π → Sᵏ → K → 0` of `R`-modules and applying the
two-out-of-three properties. The inductions run over modules in the universe of `S`, where the
kernels of such surjections live. -/

/-! ### From `S` to `R` -/

/-- Finite-degree descent for modules in the universe of `S`: if `S` is `n`-pseudocoherent over
`R`, then every `n`-pseudocoherent `S`-module `K : Type u` is `n`-pseudocoherent over `R`. -/
private theorem trans_nat : ∀ (n : ℕ) {K : Type u} [AddCommGroup K] [Module R K] [Module S K]
    [IsScalarTower R S K], IsPseudoCoherentOver R S n → IsPseudoCoherentOver S K n →
      IsPseudoCoherentOver R K n
  | 0, K, _, _, _, _, hS, h =>
    have := zero_iff.mp hS
    have := zero_iff.mp h
    zero_iff.mpr (.trans S K)
  | n + 1, K, _, _, _, _, hS, h => by
    rw [Nat.cast_succ] at hS h ⊢
    -- For a surjection `π : Sᵏ → K` of `S`-modules, `K` is the cokernel of `ker π → Sᵏ` over `R`.
    obtain ⟨k, π, hπ, hK⟩ := succ_iff.mp h
    have hK' : IsPseudoCoherentOver R (ker π) n := trans_nat n (hS.mono le_self_add) hK
    exact cokernel (f := (ker π).subtype.restrictScalars R) (g := π.restrictScalars R)
      Subtype.val_injective (exact_subtype_ker_map π) hπ
      (fun _ ↦ by simpa using hK') (pi fun _ ↦ hS)

/-- **Pseudocoherence descends along a pseudocoherent ring map.** If `S` is `m`-pseudocoherent as
an `R`-module, then every `m`-pseudocoherent `S`-module is `m`-pseudocoherent over `R`
(Stacks, Tag 064Z). -/
theorem trans (hS : IsPseudoCoherentOver R S m) (h : IsPseudoCoherentOver S N m) :
    IsPseudoCoherentOver R N m := by
  -- Replace `N` by an equivalent quotient of `Sᵏ`, which lies in the universe of `S`.
  have := h.finite
  obtain ⟨k, π, hπ⟩ := Module.Finite.exists_fin' S N
  let e := π.quotKerEquivOfSurjective hπ
  have hnat (n : ℕ) (hS : IsPseudoCoherentOver R S n) (h : IsPseudoCoherentOver S N n) :
      IsPseudoCoherentOver R N n :=
    (trans_nat n hS (h.of_equiv e.symm)).of_equiv (e.restrictScalars R)
  induction m using ENat.recTopCoe with
  | top => exact top_iff.mpr fun n ↦ hnat n (top_iff.mp hS n) (top_iff.mp h n)
  | coe n => exact hnat n hS h

/-! ### From `R` to `S` -/

/-- Positive finite-degree ascent for modules in the universe of `S`: if `S` is `n`-pseudocoherent
over `R`, then every `S`-module `K : Type u` that is `(n + 1)`-pseudocoherent over `R` is
`(n + 1)`-pseudocoherent over `S`. -/
private theorem of_restrictScalars_nat : ∀ (n : ℕ) {K : Type u} [AddCommGroup K] [Module R K]
    [Module S K] [IsScalarTower R S K], IsPseudoCoherentOver R S n →
      IsPseudoCoherentOver R K (n + 1 : ℕ) → IsPseudoCoherentOver S K (n + 1 : ℕ)
  | n, K, _, _, _, _, hS, h => by
    have := h.finite
    have : Module.Finite S K := .of_restrictScalars_finite R S K
    obtain ⟨k, π, hπ⟩ := Module.Finite.exists_fin' S K
    rw [Nat.cast_succ] at h ⊢
    -- For a surjection `π : Sᵏ → K` of `S`-modules, `ker π` is the kernel of a surjection over `R`,
    -- and it is pseudocoherent over `S` by induction.
    have hK : IsPseudoCoherentOver R (ker π) n :=
      kernel (f := (ker π).subtype.restrictScalars R) (g := π.restrictScalars R)
        Subtype.val_injective (exact_subtype_ker_map π) hπ (pi fun _ ↦ hS) h
    refine (succ_iff_ker hπ).mpr ?_
    cases n with
    | zero =>
      have := zero_iff.mp hK
      exact zero_iff.mpr (.of_restrictScalars_finite R S _)
    | succ n => exact of_restrictScalars_nat n (hS.mono (by simp)) hK

/-- **Pseudocoherence ascends along a finite ring map.** If `S` is `(m - 1)`-pseudocoherent as an
`R`-module (no condition when `m = 0`), then every `S`-module that is `m`-pseudocoherent over `R` is
`m`-pseudocoherent over `S` (Stacks, Tag 064Z). In degree `1` this says that a module finitely
presented over `R` is finitely presented over a finite `R`-algebra `S`. -/
theorem of_restrictScalars (hS : 0 < m → IsPseudoCoherentOver R S (m - 1))
    (h : IsPseudoCoherentOver R N m) : IsPseudoCoherentOver S N m := by
  have := h.finite
  have : Module.Finite S N := .of_restrictScalars_finite R S N
  rcases eq_zero_or_pos m with rfl | hm
  · exact zero_iff.mpr ‹_›
  -- Replace `N` by an equivalent quotient of `Sᵏ`, which lies in the universe of `S`.
  obtain ⟨k, π, hπ⟩ := Module.Finite.exists_fin' S N
  let e := π.quotKerEquivOfSurjective hπ
  have hnat (n : ℕ) (hS : IsPseudoCoherentOver R S n) (h : IsPseudoCoherentOver R N (n + 1 : ℕ)) :
      IsPseudoCoherentOver S N (n + 1 : ℕ) :=
    (of_restrictScalars_nat n hS (h.of_equiv (e.restrictScalars R).symm)).of_equiv e
  have hS := hS hm
  induction m using ENat.recTopCoe with
  | top =>
    exact top_iff.mpr fun n ↦
      (hnat n (top_iff.mp hS n) (top_iff.mp h (n + 1))).mono (by exact_mod_cast n.le_succ)
  | coe n =>
    obtain ⟨n, rfl⟩ := Nat.exists_eq_add_one_of_ne_zero (by exact_mod_cast hm.ne')
    exact hnat n (by simpa using hS) h

end IsPseudoCoherentOver

/-- **Pseudocoherence along a pseudocoherent ring map.** If `S` is `m`-pseudocoherent as an
`R`-module, an `S`-module is `m`-pseudocoherent over `R` exactly when it is `m`-pseudocoherent
over `S` (Stacks, Tag 064Z). -/
theorem isPseudoCoherentOver_restrictScalars_iff (hS : IsPseudoCoherentOver R S m) :
    IsPseudoCoherentOver R N m ↔ IsPseudoCoherentOver S N m :=
  ⟨.of_restrictScalars fun _ ↦ hS.mono tsub_le_self, hS.trans⟩

end TauCeti.Huber
