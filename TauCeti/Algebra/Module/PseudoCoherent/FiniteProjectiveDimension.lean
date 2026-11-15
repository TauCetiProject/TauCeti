/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Category.ModuleCat.Projective.Dimension
public import TauCeti.Algebra.Module.PseudoCoherent.TwoOutOfThree

/-!
# Modules of finite projective dimension

A module `M` over a ring `R` is *`m`-fpd* when it has a resolution
`0 → P_m → ⋯ → P₁ → P₀ → M → 0` of length at most `m` by finitely generated projective modules.
Following Kedlaya–Liu, `TauCeti.Module.IsFPD R M m` states this with a finite free resolution
`⋯ → F₁ → F₀ → M → 0`, exact everywhere, whose `m`-th syzygy is projective: the syzygy is `M`
itself when `m = 0` and the image of `F_m → F_{m-1}` otherwise. Cutting the resolution at that
syzygy gives a finite projective resolution of length `m`. In particular every `m`-fpd module is
pseudocoherent.

The main result identifies the definition with Mathlib's projective dimension: `M` is `m`-fpd
exactly when it is pseudocoherent and `HasProjectiveDimensionLE (ModuleCat.of R M) m`. The proof
is dimension shifting along `0 → ker ε → F₀ → M → 0`, and it shows that the projectivity of the
`m`-th syzygy does not depend on the chosen resolution. From it, `M` is `(m + 1)`-fpd exactly
when the kernel of some, equivalently every, surjection onto `M` from a finitely generated
projective module is `m`-fpd.

## Main definitions

* `TauCeti.Module.IsFPD R M m`: `M` has a finite free resolution, exact everywhere, whose `m`-th
  syzygy is projective.

## Main results

* `TauCeti.Module.IsFPD.isPseudoCoherentOver`: an `m`-fpd module is pseudocoherent.
* `TauCeti.Module.IsFPD.zero_iff`: `0`-fpd means finitely generated and projective.
* `TauCeti.Module.IsFPD.mono`: an `m`-fpd module is `m'`-fpd for every `m' ≥ m`.
* `TauCeti.Module.isFPD_iff_hasProjectiveDimensionLE`: `M` is `m`-fpd exactly when it is
  pseudocoherent of projective dimension at most `m`.
* `TauCeti.Module.IsFPD.succ_iff_ker`: for a surjection `f` onto `M` from a finitely generated
  projective module, `M` is `(m + 1)`-fpd exactly when `ker f` is `m`-fpd.
* `TauCeti.Module.IsFPD.cokernel`: in a short exact sequence `0 → M₁ → M → M₂ → 0` with `M₁`
  `m`-fpd and `M` `(m + 1)`-fpd, `M₂` is `(m + 1)`-fpd.

## References

* K. S. Kedlaya and R. Liu, *Relative p-adic Hodge theory, II: Imperfect period rings*, §1.1,
  Definition 1.1.1.
-/

public section

namespace TauCeti.Module

open LinearMap CategoryTheory

universe u v w

section Definition

variable (R : Type u) (M : Type v) [Ring R] [AddCommGroup M] [Module R M]

/-- `M` is *`m`-fpd* over `R`: it has a resolution `0 → P_m → ⋯ → P₀ → M → 0` of length at most
`m` by finitely generated projective modules (Kedlaya–Liu II, Definition 1.1.1). It is stated
with a resolution `⋯ → F₁ → F₀ → M → 0` by finite free modules `Fᵢ = Fin (n i) → R`, exact
everywhere, whose `m`-th syzygy is projective: `M` itself when `m = 0`, and the image of
`d (m - 1) : F_m → F_{m-1}` otherwise. -/
def IsFPD (m : ℕ) : Prop :=
  ∃ (n : ℕ → ℕ) (d : ∀ i, (Fin (n (i + 1)) → R) →ₗ[R] (Fin (n i) → R))
    (ε : (Fin (n 0) → R) →ₗ[R] M),
    Function.Surjective ε ∧ Function.Exact (d 0) ε ∧ (∀ i, Function.Exact (d (i + 1)) (d i)) ∧
      (m = 0 → Module.Projective R M) ∧ ∀ k : ℕ, m = k + 1 → Module.Projective R (range (d k))

/-- `M` is `m`-fpd over `R` if and only if it has a finite free resolution
`⋯ → Fin (n 1) → R → Fin (n 0) → R → M → 0`, exact everywhere, whose `m`-th syzygy is
projective. -/
theorem isFPD_iff (m : ℕ) :
    IsFPD R M m ↔
      ∃ (n : ℕ → ℕ) (d : ∀ i, (Fin (n (i + 1)) → R) →ₗ[R] (Fin (n i) → R))
        (ε : (Fin (n 0) → R) →ₗ[R] M),
        Function.Surjective ε ∧ Function.Exact (d 0) ε ∧
          (∀ i, Function.Exact (d (i + 1)) (d i)) ∧
          (m = 0 → Module.Projective R M) ∧
          ∀ k : ℕ, m = k + 1 → Module.Projective R (range (d k)) :=
  Iff.rfl

end Definition

variable {R : Type u} {M : Type v} {N : Type w} [Ring R] [AddCommGroup M] [Module R M]
  [AddCommGroup N] [Module R N] {m : ℕ}

namespace IsFPD

/-- Finite projective dimension is invariant under linear equivalence. -/
theorem of_equiv (e : M ≃ₗ[R] N) (h : IsFPD R M m) : IsFPD R N m := by
  obtain ⟨n, d, ε, hε, h₀, hd, hM, hk⟩ := h
  exact ⟨n, d, e.toLinearMap ∘ₗ ε, e.surjective.comp hε, e.postcomp_exact_iff_exact.mpr h₀, hd,
    fun hm ↦ have := hM hm; .of_equiv' e, hk⟩

/-- **A module of finite projective dimension is pseudocoherent.** -/
theorem isPseudoCoherentOver (h : IsFPD R M m) : Huber.IsPseudoCoherentOver R M ⊤ := by
  obtain ⟨n, d, ε, hε, h₀, hd, -⟩ := h
  exact (Huber.isPseudoCoherentOver_iff R M ⊤).mpr ⟨n, d, ε, hε, fun _ ↦ h₀, fun i _ ↦ hd i⟩

/-- **`0`-fpd means finitely generated and projective.** -/
@[simp]
theorem zero_iff : IsFPD R M 0 ↔ Module.Finite R M ∧ Module.Projective R M := by
  refine ⟨fun h ↦ ⟨h.isPseudoCoherentOver.finite, ?_⟩, fun ⟨_, hM⟩ ↦ ?_⟩
  · obtain ⟨-, -, -, -, -, -, hM, -⟩ := h
    exact hM rfl
  · obtain ⟨n, d, ε, hε, h₀, hd⟩ := (Huber.isPseudoCoherentOver_iff R M ⊤).mp .of_projective
    exact ⟨n, d, ε, hε, h₀ le_top, fun i ↦ hd i le_top, fun _ ↦ hM, fun _ h ↦ absurd h.symm
      (Nat.succ_ne_zero _)⟩

/-- **Finitely generated projective modules are `0`-fpd.** -/
theorem of_projective [Module.Finite R M] [Module.Projective R M] : IsFPD R M 0 :=
  zero_iff.mpr ⟨‹_›, ‹_›⟩

/-- An `m`-fpd module is `(m + 1)`-fpd, with the same resolution: if the `m`-th syzygy is
projective, the next syzygy is the kernel of a surjection onto it from a finite free module, hence
a direct summand of that free module. -/
private theorem succ (h : IsFPD R M m) : IsFPD R M (m + 1) := by
  obtain ⟨n, d, ε, hε, h₀, hd, hM, hk⟩ := h
  refine ⟨n, d, ε, hε, h₀, hd, fun h ↦ absurd h (Nat.succ_ne_zero _), fun k hk' ↦ ?_⟩
  obtain rfl := Nat.succ_injective hk'
  rcases m with _ | k
  · have := hM rfl
    have := ε.projective_ker_of_surjective hε
    exact .of_equiv' (LinearEquiv.ofEq _ _ (exact_iff.mp h₀))
  · have := hk k rfl
    have := (d k).rangeRestrict.projective_ker_of_surjective (d k).surjective_rangeRestrict
    exact .of_equiv' (LinearEquiv.ofEq (ker (d k).rangeRestrict) _
      (by rw [ker_rangeRestrict, exact_iff.mp (hd k)]))

/-- **An `m`-fpd module is `m'`-fpd for every `m' ≥ m`.** -/
theorem mono {m' : ℕ} (h : IsFPD R M m) (hm : m ≤ m') : IsFPD R M m' := by
  induction m', hm using Nat.le_induction with
  | base => exact h
  | succ _ _ ih => exact ih.succ

end IsFPD

/-! ### Comparison with projective dimension -/

section ProjectiveDimension

variable {R : Type u} [Ring R]

/-- **Finite projective dimension is pseudocoherence with bounded projective dimension.** A module
`M` is `m`-fpd exactly when it is pseudocoherent and
`HasProjectiveDimensionLE (ModuleCat.of R M) m`, that is, `Ext^i(M, -)` vanishes for `i > m`. -/
theorem isFPD_iff_hasProjectiveDimensionLE {M : Type u} [AddCommGroup M] [Module R M] {m : ℕ} :
    IsFPD R M m ↔
      Huber.IsPseudoCoherentOver R M ⊤ ∧ HasProjectiveDimensionLE (ModuleCat.of R M) m := by
  -- Along any exact finite free resolution, the projectivity clauses say exactly that the
  -- projective dimension is at most `m`.
  have key {n : ℕ → ℕ} {d : ∀ i, (Fin (n (i + 1)) → R) →ₗ[R] (Fin (n i) → R)}
      {ε : (Fin (n 0) → R) →ₗ[R] M} (hε : Function.Surjective ε) (h₀ : Function.Exact (d 0) ε)
      (hd : ∀ i, Function.Exact (d (i + 1)) (d i)) :
      ((m = 0 → Module.Projective R M) ∧ ∀ k : ℕ, m = k + 1 → Module.Projective R (range (d k)))
        ↔ HasProjectiveDimensionLE (ModuleCat.of R M) m := by
    rcases m with _ | k
    · rw [IsProjective.iff_projective, projective_iff_hasProjectiveDimensionLE_zero]
      exact ⟨fun h ↦ h.1 rfl, fun h ↦ ⟨fun _ ↦ h, fun k hk ↦ absurd hk.symm k.succ_ne_zero⟩⟩
    · rw [← projective_range_iff_hasProjectiveDimensionLE k (F := fun i ↦ Fin (n i) → R) hε h₀
        hd]
      exact ⟨fun h ↦ h.2 k rfl, fun h ↦ ⟨fun hk ↦ absurd hk k.succ_ne_zero,
        fun _ hk ↦ Nat.succ_injective hk ▸ h⟩⟩
  refine ⟨fun h ↦ ⟨h.isPseudoCoherentOver, ?_⟩, fun ⟨hM, hpd⟩ ↦ ?_⟩
  · obtain ⟨n, d, ε, hε, h₀, hd, hp⟩ := h
    exact (key hε h₀ hd).mp hp
  · obtain ⟨n, d, ε, hε, h₀, hd⟩ := (Huber.isPseudoCoherentOver_iff R M ⊤).mp hM
    exact ⟨n, d, ε, hε, h₀ le_top, fun i ↦ hd i le_top,
      (key hε (h₀ le_top) fun i ↦ hd i le_top).mpr hpd⟩

/-- `IsFPD.succ_iff_ker` for modules in the universe of the ring, through projective dimension. -/
private theorem IsFPD.succ_iff_ker_aux {P M : Type u} [AddCommGroup P] [Module R P]
    [Module.Finite R P] [Module.Projective R P] [AddCommGroup M] [Module R M] {m : ℕ}
    {f : P →ₗ[R] M} (hf : Function.Surjective f) :
    IsFPD R M (m + 1) ↔ IsFPD R (ker f) m := by
  rw [isFPD_iff_hasProjectiveDimensionLE, isFPD_iff_hasProjectiveDimensionLE,
    hasProjectiveDimensionLE_succ_iff_ker hf]
  refine and_congr_left' ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · exact (top_add (1 : ℕ∞) ▸ h).ker_of_projective hf
  · exact Huber.IsPseudoCoherentOver.cokernel (ker f).injective_subtype (exact_subtype_ker_map f)
      hf (fun _ ↦ ENat.top_sub_one ▸ h) .of_projective

end ProjectiveDimension

namespace IsFPD

variable {R : Type u} {M : Type v} [Ring R] [AddCommGroup M] [Module R M] {m : ℕ}

/-- **Finite projective dimension one degree at a time.** For a surjection `f` onto `M` from a
finitely generated projective module, `M` is `(m + 1)`-fpd exactly when `ker f` is `m`-fpd. In
particular the condition on `ker f` does not depend on `f`. -/
theorem succ_iff_ker {P : Type w} [AddCommGroup P] [Module R P] [Module.Finite R P]
    [Module.Projective R P] {f : P →ₗ[R] M} (hf : Function.Surjective f) :
    IsFPD R M (m + 1) ↔ IsFPD R (ker f) m := by
  -- Replace `P` by a quotient `P'` of a finite free module and `M` by `P' ⧸ ker (f ∘ e)`, which lie
  -- in the universe of `R`.
  obtain ⟨k, g, hg⟩ := Module.Finite.exists_fin' R P
  let e : ((Fin k → R) ⧸ ker g) ≃ₗ[R] P := g.quotKerEquivOfSurjective hg
  have : Module.Projective R ((Fin k → R) ⧸ ker g) := .of_equiv' e.symm
  let f' := f ∘ₗ e.toLinearMap
  have hf' : Function.Surjective f' := hf.comp e.surjective
  let eM : (((Fin k → R) ⧸ ker g) ⧸ ker f') ≃ₗ[R] M := f'.quotKerEquivOfSurjective hf'
  have hker : (ker f').map e.toLinearMap = ker f := by
    rw [ker_comp, Submodule.map_comap_eq_of_surjective e.surjective]
  let eK : ker (ker f').mkQ ≃ₗ[R] ker f :=
    (LinearEquiv.ofEq _ _ (Submodule.ker_mkQ _)).trans (e.ofSubmodules _ _ hker)
  rw [← (show _ ↔ IsFPD R M (m + 1) from ⟨of_equiv eM, of_equiv eM.symm⟩),
    ← (show _ ↔ IsFPD R (ker f) m from ⟨of_equiv eK, of_equiv eK.symm⟩)]
  exact succ_iff_ker_aux (Submodule.mkQ_surjective _)

/-- `IsFPD.cokernel` for a quotient `P ⧸ N` of a module in the universe of the ring, through
projective dimension. -/
private theorem cokernel_aux {P : Type u} [AddCommGroup P] [Module R P] {N : Submodule R P}
    (hN : IsFPD R N m) (hP : IsFPD R P (m + 1)) : IsFPD R (P ⧸ N) (m + 1) := by
  have hK : IsFPD R (ker N.mkQ) m := hN.of_equiv (.ofEq _ _ N.ker_mkQ.symm)
  rw [isFPD_iff_hasProjectiveDimensionLE] at hK hP ⊢
  refine ⟨Huber.IsPseudoCoherentOver.cokernel N.injective_subtype (exact_subtype_mkQ N)
    N.mkQ_surjective (fun _ ↦ ENat.top_sub_one ▸ hN.isPseudoCoherentOver) hP.1, ?_⟩
  exact (N.mkQ.shortExact_shortComplexKer N.mkQ_surjective).hasProjectiveDimensionLT_X₃ (m + 1)
    hK.2 hP.2

/-- **A cokernel of `m`-fpd modules is `(m + 1)`-fpd.** If `0 → M₁ → M → M₂ → 0` is exact, `M₁`
is `m`-fpd and `M` is `(m + 1)`-fpd, then `M₂` is `(m + 1)`-fpd (Kedlaya–Liu II, Lemma 1.1.5). -/
theorem cokernel {M₁ M₂ : Type*} [AddCommGroup M₁] [Module R M₁] [AddCommGroup M₂]
    [Module R M₂] {f : M₁ →ₗ[R] M} {g : M →ₗ[R] M₂} (hf : Function.Injective f)
    (hfg : Function.Exact f g) (hg : Function.Surjective g) (h₁ : IsFPD R M₁ m)
    (h : IsFPD R M (m + 1)) :
    IsFPD R M₂ (m + 1) := by
  -- Replace `M` by a quotient `P` of a finite free module, `M₁` by the submodule of `P`
  -- corresponding to `ker g`, and `M₂` by the quotient of `P` by it; all lie in the universe
  -- of `R`.
  have := h.isPseudoCoherentOver.finite
  obtain ⟨k, π, hπ⟩ := Module.Finite.exists_fin' R M
  let e : ((Fin k → R) ⧸ ker π) ≃ₗ[R] M := π.quotKerEquivOfSurjective hπ
  have hmap : ((ker g).comap e.toLinearMap).map e.toLinearMap = ker g :=
    Submodule.map_comap_eq_of_surjective e.surjective _
  let e₁ : M₁ ≃ₗ[R] (ker g).comap e.toLinearMap :=
    ((LinearEquiv.ofInjective f hf).trans (.ofEq _ _ (exact_iff.mp hfg).symm)).trans
      (e.ofSubmodules _ _ hmap).symm
  exact (cokernel_aux (h₁.of_equiv e₁) (h.of_equiv e.symm)).of_equiv
    ((Submodule.Quotient.equiv _ _ e hmap).trans (g.quotKerEquivOfSurjective hg))

end IsFPD

end TauCeti.Module
