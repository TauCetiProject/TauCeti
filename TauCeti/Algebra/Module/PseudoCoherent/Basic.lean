/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.FinitePresentation
public import Mathlib.Data.ENat.Basic
public import Mathlib.LinearAlgebra.FreeModule.Finite.Basic
public import Mathlib.RingTheory.Noetherian.Basic
public import TauCeti.Algebra.Module.Projective.Schanuel

import Mathlib.LinearAlgebra.Basis.Prod
import Mathlib.LinearAlgebra.Projection
import Mathlib.RingTheory.Finiteness.Prod

/-!
# Pseudocoherent modules

A module `M` over a ring `R` is *`m`-pseudocoherent*, for `m ∈ ℕ ∪ {∞}`, when it has a resolution
`⋯ → F₁ → F₀ → M → 0` by finite free modules that is exact at `M, F₀, …, F_{m-1}`: only the terms
`F₀, …, F_m` of the resolution matter. It is *pseudocoherent* when it is `∞`-pseudocoherent. The
notion is a property of the module alone. A module is `0`-pseudocoherent exactly when it is finitely
generated and `1`-pseudocoherent exactly when it is finitely presented. Over a coherent ring, for
instance a noetherian ring, every finitely presented module is pseudocoherent, but in general
`m`-pseudocoherence becomes strictly stronger as `m` grows. Pseudocoherent modules replace finitely
presented ones in the module theory of sheafy rings that are not noetherian.

The predicate `TauCeti.Huber.IsPseudoCoherentOver R M m` uses coordinate resolutions: the terms are
the modules `Fin k → R`, and exactness is `Function.Exact`.

The main results describe pseudocoherence one degree at a time. `M` is `(m + 1)`-pseudocoherent
exactly when the kernel of a surjection onto `M` from a finite free module is `m`-pseudocoherent,
and then the kernel of every surjection from a finitely generated projective module is
`m`-pseudocoherent. The second statement rests on Schanuel's lemma
(`TauCeti.exists_linearEquiv_comp_fst_eq_comp_snd_comp`). It allows a resolution to be extended one
step at a time, which shows that pseudocoherence is pseudocoherence in every finite degree.

## Main definitions

* `TauCeti.Huber.IsPseudoCoherentOver R M m`: `M` has a finite free resolution exact at
  `M, F₀, …, F_{m-1}`.

## Main results

* `TauCeti.Huber.IsPseudoCoherentOver.zero_iff`, `TauCeti.Huber.IsPseudoCoherentOver.one_iff`:
  `0`-pseudocoherent means finitely generated, and `1`-pseudocoherent means finitely presented.
* `TauCeti.Huber.IsPseudoCoherentOver.succ_iff_ker`: for a surjection `f` from a finite free
  module, `M` is `(m + 1)`-pseudocoherent exactly when `ker f` is `m`-pseudocoherent.
* `TauCeti.Huber.IsPseudoCoherentOver.ker_of_projective`: the kernel of a surjection from a
  finitely generated projective module onto an `(m + 1)`-pseudocoherent module is
  `m`-pseudocoherent.
* `TauCeti.Huber.IsPseudoCoherentOver.top_iff`: a module is pseudocoherent exactly when it is
  `m`-pseudocoherent for every natural number `m`.
* `TauCeti.Huber.IsPseudoCoherentOver.of_projective`: finitely generated projective modules are
  pseudocoherent.
* `TauCeti.Huber.IsPseudoCoherentOver.prod`: products of `m`-pseudocoherent modules are
  `m`-pseudocoherent.
* `TauCeti.Huber.IsPseudoCoherentOver.of_isNoetherianRing`: over a noetherian ring, finitely
  generated modules are pseudocoherent.

## References

* K. S. Kedlaya and R. Liu, *Relative p-adic Hodge theory, II: Imperfect period rings*, §1.1,
  Definition 1.1.1 and Remark 1.1.6.
* The Stacks Project, Tags 064Q, 064T, 064U and 066E (with the index negated).
-/

public section

namespace TauCeti.Huber

open LinearMap

universe u v w

section Definition

variable (R : Type u) (M : Type v) [Ring R] [AddCommGroup M] [Module R M]

/-- `M` is *`m`-pseudocoherent* over `R`: it has a resolution `⋯ → F₁ → F₀ → M → 0` by finite free
modules `Fᵢ = Fin (n i) → R`, with augmentation `ε` and differentials `d i : Fᵢ₊₁ → Fᵢ`, which is
exact at `M, F₀, …, F_{m-1}`. Thus `0`-pseudocoherent means finitely generated,
`1`-pseudocoherent means finitely presented, and for `m = ⊤` the whole resolution is exact
(Kedlaya–Liu II, Definition 1.1.1; Stacks, Tag 064T, with the index negated). -/
def IsPseudoCoherentOver (m : ℕ∞) : Prop :=
  ∃ (n : ℕ → ℕ) (d : ∀ i, (Fin (n (i + 1)) → R) →ₗ[R] (Fin (n i) → R))
    (ε : (Fin (n 0) → R) →ₗ[R] M),
    Function.Surjective ε ∧ (1 ≤ m → Function.Exact (d 0) ε) ∧
      ∀ i : ℕ, ((i + 2 : ℕ) : ℕ∞) ≤ m → Function.Exact (d (i + 1)) (d i)

/-- `M` is `m`-pseudocoherent over `R` if and only if it has a resolution
`⋯ → Fin (n 1) → R → Fin (n 0) → R → M → 0`, with augmentation `ε` and differentials `d i`, that is
exact at `M, F₀, …, F_{m-1}`. -/
theorem isPseudoCoherentOver_iff (m : ℕ∞) :
    IsPseudoCoherentOver R M m ↔
      ∃ (n : ℕ → ℕ) (d : ∀ i, (Fin (n (i + 1)) → R) →ₗ[R] (Fin (n i) → R))
        (ε : (Fin (n 0) → R) →ₗ[R] M),
        Function.Surjective ε ∧ (1 ≤ m → Function.Exact (d 0) ε) ∧
          ∀ i : ℕ, ((i + 2 : ℕ) : ℕ∞) ≤ m → Function.Exact (d (i + 1)) (d i) :=
  Iff.rfl

end Definition

namespace IsPseudoCoherentOver

variable {R : Type u} {M : Type v} {N : Type w} [Ring R] [AddCommGroup M] [Module R M]
  [AddCommGroup N] [Module R N] {m : ℕ∞}

/-- An `m`-pseudocoherent module is `m'`-pseudocoherent for every `m' ≤ m`. -/
theorem mono {m' : ℕ∞} (h : IsPseudoCoherentOver R M m) (hm : m' ≤ m) :
    IsPseudoCoherentOver R M m' := by
  obtain ⟨n, d, ε, hε, h₀, hd⟩ := h
  exact ⟨n, d, ε, hε, fun h₁ ↦ h₀ (h₁.trans hm), fun i hi ↦ hd i (hi.trans hm)⟩

/-- Pseudocoherence is invariant under linear equivalence. -/
theorem of_equiv (e : M ≃ₗ[R] N) (h : IsPseudoCoherentOver R M m) :
    IsPseudoCoherentOver R N m := by
  obtain ⟨n, d, ε, hε, h₀, hd⟩ := h
  exact ⟨n, d, e.toLinearMap ∘ₗ ε, e.surjective.comp hε,
    fun h₁ ↦ e.postcomp_exact_iff_exact.mpr (h₀ h₁), hd⟩

/-- A pseudocoherent module, in any degree, is finitely generated. -/
theorem finite (h : IsPseudoCoherentOver R M m) : Module.Finite R M := by
  obtain ⟨_, _, ε, hε, _⟩ := h
  exact .of_surjective ε hε

/-- `0`-pseudocoherent means finitely generated. -/
@[simp]
theorem zero_iff : IsPseudoCoherentOver R M 0 ↔ Module.Finite R M := by
  refine ⟨finite, fun _ ↦ ?_⟩
  obtain ⟨k, ε, hε⟩ := Module.Finite.exists_fin' R M
  exact ⟨fun _ ↦ k, fun _ ↦ 0, ε, hε, fun h ↦ absurd h (by simp), fun i hi ↦ absurd hi (by simp)⟩

/-- **Pseudocoherence one degree at a time.** `M` is `(m + 1)`-pseudocoherent exactly when there is
a surjection onto `M` from a finite free module whose kernel is `m`-pseudocoherent. -/
theorem succ_iff :
    IsPseudoCoherentOver R M (m + 1) ↔ ∃ (k : ℕ) (f : (Fin k → R) →ₗ[R] M),
      Function.Surjective f ∧ IsPseudoCoherentOver R (ker f) m := by
  constructor
  · rintro ⟨n, d, ε, hε, h₀, hd⟩
    have hex : Function.Exact (d 0) ε := h₀ le_add_self
    refine ⟨n 0, ε, hε, fun i ↦ n (i + 1), fun i ↦ d (i + 1),
      (d 0).codRestrict (ker ε) fun x ↦ hex.apply_apply_eq_zero x, ?_, fun h₁ ↦ ?_, fun i hi ↦ ?_⟩
    · rintro ⟨x, hx⟩
      obtain ⟨y, rfl⟩ := (hex x).mp hx
      exact ⟨y, rfl⟩
    · exact fun x ↦ Subtype.ext_iff.trans (hd 0 (by
        rw [Nat.cast_add_one, ENat.add_le_add_iff_right ENat.one_ne_top]; simpa using h₁) x)
    · exact hd (i + 1) (by rwa [Nat.cast_add_one, ENat.add_le_add_iff_right ENat.one_ne_top])
  · rintro ⟨k, f, hf, n, d, ε, hε, h₀, hd⟩
    have hf₀ := hε.comp_exact_iff_exact.mpr (exact_subtype_ker_map f)
    refine ⟨fun | 0 => k | i + 1 => n i, fun | 0 => (ker f).subtype ∘ₗ ε | i + 1 => d i, f, hf,
      fun _ ↦ hf₀, fun i hi ↦ ?_⟩
    rcases i with _ | i
    · rw [Nat.cast_add_one, ENat.add_le_add_iff_right ENat.one_ne_top] at hi
      exact (Submodule.injective_subtype _).comp_exact_iff_exact.mpr (h₀ (by simpa using hi))
    · rw [Nat.cast_add_one, ENat.add_le_add_iff_right ENat.one_ne_top] at hi
      exact hd i hi

/-- The kernel of `g ∘ e` for a linear equivalence `e` is equivalent to the kernel of `g`. -/
private theorem ker_comp_equiv_iff {F F' : Type*} [AddCommGroup F] [Module R F] [AddCommGroup F']
    [Module R F'] (g : F' →ₗ[R] M) (e : F ≃ₗ[R] F') :
    IsPseudoCoherentOver R (ker (g ∘ₗ e.toLinearMap)) m ↔ IsPseudoCoherentOver R (ker g) m := by
  have h : (ker (g ∘ₗ e.toLinearMap)).map e.toLinearMap = ker g := by
    rw [ker_comp, Submodule.map_comap_eq_of_surjective e.surjective]
  exact ⟨of_equiv (e.ofSubmodules _ _ h), of_equiv (e.ofSubmodules _ _ h).symm⟩

/-- A surjection from a finite free module with `m`-pseudocoherent kernel makes the target
`(m + 1)`-pseudocoherent. -/
private theorem succ_of_ker {F : Type*} [AddCommGroup F] [Module R F] [Module.Free R F]
    [Module.Finite R F] {f : F →ₗ[R] M} (hf : Function.Surjective f)
    (h : IsPseudoCoherentOver R (ker f) m) : IsPseudoCoherentOver R M (m + 1) := by
  let e : F ≃ₗ[R] (Fin _ → R) :=
    ((Module.Free.chooseBasis R F).reindex (Fintype.equivFin _)).equivFun
  exact succ_iff.mpr ⟨_, f ∘ₗ e.symm.toLinearMap, hf.comp e.symm.surjective,
    (ker_comp_equiv_iff f e.symm).mpr h⟩

/-- **Finitely generated projective modules are `⊤`-pseudocoherent.** -/
theorem of_projective [Module.Finite R M] [Module.Projective R M] :
    IsPseudoCoherentOver R M ⊤ := by
  -- For a splitting `π ∘ s = id` of a surjection `π : Rᵏ → M`, the idempotent `e = s ∘ π` gives
  -- the periodic resolution `⋯ → Rᵏ → Rᵏ → M → 0` with differentials alternating between
  -- `1 - e` and `e`.
  obtain ⟨k, π, s, hπ, hs, hπs⟩ := Module.Finite.exists_comp_eq_id_of_projective R M
  have he : IsIdempotentElem (s ∘ₗ π) := by
    rw [IsIdempotentElem, Module.End.mul_eq_comp, comp_assoc, ← comp_assoc π, hπs, id_comp]
  have hker : ker π = ker (s ∘ₗ π) := by
    rw [ker_comp, ker_eq_bot.mpr hs, Submodule.comap_bot]
  refine ⟨fun _ ↦ k, fun i ↦ if Even i then 1 - s ∘ₗ π else s ∘ₗ π, π, hπ, fun _ ↦ ?_,
    fun i _ ↦ ?_⟩
  · rw [exact_iff, hker, he.ker_eq_range_one_sub]
    simp
  · rw [exact_iff]
    rcases Nat.even_or_odd i with hi | hi
    · simpa [hi, Nat.even_add_one] using he.range_eq_ker_one_sub.symm
    · simpa [Nat.not_even_iff_odd.mpr hi, Nat.even_add_one, Nat.not_even_iff_odd]
        using he.ker_eq_range_one_sub

/-- `1`-pseudocoherent means finitely presented. -/
@[simp]
theorem one_iff : IsPseudoCoherentOver R M 1 ↔ Module.FinitePresentation R M := by
  rw [← zero_add (1 : ℕ∞), succ_iff]
  constructor
  · rintro ⟨k, f, hf, h⟩
    have := zero_iff.mp h
    exact Module.finitePresentation_of_surjective f hf (Module.Finite.iff_fg.mp this)
  · intro _
    obtain ⟨k, f, hf⟩ := Module.Finite.exists_fin' R M
    exact ⟨k, f, hf, zero_iff.mpr
      (Module.Finite.iff_fg.mpr (Module.FinitePresentation.fg_ker f hf))⟩

/-- A module that is pseudocoherent in some positive degree is finitely presented. -/
theorem finitePresentation (h : IsPseudoCoherentOver R M m) (hm : 1 ≤ m) :
    Module.FinitePresentation R M :=
  one_iff.mp (h.mono hm)

/-! ### Products, and cancellation of free summands, in finite degrees

Kernels of maps between finite free modules lie in the universe of the ring, so the inductions on
the degree run there. A finitely generated module `M` is equivalent to a quotient of some `Rᵏ`,
which lies in that universe. -/

private theorem prod_nat_aux : ∀ (n : ℕ) {N₁ N₂ : Type u} [AddCommGroup N₁] [Module R N₁]
    [AddCommGroup N₂] [Module R N₂], IsPseudoCoherentOver R N₁ n →
      IsPseudoCoherentOver R N₂ n → IsPseudoCoherentOver R (N₁ × N₂) n
  | 0, _, _, _, _, _, _, h₁, h₂ => by
    have := zero_iff.mp h₁
    have := zero_iff.mp h₂
    exact zero_iff.mpr inferInstance
  | n + 1, _, _, _, _, _, _, h₁, h₂ => by
    rw [Nat.cast_succ, succ_iff] at h₁ h₂
    obtain ⟨a, f₁, hf₁, h₁⟩ := h₁
    obtain ⟨b, f₂, hf₂, h₂⟩ := h₂
    rw [Nat.cast_succ]
    exact succ_of_ker (Prod.map_surjective.mpr ⟨hf₁, hf₂⟩) ((prod_nat_aux n h₁ h₂).of_equiv
      ((LinearEquiv.ofEq _ _ (ker_prodMap f₁ f₂)).trans (Submodule.prodEquiv _ _)).symm)

private theorem prod_nat {n : ℕ} (h₁ : IsPseudoCoherentOver R M n)
    (h₂ : IsPseudoCoherentOver R N n) : IsPseudoCoherentOver R (M × N) n := by
  have := h₁.finite
  have := h₂.finite
  obtain ⟨_, f₁, hf₁⟩ := Module.Finite.exists_fin' R M
  obtain ⟨_, f₂, hf₂⟩ := Module.Finite.exists_fin' R N
  let e₁ := f₁.quotKerEquivOfSurjective hf₁
  let e₂ := f₂.quotKerEquivOfSurjective hf₂
  exact (prod_nat_aux n (h₁.of_equiv e₁.symm) (h₂.of_equiv e₂.symm)).of_equiv (e₁.prodCongr e₂)

/-- **The Schanuel step.** If free summands can be cancelled in degree `n`, then the kernel of a
surjection `f` from a finitely generated projective module `P` onto an `(n + 1)`-pseudocoherent
module `M` is `n`-pseudocoherent. Compare `f` with a surjection `g : Rᵃ → M` whose kernel is
`n`-pseudocoherent: by Schanuel's lemma `ker f × Rᵃ ≃ P × ker g`, and the right-hand side is
`n`-pseudocoherent. -/
private theorem ker_nat_of_cancel {n : ℕ} {P : Type w} [AddCommGroup P] [Module R P]
    [Module.Finite R P] [Module.Projective R P]
    (hcancel : ∀ (K : Type w) [AddCommGroup K] [Module R K] (a : ℕ),
      IsPseudoCoherentOver R (K × (Fin a → R)) n → IsPseudoCoherentOver R K n)
    (hM : IsPseudoCoherentOver R M (n + 1 : ℕ)) {f : P →ₗ[R] M} (hf : Function.Surjective f) :
    IsPseudoCoherentOver R (ker f) n := by
  rw [Nat.cast_succ, succ_iff] at hM
  obtain ⟨a, g, hg, hK⟩ := hM
  obtain ⟨e, he⟩ := exists_linearEquiv_comp_fst_eq_comp_snd_comp (a := f) (b := g)
    (by rw [range_eq_top.mpr hf, range_eq_top.mpr hg])
  have hsnd : ker (g ∘ₗ snd R P (Fin a → R)) = (⊤ : Submodule R P).prod (ker g) := by
    rw [ker_comp, Submodule.comap_snd]
  have hfst : ker (f ∘ₗ fst R P (Fin a → R)) = (ker f).prod ⊤ := by
    rw [ker_comp, Submodule.comap_fst]
  have h₁ : IsPseudoCoherentOver R (ker (g ∘ₗ snd R P (Fin a → R))) n :=
    (prod_nat (of_projective.mono le_top) hK).of_equiv ((LinearEquiv.ofEq _ _ hsnd).trans
      ((Submodule.prodEquiv _ _).trans
        (Submodule.topEquiv.prodCongr (LinearEquiv.refl R _)))).symm
  have h₂ : IsPseudoCoherentOver R (ker (f ∘ₗ fst R P (Fin a → R))) n := by
    rw [he, ← comp_assoc]
    exact (ker_comp_equiv_iff _ e).mpr h₁
  exact hcancel _ a (h₂.of_equiv ((LinearEquiv.ofEq _ _ hfst).trans
    ((Submodule.prodEquiv _ _).trans ((LinearEquiv.refl R _).prodCongr Submodule.topEquiv))))

/-- Cancellation of free summands in the universe of the ring, by induction on the degree: for a
surjection `g : Rᵇ → K`, the kernel of `g × id : Rᵇ × Rᵃ → K × Rᵃ` is `ker g`, and it is
`n`-pseudocoherent by the Schanuel step. -/
private theorem cancel_nat_aux : ∀ (n : ℕ) (K : Type u) [AddCommGroup K] [Module R K] (a : ℕ),
    IsPseudoCoherentOver R (K × (Fin a → R)) n → IsPseudoCoherentOver R K n
  | 0, _, _, _, a, h =>
    have := h.finite
    zero_iff.mpr (.of_surjective (fst R _ (Fin a → R)) Prod.fst_surjective)
  | n + 1, K, _, _, a, h => by
    have := h.finite
    have := Module.Finite.of_surjective (fst R K (Fin a → R)) Prod.fst_surjective
    obtain ⟨b, g, hg⟩ := Module.Finite.exists_fin' R K
    have hk := ker_nat_of_cancel (cancel_nat_aux n) h
      (f := g.prodMap (LinearMap.id : _ →ₗ[R] (Fin a → R)))
      (Prod.map_surjective.mpr ⟨hg, Function.surjective_id⟩)
    have hker : ker (g.prodMap (LinearMap.id : _ →ₗ[R] (Fin a → R))) = (ker g).prod ⊥ := by
      rw [ker_prodMap, ker_id]
    rw [Nat.cast_succ, succ_iff]
    exact ⟨b, g, hg, hk.of_equiv ((LinearEquiv.ofEq _ _ hker).trans
      ((Submodule.prodEquiv _ _).trans LinearEquiv.prodUnique))⟩

/-- **Cancellation of free summands**: if `M × Rᵃ` is `n`-pseudocoherent, so is `M`. -/
private theorem cancel_nat {n a : ℕ} (h : IsPseudoCoherentOver R (M × (Fin a → R)) n) :
    IsPseudoCoherentOver R M n := by
  have := h.finite
  have := Module.Finite.of_surjective (fst R M (Fin a → R)) Prod.fst_surjective
  obtain ⟨_, f, hf⟩ := Module.Finite.exists_fin' R M
  let e := f.quotKerEquivOfSurjective hf
  exact (cancel_nat_aux n _ a (h.of_equiv (e.symm.prodCongr (.refl R _)))).of_equiv e

private theorem ker_nat {n : ℕ} {P : Type w} [AddCommGroup P] [Module R P]
    [Module.Finite R P] [Module.Projective R P] (hM : IsPseudoCoherentOver R M (n + 1 : ℕ))
    {f : P →ₗ[R] M} (hf : Function.Surjective f) : IsPseudoCoherentOver R (ker f) n :=
  ker_nat_of_cancel (fun _ _ _ _ h ↦ cancel_nat h) hM hf

/-! ### Pseudocoherence in every finite degree -/

/-- **Pseudocoherence is pseudocoherence in every finite degree.** `M` is `⊤`-pseudocoherent
exactly when it is `m`-pseudocoherent for every natural number `m` (Stacks, Tag 064U). -/
theorem top_iff : IsPseudoCoherentOver R M ⊤ ↔ ∀ m : ℕ, IsPseudoCoherentOver R M m := by
  refine ⟨fun h m ↦ h.mono le_top, fun h ↦ ?_⟩
  -- A resolution is built one step at a time: the kernel of each chosen surjection from a finite
  -- free module is again pseudocoherent in every finite degree.
  have := (h 0).finite
  obtain ⟨a, f₀, hf₀⟩ := Module.Finite.exists_fin' R M
  -- The stages: submodules of finite free modules, pseudocoherent in every finite degree.
  let S := {s : Σ k : ℕ, Submodule R (Fin k → R) // ∀ n : ℕ, IsPseudoCoherentOver R s.2 n}
  have hstep (s : S) : ∃ (b : ℕ) (d : (Fin b → R) →ₗ[R] (Fin s.1.1 → R)),
      range d = s.1.2 ∧ ∀ n : ℕ, IsPseudoCoherentOver R (ker d) n := by
    obtain ⟨⟨k, K⟩, hK⟩ := s
    have := (hK 0).finite
    obtain ⟨b, π, hπ⟩ := Module.Finite.exists_fin' R K
    refine ⟨b, K.subtype ∘ₗ π, ?_, fun n ↦ ?_⟩
    · rw [range_comp, range_eq_top.mpr hπ, Submodule.map_top, Submodule.range_subtype]
    · rw [ker_comp, Submodule.ker_subtype, Submodule.comap_bot]
      exact ker_nat (hK (n + 1)) hπ
  choose b d hrange hker using hstep
  -- The `i`-th stage is the kernel of the `i`-th differential, and the next differential is a
  -- chosen surjection onto it.
  let stage : ℕ → S := fun i ↦ Nat.rec ⟨⟨a, ker f₀⟩, fun n ↦ ker_nat (h (n + 1)) hf₀⟩
    (fun _ s ↦ ⟨⟨b s, ker (d s)⟩, hker s⟩) i
  exact ⟨fun i ↦ (stage i).1.1, fun i ↦ d (stage i), f₀, hf₀,
    fun _ ↦ exact_iff.mpr (hrange (stage 0)).symm,
    fun i _ ↦ exact_iff.mpr (hrange (stage (i + 1))).symm⟩

/-- **Products of `m`-pseudocoherent modules are `m`-pseudocoherent.** -/
theorem prod (h₁ : IsPseudoCoherentOver R M m) (h₂ : IsPseudoCoherentOver R N m) :
    IsPseudoCoherentOver R (M × N) m := by
  induction m using ENat.recTopCoe with
  | top => exact top_iff.mpr fun n ↦ prod_nat (top_iff.mp h₁ n) (top_iff.mp h₂ n)
  | coe n => exact prod_nat h₁ h₂

/-- **Kernels of surjections from projective modules.** If `M` is `(m + 1)`-pseudocoherent, the
kernel of every surjection onto `M` from a finitely generated projective module is
`m`-pseudocoherent. -/
theorem ker_of_projective {P : Type*} [AddCommGroup P] [Module R P] [Module.Finite R P]
    [Module.Projective R P] (h : IsPseudoCoherentOver R M (m + 1)) {f : P →ₗ[R] M}
    (hf : Function.Surjective f) : IsPseudoCoherentOver R (ker f) m := by
  induction m using ENat.recTopCoe with
  | top =>
    rw [top_add] at h
    exact top_iff.mpr fun n ↦ ker_nat (top_iff.mp h (n + 1)) hf
  | coe n => exact ker_nat (by rwa [Nat.cast_succ]) hf

/-- For a surjection `f` onto `M` from a finite free module, `M` is `(m + 1)`-pseudocoherent
exactly when `ker f` is `m`-pseudocoherent (Stacks, Tag 064T, with the index negated). -/
theorem succ_iff_ker {F : Type*} [AddCommGroup F] [Module R F] [Module.Free R F]
    [Module.Finite R F] {f : F →ₗ[R] M} (hf : Function.Surjective f) :
    IsPseudoCoherentOver R M (m + 1) ↔ IsPseudoCoherentOver R (ker f) m :=
  ⟨fun h ↦ h.ker_of_projective hf, succ_of_ker hf⟩

private theorem of_isNoetherianRing_aux [IsNoetherianRing R] : ∀ (n : ℕ) (K : Type u)
    [AddCommGroup K] [Module R K] [Module.Finite R K], IsPseudoCoherentOver R K n
  | 0, _, _, _, _ => zero_iff.mpr ‹_›
  | n + 1, K, _, _, _ => by
    obtain ⟨k, f, hf⟩ := Module.Finite.exists_fin' R K
    have : Module.Finite R (ker f) := Module.Finite.iff_fg.mpr (IsNoetherian.noetherian _)
    rw [Nat.cast_succ]
    exact succ_iff.mpr ⟨k, f, hf, of_isNoetherianRing_aux n _⟩

/-- **Over a noetherian ring, finitely generated modules are pseudocoherent** (Stacks,
Tag 066E). -/
theorem of_isNoetherianRing [IsNoetherianRing R] [Module.Finite R M] :
    IsPseudoCoherentOver R M ⊤ := by
  obtain ⟨_, f, hf⟩ := Module.Finite.exists_fin' R M
  exact top_iff.mpr fun n ↦ (of_isNoetherianRing_aux n _).of_equiv (f.quotKerEquivOfSurjective hf)

end IsPseudoCoherentOver

end TauCeti.Huber
