/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Exact.Abelian
public import TauCeti.CategoryTheory.Exact.Resolution.ChainComplex
public import TauCeti.RingTheory.CohenMacaulay.Basic

/-!
# Free resolutions ending in a maximal Cohen–Macaulay module

Let `R` be a Noetherian local ring and `M` a finite `R`-module. Resolving `M` by finite free
modules raises the depth of the syzygies: in a short exact sequence `0 → K → F → M → 0` with `F`
finite free, the depth lemma gives `depth K ≥ min (depth R, depth M + 1)`. After `n` steps with
`depth R ≤ depth M + n`, the syzygy reached has depth at least `depth R`.

Over a Cohen–Macaulay local ring of dimension `d`, this says that a finite module of depth `e`
has an exact complex `0 → K → F_{d-e-1} → ⋯ → F₀ → M → 0` with finite free terms `Fᵢ` and with `K`
finite of depth at least `d`. A finite module of depth at least `d` is zero or maximal
Cohen–Macaulay, since its depth is at most the dimension of its support; this is Stacks,
Lemma 10.104.9 (00NG).

The resolutions are `TauCeti.ExactStructure.FiniteResolution`s for the abelian exact structure on
`ModuleCat R`. Their objects all satisfy the resolving property: they are finite of depth at
least `depth R`, respectively at least `d`. This holds for the last syzygy by construction and
for the finite free terms because they have the depth of the ring. The terms other than the last
syzygy are moreover free, which is stated through
`TauCeti.ExactStructure.FiniteResolution.term`.

## Main results

* `TauCeti.exists_finiteResolution_free_of_depth_le_depth_add`: over a Noetherian local ring, if
  `depth R ≤ depth M + n`, then `M` has a finite resolution of length `n` by finite free modules
  whose `n`-th syzygy is finite of depth at least `depth R`.
* `TauCeti.exists_resolution_maximalCohenMacaulay`: the same over a Cohen–Macaulay local ring,
  with `ringKrullDim R` in place of `depth R` (Stacks, Lemma 10.104.9 (00NG)).

## References

* [The Stacks Project, Lemma 10.104.9](https://stacks.math.columbia.edu/tag/00NG).
* [The Stacks Project, Tag 00LX](https://stacks.math.columbia.edu/tag/00LX), the depth lemma.
-/

public section

namespace TauCeti

open CategoryTheory IsLocalRing

universe u

variable {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]

/-- Over a Noetherian local ring, a finite module `M` with `depth R ≤ depth M + n` has a finite
resolution of length `n` by finite free modules whose `n`-th syzygy is a finite module of depth at
least `depth R`. Every object of the resolution is finite of depth at least `depth R`. -/
theorem exists_finiteResolution_free_of_depth_le_depth_add (M : ModuleCat.{u} R)
    [Module.Finite R M] {n : ℕ} (h : depth (ModuleCat.of R R) ≤ depth M + n) :
    ∃ r : (ExactStructure.abelian (ModuleCat.{u} R)).FiniteResolution
        (fun N ↦ Module.Finite R N ∧ depth (ModuleCat.of R R) ≤ depth N) M,
      r.length = n ∧ ∀ i < n, Module.Free R (r.term i) := by
  induction n generalizing M with
  | zero => exact ⟨.base ⟨inferInstance, by simpa using h⟩, by simp, by simp⟩
  | succ n ih =>
    obtain ⟨d, f, hf⟩ := Module.Finite.exists_fin' R M
    let S := f.shortComplexKer
    have hS : S.ShortExact := f.shortExact_shortComplexKer hf
    have : Module.Finite R S.X₁ := inferInstanceAs (Module.Finite R (LinearMap.ker f))
    -- A finite free module has depth at least that of the ring.
    have hF : depth (ModuleCat.of R R) ≤ depth (ModuleCat.of R (Fin d → R)) := by
      cases subsingleton_or_nontrivial (Fin d → R)
      · simp only [depth, Ideal.depth_eq_top_of_subsingleton, le_top]
      · exact (depth_eq_depth_self_of_free _).ge
    -- The depth lemma for `0 → ker f → Rᵈ → M → 0`.
    have hK := depth_min_snd_trd_add_one_le_fst_of_exact (LinearMap.ker f).subtype f
      (LinearMap.exact_subtype_ker_map f) (LinearMap.ker f).injective_subtype hf
    have hKn : depth (ModuleCat.of R R) ≤ depth S.X₁ + n := by
      refine le_trans ?_ (add_le_add hK le_rfl)
      rcases le_total (depth (ModuleCat.of R (Fin d → R))) (depth M + 1) with hle | hle
      · rw [inf_eq_left.2 hle]
        exact hF.trans le_self_add
      · rw [inf_eq_right.2 hle, add_assoc, add_comm 1]
        simpa using h
    obtain ⟨r, hr, hfree⟩ := ih S.X₁ hKn
    refine ⟨.step ⟨inferInstanceAs (Module.Finite R (Fin d → R)), hF⟩ S.f S.g S.zero
      ((ExactStructure.abelian_conflation S).2 hS) r, by simp [hr], fun i hi ↦ ?_⟩
    cases i with
    | zero => exact inferInstanceAs (Module.Free R (Fin d → R))
    | succ i => exact hfree i (by omega)

/-- **Free resolutions ending in a maximal Cohen–Macaulay module.** Over a Cohen–Macaulay local
ring `R` of dimension `d`, a finite module `M` with `d ≤ depth M + n` has a finite resolution of
length `n` by finite free modules whose `n`-th syzygy is a finite module of depth at least `d`,
so zero or maximal Cohen–Macaulay. Taking `n = d - depth M`, this is an exact complex
`0 → K → F_{n-1} → ⋯ → F₀ → M → 0` with finite free `Fᵢ` and `K` zero or maximal
Cohen–Macaulay. -/
@[stacks 00NG]
theorem exists_resolution_maximalCohenMacaulay (hR : Module.IsCohenMacaulay R R)
    (M : ModuleCat.{u} R) [Module.Finite R M] {n : ℕ}
    (h : ringKrullDim R ≤ (depth M : WithBot ℕ∞) + n) :
    ∃ r : (ExactStructure.abelian (ModuleCat.{u} R)).FiniteResolution
        (fun N ↦ Module.Finite R N ∧ ringKrullDim R ≤ (depth N : WithBot ℕ∞)) M,
      r.length = n ∧ ∀ i < n, Module.Free R (r.term i) := by
  have hd : (depth (ModuleCat.of R R) : WithBot ℕ∞) = ringKrullDim R := by
    rw [hR.depth_eq, Module.supportDim_self_eq_ringKrullDim]
  have hP : (fun N : ModuleCat.{u} R ↦ Module.Finite R N ∧ depth (ModuleCat.of R R) ≤ depth N) =
      fun N : ModuleCat.{u} R ↦ Module.Finite R N ∧ ringKrullDim R ≤ (depth N : WithBot ℕ∞) := by
    ext N
    rw [← hd, WithBot.coe_le_coe]
  rw [← hd] at h
  exact hP ▸ exists_finiteResolution_free_of_depth_le_depth_add M (by exact_mod_cast h)

end TauCeti
