/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import Mathlib.RingTheory.Filtration

/-!
# Consequences of the Artin–Rees lemma for `I`-adic filtrations

Mathlib's Artin–Rees lemma, `Ideal.exists_pow_inf_eq_pow_smul`, compares the `I`-adic filtration
of a module with the filtration it induces on a submodule. This file draws two consequences that
the adic theory uses: lifting through a surjection with control on the filtration, and the
Artin–Rees lemma for a finitely generated submodule of an arbitrary module, comparing the
filtration it induces on another submodule with that submodule's `I`-adic filtration.

Fix a submodule `N` of a finite module `M` over a noetherian ring. Then **one shift `k₀` serves
every surjection onto `N` and every depth at once**: for any module `P` and any surjection
`φ : P →ₗ[R] N`, an element of `N` lying `k₀` steps deeper than `m` in the *ambient* filtration
of `M` is the image under `φ` of something at depth `m` in `P`.

The order of quantifiers is the content. `k₀` comes from `Ideal.exists_pow_inf_eq_pow_smul`,
which mentions only `I` and `N`, so it is bound outside `P` and `φ`; a statement giving a
constant only after the surjection is fixed would be strictly weaker and would not compose.

The shift is what makes the statement useful and what makes it non-trivial. Membership in
`I ^ n • ⊤` is measured in `M`, while a lift is constrained by the filtration `N` inherits, and
those two differ; Artin–Rees is exactly the input that bounds the discrepancy by a constant
independent of `n`. Without the shift the statement is false in general.

Nothing here is topological or adic-space-specific — it is filtration algebra over an arbitrary
commutative noetherian ring — so it sits beside Mathlib's own Artin–Rees material rather than in
the Huber development that consumes it.

## Main results

* `TauCeti.ArtinRees.exists_controlled_lift`: there is a shift depending only on `I` and the
  submodule — quantified before the surjection — for which every surjection onto that submodule
  admits lifts with control on the `I`-adic filtration.
* `Submodule.map_subtype_smul_top_inf_comap`: transport of the filtration induced by
  `J • ⊤` from a submodule `N₀` to the ambient module, where it becomes `J • N₀ ⊓ L`.
* `Ideal.exists_pow_add_smul_inf_eq_pow_smul`: for `N₀` finitely generated, one shift
  `k` gives `I ^ (n + k) • N₀ ⊓ L = I ^ n • (I ^ k • N₀ ⊓ L)` for all `n`; this is the form used
  to compare natural topologies of finite modules over Huber rings.

## Provenance

Adapted from AINTLIB's `ArtinRees.controlled_lift`, branch `dev/adic-spaces`, commit `37bbdaeb`,
Apache-2.0, Chris Birkbeck, `projects/AdicSpaces/Adic spaces/ArtinReesConvergence.lean`, whose
reference is given there as Wedhorn Lemma 8.31. Note that the TauCeti roadmap assigns that
number to a different statement — `A⟨X⟩` faithfully flat over `A`, in
`AdicSpaces/README.md` — so the citation below is the source's own attribution, not a
roadmap node. Two generalisations:

* the source fixes the ambient module to `Fin l → R` and the source of the surjection to
  `Fin k → R`, presenting the map as `∑ j, c j • s j` for a chosen spanning family; here the
  ambient module, the source and the map are arbitrary, since the proof uses only surjectivity.
  The source's `surjMap` and its two lemmas are consequently dropped — that map is Mathlib's
  `Fintype.linearCombination`, and the image computation is `Submodule.map_smul''` composed with
  `Submodule.map_top`;
* the source takes the Artin–Rees conclusion as a hypothesis `hAR` together with the constant
  `k₀`; here both come from `Ideal.exists_pow_inf_eq_pow_smul`, so no caller has to supply them.

One declaration is not ported: the source's `pi_smul_top_component`, which has no consumer.

## References

* [T. Wedhorn, *Adic Spaces*][wedhorn_adic] (arXiv:1910.05934v1), Lemma 8.31.
* [C. Birkbeck, *AINTLIB*](https://github.com/CBirkbeck/AINTLIB), branch `dev/adic-spaces`,
  commit `37bbdaeb`, `projects/AdicSpaces/Adic spaces/ArtinReesConvergence.lean`.
-/

public section

namespace TauCeti.ArtinRees

variable {R : Type*} [CommRing R] {M : Type*} [AddCommGroup M] [Module R M]

/-- **Artin–Rees controlled lift.** For an ideal `I` and a submodule `N` of a finite module over a
noetherian ring there is a shift `k₀` — depending on `I` and `N` alone, so independent of both
the depth and the surjection — such that for every surjection `φ` onto `N`, every `v : N` whose
image in `M` lies in `I ^ (m + k₀) • ⊤` has a `φ`-preimage in `I ^ m • ⊤`. -/
theorem exists_controlled_lift [IsNoetherianRing R] [Module.Finite R M] (I : Ideal R)
    (N : Submodule R M) :
    ∃ k₀ : ℕ, ∀ {P : Type*} [AddCommGroup P] [Module R P] (φ : P →ₗ[R] N),
      Function.Surjective φ → ∀ (m : ℕ) (v : N),
        (v : M) ∈ (I ^ (m + k₀) • ⊤ : Submodule R M) →
          ∃ c ∈ (I ^ m • ⊤ : Submodule R P), φ c = v := by
  obtain ⟨k₀, hAR⟩ := I.exists_pow_inf_eq_pow_smul N
  refine ⟨k₀, fun {P} _ _ φ hφ m v hv ↦ ?_⟩
  -- Artin–Rees turns ambient depth `m + k₀` into depth `m` for the filtration induced on `N`
  have hv_inf : (v : M) ∈ I ^ (m + k₀) • ⊤ ⊓ N := ⟨hv, v.prop⟩
  rw [hAR (m + k₀) (Nat.le_add_left k₀ m), Nat.add_sub_cancel] at hv_inf
  have hv_smul_N : (v : M) ∈ I ^ m • N := (Submodule.smul_mono le_rfl inf_le_right) hv_inf
  have hv_top : v ∈ (I ^ m • ⊤ : Submodule R N) :=
    (Submodule.mem_smul_top_iff (I ^ m) N v).mpr hv_smul_N
  -- a surjection carries `I ^ m • ⊤` onto `I ^ m • ⊤`, so the lift can be taken at depth `m`
  have hmap : (I ^ m • ⊤ : Submodule R P).map φ = (I ^ m • ⊤ : Submodule R N) := by
    rw [Submodule.map_smul'', Submodule.map_top, LinearMap.range_eq_top.mpr hφ]
  rw [← hmap] at hv_top
  exact Submodule.mem_map.mp hv_top

end TauCeti.ArtinRees

variable {R : Type*} [CommRing R] {M : Type*} [AddCommGroup M] [Module R M]

namespace Submodule

/-- Pushing the filtration that `J • ⊤` induces on `L ∩ N₀`, viewed inside `N₀`, forward along
the inclusion `N₀ → M` gives `J • N₀ ⊓ L`. -/
@[simp]
theorem map_subtype_smul_top_inf_comap (N₀ : Submodule R M) (J : Ideal R) (L : Submodule R M) :
    (J • ⊤ ⊓ L.comap N₀.subtype).map N₀.subtype = J • N₀ ⊓ L := by
  rw [Submodule.map_inf _ N₀.injective_subtype, Submodule.map_smul'', Submodule.map_top,
    Submodule.range_subtype, Submodule.map_comap_subtype, ← inf_assoc,
    inf_eq_left.mpr Submodule.smul_le_right]

end Submodule

namespace Ideal

/-- **Artin–Rees for a finitely generated submodule.** If `N₀` is a finitely generated submodule
over a noetherian ring, there is a shift `k` such that `I ^ (n + k) • N₀ ⊓ L` equals
`I ^ n • (I ^ k • N₀ ⊓ L)` for every submodule `L` and every `n`. The ambient module need not be
finite: only `N₀` is, so Mathlib's `Ideal.exists_pow_inf_eq_pow_smul` is applied inside `N₀`.
In particular `I ^ (n + k) • N₀ ⊓ L ≤ I ^ n • L`; when `L ≤ N₀`, this shows that the
filtration `N₀` induces on `L` is cofinal in the `I`-adic filtration of `L`. -/
theorem exists_pow_add_smul_inf_eq_pow_smul [IsNoetherianRing R] (I : Ideal R)
    {N₀ : Submodule R M} (hN₀ : N₀.FG) (L : Submodule R M) :
    ∃ k : ℕ, ∀ n : ℕ, I ^ (n + k) • N₀ ⊓ L = I ^ n • (I ^ k • N₀ ⊓ L) := by
  have : Module.Finite R N₀ := Module.Finite.iff_fg.mpr hN₀
  obtain ⟨k, hk⟩ := I.exists_pow_inf_eq_pow_smul (L.comap N₀.subtype)
  refine ⟨k, fun n ↦ ?_⟩
  -- Artin–Rees inside `N₀`, transported to `M` along the inclusion `N₀ → M`.
  have h := congrArg (Submodule.map N₀.subtype) (hk (n + k) (Nat.le_add_left k n))
  rwa [Submodule.map_subtype_smul_top_inf_comap, Nat.add_sub_cancel, Submodule.map_smul'',
    Submodule.map_subtype_smul_top_inf_comap] at h

end Ideal

end
