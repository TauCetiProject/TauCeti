/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import Mathlib.RingTheory.Filtration
public import TauCeti.Algebra.Module.Torsion.PrimaryComponent

import TauCeti.RingTheory.Ideal.Operations

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
* `Ideal.exists_pow_add_smul_inf_eq_pow_smul`: for `N₀` finitely generated and a submodule `L`,
  one shift `k` gives `I ^ (n + k) • N₀ ⊓ L = I ^ n • (I ^ k • N₀ ⊓ L)` for all `n`; this is the
  form used to compare natural topologies of finite modules over Huber rings.
* `Ideal.exists_pow_smul_sup_linearMap_of_mem_primaryComponent`: over a Noetherian ring, a linear
  map from a submodule of a finite module into `Γ_𝔞(M)` extends by zero on `𝔞ᵐ • ⊤` for some `m`.

## Provenance

Adapted from AINTLIB's `ArtinRees.controlled_lift`, branch `dev/adic-spaces`, commit `37bbdaeb`,
Apache-2.0, Chris Birkbeck, `projects/AdicSpaces/Adic spaces/ArtinReesConvergence.lean`, whose
reference is given there as Wedhorn Lemma 8.31; the citation below is that source's own
attribution. That lemma is not itself an Artin–Rees statement: in arXiv:1910.05934v1 it says
that for a noetherian complete Tate ring `A` the ring `A⟨X⟩` is faithfully flat over `A`, and
that `A⟨X⟩ / (f - X)` and `A⟨X⟩ / (1 - f X)` are flat over `A` for every `f ∈ A`.
Two generalisations:

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

* [T. Wedhorn, *Adic Spaces*][wedhorn_adic] (arXiv:1910.05934v1), Lemma 8.31 (flatness of
  `A⟨X⟩`; cited by the AINTLIB source).
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

namespace Ideal

/-- **Artin–Rees for a finitely generated submodule.** If `N₀` is a finitely generated submodule
over a noetherian ring and `L` is any submodule, there is a shift `k`, depending on `I`, `N₀`
and `L`, such that `I ^ (n + k) • N₀ ⊓ L` equals `I ^ n • (I ^ k • N₀ ⊓ L)` for every `n`.
The ambient module need not be finite: only `N₀` is, so Mathlib's
`Ideal.exists_pow_inf_eq_pow_smul` is applied inside `N₀`.
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

/-- Over a Noetherian commutative ring, any linear map `g : N →ₗ[R] M` from a submodule of a finite
module `P` whose values lie in `𝔞.primaryComponent M` extends to `N ⊔ 𝔞 ^ m • ⊤` (for some `m`)
vanishing on `𝔞 ^ m • ⊤`. -/
theorem exists_pow_smul_sup_linearMap_of_mem_primaryComponent {R P M : Type*} [CommRing R]
    [IsNoetherianRing R] [AddCommGroup P] [Module R P] [Module.Finite R P]
    [AddCommGroup M] [Module R M] (𝔞 : Ideal R) (N : Submodule R P) (g : N →ₗ[R] M)
    (hg : ∀ x, g x ∈ 𝔞.primaryComponent M) :
    ∃ (m : ℕ) (g' : ↥(N ⊔ 𝔞 ^ m • (⊤ : Submodule R P)) →ₗ[R] M),
      (∀ x (hx : x ∈ N), g' ⟨x, Submodule.mem_sup_left hx⟩ = g ⟨x, hx⟩) ∧
      (∀ y (hy : y ∈ 𝔞 ^ m • (⊤ : Submodule R P)), g' ⟨y, Submodule.mem_sup_right hy⟩ = 0) := by
  have : Module.Finite R N := Module.Finite.iff_fg.mpr (IsNoetherian.noetherian N)
  obtain ⟨n, hn⟩ := 𝔞.exists_forall_mem_torsionBySet_pow_of_mem_primaryComponent g hg
  have hker : 𝔞 ^ n • (⊤ : Submodule R N) ≤ LinearMap.ker g :=
    Submodule.smul_le.mpr fun r hr x _ ↦ by
      rw [LinearMap.mem_ker, map_smul]
      exact (Submodule.mem_torsionBySet_iff _ _).mp (hn x) ⟨r, hr⟩
  -- By Artin–Rees, `𝔞^(n + k) • ⊤ ⊓ N ≤ 𝔞^n • N`, on which `g` vanishes.
  obtain ⟨k, hk⟩ := Ideal.exists_pow_inf_eq_pow_smul 𝔞 N
  have hvanish : ∀ x : N, (x : P) ∈ 𝔞 ^ (n + k) • (⊤ : Submodule R P) → g x = 0 := fun x hx ↦ by
    have hmem : (x : P) ∈ 𝔞 ^ n • N := by
      have h := hk (n + k) (Nat.le_add_left k n)
      rw [Nat.add_sub_cancel] at h
      exact Submodule.smul_mono le_rfl inf_le_right (h.le ⟨hx, x.property⟩)
    exact hker ((Submodule.mem_smul_top_iff (𝔞 ^ n) N x).mpr hmem)
  let φ : P →ₗ.[R] M := ⟨N, g⟩
  let ψ : P →ₗ.[R] M := ⟨𝔞 ^ (n + k) • ⊤, 0⟩
  have hagree : ∀ (x : φ.domain) (y : ψ.domain), (x : P) = y → φ x = ψ y := fun x y hxy ↦
    (hvanish x (hxy ▸ y.property)).trans (LinearMap.zero_apply _).symm
  refine ⟨n + k, (φ.sup ψ hagree).toFun, fun x hx ↦ ?_, fun y hy ↦ ?_⟩
  · exact (LinearPMap.sup_apply hagree ⟨x, hx⟩ 0 _ (add_zero x)).trans (by simp [φ, ψ])
  · exact (LinearPMap.sup_apply hagree 0 ⟨y, hy⟩ _ (zero_add y)).trans (by simp [φ, ψ])

end Ideal

end
