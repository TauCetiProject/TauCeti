/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import Mathlib.RingTheory.Filtration
public import Mathlib.RingTheory.Ideal.Quotient.PowTransition

import TauCeti.RingTheory.Ideal.Operations

/-!
# Consequences of the Artin–Rees lemma for `I`-adic filtrations

Mathlib's Artin–Rees lemma, `Ideal.exists_pow_inf_eq_pow_smul`, compares the `I`-adic filtration
of a module with the filtration it induces on a submodule. This file draws three consequences that
the adic theory uses: lifting through a surjection with control on the filtration, the
Artin–Rees lemma for a finitely generated submodule of an arbitrary module, comparing the
filtration it induces on another submodule with that submodule's `I`-adic filtration, and the
comparison of `Hom` with reduction modulo powers of `I`.

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

For finite modules `M` and `N` over a noetherian ring, the comparison maps
`Hom(M, N) / I ^ n Hom(M, N) → Hom(M, N / I ^ n N)` need not be injective or surjective, but their
kernels and cokernels form pro-zero towers, with one shift `k` for every level. For `R = ℤ`,
`I = (2)`, `M = ℤ / 2` and `N = ℤ`, the source is zero while the target `Hom(ℤ / 2, ℤ / 2ⁿ)` is
`ℤ / 2` for `n ≥ 1`, with zero transition maps. The cokernel half says that a map
`M → N / I ^ (n + k) N`, reduced modulo `I ^ n N`, lifts to a map `M → N`. For an `R`-algebra
`M = S` and `N = R`, it turns an `R`-linear retraction of `R / I ^ (n + k) → S / I ^ (n + k) S`
into an `R`-linear map `S → R` that is a retraction modulo `I ^ n`.

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
* `Ideal.exists_mem_pow_smul_top_of_range_le`: there is a shift `k` such that a linear map between
  finite modules with values in `I ^ (n + k) N` lies in `I ^ n • Hom(M, N)`.
* `Ideal.exists_mkQ_comp_eq_factorPow_comp`: there is a shift `k` such that the reduction modulo
  `I ^ n N` of any linear map `M → N / I ^ (n + k) N` lifts to a linear map `M → N`.

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

* B. Bhatt, *On the direct summand conjecture and its derived variant*, Invent. Math. 212 (2018),
  Lemma 5.3 (the pro-isomorphism comparing `Hom` with reduction modulo powers of `I`).
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

section Hom

variable {N : Type*} [AddCommGroup N] [Module R N]

/-- **Artin–Rees for `Hom`, kernel half.** For finite modules `M` and `N` over a noetherian ring
there is a shift `k` such that, for every `n`, a linear map `M → N` with values in `I ^ (n + k) N`
lies in `I ^ n • Hom(M, N)`. So the kernels of the comparison maps
`Hom(M, N) / I ^ n Hom(M, N) → Hom(M, N / I ^ n N)` form a pro-zero tower. -/
theorem exists_mem_pow_smul_top_of_range_le [IsNoetherianRing R] [Module.Finite R M]
    [Module.Finite R N] (I : Ideal R) :
    ∃ k : ℕ, ∀ (n : ℕ) (f : M →ₗ[R] N), LinearMap.range f ≤ I ^ (n + k) • ⊤ →
      f ∈ I ^ n • (⊤ : Submodule R (M →ₗ[R] N)) := by
  -- Restriction along a surjection `Rᵇ → M` embeds `Hom(M, N)` into the finite module `Hom(Rᵇ, N)`.
  obtain ⟨b, π, hπ⟩ := Module.Finite.exists_fin' R M
  let Ψ : (M →ₗ[R] N) →ₗ[R] (Fin b → R) →ₗ[R] N := LinearMap.lcomp R N π
  obtain ⟨k, hk⟩ := TauCeti.ArtinRees.exists_controlled_lift I (LinearMap.range Ψ)
  refine ⟨k, fun n f hf ↦ ?_⟩
  have hΨf : Ψ f ∈ (I ^ (n + k) • ⊤ : Submodule R ((Fin b → R) →ₗ[R] N)) :=
    (Pi.basisFun R (Fin b)).mem_smul_top_linearMap_iff.mpr fun _ ↦ by
      simpa only [Ψ, LinearMap.lcomp_apply] using hf (LinearMap.mem_range_self f _)
  -- The controlled lift through `Hom(M, N) → range Ψ` gives `g ∈ I ^ n • ⊤` with `Ψ g = Ψ f`.
  obtain ⟨g, hg, hgf⟩ := hk Ψ.rangeRestrict (LinearMap.surjective_rangeRestrict Ψ) n
    ⟨Ψ f, f, rfl⟩ hΨf
  -- `Ψ` is injective because `π` is surjective.
  have hgf' : g ∘ₗ π = f ∘ₗ π := by
    simpa only [Ψ, LinearMap.codRestrict_apply, LinearMap.lcomp_apply'] using
      congrArg Subtype.val hgf
  exact (LinearMap.cancel_right hπ).mp hgf' ▸ hg

/-- **Artin–Rees for `Hom`, cokernel half.** For finite modules `M` and `N` over a noetherian ring
there is a shift `k` such that, for every `n`, the reduction modulo `I ^ n N` of a linear map
`M → N / I ^ (n + k) N` lifts to a linear map `M → N`. So the cokernels of the comparison maps
`Hom(M, N) / I ^ n Hom(M, N) → Hom(M, N / I ^ n N)` form a pro-zero tower. -/
theorem exists_mkQ_comp_eq_factorPow_comp [IsNoetherianRing R] [Module.Finite R M]
    [Module.Finite R N] (I : Ideal R) :
    ∃ k : ℕ, ∀ (n : ℕ) (g : M →ₗ[R] N ⧸ (I ^ (n + k) • ⊤ : Submodule R N)),
      ∃ f : M →ₗ[R] N, (I ^ n • ⊤ : Submodule R N).mkQ ∘ₗ f =
        Submodule.factorPow I N (Nat.le_add_right n k) ∘ₗ g := by
  -- Present `M` as `Rᵃ → Rᵇ → M → 0`, with `κ` spanning the kernel of `π`.
  obtain ⟨b, π, hπ⟩ := Module.Finite.exists_fin' R M
  obtain ⟨a, κ, hκ⟩ := Submodule.fg_iff_exists_fin_generating_family.mp
    (IsNoetherian.noetherian (LinearMap.ker π))
  let K : (Fin a → R) →ₗ[R] Fin b → R := Fintype.linearCombination R κ
  have hK : LinearMap.range K = LinearMap.ker π := by
    rw [Fintype.range_linearCombination, hκ]
  -- Restriction along `K` sends `Hom(Rᵇ, N)` to the finite module `Hom(Rᵃ, N)`.
  let Φ : ((Fin b → R) →ₗ[R] N) →ₗ[R] (Fin a → R) →ₗ[R] N := LinearMap.lcomp R N K
  obtain ⟨k, hk⟩ := TauCeti.ArtinRees.exists_controlled_lift I (LinearMap.range Φ)
  refine ⟨k, fun n g ↦ ?_⟩
  -- Lift `g ∘ π` to `h : Rᵇ → N`; then `h ∘ K` has values in `I ^ (n + k) N`.
  choose h₀ hh₀ using fun j ↦ Submodule.Quotient.mk_surjective _ (g (π (Pi.single j 1)))
  let h := (Pi.basisFun R (Fin b)).constr R h₀
  have hgh : (I ^ (n + k) • ⊤ : Submodule R N).mkQ ∘ₗ h = g ∘ₗ π := by
    ext j
    simp [h, hh₀]
  have hΦh : (Φ h : (Fin a → R) →ₗ[R] N) ∈ (I ^ (n + k) • ⊤ : Submodule R _) := by
    refine (Pi.basisFun R (Fin a)).mem_smul_top_linearMap_iff.mpr fun t ↦ ?_
    have hKt : π (K (Pi.single t 1)) = 0 := by
      rw [← LinearMap.mem_ker, ← hK]
      exact LinearMap.mem_range_self K _
    have := LinearMap.congr_fun hgh (K (Pi.basisFun R (Fin a) t))
    simpa [Φ, hKt, Submodule.Quotient.mk_eq_zero] using this
  -- Artin–Rees corrects `h` by some `c ∈ I ^ n • Hom(Rᵇ, N)` to a map killing `range K = ker π`.
  obtain ⟨c, hc, hΦc⟩ := hk (Φ.rangeRestrict) (LinearMap.surjective_rangeRestrict Φ) n
    ⟨Φ h, h, rfl⟩ hΦh
  have hker : LinearMap.ker π ≤ LinearMap.ker (h - c) := by
    rw [← hK, LinearMap.range_le_ker_iff]
    have : Φ c = Φ h := congrArg Subtype.val hΦc
    simpa [Φ, LinearMap.sub_comp, sub_eq_zero, LinearMap.lcomp_apply'] using this.symm
  -- The corrected map factors through `π`, and agrees with `h` modulo `I ^ n N`.
  refine ⟨π.liftOfSurjective hπ ⟨h - c, hker⟩, (LinearMap.cancel_right hπ).mp ?_⟩
  refine LinearMap.ext fun x ↦ ?_
  have hgx := LinearMap.congr_fun hgh x
  simp only [LinearMap.comp_apply, Submodule.mkQ_apply] at hgx
  simp [← hgx, (Submodule.Quotient.mk_eq_zero _).mpr
    (LinearMap.apply_mem_smul_top_of_mem_smul_top hc x)]

end Hom

end Ideal

end
