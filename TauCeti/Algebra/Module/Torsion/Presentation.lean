/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Module.Torsion.PrimaryComponent

/-!
# Cyclic presentations of ideal-power torsion modules

An `I`-power torsion module is precisely a quotient of a direct sum of modules `R / Iⁿ`.
No finite generation or Noetherianity is required. Such a presentation reduces extension
problems for arbitrary torsion modules to extension problems for the cyclic quotients.
The module of relations is again `I`-power torsion: the presenting direct sum is torsion,
and primary components commute with restriction to submodules.

## References

* [Stacks Project, Lemma 15.90.2](https://stacks.math.columbia.edu/tag/05E8).
* [Stacks Project, Lemma 15.91.8](https://stacks.math.columbia.edu/tag/05EG), for the reduction
  of extension descent to direct sums of cyclic quotients.
-/

public section

open DirectSum Submodule

universe u v

namespace Ideal

variable {R : Type u} [CommRing R] (I : Ideal R)

/-- A module is `I`-power torsion if and only if it is a quotient of a direct sum of cyclic
modules `R / Iⁿ`. The summands may have different exponents, and no finiteness assumptions on
the ring, ideal, or module are needed. -/
@[stacks 05E8 "the cyclic-quotient presentation, with its converse"]
theorem primaryComponent_eq_top_iff_exists_surjective_directSum_quotient_pow
    {M : Type v} [AddCommGroup M] [Module R M] :
    I.primaryComponent M = ⊤ ↔
      ∃ (ι : Type v) (n : ι → ℕ) (π : (⨁ i : ι, R ⧸ I ^ n i) →ₗ[R] M),
        Function.Surjective π := by
  constructor
  · intro hM
    classical
    have hm (m : M) : ∃ n, m ∈ torsionBySet R M ↑(I ^ n) :=
      (I.primaryComponent_mem M m).mp (hM ▸ mem_top)
    choose n hn using hm
    let f (m : M) : (R ⧸ I ^ n m) →ₗ[R] M :=
      (I ^ n m).liftQ (LinearMap.toSpanSingleton R M m) fun r hr ↦
        LinearMap.mem_ker.mpr (by
          simpa only [LinearMap.toSpanSingleton_apply] using
            (mem_torsionBySet_iff _ _).mp (hn m) ⟨r, hr⟩)
    refine ⟨M, n, toModule R M M f, fun m ↦ ⟨lof R M _ m (Ideal.Quotient.mk _ 1), ?_⟩⟩
    rw [toModule_lof]
    dsimp only [f]
    rw [← Ideal.Quotient.mk_eq_mk, Submodule.liftQ_apply]
    simp
  · rintro ⟨ι, n, π, hπ⟩
    have hP := I.primaryComponent_directSum_eq_top fun i ↦
      I.primaryComponent_quotient_pow_eq_top (n i)
    refine eq_top_iff'.mpr fun m ↦ ?_
    obtain ⟨x, rfl⟩ := hπ m
    exact I.primaryComponent_map_mem π ⟨x, hP ▸ mem_top⟩

end Ideal
