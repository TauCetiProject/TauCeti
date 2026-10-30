/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Affinoid.MaximalSpectrum
public import TauCeti.RingTheory.Dagger.GaussNorm
public import TauCeti.RingTheory.MvPowerSeries.TateAlgebra.ClosedIdeal

import TauCeti.RingTheory.Ideal.Quotient.Finite
import TauCeti.RingTheory.MvPowerSeries.TateAlgebra.Groebner
import TauCeti.Topology.Algebra.Module.FiniteDimension
import Mathlib.Analysis.Normed.Ring.Units

/-!
# Maximal ideals of the Monsky–Washnitzer algebra and of the Tate algebra

Let `K` be a complete nontrivially normed ultrametric field, and let `W = K⟨X⟩†` be the
Monsky–Washnitzer algebra in finitely many variables, with its inclusion `toTate` into the Tate
algebra `T = K⟨X⟩`. Contracting along `toTate` is a bijection from the maximal ideals of `T` to
the maximal ideals of `W`, and it preserves residue fields: `W ⧸ (m ∩ W) ≃ₐ[K] T ⧸ m` for every
maximal ideal `m` of `T`. So the classical points of the closed unit polydisc are the same for
the overconvergent and for the rigid structure.

Both statements follow from the density of `W` in `T` rather than from Weierstrass theory.

* If `I` is an ideal of `T` with `T ⧸ I` finite-dimensional over `K`, then `W → T ⧸ I` is
  surjective. Indeed `I` is closed, so `T ⧸ I` is a finite-dimensional normed space over the
  complete field `K`. The image of `W` is dense, and finite-dimensional subspaces are closed.
  This gives the isomorphism of residue fields, and injectivity of contraction by the Chinese
  remainder theorem applied to `m * m'`.
* A proper ideal `p` of `W` generates a proper ideal of `T`. Otherwise `1` is a finite
  `T`-linear combination of elements of `p`, and approximating the coefficients by elements
  of `W` gives an element of `p` within distance `1` of `1`. That element is a unit of `T`, and so
  of `W` by the overconvergent unit criterion. Hence every maximal ideal of `W` lies under a
  maximal ideal of `T`, which is surjectivity of contraction.

## Main results

* `TauCeti.Dagger.washnitzerAlgebra.surjective_quotient_mkₐ_comp_toTate`: `W` surjects onto
  every quotient of `T` of finite codimension.
* `TauCeti.Dagger.washnitzerAlgebra.quotientComapAlgEquiv`: for an ideal `I` of `T` of finite
  codimension, `W ⧸ (I ∩ W) ≃ₐ[K] T ⧸ I`.
* `TauCeti.Dagger.washnitzerAlgebra.map_toTate_ne_top`: a proper ideal of `W` generates a proper
  ideal of `T`.
* `TauCeti.Dagger.washnitzerAlgebra.bijective_maximalSpectrumComap_toTate`: contraction is a
  bijection `MaximalSpectrum T → MaximalSpectrum W`.
* `TauCeti.Dagger.washnitzerAlgebra.existsUnique_isMaximal_comap`: every maximal ideal of `W` is
  the contraction of exactly one maximal ideal of `T`.

## References

* E. Grosse-Klönne, *Rigid analytic spaces with overconvergent structure sheaf*,
  J. reine angew. Math. 519 (2000), §1, Proposition 1.5.
-/

public section

namespace TauCeti.Dagger.washnitzerAlgebra

open _root_.MvPowerSeries

section NormedField

variable {K : Type*} [NormedField K] [IsUltrametricDist K] [CompleteSpace K] {σ : Type*}

/-- A proper ideal of the Monsky–Washnitzer algebra generates a proper ideal of the Tate
algebra. -/
theorem map_toTate_ne_top {p : Ideal (washnitzerAlgebra σ K)} (hp : p ≠ ⊤) :
    p.map (toTate σ K) ≠ ⊤ := by
  intro h
  obtain ⟨n, c, g, hcg⟩ := Submodule.mem_span_set'.mp ((Ideal.eq_top_iff_one _).mp h)
  choose a ha hag using fun i ↦ (g i).2
  -- Approximate the coefficients `c i` by overconvergent series `w i`.
  have hΦ : Continuous fun d : Fin n → _ ↦ ∑ i, d i * toTate σ K (a i) := by fun_prop
  have h1 : ∑ i, c i * toTate σ K (a i) = 1 := by simpa [hag] using hcg
  obtain ⟨w, hw⟩ := (DenseRange.piMap fun _ ↦ denseRange_toTate).exists_mem_open
    ((Metric.isOpen_ball (x := 1) (ε := 1)).preimage hΦ) ⟨c, by simp [h1]⟩
  refine hp (p.eq_top_of_isUnit_mem
    (p.sum_mem (t := Finset.univ) fun i _ ↦ p.mul_mem_left (w i) (ha i)) ?_)
  rw [← isUnit_toTate_iff]
  by_contra hu
  exact nonunits.subset_compl_ball hu (by simpa using hw)

end NormedField

variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {σ : Type*} [Finite σ]

local notation "Tate " σ:max => IsRestricted.subring (R := K) (fun _ : σ ↦ (1 : ℝ))

/-- For an ideal `I` of finite codimension in the Tate algebra `T`, the Monsky–Washnitzer algebra
`W` surjects onto `T ⧸ I`: its image is dense, and `T ⧸ I` is a finite-dimensional normed space
because every ideal of `T` is closed. -/
theorem surjective_quotient_mkₐ_comp_toTate (I : Ideal (Tate σ)) [Module.Finite K (Tate σ ⧸ I)] :
    Function.Surjective ((Ideal.Quotient.mkₐ K I).comp (toTate σ K)) := by
  -- The `K`-action on `T ⧸ I` as a quotient module agrees with the action of the residue normed
  -- algebra only after unfolding instances, so instance search does not find continuity of
  -- scalar multiplication; we supply it from the normed-algebra structure.
  have : ContinuousSMul K (Tate σ ⧸ I) := IsBoundedSMul.continuousSMul (α := K) (β := Tate σ ⧸ I)
  exact LinearMap.surjective_of_denseRange ((Ideal.Quotient.mkₐ K I).comp (toTate σ K)).toLinearMap
    (Ideal.Quotient.mk_surjective.denseRange.comp denseRange_toTate continuous_quot_mk)

variable (K) in
/-- For an ideal `I` of finite codimension in the Tate algebra `T`, the inclusion of the
Monsky–Washnitzer algebra `W` induces an isomorphism `W ⧸ (I ∩ W) ≃ₐ[K] T ⧸ I`. In particular
corresponding maximal ideals have isomorphic residue fields. -/
noncomputable def quotientComapAlgEquiv (I : Ideal (Tate σ)) [Module.Finite K (Tate σ ⧸ I)] :
    (washnitzerAlgebra σ K ⧸ I.comap (toTate σ K)) ≃ₐ[K] Tate σ ⧸ I :=
  AlgEquiv.ofBijective (Ideal.quotientMapₐ I (toTate σ K) le_rfl)
    ⟨Ideal.quotientMap_injective, fun y ↦ by
      obtain ⟨x, rfl⟩ := surjective_quotient_mkₐ_comp_toTate I y
      exact ⟨Ideal.Quotient.mk _ x, rfl⟩⟩

@[simp]
theorem quotientComapAlgEquiv_mk (I : Ideal (Tate σ)) [Module.Finite K (Tate σ ⧸ I)]
    (f : washnitzerAlgebra σ K) :
    quotientComapAlgEquiv K I (Ideal.Quotient.mk _ f) = Ideal.Quotient.mk I (toTate σ K f) :=
  (rfl)

/-- **Maximal ideals of `W` and of `T`.** Over a complete nontrivially normed ultrametric field,
contraction along the inclusion of the Monsky–Washnitzer algebra into the Tate algebra in
finitely many variables is a bijection of maximal spectra. -/
theorem bijective_maximalSpectrumComap_toTate :
    Function.Bijective (isAffinoidAlgebra_tate.maximalSpectrumComap (toTate σ K)) := by
  refine ⟨fun x y hxy ↦ ?_, fun p ↦ ?_⟩
  · -- If `x ≠ y`, an element of `W` congruent to `1` modulo `y` and to `0` modulo `x` lies in
    -- the common contraction, hence in `y`, which is absurd.
    by_contra hne
    obtain ⟨a, ha, b, hb, hab⟩ := Ideal.isCoprime_iff_exists.mp
      (Ideal.isCoprime_of_isMaximal fun h ↦ hne (MaximalSpectrum.ext h))
    have := (isAffinoidAlgebra_tate (K := K) (σ := σ)).finite_quotient_of_isMaximal x.asIdeal
    have := (isAffinoidAlgebra_tate (K := K) (σ := σ)).finite_quotient_of_isMaximal y.asIdeal
    have := MvPowerSeries.isNoetherianRing_isRestricted_subring (K := K) (σ := σ)
      (c := fun _ ↦ 1)
    have : Module.Finite (Tate σ) x.asIdeal := Module.Finite.iff_fg.mpr (IsNoetherian.noetherian _)
    have := Ideal.finite_quotient_mul (A := K) x.asIdeal y.asIdeal
    obtain ⟨w, hw⟩ := surjective_quotient_mkₐ_comp_toTate (x.asIdeal * y.asIdeal)
      (Ideal.Quotient.mk _ a)
    have hw' : toTate σ K w - a ∈ x.asIdeal ⊓ y.asIdeal :=
      Ideal.mul_le_inf (Ideal.Quotient.eq.mp hw)
    have hwx : w ∈ x.asIdeal.comap (toTate σ K) := by
      simpa using x.asIdeal.add_mem hw'.1 ha
    have hwy : toTate σ K w ∈ y.asIdeal := by
      rwa [← Ideal.mem_comap, ← IsAffinoidAlgebra.maximalSpectrumComap_asIdeal
        isAffinoidAlgebra_tate, ← hxy, IsAffinoidAlgebra.maximalSpectrumComap_asIdeal]
    refine y.isMaximal.ne_top ((Ideal.eq_top_iff_one _).mpr ?_)
    have := y.asIdeal.add_mem (y.asIdeal.sub_mem hwy hw'.2) hb
    rwa [sub_sub_cancel, hab] at this
  · -- A maximal ideal `p` of `W` generates a proper ideal of `T`, which lies in a maximal ideal
    -- of `T` contracting to `p`.
    obtain ⟨m, hm, hpm⟩ := Ideal.exists_le_maximal _ (map_toTate_ne_top p.isMaximal.ne_top)
    refine ⟨⟨m, hm⟩, MaximalSpectrum.ext ?_⟩
    rw [IsAffinoidAlgebra.maximalSpectrumComap_asIdeal]
    exact (p.isMaximal.eq_of_le (isAffinoidAlgebra_tate.comap_isMaximal _ m).ne_top
      (Ideal.map_le_iff_le_comap.mp hpm)).symm

/-- Every maximal ideal of the Monsky–Washnitzer algebra in finitely many variables is the
contraction of exactly one maximal ideal of the Tate algebra. -/
theorem existsUnique_isMaximal_comap (p : Ideal (washnitzerAlgebra σ K)) [p.IsMaximal] :
    ∃! m : Ideal (Tate σ), m.IsMaximal ∧ m.comap (toTate σ K) = p := by
  obtain ⟨⟨m, hm⟩, h⟩ := (bijective_maximalSpectrumComap_toTate (K := K) (σ := σ)).2
    ⟨p, inferInstance⟩
  have hmp : m.comap (toTate σ K) = p := by
    simpa using congrArg MaximalSpectrum.asIdeal h
  refine ⟨m, ⟨hm, hmp⟩, fun m' ⟨hm', h'⟩ ↦ ?_⟩
  exact congrArg MaximalSpectrum.asIdeal <|
    (bijective_maximalSpectrumComap_toTate (K := K) (σ := σ)).1 (a₁ := ⟨m', hm'⟩)
      (a₂ := ⟨m, hm⟩) (MaximalSpectrum.ext (by simpa using h'.trans hmp.symm))

end TauCeti.Dagger.washnitzerAlgebra
