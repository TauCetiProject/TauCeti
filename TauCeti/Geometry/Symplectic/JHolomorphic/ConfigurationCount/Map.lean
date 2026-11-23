/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.JHolomorphic.PointConfigurationCount

/-!
# Weighted configuration counts under a map of classes

Taubes's weighted counts of configurations of pseudoholomorphic curves
(`TauCeti.configurationCount`, `TauCeti.pointConfigurationCount`) are indexed by the integral class
`A` of a configuration, and for candidates of positive period they are collected into the
generating series `∑_A Gr(A) e^A` (`TauCeti.configurationCountSeries`), a Novikov series on the
group `H` of classes. To compare these counts with invariants indexed by a coarser group, such as
the classes of the closed orbits of a surface mapping torus or their periods, the exponents are
specialized along a homomorphism `φ : H →+ H'`. This file shows that this specialization is
computed by the same counts, taken with the classes `φ ∘ cls` in place of `cls`.

* **Configurations.** A multiplicity assignment has class `A'` for the classes `φ ∘ cls` exactly
  when its class `A` for the classes `cls` satisfies `φ A = A'`
  (`TauCeti.mem_compatibleConfigurations_comp`). So the configurations in class `A'` for `φ ∘ cls`
  are the union, over the fibre `φ ⁻¹' {A'}`, of the configurations for `cls`
  (`TauCeti.compatibleConfigurations_comp`), and likewise for the configurations through given
  points (`TauCeti.pointConfigurations_comp`). The union is disjoint, since a configuration has
  only one class (`TauCeti.pairwise_disjoint_compatibleConfigurations`).
* **Counts.** When there are finitely many configurations in class `A'` for `φ ∘ cls`, the count
  in class `A'` is the sum of the counts in the classes of its fibre
  (`TauCeti.configurationCount_comp`, `TauCeti.pointConfigurationCount_comp`). When `φ` is
  injective the counts do not change at all (`TauCeti.configurationCount_comp_of_injective`,
  `TauCeti.pointConfigurationCount_comp_of_injective`); no finiteness is needed then.
* **Generating series.** Let `N : H →+ ℝ` be a period, positive on the candidates with finitely
  many candidates below each cutoff, and let `φ` rescale periods by a positive constant,
  `N' (φ h) = c * N h`. Then only finitely many classes of each fibre of `φ` have a nonzero count,
  and the pushforward of Novikov series along `φ` (`TauCeti.NovikovSeries.map`) sends the
  generating series of the counts to the series whose coefficient at `A'` is the count in class
  `A'` for the classes `φ ∘ cls` (`TauCeti.coeff_map_configurationCountSeries`), that is, to the
  generating series for the classes `φ ∘ cls` (`TauCeti.mapRingHom_configurationCountSeries`).
  Finiteness below each cutoff passes along `φ` (`TauCeti.NovikovSeries.finite_setOf_map_le`).
  For pairwise compatible candidates, such as the disjoint orbit tori of a mapping torus, with
  weights given by local series `f c`, the specialized generating series is therefore the
  infinite product `∏_c f c (e ^ φ (cls c))` of the local series at the specialized classes
  (`TauCeti.hasProd_ofPowerSeries_mapRingHom_configurationCountSeries`).

The candidates, their classes and weights, and the map `φ` are inputs here; identifying the
specialized classes geometrically, for instance the class of an orbit torus with that of its
orbit, is separate.

## Main results

* `TauCeti.compatibleConfigurations_comp`, `TauCeti.pointConfigurations_comp`: the configurations
  for the classes `φ ∘ cls` in class `A'` are those for the classes `cls` in the classes over
  `A'`.
* `TauCeti.configurationCount_comp`, `TauCeti.pointConfigurationCount_comp`: the counts for the
  classes `φ ∘ cls` are the sums of the counts over the fibres of `φ`.
* `TauCeti.configurationCount_comp_of_injective`,
  `TauCeti.pointConfigurationCount_comp_of_injective`: an injective map of classes does not change
  the counts.
* `TauCeti.coeff_map_configurationCountSeries`: the pushforward of the generating series along a
  period-rescaling `φ` has the counts for the classes `φ ∘ cls` as coefficients.
* `TauCeti.mapRingHom_configurationCountSeries`: the pushforward of the generating series is the
  generating series for the classes `φ ∘ cls`.
* `TauCeti.hasProd_ofPowerSeries_mapRingHom_configurationCountSeries`: the pushforward of the
  generating series is the product of the local series at the specialized classes.

## References

* C. H. Taubes, *Counting pseudo-holomorphic submanifolds in dimension 4*,
  J. Differential Geom. 44 (1996), 818--893.
-/

public section

namespace TauCeti

open PowerSeries NovikovSeries

variable {ι H H' P R : Type*}

section Configuration

variable [AddCommMonoid H] [AddCommMonoid H'] {r : ι → ι → Prop} {cls : ι → H}
  {pts : ι → Finset P} {s : Set ι} {φ : H →+ H'} {A' : H'} {l : ι →₀ ℕ}

/-- A multiplicity assignment is a configuration in class `A'` for the classes `φ ∘ cls` exactly
when it is a configuration for the classes `cls`, necessarily in its class
`∑ l c • cls c`, and `φ` maps that class to `A'`. -/
theorem mem_compatibleConfigurations_comp :
    l ∈ compatibleConfigurations r (φ ∘ cls) s A' ↔
      l ∈ compatibleConfigurations r cls s (Finsupp.linearCombination ℕ cls l) ∧
        φ (Finsupp.linearCombination ℕ cls l) = A' := by
  have h := LinearMap.map_finsupp_linearCombination φ.toNatLinearMap (g := cls) l
  rw [AddMonoidHom.coe_toNatLinearMap] at h
  simp only [mem_compatibleConfigurations, ← h, and_true, and_assoc]

/-- **Configurations under a map of classes.** The configurations in class `A'` for the classes
`φ ∘ cls` are the configurations for the classes `cls` in the classes `A` with `φ A = A'`. The
union is disjoint (`TauCeti.pairwise_disjoint_compatibleConfigurations`). -/
theorem compatibleConfigurations_comp (φ : H →+ H') (A' : H') :
    compatibleConfigurations r (φ ∘ cls) s A' =
      ⋃ A ∈ φ ⁻¹' {A'}, compatibleConfigurations r cls s A := by
  ext l
  simp only [mem_compatibleConfigurations_comp, Set.mem_iUnion, Set.mem_preimage,
    Set.mem_singleton_iff, exists_prop]
  refine ⟨fun h ↦ ⟨_, h.2, h.1⟩, ?_⟩
  rintro ⟨A, hA, hl⟩
  obtain rfl := (mem_compatibleConfigurations.1 hl).2.2
  exact ⟨hl, hA⟩

/-- An injective map of classes does not change the configurations. -/
theorem compatibleConfigurations_comp_of_injective (hφ : Function.Injective φ) (A : H) :
    compatibleConfigurations r (φ ∘ cls) s (φ A) = compatibleConfigurations r cls s A := by
  ext l
  rw [mem_compatibleConfigurations_comp, hφ.eq_iff]
  refine ⟨fun h ↦ h.2 ▸ h.1, fun hl ↦ ⟨?_, (mem_compatibleConfigurations.1 hl).2.2⟩⟩
  rwa [(mem_compatibleConfigurations.1 hl).2.2]

/-- **Point configurations under a map of classes.** The configurations through the points in
class `A'` for the classes `φ ∘ cls` are those for the classes `cls` in the classes `A` with
`φ A = A'`. -/
theorem pointConfigurations_comp (φ : H →+ H') (A' : H') :
    pointConfigurations r (φ ∘ cls) pts s A' =
      ⋃ A ∈ φ ⁻¹' {A'}, pointConfigurations r cls pts s A := by
  simp only [pointConfigurations_eq_inter, compatibleConfigurations_comp, Set.iUnion₂_inter]

/-- An injective map of classes does not change the configurations through the points. -/
theorem pointConfigurations_comp_of_injective (hφ : Function.Injective φ) (A : H) :
    pointConfigurations r (φ ∘ cls) pts s (φ A) = pointConfigurations r cls pts s A := by
  rw [pointConfigurations_eq_inter, pointConfigurations_eq_inter,
    compatibleConfigurations_comp_of_injective hφ]

/-- Summing over the configurations in class `A'` for the classes `φ ∘ cls` that satisfy a further
condition `Q` is summing, fibre by fibre of `φ`, over those for the classes `cls`, provided there
are finitely many of them. -/
private theorem finsum_mem_compatibleConfigurations_comp_inter {M : Type*} [AddCommMonoid M]
    (Q : Set (ι →₀ ℕ)) (g : (ι →₀ ℕ) → M)
    (h : (compatibleConfigurations r (φ ∘ cls) s A' ∩ Q).Finite) :
    ∑ᶠ l ∈ compatibleConfigurations r (φ ∘ cls) s A' ∩ Q, g l =
      ∑ᶠ A ∈ φ ⁻¹' {A'}, ∑ᶠ l ∈ compatibleConfigurations r cls s A ∩ Q, g l := by
  set T : H → Set (ι →₀ ℕ) := fun A ↦ compatibleConfigurations r cls s A ∩ Q
  -- The classes that actually carry a configuration form a finite subset `I` of the fibre.
  set I := Finsupp.linearCombination ℕ cls '' (compatibleConfigurations r (φ ∘ cls) s A' ∩ Q)
  have hTsub {A : H} (hA : φ A = A') : T A ⊆ compatibleConfigurations r (φ ∘ cls) s A' ∩ Q := by
    rw [compatibleConfigurations_comp, Set.iUnion₂_inter]
    exact Set.subset_biUnion_of_mem (u := T) hA
  have hI : compatibleConfigurations r (φ ∘ cls) s A' ∩ Q = ⋃ A ∈ I, T A := by
    refine Set.Subset.antisymm (fun l hl ↦ Set.mem_biUnion (Set.mem_image_of_mem _ hl)
      (Set.mem_inter (mem_compatibleConfigurations_comp.1 hl.1).1 hl.2))
      (Set.iUnion₂_subset fun A hA ↦ ?_)
    obtain ⟨l, hl, rfl⟩ := hA
    exact hTsub (mem_compatibleConfigurations_comp.1 hl.1).2
  have hIφ {A : H} (hA : A ∈ I) : φ A = A' := by
    obtain ⟨l, hl, rfl⟩ := hA
    exact (mem_compatibleConfigurations_comp.1 hl.1).2
  rw [hI, finsum_mem_biUnion (fun A _ B _ hAB ↦
      (pairwise_disjoint_compatibleConfigurations hAB).mono Set.inter_subset_left
        Set.inter_subset_left) (h.image _) fun A hA ↦ h.subset (hTsub (hIφ hA))]
  -- Outside `I`, the classes of the fibre carry no configuration.
  refine finsum_mem_inter_support_eq' _ _ _ fun A hA ↦ ⟨hIφ, fun hAφ ↦ ?_⟩
  obtain ⟨l, hl, -⟩ := exists_ne_zero_of_finsum_mem_ne_zero hA
  exact ⟨l, hTsub hAφ hl, (mem_compatibleConfigurations.1 hl.1).2.2⟩

variable [CommSemiring R] {w : ι → ℕ → R}

/-- **Counts under a map of classes.** If there are finitely many configurations in class `A'` for
the classes `φ ∘ cls`, the count in class `A'` is the sum of the counts in the classes `A` with
`φ A = A'`, of which only finitely many are nonzero. -/
theorem configurationCount_comp (h : (compatibleConfigurations r (φ ∘ cls) s A').Finite) :
    configurationCount r (φ ∘ cls) w s A' =
      ∑ᶠ A ∈ φ ⁻¹' {A'}, configurationCount r cls w s A := by
  simpa only [configurationCount_def, Set.inter_univ] using
    finsum_mem_compatibleConfigurations_comp_inter Set.univ (fun l ↦ l.prod w)
      (by rwa [Set.inter_univ])

/-- An injective map of classes does not change the counts. -/
theorem configurationCount_comp_of_injective (hφ : Function.Injective φ) (A : H) :
    configurationCount r (φ ∘ cls) w s (φ A) = configurationCount r cls w s A := by
  rw [configurationCount_def, configurationCount_def,
    compatibleConfigurations_comp_of_injective hφ]

/-- **Counts through the points under a map of classes.** If there are finitely many
configurations through the points in class `A'` for the classes `φ ∘ cls`, the count through the
points in class `A'` is the sum of the counts in the classes `A` with `φ A = A'`. -/
theorem pointConfigurationCount_comp (h : (pointConfigurations r (φ ∘ cls) pts s A').Finite) :
    pointConfigurationCount r (φ ∘ cls) pts w s A' =
      ∑ᶠ A ∈ φ ⁻¹' {A'}, pointConfigurationCount r cls pts w s A := by
  rw [pointConfigurations_eq_inter] at h
  simpa only [pointConfigurationCount_def, pointConfigurations_eq_inter] using
    finsum_mem_compatibleConfigurations_comp_inter _ (fun l ↦ l.prod w) h

/-- An injective map of classes does not change the counts through the points. -/
theorem pointConfigurationCount_comp_of_injective (hφ : Function.Injective φ) (A : H) :
    pointConfigurationCount r (φ ∘ cls) pts w s (φ A) =
      pointConfigurationCount r cls pts w s A := by
  rw [pointConfigurationCount_def, pointConfigurationCount_def,
    pointConfigurations_comp_of_injective hφ]

end Configuration

/-! ### The generating series under a map of classes -/

section Series

variable [AddCommMonoid H] [AddCommMonoid H'] {N : H →+ ℝ} {N' : H' →+ ℝ} {r : ι → ι → Prop}
  {cls : ι → H} {s : Set ι} {φ : H →+ H'}

section CommSemiring

variable [CommSemiring R] {w : ι → ℕ → R}

/-- **Specializing the generating series.** Let the candidates have positive period `N`, finitely
many below each cutoff, and let `φ` rescale periods by a positive constant. The pushforward along
`φ` (and a coefficient map `ρ`) of the generating series `∑_A Gr(A) e^A` of the counts has at `A'`
the count in class `A'` for the classes `φ ∘ cls`, that is, the sum of the counts in the classes
over `A'` (`TauCeti.configurationCount_comp`). -/
@[simp]
theorem coeff_map_configurationCountSeries {S : Type*} [AddCommMonoid S] (ρ : R →+ S)
    (hφ : ∃ c > 0, ∀ h, N' (φ h) = c * N h) {hpos : ∀ c ∈ s, 0 < N (cls c)}
    {hfin : ∀ C : ℝ, {c ∈ s | N (cls c) ≤ C}.Finite} (A' : H') :
    (map ρ φ hφ (configurationCountSeries r cls w hpos hfin)).coeff A' =
      ρ (configurationCount r (φ ∘ cls) w s A') := by
  obtain ⟨k, hk, hkφ⟩ := hφ
  have hpos' : ∀ c ∈ s, 0 < N' ((φ ∘ cls) c) := fun c hc ↦ by
    rw [Function.comp_apply, hkφ]
    exact mul_pos hk (hpos c hc)
  have hsupp : (φ ⁻¹' {A'} ∩ Function.support (configurationCount r cls w s)).Finite :=
    ((configurationCountSeries r cls w hpos hfin).finite_support_inter_preimage_singleton
      ⟨k, hk, hkφ⟩ A').subset fun A hA ↦
        ⟨by rw [mem_support, coeff_configurationCountSeries]; exact hA.2, hA.1⟩
  rw [NovikovSeries.coeff_map]
  simp only [coeff_configurationCountSeries]
  rw [configurationCount_comp (finite_compatibleConfigurations hpos'
    (finite_setOf_map_le ⟨k, hk, hkφ⟩ hfin _)), AddMonoidHom.map_finsum_mem' ρ hsupp]

/-- **The specialized generating series.** Let the candidates have positive period `N`, finitely
many below each cutoff, and let `φ` rescale periods by a positive constant. The pushforward along
`φ` of the generating series of the counts for the classes `cls` is the generating series of the
counts for the classes `φ ∘ cls`. -/
theorem mapRingHom_configurationCountSeries (hφ : ∃ c > 0, ∀ h, N' (φ h) = c * N h)
    (hpos : ∀ c ∈ s, 0 < N (cls c)) (hpos' : ∀ c ∈ s, 0 < N' (φ (cls c)))
    (hfin : ∀ C : ℝ, {c ∈ s | N (cls c) ≤ C}.Finite) :
    mapRingHom (RingHom.id R) φ hφ (configurationCountSeries r cls w hpos hfin) =
      configurationCountSeries r (φ ∘ cls) w hpos' (finite_setOf_map_le hφ hfin) := by
  ext A'
  rw [mapRingHom_apply, coeff_map_configurationCountSeries, coeff_configurationCountSeries]
  simp only [AddMonoidHom.coe_ofClass, RingHom.id_apply]

end CommSemiring

variable [CommRing R] {w : ι → ℕ → R} {f : ι → R⟦X⟧}

/-- **The specialized generating series is the product of the local series.** Let the candidates
of `s` be pairwise compatible, of positive period `N` and finitely many below each cutoff, with
weights `w c k = [t ^ k] f c` given by series `f c` with constant term `1`, and let `φ` rescale
periods by a positive constant. Then the pushforward along `φ` of the generating series of the
counts is the infinite product `∏_c f c (e ^ φ (cls c))` of the local series at the specialized
classes, in the period topology. -/
theorem hasProd_ofPowerSeries_mapRingHom_configurationCountSeries (hs : s.Pairwise r)
    (hφ : ∃ c > 0, ∀ h, N' (φ h) = c * N h) (hpos : ∀ c ∈ s, 0 < N (cls c))
    (hpos' : ∀ c ∈ s, 0 < N' (φ (cls c))) (hfin : ∀ C : ℝ, {c ∈ s | N (cls c) ≤ C}.Finite)
    (hw : ∀ c ∈ s, ∀ k, w c k = coeff k (f c)) (hf : ∀ c ∈ s, constantCoeff (f c) = 1) :
    HasProd (fun c : s ↦ ofPowerSeries (φ (cls c)) (hpos' c c.property) (f c))
      (mapRingHom (RingHom.id R) φ hφ (configurationCountSeries r cls w hpos hfin)) := by
  rw [mapRingHom_configurationCountSeries hφ hpos hpos' hfin]
  exact hasProd_ofPowerSeries_configurationCountSeries hs hpos' (finite_setOf_map_le hφ hfin) hw
    hf

end Series

end TauCeti
