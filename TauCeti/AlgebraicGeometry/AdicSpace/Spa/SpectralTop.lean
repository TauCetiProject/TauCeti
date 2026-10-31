/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.AdicSpace.Spa.Comap
public import TauCeti.RingTheory.Huber.OpenIdeal
public import TauCeti.RingTheory.Huber.TateGauge.Spectral.Topology
import TauCeti.RingTheory.Valuation.Continuous.TopologicallyNilpotent
import TauCeti.RingTheory.Valuation.LtAddSubgroup

/-!
# The adic spectrum of the spectral topology

Let `A` be a Tate ring and `A_sp = SpectralTop A` the ring `A` with its spectral topology, which
is coarser than the topology of `A`. This file shows that the two topologies cannot be told
apart by valuations: a valuation is continuous for the topology of `A` exactly when it is
continuous for the spectral topology. Consequently, for every subring `A⁺` of `A`, the adic
spectra `Spa(A_sp, A⁺)` and `Spa(A, A⁺)` agree, and so do their rational subsets `R(T/s)`. An
ideal of `A` is open exactly when its image in `A_sp` is, both being Tate rings.

One direction is continuity of the identity `A → A_sp`. Conversely, if `v` is continuous on `A`
and `v(b) ≠ 0`, pick a pseudouniformiser `ϖ` and `n` with `v(ϖ)ⁿ < v(b)`; since `v` is below `1`
on the topologically nilpotent elements `A°°`, the spectral neighbourhood `ϖⁿ • A°°` of zero lies
in the additive subgroup `{x | v(x) < v(b)}`, which is therefore open for the spectral topology.

Points of `Spv A_sp` are compared with points of `Spv A` by pullback along the ring isomorphism
`toSpectralTop A : A ≃+* A_sp`; this is a bijection, and its inverse is pullback along the
(in general discontinuous) inverse isomorphism, which is still continuous on valuation spectra.

## Main results

* `TauCeti.Huber.SpectralTop.valuation_isContinuous_iff`: a valuation on `A_sp` is continuous
  exactly when its pullback to `A` is.
* `TauCeti.Huber.SpectralTop.isContinuous_iff`, `TauCeti.Huber.SpectralTop.comap_preimage_cont`:
  `Cont(A_sp) = Cont(A)`.
* `TauCeti.Huber.SpectralTop.comap_preimage_spa`: `Spa(A_sp, A⁺) = Spa(A, A⁺)`.
* `TauCeti.Huber.SpectralTop.isHomeomorph_spaComap`: the pullback map
  `Spa(A_sp, A⁺) → Spa(A, A⁺)` is a homeomorphism.
* `TauCeti.Huber.SpectralTop.comap_preimage_rationalSubset`: the rational subsets `R(T/s)` of the
  two adic spectra agree.
* `TauCeti.Huber.SpectralTop.isOpen_map_ideal_iff`: an ideal of `A` is open exactly when its image
  in `A_sp` is.

## References

* K. S. Kedlaya and R. Liu, *Relative p-adic Hodge theory: foundations*, Astérisque 371 (2015),
  Definition 2.4.3 and Definition 2.8.13.
* T. Wedhorn, *Adic Spaces*, arXiv:1910.05934v1, Definition 7.7 and Theorem 7.10.
-/

public section

open Topology TauCeti.ValuationSpectrum

namespace TauCeti.Huber.SpectralTop

variable {A : Type*} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] [IsTateRing A]

/-- **Valuations do not see the spectral topology.** A valuation on `SpectralTop A` is continuous
exactly when its pullback to `A` is continuous for the topology of `A`. -/
theorem valuation_isContinuous_iff {Γ₀ : Type*} [LinearOrderedCommMonoidWithZero Γ₀]
    {v : Valuation (SpectralTop A) Γ₀} :
    v.IsContinuous ↔ (v.comap (toSpectralTop A : A →+* SpectralTop A)).IsContinuous := by
  refine ⟨fun hv ↦ hv.comap continuous_toSpectralTop, fun hv ↦ ?_⟩
  set w := v.comap (toSpectralTop A : A →+* SpectralTop A)
  have hw (x : A) : w x = v (toSpectralTop A x) := by simp [w]
  rw [Valuation.isContinuous_def]
  intro b
  rcases eq_or_ne (v b) 0 with hb | hb
  · simp [hb]
  have : Nontrivial Γ₀ := ⟨⟨_, _, hb⟩⟩
  obtain ⟨ϖ, hϖ⟩ := IsTateRing.exists_isPseudoUniformizer (A := A)
  -- Some power of `ϖ` has value below `v b`.
  have hball : {x : A | w x < v b} ∈ 𝓝 0 := by
    have hopen := Valuation.isContinuous_def.mp hv ((toSpectralTop A).symm b)
    rw [hw, RingEquiv.apply_symm_apply] at hopen
    exact hopen.mem_nhds (by simpa [hw] using pos_iff_ne_zero.mpr hb)
  obtain ⟨n, hn⟩ := Valuation.exists_pow_lt_of_isTopologicallyNilpotent hball
    hϖ.isTopologicallyNilpotent
  -- The spectral neighbourhood `ϖ ^ n • A°°` of zero lies in the subgroup `{x | v x < v b}`,
  -- since `v < 1` on `A°°`.
  have hmem : ((v.ltAddSubgroupOfNeZero hb : AddSubgroup (SpectralTop A)) : Set (SpectralTop A)) ∈
      𝓝 0 := by
    refine Filter.mem_of_superset ((hasBasis_nhds_zero hϖ).mem_of_mem (i := n) trivial) ?_
    rintro _ ⟨_, ⟨a, ha, rfl⟩, rfl⟩
    rw [SetLike.mem_coe, Valuation.mem_ltAddSubgroupOfNeZero, ← hw]
    beta_reduce
    rw [smul_eq_mul, map_mul, map_pow]
    calc w ϖ ^ n * w a ≤ w ϖ ^ n * 1 := by
          gcongr
          exact (hv.lt_one_of_isTopologicallyNilpotent ha).le
      _ < v b := by rwa [mul_one]
  simpa using (v.ltAddSubgroupOfNeZero hb).isOpen_of_mem_nhds hmem

/-- **`Cont(A_sp) = Cont(A)`, pointwise.** A point of `Spv (SpectralTop A)` is continuous exactly
when its pullback to `Spv A` is. -/
theorem isContinuous_iff (v : Spv (SpectralTop A)) :
    v.IsContinuous ↔ (comap (toSpectralTop A : A →+* SpectralTop A) v).IsContinuous := by
  conv_rhs => rw [← ofValuation_valuation v, comap_ofValuation, isContinuous_ofValuation_iff]
  exact (isContinuous_def v).trans valuation_isContinuous_iff

/-- **`Cont(A_sp) = Cont(A)`.** Pulling back along `toSpectralTop A`, the continuous points of
`Spv A` are exactly the continuous points of `Spv (SpectralTop A)`. -/
theorem comap_preimage_cont :
    comap (toSpectralTop A : A →+* SpectralTop A) ⁻¹' cont A = cont (SpectralTop A) :=
  Set.ext fun v ↦ by rw [Set.mem_preimage, mem_cont_iff, mem_cont_iff, isContinuous_iff]

/-- `toSpectralTop A` is continuous, as a ring homomorphism. -/
private theorem continuous_toRingHom : Continuous (toSpectralTop A : A →+* SpectralTop A) :=
  continuous_toSpectralTop

/-- **`Spa(A_sp, A⁺) = Spa(A, A⁺)`.** For every subring `A⁺` of `A`, pulling back along
`toSpectralTop A` identifies the adic spectrum of `A` with that of `SpectralTop A` for the image
of `A⁺`. -/
theorem comap_preimage_spa (Aplus : Subring A) :
    comap (toSpectralTop A : A →+* SpectralTop A) ⁻¹' spa Aplus =
      spa (Aplus.map (toSpectralTop A : A →+* SpectralTop A)) := by
  ext v
  rw [Set.mem_preimage]
  by_cases hv : v.IsContinuous
  · exact (mem_spa_map_iff continuous_toRingHom Aplus hv).symm
  · rw [mem_spa_iff, mem_spa_iff, ← isContinuous_iff]
    simp [hv, -isContinuous_def]

omit [TopologicalSpace A] [IsTopologicalRing A] [IsTateRing A] in
/-- Pulling back along `toSpectralTop A` undoes pulling back along its inverse. -/
private theorem comap_comap_symm (v : Spv A) :
    comap (toSpectralTop A : A →+* SpectralTop A)
      (comap ((toSpectralTop A).symm : SpectralTop A →+* A) v) = v := by
  rw [← Function.comp_apply (f := comap _), ← comap_comp]
  simp

omit [TopologicalSpace A] [IsTopologicalRing A] [IsTateRing A] in
/-- Pulling back along the inverse of `toSpectralTop A` undoes pulling back along it. -/
private theorem comap_symm_comap (v : Spv (SpectralTop A)) :
    comap ((toSpectralTop A).symm : SpectralTop A →+* A)
      (comap (toSpectralTop A : A →+* SpectralTop A) v) = v := by
  rw [← Function.comp_apply (f := comap _), ← comap_comp]
  simp

/-- **The adic spectra of `A` and `A_sp` are homeomorphic.** For every subring `A⁺` of `A`, the
pullback `Spa(A_sp, A⁺) → Spa(A, A⁺)` along the continuous identity `A → A_sp` is a
homeomorphism. Its inverse is pullback along the inverse ring isomorphism, which need not be
continuous for the topologies on the rings. -/
theorem isHomeomorph_spaComap (Aplus : Subring A) :
    IsHomeomorph (spaComap (toSpectralTop A : A →+* SpectralTop A)
      (continuous_toSpectralTop : Continuous (toSpectralTop A : A →+* SpectralTop A)) Aplus
      (Aplus.map (toSpectralTop A : A →+* SpectralTop A))
      fun _ ha ↦ Subring.mem_map.mpr ⟨_, ha, rfl⟩) := by
  let e : SpectralTop A →+* A := (toSpectralTop A).symm
  have he (v : Spv A) (hv : v ∈ spa Aplus) :
      comap e v ∈ spa (Aplus.map (toSpectralTop A : A →+* SpectralTop A)) := by
    rw [← comap_preimage_spa, Set.mem_preimage, comap_comap_symm]
    exact hv
  refine Homeomorph.isHomeomorph
    { toFun := spaComap _ continuous_toRingHom Aplus _
        fun _ ha ↦ Subring.mem_map.mpr ⟨_, ha, rfl⟩
      invFun v := ⟨comap e v.1, he v.1 v.2⟩
      left_inv v := Subtype.ext ?_
      right_inv v := Subtype.ext ?_
      continuous_toFun := continuous_spaComap ..
      continuous_invFun := continuous_induced_rng.mpr
        ((continuous_comap e).comp continuous_subtype_val) }
  · simp only [spaComap_val]
    exact comap_symm_comap v.1
  · rw [spaComap_val]
    exact comap_comap_symm v.1

open scoped Classical in
/-- **The rational subsets of `Spa(A_sp, A⁺)` and `Spa(A, A⁺)` agree.** Pulling back along
`toSpectralTop A`, the rational subset `R(T/s)` of `Spa(A, A⁺)` is the rational subset of
`Spa(A_sp, A⁺)` presented by the same numerators and denominator. -/
theorem comap_preimage_rationalSubset (Aplus : Subring A) (T : Finset A) (s : A) :
    comap (toSpectralTop A : A →+* SpectralTop A) ⁻¹' rationalSubset Aplus T s =
      rationalSubset (Aplus.map (toSpectralTop A : A →+* SpectralTop A))
        (T.image (toSpectralTop A)) (toSpectralTop A s) := by
  have h := comap_preimage_rationalSubset_inter_spa _ continuous_toRingHom
    (Aplus := Aplus) (fun _ ha ↦ Subring.mem_map.mpr ⟨_, ha, rfl⟩) T s
  rw [← comap_preimage_spa, ← Set.preimage_inter,
    Set.inter_eq_left.mpr (rationalSubset_subset_spa Aplus T s)] at h
  simpa only [RingEquiv.coe_toRingHom] using h

/-- **Open ideals of `A` and `A_sp` correspond.** An ideal of `A` is open exactly when its image in
`SpectralTop A` is; in both Tate rings this means that it is the unit ideal. -/
theorem isOpen_map_ideal_iff (J : Ideal A) :
    IsOpen (J.map (toSpectralTop A) : Set (SpectralTop A)) ↔ IsOpen (J : Set A) := by
  rw [IsTateRing.isOpen_iff_eq_top, IsTateRing.isOpen_iff_eq_top]
  refine ⟨fun h ↦ ?_, fun h ↦ by rw [h, Ideal.map_top]⟩
  rw [← Ideal.comap_map_of_bijective _ (toSpectralTop A).bijective (I := J), h, Ideal.comap_top]

end TauCeti.Huber.SpectralTop
