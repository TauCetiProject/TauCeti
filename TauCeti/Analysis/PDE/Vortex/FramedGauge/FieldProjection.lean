/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Vortex.FramedGauge.SmoothDivisor

/-!
# The field projection onto the moduli space of framed plane vortices

For an integer `k ≥ 2`, the Sobolev framed gauge group `G_(k+2)` acts on the continuous fields of
`A_m^(k+1) = x_m + H^(k+1)(ℂ; iT*ℂ ⊕ ℂ)` (`TauCeti.Vortex.SobolevFieldSpace`), and the vortex
orbits form a smooth manifold of dimension `2m`
(`TauCeti.Vortex.SobolevFieldSpace.isManifold_vortexModuli`). Gluing plane vortices into
approximate solutions reads a field that is only close to a vortex through a nearby vortex orbit:
the *field projection*. This file constructs it near every smooth vortex `x₀`, as a smooth,
gauge-invariant map from a neighbourhood of `x₀` to the vortices of the Coulomb slice of `x₀` that
keeps the gauge orbit of every vortex.

**The Coulomb projection is gauge invariant.** Near a field `x`, the smooth Coulomb gauge carries
each field `y` to a field `g · y` of the Coulomb slice `d₀* (· - x) = 0`, with coordinates `π y`
smooth in those of `y`. Since the slice meets each nearby gauge orbit only once, on a smaller
neighbourhood `π` takes the same value on gauge equivalent fields
(`TauCeti.Vortex.SobolevFieldSpace.`
`exists_isOpen_contDiffOn_forall_realSubRef_smul_eq_and_forall_apply_smul_eq`).

**The retraction in the slice.** At a vortex `x₀` lying in every `A_m^j`, the Coulomb slice chart
reads a vortex `t` of the slice through a continuous linear map `Ψ` applied to the difference of
the coordinates of `t` and of `x₀`, the projection onto the kernel of the gauge-fixed operator
`L_{x₀}` (`exists_coulombSliceChart_apply_eq_and_contDiffAt_symm`). Applying the inverse chart to
`Ψ` of the difference of the coordinates of an arbitrary field `u` and of `x₀` gives the vortex
`σ u` of the slice with the same kernel component as `u`. It is smooth near `x₀`, by the implicit
function theorem, and it fixes the vortices of the slice near `x₀`
(`TauCeti.Vortex.SobolevFieldSpace.exists_isOpen_sliceVortexRetraction`).

**The field projection.** The composite `P y = σ (π y)` is defined on a neighbourhood `U` of `x₀`
and takes values in the vortices of the Coulomb slice of `x₀`
(`TauCeti.Vortex.SobolevFieldSpace.exists_isOpen_fieldProjection`):

* it is smooth in the real coordinates of the fields;
* it is gauge invariant: `P (g · y) = P y` whenever `y` and `g · y` lie in `U`;
* it fixes vortex orbits: a vortex `y` of `U` is gauge equivalent to `P y`;
* it fixes `x₀`.

So the vortex orbit `[P y]` depends only on the gauge orbit of `y` within `U`, and it is the orbit
of `y` when `y` is a vortex. For `k ≥ 3`, composing with the divisor gives
gauge-invariant divisor coordinates `y ↦ c(D(P y)) ∈ ℂᵐ` near `x₀`, the coefficients of the monic
polynomial whose roots are the zeros of `P y`; they are smooth in the field coordinates and are
the coefficients of the divisor of `y` when `y` is a vortex
(`TauCeti.Vortex.SobolevFieldSpace.exists_isOpen_contDiffAt_coeffEquiv_sobolevVortexDivisor`).

## Main results

* `TauCeti.Vortex.SobolevFieldSpace.exists_isOpen_sliceVortexRetraction`: a smooth
  retraction of the fields near a vortex onto the vortices of its Coulomb slice.
* `TauCeti.Vortex.SobolevFieldSpace.exists_isOpen_fieldProjection`: the field projection near a
  vortex.
* `TauCeti.Vortex.SobolevFieldSpace.exists_isOpen_contDiffAt_coeffEquiv_sobolevVortexDivisor`:
  gauge-invariant smooth divisor coordinates near a vortex.

## References

* C. H. Taubes, *Gr ⇒ SW: from pseudo-holomorphic curves to Seiberg–Witten solutions*,
  J. Differential Geom. 51 (1999), 203–334.
* S. K. Donaldson and P. B. Kronheimer, *The Geometry of Four-Manifolds*, Oxford University Press,
  1990, Section 4.2.
-/

public section

namespace TauCeti.Vortex

namespace SobolevFieldSpace

open BesselPotentialSpace Filter Topology SobolevTopologicalGaugeGroup
open scoped ContDiff

variable {f : ContDiffBump (0 : ℝ)} {m k : ℕ}

variable [Fact (1 < k + 1)] {hs : 1 < ((k + 1 : ℕ) : ℝ) + 1}

omit [Fact (1 < k + 1)] in
/-- The Coulomb slice chart at `x₀`, read through a continuous linear map `Ψ` of the difference of
slice coordinates on an open set `O` cutting out its source, sends a vortex `t` of the slice with
slice coordinates in `O` to `Ψ (φ t - φ x₀)`; so its inverse returns `t`. -/
private theorem sliceCoords_symm_coulombSliceChart_symm_eq (hk : 2 ≤ k)
    {x₀ : SobolevFieldSpace f m (k + 1 : ℕ)}
    (hmem : ∀ j : ℕ, ⇑(congrOrder (Nat.cast_succ k) x₀) ∈ framedFieldSpace f m j)
    (hsol : ∀ z, equation (congrOrder (Nat.cast_succ k) x₀) z = 0)
    {Ψ : (Fin 4 → realSubmodule ℂ (k.cast_add_one_pos (α := ℝ)).le) →L[ℝ] (Fin (2 * m) → ℝ)}
    (hΨ : ∀ p, coulombSliceChart hk (congrOrder (Nat.cast_succ k) x₀) hmem hsol p =
      Ψ ((p : Fin 4 → _) - (congrOrder (Nat.cast_succ k) x₀).realSubRef _))
    {O : Set (Fin 4 → realSubmodule ℂ (k.cast_add_one_pos (α := ℝ)).le)}
    (hOs : Subtype.val ⁻¹' O = (coulombSliceChart hk (congrOrder (Nat.cast_succ k) x₀) hmem
      hsol).source)
    {t : SobolevFieldSpace f m (k + 1 : ℕ)} (htS : t ∈ coulombSlice x₀)
    (ht : ∀ z, equation t z = 0) (htO : sliceCoords hk t ∈ O) :
    (sliceCoords hk).symm ((coulombSliceChart hk (congrOrder (Nat.cast_succ k) x₀) hmem hsol).symm
      (Ψ (sliceCoords hk t - sliceCoords hk x₀))).val = t := by
  set c := coulombSliceChart hk (congrOrder (Nat.cast_succ k) x₀) hmem hsol
  have htmem := (realSobolevSliceEquation_realSubRef_congrOrder_eq_zero_iff hk x₀ t).2 ⟨htS, ht⟩
  rw [← sliceCoords_apply] at htmem
  have hpt : (⟨_, htmem⟩ : {u | realSobolevSliceEquation f m hk _ u = 0}) ∈ c.source := by
    rw [← hOs]; exact htO
  have hcpt : c ⟨_, htmem⟩ = Ψ (sliceCoords hk t - sliceCoords hk x₀) := by
    rw [hΨ, sliceCoords_apply hk x₀]
  rw [← hcpt, c.left_inv hpt]
  exact (sliceCoords hk).symm_apply_apply t

omit [Fact (1 < k + 1)] in
/-- **A smooth retraction onto the vortices of the Coulomb slice.** Let `x₀` be a continuous
vortex of `A_m^(k+1)`, `k ≥ 2`, lying in `A_m^j` for every `j`. There are an open neighbourhood
`S` of the real coordinates of `x₀` and a map `σ` from real coordinates to fields such that

* every `σ u` is a vortex in the Coulomb slice of `x₀`, and `σ` fixes `x₀`;
* `σ` fixes every vortex of the Coulomb slice of `x₀` with coordinates in `S`;
* `σ` is smooth on `S` in the real coordinates.

The vortex `σ u` has the same component as `u` in the kernel of the gauge-fixed operator at `x₀`,
read through the Coulomb slice chart (`coulombSliceChart`). -/
theorem exists_isOpen_sliceVortexRetraction (hk : 2 ≤ k)
    (x₀ : SobolevFieldSpace f m (k + 1 : ℕ)) (hmem : ∀ j : ℕ, ⇑x₀ ∈ framedFieldSpace f m j)
    (hsol : ∀ z, equation x₀ z = 0) :
    ∃ S : Set (Fin 4 → realSubmodule ℂ (Nat.cast_nonneg (k + 1) : (0 : ℝ) ≤ ((k + 1 : ℕ) : ℝ))),
      IsOpen S ∧ x₀.realSubRef (Nat.cast_nonneg (k + 1)) ∈ S ∧
      ∃ σ : (Fin 4 → realSubmodule ℂ (Nat.cast_nonneg (k + 1) : (0 : ℝ) ≤ ((k + 1 : ℕ) : ℝ))) →
          SobolevFieldSpace f m (k + 1 : ℕ),
        (∀ u, σ u ∈ coulombSlice x₀ ∧ ∀ z, equation (σ u) z = 0) ∧
        σ (x₀.realSubRef (Nat.cast_nonneg (k + 1))) = x₀ ∧
        (∀ t : SobolevFieldSpace f m (k + 1 : ℕ), t ∈ coulombSlice x₀ → (∀ z, equation t z = 0) →
          t.realSubRef (Nat.cast_nonneg (k + 1)) ∈ S →
            σ (t.realSubRef (Nat.cast_nonneg (k + 1))) = t) ∧
        ∀ u ∈ S, ContDiffAt ℝ ∞ (fun u ↦ (σ u).realSubRef (Nat.cast_nonneg (k + 1))) u := by
  have hmem' : ∀ j : ℕ, ⇑(congrOrder (Nat.cast_succ k) x₀) ∈ framedFieldSpace f m j :=
    coe_congrOrder _ x₀ ▸ hmem
  have hsol' : ∀ z, equation (congrOrder (Nat.cast_succ k) x₀) z = 0 := coe_congrOrder _ x₀ ▸ hsol
  set c := coulombSliceChart hk (congrOrder (Nat.cast_succ k) x₀) hmem' hsol'
  obtain ⟨⟨Ψ, hΨ⟩, A, hA, hx₀A, hAc⟩ :=
    exists_coulombSliceChart_apply_eq_and_contDiffAt_symm hk _ hmem' hsol'
  -- The slice coordinates `φ` at the order `↑k + 1` of the chart are the real coordinates at the
  -- order `↑(k + 1)` up to the identification `κ`.
  set φ := sliceCoords (f := f) (m := m) hk
  set κ := ContinuousLinearEquiv.piCongrRight fun _ : Fin 4 ↦ realSubmoduleCongr ℂ
    (Nat.cast_succ k) (Nat.cast_nonneg (k + 1)) (k.cast_add_one_pos (α := ℝ)).le
  have hφκ (y) : φ y = κ (y.realSubRef _) := sliceCoords_eq_piCongrRight_realSubRef hk y
  have hp₀ := mem_coulombSliceChart_source hk _ hmem' hsol'
  have hcsymm0 := (c.left_inv hp₀).symm.trans (congrArg c.symm
    (coulombSliceChart_apply_self hk _ hmem' hsol'))
  have hu₀ := (sliceCoords_apply (f := f) (m := m) hk x₀).symm
  obtain ⟨O, hO, hOs⟩ := isOpen_induced_iff.1 c.open_source
  -- `v u` reads the kernel component of `u - x₀`; on the open set `T` the inverse chart is smooth.
  set v := fun u ↦ Ψ (κ u - φ x₀)
  have hv : ContDiff ℝ ∞ v := Ψ.contDiff.comp (κ.contDiff.sub contDiff_const)
  set T := c.target ∩ (fun w ↦ ((c.symm w : _) : Fin 4 → _)) ⁻¹' A
  have hT : IsOpen T := (continuous_subtypeVal.comp_continuousOn
    c.continuousOn_symm).isOpen_inter_preimage c.open_target hA
  have hv₀ : v (x₀.realSubRef (Nat.cast_nonneg (k + 1))) = 0 := by simp [v, ← hφκ]
  refine ⟨κ ⁻¹' O ∩ v ⁻¹' T, (hO.preimage κ.continuous).inter (hT.preimage hv.continuous),
    ⟨?_, ?_⟩, fun u ↦ φ.symm (c.symm (v u)).val, fun u ↦ ?_, ?_, fun t htS ht htO ↦ ?_,
    fun u hu ↦ ?_⟩
  · rw [Set.mem_preimage, ← hφκ, ← hu₀]
    exact (Set.ext_iff.1 hOs _).2 hp₀
  · rw [Set.mem_preimage, hv₀]
    refine ⟨mem_coulombSliceChart_target hk _ hmem' hsol', ?_⟩
    rw [Set.mem_preimage, ← hcsymm0]
    exact hx₀A
  · refine (realSobolevSliceEquation_realSubRef_congrOrder_eq_zero_iff hk x₀ _).1 ?_
    rw [← sliceCoords_apply hk, φ.apply_symm_apply]
    exact (c.symm _).property
  · beta_reduce
    rw [hv₀, ← hcsymm0]
    exact (congrArg φ.symm hu₀).trans (φ.symm_apply_apply x₀)
  · have h := sliceCoords_symm_coulombSliceChart_symm_eq hk hmem' hsol' hΨ hOs htS ht
      (by rw [hφκ]; exact htO.1)
    rwa [hφκ t] at h
  · -- In coordinates, `σ` is the inverse chart composed with the smooth map `v`.
    have h := (κ.symm.contDiff.contDiffAt.comp _ (hAc _ hu.2.1 hu.2.2)).comp u hv.contDiffAt
    refine h.congr_of_eventuallyEq (Eventually.of_forall fun u ↦ ?_)
    exact realSubRef_sliceCoords_symm hk _

/-- **The field projection near a vortex.** Let `x₀` be a continuous vortex of `A_m^(k+1)`,
`k ≥ 2`, lying in `A_m^j` for every `j`. There are an open neighbourhood `U` of `x₀` and a map `P`
of the fields into the vortices of the Coulomb slice of `x₀` such that

* `P` fixes `x₀`;
* a vortex `y` of `U` is gauge equivalent to `P y`;
* `P` is gauge invariant on `U`: `P (g · y) = P y` whenever `y` and `g · y` lie in `U`;
* `P` is smooth in the real coordinates of the fields at every field of `U`.

So the vortex orbit `[P y]` depends only on the gauge orbit of `y` within `U`, and it is the orbit
of `y` when `y` is a vortex. -/
theorem exists_isOpen_fieldProjection (hk : 2 ≤ k) (x₀ : SobolevFieldSpace f m (k + 1 : ℕ))
    (hmem : ∀ j : ℕ, ⇑x₀ ∈ framedFieldSpace f m j) (hsol : ∀ z, equation x₀ z = 0) :
    ∃ U : Set (SobolevFieldSpace f m (k + 1 : ℕ)), IsOpen U ∧ x₀ ∈ U ∧
      ∃ P : SobolevFieldSpace f m (k + 1 : ℕ) → SobolevFieldSpace f m (k + 1 : ℕ),
        (∀ y, P y ∈ coulombSlice x₀ ∧ ∀ z, equation (P y) z = 0) ∧ P x₀ = x₀ ∧
        (∀ y ∈ U, (∀ z, equation y z = 0) →
          ∃ g : SobolevTopologicalGaugeGroup hs, g • y = P y) ∧
        (∀ y ∈ U, ∀ g : SobolevTopologicalGaugeGroup hs, g • y ∈ U → P (g • y) = P y) ∧
        ∀ y ∈ U, ContDiffAt ℝ ∞
          (fun u ↦ (P (ofRealSubRef (Nat.one_lt_cast.2 Fact.out) u)).realSubRef
            (Nat.cast_nonneg (k + 1)))
          (y.realSubRef (Nat.cast_nonneg (k + 1))) := by
  have hX : 1 < ((k + 1 : ℕ) : ℝ) := Nat.one_lt_cast.2 Fact.out
  set h0 : (0 : ℝ) ≤ ((k + 1 : ℕ) : ℝ) := Nat.cast_nonneg (k + 1)
  have hρι (u) : (ofRealSubRef (f := f) (m := m) hX u).realSubRef h0 = u :=
    realSubRef_ofRealSubRef hX u
  obtain ⟨U₁, hU₁, hx₀U₁, π, hπ, hπx₀, hπS, hπg⟩ :=
    exists_isOpen_contDiffOn_forall_realSubRef_smul_eq_and_forall_apply_smul_eq hs (by omega) x₀
  obtain ⟨S, hS, hx₀S, σ, hσ, hσx₀, hσt, hσc⟩ :=
    exists_isOpen_sliceVortexRetraction hk x₀ hmem hsol
  refine ⟨realSubRef h0 ⁻¹' (U₁ ∩ π ⁻¹' S), (hπ.continuousOn.isOpen_inter_preimage hU₁
      hS).preimage (continuous_realSubRef h0), ⟨hx₀U₁, by
        rw [Set.mem_preimage, hπx₀]; exact hx₀S⟩, fun y ↦ σ (π (y.realSubRef h0)),
      fun y ↦ hσ _, by beta_reduce; rw [hπx₀, hσx₀], fun y hy hsoly ↦ ?_,
      fun y hy g hgy ↦ by beta_reduce; rw [hπg y g hy.1 hgy.1], fun y hy ↦ ?_⟩
  · -- A vortex is sent to its Coulomb representative.
    obtain ⟨g, hgS, hgρ⟩ := hπS y hy.1
    refine ⟨g, ?_⟩
    have hgsol : ∀ z, equation ⇑(g • y) z = 0 := fun z ↦
      (equation_smul_eq_zero_iff (by omega) g y z).2 (hsoly z)
    beta_reduce
    rw [← hgρ, hσt (g • y) hgS hgsol (by rw [hgρ]; exact hy.2)]
  · -- In coordinates, `P` is the composite of the smooth maps `σ` and `π`.
    refine ((hσc _ hy.2).comp _ (hπ.contDiffAt (hU₁.mem_nhds hy.1))).congr_of_eventuallyEq
      (Eventually.of_forall fun u ↦ ?_)
    simp only [Function.comp_apply, hρι]

/-- **Divisor coordinates near a vortex.** Let `x₀` be a continuous vortex of `A_m^(k+1)`, `k ≥ 3`,
lying in `A_m^j` for every `j`. There are an open neighbourhood `U` of `x₀` and a map `c` from the
fields to `ℂᵐ` such that

* `c` is gauge invariant on `U`: `c (g · y) = c y` whenever `y` and `g · y` lie in `U`;
* at a vortex `y` of `U`, `c y` is the tuple of coefficients of the monic polynomial whose roots
  are the zeros of `y`, counted with multiplicity;
* `c` is smooth in the real coordinates of the fields at every field of `U`.

It is the divisor of the field projection `exists_isOpen_fieldProjection`. -/
theorem exists_isOpen_contDiffAt_coeffEquiv_sobolevVortexDivisor (hk : 3 ≤ k)
    (x₀ : SobolevFieldSpace f m (k + 1 : ℕ)) (hmem : ∀ j : ℕ, ⇑x₀ ∈ framedFieldSpace f m j)
    (hsol : ∀ z, equation x₀ z = 0) :
    ∃ U : Set (SobolevFieldSpace f m (k + 1 : ℕ)), IsOpen U ∧ x₀ ∈ U ∧
      ∃ c : SobolevFieldSpace f m (k + 1 : ℕ) → Fin m → ℂ,
        (∀ y ∈ U, ∀ g : SobolevTopologicalGaugeGroup hs, g • y ∈ U → c (g • y) = c y) ∧
        (∀ y ∈ U, ∀ hy : ∀ z, equation y z = 0, c y = Sym.coeffEquiv ℂ m
          (sobolevVortexDivisor ⟨_, toFramedFieldSpace_mem_sobolevVortices (by omega) hy⟩)) ∧
        ∀ y ∈ U, ContDiffAt ℝ ∞ (fun u ↦ c (ofRealSubRef (Nat.one_lt_cast.2 Fact.out) u))
          (y.realSubRef (Nat.cast_nonneg (k + 1))) := by
  obtain ⟨U, hU, hx₀U, P, hP, -, hPy, hPg, hPc⟩ :=
    exists_isOpen_fieldProjection (hs := hs) (by omega) x₀ hmem hsol
  set D := fun y : SobolevFieldSpace f m (k + 1 : ℕ) ↦ Sym.coeffEquiv ℂ m
    (sobolevVortexDivisor ⟨_, toFramedFieldSpace_mem_sobolevVortices (by omega) (hP y).2⟩)
  refine ⟨U, hU, hx₀U, D, fun y hy g hgy ↦ by simp only [D, hPg y hy g hgy],
    fun y hy hsoly ↦ ?_, fun y hy ↦ ?_⟩
  · -- Gauges keep the divisor of a vortex.
    obtain ⟨g, hg⟩ := hPy y hy hsoly
    simp only [D, ← hg]
    exact congrArg (Sym.coeffEquiv ℂ m) (sobolevVortexDivisor_smul (by omega) g hsoly)
  · -- `P` is a smooth family of vortices near `y`, so its divisor coefficients are smooth.
    obtain ⟨F, hF, hFev⟩ := exists_contDiffAt_eventually_coeffEquiv_sobolevVortexDivisor_eq
      (by omega) (hPc y hy)
    refine hF.congr_of_eventuallyEq ?_
    filter_upwards [hFev] with u hu
    exact hu (hP _).2

end SobolevFieldSpace

end TauCeti.Vortex
