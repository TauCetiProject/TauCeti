/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.PowerSeries.Basic
public import TauCeti.Algebra.CharP.Frobenius.Fixed
public import TauCeti.RingTheory.Huber.Normed
public import TauCeti.RingTheory.Perfectoid.Cyclotomic.Basic

import TauCeti.RingTheory.Huber.ValuedField


/-!
# Charts in `A_inf`

Let `A` be a `p`-adically complete ring in which `p` is not a unit, `A♭ = PreTilt A p` its tilt,
`A_inf = W(A♭)` and `θ : A_inf → A` Fontaine's map. The motivating case is `A = O_C`, the valuation
ring of `ℂ_p`. For `f ≥ 1`, the *constants* `𝔽_{p^f} ⊆ A♭` are the elements fixed by the
`p ^ f`-power Frobenius (`TauCeti.frobeniusFixedSubring`), and `Λ = W(𝔽_{p^f})` maps into `A_inf`
by functoriality of Witt vectors. When `A` is a domain, `𝔽_{p^f}` is a finite field
(`TauCeti.isField_frobeniusFixedSubring`), with exactly `p ^ f` elements when `A♭` is absolutely
integrally closed, as it is for `A = O_C`
(`TauCeti.IsAbsolutelyIntegrallyClosed.natCard_frobeniusFixedSubring`).

A *chart* (`TauCeti.Perfectoid.Chart`) requires `f ≠ 0` and consists of a `Λ`-algebra map
`Λ⟦X⟧ → A_inf`, an element
`ϖ♭ ∈ A♭` with `X ↦ z = [ϖ♭]`, an integer `e ≥ 0` and a unit `A(X)` of `Λ⟦X⟧`, such that the image
`E = z ^ e A(z) + p` of `X ^ e A(X) + p` generates the kernel of `θ`. Its ring `S ⊆ A_inf` is the
image of `Λ⟦X⟧`. For `A = O_C` the condition on `E` says that `E` is a unit multiple of the period
`ξ` (`TauCeti.Perfectoid.Chart.associated_E_cyclotomicXi`). A chart stands in for the embedding
`W(k)⟦u⟧ → A_inf`, `u ↦ [π♭]`, attached to a uniformiser `π` of a `p`-adic field and compatible
`p`-power roots of it.

Applying `θ` to `E` gives `θ(z) ^ e θ(A(z)) = -p` with `θ(A(z))` a unit of `A`. Since `p` is not a
unit, this forces `e ≠ 0` and shows that `θ(z)`, and hence `z` and `ϖ♭`, are not units; so a
chart need not require `z` to be a nonunit, as this follows from the other conditions.

## Main definitions

* `TauCeti.Perfectoid.Chart`: a chart in `A_inf`.
* `TauCeti.Perfectoid.Chart.z`, `TauCeti.Perfectoid.Chart.E`, `TauCeti.Perfectoid.Chart.S`: the
  elements `z = [ϖ♭]` and `E = z ^ e A(z) + p` of `A_inf`, and the ring of the chart.

## Main results

* `TauCeti.Perfectoid.Chart.ext`: a chart is determined by its map, `e` and `A(X)`.
* `TauCeti.Perfectoid.Chart.ker_fontaineTheta_eq_span_E`: `E` generates the kernel of `θ`, and
  `TauCeti.Perfectoid.Chart.associated_E_cyclotomicXi`: for `A = O_C`, `E` is a unit multiple of
  `ξ`.
* `TauCeti.Perfectoid.Chart.untilt_pow_mul_fontaineTheta_unitSeries`: `θ(z) ^ e θ(A(z)) = -p`.
* `TauCeti.Perfectoid.Chart.e_ne_zero`, `TauCeti.Perfectoid.Chart.not_isUnit_z`: `e ≠ 0` and `z`
  is not a unit.

## References

* M. Kisin, *Crystalline representations and F-crystals*, in *Algebraic geometry and number
  theory*, Progr. Math. 253 (2006), for the embedding `W(k)⟦u⟧ → A_inf`.
* B. Bhatt, M. Morrow, P. Scholze, *Integral p-adic Hodge theory*, Publ. Math. IHÉS 128 (2018),
  §4, for Breuil–Kisin rings inside `A_inf`.
* The definition follows `New.Lift.Chart` of the formal proof grh-lean
  (https://github.com/lsernau/grh-lean, `src/Lib/PadicHodge/Kisin/Charts.lean`, Apache 2.0), with
  the condition on `E` stated through the kernel of `θ` instead of a chosen `ξ`.
-/

public section

open PowerSeries WittVector

namespace TauCeti.Perfectoid

section Chart

variable (p : ℕ) [Fact p.Prime] (A : Type*) [CommRing A] [Fact ¬IsUnit (p : A)]
  [IsAdicComplete (Ideal.span {(p : A)}) A]

/-- A *chart* in `A_inf = W(A♭)`, for `A♭ = PreTilt A p`, with constants `Λ = W(𝔽_{p^f})`, where
`𝔽_{p^f} ⊆ A♭` is the subring of elements fixed by the `p ^ f`-power Frobenius. It consists of a
`Λ`-algebra map `Λ⟦X⟧ → A_inf`, an element `ϖ♭ ∈ A♭` such that `X ↦ z = [ϖ♭]`, an integer
`e ≥ 0` and a unit `A(X)` of `Λ⟦X⟧`, such that the image `E` of `X ^ e A(X) + p` generates the
kernel of Fontaine's map `θ : A_inf → A`.

The image of `Λ⟦X⟧` is the ring `TauCeti.Perfectoid.Chart.S` of the chart. The conditions force
`e ≠ 0` and that `z` is not a unit (`TauCeti.Perfectoid.Chart.e_ne_zero`,
`TauCeti.Perfectoid.Chart.not_isUnit_z`). The constant-field exponent `f` is nonzero, so the
constants form a finite field when `A` is a domain. -/
structure Chart (f : ℕ) where
  /-- The constant-field exponent is positive. -/
  f_ne_zero : f ≠ 0
  /-- The map `Λ⟦X⟧ → A_inf` of the chart. -/
  seriesMap : (WittVector p (frobeniusFixedSubring (PreTilt A p) p f))⟦X⟧ →+*
    WittVector p (PreTilt A p)
  /-- The map of the chart is `Λ`-linear: on constants it is the inclusion `Λ → A_inf`. -/
  seriesMap_comp_C :
    seriesMap.comp C = WittVector.map (frobeniusFixedSubring (PreTilt A p) p f).subtype
  /-- The element `ϖ♭` of the tilt with `X ↦ [ϖ♭]`. For the chart of a uniformiser `π` of a
  `p`-adic field, `ϖ♭` is a compatible system of `p`-power roots of `π`. -/
  uniformizer : PreTilt A p
  /-- The map of the chart sends `X` to the Teichmüller lift `z = [ϖ♭]`. -/
  seriesMap_X : seriesMap X = teichmuller p uniformizer
  /-- The exponent `e` in `E = z ^ e A(z) + p`. -/
  e : ℕ
  /-- The unit `A(X)` in `E = z ^ e A(z) + p`. -/
  unitSeries : ((WittVector p (frobeniusFixedSubring (PreTilt A p) p f))⟦X⟧)ˣ
  /-- The image `E = z ^ e A(z) + p` of `X ^ e A(X) + p` generates the kernel of `θ`. -/
  ker_fontaineTheta : RingHom.ker (fontaineTheta A p) =
    Ideal.span {teichmuller p uniformizer ^ e * seriesMap unitSeries + p}

namespace Chart

variable {p A} {f : ℕ} (c : Chart p A f)

/-- The element `z = [ϖ♭]` of `A_inf`, the image of `X` under the map of the chart. -/
noncomputable def z : WittVector p (PreTilt A p) :=
  teichmuller p c.uniformizer

/-- The element `E = z ^ e A(z) + p` of `A_inf`, the image of `X ^ e A(X) + p`. -/
noncomputable def E : WittVector p (PreTilt A p) :=
  c.z ^ c.e * c.seriesMap c.unitSeries + p

/-- The ring `S ⊆ A_inf` of the chart: the image of `Λ⟦X⟧`. -/
noncomputable def S : Subring (WittVector p (PreTilt A p)) :=
  c.seriesMap.range

/-- The element `z` is the Teichmüller lift of `ϖ♭`. -/
theorem z_def : c.z = teichmuller p c.uniformizer := (rfl)

/-- The element `E` is `z ^ e A(z) + p`. -/
theorem E_def : c.E = c.z ^ c.e * c.seriesMap c.unitSeries + p := (rfl)

/-- The ring of the chart is the image of `Λ⟦X⟧`. -/
theorem S_def : c.S = c.seriesMap.range := (rfl)

/-- The map of the chart sends a constant `a ∈ Λ` to its image in `A_inf`. -/
@[simp]
theorem seriesMap_C (a : WittVector p (frobeniusFixedSubring (PreTilt A p) p f)) :
    c.seriesMap (C a) = WittVector.map (frobeniusFixedSubring (PreTilt A p) p f).subtype a :=
  RingHom.congr_fun c.seriesMap_comp_C a

/-- The map of the chart sends `X` to `z`. -/
@[simp]
theorem seriesMap_X_eq_z : c.seriesMap X = c.z := by
  rw [c.seriesMap_X, z_def]

/-- The map of the chart sends `X ^ e A(X) + p` to `E`. -/
theorem seriesMap_X_pow_mul_add :
    c.seriesMap ((X : (WittVector p (frobeniusFixedSubring (PreTilt A p) p f))⟦X⟧) ^ c.e *
      c.unitSeries + p) = c.E := by
  rw [map_add, map_mul, map_pow, map_natCast, seriesMap_X_eq_z, E_def]

/-- **Extensionality for charts.** A chart is determined by its map, the exponent `e` and the unit
`A(X)`: the map determines `ϖ♭` as the zeroth Witt coordinate of the image of `X`. -/
@[ext]
theorem ext {c d : Chart p A f} (hmap : c.seriesMap = d.seriesMap) (he : c.e = d.e)
    (hA : c.unitSeries = d.unitSeries) : c = d := by
  have hϖ : c.uniformizer = d.uniformizer := by
    rw [← teichmuller_coeff_zero p c.uniformizer, ← teichmuller_coeff_zero p d.uniformizer,
      ← c.seriesMap_X, ← d.seriesMap_X, hmap]
  cases c
  cases d
  simp_all

/-- Membership in the ring of a chart: being the image of a power series. -/
@[simp]
theorem mem_S {x : WittVector p (PreTilt A p)} : x ∈ c.S ↔ ∃ g, c.seriesMap g = x := by
  rw [S_def, RingHom.mem_range]

/-- The image of a power series lies in the ring of the chart. -/
theorem seriesMap_mem_S (g : (WittVector p (frobeniusFixedSubring (PreTilt A p) p f))⟦X⟧) :
    c.seriesMap g ∈ c.S :=
  c.mem_S.mpr ⟨g, rfl⟩

/-- The constants `Λ` lie in the ring of the chart. -/
theorem map_subtype_mem_S (a : WittVector p (frobeniusFixedSubring (PreTilt A p) p f)) :
    WittVector.map (frobeniusFixedSubring (PreTilt A p) p f).subtype a ∈ c.S :=
  c.seriesMap_C a ▸ c.seriesMap_mem_S (C a)

/-- The element `z` lies in the ring of the chart. -/
theorem z_mem_S : c.z ∈ c.S :=
  c.seriesMap_X_eq_z ▸ c.seriesMap_mem_S X

/-- The element `E` lies in the ring of the chart. -/
theorem E_mem_S : c.E ∈ c.S :=
  c.seriesMap_X_pow_mul_add ▸ c.seriesMap_mem_S _

/-- **`E` generates the kernel of Fontaine's map.** -/
theorem ker_fontaineTheta_eq_span_E : RingHom.ker (fontaineTheta A p) = Ideal.span {c.E} := by
  rw [c.ker_fontaineTheta, E_def, z_def]

/-- Fontaine's map kills `E`. -/
@[simp]
theorem fontaineTheta_E : fontaineTheta A p c.E = 0 := by
  rw [← RingHom.mem_ker, ker_fontaineTheta_eq_span_E]
  exact Ideal.mem_span_singleton_self c.E

/-- Fontaine's map sends `z = [ϖ♭]` to the untilt of `ϖ♭`. -/
@[simp]
theorem fontaineTheta_z : fontaineTheta A p c.z = c.uniformizer.untilt := by
  rw [z_def, fontaineTheta_teichmuller]

/-- Fontaine's map sends the unit `A(z)` to a unit of `A`. -/
theorem isUnit_fontaineTheta_unitSeries :
    IsUnit (fontaineTheta A p (c.seriesMap c.unitSeries)) :=
  (c.unitSeries.isUnit.map c.seriesMap).map (fontaineTheta A p)

/-- **The equation of a chart in `A`.** Applying Fontaine's map to `E` gives
`θ(z) ^ e θ(A(z)) = -p`, where `θ(z)` is the untilt of `ϖ♭` and `θ(A(z))` is a unit of `A`
(`TauCeti.Perfectoid.Chart.isUnit_fontaineTheta_unitSeries`). -/
theorem untilt_pow_mul_fontaineTheta_unitSeries :
    c.uniformizer.untilt ^ c.e * fontaineTheta A p (c.seriesMap c.unitSeries) = -p := by
  have h := c.fontaineTheta_E
  rw [E_def, map_add, map_mul, map_pow, map_natCast, fontaineTheta_z] at h
  exact eq_neg_of_add_eq_zero_left h

/-- The untilt of `ϖ♭` is not a unit of `A`: otherwise `-p = θ(z) ^ e θ(A(z))` would be one. -/
theorem not_isUnit_untilt_uniformizer : ¬IsUnit c.uniformizer.untilt := fun h ↦
  (Fact.out : ¬IsUnit (p : A)) <| (IsUnit.neg_iff _).mp <|
    c.untilt_pow_mul_fontaineTheta_unitSeries ▸ (h.pow c.e).mul c.isUnit_fontaineTheta_unitSeries

/-- The element `ϖ♭` is not a unit of the tilt. -/
theorem not_isUnit_uniformizer : ¬IsUnit c.uniformizer := fun h ↦
  c.not_isUnit_untilt_uniformizer (h.map PreTilt.untilt)

/-- **The element `z` is not a unit of `A_inf`.** -/
theorem not_isUnit_z : ¬IsUnit c.z := fun h ↦
  c.not_isUnit_untilt_uniformizer (c.fontaineTheta_z ▸ h.map (fontaineTheta A p))

/-- **The exponent of a chart is nonzero.** For `e = 0` the equation of the chart would make
`-p = θ(A(z))` a unit of `A`. -/
theorem e_ne_zero : c.e ≠ 0 := fun he ↦ by
  have h := c.untilt_pow_mul_fontaineTheta_unitSeries
  rw [he, pow_zero, one_mul] at h
  exact (Fact.out : ¬IsUnit (p : A))
    ((IsUnit.neg_iff _).mp (h ▸ c.isUnit_fontaineTheta_unitSeries))

end Chart

end Chart

section PerfectoidField

open TauCeti.WittVector
open scoped _root_.NormedField Valued

variable {p : ℕ} [Fact p.Prime] {C : Type*} [NontriviallyNormedField C] [IsUltrametricDist C]
  [CompleteSpace C] [IsPerfectoidTateRing p C] [Fact ¬IsUnit (p : 𝒪[C])]
  [IsAdicComplete (Ideal.span {(p : 𝒪[C])}) 𝒪[C]] {f : ℕ}

/-- **`E` is a unit multiple of `ξ`.** For the valuation ring `O_C` of a complete perfectoid
nonarchimedean field and `ε ∈ O_C♭` such that the untilt of `ε ^ (1 / p)` is a primitive `p`-th
root of unity, the element `E` of a chart is a unit multiple of the period `ξ` attached to `ε`. -/
theorem Chart.associated_E_cyclotomicXi (c : Chart p 𝒪[C] f) (ε : PreTilt 𝒪[C] p)
    (hε : IsPrimitiveRoot
      (PreTilt.untilt ((_root_.frobeniusEquiv (PreTilt 𝒪[C] p) p).symm ε)) p) :
    Associated c.E (cyclotomicXi p ε) :=
  ((Huber.isRingOfIntegralElements_integer C).ker_fontaineTheta_eq_span_iff_associated_cyclotomicXi
    (hε.geom_sum_eq_zero (Fact.out : p.Prime).one_lt)).mp c.ker_fontaineTheta_eq_span_E

end PerfectoidField

end TauCeti.Perfectoid
