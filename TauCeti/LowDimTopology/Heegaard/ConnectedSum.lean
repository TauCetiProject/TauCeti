/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LowDimTopology.Heegaard.AddBasepoint
public import TauCeti.LowDimTopology.Heegaard.MapRegion
import TauCeti.Algebra.BigOperators.Pi

/-!
# Connected sum of a Heegaard diagram with the diagram of `S¹ × S²`

A Heegaard diagram of the connected sum `Y # (S¹ × S²)` is obtained from a pointed diagram of `Y`
by a local move inside a region `R₀`: draw a small `α`-circle and a small `β`-circle meeting in two
points `p` and `q`, as when adding a basepoint, and attach a tube joining the lens enclosed by both
circles to the rest of `R₀`. The tube raises the genus by one and makes both new circles
nonseparating; they are then two isotopic curves meeting in two points, the standard genus-one
diagram of `S¹ × S²` (`TauCeti.HeegaardRegionSystem.circleTimesSphere`), summed with the
diagram of `Y` along its annulus. The complement of the new curves consists of the two bigons
`B₁` and `B₂`, the former crescents, and of the region `R₀`, now joined to the lens by the tube.
Each tube end removes an open disc, so the Euler characteristic of `R₀` drops by two. No basepoint
is added.

This file performs the move on the incidence data `TauCeti.HeegaardRegionSystem`
(`TauCeti.HeegaardRegionSystem.sumCircleTimesSphere`) by relabelling the regions of the diagram
with an added basepoint (`TauCeti.HeegaardRegionSystem.addBasepoint`): the lens becomes `R₀`
(`TauCeti.HeegaardRegionSystem.sumCircleTimesSphereRegion`), and the basepoint added in the lens
is dropped (`TauCeti.HeegaardRegionSystem.mapRegion`). The intersection points become
`Point ⊕ Fin 2` and the regions `Region ⊕ Fin 2`, with `Sum.inr 0` and `Sum.inr 1` the bigons. The
two diagrams share their intersection data, so the generators of the connected sum are the
generators `(x, k)` of `TauCeti.HeegaardRegionSystem.addBasepointGenerator`, pairs of a generator
of the original diagram and a new point.

A domain `D` of the connected sum connects `(x, i)` to `(y, j)` exactly when its restriction to the
old regions connects `x` to `y` and `D(B₁) + D(B₂) - 2 D(R₀) = j - i`
(`TauCeti.HeegaardRegionSystem.isDomainBetween_sumCircleTimesSphere_iff`), and its Maslov index
is `μ(D|_old) + D(B₁) + D(B₂) - 2 D(R₀)`
(`TauCeti.HeegaardRegionSystem.maslovIndex_sumCircleTimesSphere`). When `R₀` contains a basepoint,
the domains counted by the hat differential vanish on `R₀`, and they correspond exactly to the
domains counted after adding a basepoint, which vanish on `R₀` and on the lens. So the hat
complex of `Y # (S¹ × S²)` is the hat complex of `Y` tensored with the two-dimensional space `W`
on `p` and `q` with zero differential
(`TauCeti.HeegaardRegionSystem.hatDifferential_sumCircleTimesSphere_comp_addBasepointChainEquiv`),
the chain-level form of `HF̂(Y # (S¹ × S²)) ≅ HF̂(Y) ⊗ HF̂(S¹ × S²)`. The two bigons are the
counted domains from `p` to `q`; they cancel modulo two and put `p` and `q` one apart in relative
Maslov grading.

Unlike adding a basepoint, the connected sum creates a new periodic domain: `B₁ - B₂`, whose
boundary is `α - β`, the class of the sphere `S²` in `S¹ × S²`. A domain of the connected sum is
periodic exactly when its restriction to the old regions is periodic and its multiplicities on the
two bigons add up to twice that on `R₀`
(`TauCeti.HeegaardRegionSystem.mem_periodicDomains_sumCircleTimesSphere_iff`). So the periodic
domains are the old ones, extended by their multiplicity on `R₀` over both bigons, plus multiples
of `B₁ - B₂`, and the connected sum is weakly admissible exactly when the original diagram is
(`TauCeti.HeegaardRegionSystem.weaklyAdmissible_sumCircleTimesSphere_iff`).

## Main definitions

* `TauCeti.HeegaardRegionSystem.sumCircleTimesSphere`: the connected sum of a diagram with the
  diagram of `S¹ × S²`, taken in a region.
* `TauCeti.HeegaardRegionSystem.sumCircleTimesSphereEuler`: its region Euler characteristics.

## Main results

* `TauCeti.HeegaardRegionSystem.isDomainBetween_sumCircleTimesSphere_iff` and
  `TauCeti.HeegaardRegionSystem.maslovIndex_sumCircleTimesSphere`: domains of the connected sum
  and their Maslov indices.
* `TauCeti.HeegaardRegionSystem.mem_periodicDomains_sumCircleTimesSphere_iff` and
  `TauCeti.HeegaardRegionSystem.weaklyAdmissible_sumCircleTimesSphere_iff`: its periodic domains
  and weak admissibility.
* `TauCeti.HeegaardRegionSystem.hatCoefficient_sumCircleTimesSphere`: the hat coefficient from
  `(x, i)` to `(y, j)` is that from `x` to `y` when `i = j` and zero otherwise.
* `TauCeti.HeegaardRegionSystem.hatDifferential_sumCircleTimesSphere_comp_addBasepointChainEquiv`:
  the hat differential of the connected sum is `∂ ⊗ 1` on `CF̂(Y) ⊗ W`.
* `TauCeti.HeegaardRegionSystem.single_mem_hatDomains_sumCircleTimesSphere`: each bigon is a
  counted domain from `(x, p)` to `(x, q)`.

## References

* P. Ozsváth and Z. Szabó, *Holomorphic disks and topological invariants for closed
  three-manifolds*, Ann. of Math. **159** (2004),
  [arXiv:math/0101206](https://arxiv.org/abs/math/0101206), §2 (pointed Heegaard diagrams).
* P. Ozsváth and Z. Szabó, *Holomorphic disks and three-manifold invariants: properties and
  applications*, Ann. of Math. **159** (2004),
  [arXiv:math/0105202](https://arxiv.org/abs/math/0105202) (the connected sum formula
  `HF̂(Y₁ # Y₂) ≅ HF̂(Y₁) ⊗ HF̂(Y₂)`, of which the main theorem here is the chain-level case of the
  standard diagram of `S¹ × S²`).
-/

public section

namespace TauCeti

namespace HeegaardRegionSystem

universe u v w

variable {n : ℕ} {Point : Type u} {Region : Type v} {Basepoint : Type w}
  (H : HeegaardRegionSystem n Point Region Basepoint)

open Function
open scoped TensorProduct

section Construction

variable (r₀ : Region)

/-- The regions of the connected sum with `S¹ × S²` in the region `r₀`, as images of the regions
of the diagram with a basepoint added in `r₀`: the two crescents become the two bigons
`Sum.inr 0` and `Sum.inr 1`, and the lens `Sum.inr 2` is joined to `r₀` by the tube. -/
def sumCircleTimesSphereRegion : Region ⊕ Fin 3 → Region ⊕ Fin 2 :=
  Sum.elim Sum.inl ![Sum.inr 0, Sum.inr 1, Sum.inl r₀]

@[simp]
theorem sumCircleTimesSphereRegion_inl (r : Region) :
    sumCircleTimesSphereRegion r₀ (Sum.inl r) = Sum.inl r :=
  (rfl)

@[simp]
theorem sumCircleTimesSphereRegion_inr_zero :
    sumCircleTimesSphereRegion r₀ (Sum.inr 0) = Sum.inr 0 :=
  (rfl)

@[simp]
theorem sumCircleTimesSphereRegion_inr_one :
    sumCircleTimesSphereRegion r₀ (Sum.inr 1) = Sum.inr 1 :=
  (rfl)

/-- The old regions are kept. -/
@[simp]
theorem sumCircleTimesSphereRegion_comp_inl :
    sumCircleTimesSphereRegion r₀ ∘ Sum.inl = (Sum.inl : Region → Region ⊕ Fin 2) :=
  (rfl)

/-- The lens is joined to `r₀`. -/
@[simp]
theorem sumCircleTimesSphereRegion_inr_two :
    sumCircleTimesSphereRegion r₀ (Sum.inr 2) = Sum.inl r₀ :=
  (rfl)

/-- Every region of the connected sum comes from a region of the diagram with an added
basepoint. -/
theorem sumCircleTimesSphereRegion_surjective : Surjective (sumCircleTimesSphereRegion r₀) := by
  rintro (r | k)
  · exact ⟨Sum.inl r, rfl⟩
  · fin_cases k
    · exact ⟨Sum.inr 0, rfl⟩
    · exact ⟨Sum.inr 1, rfl⟩

/-- The connected sum of the diagram with the genus-one diagram of `S¹ × S²`, taken in the region
`r₀`. Inside `r₀` a new `α`-circle and a new `β`-circle, the last curves, meet in the two new
points `Sum.inr 0` and `Sum.inr 1`, as for `TauCeti.HeegaardRegionSystem.addBasepoint`, and a tube
joins the lens they enclose to the rest of `r₀`. The complementary regions are the old ones, the
label `Sum.inl r₀` now standing for `r₀` joined to the lens, and the two bigons `Sum.inr 0` and
`Sum.inr 1`; the basepoints are the old ones.

This is an abbreviation so that the connected sum visibly has the intersection data of the
diagram with an added basepoint, and hence its generators, also to `simp` and `rw`. -/
abbrev sumCircleTimesSphere :
    HeegaardRegionSystem (n + 1) (Point ⊕ Fin 2) (Region ⊕ Fin 2) Basepoint :=
  (H.addBasepoint r₀).mapRegion (sumCircleTimesSphereRegion_surjective r₀) (Sum.inl ∘ H.basepoint)

/-- The regions to the left of the `α`-arcs: the bigon `B₁` and the region `r₀` for the two new
arcs. -/
theorem sumCircleTimesSphere_alphaLeft :
    (H.sumCircleTimesSphere r₀).alphaLeft =
      Sum.elim (Sum.inl ∘ H.alphaLeft) ![Sum.inr 0, Sum.inl r₀] := by
  funext p
  rcases p with p | k
  · simp
  · fin_cases k <;> simp

/-- The regions to the right of the `α`-arcs: the region `r₀` and the bigon `B₂` for the two new
arcs. -/
theorem sumCircleTimesSphere_alphaRight :
    (H.sumCircleTimesSphere r₀).alphaRight =
      Sum.elim (Sum.inl ∘ H.alphaRight) ![Sum.inl r₀, Sum.inr 1] := by
  funext p
  rcases p with p | k
  · simp
  · fin_cases k <;> simp

/-- The regions to the left of the `β`-arcs: the region `r₀` and the bigon `B₂` for the two new
arcs. -/
theorem sumCircleTimesSphere_betaLeft :
    (H.sumCircleTimesSphere r₀).betaLeft =
      Sum.elim (Sum.inl ∘ H.betaLeft) ![Sum.inl r₀, Sum.inr 1] := by
  funext p
  rcases p with p | k
  · simp
  · fin_cases k <;> simp

/-- The regions to the right of the `β`-arcs: the bigon `B₁` and the region `r₀` for the two new
arcs. -/
theorem sumCircleTimesSphere_betaRight :
    (H.sumCircleTimesSphere r₀).betaRight =
      Sum.elim (Sum.inl ∘ H.betaRight) ![Sum.inr 0, Sum.inl r₀] := by
  funext p
  rcases p with p | k
  · simp
  · fin_cases k <;> simp

end Construction

section Euler

variable [DecidableEq Region]

/-- The region Euler characteristics of the connected sum with `S¹ × S²` in `r₀`: each end of the
tube removes an open disc from `r₀`, so its Euler characteristic drops by two, and the two bigons
are discs. -/
def sumCircleTimesSphereEuler (χ : Region → ℤ) (r₀ : Region) : Region ⊕ Fin 2 → ℤ :=
  Sum.elim (χ - Pi.single r₀ 2) 1

/-- The Euler characteristic of an old region, two less for `r₀`. -/
@[simp]
theorem sumCircleTimesSphereEuler_inl (χ : Region → ℤ) (r₀ r : Region) :
    sumCircleTimesSphereEuler χ r₀ (Sum.inl r) = χ r - (Pi.single r₀ 2 : Region → ℤ) r :=
  (rfl)

/-- The bigons are discs. -/
@[simp]
theorem sumCircleTimesSphereEuler_inr (χ : Region → ℤ) (r₀ : Region) (k : Fin 2) :
    sumCircleTimesSphereEuler χ r₀ (Sum.inr k) = 1 :=
  (rfl)

variable [Fintype Region]

/-- The connected sum has the same total Euler characteristic of regions and two more intersection
points, so `∑ χ(R) - #(α ∩ β)`, the Euler characteristic of the closed surface, drops by two: the
genus goes up by one. -/
theorem sum_sumCircleTimesSphereEuler_sub_card [Fintype Point] (χ : Region → ℤ) (r₀ : Region) :
    ∑ r, sumCircleTimesSphereEuler χ r₀ r - Fintype.card (Point ⊕ Fin 2) =
      ∑ r, χ r - Fintype.card Point - 2 := by
  simp [Fintype.sum_sum_type, Finset.sum_sub_distrib, Fintype.card_sum]
  ring

end Euler

section Domain

variable (r₀ : Region) {x y : H.Generator} {i j : Fin 2}

/-- A domain of the connected sum connects `(x, i)` to `(y, j)` exactly when its restriction to the
old regions connects `x` to `y` and the multiplicities of the two bigons and of `r₀` satisfy
`D(B₁) + D(B₂) - 2 D(r₀) = j - i`. -/
theorem isDomainBetween_sumCircleTimesSphere_iff {D : Region ⊕ Fin 2 → ℤ} :
    (H.sumCircleTimesSphere r₀).IsDomainBetween (H.addBasepointGenerator r₀ x i)
        (H.addBasepointGenerator r₀ y j) D ↔
      H.IsDomainBetween x y (D ∘ Sum.inl) ∧
        D (Sum.inr 0) + D (Sum.inr 1) - 2 * D (Sum.inl r₀) = (j : ℤ) - i := by
  rw [isDomainBetween_mapRegion_iff, isDomainBetween_addBasepoint_iff]
  simp only [comp_apply, sumCircleTimesSphereRegion_inl, sumCircleTimesSphereRegion_inr_zero,
    sumCircleTimesSphereRegion_inr_one, sumCircleTimesSphereRegion_inr_two]
  constructor
  · rintro ⟨hD, hs⟩
    exact ⟨hD, by linarith⟩
  · rintro ⟨hD, hs⟩
    exact ⟨hD, by linarith⟩

/-- A domain of the connected sum with `S¹ × S²` in `r₀` is periodic exactly when its restriction
to the old regions is periodic and the multiplicities of the two bigons add up to twice that of
`r₀`. -/
theorem mem_periodicDomains_sumCircleTimesSphere_iff {P : Region ⊕ Fin 2 → ℤ} :
    P ∈ (H.sumCircleTimesSphere r₀).periodicDomains ↔
      P ∘ Sum.inl ∈ H.periodicDomains ∧ P (Sum.inr 0) + P (Sum.inr 1) = 2 * P (Sum.inl r₀) := by
  rw [mem_periodicDomains_iff, mem_periodicDomains_iff]
  simp [funext_iff, Sum.forall, Fin.forall_fin_two]
  grind

/-- The difference `B₁ - B₂` of the two bigons is a periodic domain of the connected sum, with
boundary `α - β`: the class of the sphere `S²` in `S¹ × S²`. -/
theorem single_sub_single_mem_periodicDomains_sumCircleTimesSphere [DecidableEq Region] :
    Pi.single (Sum.inr 0) 1 - Pi.single (Sum.inr 1) 1 ∈
      (H.sumCircleTimesSphere r₀).periodicDomains := by
  rw [H.mem_periodicDomains_sumCircleTimesSphere_iff r₀]
  refine ⟨?_, by simp⟩
  have : (Pi.single (Sum.inr 0) 1 - Pi.single (Sum.inr 1) 1 : Region ⊕ Fin 2 → ℤ) ∘ Sum.inl =
      0 := funext fun r => by simp
  rw [this]
  exact zero_mem _

/-- The connected sum with `S¹ × S²` in any region is weakly admissible exactly when the original
diagram is: its new periodic domains `k (B₁ - B₂)` have coefficients of both signs. -/
theorem weaklyAdmissible_sumCircleTimesSphere_iff :
    (H.sumCircleTimesSphere r₀).WeaklyAdmissible ↔ H.WeaklyAdmissible := by
  simp only [weaklyAdmissible_iff, H.mem_periodicDomains_sumCircleTimesSphere_iff r₀]
  constructor
  · intro h P hP hP₀
    have := h (Sum.elim P fun _ => P r₀) ⟨by simpa using hP, by simp [two_mul]⟩ fun r => by
      rcases r with r | -
      · exact hP₀ r
      · exact hP₀ r₀
    funext r
    simpa using congrFun this (Sum.inl r)
  · rintro h P ⟨hP, hs⟩ hP₀
    have hold := h _ hP fun r => hP₀ (Sum.inl r)
    have hr := congrFun hold r₀
    have h0 := hP₀ (Sum.inr 0)
    have h1 := hP₀ (Sum.inr 1)
    obtain ⟨h0', h1'⟩ : P (Sum.inr 0) = 0 ∧ P (Sum.inr 1) = 0 := by
      simp only [comp_apply, Pi.zero_apply] at h0 h1 hr
      omega
    funext r
    rcases r with r | k
    · exact congrFun hold r
    · fin_cases k <;> simp [h0', h1']

end Domain

section MaslovIndex

variable [Fintype Point] [DecidableEq Region] [Fintype Region] (r₀ : Region)

/-- The Maslov index of a domain `D` of the connected sum is that of its pullback `D ∘ f` to the
diagram with an added basepoint, where `f` joins the lens to `r₀`, minus `2 D(r₀)`: the tube
lowers the Euler characteristic of `r₀` and the lens together by two. -/
theorem maslovIndex_sumCircleTimesSphere_eq_maslovIndex_addBasepoint_sub (χ : Region → ℤ)
    (x y : (H.addBasepoint r₀).Generator) (D : Region ⊕ Fin 2 → ℤ) :
    (H.sumCircleTimesSphere r₀).maslovIndex (sumCircleTimesSphereEuler χ r₀) x y D =
      (H.addBasepoint r₀).maslovIndex (addBasepointEuler χ r₀) x y
        (D ∘ sumCircleTimesSphereRegion r₀) - 2 * D (Sum.inl r₀) := by
  rw [maslovIndex_mapRegion (χ := addBasepointEuler χ r₀)]
  simp only [Fintype.sum_sum_type, sumCircleTimesSphereEuler_inl, sumCircleTimesSphereEuler_inr,
    addBasepointEuler_inl, addBasepointEuler_inr, Fin.sum_univ_two, Fin.sum_univ_three,
    sumCircleTimesSphereRegion_inl, sumCircleTimesSphereRegion_inr_zero,
    sumCircleTimesSphereRegion_inr_one, sumCircleTimesSphereRegion_inr_two,
    Fintype.sum_intCast_sub_pi_single_mul]
  push_cast
  ring

/-- The Maslov index of a domain `D` of the connected sum from `(x, i)` to `(y, j)` is
`μ(D|_old) + D(B₁) + D(B₂) - 2 D(r₀)`, where `D|_old` is its restriction to the old regions. -/
theorem maslovIndex_sumCircleTimesSphere (χ : Region → ℤ) (x y : H.Generator) (i j : Fin 2)
    (D : Region ⊕ Fin 2 → ℤ) :
    (H.sumCircleTimesSphere r₀).maslovIndex (sumCircleTimesSphereEuler χ r₀)
        (H.addBasepointGenerator r₀ x i) (H.addBasepointGenerator r₀ y j) D =
      H.maslovIndex χ x y (D ∘ Sum.inl) + D (Sum.inr 0) + D (Sum.inr 1) -
        2 * D (Sum.inl r₀) := by
  rw [maslovIndex_sumCircleTimesSphere_eq_maslovIndex_addBasepoint_sub, maslovIndex_addBasepoint]
  simp only [comp_apply, sumCircleTimesSphereRegion_inl, sumCircleTimesSphereRegion_inr_zero,
    sumCircleTimesSphereRegion_inr_one, sumCircleTimesSphereRegion_inr_two]
  -- The pullback restricted to the old regions is the restriction of `D`.
  rw [comp_assoc, sumCircleTimesSphereRegion_comp_inl]
  ring

end MaslovIndex

section Hat

variable [Fintype Point] [DecidableEq Region] [Fintype Region] (r₀ : Region) {χ : Region → ℤ}

/-- When `r₀` contains a basepoint, a domain of the connected sum is counted by its hat
differential exactly when its pullback, which puts the multiplicity of `r₀` on the lens, is
counted by the hat differential of the diagram with an added basepoint. -/
theorem mem_hatDomains_sumCircleTimesSphere_iff (hr₀ : r₀ ∈ Set.range H.basepoint)
    {x y : (H.addBasepoint r₀).Generator} {D : Region ⊕ Fin 2 → ℤ} :
    D ∈ (H.sumCircleTimesSphere r₀).hatDomains (sumCircleTimesSphereEuler χ r₀) x y ↔
      D ∘ sumCircleTimesSphereRegion r₀ ∈
        (H.addBasepoint r₀).hatDomains (addBasepointEuler χ r₀) x y := by
  have hnonneg : 0 ≤ D ↔ 0 ≤ D ∘ sumCircleTimesSphereRegion r₀ :=
    (sumCircleTimesSphereRegion_surjective r₀).forall
  obtain ⟨z₀, rfl⟩ := hr₀
  rw [mem_hatDomains_iff, mem_hatDomains_iff, isDomainBetween_mapRegion_iff, hnonneg,
    maslovIndex_sumCircleTimesSphere_eq_maslovIndex_addBasepoint_sub]
  simp only [addBasepoint_basepoint, Sum.forall, Sum.elim_inl, Sum.elim_inr, comp_apply,
    sumCircleTimesSphereRegion_inl, sumCircleTimesSphereRegion_inr_two, forall_const]
  constructor
  · rintro ⟨hD, hz, hD₀, hμ⟩
    have h₀ := hz z₀
    exact ⟨hD, ⟨hz, h₀⟩, hD₀, by rw [h₀] at hμ; simpa using hμ⟩
  · rintro ⟨hD, ⟨hz, -⟩, hD₀, hμ⟩
    have h₀ := hz z₀
    exact ⟨hD, hz, hD₀, by rw [h₀]; simpa using hμ⟩

/-- When `r₀` contains a basepoint, the domains counted by the hat differential of the diagram
with an added basepoint in `r₀` are the pullbacks of those counted by the hat differential of the
connected sum: they vanish on `r₀` and on the lens alike. -/
theorem hatDomains_addBasepoint_eq_image_hatDomains_sumCircleTimesSphere
    (hr₀ : r₀ ∈ Set.range H.basepoint) (x y : (H.addBasepoint r₀).Generator) :
    (H.addBasepoint r₀).hatDomains (addBasepointEuler χ r₀) x y =
      (· ∘ sumCircleTimesSphereRegion r₀) ''
        (H.sumCircleTimesSphere r₀).hatDomains (sumCircleTimesSphereEuler χ r₀) x y := by
  ext E
  constructor
  · intro hE
    obtain ⟨z₀, hz₀⟩ := hr₀
    have hz := (mem_hatDomains_iff.mp hE).2.1
    -- The lens and `r₀` both contain a basepoint, so `E` vanishes on both.
    have hlens : E (Sum.inr 2) = E (Sum.inl r₀) := by
      have h₁ := hz (Sum.inr ())
      have h₂ := hz (Sum.inl z₀)
      simp only [addBasepoint_basepoint, Sum.elim_inr, Sum.elim_inl, comp_apply] at h₁ h₂
      rw [h₁, ← hz₀, h₂]
    have hcomp : (Sum.elim (E ∘ Sum.inl) ![E (Sum.inr 0), E (Sum.inr 1)] :
        Region ⊕ Fin 2 → ℤ) ∘ sumCircleTimesSphereRegion r₀ = E := by
      funext s
      rcases s with r | k
      · simp
      · fin_cases k <;> simp [hlens]
    refine ⟨_, ?_, hcomp⟩
    rw [H.mem_hatDomains_sumCircleTimesSphere_iff r₀ ⟨z₀, hz₀⟩, hcomp]
    exact hE
  · rintro ⟨D, hD, rfl⟩
    exact (H.mem_hatDomains_sumCircleTimesSphere_iff r₀ hr₀).mp hD

/-- When `r₀` contains a basepoint, the connected sum with `S¹ × S²` in `r₀` and the diagram with
an added basepoint in `r₀` have the same hat coefficients between their common generators. -/
theorem hatCoefficient_sumCircleTimesSphere_eq_hatCoefficient_addBasepoint
    (hr₀ : r₀ ∈ Set.range H.basepoint) (x y : (H.addBasepoint r₀).Generator) :
    (H.sumCircleTimesSphere r₀).hatCoefficient (sumCircleTimesSphereEuler χ r₀) x y =
      (H.addBasepoint r₀).hatCoefficient (addBasepointEuler χ r₀) x y := by
  rw [hatCoefficient_def, hatCoefficient_def,
    H.hatDomains_addBasepoint_eq_image_hatDomains_sumCircleTimesSphere r₀ hr₀,
    Set.ncard_image_of_injective _ (sumCircleTimesSphereRegion_surjective r₀).injective_comp_right]

/-- The coefficient of the hat differential of the connected sum with `S¹ × S²` in a region
containing a basepoint, from `(x, i)` to `(y, j)`, is that of the original diagram from `x` to `y`
when `i = j`, and zero otherwise: from `p` to `q` the counted domains are the pairs of an old
domain of Maslov index zero and one of the two bigons, which cancel modulo two. -/
theorem hatCoefficient_sumCircleTimesSphere (hr₀ : r₀ ∈ Set.range H.basepoint)
    (x y : H.Generator) (i j : Fin 2) :
    (H.sumCircleTimesSphere r₀).hatCoefficient (sumCircleTimesSphereEuler χ r₀)
        (H.addBasepointGenerator r₀ x i) (H.addBasepointGenerator r₀ y j) =
      if i = j then H.hatCoefficient χ x y else 0 := by
  rw [H.hatCoefficient_sumCircleTimesSphere_eq_hatCoefficient_addBasepoint r₀ hr₀,
    H.hatCoefficient_addBasepoint r₀ hr₀]

/-- Each of the two bigons is a domain counted by the hat differential of the connected sum from
`(x, p)` to `(x, q)`: it has Maslov index one and avoids all basepoints, so `p` and `q` lie one
apart in relative Maslov grading. -/
theorem single_mem_hatDomains_sumCircleTimesSphere (x : H.Generator) (k : Fin 2) :
    Pi.single (Sum.inr k) 1 ∈
      (H.sumCircleTimesSphere r₀).hatDomains (sumCircleTimesSphereEuler χ r₀)
        (H.addBasepointGenerator r₀ x 0) (H.addBasepointGenerator r₀ x 1) := by
  have hinl : (Pi.single (Sum.inr k) 1 : Region ⊕ Fin 2 → ℤ) ∘ Sum.inl = 0 :=
    funext fun r => by simp
  rw [mem_hatDomains_iff, isDomainBetween_sumCircleTimesSphere_iff,
    maslovIndex_sumCircleTimesSphere, hinl]
  refine ⟨⟨isDomainBetween_zero x, ?_⟩, fun z => by simp, fun r => ?_, ?_⟩
  · fin_cases k <;> simp
  · rcases r with r | m
    · simp
    · fin_cases k <;> fin_cases m <;> simp
  · fin_cases k <;> simp

end Hat

section Differential

variable [Fintype Point] [DecidableEq Region] [Fintype Region] (r₀ : Region) {χ : Region → ℤ}

/-- When `r₀` contains a basepoint, the connected sum with `S¹ × S²` in `r₀` and the diagram with
an added basepoint in `r₀` have the same hat differential on their common chain group. -/
theorem hatDifferential_sumCircleTimesSphere_eq_hatDifferential_addBasepoint
    (hr₀ : r₀ ∈ Set.range H.basepoint) :
    (H.sumCircleTimesSphere r₀).hatDifferential (sumCircleTimesSphereEuler χ r₀) =
      (H.addBasepoint r₀).hatDifferential (addBasepointEuler χ r₀) := by
  ext x y
  simp only [LinearMap.comp_apply, Finsupp.lsingle_apply, hatDifferential_single_apply,
    H.hatCoefficient_sumCircleTimesSphere_eq_hatCoefficient_addBasepoint r₀ hr₀]

/-- The hat differential of the connected sum with `S¹ × S²` in a region containing a basepoint is
`∂ ⊗ 1` on `CF̂(Y) ⊗ W`, where `∂` is the hat differential of the original diagram and `W` is the
two-dimensional space on the two new points with zero differential: under the identification
`TauCeti.HeegaardRegionSystem.addBasepointChainEquiv`, sending `x ⊗ k` to the generator `(x, k)`,
the hat complex of the connected sum is the tensor product of the original one with `W`. -/
theorem hatDifferential_sumCircleTimesSphere_comp_addBasepointChainEquiv
    (hr₀ : r₀ ∈ Set.range H.basepoint) :
    (H.sumCircleTimesSphere r₀).hatDifferential (sumCircleTimesSphereEuler χ r₀) ∘ₗ
        (H.addBasepointChainEquiv r₀).toLinearMap =
      (H.addBasepointChainEquiv r₀).toLinearMap ∘ₗ
        TensorProduct.map (H.hatDifferential χ) LinearMap.id := by
  rw [H.hatDifferential_sumCircleTimesSphere_eq_hatDifferential_addBasepoint r₀ hr₀]
  exact H.hatDifferential_comp_addBasepointChainEquiv r₀ hr₀

end Differential

end HeegaardRegionSystem

end TauCeti
