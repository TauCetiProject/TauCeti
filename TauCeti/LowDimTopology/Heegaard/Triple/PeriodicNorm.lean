/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LowDimTopology.Heegaard.PeriodicNorm
public import TauCeti.LowDimTopology.Heegaard.Triple.SpincAdmissibility

/-!
# Admissibility of Heegaard triples from norms on doubly periodic domains

The triangle maps of Heegaard Floer homology count holomorphic triangles in a pointed Heegaard
triple diagram `(Σ, α, β, γ, z)`, and they are finite sums when the triple is weakly or strongly
admissible: every nonzero sum `P` of doubly periodic domains has coefficients of both signs, or a
coefficient larger than half the change `μ(E + P) - μ(E)` of the Maslov index of a triangle domain
`E` (`TauCeti.HeegaardTripleRegionSystem.WeaklyAdmissible` and
`TauCeti.HeegaardTripleRegionSystem.StronglyAdmissible`). As for a single diagram, Ozsváth and
Szabó produce such triples by winding the attaching curves, which creates regions on which every
nonzero sum of doubly periodic domains has large positive and negative multiplicities, measured by
a norm. This file is the part of that argument which takes place on the incidence data
`TauCeti.HeegaardTripleRegionSystem`, in parallel with
`TauCeti.LowDimTopology.Heegaard.PeriodicNorm` for diagrams; both apply the criteria for subgroups
of `Region → ℤ` of that file, `TauCeti.forall_nonneg_eq_zero_of_forall_exists_mul_norm_le`,
`TauCeti.forall_ne_zero_exists_half_lt_of_forall_exists_mul_norm_le` and
`TauCeti.exists_forall_ne_zero_exists_half_lt_of_forall_exists_mul_norm_le`, the last one to the
finitely many changes of the Maslov index at triangle domains with given corners, which are bounded
by the norm with the lattice bound `AddMonoidHom.exists_forall_abs_le_mul_norm_of_injective`.

The norms are the sup norms `‖ν P‖` of an additive map `ν : (Region → ℤ) →+ (κ → ℤ)`, with `κ`
finite, injective on the sums of doubly periodic domains; in the winding argument `ν P` records the
multiplicities of the boundary of `P` on the attaching curves.

* **Weak admissibility.** If, for some `D > 0`, every sum of doubly periodic domains `P` has a
  region of multiplicity at least `D * ‖ν P‖`, then the triple is weakly admissible
  (`TauCeti.HeegaardTripleRegionSystem.weaklyAdmissible_of_forall_exists_mul_norm_le`).
* **The Maslov index is bounded by the norm.** There is a constant `C` with
  `|μ(E + P) - μ(E)| ≤ C * ‖ν P‖` for every sum of doubly periodic domains `P` and every triangle
  domain `E`, whatever its corners
  (`TauCeti.HeegaardTripleRegionSystem.exists_abs_periodicMaslovIndex_le_mul_norm`). For fixed
  corners `x`, `y`, `w` the change of the Maslov index is one additive functional of `P`, the same
  at all triangle domains with these corners
  (`HeegaardTripleRegionSystem.IsTriangleDomain.periodicMaslovIndex_eq_of_isTriangleDomain`), and
  there are finitely many corners. On a geometric triple the change is the pairing of
  `c₁(s_z(ψ))` with the class of `P` for a triangle `ψ` with domain `E`, so this bounds the Chern
  class pairings of all spin^c structures of triangles by the norm.
* **Strong admissibility.** If moreover `μ(E + P) - μ(E) ≤ C * ‖ν P‖` on sums of doubly periodic
  domains, with `C < 2 * D`, then the triple is strongly admissible at `E`
  (`TauCeti.HeegaardTripleRegionSystem.stronglyAdmissible_of_forall_exists_mul_norm_le`). Combining
  the two, some `C` depending only on the triple, the Euler characteristics `χ` and `ν` makes every
  `D > C` force strong admissibility at all triangle domains at once
  (`HeegaardTripleRegionSystem.exists_forall_stronglyAdmissible_of_forall_exists_mul_norm_le`),
  which on a geometric triple is strong admissibility for every spin^c structure carrying a
  triangle.

The winding estimate `AddMonoidHom.exists_forall_exists_le_add_mul_abs_and_sub_mul_abs_le`
supplies the hypothesis on the regions created by winding, with `D` growing linearly in the winding
amount. The construction of the wound triple, and the identification of its doubly periodic domains
and Maslov indices with those of the original triple, are not part of this file.

## References

* P. Ozsváth and Z. Szabó, *Holomorphic disks and topological invariants for closed
  three-manifolds*, Ann. of Math. **159** (2004),
  [arXiv:math/0101206](https://arxiv.org/abs/math/0101206), §5, Lemmas 5.2 and 5.4 (admissibility
  by winding), and §8, Definition 8.8 and Lemmas 8.9–8.11 (admissibility of triples and finiteness
  of the triangle classes).
-/

public section

open Finset

namespace TauCeti

namespace HeegaardTripleRegionSystem

variable {n : ℕ} {PointAB PointBC PointAC Region Basepoint κ : Type*}
  {T : HeegaardTripleRegionSystem n PointAB PointBC PointAC Region Basepoint} [Fintype κ]
  {ν : (Region → ℤ) →+ (κ → ℤ)}

/-- **Weak admissibility of a triple from a detected norm.** If `ν` is injective on the sums of
doubly periodic domains and, for some `D > 0`, every such sum `P` has a region of multiplicity at
least `D * ‖ν P‖`, the triple is weakly admissible. -/
theorem weaklyAdmissible_of_forall_exists_mul_norm_le
    (hν : ∀ P ∈ T.doublyPeriodicDomains, ν P = 0 → P = 0) {D : ℝ} (hD₀ : 0 < D)
    (hD : ∀ P ∈ T.doublyPeriodicDomains, ∃ r, D * ‖ν P‖ ≤ P r) : T.WeaklyAdmissible :=
  weaklyAdmissible_iff.mpr (forall_nonneg_eq_zero_of_forall_exists_mul_norm_le hν hD₀ hD)

variable [Fintype PointAB] [Fintype PointBC] [Fintype PointAC] [Fintype Region]

open Classical in
/-- The change of the Maslov index at a triangle domain with corners `c`, as an additive functional
on the sums of doubly periodic domains; it is the same at all such triangle domains, and `0` when
there are none. -/
private noncomputable def cornerMaslovIndex (χ : Region → ℤ)
    (c : T.alphaBeta.Generator × T.betaGamma.Generator × T.alphaGamma.Generator) :
    T.doublyPeriodicDomains →+ ℚ :=
  if h : ∃ E, T.IsTriangleDomain c.1 c.2.1 c.2.2 E then
    AddMonoidHom.mk' (fun P ↦ T.periodicMaslovIndex χ c.1 c.2.2 h.choose P) fun P Q ↦
      h.choose_spec.periodicMaslovIndex_add χ P.property Q.property
  else 0

/-- At a triangle domain `E` with corners `x`, `y`, `w`, the functional `cornerMaslovIndex` is the
change of the Maslov index of `E`. -/
private theorem cornerMaslovIndex_apply {χ : Region → ℤ} {x : T.alphaBeta.Generator}
    {y : T.betaGamma.Generator} {w : T.alphaGamma.Generator} {E : Region → ℤ}
    (hE : T.IsTriangleDomain x y w E) (P : T.doublyPeriodicDomains) :
    cornerMaslovIndex χ (x, y, w) P = T.periodicMaslovIndex χ x w E P := by
  have h : ∃ E, T.IsTriangleDomain x y w E := ⟨E, hE⟩
  simp only [cornerMaslovIndex, h, ↓reduceDIte, AddMonoidHom.mk'_apply]
  exact hE.periodicMaslovIndex_eq_of_isTriangleDomain χ (Exists.choose_spec _) P.property

/-- **The Maslov index of a triple is bounded by the norm.** If `ν` is injective on the sums of
doubly periodic domains, there is a constant `C ≥ 0` such that `|μ(E + P) - μ(E)| ≤ C * ‖ν P‖` for
every such sum `P` and every triangle domain `E`, with any corners. -/
theorem exists_abs_periodicMaslovIndex_le_mul_norm
    (hν : ∀ P ∈ T.doublyPeriodicDomains, ν P = 0 → P = 0) (χ : Region → ℤ) :
    ∃ C, 0 ≤ C ∧ ∀ x y w E, T.IsTriangleDomain x y w E → ∀ P ∈ T.doublyPeriodicDomains,
      |(T.periodicMaslovIndex χ x w E P : ℝ)| ≤ C * ‖ν P‖ := by
  -- For fixed corners, the change of the Maslov index is one additive functional of `P`, and
  -- there are finitely many corners.
  obtain ⟨C, hC₀, hC⟩ := AddMonoidHom.exists_forall_abs_le_mul_norm_of_injective
    (fun c ↦ (Rat.castHom ℝ).toAddMonoidHom.comp (cornerMaslovIndex (T := T) χ c))
    (n := ν.comp T.doublyPeriodicDomains.subtype)
    ((injective_iff_map_eq_zero _).mpr fun P hP ↦ Subtype.ext (hν P P.property hP))
  refine ⟨C, hC₀, fun x y w E hE P hP ↦ ?_⟩
  simpa [cornerMaslovIndex_apply hE] using hC (x, y, w) ⟨P, hP⟩

/-- **Strong admissibility of a triple from a detected norm.** If `ν` is injective on the sums of
doubly periodic domains, the change `μ(E + P) - μ(E)` of the Maslov index of `E` is at most
`C * ‖ν P‖` for every such sum `P`, and every such `P` has a region of multiplicity at least
`D * ‖ν P‖` with `C < 2 * D`, the triple is strongly admissible at `E`. -/
theorem stronglyAdmissible_of_forall_exists_mul_norm_le
    (hν : ∀ P ∈ T.doublyPeriodicDomains, ν P = 0 → P = 0) {χ : Region → ℤ}
    {x : T.alphaBeta.Generator} {w : T.alphaGamma.Generator} {E : Region → ℤ} {C D : ℝ}
    (hC : ∀ P ∈ T.doublyPeriodicDomains, (T.periodicMaslovIndex χ x w E P : ℝ) ≤ C * ‖ν P‖)
    (hD : ∀ P ∈ T.doublyPeriodicDomains, ∃ r, D * ‖ν P‖ ≤ P r) (hCD : C < 2 * D) :
    T.StronglyAdmissible χ x w E :=
  stronglyAdmissible_iff.mpr fun P hP hne _ ↦
    forall_ne_zero_exists_half_lt_of_forall_exists_mul_norm_le hν hC hD hCD P hP hne

/-- **Strong admissibility of a triple at every triangle domain from a detected norm.** If `ν` is
injective on the sums of doubly periodic domains, there is a constant `C ≥ 0` such that, whenever
every such sum `P` has a region of multiplicity at least `D * ‖ν P‖` for some `D > C`, the triple is
strongly admissible at every triangle domain. -/
theorem exists_forall_stronglyAdmissible_of_forall_exists_mul_norm_le
    (hν : ∀ P ∈ T.doublyPeriodicDomains, ν P = 0 → P = 0) (χ : Region → ℤ) :
    ∃ C, 0 ≤ C ∧ ∀ D, C < D → (∀ P ∈ T.doublyPeriodicDomains, ∃ r, D * ‖ν P‖ ≤ P r) →
      ∀ x y w E, T.IsTriangleDomain x y w E → T.StronglyAdmissible χ x w E := by
  obtain ⟨C, hC₀, hC⟩ :=
    exists_forall_ne_zero_exists_half_lt_of_forall_exists_mul_norm_le hν (cornerMaslovIndex χ)
  refine ⟨C, hC₀, fun D hCD hD x y w E hE ↦ stronglyAdmissible_iff.mpr fun P hP hne _ ↦ ?_⟩
  simpa [cornerMaslovIndex_apply hE] using hC D hCD hD (x, y, w) ⟨P, hP⟩ hne

end HeegaardTripleRegionSystem

end TauCeti
