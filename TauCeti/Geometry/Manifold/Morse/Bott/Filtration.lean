/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Morse.Bott.Complex
public import TauCeti.Algebra.Homology.SpectralSequence.Filtered.Convergence
public import Mathlib.Algebra.Homology.CochainComplexOpposite
public import Mathlib.Algebra.Homology.Embedding.RestrictionHomology
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.Algebra.Category.ModuleCat.Biproducts
public import Mathlib.Algebra.Category.ModuleCat.Ulift
public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
public import Mathlib.Basic.Real.Basic
public import Mathlib.Order.Interval.Set.OrdConnected
import TauCeti.Algebra.Homology.Embedding.Restriction.Sequence
import TauCeti.Algebra.Homology.ModuleCat.Basic

/-!
# The critical-value filtration of the Bott complex

A Morse–Bott function `f` gives Bott chain data (`TauCeti.BottChainData`): the critical
components `C`, with chains `M C` graded by `S C`, and the pushforwards `P_CD` along the Bott
trajectories from `C` to `D`, out of which the Bott complex is built
(`TauCeti.BottChainData.chainComplex`). Every nonconstant trajectory strictly lowers `f`, so for
the values `v C = f(C)` a nonzero pushforward strictly lowers the value:
`v C ≤ v D → P_CD = 0` (the hypothesis `hv` below, which also excludes self-pushforwards). The
Bott complex is therefore filtered by critical values. This file constructs this filtration and
studies its spectral sequence, for any such data.

* **The Bott complex of a set of components.** For a set `p` of components through which no
  broken trajectory between two components of `p` escapes, keeping the boundaries of the
  components of `p` and the pushforwards between them gives Bott data
  (`TauCeti.BottChainData.restrict`), whose Bott complex on the chains of the components of `p`
  (graded by `TauCeti.BottChainData.restrictGrading`) is `TauCeti.BottChainData.chainComplexOn`.
  If no pushforward leaves a part `p` of `q` within `q`, the complex of `p` is a subcomplex of
  that of `q` (`TauCeti.BottChainData.chainComplexOnInclusion`); if none enters it, projecting to
  `p` is a chain map (`TauCeti.BottChainData.chainComplexOnRestriction`). For a lower part and
  its complement these form a short exact sequence
  (`TauCeti.BottChainData.chainComplexOnShortComplex_shortExact`).
* **Values in a set.** For an order-connected set `s` of values, no broken trajectory between two
  components with value in `s` escapes `s`, which gives the Bott complex
  `TauCeti.BottChainData.complexOn` of the components with value in `s`. For `a ≤ b` the
  sublevel `Iic a`, the sublevel `Iic b` and the band `Ioc a b` give the short exact sequence
  `0 → C(Iic a) → C(Iic b) → C(Ioc a b) → 0` (`TauCeti.BottChainData.bandSequence_shortExact`),
  and two adjacent bands give the short exact sequence
  `0 → C(Ioc a b) → C(Ioc a c) → C(Ioc b c) → 0`
  (`TauCeti.BottChainData.adjacentBandSequence_shortExact`). The connecting map of the sequence of
  a lower part `p` and its complement `r` sends the class of a cycle `x` of `r` to the class of the
  part on `p` of its Bott differential, the correspondences `F_CD (x C)` from `r` to `p`
  (`TauCeti.BottChainData.chainComplexOnShortComplex_δ_homologyπ`).
* **The critical-value spectral sequence.** For a monotone sequence `a : ℤ → ℝ` of cut values,
  the complexes of the sublevels `Iic (a q)` form an increasing filtration of the Bott complex
  (`TauCeti.BottChainData.filtration`), regraded as a cochain complex along `n ↦ -n`. On the
  first page of its spectral sequence (`TauCeti.BottChainData.spectralSequence`; numbered `2` in
  the indexing of `CochainComplex.spectralSequence`), the object at `(p, q)` with `p + q = -n` is
  the homology in total degree `n` of the band `Ioc (a q) (a (q + 1))`
  (`TauCeti.BottChainData.spectralSequenceFirstPageXIso`). If some `a q` lies below and some
  `a q'` above all critical values, the filtration is finite and the spectral sequence converges
  strongly to the homology of the Bott complex: on late enough pages the object at `(p, q)` is
  the graded piece of the induced filtration of the homology in total degree `-(p + q)`
  (`TauCeti.BottChainData.spectralSequencePageXIsoGraded`, with abutment
  `TauCeti.BottChainData.filtrationAbutmentIso`). The extension data of this filtration of the
  homology are kept: no splitting is asserted.
* **Bands with a single value.** There are no trajectories between components of the same value
  (`TauCeti.BottChainData.restrict_differential_apply_of_value_eq`), so the Bott complex of such
  a band is the direct sum of the Bott complexes `TauCeti.BottChainData.componentComplex` of its
  components (`TauCeti.BottChainData.isBilimitComplexOnBicone`). The Bott complex of a single
  component `C` has in total degree `n` the chains of degree `n - λ_C` on `C`
  (`TauCeti.BottChainData.mem_totalDegree_restrictGrading_eq_iff`), with differential
  `(-1)^λ_C ∂`, so its homology in total degree `n` is the homology `H_(n - λ_C)(C)` of the
  chain complex `TauCeti.BottChainData.componentChains` of the chains on `C` with the boundary `∂`
  (`TauCeti.BottChainData.componentComplexHomologyIso`, up to a universe lift). If each band
  contains a single critical value, the first page is therefore
  `E_(p,q) = ⊕_(C in the band) H_(n - λ_C)(C)`, the homology of the chains on the components
  shifted by their negative-normal ranks
  (`TauCeti.BottChainData.spectralSequenceFirstPageXIsoBiproduct`).

The same construction for the Morse complex, whose components are the critical points, is
`TauCeti.MorseBoundaryCoeffs.spectralSequence`. Identifying the abutment with the singular
homology of the manifold, and comparing this spectral sequence with that of the filtration of the
manifold by sublevel sets, are not attempted here.

## Main declarations

* `TauCeti.BottChainData.restrict`, `TauCeti.BottChainData.chainComplexOn`: the Bott data and
  the Bott complex of a set of components.
* `TauCeti.BottChainData.chainComplexOnInclusion`, `TauCeti.BottChainData.chainComplexOnι`,
  `TauCeti.BottChainData.chainComplexOnRestriction`: inclusions of lower parts and restrictions
  to upper parts.
* `TauCeti.BottChainData.chainComplexOnShortComplex_shortExact`,
  `TauCeti.BottChainData.bandSequence_shortExact`,
  `TauCeti.BottChainData.adjacentBandSequence_shortExact`: the short exact sequences of a lower
  part and its complement, of two sublevels and the band between them, and of two adjacent bands.
* `TauCeti.BottChainData.chainComplexOnShortComplex_δ_homologyπ`: the connecting map of a lower
  part and its complement sends the class of a cycle of the complement to the class of its
  correspondences to the lower part.
* `TauCeti.BottChainData.filtration`, `TauCeti.BottChainData.spectralSequence`: the
  critical-value filtration of the Bott complex and its spectral sequence.
* `TauCeti.BottChainData.spectralSequenceFirstPageXIso`,
  `TauCeti.BottChainData.spectralSequenceFirstPageXIsoBiproduct`: its first page.
* `TauCeti.BottChainData.filtrationAbutmentIso`,
  `TauCeti.BottChainData.spectralSequencePageXIsoGraded`: its convergence to the homology of the
  Bott complex.
* `TauCeti.BottChainData.componentChains`,
  `TauCeti.BottChainData.componentComplexHomologyIso`: the chain complex of a single component
  and the homology of the Bott complex of that component.

## References

* M. Hutchings, *Lecture notes on Morse homology (with an eye towards Floer theory and
  pseudoholomorphic curves)*, 2002, §6.4 (the filtrations of the Morse–Bott complex and their
  spectral sequences).
* J. McCleary, *A User's Guide to Spectral Sequences*, 2nd ed., Cambridge University Press, 2001,
  Section 2.2 (the spectral sequence of a filtered complex).
-/

public section

open CategoryTheory Limits HomologicalComplex

namespace TauCeti

namespace BottChainData

variable {R : Type*} [Ring R] {ι : Type*} {M : ι → Type*} [∀ C, AddCommGroup (M C)]
  [∀ C, Module R (M C)]

/-! ### Chains on a set of components -/

section Grading

variable (p : ι → Prop) [DecidablePred p]

/-- **The grading of chains on the components in `p`**: the chains of degree `j` on a component
of `p`, and only the zero chain on a component outside `p`. -/
def restrictGrading (S : ∀ C, ℤ → Submodule R (M C)) (C : ι) (j : ℤ) : Submodule R (M C) :=
  if p C then S C j else ⊥

variable {p} (S : ∀ C, ℤ → Submodule R (M C))

@[simp]
theorem restrictGrading_of_pos {C : ι} (hC : p C) (j : ℤ) : restrictGrading p S C j = S C j := by
  simp [restrictGrading, hC]

@[simp]
theorem restrictGrading_of_neg {C : ι} (hC : ¬p C) (j : ℤ) : restrictGrading p S C j = ⊥ := by
  simp [restrictGrading, hC]

theorem restrictGrading_le (C : ι) (j : ℤ) : restrictGrading p S C j ≤ S C j := by
  by_cases hC : p C <;> simp [hC]

theorem restrictGrading_mono {q : ι → Prop} [DecidablePred q] (hpq : ∀ C, p C → q C) (C : ι)
    (j : ℤ) : restrictGrading p S C j ≤ restrictGrading q S C j := by
  by_cases hC : p C
  · simp [hC, hpq C hC]
  · simp [hC]

/-- A chain graded by `restrictGrading p S` vanishes on the components outside `p`. -/
theorem eq_zero_of_mem_restrictGrading {C : ι} {j : ℤ} {x : M C}
    (hx : x ∈ restrictGrading p S C j) (hC : ¬p C) : x = 0 := by
  simpa [hC] using hx

variable (R) (p) in
/-- **The projection onto the chains of the components in `p`**, which keeps the chains on the
components of `p` and discards the others. -/
def restrictProj : (∀ C, M C) →ₗ[R] ∀ C, M C :=
  LinearMap.pi fun C ↦ if p C then LinearMap.proj C else 0

@[simp]
theorem restrictProj_apply (x : ∀ C, M C) (C : ι) :
    restrictProj R p x C = if p C then x C else 0 := by
  by_cases hC : p C <;> simp [restrictProj, hC]

/-- The projection onto the chains of `p` sends chains graded by `restrictGrading q S` to chains
graded by `restrictGrading p S`. -/
theorem restrictProj_apply_mem_restrictGrading {q : ι → Prop} [DecidablePred q] {x : ∀ C, M C}
    {C : ι} {j : ℤ} (hx : x C ∈ restrictGrading q S C j) (hpq : ∀ C, p C → q C) :
    restrictProj R p x C ∈ restrictGrading p S C j := by
  by_cases hC : p C
  · simpa [hC, hpq C hC] using hx
  · simp [hC]

end Grading

variable [Fintype ι] (B : BottChainData R ι M)


section Restrict

variable (p : ι → Prop) [DecidablePred p]

/-- **The Bott data of a set of components.** The components in `p` keep their chains, their
boundaries and the pushforwards between them; every pushforward into or out of a component outside
`p` is replaced by zero. The face relation survives when no broken trajectory between two
components of `p` passes through a component outside `p`, which is the hypothesis `hp`. Chains on
the components outside `p` are discarded by the grading `TauCeti.BottChainData.restrictGrading`. -/
def restrict (hp : ∀ C E D, p C → p D → ¬p E → B.pushforward E D ∘ₗ B.pushforward C E = 0) :
    BottChainData R ι M where
  rank := B.rank
  dim := B.dim
  boundary := B.boundary
  boundary_comp_boundary := B.boundary_comp_boundary
  pushforward C D := if p C ∧ p D then B.pushforward C D else 0
  boundary_comp_pushforward C D := by
    by_cases hC : p C
    · by_cases hD : p D
      · simp only [hC, hD, and_self, ite_true, B.boundary_comp_pushforward]
        congr 1
        refine Finset.sum_congr rfl fun E _ ↦ ?_
        by_cases hE : p E
        · simp [hE]
        · simp [hE, hp C E D hC hD hE]
      · simp [hD]
    · simp [hC]

variable (hp : ∀ C E D, p C → p D → ¬p E → B.pushforward E D ∘ₗ B.pushforward C E = 0)

@[simp]
theorem restrict_rank : (B.restrict p hp).rank = B.rank :=
  (rfl)

@[simp]
theorem restrict_dim : (B.restrict p hp).dim = B.dim :=
  (rfl)

@[simp]
theorem restrict_boundary : (B.restrict p hp).boundary = B.boundary :=
  (rfl)

@[simp]
theorem restrict_pushforward (C D : ι) :
    (B.restrict p hp).pushforward C D = if p C ∧ p D then B.pushforward C D else 0 :=
  (rfl)

/-- The signed correspondences of the Bott data of `p` are those of `B` between components of `p`,
and zero otherwise. -/
theorem restrict_correspondence (C D : ι) :
    (B.restrict p hp).correspondence C D = if p C ∧ p D then B.correspondence C D else 0 := by
  ext x
  split_ifs with h <;> simp [correspondence_apply, h]

@[simp]
theorem restrict_totalDegree : (B.restrict p hp).totalDegree = B.totalDegree := by
  ext S k x
  simp [mem_totalDegree_iff]

/-- The Bott differential of the components in `p`: the internal boundary of every component and
the correspondences between components of `p`. -/
theorem restrict_differential_apply (x : ∀ C, M C) (D : ι) :
    (B.restrict p hp).differential x D =
      (B.rank D : ℤ).negOnePow • B.boundary D (x D) +
        ∑ C, if p C ∧ p D then B.correspondence C D (x C) else 0 := by
  simp only [differential_apply, restrict_rank, restrict_boundary, restrict_correspondence]
  congr 1
  refine Finset.sum_congr rfl fun C _ ↦ ?_
  split_ifs <;> simp

/-- **The Bott differential on a lower part.** Let `p` be a part of `q` which no pushforward from a
component of `p` leaves within `q`. On chains supported on `p`, the Bott differentials of `p` and
of `q` agree. -/
theorem restrict_differential_eq_of_lower {q : ι → Prop} [DecidablePred q]
    (hq : ∀ C E D, q C → q D → ¬q E → B.pushforward E D ∘ₗ B.pushforward C E = 0)
    (hpq : ∀ C, p C → q C) (hlow : ∀ C D, p C → q D → ¬p D → B.pushforward C D = 0)
    {x : ∀ C, M C} (hx : ∀ C, ¬p C → x C = 0) :
    (B.restrict q hq).differential x = (B.restrict p hp).differential x := by
  funext D
  rw [restrict_differential_apply, restrict_differential_apply]
  congr 1
  refine Finset.sum_congr rfl fun C _ ↦ ?_
  by_cases hC : p C
  · by_cases hD : p D
    · simp [hC, hD, hpq C hC, hpq D hD]
    · by_cases hqD : q D
      · simp [hD, hqD, hpq C hC, correspondence_apply, hlow C D hC hqD hD]
      · simp [hD, hqD]
  · simp [hx C hC]

/-- **The Bott differential on a lower set.** If no pushforward leaves `p`, then on chains
supported on `p` the Bott differential of `p` is that of all components. -/
theorem differential_eq_restrict_differential_of_lower
    (hlow : ∀ C D, p C → ¬p D → B.pushforward C D = 0) {x : ∀ C, M C}
    (hx : ∀ C, ¬p C → x C = 0) :
    B.differential x = (B.restrict p hp).differential x := by
  funext D
  rw [differential_apply, restrict_differential_apply]
  congr 1
  refine Finset.sum_congr rfl fun C _ ↦ ?_
  by_cases hC : p C
  · by_cases hD : p D
    · simp [hC, hD]
    · simp [hD, correspondence_apply, hlow C D hC hD]
  · simp [hx C hC]

/-- **The Bott differential on an upper part.** Let `p` be a part of `q` which no pushforward from
a component of `q` enters from outside `p`. On chains supported on `q`, projecting onto the chains
of `p` intertwines the Bott differentials of `q` and of `p`. -/
theorem restrict_differential_restrictProj_of_upper {q : ι → Prop} [DecidablePred q]
    (hq : ∀ C E D, q C → q D → ¬q E → B.pushforward E D ∘ₗ B.pushforward C E = 0)
    (hpq : ∀ C, p C → q C) (hup : ∀ C D, q C → p D → ¬p C → B.pushforward C D = 0)
    {x : ∀ C, M C} (hx : ∀ C, ¬q C → x C = 0) :
    (B.restrict p hp).differential (restrictProj R p x) =
      restrictProj R p ((B.restrict q hq).differential x) := by
  funext D
  by_cases hD : p D
  · rw [restrictProj_apply, restrict_differential_apply, restrict_differential_apply,
      restrictProj_apply]
    simp only [hD, ite_true]
    congr 1
    refine Finset.sum_congr rfl fun C _ ↦ ?_
    by_cases hC : p C
    · simp [hC, hpq C hC, hpq D hD]
    · by_cases hqC : q C
      · simp [hC, hqC, hpq D hD, correspondence_apply, hup C D hqC hD hC]
      · simp [hC, hx C hqC]
  · rw [restrictProj_apply, restrict_differential_apply]
    simp [hD]

variable {S : ∀ C, ℤ → Submodule R (M C)}
  (hboundary : ∀ C j, ∀ x ∈ S C j, B.boundary C x ∈ S C (j - 1))
  (hpushforward : ∀ C D j, ∀ x ∈ S C j,
    B.pushforward C D x ∈ S D (j + bottDegreeShift B.rank C D))

include hboundary in
/-- The boundary of the Bott data of `p` lowers the degree of chains on the components of `p` by
one. -/
theorem restrict_boundary_mem_restrictGrading (C : ι) (j : ℤ) (x : M C)
    (hx : x ∈ restrictGrading p S C j) :
    (B.restrict p hp).boundary C x ∈ restrictGrading p S C (j - 1) := by
  by_cases hC : p C
  · rw [restrictGrading_of_pos S hC] at hx ⊢
    exact hboundary C j x hx
  · simp [eq_zero_of_mem_restrictGrading S hx hC]

include hpushforward in
/-- The pushforwards of the Bott data of `p` shift the degree of chains on the components of `p` by
`d_CD`. -/
theorem restrict_pushforward_mem_restrictGrading (C D : ι) (j : ℤ) (x : M C)
    (hx : x ∈ restrictGrading p S C j) :
    (B.restrict p hp).pushforward C D x ∈
      restrictGrading p S D (j + bottDegreeShift (B.restrict p hp).rank C D) := by
  rw [restrict_pushforward]
  split_ifs with h
  · rw [restrictGrading_of_pos S h.2]
    rw [restrictGrading_of_pos S h.1] at hx
    exact hpushforward C D j x hx
  · simp

/-- **The Bott complex of the components in `p`**: the Bott complex of the Bott data of `p`, on
the chains of the components of `p`. -/
-- The body is exposed so that the terms of the complex compute to the total-degree pieces, which
-- the chain maps below are built on.
@[expose]
noncomputable def chainComplexOn : ChainComplex (ModuleCat R) ℤ :=
  (B.restrict p hp).chainComplex (S := restrictGrading p S)
    (B.restrict_boundary_mem_restrictGrading p hp hboundary)
    (B.restrict_pushforward_mem_restrictGrading p hp hpushforward)

/-- The term of the Bott complex of `p` in total degree `k` consists of the chains on the
components of `p` of total degree `k`. -/
theorem chainComplexOn_X (k : ℤ) :
    (B.chainComplexOn p hp hboundary hpushforward).X k =
      ModuleCat.of R ((B.restrict p hp).totalDegree (restrictGrading p S) k) :=
  (rfl)

/-- A chain of total degree `k` on the components of `p` vanishes on the components outside
`p`. -/
theorem apply_eq_zero_of_mem_restrict_totalDegree {k : ℤ} {x : ∀ C, M C}
    (hx : x ∈ (B.restrict p hp).totalDegree (restrictGrading p S) k) {C : ι} (hC : ¬p C) :
    x C = 0 :=
  eq_zero_of_mem_restrictGrading S ((mem_totalDegree_iff _ _).1 hx C) hC

/-- The differential of the Bott complex of `p` is the Bott differential of `p`. -/
@[simp]
theorem chainComplexOn_d_apply (k : ℤ)
    (x : (B.restrict p hp).totalDegree (restrictGrading p S) (k + 1)) :
    (((B.chainComplexOn p hp hboundary hpushforward).d (k + 1) k).hom x :
        (B.restrict p hp).totalDegree (restrictGrading p S) k).val =
      (B.restrict p hp).differential x.val :=
  chainComplex_d_apply _ _ _ k x

/-- The chains of total degree `k` on the components of `p` are chains of total degree `k` on the
components of `q ⊇ p`. -/
theorem restrict_totalDegree_le {q : ι → Prop} [DecidablePred q]
    (hq : ∀ C E D, q C → q D → ¬q E → B.pushforward E D ∘ₗ B.pushforward C E = 0)
    (hpq : ∀ C, p C → q C) (k : ℤ) :
    (B.restrict p hp).totalDegree (restrictGrading p S) k ≤
      (B.restrict q hq).totalDegree (restrictGrading q S) k := fun x hx ↦ by
  rw [mem_totalDegree_iff] at hx ⊢
  exact fun C ↦ restrictGrading_mono S hpq C _ (hx C)

/-- The chains of total degree `k` on the single component `C` are the chains of degree `k - λ_C`
on `C`. -/
theorem mem_totalDegree_restrictGrading_eq_iff [DecidableEq ι] (C : ι) {k : ℤ}
    {x : ∀ D, M D} :
    x ∈ B.totalDegree (restrictGrading (· = C) S) k ↔
      x C ∈ S C (k - B.rank C) ∧ ∀ D, D ≠ C → x D = 0 := by
  rw [mem_totalDegree_iff]
  refine ⟨fun h ↦ ⟨by simpa using h C, fun D hD ↦ by simpa [hD] using h D⟩, fun h D ↦ ?_⟩
  by_cases hD : D = C
  · subst hD
    simpa using h.1
  · simp [hD, h.2 D hD]

/-- The chains of total degree `k` on the components of `p` are chains of total degree `k` of the
Bott complex. -/
theorem restrict_totalDegree_le_totalDegree (k : ℤ) :
    (B.restrict p hp).totalDegree (restrictGrading p S) k ≤ B.totalDegree S k := fun x hx ↦ by
  rw [mem_totalDegree_iff] at hx ⊢
  exact fun C ↦ restrictGrading_le S C _ (hx C)

variable {q : ι → Prop} [DecidablePred q]
  (hq : ∀ C E D, q C → q D → ¬q E → B.pushforward E D ∘ₗ B.pushforward C E = 0)

/-- **The inclusion of a lower part.** If `p` is a part of `q` which no pushforward from a
component of `p` leaves within `q`, the Bott complex of `p` is a subcomplex of that of `q`. -/
noncomputable def chainComplexOnInclusion (hpq : ∀ C, p C → q C)
    (hlow : ∀ C D, p C → q D → ¬p D → B.pushforward C D = 0) :
    B.chainComplexOn p hp hboundary hpushforward ⟶ B.chainComplexOn q hq hboundary hpushforward
    where
  f k := ModuleCat.ofHom (Submodule.inclusion (B.restrict_totalDegree_le p hp hq hpq k))
  comm' := by
    rintro _ k rfl
    ext x : 2
    refine Subtype.ext ?_
    -- The terms `(B.chainComplexOn _ _ _ _).X k` are the total-degree pieces only after unfolding
    -- `chainComplexOn`, so the goal is not type-correct at reducible transparency and the
    -- `ModuleCat` composition lemmas do not rewrite it; `change` states it on the chains instead.
    change ((((B.chainComplexOn q hq hboundary hpushforward).d (k + 1) k).hom
        (Submodule.inclusion (B.restrict_totalDegree_le p hp hq hpq (k + 1)) x)) :
          (B.restrict q hq).totalDegree (restrictGrading q S) k).val =
      (((B.chainComplexOn p hp hboundary hpushforward).d (k + 1) k).hom x :
          (B.restrict p hp).totalDegree (restrictGrading p S) k).val
    rw [chainComplexOn_d_apply]
    -- the inclusion of submodules does not change the underlying chain
    refine (B.restrict_differential_eq_of_lower p hp hq hpq hlow (x := x.val) fun C hC ↦ ?_).trans
      (chainComplexOn_d_apply B p hp hboundary hpushforward k x).symm
    exact B.apply_eq_zero_of_mem_restrict_totalDegree _ _ x.property hC

/-- The inclusion of a lower part sends a chain to the same chain. -/
@[simp]
theorem chainComplexOnInclusion_f_apply (hpq : ∀ C, p C → q C)
    (hlow : ∀ C D, p C → q D → ¬p D → B.pushforward C D = 0) (k : ℤ)
    (x : (B.restrict p hp).totalDegree (restrictGrading p S) k) :
    ((B.chainComplexOnInclusion p hp hboundary hpushforward hq hpq hlow).f k).hom x =
      Submodule.inclusion (B.restrict_totalDegree_le p hp hq hpq k) x :=
  (rfl)

instance mono_chainComplexOnInclusion (hpq : ∀ C, p C → q C)
    (hlow : ∀ C D, p C → q D → ¬p D → B.pushforward C D = 0) :
    Mono (B.chainComplexOnInclusion p hp hboundary hpushforward hq hpq hlow) :=
  mono_of_mono_f _ fun k ↦ (ModuleCat.mono_iff_injective _).2
    (Submodule.inclusion_injective (B.restrict_totalDegree_le p hp hq hpq k))

/-- **The restriction to an upper part.** If `p` is a part of `q` which no pushforward from a
component of `q` enters from outside `p`, projecting onto the chains of `p` is a chain map from the
Bott complex of `q` to that of `p`. -/
noncomputable def chainComplexOnRestriction (hpq : ∀ C, p C → q C)
    (hup : ∀ C D, q C → p D → ¬p C → B.pushforward C D = 0) :
    B.chainComplexOn q hq hboundary hpushforward ⟶ B.chainComplexOn p hp hboundary hpushforward
    where
  f k := ModuleCat.ofHom ((restrictProj R p).restrict fun x hx ↦ by
    rw [mem_totalDegree_iff] at hx ⊢
    exact fun C ↦ restrictProj_apply_mem_restrictGrading S (hx C) hpq)
  comm' := by
    rintro _ k rfl
    ext x : 2
    refine Subtype.ext ?_
    -- As for `chainComplexOnInclusion`, `change` states the goal on the chains.
    change ((((B.chainComplexOn p hp hboundary hpushforward).d (k + 1) k).hom
        ⟨restrictProj R p x.val, _⟩) :
          (B.restrict p hp).totalDegree (restrictGrading p S) k).val =
      restrictProj R p (((B.chainComplexOn q hq hboundary hpushforward).d (k + 1) k).hom x :
          (B.restrict q hq).totalDegree (restrictGrading q S) k).val
    rw [chainComplexOn_d_apply]
    refine (B.restrict_differential_restrictProj_of_upper p hp hq hpq hup (x := x.val)
      fun C hC ↦ ?_).trans
        (congrArg _ (chainComplexOn_d_apply B q hq hboundary hpushforward k x).symm)
    exact B.apply_eq_zero_of_mem_restrict_totalDegree _ _ x.property hC

/-- The restriction to an upper part projects a chain onto the chains of `p`. -/
@[simp]
theorem chainComplexOnRestriction_f_apply_coe (hpq : ∀ C, p C → q C)
    (hup : ∀ C D, q C → p D → ¬p C → B.pushforward C D = 0) (k : ℤ)
    (x : (B.restrict q hq).totalDegree (restrictGrading q S) k) :
    (((B.chainComplexOnRestriction p hp hboundary hpushforward hq hpq hup).f k).hom x :
        (B.restrict p hp).totalDegree (restrictGrading p S) k).val =
      restrictProj R p x.val :=
  (rfl)

/-- A chain on the components of `p ⊆ q` is the projection of itself, seen as a chain on the
components of `q`. -/
theorem restrictProj_eq_self {k : ℤ} {x : ∀ C, M C}
    (hx : x ∈ (B.restrict p hp).totalDegree (restrictGrading p S) k) : restrictProj R p x = x := by
  funext C
  by_cases hC : p C
  · simp [hC]
  · simp [hC, B.apply_eq_zero_of_mem_restrict_totalDegree _ _ hx hC]

instance epi_chainComplexOnRestriction (hpq : ∀ C, p C → q C)
    (hup : ∀ C D, q C → p D → ¬p C → B.pushforward C D = 0) :
    Epi (B.chainComplexOnRestriction p hp hboundary hpushforward hq hpq hup) :=
  epi_of_epi_f _ fun k ↦ (ModuleCat.epi_iff_surjective _).2 fun x ↦
    ⟨Submodule.inclusion (B.restrict_totalDegree_le p hp hq hpq k) x, Subtype.ext <|
      (chainComplexOnRestriction_f_apply_coe ..).trans (B.restrictProj_eq_self p hp x.property)⟩

/-- **The inclusion of a lower set into the Bott complex.** If no pushforward leaves `p`, the Bott
complex of `p` is a subcomplex of the Bott complex. -/
noncomputable def chainComplexOnι (hlow : ∀ C D, p C → ¬p D → B.pushforward C D = 0) :
    B.chainComplexOn p hp hboundary hpushforward ⟶ B.chainComplex hboundary hpushforward where
  f k := ModuleCat.ofHom (Submodule.inclusion (B.restrict_totalDegree_le_totalDegree p hp k))
  comm' := by
    rintro _ k rfl
    ext x : 2
    refine Subtype.ext ?_
    -- As for `chainComplexOnInclusion`, `change` states the goal on the chains.
    change ((((B.chainComplex hboundary hpushforward).d (k + 1) k).hom
        (Submodule.inclusion (B.restrict_totalDegree_le_totalDegree p hp (k + 1)) x)) :
          B.totalDegree S k).val =
      (((B.chainComplexOn p hp hboundary hpushforward).d (k + 1) k).hom x :
          (B.restrict p hp).totalDegree (restrictGrading p S) k).val
    rw [chainComplex_d_apply]
    -- the inclusion of submodules does not change the underlying chain
    refine (B.differential_eq_restrict_differential_of_lower p hp hlow (x := x.val)
      fun C hC ↦ ?_).trans (chainComplexOn_d_apply B p hp hboundary hpushforward k x).symm
    exact B.apply_eq_zero_of_mem_restrict_totalDegree _ _ x.property hC

/-- The inclusion of a lower set into the Bott complex sends a chain to the same chain. -/
@[simp]
theorem chainComplexOnι_f_apply (hlow : ∀ C D, p C → ¬p D → B.pushforward C D = 0) (k : ℤ)
    (x : (B.restrict p hp).totalDegree (restrictGrading p S) k) :
    ((B.chainComplexOnι p hp hboundary hpushforward hlow).f k).hom x =
      Submodule.inclusion (B.restrict_totalDegree_le_totalDegree p hp k) x :=
  (rfl)

instance mono_chainComplexOnι (hlow : ∀ C D, p C → ¬p D → B.pushforward C D = 0) :
    Mono (B.chainComplexOnι p hp hboundary hpushforward hlow) :=
  mono_of_mono_f _ fun k ↦ (ModuleCat.mono_iff_injective _).2
    (Submodule.inclusion_injective (B.restrict_totalDegree_le_totalDegree p hp k))

/-- The inclusions of a lower part of a lower set and of the lower set into the Bott complex
compose to the inclusion of the lower part. -/
@[reassoc (attr := simp)]
theorem chainComplexOnInclusion_comp_chainComplexOnι (hpq : ∀ C, p C → q C)
    (hlow : ∀ C D, p C → q D → ¬p D → B.pushforward C D = 0)
    (hlowq : ∀ C D, q C → ¬q D → B.pushforward C D = 0)
    (hlowp : ∀ C D, p C → ¬p D → B.pushforward C D = 0) :
    B.chainComplexOnInclusion p hp hboundary hpushforward hq hpq hlow ≫
        B.chainComplexOnι q hq hboundary hpushforward hlowq =
      B.chainComplexOnι p hp hboundary hpushforward hlowp :=
  HomologicalComplex.hom_ext _ _ fun _ ↦ (rfl)

section ShortComplex

variable {r : ι → Prop} [DecidablePred r]
  (hr : ∀ C E D, r C → r D → ¬r E → B.pushforward E D ∘ₗ B.pushforward C E = 0)
  (hpq : ∀ C, p C → q C) (hrq : ∀ C, r C → q C) (hpr : ∀ C, q C → (r C ↔ ¬p C))
  (hlow : ∀ C D, p C → q D → ¬p D → B.pushforward C D = 0)

omit [DecidablePred p] [DecidablePred q] [DecidablePred r] in
include hrq hpr hlow in
/-- If `q` is the disjoint union of a lower part `p` and its complement `r`, no pushforward enters
`r` from `p`. -/
theorem pushforward_eq_zero_of_compl (C D : ι) (hC : q C) (hD : r D) (hC' : ¬r C) :
    B.pushforward C D = 0 :=
  hlow C D (not_not.1 fun h ↦ hC' ((hpr C hC).2 h)) (hrq D hD) ((hpr D (hrq D hD)).1 hD)

/-- **The sequence of a lower part and its complement.** If `q` is the disjoint union of a lower
part `p` and its complement `r`, the short complex `C(p) → C(q) → C(r)` of the inclusion of the
Bott complex of `p` into that of `q` and the restriction of the latter to `r`. -/
-- This is an abbreviation so that the terms of the sequence reduce to the Bott complexes of `p`,
-- `q` and `r`, which the band sequences are composed with, and its maps compute to the inclusion
-- and the restriction, which `chainComplexOnShortComplex_shortExact` unfolds.
noncomputable abbrev chainComplexOnShortComplex : ShortComplex (ChainComplex (ModuleCat R) ℤ) :=
  ShortComplex.mk (B.chainComplexOnInclusion p hp hboundary hpushforward hq hpq hlow)
    (B.chainComplexOnRestriction r hr hboundary hpushforward hq hrq
      (B.pushforward_eq_zero_of_compl p hrq hpr hlow)) <| by
    ext k x : 3
    refine Subtype.ext (funext fun C ↦ ?_)
    -- The terms of the complexes are the total-degree pieces only after unfolding
    -- `chainComplexOn`, so `change` states the goal on the chains.
    change restrictProj R r x.val C = 0
    by_cases hC : r C
    · simp only [restrictProj_apply, hC, ite_true]
      exact B.apply_eq_zero_of_mem_restrict_totalDegree _ _ x.property ((hpr C (hrq C hC)).1 hC)
    · simp [hC]

/-- The first map of the sequence of a lower part and its complement is the inclusion. -/
@[simp]
theorem chainComplexOnShortComplex_f :
    (B.chainComplexOnShortComplex p hp hboundary hpushforward hq hr hpq hrq hpr hlow).f =
      B.chainComplexOnInclusion p hp hboundary hpushforward hq hpq hlow :=
  (rfl)

/-- The second map of the sequence of a lower part and its complement is the restriction. -/
@[simp]
theorem chainComplexOnShortComplex_g :
    (B.chainComplexOnShortComplex p hp hboundary hpushforward hq hr hpq hrq hpr hlow).g =
      B.chainComplexOnRestriction r hr hboundary hpushforward hq hrq
        (B.pushforward_eq_zero_of_compl p hrq hpr hlow) :=
  (rfl)

/-- **The sequence of a lower part and its complement is short exact**: the chains on the
components of `q` whose projection to `r` vanishes are the chains on the components of `p`. -/
theorem chainComplexOnShortComplex_shortExact :
    (B.chainComplexOnShortComplex p hp hboundary hpushforward hq hr hpq hrq hpr hlow).ShortExact
    := by
  refine shortExact_of_degreewise_shortExact _ fun k ↦ ?_
  refine .mk' ((ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).2
    fun (x : (B.restrict q hq).totalDegree (restrictGrading q S) k) ↦ ⟨fun hx ↦ ?_, ?_⟩)
    ((ModuleCat.mono_iff_injective _).2
      (Submodule.inclusion_injective (B.restrict_totalDegree_le p hp hq hpq k)))
    (by
      -- Instance search does not see the second map of the sequence as the restriction without
      -- unfolding `chainComplexOnShortComplex`, so it is unfolded by `dsimp`.
      have : Epi (B.chainComplexOnShortComplex p hp hboundary hpushforward hq hr hpq hrq hpr
          hlow).g := by
        dsimp only [chainComplexOnShortComplex]
        infer_instance
      exact inferInstanceAs (Epi ((B.chainComplexOnShortComplex p hp hboundary hpushforward hq hr
        hpq hrq hpr hlow).g.f k)))
  · -- A chain on `q` with vanishing projection to `r` is a chain on `p`.
    have hx' : ∀ C, ¬p C → x.val C = 0 := fun C hC ↦ by
      by_cases hqC : q C
      · have h := congrFun (congrArg Subtype.val hx) C
        -- `hx` states that the projection of `x` to the chains of `r` vanishes.
        change restrictProj R r x.val C = 0 at h
        simpa only [restrictProj_apply, (hpr C hqC).2 hC, ite_true] using h
      · exact B.apply_eq_zero_of_mem_restrict_totalDegree _ _ x.property hqC
    refine ⟨⟨x.val, (mem_totalDegree_iff _ _).2 fun C ↦ ?_⟩, rfl⟩
    by_cases hC : p C
    · rw [restrictGrading_of_pos S hC]
      have := (mem_totalDegree_iff _ _).1 x.property C
      rwa [restrictGrading_of_pos S (hpq C hC)] at this
    · simp [restrictGrading_of_neg S hC, hx' C hC]
  · rintro ⟨y, rfl⟩
    exact ShortComplex.moduleCat_zero_apply _ y

include hpq hrq hpr in
/-- **The Bott differential of a cycle of the complement.** Let `q` be the disjoint union of a
lower part `p` and its complement `r`, and let `x` be a chain on the components of `r` whose Bott
differential in `r` vanishes. Then the Bott differential of `x` in `q` is the part on `p` of its
Bott differential: the correspondences from the components of `r` to those of `p`. -/
theorem restrict_differential_eq_restrictProj_differential {x : ∀ C, M C}
    (hx : ∀ C, ¬r C → x C = 0) (hdx : (B.restrict r hr).differential x = 0) :
    (B.restrict q hq).differential x = restrictProj R p (B.differential x) := by
  funext D
  rw [restrict_differential_apply, restrictProj_apply]
  by_cases hD : p D
  · -- On a component of `p` the chain vanishes, and only the correspondences out of `r` remain.
    have hxD : x D = 0 := hx D fun h ↦ (hpr D (hpq D hD)).1 h hD
    simp only [hD, ite_true]
    rw [differential_apply, hxD, map_zero, smul_zero, zero_add, zero_add]
    refine Finset.sum_congr rfl fun C _ ↦ ?_
    by_cases hC : r C
    · simp [hrq C hC, hpq D hD]
    · simp [hx C hC]
  · simp only [hD, ite_false]
    by_cases hqD : q D
    · -- On a component of `r` this is the Bott differential in `r`, which vanishes.
      have hrD : r D := (hpr D hqD).2 hD
      refine Eq.trans ?_ (congrFun hdx D)
      rw [restrict_differential_apply]
      congr 1
      refine Finset.sum_congr rfl fun C _ ↦ ?_
      by_cases hC : r C
      · simp [hC, hrD, hrq C hC, hqD]
      · simp [hx C hC]
    · simp [hx D fun h ↦ hqD (hrq D h), hqD]

omit [DecidablePred q] in
include hq hpq hrq hpr hlow in
/-- The part on the lower part `p` of the Bott differential of a cycle of the complement `r` is a
cycle of `p`. -/
theorem restrict_differential_restrictProj_differential_eq_zero {x : ∀ C, M C}
    (hx : ∀ C, ¬r C → x C = 0) (hdx : (B.restrict r hr).differential x = 0) :
    (B.restrict p hp).differential (restrictProj R p (B.differential x)) = 0 := by
  classical
  rw [← B.restrict_differential_eq_of_lower p hp hq hpq hlow fun C hC ↦ by simp [hC],
    ← B.restrict_differential_eq_restrictProj_differential p hq hr hpq hrq hpr hx hdx]
  exact (B.restrict q hq).differential_differential x

/-- **The connecting map of a lower part and its complement.** Let `q` be the disjoint union of a
lower part `p` and its complement `r`. The connecting map `H_(k+1)(C(r)) → H_k(C(p))` of the short
exact sequence `C(p) → C(q) → C(r)` sends the class of a cycle `x` of `r` to the class of the part
on `p` of its Bott differential, that is of the chain `∑_C F_CD (x C)` on the components `D` of
`p`, summed over the components `C` of `r`. The cycle `z'` of `p` is given with this chain as
underlying chain. -/
theorem chainComplexOnShortComplex_δ_homologyπ (k : ℤ)
    (z : (B.chainComplexOn r hr hboundary hpushforward).cycles (k + 1))
    (z' : (B.chainComplexOn p hp hboundary hpushforward).cycles k)
    (hz' : (((B.chainComplexOn p hp hboundary hpushforward).iCycles k).hom z' :
        (B.restrict p hp).totalDegree (restrictGrading p S) k).val =
      restrictProj R p (B.differential
        (((B.chainComplexOn r hr hboundary hpushforward).iCycles (k + 1)).hom z :
          (B.restrict r hr).totalDegree (restrictGrading r S) (k + 1)).val)) :
    ((B.chainComplexOnShortComplex_shortExact p hp hboundary hpushforward hq hr hpq hrq hpr
        hlow).δ (k + 1) k (by simp)).hom
        (((B.chainComplexOn r hr hboundary hpushforward).homologyπ (k + 1)).hom z) =
      ((B.chainComplexOn p hp hboundary hpushforward).homologyπ k).hom z' := by
  -- the underlying cycle of `z`, a chain on the components of `r`
  set x : (B.restrict r hr).totalDegree (restrictGrading r S) (k + 1) :=
    ((B.chainComplexOn r hr hboundary hpushforward).iCycles (k + 1)).hom z
  have hxr : ∀ C, ¬r C → x.val C = 0 := fun C hC ↦
    B.apply_eq_zero_of_mem_restrict_totalDegree _ _ x.property hC
  have hdx : (B.restrict r hr).differential x.val = 0 := by
    rw [← chainComplexOn_d_apply]
    exact congrArg Subtype.val (HomologicalComplex.moduleCat_d_iCycles_apply _ _ _ z)
  -- the lift of `x` to the chains of `q`
  refine (B.chainComplexOnShortComplex_shortExact p hp hboundary hpushforward hq hr hpq hrq hpr
    hlow).moduleCat_δ_homologyπ (k + 1) k (by simp) z
      (Submodule.inclusion (B.restrict_totalDegree_le r hr hq hrq (k + 1)) x)
      (Subtype.ext ?_) z' (Subtype.ext ?_)
  · -- `x` is its own projection to `r`
    exact B.restrictProj_eq_self r hr x.property
  · -- the differential of the lift is the part on `p` of the Bott differential of `x`
    refine hz'.trans ?_
    rw [← B.restrict_differential_eq_restrictProj_differential p hq hr hpq hrq hpr hxr hdx]
    exact (chainComplexOn_d_apply B q hq hboundary hpushforward k
      (Submodule.inclusion (B.restrict_totalDegree_le r hr hq hrq (k + 1)) x)).symm

end ShortComplex

end Restrict

/-! ### Chains with critical values in a set -/

section Value

open Set

variable (v : ι → ℝ) (hv : ∀ C D, v C ≤ v D → B.pushforward C D = 0)

include hv in
/-- **No broken trajectory leaves an order-connected set of values.** If every nonzero pushforward
strictly lowers the value `v`, a composite of nonzero pushforwards from a component with value in
the order-connected set `s` to another one passes through a component with value in `s`. -/
theorem pushforward_comp_pushforward_eq_zero_of_ordConnected (s : Set ℝ) [s.OrdConnected]
    (C E D : ι) (hC : v C ∈ s) (hD : v D ∈ s) (hE : v E ∉ s) :
    B.pushforward E D ∘ₗ B.pushforward C E = 0 := by
  by_cases h₁ : v C ≤ v E
  · rw [hv C E h₁, LinearMap.comp_zero]
  by_cases h₂ : v E ≤ v D
  · rw [hv E D h₂, LinearMap.zero_comp]
  exact absurd (Set.OrdConnected.out ‹_› hD hC ⟨(not_le.1 h₂).le, (not_le.1 h₁).le⟩) hE

/-- **A band with a single value carries no trajectories.** If all values in `s` agree, no
pushforward joins two components with value in `s`, so the Bott differential of these components
is the internal boundary `(-1)^λ_C ∂` of each of them. -/
theorem restrict_differential_apply_of_value_eq (s : Set ℝ) [s.OrdConnected]
    [DecidablePred (· ∈ s)] (hs : ∀ C D, v C ∈ s → v D ∈ s → v C = v D) (x : ∀ C, M C)
    (D : ι) :
    (B.restrict (fun C ↦ v C ∈ s)
        (B.pushforward_comp_pushforward_eq_zero_of_ordConnected v hv s)).differential x D =
      (B.rank D : ℤ).negOnePow • B.boundary D (x D) := by
  rw [restrict_differential_apply, add_eq_left]
  refine Finset.sum_eq_zero fun C _ ↦ ?_
  split_ifs with h
  · rw [correspondence_apply, hv C D (hs C D h.1 h.2).le, LinearMap.zero_apply, smul_zero]
  · rfl

include hv in
/-- **No pushforward leaves a sublevel**: a pushforward from a component with value at most `b` to
one with value above `b` vanishes. -/
theorem pushforward_eq_zero_of_mem_Iic_of_notMem_Iic {b : ℝ} {C D : ι} (hC : v C ∈ Iic b)
    (hD : v D ∉ Iic b) : B.pushforward C D = 0 :=
  hv C D (le_trans (mem_Iic.1 hC) (not_le.1 hD).le)

variable {S : ∀ C, ℤ → Submodule R (M C)}
  (hboundary : ∀ C j, ∀ x ∈ S C j, B.boundary C x ∈ S C (j - 1))
  (hpushforward : ∀ C D j, ∀ x ∈ S C j,
    B.pushforward C D x ∈ S D (j + bottDegreeShift B.rank C D))

/-- **The Bott complex of the critical components with value in `s`**, for an order-connected set
`s` of values: the Bott complex of the components `C` with `v C ∈ s`. -/
noncomputable abbrev complexOn (s : Set ℝ) [s.OrdConnected] [DecidablePred (· ∈ s)] :
    ChainComplex (ModuleCat R) ℤ :=
  B.chainComplexOn (fun C ↦ v C ∈ s)
    (B.pushforward_comp_pushforward_eq_zero_of_ordConnected v hv s) hboundary hpushforward

/-- **The sublevel–band sequence.** For `a ≤ b`, the short complex `C(Iic a) → C(Iic b) →
C(Ioc a b)` including the Bott complex of the components with value at most `a` into that of the
components with value at most `b`, and restricting the latter to the components in the band
between them. -/
noncomputable abbrev bandSequence {a b : ℝ} (hab : a ≤ b) :
    ShortComplex (ChainComplex (ModuleCat R) ℤ) :=
  B.chainComplexOnShortComplex (fun C ↦ v C ∈ Iic a)
    (B.pushforward_comp_pushforward_eq_zero_of_ordConnected v hv _) hboundary hpushforward
    (B.pushforward_comp_pushforward_eq_zero_of_ordConnected v hv (Iic b))
    (B.pushforward_comp_pushforward_eq_zero_of_ordConnected v hv (Ioc a b))
    (fun _ hC ↦ mem_Iic.2 (le_trans (mem_Iic.1 hC) hab)) (fun _ hC ↦ mem_Iic.2 hC.2)
    (fun _ hC ↦ ⟨fun h ↦ not_le.2 h.1, fun h ↦ ⟨not_le.1 h, hC⟩⟩)
    (fun _ _ hC _ hD ↦ B.pushforward_eq_zero_of_mem_Iic_of_notMem_Iic v hv hC hD)

/-- **The sublevel–band sequence is short exact.** -/
theorem bandSequence_shortExact {a b : ℝ} (hab : a ≤ b) :
    (B.bandSequence v hv hboundary hpushforward hab).ShortExact :=
  B.chainComplexOnShortComplex_shortExact ..

/-- The inclusion of the Bott complex of the components with value at most `b` into the Bott
complex, both regraded as cochain complexes along `n ↦ -n`. -/
noncomputable def filtrationι (b : ℝ) :
    (B.complexOn v hv hboundary hpushforward (Iic b)).restriction
        ComplexShape.embeddingUpIntDownInt ⟶
      (B.chainComplex hboundary hpushforward).restriction ComplexShape.embeddingUpIntDownInt :=
  restrictionMap (B.chainComplexOnι _ _ hboundary hpushforward
    fun _ _ hC hD ↦ B.pushforward_eq_zero_of_mem_Iic_of_notMem_Iic v hv hC hD) _

/-- The regraded inclusion of the components with value at most `b` is the restriction along
`n ↦ -n` of the inclusion of their Bott complex into the Bott complex. -/
theorem filtrationι_def (b : ℝ) :
    B.filtrationι v hv hboundary hpushforward b =
      restrictionMap (B.chainComplexOnι _ _ hboundary hpushforward
        fun _ _ hC hD ↦ B.pushforward_eq_zero_of_mem_Iic_of_notMem_Iic v hv hC hD) _ :=
  (rfl)

instance mono_filtrationι (b : ℝ) : Mono (B.filtrationι v hv hboundary hpushforward b) :=
  mono_of_mono_f _ fun k ↦ (ModuleCat.mono_iff_injective _).2
    (Submodule.inclusion_injective (B.restrict_totalDegree_le_totalDegree _
      (B.pushforward_comp_pushforward_eq_zero_of_ordConnected v hv (Iic b)) (-k)))

/-- **The critical-value filtration of the Bott complex.** For cut values `a : ℤ → ℝ`, the `q`th
stage is the Bott complex of the components with value at most `a q`, as a subcomplex of the Bott
complex regraded as a cochain complex along `n ↦ -n`. -/
noncomputable def filtration (a : ℤ → ℝ) (q : ℤ) :
    Subobject ((B.chainComplex hboundary hpushforward).restriction
      ComplexShape.embeddingUpIntDownInt) :=
  Subobject.mk (B.filtrationι v hv hboundary hpushforward (a q))

theorem filtration_eq_mk (a : ℤ → ℝ) (q : ℤ) :
    B.filtration v hv hboundary hpushforward a q =
      Subobject.mk (B.filtrationι v hv hboundary hpushforward (a q)) :=
  (rfl)

/-- The inclusion of the Bott complex of the components with value at most `b` into that of the
components with value at most `c ≥ b`. -/
noncomputable abbrev sublevelInclusion {b c : ℝ} (hbc : b ≤ c) :
    B.complexOn v hv hboundary hpushforward (Iic b) ⟶
      B.complexOn v hv hboundary hpushforward (Iic c) :=
  B.chainComplexOnInclusion _ _ hboundary hpushforward _
    (fun _ hC ↦ mem_Iic.2 (le_trans (mem_Iic.1 hC) hbc))
    (fun _ _ hC _ hD ↦ B.pushforward_eq_zero_of_mem_Iic_of_notMem_Iic v hv hC hD)

/-- For `b ≤ c`, the regraded inclusion of the components with value at most `b` into the Bott
complex factors through the components with value at most `c`. -/
@[reassoc (attr := simp)]
theorem restrictionMap_sublevelInclusion_comp_filtrationι {b c : ℝ} (hbc : b ≤ c) :
    restrictionMap (B.sublevelInclusion v hv hboundary hpushforward hbc)
        ComplexShape.embeddingUpIntDownInt ≫ B.filtrationι v hv hboundary hpushforward c =
      B.filtrationι v hv hboundary hpushforward b := by
  rw [filtrationι, filtrationι, ← restrictionMap_comp, chainComplexOnInclusion_comp_chainComplexOnι]

section AdjacentBands

variable {b₀ b₁ b₂ : ℝ} (h₀₁ : b₀ ≤ b₁) (h₁₂ : b₁ ≤ b₂)

/-- **The sequence of two adjacent bands.** For `b₀ ≤ b₁ ≤ b₂`, the short complex
`C(Ioc b₀ b₁) → C(Ioc b₀ b₂) → C(Ioc b₁ b₂)` including the Bott complex of the components with
value in the lower band into that of the components with value in the union of the two bands, and
restricting the latter to the components with value in the upper band. -/
noncomputable abbrev adjacentBandSequence :
    ShortComplex (ChainComplex (ModuleCat R) ℤ) :=
  B.chainComplexOnShortComplex (fun C ↦ v C ∈ Ioc b₀ b₁)
    (B.pushforward_comp_pushforward_eq_zero_of_ordConnected v hv _) hboundary hpushforward
    (B.pushforward_comp_pushforward_eq_zero_of_ordConnected v hv (Ioc b₀ b₂))
    (B.pushforward_comp_pushforward_eq_zero_of_ordConnected v hv (Ioc b₁ b₂))
    (fun _ hC ↦ ⟨hC.1, hC.2.trans h₁₂⟩) (fun _ hC ↦ ⟨h₀₁.trans_lt hC.1, hC.2⟩)
    (fun _ hC ↦ ⟨fun h h' ↦ not_le.2 h.1 h'.2, fun h ↦ ⟨not_le.1 fun h' ↦ h ⟨hC.1, h'⟩, hC.2⟩⟩)
    (fun C D hC hD hD' ↦ hv C D (hC.2.trans (not_le.1 fun h ↦ hD' ⟨hD.1, h⟩).le))

/-- **The sequence of two adjacent bands is short exact.** -/
theorem adjacentBandSequence_shortExact :
    (B.adjacentBandSequence v hv hboundary hpushforward h₀₁ h₁₂).ShortExact :=
  B.chainComplexOnShortComplex_shortExact ..

/-- Restricting the chains with value at most `b₁` to the band `Ioc b₀ b₁` and including them into
the union `Ioc b₀ b₂` of two adjacent bands is restricting them to the union. -/
theorem bandSequence_g_comp_adjacentBandSequence_f :
    (B.bandSequence v hv hboundary hpushforward h₀₁).g ≫
        (B.adjacentBandSequence v hv hboundary hpushforward h₀₁ h₁₂).f =
      B.sublevelInclusion v hv hboundary hpushforward h₁₂ ≫
        (B.bandSequence v hv hboundary hpushforward (h₀₁.trans h₁₂)).g := by
  ext k x : 3
  refine Subtype.ext (funext fun C ↦ ?_)
  -- The terms of the complexes are the total-degree pieces only after unfolding
  -- `chainComplexOn`, so `change` states the goal on the chains: both maps project onto a band.
  change restrictProj R (fun C ↦ v C ∈ Ioc b₀ b₁) x.val C =
    restrictProj R (fun C ↦ v C ∈ Ioc b₀ b₂) x.val C
  by_cases hC : v C ≤ b₁
  · simp [hC, hC.trans h₁₂]
  · simp [hC, B.apply_eq_zero_of_mem_restrict_totalDegree _ _ x.property hC]

/-- Restricting the chains with value at most `b₂` to the union `Ioc b₀ b₂` of two adjacent bands,
and then to the upper band `Ioc b₁ b₂`, is restricting them to the upper band. -/
theorem bandSequence_g_comp_adjacentBandSequence_g :
    (B.bandSequence v hv hboundary hpushforward (h₀₁.trans h₁₂)).g ≫
        (B.adjacentBandSequence v hv hboundary hpushforward h₀₁ h₁₂).g =
      (B.bandSequence v hv hboundary hpushforward h₁₂).g := by
  ext k x : 3
  refine Subtype.ext (funext fun C ↦ ?_)
  -- As above, `change` states the goal on the chains.
  change restrictProj R (fun C ↦ v C ∈ Ioc b₁ b₂)
      (restrictProj R (fun C ↦ v C ∈ Ioc b₀ b₂) x.val) C =
    restrictProj R (fun C ↦ v C ∈ Ioc b₁ b₂) x.val C
  by_cases hC : v C ∈ Ioc b₁ b₂
  · simp only [restrictProj_apply, hC, ite_true,
      show v C ∈ Ioc b₀ b₂ from ⟨h₀₁.trans_lt hC.1, hC.2⟩]
  · simp only [restrictProj_apply, hC, ite_false]

/-- Restricting the chains with value at most `b₀` to the union `Ioc b₀ b₂` of two bands above
`b₀` gives zero. -/
theorem sublevelInclusion_comp_bandSequence_g_eq_zero :
    B.sublevelInclusion v hv hboundary hpushforward h₀₁ ≫
        B.sublevelInclusion v hv hboundary hpushforward h₁₂ ≫
          (B.bandSequence v hv hboundary hpushforward (h₀₁.trans h₁₂)).g = 0 := by
  ext k x : 3
  refine Subtype.ext (funext fun C ↦ ?_)
  -- As above, `change` states the goal on the chains.
  change restrictProj R (fun C ↦ v C ∈ Ioc b₀ b₂) x.val C = 0
  by_cases hC : v C ≤ b₀
  · simp [hC]
  · simp [B.apply_eq_zero_of_mem_restrict_totalDegree _ _ x.property hC]

end AdjacentBands

variable {a : ℤ → ℝ}

/-- The critical-value filtration grows with the cut values. -/
theorem filtration_mono {q q' : ℤ} (hqq' : a q ≤ a q') :
    B.filtration v hv hboundary hpushforward a q ≤ B.filtration v hv hboundary hpushforward a q' :=
  Subobject.mk_le_mk_of_comm _ (B.restrictionMap_sublevelInclusion_comp_filtrationι v hv
    hboundary hpushforward hqq')

/-- For monotone cut values, the critical-value filtration is increasing. -/
theorem monotone_filtration (ha : Monotone a) :
    Monotone (B.filtration v hv hboundary hpushforward a) :=
  fun _ _ hqq' ↦ B.filtration_mono v hv hboundary hpushforward (ha hqq')

/-- Below all critical values, the critical-value filtration is zero. -/
theorem filtration_eq_bot {q : ℤ} (hq : ∀ C, a q < v C) :
    B.filtration v hv hboundary hpushforward a q = ⊥ := by
  refine Subobject.mk_eq_bot_iff_zero.2 (IsZero.eq_of_src ?_ _ _)
  refine (IsZero.iff_id_eq_zero _).2 (HomologicalComplex.hom_ext _ _ fun k ↦ ?_)
  -- every chain on the components with value at most `a q` vanishes, as there are none
  have hsub : ∀ j, Subsingleton ((B.restrict (fun C ↦ v C ∈ Iic (a q))
      (B.pushforward_comp_pushforward_eq_zero_of_ordConnected v hv (Iic (a q)))).totalDegree
        (restrictGrading (fun C ↦ v C ∈ Iic (a q)) S) j) := fun j ↦
    ⟨fun x y ↦ Subtype.ext <| funext fun C ↦ by
      have hC : ¬v C ∈ Iic (a q) := not_le.2 (hq C)
      rw [B.apply_eq_zero_of_mem_restrict_totalDegree _ _ x.property hC,
        B.apply_eq_zero_of_mem_restrict_totalDegree _ _ y.property hC]⟩
  have := hsub (ComplexShape.embeddingUpIntDownInt.f k)
  -- The term of the regraded complex at `k` is, by `TauCeti.BottChainData.chainComplexOn_X`, the
  -- module of chains of total degree `embeddingUpIntDownInt.f k` on these components, which is a
  -- subsingleton; the placeholder in `ModuleCat.of R _` is solved by unfolding to it.
  exact (ModuleCat.isZero_of_subsingleton (ModuleCat.of R _)).eq_of_src _ _

/-- Above all critical values, the critical-value filtration is everything. -/
theorem filtration_eq_top {q : ℤ} (hq : ∀ C, v C ≤ a q) :
    B.filtration v hv hboundary hpushforward a q = ⊤ := by
  have hS : ∀ k, (B.restrict (fun C ↦ v C ∈ Iic (a q))
      (B.pushforward_comp_pushforward_eq_zero_of_ordConnected v hv (Iic (a q)))).totalDegree
        (restrictGrading (fun C ↦ v C ∈ Iic (a q)) S) k = B.totalDegree S k := fun k ↦ by
    ext x
    simp only [mem_totalDegree_iff, restrict_rank]
    exact forall_congr' fun C ↦ by
      rw [restrictGrading_of_pos (p := fun C ↦ v C ∈ Iic (a q)) S (mem_Iic.2 (hq C))]
  have : ∀ k, IsIso ((B.filtrationι v hv hboundary hpushforward (a q)).f k) := fun k ↦
    (ConcreteCategory.isIso_iff_bijective _).2 ⟨Submodule.inclusion_injective (hS _).le,
      fun x ↦ ⟨⟨x.val, (hS _).ge x.property⟩, rfl⟩⟩
  have := Hom.isIso_of_components (B.filtrationι v hv hboundary hpushforward (a q))
  exact Subobject.mk_eq_top_of_isIso _

variable (ha : Monotone a)

/-- **The graded pieces of the critical-value filtration are the band complexes.** The quotient of
the stage `a (q + 1)` of the filtration by the stage `a q`, as the cokernel of a transition map of
the functor `CochainComplex.filtrationFunctor` of the filtration, is the regraded Bott complex of
the components with value in `Ioc (a q) (a (q + 1))`. The isomorphism is induced by restricting
chains to the band. -/
noncomputable def filtrationCokernelIso (q : ℤ) :
    cokernel ((CochainComplex.filtrationFunctor _
        (B.monotone_filtration v hv hboundary hpushforward ha)).map
        (homOfLE (CochainComplex.coe_le_coe_of_eq_add_one (rfl : q = q) rfl))) ≅
      (B.complexOn v hv hboundary hpushforward (Ioc (a q) (a (q + 1)))).restriction
        ComplexShape.embeddingUpIntDownInt :=
  CochainComplex.cokernelFiltrationFunctorMapIsoOfIsColimit _ _
    (fun q ↦ B.filtrationι v hv hboundary hpushforward (a q))
    (B.filtration_eq_mk v hv hboundary hpushforward a) q _
    (B.restrictionMap_sublevelInclusion_comp_filtrationι v hv hboundary hpushforward
      (ha (Int.le_add_one le_rfl))) _ _
    ((B.bandSequence_shortExact v hv hboundary hpushforward
      (ha (Int.le_add_one le_rfl))).restriction ComplexShape.embeddingUpIntDownInt).gIsCokernel

/-- The identification of the graded piece of the critical-value filtration with the band complex
restricts chains to the band: under the identification of the stage `a (q + 1)` with the sublevel
chains, the cokernel projection is the restriction to the band `Ioc (a q) (a (q + 1))`. -/
@[reassoc (attr := simp)]
theorem π_filtrationCokernelIso_hom (q : ℤ) :
    cokernel.π _ ≫ (B.filtrationCokernelIso v hv hboundary hpushforward ha q).hom =
      (CochainComplex.filtrationFunctorObjIsoOfEqMk _
          (B.monotone_filtration v hv hboundary hpushforward ha)
          (B.filtrationι v hv hboundary hpushforward (a (q + 1)))
          (B.filtration_eq_mk v hv hboundary hpushforward a (q + 1))).hom ≫
        restrictionMap (B.bandSequence v hv hboundary hpushforward
          (ha (Int.le_add_one le_rfl : q ≤ q + 1))).g ComplexShape.embeddingUpIntDownInt :=
  CochainComplex.π_cokernelFiltrationFunctorMapIsoOfIsColimit_hom _ _ _ _ _ _ _ _ _ _

/-- **The critical-value spectral sequence of the Bott complex.** For monotone cut values
`a : ℤ → ℝ`, the spectral sequence of the filtration of the Bott complex by the components with
value at most `a q`, in the cohomological indexing of `CochainComplex.spectralSequence`: chains of
total degree `n` sit in degree `-n`. -/
noncomputable abbrev spectralSequence :=
  CochainComplex.spectralSequence
    (CochainComplex.filtrationFunctor _ (B.monotone_filtration v hv hboundary hpushforward ha))

/-- **The first page of the critical-value spectral sequence.** The object at `(p, q)` on the
first page (numbered `2`, as in `CochainComplex.spectralSequence`) is the homology in total degree
`n` of the Bott complex of the components with value in the band `Ioc (a q) (a (q + 1))`, where
`p + q = -n`. -/
noncomputable def spectralSequenceFirstPageXIso (pq : ℤ × ℤ) (n : ℤ) (hn : pq.1 + pq.2 = -n) :
    ((B.spectralSequence v hv hboundary hpushforward ha).page 2).X pq ≅
      (B.complexOn v hv hboundary hpushforward (Ioc (a pq.2) (a (pq.2 + 1)))).homology n :=
  CochainComplex.spectralSequenceFirstPageXIsoCokernel _ pq pq.2 (pq.2 + 1) rfl rfl _ rfl ≪≫
    (homologyFunctor _ _ _).mapIso (B.filtrationCokernelIso v hv hboundary hpushforward ha pq.2) ≪≫
    HomologicalComplex.restrictionHomologyIso _ _ (pq.1 + pq.2 - 1) (pq.1 + pq.2)
      (pq.1 + pq.2 + 1) (by simp) (by simp) (i' := n + 1) (k' := n - 1) (by simp; omega)
      (by simp; omega) (by simp; omega) (by simp) (by simp)

/-- The identification of the first page of the critical-value spectral sequence with the homology
of a band is that of the first page of a filtered complex with the homology of its graded piece
(`CochainComplex.spectralSequenceFirstPageXIsoCokernel`), followed by the identification of the
graded piece with the band complex (`TauCeti.BottChainData.filtrationCokernelIso`) and the
regrading along `n ↦ -n`. -/
theorem spectralSequenceFirstPageXIso_def (pq : ℤ × ℤ) (n : ℤ) (hn : pq.1 + pq.2 = -n) :
    B.spectralSequenceFirstPageXIso v hv hboundary hpushforward ha pq n hn =
      CochainComplex.spectralSequenceFirstPageXIsoCokernel _ pq pq.2 (pq.2 + 1) rfl rfl _ rfl ≪≫
        (homologyFunctor _ _ _).mapIso
          (B.filtrationCokernelIso v hv hboundary hpushforward ha pq.2) ≪≫
        HomologicalComplex.restrictionHomologyIso _ _ (pq.1 + pq.2 - 1) (pq.1 + pq.2)
          (pq.1 + pq.2 + 1) (by simp) (by simp) (i' := n + 1) (k' := n - 1) (by simp; omega)
          (by simp; omega) (by simp; omega) (by simp) (by simp) :=
  (rfl)

/-- **The abutment of the critical-value spectral sequence** in degree `-n` is the homology in
total degree `n` of the Bott complex. -/
noncomputable def filtrationAbutmentIso (n : ℤ) :
    (CochainComplex.spectralObject (CochainComplex.filtrationFunctor _
        (B.monotone_filtration v hv hboundary hpushforward ha))).abutment (-n) ≅
      (B.chainComplex hboundary hpushforward).homology n :=
  CochainComplex.filtrationAbutmentIso _ _ _ ≪≫
    HomologicalComplex.restrictionHomologyIso _ _ (-n - 1) (-n) (-n + 1) (by simp) (by simp)
      (i' := n + 1) (k' := n - 1) (by simp; omega) (by simp) (by simp; omega) (by simp) (by simp)

/-- **Strong convergence of the critical-value spectral sequence.** If `a q₀` lies below and
`a q₁` above all critical values, then on every page `r ≥ 2` with `q - r + 2 ≤ q₀` and
`q₁ ≤ q + r - 1`, the object at `(p, q)` is the graded piece `F_{q+1} H / F_q H` of the
filtration of the abutment in degree `p + q`, which is the homology of the Bott complex in total
degree `-(p + q)` by `TauCeti.BottChainData.filtrationAbutmentIso`. -/
noncomputable def spectralSequencePageXIsoGraded {q₀ q₁ : ℤ} (h₀ : ∀ C, a q₀ < v C)
    (h₁ : ∀ C, v C ≤ a q₁) (r : ℤ) (hr : 2 ≤ r) (pq : ℤ × ℤ) (hr₀ : pq.2 - r + 2 ≤ q₀)
    (hr₁ : q₁ ≤ pq.2 + r - 1) :
    ((B.spectralSequence v hv hboundary hpushforward ha).page r).X pq ≅
      cokernel ((CochainComplex.spectralObject (CochainComplex.filtrationFunctor _
        (B.monotone_filtration v hv hboundary hpushforward ha))).abutmentFiltrationMap pq.2
          (pq.1 + pq.2)) :=
  CochainComplex.filtrationSpectralSequencePageXIsoGradedOfFinite _ _
    (B.filtration_eq_bot v hv hboundary hpushforward h₀)
    (B.filtration_eq_top v hv hboundary hpushforward h₁) r hr pq hr₀ hr₁

/-! ### The components of a band with a single value -/

section Component

include hv in
/-- No broken trajectory leaves and returns to a single component, as nonzero pushforwards
strictly lower the value. -/
theorem pushforward_comp_pushforward_eq_zero_of_eq (C : ι) (D E F : ι) (hD : D = C)
    (hF : F = C) (_ : ¬E = C) : B.pushforward E F ∘ₗ B.pushforward D E = 0 := by
  rw [hD, hF]
  by_cases h : v C ≤ v E
  · rw [hv C E h, LinearMap.comp_zero]
  · rw [hv E C (not_le.1 h).le, LinearMap.zero_comp]

/-- **The chain complex of a component** `C`: the chains `S C j` of degree `j` on `C`, with the
internal boundary `∂` of `C`. -/
-- The body is exposed so that the terms of the complex compute to the chains of each degree,
-- which the identification `TauCeti.BottChainData.componentComplexHomologyIso` is built on.
@[expose]
noncomputable def componentChains (C : ι) : ChainComplex (ModuleCat R) ℤ :=
  ChainComplex.of (fun j ↦ ModuleCat.of R (S C j))
    (fun j ↦ ModuleCat.ofHom ((B.boundary C).restrict fun x hx ↦ by
      simpa using hboundary C (j + 1) x hx))
    (fun j ↦ by
      ext x : 2
      exact Subtype.ext (LinearMap.congr_fun (B.boundary_comp_boundary C) x.val))

/-- The term of the chain complex of `C` in degree `j` consists of the chains of degree `j` on
`C`. -/
theorem componentChains_X (C : ι) (j : ℤ) :
    (B.componentChains hboundary C).X j = ModuleCat.of R (S C j) :=
  (rfl)

/-- The differential of the chain complex of `C` is the boundary of `C`. -/
theorem componentChains_d_apply (C : ι) {i k : ℤ} (hik : i = k + 1) (x : S C i) :
    ((((B.componentChains hboundary C).d i k).hom x : S C k)).val = B.boundary C x.val := by
  subst hik
  simp only [componentChains, ChainComplex.of_d, ModuleCat.hom_ofHom]
  exact LinearMap.coe_restrict_apply _ _

variable [DecidableEq ι]

/-- **The Bott complex of a single component** `C`: its chains in total degree `n` are the chains
of degree `n - λ_C` on `C`, with differential `(-1)^λ_C ∂`. -/
noncomputable abbrev componentComplex (C : ι) : ChainComplex (ModuleCat R) ℤ :=
  B.chainComplexOn (· = C) (B.pushforward_comp_pushforward_eq_zero_of_eq v hv C) hboundary
    hpushforward

/-- **The Bott data of a single component** `C`: the boundary of `C`, and no pushforwards. -/
abbrev componentData (C : ι) : BottChainData R ι M :=
  B.restrict (· = C) (B.pushforward_comp_pushforward_eq_zero_of_eq v hv C)

/-- The differential of the Bott complex of a single component `C` is `(-1)^λ_C ∂`. -/
theorem componentComplex_d_apply (C : ι) {i k : ℤ} (hik : i = k + 1)
    (x : (B.componentData v hv C).totalDegree (restrictGrading (· = C) S) i) :
    (((B.componentComplex v hv hboundary hpushforward C).d i k).hom x :
        (B.componentData v hv C).totalDegree (restrictGrading (· = C) S) k).val C =
      (B.rank C : ℤ).negOnePow • B.boundary C (x.val C) := by
  subst hik
  rw [chainComplexOn_d_apply, restrict_differential_apply, add_eq_left]
  refine Finset.sum_eq_zero fun D _ ↦ ?_
  split_ifs with hD
  · rw [hD.1, correspondence_apply, hv C C le_rfl, LinearMap.zero_apply, smul_zero]
  · rfl

/-- **The chains of total degree `m` on a single component** `C` are, by evaluation at `C`, the
chains of degree `j = m - λ_C` on `C`. The evaluation is multiplied by a sign `u`. -/
noncomputable def componentTotalDegreeEquiv (B : BottChainData R ι M) (C : ι) (u : ℤˣ) {m j : ℤ}
    (h : m - B.rank C = j) : B.totalDegree (restrictGrading (· = C) S) m ≃ₗ[R] S C j where
  toFun x := ⟨u • x.val C, by
    have := ((B.mem_totalDegree_restrictGrading_eq_iff C).1 x.property).1
    rw [h] at this
    rw [Units.smul_def]
    exact zsmul_mem this _⟩
  invFun y := ⟨Pi.single C (u • y.val), (B.mem_totalDegree_restrictGrading_eq_iff C).2
    ⟨by rw [Pi.single_eq_same, h, Units.smul_def]; exact zsmul_mem y.property _,
      fun _ hD ↦ Pi.single_eq_of_ne hD _⟩⟩
  map_add' x y := Subtype.ext (smul_add u (x.val C) (y.val C))
  map_smul' r x := Subtype.ext (smul_comm u r (x.val C))
  left_inv x := Subtype.ext <| funext fun D ↦ by
    by_cases hD : D = C
    · subst hD
      simp [smul_smul]
    · simp [Pi.single_eq_of_ne hD,
        ((B.mem_totalDegree_restrictGrading_eq_iff C).1 x.property).2 D hD]
  right_inv y := Subtype.ext (by simp [smul_smul])

@[simp]
theorem componentTotalDegreeEquiv_apply_coe (B : BottChainData R ι M) (C : ι) (u : ℤˣ) {m j : ℤ}
    (h : m - B.rank C = j) (x : B.totalDegree (restrictGrading (· = C) S) m) :
    (B.componentTotalDegreeEquiv C u h x : M C) = u • x.val C :=
  (rfl)

/-- The short complex of the Bott complex of a single component `C` in total degree `n` is that of
the chain complex of `C` in degree `n - λ_C`, lifted to the universe of the Bott complex:
evaluation at `C`, multiplied by `(-1)^λ_C` in total degree `n`, identifies the differential
`(-1)^λ_C ∂` with `∂`. -/
noncomputable def componentComplexScIso (C : ι) (n : ℤ) :
    (B.componentComplex v hv hboundary hpushforward C).sc' (n + 1) n (n - 1) ≅
      ((B.componentChains hboundary C).sc' (n - B.rank C + 1) (n - B.rank C)
        (n - B.rank C - 1)).map (ModuleCat.uliftFunctor R) :=
  ShortComplex.isoMk
    (((B.componentData v hv C).componentTotalDegreeEquiv C 1
      (by rw [restrict_rank]; ring : _ = n - B.rank C + 1)).trans
        ULift.moduleEquiv.symm).toModuleIso
    (((B.componentData v hv C).componentTotalDegreeEquiv C (B.rank C : ℤ).negOnePow
      (rfl : _ = n - B.rank C)).trans ULift.moduleEquiv.symm).toModuleIso
    (((B.componentData v hv C).componentTotalDegreeEquiv C 1
      (by rw [restrict_rank]; ring : _ = n - B.rank C - 1)).trans
        ULift.moduleEquiv.symm).toModuleIso
    (ModuleCat.hom_ext (LinearMap.ext fun (x : (B.componentData v hv C).totalDegree
        (restrictGrading (· = C) S) (n + 1)) ↦ ULift.ext (Subtype.ext (by
      -- On chains, the square states `∂ (x C) = (-1)^λ_C • (-1)^λ_C • ∂ (x C)`; the terms of the
      -- complexes are the modules of chains only after unfolding, so `change` states it there.
      change (((B.componentChains hboundary C).d (n - B.rank C + 1) (n - B.rank C)).hom
          ((B.componentData v hv C).componentTotalDegreeEquiv C 1
            (by rw [restrict_rank]; ring : _ = n - B.rank C + 1) x) : S C _).val =
        (B.rank C : ℤ).negOnePow • ((((B.componentComplex v hv hboundary hpushforward C).d
          (n + 1) n).hom x : (B.componentData v hv C).totalDegree (restrictGrading (· = C) S) n).val
            C)
      rw [B.componentChains_d_apply hboundary C rfl]
      change B.boundary C ((1 : ℤˣ) • x.val C) = _
      rw [B.componentComplex_d_apply v hv hboundary hpushforward C rfl, smul_smul,
        Int.units_mul_self, one_smul, one_smul]))))
    (ModuleCat.hom_ext (LinearMap.ext fun (x : (B.componentData v hv C).totalDegree
        (restrictGrading (· = C) S) n) ↦ ULift.ext (Subtype.ext (by
      -- On chains, the square states `∂ ((-1)^λ_C • x C) = (-1)^λ_C • ∂ (x C)`.
      change (((B.componentChains hboundary C).d (n - B.rank C) (n - B.rank C - 1)).hom
          ((B.componentData v hv C).componentTotalDegreeEquiv C (B.rank C : ℤ).negOnePow
            (rfl : _ = n - B.rank C) x) : S C _).val =
        (1 : ℤˣ) • ((((B.componentComplex v hv hboundary hpushforward C).d n (n - 1)).hom x :
          (B.componentData v hv C).totalDegree (restrictGrading (· = C) S) (n - 1)).val C)
      rw [B.componentChains_d_apply hboundary C (by ring)]
      change B.boundary C ((B.rank C : ℤ).negOnePow • x.val C) = _
      rw [B.componentComplex_d_apply v hv hboundary hpushforward C (by ring), one_smul,
        LinearMap.map_smul_of_tower]))))

/-- In total degree `n`, the identification `TauCeti.BottChainData.componentComplexScIso`
evaluates a chain at `C` and multiplies it by `(-1)^λ_C`. -/
theorem componentComplexScIso_hom_τ₂_apply (C : ι) (n : ℤ)
    (x : (B.componentData v hv C).totalDegree (restrictGrading (· = C) S) n) :
    Subtype.val (p := (· ∈ S C (n - B.rank C)))
        ((B.componentComplexScIso v hv hboundary hpushforward C n).hom.τ₂.hom x).down =
      (B.rank C : ℤ).negOnePow • x.val C :=
  (rfl)

/-- **The homology of the Bott complex of a single component** `C` in total degree `n` is the
homology `H_(n - λ_C)(C)` of the chains on `C`, lifted to the universe of the Bott complex
(`TauCeti.BottChainData.componentComplexScIso`). -/
noncomputable def componentComplexHomologyIso (C : ι) (n : ℤ) :
    (B.componentComplex v hv hboundary hpushforward C).homology n ≅
      (ModuleCat.uliftFunctor R).obj ((B.componentChains hboundary C).homology (n - B.rank C)) :=
  (B.componentComplex v hv hboundary hpushforward C).homologyIsoSc' (n + 1) n (n - 1)
      (by simp) (by simp) ≪≫
    ShortComplex.homologyMapIso (B.componentComplexScIso v hv hboundary hpushforward C n) ≪≫
    ((B.componentChains hboundary C).sc' _ _ _).mapHomologyIso (ModuleCat.uliftFunctor R) ≪≫
    (ModuleCat.uliftFunctor R).mapIso ((B.componentChains hboundary C).homologyIsoSc'
      (n - B.rank C + 1) (n - B.rank C) (n - B.rank C - 1) (by simp) (by simp)).symm

variable (s : Set ℝ) [s.OrdConnected] [DecidablePred (· ∈ s)]
  (hs : ∀ C D, v C ∈ s → v D ∈ s → v C = v D)

/-- The bicone exhibiting the Bott complex of the components with value in `s`, all of the same
value, as the direct sum of the Bott complexes of these components: the inclusions of the single
components and the projections onto them. -/
-- The body is exposed so that the vertex, projections and inclusions of the bicone, stated by the
-- `@[simps]` lemmas, are the complex of the band and the restrictions to and inclusions of its
-- components.
@[expose, simps]
noncomputable def complexOnBicone :
    Bicone fun C : {C // v C ∈ s} ↦ B.componentComplex v hv hboundary hpushforward C.val where
  pt := B.complexOn v hv hboundary hpushforward s
  π C := B.chainComplexOnRestriction _ _ hboundary hpushforward _
    (fun _ hD ↦ hD ▸ C.property) fun D E hD hE _ ↦ hv D E (hs D E hD (hE ▸ C.property)).le
  ι C := B.chainComplexOnInclusion _ _ hboundary hpushforward _
    (fun _ hD ↦ hD ▸ C.property) fun D E hD hE _ ↦ hv D E (hs D E (hD ▸ C.property) hE).le
  ι_π C D := by
    ext k x : 3
    refine Subtype.ext (funext fun E ↦ ?_)
    split_ifs with h
    · subst h
      -- The terms of the complexes are the total-degree pieces only after unfolding
      -- `chainComplexOn`, so `change` states the goal on the chains.
      change restrictProj R (· = C.val) x.val E = x.val E
      rw [B.restrictProj_eq_self _ _ x.property]
    · change restrictProj R (· = D.val) x.val E = 0
      by_cases hE : E = D.val
      · subst hE
        simp only [restrictProj_apply, ite_true]
        exact B.apply_eq_zero_of_mem_restrict_totalDegree _ _ x.property
          fun h' ↦ h (Subtype.ext h'.symm)
      · simp [hE]

/-- The bicone of the components with value in `s` is a direct sum: the chains on the components
with value in `s` are the sums of their projections to the single components. -/
noncomputable def isBilimitComplexOnBicone :
    (B.complexOnBicone v hv hboundary hpushforward s hs).IsBilimit :=
  isBilimitOfTotal _ <| HomologicalComplex.hom_ext _ _ fun k ↦ by
    -- the chains of total degree `k` on the components with value in `s`
    let T := (B.restrict (fun D ↦ v D ∈ s)
      (B.pushforward_comp_pushforward_eq_zero_of_ordConnected v hv s)).totalDegree
        (restrictGrading (fun D ↦ v D ∈ s) S) k
    have hT (C : {C // v C ∈ s}) (y : ∀ C, M C) (hy : y ∈ T) :
        restrictProj R (· = C.val) y ∈ T :=
      (mem_totalDegree_iff _ _).2 fun D ↦ restrictGrading_mono S (fun D hD ↦ hD ▸ C.property) D _
        (restrictProj_apply_mem_restrictGrading S ((mem_totalDegree_iff _ _).1 hy D)
          fun D hD ↦ hD ▸ C.property)
    -- each summand is the projection onto the chains of a single component
    have hP (C : {C // v C ∈ s}) : ((B.complexOnBicone v hv hboundary hpushforward s hs).π C ≫
        (B.complexOnBicone v hv hboundary hpushforward s hs).ι C).f k =
          ModuleCat.ofHom ((restrictProj R (· = C.val)).restrict (p := T) (q := T) (hT C)) :=
      -- In degree `k`, `π C ≫ ι C` is the `ModuleCat` composite of the projection
      -- `ofHom ((restrictProj R (· = C)).restrict _)` of `chainComplexOnRestriction` and the
      -- inclusion `ofHom (Submodule.inclusion _)` of `chainComplexOnInclusion`. Both maps are
      -- restrictions of linear maps of `∀ D, M D`, so their composite is, by unfolding
      -- `ModuleCat.ofHom`, `LinearMap.restrict` and `Submodule.inclusion`, the restriction of
      -- `restrictProj R (· = C)` to `T`. The rewriting lemmas `HomologicalComplex.comp_f` and
      -- `ModuleCat.hom_comp` do not apply, as the terms of the complexes are the modules of chains
      -- only after unfolding `chainComplexOn`.
      (rfl)
    rw [show (∑ C, (B.complexOnBicone v hv hboundary hpushforward s hs).π C ≫
        (B.complexOnBicone v hv hboundary hpushforward s hs).ι C).f k =
          ∑ C, ((B.complexOnBicone v hv hboundary hpushforward s hs).π C ≫
            (B.complexOnBicone v hv hboundary hpushforward s hs).ι C).f k from
        (HomologicalComplex.eval _ _ k).map_sum _ _, Finset.sum_congr rfl fun C _ ↦ hP C]
    -- The sum is stated between the total-degree pieces, which are the terms of the complexes
    -- only after unfolding `chainComplexOn`, so it is proved there and closed by `exact`.
    have key : (∑ C, ModuleCat.ofHom ((restrictProj R (· = C.val)).restrict (p := T) (q := T)
        (hT C)) : ModuleCat.of R T ⟶ ModuleCat.of R T) = 𝟙 _ := by
      refine ModuleCat.hom_ext (LinearMap.ext fun x ↦ Subtype.ext (funext fun E ↦ ?_))
      rw [ModuleCat.hom_sum, LinearMap.sum_apply, Submodule.coe_sum, Finset.sum_apply]
      simp only [ModuleCat.hom_ofHom, LinearMap.coe_restrict_apply, restrictProj_apply,
        ModuleCat.hom_id, LinearMap.id_apply]
      by_cases hE : v E ∈ s
      · rw [Fintype.sum_eq_single ⟨E, hE⟩ fun C hC ↦ ite_eq_right_iff.2 fun h ↦
          absurd (Subtype.ext h.symm) hC]
        simp
      · rw [Finset.sum_eq_zero fun C _ ↦ ite_eq_right_iff.2 fun (h : E = C.val) ↦
          absurd (h ▸ C.property) hE]
        exact (B.apply_eq_zero_of_mem_restrict_totalDegree _ _ x.property hE).symm
    exact key

/-- **The homology of a band with a single value is the direct sum of the homologies of its
components.** If all values in `s` agree, there are no trajectories between the components with
value in `s`, so their Bott complex is the direct sum of the Bott complexes of the single
components (`TauCeti.BottChainData.isBilimitComplexOnBicone`), and its homology is the direct
sum of their homologies. -/
noncomputable def homologyComplexOnIsoBiproduct (n : ℤ) :
    (B.complexOn v hv hboundary hpushforward s).homology n ≅
      ⨁ fun C : {C // v C ∈ s} ↦
        (B.componentComplex v hv hboundary hpushforward C.val).homology n :=
  biproduct.uniqueUpToIso _
    (b := (homologyFunctor _ _ n).mapBicone (B.complexOnBicone v hv hboundary hpushforward s hs))
    -- The homology functor is additive, so it keeps the relation `∑ π ≫ ι = 𝟙`; Mathlib's
    -- preservation instance `Functor.preservesFiniteBiproductsOfAdditive` only covers index types
    -- in `Type`, whereas the components form a type in any universe.
    (isBilimitOfTotal _ <| by
      have h : ∑ C, (homologyFunctor (ModuleCat R) _ n).map
          ((B.complexOnBicone v hv hboundary hpushforward s hs).π C ≫
            (B.complexOnBicone v hv hboundary hpushforward s hs).ι C) = 𝟙 _ := by
        rw [← Functor.map_sum, IsBilimit.total (B.isBilimitComplexOnBicone v hv hboundary
          hpushforward s hs), CategoryTheory.Functor.map_id]
      simp only [CategoryTheory.Functor.map_comp] at h
      exact h)

end Component
/-- **The first page of the critical-value spectral sequence for a single critical value per
band.** If all values in the band `Ioc (a q) (a (q + 1))` agree, the object at `(p, q)` on the first
page, with `p + q = -n`, is the direct sum `⊕ H_(n - λ_C)(C)` over the components `C` in the band
of the homology in degree `n - λ_C` of the chains on `C` (`TauCeti.BottChainData.componentChains`),
lifted to the universe of the Bott complex (`TauCeti.BottChainData.componentComplexHomologyIso`).
-/
noncomputable def spectralSequenceFirstPageXIsoBiproduct [DecidableEq ι] (pq : ℤ × ℤ) (n : ℤ)
    (hn : pq.1 + pq.2 = -n)
    (hband : ∀ C D, v C ∈ Ioc (a pq.2) (a (pq.2 + 1)) → v D ∈ Ioc (a pq.2) (a (pq.2 + 1)) →
      v C = v D) :
    ((B.spectralSequence v hv hboundary hpushforward ha).page 2).X pq ≅
      ⨁ fun C : {C // v C ∈ Ioc (a pq.2) (a (pq.2 + 1))} ↦ (ModuleCat.uliftFunctor R).obj
        ((B.componentChains hboundary C.val).homology (n - B.rank C.val)) :=
  B.spectralSequenceFirstPageXIso v hv hboundary hpushforward ha pq n hn ≪≫
    B.homologyComplexOnIsoBiproduct v hv hboundary hpushforward _ hband n ≪≫
    biproduct.mapIso fun C ↦ B.componentComplexHomologyIso v hv hboundary hpushforward C.val n

/-- The identification of the first page with a direct sum of homologies of components is the
identification with the homology of the band
(`TauCeti.BottChainData.spectralSequenceFirstPageXIso`) followed by the splitting of the band into
its components (`TauCeti.BottChainData.homologyComplexOnIsoBiproduct`). -/
theorem spectralSequenceFirstPageXIsoBiproduct_def [DecidableEq ι] (pq : ℤ × ℤ) (n : ℤ)
    (hn : pq.1 + pq.2 = -n)
    (hband : ∀ C D, v C ∈ Ioc (a pq.2) (a (pq.2 + 1)) → v D ∈ Ioc (a pq.2) (a (pq.2 + 1)) →
      v C = v D) :
    B.spectralSequenceFirstPageXIsoBiproduct v hv hboundary hpushforward ha pq n hn hband =
      B.spectralSequenceFirstPageXIso v hv hboundary hpushforward ha pq n hn ≪≫
        B.homologyComplexOnIsoBiproduct v hv hboundary hpushforward _ hband n ≪≫
        biproduct.mapIso fun C ↦
          B.componentComplexHomologyIso v hv hboundary hpushforward C.val n :=
  (rfl)

end Value

end BottChainData

end TauCeti
