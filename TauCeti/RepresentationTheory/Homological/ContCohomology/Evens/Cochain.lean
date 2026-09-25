/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.CharP.Two
public import Mathlib.Data.ZMod.Basic
public import Mathlib.GroupTheory.Index
public import Mathlib.Topology.Algebra.OpenSubgroup
public import Mathlib.Topology.Instances.ZMod
public import Mathlib.Topology.Piecewise

import Mathlib.Tactic.Abel
import Mathlib.Tactic.Group
import Mathlib.Tactic.LinearCombination

/-!
# The two-point graph cochain of the Evens norm at index two

Let `U` be a subgroup of index two of a topological group `G`, let `s` be an element outside `U`,
and let `α : U →* Multiplicative (ZMod 2)` be a continuous homomorphism, that is a continuous
`1`-cocycle of `U` with trivial `𝔽₂` coefficients. The multiplicative transfer (Evens norm)
`N^{Ev}(α) ∈ H²(G, 𝔽₂)` is, in this degree and at this index, the class of an explicit
`2`-cochain built from the two components of the Shapiro description of `α`:

```text
b₁ γ = α γ            (γ ∈ U),        b₁ γ = α (γ s)        (γ ∉ U),
b_s γ = b₁ (s⁻¹ γ),
ν (γ, η) = b₁ γ * b_s η                         (γ ∈ U),
ν (γ, η) = b₁ γ * b₁ η + b₁ η * b_s η           (γ ∉ U).
```

This file builds `b₁`, `b_s`, their sum and `ν`, and proves the cochain-level facts the class
`N^{Ev}(α)` and its characterizing identities rest on: `b₁` and `b_s` are the two coordinates of
a `1`-cocycle of `G` valued in the permutation module `𝔽₂[G/U]`, so their sum is a continuous
homomorphism `G → 𝔽₂`, and `ν` is a continuous `2`-cocycle whose class does not depend on the
element `s` chosen outside `U`.

## Main definitions

* `TauCeti.ContCohomology.evensExtend`: a homomorphism on `U`, extended by zero to `G`.
* `TauCeti.ContCohomology.evensB1` and `TauCeti.ContCohomology.evensBs`: the two Shapiro
  components.
* `TauCeti.ContCohomology.evensCorCochain`: their sum, the shape the degree-one corestriction
  of `α` over the transversal `{1, s}` takes.
* `TauCeti.ContCohomology.evensGraphCochain`: the two-point graph `2`-cochain `ν`.

## Main statements

* `TauCeti.ContCohomology.evensExtend_mul_hom`, `evensB1_mul_hom` and `evensBs_mul_hom`:
  the extension by zero and the two Shapiro components are additive in the homomorphism.
* `TauCeti.ContCohomology.evensB1_mul_of_mem`, `evensB1_mul_of_notMem`, `evensBs_mul_of_mem` and
  `evensBs_mul_of_notMem`: the cocycle law of the pair `(b₁, b_s)` in the permutation module,
  from which everything else follows.
* `TauCeti.ContCohomology.evensCorCochain_mul`: the sum `b₁ + b_s` is a homomorphism,
  which neither summand is.
* `TauCeti.ContCohomology.evensGraphCochain_cocycle_identity`: the `2`-cocycle identity for `ν`,
  in its trivial-action form.
* `TauCeti.ContCohomology.continuous_evensGraphCochain`: continuity of `ν`, for `U` open.
* `TauCeti.ContCohomology.evensGraphCochain_sub_evensGraphCochain`: two elements outside `U` give
  graph cochains differing by the explicit coboundary of
  `γ ↦ α (s⁻¹ s') * evensExtend U α γ`, so the class of `ν` depends on `U` and `α` alone.
* `TauCeti.ContCohomology.evensGraphCochain_apply_of_mem_of_mem`: on `U × U` the graph cochain is
  the cup-product cochain of `α` with its conjugate `η ↦ α (s⁻¹ η s)`.

## Implementation notes

`b₁` and `b_s` are cochains and **not** cocycles, so neither has a class of its own: for
`G = C₄ = ⟨σ⟩`, `U = ⟨σ²⟩`, `s = σ` and `α ≠ 0`, the values of `b₁` at `1, σ, σ², σ³` are
`0, 1, 1, 0`, so `b₁ (σ * σ) ≠ b₁ σ + b₁ σ`. Only the sum is a homomorphism; the section
`AcceptanceCheck` at the end of this file records that computation, which is why the
corestriction statement is about the sum and not about the two components separately.

The element `s` is data of the cochain formulas and of nothing else. Two elements outside `U`
give graph cochains differing by an explicit coboundary, so the class they define depends on `U`
and `α` alone; that is `TauCeti.ContCohomology.evensGraphCochain_sub_evensGraphCochain`, which is
stated at **every** `s'` outside `U` rather than at a chosen one.

Everything below is stated for a plain subgroup `U` together with the hypotheses `U.index = 2`
where the cocycle identities require it, and `IsOpen (U : Set G)` for continuity. The continuity
statements need only separately continuous multiplication, since the arguments use fixed
translations and the fact that an open subgroup is closed. No topology at all is needed for the
algebraic half: the cocycle laws and the comparison of two elements outside `U` are identities of
plain functions `G → 𝔽₂`.

The `2`-cocycle identity is stated in the form it takes for a trivial action, an equation between
sums of four values, rather than through `groupCohomology.IsCocycle₂`, whose statement carries a
scalar action of `G` on `𝔽₂` that nothing here has to fix.

Characteristic two is used only through `CharTwo.two_eq_zero` and `CharTwo.neg_eq`, and only in
three places: the `2`-cocycle identity when `γ` lies outside `U`, the comparison of two elements
outside `U`, and the fact that the extension by zero is invariant under inversion. The
corresponding identities over a general coefficient ring are false, which is why Evens' expansion
is restricted to even degrees away from characteristic two.

## References

* L. Evens, *A generalization of the transfer map in the cohomology of groups*, Trans. Amer.
  Math. Soc. **108** (1963), 54–65: the multiplicative transfer, of which the cochain built here
  is the index-two, degree-one case.
* A. Kozlowski, *The Evens–Kahn formula for the total Stiefel–Whitney class*, Proc. Amer. Math.
  Soc. **91** (1984), 309–313: the transfer for double coverings, that is the index-two case,
  and the formula it gives for a representation induced from a subgroup of index two.
* A. Kozlowski, *Transfers in the group of multiplicative units of the classical cohomology ring
  and Stiefel–Whitney classes*, Publ. Res. Inst. Math. Sci. **25** (1989), 59–74: the same
  transfer on the multiplicative units of the cohomology ring, expressed for double coverings in
  terms of the Evens transfer; that expression in low degrees is the identity the cochain here is
  built to satisfy.
-/

public section

namespace TauCeti.ContCohomology

universe u

variable {G : Type u} [Group G]

section Extend

/-! ### A homomorphism on `U`, extended by zero -/

variable (U : Subgroup G) (α : U →* Multiplicative (ZMod 2))

open scoped Classical in
/-- A homomorphism `α : U →* Multiplicative 𝔽₂` — that is, a `1`-cocycle of `U` with trivial
coefficients — extended by zero to the whole group: it is `Multiplicative.toAdd ∘ α` on `U` and
`0` outside. No hypothesis on `U` or on `α` is needed to define it; when `U` is open and `α` is
continuous the extension is continuous, by
`TauCeti.ContCohomology.continuous_evensExtend`. The Shapiro components of the Evens norm are
built from it. -/
noncomputable def evensExtend : G → ZMod 2 :=
  fun γ => if h : γ ∈ U then Multiplicative.toAdd (α ⟨γ, h⟩) else 0

variable {U α}

/-- On `U`, the extension by zero of `α` is `α`, read additively. -/
@[simp]
theorem evensExtend_of_mem {γ : G} (h : γ ∈ U) :
    evensExtend U α γ = Multiplicative.toAdd (α ⟨γ, h⟩) :=
  dite_eq_left h

/-- Off `U`, the extension by zero of `α` vanishes. -/
@[simp]
theorem evensExtend_of_notMem {γ : G} (h : γ ∉ U) : evensExtend U α γ = 0 :=
  dite_eq_right h

/-- The extension by zero is additive in the homomorphism. -/
@[simp]
theorem evensExtend_mul_hom {β : U →* Multiplicative (ZMod 2)} (γ : G) :
    evensExtend U (α * β) γ = evensExtend U α γ + evensExtend U β γ := by
  by_cases h : γ ∈ U
  · simp [evensExtend_of_mem h]
  · simp [evensExtend_of_notMem h]

/-- The extension by zero is additive on `U`, where it is `α`. It is not additive on `G`: that
failure is what the Evens norm measures. -/
@[simp]
theorem evensExtend_mul {x y : G} (hx : x ∈ U) (hy : y ∈ U) :
    evensExtend U α (x * y) = evensExtend U α x + evensExtend U α y := by
  -- the three values are `α` at three points of `U`, and the first point is the product of the
  -- other two in `U`, since membership is a proposition and the coercion is multiplicative
  have hmk : (⟨x * y, U.mul_mem hx hy⟩ : U) = ⟨x, hx⟩ * ⟨y, hy⟩ := Subtype.ext (by simp)
  rw [evensExtend_of_mem (U.mul_mem hx hy), evensExtend_of_mem hx, evensExtend_of_mem hy, hmk,
    map_mul, toAdd_mul]

/-- The extension by zero is `𝔽₂`-valued, so it takes inverses to themselves. No membership
hypothesis is needed: on `U` this is `CharTwo.neg_eq`, and outside `U` both sides vanish. -/
@[simp]
theorem evensExtend_inv (x : G) : evensExtend U α x⁻¹ = evensExtend U α x := by
  by_cases hx : x ∈ U
  · -- as in `evensExtend_mul`, the point `⟨x⁻¹, _⟩` of `U` is the inverse of the point `⟨x, hx⟩`
    have hmk : (⟨x⁻¹, U.inv_mem hx⟩ : U) = (⟨x, hx⟩ : U)⁻¹ := Subtype.ext (by simp)
    rw [evensExtend_of_mem (U.inv_mem hx), evensExtend_of_mem hx, hmk, map_inv, toAdd_inv,
      CharTwo.neg_eq]
  · rw [evensExtend_of_notMem (mt U.inv_mem_iff.mp hx), evensExtend_of_notMem hx]

variable (U α)

/-- The extension by zero of a continuous homomorphism on an open subgroup is continuous: `U` is
clopen and `𝔽₂` is discrete, so the two branches do not have to agree anywhere. -/
theorem continuous_evensExtend [TopologicalSpace G] [SeparatelyContinuousMul G]
    (hopen : IsOpen (U : Set G)) (hα : Continuous α) : Continuous (evensExtend U α) := by
  -- on `U` the extension takes the first branch of its `dite`, so it restricts to `α` there
  have hres : (U : Set G).domRestrict (evensExtend U α) =
      fun v : ↥(U : Set G) => Multiplicative.toAdd (α ⟨(v : G), v.2⟩) :=
    funext fun v => dite_eq_left v.2
  -- off `U` it takes the second branch, so it restricts to the constant `0`
  have hresc : ((U : Set G)ᶜ).domRestrict (evensExtend U α) = fun _ => (0 : ZMod 2) :=
    funext fun v => dite_eq_right v.2
  have hon : ContinuousOn (evensExtend U α) (U : Set G) := by
    rw [continuousOn_iff_continuous_domRestrict, hres]
    exact continuous_toAdd.comp (hα.comp (continuous_subtype_val.subtype_mk _))
  have hoff : ContinuousOn (evensExtend U α) ((U : Set G)ᶜ) := by
    rw [continuousOn_iff_continuous_domRestrict, hresc]
    exact continuous_const
  rw [continuous_iff_continuousAt]
  intro x
  by_cases hx : x ∈ U
  · exact hon.continuousAt (hopen.mem_nhds hx)
  · exact hoff.continuousAt ((U.isClosed_of_isOpen hopen).isOpen_compl.mem_nhds hx)

end Extend

section ShapiroComponents

/-! ### The two Shapiro components and their sum -/

variable (U : Subgroup G) (s : G) (α : U →* Multiplicative (ZMod 2))

open scoped Classical in
/-- The first Shapiro component `b₁ γ = α γ` for `γ ∈ U` and `b₁ γ = α (γ s)` otherwise.

It is a cochain and **not** a cocycle, so it has no class of its own; only the sum
`TauCeti.ContCohomology.evensCorCochain` of the two components is a homomorphism. -/
noncomputable def evensB1 : G → ZMod 2 :=
  fun γ => if γ ∈ U then evensExtend U α γ else evensExtend U α (γ * s)

/-- The second Shapiro component `b_s γ = b₁ (s⁻¹ γ)`. A cochain, for the same reason as
`TauCeti.ContCohomology.evensB1`. -/
noncomputable def evensBs : G → ZMod 2 :=
  fun γ => evensB1 U s α (s⁻¹ * γ)

/-- The sum `b₁ + b_s` of the two Shapiro components, a cochain defined for any `U` and any `s`.
For `U` of index two and `s ∉ U` it is, unlike either summand, a homomorphism, by
`TauCeti.ContCohomology.evensCorCochain_mul`, and it is continuous whenever `U` is open and `α`
is continuous, by `TauCeti.ContCohomology.continuous_evensCorCochain`; it is then the shape the
degree-one corestriction of `α` over the transversal `{1, s}` takes. -/
noncomputable def evensCorCochain : G → ZMod 2 :=
  fun γ => evensB1 U s α γ + evensBs U s α γ

variable {U s α}

/-- On `U`, the first Shapiro component `b₁` is the extension by zero of `α`. -/
@[simp]
theorem evensB1_of_mem {γ : G} (h : γ ∈ U) : evensB1 U s α γ = evensExtend U α γ :=
  ite_eq_left h

/-- Off `U`, the first Shapiro component is `b₁ γ = α (γ s)`, with `α` extended by zero. -/
@[simp]
theorem evensB1_of_notMem {γ : G} (h : γ ∉ U) : evensB1 U s α γ = evensExtend U α (γ * s) :=
  ite_eq_right h

/-- The second Shapiro component is `b_s γ = b₁ (s⁻¹ γ)`. -/
@[simp]
theorem evensBs_apply (γ : G) : evensBs U s α γ = evensB1 U s α (s⁻¹ * γ) := (rfl)

/-- The first Shapiro component is additive in the homomorphism. -/
@[simp]
theorem evensB1_mul_hom {β : U →* Multiplicative (ZMod 2)} (γ : G) :
    evensB1 U s (α * β) γ = evensB1 U s α γ + evensB1 U s β γ := by
  by_cases h : γ ∈ U
  · simp [evensB1_of_mem h]
  · simp [evensB1_of_notMem h]

/-- The second Shapiro component is additive in the homomorphism. -/
theorem evensBs_mul_hom {β : U →* Multiplicative (ZMod 2)} (γ : G) :
    evensBs U s (α * β) γ = evensBs U s α γ + evensBs U s β γ := by
  simp

/-- The corestriction cochain is the sum `b₁ + b_s` of the two Shapiro components. -/
@[simp]
theorem evensCorCochain_apply (γ : G) :
    evensCorCochain U s α γ = evensB1 U s α γ + evensBs U s α γ := (rfl)

/-! The four identities below are the cocycle law of the pair `(b₁, b_s)` read in the permutation
module `𝔽₂[G/U]`: left translation by an element of `U` fixes the two coordinates and left
translation by an element outside `U` exchanges them.

They and `TauCeti.ContCohomology.evensCorCochain_mul` carry `@[grind =]` rather than `@[simp]`:
their side conditions `U.index = 2` and `s ∉ U` are hypotheses of the ambient context, which
`grind` uses and `simp`'s discharger does not see, and three of them loop as `simp` lemmas
against the unfolding lemma `TauCeti.ContCohomology.evensBs_apply`, which turns a `b_s` produced
on the right back into a `b₁` the left-hand side matches again. -/

/-- Left translation of `b₁` by an element of `U`. -/
@[grind =]
theorem evensB1_mul_of_mem (hU : U.index = 2) (hs : s ∉ U) {γ : G} (hγ : γ ∈ U) (η : G) :
    evensB1 U s α (γ * η) = evensB1 U s α γ + evensB1 U s α η := by
  by_cases hη : η ∈ U
  · rw [evensB1_of_mem (U.mul_mem hγ hη), evensB1_of_mem hγ, evensB1_of_mem hη,
      evensExtend_mul hγ hη]
  · have hγη : γ * η ∉ U := by simp [Subgroup.mul_mem_iff_of_index_two hU, hγ, hη]
    have hηs : η * s ∈ U := by simp [Subgroup.mul_mem_iff_of_index_two hU, hs, hη]
    rw [evensB1_of_notMem hγη, evensB1_of_mem hγ, evensB1_of_notMem hη, mul_assoc,
      evensExtend_mul hγ hηs]

/-- Left translation of `b₁` by an element outside `U` produces the *other* component. -/
@[grind =]
theorem evensB1_mul_of_notMem (hU : U.index = 2) (hs : s ∉ U) {γ : G} (hγ : γ ∉ U) (η : G) :
    evensB1 U s α (γ * η) = evensB1 U s α γ + evensBs U s α η := by
  have hγs : γ * s ∈ U := by simp [Subgroup.mul_mem_iff_of_index_two hU, hs, hγ]
  by_cases hη : η ∈ U
  · have hγη : γ * η ∉ U := by simp [Subgroup.mul_mem_iff_of_index_two hU, hγ, hη]
    have hsη : s⁻¹ * η ∉ U := by
      simp [Subgroup.mul_mem_iff_of_index_two hU, hs, hη]
    have hsηs : s⁻¹ * η * s ∈ U := by
      simp [Subgroup.mul_mem_iff_of_index_two hU, hs, hη]
    rw [evensB1_of_notMem hγη, evensB1_of_notMem hγ, evensBs_apply, evensB1_of_notMem hsη,
      ← evensExtend_mul hγs hsηs]
    congr 1
    group
  · have hγη : γ * η ∈ U := by simp [Subgroup.mul_mem_iff_of_index_two hU, hγ, hη]
    have hsη : s⁻¹ * η ∈ U := by
      simp [Subgroup.mul_mem_iff_of_index_two hU, hs, hη]
    rw [evensB1_of_mem hγη, evensB1_of_notMem hγ, evensBs_apply, evensB1_of_mem hsη,
      ← evensExtend_mul hγs hsη]
    congr 1
    group

/-- Left translation of `b_s` by an element of `U`. -/
@[grind =]
theorem evensBs_mul_of_mem (hU : U.index = 2) (hs : s ∉ U) {γ : G} (hγ : γ ∈ U) (η : G) :
    evensBs U s α (γ * η) = evensBs U s α γ + evensBs U s α η := by
  have hsγ : s⁻¹ * γ ∉ U := by
    simp [Subgroup.mul_mem_iff_of_index_two hU, hs, hγ]
  rw [evensBs_apply, ← mul_assoc, evensB1_mul_of_notMem hU hs hsγ η, ← evensBs_apply]

/-- Left translation of `b_s` by an element outside `U` produces the *other* component. -/
@[grind =]
theorem evensBs_mul_of_notMem (hU : U.index = 2) (hs : s ∉ U) {γ : G} (hγ : γ ∉ U) (η : G) :
    evensBs U s α (γ * η) = evensBs U s α γ + evensB1 U s α η := by
  have hsγ : s⁻¹ * γ ∈ U := by
    simp [Subgroup.mul_mem_iff_of_index_two hU, hs, hγ]
  rw [evensBs_apply, ← mul_assoc, evensB1_mul_of_mem hU hs hsγ η, ← evensBs_apply]

/-- **The corestriction cochain is a `1`-cocycle.** With trivial coefficients a `1`-cocycle is a
homomorphism; the index-two hypothesis is what makes the two cross terms recombine. Neither
`TauCeti.ContCohomology.evensB1` nor `TauCeti.ContCohomology.evensBs` satisfies this on its own,
which is why the corestriction is the class of the sum and not of either summand. -/
@[grind =]
theorem evensCorCochain_mul (hU : U.index = 2) (hs : s ∉ U) (γ η : G) :
    evensCorCochain U s α (γ * η) = evensCorCochain U s α γ + evensCorCochain U s α η := by
  simp only [evensCorCochain_apply]
  by_cases hγ : γ ∈ U
  · rw [evensB1_mul_of_mem hU hs hγ, evensBs_mul_of_mem hU hs hγ]
    abel
  · rw [evensB1_mul_of_notMem hU hs hγ, evensBs_mul_of_notMem hU hs hγ]
    abel

variable (U s α)

/-- The first Shapiro component of a continuous homomorphism on an open subgroup is continuous:
`U` is clopen, so the case split is. -/
theorem continuous_evensB1 [TopologicalSpace G] [SeparatelyContinuousMul G]
    (hopen : IsOpen (U : Set G)) (hα : Continuous α) : Continuous (evensB1 U s α) := by
  classical
  have hclopen : IsClopen (U : Set G) := ⟨U.isClosed_of_isOpen hopen, hopen⟩
  exact Continuous.if (by simp [hclopen.frontier_eq])
    (continuous_evensExtend U α hopen hα)
    ((continuous_evensExtend U α hopen hα).comp (continuous_mul_const s))

/-- The second Shapiro component is the first one translated, hence continuous. -/
theorem continuous_evensBs [TopologicalSpace G] [SeparatelyContinuousMul G]
    (hopen : IsOpen (U : Set G)) (hα : Continuous α) : Continuous (evensBs U s α) :=
  (continuous_evensB1 U s α hopen hα).comp (continuous_const_mul s⁻¹)

/-- The corestriction cochain of a continuous homomorphism on an open subgroup is continuous. -/
theorem continuous_evensCorCochain [TopologicalSpace G] [SeparatelyContinuousMul G]
    (hopen : IsOpen (U : Set G)) (hα : Continuous α) : Continuous (evensCorCochain U s α) :=
  (continuous_evensB1 U s α hopen hα).add (continuous_evensBs U s α hopen hα)

end ShapiroComponents

section GraphCochain

/-! ### The two-point graph cochain -/

variable (U : Subgroup G) (s : G) (α : U →* Multiplicative (ZMod 2))

open scoped Classical in
/-- **The two-point graph `2`-cochain** of a homomorphism `α` on an index-two subgroup `U` at an
element `s` outside it:

```text
ν (γ, η) = b₁ γ * b_s η                        if γ ∈ U,
ν (γ, η) = b₁ γ * b₁ η + b₁ η * b_s η          otherwise.
```

The formula defines a cochain for any `U` and any `s`. For `U` of index two and `s ∉ U` it
satisfies the `2`-cocycle identity, by
`TauCeti.ContCohomology.evensGraphCochain_cocycle_identity`, and it is continuous whenever `U`
is open and `α` is continuous, by
`TauCeti.ContCohomology.continuous_evensGraphCochain`; under those hypotheses its class in
`H²(G, 𝔽₂)` is the Evens norm `N^{Ev}(α)`. -/
noncomputable def evensGraphCochain : G × G → ZMod 2 :=
  fun q => if q.1 ∈ U then evensB1 U s α q.1 * evensBs U s α q.2
    else evensB1 U s α q.1 * evensB1 U s α q.2 + evensB1 U s α q.2 * evensBs U s α q.2

variable {U s α}

/-- For `γ ∈ U`, the graph cochain takes `(γ, η)` to `b₁ γ · b_s η`. -/
@[simp]
theorem evensGraphCochain_of_mem {γ : G} (h : γ ∈ U) (η : G) :
    evensGraphCochain U s α (γ, η) = evensB1 U s α γ * evensBs U s α η :=
  ite_eq_left h

/-- For `γ ∉ U`, the graph cochain takes `(γ, η)` to `b₁ γ · b₁ η + b₁ η · b_s η`. -/
@[simp]
theorem evensGraphCochain_of_notMem {γ : G} (h : γ ∉ U) (η : G) :
    evensGraphCochain U s α (γ, η) =
      evensB1 U s α γ * evensB1 U s α η + evensB1 U s α η * evensBs U s α η :=
  ite_eq_right h

/-- **The graph cochain is a `2`-cocycle.** This is the trivial-action form of the inhomogeneous
`2`-cocycle identity, the same equation as `groupCohomology.IsCocycle₂` with the scalar action
dropped. The two cases in which `γ` lies outside `U` need characteristic two; the other two hold
over any commutative ring. -/
theorem evensGraphCochain_cocycle_identity (hU : U.index = 2) (hs : s ∉ U) (γ η j : G) :
    evensGraphCochain U s α (γ * η, j) + evensGraphCochain U s α (γ, η) =
      evensGraphCochain U s α (η, j) + evensGraphCochain U s α (γ, η * j) := by
  by_cases hγ : γ ∈ U <;> by_cases hη : η ∈ U
  · rw [evensGraphCochain_of_mem (U.mul_mem hγ hη), evensGraphCochain_of_mem hγ,
      evensGraphCochain_of_mem hη, evensGraphCochain_of_mem hγ,
      evensB1_mul_of_mem hU hs hγ, evensBs_mul_of_mem hU hs hη]
    ring
  · have hγη : γ * η ∉ U := by simp [Subgroup.mul_mem_iff_of_index_two hU, hγ, hη]
    rw [evensGraphCochain_of_notMem hγη, evensGraphCochain_of_mem hγ,
      evensGraphCochain_of_notMem hη, evensGraphCochain_of_mem hγ,
      evensB1_mul_of_mem hU hs hγ, evensBs_mul_of_notMem hU hs hη]
    ring
  · have hγη : γ * η ∉ U := by simp [Subgroup.mul_mem_iff_of_index_two hU, hγ, hη]
    rw [evensGraphCochain_of_notMem hγη, evensGraphCochain_of_notMem hγ,
      evensGraphCochain_of_mem hη, evensGraphCochain_of_notMem hγ,
      evensB1_mul_of_notMem hU hs hγ, evensB1_mul_of_mem hU hs hη,
      evensBs_mul_of_mem hU hs hη]
    linear_combination (-(evensB1 U s α η * evensBs U s α j)) * CharTwo.two_eq_zero (R := ZMod 2)
  · have hγη : γ * η ∈ U := by simp [Subgroup.mul_mem_iff_of_index_two hU, hγ, hη]
    rw [evensGraphCochain_of_mem hγη, evensGraphCochain_of_notMem hγ,
      evensGraphCochain_of_notMem hη, evensGraphCochain_of_notMem hγ,
      evensB1_mul_of_notMem hU hs hγ, evensB1_mul_of_notMem hU hs hη,
      evensBs_mul_of_notMem hU hs hη]
    linear_combination
      (-(evensB1 U s α η * evensB1 U s α j + evensB1 U s α j * evensBs U s α j)) *
        CharTwo.two_eq_zero (R := ZMod 2)

variable (U s α)

/-- The graph cochain of a continuous homomorphism on an open subgroup is continuous: the case
split is on the clopen set `U × G` and both branches are products of continuous functions. -/
theorem continuous_evensGraphCochain [TopologicalSpace G] [SeparatelyContinuousMul G]
    (hopen : IsOpen (U : Set G)) (hα : Continuous α) : Continuous (evensGraphCochain U s α) := by
  classical
  have hclopen : IsClopen {q : G × G | q.1 ∈ U} :=
    ⟨(U.isClosed_of_isOpen hopen).preimage continuous_fst, hopen.preimage continuous_fst⟩
  have hb1 : Continuous (evensB1 U s α) := continuous_evensB1 U s α hopen hα
  have hbs : Continuous (evensBs U s α) := continuous_evensBs U s α hopen hα
  exact Continuous.if (by simp [hclopen.frontier_eq])
    ((hb1.comp continuous_fst).mul (hbs.comp continuous_snd))
    (((hb1.comp continuous_fst).mul (hb1.comp continuous_snd)).add
      ((hb1.comp continuous_snd).mul (hbs.comp continuous_snd)))

end GraphCochain

section Restriction

/-! ### The graph cochain on the subgroup

On `U × U` the graph cochain is the cup-product cochain of `α` with its conjugate by `s`, which
is again a homomorphism on `U` since `U` is normal at index two. This is the cochain form of the
identity `res_U N^{Ev}(α) = α ⌣ (s · α)`. -/

variable {U : Subgroup G} {s : G} {α : U →* Multiplicative (ZMod 2)}

/-- **The graph cochain restricted to `U`** is the product of the extension of `α` with its
`s`-conjugate. This evaluation formula holds for any subgroup and any `s ∉ U`. -/
theorem evensGraphCochain_apply_of_mem_of_mem (hs : s ∉ U) {γ η : G}
    (hγ : γ ∈ U) (hη : η ∈ U) :
    evensGraphCochain U s α (γ, η) =
      evensExtend U α γ * evensExtend U α (s⁻¹ * η * s) := by
  have hsη : s⁻¹ * η ∉ U := by
    simpa only [U.mul_mem_cancel_right hη, U.inv_mem_iff] using hs
  rw [evensGraphCochain_of_mem hγ, evensB1_of_mem hγ, evensBs_apply, evensB1_of_notMem hsη]

end Restriction

section ChangeOfElement

/-! ### Independence of the element outside `U`

Two elements outside `U` give graph cochains differing by an explicit coboundary, so the class of
the graph cochain in `H²(G, 𝔽₂)` depends on `U` and `α` alone. This is an identity of plain
functions and needs no topology; the `1`-cochain whose coboundary it is becomes continuous once
`G` is a topological group, `U` is open and `α` is continuous, by
`TauCeti.ContCohomology.continuous_evensExtend`. -/

variable {U : Subgroup G} {s s' : G} {α : U →* Multiplicative (ZMod 2)}

/-- Outside `U` the first Shapiro component changes by the value of `α` at `s⁻¹ s'`. -/
theorem evensB1_eq_add_of_notMem (hU : U.index = 2) (hs : s ∉ U) (hs' : s' ∉ U) {γ : G}
    (hγ : γ ∉ U) :
    evensB1 U s' α γ = evensB1 U s α γ + evensExtend U α (s⁻¹ * s') := by
  have hss' : s⁻¹ * s' ∈ U := by
    simp [Subgroup.mul_mem_iff_of_index_two hU, hs, hs']
  have hγs : γ * s ∈ U := by simp [Subgroup.mul_mem_iff_of_index_two hU, hs, hγ]
  -- the two evaluation points differ by the factor `s⁻¹ * s'` of `U`, at which `α` is additive
  have hsplit : γ * s' = γ * s * (s⁻¹ * s') := by group
  rw [evensB1_of_notMem hγ, evensB1_of_notMem hγ, hsplit, evensExtend_mul hγs hss']

/-- Outside `U` the second Shapiro component changes by the same value, so the two components
move together and their sum, the corestriction cochain, does not change at all. -/
theorem evensBs_eq_add_of_notMem (hU : U.index = 2) (hs : s ∉ U) (hs' : s' ∉ U) {γ : G}
    (hγ : γ ∉ U) :
    evensBs U s' α γ = evensBs U s α γ + evensExtend U α (s⁻¹ * s') := by
  have hss' : s⁻¹ * s' ∈ U := by
    simp [Subgroup.mul_mem_iff_of_index_two hU, hs, hs']
  have hsγ : s⁻¹ * γ ∈ U := by
    simp [Subgroup.mul_mem_iff_of_index_two hU, hs, hγ]
  have hs'γ : s'⁻¹ * γ ∈ U := by
    simp [Subgroup.mul_mem_iff_of_index_two hU, hs', hγ]
  -- the two evaluation points differ by the factor `(s⁻¹ * s')⁻¹` of `U`
  have hsplit : s'⁻¹ * γ = (s⁻¹ * s')⁻¹ * (s⁻¹ * γ) := by group
  rw [evensBs_apply, evensBs_apply, evensB1_of_mem hs'γ, evensB1_of_mem hsγ, hsplit,
    evensExtend_mul (U.inv_mem hss') hsγ, evensExtend_inv]
  abel

/-- On `U` the second Shapiro component does not depend on the element chosen outside either: it
is evaluated at `s⁻¹ γ`, which lies outside `U`, and the change in the first component there is
cancelled by the change in the evaluation point. -/
theorem evensBs_eq_of_mem (hU : U.index = 2) (hs : s ∉ U) (hs' : s' ∉ U) {γ : G} (hγ : γ ∈ U) :
    evensBs U s' α γ = evensBs U s α γ := by
  have hss' : s⁻¹ * s' ∈ U := by
    simp [Subgroup.mul_mem_iff_of_index_two hU, hs, hs']
  have hsγ : s⁻¹ * γ ∉ U := by
    simp [Subgroup.mul_mem_iff_of_index_two hU, hs, hγ]
  have hs'γ : s'⁻¹ * γ ∉ U := by
    simp [Subgroup.mul_mem_iff_of_index_two hU, hs', hγ]
  have hsγs : s⁻¹ * γ * s ∈ U := by
    simp [Subgroup.mul_mem_iff_of_index_two hU, hs, hγ]
  -- the change of element conjugates the evaluation point by the factor `s⁻¹ * s'` of `U`
  have hsplit : s'⁻¹ * γ * s' = (s⁻¹ * s')⁻¹ * (s⁻¹ * γ * s) * (s⁻¹ * s') := by group
  rw [evensBs_apply, evensBs_apply, evensB1_of_notMem hs'γ, evensB1_of_notMem hsγ, hsplit,
    evensExtend_mul (U.mul_mem (U.inv_mem hss') hsγs) hss',
    evensExtend_mul (U.inv_mem hss') hsγs, evensExtend_inv]
  linear_combination (evensExtend U α (s⁻¹ * s')) * CharTwo.two_eq_zero (R := ZMod 2)

/-- **The graph cochain does not depend on the element chosen outside `U`, up to a coboundary.**
Two elements `s` and `s'` outside an index-two subgroup give graph cochains differing by the
coboundary of `γ ↦ α (s⁻¹ s') * evensExtend U α γ`, where
`TauCeti.ContCohomology.evensExtend` is the extension of `α` by zero. That `1`-cochain is
continuous whenever `α` is and `U` is open, by
`TauCeti.ContCohomology.continuous_evensExtend`, so the class of the graph cochain in
`H²(G, 𝔽₂)` depends on `U` and `α` alone. -/
theorem evensGraphCochain_sub_evensGraphCochain (hU : U.index = 2) (hs : s ∉ U) (hs' : s' ∉ U)
    (γ η : G) :
    evensGraphCochain U s' α (γ, η) - evensGraphCochain U s α (γ, η) =
      evensExtend U α (s⁻¹ * s') * evensExtend U α η -
          evensExtend U α (s⁻¹ * s') * evensExtend U α (γ * η) +
        evensExtend U α (s⁻¹ * s') * evensExtend U α γ := by
  by_cases hγ : γ ∈ U <;> by_cases hη : η ∈ U
  · simp only [evensGraphCochain_of_mem hγ, evensB1_of_mem hγ]
    rw [evensBs_eq_of_mem hU hs hs' hη, evensExtend_mul hγ hη]
    ring
  · have hγη : γ * η ∉ U := by simp [Subgroup.mul_mem_iff_of_index_two hU, hγ, hη]
    simp only [evensGraphCochain_of_mem hγ, evensB1_of_mem hγ]
    rw [evensBs_eq_add_of_notMem hU hs hs' hη, evensExtend_of_notMem hη,
      evensExtend_of_notMem hγη]
    ring
  · have hγη : γ * η ∉ U := by simp [Subgroup.mul_mem_iff_of_index_two hU, hγ, hη]
    simp only [evensGraphCochain_of_notMem hγ, evensB1_of_mem hη]
    rw [evensB1_eq_add_of_notMem hU hs hs' hγ, evensBs_eq_of_mem hU hs hs' hη,
      evensExtend_of_notMem hγ, evensExtend_of_notMem hγη]
    ring
  · have hγη : γ * η ∈ U := by simp [Subgroup.mul_mem_iff_of_index_two hU, hγ, hη]
    have hsplit : evensExtend U α (γ * η) = evensB1 U s α γ + evensBs U s α η := by
      rw [← evensB1_of_mem hγη]
      exact evensB1_mul_of_notMem hU hs hγ η
    rw [evensGraphCochain_of_notMem hγ, evensGraphCochain_of_notMem hγ,
      evensB1_eq_add_of_notMem hU hs hs' hγ, evensB1_eq_add_of_notMem hU hs hs' hη,
      evensBs_eq_add_of_notMem hU hs hs' hη, evensExtend_of_notMem hγ,
      evensExtend_of_notMem hη, hsplit]
    linear_combination
      (evensExtend U α (s⁻¹ * s') * evensB1 U s α γ +
          evensExtend U α (s⁻¹ * s') * evensB1 U s α η +
          evensExtend U α (s⁻¹ * s') * evensBs U s α η +
          evensExtend U α (s⁻¹ * s') * evensExtend U α (s⁻¹ * s')) *
        CharTwo.two_eq_zero (R := ZMod 2)

end ChangeOfElement

section AcceptanceCheck

/-! ### The two components are not cocycles

Evaluated at `(s, s)` neither Shapiro component is additive as soon as `α (s²) ≠ 0`, while their
sum is. The smallest instance is `G = C₄ = ⟨σ⟩` with `U = ⟨σ²⟩`, `s = σ` and `α ≠ 0`, where the
values of `b₁` at `1, σ, σ², σ³` are `0, 1, 1, 0`. Giving `b₁` and `b_s` classes of their own
would be a type error dressed as a statement, and this is the computation that catches it. -/

variable {U : Subgroup G} {s : G} {α : U →* Multiplicative (ZMod 2)}

example (hU : U.index = 2) (hs : s ∉ U) (hs2 : s * s ∈ U)
    (hα : Multiplicative.toAdd (α ⟨s * s, hs2⟩) ≠ 0) :
    evensB1 U s α (s * s) ≠ evensB1 U s α s + evensB1 U s α s ∧
      evensBs U s α (s * s) ≠ evensBs U s α s + evensBs U s α s ∧
        evensCorCochain U s α (s * s) =
          evensCorCochain U s α s + evensCorCochain U s α s := by
  have hsinv : s⁻¹ * s ∈ U := by rw [inv_mul_cancel]; exact U.one_mem
  -- `b_s` is read at `s⁻¹ * (s * s) = s`, which lies outside `U`
  have hcancel : s⁻¹ * (s * s) = s := by group
  have hsinvs : s⁻¹ * (s * s) ∉ U := by rw [hcancel]; exact hs
  have hcancels : s⁻¹ * (s * s) * s = s * s := by rw [hcancel]
  refine ⟨?_, ?_, evensCorCochain_mul hU hs s s⟩
  · rw [evensB1_of_mem hs2, evensExtend_of_mem hs2, evensB1_of_notMem hs,
      CharTwo.add_self_eq_zero]
    exact hα
  · rw [evensBs_apply, evensBs_apply, evensB1_of_notMem hsinvs, evensB1_of_mem hsinv,
      CharTwo.add_self_eq_zero, hcancels, evensExtend_of_mem hs2]
    exact hα

end AcceptanceCheck

end TauCeti.ContCohomology
