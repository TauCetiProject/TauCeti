/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Finset.Sum
public import TauCeti.LowDimTopology.Bordered.StrandsAlgebra.Occupancy
public import TauCeti.LowDimTopology.Heegaard.Generator

/-!
# Generators of bordered Heegaard diagrams and their idempotents

A bordered Heegaard diagram of Lipshitz, Ozsváth and Thurston is a compact surface `Σ` of genus
`g` with one boundary circle, carrying `g` disjoint `β`-circles and an `α`-system made of `2k`
disjoint `α`-arcs with their ends on `∂Σ` and `g - k` disjoint `α`-circles in the interior. The
boundary circle with the ends of the `α`-arcs is a pointed matched circle `Z` with `4k` points,
the two ends of each arc forming a matched pair. A *generator* is a set of `g` intersection
points of the `α`- and `β`-curves with exactly one point on each `β`-circle, exactly one on each
`α`-circle, and at most one on each `α`-arc. Its *occupancy* `o(x)` is the set of `α`-arcs it
meets; counting points shows that it has `g - (g - k) = k` elements.

The occupancy decides the idempotent of a generator in the two bordered invariants: in the type
`A` module `CFA(H)` over the algebra `A(Z)` the generator `x` satisfies `x I_A(x) = x` with
`I_A(x) = I(o(x))`, and in the type `D` structure `CFD(H)` over `A(-Z)` it satisfies
`I_D(x) x = x` with `I_D(x) = I(o(x)ᶜ)`, the idempotent of the complementary set of arcs. The
idempotent `I(s)` of a set `s` of matched pairs only depends on the pairs, and `-Z` has the same
pairs as `Z`. Both idempotents have `k` strands, so the bordered invariants of a diagram whose
boundary has genus `k` live over the summands with `k` strands.

Gluing a diagram `H₁` with boundary `Z` to a diagram `H₂` with boundary `-Z` along their
boundaries joins each `α`-arc of `H₁` to the `α`-arc of `H₂` with the same ends into an
`α`-circle, and gives a closed Heegaard diagram `H₁ ∪ H₂` of genus `g₁ + g₂`. Its generators are
exactly the pairs `(x₁, x₂)` of generators with complementary occupancies, that is, with
`I_A(x₁) I_D(x₂) ≠ 0`: these are the generators `x₁ ⊗ x₂` of the box tensor product
`CFA(H₁) ⊠ CFD(H₂)` over the idempotents. This is the identification of generators in the
pairing theorem `CF̂(H₁ ∪ H₂) ≃ CFA(H₁) ⊠ CFD(H₂)`.

Here a diagram is recorded only by its intersection data, as in
`TauCeti.LowDimTopology.Heegaard.Generator`: each intersection point has a `β`-circle in `Fin g`
and an `α`-curve, an arc in `Arc` or a circle in `AlphaCircle`
(`TauCeti.BorderedHeegaardIntersectionSystem`). For the idempotents the arcs are labelled by the
pairs of the matched circle through a map `M` from its points to `Arc`, sending each point to the
arc ending there, as in the matched subalgebra `TauCeti.StrandsAlgebra.matchedSubalgebra R M`;
for the algebra `A(-Z)` the points are read in the reversed order. The counts `2k` and `g - k` of
arcs and circles are hypotheses of the results that use them. Both glued diagrams use the same
labels of the arcs: the ends of an `α`-arc of `H₂` form the same matched pair. The agreement of
these data with an actual bordered diagram and of the generators with intersection points of the
tori in the symmetric product is geometric and is not formalized here.

## Main definitions

* `TauCeti.BorderedHeegaardIntersectionSystem`: the intersection data of a bordered Heegaard
  diagram.
* `TauCeti.BorderedHeegaardIntersectionSystem.Generator`: its generators, one intersection point
  on each `β`-circle, on distinct `α`-curves, meeting every `α`-circle.
* `TauCeti.BorderedHeegaardIntersectionSystem.occupied`: the occupancy `o(x)`.
* `TauCeti.BorderedHeegaardIntersectionSystem.typeAIdem`,
  `TauCeti.BorderedHeegaardIntersectionSystem.typeDIdem`: the idempotents `I_A(x)` and `I_D(x)`.
* `TauCeti.BorderedHeegaardIntersectionSystem.glue`: the intersection data of the closed diagram
  `H₁ ∪ H₂`.

## Main results

* `TauCeti.BorderedHeegaardIntersectionSystem.card_occupied_add_card`: `#o(x) + (g - k) = g`.
* `TauCeti.BorderedHeegaardIntersectionSystem.typeAIdem_mem_matchedSummand`,
  `TauCeti.BorderedHeegaardIntersectionSystem.typeDIdem_mem_matchedSummand`: both idempotents lie
  in the summand with `k` strands.
* `TauCeti.BorderedHeegaardIntersectionSystem.typeAIdem_mul_typeDIdem_ne_zero_iff`:
  `I_A(x₁) I_D(x₂)` is nonzero exactly when `o(x₁) = o(x₂)ᶜ`.
* `TauCeti.BorderedHeegaardIntersectionSystem.glueGeneratorEquiv`: the generators of `H₁ ∪ H₂` are
  the pairs of generators with complementary occupancies, and
  `TauCeti.BorderedHeegaardIntersectionSystem.glueGeneratorEquivTypeAIdem` those with
  `I_A(x₁) I_D(x₂) ≠ 0`.

## References

* R. Lipshitz, P. Ozsváth and D. Thurston, *Bordered Heegaard Floer homology*, Mem. Amer. Math.
  Soc. **254** (2018), no. 1216, [arXiv:0810.0687](https://arxiv.org/abs/0810.0687): Chapter 4
  (bordered Heegaard diagrams and their generators), the definitions of `CFD` and `CFA` (the
  idempotents `I_D(x)` and `I_A(x)`), and the proof of the pairing theorem, Theorem 1.3 (the
  generators of the glued diagram).
-/

public section

open Finset

namespace TauCeti

universe u v w

/-- The intersection data of a bordered Heegaard diagram of genus `g`: each intersection point
lies on one of the `g` `β`-circles and on one `α`-curve, which is either an `α`-arc in `Arc`,
with ends on the boundary circle, or an `α`-circle in `AlphaCircle`. Geometric surface data are
additional structure. -/
@[ext]
structure BorderedHeegaardIntersectionSystem (g : ℕ) (Arc : Type u) (AlphaCircle : Type v)
    (Point : Type w) where
  /-- The `α`-arc or `α`-circle containing an intersection point. -/
  alpha : Point → Arc ⊕ AlphaCircle
  /-- The `β`-circle containing an intersection point. -/
  beta : Point → Fin g

namespace BorderedHeegaardIntersectionSystem

variable {g : ℕ} {Arc : Type u} {AlphaCircle : Type v} {Point : Type w}
  (H : BorderedHeegaardIntersectionSystem g Arc AlphaCircle Point)

/-- A generator of a bordered Heegaard diagram: one intersection point on each `β`-circle, such
that no two of them lie on the same `α`-curve and every `α`-circle contains one of them. So each
`α`-circle contains exactly one point and each `α`-arc at most one. -/
@[ext]
structure Generator where
  /-- The point of the generator on the `β`-circle `j`. -/
  point : Fin g → Point
  beta_point (j : Fin g) : H.beta (point j) = j
  alpha_comp_point_injective : Function.Injective (H.alpha ∘ point)
  exists_alpha_point_eq_inr (c : AlphaCircle) : ∃ j, H.alpha (point j) = .inr c

attribute [simp] Generator.beta_point

/-- A generator is determined by its points. -/
theorem Generator.point_injective : Function.Injective (Generator.point (H := H)) :=
  fun _ _ ↦ Generator.ext

instance [Finite Point] : Finite H.Generator :=
  Finite.of_injective _ (Generator.point_injective H)

/-! ### The occupancy of a generator -/

/-- The occupancy `o(x)` of a generator: the set of `α`-arcs containing one of its points. -/
def occupied (x : H.Generator) : Finset Arc :=
  (univ.map ⟨H.alpha ∘ x.point, x.alpha_comp_point_injective⟩).toLeft

variable {H} in
@[simp]
theorem mem_occupied {x : H.Generator} {a : Arc} :
    a ∈ H.occupied x ↔ ∃ j, H.alpha (x.point j) = .inl a := by
  simp [occupied]

/-- **The occupancy of a generator** of a diagram of genus `g` with `g - k` `α`-circles has `k`
elements: the `g` points of a generator lie on distinct `α`-curves, one on each `α`-circle and
the others on the occupied arcs. -/
theorem card_occupied_add_card [Fintype AlphaCircle] (x : H.Generator) :
    #(H.occupied x) + Fintype.card AlphaCircle = g := by
  have hright : (univ.map ⟨H.alpha ∘ x.point, x.alpha_comp_point_injective⟩).toRight = univ := by
    ext c
    simpa using x.exists_alpha_point_eq_inr c
  have h := card_toLeft_add_card_toRight
    (u := univ.map ⟨H.alpha ∘ x.point, x.alpha_comp_point_injective⟩)
  rwa [hright, card_univ, card_map, card_univ, Fintype.card_fin] at h

/-! ### The idempotents of a generator -/

section Idempotents

variable [DecidableEq Arc] (R : Type*) [CommSemiring R] {α : Type*} [LinearOrder α]
  [Fintype α] (M : α → Arc)

/-- The idempotent `I_A(x) = I(o(x))` of a generator in the type `A` module of the diagram: the
idempotent of the matched subalgebra for the matching `M` of the boundary points by the arcs
ending at them, at the occupied arcs. -/
noncomputable def typeAIdem (x : H.Generator) : StrandsAlgebra R α :=
  StrandsAlgebra.matchedIdem R M (H.occupied x)

/-- The idempotent `I_D(x) = I(o(x)ᶜ)` of a generator in the type `D` structure of the diagram:
the idempotent of the matched subalgebra for the matching `M` at the unoccupied arcs. For a
diagram with boundary `Z` the type `D` structure lives over `A(-Z)`, whose matching reads the
points of `Z` in the reversed order. -/
noncomputable def typeDIdem [Fintype Arc] (x : H.Generator) : StrandsAlgebra R α :=
  StrandsAlgebra.matchedIdem R M (H.occupied x)ᶜ

theorem typeAIdem_def (x : H.Generator) :
    H.typeAIdem R M x = StrandsAlgebra.matchedIdem R M (H.occupied x) :=
  (rfl)

theorem typeDIdem_def [Fintype Arc] (x : H.Generator) :
    H.typeDIdem R M x = StrandsAlgebra.matchedIdem R M (H.occupied x)ᶜ :=
  (rfl)

theorem isIdempotentElem_typeAIdem (x : H.Generator) : IsIdempotentElem (H.typeAIdem R M x) :=
  StrandsAlgebra.isIdempotentElem_matchedIdem M _

theorem isIdempotentElem_typeDIdem [Fintype Arc] (x : H.Generator) :
    IsIdempotentElem (H.typeDIdem R M x) :=
  StrandsAlgebra.isIdempotentElem_matchedIdem M _

/-- In a diagram of genus `g` with `g - k` `α`-circles, the idempotent `I_A(x)` has `k` strands. -/
theorem typeAIdem_mem_matchedSummand [Fintype AlphaCircle] {k : ℕ}
    (hk : Fintype.card AlphaCircle + k = g) (x : H.Generator) :
    H.typeAIdem R M x ∈ StrandsAlgebra.matchedSummand R M k := by
  have hx := H.card_occupied_add_card x
  obtain rfl : #(H.occupied x) = k := by omega
  exact StrandsAlgebra.matchedIdem_mem_matchedSummand M _

/-- In a diagram of genus `g` with `2k` `α`-arcs and `g - k` `α`-circles, the idempotent `I_D(x)`
has `k` strands. -/
theorem typeDIdem_mem_matchedSummand [Fintype Arc] [Fintype AlphaCircle] {k : ℕ}
    (hk : Fintype.card AlphaCircle + k = g) (hArc : Fintype.card Arc = 2 * k) (x : H.Generator) :
    H.typeDIdem R M x ∈ StrandsAlgebra.matchedSummand R M k := by
  have hx := H.card_occupied_add_card x
  have hc : #(H.occupied x)ᶜ = k := by
    rw [card_compl]
    omega
  rw [typeDIdem_def, ← hc]
  exact StrandsAlgebra.matchedIdem_mem_matchedSummand M _

variable {g₂ : ℕ} {AlphaCircle₂ : Type*} {Point₂ : Type*}
  (H₂ : BorderedHeegaardIntersectionSystem g₂ Arc AlphaCircle₂ Point₂)

/-- The product `I_A(x₁) I_D(x₂)` of the idempotents of generators of two diagrams with the same
arcs is `I_A(x₁)` when `o(x₁) = o(x₂)ᶜ`, and zero otherwise. -/
theorem typeAIdem_mul_typeDIdem [Fintype Arc] (x₁ : H.Generator) (x₂ : H₂.Generator) :
    H.typeAIdem R M x₁ * H₂.typeDIdem R M x₂ =
      if H.occupied x₁ = (H₂.occupied x₂)ᶜ then H.typeAIdem R M x₁ else 0 :=
  StrandsAlgebra.matchedIdem_mul_matchedIdem M _ _

/-- When every arc has an end and the coefficients are nontrivial, `I_A(x₁) I_D(x₂)` is nonzero
exactly when the occupancies `o(x₁)` and `o(x₂)` are complementary. These are the pairs giving
generators `x₁ ⊗ x₂` of the box tensor product of the type `A` module of the first diagram with
the type `D` structure of the second over the idempotents. -/
theorem typeAIdem_mul_typeDIdem_ne_zero_iff [Fintype Arc] [Nontrivial R]
    (hM : Function.Surjective M) (x₁ : H.Generator) (x₂ : H₂.Generator) :
    H.typeAIdem R M x₁ * H₂.typeDIdem R M x₂ ≠ 0 ↔ H.occupied x₁ = (H₂.occupied x₂)ᶜ :=
  StrandsAlgebra.matchedIdem_mul_matchedIdem_ne_zero_iff (by simp [hM.range_eq])

end Idempotents

/-! ### Gluing two bordered diagrams -/

section Glue

variable {g₁ g₂ : ℕ} {AlphaCircle₁ : Type*} {AlphaCircle₂ : Type*} {Point₁ : Type*}
  {Point₂ : Type*}

/-- The `α`-curve of the glued diagram containing an `α`-arc or `α`-circle of the first diagram:
an arc becomes the circle made of the two arcs with its ends. -/
def glueCurveLeft : Arc ⊕ AlphaCircle₁ → (AlphaCircle₁ ⊕ AlphaCircle₂) ⊕ Arc :=
  Sum.elim .inr (.inl ∘ .inl)

/-- The `α`-curve of the glued diagram containing an `α`-arc or `α`-circle of the second
diagram. -/
def glueCurveRight : Arc ⊕ AlphaCircle₂ → (AlphaCircle₁ ⊕ AlphaCircle₂) ⊕ Arc :=
  Sum.elim .inr (.inl ∘ .inr)

@[simp]
theorem glueCurveLeft_inl (a : Arc) :
    (glueCurveLeft (.inl a) : (AlphaCircle₁ ⊕ AlphaCircle₂) ⊕ Arc) = .inr a :=
  (rfl)

@[simp]
theorem glueCurveLeft_inr (c : AlphaCircle₁) :
    (glueCurveLeft (.inr c) : (AlphaCircle₁ ⊕ AlphaCircle₂) ⊕ Arc) = .inl (.inl c) :=
  (rfl)

@[simp]
theorem glueCurveRight_inl (a : Arc) :
    (glueCurveRight (.inl a) : (AlphaCircle₁ ⊕ AlphaCircle₂) ⊕ Arc) = .inr a :=
  (rfl)

@[simp]
theorem glueCurveRight_inr (c : AlphaCircle₂) :
    (glueCurveRight (.inr c) : (AlphaCircle₁ ⊕ AlphaCircle₂) ⊕ Arc) = .inl (.inr c) :=
  (rfl)

theorem glueCurveLeft_injective :
    Function.Injective
      (glueCurveLeft : Arc ⊕ AlphaCircle₁ → (AlphaCircle₁ ⊕ AlphaCircle₂) ⊕ Arc) :=
  Sum.inr_injective.sumElim (Sum.inl_injective.comp Sum.inl_injective) (by simp)

theorem glueCurveRight_injective :
    Function.Injective
      (glueCurveRight : Arc ⊕ AlphaCircle₂ → (AlphaCircle₁ ⊕ AlphaCircle₂) ⊕ Arc) :=
  Sum.inr_injective.sumElim (Sum.inl_injective.comp Sum.inr_injective) (by simp)

variable (H₁ : BorderedHeegaardIntersectionSystem g₁ Arc AlphaCircle₁ Point₁)
  (H₂ : BorderedHeegaardIntersectionSystem g₂ Arc AlphaCircle₂ Point₂)
  (e : (AlphaCircle₁ ⊕ AlphaCircle₂) ⊕ Arc ≃ Fin (g₁ + g₂))

section GluePoint

variable {H₁ H₂}


/-- The points of a pair of generators, one on each `β`-circle of the glued diagram. -/
def gluePoint (x₁ : H₁.Generator) (x₂ : H₂.Generator) (j : Fin (g₁ + g₂)) : Point₁ ⊕ Point₂ :=
  Sum.elim (.inl ∘ x₁.point) (.inr ∘ x₂.point) (finSumFinEquiv.symm j)

@[simp]
theorem gluePoint_castAdd (x₁ : H₁.Generator) (x₂ : H₂.Generator) (j : Fin g₁) :
    gluePoint x₁ x₂ (Fin.castAdd g₂ j) = .inl (x₁.point j) := by
  simp [gluePoint]

@[simp]
theorem gluePoint_natAdd (x₁ : H₁.Generator) (x₂ : H₂.Generator) (j : Fin g₂) :
    gluePoint x₁ x₂ (Fin.natAdd g₁ j) = .inr (x₂.point j) := by
  simp [gluePoint]

end GluePoint

variable [Fintype Point₁] [Fintype Point₂]

/-- The intersection data of the closed Heegaard diagram `H₁ ∪ H₂` obtained by gluing two bordered
diagrams along their boundaries: its intersection points are those of `H₁` and of `H₂`, its
`β`-circles are those of `H₁` followed by those of `H₂`, and its `α`-circles are those of `H₁`,
those of `H₂`, and one circle for each arc, made of the arcs of `H₁` and `H₂` with the same ends.
The `α`-circles are numbered by an equivalence `e`. -/
def glue : HeegaardIntersectionSystem (g₁ + g₂) (Point₁ ⊕ Point₂) where
  pointFintype := inferInstance
  alpha := e ∘ Sum.elim (glueCurveLeft ∘ H₁.alpha) (glueCurveRight ∘ H₂.alpha)
  beta := finSumFinEquiv ∘ Sum.map H₁.beta H₂.beta

@[simp]
theorem glue_alpha_inl (p : Point₁) :
    (glue H₁ H₂ e).alpha (.inl p) = e (glueCurveLeft (H₁.alpha p)) :=
  (rfl)

@[simp]
theorem glue_alpha_inr (p : Point₂) :
    (glue H₁ H₂ e).alpha (.inr p) = e (glueCurveRight (H₂.alpha p)) :=
  (rfl)

@[simp]
theorem glue_beta_inl (p : Point₁) :
    (glue H₁ H₂ e).beta (.inl p) = Fin.castAdd g₂ (H₁.beta p) :=
  (rfl)

@[simp]
theorem glue_beta_inr (p : Point₂) :
    (glue H₁ H₂ e).beta (.inr p) = Fin.natAdd g₁ (H₂.beta p) :=
  (rfl)

variable {H₁ H₂}

/-- The points of the glued diagram on the `β`-circle `j` of the first diagram are the points of
the first diagram on `j`. -/
theorem glue_beta_eq_castAdd_iff (q : Point₁ ⊕ Point₂) (j : Fin g₁) :
    (glue H₁ H₂ e).beta q = Fin.castAdd g₂ j ↔ ∃ p, q = .inl p ∧ H₁.beta p = j := by
  rcases q with p | p
  · simp
  · simp only [glue_beta_inr, reduceCtorEq, false_and, exists_false, iff_false, Fin.ext_iff,
      Fin.val_natAdd, Fin.val_castAdd]
    omega

/-- The points of the glued diagram on the `β`-circle `j` of the second diagram are the points of
the second diagram on `j`. -/
theorem glue_beta_eq_natAdd_iff (q : Point₁ ⊕ Point₂) (j : Fin g₂) :
    (glue H₁ H₂ e).beta q = Fin.natAdd g₁ j ↔ ∃ p, q = .inr p ∧ H₂.beta p = j := by
  rcases q with p | p
  · simp only [glue_beta_inl, reduceCtorEq, false_and, exists_false, iff_false, Fin.ext_iff,
      Fin.val_natAdd, Fin.val_castAdd]
    omega
  · simp

theorem glue_beta_gluePoint (x₁ : H₁.Generator) (x₂ : H₂.Generator) (j : Fin (g₁ + g₂)) :
    (glue H₁ H₂ e).beta (gluePoint x₁ x₂ j) = j := by
  obtain ⟨j, rfl⟩ := finSumFinEquiv.surjective j
  cases j <;> simp

/-- The `α`-curves of the points of a pair of generators, read through the two diagrams. -/
private theorem glue_alpha_comp_gluePoint (x₁ : H₁.Generator) (x₂ : H₂.Generator) :
    (glue H₁ H₂ e).alpha ∘ gluePoint x₁ x₂ =
      e ∘ Sum.elim (glueCurveLeft ∘ H₁.alpha ∘ x₁.point) (glueCurveRight ∘ H₂.alpha ∘ x₂.point) ∘
        finSumFinEquiv.symm := by
  ext j
  obtain ⟨j, rfl⟩ := finSumFinEquiv.surjective j
  cases j <;> simp

/-- The points of a pair of generators lie on distinct `α`-curves of the glued diagram exactly
when the occupancies of the two generators are disjoint: the `α`-circles of the two diagrams stay
apart, and an arc of the glued diagram meets both points only if both generators occupy it. -/
theorem glue_alpha_comp_gluePoint_injective_iff (x₁ : H₁.Generator) (x₂ : H₂.Generator) :
    Function.Injective ((glue H₁ H₂ e).alpha ∘ gluePoint x₁ x₂) ↔
      Disjoint (H₁.occupied x₁) (H₂.occupied x₂) := by
  rw [glue_alpha_comp_gluePoint, e.comp_injective, Equiv.injective_comp, Sum.elim_injective,
    disjoint_left]
  refine ⟨?_, fun h ↦ ⟨?_, ?_, ?_⟩⟩
  · rintro ⟨-, -, h⟩ a ha₁ ha₂
    obtain ⟨i, hi⟩ := mem_occupied.1 ha₁
    obtain ⟨j, hj⟩ := mem_occupied.1 ha₂
    exact h i j (by simp [hi, hj])
  · exact glueCurveLeft_injective.comp x₁.alpha_comp_point_injective
  · exact glueCurveRight_injective.comp x₂.alpha_comp_point_injective
  · intro i j hij
    rcases hi : H₁.alpha (x₁.point i) with a | c <;>
      rcases hj : H₂.alpha (x₂.point j) with b | d <;>
      simp only [Function.comp_apply, hi, hj, glueCurveLeft_inl, glueCurveLeft_inr,
        glueCurveRight_inl, glueCurveRight_inr, reduceCtorEq, Sum.inr.injEq, Sum.inl.injEq] at hij
    subst hij
    exact h (mem_occupied.2 ⟨i, hi⟩) (mem_occupied.2 ⟨j, hj⟩)

/-- The points of a pair of generators meet every `α`-curve of the glued diagram exactly when
every arc is occupied by one of the two generators: each generator already meets every `α`-circle
of its own diagram. -/
theorem glue_alpha_comp_gluePoint_surjective_iff [Fintype Arc] [DecidableEq Arc]
    (x₁ : H₁.Generator) (x₂ : H₂.Generator) :
    Function.Surjective ((glue H₁ H₂ e).alpha ∘ gluePoint x₁ x₂) ↔
      H₁.occupied x₁ ∪ H₂.occupied x₂ = univ := by
  rw [glue_alpha_comp_gluePoint, e.comp_surjective, Equiv.surjective_comp, eq_univ_iff_forall]
  refine ⟨fun h a ↦ ?_, fun h ↦ ?_⟩
  · obtain ⟨j, hj⟩ := h (.inr a)
    rcases j with j | j
    · rcases hi : H₁.alpha (x₁.point j) with b | c
      · obtain rfl : b = a := by simpa [hi] using hj
        exact mem_union.2 (.inl (mem_occupied.2 ⟨j, hi⟩))
      · simp [hi] at hj
    · rcases hi : H₂.alpha (x₂.point j) with b | c
      · obtain rfl : b = a := by simpa [hi] using hj
        exact mem_union.2 (.inr (mem_occupied.2 ⟨j, hi⟩))
      · simp [hi] at hj
  · rintro ((c | c) | a)
    · obtain ⟨j, hj⟩ := x₁.exists_alpha_point_eq_inr c
      exact ⟨.inl j, by simp [hj]⟩
    · obtain ⟨j, hj⟩ := x₂.exists_alpha_point_eq_inr c
      exact ⟨.inr j, by simp [hj]⟩
    · rcases mem_union.1 (h a) with ha | ha
      · obtain ⟨j, hj⟩ := mem_occupied.1 ha
        exact ⟨.inl j, by simp [hj]⟩
      · obtain ⟨j, hj⟩ := mem_occupied.1 ha
        exact ⟨.inr j, by simp [hj]⟩

/-- The points of a pair of generators lie on distinct `α`-curves of the glued diagram exhausting
all of them exactly when the occupancies of the two generators are complementary. -/
theorem glue_alpha_comp_gluePoint_bijective_iff [Fintype Arc] [DecidableEq Arc]
    (x₁ : H₁.Generator) (x₂ : H₂.Generator) :
    Function.Bijective ((glue H₁ H₂ e).alpha ∘ gluePoint x₁ x₂) ↔
      H₁.occupied x₁ = (H₂.occupied x₂)ᶜ := by
  simp [Function.Bijective, glue_alpha_comp_gluePoint_injective_iff,
    glue_alpha_comp_gluePoint_surjective_iff, eq_compl_iff_isCompl, isCompl_iff, codisjoint_iff]

/-! ### The generators of the glued diagram -/

/-- The point of a generator of the glued diagram on the `β`-circle `j` of the first diagram, an
intersection point of the first diagram. -/
noncomputable def glueLeftPoint (x : (glue H₁ H₂ e).Generator) (j : Fin g₁) : Point₁ :=
  ((glue H₁ H₂ e).betaPoint x (Fin.castAdd g₂ j)).getLeft (by
    obtain ⟨p, hp, -⟩ := (glue_beta_eq_castAdd_iff e _ j).1 ((glue H₁ H₂ e).beta_betaPoint x _)
    simp [hp])

/-- The point of a generator of the glued diagram on the `β`-circle `j` of the second diagram, an
intersection point of the second diagram. -/
noncomputable def glueRightPoint (x : (glue H₁ H₂ e).Generator) (j : Fin g₂) : Point₂ :=
  ((glue H₁ H₂ e).betaPoint x (Fin.natAdd g₁ j)).getRight (by
    obtain ⟨p, hp, -⟩ := (glue_beta_eq_natAdd_iff e _ j).1 ((glue H₁ H₂ e).beta_betaPoint x _)
    simp [hp])

@[simp]
theorem inl_glueLeftPoint (x : (glue H₁ H₂ e).Generator) (j : Fin g₁) :
    .inl (glueLeftPoint e x j) = (glue H₁ H₂ e).betaPoint x (Fin.castAdd g₂ j) :=
  Sum.inl_getLeft _ _

@[simp]
theorem inr_glueRightPoint (x : (glue H₁ H₂ e).Generator) (j : Fin g₂) :
    .inr (glueRightPoint e x j) = (glue H₁ H₂ e).betaPoint x (Fin.natAdd g₁ j) :=
  Sum.inr_getRight _ _

theorem beta_glueLeftPoint (x : (glue H₁ H₂ e).Generator) (j : Fin g₁) :
    H₁.beta (glueLeftPoint e x j) = j := by
  obtain ⟨p, hp, rfl⟩ :=
    (glue_beta_eq_castAdd_iff e _ j).1 ((glue H₁ H₂ e).beta_betaPoint x _)
  rw [← inl_glueLeftPoint, Sum.inl.injEq] at hp
  rw [hp]

theorem beta_glueRightPoint (x : (glue H₁ H₂ e).Generator) (j : Fin g₂) :
    H₂.beta (glueRightPoint e x j) = j := by
  obtain ⟨p, hp, rfl⟩ :=
    (glue_beta_eq_natAdd_iff e _ j).1 ((glue H₁ H₂ e).beta_betaPoint x _)
  rw [← inr_glueRightPoint, Sum.inr.injEq] at hp
  rw [hp]

/-- The generator of the first diagram cut out of a generator of the glued diagram: its points on
the `β`-circles of the first diagram. -/
noncomputable def glueLeft (x : (glue H₁ H₂ e).Generator) : H₁.Generator where
  point := glueLeftPoint e x
  beta_point := beta_glueLeftPoint e x
  alpha_comp_point_injective i j hij := by
    have h : (glue H₁ H₂ e).alpha ((glue H₁ H₂ e).betaPoint x (Fin.castAdd g₂ i)) =
        (glue H₁ H₂ e).alpha ((glue H₁ H₂ e).betaPoint x (Fin.castAdd g₂ j)) := by
      rw [← inl_glueLeftPoint, ← inl_glueLeftPoint, glue_alpha_inl, glue_alpha_inl]
      exact congrArg (e ∘ glueCurveLeft) hij
    exact Fin.castAdd_injective _ _ (((glue H₁ H₂ e).alpha_comp_betaPoint_bijective x).1 h)
  exists_alpha_point_eq_inr c := by
    obtain ⟨j, hj⟩ := ((glue H₁ H₂ e).alpha_comp_betaPoint_bijective x).2 (e (.inl (.inl c)))
    have hβ := (glue H₁ H₂ e).beta_betaPoint x j
    rcases hq : (glue H₁ H₂ e).betaPoint x j with p | p <;>
      simp only [Function.comp_apply, hq, glue_alpha_inl, glue_alpha_inr, glue_beta_inl,
        glue_beta_inr, EmbeddingLike.apply_eq_iff_eq] at hj hβ
    · refine ⟨H₁.beta p, ?_⟩
      have hp : glueLeftPoint e x (H₁.beta p) = p := by
        apply Sum.inl_injective
        rw [inl_glueLeftPoint, hβ, hq]
      rw [hp]
      exact glueCurveLeft_injective (hj.trans (glueCurveLeft_inr c).symm)
    · rcases hp : H₂.alpha p with b | d <;> simp [hp] at hj

/-- The generator of the second diagram cut out of a generator of the glued diagram: its points on
the `β`-circles of the second diagram. -/
noncomputable def glueRight (x : (glue H₁ H₂ e).Generator) : H₂.Generator where
  point := glueRightPoint e x
  beta_point := beta_glueRightPoint e x
  alpha_comp_point_injective i j hij := by
    have h : (glue H₁ H₂ e).alpha ((glue H₁ H₂ e).betaPoint x (Fin.natAdd g₁ i)) =
        (glue H₁ H₂ e).alpha ((glue H₁ H₂ e).betaPoint x (Fin.natAdd g₁ j)) := by
      rw [← inr_glueRightPoint, ← inr_glueRightPoint, glue_alpha_inr, glue_alpha_inr]
      exact congrArg (e ∘ glueCurveRight) hij
    exact Fin.natAdd_injective _ _ (((glue H₁ H₂ e).alpha_comp_betaPoint_bijective x).1 h)
  exists_alpha_point_eq_inr c := by
    obtain ⟨j, hj⟩ := ((glue H₁ H₂ e).alpha_comp_betaPoint_bijective x).2 (e (.inl (.inr c)))
    have hβ := (glue H₁ H₂ e).beta_betaPoint x j
    rcases hq : (glue H₁ H₂ e).betaPoint x j with p | p <;>
      simp only [Function.comp_apply, hq, glue_alpha_inl, glue_alpha_inr, glue_beta_inl,
        glue_beta_inr, EmbeddingLike.apply_eq_iff_eq] at hj hβ
    · rcases hp : H₁.alpha p with b | d <;> simp [hp] at hj
    · refine ⟨H₂.beta p, ?_⟩
      have hp : glueRightPoint e x (H₂.beta p) = p := by
        apply Sum.inr_injective
        rw [inr_glueRightPoint, hβ, hq]
      rw [hp]
      exact glueCurveRight_injective (hj.trans (glueCurveRight_inr c).symm)

@[simp]
theorem glueLeft_point (x : (glue H₁ H₂ e).Generator) :
    (glueLeft e x).point = glueLeftPoint e x :=
  (rfl)

@[simp]
theorem glueRight_point (x : (glue H₁ H₂ e).Generator) :
    (glueRight e x).point = glueRightPoint e x :=
  (rfl)

/-- A generator of the glued diagram consists of the points of the two generators cut out of it. -/
theorem gluePoint_glueLeft_glueRight (x : (glue H₁ H₂ e).Generator) :
    gluePoint (glueLeft e x) (glueRight e x) = (glue H₁ H₂ e).betaPoint x := by
  ext j
  obtain ⟨j, rfl⟩ := finSumFinEquiv.surjective j
  cases j <;> simp

theorem glueLeft_generatorOfBetaPoint (x₁ : H₁.Generator) (x₂ : H₂.Generator)
    (hα : Function.Bijective ((glue H₁ H₂ e).alpha ∘ gluePoint x₁ x₂)) :
    glueLeft e ((glue H₁ H₂ e).generatorOfBetaPoint (gluePoint x₁ x₂)
      (glue_beta_gluePoint e x₁ x₂) hα) = x₁ := by
  ext j
  apply Sum.inl_injective (β := Point₂)
  simp

theorem glueRight_generatorOfBetaPoint (x₁ : H₁.Generator) (x₂ : H₂.Generator)
    (hα : Function.Bijective ((glue H₁ H₂ e).alpha ∘ gluePoint x₁ x₂)) :
    glueRight e ((glue H₁ H₂ e).generatorOfBetaPoint (gluePoint x₁ x₂)
      (glue_beta_gluePoint e x₁ x₂) hα) = x₂ := by
  ext j
  apply Sum.inr_injective (α := Point₁)
  simp

variable [Fintype Arc] [DecidableEq Arc]

/-- **The generators of a glued diagram.** The generators of the closed diagram `H₁ ∪ H₂` are the
pairs of generators of `H₁` and of `H₂` whose occupancies are complementary: a generator of
`H₁ ∪ H₂` has one point on each `α`-circle made of two arcs, lying on one of the two arcs. -/
noncomputable def glueGeneratorEquiv :
    (glue H₁ H₂ e).Generator ≃
      {x : H₁.Generator × H₂.Generator // H₁.occupied x.1 = (H₂.occupied x.2)ᶜ} where
  toFun x := ⟨(glueLeft e x, glueRight e x),
    (glue_alpha_comp_gluePoint_bijective_iff e _ _).1 (by
      rw [gluePoint_glueLeft_glueRight]
      exact (glue H₁ H₂ e).alpha_comp_betaPoint_bijective x)⟩
  invFun x := (glue H₁ H₂ e).generatorOfBetaPoint (gluePoint x.1.1 x.1.2)
    (glue_beta_gluePoint e _ _) ((glue_alpha_comp_gluePoint_bijective_iff e _ _).2 x.2)
  left_inv x := (glue H₁ H₂ e).betaPoint_injective (by simp [gluePoint_glueLeft_glueRight])
  right_inv x := Subtype.ext (Prod.ext (glueLeft_generatorOfBetaPoint e _ _ _)
    (glueRight_generatorOfBetaPoint e _ _ _))

@[simp]
theorem coe_glueGeneratorEquiv (x : (glue H₁ H₂ e).Generator) :
    (glueGeneratorEquiv e x : H₁.Generator × H₂.Generator) = (glueLeft e x, glueRight e x) :=
  (rfl)

/-- The points of the generator of the glued diagram given by a pair of generators. -/
@[simp]
theorem betaPoint_glueGeneratorEquiv_symm
    (x : {x : H₁.Generator × H₂.Generator // H₁.occupied x.1 = (H₂.occupied x.2)ᶜ}) :
    (glue H₁ H₂ e).betaPoint ((glueGeneratorEquiv e).symm x) = gluePoint x.1.1 x.1.2 :=
  (glue H₁ H₂ e).betaPoint_generatorOfBetaPoint _ _ _

/-- **The generators of a glued diagram are those of the box tensor product.** When every arc has
an end and the coefficients are nontrivial, the generators of `H₁ ∪ H₂` are the pairs of
generators `x₁` of `H₁` and `x₂` of `H₂` with `I_A(x₁) I_D(x₂) ≠ 0`, which index the generators
`x₁ ⊗ x₂` of the box tensor product of the type `A` module of `H₁` with the type `D` structure of
`H₂` over the idempotents. -/
noncomputable def glueGeneratorEquivTypeAIdem (R : Type*) [CommSemiring R] [Nontrivial R]
    {α : Type*} [LinearOrder α] [Fintype α] {M : α → Arc} (hM : Function.Surjective M) :
    (glue H₁ H₂ e).Generator ≃
      {x : H₁.Generator × H₂.Generator // H₁.typeAIdem R M x.1 * H₂.typeDIdem R M x.2 ≠ 0} :=
  (glueGeneratorEquiv e).trans
    (Equiv.subtypeEquivRight fun _ ↦ (typeAIdem_mul_typeDIdem_ne_zero_iff H₁ R M H₂ hM _ _).symm)

@[simp]
theorem coe_glueGeneratorEquivTypeAIdem (R : Type*) [CommSemiring R] [Nontrivial R]
    {α : Type*} [LinearOrder α] [Fintype α] {M : α → Arc} (hM : Function.Surjective M)
    (x : (glue H₁ H₂ e).Generator) :
    (glueGeneratorEquivTypeAIdem e R hM x : H₁.Generator × H₂.Generator) =
      (glueLeft e x, glueRight e x) :=
  (rfl)

/-- The points of the generator of the glued diagram given by a pair of generators `x₁`, `x₂`
with `I_A(x₁) I_D(x₂) ≠ 0`. -/
@[simp]
theorem betaPoint_glueGeneratorEquivTypeAIdem_symm (R : Type*) [CommSemiring R] [Nontrivial R]
    {α : Type*} [LinearOrder α] [Fintype α] {M : α → Arc} (hM : Function.Surjective M)
    (x : {x : H₁.Generator × H₂.Generator // H₁.typeAIdem R M x.1 * H₂.typeDIdem R M x.2 ≠ 0}) :
    (glue H₁ H₂ e).betaPoint ((glueGeneratorEquivTypeAIdem e R hM).symm x) =
      gluePoint x.1.1 x.1.2 :=
  (glue H₁ H₂ e).betaPoint_generatorOfBetaPoint _ _ _

end Glue

end BorderedHeegaardIntersectionSystem

/-! ### Gluing two genus-one diagrams

In the genus-one intersection data `oneArc a`, with two `α`-arcs, no `α`-circle and one
`β`-circle, the `β`-circle meets the arc `a` in one point and the other arc not at all; this is the
intersection pattern of the standard bordered diagrams of a solid torus. Its only generator
occupies `{a}`. Gluing two such diagrams along their boundaries gives a closed diagram of genus
two whose two `α`-circles are made of the matching arcs. If the two `β`-circles meet different
arcs the glued diagram has exactly one generator; if they meet the same arc it has none.
-/

section Examples

open BorderedHeegaardIntersectionSystem

/-- The genus-one intersection data in which the `β`-circle meets the arc `a` once and the other
arc not at all. -/
private abbrev oneArc (a : Fin 2) : BorderedHeegaardIntersectionSystem 1 (Fin 2) Empty Unit :=
  ⟨fun _ ↦ .inl a, fun _ ↦ 0⟩

private def oneArcGenerator (a : Fin 2) : (oneArc a).Generator :=
  ⟨fun _ ↦ (), fun _ ↦ Subsingleton.elim _ _, fun i j _ ↦ Subsingleton.elim i j, fun c ↦ c.elim⟩

private theorem eq_oneArcGenerator {a : Fin 2} (x : (oneArc a).Generator) :
    x = oneArcGenerator a :=
  Generator.ext (funext fun _ ↦ rfl)

private theorem occupied_oneArc {a : Fin 2} (x : (oneArc a).Generator) :
    (oneArc a).occupied x = {a} := by
  ext b
  simp [eq_comm]

/-- The numbering of the two `α`-circles of a glued genus-two diagram by the two arcs. -/
private def twoArcs : (Empty ⊕ Empty) ⊕ Fin 2 ≃ Fin (1 + 1) :=
  Equiv.emptySum _ _

/-- The `β`-circles meet different arcs: the glued diagram has exactly one generator. -/
example : Nat.card (glue (oneArc 0) (oneArc 1) twoArcs).Generator = 1 := by
  rw [Nat.card_congr (glueGeneratorEquiv twoArcs), Nat.card_eq_one_iff_exists]
  refine ⟨⟨(oneArcGenerator 0, oneArcGenerator 1), ?_⟩, fun y ↦ ?_⟩
  · rw [occupied_oneArc, occupied_oneArc]
    decide
  · exact Subtype.ext (Prod.ext (eq_oneArcGenerator _) (eq_oneArcGenerator _))

/-- The `β`-circles meet the same arc: the glued diagram has no generator. -/
example : IsEmpty (glue (oneArc 0) (oneArc 0) twoArcs).Generator := by
  rw [(glueGeneratorEquiv twoArcs).isEmpty_congr]
  refine ⟨fun ⟨x, hx⟩ ↦ ?_⟩
  rw [occupied_oneArc, occupied_oneArc] at hx
  exact absurd hx (by decide)

end Examples

end TauCeti
