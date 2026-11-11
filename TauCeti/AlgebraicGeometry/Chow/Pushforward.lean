/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.AlgebraicCycle.OverField
public import TauCeti.AlgebraicGeometry.Chow.ClosedImmersion

/-!
# Pushforward of cycles over a field

Let `k` be a field and `f : X ⟶ Y` a quasi-compact morphism of schemes locally of finite type over
`k`, over `Spec k`. Mathlib's pushforward of algebraic cycles `AlgebraicCycle.map f height height`
sends the cycle `[V]` of an integral closed subscheme `V ⊆ X` to `[κ(V) : κ(f(V))] [f(V)]` when
`f(V)` has the dimension of `V`, and to `0` otherwise. Over a field the dimension condition is
automatic: when `κ(V)` is finite over `κ(f(V))`, both have the same transcendence degree over `k`
(`TauCeti.AlgebraicGeometry.height_apply_eq_height_of_residueDegree_ne_zero`), so the
multiplicity is just the residue degree (`AlgebraicCycle.mapCoeff_height_eq_residueDegree`), and
the pushforward sends `n`-cycles to `n`-cycles (`Chow.map_height_mem_cyclesOfDimension`). This
makes the pushforward of `k`-cycles functorial, and compatible with degrees of zero-cycles
([Stacks, Sections 42.12 and 42.41](https://stacks.math.columbia.edu/tag/02R3); Fulton,
*Intersection Theory*, §1.4).

* `Chow.cyclesMap k f`: the pushforward `Z_n(X) →+ Z_n(Y)` of `n`-cycles, with
  `Chow.cyclesMap_id` and `Chow.cyclesMap_comp`.
* `Chow.cyclesDegree k X`: the degree `Z_0(X) →+ ℤ`, `Σ n_x [x] ↦ Σ n_x [κ(x) : k]`, of
  zero-cycles on a quasi-compact `X` (Mathlib's `AlgebraicCycle.degree` of the structure
  morphism), with `Chow.cyclesDegree_cyclesMap`: `deg f_* α = deg α`, the case of zero-cycles of
  `AlgebraicCycle.degree_map_height`.
-/

public section

open AlgebraicGeometry Order CategoryTheory

universe u

namespace TauCeti.AlgebraicGeometry.Chow

variable (k : Type u) [Field k] {X Y Z : Scheme.{u}}
  [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))] [Z.Over (Spec (.of k))]
  [LocallyOfFiniteType (X ↘ Spec (.of k))] [LocallyOfFiniteType (Y ↘ Spec (.of k))]
  [LocallyOfFiniteType (Z ↘ Spec (.of k))]

/-- Over a field, Mathlib's pushforward of cycles with height weights sends `n`-cycles to
`n`-cycles: a point with finite residue extension has the dimension of its image. -/
lemma map_height_mem_cyclesOfDimension (f : X ⟶ Y) [f.IsOver (Spec (.of k))] [QuasiCompact f]
    {n : ℤ} {α : AlgebraicCycle X ℤ} (hα : α ∈ cyclesOfDimension X n) :
    AlgebraicCycle.map f height height α ∈ cyclesOfDimension Y n := by
  rw [mem_cyclesOfDimension_iff]
  intro y hy
  rw [Function.mem_support, AlgebraicCycle.map_height_apply k] at hy
  obtain ⟨x, hxy, hx⟩ := exists_ne_zero_of_finsum_mem_ne_zero hy
  rw [Set.mem_preimage, Set.mem_singleton_iff] at hxy
  have hd : f.residueDegree x ≠ 0 := by exact_mod_cast right_ne_zero_of_mul hx
  have hx' := mem_cyclesOfDimension_iff.mp hα (left_ne_zero_of_mul hx)
  rw [← hxy]
  simpa only [mem_pointsOfDimension,
    height_apply_eq_height_of_residueDegree_ne_zero k f hd] using hx'

/-- The pushforward of `n`-cycles along a quasi-compact morphism over a field: Mathlib's
pushforward of cycles with height weights, `[V] ↦ [κ(V) : κ(f(V))] [f(V)]`. -/
noncomputable def cyclesMap (f : X ⟶ Y) [f.IsOver (Spec (.of k))] [QuasiCompact f] {n : ℤ} :
    cyclesOfDimension X n →+ cyclesOfDimension Y n :=
  AddMonoidHom.mk' (fun α ↦ ⟨AlgebraicCycle.map f height height (α : AlgebraicCycle X ℤ),
      map_height_mem_cyclesOfDimension k f α.2⟩)
    fun _ _ ↦ Subtype.ext (AlgebraicCycle.map_add _ _ _ _ _)

variable {k}

/-- The underlying cycle of a pushforward is Mathlib's pushforward with height weights. -/
lemma coe_cyclesMap (f : X ⟶ Y) [f.IsOver (Spec (.of k))] [QuasiCompact f] {n : ℤ}
    (α : cyclesOfDimension X n) :
    (cyclesMap k f α : AlgebraicCycle Y ℤ) =
      AlgebraicCycle.map f height height (α : AlgebraicCycle X ℤ) :=
  (rfl)

/-- The coefficient of a pushforward at `y` is the sum of the coefficients at the points over `y`,
weighted by the residue degrees. -/
lemma cyclesMap_apply (f : X ⟶ Y) [f.IsOver (Spec (.of k))] [QuasiCompact f] {n : ℤ}
    (α : cyclesOfDimension X n) (y : Y) :
    (cyclesMap k f α : AlgebraicCycle Y ℤ) y =
      ∑ᶠ x ∈ f ⁻¹' {y}, (α : AlgebraicCycle X ℤ) x * f.residueDegree x :=
  AlgebraicCycle.map_height_apply k f _ y

variable (k)

/-- The pushforward of cycles along the identity is the identity. -/
@[simp]
lemma cyclesMap_id {n : ℤ} :
    cyclesMap k (𝟙 X) (n := n) = AddMonoidHom.id _ := by
  ext α : 2
  exact AlgebraicCycle.map_id _ _

/-- The pushforward of cycles is functorial: `(g ∘ f)_* = g_* f_*`. -/
lemma cyclesMap_comp (f : X ⟶ Y) (g : Y ⟶ Z) [f.IsOver (Spec (.of k))]
    [g.IsOver (Spec (.of k))] [QuasiCompact f] [QuasiCompact g] {n : ℤ} :
    cyclesMap k (f ≫ g) (n := n) = (cyclesMap k g).comp (cyclesMap k f) := by
  ext α : 2
  exact AlgebraicCycle.map_height_comp k f g _

/-- Along a closed immersion over `k`, the pushforward of cycles is the closed-immersion
pushforward `Chow.cyclesPushforward`, which transports coefficients. -/
lemma cyclesMap_eq_cyclesPushforward (i : X ⟶ Y) [i.IsOver (Spec (.of k))] [IsClosedImmersion i]
    {n : ℤ} : cyclesMap k i (n := n) = cyclesPushforward i := by
  ext α : 2
  rw [coe_cyclesMap, coe_cyclesPushforward]

section Degree

variable (X) [CompactSpace X]

omit [LocallyOfFiniteType (X ↘ Spec (.of k))] in
/-- The degree `Σ n_x [x] ↦ Σ n_x [κ(x) : k]` of zero-cycles on a quasi-compact scheme over a field
`k`: Mathlib's degree of cycles along the structure morphism. -/
noncomputable def cyclesDegree : cyclesOfDimension X 0 →+ ℤ :=
  (AlgebraicCycle.degree (X ↘ Spec (.of k))).comp (cyclesOfDimension X 0).subtype

variable {X}

omit [LocallyOfFiniteType (X ↘ Spec (.of k))] in
/-- The degree of a zero-cycle is the sum of its coefficients weighted by the degrees of the
residue fields. -/
lemma cyclesDegree_apply (α : cyclesOfDimension X 0) :
    cyclesDegree k X α =
      ∑ᶠ x, (X ↘ Spec (.of k)).residueDegree x • (α : AlgebraicCycle X ℤ) x :=
  AlgebraicCycle.degree_apply _ _

/-- Pushforward along a morphism over `k` of quasi-compact schemes preserves the degree of
zero-cycles. -/
@[simp]
lemma cyclesDegree_cyclesMap [CompactSpace Y] (f : X ⟶ Y) [f.IsOver (Spec (.of k))]
    [QuasiCompact f] (α : cyclesOfDimension X 0) :
    cyclesDegree k Y (cyclesMap k f α) = cyclesDegree k X α :=
  AlgebraicCycle.degree_map_height k f (α : AlgebraicCycle X ℤ)

end Degree

end TauCeti.AlgebraicGeometry.Chow
