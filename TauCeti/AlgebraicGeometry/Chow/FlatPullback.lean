/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Chow.OpenRestriction
public import TauCeti.AlgebraicGeometry.AlgebraicCycle.Pullback
public import TauCeti.AlgebraicGeometry.Morphisms.PureRelativeDimension
public import TauCeti.AlgebraicGeometry.Scheme.BaseAlgebra
import TauCeti.AlgebraicGeometry.Fibers.Dimension

/-!
# Pullback of cycles along morphisms of pure relative dimension

Let `f` be a morphism over a field `k`, of pure relative dimension `n`, between schemes locally of
finite type over `k`. A generic point `x` of a fibre satisfies `dim {x}⁻ = dim {f x}⁻ + n`
(`TauCeti.AlgebraicGeometry.height_eq_height_add_of_isFiberGenericPoint`), so the pullback of
cycles `AlgebraicGeometry.AlgebraicCycle.pullback f`, whose coefficient at `x` is `n_{f x} · m_f(x)`
with `m_f(x)` supported on the generic points of the fibres, sends `m`-cycles to `(m + n)`-cycles.
When `f` is moreover flat, the generic points of the fibre over the generic point of `V` are those
of the components of `f⁻¹(V)`, all of dimension `dim V + n`, and this is the flat pullback
`f^*[V] = [f⁻¹(V)]_{dim V + n}` of
[Stacks, Section 42.14](https://stacks.math.columbia.edu/tag/02RA) and Fulton, *Intersection
Theory*, §1.7.

## Main definitions and results

* `Chow.cyclesPullback k f n`: for `f` over a field `k`, of pure relative dimension `n`,
  between schemes locally of finite type over `k`, the pullback `Z_m(Y) →+ Z_{m+n}(X)` of
  `m`-cycles. Flatness is not assumed; for `f` flat this is the flat pullback.
* `Chow.coe_cyclesPullback_eq_coe_cyclesRestrict`: along an open immersion, of pure relative
  dimension zero, the pullback is the restriction `Chow.cyclesRestrict`; in particular
  `Chow.coe_cyclesPullback_id`.
-/

public section

open AlgebraicGeometry CategoryTheory Limits Order Topology TopologicalSpace

universe u

namespace TauCeti.AlgebraicGeometry

namespace Chow

section OverField

variable (k : Type u) [Field k] {X Y : Scheme.{u}} [X.Over (Spec (.of k))]
  [Y.Over (Spec (.of k))] [LocallyOfFiniteType (X ↘ Spec (.of k))]
  [LocallyOfFiniteType (Y ↘ Spec (.of k))]

/-- For a morphism `f` over a field `k`, of pure relative dimension `n`, between schemes locally of
finite type over `k`, the pullback sends `m`-cycles to `(m + n)`-cycles. -/
lemma pullback_mem_cyclesOfDimension [IsLocallyNoetherian X] (f : X ⟶ Y)
    [f.IsOver (Spec (.of k))] (n : ℕ) [PureRelativeDimension n f] {m : ℤ}
    {α : AlgebraicCycle Y ℤ} (hα : α ∈ cyclesOfDimension Y m) :
    AlgebraicCycle.pullback f α ∈ cyclesOfDimension X (m + n) := by
  rw [mem_cyclesOfDimension_iff]
  intro x hx
  rw [Function.mem_support, AlgebraicCycle.pullback_apply] at hx
  obtain ⟨j, hj, rfl⟩ :=
    mem_pointsOfDimension.mp (mem_cyclesOfDimension_iff.mp hα (left_ne_zero_of_mul hx))
  -- A generic point of a fibre over a point of dimension `m` has dimension `m + n`.
  have hg := AlgebraicCycle.isFiberGenericPoint_of_pullbackMultiplicity_ne_zero f
    (by exact_mod_cast right_ne_zero_of_mul hx)
  refine mem_pointsOfDimension.mpr ⟨j + n, ?_, by push_cast; ring⟩
  rw [height_eq_height_add_of_isFiberGenericPoint k f n hg, hj]
  norm_cast

/-- The pullback `Z_m(Y) →+ Z_{m+n}(X)` of `m`-cycles along a morphism `f` of pure relative
dimension `n` between schemes locally of finite type over a field `k`:
`f^*[V] = Σ_ξ m_f(ξ) [ξ]` over the generic points `ξ` of the fibre over the generic point of `V`.
For `f` flat this is the flat pullback `f^*[V] = [f⁻¹(V)]_{m+n}` of
[Stacks, Section 42.14](https://stacks.math.columbia.edu/tag/02RA) and Fulton, *Intersection
Theory*, §1.7. -/
noncomputable def cyclesPullback (f : X ⟶ Y) [f.IsOver (Spec (.of k))] (n : ℕ)
    [PureRelativeDimension n f] {m : ℤ} :
    cyclesOfDimension Y m →+ cyclesOfDimension X (m + n) :=
  letI := LocallyOfFiniteType.isLocallyNoetherian (X ↘ Spec (.of k))
  AddMonoidHom.mk'
    (fun α ↦ ⟨AlgebraicCycle.pullback f α, pullback_mem_cyclesOfDimension k f n α.property⟩)
    fun _ _ ↦ Subtype.ext (map_add _ _ _)

variable {k}

/-- The coefficient of a pullback of `m`-cycles at `x` is the coefficient at `f x` times the
multiplicity. -/
@[simp]
lemma cyclesPullback_apply (f : X ⟶ Y) [f.IsOver (Spec (.of k))] (n : ℕ)
    [PureRelativeDimension n f] {m : ℤ} (α : cyclesOfDimension Y m) (x : X) :
    (cyclesPullback k f n α : AlgebraicCycle X ℤ) x =
      (α : AlgebraicCycle Y ℤ) (f x) * AlgebraicCycle.pullbackMultiplicity f x :=
  letI := LocallyOfFiniteType.isLocallyNoetherian (X ↘ Spec (.of k))
  AlgebraicCycle.pullback_apply f _ x

/-- The pullback of `m`-cycles is the pullback of the underlying cycles. -/
lemma coe_cyclesPullback [IsLocallyNoetherian X] (f : X ⟶ Y) [f.IsOver (Spec (.of k))]
    (n : ℕ) [PureRelativeDimension n f] {m : ℤ} (α : cyclesOfDimension Y m) :
    (cyclesPullback k f n α : AlgebraicCycle X ℤ) =
      AlgebraicCycle.pullback f (α : AlgebraicCycle Y ℤ) :=
  (rfl)

/-- Along an open immersion, of pure relative dimension zero, the pullback of `m`-cycles is the
restriction `Chow.cyclesRestrict`. -/
lemma coe_cyclesPullback_eq_coe_cyclesRestrict (j : X ⟶ Y) [IsOpenImmersion j]
    [j.IsOver (Spec (.of k))] {m : ℤ} (α : cyclesOfDimension Y m) :
    (cyclesPullback k j 0 α : AlgebraicCycle X ℤ) =
      (cyclesRestrict k j α : AlgebraicCycle X ℤ) := by
  have := LocallyOfFiniteType.isLocallyNoetherian (X ↘ Spec (.of k))
  rw [coe_cyclesPullback, AlgebraicCycle.pullback_eq_comap_of_isOpenImmersion]
  refine Function.locallyFinsuppWithin.ext fun x ↦ ?_
  rw [cyclesRestrict_apply, Function.locallyFinsupp.comap_apply]

/-- Pulling back `m`-cycles along the identity does nothing. This is not a simp lemma: `simp`
rewrites the cast `((0 : ℕ) : ℤ)` in the dimension `m + 0` of its left-hand side. -/
lemma coe_cyclesPullback_id {m : ℤ} (α : cyclesOfDimension X m) :
    (cyclesPullback k (𝟙 X) 0 α : AlgebraicCycle X ℤ) = (α : AlgebraicCycle X ℤ) := by
  rw [coe_cyclesPullback_eq_coe_cyclesRestrict, cyclesRestrict_id, AddMonoidHom.id_apply]

end OverField

end Chow

end TauCeti.AlgebraicGeometry
