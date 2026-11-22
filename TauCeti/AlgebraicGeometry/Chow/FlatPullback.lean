/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Chow.OpenRestriction
public import TauCeti.AlgebraicGeometry.Fibers.GenericPoint
public import TauCeti.AlgebraicGeometry.Morphisms.PureRelativeDimension
public import TauCeti.AlgebraicGeometry.Scheme.BaseAlgebra
import TauCeti.AlgebraicGeometry.Fibers.Dimension

/-!
# Pullback of cycles along morphisms of pure relative dimension

Let `f : X ⟶ Y` be a morphism of schemes. The pullback of a cycle `α = Σ n_y [y]` on `Y` is the
cycle on `X` whose coefficient at `x` is `n_{f x} · m_f(x)`. The multiplicity `m_f(x)` is, at a
generic point `x` of its fibre (`AlgebraicGeometry.Scheme.Hom.IsFiberGenericPoint`), the length
`length_{O_{X,x}} (O_{X,x} / m_{f x} O_{X,x})` of the local ring of the fibre, read in `ℕ` (so `0`
if that length is infinite; it is finite when `X` is locally Noetherian), and `0` at the other
points. Thus `f^*[V] = Σ_ξ m_f(ξ) [ξ]`, the sum over the generic points `ξ` of the fibre of `f`
over the generic point of `V`.

Let `f` be a morphism over a field `k`, of pure relative dimension `n`, between schemes locally of
finite type over `k`. A generic point `x` of a fibre satisfies `dim {x}⁻ = dim {f x}⁻ + n`
(`TauCeti.AlgebraicGeometry.height_eq_height_add_of_isFiberGenericPoint`), so the pullback sends
`m`-cycles to `(m + n)`-cycles. When `f` is moreover flat, the generic points of the fibre over the
generic point of `V` are those of the components of `f⁻¹(V)`, all of dimension `dim V + n`, and
this is the flat pullback `f^*[V] = [f⁻¹(V)]_{dim V + n}` of
[Stacks, Section 42.14](https://stacks.math.columbia.edu/tag/02RA) and Fulton, *Intersection
Theory*, §1.7.

## Main definitions and results

* `Chow.flatPullbackMultiplicity f x`: the multiplicity `m_f(x)`.
* `Chow.cyclePullback f`: the pullback `AlgebraicCycle Y ℤ →+ AlgebraicCycle X ℤ`, for `X` locally
  Noetherian.
* `Chow.cyclesFlatPullback k f n`: for `f` over a field `k`, of pure relative dimension `n`,
  between schemes locally of finite type over `k`, the pullback `Z_m(Y) →+ Z_{m+n}(X)` of
  `m`-cycles.
* `Chow.coe_cyclesFlatPullback_eq_coe_cyclesRestrict`: along an open immersion, of pure relative
  dimension zero, the pullback is the restriction `Chow.cyclesRestrict`; the multiplicities are
  then one (`Chow.flatPullbackMultiplicity_eq_one_of_isOpenImmersion`).
-/

public section

open AlgebraicGeometry CategoryTheory Limits Order Topology TopologicalSpace

universe u

namespace TauCeti.AlgebraicGeometry

namespace Chow

section Pullback

variable {X Y : Scheme.{u}}

open scoped Classical in
/-- The multiplicity of the pullback of cycles along `f : X ⟶ Y` at `x`: for `x` a generic point
of its fibre, the length `length_{O_{X,x}} (O_{X,x} / m_{f x} O_{X,x})` of the local ring of the
fibre at `x`, read in `ℕ` through `ENat.toNat` (so `0` if the length is infinite; it is finite and
positive when `X` is locally Noetherian); zero at the other points. -/
noncomputable def flatPullbackMultiplicity (f : X ⟶ Y) (x : X) : ℕ :=
  if f.IsFiberGenericPoint x then
    (Module.length (X.presheaf.stalk x) (X.presheaf.stalk x ⧸
      (IsLocalRing.maximalIdeal (Y.presheaf.stalk (f x))).map (f.stalkMap x).hom)).toNat
  else 0

/-- At a generic point of its fibre, the multiplicity is the length of the local ring of the
fibre, through `ENat.toNat`. -/
lemma flatPullbackMultiplicity_of_isFiberGenericPoint (f : X ⟶ Y) {x : X}
    (hx : f.IsFiberGenericPoint x) :
    flatPullbackMultiplicity f x =
      (Module.length (X.presheaf.stalk x) (X.presheaf.stalk x ⧸
        (IsLocalRing.maximalIdeal (Y.presheaf.stalk (f x))).map (f.stalkMap x).hom)).toNat := by
  simp only [flatPullbackMultiplicity, hx, ↓reduceIte]

/-- At a point which is not a generic point of its fibre, the multiplicity is zero. -/
@[simp]
lemma flatPullbackMultiplicity_of_not_isFiberGenericPoint (f : X ⟶ Y) {x : X}
    (hx : ¬ f.IsFiberGenericPoint x) : flatPullbackMultiplicity f x = 0 := by
  simp only [flatPullbackMultiplicity, hx, ↓reduceIte]

/-- A point with nonzero multiplicity is a generic point of its fibre. -/
lemma isFiberGenericPoint_of_flatPullbackMultiplicity_ne_zero (f : X ⟶ Y) {x : X}
    (hx : flatPullbackMultiplicity f x ≠ 0) : f.IsFiberGenericPoint x := by
  by_contra h
  exact hx (flatPullbackMultiplicity_of_not_isFiberGenericPoint f h)

/-- Along an open immersion every multiplicity is one. -/
@[simp]
lemma flatPullbackMultiplicity_eq_one_of_isOpenImmersion (f : X ⟶ Y) [IsOpenImmersion f]
    (x : X) : flatPullbackMultiplicity f x = 1 := by
  -- The fibre over `f x` is the single point `x`, and the stalk map is an isomorphism, so the
  -- local ring of the fibre is the residue field.
  rw [flatPullbackMultiplicity_of_isFiberGenericPoint f
    (f.isFiberGenericPoint_of_injective f.isOpenEmbedding.injective x)]
  have hmap : (IsLocalRing.maximalIdeal (Y.presheaf.stalk (f x))).map (f.stalkMap x).hom =
      IsLocalRing.maximalIdeal (X.presheaf.stalk x) :=
    IsLocalRing.eq_maximalIdeal
      (Ideal.map_isMaximal_of_equiv (asIso (f.stalkMap x)).commRingCatIsoToRingEquiv)
  have : IsSimpleModule (X.presheaf.stalk x)
      (X.presheaf.stalk x ⧸ IsLocalRing.maximalIdeal (X.presheaf.stalk x)) :=
    isSimpleModule_iff_isCoatom.mpr (Ideal.isMaximal_def.mp inferInstance)
  rw [hmap, Module.length_eq_one]
  rfl

/-- For `X` locally Noetherian, the pullback `f^* α`, with coefficient `α (f x) · m_f(x)` at `x`,
has locally finite support. -/
private lemma locallyFiniteSupport_mul_flatPullbackMultiplicity [IsLocallyNoetherian X]
    (f : X ⟶ Y) (α : AlgebraicCycle Y ℤ) :
    LocallyFiniteSupport fun x ↦ α (f x) * flatPullbackMultiplicity f x := by
  -- An affine open `U` of `X` has compact image, which meets the support of `α` in finitely many
  -- points, and `U` contains finitely many generic points of each fibre.
  intro z
  obtain ⟨_, ⟨U, hU, rfl⟩, hzU, -⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ z) isOpen_univ
  have : IsNoetherianRing Γ(X, U) := IsLocallyNoetherian.component_noetherian ⟨U, hU⟩
  have : NoetherianSpace (U : Set X) := noetherianSpace_of_isAffineOpen U hU
  refine ⟨U, U.isOpen.mem_nhds hzU, ?_⟩
  have hF : (f '' (U : Set X) ∩ Function.support α).Finite :=
    (Function.locallyFinsupp.locallyFiniteSupport α).finite_inter_support_of_isCompact
      (hU.isCompact.image f.continuous)
  refine (hF.biUnion fun y _ ↦
    f.finite_setOf_mem_and_apply_eq_and_isFiberGenericPoint U.isOpen y).subset ?_
  rintro x ⟨hxU, hx⟩
  have hm : flatPullbackMultiplicity f x ≠ 0 := by exact_mod_cast right_ne_zero_of_mul hx
  exact Set.mem_biUnion (x := f x) ⟨⟨x, hxU, rfl⟩, left_ne_zero_of_mul hx⟩
    ⟨hxU, rfl, isFiberGenericPoint_of_flatPullbackMultiplicity_ne_zero f hm⟩

/-- The pullback of cycles along `f : X ⟶ Y`, for `X` locally Noetherian: the coefficient of
`f^* α` at `x` is `α (f x) · m_f(x)`, so `f^*[y] = Σ m_f(x) [x]` over the generic points `x` of
the fibre over `y`. For `f` flat of constant relative dimension between schemes locally of finite
type over a field, this is the flat pullback of
[Stacks, Section 42.14](https://stacks.math.columbia.edu/tag/02RA). -/
noncomputable def cyclePullback [IsLocallyNoetherian X] (f : X ⟶ Y) :
    AlgebraicCycle Y ℤ →+ AlgebraicCycle X ℤ where
  toFun α :=
    { toFun x := α (f x) * flatPullbackMultiplicity f x
      supportWithinDomain' := Set.subset_univ _
      supportLocallyFiniteWithinDomain' z _ :=
        locallyFiniteSupport_mul_flatPullbackMultiplicity f α z }
  map_zero' := by
    ext x
    exact zero_mul _
  map_add' α β := by
    ext x
    exact add_mul _ _ _

/-- The coefficient of a pullback at `x` is the coefficient at `f x` times the multiplicity. -/
@[simp]
lemma cyclePullback_apply [IsLocallyNoetherian X] (f : X ⟶ Y) (α : AlgebraicCycle Y ℤ) (x : X) :
    cyclePullback f α x = α (f x) * flatPullbackMultiplicity f x :=
  (rfl)

/-- Along an open immersion, the pullback of cycles is the restriction `α ↦ α ∘ f`. -/
lemma cyclePullback_eq_comap_of_isOpenImmersion [IsLocallyNoetherian X] (f : X ⟶ Y)
    [IsOpenImmersion f] (α : AlgebraicCycle Y ℤ) :
    cyclePullback f α =
      Function.locallyFinsupp.comap f f.continuous f.isOpenEmbedding.injective α := by
  ext x
  rw [cyclePullback_apply, flatPullbackMultiplicity_eq_one_of_isOpenImmersion, Nat.cast_one,
    mul_one, Function.locallyFinsupp.comap_apply]

/-- Pulling back along the identity does nothing. -/
@[simp]
lemma cyclePullback_id [IsLocallyNoetherian X] : cyclePullback (𝟙 X) = AddMonoidHom.id _ := by
  ext α x
  simp

end Pullback

section OverField

variable (k : Type u) [Field k] {X Y : Scheme.{u}} [X.Over (Spec (.of k))]
  [Y.Over (Spec (.of k))] [LocallyOfFiniteType (X ↘ Spec (.of k))]
  [LocallyOfFiniteType (Y ↘ Spec (.of k))]

/-- For a morphism `f` over a field `k`, of pure relative dimension `n`, between schemes locally of
finite type over `k`, the pullback sends `m`-cycles to `(m + n)`-cycles. -/
lemma cyclePullback_mem_cyclesOfDimension [IsLocallyNoetherian X] (f : X ⟶ Y)
    [f.IsOver (Spec (.of k))] (n : ℕ) [PureRelativeDimension n f] {m : ℤ}
    {α : AlgebraicCycle Y ℤ} (hα : α ∈ cyclesOfDimension Y m) :
    cyclePullback f α ∈ cyclesOfDimension X (m + n) := by
  rw [mem_cyclesOfDimension_iff]
  intro x hx
  rw [Function.mem_support, cyclePullback_apply] at hx
  obtain ⟨j, hj, rfl⟩ :=
    mem_pointsOfDimension.mp (mem_cyclesOfDimension_iff.mp hα (left_ne_zero_of_mul hx))
  -- A generic point of a fibre over a point of dimension `m` has dimension `m + n`.
  have hg := isFiberGenericPoint_of_flatPullbackMultiplicity_ne_zero f
    (by exact_mod_cast right_ne_zero_of_mul hx)
  refine mem_pointsOfDimension.mpr ⟨j + n, ?_, by push_cast; rfl⟩
  rw [height_eq_height_add_of_isFiberGenericPoint k f n hg, hj]
  push_cast
  rfl

/-- The pullback `Z_m(Y) →+ Z_{m+n}(X)` of `m`-cycles along a morphism `f` of pure relative
dimension `n` between schemes locally of finite type over a field `k`:
`f^*[V] = Σ_ξ m_f(ξ) [ξ]` over the generic points `ξ` of the fibre over the generic point of `V`.
For `f` flat this is the flat pullback `f^*[V] = [f⁻¹(V)]_{m+n}` of
[Stacks, Section 42.14](https://stacks.math.columbia.edu/tag/02RA) and Fulton, *Intersection
Theory*, §1.7. -/
noncomputable def cyclesFlatPullback (f : X ⟶ Y) [f.IsOver (Spec (.of k))] (n : ℕ)
    [PureRelativeDimension n f] {m : ℤ} :
    cyclesOfDimension Y m →+ cyclesOfDimension X (m + n) :=
  letI := LocallyOfFiniteType.isLocallyNoetherian (X ↘ Spec (.of k))
  AddMonoidHom.mk'
    (fun α ↦ ⟨cyclePullback f α, cyclePullback_mem_cyclesOfDimension k f n α.property⟩)
    fun _ _ ↦ Subtype.ext (map_add _ _ _)

variable {k}

/-- The coefficient of a pullback of `m`-cycles at `x` is the coefficient at `f x` times the
multiplicity. -/
@[simp]
lemma cyclesFlatPullback_apply (f : X ⟶ Y) [f.IsOver (Spec (.of k))] (n : ℕ)
    [PureRelativeDimension n f] {m : ℤ} (α : cyclesOfDimension Y m) (x : X) :
    (cyclesFlatPullback k f n α : AlgebraicCycle X ℤ) x =
      (α : AlgebraicCycle Y ℤ) (f x) * flatPullbackMultiplicity f x :=
  (rfl)

/-- The pullback of `m`-cycles is the pullback of the underlying cycles. -/
lemma coe_cyclesFlatPullback [IsLocallyNoetherian X] (f : X ⟶ Y) [f.IsOver (Spec (.of k))]
    (n : ℕ) [PureRelativeDimension n f] {m : ℤ} (α : cyclesOfDimension Y m) :
    (cyclesFlatPullback k f n α : AlgebraicCycle X ℤ) = cyclePullback f (α : AlgebraicCycle Y ℤ) :=
  (rfl)

/-- Along an open immersion, of pure relative dimension zero, the pullback of `m`-cycles is the
restriction `Chow.cyclesRestrict`. -/
lemma coe_cyclesFlatPullback_eq_coe_cyclesRestrict (j : X ⟶ Y) [IsOpenImmersion j]
    [j.IsOver (Spec (.of k))] {m : ℤ} (α : cyclesOfDimension Y m) :
    (cyclesFlatPullback k j 0 α : AlgebraicCycle X ℤ) =
      (cyclesRestrict k j α : AlgebraicCycle X ℤ) := by
  have := LocallyOfFiniteType.isLocallyNoetherian (X ↘ Spec (.of k))
  rw [coe_cyclesFlatPullback, cyclePullback_eq_comap_of_isOpenImmersion]
  refine Function.locallyFinsuppWithin.ext fun x ↦ ?_
  rw [cyclesRestrict_apply, Function.locallyFinsupp.comap_apply]

end OverField

end Chow

end TauCeti.AlgebraicGeometry
