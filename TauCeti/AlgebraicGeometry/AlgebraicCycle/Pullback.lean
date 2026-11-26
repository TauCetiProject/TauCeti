/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.AlgebraicCycle.Basic
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.RingTheory.Length
public import TauCeti.AlgebraicGeometry.Fibers.GenericPoint
public import TauCeti.Topology.LocallyFinsupp.Comap

/-!
# Pullback of algebraic cycles

Let `f : X ⟶ Y` be a morphism of schemes. The pullback of a cycle `α = Σ n_y [y]` on `Y` is the
cycle on `X` whose coefficient at `x` is `n_{f x} · m_f(x)`. The multiplicity `m_f(x)` is, at a
generic point `x` of its fibre (`AlgebraicGeometry.Scheme.Hom.IsFiberGenericPoint`), the length
`length_{O_{X,x}} (O_{X,x} / m_{f x} O_{X,x})` of the local ring of the fibre, read in `ℕ` (so `0`
if that length is infinite; it is finite when `X` is locally Noetherian), and `0` at the other
points. Thus `f^*[y] = Σ_x m_f(x) [x]`, the sum over the generic points `x` of the fibre of `f`
over `y`. For `f` flat of pure relative dimension between schemes locally of finite type over a
field, this is the flat pullback of
[Stacks, Section 42.14](https://stacks.math.columbia.edu/tag/02RA); the version on cycles of
fixed dimension is `TauCeti.AlgebraicGeometry.Chow.cyclesPullback`.

## Main definitions and results

* `AlgebraicGeometry.AlgebraicCycle.pullbackMultiplicity f x`: the multiplicity `m_f(x)`.
* `AlgebraicGeometry.AlgebraicCycle.pullback f`: the pullback
  `AlgebraicCycle Y R →+ AlgebraicCycle X R`, for `X` locally Noetherian.
* `AlgebraicGeometry.AlgebraicCycle.pullback_eq_comap_of_isOpenImmersion`: along an open
  immersion the multiplicities are one
  (`AlgebraicGeometry.AlgebraicCycle.pullbackMultiplicity_eq_one_of_isOpenImmersion`), and the
  pullback is the restriction `α ↦ α ∘ f`.
-/

public section

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry.AlgebraicCycle

variable {R : Type*} [Semiring R] {X Y : Scheme.{u}}

open scoped Classical in
/-- The multiplicity of the pullback of cycles along `f : X ⟶ Y` at `x`: for `x` a generic point
of its fibre, the length `length_{O_{X,x}} (O_{X,x} / m_{f x} O_{X,x})` of the local ring of the
fibre at `x`, read in `ℕ` through `ENat.toNat` (so `0` if the length is infinite; it is finite and
positive when `X` is locally Noetherian); zero at the other points. -/
noncomputable def pullbackMultiplicity (f : X ⟶ Y) (x : X) : ℕ :=
  if f.IsFiberGenericPoint x then
    (Module.length (X.presheaf.stalk x) (X.presheaf.stalk x ⧸
      (IsLocalRing.maximalIdeal (Y.presheaf.stalk (f x))).map (f.stalkMap x).hom)).toNat
  else 0

/-- At a generic point of its fibre, the multiplicity is the length of the local ring of the
fibre, through `ENat.toNat`. -/
lemma pullbackMultiplicity_of_isFiberGenericPoint (f : X ⟶ Y) {x : X}
    (hx : f.IsFiberGenericPoint x) :
    pullbackMultiplicity f x =
      (Module.length (X.presheaf.stalk x) (X.presheaf.stalk x ⧸
        (IsLocalRing.maximalIdeal (Y.presheaf.stalk (f x))).map (f.stalkMap x).hom)).toNat := by
  simp only [pullbackMultiplicity, hx, ↓reduceIte]

/-- At a point which is not a generic point of its fibre, the multiplicity is zero. -/
@[simp]
lemma pullbackMultiplicity_of_not_isFiberGenericPoint (f : X ⟶ Y) {x : X}
    (hx : ¬ f.IsFiberGenericPoint x) : pullbackMultiplicity f x = 0 := by
  simp only [pullbackMultiplicity, hx, ↓reduceIte]

/-- A point with nonzero multiplicity is a generic point of its fibre. -/
lemma isFiberGenericPoint_of_pullbackMultiplicity_ne_zero (f : X ⟶ Y) {x : X}
    (hx : pullbackMultiplicity f x ≠ 0) : f.IsFiberGenericPoint x := by
  by_contra h
  exact hx (pullbackMultiplicity_of_not_isFiberGenericPoint f h)

/-- Along an open immersion every multiplicity is one. -/
@[simp]
lemma pullbackMultiplicity_eq_one_of_isOpenImmersion (f : X ⟶ Y) [IsOpenImmersion f]
    (x : X) : pullbackMultiplicity f x = 1 := by
  -- The fibre over `f x` is the single point `x`, and the stalk map is an isomorphism, so the
  -- local ring of the fibre is the residue field.
  rw [pullbackMultiplicity_of_isFiberGenericPoint f (f.isFiberGenericPoint_of_isPreimmersion x)]
  have hmap : (IsLocalRing.maximalIdeal (Y.presheaf.stalk (f x))).map (f.stalkMap x).hom =
      IsLocalRing.maximalIdeal (X.presheaf.stalk x) :=
    IsLocalRing.eq_maximalIdeal
      (Ideal.map_isMaximal_of_equiv (asIso (f.stalkMap x)).commRingCatIsoToRingEquiv)
  have : IsSimpleModule (X.presheaf.stalk x)
      (X.presheaf.stalk x ⧸ IsLocalRing.maximalIdeal (X.presheaf.stalk x)) :=
    isSimpleModule_iff_isCoatom.mpr (Ideal.isMaximal_def.mp inferInstance)
  rw [hmap, Module.length_eq_one, ENat.toNat_one]

/-- For `X` locally Noetherian, the pullback `f^* α`, with coefficient `α (f x) · m_f(x)` at `x`,
has locally finite support. -/
private lemma locallyFiniteSupport_mul_pullbackMultiplicity [IsLocallyNoetherian X]
    (f : X ⟶ Y) (α : AlgebraicCycle Y R) :
    LocallyFiniteSupport fun x ↦ α (f x) * pullbackMultiplicity f x := by
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
  have hm : pullbackMultiplicity f x ≠ 0 := fun h ↦
    right_ne_zero_of_mul hx (by rw [h, Nat.cast_zero])
  exact Set.mem_biUnion (x := f x) ⟨⟨x, hxU, rfl⟩, left_ne_zero_of_mul hx⟩
    ⟨hxU, rfl, isFiberGenericPoint_of_pullbackMultiplicity_ne_zero f hm⟩

/-- The pullback of cycles along `f : X ⟶ Y`, for `X` locally Noetherian: the coefficient of
`f^* α` at `x` is `α (f x) · m_f(x)`, so `f^*[y] = Σ m_f(x) [x]` over the generic points `x` of
the fibre over `y`. For `f` flat of constant relative dimension between schemes locally of finite
type over a field, this is the flat pullback of
[Stacks, Section 42.14](https://stacks.math.columbia.edu/tag/02RA). -/
noncomputable def pullback [IsLocallyNoetherian X] (f : X ⟶ Y) :
    AlgebraicCycle Y R →+ AlgebraicCycle X R where
  toFun α :=
    { toFun x := α (f x) * pullbackMultiplicity f x
      supportWithinDomain' := Set.subset_univ _
      supportLocallyFiniteWithinDomain' z _ :=
        locallyFiniteSupport_mul_pullbackMultiplicity f α z }
  map_zero' := by
    ext x
    exact zero_mul _
  map_add' α β := by
    ext x
    exact add_mul _ _ _

/-- The coefficient of a pullback at `x` is the coefficient at `f x` times the multiplicity. -/
@[simp]
lemma pullback_apply [IsLocallyNoetherian X] (f : X ⟶ Y) (α : AlgebraicCycle Y R) (x : X) :
    pullback f α x = α (f x) * pullbackMultiplicity f x :=
  (rfl)

/-- Along an open immersion, the pullback of cycles is the restriction `α ↦ α ∘ f`. -/
lemma pullback_eq_comap_of_isOpenImmersion [IsLocallyNoetherian X] (f : X ⟶ Y)
    [IsOpenImmersion f] (α : AlgebraicCycle Y R) :
    pullback f α =
      Function.locallyFinsupp.comap f f.continuous f.isOpenEmbedding.injective α := by
  ext x
  rw [pullback_apply, pullbackMultiplicity_eq_one_of_isOpenImmersion, Nat.cast_one,
    mul_one, Function.locallyFinsupp.comap_apply]

/-- Pulling back along the identity does nothing. -/
@[simp]
lemma pullback_id [IsLocallyNoetherian X] :
    pullback (R := R) (𝟙 X) = AddMonoidHom.id _ := by
  ext α x
  simp

end AlgebraicGeometry.AlgebraicCycle
