/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Chow.OpenRestriction
public import TauCeti.AlgebraicGeometry.Morphisms.PureRelativeDimension
public import TauCeti.AlgebraicGeometry.Scheme.BaseAlgebra
import Mathlib.AlgebraicGeometry.Fiber
import Mathlib.FieldTheory.FinTrdeg
import TauCeti.AlgebraicGeometry.ResidueField
import TauCeti.AlgebraicGeometry.Scheme.LocalDimension
import TauCeti.Topology.Sober

/-!
# Pullback of cycles along morphisms of pure relative dimension

Let `f : X ⟶ Y` be a morphism of schemes. A point `x ∈ X` is a *generic point of its fibre*
(`TauCeti.AlgebraicGeometry.IsFiberGenericPoint f x`) when it is the generic point of an
irreducible component of the fibre `f⁻¹(f x)`. The pullback of a cycle `α = Σ n_y [y]` on `Y` is
the cycle on `X` whose coefficient at `x` is `n_{f x} · m_f(x)`, where the multiplicity
`m_f(x) = length_{O_{X,x}} (O_{X,x} / m_{f x} O_{X,x})` is the length of the local ring of the
fibre at a generic point `x` of the fibre, and `m_f(x) = 0` at the other points. Thus
`f^*[V] = Σ_ξ m_f(ξ) [ξ]`, the sum over the generic points `ξ` of the fibre of `f` over the generic
point of `V`, with the multiplicities of the components of `f⁻¹(V)`. When `f` is flat of relative
dimension `n` over a field, these are exactly the components of `f⁻¹(V)` of dimension
`dim V + n`, and this is the flat pullback `f^*[V] = [f⁻¹(V)]_{k+n}` of
[Stacks, Section 42.14](https://stacks.math.columbia.edu/tag/02RA) and Fulton, *Intersection
Theory*, §1.7.

Over a field `k`, a generic point `x` of a fibre of a morphism `f` of pure relative dimension `n`
satisfies `dim {x}⁻ = dim {f x}⁻ + n`
(`TauCeti.AlgebraicGeometry.height_eq_height_add_of_isFiberGenericPoint`): the transcendence
degree of `κ(x)` over `k` is that of `κ(f x)` plus that of `κ(x)` over `κ(f x)`, and the latter
is the dimension of the closure of `x` in the fibre, an irreducible component of dimension `n`.
So the pullback sends `m`-cycles to `(m + n)`-cycles.

## Main definitions and results

* `TauCeti.AlgebraicGeometry.IsFiberGenericPoint f x`: `x` is the generic point of an irreducible
  component of its fibre.
* `TauCeti.AlgebraicGeometry.height_eq_height_add_of_isFiberGenericPoint`: over a field, for `f`
  of pure relative dimension `n` and `x` a generic point of its fibre,
  `height x = height (f x) + n`.
* `Chow.flatPullbackMultiplicity f x`: the multiplicity `m_f(x)`.
* `Chow.cyclePullback f`: the pullback `AlgebraicCycle Y ℤ →+ AlgebraicCycle X ℤ`, for `X` locally
  Noetherian. Local finiteness holds because an affine open of `X` meets only finitely many
  fibres over the support of a cycle, and only finitely many generic points of each.
* `Chow.cyclesFlatPullback k f n`: over a field `k`, for `f` of pure relative dimension `n`, the
  pullback `Z_m(Y) →+ Z_{m+n}(X)` of `m`-cycles.
* `Chow.coe_cyclesFlatPullback_eq_coe_cyclesRestrict`: along an open immersion, of pure relative
  dimension zero, the pullback is the restriction `Chow.cyclesRestrict`; the multiplicities are
  then one (`Chow.flatPullbackMultiplicity_eq_one_of_isOpenImmersion`).
-/

public section

open AlgebraicGeometry CategoryTheory Limits Order Topology TopologicalSpace

universe u

namespace TauCeti.AlgebraicGeometry

section Fiber

variable {X Y : Scheme.{u}}

/-- A point `x` of `X` is a generic point of its fibre under `f : X ⟶ Y` when it is the generic
point of an irreducible component of the fibre `f⁻¹(f x)`. -/
def IsFiberGenericPoint (f : X ⟶ Y) (x : X) : Prop :=
  (⟨x, rfl⟩ : f ⁻¹' {f x}) ∈ genericPoints (f ⁻¹' {f x})

/-- Unfolding `IsFiberGenericPoint`. -/
lemma isFiberGenericPoint_iff (f : X ⟶ Y) (x : X) :
    IsFiberGenericPoint f x ↔ (⟨x, rfl⟩ : f ⁻¹' {f x}) ∈ genericPoints (f ⁻¹' {f x}) :=
  Iff.rfl

/-- For a morphism injective on points every fibre has at most one point, which is its generic
point. -/
lemma isFiberGenericPoint_of_injective (f : X ⟶ Y) (hf : Function.Injective f) (x : X) :
    IsFiberGenericPoint f x := by
  have : Subsingleton (f ⁻¹' {f x}) := ⟨fun a b ↦ Subtype.ext (hf (a.2.trans b.2.symm))⟩
  have : IrreducibleSpace (f ⁻¹' {f x}) :=
    { isPreirreducible_univ := Set.subsingleton_univ.isPreirreducible
      toNonempty := ⟨⟨x, rfl⟩⟩ }
  rw [isFiberGenericPoint_iff, genericPoints, Set.mem_ofPred_eq,
    irreducibleComponents_eq_singleton, Set.mem_singleton_iff]
  exact Set.eq_univ_of_forall fun b ↦ Subsingleton.elim (⟨x, rfl⟩ : f ⁻¹' {f x}) b ▸
    subset_closure rfl

/-- An open subset `U` of `X` that is a Noetherian space contains only finitely many generic
points of the fibre of `f` over a given point. -/
lemma finite_setOf_isFiberGenericPoint (f : X ⟶ Y) {U : Set X} (hU : IsOpen U)
    [NoetherianSpace U] (y : Y) :
    {x | x ∈ U ∧ f x = y ∧ IsFiberGenericPoint f x}.Finite := by
  let V : Set (f ⁻¹' {y}) := Subtype.val ⁻¹' U
  have hV : IsOpen V := hU.preimage continuous_subtype_val
  -- `V` is the part of the fibre in `U`, a subspace of the Noetherian space `U`.
  have : NoetherianSpace V :=
    ((IsInducing.subtypeVal.comp IsInducing.subtypeVal).codRestrict
      (s := U) fun v ↦ v.2).noetherianSpace
  refine ((genericPoints.finite NoetherianSpace.finite_irreducibleComponents).image
    fun v : V ↦ (v : f ⁻¹' {y}).1).subset ?_
  rintro x ⟨hxU, rfl, hx⟩
  exact ⟨⟨⟨x, rfl⟩, hxU⟩,
    (hV.isOpenEmbedding_subtypeVal.mem_genericPoints_iff (⟨⟨x, rfl⟩, hxU⟩ : V)).mp hx, rfl⟩

end Fiber

section Dimension

variable (k : Type u) [Field k] {X Y : Scheme.{u}} [X.Over (Spec (.of k))]
  [Y.Over (Spec (.of k))]

/-- On a scheme locally of finite type over a field `k`, every residue field has finite
transcendence degree over `k`. -/
theorem trdeg_residueField_lt_aleph0 [LocallyOfFiniteType (X ↘ Spec (.of k))] (x : X) :
    Algebra.trdeg k (X.residueField x) < Cardinal.aleph0 := by
  obtain ⟨R, g, _, y, φ, hφ, rfl, hR⟩ := (X ↘ Spec (.of k)).exists_isOpenImmersion_finiteType x
  let := φ.hom.toAlgebra
  have : Algebra.FiniteType k R := hR
  have := y.isPrime
  rw [(g.residueFieldAlgEquivOfIsOpenImmersion φ hφ y).trdeg_eq]
  have : Algebra.EssFiniteType k y.asIdeal.ResidueField := .comp k R _
  exact trdeg_lt_aleph0 k _

variable {k} in
/-- A morphism over `Spec k` inducing an isomorphism of residue fields at `x` preserves the
transcendence degree of the residue field over `k`. -/
theorem trdeg_residueField_eq_of_isIso (f : X ⟶ Y) [f.IsOver (Spec (.of k))] (x : X)
    [IsIso (f.residueFieldMap x)] :
    Algebra.trdeg k (X.residueField x) = Algebra.trdeg k (Y.residueField (f x)) := by
  let e : Y.residueField (f x) ≃+* X.residueField x :=
    (asIso (f.residueFieldMap x)).commRingCatIsoToRingEquiv
  exact (AlgEquiv.ofRingEquiv (f := e) fun c ↦ f.residueFieldMap_algebraMap k x c).trdeg_eq.symm

variable {k} in
/-- **Transcendence degree over a point.** Let `F` be a scheme over a field `K`, through
`p : F ⟶ Spec K`, with `p` a morphism over a field `k`. Then for every point `z` of `F`,
`trdeg_k κ(z) = trdeg_k κ(p z) + trdeg_K κ(z)`, where `κ(p z)` is the residue field of the point
of `Spec K`, algebraic over `K`. -/
theorem trdeg_residueField_eq_add_of_over (K : Type u) [Field K] {F : Scheme.{u}}
    [F.Over (Spec (.of k))] [F.Over (Spec (.of K))] [(Spec (.of K)).Over (Spec (.of k))]
    [(F ↘ Spec (.of K)).IsOver (Spec (.of k))] (z : F) :
    Algebra.trdeg k (F.residueField z) =
      Algebra.trdeg k ((Spec (.of K)).residueField ((F ↘ Spec (.of K)) z)) +
        Algebra.trdeg K (F.residueField z) := by
  let p := F ↘ Spec (.of K)
  let _ : (Spec (.of K)).Over (Spec (.of K)) := ⟨𝟙 _⟩
  have : p.IsOver (Spec (.of K)) := ⟨Category.comp_id _⟩
  have : LocallyOfFiniteType ((Spec (.of K)) ↘ Spec (.of K)) :=
    inferInstanceAs (LocallyOfFiniteType (𝟙 _))
  -- The towers `k → L → κ(z)` and `K → L → κ(z)`, with `L` the residue field of `Spec K`.
  let L := (Spec (.of K)).residueField (p z)
  let : Algebra L (F.residueField z) := (p.residueFieldMap z).hom.toAlgebra
  have : IsScalarTower K L (F.residueField z) :=
    IsScalarTower.of_algebraMap_eq fun c ↦ (p.residueFieldMap_algebraMap K z c).symm
  have : IsScalarTower k L (F.residueField z) :=
    IsScalarTower.of_algebraMap_eq fun c ↦ (p.residueFieldMap_algebraMap k z c).symm
  -- `L` has height zero in `Spec K`, so it is algebraic over `K`.
  have hKL : Algebra.trdeg K L = 0 := by
    have h0 := height_eq_toNat_trdeg_residueField K (p z)
    rw [Order.height_eq_zero.mpr (Subsingleton.isMin _)] at h0
    exact (Cardinal.toNat_eq_zero.mp (by exact_mod_cast h0.symm)).resolve_right
      (not_le.mpr (trdeg_residueField_lt_aleph0 K (p z)))
  rw [← trdeg_add_eq k L, ← trdeg_add_eq K L, hKL, zero_add]

variable [LocallyOfFiniteType (X ↘ Spec (.of k))]

/-- The closure of a generic point `x` of its fibre under a morphism `f` of pure relative
dimension `n`, taken in the scheme-theoretic fibre, has dimension `n`: it is an irreducible
component of the fibre. -/
theorem topologicalKrullDim_closure_asFiber (f : X ⟶ Y) (n : ℕ) [PureRelativeDimension n f]
    {x : X} (hx : IsFiberGenericPoint f x) :
    topologicalKrullDim (closure ({f.asFiber x} : Set (f.fiber (f x)))) = n := by
  have h : f.fiberHomeo (f x) (f.asFiber x) = ⟨x, rfl⟩ := Subtype.ext (f.fiberι_asFiber x)
  refine isPureDimensional_iff.mp (PureRelativeDimension.isPureDimensional_fiber f (f x)) _ ?_
  change f.asFiber x ∈ genericPoints (f.fiber (f x))
  rw [← (f.fiberHomeo (f x)).isOpenEmbedding.mem_genericPoints_iff, h]
  exact hx

variable [LocallyOfFiniteType (Y ↘ Spec (.of k))]

/-- **Dimension of a generic point of a fibre.** Let `f : X ⟶ Y` be a morphism of pure relative
dimension `n` between schemes locally of finite type over a field `k`. If `x` is the generic point
of an irreducible component of its fibre, then the closure of `x` has dimension that of the
closure of `f x` plus `n`. The residue fields satisfy
`trdeg_k κ(x) = trdeg_k κ(f x) + trdeg_{κ(f x)} κ(x)`, and the last term is the dimension of the
closure of `x` in the fibre, an irreducible component of the fibre. -/
theorem height_eq_height_add_of_isFiberGenericPoint (f : X ⟶ Y) [f.IsOver (Spec (.of k))]
    (n : ℕ) [PureRelativeDimension n f] {x : X} (hx : IsFiberGenericPoint f x) :
    height x = height (f x) + n := by
  have hdim := topologicalKrullDim_closure_asFiber f n hx
  set y := f x
  let K : Type u := Y.residueField y
  let F := f.fiber y
  let x' : F := f.asFiber x
  let p : F ⟶ Spec (.of K) := f.fiberToSpecResidueField y
  let g : Spec (.of K) ⟶ Y := Y.fromSpecResidueField y
  have : LocallyOfFiniteType f := by
    have : LocallyOfFiniteType (f ≫ Y ↘ Spec (.of k)) := by
      rw [comp_over]
      infer_instance
    exact locallyOfFiniteType_of_comp f (Y ↘ Spec (.of k))
  -- The fibre and `Spec κ(y)` lie over `k` through `X` and `Y`, and the fibre lies over `κ(y)`.
  let _ : F.Over (Spec (.of k)) := ⟨f.fiberι y ≫ X ↘ Spec (.of k)⟩
  let _ : (Spec (.of K)).Over (Spec (.of k)) := ⟨g ≫ Y ↘ Spec (.of k)⟩
  let _ : F.Over (Spec (.of K)) := ⟨p⟩
  have : (f.fiberι y).IsOver (Spec (.of k)) := ⟨rfl⟩
  have : g.IsOver (Spec (.of k)) := ⟨rfl⟩
  have : (F ↘ Spec (.of K)).IsOver (Spec (.of k)) := ⟨by
    change p ≫ g ≫ Y ↘ Spec (.of k) = f.fiberι y ≫ X ↘ Spec (.of k)
    rw [← comp_over f (Spec (.of k)), ← Category.assoc, ← Category.assoc]
    exact congrArg (· ≫ Y ↘ Spec (.of k)) (f.fiber_fac y).symm⟩
  have : LocallyOfFiniteType (F ↘ Spec (.of K)) :=
    inferInstanceAs (LocallyOfFiniteType (pullback.snd f (Y.fromSpecResidueField y)))
  -- The dimension `n` of the closure of `x'` in the fibre is `trdeg_{κ(y)} κ(x')`.
  rw [topologicalKrullDim_closure_singleton_eq_toNat_trdeg_residueField K x'] at hdim
  have hn : (Algebra.trdeg K (F.residueField x')).toNat = n := by exact_mod_cast hdim
  have e1 : height x = (Algebra.trdeg k (X.residueField (f.fiberι y x'))).toNat := by
    rw [← height_eq_toNat_trdeg_residueField k]
    exact congrArg height (f.fiberι_asFiber x).symm
  have e2 :
      height y = (Algebra.trdeg k (Y.residueField (g ((F ↘ Spec (.of K)) x')))).toNat := by
    rw [← height_eq_toNat_trdeg_residueField k]
    exact congrArg height (Y.fromSpecResidueField_apply y _).symm
  rw [e1, e2, ← trdeg_residueField_eq_of_isIso (f.fiberι y) x',
    trdeg_residueField_eq_add_of_over K x', trdeg_residueField_eq_of_isIso g,
    Cardinal.toNat_add (trdeg_residueField_lt_aleph0 k _) (trdeg_residueField_lt_aleph0 K x'), hn]
  push_cast
  rfl

end Dimension

namespace Chow

section Pullback

variable {X Y : Scheme.{u}}

open scoped Classical in
/-- The multiplicity of the pullback of cycles along `f : X ⟶ Y` at `x`: for `x` a generic point
of its fibre, the length `length_{O_{X,x}} (O_{X,x} / m_{f x} O_{X,x})` of the local ring of the
fibre at `x`; zero at the other points. -/
noncomputable def flatPullbackMultiplicity (f : X ⟶ Y) (x : X) : ℕ :=
  if IsFiberGenericPoint f x then
    (Module.length (X.presheaf.stalk x) (X.presheaf.stalk x ⧸
      (IsLocalRing.maximalIdeal (Y.presheaf.stalk (f x))).map (f.stalkMap x).hom)).toNat
  else 0

/-- At a generic point of its fibre, the multiplicity is the length of the local ring of the
fibre. -/
lemma flatPullbackMultiplicity_of_isFiberGenericPoint (f : X ⟶ Y) {x : X}
    (hx : IsFiberGenericPoint f x) :
    flatPullbackMultiplicity f x =
      (Module.length (X.presheaf.stalk x) (X.presheaf.stalk x ⧸
        (IsLocalRing.maximalIdeal (Y.presheaf.stalk (f x))).map (f.stalkMap x).hom)).toNat := by
  simp only [flatPullbackMultiplicity, hx, ↓reduceIte]

/-- A point with nonzero multiplicity is a generic point of its fibre. -/
lemma isFiberGenericPoint_of_flatPullbackMultiplicity_ne_zero (f : X ⟶ Y) {x : X}
    (hx : flatPullbackMultiplicity f x ≠ 0) : IsFiberGenericPoint f x := by
  by_contra h
  exact hx (by simp only [flatPullbackMultiplicity, h, ↓reduceIte])

/-- Along an open immersion every multiplicity is one: the fibre at `x` is the single point `x`,
and the stalk map is an isomorphism, so the local ring of the fibre is the residue field. -/
lemma flatPullbackMultiplicity_eq_one_of_isOpenImmersion (f : X ⟶ Y) [IsOpenImmersion f]
    (x : X) : flatPullbackMultiplicity f x = 1 := by
  rw [flatPullbackMultiplicity_of_isFiberGenericPoint f
    (isFiberGenericPoint_of_injective f f.isOpenEmbedding.injective x)]
  have hmap : (IsLocalRing.maximalIdeal (Y.presheaf.stalk (f x))).map (f.stalkMap x).hom =
      IsLocalRing.maximalIdeal (X.presheaf.stalk x) :=
    IsLocalRing.eq_maximalIdeal
      (Ideal.map_isMaximal_of_equiv (asIso (f.stalkMap x)).commRingCatIsoToRingEquiv)
  have : IsSimpleModule (X.presheaf.stalk x)
      (X.presheaf.stalk x ⧸ IsLocalRing.maximalIdeal (X.presheaf.stalk x)) :=
    isSimpleModule_iff_isCoatom.mpr (Ideal.isMaximal_def.mp inferInstance)
  rw [hmap, Module.length_eq_one]
  rfl

/-- The pullback `f^* α`, with coefficient `α (f x) · m_f(x)` at `x`, has locally finite support:
an affine open `U` of `X` has compact image, which meets the support of `α` in finitely many
points, and `U` contains finitely many generic points of each fibre. -/
lemma locallyFiniteSupport_cyclePullback [IsLocallyNoetherian X] (f : X ⟶ Y)
    (α : AlgebraicCycle Y ℤ) :
    LocallyFiniteSupport fun x ↦ α (f x) * flatPullbackMultiplicity f x := by
  intro z
  obtain ⟨_, ⟨U, hU, rfl⟩, hzU, -⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ z) isOpen_univ
  have : IsNoetherianRing Γ(X, U) := IsLocallyNoetherian.component_noetherian ⟨U, hU⟩
  have : NoetherianSpace (U : Set X) := noetherianSpace_of_isAffineOpen U hU
  refine ⟨U, U.isOpen.mem_nhds hzU, ?_⟩
  have hF : (f '' (U : Set X) ∩ Function.support α).Finite :=
    (Function.locallyFinsupp.locallyFiniteSupport α).finite_inter_support_of_isCompact
      (hU.isCompact.image f.continuous)
  refine (hF.biUnion fun y _ ↦ finite_setOf_isFiberGenericPoint f U.isOpen y).subset ?_
  rintro x ⟨hxU, hx⟩
  have hm : flatPullbackMultiplicity f x ≠ 0 := by exact_mod_cast right_ne_zero_of_mul hx
  exact Set.mem_biUnion (x := f x) ⟨⟨x, hxU, rfl⟩, left_ne_zero_of_mul hx⟩
    ⟨hxU, rfl, isFiberGenericPoint_of_flatPullbackMultiplicity_ne_zero f hm⟩

/-- The pullback of cycles along `f : X ⟶ Y`, for `X` locally Noetherian: the coefficient of
`f^* α` at `x` is `α (f x) · m_f(x)`, so `f^*[y] = Σ m_f(x) [x]` over the generic points `x` of
the fibre over `y`. For `f` flat this is the flat pullback of
[Stacks, Section 42.14](https://stacks.math.columbia.edu/tag/02RA). -/
noncomputable def cyclePullback [IsLocallyNoetherian X] (f : X ⟶ Y) :
    AlgebraicCycle Y ℤ →+ AlgebraicCycle X ℤ where
  toFun α :=
    { toFun x := α (f x) * flatPullbackMultiplicity f x
      supportWithinDomain' := Set.subset_univ _
      supportLocallyFiniteWithinDomain' z _ := locallyFiniteSupport_cyclePullback f α z }
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
lemma cyclePullback_of_isOpenImmersion [IsLocallyNoetherian X] (f : X ⟶ Y) [IsOpenImmersion f]
    (α : AlgebraicCycle Y ℤ) :
    cyclePullback f α =
      Function.locallyFinsupp.comap f f.continuous f.isOpenEmbedding.injective α := by
  ext x
  rw [cyclePullback_apply, flatPullbackMultiplicity_eq_one_of_isOpenImmersion, Nat.cast_one,
    mul_one, Function.locallyFinsupp.comap_apply]

end Pullback

section OverField

variable (k : Type u) [Field k] {X Y : Scheme.{u}} [X.Over (Spec (.of k))]
  [Y.Over (Spec (.of k))] [LocallyOfFiniteType (X ↘ Spec (.of k))]
  [LocallyOfFiniteType (Y ↘ Spec (.of k))]

/-- Over a field, the pullback along a morphism of pure relative dimension `n` sends `m`-cycles to
`(m + n)`-cycles: a generic point of a fibre over a point of dimension `m` has dimension
`m + n`. (`X` is locally Noetherian, being locally of finite type over `k`.) -/
lemma cyclePullback_mem_cyclesOfDimension [IsLocallyNoetherian X] (f : X ⟶ Y)
    [f.IsOver (Spec (.of k))] (n : ℕ) [PureRelativeDimension n f] {m : ℤ}
    {α : AlgebraicCycle Y ℤ} (hα : α ∈ cyclesOfDimension Y m) :
    cyclePullback f α ∈ cyclesOfDimension X (m + n) := by
  rw [mem_cyclesOfDimension_iff]
  intro x hx
  rw [Function.mem_support, cyclePullback_apply] at hx
  obtain ⟨j, hj, rfl⟩ :=
    mem_pointsOfDimension.mp (mem_cyclesOfDimension_iff.mp hα (left_ne_zero_of_mul hx))
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
  AddMonoidHom.mk' (fun α ↦ ⟨cyclePullback f α, cyclePullback_mem_cyclesOfDimension k f n α.2⟩)
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

/-- Along an open immersion, of pure relative dimension zero, the pullback of `m`-cycles is the
restriction `Chow.cyclesRestrict`. -/
lemma coe_cyclesFlatPullback_eq_coe_cyclesRestrict (j : X ⟶ Y) [IsOpenImmersion j]
    [j.IsOver (Spec (.of k))] {m : ℤ} (α : cyclesOfDimension Y m) :
    (cyclesFlatPullback k j 0 α : AlgebraicCycle X ℤ) =
      (cyclesRestrict k j α : AlgebraicCycle X ℤ) := by
  refine Function.locallyFinsuppWithin.ext fun x ↦ ?_
  rw [cyclesFlatPullback_apply, cyclesRestrict_apply,
    flatPullbackMultiplicity_eq_one_of_isOpenImmersion, Nat.cast_one, mul_one]

end OverField

end Chow

end TauCeti.AlgebraicGeometry
