/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.AlgebraicGeometry.Fiber
public import TauCeti.AlgebraicGeometry.Fibers.GenericPoint
public import TauCeti.AlgebraicGeometry.Morphisms.PureRelativeDimension
public import TauCeti.AlgebraicGeometry.Scheme.BaseAlgebra
import TauCeti.AlgebraicGeometry.ResidueField
import TauCeti.AlgebraicGeometry.Scheme.LocalDimension
import TauCeti.Topology.Sober

/-!
# Codimension inside closed subsets and fibres of an affine scheme

For a point `x` of `Spec A`, its codimension inside the closed subset `V(I)` is the height of its
image in `A ⧸ I`. For a ring map `φ : R ⟶ S`, the generizations of a point of `Spec S` in its
fibre over `Spec R` are exactly its generizations in `V(q S)`, where `q` is the prime of `R`
below it, so the codimension in the fibre is the height of its image in `S ⧸ q S`.

## Main declarations

* `TauCeti.AlgebraicGeometry.coheight_zeroLocus_eq_height_map`: the codimension of a point of
  `Spec A` inside `V(I)` is the height of its image in `A ⧸ I`.
* `TauCeti.AlgebraicGeometry.coheight_fiber_eq_height_map`: the codimension of a point in its
  fibre over `Spec R` is the height of its image in `S ⧸ q S`.
* `TauCeti.AlgebraicGeometry.height_eq_height_add_of_isFiberGenericPoint`: for a morphism `f` of
  pure relative dimension `n` between schemes locally of finite type over a field `k`, a generic
  point `x` of its fibre satisfies `dim {x}⁻ = dim {f x}⁻ + n`.
-/

public section

open CategoryTheory Order Topology TopologicalSpace AlgebraicGeometry

universe u

namespace TauCeti.AlgebraicGeometry

/-- In `Spec A`, the codimension of a point `x` of the closed subset `V(I)`, written as
`{y | I ≤ y.asIdeal}`, inside `V(I)` is the height of the image of `x` in `A ⧸ I`. -/
theorem coheight_zeroLocus_eq_height_map {A : CommRingCat.{u}} (I : Ideal A) (x : Spec A)
    (hx : I ≤ x.asIdeal) :
    coheight (⟨x, hx⟩ : {y : Spec A | I ≤ y.asIdeal}) =
      (x.asIdeal.map (Ideal.Quotient.mk I)).height := by
  let e : {y : Spec A | I ≤ y.asIdeal} ≃o (PrimeSpectrum.zeroLocus (R := A) I)ᵒᵈ :=
    { toEquiv := (Equiv.refl _).trans OrderDual.toDual
      map_rel_iff' := fun {a b} ↦ PrimeSpectrum.le_iff_specializes b.val a.val }
  rw [← coheight_orderIso e, ← height_ofDual,
    ← height_orderIso I.primeSpectrumQuotientOrderIsoZeroLocus.symm,
    ← PrimeSpectrum.height_eq_orderHeight]
  congr 1

/-- In `Spec S`, for a ring map `φ : R ⟶ S`, the codimension of a point `x` in its fibre
`{v | Spec.map φ v = Spec.map φ x}` is the height of its image in `S ⧸ q S`, where `q` is the prime
of `R` below `x`: the generizations of `x` in the fibre are exactly its generizations in
`V(q S)`. -/
theorem coheight_fiber_eq_height_map {R S : CommRingCat.{u}} (φ : R ⟶ S) (x : Spec S) :
    coheight (⟨x, rfl⟩ : {v : Spec S | Spec.map φ v = Spec.map φ x}) =
      (x.asIdeal.map (Ideal.Quotient.mk ((Spec.map φ x).asIdeal.map φ.hom))).height := by
  let T : Set (Spec S) := {v | Spec.map φ v = Spec.map φ x}
  let I : Ideal S := (Spec.map φ x).asIdeal.map φ.hom
  have hTI {v : Spec S} (hv : v ∈ T) : I ≤ v.asIdeal :=
    Ideal.map_le_iff_le_comap.mpr (congrArg PrimeSpectrum.asIdeal hv).ge
  have hTup {v v' : Spec S} (hv : v ∈ T) (hvv' : v ≤ v') (hv' : I ≤ v'.asIdeal) : v' ∈ T := by
    have hle : v'.asIdeal ≤ v.asIdeal := (PrimeSpectrum.le_iff_specializes _ _).mpr hvv'
    refine PrimeSpectrum.ext (le_antisymm ?_ (Ideal.map_le_iff_le_comap.mp hv'))
    rw [← hv]
    exact Ideal.comap_mono hle
  rw [← coheight_zeroLocus_eq_height_map I x (hTI rfl)]
  exact coheight_eq_of_strictMono
    (fun v : T ↦ (⟨v, hTI v.property⟩ : {v : Spec S | I ≤ v.asIdeal})) (fun _ _ h ↦ h)
    (fun v b h ↦ ⟨⟨b, hTup v.property h.le b.property⟩, h, rfl⟩) ⟨x, rfl⟩

end TauCeti.AlgebraicGeometry

namespace AlgebraicGeometry.Scheme.Hom

open TauCeti TauCeti.AlgebraicGeometry

variable {X Y : Scheme.{u}}

/-- The closure of a generic point `x` of its fibre under a morphism `f` of pure relative
dimension `n`, taken in the scheme-theoretic fibre, has dimension `n`: it is an irreducible
component of the fibre. -/
theorem topologicalKrullDim_closure_singleton_asFiber_of_isFiberGenericPoint
    (f : X ⟶ Y) (n : ℕ) [PureRelativeDimension n f] {x : X} (hx : f.IsFiberGenericPoint x) :
    topologicalKrullDim (closure ({f.asFiber x} : Set (f.fiber (f x)))) = n := by
  have h : f.fiberHomeo (f x) (f.asFiber x) = ⟨x, rfl⟩ := Subtype.ext (f.fiberι_asFiber x)
  refine isPureDimensional_iff.mp (PureRelativeDimension.isPureDimensional_fiber f (f x)) _ ?_
  -- `irreducibleComponents` membership of a point closure is, by definition of `genericPoints`,
  -- membership of the point in `genericPoints`.
  change f.asFiber x ∈ genericPoints (f.fiber (f x))
  rw [← (f.fiberHomeo (f x)).isOpenEmbedding.mem_genericPoints_iff, h]
  exact (f.isFiberGenericPoint_iff x).mp hx

end AlgebraicGeometry.Scheme.Hom

namespace TauCeti.AlgebraicGeometry

open CategoryTheory.Limits

section GenericPointDimension

variable (k : Type u) [Field k] {X Y : Scheme.{u}} [X.Over (Spec (.of k))]
  [Y.Over (Spec (.of k))]

variable [LocallyOfFiniteType (X ↘ Spec (.of k))]

variable [LocallyOfFiniteType (Y ↘ Spec (.of k))]

/-- **Dimension of a generic point of a fibre.** Let `f : X ⟶ Y` be a morphism of pure relative
dimension `n` between schemes locally of finite type over a field `k`. If `x` is the generic point
of an irreducible component of its fibre, then the closure of `x` has dimension that of the
closure of `f x` plus `n`. The residue fields satisfy
`trdeg_k κ(x) = trdeg_k κ(f x) + trdeg_{κ(f x)} κ(x)`, and the last term is the dimension of the
closure of `x` in the fibre, an irreducible component of the fibre. -/
theorem height_eq_height_add_of_isFiberGenericPoint (f : X ⟶ Y) [f.IsOver (Spec (.of k))]
    (n : ℕ) [PureRelativeDimension n f] {x : X} (hx : f.IsFiberGenericPoint x) :
    height x = height (f x) + n := by
  have hdim := f.topologicalKrullDim_closure_singleton_asFiber_of_isFiberGenericPoint n hx
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
    -- The structure morphisms chosen above are `p`, `g ≫ Y ↘ Spec k` and `fiberι y ≫ X ↘ Spec k`;
    -- `change` unfolds `↘` and `IsOver` to these composites.
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
  rw [e1, e2, ← (f.fiberι y).trdeg_residueField_eq_of_isIso_residueFieldMap x',
    trdeg_residueField_eq_add_of_over K x', g.trdeg_residueField_eq_of_isIso_residueFieldMap,
    Cardinal.toNat_add (trdeg_residueField_lt_aleph0 k _) (trdeg_residueField_lt_aleph0 K x'), hn]
  push_cast
  rfl

end GenericPointDimension

end TauCeti.AlgebraicGeometry

end
