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
# Dimensions of points and fibres

For a point `x` of `Spec A`, its codimension inside the closed subset `V(I)` is the height of its
image in `A ⧸ I`. For a ring map `φ : R ⟶ S`, the generizations of a point of `Spec S` in its
fibre over `Spec R` are exactly its generizations in `V(q S)`, where `q` is the prime of `R`
below it, so the codimension in the fibre is the height of its image in `S ⧸ q S`.

Globally, for a morphism `f : X ⟶ Y` over a field `k` between schemes locally of finite type over
`k`, the closure of a point `x` satisfies `dim {x}⁻ = dim {f x}⁻ + dim {x}⁻_F`, the last closure
taken in the scheme-theoretic fibre `F` of `f` over `f x`; this comes from additivity of
transcendence degrees of residue fields. When `f` has pure relative dimension `n` and `x` is a
generic point of its fibre, the last term is `n`. This gives the dimension shift of the pullback of
algebraic cycles, `TauCeti.AlgebraicGeometry.Chow.cyclesPullback`.

## Main declarations

* `TauCeti.AlgebraicGeometry.coheight_zeroLocus_eq_height_map`: the codimension of a point of
  `Spec A` inside `V(I)` is the height of its image in `A ⧸ I`.
* `TauCeti.AlgebraicGeometry.coheight_fiber_eq_height_map`: the codimension of a point in its
  fibre over `Spec R` is the height of its image in `S ⧸ q S`.
* `Scheme.Hom.topologicalKrullDim_closure_singleton_asFiber_of_isFiberGenericPoint`:
  if the fibre of `f` over `f x` is pure-dimensional of dimension `n`, the closure in that fibre
  of a generic point `x` of the fibre has dimension `n`.
* `TauCeti.AlgebraicGeometry.height_eq_height_add_height_asFiber`: for a morphism `f` over a
  field `k` between schemes locally of finite type over `k`, every point `x` satisfies
  `dim {x}⁻ = dim {f x}⁻ + dim {x}⁻_F`, the last closure taken in the fibre `F` of `f` over `f x`.
* `TauCeti.AlgebraicGeometry.height_eq_height_add_of_isFiberGenericPoint`: if moreover `f` has
  pure relative dimension `n`, a generic point `x` of its fibre satisfies
  `dim {x}⁻ = dim {f x}⁻ + n`.
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

/-- If the scheme-theoretic fibre of `f` over `f x` is pure-dimensional of dimension `n`, the
closure of a generic point `x` of its fibre, taken in that fibre, has dimension `n`: it is an
irreducible component of the fibre. -/
theorem topologicalKrullDim_closure_singleton_asFiber_of_isFiberGenericPoint
    (f : X ⟶ Y) {n : ℕ} {x : X} (hn : IsPureDimensional n (f.fiber (f x)))
    (hx : f.IsFiberGenericPoint x) :
    topologicalKrullDim (closure ({f.asFiber x} : Set (f.fiber (f x)))) = n :=
  -- `irreducibleComponents` membership of a point closure is, by definition of `genericPoints`,
  -- membership of the point in `genericPoints`.
  isPureDimensional_iff.mp hn _ ((f.isFiberGenericPoint_iff_asFiber_mem_genericPoints x).mp hx)

end AlgebraicGeometry.Scheme.Hom

namespace TauCeti.AlgebraicGeometry

open CategoryTheory.Limits

section GenericPointDimension

variable (k : Type u) [Field k] {X Y : Scheme.{u}} [X.Over (Spec (.of k))]
  [Y.Over (Spec (.of k))]

variable [LocallyOfFiniteType (X ↘ Spec (.of k))]

variable [LocallyOfFiniteType (Y ↘ Spec (.of k))]

/-- **Dimension of a point and of its fibre.** Let `f : X ⟶ Y` be a morphism over a field `k`
between schemes locally of finite type over `k`. Then the closure of a point `x` has dimension
that of the closure of `f x` plus that of the closure of `x` in the scheme-theoretic fibre of `f`
over `f x`. -/
theorem height_eq_height_add_height_asFiber (f : X ⟶ Y) [f.IsOver (Spec (.of k))] (x : X) :
    height x = height (f x) + height (f.asFiber x) := by
  set y := f x
  let K : Type u := Y.residueField y
  let F := f.fiber y
  let x' : F := f.asFiber x
  let p : F ⟶ Spec (.of K) := f.fiberToSpecResidueField y
  have : LocallyOfFiniteType f := by
    have : LocallyOfFiniteType (f ≫ Y ↘ Spec (.of k)) := by
      rw [comp_over]
      infer_instance
    exact locallyOfFiniteType_of_comp f (Y ↘ Spec (.of k))
  -- The fibre lies over `k` through `X`, and over `κ(y)`.
  let _ : F.Over (Spec (.of k)) := ⟨f.fiberι y ≫ X ↘ Spec (.of k)⟩
  let _ : F.Over (Spec (.of K)) := ⟨p⟩
  have : (f.fiberι y).IsOver (Spec (.of k)) := ⟨rfl⟩
  have hF : F ↘ Spec (.of K) ≫ Spec.map (CommRingCat.ofHom (algebraMap k K)) =
      F ↘ Spec (.of k) := by
    -- The structure morphisms chosen above are `p` and `fiberι y ≫ X ↘ Spec k`; `change`
    -- unfolds `↘` to them.
    change p ≫ _ = f.fiberι y ≫ X ↘ Spec (.of k)
    rw [← Y.fromSpecResidueField_comp_over k y, ← comp_over f (Spec (.of k)), ← Category.assoc,
      ← Category.assoc]
    exact congrArg (· ≫ Y ↘ Spec (.of k)) (f.fiber_fac y).symm
  have : LocallyOfFiniteType (F ↘ Spec (.of K)) :=
    inferInstanceAs (LocallyOfFiniteType (pullback.snd f (Y.fromSpecResidueField y)))
  have e1 : height x = (Algebra.trdeg k (X.residueField (f.fiberι y x'))).toNat := by
    rw [← height_eq_toNat_trdeg_residueField k]
    exact congrArg height (f.fiberι_asFiber x).symm
  have e3 : height x' = (Algebra.trdeg K (F.residueField x')).toNat :=
    height_eq_toNat_trdeg_residueField K x'
  rw [e1, height_eq_toNat_trdeg_residueField k y, e3,
    ← (f.fiberι y).trdeg_residueField_eq_of_isIso_residueFieldMap x',
    trdeg_residueField_eq_add_of_over k K hF x',
    Cardinal.toNat_add (trdeg_residueField_lt_aleph0 k y) (trdeg_residueField_lt_aleph0 K x')]
  norm_cast

/-- **Dimension of a generic point of a fibre.** Let `f : X ⟶ Y` be a morphism over a field `k`,
of pure relative dimension `n`, between schemes locally of finite type over `k`. If `x` is the
generic point of an irreducible component of its fibre, then the closure of `x` has dimension
that of the closure of `f x` plus `n`. -/
theorem height_eq_height_add_of_isFiberGenericPoint (f : X ⟶ Y) [f.IsOver (Spec (.of k))]
    (n : ℕ) [PureRelativeDimension n f] {x : X} (hx : f.IsFiberGenericPoint x) :
    height x = height (f x) + n := by
  have hdim := f.topologicalKrullDim_closure_singleton_asFiber_of_isFiberGenericPoint
    (PureRelativeDimension.isPureDimensional_fiber (d := n) f (f x)) hx
  have h : height (f.asFiber x) = n := by
    have := (height_eq_topologicalKrullDim_closure_singleton (f.asFiber x)).trans hdim
    exact_mod_cast this
  rw [height_eq_height_add_height_asFiber k f x, h]

end GenericPointDimension

end TauCeti.AlgebraicGeometry

end
