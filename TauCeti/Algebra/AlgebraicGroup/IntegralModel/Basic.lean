/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Smooth.Flat
public import TauCeti.Algebra.AlgebraicGroup.Connected.CommHopfAlgCat
public import TauCeti.Algebra.AlgebraicGroup.FiniteType.BaseChange
public import TauCeti.Algebra.AlgebraicGroup.IntegralModel.Points

/-!
# Smooth affine integral models

Let `O` be a commutative ring with an algebra map to a commutative ring `K`, typically a valuation
ring and its fraction field, and let `G` be an affine group of finite type over `K` with coordinate
Hopf algebra `H`. A smooth affine `O`-model of `G` is a smooth commutative Hopf `O`-algebra `A`,
of finite type, together with a Hopf isomorphism `K ⊗[O] A ≅ H`. We call the base change
`K ⊗[O] A` the generic fiber of the model; this is shorthand, as `K` is an arbitrary `O`-algebra
and need not be the fraction field of a domain `O`. The integral points of the model are the image
of `𝒢(O) = Hom_O(A, O)` in `G(K) = Hom_K(H, K)` under base change along `O → K`. When `O → K` is
injective (`FaithfulSMul O K`), a point `g` of `G` is integral exactly when `g` takes values in
the image of `O` on the image of `A`. Morphisms of models are Hopf maps of the coordinate algebras
over the identity of `H`, that is, morphisms of the corresponding objects of
`CostructuredArrow (FiniteTypeCommHopfAlgCat.baseChangeFunctor) H`; they compare integral points,
and when `O → K` is injective there is at most one morphism between two models.

Over a local ring `O` with residue field `κ`, the special fiber of `𝒢` is the base change
`κ ⊗[O] A`. When `K` is a field, a model has connected fibers when its two selected base changes,
to `K` and to `κ`, are geometrically connected; other fibers of `Spec A → Spec O` are not tested.

## Main declarations

* `TauCeti.IntegralModel.SmoothModel`: a smooth affine `O`-model of an affine `K`-group.
* `TauCeti.IntegralModel.SmoothModel.integralPoints`: the subgroup of `G(K)` of integral points,
  with membership criterion `SmoothModel.mem_integralPoints_iff`.
* `TauCeti.IntegralModel.SmoothModel.Hom`: morphisms of models, at most one between two models
  when `O → K` is injective (`SmoothModel.Hom.instSubsingleton`);
  `SmoothModel.Hom.integralPoints_le` compares integral points along a morphism.
* `TauCeti.IntegralModel.SmoothModel.specialFiber` and `SmoothModel.HasConnectedFibers`: the
  special fiber and the connectedness condition on the two selected base changes.

## References

* F. Bruhat, J. Tits, *Groupes réductifs sur un corps local II*, Publ. Math. IHÉS 60 (1984),
  1.2.2–1.2.5, pp. 17–18.
-/

public section

open CategoryTheory TensorProduct

namespace TauCeti.IntegralModel

universe u

variable {O K : Type u} [CommRing O] [CommRing K] [Algebra O K]

/-- A smooth affine `O`-model of the affine `K`-group with coordinate Hopf algebra `H`: a smooth
commutative Hopf `O`-algebra of finite type with a Hopf isomorphism from its generic fiber
`K ⊗[O] O[𝒢]` to `H` ([Bruhat–Tits II], 1.2.2–1.2.5). -/
structure SmoothModel (O K : Type u) [CommRing O] [CommRing K] [Algebra O K]
    (H : FiniteTypeCommHopfAlgCat.{u, u} K) where
  /-- The coordinate Hopf algebra `O[𝒢]` of the model. -/
  coord : FiniteTypeCommHopfAlgCat.{u, u} O
  /-- The coordinate algebra of the model is smooth over `O`. -/
  smooth : Algebra.Smooth O coord
  /-- The identification `K ⊗[O] O[𝒢] ≅ H` of the generic fiber. -/
  genericFiberIso : FiniteTypeCommHopfAlgCat.baseChange (K := K) coord ≅ H

namespace SmoothModel

attribute [instance] SmoothModel.smooth

variable {H : FiniteTypeCommHopfAlgCat.{u, u} K} (𝒢 : SmoothModel O K H)

/-- The integral points of a smooth model, as a subgroup of the points `G(K) = Hom_K(H, K)` of its
generic fiber: the points whose pullback along the generic fiber isomorphism is an integral point
of the coordinate algebra. -/
noncomputable def integralPoints : Subgroup (WithConv (H →ₐ[K] K)) :=
  (IntegralModel.integralPoints O K 𝒢.coord).comap
    (BialgHom.mapDomain (FiniteTypeCommHopfAlgCat.toBialgHom 𝒢.genericFiberIso.hom) :
      WithConv (H →ₐ[K] K) →* WithConv (K ⊗[O] 𝒢.coord →ₐ[K] K))

/-- Unfolding lemma for `SmoothModel.integralPoints`. -/
theorem integralPoints_def :
    𝒢.integralPoints = (IntegralModel.integralPoints O K 𝒢.coord).comap
      (BialgHom.mapDomain (FiniteTypeCommHopfAlgCat.toBialgHom 𝒢.genericFiberIso.hom) :
        WithConv (H →ₐ[K] K) →* WithConv (K ⊗[O] 𝒢.coord →ₐ[K] K)) :=
  (rfl)

/-- A point `g` of `G` lies in the integral points of `𝒢` exactly when its pullback along the
generic fiber isomorphism is an integral point of the coordinate algebra. -/
theorem mem_integralPoints_iff_mapDomain (g : WithConv (H →ₐ[K] K)) :
    g ∈ 𝒢.integralPoints ↔
      BialgHom.mapDomain (FiniteTypeCommHopfAlgCat.toBialgHom 𝒢.genericFiberIso.hom) g ∈
        IntegralModel.integralPoints O K 𝒢.coord := by
  rw [integralPoints_def, Subgroup.mem_comap]

/-- When `O → K` is injective, a point `g` of `G` is integral for `𝒢` exactly when it takes
values in the image of `O` on the image of every `a ∈ O[𝒢]` in `H`. -/
theorem mem_integralPoints_iff [FaithfulSMul O K] (g : WithConv (H →ₐ[K] K)) :
    g ∈ 𝒢.integralPoints ↔ ∀ a : 𝒢.coord,
      g (FiniteTypeCommHopfAlgCat.toBialgHom 𝒢.genericFiberIso.hom (1 ⊗ₜ[O] a)) ∈
        (algebraMap O K).range := by
  simp only [mem_integralPoints_iff_mapDomain, IntegralModel.mem_integralPoints_iff,
    BialgHom.mapDomain_apply_apply, RingHom.mem_rangeS, RingHom.mem_range]

/-- A smooth model as an object of `CostructuredArrow FiniteTypeCommHopfAlgCat.baseChangeFunctor H`:
its coordinate algebra together with its generic fiber isomorphism. -/
noncomputable abbrev toCostructuredArrow :
    CostructuredArrow (FiniteTypeCommHopfAlgCat.baseChangeFunctor (k := O) (K := K)) H :=
  CostructuredArrow.mk 𝒢.genericFiberIso.hom

/-- A morphism of smooth models `𝒢' → 𝒢`, given by a Hopf map `O[𝒢] → O[𝒢']` of coordinate
algebras over the identity of `H`: a morphism `𝒢.toCostructuredArrow ⟶ 𝒢'.toCostructuredArrow`,
with identity `𝟙`, composition `≫`, underlying Hopf map `CostructuredArrow.Hom.left` and
compatibility `CostructuredArrow.w`. -/
abbrev Hom (𝒢 𝒢' : SmoothModel O K H) : Type u :=
  𝒢.toCostructuredArrow ⟶ 𝒢'.toCostructuredArrow

namespace Hom

variable {𝒢} {𝒢' : SmoothModel O K H}

/-- A morphism of models intertwines the generic fiber isomorphisms, as bialgebra maps. -/
theorem toBialgHom_genericFiberIso_hom_comp (f : Hom 𝒢 𝒢') :
    (FiniteTypeCommHopfAlgCat.toBialgHom 𝒢'.genericFiberIso.hom).comp
        (_root_.Bialgebra.TensorProduct.map (_root_.BialgHom.id K K)
          (FiniteTypeCommHopfAlgCat.toBialgHom f.left)) =
      FiniteTypeCommHopfAlgCat.toBialgHom 𝒢.genericFiberIso.hom := by
  simpa only [CostructuredArrow.mk_left, CostructuredArrow.mk_hom_eq_self,
    FiniteTypeCommHopfAlgCat.toBialgHom_comp, FiniteTypeCommHopfAlgCat.baseChangeFunctor_map,
    FiniteTypeCommHopfAlgCat.toBialgHom_baseChangeMap] using
    congrArg FiniteTypeCommHopfAlgCat.toBialgHom (CostructuredArrow.w f)

/-- On pure tensors `1 ⊗ a`, a morphism of models is compatible with the generic-fiber
isomorphisms. -/
@[simp]
lemma genericFiberIso_hom_one_tmul (f : Hom 𝒢 𝒢') (a : 𝒢.coord) :
    FiniteTypeCommHopfAlgCat.toBialgHom 𝒢'.genericFiberIso.hom
        (1 ⊗ₜ[O] FiniteTypeCommHopfAlgCat.toBialgHom (H := 𝒢.coord) (K := 𝒢'.coord) f.left a) =
      FiniteTypeCommHopfAlgCat.toBialgHom 𝒢.genericFiberIso.hom (1 ⊗ₜ[O] a) := by
  simpa only [CostructuredArrow.mk_left, BialgHom.comp_apply, Bialgebra.TensorProduct.map_tmul,
    BialgHom.id_apply] using DFunLike.congr_fun (toBialgHom_genericFiberIso_hom_comp f) (1 ⊗ₜ[O] a)

/-- When `O → K` is injective, there is at most one morphism between two smooth models. -/
instance instSubsingleton [FaithfulSMul O K] : Subsingleton (Hom 𝒢 𝒢') :=
  ⟨fun f f' ↦ CostructuredArrow.hom_ext _ _ <| ObjectProperty.hom_ext _ <|
    CommHopfAlgCat.baseChangeMap_injective_hom (H := 𝒢.coord.obj) (L := 𝒢'.coord.obj)
      (FaithfulSMul.algebraMap_injective O K) <|
      congrArg (fun φ ↦ φ.hom) ((cancel_mono 𝒢'.genericFiberIso.hom).1
        ((CostructuredArrow.w f).trans (CostructuredArrow.w f').symm))⟩

/-- A morphism of models `𝒢' → 𝒢` gives an inclusion of the integral points of `𝒢'` in those
of `𝒢`. -/
theorem integralPoints_le (f : Hom 𝒢 𝒢') :
    𝒢'.integralPoints ≤ 𝒢.integralPoints := by
  intro g hg
  rw [mem_integralPoints_iff_mapDomain] at hg ⊢
  have := integralPoints_le_comap (K := K) (FiniteTypeCommHopfAlgCat.toBialgHom f.left) hg
  rwa [Subgroup.mem_comap, ← MonoidHom.comp_apply, ← BialgHom.mapDomain_comp,
    toBialgHom_genericFiberIso_hom_comp] at this

end Hom

/-- The special fiber `κ ⊗[O] O[𝒢]` of a smooth model over a local ring `O` with residue
field `κ`. -/
noncomputable abbrev specialFiber [IsLocalRing O] :
    FiniteTypeCommHopfAlgCat.{u, u} (IsLocalRing.ResidueField O) :=
  FiniteTypeCommHopfAlgCat.baseChange (K := IsLocalRing.ResidueField O) 𝒢.coord

section Fibers

variable {K : Type u} [Field K] [Algebra O K] [IsLocalRing O]
  {H : FiniteTypeCommHopfAlgCat.{u, u} K} (𝒢 : SmoothModel O K H)

/-- A smooth model has connected fibers when its two selected base changes, the generic fiber `G`
over `K` and the special fiber over the residue field of `O`, are geometrically connected. -/
def HasConnectedFibers : Prop :=
  geometricallyConnectedCommHopfAlgProperty K H.obj ∧
    geometricallyConnectedCommHopfAlgProperty (IsLocalRing.ResidueField O) 𝒢.specialFiber.obj

/-- Unfolding lemma for `SmoothModel.HasConnectedFibers`. -/
theorem hasConnectedFibers_iff :
    𝒢.HasConnectedFibers ↔ geometricallyConnectedCommHopfAlgProperty K H.obj ∧
      geometricallyConnectedCommHopfAlgProperty (IsLocalRing.ResidueField O) 𝒢.specialFiber.obj :=
  Iff.rfl

variable {𝒢}

/-- The generic fiber of a model with connected fibers is geometrically connected. -/
theorem HasConnectedFibers.genericFiber (h𝒢 : 𝒢.HasConnectedFibers) :
    geometricallyConnectedCommHopfAlgProperty K H.obj :=
  h𝒢.1

/-- The special fiber of a model with connected fibers is geometrically connected. -/
theorem HasConnectedFibers.specialFiber (h𝒢 : 𝒢.HasConnectedFibers) :
    geometricallyConnectedCommHopfAlgProperty (IsLocalRing.ResidueField O) 𝒢.specialFiber.obj :=
  h𝒢.2

end Fibers

end SmoothModel

end TauCeti.IntegralModel
