/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Smooth.Flat
public import TauCeti.Algebra.AlgebraicGroup.BaseChange.Naturality
public import TauCeti.Algebra.AlgebraicGroup.FiniteType.BaseChange
public import TauCeti.Algebra.AlgebraicGroup.Reductive.Over

/-!
# Smooth affine integral models and reductive models

Let `O` be a commutative ring with an algebra map to a commutative ring `K`, typically a valuation
ring and its fraction field, and let `G` be an affine group of finite type over `K` with coordinate
Hopf algebra `H`. A smooth affine `O`-model of `G` is a smooth commutative Hopf `O`-algebra `A`,
of finite type, together with a Hopf isomorphism `K ⊗[O] A ≅ H`. Its integral points are the
image of `𝒢(O) = Hom_O(A, O)` in `G(K) = Hom_K(H, K)` under base change along `O → K`. When
`O → K` is injective (`FaithfulSMul O K`), a point `g` of `G` is integral exactly when `g` takes
values in the image of `O` on the image of `A`. Morphisms of models are Hopf maps of the
coordinate algebras over the identity of `H`; they compare integral points, and when `O → K` is
injective there is at most one morphism between two models.

Over a local ring `O` with residue field `κ` and a field `K`, the special fiber of `𝒢` is
`κ ⊗[O] A`. A model is reductive when both fibers are connected reductive groups, and a subgroup
of `G(K)` is hyperspecial when it is the group of integral points of a reductive model. A reductive
group scheme over `O` in the sense of `TauCeti.reductiveCommHopfAlgPropertyOver` gives a reductive
model.

## Main declarations

* `TauCeti.IntegralModel.integralPoints`: the integral points of a Hopf `O`-algebra, as a subgroup
  of the points of its generic fiber.
* `TauCeti.IntegralModel.SmoothModel`: a smooth affine `O`-model of an affine `K`-group.
* `TauCeti.IntegralModel.SmoothModel.integralPoints`: the subgroup of `G(K)` of integral points,
  with membership criterion `SmoothModel.mem_integralPoints_iff`.
* `TauCeti.IntegralModel.SmoothModel.Hom`: morphisms of models, with identity and composition, at
  most one between two models when `O → K` is injective (`SmoothModel.Hom.instSubsingleton`);
  `SmoothModel.Hom.integralPoints_le` compares integral points along a morphism.
* `TauCeti.IntegralModel.SmoothModel.specialFiber`, `SmoothModel.HasConnectedFibers` and
  `SmoothModel.IsReductive`: the special fiber and the fiberwise conditions on a model.
* `TauCeti.IntegralModel.IsHyperspecialSubgroup`: the integral points of some reductive model.

## References

* F. Bruhat, J. Tits, *Groupes réductifs sur un corps local II*, Publ. Math. IHÉS 60 (1984),
  1.2.2–1.2.5, pp. 17–18, and 4.6.31, pp. 136–137.
* J. Tits, *Reductive groups over local fields*, in *Automorphic forms, representations and
  L-functions*, Proc. Sympos. Pure Math. 33, Part 1 (1979), §3.8.1.
* B. Conrad, *Reductive group schemes* (2014), Definition 3.1.1.
-/

public section

open CategoryTheory TensorProduct

namespace TauCeti.IntegralModel

universe u

variable (O K : Type u) [CommRing O] [CommRing K] [Algebra O K]

/-- The integral points of a Hopf `O`-algebra `A`, as a subgroup of the points
`Hom_K(K ⊗[O] A, K)` of its generic fiber: the image of `Hom_O(A, O)` under base change of points
along `O → K` (`AlgHom.pointsBaseChange`). -/
noncomputable def integralPoints (A : FiniteTypeCommHopfAlgCat.{u, u} O) :
    Subgroup (WithConv (K ⊗[O] A →ₐ[K] K)) :=
  (AlgHom.pointsBaseChange (k := O) (A := A) K).range

/-- Unfolding lemma for `IntegralModel.integralPoints`. -/
theorem integralPoints_def (A : FiniteTypeCommHopfAlgCat.{u, u} O) :
    integralPoints O K A = (AlgHom.pointsBaseChange (k := O) (A := A) K).range :=
  (rfl)

variable {O K}

/-- When `O → K` is injective, a point of the generic fiber is integral exactly when its values on
`1 ⊗ a` lie in the image of `O` for every `a ∈ A`. -/
theorem mem_integralPoints_iff [FaithfulSMul O K] (A : FiniteTypeCommHopfAlgCat.{u, u} O)
    (g : WithConv (K ⊗[O] A →ₐ[K] K)) :
    g ∈ integralPoints O K A ↔ ∀ a : A, g (1 ⊗ₜ[O] a) ∈ (algebraMap O K).range := by
  rw [integralPoints, AlgHom.pointsBaseChange_def, MonoidHom.range_comp, Subgroup.mem_map_equiv,
    MonoidHom.mem_range, ← MonoidHom.mem_mrange,
    AlgHom.mem_mrange_mapValue_iff (FaithfulSMul.algebraMap_injective O K)]
  simp only [AlgHom.baseChangePointsMulEquiv_symm_apply, AlgHom.mem_range, RingHom.mem_range,
    Algebra.ofId_apply]

/-- Integral points are contravariant in the Hopf algebra: a Hopf map `φ : A ⟶ A'` sends the
integral points of `A'` to integral points of `A` by precomposition with its scalar extension. -/
theorem integralPoints_le_comap {A A' : FiniteTypeCommHopfAlgCat.{u, u} O} (φ : A ⟶ A') :
    integralPoints O K A' ≤ (integralPoints O K A).comap
      (BialgHom.mapDomain (A := K) (FiniteTypeCommHopfAlgCat.toBialgHom
        (FiniteTypeCommHopfAlgCat.baseChangeMap (K := K) φ))) := by
  rintro _ ⟨x, rfl⟩
  exact ⟨BialgHom.mapDomain (FiniteTypeCommHopfAlgCat.toBialgHom φ) x,
    (BialgHom.mapDomain_pointsBaseChange K _ x).symm⟩

/-- A smooth affine `O`-model of the affine `K`-group with coordinate Hopf algebra `H`: a smooth
commutative Hopf `O`-algebra of finite type with a Hopf isomorphism from its generic fiber to
`H` ([Bruhat–Tits II], 1.2.2–1.2.5). -/
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
generic fiber: the integral points of its coordinate algebra, transported along the generic fiber
isomorphism. -/
noncomputable def integralPoints : Subgroup (WithConv (H →ₐ[K] K)) :=
  (IntegralModel.integralPoints O K 𝒢.coord).map
    (BialgHom.mapDomain (FiniteTypeCommHopfAlgCat.toBialgHom 𝒢.genericFiberIso.inv) :
      WithConv (K ⊗[O] 𝒢.coord →ₐ[K] K) →* WithConv (H →ₐ[K] K))

/-- Unfolding lemma for `SmoothModel.integralPoints`. -/
theorem integralPoints_def :
    𝒢.integralPoints = (IntegralModel.integralPoints O K 𝒢.coord).map
      (BialgHom.mapDomain (FiniteTypeCommHopfAlgCat.toBialgHom 𝒢.genericFiberIso.inv) :
        WithConv (K ⊗[O] 𝒢.coord →ₐ[K] K) →* WithConv (H →ₐ[K] K)) :=
  (rfl)

/-- A point `g` of `G` lies in the integral points of `𝒢` exactly when its pullback along the
generic fiber isomorphism is an integral point of the coordinate algebra. -/
theorem mem_integralPoints_iff_mapDomain (g : WithConv (H →ₐ[K] K)) :
    g ∈ 𝒢.integralPoints ↔
      BialgHom.mapDomain (FiniteTypeCommHopfAlgCat.toBialgHom 𝒢.genericFiberIso.hom) g ∈
        IntegralModel.integralPoints O K 𝒢.coord := by
  have h₁ : (BialgHom.mapDomain (FiniteTypeCommHopfAlgCat.toBialgHom 𝒢.genericFiberIso.hom)).comp
      (BialgHom.mapDomain (A := K) (FiniteTypeCommHopfAlgCat.toBialgHom 𝒢.genericFiberIso.inv)) =
        MonoidHom.id _ := by
    rw [← BialgHom.mapDomain_comp, ← FiniteTypeCommHopfAlgCat.toBialgHom_comp, Iso.hom_inv_id,
      FiniteTypeCommHopfAlgCat.toBialgHom_id, BialgHom.mapDomain_id]
  have h₂ : (BialgHom.mapDomain (FiniteTypeCommHopfAlgCat.toBialgHom 𝒢.genericFiberIso.inv)).comp
      (BialgHom.mapDomain (A := K) (FiniteTypeCommHopfAlgCat.toBialgHom 𝒢.genericFiberIso.hom)) =
        MonoidHom.id _ := by
    rw [← BialgHom.mapDomain_comp, ← FiniteTypeCommHopfAlgCat.toBialgHom_comp, Iso.inv_hom_id,
      FiniteTypeCommHopfAlgCat.toBialgHom_id, BialgHom.mapDomain_id]
  exact Subgroup.mem_map_equiv (f := MonoidHom.toMulEquiv _ _ h₁ h₂)

/-- When `O → K` is injective, a point `g` of `G` is integral for `𝒢` exactly when it takes
values in the image of `O` on the image of every `a ∈ O[𝒢]` in `H`. -/
theorem mem_integralPoints_iff [FaithfulSMul O K] (g : WithConv (H →ₐ[K] K)) :
    g ∈ 𝒢.integralPoints ↔ ∀ a : 𝒢.coord,
      g (FiniteTypeCommHopfAlgCat.toBialgHom 𝒢.genericFiberIso.hom (1 ⊗ₜ[O] a)) ∈
        (algebraMap O K).range := by
  simp only [mem_integralPoints_iff_mapDomain, IntegralModel.mem_integralPoints_iff,
    BialgHom.mapDomain_apply_apply]

/-- A morphism of smooth models `𝒢' → 𝒢`, given by a Hopf map `O[𝒢] → O[𝒢']` of coordinate
algebras over the identity of `H`. -/
@[ext]
structure Hom (𝒢 𝒢' : SmoothModel O K H) where
  /-- The Hopf map of coordinate algebras. -/
  hom : 𝒢.coord ⟶ 𝒢'.coord
  /-- The map lies over the identity of the generic fiber. -/
  comm : FiniteTypeCommHopfAlgCat.baseChangeMap (K := K) hom ≫ 𝒢'.genericFiberIso.hom =
    𝒢.genericFiberIso.hom

namespace Hom

attribute [reassoc (attr := simp)] comm

/-- The identity morphism of a smooth model. -/
protected def id : Hom 𝒢 𝒢 where
  hom := 𝟙 _
  comm := by
    rw [show FiniteTypeCommHopfAlgCat.baseChangeMap (K := K) (𝟙 𝒢.coord) = 𝟙 _ from
      (FiniteTypeCommHopfAlgCat.baseChangeFunctor (K := K)).map_id _, Category.id_comp]

/-- The identity morphism is the identity Hopf map. -/
@[simp]
theorem id_hom : (Hom.id 𝒢).hom = 𝟙 _ :=
  (rfl)

variable {𝒢} {𝒢' 𝒢'' : SmoothModel O K H}

/-- The composite of morphisms of smooth models, given by composing the Hopf maps of coordinate
algebras. -/
protected def comp (f : Hom 𝒢 𝒢') (f' : Hom 𝒢' 𝒢'') : Hom 𝒢 𝒢'' where
  hom := f.hom ≫ f'.hom
  comm := by
    rw [show FiniteTypeCommHopfAlgCat.baseChangeMap (K := K) (f.hom ≫ f'.hom) =
        FiniteTypeCommHopfAlgCat.baseChangeMap f.hom ≫
          FiniteTypeCommHopfAlgCat.baseChangeMap f'.hom from
      (FiniteTypeCommHopfAlgCat.baseChangeFunctor (K := K)).map_comp _ _, Category.assoc,
      f'.comm, f.comm]

/-- Composition of morphisms of models composes the Hopf maps. -/
@[simp]
theorem comp_hom (f : Hom 𝒢 𝒢') (f' : Hom 𝒢' 𝒢'') : (f.comp f').hom = f.hom ≫ f'.hom :=
  (rfl)

/-- On pure tensors `1 ⊗ a`, a morphism of models is compatible with the generic-fiber
isomorphisms. -/
@[simp]
lemma genericFiberIso_hom_one_tmul (f : Hom 𝒢 𝒢') (a : 𝒢.coord) :
    FiniteTypeCommHopfAlgCat.toBialgHom 𝒢'.genericFiberIso.hom
        (1 ⊗ₜ[O] FiniteTypeCommHopfAlgCat.toBialgHom f.hom a) =
      FiniteTypeCommHopfAlgCat.toBialgHom 𝒢.genericFiberIso.hom (1 ⊗ₜ[O] a) := by
  rw [← FiniteTypeCommHopfAlgCat.baseChangeMap_apply_tmul (K := K) f.hom, ← BialgHom.comp_apply,
    ← FiniteTypeCommHopfAlgCat.toBialgHom_comp, f.comm]

/-- When `O → K` is injective, there is at most one morphism between two smooth models. -/
instance instSubsingleton [FaithfulSMul O K] : Subsingleton (Hom 𝒢 𝒢') :=
  ⟨fun f f' ↦ Hom.ext <| ObjectProperty.hom_ext _ <|
    CommHopfAlgCat.baseChangeMap_injective_hom (FaithfulSMul.algebraMap_injective O K) <|
      congrArg (fun φ ↦ φ.hom) ((cancel_mono 𝒢'.genericFiberIso.hom).1
        (f.comm.trans f'.comm.symm))⟩

/-- A morphism of models `𝒢' → 𝒢` gives an inclusion of the integral points of `𝒢'` in those
of `𝒢`. -/
theorem integralPoints_le (f : Hom 𝒢 𝒢') :
    𝒢'.integralPoints ≤ 𝒢.integralPoints := by
  intro g hg
  rw [mem_integralPoints_iff_mapDomain] at hg ⊢
  have := integralPoints_le_comap (K := K) f.hom hg
  rwa [Subgroup.mem_comap, ← MonoidHom.comp_apply, ← BialgHom.mapDomain_comp,
    ← FiniteTypeCommHopfAlgCat.toBialgHom_comp, f.comm] at this

end Hom

section Fibers

variable {K : Type u} [Field K] [Algebra O K] [IsLocalRing O]
  {H : FiniteTypeCommHopfAlgCat.{u, u} K} (𝒢 : SmoothModel O K H)

/-- The special fiber `κ ⊗[O] O[𝒢]` of a smooth model over a local ring `O` with residue
field `κ`. -/
noncomputable abbrev specialFiber :
    FiniteTypeCommHopfAlgCat.{u, u} (IsLocalRing.ResidueField O) :=
  FiniteTypeCommHopfAlgCat.baseChange (K := IsLocalRing.ResidueField O) 𝒢.coord

/-- A smooth model has connected fibers when both its generic fiber `G` and its special fiber are
geometrically connected. -/
def HasConnectedFibers : Prop :=
  geometricallyConnectedCommHopfAlgProperty K H.obj ∧
    geometricallyConnectedCommHopfAlgProperty (IsLocalRing.ResidueField O) 𝒢.specialFiber.obj

/-- Unfolding lemma for `SmoothModel.HasConnectedFibers`. -/
theorem hasConnectedFibers_iff :
    𝒢.HasConnectedFibers ↔ geometricallyConnectedCommHopfAlgProperty K H.obj ∧
      geometricallyConnectedCommHopfAlgProperty (IsLocalRing.ResidueField O) 𝒢.specialFiber.obj :=
  Iff.rfl

/-- A smooth model is reductive when both its generic fiber `G` and its special fiber are
connected reductive groups ([Bruhat–Tits II], 4.6.31; [Conrad], Definition 3.1.1). -/
def IsReductive : Prop :=
  reductiveCommHopfAlgProperty K H ∧
    reductiveCommHopfAlgProperty (IsLocalRing.ResidueField O) 𝒢.specialFiber

/-- Unfolding lemma for `SmoothModel.IsReductive`. -/
theorem isReductive_iff :
    𝒢.IsReductive ↔ reductiveCommHopfAlgProperty K H ∧
      reductiveCommHopfAlgProperty (IsLocalRing.ResidueField O) 𝒢.specialFiber :=
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

/-- The generic fiber of a reductive model is a connected reductive group. -/
theorem IsReductive.genericFiber (h𝒢 : 𝒢.IsReductive) : reductiveCommHopfAlgProperty K H :=
  h𝒢.1

/-- The special fiber of a reductive model is a connected reductive group. -/
theorem IsReductive.specialFiber (h𝒢 : 𝒢.IsReductive) :
    reductiveCommHopfAlgProperty (IsLocalRing.ResidueField O) 𝒢.specialFiber :=
  h𝒢.2

/-- A reductive model has connected fibers. -/
theorem IsReductive.hasConnectedFibers (h𝒢 : 𝒢.IsReductive) : 𝒢.HasConnectedFibers :=
  ⟨h𝒢.1.geometricallyConnected, h𝒢.2.geometricallyConnected⟩

/-- A smooth model whose coordinate algebra is a reductive group scheme over `O` is a reductive
model. -/
theorem isReductive_of_reductiveCommHopfAlgPropertyOver
    (h𝒢 : reductiveCommHopfAlgPropertyOver O 𝒢.coord) : 𝒢.IsReductive :=
  ⟨(reductiveCommHopfAlgProperty K).prop_of_iso 𝒢.genericFiberIso (h𝒢.fiber K),
    h𝒢.fiber (IsLocalRing.ResidueField O)⟩

end Fibers

end SmoothModel

section Hyperspecial

variable {K : Type u} [Field K] [Algebra O K] [IsLocalRing O]

variable (O) in
/-- A subgroup of `G(K)` is hyperspecial when it is the group of integral points of a reductive
model of `G` over the local ring `O` ([Tits], §3.8.1). -/
def IsHyperspecialSubgroup {H : FiniteTypeCommHopfAlgCat.{u, u} K}
    (P : Subgroup (WithConv (H →ₐ[K] K))) : Prop :=
  ∃ 𝒢 : SmoothModel O K H, 𝒢.IsReductive ∧ 𝒢.integralPoints = P

variable (O) in
/-- Unfolding lemma for `IsHyperspecialSubgroup`. -/
theorem isHyperspecialSubgroup_iff {H : FiniteTypeCommHopfAlgCat.{u, u} K}
    (P : Subgroup (WithConv (H →ₐ[K] K))) :
    IsHyperspecialSubgroup O P ↔ ∃ 𝒢 : SmoothModel O K H, 𝒢.IsReductive ∧ 𝒢.integralPoints = P :=
  Iff.rfl

/-- The integral points of a reductive model form a hyperspecial subgroup. -/
theorem SmoothModel.IsReductive.isHyperspecialSubgroup {H : FiniteTypeCommHopfAlgCat.{u, u} K}
    {𝒢 : SmoothModel O K H} (h𝒢 : 𝒢.IsReductive) :
    IsHyperspecialSubgroup O 𝒢.integralPoints :=
  ⟨𝒢, h𝒢, rfl⟩

end Hyperspecial

end TauCeti.IntegralModel
