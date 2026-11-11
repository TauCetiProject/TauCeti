/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Smooth.Flat
public import TauCeti.Algebra.Algebra.Hom
public import TauCeti.Algebra.AlgebraicGroup.BaseChange.Basic
public import TauCeti.Algebra.AlgebraicGroup.GeneralLinear.Coordinate.BaseChange
public import TauCeti.Algebra.AlgebraicGroup.GeneralLinear.Reductive.Over
public import TauCeti.Algebra.AlgebraicGroup.Hopf.Map

/-!
# Smooth affine integral models and reductive models

Let `O` be a commutative ring with an algebra map to a field `K`, typically a valuation ring with
fraction field `K`, and let `G` be an affine group of finite type over `K` with coordinate Hopf
algebra `H`. A smooth affine `O`-model of `G` is a smooth commutative Hopf `O`-algebra `A`, of
finite type, together with a Hopf isomorphism `K ⊗[O] A ≅ H`. Its integral points
`𝒢(O) = Hom_O(A, O)` form a subgroup of `G(K) = Hom_K(H, K)`: a point `g` of `G` lies in `𝒢(O)`
exactly when `g` takes integral values on the image of `A`. Morphisms of models are Hopf maps of
the coordinate algebras over the identity of `H`; since a smooth algebra is flat, `A` embeds in
`K ⊗[O] A` and there is at most one morphism between two models.

Over a local ring `O` with residue field `κ`, the special fibre of `𝒢` is `κ ⊗[O] A`. A model is
reductive when both fibres are connected reductive groups, and a subgroup of `G(K)` is
hyperspecial when it is the group of integral points of a reductive model. A reductive group
scheme over `O` in the sense of `TauCeti.reductiveCommHopfAlgPropertyOver` gives a reductive
model; in particular `GL_n` over `O` is a reductive model of `GL_n` over `K`, so `GL_n(O)` is
hyperspecial.

## Main declarations

* `TauCeti.IntegralModel.integralPoints`: the integral points of a Hopf `O`-algebra, as a subgroup
  of the points of its generic fibre.
* `TauCeti.IntegralModel.SmoothModel`: a smooth affine `O`-model of an affine `K`-group.
* `TauCeti.IntegralModel.SmoothModel.integralPoints`: the subgroup `𝒢(O)` of `G(K)`, with
  membership criterion `SmoothModel.mem_integralPoints_iff`.
* `TauCeti.IntegralModel.SmoothModel.Hom`: morphisms of models, at most one between two models
  (`SmoothModel.Hom.instSubsingleton`); `SmoothModel.Hom.integralPoints_le` compares integral
  points along a morphism.
* `TauCeti.IntegralModel.SmoothModel.specialFibre`, `SmoothModel.HasConnectedFibres` and
  `SmoothModel.IsReductive`: the special fibre and the fibrewise conditions on a model.
* `TauCeti.IntegralModel.IsHyperspecialSubgroup`: the integral points of some reductive model.
* `TauCeti.IntegralModel.SmoothModel.generalLinear`: the standard model of `GL_n`, which is
  reductive (`SmoothModel.generalLinear_isReductive`).

## References

* F. Bruhat, J. Tits, *Groupes réductifs sur un corps local II*, Publ. Math. IHÉS 60 (1984),
  1.2.2–1.2.5, pp. 17–18, and 4.6.31, pp. 136–137.
* X. Zhu, *Affine Grassmannians and the geometric Satake in mixed characteristic*, Ann. of Math.
  185 (2017), §0.5.
* B. Conrad, *Reductive group schemes* (2014), Definition 3.1.1.
-/

public section

open CategoryTheory TensorProduct

namespace TauCeti.IntegralModel

universe u

variable (O K : Type u) [CommRing O] [Field K] [Algebra O K]

/-- The integral points `Hom_O(A, O)` of a Hopf `O`-algebra `A`, as a subgroup of the points
`Hom_K(K ⊗[O] A, K)` of its generic fibre: the image of coefficient inclusion `O → K` followed by
the base-change point equivalence. -/
noncomputable def integralPoints (A : FiniteTypeCommHopfAlgCat.{u, u} O) :
    Subgroup (WithConv (K ⊗[O] A →ₐ[K] K)) :=
  ((AlgHom.baseChangePointsMulEquiv (k := O) (K := K) (A := A) (R := K)).toMonoidHom.comp
    (AlgHom.mapValue (H := A) (Algebra.ofId O K))).range

variable {O K}

/-- A point of the generic fibre is integral exactly when its values on `1 ⊗ a` are integral for
every `a ∈ A`. -/
theorem mem_integralPoints_iff [FaithfulSMul O K] (A : FiniteTypeCommHopfAlgCat.{u, u} O)
    (g : WithConv (K ⊗[O] A →ₐ[K] K)) :
    g ∈ integralPoints O K A ↔ ∀ a : A, g (1 ⊗ₜ[O] a) ∈ (algebraMap O K).range := by
  let e := AlgHom.baseChangePointsMulEquiv (k := O) (K := K) (A := A) (R := K)
  have hrange := AlgHom.range_comp_left_of_injective (A := A) (Algebra.ofId O K)
    (FaithfulSMul.algebraMap_injective O K)
  constructor
  · rintro ⟨x, rfl⟩ a
    exact ⟨x.ofConv a, by simp [AlgHom.mapValue_apply]⟩
  · intro hg
    obtain ⟨x, hx⟩ : (e.symm g).ofConv ∈
        Set.range (fun x : A →ₐ[O] O ↦ (Algebra.ofId O K).comp x) := by
      rw [hrange]
      intro a
      exact hg a
    have hx' : (Algebra.ofId O K).comp x = (e.symm g).ofConv := hx
    refine ⟨WithConv.toConv x, ?_⟩
    change e (AlgHom.mapValue (Algebra.ofId O K) (WithConv.toConv x)) = g
    rw [AlgHom.mapValue_apply, WithConv.ofConv_toConv, hx', WithConv.toConv_ofConv,
      MulEquiv.apply_symm_apply]

/-- A smooth affine `O`-model of the affine `K`-group with coordinate Hopf algebra `H`: a smooth
commutative Hopf `O`-algebra of finite type with a Hopf isomorphism from its generic fibre to
`H` ([Bruhat–Tits II], 1.2.2–1.2.5). -/
structure SmoothModel (O K : Type u) [CommRing O] [Field K] [Algebra O K]
    (H : FiniteTypeCommHopfAlgCat.{u, u} K) where
  /-- The coordinate Hopf algebra `O[𝒢]` of the model. -/
  coord : FiniteTypeCommHopfAlgCat.{u, u} O
  /-- The coordinate algebra of the model is smooth over `O`. -/
  smooth : Algebra.Smooth O coord
  /-- The identification `K ⊗[O] O[𝒢] ≅ H` of the generic fibre. -/
  genericFibreIso : FiniteTypeCommHopfAlgCat.baseChange (K := K) coord ≅ H

namespace SmoothModel

attribute [instance] SmoothModel.smooth

variable {H : FiniteTypeCommHopfAlgCat.{u, u} K} (𝒢 : SmoothModel O K H)

/-- Applying the inverse of the generic-fibre isomorphism after it is the identity. -/
@[simp]
lemma genericFibreIso_inv_hom_apply (x : K ⊗[O] 𝒢.coord) :
    FiniteTypeCommHopfAlgCat.toBialgHom 𝒢.genericFibreIso.inv
      (FiniteTypeCommHopfAlgCat.toBialgHom 𝒢.genericFibreIso.hom x) = x := by
  have := DFunLike.congr_fun
    (congrArg FiniteTypeCommHopfAlgCat.toBialgHom 𝒢.genericFibreIso.hom_inv_id) x
  rwa [FiniteTypeCommHopfAlgCat.toBialgHom_comp, FiniteTypeCommHopfAlgCat.toBialgHom_id] at this

/-- Applying the generic-fibre isomorphism after its inverse is the identity. -/
@[simp]
lemma genericFibreIso_hom_inv_apply (h : H) :
    FiniteTypeCommHopfAlgCat.toBialgHom 𝒢.genericFibreIso.hom
      (FiniteTypeCommHopfAlgCat.toBialgHom 𝒢.genericFibreIso.inv h) = h := by
  have := DFunLike.congr_fun
    (congrArg FiniteTypeCommHopfAlgCat.toBialgHom 𝒢.genericFibreIso.inv_hom_id) h
  rwa [FiniteTypeCommHopfAlgCat.toBialgHom_comp, FiniteTypeCommHopfAlgCat.toBialgHom_id] at this

/-- The integral points `𝒢(O) = Hom_O(O[𝒢], O)` of a smooth model, as a subgroup of the points
`G(K) = Hom_K(H, K)` of its generic fibre. -/
noncomputable def integralPoints : Subgroup (WithConv (H →ₐ[K] K)) :=
  (IntegralModel.integralPoints O K 𝒢.coord).map
    (BialgHom.mapDomain (FiniteTypeCommHopfAlgCat.toBialgHom 𝒢.genericFibreIso.inv) :
      WithConv (K ⊗[O] 𝒢.coord →ₐ[K] K) →* WithConv (H →ₐ[K] K))

/-- A point `g` of `G` lies in `𝒢(O)` exactly when `g` takes integral values on the image of
every `a ∈ O[𝒢]` in `H`. -/
theorem mem_integralPoints_iff [FaithfulSMul O K] (g : WithConv (H →ₐ[K] K)) :
    g ∈ 𝒢.integralPoints ↔ ∀ a : 𝒢.coord,
      g (FiniteTypeCommHopfAlgCat.toBialgHom 𝒢.genericFibreIso.hom (1 ⊗ₜ[O] a)) ∈
        (algebraMap O K).range := by
  constructor
  · rintro ⟨g', hg', rfl⟩ a
    rw [SetLike.mem_coe, IntegralModel.mem_integralPoints_iff] at hg'
    simp only [BialgHom.mapDomain_apply, WithConv.ofConv_toConv, AlgHom.coe_comp,
      Function.comp_apply, BialgHom.coe_toAlgHom]
    rw [genericFibreIso_inv_hom_apply]
    exact hg' a
  · intro hg
    refine ⟨BialgHom.mapDomain (A := K)
      (FiniteTypeCommHopfAlgCat.toBialgHom 𝒢.genericFibreIso.hom) g,
      (IntegralModel.mem_integralPoints_iff _ _).2 fun a ↦ by
        simpa [BialgHom.mapDomain_apply] using hg a, ?_⟩
    ext h
    simp only [BialgHom.mapDomain_apply, WithConv.ofConv_toConv, AlgHom.coe_comp,
      Function.comp_apply, BialgHom.coe_toAlgHom]
    rw [genericFibreIso_hom_inv_apply]

/-- A morphism of smooth models `𝒢' → 𝒢`, given by a Hopf map `O[𝒢] → O[𝒢']` of coordinate
algebras over the identity of `H`. -/
@[ext]
structure Hom (𝒢 𝒢' : SmoothModel O K H) where
  /-- The Hopf map of coordinate algebras. -/
  hom : 𝒢.coord ⟶ 𝒢'.coord
  /-- The map lies over the identity of the generic fibre. -/
  comm : FiniteTypeCommHopfAlgCat.baseChangeMap (K := K) hom ≫ 𝒢'.genericFibreIso.hom =
    𝒢.genericFibreIso.hom

namespace Hom

variable {𝒢} {𝒢' : SmoothModel O K H}

/-- On pure tensors `1 ⊗ a`, a morphism of models is compatible with the generic-fibre
isomorphisms. -/
lemma genericFibreIso_hom_one_tmul (f : Hom 𝒢 𝒢') (a : 𝒢.coord) :
    FiniteTypeCommHopfAlgCat.toBialgHom 𝒢'.genericFibreIso.hom
        (1 ⊗ₜ[O] FiniteTypeCommHopfAlgCat.toBialgHom f.hom a) =
      FiniteTypeCommHopfAlgCat.toBialgHom 𝒢.genericFibreIso.hom (1 ⊗ₜ[O] a) := by
  rw [← FiniteTypeCommHopfAlgCat.baseChangeMap_apply_tmul (K := K) f.hom]
  exact DFunLike.congr_fun (congrArg FiniteTypeCommHopfAlgCat.toBialgHom f.comm) _

/-- There is at most one morphism between two smooth models: a smooth algebra is flat, so it
embeds in its generic fibre. -/
instance instSubsingleton [FaithfulSMul O K] : Subsingleton (Hom 𝒢 𝒢') := by
  refine ⟨fun f f' ↦ Hom.ext (FiniteTypeCommHopfAlgCat.hom_ext (BialgHom.ext fun a ↦ ?_))⟩
  apply Algebra.TensorProduct.includeRight_injective (A := K)
    (FaithfulSMul.algebraMap_injective O K)
  have h := (genericFibreIso_hom_one_tmul f a).trans (genericFibreIso_hom_one_tmul f' a).symm
  have h' := congrArg (FiniteTypeCommHopfAlgCat.toBialgHom 𝒢'.genericFibreIso.inv) h
  rwa [genericFibreIso_inv_hom_apply, genericFibreIso_inv_hom_apply] at h'

/-- A morphism of models `𝒢' → 𝒢` gives `𝒢'(O) ≤ 𝒢(O)`. -/
theorem integralPoints_le [FaithfulSMul O K] (f : Hom 𝒢 𝒢') :
    𝒢'.integralPoints ≤ 𝒢.integralPoints := by
  intro g hg
  rw [mem_integralPoints_iff] at hg ⊢
  intro a
  rw [← genericFibreIso_hom_one_tmul f a]
  exact hg _

end Hom

section Fibres

variable [IsLocalRing O]

/-- The special fibre `κ ⊗[O] O[𝒢]` of a smooth model over a local ring `O` with residue
field `κ`. -/
noncomputable abbrev specialFibre :
    FiniteTypeCommHopfAlgCat.{u, u} (IsLocalRing.ResidueField O) :=
  FiniteTypeCommHopfAlgCat.baseChange (K := IsLocalRing.ResidueField O) 𝒢.coord

/-- A smooth model has connected fibres when both its generic fibre `G` and its special fibre are
geometrically connected. -/
def HasConnectedFibres : Prop :=
  geometricallyConnectedCommHopfAlgProperty K H.obj ∧
    geometricallyConnectedCommHopfAlgProperty (IsLocalRing.ResidueField O) 𝒢.specialFibre.obj

/-- A smooth model is reductive when both its generic fibre `G` and its special fibre are
connected reductive groups ([Bruhat–Tits II], 4.6.31; [Zhu], §0.5). -/
def IsReductive : Prop :=
  reductiveCommHopfAlgProperty K H ∧
    reductiveCommHopfAlgProperty (IsLocalRing.ResidueField O) 𝒢.specialFibre

variable {𝒢}

/-- A reductive model has connected fibres. -/
theorem IsReductive.hasConnectedFibres (h𝒢 : 𝒢.IsReductive) : 𝒢.HasConnectedFibres :=
  ⟨((reductiveCommHopfAlgProperty_iff K H).1 h𝒢.1).2.1,
    ((reductiveCommHopfAlgProperty_iff _ _).1 h𝒢.2).2.1⟩

/-- A smooth model whose coordinate algebra is a reductive group scheme over `O` is a reductive
model. -/
theorem isReductive_of_reductiveCommHopfAlgPropertyOver
    (h𝒢 : reductiveCommHopfAlgPropertyOver O 𝒢.coord) : 𝒢.IsReductive :=
  ⟨(reductiveCommHopfAlgProperty K).prop_of_iso 𝒢.genericFibreIso (h𝒢.fiber K),
    h𝒢.fiber (IsLocalRing.ResidueField O)⟩

end Fibres

end SmoothModel

/-- A subgroup of `G(K)` is hyperspecial when it is the group of integral points of a reductive
model of `G` over the local ring `O` ([Bruhat–Tits II], 5.1.40; [Zhu], §0.5). -/
def IsHyperspecialSubgroup [IsLocalRing O] {H : FiniteTypeCommHopfAlgCat.{u, u} K}
    (P : Subgroup (WithConv (H →ₐ[K] K))) : Prop :=
  ∃ 𝒢 : SmoothModel O K H, 𝒢.IsReductive ∧ 𝒢.integralPoints = P

/-- The integral points of a reductive model form a hyperspecial subgroup. -/
theorem SmoothModel.IsReductive.isHyperspecialSubgroup [IsLocalRing O]
    {H : FiniteTypeCommHopfAlgCat.{u, u} K} {𝒢 : SmoothModel O K H} (h𝒢 : 𝒢.IsReductive) :
    IsHyperspecialSubgroup (O := O) 𝒢.integralPoints :=
  ⟨𝒢, h𝒢, rfl⟩

namespace SmoothModel

variable (O K) in
/-- The standard smooth model `GL_{n,O}` of `GL_{n,K}`. -/
noncomputable def generalLinear (n : ℕ) :
    SmoothModel O K (GeneralLinear.finiteTypeCoordinateHopfAlgebra K n) where
  coord := GeneralLinear.finiteTypeCoordinateHopfAlgebra O n
  smooth := (GeneralLinear.reductiveCommHopfAlgPropertyOver_finiteTypeCoordinateHopfAlgebra
    O n).smooth
  genericFibreIso := GeneralLinear.finiteTypeCoordinateHopfAlgebraBaseChangeIso O K n

/-- The standard model `GL_{n,O}` is a reductive model of `GL_{n,K}`. -/
theorem generalLinear_isReductive [IsLocalRing O] (n : ℕ) :
    (generalLinear O K n).IsReductive :=
  isReductive_of_reductiveCommHopfAlgPropertyOver
    (GeneralLinear.reductiveCommHopfAlgPropertyOver_finiteTypeCoordinateHopfAlgebra O n)

/-- Both fibres `GL_{n,K}` and `GL_{n,κ}` of the standard model are geometrically connected. -/
theorem hasConnectedFibres_generalLinear [IsLocalRing O] (n : ℕ) :
    (generalLinear O K n).HasConnectedFibres :=
  (generalLinear_isReductive n).hasConnectedFibres

/-- `GL_n(O)` is a hyperspecial subgroup of `GL_n(K)`. -/
theorem isHyperspecialSubgroup_generalLinear [IsLocalRing O] (n : ℕ) :
    IsHyperspecialSubgroup (O := O) (generalLinear O K n).integralPoints :=
  (generalLinear_isReductive n).isHyperspecialSubgroup

end SmoothModel

end TauCeti.IntegralModel
