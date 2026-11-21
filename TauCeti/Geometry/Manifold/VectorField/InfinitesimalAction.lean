/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Lie.Abelian
public import Mathlib.Algebra.Lie.OfAssociative
public import Mathlib.Algebra.Lie.Prod
public import Mathlib.Geometry.Manifold.VectorBundle.ContMDiffSection
public import Mathlib.Geometry.Manifold.VectorField.LieBracket
public import Mathlib.Topology.Algebra.Module.FiniteDimension
public import TauCeti.Algebra.Lie.AffineLine
public import TauCeti.Geometry.Manifold.VectorField.Prod

import TauCeti.Geometry.Manifold.IsManifold.Basic
import TauCeti.Geometry.Manifold.MFDeriv.Graph
import TauCeti.Geometry.Manifold.VectorField.LieBracket
import TauCeti.LinearAlgebra.Submodule.Prod

/-!
# Infinitesimal actions of Lie algebras by vector fields

An infinitesimal action of a real Lie algebra `𝔤` on a manifold `M` is a linear map `Z ↦ Z_M`
from `𝔤` to smooth vector fields on `M` satisfying `(⁅Z, Z'⁆)_M = -[Z_M, Z'_M]`, where `[·, ·]`
is Mathlib's Lie bracket of vector fields `VectorField.mlieBracket` (in a chart,
`[V, W] = DW · V - DV · W`). The sign is the one satisfied by the fundamental vector fields
`ξ_M(x) = d/dt|₀ exp(t ξ) • x` of a left action of a Lie group, so an infinitesimal action is an
antihomomorphism into the Lie algebra of vector fields. Infinitesimal actions are the input of
moment maps (`TauCeti.SmoothTwoForm.IsMomentMap`).

An infinitesimal action restricts along a Lie algebra homomorphism `𝔥 → 𝔤`
(`TauCeti.InfinitesimalAction.comp`), for instance to a Lie subalgebra. Two infinitesimal actions of
the same Lie algebra on `M` and on `N` give the diagonal action `Z ↦ (Z_M, Z_N)` on `M × N`
(`TauCeti.InfinitesimalAction.prod`), because Lie brackets of product vector fields are computed
factor by factor. Infinitesimal actions of `𝔤` on `M` and of `𝔥` on `N` give the componentwise
action `(Z, Z') ↦ (Z_M, Z'_N)` of `𝔤 × 𝔥` on `M × N` (`TauCeti.InfinitesimalAction.prodMap`),
whose orbit tangent spaces and isotropy algebras are the products of those of the factors. For
maps `i₁ × i₂` and `p₁ × p₂` out of a product, the vertical vectors of `p₁ × p₂` are sent by
`d(i₁ × i₂)` into, or are exactly those sent into, the orbit directions of `S × S'` exactly when
the same holds for both factors
(`TauCeti.InfinitesimalAction.ker_mfderiv_prodMap_le_comap_map_eval_prodMap_iff`,
`TauCeti.InfinitesimalAction.ker_mfderiv_prodMap_eq_comap_map_eval_prodMap_iff`). The basic
example is the action of the Lie algebra of all endomorphisms of a finite-dimensional real vector
space `V` on `V` by the linear vector fields `x ↦ A x` (`TauCeti.InfinitesimalAction.linear`),
which restricts to the linear actions of the classical subalgebras, such as the symplectic Lie
algebra. An abelian Lie algebra acts by translations, through the constant vector fields `x ↦ τ Z`
of a linear map `τ` (`TauCeti.InfinitesimalAction.translation`).

At a point `x`, an infinitesimal action has an **orbit tangent space** `𝔤 · x = {Z_M(x)}`
(`TauCeti.InfinitesimalAction.orbitTangent`) and an **isotropy algebra** `𝔤_x = {Z | Z_M(x) = 0}`
(`TauCeti.InfinitesimalAction.isotropy`), the range and the kernel of the linear map
`Z ↦ Z_M(x)` (`TauCeti.InfinitesimalAction.eval`). The isotropy algebra is a Lie subalgebra, since
the Lie bracket of two vector fields vanishing at `x` vanishes at `x`. The orbit map identifies
`𝔤 ⧸ 𝔤_x` with `𝔤 · x` (`TauCeti.InfinitesimalAction.quotIsotropyEquivOrbitTangent`), and more
generally `𝔨 ⧸ (𝔨 ∩ 𝔤_x)` with `𝔨 · x` for a subspace `𝔨` of `𝔤`
(`TauCeti.InfinitesimalAction.quotIsotropyEquivMap`); rank–nullity gives
`dim (𝔤 · x) + dim 𝔤_x = dim 𝔤`. Where the action is locally free, that is `𝔤_x = 0`, the orbit
map embeds `𝔤` into the tangent space at `x`, so `𝔤` is finite-dimensional when `M` is
(`TauCeti.InfinitesimalAction.finiteDimensional_of_isotropy_eq_bot`). For the fundamental vector
fields of a Lie group action, `𝔤 · x` and `𝔤_x` are the image and the kernel of the differential at
the identity of the orbit map `g ↦ g • x`. These are the pointwise data entering the differential
of a moment map.

## Main definitions

* `TauCeti.InfinitesimalAction 𝔤 I M`: infinitesimal actions of `𝔤` on `M`.
* `TauCeti.InfinitesimalAction.comp`: the restriction of an infinitesimal action along a Lie
  algebra homomorphism.
* `TauCeti.InfinitesimalAction.toSectionLinearMap`: the action viewed as an `ℝ`-linear map into
  smooth tangent sections.
* `TauCeti.InfinitesimalAction.prod`: the diagonal action on a product of two manifolds.
* `TauCeti.InfinitesimalAction.prodMap`: the componentwise action of a product of Lie algebras on
  a product of two manifolds.
* `TauCeti.InfinitesimalAction.eval a x`: the linear map `Z ↦ Z_M(x)`.
* `TauCeti.InfinitesimalAction.orbitTangent a x`: the orbit tangent space `𝔤 · x`.
* `TauCeti.InfinitesimalAction.isotropy a x`: the isotropy Lie subalgebra `𝔤_x`.
* `TauCeti.InfinitesimalAction.quotIsotropyEquivOrbitTangent a x`: the identification
  `𝔤 ⧸ 𝔤_x ≃ 𝔤 · x`.
* `TauCeti.InfinitesimalAction.quotIsotropyEquivMap a x 𝔨`: the identification
  `𝔨 ⧸ (𝔨 ∩ 𝔤_x) ≃ 𝔨 · x`.
* `TauCeti.InfinitesimalAction.linear V`: the action of `Module.End ℝ V` on `V` by linear vector
  fields.
* `TauCeti.InfinitesimalAction.translation τ`: the action of an abelian Lie algebra on a vector
  space by the constant vector fields of a linear map `τ`.
* `TauCeti.InfinitesimalAction.affineLine`: the action of `LieAlgebra.AffineLine ℝ` on `ℝ` by
  affine vector fields `x ↦ u.1 * x + u.2`.

## References

* V. Guillemin, S. Sternberg, *Symplectic Techniques in Physics*, Cambridge University Press,
  1984, Section 26.
* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Graduate Texts in Mathematics 218,
  Springer, 2013, Chapter 20 (infinitesimal generators of group actions).
-/

public noncomputable section

open scoped Manifold ContDiff
open VectorField

namespace TauCeti

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]

variable (𝔤 : Type*) [LieRing 𝔤] [LieAlgebra ℝ 𝔤] (I : ModelWithCorners ℝ E H)
  (M : Type*) [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]

/-- An **infinitesimal action** of a real Lie algebra `𝔤` on a manifold `M`: a linear map
`Z ↦ Z_M` from `𝔤` to smooth vector fields on `M` with `(⁅Z, Z'⁆)_M = -[Z_M, Z'_M]`. -/
structure InfinitesimalAction where
  /-- The vector field `Z_M` generated by `Z`, as a linear map in `Z`. -/
  toLinearMap : 𝔤 →ₗ[ℝ] (x : M) → TangentSpace I x
  /-- Each generated vector field is smooth. -/
  contMDiff_toLinearMap' :
    ∀ Z, ContMDiff I I.tangent ∞ fun x ↦ (⟨x, toLinearMap Z x⟩ : TangentBundle I M)
  /-- The generated vector fields form an antihomomorphism of Lie algebras. -/
  toLinearMap_lie' :
    ∀ Z Z', toLinearMap ⁅Z, Z'⁆ = -mlieBracket I (toLinearMap Z) (toLinearMap Z')

namespace InfinitesimalAction

variable {𝔤 I M}

instance : FunLike (InfinitesimalAction 𝔤 I M) 𝔤 ((x : M) → TangentSpace I x) where
  coe a := a.toLinearMap
  coe_injective a b h := by
    obtain ⟨f, _, _⟩ := a
    obtain ⟨g, _, _⟩ := b
    congr
    exact LinearMap.coe_injective h

instance : LinearMapClass (InfinitesimalAction 𝔤 I M) ℝ 𝔤 ((x : M) → TangentSpace I x) where
  map_add a := a.toLinearMap.map_add
  map_smulₛₗ a := a.toLinearMap.map_smul

@[simp]
theorem coe_toLinearMap (a : InfinitesimalAction 𝔤 I M) : ⇑a.toLinearMap = a :=
  (rfl)

@[simp]
theorem coe_mk (f : 𝔤 →ₗ[ℝ] (x : M) → TangentSpace I x) (h₁ h₂) :
    ⇑(⟨f, h₁, h₂⟩ : InfinitesimalAction 𝔤 I M) = f :=
  (rfl)

/-- Two infinitesimal actions generating the same vector fields are equal. -/
@[ext]
theorem ext {a b : InfinitesimalAction 𝔤 I M} (h : ∀ Z, a Z = b Z) : a = b :=
  DFunLike.ext _ _ h

/-- The vector field generated by an element of the Lie algebra is smooth. -/
theorem contMDiff (a : InfinitesimalAction 𝔤 I M) (Z : 𝔤) :
    ContMDiff I I.tangent ∞ fun x ↦ (⟨x, a Z x⟩ : TangentBundle I M) :=
  a.contMDiff_toLinearMap' Z

/-- An infinitesimal action is an antihomomorphism of Lie algebras:
`(⁅Z, Z'⁆)_M = -[Z_M, Z'_M]`. -/
theorem map_lie (a : InfinitesimalAction 𝔤 I M) (Z Z' : 𝔤) :
    a ⁅Z, Z'⁆ = -mlieBracket I (a Z) (a Z') :=
  a.toLinearMap_lie' Z Z'

section comp

variable {𝔥 : Type*} [LieRing 𝔥] [LieAlgebra ℝ 𝔥]

/-- The restriction `Z ↦ (f Z)_M` of an infinitesimal action of `𝔤` along a Lie algebra
homomorphism `f : 𝔥 → 𝔤`, for instance the inclusion of a Lie subalgebra. -/
def comp (a : InfinitesimalAction 𝔤 I M) (f : 𝔥 →ₗ⁅ℝ⁆ 𝔤) : InfinitesimalAction 𝔥 I M where
  toLinearMap := a.toLinearMap ∘ₗ (f : 𝔥 →ₗ[ℝ] 𝔤)
  contMDiff_toLinearMap' Z := a.contMDiff (f Z)
  toLinearMap_lie' Z Z' := by
    simp only [LinearMap.coe_comp, LieHom.coe_toLinearMap, Function.comp_apply, LieHom.map_lie,
      coe_toLinearMap, map_lie]

@[simp]
theorem comp_apply (a : InfinitesimalAction 𝔤 I M) (f : 𝔥 →ₗ⁅ℝ⁆ 𝔤) (Z : 𝔥) :
    a.comp f Z = a (f Z) :=
  (rfl)

end comp

section toSectionLinearMap
variable (a : InfinitesimalAction 𝔤 I M)

/-- An infinitesimal action viewed as an `ℝ`-linear map into smooth tangent sections. -/
def toSectionLinearMap : 𝔤 →ₗ[ℝ] Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯ :=
  ⟨⟨fun ξ ↦ ⟨a ξ, a.contMDiff ξ⟩, fun _ _ ↦ by ext; simp⟩, fun _ _ ↦ by ext; simp⟩

@[simp] theorem toSectionLinearMap_apply (ξ : 𝔤) (x : M) : a.toSectionLinearMap ξ x = a ξ x := (rfl)

@[simp] theorem comp_toSectionLinearMap {𝔥 : Type*} [LieRing 𝔥] [LieAlgebra ℝ 𝔥] (ψ : 𝔥 →ₗ⁅ℝ⁆ 𝔤) :
    (a.comp ψ).toSectionLinearMap = a.toSectionLinearMap.comp ψ.toLinearMap := by ext; simp

end toSectionLinearMap

section orbit

variable {𝔥 : Type*} [LieRing 𝔥] [LieAlgebra ℝ 𝔥] (a : InfinitesimalAction 𝔤 I M) (x : M)

/-- The linear map `Z ↦ Z_M(x)` from `𝔤` to the tangent space at `x`. For the fundamental vector
fields of a Lie group action it is the differential at the identity of the orbit map
`g ↦ g • x`. -/
def eval : 𝔤 →ₗ[ℝ] TangentSpace I x :=
  (LinearMap.proj x).comp a.toLinearMap

@[simp]
theorem eval_apply (Z : 𝔤) : a.eval x Z = a Z x :=
  (rfl)

/-- The **orbit tangent space** `𝔤 · x = {Z_M(x) | Z ∈ 𝔤}` of an infinitesimal action at `x`, the
range of `Z ↦ Z_M(x)`. -/
def orbitTangent : Submodule ℝ (TangentSpace I x) :=
  LinearMap.range (a.eval x)

theorem orbitTangent_eq_range : a.orbitTangent x = LinearMap.range (a.eval x) :=
  (rfl)

@[simp]
theorem mem_orbitTangent_iff {v : TangentSpace I x} :
    v ∈ a.orbitTangent x ↔ ∃ Z, a Z x = v :=
  LinearMap.mem_range

theorem mem_orbitTangent (Z : 𝔤) : a Z x ∈ a.orbitTangent x :=
  (a.mem_orbitTangent_iff x).2 ⟨Z, rfl⟩

/-- The **isotropy algebra** `𝔤_x = {Z ∈ 𝔤 | Z_M(x) = 0}` of an infinitesimal action at `x`. It is
a Lie subalgebra because the Lie bracket of two vector fields vanishing at `x` vanishes at `x`. -/
def isotropy : LieSubalgebra ℝ 𝔤 where
  toSubmodule := LinearMap.ker (a.eval x)
  lie_mem' {Z Z'} hZ hZ' := by
    rw [Submodule.mem_carrier, SetLike.mem_coe, LinearMap.mem_ker, eval_apply] at hZ hZ' ⊢
    rw [map_lie, Pi.neg_apply, mlieBracket_eq_zero_of_eq_zero hZ hZ', neg_zero]

@[simp]
theorem mem_isotropy_iff {Z : 𝔤} : Z ∈ a.isotropy x ↔ a Z x = 0 :=
  LinearMap.mem_ker

theorem isotropy_toSubmodule : (a.isotropy x).toSubmodule = LinearMap.ker (a.eval x) :=
  (rfl)

/-- The isotropy algebra is trivial exactly when `Z ↦ Z_M(x)` is injective, that is, when the
action is locally free at `x`. -/
theorem isotropy_eq_bot_iff : a.isotropy x = ⊥ ↔ Function.Injective (a.eval x) := by
  rw [← LinearMap.ker_eq_bot, ← isotropy_toSubmodule, LieSubalgebra.toSubmodule_eq_bot]

/-- Rank–nullity for the orbit map: `dim (𝔤 · x) + dim 𝔤_x = dim 𝔤`. -/
theorem finrank_orbitTangent_add_finrank_isotropy [FiniteDimensional ℝ 𝔤] :
    Module.finrank ℝ (a.orbitTangent x) + Module.finrank ℝ (a.isotropy x) =
      Module.finrank ℝ 𝔤 :=
  LinearMap.finrank_range_add_finrank_ker (a.eval x)

/-- The orbit map `Z ↦ Z_M(x)` identifies `𝔤 ⧸ 𝔤_x` with the orbit tangent space `𝔤 · x`. -/
def quotIsotropyEquivOrbitTangent :
    (𝔤 ⧸ (a.isotropy x).toSubmodule) ≃ₗ[ℝ] a.orbitTangent x :=
  (Submodule.quotEquivOfEq _ _ (a.isotropy_toSubmodule x)).trans
    ((a.eval x).quotKerEquivRange.trans (LinearEquiv.ofEq _ _ (a.orbitTangent_eq_range x).symm))

@[simp]
theorem coe_quotIsotropyEquivOrbitTangent_mk (Z : 𝔤) :
    (a.quotIsotropyEquivOrbitTangent x (Submodule.Quotient.mk Z) : TangentSpace I x) = a Z x := by
  simp [quotIsotropyEquivOrbitTangent]

/-- For a subspace `𝔨` of `𝔤`, the orbit map `Z ↦ Z_M(x)` identifies `𝔨 ⧸ (𝔨 ∩ 𝔤_x)` with the
subspace `𝔨 · x` of the orbit tangent space. -/
def quotIsotropyEquivMap (p : Submodule ℝ 𝔤) :
    (p ⧸ (a.isotropy x).toSubmodule.comap p.subtype) ≃ₗ[ℝ] p.map (a.eval x) :=
  (Submodule.quotEquivOfEq _ _ (by rw [LinearMap.ker_domRestrict, a.isotropy_toSubmodule x])).trans
    (((a.eval x).domRestrict p).quotKerEquivRange.trans
      (LinearEquiv.ofEq _ _ (LinearMap.range_domRestrict p (a.eval x))))

@[simp]
theorem coe_quotIsotropyEquivMap_mk (p : Submodule ℝ 𝔤) (Z : p) :
    (a.quotIsotropyEquivMap x p (Submodule.Quotient.mk Z) : TangentSpace I x) = a Z x := by
  simp [quotIsotropyEquivMap]

/-- Where the action is locally free, the orbit tangent space has the dimension of `𝔤`. -/
theorem finrank_orbitTangent_of_isotropy_eq_bot (h : a.isotropy x = ⊥) :
    Module.finrank ℝ (a.orbitTangent x) = Module.finrank ℝ 𝔤 :=
  LinearMap.finrank_range_of_inj ((a.isotropy_eq_bot_iff x).1 h)

/-- **A Lie algebra acting locally freely at a point of a finite-dimensional manifold is
finite-dimensional.** If `𝔤_x` vanishes, `Z ↦ Z_M(x)` embeds `𝔤` into the tangent space at `x`. -/
theorem finiteDimensional_of_isotropy_eq_bot [FiniteDimensional ℝ E] (h : a.isotropy x = ⊥) :
    FiniteDimensional ℝ 𝔤 :=
  FiniteDimensional.of_injective (a.eval x) ((a.isotropy_eq_bot_iff x).1 h)

/-- The isotropy algebra of a restricted action is the preimage of the isotropy algebra. -/
@[simp]
theorem isotropy_comp (f : 𝔥 →ₗ⁅ℝ⁆ 𝔤) : (a.comp f).isotropy x = (a.isotropy x).comap f :=
  LieSubalgebra.ext _ _ fun _ ↦ by simp

/-- The orbit tangent space of a restricted action is the image of the restricting Lie algebra. -/
theorem orbitTangent_comp (f : 𝔥 →ₗ⁅ℝ⁆ 𝔤) :
    (a.comp f).orbitTangent x = (LinearMap.range (f : 𝔥 →ₗ[ℝ] 𝔤)).map (a.eval x) := by
  ext v
  simp

end orbit

/-- Where an infinitesimal action is locally free (`𝔤_x = 0`), the dimension of `𝔤` is at most the
dimension of `M`. -/
theorem finrank_le_of_isotropy_eq_bot [FiniteDimensional ℝ E] (a : InfinitesimalAction 𝔤 I M)
    {x : M} (hx : a.isotropy x = ⊥) : Module.finrank ℝ 𝔤 ≤ Module.finrank ℝ E := by
  have hle : Module.finrank ℝ (a.orbitTangent x) ≤ Module.finrank ℝ (TangentSpace I x) :=
    Submodule.finrank_le _
  rwa [a.finrank_orbitTangent_of_isotropy_eq_bot x hx, finrank_tangentSpace] at hle

section prod

variable {E' H' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [TopologicalSpace H']
  {J : ModelWithCorners ℝ E' H'} {N : Type*} [TopologicalSpace N] [ChartedSpace H' N]
  [CompleteSpace E] [CompleteSpace E'] [IsManifold I 2 M] [IsManifold J 2 N]

/-- The diagonal infinitesimal action `Z ↦ (Z_M, Z_N)` of `𝔤` on `M × N` of infinitesimal actions
of `𝔤` on `M` and on `N`: the product of the vector fields generated on the two factors. -/
def prod (a : InfinitesimalAction 𝔤 I M) (b : InfinitesimalAction 𝔤 J N) :
    InfinitesimalAction 𝔤 (I.prod J) (M × N) where
  toLinearMap :=
    { toFun Z := Manifold.prodVectorField (a Z) (b Z)
      map_add' Z Z' := by simp only [map_add, Manifold.prodVectorField_add]
      map_smul' c Z := by simp only [map_smul, Manifold.prodVectorField_smul, RingHom.id_apply] }
  contMDiff_toLinearMap' Z := Manifold.contMDiff_prodVectorField (a.contMDiff Z) (b.contMDiff Z)
  toLinearMap_lie' Z Z' := funext fun p ↦ by
    have : IsManifold I (minSmoothness ℝ 2) M := by
      rw [minSmoothness_of_isRCLikeNormedField]; infer_instance
    have : IsManifold J (minSmoothness ℝ 2) N := by
      rw [minSmoothness_of_isRCLikeNormedField]; infer_instance
    simp only [LinearMap.coe_mk, AddHom.coe_mk, Pi.neg_apply]
    rw [Manifold.mlieBracket_prodVectorField ((a.contMDiff Z p.1).mdifferentiableAt (by simp))
      ((a.contMDiff Z' p.1).mdifferentiableAt (by simp))
      ((b.contMDiff Z p.2).mdifferentiableAt (by simp))
      ((b.contMDiff Z' p.2).mdifferentiableAt (by simp)), map_lie, map_lie,
      Manifold.prodVectorField_neg, Pi.neg_apply]

/-- The diagonal action of `Z` is the product of the fields generated on the factors. -/
@[simp]
theorem prod_apply (a : InfinitesimalAction 𝔤 I M) (b : InfinitesimalAction 𝔤 J N) (Z : 𝔤) :
    a.prod b Z = Manifold.prodVectorField (a Z) (b Z) :=
  (rfl)

/-- The isotropy algebra of the diagonal action at `(x, y)` is the intersection of the isotropy
algebras of the two factors. -/
@[simp]
theorem isotropy_prod (a : InfinitesimalAction 𝔤 I M) (b : InfinitesimalAction 𝔤 J N)
    (p : M × N) : (a.prod b).isotropy p = a.isotropy p.1 ⊓ b.isotropy p.2 :=
  LieSubalgebra.ext _ _ fun Z ↦ by
    rw [LieSubalgebra.mem_inf, mem_isotropy_iff, mem_isotropy_iff, mem_isotropy_iff, prod_apply,
      ← (Manifold.tangentSpaceProdEquiv p).map_eq_zero_iff,
      Manifold.tangentSpaceProdEquiv_prodVectorField, Prod.mk_eq_zero]

variable {𝔥 : Type*} [LieRing 𝔥] [LieAlgebra ℝ 𝔥]

/-- The componentwise infinitesimal action `(Z, Z') ↦ (Z_M, Z'_N)` of `𝔤 × 𝔥` on `M × N` of
infinitesimal actions of `𝔤` on `M` and of `𝔥` on `N`: the diagonal action of the actions `a ∘ pr₁`
and `b ∘ pr₂` of `𝔤 × 𝔥`. -/
def prodMap (a : InfinitesimalAction 𝔤 I M) (b : InfinitesimalAction 𝔥 J N) :
    InfinitesimalAction (𝔤 × 𝔥) (I.prod J) (M × N) :=
  (a.comp (LieHom.fst ℝ 𝔤 𝔥)).prod (b.comp (LieHom.snd ℝ 𝔤 𝔥))

theorem prodMap_def (a : InfinitesimalAction 𝔤 I M) (b : InfinitesimalAction 𝔥 J N) :
    a.prodMap b = (a.comp (LieHom.fst ℝ 𝔤 𝔥)).prod (b.comp (LieHom.snd ℝ 𝔤 𝔥)) :=
  (rfl)

/-- The componentwise action of `(Z, Z')` is the product of the fields generated by `Z` and `Z'`
on the factors. -/
@[simp]
theorem prodMap_apply (a : InfinitesimalAction 𝔤 I M) (b : InfinitesimalAction 𝔥 J N)
    (Z : 𝔤 × 𝔥) : a.prodMap b Z = Manifold.prodVectorField (a Z.1) (b Z.2) :=
  (rfl)

/-- Read in the product tangent space, the orbit map `Z ↦ Z_{M × N}(x, y)` of the componentwise
action is the product of the orbit maps of the factors at `x` and at `y`. -/
theorem tangentSpaceProdEquiv_comp_eval_prodMap (a : InfinitesimalAction 𝔤 I M)
    (b : InfinitesimalAction 𝔥 J N) (p : M × N) :
    (Manifold.tangentSpaceProdEquiv p).toLinearMap ∘ₗ (a.prodMap b).eval p =
      (a.eval p.1).prodMap (b.eval p.2) :=
  LinearMap.ext fun _ ↦ Manifold.tangentSpaceProdEquiv_prodVectorField _ _ p

/-- The image of `S × S'` under the orbit map at `(x, y)` of the componentwise action consists of
the tangent vectors whose components lie in the images of `S` and `S'` under the orbit maps of the
factors. -/
theorem map_eval_prodMap (a : InfinitesimalAction 𝔤 I M) (b : InfinitesimalAction 𝔥 J N)
    (p : M × N) (S : Submodule ℝ 𝔤) (S' : Submodule ℝ 𝔥) :
    (S.prod S').map ((a.prodMap b).eval p) =
      ((S.map (a.eval p.1)).prod (S'.map (b.eval p.2))).comap
        (Manifold.tangentSpaceProdEquiv p).toLinearMap := by
  rw [← LinearMap.prodMap_map_prod, ← tangentSpaceProdEquiv_comp_eval_prodMap, Submodule.map_comp,
    Submodule.comap_map_eq_of_injective (Manifold.tangentSpaceProdEquiv p).injective]

/-- The orbit tangent space at `(x, y)` of the componentwise action is `(𝔤 · x) × (𝔥 · y)`. -/
theorem orbitTangent_prodMap (a : InfinitesimalAction 𝔤 I M) (b : InfinitesimalAction 𝔥 J N)
    (p : M × N) :
    (a.prodMap b).orbitTangent p =
      ((a.orbitTangent p.1).prod (b.orbitTangent p.2)).comap
        (Manifold.tangentSpaceProdEquiv p).toLinearMap := by
  rw [orbitTangent_eq_range, orbitTangent_eq_range, orbitTangent_eq_range, LinearMap.range_eq_map,
    LinearMap.range_eq_map, LinearMap.range_eq_map, ← map_eval_prodMap, Submodule.prod_top]

/-- The isotropy algebra at `(x, y)` of the componentwise action is `𝔤_x × 𝔥_y`. -/
@[simp]
theorem toSubmodule_isotropy_prodMap (a : InfinitesimalAction 𝔤 I M)
    (b : InfinitesimalAction 𝔥 J N) (p : M × N) :
    ((a.prodMap b).isotropy p).toSubmodule =
      (a.isotropy p.1).toSubmodule.prod (b.isotropy p.2).toSubmodule := by
  rw [isotropy_toSubmodule, isotropy_toSubmodule, isotropy_toSubmodule,
    ← (Manifold.tangentSpaceProdEquiv p).toLinearEquiv.ker_comp,
    tangentSpaceProdEquiv_comp_eval_prodMap, LinearMap.ker_prodMap]

/-- An element `(Z, Z')` lies in the isotropy algebra at `(x, y)` of the componentwise action
exactly when `Z ∈ 𝔤_x` and `Z' ∈ 𝔥_y`. -/
theorem mem_isotropy_prodMap (a : InfinitesimalAction 𝔤 I M) (b : InfinitesimalAction 𝔥 J N)
    (p : M × N) {Z : 𝔤 × 𝔥} :
    Z ∈ (a.prodMap b).isotropy p ↔ Z.1 ∈ a.isotropy p.1 ∧ Z.2 ∈ b.isotropy p.2 := by
  rw [← LieSubalgebra.mem_toSubmodule, toSubmodule_isotropy_prodMap, Submodule.mem_prod,
    LieSubalgebra.mem_toSubmodule, LieSubalgebra.mem_toSubmodule]

/-- The componentwise action is locally free at `(x, y)` exactly when both factors are locally
free, at `x` and at `y`. -/
@[simp]
theorem isotropy_prodMap_eq_bot_iff (a : InfinitesimalAction 𝔤 I M)
    (b : InfinitesimalAction 𝔥 J N) (p : M × N) :
    (a.prodMap b).isotropy p = ⊥ ↔ a.isotropy p.1 = ⊥ ∧ b.isotropy p.2 = ⊥ := by
  simp only [← LieSubalgebra.toSubmodule_eq_bot, toSubmodule_isotropy_prodMap,
    Submodule.prod_eq_bot_iff]

section vertical

variable {EZ₁ HZ₁ Z₁ : Type*} [NormedAddCommGroup EZ₁] [NormedSpace ℝ EZ₁] [TopologicalSpace HZ₁]
  {J₁ : ModelWithCorners ℝ EZ₁ HZ₁} [TopologicalSpace Z₁] [ChartedSpace HZ₁ Z₁]
  {EZ₂ HZ₂ Z₂ : Type*} [NormedAddCommGroup EZ₂] [NormedSpace ℝ EZ₂] [TopologicalSpace HZ₂]
  {J₂ : ModelWithCorners ℝ EZ₂ HZ₂} [TopologicalSpace Z₂] [ChartedSpace HZ₂ Z₂]
  {EQ₁ HQ₁ Q₁ : Type*} [NormedAddCommGroup EQ₁] [NormedSpace ℝ EQ₁] [TopologicalSpace HQ₁]
  {JQ₁ : ModelWithCorners ℝ EQ₁ HQ₁} [TopologicalSpace Q₁] [ChartedSpace HQ₁ Q₁]
  {EQ₂ HQ₂ Q₂ : Type*} [NormedAddCommGroup EQ₂] [NormedSpace ℝ EQ₂] [TopologicalSpace HQ₂]
  {JQ₂ : ModelWithCorners ℝ EQ₂ HQ₂} [TopologicalSpace Q₂] [ChartedSpace HQ₂ Q₂]
  {i₁ : Z₁ → M} {i₂ : Z₂ → N} {p₁ : Z₁ → Q₁} {p₂ : Z₂ → Q₂}

/-- The tangent vectors at `(z₁, z₂)` sent by `d(i₁ × i₂)` into the image of `S × S'` under the
orbit map of the componentwise action are, read in the product tangent spaces, the products of
those sent by `di₁` and `di₂` into the images of `S` and `S'`. -/
theorem comap_mfderiv_prodMap_map_eval_prodMap (a : InfinitesimalAction 𝔤 I M)
    (b : InfinitesimalAction 𝔥 J N) (S : Submodule ℝ 𝔤) (S' : Submodule ℝ 𝔥)
    {z : Z₁ × Z₂} (hi₁ : MDifferentiableAt J₁ I i₁ z.1) (hi₂ : MDifferentiableAt J₂ J i₂ z.2) :
    ((S.prod S').map ((a.prodMap b).eval (Prod.map i₁ i₂ z))).comap
        (mfderiv (J₁.prod J₂) (I.prod J) (Prod.map i₁ i₂) z).toLinearMap =
      (((S.map (a.eval (i₁ z.1))).comap (mfderiv J₁ I i₁ z.1).toLinearMap).prod
        ((S'.map (b.eval (i₂ z.2))).comap (mfderiv J₂ J i₂ z.2).toLinearMap)).comap
        (Manifold.tangentSpaceProdEquiv z).toLinearMap := by
  rw [map_eval_prodMap, Prod.map_fst, Prod.map_snd, ← Submodule.comap_comp,
    ← LinearMap.prodMap_comap_prod, ← Submodule.comap_comp,
    Manifold.tangentSpaceProdEquiv_comp_mfderiv_prodMap hi₁ hi₂]

/-- **Vertical directions of products.** The vertical tangent vectors of `p₁ × p₂` at `(z₁, z₂)`
are sent by `d(i₁ × i₂)` into the orbit directions `(S × S') · (i₁ × i₂)(z₁, z₂)` of the
componentwise action exactly when the vertical vectors of `p₁` at `z₁` and of `p₂` at `z₂` are sent
by `di₁` and `di₂` into `S · i₁(z₁)` and `S' · i₂(z₂)`. -/
theorem ker_mfderiv_prodMap_le_comap_map_eval_prodMap_iff (a : InfinitesimalAction 𝔤 I M)
    (b : InfinitesimalAction 𝔥 J N) (S : Submodule ℝ 𝔤) (S' : Submodule ℝ 𝔥)
    {z : Z₁ × Z₂} (hi₁ : MDifferentiableAt J₁ I i₁ z.1) (hi₂ : MDifferentiableAt J₂ J i₂ z.2)
    (hp₁ : MDifferentiableAt J₁ JQ₁ p₁ z.1) (hp₂ : MDifferentiableAt J₂ JQ₂ p₂ z.2) :
    (mfderiv (J₁.prod J₂) (JQ₁.prod JQ₂) (Prod.map p₁ p₂) z).ker ≤
        ((S.prod S').map ((a.prodMap b).eval (Prod.map i₁ i₂ z))).comap
          (mfderiv (J₁.prod J₂) (I.prod J) (Prod.map i₁ i₂) z).toLinearMap ↔
      (mfderiv J₁ JQ₁ p₁ z.1).ker ≤
          (S.map (a.eval (i₁ z.1))).comap (mfderiv J₁ I i₁ z.1).toLinearMap ∧
        (mfderiv J₂ JQ₂ p₂ z.2).ker ≤
          (S'.map (b.eval (i₂ z.2))).comap (mfderiv J₂ J i₂ z.2).toLinearMap := by
  rw [Manifold.ker_mfderiv_prodMap hp₁ hp₂, comap_mfderiv_prodMap_map_eval_prodMap a b S S' hi₁ hi₂,
    Submodule.comap_le_comap_iff_of_surjective (Manifold.tangentSpaceProdEquiv z).surjective,
    Submodule.prod_le_prod_iff]

/-- **The vertical directions of a product of reduction data.** The vertical tangent vectors of
`p₁ × p₂` at `(z₁, z₂)` are exactly those sent by `d(i₁ × i₂)` into the orbit directions
`(S × S') · (i₁ × i₂)(z₁, z₂)` of the componentwise action exactly when the vertical vectors of
`p₁` at `z₁` and of `p₂` at `z₂` are exactly those sent by `di₁` and `di₂` into `S · i₁(z₁)` and
`S' · i₂(z₂)`. -/
theorem ker_mfderiv_prodMap_eq_comap_map_eval_prodMap_iff (a : InfinitesimalAction 𝔤 I M)
    (b : InfinitesimalAction 𝔥 J N) (S : Submodule ℝ 𝔤) (S' : Submodule ℝ 𝔥)
    {z : Z₁ × Z₂} (hi₁ : MDifferentiableAt J₁ I i₁ z.1) (hi₂ : MDifferentiableAt J₂ J i₂ z.2)
    (hp₁ : MDifferentiableAt J₁ JQ₁ p₁ z.1) (hp₂ : MDifferentiableAt J₂ JQ₂ p₂ z.2) :
    (mfderiv (J₁.prod J₂) (JQ₁.prod JQ₂) (Prod.map p₁ p₂) z).ker =
        ((S.prod S').map ((a.prodMap b).eval (Prod.map i₁ i₂ z))).comap
          (mfderiv (J₁.prod J₂) (I.prod J) (Prod.map i₁ i₂) z).toLinearMap ↔
      (mfderiv J₁ JQ₁ p₁ z.1).ker =
          (S.map (a.eval (i₁ z.1))).comap (mfderiv J₁ I i₁ z.1).toLinearMap ∧
        (mfderiv J₂ JQ₂ p₂ z.2).ker =
          (S'.map (b.eval (i₂ z.2))).comap (mfderiv J₂ J i₂ z.2).toLinearMap := by
  rw [Manifold.ker_mfderiv_prodMap hp₁ hp₂, comap_mfderiv_prodMap_map_eval_prodMap a b S S' hi₁ hi₂,
    (Submodule.comap_injective_of_surjective (Manifold.tangentSpaceProdEquiv z).surjective).eq_iff,
    Submodule.prod_inj]

end vertical

end prod

section linear

attribute [local instance 100] LieRing.ofAssociativeRing

variable (V : Type*) [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]

/-- The infinitesimal action of the Lie algebra `Module.End ℝ V` of a finite-dimensional real
vector space `V` on `V` by the linear vector fields `x ↦ A x`. -/
def linear : InfinitesimalAction (Module.End ℝ V) 𝓘(ℝ, V) V where
  toLinearMap :=
    { toFun A x := A x
      map_add' _ _ := rfl
      map_smul' _ _ := rfl }
  contMDiff_toLinearMap' A :=
    contMDiff_vectorSpace_iff_contDiff.2 (LinearMap.toContinuousLinearMap A).contDiff
  toLinearMap_lie' A B := by
    funext x
    have h := mlieBracket_continuousLinearMap_model_space
      (LinearMap.toContinuousLinearMap A) (LinearMap.toContinuousLinearMap B) x
    simp only [LinearMap.coe_toContinuousLinearMap'] at h
    -- Evaluate the bundled map `A ↦ (x ↦ A x)` being defined; `LinearMap.coe_mk` cannot do this
    -- because its values are typed as tangent vectors rather than elements of `V`.
    change ⁅A, B⁆ x = -mlieBracket 𝓘(ℝ, V) (fun y ↦ A y) (fun y ↦ B y) x
    rw [h, LieRing.of_associative_ring_bracket, LinearMap.sub_apply, mul_apply_eq_comp,
      mul_apply_eq_comp]
    exact (neg_sub _ _).symm

@[simp]
theorem linear_apply (A : Module.End ℝ V) (x : V) : linear V A x = A x :=
  (rfl)

end linear

section translation

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [IsLieAbelian 𝔤]

/-- The infinitesimal action of an abelian Lie algebra `𝔤` on a normed space `V` by the constant
vector fields `x ↦ τ Z` of a linear map `τ : 𝔤 → V`, the generators of the translations
`x ↦ x + t • τ Z`. -/
def translation (τ : 𝔤 →ₗ[ℝ] V) : InfinitesimalAction 𝔤 𝓘(ℝ, V) V where
  toLinearMap :=
    { toFun Z _ := τ Z
      map_add' _ _ := funext fun _ ↦ τ.map_add _ _
      map_smul' _ _ := funext fun _ ↦ τ.map_smul _ _ }
  contMDiff_toLinearMap' Z := contMDiff_vectorSpace_iff_contDiff.2 contDiff_const
  toLinearMap_lie' Z Z' := by
    funext x
    -- Evaluate the bundled map `Z ↦ (x ↦ τ Z)` being defined; its values are typed as tangent
    -- vectors rather than elements of `V`.
    change τ ⁅Z, Z'⁆ = -mlieBracket 𝓘(ℝ, V) (fun _ ↦ τ Z) (fun _ ↦ τ Z') x
    rw [mlieBracket_const_model_space, trivial_lie_zero, map_zero, neg_zero]
    -- The zero of `V` and the zero of its tangent space at `x` agree by definition.
    rfl

@[simp]
theorem translation_apply (τ : 𝔤 →ₗ[ℝ] V) (Z : 𝔤) (x : V) : translation τ Z x = τ Z :=
  (rfl)

end translation

section affineLine

/-- The standard infinitesimal action of `LieAlgebra.AffineLine ℝ` on `ℝ`, sending the dilation
`(1, 0)` to `x ↦ x` (`x ∂_x`) and the translation `(0, 1)` to `x ↦ 1` (`∂_x`). -/
def affineLine : InfinitesimalAction (LieAlgebra.AffineLine ℝ) 𝓘(ℝ, ℝ) ℝ :=
  let f (u : LieAlgebra.AffineLine ℝ) (x : ℝ) : ℝ := u.1 * x + u.2
  let V (u : LieAlgebra.AffineLine ℝ) : ∀ x : ℝ, TangentSpace 𝓘(ℝ, ℝ) x := f u
  have hV (u x) : NormedSpace.fromTangentSpace (𝕜 := ℝ) x (V u x) = f u x :=
    NormedSpace.fromTangentSpace_apply x (V u x)
  ⟨⟨⟨V, fun _ _ ↦ funext fun x ↦ (NormedSpace.fromTangentSpace (𝕜 := ℝ) x).injective <| by
      simp only [Pi.add_apply, map_add, hV, f, Prod.fst_add, Prod.snd_add]; ring⟩,
    fun _ _ ↦ funext fun x ↦ (NormedSpace.fromTangentSpace (𝕜 := ℝ) x).injective <| by
      simp only [Pi.smul_apply, map_smul, hV, f, RingHom.id_apply, smul_eq_mul,
        Prod.smul_fst, Prod.smul_snd]; ring⟩,
    fun _ ↦
      contMDiff_vectorSpace_iff_contDiff.2 ((contDiff_const.mul contDiff_id).add contDiff_const),
    fun u v ↦ funext fun x ↦ (NormedSpace.fromTangentSpace (𝕜 := ℝ) x).injective <| by
      have hu (w : LieAlgebra.AffineLine ℝ) : HasFDerivAt (f w) (w.1 • .id ℝ ℝ) x := by
        simpa [f] using ((hasFDerivAt_id x).const_mul w.1).add_const w.2
      have hmlie : NormedSpace.fromTangentSpace (𝕜 := ℝ) x (mlieBracket 𝓘(ℝ, ℝ) (V u) (V v) x) =
          lieBracket ℝ (f u) (f v) x :=
        (NormedSpace.fromTangentSpace_apply x _).trans (congrFun mlieBracket_eq_lieBracket x)
      simp only [LinearMap.coe_mk, AddHom.coe_mk, Pi.neg_apply, map_neg, hV, hmlie,
        congrFun lieBracket_eq x, (hu u).fderiv, (hu v).fderiv, f,
        LieAlgebra.AffineLine.fst_lie, LieAlgebra.AffineLine.snd_lie,
        _root_.smul_apply, ContinuousLinearMap.id_apply, smul_eq_mul]; ring⟩

@[simp] theorem affineLine_apply (u : LieAlgebra.AffineLine ℝ) (x : ℝ) :
    affineLine u x = u.1 * x + u.2 := (rfl)

end affineLine
end InfinitesimalAction
end TauCeti
