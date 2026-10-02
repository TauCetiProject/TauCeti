/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Contraction
public import TauCeti.Geometry.Hodge.Dual
public import TauCeti.Geometry.Hodge.Morphism
public import TauCeti.Geometry.Hodge.TensorProduct.Basic

/-!
# Internal homs of pure Hodge structures

For pure Hodge structures `V` and `W`, the complex vector space `Hom_ℂ(V, W)` carries a pure
Hodge structure of weight `weight W - weight V`. Its conjugation sends a map `f` to
`x ↦ conj (f (conj x))`, and its degree-`r` component consists of the maps carrying the degree-`p`
component of `V` into the degree-`p+r` component of `W`.

Those degree-shifting subspaces are the construction: since a Hodge decomposition has only
finitely many nonzero components, every linear map is the finite sum of the compositions
`proj_W^q ∘ f ∘ proj_V^p`, so the degree-shifting subspaces decompose `Hom_ℂ(V, W)`. Conjugation
exchanges them in complementary degrees, and they vanish in low degrees, so they form a Hodge
decomposition in the sense of `TauCeti.Hodge.IsHodgeDecomposition`. No finiteness hypothesis on
`V` or `W` is needed.

When `V` is finite-dimensional the construction agrees with the transport of the tensor product of
the dual Hodge structure on `V^*` and the Hodge structure on `W` along Mathlib's contraction
equivalence `V^* ⊗ W ≃ₗ[ℂ] Hom_ℂ(V, W)`; that comparison is
`TauCeti.Hodge.HodgeStructureOn.internalHom_piece_eq_comap`.

The Weil operator of the internal hom conjugates a map by the two Weil operators,
`C(f) = C_W ∘ f ∘ C_V⁻¹`, and the internal hom is functorial in morphisms: contravariantly in `V`
and covariantly in `W`.

For integral structures on lattices `V_ℤ` and `W_ℤ`, with `V_ℤ` finite free, the internal hom is
an integral pure Hodge structure on the lattice `Hom_ℤ(V_ℤ, W_ℤ)`: the complex-linear maps between
the complexifications are a complexification of the integral linear maps, whose lattice
conjugation is the internal-hom conjugation (`TauCeti.Hodge.latticeConjugation_internalHom`).

When `V` and `W` have the same weight, the internal hom has weight `0`, and its real vectors of
type `(0,0)` — equivalently, its real vectors in `F^0` — are exactly the morphisms of pure Hodge
structures `V → W`. For integral structures this reads `Hom_HS(V, W) = Hom_ℤ(V, W) ∩ F^0`: an
integral linear map is a Hodge morphism exactly when its complexification lies in `F^0` of the
internal hom, the conjugation condition being automatic for complexified integral maps.

## Main declarations

* `TauCeti.Hodge.HodgeStructureOn.internalHom`: the internal hom Hodge structure, of weight
  `n₂ - n₁`, with `TauCeti.Hodge.HodgeStructureOn.internalHom_piece` its components.
* `TauCeti.Hodge.HodgeStructureOn.map_mem_piece_of_mem_internalHom_piece`: a degree-`r` map sends
  the degree-`p` component into the degree-`p+r` component, and
  `TauCeti.Hodge.HodgeStructureOn.mem_internalHom_piece_iff` says this characterizes the
  components.
* `TauCeti.Hodge.HodgeStructureOn.map_mem_F_of_mem_internalHom_F`: a map in filtration degree
  at least `r` sends `F^p V` into `F^{p+r} W`, and
  `TauCeti.Hodge.HodgeStructureOn.mem_internalHom_F_iff` says this characterizes the filtration.
* `TauCeti.Hodge.HodgeStructureOn.id_mem_internalHom_piece` and
  `TauCeti.Hodge.HodgeStructureOn.comp_mem_internalHom_piece`: the identity has internal-hom
  degree `0`, and composing maps adds internal-hom degrees.
* `TauCeti.Hodge.HodgeStructureOn.internalHom_piece_eq_comap` and
  `TauCeti.Hodge.HodgeStructureOn.internalHom_F_eq_comap`: over a finite-dimensional source, the
  internal-hom components and filtration are the pullbacks of those of `V^* ⊗ W` along the
  contraction equivalence.
* `TauCeti.Hodge.HodgeStructureOn.weilOperator_internalHom`: the Weil operator of the internal hom
  is conjugation by the Weil operators, so that
  `TauCeti.Hodge.HodgeStructureOn.weilOperator_internalHom_apply_weilOperator` gives
  `C(f) (C_V x) = C_W (f x)`.
* `TauCeti.Hodge.HodgeStructureOn.IsMorphism.internalHomMap`: pre- and post-composition by
  morphisms is a morphism between internal homs.
* `TauCeti.Hodge.HodgeStructureOn.isMorphism_iff_mem_internalHom_piece` and
  `TauCeti.Hodge.HodgeStructureOn.isMorphism_iff_mem_internalHom_F`: the morphisms of pure Hodge
  structures of the same weight are the real vectors of type `(0,0)` of the internal hom, or
  equivalently its real vectors in `F^0`.
* `TauCeti.Hodge.HodgeStructure.Hom.ofMemInternalHomF` and
  `TauCeti.Hodge.HodgeStructure.Hom.exists_toIntLinearMap_eq_iff`: an integral linear map is a
  morphism of integral pure Hodge structures exactly when its complexification lies in `F^0` of
  the internal hom.
* `TauCeti.Hodge.HodgeStructure.internalHom`: the internal hom of integral pure Hodge structures,
  on the lattice of integral linear maps, with `TauCeti.Hodge.HodgeStructure.internalHom_F`,
  `…internalHom_piece` and `…internalHom_weilOperator` identifying its filtration, components and
  Weil operator with those of the complex internal hom.
* `TauCeti.Hodge.HodgeStructure.Hom.internalHomMap`: the morphism `φ ↦ g ∘ φ ∘ f` between
  integral internal homs induced by morphisms `f` and `g`, with
  `TauCeti.Hodge.HodgeStructure.Hom.internalHomMap_id` and `…internalHomMap_comp` its
  functoriality.

This is the internal-hom companion to duals and tensor products for pure Hodge structures;
the convention follows Peters--Steenbrink, *Mixed Hodge Structures*, §2.1.
-/

public section

open scoped TensorProduct

namespace TauCeti.Hodge

universe u v w

variable {W₁ : Type u} {W₂ : Type v}
variable [AddCommGroup W₁] [Module ℂ W₁]
variable [AddCommGroup W₂] [Module ℂ W₂]

namespace Conjugation

/-- The contraction `V^* ⊗ W → Hom_ℂ(V, W)` intertwines tensor-product conjugation with the
intrinsic conjugation on the space of linear maps. -/
theorem dualTensorHom_map_tensorProduct_conj (ω₁ : Conjugation W₁) (ω₂ : Conjugation W₂)
    (z : Module.Dual ℂ W₁ ⊗[ℂ] W₂) :
    dualTensorHom ℂ W₁ W₂ ((ω₁.dual.tensorProduct ω₂).toEquiv z) =
      (ω₁.internalHom ω₂).toEquiv (dualTensorHom ℂ W₁ W₂ z) := by
  induction z using TensorProduct.inductionOn with
  | tmul φ y =>
      ext x
      simpa only [Conjugation.tensorProduct_toEquiv_tmul, Conjugation.dual_toEquiv_apply,
        dualTensorHom_apply, Conjugation.internalHom_toEquiv_apply_apply, starRingEnd_apply] using
          (ω₂.toEquiv.map_smulₛₗ (φ (ω₁.toEquiv x)) y).symm
  | add x y hx hy => simp [hx, hy]

/-- The inverse of the finite-dimensional contraction equivalence intertwines internal-hom
conjugation with tensor-product conjugation. -/
theorem dualTensorHomEquiv_symm_map_internalHom_conj [FiniteDimensional ℂ W₁]
    (ω₁ : Conjugation W₁) (ω₂ : Conjugation W₂) (f : W₁ →ₗ[ℂ] W₂) :
    (dualTensorHomEquiv ℂ W₁ W₂).symm ((ω₁.internalHom ω₂).toEquiv f) =
      (ω₁.dual.tensorProduct ω₂).toEquiv ((dualTensorHomEquiv ℂ W₁ W₂).symm f) := by
  apply (dualTensorHomEquiv ℂ W₁ W₂).injective
  rw [LinearEquiv.apply_symm_apply]
  calc
    (ω₁.internalHom ω₂).toEquiv f =
        (ω₁.internalHom ω₂).toEquiv
          (dualTensorHom ℂ W₁ W₂ ((dualTensorHomEquiv ℂ W₁ W₂).symm f)) := by
      rw [dualTensorHom_dualTensorHomEquiv_symm]
    _ = dualTensorHom ℂ W₁ W₂
        ((ω₁.dual.tensorProduct ω₂).toEquiv ((dualTensorHomEquiv ℂ W₁ W₂).symm f)) :=
      (ω₁.dualTensorHom_map_tensorProduct_conj ω₂ _).symm
    _ = (dualTensorHomEquiv ℂ W₁ W₂)
        ((ω₁.dual.tensorProduct ω₂).toEquiv ((dualTensorHomEquiv ℂ W₁ W₂).symm f)) := by
      simpa only [LinearEquiv.coe_coe] using
        (DFunLike.congr_fun toLinearMap_dualTensorHomEquiv
          ((ω₁.dual.tensorProduct ω₂).toEquiv
            ((dualTensorHomEquiv ℂ W₁ W₂).symm f))).symm

end Conjugation

namespace HodgeStructureOn

variable {ω₁ : Conjugation W₁} {ω₂ : Conjugation W₂} {n₁ n₂ : ℤ}

/-- The complex-linear maps shifting Hodge degree by exactly `r`: those carrying the degree-`a`
component of the source into the degree-`a + r` component of the target, that is, the maps
homogeneous of degree `r` for the two Hodge decompositions. These subspaces are the Hodge
components of the internal hom, by `TauCeti.Hodge.HodgeStructureOn.internalHom_piece`. -/
private noncomputable def internalHomPiece (hs₁ : HodgeStructureOn W₁ ω₁ n₁)
    (hs₂ : HodgeStructureOn W₂ ω₂ n₂) (r : ℤ) : Submodule ℂ (W₁ →ₗ[ℂ] W₂) :=
  LinearMap.homogeneousSubmodule hs₁.piece hs₂.piece r

/-- A map shifts Hodge degree by `r` exactly when it is homogeneous of degree `r` for the two
Hodge decompositions; `TauCeti.LinearMap.isHomogeneous_def` spells that out elementwise. -/
@[simp]
private theorem mem_internalHomPiece_iff (hs₁ : HodgeStructureOn W₁ ω₁ n₁)
    (hs₂ : HodgeStructureOn W₂ ω₂ n₂) {r : ℤ} {f : W₁ →ₗ[ℂ] W₂} :
    f ∈ hs₁.internalHomPiece hs₂ r ↔ LinearMap.IsHomogeneous f hs₁.piece hs₂.piece r :=
  LinearMap.mem_homogeneousSubmodule

/-- Conjugating a map shifting Hodge degree by `r` gives one shifting Hodge degree by the
complementary amount `n₂ - n₁ - r`. -/
private theorem conj_mem_internalHomPiece (hs₁ : HodgeStructureOn W₁ ω₁ n₁)
    (hs₂ : HodgeStructureOn W₂ ω₂ n₂) {r : ℤ} {f : W₁ →ₗ[ℂ] W₂}
    (hf : f ∈ hs₁.internalHomPiece hs₂ r) :
    (ω₁.internalHom ω₂).toEquiv f ∈ hs₁.internalHomPiece hs₂ (n₂ - n₁ - r) := by
  rw [mem_internalHomPiece_iff, LinearMap.isHomogeneous_def] at hf ⊢
  intro a x hx
  have hidx : a + (n₂ - n₁ - r) = n₂ - (n₁ - a + r) := by ring
  rw [Conjugation.internalHom_toEquiv_apply_apply, hidx]
  exact hs₂.conj_mem_piece (hf _ _ (hs₁.conj_mem_piece hx))

/-- Maps shifting Hodge degree by different amounts are independent. -/
private theorem internalHomPiece_iSupIndep (hs₁ : HodgeStructureOn W₁ ω₁ n₁)
    (hs₂ : HodgeStructureOn W₂ ω₂ n₂) : iSupIndep (hs₁.internalHomPiece hs₂) := by
  intro r
  rw [Submodule.disjoint_def]
  intro f hf hf'
  rw [mem_internalHomPiece_iff] at hf
  refine hs₁.linearMap_ext_of_piece (g := 0) fun a x hx ↦ ?_
  have hmem : f x ∈ ⨆ b, ⨆ (_ : b ≠ a + r), hs₂.piece b := by
    refine Submodule.iSup_induction
      (motive := fun g ↦ g x ∈ ⨆ b, ⨆ (_ : b ≠ a + r), hs₂.piece b) _ hf'
      (fun s g hg ↦ ?_) (by simp) (fun g h hg hh ↦ by simpa using Submodule.add_mem _ hg hh)
    refine Submodule.iSup_induction
      (motive := fun g ↦ g x ∈ ⨆ b, ⨆ (_ : b ≠ a + r), hs₂.piece b) _ hg
      (fun hsr g hg ↦ ?_) (by simp) (fun g h hg hh ↦ by simpa using Submodule.add_mem _ hg hh)
    have hle : hs₂.piece (a + s) ≤ ⨆ b, ⨆ (_ : b ≠ a + r), hs₂.piece b :=
      le_iSup₂_of_le (a + s) (by omega) le_rfl
    exact hle (((mem_internalHomPiece_iff hs₁ hs₂).mp hg).map_mem hx)
  simpa using Submodule.disjoint_def.1 (hs₂.piece_iSupIndep (a + r)) _ (hf.map_mem hx) hmem

/-- The maps shifting Hodge degree span the whole space of linear maps: a map is the finite sum of
its components `proj^b ∘ f ∘ proj^a`. -/
private theorem iSup_internalHomPiece_eq_top (hs₁ : HodgeStructureOn W₁ ω₁ n₁)
    (hs₂ : HodgeStructureOn W₂ ω₂ n₂) : ⨆ r, hs₁.internalHomPiece hs₂ r = ⊤ := by
  classical
  refine top_unique fun f _ ↦ ?_
  -- Only finitely many components are nonzero on either side.
  obtain ⟨S₁, hS₁⟩ : ∃ S : Finset ℤ, ∀ a ∉ S, hs₁.piece a = ⊥ :=
    ⟨hs₁.finite_setOf_piece_ne_bot.toFinset, fun a ha ↦ by simpa using ha⟩
  obtain ⟨S₂, hS₂⟩ : ∃ S : Finset ℤ, ∀ b ∉ S, hs₂.piece b = ⊥ :=
    ⟨hs₂.finite_setOf_piece_ne_bot.toFinset, fun b hb ↦ by simpa using hb⟩
  have hf : f = ∑ a ∈ S₁, ∑ b ∈ S₂, (hs₂.proj b).comp (f.comp (hs₁.proj a)) := by
    refine LinearMap.ext fun x ↦ ?_
    simp only [LinearMap.sum_apply, LinearMap.comp_apply]
    calc f x
        = f (∑ a ∈ S₁, hs₁.proj a x) := by rw [hs₁.sum_proj_eq hS₁ x]
      _ = ∑ a ∈ S₁, f (hs₁.proj a x) := map_sum f _ _
      _ = ∑ a ∈ S₁, ∑ b ∈ S₂, hs₂.proj b (f (hs₁.proj a x)) :=
          Finset.sum_congr rfl fun a _ ↦ (hs₂.sum_proj_eq hS₂ _).symm
  rw [hf]
  refine Submodule.sum_mem _ fun a _ ↦ Submodule.sum_mem _ fun b _ ↦ ?_
  refine Submodule.mem_iSup_of_mem (b - a) ?_
  rw [mem_internalHomPiece_iff, LinearMap.isHomogeneous_def]
  intro c x hx
  simp only [LinearMap.comp_apply]
  by_cases hca : a = c
  · subst hca
    have hidx : a + (b - a) = b := by ring
    rw [hs₁.proj_apply_of_mem hx, hidx]
    exact hs₂.proj_mem b (f x)
  · rw [hs₁.proj_apply_eq_zero_of_mem_of_ne hx (Ne.symm hca), map_zero, map_zero]
    exact Submodule.zero_mem _

/-- **The Hodge decomposition of an internal hom.** The maps shifting Hodge degree by a fixed
amount decompose the space of complex-linear maps, are exchanged by the internal-hom conjugation
in complementary degrees, and vanish in low degrees. -/
private theorem isHodgeDecomposition_internalHomPiece (hs₁ : HodgeStructureOn W₁ ω₁ n₁)
    (hs₂ : HodgeStructureOn W₂ ω₂ n₂) :
    IsHodgeDecomposition (ω₁.internalHom ω₂) (n₂ - n₁) (hs₁.internalHomPiece hs₂) where
  isInternal := by
    classical
    exact DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top
      (hs₁.internalHomPiece_iSupIndep hs₂) (hs₁.iSup_internalHomPiece_eq_top hs₂)
  map_conj r := by
    refine le_antisymm ?_ fun f hf ↦ ?_
    · rintro _ ⟨g, hg, rfl⟩
      exact hs₁.conj_mem_internalHomPiece hs₂ hg
    · refine ⟨(ω₁.internalHom ω₂).toEquiv f, ?_, (ω₁.internalHom ω₂).apply_apply f⟩
      have hidx : n₂ - n₁ - (n₂ - n₁ - r) = r := by ring
      have h := hs₁.conj_mem_internalHomPiece hs₂ hf
      rwa [hidx] at h
  exists_forall_lt_eq_bot := by
    obtain ⟨a₂, ha₂⟩ := hs₂.F_top
    obtain ⟨b₁, hb₁⟩ := hs₁.F_bot
    refine ⟨a₂ - b₁, fun r hr ↦ (Submodule.eq_bot_iff _).2 fun f hf ↦ ?_⟩
    refine hs₁.linearMap_ext_of_piece (g := 0) fun a x hx ↦ ?_
    by_cases hab : b₁ ≤ a
    · rw [hs₁.piece_eq_bot_of_F_eq_bot hb₁ hab] at hx
      rw [(Submodule.mem_bot ℂ).1 hx]
      simp
    · have hbot : hs₂.piece (a + r) = ⊥ := hs₂.piece_eq_bot_of_F_eq_top ha₂ (by omega)
      have hzero := ((mem_internalHomPiece_iff hs₁ hs₂).mp hf).map_mem hx
      rw [hbot] at hzero
      simpa using hzero

/-- **The internal hom** of a pure Hodge structure of weight `n₁` and one of weight `n₂`, as a
pure Hodge structure of weight `n₂ - n₁` on the space of complex-linear maps.

Its components are the maps shifting Hodge degree by a fixed amount. -/
noncomputable def internalHom (hs₁ : HodgeStructureOn W₁ ω₁ n₁)
    (hs₂ : HodgeStructureOn W₂ ω₂ n₂) :
    HodgeStructureOn (W₁ →ₗ[ℂ] W₂) (ω₁.internalHom ω₂) (n₂ - n₁) :=
  ofDecomposition (hs₁.isHodgeDecomposition_internalHomPiece hs₂)

/-- The degree-`r` component of the internal hom is the space of maps shifting Hodge degree
by `r`. -/
@[simp]
theorem internalHom_piece (hs₁ : HodgeStructureOn W₁ ω₁ n₁)
    (hs₂ : HodgeStructureOn W₂ ω₂ n₂) (r : ℤ) :
    (hs₁.internalHom hs₂).piece r =
      LinearMap.homogeneousSubmodule hs₁.piece hs₂.piece r :=
  ofDecomposition_piece _ r

/-- The internal-hom filtration is the sum of the components shifting Hodge degree by at
least `p`. -/
@[simp]
theorem internalHom_F (hs₁ : HodgeStructureOn W₁ ω₁ n₁)
    (hs₂ : HodgeStructureOn W₂ ω₂ n₂) (p : ℤ) :
    (hs₁.internalHom hs₂).F p =
      ⨆ r, ⨆ (_ : p ≤ r), LinearMap.homogeneousSubmodule hs₁.piece hs₂.piece r :=
  ofDecomposition_F _ p

/-- The conjugate internal-hom filtration is the sum of the components shifting Hodge degree by
less than the complementary index. -/
@[simp]
theorem internalHom_conjF (hs₁ : HodgeStructureOn W₁ ω₁ n₁)
    (hs₂ : HodgeStructureOn W₂ ω₂ n₂) (p : ℤ) :
    (hs₁.internalHom hs₂).conjF p =
      ⨆ r, ⨆ (_ : r < n₂ - n₁ + 1 - p),
        LinearMap.homogeneousSubmodule hs₁.piece hs₂.piece r :=
  ofDecomposition_conjF _ p

/-- A map of internal-hom Hodge degree `p` carries the source component of degree `a` into the
target component of degree `a + p`. -/
theorem map_mem_piece_of_mem_internalHom_piece (hs₁ : HodgeStructureOn W₁ ω₁ n₁)
    (hs₂ : HodgeStructureOn W₂ ω₂ n₂) {p a : ℤ} {f : W₁ →ₗ[ℂ] W₂}
    (hf : f ∈ (hs₁.internalHom hs₂).piece p) {x : W₁} (hx : x ∈ hs₁.piece a) :
    f x ∈ hs₂.piece (a + p) := by
  rw [internalHom_piece, LinearMap.mem_homogeneousSubmodule] at hf
  exact hf.map_mem hx

/-- A map lies in the degree-`p` internal-hom component exactly when it carries every source
component of degree `a` into the target component of degree `a + p`. -/
theorem mem_internalHom_piece_iff (hs₁ : HodgeStructureOn W₁ ω₁ n₁)
    (hs₂ : HodgeStructureOn W₂ ω₂ n₂) {p : ℤ} (f : W₁ →ₗ[ℂ] W₂) :
    f ∈ (hs₁.internalHom hs₂).piece p ↔ ∀ a, ∀ x ∈ hs₁.piece a, f x ∈ hs₂.piece (a + p) := by
  rw [internalHom_piece, LinearMap.mem_homogeneousSubmodule, LinearMap.isHomogeneous_def]

/-- The identity map has internal-hom degree `0`. -/
theorem id_mem_internalHom_piece (hs : HodgeStructureOn W₁ ω₁ n₁) :
    LinearMap.id ∈ (hs.internalHom hs).piece 0 := by
  rw [internalHom_piece, LinearMap.mem_homogeneousSubmodule]
  exact LinearMap.isHomogeneous_id hs.piece

/-- Composing a map of internal-hom degree `p` with one of internal-hom degree `q` gives a map of
internal-hom degree `p + q`. -/
theorem comp_mem_internalHom_piece {W₃ : Type w} [AddCommGroup W₃] [Module ℂ W₃]
    {ω₃ : Conjugation W₃} {n₃ : ℤ} (hs₁ : HodgeStructureOn W₁ ω₁ n₁)
    (hs₂ : HodgeStructureOn W₂ ω₂ n₂) (hs₃ : HodgeStructureOn W₃ ω₃ n₃) {p q : ℤ}
    {f : W₁ →ₗ[ℂ] W₂} {g : W₂ →ₗ[ℂ] W₃} (hf : f ∈ (hs₁.internalHom hs₂).piece p)
    (hg : g ∈ (hs₂.internalHom hs₃).piece q) :
    g ∘ₗ f ∈ (hs₁.internalHom hs₃).piece (p + q) := by
  rw [internalHom_piece, LinearMap.mem_homogeneousSubmodule] at hf hg ⊢
  exact hg.comp hf

/-- A rank-one map made from a dual vector of degree `p` and a target vector of degree `q` has
internal-hom degree `p + q`. -/
theorem dualTensorHom_mem_internalHom_piece (hs₁ : HodgeStructureOn W₁ ω₁ n₁)
    (hs₂ : HodgeStructureOn W₂ ω₂ n₂) {p q : ℤ} {φ : Module.Dual ℂ W₁} {y : W₂}
    (hφ : φ ∈ (hs₁.dual).piece p) (hy : y ∈ hs₂.piece q) :
    dualTensorHom ℂ W₁ W₂ (φ ⊗ₜ[ℂ] y) ∈ (hs₁.internalHom hs₂).piece (p + q) := by
  rw [mem_internalHom_piece_iff]
  intro a x hx
  rw [dualTensorHom_apply]
  by_cases hap : a = -p
  · subst hap
    have hidx : -p + (p + q) = q := by ring
    rw [hidx]
    exact Submodule.smul_mem _ _ hy
  · rw [hs₁.apply_eq_zero_of_mem_piece_of_ne hx hφ hap, zero_smul]
    exact Submodule.zero_mem _

/-- The degree-`r` internal-hom component of a map, evaluated at a vector of Hodge degree `a`,
is the degree-`a + r` component of the value. -/
theorem internalHom_proj_apply_apply (hs₁ : HodgeStructureOn W₁ ω₁ n₁)
    (hs₂ : HodgeStructureOn W₂ ω₂ n₂) {r a : ℤ} (f : W₁ →ₗ[ℂ] W₂) {x : W₁}
    (hx : x ∈ hs₁.piece a) :
    (hs₁.internalHom hs₂).proj r f x = hs₂.proj (a + r) (f x) := by
  have hext : LinearMap.applyₗ (R := ℂ) x ∘ₗ (hs₁.internalHom hs₂).proj r =
      hs₂.proj (a + r) ∘ₗ LinearMap.applyₗ (R := ℂ) x := by
    refine (hs₁.internalHom hs₂).linearMap_ext_of_piece fun s g hg ↦ ?_
    have hgx : g x ∈ hs₂.piece (a + s) := hs₁.map_mem_piece_of_mem_internalHom_piece hs₂ hg hx
    rcases eq_or_ne s r with rfl | hsr
    · simp only [LinearMap.comp_apply, LinearMap.applyₗ_apply_apply,
        (hs₁.internalHom hs₂).proj_apply_of_mem hg, hs₂.proj_apply_of_mem hgx]
    · simp only [LinearMap.comp_apply, LinearMap.applyₗ_apply_apply,
        (hs₁.internalHom hs₂).proj_apply_eq_zero_of_mem_of_ne hg hsr, LinearMap.zero_apply,
        hs₂.proj_apply_eq_zero_of_mem_of_ne hgx (by omega : a + s ≠ a + r)]
  exact congrArg (fun L ↦ L f) hext

/-- A map in the `p`-th step of the internal-hom filtration sends the `q`-th step of the source
filtration into the `(p+q)`-th step of the target filtration. -/
theorem map_mem_F_of_mem_internalHom_F (hs₁ : HodgeStructureOn W₁ ω₁ n₁)
    (hs₂ : HodgeStructureOn W₂ ω₂ n₂) {p q : ℤ} {f : W₁ →ₗ[ℂ] W₂}
    (hf : f ∈ (hs₁.internalHom hs₂).F p) {x : W₁} (hx : x ∈ hs₁.F q) :
    f x ∈ hs₂.F (p + q) := by
  rw [(hs₁.internalHom hs₂).F_eq_iSup_piece p] at hf
  refine Submodule.iSup_induction (motive := fun g ↦ g x ∈ hs₂.F (p + q)) _ hf
    (fun r g hg ↦ ?_) (by simp) (fun g h hg hh ↦ by simpa using Submodule.add_mem _ hg hh)
  refine Submodule.iSup_induction (motive := fun g ↦ g x ∈ hs₂.F (p + q)) _ hg
    (fun hr g hg ↦ ?_) (by simp) (fun g h hg hh ↦ by simpa using Submodule.add_mem _ hg hh)
  rw [hs₁.F_eq_iSup_piece q] at hx
  refine Submodule.iSup_induction (motive := fun y ↦ g y ∈ hs₂.F (p + q)) _ hx
    (fun a y hy ↦ ?_) (by simp) (fun y z hy hz ↦ by simpa using Submodule.add_mem _ hy hz)
  refine Submodule.iSup_induction (motive := fun y ↦ g y ∈ hs₂.F (p + q)) _ hy
    (fun ha y hy ↦ ?_) (by simp) (fun y z hy hz ↦ by simpa using Submodule.add_mem _ hy hz)
  exact ((hs₂.piece_le_F (a + r)).trans (hs₂.F_antitone (by omega)))
    (hs₁.map_mem_piece_of_mem_internalHom_piece hs₂ hg hy)

/-- A map lies in the `p`-th step of the internal-hom filtration exactly when it sends every
step `F^q` of the source filtration into the step `F^{p+q}` of the target filtration. -/
theorem mem_internalHom_F_iff (hs₁ : HodgeStructureOn W₁ ω₁ n₁)
    (hs₂ : HodgeStructureOn W₂ ω₂ n₂) {p : ℤ} (f : W₁ →ₗ[ℂ] W₂) :
    f ∈ (hs₁.internalHom hs₂).F p ↔ ∀ q, ∀ x ∈ hs₁.F q, f x ∈ hs₂.F (p + q) := by
  refine ⟨fun hf q x hx ↦ hs₁.map_mem_F_of_mem_internalHom_F hs₂ hf hx, fun hf ↦ ?_⟩
  refine (hs₁.internalHom hs₂).mem_of_proj_mem fun r ↦ ?_
  rcases lt_or_ge r p with hrp | hpr
  · have hzero : (hs₁.internalHom hs₂).proj r f = 0 :=
      hs₁.linearMap_ext_of_piece fun a x hx ↦ by
        rw [hs₁.internalHom_proj_apply_apply hs₂ f hx,
          hs₂.proj_eq_zero_of_mem_F_of_lt (hf a x (hs₁.piece_le_F a hx)) (by omega),
          LinearMap.zero_apply]
    rw [hzero]
    exact Submodule.zero_mem _
  · exact ((hs₁.internalHom hs₂).piece_le_F r).trans ((hs₁.internalHom hs₂).F_antitone hpr)
      ((hs₁.internalHom hs₂).proj_mem r f)

section Contraction

variable [FiniteDimensional ℂ W₁]

/-- **The tensor presentation of the internal hom.** Over a finite-dimensional source, the
degree-`p` internal-hom component is the pullback of the degree-`p` component of the tensor
product `V^* ⊗ W` along Mathlib's contraction equivalence. -/
theorem internalHom_piece_eq_comap (hs₁ : HodgeStructureOn W₁ ω₁ n₁)
    (hs₂ : HodgeStructureOn W₂ ω₂ n₂) (p : ℤ) :
    (hs₁.internalHom hs₂).piece p =
      ((hs₁.dual.tensorProduct hs₂).piece p).comap
        (dualTensorHomEquiv ℂ W₁ W₂).symm.toLinearMap := by
  have hpiece : ∀ q, ((hs₁.dual.tensorProduct hs₂).comap (dualTensorHomEquiv ℂ W₁ W₂).symm
      (ω₁.dualTensorHomEquiv_symm_map_internalHom_conj ω₂)).piece q ≤
        (hs₁.internalHom hs₂).piece q := by
    intro q f hf
    rw [comap_piece, Submodule.mem_comap, LinearEquiv.coe_coe] at hf
    rw [internalHom_piece, LinearMap.mem_homogeneousSubmodule, LinearMap.isHomogeneous_def]
    intro a x hx
    -- A tensor of total degree `q` sends the degree-`a` component into the degree-`a + q` one.
    have hle : (hs₁.dual.tensorProduct hs₂).piece q ≤
        (hs₂.piece (a + q)).comap ((LinearMap.applyₗ (R := ℂ) x) ∘ₗ dualTensorHom ℂ W₁ W₂) := by
      rw [tensorProduct_piece_eq_iSup]
      refine iSup_le fun r ↦ Submodule.map₂_le.mpr fun φ hφ y hy ↦ ?_
      simp only [Submodule.mem_comap, LinearMap.comp_apply, LinearMap.applyₗ_apply_apply,
        dualTensorHom_apply, TensorProduct.mk_apply]
      by_cases har : a = -r
      · have hidx : a + q = q - r := by omega
        rw [hidx]
        exact Submodule.smul_mem _ _ hy
      · rw [hs₁.apply_eq_zero_of_mem_piece_of_ne hx hφ har, zero_smul]
        exact Submodule.zero_mem _
    have he : dualTensorHom ℂ W₁ W₂ ((dualTensorHomEquiv ℂ W₁ W₂).symm f) = f :=
      dualTensorHom_dualTensorHomEquiv_symm f
    have hmem := hle hf
    rw [Submodule.mem_comap, LinearMap.comp_apply, LinearMap.applyₗ_apply_apply, he] at hmem
    exact hmem
  rw [← congrFun (((hs₁.internalHom hs₂).piece_iSupIndep.le_iff_eq_of_iSup_eq_top
    (((hs₁.dual.tensorProduct hs₂).comap (dualTensorHomEquiv ℂ W₁ W₂).symm
      (ω₁.dualTensorHomEquiv_symm_map_internalHom_conj ω₂)).iSup_piece_eq_top)).mp hpiece) p,
    comap_piece]

/-- In the tensor presentation, the internal-hom filtration is the pullback of the tensor-product
filtration on `V^* ⊗ W`. -/
theorem internalHom_F_eq_comap (hs₁ : HodgeStructureOn W₁ ω₁ n₁)
    (hs₂ : HodgeStructureOn W₂ ω₂ n₂) (p : ℤ) :
    (hs₁.internalHom hs₂).F p =
      ((hs₁.dual.tensorProduct hs₂).F p).comap
        (dualTensorHomEquiv ℂ W₁ W₂).symm.toLinearMap := by
  rw [(hs₁.internalHom hs₂).F_eq_iSup_piece p, (hs₁.dual.tensorProduct hs₂).F_eq_iSup_piece p,
    Submodule.comap_equiv_eq_map_symm, LinearEquiv.symm_symm, Submodule.map_iSup]
  refine iSup_congr fun q ↦ ?_
  rw [Submodule.map_iSup]
  refine iSup_congr fun _ ↦ ?_
  rw [hs₁.internalHom_piece_eq_comap hs₂ q, Submodule.comap_equiv_eq_map_symm,
    LinearEquiv.symm_symm]

end Contraction

/-! ### The Weil operator of the internal hom -/

/-- **The Weil operator of the internal hom** is conjugation by the Weil operators: it sends a
map `f` to `C_W ∘ f ∘ C_V⁻¹`. -/
@[simp]
theorem weilOperator_internalHom (hs₁ : HodgeStructureOn W₁ ω₁ n₁)
    (hs₂ : HodgeStructureOn W₂ ω₂ n₂) :
    (hs₁.internalHom hs₂).weilOperator =
      (hs₁.weilOperatorEquiv.arrowCongr hs₂.weilOperatorEquiv).toLinearMap := by
  refine ((hs₁.internalHom hs₂).weilOperator_unique _ fun r φ hφ ↦ ?_).symm
  refine hs₁.linearMap_ext_of_piece fun a x hx ↦ ?_
  have hφx := hs₁.map_mem_piece_of_mem_internalHom_piece hs₂ hφ hx
  simp only [LinearEquiv.coe_coe, LinearEquiv.arrowCongr_apply, weilOperatorEquiv_symm_apply,
    weilOperatorEquiv_apply, hs₁.weilOperator_apply_of_mem hx, map_smul,
    hs₂.weilOperator_apply_of_mem hφx, LinearMap.smul_apply, smul_smul]
  congr 1
  -- The inverse Weil scalar of degree `a` in weight `n₁` times the Weil scalar of degree `a + r`
  -- in weight `n₂` is the Weil scalar of degree `r` in weight `n₂ - n₁`. Write `-1 = i^2`; the
  -- exponents then add up to `2r - (n₂ - n₁) + 4a`, and `i^(4a) = 1`.
  rw [show (-1 : ℂ) = Complex.I ^ (2 : ℤ) by simp, ← zpow_mul, ← zpow_add₀ Complex.I_ne_zero,
    ← zpow_add₀ Complex.I_ne_zero,
    show 2 * n₁ + (2 * a - n₁) + (2 * (a + r) - n₂) = 2 * r - (n₂ - n₁) + 4 * a by ring,
    zpow_add₀ Complex.I_ne_zero, zpow_mul]
  simp

/-- The Weil operators intertwine evaluation: `C(f) (C_V x) = C_W (f x)`. -/
theorem weilOperator_internalHom_apply_weilOperator (hs₁ : HodgeStructureOn W₁ ω₁ n₁)
    (hs₂ : HodgeStructureOn W₂ ω₂ n₂) (φ : W₁ →ₗ[ℂ] W₂) (x : W₁) :
    (hs₁.internalHom hs₂).weilOperator φ (hs₁.weilOperator x) = hs₂.weilOperator (φ x) := by
  rw [weilOperator_internalHom, LinearEquiv.coe_coe, LinearEquiv.arrowCongr_apply,
    ← weilOperatorEquiv_apply, LinearEquiv.symm_apply_apply, weilOperatorEquiv_apply]

/-! ### Morphisms as Hodge classes of the internal hom -/

variable {n : ℤ} {hs₁ : HodgeStructureOn W₁ ω₁ n} {hs₂ : HodgeStructureOn W₂ ω₂ n}
  {g : W₁ →ₗ[ℂ] W₂}

/-- **Morphisms are the real vectors of `F^0` of the internal hom.** A complex-linear map between
pure Hodge structures of the same weight is a morphism exactly when it lies in `F^0` of the
internal hom and is fixed by the internal-hom conjugation. -/
theorem isMorphism_iff_mem_internalHom_F :
    IsMorphism hs₁ hs₂ g ↔
      g ∈ (hs₁.internalHom hs₂).F 0 ∧ (ω₁.internalHom ω₂).toEquiv g = g := by
  rw [mem_internalHom_F_iff, Conjugation.internalHom_toEquiv_eq_self_iff]
  refine ⟨fun h ↦ ⟨fun q x hx ↦ ?_, h.commutes_conj⟩, fun h ↦ ⟨h.2, fun p ↦ ?_⟩⟩
  · rw [zero_add]
    exact h.map_F_le q ⟨x, hx, rfl⟩
  · rintro _ ⟨x, hx, rfl⟩
    simpa only [zero_add] using h.1 p x hx

/-- **Morphisms are the real Hodge classes of type `(0,0)` of the internal hom.** A complex-linear
map between pure Hodge structures of the same weight is a morphism exactly when it lies in the
Hodge component `H^{0,0}` of the internal hom, which has weight `0`, and is fixed by the
internal-hom conjugation. -/
theorem isMorphism_iff_mem_internalHom_piece :
    IsMorphism hs₁ hs₂ g ↔
      g ∈ (hs₁.internalHom hs₂).piece 0 ∧ (ω₁.internalHom ω₂).toEquiv g = g := by
  rw [isMorphism_iff_mem_internalHom_F]
  refine and_congr_left fun hg ↦ ?_
  simp only [mem_piece_iff_of_conj_eq _ _ hg, sub_self, and_self]

/-- A morphism of pure Hodge structures of the same weight lies in the Hodge component `H^{0,0}`
of the internal hom. -/
theorem IsMorphism.mem_internalHom_piece (h : IsMorphism hs₁ hs₂ g) :
    g ∈ (hs₁.internalHom hs₂).piece 0 :=
  (isMorphism_iff_mem_internalHom_piece.mp h).1

variable {W₁' W₂' : Type*} [AddCommGroup W₁'] [Module ℂ W₁'] [AddCommGroup W₂'] [Module ℂ W₂']
variable {ω₁' : Conjugation W₁'} {ω₂' : Conjugation W₂'} {m : ℤ}

/-- **Functoriality of the internal hom.** Pre-composition by a morphism into the source and
post-composition by a morphism out of the target, `φ ↦ g ∘ φ ∘ f`, is a morphism between the
internal homs. -/
theorem IsMorphism.internalHomMap {hs₁ : HodgeStructureOn W₁ ω₁ n}
    {hs₂ : HodgeStructureOn W₂ ω₂ m} {hs₁' : HodgeStructureOn W₁' ω₁' n}
    {hs₂' : HodgeStructureOn W₂' ω₂' m} {f : W₁' →ₗ[ℂ] W₁} {g : W₂ →ₗ[ℂ] W₂'}
    (hf : IsMorphism hs₁' hs₁ f) (hg : IsMorphism hs₂ hs₂' g) :
    IsMorphism (hs₁.internalHom hs₂) (hs₁'.internalHom hs₂')
      (LinearMap.lcomp ℂ W₂' f ∘ₗ LinearMap.llcomp ℂ W₁ W₂ W₂' g) where
  commutes_conj φ := by
    ext x
    simp [LinearMap.lcomp_apply', LinearMap.llcomp_apply', hf.commutes_conj, hg.commutes_conj]
  map_F_le p := by
    rintro _ ⟨φ, hφ, rfl⟩
    rw [SetLike.mem_coe, mem_internalHom_F_iff] at hφ
    rw [mem_internalHom_F_iff]
    intro q x hx
    exact hg.map_F_le _ ⟨_, hφ q _ (hf.map_F_le q ⟨x, hx, rfl⟩), rfl⟩

end HodgeStructureOn

namespace HodgeStructure.Hom

variable {V₁ V₂ : Type*} [AddCommGroup V₁] [AddCommGroup V₂]
variable {ι₁ : V₁ →ₗ[ℤ] W₁} {ι₂ : V₂ →ₗ[ℤ] W₂} {h₁ : IsBaseChange ℂ ι₁} {h₂ : IsBaseChange ℂ ι₂}
variable {n : ℤ} {source : HodgeStructure h₁ n} {target : HodgeStructure h₂ n}

/-- The complex action of a morphism of integral pure Hodge structures lies in the Hodge
component `H^{0,0}` of the internal hom. -/
theorem toLinearMap_mem_internalHom_piece (f : Hom source target) :
    f.toLinearMap ∈ (source.internalHom target).piece 0 :=
  f.isMorphism.mem_internalHom_piece

/-- The complex action of a morphism of integral pure Hodge structures lies in `F^0` of the
internal hom. -/
theorem toLinearMap_mem_internalHom_F (f : Hom source target) :
    f.toLinearMap ∈ (source.internalHom target).F 0 :=
  (source.internalHom target).piece_le_F 0 f.toLinearMap_mem_internalHom_piece

/-- An integral linear map whose complexification lies in `F^0` of the internal hom is a morphism
of integral pure Hodge structures. -/
noncomputable def ofMemInternalHomF (φ : V₁ →ₗ[ℤ] V₂)
    (hφ : integralMapToComplex h₁ ι₂ φ ∈ (source.internalHom target).F 0) :
    Hom source target where
  toIntLinearMap := φ
  map_mem_F p x hx := by
    simpa only [zero_add] using
      (HodgeStructureOn.mem_internalHom_F_iff source target _).mp hφ p x hx

/-- The integral map underlying `TauCeti.Hodge.HodgeStructure.Hom.ofMemInternalHomF` is the given
one. -/
@[simp]
theorem ofMemInternalHomF_toIntLinearMap (φ : V₁ →ₗ[ℤ] V₂)
    (hφ : integralMapToComplex h₁ ι₂ φ ∈ (source.internalHom target).F 0) :
    (ofMemInternalHomF φ hφ).toIntLinearMap = φ :=
  (rfl)

/-- **Integral Hodge morphisms are the integral maps in `F^0` of the internal hom.** An integral
linear map underlies a morphism of integral pure Hodge structures exactly when its
complexification lies in `F^0` of the internal hom: `Hom_HS(V, W) = Hom_ℤ(V, W) ∩ F^0`. -/
theorem exists_toIntLinearMap_eq_iff (φ : V₁ →ₗ[ℤ] V₂) :
    (∃ f : Hom source target, f.toIntLinearMap = φ) ↔
      integralMapToComplex h₁ ι₂ φ ∈ (source.internalHom target).F 0 := by
  refine ⟨?_, fun hφ ↦ ⟨ofMemInternalHomF φ hφ, ofMemInternalHomF_toIntLinearMap φ hφ⟩⟩
  rintro ⟨f, rfl⟩
  rw [← toLinearMap_def]
  exact f.toLinearMap_mem_internalHom_F

end HodgeStructure.Hom

/-! ### The internal hom of two integral Hodge structures -/

namespace HodgeStructure

variable {V₁ V₂ : Type*} [AddCommGroup V₁] [AddCommGroup V₂]
variable {ι₁ : V₁ →ₗ[ℤ] W₁} {ι₂ : V₂ →ₗ[ℤ] W₂} {h₁ : IsBaseChange ℂ ι₁} {h₂ : IsBaseChange ℂ ι₂}
variable [Module.Free ℤ V₁] [Module.Finite ℤ V₁] {n₁ n₂ : ℤ}

/-- **The internal hom of two integral pure Hodge structures**, of weight `n₂ - n₁`. It is carried
by the lattice of integral linear maps `Hom_ℤ(V₁, V₂)`, and its Hodge filtration is that of the
internal hom of the complex Hodge structures (`HodgeStructure.internalHom_F`). -/
noncomputable def internalHom (hs₁ : HodgeStructure h₁ n₁) (hs₂ : HodgeStructure h₂ n₂) :
    HodgeStructure (isBaseChange_homLatticeMap h₁ h₂) (n₂ - n₁) :=
  (HodgeStructureOn.internalHom hs₁ hs₂).comap (LinearEquiv.refl ℂ _) fun x ↦ by
    rw [latticeConjugation_internalHom, LinearEquiv.refl_apply, LinearEquiv.refl_apply]

variable (hs₁ : HodgeStructure h₁ n₁) (hs₂ : HodgeStructure h₂ n₂)

/-- The Hodge filtration of the internal hom of two integral Hodge structures is that of the
internal hom of the complex Hodge structures. -/
@[simp]
theorem internalHom_F (p : ℤ) :
    (hs₁.internalHom hs₂).F p = (HodgeStructureOn.internalHom hs₁ hs₂).F p := by
  rw [internalHom, HodgeStructureOn.comap_F, LinearEquiv.refl_toLinearMap, Submodule.comap_id]

/-- The Hodge components of the internal hom of two integral Hodge structures are those of the
internal hom of the complex Hodge structures. -/
@[simp]
theorem internalHom_piece (p : ℤ) :
    (hs₁.internalHom hs₂).piece p = (HodgeStructureOn.internalHom hs₁ hs₂).piece p := by
  rw [internalHom, HodgeStructureOn.comap_piece, LinearEquiv.refl_toLinearMap,
    Submodule.comap_id]

/-- The Weil operator of the integral internal hom is conjugation by the Weil operators. -/
@[simp]
theorem internalHom_weilOperator :
    (hs₁.internalHom hs₂).weilOperator =
      (hs₁.weilOperatorEquiv.arrowCongr hs₂.weilOperatorEquiv).toLinearMap := by
  simp [internalHom, HodgeStructureOn.weilOperator_comap,
    HodgeStructureOn.weilOperator_internalHom]

namespace Hom

variable {V₁' V₂' W₁' W₂' : Type*} [AddCommGroup V₁'] [AddCommGroup V₂']
variable [AddCommGroup W₁'] [Module ℂ W₁'] [AddCommGroup W₂'] [Module ℂ W₂']
variable {ι₁' : V₁' →ₗ[ℤ] W₁'} {ι₂' : V₂' →ₗ[ℤ] W₂'}
variable {h₁' : IsBaseChange ℂ ι₁'} {h₂' : IsBaseChange ℂ ι₂'}
variable [Module.Free ℤ V₁'] [Module.Finite ℤ V₁']
variable {hs₁ hs₂} {hs₁' : HodgeStructure h₁' n₁} {hs₂' : HodgeStructure h₂' n₂}

/-- The morphism `φ ↦ g ∘ φ ∘ f` between integral internal homs induced by a morphism `f` into the
source and a morphism `g` out of the target. -/
noncomputable def internalHomMap (f : Hom hs₁' hs₁) (g : Hom hs₂ hs₂') :
    Hom (hs₁.internalHom hs₂) (hs₁'.internalHom hs₂') where
  toIntLinearMap :=
    LinearMap.lcomp ℤ V₂' f.toIntLinearMap ∘ₗ LinearMap.llcomp ℤ V₁ V₂ V₂' g.toIntLinearMap
  map_mem_F p φ hφ := by
    rw [integralMapToComplex_lcomp_comp_llcomp h₁ h₂, ← toLinearMap_def, ← toLinearMap_def,
      internalHom_F]
    rw [internalHom_F] at hφ
    exact (f.isMorphism.internalHomMap g.isMorphism).map_F_le p ⟨φ, hφ, rfl⟩

/-- The integral map underlying `TauCeti.Hodge.HodgeStructure.Hom.internalHomMap` is pre- and
post-composition by the integral maps. -/
@[simp]
theorem internalHomMap_toIntLinearMap (f : Hom hs₁' hs₁) (g : Hom hs₂ hs₂') :
    (f.internalHomMap g).toIntLinearMap =
      LinearMap.lcomp ℤ V₂' f.toIntLinearMap ∘ₗ LinearMap.llcomp ℤ V₁ V₂ V₂' g.toIntLinearMap :=
  (rfl)

/-- The morphism between integral internal homs acts on a complex-linear map by pre- and
post-composition. -/
@[simp]
theorem internalHomMap_apply (f : Hom hs₁' hs₁) (g : Hom hs₂ hs₂') (φ : W₁ →ₗ[ℂ] W₂) :
    f.internalHomMap g φ = g.toLinearMap ∘ₗ φ ∘ₗ f.toLinearMap := by
  rw [toLinearMap_def, internalHomMap_toIntLinearMap, integralMapToComplex_lcomp_comp_llcomp h₁ h₂]
  simp [toLinearMap_def, LinearMap.lcomp_apply', LinearMap.llcomp_apply', LinearMap.comp_assoc]

/-- The internal hom of identity morphisms is the identity. -/
@[simp]
theorem internalHomMap_id : (id hs₁).internalHomMap (id hs₂) = id (hs₁.internalHom hs₂) := by
  ext φ
  simp

/-- The internal hom is functorial: contravariant in the source and covariant in the target. -/
@[simp]
theorem internalHomMap_comp {V₁'' V₂'' W₁'' W₂'' : Type*} [AddCommGroup V₁''] [AddCommGroup V₂'']
    [AddCommGroup W₁''] [Module ℂ W₁''] [AddCommGroup W₂''] [Module ℂ W₂'']
    {ι₁'' : V₁'' →ₗ[ℤ] W₁''} {ι₂'' : V₂'' →ₗ[ℤ] W₂''} {h₁'' : IsBaseChange ℂ ι₁''}
    {h₂'' : IsBaseChange ℂ ι₂''} [Module.Free ℤ V₁''] [Module.Finite ℤ V₁'']
    {hs₁'' : HodgeStructure h₁'' n₁} {hs₂'' : HodgeStructure h₂'' n₂}
    (f : Hom hs₁' hs₁) (f' : Hom hs₁'' hs₁') (g : Hom hs₂ hs₂') (g' : Hom hs₂' hs₂'') :
    (f.comp f').internalHomMap (g'.comp g) = (f'.internalHomMap g').comp (f.internalHomMap g) := by
  ext φ
  simp

end Hom

end HodgeStructure

end TauCeti.Hodge
