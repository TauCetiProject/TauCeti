/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.EnoughInjectives
public import TauCeti.Algebra.Category.GradedModuleCat.Abelian
public import TauCeti.Algebra.Category.GradedModuleCat.Injective
public import TauCeti.Algebra.Category.GradedModuleCat.Products
public import TauCeti.Algebra.Category.GradedModuleCat.RestrictScalars
import TauCeti.Algebra.Category.ModuleCat.CoextendScalars
import TauCeti.Algebra.Module.GradedModule.Dual.Basic

/-!
# Graded coinduced modules and enough injectives

Let `A` be an internally `ℤ`-graded `k`-algebra. Given a `k`-module `V`, `A →ₗ[k] V` carries the
left `A`-action `(a • ψ)(b) = ψ(b * a)`. Maps supported on `A_{-p}` form the degree-`p` submodule
of the **graded coinduced module** associated to `V`, and their finite sums form a graded
`A`-submodule. Morphisms `M ⟶ (coinducedSingle 𝒜 V){n}` correspond `k`-linearly to `M_n →ₗ[k] V`
via evaluation at `1 ∈ A` and `f ↦ (x ↦ (b ↦ f((b • x)_n)))`, dual to `A{n}`; degreewise graded
products yield general coinduced graded modules.

When `V` is injective (or Baer) over `k`, its coinduced graded module is injective. In any module
universe `max uA v` at least that of `A`, embedding each homogeneous piece into an injective
`k`-module gives enough injectives when `k` is `max uA v`-small, and restricting the base ring of
`𝒜` to `ℤ` via `TauCeti.GradedModuleCat.restrictBaseEquivalence` transfers enough injectives to
`GradedModuleCat.{max uA v} 𝒜` over an arbitrary commutative base ring `k`.

## Main definitions

* `TauCeti.GradedModuleCat.coinducedSingle`, `TauCeti.GradedModuleCat.coinducedSingleApply`,
  `TauCeti.GradedModuleCat.coinducedSingleMap`, and
  `TauCeti.GradedModuleCat.coinducedSinglePieceEquiv`: the degree-zero coinduced graded
  `A`-module, its underlying `k`-linear evaluation map, functoriality in the coefficient module,
  and the `k`-linear identification of its degree-`p` piece with `𝒜 (-p) →ₗ[k] V`.
* `TauCeti.GradedModuleCat.coinducedSingleShiftHomEquiv`,
  `TauCeti.GradedModuleCat.coinducedSingleHomEquiv`, `TauCeti.GradedModuleCat.coinduced`,
  `TauCeti.GradedModuleCat.coinducedMap`, and `TauCeti.GradedModuleCat.coinducedHomEquiv`:
  functoriality and universal properties of single and family coinduced graded modules.

## Main results

* `TauCeti.GradedModuleCat.mem_range_coinducedSingleApply_iff`: a `k`-linear functional `A →ₗ[k] V`
  lies in the range of `coinducedSingleApply` iff it vanishes on all homogeneous pieces outside a
  finite set.
* `TauCeti.GradedModuleCat.injective_coinducedSingle_of_baer`,
  `TauCeti.GradedModuleCat.injective_coinducedSingle`,
  `TauCeti.GradedModuleCat.injective_coinduced_of_baer`, and
  `TauCeti.GradedModuleCat.injective_coinduced`: coinduced graded modules of Baer or injective
  `k`-modules are injective.
* `TauCeti.GradedModuleCat.enoughInjectives`: `GradedModuleCat.{max uA v} 𝒜` has enough injectives
  in every module universe at least that of `A`, over an arbitrary commutative base ring `k`.

## References

* C. Năstăsescu and F. Van Oystaeyen, *Methods of Graded Rings*, Lecture Notes in Mathematics
  1836, Springer (2004), Sections 2.2 and 2.3.
* Wentao Li, `TauCeti.Algebra.Module.GradedModule.Product`: the finite-degree-support carrier,
  internal-grading transport, scalar-stability, and homogeneous-lift construction are adapted
  from this file.
-/

public section

noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped DirectSum

namespace TauCeti.GradedModuleCat

universe uk uA v

section Single

variable {k : Type uk} [CommRing k] {A : Type uA} [Ring A] [Algebra k A]
  (𝒜 : ℤ → Submodule k A) (V : Type v) [AddCommGroup V] [Module k V]
  [GradedAlgebra 𝒜]

/-- Finite sums of homogeneous coinduced functionals inside `A →ₗ[k] V`. -/
private abbrev coinducedSingleCarrier : Submodule k (A →ₗ[k] V) :=
  LinearMap.range (DirectSum.coeLinearMap ((InternalGrading.ofDecomposition 𝒜).homPiece V))

private def coinducedSingleGrading : InternalGrading k (coinducedSingleCarrier 𝒜 V) ℤ :=
  InternalGrading.ofRangeCoe ((InternalGrading.ofDecomposition 𝒜).homPiece V)
    ((InternalGrading.ofDecomposition 𝒜).coeLinearMap_homPiece_injective V)

private theorem mem_coinducedSingleGrading_piece_iff (p : ℤ) (ψ : coinducedSingleCarrier 𝒜 V) :
    ψ ∈ (coinducedSingleGrading 𝒜 V).piece p ↔
      ∀ q : ℤ, ∀ b ∈ 𝒜 q, q ≠ -p → ψ.val b = 0 := by
  rw [coinducedSingleGrading, InternalGrading.mem_ofRangeCoe_piece_iff,
    InternalGrading.mem_homPiece_iff]
  simp only [InternalGrading.ofDecomposition_piece]

/-- Right translation of the algebra argument on `A →ₗ[k] V`, bundled `k`-linearly in `a : A`. -/
private def coinducedActionLinear (ψ : A →ₗ[k] V) : A →ₗ[k] (A →ₗ[k] V) where
  toFun a := ψ.comp (LinearMap.mulRight k a)
  map_add' _ _ := LinearMap.ext fun _ ↦ by simp [mul_add]
  map_smul' _ _ := LinearMap.ext fun _ ↦ by simp

private theorem coinducedActionLinear_mem_piece {r p : ℤ} {a : A} (ha : a ∈ 𝒜 r)
    {ψ : A →ₗ[k] V} (hψ : ψ ∈ (InternalGrading.ofDecomposition 𝒜).homPiece V p) :
    coinducedActionLinear V ψ a ∈ (InternalGrading.ofDecomposition 𝒜).homPiece V (r + p) := by
  rw [InternalGrading.mem_homPiece_iff] at hψ ⊢
  intro q b hb _
  rw [InternalGrading.ofDecomposition_piece] at hb
  exact hψ (q + r) (b * a) (by
    rw [InternalGrading.ofDecomposition_piece]
    exact SetLike.GradedMul.mul_mem hb ha) (by omega)

private theorem coinducedActionLinear_mem_carrier (a : A) {ψ : A →ₗ[k] V}
    (hψ : ψ ∈ coinducedSingleCarrier 𝒜 V) :
    coinducedActionLinear V ψ a ∈ coinducedSingleCarrier 𝒜 V := by
  classical
  obtain ⟨y, rfl⟩ := hψ
  induction y using DirectSum.induction_on with
  | zero => simp [coinducedActionLinear]
  | add y z hy hz =>
    have hadd : coinducedActionLinear V (DirectSum.coeLinearMap _ y + DirectSum.coeLinearMap _ z)
        a = _ + _ := LinearMap.add_comp _ _ _
    rw [map_add, hadd]; exact (coinducedSingleCarrier 𝒜 V).add_mem hy hz
  | of p y =>
    rw [DirectSum.coeLinearMap_of, ← DirectSum.sum_support_decompose 𝒜 a, map_sum]
    exact (coinducedSingleCarrier 𝒜 V).sum_mem fun r _ ↦
      InternalGrading.le_range_coeLinearMap ((InternalGrading.ofDecomposition 𝒜).homPiece V)
        (r + p)
        (coinducedActionLinear_mem_piece 𝒜 V (DirectSum.decompose 𝒜 a r).property y.property)

private def coinducedSingleSubmodule :
    Submodule A ((ModuleCat.coextendScalars (algebraMap k A)).obj (ModuleCat.of k V)) where
  carrier := {ψ | coextendScalarsBaseEquiv k A V ψ ∈ coinducedSingleCarrier 𝒜 V}
  zero_mem' := by rw [Set.mem_ofPred_eq, map_zero]; exact (coinducedSingleCarrier 𝒜 V).zero_mem
  add_mem' {ψ₁ ψ₂} h₁ h₂ := by
    simpa [map_add] using (coinducedSingleCarrier 𝒜 V).add_mem h₁ h₂
  smul_mem' a ψ hψ := by
    have h : coextendScalarsBaseEquiv k A V (a • ψ) =
        coinducedActionLinear V (coextendScalarsBaseEquiv k A V ψ) a :=
      LinearMap.ext fun b ↦ coextendScalarsBaseEquiv_smul_apply k A V a ψ b
    rw [Set.mem_ofPred_eq, h]
    exact coinducedActionLinear_mem_carrier 𝒜 V a hψ

private theorem mem_coinducedSingleSubmodule_iff
    (ψ : (ModuleCat.coextendScalars (algebraMap k A)).obj (ModuleCat.of k V)) :
    ψ ∈ coinducedSingleSubmodule 𝒜 V ↔
      coextendScalarsBaseEquiv k A V ψ ∈ coinducedSingleCarrier 𝒜 V :=
  Iff.rfl

private theorem map_coinducedSingleSubmodule_restrictScalars :
    letI : Module k ((ModuleCat.coextendScalars (algebraMap k A)).obj (ModuleCat.of k V)) :=
      Module.restrictScalars k A _
    letI : IsScalarTower k A
        ((ModuleCat.coextendScalars (algebraMap k A)).obj (ModuleCat.of k V)) :=
      IsScalarTower.restrictScalars k A _
    ((coinducedSingleSubmodule 𝒜 V).restrictScalars k).map
        (coextendScalarsBaseEquiv k A V).toLinearMap =
      coinducedSingleCarrier 𝒜 V := by
  let _ : Module k ((ModuleCat.coextendScalars (algebraMap k A)).obj (ModuleCat.of k V)) :=
    Module.restrictScalars k A _
  let _ : IsScalarTower k A
      ((ModuleCat.coextendScalars (algebraMap k A)).obj (ModuleCat.of k V)) :=
    IsScalarTower.restrictScalars k A _
  have hcomap : (coinducedSingleSubmodule 𝒜 V).restrictScalars k =
      (coinducedSingleCarrier 𝒜 V).comap (coextendScalarsBaseEquiv k A V).toLinearMap := by
    ext ψ
    rw [Submodule.restrictScalars_mem, mem_coinducedSingleSubmodule_iff, Submodule.mem_comap,
      LinearEquiv.coe_coe]
  rw [hcomap]
  exact Submodule.map_comap_eq_of_surjective (coextendScalarsBaseEquiv k A V).surjective _

private def coinducedSingleCarrierEquiv :
    let C := coinducedSingleSubmodule 𝒜 V
    letI : Module k C := Module.restrictScalars k A C
    C ≃ₗ[k] coinducedSingleCarrier 𝒜 V :=
  letI : Module k ((ModuleCat.coextendScalars (algebraMap k A)).obj (ModuleCat.of k V)) :=
    Module.restrictScalars k A _
  letI : IsScalarTower k A
      ((ModuleCat.coextendScalars (algebraMap k A)).obj (ModuleCat.of k V)) :=
    IsScalarTower.restrictScalars k A _
  (coextendScalarsBaseEquiv k A V).ofSubmodules
    ((coinducedSingleSubmodule 𝒜 V).restrictScalars k)
    (coinducedSingleCarrier 𝒜 V)
    (map_coinducedSingleSubmodule_restrictScalars 𝒜 V)

private theorem coinducedSingleCarrierEquiv_apply_val (ψ : coinducedSingleSubmodule 𝒜 V) :
    (coinducedSingleCarrierEquiv 𝒜 V ψ).val = coextendScalarsBaseEquiv k A V ψ.val :=
  letI : Module k ((ModuleCat.coextendScalars (algebraMap k A)).obj (ModuleCat.of k V)) :=
    Module.restrictScalars k A _
  letI : IsScalarTower k A
      ((ModuleCat.coextendScalars (algebraMap k A)).obj (ModuleCat.of k V)) :=
    IsScalarTower.restrictScalars k A _
  LinearEquiv.ofSubmodules_apply (coextendScalarsBaseEquiv k A V)
    (map_coinducedSingleSubmodule_restrictScalars 𝒜 V) ψ

private theorem coinducedSingleCarrierEquiv_smul (a : A) (ψ : coinducedSingleSubmodule 𝒜 V) :
    (coinducedSingleCarrierEquiv 𝒜 V (a • ψ)).val =
      coinducedActionLinear V (coinducedSingleCarrierEquiv 𝒜 V ψ).val a :=
  LinearMap.ext fun b ↦ by
    rw [coinducedSingleCarrierEquiv_apply_val, Submodule.coe_smul,
      coextendScalarsBaseEquiv_smul_apply, coinducedSingleCarrierEquiv_apply_val]
    rfl

/-- The graded `𝒜`-module coinduced from a `k`-module `V` placed in degree zero. -/
def coinducedSingle : GradedModuleCat.{max uA v} 𝒜 :=
  let C := coinducedSingleSubmodule 𝒜 V
  letI : Module k C := Module.restrictScalars k A C
  letI : IsScalarTower k A C := IsScalarTower.restrictScalars k A C
  let G : InternalGrading k C ℤ :=
    (coinducedSingleGrading 𝒜 V).map (coinducedSingleCarrierEquiv 𝒜 V).symm
  letI : SetLike.GradedSMul 𝒜 G.piece :=
    ⟨fun {r p} a ψ ha hψ ↦ by
      rw [InternalGrading.mem_map_piece_iff, LinearEquiv.symm_symm,
        mem_coinducedSingleGrading_piece_iff] at hψ ⊢
      have hψ' : (coinducedSingleCarrierEquiv 𝒜 V ψ).val ∈
          (InternalGrading.ofDecomposition 𝒜).homPiece V p := by
        rw [InternalGrading.mem_homPiece_iff]
        simpa only [InternalGrading.ofDecomposition_piece] using hψ
      rw [coinducedSingleCarrierEquiv_smul]
      have hact := coinducedActionLinear_mem_piece 𝒜 V ha hψ'
      rw [InternalGrading.mem_homPiece_iff] at hact
      simpa only [InternalGrading.ofDecomposition_piece, vadd_eq_add] using hact⟩
  { carrier := C, grading := G }

variable {𝒜 V}

/-- Internal carrier comparison keeping `coinducedSingle` sealed in public signatures. -/
private def toCoinducedSingle : coinducedSingleCarrier 𝒜 V ≃ₗ[k] coinducedSingle 𝒜 V :=
  (coinducedSingleCarrierEquiv 𝒜 V).symm

/-- The underlying `k`-linear functional `A →ₗ[k] V` of an element of `coinducedSingle`. -/
def coinducedSingleApply : coinducedSingle 𝒜 V →ₗ[k] (A →ₗ[k] V) :=
  (coinducedSingleCarrier 𝒜 V).subtype.comp toCoinducedSingle.symm.toLinearMap

@[simp]
private theorem coinducedSingleApply_toCoinducedSingle (y : coinducedSingleCarrier 𝒜 V) :
    coinducedSingleApply (toCoinducedSingle y) = y.val := by
  simp [coinducedSingleApply]

private theorem coinducedSingleApply_eq_baseEquiv (x : coinducedSingle 𝒜 V) :
    coinducedSingleApply x =
      coextendScalarsBaseEquiv k A V
        (x.val : (ModuleCat.coextendScalars (algebraMap k A)).obj (ModuleCat.of k V)) := by
  rw [coinducedSingleApply, LinearMap.comp_apply, Submodule.coe_subtype, LinearEquiv.coe_coe]
  exact coinducedSingleCarrierEquiv_apply_val 𝒜 V x

/-- Elements of `coinducedSingle` are determined by their underlying `k`-linear maps. -/
theorem coinducedSingleApply_injective :
    Function.Injective (coinducedSingleApply (𝒜 := 𝒜) (V := V)) :=
  (Submodule.subtype_injective _).comp toCoinducedSingle.symm.injective

/-- Two elements of `coinducedSingle` agree when they agree on every element of `A`. -/
@[ext]
theorem coinducedSingle_ext {x y : coinducedSingle 𝒜 V}
    (h : ∀ b : A, coinducedSingleApply x b = coinducedSingleApply y b) : x = y :=
  coinducedSingleApply_injective (LinearMap.ext h)

/-- Scalar multiplication on `coinducedSingle` multiplies the algebra argument on the right. -/
@[simp]
theorem coinducedSingleApply_smul (a : A) (x : coinducedSingle 𝒜 V) (b : A) :
    coinducedSingleApply (a • x) b = coinducedSingleApply x (b * a) := by
  have hsmul : ((a • x : coinducedSingle 𝒜 V).val) = a • x.val :=
    Submodule.coe_smul a (x : coinducedSingleSubmodule 𝒜 V)
  rw [coinducedSingleApply_eq_baseEquiv, coinducedSingleApply_eq_baseEquiv, hsmul,
    coextendScalarsBaseEquiv_smul_apply]

/-- A `k`-linear functional `A →ₗ[k] V` lies in the range of `coinducedSingleApply` precisely
when it vanishes on all homogeneous pieces outside a finite set of degrees. -/
theorem mem_range_coinducedSingleApply_iff (ψ : A →ₗ[k] V) :
    ψ ∈ LinearMap.range (coinducedSingleApply (𝒜 := 𝒜) (V := V)) ↔
      ∃ s : Finset ℤ, ∀ q : ℤ, ∀ b ∈ 𝒜 q, q ∉ s → ψ b = 0 := by
  have hmem :=
    InternalGrading.mem_range_coeLinearMap_homPiece_iff (InternalGrading.ofDecomposition 𝒜) V ψ
  simp only [InternalGrading.ofDecomposition_piece] at hmem
  rw [← hmem]
  refine ⟨?_, fun hψ ↦ ⟨toCoinducedSingle ⟨ψ, hψ⟩, coinducedSingleApply_toCoinducedSingle _⟩⟩
  rintro ⟨x, rfl⟩
  exact (toCoinducedSingle.symm x).property

/-- An element of `coinducedSingle` has degree `p` precisely when it vanishes outside `𝒜 (-p)`. -/
@[simp]
theorem mem_coinducedSingle_piece_iff (p : ℤ) (x : coinducedSingle 𝒜 V) :
    x ∈ (coinducedSingle 𝒜 V).grading.piece p ↔
      ∀ q : ℤ, ∀ b ∈ 𝒜 q, q ≠ -p → coinducedSingleApply x b = 0 := by
  have h1 : x ∈ ((coinducedSingleGrading 𝒜 V).map toCoinducedSingle).piece p ↔
      toCoinducedSingle.symm x ∈ (coinducedSingleGrading 𝒜 V).piece p :=
    InternalGrading.mem_map_piece_iff (coinducedSingleGrading 𝒜 V) toCoinducedSingle p x
  have hval : (toCoinducedSingle.symm x).val = coinducedSingleApply x := rfl
  exact Iff.trans Iff.rfl (h1.trans (by rw [mem_coinducedSingleGrading_piece_iff, hval]))

private theorem comp_mem_coinducedSingleCarrier {V W : Type v} [AddCommGroup V] [Module k V]
    [AddCommGroup W] [Module k W] (g : V →ₗ[k] W) {ψ : A →ₗ[k] V}
    (hψ : ψ ∈ coinducedSingleCarrier 𝒜 V) :
    g.comp ψ ∈ coinducedSingleCarrier 𝒜 W := by
  rw [InternalGrading.mem_range_coeLinearMap_homPiece_iff] at hψ ⊢
  obtain ⟨s, hs⟩ := hψ
  exact ⟨s, fun q b hb hq ↦ by rw [LinearMap.comp_apply, hs q b hb hq, map_zero]⟩

private def coinducedSingleMapCarrier {V W : Type v} [AddCommGroup V] [Module k V]
    [AddCommGroup W] [Module k W] (g : V →ₗ[k] W) :
    coinducedSingle 𝒜 V →ₗ[k] coinducedSingle 𝒜 W where
  toFun x := toCoinducedSingle
    ⟨g.comp (coinducedSingleApply x),
      comp_mem_coinducedSingleCarrier (𝒜 := 𝒜) g (toCoinducedSingle.symm x).property⟩
  map_add' _ _ := coinducedSingle_ext fun _ ↦ by simp [coinducedSingleApply_toCoinducedSingle]
  map_smul' _ _ := coinducedSingle_ext fun _ ↦ by simp [coinducedSingleApply_toCoinducedSingle]

@[simp]
private theorem coinducedSingleApply_coinducedSingleMapCarrier {V W : Type v}
    [AddCommGroup V] [Module k V] [AddCommGroup W] [Module k W] (g : V →ₗ[k] W)
    (x : coinducedSingle 𝒜 V) (b : A) :
    coinducedSingleApply (coinducedSingleMapCarrier (𝒜 := 𝒜) g x) b =
      g (coinducedSingleApply x b) := by
  dsimp only [coinducedSingleMapCarrier, LinearMap.coe_mk, AddHom.coe_mk]
  rw [coinducedSingleApply_toCoinducedSingle, LinearMap.comp_apply]

variable (𝒜) in
/-- Functoriality of `coinducedSingle` in the coefficient `k`-module: postcomposing functionals
with `g : V →ₗ[k] W`. -/
def coinducedSingleMap {V W : Type v} [AddCommGroup V] [Module k V]
    [AddCommGroup W] [Module k W] (g : V →ₗ[k] W) :
    coinducedSingle 𝒜 V ⟶ coinducedSingle 𝒜 W :=
  ofHom
    { toFun := coinducedSingleMapCarrier g
      map_add' := (coinducedSingleMapCarrier g).map_add
      map_smul' := fun a x ↦ coinducedSingle_ext fun b ↦ by
        simp only [RingHom.id_apply, coinducedSingleApply_smul,
          coinducedSingleApply_coinducedSingleMapCarrier] }
    (LinearMap.isHomogeneous_def.mpr fun p x hx ↦ by
      rw [add_zero, mem_coinducedSingle_piece_iff]
      intro q b hb hq
      dsimp only [LinearMap.coe_mk, AddHom.coe_mk]
      rw [coinducedSingleApply_coinducedSingleMapCarrier,
        (mem_coinducedSingle_piece_iff p x).1 hx q b hb hq, map_zero])

/-- Evaluating `coinducedSingleMap 𝒜 g` postcomposes the underlying functional with `g`. -/
@[simp]
theorem coinducedSingleApply_coinducedSingleMap {V W : Type v} [AddCommGroup V] [Module k V]
    [AddCommGroup W] [Module k W] (g : V →ₗ[k] W) (x : coinducedSingle 𝒜 V) (b : A) :
    coinducedSingleApply ((coinducedSingleMap 𝒜 g).hom x) b = g (coinducedSingleApply x b) := by
  rw [coinducedSingleMap, hom_ofHom]
  exact coinducedSingleApply_coinducedSingleMapCarrier g x b

/-- Postcomposing with the identity map on `V` is the identity on `coinducedSingle 𝒜 V`. -/
@[simp]
theorem coinducedSingleMap_id {V : Type v} [AddCommGroup V] [Module k V] :
    coinducedSingleMap 𝒜 (LinearMap.id : V →ₗ[k] V) = 𝟙 (coinducedSingle 𝒜 V) :=
  hom_ext <| LinearMap.ext fun _ ↦ coinducedSingle_ext fun _ ↦ by simp

/-- `coinducedSingleMap` respects composition of `k`-linear maps. -/
@[simp]
theorem coinducedSingleMap_comp {V W U : Type v} [AddCommGroup V] [Module k V]
    [AddCommGroup W] [Module k W] [AddCommGroup U] [Module k U]
    (g : V →ₗ[k] W) (h : W →ₗ[k] U) :
    coinducedSingleMap 𝒜 (h.comp g) = coinducedSingleMap 𝒜 g ≫ coinducedSingleMap 𝒜 h :=
  hom_ext <| LinearMap.ext fun _ ↦ coinducedSingle_ext fun _ ↦ by simp

private def coinducedSinglePieceToHomPiece (𝒜 : ℤ → Submodule k A) [GradedAlgebra 𝒜]
    (V : Type v) [AddCommGroup V] [Module k V] (p : ℤ) :
    (coinducedSingle 𝒜 V).grading.piece p ≃ₗ[k]
      (InternalGrading.ofDecomposition 𝒜).homPiece V p where
  toFun x :=
    ⟨coinducedSingleApply x.val, (InternalGrading.mem_homPiece_iff _ V p _).2 fun q b hb hq ↦ by
      rw [InternalGrading.ofDecomposition_piece] at hb
      exact (mem_coinducedSingle_piece_iff p x.val).1 x.property q b hb hq⟩
  invFun ψ :=
    ⟨toCoinducedSingle ⟨ψ.val,
      InternalGrading.le_range_coeLinearMap ((InternalGrading.ofDecomposition 𝒜).homPiece V) p
        ψ.property⟩,
      (mem_coinducedSingle_piece_iff p _).2 fun q b hb hq ↦ by
        rw [coinducedSingleApply_toCoinducedSingle]
        exact (InternalGrading.mem_homPiece_iff _ V p _).1 ψ.property q b (by
          rw [InternalGrading.ofDecomposition_piece]; exact hb) hq⟩
  left_inv x := Subtype.ext <|
    coinducedSingleApply_injective (coinducedSingleApply_toCoinducedSingle _)
  right_inv ψ := Subtype.ext (coinducedSingleApply_toCoinducedSingle _)
  map_add' _ _ := Subtype.ext (map_add coinducedSingleApply _ _)
  map_smul' _ _ := Subtype.ext (map_smul coinducedSingleApply _ _)

variable (𝒜 V) in
/-- The degree-`p` piece of `coinducedSingle 𝒜 V` is `k`-linearly equivalent to `𝒜 (-p) →ₗ[k] V`,
via restricting the underlying functional to `𝒜 (-p)` and extending by zero on other degrees. -/
def coinducedSinglePieceEquiv (p : ℤ) :
    (coinducedSingle 𝒜 V).grading.piece p ≃ₗ[k] (𝒜 (-p) →ₗ[k] V) :=
  (coinducedSinglePieceToHomPiece 𝒜 V p).trans
    (((InternalGrading.ofDecomposition 𝒜).homPieceEquiv V p).trans
      (LinearEquiv.congrLeft V k
        (LinearEquiv.ofEq ((InternalGrading.ofDecomposition 𝒜).piece (-p)) (𝒜 (-p))
          (congrFun (InternalGrading.ofDecomposition_piece 𝒜) (-p)))))

/-- Evaluating `coinducedSinglePieceEquiv` on an element of degree `p` restricts its underlying
functional to `𝒜 (-p)`. -/
@[simp]
theorem coinducedSinglePieceEquiv_apply (p : ℤ) (x : (coinducedSingle 𝒜 V).grading.piece p)
    (b : 𝒜 (-p)) :
    coinducedSinglePieceEquiv 𝒜 V p x b = coinducedSingleApply x.val b := by
  simp only [coinducedSinglePieceEquiv, LinearEquiv.trans_apply, LinearEquiv.congrLeft_apply,
    AddEquiv.toFun_eq_coe, LinearEquiv.arrowCongrAddEquiv_apply, LinearEquiv.refl_toLinearMap,
    LinearMap.id_comp, LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.ofEq_symm,
    LinearEquiv.coe_ofEq_apply, InternalGrading.homPieceEquiv_apply]
  rfl

private theorem coinducedSingleApply_coinducedSinglePieceToHomPiece_symm (p : ℤ)
    (ψ : (InternalGrading.ofDecomposition 𝒜).homPiece V p) :
    coinducedSingleApply ((coinducedSinglePieceToHomPiece 𝒜 V p).symm ψ : coinducedSingle 𝒜 V) =
      ψ.val := by
  dsimp only [coinducedSinglePieceToHomPiece, LinearEquiv.coe_symm_mk]
  exact coinducedSingleApply_toCoinducedSingle _

/-- Evaluating the inverse of `coinducedSinglePieceEquiv` at `b : A` applies the linear map to
the degree-`(-p)` homogeneous component of `b`. -/
@[simp]
theorem coinducedSingleApply_coinducedSinglePieceEquiv_symm (p : ℤ) (φ : 𝒜 (-p) →ₗ[k] V)
    (b : A) :
    coinducedSingleApply ((coinducedSinglePieceEquiv 𝒜 V p).symm φ : coinducedSingle 𝒜 V) b =
      φ (DirectSum.decompose 𝒜 b (-p)) := by
  rw [coinducedSinglePieceEquiv, LinearEquiv.trans_symm, LinearEquiv.trans_symm,
    LinearEquiv.trans_apply, LinearEquiv.trans_apply,
    coinducedSingleApply_coinducedSinglePieceToHomPiece_symm,
    InternalGrading.homPieceEquiv_symm_apply]
  simp only [LinearEquiv.congrLeft_symm_apply, AddEquiv.invFun_eq_symm,
    LinearEquiv.arrowCongrAddEquiv_symm_apply, LinearEquiv.refl_symm,
    LinearEquiv.refl_toLinearMap, LinearMap.id_comp, LinearMap.comp_apply, LinearEquiv.coe_coe]
  exact congrArg φ
    (Subtype.ext (InternalGrading.coe_decompose_ofDecomposition_piece_apply 𝒜 b (-p)))

omit [GradedAlgebra 𝒜] in
private def coinducedSingleShiftLiftLinear {M : GradedModuleCat.{max uA v} 𝒜} (n : ℤ)
    (f : M.grading.piece n →ₗ[k] V) : M →ₗ[k] (A →ₗ[k] V) where
  toFun x :=
    { toFun := fun b ↦ f (DirectSum.decompose M.grading.piece (b • x) n)
      map_add' := fun _ _ ↦ by rw [add_smul, DirectSum.decompose_add, DirectSum.add_apply, map_add]
      map_smul' := fun _ _ ↦ by
        rw [RingHom.id_apply, smul_assoc, DirectSum.decompose_smul, DirectSum.smul_apply,
          map_smul] }
  map_add' _ _ := LinearMap.ext fun _ ↦ by
    dsimp only [LinearMap.coe_mk, AddHom.coe_mk, LinearMap.add_apply]
    rw [smul_add, DirectSum.decompose_add, DirectSum.add_apply, map_add]
  map_smul' c x := LinearMap.ext fun b ↦ by
    dsimp only [RingHom.id_apply, LinearMap.coe_mk, AddHom.coe_mk, LinearMap.smul_apply]
    rw [smul_comm b c x, DirectSum.decompose_smul, DirectSum.smul_apply, map_smul]

omit [GradedAlgebra 𝒜] in
@[simp]
private theorem coinducedSingleShiftLiftLinear_apply {M : GradedModuleCat.{max uA v} 𝒜} (n : ℤ)
    (f : M.grading.piece n →ₗ[k] V) (x : M) (b : A) :
    coinducedSingleShiftLiftLinear n f x b = f (DirectSum.decompose M.grading.piece (b • x) n) :=
  rfl

private theorem coinducedSingleShiftLiftLinear_mem_piece {M : GradedModuleCat.{max uA v} 𝒜} (n : ℤ)
    (f : M.grading.piece n →ₗ[k] V) {p : ℤ} {x : M} (hx : x ∈ M.grading.piece p) :
    coinducedSingleShiftLiftLinear n f x ∈
      (InternalGrading.ofDecomposition 𝒜).homPiece V (p - n) := by
  rw [InternalGrading.mem_homPiece_iff]
  intro q b hb _
  rw [InternalGrading.ofDecomposition_piece] at hb
  have hbx : b • x ∈ M.grading.piece (q + p) := SetLike.GradedSMul.smul_mem hb hx
  have hdec : DirectSum.decompose M.grading.piece (b • x) n = 0 :=
    Subtype.ext (DirectSum.decompose_of_mem_ne M.grading.piece hbx (by omega))
  rw [coinducedSingleShiftLiftLinear_apply, hdec, map_zero]

private theorem coinducedSingleShiftLiftLinear_mem_carrier {M : GradedModuleCat.{max uA v} 𝒜}
    (n : ℤ) (f : M.grading.piece n →ₗ[k] V) (x : M) :
    coinducedSingleShiftLiftLinear n f x ∈ coinducedSingleCarrier 𝒜 V := by
  classical
  rw [← DirectSum.sum_support_decompose M.grading.piece x, map_sum]
  exact (coinducedSingleCarrier 𝒜 V).sum_mem fun p _ ↦
    InternalGrading.le_range_coeLinearMap ((InternalGrading.ofDecomposition 𝒜).homPiece V) (p - n)
      (coinducedSingleShiftLiftLinear_mem_piece n f
        (DirectSum.decompose M.grading.piece x p).property)

private def coinducedSingleShiftLiftCarrier {M : GradedModuleCat.{max uA v} 𝒜} (n : ℤ)
    (f : M.grading.piece n →ₗ[k] V) : M →ₗ[k] coinducedSingle 𝒜 V :=
  (toCoinducedSingle (𝒜 := 𝒜) (V := V)).toLinearMap.comp
    ((coinducedSingleShiftLiftLinear n f).codRestrict (coinducedSingleCarrier 𝒜 V)
      (coinducedSingleShiftLiftLinear_mem_carrier n f))

@[simp]
private theorem coinducedSingleApply_coinducedSingleShiftLiftCarrier
    {M : GradedModuleCat.{max uA v} 𝒜} (n : ℤ) (f : M.grading.piece n →ₗ[k] V) (x : M) (b : A) :
    coinducedSingleApply (coinducedSingleShiftLiftCarrier n f x) b =
      f (DirectSum.decompose M.grading.piece (b • x) n) := by
  rw [coinducedSingleShiftLiftCarrier, LinearMap.comp_apply, LinearEquiv.coe_coe,
    coinducedSingleApply_toCoinducedSingle, LinearMap.codRestrict_apply,
    coinducedSingleShiftLiftLinear_apply]

/-- Lift a `k`-linear map on `M_n` to a graded morphism `M ⟶ (coinducedSingle 𝒜 V).shiftObj n`. -/
private def coinducedSingleShiftLift {M : GradedModuleCat.{max uA v} 𝒜} (n : ℤ)
    (f : M.grading.piece n →ₗ[k] V) : M ⟶ (coinducedSingle 𝒜 V).shiftObj n :=
  ofHom
    { toFun := coinducedSingleShiftLiftCarrier n f
      map_add' := (coinducedSingleShiftLiftCarrier n f).map_add
      map_smul' := fun a x ↦ coinducedSingle_ext fun b ↦ by
        simp only [RingHom.id_apply, coinducedSingleApply_smul,
          coinducedSingleApply_coinducedSingleShiftLiftCarrier, mul_smul] }
    (LinearMap.isHomogeneous_def.mpr fun p x hx ↦ by
      rw [add_zero, mem_shiftObj_piece_iff, mem_coinducedSingle_piece_iff]
      intro q b hb hq
      dsimp only [LinearMap.coe_mk, AddHom.coe_mk]
      rw [coinducedSingleApply_coinducedSingleShiftLiftCarrier]
      exact (InternalGrading.mem_homPiece_iff _ V (p - n) _).mp
        (coinducedSingleShiftLiftLinear_mem_piece n f hx) q b (by
          rw [InternalGrading.ofDecomposition_piece]; exact hb) hq)

private theorem coinducedSingleApply_coinducedSingleShiftLift
    {M : GradedModuleCat.{max uA v} 𝒜} (n : ℤ) (f : M.grading.piece n →ₗ[k] V) (x : M) (b : A) :
    coinducedSingleApply ((coinducedSingleShiftLift n f).hom x) b =
      f (DirectSum.decompose M.grading.piece (b • x) n) :=
  coinducedSingleApply_coinducedSingleShiftLiftCarrier n f x b

/-- **Universal property of shifted coinduced modules.** Morphisms `M ⟶ (coinducedSingle 𝒜 V){n}`
correspond `k`-linearly to `k`-linear maps `M_n →ₗ[k] V`, via evaluation at `1 : A`. -/
def coinducedSingleShiftHomEquiv (M : GradedModuleCat.{max uA v} 𝒜)
    (V : Type v) [AddCommGroup V] [Module k V] (n : ℤ) :
    (M ⟶ (coinducedSingle 𝒜 V).shiftObj n) ≃ₗ[k] (M.grading.piece n →ₗ[k] V) where
  toFun Ψ :=
    { toFun := fun x ↦ coinducedSingleApply (Ψ.hom x) 1
      map_add' := fun _ _ ↦ by simp
      map_smul' := fun c x ↦ by
        rw [RingHom.id_apply, Submodule.coe_smul_of_tower, ← algebraMap_smul A c (x : M),
          Ψ.hom.map_smul, algebraMap_smul]
        simp }
  invFun := coinducedSingleShiftLift n
  left_inv Ψ := hom_ext <| M.grading.linearMap_ext fun p x hx ↦ coinducedSingleApply_injective <|
    (InternalGrading.ofDecomposition 𝒜).linearMap_ext fun q b hb ↦ by
      rw [InternalGrading.ofDecomposition_piece] at hb
      rw [coinducedSingleApply_coinducedSingleShiftLift]
      have hbx_eq : coinducedSingleApply (Ψ.hom x) b = coinducedSingleApply (Ψ.hom (b • x)) 1 := by
        rw [Ψ.hom.map_smul, coinducedSingleApply_smul, one_mul]
      rw [hbx_eq]
      have hbx : b • x ∈ M.grading.piece (q + p) := SetLike.GradedSMul.smul_mem hb hx
      by_cases hqp : q + p = n
      · subst hqp; dsimp only [LinearMap.coe_mk, AddHom.coe_mk]
        rw [DirectSum.decompose_of_mem_same M.grading.piece hbx]
      · have hdec : DirectSum.decompose M.grading.piece (b • x) n = 0 :=
          Subtype.ext (DirectSum.decompose_of_mem_ne M.grading.piece hbx hqp)
        have hΨ := map_mem Ψ hbx
        rw [mem_shiftObj_piece_iff, mem_coinducedSingle_piece_iff] at hΨ
        simp only [hdec, map_zero, hΨ 0 1 (SetLike.GradedOne.one_mem (A := 𝒜)) (by omega)]
  right_inv f := LinearMap.ext fun x ↦ by
    dsimp only [LinearMap.coe_mk, AddHom.coe_mk]
    rw [coinducedSingleApply_coinducedSingleShiftLift, one_smul]
    exact congrArg f (Subtype.ext (DirectSum.decompose_of_mem_same M.grading.piece x.property))
  map_add' _ _ := LinearMap.ext fun _ ↦ by simp
  map_smul' _ _ := LinearMap.ext fun _ ↦ by simp

/-- The forward universal-property map evaluates at `1 : A`. -/
@[simp]
theorem coinducedSingleShiftHomEquiv_apply (M : GradedModuleCat.{max uA v} 𝒜)
    (V : Type v) [AddCommGroup V] [Module k V] (n : ℤ)
    (Ψ : M ⟶ (coinducedSingle 𝒜 V).shiftObj n) (x : M.grading.piece n) :
    coinducedSingleShiftHomEquiv M V n Ψ x = coinducedSingleApply (Ψ.hom x) 1 := by
  rw [coinducedSingleShiftHomEquiv]; rfl

/-- Evaluating `(coinducedSingleShiftHomEquiv M V n).symm f` applies `f` to the degree-`n` part
of `b • x`. -/
@[simp]
theorem coinducedSingleApply_coinducedSingleShiftHomEquiv_symm (M : GradedModuleCat.{max uA v} 𝒜)
    (V : Type v) [AddCommGroup V] [Module k V] (n : ℤ)
    (f : M.grading.piece n →ₗ[k] V) (x : M) (b : A) :
    (dsimp% only (coinducedSingleApply (((coinducedSingleShiftHomEquiv M V n).symm f).hom x) b)) =
      f (DirectSum.decompose M.grading.piece (b • x) n) :=
  coinducedSingleApply_coinducedSingleShiftLift n f x b

/-- Precomposing a morphism into `(coinducedSingle 𝒜 V).shiftObj n` restricts the degree-`n`
map. -/
theorem coinducedSingleShiftHomEquiv_comp {X Y : GradedModuleCat.{max uA v} 𝒜} (n : ℤ)
    (f : X ⟶ Y) (Ψ : Y ⟶ (coinducedSingle 𝒜 V).shiftObj n) (x : X.grading.piece n) :
    coinducedSingleShiftHomEquiv X V n (f ≫ Ψ) x =
      coinducedSingleShiftHomEquiv Y V n Ψ ⟨f.hom x, map_mem f x.property⟩ := by simp

/-- Precomposing the lifted morphism `(coinducedSingleShiftHomEquiv Y V n).symm f` with `g`
lifts the restriction of `f` along `g` in degree `n`. -/
@[reassoc (attr := simp)]
theorem comp_coinducedSingleShiftHomEquiv_symm {X Y : GradedModuleCat.{max uA v} 𝒜} (n : ℤ)
    (g : X ⟶ Y) (f : Y.grading.piece n →ₗ[k] V) :
    g ≫ (coinducedSingleShiftHomEquiv Y V n).symm f =
      (coinducedSingleShiftHomEquiv X V n).symm
        (f.comp ((g.hom.restrictScalars k).restrict fun _ hx ↦ map_mem g hx)) := by
  apply (coinducedSingleShiftHomEquiv X V n).injective
  ext x
  simp only [coinducedSingleShiftHomEquiv_apply, GradedModuleCat.hom_comp, LinearMap.comp_apply,
    coinducedSingleApply_coinducedSingleShiftHomEquiv_symm, one_smul]
  congr 1
  ext
  rw [DirectSum.decompose_of_mem_same Y.grading.piece (map_mem g x.property)]
  exact congrArg g.hom (DirectSum.decompose_of_mem_same X.grading.piece x.property).symm

/-- Postcomposing a morphism into `(coinducedSingle 𝒜 V).shiftObj n` with a coefficient-module map
postcomposes the induced degree-`n` map. -/
@[simp]
theorem coinducedSingleShiftHomEquiv_comp_coinducedSingleMap
    (M : GradedModuleCat.{max uA v} 𝒜) {V W : Type v} [AddCommGroup V] [Module k V]
    [AddCommGroup W] [Module k W] (n : ℤ) (g : V →ₗ[k] W)
    (Ψ : M ⟶ (coinducedSingle 𝒜 V).shiftObj n) :
    coinducedSingleShiftHomEquiv M W n (Ψ ≫ (shiftFunctor n).map (coinducedSingleMap 𝒜 g)) =
      g.comp (coinducedSingleShiftHomEquiv M V n Ψ) := by
  ext x
  simp only [coinducedSingleShiftHomEquiv_apply, LinearMap.comp_apply, hom_comp,
    hom_shiftFunctor_map, coinducedSingleApply_coinducedSingleMap]

/-- Postcomposing a shifted coinduced lift with a coefficient-module map lifts the postcomposed
degree-`n` map. -/
@[reassoc (attr := simp)]
theorem coinducedSingleShiftHomEquiv_symm_comp_coinducedSingleMap
    (M : GradedModuleCat.{max uA v} 𝒜) {V W : Type v} [AddCommGroup V] [Module k V]
    [AddCommGroup W] [Module k W] (n : ℤ) (g : V →ₗ[k] W) (f : M.grading.piece n →ₗ[k] V) :
    (coinducedSingleShiftHomEquiv M V n).symm f ≫
        (shiftFunctor n).map (coinducedSingleMap 𝒜 g) =
      (coinducedSingleShiftHomEquiv M W n).symm (g.comp f) :=
  (coinducedSingleShiftHomEquiv M W n).injective (by simp)

/-- **Universal property of degree-zero coinduced modules.** Morphisms `M ⟶ coinducedSingle 𝒜 V`
correspond `k`-linearly to `k`-linear maps `M_0 →ₗ[k] V`. -/
def coinducedSingleHomEquiv (M : GradedModuleCat.{max uA v} 𝒜)
    (V : Type v) [AddCommGroup V] [Module k V] :
    (M ⟶ coinducedSingle 𝒜 V) ≃ₗ[k] (M.grading.piece 0 →ₗ[k] V) :=
  (Linear.homCongr k (Iso.refl M) ((shiftFunctorZeroIso 𝒜).app (coinducedSingle 𝒜 V)).symm).trans
    (coinducedSingleShiftHomEquiv M V 0)

/-- Evaluating a degree-zero coinduced morphism reads its values on `M_0` at `1 : A`. -/
@[simp]
theorem coinducedSingleHomEquiv_apply (M : GradedModuleCat.{max uA v} 𝒜)
    (V : Type v) [AddCommGroup V] [Module k V]
    (Ψ : M ⟶ coinducedSingle 𝒜 V) (x : M.grading.piece 0) :
    coinducedSingleHomEquiv M V Ψ x = coinducedSingleApply (Ψ.hom x) 1 := by
  simp [coinducedSingleHomEquiv, Linear.homCongr_apply]

/-- Evaluating `(coinducedSingleHomEquiv M V).symm f` applies `f` to `(b • x)_0`. -/
@[simp]
theorem coinducedSingleApply_coinducedSingleHomEquiv_symm (M : GradedModuleCat.{max uA v} 𝒜)
    (V : Type v) [AddCommGroup V] [Module k V]
    (f : M.grading.piece 0 →ₗ[k] V) (x : M) (b : A) :
    coinducedSingleApply (((coinducedSingleHomEquiv M V).symm f).hom x) b =
      f (DirectSum.decompose M.grading.piece (b • x) 0) := by
  simp [coinducedSingleHomEquiv, Linear.homCongr_symm_apply]

/-- Precomposing a morphism into `coinducedSingle 𝒜 V` restricts the degree-zero map. -/
theorem coinducedSingleHomEquiv_comp {X Y : GradedModuleCat.{max uA v} 𝒜} (f : X ⟶ Y)
    (Ψ : Y ⟶ coinducedSingle 𝒜 V) (x : X.grading.piece 0) :
    coinducedSingleHomEquiv X V (f ≫ Ψ) x =
      coinducedSingleHomEquiv Y V Ψ ⟨f.hom x, map_mem f x.property⟩ := by simp

/-- Postcomposing a morphism into `coinducedSingle 𝒜 V` with a coefficient-module map postcomposes
the induced degree-zero map. -/
@[simp]
theorem coinducedSingleHomEquiv_comp_coinducedSingleMap
    (M : GradedModuleCat.{max uA v} 𝒜) {V W : Type v} [AddCommGroup V] [Module k V]
    [AddCommGroup W] [Module k W] (g : V →ₗ[k] W) (Ψ : M ⟶ coinducedSingle 𝒜 V) :
    coinducedSingleHomEquiv M W (Ψ ≫ coinducedSingleMap 𝒜 g) =
      g.comp (coinducedSingleHomEquiv M V Ψ) := by
  have hnat : coinducedSingleMap 𝒜 g ≫ ((shiftFunctorZeroIso 𝒜).app (coinducedSingle 𝒜 W)).inv =
      ((shiftFunctorZeroIso 𝒜).app (coinducedSingle 𝒜 V)).inv ≫
        (shiftFunctor 0).map (coinducedSingleMap 𝒜 g) := by
    simpa using (shiftFunctorZeroIso 𝒜).inv.naturality (coinducedSingleMap 𝒜 g)
  dsimp only [coinducedSingleHomEquiv, LinearEquiv.trans_apply, Linear.homCongr_apply]
  simp only [Iso.symm_hom, Category.assoc]
  rw [hnat, ← Category.assoc]
  exact coinducedSingleShiftHomEquiv_comp_coinducedSingleMap M 0 g
    (Ψ ≫ ((shiftFunctorZeroIso 𝒜).app (coinducedSingle 𝒜 V)).inv)

/-- Postcomposing a degree-zero coinduced lift with a coefficient-module map lifts the postcomposed
degree-zero map. -/
@[reassoc (attr := simp)]
theorem coinducedSingleHomEquiv_symm_comp_coinducedSingleMap
    (M : GradedModuleCat.{max uA v} 𝒜) {V W : Type v} [AddCommGroup V] [Module k V]
    [AddCommGroup W] [Module k W] (g : V →ₗ[k] W) (f : M.grading.piece 0 →ₗ[k] V) :
    (coinducedSingleHomEquiv M V).symm f ≫ coinducedSingleMap 𝒜 g =
      (coinducedSingleHomEquiv M W).symm (g.comp f) :=
  (coinducedSingleHomEquiv M W).injective (by simp)

private theorem injective_coinducedSingle_of_extension {V : Type v} [AddCommGroup V] [Module k V]
    (hext : ∀ ⦃M N : Type (max uA v)⦄ [AddCommGroup M] [AddCommGroup N] [Module k M] [Module k N]
      (f : M →ₗ[k] N), Function.Injective f → ∀ g : M →ₗ[k] V,
        ∃ h : N →ₗ[k] V, ∀ x, h (f x) = g x) :
    Injective (coinducedSingle 𝒜 V) where
  factors {X Y} g f hf := by
    have hinj : Function.Injective f.hom := (mono_iff_injective f).mp hf
    let f₀ : X.grading.piece 0 →ₗ[k] Y.grading.piece 0 :=
      (f.hom.restrictScalars k).restrict fun _ hx ↦ map_mem f hx
    obtain ⟨h₀, hh₀⟩ := hext f₀ (fun _ _ hxy ↦ Subtype.ext (hinj (congrArg Subtype.val hxy)))
      (coinducedSingleHomEquiv X V g)
    refine ⟨(coinducedSingleHomEquiv Y V).symm h₀,
      (coinducedSingleHomEquiv X V).injective (LinearMap.ext fun x ↦ ?_)⟩
    rw [coinducedSingleHomEquiv_comp, LinearEquiv.apply_symm_apply]; exact hh₀ x

/-- If `V` satisfies Baer's criterion over `k`, `coinducedSingle 𝒜 V` is injective. -/
theorem injective_coinducedSingle_of_baer {V : Type v} [AddCommGroup V] [Module k V]
    (hV : Module.Baer k V) : Injective (coinducedSingle 𝒜 V) :=
  injective_coinducedSingle_of_extension fun _ _ _ _ _ _ f hf g ↦
    let ⟨h₀, hh₀⟩ := hV.extension_property f hf g; ⟨h₀, LinearMap.congr_fun hh₀⟩

/-- Coinducing an injective `k`-module produces an injective graded `𝒜`-module. -/
instance injective_coinducedSingle (V : Type (max uA v)) [AddCommGroup V] [Module k V]
    [inj : Module.Injective k V] : Injective (coinducedSingle 𝒜 V) :=
  injective_coinducedSingle_of_extension inj.out

end Single

section Family

variable {k : Type uk} [CommRing k] {A : Type uA} [Ring A] [Algebra k A]
  (𝒜 : ℤ → Submodule k A) [GradedAlgebra 𝒜]
  {I : Type (max uA v)} (d : I → ℤ)

/-- The graded module coinduced from a family of `k`-modules `V i` placed in degrees `d i`,
realized as the degreewise product of shifted single-target coinduced modules. -/
abbrev coinduced (V : I → Type v) [∀ i, AddCommGroup (V i)] [∀ i, Module k (V i)] :
    GradedModuleCat.{max uA v} 𝒜 :=
  product fun i ↦ (coinducedSingle 𝒜 (V i)).shiftObj (d i)

/-- Componentwise morphism on coinduced graded modules induced by a family of `k`-linear maps
`g i : V i →ₗ[k] W i`. -/
def coinducedMap {V W : I → Type v} [∀ i, AddCommGroup (V i)] [∀ i, Module k (V i)]
    [∀ i, AddCommGroup (W i)] [∀ i, Module k (W i)] (g : ∀ i, V i →ₗ[k] W i) :
    coinduced 𝒜 d V ⟶ coinduced 𝒜 d W :=
  productLift _ fun i ↦ productπ _ i ≫ (shiftFunctor (d i)).map (coinducedSingleMap 𝒜 (g i))

/-- Projecting `coinducedMap 𝒜 d g` onto the `i`-th factor commutes with the shifted single map.
-/
@[reassoc (attr := simp)]
theorem coinducedMap_π {V W : I → Type v} [∀ i, AddCommGroup (V i)] [∀ i, Module k (V i)]
    [∀ i, AddCommGroup (W i)] [∀ i, Module k (W i)] (g : ∀ i, V i →ₗ[k] W i) (i : I) :
    coinducedMap 𝒜 d g ≫ productπ _ i =
      productπ _ i ≫ (shiftFunctor (d i)).map (coinducedSingleMap 𝒜 (g i)) :=
  productLift_π _ _ i

/-- Postcomposing a family with identity maps yields the identity on `coinduced 𝒜 d V`. -/
@[simp]
theorem coinducedMap_id {V : I → Type v} [∀ i, AddCommGroup (V i)] [∀ i, Module k (V i)] :
    coinducedMap 𝒜 d (fun i ↦ (LinearMap.id : V i →ₗ[k] V i)) = 𝟙 (coinduced 𝒜 d V) :=
  product_hom_ext _ fun i ↦ by simp

/-- `coinducedMap` respects componentwise composition of `k`-linear maps. -/
@[simp]
theorem coinducedMap_comp {V W U : I → Type v} [∀ i, AddCommGroup (V i)] [∀ i, Module k (V i)]
    [∀ i, AddCommGroup (W i)] [∀ i, Module k (W i)]
    [∀ i, AddCommGroup (U i)] [∀ i, Module k (U i)]
    (g : ∀ i, V i →ₗ[k] W i) (h : ∀ i, W i →ₗ[k] U i) :
    coinducedMap 𝒜 d (fun i ↦ (h i).comp (g i)) = coinducedMap 𝒜 d g ≫ coinducedMap 𝒜 d h :=
  product_hom_ext _ fun i ↦ by simp

section UnivProp

variable {𝒜 d}

/-- **Universal property of coinduced graded modules.** Morphisms into `coinduced 𝒜 d V`
correspond `k`-linearly to families of `k`-linear maps `M_{d i} →ₗ[k] V i`. -/
def coinducedHomEquiv {V : I → Type v} [∀ i, AddCommGroup (V i)] [∀ i, Module k (V i)]
    (M : GradedModuleCat.{max uA v} 𝒜) :
    (M ⟶ coinduced 𝒜 d V) ≃ₗ[k] ∀ i, M.grading.piece (d i) →ₗ[k] V i where
  toFun Ψ i := coinducedSingleShiftHomEquiv M (V i) (d i) (Ψ ≫ productπ _ i)
  invFun f := productLift _ fun i ↦ (coinducedSingleShiftHomEquiv M (V i) (d i)).symm (f i)
  left_inv Ψ := product_hom_ext _ fun i ↦ by simp
  right_inv f := funext fun i ↦ by dsimp only; rw [productLift_π, LinearEquiv.apply_symm_apply]
  map_add' _ _ := funext fun _ ↦ by simp [Preadditive.add_comp]
  map_smul' _ _ := funext fun _ ↦ by simp [Linear.smul_comp]

/-- Applying `coinducedHomEquiv` at `i` projects onto the `i`-th factor and evaluates at `1`. -/
@[simp]
theorem coinducedHomEquiv_apply {V : I → Type v} [∀ i, AddCommGroup (V i)] [∀ i, Module k (V i)]
    (M : GradedModuleCat.{max uA v} 𝒜) (Ψ : M ⟶ coinduced 𝒜 d V) (i : I) :
    coinducedHomEquiv M Ψ i = coinducedSingleShiftHomEquiv M (V i) (d i) (Ψ ≫ productπ _ i) := by
  rw [coinducedHomEquiv]; rfl

/-- Following `(coinducedHomEquiv M).symm f` with `productπ _ i` recovers the `i`-th lift. -/
@[reassoc (attr := simp)]
theorem coinducedHomEquiv_symm_π {V : I → Type v} [∀ i, AddCommGroup (V i)] [∀ i, Module k (V i)]
    (M : GradedModuleCat.{max uA v} 𝒜)
    (f : ∀ i, M.grading.piece (d i) →ₗ[k] V i) (i : I) :
    (coinducedHomEquiv M).symm f ≫ productπ _ i =
      (coinducedSingleShiftHomEquiv M (V i) (d i)).symm (f i) := by
  rw [coinducedHomEquiv]; dsimp only [LinearEquiv.coe_symm_mk]
  rw [productLift_π]

/-- Precomposing a morphism into `coinduced 𝒜 d V` restricts each degree-`d i` map. -/
theorem coinducedHomEquiv_comp {V : I → Type v} [∀ i, AddCommGroup (V i)] [∀ i, Module k (V i)]
    {X Y : GradedModuleCat.{max uA v} 𝒜} (f : X ⟶ Y) (Ψ : Y ⟶ coinduced 𝒜 d V) (i : I)
    (x : X.grading.piece (d i)) :
    coinducedHomEquiv X (f ≫ Ψ) i x =
      coinducedHomEquiv Y Ψ i ⟨f.hom x, map_mem f x.property⟩ := by
  simp

/-- Precomposing `(coinducedHomEquiv Y).symm f` with `g` lifts the restricted maps. -/
@[reassoc (attr := simp)]
theorem comp_coinducedHomEquiv_symm {V : I → Type v} [∀ i, AddCommGroup (V i)]
    [∀ i, Module k (V i)] {X Y : GradedModuleCat.{max uA v} 𝒜} (g : X ⟶ Y)
    (f : ∀ i, Y.grading.piece (d i) →ₗ[k] V i) :
    g ≫ (coinducedHomEquiv Y).symm f =
      (coinducedHomEquiv X).symm
        (fun i ↦ (f i).comp ((g.hom.restrictScalars k).restrict fun _ hx ↦ map_mem g hx)) :=
  product_hom_ext _ fun i ↦ by simp

/-- Postcomposing a morphism into `coinduced 𝒜 d V` with `coinducedMap 𝒜 d g` postcomposes each
induced degree-`d i` map with `g i`. -/
@[simp]
theorem coinducedHomEquiv_comp_coinducedMap (M : GradedModuleCat.{max uA v} 𝒜)
    {V W : I → Type v} [∀ i, AddCommGroup (V i)] [∀ i, Module k (V i)]
    [∀ i, AddCommGroup (W i)] [∀ i, Module k (W i)]
    (g : ∀ i, V i →ₗ[k] W i) (Ψ : M ⟶ coinduced 𝒜 d V) :
    coinducedHomEquiv M (Ψ ≫ coinducedMap 𝒜 d g) = fun i ↦ (g i).comp (coinducedHomEquiv M Ψ i) :=
  funext fun i ↦ by
    rw [coinducedHomEquiv_apply, Category.assoc, coinducedMap_π, ← Category.assoc,
      coinducedSingleShiftHomEquiv_comp_coinducedSingleMap, coinducedHomEquiv_apply]

/-- Postcomposing `(coinducedHomEquiv M).symm f` with `coinducedMap 𝒜 d g` lifts the postcomposed
family. -/
@[reassoc (attr := simp)]
theorem coinducedHomEquiv_symm_comp_coinducedMap (M : GradedModuleCat.{max uA v} 𝒜)
    {V W : I → Type v} [∀ i, AddCommGroup (V i)] [∀ i, Module k (V i)]
    [∀ i, AddCommGroup (W i)] [∀ i, Module k (W i)]
    (g : ∀ i, V i →ₗ[k] W i) (f : ∀ i, M.grading.piece (d i) →ₗ[k] V i) :
    (coinducedHomEquiv M).symm f ≫ coinducedMap 𝒜 d g =
      (coinducedHomEquiv M).symm (fun i ↦ (g i).comp (f i)) :=
  product_hom_ext _ fun i ↦ by simp

/-- If every `V i` satisfies Baer's criterion over `k`, `coinduced 𝒜 d V` is injective. -/
theorem injective_coinduced_of_baer {V : I → Type v} [∀ i, AddCommGroup (V i)]
    [∀ i, Module k (V i)] (hV : ∀ i, Module.Baer k (V i)) :
    Injective (coinduced 𝒜 d V) := by
  have (i : I) : Injective (coinducedSingle 𝒜 (V i)) := injective_coinducedSingle_of_baer (hV i)
  infer_instance

end UnivProp

/-- Coinducing a family of injective `k`-modules gives an injective graded `𝒜`-module. -/
instance injective_coinduced (W : I → Type (max uA v)) [∀ i, AddCommGroup (W i)]
    [∀ i, Module k (W i)] [∀ i, Module.Injective k (W i)] : Injective (coinduced 𝒜 d W) :=
  inferInstance

end Family

section EnoughInjectives

variable {k : Type uk} [CommRing k] {A : Type uA} [Ring A] [Algebra k A]
  {𝒜 : ℤ → Submodule k A} [GradedAlgebra 𝒜]

private theorem enoughInjectives_of_small [Small.{max uA v} k] :
    EnoughInjectives (GradedModuleCat.{max uA v} 𝒜) where
  presentation M := by
    let P (s : ℤ) := Injective.under (ModuleCat.of k (M.grading.piece s))
    let ι (s : ℤ) : ModuleCat.of k (M.grading.piece s) ⟶ P s := Injective.ι _
    have (s : ℤ) : Module.Injective k (P s) :=
      Module.injective_module_of_injective_object k (P s)
        (inj := Injective.injective_under (ModuleCat.of k (M.grading.piece s)))
    let Q := coinduced 𝒜 (fun j : ULift.{max uA v} ℤ ↦ j.down) (fun j ↦ P j.down)
    let f : M ⟶ Q := (coinducedHomEquiv M).symm fun j ↦ (ι j.down).hom
    have hf : Function.Injective f.hom := by
      rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
      intro z hz
      apply (DirectSum.decompose M.grading.piece).injective
      rw [DirectSum.decompose_zero]
      refine DirectSum.ext fun s ↦ ((ModuleCat.mono_iff_injective (ι s)).mp inferInstance) ?_
      have hfac : f ≫ productπ _ (ULift.up s) =
          (coinducedSingleShiftHomEquiv M (P s) s).symm (ι s).hom :=
        coinducedHomEquiv_symm_π M _ (ULift.up s)
      have heval := congrArg
        (fun g : M ⟶ (coinducedSingle 𝒜 (P s)).shiftObj s ↦ coinducedSingleApply (g.hom z) 1) hfac
      simpa [LinearMap.mem_ker.mp hz] using heval.symm
    have : Mono f := (mono_iff_injective f).mpr hf
    exact ⟨{ J := Q, f := f }⟩

/-- In any module universe `max uA v` at least that of `A`, `GradedModuleCat.{max uA v} 𝒜` has
enough injectives, with no smallness assumption on the base ring `k`. -/
instance enoughInjectives : EnoughInjectives (GradedModuleCat.{max uA v} 𝒜) :=
  (restrictBaseEquivalence ℤ 𝒜).enoughInjectives_iff.2 enoughInjectives_of_small

end EnoughInjectives

end TauCeti.GradedModuleCat
