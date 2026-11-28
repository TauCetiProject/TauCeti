/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
public import Mathlib.Topology.Algebra.Constructions
public import Mathlib.Topology.Instances.Matrix
public import TauCeti.RingTheory.DedekindDomain.FiniteAdeleRing.Place
import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Map
import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Subalgebra
import TauCeti.LinearAlgebra.Matrix.SpecialLinearGroup.Basic
import TauCeti.Topology.Algebra.Matrix.GeneralLinearGroup.Basic

/-!
# Integral matrices over the finite adeles

For a Dedekind domain `R` with fraction field `K` (for instance the ring of integers of a number
field), write `𝔸_f` for the finite adeles and `Ô = ∏_v 𝒪_v` for the integral ones. For a finite
index type `ι` of size `n`, this file studies the inclusion `GL_n(Ô) → GL_n(𝔸_f)` induced by
`Ô ⊆ 𝔸_f` (`IsDedekindDomain.FiniteAdeleRing.integralGL`).

It is injective, and its image consists of the matrices whose entries and inverse entries are
integral; it is an open embedding, as `Ô` is open in `𝔸_f`. A matrix of `GL_n(Ô)` carries the
integral vectors `Ô^n` onto themselves, and a matrix of `GL_n(K)` of determinant `1` with integral
entries comes from `SL_n(R)`. Membership in the image of a subgroup of `GL_n(Ô)` cut out by a
condition on the entries is again a condition on the entries, which is how the congruence levels
of `GL₂(𝔸_f)` (`TauCeti.RingTheory.DedekindDomain.FiniteAdeleRing.CongruenceLevel`) are described.
These are the cases `Ô ⊆ 𝔸_f` of the general statements for a subalgebra
(`Matrix.GeneralLinearGroup.mem_range_map_val_iff`,
`Matrix.GeneralLinearGroup.forall_mulVec_mem_iff`,
`Matrix.GeneralLinearGroup.mem_map_map_val_iff`) and for an open embedding
(`Topology.IsOpenEmbedding.generalLinearGroup_map`).

## Main declarations

* `IsDedekindDomain.FiniteAdeleRing.integralGL`: the inclusion `GL_n(Ô) → GL_n(𝔸_f)`, which is
  `Matrix.GeneralLinearGroup.map` along `Ô ⊆ 𝔸_f`
  (`IsDedekindDomain.FiniteAdeleRing.integralGL_def`).
* `IsDedekindDomain.FiniteAdeleRing.mem_range_integralGL_iff`: its range is the set of matrices
  whose entries and inverse entries are integral.
* `IsDedekindDomain.FiniteAdeleRing.isOpenEmbedding_integralGL`: it is an open embedding.
* `IsDedekindDomain.FiniteAdeleRing.forall_mulVec_mem_integralAdeles_iff`: a matrix of `GL_n(Ô)`
  carries a vector to an integral vector exactly when the vector is integral.
* `IsDedekindDomain.FiniteAdeleRing.mem_range_mapGL_of_det_eq_one`: a matrix in `GL_n(K)` of
  determinant `1` whose entries are integral at every finite place comes from `SL_n(R)`.
* `IsDedekindDomain.FiniteAdeleRing.mem_map_integralGL_iff`: entrywise membership in the image of
  a subgroup of `GL_n(Ô)`.
* `IsDedekindDomain.FiniteAdeleRing.generalLinearGroup_ext`: a matrix of `GL_n(𝔸_f)` is determined
  by its components at the finite places.
* `IsDedekindDomain.FiniteAdeleRing.eventually_map_proj_mem_range`: the component at `v` of a
  matrix of `GL_n(𝔸_f)` lies in `GL_n(𝒪_v)` for all but finitely many finite places `v`.
* `IsDedekindDomain.FiniteAdeleRing.det_integralGL`,
  `IsDedekindDomain.FiniteAdeleRing.map_det_map_integralGL`: compatibility with determinants.
-/

public section
noncomputable section

open Topology
open scoped Matrix

namespace IsDedekindDomain.FiniteAdeleRing

variable {R : Type*} [CommRing R] [IsDedekindDomain R]
variable (K : Type*) [Field K] [Algebra R K] [IsFractionRing R K]
variable (ι : Type*) [Fintype ι] [DecidableEq ι]

/-- The inclusion `GL_n(Ô) → GL_n(𝔸_f)` induced by `Ô ⊆ 𝔸_f`, for a finite index type `ι` of
size `n`. -/
def integralGL : GL ι (integralAdeles R K) →* GL ι 𝔸ᶠ[R, K] :=
  Matrix.GeneralLinearGroup.map (integralAdeles R K).val.toRingHom

/-- The inclusion `GL_n(Ô) → GL_n(𝔸_f)` is `Matrix.GeneralLinearGroup.map` along `Ô ⊆ 𝔸_f`, so the
general lemmas about `Matrix.GeneralLinearGroup.map` apply to it. -/
theorem integralGL_def :
    integralGL K ι = Matrix.GeneralLinearGroup.map (integralAdeles R K).val.toRingHom :=
  (rfl)

variable {K ι}

/-- The entries of the image of an integral matrix. -/
@[simp]
theorem integralGL_apply (g : GL ι (integralAdeles R K)) (i j : ι) :
    (integralGL K ι g : Matrix ι ι 𝔸ᶠ[R, K]) i j =
      (g : Matrix ι ι (integralAdeles R K)) i j :=
  (rfl)

/-- The entries of the inverse of the image of an integral matrix. -/
@[simp]
theorem integralGL_inv_apply (g : GL ι (integralAdeles R K)) (i j : ι) :
    (↑(integralGL K ι g)⁻¹ : Matrix ι ι 𝔸ᶠ[R, K]) i j =
      (↑g⁻¹ : Matrix ι ι (integralAdeles R K)) i j :=
  (rfl)

/-- The determinant of the image in `GL_n(𝔸_f)` of a matrix of `GL_n(Ô)` is the image in `𝔸_f^×`
of its determinant. -/
@[simp]
theorem det_integralGL (g : GL ι (integralAdeles R K)) :
    Matrix.GeneralLinearGroup.det (integralGL K ι g) =
      Units.map ((integralAdeles R K).val.toRingHom : integralAdeles R K →* 𝔸ᶠ[R, K])
        (Matrix.GeneralLinearGroup.det g) :=
  Matrix.GeneralLinearGroup.map_det _ g

/-- The determinant of the image in `GL_n(𝔸_f)` of a subgroup `H ≤ GL_n(Ô)` is the image in
`𝔸_f^×` of the determinant of `H`. -/
theorem map_det_map_integralGL (H : Subgroup (GL ι (integralAdeles R K))) :
    (H.map (integralGL K ι)).map Matrix.GeneralLinearGroup.det =
      (H.map Matrix.GeneralLinearGroup.det).map
        (Units.map ((integralAdeles R K).val.toRingHom : integralAdeles R K →* 𝔸ᶠ[R, K])) := by
  rw [Subgroup.map_map, Subgroup.map_map]
  congr 1
  exact MonoidHom.ext fun g ↦ det_integralGL g

variable (K ι) in
/-- The inclusion `GL_n(Ô) → GL_n(𝔸_f)` is injective. -/
theorem integralGL_injective : Function.Injective (integralGL K ι (R := R)) :=
  Matrix.GeneralLinearGroup.map_injective Subtype.val_injective

/-- A matrix in `GL_n(𝔸_f)` lies in `GL_n(Ô)` exactly when its entries and the entries of its
inverse are integral. -/
theorem mem_range_integralGL_iff {g : GL ι 𝔸ᶠ[R, K]} :
    g ∈ (integralGL K ι).range ↔
      (∀ i j, (g : Matrix ι ι 𝔸ᶠ[R, K]) i j ∈ integralAdeles R K) ∧
        ∀ i j, (↑g⁻¹ : Matrix ι ι 𝔸ᶠ[R, K]) i j ∈ integralAdeles R K :=
  Matrix.GeneralLinearGroup.mem_range_map_val_iff (integralAdeles R K) g

/-- **Integral matrices preserve integral vectors.** For `g ∈ GL_n(Ô)`, the vector `g v` is
integral exactly when `v` is: the entries of `g` and of `g⁻¹` are integral. -/
theorem forall_mulVec_mem_integralAdeles_iff {g : GL ι 𝔸ᶠ[R, K]}
    (hg : g ∈ (integralGL K ι).range) {v : ι → 𝔸ᶠ[R, K]} :
    (∀ i, ((g : Matrix ι ι 𝔸ᶠ[R, K]) *ᵥ v) i ∈ integralAdeles R K) ↔
      ∀ i, v i ∈ integralAdeles R K :=
  Matrix.GeneralLinearGroup.forall_mulVec_mem_iff hg

/-- A matrix in `GL_n(K)` of determinant `1` whose entries are integral at every finite place,
that is whose diagonal images in `𝔸_f` lie in `Ô`, comes from `SL_n(R)`. -/
theorem mem_range_mapGL_of_det_eq_one {γ : GL ι K}
    (hdet : Matrix.GeneralLinearGroup.det γ = 1)
    (hint : ∀ i j, algebraMap K 𝔸ᶠ[R, K] ((γ : Matrix ι ι K) i j) ∈ integralAdeles R K) :
    γ ∈ (Matrix.SpecialLinearGroup.mapGL (n := ι) (R := R) K).range := by
  have hent (i j : ι) : (γ : Matrix ι ι K) i j ∈ (algebraMap R K).range :=
    (algebraMap_mem_integralAdeles_iff (R := R) _).1 (hint i j)
  obtain ⟨σ, hσ⟩ := (Matrix.SpecialLinearGroup.mem_range_map_iff (IsFractionRing.injective R K)
    ⟨(γ : Matrix ι ι K), by simpa using congrArg Units.val hdet⟩).mpr hent
  exact ⟨σ, Units.ext ((Matrix.SpecialLinearGroup.mapGL_coe_matrix σ).trans
    (congrArg Subtype.val hσ))⟩

variable (K ι) in
/-- The inclusion `GL_n(Ô) → GL_n(𝔸_f)` is an open embedding, as `Ô ⊆ 𝔸_f` is one. -/
theorem isOpenEmbedding_integralGL : IsOpenEmbedding (integralGL K ι (R := R)) :=
  (isOpen_integralAdeles R K).isOpenEmbedding_subtypeVal.generalLinearGroup_map

variable (K ι) in
/-- The inclusion `GL_n(Ô) → GL_n(𝔸_f)` is continuous. -/
theorem continuous_integralGL : Continuous (integralGL K ι (R := R)) :=
  (isOpenEmbedding_integralGL K ι).continuous

variable (ι) in
/-- Entrywise membership in the image of a subgroup `H ≤ GL_n(Ô)`, when membership in `H` is a
condition `P` on the matrix entries: integral entries, integral inverse entries, and `P` for the
matrix of entries viewed in `Ô`. -/
theorem mem_map_integralGL_iff {H : Subgroup (GL ι (integralAdeles R K))}
    {P : Matrix ι ι (integralAdeles R K) → Prop} (hH : ∀ h, h ∈ H ↔ P h)
    {g : GL ι 𝔸ᶠ[R, K]} :
    g ∈ H.map (integralGL K ι) ↔
      ∃ (hg : ∀ i j, (g : Matrix ι ι 𝔸ᶠ[R, K]) i j ∈ integralAdeles R K),
        (∀ i j, (↑g⁻¹ : Matrix ι ι 𝔸ᶠ[R, K]) i j ∈ integralAdeles R K) ∧
          P (Matrix.of fun i j ↦ ⟨_, hg i j⟩) :=
  Matrix.GeneralLinearGroup.mem_map_map_val_iff hH

/-! ### Components at the finite places -/

/-- A matrix of `GL_n(𝔸_f)` is determined by its components at the finite places. -/
theorem generalLinearGroup_ext {g h : GL ι 𝔸ᶠ[R, K]}
    (H : ∀ v : HeightOneSpectrum R, Matrix.GeneralLinearGroup.map (proj K v).toRingHom g =
      Matrix.GeneralLinearGroup.map (proj K v).toRingHom h) : g = h := by
  refine Units.ext <| Matrix.ext fun i j ↦ ext K fun v ↦ ?_
  simpa using congrArg (fun x : GL ι (v.adicCompletion K) ↦ x.val i j) (H v)

/-- **Almost all components are integral.** The component at `v` of a matrix of `GL_n(𝔸_f)` lies
in the image `GL_n(𝒪_v)` of the general linear group over the local integers for all but finitely
many finite places `v`: the entries of the matrix and of its inverse are integral there. -/
theorem eventually_map_proj_mem_range (g : GL ι 𝔸ᶠ[R, K]) :
    ∀ᶠ v in Filter.cofinite, Matrix.GeneralLinearGroup.map (proj K v).toRingHom g ∈
      (Matrix.GeneralLinearGroup.map (n := ι) (v.adicCompletionIntegers K).subtype).range := by
  have hS (v : HeightOneSpectrum R) (x : v.adicCompletion K) :
      x ∈ (v.adicCompletionIntegers K).subtype.range ↔ x ∈ v.adicCompletionIntegers K :=
    ⟨fun ⟨y, hy⟩ ↦ hy ▸ y.property, fun h ↦ ⟨⟨x, h⟩, rfl⟩⟩
  have hent (A : Matrix ι ι 𝔸ᶠ[R, K]) :
      ∀ᶠ v in Filter.cofinite, ∀ i j, A i j v ∈ v.adicCompletionIntegers K :=
    Filter.eventually_all.2 fun i ↦ Filter.eventually_all.2 fun j ↦
      (A i j).cofinite_mem_adicCompletionIntegers
  filter_upwards [hent g, hent ↑g⁻¹] with v h₁ h₂
  simpa only [Matrix.GeneralLinearGroup.mem_range_map_iff_of_injective
    (ValuationSubring.subtype_injective _), hS, ← map_inv, Matrix.GeneralLinearGroup.map_apply,
    Matrix.map_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, ContinuousAlgHom.coe_coe,
    proj_apply] using And.intro h₁ h₂

end IsDedekindDomain.FiniteAdeleRing
