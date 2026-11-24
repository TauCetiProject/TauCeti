/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.Lattice.Full
public import Mathlib.LinearAlgebra.Pi
public import Mathlib.LinearAlgebra.StdBasis
public import Mathlib.LinearAlgebra.TensorProduct.Projective
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.Localization.Module
public import Mathlib.RingTheory.TensorProduct.Finite
public import Mathlib.RingTheory.TensorProduct.IsBaseChangePi
public import TauCeti.Algebra.Module.LocalizedModule.Submodule
import TauCeti.LinearAlgebra.Pi

/-!
# Finite projective lattices

Let `K` be a commutative `B`-algebra and `V` a `K`-module. A *finite projective lattice* in `V`
is a finitely generated projective `B`-submodule `Λ` of `V` whose `K`-span is all of `V`.

For `B = W(R)` the Witt vectors of a perfect `𝔽_p`-algebra `R`, `K = W(R)[1/p]` and `V = K ^ n`,
these are the `R`-points of the Witt vector affine Grassmannian of `GL_n`; for `B = R⟦t⟧` and
`K = R((t))` they are the `R`-points of the classical affine Grassmannian of `GL_n`. This file
develops the algebraic carrier over an arbitrary coefficient algebra:

* lattices are determined by their underlying submodules, and finite projectivity carries no
  further data (`TauCeti.ProjectiveLattice.ext`);
* when `B → K` is injective and `ι` is finite, the image of `ι → B` in `ι → K` is a lattice, the
  *standard lattice* (`TauCeti.ProjectiveLattice.standard`);
* the zero module has exactly one lattice, its zero submodule, while in a nonzero module no
  lattice is zero;
* `K`-linear automorphisms of `V`, such as the elements of `GL_n(K)` acting on `K ^ n`, act on
  lattices (`TauCeti.ProjectiveLattice.map`);
* when `K` is a localization of `B` at `S`, every lattice is a full lattice in the sense of
  `Submodule.IsFullLattice`, and any two lattices are commensurable: an element of `S` multiplies
  one into the other (`TauCeti.ProjectiveLattice.exists_smul_mem`). For `S` the powers of `p`
  these are the two pole bounds `p ^ a • Λ' ⊆ Λ ⊆ p ^ (-b) • Λ'`;
* lattices base change along coefficient maps `B → B'` whenever `K' = B'[S⁻¹]` and `B' → K'` is
  injective (as for `W(R) → W(R')`): the `B'`-span of the image of `Λ` is a lattice isomorphic to
  `B' ⊗[B] Λ` (`TauCeti.ProjectiveLattice.baseChange`). This gives the base change map on lattices
  along `B → B'`, and it carries the standard lattice to the standard lattice.

## Main declarations

* `TauCeti.ProjectiveLattice B K V`: finitely generated projective `B`-submodules of `V` spanning
  `V` over `K`.
* `TauCeti.ProjectiveLattice.standard`: the image of `ι → B` in `ι → K`.
* `TauCeti.ProjectiveLattice.mem_standard`: a vector lies in the standard lattice exactly when all
  its coordinates come from `B`.
* `TauCeti.ProjectiveLattice.map`: the image of a lattice under a `K`-linear equivalence, giving
  the action of `V ≃ₗ[K] V` on lattices in `V`.
* `TauCeti.ProjectiveLattice.isFullLattice`: over a localization, a lattice is a full lattice.
* `TauCeti.ProjectiveLattice.exists_smul_mem`: commensurability of lattices over a localization.
* `TauCeti.ProjectiveLattice.baseChange` and `TauCeti.ProjectiveLattice.baseChangeEquiv`: base
  change of lattices along `B → B'`, and its identification with `B' ⊗[B] Λ`.
* `TauCeti.ProjectiveLattice.baseChange_standard`: base change preserves the standard lattice.

## References

* B. Bhatt and P. Scholze, *Projectivity of the Witt vector affine Grassmannian*, Invent. Math.
  209 (2017), §§8–9.
-/

public section

namespace TauCeti

/-- A *finite projective lattice* in a `K`-module `V`, for a commutative `B`-algebra `K`: a
finitely generated projective `B`-submodule of `V` whose `K`-span is `V`. -/
structure ProjectiveLattice (B K V : Type*) [CommRing B] [CommRing K] [Algebra B K]
    [AddCommGroup V] [Module B V] [Module K V] [IsScalarTower B K V] where
  /-- The underlying `B`-submodule of the lattice. -/
  toSubmodule : Submodule B V
  /-- A lattice is finitely generated over `B`. -/
  fg : toSubmodule.FG
  /-- A lattice is projective over `B`. -/
  projective : Module.Projective B toSubmodule
  /-- A lattice spans the ambient module over `K`. -/
  span_eq_top : Submodule.span K (toSubmodule : Set V) = ⊤

namespace ProjectiveLattice

variable {B K V : Type*} [CommRing B] [CommRing K] [Algebra B K]
variable [AddCommGroup V] [Module B V] [Module K V] [IsScalarTower B K V]

section Basic

instance : SetLike (ProjectiveLattice B K V) V where
  coe Λ := Λ.toSubmodule
  coe_injective Λ Λ' h := by
    cases Λ
    cases Λ'
    congr
    exact SetLike.coe_injective h

instance : PartialOrder (ProjectiveLattice B K V) := .ofSetLike (ProjectiveLattice B K V)

instance : AddSubgroupClass (ProjectiveLattice B K V) V where
  zero_mem Λ := Λ.toSubmodule.zero_mem
  add_mem {Λ} := Λ.toSubmodule.add_mem
  neg_mem {Λ} := Λ.toSubmodule.neg_mem

instance : SMulMemClass (ProjectiveLattice B K V) B V where
  smul_mem {Λ} r _ hx := Λ.toSubmodule.smul_mem r hx

@[simp]
theorem coe_toSubmodule (Λ : ProjectiveLattice B K V) : (Λ.toSubmodule : Set V) = Λ :=
  rfl

@[simp]
theorem mem_toSubmodule {Λ : ProjectiveLattice B K V} {x : V} : x ∈ Λ.toSubmodule ↔ x ∈ Λ :=
  Iff.rfl

theorem toSubmodule_injective :
    Function.Injective (toSubmodule : ProjectiveLattice B K V → Submodule B V) :=
  fun _ _ h ↦ SetLike.coe_injective congr(($h : Set V))

@[simp]
theorem toSubmodule_inj {Λ Λ' : ProjectiveLattice B K V} :
    Λ.toSubmodule = Λ'.toSubmodule ↔ Λ = Λ' :=
  toSubmodule_injective.eq_iff

@[simp]
theorem toSubmodule_le_toSubmodule {Λ Λ' : ProjectiveLattice B K V} :
    Λ.toSubmodule ≤ Λ'.toSubmodule ↔ Λ ≤ Λ' :=
  ⟨fun h _ hx ↦ h hx, fun h _ hx ↦ h hx⟩

/-- Two lattices are equal when they have the same elements. -/
@[ext]
theorem ext {Λ Λ' : ProjectiveLattice B K V} (h : ∀ x, x ∈ Λ ↔ x ∈ Λ') : Λ = Λ' :=
  SetLike.ext h

instance (Λ : ProjectiveLattice B K V) : Module.Finite B Λ.toSubmodule :=
  Module.Finite.iff_fg.mpr Λ.fg

instance (Λ : ProjectiveLattice B K V) : Module.Projective B Λ.toSubmodule :=
  Λ.projective

/-- The `K`-span of a lattice is the whole ambient module. -/
@[simp]
theorem span_coe_eq_top (Λ : ProjectiveLattice B K V) : Submodule.span K (Λ : Set V) = ⊤ :=
  Λ.span_eq_top

end Basic

section RankZero

/-- The zero submodule is the unique lattice in the zero module. -/
instance [Subsingleton V] : Unique (ProjectiveLattice B K V) where
  default :=
    { toSubmodule := ⊥
      fg := Submodule.fg_bot
      projective := Module.Projective.of_free
      span_eq_top := Subsingleton.elim _ _ }
  uniq Λ := ext fun x ↦ by simp [Subsingleton.elim x 0, zero_mem]

/-- In the zero module every lattice is the zero submodule. -/
theorem toSubmodule_eq_bot [Subsingleton V] (Λ : ProjectiveLattice B K V) : Λ.toSubmodule = ⊥ :=
  Subsingleton.elim _ _

/-- In a nonzero module no lattice is the zero submodule. -/
theorem toSubmodule_ne_bot [Nontrivial V] (Λ : ProjectiveLattice B K V) : Λ.toSubmodule ≠ ⊥ := by
  intro h
  have := Λ.span_eq_top
  rw [h, Submodule.bot_coe, Submodule.span_zero_singleton] at this
  exact bot_ne_top this

end RankZero

section Standard

variable (B K) (ι : Type*) [Finite ι] [FaithfulSMul B K]

/-- The *standard lattice* in `ι → K`: the image of `ι → B` under the coordinatewise map
`B → K`, which is assumed injective. -/
noncomputable def standard : ProjectiveLattice B K (ι → K) where
  toSubmodule := LinearMap.range ((Algebra.linearMap B K).compLeft ι)
  fg := by
    rw [LinearMap.range_eq_map]
    exact Module.Finite.fg_top.map _
  projective := by
    have hinj : Function.Injective ((Algebra.linearMap B K).compLeft ι) := fun x y h ↦
      funext fun i ↦ FaithfulSMul.algebraMap_injective B K (congr_fun h i)
    exact Module.Projective.of_equiv (LinearEquiv.ofInjective _ hinj)
  span_eq_top := by
    classical
    rw [eq_top_iff, ← (Pi.basisFun K ι).span_eq, Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    exact Submodule.subset_span ⟨Pi.single i 1, by simp⟩

variable {B K ι}

theorem toSubmodule_standard :
    (standard B K ι).toSubmodule = LinearMap.range ((Algebra.linearMap B K).compLeft ι) :=
  (rfl)

/-- A vector lies in the standard lattice exactly when all its coordinates come from `B`. -/
@[simp]
theorem mem_standard {x : ι → K} :
    x ∈ standard B K ι ↔ ∀ i, x i ∈ Set.range (algebraMap B K) := by
  rw [← mem_toSubmodule, toSubmodule_standard, LinearMap.range_compLeft]
  simp [Submodule.mem_pi, Set.mem_range]

/-- The standard lattice contains the standard basis vectors. -/
theorem single_one_mem_standard [DecidableEq ι] (i : ι) : Pi.single i (1 : K) ∈ standard B K ι :=
  mem_toSubmodule.mp (LinearMap.mem_range.mpr ⟨Pi.single i 1, by simp⟩)

variable (K ι) in
/-- When `B = K`, the standard lattice is the whole space. -/
@[simp]
theorem toSubmodule_standard_self : (standard K K ι).toSubmodule = ⊤ :=
  eq_top_iff.mpr fun x _ ↦ mem_standard.mpr fun i ↦ ⟨x i, rfl⟩

end Standard

section Map

variable {W : Type*} [AddCommGroup W] [Module B W] [Module K W] [IsScalarTower B K W]

/-- The image of a lattice under a `K`-linear equivalence. -/
noncomputable def map (e : V ≃ₗ[K] W) (Λ : ProjectiveLattice B K V) : ProjectiveLattice B K W where
  toSubmodule := Λ.toSubmodule.map (e.restrictScalars B : V →ₗ[B] W)
  fg := Λ.fg.map _
  projective := Module.Projective.of_equiv (Λ.toSubmodule.equivMapOfInjective _
    (e.restrictScalars B).injective)
  span_eq_top := by simp [Submodule.map_coe]

@[simp]
theorem toSubmodule_map (e : V ≃ₗ[K] W) (Λ : ProjectiveLattice B K V) :
    (Λ.map e).toSubmodule = Λ.toSubmodule.map (e.restrictScalars B : V →ₗ[B] W) :=
  (rfl)

@[simp]
theorem mem_map {e : V ≃ₗ[K] W} {Λ : ProjectiveLattice B K V} {y : W} :
    y ∈ Λ.map e ↔ e.symm y ∈ Λ := by
  rw [← mem_toSubmodule, toSubmodule_map, Submodule.mem_map_equiv]
  simp

@[simp]
theorem map_refl (Λ : ProjectiveLattice B K V) : Λ.map (LinearEquiv.refl K V) = Λ :=
  ext fun _ ↦ by simp

theorem map_trans {U : Type*} [AddCommGroup U] [Module B U] [Module K U] [IsScalarTower B K U]
    (e : V ≃ₗ[K] W) (f : W ≃ₗ[K] U) (Λ : ProjectiveLattice B K V) :
    Λ.map (e.trans f) = (Λ.map e).map f :=
  ext fun _ ↦ by simp

/-- The group of `K`-linear automorphisms of `V` acts on lattices in `V` by taking images. -/
noncomputable instance : MulAction (V ≃ₗ[K] V) (ProjectiveLattice B K V) where
  smul e Λ := Λ.map e
  one_smul := map_refl
  mul_smul e f Λ := map_trans f e Λ

theorem smul_def (e : V ≃ₗ[K] V) (Λ : ProjectiveLattice B K V) : e • Λ = Λ.map e :=
  rfl

@[simp]
theorem mem_smul {e : V ≃ₗ[K] V} {Λ : ProjectiveLattice B K V} {y : V} :
    y ∈ e • Λ ↔ e.symm y ∈ Λ :=
  mem_map

end Map

section Localization

/-- When `K` is a localization of `B`, every finite projective lattice is a full lattice. -/
theorem isFullLattice (S : Submonoid B) [IsLocalization S K] (Λ : ProjectiveLattice B K V) :
    Λ.toSubmodule.IsFullLattice K where
  fg := Λ.fg
  linearIndepOn _ _ h := h.localization (Rₛ := K) S
  span_eq_top := Λ.span_eq_top

/-- **Commensurability.** When `K` is a localization of `B` at `S`, a single element of `S`
multiplies a lattice into any other lattice. For `ι → K` and the standard lattice this bounds the
denominators of a lattice, and the poles of the standard lattice with respect to it. -/
theorem exists_smul_mem (S : Submonoid B) [IsLocalization S K] (Λ Λ' : ProjectiveLattice B K V) :
    ∃ s ∈ S, ∀ x ∈ Λ, s • x ∈ Λ' :=
  Λ.fg.exists_smul_mem_of_le_span (F := K) S (M := Λ'.toSubmodule) (by simp)

end Localization

section BaseChange

open TensorProduct

variable {B' K' V' : Type*} [CommRing B'] [CommRing K'] [Algebra B' K']
variable [AddCommGroup V'] [Module B' V'] [Module K' V'] [IsScalarTower B' K' V']
variable [Algebra B B'] [Algebra K K'] [Algebra B K'] [IsScalarTower B K K']
  [IsScalarTower B B' K']
variable [Module B V'] [Module K V'] [IsScalarTower K K' V'] [IsScalarTower B K V']
  [IsScalarTower B B' V'] [IsScalarTower B K' V']

/-- The `B'`-linear map `B' ⊗[B] Λ → V'` induced by a `K`-linear map `f : V → V'`; its image is
the base change of `Λ` along `f`. -/
noncomputable def baseChangeMap (f : V →ₗ[K] V') (Λ : ProjectiveLattice B K V) :
    B' ⊗[B] Λ.toSubmodule →ₗ[B'] V' :=
  ((f.restrictScalars B) ∘ₗ Λ.toSubmodule.subtype).liftBaseChange B'

@[simp]
theorem baseChangeMap_tmul (f : V →ₗ[K] V') (Λ : ProjectiveLattice B K V) (b : B')
    (x : Λ.toSubmodule) : baseChangeMap f Λ (b ⊗ₜ x) = b • f x :=
  (rfl)

theorem range_baseChangeMap (f : V →ₗ[K] V') (Λ : ProjectiveLattice B K V) :
    LinearMap.range (baseChangeMap (B' := B') f Λ) = Submodule.span B' (f '' Λ) := by
  simp [baseChangeMap, LinearMap.range_liftBaseChange, LinearMap.range_comp, Submodule.map_coe]

variable (S : Submonoid B) [IsLocalization S K]
  [IsLocalization (Algebra.algebraMapSubmonoid B' S) K']
include S

/-- If `K` is a localization of `B` at `S`, `K'` the corresponding localization of `B'`, and
`V'` the base change of `V` along `K → K'`, then `B' ⊗[B] Λ → V'` is a localization at the image
of `S`. -/
theorem isLocalizedModule_baseChangeMap {f : V →ₗ[K] V'} (hf : IsBaseChange K' f)
    (Λ : ProjectiveLattice B K V) :
    IsLocalizedModule (Algebra.algebraMapSubmonoid B' S) (baseChangeMap f Λ) := by
  rw [isLocalizedModule_iff_isBaseChange (Algebra.algebraMapSubmonoid B' S) K']
  refine (TensorProduct.isBaseChange B Λ.toSubmodule B').of_comp ?_
  have h :=
    ((isLocalizedModule_iff_isBaseChange S K _).mp
      (Λ.toSubmodule.isLocalizedModule_subtype_of_span_eq_top S Λ.span_eq_top)).comp hf
  convert h using 1
  ext
  simp

variable [FaithfulSMul B' K']

/-- If moreover `B' → K'` is injective, then `B' ⊗[B] Λ → V'` is injective. -/
theorem baseChangeMap_injective {f : V →ₗ[K] V'} (hf : IsBaseChange K' f)
    (Λ : ProjectiveLattice B K V) : Function.Injective (baseChangeMap (B' := B') f Λ) := by
  have := Λ.isLocalizedModule_baseChangeMap (B' := B') S hf
  refine (IsLocalizedModule.injective_iff_isRegular (Algebra.algebraMapSubmonoid B' S) _).mpr
    fun c ↦ ?_
  have hc0 : (c : B') ∈ nonZeroDivisors B' :=
    mem_nonZeroDivisors_of_injective (FaithfulSMul.algebraMap_injective B' K')
      (IsLocalization.map_units K' c).mem_nonZeroDivisors
  exact Module.Flat.isSMulRegular_of_nonZeroDivisors (M := B' ⊗[B] Λ.toSubmodule) hc0

variable (B') in
/-- The *base change* of a lattice along a base change `f : V → V'` of `K`-modules to `K'`, where
`K'` is the localization of `B'` at the image of `S`: the `B'`-span of the image of the lattice.
It is isomorphic to `B' ⊗[B] Λ` (`TauCeti.ProjectiveLattice.baseChangeEquiv`). -/
noncomputable def baseChange {f : V →ₗ[K] V'} (hf : IsBaseChange K' f)
    (Λ : ProjectiveLattice B K V) : ProjectiveLattice B' K' V' where
  toSubmodule := Submodule.span B' (f '' Λ)
  fg := by
    rw [← range_baseChangeMap, LinearMap.range_eq_map]
    exact Module.Finite.fg_top.map _
  projective := by
    rw [← range_baseChangeMap]
    exact Module.Projective.of_equiv
      (LinearEquiv.ofInjective _ (Λ.baseChangeMap_injective (B' := B') S hf))
  span_eq_top := by
    have := Λ.isLocalizedModule_baseChangeMap (B' := B') S hf
    rw [← range_baseChangeMap, LinearMap.coe_range, ← Set.image_univ]
    exact span_eq_top_of_isLocalizedModule K' (Algebra.algebraMapSubmonoid B' S)
      (baseChangeMap f Λ) Submodule.span_univ

@[simp]
theorem toSubmodule_baseChange {f : V →ₗ[K] V'} (hf : IsBaseChange K' f)
    (Λ : ProjectiveLattice B K V) :
    (Λ.baseChange B' S hf).toSubmodule = Submodule.span B' (f '' Λ) :=
  (rfl)

theorem apply_mem_baseChange {f : V →ₗ[K] V'} (hf : IsBaseChange K' f)
    {Λ : ProjectiveLattice B K V} {x : V} (hx : x ∈ Λ) : f x ∈ Λ.baseChange B' S hf :=
  Submodule.subset_span ⟨x, hx, rfl⟩

variable (B') in
/-- The base change of a lattice `Λ` is isomorphic to the scalar extension `B' ⊗[B] Λ`. -/
noncomputable def baseChangeEquiv {f : V →ₗ[K] V'} (hf : IsBaseChange K' f)
    (Λ : ProjectiveLattice B K V) :
    B' ⊗[B] Λ.toSubmodule ≃ₗ[B'] (Λ.baseChange B' S hf).toSubmodule :=
  (LinearEquiv.ofInjective _ (Λ.baseChangeMap_injective (B' := B') S hf)).trans
    (LinearEquiv.ofEq _ _ ((range_baseChangeMap f Λ).trans (toSubmodule_baseChange S hf Λ).symm))

@[simp]
theorem baseChangeEquiv_tmul {f : V →ₗ[K] V'} (hf : IsBaseChange K' f)
    (Λ : ProjectiveLattice B K V) (b : B') (x : Λ.toSubmodule) :
    (Λ.baseChangeEquiv B' S hf (b ⊗ₜ x) : V') = b • f x := by
  simp [baseChangeEquiv]

/-- The base change of the standard lattice in `ι → K` along the coordinatewise map
`ι → K → ι → K'` is the standard lattice in `ι → K'`. -/
theorem baseChange_standard [FaithfulSMul B K] (ι : Type*) [Finite ι] :
    (standard B K ι).baseChange B' S (.finitePow ι (.linearMap K K')) =
      standard B' K' ι := by
  classical
  cases nonempty_fintype ι
  refine le_antisymm ?_ ?_
  · rw [← toSubmodule_le_toSubmodule, toSubmodule_baseChange, Submodule.span_le]
    rintro _ ⟨y, hy, rfl⟩
    refine mem_standard.mpr fun i ↦ ?_
    obtain ⟨b, hb⟩ := mem_standard.mp hy i
    exact ⟨algebraMap B B' b, by simp [← hb, ← IsScalarTower.algebraMap_apply]⟩
  · intro x hx
    choose y hy using mem_standard.mp hx
    have hx : x = ∑ i, y i • Pi.single i (1 : K') := by
      ext j
      simp [hy, Finset.sum_apply, Pi.single_apply, Algebra.smul_def]
    rw [hx]
    refine sum_mem fun i _ ↦ SMulMemClass.smul_mem _ ?_
    simpa using apply_mem_baseChange S (.finitePow ι (.linearMap K K'))
      (single_one_mem_standard (B := B) i)

end BaseChange

end ProjectiveLattice

end TauCeti
