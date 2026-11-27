/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.CStarAlgebra.Spectrum
public import Mathlib.Analysis.CStarAlgebra.Unitization
public import Mathlib.Topology.UnitInterval
public import TauCeti.Analysis.Matrix.GeneralLinearGroup.StableComponent
public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Unitization
public import TauCeti.Topology.Algebra.Matrix.GeneralLinearGroup.StableComponent

/-!
# `K₁` of a nonunital algebra through the unitization

For a nonunital normed algebra `A` over a nontrivially normed field `𝕜`, the scalar part
`A⁺ = Unitization 𝕜 A → 𝕜` induces a homomorphism `π₀GL_∞(A⁺) → π₀GL_∞(𝕜)` of stable component
groups (`TauCeti.StableComponentGroup`). Its kernel is `K₁(A)` (`TauCeti.UnitizationKOne`), the
analogue for `K₁` of `TauCeti.UnitizationKZero`.

`K₁(A)` is classically described by stable homotopy classes of invertible matrices over `A⁺`
whose scalar part is the identity, that is of elements of `TauCeti.unitizationGLFstOne`. This
file proves this invertible-matrix description for the kernel:

* every class of the kernel is the class of an invertible matrix with scalar part `1`
  (`TauCeti.UnitizationKOne.exists_mk_eq`);
* two invertible matrices with scalar part `1` have the same class exactly when, after a common
  stabilization, they differ by an element of the identity component of the group of invertible
  matrices with scalar part `1` (`TauCeti.UnitizationKOne.mk_eq_mk_iff`), so homotopies can be
  chosen with the same scalar condition.

The corresponding description by unitaries of `A⁺` is in
`TauCeti.Analysis.Matrix.GeneralLinearGroup.Unitization.Unitary`.

Both rest on the retraction `g ↦ g · s(g)⁻¹` of `GLₙ(A⁺)` onto the matrices with scalar part `1`
(`TauCeti.unitizationGLRetract`), where `s(g)` is the scalar part of `g` viewed in `GLₙ(A⁺)`. It
is continuous (`TauCeti.continuous_unitizationGLRetract`), fixes those matrices, and so maps the
identity component of `GLₙ(A⁺)` to a connected set containing `1`
(`TauCeti.mem_connectedComponentIn_unitizationGLFstOne`).

When `K₁(𝕜) = 0`, as for `𝕜 = ℂ` since every `GLₙ(ℂ)` is connected, the kernel condition is
vacuous: `K₁(A)` is all of `π₀GL_∞(A⁺)` (`TauCeti.UnitizationKOne.eq_top`,
`TauCeti.UnitizationKOne.equivStableComponentGroup`). For C⋆-algebras `K₁(A)` is functorial for
star homomorphisms through `Unitization.starMap` (`TauCeti.UnitizationKOne.map`, `map_id`,
`map_comp`). This functoriality is homotopy invariant: a point-norm continuous path `t ↦ φₜ` of
star homomorphisms `A → B`, `t ∈ [0, 1]`, induces the same map `K₁(A) → K₁(B)` at both ends
(`TauCeti.UnitizationKOne.map_eq_of_continuous`), since for an invertible matrix `u` over `A⁺`
the invertible matrices obtained by applying `φₜ⁺` to the entries form a path in `GLₙ(B⁺)`.
The zero star homomorphism induces the trivial map
(`TauCeti.UnitizationKOne.map_zero_eq_one`), since its unitization sends every invertible
matrix to its scalar part, whose class comes from `π₀GL_∞(ℂ)`, which is trivial.

## Main definitions

* `TauCeti.UnitizationKOne`: `K₁(A) = ker(π₀GL_∞(A⁺) → π₀GL_∞(𝕜))`.
* `TauCeti.UnitizationKOne.map`: functoriality for star homomorphisms of C⋆-algebras.

## Main results

* `TauCeti.continuous_unitizationGLFst`, `TauCeti.continuous_unitizationGLInl`,
  `TauCeti.continuous_unitizationGLRetract`: continuity of the scalar part, of the inclusion of
  scalar matrices and of the retraction onto `TauCeti.unitizationGLFstOne`.
* `TauCeti.UnitizationKOne.mk_unitizationGLRetract`: the retraction onto the matrices with scalar
  part `1` preserves classes of `K₁(A)`.
* `TauCeti.UnitizationKOne.exists_mk_eq`, `TauCeti.UnitizationKOne.mk_eq_mk_iff`:
  representatives of `K₁(A)` with scalar part `1`, and homotopies within the scalar condition.
* `TauCeti.UnitizationKOne.map_id`, `TauCeti.UnitizationKOne.map_comp`: functoriality.
* `TauCeti.UnitizationKOne.map_eq_of_continuous`: homotopy invariance of `K₁`.
* `TauCeti.UnitizationKOne.map_zero_eq_one`: the zero star homomorphism induces the trivial map.
* `TauCeti.UnitizationKOne.eq_top`, `TauCeti.UnitizationKOne.equivStableComponentGroup`:
  `K₁(A) ≅ K₁(A⁺)` when `K₁(𝕜) = 0`, for instance for `𝕜 = ℂ`.

## References

* B. Blackadar, *K-Theory for Operator Algebras*, second edition, Mathematical Sciences Research
  Institute Publications 5, Cambridge University Press (1998), 8.1.5 and Corollary 8.3.7.
-/

public section

noncomputable section

open Matrix

namespace TauCeti

section General

variable (𝕜 A : Type*) [NontriviallyNormedField 𝕜] [NonUnitalNormedRing A] [NormedSpace 𝕜 A]
  [IsScalarTower 𝕜 A A] [SMulCommClass 𝕜 A A]

/-- The scalar part `A⁺ → 𝕜` of the unitization is continuous, stated for the bundled ring
homomorphism so that it matches the continuity argument of `TauCeti.StableComponentGroup.map`. -/
theorem _root_.Unitization.continuous_fstHom :
    Continuous (Unitization.fstHom 𝕜 A : Unitization 𝕜 A →+* 𝕜) :=
  Unitization.continuous_fst

/-- The scalar part `GLₙ(A⁺) →* GLₙ(𝕜)` is continuous. -/
theorem continuous_unitizationGLFst (n : Type*) [Fintype n] [DecidableEq n] :
    Continuous (unitizationGLFst 𝕜 A n) := by
  rw [unitizationGLFst_def]
  exact Units.continuous_map (continuous_id.matrix_map Unitization.continuous_fst)

/-- The inclusion `GLₙ(𝕜) →* GLₙ(A⁺)` of invertible scalar matrices is continuous. -/
theorem continuous_unitizationGLInl (n : Type*) [Fintype n] [DecidableEq n] :
    Continuous (unitizationGLInl 𝕜 A n) := by
  rw [unitizationGLInl_def]
  exact Units.continuous_map (continuous_id.matrix_map Unitization.continuous_inl)

variable [RegularNormedAlgebra 𝕜 A]

/-- The retraction of `GLₙ(A⁺)` onto `unitizationGLFstOne` is continuous. -/
theorem continuous_unitizationGLRetract (n : Type*) [Fintype n] [DecidableEq n] :
    Continuous (unitizationGLRetract 𝕜 A n) :=
  (continuous_id.mul ((continuous_unitizationGLInl 𝕜 A n).comp
    (continuous_unitizationGLFst 𝕜 A n)).inv).congr fun g ↦ (unitizationGLRetract_def g).symm

variable {𝕜 A} in
/-- An invertible matrix with identity scalar part in the identity component of `GLₙ(A⁺)` lies in
the identity component of the group `unitizationGLFstOne` of invertible matrices with identity
scalar part. -/
theorem mem_connectedComponentIn_unitizationGLFstOne {n : Type*} [Fintype n] [DecidableEq n]
    {g : GL n (Unitization 𝕜 A)} (hg : g ∈ unitizationGLFstOne 𝕜 A n)
    (hg₀ : g ∈ connectedComponent 1) :
    g ∈ connectedComponentIn (unitizationGLFstOne 𝕜 A n : Set _) 1 := by
  have hconn : IsPreconnected (unitizationGLRetract 𝕜 A n '' connectedComponent 1) :=
    isPreconnected_connectedComponent.image _
      (continuous_unitizationGLRetract 𝕜 A n).continuousOn
  have h1 : (1 : GL n (Unitization 𝕜 A)) ∈ unitizationGLRetract 𝕜 A n '' connectedComponent 1 :=
    ⟨1, mem_connectedComponent, unitizationGLRetract_of_mem (one_mem _)⟩
  refine hconn.subset_connectedComponentIn h1 ?_ ⟨g, hg₀, unitizationGLRetract_of_mem hg⟩
  rintro _ ⟨u, -, rfl⟩
  exact unitizationGLRetract_mem_unitizationGLFstOne u

/-- **`K₁` of a nonunital algebra**: the kernel of the homomorphism
`π₀GL_∞(A⁺) → π₀GL_∞(𝕜)` of stable component groups induced by the scalar part of the
unitization `A⁺ = Unitization 𝕜 A`. -/
def UnitizationKOne : Subgroup (StableComponentGroup (Unitization 𝕜 A)) :=
  (StableComponentGroup.map (Unitization.fstHom 𝕜 A : Unitization 𝕜 A →+* 𝕜)
    (Unitization.continuous_fstHom 𝕜 A)).ker

namespace UnitizationKOne

variable {𝕜 A}

/-- Membership in `K₁(A)`: the class maps to `1` in `π₀GL_∞(𝕜)`. -/
theorem mem_iff {x : StableComponentGroup (Unitization 𝕜 A)} :
    x ∈ UnitizationKOne 𝕜 A ↔
      StableComponentGroup.map (Unitization.fstHom 𝕜 A : Unitization 𝕜 A →+* 𝕜)
        (Unitization.continuous_fstHom 𝕜 A) x = 1 :=
  MonoidHom.mem_ker

/-- The class in `π₀GL_∞(𝕜)` of the scalar part of an invertible matrix is the image of its
class. -/
theorem map_mk (n : ℕ) (u : GL (Fin n) (Unitization 𝕜 A)) :
    StableComponentGroup.map (Unitization.fstHom 𝕜 A : Unitization 𝕜 A →+* 𝕜)
        (Unitization.continuous_fstHom 𝕜 A) (StableComponentGroup.mk _ n u) =
      StableComponentGroup.mk 𝕜 n (unitizationGLFst 𝕜 A (Fin n) u) := by
  rw [unitizationGLFst_def]
  exact StableComponentGroup.map_mk ..

/-- The class in `π₀GL_∞(A⁺)` of an included scalar matrix is the image of its class. -/
theorem map_inlRingHom_mk (n : ℕ) (g : GL (Fin n) 𝕜) :
    StableComponentGroup.map (Unitization.inlRingHom 𝕜 A) Unitization.continuous_inl
        (StableComponentGroup.mk 𝕜 n g) =
      StableComponentGroup.mk _ n (unitizationGLInl 𝕜 A (Fin n) g) := by
  rw [unitizationGLInl_def]
  exact StableComponentGroup.map_mk ..

/-- The class of an invertible matrix with scalar part `1` lies in `K₁(A)`. -/
theorem mk_mem {n : ℕ} {u : GL (Fin n) (Unitization 𝕜 A)}
    (hu : u ∈ unitizationGLFstOne 𝕜 A (Fin n)) :
    StableComponentGroup.mk _ n u ∈ UnitizationKOne 𝕜 A := by
  rw [mem_iff, map_mk, mem_unitizationGLFstOne_iff_unitizationGLFst.1 hu, map_one]

/-- The retraction `g ↦ g · s(g)⁻¹` onto the matrices with scalar part `1` does not change the
class of an invertible matrix whose class lies in `K₁(A)`. -/
theorem mk_unitizationGLRetract {n : ℕ} {g : GL (Fin n) (Unitization 𝕜 A)}
    (hg : StableComponentGroup.mk _ n g ∈ UnitizationKOne 𝕜 A) :
    StableComponentGroup.mk _ n (unitizationGLRetract 𝕜 A (Fin n) g) =
      StableComponentGroup.mk _ n g := by
  have h₁ : StableComponentGroup.mk 𝕜 n (unitizationGLFst 𝕜 A (Fin n) g) = 1 := by
    rw [← map_mk]
    exact mem_iff.1 hg
  have h₂ : StableComponentGroup.mk _ n
      (unitizationGLInl 𝕜 A (Fin n) (unitizationGLFst 𝕜 A (Fin n) g)) = 1 := by
    rw [← map_inlRingHom_mk, h₁, map_one]
  rw [unitizationGLRetract_def, map_mul, map_inv, h₂, inv_one, mul_one]

/-- **Representatives of `K₁(A)`.** Every class of `K₁(A)` is the class of an invertible matrix
over `A⁺` whose scalar part is the identity. -/
theorem exists_mk_eq {x : StableComponentGroup (Unitization 𝕜 A)}
    (hx : x ∈ UnitizationKOne 𝕜 A) :
    ∃ n, ∃ u ∈ unitizationGLFstOne 𝕜 A (Fin n), StableComponentGroup.mk _ n u = x := by
  obtain ⟨n, g, rfl⟩ := StableComponentGroup.exists_mk x
  exact ⟨n, unitizationGLRetract 𝕜 A (Fin n) g, unitizationGLRetract_mem_unitizationGLFstOne g,
    mk_unitizationGLRetract hx⟩

/-- **Homotopies within the scalar condition.** Two invertible matrices over `A⁺` with scalar
part `1` have the same class exactly when, after a common stabilization, they differ by an
element of the identity component of the group of invertible matrices with scalar part `1`. -/
theorem mk_eq_mk_iff {n : ℕ} {u v : GL (Fin n) (Unitization 𝕜 A)}
    (hu : u ∈ unitizationGLFstOne 𝕜 A (Fin n)) (hv : v ∈ unitizationGLFstOne 𝕜 A (Fin n)) :
    StableComponentGroup.mk _ n u = StableComponentGroup.mk _ n v ↔
      ∃ k, ∃ h : n ≤ k, stabilizeGL _ h (u⁻¹ * v) ∈
        connectedComponentIn (unitizationGLFstOne 𝕜 A (Fin k) : Set _) 1 := by
  rw [StableComponentGroup.mk_eq_mk_iff]
  refine exists_congr fun k ↦ exists_congr fun h ↦ ⟨fun hc ↦ ?_, fun hc ↦ ?_⟩
  · exact mem_connectedComponentIn_unitizationGLFstOne
      (stabilizeGL_mem_unitizationGLFstOne h (mul_mem (inv_mem hu) hv)) hc
  · rw [Subgroup.mem_connectedComponentOfOne_iff, ← connectedComponentIn_univ]
    exact connectedComponentIn_mono _ (Set.subset_univ _) hc

/-- **`K₁(A) = K₁(A⁺)` when `K₁(𝕜) = 0`**, for instance for `𝕜 = ℂ`: the kernel condition is
vacuous. -/
theorem eq_top [Subsingleton (StableComponentGroup 𝕜)] : UnitizationKOne 𝕜 A = ⊤ :=
  eq_top_iff.2 fun _ _ ↦ mem_iff.2 (Subsingleton.elim _ _)

/-- The isomorphism `K₁(A) ≃* π₀GL_∞(A⁺)` when `K₁(𝕜) = 0`, for instance for `𝕜 = ℂ`. -/
def equivStableComponentGroup [Subsingleton (StableComponentGroup 𝕜)] :
    UnitizationKOne 𝕜 A ≃* StableComponentGroup (Unitization 𝕜 A) :=
  (MulEquiv.subgroupCongr eq_top).trans Subgroup.topEquiv

/-- The isomorphism `K₁(A) ≃* π₀GL_∞(A⁺)` is the inclusion. -/
@[simp]
theorem equivStableComponentGroup_apply [Subsingleton (StableComponentGroup 𝕜)]
    (x : UnitizationKOne 𝕜 A) : equivStableComponentGroup x = x :=
  (rfl)

/-- The inverse of the isomorphism `K₁(A) ≃* π₀GL_∞(A⁺)` does not change the class. -/
@[simp]
theorem coe_equivStableComponentGroup_symm_apply [Subsingleton (StableComponentGroup 𝕜)]
    (x : StableComponentGroup (Unitization 𝕜 A)) :
    ((equivStableComponentGroup.symm x : UnitizationKOne 𝕜 A) :
      StableComponentGroup (Unitization 𝕜 A)) = x :=
  (rfl)

end UnitizationKOne

end General

/-! ## C⋆-algebras -/

namespace UnitizationKOne

open scoped CStarAlgebra

variable {A B C : Type*} [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B]
  [NonUnitalCStarAlgebra C]

/-- The unitization of a star homomorphism of C⋆-algebras is continuous, stated for the bundled
ring homomorphism so that it matches the continuity argument of `TauCeti.StableComponentGroup.map`.
-/
theorem _root_.Unitization.continuous_starMap (φ : A →⋆ₙₐ[ℂ] B) :
    Continuous (Unitization.starMap φ : Unitization ℂ A →+* Unitization ℂ B) :=
  map_continuous (Unitization.starMap φ)

/-- For a point-norm continuous family `x ↦ φₓ` of star homomorphisms, applying `φₓ⁺` to the
entries of an invertible matrix over `A⁺` gives a continuous family in `GLₙ(B⁺)`. -/
theorem _root_.Unitization.continuous_units_map_starMap {X : Type*} [TopologicalSpace X]
    {φ : X → A →⋆ₙₐ[ℂ] B} (hφ : ∀ a, Continuous fun x ↦ φ x a) {n : Type*} [Fintype n]
    [DecidableEq n] (u : GL n (Unitization ℂ A)) :
    Continuous fun x ↦ Units.map ((Unitization.starMap (φ x) :
      Unitization ℂ A →+* Unitization ℂ B).mapMatrix (m := n)).toMonoidHom u := by
  have hentry (v : Matrix n n (Unitization ℂ A)) :
      Continuous fun x ↦ (v.map (Unitization.starMap (φ x)) : Matrix n n (Unitization ℂ B)) := by
    refine continuous_pi fun i ↦ continuous_pi fun j ↦ ?_
    refine Unitization.continuous_iff.2 ⟨?_, ?_⟩
    · simp only [Matrix.map_apply, Unitization.fst_starMap]
      exact continuous_const
    · simp only [Matrix.map_apply, Unitization.snd_starMap]
      exact hφ _
  refine Units.continuous_iff.2 ⟨hentry (u : Matrix n n (Unitization ℂ A)), ?_⟩
  simp only [← map_inv]
  exact hentry ((u⁻¹ : GL n (Unitization ℂ A)) : Matrix n n (Unitization ℂ A))

/-- The map of stable component groups induced by the unitization of a star homomorphism of
C⋆-algebras sends `K₁(A)` into `K₁(B)`, since it preserves the scalar part. -/
theorem map_starMap_mem (φ : A →⋆ₙₐ[ℂ] B) {x : StableComponentGroup (Unitization ℂ A)}
    (hx : x ∈ UnitizationKOne ℂ A) :
    StableComponentGroup.map (Unitization.starMap φ : Unitization ℂ A →+* Unitization ℂ B)
      (Unitization.continuous_starMap φ) x ∈ UnitizationKOne ℂ B := by
  have h : (Unitization.fstHom ℂ B : Unitization ℂ B →+* ℂ).comp
      (Unitization.starMap φ : Unitization ℂ A →+* Unitization ℂ B) =
        (Unitization.fstHom ℂ A : Unitization ℂ A →+* ℂ) :=
    RingHom.ext fun x ↦ by simp
  rw [mem_iff, StableComponentGroup.map_map]
  simp_rw [h]
  exact mem_iff.1 hx

/-- **Functoriality of `K₁`** for star homomorphisms of C⋆-algebras, through the unitization. -/
def map (φ : A →⋆ₙₐ[ℂ] B) : UnitizationKOne ℂ A →* UnitizationKOne ℂ B :=
  ((StableComponentGroup.map (Unitization.starMap φ : Unitization ℂ A →+* Unitization ℂ B)
    (Unitization.continuous_starMap φ)).comp (UnitizationKOne ℂ A).subtype).codRestrict
    (UnitizationKOne ℂ B) fun x ↦ map_starMap_mem φ x.property

/-- The underlying class of the image of a class under `map φ`. -/
@[simp]
theorem coe_map (φ : A →⋆ₙₐ[ℂ] B) (x : UnitizationKOne ℂ A) :
    (map φ x : StableComponentGroup (Unitization ℂ B)) =
      StableComponentGroup.map (Unitization.starMap φ : Unitization ℂ A →+* Unitization ℂ B)
        (Unitization.continuous_starMap φ) x :=
  (rfl)

/-- The identity star homomorphism induces the identity on `K₁`. -/
@[simp]
theorem map_id : map (NonUnitalStarAlgHom.id ℂ A) = MonoidHom.id (UnitizationKOne ℂ A) := by
  ext x
  have h : (Unitization.starMap (NonUnitalStarAlgHom.id ℂ A) :
      Unitization ℂ A →+* Unitization ℂ A) = RingHom.id _ :=
    RingHom.ext fun x ↦ by simp [Unitization.starMap_id]
  simp_rw [coe_map, h, StableComponentGroup.map_id]
  simp

/-- `K₁` is functorial for star homomorphisms of C⋆-algebras. -/
theorem map_comp (ψ : B →⋆ₙₐ[ℂ] C) (φ : A →⋆ₙₐ[ℂ] B) :
    map (ψ.comp φ) = (map ψ).comp (map φ) := by
  ext x
  rw [coe_map, MonoidHom.comp_apply, coe_map, coe_map, StableComponentGroup.map_map]
  have h : (Unitization.starMap (ψ.comp φ) : Unitization ℂ A →+* Unitization ℂ C) =
      (Unitization.starMap ψ : Unitization ℂ B →+* Unitization ℂ C).comp
        (Unitization.starMap φ : Unitization ℂ A →+* Unitization ℂ B) :=
    RingHom.ext fun x ↦ by simp [Unitization.starMap_comp]
  simp_rw [h]

/-- **Homotopy invariance of `K₁`.** A point-norm continuous path `t ↦ φₜ`, `t ∈ [0, 1]`, of star
homomorphisms `A → B` induces the same map `K₁(A) → K₁(B)` at `t = 0` and `t = 1`. -/
theorem map_eq_of_continuous {φ : unitInterval → A →⋆ₙₐ[ℂ] B}
    (hφ : ∀ a, Continuous fun t ↦ φ t a) : map (φ 0) = map (φ 1) := by
  ext x
  obtain ⟨n, u, hu⟩ := StableComponentGroup.exists_mk (x : StableComponentGroup (Unitization ℂ A))
  rw [coe_map, coe_map, ← hu, StableComponentGroup.map_mk, StableComponentGroup.map_mk,
    StableComponentGroup.mk_eq_mk_iff]
  refine ⟨n, le_rfl, ?_⟩
  rw [stabilizeGL_refl, MonoidHom.id_apply]
  have hpath : Joined
      (Units.map ((Unitization.starMap (φ 0) :
        Unitization ℂ A →+* Unitization ℂ B).mapMatrix (m := Fin n)).toMonoidHom u)
      (Units.map ((Unitization.starMap (φ 1) :
        Unitization ℂ A →+* Unitization ℂ B).mapMatrix (m := Fin n)).toMonoidHom u) :=
    ⟨⟨⟨_, Unitization.continuous_units_map_starMap hφ u⟩, rfl, rfl⟩⟩
  exact hpath.inv_mul_mem_connectedComponentOfOne

/-- **Zero maps on `K₁`.** The zero star homomorphism induces the trivial map on `K₁`. -/
@[simp]
theorem map_zero_eq_one : map (0 : A →⋆ₙₐ[ℂ] B) = 1 := by
  ext x
  obtain ⟨n, u, hu⟩ := StableComponentGroup.exists_mk (x : StableComponentGroup (Unitization ℂ A))
  rw [coe_map, ← hu, StableComponentGroup.map_mk, MonoidHom.one_apply, OneMemClass.coe_one]
  have h : Units.map ((Unitization.starMap (0 : A →⋆ₙₐ[ℂ] B) :
      Unitization ℂ A →+* Unitization ℂ B).mapMatrix (m := Fin n)).toMonoidHom u =
        unitizationGLInl ℂ B (Fin n) (unitizationGLFst ℂ A (Fin n) u) := by
    refine Units.ext (Matrix.ext fun i j ↦ Unitization.ext ?_ ?_) <;> simp
  rw [h, ← map_inlRingHom_mk, Subsingleton.elim (StableComponentGroup.mk ℂ n _) 1, map_one]

end UnitizationKOne

end TauCeti
