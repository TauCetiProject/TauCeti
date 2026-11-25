/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.CStarAlgebra.Spectrum
public import Mathlib.Analysis.CStarAlgebra.Unitization
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

The corresponding description by unitaries of `A⁺` is not treated here.

Both rest on the continuous retraction `g ↦ g · s(g)⁻¹` of `GLₙ(A⁺)` onto the matrices with
scalar part `1` (`TauCeti.UnitizationKOne.retract`), where `s(g)` is the scalar part of `g` viewed
in `GLₙ(A⁺)`: it fixes those matrices and maps the identity component of `GLₙ(A⁺)` to a connected
set containing `1`.

When `K₁(𝕜) = 0`, as for `𝕜 = ℂ` since every `GLₙ(ℂ)` is connected, the kernel condition is
vacuous: `K₁(A)` is all of `π₀GL_∞(A⁺)` (`TauCeti.UnitizationKOne.eq_top`,
`TauCeti.UnitizationKOne.equivStableComponentGroup`). For C⋆-algebras `K₁(A)` is functorial for
star homomorphisms through `Unitization.starMap` (`TauCeti.UnitizationKOne.map`, `map_id`,
`map_comp`).

## Main definitions

* `TauCeti.UnitizationKOne`: `K₁(A) = ker(π₀GL_∞(A⁺) → π₀GL_∞(𝕜))`.
* `TauCeti.UnitizationKOne.scalarGL`, `TauCeti.UnitizationKOne.inlGL`: the scalar part
  `GLₙ(A⁺) → GLₙ(𝕜)`, whose kernel is `TauCeti.unitizationGLFstOne`, and the inclusion
  `GLₙ(𝕜) → GLₙ(A⁺)`.
* `TauCeti.UnitizationKOne.retract`: the retraction `g ↦ g · s(g)⁻¹`.
* `TauCeti.UnitizationKOne.map`: functoriality for star homomorphisms of C⋆-algebras.

## Main results

* `TauCeti.UnitizationKOne.exists_mk_eq`, `TauCeti.UnitizationKOne.mk_eq_mk_iff`:
  representatives of `K₁(A)` with scalar part `1`, and homotopies within the scalar condition.
* `TauCeti.UnitizationKOne.map_id`, `TauCeti.UnitizationKOne.map_comp`: functoriality.
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

namespace UnitizationKOne

variable {𝕜 A}

variable (𝕜 A) in
/-- The scalar part `GLₙ(A⁺) →* GLₙ(𝕜)` of an invertible matrix over the unitization. -/
def scalarGL (n : ℕ) : GL (Fin n) (Unitization 𝕜 A) →* GL (Fin n) 𝕜 :=
  Units.map ((Unitization.fstHom 𝕜 A : Unitization 𝕜 A →+* 𝕜).mapMatrix (m := Fin n)).toMonoidHom

variable (𝕜 A) in
/-- The inclusion `GLₙ(𝕜) →* GLₙ(A⁺)` of invertible scalar matrices. -/
def inlGL (n : ℕ) : GL (Fin n) 𝕜 →* GL (Fin n) (Unitization 𝕜 A) :=
  Units.map ((Unitization.inlRingHom 𝕜 A).mapMatrix (m := Fin n)).toMonoidHom

/-- The matrix of the scalar part is the entrywise scalar part. -/
@[simp]
theorem coe_scalarGL {n : ℕ} (u : GL (Fin n) (Unitization 𝕜 A)) :
    ((scalarGL 𝕜 A n u : GL (Fin n) 𝕜) : Matrix (Fin n) (Fin n) 𝕜) =
      (u : Matrix (Fin n) (Fin n) (Unitization 𝕜 A)).map fun x ↦ x.fst :=
  (rfl)

/-- The matrix of an included scalar matrix is its entrywise inclusion. -/
@[simp]
theorem coe_inlGL {n : ℕ} (g : GL (Fin n) 𝕜) :
    ((inlGL 𝕜 A n g : GL (Fin n) (Unitization 𝕜 A)) :
        Matrix (Fin n) (Fin n) (Unitization 𝕜 A)) =
      (g : Matrix (Fin n) (Fin n) 𝕜).map Unitization.inl :=
  (rfl)

variable (𝕜 A) in
/-- The kernel of the scalar part is the group `unitizationGLFstOne` of invertible matrices with
scalar part `1`. -/
theorem ker_scalarGL (n : ℕ) : (scalarGL 𝕜 A n).ker = unitizationGLFstOne 𝕜 A (Fin n) :=
  unitizationGLFstOne_def.symm

/-- An invertible matrix over `A⁺` lies in `unitizationGLFstOne` exactly when its scalar part
`scalarGL` is `1`. -/
theorem mem_unitizationGLFstOne_iff_scalarGL {n : ℕ} {u : GL (Fin n) (Unitization 𝕜 A)} :
    u ∈ unitizationGLFstOne 𝕜 A (Fin n) ↔ scalarGL 𝕜 A n u = 1 := by
  rw [← ker_scalarGL, MonoidHom.mem_ker]

/-- The scalar part of an included scalar matrix is the matrix itself. -/
@[simp]
theorem scalarGL_inlGL {n : ℕ} (g : GL (Fin n) 𝕜) : scalarGL 𝕜 A n (inlGL 𝕜 A n g) = g :=
  Units.ext <| by
    ext i j
    simp

/-- The scalar part is continuous. -/
theorem continuous_scalarGL (n : ℕ) : Continuous (scalarGL 𝕜 A n) :=
  Units.continuous_map (continuous_id.matrix_map Unitization.continuous_fst)

/-- The inclusion of scalar matrices is continuous. -/
theorem continuous_inlGL (n : ℕ) : Continuous (inlGL 𝕜 A n) :=
  Units.continuous_map (continuous_id.matrix_map Unitization.continuous_inl)

/-- The scalar part commutes with stabilization. -/
theorem scalarGL_stabilizeGL {m n : ℕ} (h : m ≤ n) (u : GL (Fin m) (Unitization 𝕜 A)) :
    scalarGL 𝕜 A n (stabilizeGL _ h u) = stabilizeGL 𝕜 h (scalarGL 𝕜 A m u) :=
  (stabilizeGL_map h _ u).symm

variable (𝕜 A) in
/-- The retraction `g ↦ g · s(g)⁻¹` of `GLₙ(A⁺)` onto the invertible matrices with scalar
part `1`, where `s(g)` is the scalar part of `g` included back into `GLₙ(A⁺)`. -/
def retract (n : ℕ) (g : GL (Fin n) (Unitization 𝕜 A)) : GL (Fin n) (Unitization 𝕜 A) :=
  g * (inlGL 𝕜 A n (scalarGL 𝕜 A n g))⁻¹

/-- The retraction multiplies by the inverse of the included scalar part. -/
theorem retract_def {n : ℕ} (g : GL (Fin n) (Unitization 𝕜 A)) :
    retract 𝕜 A n g = g * (inlGL 𝕜 A n (scalarGL 𝕜 A n g))⁻¹ :=
  (rfl)

/-- The retraction has scalar part `1`. -/
theorem retract_mem_unitizationGLFstOne {n : ℕ} (g : GL (Fin n) (Unitization 𝕜 A)) :
    retract 𝕜 A n g ∈ unitizationGLFstOne 𝕜 A (Fin n) :=
  mem_unitizationGLFstOne_iff_scalarGL.2 <| by simp [retract_def]

/-- The retraction fixes the matrices with scalar part `1`. -/
theorem retract_of_mem {n : ℕ} {g : GL (Fin n) (Unitization 𝕜 A)}
    (hg : g ∈ unitizationGLFstOne 𝕜 A (Fin n)) : retract 𝕜 A n g = g := by
  simp [retract_def, mem_unitizationGLFstOne_iff_scalarGL.1 hg]

end UnitizationKOne

variable [RegularNormedAlgebra 𝕜 A]

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
      StableComponentGroup.mk 𝕜 n (scalarGL 𝕜 A n u) :=
  StableComponentGroup.map_mk ..

/-- The class in `π₀GL_∞(A⁺)` of an included scalar matrix is the image of its class. -/
theorem map_inlRingHom_mk (n : ℕ) (g : GL (Fin n) 𝕜) :
    StableComponentGroup.map (Unitization.inlRingHom 𝕜 A) Unitization.continuous_inl
        (StableComponentGroup.mk 𝕜 n g) =
      StableComponentGroup.mk _ n (inlGL 𝕜 A n g) :=
  StableComponentGroup.map_mk ..

/-- The class of an invertible matrix with scalar part `1` lies in `K₁(A)`. -/
theorem mk_mem {n : ℕ} {u : GL (Fin n) (Unitization 𝕜 A)}
    (hu : u ∈ unitizationGLFstOne 𝕜 A (Fin n)) :
    StableComponentGroup.mk _ n u ∈ UnitizationKOne 𝕜 A := by
  rw [mem_iff, map_mk, mem_unitizationGLFstOne_iff_scalarGL.1 hu, map_one]

/-- The retraction is continuous. -/
theorem continuous_retract (n : ℕ) : Continuous (retract 𝕜 A n) :=
  continuous_id.mul ((continuous_inlGL n).comp (continuous_scalarGL n)).inv

/-- **Representatives of `K₁(A)`.** Every class of `K₁(A)` is the class of an invertible matrix
over `A⁺` whose scalar part is the identity. -/
theorem exists_mk_eq {x : StableComponentGroup (Unitization 𝕜 A)}
    (hx : x ∈ UnitizationKOne 𝕜 A) :
    ∃ n, ∃ u ∈ unitizationGLFstOne 𝕜 A (Fin n), StableComponentGroup.mk _ n u = x := by
  obtain ⟨n, g, rfl⟩ := StableComponentGroup.exists_mk x
  refine ⟨n, retract 𝕜 A n g, retract_mem_unitizationGLFstOne g, ?_⟩
  have h₁ : StableComponentGroup.mk 𝕜 n (scalarGL 𝕜 A n g) = 1 := by
    rw [← map_mk]
    exact mem_iff.1 hx
  have h₂ : StableComponentGroup.mk _ n (inlGL 𝕜 A n (scalarGL 𝕜 A n g)) = 1 := by
    rw [← map_inlRingHom_mk, h₁, map_one]
  rw [retract_def, map_mul, map_inv, h₂, inv_one, mul_one]

/-- An invertible matrix with scalar part `1` in the identity component of `GLₙ(A⁺)` lies in
the identity component of the group of invertible matrices with scalar part `1`. -/
theorem mem_connectedComponentIn_of_mem_connectedComponent {n : ℕ}
    {g : GL (Fin n) (Unitization 𝕜 A)} (hg : g ∈ unitizationGLFstOne 𝕜 A (Fin n))
    (hg₀ : g ∈ connectedComponent 1) :
    g ∈ connectedComponentIn (unitizationGLFstOne 𝕜 A (Fin n) : Set _) 1 := by
  have hconn : IsPreconnected (retract 𝕜 A n '' connectedComponent 1) :=
    isPreconnected_connectedComponent.image _ (continuous_retract n).continuousOn
  have h1 : (1 : GL (Fin n) (Unitization 𝕜 A)) ∈ retract 𝕜 A n '' connectedComponent 1 :=
    ⟨1, mem_connectedComponent, retract_of_mem (one_mem _)⟩
  refine hconn.subset_connectedComponentIn h1 ?_ ⟨g, hg₀, retract_of_mem hg⟩
  rintro _ ⟨u, -, rfl⟩
  exact retract_mem_unitizationGLFstOne u

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
  · refine mem_connectedComponentIn_of_mem_connectedComponent ?_ hc
    rw [mem_unitizationGLFstOne_iff_scalarGL, scalarGL_stabilizeGL, map_mul, map_inv,
      mem_unitizationGLFstOne_iff_scalarGL.1 hu, mem_unitizationGLFstOne_iff_scalarGL.1 hv,
      inv_one, one_mul, map_one]
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

/-- **Functoriality of `K₁`** for star homomorphisms of C⋆-algebras, through the unitization. -/
def map (φ : A →⋆ₙₐ[ℂ] B) : UnitizationKOne ℂ A →* UnitizationKOne ℂ B :=
  ((StableComponentGroup.map (Unitization.starMap φ : Unitization ℂ A →+* Unitization ℂ B)
    (Unitization.continuous_starMap φ)).comp (UnitizationKOne ℂ A).subtype).codRestrict
    (UnitizationKOne ℂ B) fun x ↦ by
      have h : (Unitization.fstHom ℂ B : Unitization ℂ B →+* ℂ).comp
          (Unitization.starMap φ : Unitization ℂ A →+* Unitization ℂ B) =
            (Unitization.fstHom ℂ A : Unitization ℂ A →+* ℂ) :=
        RingHom.ext fun x ↦ by simp
      rw [mem_iff, MonoidHom.comp_apply, StableComponentGroup.map_map]
      simp_rw [h]
      exact mem_iff.1 x.property

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

end UnitizationKOne

end TauCeti
