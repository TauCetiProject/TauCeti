/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Module.Primitive
public import TauCeti.Geometry.Toric.Algebraic.Cone
public import TauCeti.Geometry.Toric.Algebraic.Lattice
public import TauCeti.Geometry.Toric.Algebraic.Ray.Basic

/-!
# Primitive generators of toric rays

A rational salient ray in an integral lattice contains a unique primitive lattice vector pointing
along it. This file characterizes that vector as the primitive generator and provides a canonical
choice for each ray of a toric cone.

Primitive generators give canonical integral vectors for the rays of a toric cone. They are the
vectors which enter the definition of a regular cone and, later, its affine monomial coordinates.

## Main declarations

* `TauCeti.Toric.IsPrimitiveGenerator`: a primitive lattice vector on a ray.
* `TauCeti.Toric.IsToricCone.existsUnique_primitiveGenerator`: every ray of a toric cone in an
  integral lattice has a unique primitive generator.
* `TauCeti.Toric.primitiveGenerator`: the resulting canonical lattice vector, with membership,
  nonvanishing, and primitivity lemmas.

## References

The construction is from §1.2 of W. Fulton, *Introduction to Toric Varieties*, and §1.2 of
D. Cox, J. Little and H. Schenck, *Toric Varieties*.
-/

public section

namespace TauCeti.Toric

variable {N V : Type*} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V} {σ : PointedCone ℝ V}

/-- A primitive lattice generator of a ray is a primitive lattice vector pointing along the ray. -/
-- Interface source: `TauCetiRoadmap/AnalyticToricGeometry/Suggested.lean`.
def IsPrimitiveGenerator (i : N →+ V) {σ : PointedCone ℝ V}
    (ρ : ToricRay σ) (v : N) : Prop :=
  i v ∈ ρ ∧ IsPrimitive v

/-- The characteristic property of a primitive generator. -/
theorem isPrimitiveGenerator_iff {ρ : ToricRay σ} {v : N} :
    IsPrimitiveGenerator i ρ v ↔ i v ∈ ρ ∧ IsPrimitive v :=
  Iff.rfl

namespace IsPrimitiveGenerator

variable {ρ : ToricRay σ} {v : N}

/-- A primitive generator points along its ray. -/
theorem mem (h : IsPrimitiveGenerator i ρ v) : i v ∈ ρ := h.1

/-- A primitive generator is primitive. -/
theorem isPrimitive (h : IsPrimitiveGenerator i ρ v) : IsPrimitive v := h.2

/-- A primitive generator is nonzero. -/
theorem ne_zero (h : IsPrimitiveGenerator i ρ v) : v ≠ 0 := h.isPrimitive.ne_zero

end IsPrimitiveGenerator

namespace IsToricCone

/-- Every toric ray in an integral lattice has a unique primitive generator. -/
theorem existsUnique_primitiveGenerator {ρ : ToricRay σ}
    (hρ : IsToricCone i ρ.toPointedCone) (hi : IsIntegralLattice i) :
    ∃! v : N, IsPrimitiveGenerator i ρ v := by
  let _ := hi.free
  obtain ⟨n, hnρ, hn0⟩ := hρ.rational.exists_mem_ne_zero ρ.toPointedCone_ne_bot
  have hn : n ≠ 0 := fun h ↦ hn0 (by simp [h])
  obtain ⟨d, v, hd, hv, hnv⟩ := exists_eq_zsmul_isPrimitive hn
  have hdℝ : (0 : ℝ) < d := by exact_mod_cast hd
  have hvρ : i v ∈ ρ := by
    have hscaled := ρ.toPointedCone.smul_mem (inv_nonneg.mpr hdℝ.le) hnρ
    rw [hnv, map_zsmul, ← Int.cast_smul_eq_zsmul ℝ,
      inv_smul_smul₀ hdℝ.ne'] at hscaled
    exact hscaled
  have hvgen : IsPrimitiveGenerator i ρ v := ⟨hvρ, hv⟩
  refine ⟨v, hvgen, fun u hu ↦ ?_⟩
  have hρeq : ρ.toPointedCone = PointedCone.hull ℝ {i v} :=
    ρ.eq_hull_singleton hρ.salient hvρ (by simpa using hi.injective.ne hv.ne_zero)
  have huρ : i u ∈ ρ.toPointedCone := hu.mem
  rw [hρeq] at huρ
  obtain ⟨a, ha, hau⟩ := PointedCone.mem_hull_singleton.mp huρ
  obtain ⟨f, hfv⟩ := isPrimitive_def.mp hv
  let g : V →ₗ[ℝ] ℝ := hi.extend (Int.castAddHom ℝ) f.toAddMonoidHom
  have hg (x : N) : g (i x) = (f x : ℝ) := by
    have hcast (z : ℤ) : (Int.castAddHom ℝ) z = (z : ℝ) := rfl
    have hcoe : f.toAddMonoidHom x = f x := rfl
    simpa only [g, hcast, hcoe] using
      hi.extend_apply (Int.castAddHom ℝ) f.toAddMonoidHom x
  have haInt : a = (f u : ℝ) := by
    have h := congrArg g hau
    rw [map_smul, hg, hg, hfv, Int.cast_one, smul_eq_mul, mul_one] at h
    exact h
  let k := f u
  have hk0 : 0 ≤ k := by exact_mod_cast haInt ▸ ha
  let m := k.toNat
  have hmk : (m : ℤ) = k := Int.toNat_of_nonneg hk0
  have ham : a = (m : ℝ) := by
    calc
      a = (k : ℝ) := haInt
      _ = (m : ℝ) := by exact_mod_cast hmk.symm
  have huv : u = m • v := by
    apply hi.injective
    rw [map_nsmul, ← Nat.cast_smul_eq_nsmul ℝ, ← ham, hau]
  exact huv.trans (by rw [hu.isPrimitive.eq_one_of_eq_nsmul huv, one_nsmul])

end IsToricCone

/-- The canonical primitive lattice generator of a ray of a toric cone. -/
noncomputable def primitiveGenerator (hi : IsIntegralLattice i) (hσ : IsToricCone i σ)
    (ρ : ToricRay σ) : N :=
  ((hσ.face ρ.1).existsUnique_primitiveGenerator hi).choose

/-- The canonical primitive generator satisfies the defining primitive-generator property. -/
theorem isPrimitiveGenerator_primitiveGenerator (hi : IsIntegralLattice i)
    (hσ : IsToricCone i σ) (ρ : ToricRay σ) :
    IsPrimitiveGenerator i ρ (primitiveGenerator hi hσ ρ) :=
  ((hσ.face ρ.1).existsUnique_primitiveGenerator hi).choose_spec.1

/-- The image of the primitive generator lies on its ray. -/
@[simp]
theorem primitiveGenerator_mem (hi : IsIntegralLattice i) (hσ : IsToricCone i σ)
    (ρ : ToricRay σ) : i (primitiveGenerator hi hσ ρ) ∈ ρ :=
  (isPrimitiveGenerator_primitiveGenerator hi hσ ρ).mem

/-- The primitive generator is primitive. -/
@[simp]
theorem primitiveGenerator_isPrimitive (hi : IsIntegralLattice i) (hσ : IsToricCone i σ)
    (ρ : ToricRay σ) : IsPrimitive (primitiveGenerator hi hσ ρ) :=
  (isPrimitiveGenerator_primitiveGenerator hi hσ ρ).isPrimitive

/-- The primitive generator is nonzero. -/
@[simp]
theorem primitiveGenerator_ne_zero (hi : IsIntegralLattice i) (hσ : IsToricCone i σ)
    (ρ : ToricRay σ) : primitiveGenerator hi hσ ρ ≠ 0 :=
  (isPrimitiveGenerator_primitiveGenerator hi hσ ρ).ne_zero

/-- Every primitive generator of a ray is its canonical primitive generator. -/
theorem IsPrimitiveGenerator.eq_primitiveGenerator {v : N} (hv : IsPrimitiveGenerator i ρ v)
    (hi : IsIntegralLattice i) (hσ : IsToricCone i σ) :
    v = primitiveGenerator hi hσ ρ :=
  ((hσ.face ρ.1).existsUnique_primitiveGenerator hi).choose_spec.2 v hv

/-- A lattice vector is a primitive generator of a ray exactly when it is the canonical one. -/
@[simp]
theorem isPrimitiveGenerator_iff_eq_primitiveGenerator {v : N} (hi : IsIntegralLattice i)
    (hσ : IsToricCone i σ) (ρ : ToricRay σ) :
    IsPrimitiveGenerator i ρ v ↔ v = primitiveGenerator hi hσ ρ :=
  ⟨fun hv ↦ hv.eq_primitiveGenerator hi hσ,
    fun hv ↦ hv ▸ isPrimitiveGenerator_primitiveGenerator hi hσ ρ⟩

end TauCeti.Toric
