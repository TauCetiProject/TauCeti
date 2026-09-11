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

A rational ray in an integral lattice contains a unique first lattice point. This file calls it
the primitive generator of the ray. Existence is obtained by dividing the coordinates of any
nonzero lattice point on the ray by their gcd. Uniqueness uses Bezout's identity: if a second
lattice point lies on the same half-line, its real scaling factor is an integer, and primitivity
forces that integer to be one.

Primitive generators give canonical integral vectors for the rays of a toric cone. They are the
vectors which enter the definition of a regular cone and, later, its affine monomial coordinates.

## Main declarations

* `TauCeti.Toric.IsPrimitiveGenerator`: a nonzero lattice vector on a ray which is not a proper
  positive natural multiple of another lattice vector.
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

/-- A primitive lattice generator of a ray is a nonzero lattice vector pointing along the ray
which is not a proper positive natural multiple of another lattice vector. -/
-- Interface source: `TauCetiRoadmap/AnalyticToricGeometry/Suggested.lean`.
def IsPrimitiveGenerator (i : N →+ V) {σ : PointedCone ℝ V}
    (ρ : ToricRay σ) (v : N) : Prop :=
  i v ∈ ρ ∧ v ≠ 0 ∧
    ∀ (m : ℕ), 0 < m → ∀ w : N, v = m • w → m = 1

/-- The characteristic property of a primitive generator. -/
theorem isPrimitiveGenerator_iff {ρ : ToricRay σ} {v : N} :
    IsPrimitiveGenerator i ρ v ↔
      i v ∈ ρ ∧ v ≠ 0 ∧ ∀ (m : ℕ), 0 < m → ∀ w : N, v = m • w → m = 1 :=
  Iff.rfl

namespace IsPrimitiveGenerator

variable {ρ : ToricRay σ} {v : N}

/-- A primitive generator points along its ray. -/
theorem mem (h : IsPrimitiveGenerator i ρ v) : i v ∈ ρ := h.1

/-- A primitive generator is nonzero. -/
theorem ne_zero (h : IsPrimitiveGenerator i ρ v) : v ≠ 0 := h.2.1

/-- A primitive generator cannot be a proper positive natural multiple. -/
theorem eq_one_of_eq_nsmul (h : IsPrimitiveGenerator i ρ v) {m : ℕ} (hm : 0 < m)
    (w : N) (hw : v = m • w) : m = 1 := h.2.2 m hm w hw

end IsPrimitiveGenerator

namespace IsToricCone

/-- Every ray of a toric cone in an integral lattice has a unique primitive generator. -/
theorem existsUnique_primitiveGenerator (hσ : IsToricCone i σ) (hi : IsIntegralLattice i)
    (ρ : ToricRay σ) :
    ∃! v : N, IsPrimitiveGenerator i ρ v := by
  let _ := hi.free
  have hρtoric := hσ.of_isFaceOf ρ.1.isFaceOf
  obtain ⟨n, hnρ, hn0⟩ := hρtoric.rational.exists_mem_ne_zero ρ.toPointedCone_ne_bot
  have hn : n ≠ 0 := fun h ↦ hn0 (by simp [h])
  obtain ⟨d, v, hd, hv, hnv⟩ := exists_eq_zsmul_isPrimitive hn
  have hdℝ : (0 : ℝ) < d := by exact_mod_cast hd
  have hvρ : i v ∈ ρ := by
    have hscaled := ρ.toPointedCone.smul_mem (inv_nonneg.mpr hdℝ.le) hnρ
    rw [hnv, map_zsmul, ← Int.cast_smul_eq_zsmul ℝ,
      inv_smul_smul₀ hdℝ.ne'] at hscaled
    exact hscaled
  have hvgen : IsPrimitiveGenerator i ρ v :=
    ⟨hvρ, hv.ne_zero, fun _ _ _ hvw ↦ hv.eq_one_of_eq_nsmul hvw⟩
  refine ⟨v, hvgen, fun u hu ↦ ?_⟩
  have hρsalient : (ρ.toPointedCone : ConvexCone ℝ V).Salient :=
    hσ.salient.anti fun _ hx ↦ ρ.1.isFaceOf.le hx
  have hρeq : ρ.toPointedCone = PointedCone.hull ℝ {i v} :=
    ρ.eq_hull_singleton hρsalient hvρ (by simpa using hi.injective.ne hv.ne_zero)
  have huρ : i u ∈ ρ.toPointedCone := hu.mem
  rw [hρeq] at huρ
  obtain ⟨a, ha, hau⟩ := PointedCone.mem_hull_singleton.mp huρ
  obtain ⟨f, hfv⟩ := isPrimitive_def.mp hv
  let g : V →ₗ[ℝ] ℝ := hi.extend (Int.castAddHom ℝ) f.toAddMonoidHom
  have hg (x : N) : g (i x) = (f x : ℝ) := by
    change g (i x) = (Int.castAddHom ℝ) (f x)
    exact hi.extend_apply (Int.castAddHom ℝ) f.toAddMonoidHom x
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
  have hm0 : 0 < m := by
    by_contra hm
    have hm' : m = 0 := Nat.eq_zero_of_not_pos hm
    exact hu.ne_zero (by simpa [hm'] using huv)
  exact huv.trans (by rw [hu.eq_one_of_eq_nsmul hm0 v huv, one_nsmul])

end IsToricCone

/-- The canonical primitive lattice generator of a ray of a toric cone. -/
noncomputable def primitiveGenerator (hi : IsIntegralLattice i) (hσ : IsToricCone i σ)
    (ρ : ToricRay σ) : N :=
  (hσ.existsUnique_primitiveGenerator hi ρ).choose

/-- The canonical primitive generator satisfies the defining primitive-generator property. -/
theorem isPrimitiveGenerator_primitiveGenerator (hi : IsIntegralLattice i)
    (hσ : IsToricCone i σ) (ρ : ToricRay σ) :
    IsPrimitiveGenerator i ρ (primitiveGenerator hi hσ ρ) :=
  (hσ.existsUnique_primitiveGenerator hi ρ).choose_spec.1

/-- The image of the primitive generator lies on its ray. -/
theorem primitiveGenerator_mem (hi : IsIntegralLattice i) (hσ : IsToricCone i σ)
    (ρ : ToricRay σ) : i (primitiveGenerator hi hσ ρ) ∈ ρ :=
  (isPrimitiveGenerator_primitiveGenerator hi hσ ρ).mem

/-- The primitive generator is nonzero. -/
theorem primitiveGenerator_ne_zero (hi : IsIntegralLattice i) (hσ : IsToricCone i σ)
    (ρ : ToricRay σ) : primitiveGenerator hi hσ ρ ≠ 0 :=
  (isPrimitiveGenerator_primitiveGenerator hi hσ ρ).ne_zero

/-- Every primitive generator of a ray is its canonical primitive generator. -/
theorem IsPrimitiveGenerator.eq_primitiveGenerator {v : N} (hv : IsPrimitiveGenerator i ρ v)
    (hi : IsIntegralLattice i) (hσ : IsToricCone i σ) :
    v = primitiveGenerator hi hσ ρ :=
  (hσ.existsUnique_primitiveGenerator hi ρ).choose_spec.2 v hv

/-- A lattice vector is a primitive generator of a ray exactly when it is the canonical one. -/
@[simp]
theorem isPrimitiveGenerator_iff_eq_primitiveGenerator {v : N} (hi : IsIntegralLattice i)
    (hσ : IsToricCone i σ) (ρ : ToricRay σ) :
    IsPrimitiveGenerator i ρ v ↔ v = primitiveGenerator hi hσ ρ :=
  ⟨fun hv ↦ hv.eq_primitiveGenerator hi hσ,
    fun hv ↦ hv ▸ isPrimitiveGenerator_primitiveGenerator hi hσ ρ⟩

end TauCeti.Toric
