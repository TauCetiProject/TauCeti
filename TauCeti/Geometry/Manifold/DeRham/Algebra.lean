/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.DeRham.Wedge
public import TauCeti.Geometry.Manifold.DeRham.DegreeZero
public import TauCeti.RingTheory.GradedAlgebra.DirectSum
import TauCeti.Geometry.Manifold.DifferentialForm.Wedge.Smooth.Assoc

/-!
# The graded de Rham algebra

The direct sum of the real de Rham cohomology groups is an associative unital real algebra.
Multiplication is induced by the wedge of closed smooth forms, and its unit is the class of the
constant function one. Homogeneous elements commute with the Koszul sign `(-1) ^ (k * l)`.
The grading is the natural-number degree of differential forms.

The algebra uses Mathlib's `DirectSum.GRing` and `DirectSum.GAlgebra` constructions; its
homogeneous laws descend the existing associativity and graded commutativity of `SmoothForm.wedge`.

The construction applies to `C²` manifolds with corners without finite-dimensionality,
separation, or completeness assumptions on the model space.

## References

* John M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Chapter 17.
-/

public section

noncomputable section

open scoped ContDiff Manifold DirectSum

namespace TauCeti

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I 2 M] {k l m : ℕ}

namespace deRhamCohomology

-- Equality of degrees transports both the tangent tuple and the selected homology carrier.
private theorem mk_heq_of_apply_eq {a b : ℕ} (h : a = b)
    (φ : closedForms I M a) (ψ : closedForms I M b)
    (hφ : ∀ x (v : Fin a → TangentSpace I x),
      φ.1.1 x v = ψ.1.1 x (v ∘ Fin.cast h.symm)) :
    HEq (mk I a φ) (mk I b ψ) := by
  subst b
  have hφψ : φ = ψ := by
    apply Subtype.ext
    apply Subtype.ext
    funext x
    ext v
    simpa using hφ x v
  rw [hφψ]

/-- The wedge on cohomology is associative after reassociating its degree. -/
theorem wedge_assoc (a : deRhamCohomology I M k) (b : deRhamCohomology I M l)
    (c : deRhamCohomology I M m) :
    GradedMonoid.mk _ (wedge I M (k + l) m (wedge I M k l a b) c) =
      GradedMonoid.mk _ (wedge I M k (l + m) a (wedge I M l m b c)) := by
  obtain ⟨φ, rfl⟩ := mk_surjective I k a
  obtain ⟨ψ, rfl⟩ := mk_surjective I l b
  obtain ⟨χ, rfl⟩ := mk_surjective I m c
  simp only [wedge_mk]
  exact Sigma.ext (Nat.add_assoc k l m) <|
    mk_heq_of_apply_eq (Nat.add_assoc k l m) _ _ (SmoothForm.wedge_assoc_apply φ.1 ψ.1 χ.1)

/-- Homogeneous de Rham classes commute with the Koszul sign. -/
theorem wedge_comm (a : deRhamCohomology I M k) (b : deRhamCohomology I M l) :
    GradedMonoid.mk _ (wedge I M k l a b) =
      GradedMonoid.mk _ ((-1 : ℝ) ^ (k * l) • wedge I M l k b a) := by
  obtain ⟨φ, rfl⟩ := mk_surjective I k a
  obtain ⟨ψ, rfl⟩ := mk_surjective I l b
  simp only [wedge_mk, ← map_smul]
  exact Sigma.ext (Nat.add_comm k l) <|
    mk_heq_of_apply_eq (Nat.add_comm k l) _ _ (SmoothForm.wedge_comm φ.1 ψ.1)

/-- Wedge with the class of a constant function on the right is scalar multiplication. -/
@[simp]
theorem wedge_const (a : deRhamCohomology I M k) (r : ℝ) :
    wedge I M k 0 a (const I M r) = r • a := by
  obtain ⟨φ, rfl⟩ := mk_surjective I k a
  rw [const_eq_mk, wedge_mk, ← map_smul]
  congr 1
  apply Subtype.ext
  apply Subtype.ext
  funext x
  ext v
  simp only [Submodule.coe_smul, Pi.smul_apply,
    ContinuousAlternatingMap.smul_apply]
  rw [SmoothForm.wedge_apply_zero_right]
  simp [coe_closedFormsZeroEquiv_symm_apply, mul_comm]

/-- Wedge with the class of a constant function on the left is scalar multiplication,
after identifying the degree `0 + k` with `k`. -/
theorem const_wedge (r : ℝ) (a : deRhamCohomology I M k) :
    GradedMonoid.mk _ (wedge I M 0 k (const I M r) a) = GradedMonoid.mk _ (r • a) := by
  simpa using (wedge_comm (const I M r) a)

end deRhamCohomology

variable (I M) in
/-- The total de Rham cohomology, graded by natural-number degree. Its product is the wedge. -/
abbrev deRhamAlgebra := ⨁ k : ℕ, deRhamCohomology I M k

namespace deRhamAlgebra

/-- The graded multiplication is the wedge on cohomology. -/
instance gMul : GradedMonoid.GMul (deRhamCohomology I M) where
  mul a b := deRhamCohomology.wedge I M _ _ a b

/-- The graded unit is the class of the constant function one. -/
instance gOne : GradedMonoid.GOne (deRhamCohomology I M) where
  one := deRhamCohomology.const I M 1

/-- The multiplication selected by the graded structure is the cohomology wedge. -/
@[simp]
theorem gMul_mul (a : deRhamCohomology I M k) (b : deRhamCohomology I M l) :
    GradedMonoid.GMul.mul a b = deRhamCohomology.wedge I M k l a b := (rfl)

/-- The unit selected by the graded structure is the constant degree-zero class. -/
@[simp]
theorem gOne_one : (GradedMonoid.GOne.one : deRhamCohomology I M 0) =
    deRhamCohomology.const I M 1 := (rfl)

-- Pattern-matching a `GradedMonoid` as a raw sigma type fails implicit-transparency checks.
-- Keep its carrier intact and explicitly normalize the homogeneous operations in the proofs.
/-- The wedge and its constant-one unit make cohomology a graded monoid. -/
instance gMonoid : GradedMonoid.GMonoid (deRhamCohomology I M) where
  one_mul a := by
    -- Express the sigma-carrier operation in terms of its homogeneous components.
    change GradedMonoid.mk _ (deRhamCohomology.wedge I M 0 a.1
      (deRhamCohomology.const I M 1) a.2) = GradedMonoid.mk a.1 a.2
    simpa only [one_smul] using deRhamCohomology.const_wedge (1 : ℝ) a.2
  mul_one a := by
    -- The right degree is definitionally `a.1 + 0 = a.1`.
    change GradedMonoid.mk _ (deRhamCohomology.wedge I M a.1 0 a.2
      (deRhamCohomology.const I M 1)) = GradedMonoid.mk a.1 a.2
    simp only [deRhamCohomology.wedge_const, one_smul, Nat.add_zero]
  mul_assoc a b c := by
    -- The bundled sigma multiplication carries the same homogeneous wedge components.
    change GradedMonoid.mk _ (deRhamCohomology.wedge I M (a.1 + b.1) c.1
      (deRhamCohomology.wedge I M a.1 b.1 a.2 b.2) c.2) =
      GradedMonoid.mk _ (deRhamCohomology.wedge I M a.1 (b.1 + c.1) a.2
        (deRhamCohomology.wedge I M b.1 c.1 b.2 c.2))
    exact deRhamCohomology.wedge_assoc a.2 b.2 c.2

/-- Additivity of the wedge makes cohomology a graded ring. -/
instance gRing : DirectSum.GRing (deRhamCohomology I M) where
  toGMonoid := gMonoid
  mul_zero := fun _ ↦ map_zero _
  zero_mul := fun _ ↦ LinearMap.map_zero₂ _ _
  mul_add := fun _ _ _ ↦ map_add _ _ _
  add_mul := fun _ _ _ ↦ LinearMap.map_add₂ _ _ _ _
  natCast := fun n ↦ deRhamCohomology.const I M n
  natCast_zero := by simp
  natCast_succ := fun n ↦ by simp [Nat.cast_add, map_add]
  intCast := fun n ↦ deRhamCohomology.const I M n
  intCast_ofNat := fun _ ↦ rfl
  intCast_negSucc_ofNat := fun n ↦ by simp [map_neg, Nat.cast_add]

/-- Real scalars act by multiplication with their constant degree-zero classes. -/
instance gAlgebra : DirectSum.GAlgebra ℝ (deRhamCohomology I M) where
  toFun := (deRhamCohomology.const I M).toAddMonoidHom
  map_one := gOne_one.symm
  map_mul r s := by
    refine congrArg (GradedMonoid.mk 0) ?_
    simp only [gMul_mul, LinearMap.toAddMonoidHom_coe, deRhamCohomology.wedge_const]
    simpa only [smul_eq_mul, mul_comm] using (map_smul (deRhamCohomology.const I M) s r)
  commutes r a := by
    -- Resolve the two sigma products without changing their degree components.
    change GradedMonoid.mk _ (deRhamCohomology.wedge I M 0 a.1
      (deRhamCohomology.const I M r) a.2) = GradedMonoid.mk _
        (deRhamCohomology.wedge I M a.1 0 a.2 (deRhamCohomology.const I M r))
    simpa only [zero_mul, pow_zero, one_smul] using deRhamCohomology.wedge_comm
      (deRhamCohomology.const I M r) a.2
  smul_def r a := by
    -- The sigma action applies the original real action to its homogeneous component.
    change GradedMonoid.mk a.1 (r • a.2) = GradedMonoid.mk _
      (deRhamCohomology.wedge I M 0 a.1 (deRhamCohomology.const I M r) a.2)
    exact (deRhamCohomology.const_wedge r a.2).symm

/-- The scalar homomorphism of the graded algebra is the constant-class map. -/
@[simp]
theorem gAlgebra_toFun (r : ℝ) :
    DirectSum.GAlgebra.toFun (A := deRhamCohomology I M) r = deRhamCohomology.const I M r :=
  (rfl)

/-- Homogeneous elements of the de Rham algebra commute with the Koszul sign. -/
theorem of_mul_of_comm (a : deRhamCohomology I M k) (b : deRhamCohomology I M l) :
    DirectSum.of (deRhamCohomology I M) k a * DirectSum.of (deRhamCohomology I M) l b =
      (-1 : ℝ) ^ (k * l) •
        (DirectSum.of (deRhamCohomology I M) l b * DirectSum.of (deRhamCohomology I M) k a) := by
  rw [DirectSum.of_mul_of, DirectSum.of_mul_of, gMul_mul, gMul_mul, ← DirectSum.of_smul]
  exact DirectSum.of_eq_of_gradedMonoid_eq (deRhamCohomology.wedge_comm a b)

end deRhamAlgebra

end TauCeti
