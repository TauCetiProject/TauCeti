/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.CartierDivisor.WeilComparison
public import TauCeti.AlgebraicGeometry.WeilDivisor.Scheme.EulerCharacteristic

/-!
# Degree of Cartier divisors on a curve

The order of a Cartier divisor at each codimension-one point gives its associated Weil divisor.
Taking the residue-degree-weighted sum of those orders defines its degree. On a proper curve the
degree of a principal Cartier divisor is zero, so principal translation preserves degree.

On a Noetherian integral curve with discrete valuation rings at codimension-one points, the
Weil--Cartier equivalence preserves degree and restricts to an equivalence of degree-zero
divisors. When the curve is proper over a field and the first cohomology of its structure
sheaf is finite dimensional, the comparison of their divisor sheaves identifies this degree
with the Euler-characteristic degree of the associated line bundle.

## References

* R. Hartshorne, *Algebraic Geometry*, Chapter II, Section 6 and Chapter IV, Section 1.
-/

public section

open AlgebraicGeometry CategoryTheory Order

namespace TauCeti.AlgebraicGeometry

universe u

noncomputable section

namespace Scheme.CartierDivisor

variable {X Y : Scheme.{u}} [IsIntegral X] [IsNoetherian X]

/-- The degree of a Cartier divisor relative to `f`, obtained by weighting its orders at
codimension-one points by their residue degrees. -/
def relativeDegree (f : X ⟶ Y) : CartierDivisor X →+ ℤ :=
  (SchemeWeilDivisor.relativeDegree f).comp (toWeilDivisorHom : CartierDivisor X →+ _)

/-- The Cartier degree is the degree of the associated Weil divisor. -/
@[simp]
lemma relativeDegree_apply (f : X ⟶ Y) (D : CartierDivisor X) :
    relativeDegree f D = SchemeWeilDivisor.relativeDegree f D.toWeilDivisor :=
  by simp only [relativeDegree, AddMonoidHom.comp_apply, toWeilDivisorHom_apply]

/-- The degree of a Cartier divisor is the finite sum of its orders times residue degrees. -/
lemma relativeDegree_eq_sum (f : X ⟶ Y) (D : CartierDivisor X) :
    relativeDegree f D =
      D.toWeilDivisor.sum fun x n ↦ n * (f.residueDegree x : ℤ) := by
  rw [relativeDegree_apply, SchemeWeilDivisor.relativeDegree_apply]

/-- The degree-zero Cartier divisors form the kernel of the degree homomorphism. -/
def degreeZero (f : X ⟶ Y) : AddSubgroup (CartierDivisor X) :=
  (relativeDegree f).ker

/-- A Cartier divisor has degree zero exactly when its weighted order sum vanishes. -/
@[simp]
lemma mem_degreeZero_iff (f : X ⟶ Y) (D : CartierDivisor X) :
    D ∈ degreeZero f ↔ relativeDegree f D = 0 :=
  AddMonoidHom.mem_ker

end Scheme.CartierDivisor

namespace SchemeWeilDivisor

variable {X Y : Scheme.{u}} [IsIntegral X] [IsNoetherian X]
  [∀ x : CodimensionOnePoint X, IsDiscreteValuationRing (X.presheaf.stalk (x : X))]

/-- The Weil--Cartier equivalence preserves residue-degree-weighted degree. -/
theorem relativeDegree_equivCartierDivisor (hX : ∀ x : X, coheight x ≤ 1)
    (f : X ⟶ Y) (D : SchemeWeilDivisor X) :
    Scheme.CartierDivisor.relativeDegree f (equivCartierDivisor hX D) =
      relativeDegree f D := by
  rw [Scheme.CartierDivisor.relativeDegree_apply,
    ← equivCartierDivisor_symm_apply hX, AddEquiv.symm_apply_apply]

/-- The Weil--Cartier equivalence restricts to degree-zero divisors. -/
def degreeZeroEquivCartierDivisor (hX : ∀ x : X, coheight x ≤ 1) (f : X ⟶ Y) :
    (relativeDegree f).ker ≃+ Scheme.CartierDivisor.degreeZero f := by
  refine
    { toFun := fun D ↦ ⟨equivCartierDivisor hX D.1, ?_⟩
      invFun := fun D ↦ ⟨(equivCartierDivisor hX).symm D.1, ?_⟩
      left_inv := fun D ↦ Subtype.ext ((equivCartierDivisor hX).symm_apply_apply D.1)
      right_inv := fun D ↦ Subtype.ext ((equivCartierDivisor hX).apply_symm_apply D.1)
      map_add' := fun D E ↦ Subtype.ext (map_add (equivCartierDivisor hX) D.1 E.1) }
  · rw [Scheme.CartierDivisor.mem_degreeZero_iff,
      relativeDegree_equivCartierDivisor]
    exact D.2
  · rw [AddMonoidHom.mem_ker]
    rw [← relativeDegree_equivCartierDivisor hX f,
      (equivCartierDivisor hX).apply_symm_apply]
    exact D.2

/-- The degree-zero Weil--Cartier equivalence sends a divisor to its Cartier divisor. -/
@[simp]
lemma degreeZeroEquivCartierDivisor_apply (hX : ∀ x : X, coheight x ≤ 1) (f : X ⟶ Y)
    (D : (relativeDegree f).ker) :
    ((degreeZeroEquivCartierDivisor hX f D : Scheme.CartierDivisor.degreeZero f) :
      Scheme.CartierDivisor X) = equivCartierDivisor hX D.1 :=
  by simp [degreeZeroEquivCartierDivisor]

/-- The inverse degree-zero equivalence sends a Cartier divisor to its associated Weil divisor. -/
@[simp]
lemma degreeZeroEquivCartierDivisor_symm_apply (hX : ∀ x : X, coheight x ≤ 1)
    (f : X ⟶ Y) (D : Scheme.CartierDivisor.degreeZero f) :
    ((degreeZeroEquivCartierDivisor hX f).symm D : SchemeWeilDivisor X) =
      D.1.toWeilDivisor := by
  rw [← equivCartierDivisor_symm_apply hX]
  simp [degreeZeroEquivCartierDivisor]

end SchemeWeilDivisor

namespace Scheme.CartierDivisor

variable {k : Type u} [Field k] {X : Scheme.{u}} [IsIntegral X] [IsNoetherian X]
  [∀ x : CodimensionOnePoint X, IsDiscreteValuationRing (X.presheaf.stalk (x : X))]
  [X.Over (Spec (.of k))] [IsProper (X ↘ Spec (.of k))]
  [FiniteDimensional k (Scheme.Modules.Cohomology (InvertibleSheaf.trivial X).obj 1)]

/-- A principal Cartier divisor has degree zero on a proper integral curve. -/
theorem relativeDegree_principalCartierDivisor (hX : ∀ x : X, coheight x ≤ 1)
    (g : Additive X.functionFieldˣ) :
    relativeDegree (X ↘ Spec (.of k)) (principalCartierDivisorAddHom X g) = 0 := by
  rw [relativeDegree_apply, principalCartierDivisorAddHom_apply,
    toWeilDivisor_principalCartierDivisor]
  exact SchemeWeilDivisor.relativeDegree_principalDivisor k hX g

/-- Translation by a principal Cartier divisor preserves degree on a proper curve. -/
theorem relativeDegree_add_principalCartierDivisor (hX : ∀ x : X, coheight x ≤ 1)
    (D : CartierDivisor X) (g : Additive X.functionFieldˣ) :
    relativeDegree (X ↘ Spec (.of k)) (D + principalCartierDivisorAddHom X g) =
      relativeDegree (X ↘ Spec (.of k)) D := by
  rw [map_add, relativeDegree_principalCartierDivisor hX, add_zero]

/-- Principal Cartier divisors lie in the degree-zero subgroup. -/
theorem principalCartierDivisor_mem_degreeZero (hX : ∀ x : X, coheight x ≤ 1)
    (g : Additive X.functionFieldˣ) :
    principalCartierDivisorAddHom X g ∈ degreeZero (X ↘ Spec (.of k)) := by
  rw [mem_degreeZero_iff]
  exact relativeDegree_principalCartierDivisor hX g

/-- The Euler-characteristic degree of the line bundle of a Cartier divisor equals its
residue-degree-weighted degree. -/
@[simp]
theorem eulerDegree_toLineBundleClass (hX : ∀ x : X, coheight x ≤ 1)
    (D : CartierDivisor X) :
    LineBundleClass.eulerDegree k D.toLineBundleClass =
      relativeDegree (X ↘ Spec (.of k)) D := by
  have hmk : D.toLineBundleClass = LineBundleClass.mk D.toInvertibleSheaf :=
    toLineBundleClass_eq_mk_iff.mpr ⟨(eqToIso (toInvertibleSheaf_obj D)).symm⟩
  rw [hmk, LineBundleClass.eulerDegree_mk, relativeDegree_apply]
  exact InvertibleSheaf.eulerDegree_eq_relativeDegree k hX
    ((eqToIso (toInvertibleSheaf_obj D)) ≪≫ D.sheafIsoToWeilDivisor hX)

end Scheme.CartierDivisor

end

end TauCeti.AlgebraicGeometry
