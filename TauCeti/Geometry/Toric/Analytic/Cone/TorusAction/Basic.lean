/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Toric.Analytic.Character.Action
public import TauCeti.Geometry.Toric.Analytic.Character.Basic
public import TauCeti.Geometry.Toric.Analytic.Cone.Chart

/-!
# The torus action on the affine chart of a toric cone

The coordinate-free complex torus `ComplexTorus N` of an integral lattice `N` consists of the
invertible characters of the character lattice `N →+ ℤ`. The dual semigroup of a toric cone `σ`
is a submonoid of that lattice, so the torus acts on the complex points of the affine toric scheme
of `σ` by restricting characters to the dual semigroup and multiplying values on monomials.

In the affine analytic chart attached to an integral basis extending the primitive ray generators
of `σ`, the action is coordinatewise multiplication: a torus point multiplies the coordinate
indexed by a basis vector by its value on the coordinate functional of that vector. The orbit of
the distinguished point, at which every monomial takes the value `1`, is exactly the locus where
all ray coordinates are nonzero; the torus acts freely on it, so it is a copy of the torus, and it
is open and dense in the chart. This is the dense torus of the affine toric variety of `σ`.

## Main declarations

* `TauCeti.Toric.coneChartEquiv_smul_fst` and `TauCeti.Toric.coneChartEquiv_smul_snd`: in the
  chart of an extending basis the torus acts by coordinatewise multiplication.
* `TauCeti.Toric.complexTorus_smul_default_injective`: the torus acts freely on the distinguished
  point.
* `TauCeti.Toric.mem_orbit_complexTorus_default_iff`: the torus orbit of the distinguished point is
  the locus where every ray coordinate is nonzero.
* `TauCeti.Toric.orbit_complexTorus_default_eq_orbit`: every invertible character of the dual
  semigroup is the restriction of a torus point, so the torus orbit is the orbit under all
  invertible characters of the dual semigroup.
* `TauCeti.Toric.isOpen_orbit_complexTorus_default` and
  `TauCeti.Toric.dense_orbit_complexTorus_default`: the dense torus of the chart is open and dense.
* `TauCeti.Toric.zeroConeChartHomeomorphOfBasis`: any extending basis and finite generating
  family identify the affine chart of the zero cone with the coordinate-free complex torus.
* `TauCeti.Toric.zeroConeChartHomeomorphOfBasis_apply`: this identification sends a torus point
  to its translate of the distinguished point.

## References

* W. Fulton, *Introduction to Toric Varieties*, §§1.2 and 2.1.
* D. Cox, J. Little and H. Schenck, *Toric Varieties*, §§1.1, 3.1 and 3.2.
-/

public section

open Multiplicative Topology

namespace TauCeti.Toric

open AffineSemigroupComplexPoint

variable {N V ι : Type*} [AddCommGroup N]
  [AddCommGroup V] [Module ℝ V] {i : N →+ V} {σ : PointedCone ℝ V} {s : ℕ}

variable (hi : IsIntegralLattice i) (hσ : IsToricCone i σ)
  {b : Module.Basis (ToricRay σ ⊕ ι) ℤ N} (hb : ∀ ρ, IsPrimitiveGenerator i ρ (b (Sum.inl ρ)))

include hσ hb

/-! ### The action in the chart of an extending basis -/

/-- A torus point multiplies the coordinate of the chart indexed by a ray by its value on the
coordinate functional of the primitive generator of that ray. -/
theorem coneChartEquiv_smul_fst (T : ComplexTorus N)
    (x : AffineSemigroupComplexPoint (dualSemigroup hi σ)) (ρ : ToricRay σ) :
    (coneChartEquiv hi hσ hb (T • x)).1 ρ =
      T (b.coord (Sum.inl ρ)).toAddMonoidHom * (coneChartEquiv hi hσ hb x).1 ρ := by
  simp

/-- A torus point multiplies the coordinate of the chart indexed by a complementary basis vector
by its value on the coordinate functional of that vector. -/
theorem coneChartEquiv_smul_snd (T : ComplexTorus N)
    (x : AffineSemigroupComplexPoint (dualSemigroup hi σ)) (j : ι) :
    (coneChartEquiv hi hσ hb (T • x)).2 j =
      T (b.coord (Sum.inr j)).toAddMonoidHom * (coneChartEquiv hi hσ hb x).2 j :=
  Units.ext (by simp)

/-- The distinguished point has all chart coordinates equal to `1`. -/
@[simp]
theorem coneChartEquiv_default :
    coneChartEquiv hi hσ hb (default : AffineSemigroupComplexPoint (dualSemigroup hi σ)) = 1 :=
  Prod.ext (funext fun ρ ↦ by simp) (funext fun j ↦ Units.ext (by simp))

/-! ### The dense torus of the chart -/

/-- The torus acts freely on the distinguished point of the affine chart: the coordinate
functionals of an extending basis lie in the dual semigroup and determine a torus point. -/
theorem complexTorus_smul_default_injective :
    Function.Injective fun T : ComplexTorus N ↦
      T • (default : AffineSemigroupComplexPoint (dualSemigroup hi σ)) := by
  let _ := hi.finite
  intro T T' h
  refine b.complexTorusCoordinates.injective (funext fun c ↦ ?_)
  have h' := congrArg (coneChartEquiv hi hσ hb) h
  rcases c with ρ | j
  · have hρ := congrArg (fun z : (ToricRay σ → ℂ) × (ι → ℂˣ) ↦ z.1 ρ) h'
    exact Units.ext (by simpa using hρ)
  · have hj := congrArg (fun z : (ToricRay σ → ℂ) × (ι → ℂˣ) ↦ (z.2 j : ℂ)) h'
    exact Units.ext (by simpa using hj)

/-- The torus orbit of the distinguished point is the locus of the affine chart where every ray
coordinate is nonzero: a point with nonzero ray coordinates is the translate of the distinguished
point by the torus point with those basis coordinates. -/
theorem mem_orbit_complexTorus_default_iff
    {x : AffineSemigroupComplexPoint (dualSemigroup hi σ)} :
    x ∈ MulAction.orbit (ComplexTorus N)
        (default : AffineSemigroupComplexPoint (dualSemigroup hi σ)) ↔
      ∀ ρ, (coneChartEquiv hi hσ hb x).1 ρ ≠ 0 := by
  let _ := hi.finite
  refine ⟨?_, fun h ↦ ?_⟩
  · rintro ⟨T, rfl⟩ ρ
    simp
  · refine ⟨b.complexTorusCoordinates.symm
      (Sum.elim (fun ρ ↦ Units.mk0 _ (h ρ)) (coneChartEquiv hi hσ hb x).2),
      (coneChartEquiv hi hσ hb).injective ?_⟩
    exact Prod.ext (funext fun ρ ↦ by simp) (funext fun j ↦ Units.ext (by simp))

/-- Every invertible character of the dual semigroup of a cone with an extending basis is the
restriction of a torus point: the torus orbit of the distinguished point is its orbit under all
invertible characters of the dual semigroup. -/
theorem orbit_complexTorus_default_eq_orbit :
    MulAction.orbit (ComplexTorus N)
        (default : AffineSemigroupComplexPoint (dualSemigroup hi σ)) =
      MulAction.orbit (AddChar (dualSemigroup hi σ) ℂˣ)
        (default : AffineSemigroupComplexPoint (dualSemigroup hi σ)) := by
  refine (orbit_default_subset _).antisymm ?_
  rintro _ ⟨t, rfl⟩
  rw [mem_orbit_complexTorus_default_iff hi hσ hb]
  intro ρ
  simp

/-- The dense torus of the affine chart is open for the monomial-embedding topology of any finite
generating family of the dual semigroup. -/
theorem isOpen_orbit_complexTorus_default (g : AddGeneratingFamily (dualSemigroup hi σ) s) :
    IsOpen[affinePointTopology g] (MulAction.orbit (ComplexTorus N)
      (default : AffineSemigroupComplexPoint (dualSemigroup hi σ))) := by
  rw [orbit_complexTorus_default_eq_orbit hi hσ hb]
  exact AffineSemigroupComplexPoint.isOpen_orbit_default g

/-- The dense torus of the affine chart is dense for the monomial-embedding topology of any finite
generating family of the dual semigroup. -/
theorem dense_orbit_complexTorus_default (g : AddGeneratingFamily (dualSemigroup hi σ) s) :
    @Dense _ (affinePointTopology g) (MulAction.orbit (ComplexTorus N)
      (default : AffineSemigroupComplexPoint (dualSemigroup hi σ))) := by
  rw [orbit_complexTorus_default_eq_orbit hi hσ hb]
  exact dense_orbit_default g (regularDualSemigroupEquiv hi hσ hb)

omit hσ hb

/-! ### The affine chart of the zero cone -/

/-- An extending basis identifies the coordinate-free complex torus with the affine chart of the
zero cone, for the monomial-embedding topology of any finite generating family. The identification
sends a torus point to its translate of the distinguished point, independently of these choices. -/
noncomputable def zeroConeChartHomeomorphOfBasis {l s : ℕ}
    {B : Module.Basis (ToricRay (⊥ : PointedCone ℝ V) ⊕ Fin l) ℤ N}
    (hB : ∀ ρ, IsPrimitiveGenerator i ρ (B (Sum.inl ρ)))
    (g : AddGeneratingFamily (dualSemigroup hi (⊥ : PointedCone ℝ V)) s) :
    @Homeomorph (ComplexTorus N) (AffineSemigroupComplexPoint (dualSemigroup hi ⊥))
      inferInstance (affinePointTopology g) :=
  let _ := affinePointTopology g
  (((complexTorusCoordinatesContinuousMulEquiv B.integralCharacterRepr).toHomeomorph.trans
    Homeomorph.sumArrowHomeomorphProdArrow).trans
      (Homeomorph.uniqueProd (ToricRay (⊥ : PointedCone ℝ V) → ℂˣ) (Fin l → ℂˣ))).trans
        ((coneChartHomeomorph hi (isToricCone_bot i) hB g).trans
          (Homeomorph.uniqueProd (ToricRay (⊥ : PointedCone ℝ V) → ℂ) (Fin l → ℂˣ))).symm

/-- The zero-cone chart identification is the orbit map of the distinguished point. -/
@[simp]
theorem zeroConeChartHomeomorphOfBasis_apply {l s : ℕ}
    {B : Module.Basis (ToricRay (⊥ : PointedCone ℝ V) ⊕ Fin l) ℤ N}
    (hB : ∀ ρ, IsPrimitiveGenerator i ρ (B (Sum.inl ρ)))
    (g : AddGeneratingFamily (dualSemigroup hi (⊥ : PointedCone ℝ V)) s)
    (t : ComplexTorus N) :
    zeroConeChartHomeomorphOfBasis hi hB g t =
      t • (default : AffineSemigroupComplexPoint (dualSemigroup hi (⊥ : PointedCone ℝ V))) := by
  classical
  let _ := affinePointTopology g
  apply ((coneChartHomeomorph hi (isToricCone_bot i) hB g).trans
    (Homeomorph.uniqueProd (ToricRay (⊥ : PointedCone ℝ V) → ℂ) (Fin l → ℂˣ))).injective
  simp only [zeroConeChartHomeomorphOfBasis, Homeomorph.trans_apply,
    Homeomorph.apply_symm_apply, Homeomorph.coe_uniqueProd, coe_coneChartHomeomorph,
    Homeomorph.sumArrowHomeomorphProdArrow_apply, ContinuousMulEquiv.toHomeomorph_eq_coe,
    HomeomorphClass.coe_coe, coe_complexTorusCoordinatesContinuousMulEquiv]
  ext j
  simp only [Function.comp_apply, complexTorusCoordinates_apply, coneChartEquiv_smul_snd,
    coneChartEquiv_default, Prod.snd_one, Pi.one_apply, mul_one]
  apply congrArg (fun m : IntegralCharacter N ↦ (t m : ℂ))
  apply B.integralCharacterRepr.injective
  ext a
  simp [Finsupp.single_apply, eq_comm]

end TauCeti.Toric
