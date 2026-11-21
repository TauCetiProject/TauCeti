/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.Circle
public import Mathlib.GroupTheory.SpecificGroups.Cyclic.Basic
public import TauCeti.LinearAlgebra.Matrix.SpecialOrthogonalGroup.Axis

import Mathlib.RingTheory.IntegralDomain
import TauCeti.LinearAlgebra.Matrix.DotProduct
import TauCeti.LinearAlgebra.Matrix.OrthogonalGroup.Basic

/-!
# Rotations of `ℝ³` fixing a vector

A rotation `g ∈ SO(3)` fixing a unit vector `p` preserves the plane orthogonal to `p`, and acts on
it as a rotation of that oriented plane. Concretely, choose a unit vector `u` orthogonal to `p` and
put `w = p ⨯₃ u`, so that `(p, u, w)` is a positively oriented orthonormal frame. Then

`g u = a • u + b • w` and `g w = a • w - b • u`, with `a² + b² = 1`,

so `g` turns the plane by the unit complex number `a + b i`, where `a = u ⬝ᵥ g u` and
`b = w ⬝ᵥ g u`. This defines a group homomorphism from the stabilizer of `p` to the unit circle,
and it is injective because a rotation fixing both `p` and `u` is the identity.

A finite subgroup of the multiplicative group of a field is cyclic, so **every finite group of
rotations fixing a nonzero vector is cyclic**. This is the step of the classification of the finite
subgroups of `SO(3)` showing that the stabilizer of a pole, the group of rotations of `K` about one
axis, is cyclic.

## Main definitions

* `TauCeti.Matrix.SpecialOrthogonalGroup.stabilizerToCircle K hp hu hpu`: for a group `K` of
  rotations, a unit vector `p` and a unit vector `u` orthogonal to `p`, the homomorphism from the
  stabilizer of `p` in `K` to the unit circle recording how each rotation turns the oriented plane
  with orthonormal basis `(u, p ⨯₃ u)`.

## Main results

* `mulVec_eq_stabilizerToCircle`, `mulVec_cross_eq_stabilizerToCircle`: a rotation `g` fixing `p`
  acts on the basis `(u, p ⨯₃ u)` of the orthogonal plane as multiplication by
  `stabilizerToCircle K hp hu hpu g`.
* `stabilizerToCircle_injective`: this homomorphism is injective.
* `isCyclic_stabilizer`: in a finite group of rotations, the stabilizer of a nonzero vector is
  cyclic.
* `TauCeti.exists_dotProduct_self_eq_one_dotProduct_eq_zero`: every real vector, in dimension at
  least two, is orthogonal to some unit vector.

## References

* M. Artin, *Algebra*, second edition, Pearson, 2011, Section 6.12 (the finite subgroups of the
  rotation group; the stabilizer of a pole is a cyclic group of rotations about its axis).
-/

public section

open Matrix MulAction

/-- **Every real vector is orthogonal to a unit vector**, in dimension at least two. -/
theorem TauCeti.exists_dotProduct_self_eq_one_dotProduct_eq_zero {n : Type*} [Fintype n]
    [Nontrivial n] (p : n → ℝ) : ∃ u, u ⬝ᵥ u = 1 ∧ p ⬝ᵥ u = 0 := by
  obtain ⟨v, hv, hvp⟩ := exists_ne_zero_dotProduct_eq_zero p
  have hpos : 0 < v ⬝ᵥ v :=
    (dotProduct_self_nonneg v).lt_of_ne' (dotProduct_self_eq_zero.not.mpr hv)
  refine ⟨(√(v ⬝ᵥ v))⁻¹ • v, ?_, by rw [dotProduct_smul, dotProduct_comm p, hvp, smul_zero]⟩
  simp only [smul_dotProduct, dotProduct_smul, smul_eq_mul]
  field_simp
  exact (Real.sq_sqrt hpos.le).symm

namespace TauCeti.Matrix.SpecialOrthogonalGroup

section CommRing

/-! ### A rotation fixing `p` acts on the orthogonal plane

Over any commutative ring, let `p` and `u` be orthonormal and `g ∈ SO(3)` fix `p`. -/

variable {R : Type*} [CommRing R] {p u : Fin 3 → R} {g h : Matrix (Fin 3) (Fin 3) R}

private theorem cross_dotProduct_cross_self (hp : p ⬝ᵥ p = 1) (hu : u ⬝ᵥ u = 1)
    (hpu : p ⬝ᵥ u = 0) : (p ⨯₃ u) ⬝ᵥ (p ⨯₃ u) = 1 := by
  rw [cross_dot_cross, hp, hu, dotProduct_comm u p, hpu]
  ring

/-- `g u` lies in the plane spanned by `u` and `p ⨯₃ u`. -/
private theorem mulVec_eq_of_mulVec_eq_self (hg : g ∈ specialOrthogonalGroup (Fin 3) R)
    (hgp : g *ᵥ p = p) (hp : p ⬝ᵥ p = 1) (hu : u ⬝ᵥ u = 1) (hpu : p ⬝ᵥ u = 0) :
    g *ᵥ u = (u ⬝ᵥ (g *ᵥ u)) • u + ((p ⨯₃ u) ⬝ᵥ (g *ᵥ u)) • (p ⨯₃ u) := by
  -- `g u` is orthogonal to `g p = p`.
  have h0 : p ⬝ᵥ (g *ᵥ u) = 0 := by
    rw [← hpu, ← mem_orthogonalGroup_iff_dotProduct_mulVec.mp
      (mem_specialOrthogonalGroup_iff.mp hg).1 p u, hgp]
  conv_lhs =>
    rw [← dotProduct_smul_add_dotProduct_smul_add_cross_dotProduct_smul hp hu hpu (g *ᵥ u)]
  rw [h0, zero_smul, zero_add]

/-- `g (p ⨯₃ u) = p ⨯₃ g u` is `g u` turned by a quarter turn about `p`. -/
private theorem mulVec_cross_eq_of_mulVec_eq_self (hg : g ∈ specialOrthogonalGroup (Fin 3) R)
    (hgp : g *ᵥ p = p) (hp : p ⬝ᵥ p = 1) (hu : u ⬝ᵥ u = 1) (hpu : p ⬝ᵥ u = 0) :
    g *ᵥ (p ⨯₃ u) = (u ⬝ᵥ (g *ᵥ u)) • (p ⨯₃ u) - ((p ⨯₃ u) ⬝ᵥ (g *ᵥ u)) • u := by
  have hgu := mulVec_eq_of_mulVec_eq_self hg hgp hp hu hpu
  set a := u ⬝ᵥ (g *ᵥ u)
  set b := (p ⨯₃ u) ⬝ᵥ (g *ᵥ u)
  rw [← mulVec_cross_mulVec_of_mem_specialOrthogonalGroup hg, hgp, hgu, map_add, map_smul,
    map_smul, cross_cross_eq_smul_sub_smul', hp, hpu]
  module

/-- The two coordinates of `g u` in the basis `(u, p ⨯₃ u)` have squares summing to `1`. -/
private theorem sq_add_sq_of_mulVec_eq_self (hg : g ∈ specialOrthogonalGroup (Fin 3) R)
    (hgp : g *ᵥ p = p) (hp : p ⬝ᵥ p = 1) (hu : u ⬝ᵥ u = 1) (hpu : p ⬝ᵥ u = 0) :
    (u ⬝ᵥ (g *ᵥ u)) ^ 2 + ((p ⨯₃ u) ⬝ᵥ (g *ᵥ u)) ^ 2 = 1 := by
  have h :=
    mem_orthogonalGroup_iff_dotProduct_mulVec.mp (mem_specialOrthogonalGroup_iff.mp hg).1 u u
  rw [hu, mulVec_eq_of_mulVec_eq_self hg hgp hp hu hpu] at h
  simpa [add_dotProduct, dotProduct_add, smul_dotProduct, dotProduct_smul, hu,
    cross_dotProduct_cross_self hp hu hpu, dot_cross_self, dotProduct_comm (p ⨯₃ u) u, sq] using h

/-- The coordinates of `(g * h) u` are those of the product of the complex numbers attached to
`g` and `h`. -/
private theorem mul_mulVec_eq_of_mulVec_eq_self (hg : g ∈ specialOrthogonalGroup (Fin 3) R)
    (hh : h ∈ specialOrthogonalGroup (Fin 3) R) (hgp : g *ᵥ p = p) (hhp : h *ᵥ p = p)
    (hp : p ⬝ᵥ p = 1) (hu : u ⬝ᵥ u = 1) (hpu : p ⬝ᵥ u = 0) :
    u ⬝ᵥ ((g * h) *ᵥ u) =
        u ⬝ᵥ (g *ᵥ u) * u ⬝ᵥ (h *ᵥ u) - (p ⨯₃ u) ⬝ᵥ (g *ᵥ u) * (p ⨯₃ u) ⬝ᵥ (h *ᵥ u) ∧
      (p ⨯₃ u) ⬝ᵥ ((g * h) *ᵥ u) =
        u ⬝ᵥ (g *ᵥ u) * (p ⨯₃ u) ⬝ᵥ (h *ᵥ u) + (p ⨯₃ u) ⬝ᵥ (g *ᵥ u) * u ⬝ᵥ (h *ᵥ u) := by
  have hw := cross_dotProduct_cross_self hp hu hpu
  rw [← mulVec_mulVec, mulVec_eq_of_mulVec_eq_self hh hhp hp hu hpu, mulVec_add, mulVec_smul,
    mulVec_smul, mulVec_cross_eq_of_mulVec_eq_self hg hgp hp hu hpu]
  constructor <;>
  · simp only [dotProduct_add, dotProduct_sub, dotProduct_smul, smul_eq_mul, hu, hw,
      dot_cross_self, dotProduct_comm (p ⨯₃ u) u]
    ring

end CommRing

/-! ### The homomorphism to the circle -/

variable {K : Subgroup (specialOrthogonalGroup (Fin 3) ℝ)} {p u : Fin 3 → ℝ}

/-- The coordinates of `g u` in the basis `(u, p ⨯₃ u)` form a unit complex number. -/
private theorem mem_unitSphere {g : Matrix (Fin 3) (Fin 3) ℝ}
    (hg : g ∈ specialOrthogonalGroup (Fin 3) ℝ) (hgp : g *ᵥ p = p) (hp : p ⬝ᵥ p = 1)
    (hu : u ⬝ᵥ u = 1) (hpu : p ⬝ᵥ u = 0) :
    (⟨u ⬝ᵥ g *ᵥ u, (p ⨯₃ u) ⬝ᵥ g *ᵥ u⟩ : ℂ) ∈ Submonoid.unitSphere ℂ :=
  mem_sphere_zero_iff_norm.2 <| by
    rw [Complex.norm_def, Complex.normSq_mk, ← sq, ← sq,
      sq_add_sq_of_mulVec_eq_self hg hgp hp hu hpu, Real.sqrt_one]

/-- An element of the stabilizer of `p` in `K` is a rotation fixing `p`. -/
private theorem mulVec_eq_self (g : stabilizer K p) : (g : Matrix (Fin 3) (Fin 3) ℝ) *ᵥ p = p :=
  mem_stabilizer_iff.mp g.property

/-- An element of the stabilizer of `p` in `K` is a rotation. -/
private theorem mem_specialOrthogonalGroup (g : stabilizer K p) :
    (g : Matrix (Fin 3) (Fin 3) ℝ) ∈ specialOrthogonalGroup (Fin 3) ℝ :=
  (g : specialOrthogonalGroup (Fin 3) ℝ).property

/-- The unit complex number with coordinates those of `g u` in the basis `(u, p ⨯₃ u)`: the value
of `stabilizerToCircle`, kept as a separate definition so that its coercion to `ℂ` has the rewrite
lemma `coe_toCircle`. -/
private noncomputable def toCircle (hp : p ⬝ᵥ p = 1) (hu : u ⬝ᵥ u = 1) (hpu : p ⬝ᵥ u = 0)
    (g : stabilizer K p) : Circle :=
  ⟨⟨u ⬝ᵥ (g : Matrix (Fin 3) (Fin 3) ℝ) *ᵥ u, (p ⨯₃ u) ⬝ᵥ (g : Matrix (Fin 3) (Fin 3) ℝ) *ᵥ u⟩,
    mem_unitSphere (mem_specialOrthogonalGroup g) (mulVec_eq_self g) hp hu hpu⟩

private theorem coe_toCircle (hp : p ⬝ᵥ p = 1) (hu : u ⬝ᵥ u = 1) (hpu : p ⬝ᵥ u = 0)
    (g : stabilizer K p) :
    (toCircle hp hu hpu g : ℂ) =
      ⟨u ⬝ᵥ (g : Matrix (Fin 3) (Fin 3) ℝ) *ᵥ u, (p ⨯₃ u) ⬝ᵥ (g : Matrix (Fin 3) (Fin 3) ℝ) *ᵥ u⟩ :=
  rfl

variable (K) in
/-- **The rotation of the plane orthogonal to `p`.** For a group `K` of rotations of `ℝ³`, a unit
vector `p` and a unit vector `u` orthogonal to `p`, an element `g` of `K` fixing `p` turns the
oriented plane with orthonormal basis `(u, p ⨯₃ u)` by the unit complex number
`u ⬝ᵥ g u + ((p ⨯₃ u) ⬝ᵥ g u) i` (`mulVec_eq_stabilizerToCircle`). This is a group homomorphism
from the stabilizer of `p` to the unit circle, and it is injective
(`stabilizerToCircle_injective`). -/
noncomputable def stabilizerToCircle (hp : p ⬝ᵥ p = 1) (hu : u ⬝ᵥ u = 1) (hpu : p ⬝ᵥ u = 0) :
    stabilizer K p →* Circle where
  toFun := toCircle hp hu hpu
  map_one' := Circle.ext <| by
    rw [coe_toCircle, Circle.coe_one]
    exact Complex.ext (by simp [hu]) (by simp [dotProduct_comm (p ⨯₃ u) u])
  map_mul' g h := Circle.ext <| by
    obtain ⟨h1, h2⟩ := mul_mulVec_eq_of_mulVec_eq_self (mem_specialOrthogonalGroup g)
      (mem_specialOrthogonalGroup h) (mulVec_eq_self g) (mulVec_eq_self h) hp hu hpu
    rw [Circle.coe_mul, coe_toCircle, coe_toCircle, coe_toCircle]
    exact Complex.ext (by simpa using h1) (by simpa using h2)

/-- The real part of `stabilizerToCircle K hp hu hpu g` is the component `u ⬝ᵥ g u` of `g u`
along `u`. -/
@[simp]
theorem stabilizerToCircle_re (hp : p ⬝ᵥ p = 1) (hu : u ⬝ᵥ u = 1) (hpu : p ⬝ᵥ u = 0)
    (g : stabilizer K p) :
    (stabilizerToCircle K hp hu hpu g : ℂ).re = u ⬝ᵥ (g : Matrix (Fin 3) (Fin 3) ℝ) *ᵥ u :=
  (rfl)

/-- The imaginary part of `stabilizerToCircle K hp hu hpu g` is the component `(p ⨯₃ u) ⬝ᵥ g u`
of `g u` along `p ⨯₃ u`. -/
@[simp]
theorem stabilizerToCircle_im (hp : p ⬝ᵥ p = 1) (hu : u ⬝ᵥ u = 1) (hpu : p ⬝ᵥ u = 0)
    (g : stabilizer K p) :
    (stabilizerToCircle K hp hu hpu g : ℂ).im = (p ⨯₃ u) ⬝ᵥ (g : Matrix (Fin 3) (Fin 3) ℝ) *ᵥ u :=
  (rfl)

/-- **A rotation fixing `p` turns `u` by `stabilizerToCircle`**: writing `z` for
`stabilizerToCircle K hp hu hpu g`, `g u = (re z) • u + (im z) • (p ⨯₃ u)`. -/
theorem mulVec_eq_stabilizerToCircle (hp : p ⬝ᵥ p = 1) (hu : u ⬝ᵥ u = 1) (hpu : p ⬝ᵥ u = 0)
    (g : stabilizer K p) :
    (g : Matrix (Fin 3) (Fin 3) ℝ) *ᵥ u =
      (stabilizerToCircle K hp hu hpu g : ℂ).re • u +
        (stabilizerToCircle K hp hu hpu g : ℂ).im • (p ⨯₃ u) := by
  rw [stabilizerToCircle_re, stabilizerToCircle_im]
  exact mulVec_eq_of_mulVec_eq_self (mem_specialOrthogonalGroup g) (mulVec_eq_self g) hp hu hpu

/-- **A rotation fixing `p` turns `p ⨯₃ u` by `stabilizerToCircle`**: writing `z` for
`stabilizerToCircle K hp hu hpu g`, `g (p ⨯₃ u) = (re z) • (p ⨯₃ u) - (im z) • u`. -/
theorem mulVec_cross_eq_stabilizerToCircle (hp : p ⬝ᵥ p = 1) (hu : u ⬝ᵥ u = 1)
    (hpu : p ⬝ᵥ u = 0) (g : stabilizer K p) :
    (g : Matrix (Fin 3) (Fin 3) ℝ) *ᵥ (p ⨯₃ u) =
      (stabilizerToCircle K hp hu hpu g : ℂ).re • (p ⨯₃ u) -
        (stabilizerToCircle K hp hu hpu g : ℂ).im • u := by
  rw [stabilizerToCircle_re, stabilizerToCircle_im]
  exact mulVec_cross_eq_of_mulVec_eq_self (mem_specialOrthogonalGroup g) (mulVec_eq_self g) hp hu
    hpu

/-- **A rotation fixing `p` is determined by how it turns the plane orthogonal to `p`**: the
homomorphism `stabilizerToCircle` is injective. -/
theorem stabilizerToCircle_injective (hp : p ⬝ᵥ p = 1) (hu : u ⬝ᵥ u = 1) (hpu : p ⬝ᵥ u = 0) :
    Function.Injective (stabilizerToCircle K hp hu hpu) := by
  refine (injective_iff_map_eq_one _).mpr fun g hg ↦ ?_
  -- A rotation sending `1` to `1` fixes `u` as well as `p`.
  have hgu := mulVec_eq_stabilizerToCircle hp hu hpu g
  rw [hg, Circle.coe_one, Complex.one_re, Complex.one_im, one_smul, zero_smul, add_zero] at hgu
  exact Subtype.ext <| Subtype.ext <| Subtype.ext <|
    eq_one_of_mem_specialOrthogonalGroup_of_mulVec_eq_self_of_isRegular_cross_dotProduct
      (mem_specialOrthogonalGroup g) (mulVec_eq_self g) hgu
      (by rw [cross_dotProduct_cross_self hp hu hpu]; exact isRegular_one)

/-- **In a finite group of rotations of `ℝ³`, the stabilizer of a nonzero vector is cyclic.** It
embeds into the unit circle through `stabilizerToCircle`, and a finite subgroup of the
multiplicative group of `ℂ` is cyclic. -/
theorem isCyclic_stabilizer [Finite K] {p : Fin 3 → ℝ} (hp : p ≠ 0) :
    IsCyclic (stabilizer K p) := by
  have hpos : 0 < p ⬝ᵥ p :=
    (dotProduct_self_nonneg p).lt_of_ne' (dotProduct_self_eq_zero.not.mpr hp)
  -- Rescale `p` to the unit vector `c • p` on the same ray, which has the same stabilizer.
  set c : ℝˣ := Units.mk0 (√(p ⬝ᵥ p))⁻¹ (inv_ne_zero (Real.sqrt_pos.mpr hpos).ne')
  have hq : (c • p) ⬝ᵥ (c • p) = 1 := by
    simp only [c, Units.smul_mk0, smul_dotProduct, dotProduct_smul, smul_eq_mul]
    field_simp
    exact (Real.sq_sqrt hpos.le).symm
  obtain ⟨u, hu, hqu⟩ := TauCeti.exists_dotProduct_self_eq_one_dotProduct_eq_zero (c • p)
  rw [← stabilizer_smul_eq_right c p]
  exact isCyclic_of_injective_ringHom (Circle.coeHom.comp (stabilizerToCircle K hq hu hqu))
    (Circle.coe_injective.comp (stabilizerToCircle_injective hq hu hqu))

end TauCeti.Matrix.SpecialOrthogonalGroup
