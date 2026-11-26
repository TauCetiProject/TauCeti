/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Instances.AddCircle.Torus
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import TauCeti.LinearAlgebra.Matrix.Determinant.Basic

/-!
# Straight circles in a torus and their intersections

For an integer vector `u : ι → ℤ` and an additive commutative group `G`, the straight circle of
direction `u` is the homomorphism `g ↦ (u i • g)ᵢ` from `G` to `ι → G`
(`TauCeti.straightCircleHom`). For `G = AddCircle p` it parametrizes the image in the torus
`ι → AddCircle p` of the line through `0` spanned by `p u`. For two coordinates which are
coprime it is injective (`TauCeti.straightCircleHom_injective`), so that its image is an embedded
circle. On the two-torus these are the attaching circles of the standard genus-one Heegaard
diagrams of lens spaces and of `S³`.

Two straight circles of directions `u` and `v` meet in a subgroup of the torus. Its points are
read off from the kernel of the integer matrix `A` with columns `u` and `v`, acting on the torus
`Fin 2 → G` by `Matrix.smulVecHom`: a point `(σ, τ)` of that kernel has
`(u i • σ)ᵢ = ((-v i) • τ)ᵢ`, a point of both circles. When both circles are injective this is an
isomorphism from the kernel onto the intersection (`TauCeti.straightCircleInfEquiv`). On the torus
`Fin 2 → AddCircle p`, `p ≠ 0`, the kernel of `A` has `|det A|` points
(`Matrix.natCard_ker_smulVecHom`), so two straight circles of primitive directions `u` and `v`
meet in exactly `|u₀ v₁ - u₁ v₀|` points (`TauCeti.natCard_straightCircle_inf`), finitely many
exactly when the directions are not parallel (`TauCeti.finite_straightCircle_inf_iff`). When
`det A ≠ 0` the kernel is moreover `ℤ² / A ℤ²` (`Matrix.quotientRangeEquivKerSmulVecHom`), which
identifies the intersection with `ℤ² / ⟨u, v⟩` (`TauCeti.straightCircleInfQuotientEquiv`). The
class of an intersection point `z` is the class of the integer vector `s u + t v`, for real `s`
and `t` such that `z` is the image of `p s u` and also of `-p t v`
(`TauCeti.straightCircleInfQuotientEquiv_apply`): going from `0` to `z` along the first circle and
back along the second one moves through the lattice vector `p (s u + t v)`, and such a loop closes
up whenever `s u + t v` is an integer vector
(`TauCeti.straightCircleHom_add_straightCircleHom_eq_zero`).

## Main definitions

* `TauCeti.straightCircleHom`: the straight circle `g ↦ (u i • g)ᵢ` of direction `u`.
* `TauCeti.straightCircleInfEquiv`: the intersection of two injective straight circles is the
  kernel of the matrix with columns their directions.
* `TauCeti.straightCircleInfQuotientEquiv`: on a torus `Fin 2 → AddCircle p`, the intersection of
  two straight circles of primitive directions `u` and `v` with `det (u, v) ≠ 0` is `ℤ² / ⟨u, v⟩`.

## Main results

* `TauCeti.straightCircleHom_injective`: the straight circle of a primitive direction is
  injective.
* `TauCeti.natCard_straightCircle_inf`: two straight circles of primitive directions `u` and `v` in
  a torus `Fin 2 → AddCircle p` meet in `|u₀ v₁ - u₁ v₀|` points.
* `TauCeti.finite_straightCircle_inf_iff`: they meet in finitely many points exactly when
  `u₀ v₁ - u₁ v₀ ≠ 0`.
* `TauCeti.straightCircleInfQuotientEquiv_apply`: the class of an intersection point in
  `ℤ² / ⟨u, v⟩` is that of the lattice displacement of the loop through it along the two circles.
-/

public section

noncomputable section

open scoped Matrix

namespace TauCeti

variable (G : Type*) [AddCommGroup G] {ι : Type*}

/-- The straight circle of direction `u : ι → ℤ` in `ι → G`, the homomorphism `g ↦ (u i • g)ᵢ`.
For `G = AddCircle p` its image is the image in the torus of the line spanned by `p u`. -/
def straightCircleHom (u : ι → ℤ) : G →+ (ι → G) :=
  AddMonoidHom.pi fun i ↦ zsmulAddGroupHom (u i)

@[simp]
theorem straightCircleHom_apply (u : ι → ℤ) (g : G) (i : ι) :
    straightCircleHom G u g i = u i • g :=
  (rfl)

variable {G}

/-- **A straight circle of primitive direction is injective.** If the two coordinates of
`u : Fin 2 → ℤ` are coprime, then `g ↦ (u 0 • g, u 1 • g)` is injective: with `a u₀ + b u₁ = 1`,
`g = a • (u₀ • g) + b • (u₁ • g)`. -/
theorem straightCircleHom_injective {u : Fin 2 → ℤ} (hu : IsCoprime (u 0) (u 1)) :
    Function.Injective (straightCircleHom G u) := by
  obtain ⟨a, b, hab⟩ := hu
  refine (injective_iff_map_eq_zero _).2 fun g hg ↦ ?_
  have h0 : u 0 • g = 0 := by simpa using congrFun hg 0
  have h1 : u 1 • g = 0 := by simpa using congrFun hg 1
  calc g = (a * u 0 + b * u 1) • g := by rw [hab, one_smul]
    _ = a • (u 0 • g) + b • (u 1 • g) := by rw [add_smul, mul_smul, mul_smul]
    _ = 0 := by rw [h0, h1, smul_zero, smul_zero, add_zero]

/-! ### Intersections of two straight circles -/

section Inf

variable [TopologicalSpace G] [IsTopologicalAddGroup G]

/-- The integer matrix with columns `u` and `v` acts on `Fin 2 → G` by
`(σ, τ) ↦ (u i • σ + v i • τ)ᵢ`, the sum of the two straight circles. -/
theorem smulVecHom_transpose_of_apply (u v : ι → ℤ) (x : Fin 2 → G) :
    (Matrix.of ![u, v])ᵀ.smulVecHom G x =
      straightCircleHom G u (x 0) + straightCircleHom G v (x 1) := by
  ext i
  simp

/-- A point `(σ, τ)` of the kernel of the matrix with columns `u` and `v` gives the point
`(u i • σ)ᵢ = ((-v i) • τ)ᵢ` of both straight circles. -/
private def kerToStraightCircleInf (u v : ι → ℤ) :
    ((Matrix.of ![u, v])ᵀ.smulVecHom G : (Fin 2 → G) →+ (ι → G)).ker →+
      ↥((straightCircleHom G u).range ⊓ (straightCircleHom G v).range) :=
  AddMonoidHom.codRestrict
    ((straightCircleHom G u).comp ((Pi.evalAddMonoidHom (fun _ ↦ G) 0).comp
      (AddSubgroup.subtype _))) _ fun x ↦ by
    refine ⟨⟨_, rfl⟩, -(x : Fin 2 → G) 1, ?_⟩
    have hx := x.property
    rw [AddMonoidHom.mem_ker, AddMonoidHom.coe_ofClass, smulVecHom_transpose_of_apply] at hx
    simp only [AddMonoidHom.coe_comp, Function.comp_apply, AddSubgroup.coe_subtype,
      Pi.evalAddMonoidHom_apply, map_neg]
    exact neg_eq_of_add_eq_zero_left hx

private theorem coe_kerToStraightCircleInf (u v : ι → ℤ)
    (x : ((Matrix.of ![u, v])ᵀ.smulVecHom G : (Fin 2 → G) →+ (ι → G)).ker) :
    (kerToStraightCircleInf u v x : ι → G) = straightCircleHom G u ((x : Fin 2 → G) 0) :=
  (rfl)

private theorem bijective_kerToStraightCircleInf {u v : ι → ℤ}
    (hu : Function.Injective (straightCircleHom G u))
    (hv : Function.Injective (straightCircleHom G v)) :
    Function.Bijective (kerToStraightCircleInf (G := G) u v) := by
  refine ⟨(injective_iff_map_eq_zero _).2 fun x hx ↦ ?_, fun z ↦ ?_⟩
  · have hx0 : (x : Fin 2 → G) 0 = 0 :=
      hu (by rw [← coe_kerToStraightCircleInf, hx, map_zero, AddSubgroup.coe_zero])
    have hker := x.property
    rw [AddMonoidHom.mem_ker, AddMonoidHom.coe_ofClass, smulVecHom_transpose_of_apply, hx0,
      map_zero, zero_add] at hker
    have hx1 : (x : Fin 2 → G) 1 = 0 := hv (by rw [hker, map_zero])
    exact Subtype.ext (funext fun i ↦ by fin_cases i <;> simp [hx0, hx1])
  · obtain ⟨⟨σ, hσ⟩, τ, hτ⟩ := z.property
    refine ⟨⟨![σ, -τ], ?_⟩, Subtype.ext ?_⟩
    · rw [AddMonoidHom.mem_ker, AddMonoidHom.coe_ofClass, smulVecHom_transpose_of_apply]
      simp [hσ, hτ]
    · rw [coe_kerToStraightCircleInf]
      simpa using hσ

/-- **The intersection of two straight circles.** If the straight circles of directions `u` and
`v` are injective, their intersection is isomorphic to the kernel of the matrix with columns `u` and
`v`, the point `z` going to `(σ, -τ)` for the parameters `σ` and `τ` of `z` on the two circles
(`TauCeti.straightCircleInfEquiv_apply`). -/
def straightCircleInfEquiv {u v : ι → ℤ} (hu : Function.Injective (straightCircleHom G u))
    (hv : Function.Injective (straightCircleHom G v)) :
    ↥((straightCircleHom G u).range ⊓ (straightCircleHom G v).range) ≃+
      ((Matrix.of ![u, v])ᵀ.smulVecHom G : (Fin 2 → G) →+ (ι → G)).ker :=
  (AddEquiv.ofBijective _ (bijective_kerToStraightCircleInf hu hv)).symm

/-- The point of the intersection of two straight circles with kernel coordinates `(σ, τ)` is the
point `(u i • σ)ᵢ` of the first circle. -/
theorem coe_straightCircleInfEquiv_symm_apply {u v : ι → ℤ}
    (hu : Function.Injective (straightCircleHom G u))
    (hv : Function.Injective (straightCircleHom G v))
    (x : ((Matrix.of ![u, v])ᵀ.smulVecHom G : (Fin 2 → G) →+ (ι → G)).ker) :
    ((straightCircleInfEquiv hu hv).symm x : ι → G) = straightCircleHom G u ((x : Fin 2 → G) 0) :=
  (rfl)

/-- The kernel coordinates of a point `z` of two straight circles are `(σ, -τ)`, for its
parameters `σ` on the first circle and `τ` on the second one. -/
theorem straightCircleInfEquiv_apply {u v : ι → ℤ}
    (hu : Function.Injective (straightCircleHom G u))
    (hv : Function.Injective (straightCircleHom G v))
    (z : ↥((straightCircleHom G u).range ⊓ (straightCircleHom G v).range)) {σ τ : G}
    (hσ : straightCircleHom G u σ = z) (hτ : straightCircleHom G v τ = z) :
    (straightCircleInfEquiv hu hv z : Fin 2 → G) = ![σ, -τ] := by
  have hmem : ![σ, -τ] ∈ ((Matrix.of ![u, v])ᵀ.smulVecHom G : (Fin 2 → G) →+ (ι → G)).ker := by
    rw [AddMonoidHom.mem_ker, AddMonoidHom.coe_ofClass, smulVecHom_transpose_of_apply]
    simp [hσ, hτ]
  have hz : z = (straightCircleInfEquiv hu hv).symm ⟨_, hmem⟩ :=
    Subtype.ext (by rw [coe_straightCircleInfEquiv_symm_apply]; simpa using hσ.symm)
  rw [hz, AddEquiv.apply_symm_apply]

end Inf

/-! ### Straight circles in a torus -/

section AddCircle

variable (p : ℝ)

/-- **Two straight circles in a two-torus meet in `|det|` points.** In the torus
`Fin 2 → AddCircle p`, `p ≠ 0`, the straight circles of directions `u` and `v` with coprime
coordinates meet in exactly `|u₀ v₁ - u₁ v₀|` points. When `u₀ v₁ - u₁ v₀ = 0` they meet in
infinitely many points and `Nat.card` takes the junk value `0`. -/
theorem natCard_straightCircle_inf (hp : p ≠ 0) {u v : Fin 2 → ℤ} (hu : IsCoprime (u 0) (u 1))
    (hv : IsCoprime (v 0) (v 1)) :
    Nat.card ↥((straightCircleHom (AddCircle p) u).range ⊓
        (straightCircleHom (AddCircle p) v).range) = (u 0 * v 1 - u 1 * v 0).natAbs := by
  rw [Nat.card_congr (straightCircleInfEquiv (straightCircleHom_injective hu)
    (straightCircleHom_injective hv)).toEquiv, Matrix.natCard_ker_smulVecHom p _ hp,
    Matrix.det_transpose, Matrix.det_fin_two]
  simp

/-- A straight circle of the torus `Fin 2 → AddCircle p` meets another one in finitely many points
exactly when their directions are not parallel. -/
theorem finite_straightCircle_inf_iff {u v : Fin 2 → ℤ} (hu : IsCoprime (u 0) (u 1))
    (hv : IsCoprime (v 0) (v 1)) :
    Finite ↥((straightCircleHom (AddCircle p) u).range ⊓
        (straightCircleHom (AddCircle p) v).range) ↔ u 0 * v 1 - u 1 * v 0 ≠ 0 := by
  rw [(straightCircleInfEquiv (straightCircleHom_injective hu)
    (straightCircleHom_injective hv)).toEquiv.finite_iff, Matrix.finite_ker_smulVecHom_iff,
    Matrix.det_transpose, Matrix.det_fin_two]
  simp

/-- **Lattice displacements close up.** If `s u + t v = n` is an integer vector, the points of the
torus `ι → AddCircle p` reached from `0` by moving `p s` along the straight circle of direction `u`
and `p t` along the one of direction `v` add up to `[p n] = 0`. -/
theorem straightCircleHom_add_straightCircleHom_eq_zero {u v n : ι → ℤ} {s t : ℝ}
    (hn : ∀ i, s * u i + t * v i = n i) :
    straightCircleHom (AddCircle p) u ((s * p : ℝ) : AddCircle p) +
      straightCircleHom (AddCircle p) v ((t * p : ℝ) : AddCircle p) = 0 := by
  ext i
  have hi : (u i : ℝ) * (s * p) + v i * (t * p) = n i • p := by
    rw [zsmul_eq_mul, ← hn i]
    ring
  simp only [Pi.add_apply, straightCircleHom_apply, Pi.zero_apply, ← AddCircle.coe_zsmul,
    ← AddCircle.coe_add]
  rw [zsmul_eq_mul, zsmul_eq_mul, hi, AddCircle.coe_zsmul, AddCircle.coe_period, smul_zero]

/-- The lattice spanned by the columns `u` and `v` of an integer `2 × 2` matrix is the range of the
matrix. -/
private theorem range_mulVecLin_transpose_of (u v : Fin 2 → ℤ) :
    LinearMap.range (Matrix.of ![u, v])ᵀ.mulVecLin = Submodule.span ℤ {u, v} := by
  have hcol : (Matrix.of ![u, v])ᵀ.col = ![u, v] := by
    ext j i
    fin_cases j <;> rfl
  rw [Matrix.range_mulVecLin, hcol, Matrix.range_cons_cons_empty]

/-- **The intersection of two straight circles as a quotient lattice.** In the torus
`Fin 2 → AddCircle p`, `p ≠ 0`, the intersection of the straight circles of directions `u` and
`v` with coprime coordinates and `u₀ v₁ - u₁ v₀ ≠ 0` is isomorphic to `ℤ² / ⟨u, v⟩`. The class of
a point is the class of `s u + t v` for real `s` and `t` with `p (s u + t v) ∈ p ℤ²` such that
the point is the image of `p s u` (`TauCeti.straightCircleInfQuotientEquiv_apply`). -/
def straightCircleInfQuotientEquiv (hp : p ≠ 0) {u v : Fin 2 → ℤ} (hu : IsCoprime (u 0) (u 1))
    (hv : IsCoprime (v 0) (v 1)) (hdet : u 0 * v 1 - u 1 * v 0 ≠ 0) :
    ↥((straightCircleHom (AddCircle p) u).range ⊓ (straightCircleHom (AddCircle p) v).range) ≃+
      (Fin 2 → ℤ) ⧸ (Submodule.span ℤ {u, v}).toAddSubgroup :=
  (straightCircleInfEquiv (straightCircleHom_injective hu) (straightCircleHom_injective hv)).trans
    ((Matrix.quotientRangeEquivKerSmulVecHom p _
      (by rwa [Matrix.det_transpose, Matrix.det_fin_two]) hp).symm.trans
      (QuotientAddGroup.quotientAddEquivOfEq (by rw [range_mulVecLin_transpose_of])))

/-- **The class of an intersection point is its lattice displacement.** Let `z` be a point of the
straight circles of directions `u` and `v` in `Fin 2 → AddCircle p`, and let `s`, `t` be real and
`n` integral with `s u + t v = n`. If `z` is the image of `p s u`, its class in `ℤ² / ⟨u, v⟩` is
that of `n`. The image of `-p t v` is then `z` as well: the loop from `0` to `z` along the first
circle and back along the second one lifts to the path from `0` to `p s u` and on to
`p (s u + t v) = p n`. -/
theorem straightCircleInfQuotientEquiv_apply (hp : p ≠ 0) {u v : Fin 2 → ℤ}
    (hu : IsCoprime (u 0) (u 1)) (hv : IsCoprime (v 0) (v 1)) (hdet : u 0 * v 1 - u 1 * v 0 ≠ 0)
    (z : ↥((straightCircleHom (AddCircle p) u).range ⊓ (straightCircleHom (AddCircle p) v).range))
    {s t : ℝ} {n : Fin 2 → ℤ} (hn : ∀ i, s * u i + t * v i = n i)
    (hz : straightCircleHom (AddCircle p) u ((s * p : ℝ) : AddCircle p) = z) :
    straightCircleInfQuotientEquiv p hp hu hv hdet z = QuotientAddGroup.mk n := by
  have hdet' : (Matrix.of ![u, v])ᵀ.det ≠ 0 := by rwa [Matrix.det_transpose, Matrix.det_fin_two]
  -- The image of `-p t v` is `z` too, since `p (s u + t v) = p n` lies in `p ℤ²`.
  have hτ : straightCircleHom (AddCircle p) v (-((t * p : ℝ) : AddCircle p)) = z := by
    rw [map_neg, ← hz]
    exact (eq_neg_of_add_eq_zero_left (straightCircleHom_add_straightCircleHom_eq_zero p hn)).symm
  -- The kernel point `[(s p, t p)]` is the image of the class of `n`.
  have hQ : Matrix.quotientRangeEquivKerSmulVecHom p _ hdet' hp (QuotientAddGroup.mk n) =
      straightCircleInfEquiv (straightCircleHom_injective hu)
        (straightCircleHom_injective hv) z := by
    have := Matrix.invertibleOfIsUnitDet _ (Matrix.isUnit_det_map_intCast (K := ℝ) hdet')
    have hA : ((Matrix.of ![u, v])ᵀ.map ((↑) : ℤ → ℝ)) *ᵥ ![s * p, t * p] =
        p • (n · : Fin 2 → ℝ) := by
      ext k
      simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two, Matrix.map_apply,
        Matrix.transpose_apply, Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
        Pi.smul_apply, smul_eq_mul, ← hn k]
      ring
    refine Subtype.ext ?_
    rw [Matrix.coe_quotientRangeEquivKerSmulVecHom_mk, Matrix.inv_mulVec_eq_vec hA.symm,
      straightCircleInfEquiv_apply _ _ z hz hτ, neg_neg]
    ext i
    fin_cases i <;> rfl
  rw [straightCircleInfQuotientEquiv, AddEquiv.trans_apply, AddEquiv.trans_apply, ← hQ,
    AddEquiv.symm_apply_apply, QuotientAddGroup.quotientAddEquivOfEq_mk]

end AddCircle

end TauCeti
