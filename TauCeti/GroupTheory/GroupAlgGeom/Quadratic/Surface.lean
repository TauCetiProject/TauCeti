/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.GroupAlgGeom.Quadratic.Basic
public import TauCeti.GroupTheory.SurfaceGroup.Basic
import TauCeti.GroupTheory.SurfaceGroup.LowGenus

/-!
# Solutions of standard quadratic equations as homomorphisms of surface groups

The left side of a standard quadratic equation over a group `G` is a surface word. With the
commutator convention `[x, y] = x⁻¹ y⁻¹ x y`, the words `∏ᵢ [xᵢ, yᵢ]` and `∏ᵢ xᵢ²` of the
equations of types (1) and (3) are the relators of the closed surface groups `S⁺(n, 0)` and
`S⁻(n, 0)` at the variables, and the words `∏ᵢ [xᵢ, yᵢ] ∏ⱼ zⱼ⁻¹ cⱼ zⱼ d` and
`∏ᵢ xᵢ² ∏ⱼ zⱼ⁻¹ cⱼ zⱼ d` of the types (2) and (4) are the relators of `S⁺(n, m + 1)` and
`S⁻(n, m + 1)` in which the peripheral generators are replaced by the conjugates `zⱼ⁻¹ cⱼ zⱼ` of
the coefficients and by the constant `d`: the surface of the equation has one boundary component
for each coefficient.

Consequently a solution of a standard quadratic equation in a group `H` over `ι : G →* H` is a
homomorphism from the surface group of the equation to `H`. For the types (1) and (3) every
homomorphism `S⁺(n, 0) →* H`, respectively `S⁻(n, 0) →* H`, arises from a solution. For the types
(2) and (4) the homomorphisms arising from solutions are those sending the first `m` peripheral
elements to conjugates of the coefficients `ι (cⱼ)` and the last one to `ι d`.

## Main definitions

* `TauCeti.GroupAlgGeom.Quadratic.Standard.surfaceHomOrientable`,
  `TauCeti.GroupAlgGeom.Quadratic.Standard.surfaceHomNonorientable`: the homomorphism
  `S⁺(n, 0) →* H`, respectively `S⁻(n, 0) →* H`, of a solution of an equation of type (1),
  respectively (3).
* `TauCeti.GroupAlgGeom.Quadratic.Standard.surfaceHomOrientableCoeff`,
  `TauCeti.GroupAlgGeom.Quadratic.Standard.surfaceHomNonorientableCoeff`: the homomorphism
  `S⁺(n, m + 1) →* H`, respectively `S⁻(n, m + 1) →* H`, of a solution of an equation of type (2),
  respectively (4).
* `TauCeti.GroupAlgGeom.Quadratic.Standard.orientableCoeffPoint`,
  `TauCeti.GroupAlgGeom.Quadratic.Standard.nonorientableCoeffPoint`: conversely, the point of an
  equation of type (2), respectively (4), given by a homomorphism from the surface group and values
  of the variables `zⱼ`.

## Main results

* `TauCeti.GroupAlgGeom.Quadratic.Standard.toWord_orientable` and its three analogues: the left
  side of a standard quadratic equation is a surface word in `G[X]`.
* `TauCeti.GroupAlgGeom.Quadratic.Standard.eval_toWord_orientable` and its three analogues: the
  value of a standard quadratic equation at a point is a surface word.
* `TauCeti.GroupAlgGeom.Quadratic.Standard.exists_surfaceHomOrientable_eq` and its three
  analogues: the homomorphisms of surface groups that arise from solutions.
* `TauCeti.GroupAlgGeom.Quadratic.Standard.orientableCoeffPoint_mem_V`,
  `TauCeti.GroupAlgGeom.Quadratic.Standard.nonorientableCoeffPoint_mem_V`: the point of a
  homomorphism sending the peripheral elements to conjugates of the coefficients and to the
  constant is a solution.
* `TauCeti.GroupAlgGeom.Quadratic.Standard.mem_V_orientable_one_iff`: the solutions of the torus
  equation `[x, y] = 1` are the commuting pairs.

## References

* [IFT] O. Kharlampovich, A. Myasnikov, *Implicit function theorem over free groups*, J. Algebra
  290 (2005), §2.7, Definitions 3 and 4.
* [VAR-I] O. Kharlampovich, A. Myasnikov, *Irreducible affine varieties over a free group. I:
  Irreducibility of quadratic equations and Nullstellensatz*, J. Algebra 200 (1998), §1.
-/

public section

open Monoid.Coprod

namespace TauCeti.GroupAlgGeom.Quadratic.Standard

open SurfaceGroup

variable {G H X : Type*} [Group G] [Group H]
variable {n m : ℕ} {x y : Fin n → X} {z : Fin m → X} {c : Fin m → G} {d : G}

/-! ### Standard quadratic words are surface words -/

section Words

/-- The left side `∏ᵢ [xᵢ, yᵢ]` of a standard quadratic equation of type (1) is the relator of
the closed orientable surface group `S⁺(n, 0)` at the variables. -/
theorem toWord_orientable (hn : 0 < n) (inj : (Sum.elim x y).Injective) :
    (orientable (G := G) n hn x y inj).toWord =
      orientableWord (fun i => inr (FreeGroup.of (x i))) (fun i => inr (FreeGroup.of (y i)))
        Fin.elim0 := by
  simp [toWord_def, orientableWord_def, commutatorElement_def]

/-- The left side `∏ᵢ [xᵢ, yᵢ] ∏ⱼ zⱼ⁻¹ cⱼ zⱼ d` of a standard quadratic equation of type (2) is
the relator of the orientable surface group `S⁺(n, m + 1)` at the variables, the conjugates
`zⱼ⁻¹ cⱼ zⱼ` of the coefficients and the constant `d`. -/
theorem toWord_orientableCoeff (hnm : 0 < n + m) (inj : (Sum.elim (Sum.elim x y) z).Injective)
    (hc : ∀ j, c j ≠ 1) (hd : d ≠ 1) :
    (orientableCoeff n m hnm x y z inj c hc d hd).toWord =
      orientableWord (fun i => inr (FreeGroup.of (x i))) (fun i => inr (FreeGroup.of (y i)))
        (Fin.snoc (α := fun _ => GX G X)
          (fun j => (inr (FreeGroup.of (z j)))⁻¹ * inl (c j) * inr (FreeGroup.of (z j)))
          (inl d)) := by
  rw [toWord_def, orientableWord_def, List.ofFn_succ', List.prod_concat]
  simp [commutatorElement_def, mul_assoc]

/-- The left side `∏ᵢ xᵢ²` of a standard quadratic equation of type (3) is the relator of the
closed nonorientable surface group `S⁻(n, 0)` at the variables. -/
theorem toWord_nonorientable {x : Fin n → X} (hn : 0 < n) (inj : x.Injective) :
    (nonorientable (G := G) n hn x inj).toWord =
      nonorientableWord (fun i => inr (FreeGroup.of (x i))) Fin.elim0 := by
  simp [toWord_def, nonorientableWord_def]

/-- The left side `∏ᵢ xᵢ² ∏ⱼ zⱼ⁻¹ cⱼ zⱼ d` of a standard quadratic equation of type (4) is the
relator of the nonorientable surface group `S⁻(n, m + 1)` at the variables, the conjugates
`zⱼ⁻¹ cⱼ zⱼ` of the coefficients and the constant `d`. -/
theorem toWord_nonorientableCoeff {x : Fin n → X} (hn : 0 < n) (inj : (Sum.elim x z).Injective)
    (hc : ∀ j, c j ≠ 1) (hd : d ≠ 1) :
    (nonorientableCoeff n m hn x z inj c hc d hd).toWord =
      nonorientableWord (fun i => inr (FreeGroup.of (x i)))
        (Fin.snoc (α := fun _ => GX G X)
          (fun j => (inr (FreeGroup.of (z j)))⁻¹ * inl (c j) * inr (FreeGroup.of (z j)))
          (inl d)) := by
  rw [toWord_def, nonorientableWord_def, List.ofFn_succ', List.prod_concat]
  simp [mul_assoc]

variable (ι : G →* H) (v : X → H)

/-- The value of `∏ᵢ [xᵢ, yᵢ]` at a point `v` is the surface word of `S⁺(n, 0)` at the values of
the variables. -/
@[simp]
theorem eval_toWord_orientable (hn : 0 < n) (inj : (Sum.elim x y).Injective) :
    eval ι v (orientable n hn x y inj).toWord =
      orientableWord (fun i => v (x i)) (fun i => v (y i)) Fin.elim0 := by
  rw [toWord_orientable, map_orientableWord]
  simp [Subsingleton.elim (fun j : Fin 0 => eval ι v (Fin.elim0 j)) Fin.elim0]

/-- The value of `∏ᵢ [xᵢ, yᵢ] ∏ⱼ zⱼ⁻¹ cⱼ zⱼ d` at a point `v` is the surface word of
`S⁺(n, m + 1)` at the values of the variables, the conjugates of the coefficients and the
constant. -/
@[simp]
theorem eval_toWord_orientableCoeff (hnm : 0 < n + m)
    (inj : (Sum.elim (Sum.elim x y) z).Injective) (hc : ∀ j, c j ≠ 1) (hd : d ≠ 1) :
    eval ι v (orientableCoeff n m hnm x y z inj c hc d hd).toWord =
      orientableWord (fun i => v (x i)) (fun i => v (y i))
        (Fin.snoc (α := fun _ => H) (fun j => (v (z j))⁻¹ * ι (c j) * v (z j)) (ι d)) := by
  rw [toWord_orientableCoeff, map_orientableWord]
  simp only [eval_inr_of]
  congr 1
  ext j
  induction j using Fin.lastCases <;> simp

/-- The value of `∏ᵢ xᵢ²` at a point `v` is the surface word of `S⁻(n, 0)` at the values of the
variables. -/
@[simp]
theorem eval_toWord_nonorientable {x : Fin n → X} (hn : 0 < n) (inj : x.Injective) :
    eval ι v (nonorientable n hn x inj).toWord =
      nonorientableWord (fun i => v (x i)) Fin.elim0 := by
  rw [toWord_nonorientable, map_nonorientableWord]
  simp [Subsingleton.elim (fun j : Fin 0 => eval ι v (Fin.elim0 j)) Fin.elim0]

/-- The value of `∏ᵢ xᵢ² ∏ⱼ zⱼ⁻¹ cⱼ zⱼ d` at a point `v` is the surface word of `S⁻(n, m + 1)` at
the values of the variables, the conjugates of the coefficients and the constant. -/
@[simp]
theorem eval_toWord_nonorientableCoeff {x : Fin n → X} (hn : 0 < n)
    (inj : (Sum.elim x z).Injective) (hc : ∀ j, c j ≠ 1) (hd : d ≠ 1) :
    eval ι v (nonorientableCoeff n m hn x z inj c hc d hd).toWord =
      nonorientableWord (fun i => v (x i))
        (Fin.snoc (α := fun _ => H) (fun j => (v (z j))⁻¹ * ι (c j) * v (z j)) (ι d)) := by
  rw [toWord_nonorientableCoeff, map_nonorientableWord]
  simp only [eval_inr_of]
  congr 1
  ext j
  induction j using Fin.lastCases <;> simp

end Words

/-! ### The homomorphism of a solution -/

section SurfaceHom

variable {ι : G →* H} {v : X → H}

section Orientable

variable {hn : 0 < n} {inj : (Sum.elim x y).Injective}

/-- A solution `v` of the standard quadratic equation `∏ᵢ [xᵢ, yᵢ] = 1` of type (1) is a
homomorphism from the closed orientable surface group `S⁺(n, 0)`, sending `aᵢ` and `bᵢ` to the
values of `xᵢ` and `yᵢ`. -/
def surfaceHomOrientable (hv : v ∈ V ι {(orientable n hn x y inj).toWord}) :
    Orientable n 0 →* H :=
  Orientable.lift (fun i => v (x i)) (fun i => v (y i)) Fin.elim0 (by simpa using hv)

@[simp]
theorem surfaceHomOrientable_a (hv : v ∈ V ι {(orientable n hn x y inj).toWord}) (i : Fin n) :
    surfaceHomOrientable hv (Orientable.a n 0 i) = v (x i) :=
  Orientable.lift_a ..

@[simp]
theorem surfaceHomOrientable_b (hv : v ∈ V ι {(orientable n hn x y inj).toWord}) (i : Fin n) :
    surfaceHomOrientable hv (Orientable.b n 0 i) = v (y i) :=
  Orientable.lift_b ..

variable (ι hn inj) in
/-- Every homomorphism from the closed orientable surface group `S⁺(n, 0)` is the homomorphism of
a solution of the standard quadratic equation `∏ᵢ [xᵢ, yᵢ] = 1`. -/
theorem exists_surfaceHomOrientable_eq (f : Orientable n 0 →* H) :
    ∃ (v : X → H) (hv : v ∈ V ι {(orientable n hn x y inj).toWord}),
      surfaceHomOrientable hv = f := by
  set u : X → H := Function.extend (Sum.elim x y)
    (Sum.elim (fun i => f (Orientable.a n 0 i)) fun i => f (Orientable.b n 0 i)) 1
  have hx (i : Fin n) : u (x i) = f (Orientable.a n 0 i) := inj.extend_apply _ _ (Sum.inl i)
  have hy (i : Fin n) : u (y i) = f (Orientable.b n 0 i) := inj.extend_apply _ _ (Sum.inr i)
  refine ⟨u, ?_, ?_⟩
  · rw [mem_V, Set.forall_mem_singleton, eval_toWord_orientable, funext hx, funext hy,
      Subsingleton.elim Fin.elim0 fun j => f (Orientable.peripheral n 0 j),
      ← map_orientableWord, Orientable.orientableWord_a_b_peripheral, map_one]
  · ext i
    · simp [hx]
    · simp [hy]
    · exact i.elim0

/-- The solutions of the torus equation `[x, y] = 1` are the commuting pairs. -/
theorem mem_V_orientable_one_iff {x y : Fin 1 → X} {inj : (Sum.elim x y).Injective} :
    v ∈ V ι {(orientable 1 one_pos x y inj).toWord} ↔ Commute (v (x 0)) (v (y 0)) := by
  refine ⟨fun hv => ?_, fun h => ?_⟩
  · simpa using Orientable.commute_torus_a_b.map (surfaceHomOrientable hv)
  · rw [mem_V, Set.forall_mem_singleton, eval_toWord_orientable]
    simp [orientableWord_def, mul_assoc, h.eq]

end Orientable

section OrientableCoeff

variable {hnm : 0 < n + m} {inj : (Sum.elim (Sum.elim x y) z).Injective} {hc : ∀ j, c j ≠ 1}
  {hd : d ≠ 1}

/-- A solution `v` of the standard quadratic equation `∏ᵢ [xᵢ, yᵢ] ∏ⱼ zⱼ⁻¹ cⱼ zⱼ d = 1` of
type (2) is a homomorphism from the orientable surface group `S⁺(n, m + 1)`, sending `aᵢ` and `bᵢ`
to the values of `xᵢ` and `yᵢ`, the first `m` peripheral elements to the conjugates
`zⱼ⁻¹ cⱼ zⱼ` of the coefficients and the last peripheral element to the constant `d`. -/
def surfaceHomOrientableCoeff
    (hv : v ∈ V ι {(orientableCoeff n m hnm x y z inj c hc d hd).toWord}) :
    Orientable n (m + 1) →* H :=
  Orientable.lift (fun i => v (x i)) (fun i => v (y i))
    (Fin.snoc (α := fun _ => H) (fun j => (v (z j))⁻¹ * ι (c j) * v (z j)) (ι d))
    (by simpa using hv)

@[simp]
theorem surfaceHomOrientableCoeff_a
    (hv : v ∈ V ι {(orientableCoeff n m hnm x y z inj c hc d hd).toWord}) (i : Fin n) :
    surfaceHomOrientableCoeff hv (Orientable.a n (m + 1) i) = v (x i) :=
  Orientable.lift_a ..

@[simp]
theorem surfaceHomOrientableCoeff_b
    (hv : v ∈ V ι {(orientableCoeff n m hnm x y z inj c hc d hd).toWord}) (i : Fin n) :
    surfaceHomOrientableCoeff hv (Orientable.b n (m + 1) i) = v (y i) :=
  Orientable.lift_b ..

@[simp]
theorem surfaceHomOrientableCoeff_peripheral_castSucc
    (hv : v ∈ V ι {(orientableCoeff n m hnm x y z inj c hc d hd).toWord}) (j : Fin m) :
    surfaceHomOrientableCoeff hv (Orientable.peripheral n (m + 1) j.castSucc) =
      (v (z j))⁻¹ * ι (c j) * v (z j) := by
  simp [surfaceHomOrientableCoeff]

@[simp]
theorem surfaceHomOrientableCoeff_peripheral_last
    (hv : v ∈ V ι {(orientableCoeff n m hnm x y z inj c hc d hd).toWord}) :
    surfaceHomOrientableCoeff hv (Orientable.peripheral n (m + 1) (Fin.last m)) = ι d := by
  simp [surfaceHomOrientableCoeff]

variable (x y z) in
/-- The point of a homomorphism `f` from the orientable surface group `S⁺(n, m + 1)` and of values
`t` of the variables `zⱼ`: the variables `xᵢ`, `yᵢ`, `zⱼ` take the values `f aᵢ`, `f bᵢ`, `tⱼ`, and
every other variable the value `1`. -/
noncomputable def orientableCoeffPoint (f : Orientable n (m + 1) →* H) (t : Fin m → H) : X → H :=
  Function.extend (Sum.elim (Sum.elim x y) z) (Sum.elim (Sum.elim
    (fun i => f (Orientable.a n (m + 1) i)) fun i => f (Orientable.b n (m + 1) i)) t) 1

@[simp]
theorem orientableCoeffPoint_x (inj : (Sum.elim (Sum.elim x y) z).Injective)
    (f : Orientable n (m + 1) →* H) (t : Fin m → H) (i : Fin n) :
    orientableCoeffPoint x y z f t (x i) = f (Orientable.a n (m + 1) i) :=
  inj.extend_apply _ _ (Sum.inl (Sum.inl i))

@[simp]
theorem orientableCoeffPoint_y (inj : (Sum.elim (Sum.elim x y) z).Injective)
    (f : Orientable n (m + 1) →* H) (t : Fin m → H) (i : Fin n) :
    orientableCoeffPoint x y z f t (y i) = f (Orientable.b n (m + 1) i) :=
  inj.extend_apply _ _ (Sum.inl (Sum.inr i))

@[simp]
theorem orientableCoeffPoint_z (inj : (Sum.elim (Sum.elim x y) z).Injective)
    (f : Orientable n (m + 1) →* H) (t : Fin m → H) (j : Fin m) :
    orientableCoeffPoint x y z f t (z j) = t j :=
  inj.extend_apply _ _ (Sum.inr j)

variable (hnm inj hc hd) in
/-- The point of a homomorphism `f` from the orientable surface group `S⁺(n, m + 1)` sending the
first `m` peripheral elements to the conjugates `tⱼ⁻¹ cⱼ tⱼ` of the coefficients and the last one to
the constant `d` is a solution of the standard quadratic equation
`∏ᵢ [xᵢ, yᵢ] ∏ⱼ zⱼ⁻¹ cⱼ zⱼ d = 1`. -/
theorem orientableCoeffPoint_mem_V (f : Orientable n (m + 1) →* H) (t : Fin m → H)
    (ht : ∀ j, f (Orientable.peripheral n (m + 1) j.castSucc) = (t j)⁻¹ * ι (c j) * t j)
    (hf : f (Orientable.peripheral n (m + 1) (Fin.last m)) = ι d) :
    orientableCoeffPoint x y z f t ∈
      V ι {(orientableCoeff n m hnm x y z inj c hc d hd).toWord} := by
  have hp : Fin.snoc (α := fun _ => H) (fun j => (orientableCoeffPoint x y z f t (z j))⁻¹ *
      ι (c j) * orientableCoeffPoint x y z f t (z j)) (ι d) =
      fun j => f (Orientable.peripheral n (m + 1) j) := by
    ext j
    induction j using Fin.lastCases with
    | last => simp [hf]
    | cast j => simp [orientableCoeffPoint_z inj, ht]
  rw [mem_V, Set.forall_mem_singleton, eval_toWord_orientableCoeff,
    funext (orientableCoeffPoint_x inj f t), funext (orientableCoeffPoint_y inj f t), hp,
    ← map_orientableWord, Orientable.orientableWord_a_b_peripheral, map_one]

variable (hnm inj hc hd) in
/-- A homomorphism from the orientable surface group `S⁺(n, m + 1)` is the homomorphism of a
solution of the standard quadratic equation `∏ᵢ [xᵢ, yᵢ] ∏ⱼ zⱼ⁻¹ cⱼ zⱼ d = 1` as soon as it sends
the first `m` peripheral elements to conjugates of the coefficients `cⱼ` and the last one to the
constant `d`. -/
theorem exists_surfaceHomOrientableCoeff_eq (f : Orientable n (m + 1) →* H) (t : Fin m → H)
    (ht : ∀ j, f (Orientable.peripheral n (m + 1) j.castSucc) = (t j)⁻¹ * ι (c j) * t j)
    (hf : f (Orientable.peripheral n (m + 1) (Fin.last m)) = ι d) :
    ∃ (v : X → H) (hv : v ∈ V ι {(orientableCoeff n m hnm x y z inj c hc d hd).toWord}),
      surfaceHomOrientableCoeff hv = f := by
  refine ⟨_, orientableCoeffPoint_mem_V hnm inj hc hd f t ht hf, ?_⟩
  ext j
  · simp [orientableCoeffPoint_x inj]
  · simp [orientableCoeffPoint_y inj]
  · induction j using Fin.lastCases <;> simp [orientableCoeffPoint_z inj, ht, hf]

end OrientableCoeff

section Nonorientable

variable {x : Fin n → X} {hn : 0 < n} {inj : x.Injective}

/-- A solution `v` of the standard quadratic equation `∏ᵢ xᵢ² = 1` of type (3) is a homomorphism
from the closed nonorientable surface group `S⁻(n, 0)`, sending `cᵢ` to the value of `xᵢ`. -/
def surfaceHomNonorientable (hv : v ∈ V ι {(nonorientable n hn x inj).toWord}) :
    Nonorientable n 0 →* H :=
  Nonorientable.lift (fun i => v (x i)) Fin.elim0 (by simpa using hv)

@[simp]
theorem surfaceHomNonorientable_c (hv : v ∈ V ι {(nonorientable n hn x inj).toWord})
    (i : Fin n) : surfaceHomNonorientable hv (Nonorientable.c n 0 i) = v (x i) :=
  Nonorientable.lift_c ..

variable (ι hn inj) in
/-- Every homomorphism from the closed nonorientable surface group `S⁻(n, 0)` is the homomorphism
of a solution of the standard quadratic equation `∏ᵢ xᵢ² = 1`. -/
theorem exists_surfaceHomNonorientable_eq (f : Nonorientable n 0 →* H) :
    ∃ (v : X → H) (hv : v ∈ V ι {(nonorientable n hn x inj).toWord}),
      surfaceHomNonorientable hv = f := by
  set u : X → H := Function.extend x (fun i => f (Nonorientable.c n 0 i)) 1
  have hx (i : Fin n) : u (x i) = f (Nonorientable.c n 0 i) := inj.extend_apply _ _ i
  refine ⟨u, ?_, ?_⟩
  · rw [mem_V, Set.forall_mem_singleton, eval_toWord_nonorientable, funext hx,
      Subsingleton.elim Fin.elim0 fun j => f (Nonorientable.peripheral n 0 j),
      ← map_nonorientableWord, Nonorientable.nonorientableWord_c_peripheral, map_one]
  · ext i
    · simp [hx]
    · exact i.elim0

end Nonorientable

section NonorientableCoeff

variable {x : Fin n → X} {hn : 0 < n} {inj : (Sum.elim x z).Injective} {hc : ∀ j, c j ≠ 1}
  {hd : d ≠ 1}

/-- A solution `v` of the standard quadratic equation `∏ᵢ xᵢ² ∏ⱼ zⱼ⁻¹ cⱼ zⱼ d = 1` of type (4) is
a homomorphism from the nonorientable surface group `S⁻(n, m + 1)`, sending `cᵢ` to the value of
`xᵢ`, the first `m` peripheral elements to the conjugates `zⱼ⁻¹ cⱼ zⱼ` of the coefficients and the
last peripheral element to the constant `d`. -/
def surfaceHomNonorientableCoeff
    (hv : v ∈ V ι {(nonorientableCoeff n m hn x z inj c hc d hd).toWord}) :
    Nonorientable n (m + 1) →* H :=
  Nonorientable.lift (fun i => v (x i))
    (Fin.snoc (α := fun _ => H) (fun j => (v (z j))⁻¹ * ι (c j) * v (z j)) (ι d))
    (by simpa using hv)

@[simp]
theorem surfaceHomNonorientableCoeff_c
    (hv : v ∈ V ι {(nonorientableCoeff n m hn x z inj c hc d hd).toWord}) (i : Fin n) :
    surfaceHomNonorientableCoeff hv (Nonorientable.c n (m + 1) i) = v (x i) :=
  Nonorientable.lift_c ..

@[simp]
theorem surfaceHomNonorientableCoeff_peripheral_castSucc
    (hv : v ∈ V ι {(nonorientableCoeff n m hn x z inj c hc d hd).toWord}) (j : Fin m) :
    surfaceHomNonorientableCoeff hv (Nonorientable.peripheral n (m + 1) j.castSucc) =
      (v (z j))⁻¹ * ι (c j) * v (z j) := by
  simp [surfaceHomNonorientableCoeff]

@[simp]
theorem surfaceHomNonorientableCoeff_peripheral_last
    (hv : v ∈ V ι {(nonorientableCoeff n m hn x z inj c hc d hd).toWord}) :
    surfaceHomNonorientableCoeff hv (Nonorientable.peripheral n (m + 1) (Fin.last m)) = ι d := by
  simp [surfaceHomNonorientableCoeff]

/-- The point of a homomorphism `f` from the nonorientable surface group `S⁻(n, m + 1)` and of
values `t` of the variables `zⱼ`: the variables `xᵢ`, `zⱼ` take the values `f cᵢ`, `tⱼ`, and every
other variable the value `1`. -/
noncomputable def nonorientableCoeffPoint (x : Fin n → X) (z : Fin m → X)
    (f : Nonorientable n (m + 1) →* H) (t : Fin m → H) : X → H :=
  Function.extend (Sum.elim x z) (Sum.elim (fun i => f (Nonorientable.c n (m + 1) i)) t) 1

@[simp]
theorem nonorientableCoeffPoint_x (inj : (Sum.elim x z).Injective)
    (f : Nonorientable n (m + 1) →* H) (t : Fin m → H) (i : Fin n) :
    nonorientableCoeffPoint x z f t (x i) = f (Nonorientable.c n (m + 1) i) :=
  inj.extend_apply _ _ (Sum.inl i)

@[simp]
theorem nonorientableCoeffPoint_z (inj : (Sum.elim x z).Injective)
    (f : Nonorientable n (m + 1) →* H) (t : Fin m → H) (j : Fin m) :
    nonorientableCoeffPoint x z f t (z j) = t j :=
  inj.extend_apply _ _ (Sum.inr j)

variable (hn inj hc hd) in
/-- The point of a homomorphism `f` from the nonorientable surface group `S⁻(n, m + 1)` sending
the first `m` peripheral elements to the conjugates `tⱼ⁻¹ cⱼ tⱼ` of the coefficients and the last
one to the constant `d` is a solution of the standard quadratic equation
`∏ᵢ xᵢ² ∏ⱼ zⱼ⁻¹ cⱼ zⱼ d = 1`. -/
theorem nonorientableCoeffPoint_mem_V (f : Nonorientable n (m + 1) →* H) (t : Fin m → H)
    (ht : ∀ j, f (Nonorientable.peripheral n (m + 1) j.castSucc) = (t j)⁻¹ * ι (c j) * t j)
    (hf : f (Nonorientable.peripheral n (m + 1) (Fin.last m)) = ι d) :
    nonorientableCoeffPoint x z f t ∈
      V ι {(nonorientableCoeff n m hn x z inj c hc d hd).toWord} := by
  have hp : Fin.snoc (α := fun _ => H) (fun j => (nonorientableCoeffPoint x z f t (z j))⁻¹ *
      ι (c j) * nonorientableCoeffPoint x z f t (z j)) (ι d) =
      fun j => f (Nonorientable.peripheral n (m + 1) j) := by
    ext j
    induction j using Fin.lastCases with
    | last => simp [hf]
    | cast j => simp [nonorientableCoeffPoint_z inj, ht]
  rw [mem_V, Set.forall_mem_singleton, eval_toWord_nonorientableCoeff,
    funext (nonorientableCoeffPoint_x inj f t), hp, ← map_nonorientableWord,
    Nonorientable.nonorientableWord_c_peripheral, map_one]

variable (hn inj hc hd) in
/-- A homomorphism from the nonorientable surface group `S⁻(n, m + 1)` is the homomorphism of a
solution of the standard quadratic equation `∏ᵢ xᵢ² ∏ⱼ zⱼ⁻¹ cⱼ zⱼ d = 1` as soon as it sends the
first `m` peripheral elements to conjugates of the coefficients `cⱼ` and the last one to the
constant `d`. -/
theorem exists_surfaceHomNonorientableCoeff_eq (f : Nonorientable n (m + 1) →* H) (t : Fin m → H)
    (ht : ∀ j, f (Nonorientable.peripheral n (m + 1) j.castSucc) = (t j)⁻¹ * ι (c j) * t j)
    (hf : f (Nonorientable.peripheral n (m + 1) (Fin.last m)) = ι d) :
    ∃ (v : X → H) (hv : v ∈ V ι {(nonorientableCoeff n m hn x z inj c hc d hd).toWord}),
      surfaceHomNonorientableCoeff hv = f := by
  refine ⟨_, nonorientableCoeffPoint_mem_V hn inj hc hd f t ht hf, ?_⟩
  ext j
  · simp [nonorientableCoeffPoint_x inj]
  · induction j using Fin.lastCases <;> simp [nonorientableCoeffPoint_z inj, ht, hf]

end NonorientableCoeff

end SurfaceHom

end TauCeti.GroupAlgGeom.Quadratic.Standard
