/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.UnitaryGroup
public import Mathlib.Analysis.Complex.Polynomial.Basic
public import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import TauCeti.RepresentationTheory.Irreducible
import TauCeti.RepresentationTheory.ScalarCommutator

/-!
# The twisted `SU(r)` relation set

For a rank `r`, a complex number `ζ` and a genus `g`, the *twisted relation set*
`TauCeti.relationSet r ζ g` consists of the tuples `(A₁, B₁, …, A_g, B_g)` in `SU(r)` whose
ordered product of group commutators is the scalar matrix `ζ • 1`:

    [A₁,B₁]⋯[A_g,B_g] = ζ • 1.

With `ζ = exp(2πi d/r)` this is the holonomy description of the projectively flat
connections of rank `r` and degree `d` on a closed surface of genus `g` whose determinant is a
fixed connection; its quotient by simultaneous conjugation is the representation model of the
fixed-determinant moduli space (Wehrheim–Woodward, *Floer field theory for coprime rank and
degree*, Theorem 3.3.3 and Remark 3.3.7).

When `ζ` is a primitive `r`-th root of unity (equivalently `gcd(r, d) = 1`), the stabilizer of
every solution under simultaneous conjugation is the center of `SU(r)`
(`TauCeti.relationSet_stabilizer_central`). The proof is the holonomy form of the exclusion of
parallel subbundles in Wehrheim–Woodward's proof of Theorem 3.3.3: an element commuting with all
`A_j, B_j` has an eigenspace preserved by all of them, the restricted commutator product has
determinant `1 = ζ ^ dim`, so the eigenspace is everything. Here this is packaged as the
irreducibility of the representation of the centralizer on `ℂ^r`
(`Representation.isIrreducible_of_mem_commutator`) followed by Schur's lemma.

So the effective action of `PSU(r)` on the relation set is free. Without the primitivity hypothesis
this fails: for `r = 2`, `ζ = 1` the pair `(1, 1)` is a solution stabilized by all of `SU(2)`.

## Main definitions

* `TauCeti.relationSet`: the tuples in `SU(r)` whose ordered product of commutators is `ζ • 1`.

## Main results

* `TauCeti.relationSet_zero_eq_empty`: in genus zero the relation set is empty unless `ζ = 1`
  (for `r ≥ 1`).
* `TauCeti.relationSet_two_neg_one_one_nonempty`: the torus relation `[A, B] = -1` has a solution
  in `SU(2)`.
* `TauCeti.relationSet_stabilizer_central`: for a primitive `r`-th root of unity `ζ`, every element
  of `SU(r)` commuting with all entries of a solution is central.
-/

public section

open scoped commutatorElement

namespace TauCeti

/-- **The twisted relation set.** The tuples `(A₁, B₁, …, A_g, B_g)` in `SU(r)`, recorded as a
family of pairs indexed by `Fin g`, whose ordered product of group commutators
`[A₁,B₁]⋯[A_g,B_g]` is the scalar matrix `ζ • 1`. With `ζ = exp(2πi d/r)` this is the holonomy
relation of the projectively flat rank-`r`, degree-`d` connections on a closed surface of genus `g`
(Wehrheim–Woodward, *Floer field theory for coprime rank and degree*, Remark 3.3.7). -/
def relationSet (r : ℕ) (ζ : ℂ) (g : ℕ) :
    Set (Fin g → Matrix.specialUnitaryGroup (Fin r) ℂ × Matrix.specialUnitaryGroup (Fin r) ℂ) :=
  {x | ((List.ofFn fun j ↦ ⁅(x j).1, (x j).2⁆).prod : Matrix (Fin r) (Fin r) ℂ) = ζ • 1}

/-- Membership in the twisted relation set: the ordered product of commutators is `ζ • 1`. -/
@[simp]
theorem mem_relationSet {r : ℕ} {ζ : ℂ} {g : ℕ}
    {x : Fin g → Matrix.specialUnitaryGroup (Fin r) ℂ × Matrix.specialUnitaryGroup (Fin r) ℂ} :
    x ∈ relationSet r ζ g ↔
      ((List.ofFn fun j ↦ ⁅(x j).1, (x j).2⁆).prod : Matrix (Fin r) (Fin r) ℂ) = ζ • 1 :=
  Iff.rfl

/-- **The sphere relation set.** In genus zero the product of commutators is empty, so for
`r ≥ 1` the relation `1 = ζ • 1` has no solution unless `ζ = 1`; in particular, for a primitive
`r`-th root of unity with `r ≥ 2` the sphere moduli space is empty. -/
theorem relationSet_zero_eq_empty {r : ℕ} (hr : r ≠ 0) {ζ : ℂ} (hζ : ζ ≠ 1) :
    relationSet r ζ 0 = ∅ := by
  refine Set.eq_empty_of_forall_notMem fun x hx ↦ hζ ?_
  have h := congrFun (congrFun (mem_relationSet.1 hx) ⟨0, Nat.pos_of_ne_zero hr⟩)
    ⟨0, Nat.pos_of_ne_zero hr⟩
  simpa using h.symm

/-- **The rank-two torus relation has a solution.** The matrices `A = diag(i, -i)` and
`B = !![0, 1; -1, 0]` lie in `SU(2)` and satisfy `A B A⁻¹ B⁻¹ = -1`, so the relation set for
`r = 2`, `ζ = -1`, `g = 1` is nonempty. -/
theorem relationSet_two_neg_one_one_nonempty : (relationSet 2 (-1) 1).Nonempty := by
  obtain ⟨hA, hB⟩ : !![Complex.I, 0; 0, -Complex.I] ∈ Matrix.specialUnitaryGroup (Fin 2) ℂ ∧
      !![(0 : ℂ), 1; -1, 0] ∈ Matrix.specialUnitaryGroup (Fin 2) ℂ := by
    constructor <;> refine ⟨Matrix.mem_unitaryGroup_iff.2 ?_, by simp [Matrix.det_fin_two]⟩ <;>
      ext i j <;> fin_cases i <;> fin_cases j <;>
      simp [Matrix.star_eq_conjTranspose, Matrix.mul_apply, Fin.sum_univ_two]
  refine ⟨fun _ ↦ (⟨_, hA⟩, ⟨_, hB⟩), mem_relationSet.2 ?_⟩
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [commutatorElement_def, ← Matrix.star_eq_inv, Matrix.star_eq_conjTranspose,
      Matrix.mul_apply, Fin.sum_univ_two, Matrix.vecMul, dotProduct, Matrix.conjTranspose_apply]

/-- **Stabilizers of the coprime twisted relation are central.** Let `ζ` be a primitive `r`-th root
of unity and `x` a solution of `[A₁,B₁]⋯[A_g,B_g] = ζ • 1` in `SU(r)`. Every `u ∈ SU(r)` commuting
with all `A_j` and `B_j` lies in the center of `SU(r)`. Equivalently, the effective `PSU(r)` action
on the relation set by simultaneous conjugation is free (Wehrheim–Woodward, *Floer field theory
for coprime rank and degree*, proof of Theorem 3.3.3). -/
theorem relationSet_stabilizer_central {r : ℕ} {ζ : ℂ} (hζ : IsPrimitiveRoot ζ r) {g : ℕ}
    {x : Fin g → Matrix.specialUnitaryGroup (Fin r) ℂ × Matrix.specialUnitaryGroup (Fin r) ℂ}
    (hx : x ∈ relationSet r ζ g) {u : Matrix.specialUnitaryGroup (Fin r) ℂ}
    (hu : ∀ j, Commute u (x j).1 ∧ Commute u (x j).2) :
    u ∈ Subgroup.center (Matrix.specialUnitaryGroup (Fin r) ℂ) := by
  rcases Nat.eq_zero_or_pos r with rfl | hr
  · exact Subgroup.mem_center_iff.2 fun _ ↦ Subtype.ext <| Matrix.ext fun i ↦ i.elim0
  have : NeZero r := ⟨hr.ne'⟩
  -- The centralizer `H` of `u` contains every entry of `x`, and acts on `ℂ^r`.
  let H := Subgroup.centralizer ({u} : Set (Matrix.specialUnitaryGroup (Fin r) ℂ))
  have hmem (j : Fin g) : (x j).1 ∈ H ∧ (x j).2 ∈ H :=
    ⟨Subgroup.mem_centralizer_singleton_iff.2 (hu j).1.symm,
      Subgroup.mem_centralizer_singleton_iff.2 (hu j).2.symm⟩
  let ρ : Representation ℂ H (Fin r → ℂ) :=
    MonoidHom.comp (Matrix.toLinAlgEquiv' : Matrix (Fin r) (Fin r) ℂ ≃ₐ[ℂ] _).toMonoidHom
      ((Matrix.specialUnitaryGroup (Fin r) ℂ).subtype.comp H.subtype)
  -- The product of commutators, read in `H`, lies in the commutator subgroup and acts by `ζ`.
  let z : H := (List.ofFn fun j ↦ ⁅(⟨(x j).1, (hmem j).1⟩ : H), ⟨(x j).2, (hmem j).2⟩⁆).prod
  have hz : z ∈ commutator H := by
    refine Subgroup.list_prod_mem _ fun y hy ↦ ?_
    obtain ⟨j, rfl⟩ := List.mem_ofFn.1 hy
    exact Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)
  have hzζ : ρ z = ζ • 1 := by
    have hzx : (((z : Matrix.specialUnitaryGroup (Fin r) ℂ)) : Matrix (Fin r) (Fin r) ℂ) =
        ((List.ofFn fun j ↦ ⁅(x j).1, (x j).2⁆).prod : Matrix (Fin r) (Fin r) ℂ) := by
      simp [z, ← H.subtype_apply, List.map_ofFn, Function.comp_def,
        map_commutatorElement]
    simp [ρ, hzx, mem_relationSet.1 hx]
  have hirr : ρ.IsIrreducible :=
    Representation.isIrreducible_of_mem_commutator hz (by simpa using hζ) hzζ
  -- By Schur's lemma, `u`, which commutes with the action of `H`, is a scalar matrix.
  obtain ⟨c, hc⟩ := Representation.IsIrreducible.exists_forall_apply_eq_smul (ρ := ρ)
    (Matrix.toLin' (u : Matrix (Fin r) (Fin r) ℂ)) fun h v ↦ by
      have hh : (u : Matrix (Fin r) (Fin r) ℂ) * (h : Matrix.specialUnitaryGroup (Fin r) ℂ) =
          (h : Matrix.specialUnitaryGroup (Fin r) ℂ) * u :=
        congrArg Subtype.val (Subgroup.mem_centralizer_singleton_iff.1 h.2).symm
      simp [ρ, Matrix.mulVec_mulVec, hh]
  have hu' : (u : Matrix (Fin r) (Fin r) ℂ) = c • 1 :=
    Matrix.toLin'.injective <| LinearMap.ext fun v ↦ by simpa using hc v
  exact Subgroup.mem_center_iff.2 fun w ↦ Subtype.ext <| by simp [hu']

end TauCeti
