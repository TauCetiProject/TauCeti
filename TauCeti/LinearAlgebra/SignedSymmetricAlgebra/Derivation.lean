/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.DG.Algebra.Defs
public import TauCeti.LinearAlgebra.SignedSymmetricAlgebra.Supercommutativity
import Mathlib.Data.Matrix.Basic
import Mathlib.GroupTheory.GroupAction.Ring
import TauCeti.Algebra.Module.GradedModule.KoszulTwist.Algebra

/-!
# Odd derivations of the signed symmetric algebra

A linear map `δ : V → A(V)` into the signed symmetric algebra `A(V) = TauCeti.SignedSym G`
which raises degree by one extends uniquely to a linear endomorphism `d` of `A(V)` satisfying
the signed Leibniz rule

`d (a * b) = d a * b + (-1) ^ p • (a * d b)` for `a` of degree `p`.

This extension `TauCeti.SignedSym.liftDerivation` again raises degree by one. Its square is an
unsigned derivation, so it vanishes as soon as it vanishes on generators. Consequently `d` is the
differential of a differential graded algebra structure on `A(V)` exactly when `d (δ x) = 0`
for every `x : V`. This reduces the identity `d ∘ d = 0` for the differential of a free
supercommutative algebra, such as the contact homology differential, to a check on generators.

The extension is constructed through the universal property of `A(V)`: the matrices
`[[a, 0], [d a, σ a]]`, where `σ` is the grade involution `a ↦ (-1) ^ |a| • a`, multiply as
`a + ε d a` in the dual numbers over `A(V)` with one odd generator `ε`. The signed Leibniz rule
for `d` is multiplicativity of `a ↦ [[a, 0], [d a, σ a]]`.

## Main definitions

* `TauCeti.SignedSym.liftDerivation`: the odd derivation extending a degree-one assignment on
  generators.

## Main results

* `TauCeti.SignedSym.liftDerivation_mul`: the signed Leibniz rule.
* `TauCeti.SignedSym.isHomogeneous_liftDerivation`: the extension raises degree by one.
* `TauCeti.SignedSym.eq_liftDerivation` and `TauCeti.SignedSym.existsUnique_odd_extension`:
  an odd derivation is determined by its values on generators.
* `TauCeti.SignedSym.comp_self_eq_zero_iff`: a degree-one signed Leibniz map squares to zero if
  and only if its square vanishes on generators.
* `TauCeti.SignedSym.isDGAlgebra_liftDerivation_iff`: the extension is a differential graded
  algebra differential if and only if it kills the image of the assignment.

## References

* J. Pardon, *Contact homology and virtual fundamental cycles*, equation (1.1), for the free
  supercommutative algebra on which the contact homology differential is defined.
-/

public section

namespace TauCeti.SignedSym

universe u v

variable {R : Type u} [CommRing R]
variable {V : Type v} [AddCommGroup V] [Module R V]
variable {G : InternalGrading R V}

/-- A linear endomorphism of `A(V)` satisfying a Leibniz rule with an arbitrary sign `s p` for a
left factor of degree `p`, and vanishing on generators, is zero. This covers both the difference
of two odd derivations and the square of an odd derivation. -/
private theorem eq_zero_of_leibniz (s : ℤ → ℤˣ) {D : SignedSym G →ₗ[R] SignedSym G}
    (hD : ∀ {p : ℤ} {a : SignedSym G}, a ∈ signedSymPiece G p → ∀ b : SignedSym G,
      D (a * b) = D a * b + s p • (a * D b))
    (hgen : ∀ x, D (generator G x) = 0) : D = 0 := by
  have hone : D 1 = 0 := by
    have h := hD (SetLike.GradedOne.one_mem (A := signedSymPiece G)) 1
    simp only [mul_one, one_mul, left_eq_add] at h
    exact (smul_eq_zero_iff_eq (s 0)).1 h
  have hhom : ∀ {p : ℤ} {a : SignedSym G}, a ∈ signedSymPiece G p → D a = 0 := by
    intro p a ha
    refine (homogeneous_induction G (P := fun p a => a ∈ signedSymPiece G p ∧ D a = 0)
      ⟨SetLike.GradedOne.one_mem, hone⟩
      (fun p x hx => ⟨generator_mem_signedSymPiece G hx, hgen x⟩)
      (fun p q a b ha hb => ⟨SetLike.mul_mem_graded ha.1 hb.1, by
        rw [hD ha.1, ha.2, hb.2, zero_mul, mul_zero, zero_add]
        exact smul_zero _⟩)
      (fun p => ⟨zero_mem _, map_zero D⟩)
      (fun p a b ha hb => ⟨add_mem ha.1 hb.1, by rw [map_add, ha.2, hb.2, add_zero]⟩)
      (fun p r a ha => ⟨Submodule.smul_mem _ r ha.1, by rw [map_smul, ha.2, smul_zero]⟩)
      ha).2
  ext a
  induction a using DirectSum.Decomposition.inductionOn (signedSymPiece G) with
  | zero => simp
  | homogeneous a => exact hhom a.2
  | add a b ha hb => simp_all

section Lift

variable (δ : V →ₗ[R] SignedSym G)

/-- The grade involution `a ↦ (-1) ^ |a| • a` of `A(V)`. -/
private noncomputable def twist : SignedSym G ≃ₐ[R] SignedSym G :=
  InternalGrading.koszulTwistAlgEquiv (signedSymPiece G) 1

private theorem twist_of_mem {p : ℤ} {a : SignedSym G} (ha : a ∈ signedSymPiece G p) :
    twist (G := G) a = p.negOnePow • a := by
  simpa [twist] using InternalGrading.koszulTwistAlgEquiv_apply_of_mem (signedSymPiece G) 1 ha

/-- The Koszul sign identity behind the lower left entry of a product of triangular matrices:
for `a`, `b` of degrees `p`, `q` and `a'`, `b'` of degrees `p + 1`, `q + 1`,
`a' * b + σ a * b' = (-1) ^ (p * q) • (b' * a + σ b * a')`. -/
private theorem mul_add_twist_mul_comm {p q : ℤ} {a b a' b' : SignedSym G}
    (ha : a ∈ signedSymPiece G p) (hb : b ∈ signedSymPiece G q)
    (ha' : a' ∈ signedSymPiece G (p + 1)) (hb' : b' ∈ signedSymPiece G (q + 1)) :
    a' * b + twist a * b' = ((p * q).negOnePow : ℤ) • (b' * a + twist b * a') := by
  have h₁ : ((p + 1) * q).negOnePow = (p * q).negOnePow * q.negOnePow := by
    rw [← Int.negOnePow_add]; congr 1; ring
  have h₂ : p.negOnePow * (p * (q + 1)).negOnePow = (p * q).negOnePow := by
    rw [← Int.negOnePow_add, Int.negOnePow_eq_iff]; exact ⟨p, by ring⟩
  rw [twist_of_mem ha, twist_of_mem hb, smul_mul_assoc, smul_mul_assoc,
    mul_eq_negOnePow_smul_mul G ha' hb, mul_eq_negOnePow_smul_mul G ha hb', h₁, ← h₂]
  simp only [Units.smul_def, Units.val_mul, mul_smul]
  module

/-- The lower triangular matrix `[[x, 0], [δ x, σ x]]` attached to a generator `x`. -/
private noncomputable def triangular : V →ₗ[R] Matrix (Fin 2) (Fin 2) (SignedSym G) where
  toFun x := !![generator G x, 0; δ x, twist (generator G x)]
  map_add' x y := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  map_smul' r x := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp

variable {δ}
variable (hδ : LinearMap.IsHomogeneous δ G.piece (signedSymPiece G) 1)

include hδ in
/-- The triangular matrices of homogeneous generators obey the Koszul relation. -/
private theorem triangular_mul_triangular {p q : ℤ} {x y : V}
    (hx : x ∈ G.piece p) (hy : y ∈ G.piece q) :
    triangular δ x * triangular δ y =
      ((p * q).negOnePow : ℤ) • (triangular δ y * triangular δ x) := by
  have hgx := generator_mem_signedSymPiece G hx
  have hgy := generator_mem_signedSymPiece G hy
  have hdx := hδ.map_mem hx
  have hdy := hδ.map_mem hy
  ext i j
  fin_cases i <;> fin_cases j
  · simpa [triangular, Matrix.mul_apply] using mul_eq_negOnePow_smul_mul G hgx hgy
  · simp [triangular, Matrix.mul_apply]
  · simpa [triangular, Matrix.mul_apply, Fin.sum_univ_two] using
      mul_add_twist_mul_comm hgx hgy hdx hdy
  · have key : twist (generator G x) * twist (generator G y) =
        ((p * q).negOnePow : ℤ) • (twist (generator G y) * twist (generator G x)) := by
      rw [← map_mul (twist (G := G)), ← map_mul (twist (G := G)),
        generator_mul_generator G hx hy, map_zsmul]
    simpa [triangular, Matrix.mul_apply, Fin.sum_univ_two] using key

/-- The algebra map `a ↦ [[a, 0], [d a, σ a]]` whose lower left entry is the extension. -/
private noncomputable def triangularLift :
    SignedSym G →ₐ[R] Matrix (Fin 2) (Fin 2) (SignedSym G) :=
  lift G (triangular δ) fun _ _ _ _ hx hy => triangular_mul_triangular hδ hx hy

/-- The diagonal and upper right entries of `triangularLift` are `a`, `σ a` and `0`. -/
private theorem triangularLift_apply (a : SignedSym G) :
    triangularLift hδ a 0 0 = a ∧ triangularLift hδ a 0 1 = 0 ∧
      triangularLift hδ a 1 1 = twist a := by
  induction a using SignedSym.induction with
  | algebraMap r => simp [Matrix.algebraMap_matrix_apply]
  | generator x => simp [triangularLift, triangular]
  | mul a b ha hb =>
    simp [Matrix.mul_apply, Fin.sum_univ_two, ha.1, ha.2.1, ha.2.2, hb.1, hb.2.1, hb.2.2]
  | add a b ha hb => simp [ha.1, ha.2.1, ha.2.2, hb.1, hb.2.1, hb.2.2]

variable (δ) in
/-- The odd derivation of `A(V)` extending a degree-one linear map `δ : V → A(V)`. It satisfies
the signed Leibniz rule `TauCeti.SignedSym.liftDerivation_mul`, raises degree by one, and is the
unique such extension of `δ` (`TauCeti.SignedSym.eq_liftDerivation`). -/
noncomputable def liftDerivation : SignedSym G →ₗ[R] SignedSym G :=
  Matrix.entryLinearMap R (SignedSym G) (1 : Fin 2) (0 : Fin 2) ∘ₗ
    (triangularLift hδ).toLinearMap

private theorem liftDerivation_apply (a : SignedSym G) :
    liftDerivation δ hδ a = triangularLift hδ a 1 0 := (rfl)

/-- The odd derivation extends the assignment on generators. -/
@[simp]
theorem liftDerivation_generator (x : V) : liftDerivation δ hδ (generator G x) = δ x := by
  simp [liftDerivation_apply, triangularLift, triangular]

/-- **The signed Leibniz rule**: for a left factor of degree `p`,
`d (a * b) = d a * b + (-1) ^ p • (a * d b)`. -/
theorem liftDerivation_mul {p : ℤ} {a : SignedSym G} (ha : a ∈ signedSymPiece G p)
    (b : SignedSym G) :
    liftDerivation δ hδ (a * b) =
      liftDerivation δ hδ a * b + p.negOnePow • (a * liftDerivation δ hδ b) := by
  simp only [liftDerivation_apply, map_mul, Matrix.mul_apply, Fin.sum_univ_two,
    (triangularLift_apply hδ a).2.2, (triangularLift_apply hδ b).1, twist_of_mem ha]
  rw [Units.smul_def, Units.smul_def, smul_mul_assoc]

/-- The odd derivation annihilates the coefficients. -/
@[simp]
theorem liftDerivation_algebraMap (r : R) : liftDerivation δ hδ (algebraMap R _ r) = 0 :=
  map_algebraMap_of_leibniz (𝒜 := signedSymPiece G) (liftDerivation_mul hδ) r

/-- The odd derivation annihilates the unit. -/
@[simp]
theorem liftDerivation_one : liftDerivation δ hδ 1 = 0 :=
  map_one_eq_zero_of_leibniz (𝒜 := signedSymPiece G) (liftDerivation_mul hδ)

/-- The odd derivation raises degree by one. -/
theorem isHomogeneous_liftDerivation :
    LinearMap.IsHomogeneous (liftDerivation δ hδ) (signedSymPiece G) (signedSymPiece G) 1 := by
  refine LinearMap.isHomogeneous_def.2 fun p a ha => ?_
  refine (homogeneous_induction G
    (P := fun p a => a ∈ signedSymPiece G p ∧ liftDerivation δ hδ a ∈ signedSymPiece G (p + 1))
    ⟨SetLike.GradedOne.one_mem, by simp⟩
    (fun p x hx => ⟨generator_mem_signedSymPiece G hx, by simpa using hδ.map_mem hx⟩)
    (fun p q a b ha hb => ⟨SetLike.mul_mem_graded ha.1 hb.1, by
      rw [liftDerivation_mul hδ ha.1]
      refine add_mem ?_ (Submodule.smul_of_tower_mem _ _ ?_)
      · simpa [add_right_comm] using SetLike.mul_mem_graded ha.2 hb.1
      · simpa [add_assoc] using SetLike.mul_mem_graded ha.1 hb.2⟩)
    (fun p => ⟨zero_mem _, by simp⟩)
    (fun p a b ha hb => ⟨add_mem ha.1 hb.1, by rw [map_add]; exact add_mem ha.2 hb.2⟩)
    (fun p r a ha => ⟨Submodule.smul_mem _ r ha.1, by
      rw [map_smul]; exact Submodule.smul_mem _ r ha.2⟩)
    ha).2

/-- **Uniqueness of odd derivations**: a linear endomorphism of `A(V)` satisfying the signed
Leibniz rule and agreeing with `δ` on generators is `liftDerivation δ hδ`. No degree condition
on the endomorphism is needed. -/
theorem eq_liftDerivation {d : SignedSym G →ₗ[R] SignedSym G}
    (hleibniz : ∀ {p : ℤ} {a : SignedSym G}, a ∈ signedSymPiece G p → ∀ b : SignedSym G,
      d (a * b) = d a * b + p.negOnePow • (a * d b))
    (hgen : ∀ x, d (generator G x) = δ x) : d = liftDerivation δ hδ := by
  rw [← sub_eq_zero]
  refine eq_zero_of_leibniz Int.negOnePow (fun {p a} ha b => ?_) (fun x => ?_)
  · simp only [LinearMap.sub_apply, hleibniz ha, liftDerivation_mul hδ ha, sub_mul, mul_sub,
      Units.smul_def, zsmul_sub]
    abel
  · simp [hgen]

end Lift

/-- **Odd derivations are free on generators**: a degree-one linear map `δ : V → A(V)` extends
uniquely to a linear endomorphism of `A(V)` satisfying the signed Leibniz rule. -/
theorem existsUnique_odd_extension {δ : V →ₗ[R] SignedSym G}
    (hδ : LinearMap.IsHomogeneous δ G.piece (signedSymPiece G) 1) :
    ∃! d : SignedSym G →ₗ[R] SignedSym G, d ∘ₗ generator G = δ ∧
      ∀ {p : ℤ} {a : SignedSym G}, a ∈ signedSymPiece G p → ∀ b : SignedSym G,
        d (a * b) = d a * b + p.negOnePow • (a * d b) :=
  ⟨liftDerivation δ hδ, ⟨LinearMap.ext (liftDerivation_generator hδ), liftDerivation_mul hδ⟩,
    fun _ hd => eq_liftDerivation hδ hd.2 fun x => LinearMap.congr_fun hd.1 x⟩

/-- **The square of an odd derivation is determined by generators**: a degree-one linear
endomorphism of `A(V)` satisfying the signed Leibniz rule squares to zero if and only if its
square vanishes on generators. The square is an unsigned derivation, since the two cross terms
of the signed Leibniz rule cancel. -/
theorem comp_self_eq_zero_iff {d : SignedSym G →ₗ[R] SignedSym G}
    (hdeg : LinearMap.IsHomogeneous d (signedSymPiece G) (signedSymPiece G) 1)
    (hleibniz : ∀ {p : ℤ} {a : SignedSym G}, a ∈ signedSymPiece G p → ∀ b : SignedSym G,
      d (a * b) = d a * b + p.negOnePow • (a * d b)) :
    d ∘ₗ d = 0 ↔ ∀ x, d (d (generator G x)) = 0 := by
  refine ⟨fun h x => LinearMap.congr_fun h (generator G x), fun h => ?_⟩
  refine eq_zero_of_leibniz 1 (fun {p a} ha b => ?_) h
  have hda := hdeg.map_mem ha
  rw [LinearMap.comp_apply, LinearMap.comp_apply, LinearMap.comp_apply, hleibniz ha, map_add,
    map_zsmul_unit, hleibniz hda, hleibniz ha, Int.negOnePow_succ]
  simp only [Units.smul_def, Units.val_neg, neg_zsmul, zsmul_add, smul_smul, ← Units.val_mul,
    Int.units_mul_self, Units.val_one, one_zsmul, Pi.one_apply]
  abel

/-- **The extension is a differential**: `liftDerivation δ hδ` makes `A(V)` a differential
graded algebra if and only if it annihilates `δ x` for every `x : V`. -/
theorem isDGAlgebra_liftDerivation_iff {δ : V →ₗ[R] SignedSym G}
    (hδ : LinearMap.IsHomogeneous δ G.piece (signedSymPiece G) 1) :
    IsDGAlgebra (signedSymPiece G) (liftDerivation δ hδ) ↔
      ∀ x, liftDerivation δ hδ (δ x) = 0 := by
  refine ⟨fun h x => by simpa using h.sq_zero (generator G x), fun h => ?_⟩
  have hsq := (comp_self_eq_zero_iff (isHomogeneous_liftDerivation hδ)
    (liftDerivation_mul hδ)).2 (by simpa using h)
  exact
    { map_mem := fun ha => (isHomogeneous_liftDerivation hδ).map_mem ha
      sq_zero := fun a => LinearMap.congr_fun hsq a
      leibniz := fun ha b => liftDerivation_mul hδ ha b }

end TauCeti.SignedSym
