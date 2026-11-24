/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.CliffordAlgebra.Bivector.Basic
public import TauCeti.LinearAlgebra.ExteriorAlgebra.Contraction
public import TauCeti.RepresentationTheory.Spin.Equivariance
public import TauCeti.RepresentationTheory.Spin.HalfSpin.Basic
public import TauCeti.RepresentationTheory.Spin.ReversalPairing
import Mathlib.Algebra.Lie.OfAssociative
import TauCeti.LinearAlgebra.CliffordAlgebra.Reversal.Basic
import TauCeti.RepresentationTheory.Spin.HalfSpin.Weight

/-!
# The Clifford-multiplication trilinear form on vectors and spinors

Let `P` be a polarization of a quadratic space `(V, Q)`, with Fock model `S = ⋀ W` and Clifford
action `c = TauCeti.spinAction Q P`, and let `⟨s, t⟩ = φ (reverse s * t)` be the reversal pairing
of a functional `φ` on `S`. Composing Clifford multiplication `V ⊗ S → S` with the pairing gives
the trilinear form

  `T (v, s, t) = ⟨c(v) s, t⟩`

on `V × S × S`. When `φ` kills every contraction (and is invariant under the grade involution if
the polarization has a line summand), every vector acts self-adjointly, so
`T (v, s, t) = ⟨s, c(v) t⟩`. Combined with the Spin-equivariance of Clifford multiplication,
`ρ(g) c(v) ρ(g)⁻¹ = c(g • v)`, and the Spin-invariance of the pairing, this makes `T` invariant
under the diagonal action of the Spin group on `V × S × S`. For a Clifford element `x` with
`reverse x = -x` whose commutator with a vector `v` is again a vector, `x v - v x = w`, the form
satisfies `T (w, s, t) + T (v, c(x) s, t) + T (v, s, c(x) t) = 0`. A bivector satisfies this for
every `v`, so `T` is infinitesimally invariant under bivectors acting on `V` by the commutator and
on `S` by Clifford multiplication.

Without a line summand, Clifford multiplication by a vector exchanges the two half-spin summands
`S⁺` and `S⁻`, and `T` restricts to a trilinear form on `V × S⁺ × S⁻`, invariant under the Spin
group acting on all three factors. For the top-degree coefficient of a basis `w₁, …, wₙ` of `W`
the form is normalized by `T (w₁, 1, w₂ ∧ ⋯ ∧ wₙ) = 1`, and it vanishes on `(wᵢ, 1, x)` whenever
`x` already contains `wᵢ`. Over a nontrivial ring, when `n` is positive and even it is a nonzero
form on `V × S⁺ × S⁻`. When `n = 4` and the polarization has no line summand (`dim V = 8`), this
gives a nonzero `Spin₈`-invariant form on `V × S⁺ × S⁻`, the candidate triality form; its rank-four
normalization is in `TauCeti.RepresentationTheory.Spin.Triality.CliffordForm`.

## Main definitions

* `TauCeti.SpinPolarizationData.spinTrilinearForm`: the form `T (v, s, t) = ⟨c(v) s, t⟩` on
  `V × S × S`.
* `TauCeti.SpinPolarizationData.halfSpinTrilinearForm`: its restriction to `V × S⁺ × S⁻`.

## Main results

* `TauCeti.SpinPolarizationData.spinTrilinearForm_spinRep`: Spin-invariance of `T`.
* `TauCeti.SpinPolarizationData.spinTrilinearForm_add_add_eq_zero`: the infinitesimal-invariance
  identity for a Clifford element `x` with `reverse x = -x` at a vector `v` with
  `x v - v x = w` a vector, and
  `TauCeti.SpinPolarizationData.spinTrilinearForm_bivector_add_add_eq_zero`: infinitesimal
  invariance under bivectors.
* `TauCeti.SpinPolarizationData.halfSpinTrilinearForm_spinPlusAction_spinMinusAction`:
  Spin-invariance of the restricted form, through the actions on the two half-spin summands.
* `TauCeti.SpinPolarizationData.spinTrilinearForm_coord_univ_basis_erase`: the normalization
  `T (wᵢ, 1, w_{univ ∖ {i}}) = ±1`, and
  `TauCeti.SpinPolarizationData.halfSpinTrilinearForm_coord_univ_ne_zero`: over a nontrivial ring
  the restricted form is nonzero in positive even rank.

## References

* C. Chevalley, *The Algebraic Theory of Spinors* (1954), Chapter IV.
* J. C. Baez, *The Octonions*, Bull. Amer. Math. Soc. 39 (2002), §2.4.
* W. Fulton and J. Harris, *Representation Theory: A First Course*, Lecture 20, §20.3.
-/

public section

open CliffordAlgebra Module

namespace TauCeti.SpinPolarizationData

universe u v w

variable {K : Type u} [CommRing K] {V : Type v} [AddCommGroup V] [Module K V]
  {Q : QuadraticForm K V} (P : SpinPolarizationData Q)
  (φ : Module.Dual K (ExteriorAlgebra K P.W))

/-! ### The trilinear form on vectors and spinors -/

/-- **The Clifford-multiplication trilinear form** `T (v, s, t) = ⟨c(v) s, t⟩` on vectors and
spinors, the reversal pairing of `φ` composed with Clifford multiplication by a vector. -/
noncomputable def spinTrilinearForm :
    V →ₗ[K] ExteriorAlgebra K P.W →ₗ[K] ExteriorAlgebra K P.W →ₗ[K] K :=
  LinearMap.llcomp K _ _ _ (ExteriorAlgebra.reversalPairing φ) ∘ₗ
    (spinAction Q P).toLinearMap ∘ₗ ι Q

@[simp]
theorem spinTrilinearForm_apply (v : V) (s t : ExteriorAlgebra K P.W) :
    P.spinTrilinearForm φ v s t =
      ExteriorAlgebra.reversalPairing φ (spinAction Q P (ι Q v) s) t :=
  -- `(rfl)`, not `rfl`: the body of `spinTrilinearForm` is not `@[expose]`d.
  (rfl)

variable {φ}

/-- **Vectors may act on either spinor argument**: `⟨c(v) s, t⟩ = ⟨s, c(v) t⟩`, for a functional
killing every contraction and, unless the remainder of the polarization is zero, invariant under
the grade involution. -/
theorem spinTrilinearForm_apply_eq_reversalPairing_spinAction_ι
    (hφ : ∀ (d : Module.Dual K P.W) (x : ExteriorAlgebra K P.W), φ (contractLeft d x) = 0)
    (hline : P.line = ⊥ ∨ ∀ x : ExteriorAlgebra K P.W, φ (involute x) = φ x)
    (v : V) (s t : ExteriorAlgebra K P.W) :
    P.spinTrilinearForm φ v s t =
      ExteriorAlgebra.reversalPairing φ s (spinAction Q P (ι Q v) t) := by
  rw [spinTrilinearForm_apply, reversalPairing_spinAction_ι P φ hφ hline]

/-- **The trilinear form is `c`-symmetric in its spinor arguments** when reversal multiplies `φ`
by `c`. For the top-degree coefficient in rank `n`, `c = (-1) ^ (n.choose 2)`. -/
theorem spinTrilinearForm_swap
    (hφ : ∀ (d : Module.Dual K P.W) (x : ExteriorAlgebra K P.W), φ (contractLeft d x) = 0)
    (hline : P.line = ⊥ ∨ ∀ x : ExteriorAlgebra K P.W, φ (involute x) = φ x)
    {c : K} (hrev : ∀ x : ExteriorAlgebra K P.W, φ (reverse x) = c * φ x)
    (v : V) (s t : ExteriorAlgebra K P.W) :
    P.spinTrilinearForm φ v t s = c * P.spinTrilinearForm φ v s t := by
  rw [P.spinTrilinearForm_apply_eq_reversalPairing_spinAction_ι hφ hline, spinTrilinearForm_apply,
    ExteriorAlgebra.reversalPairing_swap φ hrev]

/-- **The trilinear form is Spin-invariant**: `T (g • v, g s, g t) = T (v, s, t)` for `g` in the
Spin group, acting on vectors through the special orthogonal group and on spinors by the spin
representation, for a functional killing every contraction and, unless the remainder of the
polarization is zero, invariant under the grade involution. -/
theorem spinTrilinearForm_spinRep [Invertible (2 : K)]
    (hφ : ∀ (d : Module.Dual K P.W) (x : ExteriorAlgebra K P.W), φ (contractLeft d x) = 0)
    (hline : P.line = ⊥ ∨ ∀ x : ExteriorAlgebra K P.W, φ (involute x) = φ x)
    (g : spinGroup Q) (v : V) (s t : ExteriorAlgebra K P.W) :
    P.spinTrilinearForm φ
        (((spinToSpecialOrthogonal Q g : QuadraticMap.specialOrthogonalGroup Q) : V ≃ₗ[K] V) v)
        (spinRep Q P g s) (spinRep Q P g t) =
      P.spinTrilinearForm φ v s t := by
  rw [spinTrilinearForm_apply, ← mul_apply_eq_comp, ← spinRep_mul_spinAction_ι,
    mul_apply_eq_comp, reversalPairing_spinRep P φ hφ hline, spinTrilinearForm_apply]

/-- **The infinitesimal-invariance identity** for a Clifford element `x` with `reverse x = -x`:
at a vector `v` whose commutator `x v - v x = w` is again a vector,
`T (w, s, t) + T (v, c(x) s, t) + T (v, s, c(x) t) = 0`. This is infinitesimal invariance of `T`
whenever the commutator with `x` preserves `V`, as it does for a bivector. -/
theorem spinTrilinearForm_add_add_eq_zero
    (hφ : ∀ (d : Module.Dual K P.W) (x : ExteriorAlgebra K P.W), φ (contractLeft d x) = 0)
    (hline : P.line = ⊥ ∨ ∀ x : ExteriorAlgebra K P.W, φ (involute x) = φ x)
    {x : CliffordAlgebra Q} (hx : reverse x = -x) {v w : V}
    (hw : x * ι Q v - ι Q v * x = ι Q w) (s t : ExteriorAlgebra K P.W) :
    P.spinTrilinearForm φ w s t + P.spinTrilinearForm φ v (spinAction Q P x s) t +
      P.spinTrilinearForm φ v s (spinAction Q P x t) = 0 := by
  -- Move every operator onto the last argument: the three terms become `⟨s, y t⟩` for
  -- `y = x v - v x`, `reverse x * v = -x v` and `v x`, which sum to zero.
  rw [P.spinTrilinearForm_apply_eq_reversalPairing_spinAction_ι hφ hline w,
    P.spinTrilinearForm_apply_eq_reversalPairing_spinAction_ι hφ hline v,
    spinTrilinearForm_apply, ← hw, reversalPairing_spinAction P φ hφ hline,
    reversalPairing_spinAction P φ hφ hline, hx, reverse_ι]
  simp only [map_sub, map_neg, map_mul, LinearMap.sub_apply, LinearMap.neg_apply,
    mul_apply_eq_comp]
  ring

/-- **The trilinear form is infinitesimally invariant under bivectors**: the bivector of `a` and
`b` acts on vectors by the infinitesimal rotation `v ↦ Q.polar b v • a - Q.polar a v • b`. -/
theorem spinTrilinearForm_bivector_add_add_eq_zero [Invertible (2 : K)]
    (hφ : ∀ (d : Module.Dual K P.W) (x : ExteriorAlgebra K P.W), φ (contractLeft d x) = 0)
    (hline : P.line = ⊥ ∨ ∀ x : ExteriorAlgebra K P.W, φ (involute x) = φ x)
    (a b v : V) (s t : ExteriorAlgebra K P.W) :
    P.spinTrilinearForm φ (QuadraticMap.polar Q b v • a - QuadraticMap.polar Q a v • b) s t +
        P.spinTrilinearForm φ v (spinAction Q P (bivector Q a b) s) t +
      P.spinTrilinearForm φ v s (spinAction Q P (bivector Q a b) t) = 0 := by
  let := LieRing.ofAssociativeRing (A := CliffordAlgebra Q)
  exact P.spinTrilinearForm_add_add_eq_zero hφ hline (reverse_bivector Q a b)
    (by rw [← Ring.lie_def, bivector_lie_ι]) s t

/-! ### The restriction to the two half-spin summands -/

/-- **The trilinear form on vectors and the two half-spin summands**, the restriction of
`TauCeti.SpinPolarizationData.spinTrilinearForm` to `V × S⁺ × S⁻`. -/
noncomputable def halfSpinTrilinearForm (φ : Module.Dual K (ExteriorAlgebra K P.W)) :
    V →ₗ[K] spinPlus Q P →ₗ[K] spinMinus Q P →ₗ[K] K :=
  ((P.spinTrilinearForm φ).compl₂ (spinPlus Q P).subtype).compr₂
    (LinearMap.lcomp K K (spinMinus Q P).subtype)

@[simp]
theorem halfSpinTrilinearForm_apply (v : V) (s : spinPlus Q P) (t : spinMinus Q P) :
    P.halfSpinTrilinearForm φ v s t = P.spinTrilinearForm φ v s t :=
  -- `(rfl)`, not `rfl`: the body of `halfSpinTrilinearForm` is not `@[expose]`d.
  (rfl)

/-- **The half-spin trilinear form is Spin-invariant**, for a polarization without a line summand
and a functional killing every contraction: a Spin element `g` acts on `V` through the special
orthogonal group and on `S⁺` and `S⁻` through the even Clifford algebra. -/
theorem halfSpinTrilinearForm_spinPlusAction_spinMinusAction [Invertible (2 : K)]
    (hφ : ∀ (d : Module.Dual K P.W) (x : ExteriorAlgebra K P.W), φ (contractLeft d x) = 0)
    (hline : P.line = ⊥) (g : spinGroup Q) (v : V) (s : spinPlus Q P) (t : spinMinus Q P) :
    P.halfSpinTrilinearForm φ
        (((spinToSpecialOrthogonal Q g : QuadraticMap.specialOrthogonalGroup Q) : V ≃ₗ[K] V) v)
        (spinPlusAction Q P hline ⟨g, spinGroup.mem_even g.property⟩ s)
        (spinMinusAction Q P hline ⟨g, spinGroup.mem_even g.property⟩ t) =
      P.halfSpinTrilinearForm φ v s t := by
  simpa only [halfSpinTrilinearForm_apply, coe_spinPlusAction_apply, coe_spinMinusAction_apply,
    spinRep_apply] using P.spinTrilinearForm_spinRep hφ (Or.inl hline) g v s t

/-! ### Normalization by the top-degree coefficient of a basis -/

section Basis

variable {I : Type w} [LinearOrder I] (b : Module.Basis I K P.W)

/-- **The trilinear form on a basis vector, the vacuum and an exterior-basis vector**:
`T (wᵢ, 1, w_s) = φ (wᵢ ∧ w_s)`, which is zero when `i ∈ s` and otherwise `φ` of the basis vector
of `insert i s` times the sign moving `i` to the front. -/
theorem spinTrilinearForm_basis_one_basis (φ : Module.Dual K (ExteriorAlgebra K P.W)) (i : I)
    (s : Finset I) :
    P.spinTrilinearForm φ (b i : V) 1 (b.ExteriorAlgebra s) =
      if i ∈ s then 0
        else
          ExteriorAlgebra.basisEraseSign i (insert i s) • φ (b.ExteriorAlgebra (insert i s)) := by
  rw [spinTrilinearForm_apply, spinAction_ι_wedge, mul_one, ExteriorAlgebra.reversalPairing_apply,
    reverse_ι, ExteriorAlgebra.ι_mul_basis, apply_ite φ, map_zero, Units.smul_def, map_zsmul,
    Units.smul_def]

/-- **The top-degree normalization of the trilinear form**: for a basis `w` of `W` and the
top-degree coefficient, `T (wᵢ, 1, w_{univ ∖ {i}})` is the sign moving `i` to the front of the
index set. -/
theorem spinTrilinearForm_coord_univ_basis_erase [Fintype I] (i : I) :
    P.spinTrilinearForm (b.ExteriorAlgebra.coord Finset.univ) (b i : V) 1
        (b.ExteriorAlgebra (Finset.univ.erase i)) =
      ((ExteriorAlgebra.basisEraseSign i Finset.univ : ℤ) : K) := by
  rw [spinTrilinearForm_basis_one_basis, ite_eq_right (Finset.notMem_erase i _),
    Finset.insert_erase (Finset.mem_univ i)]
  simp [Units.smul_def]

/-- **The trilinear form vanishes on a repeated basis vector**: `T (wᵢ, 1, w_s) = 0` when
`i ∈ s`, since `wᵢ ∧ w_s = 0`. -/
theorem spinTrilinearForm_basis_one_basis_eq_zero_of_mem
    (φ : Module.Dual K (ExteriorAlgebra K P.W)) {i : I} {s : Finset I} (hi : i ∈ s) :
    P.spinTrilinearForm φ (b i : V) 1 (b.ExteriorAlgebra s) = 0 := by
  rw [spinTrilinearForm_basis_one_basis, ite_eq_left hi]

/-- **The trilinear form of the top-degree coefficient pairs `wᵢ`, `1` and `w_{univ ∖ {i}}` to a
nonzero scalar** over a nontrivial ring, namely the sign `±1`. -/
theorem spinTrilinearForm_coord_univ_basis_erase_ne_zero [Fintype I] [Nontrivial K] (i : I) :
    P.spinTrilinearForm (b.ExteriorAlgebra.coord Finset.univ) (b i : V) 1
        (b.ExteriorAlgebra (Finset.univ.erase i)) ≠ 0 := by
  rw [spinTrilinearForm_coord_univ_basis_erase]
  exact ((ExteriorAlgebra.basisEraseSign i Finset.univ).isUnit.map (Int.castRingHom K)).ne_zero

/-- **The trilinear form of the top-degree coefficient is nonzero** over a nontrivial ring, for
a nonzero isotropic summand `W`. -/
theorem spinTrilinearForm_coord_univ_ne_zero [Fintype I] [Nontrivial K] [Nonempty I] :
    P.spinTrilinearForm (b.ExteriorAlgebra.coord Finset.univ) ≠ 0 := by
  obtain ⟨i⟩ := ‹Nonempty I›
  intro h
  exact P.spinTrilinearForm_coord_univ_basis_erase_ne_zero b i (by simp [h])

/-- **The half-spin trilinear form of the top-degree coefficient is nonzero** over a nontrivial
ring in positive even rank: it pairs the vacuum `1 ∈ S⁺`, the odd spinor
`w_{univ ∖ {i}} ∈ S⁻` and the vector `wᵢ` to `±1`. -/
theorem halfSpinTrilinearForm_coord_univ_ne_zero [Fintype I] [Nontrivial K] [Nonempty I]
    (hI : Even (Fintype.card I)) :
    P.halfSpinTrilinearForm (b.ExteriorAlgebra.coord Finset.univ) ≠ 0 := by
  classical
  obtain ⟨i⟩ := ‹Nonempty I›
  have ht : b.ExteriorAlgebra (Finset.univ.erase i) ∈ spinMinus Q P :=
    (basis_mem_spinMinus_iff P b _).2 (by
      rw [Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_univ]
      exact Nat.Even.sub_odd Fintype.card_pos hI odd_one)
  intro h
  refine P.spinTrilinearForm_coord_univ_basis_erase_ne_zero b i ?_
  rw [← P.halfSpinTrilinearForm_apply (s := ⟨1, (mem_spinPlus P).2 (SetLike.one_mem_graded _)⟩)
    (t := ⟨_, ht⟩), h]
  simp

end Basis

end TauCeti.SpinPolarizationData
