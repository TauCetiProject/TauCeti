/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.CliffordAlgebra.Spin.Kernel
public import TauCeti.RepresentationTheory.ClassicalGroups.Symplectic
public import TauCeti.RepresentationTheory.Spin.ReversalPairing
import TauCeti.RepresentationTheory.Spin.Exceptional.Five.Group

/-!
# The reversal pairing of `Spin₅` and the standard symplectic form

For a polarization `V = W ⊕ W' ⊕ L` of a five-dimensional quadratic space, the four-dimensional
spinor module `S = ⋀ W` carries the reversal pairing `⟨s, t⟩ = [reverse s ∧ t]_top` of a basis
`w₁, w₂` of `W`, which is Spin-invariant (`TauCeti.reversalPairing_coord_univ_spinRep`). When
`2 ≠ 0` in `K`, the group `Spin(Q)` is isomorphic to `Sp₄(K)` by an isomorphism `f` under which
the spin representation is the standard representation of `Sp₄`, along a linear equivalence
`E : S ≃ K⁴`
(`exists_spinGroup_mulEquiv_symplecticGroup_and_spinRep_equiv_stdSymplecticRep_of_finrank_eq_five`).

This file compares the two symplectic structures on `S`. Every bilinear form on `K⁴` invariant
under `Sp₄(K)` is a multiple of the standard form `ω(x, y) = xᵀ J y`
(`TauCeti.exists_eq_smul_stdSymplecticBilinForm`), so every Spin-invariant bilinear form on `S`
is a multiple of `ω(E s, E t)`. For the reversal pairing the multiple is nonzero, since
`⟨1, w₁ ∧ w₂⟩ = 1`. Consequently, when `2 ≠ 0`, the Spin-invariant bilinear forms on `S` form a
line, spanned by the reversal pairing. The scalar `-1` of `Spin(Q)` acts on `S` by `-1`, so `f`
sends it to the central element `-I` of `Sp₄(K)`; when `2 ≠ 0` it does not act trivially, as it
does on `V`.

## Main results

* `TauCeti.exists_eq_mul_stdSymplecticBilinForm_of_isInvariantForm`: along `(f, E)`, a
  Spin-invariant bilinear form on `S` is a multiple of the standard symplectic form.
* `TauCeti.exists_reversalPairing_eq_mul_stdSymplecticBilinForm`: along `(f, E)`, the reversal
  pairing is a nonzero multiple of the standard symplectic form.
* `TauCeti.coe_apply_spinGroup_negOne`: `f` sends the scalar `-1` of `Spin(Q)` to `-I`.
* `TauCeti.exists_eq_smul_reversalPairing_of_finrank_eq_five` and
  `TauCeti.invariantForms_spinRep_eq_span_reversalPairing_of_finrank_eq_five`: in dimension five
  with `2 ≠ 0`, every Spin-invariant bilinear form on `S` is a multiple of the reversal pairing.

## References

* W. Fulton and J. Harris, *Representation Theory: A First Course*, Lecture 20, §20.1.
* C. Chevalley, *The Algebraic Theory of Spinors* (1954), Chapter III.
-/

public section

open CliffordAlgebra Module

namespace TauCeti

universe u v

variable {K : Type u} [Field K] {V : Type v} [AddCommGroup V] [Module K V]
  {Q : QuadraticForm K V} {P : SpinPolarizationData Q} {n : ℕ}
  {f : spinGroup Q ≃* Matrix.symplecticGroup (Fin n) K}

/-- **Spin-invariant forms are multiples of the transported standard symplectic form.** Along an
isomorphism `f : Spin(Q) ≃ Sp₂ₙ(K)` and an equivalence `E` of the spin representation with the
standard representation of `Sp₂ₙ(K)` through `f`, every Spin-invariant bilinear form on the
spinor module is a multiple of the standard symplectic form `ω(E s, E t)`. In dimension five over
a field with `2 ≠ 0`, such `f` and `E` exist with `n = 2`, by
`exists_spinGroup_mulEquiv_symplecticGroup_and_spinRep_equiv_stdSymplecticRep_of_finrank_eq_five`.
-/
theorem exists_eq_mul_stdSymplecticBilinForm_of_isInvariantForm
    (E : (spinRep Q P).Equiv ((stdSymplecticRep K n).comp f.toMonoidHom))
    {B : LinearMap.BilinForm K (ExteriorAlgebra K P.W)}
    (hB : Representation.IsInvariantForm (spinRep Q P) B) :
    ∃ c : K, ∀ s t, B s t = c * stdSymplecticBilinForm K n (E s) (E t) := by
  -- Transport `B` to `K^(2n)` along `E`; it is invariant under `Sp₂ₙ(K)` since `f` is onto.
  obtain ⟨c, hc⟩ :=
    exists_eq_smul_stdSymplecticBilinForm K n (hB.comp_equiv_symm E f.surjective)
  set e := E.toLinearEquiv
  have he (s : ExteriorAlgebra K P.W) : e s = E s := by
    rw [Representation.Equiv.toLinearEquiv_apply, Representation.Equiv.coe_toIntertwiningMap]
  refine ⟨c, fun s t => ?_⟩
  have h := LinearMap.BilinForm.congr_fun hc (e s) (e t)
  simp only [LinearMap.BilinForm.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply,
    LinearMap.smul_apply, smul_eq_mul] at h
  rwa [he, he] at h

/-- **The reversal pairing is a nonzero multiple of the transported standard symplectic form.**
Along an isomorphism `f : Spin(Q) ≃ Sp₂ₙ(K)` and an equivalence `E` of the spin representation
with the standard representation of `Sp₂ₙ(K)` through `f`, the reversal pairing
`[reverse s ∧ t]_top` of a basis of the rank-two isotropic summand `W` is a nonzero multiple of
the standard symplectic form `ω(E s, E t)`. In dimension five over a field with `2 ≠ 0`, such `f`
and `E` exist with `n = 2`, by
`exists_spinGroup_mulEquiv_symplecticGroup_and_spinRep_equiv_stdSymplecticRep_of_finrank_eq_five`.
-/
theorem exists_reversalPairing_eq_mul_stdSymplecticBilinForm
    (E : (spinRep Q P).Equiv ((stdSymplecticRep K n).comp f.toMonoidHom))
    (b : Basis (Fin 2) K P.W) :
    ∃ c : K, c ≠ 0 ∧ ∀ s t,
      ExteriorAlgebra.reversalPairing (b.ExteriorAlgebra.coord Finset.univ) s t =
        c * stdSymplecticBilinForm K n (E s) (E t) := by
  obtain ⟨c, hc⟩ := exists_eq_mul_stdSymplecticBilinForm_of_isInvariantForm E
    (isInvariantForm_reversalPairing_coord_univ P b (Or.inr (by simp)))
  refine ⟨c, fun h0 => ?_, hc⟩
  have h := hc 1 (ExteriorAlgebra.ι K (b 0) * ExteriorAlgebra.ι K (b 1))
  rw [ExteriorAlgebra.reversalPairing_coord_univ_one_ι_zero_mul_ι_one, h0, zero_mul] at h
  exact one_ne_zero h

/-- **`-1` goes to `-I`.** An isomorphism `f : Spin(Q) ≃ Sp₂ₙ(K)` along which the spin
representation is the standard representation of `Sp₂ₙ(K)` sends the scalar `-1` of `Spin(Q)`,
which acts on the spinor module by `-1`, to the central element `-I`. -/
theorem coe_apply_spinGroup_negOne
    (E : (spinRep Q P).Equiv ((stdSymplecticRep K n).comp f.toMonoidHom)) (hQ : Q ≠ 0) :
    (f (spinGroup.negOne Q hQ) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) = -1 := by
  refine Matrix.mulVec_injective (funext fun x => ?_)
  obtain ⟨s, rfl⟩ := E.surjective x
  have h := Representation.IntertwiningMap.isIntertwining _ _ E.toIntertwiningMap
    (spinGroup.negOne Q hQ) s
  simp only [spinRep_apply, spinGroup.coe_negOne, map_neg, map_one, LinearMap.neg_apply,
    one_apply_eq_self, MonoidHom.comp_apply, stdSymplecticRep_apply_apply,
    Representation.Equiv.coe_toIntertwiningMap] at h
  rw [Matrix.neg_mulVec, Matrix.one_mulVec]
  exact h.symm

/-- **The invariant forms on the spinors of `Spin₅`.** For a polarization of a five-dimensional
quadratic space over a field with `2 ≠ 0`, every Spin-invariant bilinear form on the spinor
module `⋀ W` is a scalar multiple of the reversal pairing `[reverse s ∧ t]_top` of a basis of
`W`. -/
theorem exists_eq_smul_reversalPairing_of_finrank_eq_five [NeZero (2 : K)]
    (hV : finrank K V = 5) (b : Basis (Fin 2) K P.W)
    {B : LinearMap.BilinForm K (ExteriorAlgebra K P.W)}
    (hB : Representation.IsInvariantForm (spinRep Q P) B) :
    ∃ c : K, B = c • ExteriorAlgebra.reversalPairing (b.ExteriorAlgebra.coord Finset.univ) := by
  obtain ⟨f, ⟨E⟩⟩ :=
    exists_spinGroup_mulEquiv_symplecticGroup_and_spinRep_equiv_stdSymplecticRep_of_finrank_eq_five
      P hV
  obtain ⟨c, hc⟩ := exists_eq_mul_stdSymplecticBilinForm_of_isInvariantForm E hB
  obtain ⟨d, hd, hrev⟩ := exists_reversalPairing_eq_mul_stdSymplecticBilinForm E b
  refine ⟨c / d, LinearMap.BilinForm.ext fun s t => ?_⟩
  rw [hc, LinearMap.smul_apply, LinearMap.smul_apply, hrev, smul_eq_mul]
  field_simp

/-- **The invariant forms on the spinors of `Spin₅` form a line**: for a polarization of a
five-dimensional quadratic space over a field with `2 ≠ 0`, the Spin-invariant bilinear forms on
the spinor module `⋀ W` are the multiples of the reversal pairing `[reverse s ∧ t]_top` of a basis
of `W`. -/
theorem invariantForms_spinRep_eq_span_reversalPairing_of_finrank_eq_five [NeZero (2 : K)]
    (hV : finrank K V = 5) (b : Basis (Fin 2) K P.W) :
    Representation.invariantForms (spinRep Q P) =
      Submodule.span K {ExteriorAlgebra.reversalPairing (b.ExteriorAlgebra.coord Finset.univ)} :=
  Representation.IsInvariantForm.invariantForms_eq_span_of_forall_exists_eq_smul
    (isInvariantForm_reversalPairing_coord_univ P b (Or.inr (by simp)))
    fun _ => exists_eq_smul_reversalPairing_of_finrank_eq_five hV b

end TauCeti
