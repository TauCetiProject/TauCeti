/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.MvPolynomial.Dehomogenization

/-!
# Detecting projective hypersurface singularities on standard charts

For a homogeneous polynomial over a field, the geometric gradient criterion on the
punctured affine cone is equivalent to the unit-ideal criterion on every affine chart.
The equivalence also applies when the characteristic divides the degree.
-/

public section

namespace MvPolynomial

open TauCeti (dehomogenize)

variable {k F : Type*} [Field k] [Field F] [Algebra k F] [IsAlgClosed F] {n d : ℕ}

/-- The gradient is nonzero at every nonzero geometric zero of a homogeneous polynomial
if and only if each dehomogenization generates the unit ideal together with its partials. -/
theorem IsHomogeneous.forall_exists_aeval_pderiv_ne_zero_iff {P : MvPolynomial (Fin (n + 1)) k}
    (hP : P.IsHomogeneous d) :
    (∀ x : Fin (n + 1) → F, x ≠ 0 → MvPolynomial.aeval x P = 0 →
      ∃ j, MvPolynomial.aeval x (MvPolynomial.pderiv j P) ≠ 0) ↔
      ∀ i, Ideal.span (insert (dehomogenize i P)
        (Set.range fun j ↦ MvPolynomial.pderiv j (dehomogenize i P))) = ⊤ := by
  constructor
  · intro h i
    apply TauCeti.span_insert_range_pderiv_dehomogenize_eq_top (K := F) hP
    exact fun a ↦ h _ (fun he ↦ (one_ne_zero : (1 : F) ≠ 0) (by simpa using congrFun he i))
  · intro h x hx hxQ
    obtain ⟨i, hi⟩ := Function.ne_iff.mp hx
    let a := fun j ↦ x (i.succAbove j) / x i
    let f := algebraMap k F
    have heval {σ : Type} (v : σ → F) (g : MvPolynomial σ k) :
        MvPolynomial.eval v (MvPolynomial.map f g) = MvPolynomial.aeval v g := by
      rw [eval_map, aeval_def]
    have hm := hP.map f
    have hzero := (heval x _).trans hxQ
    have ha : MvPolynomial.aeval a (dehomogenize i P) = 0 := by
      rw [← heval, TauCeti.map_dehomogenize, TauCeti.eval_dehomogenize_div i hm x hi,
        hzero, mul_zero]
    obtain ⟨g, hg, hg₀⟩ := (span_eq_top_iff_forall_exists_aeval_ne_zero (K := F)).mp (h i) a
    rcases hg with rfl | ⟨j, rfl⟩
    · exact (hg₀ ha).elim
    · have hj : MvPolynomial.eval a
          (MvPolynomial.pderiv j (dehomogenize i (MvPolynomial.map f P))) ≠ 0 := by
        rwa [← TauCeti.map_dehomogenize, pderiv_map, heval]
      obtain ⟨l, hl⟩ :=
        (TauCeti.exists_eval_pderiv_ne_zero_iff_dehomogenize_div i hm x hi hzero).mpr ⟨j, hj⟩
      exact ⟨l, by rwa [pderiv_map, heval] at hl⟩

end MvPolynomial
