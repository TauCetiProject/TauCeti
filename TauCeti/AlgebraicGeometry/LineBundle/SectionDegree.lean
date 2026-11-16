/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EffectiveCartierDivisor.ZeroLocus
public import TauCeti.AlgebraicGeometry.EffectiveCartierDivisor.Degree.EulerCharacteristic
public import TauCeti.AlgebraicGeometry.EffectiveCartierDivisor.TensorProduct

/-!
# Nonzero sections and degree on integral curves

On a proper integral curve a line bundle with a nonzero global section has nonnegative
Euler-characteristic degree. Its degree is zero exactly when its class is trivial. The
curve may be singular and the ground field need not be algebraically closed. Only the
finite-dimensionality of `H⁰(𝒪_X)` and `H¹(𝒪_X)` is needed as cohomological input.

The zero divisor of a section gives these conclusions by its finite length. This is the
section-theoretic input to positivity of ample line bundles on proper curves.

## References

* The Stacks Project, Section 33.44, *Degrees on curves* (Tag 0AYQ).
-/

public section

open AlgebraicGeometry CategoryTheory

namespace TauCeti.AlgebraicGeometry.InvertibleSheaf

universe u

variable (k : Type u) [Field k] {X : Scheme.{u}} [X.Over (Spec (.of k))] [IsIntegral X]
  [IsProper (X ↘ Spec (.of k))] [RelativeDimensionLE 1 (X ↘ Spec (.of k))]
  [FiniteDimensional k (Scheme.Modules.Cohomology (trivial X).obj 0)]
  [FiniteDimensional k (Scheme.Modules.Cohomology (trivial X).obj 1)]
  (L : InvertibleSheaf X)

/-- A nonzero section on a proper integral curve gives an effective Cartier ideal of inverse
class, and the degree of the line bundle is the length over the ground field of its zero
subscheme. -/
theorem exists_isEffectiveCartier_eulerDegree_eq_of_ne_zero
    (s : Γ(L.obj, ⊤)) (hs : s ≠ 0) :
    ∃ (I : X.IdealSheafData) (hI : I.IsEffectiveCartier),
      LineBundleClass.mk hI.toInvertibleSheaf = (LineBundleClass.mk L)⁻¹ ∧
        L.eulerDegree k = (I.subschemeι ≫ X ↘ Spec (.of k)).finrank default := by
  obtain ⟨I, hI, hclass⟩ := L.exists_isEffectiveCartier_of_ne_zero s hs
  have := hI.isFinite_subschemeι_comp (f := X ↘ Spec (.of k))
  have hdegree := hI.eulerDegree_inv_mk_toInvertibleSheaf k I default
  rw [hclass, inv_inv, LineBundleClass.eulerDegree_mk] at hdegree
  exact ⟨I, hI, hclass, hdegree⟩

/-- A line bundle with a nonzero global section on a proper integral curve has nonnegative
Euler-characteristic degree, even when the curve is singular. -/
theorem eulerDegree_nonneg_of_ne_zero (s : Γ(L.obj, ⊤)) (hs : s ≠ 0) :
    0 ≤ L.eulerDegree k := by
  obtain ⟨I, _, _, hdegree⟩ := L.exists_isEffectiveCartier_eulerDegree_eq_of_ne_zero k s hs
  exact hdegree.symm ▸ Int.natCast_nonneg _

/-- A line bundle on a proper integral curve that has a nonzero global section has degree
zero exactly when it is trivial. No genus, smoothness, or rational-point assumption is needed. -/
theorem eulerDegree_eq_zero_iff_of_ne_zero (s : Γ(L.obj, ⊤)) (hs : s ≠ 0) :
    L.eulerDegree k = 0 ↔ LineBundleClass.mk L = 1 := by
  constructor
  · intro hdeg
    obtain ⟨I, hI, hclass, hdegree⟩ :=
      L.exists_isEffectiveCartier_eulerDegree_eq_of_ne_zero k s hs
    have := hI.isFinite_subschemeι_comp (f := X ↘ Spec (.of k))
    rw [hdeg] at hdegree
    have hempty : IsEmpty I.subscheme := by
      have hnot := (Scheme.Hom.finrank_eq_zero_iff_notMem_range
        (I.subschemeι ≫ X ↘ Spec (.of k)) default).mp (Int.natCast_eq_zero.mp hdegree.symm)
      exact ⟨fun x ↦ hnot ⟨x, Subsingleton.elim _ _⟩⟩
    have htop : I = ⊤ := by
      rw [← I.ker_subschemeι, Scheme.Hom.ker_eq_top_iff_isEmpty]
      exact hempty
    have hclassOne : LineBundleClass.mk hI.toInvertibleSheaf = 1 := by
      subst I
      exact LineBundleClass.mk_toInvertibleSheaf_top
    exact inv_eq_one.mp (hclass.symm.trans hclassOne)
  · intro hclass
    rw [← LineBundleClass.eulerDegree_mk, hclass, LineBundleClass.eulerDegree_one]

end TauCeti.AlgebraicGeometry.InvertibleSheaf
