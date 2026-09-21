/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Lie.Killing
public import Mathlib.LinearAlgebra.BilinearForm.Orthogonal

/-!
# An ad-nilpotent element of a Killing Lie algebra is a bracket with itself

Let `L` be a finite-dimensional Lie algebra over a field whose Killing form `κ` is nondegenerate,
and let `x : L` be an element whose adjoint action `ad x` is nilpotent.  Then there is a `t : L`
with

`⁅x, t⁆ = x`,

which is `TauCeti.exists_lie_eq_self_of_isNilpotent_ad`.  Equivalently, `x` is an eigenvector of
`ad t` for the eigenvalue `-1`.

The proof is the Killing-orthogonality of the kernel and the range of `ad x`, and it needs no
algebraically closed field, no Cartan subalgebra, and no `sl₂`-triple.  In two steps:

* **`x` is Killing-orthogonal to `ker (ad x)`.**  If `⁅x, z⁆ = 0` then `ad x` and `ad z` commute,
  so `ad x ∘ ad z` is nilpotent and its trace `κ x z` vanishes.  Only reducedness of the
  coefficients is used, and the statement is proved for the trace form of an arbitrary
  representation (`TauCeti.traceForm_eq_zero_of_isNilpotent_of_lie_eq_zero`), the Killing form
  being the trace form of the adjoint representation.
* **The Killing-orthogonal complement of `range (ad x)` is `ker (ad x)`.**  This is invariance,
  `κ ⁅x, z⁆ y = - κ z ⁅x, y⁆`: the left-hand side vanishes for every `z` exactly when `⁅x, y⁆` is
  Killing-orthogonal to everything, which by nondegeneracy means `⁅x, y⁆ = 0`.  On a
  finite-dimensional space a nondegenerate symmetric form is reflexive and its double orthogonal
  complement is the original subspace, so `range (ad x)` is in turn the orthogonal complement of
  `ker (ad x)`, and the first step places `x` in it.

Nondegeneracy is what carries the argument: in an abelian Lie algebra every `ad x` is nilpotent
while `range (ad x)` is `⊥`, so no nonzero `x` is a bracket with itself there.  The hypothesis is
satisfied, nonvacuously, by every root vector of a split semisimple Lie algebra, which is
ad-nilpotent by `LieAlgebra.isNilpotent_ad_of_mem_rootSpace`.  For such a vector `e` the
conclusion is also visible in an `sl₂`-triple `(h, e, f)`, where `⁅h, e⁆ = 2 • e` gives
`t = -(2 : K)⁻¹ • h`; what is proved here needs no triple, no Cartan subalgebra, no root space
decomposition, no triangularizability and no invertible `2`, only ad-nilpotence of `x` and
nondegeneracy of `κ`.

## Main results

* `TauCeti.traceForm_eq_zero_of_isNilpotent_of_lie_eq_zero`: **commuting elements, one of them
  acting nilpotently, are orthogonal for the trace form** of any representation.
* `TauCeti.orthogonal_range_ad_eq_ker_ad` and `TauCeti.range_ad_eq_orthogonal_ker_ad`: **the
  kernel and the range of `ad x` are each other's Killing-orthogonal complements.**
* `TauCeti.mem_range_ad_self_of_isNilpotent_ad`: **an ad-nilpotent element lies in the range of
  its own adjoint action.**
* `TauCeti.exists_lie_eq_self_of_isNilpotent_ad`: **hence `⁅x, t⁆ = x` for some `t`**, with
  `TauCeti.exists_lie_eq_neg_self_of_isNilpotent_ad` the eigenvector reading.

## References

This is the `⁅s, t⁆ = s` milestone that Layer 5 of
`TauCetiRoadmap/RepresentationTheory/AdoIwasawa/README.md` asks to be named as its own target and
proved over the original field, "with no algebraic closure and no appeal to `sl₂`-triple
existence", so that Jacobson-Morozov stays out of the dependency graph of Hochschild's
strengthening of Ado's theorem.

* G. Hochschild, *An addition to Ado's theorem*, Proc. Amer. Math. Soc. **17** (1966), 531-533.
* J. E. Humphreys, *Introduction to Lie Algebras and Representation Theory*, GTM 9, §5.1, for the
  invariance and nondegeneracy of the Killing form.
-/

public section

namespace TauCeti

open LieAlgebra LieModule

section TraceForm

variable {R L M : Type*} [CommRing R] [IsReduced R] [LieRing L] [LieAlgebra R L]
  [AddCommGroup M] [Module R M] [LieRingModule L M] [LieModule R L M]

/-- **Commuting operators, one of them nilpotent, are orthogonal for the trace form.**  The trace
form pairs `x` and `y` by the trace of the composite of their actions; if the two actions commute
and the first is nilpotent then so is the composite, and a nilpotent scalar in a reduced ring is
zero. -/
theorem traceForm_eq_zero_of_isNilpotent_of_commute {x y : L}
    (hx : IsNilpotent (toEnd R L M x)) (hcomm : Commute (toEnd R L M x) (toEnd R L M y)) :
    traceForm R L M x y = 0 := by
  rw [traceForm_apply_apply, ← Module.End.mul_eq_comp]
  exact (LinearMap.isNilpotent_trace_of_isNilpotent (hcomm.isNilpotent_mul_right hx)).eq_zero

/-- **An element acting nilpotently is orthogonal, for the trace form of any representation, to
everything it commutes with.**  Bracketing to zero in `L` is stronger than having commuting
actions, and it is the hypothesis available in the adjoint setting of
`TauCeti.killingForm_eq_zero_of_isNilpotent_ad_of_lie_eq_zero`. -/
theorem traceForm_eq_zero_of_isNilpotent_of_lie_eq_zero {x y : L}
    (hx : IsNilpotent (toEnd R L M x)) (hxy : ⁅x, y⁆ = 0) :
    traceForm R L M x y = 0 := by
  have hcomm : toEnd R L M x * toEnd R L M y = toEnd R L M y * toEnd R L M x :=
    LinearMap.ext fun m ↦ by
      have h := lie_lie x y m
      rw [hxy, zero_lie] at h
      simp only [Module.End.mul_apply, toEnd_apply_apply]
      exact sub_eq_zero.mp h.symm
  exact traceForm_eq_zero_of_isNilpotent_of_commute hx hcomm

end TraceForm

section KillingForm

variable {R L : Type*} [CommRing R] [IsReduced R] [LieRing L] [LieAlgebra R L]

/-- **An ad-nilpotent element is Killing-orthogonal to its own centraliser.**  This is
`TauCeti.traceForm_eq_zero_of_isNilpotent_of_lie_eq_zero` for the adjoint representation. -/
theorem killingForm_eq_zero_of_isNilpotent_ad_of_lie_eq_zero {x y : L}
    (hx : IsNilpotent (ad R L x)) (hxy : ⁅x, y⁆ = 0) :
    killingForm R L x y = 0 :=
  traceForm_eq_zero_of_isNilpotent_of_lie_eq_zero hx hxy

/-- **An ad-nilpotent element is Killing-isotropic**, the case `y = x` of
`TauCeti.killingForm_eq_zero_of_isNilpotent_ad_of_lie_eq_zero`. -/
theorem killingForm_self_eq_zero_of_isNilpotent_ad {x : L} (hx : IsNilpotent (ad R L x)) :
    killingForm R L x x = 0 :=
  killingForm_eq_zero_of_isNilpotent_ad_of_lie_eq_zero hx (lie_self x)

end KillingForm

section Orthogonal

variable {R L : Type*} [CommRing R] [LieRing L] [LieAlgebra R L]

/-- **The centraliser of `x` is Killing-orthogonal to the range of `ad x`.**  This half of
`TauCeti.orthogonal_range_ad_eq_ker_ad` is pure invariance of the Killing form and needs no
nondegeneracy. -/
theorem ker_ad_le_orthogonal_range_ad (x : L) :
    LinearMap.ker (ad R L x) ≤ (killingForm R L).orthogonal (LinearMap.range (ad R L x)) := by
  intro y hy
  rw [LinearMap.mem_ker, ad_apply] at hy
  rintro - ⟨z, rfl⟩
  rw [ad_apply, traceForm_apply_lie_apply' R L L x z y, hy, map_zero, neg_zero]

variable [LieAlgebra.IsKilling R L]

/-- **The Killing-orthogonal complement of the range of `ad x` is the centraliser of `x`.**
Invariance turns `κ ⁅x, z⁆ y = 0` for all `z` into `κ ⁅x, y⁆ z = 0` for all `z`, and nondegeneracy
then forces `⁅x, y⁆ = 0`. -/
theorem orthogonal_range_ad_eq_ker_ad (x : L) :
    (killingForm R L).orthogonal (LinearMap.range (ad R L x)) = LinearMap.ker (ad R L x) := by
  refine le_antisymm (fun y hy ↦ ?_) (ker_ad_le_orthogonal_range_ad x)
  rw [LinearMap.mem_ker, ad_apply]
  refine (LieAlgebra.IsKilling.killingForm_nondegenerate R L).1 _ fun z ↦ ?_
  have h := hy (ad R L x z) ⟨z, rfl⟩
  rw [ad_apply, traceForm_apply_lie_apply' R L L x z y, neg_eq_zero,
    LieModule.traceForm_comm] at h
  exact h

end Orthogonal

section Killing

variable {K L : Type*} [Field K] [LieRing L] [LieAlgebra K L] [FiniteDimensional K L]
  [LieAlgebra.IsKilling K L]

/-- **The range of `ad x` is the Killing-orthogonal complement of the centraliser of `x`.**  This
is `TauCeti.orthogonal_range_ad_eq_ker_ad` read backwards through the double orthogonal complement
of a nondegenerate symmetric form on a finite-dimensional space. -/
theorem range_ad_eq_orthogonal_ker_ad (x : L) :
    LinearMap.range (ad K L x) = (killingForm K L).orthogonal (LinearMap.ker (ad K L x)) := by
  rw [← orthogonal_range_ad_eq_ker_ad x,
    LinearMap.BilinForm.orthogonal_orthogonal (LieAlgebra.IsKilling.killingForm_nondegenerate K L)
      (LieModule.traceForm_isSymm K L L).isRefl]

/-- **An ad-nilpotent element of a Killing Lie algebra lies in the range of its own adjoint
action.**  It is Killing-orthogonal to its centraliser by
`TauCeti.killingForm_eq_zero_of_isNilpotent_ad_of_lie_eq_zero`, and that orthogonal complement is
the range of `ad x`. -/
theorem mem_range_ad_self_of_isNilpotent_ad {x : L} (hx : IsNilpotent (ad K L x)) :
    x ∈ LinearMap.range (ad K L x) := by
  rw [range_ad_eq_orthogonal_ker_ad]
  intro z hz
  rw [LinearMap.mem_ker, ad_apply] at hz
  rw [LieModule.traceForm_comm]
  exact killingForm_eq_zero_of_isNilpotent_ad_of_lie_eq_zero hx hz

/-- **An ad-nilpotent element of a Killing Lie algebra is a bracket with itself**: there is a
`t : L` with `⁅x, t⁆ = x`.

This is the step that lets Hochschild's strengthening of Ado's theorem pass from ad-nilpotence of
a semisimple component to the solvable subalgebra spanned by `x` and `t`, with no algebraically
closed field and no `sl₂`-triple. -/
theorem exists_lie_eq_self_of_isNilpotent_ad {x : L} (hx : IsNilpotent (ad K L x)) :
    ∃ t : L, ⁅x, t⁆ = x := by
  obtain ⟨t, ht⟩ := mem_range_ad_self_of_isNilpotent_ad hx
  exact ⟨t, by rwa [ad_apply] at ht⟩

/-- **An ad-nilpotent element of a Killing Lie algebra is an eigenvector of some `ad t` for the
eigenvalue `-1`**, the skew form of `TauCeti.exists_lie_eq_self_of_isNilpotent_ad`. -/
theorem exists_lie_eq_neg_self_of_isNilpotent_ad {x : L} (hx : IsNilpotent (ad K L x)) :
    ∃ t : L, ⁅t, x⁆ = -x := by
  obtain ⟨t, ht⟩ := exists_lie_eq_self_of_isNilpotent_ad hx
  exact ⟨t, by rw [← lie_skew, ht]⟩

end Killing

end TauCeti
