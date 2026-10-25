/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Mathlib.RingTheory.Discriminant
public import TauCeti.RingTheory.NormTrace.Pi

/-!
# Nondegeneracy of trace forms

Nondegeneracy of the trace form `Algebra.traceForm K B` is invariant under algebra isomorphisms,
holds on a finite product exactly when it holds on every factor, and forces `B` to be reduced when
the base ring is reduced. These are the inputs that reduce the trace-form criterion
for étaleness over a field to finite separable field extensions.

## Main results

* `TauCeti.Algebra.traceForm_nondegenerate_congr`: nondegeneracy of the trace form is invariant
  under algebra isomorphisms.
* `TauCeti.Algebra.traceForm_pi_nondegenerate_iff`: the trace form of a finite product is
  nondegenerate iff the trace form of every factor is.
* `TauCeti.Algebra.discr_ne_zero_iff_traceForm_nondegenerate`: over a domain, the discriminant of
  a basis is nonzero iff the trace form is nondegenerate.
* `TauCeti.Algebra.isReduced_of_traceForm_nondegenerate`: an algebra over a reduced ring with
  nondegenerate trace form is reduced.

## References

* Ported from T. Dupuy, T. Tucker and Z. Wang,
  [pcfawd-formalization](https://github.com/tdupu/pcfawd-formalization) at commit
  `9a20b3f351446d64e6015d704198bc71c7002008` (Apache-2.0),
  `lean/Pcf/Stacks/Purity/DiscriminantFiber.lean` and
  `lean/Pcf/Stacks/Purity/DiscriminantGlobal.lean`, namespace `Pcf.Stacks`:
  `traceForm_nondegenerate_congr` is its `Algebra.traceForm_nondegenerate_of_algEquiv`;
  `traceForm_pi_nondegenerate_iff` combines its `Algebra.traceForm_pi_nondegenerate` and
  `Algebra.traceForm_pi_nondegenerate_factors`; `isReduced_of_traceForm_nondegenerate` is the
  trace-pairing step of its `Algebra.isReduced_of_discr_ne_zero_of_basis`; and the source proves
  `discr_ne_zero_iff_traceForm_nondegenerate` inline (in its
  `Algebra.discr_ne_zero_of_formallyEtale_of_basis`).
-/

public section

namespace TauCeti

variable {K : Type*} [CommRing K]

section AlgEquiv

variable {S T : Type*} [CommRing S] [CommRing T] [Algebra K S] [Algebra K T]

/-- Nondegeneracy of the trace form is invariant under algebra isomorphisms. -/
theorem Algebra.traceForm_nondegenerate_congr (e : S ≃ₐ[K] T) :
    (Algebra.traceForm K S).Nondegenerate ↔ (Algebra.traceForm K T).Nondegenerate := by
  have htrace : Algebra.traceForm K S =
      LinearMap.BilinForm.congr e.symm.toLinearEquiv (Algebra.traceForm K T) := by
    ext x y
    simp [Algebra.traceForm_apply, ← map_mul, Algebra.trace_eq_of_algEquiv]
  rw [htrace, LinearMap.BilinForm.nondegenerate_congr_iff]

end AlgEquiv

/-- The trace form of a finite product of finite free algebras is nondegenerate iff the trace form
of every factor is. -/
@[simp]
theorem Algebra.traceForm_pi_nondegenerate_iff {ι : Type*} [Finite ι] (L : ι → Type*)
    [∀ i, CommRing (L i)] [∀ i, Algebra K (L i)] [∀ i, Module.Free K (L i)]
    [∀ i, Module.Finite K (L i)] :
    (Algebra.traceForm K (∀ i, L i)).Nondegenerate ↔
      ∀ i, (Algebra.traceForm K (L i)).Nondegenerate := by
  classical
  have := Fintype.ofFinite ι
  have hsum (x y : ∀ i, L i) :
      Algebra.traceForm K (∀ i, L i) x y = ∑ i, Algebra.traceForm K (L i) (x i) (y i) := by
    simp [Algebra.traceForm_apply, Algebra.trace_pi]
  have hsingle (x : ∀ i, L i) (i : ι) (z : L i) :
      Algebra.traceForm K (∀ i, L i) x (Pi.single i z) = Algebra.traceForm K (L i) (x i) z := by
    rw [hsum, Finset.sum_eq_single i]
    · simp
    · intro j _ hj
      simp [Pi.single_eq_of_ne hj]
    · simp
  have hleft (i : ι) : (Algebra.traceForm K (L i)).Nondegenerate ↔
      (Algebra.traceForm K (L i)).SeparatingLeft :=
    LinearMap.IsRefl.nondegenerate_iff_separatingLeft (Algebra.traceForm_isSymm K).isRefl
  refine (LinearMap.IsRefl.nondegenerate_iff_separatingLeft
    (Algebra.traceForm_isSymm (R := K) (S := ∀ i, L i)).isRefl).trans
      ((Iff.trans ?_ (forall_congr' hleft).symm))
  constructor
  · intro h i z hz
    have hzero : (Pi.single i z : ∀ i, L i) = 0 := by
      refine h _ fun y ↦ ?_
      rw [(Algebra.traceForm_isSymm K).eq, hsingle, (Algebra.traceForm_isSymm K).eq]
      exact hz (y i)
    simpa using congr_fun hzero i
  · intro h x hx
    funext i
    exact h i (x i) fun z ↦ by rw [← hsingle]; exact hx _

/-- An algebra over a reduced ring with nondegenerate trace form is reduced. -/
theorem Algebra.isReduced_of_traceForm_nondegenerate {B : Type*} [IsReduced K] [CommRing B]
    [Algebra K B] (h : (Algebra.traceForm K B).Nondegenerate) : IsReduced B := by
  refine ⟨fun x hx ↦ h.1 x fun y ↦ ?_⟩
  rw [Algebra.traceForm_apply]
  exact (Algebra.isNilpotent_trace_of_isNilpotent
    ((Commute.all x y).isNilpotent_mul_right hx)).eq_zero

/-- The discriminant of a basis of a finite free algebra over a domain is nonzero iff the trace
form is nondegenerate. -/
theorem Algebra.discr_ne_zero_iff_traceForm_nondegenerate {F B ι : Type*} [CommRing F]
    [IsDomain F] [CommRing B] [Algebra F B] [Fintype ι] [DecidableEq ι] (b : Module.Basis ι F B) :
    Algebra.discr F b ≠ 0 ↔ (Algebra.traceForm F B).Nondegenerate := by
  rw [LinearMap.BilinForm.nondegenerate_iff_det_ne_zero b, ← Algebra.traceMatrix_of_basis,
    Algebra.discr_def]

end TauCeti
