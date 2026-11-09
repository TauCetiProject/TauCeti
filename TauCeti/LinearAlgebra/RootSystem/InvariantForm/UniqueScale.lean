/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.QuadraticForm.Basic
public import Mathlib.LinearAlgebra.RootSystem.Finite.Nondegenerate
public import Mathlib.LinearAlgebra.RootSystem.Irreducible
public import TauCeti.LinearAlgebra.RootSystem.InvariantForm.Basic

/-!
# Invariant forms on an irreducible root pairing differ by a scalar

On an irreducible root pairing an invariant form is determined by its value on a single root: if
`C (α, α) = c * B (α, α)` for one root `α`, then `C = c • B`. Indeed the coroot normalisation
`2 ⟨x, α⟩ = ⟨x, α^∨⟩ ⟨α, α⟩` of `RootPairing.InvariantForm.two_mul_apply_root` puts `α` in the
radical of `C - c • B`, this radical is stable under the reflections, and irreducibility then makes
it the whole space.

Over a field the scalar exists and is unique. Over a linearly ordered field, two positive-definite
invariant forms differ by a unique positive scalar, and the positive-definite invariant forms of a
finite irreducible root system are exactly the positive multiples of its canonical root form.
Neither finiteness, reducedness nor crystallographicity is needed for the scalar itself, so the
non-reduced rank-one pairing with roots `±1, ±2` is covered.

This is the rigidity on a single irreducible component behind the description of the invariant
metrics of a general root system by one positive scale per component.

## Main results

* `RootPairing.InvariantForm.form_eq_smul_of_apply_root_root_eq`: an invariant form is determined by
  its value on one root.
* `RootPairing.InvariantForm.existsUnique_form_eq_smul`: over a field, two invariant forms differ by
  a unique scalar.
* `RootPairing.invariantMetric_unique_scale`: two positive-definite invariant forms differ by a
  unique positive scalar.
* `RootPairing.rootForm_posDef`: the canonical root form of a finite root system is positive
  definite over a linearly ordered field.
* `RootPairing.InvariantForm.form_toQuadraticMap_posDef_iff`: the positive-definite invariant forms
  are the positive multiples of the canonical root form.

## References

* J. S. Milne, *Algebraic Groups*, Cambridge University Press, 2017, Appendix C(g), which treats the
  reduced crystallographic case.
-/

public section

namespace RootPairing

variable {ι R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N]
  [Module R N] {P : RootPairing ι R M N}

/-- A root system on a nontrivial module has a root. -/
lemma nonempty_of_isRootSystem [Nontrivial M] (P : RootPairing ι R M N) [P.IsRootSystem] :
    Nonempty ι := by
  by_contra! h
  have hspan := IsRootSystem.span_root_eq_top (P := P)
  rw [Set.range_eq_empty, Submodule.span_empty] at hspan
  exact bot_ne_top hspan

namespace InvariantForm

/-- **An invariant form on an irreducible root pairing is determined by its value on one root.**
If `C (α, α) = c * B (α, α)` for one root `α`, then `C = c • B`. -/
theorem form_eq_smul_of_apply_root_root_eq [IsDomain R] [NeZero (2 : R)] [P.IsIrreducible]
    (B C : P.InvariantForm) (i : ι) {c : R}
    (hc : C.form (P.root i) (P.root i) = c * B.form (P.root i) (P.root i)) :
    C.form = c • B.form := by
  let D : LinearMap.BilinForm R M := C.form - c • B.form
  have hD (x y : M) : D x y = C.form x y - c * B.form x y := by simp [D]
  -- The root `α` is in the radical of `D`, by the coroot normalisation for `B` and `C`.
  have hroot (x : M) : D x (P.root i) = 0 := by
    refine (mul_eq_zero.mp ?_).resolve_left (two_ne_zero (α := R))
    rw [hD]
    linear_combination C.two_mul_apply_root x i - c * B.two_mul_apply_root x i +
      P.coroot' i x * hc
  have hinv (j : ι) (x y : M) : D (P.reflection j x) (P.reflection j y) = D x y := by
    simp [hD]
  -- So the radical is a nonzero reflection-invariant submodule, and hence everything.
  have htop : LinearMap.ker D.flip = ⊤ := by
    refine IsIrreducible.eq_top_of_invtSubmodule_reflection (P := P) _ (fun j x hx ↦ ?_) ?_
    · ext y
      have hx' : D (P.reflection j y) x = 0 := LinearMap.congr_fun (LinearMap.mem_ker.mp hx) _
      rw [← hinv j (P.reflection j y) x, P.reflection_same] at hx'
      simpa using hx'
    · refine (Submodule.ne_bot_iff _).mpr ⟨P.root i, LinearMap.mem_ker.mpr ?_, P.ne_zero i⟩
      ext x
      simpa using hroot x
  have hzero : D = 0 := by
    ext x y
    simpa using LinearMap.congr_fun₂ (LinearMap.ker_eq_top.mp htop) y x
  exact sub_eq_zero.mp hzero

/-- **Two invariant forms on an irreducible root pairing over a field differ by a unique scalar.**
The hypothesis `Nonempty ι` excludes the rootless case, where the zero form is invariant. -/
theorem existsUnique_form_eq_smul {K : Type*} [Field K] [NeZero (2 : K)] [Module K M] [Module K N]
    {P : RootPairing ι K M N} [P.IsIrreducible] [Nonempty ι] (B C : P.InvariantForm) :
    ∃! c : K, C.form = c • B.form := by
  obtain ⟨i⟩ := ‹Nonempty ι›
  have hi := B.ne_zero i
  refine ⟨C.form (P.root i) (P.root i) / B.form (P.root i) (P.root i),
    form_eq_smul_of_apply_root_root_eq B C i (by field_simp), fun c hc ↦ ?_⟩
  rw [hc]
  simp [hi]

end InvariantForm

section LinearOrderedField

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K] [Module K M] [Module K N]

/-- **Two positive-definite invariant forms on an irreducible root system differ by a unique
positive scalar.** -/
theorem invariantMetric_unique_scale (P : RootPairing ι K M N) [P.IsRootSystem] [P.IsIrreducible]
    (B C : P.InvariantForm) (hB : B.form.toQuadraticMap.PosDef)
    (hC : C.form.toQuadraticMap.PosDef) :
    ∃! c : K, 0 < c ∧ C.form = c • B.form := by
  have := IsIrreducible.nontrivial P
  obtain ⟨i⟩ := P.nonempty_of_isRootSystem
  have : Nonempty ι := ⟨i⟩
  obtain ⟨c, hc, huniq⟩ := InvariantForm.existsUnique_form_eq_smul B C
  refine ⟨c, ⟨?_, hc⟩, fun d hd ↦ huniq d hd.2⟩
  have hBi : 0 < B.form (P.root i) (P.root i) := hB _ (P.ne_zero i)
  have hCi : 0 < C.form (P.root i) (P.root i) := hC _ (P.ne_zero i)
  rw [hc] at hCi
  simpa [hBi] using hCi

/-- The canonical root form of a finite root system over a linearly ordered field is positive
definite. -/
lemma rootForm_posDef [Fintype ι] (P : RootPairing ι K M N) [P.IsRootSystem] :
    P.RootForm.toQuadraticMap.PosDef :=
  fun _ hx ↦ P.rootForm_pos_of_ne_zero (by simp) hx

/-- **The positive-definite invariant forms of a finite irreducible root system are exactly the
positive multiples of the canonical root form.** -/
theorem InvariantForm.form_toQuadraticMap_posDef_iff [Fintype ι]
    {P : RootPairing ι K M N} [P.IsRootSystem] [P.IsIrreducible] (B : P.InvariantForm) :
    B.form.toQuadraticMap.PosDef ↔ ∃ c : K, 0 < c ∧ B.form = c • P.RootForm := by
  refine ⟨fun hB ↦ ?_, fun ⟨c, hc, hB⟩ x hx ↦ ?_⟩
  · exact (invariantMetric_unique_scale P P.toInvariantForm B P.rootForm_posDef hB).exists
  · rw [hB]
    simpa using mul_pos hc (P.rootForm_posDef x hx)

end LinearOrderedField

end RootPairing
