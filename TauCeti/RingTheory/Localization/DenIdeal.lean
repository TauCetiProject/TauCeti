/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Ideal.Colon
public import Mathlib.RingTheory.Localization.FractionRing

/-!
# The denominator ideal of an element of an algebra

For `x` in an `R`-algebra `K`, the denominator ideal `Algebra.denIdeal K x` is the colon ideal
`(R : x) = {r : R | r • x ∈ R}` — the `r` that clear the denominator of `x`. When `K` is a
localization of a nontrivial ring `R` it is nonzero (`Algebra.denIdeal_ne_bot`), because any
expression of `x` as a fraction exhibits a denominator in it.

This is general commutative algebra. Over a Dedekind domain it is used to show that every ideal
of a ring of `S`-integers is extended from the base, and to find common denominators coprime to a
given ideal; it also describes the points of a field not lying in a local subring.

Split out of material adapted from Michael Stoll's elliptic-curves formalisation
(`github.com/MichaelStollBayreuth/EllipticCurves`, `EllipticCurves/Mathlib/SIntegers.lean` at
commit `66889eada51a`, Apache 2.0, by Michael Stoll).
-/

public section

variable {R : Type*} [CommSemiring R]

section Semiring

variable (K : Type*) [Semiring K] [Algebra R K]

/-- The denominator ideal of `x : K`: the colon ideal `(R : x) = {r : R | r • x ∈ R}`.

It is an opaque `def` rather than an `abbrev` so that `simp` cannot rewrite through it with
`Submodule.mem_colon_singleton` before `mem_denIdeal_iff` fires; membership is accessed
through that lemma throughout, and the colon-ideal description through `denIdeal_def`. -/
def Algebra.denIdeal (x : K) : Ideal R := (1 : Submodule R K).colon {x}

/-- The defining equality of `Algebra.denIdeal`, exported because the definition is opaque:
consumers reaching for colon-ideal operations rewrite with this, while `mem_denIdeal_iff`
remains the membership normal form. Not a `simp` lemma — rewriting with it would undo
`mem_denIdeal_iff`. -/
lemma Algebra.denIdeal_def (x : K) :
    Algebra.denIdeal K x = (1 : Submodule R K).colon {x} :=
  (rfl)

/-- Membership in the denominator ideal: `r` clears `x` into the image of `R`, in the sense that
`r * x` is the image of some `s : R`. -/
@[simp] lemma Algebra.mem_denIdeal_iff {x : K} {r : R} :
    r ∈ Algebra.denIdeal K x ↔ ∃ s : R, algebraMap R K r * x = algebraMap R K s := by
  rw [Algebra.denIdeal, Submodule.mem_colon_singleton, Algebra.smul_def, Submodule.mem_one]
  exact exists_congr fun s ↦ eq_comm

end Semiring

section CommSemiring

variable (K : Type*) [CommSemiring K] [Algebra R K]

/-- The denominator ideal of an element of a localization of a nontrivial ring is nonzero: a
denominator witnessing the element as a fraction lies in it. (When `0 ∈ M` the localization is
trivial and the denominator ideal is all of `R`.) -/
lemma Algebra.denIdeal_ne_bot [Nontrivial R] (M : Submonoid R) [IsLocalization M K] (x : K) :
    Algebra.denIdeal K x ≠ (⊥ : Ideal R) := by
  obtain ⟨⟨a, b⟩, hab⟩ := IsLocalization.surj M x
  intro h0
  have hb : (b : R) ∈ Algebra.denIdeal K x :=
    (Algebra.mem_denIdeal_iff K).2 ⟨a, by rw [mul_comm, hab]⟩
  rw [h0, Ideal.mem_bot] at hb
  have := IsLocalization.uniqueOfZeroMem (M := M) (S := K) (hb ▸ b.2)
  have h1 : (1 : R) ∈ Algebra.denIdeal K x :=
    (Algebra.mem_denIdeal_iff K).2 ⟨0, Subsingleton.elim _ _⟩
  simp [h0] at h1

end CommSemiring

end
