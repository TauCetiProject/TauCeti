/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.DG.Algebra.Defs

/-!
# Twisting cocycles over a differential graded algebra

A **twisting cocycle** on a finite set `P` of generators graded by `ind : P → ℤ`, with values in a
differential graded algebra `(𝒜, d)`, is a matrix `m : P → P → A` of homogeneous elements which
satisfies the twisting equation

`d (m x y) = Σ_z (-1) ^ (ind x - ind z) • (m x z * m z y)`

and the one-sidedness condition `m x y = 0` whenever `ind x ≤ ind y`.  It is the Barraud–Cornea
structure that the compactified trajectory spaces of a Morse or Floer theory produce, by evaluating
their fundamental chains into chains on a loop space, and it is the only input of the twisted
complex `𝓕 ⊗ ⟨P⟩` of `TauCeti.Algebra.Homology.DG.Twisted.Complex`.

The source works with homological gradings, where `m x y` has degree `ind x - ind y - 1`.  Tau
Ceti's differential graded algebras are cohomologically graded, and the bridge `C^{-n} = C_n` puts
`m x y` in cohomological degree `ind y - ind x + 1`.  The twisting equation itself carries no
grading and is stated verbatim.

The one-sidedness condition is part of the data.  It does not follow from the degree and the
twisting equation over an arbitrary differential graded algebra: over `ℚ[ε]/(ε²)` with `ε` in
cohomological degree `1` and `d = 0`, one generator `x` with `m x x = ε` satisfies both.  It is
automatic over a cohomologically nonpositive algebra, since then the degree `ind y - ind x + 1` is
positive when `ind x ≤ ind y` (`TauCeti.TwistingCocycle.one_sided_of_nonpos`).  The cubical chains
on a loop space are cohomologically nonpositive, so for every geometric cocycle the condition is a
lemma.

## Main definitions

* `TauCeti.TwistingCocycle`: the structure, with fields `mem_graded`, `twisting` and `one_sided`.
* `TauCeti.TwistingCocycle.ofNonpos`: a twisting cocycle over a cohomologically nonpositive
  algebra, from the graded matrix and the twisting equation alone.

## Main results

* `TauCeti.TwistingCocycle.one_sided_of_nonpos`: over a cohomologically nonpositive algebra, the
  degree condition alone forces one-sidedness.
* `TauCeti.TwistingCocycle.m_self`: the diagonal of a twisting cocycle vanishes.

## References

* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Floer homology with DG coefficients.
  Applications to cotangent bundles*, arXiv:2404.07953, Definition 1.9.
* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Morse homology with differential graded
  coefficients*, Progress in Mathematics 360, Birkhäuser, 2025, Chapter 3.
* J.-F. Barraud, O. Cornea, *Lagrangian intersections and the Serre spectral sequence*, Ann. of
  Math. 166 (2007).
-/

public section

namespace TauCeti

universe uR uA uP

variable {R : Type uR} {A : Type uA} [CommRing R] [Ring A] [Algebra R A]

/-- A **twisting cocycle** with values in the differential graded algebra `(𝒜, d)`, on the finite
set `P` of generators graded by `ind`.  The entry `m x y` is the coefficient of `y` in the twisted
differential of `x`.  It is homogeneous of cohomological degree `ind y - ind x + 1`, the matrix
satisfies the twisting equation `d (m x y) = Σ_z (-1) ^ (ind x - ind z) • (m x z * m z y)`, and it
is strictly upper triangular for the order by `ind`: `m x y = 0` whenever `ind x ≤ ind y`. -/
structure TwistingCocycle (𝒜 : ℤ → Submodule R A) (d : A →ₗ[R] A) (P : Type uP) [Fintype P]
    (ind : P → ℤ) where
  /-- The coefficient of `y` in the twisted differential of `x`. -/
  m : P → P → A
  /-- Each entry is homogeneous, of cohomological degree `ind y - ind x + 1`. -/
  mem_graded : ∀ x y, m x y ∈ 𝒜 (ind y - ind x + 1)
  /-- The twisting equation, in the source's homological sign convention. -/
  twisting : ∀ x y, d (m x y) = ∑ z, (ind x - ind z).negOnePow • (m x z * m z y)
  /-- One-sidedness: the matrix is strictly upper triangular for the order by `ind`. -/
  one_sided : ∀ x y, ind x ≤ ind y → m x y = 0

namespace TwistingCocycle

variable {𝒜 : ℤ → Submodule R A} {d : A →ₗ[R] A} {P : Type uP} [Fintype P] {ind : P → ℤ}

@[ext]
theorem ext {m₁ m₂ : TwistingCocycle 𝒜 d P ind} (h : ∀ x y, m₁.m x y = m₂.m x y) : m₁ = m₂ := by
  cases m₁; cases m₂
  congr
  funext x y
  exact h x y

/-- The diagonal of a twisting cocycle vanishes. -/
@[simp]
theorem m_self (m : TwistingCocycle 𝒜 d P ind) (x : P) : m.m x x = 0 :=
  m.one_sided x x le_rfl

/-- Entries below or on the diagonal vanish. -/
theorem m_eq_zero_of_le (m : TwistingCocycle 𝒜 d P ind) {x y : P} (hxy : ind x ≤ ind y) :
    m.m x y = 0 :=
  m.one_sided x y hxy

/-- The zero matrix is a twisting cocycle: both sides of the twisting equation vanish. -/
instance : Zero (TwistingCocycle 𝒜 d P ind) where
  zero :=
    { m := fun _ _ ↦ 0
      mem_graded := fun _ _ ↦ Submodule.zero_mem _
      twisting := fun _ _ ↦ by simp
      one_sided := fun _ _ _ ↦ rfl }

@[simp]
theorem zero_m (x y : P) : (0 : TwistingCocycle 𝒜 d P ind).m x y = 0 :=
  rfl

omit [Fintype P] in
/-- Over a cohomologically nonpositive algebra, the degree condition alone forces one-sidedness:
an entry `m x y` with `ind x ≤ ind y` lives in a positive degree, where the algebra vanishes.  This
is the situation of the cubical chains on a loop space.  No differential and no twisting equation
is involved. -/
theorem one_sided_of_nonpos (m : P → P → A) (hm : ∀ x y, m x y ∈ 𝒜 (ind y - ind x + 1))
    (h𝒜 : ∀ n, 0 < n → 𝒜 n = ⊥) : ∀ x y, ind x ≤ ind y → m x y = 0 := by
  intro x y hxy
  have h := hm x y
  rw [h𝒜 _ (by omega)] at h
  exact (Submodule.mem_bot R).1 h

/-- A twisting cocycle over a cohomologically nonpositive algebra, from the graded matrix and the
twisting equation alone: one-sidedness is supplied by `one_sided_of_nonpos`. -/
def ofNonpos (m : P → P → A) (hm : ∀ x y, m x y ∈ 𝒜 (ind y - ind x + 1))
    (ht : ∀ x y, d (m x y) = ∑ z, (ind x - ind z).negOnePow • (m x z * m z y))
    (h𝒜 : ∀ n, 0 < n → 𝒜 n = ⊥) : TwistingCocycle 𝒜 d P ind where
  m := m
  mem_graded := hm
  twisting := ht
  one_sided := one_sided_of_nonpos m hm h𝒜

@[simp]
theorem ofNonpos_m (m : P → P → A) (hm : ∀ x y, m x y ∈ 𝒜 (ind y - ind x + 1))
    (ht : ∀ x y, d (m x y) = ∑ z, (ind x - ind z).negOnePow • (m x z * m z y))
    (h𝒜 : ∀ n, 0 < n → 𝒜 n = ⊥) : (ofNonpos m hm ht h𝒜).m = m := by
  rw [ofNonpos]

end TwistingCocycle

end TauCeti
