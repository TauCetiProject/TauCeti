/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Span.Defs
public import TauCeti.LinearAlgebra.Matrix.GramSize.Basic
public import TauCeti.LinearAlgebra.Matrix.IndefiniteUnitaryGroup
import Mathlib.Tactic.Module
import TauCeti.Algebra.Star.SelfAdjoint
import TauCeti.LinearAlgebra.Matrix.DotProduct

/-!
# Lengths of vectors at points of a unitary group, and their comparison at two points

Let `S` be a size for the Gram matrix `J` of a sesquilinear form `⟨v, w⟩ = star v ⬝ᵥ J *ᵥ w` on
`ι → A` (`TauCeti.GramSize`), and let `e₀, e₁, …` be a family of vectors (in the application,
the basis vectors of an isotropic flag). For `l : ℕ`, a vector `ω` is *orthogonal below `l`* if
`⟨e_b, ω⟩ = 0` for `b < l`, and two vectors are *congruent below `l`* if they differ by an element
of the span of the `e_b`, `b < l`; the classes of the vectors orthogonal below `l` form the
quotient `Y^(l)` along the flag.

A size has no scale of its own; the phrase *length at most `L ^ i`* is informal notation for
size `i`, so named because for the size `TauCeti.GramSize.ofNorm L` at a real place, size `i`
means norm at most `L ^ i`. The exponents below are sizes in this sense.

* A vector `y` has **length at most `L ^ i` at `g`** if `g⁻¹ y` has size `i`
  (`TauCeti.GramSize.LengthLeAt`); its class in `Y^(l)` has **induced length at most `L ^ i`** if
  some vector congruent to `y` below `l` does (`TauCeti.GramSize.InducedLengthLe`).
* For a unit `ρ` and two invertible matrices `g` and `g'`, a vector `ω`, read at `g`, **agrees
  modulo `ρ` up to size `i` with a lift of its class in `Y^(l)` read at `g'`** if
  `(g⁻¹ ω - g'⁻¹ ω') / ρ` has size `i` for some `ω'` congruent to `ω` below `l`
  (`TauCeti.GramSize.AgreesWithLift`). The **lengths at `g` and `g'` differ by at most `L ^ t` on
  `Y^(l)` modulo `ρ`** if every vector orthogonal below `l` of length at most `L ^ i` at `g` agrees
  in this way up to size `i + t` (`TauCeti.GramSize.LengthsDifferLe`).
* The vector `e_a` **has a short dual of exponent `c`** for `(g, g')` modulo `ρ` if some dual `ζ`
  of `e_a` (orthogonal below `a`, with `⟨e_a, ζ⟩ = 1`) has length at most `L ^ c` at `g` and agrees
  modulo `ρ` up to size `c` with a lift of its class in `Y^(a)` read at `g'`
  (`TauCeti.GramSize.HasShortDual`).

The first two results compare the lengths at two points `g` and `g'` of the unitary group of a
Hermitian form, for a self-adjoint unit `ρ` of size `1`:

* if `e_b` is orthogonal to `e_0, …, e_a` for every `b < a`, the class of `e_a` in `Y^(a)` has
  induced length at most `L ^ c` at `g` and at `g'`, `e_a` has a short dual of exponent `c`, and
  the lengths differ by at most `L ^ t` on `Y^(a + 1)`, then they differ by at most
  `L ^ (t + 4c + 12)` on `Y^(a)` (`TauCeti.GramSize.LengthsDifferLe.of_succ`);
* by induction, if `⟨e_b, e_b'⟩ = 0` for all `b, b' < j` (the `e_b`, `b < j`, span a totally
  isotropic subspace), the hypotheses on the class and the dual of `e_a` hold for every
  `a < j`, and the lengths differ by at most `L ^ t` on `Y^(j)`, then they differ by at most
  `L ^ (t + (4c + 12) j)` on the whole space `Y^(0)`
  (`TauCeti.GramSize.LengthsDifferLe.zero_of_hasShortDual`).

The third holds for any invertible Gram matrix `J` and self-adjoint unit `ρ`:

* if the lengths at `g` and `g x` differ by at most `L ^ i` on the whole space, for `x` in the
  unitary group, then `(x - 1) / ρ` has size `i + 4`
  (`TauCeti.GramSize.LengthsDifferLe.smul_sub_one_mem_matsOfSize`): `x` is close to `1`.

The proof of the first statement splits a vector `ω` orthogonal below `a` as
`ω = ω₀ + ⟨e_a, ω⟩ ζ` along the dual `ζ`, with `ω₀` orthogonal below `a + 1`. The component `ω₀`
is compared by hypothesis; its lift `ω₀'` is congruent to `ω₀` only below `a + 1`, and its
coefficient along `e_a`, read off by the dual, is replaced by a short representative of `e_a` at
`g'`. The coefficient `⟨e_a, ω⟩` is the value of the form at `g⁻¹` of a short representative of
`e_a` and `g⁻¹ ω`, which bounds its size.

These estimates compare orbital integrals of Bessel functions at two points of a unitary group
with a Bessel subgroup, in the analysis of second moments of Poincaré series.

## Provenance

The definitions and the three comparison statements follow the Lean project grh-lean
(https://github.com/lsernau/grh-lean, Apache 2.0, Copyright 2026 Anthropic, PBC), files
`src/New/Spanning/Frames/Lengths.lean` (`New.Floors.Size.LengthLeAt`,
`New.Floors.Size.InducedLengthLe`, `New.Floors.Size.GaugesDifferLe`,
`New.Floors.Size.HasShortDual`) and `src/New/Spanning/Frames/TwoGauges.lean`
(`New.Floors.Size.GaugesDifferLe.of_succ`,
`New.Floors.Size.GaugesDifferLe.on_whole_space_of_hasShortDual`,
`New.Floors.Size.GaugesDifferLe.hasMatrixSize_sub_one`). Here the flag is any family of vectors
with the isotropy used by the proof, and the points need only be invertible in the definitions.
-/

public section

open Matrix

namespace TauCeti

namespace GramSize

variable {ι A : Type*} [Fintype ι] [DecidableEq ι] [CommRing A] [StarRing A]
  {J : Matrix ι ι A} (S : GramSize J)

/-- A vector `y` has **length at most `L ^ i` at `g`** when `g⁻¹ y` has size `i`. Here `L ^ i` is
informal notation for size `i` (for `TauCeti.GramSize.ofNorm L`, the entries of `g⁻¹ y` have norm
at most `L ^ i`); a size has no scale `L` of its own. -/
def LengthLeAt (g : GL ι A) (i : ℕ) (y : ι → A) : Prop :=
  ((g⁻¹ : GL ι A) : Matrix ι ι A) *ᵥ y ∈ S.vecsOfSize i

/-- The class of `y` in the quotient `Y^(l)` along the flag `e` has **induced length at most
`L ^ i` at `g`** when some vector congruent to `y` modulo the span of the `e_b`, `b < l`, has
length at most `L ^ i` at `g`. -/
def InducedLengthLe (e : ℕ → ι → A) (l : ℕ) (g : GL ι A) (i : ℕ) (y : ι → A) : Prop :=
  ∃ y', y - y' ∈ Submodule.span A (e '' Set.Iio l) ∧ S.LengthLeAt g i y'

/-- A vector `ω`, read at `g`, **agrees modulo `ρ` up to size `i` with a lift of its class in
`Y^(l)` read at `g'`** when `(g⁻¹ ω - g'⁻¹ ω') / ρ` has size `i` for some `ω'` congruent to `ω`
modulo the span of the `e_b`, `b < l`. -/
def AgreesWithLift (e : ℕ → ι → A) (l : ℕ) (ρ : Aˣ) (g g' : GL ι A) (i : ℕ) (ω : ι → A) :
    Prop :=
  ∃ ω', ω - ω' ∈ Submodule.span A (e '' Set.Iio l) ∧
    ((ρ⁻¹ : Aˣ) : A) • (((g⁻¹ : GL ι A) : Matrix ι ι A) *ᵥ ω -
      ((g'⁻¹ : GL ι A) : Matrix ι ι A) *ᵥ ω') ∈ S.vecsOfSize i

/-- The **lengths at `g` and `g'` differ by at most `L ^ t` on `Y^(l)` modulo `ρ`**: every vector
orthogonal to the `e_b`, `b < l`, of length at most `L ^ i` at `g`, agrees modulo `ρ` up to size
`i + t` with a lift of its class in `Y^(l)` read at `g'`. -/
def LengthsDifferLe (e : ℕ → ι → A) (l : ℕ) (ρ : Aˣ) (g g' : GL ι A) (t : ℕ) : Prop :=
  ∀ (i : ℕ) (ω : ι → A), (∀ b < l, star (e b) ⬝ᵥ J *ᵥ ω = 0) → S.LengthLeAt g i ω →
    S.AgreesWithLift e l ρ g g' (i + t) ω

/-- The vector `e_a` **has a short dual of exponent `c` for `(g, g')` modulo `ρ`**: some dual `ζ`
of `e_a`, a vector orthogonal to the `e_b`, `b < a`, with `⟨e_a, ζ⟩ = 1`, has length at most
`L ^ c` at `g` and, read at `g`, agrees modulo `ρ` up to size `c` with a lift of its class in
`Y^(a)` read at `g'`. -/
def HasShortDual (e : ℕ → ι → A) (a : ℕ) (ρ : Aˣ) (g g' : GL ι A) (c : ℕ) : Prop :=
  ∃ ζ, (∀ b < a, star (e b) ⬝ᵥ J *ᵥ ζ = 0) ∧ star (e a) ⬝ᵥ J *ᵥ ζ = 1 ∧
    S.LengthLeAt g c ζ ∧ S.AgreesWithLift e a ρ g g' c ζ

variable {S}

theorem lengthLeAt_iff {g : GL ι A} {i : ℕ} {y : ι → A} :
    S.LengthLeAt g i y ↔ ((g⁻¹ : GL ι A) : Matrix ι ι A) *ᵥ y ∈ S.vecsOfSize i :=
  Iff.rfl

theorem inducedLengthLe_iff {e : ℕ → ι → A} {l : ℕ} {g : GL ι A} {i : ℕ} {y : ι → A} :
    S.InducedLengthLe e l g i y ↔
      ∃ y', y - y' ∈ Submodule.span A (e '' Set.Iio l) ∧ S.LengthLeAt g i y' :=
  Iff.rfl

theorem agreesWithLift_iff {e : ℕ → ι → A} {l : ℕ} {ρ : Aˣ} {g g' : GL ι A} {i : ℕ}
    {ω : ι → A} :
    S.AgreesWithLift e l ρ g g' i ω ↔ ∃ ω', ω - ω' ∈ Submodule.span A (e '' Set.Iio l) ∧
      ((ρ⁻¹ : Aˣ) : A) • (((g⁻¹ : GL ι A) : Matrix ι ι A) *ᵥ ω -
        ((g'⁻¹ : GL ι A) : Matrix ι ι A) *ᵥ ω') ∈ S.vecsOfSize i :=
  Iff.rfl

theorem lengthsDifferLe_iff {e : ℕ → ι → A} {l : ℕ} {ρ : Aˣ} {g g' : GL ι A} {t : ℕ} :
    S.LengthsDifferLe e l ρ g g' t ↔ ∀ (i : ℕ) (ω : ι → A),
      (∀ b < l, star (e b) ⬝ᵥ J *ᵥ ω = 0) → S.LengthLeAt g i ω →
        S.AgreesWithLift e l ρ g g' (i + t) ω :=
  Iff.rfl

theorem hasShortDual_iff {e : ℕ → ι → A} {a : ℕ} {ρ : Aˣ} {g g' : GL ι A} {c : ℕ} :
    S.HasShortDual e a ρ g g' c ↔ ∃ ζ, (∀ b < a, star (e b) ⬝ᵥ J *ᵥ ζ = 0) ∧
      star (e a) ⬝ᵥ J *ᵥ ζ = 1 ∧ S.LengthLeAt g c ζ ∧ S.AgreesWithLift e a ρ g g' c ζ :=
  Iff.rfl

/-! ### Raising the exponents -/

/-- A vector of length at most `L ^ i` at `g` has length at most `L ^ j` there for `i ≤ j`. -/
theorem LengthLeAt.mono {g : GL ι A} {i j : ℕ} {y : ι → A} (h : S.LengthLeAt g i y)
    (hij : i ≤ j) : S.LengthLeAt g j y :=
  S.mem_vecsOfSize_of_le h hij

/-- A vector of length at most `L ^ i` at `g` has a class of induced length at most `L ^ i`. -/
theorem LengthLeAt.inducedLengthLe {e : ℕ → ι → A} {l : ℕ} {g : GL ι A} {i : ℕ} {y : ι → A}
    (h : S.LengthLeAt g i y) : S.InducedLengthLe e l g i y :=
  ⟨y, by simp, h⟩

/-- Induced lengths increase with the exponent. -/
theorem InducedLengthLe.mono {e : ℕ → ι → A} {l : ℕ} {g : GL ι A} {i j : ℕ} {y : ι → A}
    (h : S.InducedLengthLe e l g i y) (hij : i ≤ j) : S.InducedLengthLe e l g j y :=
  let ⟨y', hy', hy'g⟩ := h
  ⟨y', hy', hy'g.mono hij⟩

/-- Agreement with a lift up to size `i` implies agreement up to every size `j ≥ i`. -/
theorem AgreesWithLift.mono {e : ℕ → ι → A} {l : ℕ} {ρ : Aˣ} {g g' : GL ι A} {i j : ℕ}
    {ω : ι → A} (h : S.AgreesWithLift e l ρ g g' i ω) (hij : i ≤ j) :
    S.AgreesWithLift e l ρ g g' j ω :=
  let ⟨ω', hω', hD⟩ := h
  ⟨ω', hω', S.mem_vecsOfSize_of_le hD hij⟩

/-- Lengths differing by at most `L ^ t` differ by at most `L ^ t'` for `t ≤ t'`. -/
theorem LengthsDifferLe.mono {e : ℕ → ι → A} {l : ℕ} {ρ : Aˣ} {g g' : GL ι A} {t t' : ℕ}
    (h : S.LengthsDifferLe e l ρ g g' t) (htt' : t ≤ t') : S.LengthsDifferLe e l ρ g g' t' :=
  fun i ω hω hωg => (h i ω hω hωg).mono (by omega)

/-- A short dual of exponent `c` is a short dual of every exponent `c' ≥ c`. -/
theorem HasShortDual.mono {e : ℕ → ι → A} {a : ℕ} {ρ : Aˣ} {g g' : GL ι A} {c c' : ℕ}
    (h : S.HasShortDual e a ρ g g' c) (hcc' : c ≤ c') : S.HasShortDual e a ρ g g' c' :=
  let ⟨ζ, hζ, hζa, hζg, hD⟩ := h
  ⟨ζ, hζ, hζa, hζg.mono hcc', hD.mono hcc'⟩

/-! ### Elementary facts about the form -/

section Form

omit [DecidableEq ι] in
/-- The difference of two values of the form at nearby vectors: with `D₁ = (u - u') / ρ` and
`D₂ = (v - v') / ρ`, `⟨u, v⟩ - ⟨u', v'⟩ = ρ (⟨D₁, v⟩ + ⟨u', D₂⟩)` for self-adjoint `ρ`. -/
private theorem star_dotProduct_mulVec_sub_eq {ρ : Aˣ} (hρ : IsSelfAdjoint (ρ : A))
    (u u' v v' : ι → A) :
    star u ⬝ᵥ J *ᵥ v - star u' ⬝ᵥ J *ᵥ v' =
      ρ * (star (((ρ⁻¹ : Aˣ) : A) • (u - u')) ⬝ᵥ J *ᵥ v +
        star u' ⬝ᵥ J *ᵥ (((ρ⁻¹ : Aˣ) : A) • (v - v'))) := by
  have hρ' := (hρ.of_mul_eq_one (Units.mul_inv ρ)).star_eq
  have h1 : (ρ : A) * ((ρ⁻¹ : Aˣ) : A) = 1 := Units.mul_inv ρ
  simp only [star_smul, hρ', star_sub, mulVec_smul, mulVec_sub, smul_dotProduct, dotProduct_smul,
    sub_dotProduct, dotProduct_sub, smul_eq_mul]
  linear_combination (-(star u ⬝ᵥ J *ᵥ v - star u' ⬝ᵥ J *ᵥ v')) * h1

end Form

/-! ### Comparing the lengths at two points -/

variable {e : ℕ → ι → A} {ρ : Aˣ} {g g' : GL ι A}

/-- The size of the coefficient `⟨e_a, ω⟩` of a vector `ω` orthogonal below `a` of length at most
`L ^ i` at `g`, when the class of `e_a` in `Y^(a)` has induced length at most `L ^ c` at `g`. -/
private theorem star_dotProduct_mulVec_mem_of_inducedLengthLe (hg : g ∈ unitaryGroupOf J)
    {a c i : ℕ} {ω : ι → A} (h : S.InducedLengthLe e a g c (e a))
    (hω : ∀ b < a, star (e b) ⬝ᵥ J *ᵥ ω = 0) (hωg : S.LengthLeAt g i ω) :
    star (e a) ⬝ᵥ J *ᵥ ω ∈ S.ofSize (c + i + 3) := by
  obtain ⟨e₁, he₁, he₁g⟩ := h
  rw [star_dotProduct_mulVec_eq_of_sub_mem_span (by rintro _ ⟨b, hb, rfl⟩; exact hω b hb) he₁,
    ← mem_unitaryGroupOf_iff_forall_dotProduct.mp (inv_mem hg)]
  exact S.star_dotProduct_mulVec_mem he₁g hωg

omit [DecidableEq ι] in
/-- Splitting along a dual `ζ` of `e_a`: if `ω` is orthogonal below `a`, then `ω - ⟨e_a, ω⟩ ζ` is
orthogonal below `a + 1`. -/
private theorem star_dotProduct_mulVec_sub_smul_eq_zero {a : ℕ} {ω ζ : ι → A}
    (hω : ∀ b < a, star (e b) ⬝ᵥ J *ᵥ ω = 0) (hζ : ∀ b < a, star (e b) ⬝ᵥ J *ᵥ ζ = 0)
    (hζa : star (e a) ⬝ᵥ J *ᵥ ζ = 1) :
    ∀ b < a + 1, star (e b) ⬝ᵥ J *ᵥ (ω - (star (e a) ⬝ᵥ J *ᵥ ω) • ζ) = 0 := by
  intro b hb
  simp only [mulVec_sub, mulVec_smul, dotProduct_sub, dotProduct_smul, smul_eq_mul]
  rcases Nat.lt_succ_iff_lt_or_eq.mp hb with hb | rfl
  · rw [hω b hb, hζ b hb, mul_zero, sub_zero]
  · rw [hζa, mul_one, sub_self]

/-- The coefficient along `e_a` of the difference between a vector `ω₀` orthogonal below `a + 1`
and a lift `ω₀'` of its class, divided by `ρ`, is small. It is read off by a short dual `ζ` of
`e_a`, as a difference of two values of the form, at `g` and at `g'`. -/
private theorem inv_mul_mem_of_add_eq_sub [Nonempty ι] (hJ : J.IsHermitian)
    (hg : g ∈ unitaryGroupOf J) (hg' : g' ∈ unitaryGroupOf J) (hρ : IsSelfAdjoint (ρ : A))
    (hρS : (ρ : A) ∈ S.ofSize 1) {a c i t : ℕ}
    (he : ∀ b < a, ∀ b' ≤ a, star (e b) ⬝ᵥ J *ᵥ e b' = 0) {ζ ζ' ω₀ ω₀' s : ι → A} {μ : A}
    (hζ : ∀ b < a, star (e b) ⬝ᵥ J *ᵥ ζ = 0) (hζa : star (e a) ⬝ᵥ J *ᵥ ζ = 1)
    (hζg : S.LengthLeAt g c ζ) (hζζ' : ζ - ζ' ∈ Submodule.span A (e '' Set.Iio a))
    (hD₁ : ((ρ⁻¹ : Aˣ) : A) • (((g⁻¹ : GL ι A) : Matrix ι ι A) *ᵥ ζ -
      ((g'⁻¹ : GL ι A) : Matrix ι ι A) *ᵥ ζ') ∈ S.vecsOfSize c)
    (hω₀ : ∀ b < a + 1, star (e b) ⬝ᵥ J *ᵥ ω₀ = 0) (hω₀g : S.LengthLeAt g i ω₀)
    (hD₂ : ((ρ⁻¹ : Aˣ) : A) • (((g⁻¹ : GL ι A) : Matrix ι ι A) *ᵥ ω₀ -
      ((g'⁻¹ : GL ι A) : Matrix ι ι A) *ᵥ ω₀') ∈ S.vecsOfSize (i + t))
    (hs : s ∈ Submodule.span A (e '' Set.Iio a)) (hys : μ • e a + s = ω₀ - ω₀') :
    ((ρ⁻¹ : Aˣ) : A) * μ ∈ S.ofSize (i + c + t + 6) := by
  -- `μ = ⟨ζ, ω₀⟩ - ⟨ζ, ω₀'⟩`, since `⟨ζ, e_a⟩ = 1` and `ζ` is orthogonal to `s`.
  have hμ : μ = star ζ ⬝ᵥ J *ᵥ ω₀ - star ζ ⬝ᵥ J *ᵥ ω₀' := by
    have hζs : star ζ ⬝ᵥ J *ᵥ s = 0 :=
      dotProduct_mulVec_eq_zero_of_mem_span (by
        rintro _ ⟨b, hb, rfl⟩
        rw [← hJ.star_dotProduct_mulVec_comm, hζ b hb, star_zero]) hs
    have hζea : star ζ ⬝ᵥ J *ᵥ e a = 1 := by
      rw [← hJ.star_dotProduct_mulVec_comm, hζa, star_one]
    have := congrArg (fun v => star ζ ⬝ᵥ J *ᵥ v) hys
    simpa only [mulVec_add, mulVec_smul, dotProduct_add, dotProduct_smul, smul_eq_mul, hζs, hζea,
      mul_one, add_zero, mulVec_sub, dotProduct_sub] using this
  -- `ω₀'` is still orthogonal below `a`, so `⟨ζ, ω₀'⟩ = ⟨ζ', ω₀'⟩`.
  have hω₀' : ∀ b < a, star (e b) ⬝ᵥ J *ᵥ ω₀' = 0 := by
    intro b hb
    have hsp : ω₀ - ω₀' ∈ Submodule.span A (e '' Set.Iio (a + 1)) := by
      rw [← hys]
      refine Submodule.add_mem _ (Submodule.smul_mem _ _ (Submodule.subset_span ⟨a, by simp, rfl⟩))
        (Submodule.span_mono (Set.image_mono (Set.Iio_subset_Iio (Nat.le_succ a))) hs)
    have h0 := dotProduct_mulVec_eq_zero_of_mem_span
      (by rintro _ ⟨b', hb', rfl⟩; exact he b hb b' (Nat.le_of_lt_succ hb')) hsp
    rwa [mulVec_sub, dotProduct_sub, hω₀ b (by omega), zero_sub, neg_eq_zero] at h0
  have hζζ'ω₀' : star ζ ⬝ᵥ J *ᵥ ω₀' = star ζ' ⬝ᵥ J *ᵥ ω₀' :=
    star_dotProduct_mulVec_eq_of_sub_mem_span (by rintro _ ⟨b, hb, rfl⟩; exact hω₀' b hb) hζζ'
  -- Read at `g⁻¹` and `g'⁻¹`, which preserve the form, `μ` is a difference of two nearby values.
  have hμ' : μ = star (((g⁻¹ : GL ι A) : Matrix ι ι A) *ᵥ ζ) ⬝ᵥ
      J *ᵥ (((g⁻¹ : GL ι A) : Matrix ι ι A) *ᵥ ω₀) -
      star (((g'⁻¹ : GL ι A) : Matrix ι ι A) *ᵥ ζ') ⬝ᵥ
        J *ᵥ (((g'⁻¹ : GL ι A) : Matrix ι ι A) *ᵥ ω₀') := by
    rw [hμ, hζζ'ω₀', mem_unitaryGroupOf_iff_forall_dotProduct.mp (inv_mem hg) ζ ω₀,
      mem_unitaryGroupOf_iff_forall_dotProduct.mp (inv_mem hg') ζ' ω₀']
  rw [hμ', star_dotProduct_mulVec_sub_eq hρ, Units.inv_mul_cancel_left]
  -- `g'⁻¹ ζ' = g⁻¹ ζ - ρ D₁` has size `c + 2`.
  have hu' : ((g'⁻¹ : GL ι A) : Matrix ι ι A) *ᵥ ζ' ∈ S.vecsOfSize (c + 2) := by
    have h := S.sub_mem_vecsOfSize (hζg.mono (by omega : c ≤ 1 + c))
      (S.smul_mem_vecsOfSize hρS hD₁)
    rw [smul_smul, Units.mul_inv, one_smul, sub_sub_cancel] at h
    exact S.mem_vecsOfSize_of_le h (by omega)
  have h₁ := S.star_dotProduct_mulVec_mem hD₁ hω₀g
  have h₂ := S.star_dotProduct_mulVec_mem hu' hD₂
  exact S.add_mem (i := i + c + t + 5) (S.mem_of_le h₁ (by omega)) (S.mem_of_le h₂ (by omega))

/-- **The comparison of the lengths descends one step along the flag.** Let `g` and `g'` lie in
the unitary group of a Hermitian Gram matrix `J`, let `ρ` be a self-adjoint unit of size `1`, and
let each `e_b`, `b < a`, be orthogonal to `e_0, …, e_a`. If the class of `e_a` in `Y^(a)` has
induced length at most `L ^ c` at `g` and at `g'`, `e_a` has a short dual of exponent `c` for
`(g, g')` modulo `ρ`, and the lengths at `g` and `g'` differ by at most `L ^ t` on `Y^(a + 1)`
modulo `ρ`, then they differ by at most `L ^ (t + 4c + 12)` on `Y^(a)` modulo `ρ`. -/
theorem LengthsDifferLe.of_succ (hJ : J.IsHermitian) (hg : g ∈ unitaryGroupOf J)
    (hg' : g' ∈ unitaryGroupOf J) (hρ : IsSelfAdjoint (ρ : A)) (hρS : (ρ : A) ∈ S.ofSize 1)
    {a c t : ℕ} (he : ∀ b < a, ∀ b' ≤ a, star (e b) ⬝ᵥ J *ᵥ e b' = 0)
    (h₁ : S.InducedLengthLe e a g c (e a)) (h₂ : S.InducedLengthLe e a g' c (e a))
    (hd : S.HasShortDual e a ρ g g' c) (ht : S.LengthsDifferLe e (a + 1) ρ g g' t) :
    S.LengthsDifferLe e a ρ g g' (t + 4 * c + 12) := by
  intro i ω hω hωg
  rcases isEmpty_or_nonempty ι with hι | hι
  · exact ⟨ω, by simp, (S.mem_vecsOfSize).mpr fun k => isEmptyElim k⟩
  obtain ⟨e₂, he₂, he₂g'⟩ := h₂
  obtain ⟨ζ, hζ, hζa, hζg, ζ', hζζ', hD₁⟩ := hd
  -- Split `ω = ω₀ + λ ζ` with `λ = ⟨e_a, ω⟩` and `ω₀` orthogonal below `a + 1`.
  set lam := star (e a) ⬝ᵥ J *ᵥ ω
  have hlam : lam ∈ S.ofSize (c + i + 3) :=
    star_dotProduct_mulVec_mem_of_inducedLengthLe hg h₁ hω hωg
  set ω₀ := ω - lam • ζ with hω₀
  have hω₀g : S.LengthLeAt g (i + 2 * c + 4) ω₀ := by
    have h := S.sub_mem_vecsOfSize (hωg.mono (by omega : i ≤ c + i + 3 + c))
      (S.smul_mem_vecsOfSize hlam hζg)
    simpa only [LengthLeAt, hω₀, mulVec_sub, mulVec_smul,
      show c + i + 3 + c + 1 = i + 2 * c + 4 by omega] using h
  -- Compare `ω₀` by hypothesis, and split the difference `ω₀ - ω₀' = μ e_a + s`.
  have hω₀orth := star_dotProduct_mulVec_sub_smul_eq_zero hω hζ hζa
  obtain ⟨ω₀', hω₀ω₀', hD₂⟩ := ht (i + 2 * c + 4) ω₀ hω₀orth hω₀g
  have hIio : e '' Set.Iio (a + 1) = insert (e a) (e '' Set.Iio a) := by
    rw [← Set.image_insert_eq, ← Order.succ_eq_add_one, Order.Iio_succ_eq_insert]
  rw [hIio, Submodule.span_insert, Submodule.mem_sup] at hω₀ω₀'
  obtain ⟨y, hy, s, hs, hys⟩ := hω₀ω₀'
  obtain ⟨μ, rfl⟩ := Submodule.mem_span_singleton.mp hy
  have hμ := inv_mul_mem_of_add_eq_sub hJ hg hg' hρ hρS he hζ hζa hζg hζζ' hD₁ hω₀orth hω₀g hD₂
    hs hys
  -- The lift `ω' = ω₀' + μ e₂ + λ ζ'`.
  refine ⟨ω₀' + μ • e₂ + lam • ζ', ?_, ?_⟩
  · have hdiff : ω - (ω₀' + μ • e₂ + lam • ζ') = s + μ • (e a - e₂) + lam • (ζ - ζ') := by
      rw [eq_sub_of_add_eq' hys, hω₀]
      module
    rw [hdiff]
    exact Submodule.add_mem _ (Submodule.add_mem _ hs (Submodule.smul_mem _ _ he₂))
      (Submodule.smul_mem _ _ hζζ')
  · set G : Matrix ι ι A := ((g⁻¹ : GL ι A) : Matrix ι ι A)
    set G' : Matrix ι ι A := ((g'⁻¹ : GL ι A) : Matrix ι ι A)
    set r : A := ((ρ⁻¹ : Aˣ) : A)
    have hdiff : r • (G *ᵥ ω - G' *ᵥ (ω₀' + μ • e₂ + lam • ζ')) =
        r • (G *ᵥ ω₀ - G' *ᵥ ω₀') - (r * μ) • (G' *ᵥ e₂) + lam • (r • (G *ᵥ ζ - G' *ᵥ ζ')) := by
      rw [hω₀]
      simp only [mulVec_add, mulVec_sub, mulVec_smul]
      module
    rw [hdiff]
    have hsub := S.sub_mem_vecsOfSize (S.mem_vecsOfSize_of_le hD₂ (by omega))
      (S.smul_mem_vecsOfSize hμ he₂g')
    exact S.mem_vecsOfSize_of_le (S.add_mem_vecsOfSize hsub
      (S.mem_vecsOfSize_of_le (S.smul_mem_vecsOfSize hlam hD₁) (by omega))) (by omega)

/-- **The comparison of the lengths on the whole space.** Let `g` and `g'` lie in the unitary
group of a Hermitian Gram matrix `J`, let `ρ` be a self-adjoint unit of size `1`, and let
`⟨e_b, e_b'⟩ = 0` for all `b, b' < j` (each `e_b` is isotropic as well as orthogonal to the
others). If, for every `a < j`, the class of `e_a` in `Y^(a)` has induced length at most `L ^ c`
at `g` and at `g'` and `e_a` has a short dual of exponent `c` for `(g, g')` modulo `ρ`, and the
lengths at `g` and `g'` differ by at most `L ^ t` on `Y^(j)` modulo `ρ`, then they differ by at
most `L ^ (t + (4c + 12) j)` on the whole space `Y^(0)` modulo `ρ`. -/
theorem LengthsDifferLe.zero_of_hasShortDual (hJ : J.IsHermitian) (hg : g ∈ unitaryGroupOf J)
    (hg' : g' ∈ unitaryGroupOf J) (hρ : IsSelfAdjoint (ρ : A)) (hρS : (ρ : A) ∈ S.ofSize 1)
    {j c t : ℕ} (he : ∀ b < j, ∀ b' < j, star (e b) ⬝ᵥ J *ᵥ e b' = 0)
    (h : ∀ a < j, S.InducedLengthLe e a g c (e a) ∧ S.InducedLengthLe e a g' c (e a) ∧
      S.HasShortDual e a ρ g g' c)
    (ht : S.LengthsDifferLe e j ρ g g' t) :
    S.LengthsDifferLe e 0 ρ g g' (t + (4 * c + 12) * j) := by
  induction j generalizing t with
  | zero => simpa using ht
  | succ j ih =>
    obtain ⟨h₁, h₂, hd⟩ := h j (Nat.lt_succ_self j)
    have hj := ht.of_succ hJ hg hg' hρ hρS
      (fun b hb b' hb' => he b (by omega) b' (by omega)) h₁ h₂ hd
    have := ih (fun b hb b' hb' => he b (by omega) b' (by omega))
      (fun a ha => h a (by omega)) hj
    rwa [show t + 4 * c + 12 + (4 * c + 12) * j = t + (4 * c + 12) * (j + 1) by ring] at this

/-- **Points with comparable lengths are close.** If `x` lies in the unitary group of an
invertible Gram matrix `J`, `ρ` is a self-adjoint unit, and the lengths at `g` and `g x` differ by
at most `L ^ i` on the whole space `Y^(0)` modulo `ρ`, then `(x - 1) / ρ` has size `i + 4`. -/
theorem LengthsDifferLe.smul_sub_one_mem_matsOfSize (hJ : IsUnit J) {x : GL ι A}
    (hx : x ∈ unitaryGroupOf J) (hρ : IsSelfAdjoint (ρ : A)) {i : ℕ}
    (h : S.LengthsDifferLe e 0 ρ g (g * x) i) :
    ((ρ⁻¹ : Aˣ) : A) • ((x : Matrix ι ι A) - 1) ∈ S.matsOfSize (i + 4) := by
  set r : A := ((ρ⁻¹ : Aˣ) : A) with hr
  set M : Matrix ι ι A := r • (1 - ((x⁻¹ : GL ι A) : Matrix ι ι A)) with hM
  -- The columns of `(1 - x⁻¹) / ρ` are the differences at `g` and `g x` of the vectors `g e_k`.
  have hMS : M ∈ S.matsOfSize i := by
    refine S.mem_matsOfSize_of_col fun k => ?_
    obtain ⟨ω', hω', hk⟩ := h 0 ((g : Matrix ι ι A) *ᵥ Pi.single k 1) (fun b hb => absurd hb
      (Nat.not_lt_zero b)) (by
        rw [LengthLeAt, mulVec_mulVec, Units.inv_mul, one_mulVec]
        exact S.single_one_mem_vecsOfSize 0 k)
    have hω'eq : ω' = (g : Matrix ι ι A) *ᵥ Pi.single k 1 := by
      have h0 : Set.Iio (0 : ℕ) = ∅ := Set.Iio_eq_empty_iff.mpr isMin_bot
      rw [h0, Set.image_empty, Submodule.span_empty, Submodule.mem_bot, sub_eq_zero] at hω'
      exact hω'.symm
    have hgx : (((g * x)⁻¹ : GL ι A) : Matrix ι ι A) * g = ((x⁻¹ : GL ι A) : Matrix ι ι A) := by
      rw [← Units.val_mul, _root_.mul_inv_rev, inv_mul_cancel_right]
    simp only [hω'eq, zero_add, mulVec_mulVec, Units.inv_mul, hgx, one_mulVec] at hk
    convert hk using 1
    ext a
    simp [hM, hr, Matrix.one_apply, Pi.single_apply]
  -- `x = J⁻¹ * star x⁻¹ * J`, so that `(x - 1) / ρ = -(J⁻¹ * Mᴴ * J)`.
  have hxJ : (x : Matrix ι ι A) = J⁻¹ * star ((x⁻¹ : GL ι A) : Matrix ι ι A) * J := by
    rw [← val_inv_of_mem_unitaryGroupOf hJ (inv_mem hx), inv_inv]
  have hρ' : star r = r := (hρ.of_mul_eq_one (Units.mul_inv ρ)).star_eq
  have hJJ : J⁻¹ * J = 1 := nonsing_inv_mul J ((isUnit_iff_isUnit_det J).mp hJ)
  have hkey : r • ((x : Matrix ι ι A) - 1) = -(J⁻¹ * Mᴴ * J) := by
    rw [hxJ]
    simp [hM, hρ', Matrix.mul_sub, Matrix.sub_mul, hJJ, star_eq_conjTranspose, smul_sub]
  rw [hkey, neg_mem_matsOfSize_iff]
  have h₁ := S.mul_mem_matsOfSize S.gram_inv_mem_matsOfSize
    ((S.conjTranspose_mem_matsOfSize_iff).mpr hMS)
  have h₂ := S.mul_mem_matsOfSize h₁ S.gram_mem_matsOfSize
  exact S.mem_matsOfSize_of_le h₂ (by omega)

end GramSize

end TauCeti
