/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Lie.Abelian
public import Mathlib.Algebra.Lie.Semisimple.Defs
public import TauCeti.Algebra.Octonion.Derivation
import Mathlib.Tactic.LinearCombination

/-!
# The imaginary octonions are the fundamental representation of `G₂ = Der 𝕆`

`TauCeti/Algebra/Octonion/Derivation.lean` builds the derivation algebra `Der 𝕆` of the split
octonions, shows that it is `14`-dimensional, and exhibits the imaginary octonions
`TauCeti.Octonion.imaginaryLieSubmodule` as a `7`-dimensional Lie submodule of `𝕆` on which it acts
faithfully. That makes `Im 𝕆` the *candidate* fundamental representation of `G₂`. This file proves
that it really is one: over a field in which `2` is nonzero, `Im 𝕆` is an **irreducible**
representation of `Der 𝕆` (`TauCeti.Octonion.isIrreducible_imaginaryLieSubmodule`), of dimension `7`
by `TauCeti.Octonion.finrank_imaginary`.

The whole argument runs on two of the three explicit families of derivations of
`TauCeti/Algebra/Octonion/Derivation.lean`, the vector families
`TauCeti.Octonion.upperDerivation` and `TauCeti.Octonion.lowerDerivation`, and never mentions the
`𝔰𝔩₃` family. Write `ε = ⟨1, -1, 0, 0⟩` for the imaginary part of the diagonal idempotent of `𝕆`,
the one imaginary direction on the scalar diagonal. The two computations that do the work are
iterations of a single vector derivation:

* applying `upperDerivation u` twice kills every entry but the upper vector one, where it leaves
  `-2 ⟨u, w⟩ · u`, so one more `lowerDerivation t` lands on the line through `ε`
  (`TauCeti.Octonion.lowerDerivation_upperDerivation_upperDerivation_apply`), with coefficient
  `2 ⟨u, w⟩ ⟨t, u⟩`;
* symmetrically for `lowerDerivation` twice followed by `upperDerivation`
  (`TauCeti.Octonion.upperDerivation_lowerDerivation_lowerDerivation_apply`), with coefficient
  `2 ⟨t, v⟩ ⟨u, t⟩`.

Taking `u = t` a standard basis vector makes the coefficient `2 wᵢ`, respectively `2 vᵢ`. So a Lie
submodule containing a nonzero imaginary octonion contains `ε`: if some lower coordinate `wᵢ` is
nonzero the first computation produces a nonzero multiple of `ε`, if some upper coordinate `vᵢ` is
nonzero the second does, and if all of them vanish the octonion is already a nonzero multiple of
`ε`. Conversely `ε` generates: `upperDerivation u` and `lowerDerivation t` send `ε` to the upper
vector `2 u` and the lower vector `2 t`, so with `2` invertible every imaginary octonion
`⟨a, -a, v, w⟩` is `a · ε` plus the images of `ε` under the two derivations attached to `2⁻¹ v` and
`2⁻¹ w`. Together these two directions say that `Im 𝕆` is a *minimal* nonzero Lie submodule of `𝕆`
(`TauCeti.Octonion.eq_imaginaryLieSubmodule_of_le_of_ne_bot`), which is irreducibility.

Some hypothesis on `2` is necessary, and it is the same one that
`TauCeti.Octonion.isFaithful_imaginaryLieSubmodule` needs: where `2` vanishes so does `trace 1`, so
`1` is imaginary, and a derivation kills `1`, so the line through `1` is a Lie submodule of `Im 𝕆`
different from `0` and from `Im 𝕆`. That is
`TauCeti.Octonion.not_isIrreducible_imaginaryLieSubmodule_of_two_eq_zero`, proved below over every
nontrivial base ring in which `2` vanishes, so the hypothesis is not an artefact of the argument.

## Main results

* `TauCeti.Octonion.lowerDerivation_upperDerivation_upperDerivation_apply` and
  `TauCeti.Octonion.upperDerivation_lowerDerivation_lowerDerivation_apply`: three vector
  derivations, applied to an arbitrary octonion, land on the line through `ε = ⟨1, -1, 0, 0⟩`, with
  the coefficients displayed above.
* `TauCeti.Octonion.imaginaryLieSubmodule_le_of_mem`: a Lie submodule of `𝕆` containing `ε`
  contains every imaginary octonion, as soon as `2` is invertible.
* `TauCeti.Octonion.diagonal_mem_of_mem_of_trace_eq_zero`: over a field in which `2` is nonzero,
  a Lie submodule of `𝕆` containing a nonzero imaginary octonion contains `ε`.
* `TauCeti.Octonion.eq_imaginaryLieSubmodule_of_le_of_ne_bot`: **`Im 𝕆` is a minimal nonzero Lie
  submodule of `𝕆`.**
* `TauCeti.Octonion.isIrreducible_imaginaryLieSubmodule`: **`Im 𝕆` is an irreducible representation
  of `Der 𝕆`**, with `TauCeti.Octonion.instIsIrreducibleImaginaryLieSubmodule` its instance form.
* `TauCeti.Octonion.not_isIrreducible_imaginaryLieSubmodule_of_two_eq_zero`: and it is **reducible**
  where `2` vanishes, so the hypothesis on `2` is necessary.

## Implementation notes

The element `ε` is spelled out as the vector-matrix literal `⟨1, -1, 0, 0⟩` rather than given a
name of its own: it occurs only as the right-hand side of the two computations and as the generator
in the statements above, and `TauCeti/Algebra/Octonion/Basic.lean` names no other individual
octonion either.

The computational lemmas are stated over a commutative ring and for an arbitrary octonion, not only
an imaginary one; nothing in them needs the trace to vanish. Invertibility of `2` enters only in the
generation lemma, and a field only where a nonzero coefficient has to be inverted, so the two halves
of minimality carry different hypotheses. The minimality statement is made for Lie
submodules of `𝕆` itself, which is where the derivations act; irreducibility of the subtype
`↥(Im 𝕆)` is read off it by pushing a Lie submodule of the subtype forward along
`LieSubmodule.incl`, which is injective.

## References

The identification of `Der 𝕆` with the split `LieAlgebra.g₂` and its type-`G₂` Killing-simplicity
are not proved here.

* T. A. Springer and F. D. Veldkamp, *Octonions, Jordan Algebras and Exceptional Groups*, §2.
* J. C. Baez, *The octonions*, Bull. Amer. Math. Soc. 39 (2002), §4.1.
-/

public section

namespace TauCeti

namespace Octonion

open Matrix

attribute [local instance 100] LieRing.ofAssociativeRing

/-! ### Iterating a vector derivation -/

section Computation

variable {R : Type*} [CommRing R]

/-- Applying `TauCeti.Octonion.upperDerivation u` twice kills every entry but the upper vector one,
where it leaves `-2 ⟨u, w⟩ · u`: the two cross-product terms vanish because `u ⨯₃ u = 0` and
`u ⬝ᵥ (u ⨯₃ v) = 0`. -/
theorem upperDerivation_upperDerivation_apply (u : Fin 3 → R) (x : Octonion R) :
    (upperDerivation u : Module.End R (Octonion R))
        ((upperDerivation u : Module.End R (Octonion R)) x) =
      ⟨0, 0, -(2 * (u ⬝ᵥ x.w)) • u, 0⟩ := by
  refine Octonion.ext ?_ ?_ ?_ ?_
  · simp [dot_self_cross]
  · simp [dot_self_cross]
  · simp only [upperDerivation_apply_v, upperDerivation_apply_a, upperDerivation_apply_b]
    congr 1
    ring
  · simp [cross_self]

/-- Applying `TauCeti.Octonion.lowerDerivation t` twice kills every entry but the lower vector one,
where it leaves `-2 ⟨t, v⟩ · t`: the two cross-product terms vanish because `t ⨯₃ t = 0` and
`t ⬝ᵥ (t ⨯₃ w) = 0`. This statement is the mirror image of
`TauCeti.Octonion.upperDerivation_upperDerivation_apply`. -/
theorem lowerDerivation_lowerDerivation_apply (t : Fin 3 → R) (x : Octonion R) :
    (lowerDerivation t : Module.End R (Octonion R))
        ((lowerDerivation t : Module.End R (Octonion R)) x) =
      ⟨0, 0, 0, -(2 * (t ⬝ᵥ x.v)) • t⟩ := by
  refine Octonion.ext ?_ ?_ ?_ ?_
  · simp [dot_self_cross]
  · simp [dot_self_cross]
  · simp [cross_self]
  · simp only [lowerDerivation_apply_w, lowerDerivation_apply_a, lowerDerivation_apply_b]
    congr 1
    ring

/-- **Two upper vector derivations and one lower one land on the diagonal imaginary line.** The
double upper derivation of `TauCeti.Octonion.upperDerivation_upperDerivation_apply` leaves a pure
upper vector, which a lower derivation turns into a multiple of `ε = ⟨1, -1, 0, 0⟩`. -/
theorem lowerDerivation_upperDerivation_upperDerivation_apply (t u : Fin 3 → R) (x : Octonion R) :
    (lowerDerivation t : Module.End R (Octonion R))
        ((upperDerivation u : Module.End R (Octonion R))
          ((upperDerivation u : Module.End R (Octonion R)) x)) =
      (2 * (u ⬝ᵥ x.w) * (t ⬝ᵥ u)) • (⟨1, -1, 0, 0⟩ : Octonion R) := by
  rw [upperDerivation_upperDerivation_apply]
  refine Octonion.ext ?_ ?_ ?_ ?_
  · simp [dotProduct_smul]
  · simp [dotProduct_smul]
  · simp
  · simp

/-- **Two lower vector derivations and one upper one land on the diagonal imaginary line.** The
double lower derivation of `TauCeti.Octonion.lowerDerivation_lowerDerivation_apply` leaves a pure
lower vector, which an upper derivation turns into the multiple `2 ⟨t, v⟩ ⟨u, t⟩` of
`ε = ⟨1, -1, 0, 0⟩`; these statements are the mirror images of
`TauCeti.Octonion.lowerDerivation_upperDerivation_upperDerivation_apply` and its inputs. -/
theorem upperDerivation_lowerDerivation_lowerDerivation_apply (u t : Fin 3 → R) (x : Octonion R) :
    (upperDerivation u : Module.End R (Octonion R))
        ((lowerDerivation t : Module.End R (Octonion R))
          ((lowerDerivation t : Module.End R (Octonion R)) x)) =
      (2 * (t ⬝ᵥ x.v) * (u ⬝ᵥ t)) • (⟨1, -1, 0, 0⟩ : Octonion R) := by
  rw [lowerDerivation_lowerDerivation_apply]
  refine Octonion.ext ?_ ?_ ?_ ?_
  · simp [dotProduct_smul]
  · simp [dotProduct_smul]
  · simp
  · simp

/-- An upper vector derivation moves `ε = ⟨1, -1, 0, 0⟩` onto the upper vector `2 u`: the diagonal
entries of `ε` differ by `2`, and its vector entries vanish. -/
theorem upperDerivation_apply_diagonal (u : Fin 3 → R) :
    (upperDerivation u : Module.End R (Octonion R)) ⟨1, -1, 0, 0⟩ =
      ⟨0, 0, (2 : R) • u, 0⟩ := by
  refine Octonion.ext ?_ ?_ ?_ ?_
  · simp
  · simp
  · simp only [upperDerivation_apply_v]
    congr 1
    ring
  · simp

/-- A lower vector derivation moves `ε = ⟨1, -1, 0, 0⟩` onto the lower vector `2 t`, the mirror
image of the statement `TauCeti.Octonion.upperDerivation_apply_diagonal`. -/
theorem lowerDerivation_apply_diagonal (t : Fin 3 → R) :
    (lowerDerivation t : Module.End R (Octonion R)) ⟨1, -1, 0, 0⟩ =
      ⟨0, 0, 0, (2 : R) • t⟩ := by
  refine Octonion.ext ?_ ?_ ?_ ?_
  · simp
  · simp
  · simp
  · simp only [lowerDerivation_apply_w]
    congr 1
    ring

end Computation

/-! ### `ε` generates the imaginary octonions -/

section Generation

variable {R : Type*} [CommRing R] [Invertible (2 : R)]
  {N : LieSubmodule R (derivationLieAlgebra R (Octonion R)) (Octonion R)}

/-- **`ε = ⟨1, -1, 0, 0⟩` generates the imaginary octonions.** A Lie submodule of `𝕆` containing
`ε` contains every imaginary octonion: writing `x = ⟨a, -a, v, w⟩`, the three summands of
`x = a · ε + D₊ ε + D₋ ε` for the vector derivations `D₊`, `D₋` attached to `⅟2 • v` and `⅟2 • w`
are all in the submodule, by `TauCeti.Octonion.upperDerivation_apply_diagonal` and
`TauCeti.Octonion.lowerDerivation_apply_diagonal`. -/
theorem imaginaryLieSubmodule_le_of_mem (h : (⟨1, -1, 0, 0⟩ : Octonion R) ∈ N) :
    imaginaryLieSubmodule R ≤ N := by
  intro x hx
  have hb : x.b = -x.a := by
    have htr : x.a + x.b = 0 := by simpa using mem_imaginaryLieSubmodule.mp hx
    linear_combination htr
  have hdecomp : x = x.a • (⟨1, -1, 0, 0⟩ : Octonion R) +
      (⁅upperDerivation (⅟(2 : R) • x.v), (⟨1, -1, 0, 0⟩ : Octonion R)⁆ +
        ⁅lowerDerivation (⅟(2 : R) • x.w), (⟨1, -1, 0, 0⟩ : Octonion R)⁆) := by
    simp only [LieSubalgebra.coe_bracket_of_module, Module.End.lie_apply,
      upperDerivation_apply_diagonal, lowerDerivation_apply_diagonal]
    refine Octonion.ext ?_ ?_ ?_ ?_
    · simp
    · simp [hb]
    · simp [smul_smul]
    · simp [smul_smul]
  rw [hdecomp]
  exact N.add_mem (N.smul_mem _ h) (N.add_mem (N.lie_mem h) (N.lie_mem h))

end Generation

/-! ### Minimality and irreducibility -/

section Field

variable {K : Type*} [Field K]
  {N : LieSubmodule K (derivationLieAlgebra K (Octonion K)) (Octonion K)}

/-- **A Lie submodule of `𝕆` containing a nonzero imaginary octonion contains
`ε = ⟨1, -1, 0, 0⟩`.** If some lower coordinate of `x` is nonzero,
`TauCeti.Octonion.lowerDerivation_upperDerivation_upperDerivation_apply` at the matching standard
basis vector produces the nonzero multiple `2 x.w i · ε`; if some upper coordinate is nonzero,
`TauCeti.Octonion.upperDerivation_lowerDerivation_lowerDerivation_apply` does; and if both vector
entries vanish then `x` is already `x.a · ε` with `x.a ≠ 0`. -/
theorem diagonal_mem_of_mem_of_trace_eq_zero (h2 : (2 : K) ≠ 0) {x : Octonion K} (hxN : x ∈ N)
    (hx : trace x = 0) (hx0 : x ≠ 0) : (⟨1, -1, 0, 0⟩ : Octonion K) ∈ N := by
  have hb : x.b = -x.a := by
    have htr : x.a + x.b = 0 := by simpa using hx
    linear_combination htr
  have key : ∀ c : K, c ≠ 0 → c • (⟨1, -1, 0, 0⟩ : Octonion K) ∈ N →
      (⟨1, -1, 0, 0⟩ : Octonion K) ∈ N := by
    intro c hc hmem
    have := N.smul_mem c⁻¹ hmem
    rwa [smul_smul, inv_mul_cancel₀ hc, one_smul] at this
  rcases eq_or_ne x.w 0 with hw | hw
  · rcases eq_or_ne x.v 0 with hv | hv
    · have hxa : x.a ≠ 0 := fun h0 =>
        hx0 (Octonion.ext h0 (by simp [hb, h0]) hv hw)
      refine key x.a hxa ?_
      have hxeq : x.a • (⟨1, -1, 0, 0⟩ : Octonion K) = x := by
        refine Octonion.ext ?_ ?_ ?_ ?_
        · simp
        · simp [hb]
        · simp [hv]
        · simp [hw]
      rwa [hxeq]
    · obtain ⟨i, hi⟩ := Function.ne_iff.mp hv
      rw [Pi.zero_apply] at hi
      refine key (2 * x.v i) (by simp [h2, hi]) ?_
      have := N.lie_mem (x := upperDerivation (Pi.single i 1))
        (N.lie_mem (x := lowerDerivation (Pi.single i 1))
          (N.lie_mem (x := lowerDerivation (Pi.single i 1)) hxN))
      simp only [LieSubalgebra.coe_bracket_of_module, Module.End.lie_apply,
        upperDerivation_lowerDerivation_lowerDerivation_apply] at this
      simpa [single_dotProduct] using this
  · obtain ⟨i, hi⟩ := Function.ne_iff.mp hw
    rw [Pi.zero_apply] at hi
    refine key (2 * x.w i) (by simp [h2, hi]) ?_
    have := N.lie_mem (x := lowerDerivation (Pi.single i 1))
      (N.lie_mem (x := upperDerivation (Pi.single i 1))
        (N.lie_mem (x := upperDerivation (Pi.single i 1)) hxN))
    simp only [LieSubalgebra.coe_bracket_of_module, Module.End.lie_apply,
      lowerDerivation_upperDerivation_upperDerivation_apply] at this
    simpa [single_dotProduct] using this

/-- **The imaginary octonions are a minimal nonzero Lie submodule of `𝕆`.** A nonzero Lie submodule
contained in `Im 𝕆` contains `ε = ⟨1, -1, 0, 0⟩` by
`TauCeti.Octonion.diagonal_mem_of_mem_of_trace_eq_zero`, hence all of `Im 𝕆` by
`TauCeti.Octonion.imaginaryLieSubmodule_le_of_mem`. -/
theorem eq_imaginaryLieSubmodule_of_le_of_ne_bot (h2 : (2 : K) ≠ 0)
    (hle : N ≤ imaginaryLieSubmodule K) (hne : N ≠ ⊥) : N = imaginaryLieSubmodule K := by
  have h2' : Invertible (2 : K) := invertibleOfNonzero h2
  rw [Ne, LieSubmodule.eq_bot_iff] at hne
  push Not at hne
  obtain ⟨x, hxN, hx0⟩ := hne
  exact le_antisymm hle
    (imaginaryLieSubmodule_le_of_mem
      (diagonal_mem_of_mem_of_trace_eq_zero h2 hxN (mem_imaginaryLieSubmodule.mp (hle hxN)) hx0))

/-- **The imaginary octonions are an irreducible representation of `Der 𝕆`.** Over a field in which
`2` is nonzero the `7`-dimensional Lie submodule `Im 𝕆` of
`TauCeti/Algebra/Octonion/Derivation.lean` is irreducible, so together with
`TauCeti.Octonion.finrank_imaginary` and
`TauCeti.Octonion.isFaithful_imaginaryLieSubmodule` it is the `7`-dimensional fundamental
representation of `G₂ = Der 𝕆`.

Where `2` vanishes the statement fails, by
`TauCeti.Octonion.not_isIrreducible_imaginaryLieSubmodule_of_two_eq_zero`: there `1` is imaginary
and is killed by every derivation, so it spans a Lie submodule of `Im 𝕆` that is neither `⊥` nor
`⊤`. -/
theorem isIrreducible_imaginaryLieSubmodule (h2 : (2 : K) ≠ 0) :
    LieModule.IsIrreducible K (derivationLieAlgebra K (Octonion K))
      (imaginaryLieSubmodule K) := by
  have hεmem : (⟨1, -1, 0, 0⟩ : Octonion K) ∈ imaginaryLieSubmodule K := by simp
  have hε0 : (⟨1, -1, 0, 0⟩ : Octonion K) ≠ 0 := fun h => by simpa using congrArg Octonion.a h
  have hnt : Nontrivial (imaginaryLieSubmodule K) :=
    (LieSubmodule.nontrivial_iff_ne_bot K _ _).mpr fun h =>
      hε0 ((LieSubmodule.eq_bot_iff _).mp h _ hεmem)
  refine LieModule.IsIrreducible.mk fun P hP => ?_
  have hinj : Function.Injective (imaginaryLieSubmodule K).incl :=
    LieSubmodule.injective_incl _
  have hle : P.map (imaginaryLieSubmodule K).incl ≤ imaginaryLieSubmodule K := by
    rw [LieSubmodule.map_le_iff_le_comap, LieSubmodule.comap_incl_self]
    exact le_top
  have hne : P.map (imaginaryLieSubmodule K).incl ≠ ⊥ := by
    intro h
    exact hP (LieSubmodule.map_injective_of_injective hinj (by rw [h, LieSubmodule.map_bot]))
  refine LieSubmodule.map_injective_of_injective hinj ?_
  rw [LieSubmodule.map_incl_top]
  exact eq_imaginaryLieSubmodule_of_le_of_ne_bot h2 hle hne

/-- **The imaginary octonions are an irreducible representation of `Der 𝕆`**, the instance form of
`TauCeti.Octonion.isIrreducible_imaginaryLieSubmodule`. -/
instance instIsIrreducibleImaginaryLieSubmodule [NeZero (2 : K)] :
    LieModule.IsIrreducible K (derivationLieAlgebra K (Octonion K))
      (imaginaryLieSubmodule K) :=
  isIrreducible_imaginaryLieSubmodule (NeZero.ne (2 : K))

end Field

/-! ### The hypothesis on `2` is necessary -/

section CharTwo

variable {R : Type*} [CommRing R] [Nontrivial R]

/-- **In characteristic `2` the imaginary octonions are reducible**, so the hypothesis `2 ≠ 0` of
`TauCeti.Octonion.isIrreducible_imaginaryLieSubmodule` cannot be dropped. Where `2` vanishes so does
`trace 1`, making `1` imaginary; a derivation kills `1`
(`TauCeti.derivationLieAlgebra.apply_one_eq_zero`), so `1` lies in the largest submodule
`LieModule.maxTrivSubmodule` on which `Der 𝕆` acts trivially, which therefore meets `Im 𝕆` in more
than `0`. It does not contain all of `Im 𝕆`: a lower vector derivation moves the imaginary octonion
`⟨0, 0, e₀, 0⟩` onto `-ε`, which is nonzero. -/
theorem not_isIrreducible_imaginaryLieSubmodule_of_two_eq_zero (h2 : (2 : R) = 0) :
    ¬ LieModule.IsIrreducible R (derivationLieAlgebra R (Octonion R))
      (imaginaryLieSubmodule R) := by
  intro h
  have h1 : (1 : Octonion R) ∈ imaginaryLieSubmodule R :=
    mem_imaginaryLieSubmodule.mpr (by rw [trace_one, h2])
  have h1triv : (1 : Octonion R) ∈
      LieModule.maxTrivSubmodule R (derivationLieAlgebra R (Octonion R)) (Octonion R) := by
    rw [LieModule.mem_maxTrivSubmodule]
    intro D
    simp
  rcases IsSimpleOrder.eq_bot_or_eq_top
      ((LieModule.maxTrivSubmodule R (derivationLieAlgebra R (Octonion R))
        (Octonion R)).comap (imaginaryLieSubmodule R).incl) with hbot | htop
  · rw [LieSubmodule.comap_incl_eq_bot] at hbot
    have hmem : (1 : Octonion R) ∈
        imaginaryLieSubmodule R ⊓ LieModule.maxTrivSubmodule R
          (derivationLieAlgebra R (Octonion R)) (Octonion R) := ⟨h1, h1triv⟩
    rw [hbot, LieSubmodule.mem_bot] at hmem
    simpa using congrArg Octonion.a hmem
  · rw [LieSubmodule.comap_incl_eq_top] at htop
    have hx : (⟨0, 0, Pi.single 0 1, 0⟩ : Octonion R) ∈ imaginaryLieSubmodule R := by simp
    have hzero := (LieModule.mem_maxTrivSubmodule _ _ _ _).mp (htop hx)
      (lowerDerivation (Pi.single 0 1))
    have ha := congrArg Octonion.a hzero
    simp only [LieSubalgebra.coe_bracket_of_module, Module.End.lie_apply,
      lowerDerivation_apply_a, zero_a, single_dotProduct, Pi.single_eq_same, mul_one,
      neg_eq_zero] at ha
    exact one_ne_zero ha

end CharTwo

end Octonion

end TauCeti
