/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.LSPath.Dual
public import TauCeti.RepresentationTheory.LSPath.Lower
public import TauCeti.RepresentationTheory.LSPath.StringLength
public import TauCeti.RepresentationTheory.LSPath.Word

import TauCeti.LinearAlgebra.RootSystem.Reduced

/-!
# Littelmann's raising operator and operator words preserve Lakshmibai–Seshadri paths

Let `π` be a Lakshmibai–Seshadri path of dominant shape `λ` and `αᵢ` a simple root. On
piecewise-linear paths, Littelmann's raising operator `e_αᵢ` is conjugate to the lowering operator
`f_αᵢ` by path reversal (`TauCeti.PLPath.raise_def`): `e_αᵢ p = (f_αᵢ p.reverse).map reverse`.

On Lakshmibai–Seshadri encodings, path reversal is realized by Littelmann's duality
`TauCeti.LSPath.dual`, which sends `LSPath P b λ` to `LSPath P b (-(w₀ • λ))`
(`TauCeti.LSPath.toPLPath_dual`). When `λ` is dominant, `-(w₀ • λ)` is again dominant
(`TauCeti.neg_smul_mem_dominantChamber_longestElement`), so stability of Lakshmibai–Seshadri paths
under `f_αᵢ` (`TauCeti.LSPath.exists_toPLPath_eq_of_lower_eq_some`) immediately implies stability
under `e_αᵢ` (`TauCeti.LSPath.exists_toPLPath_eq_of_raise_eq_some`).

By induction along strings, operator words, and arbitrary mixed sequences of simple-root lowering
and raising steps, the set of realized Lakshmibai–Seshadri paths of dominant shape `λ` is closed
under all Littelmann root operators.

## Main results

* `TauCeti.LSPath.exists_toPLPath_eq_of_raise_eq_some`: **Littelmann's raising operator preserves
  Lakshmibai–Seshadri paths of dominant shape.**
* `TauCeti.LSPath.exists_toPLPath_eq_of_lowerIter_eq_some` and
  `TauCeti.LSPath.exists_toPLPath_eq_of_raiseIter_eq_some`: closure under iterated lowering and
  raising along a single simple root.
* `TauCeti.LSPath.exists_toPLPath_eq_of_lowerWord_eq_some` and
  `TauCeti.LSPath.exists_toPLPath_eq_of_raiseWord_eq_some`: closure under lowering and raising
  words.
* `TauCeti.LSPath.mem_range_toPLPath_of_reflTransGen`: closure of the realized LS paths under
  arbitrary mixed sequences of simple-root lowering and raising steps.

## References

* P. Littelmann, *A Littlewood–Richardson rule for symmetrizable Kac–Moody algebras*, Invent.
  Math. 116 (1994), 329--346, Section 4.
* P. Littelmann, *Paths and root operators in representation theory*, Ann. of Math. 142 (1995),
  499--525, Section 4.
-/

public section

namespace TauCeti.LSPath

open RootPairing

variable {ι M N : Type*} [AddCommGroup M] [AddCommGroup N]
  {P : RootPairing ι ℤ M N} {b : P.Base} [Finite ι] [P.IsReduced] {lam : M}
  {𝕜 V : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
  [AddCommGroup V] [Module 𝕜 V]

/-! ### Single-step and iterated raising stability -/

/-- **Littelmann's raising operator preserves Lakshmibai–Seshadri paths.** Let `π` be an LS path of
dominant shape `λ`, realized in `V` by `f`, let `αᵢ` be a simple root and let `F` be a form on `V`
inducing the simple coroot pairing `⟨-, αᵢ^∨⟩`. If the raising operator `e_αᵢ` is defined on the
path of `π`, then its result is again the path of an LS path of shape `λ`. -/
theorem exists_toPLPath_eq_of_raise_eq_some (π : LSPath P b lam)
    (hlam : lam ∈ dominantChamber P b) (f : M →+ V) (i : b.support) (F : Module.Dual 𝕜 V)
    (hF : ∀ m, F (f m) = (P.coroot' i m : 𝕜)) {q : PLPath 𝕜 V}
    (hq : PLPath.raise F (f (P.root i)) (π.toPLPath 𝕜 f) = some q) :
    ∃ π' : LSPath P b lam, π'.toPLPath 𝕜 f = q := by
  have := P.flip_isReduced
  rw [PLPath.raise_def, Option.map_eq_some_iff, ← toPLPath_dual] at hq
  obtain ⟨r, hr, rfl⟩ := hq
  obtain ⟨σ, rfl⟩ := exists_toPLPath_eq_of_lower_eq_some (dual π)
    (neg_smul_mem_dominantChamber_longestElement hlam) f i F hF hr
  exact ⟨dual.symm σ, toPLPath_dual_symm 𝕜 f σ⟩

/-- Iterated lowering along a simple root preserves Lakshmibai–Seshadri paths of dominant shape. -/
theorem exists_toPLPath_eq_of_lowerIter_eq_some (π : LSPath P b lam)
    (hlam : lam ∈ dominantChamber P b) (f : M →+ V) (i : b.support) (F : Module.Dual 𝕜 V)
    (hF : ∀ m, F (f m) = (P.coroot' i m : 𝕜)) {n : ℕ} {q : PLPath 𝕜 V}
    (hq : PLPath.lowerIter F (f (P.root i)) n (π.toPLPath 𝕜 f) = some q) :
    ∃ π' : LSPath P b lam, π'.toPLPath 𝕜 f = q := by
  have := P.flip_isReduced
  induction n generalizing π with
  | zero =>
    rw [PLPath.lowerIter_zero] at hq
    exact ⟨π, Option.some.inj hq⟩
  | succ n ih =>
    rw [PLPath.lowerIter_succ] at hq
    obtain ⟨r, hr, hq'⟩ := Option.bind_eq_some_iff.mp hq
    obtain ⟨π₁, rfl⟩ := exists_toPLPath_eq_of_lower_eq_some π hlam f i F hF hr
    exact ih π₁ hq'

/-- Iterated raising along a simple root preserves Lakshmibai–Seshadri paths of dominant shape. -/
theorem exists_toPLPath_eq_of_raiseIter_eq_some (π : LSPath P b lam)
    (hlam : lam ∈ dominantChamber P b) (f : M →+ V) (i : b.support) (F : Module.Dual 𝕜 V)
    (hF : ∀ m, F (f m) = (P.coroot' i m : 𝕜)) {n : ℕ} {q : PLPath 𝕜 V}
    (hq : PLPath.raiseIter F (f (P.root i)) n (π.toPLPath 𝕜 f) = some q) :
    ∃ π' : LSPath P b lam, π'.toPLPath 𝕜 f = q := by
  induction n generalizing π with
  | zero =>
    rw [PLPath.raiseIter_zero] at hq
    exact ⟨π, Option.some.inj hq⟩
  | succ n ih =>
    rw [PLPath.raiseIter_succ] at hq
    obtain ⟨r, hr, hq'⟩ := Option.bind_eq_some_iff.mp hq
    obtain ⟨π₁, rfl⟩ := exists_toPLPath_eq_of_raise_eq_some π hlam f i F hF hr
    exact ih π₁ hq'

/-! ### Closure under operator words and mixed root-operator steps -/

/-- Lowering along a word of simple roots preserves Lakshmibai–Seshadri paths of dominant shape. -/
theorem exists_toPLPath_eq_of_lowerWord_eq_some (π : LSPath P b lam)
    (hlam : lam ∈ dominantChamber P b) (f : M →+ V) (F : b.support → Module.Dual 𝕜 V)
    (hF : ∀ i m, F i (f m) = (P.coroot' i m : 𝕜)) {w : List b.support} {q : PLPath 𝕜 V}
    (hq : PLPath.lowerWord F (fun i ↦ f (P.root i)) w (π.toPLPath 𝕜 f) = some q) :
    ∃ π' : LSPath P b lam, π'.toPLPath 𝕜 f = q := by
  have := P.flip_isReduced
  induction w generalizing π with
  | nil =>
    rw [PLPath.lowerWord_nil] at hq
    exact ⟨π, Option.some.inj hq⟩
  | cons i w ih =>
    rw [PLPath.lowerWord_cons] at hq
    obtain ⟨r, hr, hq'⟩ := Option.bind_eq_some_iff.mp hq
    obtain ⟨π₁, rfl⟩ := exists_toPLPath_eq_of_lower_eq_some π hlam f i (F i) (hF i) hr
    exact ih π₁ hq'

/-- Raising along a word of simple roots preserves Lakshmibai–Seshadri paths of dominant shape. -/
theorem exists_toPLPath_eq_of_raiseWord_eq_some (π : LSPath P b lam)
    (hlam : lam ∈ dominantChamber P b) (f : M →+ V) (F : b.support → Module.Dual 𝕜 V)
    (hF : ∀ i m, F i (f m) = (P.coroot' i m : 𝕜)) {w : List b.support} {q : PLPath 𝕜 V}
    (hq : PLPath.raiseWord F (fun i ↦ f (P.root i)) w (π.toPLPath 𝕜 f) = some q) :
    ∃ π' : LSPath P b lam, π'.toPLPath 𝕜 f = q := by
  induction w generalizing π with
  | nil =>
    rw [PLPath.raiseWord_nil] at hq
    exact ⟨π, Option.some.inj hq⟩
  | cons i w ih =>
    rw [PLPath.raiseWord_cons] at hq
    obtain ⟨r, hr, hq'⟩ := Option.bind_eq_some_iff.mp hq
    obtain ⟨π₁, rfl⟩ := exists_toPLPath_eq_of_raise_eq_some π hlam f i (F i) (hF i) hr
    exact ih π₁ hq'

/-- The image of `TauCeti.LSPath.toPLPath` for dominant `λ` is closed under `PLPath.lower`. -/
theorem mem_range_toPLPath_of_lower_eq_some (hlam : lam ∈ dominantChamber P b) (f : M →+ V)
    (i : b.support) (F : Module.Dual 𝕜 V) (hF : ∀ m, F (f m) = (P.coroot' i m : 𝕜))
    {p q : PLPath 𝕜 V} (hp : p ∈ Set.range fun π : LSPath P b lam ↦ π.toPLPath 𝕜 f)
    (hq : PLPath.lower F (f (P.root i)) p = some q) :
    q ∈ Set.range fun π : LSPath P b lam ↦ π.toPLPath 𝕜 f := by
  have := P.flip_isReduced
  obtain ⟨π, rfl⟩ := hp
  exact exists_toPLPath_eq_of_lower_eq_some π hlam f i F hF hq

/-- The image of `TauCeti.LSPath.toPLPath` for dominant `λ` is closed under `PLPath.raise`. -/
theorem mem_range_toPLPath_of_raise_eq_some (hlam : lam ∈ dominantChamber P b) (f : M →+ V)
    (i : b.support) (F : Module.Dual 𝕜 V) (hF : ∀ m, F (f m) = (P.coroot' i m : 𝕜))
    {p q : PLPath 𝕜 V} (hp : p ∈ Set.range fun π : LSPath P b lam ↦ π.toPLPath 𝕜 f)
    (hq : PLPath.raise F (f (P.root i)) p = some q) :
    q ∈ Set.range fun π : LSPath P b lam ↦ π.toPLPath 𝕜 f := by
  obtain ⟨π, rfl⟩ := hp
  exact exists_toPLPath_eq_of_raise_eq_some π hlam f i F hF hq

/-- **The realized Lakshmibai–Seshadri paths of dominant shape `λ` are closed under arbitrary mixed
sequences of simple-root lowering and raising steps.** -/
theorem mem_range_toPLPath_of_reflTransGen (hlam : lam ∈ dominantChamber P b) (f : M →+ V)
    (F : b.support → Module.Dual 𝕜 V) (hF : ∀ i m, F i (f m) = (P.coroot' i m : 𝕜))
    {p q : PLPath 𝕜 V} (hp : p ∈ Set.range fun π : LSPath P b lam ↦ π.toPLPath 𝕜 f)
    (hpq : Relation.ReflTransGen
      (fun r s ↦ ∃ i : b.support,
        PLPath.lower (F i) (f (P.root i)) r = some s ∨
          PLPath.raise (F i) (f (P.root i)) r = some s) p q) :
    q ∈ Set.range fun π : LSPath P b lam ↦ π.toPLPath 𝕜 f := by
  induction hpq with
  | refl => exact hp
  | tail _ hstep ih =>
    obtain ⟨i, hlow | hraise⟩ := hstep
    · exact mem_range_toPLPath_of_lower_eq_some hlam f i (F i) (hF i) ih hlow
    · exact mem_range_toPLPath_of_raise_eq_some hlam f i (F i) (hF i) ih hraise

end TauCeti.LSPath
