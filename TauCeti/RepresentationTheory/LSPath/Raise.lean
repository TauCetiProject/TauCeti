/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.LSPath.Dual
public import TauCeti.RepresentationTheory.LSPath.Lower

import TauCeti.LinearAlgebra.RootSystem.Reduced

/-!
# Littelmann's raising operator preserves Lakshmibai–Seshadri paths

On piecewise-linear paths, `e_αᵢ` is conjugate to `f_αᵢ` by path reversal (`PLPath.raise_def`),
which on LS encodings is realized by `TauCeti.LSPath.dual` (`TauCeti.LSPath.toPLPath_dual`). Since
`-(w₀ • λ)` is dominant whenever `λ` is, stability of LS paths under `f_αᵢ`
(`TauCeti.LSPath.exists_toPLPath_eq_of_lower_eq_some`) yields stability under `e_αᵢ`.

## Main results

* `TauCeti.LSPath.exists_toPLPath_eq_of_raise_eq_some`,
  `TauCeti.LSPath.mem_range_toPLPath_of_raise_eq_some`.

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

/-- **Littelmann's raising operator preserves Lakshmibai–Seshadri paths of dominant shape.** -/
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

/-- The image of `TauCeti.LSPath.toPLPath` for dominant `λ` is closed under `PLPath.raise`. -/
theorem mem_range_toPLPath_of_raise_eq_some (hlam : lam ∈ dominantChamber P b) (f : M →+ V)
    (i : b.support) (F : Module.Dual 𝕜 V) (hF : ∀ m, F (f m) = (P.coroot' i m : 𝕜))
    {p q : PLPath 𝕜 V} (hp : p ∈ Set.range fun π : LSPath P b lam ↦ π.toPLPath 𝕜 f)
    (hq : PLPath.raise F (f (P.root i)) p = some q) :
    q ∈ Set.range fun π : LSPath P b lam ↦ π.toPLPath 𝕜 f := by
  rcases hp with ⟨π, rfl⟩; exact exists_toPLPath_eq_of_raise_eq_some π hlam f i F hF hq

end TauCeti.LSPath
