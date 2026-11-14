/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.LSPath.Dual
public import TauCeti.RepresentationTheory.LSPath.Lower

/-!
# Littelmann's raising operator preserves Lakshmibai–Seshadri paths

By definition (`TauCeti.PLPath.raise_def`), Littelmann's raising operator `e_αᵢ` acts on a
piecewise-linear path `p` by reversing `p`, applying the lowering operator `f_αᵢ`, and reversing
back: `raise F x p = (lower F x p.reverse).map reverse`.

For a Lakshmibai–Seshadri path `π` of dominant shape `λ`, the dual path `π.dual hlam` of dominant
shape `-w₀ λ` realizes `(π.toPLPath 𝕜 f).reverse` (`TauCeti.LSPath.toPLPath_dual`). Stability of LS
paths of shape `-w₀ λ` under lowering (`TauCeti.LSPath.exists_toPLPath_eq_and_lower_eq_some`) and
duality (`TauCeti.LSPath.dualEquiv`) therefore imply that `e_αᵢ` preserves LS paths of shape `λ`,
and that the resulting LS path is independent of the chosen realization `(𝕜, V, f, F)`.

## Main results

* `TauCeti.LSPath.exists_toPLPath_eq_and_raise_eq_some`: **the raised LS path is independent of the
  chosen realization** `(𝕜, V, f, F)`.
* `TauCeti.LSPath.exists_toPLPath_eq_of_raise_eq_some`: **Littelmann's raising operator preserves
  Lakshmibai–Seshadri paths**.

## References

* P. Littelmann, *Paths and root operators in representation theory*, Ann. of Math. 142 (1995),
  §§1–2, 4.
-/

public section

namespace TauCeti.LSPath

open RootPairing

variable {ι M N 𝕜 V : Type*} [AddCommGroup M] [AddCommGroup N]
  {P : RootPairing ι ℤ M N} {b : P.Base} [Finite ι] [P.IsReduced]
  {lam : M} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
  [AddCommGroup V] [Module 𝕜 V]

/-- **The raised Lakshmibai–Seshadri path is independent of the realization.** If `e_αᵢ` is defined
on `π.toPLPath 𝕜 f` in some realization `(𝕜, V, f, F)`, there is an LS path `π'` of shape `λ`
presenting the raised path there such that in any other realization `(𝕜', V', f', F')` agreeing
with `⟨-, αᵢ^∨⟩`, `e_αᵢ` sends `π.toPLPath 𝕜' f'` to `π'.toPLPath 𝕜' f'`. -/
theorem exists_toPLPath_eq_and_raise_eq_some {𝕜' V' : Type*}
    [Field 𝕜'] [LinearOrder 𝕜'] [IsStrictOrderedRing 𝕜'] [AddCommGroup V'] [Module 𝕜' V']
    (π : LSPath P b lam) (hlam : lam ∈ dominantChamber P b)
    (f : M →+ V) (i : b.support) (F : Module.Dual 𝕜 V)
    (hF : ∀ m, F (f m) = (P.coroot' i m : 𝕜)) {q : PLPath 𝕜 V}
    (hq : PLPath.raise F (f (P.root i)) (π.toPLPath 𝕜 f) = some q)
    (f' : M →+ V') (F' : Module.Dual 𝕜' V')
    (hF' : ∀ m, F' (f' m) = (P.coroot' i m : 𝕜')) :
    ∃ π' : LSPath P b lam, π'.toPLPath 𝕜 f = q ∧
      PLPath.raise F' (f' (P.root i)) (π.toPLPath 𝕜' f') = some (π'.toPLPath 𝕜' f') := by
  have hlam' : -(longestElement P b • lam) ∈ dominantChamber P b :=
    neg_smul_mem_dominantChamber_longestElement_int hlam
  rw [PLPath.raise_def, ← toPLPath_dual 𝕜 f hlam π, Option.map_eq_some_iff] at hq
  obtain ⟨r, hlow, rfl⟩ := hq
  obtain ⟨ρ, hρ, hρ'⟩ :=
    (π.dual hlam).exists_toPLPath_eq_and_lower_eq_some hlam' f i F hF hlow f' F' hF'
  refine ⟨(dualEquiv hlam).symm ρ, ?_, ?_⟩
  · rw [toPLPath_dualEquiv_symm, hρ]
  · rw [PLPath.raise_def, ← toPLPath_dual 𝕜' f' hlam π, hρ', Option.map_some,
      toPLPath_dualEquiv_symm]

/-- **Littelmann's raising operator preserves Lakshmibai–Seshadri paths.** Let `π` be an LS path of
dominant shape `λ`, realized in `V` by `f`, let `αᵢ` be a simple root and let `F` be a form on `V`
inducing the simple coroot pairing `⟨-, αᵢ^∨⟩`. If the raising operator `e_αᵢ` is defined on the
path of `π`, then its result is again the path of an LS path of shape `λ`. -/
theorem exists_toPLPath_eq_of_raise_eq_some (π : LSPath P b lam)
    (hlam : lam ∈ dominantChamber P b) (f : M →+ V) (i : b.support) (F : Module.Dual 𝕜 V)
    (hF : ∀ m, F (f m) = (P.coroot' i m : 𝕜)) {q : PLPath 𝕜 V}
    (hq : PLPath.raise F (f (P.root i)) (π.toPLPath 𝕜 f) = some q) :
    ∃ π' : LSPath P b lam, π'.toPLPath 𝕜 f = q := by
  obtain ⟨π', hπ', -⟩ := π.exists_toPLPath_eq_and_raise_eq_some hlam f i F hF hq f F hF
  exact ⟨π', hπ'⟩

end TauCeti.LSPath
