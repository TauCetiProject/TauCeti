/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import TauCeti.Analysis.Complex.UpperHalfPlane.PSLAction
public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Map
-- supplies `UpperHalfPlane.forall_smul_eq_self_iff_mem_center`, which identifies the kernel
import Mathlib.Analysis.Complex.UpperHalfPlane.FixedPoints

/-!
# The rational projective action on the upper half-plane

`GL(2, ℚ)⁺` does not act on `ℍ`; `PSL(2, ℝ)` does. This file supplies the homomorphism
between them, `ratPosToPSL2R`, and identifies its kernel on the determinant-one locus.

Hecke operators are indexed by double cosets of matrices with *rational* entries, so every
geometric statement about them has to be pushed along such a homomorphism before Mathlib's
`ℍ`-API applies. The change of scalars `GL(2, ℚ) →* GL(2, ℝ)` alone will not do: it is
injective, so it keeps `-1`, which acts trivially on `ℍ`. Anything demanding a *faithful*
action — `MeasureTheory.IsFundamentalDomain` in particular, whose a.e.-disjointness clause
is `Pairwise` over group elements — is then unsatisfiable. Passing to `PSL(2, ℝ)` collapses
exactly the scalars, and `eq_one_or_neg_one_of_mem_ratPosToPSL2R_ker_of_det_eq_one` says that on the
determinant-one locus nothing else is lost: an element of the kernel with determinant one is
`±1`. (Only that containment is proved here; the converse, that `±1` do lie in the kernel, is not
needed by any consumer and is not claimed.)

## Main definitions

* `TauCeti.ratPosToRealPos`: the change of scalars `GL(2, ℚ)⁺ →* GL(2, ℝ)⁺`.
* `TauCeti.ratPosToPSL2R`: the composite `GL(2, ℚ)⁺ →* GL(2, ℝ)⁺ →* PSL(2, ℝ)`.

## Main results

* `UpperHalfPlane.ratPosToPSL2R_smul`: `ratPosToPSL2R g` acts on `ℍ` as the real matrix does.
* `TauCeti.eq_one_or_neg_one_of_mem_ratPosToPSL2R_ker_of_det_eq_one`: an element of
  `ker ratPosToPSL2R` with determinant one is `±1` — a containment, not an identification.
* `TauCeti.ratPosToPSL2R_ker_inf_le`: the consequence consumers apply —
  `ker ratPosToPSL2R ⊓ H ≤ Γ` whenever `H` lies in the determinant-one locus and `-1 ∈ Γ`, which
  holds of every `Γ₀(N)`.

## References

* [DS] Diamond–Shurman, *A First Course in Modular Forms*, §5.5
-/

public section

open Matrix UpperHalfPlane

open scoped MatrixGroups

namespace TauCeti

/-- The change of scalars `GL(2, ℚ)⁺ →* GL(2, ℝ)⁺`, the restriction of
`Matrix.GeneralLinearGroup.map (algebraMap ℚ ℝ)` to the positive-determinant subgroups. Its
underlying `GL (Fin 2) ℝ` matrix is that map applied to `g` definitionally, so a goal mixing
the two spellings closes by `rfl`. -/
noncomputable def ratPosToRealPos : GL(2, ℚ)⁺ →* GL(2, ℝ)⁺ :=
  (Matrix.GeneralLinearGroup.map (algebraMap ℚ ℝ)).restrict fun _ ↦
    Matrix.GeneralLinearGroup.map_mem_glpos Rat.cast_strictMono

/-- The underlying `GL (Fin 2) ℝ` matrix of `ratPosToRealPos g` is the entrywise change of
scalars `ℚ → ℝ` applied to `g`. -/
-- `by rfl`, not `rfl`: `ratPosToRealPos` is not `@[expose]`, so a theorem exported from this
-- module cannot unfold it in term mode.
@[simp]
theorem coe_ratPosToRealPos (g : GL(2, ℚ)⁺) :
    (ratPosToRealPos g : GL (Fin 2) ℝ) =
      Matrix.GeneralLinearGroup.map (algebraMap ℚ ℝ) (g : GL (Fin 2) ℚ) := by rfl

/-- **The rational projective action.** `GL(2, ℚ)⁺` acts on `ℍ` through `PSL(2, ℝ)`: the change
of scalars `ratPosToRealPos` followed by the projectivization `glPosToPSL2R`. Compute the
action with `UpperHalfPlane.ratPosToPSL2R_smul`; unlike `ratPosToRealPos` this map is
deliberately *not* injective, as it collapses the scalar matrices, which act trivially on `ℍ`. -/
noncomputable def ratPosToPSL2R : GL(2, ℚ)⁺ →* PSL(2, ℝ) := glPosToPSL2R.comp ratPosToRealPos

/-- `ratPosToPSL2R g` acts on `ℍ` exactly as the real matrix `g` does. Rewriting with this
turns a goal about the `PSL(2, ℝ)`-action into one about Mathlib's `GL(2, ℝ)`-action on `ℍ`;
it is the `ℚ`-coefficient counterpart of `UpperHalfPlane.glPosToPSL2R_smul`. -/
@[simp]
theorem _root_.UpperHalfPlane.ratPosToPSL2R_smul (g : GL(2, ℚ)⁺) (τ : ℍ) :
    ratPosToPSL2R g • τ =
      Matrix.GeneralLinearGroup.map (algebraMap ℚ ℝ) (g : GL (Fin 2) ℚ) • τ := by
  unfold ratPosToPSL2R
  rw [MonoidHom.comp_apply, glPosToPSL2R_smul]
  -- the last step is `coe_ratPosToRealPos` under the action, not a definitional unfolding
  exact congrArg (fun m : GL (Fin 2) ℝ ↦ m • τ) (coe_ratPosToRealPos g)

/-- An element of `ker ratPosToPSL2R` has central real image.

Central in `GL (Fin 2) ℝ` means scalar (`Matrix.GeneralLinearGroup.center_eq_range_scalar`), so
this alone pins the image down only up to a scalar; adding determinant one cuts it to `±1` —
that stronger form is `eq_one_or_neg_one_of_mem_ratPosToPSL2R_ker_of_det_eq_one`. -/
theorem map_mem_center_of_mem_ratPosToPSL2R_ker {g : GL(2, ℚ)⁺} (hg : g ∈ ratPosToPSL2R.ker) :
    Matrix.GeneralLinearGroup.map (algebraMap ℚ ℝ) (g : GL (Fin 2) ℚ) ∈ Subgroup.center
      (GL (Fin 2) ℝ) :=
  -- the real matrix acts on `ℍ` exactly as its projective class does, and that class is `1`
  UpperHalfPlane.forall_smul_eq_self_iff_mem_center.mp fun τ ↦ by
    rw [← ratPosToPSL2R_smul, MonoidHom.mem_ker.mp hg, one_smul]

/-- **On the determinant-one locus, a kernel element is `±1`.**

This is one containment only; nothing here says `±1` lie in the kernel, and no consumer needs
that. Use it to discharge `ratPosToPSL2R.ker ⊓ H ≤ Γ` whenever `H` lies in the determinant-one
locus and `Γ` contains `±1` — every `Γ₀(N)`, in particular. Without `hdet` only
`map_mem_center_of_mem_ratPosToPSL2R_ker` is available, and that pins the image down to a
scalar, no further. -/
theorem eq_one_or_neg_one_of_mem_ratPosToPSL2R_ker_of_det_eq_one {g : GL(2, ℚ)⁺}
    (hg : g ∈ ratPosToPSL2R.ker)
    (hdet : ((g : GL (Fin 2) ℚ) : Matrix (Fin 2) (Fin 2) ℚ).det = 1) :
    (g : GL (Fin 2) ℚ) = 1 ∨ (g : GL (Fin 2) ℚ) = -1 := by
  -- central in `GL(2, ℝ)` means scalar
  obtain ⟨c, hcs⟩ :=
    Matrix.GeneralLinearGroup.center_eq_range_scalar.le (map_mem_center_of_mem_ratPosToPSL2R_ker hg)
  -- a scalar of determinant one has scalar `±1`
  have hc2 : c = 1 ∨ c = -1 := by
    have hsq : (c : ℝ) ^ 2 = 1 := by
      simpa [Matrix.GeneralLinearGroup.map_det, hdet]
        using congrArg Units.val (congrArg Matrix.GeneralLinearGroup.det hcs)
    exact (sq_eq_one_iff.mp hsq).imp Units.ext Units.ext
  -- and the change of scalars is injective
  refine hc2.imp ?_ ?_ <;> rintro rfl <;>
    exact Matrix.GeneralLinearGroup.map_injective (algebraMap ℚ ℝ).injective <| by
      simpa [Units.ext_iff, ← RingHom.mapMatrix_apply, -Matrix.scalar_apply] using hcs.symm

/-- **The kernel meets the determinant-one locus inside any `Γ` containing `-1`.**

This is the consequence of `eq_one_or_neg_one_of_mem_ratPosToPSL2R_ker_of_det_eq_one` that
consumers actually apply: it is the `hker` hypothesis of the Hecke-coset tiling
`HeckeRing.GL2.isFundamentalDomain_iUnion_rightCosetRep_smul`, and without it every call site
repeats the same two-case split.

Only `-1 ∈ Γ` is asked for; the `1` branch is discharged internally by `Γ.one_mem`. Every
`Γ₀(N)` contains `-1`, whose lower-left entry is zero. **`Γ₁(N)` does not**, except at `N ∣ 2`:
`-1` has diagonal `(-1, -1)` and `Γ₁(N)` asks for `≡ (1, 1)`. A consumer whose `Γ` is a `Γ₁(N)`
therefore cannot use this lemma at `N ≥ 3`, and indeed `ker ratPosToPSL2R ⊓ H ≤ Γ₁(N)` is false
there, since `-1` lies in the kernel.

The form a consumer actually wants is `Γ.withCenter`, which adjoins the centre and so contains
`-1` for every `Γ`. That is the shape the Petersson layer works in — `peterssonInnerCosets` sums
over `SL(2, ℤ) ⧸ Γ.withCenter` — so the hypothesis is satisfiable exactly where it is needed.

`hH` is stated on the underlying matrix because that is the form in which the determinant
condition defining the locus arrives. -/
theorem ratPosToPSL2R_ker_inf_le {H Γ : Subgroup GL(2, ℚ)⁺}
    (hH : ∀ g ∈ H, ((g : GL (Fin 2) ℚ) : Matrix (Fin 2) (Fin 2) ℚ).det = 1)
    (hneg : (-1 : GL(2, ℚ)⁺) ∈ Γ) :
    ratPosToPSL2R.ker ⊓ H ≤ Γ := by
  rintro g ⟨hk, hm⟩
  rcases eq_one_or_neg_one_of_mem_ratPosToPSL2R_ker_of_det_eq_one hk (hH g hm) with h | h
  · exact (Subtype.ext h : g = 1) ▸ Γ.one_mem
  · exact (Subtype.ext h : g = -1) ▸ hneg


end TauCeti
