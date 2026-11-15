/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Fredholm.LevelSet.Parametric
import TauCeti.Analysis.Calculus.FDeriv.Basic

/-!
# Global parametric transversality for Fredholm equations

Let `f : E × Λ → F` be a parametrized equation. A parameter `l` is regular at the level
`c` when the fixed-parameter linearization of `x ↦ f (x, l)` is surjective at every solution.
This file proves that the regular parameters form a residual, and hence dense, subset of `Λ`
provided the universal linearization is surjective and the fixed-parameter linearization is
Fredholm at every solution, and `f` is smooth enough there: of class `C^k` for Smale's
threshold `k > max (i, 0)`, where `i` is the index of the fixed-parameter linearization.

The file also introduces regularity on a subset `U ⊆ E × Λ`, which asks for surjectivity only at
the solutions lying in `U`. It reduces to regularity for `U = univ` and is monotone in `U`. The
finite-dimensional measure-zero form of the theorem in
`TauCeti.Analysis.Fredholm.LevelSet.FiniteDimensional` is stated for this variant.

The proof globalizes the local statement in
`TauCeti.Analysis.Fredholm.LevelSet.Parametric`. Around each solution, a level-set chart turns the
projection to `Λ` into `TauCeti.levelSetParameterMap`; local Sard--Smale puts its non-regular
values in a nowhere dense set. Second countability of the universal level set supplies a
countable subcover, so all non-regular parameters form a meagre set. Completeness of `Λ` then
makes the residual set of regular parameters dense by the Baire category theorem.

This is the parametric transversality theorem for maps between Banach spaces. Fredholm sections
of Banach bundles require a separate bundle-level extension.

## Main results

* `TauCeti.IsRegularParameter`: every solution at a parameter has surjective fixed-parameter
  linearization, which implies differentiability there
  (`TauCeti.IsRegularParameter.differentiableAt`).
* `TauCeti.IsRegularParameterOn`: the variant restricted to the solutions in a set `U`
  (`TauCeti.IsRegularParameterOn.differentiableAt`); it is
  `TauCeti.IsRegularParameter` for `U = univ` (`TauCeti.isRegularParameterOn_univ`), holds vacuously
  on `∅` (`TauCeti.isRegularParameterOn_empty`), distributes over binary and indexed unions
  (`TauCeti.isRegularParameterOn_union`, `TauCeti.isRegularParameterOn_iUnion`), is monotone in `U`
  (`TauCeti.IsRegularParameterOn.mono`), and depends only on the restriction to `U` when `U` is open
  (`IsOpen.isRegularParameterOn_congr`).
* `TauCeti.isMeagre_setOf_not_isRegularParameter`: the non-regular parameters of a universal
  Fredholm equation form a meagre set.
* `TauCeti.mem_residual_setOf_isRegularParameter`: the regular parameters form a residual set.
* `TauCeti.dense_setOf_isRegularParameter`: the regular parameters are dense.

## References

* D. McDuff, D. Salamon, *J-holomorphic Curves and Symplectic Topology*, 2nd ed., AMS Colloquium
  Publications 52, 2012, Appendix A.3.
* S. Smale, *An infinite dimensional version of Sard's theorem*, Amer. J. Math. 87 (1965),
  861--866.
-/

public section

open Filter Function Module Set
open scoped ContDiff Topology

namespace TauCeti

variable {E Λ F : Type*}
variable [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
variable [NormedAddCommGroup Λ] [NormedSpace ℝ Λ] [CompleteSpace Λ]
variable [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

/-- A parameter `l` is regular for the level equation `f (x, l) = c` when its fixed-parameter
linearization is surjective at every solution `x`.

This is deliberately a condition only on the `E` direction. Surjectivity of the total derivative
on `E × Λ`, used by the parametric transversality theorem, is a separate hypothesis. -/
def IsRegularParameter (f : E × Λ → F) (c : F) (l : Λ) : Prop :=
  ∀ x, f (x, l) = c →
    Surjective ((fderiv ℝ f (x, l)).comp (ContinuousLinearMap.inl ℝ E Λ))

omit [CompleteSpace E] [CompleteSpace Λ] [CompleteSpace F] in
/-- A parameter is regular exactly when the fixed-parameter derivatives are surjective
at all solutions of the level equation. -/
theorem isRegularParameter_iff {f : E × Λ → F} {c : F} {l : Λ} :
    IsRegularParameter f c l ↔ ∀ x, f (x, l) = c →
      Surjective ((fderiv ℝ f (x, l)).comp (ContinuousLinearMap.inl ℝ E Λ)) :=
  (Iff.rfl)

/-- A parameter `l` is regular on the set `U` for the level equation `f (x, l) = c` when its
fixed-parameter linearization is surjective at every solution `x` with `(x, l) ∈ U`.

This is `TauCeti.IsRegularParameter` with the solutions restricted to `U`; the two agree for
`U = univ` (`TauCeti.isRegularParameterOn_univ`). It is the form in which the finite-dimensional
parametric transversality theorem of `TauCeti.Analysis.Fredholm.LevelSet.FiniteDimensional` is
stated, whose universal equations are smooth and transverse only on a subset of their domain. -/
def IsRegularParameterOn (f : E × Λ → F) (U : Set (E × Λ)) (c : F) (l : Λ) : Prop :=
  ∀ x, (x, l) ∈ U → f (x, l) = c →
    Surjective ((fderiv ℝ f (x, l)).comp (ContinuousLinearMap.inl ℝ E Λ))

omit [CompleteSpace E] [CompleteSpace Λ] [CompleteSpace F] in
/-- A parameter is regular on `U` exactly when the fixed-parameter derivatives are surjective at
all solutions of the level equation in `U`. -/
theorem isRegularParameterOn_iff {f : E × Λ → F} {U : Set (E × Λ)} {c : F} {l : Λ} :
    IsRegularParameterOn f U c l ↔ ∀ x, (x, l) ∈ U → f (x, l) = c →
      Surjective ((fderiv ℝ f (x, l)).comp (ContinuousLinearMap.inl ℝ E Λ)) :=
  (Iff.rfl)

omit [CompleteSpace E] [CompleteSpace Λ] [CompleteSpace F] in
/-- Regularity on the whole space is regularity. -/
@[simp]
theorem isRegularParameterOn_univ {f : E × Λ → F} {c : F} {l : Λ} :
    IsRegularParameterOn f univ c l ↔ IsRegularParameter f c l :=
  ⟨fun h x hx ↦ h x (mem_univ _) hx, fun h x _ hx ↦ h x hx⟩

omit [CompleteSpace E] [CompleteSpace Λ] [CompleteSpace F] in
/-- Regularity on a set is inherited by its subsets. -/
theorem IsRegularParameterOn.mono {f : E × Λ → F} {U V : Set (E × Λ)} {c : F} {l : Λ}
    (hUV : U ⊆ V) (h : IsRegularParameterOn f V c l) : IsRegularParameterOn f U c l :=
  fun x hx hfx ↦ h x (hUV hx) hfx

omit [CompleteSpace E] [CompleteSpace Λ] [CompleteSpace F] in
/-- A regular parameter is regular on every set. -/
theorem IsRegularParameter.isRegularParameterOn {f : E × Λ → F} {U : Set (E × Λ)} {c : F}
    {l : Λ} (h : IsRegularParameter f c l) : IsRegularParameterOn f U c l :=
  (isRegularParameterOn_univ.2 h).mono (subset_univ U)

omit [CompleteSpace E] [CompleteSpace Λ] [CompleteSpace F] in
/-- Every parameter is vacuously regular on the empty set. -/
@[simp]
theorem isRegularParameterOn_empty (f : E × Λ → F) (c : F) (l : Λ) :
    IsRegularParameterOn f ∅ c l :=
  fun _ h ↦ False.elim h

omit [CompleteSpace E] [CompleteSpace Λ] [CompleteSpace F] in
/-- Regularity on a binary union holds if and only if it holds on each piece. -/
@[simp]
theorem isRegularParameterOn_union {f : E × Λ → F} {U V : Set (E × Λ)} {c : F} {l : Λ} :
    IsRegularParameterOn f (U ∪ V) c l ↔
      IsRegularParameterOn f U c l ∧ IsRegularParameterOn f V c l := by
  simp only [isRegularParameterOn_iff, mem_union]
  exact ⟨fun h ↦ ⟨fun x hU ↦ h x (.inl hU), fun x hV ↦ h x (.inr hV)⟩,
    fun ⟨hU, hV⟩ x hUV ↦ hUV.elim (hU x) (hV x)⟩

omit [CompleteSpace E] [CompleteSpace Λ] [CompleteSpace F] in
/-- Regularity on an indexed union holds if and only if it holds on each member. -/
@[simp]
theorem isRegularParameterOn_iUnion {ι : Sort*} {f : E × Λ → F} {U : ι → Set (E × Λ)}
    {c : F} {l : Λ} :
    IsRegularParameterOn f (⋃ i, U i) c l ↔ ∀ i, IsRegularParameterOn f (U i) c l := by
  simp only [isRegularParameterOn_iff, mem_iUnion, forall_exists_index]
  exact ⟨fun h i x hU ↦ h x i hU, fun h x i hU ↦ h i x hU⟩

omit [CompleteSpace E] [CompleteSpace Λ] [CompleteSpace F] in
/-- On an open set `U`, `TauCeti.IsRegularParameterOn` depends only on the values of `f` on `U`. -/
theorem _root_.IsOpen.isRegularParameterOn_congr {f g : E × Λ → F} {U : Set (E × Λ)}
    (hU : IsOpen U) {c : F} {l : Λ} (hEq : EqOn f g U) :
    IsRegularParameterOn f U c l ↔ IsRegularParameterOn g U c l := by
  rw [isRegularParameterOn_iff, isRegularParameterOn_iff]
  refine forall_congr' fun x ↦ imp_congr_right fun hxU ↦ ?_
  have hev : f =ᶠ[𝓝 (x, l)] g := hEq.eventuallyEq_of_mem (hU.mem_nhds hxU)
  rw [hEq hxU, hev.fderiv_eq]

omit [CompleteSpace E] [CompleteSpace Λ] [CompleteSpace F] in
/-- A regular parameter equation is differentiable at each solution in its specified set. -/
theorem IsRegularParameterOn.differentiableAt {f : E × Λ → F} {U : Set (E × Λ)}
    {c : F} {l : Λ} {x : E} (h : IsRegularParameterOn f U c l)
    (hxU : (x, l) ∈ U) (hx : f (x, l) = c) : DifferentiableAt ℝ f (x, l) := by
  have hs := isRegularParameterOn_iff.1 h x hxU hx
  rw [ContinuousLinearMap.coe_comp] at hs
  exact differentiableAt_of_fderiv_surjective hs.of_comp

omit [CompleteSpace E] [CompleteSpace Λ] [CompleteSpace F] in
/-- A regular parameter equation is differentiable at each solution. -/
theorem IsRegularParameter.differentiableAt {f : E × Λ → F} {c : F} {l : Λ} {x : E}
    (h : IsRegularParameter f c l) (hx : f (x, l) = c) : DifferentiableAt ℝ f (x, l) :=
  h.isRegularParameterOn.differentiableAt (mem_univ _) hx

/-- **Global parametric transversality.** The non-regular parameters of a sufficiently smooth
universal Fredholm equation form a meagre set.

The hypotheses are imposed only along the level set `f⁻¹(c)`. There the fixed-parameter
linearization must be Fredholm, the total linearization must be surjective, and the smoothness
order must meet Smale's threshold `n > max (index, 0)` for the index of the fixed-parameter
linearization. Second countability of the universal source makes the level set second countable
and hence allows the local nowhere dense exceptional sets to be reduced to a countable family. -/
theorem isMeagre_setOf_not_isRegularParameter [SecondCountableTopology (E × Λ)]
    {f : E × Λ → F} {c : F} {n : ℕ∞ω}
    (hcont : ∀ z, f z = c → ContDiffAt ℝ n f z)
    (hFred : ∀ z, f z = c →
      ContinuousLinearMap.IsFredholm
        ((fderiv ℝ f z).comp (ContinuousLinearMap.inl ℝ E Λ)))
    (htotal : ∀ z, f z = c → Surjective (fderiv ℝ f z))
    (hn : ∀ z, f z = c →
      ((((fderiv ℝ f z).comp (ContinuousLinearMap.inl ℝ E Λ)).index.toNat + 1 : ℕ) :
        ℕ∞ω) ≤ n) :
    IsMeagre {l | ¬ IsRegularParameter f c l} := by
  let S := {z : E × Λ | f z = c}
  -- Package the coordinate-level local theorem as a neighbourhood of each solution together
  -- with one nowhere dense exceptional set in the common parameter space.
  have hlocal := fun z : S => exists_mem_nhds_isNowhereDense_not_surjective_fderiv_comp_inl z
    (hcont z z.2) (hFred z z.2) (htotal z z.2) (hn z z.2)
  -- Second countability reduces this neighbourhood cover of the universal level set to a
  -- countable subcover.
  choose! Q hQnhds B hBnowhere hQB using hlocal
  obtain ⟨t, -, htcount, htcover⟩ := TopologicalSpace.countable_cover_nhdsWithin
    (f := Q) (s := (univ : Set S)) fun z _ ↦ nhdsWithin_le_nhds (hQnhds z)
  have hsub : {l | ¬ IsRegularParameter f c l} ⊆ ⋃ z ∈ t, B z := by
    intro l hl
    have hl' : ¬ IsRegularParameter f c l := hl
    simp only [IsRegularParameter] at hl'
    push Not at hl'
    obtain ⟨x, hx, hxbad⟩ := hl'
    let w : S := ⟨(x, l), hx⟩
    obtain ⟨z, hzt, hwQ⟩ := Set.mem_iUnion₂.1 (htcover (Set.mem_univ w))
    exact Set.mem_iUnion₂.2 ⟨z, hzt, hQB z w hwQ hxbad⟩
  exact IsMeagre.mono hsub
    (isMeagre_biUnion htcount fun z _ ↦ (hBnowhere z).isMeagre)

/-- The regular parameters of a sufficiently smooth universal Fredholm equation form a residual
set.

This is the complement formulation of
`TauCeti.isMeagre_setOf_not_isRegularParameter`. -/
theorem mem_residual_setOf_isRegularParameter [SecondCountableTopology (E × Λ)]
    {f : E × Λ → F} {c : F} {n : ℕ∞ω}
    (hcont : ∀ z, f z = c → ContDiffAt ℝ n f z)
    (hFred : ∀ z, f z = c →
      ContinuousLinearMap.IsFredholm
        ((fderiv ℝ f z).comp (ContinuousLinearMap.inl ℝ E Λ)))
    (htotal : ∀ z, f z = c → Surjective (fderiv ℝ f z))
    (hn : ∀ z, f z = c →
      ((((fderiv ℝ f z).comp (ContinuousLinearMap.inl ℝ E Λ)).index.toNat + 1 : ℕ) :
        ℕ∞ω) ≤ n) :
    {l | IsRegularParameter f c l} ∈ residual Λ := by
  simpa only [IsMeagre, Set.compl_ofPred, Classical.not_not] using
    isMeagre_setOf_not_isRegularParameter hcont hFred htotal hn

/-- The regular parameters of a sufficiently smooth universal Fredholm equation are dense.

This is the Baire-category consequence of
`TauCeti.mem_residual_setOf_isRegularParameter`. -/
theorem dense_setOf_isRegularParameter [SecondCountableTopology (E × Λ)]
    {f : E × Λ → F} {c : F} {n : ℕ∞ω}
    (hcont : ∀ z, f z = c → ContDiffAt ℝ n f z)
    (hFred : ∀ z, f z = c →
      ContinuousLinearMap.IsFredholm
        ((fderiv ℝ f z).comp (ContinuousLinearMap.inl ℝ E Λ)))
    (htotal : ∀ z, f z = c → Surjective (fderiv ℝ f z))
    (hn : ∀ z, f z = c →
      ((((fderiv ℝ f z).comp (ContinuousLinearMap.inl ℝ E Λ)).index.toNat + 1 : ℕ) :
        ℕ∞ω) ≤ n) :
    Dense {l | IsRegularParameter f c l} := by
  exact dense_of_mem_residual
    (mem_residual_setOf_isRegularParameter hcont hFred htotal hn)

end TauCeti

end
