/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Normed.Algebra.Amenable.Basic
public import TauCeti.Analysis.Normed.Algebra.VirtualDiagonal
import TauCeti.Analysis.Normed.Algebra.Amenable.ApproximateUnit
import TauCeti.Analysis.Normed.Algebra.Amenable.Bidual
import TauCeti.Analysis.Normed.Algebra.Derivation.Basic

/-!
# Johnson's diagonal characterizations of amenable Banach algebras

This file establishes B. E. Johnson's characterization of amenable Banach algebras in terms of
virtual and bounded approximate diagonals:

1. **Sufficiency of virtual and approximate diagonals.** By
   `TauCeti.IsVirtualDiagonal.exists_eq_dualAction_sub_dualAction` and
   `TauCeti.IsApproximateDiagonal.exists_eq_dualAction_sub_dualAction` (from
   `TauCeti.Analysis.Normed.Algebra.VirtualDiagonal`), every Banach algebra with a virtual diagonal
   (over a complete scalar field) or bounded approximate diagonal (over a proper scalar field) is
   amenable (`TauCeti.IsVirtualDiagonal.isAmenable`, `TauCeti.IsApproximateDiagonal.isAmenable`).
2. **Necessity of virtual and approximate diagonals.** Over `ℝ` or `ℂ`, given a bounded two-sided
   approximate identity `(eᵢ)` of an amenable Banach algebra `A`
   (`TauCeti.IsAmenable.exists_isApproximateUnit`),
   `CompletedProjectiveTensor.exists_bidual_mul_comp_mul'_eq_of_isApproximateUnit` (from
   `TauCeti.Analysis.Normed.Algebra.ApproximateDiagonal`) supplies a weak-star cluster point
   `E₀ ∈ (A ⊗̂π A)**` satisfying `a · Δ** E₀ = J_A a = Δ** E₀ · a`, so `a ↦ a · E₀ - E₀ · a` is
   a bounded derivation with values in `ker Δ**`. By Cohen–Hewitt factorization `Δ = mul' 𝕜 A` is
   surjective, so `TauCeti.IsAmenable.exists_mem_ker_precomp_precomp_eq_dualAction_sub` (from
   `TauCeti.Analysis.Normed.Algebra.Amenable.Bidual`) supplies `N ∈ ker Δ**` such that `M = E₀ - N`
   is a virtual diagonal, and bidual norm approximation turns `M` into a bounded approximate
   diagonal.

Consequently, for a Banach algebra `A` over `ℝ` or `ℂ`, amenability is equivalent to the existence
of a virtual diagonal and to the existence of a bounded approximate diagonal, and implies innerness
of bounded derivations into `E*` for seminormed bimodules `E` in arbitrary universes (see also
`TauCeti.Analysis.Normed.Algebra.Amenable.Cohomology` for `H¹(A, E*) = 0`).

## Main results

* `TauCeti.IsVirtualDiagonal.isAmenable` and `TauCeti.IsApproximateDiagonal.isAmenable`:
  sufficiency of virtual and bounded approximate diagonals for amenability.
* `TauCeti.IsAmenable.exists_isVirtualDiagonal` and
  `TauCeti.IsAmenable.exists_isApproximateDiagonal`: every amenable Banach algebra over `ℝ` or `ℂ`
  has a virtual diagonal and a bounded approximate diagonal.
* `TauCeti.isAmenable_iff_exists_isVirtualDiagonal` and
  `TauCeti.isAmenable_iff_exists_isApproximateDiagonal`: Johnson's diagonal characterizations of
  amenable Banach algebras over `ℝ` or `ℂ`.
* `TauCeti.IsAmenable.exists_eq_dualAction_sub_dualAction'`: universe-polymorphic innerness for
  amenable Banach algebras over `ℝ` or `ℂ`.

## References

* B. E. Johnson, *Cohomology in Banach algebras*, Mem. Amer. Math. Soc. 127 (1972).
* B. E. Johnson, *Approximate diagonals and cohomology of certain annihilator Banach algebras*,
  Amer. J. Math. 94 (1972), 685–698.
* V. Runde, *Lectures on Amenability*, Springer, 2002, §2.2, Theorem 2.2.4.
* H. G. Dales, *Banach Algebras and Automatic Continuity*, §§2.8–2.9.
-/

public section

noncomputable section

universe u v

open Filter NormedSpace Topology ContinuousLinearMap

namespace TauCeti

open CompletedProjectiveTensor

-- Shorten instance search for submodules and operators on iterated duals.
attribute [local instance] ContinuousLinearMap.strongDualSeminormedAddCommGroup
  ContinuousLinearMap.strongDualNormedSpace
  ContinuousLinearMap.strongBidualSeminormedAddCommGroup
  ContinuousLinearMap.strongBidualNormedSpace

section Amenable

variable {𝕜 : Type v} {A : Type u} [NontriviallyNormedField 𝕜] [NonUnitalNormedRing A]
  [NormedSpace 𝕜 A] [IsScalarTower 𝕜 A A] [SMulCommClass 𝕜 A A]

/-- A Banach algebra over a complete scalar field with a virtual diagonal is amenable. -/
theorem IsVirtualDiagonal.isAmenable [CompleteSpace 𝕜] [CompleteSpace A]
    {M : StrongDual 𝕜 (StrongDual 𝕜 (CompletedProjectiveTensor 𝕜 A A))}
    (hM : IsVirtualDiagonal 𝕜 M) : IsAmenable 𝕜 A :=
  isAmenable_def.2 fun _ _ _ _ _ _ hL hR hLR D hD ↦
    hM.exists_eq_dualAction_sub_dualAction hL hR hLR D hD

/-- A Banach algebra over a proper scalar field with a bounded approximate diagonal is amenable. -/
theorem IsApproximateDiagonal.isAmenable [ProperSpace 𝕜] [CompleteSpace A]
    {l : Filter (CompletedProjectiveTensor 𝕜 A A)} (h : IsApproximateDiagonal 𝕜 l) {C : ℝ}
    (hC : ∀ᶠ m in l, ‖m‖ ≤ C) : IsAmenable 𝕜 A :=
  isAmenable_def.2 fun _ _ _ _ _ _ hL hR hLR D hD ↦
    h.exists_eq_dualAction_sub_dualAction hC hL hR hLR D hD

end Amenable

section DiagonalCharacterization

variable {𝕜 : Type v} {A : Type u} [RCLike 𝕜] [NonUnitalNormedRing A]
  [NormedSpace 𝕜 A] [IsScalarTower 𝕜 A A] [SMulCommClass 𝕜 A A] [CompleteSpace A]

/-- In an amenable Banach algebra `A` over `ℝ` or `ℂ` with surjective multiplication map
`Δ = mul' 𝕜 A`, if `E₀ ∈ (A ⊗̂π A)**` satisfies `E₀ (f ∘ Δ ∘ mulLeft a) = E₀ (f ∘ Δ ∘ mulRight a)`
for all `a : A` and `f ∈ A*`, then there is `N ∈ (A ⊗̂π A)**` with `Δ** N = 0` and the same outer
commutator as `E₀`. -/
private theorem IsAmenable.exists_ker_mul'_eq_commutator
    (h : IsAmenable 𝕜 A) (hsurj : Function.Surjective (mul' 𝕜 A))
    (E₀ : StrongDual 𝕜 (StrongDual 𝕜 (CompletedProjectiveTensor 𝕜 A A)))
    (hE₀ : ∀ (a : A) (f : StrongDual 𝕜 A),
      E₀ ((f.comp (mul' 𝕜 A)).comp (mulLeft 𝕜 A a)) =
        E₀ ((f.comp (mul' 𝕜 A)).comp (mulRight 𝕜 A a))) :
    ∃ N : StrongDual 𝕜 (StrongDual 𝕜 (CompletedProjectiveTensor 𝕜 A A)),
      precomp 𝕜 (precomp 𝕜 (mul' 𝕜 A)) N = 0 ∧
      ∀ a : A,
        dualAction (dualAction (mulLeft 𝕜 A)) a N -
          dualAction (dualAction (mulRight 𝕜 A)) a N =
        dualAction (dualAction (mulLeft 𝕜 A)) a E₀ -
          dualAction (dualAction (mulRight 𝕜 A)) a E₀ := by
  have hclosed : IsClosed ((mul' 𝕜 A).range : Set A) := by
    rw [LinearMap.range_eq_top.mpr hsurj]
    exact isClosed_univ
  let D₀ : A →L[𝕜] StrongDual 𝕜 (StrongDual 𝕜 (CompletedProjectiveTensor 𝕜 A A)) :=
    (dualAction (dualAction (mulLeft 𝕜 A))).flip E₀ -
      (dualAction (dualAction (mulRight 𝕜 A))).flip E₀
  obtain ⟨N, hN_ker, hN_comm⟩ := h.exists_mem_ker_precomp_precomp_eq_dualAction_sub hclosed
    (mulLeft_mul_apply (𝕜 := 𝕜) (A := A))
    (mulRight_mul_apply (𝕜 := 𝕜) (A := A))
    (mulLeft_mulRight_apply_comm (𝕜 := 𝕜) (A := A))
    (fun a x hx ↦ by
      simp only [LinearMap.mem_ker, coe_coe] at hx ⊢
      rw [mul'_mulLeft_apply, hx, mul_zero])
    (fun a x hx ↦ by
      simp only [LinearMap.mem_ker, coe_coe] at hx ⊢
      rw [mul'_mulRight_apply, hx, zero_mul])
    D₀
    (flip_sub_flip_mul_apply
      (dualAction_mul_apply_of_right
        (dualAction_mul_apply_of_left (mulLeft_mul_apply (𝕜 := 𝕜) (A := A))))
      (dualAction_mul_apply_of_left
        (dualAction_mul_apply_of_right (mulRight_mul_apply (𝕜 := 𝕜) (A := A))))
      (dualAction_apply_dualAction_apply_comm
        (dualAction_apply_dualAction_apply_comm (mulLeft_mulRight_apply_comm (𝕜 := 𝕜) (A := A))))
      E₀)
    fun a ↦ by
      rw [LinearMap.mem_ker]
      ext f
      simpa only [D₀, coe_coe, precomp_apply, comp_apply, sub_apply, flip_apply,
        dualAction_dualAction_apply_apply, sub_eq_zero, zero_apply] using hE₀ a f
  exact ⟨N, LinearMap.mem_ker.mp hN_ker, fun a ↦ by
    simpa only [D₀, sub_apply, flip_apply] using (hN_comm a).symm⟩

/-- **Amenability implies the existence of a virtual diagonal.** Every amenable Banach algebra over
`ℝ` or `ℂ` has a virtual diagonal `M ∈ (A ⊗̂π A)**`. -/
theorem IsAmenable.exists_isVirtualDiagonal (h : IsAmenable 𝕜 A) :
    ∃ M : StrongDual 𝕜 (StrongDual 𝕜 (CompletedProjectiveTensor 𝕜 A A)),
      IsVirtualDiagonal 𝕜 M := by
  obtain ⟨C, l, hl, hC⟩ := h.exists_isApproximateUnit
  have := hl.neBot
  obtain ⟨E₀, hE₀L, hE₀R⟩ :=
    exists_bidual_mul_comp_mul'_eq_of_isApproximateUnit (𝕜 := 𝕜) hl hC
  have hE₀ (a : A) (f : StrongDual 𝕜 A) :
      E₀ ((f.comp (mul' 𝕜 A)).comp (mulLeft 𝕜 A a)) =
        E₀ ((f.comp (mul' 𝕜 A)).comp (mulRight 𝕜 A a)) := by
    rw [comp_assoc, mul'_comp_mulLeft, ← comp_assoc, hE₀L,
      comp_assoc, mul'_comp_mulRight, ← comp_assoc, hE₀R]
  obtain ⟨N, hN0, hNcomm⟩ :=
    h.exists_ker_mul'_eq_commutator (mul'_surjective hC hl.tendsto_mul_right) E₀ hE₀
  refine ⟨E₀ - N, ⟨fun a ↦ ?_, fun a ↦ ?_⟩⟩
  · simpa only [map_sub] using sub_eq_sub_iff_sub_eq_sub.2 (hNcomm a).symm
  · rw [map_sub, hN0, sub_zero]
    ext f
    simpa only [dualAction_dualAction_apply_apply, precomp_apply, comp_apply, dual_def]
      using hE₀L a f

/-- **Amenability implies the existence of a bounded approximate diagonal.** Every amenable Banach
algebra over `ℝ` or `ℂ` has a bounded approximate diagonal. -/
theorem IsAmenable.exists_isApproximateDiagonal (h : IsAmenable 𝕜 A) :
    ∃ (C : ℝ) (l : Filter (CompletedProjectiveTensor 𝕜 A A)),
      IsApproximateDiagonal 𝕜 l ∧ ∀ᶠ m in l, ‖m‖ ≤ C :=
  let ⟨M, hM⟩ := h.exists_isVirtualDiagonal
  ⟨‖M‖, hM.exists_isApproximateDiagonal⟩

/-- **Johnson's virtual-diagonal characterization of amenability.** A Banach algebra over `ℝ` or
`ℂ` is amenable if and only if it has a virtual diagonal in `(A ⊗̂π A)**`. -/
theorem isAmenable_iff_exists_isVirtualDiagonal :
    IsAmenable 𝕜 A ↔
      ∃ M : StrongDual 𝕜 (StrongDual 𝕜 (CompletedProjectiveTensor 𝕜 A A)),
        IsVirtualDiagonal 𝕜 M :=
  ⟨fun h ↦ h.exists_isVirtualDiagonal, fun ⟨_, hM⟩ ↦ hM.isAmenable⟩

/-- **Johnson's approximate-diagonal characterization of amenability.** A Banach algebra over `ℝ`
or `ℂ` is amenable if and only if it has a bounded approximate diagonal. -/
theorem isAmenable_iff_exists_isApproximateDiagonal :
    IsAmenable 𝕜 A ↔
      ∃ (C : ℝ) (l : Filter (CompletedProjectiveTensor 𝕜 A A)),
        IsApproximateDiagonal 𝕜 l ∧ ∀ᶠ m in l, ‖m‖ ≤ C :=
  isAmenable_iff_exists_isVirtualDiagonal.trans
    exists_isVirtualDiagonal_iff_exists_isApproximateDiagonal

/-- Universe-polymorphic innerness for amenable Banach algebras over `ℝ` or `ℂ`: every bounded
derivation into the dual `E*` of a seminormed `A`-bimodule `E` in *any* universe (without requiring
completeness of `E`) is inner. -/
theorem IsAmenable.exists_eq_dualAction_sub_dualAction' (h : IsAmenable 𝕜 A) {E : Type*}
    [SeminormedAddCommGroup E] [NormedSpace 𝕜 E] {L R : A →L[𝕜] E →L[𝕜] E}
    (hL : ∀ a b x, L (a * b) x = L a (L b x)) (hR : ∀ a b x, R (a * b) x = R b (R a x))
    (hLR : ∀ a b x, L a (R b x) = R b (L a x)) (D : A →L[𝕜] StrongDual 𝕜 E)
    (hD : ∀ a b, D (a * b) = dualAction R a (D b) + dualAction L b (D a)) :
    ∃ φ : StrongDual 𝕜 E, ∀ a, D a = dualAction R a φ - dualAction L a φ :=
  let ⟨_, hM⟩ := h.exists_isVirtualDiagonal
  hM.exists_eq_dualAction_sub_dualAction hL hR hLR D hD

end DiagonalCharacterization

end TauCeti
