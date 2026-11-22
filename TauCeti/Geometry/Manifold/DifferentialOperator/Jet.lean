/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.DifferentialOperator.Section
public import TauCeti.Geometry.Manifold.VectorBundle.Jet.VanishingIdeal

/-!
# Differential operators factor through jet bundles

Let `V` and `W` be smooth real vector bundles over a finite-dimensional Hausdorff boundaryless
smooth manifold `M`, with `V` of finite rank. A real-linear map `P : Γ(V) → Γ(W)` between the
modules of smooth sections is a differential operator of order at most `r` in Grothendieck's sense
(`TauCeti.differentialOperators`) when all its `(r + 1)`-fold commutators with multiplication by
smooth functions vanish. No continuity of `P` is assumed.

Such an operator factors through the bundle `JᵣV` of `r`-jets (`TauCeti.JetBundle`): at every
point `x` there is a unique real-linear map `A_x : (JᵣV)_x → W_x` with

`(P s)(x) = A_x (jʳs(x))`

for every smooth section `s`, where `jʳs(x)` is the `r`-jet of `s` at `x`. Conversely, when `W`
also has finite rank, a linear map `P` of this form is a differential operator of order at most
`r`. So for operators between sections of finite-rank bundles, the algebraic order filtration by
iterated commutators agrees with the order filtration by factorization through jets.

The proof combines two identifications of the same filtration. An operator of order at most `r`
sends `I_x ^ (r + 1) Γ(V)` into `I_x Γ(W)`, where `I_x` is the ideal of smooth functions vanishing
at `x`, and the sections of `W` in `I_x Γ(W)` are those vanishing at `x`
(`TauCeti.mem_differentialOperators_section_iff_forall_apply_eq_zero`). The sections of `V` in
`I_x ^ (r + 1) Γ(V)` are those with vanishing `r`-jet at `x`
(`TauCeti.JetBundle.jet_eq_zero_iff_mem_smoothVanishingIdeal_pow_smul_top`), and every `r`-jet at
`x` is the jet of a smooth section (`TauCeti.JetBundle.jetLinearMap_surjective`).

## Main definitions and results

* `TauCeti.differentialOperators_section_apply_eq_of_jet_eq`: a differential operator of order at
  most `r` takes the same value at `x` on two smooth sections with the same `r`-jet at `x`.
* `TauCeti.mem_differentialOperators_section_iff_forall_jet_eq`: for `W` of finite rank, this
  characterizes the differential operators of order at most `r`.
* `LinearMap.jetFactorOfMemDifferentialOperators`: the fibrewise linear map `(JᵣV)_x → W_x`
  through which a differential operator of order at most `r` factors at `x`, characterized by
  `LinearMap.jetFactorOfMemDifferentialOperators_jet` and
  `LinearMap.eq_jetFactorOfMemDifferentialOperators`.
* `TauCeti.mem_differentialOperators_section_iff_exists_linearMap`: for `W` of finite rank, the
  differential operators of order at most `r` are exactly the linear maps that factor at each point
  through a linear map on the fibre of `JᵣV`.

## References

* A. Grothendieck, *Éléments de géométrie algébrique IV*, Quatrième partie, §16.8.
* I. Kolář, P. W. Michor and J. Slovák, *Natural Operations in Differential Geometry*,
  §§12.2–12.5.
-/

public section

noncomputable section

open Bundle
open scoped ContDiff Manifold

namespace TauCeti

open JetBundle

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {V : M → Type*} [TopologicalSpace (TotalSpace F V)]
  [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)] [∀ x, TopologicalSpace (V x)]
  [FiberBundle F V] [VectorBundle ℝ F V] [ContMDiffVectorBundle ∞ F V I]
  {F' : Type*} [NormedAddCommGroup F'] [NormedSpace ℝ F']
  {W : M → Type*} [TopologicalSpace (TotalSpace F' W)]
  [∀ x, AddCommGroup (W x)] [∀ x, Module ℝ (W x)] [∀ x, TopologicalSpace (W x)]
  [FiberBundle F' W] [VectorBundle ℝ F' W] {r : ℕ}

/-- **Differential operators factor through jets.** A differential operator of order at most `r`
between sections, in Grothendieck's sense of iterated commutators with multiplication operators,
takes the same value at `x` on two smooth sections with the same `r`-jet at `x`. -/
theorem differentialOperators_section_apply_eq_of_jet_eq
    {P : Cₛ^∞⟮I; F, V⟯ →ₗ[ℝ] Cₛ^∞⟮I; F', W⟯}
    (hP : P ∈ differentialOperators ℝ C^∞⟮I, M; ℝ⟯ Cₛ^∞⟮I; F, V⟯ Cₛ^∞⟮I; F', W⟯ r) {x : M}
    {s t : Cₛ^∞⟮I; F, V⟯} (hst : jet I F r s x = jet I F r t x) : P s x = P t x := by
  have h := apply_eq_zero_of_mem_smoothVanishingIdeal_smul_top
    (apply_mem_smul_top_of_mem_pow_smul_top hP _
      ((jet_eq_jet_iff_sub_mem_smoothVanishingIdeal_pow_smul_top s t).1 hst))
  rwa [map_sub, ContMDiffSection.coe_sub, Pi.sub_apply, sub_eq_zero] at h

/-- **Differential operators are the operators that factor through jets.** For a smooth real
vector bundle `W` of finite rank, a linear map `P : Γ(V) → Γ(W)` is a differential operator of
order at most `r` in Grothendieck's sense if and only if, at every point `x`, the value `(P s)(x)`
only depends on the `r`-jet of `s` at `x`. -/
theorem mem_differentialOperators_section_iff_forall_jet_eq
    [FiniteDimensional ℝ F'] [ContMDiffVectorBundle ∞ F' W I]
    {P : Cₛ^∞⟮I; F, V⟯ →ₗ[ℝ] Cₛ^∞⟮I; F', W⟯} :
    P ∈ differentialOperators ℝ C^∞⟮I, M; ℝ⟯ Cₛ^∞⟮I; F, V⟯ Cₛ^∞⟮I; F', W⟯ r ↔
      ∀ x (s t : Cₛ^∞⟮I; F, V⟯), jet I F r s x = jet I F r t x → P s x = P t x := by
  refine ⟨fun hP x s t ↦ differentialOperators_section_apply_eq_of_jet_eq hP, fun hP ↦ ?_⟩
  rw [mem_differentialOperators_section_iff_forall_apply_eq_zero]
  intro x s hs
  have h := hP x s 0 (by
    rw [jet_eq_zero_of_mem_smoothVanishingIdeal_pow_smul_top hs, ContMDiffSection.coe_zero,
      jet_zero])
  rwa [map_zero, ContMDiffSection.coe_zero, Pi.zero_apply] at h

/-- The **jet factor** of a differential operator `P : Γ(V) → Γ(W)` of order at most `r` at a
point `x`: the real-linear map `(JᵣV)_x → W_x` sending the `r`-jet `jʳs(x)` of a smooth section
`s` to `(P s)(x)` (`LinearMap.jetFactorOfMemDifferentialOperators_jet`). It is the unique such map
(`LinearMap.eq_jetFactorOfMemDifferentialOperators`). -/
def _root_.LinearMap.jetFactorOfMemDifferentialOperators (P : Cₛ^∞⟮I; F, V⟯ →ₗ[ℝ] Cₛ^∞⟮I; F', W⟯)
    (hP : P ∈ differentialOperators ℝ C^∞⟮I, M; ℝ⟯ Cₛ^∞⟮I; F, V⟯ Cₛ^∞⟮I; F', W⟯ r) (x : M) :
    JetBundle I F V r x →ₗ[ℝ] W x :=
  (LinearMap.ker (jetLinearMap I F V r x)).liftQ (ContMDiffSection.evalLinearMap I F' ∞ W x ∘ₗ P)
      (fun s hs ↦ by
        rw [LinearMap.mem_ker, jetLinearMap_apply] at hs
        rw [LinearMap.mem_ker, LinearMap.comp_apply, ContMDiffSection.evalLinearMap_apply,
          differentialOperators_section_apply_eq_of_jet_eq hP (t := 0)
            (by rw [hs, ContMDiffSection.coe_zero, jet_zero]),
          map_zero, ContMDiffSection.coe_zero, Pi.zero_apply]) ∘ₗ
    ((jetLinearMap I F V r x).quotKerEquivOfSurjective (jetLinearMap_surjective x)).symm.toLinearMap

/-- The jet factor of a differential operator `P` at `x` sends the `r`-jet of a smooth section `s`
at `x` to `(P s)(x)`. -/
@[simp]
theorem _root_.LinearMap.jetFactorOfMemDifferentialOperators_jet
    {P : Cₛ^∞⟮I; F, V⟯ →ₗ[ℝ] Cₛ^∞⟮I; F', W⟯}
    (hP : P ∈ differentialOperators ℝ C^∞⟮I, M; ℝ⟯ Cₛ^∞⟮I; F, V⟯ Cₛ^∞⟮I; F', W⟯ r) (x : M)
    (s : Cₛ^∞⟮I; F, V⟯) :
    P.jetFactorOfMemDifferentialOperators hP x (jet I F r s x) = P s x := by
  have h : ((jetLinearMap I F V r x).quotKerEquivOfSurjective (jetLinearMap_surjective x)).symm
      (jet I F r s x) = Submodule.Quotient.mk s := by
    rw [LinearEquiv.symm_apply_eq, LinearMap.quotKerEquivOfSurjective_apply_mk, jetLinearMap_apply]
  simp [LinearMap.jetFactorOfMemDifferentialOperators, h]

/-- **Uniqueness of the jet factor.** A linear map `(JᵣV)_x → W_x` sending the `r`-jet at `x` of
every smooth section `s` to `(P s)(x)` is the jet factor of `P` at `x`. -/
theorem _root_.LinearMap.eq_jetFactorOfMemDifferentialOperators
    {P : Cₛ^∞⟮I; F, V⟯ →ₗ[ℝ] Cₛ^∞⟮I; F', W⟯}
    (hP : P ∈ differentialOperators ℝ C^∞⟮I, M; ℝ⟯ Cₛ^∞⟮I; F, V⟯ Cₛ^∞⟮I; F', W⟯ r) {x : M}
    {A : JetBundle I F V r x →ₗ[ℝ] W x} (hA : ∀ s : Cₛ^∞⟮I; F, V⟯, A (jet I F r s x) = P s x) :
    A = P.jetFactorOfMemDifferentialOperators hP x := by
  ext B
  obtain ⟨s, rfl⟩ := jetLinearMap_surjective x B
  rw [jetLinearMap_apply, hA, LinearMap.jetFactorOfMemDifferentialOperators_jet]

/-- **Factorization through the jet bundle.** For a smooth real vector bundle `W` of finite rank, a
linear map `P : Γ(V) → Γ(W)` is a differential operator of order at most `r` in Grothendieck's
sense if and only if at every point `x` there is a linear map `A : (JᵣV)_x → W_x` with
`(P s)(x) = A (jʳs(x))` for every smooth section `s`. -/
theorem mem_differentialOperators_section_iff_exists_linearMap
    [FiniteDimensional ℝ F'] [ContMDiffVectorBundle ∞ F' W I]
    {P : Cₛ^∞⟮I; F, V⟯ →ₗ[ℝ] Cₛ^∞⟮I; F', W⟯} :
    P ∈ differentialOperators ℝ C^∞⟮I, M; ℝ⟯ Cₛ^∞⟮I; F, V⟯ Cₛ^∞⟮I; F', W⟯ r ↔
      ∀ x, ∃ A : JetBundle I F V r x →ₗ[ℝ] W x, ∀ s : Cₛ^∞⟮I; F, V⟯, P s x = A (jet I F r s x) := by
  refine ⟨fun hP x ↦ ⟨P.jetFactorOfMemDifferentialOperators hP x, fun s ↦
    (LinearMap.jetFactorOfMemDifferentialOperators_jet hP x s).symm⟩, fun h ↦ ?_⟩
  refine mem_differentialOperators_section_iff_forall_jet_eq.2 fun x s t hst ↦ ?_
  obtain ⟨A, hA⟩ := h x
  rw [hA, hA, hst]

end TauCeti
