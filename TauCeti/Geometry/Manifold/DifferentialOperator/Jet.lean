/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.DifferentialOperator.Section
public import TauCeti.Geometry.Manifold.VectorBundle.FrameTrivialization
public import TauCeti.Geometry.Manifold.VectorBundle.Hom
public import TauCeti.Geometry.Manifold.VectorBundle.Jet.VanishingIdeal

/-!
# Differential operators factor fibrewise through jets

Let `V` and `W` be smooth real vector bundles over a finite-dimensional Hausdorff boundaryless
smooth manifold `M`, with `V` of finite rank. A real-linear map `P : Γ(V) → Γ(W)` between the
modules of smooth sections is a differential operator of order at most `r` in Grothendieck's sense
(`TauCeti.differentialOperators`) when all its `(r + 1)`-fold commutators with multiplication by
smooth functions vanish. No continuity of `P` is assumed.

Such an operator factors fibrewise through the fibres of the bundle `JᵣV` of `r`-jets
(`TauCeti.JetBundle`): at every point `x` there is a unique real-linear map
`A_x : (JᵣV)_x → W_x` with

`(P s)(x) = A_x (jʳs(x))`

for every smooth section `s`, where `jʳs(x)` is the `r`-jet of `s` at `x`. Conversely, when `W`
also has finite rank, a linear map `P` of this form is a differential operator of order at most
`r`. So for operators between sections of finite-rank bundles, the algebraic order filtration by
iterated commutators agrees with the order filtration by fibrewise factorization through jets.

The family `x ↦ A_x` is moreover smooth: it is a smooth section of the bundle `Hom(JᵣV, W)`, so
that `P` factors through `jʳ` by a smooth bundle map `JᵣV → W`
(`LinearMap.jetFactorSection`). Conversely every smooth bundle map `A : JᵣV → W` defines the
differential operator `s ↦ (x ↦ A_x (jʳs(x)))` of order at most `r`. For `W` of finite rank this
identifies the differential operators `Γ(V) → Γ(W)` of order at most `r` with the smooth sections
of `Hom(JᵣV, W)` (`TauCeti.differentialOperatorsEquivJetHom`). Smoothness is local: near a point
`x₀`, the jets of finitely many smooth sections `sₖ` whose jets at `x₀` form a basis of `(JᵣV)_x₀`
form a local frame of `JᵣV` (`IsLocalFrameOn.exists_of_linearIndependent`), and a smooth section of
`JᵣV` with coefficients `cₖ` in this frame is sent by `A` to the smooth section `∑ₖ cₖ P sₖ`.

The proof combines two identifications of the same filtration. An operator of order at most `r`
sends `I_x ^ (r + 1) Γ(V)` into `I_x Γ(W)`, where `I_x` is the ideal of smooth functions vanishing
at `x`, and the sections of `W` in `I_x Γ(W)` vanish at `x`
(`TauCeti.apply_eq_zero_of_mem_smoothVanishingIdeal_smul_top`). The sections of `V` in
`I_x ^ (r + 1) Γ(V)` are those with vanishing `r`-jet at `x`
(`TauCeti.JetBundle.jet_eq_zero_iff_mem_smoothVanishingIdeal_pow_smul_top`), and every `r`-jet at
`x` is the jet of a smooth section (`TauCeti.JetBundle.jetLinearMap_surjective`), so that
`Γ(V) / I_x ^ (r + 1) Γ(V)` is the fibre of `JᵣV` at `x`
(`TauCeti.JetBundle.smoothSectionJetEquiv`).

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
* `LinearMap.jetFactorSection`: the jet factors of a differential operator of order at most `r`,
  as a smooth section of `Hom(JᵣV, W)`; it is unique (`LinearMap.eq_jetFactorSection`).
* `TauCeti.differentialOperatorsEquivJetHom`: for `W` of finite rank, the differential operators
  of order at most `r` are the smooth bundle maps `JᵣV → W`.

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

/-- **Differential operators factor fibrewise through jets.** A differential operator of order at
most `r` between sections, in Grothendieck's sense of iterated commutators with multiplication
operators, takes the same value at `x` on two smooth sections with the same `r`-jet at `x`. -/
theorem differentialOperators_section_apply_eq_of_jet_eq
    {P : Cₛ^∞⟮I; F, V⟯ →ₗ[ℝ] Cₛ^∞⟮I; F', W⟯}
    (hP : P ∈ differentialOperators ℝ C^∞⟮I, M; ℝ⟯ Cₛ^∞⟮I; F, V⟯ Cₛ^∞⟮I; F', W⟯ r) {x : M}
    {s t : Cₛ^∞⟮I; F, V⟯} (hst : jet I F r s x = jet I F r t x) : P s x = P t x := by
  have h := apply_eq_zero_of_mem_smoothVanishingIdeal_smul_top
    (apply_mem_smul_top_of_mem_pow_smul_top hP _
      ((jet_eq_jet_iff_sub_mem_smoothVanishingIdeal_pow_smul_top s t).1 hst))
  rwa [map_sub, ContMDiffSection.coe_sub, Pi.sub_apply, sub_eq_zero] at h

/-- **Differential operators are the operators that factor fibrewise through jets.** For a smooth
real vector bundle `W` of finite rank, a linear map `P : Γ(V) → Γ(W)` is a differential operator
of order at most `r` in Grothendieck's sense if and only if, at every point `x`, the value
`(P s)(x)` only depends on the `r`-jet of `s` at `x`. -/
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
(`LinearMap.eq_jetFactorOfMemDifferentialOperators`). It is induced on
`(JᵣV)_x ≃ Γ(V) / I_x ^ (r + 1) Γ(V)` (`TauCeti.JetBundle.smoothSectionJetEquiv`) by `s ↦ (P s)(x)`,
which kills `I_x ^ (r + 1) Γ(V)`. -/
def _root_.LinearMap.jetFactorOfMemDifferentialOperators (P : Cₛ^∞⟮I; F, V⟯ →ₗ[ℝ] Cₛ^∞⟮I; F', W⟯)
    (hP : P ∈ differentialOperators ℝ C^∞⟮I, M; ℝ⟯ Cₛ^∞⟮I; F, V⟯ Cₛ^∞⟮I; F', W⟯ r) (x : M) :
    JetBundle I F V r x →ₗ[ℝ] W x :=
  ((smoothVanishingIdeal I x ^ (r + 1) •
      (⊤ : Submodule C^∞⟮I, M; ℝ⟯ Cₛ^∞⟮I; F, V⟯)).restrictScalars ℝ).liftQ
      (ContMDiffSection.evalLinearMap I F' ∞ W x ∘ₗ P) (fun s hs ↦ by
        rw [LinearMap.mem_ker, LinearMap.comp_apply, ContMDiffSection.evalLinearMap_apply]
        exact apply_eq_zero_of_mem_smoothVanishingIdeal_smul_top
          (apply_mem_smul_top_of_mem_pow_smul_top hP _ hs)) ∘ₗ
    (Submodule.Quotient.restrictScalarsEquiv ℝ _).symm.toLinearMap ∘ₗ
    (smoothSectionJetEquiv I F V r x).symm.toLinearMap

/-- The jet factor of a differential operator `P` at `x` sends the `r`-jet of a smooth section `s`
at `x` to `(P s)(x)`. -/
@[simp]
theorem _root_.LinearMap.jetFactorOfMemDifferentialOperators_jet
    {P : Cₛ^∞⟮I; F, V⟯ →ₗ[ℝ] Cₛ^∞⟮I; F', W⟯}
    (hP : P ∈ differentialOperators ℝ C^∞⟮I, M; ℝ⟯ Cₛ^∞⟮I; F, V⟯ Cₛ^∞⟮I; F', W⟯ r) (x : M)
    (s : Cₛ^∞⟮I; F, V⟯) :
    P.jetFactorOfMemDifferentialOperators hP x (jet I F r s x) = P s x := by
  simp [LinearMap.jetFactorOfMemDifferentialOperators]

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

/-- **Fibrewise factorization through jets.** For a smooth real vector bundle `W` of finite rank, a
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

/-! ### Smoothness of the jet factor -/

section Smooth

variable [∀ x, IsTopologicalAddGroup (W x)] [∀ x, ContinuousSMul ℝ (W x)]
  [ContMDiffVectorBundle ∞ F' W I]

/-- **Differential operators factor through jets by a smooth bundle map.** The jet factors
`A_x : (JᵣV)_x → W_x` of a differential operator `P : Γ(V) → Γ(W)` of order at most `r`
(`LinearMap.jetFactorOfMemDifferentialOperators`) form a smooth section of the bundle
`Hom(JᵣV, W)`, so that `(P s)(x) = A_x (jʳs(x))` for a smooth bundle map `A : JᵣV → W`
(`LinearMap.jetFactorSection_apply_jet`). -/
def _root_.LinearMap.jetFactorSection (P : Cₛ^∞⟮I; F, V⟯ →ₗ[ℝ] Cₛ^∞⟮I; F', W⟯)
    (hP : P ∈ differentialOperators ℝ C^∞⟮I, M; ℝ⟯ Cₛ^∞⟮I; F, V⟯ Cₛ^∞⟮I; F', W⟯ r) :
    Cₛ^∞⟮I; SymmetricJet ℝ E F r →L[ℝ] F', fun x ↦ JetBundle I F V r x →L[ℝ] W x⟯ where
  toFun x :=
    -- The fibre of `JᵣV` is finite-dimensional and Hausdorff, so linear maps out of it are
    -- continuous.
    haveI := FiberBundle.t2Space (SymmetricJet ℝ E F r) (JetBundle I F V r) x
    haveI := VectorBundle.finiteDimensional ℝ (SymmetricJet ℝ E F r) (JetBundle I F V r) x
    (P.jetFactorOfMemDifferentialOperators hP x).toContinuousLinearMap
  contMDiff_toFun := by
    refine (Manifold.contMDiff_hom_iff _).2 fun j hj x₀ ↦ ?_
    -- The jets at `x₀` of finitely many smooth sections `s k` form a basis of the fibre.
    let c := (Module.finBasis ℝ (SymmetricJet ℝ E F r)).map
      ((trivializationAt (SymmetricJet ℝ E F r) (JetBundle I F V r) x₀).linearEquivAt ℝ x₀
        (FiberBundle.mem_baseSet_trivializationAt' x₀)).symm
    choose s hs using fun k ↦ jetLinearMap_surjective (I := I) (V := V) (r := r) x₀ (c k)
    have hc : (fun k ↦ jet I F r (s k) x₀) = ⇑c :=
      funext fun k ↦ (jetLinearMap_apply x₀ (s k)).symm.trans (hs k)
    -- Their jets form a local frame of `JᵣV` near `x₀`, in which `j` has smooth coefficients.
    obtain ⟨U, -, hU, hx₀, hfr⟩ := IsLocalFrameOn.exists_of_linearIndependent isOpen_univ
      (fun k ↦ (contMDiff_infty_jet (s k).contMDiff).contMDiffOn) (Set.mem_univ x₀)
      (hc ▸ c.linearIndependent) (hc ▸ c.span_eq.ge)
    have hsum : ContMDiffAt I (I.prod 𝓘(ℝ, F')) ∞ (fun x ↦ TotalSpace.mk' F' x
        (∑ k, hfr.coeff k x (j x) • P (s k) x)) x₀ :=
      ContMDiffAt.sum_section fun k _ ↦
        ((hfr.contMDiffOn_coeff hU le_rfl hj.contMDiffOn k).contMDiffAt (hU.mem_nhds hx₀))
          |>.smul_section ((P (s k)).contMDiff x₀)
    refine hsum.congr_of_eventuallyEq ?_
    filter_upwards [hU.mem_nhds hx₀] with x hx
    conv_lhs => rw [hfr.coeff_sum_eq j hx]
    simp

/-- The smooth bundle map through which a differential operator `P` of order at most `r` factors
sends the `r`-jet at `x` of a smooth section `s` to `(P s)(x)`. -/
@[simp]
theorem _root_.LinearMap.jetFactorSection_apply_jet
    {P : Cₛ^∞⟮I; F, V⟯ →ₗ[ℝ] Cₛ^∞⟮I; F', W⟯}
    (hP : P ∈ differentialOperators ℝ C^∞⟮I, M; ℝ⟯ Cₛ^∞⟮I; F, V⟯ Cₛ^∞⟮I; F', W⟯ r) (x : M)
    (s : Cₛ^∞⟮I; F, V⟯) : P.jetFactorSection hP x (jet I F r s x) = P s x := by
  simp [LinearMap.jetFactorSection]

/-- At every point, the smooth bundle map through which a differential operator factors is its
jet factor at that point. -/
@[simp]
theorem _root_.LinearMap.coe_jetFactorSection_apply
    {P : Cₛ^∞⟮I; F, V⟯ →ₗ[ℝ] Cₛ^∞⟮I; F', W⟯}
    (hP : P ∈ differentialOperators ℝ C^∞⟮I, M; ℝ⟯ Cₛ^∞⟮I; F, V⟯ Cₛ^∞⟮I; F', W⟯ r) (x : M) :
    (P.jetFactorSection hP x : JetBundle I F V r x →ₗ[ℝ] W x) =
      P.jetFactorOfMemDifferentialOperators hP x := by
  simp [LinearMap.jetFactorSection]

/-- **Uniqueness of the smooth jet factor.** A smooth bundle map `A : JᵣV → W` sending the
`r`-jet at `x` of every smooth section `s` to `(P s)(x)` is the smooth jet factor of `P`. -/
theorem _root_.LinearMap.eq_jetFactorSection {P : Cₛ^∞⟮I; F, V⟯ →ₗ[ℝ] Cₛ^∞⟮I; F', W⟯}
    (hP : P ∈ differentialOperators ℝ C^∞⟮I, M; ℝ⟯ Cₛ^∞⟮I; F, V⟯ Cₛ^∞⟮I; F', W⟯ r)
    {A : Cₛ^∞⟮I; SymmetricJet ℝ E F r →L[ℝ] F', fun x ↦ JetBundle I F V r x →L[ℝ] W x⟯}
    (hA : ∀ x (s : Cₛ^∞⟮I; F, V⟯), A x (jet I F r s x) = P s x) : A = P.jetFactorSection hP := by
  ext x j
  obtain ⟨s, rfl⟩ := jetLinearMap_surjective x j
  rw [jetLinearMap_apply, hA, LinearMap.jetFactorSection_apply_jet]

/-- The operator `s ↦ (x ↦ A_x (jʳs(x)))` defined by a smooth bundle map `A : JᵣV → W`. -/
private def jetOperator
    (A : Cₛ^∞⟮I; SymmetricJet ℝ E F r →L[ℝ] F', fun x ↦ JetBundle I F V r x →L[ℝ] W x⟯) :
    Cₛ^∞⟮I; F, V⟯ →ₗ[ℝ] Cₛ^∞⟮I; F', W⟯ where
  toFun s := ⟨fun x ↦ A x (jet I F r s x), A.contMDiff.clm_bundle_apply
    (contMDiff_infty_jet s.contMDiff)⟩
  map_add' s t := by
    ext x
    simp only [ContMDiffSection.coeFn_mk, ContMDiffSection.coe_add, Pi.add_apply]
    rw [← ContMDiffSection.coe_add, ← jetLinearMap_apply, ← jetLinearMap_apply,
      ← jetLinearMap_apply, map_add, map_add]
  map_smul' c s := by
    ext x
    simp only [ContMDiffSection.coeFn_mk, ContMDiffSection.coe_smul, Pi.smul_apply,
      RingHom.id_apply]
    rw [← ContMDiffSection.coe_smul, ← jetLinearMap_apply, ← jetLinearMap_apply, map_smul,
      map_smul]

omit [FiniteDimensional ℝ E] [T2Space M] [FiniteDimensional ℝ F]
  [ContMDiffVectorBundle ∞ F' W I] in
private theorem jetOperator_apply
    (A : Cₛ^∞⟮I; SymmetricJet ℝ E F r →L[ℝ] F', fun x ↦ JetBundle I F V r x →L[ℝ] W x⟯)
    (s : Cₛ^∞⟮I; F, V⟯) (x : M) : jetOperator A s x = A x (jet I F r s x) :=
  (rfl)

variable [FiniteDimensional ℝ F']

private theorem jetOperator_mem_differentialOperators
    (A : Cₛ^∞⟮I; SymmetricJet ℝ E F r →L[ℝ] F', fun x ↦ JetBundle I F V r x →L[ℝ] W x⟯) :
    jetOperator A ∈ differentialOperators ℝ C^∞⟮I, M; ℝ⟯ Cₛ^∞⟮I; F, V⟯ Cₛ^∞⟮I; F', W⟯ r :=
  mem_differentialOperators_section_iff_exists_linearMap.2 fun x ↦
    ⟨(A x : JetBundle I F V r x →ₗ[ℝ] W x), fun s ↦ jetOperator_apply A s x⟩

variable (I F V F' W r) in
/-- **Differential operators are the smooth bundle maps out of the jet bundle.** For a smooth real
vector bundle `W` of finite rank, sending a differential operator `P : Γ(V) → Γ(W)` of order at
most `r`, in Grothendieck's sense of iterated commutators with multiplication operators, to the
smooth bundle map `A : JᵣV → W` with `(P s)(x) = A_x (jʳs(x))` (`LinearMap.jetFactorSection`) is a
real-linear equivalence onto the smooth sections of `Hom(JᵣV, W)`. Its inverse sends `A` to the
operator `s ↦ (x ↦ A_x (jʳs(x)))` (`TauCeti.differentialOperatorsEquivJetHom_symm_apply_apply`). -/
def differentialOperatorsEquivJetHom :
    differentialOperators ℝ C^∞⟮I, M; ℝ⟯ Cₛ^∞⟮I; F, V⟯ Cₛ^∞⟮I; F', W⟯ r ≃ₗ[ℝ]
      Cₛ^∞⟮I; SymmetricJet ℝ E F r →L[ℝ] F', fun x ↦ JetBundle I F V r x →L[ℝ] W x⟯ :=
  LinearEquiv.symm
    { toFun A := ⟨jetOperator A, jetOperator_mem_differentialOperators A⟩
      map_add' A B := by
        ext s x
        simp only [Submodule.coe_add, LinearMap.add_apply, ContMDiffSection.coe_add,
          Pi.add_apply, jetOperator_apply, add_apply]
      map_smul' c A := by
        ext s x
        simp only [Submodule.coe_smul, LinearMap.smul_apply, ContMDiffSection.coe_smul,
          Pi.smul_apply, jetOperator_apply, smul_apply, RingHom.id_apply]
      invFun P := P.val.jetFactorSection P.property
      left_inv A :=
        (LinearMap.eq_jetFactorSection _ fun x s ↦ (jetOperator_apply A s x).symm).symm
      right_inv P := by
        ext s x
        rw [jetOperator_apply, LinearMap.jetFactorSection_apply_jet] }

/-- The equivalence `TauCeti.differentialOperatorsEquivJetHom` sends a differential operator to
its smooth jet factor. -/
@[simp]
theorem differentialOperatorsEquivJetHom_apply
    (P : differentialOperators ℝ C^∞⟮I, M; ℝ⟯ Cₛ^∞⟮I; F, V⟯ Cₛ^∞⟮I; F', W⟯ r) :
    differentialOperatorsEquivJetHom I F V F' W r P = P.val.jetFactorSection P.property :=
  (rfl)

/-- The differential operator corresponding to a smooth bundle map `A : JᵣV → W` sends a smooth
section `s` to `x ↦ A_x (jʳs(x))`. -/
@[simp]
theorem differentialOperatorsEquivJetHom_symm_apply_apply
    (A : Cₛ^∞⟮I; SymmetricJet ℝ E F r →L[ℝ] F', fun x ↦ JetBundle I F V r x →L[ℝ] W x⟯)
    (s : Cₛ^∞⟮I; F, V⟯) (x : M) :
    ((differentialOperatorsEquivJetHom I F V F' W r).symm A : Cₛ^∞⟮I; F, V⟯ →ₗ[ℝ]
      Cₛ^∞⟮I; F', W⟯) s x = A x (jet I F r s x) :=
  (rfl)

end Smooth

end TauCeti
