/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Morse.Boundary.OrientationLine.Basic
public import TauCeti.Geometry.Manifold.Morse.Boundary.SignedChainComplex

/-!
# The Morse chain complex on orientation lines

Let `f` be a Morse function on a compact boundaryless manifold and `X` a pseudo-gradient adapted
to `f`. Fix a Morse chart `φ p` at every critical point `p`. The boundary on orientation lines
`TauCeti.IsAdaptedPseudoGradient.orientationLineBoundary` acts on the families `c` with `c p` in
the orientation line `o(p)` of the unstable manifold of `p`, and involves no choice of
orientations. This file grades it by the Morse index and packages it as a chain complex, the
**Morse complex on orientation lines**, which is the integral Morse complex without a choice of
orientations.

The chains of degree `n` (`TauCeti.orientationLineChainsAt`) are the families vanishing at every
critical point whose index is not `n`, a submodule of all families. The boundary maps the chains of
degree `n + 1` to those of degree `n`
(`TauCeti.IsAdaptedPseudoGradient.orientationLineBoundary_mem_orientationLineChainsAt`), and its
restriction (`TauCeti.IsAdaptedPseudoGradient.orientationLineBoundaryAt`) is the differential.
Whenever the boundary squares to zero, these differentials form a chain complex of `R`-modules
indexed by `ℕ` (`TauCeti.IsAdaptedPseudoGradient.orientationLineComplex`).

Two comparisons identify it with the other forms of the Morse complex.

* **Choosing orientations.** For orientation data `𝔬 : TauCeti.MorseOrientation f X` in the charts
  `φ`, evaluating each `c p` at the chosen orientation of `p` identifies the chains of degree `n`
  with the free module on the critical points of index `n`
  (`TauCeti.MorseOrientation.orientationLineEquivAt`). These identifications intertwine the
  differentials, so they form an isomorphism with the integral Morse complex `signedMorseComplex`
  defined by `𝔬` (`TauCeti.IsAdaptedPseudoGradient.orientationLineComplexIso`).
* **Changing the charts.** If `X` is linear in the Morse charts `φ` and in the Morse charts `φ'`,
  transporting the orientation lines along the changes of negative coordinates
  (`TauCeti.orientationLineChartEquiv`) preserves the degree
  (`TauCeti.orientationLineChartEquivAt`) and gives an isomorphism of the complexes on orientation
  lines in the two families of charts
  (`TauCeti.IsAdaptedPseudoGradient.orientationLineComplexChartIso`). These isomorphisms are
  coherent: the one from a family of charts to itself is the identity
  (`TauCeti.IsAdaptedPseudoGradient.orientationLineComplexChartIso_self`), and they compose
  (`TauCeti.IsAdaptedPseudoGradient.orientationLineComplexChartIso_trans`).

So the integral Morse complex of `(f, X)` is defined up to these canonical isomorphisms by `f` and
`X` alone, among the Morse charts in which `X` is linear; the integral Morse complex for orientation
data is one of its presentations.

## Main definitions

* `TauCeti.orientationLineChainsAt`: the chains of degree `n` on orientation lines.
* `TauCeti.IsAdaptedPseudoGradient.orientationLineBoundaryAt`: the differential of degree `-1`.
* `TauCeti.IsAdaptedPseudoGradient.orientationLineComplex`: the Morse complex on orientation lines.
* `TauCeti.MorseOrientation.orientationLineEquivAt`: evaluation at chosen orientations, in degree
  `n`.
* `TauCeti.IsAdaptedPseudoGradient.orientationLineComplexIso`: the isomorphism with the integral
  Morse complex for orientation data.
* `TauCeti.orientationLineChartEquivAt`: the transport between two families of Morse charts, in
  degree `n`.
* `TauCeti.IsAdaptedPseudoGradient.orientationLineComplexChartIso`: the isomorphism of the
  complexes on orientation lines for two families of Morse charts.

## Main results

* `TauCeti.MorseOrientation.orientationLineEquivAt_orientationLineBoundaryAt`: chosen orientations
  identify the differential on orientation lines with the graded integral Morse boundary.
* `TauCeti.IsAdaptedPseudoGradient.orientationLineComplexChartIso_self` and
  `TauCeti.IsAdaptedPseudoGradient.orientationLineComplexChartIso_trans`: the coherence of the
  changes of charts.

## References

* M. Hutchings, *Lecture notes on Morse homology (with an eye towards Floer theory and
  pseudoholomorphic curves)*, 2002, §2.3 (the Morse complex over `ℤ` and its independence of the
  orientations).
* M. Audin and M. Damian, *Morse Theory and Floer Homology*, Springer Universitext, 2014,
  Chapter 4 (the Morse complex with integer coefficients).
-/

public section

open CategoryTheory Set Module
open scoped ContDiff Manifold

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
  {f : M → ℝ} {X : (x : M) → TangentSpace 𝓘(ℝ, E) x}

section Chains

variable (φ : (p : criticalPoints 𝓘(ℝ, E) f) → MorseChart E f p) (R : Type*) [Ring R]

/-- The **chains of degree `n` on orientation lines**: the families `c`, with `c p` in the
orientation line of the unstable manifold of `p` in the Morse chart `φ p`, that vanish at every
critical point whose index is not `n`. -/
noncomputable def orientationLineChainsAt (n : ℕ) :
    Submodule R ((p : criticalPoints 𝓘(ℝ, E) f) → (φ p).unstableOrientationLine R) :=
  Submodule.pi {p | manifoldMorseIndex 𝓘(ℝ, E) f p ≠ n} fun _ ↦ ⊥

variable {φ R} in
/-- A family lies in the chains of degree `n` exactly when it vanishes at the critical points whose
index is not `n`. -/
theorem mem_orientationLineChainsAt {n : ℕ}
    {c : (p : criticalPoints 𝓘(ℝ, E) f) → (φ p).unstableOrientationLine R} :
    c ∈ orientationLineChainsAt φ R n ↔
      ∀ p : criticalPoints 𝓘(ℝ, E) f, manifoldMorseIndex 𝓘(ℝ, E) f p ≠ n → c p = 0 := by
  simp [orientationLineChainsAt, Submodule.mem_pi]

end Chains

variable [IsManifold 𝓘(ℝ, E) ∞ M] [CompactSpace M]

namespace IsAdaptedPseudoGradient

variable [FiniteDimensional ℝ E] [T2Space M] (hX : IsAdaptedPseudoGradient f X)
  (φ : (p : criticalPoints 𝓘(ℝ, E) f) → MorseChart E f p)
  {hf : IsMorse 𝓘(ℝ, E) f} (R : Type*) [Ring R]

variable {hX φ R} in
/-- **The boundary on orientation lines lowers the degree by one**: it maps the chains of degree
`n + 1` to the chains of degree `n`, since it only counts trajectories between critical points of
consecutive index. -/
theorem orientationLineBoundary_mem_orientationLineChainsAt (hf : IsMorse 𝓘(ℝ, E) f) {n : ℕ}
    {c : (p : criticalPoints 𝓘(ℝ, E) f) → (φ p).unstableOrientationLine R}
    (hc : c ∈ orientationLineChainsAt φ R (n + 1)) :
    hX.orientationLineBoundary φ R c ∈ orientationLineChainsAt φ R n := by
  rw [mem_orientationLineChainsAt] at hc ⊢
  intro q hq
  -- Compare both sides at one orientation of the unstable manifold at `q`.
  refine orientationLine_ext (φ q).card_fin_manifoldMorseIndex_eq_finrank
    (φ q).negativeOrientation ?_
  rw [orientationLineBoundary_apply hf c (fun p ↦ (φ p).negativeOrientation) q]
  rw [ZeroMemClass.coe_zero, Pi.zero_apply]
  refine finsum_eq_zero_of_forall_eq_zero fun p ↦ ?_
  split_ifs with hpq
  · rw [hc p (by omega), ZeroMemClass.coe_zero, Pi.zero_apply, zero_mul]
  · rfl

variable (hf) in
/-- **The differential on orientation lines**: the boundary on orientation lines, from the chains
of degree `n + 1` to the chains of degree `n`. -/
noncomputable def orientationLineBoundaryAt (n : ℕ) :
    orientationLineChainsAt φ R (n + 1) →ₗ[R] orientationLineChainsAt φ R n :=
  (hX.orientationLineBoundary φ R).restrict fun _ hc ↦
    orientationLineBoundary_mem_orientationLineChainsAt hf hc

/-- The differential on orientation lines is the boundary on orientation lines. -/
@[simp]
theorem coe_orientationLineBoundaryAt_apply (n : ℕ) (c : orientationLineChainsAt φ R (n + 1)) :
    (hX.orientationLineBoundaryAt φ hf R n c : (p : criticalPoints 𝓘(ℝ, E) f) →
      (φ p).unstableOrientationLine R) = hX.orientationLineBoundary φ R c :=
  (rfl)

variable (hf) in
/-- **The Morse complex on orientation lines.** When the boundary on orientation lines squares to
zero, the differentials `orientationLineBoundaryAt` form a chain complex of `R`-modules indexed by
`ℕ`. Its term in degree `n` is the module of the chains on the orientation lines of the unstable
manifolds of the critical points of index `n`; no orientation is chosen. -/
-- The body is exposed so that the terms of the complex compute to the chains of each degree, which
-- the statements of `orientationLineComplex_X` and `orientationLineComplex_d` need.
@[expose]
noncomputable def orientationLineComplex
    (hsq : hX.orientationLineBoundary φ R ∘ₗ hX.orientationLineBoundary φ R = 0) :
    ChainComplex (ModuleCat R) ℕ :=
  ChainComplex.of (fun n ↦ ModuleCat.of R (orientationLineChainsAt φ R n))
    (fun n ↦ ModuleCat.ofHom (hX.orientationLineBoundaryAt φ hf R n))
    fun n ↦ by
      rw [← ModuleCat.ofHom_comp, ← ModuleCat.ofHom_zero]
      congr 1
      exact LinearMap.ext fun c ↦ Subtype.ext (LinearMap.congr_fun hsq c)

variable (hsq : hX.orientationLineBoundary φ R ∘ₗ hX.orientationLineBoundary φ R = 0)

/-- The term of the Morse complex on orientation lines in degree `n` is the module of the chains of
degree `n`. -/
@[simp]
theorem orientationLineComplex_X (n : ℕ) :
    (hX.orientationLineComplex φ hf R hsq).X n =
      ModuleCat.of R (orientationLineChainsAt φ R n) :=
  (rfl)

/-- The differential of the Morse complex on orientation lines from degree `n + 1` to degree `n`
is the differential on orientation lines. -/
theorem orientationLineComplex_d (n : ℕ) :
    (hX.orientationLineComplex φ hf R hsq).d (n + 1) n =
      ModuleCat.ofHom (hX.orientationLineBoundaryAt φ hf R n) := by
  simp [orientationLineComplex]

end IsAdaptedPseudoGradient

/-! ### Choosing orientations -/

namespace MorseOrientation

variable (𝔬 : MorseOrientation f X) (hf : IsMorse 𝓘(ℝ, E) f) (R : Type*) [Ring R]

variable {𝔬 R} in
/-- Evaluation at chosen orientations maps the chains of degree `n` on orientation lines onto the
chains supported on the critical points of index `n`. -/
private theorem map_orientationLineEquiv_orientationLineChainsAt (n : ℕ) :
    (orientationLineChainsAt 𝔬.chart R n).map (𝔬.orientationLineEquiv hf R).toLinearMap =
      Finsupp.supported R R
        {p : criticalPoints 𝓘(ℝ, E) f | manifoldMorseIndex 𝓘(ℝ, E) f p = n} := by
  rw [Submodule.map_equiv_eq_comap_symm]
  ext c
  rw [Submodule.mem_comap, mem_orientationLineChainsAt, Finsupp.mem_supported']
  refine forall_congr' fun p ↦ imp_congr Iff.rfl ?_
  -- An element of an orientation line vanishes exactly when its value at an orientation does.
  rw [← orientationLineEquiv_symm_apply (hf := hf) c p, LinearEquiv.coe_coe]
  exact ⟨fun h ↦ by rw [h, ZeroMemClass.coe_zero, Pi.zero_apply], fun h ↦ orientationLine_ext
    (𝔬.chart p).card_fin_manifoldMorseIndex_eq_finrank (𝔬.orientation p)
      (by rw [h, ZeroMemClass.coe_zero, Pi.zero_apply])⟩

/-- **Evaluation at chosen orientations, in degree `n`.** Orientation data identify the chains of
degree `n` on orientation lines, in the charts of the data, with the free module on the critical
points of index `n`: a family `c` goes to the function whose value at `p` is `c p` evaluated at the
chosen orientation of `p`. -/
noncomputable def orientationLineEquivAt (n : ℕ) :
    orientationLineChainsAt 𝔬.chart R n ≃ₗ[R]
      ({p : criticalPoints 𝓘(ℝ, E) f // manifoldMorseIndex 𝓘(ℝ, E) f p = n} →₀ R) :=
  ((𝔬.orientationLineEquiv hf R).ofSubmodules _ _
    (map_orientationLineEquiv_orientationLineChainsAt hf n)).trans
      (Finsupp.supportedEquivFinsupp _)

variable {𝔬 hf R}

/-- The value at `p` of the evaluation of `c` at chosen orientations is `c p` evaluated at the
chosen orientation of `p`. -/
@[simp]
theorem orientationLineEquivAt_apply {n : ℕ} (c : orientationLineChainsAt 𝔬.chart R n)
    (p : {p : criticalPoints 𝓘(ℝ, E) f // manifoldMorseIndex 𝓘(ℝ, E) f p = n}) :
    𝔬.orientationLineEquivAt hf R n c p = (c.val p.val).val (𝔬.orientation p.val) :=
  orientationLineEquiv_apply c.val p.val

/-- Including the chains of index `n` into all chains, after evaluation at chosen orientations in
degree `n`, is evaluation at chosen orientations. -/
theorem mapDomain_orientationLineEquivAt {n : ℕ} (c : orientationLineChainsAt 𝔬.chart R n) :
    (𝔬.orientationLineEquivAt hf R n c).mapDomain Subtype.val =
      𝔬.orientationLineEquiv hf R c.val := by
  ext p
  by_cases hp : manifoldMorseIndex 𝓘(ℝ, E) f p = n
  · rw [Finsupp.mapDomain_apply_of_injective Subtype.val_injective _ ⟨p, hp⟩,
      orientationLineEquivAt_apply, orientationLineEquiv_apply]
  · rw [Finsupp.mapDomain_of_notMem_range _ _ fun ⟨q, hq⟩ ↦ hp (hq ▸ q.property),
      orientationLineEquiv_apply, mem_orientationLineChainsAt.1 c.property p hp,
      ZeroMemClass.coe_zero, Pi.zero_apply]

variable [FiniteDimensional ℝ E] [T2Space M] {hX : IsAdaptedPseudoGradient f X}

/-- **Chosen orientations identify the differential on orientation lines with the graded integral
Morse boundary.** Evaluation at the orientations of `𝔬`, in degrees `n + 1` and `n`, carries the
differential on orientation lines, in the Morse charts of `𝔬`, to the graded integral Morse
boundary defined by `𝔬`. -/
theorem orientationLineEquivAt_orientationLineBoundaryAt {n : ℕ}
    (c : orientationLineChainsAt 𝔬.chart R (n + 1)) :
    𝔬.orientationLineEquivAt hf R n (hX.orientationLineBoundaryAt 𝔬.chart hf R n c) =
      hX.signedMorseBoundaryAt 𝔬 hf R n (𝔬.orientationLineEquivAt hf R (n + 1) c) := by
  refine Finsupp.mapDomain_injective Subtype.val_injective ?_
  rw [mapDomain_orientationLineEquivAt, IsAdaptedPseudoGradient.mapDomain_signedMorseBoundaryAt,
    mapDomain_orientationLineEquivAt, IsAdaptedPseudoGradient.coe_orientationLineBoundaryAt_apply,
    IsAdaptedPseudoGradient.orientationLineEquiv_orientationLineBoundary]

end MorseOrientation

namespace IsAdaptedPseudoGradient

variable [FiniteDimensional ℝ E] [T2Space M] {hX : IsAdaptedPseudoGradient f X}
  (𝔬 : MorseOrientation f X) {hf : IsMorse 𝓘(ℝ, E) f}
  (R : Type*) [Ring R]
  (hsq : hX.orientationLineBoundary 𝔬.chart R ∘ₗ hX.orientationLineBoundary 𝔬.chart R = 0)
  (hsq' : hX.signedMorseBoundary 𝔬 hf R ∘ₗ hX.signedMorseBoundary 𝔬 hf R = 0)

/-- **The Morse complex on orientation lines is the integral Morse complex for any orientations.**
For orientation data `𝔬`, evaluation at the orientations of `𝔬` is an isomorphism from the Morse
complex on orientation lines, in the Morse charts of `𝔬`, to the integral Morse complex defined by
`𝔬`. The hypotheses `hsq` and `hsq'` that the two boundaries square to zero are equivalent
(`TauCeti.IsAdaptedPseudoGradient.orientationLineBoundary_comp_self_eq_zero_iff`). -/
noncomputable def orientationLineComplexIso :
    hX.orientationLineComplex 𝔬.chart hf R hsq ≅ hX.signedMorseComplex 𝔬 hf R hsq' :=
  HomologicalComplex.Hom.isoOfComponents
    (fun n ↦ (𝔬.orientationLineEquivAt hf R n).toModuleIso) <| by
    rintro _ n rfl
    rw [orientationLineComplex_d, signedMorseComplex_d]
    refine ModuleCat.hom_ext (LinearMap.ext fun (c : orientationLineChainsAt 𝔬.chart R (n + 1)) ↦
      ?_)
    -- The terms of both complexes are their chain modules only after unfolding the complexes, so
    -- the `ModuleCat` composition lemmas do not rewrite the goal; `change` states it on the chains.
    change hX.signedMorseBoundaryAt 𝔬 hf R n (𝔬.orientationLineEquivAt hf R (n + 1) c) =
      𝔬.orientationLineEquivAt hf R n (hX.orientationLineBoundaryAt 𝔬.chart hf R n c)
    exact (MorseOrientation.orientationLineEquivAt_orientationLineBoundaryAt c).symm

/-- The isomorphism of the Morse complex on orientation lines with the integral Morse complex
evaluates the chains at the chosen orientations. -/
@[simp]
theorem orientationLineComplexIso_hom_f_apply (n : ℕ) (c : orientationLineChainsAt 𝔬.chart R n) :
    (hX.orientationLineComplexIso 𝔬 R hsq hsq').hom.f n c = 𝔬.orientationLineEquivAt hf R n c :=
  (rfl)

end IsAdaptedPseudoGradient

/-! ### Changing the Morse charts -/

section ChartChange

variable [FiniteDimensional ℝ E] (φ φ' : (p : criticalPoints 𝓘(ℝ, E) f) → MorseChart E f p)
  (R : Type*) [Ring R]

omit [IsManifold 𝓘(ℝ, E) ∞ M] [CompactSpace M] in
variable {φ φ' R} in
/-- The transport of the chains on orientation lines between two families of Morse charts maps the
chains of degree `n` onto the chains of degree `n`, since it acts at each critical point by an
isomorphism. -/
private theorem map_orientationLineChartEquiv_orientationLineChainsAt (n : ℕ) :
    (orientationLineChainsAt φ R n).map (orientationLineChartEquiv φ φ' R).toLinearMap =
      orientationLineChainsAt φ' R n := by
  rw [Submodule.map_equiv_eq_comap_symm]
  ext c
  rw [Submodule.mem_comap, mem_orientationLineChainsAt, mem_orientationLineChainsAt]
  refine forall_congr' fun p ↦ imp_congr Iff.rfl ?_
  conv_rhs => rw [← (orientationLineChartEquiv φ φ' R).apply_symm_apply c]
  rw [orientationLineChartEquiv_apply, LinearEquiv.map_eq_zero_iff, LinearEquiv.coe_coe]

/-- **The transport of the chains of degree `n` on orientation lines** from the Morse charts `φ`
to the Morse charts `φ'`, along the changes of negative coordinates. -/
noncomputable def orientationLineChartEquivAt (n : ℕ) :
    orientationLineChainsAt φ R n ≃ₗ[R] orientationLineChainsAt φ' R n :=
  (orientationLineChartEquiv φ φ' R).ofSubmodules _ _
    (map_orientationLineChartEquiv_orientationLineChainsAt n)

variable {φ φ' R}

omit [IsManifold 𝓘(ℝ, E) ∞ M] [CompactSpace M] in
/-- The transport of the chains of degree `n` is the transport of all chains. -/
@[simp]
theorem coe_orientationLineChartEquivAt_apply {n : ℕ} (c : orientationLineChainsAt φ R n) :
    (orientationLineChartEquivAt φ φ' R n c : (p : criticalPoints 𝓘(ℝ, E) f) →
      (φ' p).unstableOrientationLine R) = orientationLineChartEquiv φ φ' R c :=
  (rfl)

variable [T2Space M] {hX : IsAdaptedPseudoGradient f X} {hf : IsMorse 𝓘(ℝ, E) f}

/-- **The differentials on orientation lines do not depend on the Morse charts.** If `X` is linear
in the Morse charts `φ` and in the Morse charts `φ'`, the transport of the chains along the changes
of negative coordinates intertwines the differentials defined in the two families of charts. -/
theorem orientationLineChartEquivAt_orientationLineBoundaryAt
    (hφ : ∀ p : criticalPoints 𝓘(ℝ, E) f, ∀ y ∈ (φ p).toChart.source,
      (φ p).coord (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (φ p).toChart y (X y)) =
        fun i ↦ -((φ p).weight i * (φ p).coord ((φ p).toChart y) i))
    (hφ' : ∀ p : criticalPoints 𝓘(ℝ, E) f, ∀ y ∈ (φ' p).toChart.source,
      (φ' p).coord (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (φ' p).toChart y (X y)) =
        fun i ↦ -((φ' p).weight i * (φ' p).coord ((φ' p).toChart y) i))
    {n : ℕ} (c : orientationLineChainsAt φ R (n + 1)) :
    orientationLineChartEquivAt φ φ' R n (hX.orientationLineBoundaryAt φ hf R n c) =
      hX.orientationLineBoundaryAt φ' hf R n (orientationLineChartEquivAt φ φ' R (n + 1) c) :=
  Subtype.ext (orientationLineChartEquiv_orientationLineBoundary hf hφ hφ' c.val)

end ChartChange

namespace IsAdaptedPseudoGradient

variable [FiniteDimensional ℝ E] [T2Space M] {hX : IsAdaptedPseudoGradient f X}
  (hf : IsMorse 𝓘(ℝ, E) f) {φ φ' : (p : criticalPoints 𝓘(ℝ, E) f) → MorseChart E f p}
  (R : Type*) [Ring R]
  (hφ : ∀ p : criticalPoints 𝓘(ℝ, E) f, ∀ y ∈ (φ p).toChart.source,
    (φ p).coord (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (φ p).toChart y (X y)) =
      fun i ↦ -((φ p).weight i * (φ p).coord ((φ p).toChart y) i))
  (hφ' : ∀ p : criticalPoints 𝓘(ℝ, E) f, ∀ y ∈ (φ' p).toChart.source,
    (φ' p).coord (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (φ' p).toChart y (X y)) =
      fun i ↦ -((φ' p).weight i * (φ' p).coord ((φ' p).toChart y) i))
  (hsq : hX.orientationLineBoundary φ R ∘ₗ hX.orientationLineBoundary φ R = 0)
  (hsq' : hX.orientationLineBoundary φ' R ∘ₗ hX.orientationLineBoundary φ' R = 0)

/-- **The Morse complex on orientation lines does not depend on the Morse charts.** If `X` is
linear in the Morse charts `φ` and in the Morse charts `φ'`, the transport of the chains along the
changes of negative coordinates is an isomorphism between the Morse complexes on orientation lines
in the two families of charts. -/
noncomputable def orientationLineComplexChartIso :
    hX.orientationLineComplex φ hf R hsq ≅ hX.orientationLineComplex φ' hf R hsq' :=
  HomologicalComplex.Hom.isoOfComponents
    (fun n ↦ (orientationLineChartEquivAt φ φ' R n).toModuleIso) <| by
    rintro _ n rfl
    rw [orientationLineComplex_d, orientationLineComplex_d]
    refine ModuleCat.hom_ext (LinearMap.ext fun (c : orientationLineChainsAt φ R (n + 1)) ↦ ?_)
    -- As for `orientationLineComplexIso`, `change` states the goal on the chains.
    change hX.orientationLineBoundaryAt φ' hf R n (orientationLineChartEquivAt φ φ' R (n + 1) c) =
      orientationLineChartEquivAt φ φ' R n (hX.orientationLineBoundaryAt φ hf R n c)
    exact (orientationLineChartEquivAt_orientationLineBoundaryAt hφ hφ' c).symm

/-- The isomorphism of the Morse complexes on orientation lines for two families of Morse charts
transports the chains along the changes of negative coordinates. -/
@[simp]
theorem orientationLineComplexChartIso_hom_f_apply (n : ℕ) (c : orientationLineChainsAt φ R n) :
    (hX.orientationLineComplexChartIso hf R hφ hφ' hsq hsq').hom.f n c =
      orientationLineChartEquivAt φ φ' R n c :=
  (rfl)

/-- The isomorphism of the Morse complexes on orientation lines from a family of Morse charts to
itself is the identity. -/
@[simp]
theorem orientationLineComplexChartIso_self :
    hX.orientationLineComplexChartIso hf R hφ hφ hsq hsq = Iso.refl _ := by
  ext n : 2
  refine ModuleCat.hom_ext (LinearMap.ext fun (c : orientationLineChainsAt φ R n) ↦ ?_)
  rw [orientationLineComplexChartIso_hom_f_apply]
  refine Subtype.ext ?_
  rw [coe_orientationLineChartEquivAt_apply, orientationLineChartEquiv_self]
  rfl

/-- **The isomorphisms of the Morse complexes on orientation lines compose**: changing the Morse
charts from `φ` to `φ'` and then from `φ'` to `φ''` is the change from `φ` to `φ''`. -/
theorem orientationLineComplexChartIso_trans
    {φ'' : (p : criticalPoints 𝓘(ℝ, E) f) → MorseChart E f p}
    (hφ'' : ∀ p : criticalPoints 𝓘(ℝ, E) f, ∀ y ∈ (φ'' p).toChart.source,
      (φ'' p).coord (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (φ'' p).toChart y (X y)) =
        fun i ↦ -((φ'' p).weight i * (φ'' p).coord ((φ'' p).toChart y) i))
    (hsq'' : hX.orientationLineBoundary φ'' R ∘ₗ hX.orientationLineBoundary φ'' R = 0) :
    hX.orientationLineComplexChartIso hf R hφ hφ' hsq hsq' ≪≫
        hX.orientationLineComplexChartIso hf R hφ' hφ'' hsq' hsq'' =
      hX.orientationLineComplexChartIso hf R hφ hφ'' hsq hsq'' := by
  ext n : 2
  refine ModuleCat.hom_ext (LinearMap.ext fun (c : orientationLineChainsAt φ R n) ↦ ?_)
  -- The components are the transports of the chains of degree `n`.
  change orientationLineChartEquivAt φ' φ'' R n (orientationLineChartEquivAt φ φ' R n c) =
    orientationLineChartEquivAt φ φ'' R n c
  refine Subtype.ext ?_
  rw [coe_orientationLineChartEquivAt_apply, coe_orientationLineChartEquivAt_apply,
    coe_orientationLineChartEquivAt_apply, ← LinearEquiv.trans_apply,
    orientationLineChartEquiv_trans_orientationLineChartEquiv hX hf hφ hφ' hφ'']

end IsAdaptedPseudoGradient

end TauCeti
