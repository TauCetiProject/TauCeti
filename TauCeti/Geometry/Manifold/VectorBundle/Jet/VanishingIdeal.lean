/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.VectorBundle.Jet.Basic
public import TauCeti.Geometry.Manifold.VectorBundle.Section.VanishingIdeal
import TauCeti.Analysis.Calculus.IteratedFDeriv.Mul
import TauCeti.Geometry.Manifold.Algebra.VanishingIdeal.Pow
import TauCeti.Geometry.Manifold.MFDeriv.Chart.Basic
import TauCeti.Geometry.Manifold.VectorBundle.Section.Extension

/-!
# Jets of smooth sections and powers of the vanishing ideal

Let `V` be a smooth real vector bundle over a finite-dimensional Hausdorff boundaryless smooth
manifold `M`, and let `I_x` be the ideal of smooth real functions on `M` vanishing at `x`. The
smooth sections `Γ(V)` form a module over `C^∞(M)`, and `I_x ^ (r + 1) Γ(V)` is its submodule of
finite sums `∑ fᵢ sᵢ` with each `fᵢ` a finite sum of products of `r + 1` functions vanishing
at `x`. For `V` of finite rank, a smooth section lies in `I_x ^ (r + 1) Γ(V)` exactly when its
`r`-jet `jʳs(x)` (`TauCeti.JetBundle.jet`) vanishes. Every `r`-jet at `x` is the jet of a global
smooth section, so the `r`-jet at `x` is a surjective linear map from `Γ(V)` onto the fibre of the
jet bundle `JᵣV` at `x` with kernel `I_x ^ (r + 1) Γ(V)`, identifying `Γ(V) / I_x ^ (r + 1) Γ(V)`
with that fibre (`TauCeti.JetBundle.smoothSectionJetEquiv`). This is the analogue for `r`-jets of
the identification of `Γ(V) / I_x Γ(V)` with the fibre `V_x` (`TauCeti.smoothSectionFiberEquiv`).

This is the bridge between the algebraic, Grothendieck description of differential operators
between modules of sections, through iterated commutators with multiplication operators, and the
geometric one through jets: an operator of order at most `r` kills `I_x ^ (r + 1) Γ(V)` modulo
`I_x Γ(W)`, so its value at `x` only depends on the `r`-jet at `x`.

## Main definitions and results

* `TauCeti.JetBundle.jet_eq_zero_of_mem_smoothVanishingIdeal_pow_smul_top`: a smooth section in
  `I_x ^ (r + 1) Γ(V)` has vanishing `r`-jet at `x`; orders of vanishing add under multiplication.
* `TauCeti.JetBundle.jet_eq_zero_iff_mem_smoothVanishingIdeal_pow_smul_top`: for `V` of finite
  rank, the converse holds as well.
* `TauCeti.JetBundle.jetLinearMap`: the `r`-jet at `x` as a real-linear map on smooth sections.
* `TauCeti.JetBundle.ker_jetLinearMap`, `TauCeti.JetBundle.jetLinearMap_surjective`: its kernel is
  `I_x ^ (r + 1) Γ(V)`, and it is onto the fibre of `JᵣV` at `x`.
* `TauCeti.JetBundle.smoothSectionJetEquiv`: the induced real-linear equivalence
  `Γ(V) / I_x ^ (r + 1) Γ(V) ≃ (JᵣV)_x`.

## References

* I. Kolář, P. W. Michor and J. Slovák, *Natural Operations in Differential Geometry*,
  §§12.2–12.5.
* A. Grothendieck, *Éléments de géométrie algébrique IV*, Quatrième partie, §16.7.
-/

public section

noncomputable section

open Bundle Filter Set
open scoped ContDiff Manifold Topology

namespace TauCeti

namespace JetBundle

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {V : M → Type*} [TopologicalSpace (TotalSpace F V)]
  [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)] [∀ x, TopologicalSpace (V x)]
  [FiberBundle F V] [VectorBundle ℝ F V] [ContMDiffVectorBundle ∞ F V I] {r : ℕ}

omit [I.Boundaryless] [IsManifold I ∞ M] [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)]
  [VectorBundle ℝ F V] [ContMDiffVectorBundle ∞ F V I] in
/-- A smooth section is `C^r` at every point. -/
private theorem contMDiffAt_section (s : Cₛ^∞⟮I; F, V⟯) (x : M) :
    ContMDiffAt I (I.prod 𝓘(ℝ, F)) r (fun x ↦ TotalSpace.mk' F x (s x)) x :=
  (s.contMDiff x).of_le (by exact_mod_cast le_top)

/-- The product of a smooth section with a function vanishing to order `r + 1` at `x` has
vanishing `r`-jet at `x`. -/
private theorem jet_smul_eq_zero {x : M} {f : C^∞⟮I, M; ℝ⟯}
    (hf : f ∈ smoothVanishingIdeal I x ^ (r + 1)) (t : Cₛ^∞⟮I; F, V⟯) :
    jet I F r (f • t : Cₛ^∞⟮I; F, V⟯) x = 0 := by
  have hx := FirstJetBundle.mem_baseSet_self (H := H) F V x
  have hxI : I.IsInteriorPoint x := BoundarylessManifold.isInteriorPoint
  rw [jet_eq_zero_iff_forall_iteratedFDeriv_localRep_eq_zero (contMDiffAt_section _ x)]
  intro k hk
  -- Near the image of `x`, the local representative of `f • t` is the chart expression `g` of `f`
  -- times that of `t`, written as the application of `L ∘ g` with `L c = c • id`.
  set g : E → ℝ := (f : M → ℝ) ∘ (extChartAt I x).symm
  have hg : ContDiffAt ℝ ∞ g (extChartAt I x x) :=
    f.contMDiff.contMDiffAt.contDiffAt_comp_extChartAt_symm_of_isInteriorPoint hxI
  let L : ℝ →L[ℝ] F →L[ℝ] F := (ContinuousLinearMap.id ℝ ℝ).smulRight (ContinuousLinearMap.id ℝ F)
  have hloc : FirstJetBundle.localRep I F (f • t : Cₛ^∞⟮I; F, V⟯) x =ᶠ[𝓝 (extChartAt I x x)]
      fun z ↦ (L ∘ g) z (FirstJetBundle.localRep I F t x z) := by
    rw [show ⇑(f • t : Cₛ^∞⟮I; F, V⟯) = fun y ↦ f y • t y from
      funext (ContMDiffSection.smul_apply f t)]
    exact (FirstJetBundle.localRep_smul_eventuallyEq I F f t hx).mono fun z hz ↦ hz.trans (by
      simp [L, g])
  rw [(hloc.iteratedFDeriv ℝ k).eq_of_nhds]
  -- `L ∘ g` vanishes to order `r + 1` at the image of `x`, since `f ∈ I_x ^ (r + 1)`.
  refine iteratedFDeriv_clm_apply_eq_zero_of_lt_add (L.contDiff.contDiffAt.comp _ hg)
    (FirstJetBundle.contDiffAt_localRep I F (t.contMDiff x) hx) (m := r + 1) (n := 0)
    (fun i hi ↦ ?_) (fun i hi ↦ absurd hi (Nat.not_lt_zero i)) (by omega)
    (by exact_mod_cast le_top)
  rw [L.iteratedFDeriv_comp_left hg (by exact_mod_cast le_top),
    iteratedFDeriv_comp_extChartAt_symm_eq_zero_of_mem_smoothVanishingIdeal_pow hxI hf
      (by omega)]
  ext v
  simp [ContinuousLinearMap.compContinuousMultilinearMap_coe]

/-- **Sections in a power of the vanishing ideal have vanishing jets.** A smooth section in
`I_x ^ (r + 1) Γ(V)`, a finite sum of sections times products of `r + 1` smooth functions
vanishing at `x`, has vanishing `r`-jet at `x`. -/
theorem jet_eq_zero_of_mem_smoothVanishingIdeal_pow_smul_top {x : M} {s : Cₛ^∞⟮I; F, V⟯}
    (hs : s ∈ smoothVanishingIdeal I x ^ (r + 1) •
      (⊤ : Submodule C^∞⟮I, M; ℝ⟯ Cₛ^∞⟮I; F, V⟯)) :
    jet I F r s x = 0 := by
  refine Submodule.smul_induction_on hs (fun f hf t _ ↦ jet_smul_eq_zero hf t) fun a b ha hb ↦ ?_
  rw [ContMDiffSection.coe_add, jet_add (contMDiffAt_section a x) (contMDiffAt_section b x), ha,
    hb, add_zero]

variable (I F V r) in
/-- The `r`-jet at `x` of smooth sections, as a real-linear map
`Γ(V) → (JᵣV)_x`, `s ↦ jʳs(x)`. -/
def jetLinearMap (x : M) : Cₛ^∞⟮I; F, V⟯ →ₗ[ℝ] JetBundle I F V r x where
  toFun s := jet I F r s x
  map_add' s t := by
    rw [ContMDiffSection.coe_add]
    exact jet_add (contMDiffAt_section s x) (contMDiffAt_section t x)
  map_smul' c s := by
    rw [ContMDiffSection.coe_smul]
    exact jet_const_smul c (contMDiffAt_section s x)

/-- `TauCeti.JetBundle.jetLinearMap I F V r x` sends a smooth section to its `r`-jet at `x`. -/
@[simp]
theorem jetLinearMap_apply (x : M) (s : Cₛ^∞⟮I; F, V⟯) :
    jetLinearMap I F V r x s = jet I F r s x := (rfl)

variable [FiniteDimensional ℝ E] [T2Space M]

/-- **Jets and powers of the vanishing ideal.** For a smooth real vector bundle `V` of finite
rank, a smooth section has vanishing `r`-jet at `x` if and only if it lies in
`I_x ^ (r + 1) Γ(V)`: it is a finite sum of sections times products of `r + 1` smooth functions
vanishing at `x`. -/
theorem jet_eq_zero_iff_mem_smoothVanishingIdeal_pow_smul_top [FiniteDimensional ℝ F] {x : M}
    (s : Cₛ^∞⟮I; F, V⟯) :
    jet I F r s x = 0 ↔
      s ∈ smoothVanishingIdeal I x ^ (r + 1) • (⊤ : Submodule C^∞⟮I, M; ℝ⟯ Cₛ^∞⟮I; F, V⟯) := by
  refine ⟨fun h ↦ ?_, jet_eq_zero_of_mem_smoothVanishingIdeal_pow_smul_top⟩
  -- The local representative at `x` is the trivialized section read through the chart at `x`.
  have hrep : (fun y ↦ (trivializationAt F V x ⟨y, s y⟩).2) ∘ (extChartAt I x).symm =
      FirstJetBundle.localRep I F s x :=
    funext fun z ↦ (FirstJetBundle.localRep_apply I F s x z).symm
  refine mem_smoothVanishingIdeal_pow_succ_smul_top_of_iteratedFDeriv_eq_zero
    (trivializationAt F V x) (mem_baseSet_trivializationAt F V x)
    BoundarylessManifold.isInteriorPoint fun k hk ↦ ?_
  rw [hrep]
  exact (jet_eq_zero_iff_forall_iteratedFDeriv_localRep_eq_zero (contMDiffAt_section s x)).1
    h k hk

/-- **Equal jets.** For a smooth real vector bundle `V` of finite rank, two smooth sections have
the same `r`-jet at `x` if and only if their difference lies in `I_x ^ (r + 1) Γ(V)`. -/
theorem jet_eq_jet_iff_sub_mem_smoothVanishingIdeal_pow_smul_top [FiniteDimensional ℝ F]
    {x : M} (s t : Cₛ^∞⟮I; F, V⟯) :
    jet I F r s x = jet I F r t x ↔
      s - t ∈ smoothVanishingIdeal I x ^ (r + 1) •
        (⊤ : Submodule C^∞⟮I, M; ℝ⟯ Cₛ^∞⟮I; F, V⟯) := by
  rw [← jet_eq_zero_iff_mem_smoothVanishingIdeal_pow_smul_top, ← jetLinearMap_apply,
    ← jetLinearMap_apply, ← jetLinearMap_apply, map_sub, sub_eq_zero]

/-- The kernel of the `r`-jet at `x` on smooth sections of a finite-rank bundle is
`I_x ^ (r + 1) Γ(V)`. -/
theorem ker_jetLinearMap [FiniteDimensional ℝ F] (x : M) :
    LinearMap.ker (jetLinearMap I F V r x) =
      (smoothVanishingIdeal I x ^ (r + 1) •
        (⊤ : Submodule C^∞⟮I, M; ℝ⟯ Cₛ^∞⟮I; F, V⟯)).restrictScalars ℝ := by
  ext s
  simp [jet_eq_zero_iff_mem_smoothVanishingIdeal_pow_smul_top]

/-- **Every `r`-jet is the jet of a global smooth section.** -/
theorem jetLinearMap_surjective (x : M) : Function.Surjective (jetLinearMap I F V r x) := by
  intro A
  obtain ⟨s, hs, hsA⟩ := exists_contMDiffOn_jet_eq (n := ∞) x A
  -- Cut `s` off near `x` to a global smooth section; this does not change its jet at `x`.
  obtain ⟨t, hts, -, -⟩ := ContMDiffSection.exists_eventuallyEq_isCompact_tsupport_subset
    isCompact_singleton (nhdsSet_singleton (x := x) ▸
      (FirstJetBundle.isOpen_baseSet F V x).mem_nhds (FirstJetBundle.mem_baseSet_self F V x)) hs
  rw [nhdsSet_singleton] at hts
  exact ⟨t, (jet_congr_of_eventuallyEq hts).trans hsA⟩

variable (I F V r) in
/-- **The fibre of the jet bundle is the module of sections modulo a power of the vanishing
ideal.** For a smooth real vector bundle `V` of finite rank over a finite-dimensional Hausdorff
manifold, the `r`-jet at `x` induces a real-linear equivalence
`Γ(V) / I_x ^ (r + 1) Γ(V) ≃ (JᵣV)_x`, the analogue for `r`-jets of
`TauCeti.smoothSectionFiberEquiv`. -/
def smoothSectionJetEquiv [FiniteDimensional ℝ F] (x : M) :
    (Cₛ^∞⟮I; F, V⟯ ⧸ smoothVanishingIdeal I x ^ (r + 1) •
      (⊤ : Submodule C^∞⟮I, M; ℝ⟯ Cₛ^∞⟮I; F, V⟯)) ≃ₗ[ℝ] JetBundle I F V r x :=
  (Submodule.Quotient.restrictScalarsEquiv ℝ _).symm ≪≫ₗ
    Submodule.quotEquivOfEq _ _ (ker_jetLinearMap x).symm ≪≫ₗ
    (jetLinearMap I F V r x).quotKerEquivOfSurjective (jetLinearMap_surjective x)

/-- The equivalence `Γ(V) / I_x ^ (r + 1) Γ(V) ≃ (JᵣV)_x` sends the class of a section to its
`r`-jet at `x`. -/
@[simp]
theorem smoothSectionJetEquiv_mk [FiniteDimensional ℝ F] (x : M) (s : Cₛ^∞⟮I; F, V⟯) :
    smoothSectionJetEquiv I F V r x (Submodule.Quotient.mk s) = jet I F r s x := by
  simp [smoothSectionJetEquiv]

/-- The inverse of `Γ(V) / I_x ^ (r + 1) Γ(V) ≃ (JᵣV)_x` sends the `r`-jet of a section at `x` to
its class. -/
@[simp]
theorem smoothSectionJetEquiv_symm_apply [FiniteDimensional ℝ F] (x : M) (s : Cₛ^∞⟮I; F, V⟯) :
    (smoothSectionJetEquiv I F V r x).symm (jet I F r s x) = Submodule.Quotient.mk s := by
  rw [LinearEquiv.symm_apply_eq, smoothSectionJetEquiv_mk]

end JetBundle

end TauCeti
