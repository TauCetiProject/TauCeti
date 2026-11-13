/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.DifferentialOperator.Section
import TauCeti.Geometry.Manifold.DifferentialOperator.Peetre.Basic
import TauCeti.Geometry.Manifold.VectorBundle.Section.LocalFrameCoeff
import TauCeti.RingTheory.Ideal.Operations

/-!
# Peetre's theorem for operators between sections of vector bundles

Let `V` be a smooth real vector bundle of finite rank over a finite-dimensional Hausdorff
boundaryless manifold `M`, let `W` be a topological real vector bundle over `M`, and let `P` be a
linear map from the smooth sections `Γ(V)` to the sections of `W`. Suppose that on an open set `U`
the operator `P` is *local*, that is `(P s) x = 0` whenever `s` vanishes on a neighbourhood of
`x ∈ U`, and that every `P s` is continuous on `U`. No continuity of `P` itself is assumed.
Peetre's theorem says that `P` then has locally finite order: for every compact `K ⊆ U` there is
`r` such that `(P s) x = 0` whenever `x ∈ K` and `s` lies in `I_x ^ (r + 1) Γ(V)`, the submodule of
finite sums `∑ fᵢ sᵢ` with every `fᵢ` in the `(r + 1)`-st power of the ideal `I_x` of smooth
functions vanishing at `x`
(`LinearMap.exists_apply_eq_zero_of_mem_smoothVanishingIdeal_pow_smul_top`). The quotient
`Γ(V) / I_x ^ (r + 1) Γ(V)` is the algebraic space of `r`-jets of sections at `x` (for functions,
`TauCeti.quotient_mk_smoothVanishingIdeal_pow_succ_eq_iff` identifies it with chart derivatives of
order at most `r`), so `(P s) x` depends only on the `r`-jet of `s` at `x`.

The proof reduces to the scalar theorem
`LinearMap.exists_apply_eq_zero_of_mem_smoothVanishingIdeal_pow`. Near a point `x₀ ∈ U`, take a
local frame `eᵢ` of `V`, global smooth sections `tᵢ` equal to `eᵢ` near `x₀`, and the coefficient
functionals of the frame cut off by a bump function at `x₀`. The latter are `C^∞(M)`-linear maps
`cᵢ : Γ(V) → C^∞(M)` with `s = ∑ cᵢ(s) tᵢ` near `x₀`. By locality `(P s) y = ∑ (Pᵢ (cᵢ s)) y`
for `y` there, where the scalar operators `Pᵢ f = P (f tᵢ)` are again local. Linearity of `cᵢ`
over `C^∞(M)` sends `I_y ^ (r + 1) Γ(V)` into `I_y ^ (r + 1)`, so the scalar theorem for the
`Pᵢ`, read in a trivialization of `W`, gives a common order near `x₀`. A finite cover of `K` gives
the uniform order.

Conversely, a differential operator of order `r` in Grothendieck's sense is local
(`TauCeti.differentialOperators_section_apply_eq_zero_of_eventuallyEq`), and for a finite-rank
smooth bundle `W` a linear map `Γ(V) → Γ(W)` has order `r` exactly when `(P s) x = 0` for every `x`
and every `s ∈ I_x ^ (r + 1) Γ(V)`
(`TauCeti.mem_differentialOperators_section_iff_forall_apply_eq_zero`); both facts are proved in
`TauCeti.Geometry.Manifold.DifferentialOperator.Section`. On a compact manifold the order given by
Peetre's theorem is bounded, so for compact `M`, a linear map `Γ(V) → Γ(W)` is local if and only
if it is a differential operator of finite order
(`LinearMap.exists_mem_differentialOperators_section_iff_apply_eq_zero_of_eventuallyEq`).

## Main results

* `LinearMap.exists_apply_eq_zero_of_mem_smoothVanishingIdeal_pow_smul_top`: **Peetre's theorem**
  for local operators between sections of vector bundles.
* `LinearMap.exists_apply_eq_apply_of_sub_mem_smoothVanishingIdeal_pow_smul_top`: its jet form.
* `LinearMap.exists_mem_differentialOperators_section_iff_apply_eq_zero_of_eventuallyEq`: on a
  compact manifold the local operators `Γ(V) → Γ(W)` are exactly the differential operators.

## References

* J. Peetre, *Réctification à l'article « Une caractérisation abstraite des opérateurs
  différentiels »*, Math. Scand. 8 (1960), 116–120.
* I. Kolář, P. W. Michor, J. Slovák, *Natural Operations in Differential Geometry*, Springer,
  1993, Theorem 19.1.
* A. Grothendieck, *Éléments de géométrie algébrique IV*, Quatrième partie, §16.8.
-/

public section

open Bundle Set Filter Module
open scoped ContDiff Manifold Topology

noncomputable section

namespace LinearMap

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {V : M → Type*} [TopologicalSpace (TotalSpace F V)]
  [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)] [∀ x, TopologicalSpace (V x)]
  [FiberBundle F V] [VectorBundle ℝ F V] [ContMDiffVectorBundle ∞ F V I]
  {F' : Type*} [NormedAddCommGroup F'] [NormedSpace ℝ F']
  {W : M → Type*} [TopologicalSpace (TotalSpace F' W)]
  [∀ x, AddCommGroup (W x)] [∀ x, Module ℝ (W x)] [∀ x, TopologicalSpace (W x)]
  [FiberBundle F' W] [VectorBundle ℝ F' W]

variable [BoundarylessManifold I M]

/-- **Peetre's theorem** for sections, local form: near each point `x₀` of `U` there is a common
order `r` such that `(P s) y = 0` for every `y` near `x₀` and every `s ∈ I_y ^ (r + 1) Γ(V)`. -/
private theorem exists_mem_nhds_forall_apply_eq_zero_section
    (P : Cₛ^∞⟮I; F, V⟯ →ₗ[ℝ] Π x, W x) {U : Set M} (hU : IsOpen U)
    (hloc : ∀ s : Cₛ^∞⟮I; F, V⟯, ∀ x ∈ U, (∀ᶠ y in 𝓝 x, s y = 0) → P s x = 0)
    (hcont : ∀ s, ContinuousOn (fun x ↦ TotalSpace.mk' F' x (P s x)) U) {x₀ : M}
    (hx₀ : x₀ ∈ U) :
    ∃ N ∈ 𝓝 x₀, ∃ r : ℕ, ∀ y ∈ N, ∀ s ∈ TauCeti.smoothVanishingIdeal I y ^ (r + 1) •
      (⊤ : Submodule C^∞⟮I, M; ℝ⟯ Cₛ^∞⟮I; F, V⟯), P s y = 0 := by
  classical
  let e := trivializationAt F V x₀
  let e' := trivializationAt F' W x₀
  let b := Module.finBasis ℝ F
  have he : e.baseSet ∈ 𝓝 x₀ := e.open_baseSet.mem_nhds (mem_baseSet_trivializationAt F V x₀)
  obtain ⟨ρ, hρ, -⟩ := (SmoothBumpFunction.nhds_basis_support (I := I) he).mem_iff.mp he
  let c := e.cutoffLocalFrameCoeff b ⟨ρ, ρ.contMDiff⟩ hρ
  obtain ⟨fr', hfr', hfreq⟩ :=
    e.exists_contMDiff_eventuallyEq_localFrame (I := I) b (mem_baseSet_trivializationAt F V x₀)
  let fr (i : Fin (finrank ℝ F)) : Cₛ^∞⟮I; F, V⟯ := ⟨fr' i, hfr' i⟩
  -- Near `x₀`, `ρ = 1` and the global sections `fr i` agree with the local frame of `e`.
  set G := {y | ρ y = 1 ∧ ∀ i, fr' i y = e.localFrame b i y}
  have hG : G ∈ 𝓝 x₀ := ρ.eventuallyEq_one.and (eventually_all.2 hfreq)
  -- The scalar operators `f ↦ P (f • fr i)`, read in the trivialization `e'` of `W`.
  let Q (i : Fin (finrank ℝ F)) : C^∞⟮I, M; ℝ⟯ →ₗ[ℝ] M → F' :=
    { toFun := fun f y ↦ e'.continuousLinearMapAt ℝ y (P (f • fr i) y)
      map_add' := fun f g ↦ by
        ext y
        simp [add_smul]
      map_smul' := fun a f ↦ by
        ext y
        simp [smul_assoc] }
  have hQ (i : Fin (finrank ℝ F)) (f : C^∞⟮I, M; ℝ⟯) (y : M) :
      Q i f y = e'.continuousLinearMapAt ℝ y (P (f • fr i) y) := (rfl)
  set U' := U ∩ e'.baseSet
  have hU' : IsOpen U' := hU.inter e'.open_baseSet
  have hQloc (i : Fin (finrank ℝ F)) (f : C^∞⟮I, M; ℝ⟯) (x : M) (hx : x ∈ U')
      (hf : (f : M → ℝ) =ᶠ[𝓝 x] 0) : Q i f x = 0 := by
    have hfi : ∀ᶠ y in 𝓝 x, (f • fr i) y = 0 := by
      filter_upwards [hf] with y hy
      rw [ContMDiffSection.smul_apply, hy, Pi.zero_apply, zero_smul]
    rw [hQ, hloc _ x hx.1 hfi, map_zero]
  have hQcont (i : Fin (finrank ℝ F)) (f : C^∞⟮I, M; ℝ⟯) : ContinuousOn (Q i f) U' := by
    refine (continuous_snd.comp_continuousOn (e'.continuousOn.comp
      ((hcont (f • fr i)).mono inter_subset_left) fun y hy ↦ e'.mem_source.2 hy.2)).congr
      fun y hy ↦ ?_
    rw [hQ, Trivialization.continuousLinearMapAt_apply_of_mem (R := ℝ) e' hy.2,
      Function.comp_apply, Function.comp_apply]
  -- A compact neighbourhood of `x₀` inside `G` on which the scalar theorem applies.
  have hx₀' : x₀ ∈ U' ∩ interior G :=
    ⟨⟨hx₀, mem_baseSet_trivializationAt F' W x₀⟩, mem_interior_iff_mem_nhds.2 hG⟩
  have : LocallyCompactSpace M := Manifold.locallyCompact_of_finiteDimensional I
  obtain ⟨K, hK, hx₀K, hKsub⟩ := exists_compact_subset (hU'.inter isOpen_interior) hx₀'
  choose r hr using fun i ↦ exists_apply_eq_zero_of_mem_smoothVanishingIdeal_pow (Q i) hU'
    (hQloc i) (hQcont i) hK (hKsub.trans inter_subset_left)
  refine ⟨K, mem_interior_iff_mem_nhds.1 hx₀K, Finset.univ.sup r, fun y hy s hs ↦ ?_⟩
  -- Near `y`, `s` is the sum of the `c i s • fr i`.
  have hsum : P s y = ∑ i, P (c i s • fr i) y := by
    have h := hloc (s - ∑ i, c i s • fr i) y (hKsub hy).1.1 <| by
      filter_upwards [isOpen_interior.mem_nhds (hKsub hy).2] with z hz
      rw [ContMDiffSection.coe_sub, Pi.sub_apply, sub_eq_zero]
      exact e.apply_eq_sum_cutoffLocalFrameCoeff_smul b ⟨ρ, ρ.contMDiff⟩ hρ fr s
        (interior_subset hz).1 (interior_subset hz).2
    rwa [map_sub, map_sum, Pi.sub_apply, Finset.sum_apply, sub_eq_zero] at h
  rw [hsum]
  refine Finset.sum_eq_zero fun i _ ↦ ?_
  have hci : c i s ∈ TauCeti.smoothVanishingIdeal I y ^ (r i + 1) :=
    Ideal.pow_le_pow_right (Nat.succ_le_succ (Finset.le_sup (Finset.mem_univ i)))
      ((c i).apply_mem_of_mem_smul_top hs)
  have h := hr i y hy _ hci
  rw [hQ] at h
  rw [← e'.symmL_continuousLinearMapAt (R := ℝ) (hKsub hy).1.2 (P _ y), h, map_zero]

/-- **Peetre's theorem** for operators between sections of vector bundles. Let `V` be a smooth
real vector bundle of finite rank over a finite-dimensional Hausdorff boundaryless manifold, `W` a
topological real vector bundle, and `P` a linear map from the smooth sections of `V` to the
sections of `W`. Suppose that `P` is local on the open set `U` (`(P s) x = 0` whenever `s`
vanishes near `x ∈ U`) and that every `P s` is continuous on `U`. Then `P` has locally finite
order: for every compact `K ⊆ U` there is `r` such that `(P s) x = 0` whenever `x ∈ K` and `s` is
a finite sum of sections times products of `r + 1` smooth functions vanishing at `x`. No
continuity of `P` is assumed. -/
theorem exists_apply_eq_zero_of_mem_smoothVanishingIdeal_pow_smul_top
    (P : Cₛ^∞⟮I; F, V⟯ →ₗ[ℝ] Π x, W x) {U : Set M} (hU : IsOpen U)
    (hloc : ∀ s : Cₛ^∞⟮I; F, V⟯, ∀ x ∈ U, (∀ᶠ y in 𝓝 x, s y = 0) → P s x = 0)
    (hcont : ∀ s, ContinuousOn (fun x ↦ TotalSpace.mk' F' x (P s x)) U) {K : Set M}
    (hK : IsCompact K) (hKU : K ⊆ U) :
    ∃ r : ℕ, ∀ x ∈ K, ∀ s ∈ TauCeti.smoothVanishingIdeal I x ^ (r + 1) •
      (⊤ : Submodule C^∞⟮I, M; ℝ⟯ Cₛ^∞⟮I; F, V⟯), P s x = 0 := by
  choose! N hN r hr using fun x (hx : x ∈ U) ↦
    exists_mem_nhds_forall_apply_eq_zero_section P hU hloc hcont hx
  obtain ⟨t, htK, hKt⟩ := hK.elim_nhds_subcover N fun x hx ↦ hN x (hKU hx)
  refine ⟨t.sup r, fun x hx s hs ↦ ?_⟩
  obtain ⟨c, hct, hxc⟩ := mem_iUnion₂.mp (hKt hx)
  exact hr c (hKU (htK c hct)) x hxc s
    (Submodule.smul_mono_left (Ideal.pow_le_pow_right
      (Nat.succ_le_succ (Finset.le_sup hct))) hs)

/-- **Peetre's theorem** for sections, in jet form: for every compact `K ⊆ U` there is `r` such
that `(P s) x = (P t) x` whenever `x ∈ K` and `s`, `t` have the same `r`-jet at `x`, that is,
`s - t ∈ I_x ^ (r + 1) Γ(V)`. -/
theorem exists_apply_eq_apply_of_sub_mem_smoothVanishingIdeal_pow_smul_top
    (P : Cₛ^∞⟮I; F, V⟯ →ₗ[ℝ] Π x, W x) {U : Set M} (hU : IsOpen U)
    (hloc : ∀ s : Cₛ^∞⟮I; F, V⟯, ∀ x ∈ U, (∀ᶠ y in 𝓝 x, s y = 0) → P s x = 0)
    (hcont : ∀ s, ContinuousOn (fun x ↦ TotalSpace.mk' F' x (P s x)) U) {K : Set M}
    (hK : IsCompact K) (hKU : K ⊆ U) :
    ∃ r : ℕ, ∀ x ∈ K, ∀ s t : Cₛ^∞⟮I; F, V⟯, s - t ∈ TauCeti.smoothVanishingIdeal I x ^ (r + 1) •
      (⊤ : Submodule C^∞⟮I, M; ℝ⟯ Cₛ^∞⟮I; F, V⟯) → P s x = P t x := by
  obtain ⟨r, hr⟩ :=
    exists_apply_eq_zero_of_mem_smoothVanishingIdeal_pow_smul_top P hU hloc hcont hK hKU
  refine ⟨r, fun x hx s t hst ↦ ?_⟩
  have h := hr x hx _ hst
  rwa [map_sub, Pi.sub_apply, sub_eq_zero] at h

/-- **Local operators between sections over a compact manifold are differential operators.** Let
`V` and `W` be smooth real vector bundles of finite rank over a compact finite-dimensional
Hausdorff boundaryless manifold `M`. A linear map `P : Γ(V) → Γ(W)` is local, that is
`(P s) x = 0` whenever `s` vanishes near `x`, if and only if it is a differential operator of some
finite order in Grothendieck's sense: for some `r`, all its `(r + 1)`-fold commutators with
multiplication by smooth functions vanish. No continuity of `P` is assumed. -/
theorem exists_mem_differentialOperators_section_iff_apply_eq_zero_of_eventuallyEq
    [CompactSpace M] [FiniteDimensional ℝ F'] [ContMDiffVectorBundle ∞ F' W I]
    (P : Cₛ^∞⟮I; F, V⟯ →ₗ[ℝ] Cₛ^∞⟮I; F', W⟯) :
    (∃ r, P ∈ TauCeti.differentialOperators ℝ C^∞⟮I, M; ℝ⟯ Cₛ^∞⟮I; F, V⟯ Cₛ^∞⟮I; F', W⟯ r) ↔
      ∀ (s : Cₛ^∞⟮I; F, V⟯) (x : M), (∀ᶠ y in 𝓝 x, s y = 0) → P s x = 0 := by
  constructor
  · rintro ⟨r, hP⟩ s x hs
    exact TauCeti.differentialOperators_section_apply_eq_zero_of_eventuallyEq hP hs
  · intro hloc
    obtain ⟨r, hr⟩ := exists_apply_eq_zero_of_mem_smoothVanishingIdeal_pow_smul_top
      (LinearMap.pi (ContMDiffSection.evalLinearMap I F' ∞ W) ∘ₗ P) isOpen_univ
      (fun s x _ hs ↦ by simpa using hloc s x hs)
      (fun s ↦ by simpa using (P s).contMDiff.continuous) isCompact_univ subset_rfl
    exact ⟨r, TauCeti.mem_differentialOperators_section_iff_forall_apply_eq_zero.2
      fun x s hs ↦ by simpa using hr x (mem_univ x) s hs⟩

end LinearMap
