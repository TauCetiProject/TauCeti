/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
public import TauCeti.Analysis.Distribution.ComplexPairing
import TauCeti.Analysis.Distribution.Support
import TauCeti.Analysis.Distribution.TestFunction.PartitionOfUnity
import TauCeti.Analysis.Fourier.Decay
import TauCeti.Analysis.PositiveDefinite.FourierAtom

/-!
# The wave front set of a distribution

Let `Ω` be an open subset of a finite-dimensional real inner product space `E` and
`T : 𝓓'(Ω, ℂ)` a complex distribution. Cutting `T` off by a test function `φ` gives a compactly
supported distribution `φ T`, whose Fourier transform is the function `η ↦ T (φ e_η)`, where
`e_η x = 𝐞 (-⟪x, η⟫)` is the character of Mathlib's Fourier transform. This file works directly
with that function, `Distribution.localFourier T φ`, defined through the complex-linear extension
`Distribution.complexPairing` of `T` to complex test functions.

A distribution is smooth near `x` exactly when such localized Fourier transforms decay rapidly in
every direction. The **wave front set** records the directions in which this fails: `T` is
*microlocally smooth* at `(x, ξ)` if some test function `φ` with `φ x ≠ 0` has localized Fourier
transform rapidly decreasing in an open cone containing `ξ`, and the wave front set
`Distribution.waveFrontSet T` consists of the `(x, ξ)` with `x ∈ Ω` and `ξ ≠ 0` at which `T` is
not microlocally smooth.

## Main declarations

* `Distribution.localFourier T φ`: the Fourier transform `η ↦ T (φ e_η)` of `φ T`.
* `Distribution.IsMicrolocallySmoothAt T x ξ`: microlocal smoothness at `(x, ξ)`.
* `Distribution.waveFrontSet T`: the wave front set.

## Main results

* `Distribution.isOpen_setOf_isMicrolocallySmoothAt`, `Distribution.isOpen_diff_waveFrontSet`:
  the wave front set is closed in `Ω × (E \ {0})`.
* `Distribution.smul_mem_waveFrontSet_iff`: it is conic in the frequency variable.
* `Distribution.waveFrontSet_subset_dsupport`: it lies over the support of `T`.
* `Distribution.waveFrontSet_smul`, `Distribution.waveFrontSet_conj`: nonzero scalar multiples
  have the same wave front set, and complex conjugation reflects the frequencies.
* `Distribution.localFourier_eq_fourier`: where `T` is a locally integrable function `f`, the
  localized Fourier transform is the Fourier transform of `φ f`.
* `Distribution.isMicrolocallySmoothAt_of_apply_eq_integral`: there is no wave front set over an
  open set on which `T` is a smooth function; in particular
  `Distribution.waveFrontSet_ofFun_eq_empty` for a function smooth on `Ω`.
* `Distribution.waveFrontSet_delta`: the point mass at `x₀ ∈ Ω` has wave front set
  `{x₀} × (E \ {0})`.

## Implementation notes

The cutoffs `φ` are complex test functions, as in Hörmander's definition. Rapid decay on a set
`Γ` means a bound `(1 + ‖η‖) ^ N * ‖localFourier T φ η‖ ≤ C` on `Γ` for every `N`, and an open
cone is an open set closed under multiplication by positive reals. The complex conjugate of `T`
is `mapCLM conjCLE T`, and the complex point mass at `x₀` is `mapCLM ofRealCLM (delta x₀)`.

## References

* L. Hörmander, *The Analysis of Linear Partial Differential Operators I*, §8.1,
  Definition 8.1.2.
* M. Taylor, *Pseudodifferential Operators: Four Lectures at MSRI*, Lecture I, §7.
-/

public section

noncomputable section

open Complex ComplexConjugate Filter Set TopologicalSpace TestFunction
open scoped Distributions Topology FourierTransform RealInnerProductSpace ContDiff

namespace Distribution

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {Ω : Opens E}

/-- The **localized Fourier transform** `η ↦ T (φ e_η)` of a complex distribution `T` on `Ω`, cut
off by a complex test function `φ`, where `e_η x = 𝐞 (-⟪x, η⟫)`. It is the Fourier transform of
the compactly supported distribution `φ T`. -/
def localFourier (T : 𝓓'(Ω, ℂ)) (φ : 𝓓(Ω, ℂ)) (η : E) : ℂ :=
  T.complexPairing
    (bilinLeftCLM (ContinuousLinearMap.mul ℝ ℂ) (TauCeti.contDiff_fourierChar_neg_inner η) φ)

/-- The localized Fourier transform at `η` pairs `T` with any test function equal to
`x ↦ φ x * 𝐞 (-⟪x, η⟫)`. -/
theorem localFourier_eq (T : 𝓓'(Ω, ℂ)) (φ : 𝓓(Ω, ℂ)) {η : E} {ψ : 𝓓(Ω, ℂ)}
    (hψ : ∀ x, ψ x = φ x * 𝐞 (-⟪x, η⟫)) : T.localFourier φ η = T.complexPairing ψ := by
  rw [localFourier]
  congr 1
  ext x
  simp [hψ]

/-- The localized Fourier transform is additive in the distribution. -/
@[simp]
theorem localFourier_add (T S : 𝓓'(Ω, ℂ)) (φ : 𝓓(Ω, ℂ)) (η : E) :
    (T + S).localFourier φ η = T.localFourier φ η + S.localFourier φ η :=
  complexPairing_add T S _

/-- The localized Fourier transform is complex-linear in the distribution. -/
@[simp]
theorem localFourier_smul (c : ℂ) (T : 𝓓'(Ω, ℂ)) (φ : 𝓓(Ω, ℂ)) (η : E) :
    (c • T).localFourier φ η = c * T.localFourier φ η :=
  complexPairing_smul c T _

/-- A complex distribution `T` is **microlocally smooth** at `(x, ξ)` if some complex test
function `φ` with `φ x ≠ 0` has localized Fourier transform `localFourier T φ` rapidly
decreasing in an open cone `Γ` containing `ξ`. -/
def IsMicrolocallySmoothAt (T : 𝓓'(Ω, ℂ)) (x ξ : E) : Prop :=
  ∃ φ : 𝓓(Ω, ℂ), φ x ≠ 0 ∧ ∃ Γ : Set E, IsOpen Γ ∧ ξ ∈ Γ ∧
    (∀ t : ℝ, 0 < t → ∀ η ∈ Γ, t • η ∈ Γ) ∧
    ∀ N : ℕ, ∃ C, ∀ η ∈ Γ, (1 + ‖η‖) ^ N * ‖T.localFourier φ η‖ ≤ C

/-- Unfolds `IsMicrolocallySmoothAt` into its cutoff, cone and decay witnesses. -/
theorem isMicrolocallySmoothAt_iff {T : 𝓓'(Ω, ℂ)} {x ξ : E} :
    T.IsMicrolocallySmoothAt x ξ ↔
      ∃ φ : 𝓓(Ω, ℂ), φ x ≠ 0 ∧ ∃ Γ : Set E, IsOpen Γ ∧ ξ ∈ Γ ∧
        (∀ t : ℝ, 0 < t → ∀ η ∈ Γ, t • η ∈ Γ) ∧
        ∀ N : ℕ, ∃ C, ∀ η ∈ Γ, (1 + ‖η‖) ^ N * ‖T.localFourier φ η‖ ≤ C :=
  Iff.rfl

/-- The **wave front set** of a complex distribution `T` on `Ω`: the pairs `(x, ξ)` with `x ∈ Ω`
and `ξ ≠ 0` at which `T` is not microlocally smooth. -/
def waveFrontSet (T : 𝓓'(Ω, ℂ)) : Set (E × E) :=
  {p | p.1 ∈ Ω ∧ p.2 ≠ 0 ∧ ¬ T.IsMicrolocallySmoothAt p.1 p.2}

@[simp]
theorem mem_waveFrontSet_iff {T : 𝓓'(Ω, ℂ)} {x ξ : E} :
    (x, ξ) ∈ T.waveFrontSet ↔ x ∈ Ω ∧ ξ ≠ 0 ∧ ¬ T.IsMicrolocallySmoothAt x ξ :=
  Iff.rfl

/-- The wave front set lies in `Ω × (E \ {0})`. -/
theorem waveFrontSet_subset (T : 𝓓'(Ω, ℂ)) :
    T.waveFrontSet ⊆ (Ω : Set E) ×ˢ {0}ᶜ :=
  fun _ hp => ⟨hp.1, hp.2.1⟩

/-- Microlocal smoothness depends only on the ray through the frequency. -/
theorem isMicrolocallySmoothAt_smul_iff {T : 𝓓'(Ω, ℂ)} {x ξ : E} {t : ℝ} (ht : 0 < t) :
    T.IsMicrolocallySmoothAt x (t • ξ) ↔ T.IsMicrolocallySmoothAt x ξ := by
  -- An open cone contains `ξ` exactly when it contains `t • ξ`.
  have key {s : ℝ} (hs : 0 < s) {ζ : E} :
      T.IsMicrolocallySmoothAt x ζ → T.IsMicrolocallySmoothAt x (s • ζ) := by
    rintro ⟨φ, hφ, Γ, hΓ, hζ, hcone, hdecay⟩
    exact ⟨φ, hφ, Γ, hΓ, hcone s hs ζ hζ, hcone, hdecay⟩
  refine ⟨fun h => ?_, key ht⟩
  simpa [smul_smul, inv_mul_cancel₀ ht.ne'] using key (inv_pos.2 ht) h

/-- The wave front set is conic in the frequency variable. -/
theorem smul_mem_waveFrontSet_iff {T : 𝓓'(Ω, ℂ)} {x ξ : E} {t : ℝ} (ht : 0 < t) :
    (x, t • ξ) ∈ T.waveFrontSet ↔ (x, ξ) ∈ T.waveFrontSet := by
  simp [isMicrolocallySmoothAt_smul_iff ht, ht.ne']

/-- The set of points at which a distribution is microlocally smooth is open. -/
theorem isOpen_setOf_isMicrolocallySmoothAt (T : 𝓓'(Ω, ℂ)) :
    IsOpen {p : E × E | T.IsMicrolocallySmoothAt p.1 p.2} := by
  refine isOpen_iff_mem_nhds.2 fun p ⟨φ, hφ, Γ, hΓ, hξ, hcone, hdecay⟩ => ?_
  have hU : IsOpen {y : E | φ y ≠ 0} := isOpen_ne_fun φ.continuous continuous_const
  filter_upwards [(hU.prod hΓ).mem_nhds ⟨hφ, hξ⟩] with q hq
  exact ⟨φ, hq.1, Γ, hΓ, hq.2, hcone, hdecay⟩

/-- The wave front set is closed in `Ω × (E \ {0})`. -/
theorem isOpen_diff_waveFrontSet (T : 𝓓'(Ω, ℂ)) :
    IsOpen (((Ω : Set E) ×ˢ {0}ᶜ) \ T.waveFrontSet) := by
  have h : ((Ω : Set E) ×ˢ {0}ᶜ) \ T.waveFrontSet =
      ((Ω : Set E) ×ˢ {0}ᶜ) ∩ {p : E × E | T.IsMicrolocallySmoothAt p.1 p.2} := by
    ext ⟨x, ξ⟩
    simp only [waveFrontSet, Set.mem_sdiff, mem_inter_iff, mem_prod, mem_compl_iff, mem_ofPred_eq]
    tauto
  rw [h]
  exact (Ω.isOpen.prod isOpen_compl_singleton).inter T.isOpen_setOf_isMicrolocallySmoothAt

/-! ### Scalar multiples and conjugation -/

/-- A scalar multiple of `T` is microlocally smooth wherever `T` is. -/
theorem IsMicrolocallySmoothAt.smul {T : 𝓓'(Ω, ℂ)} {x ξ : E} (h : T.IsMicrolocallySmoothAt x ξ)
    (c : ℂ) : (c • T).IsMicrolocallySmoothAt x ξ := by
  obtain ⟨φ, hφ, Γ, hΓ, hξ, hcone, hdecay⟩ := h
  refine ⟨φ, hφ, Γ, hΓ, hξ, hcone, fun N => ?_⟩
  obtain ⟨C, hC⟩ := hdecay N
  refine ⟨‖c‖ * C, fun η hη => ?_⟩
  rw [localFourier_smul, norm_mul, mul_left_comm]
  exact mul_le_mul_of_nonneg_left (hC η hη) (norm_nonneg c)

/-- A scalar multiple of `T` has wave front set contained in that of `T`. -/
theorem waveFrontSet_smul_subset (c : ℂ) (T : 𝓓'(Ω, ℂ)) :
    (c • T).waveFrontSet ⊆ T.waveFrontSet :=
  fun _ ⟨hx, hξ, hT⟩ => ⟨hx, hξ, fun h => hT (h.smul c)⟩

/-- A nonzero scalar multiple of `T` has the same wave front set as `T`. -/
@[simp]
theorem waveFrontSet_smul {c : ℂ} (hc : c ≠ 0) (T : 𝓓'(Ω, ℂ)) :
    (c • T).waveFrontSet = T.waveFrontSet := by
  refine (waveFrontSet_smul_subset c T).antisymm ?_
  simpa [smul_smul, inv_mul_cancel₀ hc] using waveFrontSet_smul_subset c⁻¹ (c • T)

/-- The negative of `T` has the same wave front set as `T`. -/
@[simp]
theorem waveFrontSet_neg (T : 𝓓'(Ω, ℂ)) : (-T).waveFrontSet = T.waveFrontSet := by
  rw [← neg_one_smul ℂ T, waveFrontSet_smul (neg_ne_zero.2 one_ne_zero)]

/-- The localized Fourier transform of the complex conjugate distribution is the conjugate of the
localized Fourier transform at the opposite frequency, with conjugate cutoff. -/
theorem localFourier_conj (T : 𝓓'(Ω, ℂ)) (φ : 𝓓(Ω, ℂ)) (η : E) :
    (mapCLM conjCLE.toContinuousLinearMap T).localFourier φ η =
      conj (T.localFourier (postcompCLM (𝕜 := ℝ) conjCLE.toContinuousLinearMap φ) (-η)) := by
  set ψ := bilinLeftCLM (ContinuousLinearMap.mul ℝ ℂ) (TauCeti.contDiff_fourierChar_neg_inner η) φ
  set ψ' := postcompCLM (𝕜 := ℝ) conjCLE.toContinuousLinearMap ψ
  rw [localFourier_eq _ _ (ψ := ψ) fun x => rfl, localFourier_eq _ _ (ψ := ψ') fun x => ?_]
  · have hre : postcompCLM (𝕜 := ℝ) reCLM ψ' = postcompCLM (𝕜 := ℝ) reCLM ψ := by
      ext x
      simp [ψ']
    have him : postcompCLM (𝕜 := ℝ) imCLM ψ' = -postcompCLM (𝕜 := ℝ) imCLM ψ := by
      ext x
      simp [ψ']
    simp only [complexPairing_apply, hre, him, map_neg, mapCLM_apply,
      ContinuousLinearEquiv.coe_coe, conjCLE_apply, map_add, map_mul, conj_I, mul_neg, neg_mul]
    ring
  · simp only [ψ', postcompCLM_apply, Function.comp_apply, ContinuousLinearEquiv.coe_coe,
      conjCLE_apply, ψ, bilinLeftCLM_apply, ContinuousLinearMap.mul_apply', map_mul,
      inner_neg_right, neg_neg]
    rw [← Circle.coe_inv_eq_conj, ← AddChar.map_neg_eq_inv, neg_neg]

/-- The complex conjugate of `T` is microlocally smooth at `(x, ξ)` exactly when `T` is
microlocally smooth at `(x, -ξ)`. -/
theorem isMicrolocallySmoothAt_conj_iff {T : 𝓓'(Ω, ℂ)} {x ξ : E} :
    (mapCLM conjCLE.toContinuousLinearMap T).IsMicrolocallySmoothAt x ξ ↔
      T.IsMicrolocallySmoothAt x (-ξ) := by
  -- Conjugating the cutoff and reflecting the cone transfers the decay from `T` to its conjugate.
  have key {S : 𝓓'(Ω, ℂ)} {ζ : E} (h : S.IsMicrolocallySmoothAt x (-ζ)) :
      (mapCLM conjCLE.toContinuousLinearMap S).IsMicrolocallySmoothAt x ζ := by
    obtain ⟨φ, hφ, Γ, hΓ, hζ, hcone, hdecay⟩ := h
    have hφφ : postcompCLM (𝕜 := ℝ) conjCLE.toContinuousLinearMap
        (postcompCLM (𝕜 := ℝ) conjCLE.toContinuousLinearMap φ) = φ := by
      ext y
      simp
    refine ⟨postcompCLM (𝕜 := ℝ) conjCLE.toContinuousLinearMap φ, by simpa using hφ,
      Neg.neg ⁻¹' Γ, hΓ.preimage continuous_neg, hζ, fun t ht η hη => ?_, fun N => ?_⟩
    · simpa [smul_neg] using hcone t ht (-η) hη
    · obtain ⟨C, hC⟩ := hdecay N
      exact ⟨C, fun η hη => by simpa [localFourier_conj, hφφ] using hC (-η) hη⟩
  have hconj : mapCLM conjCLE.toContinuousLinearMap (mapCLM conjCLE.toContinuousLinearMap T) =
      T := by
    ext φ
    simp [mapCLM_apply]
  refine ⟨fun h => ?_, key⟩
  rw [← hconj]
  exact key (by rwa [neg_neg])

/-- Complex conjugation reflects the wave front set in the frequency variable. -/
theorem waveFrontSet_conj (T : 𝓓'(Ω, ℂ)) :
    (mapCLM conjCLE.toContinuousLinearMap T).waveFrontSet =
      Prod.map id Neg.neg ⁻¹' T.waveFrontSet := by
  ext ⟨x, ξ⟩
  simp [isMicrolocallySmoothAt_conj_iff]

/-! ### Support, smooth functions and point masses -/

/-- A distribution whose localized Fourier transform, for a cutoff not vanishing at `x`, decays
rapidly on all of `E` is microlocally smooth at `x` in every direction. -/
theorem isMicrolocallySmoothAt_of_forall_decay {T : 𝓓'(Ω, ℂ)} {x : E} {φ : 𝓓(Ω, ℂ)}
    (hφ : φ x ≠ 0) (h : ∀ N : ℕ, ∃ C, ∀ η, (1 + ‖η‖) ^ N * ‖T.localFourier φ η‖ ≤ C) (ξ : E) :
    T.IsMicrolocallySmoothAt x ξ :=
  ⟨φ, hφ, univ, isOpen_univ, mem_univ ξ, fun _ _ _ _ => mem_univ _,
    fun N => (h N).imp fun _ hC η _ => hC η⟩

/-- The localized Fourier transform of the complex point mass at `x₀`. -/
@[simp]
theorem localFourier_delta (x₀ : E) (φ : 𝓓(Ω, ℂ)) (η : E) :
    (mapCLM ofRealCLM (delta x₀ : 𝓓'(Ω, ℝ))).localFourier φ η = φ x₀ * 𝐞 (-⟪x₀, η⟫) := by
  simp [localFourier]

section FiniteDimensional

variable [FiniteDimensional ℝ E]

/-- A distribution is microlocally smooth in every direction at a point of `Ω` outside its
support. -/
theorem isMicrolocallySmoothAt_of_notMem_dsupport {T : 𝓓'(Ω, ℂ)} {x : E} (hx : x ∈ Ω)
    (hxT : x ∉ dsupport T) (ξ : E) : T.IsMicrolocallySmoothAt x ξ := by
  obtain ⟨φ, hφ, hφx⟩ := exists_tsupport_subset_apply_eq (n := ⊤)
    (inter_mem (isClosed_dsupport.isOpen_compl.mem_nhds hxT) (Ω.isOpen.mem_nhds hx))
    inter_subset_right (1 : ℂ)
  refine isMicrolocallySmoothAt_of_forall_decay (φ := φ) (by simp [hφx])
    (fun N => ⟨0, fun η => ?_⟩) ξ
  -- The cut-off test function vanishes on the open neighbourhood `(tsupport φ)ᶜ` of the support.
  have hzero : T.localFourier φ η = 0 := by
    rw [localFourier, ← map_zero T.complexPairing]
    refine complexPairing_eq_of_eventuallyEq T ?_
    refine (eventuallyEq_of_mem ((isOpen_compl_iff.2 (isClosed_tsupport φ)).mem_nhdsSet.2
      fun y hy hyφ => (hφ hyφ).1 hy) fun y hy => ?_)
    simp [image_eq_zero_of_notMem_tsupport hy]
  simp [hzero]

/-- The wave front set lies over the support of the distribution. -/
theorem waveFrontSet_subset_dsupport (T : 𝓓'(Ω, ℂ)) :
    T.waveFrontSet ⊆ dsupport T ×ˢ univ := by
  rintro ⟨x, ξ⟩ ⟨hx, -, hT⟩
  exact ⟨by_contra fun hxT => hT (isMicrolocallySmoothAt_of_notMem_dsupport hx hxT ξ), trivial⟩

/-- The zero distribution has empty wave front set. -/
@[simp]
theorem waveFrontSet_zero : (0 : 𝓓'(Ω, ℂ)).waveFrontSet = ∅ := by
  have h : dsupport ⇑(0 : 𝓓'(Ω, ℂ)) = ∅ := (dsupport_eq_empty_iff _).2 rfl
  refine subset_empty_iff.1 ((waveFrontSet_subset_dsupport 0).trans ?_)
  rw [h, empty_prod]

/-- The point mass at `x₀ ∈ Ω` has wave front set `{x₀} × (E \ {0})`: it is singular at `x₀` in
every direction. -/
theorem waveFrontSet_delta {x₀ : E} (hx₀ : x₀ ∈ Ω) :
    (mapCLM ofRealCLM (delta x₀ : 𝓓'(Ω, ℝ))).waveFrontSet = {x₀} ×ˢ {0}ᶜ := by
  ext ⟨x, ξ⟩
  refine ⟨fun ⟨hx, hξ, hT⟩ => ⟨by_contra fun hne => hT ?_, hξ⟩, fun ⟨hx, hξ⟩ => ?_⟩
  · -- Away from `x₀`, a cutoff vanishing at `x₀` kills the localized Fourier transform.
    obtain ⟨φ, hφ, hφx⟩ := exists_tsupport_subset_apply_eq (n := ⊤)
      (inter_mem (isOpen_compl_singleton.mem_nhds hne) (Ω.isOpen.mem_nhds hx)) inter_subset_right
      (1 : ℂ)
    have hφx₀ : φ x₀ = 0 := image_eq_zero_of_notMem_tsupport fun h => (hφ h).1 rfl
    exact isMicrolocallySmoothAt_of_forall_decay (φ := φ) (by simp [hφx])
      (fun N => ⟨0, fun η => by simp [hφx₀]⟩) ξ
  · -- At `x₀` the localized Fourier transform has constant modulus `‖φ x₀‖` on every ray.
    rw [mem_singleton_iff] at hx
    subst hx
    refine ⟨hx₀, hξ, fun ⟨φ, hφ, Γ, _, hξΓ, hcone, hdecay⟩ => ?_⟩
    obtain ⟨C, hC⟩ := hdecay 1
    have ha : 0 < ‖φ x‖ := norm_pos_iff.2 hφ
    have hξ' : 0 < ‖ξ‖ := norm_pos_iff.2 hξ
    set t := |C| / (‖φ x‖ * ‖ξ‖) + 1
    have ht : 0 < t := by positivity
    have hbound := hC (t • ξ) (hcone t ht ξ hξΓ)
    simp only [localFourier_delta, norm_mul, Circle.norm_coe, mul_one, pow_one, norm_smul,
      Real.norm_eq_abs, abs_of_pos ht] at hbound
    have htξ : t * ‖ξ‖ * ‖φ x‖ = |C| + ‖ξ‖ * ‖φ x‖ := by
      simp only [t]
      field_simp
    nlinarith [le_abs_self C, mul_pos hξ' ha]

variable [MeasurableSpace E] [BorelSpace E]

/-- If `T` coincides on an open set `U` with a locally integrable function `f`, in the sense that
`T φ = ∫ φ • f` for every real test function `φ` supported in `U`, then for a cutoff `φ` supported
in `U` the localized Fourier transform of `T` is the Fourier transform of `φ f`. -/
theorem localFourier_eq_fourier {T : 𝓓'(Ω, ℂ)} {U : Set E} (hU : IsOpen U) {f : E → ℂ}
    (hf : MeasureTheory.LocallyIntegrableOn f U)
    (hT : ∀ φ : 𝓓(Ω, ℝ), tsupport φ ⊆ U → T φ = ∫ y, φ y • f y) {φ : 𝓓(Ω, ℂ)}
    (hφ : tsupport φ ⊆ U) (η : E) : T.localFourier φ η = 𝓕 (fun y => φ y * f y) η := by
  have hψ : tsupport (bilinLeftCLM (ContinuousLinearMap.mul ℝ ℂ)
      (TauCeti.contDiff_fourierChar_neg_inner η) φ) ⊆ U := by
    rw [bilinLeftCLM_apply]
    exact (tsupport_mul_subset_left (f := φ)).trans hφ
  rw [localFourier, complexPairing_eq_integral hU hf hT hψ, Real.fourier_eq]
  simp only [bilinLeftCLM_apply, ContinuousLinearMap.mul_apply', Circle.smul_def, smul_eq_mul]
  exact MeasureTheory.integral_congr_ae (Eventually.of_forall fun y => by ring)

/-- For a locally integrable function `f` on `Ω`, the localized Fourier transform of `f` cut off by
`φ` is the Fourier transform of `φ f`. -/
theorem localFourier_ofFun {f : E → ℂ} (hf : MeasureTheory.LocallyIntegrableOn f Ω)
    (φ : 𝓓(Ω, ℂ)) (η : E) :
    (ofFun Ω f MeasureTheory.volume ⊤).localFourier φ η = 𝓕 (fun x => φ x * f x) η :=
  localFourier_eq_fourier Ω.isOpen hf (fun _ _ => ofFun_apply hf) φ.tsupport_subset η

/-- **Microlocal smoothness over the smooth part.** If `T` coincides on an open set `U` with a
function `f` smooth on `U`, in the sense that `T φ = ∫ φ • f` for every real test function `φ`
supported in `U`, then `T` is microlocally smooth at every point of `U ∩ Ω` in every direction. -/
theorem isMicrolocallySmoothAt_of_apply_eq_integral {T : 𝓓'(Ω, ℂ)} {U : Set E} (hU : IsOpen U)
    {f : E → ℂ} (hf : ContDiffOn ℝ ∞ f U)
    (hT : ∀ φ : 𝓓(Ω, ℝ), tsupport φ ⊆ U → T φ = ∫ y, φ y • f y) {x : E} (hxU : x ∈ U)
    (hxΩ : x ∈ Ω) (ξ : E) : T.IsMicrolocallySmoothAt x ξ := by
  obtain ⟨φ, hφ, hφx⟩ := exists_tsupport_subset_apply_eq (n := ⊤)
    (inter_mem (hU.mem_nhds hxU) (Ω.isOpen.mem_nhds hxΩ)) inter_subset_right (1 : ℂ)
  have hφU : tsupport φ ⊆ U := hφ.trans inter_subset_left
  -- The product `φ f` is smooth and compactly supported, so its Fourier transform decays rapidly.
  have hg : ContDiff ℝ ∞ fun y => φ y * f y := by
    refine contDiff_iff_contDiffAt.2 fun y => ?_
    by_cases hy : y ∈ U
    · exact φ.contDiff.contDiffAt.mul (hf.contDiffAt (hU.mem_nhds hy))
    · refine (contDiffAt_const (c := (0 : ℂ))).congr_of_eventuallyEq ?_
      filter_upwards [notMem_tsupport_iff_eventuallyEq.1 fun h => hy (hφU h)] with z hz
      simp [hz]
  refine isMicrolocallySmoothAt_of_forall_decay (φ := φ) (by simp [hφx]) (fun N => ?_) ξ
  simpa only [localFourier_eq_fourier hU (hf.continuousOn.locallyIntegrableOn hU.measurableSet) hT
    hφU] using TauCeti.exists_one_add_norm_pow_mul_norm_fourier_le hg
      φ.hasCompactSupport.mul_right N

/-- A function smooth on `Ω` is microlocally smooth at every point of `Ω` in every direction. -/
theorem isMicrolocallySmoothAt_ofFun {f : E → ℂ} (hf : ContDiffOn ℝ ∞ f Ω) {x : E}
    (hx : x ∈ Ω) (ξ : E) : (ofFun Ω f MeasureTheory.volume ⊤).IsMicrolocallySmoothAt x ξ :=
  isMicrolocallySmoothAt_of_apply_eq_integral Ω.isOpen hf
    (fun _ _ => ofFun_apply (hf.continuousOn.locallyIntegrableOn Ω.isOpen.measurableSet)) hx hx ξ

/-- A function smooth on `Ω` has empty wave front set. -/
theorem waveFrontSet_ofFun_eq_empty {f : E → ℂ} (hf : ContDiffOn ℝ ∞ f Ω) :
    (ofFun Ω f MeasureTheory.volume ⊤).waveFrontSet = ∅ :=
  eq_empty_iff_forall_notMem.2 fun _ ⟨hx, _, h⟩ => h (isMicrolocallySmoothAt_ofFun hf hx _)

end FiniteDimensional

end Distribution
