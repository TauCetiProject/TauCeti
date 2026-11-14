/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.ProdL2
public import TauCeti.Analysis.Distribution.LinearEquiv
public import TauCeti.Analysis.Distribution.TensorProduct
public import TauCeti.Analysis.Distribution.WaveFrontSet.Localization
import TauCeti.Analysis.Distribution.Support
import TauCeti.Analysis.Distribution.TestFunction.PartitionOfUnity
import TauCeti.Analysis.Normed.Lp.ProdLp
import TauCeti.Analysis.Normed.Module.Cone
import TauCeti.Analysis.PositiveDefinite.FourierAtom

/-!
# The wave front set of a tensor product

Let `S` and `T` be complex distributions on open subsets `Ω` and `O` of finite-dimensional real
inner product spaces `E` and `D`. Their tensor product `S ⊗ T` (`Distribution.tensorProduct`)
is a distribution on `Ω × O`. Wave front sets pair positions with frequencies through an inner
product, so `S ⊗ T` is moved to the Euclidean product `WithLp 2 (E × D)`, whose inner product is
`⟪(x, y), (ξ, η)⟫ = ⟪x, ξ⟫ + ⟪y, η⟫`, by `Distribution.transportCLM`. On any open set `W` of
that space lying over `Ω × O` we prove (Hörmander I, Theorem 8.2.9)

`WF(S ⊗ T) ⊆ (WF(S) × WF(T)) ∪ ((supp S × {0}) × WF(T)) ∪ (WF(S) × (supp T × {0}))`,

with a covector `((x, y), (ξ, η))` written as the pair of `(x, ξ)` and `(y, η)`. The terms with a
zero covector in one factor account for directions in which only the other factor is singular.

These terms are exact: a covector `((x, y), (ξ, 0))` lies in `WF(S ⊗ T)` if and only if
`(x, ξ) ∈ WF(S)` and `y ∈ supp T`, and symmetrically. So if `T` has no wave front set, for
instance if it is a smooth function, then

`WF(S ⊗ T) = {((x, y), (ξ, 0)) | (x, ξ) ∈ WF(S), y ∈ supp T}`.

For `T = 1` the tensor product `S ⊗ 1` is the pullback of `S` along the projection
`(x, y) ↦ x`, a submersion, and its wave front set consists exactly of the covectors of `S`
pulled back by the projection. Hörmander I, Theorem 8.2.4, gives the inclusion for pullbacks along
general smooth maps. For example `δ_{x₀} ⊗ 1` is singular exactly at the points of `W` over `x₀`,
in the directions `(ξ, 0)` with `ξ ≠ 0`.

## Main results

* `Distribution.localFourier_transportCLM_tensorProduct`: the localized Fourier transform of
  `S ⊗ T` with a product cutoff is the product of the localized Fourier transforms.
* `Distribution.IsMicrolocallySmoothAt.transportCLM_tensorProduct_left`,
  `Distribution.IsMicrolocallySmoothAt.transportCLM_tensorProduct_right`: if `S` is microlocally
  smooth at `(x, ξ)` with `ξ ≠ 0`, then `S ⊗ T` is microlocally smooth at `((x, y), (ξ, η))` for
  every `y` and `η`, and symmetrically in `T`.
* `Distribution.waveFrontSet_transportCLM_tensorProduct_subset`: the wave front set bound for
  `S ⊗ T`.
* `Distribution.IsMicrolocallySmoothAt.of_transportCLM_tensorProduct_left`,
  `Distribution.IsMicrolocallySmoothAt.of_transportCLM_tensorProduct_right`: if `S ⊗ T` is
  microlocally smooth at `((x, y), (ξ, 0))` and `y ∈ supp T`, then `S` is microlocally smooth at
  `(x, ξ)`, and symmetrically in `T`.
* `Distribution.mem_waveFrontSet_transportCLM_tensorProduct_iff_of_snd_eq_zero`,
  `Distribution.mem_waveFrontSet_transportCLM_tensorProduct_iff_of_fst_eq_zero`: the exact
  description of the covectors of `WF(S ⊗ T)` with a zero component.
* `Distribution.waveFrontSet_transportCLM_tensorProduct_of_waveFrontSet_right_eq_empty`,
  `Distribution.waveFrontSet_transportCLM_tensorProduct_of_waveFrontSet_left_eq_empty`: the wave
  front set of a tensor product with a factor that has none.
* `Distribution.waveFrontSet_transportCLM_tensorProduct_ofFun_const`: the wave front set of the
  pullback `S ⊗ 1` along the first projection, and more generally of `S ⊗ c` for a constant
  `c ≠ 0`.
* `Distribution.waveFrontSet_transportCLM_tensorProduct_delta_ofFun_one`: the example
  `δ_{x₀} ⊗ 1`.

## Implementation notes

The localized Fourier transform of `S ⊗ T` with a product cutoff `(x, y) ↦ φ x ψ y` is the product
`(φ S)^(ξ) (ψ T)^(η)` of those of `S` and `T`. If `(φ S)^` decays rapidly on an open cone around
`ξ ≠ 0`, then so does the product on the open cone of those `(ξ', η')` with `ξ'` in that cone and
`‖η'‖ < c ‖ξ'‖`, because `(ψ T)^` grows at most polynomially and `‖(ξ', η')‖` is comparable to
`‖ξ'‖` there.

Conversely, near a point `y` of the support of `T` there is a cutoff `ψ` with
`(ψ T)^(0) = T ψ ≠ 0`. Along the frequencies `(ξ', 0)` the localized Fourier transform of
`S ⊗ T` with cutoff `(x, y) ↦ φ x ψ y` is `(φ S)^(ξ') T ψ`, so rapid decay of the former on an
open cone around `(ξ, 0)` gives rapid decay of `(φ S)^` on the open cone of those `ξ'` with
`(ξ', 0)` in it.

## References

* L. Hörmander, *The Analysis of Linear Partial Differential Operators I*, §8.2, Theorem 8.2.4
  (the wave front set of a pullback, an inclusion) and Theorem 8.2.9.
* C. Brouder, N. V. Dang, F. Hélein, *Continuity of the fundamental operations on distributions
  having a specified wave front set*, arXiv:1409.7662v2, Theorem 4.6.
-/

public section

noncomputable section

open Complex Filter Set TopologicalSpace TestFunction WithLp
open scoped Distributions Topology RealInnerProductSpace ContDiff

namespace Distribution

variable {E D : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup D] [InnerProductSpace ℝ D] [FiniteDimensional ℝ D]
  {Ω : Opens E} {O : Opens D} {V : Opens (E × D)} {W : Opens (WithLp 2 (E × D))}
  (S : 𝓓'(Ω, ℂ)) (T : 𝓓'(O, ℂ)) (hV : (V : Set (E × D)) = (Ω : Set E) ×ˢ (O : Set D))
  (hW : MapsTo (prodContinuousLinearEquiv 2 ℝ E D) W V)

omit [FiniteDimensional ℝ D] in
/-- **The localized Fourier transform of a tensor product.** For a cutoff
`χ (x, y) = φ x * ψ y` on `W ⊆ WithLp 2 (E × D)`, the localized Fourier transform of `S ⊗ T` at
`(ξ, η)` is the product of the localized Fourier transforms of `S` at `ξ` and of `T` at `η`. -/
theorem localFourier_transportCLM_tensorProduct {φ : 𝓓(Ω, ℂ)} {ψ : 𝓓(O, ℂ)} {χ : 𝓓(W, ℂ)}
    (hχ : ∀ p, χ p = φ p.fst * ψ p.snd) (ζ : WithLp 2 (E × D)) :
    (transportCLM (prodContinuousLinearEquiv 2 ℝ E D) hW
        (S.tensorProduct T hV.subset)).localFourier χ ζ =
      S.localFourier φ ζ.fst * T.localFourier ψ ζ.snd := by
  rw [localFourier_eq _ χ (ψ := bilinLeftCLM (ContinuousLinearMap.mul ℝ ℂ)
      (TauCeti.contDiff_fourierAtom ζ) χ) fun _ ↦ by
      simp only [bilinLeftCLM_apply, ContinuousLinearMap.mul_apply',
        TauCeti.fourierAtom_eq_fourierChar],
    localFourier_eq S φ (ψ := bilinLeftCLM (ContinuousLinearMap.mul ℝ ℂ)
      (TauCeti.contDiff_fourierAtom ζ.fst) φ) fun _ ↦ by
        simp only [bilinLeftCLM_apply, ContinuousLinearMap.mul_apply',
          TauCeti.fourierAtom_eq_fourierChar],
    localFourier_eq T ψ (ψ := bilinLeftCLM (ContinuousLinearMap.mul ℝ ℂ)
      (TauCeti.contDiff_fourierAtom ζ.snd) ψ) fun _ ↦ by
        simp only [bilinLeftCLM_apply, ContinuousLinearMap.mul_apply',
          TauCeti.fourierAtom_eq_fourierChar],
    complexPairing_transportCLM]
  refine complexPairing_tensorProduct_eq_mul S T hV.subset hV.symm.subset fun q ↦ ?_
  -- The character of `(ξ, η)` at `(x, y)` is the product of the characters of `ξ` at `x` and of
  -- `η` at `y`.
  simp only [ContinuousLinearEquiv.transportTestFunction_apply,
    prodContinuousLinearEquiv_symm_apply, bilinLeftCLM_apply, ContinuousLinearMap.mul_apply',
    hχ, toLp_fst, toLp_snd, TauCeti.fourierAtom_eq_fourierChar, prod_inner_apply,
    ofLp_fst, ofLp_snd, neg_add, AddChar.map_add_eq_mul, Circle.coe_mul]
  ring

/-- Around a point `p` of `W`, a cutoff `φ` near `p.fst` inside `U₁` and a cutoff `ψ` near
`p.snd` inside `U₂` give a product cutoff on `W`, not vanishing at `p`, for which the localized
Fourier transform of `S ⊗ T` is the product of those of `S` and `T`. -/
private theorem exists_prod_cutoff {p : WithLp 2 (E × D)} (hp : p ∈ W) {U₁ : Set E}
    (hU₁ : U₁ ∈ 𝓝 p.fst) {U₂ : Set D} (hU₂ : U₂ ∈ 𝓝 p.snd) :
    ∃ (φ : 𝓓(Ω, ℂ)) (ψ : 𝓓(O, ℂ)) (χ : 𝓓(W, ℂ)), tsupport φ ⊆ U₁ ∧ tsupport ψ ⊆ U₂ ∧
      χ p ≠ 0 ∧ ∀ ζ, (transportCLM (prodContinuousLinearEquiv 2 ℝ E D) hW
        (S.tensorProduct T hV.subset)).localFourier χ ζ =
          S.localFourier φ ζ.fst * T.localFourier ψ ζ.snd := by
  have hpV : p.fst ∈ Ω ∧ p.snd ∈ O := by simpa [hV] using hW hp
  obtain ⟨B₁, hB₁, B₂, hB₂, hprod⟩ := exists_nhds_prod_cutoff (Ω := Ω) (O := O) hp
  obtain ⟨φ, hφ, hφp⟩ := exists_tsupport_subset_apply_eq (n := ⊤)
    (inter_mem (inter_mem hU₁ hB₁) (Ω.isOpen.mem_nhds hpV.1)) inter_subset_right (1 : ℂ)
  obtain ⟨ψ, hψ, hψp⟩ := exists_tsupport_subset_apply_eq (n := ⊤)
    (inter_mem (inter_mem hU₂ hB₂) (O.isOpen.mem_nhds hpV.2)) inter_subset_right (1 : ℂ)
  obtain ⟨χ, hχ, -⟩ := hprod φ ψ (fun _ hx ↦ (hφ hx).1.2) fun _ hy ↦ (hψ hy).1.2
  exact ⟨φ, ψ, χ, fun _ hx ↦ (hφ hx).1.1, fun _ hy ↦ (hψ hy).1.1,
    by simp [hχ, hφp, hψp], localFourier_transportCLM_tensorProduct S T hV hW hχ⟩

omit [FiniteDimensional ℝ D] in
/-- Around a point `p` of `W`, given properties `P` and `Q` of cutoffs that are satisfied by
cutoffs supported in every neighbourhood of `p.fst` and of `p.snd` respectively, some cutoffs with
these properties have a product cutoff on `W` supported in a prescribed neighbourhood `U` of `p`. -/
private theorem exists_prod_cutoff_subset {p : WithLp 2 (E × D)} (hp : p ∈ W)
    {U : Set (WithLp 2 (E × D))} (hU : U ∈ 𝓝 p) {P : 𝓓(Ω, ℂ) → Prop} {Q : 𝓓(O, ℂ) → Prop}
    (hP : ∀ U₁ ∈ 𝓝 p.fst, ∃ φ : 𝓓(Ω, ℂ), tsupport φ ⊆ U₁ ∧ P φ)
    (hQ : ∀ U₂ ∈ 𝓝 p.snd, ∃ ψ : 𝓓(O, ℂ), tsupport ψ ⊆ U₂ ∧ Q ψ) :
    ∃ (φ : 𝓓(Ω, ℂ)) (ψ : 𝓓(O, ℂ)) (χ : 𝓓(W, ℂ)), P φ ∧ Q ψ ∧ tsupport χ ⊆ U ∧
      ∀ ζ, (transportCLM (prodContinuousLinearEquiv 2 ℝ E D) hW
        (S.tensorProduct T hV.subset)).localFourier χ ζ =
          S.localFourier φ ζ.fst * T.localFourier ψ ζ.snd := by
  obtain ⟨B₁, hB₁, B₂, hB₂, hprod⟩ := exists_nhds_prod_cutoff (Ω := Ω) (O := O) hp
  -- A box `U₁ × U₂` around `p` whose Euclidean copy lies in `U`.
  have hU' : toLp 2 ⁻¹' U ∈ 𝓝 (ofLp p) :=
    (prod_continuous_toLp 2 E D).continuousAt.preimage_mem_nhds (by simpa using hU)
  obtain ⟨U₁, hU₁, U₂, hU₂, hUU⟩ := mem_nhds_prod_iff.1 hU'
  obtain ⟨φ, hφ, hPφ⟩ := hP _ (inter_mem hU₁ hB₁)
  obtain ⟨ψ, hψ, hQψ⟩ := hQ _ (inter_mem hU₂ hB₂)
  obtain ⟨χ, hχ, hχK⟩ := hprod φ ψ (fun _ hx ↦ (hφ hx).2) fun _ hy ↦ (hψ hy).2
  refine ⟨φ, ψ, χ, hPφ, hQψ, fun q hq ↦ ?_, localFourier_transportCLM_tensorProduct S T hV hW hχ⟩
  obtain ⟨hq₁, hq₂⟩ := hχK hq
  simpa using hUU ⟨(hφ hq₁).1, (hψ hq₂).1⟩

variable {S T}

/-- If `S` is microlocally smooth at `(x, ξ)` with `ξ ≠ 0`, then `S ⊗ T` is microlocally smooth
at `((x, y), (ξ, η))` for every `y` and `η`. -/
theorem IsMicrolocallySmoothAt.transportCLM_tensorProduct_left {p ζ : WithLp 2 (E × D)}
    (hS : S.IsMicrolocallySmoothAt p.fst ζ.fst) (hξ : ζ.fst ≠ 0) (hp : p ∈ W) :
    (transportCLM (prodContinuousLinearEquiv 2 ℝ E D) hW
      (S.tensorProduct T hV.subset)).IsMicrolocallySmoothAt p ζ := by
  obtain ⟨U, hU, Γ, hΓ, hξΓ, hcone, hdecay⟩ := hS.exists_nhds_cone
  obtain ⟨φ, ψ, χ, hφ, -, hχ, hprod⟩ := exists_prod_cutoff S T hV hW hp hU univ_mem
  obtain ⟨Γ', hΓ', hζΓ', hcone', hdecay'⟩ := TauCeti.exists_cone_decay_mul (fstL 2 ℝ E D)
    (sndL 2 ℝ E D) prod_norm_le_norm_fst_add_norm_snd hΓ hcone hξΓ hξ (hdecay φ hφ)
    (exists_norm_localFourier_le T ψ)
  exact isMicrolocallySmoothAt_iff.2 ⟨χ, hχ, Γ', hΓ', hζΓ', hcone',
    fun N ↦ (hdecay' N).imp fun C hC ζ' hζ' ↦ by simpa [hprod] using hC ζ' hζ'⟩

/-- If `T` is microlocally smooth at `(y, η)` with `η ≠ 0`, then `S ⊗ T` is microlocally smooth
at `((x, y), (ξ, η))` for every `x` and `ξ`. -/
theorem IsMicrolocallySmoothAt.transportCLM_tensorProduct_right {p ζ : WithLp 2 (E × D)}
    (hT : T.IsMicrolocallySmoothAt p.snd ζ.snd) (hη : ζ.snd ≠ 0) (hp : p ∈ W) :
    (transportCLM (prodContinuousLinearEquiv 2 ℝ E D) hW
      (S.tensorProduct T hV.subset)).IsMicrolocallySmoothAt p ζ := by
  obtain ⟨U, hU, Γ, hΓ, hηΓ, hcone, hdecay⟩ := hT.exists_nhds_cone
  obtain ⟨φ, ψ, χ, -, hψ, hχ, hprod⟩ := exists_prod_cutoff S T hV hW hp univ_mem hU
  obtain ⟨Γ', hΓ', hζΓ', hcone', hdecay'⟩ := TauCeti.exists_cone_decay_mul (sndL 2 ℝ E D)
    (fstL 2 ℝ E D) (fun ζ ↦ (prod_norm_le_norm_fst_add_norm_snd ζ).trans_eq (add_comm _ _))
    hΓ hcone hηΓ hη (hdecay ψ hψ) (exists_norm_localFourier_le S φ)
  exact isMicrolocallySmoothAt_iff.2 ⟨χ, hχ, Γ', hΓ', hζΓ', hcone',
    fun N ↦ (hdecay' N).imp fun C hC ζ' hζ' ↦ by simpa [hprod, mul_comm] using hC ζ' hζ'⟩

variable (S T)

/-- **The wave front set of a tensor product** (Hörmander I, Theorem 8.2.9). A covector
`((x, y), (ξ, η))` in the wave front set of `S ⊗ T` has `(x, ξ)` in `WF(S)` or `ξ = 0` with
`x ∈ supp S`, and `(y, η)` in `WF(T)` or `η = 0` with `y ∈ supp T`. Since wave front covectors
are nonzero, this is the bound
`WF(S ⊗ T) ⊆ (WF(S) × WF(T)) ∪ ((supp S × {0}) × WF(T)) ∪ (WF(S) × (supp T × {0}))`. -/
theorem waveFrontSet_transportCLM_tensorProduct_subset :
    (transportCLM (prodContinuousLinearEquiv 2 ℝ E D) hW
        (S.tensorProduct T hV.subset)).waveFrontSet ⊆
      {q | (q.1.fst, q.2.fst) ∈ S.waveFrontSet ∪ dsupport S ×ˢ {0} ∧
        (q.1.snd, q.2.snd) ∈ T.waveFrontSet ∪ dsupport T ×ˢ {0}} := by
  rintro ⟨p, ζ⟩ hq
  obtain ⟨hp, -, hR⟩ := mem_waveFrontSet_iff.1 hq
  have hpV : p.fst ∈ Ω ∧ p.snd ∈ O := by simpa [hV] using hW hp
  -- The base point lies over the supports of `S` and of `T`.
  have hST : p.fst ∈ dsupport S ∧ p.snd ∈ dsupport T := by
    simpa using dsupport_tensorProduct_subset S T hV.subset
      (dsupport_transportCLM_subset _ hW _ (waveFrontSet_subset_dsupport _ hq).1)
  refine ⟨?_, ?_⟩
  · by_cases hξ : ζ.fst = 0
    · exact Or.inr ⟨hST.1, hξ⟩
    · exact Or.inl (mem_waveFrontSet_iff.2
        ⟨hpV.1, hξ, fun hS ↦ hR (hS.transportCLM_tensorProduct_left hV hW hξ hp)⟩)
  · by_cases hη : ζ.snd = 0
    · exact Or.inr ⟨hST.2, hη⟩
    · exact Or.inl (mem_waveFrontSet_iff.2
        ⟨hpV.2, hη, fun hT ↦ hR (hT.transportCLM_tensorProduct_right hV hW hη hp)⟩)


/-! ### Zero covectors in one factor -/

variable {S T}

/-- **The directions pulled back from the first factor.** If `S ⊗ T` is microlocally smooth at
`((x, y), (ξ, 0))` and `y` lies in the support of `T`, then `S` is microlocally smooth at
`(x, ξ)`. -/
theorem IsMicrolocallySmoothAt.of_transportCLM_tensorProduct_left {p ζ : WithLp 2 (E × D)}
    (h : (transportCLM (prodContinuousLinearEquiv 2 ℝ E D) hW
      (S.tensorProduct T hV.subset)).IsMicrolocallySmoothAt p ζ)
    (hη : ζ.snd = 0) (hy : p.snd ∈ dsupport T) : S.IsMicrolocallySmoothAt p.fst ζ.fst := by
  obtain ⟨U, hU, Γ, hΓ, hζΓ, hcone, hdecay⟩ := h.exists_nhds_cone
  have hp : p ∈ W := by
    obtain ⟨χ, hχ, -⟩ := isMicrolocallySmoothAt_iff.1 h
    exact χ.tsupport_subset (subset_tsupport _ hχ)
  have hpΩ : p.fst ∈ Ω := (by simpa [hV] using hW hp : p.fst ∈ Ω ∧ p.snd ∈ O).1
  -- A product cutoff `φ ⊗ ψ` supported in `U`, with `φ (x) ≠ 0` and `T ψ ≠ 0`.
  obtain ⟨φ, ψ, χ, hφp, hTψ, hχU, hprod⟩ := exists_prod_cutoff_subset S T hV hW hp hU
    (P := fun φ ↦ φ p.fst ≠ 0) (Q := fun ψ ↦ T.localFourier ψ 0 ≠ 0)
    (fun U₁ hU₁ ↦ (exists_tsupport_subset_apply_eq (n := ⊤)
      (inter_mem hU₁ (Ω.isOpen.mem_nhds hpΩ)) inter_subset_right (1 : ℂ)).imp
        fun _ hφ ↦ ⟨hφ.1.trans inter_subset_left, by simp [hφ.2]⟩)
    fun _ hU₂ ↦ exists_tsupport_subset_localFourier_at_zero_ne_zero hy hU₂
  -- Along the frequencies `(ξ', 0)` the localized Fourier transform of `S ⊗ T` with cutoff `χ` is
  -- that of `S` with cutoff `φ`, times the nonzero constant `T ψ`.
  have hζ : toLp 2 (ζ.fst, (0 : D)) = ζ := (WithLp.ext_iff 2).2 (Prod.ext (by simp) (by simp [hη]))
  refine isMicrolocallySmoothAt_iff.2 ⟨φ, hφp, (fun ξ' ↦ toLp 2 (ξ', (0 : D))) ⁻¹' Γ,
    hΓ.preimage (by fun_prop), by rwa [mem_preimage, hζ], fun t ht ξ' hξ' ↦ ?_, fun N ↦ ?_⟩
  · have h := hcone t ht _ hξ'
    rwa [← toLp_smul, Prod.smul_mk, smul_zero] at h
  · obtain ⟨C, hC⟩ := hdecay χ hχU N
    refine ⟨C / ‖T.localFourier ψ 0‖, fun ξ' hξ' ↦ ?_⟩
    have hξ'C := hC _ hξ'
    simp only [hprod, toLp_fst, toLp_snd, norm_mul, norm_toLp_fst] at hξ'C
    rw [le_div_iff₀ (norm_pos_iff.2 hTψ), mul_assoc]
    exact hξ'C

/-- **The directions pulled back from the second factor.** If `S ⊗ T` is microlocally smooth at
`((x, y), (0, η))` and `x` lies in the support of `S`, then `T` is microlocally smooth at
`(y, η)`. -/
theorem IsMicrolocallySmoothAt.of_transportCLM_tensorProduct_right {p ζ : WithLp 2 (E × D)}
    (h : (transportCLM (prodContinuousLinearEquiv 2 ℝ E D) hW
      (S.tensorProduct T hV.subset)).IsMicrolocallySmoothAt p ζ)
    (hξ : ζ.fst = 0) (hx : p.fst ∈ dsupport S) : T.IsMicrolocallySmoothAt p.snd ζ.snd := by
  obtain ⟨U, hU, Γ, hΓ, hζΓ, hcone, hdecay⟩ := h.exists_nhds_cone
  have hp : p ∈ W := by
    obtain ⟨χ, hχ, -⟩ := isMicrolocallySmoothAt_iff.1 h
    exact χ.tsupport_subset (subset_tsupport _ hχ)
  have hpO : p.snd ∈ O := (by simpa [hV] using hW hp : p.fst ∈ Ω ∧ p.snd ∈ O).2
  -- A product cutoff `φ ⊗ ψ` supported in `U`, with `S φ ≠ 0` and `ψ (y) ≠ 0`.
  obtain ⟨φ, ψ, χ, hSφ, hψp, hχU, hprod⟩ := exists_prod_cutoff_subset S T hV hW hp hU
    (P := fun φ ↦ S.localFourier φ 0 ≠ 0) (Q := fun ψ ↦ ψ p.snd ≠ 0)
    (fun _ hU₁ ↦ exists_tsupport_subset_localFourier_at_zero_ne_zero hx hU₁)
    fun U₂ hU₂ ↦ (exists_tsupport_subset_apply_eq (n := ⊤)
      (inter_mem hU₂ (O.isOpen.mem_nhds hpO)) inter_subset_right (1 : ℂ)).imp
        fun _ hψ ↦ ⟨hψ.1.trans inter_subset_left, by simp [hψ.2]⟩
  -- Along the frequencies `(0, η')` the localized Fourier transform of `S ⊗ T` with cutoff `χ` is
  -- that of `T` with cutoff `ψ`, times the nonzero constant `S φ`.
  have hζ : toLp 2 ((0 : E), ζ.snd) = ζ := (WithLp.ext_iff 2).2 (Prod.ext (by simp [hξ]) (by simp))
  refine isMicrolocallySmoothAt_iff.2 ⟨ψ, hψp, (fun η' ↦ toLp 2 ((0 : E), η')) ⁻¹' Γ,
    hΓ.preimage (by fun_prop), by rwa [mem_preimage, hζ], fun t ht η' hη' ↦ ?_, fun N ↦ ?_⟩
  · have h := hcone t ht _ hη'
    rwa [← toLp_smul, Prod.smul_mk, smul_zero] at h
  · obtain ⟨C, hC⟩ := hdecay χ hχU N
    refine ⟨C / ‖S.localFourier φ 0‖, fun η' hη' ↦ ?_⟩
    have hη'C := hC _ hη'
    simp only [hprod, toLp_fst, toLp_snd, norm_mul, norm_toLp_snd] at hη'C
    rw [le_div_iff₀ (norm_pos_iff.2 hSφ), mul_assoc, mul_comm ‖_‖]
    exact hη'C

variable (S T)

/-- **The wave front set of a tensor product over zero covectors of the second factor.** A
covector `((x, y), (ξ, 0))` lies in `WF(S ⊗ T)` exactly when `(x, y) ∈ W`, `(x, ξ) ∈ WF(S)` and
`y ∈ supp T`. -/
theorem mem_waveFrontSet_transportCLM_tensorProduct_iff_of_snd_eq_zero
    {p ζ : WithLp 2 (E × D)} (hη : ζ.snd = 0) :
    (p, ζ) ∈ (transportCLM (prodContinuousLinearEquiv 2 ℝ E D) hW
        (S.tensorProduct T hV.subset)).waveFrontSet ↔
      p ∈ W ∧ (p.fst, ζ.fst) ∈ S.waveFrontSet ∧ p.snd ∈ dsupport T := by
  refine ⟨fun hq ↦ ?_, fun ⟨hp, hS, hy⟩ ↦ ?_⟩
  · obtain ⟨hS, hT⟩ := waveFrontSet_transportCLM_tensorProduct_subset S T hV hW hq
    obtain ⟨hp, hζ, -⟩ := mem_waveFrontSet_iff.1 hq
    refine ⟨hp, hS.resolve_right fun hξ ↦ hζ ?_,
      hT.elim (fun h ↦ ((mem_waveFrontSet_iff.1 h).2.1 hη).elim) (·.1)⟩
    exact (WithLp.ext_iff 2).2 (Prod.ext (by simpa using hξ.2) (by simpa using hη))
  · obtain ⟨-, hξ, hS⟩ := mem_waveFrontSet_iff.1 hS
    exact mem_waveFrontSet_iff.2 ⟨hp, fun hζ ↦ hξ (by simp [hζ]),
      fun h ↦ hS (h.of_transportCLM_tensorProduct_left hV hW hη hy)⟩

/-- **The wave front set of a tensor product over zero covectors of the first factor.** A
covector `((x, y), (0, η))` lies in `WF(S ⊗ T)` exactly when `(x, y) ∈ W`, `x ∈ supp S` and
`(y, η) ∈ WF(T)`. -/
theorem mem_waveFrontSet_transportCLM_tensorProduct_iff_of_fst_eq_zero
    {p ζ : WithLp 2 (E × D)} (hξ : ζ.fst = 0) :
    (p, ζ) ∈ (transportCLM (prodContinuousLinearEquiv 2 ℝ E D) hW
        (S.tensorProduct T hV.subset)).waveFrontSet ↔
      p ∈ W ∧ p.fst ∈ dsupport S ∧ (p.snd, ζ.snd) ∈ T.waveFrontSet := by
  refine ⟨fun hq ↦ ?_, fun ⟨hp, hx, hT⟩ ↦ ?_⟩
  · obtain ⟨hS, hT⟩ := waveFrontSet_transportCLM_tensorProduct_subset S T hV hW hq
    obtain ⟨hp, hζ, -⟩ := mem_waveFrontSet_iff.1 hq
    refine ⟨hp, hS.elim (fun h ↦ ((mem_waveFrontSet_iff.1 h).2.1 hξ).elim) (·.1),
      hT.resolve_right fun hη ↦ hζ ?_⟩
    exact (WithLp.ext_iff 2).2 (Prod.ext (by simpa using hξ) (by simpa using hη.2))
  · obtain ⟨-, hη, hT⟩ := mem_waveFrontSet_iff.1 hT
    exact mem_waveFrontSet_iff.2 ⟨hp, fun hζ ↦ hη (by simp [hζ]),
      fun h ↦ hT (h.of_transportCLM_tensorProduct_right hV hW hξ hx)⟩

/-- **Tensoring with a distribution without wave front set.** If `WF(T) = ∅`, for instance if `T`
is a smooth function, then `WF(S ⊗ T)` consists of the covectors `((x, y), (ξ, 0))` over `W` with
`(x, ξ) ∈ WF(S)` and `y ∈ supp T`. -/
theorem waveFrontSet_transportCLM_tensorProduct_of_waveFrontSet_right_eq_empty
    (hT : T.waveFrontSet = ∅) :
    (transportCLM (prodContinuousLinearEquiv 2 ℝ E D) hW
        (S.tensorProduct T hV.subset)).waveFrontSet =
      {q | q.1 ∈ W ∧ (q.1.fst, q.2.fst) ∈ S.waveFrontSet ∧ q.1.snd ∈ dsupport T ∧
        q.2.snd = 0} := by
  ext ⟨p, ζ⟩
  by_cases hη : ζ.snd = 0
  · simp [mem_waveFrontSet_transportCLM_tensorProduct_iff_of_snd_eq_zero S T hV hW hη, hη]
  · refine iff_of_false (fun hq ↦ hη ?_) fun hq ↦ hη hq.2.2.2
    have h := (waveFrontSet_transportCLM_tensorProduct_subset S T hV hW hq).2
    simp only [hT, empty_union, mem_prod, mem_singleton_iff] at h
    exact h.2

/-- **Tensoring with a distribution without wave front set.** If `WF(S) = ∅`, for instance if `S`
is a smooth function, then `WF(S ⊗ T)` consists of the covectors `((x, y), (0, η))` over `W` with
`x ∈ supp S` and `(y, η) ∈ WF(T)`. -/
theorem waveFrontSet_transportCLM_tensorProduct_of_waveFrontSet_left_eq_empty
    (hS : S.waveFrontSet = ∅) :
    (transportCLM (prodContinuousLinearEquiv 2 ℝ E D) hW
        (S.tensorProduct T hV.subset)).waveFrontSet =
      {q | q.1 ∈ W ∧ q.1.fst ∈ dsupport S ∧ (q.1.snd, q.2.snd) ∈ T.waveFrontSet ∧
        q.2.fst = 0} := by
  ext ⟨p, ζ⟩
  by_cases hξ : ζ.fst = 0
  · simp [mem_waveFrontSet_transportCLM_tensorProduct_iff_of_fst_eq_zero S T hV hW hξ, hξ]
  · refine iff_of_false (fun hq ↦ hξ ?_) fun hq ↦ hξ hq.2.2.2
    have h := (waveFrontSet_transportCLM_tensorProduct_subset S T hV hW hq).1
    simp only [hS, empty_union, mem_prod, mem_singleton_iff] at h
    exact h.2

variable [MeasurableSpace D] [BorelSpace D]

/-- **Pullback along the first projection.** Tensoring `S` with a nonzero constant function `c`
on `O`, which for `c = 1` pulls `S` back along the projection `(x, y) ↦ x`, gives a distribution
whose wave front set consists of the covectors `((x, y), (ξ, 0))` over `W` with `(x, ξ) ∈ WF(S)`.
The covectors are those of `S`, pulled back by the projection. -/
theorem waveFrontSet_transportCLM_tensorProduct_ofFun_const {c : ℂ} (hc : c ≠ 0) :
    (transportCLM (prodContinuousLinearEquiv 2 ℝ E D) hW
        (S.tensorProduct (ofFun O (fun _ ↦ c) MeasureTheory.volume ⊤) hV.subset)).waveFrontSet =
      {q | q.1 ∈ W ∧ (q.1.fst, q.2.fst) ∈ S.waveFrontSet ∧ q.2.snd = 0} := by
  rw [waveFrontSet_transportCLM_tensorProduct_of_waveFrontSet_right_eq_empty S _ hV hW
    (waveFrontSet_ofFun_eq_empty contDiffOn_const)]
  ext ⟨p, ζ⟩
  refine ⟨fun h ↦ ⟨h.1, h.2.1, h.2.2.2⟩, fun h ↦ ⟨h.1, h.2.1, ?_, h.2.2⟩⟩
  exact subset_dsupport_ofFun_const hc (by simpa [hV] using hW h.1 : p.fst ∈ Ω ∧ p.snd ∈ O).2

/-- **Example: a point mass times `1`.** The wave front set of `δ_{x₀} ⊗ 1` consists of the
covectors `((x₀, y), (ξ, 0))` over `W` with `ξ ≠ 0`. The covectors have zero component along the
smooth factor, but they do not vanish. -/
theorem waveFrontSet_transportCLM_tensorProduct_delta_ofFun_one {x₀ : E} (hx₀ : x₀ ∈ Ω) :
    (transportCLM (prodContinuousLinearEquiv 2 ℝ E D) hW
        ((mapCLM ofRealCLM (delta x₀ : 𝓓'(Ω, ℝ))).tensorProduct
          (ofFun O (fun _ ↦ (1 : ℂ)) MeasureTheory.volume ⊤) hV.subset)).waveFrontSet =
      {q | q.1 ∈ W ∧ q.1.fst = x₀ ∧ q.2.fst ≠ 0 ∧ q.2.snd = 0} := by
  rw [waveFrontSet_transportCLM_tensorProduct_ofFun_const _ hV hW one_ne_zero,
    waveFrontSet_delta hx₀]
  ext
  simp [and_assoc]

end Distribution
