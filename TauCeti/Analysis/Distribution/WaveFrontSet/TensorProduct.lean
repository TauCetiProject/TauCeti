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
import TauCeti.Analysis.Distribution.LocalConstancy
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

These two zero-covector terms are attained: if `(x, ξ) ∈ WF(S)` and `y ∈ supp T`, then
`((x, y), (ξ, 0)) ∈ WF(S ⊗ T)`, and symmetrically. Hence the bound is an equality when one factor
has empty wave front set; for instance `WF(S ⊗ T) = WF(S) × (supp T × {0})` when `T` is a smooth
function. Taking `T = 1` computes the wave front set of the pullback `S ⊗ 1` of `S` along the
projection `(x, y) ↦ x`. For the point mass `δ_{x₀}` it is the conormal set of `{x₀} × D`,
although `1` itself has empty wave front set.

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
* `Distribution.mem_waveFrontSet_transportCLM_tensorProduct_of_mem_left`,
  `Distribution.mem_waveFrontSet_transportCLM_tensorProduct_of_mem_right`: the zero-covector terms
  of the bound lie in `WF(S ⊗ T)`.
* `Distribution.waveFrontSet_transportCLM_tensorProduct_of_waveFrontSet_eq_empty_right`,
  `Distribution.waveFrontSet_transportCLM_tensorProduct_of_waveFrontSet_eq_empty_left`: the wave
  front set of `S ⊗ T` when one factor has empty wave front set.
* `Distribution.waveFrontSet_transportCLM_tensorProduct_delta_one`: the wave front set of
  `δ_{x₀} ⊗ 1`.

## Implementation notes

The localized Fourier transform of `S ⊗ T` with a product cutoff `(x, y) ↦ φ x ψ y` is the product
`(φ S)^(ξ) (ψ T)^(η)` of those of `S` and `T`. If `(φ S)^` decays rapidly on an open cone around
`ξ ≠ 0`, then so does the product on the open cone of those `(ξ', η')` with `ξ'` in that cone and
`‖η'‖ < c ‖ξ'‖`, because `(ψ T)^` grows at most polynomially and `‖(ξ', η')‖` is comparable to
`‖ξ'‖` there.

Conversely, suppose `S ⊗ T` decays rapidly near `(x, y)` on an open cone around `(ξ, 0)`. Since
`y ∈ supp T`, some test function `ψ` near `y` has `T ψ ≠ 0`, which is the localized Fourier
transform of `T` with cutoff `ψ` at zero frequency. Restricting the product formula to the
frequencies `(ξ', 0)` and dividing by `T ψ` gives rapid decay of `(φ S)^` on an open cone around
`ξ`.

## References

* L. Hörmander, *The Analysis of Linear Partial Differential Operators I*, §8.2, Theorem 8.2.9.
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

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ D] in
/-- Every neighbourhood `U` of a point `p` of `W` contains a box: there are neighbourhoods `B₁` of
`p.fst` and `B₂` of `p.snd` such that the product of any cutoffs supported in `B₁` and in `B₂` is
a cutoff on `W` supported in `U`. -/
private theorem exists_prod_cutoff_of_tsupport_subset {p : WithLp 2 (E × D)} (hp : p ∈ W)
    {U : Set (WithLp 2 (E × D))} (hU : U ∈ 𝓝 p) :
    ∃ B₁ ∈ 𝓝 p.fst, ∃ B₂ ∈ 𝓝 p.snd, ∀ (φ : 𝓓(Ω, ℂ)) (ψ : 𝓓(O, ℂ)), tsupport φ ⊆ B₁ →
      tsupport ψ ⊆ B₂ → ∃ χ : 𝓓(W, ℂ), tsupport χ ⊆ U ∧ ∀ q, χ q = φ q.fst * ψ q.snd := by
  -- A box `B₁ × B₂` around `p` whose Euclidean copy lies in `U ∩ W`.
  have hUW : toLp 2 ⁻¹' (U ∩ W) ∈ 𝓝 (ofLp p) :=
    (prod_continuous_toLp 2 E D).continuousAt.preimage_mem_nhds
      (by simpa using inter_mem hU (W.isOpen.mem_nhds hp))
  obtain ⟨B₁, hB₁, B₂, hB₂, hB⟩ := mem_nhds_prod_iff.1 hUW
  refine ⟨B₁, hB₁, B₂, hB₂, fun φ ψ hφ hψ ↦ ?_⟩
  -- The product cutoff is supported in the compact set `ofLp ⁻¹' (tsupport φ ×ˢ tsupport ψ)`.
  set K : Set (WithLp 2 (E × D)) := ofLp ⁻¹' (tsupport φ ×ˢ tsupport ψ) with hK_def
  have hK : IsCompact K :=
    (prodContinuousLinearEquiv 2 ℝ E D).toHomeomorph.isCompact_preimage.2
      (φ.hasCompactSupport.isCompact.prod ψ.hasCompactSupport.isCompact)
  have hsupp : tsupport (fun q : WithLp 2 (E × D) ↦ φ q.fst * ψ q.snd) ⊆ K := fun q hq ↦
    ⟨tsupport_comp_subset_preimage φ (continuous_fst.comp (prod_continuous_ofLp 2 E D))
        (tsupport_mul_subset_left hq),
      tsupport_comp_subset_preimage ψ (continuous_snd.comp (prod_continuous_ofLp 2 E D))
        (tsupport_mul_subset_right hq)⟩
  have hKUW : K ⊆ U ∩ W := fun q ⟨hq₁, hq₂⟩ ↦ by simpa using hB ⟨hφ hq₁, hψ hq₂⟩
  exact ⟨⟨fun q ↦ φ q.fst * ψ q.snd,
    (φ.contDiff.comp (fstL 2 ℝ E D).contDiff).mul (ψ.contDiff.comp (sndL 2 ℝ E D).contDiff),
    hK.of_isClosed_subset (isClosed_tsupport _) hsupp,
    hsupp.trans (hKUW.trans inter_subset_right)⟩,
    hsupp.trans (hKUW.trans inter_subset_left), fun _ ↦ rfl⟩

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
  obtain ⟨B₁, hB₁, B₂, hB₂, hprod⟩ :=
    exists_prod_cutoff_of_tsupport_subset (Ω := Ω) (O := O) hp (W.isOpen.mem_nhds hp)
  obtain ⟨φ, hφ, hφp⟩ := exists_tsupport_subset_apply_eq (n := ⊤)
    (inter_mem (inter_mem hU₁ hB₁) (Ω.isOpen.mem_nhds hpV.1)) inter_subset_right (1 : ℂ)
  obtain ⟨ψ, hψ, hψp⟩ := exists_tsupport_subset_apply_eq (n := ⊤)
    (inter_mem (inter_mem hU₂ hB₂) (O.isOpen.mem_nhds hpV.2)) inter_subset_right (1 : ℂ)
  obtain ⟨χ, -, hχ⟩ := hprod φ ψ (fun _ hx ↦ (hφ hx).1.2) fun _ hy ↦ (hψ hy).1.2
  exact ⟨φ, ψ, χ, fun _ hx ↦ (hφ hx).1.1, fun _ hy ↦ (hψ hy).1.1,
    by simp [hχ, hφp, hψp], localFourier_transportCLM_tensorProduct S T hV hW hχ⟩

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

variable {S T}

/-- **Sharpness of the zero covector in the second factor.** If `S ⊗ T` is microlocally smooth at
`((x, y), (ξ, 0))` and `y` lies in the support of `T`, then `S` is microlocally smooth at
`(x, ξ)`. -/
theorem IsMicrolocallySmoothAt.of_transportCLM_tensorProduct_left {p ζ : WithLp 2 (E × D)}
    (h : (transportCLM (prodContinuousLinearEquiv 2 ℝ E D) hW
      (S.tensorProduct T hV.subset)).IsMicrolocallySmoothAt p ζ)
    (hζ : ζ.snd = 0) (hp : p ∈ W) (hT : p.snd ∈ dsupport T) :
    S.IsMicrolocallySmoothAt p.fst ζ.fst := by
  have hpV : p.fst ∈ Ω ∧ p.snd ∈ O := by simpa [hV] using hW hp
  obtain ⟨U, hU, Γ, hΓ, hζΓ, hcone, hdecay⟩ := h.exists_nhds_cone
  obtain ⟨B₁, hB₁, B₂, hB₂, hprod⟩ :=
    exists_prod_cutoff_of_tsupport_subset (Ω := Ω) (O := O) hp hU
  obtain ⟨φ, hφ, hφp⟩ := exists_tsupport_subset_apply_eq (n := ⊤)
    (inter_mem hB₁ (Ω.isOpen.mem_nhds hpV.1)) inter_subset_right (1 : ℂ)
  -- Since `p.snd` lies in the support of `T`, some test function `u` near `p.snd` has `T u ≠ 0`;
  -- its localized Fourier transform at zero frequency is `T u`.
  obtain ⟨u, hu, hTu⟩ := (mem_dsupport_iff_forall_exists_ne _).1 hT _
    (mem_interior_iff_mem_nhds.2 hB₂) isOpen_interior
  set ψ : 𝓓(O, ℂ) := postcompCLM (𝕜 := ℝ) ofRealCLM u
  have hψ : tsupport ψ ⊆ B₂ := fun y hy ↦ interior_subset (hu (tsupport_comp_subset
    (g := ofRealCLM) (map_zero _) u (by simpa [ψ, postcompCLM_apply] using hy)))
  obtain ⟨χ, hχU, hχ⟩ := hprod φ ψ (fun _ hx ↦ (hφ hx).1) hψ
  -- On the frequencies `(η, 0)`, the localized Fourier transform of `S ⊗ T` is that of `S` at `η`
  -- times `T u`.
  refine isMicrolocallySmoothAt_iff.2 ⟨φ, by simp [hφp], TauCeti.exists_cone_decay_of_comp_eq_mul
    ((prodContinuousLinearEquiv 2 ℝ E D).symm.toContinuousLinearMap.comp
      (ContinuousLinearMap.inl ℝ E D)) (fun η ↦ by simp) hΓ hcone ?_ hTu (fun η ↦ ?_)
    (hdecay χ hχU)⟩
  · convert hζΓ using 1
    exact (WithLp.ext_iff 2).2 (Prod.ext (by simp) (by simp [hζ]))
  · simp [localFourier_transportCLM_tensorProduct S T hV hW hχ, ψ, mul_comm]

/-- **Sharpness of the zero covector in the first factor.** If `S ⊗ T` is microlocally smooth at
`((x, y), (0, η))` and `x` lies in the support of `S`, then `T` is microlocally smooth at
`(y, η)`. -/
theorem IsMicrolocallySmoothAt.of_transportCLM_tensorProduct_right {p ζ : WithLp 2 (E × D)}
    (h : (transportCLM (prodContinuousLinearEquiv 2 ℝ E D) hW
      (S.tensorProduct T hV.subset)).IsMicrolocallySmoothAt p ζ)
    (hζ : ζ.fst = 0) (hp : p ∈ W) (hS : p.fst ∈ dsupport S) :
    T.IsMicrolocallySmoothAt p.snd ζ.snd := by
  have hpV : p.fst ∈ Ω ∧ p.snd ∈ O := by simpa [hV] using hW hp
  obtain ⟨U, hU, Γ, hΓ, hζΓ, hcone, hdecay⟩ := h.exists_nhds_cone
  obtain ⟨B₁, hB₁, B₂, hB₂, hprod⟩ :=
    exists_prod_cutoff_of_tsupport_subset (Ω := Ω) (O := O) hp hU
  obtain ⟨ψ, hψ, hψp⟩ := exists_tsupport_subset_apply_eq (n := ⊤)
    (inter_mem hB₂ (O.isOpen.mem_nhds hpV.2)) inter_subset_right (1 : ℂ)
  -- Since `p.fst` lies in the support of `S`, some test function `u` near `p.fst` has `S u ≠ 0`;
  -- its localized Fourier transform at zero frequency is `S u`.
  obtain ⟨u, hu, hSu⟩ := (mem_dsupport_iff_forall_exists_ne _).1 hS _
    (mem_interior_iff_mem_nhds.2 hB₁) isOpen_interior
  set φ : 𝓓(Ω, ℂ) := postcompCLM (𝕜 := ℝ) ofRealCLM u
  have hφ : tsupport φ ⊆ B₁ := fun x hx ↦ interior_subset (hu (tsupport_comp_subset
    (g := ofRealCLM) (map_zero _) u (by simpa [φ, postcompCLM_apply] using hx)))
  obtain ⟨χ, hχU, hχ⟩ := hprod φ ψ hφ fun _ hy ↦ (hψ hy).1
  -- On the frequencies `(0, η)`, the localized Fourier transform of `S ⊗ T` is `S u` times that
  -- of `T` at `η`.
  refine isMicrolocallySmoothAt_iff.2 ⟨ψ, by simp [hψp], TauCeti.exists_cone_decay_of_comp_eq_mul
    ((prodContinuousLinearEquiv 2 ℝ E D).symm.toContinuousLinearMap.comp
      (ContinuousLinearMap.inr ℝ E D)) (fun η ↦ by simp) hΓ hcone ?_ hSu (fun η ↦ ?_)
    (hdecay χ hχU)⟩
  · convert hζΓ using 1
    exact (WithLp.ext_iff 2).2 (Prod.ext (by simp [hζ]) (by simp))
  · simp [localFourier_transportCLM_tensorProduct S T hV hW hχ, φ]

/-- **The zero covector in the second factor is attained.** If `(x, ξ) ∈ WF(S)` and `y` lies in the
support of `T`, with `(x, y) ∈ W`, then `((x, y), (ξ, 0)) ∈ WF(S ⊗ T)`. -/
theorem mem_waveFrontSet_transportCLM_tensorProduct_of_mem_left {p ζ : WithLp 2 (E × D)}
    (hp : p ∈ W) (hS : (p.fst, ζ.fst) ∈ S.waveFrontSet) (hT : p.snd ∈ dsupport T)
    (hζ : ζ.snd = 0) :
    (p, ζ) ∈ (transportCLM (prodContinuousLinearEquiv 2 ℝ E D) hW
      (S.tensorProduct T hV.subset)).waveFrontSet := by
  obtain ⟨-, hξ, hS⟩ := mem_waveFrontSet_iff.1 hS
  exact mem_waveFrontSet_iff.2 ⟨hp, fun h ↦ hξ (by simp [h]),
    fun h ↦ hS (h.of_transportCLM_tensorProduct_left hV hW hζ hp hT)⟩

/-- **The zero covector in the first factor is attained.** If `(y, η) ∈ WF(T)` and `x` lies in the
support of `S`, with `(x, y) ∈ W`, then `((x, y), (0, η)) ∈ WF(S ⊗ T)`. -/
theorem mem_waveFrontSet_transportCLM_tensorProduct_of_mem_right {p ζ : WithLp 2 (E × D)}
    (hp : p ∈ W) (hT : (p.snd, ζ.snd) ∈ T.waveFrontSet) (hS : p.fst ∈ dsupport S)
    (hζ : ζ.fst = 0) :
    (p, ζ) ∈ (transportCLM (prodContinuousLinearEquiv 2 ℝ E D) hW
      (S.tensorProduct T hV.subset)).waveFrontSet := by
  obtain ⟨-, hη, hT⟩ := mem_waveFrontSet_iff.1 hT
  exact mem_waveFrontSet_iff.2 ⟨hp, fun h ↦ hη (by simp [h]),
    fun h ↦ hT (h.of_transportCLM_tensorProduct_right hV hW hζ hp hS)⟩

/-- **The wave front set of a tensor product with a smooth second factor.** If `T` has empty wave
front set, for example if `T` is a smooth function, then `WF(S ⊗ T) = WF(S) × (supp T × {0})`
over `W`. In particular `WF(S ⊗ 1)`, the wave front set of the pullback of `S` along the
projection `(x, y) ↦ x`, consists of the covectors `((x, y), (ξ, 0))` with `(x, ξ) ∈ WF(S)`. -/
theorem waveFrontSet_transportCLM_tensorProduct_of_waveFrontSet_eq_empty_right
    (hT : T.waveFrontSet = ∅) :
    (transportCLM (prodContinuousLinearEquiv 2 ℝ E D) hW
        (S.tensorProduct T hV.subset)).waveFrontSet =
      {q | q.1 ∈ W ∧ (q.1.fst, q.2.fst) ∈ S.waveFrontSet ∧ q.1.snd ∈ dsupport T ∧
        q.2.snd = 0} := by
  ext ⟨p, ζ⟩
  refine ⟨fun hq ↦ ?_, fun ⟨hp, hS, hT', hζ⟩ ↦
    mem_waveFrontSet_transportCLM_tensorProduct_of_mem_left hV hW hp hS hT' hζ⟩
  obtain ⟨hp, hζ, -⟩ := mem_waveFrontSet_iff.1 hq
  obtain ⟨hS, hT'⟩ := waveFrontSet_transportCLM_tensorProduct_subset S T hV hW hq
  simp only [hT, empty_union, mem_prod, mem_singleton_iff] at hT'
  refine ⟨hp, hS.resolve_right fun hξ ↦ hζ ?_, hT'⟩
  exact (WithLp.ext_iff 2).2 (Prod.ext (by simpa using hξ.2) (by simp [hT'.2]))

/-- **The wave front set of a tensor product with a smooth first factor.** If `S` has empty wave
front set, for example if `S` is a smooth function, then `WF(S ⊗ T) = (supp S × {0}) × WF(T)`
over `W`. -/
theorem waveFrontSet_transportCLM_tensorProduct_of_waveFrontSet_eq_empty_left
    (hS : S.waveFrontSet = ∅) :
    (transportCLM (prodContinuousLinearEquiv 2 ℝ E D) hW
        (S.tensorProduct T hV.subset)).waveFrontSet =
      {q | q.1 ∈ W ∧ (q.1.snd, q.2.snd) ∈ T.waveFrontSet ∧ q.1.fst ∈ dsupport S ∧
        q.2.fst = 0} := by
  ext ⟨p, ζ⟩
  refine ⟨fun hq ↦ ?_, fun ⟨hp, hT, hS', hζ⟩ ↦
    mem_waveFrontSet_transportCLM_tensorProduct_of_mem_right hV hW hp hT hS' hζ⟩
  obtain ⟨hp, hζ, -⟩ := mem_waveFrontSet_iff.1 hq
  obtain ⟨hS', hT⟩ := waveFrontSet_transportCLM_tensorProduct_subset S T hV hW hq
  simp only [hS, empty_union, mem_prod, mem_singleton_iff] at hS'
  refine ⟨hp, hT.resolve_right fun hη ↦ hζ ?_, hS'⟩
  exact (WithLp.ext_iff 2).2 (Prod.ext (by simp [hS'.2]) (by simpa using hη.2))

/-- **The wave front set of `δ_{x₀} ⊗ 1`.** The tensor product of the point mass at `x₀ ∈ Ω` with
the constant function `1`, which is the pullback of `δ_{x₀}` along the projection `(x, y) ↦ x`,
has as wave front set over `W` the conormal set of `{x₀} × D`: the covectors `((x₀, y), (ξ, 0))`
with `ξ ≠ 0`. Although `1` has empty wave front set, these covectors come from its zero
covectors. -/
theorem waveFrontSet_transportCLM_tensorProduct_delta_one [MeasurableSpace D] [BorelSpace D]
    {x₀ : E} (hx₀ : x₀ ∈ Ω) :
    (transportCLM (prodContinuousLinearEquiv 2 ℝ E D) hW
        ((mapCLM ofRealCLM (delta x₀ : 𝓓'(Ω, ℝ))).tensorProduct
          (ofFun O (fun _ ↦ (1 : ℂ)) MeasureTheory.volume ⊤) hV.subset)).waveFrontSet =
      {q | q.1 ∈ W ∧ q.1.fst = x₀ ∧ q.2.fst ≠ 0 ∧ q.2.snd = 0} := by
  rw [waveFrontSet_transportCLM_tensorProduct_of_waveFrontSet_eq_empty_right hV hW
    (waveFrontSet_ofFun_eq_empty contDiffOn_const), waveFrontSet_delta hx₀,
    dsupport_ofFun_const one_ne_zero]
  ext ⟨p, ζ⟩
  have hpO (hp : p ∈ W) : p.snd ∈ closure (O : Set D) :=
    subset_closure (by simpa [hV] using hW hp : p.fst ∈ Ω ∧ p.snd ∈ O).2
  simp only [mem_ofPred_eq, mem_prod, mem_singleton_iff, mem_compl_iff]
  exact ⟨fun ⟨hp, hS, _, hζ⟩ ↦ ⟨hp, hS.1, hS.2, hζ⟩,
    fun ⟨hp, hx, hξ, hζ⟩ ↦ ⟨hp, ⟨hx, hξ⟩, hpO hp, hζ⟩⟩

end Distribution
