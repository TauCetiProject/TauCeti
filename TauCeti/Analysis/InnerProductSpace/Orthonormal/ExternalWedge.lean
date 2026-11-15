/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.ProdL2
public import TauCeti.Analysis.InnerProductSpace.Orthonormal.Alternating
public import TauCeti.Analysis.InnerProductSpace.Orthonormal.Prod
public import TauCeti.Analysis.Normed.Module.Alternating.Wedge.Specializations

/-!
# External wedge products of forms and their comass

For a real `k`-form `φ` on `E` and a real `l`-form `ψ` on `F`, the external wedge product
`φ ⊠ ψ = pr₁*φ ∧ pr₂*ψ` (`ContinuousAlternatingMap.externalWedge`) is a `(k + l)`-form on the
orthogonal direct sum `E ⊕ F`, realized as the `L²` product `WithLp 2 (E × F)`. On a product frame,
the frame of the first factor first, it evaluates to `φ e * ψ f`. External products are the
linear model for products of calibrations (Harvey–Lawson, §II.7), whose comass they control.

The comass of `φ ⊠ ψ` (the native operator norm, see
`ContinuousAlternatingMap.norm_eq_sSup_abs_orthonormal`) satisfies
`‖φ‖ ‖ψ‖ ≤ ‖φ ⊠ ψ‖ ≤ binomial(k + l, k) ‖φ‖ ‖ψ‖`. The upper bound is not sharp in general (for
`dx₁ ∧ dx₂` on `ℝ ⊕ ℝ` it is `2`, while the comass is `1`), and orthogonal support alone does not
make the lower bound an equality (Züst). It is an equality when one factor is of top degree, for
instance a unit volume form: then `‖φ ⊠ ψ‖ = ‖φ‖ ‖ψ‖`. To see this, test the bound on an
orthonormal frame `w` of `E ⊕ F`. On the span `W` of `w` the form is of top degree, so its value on
`w` is, up to sign, its value on any orthonormal basis of `W`. The first projection has rank at
most `dim E ≤ k` on `W`, so `W` contains an orthonormal `l`-frame `g` of the second factor; extend
it to an orthonormal basis `(x, g)` of `W`. Every shuffle that feeds a vector of `g` to the volume
form vanishes, so the value is `φ (pr₁ ∘ x) * ψ g`, at most `‖φ‖ ‖ψ‖` in absolute value.

## Main definitions

* `ContinuousAlternatingMap.externalWedge`: the external wedge product `φ ⊠ ψ`.

## Main results

* `ContinuousAlternatingMap.externalWedge_apply_append_toLp`: `(φ ⊠ ψ)(e, f) = φ e * ψ f`.
* `ContinuousAlternatingMap.norm_externalWedge_le`: the binomial upper bound.
* `ContinuousAlternatingMap.norm_mul_norm_le_norm_externalWedge`: the lower bound
  `‖φ‖ ‖ψ‖ ≤ ‖φ ⊠ ψ‖`.
* `ContinuousAlternatingMap.norm_externalWedge_of_finrank_le_left`,
  `ContinuousAlternatingMap.norm_externalWedge_of_finrank_le_right`: equality when one factor is
  of top degree.
* `ContinuousAlternatingMap.externalWedge_comm`: graded commutativity under exchange of the
  factors.

## References

* R. Harvey and H. B. Lawson, *Calibrated geometries*, Acta Math. 148 (1982), §II.7
  (products of calibrations, Proposition II.7.10).
* R. Züst, *A calibration on ℝ¹⁶ and Federer's product question*, arXiv:2503.12402 (2025)
  (orthogonally supported products whose comass exceeds the product of the comasses).
-/

public section

open Module

namespace ContinuousAlternatingMap

section Normed

variable {E F : Type*} [SeminormedAddCommGroup E] [NormedSpace ℝ E]
  [SeminormedAddCommGroup F] [NormedSpace ℝ F] {k l : ℕ}

/-- The **external wedge product** of a `k`-form `φ` on `E` and an `l`-form `ψ` on `F`: the
`(k + l)`-form `pr₁*φ ∧ pr₂*ψ` on the orthogonal direct sum `WithLp 2 (E × F)`, where `pr₁` and
`pr₂` are the two projections. -/
noncomputable def externalWedge (φ : E [⋀^Fin k]→L[ℝ] ℝ) (ψ : F [⋀^Fin l]→L[ℝ] ℝ) :
    WithLp 2 (E × F) [⋀^Fin (k + l)]→L[ℝ] ℝ :=
  wedge (φ.compContinuousLinearMap (WithLp.fstL 2 ℝ E F))
    (ψ.compContinuousLinearMap (WithLp.sndL 2 ℝ E F))

/-- The external wedge product is the wedge of the pullbacks along the two projections. -/
theorem externalWedge_def (φ : E [⋀^Fin k]→L[ℝ] ℝ) (ψ : F [⋀^Fin l]→L[ℝ] ℝ) :
    externalWedge φ ψ = wedge (φ.compContinuousLinearMap (WithLp.fstL 2 ℝ E F))
      (ψ.compContinuousLinearMap (WithLp.sndL 2 ℝ E F)) := (rfl)

/-- **Evaluation on a split frame.** If the vectors of `y` lie in the second factor, the external
wedge product on the concatenation of `x` and `y` is `φ (pr₁ ∘ x) * ψ (pr₂ ∘ y)`. -/
theorem externalWedge_apply_append (φ : E [⋀^Fin k]→L[ℝ] ℝ) (ψ : F [⋀^Fin l]→L[ℝ] ℝ)
    (x : Fin k → WithLp 2 (E × F)) {y : Fin l → WithLp 2 (E × F)} (hy : ∀ j, (y j).fst = 0) :
    externalWedge φ ψ (Fin.append x y) = φ (fun i ↦ (x i).fst) * ψ (fun j ↦ (y j).snd) := by
  rw [externalWedge_def, wedge_def, pairedWedge_apply_append_of_forall]
  · simp only [ContinuousLinearMap.mul_apply', compContinuousLinearMap_apply, Function.comp_def,
      WithLp.fstL_apply, WithLp.sndL_apply]
  · intro w i j hij
    exact φ.map_coord_zero (m := fun i ↦ (w i).fst) i (by simp [hij, hy])

/-- **Evaluation on a product frame**, first factor first: on the frame `(e, f)` of the direct
sum, the external wedge product is `φ e * ψ f`. -/
@[simp]
theorem externalWedge_apply_append_toLp (φ : E [⋀^Fin k]→L[ℝ] ℝ) (ψ : F [⋀^Fin l]→L[ℝ] ℝ)
    (e : Fin k → E) (f : Fin l → F) :
    externalWedge φ ψ (Fin.append (fun i ↦ WithLp.toLp 2 (e i, (0 : F)))
      (fun j ↦ WithLp.toLp 2 ((0 : E), f j))) = φ e * ψ f :=
  externalWedge_apply_append φ ψ _ fun _ ↦ rfl

/-- The external wedge product is additive in its first argument. -/
@[simp]
theorem externalWedge_add_left (φ φ' : E [⋀^Fin k]→L[ℝ] ℝ) (ψ : F [⋀^Fin l]→L[ℝ] ℝ) :
    externalWedge (φ + φ') ψ = externalWedge φ ψ + externalWedge φ' ψ := by
  simp only [externalWedge_def, ← wedge_add_left, ← compContinuousLinearMapCLM_apply,
    map_add (compContinuousLinearMapCLM (WithLp.fstL 2 ℝ E F)) φ φ']

/-- The external wedge product is additive in its second argument. -/
@[simp]
theorem externalWedge_add_right (φ : E [⋀^Fin k]→L[ℝ] ℝ) (ψ ψ' : F [⋀^Fin l]→L[ℝ] ℝ) :
    externalWedge φ (ψ + ψ') = externalWedge φ ψ + externalWedge φ ψ' := by
  simp only [externalWedge_def, ← wedge_add_right, ← compContinuousLinearMapCLM_apply,
    map_add (compContinuousLinearMapCLM (WithLp.sndL 2 ℝ E F)) ψ ψ']

/-- The external wedge product is homogeneous in its first argument. -/
@[simp]
theorem externalWedge_smul_left (c : ℝ) (φ : E [⋀^Fin k]→L[ℝ] ℝ) (ψ : F [⋀^Fin l]→L[ℝ] ℝ) :
    externalWedge (c • φ) ψ = c • externalWedge φ ψ := by
  simp only [externalWedge_def, ← wedge_smul_left, ← compContinuousLinearMapCLM_apply,
    map_smul (compContinuousLinearMapCLM (WithLp.fstL 2 ℝ E F)) c φ]

/-- The external wedge product is homogeneous in its second argument. -/
@[simp]
theorem externalWedge_smul_right (c : ℝ) (φ : E [⋀^Fin k]→L[ℝ] ℝ) (ψ : F [⋀^Fin l]→L[ℝ] ℝ) :
    externalWedge φ (c • ψ) = c • externalWedge φ ψ := by
  simp only [externalWedge_def, ← wedge_smul_right, ← compContinuousLinearMapCLM_apply,
    map_smul (compContinuousLinearMapCLM (WithLp.sndL 2 ℝ E F)) c ψ]

/-- **The binomial comass bound**: `‖φ ⊠ ψ‖ ≤ binomial(k + l, k) ‖φ‖ ‖ψ‖`. -/
theorem norm_externalWedge_le (φ : E [⋀^Fin k]→L[ℝ] ℝ) (ψ : F [⋀^Fin l]→L[ℝ] ℝ) :
    ‖externalWedge φ ψ‖ ≤ (k + l).choose k * ‖φ‖ * ‖ψ‖ := by
  have hfst : ‖φ.compContinuousLinearMap (WithLp.fstL 2 ℝ E F)‖ ≤ ‖φ‖ :=
    (norm_compContinuousLinearMap_le _ _).trans <| mul_le_of_le_one_right (norm_nonneg _) <|
      pow_le_one₀ (norm_nonneg _) <| ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun x ↦ by
        simpa using WithLp.norm_fst_le (x := x)
  have hsnd : ‖ψ.compContinuousLinearMap (WithLp.sndL 2 ℝ E F)‖ ≤ ‖ψ‖ :=
    (norm_compContinuousLinearMap_le _ _).trans <| mul_le_of_le_one_right (norm_nonneg _) <|
      pow_le_one₀ (norm_nonneg _) <| ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun x ↦ by
        simpa using WithLp.norm_snd_le (x := x)
  rw [externalWedge_def]
  refine (norm_wedge_le _ _).trans ?_
  rw [mul_assoc, mul_assoc]
  gcongr

/-- **Graded commutativity.** The external wedge product of `φ` and `ψ` is `(-1) ^ (k l)` times
that of `ψ` and `φ`, after exchanging the two factors of the direct sum. -/
theorem externalWedge_comm (φ : E [⋀^Fin k]→L[ℝ] ℝ)
    (ψ : F [⋀^Fin l]→L[ℝ] ℝ) (v : Fin (k + l) → WithLp 2 (E × F)) :
    externalWedge φ ψ v = (-1 : ℝ) ^ (k * l) *
      externalWedge ψ φ (fun i ↦ LinearIsometryEquiv.withLpProdComm 2 ℝ E F
        (v (Fin.cast (Nat.add_comm l k) i))) := by
  have hcomm : externalWedge ψ φ (fun i ↦ LinearIsometryEquiv.withLpProdComm 2 ℝ E F
      (v (Fin.cast (Nat.add_comm l k) i))) =
      wedge (ψ.compContinuousLinearMap (WithLp.sndL 2 ℝ E F))
        (φ.compContinuousLinearMap (WithLp.fstL 2 ℝ E F)) (v ∘ Fin.cast (Nat.add_comm l k)) := by
    simp only [externalWedge_def, wedge_def, pairedWedge_apply, compContinuousLinearMap_apply,
      Function.comp_def, WithLp.fstL_apply, WithLp.sndL_apply,
      LinearIsometryEquiv.withLpProdComm_apply, WithLp.toLp_fst, WithLp.toLp_snd]
  rw [hcomm, externalWedge_def, wedge_comm, smul_eq_mul]

private theorem norm_externalWedge_le_norm_externalWedge_swap (φ : E [⋀^Fin k]→L[ℝ] ℝ)
    (ψ : F [⋀^Fin l]→L[ℝ] ℝ) : ‖externalWedge φ ψ‖ ≤ ‖externalWedge ψ φ‖ := by
  refine opNorm_le_bound _ (norm_nonneg _) fun v ↦ ?_
  rw [externalWedge_comm, norm_mul, norm_pow, norm_neg, norm_one, one_pow,
    one_mul]
  refine (le_opNorm _ _).trans_eq ?_
  simp only [LinearIsometryEquiv.norm_map]
  congr 1
  exact Fintype.prod_equiv (finCongr (Nat.add_comm l k)) _ _ fun _ ↦ rfl

/-- Exchanging the two factors does not change the comass of the external wedge product. -/
theorem norm_externalWedge_comm (φ : E [⋀^Fin k]→L[ℝ] ℝ) (ψ : F [⋀^Fin l]→L[ℝ] ℝ) :
    ‖externalWedge φ ψ‖ = ‖externalWedge ψ φ‖ :=
  (norm_externalWedge_le_norm_externalWedge_swap φ ψ).antisymm
    (norm_externalWedge_le_norm_externalWedge_swap ψ φ)

end Normed

section InnerProduct

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] {k l : ℕ}

/-- **The product comass lower bound**: `‖φ‖ ‖ψ‖ ≤ ‖φ ⊠ ψ‖`, with no finite-dimensionality
assumption, since the concatenation of orthonormal frames of the two factors is an orthonormal
frame of the direct sum. -/
theorem norm_mul_norm_le_norm_externalWedge (φ : E [⋀^Fin k]→L[ℝ] ℝ)
    (ψ : F [⋀^Fin l]→L[ℝ] ℝ) : ‖φ‖ * ‖ψ‖ ≤ ‖externalWedge φ ψ‖ := by
  -- On a product frame the external wedge is `φ e * ψ f`, and product frames are orthonormal.
  have key (e : Fin k → E) (he : Orthonormal ℝ e) (f : Fin l → F) (hf : Orthonormal ℝ f) :
      |φ e| * |ψ f| ≤ ‖externalWedge φ ψ‖ := by
    have h := (opNorm_le_iff_le_orthonormal (ω := externalWedge φ ψ) (norm_nonneg _)).1 le_rfl _
      (he.append_toLp_inl_toLp_inr hf)
    rwa [externalWedge_apply_append_toLp, Real.norm_eq_abs, abs_mul] at h
  rcases (norm_nonneg ψ).eq_or_lt with hψ | hψ
  · rw [← hψ, mul_zero]
    positivity
  rw [← le_div_iff₀ hψ]
  refine (opNorm_le_iff_le_orthonormal (by positivity)).2 fun e he ↦ ?_
  rw [Real.norm_eq_abs, le_div_iff₀ hψ]
  rcases (abs_nonneg (φ e)).eq_or_lt with hφ | hφ
  · rw [← hφ, zero_mul]
    positivity
  rw [mul_comm, ← le_div_iff₀ hφ]
  refine (opNorm_le_iff_le_orthonormal (by positivity)).2 fun f hf ↦ ?_
  rw [Real.norm_eq_abs, le_div_iff₀ hφ, mul_comm]
  exact key e he f hf

/-- On an orthonormal frame whose last `l` vectors lie in the second factor, the external wedge
product is at most `‖φ‖ ‖ψ‖` in absolute value. -/
theorem abs_externalWedge_apply_append_le (φ : E [⋀^Fin k]→L[ℝ] ℝ) (ψ : F [⋀^Fin l]→L[ℝ] ℝ)
    {x : Fin k → WithLp 2 (E × F)} {y : Fin l → WithLp 2 (E × F)}
    (hxy : Orthonormal ℝ (Fin.append x y)) (hy : ∀ j, (y j).fst = 0) :
    |externalWedge φ ψ (Fin.append x y)| ≤ ‖φ‖ * ‖ψ‖ := by
  rw [externalWedge_apply_append φ ψ x hy, abs_mul]
  refine mul_le_mul ?_ ?_ (abs_nonneg _) (norm_nonneg _)
  · refine (φ.le_opNorm _).trans (mul_le_of_le_one_right (norm_nonneg _) ?_)
    refine Finset.prod_le_one₀ (fun _ _ ↦ norm_nonneg _) fun i _ ↦ ?_
    refine (WithLp.norm_fst_le (x := _)).trans ?_
    simpa using (hxy.norm_eq_one (Fin.castAdd l i)).le
  · refine (opNorm_le_iff_le_orthonormal (norm_nonneg ψ)).1 le_rfl _ ?_
    have hy' : Orthonormal ℝ y := by
      simpa [Function.comp_def] using hxy.comp _ (Fin.natAdd_injective l k)
    rw [orthonormal_iff_ite] at hy' ⊢
    intro i j
    simpa [hy] using hy' i j

/-- **The comass of a product with a volume form.** If the degree of `φ` is at least the
dimension of `E` (so that `φ` is a multiple of a volume form of `E`, or zero), then
`‖φ ⊠ ψ‖ = ‖φ‖ ‖ψ‖`. In particular, for a unit volume form `φ` the external wedge product has the
comass of `ψ`. -/
theorem norm_externalWedge_of_finrank_le_left [FiniteDimensional ℝ E] (hk : finrank ℝ E ≤ k)
    (φ : E [⋀^Fin k]→L[ℝ] ℝ) (ψ : F [⋀^Fin l]→L[ℝ] ℝ) :
    ‖externalWedge φ ψ‖ = ‖φ‖ * ‖ψ‖ := by
  classical
  refine le_antisymm ?_ (norm_mul_norm_le_norm_externalWedge φ ψ)
  refine (opNorm_le_iff_le_orthonormal (by positivity)).2 fun w hw ↦ ?_
  -- Restrict to the span `W` of the frame, where the external wedge is a top-degree form; its
  -- value on any orthonormal basis of `W` computes its norm.
  let W : Submodule ℝ (WithLp 2 (E × F)) := Submodule.span ℝ (Set.range w)
  have : FiniteDimensional ℝ W := FiniteDimensional.span_of_finite ℝ (Set.finite_range w)
  have hW : finrank ℝ W = Fintype.card (Fin (k + l)) := by
    simpa using finrank_span_eq_card hw.linearIndependent
  let ρ := (externalWedge φ ψ).compContinuousLinearMap W.subtypeL
  have hρ : ‖externalWedge φ ψ w‖ ≤ ‖ρ‖ := by
    simpa [ρ, Function.comp_def, hw.norm_eq_one] using
      ρ.le_opNorm fun i ↦ ⟨w i, Submodule.subset_span (Set.mem_range_self i)⟩
  -- The first projection has rank at most `k` on `W`, so its kernel has dimension at least `l`.
  let p : W →ₗ[ℝ] E := (WithLp.fstL 2 ℝ E F).toLinearMap ∘ₗ W.subtype
  have hker : l ≤ finrank ℝ (LinearMap.ker p) := by
    have h₁ := LinearMap.finrank_range_add_finrank_ker p
    have h₂ := (LinearMap.range p).finrank_le
    simp only [hW, Fintype.card_fin] at h₁
    omega
  -- An orthonormal `l`-frame `g` of `W` inside the second factor, extended to an orthonormal
  -- basis `b` of `W` whose last `l` vectors are `g`.
  let c := stdOrthonormalBasis ℝ (LinearMap.ker p)
  let g : Fin l → W := fun j ↦ c (Fin.castLE hker j)
  have hg : Orthonormal ℝ g :=
    (c.orthonormal.comp _ (Fin.castLE_injective hker)).comp_linearIsometry
      (LinearMap.ker p).subtypeₗᵢ
  obtain ⟨b, hb⟩ := Orthonormal.exists_orthonormalBasis_extension_of_card_eq hW
    (v := Fin.append 0 g) (s := Set.range (Fin.natAdd k)) <| by
      rw [orthonormal_iff_ite] at hg ⊢
      rintro ⟨_, i, rfl⟩ ⟨_, j, rfl⟩
      simp [hg, Subtype.ext_iff, Fin.ext_iff]
  have hbg (j : Fin l) : b (Fin.natAdd k j) = g j := by
    simpa using hb _ ⟨j, rfl⟩
  have hb_eq : (fun i ↦ (b i : WithLp 2 (E × F))) =
      Fin.append (fun i ↦ (b (Fin.castAdd l i) : WithLp 2 (E × F))) fun j ↦ (g j : _) := by
    ext1 i
    cases i using Fin.addCases <;> simp [hbg]
  have hg0 (j : Fin l) : ((g j : WithLp 2 (E × F))).fst = 0 := by
    simpa [p] using LinearMap.mem_ker.mp (c (Fin.castLE hker j)).2
  have hxy : Orthonormal ℝ
      (Fin.append (fun i ↦ (b (Fin.castAdd l i) : WithLp 2 (E × F))) fun j ↦ (g j : _)) :=
    hb_eq ▸ b.orthonormal.comp_linearIsometry W.subtypeₗᵢ
  calc ‖externalWedge φ ψ w‖ ≤ ‖ρ‖ := hρ
    _ = |ρ b| := ρ.norm_eq_norm_apply_orthonormalBasis b
    _ = |externalWedge φ ψ
          (Fin.append (fun i ↦ (b (Fin.castAdd l i) : WithLp 2 (E × F))) fun j ↦ (g j : _))| := by
      simp only [ρ, compContinuousLinearMap_apply, Submodule.coe_subtypeL, Submodule.coe_subtype,
        Function.comp_def, hb_eq]
    _ ≤ ‖φ‖ * ‖ψ‖ := abs_externalWedge_apply_append_le φ ψ hxy hg0

/-- **The comass of a product with a volume form**, for a top-degree second factor:
`‖φ ⊠ ψ‖ = ‖φ‖ ‖ψ‖` when the degree of `ψ` is at least the dimension of `F`. -/
theorem norm_externalWedge_of_finrank_le_right [FiniteDimensional ℝ F] (hl : finrank ℝ F ≤ l)
    (φ : E [⋀^Fin k]→L[ℝ] ℝ) (ψ : F [⋀^Fin l]→L[ℝ] ℝ) :
    ‖externalWedge φ ψ‖ = ‖φ‖ * ‖ψ‖ := by
  rw [norm_externalWedge_comm, norm_externalWedge_of_finrank_le_left hl, mul_comm]

end InnerProduct

end ContinuousAlternatingMap
