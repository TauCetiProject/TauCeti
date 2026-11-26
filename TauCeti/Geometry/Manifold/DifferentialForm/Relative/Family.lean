/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.DifferentialForm.Relative.FirstJet

/-!
# The relative Poincaré lemma for smooth families of forms

Let `P` be a manifold of parameters and `η` a `C^r` form on `P × M`, read as the family of its
slices `η_p = ι_p^* η` along the inclusions `ι_p : x ↦ (p, x)`. This file constructs primitives of
the slices that depend jointly `C^r` on the parameter, by applying the homotopy operator to the
family of homotopies that leaves the parameter alone.

Let `h : M × [0, 1] → M` be a `C^(r + 1)` homotopy. Its *parameter-preserving* extension
`H((p, x), t) = (p, h(x, t))` is a homotopy of `P × M`, and the homotopy operator of the cylinder
of `P × M` applied to `H^* η` gives a single `C^r` form `β` on `P × M`. Pulling back along `ι_p`
commutes with the homotopy operator, so the slice `β_p` is the homotopy operator applied to
`h^* η_p`, and the homotopy formula for `h` gives

`d β_p = h₁^* η_p - h₀^* η_p`

whenever the slice `η_p` is closed, with `hₜ = h(·, t)`
(`TauCeti.exists_isSmoothForm_mextDeriv_mpullback_prodMk_eq_sub`). Only the slices of `η` need to
be closed: the form `η` on `P × M` is not, in general, since its derivative in the parameter
direction is arbitrary. Moreover `β` vanishes as a full ambient tensor of `P × M`, including the
parameter directions, at every `(p, x)` over which `h` is stationary in time, since `dH` kills the
time direction there.

For fibre scaling on the total space of a vector bundle, transported along a diffeomorphism `Φ`
onto `M` such as a tubular neighbourhood, `h₁ = id` and `h₀` is the retraction `ρ` onto the image
of the zero section, which `h` fixes at all times. This gives the **relative Poincaré lemma for
families on a tube** (`Diffeomorph.exists_isSmoothForm_family_mextDeriv_eq_sub_mpullback`,
`Diffeomorph.exists_isSmoothForm_family_relative_primitive`): a family `η` with closed slices has
a jointly `C^r` family `β` with `d β_p = η_p - ρ^* η_p`, vanishing along `P × i` for the
zero-section inclusion `i = Φ ∘ 0`, and `d β_p = η_p` as soon as every slice restricts to zero
along `i`. Through the tubular neighbourhood theorem this gives the relative Poincaré lemma for
families near an embedded submanifold,
`TauCeti.SmoothEmbedding.exists_isSmoothForm_family_relative_primitive` in
`TauCeti.Geometry.Manifold.TubularNeighborhood.RelativePoincare`.

When every slice restricts to zero along `i`, the slice `β_p` at each parameter `p` is a
relative primitive of `η_p` in the sense of the relative Poincaré lemma for a single form
(`Diffeomorph.exists_isSmoothForm_relative_primitive`): `d β_p = η_p` and `β_p` vanishes along
`i`, but without that lemma's first-jet vanishing conclusion. What the family version adds is a
choice of these primitives that is jointly `C^r` in the parameter. This is the input to Moser's
argument relative to a submanifold for a smooth family of symplectic forms that agree along the
submanifold, where the parameter is the time and the forms `η_p` are the velocities of the family.

## Main results

* `TauCeti.exists_isSmoothForm_mextDeriv_mpullback_prodMk_eq_sub`: the homotopy formula for
  families, with primitives jointly `C^r` in the parameter.
* `Diffeomorph.exists_isSmoothForm_family_mextDeriv_eq_sub_mpullback`,
  `Diffeomorph.exists_isSmoothForm_family_relative_primitive`: the relative Poincaré lemma for
  families on a tube.

## References

* A. Cannas da Silva, *Lectures on Symplectic Geometry*, Lecture Notes in Mathematics 1764,
  Springer, 2001, §6.2 (the relative Poincaré lemma) and §7.3 (its use in Moser's relative
  theorem).
* R. Bott and L. W. Tu, *Differential Forms in Algebraic Topology*, GTM 82, §4.
-/

public section

noncomputable section

open Set Bundle Manifold
open scoped ContDiff Manifold

namespace TauCeti

variable {EP HP P E H M F : Type*}
  [NormedAddCommGroup EP] [NormedSpace ℝ EP] [TopologicalSpace HP]
  {IP : ModelWithCorners ℝ EP HP} [TopologicalSpace P] [ChartedSpace HP P]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F] {k : ℕ}

/-! ### The homotopy formula for families -/

/-- **The homotopy formula for families of forms.** Let `h : M × [0, 1] → M` be a `C^(r + 1)`
homotopy, with `1 ≤ r`, and `η` a `C^r` form of positive degree on `P × M` whose slices
`η_p = ι_p^* η`, along `ι_p : x ↦ (p, x)`, are closed. Then there is a `C^r` form `β` on `P × M`
whose slices satisfy `d β_p = h(·, 1)^* η_p - h(·, 0)^* η_p` for every parameter `p`. The form
`β` vanishes, as a full ambient tensor of `P × M`, at every point `(p, x)` such that `h(x, t)`
does not depend on `t`. It is the homotopy operator applied to the pullback of `η` along the
parameter-preserving homotopy `((p, x), t) ↦ (p, h(x, t))`. -/
theorem exists_isSmoothForm_mextDeriv_mpullback_prodMk_eq_sub {r : ℕ∞} (hr : 1 ≤ r)
    [IsManifold IP 1 P] [IsManifold I 1 M] [IsManifold IP (r + 1) P] [IsManifold I (r + 1) M]
    {h : M × Icc (0 : ℝ) 1 → M}
    (hh : ContMDiff (I.prod (𝓡∂ 1)) I (r + 1) h) {η : RoughForm (IP.prod I) (P × M) F (k + 1)}
    (hη : IsSmoothForm (IP.prod I) r η)
    (hclosed : ∀ p, mextDeriv (mpullback I (IP.prod I) (Prod.mk p) η) = 0) :
    ∃ β : RoughForm (IP.prod I) (P × M) F k, IsSmoothForm (IP.prod I) r β ∧
      (∀ p, mextDeriv (mpullback I (IP.prod I) (Prod.mk p) β) =
        mpullback I I (fun x ↦ h (x, 1)) (mpullback I (IP.prod I) (Prod.mk p) η) -
          mpullback I I (fun x ↦ h (x, 0)) (mpullback I (IP.prod I) (Prod.mk p) η)) ∧
      ∀ p x y, (∀ t, h (x, t) = y) → β (p, x) = 0 := by
  have h2 : (2 : WithTop ℕ∞) ≤ r + 1 := by
    rw [← one_add_one_eq_two]
    gcongr
    exact_mod_cast hr
  have hr' : (1 : WithTop ℕ∞) ≤ r := by exact_mod_cast hr
  have : IsManifold IP 2 P := .of_le h2
  have : IsManifold I 2 M := .of_le h2
  -- The parameter-preserving homotopy of `P × M`.
  let G : (P × M) × Icc (0 : ℝ) 1 → P × M := fun q ↦ (q.1.1, h (q.1.2, q.2))
  have hG : ContMDiff ((IP.prod I).prod (𝓡∂ 1)) (IP.prod I) (r + 1) G :=
    (contMDiff_fst.comp contMDiff_fst).prodMk
      (hh.comp ((contMDiff_snd.comp contMDiff_fst).prodMk contMDiff_snd))
  have hGη : IsSmoothForm ((IP.prod I).prod (𝓡∂ 1)) r
      (mpullback ((IP.prod I).prod (𝓡∂ 1)) (IP.prod I) G η) :=
    hη.mpullback hG
  refine ⟨homotopyOperator (mpullback ((IP.prod I).prod (𝓡∂ 1)) (IP.prod I) G η),
    hGη.homotopyOperator, fun p ↦ ?_, fun p x y hx ↦ ?_⟩
  · have hι : MDifferentiable I (IP.prod I) (Prod.mk p : M → P × M) :=
      mdifferentiable_const.prodMk mdifferentiable_id
    have hιt : MDifferentiable (I.prod (𝓡∂ 1)) ((IP.prod I).prod (𝓡∂ 1))
        (Prod.map (Prod.mk p : M → P × M) (id : Icc (0 : ℝ) 1 → Icc (0 : ℝ) 1)) :=
      hι.prodMap mdifferentiable_id
    have hθ : IsSmoothForm I r (mpullback I (IP.prod I) (Prod.mk p) η) :=
      hη.mpullback (contMDiff_const.prodMk contMDiff_id)
    -- Slicing commutes with the homotopy operator, and `G` restricted to the slice cylinder of
    -- `p` is `h` followed by `ι_p`, so the slice of `β` is the homotopy operator of `h^* η_p`.
    have hGι : G ∘ Prod.map (Prod.mk p) id = Prod.mk p ∘ h := (rfl)
    have hslice : mpullback I (IP.prod I) (Prod.mk p)
          (homotopyOperator (mpullback ((IP.prod I).prod (𝓡∂ 1)) (IP.prod I) G η)) =
        homotopyOperator (mpullback (I.prod (𝓡∂ 1)) I h
          (mpullback I (IP.prod I) (Prod.mk p) η)) := by
      rw [← homotopyOperator_mpullback_prodMap_id_of_isSmoothForm hι (hGη.of_le (by simp)),
        ← mpullback_comp hιt (hG.mdifferentiable (by simp)), hGι,
        mpullback_comp (hh.mdifferentiable (by simp)) hι]
    -- The homotopy formula for `h` and the closed slice `η_p`.
    have key := mextDeriv_homotopyOperator_mpullback_add_homotopyOperator_mpullback_mextDeriv
      (hh.of_le h2) (hθ.of_le hr')
    rw [hclosed p, mpullback_zero, homotopyOperator_zero, add_zero] at key
    rw [hslice, key]
  · exact homotopyOperator_mpullback_apply_eq_zero (y := (p, y)) (fun t ↦ by simp [G, hx t]) η

/-! ### Transport to a tube -/

section Tube

variable {B FV : Type*} {V : B → Type*} [∀ b, AddCommGroup (V b)] [∀ b, Module ℝ (V b)]
  {EB HB : Type*} [NormedAddCommGroup EB] [NormedSpace ℝ EB] [TopologicalSpace HB]
  {IB : ModelWithCorners ℝ EB HB} [TopologicalSpace B] [ChartedSpace HB B]
  [NormedAddCommGroup FV] [NormedSpace ℝ FV]
  [∀ b, TopologicalSpace (V b)] [TopologicalSpace (TotalSpace FV V)] [FiberBundle FV V]
  [VectorBundle ℝ FV V] {n : WithTop ℕ∞} [ContMDiffVectorBundle n FV V IB]
  [IsManifold IP 1 P] [IsManifold I 1 M] [IsManifold IP n P] [IsManifold I n M]

/-- **The relative Poincaré lemma for families on a tube.** Let `Φ` be a `C^n` diffeomorphism
from the total space of a `C^n` vector bundle onto `M`, such as a tubular neighbourhood, with
zero-section inclusion `i = Φ ∘ 0` and retraction `ρ = Φ ∘ 0 ∘ π ∘ Φ⁻¹` onto its image. Let `η`
be a `C^r` form of positive degree on `P × M`, with `1 ≤ r` and `r + 1 ≤ n`, whose slices
`η_p = ι_p^* η` are closed. Then there is a `C^r` form `β` on `P × M` whose slices satisfy
`d β_p = η_p - ρ^* η_p`, and which vanishes as a full ambient tensor of `P × M` at every point
`(p, i b)`. -/
theorem _root_.Diffeomorph.exists_isSmoothForm_family_mextDeriv_eq_sub_mpullback
    (Φ : TotalSpace FV V ≃ₘ^n⟮IB.prod 𝓘(ℝ, FV), I⟯ M) {r : ℕ∞} (hr : 1 ≤ r) (hn : r + 1 ≤ n)
    {η : RoughForm (IP.prod I) (P × M) F (k + 1)} (hη : IsSmoothForm (IP.prod I) r η)
    (hclosed : ∀ p, mextDeriv (mpullback I (IP.prod I) (Prod.mk p) η) = 0) :
    ∃ β : RoughForm (IP.prod I) (P × M) F k, IsSmoothForm (IP.prod I) r β ∧
      (∀ p, mextDeriv (mpullback I (IP.prod I) (Prod.mk p) β) =
        mpullback I (IP.prod I) (Prod.mk p) η -
          mpullback I I (Φ ∘ zeroSection FV V ∘ π FV V ∘ Φ.symm)
            (mpullback I (IP.prod I) (Prod.mk p) η)) ∧
      ∀ p b, β (p, Φ (zeroSection FV V b)) = 0 := by
  have : IsManifold IP (r + 1) P := .of_le hn
  have : IsManifold I (r + 1) M := .of_le hn
  have : ContMDiffVectorBundle (r + 1) FV V IB := .of_le hn
  -- Fibre scaling transported along `Φ`: a homotopy from `ρ` to the identity fixing `i`.
  let h : M × Icc (0 : ℝ) 1 → M := fun q ↦ Φ (vectorBundleFiberScaling FV V (Φ.symm q.1, q.2))
  have hh : ContMDiff (I.prod (𝓡∂ 1)) I (r + 1) h :=
    (Φ.contMDiff.of_le hn).comp (contMDiff_vectorBundleFiberScaling.comp
      (((Φ.symm.contMDiff.of_le hn).comp contMDiff_fst).prodMk contMDiff_snd))
  obtain ⟨β, hβ, hdβ, hβ₀⟩ :=
    exists_isSmoothForm_mextDeriv_mpullback_prodMk_eq_sub hr hh hη hclosed
  refine ⟨β, hβ, fun p ↦ ?_, fun p b ↦ hβ₀ p _ (Φ (zeroSection FV V b)) fun t ↦ ?_⟩
  · have h₁ : (fun x ↦ h (x, 1)) = id := funext fun x ↦ by
      simp only [h, vectorBundleFiberScaling_one, Diffeomorph.apply_symm_apply, id]
    have h₀ : (fun x ↦ h (x, 0)) = Φ ∘ zeroSection FV V ∘ π FV V ∘ Φ.symm := funext fun x ↦ by
      simp only [h, vectorBundleFiberScaling_zero, Function.comp_apply]
    rw [hdβ p, h₁, h₀, mpullback_id]
  · simp only [h, Diffeomorph.symm_apply_apply, vectorBundleFiberScaling_zeroSection]

/-- **The relative Poincaré lemma for families on a tube**, for families restricting to zero on
the core. Let `Φ` be a `C^n` diffeomorphism from the total space of a `C^n` vector bundle onto
`M`, such as a tubular neighbourhood, with zero-section inclusion `i = Φ ∘ 0`. Let `η` be a `C^r`
form of positive degree on `P × M`, with `1 ≤ r` and `r + 1 ≤ n`, whose slices `η_p = ι_p^* η`
are closed and satisfy `i^* η_p = 0`. Then there is a `C^r` form `β` on `P × M` whose slices are
primitives, `d β_p = η_p`, and which vanishes as a full ambient tensor of `P × M` at every point
`(p, i b)`. -/
theorem _root_.Diffeomorph.exists_isSmoothForm_family_relative_primitive
    (Φ : TotalSpace FV V ≃ₘ^n⟮IB.prod 𝓘(ℝ, FV), I⟯ M) {r : ℕ∞} (hr : 1 ≤ r) (hn : r + 1 ≤ n)
    {η : RoughForm (IP.prod I) (P × M) F (k + 1)} (hη : IsSmoothForm (IP.prod I) r η)
    (hclosed : ∀ p, mextDeriv (mpullback I (IP.prod I) (Prod.mk p) η) = 0)
    (hi : ∀ p, mpullback IB I (Φ ∘ zeroSection FV V) (mpullback I (IP.prod I) (Prod.mk p) η) = 0) :
    ∃ β : RoughForm (IP.prod I) (P × M) F k, IsSmoothForm (IP.prod I) r β ∧
      (∀ p, mextDeriv (mpullback I (IP.prod I) (Prod.mk p) β) =
        mpullback I (IP.prod I) (Prod.mk p) η) ∧
      ∀ p b, β (p, Φ (zeroSection FV V b)) = 0 := by
  obtain ⟨β, hβ, hdβ, hβ₀⟩ :=
    Φ.exists_isSmoothForm_family_mextDeriv_eq_sub_mpullback hr hn hη hclosed
  refine ⟨β, hβ, fun p ↦ ?_, hβ₀⟩
  rw [hdβ, Φ.mpullback_retraction_eq_zero (lt_of_lt_of_le (by simp) hn).ne' (hi p), sub_zero]

end Tube

end TauCeti
