/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Contact.Darboux.Manifold
public import TauCeti.Geometry.Contact.Standard.ConformalLift
import TauCeti.Geometry.Contact.Levi
import TauCeti.Geometry.Manifold.Diffeomorph.Basic
import TauCeti.Geometry.Manifold.LocalDiffeomorph.Constructions
import TauCeti.Geometry.Manifold.LocalDiffeomorph.MFDeriv

/-!
# Contact charts with prescribed first-order data

Let `D` and `D'` be contact structures on boundaryless manifolds `M` and `M'` of the same
dimension `2 n + 1`, with Levi forms `L_D` and `L_D'` taking values in the contact lines
`T M ⧸ D` and `T M' ⧸ D'`. At a point the first-order data of a local contactomorphism are a
linear isomorphism of the contact hyperplanes together with an isomorphism of the contact lines,
the first conformally symplectic for the Levi forms with respect to the second. This file proves
that every such pair is realized, which is the case of a point in the isotropic neighbourhood
theorem, where the conformal symplectic normal space of a point is the whole contact hyperplane.

The data are given by a single linear map `T : T_x M → T_x' M'` carrying `D x` onto `D' x'` with
`L_D' (T u, T v)` equal to the image of `L_D (u, v)` under the map of contact lines induced by `T`.
Then there is a partial diffeomorphism `φ` with `φ x = x'` whose differential carries `D` onto `D'`
on its source, agrees with `T` on `D x`, and agrees with `T` modulo `D' x'`
(`TauCeti.IsContactDistribution.exists_partialDiffeomorph_mfderiv_eq`). No contact form or
coorientation is chosen, and the map of contact lines may reverse any coorientation.

The proof reads everything in contact Darboux charts `c₁` and `c₂` centred at `x` and `x'`
(`TauCeti.IsContactDistribution.exists_darbouxChart`). At the centre the contact hyperplane is
`z = 0`, and by the naturality of the Levi form (`TauCeti.distributionLeviForm_restrict_mfderiv`)
together with `TauCeti.SmoothForm.liftQ_distributionLeviForm_kerDistribution`, the Levi form is
read as the standard symplectic form `ω` with values in `ℝ` through the `z` coordinate. So `T`
becomes a linear map `S` of `V × V × ℝ` which preserves `z = 0` and is conformally symplectic
there with multiplier `c`, the `z` coordinate of `S (0, 0, 1)`. The contact lift of its
restriction (`TauCeti.conformalContactLift`) is a contactomorphism of the standard contact space
fixing the origin whose differential there agrees with `S` on `z = 0` and in the `z` coordinate.
The partial diffeomorphism is `c₂⁻¹ ∘ F ∘ c₁`.

## Main results

* `TauCeti.IsContactDistribution.exists_partialDiffeomorph_mfderiv_eq`: contact charts with
  prescribed first-order data.

## References

* H. Geiges, *An Introduction to Contact Topology*, Cambridge Studies in Advanced Mathematics 109
  (2008), Theorem 2.5.1 (Darboux) and Section 2.5 (the isotropic neighbourhood theorem).
* S. Courte and S. Guillermou, *Introduction to symplectic and contact geometry*, course notes,
  Université Grenoble Alpes (2018), Proposition 3.5 (the conformal symplectic normal bundle with
  values in the contact line).
-/

public section

noncomputable section

open Set Filter Module
open scoped RealInnerProductSpace ContDiff Manifold Topology

namespace TauCeti

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M]

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]

omit [FiniteDimensional ℝ E] [IsManifold I ∞ M] [FiniteDimensional ℝ V] in
/-- In a chart of a contact structure `D` onto the standard contact space, centred at `x`, a
tangent vector at `x` lies in `D x` exactly when the `z` coordinate of its image vanishes. -/
private theorem mem_iff_snd_snd_eq_zero {D : Π x : M, Submodule ℝ (TangentSpace I x)}
    (c : PartialDiffeomorph I 𝓘(ℝ, V × V × ℝ) M (V × V × ℝ) ∞) {x : M} (hx : x ∈ c.source)
    (hcx : c x = 0) (hcD : ∀ y ∈ c.source, D y = ((innerProductContactForm V).kerDistribution
      (c y)).comap (mfderiv I 𝓘(ℝ, V × V × ℝ) c y).toLinearMap)
    {P : TangentSpace I x →L[ℝ] V × V × ℝ} (hP : mfderiv I 𝓘(ℝ, V × V × ℝ) c x = P)
    (v : TangentSpace I x) : v ∈ D x ↔ (P v).2.2 = 0 := by
  subst hP
  rw [hcD x hx, Submodule.mem_comap, ContinuousLinearMap.coe_coe,
    mem_kerDistribution_innerProductContactForm]
  simp only [hcx, Prod.snd_zero, Prod.fst_zero, inner_zero_left]
  exact Iff.rfl

/-- In a chart of a contact structure `D` onto the standard contact space, centred at `x`, the
Levi form of `D` at `x` is read as the standard symplectic form, with values in `ℝ` through the
`z` coordinate: if `[w] = L_D(u, v)`, then `ω(d c u, d c v)` is the `z` coordinate of `d c w`. -/
private theorem stdSymplecticForm_mfderiv_eq_of_mkQ_eq
    {D : Π x : M, Submodule ℝ (TangentSpace I x)} (hD : IsContactDistribution I ∞ D)
    (c : PartialDiffeomorph I 𝓘(ℝ, V × V × ℝ) M (V × V × ℝ) ∞) {x : M} (hx : x ∈ c.source)
    (hcx : c x = 0) (hcD : ∀ y ∈ c.source, D y = ((innerProductContactForm V).kerDistribution
      (c y)).comap (mfderiv I 𝓘(ℝ, V × V × ℝ) c y).toLinearMap)
    {P : TangentSpace I x →L[ℝ] V × V × ℝ} (hP : mfderiv I 𝓘(ℝ, V × V × ℝ) c x = P)
    {u v : D x} {w : TangentSpace I x} (hw : (D x).mkQ w = distributionLeviForm D x u v) :
    stdSymplecticForm ((P u).1, (P u).2.1) ((P v).1, (P v).2.1) = (P w).2.2 := by
  subst hP
  set α := innerProductContactForm V
  have hα := isContactForm_innerProductContactForm V
  have hK := hα.isContMDiffDistribution_kerDistribution (n := 1)
  have hD₁ := hD.isContMDiffDistribution.of_le (m := 1) (by simp)
  have hc : ContMDiffAt I _ ∞ c x := c.contMDiffOn.contMDiffAt (c.open_source.mem_nhds hx)
  have hfD (u : TangentSpace I x) (hu : u ∈ D x) :
      mfderiv I _ c x u ∈ α.kerDistribution (c x) := by
    rw [hcD x hx] at hu
    exact hu
  have hfD' : ∀ᶠ y in 𝓝 x, ∀ v ∈ α.kerDistribution (c y),
      (mfderiv I _ c y).inverse v ∈ D y := by
    filter_upwards [c.open_source.mem_nhds hx] with y hy v hv
    rw [hcD y hy, Submodule.mem_comap, ContinuousLinearMap.coe_coe,
      (c.isInvertible_mfderiv (by simp) hy).self_apply_inverse]
    exact hv
  -- The chart carries the Levi form of `D` to that of `ker α`, which `α` reads as `dα = ω`.
  have hnat := distributionLeviForm_restrict_mfderiv hD₁ hK hc (by simp)
    (c.isInvertible_mfderiv (by simp) hx) hfD hfD' u v
  have hlift := SmoothForm.liftQ_distributionLeviForm_kerDistribution (hα.apply_ne_zero (c x))
    ((mfderiv I _ c x).toLinearMap.restrict hfD u) ((mfderiv I _ c x).toLinearMap.restrict hfD v)
  rw [hnat, mextDeriv_innerProductContactForm_apply, ← hw] at hlift
  simp [hcx] at hlift
  rw [stdSymplecticForm_apply]
  exact hlift.symm

section Linear

omit [FiniteDimensional ℝ V] in
/-- A linear map of `V × V × ℝ` preserving the hyperplane `z = 0` multiplies the `z` coordinate
by the `z` coordinate of the image of `(0, 0, 1)`. -/
private theorem snd_snd_apply_eq_mul (S : V × V × ℝ →ₗ[ℝ] V × V × ℝ)
    (hS : ∀ y : V × V × ℝ, y.2.2 = 0 → (S y).2.2 = 0) (y : V × V × ℝ) :
    (S y).2.2 = (S (0, 0, 1)).2.2 * y.2.2 := by
  have hy : y = (y.1, y.2.1, 0) + y.2.2 • ((0, 0, 1) : V × V × ℝ) := by
    ext <;> simp
  rw [hy, map_add, map_smul, Prod.snd_add, Prod.snd_add, hS _ rfl]
  simp [mul_comm]

/-- **First-order realization on the standard contact space.** Let `S` be a linear map of
`V × V × ℝ` with `S y` in the hyperplane `z = 0` exactly when `y` is, and conformally symplectic on
that hyperplane with multiplier `c = (S (0, 0, 1)).2.2`. Then `c ≠ 0`, and `S` agrees on the
hyperplane, and in its `z` coordinate everywhere, with the differential at the origin of the
contact lift of a conformally symplectic linear equivalence with multiplier `c`. -/
private theorem exists_conformalContactLift_of_linearMap
    (S : V × V × ℝ →ₗ[ℝ] V × V × ℝ) (hS : ∀ y : V × V × ℝ, (S y).2.2 = 0 ↔ y.2.2 = 0)
    (hSω : ∀ u v : V × V × ℝ, u.2.2 = 0 → v.2.2 = 0 →
      stdSymplecticForm ((S u).1, (S u).2.1) ((S v).1, (S v).2.1) =
        (S (0, 0, 1)).2.2 * stdSymplecticForm (u.1, u.2.1) (v.1, v.2.1)) :
    ∃ A : (V × V) ≃L[ℝ] V × V, (S (0, 0, 1)).2.2 ≠ 0 ∧
      (∀ u w, stdSymplecticForm (A u) (A w) = (S (0, 0, 1)).2.2 * stdSymplecticForm u w) ∧
      (∀ y : V × V × ℝ, y.2.2 = 0 →
        fderiv ℝ (conformalContactLift (A : V × V →L[ℝ] V × V) (S (0, 0, 1)).2.2) 0 y = S y) ∧
      ∀ y : V × V × ℝ,
        (fderiv ℝ (conformalContactLift (A : V × V →L[ℝ] V × V) (S (0, 0, 1)).2.2) 0 y).2.2 =
          (S y).2.2 := by
  set c := (S (0, 0, 1)).2.2
  have hc : c ≠ 0 := fun h ↦ one_ne_zero ((hS (0, 0, 1)).1 h)
  -- The restriction of `S` to the hyperplane `z = 0`, read in the `(q, p)` coordinates.
  let ι : V × V →ₗ[ℝ] V × V × ℝ :=
    (LinearMap.fst ℝ V V).prod ((LinearMap.snd ℝ V V).prod 0)
  let π : V × V × ℝ →ₗ[ℝ] V × V :=
    (LinearMap.fst ℝ V (V × ℝ)).prod ((LinearMap.fst ℝ V ℝ).comp (LinearMap.snd ℝ V (V × ℝ)))
  let A₀ : V × V →L[ℝ] V × V := LinearMap.toContinuousLinearMap (π ∘ₗ S ∘ₗ ι)
  have hA₀ (w : V × V) : A₀ w = ((S (w.1, w.2, 0)).1, (S (w.1, w.2, 0)).2.1) := rfl
  have hA (u w : V × V) : stdSymplecticForm (A₀ u) (A₀ w) = c * stdSymplecticForm u w := by
    rw [hA₀, hA₀]
    exact hSω (u.1, u.2, 0) (w.1, w.2, 0) rfl rfl
  have hinj := injective_of_stdSymplecticForm_map_eq_mul hc hA
  let A : (V × V) ≃L[ℝ] V × V :=
    (LinearEquiv.ofInjectiveEndo (A₀ : V × V →ₗ[ℝ] V × V) hinj).toContinuousLinearEquiv
  have hAA₀ : (A : V × V →L[ℝ] V × V) = A₀ := by
    ext w <;> simp [A]
  -- On the hyperplane `z = 0`, `S` is determined by its `(q, p)` coordinates.
  have hS₀ (y : V × V × ℝ) (hy : y.2.2 = 0) :
      S y = ((A₀ (y.1, y.2.1)).1, (A₀ (y.1, y.2.1)).2, 0) := by
    have hy' : y = (y.1, y.2.1, 0) := by
      ext <;> simp [hy]
    have hz := (hS y).2 hy
    rw [hA₀, ← hy']
    ext <;> simp [hz]
  refine ⟨A, hc, fun u w ↦ ?_, fun y hy ↦ ?_, fun y ↦ ?_⟩
  · have hu : A u = A₀ u := congrArg (· u) hAA₀
    have hw : A w = A₀ w := congrArg (· w) hAA₀
    rw [hu, hw]
    exact hA u w
  · rw [hAA₀, fderiv_conformalContactLift_zero_apply, hS₀ y hy, hy, mul_zero]
  · rw [fderiv_conformalContactLift_zero_apply, snd_snd_apply_eq_mul S (fun y hy ↦ (hS y).2 hy) y]

end Linear

variable {E' H' M' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E']
  [TopologicalSpace H'] {I' : ModelWithCorners ℝ E' H'} [TopologicalSpace M']
  [ChartedSpace H' M'] [IsManifold I' ∞ M']

variable {D : Π x : M, Submodule ℝ (TangentSpace I x)}
  {D' : Π x : M', Submodule ℝ (TangentSpace I' x)} {x : M} {x' : M'}

/-- Read in contact charts centred at `x` and `x'`, a linear map `T` carrying `D x` onto `D' x'`
and conformally symplectic for the Levi forms is realized to first order at the origin by the
contact lift of a conformally symplectic linear equivalence: the differential of the lift agrees
with `T` on `D x`, and in the `z` coordinate everywhere. -/
private theorem exists_conformalContactLift_of_charts
    (hD : IsContactDistribution I ∞ D) (hD' : IsContactDistribution I' ∞ D')
    (c₁ : PartialDiffeomorph I 𝓘(ℝ, V × V × ℝ) M (V × V × ℝ) ∞) (hx₁ : x ∈ c₁.source)
    (hc₁x : c₁ x = 0) (hc₁D : ∀ y ∈ c₁.source, D y = ((innerProductContactForm V).kerDistribution
      (c₁ y)).comap (mfderiv I 𝓘(ℝ, V × V × ℝ) c₁ y).toLinearMap)
    (c₂ : PartialDiffeomorph I' 𝓘(ℝ, V × V × ℝ) M' (V × V × ℝ) ∞) (hx₂ : x' ∈ c₂.source)
    (hc₂x : c₂ x' = 0) (hc₂D : ∀ y ∈ c₂.source, D' y = ((innerProductContactForm V).kerDistribution
      (c₂ y)).comap (mfderiv I' 𝓘(ℝ, V × V × ℝ) c₂ y).toLinearMap)
    {P₁ : TangentSpace I x →L[ℝ] V × V × ℝ} (hP₁ : mfderiv I 𝓘(ℝ, V × V × ℝ) c₁ x = P₁)
    {P₂ : TangentSpace I' x' →L[ℝ] V × V × ℝ} (hP₂ : mfderiv I' 𝓘(ℝ, V × V × ℝ) c₂ x' = P₂)
    (T : TangentSpace I x →ₗ[ℝ] TangentSpace I' x') (hTD : ∀ u ∈ D x, T u ∈ D' x')
    (hTD' : ∀ u, T u ∈ D' x' → u ∈ D x)
    (hTL : ∀ u v : D x, distributionLeviForm D' x' (T.restrict hTD u) (T.restrict hTD v) =
      (D x).mapQ (D' x') T hTD (distributionLeviForm D x u v)) :
    ∃ (A : (V × V) ≃L[ℝ] V × V) (c : ℝ), c ≠ 0 ∧
      (∀ u w, stdSymplecticForm (A u) (A w) = c * stdSymplecticForm u w) ∧
      (∀ u ∈ D x, fderiv ℝ (conformalContactLift (A : V × V →L[ℝ] V × V) c) 0 (P₁ u) = P₂ (T u)) ∧
      ∀ v, (fderiv ℝ (conformalContactLift (A : V × V →L[ℝ] V × V) c) 0 (P₁ v)).2.2 =
        (P₂ (T v)).2.2 := by
  have hP₁i : P₁.IsInvertible := hP₁ ▸ c₁.isInvertible_mfderiv (by simp) hx₁
  have hmem₁ := mem_iff_snd_snd_eq_zero c₁ hx₁ hc₁x hc₁D hP₁
  have hmem₂ := mem_iff_snd_snd_eq_zero c₂ hx₂ hc₂x hc₂D hP₂
  have hinv₁ (y : V × V × ℝ) : P₁ (P₁.inverse y) = y := hP₁i.self_apply_inverse y
  -- The prescribed linear map, read in the two charts.
  let S : V × V × ℝ →ₗ[ℝ] V × V × ℝ := P₂.toLinearMap ∘ₗ T ∘ₗ P₁.inverse.toLinearMap
  have hSapp (y) : S y = P₂ (T (P₁.inverse y)) := rfl
  have hS (y : V × V × ℝ) : (S y).2.2 = 0 ↔ y.2.2 = 0 := by
    rw [hSapp, ← hmem₂, ← hinv₁ y, ← hmem₁, hinv₁ y]
    exact ⟨hTD' _, hTD _⟩
  -- `S` is conformally symplectic on `z = 0`, because `T` is for the Levi forms.
  have hSω (u v : V × V × ℝ) (hu : u.2.2 = 0) (hv : v.2.2 = 0) :
      stdSymplecticForm ((S u).1, (S u).2.1) ((S v).1, (S v).2.1) =
        (S (0, 0, 1)).2.2 * stdSymplecticForm (u.1, u.2.1) (v.1, v.2.1) := by
    have hu₀ : P₁.inverse u ∈ D x := (hmem₁ _).2 (by rwa [hinv₁])
    have hv₀ : P₁.inverse v ∈ D x := (hmem₁ _).2 (by rwa [hinv₁])
    obtain ⟨w, hw⟩ := (D x).mkQ_surjective (distributionLeviForm D x ⟨_, hu₀⟩ ⟨_, hv₀⟩)
    have hw' : (D' x').mkQ (T w) =
        distributionLeviForm D' x' (T.restrict hTD ⟨_, hu₀⟩) (T.restrict hTD ⟨_, hv₀⟩) := by
      rw [hTL, ← hw, Submodule.mkQ_apply, Submodule.mkQ_apply, Submodule.mapQ_apply]
    have h₁ := stdSymplecticForm_mfderiv_eq_of_mkQ_eq hD c₁ hx₁ hc₁x hc₁D hP₁ hw
    have h₂ := stdSymplecticForm_mfderiv_eq_of_mkQ_eq hD' c₂ hx₂ hc₂x hc₂D hP₂ hw'
    simp only [LinearMap.coe_restrict_apply, hinv₁] at h₁ h₂
    have hSw : S (P₁ w) = P₂ (T w) := by
      rw [hSapp, hP₁i.inverse_apply_self]
    beta_reduce
    rw [hSapp, hSapp, h₂, h₁, ← hSw, snd_snd_apply_eq_mul S (fun y hy ↦ (hS y).2 hy)]
  obtain ⟨A, hc, hA, hd₁, hd₂⟩ := exists_conformalContactLift_of_linearMap S hS hSω
  refine ⟨A, _, hc, hA, fun u hu ↦ ?_, fun v ↦ ?_⟩
  · rw [hd₁ _ ((hmem₁ u).1 hu), hSapp, hP₁i.inverse_apply_self]
  · rw [hd₂, hSapp, hP₁i.inverse_apply_self]

omit [FiniteDimensional ℝ E] [IsManifold I ∞ M] [FiniteDimensional ℝ V] [FiniteDimensional ℝ E']
  [IsManifold I' ∞ M'] in
/-- The chain rule for the composite `c₂⁻¹ ∘ F ∘ c₁` of a chart, a diffeomorphism of the standard
contact space and an inverse chart. -/
private theorem mfderiv_trans_trans_symm_apply
    (c₁ : PartialDiffeomorph I 𝓘(ℝ, V × V × ℝ) M (V × V × ℝ) ∞) (F : (V × V × ℝ) ≃ₘ[ℝ] V × V × ℝ)
    (c₂ : PartialDiffeomorph I' 𝓘(ℝ, V × V × ℝ) M' (V × V × ℝ) ∞) {y : M}
    (hy : y ∈ (c₁.trans (F.toPartialDiffeomorph.trans c₂.symm)).source) (v : TangentSpace I y) :
    mfderiv I I' (c₁.trans (F.toPartialDiffeomorph.trans c₂.symm)) y v =
      mfderiv 𝓘(ℝ, V × V × ℝ) I' c₂.symm (F (c₁ y))
        (mfderiv 𝓘(ℝ, V × V × ℝ) 𝓘(ℝ, V × V × ℝ) F (c₁ y) (mfderiv I 𝓘(ℝ, V × V × ℝ) c₁ y v)) := by
  have hinf : (∞ : ℕ∞ω) ≠ 0 := by simp
  have hy₂ : c₁ y ∈ (F.toPartialDiffeomorph.trans c₂.symm).source := by
    simp only [PartialDiffeomorph.trans_source, Set.mem_inter_iff, Set.mem_preimage] at hy
    exact hy.2
  have h₂ : mfderiv 𝓘(ℝ, V × V × ℝ) I' (F.toPartialDiffeomorph.trans c₂.symm) (c₁ y) =
      (mfderiv 𝓘(ℝ, V × V × ℝ) I' c₂.symm (F (c₁ y))).comp
        (mfderiv 𝓘(ℝ, V × V × ℝ) 𝓘(ℝ, V × V × ℝ) F (c₁ y)) := by
    rw [PartialDiffeomorph.mfderiv_trans _ _ hinf hy₂, Diffeomorph.coe_toPartialDiffeomorph]
  rw [PartialDiffeomorph.mfderiv_trans _ _ hinf hy, h₂]
  rfl

omit [FiniteDimensional ℝ E] [IsManifold I ∞ M] [FiniteDimensional ℝ V] [FiniteDimensional ℝ E']
  [IsManifold I' ∞ M'] in
/-- If `c₁` and `c₂` are charts carrying `D` and `D'` to the standard contact structure and `F`
is a contactomorphism of the standard contact structure, then `c₂⁻¹ ∘ F ∘ c₁` carries `D` onto
`D'` at every point of its source. -/
private theorem comap_mfderiv_trans_trans_symm
    (c₁ : PartialDiffeomorph I 𝓘(ℝ, V × V × ℝ) M (V × V × ℝ) ∞)
    (hc₁D : ∀ y ∈ c₁.source, D y = ((innerProductContactForm V).kerDistribution
      (c₁ y)).comap (mfderiv I 𝓘(ℝ, V × V × ℝ) c₁ y).toLinearMap)
    (c₂ : PartialDiffeomorph I' 𝓘(ℝ, V × V × ℝ) M' (V × V × ℝ) ∞)
    (hc₂D : ∀ y ∈ c₂.source, D' y = ((innerProductContactForm V).kerDistribution
      (c₂ y)).comap (mfderiv I' 𝓘(ℝ, V × V × ℝ) c₂ y).toLinearMap)
    (F : (V × V × ℝ) ≃ₘ[ℝ] V × V × ℝ)
    (hF : F.IsContactomorphism (innerProductContactForm V) (innerProductContactForm V)) {y : M}
    (hy : y ∈ (c₁.trans (F.toPartialDiffeomorph.trans c₂.symm)).source) :
    D y = (D' (c₁.trans (F.toPartialDiffeomorph.trans c₂.symm) y)).comap
      (mfderiv I I' (c₁.trans (F.toPartialDiffeomorph.trans c₂.symm)) y).toLinearMap := by
  set φ := c₁.trans (F.toPartialDiffeomorph.trans c₂.symm)
  have hφ : φ y = c₂.symm (F (c₁ y)) := by
    simp [φ]
  have hsrc : y ∈ c₁.source ∧ F (c₁ y) ∈ c₂.target := by
    simpa [φ, PartialDiffeomorph.trans_source] using hy
  have hy' : φ y ∈ c₂.source := by
    rw [hφ]
    exact c₂.map_target hsrc.2
  -- The differential of `c₂` at `φ y` undoes that of `c₂⁻¹` at `F (c₁ y)`.
  have hinv (q : M') (hq : q = c₂.symm (F (c₁ y)))
      (w : TangentSpace 𝓘(ℝ, V × V × ℝ) (F (c₁ y))) :
      mfderiv I' 𝓘(ℝ, V × V × ℝ) c₂ q (mfderiv 𝓘(ℝ, V × V × ℝ) I' c₂.symm (F (c₁ y)) w) = w := by
    subst hq
    exact c₂.mfderiv_apply_mfderiv_symm_apply (by simp) hsrc.2 w
  -- Membership in the standard contact structure only depends on the point.
  have hker {p p' : V × V × ℝ} (h : p = p') (w : V × V × ℝ) :
      w ∈ (innerProductContactForm V).kerDistribution p ↔
        w ∈ (innerProductContactForm V).kerDistribution p' := by
    subst h
    rfl
  have hr : F (c₁ y) = c₂ (φ y) := by
    rw [hφ]
    exact (c₂.right_inv hsrc.2).symm
  ext v
  rw [Submodule.mem_comap, hc₁D y hsrc.1, Submodule.mem_comap, hc₂D _ hy', Submodule.mem_comap,
    ContinuousLinearMap.coe_coe, ContinuousLinearMap.coe_coe, ContinuousLinearMap.coe_coe,
    mfderiv_trans_trans_symm_apply c₁ F c₂ hy, hinv _ hφ]
  exact (Diffeomorph.isContactomorphism_iff.1 hF _ _).symm.trans (hker hr _)

omit [FiniteDimensional ℝ E] [IsManifold I ∞ M] [FiniteDimensional ℝ V] [FiniteDimensional ℝ E']
  [IsManifold I' ∞ M'] in
/-- Given contact charts centred at `x` and `x'` and the contact lift `F` of a conformally
symplectic linear equivalence, the composite `c₂⁻¹ ∘ F ∘ c₁` is a partial diffeomorphism carrying
`D` onto `D'`, with differential at `x` read in the charts as that of `F` at the origin. -/
private theorem exists_partialDiffeomorph_of_conformalContactLift
    (c₁ : PartialDiffeomorph I 𝓘(ℝ, V × V × ℝ) M (V × V × ℝ) ∞) (hx₁ : x ∈ c₁.source)
    (hc₁x : c₁ x = 0) (hc₁D : ∀ y ∈ c₁.source, D y = ((innerProductContactForm V).kerDistribution
      (c₁ y)).comap (mfderiv I 𝓘(ℝ, V × V × ℝ) c₁ y).toLinearMap)
    (c₂ : PartialDiffeomorph I' 𝓘(ℝ, V × V × ℝ) M' (V × V × ℝ) ∞) (hx₂ : x' ∈ c₂.source)
    (hc₂x : c₂ x' = 0) (hc₂D : ∀ y ∈ c₂.source, D' y = ((innerProductContactForm V).kerDistribution
      (c₂ y)).comap (mfderiv I' 𝓘(ℝ, V × V × ℝ) c₂ y).toLinearMap)
    {P₁ : TangentSpace I x →L[ℝ] V × V × ℝ} (hP₁ : mfderiv I 𝓘(ℝ, V × V × ℝ) c₁ x = P₁)
    {P₂ : TangentSpace I' x' →L[ℝ] V × V × ℝ} (hP₂ : mfderiv I' 𝓘(ℝ, V × V × ℝ) c₂ x' = P₂)
    (A : (V × V) ≃L[ℝ] V × V) {c : ℝ} (hc : c ≠ 0)
    (hA : ∀ u w, stdSymplecticForm (A u) (A w) = c * stdSymplecticForm u w) :
    ∃ φ : PartialDiffeomorph I I' M M' ∞, x ∈ φ.source ∧ φ x = x' ∧
      (∀ y ∈ φ.source, D y = (D' (φ y)).comap (mfderiv I I' φ y).toLinearMap) ∧
      ∀ v, mfderiv I I' φ x v =
        P₂.inverse (fderiv ℝ (conformalContactLift (A : V × V →L[ℝ] V × V) c) 0 (P₁ v)) := by
  have hinf : (∞ : ℕ∞ω) ≠ 0 := by simp
  have hP₂i : P₂.IsInvertible := hP₂ ▸ c₂.isInvertible_mfderiv hinf hx₂
  set F := conformalContactLiftDiffeomorph A hc
  have hc₂0 : F (c₁ x) = c₂ x' := by
    rw [hc₁x, coe_conformalContactLiftDiffeomorph, conformalContactLift_zero, hc₂x]
  have hx : x ∈ (c₁.trans (F.toPartialDiffeomorph.trans c₂.symm)).source := by
    simpa [PartialDiffeomorph.trans_source, hx₁, hc₂0] using c₂.map_source hx₂
  -- The differential of `c₂⁻¹` at the centre is the inverse of `P₂`.
  have hsymm (p : V × V × ℝ) (hp : p = c₂ x') (y : V × V × ℝ) :
      mfderiv 𝓘(ℝ, V × V × ℝ) I' c₂.symm p y = P₂.inverse y := by
    subst hp
    have h := c₂.mfderiv_symm_apply_mfderiv_apply hinf hx₂ (P₂.inverse y)
    rw [hP₂] at h
    conv_lhs => rw [← hP₂i.self_apply_inverse y]
    exact h
  have hdF (w : V × V × ℝ) : mfderiv 𝓘(ℝ, V × V × ℝ) 𝓘(ℝ, V × V × ℝ) F (c₁ x) w =
      fderiv ℝ (conformalContactLift (A : V × V →L[ℝ] V × V) c) 0 w := by
    rw [mfderiv_eq_fderiv, coe_conformalContactLiftDiffeomorph, hc₁x]
    rfl
  refine ⟨_, hx, ?_, fun y hy ↦ comap_mfderiv_trans_trans_symm c₁ hc₁D c₂ hc₂D F
    (isContactomorphism_conformalContactLiftDiffeomorph A hc hA) hy, fun v ↦ ?_⟩
  · simp only [PartialDiffeomorph.coe_trans, Function.comp_apply,
      Diffeomorph.coe_toPartialDiffeomorph, hc₂0]
    exact c₂.left_inv hx₂
  · rw [mfderiv_trans_trans_symm_apply c₁ F c₂ hx, ← hP₁]
    exact (hsymm _ hc₂0 _).trans (congrArg P₂.inverse (hdF _))

/-- **Contact charts with prescribed first-order data**, the point case of the isotropic
neighbourhood theorem. Let `D` and `D'` be contact structures on boundaryless manifolds of the
same dimension, let `x` and `x'` be points, and let `T : T_x M → T_x' M'` be a linear map
carrying `D x` onto `D' x'` (it maps `D x` into `D' x'`, and only vectors of `D x` into `D' x'`)
which is conformally symplectic for the Levi forms: `L_D' (T u, T v)` is the image of
`L_D (u, v)` under the map of contact lines induced by `T`. Then there is a partial
diffeomorphism `φ` from `M` to `M'`, defined near `x`, with `φ x = x'`, whose differential carries
`D` onto `D'` at every point of its source, agrees with `T` on `D x`, and agrees with `T` modulo
`D' x'`: `dφ_x v = T v + w` for some `w ∈ D' x'`. So `φ` induces exactly the restriction of `T` to
`D x` and the map of contact lines induced by `T`. -/
theorem IsContactDistribution.exists_partialDiffeomorph_mfderiv_eq
    [BoundarylessManifold I M] [BoundarylessManifold I' M']
    (hD : IsContactDistribution I ∞ D) (hD' : IsContactDistribution I' ∞ D')
    (hE : finrank ℝ E' = finrank ℝ E) (T : TangentSpace I x →ₗ[ℝ] TangentSpace I' x')
    (hTD : ∀ u ∈ D x, T u ∈ D' x') (hTD' : ∀ u, T u ∈ D' x' → u ∈ D x)
    (hTL : ∀ u v : D x, distributionLeviForm D' x' (T.restrict hTD u) (T.restrict hTD v) =
      (D x).mapQ (D' x') T hTD (distributionLeviForm D x u v)) :
    ∃ φ : PartialDiffeomorph I I' M M' ∞, x ∈ φ.source ∧ φ x = x' ∧
      (∀ y ∈ φ.source, D y = (D' (φ y)).comap (mfderiv I I' φ y).toLinearMap) ∧
      (∀ u ∈ D x, mfderiv I I' φ x u = T u) ∧
      ∀ v, ∃ w ∈ D' x', mfderiv I I' φ x v = T v + w := by
  -- Contact charts at `x` and `x'`, centred at the origin of the standard contact space.
  obtain ⟨n, c₁, hn, hx₁, hc₁x, hc₁D⟩ := hD.exists_darbouxChart x
  obtain ⟨c₂, hx₂, hc₂x, hc₂D⟩ := hD'.exists_darbouxChart_of_finrank_eq (hE.trans hn) x'
  set P₁ : TangentSpace I x →L[ℝ] EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) × ℝ :=
    mfderiv I 𝓘(ℝ, EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) × ℝ) c₁ x with hP₁
  set P₂ : TangentSpace I' x' →L[ℝ] EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) × ℝ :=
    mfderiv I' 𝓘(ℝ, EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) × ℝ) c₂ x' with hP₂
  obtain ⟨A, c, hc, hA, h₁, h₂⟩ := exists_conformalContactLift_of_charts hD hD' c₁ hx₁ hc₁x hc₁D
    c₂ hx₂ hc₂x hc₂D hP₁.symm hP₂.symm T hTD hTD' hTL
  obtain ⟨φ, hx, hφx, hφD, hdφ⟩ := exists_partialDiffeomorph_of_conformalContactLift c₁ hx₁ hc₁x
    hc₁D c₂ hx₂ hc₂x hc₂D hP₁.symm hP₂.symm A hc hA
  have hP₂i : P₂.IsInvertible := c₂.isInvertible_mfderiv (by simp) hx₂
  have hmem₂ := mem_iff_snd_snd_eq_zero c₂ hx₂ hc₂x hc₂D hP₂.symm
  refine ⟨φ, hx, hφx, hφD, fun u hu ↦ ?_, fun v ↦ ?_⟩
  · rw [hdφ, h₁ u hu]
    exact hP₂i.inverse_apply_self (T u)
  · set d := fderiv ℝ (conformalContactLift (A : _ →L[ℝ] _) c) 0 (P₁ v)
    refine ⟨P₂.inverse (d - P₂ (T v)), ?_, ?_⟩
    · rw [hmem₂, hP₂i.self_apply_inverse, Prod.snd_sub, Prod.snd_sub, h₂, sub_self]
    · rw [hdφ, map_sub, hP₂i.inverse_apply_self, add_sub_cancel]

end TauCeti
