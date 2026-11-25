/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Contact.Legendrian.Normal
public import TauCeti.Geometry.Contact.OneJet
import TauCeti.Geometry.Contact.Interpolation
import TauCeti.Geometry.Contact.Pullback
import TauCeti.Geometry.Contact.StrictMoser.Interpolation
import TauCeti.Geometry.Manifold.ContMDiff.Subtype
import TauCeti.Geometry.Manifold.Diffeomorph.Basic
import TauCeti.Geometry.Manifold.DifferentialForm.Naturality
import TauCeti.Geometry.Manifold.DifferentialForm.Opens
import TauCeti.Geometry.Manifold.LocalDiffeomorph.Constructions
import TauCeti.Geometry.Manifold.MFDeriv.Opens
import TauCeti.Geometry.Manifold.Metrizable
import TauCeti.Geometry.Manifold.TubularNeighborhood.Riemannian.Coordinates

/-!
# The strict Legendrian neighbourhood theorem

Let `α` be a contact form on a manifold `M` of dimension `2 n + 1` and let `ι : Λ → M` be a smooth
embedding of an `n`-manifold which is Legendrian for `ker α`. The one-jet space `J¹Λ = T^* Λ × ℝ`
carries the contact form `dz - λ`, for the Liouville form `λ` of `T^* Λ`
(`TauCeti.SmoothForm.contactization`). This file proves that a neighbourhood of `ι(Λ)` is
**strictly** contactomorphic to a neighbourhood of the zero section of `J¹Λ`: there is a partial
diffeomorphism `φ` from `J¹Λ` to `M`, defined on an open neighbourhood of the zero section, with
`φ(0_q, 0) = ι q` for every `q` and

`φ^* α = dz - λ`

exactly, on the whole source of `φ`
(`TauCeti.SmoothEmbedding.exists_partialDiffeomorph_mpullback_eq_contactization`). This fixes the
contact form, not only the contact structure: a contactomorphism of the kernels would only give
`φ^* α = g (dz - λ)` for a nowhere vanishing function `g`. Neither compactness of `Λ` nor
closedness of its image is assumed.

The proof follows Kriegl and Michor.

* **First-order identification.** The normal bundle of `ι` is identified with `T^* Λ × ℝ` by
  `[v] ↦ (dα(dι ·, v), α(v))`
  (`TauCeti.SmoothEmbedding.normalBundleDiffeomorphOfIsLegendrianImmersion`), and composing its
  inverse with the normal exponential for an auxiliary metric gives a partial diffeomorphism `Ψ`
  from `J¹Λ` to `M` with `Ψ(0_q, 0) = ι q`. Along the zero section its differential sends
  `((u, 0), 0)` to `dι u` and `((0, p), c)` to a vector `v` with `α(v) = c` and
  `dα(dι ·, v) = p`. Hence `Ψ^* α` and `dz - λ` take the same value at the zero section, and their
  exterior derivatives agree on every pair of vectors one of which is tangent to the zero section.
  They may differ on pairs of vertical vectors.
* **Contactness of the interpolation.** The zero section is Legendrian for both forms, so its
  tangent space is a coisotropic subspace of the common hyperplane `ker (dz - λ)`, and the
  agreement above keeps every interpolation `(1 - t) (dz - λ) + t Ψ^* α` contact along the zero
  section (`TauCeti.SmoothForm.isContactFormAt_add_smul_sub_of_mextDeriv_eq_on`).
* **Strict Moser.** The slice `z = 0` of `J¹Λ` contains the zero section, and `dz` vanishes on it
  and equals `dz - λ` along the zero section. The strict relative Moser theorem
  (`exists_partialDiffeomorph_mpullback_eq_of_isContactFormAt_of_apply_mfderiv_eq_zero`, in
  `TauCeti.SmoothForm`) on the source of `Ψ` then corrects `Ψ` by a partial diffeomorphism fixing
  the zero section.

## Main results

* `TauCeti.SmoothEmbedding.exists_partialDiffeomorph_mpullback_eq_contactization`: the strict
  Legendrian neighbourhood theorem.

## References

* A. Kriegl, P. W. Michor, *The Convenient Setting of Global Analysis*, Mathematical Surveys and
  Monographs 53, AMS (1997), Proposition 43.18.
* H. Geiges, *An Introduction to Contact Topology*, Cambridge Studies in Advanced Mathematics 109
  (2008), Section 2.5.
-/

public section

noncomputable section

open Bundle Set Module
open scoped Manifold Topology ContDiff

namespace TauCeti.SmoothEmbedding

variable {E H Λ F G M : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  [TopologicalSpace Λ] [ChartedSpace H Λ] [IsManifold I ∞ Λ]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  [TopologicalSpace G] {J : ModelWithCorners ℝ F G} [J.Boundaryless]
  [TopologicalSpace M] [ChartedSpace G M] [IsManifold J ∞ M] [T2Space M]
  [SecondCountableTopology M]
  {α : SmoothForm J M ℝ 1}

/-! ### First-order agreement along the zero section -/

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] in
/-- Let `L` be a linear map from the model `(E × E^*) × ℝ` of the tangent spaces of `J¹Λ` to `F`,
sending `((u, 0), 0)` to `D u` and `((0, p), c)` to a vector on which the covector `a` takes the
value `c` and whose pairing with `D u` under the two-form `b` is `p u`. If `a` vanishes on the
image of `D` and `b` on pairs from it, then `a (L w) = w₂` and `b (D u, L w) = w₁₂ u` for all
`w`. -/
private theorem firstOrder_linear (L : (E × (E →L[ℝ] ℝ)) × ℝ →L[ℝ] F) (D : E →L[ℝ] F)
    (a : F [⋀^Fin 1]→L[ℝ] ℝ) (b : F [⋀^Fin 2]→L[ℝ] ℝ)
    (hL : ∀ u, L ((u, 0), 0) = D u) (ha : ∀ u, a ![D u] = 0) (hb : ∀ u u', b ![D u, D u'] = 0)
    (hver : ∀ (p : E →L[ℝ] ℝ) (c : ℝ), a ![L ((0, p), c)] = c ∧ ∀ u, b ![D u, L ((0, p), c)] = p u)
    (w : (E × (E →L[ℝ] ℝ)) × ℝ) :
    a ![L w] = w.2 ∧ ∀ u, b ![D u, L w] = w.1.2 u := by
  have hw : L w = D w.1.1 + L ((0, w.1.2), w.2) := by
    rw [← hL, ← map_add]
    congr 1
    ext <;> simp
  have hadd (x y z : F) : b ![x, y + z] = b ![x, y] + b ![x, z] := by
    rw [b.apply_vecCons_swap, ContinuousAlternatingMap.vecCons_add, neg_add,
      ← b.apply_vecCons_swap, ← b.apply_vecCons_swap]
  refine ⟨?_, fun u ↦ ?_⟩
  · rw [hw, ContinuousAlternatingMap.vecCons_add, ha, (hver _ _).1, zero_add]
  · rw [hw, hadd, hb, (hver _ _).2, zero_add]

variable (I) in
/-- The point `(0_q, 0)` of the one-jet space `J¹Λ = T^* Λ × ℝ` over `q`. -/
private abbrev jetZero (q : Λ) : CotangentBundle I Λ × ℝ :=
  (zeroSection (E →L[ℝ] ℝ) (fun x : Λ ↦ TangentSpace I x →L[ℝ] ℝ) q, 0)

/-- The first-order conditions on `Ψ : J¹Λ → M` at `(0_q, 0)` relative to `ι : Λ → M` and a
one-form `α` on `M`: the differential of `Ψ` sends `((u, 0), 0)` to `dι u`, and `Ψ^* α`
evaluates a tangent vector `w` to `w₂`, with `dα(dι u, dΨ w) = w₁₂ u`. -/
private def IsJetFirstOrder (ι : Λ → M) (α : SmoothForm J M ℝ 1)
    (Ψ : CotangentBundle I Λ × ℝ → M) (q : Λ) : Prop :=
  (∀ u : TangentSpace I q, mfderiv ((I.prod 𝓘(ℝ, E →L[ℝ] ℝ)).prod 𝓘(ℝ)) J Ψ (jetZero I q)
      ((u, (0 : E →L[ℝ] ℝ)), (0 : ℝ)) = mfderiv I J ι q u) ∧
    ∀ w : TangentSpace ((I.prod 𝓘(ℝ, E →L[ℝ] ℝ)).prod 𝓘(ℝ)) (jetZero I q),
      α.val (ι q) ![mfderiv ((I.prod 𝓘(ℝ, E →L[ℝ] ℝ)).prod 𝓘(ℝ)) J Ψ (jetZero I q) w] = w.2 ∧
      ∀ u : TangentSpace I q, mextDeriv α.val (ι q) ![mfderiv I J ι q u,
        mfderiv ((I.prod 𝓘(ℝ, E →L[ℝ] ℝ)).prod 𝓘(ℝ)) J Ψ (jetZero I q) w] = w.1.2 u

/-- The vertical first-order conditions on `Ψ : J¹Λ → M` at `(0_q, 0)` relative to `ι : Λ → M`
and a one-form `α` on `M`: the differential of `Ψ` sends `((0, p), c)` to a vector `v` with
`α(v) = c` and `dα(dι ·, v) = p`. -/
private def IsJetVerticalFirstOrder (ι : Λ → M) (α : SmoothForm J M ℝ 1)
    (Ψ : CotangentBundle I Λ × ℝ → M) (q : Λ) : Prop :=
  ∀ (p : TangentSpace I q →L[ℝ] ℝ) (c : ℝ),
    α.val (ι q) ![mfderiv ((I.prod 𝓘(ℝ, E →L[ℝ] ℝ)).prod 𝓘(ℝ)) J Ψ (jetZero I q)
      (((0 : E), (p : E →L[ℝ] ℝ)), c)] = c ∧
    ∀ u, mextDeriv α.val (ι q) ![mfderiv I J ι q u,
      mfderiv ((I.prod 𝓘(ℝ, E →L[ℝ] ℝ)).prod 𝓘(ℝ)) J Ψ (jetZero I q)
        (((0 : E), (p : E →L[ℝ] ℝ)), c)] = p u

omit [FiniteDimensional ℝ E] [I.Boundaryless] [J.Boundaryless] [T2Space M]
  [SecondCountableTopology M] in
/-- If the differential of `Ψ : J¹Λ → M` at `(0_q, 0)` sends `((u, 0), 0)` to `dι u` and
`((0, p), c)` to a vector `v` with `α(v) = c` and `dα(dι ·, v) = p`, then `Ψ` satisfies the
first-order conditions at `q`. -/
private theorem isJetFirstOrder_of_mfderiv {ι : Λ → M}
    (hι : IsLegendrianImmersion I α.kerDistribution ι) {Ψ : CotangentBundle I Λ × ℝ → M} {q : Λ}
    (hhor : ∀ u : TangentSpace I q, mfderiv ((I.prod 𝓘(ℝ, E →L[ℝ] ℝ)).prod 𝓘(ℝ)) J Ψ
        (jetZero I q) ((u, (0 : E →L[ℝ] ℝ)), (0 : ℝ)) = mfderiv I J ι q u)
    (hver : IsJetVerticalFirstOrder ι α Ψ q) :
    IsJetFirstOrder ι α Ψ q := by
  have hαι (u : TangentSpace I q) : α.val (ι q) ![mfderiv I J ι q u] = 0 :=
    SmoothForm.mem_kerDistribution.1
      (isHorizontalMap_iff_range_mfderiv_le.1 hι.isHorizontalMap q ⟨u, rfl⟩)
  -- The Legendrian immersion is isotropic for `dα`.
  have hdι (u u' : TangentSpace I q) :
      mextDeriv α.val (ι q) ![mfderiv I J ι q u, mfderiv I J ι q u'] = 0 := by
    have h0 := congrArg (fun φ : SmoothForm I Λ ℝ 2 ↦ φ.val q ![u, u'])
      (SmoothForm.mpullback_mextDerivₗ_eq_zero_of_isHorizontalMap hι.isImmersion.contMDiff
        hι.isHorizontalMap)
    simp only [SmoothForm.coe_mpullback, TauCeti.mpullback_apply_pair, mextDerivₗ_apply] at h0
    rw [h0]
    simp
  -- All tangent spaces involved are model spaces, where the computation is linear algebra.
  exact ⟨hhor, firstOrder_linear (E := E) (F := F)
    (mfderiv ((I.prod 𝓘(ℝ, E →L[ℝ] ℝ)).prod 𝓘(ℝ)) J Ψ (jetZero I q)) (mfderiv I J ι q)
    (α.val (ι q)) (mextDeriv α.val (ι q)) hhor hαι hdι hver⟩

/-! ### Velocities along the zero section of `J¹Λ` -/

omit [FiniteDimensional ℝ E] [I.Boundaryless] in
/-- The line `t ↦ (t p, t c)` of `J¹Λ` through the zero vector at `q` has velocity
`((0, p), c)` at `t = 0`. -/
private theorem hasMFDerivAt_jetLine (q : Λ) (p : TangentSpace I q →L[ℝ] ℝ) (c : ℝ) :
    HasMFDerivAt 𝓘(ℝ) ((I.prod 𝓘(ℝ, E →L[ℝ] ℝ)).prod 𝓘(ℝ))
      (fun t : ℝ ↦ ((⟨q, t • p⟩ : CotangentBundle I Λ), t * c)) 0
      ((1 : ℝ →L[ℝ] ℝ).smulRight (((0 : E), (p : E →L[ℝ] ℝ)), c)) := by
  have hcoord : (trivializationAt (E →L[ℝ] ℝ) (fun x : Λ ↦ TangentSpace I x →L[ℝ] ℝ) q
      ⟨q, p⟩).2 = p :=
    (Trivialization.continuousLinearMapAt_apply_of_mem (R := ℝ) _
      (FiberBundle.mem_baseSet_trivializationAt (E →L[ℝ] ℝ)
        (fun x : Λ ↦ TangentSpace I x →L[ℝ] ℝ) q) p).symm.trans
      (CotangentBundle.continuousLinearMapAt_trivializationAt_self q p)
  have h1 := TotalSpace.hasMFDerivAt_smul_curve (IB := I)
    (⟨q, p⟩ : CotangentBundle I Λ) (hasDerivAt_id (0 : ℝ))
  simp only [hcoord] at h1
  have h2 : HasMFDerivAt 𝓘(ℝ) 𝓘(ℝ) (fun t : ℝ ↦ t * c) 0 ((1 : ℝ →L[ℝ] ℝ).smulRight c) := by
    exact (hasDerivAt_mul_const c).hasFDerivAt.hasMFDerivAt.congr_mfderiv
      (ContinuousLinearMap.smulRight_one_eq_toSpanSingleton (R₁ := ℝ) c).symm
  have h3 : ((1 : ℝ →L[ℝ] ℝ).smulRight ((0 : E), (1 : ℝ) • (p : E →L[ℝ] ℝ))).prod
      ((1 : ℝ →L[ℝ] ℝ).smulRight c) =
        (1 : ℝ →L[ℝ] ℝ).smulRight (((0 : E), (p : E →L[ℝ] ℝ)), c) := by
    ext <;> simp
  exact (h1.prodMk h2).congr_mfderiv h3

omit [FiniteDimensional ℝ E] [I.Boundaryless] in
/-- The differential of the zero section `q ↦ (0_q, 0)` of `J¹Λ` sends `u` to `((u, 0), 0)`. -/
private theorem hasMFDerivAt_jetZeroSection (q : Λ) :
    HasMFDerivAt I ((I.prod 𝓘(ℝ, E →L[ℝ] ℝ)).prod 𝓘(ℝ))
      (jetZero I) q ((ContinuousLinearMap.inl ℝ E (E →L[ℝ] ℝ)).prod 0) := by
  have h := ((contMDiff_zeroSection (IB := I) (𝕜 := ℝ) (F := E →L[ℝ] ℝ)
    (E := fun x : Λ ↦ TangentSpace I x →L[ℝ] ℝ) (n := ∞)).mdifferentiableAt
    (by simp) (x := q)).hasMFDerivAt
  rw [Bundle.mfderiv_zeroSection] at h
  exact h.prodMk (hasMFDerivAt_const (0 : ℝ) q)

/-! ### The tubular map of a Legendrian embedding -/

omit [I.Boundaryless] [SecondCountableTopology M] in
/-- Let `Ψ : J¹Λ → M` agree along the line `t ↦ (t p, t c)` through the zero vector at `q` with the
normal exponential along the line `t ↦ t v` of the normal space at `q`. Then the differential of
`Ψ` at `(0_q, 0)` sends `((0, p), c)` to the normal representative of `v`. -/
private theorem mfderiv_jetLine_eq_normalRepresentative
    [RiemannianBundle (fun y : M ↦ TangentSpace J y)]
    [IsContMDiffRiemannianBundle J ∞ F (fun y : M ↦ TangentSpace J y)]
    (ι : SmoothEmbedding I J ∞ Λ M) (hn : (∞ : ℕ∞ω) ≠ 0)
    (hdim : finrank ℝ ((E →L[ℝ] ℝ) × ℝ) = finrank ℝ F - finrank ℝ E)
    {Ψ : CotangentBundle I Λ × ℝ → M} {q : Λ} (p : TangentSpace I q →L[ℝ] ℝ) (c : ℝ)
    (v : ι.NormalSpace q hn)
    (hΨ : MDifferentiableAt ((I.prod 𝓘(ℝ, E →L[ℝ] ℝ)).prod 𝓘(ℝ)) J Ψ (jetZero I q))
    (hE : letI := ι.normalSpaceFiberBundle hn hdim
      MDifferentiableAt (I.prod 𝓘(ℝ, (E →L[ℝ] ℝ) × ℝ)) J (ι.normalExp (P := (E →L[ℝ] ℝ) × ℝ) hn)
        (zeroSection ((E →L[ℝ] ℝ) × ℝ) (fun x ↦ ι.NormalSpace x hn) q))
    (hline : letI := ι.normalSpaceFiberBundle hn hdim
      (Ψ ∘ fun t : ℝ ↦ ((⟨q, t • p⟩ : CotangentBundle I Λ), t * c)) =
        ι.normalExp (P := (E →L[ℝ] ℝ) × ℝ) hn ∘ fun t : ℝ ↦
          (⟨q, t • v⟩ : TotalSpace ((E →L[ℝ] ℝ) × ℝ) (fun x ↦ ι.NormalSpace x hn))) :
    mfderiv ((I.prod 𝓘(ℝ, E →L[ℝ] ℝ)).prod 𝓘(ℝ)) J Ψ (jetZero I q)
      (((0 : E), (p : E →L[ℝ] ℝ)), c) = ι.normalRepresentative q hn v := by
  let := ι.normalSpaceFiberBundle hn hdim
  let := ι.normalSpaceVectorBundle hn hdim
  have hγ := hasMFDerivAt_jetLine q p c
  have hγ0 : ((⟨q, (0 : ℝ) • p⟩ : CotangentBundle I Λ), (0 : ℝ) * c) = jetZero I q := by
    simp [zeroSection]
  have hℓ : MDifferentiableAt 𝓘(ℝ) (I.prod 𝓘(ℝ, (E →L[ℝ] ℝ) × ℝ))
      (fun t : ℝ ↦ (⟨q, t • v⟩ : TotalSpace ((E →L[ℝ] ℝ) × ℝ) (fun x ↦ ι.NormalSpace x hn))) 0 :=
    (TotalSpace.hasMFDerivAt_smul_curve (IB := I)
      (⟨q, v⟩ : TotalSpace ((E →L[ℝ] ℝ) × ℝ) (fun x ↦ ι.NormalSpace x hn))
      (hasDerivAt_id (0 : ℝ))).mdifferentiableAt
  have hℓ0 : (⟨q, (0 : ℝ) • v⟩ : TotalSpace ((E →L[ℝ] ℝ) × ℝ)
      (fun x ↦ ι.NormalSpace x hn)) = zeroSection _ (fun x ↦ ι.NormalSpace x hn) q := by
    simp [zeroSection]
  have hγ1 : mfderiv 𝓘(ℝ) ((I.prod 𝓘(ℝ, E →L[ℝ] ℝ)).prod 𝓘(ℝ))
      (fun t : ℝ ↦ ((⟨q, t • p⟩ : CotangentBundle I Λ), t * c)) 0 (1 : ℝ) =
        ((((0 : E), (p : E →L[ℝ] ℝ)), c) : (E × (E →L[ℝ] ℝ)) × ℝ) := by
    rw [hγ.mfderiv]
    exact one_smul ℝ _
  have h3 := ι.mfderiv_normalExp_zeroSection_apply (P := (E →L[ℝ] ℝ) × ℝ) hn
    (by norm_cast) hdim q 0 v
  rw [map_zero, zero_add] at h3
  -- The points `γ 0`, `ℓ 0` and the zero vectors agree only propositionally, so the chain rule
  -- along the two lines is applied in its form for propositionally equal points. All tangent
  -- spaces involved are the model space of `M`, so the steps below chain by transitivity.
  -- `dΨ((0, p), c) = d(Ψ ∘ γ)(1)`:
  have hΨγ : mfderiv ((I.prod 𝓘(ℝ, E →L[ℝ] ℝ)).prod 𝓘(ℝ)) J Ψ (jetZero I q)
      (((0 : E), (p : E →L[ℝ] ℝ)), c) =
        mfderiv 𝓘(ℝ) J (Ψ ∘ fun t : ℝ ↦ ((⟨q, t • p⟩ : CotangentBundle I Λ), t * c)) 0
          (1 : ℝ) := by
    rw [← hγ1]
    exact (mfderiv_comp_apply_of_eq (hg := hΨ) (hf := hγ.mdifferentiableAt) (hy := hγ0)
      (v := (1 : ℝ))).symm
  -- `d(Ψ ∘ γ)(1) = d(exp ∘ ℓ)(1)`:
  have hγℓ : mfderiv 𝓘(ℝ) J (Ψ ∘ fun t : ℝ ↦ ((⟨q, t • p⟩ : CotangentBundle I Λ), t * c)) 0
      (1 : ℝ) = mfderiv 𝓘(ℝ) J (ι.normalExp (P := (E →L[ℝ] ℝ) × ℝ) hn ∘ fun t : ℝ ↦
        (⟨q, t • v⟩ : TotalSpace ((E →L[ℝ] ℝ) × ℝ) (fun x ↦ ι.NormalSpace x hn))) 0 (1 : ℝ) := by
    rw [hline]
  -- `d(exp ∘ ℓ)(1) = d exp (0, v)`:
  have hℓexp : mfderiv 𝓘(ℝ) J (ι.normalExp (P := (E →L[ℝ] ℝ) × ℝ) hn ∘ fun t : ℝ ↦
      (⟨q, t • v⟩ : TotalSpace ((E →L[ℝ] ℝ) × ℝ) (fun x ↦ ι.NormalSpace x hn))) 0 (1 : ℝ) =
        mfderiv (I.prod 𝓘(ℝ, (E →L[ℝ] ℝ) × ℝ)) J (ι.normalExp hn)
          (zeroSection _ (fun x ↦ ι.NormalSpace x hn) q)
          ((Bundle.zeroSectionTangentEquiv (I := I) q).symm (0, v)) := by
    rw [Bundle.zeroSectionTangentEquiv_symm_inr]
    exact mfderiv_comp_apply_of_eq (hg := hE) (hf := hℓ) (hy := hℓ0) (v := (1 : ℝ))
  -- `d exp (0, v)` is the normal representative of `v`.
  exact hΨγ.trans (hγℓ.trans (hℓexp.trans h3))

omit [FiniteDimensional ℝ E] [I.Boundaryless] [FiniteDimensional ℝ F] [J.Boundaryless]
  [IsManifold J ∞ M] [T2Space M] [SecondCountableTopology M] in
/-- If `Ψ : J¹Λ → M` restricts to `ι` along the zero section, its differential at `(0_q, 0)`
sends `((u, 0), 0)` to `dι u`. -/
private theorem mfderiv_jetZeroSection_eq {ι : Λ → M} {Ψ : CotangentBundle I Λ × ℝ → M}
    (hval : ∀ q, Ψ (jetZero I q) = ι q) {q : Λ}
    (hΨ : MDifferentiableAt ((I.prod 𝓘(ℝ, E →L[ℝ] ℝ)).prod 𝓘(ℝ)) J Ψ (jetZero I q))
    (u : TangentSpace I q) :
    mfderiv ((I.prod 𝓘(ℝ, E →L[ℝ] ℝ)).prod 𝓘(ℝ)) J Ψ (jetZero I q)
      ((u, (0 : E →L[ℝ] ℝ)), (0 : ℝ)) = mfderiv I J ι q u := by
  have hz := hasMFDerivAt_jetZeroSection (I := I) q
  have e := mfderiv_comp_apply (x := q) (hg := hΨ) (hf := hz.mdifferentiableAt) (v := u)
  rw [show Ψ ∘ jetZero I = ι from funext hval, hz.mfderiv] at e
  exact e.symm

omit [FiniteDimensional ℝ E] [I.Boundaryless] [J.Boundaryless] [T2Space M]
  [SecondCountableTopology M] in
/-- A tangent vector at `ι q` representing the normal class that the Legendrian identification
sends to `(p, c)` has `α`-value `c` and pairs with `dι u` under `dα` to `p u`. -/
private theorem apply_normalRepresentative {ι : SmoothEmbedding I J ∞ Λ M}
    (hι : IsLegendrianImmersion I α.kerDistribution ι) (hn : (∞ : ℕ∞ω) ≠ 0)
    [RiemannianBundle (fun y : M ↦ TangentSpace J y)] {q : Λ}
    (p : TangentSpace I q →L[ℝ] ℝ) (c : ℝ) :
    α.val (ι q) ![ι.normalRepresentative q hn
        ((ι.normalSpaceEquivOfIsLegendrianImmersion hι hn q).symm (p, c))] = c ∧
      ∀ u, mextDeriv α.val (ι q) ![mfderiv I J ι q u, ι.normalRepresentative q hn
        ((ι.normalSpaceEquivOfIsLegendrianImmersion hι hn q).symm (p, c))] = p u := by
  have hN : ι.contactPairing α q (ι.normalRepresentative q hn
      ((ι.normalSpaceEquivOfIsLegendrianImmersion hι hn q).symm (p, c))) = (p, c) := by
    rw [← ι.normalSpaceEquivOfIsLegendrianImmersion_normalClass hι hn,
      normalClass_normalRepresentative, ContinuousLinearEquiv.apply_symm_apply]
  exact ⟨(contactPairing_apply_snd ι α q _).symm.trans (congrArg Prod.snd hN), fun u ↦
    (contactPairing_apply_fst_apply ι α q _ u).symm.trans (congrArg (fun x ↦ x.1 u) hN)⟩

/-- **First-order identification of a Legendrian neighbourhood.** For a Legendrian embedding
`ι : Λ → M` there is a partial diffeomorphism `Ψ` from `J¹Λ` to `M`, defined near the zero
section, with `Ψ(0_q, 0) = ι q`, which satisfies the first-order conditions at every `q`: its
differential at `(0_q, 0)` sends `((u, 0), 0)` to `dι u`, `Ψ^* α` evaluates a tangent vector `w` at
`(0_q, 0)` to `w₂`, and `dα(dι u, dΨ w) = w₁₂ u`. It is the normal exponential for an auxiliary
metric, read through the identification of the normal bundle with `T^* Λ × ℝ` by
`[v] ↦ (dα(dι ·, v), α(v))`. -/
private theorem exists_partialDiffeomorph_jet [Nonempty Λ] (ι : SmoothEmbedding I J ∞ Λ M)
    (hι : IsLegendrianImmersion I α.kerDistribution ι) :
    ∃ Ψ : PartialDiffeomorph ((I.prod 𝓘(ℝ, E →L[ℝ] ℝ)).prod 𝓘(ℝ)) J
        (CotangentBundle I Λ × ℝ) M ∞,
      (∀ q, jetZero I q ∈ Ψ.source) ∧ (∀ q, Ψ (jetZero I q) = ι q) ∧
        ∀ q, IsJetFirstOrder ι α Ψ q := by
  have hn : (∞ : ℕ∞ω) ≠ 0 := by simp
  have hm : (∞ : ℕ∞ω) + 1 ≤ ∞ := by norm_cast
  have : LocallyCompactSpace G := J.locallyCompactSpace
  have : LocallyCompactSpace M := ChartedSpace.locallyCompactSpace G M
  obtain ⟨gM⟩ := nonempty_contMDiffRiemannianMetric (IB := J) (n := ⊤) (F := F)
    (E := fun y : M ↦ TangentSpace J y)
  let : RiemannianBundle (fun y : M ↦ TangentSpace J y) := ⟨gM.toRiemannianMetric⟩
  have : IsContMDiffRiemannianBundle J ∞ F (fun y : M ↦ TangentSpace J y) :=
    Bundle.instIsContMDiffRiemannianBundle gM
  have hdim := finrank_prod_eq_sub_of_isLegendrianImmersion hι
  let := ι.normalSpaceFiberBundle hn hdim
  let := ι.normalSpaceVectorBundle hn hdim
  obtain ⟨Φ, hΦ0, -, -, -, hΦ⟩ := ι.exists_partialDiffeomorph_normalExp_subset hn hm
    (by norm_cast) hdim isOpen_univ (subset_univ _)
  -- `Ψ` is the normal exponential, read through `J¹Λ ≃ T^* Λ × ℝ ≃ ν(ι)`.
  set D := ι.normalBundleDiffeomorphOfIsLegendrianImmersion hι hn hm hm hdim with hD
  have hD0 (q : Λ) : D.symm (jetZero I q) = zeroSection _ (fun x ↦ ι.NormalSpace x hn) q := by
    rw [hD, normalBundleDiffeomorphOfIsLegendrianImmersion_symm_apply]
    exact congrArg (TotalSpace.mk' _ q) (map_zero _)
  set Ψ := D.symm.toPartialDiffeomorph.trans Φ with hΨ
  have hΨfun : ⇑Ψ = ι.normalExp hn ∘ D.symm := by
    rw [hΨ, PartialDiffeomorph.coe_trans, hΦ, Diffeomorph.coe_toPartialDiffeomorph]
  have hsrc (q : Λ) : jetZero I q ∈ Ψ.source := by
    rw [hΨ, PartialDiffeomorph.trans_source]
    exact ⟨by simp, by simpa [hD0] using hΦ0 q⟩
  have hval (q : Λ) : Ψ (jetZero I q) = ι q := by
    rw [hΨfun, Function.comp_apply, hD0, normalExp_zeroSection]
  -- Along a vertical line, `Ψ` is the normal exponential along a line of a normal space.
  have hver (q : Λ) : IsJetVerticalFirstOrder ι α Ψ q := by
    intro p c
    set v := (ι.normalSpaceEquivOfIsLegendrianImmersion hι hn q).symm (p, c) with hv
    have key := mfderiv_jetLine_eq_normalRepresentative ι hn hdim p c v
      (Ψ.mdifferentiableAt hn (hsrc q)) (hΦ ▸ Φ.mdifferentiableAt hn (hΦ0 q)) (by
        funext t
        simp only [hΨfun, Function.comp_apply, hD,
          normalBundleDiffeomorphOfIsLegendrianImmersion_symm_apply, hv, ← map_smul, Prod.smul_mk,
          smul_eq_mul])
    rw [key, hv]
    exact apply_normalRepresentative hι hn p c
  have hhor (q : Λ) := mfderiv_jetZeroSection_eq hval (Ψ.mdifferentiableAt hn (hsrc q))
  exact ⟨Ψ, hsrc, hval, fun q ↦ isJetFirstOrder_of_mfderiv hι (hhor q) (hver q)⟩

/-! ### Contactness of the interpolation along the zero section -/

omit [FiniteDimensional ℝ E] [I.Boundaryless] in
/-- On an open set `W` of `J¹Λ`, the form `dz - λ` evaluates a tangent vector at `(0_q, 0)` to its
`z`-component, and its exterior derivative there is the canonical symplectic form. -/
private theorem contactization_subtypeVal_zeroSection
    {W : TopologicalSpace.Opens (CotangentBundle I Λ × ℝ)} {q : Λ}
    (hq : jetZero I q ∈ W) :
    (∀ v : TangentSpace ((I.prod 𝓘(ℝ, E →L[ℝ] ℝ)).prod 𝓘(ℝ)) (⟨_, hq⟩ : W),
      (SmoothForm.mpullback (Subtype.val : W → _) contMDiff_subtypeVal
        (CotangentBundle.liouvilleForm I Λ).contactization).val ⟨_, hq⟩ ![v] = v.2) ∧
    ∀ v w : TangentSpace ((I.prod 𝓘(ℝ, E →L[ℝ] ℝ)).prod 𝓘(ℝ)) (⟨_, hq⟩ : W),
      mextDeriv (SmoothForm.mpullback (Subtype.val : W → _) contMDiff_subtypeVal
        (CotangentBundle.liouvilleForm I Λ).contactization).val ⟨_, hq⟩ ![v, w] =
        w.1.2 v.1.1 - v.1.2 w.1.1 := by
  refine ⟨fun v ↦ ?_, fun v w ↦ ?_⟩
  · rw [SmoothForm.coe_mpullback_subtype_val_apply]
    exact CotangentBundle.contactization_liouvilleForm_apply_zeroSection q 0 v
  · rw [SmoothForm.mextDeriv_mpullback_apply_two, Manifold.mfderiv_subtype_val,
      ContinuousLinearEquiv.coe_coe, Manifold.tangentSpaceOpenEquiv_apply,
      Manifold.tangentSpaceOpenEquiv_apply]
    exact CotangentBundle.mextDeriv_contactization_liouvilleForm_apply _ v w

omit [FiniteDimensional ℝ E] [I.Boundaryless] [FiniteDimensional ℝ F] [J.Boundaryless]
  [T2Space M] [SecondCountableTopology M] in
/-- At a point `(0_q, 0)` of an open set `W` of `J¹Λ`, let `Ψ` satisfy the first-order conditions
at `q`. Then `(Ψ|_W)^* α` and `(dz - λ)|_W` agree at `(0_q, 0)`, and every
interpolation between them is contact there: the tangent space of the zero section is a
coisotropic subspace of `ker (dz - λ)` along which the two exterior derivatives agree. -/
private theorem isContactFormAt_jet {ι : Λ → M} {Ψ : CotangentBundle I Λ × ℝ → M} {q : Λ}
    (hval : Ψ (jetZero I q) = ι q) (hfo : IsJetFirstOrder ι α Ψ q)
    {W : TopologicalSpace.Opens (CotangentBundle I Λ × ℝ)}
    (hΨW : ContMDiff ((I.prod 𝓘(ℝ, E →L[ℝ] ℝ)).prod 𝓘(ℝ)) J ∞ (Ψ ∘ (Subtype.val : W → _)))
    (hq : jetZero I q ∈ W) :
    let α₀ := SmoothForm.mpullback (Subtype.val : W → _) contMDiff_subtypeVal
      (CotangentBundle.liouvilleForm I Λ).contactization
    (SmoothForm.mpullback _ hΨW α).val ⟨_, hq⟩ = α₀.val ⟨_, hq⟩ ∧ ∀ u ∈ Icc (0 : ℝ) 1,
      IsContactFormAt (α₀ + u • (SmoothForm.mpullback _ hΨW α - α₀)).val ⟨_, hq⟩ := by
  intro α₀
  obtain ⟨h₀, hd₀⟩ := contactization_subtypeVal_zeroSection hq
  have hvalW : (SmoothForm.mpullback _ hΨW α).val ⟨_, hq⟩ = α₀.val ⟨_, hq⟩ := by
    refine ContinuousAlternatingMap.ext fun v ↦ ?_
    rw [show v = ![v 0] from funext fun i ↦ by fin_cases i; rfl,
      SmoothForm.mpullback_comp_subtypeVal_apply, h₀, ← (hfo.2 (v 0)).1, ← hval]
    exact congrArg (α.val _) (funext fun i ↦ by fin_cases i; simp)
  -- The tangent space `{((u, 0), 0)}` of the zero section is the kernel of `w ↦ (w₁₂, w₂)`.
  set L : (E × (E →L[ℝ] ℝ)) × ℝ →ₗ[ℝ] (E →L[ℝ] ℝ) × ℝ :=
    ((LinearMap.snd ℝ E (E →L[ℝ] ℝ)).comp (LinearMap.fst ℝ (E × (E →L[ℝ] ℝ)) ℝ)).prod
      (LinearMap.snd ℝ (E × (E →L[ℝ] ℝ)) ℝ) with hL
  have hmemL (w : (E × (E →L[ℝ] ℝ)) × ℝ) : w ∈ LinearMap.ker L ↔ w.1.2 = 0 ∧ w.2 = 0 := by
    simp [hL]
  refine ⟨hvalW, fun u _ ↦ SmoothForm.isContactFormAt_add_smul_sub_of_mextDeriv_eq_on
    (W := LinearMap.ker L) ((SmoothForm.isContactFormAt_mpullback_subtype_val_iff _ _).2
      ((SmoothForm.isContactForm_iff_forall_isContactFormAt.1
        CotangentBundle.isContactForm_contactization_liouvilleForm) _))
    hvalW (fun w hw ↦ ?_) (fun v hv hvw ↦ ?_) (fun w hw v _ ↦ ?_) u⟩
  · exact RoughForm.mem_ker.2 ((h₀ w).trans ((hmemL w).1 hw).2)
  · -- A vector of `ker (dz - λ)` orthogonal to the zero section is tangent to it.
    refine (hmemL v).2 ⟨ContinuousLinearMap.ext fun u' ↦ ?_,
      (h₀ v).symm.trans (RoughForm.mem_ker.1 hv)⟩
    have h' := (hd₀ ((u', 0), 0) v).symm.trans (hvw ((u', 0), 0) ((hmemL _).2 ⟨rfl, rfl⟩))
    simpa using h'
  · -- On pairs with a vector tangent to the zero section, both derivatives are `w₁₂ u`.
    obtain ⟨⟨u', p⟩, c⟩ := w
    obtain ⟨rfl, rfl⟩ := (hmemL _).1 hw
    have hmid : mextDeriv α.val (Ψ (jetZero I q))
        ![mfderiv ((I.prod 𝓘(ℝ, E →L[ℝ] ℝ)).prod 𝓘(ℝ)) J Ψ (jetZero I q)
            ((u', (0 : E →L[ℝ] ℝ)), (0 : ℝ)),
          mfderiv ((I.prod 𝓘(ℝ, E →L[ℝ] ℝ)).prod 𝓘(ℝ)) J Ψ (jetZero I q) v] =
        v.1.2 u' - (0 : E →L[ℝ] ℝ) v.1.1 := by
      rw [hval]
      refine (congrArg (fun a ↦ mextDeriv α.val (ι q)
        ![a, mfderiv ((I.prod 𝓘(ℝ, E →L[ℝ] ℝ)).prod 𝓘(ℝ)) J Ψ (jetZero I q) v])
        (hfo.1 u')).trans (((hfo.2 v).2 u').trans ?_)
      rw [zero_apply, sub_zero]
    rw [SmoothForm.mextDeriv_mpullback_comp_subtypeVal_apply]
    refine (congrArg (mextDeriv α.val _) (funext fun i ↦ ?_)).trans
      (hmid.trans (hd₀ ((u', 0), 0) v).symm)
    fin_cases i <;> simp

/-! ### The strict Moser correction -/

omit [FiniteDimensional ℝ F] [J.Boundaryless] [T2Space M] [SecondCountableTopology M] in
/-- On an open set `W` of `J¹Λ`, a one-form `α₁` agreeing with `dz - λ` along the zero section,
such that every interpolation between them is contact there, is pulled back to `dz - λ` by a
partial diffeomorphism of `W` fixing the zero section. The slice `z = 0` contains the zero
section, and `dz` vanishes on it and equals `dz - λ` along the zero section. -/
private theorem exists_partialDiffeomorph_opens_zeroSection [T2Space Λ] [SigmaCompactSpace Λ]
    (W : TopologicalSpace.Opens (CotangentBundle I Λ × ℝ))
    {α₁ : SmoothForm ((I.prod 𝓘(ℝ, E →L[ℝ] ℝ)).prod 𝓘(ℝ)) W ℝ 1}
    (hvc : ∀ y ∈ Subtype.val ⁻¹' range (jetZero I),
      α₁.val y = (SmoothForm.mpullback (Subtype.val : W → _) contMDiff_subtypeVal
        (CotangentBundle.liouvilleForm I Λ).contactization).val y ∧
      ∀ u ∈ Icc (0 : ℝ) 1, IsContactFormAt ((SmoothForm.mpullback (Subtype.val : W → _)
        contMDiff_subtypeVal (CotangentBundle.liouvilleForm I Λ).contactization) +
        u • (α₁ - SmoothForm.mpullback (Subtype.val : W → _) contMDiff_subtypeVal
          (CotangentBundle.liouvilleForm I Λ).contactization)).val y) :
    ∃ φ : PartialDiffeomorph ((I.prod 𝓘(ℝ, E →L[ℝ] ℝ)).prod 𝓘(ℝ))
        ((I.prod 𝓘(ℝ, E →L[ℝ] ℝ)).prod 𝓘(ℝ)) W W ∞,
      Subtype.val ⁻¹' range (jetZero I) ⊆ φ.source ∧
      Subtype.val ⁻¹' range (jetZero I) ⊆ φ.target ∧
      (∀ y ∈ Subtype.val ⁻¹' range (jetZero I), φ y = y) ∧
      ∀ y ∈ φ.source, TauCeti.mpullback _ _ φ α₁.val y =
        (SmoothForm.mpullback (Subtype.val : W → _) contMDiff_subtypeVal
          (CotangentBundle.liouvilleForm I Λ).contactization).val y := by
  have := Manifold.sigmaCompactSpace_opens ((I.prod 𝓘(ℝ, E →L[ℝ] ℝ)).prod 𝓘(ℝ)) W
  -- The slice `z = 0`, read in `W`.
  set σ : CotangentBundle I Λ → CotangentBundle I Λ × ℝ := fun z ↦ (z, 0) with hσdef
  have hσ : ContMDiff (I.prod 𝓘(ℝ, E →L[ℝ] ℝ)) ((I.prod 𝓘(ℝ, E →L[ℝ] ℝ)).prod 𝓘(ℝ)) ∞ σ :=
    contMDiff_id.prodMk contMDiff_const
  have hdσ (z : CotangentBundle I Λ) : HasMFDerivAt (I.prod 𝓘(ℝ, E →L[ℝ] ℝ))
      ((I.prod 𝓘(ℝ, E →L[ℝ] ℝ)).prod 𝓘(ℝ)) σ z
      ((ContinuousLinearMap.id ℝ (E × (E →L[ℝ] ℝ))).prod 0) :=
    (hasMFDerivAt_id z).prodMk (hasMFDerivAt_const (0 : ℝ) z)
  set S : TopologicalSpace.Opens (CotangentBundle I Λ) :=
    ⟨σ ⁻¹' W, W.isOpen.preimage hσ.continuous⟩
  set σW : S → W := (W : Set (CotangentBundle I Λ × ℝ)).restrictPreimage σ with hσW
  have hσind : Topology.IsInducing σ :=
    Topology.IsInducing.id.of_comp (Continuous.prodMk_left 0) continuous_fst
  have hσWclosed : IsClosed (range σW) := by
    rw [hσW, range_restrictPreimage]
    refine IsClosed.preimage continuous_subtypeVal ?_
    rw [show range σ = univ ×ˢ {0} by ext x; simp [hσdef, Prod.ext_iff, eq_comm]]
    exact isClosed_univ.prod isClosed_singleton
  -- The one-form `dz`, read in `W`.
  set β := SmoothForm.mpullback (Subtype.val : W → _) contMDiff_subtypeVal
    (SmoothForm.mpullback Prod.snd contMDiff_snd SmoothForm.realLineCoordForm :
      SmoothForm ((I.prod 𝓘(ℝ, E →L[ℝ] ℝ)).prod 𝓘(ℝ)) (CotangentBundle I Λ × ℝ) ℝ 1) with hβ
  have hβ' (y : W) (v : TangentSpace ((I.prod 𝓘(ℝ, E →L[ℝ] ℝ)).prod 𝓘(ℝ)) y) :
      β.val y ![v] = v.2 := by
    rw [hβ, SmoothForm.coe_mpullback_subtype_val_apply]
    refine (SmoothForm.mpullback_snd_apply SmoothForm.realLineCoordForm
      (y : CotangentBundle I Λ × ℝ) ![v]).trans ?_
    rw [SmoothForm.realLineCoordForm_apply, Manifold.tangentSpaceProdEquiv_apply]
    exact congrArg Prod.snd (Matrix.cons_val_zero (α := (E × (E →L[ℝ] ℝ)) × ℝ) v ![])
  refine
    SmoothForm.exists_partialDiffeomorph_mpullback_eq_of_isContactFormAt_of_apply_mfderiv_eq_zero
    (β := β) (fun y hy ↦ (hvc y hy).2) (fun y hy ↦ (hvc y hy).1) (hσ.restrictPreimage W)
    (fun s ↦ ?_) (hσind.restrictPreimage W) hσWclosed
    (by rw [Module.finrank_prod (R := ℝ) (M := E × (E →L[ℝ] ℝ)) (M' := ℝ), Module.finrank_self])
    ?_ (fun s w ↦ ?_) ?_
  · rw [Manifold.injective_mfderiv_restrictPreimage_iff hσ.continuous W, (hdσ s).mfderiv]
    exact fun a b h ↦ congrArg Prod.fst h
  · rintro ⟨x, hx⟩ ⟨q, rfl⟩
    exact ⟨⟨zeroSection _ _ q, hx⟩, rfl⟩
  · rw [hβ', Manifold.mfderiv_restrictPreimage_apply hσ.continuous W, (hdσ s).mfderiv]
    -- The tangent spaces are model spaces, where `(id.prod 0) w` has second component `0`.
    exact (by simp : ∀ x : E × (E →L[ℝ] ℝ), ((ContinuousLinearMap.id ℝ _).prod
      (0 : E × (E →L[ℝ] ℝ) →L[ℝ] ℝ) x).2 = 0) w
  · rintro ⟨x, hx⟩ ⟨q, rfl⟩
    refine ContinuousAlternatingMap.ext fun v ↦ ?_
    rw [show v = ![v 0] from funext fun i ↦ by fin_cases i; rfl, hβ',
      SmoothForm.coe_mpullback_subtype_val_apply]
    exact (CotangentBundle.contactization_liouvilleForm_apply_zeroSection q 0 (v 0)).symm

omit [FiniteDimensional ℝ E] [I.Boundaryless] [FiniteDimensional ℝ F] [J.Boundaryless]
  [T2Space M] [SecondCountableTopology M] in
/-- Let `Ψ` be a partial diffeomorphism from `J¹Λ` to `M` and `φ` one of its source `W` fixing a set
`K`, with `φ^* (Ψ|_W)^* α = (dz - λ)|_W` on the source of `φ`. Then `φ` followed by `Ψ` is a
partial diffeomorphism from `J¹Λ` to `M`, defined near `K` and equal to `Ψ` there, which pulls
`α` back to `dz - λ` on its source. -/
private theorem exists_partialDiffeomorph_trans_opens
    (Ψ : PartialDiffeomorph ((I.prod 𝓘(ℝ, E →L[ℝ] ℝ)).prod 𝓘(ℝ)) J
      (CotangentBundle I Λ × ℝ) M ∞)
    (hΨW : ContMDiff ((I.prod 𝓘(ℝ, E →L[ℝ] ℝ)).prod 𝓘(ℝ)) J ∞
      (Ψ ∘ (Subtype.val : (⟨Ψ.source, Ψ.open_source⟩ :
        TopologicalSpace.Opens (CotangentBundle I Λ × ℝ)) → _)))
    {K : Set (CotangentBundle I Λ × ℝ)} (hK : K ⊆ Ψ.source)
    (φ : PartialDiffeomorph ((I.prod 𝓘(ℝ, E →L[ℝ] ℝ)).prod 𝓘(ℝ))
      ((I.prod 𝓘(ℝ, E →L[ℝ] ℝ)).prod 𝓘(ℝ)) (⟨Ψ.source, Ψ.open_source⟩ :
        TopologicalSpace.Opens (CotangentBundle I Λ × ℝ)) (⟨Ψ.source, Ψ.open_source⟩ :
        TopologicalSpace.Opens (CotangentBundle I Λ × ℝ)) ∞)
    (hφs : Subtype.val ⁻¹' K ⊆ φ.source) (hφt : Subtype.val ⁻¹' K ⊆ φ.target)
    (hφfix : ∀ y ∈ Subtype.val ⁻¹' K, φ y = y)
    (hφ : ∀ y ∈ φ.source, TauCeti.mpullback _ _ φ (SmoothForm.mpullback _ hΨW α).val y =
      (SmoothForm.mpullback Subtype.val contMDiff_subtypeVal
        (CotangentBundle.liouvilleForm I Λ).contactization).val y) :
    ∃ F : PartialDiffeomorph ((I.prod 𝓘(ℝ, E →L[ℝ] ℝ)).prod 𝓘(ℝ)) J
        (CotangentBundle I Λ × ℝ) M ∞,
      K ⊆ F.source ∧ (∀ x ∈ K, F x = Ψ x) ∧ ∀ x ∈ F.source, TauCeti.mpullback _ J F α.val x =
        (CotangentBundle.liouvilleForm I Λ).contactization.val x := by
  have hn : (∞ : ℕ∞ω) ≠ 0 := by simp
  obtain ⟨Φ, hΦs, -, hΦfix, hΦ⟩ :=
    exists_partialDiffeomorph_mpullback_apply_eq_of_opens hn hK φ hφs hφt hφfix
  refine ⟨Φ.trans Ψ, fun x hx ↦ ?_, fun x hx ↦ ?_, fun x hx ↦ ?_⟩
  · rw [PartialDiffeomorph.trans_source]
    exact ⟨hΦs hx, by rw [mem_preimage, hΦfix x hx]; exact hK hx⟩
  · rw [PartialDiffeomorph.coe_trans, Function.comp_apply, hΦfix x hx]
  rw [PartialDiffeomorph.trans_source] at hx
  rw [PartialDiffeomorph.coe_trans,
    mpullback_comp_at (Φ.mdifferentiableAt hn hx.1) (Ψ.mdifferentiableAt hn hx.2)]
  obtain ⟨y, hy, rfl, hyΦ⟩ := hΦ x hx.1
  rw [hyΦ]
  -- On the source of `Ψ`, `(Ψ|_W)^* α` is `Ψ^* α` read on `W`.
  have hpt : TauCeti.mpullback ((I.prod 𝓘(ℝ, E →L[ℝ] ℝ)).prod 𝓘(ℝ))
      ((I.prod 𝓘(ℝ, E →L[ℝ] ℝ)).prod 𝓘(ℝ)) Subtype.val
      (TauCeti.mpullback ((I.prod 𝓘(ℝ, E →L[ℝ] ℝ)).prod 𝓘(ℝ)) J Ψ α.val) (φ y) =
        (SmoothForm.mpullback _ hΨW α).val (φ y) := by
    rw [SmoothForm.coe_mpullback, mpullback_comp_at
      (contMDiff_subtypeVal.mdifferentiableAt one_ne_zero)
      (Ψ.mdifferentiableAt hn (φ y).property)]
  rw [← SmoothForm.coe_mpullback_subtype_val_apply, ← hφ y hy]
  refine ContinuousAlternatingMap.ext fun v ↦ ?_
  rw [TauCeti.mpullback_apply φ, TauCeti.mpullback_apply φ, hpt]

/-! ### The neighbourhood theorem -/

/-- **The strict Legendrian neighbourhood theorem.** Let `α` be a contact form on a manifold `M`
and `ι : Λ → M` a smooth embedding of a nonempty manifold which is Legendrian for `ker α`. Then
there is a partial diffeomorphism `φ` from the one-jet space `J¹Λ = T^* Λ × ℝ` to `M`, whose source
contains the zero section, with `φ(0_q, 0) = ι q` for every `q` and `φ^* α = dz - λ` on its
source, where `λ` is the Liouville form of `T^* Λ`. Its source and target are open
neighbourhoods of the zero section and of `ι(Λ)`. Neither compactness of `Λ` nor closedness of
`ι(Λ)` is needed. -/
theorem exists_partialDiffeomorph_mpullback_eq_contactization [Nonempty Λ]
    (ι : SmoothEmbedding I J ∞ Λ M) (hι : IsLegendrianImmersion I α.kerDistribution ι) :
    ∃ φ : PartialDiffeomorph ((I.prod 𝓘(ℝ, E →L[ℝ] ℝ)).prod 𝓘(ℝ)) J
        (CotangentBundle I Λ × ℝ) M ∞,
      (∀ q, (zeroSection (E →L[ℝ] ℝ) (fun x : Λ ↦ TangentSpace I x →L[ℝ] ℝ) q, (0 : ℝ)) ∈
        φ.source) ∧
      (∀ q, φ (zeroSection (E →L[ℝ] ℝ) (fun x : Λ ↦ TangentSpace I x →L[ℝ] ℝ) q, 0) = ι q) ∧
      ∀ x ∈ φ.source, TauCeti.mpullback _ J φ α.val x =
        (CotangentBundle.liouvilleForm I Λ).contactization.val x := by
  obtain ⟨Ψ, hsrc, hval, hfo⟩ := exists_partialDiffeomorph_jet ι hι
  -- `Λ` is embedded in `M`, so it is a Hausdorff σ-compact manifold.
  have : T2Space Λ := ι.isEmbedding.t2Space
  have : SecondCountableTopology Λ := ι.isEmbedding.isInducing.secondCountableTopology
  have : LocallyCompactSpace H := I.locallyCompactSpace
  have : LocallyCompactSpace Λ := ChartedSpace.locallyCompactSpace H Λ
  have hΨW : ContMDiff ((I.prod 𝓘(ℝ, E →L[ℝ] ℝ)).prod 𝓘(ℝ)) J ∞
      (Ψ ∘ (Subtype.val : (⟨Ψ.source, Ψ.open_source⟩ :
        TopologicalSpace.Opens (CotangentBundle I Λ × ℝ)) → _)) :=
    Ψ.contMDiffOn_toFun.comp_contMDiff contMDiff_subtypeVal fun y ↦ y.property
  -- Along the zero section, `(Ψ|_W)^* α` agrees with `dz - λ` and the interpolation is contact.
  obtain ⟨φ, hφs, hφt, hφfix, hφ⟩ := exists_partialDiffeomorph_opens_zeroSection _ <| by
    rintro ⟨x, hx⟩ ⟨q, rfl⟩
    exact isContactFormAt_jet (hval q) (hfo q) hΨW hx
  obtain ⟨F, hFs, hFΨ, hF⟩ := exists_partialDiffeomorph_trans_opens Ψ hΨW
    (range_subset_iff.2 hsrc) φ hφs hφt hφfix hφ
  exact ⟨F, fun q ↦ hFs ⟨q, rfl⟩, fun q ↦ (hFΨ _ ⟨q, rfl⟩).trans (hval q), hF⟩

end TauCeti.SmoothEmbedding
