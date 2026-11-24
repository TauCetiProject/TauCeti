/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Contact.Flow
public import TauCeti.Geometry.Symplectic.Hamiltonian.AlmostExistence
public import TauCeti.Geometry.Symplectic.Hamiltonian.Reeb.Basic
import Mathlib.Geometry.Manifold.IntegralCurve.ExistUnique
import TauCeti.Analysis.Calculus.IntervalIntegral.Periodic
import TauCeti.Geometry.Manifold.IntegralCurve.Basic
import TauCeti.Geometry.Manifold.IntegralCurve.Reparam
import TauCeti.Topology.Homotopy.AddCircle

/-!
# Closed Reeb orbits are closed characteristics

Let `σ` be a nondegenerate two-form on a finite-dimensional manifold `M` and `θ` a one-form with
`dθ = -σ`, and let `ι : S → M` be a hypersurface on which a function `K` takes the value `c`, in
the sense that the tangent image of `ι` at each point is the kernel of `dK`. If the restriction
`ι^* θ` is a contact form, its Reeb field `R` is carried by `dι` to the rescaled Hamiltonian field
`X_K / θ(X_K)` (`TauCeti.SmoothTwoForm.IsNondegenerate.mfderiv_reebVectorField_mpullback`), where
`θ(X_K)` vanishes nowhere along `ι`. So the closed orbits of the Reeb flow of `ι^* θ` and the closed
characteristics of the level `K⁻¹(c)` are the same loops, traced at different speeds.

This file proves this correspondence for closed characteristics in the sense of
`TauCeti.SmoothTwoForm.HasContractibleClosedCharacteristic`, keeping track of contractibility in a
set `W`:

* a periodic Reeb orbit whose loop through `ι` is contractible in a set `W` is, after a change of
  time, a closed characteristic of `K⁻¹(c)` contractible in `W`
  (`IsNondegenerate.hasContractibleClosedCharacteristic_of_reebVectorField`);
* conversely, when `S` is compact, `ι` is injective and the level `K⁻¹(c)` is the image of `ι`,
  every closed characteristic of the level contractible in `W` is traced by a periodic Reeb orbit
  whose loop through `ι` is contractible in `W`
  (`IsNondegenerate.hasContractibleClosedCharacteristic_iff_exists_reebVectorField`).

The change of time has speed `θ(X_K)` along the orbit, which has a constant sign on it. When the
sign is negative, replacing `K` by `-K` reverses the Hamiltonian field and makes it positive. For
the converse, the Reeb orbit through a point of the closed characteristic is pushed to the level and
reparametrized there into an orbit of `X_K`, which by uniqueness of integral curves is the closed
characteristic itself; injectivity of `ι` then makes the Reeb orbit periodic. In both directions
the loop of one curve over a period is a reparametrization of the loop of the other, so one is
contractible exactly when the other is (`Function.Periodic.exists_nullhomotopic_comp_iff`).

This is how existence statements for closed characteristics, such as those produced by almost
existence on a hypersurface of contact type, become statements about closed Reeb orbits, and back.

## Main results

All in the namespace `TauCeti.SmoothTwoForm`:

* `IsNondegenerate.hasContractibleClosedCharacteristic_of_reebVectorField`: a contractible closed
  Reeb orbit gives a contractible closed characteristic.
* `IsNondegenerate.hasContractibleClosedCharacteristic_iff_exists_reebVectorField`: on a compact
  embedded level, contractible closed characteristics are contractible closed Reeb orbits.

## References

* H. Hofer, E. Zehnder, *Symplectic Invariants and Hamiltonian Dynamics*, Birkhäuser, 1994,
  Sections 1.1 and 4.2 (closed characteristics of hypersurfaces of contact type).
* D. McDuff, D. Salamon, *Introduction to Symplectic Topology*, 3rd ed., Oxford, 2017,
  Section 3.5 (hypersurfaces of contact type and their characteristic line fields).
* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Floer homology with DG coefficients.
  Applications to cotangent bundles*, arXiv:2404.07953, the proof of Corollary E.
-/

public section

open Function Set
open scoped ContDiff Manifold

namespace TauCeti

namespace SmoothTwoForm

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M]
  {E' H' S : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
  [TopologicalSpace H'] {J : ModelWithCorners ℝ E' H'} [TopologicalSpace S] [ChartedSpace H' S]
  {σ : SmoothTwoForm I M} {θ : SmoothForm I M ℝ 1} {ι : S → M} {K : M → ℝ} {c : ℝ} {W : Set M}

/-- The speed `θ(X_K)` is continuous when `K` is `C¹`. -/
private theorem continuous_apply_hamiltonianVectorField (hσ : σ.IsNondegenerate)
    (hKs : ContMDiff I 𝓘(ℝ) 1 K) :
    Continuous fun x ↦ θ.val x ![σ.hamiltonianVectorField K x] :=
  (θ.contMDiff_apply_vectorField (n := 0)
    (hσ.contMDiff_hamiltonianVectorField (n := 0) (by simp) (by simpa using hKs))).continuous

omit [FiniteDimensional ℝ E] [IsManifold I ∞ M] in
/-- Along a hypersurface where `dK` vanishes, so does `d(-K)`. -/
private theorem range_mfderiv_eq_ker_mvfderiv_neg
    (hK : ∀ s, (mfderiv J I ι s).range = (mvfderiv I K (ι s)).ker) (s : S) :
    (mfderiv J I ι s).range = (mvfderiv I (-K) (ι s)).ker := by
  rw [hK, mvfderiv_neg]
  ext v
  simp

omit [FiniteDimensional ℝ E] in
/-- The speed of `-K` is the opposite of the speed of `K`. -/
private theorem apply_hamiltonianVectorField_neg (x : M) :
    θ.val x ![σ.hamiltonianVectorField (-K) x] = -θ.val x ![σ.hamiltonianVectorField K x] := by
  rw [hamiltonianVectorField_neg, ← SmoothForm.degreeOneEquiv_coe_apply, map_neg,
    SmoothForm.degreeOneEquiv_coe_apply]

section ReebToCharacteristic

variable [IsManifold J 2 S]

/-- Along the hypersurface `ι`, a Reeb trajectory of `ι^* θ` is mapped by `ι` to a trajectory of
the rescaled Hamiltonian field `X_K / θ(X_K)`. -/
private theorem isMIntegralCurve_comp_reebVectorField (hσ : σ.IsNondegenerate)
    (hι : ContMDiff J I ∞ ι) (hα : (SmoothForm.mpullback ι hι θ).IsContactForm)
    (hdθ : ∀ s, mextDeriv θ.val (ι s) = -σ.val (ι s))
    (hK : ∀ s, (mfderiv J I ι s).range = (mvfderiv I K (ι s)).ker) {γ : ℝ → S}
    (hγ : IsMIntegralCurve γ (SmoothForm.mpullback ι hι θ).reebVectorField) :
    IsMIntegralCurve (ι ∘ γ) fun x ↦
      (θ.val x ![σ.hamiltonianVectorField K x])⁻¹ • σ.hamiltonianVectorField K x := by
  rw [isMIntegralCurve_iff_isMIntegralCurveOn] at hγ ⊢
  exact hγ.map_of_mfderiv_eq (fun t _ ↦ (hι _).mdifferentiableAt (by simp))
    fun t _ ↦ hσ.mfderiv_reebVectorField_mpullback hι hα (hdθ _) (hK _)

/-- The case of `hasContractibleClosedCharacteristic_of_reebVectorField` where the speed
`θ(X_K)` is positive along the orbit: the inverse of `t ↦ ∫₀ᵗ 1 / θ(X_K)` turns the orbit into a
closed characteristic. -/
private theorem hasContractibleClosedCharacteristic_of_reebVectorField_of_pos
    (hσ : σ.IsNondegenerate) (hι : ContMDiff J I ∞ ι)
    (hα : (SmoothForm.mpullback ι hι θ).IsContactForm)
    (hdθ : ∀ s, mextDeriv θ.val (ι s) = -σ.val (ι s)) (hKs : ContMDiff I 𝓘(ℝ) 1 K)
    (hK : ∀ s, (mfderiv J I ι s).range = (mvfderiv I K (ι s)).ker) (hKι : ∀ s, K (ι s) = c)
    {γ : ℝ → S} (hγ : IsMIntegralCurve γ (SmoothForm.mpullback ι hι θ).reebVectorField)
    {P : ℝ} (hP : 0 < P) (hper : Periodic γ P)
    (hg : ∃ g : C(AddCircle P, W), g.Nullhomotopic ∧ ∀ t : ℝ, (g t : M) = ι (γ t))
    (hpos : 0 < θ.val (ι (γ 0)) ![σ.hamiltonianVectorField K (ι (γ 0))]) :
    σ.HasContractibleClosedCharacteristic W K c := by
  set X := σ.hamiltonianVectorField K
  -- The speed of the change of time.
  set h : ℝ → ℝ := fun t ↦ θ.val (ι (γ t)) ![X (ι (γ t))]
  have hcont : Continuous h :=
    (continuous_apply_hamiltonianVectorField hσ hKs).comp (hι.continuous.comp hγ.continuous)
  have hne (t : ℝ) : h t ≠ 0 := hσ.apply_hamiltonianVectorField_ne_zero hι hα (hdθ _) (hK _)
  -- It vanishes nowhere, so it keeps its sign at `0`.
  have hhpos (t : ℝ) : 0 < h t := sign_eq_one_iff.1 <| (isPreconnected_univ.sign_eq_of_continuousOn
    hcont.continuousOn (fun t _ ↦ hne t) trivial trivial).trans (sign_pos hpos)
  have hhP : Periodic h P := fun t ↦ congrArg (fun s ↦ θ.val (ι s) ![X (ι s)]) (hper t)
  obtain ⟨ψ, hψ0, ⟨T, -, hψT⟩, hψd⟩ := hhP.exists_homeomorph_hasDerivAt_of_pos hP hcont hhpos
  have hψmono : StrictMono ψ := strictMono_of_hasDerivAt_pos hψd fun s ↦ hhpos _
  have hψT₀ : ψ T = P := by simpa [hψ0] using hψT 0
  have hT : 0 < T := hψmono.lt_iff_lt.1 (by rw [hψT₀, hψ0]; exact hP)
  -- `ι ∘ γ ∘ ψ` is an orbit of `X_K`.
  have hδ : IsMIntegralCurve (ι ∘ γ ∘ ψ) X :=
    (isMIntegralCurve_comp_reebVectorField hσ hι hα hdθ hK hγ).comp_of_hasDerivAt
      (fun t ↦ (smul_inv_smul₀ (hne t) _).symm) hψd
  have hδper : Periodic (ι ∘ γ ∘ ψ) T := fun s ↦ by simp only [comp_apply, hψT s, hper _]
  -- It is not constant, since `X_K` does not vanish at `ι (γ 0)`.
  have hnc : ∃ t, (ι ∘ γ ∘ ψ) t ≠ (ι ∘ γ ∘ ψ) 0 := by
    by_contra! hc
    rw [show ι ∘ γ ∘ ψ = fun _ ↦ (ι ∘ γ ∘ ψ) 0 from funext hc, isMIntegralCurve_const_iff,
      comp_apply, comp_apply, hψ0] at hδ
    have hX0 : θ.val (ι (γ 0)) ![X (ι (γ 0))] = 0 := by
      rw [← SmoothForm.degreeOneEquiv_coe_apply, hδ, map_zero]
    exact hne 0 hX0
  -- Its loop is the loop of `ι ∘ γ` after a monotone change of time.
  obtain ⟨g, hg, hgγ⟩ := hg
  have : Fact (0 < P) := ⟨hP⟩
  have : Fact (0 < T) := ⟨hT⟩
  have hβP : Periodic (fun t : ℝ ↦ g t) P := fun t ↦ by simp
  obtain ⟨g', hg', hg'γ⟩ :=
    (hβP.exists_nullhomotopic_comp_iff (g.continuous.comp continuous_quotient_mk')
      ψ.continuous (hψmono.monotone.monotoneOn _) hψ0 hψT₀ fun s ↦ by
        simp only [comp_apply, hψT s, AddCircle.coe_add_period]).2 ⟨g, hg, fun _ ↦ rfl⟩
  exact hasContractibleClosedCharacteristic_iff.2 ⟨T, ι ∘ γ ∘ ψ, hT, hδ, hδper, hnc,
    fun t ↦ hKι _, g', hg', fun t ↦ by rw [hg'γ, hgγ, comp_apply, comp_apply]⟩

/-- **A contractible closed Reeb orbit is a contractible closed characteristic.** Let `σ` be a
nondegenerate two-form, `θ` a one-form with `dθ = -σ` along `ι : S → M`, and let the tangent image
of `ι` at each point be the kernel of `dK`, for a `C¹` function `K` equal to `c` along `ι`. If the
restriction `ι^* θ` is a contact form, then a `P`-periodic orbit `γ` of its Reeb field, `P > 0`,
whose loop `ι ∘ γ : ℝ ⧸ Pℤ → W` is contractible in `W`, makes the level `K⁻¹(c)` carry a closed
characteristic contractible in `W`: after a change of time, `ι ∘ γ` is an orbit of the Hamiltonian
field `X_K`. -/
theorem IsNondegenerate.hasContractibleClosedCharacteristic_of_reebVectorField
    (hσ : σ.IsNondegenerate) (hι : ContMDiff J I ∞ ι)
    (hα : (SmoothForm.mpullback ι hι θ).IsContactForm)
    (hdθ : ∀ s, mextDeriv θ.val (ι s) = -σ.val (ι s)) (hKs : ContMDiff I 𝓘(ℝ) 1 K)
    (hK : ∀ s, (mfderiv J I ι s).range = (mvfderiv I K (ι s)).ker) (hKι : ∀ s, K (ι s) = c)
    {γ : ℝ → S} (hγ : IsMIntegralCurve γ (SmoothForm.mpullback ι hι θ).reebVectorField)
    {P : ℝ} (hP : 0 < P) (hper : Periodic γ P)
    (hg : ∃ g : C(AddCircle P, W), g.Nullhomotopic ∧ ∀ t : ℝ, (g t : M) = ι (γ t)) :
    σ.HasContractibleClosedCharacteristic W K c := by
  rcases (hσ.apply_hamiltonianVectorField_ne_zero hι hα (hdθ (γ 0)) (hK (γ 0))).lt_or_gt
    with hneg | hpos
  swap
  · exact hasContractibleClosedCharacteristic_of_reebVectorField_of_pos hσ hι hα hdθ hKs hK hKι
      hγ hP hper hg hpos
  -- For a negative speed, `-K` has the opposite Hamiltonian field and a positive speed.
  have h := hasContractibleClosedCharacteristic_of_reebVectorField_of_pos (K := -K) hσ hι hα hdθ
    hKs.neg (range_mfderiv_eq_ker_mvfderiv_neg hK) (c := -c) (fun s ↦ by simp [hKι]) hγ hP hper
    hg (by rw [apply_hamiltonianVectorField_neg]; exact neg_pos.2 hneg)
  exact h.of_hamiltonianVectorField_eq_smul (a := -1) (by norm_num) (fun x hx ↦ by
    simpa using congrArg Neg.neg hx) fun x _ ↦ by simp

end ReebToCharacteristic

section CharacteristicToReeb

variable [IsManifold J ∞ S] [J.Boundaryless] [FiniteDimensional ℝ E'] [CompactSpace S]
  [I.Boundaryless] [T2Space M]

/-- The converse for one closed characteristic `δ` along which the speed `θ(X_K)` is positive: the
Reeb orbit through the point of `S` over `δ 0`, pushed to the level and reparametrized into an
orbit of `X_K`, is `δ` itself, so it closes up. -/
private theorem exists_reebVectorField_of_pos (hσ : σ.IsNondegenerate) (hι : ContMDiff J I ∞ ι)
    (hα : (SmoothForm.mpullback ι hι θ).IsContactForm)
    (hdθ : ∀ s, mextDeriv θ.val (ι s) = -σ.val (ι s)) (hKs : ContMDiff I 𝓘(ℝ) 2 K)
    (hK : ∀ s, (mfderiv J I ι s).range = (mvfderiv I K (ι s)).ker) (hinj : Injective ι)
    (hcι : ∀ x, K x = c → x ∈ range ι) {T : ℝ} (hT : 0 < T) {δ : ℝ → M}
    (hδ : IsMIntegralCurve δ (σ.hamiltonianVectorField K)) (hper : Periodic δ T)
    (hlev : ∀ t, K (δ t) = c)
    (hg : ∃ g : C(AddCircle T, W), g.Nullhomotopic ∧ ∀ t : ℝ, (g t : M) = δ t)
    (hpos : 0 < θ.val (δ 0) ![σ.hamiltonianVectorField K (δ 0)]) :
    ∃ (P : ℝ) (γ : ℝ → S), 0 < P ∧
      IsMIntegralCurve γ (SmoothForm.mpullback ι hι θ).reebVectorField ∧ Periodic γ P ∧
      ∃ g : C(AddCircle P, W), g.Nullhomotopic ∧ ∀ t : ℝ, (g t : M) = ι (γ t) := by
  have : T2Space S := T2Space.of_injective_continuous hinj hι.continuous
  obtain ⟨s₀, hs₀⟩ := hcι _ (hlev 0)
  -- The Reeb orbit through `s₀`.
  have hc := hα.isCompleteVectorField_reebVectorField
  set γ : ℝ → S := fun t ↦ hα.reebFlow hc t s₀
  have hγ : IsMIntegralCurve γ (SmoothForm.mpullback ι hι θ).reebVectorField :=
    hα.isMIntegralCurve_reebFlow hc s₀
  have hγ0 : γ 0 = s₀ := Flow.map_zero_apply _ _
  -- The speed `θ(X_K)` along it is positive, and bounded since `S` is compact.
  set k : S → ℝ := fun s ↦ θ.val (ι s) ![σ.hamiltonianVectorField K (ι s)]
  have hk : Continuous k :=
    (continuous_apply_hamiltonianVectorField hσ (hKs.of_le one_le_two)).comp hι.continuous
  have hne (s : S) : k s ≠ 0 := hσ.apply_hamiltonianVectorField_ne_zero hι hα (hdθ _) (hK _)
  have hk0 : 0 < k (γ 0) := by rw [hγ0]; rwa [← hs₀] at hpos
  have hkpos (t : ℝ) : 0 < (k ∘ γ) t := sign_eq_one_iff.1 <|
    (isPreconnected_univ.sign_eq_of_continuousOn (hk.comp hγ.continuous).continuousOn
      (fun t _ ↦ hne _) trivial trivial).trans (sign_pos hk0)
  obtain ⟨C, hC⟩ := (isCompact_range hk).bddAbove
  obtain ⟨ψ, hψ0, hψ⟩ := (isMIntegralCurve_comp_reebVectorField hσ hι hα hdθ hK
    hγ).exists_orderIso_isMIntegralCurve_comp (hk.comp hγ.continuous) hkpos
      (fun t ↦ hC (mem_range_self _)) fun t ↦ (smul_inv_smul₀ (hne _) _).symm
  -- By uniqueness of the orbits of `X_K`, the reparametrized orbit is `δ`.
  have hX : ContMDiff I I.tangent 1 (T% (σ.hamiltonianVectorField K)) :=
    hσ.contMDiff_hamiltonianVectorField (n := 1) (by simp) (by simpa [one_add_one_eq_two] using hKs)
  have heq : ι ∘ γ ∘ ψ = δ := isMIntegralCurve_eq_of_contMDiff (t₀ := 0)
    (fun _ ↦ BoundarylessManifold.isInteriorPoint) hX hψ hδ (by simp [hψ0, hγ0, hs₀])
  have heq' (t : ℝ) : ι (γ (ψ t)) = δ t := congrFun heq t
  -- So the Reeb orbit returns to `s₀` at the time `P = ψ T > 0`, and is `P`-periodic.
  have hP : 0 < ψ T := hψ0 ▸ ψ.strictMono hT
  have hγP : γ (ψ T) = s₀ := hinj <| by rw [heq', hper.eq, ← heq', hψ0, hγ0]
  have hγper : Periodic γ (ψ T) := fun t ↦ by
    simp only [γ, Flow.map_add]
    rw [show hα.reebFlow hc (ψ T) s₀ = s₀ from hγP]
  -- Its loop is the loop of `δ` after a monotone change of time.
  obtain ⟨g, hg, hgδ⟩ := hg
  have hW (t : ℝ) : ι (γ t) ∈ W := by
    rw [← ψ.apply_symm_apply t, heq', ← hgδ]
    exact Subtype.coe_prop _
  set β : ℝ → W := fun t ↦ ⟨ι (γ t), hW t⟩
  have : Fact (0 < T) := ⟨hT⟩
  have : Fact (0 < ψ T) := ⟨hP⟩
  have hβP : Periodic β (ψ T) := fun t ↦ Subtype.ext <| congrArg ι (hγper t)
  have hβψ : Periodic (β ∘ ψ) T := fun t ↦ Subtype.ext <| by
    simp only [comp_apply, β, heq', hper t]
  obtain ⟨g', hg', hg'β⟩ :=
    (hβP.exists_nullhomotopic_comp_iff ((hι.continuous.comp hγ.continuous).subtype_mk hW)
      ψ.continuous (ψ.monotone.monotoneOn _) hψ0 rfl hβψ).1
      ⟨g, hg, fun t ↦ Subtype.ext <| by simp only [β, hgδ, heq']⟩
  exact ⟨ψ T, γ, hP, hγ, hγper, g', hg', fun t ↦ by rw [hg'β]⟩

/-- **On a compact embedded level, contractible closed characteristics are contractible closed
Reeb orbits.** Let `σ` be a nondegenerate two-form on a boundaryless manifold, `θ` a one-form with
`dθ = -σ` along `ι : S → M`, and let `ι` be an injective map from a compact boundaryless manifold
onto the level `K⁻¹(c)` of a `C²` function `K`, whose tangent image at each point is the kernel of
`dK`. If the restriction `ι^* θ` is a contact form, then the level `K⁻¹(c)` carries a closed
characteristic contractible in `W` exactly when the Reeb field of `ι^* θ` has a `P`-periodic orbit
`γ`, `P > 0`, whose loop `ι ∘ γ : ℝ ⧸ Pℤ → W` is contractible in `W`. -/
theorem IsNondegenerate.hasContractibleClosedCharacteristic_iff_exists_reebVectorField
    (hσ : σ.IsNondegenerate) (hι : ContMDiff J I ∞ ι)
    (hα : (SmoothForm.mpullback ι hι θ).IsContactForm)
    (hdθ : ∀ s, mextDeriv θ.val (ι s) = -σ.val (ι s)) (hKs : ContMDiff I 𝓘(ℝ) 2 K)
    (hK : ∀ s, (mfderiv J I ι s).range = (mvfderiv I K (ι s)).ker) (hinj : Injective ι)
    (hKι : K ⁻¹' {c} = range ι) :
    σ.HasContractibleClosedCharacteristic W K c ↔
      ∃ (P : ℝ) (γ : ℝ → S), 0 < P ∧
        IsMIntegralCurve γ (SmoothForm.mpullback ι hι θ).reebVectorField ∧ Periodic γ P ∧
        ∃ g : C(AddCircle P, W), g.Nullhomotopic ∧ ∀ t : ℝ, (g t : M) = ι (γ t) := by
  have hcι (x : M) (hx : K x = c) : x ∈ range ι := hKι ▸ hx
  refine ⟨fun h ↦ ?_, fun ⟨P, γ, hP, hγ, hper, hg⟩ ↦
    hσ.hasContractibleClosedCharacteristic_of_reebVectorField hι hα hdθ (hKs.of_le one_le_two) hK
      (fun s ↦ (hKι.symm ▸ mem_range_self s : ι s ∈ K ⁻¹' {c})) hγ hP hper hg⟩
  obtain ⟨T, δ, hT, hδ, hper, -, hlev, hg⟩ := hasContractibleClosedCharacteristic_iff.1 h
  obtain ⟨s, hs⟩ := hcι _ (hlev 0)
  have hne := hσ.apply_hamiltonianVectorField_ne_zero hι hα (hdθ s) (hK s)
  rw [hs] at hne
  rcases hne.lt_or_gt with hneg | hpos
  swap
  · exact exists_reebVectorField_of_pos hσ hι hα hdθ hKs hK hinj hcι hT hδ hper hlev hg hpos
  -- For a negative speed, run the closed characteristic backwards as one of `-K`.
  obtain ⟨g, hg, hgδ⟩ := hg
  let n : C(AddCircle T, AddCircle T) := ⟨Neg.neg, continuous_neg⟩
  refine exists_reebVectorField_of_pos (K := -K) (c := -c) (δ := fun t ↦ δ (-t)) hσ hι hα hdθ
    hKs.neg (range_mfderiv_eq_ker_mvfderiv_neg hK) hinj (fun x hx ↦ hcι x (neg_inj.1 hx)) hT
    ?_ (fun t ↦ by simp only [neg_add, ← sub_eq_add_neg, hper.sub_eq]) (fun t ↦ by simp [hlev])
    ⟨g.comp n, hg.comp_left n, fun t ↦ by simpa [n] using hgδ (-t)⟩
    (by rw [neg_zero, apply_hamiltonianVectorField_neg]; exact neg_pos.2 hneg)
  have hδ' := hδ.comp_mul (-1)
  convert hδ' using 1
  · funext t
    simp
  · funext x
    simp

end CharacteristicToReeb

end SmoothTwoForm

end TauCeti
