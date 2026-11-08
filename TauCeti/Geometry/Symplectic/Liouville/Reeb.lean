/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Hamiltonian.Reeb
public import TauCeti.Geometry.Symplectic.Liouville.RadialHamiltonian
import TauCeti.Geometry.Contact.Flat
import TauCeti.Geometry.Manifold.Flow.Complete
import TauCeti.Geometry.Symplectic.Liouville.Scaling

/-!
# The radial field of a completion and the Reeb flow of the boundary

Let `M` be a completion of the Liouville domain `W ⊆ M` (`TauCeti.IsLiouvilleCompletion`), for the
form `ω` with primitive `α`, Liouville field `Z` (`ι_Z ω = α`) and Liouville flow `ψ`, and let
`r = TauCeti.liouvilleRadialCoordinate Z W` be the radial coordinate of its cylindrical end. The
`1`-periodic orbits of a Hamiltonian linear at infinity with slope `a` on the cylindrical end are
the closed orbits of the Hamiltonian vector field `X_r` of period `a`
(`TauCeti.IsLiouvilleCompletion.exists_periodic_hamiltonianVectorField_iff`). This file identifies
those closed orbits with the closed orbits of the Reeb flow of the boundary `∂W`, with the
convention `ι_{X_H} ω = dH`.

The boundary is described by a smooth map `ι : S → M` with injective differentials into the
frontier of `W`, from a manifold of one dimension less, typically the inclusion of the boundary
`∂W`, a regular level of a defining function, with its regular-level atlas. For `t > 0` the map
`ψ_t ∘ ι` lands on the level `{r = e^t}`, its differential is onto the kernel of `dr`
(`TauCeti.IsLiouvilleCompletion.range_mfderiv_flowOf_comp`), and it pulls `α` back to `e^t ι^* α`.
So the Liouville field, along which `dr(Z) = r` does not vanish, is transverse to it, and the
restriction `ι^* α` is a contact form (`TauCeti.IsLiouvilleCompletion.isContactForm_mpullback`):
the boundary of a Liouville domain is a contact manifold. Since `α(X_r) = -r` on the
cylindrical end, the Reeb field `R` of `ι^* α` is carried to minus the radial field,

`d(ψ_t ∘ ι)(R) = -X_r`

(`TauCeti.IsLiouvilleCompletion.mfderiv_flowOf_comp_reebVectorField`). Hence the Liouville flow
carries the Reeb orbits of `∂W`, run backwards, to the orbits of `X_r` on each level `{r = c}`,
`c > 1` (`TauCeti.IsLiouvilleCompletion.isMIntegralCurve_flowOf_comp_reebVectorField`). When `S`
is compact, `ι` is injective and its image is the whole frontier of `W`, every orbit of `X_r` on
the level `c` arises this way, so `X_r` has a `T`-periodic orbit on the level `c` exactly when
the Reeb field of `ι^* α` has a `T`-periodic orbit
(`TauCeti.IsLiouvilleCompletion.exists_periodic_hamiltonianVectorField_iff_reebVectorField`).

The slope condition of symplectic homology therefore reads as usual: if the slope `a ≠ 0` of a
Hamiltonian linear at infinity is not the period of a closed Reeb orbit of `∂W`, then all its
`1`-periodic orbits lie in a compact set
(`TauCeti.IsLinearAtInfinity.exists_isCompact_forall_mem_of_reebVectorField`).

## Main results

* `TauCeti.IsLiouvilleCompletion.range_mfderiv_flowOf_comp`: the flow-out `ψ_t ∘ ι` of the
  boundary is tangent to the kernel of `dr`.
* `TauCeti.IsLiouvilleCompletion.isContactForm_mpullback`: the primitive restricts to a contact
  form on the boundary.
* `TauCeti.IsLiouvilleCompletion.mfderiv_flowOf_comp_reebVectorField`: the Liouville flow carries
  the Reeb field of the boundary to `-X_r`.
* `TauCeti.IsLiouvilleCompletion.isMIntegralCurve_flowOf_comp_reebVectorField`: it carries
  reversed Reeb orbits to orbits of `X_r`.
* `TauCeti.IsLiouvilleCompletion.exists_periodic_hamiltonianVectorField_iff_reebVectorField`: the
  periods of `X_r` on a level are the periods of the Reeb field of the boundary.
* `TauCeti.IsLinearAtInfinity.exists_isCompact_forall_mem_of_reebVectorField`: the `1`-periodic
  orbits of a Hamiltonian linear at infinity whose slope is not a Reeb period of the boundary lie
  in a compact set.

## References

* P. Seidel, *A biased view of symplectic cohomology*, Current Developments in Mathematics 2006,
  Section 3 (Hamiltonians linear at infinity and the Reeb periods of the boundary).
* A. Oancea, *A survey of Floer homology for manifolds with contact type boundary or symplectic
  homology*, Ensaios Matemáticos 7 (2004), Section 3.
* D. McDuff, D. Salamon, *Introduction to Symplectic Topology*, 3rd ed., Oxford, 2017,
  Section 3.5 (hypersurfaces of contact type and their characteristic line fields).
-/

public section

open Function Module Set
open scoped Manifold Topology

namespace TauCeti

namespace IsLiouvilleCompletion

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless] [TopologicalSpace M]
  [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M] [T2Space M]
  {E' H' S : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [TopologicalSpace H']
  {J : ModelWithCorners ℝ E' H'} [TopologicalSpace S] [ChartedSpace H' S] [IsManifold J (⊤ : ℕ∞) S]
  {ω : SmoothTwoForm I M} {α : SmoothForm I M ℝ 1} {W : Set M} {Z : (x : M) → TangentSpace I x}
  {ι : S → M} {t : ℝ}

omit [IsManifold J (⊤ : ℕ∞) S] in
/-- The time-`t` map of the Liouville flow of a completion composed with a smooth map is
smooth. -/
private theorem contMDiff_flowOf_comp (h : IsLiouvilleCompletion ω α W)
    (hZ : RoughForm.interior Z ω.1 = α.1) (hι : ContMDiff J I (⊤ : ℕ∞) ι) (t : ℝ) :
    ContMDiff J I (⊤ : ℕ∞) (flowOf Z t ∘ ι) := by
  rw [h.flowOf_eq_globalFlowDiffeomorph hZ t]
  exact (Diffeomorph.contMDiff _).comp hι

/-- The Liouville flow rescales the restriction of the primitive, `(ψ_t ∘ ι)^* α = e^t ι^* α`. -/
private theorem mpullback_flowOf_comp (h : IsLiouvilleCompletion ω α W)
    (hZ : RoughForm.interior Z ω.1 = α.1) (hι : ContMDiff J I (⊤ : ℕ∞) ι) (t : ℝ) :
    SmoothForm.mpullback (flowOf Z t ∘ ι) (h.contMDiff_flowOf_comp hZ hι t) α =
      Real.exp t • SmoothForm.mpullback ι hι α := by
  have hZs := h.contMDiff_of_interior_eq hZ
  have hψ : MDifferentiable I I (flowOf Z t) := by
    rw [h.flowOf_eq_globalFlowDiffeomorph hZ t]
    exact (Diffeomorph.contMDiff _).mdifferentiable (by simp)
  apply Subtype.ext
  rw [SmoothForm.coe_mpullback, Submodule.coe_smul, SmoothForm.coe_mpullback,
    mpullback_comp (hι.mdifferentiable (by simp)) hψ,
    flowOf_eq_globalFlow (hZs.of_le (by simp)) (h.isCompleteVectorField hZ),
    mpullback_globalFlow_eq_exp_smul_of_interior_eq (h.isCompleteVectorField hZ)
      (hZs.of_le (by simp)) α.mdifferentiable h.mextDeriv_eq hZ t, mpullback_smul]

omit [TopologicalSpace S] in
/-- For `t > 0` the Liouville flow carries the boundary of the Liouville domain into the
cylindrical end. -/
private theorem flowOf_comp_notMem (h : IsLiouvilleCompletion ω α W)
    (hZ : RoughForm.interior Z ω.1 = α.1) (hιW : ∀ s, ι s ∈ frontier W) (ht : 0 < t) (s : S) :
    flowOf Z t (ι s) ∉ W := by
  rw [← h.one_lt_liouvilleRadialCoordinate_iff hZ,
    h.liouvilleRadialCoordinate_flowOf hZ (hιW s) ht.le]
  exact Real.one_lt_exp_iff.2 ht

omit [IsManifold J (⊤ : ℕ∞) S] in
/-- The differential of `ψ_t ∘ ι` is injective when that of `ι` is. -/
private theorem injective_mfderiv_flowOf_comp (h : IsLiouvilleCompletion ω α W)
    (hZ : RoughForm.interior Z ω.1 = α.1) (hι : ContMDiff J I (⊤ : ℕ∞) ι)
    (hιs : ∀ s, Function.Injective (mfderiv J I ι s)) (t : ℝ) (s : S) :
    Function.Injective (mfderiv J I (flowOf Z t ∘ ι) s) := by
  set ψ := globalFlowDiffeomorph (h.isCompleteVectorField hZ) le_top
    (h.contMDiff_of_interior_eq hZ) t
  rw [h.flowOf_eq_globalFlowDiffeomorph hZ t, mfderiv_comp s
    ((ψ.contMDiff (ι s)).mdifferentiableAt (by simp)) ((hι s).mdifferentiableAt (by simp)),
    ContinuousLinearMap.coe_comp]
  exact (ψ.isInvertible_mfderiv (by simp)).injective.comp (hιs s)

omit [IsManifold J (⊤ : ℕ∞) S] in
/-- **The flow-out of the boundary is a level of the radial coordinate, infinitesimally.** Let
`ι : S → M` be a smooth map with injective differentials into the frontier of the Liouville
domain, from a manifold of one dimension less. For `t > 0` the image of the differential of
`ψ_t ∘ ι` at `s` is the kernel of the differential of the radial coordinate at `ψ_t (ι s)`. -/
theorem range_mfderiv_flowOf_comp (h : IsLiouvilleCompletion ω α W)
    (hZ : RoughForm.interior Z ω.1 = α.1) (hι : ContMDiff J I (⊤ : ℕ∞) ι)
    (hιW : ∀ s, ι s ∈ frontier W)
    (hιs : ∀ s, Function.Injective (mfderiv J I ι s)) (hdim : finrank ℝ E' + 1 = finrank ℝ E)
    (ht : 0 < t) (s : S) :
    (mfderiv J I (flowOf Z t ∘ ι) s).range =
      (mvfderiv I (liouvilleRadialCoordinate Z W) (flowOf Z t (ι s))).ker := by
  set r := liouvilleRadialCoordinate Z W
  set x := flowOf Z t (ι s)
  have hx : x ∉ W := h.flowOf_comp_notMem hZ hιW ht s
  have hrx : MDifferentiableAt I 𝓘(ℝ) r x :=
    (h.contMDiffAt_liouvilleRadialCoordinate hZ hx).mdifferentiableAt (by simp)
  have hg : MDifferentiableAt J I (flowOf Z t ∘ ι) s :=
    (h.contMDiff_flowOf_comp hZ hι t s).mdifferentiableAt (by simp)
  -- `r ∘ ψ_t ∘ ι` is the constant `e^t`, so the image of the differential lies in `ker dr`.
  have hle : (mfderiv J I (flowOf Z t ∘ ι) s).range ≤ (mvfderiv I r x).ker := by
    rintro _ ⟨w, rfl⟩
    have hconst : r ∘ (flowOf Z t ∘ ι) = fun _ ↦ Real.exp t :=
      funext fun s' ↦ h.liouvilleRadialCoordinate_flowOf hZ (hιW s') ht.le
    have hcomp := mfderiv_comp s hrx hg
    rw [hconst, mfderiv_const] at hcomp
    rw [LinearMap.mem_ker, ContinuousLinearMap.coe_coe, mvfderiv_apply_eq_mfderiv_apply]
    exact (congrArg (· w) hcomp).symm
  -- Both sides have dimension `dim E - 1`: `dr(Z) = r` does not vanish.
  have hne : (mvfderiv I r x : TangentSpace I x →ₗ[ℝ] ℝ) ≠ 0 := fun h0 ↦ by
    have hZx := h.mvfderiv_liouvilleRadialCoordinate_apply hZ hx
    rw [← ContinuousLinearMap.coe_coe, h0, LinearMap.zero_apply] at hZx
    linarith [one_le_liouvilleRadialCoordinate Z W x]
  refine Submodule.eq_of_le_of_finrank_eq hle ?_
  have hker := Module.Dual.finrank_ker_add_one_of_ne_zero hne
  rw [LinearMap.finrank_range_of_inj (h.injective_mfderiv_flowOf_comp hZ hι hιs t s)]
  exact (Nat.add_right_cancel (hdim.trans hker.symm))

/-- **The boundary of a Liouville domain is a contact manifold.** Let `ι : S → M` be a smooth map
with injective differentials into the frontier of the Liouville domain `W`, from a manifold of one
dimension less. Then the restriction `ι^* α` of the primitive is a contact form on `S`. -/
theorem isContactForm_mpullback (h : IsLiouvilleCompletion ω α W)
    (hZ : RoughForm.interior Z ω.1 = α.1) (hι : ContMDiff J I (⊤ : ℕ∞) ι)
    (hιW : ∀ s, ι s ∈ frontier W)
    (hιs : ∀ s, Function.Injective (mfderiv J I ι s)) (hdim : finrank ℝ E' + 1 = finrank ℝ E) :
    (SmoothForm.mpullback ι hι α).IsContactForm := by
  -- Push the boundary off to the level `e` of `r`, where the Liouville field is transverse.
  rw [← SmoothForm.isContactForm_smul_iff (Real.exp_pos 1).ne', ← h.mpullback_flowOf_comp hZ hι 1]
  refine SmoothForm.isContactForm_iff_forall_isContactFormAt.2 fun s ↦ ?_
  rw [SmoothForm.coe_mpullback]
  have hx : flowOf Z 1 (ι s) ∉ W := h.flowOf_comp_notMem hZ hιW one_pos s
  refine isContactFormAt_mpullback hdim ((h.contMDiff_flowOf_comp hZ hι 1 s).of_le (by simp))
    (h.injective_mfderiv_flowOf_comp hZ hι hιs 1 s) (fun v hv ↦ ?_)
    ((α.contMDiff _).of_le (by simp)) (by rw [h.mextDeriv_eq]) (z := Z (flowOf Z 1 (ι s))) ?_
    fun v ↦ ?_
  · exact (SmoothTwoForm.isNondegenerate_iff_separatingLeft.1 h.isNondegenerate) _ v fun w ↦ by
      simpa [SmoothBundleForm.eval₂_apply] using hv w
  · rw [h.range_mfderiv_flowOf_comp hZ hι hιW hιs hdim one_pos s, LinearMap.mem_ker,
      ContinuousLinearMap.coe_coe, h.mvfderiv_liouvilleRadialCoordinate_apply hZ hx]
    linarith [one_le_liouvilleRadialCoordinate Z W (flowOf Z 1 (ι s))]
  · simpa only [RoughForm.interior_apply, comp_apply] using congrArg (fun a ↦ a _ ![v]) hZ

/-- **The Liouville flow carries the Reeb field of the boundary to minus the radial field.** Let
`ι : S → M` be a smooth map with injective differentials into the frontier of the Liouville
domain, from a manifold of one dimension less. For `t > 0`, the differential of `ψ_t ∘ ι` sends
the Reeb vector field of the contact form `ι^* α` to `-X_r` at `ψ_t (ι s)`. -/
theorem mfderiv_flowOf_comp_reebVectorField [FiniteDimensional ℝ E']
    (h : IsLiouvilleCompletion ω α W)
    (hZ : RoughForm.interior Z ω.1 = α.1) (hι : ContMDiff J I (⊤ : ℕ∞) ι)
    (hιW : ∀ s, ι s ∈ frontier W)
    (hιs : ∀ s, Function.Injective (mfderiv J I ι s)) (hdim : finrank ℝ E' + 1 = finrank ℝ E)
    (ht : 0 < t) (s : S) :
    mfderiv J I (flowOf Z t ∘ ι) s ((SmoothForm.mpullback ι hι α).reebVectorField s) =
      -ω.hamiltonianVectorField (liouvilleRadialCoordinate Z W) (flowOf Z t (ι s)) := by
  have hα₀ := h.isContactForm_mpullback hZ hι hιW hιs hdim
  have hg := h.contMDiff_flowOf_comp hZ hι t
  have het : Real.exp t ≠ 0 := (Real.exp_pos t).ne'
  have hrx := h.liouvilleRadialCoordinate_flowOf hZ (hιW s) ht.le
  -- The restriction of `-α` to the level `e^t` is `-e^t ι^* α`.
  have hpull : SmoothForm.mpullback (flowOf Z t ∘ ι) hg (-α) =
      (-Real.exp t) • SmoothForm.mpullback ι hι α := by
    rw [map_neg, h.mpullback_flowOf_comp hZ hι t]
    exact (neg_smul _ _).symm
  have hcontact : (SmoothForm.mpullback (flowOf Z t ∘ ι) hg (-α)).IsContactForm := by
    rwa [hpull, SmoothForm.isContactForm_smul_iff (neg_ne_zero.2 het)]
  -- `-α(X_r) = r`.
  have hθ : (-α).1 (flowOf Z t (ι s))
      ![ω.hamiltonianVectorField (liouvilleRadialCoordinate Z W) (flowOf Z t (ι s))] =
        liouvilleRadialCoordinate Z W (flowOf Z t (ι s)) := by
    rw [Submodule.coe_neg, Pi.neg_apply, ContinuousAlternatingMap.neg_apply,
      h.apply_hamiltonianVectorField_liouvilleRadialCoordinate hZ
        (h.flowOf_comp_notMem hZ hιW ht s), neg_neg]
  have key := h.isNondegenerate.mfderiv_reebVectorField_mpullback hg hcontact
    (K := liouvilleRadialCoordinate Z W) (s := s)
    (by rw [Submodule.coe_neg, mextDeriv_neg, h.mextDeriv_eq, Pi.neg_apply])
    (h.range_mfderiv_flowOf_comp hZ hι hιW hιs hdim ht s)
    (by rw [comp_apply, hθ, hrx]; exact het)
  rw [hpull, hα₀.reebVectorField_smul (neg_ne_zero.2 het), map_smul, comp_apply, hθ, hrx] at key
  -- `key : (-e^t)⁻¹ • d(ψ_t ∘ ι)(R) = (e^t)⁻¹ • X_r`.
  calc mfderiv J I (flowOf Z t ∘ ι) s ((SmoothForm.mpullback ι hι α).reebVectorField s)
      = (-Real.exp t) • ((-Real.exp t)⁻¹ •
          mfderiv J I (flowOf Z t ∘ ι) s ((SmoothForm.mpullback ι hι α).reebVectorField s)) := by
        rw [smul_smul, mul_inv_cancel₀ (neg_ne_zero.2 het), one_smul]
    _ = _ := by rw [key, smul_smul, neg_mul, mul_inv_cancel₀ het, neg_one_smul]

/-- **The Liouville flow carries reversed Reeb orbits of the boundary to orbits of the radial
field.** Let `ι : S → M` be a smooth map with injective differentials into the frontier of the
Liouville domain, from a manifold of one dimension less, and let `γ` be an integral curve of the
Reeb field of `ι^* α`. For `t > 0`, the curve `τ ↦ ψ_t (ι (γ (-τ)))`, on the level `e^t` of the
radial coordinate, is an integral curve of `X_r`. -/
theorem isMIntegralCurve_flowOf_comp_reebVectorField [FiniteDimensional ℝ E']
    (h : IsLiouvilleCompletion ω α W)
    (hZ : RoughForm.interior Z ω.1 = α.1) (hι : ContMDiff J I (⊤ : ℕ∞) ι)
    (hιW : ∀ s, ι s ∈ frontier W)
    (hιs : ∀ s, Function.Injective (mfderiv J I ι s)) (hdim : finrank ℝ E' + 1 = finrank ℝ E)
    (ht : 0 < t) {γ : ℝ → S}
    (hγ : IsMIntegralCurve γ (SmoothForm.mpullback ι hι α).reebVectorField) :
    IsMIntegralCurve (fun τ ↦ flowOf Z t (ι (γ (-τ))))
      (ω.hamiltonianVectorField (liouvilleRadialCoordinate Z W)) := by
  have hγ' := hγ.comp_mul (-1)
  rw [isMIntegralCurve_iff_isMIntegralCurveOn] at hγ' ⊢
  have hmap := hγ'.map_of_mfderiv_eq (f := flowOf Z t ∘ ι)
    (fun τ _ ↦ (h.contMDiff_flowOf_comp hZ hι t _).mdifferentiableAt (by simp))
    (fun τ _ ↦ by
      rw [Pi.smul_apply, map_smul, h.mfderiv_flowOf_comp_reebVectorField hZ hι hιW hιs hdim ht,
        neg_one_smul, neg_neg, comp_apply])
  simpa [comp_def] using hmap

/-- **The periods of the radial field are the Reeb periods of the boundary.** Let `ι : S → M` be
an injective smooth map with injective differentials from a compact boundaryless manifold of one
dimension less onto the frontier of the Liouville domain. For a level `c > 1` of the radial
coordinate, the Hamiltonian vector field `X_r` has a `T`-periodic integral curve on the level `c`
exactly when the Reeb field of the contact form `ι^* α` has a `T`-periodic integral curve: the
Liouville flow `ψ_{log c} ∘ ι` carries the reversed Reeb orbits onto the orbits of `X_r` on the
level `c`. -/
theorem exists_periodic_hamiltonianVectorField_iff_reebVectorField [FiniteDimensional ℝ E']
    [BoundarylessManifold J S] [CompactSpace S] (h : IsLiouvilleCompletion ω α W)
    (hZ : RoughForm.interior Z ω.1 = α.1) (hι : ContMDiff J I (⊤ : ℕ∞) ι)
    (hιW : ∀ s, ι s ∈ frontier W)
    (hιs : ∀ s, Function.Injective (mfderiv J I ι s)) (hdim : finrank ℝ E' + 1 = finrank ℝ E)
    (hinj : Injective ι) (hWι : frontier W ⊆ range ι) {c T : ℝ} (hc : 1 < c) :
    (∃ δ : ℝ → M, IsMIntegralCurve δ (ω.hamiltonianVectorField (liouvilleRadialCoordinate Z W)) ∧
        Periodic δ T ∧ ∀ τ, liouvilleRadialCoordinate Z W (δ τ) = c) ↔
      ∃ γ : ℝ → S, IsMIntegralCurve γ (SmoothForm.mpullback ι hι α).reebVectorField ∧
        Periodic γ T := by
  have : T2Space S := T2Space.of_injective_continuous hinj hι.continuous
  have ht : 0 < Real.log c := Real.log_pos hc
  have hlevel (γ : ℝ → S) (τ : ℝ) :
      liouvilleRadialCoordinate Z W (flowOf Z (Real.log c) (ι (γ (-τ)))) = c := by
    rw [h.liouvilleRadialCoordinate_flowOf hZ (hιW _) ht.le, Real.exp_log (one_pos.trans hc)]
  constructor
  · rintro ⟨δ, hδ, hδT, hδc⟩
    -- The orbit of `X_r` through `δ 0` starts over the boundary point `ψ_{-log c} (δ 0) = ι s₀`.
    have h0W : δ 0 ∉ W := (h.one_lt_liouvilleRadialCoordinate_iff hZ).1 (by rw [hδc]; exact hc)
    obtain ⟨s₀, hs₀⟩ := hWι (h.flowOf_neg_log_liouvilleRadialCoordinate_mem_frontier hZ
      fun hi ↦ h0W (interior_subset hi))
    have hδ0 : flowOf Z (Real.log c) (ι s₀) = δ 0 := by
      rw [hs₀, hδc, h.flowOf_flowOf hZ, add_neg_cancel, h.flowOf_zero hZ]
    -- The Reeb field of the compact boundary is complete; follow its orbit through `s₀`.
    have hR : ContMDiff J J.tangent 1 (T% (SmoothForm.mpullback ι hι α).reebVectorField) :=
      (h.isContactForm_mpullback hZ hι hιW hιs hdim).contMDiff_reebVectorField.of_le (by simp)
    set γ := fun τ ↦ globalFlow _ hR (isCompleteVectorField_of_compactSpace hR) τ s₀
    have hγ : IsMIntegralCurve γ (SmoothForm.mpullback ι hι α).reebVectorField :=
      isMIntegralCurve_globalFlow _ _ s₀
    have heq : (fun τ ↦ flowOf Z (Real.log c) (ι (γ (-τ)))) = δ :=
      h.eq_of_isMIntegralCurve_hamiltonianVectorField_liouvilleRadialCoordinate hZ hc
        (h.isMIntegralCurve_flowOf_comp_reebVectorField hZ hι hιW hιs hdim ht hγ) hδ (hlevel γ) hδc
        (by simp only [neg_zero, γ, Flow.map_zero_apply, hδ0])
    -- `ψ_{log c} ∘ ι` is injective, so the periodicity of `δ` passes to `γ`.
    have hinjg : Injective (flowOf Z (Real.log c) ∘ ι) := by
      rw [h.flowOf_eq_globalFlowDiffeomorph hZ]
      exact (Diffeomorph.toEquiv _).injective.comp hinj
    refine ⟨γ, hγ, fun τ ↦ hinjg ?_⟩
    have e₁ := congrFun heq (-(τ + T))
    have e₂ := congrFun heq (-τ)
    simp only [neg_neg] at e₁ e₂
    rw [comp_apply, comp_apply, e₁, e₂, ← hδT (-(τ + T)), neg_add, neg_add_cancel_right]
  · rintro ⟨γ, hγ, hγT⟩
    refine ⟨fun τ ↦ flowOf Z (Real.log c) (ι (γ (-τ))),
      h.isMIntegralCurve_flowOf_comp_reebVectorField hZ hι hιW hιs hdim ht hγ, fun τ ↦ ?_,
      hlevel γ⟩
    simp only [neg_add, ← sub_eq_add_neg, hγT.sub_eq]

end IsLiouvilleCompletion

/-- **Periodic orbits of Hamiltonians linear at infinity lie in a compact set** when the slope is
not a Reeb period of the boundary. On a completion of the Liouville domain `W`, let `ι : S → M`
be an injective smooth map with injective differentials from a compact boundaryless manifold of
one dimension less onto the frontier of `W`. If `F` is linear at infinity with slope `a ≠ 0`, and
the Reeb field of the contact form `ι^* α` has no `a`-periodic integral curve, then a compact set
contains every `1`-periodic orbit of `F`. -/
theorem IsLinearAtInfinity.exists_isCompact_forall_mem_of_reebVectorField {E H M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} [I.Boundaryless] [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I (⊤ : ℕ∞) M] [T2Space M] {E' H' S : Type*} [NormedAddCommGroup E']
    [NormedSpace ℝ E'] [FiniteDimensional ℝ E'] [TopologicalSpace H']
    {J : ModelWithCorners ℝ E' H'} [TopologicalSpace S] [ChartedSpace H' S]
    [IsManifold J (⊤ : ℕ∞) S] [BoundarylessManifold J S] [CompactSpace S] {ω : SmoothTwoForm I M}
    {α : SmoothForm I M ℝ 1} {W : Set M} {Z : (x : M) → TangentSpace I x} {ι : S → M}
    {F : M → ℝ} {a : ℝ} (hF : IsLinearAtInfinity Z W F a) (h : IsLiouvilleCompletion ω α W)
    (hZ : RoughForm.interior Z ω.1 = α.1) (hι : ContMDiff J I (⊤ : ℕ∞) ι)
    (hιW : ∀ s, ι s ∈ frontier W)
    (hιs : ∀ s, Function.Injective (mfderiv J I ι s)) (hdim : finrank ℝ E' + 1 = finrank ℝ E)
    (hinj : Function.Injective ι) (hWι : frontier W ⊆ range ι) (ha : a ≠ 0)
    (hper : ¬∃ γ : ℝ → S, IsMIntegralCurve γ (SmoothForm.mpullback ι hι α).reebVectorField ∧
      Function.Periodic γ a) :
    ∃ K : Set M, IsCompact K ∧ ∀ γ : ℝ → M, IsMIntegralCurve γ (ω.hamiltonianVectorField F) →
      Function.Periodic γ 1 → ∀ t, γ t ∈ K :=
  hF.exists_isCompact_forall_mem h hZ ha one_lt_two fun hδ ↦ hper
    ((h.exists_periodic_hamiltonianVectorField_iff_reebVectorField hZ hι hιW hιs hdim hinj hWι
      one_lt_two).1 hδ)

end TauCeti
