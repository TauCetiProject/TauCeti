/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Flow.Parametric
import TauCeti.Geometry.Manifold.ContMDiffMap.Extension
import TauCeti.Geometry.Manifold.LocalDiffeomorph.Basic
import TauCeti.Geometry.Manifold.LocalDiffeomorph.Injective
import TauCeti.Geometry.Manifold.MFDeriv.NormedSpace
import TauCeti.Geometry.Manifold.MFDeriv.Prod
import TauCeti.Geometry.Manifold.VectorBundle.Tangent.Basic
import TauCeti.Geometry.Manifold.VectorField.Transverse

/-!
# The transport equation along a vector field, with zero values on a transverse slice

Let `Z` be a smooth vector field and `g` a smooth function on a finite-dimensional boundaryless
manifold `M`. The **transport equation** asks for a function `h` with

`Z h = g`, that is `dh (Z) = g`,

an ordinary differential equation along the trajectories of `Z`. It is solved by integrating `g`
along these trajectories, starting from a hypersurface transverse to `Z` on which `h` is
prescribed. This file solves it with zero values on such a slice.

Let `ι : S → M` be a smooth map from a boundaryless manifold of one dimension less, let `K ⊆ S` be
a compact set on which `ι` is injective and has injective differential, and suppose that `Z` is
transverse to `ι` along `K`: `Z (ι s)` is not in the range of `dι_s` for `s ∈ K`. Then there are an
open neighbourhood `V` of `ι(K)` and a function `h`, smooth on `V`, with `Z h = g` on `V` and
`h ∘ ι = 0` near `K` (`TauCeti.exists_isOpen_contMDiffOn_mvfderiv_eq`). On a σ-compact manifold,
`h` extends from a closed neighbourhood of `ι(K)` to a smooth function on all of `M`, with the same
properties near `ι(K)` (`TauCeti.exists_contMDiff_mvfderiv_eq`). At a point `ι s` with
`g (ι s) = 0`, such a solution has vanishing differential, since `dh` kills both the tangent space
of the slice and the transverse vector `Z (ι s)`
(`TauCeti.mvfderiv_eq_zero_of_eventuallyEq_zero`).

The construction is the classical one. Adjoin to `M` a real coordinate `y` and consider the vector
field `(y, x) ↦ (g x, Z x)` on `ℝ × M`: along its trajectories the point of `M` follows `Z` while
`y` accumulates the integral of `g`. Its flow out of `s ↦ (0, ι s)` is a map
`(τ, s) ↦ (H (τ, s), Φ (τ, s))` with `H (0, s) = 0` and `Φ (0, s) = ι s`. By transversality and the
inverse function theorem, `Φ` is a local diffeomorphism along `{0} × K`, and since `K` is compact
and `Φ` is injective there, `Φ` is a diffeomorphism from a neighbourhood of `{0} × K` onto a
neighbourhood `V` of `ι(K)`. The solution is `h = H ∘ Φ⁻¹` on `V`: along a trajectory of `Z` it
grows at the rate `g`, because `H` does along the corresponding trajectory of the extended field.

The same applies to a smooth family of vector fields `v a` on `M` and a smooth family of right
sides `g a`, indexed by a parameter manifold `P`: applied to the vertical field
`(a, x) ↦ (0, v a x)` (`TauCeti.verticalField`) of `P × M` and the slice `(a, s) ↦ (a, ι s)`, it
gives a function `h` smooth in the parameter and the point which solves `v a (h a) = g a` near
`T × ι(K)` for a compact set `T` of parameters, with zero values on the slice
(`TauCeti.exists_contMDiff_mvfderiv_eq_param`). For the Reeb vector fields of a smooth family of
contact forms this is the Reeb-direction equation of the strict contact-Moser method
(`TauCeti.SmoothForm.exists_contMDiff_mvfderiv_reebVectorField_eq`).

## Main results

* `TauCeti.exists_isOpen_contMDiffOn_mvfderiv_eq`: a solution of `Z h = g` on a neighbourhood of
  `ι(K)`, smooth there and vanishing on the slice near `K`.
* `TauCeti.exists_contMDiff_mvfderiv_eq`: on a σ-compact manifold, a globally smooth function
  solving `Z h = g` near `ι(K)` and vanishing on the slice near `K`.
* `TauCeti.mvfderiv_eq_zero_of_eventuallyEq_zero`: a solution vanishing on the slice has zero
  differential wherever `g` vanishes on the slice.
* `TauCeti.exists_contMDiff_mvfderiv_eq_param`: the same for smooth families of vector fields and
  right sides, uniformly over a compact set of parameters.

## References

* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Graduate Texts in Mathematics 218,
  Springer, 2013, Theorem 9.20 (the flow-out theorem).
* A. Kriegl, P. W. Michor, *The Convenient Setting of Global Analysis*, AMS, 1997,
  Proposition 43.18 (the Reeb-direction equation solved on a transverse slice with zero initial
  values).
-/

public section

noncomputable section

open Function Set Filter Module
open scoped Manifold ContDiff Topology

namespace TauCeti

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  {E' H' S : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [TopologicalSpace H']
  {J : ModelWithCorners ℝ E' H'} [TopologicalSpace S] [ChartedSpace H' S]

/-! ### The extended vector field -/

/-- The vector field `(y, x) ↦ (g x, Z x)` on `ℝ × M`. Along its trajectories the point of `M`
follows `Z` and the real coordinate grows at the rate `g`. -/
private def transportField (Z : (x : M) → TangentSpace I x) (g : M → ℝ) :
    (p : ℝ × M) → TangentSpace (𝓘(ℝ).prod I) p :=
  fun p ↦ (g p.2, Z p.2)

/-- The extended field at `(y, x)` is `(g x, Z x)`. -/
@[simp]
private theorem transportField_apply (Z : (x : M) → TangentSpace I x) (g : M → ℝ) (p : ℝ × M) :
    transportField Z g p = (g p.2, Z p.2) :=
  rfl

/-- The extended vector field of a `C^n` vector field and a `C^n` function is `C^n`. -/
private theorem contMDiff_transportField [IsManifold I 1 M] {n : ℕ∞ω}
    {Z : (x : M) → TangentSpace I x} {g : M → ℝ} (hZ : ContMDiff I I.tangent n (T% Z))
    (hg : ContMDiff I 𝓘(ℝ) n g) :
    ContMDiff (𝓘(ℝ).prod I) (𝓘(ℝ).prod I).tangent n
      (fun p : ℝ × M ↦ (⟨p, transportField Z g p⟩ : TangentBundle (𝓘(ℝ).prod I) (ℝ × M))) := by
  -- The real component is the point `(y, g x)` of `Tℝ = ℝ × ℝ`.
  have hval : ContMDiff (𝓘(ℝ).prod I) 𝓘(ℝ).tangent n
      (fun p : ℝ × M ↦ (⟨p.1, g p.2⟩ : TangentBundle 𝓘(ℝ) ℝ)) :=
    fun p ↦ Bundle.contMDiffAt_totalSpace_iff.2 ⟨contMDiffAt_fst, by
      -- In the trivialization of `Tℝ` the fibre coordinate of `(y, c)` is `c` itself.
      exact (hg.comp contMDiff_snd p).congr_of_eventuallyEq (.of_forall fun q ↦ by simp)⟩
  exact contMDiff_equivTangentBundleProd_symm.comp (hval.prodMk (hZ.comp contMDiff_snd))

/-! ### Vanishing of the differential on the slice -/

/-- **Vanishing of the differential on a transverse slice.** Let `ι : S → M` have injective
differential at `s`, with `Z (ι s)` outside its range, where `S` has one dimension less than the
finite-dimensional `M`. If a function `h`, differentiable at `ι s`, vanishes on the slice near `s`
and its derivative along `Z` vanishes at `ι s`, then its differential at `ι s` is zero. -/
theorem mvfderiv_eq_zero_of_eventuallyEq_zero [FiniteDimensional ℝ E]
    (hdim : finrank ℝ E = finrank ℝ E' + 1) {Z : (x : M) → TangentSpace I x} {ι : S → M}
    {h : M → ℝ} {s : S}
    (hh : MDifferentiableAt I 𝓘(ℝ) h (ι s)) (hιs : MDifferentiableAt J I ι s)
    (h0 : h ∘ ι =ᶠ[𝓝 s] 0) (himm : Injective (mfderiv J I ι s))
    (htr : Z (ι s) ∉ (mfderiv J I ι s).range) (hZ : mvfderiv I h (ι s) (Z (ι s)) = 0) :
    mvfderiv I h (ι s) = 0 := by
  set L := (mfderiv J I ι s).toLinearMap
  have : FiniteDimensional ℝ E' := finiteDimensional_of_injective_mfderiv himm
  -- The differential of `h` kills the tangent space of the slice, since `h ∘ ι` vanishes near `s`.
  have hL (w : TangentSpace J s) : mvfderiv I h (ι s) (L w) = 0 := by
    have hc := mvfderiv_comp_apply s hh hιs w
    rw [h0.mvfderiv_eq, mvfderiv_zero] at hc
    exact hc.symm
  -- The tangent space of the slice and the line through `Z (ι s)` span the tangent space of `M`.
  have htop : LinearMap.range L ⊔ ℝ ∙ Z (ι s) = ⊤ := by
    refine Submodule.eq_top_of_finrank_eq ?_
    rw [Submodule.finrank_sup_span_singleton htr, LinearMap.finrank_range_of_inj himm]
    exact hdim.symm
  refine ContinuousLinearMap.ext fun v ↦ ?_
  have hv : v ∈ LinearMap.range L ⊔ ℝ ∙ Z (ι s) := htop ▸ Submodule.mem_top
  obtain ⟨_, ⟨w, rfl⟩, _, hz, rfl⟩ := Submodule.mem_sup.1 hv
  obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hz
  rw [map_add, map_smul, hL, hZ]
  simp

/-! ### Local solutions near a compact part of the slice -/

section Local

variable [FiniteDimensional ℝ E] [T2Space M] [BoundarylessManifold I M] [IsManifold I ∞ M]
  [BoundarylessManifold J S] [IsManifold J ∞ S]
  {Z : (x : M) → TangentSpace I x} {g : M → ℝ} {ι : S → M}

/-- The flow of the extended field out of the slice `s ↦ (0, ι s)`: its value at `(τ, s)` is the
point reached at time `τ` from `(0, ι s)`. Its first component accumulates the integral of `g`, its
second component follows `Z`. -/
private def transportFlowOut (Z : (x : M) → TangentSpace I x) (g : M → ℝ) (ι : S → M)
    (q : ℝ × S) : ℝ × M :=
  flowOf (transportField Z g) q.1 ((0 : ℝ), ι q.2)

/-- The set of `(τ, s)` at which the flow out of the slice is defined. -/
private def transportFlowOutDomain (Z : (x : M) → TangentSpace I x) (g : M → ℝ) (ι : S → M) :
    Set (ℝ × S) :=
  {q | (q.1, ((0 : ℝ), ι q.2)) ∈ flowDomain (transportField Z g)}

omit [FiniteDimensional ℝ E] [T2Space M] [BoundarylessManifold I M] in
/-- The extended field is `C¹`, the regularity that the flow lemmas ask for. -/
private theorem contMDiff_one_transportField
    (hZ : ContMDiff I I.tangent ∞ (T% Z)) (hg : ContMDiff I 𝓘(ℝ) ∞ g) :
    ContMDiff (𝓘(ℝ).prod I) (𝓘(ℝ).prod I).tangent 1 (T% (transportField Z g)) :=
  (contMDiff_transportField hZ hg).of_le (by simp)

omit [BoundarylessManifold J S] [IsManifold J ∞ S] in
/-- The flow out of the slice is defined on an open set containing `{0} × S`, and it is smooth
there, starting from `(0, ι s)`. -/
private theorem transportFlowOut_basic
    (hZ : ContMDiff I I.tangent ∞ (T% Z)) (hg : ContMDiff I 𝓘(ℝ) ∞ g)
    (hι : ContMDiff J I ∞ ι) :
    IsOpen (transportFlowOutDomain Z g ι) ∧ (∀ s, ((0 : ℝ), s) ∈ transportFlowOutDomain Z g ι) ∧
      (∀ q ∈ transportFlowOutDomain Z g ι,
        ContMDiffAt (𝓘(ℝ).prod J) (𝓘(ℝ).prod I) ∞ (transportFlowOut Z g ι) q) ∧
      ∀ s, transportFlowOut Z g ι (0, s) = (0, ι s) :=
  ⟨isOpen_setOf_mem_flowDomain (contMDiff_one_transportField hZ hg) continuous_fst
      (continuous_const.prodMk (hι.continuous.comp continuous_snd)),
    fun _ ↦ mem_flowDomain_zero (contMDiff_one_transportField hZ hg) _,
    fun q hq ↦ contMDiffAt_flowOf_comp le_top (contMDiff_transportField hZ hg) contMDiffAt_fst
      (contMDiffAt_const.prodMk (hι.contMDiffAt.comp q contMDiffAt_snd)) hq,
    fun _ ↦ flowOf_zero _ _⟩

omit [BoundarylessManifold J S] [IsManifold J ∞ S] in
/-- Along the slice, the differential of the `M`-component `Φ` of the flow out of the slice is
`(a, w) ↦ a Z (ι s) + dι w`. -/
private theorem mfderiv_snd_transportFlowOut_zero_apply
    (hZ : ContMDiff I I.tangent ∞ (T% Z)) (hg : ContMDiff I 𝓘(ℝ) ∞ g)
    (hι : ContMDiff J I ∞ ι) (s : S)
    (v : TangentSpace (𝓘(ℝ).prod J) ((0 : ℝ), s)) :
    mfderiv (𝓘(ℝ).prod J) I (fun q ↦ (transportFlowOut Z g ι q).2) (0, s) v =
      v.1 • Z (ι s) + mfderiv J I ι s v.2 := by
  obtain ⟨-, hD0, hΨ, hΨ0⟩ := transportFlowOut_basic hZ hg hι
  have hW1 := contMDiff_one_transportField hZ hg
  have hΦd : MDifferentiableAt (𝓘(ℝ).prod J) I (fun q ↦ (transportFlowOut Z g ι q).2) (0, s) :=
    (contMDiffAt_snd.comp _ (hΨ _ (hD0 s))).mdifferentiableAt (by simp)
  rw [mfderiv_prod_eq_add_apply hΦd]
  have hspace : (fun z : S ↦ (transportFlowOut Z g ι (0, z)).2) = ι := funext fun z ↦ by rw [hΨ0]
  rw [hspace]
  congr 1
  -- The time part is the derivative of the trajectory through `(0, ι s)`, read in `M`.
  have htraj : MDifferentiableAt 𝓘(ℝ) (𝓘(ℝ).prod I)
      (fun τ : ℝ ↦ flowOf (transportField Z g) τ ((0 : ℝ), ι s)) 0 :=
    mdifferentiableAt_flowOf hW1 (mem_flowDomain_zero hW1 _)
  refine (mfderiv_comp_apply (g := Prod.snd) (0 : ℝ) mdifferentiableAt_snd htraj v.1).trans ?_
  rw [mfderiv_snd, mfderiv_flowOf_trajectory_zero_apply hW1, transportField_apply]
  -- The second component of `a • (g (ι s), Z (ι s))` is `a • Z (ι s)`. The simp lemma
  -- `ContinuousLinearMap.snd_apply` does not fire, because the tangent space of `ℝ × M` is only
  -- definitionally the product of the tangent spaces; `ContinuousLinearMap.snd` is `Prod.snd` by
  -- definition.
  rfl

/-- **The flow out of a transverse slice is a local diffeomorphism along the slice.** At a point
`s` where `ι` has injective differential and `Z (ι s)` is not tangent to `ι`, the `M`-component of
the flow out of the slice is a local diffeomorphism at `(0, s)`. -/
private theorem isLocalDiffeomorphAt_snd_transportFlowOut [FiniteDimensional ℝ E']
    (hZ : ContMDiff I I.tangent ∞ (T% Z)) (hg : ContMDiff I 𝓘(ℝ) ∞ g) (hι : ContMDiff J I ∞ ι)
    (hdim : finrank ℝ E = finrank ℝ E' + 1) {s : S} (himm : Injective (mfderiv J I ι s))
    (htr : Z (ι s) ∉ (mfderiv J I ι s).range) :
    IsLocalDiffeomorphAt (𝓘(ℝ).prod J) I ∞ (fun q ↦ (transportFlowOut Z g ι q).2) (0, s) := by
  obtain ⟨hD, hD0, hΨ, -⟩ := transportFlowOut_basic hZ hg hι
  -- Transversality makes the differential `(a, w) ↦ a Z (ι s) + dι w` injective.
  have hinj :
      Injective (mfderiv (𝓘(ℝ).prod J) I (fun q ↦ (transportFlowOut Z g ι q).2) (0, s)) := by
    refine (injective_iff_map_eq_zero _).2 fun v hv ↦ ?_
    obtain ⟨a, w⟩ := v
    obtain ⟨rfl, rfl⟩ := (smul_add_mfderiv_eq_zero_iff himm htr).1
      ((mfderiv_snd_transportFlowOut_zero_apply hZ hg hι s (a, w)).symm.trans hv)
    rfl
  -- Source and target have the same dimension, so the inverse function theorem applies.
  exact isLocalDiffeomorphAt_of_injective_mfderiv
    (fun q hq ↦ (contMDiffAt_snd.comp q (hΨ q hq)).contMDiffWithinAt) hD (hD0 s)
    BoundarylessManifold.isInteriorPoint (by simp) hinj
    (by rw [Module.finrank_prod, Module.finrank_self, hdim, add_comm])

omit [TopologicalSpace S] [FiniteDimensional ℝ E] [BoundarylessManifold J S]
  [IsManifold J ∞ S] in
/-- **The transport equation along the flow out of the slice.** If a function `k` on `M`,
differentiable at `Φ q`, agrees near `q` along the trajectory through `q` with the real component
of the flow out of the slice, `k (Φ (τ, s)) = H (τ, s)`, then `Z k = g` at `Φ q`: the real
component grows at the rate `g` along the trajectories, which `Φ` carries to those of `Z`. -/
private theorem mvfderiv_apply_eq_of_eventually
    (hZ : ContMDiff I I.tangent ∞ (T% Z)) (hg : ContMDiff I 𝓘(ℝ) ∞ g) {q : ℝ × S}
    (hq : q ∈ transportFlowOutDomain Z g ι) {k : M → ℝ}
    (hk : MDifferentiableAt I 𝓘(ℝ) k (transportFlowOut Z g ι q).2)
    (hkH : ∀ᶠ τ in 𝓝 q.1,
      k (transportFlowOut Z g ι (τ, q.2)).2 = (transportFlowOut Z g ι (τ, q.2)).1) :
    mvfderiv I k (transportFlowOut Z g ι q).2 (Z (transportFlowOut Z g ι q).2) =
      g (transportFlowOut Z g ι q).2 := by
  have hW1 := contMDiff_one_transportField hZ hg
  -- Differentiate `k` along the trajectory, and the real coordinate along the same trajectory.
  have h1 := hasDerivAt_comp_flowOf hW1 (g := k ∘ Prod.snd) hq
    (hk.comp (transportFlowOut Z g ι q) mdifferentiableAt_snd)
  have h2 := hasDerivAt_comp_flowOf hW1 (g := Prod.fst) hq mdifferentiableAt_fst
  rw [mvfderiv_comp_snd_apply] at h1
  have h3 := h1.unique (h2.congr_of_eventuallyEq hkH)
  -- The derivative of the real coordinate of `ℝ × M` is the real component of a tangent vector.
  rw [mvfderiv_apply_eq_mfderiv_apply, mfderiv_fst, transportField_apply] at h3
  -- Both sides are read at the point `Φ q`, which is `transportFlowOut Z g ι q` by definition,
  -- and `ContinuousLinearMap.fst` is `Prod.fst` by definition; as above, its simp lemma does not
  -- fire on the tangent space of `ℝ × M`.
  exact h3

/-- By compactness, the `M`-component of the flow out of a transverse slice is injective and a
local diffeomorphism on an open neighbourhood of `{0} × K` in its domain. -/
private theorem exists_isOpen_injOn_isLocalDiffeomorphOn_snd_transportFlowOut
    (hZ : ContMDiff I I.tangent ∞ (T% Z)) (hg : ContMDiff I 𝓘(ℝ) ∞ g) (hι : ContMDiff J I ∞ ι)
    (hdim : finrank ℝ E = finrank ℝ E' + 1) {K : Set S} (hK : IsCompact K) (hinj : InjOn ι K)
    (himm : ∀ s ∈ K, Injective (mfderiv J I ι s))
    (htr : ∀ s ∈ K, Z (ι s) ∉ (mfderiv J I ι s).range) :
    ∃ U ⊆ transportFlowOutDomain Z g ι, IsOpen U ∧ (∀ s ∈ K, ((0 : ℝ), s) ∈ U) ∧
      InjOn (fun q ↦ (transportFlowOut Z g ι q).2) U ∧
      IsLocalDiffeomorphOn (𝓘(ℝ).prod J) I ∞ (fun q ↦ (transportFlowOut Z g ι q).2) U := by
  rcases K.eq_empty_or_nonempty with rfl | ⟨s₀, hs₀⟩
  · exact ⟨∅, empty_subset _, isOpen_empty, by simp, injOn_empty _, fun q ↦ q.2.elim⟩
  -- The tangent spaces of `S` embed in those of `M`, so `S` is finite-dimensional.
  have : FiniteDimensional ℝ E' := finiteDimensional_of_injective_mfderiv (himm s₀ hs₀)
  obtain ⟨hD, hD0, -, hΨ0⟩ := transportFlowOut_basic hZ hg hι
  obtain ⟨U, hUo, hKU, hUinj, hUloc⟩ :=
    (show InjOn (fun q ↦ (transportFlowOut Z g ι q).2) ((fun s ↦ ((0 : ℝ), s)) '' K) by
        rintro _ ⟨s, hs, rfl⟩ _ ⟨s', hs', rfl⟩ hss'
        simp only [hΨ0] at hss'
        rw [hinj hs hs' hss']).exists_isOpen_superset_isLocalDiffeomorphOn
      (hK.image (continuous_const.prodMk continuous_id)) (by
        rintro _ ⟨s, hs, rfl⟩
        exact isLocalDiffeomorphAt_snd_transportFlowOut hZ hg hι hdim (himm s hs) (htr s hs))
  exact ⟨U ∩ transportFlowOutDomain Z g ι, inter_subset_right, hUo.inter hD,
    fun s hs ↦ ⟨hKU ⟨s, hs, rfl⟩, hD0 s⟩, hUinj.mono inter_subset_left,
    fun q ↦ hUloc ⟨q, q.2.1⟩⟩

/-- **Local solutions of the transport equation.** Let `Z` be a smooth vector field and `g` a
smooth function on a finite-dimensional boundaryless Hausdorff manifold `M`, and let `ι : S → M`
be smooth from a boundaryless manifold of one dimension less. Let `K ⊆ S` be compact, with `ι`
injective on `K`, with injective differential at every point of `K`, and with `Z (ι s)` outside the
range of `dι_s` for `s ∈ K`. Then there are an open neighbourhood `V` of `ι(K)` and a function `h`,
smooth on `V`, with `Z h = g` on `V` and `h ∘ ι = 0` near `K`. -/
theorem exists_isOpen_contMDiffOn_mvfderiv_eq
    (hZ : ContMDiff I I.tangent ∞ (T% Z)) (hg : ContMDiff I 𝓘(ℝ) ∞ g)
    (hι : ContMDiff J I ∞ ι) (hdim : finrank ℝ E = finrank ℝ E' + 1) {K : Set S}
    (hK : IsCompact K) (hinj : InjOn ι K)
    (himm : ∀ s ∈ K, Injective (mfderiv J I ι s))
    (htr : ∀ s ∈ K, Z (ι s) ∉ (mfderiv J I ι s).range) :
    ∃ V : Set M, IsOpen V ∧ ι '' K ⊆ V ∧ ∃ h : M → ℝ, ContMDiffOn I 𝓘(ℝ) ∞ h V ∧
      (∀ x ∈ V, mvfderiv I h x (Z x) = g x) ∧ ∀ᶠ s in 𝓝ˢ K, h (ι s) = 0 := by
  rcases isEmpty_or_nonempty S with hS | ⟨⟨s₀⟩⟩
  · exact ⟨∅, isOpen_empty, by simp [eq_empty_of_isEmpty K], 0, contMDiffOn_empty, by simp,
      by simp [eq_empty_of_isEmpty K]⟩
  have : Nonempty (ℝ × S) := ⟨(0, s₀)⟩
  obtain ⟨-, -, hΨ, hΨ0⟩ := transportFlowOut_basic hZ hg hι
  obtain ⟨U, hUD, hUo, hKU, hUinj, hUloc⟩ :=
    exists_isOpen_injOn_isLocalDiffeomorphOn_snd_transportFlowOut hZ hg hι hdim hK hinj himm htr
  -- The solution is the real component of the flow, read through the inverse of `Φ` on `U`.
  set Φ := fun q ↦ (transportFlowOut Z g ι q).2
  set Φinv := invFunOn Φ U
  have hΦinv (q : ℝ × S) (hq : q ∈ U) : Φinv (Φ q) = q := hUinj.leftInvOn_invFunOn hq
  have hVo : IsOpen (Φ '' U) := hUloc.isLocalHomeomorphOn.isOpen_image hUo
  have hsol : ContMDiffOn I 𝓘(ℝ) ∞ (fun x ↦ (transportFlowOut Z g ι (Φinv x)).1) (Φ '' U) :=
    (contMDiff_fst.comp_contMDiffOn fun q (hq : q ∈ U) ↦ (hΨ q (hUD hq)).contMDiffWithinAt).comp
      (hUloc.contMDiffOn_invFunOn hUo hUinj) fun x hx ↦ invFunOn_mem hx
  refine ⟨Φ '' U, hVo, ?_, fun x ↦ (transportFlowOut Z g ι (Φinv x)).1, hsol, ?_, ?_⟩
  · rintro _ ⟨s, hs, rfl⟩
    exact ⟨_, hKU s hs, congrArg Prod.snd (hΨ0 s)⟩
  · rintro _ ⟨q, hq, rfl⟩
    refine mvfderiv_apply_eq_of_eventually hZ hg (hUD hq)
      ((hsol.contMDiffAt (hVo.mem_nhds ⟨q, hq, rfl⟩)).mdifferentiableAt (by simp)) ?_
    filter_upwards [(hUo.preimage (continuous_id.prodMk continuous_const)).mem_nhds hq] with τ hτ
    rw [hΦinv (τ, q.2) hτ]
  · filter_upwards [(hUo.preimage (continuous_const.prodMk continuous_id)).mem_nhdsSet.2
      fun s hs ↦ hKU s hs] with s hs
    have hι0 : Φ (0, s) = ι s := congrArg Prod.snd (hΨ0 s)
    rw [← hι0, hΦinv ((0 : ℝ), s) hs, hΨ0]

/-- **Solutions of the transport equation with zero values on a transverse slice.** Let `Z` be a
smooth vector field and `g` a smooth function on a finite-dimensional boundaryless Hausdorff
σ-compact manifold `M`, and let `ι : S → M` be smooth from a boundaryless manifold of one dimension
less. Let `K ⊆ S` be compact, with `ι` injective on `K`, with injective differential at every point
of `K`, and with `Z (ι s)` outside the range of `dι_s` for `s ∈ K`. Then there is a smooth function
`h` on `M` with `Z h = g` near `ι(K)` and `h ∘ ι = 0` near `K`. -/
theorem exists_contMDiff_mvfderiv_eq [SigmaCompactSpace M] (hZ : ContMDiff I I.tangent ∞ (T% Z))
    (hg : ContMDiff I 𝓘(ℝ) ∞ g) (hι : ContMDiff J I ∞ ι) (hdim : finrank ℝ E = finrank ℝ E' + 1)
    {K : Set S} (hK : IsCompact K) (hinj : InjOn ι K)
    (himm : ∀ s ∈ K, Injective (mfderiv J I ι s))
    (htr : ∀ s ∈ K, Z (ι s) ∉ (mfderiv J I ι s).range) :
    ∃ h : M → ℝ, ContMDiff I 𝓘(ℝ) ∞ h ∧ (∀ᶠ x in 𝓝ˢ (ι '' K), mvfderiv I h x (Z x) = g x) ∧
      ∀ᶠ s in 𝓝ˢ K, h (ι s) = 0 := by
  obtain ⟨V, hVo, hKV, h, hh, hZh, hι0⟩ :=
    exists_isOpen_contMDiffOn_mvfderiv_eq hZ hg hι hdim hK hinj himm htr
  have hKc : IsCompact (ι '' K) := hK.image hι.continuous
  have : LocallyCompactSpace H := I.locallyCompactSpace
  have : LocallyCompactSpace M := ChartedSpace.locallyCompactSpace H M
  -- Extend the local solution from a closed neighbourhood of `ι(K)` inside `V` to all of `M`.
  obtain ⟨O, hOo, hKO, hOV⟩ := normal_exists_closure_subset hKc.isClosed hVo hKV
  obtain ⟨G, hG, -⟩ := isClosed_closure.exists_contMDiffMap_eqOn (n := ⊤) (g := h) hVo hOV
    fun x hx ↦ ⟨V, hVo.mem_nhds (hOV hx), h, hh, eqOn_refl _ _⟩
  have heq (x : M) (hx : x ∈ O) : (G : M → ℝ) =ᶠ[𝓝 x] h := by
    filter_upwards [hOo.mem_nhds hx] with y hy using hG (subset_closure hy)
  refine ⟨G, G.contMDiff, ?_, ?_⟩
  · filter_upwards [hOo.mem_nhdsSet.2 hKO] with x hx
    rw [(heq x hx).mvfderiv_eq, hZh x (hOV (subset_closure hx))]
  · filter_upwards [hι0, (hOo.preimage hι.continuous).mem_nhdsSet.2
      fun s hs ↦ hKO (mem_image_of_mem ι hs)] with s hs hsO
    rw [hG (subset_closure hsO), hs]

end Local

/-! ### Families of vector fields -/

section ProdMapId

variable {F G P : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace G]
  {L : ModelWithCorners ℝ F G} [TopologicalSpace P] [ChartedSpace G P]
  {v : P → (x : M) → TangentSpace I x} {ι : S → M}

/-- The vertical field of the family `v` is transverse to `id × ι` at `(a, s)` when `v a` is
transverse to `ι` at `s`. -/
private theorem verticalField_notMem_range_mfderiv_prodMap_id (hι : ContMDiff J I ∞ ι)
    {z : P × S} (htr : v z.1 (ι z.2) ∉ (mfderiv J I ι z.2).range) :
    verticalField L v (Prod.map id ι z) ∉
      (mfderiv (L.prod J) (L.prod I) (Prod.map id ι) z).range := fun hmem ↦ by
  obtain ⟨w, hw⟩ := LinearMap.mem_range.1 hmem
  have h' := Manifold.mfderiv_prodMap_apply (mdifferentiableAt_id (I := L))
    ((hι.mdifferentiable (by simp)) z.2) (Manifold.tangentSpaceProdEquiv z w)
  rw [ContinuousLinearEquiv.symm_apply_apply, Manifold.tangentSpaceProdEquiv_symm_apply] at h'
  replace h' := congrArg Prod.snd (hw.symm.trans h')
  simp only [verticalField_snd, Prod.map_fst, Prod.map_snd, id_eq,
    Manifold.tangentSpaceProdEquiv_apply] at h'
  exact htr (LinearMap.mem_range.2 ⟨w.2, h'.symm⟩)

end ProdMapId

section Param

variable [FiniteDimensional ℝ E] [T2Space M] [BoundarylessManifold I M] [IsManifold I ∞ M]
  [SigmaCompactSpace M] [BoundarylessManifold J S] [IsManifold J ∞ S]
  {F G P : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  [TopologicalSpace G] {L : ModelWithCorners ℝ F G} [TopologicalSpace P] [ChartedSpace G P]
  [T2Space P] [BoundarylessManifold L P] [IsManifold L ∞ P] [SigmaCompactSpace P]
  {v : P → (x : M) → TangentSpace I x} {g : P × M → ℝ} {ι : S → M}

/-- **Solutions of the transport equation for a family of vector fields.** Let `v a` be a family
of vector fields on `M` and `g a` a family of functions, both jointly smooth in the parameter `a`
of a finite-dimensional boundaryless Hausdorff σ-compact manifold `P` and the point of `M`. Let
`ι : S → M`, `K ⊆ S` be as in `TauCeti.exists_contMDiff_mvfderiv_eq`, and let `T ⊆ P` be compact,
with `v a` transverse to `ι` along `K` for every `a ∈ T`. Then there is a jointly smooth function
`h` on `P × M` such that `h_a = h (a, ·)` solves `v a (h_a) = g a` near `T × ι(K)`, vanishes on the
slice near `T × K`, and has zero differential at `ι s` whenever `a ∈ T`, `s ∈ K` and
`g a (ι s) = 0`. -/
theorem exists_contMDiff_mvfderiv_eq_param
    (hv : ContMDiff (L.prod I) I.tangent ∞
      (fun z : P × M ↦ (⟨z.2, v z.1 z.2⟩ : TangentBundle I M)))
    (hg : ContMDiff (L.prod I) 𝓘(ℝ) ∞ g) (hι : ContMDiff J I ∞ ι)
    (hdim : finrank ℝ E = finrank ℝ E' + 1) {T : Set P} (hT : IsCompact T) {K : Set S}
    (hK : IsCompact K) (hinj : InjOn ι K) (himm : ∀ s ∈ K, Injective (mfderiv J I ι s))
    (htr : ∀ a ∈ T, ∀ s ∈ K, v a (ι s) ∉ (mfderiv J I ι s).range) :
    ∃ h : P × M → ℝ, ContMDiff (L.prod I) 𝓘(ℝ) ∞ h ∧
      (∀ᶠ z in 𝓝ˢ (T ×ˢ (ι '' K)), mvfderiv I (fun y ↦ h (z.1, y)) z.2 (v z.1 z.2) = g z) ∧
      (∀ᶠ z in 𝓝ˢ (T ×ˢ K), h (z.1, ι z.2) = 0) ∧
      ∀ a ∈ T, ∀ s ∈ K, g (a, ι s) = 0 → mvfderiv I (fun y ↦ h (a, y)) (ι s) = 0 := by
  rcases K.eq_empty_or_nonempty with rfl | ⟨s₀, hs₀⟩
  · exact ⟨0, contMDiff_const, by simp, by simp, by simp⟩
  -- The tangent spaces of `S` embed in those of `M`, so `S` is finite-dimensional.
  have : FiniteDimensional ℝ E' := finiteDimensional_of_injective_mfderiv (himm s₀ hs₀)
  -- Apply the single-field statement to the vertical field on `P × M` and the slice `id × ι`.
  have hι' : ContMDiff (L.prod J) (L.prod I) ∞ (Prod.map id ι) :=
    (contMDiff_id (I := L) (M := P)).prodMap hι
  have hdim' : finrank ℝ (F × E) = finrank ℝ (F × E') + 1 := by
    rw [Module.finrank_prod, Module.finrank_prod, hdim, add_assoc]
  have himm' (z : P × S) (hz : z.2 ∈ K) :
      Injective (mfderiv (L.prod J) (L.prod I) (Prod.map id ι) z) :=
    Manifold.injective_mfderiv_prodMap mdifferentiableAt_id ((hι.mdifferentiable (by simp)) z.2)
      (by rw [mfderiv_id]; exact injective_id) (himm z.2 hz)
  obtain ⟨h, hh, hZh, hι0⟩ := exists_contMDiff_mvfderiv_eq (contMDiff_verticalField hv)
    (I := L.prod I) hg hι' hdim' (hT.prod hK)
    (fun z hz z' hz' hzz' ↦ by
      simp only [Prod.map, id_eq, Prod.mk.injEq] at hzz'
      exact Prod.ext hzz'.1 (hinj hz.2 hz'.2 hzz'.2))
    (fun z hz ↦ himm' z hz.2)
    (fun z hz ↦ verticalField_notMem_range_mfderiv_prodMap_id hι (htr z.1 hz.1 z.2 hz.2))
  -- The derivative of a slice `h (a, ·)` along `v a` is that of `h` along the vertical field.
  have hslice (z : P × M) (w : TangentSpace I z.2) : mvfderiv I (fun y ↦ h (z.1, y)) z.2 w =
      mvfderiv (L.prod I) h z (mfderiv I (L.prod I) (Prod.mk z.1) z.2 w) :=
    mvfderiv_comp_apply (f := Prod.mk z.1) z.2 ((hh.mdifferentiable (by simp)) _)
      ((mdifferentiableAt_const (I' := L)).prodMk (mdifferentiableAt_id (I := I))) w
  have himage : Prod.map id ι '' T ×ˢ K = T ×ˢ (ι '' K) := by
    rw [prodMap_image_prod, image_id]
  rw [himage] at hZh
  refine ⟨h, hh, ?_, hι0, fun a ha s hs hg0 ↦ ?_⟩
  · filter_upwards [hZh] with z hz
    rw [hslice, mfderiv_prodMk_apply_verticalField]
    exact hz
  · -- The differential of `h` vanishes at `(a, ι s)`, by transversality of the vertical field.
    have hzero : mvfderiv (L.prod I) h (a, ι s) = 0 :=
      mvfderiv_eq_zero_of_eventuallyEq_zero (Z := verticalField L v) (s := (a, s)) hdim'
        ((hh.mdifferentiable (by simp)) _) ((hι'.mdifferentiable (by simp)) (a, s))
        (hι0.filter_mono (nhds_le_nhdsSet (show (a, s) ∈ T ×ˢ K from ⟨ha, hs⟩)))
        (himm' (a, s) hs)
        (verticalField_notMem_range_mfderiv_prodMap_id hι (htr a ha s hs))
        ((hZh.self_of_nhdsSet (a, ι s)
          (show (a, ι s) ∈ T ×ˢ (ι '' K) from ⟨ha, mem_image_of_mem ι hs⟩)).trans hg0)
    refine ContinuousLinearMap.ext fun w ↦ ?_
    rw [hslice (a, ι s), hzero, zero_apply, zero_apply]

end Param

end TauCeti
