/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.VectorBundle.FirstJet.Basic
public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.LocalFrame
public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Trivial
public import TauCeti.Topology.VectorBundle.Coordinates

/-!
# The splitting of the first-jet sequence by a connection

Let `V → M` be a finite-rank `C^1` vector bundle. Its first jets fit in the exact sequence

`0 → Hom(TₓM, Vₓ) → J¹Vₓ → Vₓ → 0`

of `TauCeti.FirstJetBundle.ofDeriv` and `TauCeti.FirstJetBundle.value`. A covariant derivative
`∇` on `V` splits it. Its connection map `K = CovariantDerivative.firstJetSplitting ∇ x` is the
continuous linear map `J¹Vₓ → Hom(TₓM, Vₓ)` sending the first jet of every section `σ`
differentiable at `x` to `∇σ(x)`, and it is a left inverse of the inclusion
`Hom(TₓM, Vₓ) → J¹Vₓ`. In the chart and trivialization at `x`, a first jet `(w, A)` is sent to
`A` read back in `Vₓ` plus the covariant derivative at `x` of the section with constant
coordinates `w`. In particular `∇σ(x)` depends only on the first jet of `σ` at `x`.

The kernel of `K` is the horizontal subspace. It is the image of the horizontal lift
`CovariantDerivative.firstJetLift ∇ x : Vₓ → J¹Vₓ`, a right inverse of the value map; a section
`σ` differentiable at `x` has first jet the horizontal lift of `σ x` exactly when `∇σ(x) = 0`.
Together these give the
decomposition `J¹Vₓ ≃ Vₓ × Hom(TₓM, Vₓ)`, `j ↦ (value j, K j)`, under which `j¹σ(x)` becomes
`(σ x, ∇σ(x))`.

Changing the connection changes the splitting by the difference one-form evaluated on the value
coordinate: `K_{∇ + A}(j) = K_∇(j) + A(value j)`, and the horizontal lift by minus the inclusion
of `A v`. For instance, on a trivial bundle the first jet of a section `σ` is `(σ x, dσ(x))` for
the canonical flat connection and `(σ x, dσ(x) + A (σ x))` for the connection `d + A`; for a
constant section `v` these are `(v, 0)` and `(v, A v)`.

## Main definitions and results

* `CovariantDerivative.firstJetSplitting`: the connection map `J¹Vₓ → Hom(TₓM, Vₓ)`, with
  `CovariantDerivative.firstJetSplitting_jet` (`K (j¹σ(x)) = ∇σ(x)`) and
  `CovariantDerivative.firstJetSplitting_ofDeriv` (`K ∘ ofDeriv = id`).
* `CovariantDerivative.eq_firstJetSplitting_iff`: the connection map is the unique continuous
  linear map sending the first jet of every section differentiable at `x` to `∇σ(x)`.
* `CovariantDerivative.congr_of_jet_eq`: the covariant derivative at `x` of a section
  differentiable at `x` depends only on its first jet at `x`.
* `CovariantDerivative.firstJetSplitting_addOneForm` and
  `CovariantDerivative.firstJetSplitting_sub_firstJetSplitting`: the change of splitting under a
  change of connection.
* `CovariantDerivative.firstJetLift`: the horizontal lift `Vₓ → J¹Vₓ`, with its coordinates
  `CovariantDerivative.firstJetLift_fst` and `CovariantDerivative.firstJetLift_snd`,
  `CovariantDerivative.value_firstJetLift`, `CovariantDerivative.firstJetSplitting_firstJetLift`,
  `CovariantDerivative.eq_firstJetLift_iff`, `CovariantDerivative.ker_firstJetSplitting` and
  `CovariantDerivative.jet_eq_firstJetLift_iff`, and its change under a change of connection
  `CovariantDerivative.firstJetLift_addOneForm` and
  `CovariantDerivative.firstJetLift_sub_firstJetLift`.
* `CovariantDerivative.firstJetEquiv`: the decomposition `J¹Vₓ ≃L Vₓ × Hom(TₓM, Vₓ)`, with
  `CovariantDerivative.firstJetEquiv_jet`.
* `CovariantDerivative.firstJetEquiv_trivial_jet` and
  `CovariantDerivative.firstJetEquiv_addOneForm_trivial_jet`: the decomposition of the first jet
  of a section of a trivial bundle by `d` and by `d + A`.

## References

* I. Kolář, P. W. Michor and J. Slovák, *Natural Operations in Differential Geometry*, §17
  (connections as splittings of first-jet sequences).
* D. J. Saunders, *The Geometry of Jet Bundles*, London Math. Soc. Lecture Note Series 142,
  Chapter 4.
-/

public section

noncomputable section

open Bundle Set Filter
open scoped Manifold Topology ContDiff

namespace CovariantDerivative

open TauCeti TauCeti.FirstJetBundle TauCeti.Manifold

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners 𝕜 E H} {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F] [FiniteDimensional 𝕜 F]
  {V : M → Type*} [TopologicalSpace (TotalSpace F V)] [∀ x, AddCommGroup (V x)]
  [∀ x, Module 𝕜 (V x)] [∀ x, TopologicalSpace (V x)] [∀ x, IsTopologicalAddGroup (V x)]
  [∀ x, ContinuousSMul 𝕜 (V x)] [FiberBundle F V] [VectorBundle 𝕜 F V]
  [IsManifold I 1 M] [ContMDiffVectorBundle 1 F V I]

/-- The **connection map** `J¹Vₓ → Hom(TₓM, Vₓ)` of a covariant derivative: the continuous linear
map sending the first jet of every section `σ` differentiable at `x` to `∇σ(x)`
(`CovariantDerivative.firstJetSplitting_jet`). It is a left inverse of the inclusion
`TauCeti.FirstJetBundle.ofDeriv` (`CovariantDerivative.firstJetSplitting_ofDeriv`), so it splits
the first-jet sequence. -/
def firstJetSplitting (cov : CovariantDerivative I F V) (x : M) :
    FirstJetBundle I F V x →L[𝕜] TangentSpace I x →L[𝕜] V x :=
  (ContinuousLinearMap.postcomp (TangentSpace I x) ((trivializationAt F V x).symmL 𝕜 x) ∘L
      ContinuousLinearMap.snd 𝕜 F (E →L[𝕜] F) :
      FirstJetBundle I F V x →L[𝕜] TangentSpace I x →L[𝕜] V x) +
    (christoffelForm (I := I) (Module.finBasis 𝕜 F) (e := trivializationAt F V x)
        (cov.isCovariantDerivativeOn (s := (trivializationAt F V x).baseSet)) x ∘L
      value I F x : FirstJetBundle I F V x →L[𝕜] TangentSpace I x →L[𝕜] V x)

/-- The connection map in the chart and trivialization at `x`, through the Christoffel form of the
covariant derivative in the frame of an arbitrary basis of the model fibre. -/
private theorem firstJetSplitting_apply_christoffelForm (cov : CovariantDerivative I F V) (x : M)
    (j : FirstJetBundle I F V x) :
    cov.firstJetSplitting x j =
      (((trivializationAt F V x).symmL 𝕜 x).comp j.2 : TangentSpace I x →L[𝕜] V x) +
      christoffelForm (I := I) (Module.finBasis 𝕜 F) (e := trivializationAt F V x)
        (cov.isCovariantDerivativeOn (s := (trivializationAt F V x).baseSet)) x (value I F x j) :=
  (rfl)

/-- **The connection map sends the first jet of a section to its covariant derivative.** -/
theorem firstJetSplitting_jet (cov : CovariantDerivative I F V) {σ : Π x, V x} {x : M}
    (hσ : MDifferentiableAt I (I.prod 𝓘(𝕜, F)) (fun x ↦ TotalSpace.mk' F x (σ x)) x) :
    cov.firstJetSplitting x (jet I F σ x) = cov σ x := by
  set e := trivializationAt F V x
  have hx : x ∈ e.baseSet := mem_baseSet_trivializationAt F V x
  have hg : MDifferentiableAt I 𝓘(𝕜, F) (fun y ↦ (e ⟨y, σ y⟩).2) x :=
    (e.mdifferentiableAt_section_iff I σ hx).1 hσ
  rw [covariantDerivative_eq_add_christoffelForm (Module.finBasis 𝕜 F)
      (cov.isCovariantDerivativeOn (s := e.baseSet)) hx hσ,
    frameCovariantDerivative_eq_symmL_comp (Module.finBasis 𝕜 F) hg.hasMFDerivAt _ hx,
    firstJetSplitting_apply_christoffelForm, value_jet, jet_snd_eq_mfderiv I F σ x]
  -- The frame coefficients of `σ` are the coordinates of its trivialization.
  intro i
  filter_upwards [e.open_baseSet.mem_nhds hx] with z hz
  rw [e.localFrameCoeff_eq_coeff hz, Module.Basis.coord_apply]

/-- **The connection map in coordinates.** In the chart and trivialization `e` at `x`, the
connection map sends a first jet `(w, A)` to `A` read back in `Vₓ` plus the covariant derivative
at `x` of the section `y ↦ e.symm y w` with constant coordinates `w`. -/
theorem firstJetSplitting_apply (cov : CovariantDerivative I F V) (x : M)
    (j : FirstJetBundle I F V x) :
    cov.firstJetSplitting x j =
      (((trivializationAt F V x).symmL 𝕜 x).comp j.2 : TangentSpace I x →L[𝕜] V x) +
        cov (fun y ↦ (trivializationAt F V x).symm y j.1) x := by
  rw [firstJetSplitting_apply_christoffelForm, value_apply,
    ← covariantDerivative_symm_eq_christoffelForm
    (Module.finBasis 𝕜 F) _ (mem_baseSet_trivializationAt F V x)]

/-- The connection map is a left inverse of the inclusion `Hom(TₓM, Vₓ) → J¹Vₓ`. -/
@[simp]
theorem firstJetSplitting_ofDeriv (cov : CovariantDerivative I F V) (x : M)
    (L : TangentSpace I x →L[𝕜] V x) :
    cov.firstJetSplitting x (ofDeriv I F x L) = L := by
  rw [firstJetSplitting_apply_christoffelForm, value_ofDeriv, map_zero, add_zero]
  ext v
  rw [ofDeriv_apply]
  -- Both compositions evaluate pointwise, so this is `e.symmL x (e.continuousLinearMapAt x (L v))`.
  exact (trivializationAt F V x).symmL_continuousLinearMapAt (R := 𝕜)
    (mem_baseSet_trivializationAt F V x) (L v)

/-- **A connection splits the first-jet sequence**: its connection map composed with the inclusion
`Hom(TₓM, Vₓ) → J¹Vₓ` is the identity. -/
@[simp]
theorem firstJetSplitting_comp_ofDeriv (cov : CovariantDerivative I F V) (x : M) :
    cov.firstJetSplitting x ∘L ofDeriv I F x = ContinuousLinearMap.id 𝕜 _ :=
  ContinuousLinearMap.ext (cov.firstJetSplitting_ofDeriv x)

/-- The covariant derivative at `x` of a section differentiable at `x` depends only on its first
jet at `x`. -/
theorem congr_of_jet_eq (cov : CovariantDerivative I F V) {σ σ' : Π x, V x} {x : M}
    (hσ : MDifferentiableAt I (I.prod 𝓘(𝕜, F)) (fun x ↦ TotalSpace.mk' F x (σ x)) x)
    (hσ' : MDifferentiableAt I (I.prod 𝓘(𝕜, F)) (fun x ↦ TotalSpace.mk' F x (σ' x)) x)
    (h : jet I F σ x = jet I F σ' x) :
    cov σ x = cov σ' x := by
  rw [← cov.firstJetSplitting_jet hσ, h, cov.firstJetSplitting_jet hσ']

/-- **Characterization of the connection map.** A continuous linear map `J¹Vₓ → Hom(TₓM, Vₓ)` is
the connection map exactly when it sends the first jet of every section `σ` differentiable at `x`
to `∇σ(x)`. -/
theorem eq_firstJetSplitting_iff (cov : CovariantDerivative I F V) {x : M}
    {K : FirstJetBundle I F V x →L[𝕜] TangentSpace I x →L[𝕜] V x} :
    K = cov.firstJetSplitting x ↔ ∀ σ : Π y, V y,
      MDifferentiableAt I (I.prod 𝓘(𝕜, F)) (fun y ↦ TotalSpace.mk' F y (σ y)) x →
        K (jet I F σ x) = cov σ x := by
  refine ⟨by rintro rfl σ hσ; exact cov.firstJetSplitting_jet hσ, fun h ↦ ?_⟩
  refine ContinuousLinearMap.ext fun j ↦ ?_
  -- Every first jet is the first jet of a section differentiable at `x`.
  obtain ⟨σ, hσ, rfl⟩ := exists_contMDiffAt_jet_eq I F (n := 1) x j
  rw [h σ (hσ.mdifferentiableAt one_ne_zero),
    cov.firstJetSplitting_jet (hσ.mdifferentiableAt one_ne_zero)]

/-- **Change of splitting.** Adding an endomorphism-valued one-form `A` to a connection adds
`A` applied to the value of a first jet to its image under the connection map. -/
@[simp]
theorem firstJetSplitting_addOneForm (cov : CovariantDerivative I F V)
    (A : Π x : M, V x →L[𝕜] TangentSpace I x →L[𝕜] V x) (x : M) (j : FirstJetBundle I F V x) :
    (cov.addOneForm A).firstJetSplitting x j = cov.firstJetSplitting x j + A x (value I F x j) := by
  rw [firstJetSplitting_apply, firstJetSplitting_apply, addOneForm_apply, value_apply,
    add_assoc]

/-- **Change of splitting.** The connection maps of two connections differ by their difference
one-form applied to the value of a first jet. -/
theorem firstJetSplitting_sub_firstJetSplitting (cov cov' : CovariantDerivative I F V) (x : M)
    (j : FirstJetBundle I F V x) :
    cov.firstJetSplitting x j - cov'.firstJetSplitting x j =
      cov.difference cov' x (value I F x j) := by
  have hx := mem_baseSet_trivializationAt F V x
  -- The section with constant coordinates `j.1` in the trivialization at `x` is differentiable.
  have hσ : MDifferentiableAt I (I.prod 𝓘(𝕜, F))
      (fun y ↦ TotalSpace.mk' F y ((trivializationAt F V x).symm y j.1)) x :=
    ((contMDiffOn_symm_baseSet (I := I) j.1).mdifferentiableOn one_ne_zero).mdifferentiableAt
      ((trivializationAt F V x).open_baseSet.mem_nhds hx)
  rw [firstJetSplitting_apply, firstJetSplitting_apply, value_apply, cov.difference_apply cov' hσ]
  abel

/-- The **horizontal lift** `Vₓ → J¹Vₓ` of a covariant derivative: the right inverse of the value
map whose image is the kernel of the connection map. It sends `v` to the first jet with value
coordinate `v` and zero derivative coordinate in the trivialization at `x`, corrected by the
inclusion of its image under the connection map. -/
def firstJetLift (cov : CovariantDerivative I F V) (x : M) : V x →L[𝕜] FirstJetBundle I F V x :=
  (ContinuousLinearMap.inl 𝕜 F (E →L[𝕜] F) ∘L (trivializationAt F V x).continuousLinearMapAt 𝕜 x :
      V x →L[𝕜] FirstJetBundle I F V x) -
    ofDeriv I F x ∘L cov.firstJetSplitting x ∘L
      (ContinuousLinearMap.inl 𝕜 F (E →L[𝕜] F) ∘L
          (trivializationAt F V x).continuousLinearMapAt 𝕜 x : V x →L[𝕜] FirstJetBundle I F V x)

/-- The horizontal lift is a right inverse of the value map. -/
@[simp]
theorem value_firstJetLift (cov : CovariantDerivative I F V) (x : M) (v : V x) :
    value I F x (cov.firstJetLift x v) = v := by
  have hx := mem_baseSet_trivializationAt F V x
  rw [firstJetLift, sub_apply, map_sub, ContinuousLinearMap.comp_apply, value_ofDeriv, sub_zero,
    value_apply]
  -- The value coordinate of the jet `(e v, 0)` is `e v`.
  exact ((trivializationAt F V x).symmL_apply (R := 𝕜) hx _).symm.trans
    ((trivializationAt F V x).symmL_continuousLinearMapAt (R := 𝕜) hx v)

/-- The horizontal lift takes values in the kernel of the connection map. -/
@[simp]
theorem firstJetSplitting_firstJetLift (cov : CovariantDerivative I F V) (x : M) (v : V x) :
    cov.firstJetSplitting x (cov.firstJetLift x v) = 0 := by
  rw [firstJetLift, sub_apply, map_sub, ContinuousLinearMap.comp_apply,
    firstJetSplitting_ofDeriv, ContinuousLinearMap.comp_apply, sub_self]

/-- The horizontal lift composed with the value map is the identity. -/
@[simp]
theorem value_comp_firstJetLift (cov : CovariantDerivative I F V) (x : M) :
    value I F x ∘L cov.firstJetLift x = ContinuousLinearMap.id 𝕜 (V x) :=
  ContinuousLinearMap.ext (cov.value_firstJetLift x)

/-- The horizontal lift composed with the connection map is zero. -/
@[simp]
theorem firstJetSplitting_comp_firstJetLift (cov : CovariantDerivative I F V) (x : M) :
    cov.firstJetSplitting x ∘L cov.firstJetLift x = 0 :=
  ContinuousLinearMap.ext (cov.firstJetSplitting_firstJetLift x)

/-- Every first jet is the horizontal lift of its value plus the inclusion of its image under the
connection map. -/
@[simp]
theorem firstJetLift_value_add_ofDeriv_firstJetSplitting (cov : CovariantDerivative I F V)
    (x : M) (j : FirstJetBundle I F V x) :
    cov.firstJetLift x (value I F x j) + ofDeriv I F x (cov.firstJetSplitting x j) = j := by
  set d := j - cov.firstJetLift x (value I F x j) - ofDeriv I F x (cov.firstJetSplitting x j)
    with hdef
  have hd : value I F x d = 0 := by
    simp only [d, map_sub, value_ofDeriv, value_firstJetLift, sub_self]
  obtain ⟨L, hL⟩ : d ∈ LinearMap.range (ofDeriv I F (V := V) x).toLinearMap := by
    rw [range_ofDeriv]; exact hd
  have hL0 : L = 0 := by
    have h := congrArg (cov.firstJetSplitting x) hL
    simp only [ContinuousLinearMap.coe_coe, firstJetSplitting_ofDeriv] at h
    rw [h]
    simp only [d, map_sub, firstJetSplitting_ofDeriv, firstJetSplitting_firstJetLift, sub_zero,
      sub_self]
  have hd0 : d = 0 := by rw [← hL, hL0, map_zero]
  rw [hdef, sub_sub, sub_eq_zero] at hd0
  exact hd0.symm

/-- A first jet is the horizontal lift of `v` exactly when it has value `v` and lies in the kernel
of the connection map. -/
theorem eq_firstJetLift_iff (cov : CovariantDerivative I F V) {x : M}
    {j : FirstJetBundle I F V x} {v : V x} :
    j = cov.firstJetLift x v ↔ value I F x j = v ∧ cov.firstJetSplitting x j = 0 := by
  refine ⟨by rintro rfl; simp, fun ⟨hv, hK⟩ ↦ ?_⟩
  rw [← cov.firstJetLift_value_add_ofDeriv_firstJetSplitting x j, hv, hK, map_zero, add_zero]

/-- **The horizontal lift in coordinates.** In the trivialization `e` at `x`, the horizontal lift
of `v` has value coordinate `e v`, and its derivative coordinate is minus the covariant derivative
at `x`, read in `e`, of the section `y ↦ e.symm y (e v)` with constant coordinates `e v`. -/
theorem firstJetLift_apply (cov : CovariantDerivative I F V) (x : M) (v : V x) :
    cov.firstJetLift x v =
      (((trivializationAt F V x).continuousLinearMapAt 𝕜 x v,
        -((trivializationAt F V x).continuousLinearMapAt 𝕜 x).comp
          (cov (fun y ↦ (trivializationAt F V x).symm y
            ((trivializationAt F V x).continuousLinearMapAt 𝕜 x v)) x)) :
        FirstJetBundle I F V x) := by
  have hx := mem_baseSet_trivializationAt F V x
  refine (cov.eq_firstJetLift_iff.2 ⟨?_, ?_⟩).symm
  · exact (value_apply I F x _).trans <|
      ((trivializationAt F V x).symmL_apply (R := 𝕜) hx _).symm.trans
        ((trivializationAt F V x).symmL_continuousLinearMapAt (R := 𝕜) hx v)
  · refine (cov.firstJetSplitting_apply x _).trans ?_
    ext w
    simp only [add_apply, ContinuousLinearMap.comp_apply, neg_apply, map_neg, zero_apply]
    rw [(trivializationAt F V x).symmL_continuousLinearMapAt (R := 𝕜) hx, neg_add_cancel]

/-- The value coordinate of the horizontal lift of `v` in the trivialization at `x` is `e v`. -/
@[simp]
theorem firstJetLift_fst (cov : CovariantDerivative I F V) (x : M) (v : V x) :
    (cov.firstJetLift x v).1 = (trivializationAt F V x).continuousLinearMapAt 𝕜 x v :=
  congrArg Prod.fst (cov.firstJetLift_apply x v)

/-- The derivative coordinate of the horizontal lift of `v` in the trivialization `e` at `x` is
minus the covariant derivative at `x`, read in `e`, of the section with constant coordinates
`e v`. -/
@[simp]
theorem firstJetLift_snd (cov : CovariantDerivative I F V) (x : M) (v : V x) :
    (cov.firstJetLift x v).2 =
      -((trivializationAt F V x).continuousLinearMapAt 𝕜 x).comp
        (cov (fun y ↦ (trivializationAt F V x).symm y
          ((trivializationAt F V x).continuousLinearMapAt 𝕜 x v)) x) :=
  congrArg Prod.snd (cov.firstJetLift_apply x v)

/-- **Change of horizontal lift.** Adding an endomorphism-valued one-form `A` to a connection
subtracts the inclusion of `A v` from the horizontal lift of `v`. -/
@[simp]
theorem firstJetLift_addOneForm (cov : CovariantDerivative I F V)
    (A : Π x : M, V x →L[𝕜] TangentSpace I x →L[𝕜] V x) (x : M) (v : V x) :
    (cov.addOneForm A).firstJetLift x v = cov.firstJetLift x v - ofDeriv I F x (A x v) :=
  ((cov.addOneForm A).eq_firstJetLift_iff.2 ⟨by simp, by simp⟩).symm

/-- **Change of horizontal lift.** The horizontal lifts of two connections differ by the inclusion
of minus their difference one-form applied to the vector. -/
theorem firstJetLift_sub_firstJetLift (cov cov' : CovariantDerivative I F V) (x : M) (v : V x) :
    cov.firstJetLift x v - cov'.firstJetLift x v = -ofDeriv I F x (cov.difference cov' x v) := by
  have h := cov'.firstJetLift_value_add_ofDeriv_firstJetSplitting x (cov.firstJetLift x v)
  have hK := cov.firstJetSplitting_sub_firstJetSplitting cov' x (cov.firstJetLift x v)
  rw [value_firstJetLift] at h hK
  rw [firstJetSplitting_firstJetLift, zero_sub] at hK
  rw [← hK, map_neg, neg_neg, sub_eq_iff_eq_add']
  exact h.symm

/-- The kernel of the connection map is the image of the horizontal lift. -/
theorem ker_firstJetSplitting (cov : CovariantDerivative I F V) (x : M) :
    LinearMap.ker (cov.firstJetSplitting x).toLinearMap =
      LinearMap.range (cov.firstJetLift x).toLinearMap := by
  ext j
  simp only [LinearMap.mem_ker, LinearMap.mem_range, ContinuousLinearMap.coe_coe]
  refine ⟨fun hj ↦ ⟨value I F x j, ?_⟩, ?_⟩
  · rw [← cov.firstJetLift_value_add_ofDeriv_firstJetSplitting x j, hj, map_zero, add_zero,
      value_firstJetLift]
  · rintro ⟨v, rfl⟩
    exact cov.firstJetSplitting_firstJetLift x v

/-- The **decomposition of first jets** by a connection: `J¹Vₓ ≃L Vₓ × Hom(TₓM, Vₓ)`, sending
a first jet to its value and its image under the connection map. Its inverse is the sum of the
horizontal lift and the inclusion of `Hom(TₓM, Vₓ)`. -/
def firstJetEquiv (cov : CovariantDerivative I F V) (x : M) :
    FirstJetBundle I F V x ≃L[𝕜] V x × (TangentSpace I x →L[𝕜] V x) :=
  ContinuousLinearEquiv.equivOfInverse ((value I F x).prod (cov.firstJetSplitting x))
    ((cov.firstJetLift x).coprod (ofDeriv I F x))
    (fun j ↦ by simp)
    (fun p ↦ by
      simp only [ContinuousLinearMap.coprod_apply, ContinuousLinearMap.prod_apply, map_add,
        value_ofDeriv, value_firstJetLift, firstJetSplitting_ofDeriv,
        firstJetSplitting_firstJetLift]
      exact Prod.ext (add_zero _) (zero_add _))

/-- The decomposition sends a first jet to its value and its image under the connection map. -/
@[simp]
theorem firstJetEquiv_apply (cov : CovariantDerivative I F V) (x : M)
    (j : FirstJetBundle I F V x) :
    cov.firstJetEquiv x j = (value I F x j, cov.firstJetSplitting x j) :=
  (rfl)

/-- The inverse decomposition is the horizontal lift plus the inclusion of `Hom(TₓM, Vₓ)`. -/
@[simp]
theorem firstJetEquiv_symm_apply (cov : CovariantDerivative I F V) (x : M)
    (p : V x × (TangentSpace I x →L[𝕜] V x)) :
    (cov.firstJetEquiv x).symm p = cov.firstJetLift x p.1 + ofDeriv I F x p.2 :=
  (rfl)

/-- The decomposition sends the first jet of a section differentiable at `x` to its value and its
covariant derivative at `x`. -/
theorem firstJetEquiv_jet (cov : CovariantDerivative I F V) {σ : Π x, V x} {x : M}
    (hσ : MDifferentiableAt I (I.prod 𝓘(𝕜, F)) (fun x ↦ TotalSpace.mk' F x (σ x)) x) :
    cov.firstJetEquiv x (jet I F σ x) = (σ x, cov σ x) := by
  rw [firstJetEquiv_apply, value_jet, cov.firstJetSplitting_jet hσ]

/-- A section differentiable at `x` has first jet the horizontal lift of its value exactly when
its covariant derivative at `x` vanishes. -/
theorem jet_eq_firstJetLift_iff (cov : CovariantDerivative I F V) {σ : Π x, V x} {x : M}
    (hσ : MDifferentiableAt I (I.prod 𝓘(𝕜, F)) (fun x ↦ TotalSpace.mk' F x (σ x)) x) :
    jet I F σ x = cov.firstJetLift x (σ x) ↔ cov σ x = 0 := by
  rw [eq_firstJetLift_iff, value_jet, cov.firstJetSplitting_jet hσ]
  exact and_iff_right rfl

end CovariantDerivative

/-! ### Trivial bundles -/

namespace CovariantDerivative

open TauCeti TauCeti.FirstJetBundle

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners 𝕜 E H} {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I 1 M] {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F] [FiniteDimensional 𝕜 F]

/-- On a trivial bundle, the canonical flat connection sends a first jet to its derivative
coordinate. -/
theorem firstJetSplitting_trivial (x : M) (j : FirstJetBundle I F (Bundle.Trivial M F) x) :
    (trivial F).firstJetSplitting x j = j.2 := by
  rw [firstJetSplitting_apply, trivial_apply]
  simp only [Trivial.fiberBundle_trivializationAt', Trivial.trivialization_symm_apply,
    mvfderiv_const, add_zero]
  ext w
  exact (Trivialization.symmL_apply (R := 𝕜) _ (mem_univ x) (j.2 w)).trans
    (Trivial.trivialization_symm_apply M F x (j.2 w))

/-- On a trivial bundle, the horizontal lift of the canonical flat connection sends `v` to the
first jet with value `v` and derivative zero. -/
theorem firstJetLift_trivial (x : M) (v : Bundle.Trivial M F x) :
    (trivial F).firstJetLift (I := I) x v =
      ((v, 0) : FirstJetBundle I F (Bundle.Trivial M F) x) := by
  rw [firstJetLift_apply, trivial_apply]
  refine Prod.ext (by simp) ?_
  simp only [Trivial.fiberBundle_trivializationAt', Trivial.trivialization_symm_apply,
    mvfderiv_const, ContinuousLinearMap.comp_zero, neg_zero]
  rfl

/-- On a trivial bundle, the decomposition of first jets by the canonical flat connection is the
identity on the coordinates. -/
theorem firstJetEquiv_trivial_apply (x : M) (j : FirstJetBundle I F (Bundle.Trivial M F) x) :
    (trivial F).firstJetEquiv x j = (j.1, j.2) := by
  rw [firstJetEquiv_apply, firstJetSplitting_trivial, value_apply]
  simp
  rfl

/-- On a trivial bundle, the canonical flat connection decomposes the first jet of a section `σ`
as its value and its derivative. -/
theorem firstJetEquiv_trivial_jet (σ : M → F) (x : M) :
    (trivial F).firstJetEquiv x (jet I F (σ : Π y, Bundle.Trivial M F y) x) =
      (σ x, mvfderiv I σ x) := by
  rw [firstJetEquiv_apply, value_jet, firstJetSplitting_trivial, jet_trivial_snd_eq_mvfderiv]

/-- On a trivial bundle, the connection `d + A` decomposes the first jet of a section `σ` as its
value and `dσ + A σ`. -/
theorem firstJetEquiv_addOneForm_trivial_jet
    (A : Π x : M, Bundle.Trivial M F x →L[𝕜] TangentSpace I x →L[𝕜] Bundle.Trivial M F x)
    (σ : M → F) (x : M) :
    ((trivial F).addOneForm A).firstJetEquiv x (jet I F (σ : Π y, Bundle.Trivial M F y) x) =
      (σ x, mvfderiv I σ x + A x (σ x)) := by
  have h : (trivial F).firstJetSplitting x (jet I F (σ : Π y, Bundle.Trivial M F y) x) =
      mvfderiv I σ x :=
    congrArg Prod.snd (firstJetEquiv_trivial_jet (I := I) σ x)
  rw [firstJetEquiv_apply, firstJetSplitting_addOneForm, value_jet, h]

/-- On a trivial bundle, the canonical flat connection decomposes the first jet of a constant
section `v` as `(v, 0)`. -/
theorem firstJetEquiv_trivial_jet_const (x : M) (v : F) :
    (trivial F).firstJetEquiv x (jet I F (fun _ ↦ v : Π y, Bundle.Trivial M F y) x) = (v, 0) := by
  rw [firstJetEquiv_trivial_jet, mvfderiv_const]

/-- On a trivial bundle, the connection `d + A` decomposes the first jet of a constant section `v`
as `(v, A v)`. -/
theorem firstJetEquiv_addOneForm_trivial_jet_const
    (A : Π x : M, Bundle.Trivial M F x →L[𝕜] TangentSpace I x →L[𝕜] Bundle.Trivial M F x)
    (x : M) (v : F) :
    ((trivial F).addOneForm A).firstJetEquiv x (jet I F (fun _ ↦ v : Π y, Bundle.Trivial M F y) x) =
      (v, A x v) := by
  rw [firstJetEquiv_addOneForm_trivial_jet, mvfderiv_const, zero_add]

end CovariantDerivative
