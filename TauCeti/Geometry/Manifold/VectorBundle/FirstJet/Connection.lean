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
`σ` with `∇σ(x) = 0` has first jet the horizontal lift of `σ x`. Together these give the
decomposition `J¹Vₓ ≃ Vₓ × Hom(TₓM, Vₓ)`, `j ↦ (value j, K j)`, under which `j¹σ(x)` becomes
`(σ x, ∇σ(x))`.

Changing the connection changes the splitting by the difference one-form evaluated on the value
coordinate: `K_{∇ + A}(j) = K_∇(j) + A(value j)`. For instance, on a trivial bundle the
first jet of a constant section `v` is `(v, 0)` for the canonical flat connection and `(v, A v)`
for the connection `d + A`.

## Main definitions and results

* `CovariantDerivative.firstJetSplitting`: the connection map `J¹Vₓ → Hom(TₓM, Vₓ)`, with
  `CovariantDerivative.firstJetSplitting_jet` (`K (j¹σ(x)) = ∇σ(x)`) and
  `CovariantDerivative.firstJetSplitting_ofDeriv` (`K ∘ ofDeriv = id`).
* `CovariantDerivative.congr_of_jet_eq`: the covariant derivative at `x` of a section
  differentiable at `x` depends only on its first jet at `x`.
* `CovariantDerivative.firstJetSplitting_addOneForm` and
  `CovariantDerivative.firstJetSplitting_sub_firstJetSplitting`: the change of splitting under a
  change of connection.
* `CovariantDerivative.firstJetLift`: the horizontal lift `Vₓ → J¹Vₓ`, with
  `CovariantDerivative.value_firstJetLift` and
  `CovariantDerivative.firstJetSplitting_firstJetLift`.
* `CovariantDerivative.firstJetEquiv`: the decomposition `J¹Vₓ ≃L Vₓ × Hom(TₓM, Vₓ)`, with
  `CovariantDerivative.firstJetEquiv_jet`.

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
    firstJetSplitting_apply_christoffelForm, value_jet, jet_snd_eq_mfderiv I F hσ]
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

/-- **Change of splitting.** Adding an endomorphism-valued one-form `A` to a connection adds
`A` applied to the value of a first jet to its image under the connection map. -/
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

/-- Every first jet is the horizontal lift of its value plus the inclusion of its image under the
connection map. -/
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

/-- The **decomposition of first jets** by a connection: `J¹Vₓ ≃L Vₓ × Hom(TₓM, Vₓ)`, sending
a first jet to its value and its image under the connection map. Its inverse is the sum of the
horizontal lift and the inclusion of `Hom(TₓM, Vₓ)`. -/
def firstJetEquiv (cov : CovariantDerivative I F V) (x : M) :
    FirstJetBundle I F V x ≃L[𝕜] V x × (TangentSpace I x →L[𝕜] V x) :=
  ContinuousLinearEquiv.equivOfInverse ((value I F x).prod (cov.firstJetSplitting x))
    ((cov.firstJetLift x).coprod (ofDeriv I F x))
    (fun j ↦ by simpa using cov.firstJetLift_value_add_ofDeriv_firstJetSplitting x j)
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

/-- A section differentiable at `x` with vanishing covariant derivative at `x` has first jet the
horizontal lift of its value. -/
theorem jet_eq_firstJetLift (cov : CovariantDerivative I F V) {σ : Π x, V x} {x : M}
    (hσ : MDifferentiableAt I (I.prod 𝓘(𝕜, F)) (fun x ↦ TotalSpace.mk' F x (σ x)) x)
    (h : cov σ x = 0) :
    jet I F σ x = cov.firstJetLift x (σ x) := by
  rw [← cov.firstJetLift_value_add_ofDeriv_firstJetSplitting x (jet I F σ x), value_jet,
    cov.firstJetSplitting_jet hσ, h, map_zero, add_zero]

end CovariantDerivative

/-! ### Trivial bundles -/

namespace CovariantDerivative

open TauCeti TauCeti.FirstJetBundle

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners 𝕜 E H} {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I 1 M] {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F] [FiniteDimensional 𝕜 F]

/-- On a trivial bundle, the connection `d + A` decomposes the first jet of a constant section `v`
as `(v, A v)`; for `A = 0` this is `(v, 0)`. -/
theorem firstJetEquiv_addOneForm_trivial_jet_const
    (A : Π x : M, Bundle.Trivial M F x →L[𝕜] TangentSpace I x →L[𝕜] Bundle.Trivial M F x)
    (x : M) (v : F) :
    ((trivial F).addOneForm A).firstJetEquiv x (jet I F (fun _ ↦ v) x) = (v, A x v) := by
  have hv : MDifferentiableAt I (I.prod 𝓘(𝕜, F))
      (fun y ↦ TotalSpace.mk' F y ((fun _ ↦ v : Π y, Bundle.Trivial M F y) y)) x := by
    rw [mdifferentiableAt_section]
    exact mdifferentiableAt_const
  rw [firstJetEquiv_jet _ hv, addOneForm_apply, trivial_apply, mvfderiv_const, zero_add]

end CovariantDerivative
