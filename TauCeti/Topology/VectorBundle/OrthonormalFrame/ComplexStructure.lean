/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.VectorBundle.OrthonormalFrame.Basic
import TauCeti.Geometry.Symplectic.Complex.InnerProductSpace
import TauCeti.Geometry.Symplectic.Complex.OrthonormalBasis

/-!
# Unitary frames of a fibrewise orthogonal complex structure

Let `E → B` be a continuous Riemannian vector bundle with model fibre `F`, and let `J` be a
fibrewise orthogonal complex structure on `E`: a linear isometry `J b` of each fibre with
`J b (J b v) = -v`. Let `V` be a real inner product space with an orthogonal complex structure
`J₀`, an element of the orthogonal group `unitary (V →L[ℝ] V)`. An orthonormal frame
`φ : V ≃ₗᵢ[ℝ] E b` is *unitary* when it carries `J₀` to `J b`, `φ (J₀ v) = J b (φ v)`. The unitary
frames form the subset `TauCeti.OrthonormalFrameBundle.unitaryFrames F J J₀` of the orthonormal
frame bundle. For an almost Hermitian four-manifold, with `E` its tangent bundle and `J` its
almost complex structure, these are the unitary frames whose bundle is the reduction of the
structure group of the orthonormal frame bundle from `O(4)` to `U(2)`.

Acting by an orthogonal transformation `g` of `V` keeps a unitary frame unitary exactly when `g`
commutes with `J₀` (`TauCeti.OrthonormalFrameBundle.smul_mem_unitaryFrames_iff`). So the
centralizer of `J₀` in the orthogonal group, the unitary group `U(V, J₀)`, acts on the unitary
frames on the right, continuously, freely
(`TauCeti.OrthonormalFrameBundle.unitaryFrames_smul_eq_self_iff`) and transitively on each fibre
(`TauCeti.OrthonormalFrameBundle.exists_unitaryFrames_smul_eq_iff`).

In rank four, when `J` is continuous on the total space, the unitary frames are locally trivial
with fibre `U(V, J₀)`, by trivializations equivariant for the action
(`TauCeti.OrthonormalFrameBundle.exists_trivialization_unitaryFrames`). Over the base set of a
linear trivialization of `E`, read `J` in the local Gram–Schmidt orthonormal frame `σ`: this gives
a continuous family `K y = σ_y⁻¹ ∘ J y ∘ σ_y` of orthogonal complex structures on `V`. For a unit
vector `a` and a vector `c` outside the complex line of `a`, the vectors
`(a, K a, u, K u)`, with `u` the normalized component of `c` orthogonal to `a` and `K a`, form an
orthonormal basis adapted to `K`, depending continuously on `K` while `c` stays outside that
complex line. Matching it with an adapted orthonormal basis of `(V, J₀)` corrects `σ` to a
continuous local unitary frame, and dividing by the corrected frame trivializes the unitary frames.

## Main definitions

* `TauCeti.OrthonormalFrameBundle.unitaryFrames F J J₀`: the orthonormal frames carrying `J₀` to
  `J`.
* The right action of `Subgroup.centralizer {J₀}` on `unitaryFrames F J J₀`.

## Main results

* `TauCeti.OrthonormalFrameBundle.smul_mem_unitaryFrames_iff`: an orthogonal transformation keeps
  a unitary frame unitary exactly when it commutes with `J₀`.
* `TauCeti.OrthonormalFrameBundle.unitaryFrames_smul_eq_self_iff`,
  `TauCeti.OrthonormalFrameBundle.exists_unitaryFrames_smul_eq_iff`: the action is free, and
  transitive on fibres.
* `TauCeti.OrthonormalFrameBundle.exists_trivialization_unitaryFrames`: in rank four the unitary
  frames are locally trivial with fibre the centralizer of `J₀`, equivariantly for the action.

## References

* S. Kobayashi, K. Nomizu, *Foundations of Differential Geometry*, Vol. II, Interscience, 1969,
  Chapter IX, §4 (the bundle of unitary frames of an almost Hermitian manifold).
* H. B. Lawson, M.-L. Michelsohn, *Spin Geometry*, Princeton University Press, 1989, Appendix D
  (the reduction of the structure group to `U(n)` given by an almost complex structure).
-/

public section

noncomputable section

open Bundle Set Module MulOpposite
open scoped Topology RealInnerProductSpace

namespace TauCeti.OrthonormalFrameBundle

section Unitary

variable {B : Type*} {F : Type*} {E : B → Type*} [∀ x, NormedAddCommGroup (E x)]
  [∀ x, InnerProductSpace ℝ (E x)] {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [CompleteSpace V] (J : ∀ b, E b ≃ₗᵢ[ℝ] E b) (J₀ : unitary (V →L[ℝ] V))

variable (F) in
/-- The unitary frames of a fibrewise complex structure `J` on `E`, modelled on `(V, J₀)`: the
orthonormal frames `φ : V ≃ₗᵢ[ℝ] E b` carrying `J₀` to `J b`, `φ (J₀ v) = J b (φ v)`. -/
def unitaryFrames : Set (OrthonormalFrameBundle ℝ F E V) :=
  {p | ∀ v, p.frame ((J₀ : V →L[ℝ] V) v) = J p.proj (p.frame v)}

variable {J J₀}

/-- A frame is unitary when it carries `J₀` to `J`. -/
@[simp]
theorem mem_unitaryFrames_iff {p : OrthonormalFrameBundle ℝ F E V} :
    p ∈ unitaryFrames F J J₀ ↔ ∀ v, p.frame ((J₀ : V →L[ℝ] V) v) = J p.proj (p.frame v) :=
  Iff.rfl

/-- The frame `φ` over `y` is unitary when it carries `J₀` to `J y`. -/
theorem mk_mem_unitaryFrames_iff {y : B} {φ : V ≃ₗᵢ[ℝ] E y} :
    (⟨y, φ⟩ : OrthonormalFrameBundle ℝ F E V) ∈ unitaryFrames F J J₀ ↔
      ∀ v, φ ((J₀ : V →L[ℝ] V) v) = J y (φ v) :=
  Iff.rfl

/-- An orthogonal transformation `g` of `V` keeps a unitary frame unitary exactly when `g`
commutes with `J₀`. -/
theorem smul_mem_unitaryFrames_iff {p : OrthonormalFrameBundle ℝ F E V}
    (hp : p ∈ unitaryFrames F J J₀) {g : unitary (V →L[ℝ] V)} :
    op g • p ∈ unitaryFrames F J J₀ ↔ g ∈ Subgroup.centralizer {J₀} := by
  rw [Subgroup.mem_centralizer_singleton_iff, commute_iff_eq, ← Subtype.coe_inj,
    Submonoid.coe_mul, Submonoid.coe_mul, ContinuousLinearMap.ext_iff]
  simp only [mem_unitaryFrames_iff, frame_smul_apply, unop_op, proj_smul,
    ContinuousLinearMap.mul_def, ContinuousLinearMap.comp_apply]
  -- Both conditions compare `p.frame (g (J₀ v))` with `p.frame (J₀ (g v)) = J (p.frame (g v))`.
  refine forall_congr' fun v ↦ ?_
  rw [← hp, p.frame.injective.eq_iff]

/-- Two unitary frames over the same base point differ by an orthogonal transformation commuting
with `J₀`. -/
theorem exists_mem_centralizer_smul_eq {p q : OrthonormalFrameBundle ℝ F E V}
    (hp : p ∈ unitaryFrames F J J₀) (hq : q ∈ unitaryFrames F J J₀) (h : p.proj = q.proj) :
    ∃ g ∈ Subgroup.centralizer {J₀}, op g • p = q := by
  obtain ⟨g, rfl⟩ := exists_smul_eq_iff.2 h
  exact ⟨g, (smul_mem_unitaryFrames_iff hp).1 hq, rfl⟩

/-- The right action of the centralizer of `J₀`, the unitary group `U(V, J₀)`, on the unitary
frames, by precomposition. -/
instance : MulAction (Subgroup.centralizer {J₀})ᵐᵒᵖ (unitaryFrames F J J₀) where
  smul g p := ⟨op (g.unop : unitary (V →L[ℝ] V)) • p.val,
    (smul_mem_unitaryFrames_iff p.property).2 g.unop.property⟩
  one_smul p := Subtype.ext (one_smul _ p.val)
  mul_smul g h p := Subtype.ext (mul_smul (op (g.unop : unitary (V →L[ℝ] V)))
    (op (h.unop : unitary (V →L[ℝ] V))) p.val)

/-- The action on unitary frames is the action on all orthonormal frames. -/
@[simp]
theorem coe_unitaryFrames_smul (g : (Subgroup.centralizer {J₀})ᵐᵒᵖ) (p : unitaryFrames F J J₀) :
    ((g • p : unitaryFrames F J J₀) : OrthonormalFrameBundle ℝ F E V) =
      op (g.unop : unitary (V →L[ℝ] V)) • (p : OrthonormalFrameBundle ℝ F E V) :=
  rfl

/-- The action of the centralizer of `J₀` on unitary frames is free. -/
@[simp↓]
theorem unitaryFrames_smul_eq_self_iff {g : Subgroup.centralizer {J₀}} {p : unitaryFrames F J J₀} :
    op g • p = p ↔ g = 1 := by
  rw [← Subtype.coe_inj, coe_unitaryFrames_smul, unop_op, smul_eq_self_iff,
    OneMemClass.coe_eq_one]

/-- The action of the centralizer of `J₀` on unitary frames is transitive on fibres: two unitary
frames differ by an element of the centralizer exactly when they lie over the same base point. -/
theorem exists_unitaryFrames_smul_eq_iff {p q : unitaryFrames F J J₀} :
    (∃ g : Subgroup.centralizer {J₀}, op g • p = q) ↔ p.val.proj = q.val.proj := by
  refine ⟨fun ⟨g, h⟩ ↦ by rw [← h, coe_unitaryFrames_smul, proj_smul], fun h ↦ ?_⟩
  obtain ⟨g, hg, hgq⟩ := exists_mem_centralizer_smul_eq p.property q.property h
  exact ⟨⟨g, hg⟩, Subtype.ext hgq⟩

variable [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace B]
  [TopologicalSpace (TotalSpace F E)] [FiberBundle F E] [VectorBundle ℝ F E] [FiniteDimensional ℝ V]

/-- The right action of the centralizer of `J₀` on unitary frames is continuous. -/
instance : ContinuousSMul (Subgroup.centralizer {J₀})ᵐᵒᵖ (unitaryFrames F J J₀) where
  continuous_smul := ((continuous_op.comp ((continuous_subtypeVal.comp continuous_unop).comp
    continuous_fst)).smul (continuous_subtypeVal.comp continuous_snd)).subtype_mk _

end Unitary

/-! ### Adapted orthonormal bases depending continuously on the complex structure -/

section AdaptedBasis

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-- The component of `c` orthogonal to `a` and `K a`, for a unit vector `a`. -/
private def residual (K : V →L[ℝ] V) (a c : V) : V :=
  c - ⟪a, c⟫ • a - ⟪K a, c⟫ • K a

/-- The normalized component of `c` orthogonal to `a` and `K a`. -/
private def adaptedUnit (K : V →L[ℝ] V) (a c : V) : V :=
  ‖residual K a c‖⁻¹ • residual K a c

/-- The vectors `(a, K a, u, K u)`, where `u` is the normalized component of `c` orthogonal to
`a` and `K a`. -/
private def adaptedVectors (K : V →L[ℝ] V) (a c : V) : Fin 4 → V :=
  ![a, K a, adaptedUnit K a c, K (adaptedUnit K a c)]

/-- For an orthogonal complex structure `K`, a unit vector `a` and a vector `c` outside the complex
line of `a`, the vectors `(a, K a, u, K u)` are orthonormal. -/
private theorem orthonormal_adaptedVectors {K : V →L[ℝ] V} (hK : ∀ v w, ⟪K v, K w⟫ = ⟪v, w⟫)
    (hK₂ : ∀ v, K (K v) = -v) {a c : V} (ha : ‖a‖ = 1) (hr : residual K a c ≠ 0) :
    Orthonormal ℝ (adaptedVectors K a c) := by
  let J : AlmostComplexStructure V := ⟨K.toLinearMap, LinearMap.ext fun v ↦ by simpa using hK₂ v⟩
  have hJ : ∀ v w, ⟪J v, J w⟫ = ⟪v, w⟫ := hK
  have haKa : ⟪a, K a⟫ = 0 := J.inner_self_apply hJ a
  have hKa : ‖K a‖ = 1 := (J.norm_apply hJ a).trans ha
  have har : ⟪a, residual K a c⟫ = 0 := by
    simp only [residual, inner_sub_right, inner_smul_right, real_inner_self_eq_norm_sq, ha, haKa]
    ring
  have hKar : ⟪K a, residual K a c⟫ = 0 := by
    simp only [residual, inner_sub_right, inner_smul_right, real_inner_self_eq_norm_sq, hKa,
      real_inner_comm a (K a), haKa]
    ring
  exact AlmostComplexStructure.orthonormal_unitaryFour hJ ha (norm_smul_inv_norm hr)
    (by rw [adaptedUnit, inner_smul_right, har, mul_zero])
    (by rw [adaptedUnit, inner_smul_right]; exact mul_eq_zero_of_right _ hKar)

variable [Fact (finrank ℝ V = 4)]

/-- Some vector of an orthonormal basis of a four-dimensional space lies outside the complex line
of `a` for `K`, the span of `a` and `K a`. -/
private theorem exists_residual_ne_zero [FiniteDimensional ℝ V] (K : V →L[ℝ] V) (a : V)
    (β : OrthonormalBasis (Fin 4) ℝ V) : ∃ j, residual K a (β j) ≠ 0 := by
  by_contra! h
  have hle : (⊤ : Submodule ℝ V) ≤ Submodule.span ℝ (Set.range ![a, K a]) := by
    rw [← β.toBasis.span_eq, Submodule.span_le]
    rintro _ ⟨j, rfl⟩
    have hj : β j = ⟪a, β j⟫ • a + ⟪K a, β j⟫ • K a := by
      have h' := h j
      rwa [residual, sub_sub, sub_eq_zero] at h'
    rw [OrthonormalBasis.coe_toBasis, hj]
    exact add_mem (Submodule.smul_mem _ _ (Submodule.subset_span ⟨0, rfl⟩))
      (Submodule.smul_mem _ _ (Submodule.subset_span ⟨1, rfl⟩))
  have h4 := (Submodule.finrank_mono hle).trans (finrank_range_le_card _)
  rw [finrank_top, Fact.out (p := finrank ℝ V = 4), Fintype.card_fin] at h4
  omega

/-- The orthonormal basis `(a, K a, u, K u)` of a four-dimensional space adapted to an orthogonal
complex structure `K`, for a unit vector `a` and a vector `c` outside the complex line of `a`. -/
private def adaptedBasis {K : V →L[ℝ] V} (hK : ∀ v w, ⟪K v, K w⟫ = ⟪v, w⟫)
    (hK₂ : ∀ v, K (K v) = -v) {a c : V} (ha : ‖a‖ = 1) (hr : residual K a c ≠ 0) :
    OrthonormalBasis (Fin 4) ℝ V :=
  (basisOfOrthonormalOfCardEqFinrank (orthonormal_adaptedVectors hK hK₂ ha hr)
    ((Fintype.card_fin 4).trans (Fact.out : finrank ℝ V = 4).symm)).toOrthonormalBasis
    (by rw [coe_basisOfOrthonormalOfCardEqFinrank]; exact orthonormal_adaptedVectors hK hK₂ ha hr)

private theorem coe_adaptedBasis {K : V →L[ℝ] V} (hK : ∀ v w, ⟪K v, K w⟫ = ⟪v, w⟫)
    (hK₂ : ∀ v, K (K v) = -v) {a c : V} (ha : ‖a‖ = 1) (hr : residual K a c ≠ 0) :
    (adaptedBasis hK hK₂ ha hr : Fin 4 → V) = adaptedVectors K a c := by
  rw [adaptedBasis, Module.Basis.coe_toOrthonormalBasis, coe_basisOfOrthonormalOfCardEqFinrank]

variable [CompleteSpace V]

open scoped Classical in
/-- The orthogonal transformation of `V` carrying the orthonormal basis `β` to the basis
`(a, K a, u, K u)` adapted to `K`, where `a = β 0`, when `K` is a complex structure and `c` lies
outside the complex line of `a`; and `1` otherwise. -/
private def adaptedCorrection (β : OrthonormalBasis (Fin 4) ℝ V) (c : V)
    (K : unitary (V →L[ℝ] V)) : unitary (V →L[ℝ] V) :=
  if h : (∀ v, (K : V →L[ℝ] V) ((K : V →L[ℝ] V) v) = -v) ∧
      residual (K : V →L[ℝ] V) (β 0) c ≠ 0 then
    Unitary.linearIsometryEquiv.symm
      (β.equiv (adaptedBasis (Unitary.inner_map_map K) h.1 (β.orthonormal.1 0) h.2) (Equiv.refl _))
  else 1

variable {β : OrthonormalBasis (Fin 4) ℝ V} {c : V} {K : unitary (V →L[ℝ] V)}

private theorem adaptedCorrection_apply_basis (hK₂ : ∀ v, (K : V →L[ℝ] V) ((K : V →L[ℝ] V) v) = -v)
    (hr : residual (K : V →L[ℝ] V) (β 0) c ≠ 0) (i : Fin 4) :
    (adaptedCorrection β c K : V →L[ℝ] V) (β i) = adaptedVectors (K : V →L[ℝ] V) (β 0) c i := by
  rw [adaptedCorrection, dite_eq_left ⟨hK₂, hr⟩, Unitary.coe_symm_linearIsometryEquiv_apply,
    LinearIsometryEquiv.coe_coe'', OrthonormalBasis.equiv_apply_basis, Equiv.refl_apply,
    coe_adaptedBasis]

private theorem adaptedCorrection_apply (hK₂ : ∀ v, (K : V →L[ℝ] V) ((K : V →L[ℝ] V) v) = -v)
    (hr : residual (K : V →L[ℝ] V) (β 0) c ≠ 0) (v : V) :
    (adaptedCorrection β c K : V →L[ℝ] V) v =
      ∑ i, ⟪β i, v⟫ • adaptedVectors (K : V →L[ℝ] V) (β 0) c i := by
  conv_lhs => rw [← β.sum_repr' v]
  simp [map_sum, map_smul, adaptedCorrection_apply_basis hK₂ hr]

/-- The adapted correction intertwines `J₀` with `K`, when `β` is adapted to `J₀`. -/
private theorem apply_adaptedCorrection {J₀ : unitary (V →L[ℝ] V)}
    (hJ₀ : ∀ v, (J₀ : V →L[ℝ] V) ((J₀ : V →L[ℝ] V) v) = -v) (hβ₁ : β 1 = (J₀ : V →L[ℝ] V) (β 0))
    (hβ₃ : β 3 = (J₀ : V →L[ℝ] V) (β 2))
    (hK₂ : ∀ v, (K : V →L[ℝ] V) ((K : V →L[ℝ] V) v) = -v)
    (hr : residual (K : V →L[ℝ] V) (β 0) c ≠ 0) (v : V) :
    (K : V →L[ℝ] V) ((adaptedCorrection β c K : V →L[ℝ] V) v) =
      (adaptedCorrection β c K : V →L[ℝ] V) ((J₀ : V →L[ℝ] V) v) := by
  have hΦ := adaptedCorrection_apply_basis hK₂ hr
  set Φ : V →L[ℝ] V := ((adaptedCorrection β c K : unitary (V →L[ℝ] V)) : V →L[ℝ] V)
  have key : (((K : V →L[ℝ] V) ∘L Φ : V →L[ℝ] V) : V →ₗ[ℝ] V) =
      ((Φ ∘L (J₀ : V →L[ℝ] V) : V →L[ℝ] V) : V →ₗ[ℝ] V) := by
    refine β.toBasis.ext fun i ↦ ?_
    simp only [OrthonormalBasis.coe_toBasis, ContinuousLinearMap.coe_comp,
      ContinuousLinearMap.coe_coe, Function.comp_apply]
    fin_cases i <;> dsimp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk]
    · simp [hΦ, ← hβ₁, adaptedVectors]
    · rw [hΦ 1, hβ₁, hJ₀, map_neg, hΦ 0]
      simp [adaptedVectors, hK₂]
    · simp [hΦ, ← hβ₃, adaptedVectors]
    · rw [hΦ 3, hβ₃, hJ₀, map_neg, hΦ 2]
      simp [adaptedVectors, hK₂]
  exact LinearMap.congr_fun key v

variable (β c) in
/-- The adapted correction depends continuously on the complex structure `K`, while `c` stays
outside the complex line of `β 0`. -/
private theorem continuousOn_adaptedCorrection [FiniteDimensional ℝ V] :
    ContinuousOn (adaptedCorrection β c)
      {K | (∀ v, (K : V →L[ℝ] V) ((K : V →L[ℝ] V) v) = -v) ∧
        residual (K : V →L[ℝ] V) (β 0) c ≠ 0} := by
  refine Topology.IsInducing.subtypeVal.continuousOn_iff.2 (continuousOn_clm_apply.2 fun v ↦ ?_)
  have hK : Continuous fun K : unitary (V →L[ℝ] V) ↦ (K : V →L[ℝ] V) := continuous_subtypeVal
  have hres : Continuous fun K : unitary (V →L[ℝ] V) ↦ residual (K : V →L[ℝ] V) (β 0) c := by
    unfold residual
    fun_prop
  have hunit : ContinuousOn (fun K : unitary (V →L[ℝ] V) ↦ adaptedUnit (K : V →L[ℝ] V) (β 0) c)
      {K | residual (K : V →L[ℝ] V) (β 0) c ≠ 0} :=
    (hres.norm.continuousOn.inv₀ fun _ hK ↦ norm_ne_zero_iff.2 hK).smul hres.continuousOn
  have hvec (i : Fin 4) : ContinuousOn
      (fun K : unitary (V →L[ℝ] V) ↦ adaptedVectors (K : V →L[ℝ] V) (β 0) c i)
      {K | (∀ v, (K : V →L[ℝ] V) ((K : V →L[ℝ] V) v) = -v) ∧
        residual (K : V →L[ℝ] V) (β 0) c ≠ 0} := by
    fin_cases i
    · exact continuousOn_const
    · exact (hK.clm_apply continuous_const).continuousOn
    · exact hunit.mono fun _ hK ↦ hK.2
    · exact hK.continuousOn.clm_apply (hunit.mono fun _ hK ↦ hK.2)
  have hsum : ContinuousOn
      (fun K : unitary (V →L[ℝ] V) ↦ ∑ i, ⟪β i, v⟫ • adaptedVectors (K : V →L[ℝ] V) (β 0) c i)
      {K | (∀ v, (K : V →L[ℝ] V) ((K : V →L[ℝ] V) v) = -v) ∧
        residual (K : V →L[ℝ] V) (β 0) c ≠ 0} :=
    continuousOn_finsetSum Finset.univ fun i _ ↦ continuousOn_const.smul (hvec i)
  exact hsum.congr fun K hK ↦ adaptedCorrection_apply hK.1 hK.2 v

end AdaptedBasis

/-! ### Local triviality in rank four -/

section ToCentralizer

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  (J₀ : unitary (V →L[ℝ] V))

open scoped Classical in
/-- An orthogonal transformation, as an element of the centralizer of `J₀` when it is one, and
`1` otherwise. -/
private def toCentralizer (g : unitary (V →L[ℝ] V)) : Subgroup.centralizer {J₀} :=
  if h : g ∈ Subgroup.centralizer {J₀} then ⟨g, h⟩ else 1

variable {J₀}

private theorem coe_toCentralizer {g : unitary (V →L[ℝ] V)} (hg : g ∈ Subgroup.centralizer {J₀}) :
    (toCentralizer J₀ g : unitary (V →L[ℝ] V)) = g := by
  simp [toCentralizer, hg]

private theorem continuousOn_toCentralizer {X : Type*} [TopologicalSpace X]
    {f : X → unitary (V →L[ℝ] V)} {s : Set X} (hf : ContinuousOn f s)
    (hs : ∀ x ∈ s, f x ∈ Subgroup.centralizer {J₀}) :
    ContinuousOn (fun x ↦ toCentralizer J₀ (f x)) s :=
  Topology.IsInducing.subtypeVal.continuousOn_iff.2
    (hf.congr fun x hx ↦ coe_toCentralizer (hs x hx))

end ToCentralizer

section Trivialization

variable {B : Type*} [TopologicalSpace B] {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {E : B → Type*} [∀ x, NormedAddCommGroup (E x)] [∀ x, InnerProductSpace ℝ (E x)]
  [TopologicalSpace (TotalSpace F E)] [FiberBundle F E] [VectorBundle ℝ F E]
  [ContinuousFiberNorm F E] {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [CompleteSpace V] [FiniteDimensional ℝ V] [Fact (finrank ℝ V = 4)]
  (J : ∀ b, E b ≃ₗᵢ[ℝ] E b) {J₀ : unitary (V →L[ℝ] V)}
  (e : Trivialization F (π F E)) [e.IsLinear ℝ] (cF : Module.Basis (Fin 4) ℝ F)
  (β : OrthonormalBasis (Fin 4) ℝ V) (c : V)

/-- The complex structure `J` read in the local Gram–Schmidt frame `σ` of `e`:
`σ_y⁻¹ ∘ J y ∘ σ_y`. -/
private def localStructure (y : B) : unitary (V →L[ℝ] V) :=
  Unitary.linearIsometryEquiv.symm
    (((e.orthonormalFrameAt cF β y).trans (J y)).trans (e.orthonormalFrameAt cF β y).symm)

omit [ContinuousFiberNorm F E] [FiniteDimensional ℝ V] [Fact (finrank ℝ V = 4)] in
/-- The local frame carries `localStructure` to `J`. -/
private theorem orthonormalFrameAt_localStructure (y : B) (v : V) :
    e.orthonormalFrameAt cF β y ((localStructure J e cF β y : V →L[ℝ] V) v) =
      J y (e.orthonormalFrameAt cF β y v) := by
  simp [localStructure]

omit [ContinuousFiberNorm F E] [FiniteDimensional ℝ V] [Fact (finrank ℝ V = 4)] in
variable {J} in
private theorem localStructure_localStructure (hJ₂ : ∀ b v, J b (J b v) = -v) (y : B) (v : V) :
    (localStructure J e cF β y : V →L[ℝ] V) ((localStructure J e cF β y : V →L[ℝ] V) v) = -v :=
  (e.orthonormalFrameAt cF β y).injective (by
    rw [orthonormalFrameAt_localStructure, orthonormalFrameAt_localStructure, hJ₂, map_neg])

omit [Fact (finrank ℝ V = 4)] in
variable {J} in
/-- If `J` is continuous on the total space, `localStructure` is continuous over the base set
of `e`. -/
private theorem continuousOn_localStructure
    (hJ : Continuous fun v : TotalSpace F E ↦ (⟨v.proj, J v.proj v.snd⟩ : TotalSpace F E)) :
    ContinuousOn (localStructure J e cF β) e.baseSet := by
  refine Topology.IsInducing.subtypeVal.continuousOn_iff.2 (continuousOn_clm_apply.2 fun v ↦ ?_)
  refine ((e.continuousOn_orthonormalFrameAt_symm cF β).comp
    (hJ.comp_continuousOn (e.continuousOn_totalSpaceMk_orthonormalFrameAt cF β v))
      fun y hy ↦ hy).congr fun y _ ↦ ?_
  simp [localStructure]

/-- The points of the base set of `e` over which `c` lies outside the complex line of `β 0` for
`localStructure`: there the local frame can be corrected to a unitary frame. -/
private def goodSet : Set B :=
  {y | y ∈ e.baseSet ∧ residual (localStructure J e cF β y : V →L[ℝ] V) (β 0) c ≠ 0}

omit [Fact (finrank ℝ V = 4)] in
variable {J} in
private theorem isOpen_goodSet
    (hJ : Continuous fun v : TotalSpace F E ↦ (⟨v.proj, J v.proj v.snd⟩ : TotalSpace F E)) :
    IsOpen (goodSet J e cF β c) := by
  have hres : ContinuousOn
      (fun y ↦ residual (localStructure J e cF β y : V →L[ℝ] V) (β 0) c) e.baseSet := by
    have hK := (continuous_subtypeVal.comp_continuousOn (continuousOn_localStructure e cF β hJ))
    unfold residual
    exact continuousOn_const.sub (continuousOn_const.smul continuousOn_const) |>.sub
      ((hK.clm_apply continuousOn_const).inner continuousOn_const |>.smul
        (hK.clm_apply continuousOn_const)) |>.congr fun _ _ ↦ rfl
  exact hres.isOpen_inter_preimage e.open_baseSet isOpen_ne

/-- The corrected local frame: the local Gram–Schmidt frame of `e` composed with the adapted
correction of `localStructure`. -/
private def correctedFrame (y : B) : OrthonormalFrameBundle ℝ F E V :=
  ⟨y, (Unitary.linearIsometryEquiv (adaptedCorrection β c (localStructure J e cF β y))).trans
    (e.orthonormalFrameAt cF β y)⟩

omit [ContinuousFiberNorm F E] [FiniteDimensional ℝ V] in
/-- The corrected local frame is the local frame acted on by the adapted correction. -/
private theorem correctedFrame_eq_smul (y : B) :
    correctedFrame J e cF β c y = op (adaptedCorrection β c (localStructure J e cF β y)) •
      (⟨y, e.orthonormalFrameAt cF β y⟩ : OrthonormalFrameBundle ℝ F E V) :=
  (rfl)

variable {J e cF β c}

omit [ContinuousFiberNorm F E] [FiniteDimensional ℝ V] in
/-- Over the good set, the corrected local frame is unitary, when `β` is adapted to `J₀`. -/
private theorem correctedFrame_mem (hJ₂ : ∀ b v, J b (J b v) = -v)
    (hJ₀ : ∀ v, (J₀ : V →L[ℝ] V) ((J₀ : V →L[ℝ] V) v) = -v) (hβ₁ : β 1 = (J₀ : V →L[ℝ] V) (β 0))
    (hβ₃ : β 3 = (J₀ : V →L[ℝ] V) (β 2)) {y : B} (hy : y ∈ goodSet J e cF β c) :
    correctedFrame J e cF β c y ∈ unitaryFrames F J J₀ := by
  refine mk_mem_unitaryFrames_iff.2 fun v ↦ ?_
  -- `Unitary.linearIsometryEquiv u` applies `u` (`Unitary.coe_linearIsometryEquiv_apply`).
  have h := apply_adaptedCorrection hJ₀ hβ₁ hβ₃ (localStructure_localStructure e cF β hJ₂ y) hy.2 v
  exact (congrArg (e.orthonormalFrameAt cF β y) h).symm.trans
    (orthonormalFrameAt_localStructure J e cF β y _)

omit [Fact (finrank ℝ V = 4)] in
private theorem mem_baseSet_orthonormalFrameBundle {y : B} (hy : y ∈ e.baseSet) :
    y ∈ (e.orthonormalFrameBundle cF β :
      Trivialization _ (proj : OrthonormalFrameBundle ℝ F E V → B)).baseSet := by
  rwa [Trivialization.baseSet_orthonormalFrameBundle]

omit [Fact (finrank ℝ V = 4)] in
/-- Over the base set of `e`, the inverse of the Gram–Schmidt trivialization acts on the local
frame. -/
private theorem symm_orthonormalFrameBundle_apply {y : B} (hy : y ∈ e.baseSet)
    (g : unitary (V →L[ℝ] V)) :
    (e.orthonormalFrameBundle cF β).toOpenPartialHomeomorph.symm (y, g) =
      op g • (⟨y, e.orthonormalFrameAt cF β y⟩ : OrthonormalFrameBundle ℝ F E V) := by
  rw [e.orthonormalFrameBundle_symm_apply cF β ⟨y, hy⟩ g, e.orthonormalFrameAt_of_mem cF β hy]

omit [Fact (finrank ℝ V = 4)] in
/-- Over the base set of `e`, every frame is the local frame acted on by its fibre coordinate. -/
private theorem eq_smul_orthonormalFrameAt {p : OrthonormalFrameBundle ℝ F E V}
    (hp : p.proj ∈ e.baseSet) :
    p = op (e.orthonormalFrameBundle cF β p).2 •
      (⟨p.proj, e.orthonormalFrameAt cF β p.proj⟩ : OrthonormalFrameBundle ℝ F E V) := by
  rw [← symm_orthonormalFrameBundle_apply hp]
  exact ((e.orthonormalFrameBundle cF β).symm_apply_mk_proj
    ((e.orthonormalFrameBundle cF β).mem_source.2 (mem_baseSet_orthonormalFrameBundle hp))).symm

section Hypotheses

variable (hJ₂ : ∀ b v, J b (J b v) = -v) (hJ₀ : ∀ v, (J₀ : V →L[ℝ] V) ((J₀ : V →L[ℝ] V) v) = -v)
  (hβ₁ : β 1 = (J₀ : V →L[ℝ] V) (β 0)) (hβ₃ : β 3 = (J₀ : V →L[ℝ] V) (β 2))

include hJ₂ hJ₀ hβ₁ hβ₃

/-- Over the good set, the fibre coordinate of a unitary frame, multiplied by the inverse adapted
correction, commutes with `J₀`. -/
private theorem inv_mul_mem_centralizer {p : OrthonormalFrameBundle ℝ F E V}
    (hp : p.proj ∈ goodSet J e cF β c) (h : p ∈ unitaryFrames F J J₀) :
    (adaptedCorrection β c (localStructure J e cF β p.proj))⁻¹ *
      (e.orthonormalFrameBundle cF β p).2 ∈ Subgroup.centralizer {J₀} := by
  rw [← smul_mem_unitaryFrames_iff (correctedFrame_mem hJ₂ hJ₀ hβ₁ hβ₃ hp),
    correctedFrame_eq_smul, smul_smul, ← op_mul, mul_inv_cancel_left,
    ← eq_smul_orthonormalFrameAt hp.1]
  exact h

/-- Over the good set, acting on the local frame by the adapted correction times an element of
the centralizer of `J₀` gives a unitary frame. -/
private theorem symm_mem_unitaryFrames {y : B} (hy : y ∈ goodSet J e cF β c)
    (g : Subgroup.centralizer {J₀}) :
    (e.orthonormalFrameBundle cF β).toOpenPartialHomeomorph.symm
      (y, adaptedCorrection β c (localStructure J e cF β y) * g) ∈ unitaryFrames F J J₀ := by
  rw [symm_orthonormalFrameBundle_apply hy.1, op_mul, mul_smul, ← correctedFrame_eq_smul]
  exact (smul_mem_unitaryFrames_iff (correctedFrame_mem hJ₂ hJ₀ hβ₁ hβ₃ hy)).2 g.property

variable (J₀ J e cF β c) in
open scoped Classical in
/-- The inverse map of `unitaryTrivialization`: it sends `(y, g)` to the corrected local frame at
`y` acted on by `g` when this is a unitary frame, and to `p₀` otherwise. -/
private def unitaryTrivializationInv (p₀ : unitaryFrames F J J₀)
    (q : B × Subgroup.centralizer {J₀}) : unitaryFrames F J J₀ :=
  if h : (e.orthonormalFrameBundle cF β).toOpenPartialHomeomorph.symm
      (q.1, adaptedCorrection β c (localStructure J e cF β q.1) * q.2) ∈ unitaryFrames F J J₀ then
    ⟨_, h⟩
  else p₀

private theorem coe_unitaryTrivializationInv (p₀ : unitaryFrames F J J₀)
    {q : B × Subgroup.centralizer {J₀}} (hq : q.1 ∈ goodSet J e cF β c) :
    (unitaryTrivializationInv J J₀ e cF β c p₀ q : OrthonormalFrameBundle ℝ F E V) =
      (e.orthonormalFrameBundle cF β).toOpenPartialHomeomorph.symm
        (q.1, adaptedCorrection β c (localStructure J e cF β q.1) * q.2) := by
  rw [unitaryTrivializationInv, dite_eq_left (symm_mem_unitaryFrames hJ₂ hJ₀ hβ₁ hβ₃ hq q.2)]

variable (hJ : Continuous fun v : TotalSpace F E ↦ (⟨v.proj, J v.proj v.snd⟩ : TotalSpace F E))

omit hJ₀ hβ₁ hβ₃ in
include hJ in
/-- The adapted correction of `localStructure` is continuous over the good set. -/
private theorem continuousOn_adaptedCorrection_localStructure :
    ContinuousOn (fun y ↦ adaptedCorrection β c (localStructure J e cF β y))
      (goodSet J e cF β c) :=
  (continuousOn_adaptedCorrection β c).comp
    ((continuousOn_localStructure e cF β hJ).mono fun _ hy ↦ hy.1)
    fun y hy ↦ ⟨localStructure_localStructure e cF β hJ₂ y, hy.2⟩

include hJ in
/-- The inverse of `unitaryTrivialization` is continuous over the good set. -/
private theorem continuousOn_unitaryTrivializationInv (p₀ : unitaryFrames F J J₀) :
    ContinuousOn (unitaryTrivializationInv J J₀ e cF β c p₀) (goodSet J e cF β c ×ˢ univ) := by
  refine Topology.IsInducing.subtypeVal.continuousOn_iff.2 (ContinuousOn.congr
    (f := fun q : B × Subgroup.centralizer {J₀} ↦
      (e.orthonormalFrameBundle cF β).toOpenPartialHomeomorph.symm
        (q.1, adaptedCorrection β c (localStructure J e cF β q.1) * q.2)) ?_
    fun q hq ↦ coe_unitaryTrivializationInv hJ₂ hJ₀ hβ₁ hβ₃ p₀ hq.1)
  refine (e.orthonormalFrameBundle cF β).toOpenPartialHomeomorph.continuousOn_symm.comp
    (continuousOn_fst.prodMk ?_) fun _ hq ↦
      (e.orthonormalFrameBundle cF β).mem_target.2 (mem_baseSet_orthonormalFrameBundle hq.1.1)
  exact ((continuousOn_adaptedCorrection_localStructure hJ₂ hJ).comp continuousOn_fst
    mapsTo_fst_prod).mul (continuous_subtypeVal.comp continuous_snd).continuousOn

variable (e cF β c) in
/-- The trivialization of the unitary frames over the good set, with fibre the centralizer of
`J₀`: a frame `p` over `y` goes to `(y, Φ_y⁻¹ * (T p).2)`, where `T` is the Gram–Schmidt
trivialization of the frame bundle over `e` and `Φ_y` the adapted correction making its local frame
unitary. The unitary frame `p₀` is a junk value of the inverse off its target. -/
private def unitaryTrivialization (p₀ : unitaryFrames F J J₀) :
    Trivialization (Subgroup.centralizer {J₀})
      (fun p : unitaryFrames F J J₀ ↦ (p : OrthonormalFrameBundle ℝ F E V).proj) where
  toFun p := (p.val.proj, toCentralizer J₀
    ((adaptedCorrection β c (localStructure J e cF β p.val.proj))⁻¹ *
      (e.orthonormalFrameBundle cF β p.val).2))
  invFun := unitaryTrivializationInv J J₀ e cF β c p₀
  source := {p | p.val.proj ∈ goodSet J e cF β c}
  target := goodSet J e cF β c ×ˢ univ
  map_source' _ hp := ⟨hp, mem_univ _⟩
  map_target' q hq := by
    rw [mem_ofPred_eq, coe_unitaryTrivializationInv hJ₂ hJ₀ hβ₁ hβ₃ p₀ hq.1,
      (e.orthonormalFrameBundle cF β).proj_symm_apply'
        (mem_baseSet_orthonormalFrameBundle hq.1.1)]
    exact hq.1
  left_inv' p hp := by
    have hm := inv_mul_mem_centralizer hJ₂ hJ₀ hβ₁ hβ₃ hp p.property
    apply Subtype.ext
    rw [coe_unitaryTrivializationInv (q := (p.val.proj, _)) hJ₂ hJ₀ hβ₁ hβ₃ p₀ hp,
      coe_toCentralizer hm, mul_inv_cancel_left]
    exact (e.orthonormalFrameBundle cF β).symm_apply_mk_proj
      ((e.orthonormalFrameBundle cF β).mem_source.2 (mem_baseSet_orthonormalFrameBundle hp.1))
  right_inv' := by
    rintro ⟨y, g⟩ hq
    rw [Prod.mk.injEq, coe_unitaryTrivializationInv hJ₂ hJ₀ hβ₁ hβ₃ p₀ hq.1,
      (e.orthonormalFrameBundle cF β).proj_symm_apply' (mem_baseSet_orthonormalFrameBundle hq.1.1),
      (e.orthonormalFrameBundle cF β).apply_symm_apply' (mem_baseSet_orthonormalFrameBundle hq.1.1),
      inv_mul_cancel_left]
    exact ⟨rfl, Subtype.ext (coe_toCentralizer g.property)⟩
  open_source := (isOpen_goodSet e cF β c hJ).preimage (continuous_proj.comp continuous_subtypeVal)
  open_target := (isOpen_goodSet e cF β c hJ).prod isOpen_univ
  continuousOn_toFun := by
    have hproj : Continuous
        fun p : unitaryFrames F J J₀ ↦ (p : OrthonormalFrameBundle ℝ F E V).proj :=
      continuous_proj.comp continuous_subtypeVal
    refine hproj.continuousOn.prodMk (continuousOn_toCentralizer ?_
      fun p hp ↦ inv_mul_mem_centralizer hJ₂ hJ₀ hβ₁ hβ₃ hp p.property)
    exact (((continuousOn_adaptedCorrection_localStructure hJ₂ hJ).comp hproj.continuousOn
      fun _ hp ↦ hp).inv).mul (continuous_snd.comp_continuousOn
        ((e.orthonormalFrameBundle cF β).continuousOn_toFun.comp continuous_subtypeVal.continuousOn
          fun _ hp ↦ (e.orthonormalFrameBundle cF β).mem_source.2
            (mem_baseSet_orthonormalFrameBundle hp.1)))
  continuousOn_invFun := continuousOn_unitaryTrivializationInv hJ₂ hJ₀ hβ₁ hβ₃ hJ p₀
  baseSet := goodSet J e cF β c
  open_baseSet := isOpen_goodSet e cF β c hJ
  source_eq := rfl
  target_eq := rfl
  proj_toFun _ _ := rfl

private theorem unitaryTrivialization_apply (p₀ p : unitaryFrames F J J₀) :
    unitaryTrivialization e cF β c hJ₂ hJ₀ hβ₁ hβ₃ hJ p₀ p =
      (p.val.proj, toCentralizer J₀
        ((adaptedCorrection β c (localStructure J e cF β p.val.proj))⁻¹ *
          (e.orthonormalFrameBundle cF β p.val).2)) :=
  rfl

/-- The trivialization `unitaryTrivialization` is equivariant over its base set. -/
private theorem unitaryTrivialization_smul (p₀ : unitaryFrames F J J₀)
    (g : Subgroup.centralizer {J₀}) {p : unitaryFrames F J J₀}
    (hp : (p : OrthonormalFrameBundle ℝ F E V).proj ∈ goodSet J e cF β c) :
    unitaryTrivialization e cF β c hJ₂ hJ₀ hβ₁ hβ₃ hJ p₀ (op g • p) =
      ((unitaryTrivialization e cF β c hJ₂ hJ₀ hβ₁ hβ₃ hJ p₀ p).1,
        (unitaryTrivialization e cF β c hJ₂ hJ₀ hβ₁ hβ₃ hJ p₀ p).2 * g) := by
  have hgp : ((op g • p : unitaryFrames F J J₀) : OrthonormalFrameBundle ℝ F E V).proj ∈
      goodSet J e cF β c := by
    rwa [coe_unitaryFrames_smul, proj_smul]
  have h₁ := inv_mul_mem_centralizer hJ₂ hJ₀ hβ₁ hβ₃ hp p.property
  have h₂ := inv_mul_mem_centralizer hJ₂ hJ₀ hβ₁ hβ₃ hgp (op g • p).property
  rw [coe_unitaryFrames_smul, unop_op, proj_smul] at h₂
  simp only [unitaryTrivialization_apply, coe_unitaryFrames_smul, unop_op, proj_smul]
  refine Prod.ext rfl (Subtype.ext ?_)
  rw [Subgroup.coe_mul, coe_toCentralizer h₁, coe_toCentralizer h₂,
    Trivialization.orthonormalFrameBundle_smul, mul_assoc]

end Hypotheses

end Trivialization

/-- In rank four, the unitary frames of a continuous fibrewise orthogonal complex structure `J` are
locally trivial with fibre the centralizer of `J₀` in the orthogonal group, the unitary group
`U(V, J₀) ≅ U(2)`, by trivializations equivariant for its right action. This is the local
triviality of the reduction of the orthonormal frame bundle of `E` from `O(4)` to `U(2)` given
by `J`. -/
theorem exists_trivialization_unitaryFrames {B : Type*} [TopologicalSpace B] {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F] {E : B → Type*} [∀ x, NormedAddCommGroup (E x)]
    [∀ x, InnerProductSpace ℝ (E x)] [TopologicalSpace (TotalSpace F E)] [FiberBundle F E]
    [VectorBundle ℝ F E] [ContinuousFiberNorm F E] {V : Type*} [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] [CompleteSpace V] {J : ∀ b, E b ≃ₗᵢ[ℝ] E b}
    {J₀ : unitary (V →L[ℝ] V)}
    (hJ : Continuous fun v : TotalSpace F E ↦ (⟨v.proj, J v.proj v.snd⟩ : TotalSpace F E))
    (hJ₂ : ∀ b v, J b (J b v) = -v) (hJ₀ : ∀ v, (J₀ : V →L[ℝ] V) ((J₀ : V →L[ℝ] V) v) = -v)
    (hV : finrank ℝ V = 4) (hF : finrank ℝ F = 4) (x : B) :
    ∃ t : Trivialization (Subgroup.centralizer {J₀})
        (fun p : unitaryFrames F J J₀ ↦ (p : OrthonormalFrameBundle ℝ F E V).proj),
      x ∈ t.baseSet ∧ ∀ (g : Subgroup.centralizer {J₀}) (p : unitaryFrames F J J₀),
        (p : OrthonormalFrameBundle ℝ F E V).proj ∈ t.baseSet →
          t (op g • p) = ((t p).1, (t p).2 * g) := by
  have : Fact (finrank ℝ V = 4) := ⟨hV⟩
  have : FiniteDimensional ℝ V := Module.finite_of_finrank_pos (by omega)
  have : FiniteDimensional ℝ F := Module.finite_of_finrank_pos (by omega)
  -- An orthonormal basis `β` of `V` adapted to `J₀`, `β 1 = J₀ (β 0)` and `β 3 = J₀ (β 2)`.
  let J₀' : AlmostComplexStructure V :=
    ⟨(J₀ : V →L[ℝ] V).toLinearMap, LinearMap.ext fun v ↦ by simpa using hJ₀ v⟩
  obtain ⟨β, -, hβ₁, hβ₃⟩ := AlmostComplexStructure.exists_unitary_orthonormalBasis_of_norm_eq_one
    (J := J₀') (Unitary.inner_map_map J₀)
    ((stdOrthonormalBasis ℝ V).orthonormal.1 ⟨0, by omega⟩)
  let e := trivializationAt F E x
  let cF := Module.finBasisOfFinrankEq ℝ F hF
  -- Some vector of `β` lies outside the complex line of `β 0` for `J` read at `x`.
  obtain ⟨j, hj⟩ := exists_residual_ne_zero (localStructure J e cF β x : V →L[ℝ] V) (β 0) β
  have hx : x ∈ goodSet J e cF β (β j) := ⟨mem_baseSet_trivializationAt F E x, hj⟩
  let p₀ : unitaryFrames F J J₀ := ⟨_, correctedFrame_mem hJ₂ hJ₀ hβ₁.symm hβ₃.symm hx⟩
  exact ⟨unitaryTrivialization e cF β (β j) hJ₂ hJ₀ hβ₁.symm hβ₃.symm hJ p₀, hx,
    fun g _ hp ↦ unitaryTrivialization_smul hJ₂ hJ₀ hβ₁.symm hβ₃.symm hJ p₀ g hp⟩

end TauCeti.OrthonormalFrameBundle
