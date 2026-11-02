/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Cayley.Smooth
public import TauCeti.Geometry.Symplectic.Manifold.AlmostComplex.Pullback

/-!
# Smooth Cayley paths between compatible almost complex structures

Let `σ` be a two-form on a finite-dimensional manifold `M` and let `J₀`, `J₁` be smooth almost
complex structures on `M` compatible with `σ`. At each point `x`, the linear Cayley path
`TauCeti.SymplecticForm.Compatible.cayleyPath` joins `J₀ x` to `J₁ x` through
`σ_x`-compatible complex structures: it is `J₀ (1 + C)(1 - C)⁻¹` for the cutoff-scaled Cayley
coordinate `C = smoothTransition t • (-(1 + J₀ J₁)(1 - J₀ J₁)⁻¹)`. This file assembles these
pointwise paths into smooth almost complex structures on `M`,

`TauCeti.SmoothTwoForm.Compatible.cayleyPath hJ₀ hJ₁ t`,

which are `σ`-compatible for every real `t`, equal to `J₀` for `t ≤ 0` and to `J₁` for `t ≥ 1`.
The path is smooth jointly in the parameter and the point: for smooth maps `b : N → M` and
`c : N → ℝ`, the endomorphism of `T_(b n) M` given by the path at time `c n` depends smoothly on
`n` (`TauCeti.SmoothTwoForm.Compatible.contMDiff_cayleyPath`). Thus it is a smooth family of
compatible structures parametrized by `ℝ × M`, constant near both ends of `[0, 1]`, as needed to
glue such paths end to end.

Since the path is given by a rational formula in `J₀` and `J₁`, it is natural: pulling it back
along a diffeomorphism gives the path between the pulled-back structures, for the pulled-back
form (`TauCeti.SmoothTwoForm.Compatible.pullback_cayleyPath`).

## Main definitions

* `TauCeti.SmoothTwoForm.Compatible.cayleyPath hJ₀ hJ₁ t`: the smooth Cayley path from `J₀` to
  `J₁` at time `t`.

## Main results

* `TauCeti.SmoothTwoForm.Compatible.compatible_cayleyPath`: the path is compatible with `σ`.
* `TauCeti.SmoothTwoForm.Compatible.cayleyPath_of_nonpos`,
  `TauCeti.SmoothTwoForm.Compatible.cayleyPath_of_one_le`: it is constant outside `(0, 1)`.
* `TauCeti.SmoothTwoForm.Compatible.contMDiff_cayleyPath`: joint smoothness in the time and the
  point.
* `TauCeti.SmoothTwoForm.Compatible.pullback_cayleyPath`: naturality under diffeomorphisms.

## References

* D. McDuff and D. Salamon, *Introduction to Symplectic Topology*, third edition,
  Section 2.5 (the Cayley chart on compatible complex structures).
* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, second edition,
  Section 2.2 (smooth families of compatible almost complex structures).
-/

public noncomputable section

open Bundle Set
open scoped Manifold ContDiff Topology

namespace TauCeti

/-- The Cayley interpolation formula `a (1 + C)(1 - C)⁻¹`, `C = s • (-(1 + a b)(1 - a b)⁻¹)`,
in an arbitrary real algebra. -/
private def cayleyFormula {R : Type*} [Ring R] [Algebra ℝ R] (a b : R) (s : ℝ) : R :=
  a * (1 + s • -((1 + a * b) * Ring.inverse (1 - a * b))) *
    Ring.inverse (1 - s • -((1 + a * b) * Ring.inverse (1 - a * b)))

/-- Algebra isomorphisms commute with the Cayley interpolation formula. -/
private theorem map_cayleyFormula {R S F : Type*} [Ring R] [Algebra ℝ R] [Ring S] [Algebra ℝ S]
    [EquivLike F R S] [AlgEquivClass F ℝ R S] (f : F) (a b : R) (s : ℝ) :
    f (cayleyFormula a b s) = cayleyFormula (f a) (f b) s := by
  simp only [cayleyFormula, map_mul, map_add, map_one, map_neg, map_sub, map_smul,
    map_ringInverse]

/-- The Cayley interpolation formula is smooth at every point where both inverses it takes are
of units. -/
private theorem contDiffAt_cayleyFormula {R : Type*} [NormedRing R] [NormedAlgebra ℝ R]
    [CompleteSpace R] {p : R × R × ℝ} (h₁ : IsUnit (1 - p.1 * p.2.1))
    (h₂ : IsUnit (1 - p.2.2 • -((1 + p.1 * p.2.1) * Ring.inverse (1 - p.1 * p.2.1)))) :
    ContDiffAt ℝ ∞ (fun q : R × R × ℝ ↦ cayleyFormula q.1 q.2.1 q.2.2) p := by
  obtain ⟨u₁, hu₁⟩ := h₁
  obtain ⟨u₂, hu₂⟩ := h₂
  have hab : ContDiffAt ℝ ∞ (fun q : R × R × ℝ ↦ q.1 * q.2.1) p :=
    contDiffAt_fst.mul contDiffAt_snd.fst
  have hinv₁ : ContDiffAt ℝ ∞ (fun q : R × R × ℝ ↦ Ring.inverse (1 - q.1 * q.2.1)) p := by
    have hi := contDiffAt_ringInverse (n := ∞) ℝ u₁
    rw [hu₁] at hi
    exact hi.comp p (contDiffAt_const.sub hab)
  have hC : ContDiffAt ℝ ∞ (fun q : R × R × ℝ ↦
      q.2.2 • -((1 + q.1 * q.2.1) * Ring.inverse (1 - q.1 * q.2.1))) p :=
    contDiffAt_snd.snd.smul ((contDiffAt_const.add hab).mul hinv₁).neg
  have hinv₂ : ContDiffAt ℝ ∞ (fun q : R × R × ℝ ↦
      Ring.inverse (1 - q.2.2 • -((1 + q.1 * q.2.1) * Ring.inverse (1 - q.1 * q.2.1)))) p := by
    have hi := contDiffAt_ringInverse (n := ∞) ℝ u₂
    rw [hu₂] at hi
    exact hi.comp p (contDiffAt_const.sub hC)
  exact (contDiffAt_fst.mul (contDiffAt_const.add hC)).mul hinv₂

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  {ω₀ : SymplecticForm V} {A₀ A₁ : AlmostComplexStructure V}

/-- The linear Cayley path in operator-norm coordinates, as the Cayley interpolation formula. -/
private theorem toContinuousLinearMap_cayleyPath_eq_cayleyFormula (h₀ : ω₀.Compatible A₀)
    (h₁ : ω₀.Compatible A₁) (t : ℝ) :
    LinearMap.toContinuousLinearMap (h₀.cayleyPath h₁ t).toLinearMap =
      cayleyFormula (LinearMap.toContinuousLinearMap A₀.toLinearMap)
        (LinearMap.toContinuousLinearMap A₁.toLinearMap) (Real.smoothTransition t) := by
  rw [h₀.toContinuousLinearMap_cayleyPath, AlmostComplexStructure.toContinuousLinearMap_cayley,
    cayleyFormula]

/-- The two inverses taken by the Cayley interpolation formula between two `ω₀`-compatible
structures, for a parameter in `[0, 1]`, are inverses of units. -/
private theorem isUnit_cayleyFormula (h₀ : ω₀.Compatible A₀) (h₁ : ω₀.Compatible A₁) {s : ℝ}
    (hs : s ∈ Icc (0 : ℝ) 1) :
    IsUnit (1 - LinearMap.toContinuousLinearMap A₀.toLinearMap *
        LinearMap.toContinuousLinearMap A₁.toLinearMap) ∧
      IsUnit (1 - s • -((1 + LinearMap.toContinuousLinearMap A₀.toLinearMap *
          LinearMap.toContinuousLinearMap A₁.toLinearMap) *
        Ring.inverse (1 - LinearMap.toContinuousLinearMap A₀.toLinearMap *
          LinearMap.toContinuousLinearMap A₁.toLinearMap))) := by
  refine ⟨ContinuousLinearMap.isUnit_iff_isUnit_toLinearMap.2 ?_, ?_⟩
  · simpa only [ContinuousLinearMap.toLinearMap_sub, ContinuousLinearMap.toLinearMap_one,
      ContinuousLinearMap.toLinearMap_mul, LinearMap.coe_toContinuousLinearMap] using
      h₀.tames.isUnit_one_sub_mul h₁.tames
  · rw [← AlmostComplexStructure.toContinuousLinearMap_cayley]
    have hmem : (s • LinearMap.toContinuousLinearMap (A₀.cayley A₁)).toLinearMap ∈
        ω₀.cayleyBall A₀ := SymplecticForm.compatibleCayleyBall_subset_cayleyBall (by
      simpa only [ContinuousLinearMap.toLinearMap_smul, LinearMap.coe_toContinuousLinearMap] using
        h₀.smul_cayley_mem_compatibleCayleyBall h₁ hs)
    exact SymplecticForm.isUnit_one_sub_of_toLinearMap_mem_cayleyBall hmem

variable {W : Type*} [AddCommGroup W] [Module ℝ W] [TopologicalSpace W] [IsTopologicalAddGroup W]
  [ContinuousSMul ℝ W] {ωW : SymplecticForm W} {B : AlmostComplexStructure W}

/-- Conjugating a continuous endomorphism by a linear equivalence `e` is transporting the
almost complex structure it represents along `e`. -/
private theorem conjContinuousAlgEquiv_eq_toContinuousLinearMap_transport (e : W ≃L[ℝ] V)
    {b : W →L[ℝ] W} (hb : b.toLinearMap = B.toLinearMap) :
    e.conjContinuousAlgEquiv b =
      LinearMap.toContinuousLinearMap (B.transport e.toLinearEquiv).toLinearMap := by
  ext v
  simp [← hb]

/-- The Cayley interpolation formula between two `ωW`-compatible structures on `W` is the linear
Cayley path between their transports along a linear equivalence `e` to a normed space,
transported back along `e`. -/
private theorem toLinearMap_cayleyFormula_eq_transport (e : W ≃L[ℝ] V)
    {B₀ B₁ : AlmostComplexStructure W}
    (h₀ : ωW.Compatible B₀) (h₁ : ωW.Compatible B₁) {b₀ b₁ : W →L[ℝ] W}
    (hb₀ : b₀.toLinearMap = B₀.toLinearMap) (hb₁ : b₁.toLinearMap = B₁.toLinearMap) (t : ℝ) :
    (cayleyFormula b₀ b₁ (Real.smoothTransition t)).toLinearMap =
      (((h₀.transport e.toLinearEquiv).cayleyPath (h₁.transport e.toLinearEquiv) t).transport
        e.symm.toLinearEquiv).toLinearMap := by
  have hP := toContinuousLinearMap_cayleyPath_eq_cayleyFormula (h₀.transport e.toLinearEquiv)
    (h₁.transport e.toLinearEquiv) t
  rw [← conjContinuousAlgEquiv_eq_toContinuousLinearMap_transport e hb₀,
    ← conjContinuousAlgEquiv_eq_toContinuousLinearMap_transport e hb₁,
    ← map_cayleyFormula] at hP
  ext v
  have hv := congrArg (fun f : V →L[ℝ] V ↦ e.symm (f (e v))) hP
  simp only [LinearMap.coe_toContinuousLinearMap',
    ContinuousLinearEquiv.conjContinuousAlgEquiv_apply_apply,
    ContinuousLinearEquiv.symm_apply_apply] at hv
  simp [← hv]

variable {E H M E' H' M' F G N : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E']
  [TopologicalSpace H'] {I' : ModelWithCorners ℝ E' H'}
  [TopologicalSpace M'] [ChartedSpace H' M'] [IsManifold I' ∞ M']
  [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace G] {IN : ModelWithCorners ℝ F G}
  [TopologicalSpace N] [ChartedSpace G N]

namespace SmoothTwoForm.Compatible

variable {σ : SmoothTwoForm I M} {J₀ J₁ : SmoothAlmostComplexStructure I M}
  (hJ₀ : σ.Compatible J₀) (hJ₁ : σ.Compatible J₁)

omit [FiniteDimensional ℝ E] in
include hJ₀ hJ₁ in
/-- At each point, the Cayley interpolation formula between the endomorphisms of `J₀` and `J₁`
is the linear Cayley path for `σ_x`, read through any linear equivalence of `T_x M` with a
normed space. -/
private theorem toLinearMap_cayleyFormula_eq (x : M) {V : Type*} [NormedAddCommGroup V]
    [NormedSpace ℝ V] [FiniteDimensional ℝ V] (e : TangentSpace I x ≃L[ℝ] V) (t : ℝ) :
    (cayleyFormula (J₀.toEndomorphism x) (J₁.toEndomorphism x)
        (Real.smoothTransition t)).toLinearMap =
      ((((hJ₀.compatibleAt x).transport e.toLinearEquiv).cayleyPath
        ((hJ₁.compatibleAt x).transport e.toLinearEquiv) t).transport
          e.symm.toLinearEquiv).toLinearMap :=
  toLinearMap_cayleyFormula_eq_transport e (hJ₀.compatibleAt x) (hJ₁.compatibleAt x)
    (J₀.almostComplexStructureAt_toLinearMap x).symm
    (J₁.almostComplexStructureAt_toLinearMap x).symm t

/-- The trivialization of the tangent bundle at `x`, as a linear equivalence of `T_x M` with
the model space. -/
private def tangentChart (x : M) : TangentSpace I x ≃L[ℝ] E :=
  (trivializationAt E (TangentSpace I) x).continuousLinearEquivAt ℝ x
    (mem_baseSet_trivializationAt E (TangentSpace I) x)

include hJ₀ hJ₁ in
/-- The Cayley interpolation formula between the endomorphism sections of `J₀` and `J₁`, along a
smooth map `b` and with a smooth parameter `s` valued in `[0, 1]`, is smooth. -/
private theorem contMDiffAt_cayleyFormula {b : N → M} {s : N → ℝ} {n₀ : N}
    (hb : ContMDiffAt IN I ∞ b n₀) (hs : ContMDiffAt IN 𝓘(ℝ) ∞ s n₀)
    (hs₀ : s n₀ ∈ Icc (0 : ℝ) 1) :
    ContMDiffAt IN (I.prod 𝓘(ℝ, E →L[ℝ] E)) ∞
      (fun n ↦ TotalSpace.mk' (E →L[ℝ] E)
        (E := fun x : M ↦ TangentSpace I x →L[ℝ] TangentSpace I x) (b n)
        (cayleyFormula (J₀.toEndomorphism (b n)) (J₁.toEndomorphism (b n)) (s n))) n₀ := by
  rw [contMDiffAt_hom_bundle]
  refine ⟨hb, ?_⟩
  set e := trivializationAt E (TangentSpace I) (b n₀)
  -- Near `n₀`, reading in the trivialization at `b n₀` is conjugation by an algebra isomorphism.
  have hcoord : ∀ᶠ n in 𝓝 n₀, ∃ hn : b n ∈ e.baseSet,
      ∀ ψ : TangentSpace I (b n) →L[ℝ] TangentSpace I (b n),
        ContinuousLinearMap.inCoordinates E (TangentSpace I) E (TangentSpace I)
          (b n₀) (b n) (b n₀) (b n) ψ =
            (e.continuousLinearEquivAt ℝ (b n) hn).conjContinuousAlgEquiv ψ := by
    filter_upwards [hb.continuousAt.preimage_mem_nhds
      (e.open_baseSet.mem_nhds (mem_baseSet_trivializationAt E (TangentSpace I) (b n₀)))]
      with n hn
    exact ⟨hn, fun ψ ↦ ContinuousLinearMap.inCoordinates_eq hn hn⟩
  have hA := ((contMDiffAt_hom_bundle _).1
    ((J₀.toEndomorphism.contMDiff (b n₀)).comp n₀ hb)).2
  have hB := ((contMDiffAt_hom_bundle _).1
    ((J₁.toEndomorphism.contMDiff (b n₀)).comp n₀ hb)).2
  obtain ⟨hn₀, hf₀⟩ := hcoord.self_of_nhds
  -- At `n₀`, the coordinate expressions are the transports of `J₀` and `J₁` to the model, so the
  -- inverses taken by the formula there are of units.
  obtain ⟨hu₁, hu₂⟩ := isUnit_cayleyFormula
    ((hJ₀.compatibleAt (b n₀)).transport (e.continuousLinearEquivAt ℝ (b n₀) hn₀).toLinearEquiv)
    ((hJ₁.compatibleAt (b n₀)).transport (e.continuousLinearEquivAt ℝ (b n₀) hn₀).toLinearEquiv)
    hs₀
  rw [← conjContinuousAlgEquiv_eq_toContinuousLinearMap_transport _
      (J₀.almostComplexStructureAt_toLinearMap (b n₀)).symm,
    ← conjContinuousAlgEquiv_eq_toContinuousLinearMap_transport _
      (J₁.almostComplexStructureAt_toLinearMap (b n₀)).symm, ← hf₀, ← hf₀] at hu₁ hu₂
  -- The coordinate expressions of `J₀` and `J₁`.
  let a : N → E →L[ℝ] E := fun n ↦ ContinuousLinearMap.inCoordinates E (TangentSpace I)
    E (TangentSpace I) (b n₀) (b n) (b n₀) (b n) (J₀.toEndomorphism (b n))
  let c : N → E →L[ℝ] E := fun n ↦ ContinuousLinearMap.inCoordinates E (TangentSpace I)
    E (TangentSpace I) (b n₀) (b n) (b n₀) (b n) (J₁.toEndomorphism (b n))
  have hsmooth : ContMDiffAt IN 𝓘(ℝ, E →L[ℝ] E) ∞
      (fun n ↦ cayleyFormula (a n) (c n) (s n)) n₀ :=
    (contDiffAt_cayleyFormula (p := (a n₀, c n₀, s n₀)) hu₁ hu₂).comp_contMDiffAt
      (f := fun n ↦ (a n, c n, s n)) (x := n₀) (hA.prodMk_space (hB.prodMk_space hs))
  refine hsmooth.congr_of_eventuallyEq ?_
  filter_upwards [hcoord] with n ⟨hn, hf⟩
  simp only [a, c, hf, map_cayleyFormula]

/-- The smooth Cayley path from `J₀` to `J₁` at time `t`: at each point `x` it is the linear
Cayley path from `J₀ x` to `J₁ x` for the symplectic form `σ_x`
(`TauCeti.SmoothTwoForm.Compatible.cayleyPath_almostComplexStructureAt`). -/
def cayleyPath (t : ℝ) : SmoothAlmostComplexStructure I M where
  toEndomorphism :=
    ⟨fun x ↦ cayleyFormula (J₀.toEndomorphism x) (J₁.toEndomorphism x) (Real.smoothTransition t),
      fun x ↦ contMDiffAt_cayleyFormula hJ₀ hJ₁ contMDiffAt_id contMDiffAt_const
        (mem_Icc.2 ⟨Real.smoothTransition.nonneg t, Real.smoothTransition.le_one t⟩)⟩
  square_neg x := by
    ext v
    have h := toLinearMap_cayleyFormula_eq hJ₀ hJ₁ x (tangentChart (I := I) x) t
    have hv (w : TangentSpace I x) := congrArg (fun f : Module.End ℝ (TangentSpace I x) ↦ f w) h
    simp only [ContinuousLinearMap.coe_coe] at hv
    -- The section evaluates at `x` to the Cayley interpolation formula, which is the linear
    -- Cayley path read through the trivialization at `x`.
    exact (congrArg _ (hv v)).trans ((hv _).trans (AlmostComplexStructure.apply_apply _ v))

/-- The endomorphism of `T_x M` underlying the smooth Cayley path. -/
private theorem cayleyPath_toEndomorphism (t : ℝ) (x : M) :
    (hJ₀.cayleyPath hJ₁ t).toEndomorphism x =
      cayleyFormula (J₀.toEndomorphism x) (J₁.toEndomorphism x) (Real.smoothTransition t) :=
  (rfl)

/-- At each point `x`, the smooth Cayley path is the linear Cayley path for `σ_x`, read through
any linear equivalence `e` of `T_x M` with a finite-dimensional normed space: it is the
transport along `e⁻¹` of the linear Cayley path between the transports of `J₀ x` and `J₁ x`. -/
theorem cayleyPath_almostComplexStructureAt (t : ℝ) (x : M) {V : Type*} [NormedAddCommGroup V]
    [NormedSpace ℝ V] [FiniteDimensional ℝ V] (e : TangentSpace I x ≃L[ℝ] V) :
    (hJ₀.cayleyPath hJ₁ t).almostComplexStructureAt x =
      (((hJ₀.compatibleAt x).transport e.toLinearEquiv).cayleyPath
        ((hJ₁.compatibleAt x).transport e.toLinearEquiv) t).transport e.symm.toLinearEquiv := by
  ext v
  rw [SmoothAlmostComplexStructure.almostComplexStructureAt_apply]
  exact congrArg (fun f : Module.End ℝ (TangentSpace I x) ↦ f v)
    (toLinearMap_cayleyFormula_eq hJ₀ hJ₁ x e t)

/-- The smooth Cayley path depends only on its endpoints, not on the form they are compatible
with. -/
theorem cayleyPath_congr {σ' : SmoothTwoForm I M} {J₀' J₁' : SmoothAlmostComplexStructure I M}
    (hJ₀' : σ'.Compatible J₀') (hJ₁' : σ'.Compatible J₁') (h₀ : J₀ = J₀') (h₁ : J₁ = J₁')
    (t : ℝ) : hJ₀.cayleyPath hJ₁ t = hJ₀'.cayleyPath hJ₁' t := by
  subst h₀ h₁
  apply SmoothAlmostComplexStructure.toEndomorphism_injective
  ext x : 1
  rw [cayleyPath_toEndomorphism, cayleyPath_toEndomorphism]

/-- Every structure on the smooth Cayley path is compatible with `σ`. -/
theorem compatible_cayleyPath (t : ℝ) : σ.Compatible (hJ₀.cayleyPath hJ₁ t) :=
  hJ₀.isNondegenerate.compatible_iff.2 fun x ↦ by
    have h := ((hJ₀.compatibleAt x).transport
      (tangentChart (I := I) x).toLinearEquiv).compatible_cayleyPath
      ((hJ₁.compatibleAt x).transport (tangentChart (I := I) x).toLinearEquiv) t
      |>.transport (tangentChart (I := I) x).symm.toLinearEquiv
    rwa [← cayleyPath_almostComplexStructureAt, ContinuousLinearEquiv.toLinearEquiv_symm,
      SymplecticForm.transport_symm_transport] at h

/-- The smooth Cayley path is `J₀` up to time zero. -/
theorem cayleyPath_of_nonpos {t : ℝ} (ht : t ≤ 0) : hJ₀.cayleyPath hJ₁ t = J₀ := by
  ext x v
  rw [← SmoothAlmostComplexStructure.almostComplexStructureAt_apply,
    cayleyPath_almostComplexStructureAt _ _ t x (tangentChart (I := I) x),
    SymplecticForm.Compatible.cayleyPath_of_nonpos _ _ ht, ContinuousLinearEquiv.toLinearEquiv_symm,
    AlmostComplexStructure.transport_symm_transport,
    SmoothAlmostComplexStructure.almostComplexStructureAt_apply]

/-- The smooth Cayley path is `J₁` from time one on. -/
theorem cayleyPath_of_one_le {t : ℝ} (ht : 1 ≤ t) : hJ₀.cayleyPath hJ₁ t = J₁ := by
  ext x v
  rw [← SmoothAlmostComplexStructure.almostComplexStructureAt_apply,
    cayleyPath_almostComplexStructureAt _ _ t x (tangentChart (I := I) x),
    SymplecticForm.Compatible.cayleyPath_of_one_le _ _ ht, ContinuousLinearEquiv.toLinearEquiv_symm,
    AlmostComplexStructure.transport_symm_transport,
    SmoothAlmostComplexStructure.almostComplexStructureAt_apply]

/-- The smooth Cayley path is jointly smooth in the time and the point: along smooth maps
`b : N → M` and `c : N → ℝ`, its endomorphism of `T_(b n) M` at time `c n` depends smoothly
on `n`. -/
theorem contMDiff_cayleyPath {b : N → M} (hb : ContMDiff IN I ∞ b) {c : N → ℝ}
    (hc : ContMDiff IN 𝓘(ℝ) ∞ c) :
    ContMDiff IN (I.prod 𝓘(ℝ, E →L[ℝ] E)) ∞
      (fun n ↦ TotalSpace.mk' (E →L[ℝ] E)
        (E := fun x : M ↦ TangentSpace I x →L[ℝ] TangentSpace I x) (b n)
        ((hJ₀.cayleyPath hJ₁ (c n)).toEndomorphism (b n))) := fun n ↦
  contMDiffAt_cayleyFormula hJ₀ hJ₁ (hb n)
    ((Real.smoothTransition.contDiff.contMDiff.comp hc) n)
    (mem_Icc.2 ⟨Real.smoothTransition.nonneg _, Real.smoothTransition.le_one _⟩)

end SmoothTwoForm.Compatible

namespace SmoothTwoForm.Compatible

variable {σ : SmoothTwoForm I' M'} {J₀ J₁ : SmoothAlmostComplexStructure I' M'}

/-- Pulling the smooth Cayley path back along a diffeomorphism gives the smooth Cayley path
between the pulled-back structures, for the pulled-back form. -/
theorem pullback_cayleyPath (hJ₀ : σ.Compatible J₀) (hJ₁ : σ.Compatible J₁)
    (h : M ≃ₘ⟮I, I'⟯ M') (t : ℝ) :
    (hJ₀.cayleyPath hJ₁ t).pullback h = (hJ₀.pullback h).cayleyPath (hJ₁.pullback h) t := by
  apply SmoothAlmostComplexStructure.toEndomorphism_injective
  ext x : 1
  -- Both sides are the Cayley interpolation formula, and pulling back is a conjugation.
  rw [SmoothAlmostComplexStructure.pullback_toEndomorphism, cayleyPath_toEndomorphism,
    cayleyPath_toEndomorphism, map_cayleyFormula,
    SmoothAlmostComplexStructure.pullback_toEndomorphism,
    SmoothAlmostComplexStructure.pullback_toEndomorphism]

end SmoothTwoForm.Compatible

end TauCeti
