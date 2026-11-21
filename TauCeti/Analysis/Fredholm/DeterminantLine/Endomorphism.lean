/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Fredholm.DeterminantLine.Transport
public import TauCeti.LinearAlgebra.Determinant.Endomorphism
import TauCeti.LinearAlgebra.Dimension.Submodule

/-!
# Determinant lines of families of endomorphisms

Let `V` be a finite-dimensional real normed space. Every endomorphism `T` of `V` is Fredholm, and
its determinant line `det T = det (ker T) ⊗ (det (coker T))^*` has a canonical trivialization
`LinearMap.detLineEndEquiv`, through the exact sequence `0 → ker T → V → V → coker T → 0` and the
contraction `det V ⊗ (det V)^* ≃ ℝ`. This file shows that, after the sign normalization of
`LinearMap.detLineEndGenerator`, these trivializations are continuous in families: for every
family `T` of endomorphisms, the normalized generators

`(-1) ^ (dim (ker (T x)) * (dim V + 1)) • (detLineEndEquiv (T x)).symm 1`

form a continuous orientation of the determinant line bundle of the family
(`TauCeti.isDetLineCoherentOn_detLineEndGenerator`). The proof uses one kernel chart for all
endomorphisms: stabilizing by the whole space, `(u, s) ↦ (T u + s, u)` is invertible, the kernel
of `(u, s) ↦ T u + s` is the graph `u ↦ (-u, T u)`, and every normalized generator is read in
this chart as the same vector. The sign normalization is needed: when `dim V` is even, the
elements `(detLineEndEquiv (T x)).symm 1` themselves change sign at the parameters where the
parity of `dim (ker (T x))` jumps.

Consequently, along a continuous path of endomorphisms, transport of orientations of determinant
lines (`TauCeti.detLineOrientationTransport`) carries the normalized generator at one end to the
normalized generator at the other
(`TauCeti.detLineOrientationTransport_rayOfNeZero_detLineEndGenerator`). At a bijective `T` the
normalized generator is `det T` times the generator of the trivialization given by invertibility
(`LinearMap.detLineEndGenerator_eq_det_smul`), so between bijective endpoints transport preserves
the orientations given by invertibility when `det (T a) * det (T b) > 0`
(`TauCeti.detLineOrientationTransport_detLineEquivOfBijective_of_pos`) and reverses them when
`det (T a) * det (T b) < 0`
(`TauCeti.detLineOrientationTransport_detLineEquivOfBijective_of_neg`). The latter happens exactly
when `T a` and `T b` have numbers of negative real eigenvalues, counted with multiplicity, of
different parity. At the
realification of a complex-linear endomorphism the normalized generator is complex positive
(`LinearMap.isComplexPositiveDetLine_detLineEndGenerator`). So transporting the complex
orientation of a complex-linear endomorphism to a bijective `T b` gives the orientation of
invertibility multiplied by the sign of `det (T b)`.

This is the finite-dimensional model of the determinant signs of twisted periodic operators. The
operator `w ↦ w' - M w` on loops twisted by a sign `ε` has the kernel and cokernel of `ε - P`, `P`
its return map (`TauCeti.detLineTwistedLinearOperatorEquiv`). For the untwisted normal operator
of an orbit torus, the complex-linear reference operator has `P = 1`, and the results here give the
sign `sgn det (1 - P)` for the path of finite endomorphisms `1 - P`. Comparing this with the
transport along the twisted operators themselves needs the identification of their determinant
lines with those of `ε - P` to be coherent along families, which is not proved here.

## Main results

* `TauCeti.isDetLineCoherentOn_detLineEndGenerator`: the normalized generators of a family of
  endomorphisms are coherent.
* `TauCeti.detLineOrientationTransport_rayOfNeZero_detLineEndGenerator`: orientation transport
  carries normalized generators to normalized generators.
* `TauCeti.detLineOrientationTransport_detLineEquivOfBijective_of_pos`,
  `TauCeti.detLineOrientationTransport_detLineEquivOfBijective_of_neg`: between bijective
  endpoints, transport preserves or reverses the orientations of invertibility according to the
  sign of `det (T a) * det (T b)`.

## References

* D. McDuff, D. Salamon, *J-holomorphic Curves and Symplectic Topology*, second edition,
  AMS Colloquium Publications 52, 2012, Section A.2 (determinant line bundles).
* A. Zinger, *The determinant line bundle for Fredholm operators: construction, properties, and
  classification*, Math. Scand. 118 (2016), 203–268, arXiv:1304.6368.
* C. H. Taubes, *Counting pseudo-holomorphic submanifolds in dimension 4*, J. Differential Geom.
  44 (1996), 818–893, for the determinant signs of the twisted normal operators of tori.
-/

public section

noncomputable section

open Module TensorProduct ContinuousLinearMap Set

namespace TauCeti

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]

namespace EndKernelChart

/-! ### The kernel chart stabilizing by the whole space -/

variable (V) in
/-- The stabilizing space of the kernel chart: the whole space, embedded by the identity. -/
private abbrev S : Submodule ℝ V := ⊤

variable (V) in
/-- The model of the kernel coordinate: the first factor of `V × S`. -/
private abbrev G : Submodule ℝ (V × S V) :=
  LinearMap.range (LinearMap.inl ℝ V (S V))

/-- The kernel coordinate `(u, s) ↦ (u, 0)`. -/
private def q : V × S V →L[ℝ] G V :=
  (ContinuousLinearMap.inl ℝ V (S V) ∘L ContinuousLinearMap.fst ℝ V (S V)).codRestrict (G V)
    fun x ↦ ⟨x.1, rfl⟩

omit [FiniteDimensional ℝ V] in
private theorem coe_q_apply (x : V × S V) : (q x : V × S V) = (x.1, 0) := rfl

/-- The pair `(u, s) ↦ (A u + s, u)` is invertible for every endomorphism `A`, so the kernel
chart `(S, q)` is valid at every endomorphism. -/
private theorem isInvertible (A : V →L[ℝ] V) :
    ((A.coprod (S V).subtypeL).prod (q (V := V))).IsInvertible := by
  have hinj : Function.Injective ((A.coprod (S V).subtypeL).prod (q (V := V))) := by
    rintro ⟨u, s⟩ ⟨u', s'⟩ h
    simp only [ContinuousLinearMap.prod_apply, Prod.mk.injEq] at h
    have hu : u = u' := by
      simpa only [coe_q_apply] using congrArg (fun g : G V ↦ (g : V × S V).1) h.2
    subst hu
    refine Prod.ext rfl (Subtype.ext ?_)
    simpa using h.1
  exact ⟨(LinearMap.linearEquivOfInjective _ hinj (by simp [Module.finrank_prod,
    LinearMap.finrank_range_of_inj LinearMap.inl_injective])).toContinuousLinearEquiv, rfl⟩

variable (A : V →L[ℝ] V)

/-- The kernel of the stabilized operator `(u, s) ↦ A u + s` is the graph `u ↦ (-u, A u)`. -/
private def kerCoprodEquiv : V ≃ₗ[ℝ] (A.coprod (S V).subtypeL).ker where
  toFun u := ⟨(-u, ⟨A u, trivial⟩), by simp⟩
  invFun x := -(x : V × S V).1
  map_add' u v := Subtype.ext (Prod.ext (neg_add _ _) (Subtype.ext (map_add A u v)))
  map_smul' c u := Subtype.ext (Prod.ext (smul_neg c u).symm (Subtype.ext (map_smul A c u)))
  left_inv u := by simp
  right_inv := by
    rintro ⟨⟨u, s⟩, hx⟩
    rw [LinearMap.mem_ker, ContinuousLinearMap.coe_coe, ContinuousLinearMap.coprod_apply] at hx
    have hs : (s : V) = -A u := eq_neg_of_add_eq_zero_right hx
    exact Subtype.ext (Prod.ext (by simp) (Subtype.ext (by simp [hs])))

omit [FiniteDimensional ℝ V] in
private theorem kerCoprodEquiv_apply (u : V) :
    (kerCoprodEquiv A u : V × S V) = (-u, ⟨A u, trivial⟩) := rfl

variable (V) in
/-- The reading of the graph in the kernel coordinate, `u ↦ (-u, 0)`, which does not depend on
`A`. -/
private def graphCoord : V ≃ₗ[ℝ] G V :=
  (LinearEquiv.neg ℝ).trans (LinearEquiv.ofInjective (LinearMap.inl ℝ V (S V))
    LinearMap.inl_injective)

private theorem kerCoprodEquiv_trans_kerEquivOfProd_symm :
    (kerCoprodEquiv A).trans
        (kerEquivOfProd (A.coprod (S V).subtypeL) q (isInvertible A)).toLinearEquiv.symm =
      graphCoord V := by
  ext u : 2
  simp [graphCoord, kerCoprodEquiv_apply, coe_q_apply]

/-- `LinearEquiv.neg` acts on the determinant line by `(-1) ^ n`
(`LinearEquiv.detLineCongr_neg_apply`), here on the first factor of a tensor product with a dual
determinant line. -/
private theorem congr_neg_refl {M N : Type*} [AddCommGroup M] [Module ℝ M] [AddCommGroup N]
    [Module ℝ N] (z : detLine ℝ M ⊗[ℝ] Dual ℝ (detLine ℝ N)) :
    TensorProduct.congr (LinearEquiv.neg ℝ : M ≃ₗ[ℝ] M).detLineCongr
        (LinearEquiv.refl ℝ N).detLineCongr.symm.dualMap z =
      (-1 : ℝ) ^ finrank ℝ M • z := by
  induction z using TensorProduct.inductionOn with
  | tmul x φ =>
    rw [TensorProduct.congr_tmul, LinearEquiv.detLineCongr_neg_apply, LinearEquiv.detLineCongr_refl,
      LinearEquiv.refl_symm, LinearEquiv.dualMap_refl, LinearEquiv.refl_apply, smul_tmul']
  | add x y hx hy => rw [map_add, hx, hy, smul_add]

/-- The identification of the top submodule with the space, as the stabilizer of the chart. -/
private abbrev stabEquiv : V ≃ₗ[ℝ] S V := Submodule.topEquiv.symm

/-- The four-term isomorphism of `0 → ker A → V → V → coker A → 0`, through which the canonical
trivialization `LinearMap.detLineEndEquiv` is defined. -/
private abbrev endFourTermEquiv := detLineFourTermEquiv
  (LinearMap.ker (A : V →ₗ[ℝ] V)).injective_subtype (A : V →ₗ[ℝ] V).exact_subtype_ker_map
  (A : V →ₗ[ℝ] V).exact_map_mkQ_range (LinearMap.range (A : V →ₗ[ℝ] V)).mkQ_surjective

/-- **The kernel sequence of the stabilization.** The sequence
`0 → ker A → ker (A.coprod S) → S → coker A → 0` is isomorphic to
`0 → ker A → V → V → coker A → 0` through `-1` on `ker A` and the graph `u ↦ (-u, A u)`, so the
four-term isomorphisms of the two sequences differ by `(-1) ^ dim (ker A)`. -/
private theorem endFourTermEquiv_eq_neg_one_pow_smul (t : detLine ℝ V ⊗[ℝ] Dual ℝ (detLine ℝ V)) :
    endFourTermEquiv A t = (-1 : ℝ) ^ finrank ℝ A.ker •
      detLineCoprodEquiv A (S V).subtypeL (surjective_of_isInvertible_prod (isInvertible A))
        (TensorProduct.congr (kerCoprodEquiv A).detLineCongr
          (stabEquiv (V := V)).detLineCongr.symm.dualMap t) := by
  have hnat := detLineFourTermEquiv_congr (LinearMap.ker (A : V →ₗ[ℝ] V)).injective_subtype
    (A : V →ₗ[ℝ] V).exact_subtype_ker_map (A : V →ₗ[ℝ] V).exact_map_mkQ_range
    (LinearMap.range (A : V →ₗ[ℝ] V)).mkQ_surjective (kerCoprodHom_injective A (S V).subtypeL)
    (exact_kerCoprodHom_parameterProj A (S V).subtypeL)
    (exact_parameterProj_parameterToCoker A (S V).subtypeL)
    ((parameterToCoker_surjective_iff_coprod_surjective A (S V).subtypeL).2
      (surjective_of_isInvertible_prod (isInvertible A)))
    (LinearEquiv.neg ℝ) (kerCoprodEquiv A) stabEquiv (LinearEquiv.refl ℝ _) ?_ ?_ ?_ t
  · rw [congr_neg_refl] at hnat
    rw [detLineCoprodEquiv_def, hnat, smul_smul, ← mul_pow, neg_one_mul, neg_neg, one_pow,
      one_smul]
  · refine LinearMap.ext fun a ↦ Subtype.ext (Prod.ext ?_ (Subtype.ext ?_))
    · simp [kerCoprodHom_apply, kerCoprodEquiv_apply]
    · simp [kerCoprodHom_apply, kerCoprodEquiv_apply]
  · exact LinearMap.ext fun u ↦ Subtype.ext (by simp [parameterProj_apply, kerCoprodEquiv_apply])
  · exact LinearMap.ext fun w ↦ by simp [parameterToCoker_apply]

/-- **The reading of the canonical trivialization in the chart.** By
`endFourTermEquiv_eq_neg_one_pow_smul`, the canonical element `(detLineEndEquiv A).symm 1` is
`(-1) ^ dim (ker A)` times a stabilization element; the normalized stabilization contributes the
Koszul sign `(-1) ^ (dim (coker A) * dim V)`, and `dim (coker A) = dim (ker A)`. -/
private theorem detLineChartEquiv_detLineEndEquiv_symm_one {β : detLine ℝ V}
    {φ : Dual ℝ (detLine ℝ V)} (hφ : φ β = 1) :
    detLineChartEquiv A (S V).subtypeL q (isInvertible A)
        ((A : V →ₗ[ℝ] V).detLineEndEquiv.symm 1) =
      (-1 : ℝ) ^ (finrank ℝ A.ker * (finrank ℝ V + 1)) •
        ((graphCoord V).detLineCongr β ⊗ₜ (stabEquiv (V := V)).detLineCongr.symm.dualMap φ) := by
  have hsurj := surjective_of_isInvertible_prod (isInvertible A)
  have hE : (A : V →ₗ[ℝ] V).detLineEndEquiv.symm 1 = endFourTermEquiv A (β ⊗ₜ φ) := by
    rw [LinearEquiv.symm_apply_eq, LinearMap.detLineEndEquiv_detLineFourTermEquiv, hφ]
  -- The four-term isomorphism of `β ⊗ φ` is the normalized stabilization isomorphism of `± y`.
  have hstab : endFourTermEquiv A (β ⊗ₜ φ) = detLineStabilizationEquiv A (S V).subtypeL hsurj
      ((-1 : ℝ) ^ (finrank ℝ A.ker + finrank ℝ (V ⧸ A.range) * finrank ℝ (S V)) •
        TensorProduct.congr (kerCoprodEquiv A).detLineCongr
          (stabEquiv (V := V)).detLineCongr.symm.dualMap (β ⊗ₜ φ)) := by
    rw [map_smul, detLineStabilizationEquiv_apply, smul_smul,
      endFourTermEquiv_eq_neg_one_pow_smul]
    congr 1
    rw [← pow_add, add_assoc, pow_add, Even.neg_one_pow ⟨_, rfl⟩, mul_one]
  -- The kernel coordinate reads the graph `u ↦ (-u, A u)` as `u ↦ (-u, 0)`.
  have hβ : (kerEquivOfProd (A.coprod (S V).subtypeL) q
      (isInvertible A)).toLinearEquiv.symm.detLineCongr ((kerCoprodEquiv A).detLineCongr β) =
        (graphCoord V).detLineCongr β :=
    (LinearEquiv.congr_fun (LinearEquiv.detLineCongr_trans _ _) β).symm.trans
      (congrArg (LinearEquiv.detLineCongr · β) (kerCoprodEquiv_trans_kerEquivOfProd_symm A))
  have hsign : (-1 : ℝ) ^ (finrank ℝ A.ker + finrank ℝ (V ⧸ A.range) * finrank ℝ (S V)) =
      (-1) ^ (finrank ℝ A.ker * (finrank ℝ V + 1)) := by
    rw [LinearMap.finrank_quotient_range_eq_finrank_ker (A : V →ₗ[ℝ] V),
      show finrank ℝ (S V) = finrank ℝ V from finrank_top ℝ V]
    ring
  rw [hE, hstab, detLineChartEquiv_detLineStabilizationEquiv, LinearEquiv.map_smul]
  simp only [TensorProduct.congr_tmul, LinearEquiv.rTensor_tmul, hβ, hsign]

/-- In the identity chart, every normalized generator is read as one fixed vector. -/
private theorem exists_forall_detLineChartEquiv_detLineEndGenerator :
    ∃ c : detLine ℝ (G V) ⊗[ℝ] Dual ℝ (detLine ℝ (S V)), ∀ A : V →L[ℝ] V,
      detLineChartEquiv A (S V).subtypeL q (isInvertible A)
        (A : V →ₗ[ℝ] V).detLineEndGenerator = c := by
  have hβ : exteriorPower.ιMulti ℝ (finrank ℝ V) (Module.finBasis ℝ V) ≠ 0 :=
    (exteriorPower.ιMulti_ne_zero_iff _).2 (Module.finBasis ℝ V).linearIndependent
  obtain ⟨φ, hφ⟩ := Module.Projective.exists_dual_eq_one ℝ hβ
  refine ⟨(graphCoord V).detLineCongr (exteriorPower.ιMulti ℝ _ (Module.finBasis ℝ V)) ⊗ₜ
    (stabEquiv (V := V)).detLineCongr.symm.dualMap φ, fun A ↦ ?_⟩
  rw [LinearMap.detLineEndGenerator_def, LinearEquiv.map_smul,
    detLineChartEquiv_detLineEndEquiv_symm_one A hφ, smul_smul, ← mul_pow, neg_one_mul, neg_neg,
    one_pow, one_smul]

end EndKernelChart

open EndKernelChart

section Coherent

variable {X : Type*} [TopologicalSpace X]

/-- **The normalized generators of the determinant lines of endomorphisms are coherent.** For every
family `T` of endomorphisms of a real finite-dimensional normed space, the normalized generators
`(T x).detLineEndGenerator` form a coherent family of elements of the determinant lines, on every
set of parameters: a continuous orientation of the determinant line bundle of the family. No
continuity of `T` is needed, since a single kernel chart, stabilizing by the whole space, reads
every normalized generator as the same vector. -/
theorem isDetLineCoherentOn_detLineEndGenerator (T : X → V →L[ℝ] V) (s : Set X) :
    IsDetLineCoherentOn T (fun x ↦ (T x : V →ₗ[ℝ] V).detLineEndGenerator) s := by
  obtain ⟨c, hc⟩ := exists_forall_detLineChartEquiv_detLineEndGenerator (V := V)
  refine isDetLineCoherentOn_iff.2 fun x _ ↦ isDetLineCoherentWithinAt_iff.2
    ⟨LinearMap.detLineEndGenerator_ne_zero _, S V, inferInstance, G V, inferInstance, q,
      isInvertible (T x), Filter.Eventually.of_forall fun y ↦ ⟨isInvertible (T y), ?_⟩⟩
  rw [hc, hc]

end Coherent

section Transport

variable {T : ℝ → V →L[ℝ] V} {a b : ℝ}

/-- **Orientation transport between endomorphisms follows the normalized generators.** Along a
continuous path of endomorphisms of a real finite-dimensional normed space, transport of
orientations of determinant lines carries the orientation of the normalized generator at `T a` to
that of the normalized generator at `T b`. -/
theorem detLineOrientationTransport_rayOfNeZero_detLineEndGenerator
    (hT : ContinuousOn T (uIcc a b)) (hF : ∀ t ∈ uIcc a b, IsFredholm (T t)) :
    detLineOrientationTransport a b hT hF
        (rayOfNeZero ℝ _ (T a : V →ₗ[ℝ] V).detLineEndGenerator_ne_zero) =
      rayOfNeZero ℝ _ (T b : V →ₗ[ℝ] V).detLineEndGenerator_ne_zero :=
  detLineOrientationTransport_rayOfNeZero hT hF (isDetLineCoherentOn_detLineEndGenerator T _)

/-- The orientation of the determinant line of a bijective `T a` given by invertibility is
transported to the ray of `det (T a) * det (T b)` times the generator of the bijective
trivialization at a bijective `T b`. -/
private theorem detLineOrientationTransport_detLineEquivOfBijective
    (hT : ContinuousOn T (uIcc a b)) (hF : ∀ t ∈ uIcc a b, IsFredholm (T t))
    (ha : Function.Bijective (T a)) (hb : Function.Bijective (T b))
    (hc : (LinearMap.det (T a : V →ₗ[ℝ] V) * LinearMap.det (T b : V →ₗ[ℝ] V)) •
      (LinearMap.detLineEquivOfBijective hb).symm 1 ≠ 0) :
    detLineOrientationTransport a b hT hF
        (rayOfNeZero ℝ _ ((LinearMap.detLineEquivOfBijective ha).symm.map_ne_zero_iff.2
          one_ne_zero)) =
      rayOfNeZero ℝ _ hc := by
  have hda : LinearMap.det (T a : V →ₗ[ℝ] V) ≠ 0 := fun h ↦
    LinearMap.det_eq_zero_iff_ker_ne_bot.1 h (LinearMap.ker_eq_bot.2 ha.1)
  -- Scaling the normalized generators by `det (T a)` gives `det (T a) ^ 2` times the generator
  -- of invertibility at `a`, which has the same ray.
  have hv := (isDetLineCoherentOn_detLineEndGenerator T (uIcc a b)).smul hda
  have key := detLineOrientationTransport_rayOfNeZero hT hF hv
  simp only [LinearMap.detLineEndGenerator_eq_det_smul _ ha,
    LinearMap.detLineEndGenerator_eq_det_smul _ hb, smul_smul] at key
  rwa [(ray_eq_iff _ _).2 (SameRay.sameRay_pos_smul_left _ (mul_self_pos.2 hda))] at key

/-- **Transport preserves the orientations of invertibility when the determinants have the same
sign.** Along a continuous path of endomorphisms of a real finite-dimensional normed space from a
bijective `T a` to a bijective `T b` with `det (T a) * det (T b) > 0`, transport of orientations
carries the orientation of the determinant line of `T a` given by invertibility
(`LinearMap.detLineEquivOfBijective`) to the one of `T b` given by invertibility. -/
theorem detLineOrientationTransport_detLineEquivOfBijective_of_pos
    (hT : ContinuousOn T (uIcc a b)) (hF : ∀ t ∈ uIcc a b, IsFredholm (T t))
    (ha : Function.Bijective (T a)) (hb : Function.Bijective (T b))
    (h : 0 < LinearMap.det (T a : V →ₗ[ℝ] V) * LinearMap.det (T b : V →ₗ[ℝ] V)) :
    detLineOrientationTransport a b hT hF
        (rayOfNeZero ℝ _ ((LinearMap.detLineEquivOfBijective ha).symm.map_ne_zero_iff.2
          one_ne_zero)) =
      rayOfNeZero ℝ _ ((LinearMap.detLineEquivOfBijective hb).symm.map_ne_zero_iff.2
        one_ne_zero) := by
  have hb₀ := (LinearMap.detLineEquivOfBijective hb).symm.map_ne_zero_iff.2 (one_ne_zero (α := ℝ))
  rw [detLineOrientationTransport_detLineEquivOfBijective hT hF ha hb (smul_ne_zero h.ne' hb₀)]
  exact (ray_eq_iff _ _).2 (SameRay.sameRay_pos_smul_left _ h)

/-- **Transport reverses the orientations of invertibility when the determinants have opposite
signs.** Along a continuous path of endomorphisms of a real finite-dimensional normed space from a
bijective `T a` to a bijective `T b` with `det (T a) * det (T b) < 0`, transport of orientations
carries the orientation of the determinant line of `T a` given by invertibility
(`LinearMap.detLineEquivOfBijective`) to the opposite of the one of `T b` given by invertibility.
-/
theorem detLineOrientationTransport_detLineEquivOfBijective_of_neg
    (hT : ContinuousOn T (uIcc a b)) (hF : ∀ t ∈ uIcc a b, IsFredholm (T t))
    (ha : Function.Bijective (T a)) (hb : Function.Bijective (T b))
    (h : LinearMap.det (T a : V →ₗ[ℝ] V) * LinearMap.det (T b : V →ₗ[ℝ] V) < 0) :
    detLineOrientationTransport a b hT hF
        (rayOfNeZero ℝ _ ((LinearMap.detLineEquivOfBijective ha).symm.map_ne_zero_iff.2
          one_ne_zero)) =
      -rayOfNeZero ℝ _ ((LinearMap.detLineEquivOfBijective hb).symm.map_ne_zero_iff.2
        one_ne_zero) := by
  have hb₀ := (LinearMap.detLineEquivOfBijective hb).symm.map_ne_zero_iff.2 (one_ne_zero (α := ℝ))
  rw [detLineOrientationTransport_detLineEquivOfBijective hT hF ha hb (smul_ne_zero h.ne hb₀)]
  -- Negation of orientations of determinant lines is `Module.Ray`'s negation for the additive
  -- group structure of the tensor product (`LinearMap.instNegRayDetLine`).
  let : AddCommGroup (T b : V →ₗ[ℝ] V).detLine := TensorProduct.addCommGroup
  exact ((ray_eq_iff _ (neg_ne_zero.2 hb₀)).2
    ((sameRay_neg_smul_left_iff_of_ne hb₀ h.ne).2 h)).trans (neg_rayOfNeZero ℝ _ hb₀).symm

end Transport

end TauCeti
