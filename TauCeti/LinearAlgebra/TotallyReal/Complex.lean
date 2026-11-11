/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.LinearAlgebra.Complex.FiniteDimensional
public import Mathlib.LinearAlgebra.Complex.Module
public import Mathlib.LinearAlgebra.Determinant
public import TauCeti.LinearAlgebra.Prod
public import TauCeti.LinearAlgebra.TotallyReal.Basic
public import TauCeti.LinearAlgebra.Complex.RealForm
import TauCeti.RingTheory.TensorProduct.IsBaseChange

/-!
# Totally real subspaces of complex modules

This file gives elementary examples of totally real real subspaces of complex modules, among them
the real line `ℝ ⊆ ℂ`, and develops the complex-linear algebra of maximal totally real subspaces.
A real basis of such a subspace is a complex basis of the ambient space. Complex-linear
automorphisms act transitively on these subspaces, and an endomorphism preserving one has real
determinant. An injective real-linear map onto a maximal totally real subspace exhibits the ambient
module as its complexification, and that subspace is exactly the fixed locus of a unique
conjugate-linear involution.

## Main declarations

* `TauCeti.isMaximalTotallyReal_span_one`: the real line `ℝ ⊆ ℂ` is maximal totally real.
* `TauCeti.IsTotallyReal.linearIndependent_complex`: real-linearly independent vectors of a
  totally real subspace are complex-linearly independent.
* `TauCeti.IsMaximalTotallyReal.complexBasis`: a real basis of a maximal totally real subspace,
  as a complex basis of the ambient space.
* `TauCeti.IsMaximalTotallyReal.det_eq_det_restrict`: a complex-linear map preserving a maximal
  totally real subspace has the same (real) determinant as its restriction.
* `TauCeti.IsMaximalTotallyReal.exists_linearEquiv_map_eq`: complex-linear automorphisms act
  transitively on maximal totally real subspaces.
* `TauCeti.IsMaximalTotallyReal.isMaximalTotallyReal_prod`: a direct sum of maximal totally real
  subspaces is maximal totally real in the product of the ambient complex modules.
* `LinearMap.isBaseChange_complex_of_isMaximalTotallyReal`: an injective real-linear map onto a
  maximal totally real subspace is a complexification.
* `LinearMap.conjugationOfMaximalTotallyReal`: the conjugate-linear involution whose fixed locus
  is exactly that subspace, with `LinearMap.conjugationOfMaximalTotallyReal_apply_self`,
  `LinearMap.conjugationOfMaximalTotallyReal_eq_self_iff`,
  `LinearMap.conjugationOfMaximalTotallyReal_unique`,
  `LinearMap.conjugationOfMaximalTotallyReal_congr_range` and
  `LinearMap.conjugationOfMaximalTotallyReal_natural`.
* `TauCeti.IsMaximalTotallyReal.projection_sum_smul`: the projection onto a maximal totally real
  subspace along its `i`-image takes real parts of complex coordinates in a real frame.
-/

public section

namespace TauCeti

open Module

variable {ι : Type*}

/-- **The real span of vectors, one in each coordinate, is totally real.** The image of the
real-linear map `τ ↦ (τ i • v i)ᵢ` from `ι → ℝ` to `ι → ℂ` meets its image under multiplication by
`i` only in `0`. -/
theorem isTotallyReal_range_pi_smulRight {v : ι → ℂ} :
    IsTotallyReal ((LinearMap.lsmul ℂ (ι → ℂ) Complex.I).restrictScalars ℝ)
      (LinearMap.range (LinearMap.pi fun i => (LinearMap.proj i : (ι → ℝ) →ₗ[ℝ] ℝ).smulRight
        (v i))) := by
  rw [isTotallyReal_iff, Submodule.disjoint_def]
  rintro _ ⟨τ, rfl⟩ ⟨_, ⟨σ, rfl⟩, hσ⟩
  funext i
  have h := congrFun hσ i
  simp only [LinearMap.restrictScalars_apply, LinearMap.lsmul_apply, LinearMap.pi_apply,
    LinearMap.smulRight_apply, LinearMap.proj_apply, Pi.smul_apply, Complex.real_smul,
    smul_eq_mul] at h ⊢
  by_cases hi : v i = 0
  · simp [hi]
  · have h' : (σ i : ℂ) * Complex.I = τ i := mul_right_cancel₀ hi (by rw [← h]; ring)
    have hτ : τ i = 0 := by simpa using (congrArg Complex.re h').symm
    simp [hτ]

/-- The real line `ℝ ⊆ ℂ`, the real span of `1`, is a maximal totally real subspace of `ℂ`: every
complex number is uniquely `a + i b` with `a, b` real. -/
theorem isMaximalTotallyReal_span_one :
    IsMaximalTotallyReal ((LinearMap.lsmul ℂ ℂ Complex.I).restrictScalars ℝ)
      (Submodule.span ℝ {(1 : ℂ)}) := by
  have hmap : (Submodule.span ℝ {(1 : ℂ)}).map
      ((LinearMap.lsmul ℂ ℂ Complex.I).restrictScalars ℝ) = Submodule.span ℝ {Complex.I} := by
    rw [Submodule.map_span, Set.image_singleton]
    simp
  rw [isMaximalTotallyReal_iff, hmap]
  constructor
  · rw [Submodule.disjoint_def]
    intro z hz hz'
    obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.1 hz
    obtain ⟨b, hb⟩ := Submodule.mem_span_singleton.1 hz'
    have := congrArg Complex.re hb
    simp only [Complex.real_smul, Complex.mul_re, Complex.ofReal_re, Complex.I_re, mul_zero,
      Complex.ofReal_im, Complex.I_im, mul_one, sub_self] at this
    simp [← this]
  · rw [codisjoint_iff, eq_top_iff]
    intro z _
    refine Submodule.mem_sup.2 ⟨z.re • 1,
      Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _),
      z.im • Complex.I, Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _), ?_⟩
    apply Complex.ext <;> simp

variable {E : Type*} [AddCommGroup E] [Module ℝ E] [Module ℂ E] [IsScalarTower ℝ ℂ E]
  {L : Submodule ℝ E}

/-- Vectors of a totally real subspace of a complex module that are linearly independent over `ℝ`
are linearly independent over `ℂ`. -/
theorem IsTotallyReal.linearIndependent_complex
    (hL : IsTotallyReal ((LinearMap.lsmul ℂ E Complex.I).restrictScalars ℝ) L) {ι : Type*}
    {v : ι → E} (hv : LinearIndependent ℝ v) (hvL : ∀ i, v i ∈ L) : LinearIndependent ℂ v := by
  classical
  rw [linearIndependent_iff'] at hv ⊢
  intro s g hsum i hi
  -- Split `∑ gⱼ vⱼ` into `a + i b` with `a, b ∈ L`; total reality forces `a = b = 0`.
  set a : E := ∑ j ∈ s, (g j).re • v j
  set b : E := ∑ j ∈ s, (g j).im • v j
  have hsplit : ∑ j ∈ s, g j • v j = a + Complex.I • b := by
    simp only [a, b, Finset.smul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [RCLike.real_smul_eq_coe_smul (K := ℂ), RCLike.real_smul_eq_coe_smul (K := ℂ), smul_smul,
      ← add_smul, mul_comm]
    simp
  have hb : b ∈ L := L.sum_mem fun j _ => L.smul_mem _ (hvL j)
  have hab : a = -(Complex.I • b) := eq_neg_of_add_eq_zero_left (hsplit ▸ hsum)
  have ha0 : a = 0 := by
    refine Submodule.disjoint_def.1 hL.disjoint a (L.sum_mem fun j _ => L.smul_mem _ (hvL j)) ?_
    rw [hab]
    exact Submodule.neg_mem _ ⟨b, hb, rfl⟩
  have hb0 : b = 0 := by
    rw [ha0, zero_eq_neg, smul_eq_zero] at hab
    exact hab.resolve_left Complex.I_ne_zero
  exact Complex.ext (hv s _ ha0 i hi) (hv s _ hb0 i hi)

/-- An injective real-linear map onto a maximal totally real subspace exhibits the ambient
complex module as its complexification. Both real scalar structures are the given compatible
ones; finite-dimensionality and a choice of basis are unnecessary. -/
theorem _root_.LinearMap.isBaseChange_complex_of_isMaximalTotallyReal
    {W : Type*} [AddCommGroup W] [Module ℝ W] (f : W →ₗ[ℝ] E)
    (hf : Function.Injective f)
    (hmax : IsMaximalTotallyReal ((LinearMap.lsmul ℂ E Complex.I).restrictScalars ℝ) f.range) :
    IsBaseChange ℂ f := by
  rw [IsBaseChange.iff_liftBaseChange_bijective]
  constructor
  · rw [f.liftBaseChange_complex_injective_iff]
    intro x y hxy
    have hxJ : f x ∈ f.range.map ((LinearMap.lsmul ℂ E Complex.I).restrictScalars ℝ) := by
      refine ⟨f (-y), ⟨-y, rfl⟩, ?_⟩
      simp only [map_neg, LinearMap.restrictScalars_apply, LinearMap.lsmul_apply]
      exact (eq_neg_of_add_eq_zero_left hxy).symm
    have hx : f x = 0 := Submodule.disjoint_def.mp hmax.disjoint (f x) ⟨x, rfl⟩ hxJ
    have hy : f y = 0 := (smul_eq_zero.mp (by simpa only [hx, zero_add] using hxy)).resolve_left
      Complex.I_ne_zero
    exact ⟨hf (by simpa using hx), hf (by simpa using hy)⟩
  · intro v
    have hv : v ∈ f.range ⊔ f.range.map ((LinearMap.lsmul ℂ E Complex.I).restrictScalars ℝ) := by
      rw [hmax.sup_eq_top]
      exact Submodule.mem_top
    obtain ⟨a, ⟨x, rfl⟩, b, ⟨u, ⟨y, rfl⟩, rfl⟩, hxy⟩ := Submodule.mem_sup.mp hv
    exact LinearMap.mem_range.mp (f.mem_range_liftBaseChange_complex_iff.mpr ⟨x, y, hxy⟩)

/-- The canonical conjugation whose real form is the image of the given maximal totally real
inclusion. It transports the existing tensor conjugation through the canonical base-change map. -/
noncomputable def _root_.LinearMap.conjugationOfMaximalTotallyReal
    {W : Type*} [AddCommGroup W] [Module ℝ W] (f : W →ₗ[ℝ] E)
    (hf : Function.Injective f)
    (hmax : IsMaximalTotallyReal ((LinearMap.lsmul ℂ E Complex.I).restrictScalars ℝ) f.range) :
    E →ₛₗ[starRingEnd ℂ] E :=
  (f.isBaseChange_complex_of_isMaximalTotallyReal hf hmax).equiv.conjugationOfComplexification

/-- The defining transport formula through the canonical complexification map. -/
theorem _root_.LinearMap.conjugationOfMaximalTotallyReal_apply
    {W : Type*} [AddCommGroup W] [Module ℝ W] (f : W →ₗ[ℝ] E)
    (hf : Function.Injective f)
    (hmax : IsMaximalTotallyReal ((LinearMap.lsmul ℂ E Complex.I).restrictScalars ℝ) f.range)
    (v : E) :
    f.conjugationOfMaximalTotallyReal hf hmax v =
      (f.isBaseChange_complex_of_isMaximalTotallyReal hf hmax).equiv
        (tmulConj W ((f.isBaseChange_complex_of_isMaximalTotallyReal hf hmax).equiv.symm v)) := by
  rw [LinearMap.conjugationOfMaximalTotallyReal, LinearEquiv.conjugationOfComplexification_apply]

/-- Applying the conjugation of a maximal real form twice gives back the input. -/
@[simp]
theorem _root_.LinearMap.conjugationOfMaximalTotallyReal_conjugationOfMaximalTotallyReal
    {W : Type*} [AddCommGroup W] [Module ℝ W] (f : W →ₗ[ℝ] E)
    (hf : Function.Injective f)
    (hmax : IsMaximalTotallyReal ((LinearMap.lsmul ℂ E Complex.I).restrictScalars ℝ) f.range)
    (v : E) :
    f.conjugationOfMaximalTotallyReal hf hmax
      (f.conjugationOfMaximalTotallyReal hf hmax v) = v := by
  rw [LinearMap.conjugationOfMaximalTotallyReal,
    LinearEquiv.conjugationOfComplexification_conjugationOfComplexification]

/-- Conjugation of a maximal real form is involutive. -/
theorem _root_.LinearMap.conjugationOfMaximalTotallyReal_involutive
    {W : Type*} [AddCommGroup W] [Module ℝ W] (f : W →ₗ[ℝ] E)
    (hf : Function.Injective f)
    (hmax : IsMaximalTotallyReal ((LinearMap.lsmul ℂ E Complex.I).restrictScalars ℝ) f.range) :
    Function.Involutive (f.conjugationOfMaximalTotallyReal hf hmax) :=
  f.conjugationOfMaximalTotallyReal_conjugationOfMaximalTotallyReal hf hmax

/-- The fixed vectors are exactly the image of the given real inclusion. -/
@[simp]
theorem _root_.LinearMap.conjugationOfMaximalTotallyReal_eq_self_iff
    {W : Type*} [AddCommGroup W] [Module ℝ W] (f : W →ₗ[ℝ] E)
    (hf : Function.Injective f)
    (hmax : IsMaximalTotallyReal ((LinearMap.lsmul ℂ E Complex.I).restrictScalars ℝ) f.range)
    (v : E) : f.conjugationOfMaximalTotallyReal hf hmax v = v ↔ v ∈ f.range := by
  rw [LinearMap.conjugationOfMaximalTotallyReal,
    LinearEquiv.conjugationOfComplexification_eq_self_iff]
  simp only [IsBaseChange.equiv_tmul, one_smul, LinearMap.mem_range]

/-- The conjugation fixes every vector of the given real inclusion. -/
@[simp]
theorem _root_.LinearMap.conjugationOfMaximalTotallyReal_apply_self
    {W : Type*} [AddCommGroup W] [Module ℝ W] (f : W →ₗ[ℝ] E)
    (hf : Function.Injective f)
    (hmax : IsMaximalTotallyReal ((LinearMap.lsmul ℂ E Complex.I).restrictScalars ℝ) f.range)
    (w : W) : f.conjugationOfMaximalTotallyReal hf hmax (f w) = f w :=
  (f.conjugationOfMaximalTotallyReal_eq_self_iff hf hmax (f w)).mpr ⟨w, rfl⟩

/-- Any conjugate-linear map fixing the given real inclusion is this conjugation. In particular
the construction is independent of frames or auxiliary complexification presentations. -/
theorem _root_.LinearMap.conjugationOfMaximalTotallyReal_unique
    {W : Type*} [AddCommGroup W] [Module ℝ W] (f : W →ₗ[ℝ] E)
    (hf : Function.Injective f)
    (hmax : IsMaximalTotallyReal ((LinearMap.lsmul ℂ E Complex.I).restrictScalars ℝ) f.range)
    (K : E →ₛₗ[starRingEnd ℂ] E) (hfix : ∀ w, K (f w) = f w) :
    K = f.conjugationOfMaximalTotallyReal hf hmax := by
  unfold LinearMap.conjugationOfMaximalTotallyReal
  apply LinearEquiv.conjugationOfComplexification_unique
  intro w
  simpa only [IsBaseChange.equiv_tmul, one_smul] using hfix w

/-- The conjugation depends only on the real range, even when two inclusions have different
source carriers. This is the independence of the presentation of the maximal real form. -/
theorem _root_.LinearMap.conjugationOfMaximalTotallyReal_congr_range
    {W W' : Type*} [AddCommGroup W] [Module ℝ W] [AddCommGroup W'] [Module ℝ W']
    (f : W →ₗ[ℝ] E) (hf : Function.Injective f)
    (hmax : IsMaximalTotallyReal ((LinearMap.lsmul ℂ E Complex.I).restrictScalars ℝ) f.range)
    (g : W' →ₗ[ℝ] E) (hg : Function.Injective g)
    (hmax' : IsMaximalTotallyReal ((LinearMap.lsmul ℂ E Complex.I).restrictScalars ℝ) g.range)
    (hrange : f.range = g.range) :
    f.conjugationOfMaximalTotallyReal hf hmax = g.conjugationOfMaximalTotallyReal hg hmax' := by
  apply g.conjugationOfMaximalTotallyReal_unique hg hmax'
  intro w
  apply (f.conjugationOfMaximalTotallyReal_eq_self_iff hf hmax (g w)).mpr
  rw [hrange]
  exact ⟨w, rfl⟩

/-- A complex-linear map carrying one maximal real form to another intertwines their canonical
conjugations. Neither map is required to be invertible. -/
theorem _root_.LinearMap.conjugationOfMaximalTotallyReal_natural
    {W W' E' : Type*} [AddCommGroup W] [Module ℝ W] [AddCommGroup W'] [Module ℝ W']
    [AddCommGroup E'] [Module ℝ E'] [Module ℂ E'] [IsScalarTower ℝ ℂ E']
    (f : W →ₗ[ℝ] E) (hf : Function.Injective f)
    (hmax : IsMaximalTotallyReal ((LinearMap.lsmul ℂ E Complex.I).restrictScalars ℝ) f.range)
    (g : W' →ₗ[ℝ] E') (hg : Function.Injective g)
    (hmax' : IsMaximalTotallyReal ((LinearMap.lsmul ℂ E' Complex.I).restrictScalars ℝ) g.range)
    (A : E →ₗ[ℂ] E') (b : W →ₗ[ℝ] W') (hreal : ∀ w, A (f w) = g (b w)) (v : E) :
    g.conjugationOfMaximalTotallyReal hg hmax' (A v) =
      A (f.conjugationOfMaximalTotallyReal hf hmax v) := by
  unfold LinearMap.conjugationOfMaximalTotallyReal
  apply LinearEquiv.conjugationOfComplexification_natural _ _ A b
  intro w
  simpa only [IsBaseChange.equiv_tmul, one_smul] using hreal w

namespace IsMaximalTotallyReal

variable (hL : IsMaximalTotallyReal ((LinearMap.lsmul ℂ E Complex.I).restrictScalars ℝ) L)
include hL

/-- Vectors spanning a maximal totally real subspace over `ℝ` span the ambient complex module over
`ℂ`. -/
theorem span_complex_eq_top {ι : Type*} {v : ι → E} (hv : Submodule.span ℝ (Set.range v) = L) :
    Submodule.span ℂ (Set.range v) = ⊤ := by
  have hle : L ≤ (Submodule.span ℂ (Set.range v)).restrictScalars ℝ :=
    hv ▸ Submodule.span_le_restrictScalars ℝ ℂ _
  have hJle : L.map ((LinearMap.lsmul ℂ E Complex.I).restrictScalars ℝ) ≤
      (Submodule.span ℂ (Set.range v)).restrictScalars ℝ := by
    rintro _ ⟨x, hx, rfl⟩
    exact Submodule.smul_mem _ Complex.I (hle hx)
  rw [← Submodule.restrictScalars_eq_top_iff ℝ, eq_top_iff, ← hL.sup_eq_top]
  exact sup_le hle hJle

/-- A real basis of a maximal totally real subspace `L` of a complex module `E` is a complex basis
of `E`: `L` is a real form of `E`. -/
noncomputable def complexBasis {ι : Type*} (b : Basis ι ℝ L) : Basis ι ℂ E :=
  Basis.mk (v := L.subtype ∘ b)
    (hL.isTotallyReal.linearIndependent_complex
      (b.linearIndependent.map' L.subtype L.ker_subtype) fun i => (b i).2)
    (hL.span_complex_eq_top (by
      rw [Set.range_comp, Submodule.span_image, b.span_eq, Submodule.map_subtype_top])).ge

@[simp]
theorem complexBasis_apply {ι : Type*} (b : Basis ι ℝ L) (i : ι) :
    hL.complexBasis b i = b i :=
  Basis.mk_apply _ _ _

/-- The complex coordinates of a vector of `L` in `complexBasis b` are its real coordinates in
`b`. -/
@[simp]
theorem complexBasis_repr_coe {ι : Type*} (b : Basis ι ℝ L) (x : L) (i : ι) :
    (hL.complexBasis b).repr x i = b.repr x i := by
  have h : ((hL.complexBasis b).repr.toLinearMap.restrictScalars ℝ).comp L.subtype =
      (Finsupp.mapRange.linearMap Complex.ofRealAm.toLinearMap).comp b.repr.toLinearMap :=
    b.ext fun j => by
      have hj := (hL.complexBasis b).repr_self j
      rw [complexBasis_apply] at hj
      simp [hj]
  simpa using DFunLike.congr_fun (LinearMap.congr_fun h x) i

/-- A complex-linear automorphism maps maximal totally real subspaces to maximal totally real
subspaces. -/
theorem map_linearEquiv (A : E ≃ₗ[ℂ] E) :
    IsMaximalTotallyReal ((LinearMap.lsmul ℂ E Complex.I).restrictScalars ℝ)
      (L.map ((A : E →ₗ[ℂ] E).restrictScalars ℝ)) := by
  have hcomm : ((LinearMap.lsmul ℂ E Complex.I).restrictScalars ℝ).comp
      ((A : E →ₗ[ℂ] E).restrictScalars ℝ) =
        ((A : E →ₗ[ℂ] E).restrictScalars ℝ).comp
          ((LinearMap.lsmul ℂ E Complex.I).restrictScalars ℝ) :=
    LinearMap.ext fun x => (A.map_smul Complex.I x).symm
  rw [isMaximalTotallyReal_iff, ← Submodule.map_comp, hcomm, Submodule.map_comp]
  exact Submodule.isCompl_map (A.restrictScalars ℝ) hL.isCompl

/-- A maximal totally real subspace has real dimension equal to the complex dimension of the
ambient module. -/
theorem finrank_eq_finrank_complex : finrank ℝ L = finrank ℂ E := by
  rw [finrank_eq_nat_card_basis (Module.Free.chooseBasis ℝ L),
    finrank_eq_nat_card_basis (hL.complexBasis (Module.Free.chooseBasis ℝ L))]

/-- A complex-linear endomorphism `f` preserving a maximal totally real subspace `L` is the
complexification of its restriction to `L`, so its determinant is the (real) determinant of that
restriction. -/
theorem det_eq_det_restrict (f : E →ₗ[ℂ] E) (hf : ∀ x ∈ L, f x ∈ L) :
    LinearMap.det f = ((LinearMap.det ((f.restrictScalars ℝ).restrict hf) : ℝ) : ℂ) := by
  classical
  let b := Module.Free.chooseBasis ℝ L
  by_cases hfin : Finite (Module.Free.ChooseBasisIndex ℝ L)
  · have := Fintype.ofFinite (Module.Free.ChooseBasisIndex ℝ L)
    rw [← LinearMap.det_toMatrix (hL.complexBasis b), ← LinearMap.det_toMatrix b]
    refine ((Complex.ofRealHom.map_det _).trans (congrArg Matrix.det ?_)).symm
    ext i j
    rw [RingHom.mapMatrix_apply, Matrix.map_apply, LinearMap.toMatrix_apply,
      LinearMap.toMatrix_apply, complexBasis_apply]
    exact (hL.complexBasis_repr_coe b ((f.restrictScalars ℝ).restrict hf (b j)) i).symm
  · have h1 : ¬ Module.Finite ℝ L := fun h => hfin (Module.Finite.finite_basis b)
    have h2 : ¬ Module.Finite ℂ E := fun h => hfin (Module.Finite.finite_basis (hL.complexBasis b))
    rw [LinearMap.det_eq_one_of_not_module_finite h2,
      LinearMap.det_eq_one_of_not_module_finite h1, Complex.ofReal_one]

variable [FiniteDimensional ℂ E]

/-- The complex-linear automorphisms act transitively on the maximal totally real subspaces of a
finite-dimensional complex module. -/
theorem exists_linearEquiv_map_eq {L' : Submodule ℝ E}
    (hL' : IsMaximalTotallyReal ((LinearMap.lsmul ℂ E Complex.I).restrictScalars ℝ) L') :
    ∃ A : E ≃ₗ[ℂ] E, L.map ((A : E →ₗ[ℂ] E).restrictScalars ℝ) = L' := by
  have : FiniteDimensional ℝ E := Module.Finite.trans ℂ E
  have hspan {K : Submodule ℝ E} (c : Basis (Fin (finrank ℂ E)) ℝ K) :
      Submodule.span ℝ (Set.range (K.subtype ∘ c)) = K := by
    rw [Set.range_comp, Submodule.span_image, c.span_eq, Submodule.map_subtype_top]
  let b := Module.finBasisOfFinrankEq ℝ L hL.finrank_eq_finrank_complex
  let b' := Module.finBasisOfFinrankEq ℝ L' hL'.finrank_eq_finrank_complex
  obtain ⟨A, hA⟩ : ∃ A : E ≃ₗ[ℂ] E, ∀ i, A (b i) = b' i :=
    ⟨(hL.complexBasis b).equiv (hL'.complexBasis b') (Equiv.refl _), fun i => by
      simpa using (hL.complexBasis b).equiv_apply i (hL'.complexBasis b') (Equiv.refl _)⟩
  refine ⟨A, ?_⟩
  rw [← hspan b, Submodule.map_span, ← Set.range_comp, ← hspan b']
  congr 2
  funext i
  exact hA i

end IsMaximalTotallyReal

namespace IsMaximalTotallyReal

variable {E' : Type*} [AddCommGroup E'] [Module ℝ E'] [Module ℂ E'] [IsScalarTower ℝ ℂ E']
  {M : Submodule ℝ E'}

/-- **A direct sum of maximal totally real subspaces is maximal totally real.** The coordinate
submodule `L.prod M` of a product of complex modules is maximal totally real for multiplication by
`i` whenever the two summands are. -/
theorem isMaximalTotallyReal_prod
    (hL : IsMaximalTotallyReal ((LinearMap.lsmul ℂ E Complex.I).restrictScalars ℝ) L)
    (hM : IsMaximalTotallyReal ((LinearMap.lsmul ℂ E' Complex.I).restrictScalars ℝ) M) :
    IsMaximalTotallyReal ((LinearMap.lsmul ℂ (E × E') Complex.I).restrictScalars ℝ) (L.prod M) := by
  rw [LinearMap.lsmul_restrictScalars_prodMap Complex.I]
  exact hL.prod hM

end IsMaximalTotallyReal

variable (E) in
/-- Multiplication by `i` on a complex module squares to `-1`. -/
theorem lsmul_I_comp_lsmul_I :
    (LinearMap.lsmul ℂ E Complex.I).restrictScalars ℝ ∘ₗ
        (LinearMap.lsmul ℂ E Complex.I).restrictScalars ℝ = -LinearMap.id := by
  ext v
  simp [smul_smul]

/-- The projection onto a maximal totally real subspace along its `i`-image takes the real part
of complex coordinates in a real frame of the subspace. -/
theorem IsMaximalTotallyReal.projection_sum_smul {ι : Type*} [Fintype ι]
    (hL : IsMaximalTotallyReal ((LinearMap.lsmul ℂ E Complex.I).restrictScalars ℝ) L)
    {v : ι → E} (hv : ∀ i, v i ∈ L) (c : ι → ℂ) :
    L.projection _ hL.isCompl (∑ i, c i • v i) = ∑ i, (c i).re • v i := by
  have hsplit : ∑ i, c i • v i = ∑ i, (c i).re • v i +
      (LinearMap.lsmul ℂ E Complex.I).restrictScalars ℝ (∑ i, (c i).im • v i) := by
    simp only [map_sum, map_smul, LinearMap.restrictScalars_apply, LinearMap.lsmul_apply,
      ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    have hr (r : ℝ) (y : E) : (r : ℂ) • y = r • y := by
      rw [← smul_one_smul ℂ r y, Complex.real_smul, mul_one]
    conv_lhs => rw [← Complex.re_add_im (c i)]
    rw [add_smul, mul_smul, hr, hr]
  rw [hsplit, map_add,
    Submodule.projection_apply_of_mem_right hL.isCompl
      ⟨_, L.sum_mem fun i _ ↦ L.smul_mem _ (hv i), rfl⟩, add_zero,
    Submodule.projection_apply_of_mem_left hL.isCompl (L.sum_mem fun i _ ↦ L.smul_mem _ (hv i))]

end TauCeti
