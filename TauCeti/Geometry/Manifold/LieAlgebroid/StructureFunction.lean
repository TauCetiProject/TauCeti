/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.LieAlgebroid.Restrict
public import TauCeti.Geometry.Manifold.VectorBundle.Section.LocalFrameCoeff
public import TauCeti.Geometry.Manifold.VectorField.Derivation
import TauCeti.Geometry.Manifold.VectorBundle.LocalFrame
import TauCeti.Geometry.Manifold.VectorBundle.Scalar
import TauCeti.Geometry.Manifold.VectorField.LieBracket

/-!
# Structure functions and local-frame equations of a Lie algebroid

Over `U : Opens M` in `e.baseSet` for a trivialization `e` of a finite-rank smooth real vector
bundle `V → M` and basis `b : Basis ι ℝ F`, restricting `A` to `U` expresses its anchor and bracket
via `A.anchorFrameField` and `A.structureFunction` (`bracket_eq_sum_openLocalFrame`,
`restrict_bracket_eq_sum_structureFunction`), satisfying skew-symmetry,
`mlieBracket_anchorFrameField`, `jacobi_structureFunction`, and coordinate-change laws
(`anchorFrameField_coordChange`, `structureFunction_coordChange`, `localFrameTransition`;
Mackenzie 2005, §3.3).
-/

public noncomputable section

open Bundle Manifold Module TopologicalSpace VectorField
open scoped ContDiff Topology

namespace TauCeti.LieAlgebroid

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {V : M → Type*}
  [TopologicalSpace (TotalSpace F V)] [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)]
  [∀ x, TopologicalSpace (V x)] [FiberBundle F V] [VectorBundle ℝ F V]

local notation "V|[" U "]" => ((ContinuousMap.mk Subtype.val continuous_subtype_val : C(U, M)) *ᵖ V)
local notation "τOpen" => Manifold.tangentSpaceOpenEquiv (I := I)

section StructureFunctions

variable [IsManifold I ∞ M] [FiniteDimensional ℝ E] [T2Space M] [ContMDiffVectorBundle ∞ F V I]
  (A : LieAlgebroid I F V) (e : Trivialization F (π F V)) [MemTrivializationAtlas e]
  {ι : Type*} (b : Basis ι ℝ F) {U : Opens M} (hU : (U : Set M) ⊆ e.baseSet)

local notation "frSection" => e.openLocalFrameSection I ∞ b hU

/-- The `i`-th anchor vector field of `A` on `U ⊆ e.baseSet`. -/
def anchorFrameField (i : ι) : Cₛ^∞⟮I; E, (TangentSpace I : U → Type _)⟯ :=
  (A.restrict U).anchorField (frSection i)

theorem anchorFrameField_eq (i : ι) :
    A.anchorFrameField e b hU i = (A.restrict U).anchorField (frSection i) := (rfl)

@[simp] theorem anchorFrameField_apply (i : ι) (x : U) :
    A.anchorFrameField e b hU i x =
      (τOpen x).symm (A.anchor (x : M) (e.localFrame b i (x : M))) := by
  rw [anchorFrameField, anchorField_apply, restrict_anchor_apply]
  exact congrArg (fun v ↦ (τOpen x).symm (A.anchor (x : M) v))
    (e.openLocalFrameSection_apply (I := I) (n := ∞) b hU i x)

theorem tangentSpaceOpenEquiv_anchorFrameField_apply (i : ι) (x : U) :
    τOpen x (A.anchorFrameField e b hU i x) = A.anchor (x : M) (e.localFrame b i (x : M)) := by
  rw [anchorFrameField_apply, ContinuousLinearEquiv.apply_symm_apply]

@[simp] theorem vectorFieldDerivation_anchorFrameField (i : ι) (f : C^∞⟮I, U; ℝ⟯) :
    vectorFieldDerivation (A.anchorFrameField e b hU i) f =
      (A.restrict U).anchorDeriv (frSection i) f := by
  ext x; rw [ContMDiffSection.vectorFieldDerivation_apply_apply, anchorFrameField,
    anchorField_apply, anchorDeriv_apply]

variable [FiniteDimensional ℝ F]

local notation "frCoeff" => e.openLocalFrameCoeff I ∞ b hU

/-- The smooth structure functions `c_{ij}^k` of `A` on `U ⊆ e.baseSet` in the frame `(e, b)`. -/
def structureFunction (i j k : ι) : C^∞⟮I, U; ℝ⟯ :=
  frCoeff k ((A.restrict U).bracket (frSection i) (frSection j))

theorem structureFunction_eq (i j k : ι) : A.structureFunction e b hU i j k =
    frCoeff k ((A.restrict U).bracket (frSection i) (frSection j)) := (rfl)

theorem bracket_openLocalFrameSection [Fintype ι] (i j : ι) :
    (A.restrict U).bracket (frSection i) (frSection j) =
      ∑ k, A.structureFunction e b hU i j k • frSection k :=
  e.eq_sum_openLocalFrameCoeff_smul b hU _

@[simp] theorem structureFunction_self (i k : ι) : A.structureFunction e b hU i i k = 0 := by
  rw [structureFunction, (A.restrict U).bracket_self, map_zero]

theorem structureFunction_swap (i j k : ι) :
    A.structureFunction e b hU i j k = -A.structureFunction e b hU j i k := by
  rw [structureFunction, (A.restrict U).bracket_swap, map_neg, structureFunction]

theorem anchorField_restrict_eq_sum_anchorFrameField [Fintype ι] (s : Cₛ^∞⟮I; F, V|[U]⟯) :
    (A.restrict U).anchorField s = ∑ i, frCoeff i s • A.anchorFrameField e b hU i := by
  conv_lhs => rw [e.eq_sum_openLocalFrameCoeff_smul b hU s]
  rw [map_sum]; exact Finset.sum_congr rfl fun i _ ↦ (A.restrict U).anchorField.map_smul _ _

omit [FiniteDimensional ℝ E] [T2Space M] in
private theorem anchorDeriv_open_eq_sum [Fintype ι] (B : LieAlgebroid I F V|[U])
    (s : Cₛ^∞⟮I; F, V|[U]⟯) (f : C^∞⟮I, U; ℝ⟯) :
    B.anchorDeriv s f = ∑ i, frCoeff i s * B.anchorDeriv (frSection i) f := by
  have : ContMDiffVectorBundle ∞ F V|[U] I := ContMDiffVectorBundle.restrictOpen U
  ext x
  have hsum := congrFun (map_sum (ContMDiffSection.coeAddHom I F ∞ V|[U])
    (fun i ↦ frCoeff i s • frSection i) Finset.univ) x
  simp only [ContMDiffSection.coeAddHom_apply, Finset.sum_apply,
    ContMDiffSection.smul_apply] at hsum
  rw [anchorDeriv_apply, (congrArg (· x) (e.eq_sum_openLocalFrameCoeff_smul b hU s)).trans hsum,
    map_sum, map_sum, ContMDiffMap.coe_sum, Finset.sum_apply]
  exact Finset.sum_congr rfl fun _ _ ↦ by
    rw [map_smul, map_smul, smul_eq_mul, ContMDiffMap.coe_mul, Pi.mul_apply, anchorDeriv_apply]

theorem anchorDeriv_restrict_eq_sum_anchorFrameField [Fintype ι] (s : Cₛ^∞⟮I; F, V|[U]⟯)
    (f : C^∞⟮I, U; ℝ⟯) : (A.restrict U).anchorDeriv s f =
      ∑ i, frCoeff i s * vectorFieldDerivation (A.anchorFrameField e b hU i) f := by
  simp_rw [anchorDeriv_open_eq_sum e b hU (A.restrict U) s f,
    vectorFieldDerivation_anchorFrameField]

omit [FiniteDimensional ℝ E] [T2Space M] in
/-- Over `U ⊆ e.baseSet`, the Lie bracket of any Lie algebroid on `V|_U` expands in the frame. -/
theorem bracket_eq_sum_openLocalFrame [Fintype ι] (B : LieAlgebroid I F V|[U])
    (s t : Cₛ^∞⟮I; F, V|[U]⟯) :
    B.bracket s t = ∑ k, (B.anchorDeriv s (frCoeff k t) - B.anchorDeriv t (frCoeff k s) +
      ∑ i, ∑ j, frCoeff i s * frCoeff j t *
        frCoeff k (B.bracket (frSection i) (frSection j))) • frSection k := by
  have : ContMDiffVectorBundle ∞ F V|[U] I := ContMDiffVectorBundle.restrictOpen U
  let c := fun i j k ↦ frCoeff k (B.bracket (frSection i) (frSection j))
  have ht : B.bracket s t = ∑ k, frCoeff k t • B.bracket s (frSection k) +
      ∑ k, B.anchorDeriv s (frCoeff k t) • frSection k := by
    conv_lhs => rw [e.eq_sum_openLocalFrameCoeff_smul b hU t]
    simp only [map_sum, B.bracket_smul_right, Finset.sum_add_distrib]
  have hs (j : ι) : frCoeff j t • B.bracket s (frSection j) =
      (∑ i, ∑ k, (frCoeff i s * frCoeff j t * c i j k) • frSection k) -
        ∑ i, (frCoeff j t * B.anchorDeriv (frSection j) (frCoeff i s)) • frSection i := by
    conv_lhs => rw [e.eq_sum_openLocalFrameCoeff_smul b hU s]
    rw [LinearMap.map_sum₂, Finset.smul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    have hc : B.bracket (frSection i) (frSection j) = ∑ k, c i j k • frSection k :=
      e.eq_sum_openLocalFrameCoeff_smul b hU _
    rw [B.bracket_smul_left, smul_sub, mul_smul, hc, Finset.smul_sum, Finset.smul_sum]
    exact congrArg (· - _) (Finset.sum_congr rfl fun k _ ↦ by
      rw [← mul_smul, ← mul_smul]; exact congrArg (· • frSection k) (by ring))
  have hsub : ∑ j, ∑ i, (frCoeff j t * B.anchorDeriv (frSection j) (frCoeff i s)) • frSection i =
      ∑ k, B.anchorDeriv t (frCoeff k s) • frSection k := by
    rw [Finset.sum_comm]; exact Finset.sum_congr rfl fun k _ ↦ by
      rw [← Finset.sum_smul, anchorDeriv_open_eq_sum e b hU B t (frCoeff k s)]
  have htriple : ∑ j, ∑ i, ∑ k, (frCoeff i s * frCoeff j t * c i j k) • frSection k =
      ∑ k, (∑ i, ∑ j, frCoeff i s * frCoeff j t * c i j k) • frSection k := by
    rw [Finset.sum_comm]
    refine (Finset.sum_congr rfl fun _ _ ↦ Finset.sum_comm).trans (Finset.sum_comm.trans ?_)
    exact Finset.sum_congr rfl fun _ _ ↦ by
      rw [Finset.sum_smul]; exact Finset.sum_congr rfl fun _ _ ↦ Finset.sum_smul.symm
  rw [ht, Finset.sum_congr rfl fun j _ ↦ hs j, Finset.sum_sub_distrib, hsub, htriple]
  simp_rw [add_smul, sub_smul]; rw [Finset.sum_add_distrib, Finset.sum_sub_distrib]; abel

/-- **Local-frame formula for the Lie bracket** in terms of `structureFunction`. -/
theorem restrict_bracket_eq_sum_structureFunction [Fintype ι] (s t : Cₛ^∞⟮I; F, V|[U]⟯) :
    (A.restrict U).bracket s t =
      ∑ k, ((A.restrict U).anchorDeriv s (frCoeff k t) -
        (A.restrict U).anchorDeriv t (frCoeff k s) +
        ∑ i, ∑ j, frCoeff i s * frCoeff j t * A.structureFunction e b hU i j k) • frSection k :=
  bracket_eq_sum_openLocalFrame e b hU (A.restrict U) s t

/-- **Anchor-bracket structure equation:** `[ρ_i, ρ_j] = ∑ k, c_{ij}^k • ρ_k`. -/
theorem mlieBracket_anchorFrameField [Fintype ι] (i j : ι) (x : U) :
    mlieBracket I (A.anchorFrameField e b hU i) (A.anchorFrameField e b hU j) x =
      ∑ k, A.structureFunction e b hU i j k x • A.anchorFrameField e b hU k x := by
  have : ContMDiffVectorBundle ∞ F V|[U] I := ContMDiffVectorBundle.restrictOpen U
  have hsum := congrFun (map_sum (ContMDiffSection.coeAddHom I E ∞ (TangentSpace I : U → Type _))
    (fun k ↦ (A.restrict U).anchorField
      (A.structureFunction e b hU i j k • frSection k)) Finset.univ) x
  simp only [ContMDiffSection.coeAddHom_apply, Finset.sum_apply] at hsum
  rw [anchorFrameField, anchorFrameField, ← (A.restrict U).anchor_bracket, ← anchorField_apply,
    A.bracket_openLocalFrameSection e b hU i j, map_sum, hsum]
  exact Finset.sum_congr rfl fun _ _ ↦ by
    rw [(A.restrict U).anchorField.map_smul, ContMDiffSection.smul_apply, anchorFrameField]

private theorem coeff_bracket_openLocalFrameSection_bracket [Fintype ι] (i j k m : ι) :
    frCoeff m ((A.restrict U).bracket (frSection i) ((A.restrict U).bracket (frSection j)
      (frSection k))) =
      vectorFieldDerivation (A.anchorFrameField e b hU i) (A.structureFunction e b hU j k m) +
        ∑ l, A.structureFunction e b hU j k l * A.structureFunction e b hU i l m := by
  classical
  rw [A.bracket_openLocalFrameSection e b hU j k, map_sum, map_sum]
  simp only [ContinuousMap.coe_mk, (A.restrict U).bracket_smul_right, map_add, LinearMap.map_smul,
    Bundle.Trivialization.openLocalFrameCoeff_openLocalFrameSection, Finset.sum_add_distrib,
    smul_eq_mul]
  rw [add_comm]; congr 1; simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ,
    ↓reduceIte, vectorFieldDerivation_anchorFrameField]

/-- **Jacobi structure equation** for `anchorFrameField` and `structureFunction`. -/
theorem jacobi_structureFunction [Fintype ι] (i j k m : ι) :
    vectorFieldDerivation (A.anchorFrameField e b hU i) (A.structureFunction e b hU j k m) +
      vectorFieldDerivation (A.anchorFrameField e b hU j) (A.structureFunction e b hU k i m) +
      vectorFieldDerivation (A.anchorFrameField e b hU k) (A.structureFunction e b hU i j m) +
      ∑ l, (A.structureFunction e b hU j k l * A.structureFunction e b hU i l m +
        A.structureFunction e b hU k i l * A.structureFunction e b hU j l m +
        A.structureFunction e b hU i j l * A.structureFunction e b hU k l m) = 0 := by
  have hjac := congrArg (frCoeff m)
    ((A.restrict U).jacobi_bracket (frSection i) (frSection j) (frSection k))
  simp only [map_add, map_zero, A.coeff_bracket_openLocalFrameSection_bracket e b hU] at hjac
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib]; linear_combination hjac

/-- **Coordinate change of `anchorFrameField`** between two local frames over `U`. -/
theorem anchorFrameField_coordChange [Fintype ι]
    (e' : Trivialization F (π F V)) [MemTrivializationAtlas e']
    {ι' : Type*} (b' : Basis ι' ℝ F) (hU' : (U : Set M) ⊆ e'.baseSet) (i' : ι') :
    A.anchorFrameField e' b' hU' i' =
      ∑ p, frCoeff p (e'.openLocalFrameSection I ∞ b' hU' i') • A.anchorFrameField e b hU p :=
  A.anchorField_restrict_eq_sum_anchorFrameField e b hU (e'.openLocalFrameSection I ∞ b' hU' i')

/-- **Coordinate change of `structureFunction`** between two local frames over `U`. -/
theorem structureFunction_coordChange [Fintype ι]
    (e' : Trivialization F (π F V)) [MemTrivializationAtlas e']
    {ι' : Type*} [Fintype ι'] (b' : Basis ι' ℝ F) (hU' : (U : Set M) ⊆ e'.baseSet)
    (i' j' : ι') (m : ι) :
    let g := fun r p ↦ frCoeff p (e'.openLocalFrameSection I ∞ b' hU' r)
    ∑ k', A.structureFunction e' b' hU' i' j' k' * g k' m =
      vectorFieldDerivation (A.anchorFrameField e' b' hU' i') (g j' m) -
        vectorFieldDerivation (A.anchorFrameField e' b' hU' j') (g i' m) +
        ∑ p, ∑ q, g i' p * g j' q * A.structureFunction e b hU p q m := by
  classical
  intro g; let fr' := e'.openLocalFrameSection I ∞ b' hU'
  trans frCoeff m ((A.restrict U).bracket (fr' i') (fr' j'))
  · rw [A.bracket_openLocalFrameSection e' b' hU' i' j', map_sum]
    exact (Finset.sum_congr rfl fun _ _ ↦ by rw [LinearMap.map_smul, smul_eq_mul]).symm
  · rw [A.restrict_bracket_eq_sum_structureFunction e b hU (fr' i') (fr' j'), map_sum]
    simp only [ContinuousMap.coe_mk, LinearMap.map_smul, smul_eq_mul, mul_ite, mul_one, mul_zero,
      Bundle.Trivialization.openLocalFrameCoeff_openLocalFrameSection, Finset.sum_ite_eq,
      Finset.mem_univ, ↓reduceIte, vectorFieldDerivation_anchorFrameField, fr', g]

end StructureFunctions
section Transition
variable [FiniteDimensional ℝ F] (I) [ContMDiffVectorBundle ∞ F V I] {U U' : Opens M}
  (e : Trivialization F (π F V)) [MemTrivializationAtlas e]
  {ι : Type*} (b : Basis ι ℝ F) (hU : (U : Set M) ⊆ e.baseSet)
  (e' : Trivialization F (π F V)) [MemTrivializationAtlas e']
  {ι' : Type*} (b' : Basis ι' ℝ F) (hU' : (U' : Set M) ⊆ e'.baseSet)

/-- The `(r, p)`-th smooth frame transition function on `U ⊓ U'`. -/
def localFrameTransition (r : ι') (p : ι) : C^∞⟮I, (U ⊓ U' : Opens M); ℝ⟯ :=
  e.openLocalFrameCoeff I ∞ b (U := U ⊓ U') (Set.inter_subset_left.trans hU) p
    (e'.openLocalFrameSection I ∞ b' (U := U ⊓ U') (Set.inter_subset_right.trans hU') r)

@[simp] theorem localFrameTransition_apply (r : ι') (p : ι) (z : (U ⊓ U' : Opens M)) :
    localFrameTransition I e b hU e' b' hU' r p z =
      e.localFrameCoeff I b p z.1 (e'.localFrame b' r z.1) :=
  (e.openLocalFrameCoeff_apply (I := I) (n := ∞) b (U := U ⊓ U')
    (Set.inter_subset_left.trans hU) p _ z).trans <| congrArg (e.localFrameCoeff I b p z.1)
      (e'.openLocalFrameSection_apply (I := I) (n := ∞) b' (U := U ⊓ U')
        (Set.inter_subset_right.trans hU') r z)
end Transition
end TauCeti.LieAlgebroid
