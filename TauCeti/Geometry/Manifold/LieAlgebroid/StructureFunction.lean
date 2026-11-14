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

Over an open subset `U : Opens M` contained in the base set of an atlas trivialization `e` of a
finite-rank smooth real vector bundle `V → M`, a model-fibre basis `b : Basis ι ℝ F` induces a
smooth local frame `e.openLocalFrameSection I ∞ b hU` of `V|_U` with dual `C^∞(U)`-linear
coefficient maps `e.openLocalFrameCoeff I ∞ b hU`. Restricting a Lie algebroid `A` to `U` reads its
anchor and bracket in this frame as:

* smooth anchor vector fields `A.anchorFrameField e b hU i` on `U`;
* smooth structure functions `A.structureFunction e b hU i j k : C^∞⟮I, U; ℝ⟯` satisfying
  `[e_i, e_j] = ∑ k, c_{ij}^k • e_k`.

These local invariants satisfy skew-symmetry (`structureFunction_swap`), the anchor-bracket equation
(`[ρ_i, ρ_j] = ∑ k, c_{ij}^k • ρ_k`, `mlieBracket_anchorFrameField`), the local-frame Jacobi
identity (`jacobi_structureFunction`), and the affine coordinate-change identities between two
local frames (`anchorFrameField_coordChange`, `structureFunction_coordChange`).

## Main definitions

* `TauCeti.LieAlgebroid.anchorFrameField`: the anchor vector fields `ρ(e_i)` of a local frame on
  `U ⊆ e.baseSet`.
* `TauCeti.LieAlgebroid.structureFunction`: the smooth structure functions `c_{ij}^k` of `A` in a
  local frame on `U ⊆ e.baseSet`.
* `TauCeti.LieAlgebroid.localFrameTransition`: the smooth frame transition coefficient functions on
  an overlap `U ⊓ U' : Opens M`.

## Main results

* `TauCeti.LieAlgebroid.bracket_eq_sum_openLocalFrame` and
  `TauCeti.LieAlgebroid.restrict_bracket_eq_sum_structureFunction`: local-frame formulas for the
  Lie bracket of sections over `U`.
* `TauCeti.LieAlgebroid.mlieBracket_anchorFrameField` and
  `TauCeti.LieAlgebroid.jacobi_structureFunction`: the structure equations in a local frame.
* `TauCeti.LieAlgebroid.anchorFrameField_coordChange` and
  `TauCeti.LieAlgebroid.structureFunction_coordChange`: transformation laws between two frames.

## References

* K. C. H. Mackenzie, *General theory of Lie groupoids and Lie algebroids*, London Math. Soc.
  Lecture Note Ser. 213, Cambridge University Press (2005), §3.3.
* M. Crainic and R. L. Fernandes, *Lectures on integrability of Lie brackets*, Geom. Topol.
  Monogr. 17 (2011), §1.1.
-/

public section

noncomputable section

open Bundle Manifold Module TopologicalSpace VectorField
open scoped ContDiff Topology

namespace TauCeti

namespace LieAlgebroid

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F] {V : M → Type*}
  [TopologicalSpace (TotalSpace F V)] [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)]
  [∀ x, TopologicalSpace (V x)] [FiberBundle F V] [VectorBundle ℝ F V]

section StructureFunctions

variable [IsManifold I ∞ M] [FiniteDimensional ℝ E] [T2Space M] [ContMDiffVectorBundle ∞ F V I]
  (A : LieAlgebroid I F V)
  (e : Trivialization F (π F V)) [MemTrivializationAtlas e]
  {ι : Type*} (b : Basis ι ℝ F) {U : Opens M} (hU : (U : Set M) ⊆ e.baseSet)

omit [FiniteDimensional ℝ F] in
/-- The `i`-th anchor vector field of `A` on `U ⊆ e.baseSet`, obtained by applying the restricted
anchor to the `i`-th local-frame section `e.openLocalFrameSection I ∞ b hU i`. -/
def anchorFrameField (i : ι) : Cₛ^∞⟮I; E, (TangentSpace I : U → Type _)⟯ :=
  (A.restrict U).anchorField (e.openLocalFrameSection I ∞ b hU i)

omit [FiniteDimensional ℝ F] in
theorem anchorFrameField_eq (i : ι) :
    A.anchorFrameField e b hU i =
      (A.restrict U).anchorField (e.openLocalFrameSection I ∞ b hU i) := by
  ext x
  rfl

omit [FiniteDimensional ℝ F] in
@[simp]
theorem anchorFrameField_apply (i : ι) (x : U) :
    A.anchorFrameField e b hU i x =
      (Manifold.tangentSpaceOpenEquiv (I := I) x).symm
        (A.anchor (x : M) (e.localFrame b i (x : M))) := by
  rw [anchorFrameField, anchorField_apply, restrict_anchor_apply]
  exact congrArg (fun v ↦ (Manifold.tangentSpaceOpenEquiv (I := I) x).symm (A.anchor (x : M) v))
    (e.openLocalFrameSection_apply (I := I) (n := ∞) b hU i x)

omit [FiniteDimensional ℝ F] in
/-- Pushing `anchorFrameField` to `M` via `tangentSpaceOpenEquiv` recovers `A.anchor` on
`e.localFrame`. -/
theorem tangentSpaceOpenEquiv_anchorFrameField_apply (i : ι) (x : U) :
    Manifold.tangentSpaceOpenEquiv (I := I) x (A.anchorFrameField e b hU i x) =
      A.anchor (x : M) (e.localFrame b i (x : M)) := by
  rw [anchorFrameField_apply, ContinuousLinearEquiv.apply_symm_apply]

omit [FiniteDimensional ℝ F] in
/-- Differentiating a smooth function on `U` along `anchorFrameField` agrees with `anchorDeriv` of
`A.restrict U` on the corresponding frame section. -/
@[simp]
theorem vectorFieldDerivation_anchorFrameField (i : ι) (f : C^∞⟮I, U; ℝ⟯) :
    vectorFieldDerivation (A.anchorFrameField e b hU i) f =
      (A.restrict U).anchorDeriv (e.openLocalFrameSection I ∞ b hU i) f := by
  ext x
  rw [ContMDiffSection.vectorFieldDerivation_apply_apply, anchorFrameField, anchorField_apply,
    anchorDeriv_apply]

/-- The smooth structure functions `c_{ij}^k` of `A` on `U ⊆ e.baseSet` relative to the local frame
`e.openLocalFrameSection I ∞ b hU`, characterized by `[e_i, e_j] = ∑ k, c_{ij}^k • e_k`. -/
def structureFunction (i j k : ι) : C^∞⟮I, U; ℝ⟯ :=
  e.openLocalFrameCoeff I ∞ b hU k
    ((A.restrict U).bracket
      (e.openLocalFrameSection I ∞ b hU i) (e.openLocalFrameSection I ∞ b hU j))

theorem structureFunction_eq (i j k : ι) :
    A.structureFunction e b hU i j k =
      e.openLocalFrameCoeff I ∞ b hU k
        ((A.restrict U).bracket
          (e.openLocalFrameSection I ∞ b hU i) (e.openLocalFrameSection I ∞ b hU j)) := by
  ext x
  rfl

/-- The Lie bracket of two local-frame sections expands in the frame with coefficients
`structureFunction`. -/
theorem bracket_openLocalFrameSection [Fintype ι] (i j : ι) :
    (A.restrict U).bracket
        (e.openLocalFrameSection I ∞ b hU i) (e.openLocalFrameSection I ∞ b hU j) =
      ∑ k, A.structureFunction e b hU i j k • e.openLocalFrameSection I ∞ b hU k :=
  e.eq_sum_openLocalFrameCoeff_smul b hU _

/-- The diagonal structure functions `c_{ii}^k` vanish. -/
@[simp]
theorem structureFunction_self (i k : ι) :
    A.structureFunction e b hU i i k = 0 := by
  rw [structureFunction, (A.restrict U).bracket_self, map_zero]

/-- The structure functions are skew-symmetric in their lower indices: `c_{ij}^k = -c_{ji}^k`. -/
theorem structureFunction_swap (i j k : ι) :
    A.structureFunction e b hU i j k = -A.structureFunction e b hU j i k := by
  rw [structureFunction, (A.restrict U).bracket_swap, map_neg, structureFunction]

/-- Over `U ⊆ e.baseSet`, the anchor vector field of any section expands in `anchorFrameField`. -/
theorem anchorField_restrict_eq_sum_anchorFrameField [Fintype ι]
    (s : Cₛ^∞⟮I; F, (⟨Subtype.val, continuous_subtype_val⟩ : C(U, M)) *ᵖ V⟯) :
    (A.restrict U).anchorField s =
      ∑ i, e.openLocalFrameCoeff I ∞ b hU i s • A.anchorFrameField e b hU i := by
  conv_lhs => rw [e.eq_sum_openLocalFrameCoeff_smul b hU s]
  rw [map_sum]
  exact Finset.sum_congr rfl fun i _ ↦ (A.restrict U).anchorField.map_smul _ _

/-- Over `U ⊆ e.baseSet`, `anchorDeriv` expands in the derivations along `anchorFrameField`. -/
theorem anchorDeriv_restrict_eq_sum_anchorFrameField [Fintype ι]
    (s : Cₛ^∞⟮I; F, (⟨Subtype.val, continuous_subtype_val⟩ : C(U, M)) *ᵖ V⟯)
    (f : C^∞⟮I, U; ℝ⟯) :
    (A.restrict U).anchorDeriv s f =
      ∑ i, e.openLocalFrameCoeff I ∞ b hU i s *
        vectorFieldDerivation (A.anchorFrameField e b hU i) f := by
  ext x
  rw [anchorDeriv_apply, ← anchorField_apply,
    A.anchorField_restrict_eq_sum_anchorFrameField e b hU s]
  let ιT := ContMDiffSection.coeAddHom I E ∞ (TangentSpace I : U → Type _)
  have hsum := congrFun (map_sum ιT
    (fun i ↦ e.openLocalFrameCoeff I ∞ b hU i s • A.anchorFrameField e b hU i) Finset.univ) x
  simp only [ιT, ContMDiffSection.coeAddHom_apply, Finset.sum_apply,
    ContMDiffSection.smul_apply] at hsum
  rw [hsum, map_sum, ContMDiffMap.coe_sum, Finset.sum_apply]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [map_smul, smul_eq_mul, ContMDiffMap.coe_mul, Pi.mul_apply,
    ContMDiffSection.vectorFieldDerivation_apply_apply]

omit [FiniteDimensional ℝ E] [T2Space M] in
private theorem anchorDeriv_open_eq_sum [Fintype ι]
    (B : LieAlgebroid I F ((⟨Subtype.val, continuous_subtype_val⟩ : C(U, M)) *ᵖ V))
    (s : Cₛ^∞⟮I; F, (⟨Subtype.val, continuous_subtype_val⟩ : C(U, M)) *ᵖ V⟯)
    (f : C^∞⟮I, U; ℝ⟯) :
    B.anchorDeriv s f =
      ∑ i, e.openLocalFrameCoeff I ∞ b hU i s *
        B.anchorDeriv (e.openLocalFrameSection I ∞ b hU i) f := by
  have : ContMDiffVectorBundle ∞ F ((⟨Subtype.val, continuous_subtype_val⟩ : C(U, M)) *ᵖ V) I :=
    ContMDiffVectorBundle.restrictOpen U
  ext x
  have hs_sum : s = ∑ i, e.openLocalFrameCoeff I ∞ b hU i s • e.openLocalFrameSection I ∞ b hU i :=
    e.eq_sum_openLocalFrameCoeff_smul b hU s
  have hval : s x = ∑ i, e.openLocalFrameCoeff I ∞ b hU i s x •
      e.openLocalFrameSection I ∞ b hU i x := by
    let ιV := ContMDiffSection.coeAddHom I F ∞
      ((⟨Subtype.val, continuous_subtype_val⟩ : C(U, M)) *ᵖ V)
    have hsum := congrFun (map_sum ιV
      (fun i ↦ e.openLocalFrameCoeff I ∞ b hU i s • e.openLocalFrameSection I ∞ b hU i)
      Finset.univ) x
    simp only [ιV, ContMDiffSection.coeAddHom_apply, Finset.sum_apply,
      ContMDiffSection.smul_apply] at hsum
    exact (congrArg (fun u ↦ u x) hs_sum).trans hsum
  rw [anchorDeriv_apply, hval, map_sum, map_sum, ContMDiffMap.coe_sum, Finset.sum_apply]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [map_smul, map_smul, smul_eq_mul, ContMDiffMap.coe_mul, Pi.mul_apply, anchorDeriv_apply]

omit [FiniteDimensional ℝ E] [T2Space M] in
/-- Over `U ⊆ e.baseSet`, the Lie bracket of any Lie algebroid on `V|_U` expands in
`e.openLocalFrameSection` in terms of `anchorDeriv` and the frame-section brackets. -/
theorem bracket_eq_sum_openLocalFrame [Fintype ι]
    (B : LieAlgebroid I F ((⟨Subtype.val, continuous_subtype_val⟩ : C(U, M)) *ᵖ V))
    (s t : Cₛ^∞⟮I; F, (⟨Subtype.val, continuous_subtype_val⟩ : C(U, M)) *ᵖ V⟯) :
    B.bracket s t =
      ∑ k, (B.anchorDeriv s (e.openLocalFrameCoeff I ∞ b hU k t) -
        B.anchorDeriv t (e.openLocalFrameCoeff I ∞ b hU k s) +
        ∑ i, ∑ j, e.openLocalFrameCoeff I ∞ b hU i s * e.openLocalFrameCoeff I ∞ b hU j t *
          e.openLocalFrameCoeff I ∞ b hU k
            (B.bracket (e.openLocalFrameSection I ∞ b hU i)
              (e.openLocalFrameSection I ∞ b hU j))) •
        e.openLocalFrameSection I ∞ b hU k := by
  have : ContMDiffVectorBundle ∞ F ((⟨Subtype.val, continuous_subtype_val⟩ : C(U, M)) *ᵖ V) I :=
    ContMDiffVectorBundle.restrictOpen U
  let fr := e.openLocalFrameSection I ∞ b hU
  let co := e.openLocalFrameCoeff I ∞ b hU
  let c := fun i j k ↦ co k (B.bracket (fr i) (fr j))
  have ht_sum : t = ∑ k, co k t • fr k := e.eq_sum_openLocalFrameCoeff_smul b hU t
  have hs_sum : s = ∑ i, co i s • fr i := e.eq_sum_openLocalFrameCoeff_smul b hU s
  have ht : B.bracket s t =
      ∑ k, co k t • B.bracket s (fr k) + ∑ k, B.anchorDeriv s (co k t) • fr k := by
    conv_lhs => rw [ht_sum]
    simp only [map_sum, B.bracket_smul_right, Finset.sum_add_distrib]
  have hs (j : ι) : co j t • B.bracket s (fr j) =
      (∑ i, ∑ k, (co i s * co j t * c i j k) • fr k) -
        ∑ i, (co j t * B.anchorDeriv (fr j) (co i s)) • fr i := by
    conv_lhs => rw [hs_sum]
    rw [LinearMap.map_sum₂, Finset.smul_sum]
    have hstep (i : ι) : co j t • B.bracket (co i s • fr i) (fr j) =
        (∑ k, (co i s * co j t * c i j k) • fr k) -
          (co j t * B.anchorDeriv (fr j) (co i s)) • fr i := by
      have hbr : B.bracket (fr i) (fr j) = ∑ k, c i j k • fr k :=
        e.eq_sum_openLocalFrameCoeff_smul b hU _
      rw [B.bracket_smul_left, smul_sub, mul_smul, hbr, Finset.smul_sum, Finset.smul_sum]
      congr 1
      exact Finset.sum_congr rfl fun k _ ↦ by rw [← mul_smul, ← mul_smul]; congr 1; ring
    rw [Finset.sum_congr rfl fun i _ ↦ hstep i, Finset.sum_sub_distrib]
  have hsub : ∑ j, ∑ i, (co j t * B.anchorDeriv (fr j) (co i s)) • fr i =
      ∑ k, B.anchorDeriv t (co k s) • fr k := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun k _ ↦ ?_
    rw [← Finset.sum_smul, anchorDeriv_open_eq_sum e b hU B t (co k s)]
  have htriple : ∑ j, ∑ i, ∑ k, (co i s * co j t * c i j k) • fr k =
      ∑ k, (∑ i, ∑ j, co i s * co j t * c i j k) • fr k := by
    rw [Finset.sum_comm]
    refine (Finset.sum_congr rfl fun i _ ↦ Finset.sum_comm).trans (Finset.sum_comm.trans ?_)
    exact Finset.sum_congr rfl fun k _ ↦ by
      rw [Finset.sum_smul]
      exact Finset.sum_congr rfl fun i _ ↦ Finset.sum_smul.symm
  rw [ht, Finset.sum_congr rfl fun j _ ↦ hs j, Finset.sum_sub_distrib, hsub, htriple]
  simp_rw [show e.openLocalFrameSection I ∞ b hU = fr from rfl,
    show e.openLocalFrameCoeff I ∞ b hU = co from rfl, add_smul, sub_smul]
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib]
  abel

/-- **Local-frame formula for the Lie bracket.** Over `U ⊆ e.baseSet`, the bracket of two smooth
sections is determined by their frame coordinates, `anchorFrameField`, and `structureFunction`. -/
theorem restrict_bracket_eq_sum_structureFunction [Fintype ι]
    (s t : Cₛ^∞⟮I; F, (⟨Subtype.val, continuous_subtype_val⟩ : C(U, M)) *ᵖ V⟯) :
    (A.restrict U).bracket s t =
      ∑ k, ((A.restrict U).anchorDeriv s (e.openLocalFrameCoeff I ∞ b hU k t) -
        (A.restrict U).anchorDeriv t (e.openLocalFrameCoeff I ∞ b hU k s) +
        ∑ i, ∑ j, e.openLocalFrameCoeff I ∞ b hU i s * e.openLocalFrameCoeff I ∞ b hU j t *
          A.structureFunction e b hU i j k) • e.openLocalFrameSection I ∞ b hU k :=
  bracket_eq_sum_openLocalFrame e b hU (A.restrict U) s t

/-- **Anchor-bracket structure equation.** In a local frame, the manifold Lie bracket of the anchor
vector fields expands in `anchorFrameField` with coefficients `structureFunction`. -/
theorem mlieBracket_anchorFrameField [Fintype ι] (i j : ι) (x : U) :
    mlieBracket I (A.anchorFrameField e b hU i) (A.anchorFrameField e b hU j) x =
      ∑ k, A.structureFunction e b hU i j k x • A.anchorFrameField e b hU k x := by
  have : ContMDiffVectorBundle ∞ F ((⟨Subtype.val, continuous_subtype_val⟩ : C(U, M)) *ᵖ V) I :=
    ContMDiffVectorBundle.restrictOpen U
  rw [anchorFrameField, anchorFrameField, ← (A.restrict U).anchor_bracket,
    ← anchorField_apply, A.bracket_openLocalFrameSection e b hU i j, map_sum]
  let ιT := ContMDiffSection.coeAddHom I E ∞ (TangentSpace I : U → Type _)
  have hsum := congrFun (map_sum ιT
    (fun k ↦ (A.restrict U).anchorField
      (A.structureFunction e b hU i j k • e.openLocalFrameSection I ∞ b hU k)) Finset.univ) x
  simp only [ιT, ContMDiffSection.coeAddHom_apply, Finset.sum_apply] at hsum
  rw [hsum]
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  rw [(A.restrict U).anchorField.map_smul, ContMDiffSection.smul_apply, anchorFrameField]

private theorem coeff_bracket_openLocalFrameSection_bracket [Fintype ι] (i j k m : ι) :
    e.openLocalFrameCoeff I ∞ b hU m
        ((A.restrict U).bracket (e.openLocalFrameSection I ∞ b hU i)
          ((A.restrict U).bracket
            (e.openLocalFrameSection I ∞ b hU j) (e.openLocalFrameSection I ∞ b hU k))) =
      vectorFieldDerivation (A.anchorFrameField e b hU i) (A.structureFunction e b hU j k m) +
        ∑ l, A.structureFunction e b hU j k l * A.structureFunction e b hU i l m := by
  classical
  rw [A.bracket_openLocalFrameSection e b hU j k, map_sum, map_sum]
  simp only [ContinuousMap.coe_mk, (A.restrict U).bracket_smul_right, map_add, LinearMap.map_smul,
    Bundle.Trivialization.openLocalFrameCoeff_openLocalFrameSection, Finset.sum_add_distrib,
    smul_eq_mul]
  rw [add_comm]
  congr 1
  simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte,
    vectorFieldDerivation_anchorFrameField]

/-- **Jacobi structure equation.** In a local frame, the cyclic sum of anchor derivatives and
quadratic contractions of `structureFunction` vanishes. -/
theorem jacobi_structureFunction [Fintype ι] (i j k m : ι) :
    vectorFieldDerivation (A.anchorFrameField e b hU i) (A.structureFunction e b hU j k m) +
      vectorFieldDerivation (A.anchorFrameField e b hU j) (A.structureFunction e b hU k i m) +
      vectorFieldDerivation (A.anchorFrameField e b hU k) (A.structureFunction e b hU i j m) +
      ∑ l, (A.structureFunction e b hU j k l * A.structureFunction e b hU i l m +
        A.structureFunction e b hU k i l * A.structureFunction e b hU j l m +
        A.structureFunction e b hU i j l * A.structureFunction e b hU k l m) = 0 := by
  have hjac := congrArg (e.openLocalFrameCoeff I ∞ b hU m)
    ((A.restrict U).jacobi_bracket (e.openLocalFrameSection I ∞ b hU i)
      (e.openLocalFrameSection I ∞ b hU j) (e.openLocalFrameSection I ∞ b hU k))
  simp only [map_add, map_zero, A.coeff_bracket_openLocalFrameSection_bracket e b hU] at hjac
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
  linear_combination hjac

/-- **Coordinate change of `anchorFrameField`.** Between two local frames over `U`, the anchor
vector fields transform linearly by the frame transition coefficients. -/
theorem anchorFrameField_coordChange [Fintype ι]
    (e' : Trivialization F (π F V)) [MemTrivializationAtlas e']
    {ι' : Type*} (b' : Basis ι' ℝ F) (hU' : (U : Set M) ⊆ e'.baseSet) (i' : ι') :
    A.anchorFrameField e' b' hU' i' =
      ∑ p, e.openLocalFrameCoeff I ∞ b hU p (e'.openLocalFrameSection I ∞ b' hU' i') •
        A.anchorFrameField e b hU p :=
  A.anchorField_restrict_eq_sum_anchorFrameField e b hU (e'.openLocalFrameSection I ∞ b' hU' i')

/-- **Coordinate change of `structureFunction`.** Between two local frames over `U`, the structure
functions satisfy the affine Lie algebroid gauge transformation law with inhomogeneous anchor
derivative terms. -/
theorem structureFunction_coordChange [Fintype ι]
    (e' : Trivialization F (π F V)) [MemTrivializationAtlas e']
    {ι' : Type*} [Fintype ι'] (b' : Basis ι' ℝ F) (hU' : (U : Set M) ⊆ e'.baseSet)
    (i' j' : ι') (m : ι) :
    let g := fun r p ↦ e.openLocalFrameCoeff I ∞ b hU p (e'.openLocalFrameSection I ∞ b' hU' r)
    ∑ k', A.structureFunction e' b' hU' i' j' k' * g k' m =
      vectorFieldDerivation (A.anchorFrameField e' b' hU' i') (g j' m) -
        vectorFieldDerivation (A.anchorFrameField e' b' hU' j') (g i' m) +
        ∑ p, ∑ q, g i' p * g j' q * A.structureFunction e b hU p q m := by
  classical
  intro g
  let fr' := e'.openLocalFrameSection I ∞ b' hU'
  have lhs_eq : e.openLocalFrameCoeff I ∞ b hU m ((A.restrict U).bracket (fr' i') (fr' j')) =
      ∑ k', A.structureFunction e' b' hU' i' j' k' * g k' m := by
    rw [A.bracket_openLocalFrameSection e' b' hU' i' j', map_sum]
    exact Finset.sum_congr rfl fun k' _ ↦ by rw [LinearMap.map_smul, smul_eq_mul]
  have rhs_eq : e.openLocalFrameCoeff I ∞ b hU m ((A.restrict U).bracket (fr' i') (fr' j')) =
      vectorFieldDerivation (A.anchorFrameField e' b' hU' i') (g j' m) -
        vectorFieldDerivation (A.anchorFrameField e' b' hU' j') (g i' m) +
        ∑ p, ∑ q, g i' p * g j' q * A.structureFunction e b hU p q m := by
    rw [A.restrict_bracket_eq_sum_structureFunction e b hU (fr' i') (fr' j'), map_sum]
    simp only [ContinuousMap.coe_mk, LinearMap.map_smul,
      Bundle.Trivialization.openLocalFrameCoeff_openLocalFrameSection,
      smul_eq_mul, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte,
      vectorFieldDerivation_anchorFrameField, fr', g]
  exact lhs_eq.symm.trans rhs_eq

end StructureFunctions

section Transition

variable (I) [ContMDiffVectorBundle ∞ F V I]

/-- The `(r, p)`-th smooth transition function on `U ⊓ U'` expressing the `r`-th frame section of
`(e', b')` in the `(e, b)`-frame. -/
def localFrameTransition {U U' : Opens M}
    (e : Trivialization F (π F V)) [MemTrivializationAtlas e]
    {ι : Type*} (b : Basis ι ℝ F) (hU : (U : Set M) ⊆ e.baseSet)
    (e' : Trivialization F (π F V)) [MemTrivializationAtlas e']
    {ι' : Type*} (b' : Basis ι' ℝ F) (hU' : (U' : Set M) ⊆ e'.baseSet)
    (r : ι') (p : ι) : C^∞⟮I, (U ⊓ U' : Opens M); ℝ⟯ :=
  e.openLocalFrameCoeff I ∞ b (U := U ⊓ U') (Set.inter_subset_left.trans hU) p
    (e'.openLocalFrameSection I ∞ b' (U := U ⊓ U') (Set.inter_subset_right.trans hU') r)

@[simp]
theorem localFrameTransition_apply {U U' : Opens M}
    (e : Trivialization F (π F V)) [MemTrivializationAtlas e]
    {ι : Type*} (b : Basis ι ℝ F) (hU : (U : Set M) ⊆ e.baseSet)
    (e' : Trivialization F (π F V)) [MemTrivializationAtlas e']
    {ι' : Type*} (b' : Basis ι' ℝ F) (hU' : (U' : Set M) ⊆ e'.baseSet)
    (r : ι') (p : ι) (z : (U ⊓ U' : Opens M)) :
    localFrameTransition I e b hU e' b' hU' r p z =
      e.localFrameCoeff I b p z.1 (e'.localFrame b' r z.1) :=
  (e.openLocalFrameCoeff_apply (I := I) (n := ∞) b (U := U ⊓ U')
    (Set.inter_subset_left.trans hU) p _ z).trans
    (congrArg (e.localFrameCoeff I b p z.1)
      (e'.openLocalFrameSection_apply (I := I) (n := ∞) b' (U := U ⊓ U')
        (Set.inter_subset_right.trans hU') r z))

end Transition

end LieAlgebroid

end TauCeti
