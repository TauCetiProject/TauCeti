/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.LieAlgebroid.StructureFunction
import TauCeti.Geometry.Manifold.ContMDiff.Subtype
import TauCeti.Geometry.Manifold.VectorBundle.Hom
import TauCeti.Geometry.Manifold.VectorBundle.LocalFrame
import TauCeti.Geometry.Manifold.VectorBundle.Scalar
import TauCeti.Geometry.Manifold.VectorField.LieBracket

/-!
# Constructing Lie algebroids from local frames and open covers

Given an open subset `U : Opens M` contained in the base set of an atlas trivialization `e` of a
finite-rank smooth real vector bundle `V → M` together with a model-fibre basis `b : Basis ι ℝ F`,
any family of smooth vector fields `ρ i` on `U` and skew-symmetric smooth structure functions
`c i j k : C^∞⟮I, U; ℝ⟯` satisfying the anchor-bracket equation `[ρ i, ρ j] = ∑ k, c i j k • ρ k`
and the local-frame Jacobi identity determines a unique Lie algebroid `LieAlgebroid.ofLocalFrame`
on the open-restricted vector bundle `V|_U` whose anchor fields and structure functions on the
frame `e.openLocalFrameSection I ∞ b hU` recover `(ρ, c)`.

When such local-frame data `(ρ a, c a)` are specified over an open cover `U a` of `M` and satisfy
the linear anchor transformation law and affine structure-function transformation law on every
overlap `U a ⊓ U a'`, they glue via `LieAlgebroid.glueOpenCover` to a unique global Lie algebroid
`LieAlgebroid.ofLocalFrameCover` on `V`.

## Main definitions

* `TauCeti.LieAlgebroid.ofLocalFrameAnchor`: the smooth anchor bundle map on `V|_U` sending the
  `i`-th local-frame vector to `ρ i`.
* `TauCeti.LieAlgebroid.ofLocalFrame`: the Lie algebroid on `V|_U` constructed from anchor vector
  fields and structure functions satisfying skew-symmetry, anchor-bracket, and Jacobi equations.
* `TauCeti.LieAlgebroid.ofLocalFrameCover`: the global Lie algebroid on `V` glued from compatible
  local-frame data over an open cover of `M`.

## Main results

* `TauCeti.LieAlgebroid.ofLocalFrame_anchorField_openLocalFrameSection` and
  `TauCeti.LieAlgebroid.ofLocalFrame_coeff_bracket_openLocalFrameSection`: evaluating `ofLocalFrame`
  on the local frame recovers `ρ` and `c`.
* `TauCeti.LieAlgebroid.eq_ofLocalFrame` and
  `TauCeti.LieAlgebroid.ofLocalFrame_anchorFrameField_structureFunction`: uniqueness of
  `ofLocalFrame` and reconstruction of `A.restrict U`.
* `TauCeti.LieAlgebroid.ofLocalFrameCover_restrict` and
  `TauCeti.LieAlgebroid.eq_ofLocalFrameCover`: restriction and uniqueness for `ofLocalFrameCover`.

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

private theorem mvfderiv_sum_contMDiffMap_apply {E H : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {N : Type*} [TopologicalSpace N] [ChartedSpace H N]
    {γ : Type*} (S : Finset γ) (f : γ → C^∞⟮I, N; ℝ⟯) (z : N) (w : TangentSpace I z) :
    mvfderiv I (∑ r ∈ S, f r : C^∞⟮I, N; ℝ⟯) z w = ∑ r ∈ S, mvfderiv I (f r) z w := by
  classical
  induction S using Finset.induction_on with
  | empty => simp only [Finset.sum_empty, ContMDiffMap.coe_zero, mvfderiv_zero,
      _root_.zero_apply]
  | insert r₀ S hr₀ ih =>
    simp only [Finset.sum_insert hr₀]
    have hadd : (⇑(f r₀ + ∑ r ∈ S, f r) : N → ℝ) = ⇑(f r₀) + ⇑(∑ r ∈ S, f r) := rfl
    rw [hadd, mvfderiv_add ((f r₀).contMDiff.mdifferentiableAt (by simp))
      ((∑ r ∈ S, f r).contMDiff.mdifferentiableAt (by simp)),
      _root_.add_apply, ih]

private theorem derivation_commutator_smul_right {R : Type*} [CommRing R] [Algebra ℝ R]
    (D₁ D₂ : Derivation ℝ R R) (f : R) :
    ⁅D₁, f • D₂⁆ = f • ⁅D₁, D₂⁆ + (D₁ f) • D₂ := by
  ext g
  simp only [Derivation.commutator_apply, _root_.add_apply, _root_.smul_apply, smul_eq_mul,
    Derivation.leibniz]
  ring

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F] {V : M → Type*}
  [TopologicalSpace (TotalSpace F V)] [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)]
  [∀ x, TopologicalSpace (V x)] [FiberBundle F V] [VectorBundle ℝ F V]

section Helpers

variable (I) [ContMDiffVectorBundle ∞ F V I]

omit [IsManifold I ∞ M] [FiniteDimensional ℝ F] in
private theorem localFrameCoeff_eq_coord
    (e : Trivialization F (π F V)) [MemTrivializationAtlas e]
    {ι : Type*} (b : Basis ι ℝ F) {x : M} (hx : x ∈ e.baseSet) (v : V x) (i : ι) :
    e.localFrameCoeff I b i x v = b.coord i (e.continuousLinearMapAt ℝ x v) := by
  have h := e.localFrameCoeff_eq_coeff (I := I) (b := b) (s := FiberBundle.extend F v) hx (i := i)
  have hv : FiberBundle.extend F v x = v := by simp
  have hT : (T% (FiberBundle.extend F v)) x = ⟨x, v⟩ := congrArg (TotalSpace.mk' F x) hv
  rw [hv, hT, ← e.continuousLinearMapAt_apply_of_mem (R := ℝ) hx v, ← b.coord_apply] at h
  exact h

omit [IsManifold I ∞ M] [FiniteDimensional ℝ F] in
private theorem eq_sum_localFrameCoeff_smul_at
    (e : Trivialization F (π F V)) [MemTrivializationAtlas e]
    {ι : Type*} [Fintype ι] (b : Basis ι ℝ F) {x : M} (hx : x ∈ e.baseSet) (v : V x) :
    v = ∑ i, e.localFrameCoeff I b i x v • e.localFrame b i x := by
  simpa only [FiberBundle.extend_apply_self] using
    e.eq_sum_localFrameCoeff_smul (I := I) (b := b) (s := FiberBundle.extend F v) hx

end Helpers

/-! ### Converse construction from local-frame data -/

section OfLocalFrame

variable [ContMDiffVectorBundle ∞ F V I]
  (e : Trivialization F (π F V)) [MemTrivializationAtlas e]
  {ι : Type*} [Fintype ι] (b : Basis ι ℝ F) {U : Opens M} (hU : (U : Set M) ⊆ e.baseSet)

include e b hU

private def ofLocalFrameAnchorTerm
    (ρ : ι → Cₛ^∞⟮I; E, (TangentSpace I : U → Type _)⟯) (i : ι) :
    Cₛ^∞⟮I; F →L[ℝ] E,
      fun x : U ↦ (((⟨Subtype.val, continuous_subtype_val⟩ : C(U, M)) *ᵖ V) x) →L[ℝ]
        TangentSpace I x⟯ where
  toFun x :=
    ((LinearMap.toContinuousLinearMap (b.coord i)).comp
      (e.continuousLinearMapAt ℝ (x : M))).smulRight (ρ i x)
  contMDiff_toFun := by
    let ιU : C(U, M) := ⟨Subtype.val, continuous_subtype_val⟩
    have hlift : ContMDiff (I.prod 𝓘(ℝ, F)) (I.prod 𝓘(ℝ, F)) ∞
        (Pullback.lift ιU : TotalSpace F (ιU *ᵖ V) → TotalSpace F V) :=
      Bundle.Pullback.contMDiff_lift ιU contMDiff_subtype_val
    have hcoord : ContMDiff (I.prod 𝓘(ℝ, F)) 𝓘(ℝ, F) ∞
        (fun p : TotalSpace F (ιU *ᵖ V) ↦ (e (Pullback.lift ιU p)).2) :=
      ((e.contMDiff_iff fun p ↦ e.mem_source.2 (hU p.proj.2)).1 hlift).2
    have ha : ContMDiff (I.prod 𝓘(ℝ, F)) 𝓘(ℝ, ℝ) ∞
        (fun p : TotalSpace F (ιU *ᵖ V) ↦
          b.coord i (e.continuousLinearMapAt ℝ (p.proj : M) p.2)) :=
      ((LinearMap.toContinuousLinearMap (b.coord i)).contMDiff.comp hcoord).congr fun p ↦
        congrArg (b.coord i)
          (e.continuousLinearMapAt_apply_of_mem (R := ℝ) (hU p.proj.2) (p.2 : V (p.proj : M)))
    exact (TauCeti.contMDiff_hom_bundle_iff (E₁ := (ιU *ᵖ V)) _).2
      (ha.smul_totalSpace ((ρ i).contMDiff.comp (Bundle.contMDiff_proj (ιU *ᵖ V))))

/-- The smooth anchor bundle map on `V|_U` sending the `i`-th local-frame vector to `ρ i`. -/
def ofLocalFrameAnchor (ρ : ι → Cₛ^∞⟮I; E, (TangentSpace I : U → Type _)⟯) :
    Cₛ^∞⟮I; F →L[ℝ] E,
      fun x : U ↦ (((⟨Subtype.val, continuous_subtype_val⟩ : C(U, M)) *ᵖ V) x) →L[ℝ]
        TangentSpace I x⟯ :=
  ∑ i, ofLocalFrameAnchorTerm e b hU ρ i

@[simp]
theorem ofLocalFrameAnchor_apply (ρ : ι → Cₛ^∞⟮I; E, (TangentSpace I : U → Type _)⟯) (x : U)
    (v : ((⟨Subtype.val, continuous_subtype_val⟩ : C(U, M)) *ᵖ V) x) :
    dsimp% only [ContinuousMap.coe_mk]
      (ofLocalFrameAnchor e b hU ρ x v = ∑ i, e.localFrameCoeff I b i (x : M) v • ρ i x) := by
  let ιH := ContMDiffSection.coeAddHom I (F →L[ℝ] E) ∞
    (fun y : U ↦ (((⟨Subtype.val, continuous_subtype_val⟩ : C(U, M)) *ᵖ V) y) →L[ℝ]
      TangentSpace I y)
  have hsum := congrFun (map_sum ιH (fun i ↦ ofLocalFrameAnchorTerm e b hU ρ i) Finset.univ) x
  simp only [ιH, ContMDiffSection.coeAddHom_apply, Finset.sum_apply] at hsum
  rw [ofLocalFrameAnchor, hsum, _root_.sum_apply]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  exact congrArg (· • ρ i x) (localFrameCoeff_eq_coord I e b (hU x.2) (v : V (x : M)) i).symm

theorem ofLocalFrameAnchor_localFrame (ρ : ι → Cₛ^∞⟮I; E, (TangentSpace I : U → Type _)⟯)
    (i : ι) (x : U) :
    ofLocalFrameAnchor e b hU ρ x (e.openLocalFrameSection I ∞ b hU i x) = ρ i x := by
  classical
  rw [ofLocalFrameAnchor_apply]
  have h (j : ι) : e.localFrameCoeff I b j (x : M) (e.openLocalFrameSection I ∞ b hU i x) =
      if j = i then 1 else 0 := by
    rw [e.openLocalFrameSection_apply, TauCeti.Manifold.localFrameCoeff_localFrame b (hU x.2)]
  simp only [h, ite_smul, one_smul, zero_smul, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]

private def ofLocalFrameDeriv (ρ : ι → Cₛ^∞⟮I; E, (TangentSpace I : U → Type _)⟯) :
    Cₛ^∞⟮I; F, (⟨Subtype.val, continuous_subtype_val⟩ : C(U, M)) *ᵖ V⟯ →ₗ[C^∞⟮I, U; ℝ⟯]
      Derivation ℝ C^∞⟮I, U; ℝ⟯ C^∞⟮I, U; ℝ⟯ where
  toFun s := ∑ i, e.openLocalFrameCoeff I ∞ b hU i s • vectorFieldDerivation (ρ i)
  map_add' s t := by simp only [map_add, add_smul, Finset.sum_add_distrib]
  map_smul' f s := by
    simp only [LinearMap.map_smul, RingHom.id_apply, Finset.smul_sum, smul_smul, smul_eq_mul]

private theorem ofLocalFrameDeriv_apply_apply
    (ρ : ι → Cₛ^∞⟮I; E, (TangentSpace I : U → Type _)⟯)
    (s : Cₛ^∞⟮I; F, (⟨Subtype.val, continuous_subtype_val⟩ : C(U, M)) *ᵖ V⟯)
    (f : C^∞⟮I, U; ℝ⟯) (x : U) :
    ofLocalFrameDeriv e b hU ρ s f x = mvfderiv I f x (ofLocalFrameAnchor e b hU ρ x (s x)) := by
  rw [ofLocalFrameDeriv, LinearMap.coe_mk, AddHom.coe_mk, _root_.sum_apply,
    ContMDiffMap.coe_sum, Finset.sum_apply, ofLocalFrameAnchor_apply, map_sum]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [_root_.smul_apply, smul_eq_mul, ContMDiffMap.coe_mul, Pi.mul_apply,
    e.openLocalFrameCoeff_apply, ContMDiffSection.vectorFieldDerivation_apply_apply,
    map_smul, smul_eq_mul]

private theorem ofLocalFrameDeriv_openLocalFrameSection
    (ρ : ι → Cₛ^∞⟮I; E, (TangentSpace I : U → Type _)⟯) (i : ι) :
    ofLocalFrameDeriv e b hU ρ (e.openLocalFrameSection I ∞ b hU i) =
      vectorFieldDerivation (ρ i) := by
  classical
  simp only [ContinuousMap.coe_mk, ofLocalFrameDeriv, LinearMap.coe_mk, AddHom.coe_mk,
    Bundle.Trivialization.openLocalFrameCoeff_openLocalFrameSection, ite_smul, one_smul, zero_smul,
    Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]

private def ofLocalFrameBracket (ρ : ι → Cₛ^∞⟮I; E, (TangentSpace I : U → Type _)⟯)
    (c : ι → ι → ι → C^∞⟮I, U; ℝ⟯) :
    Cₛ^∞⟮I; F, (⟨Subtype.val, continuous_subtype_val⟩ : C(U, M)) *ᵖ V⟯ →ₗ[ℝ]
      Cₛ^∞⟮I; F, (⟨Subtype.val, continuous_subtype_val⟩ : C(U, M)) *ᵖ V⟯ →ₗ[ℝ]
        Cₛ^∞⟮I; F, (⟨Subtype.val, continuous_subtype_val⟩ : C(U, M)) *ᵖ V⟯ :=
  let D := ofLocalFrameDeriv e b hU ρ
  let co := e.openLocalFrameCoeff I ∞ b hU
  let fr := e.openLocalFrameSection I ∞ b hU
  LinearMap.mk₂ ℝ
    (fun s t ↦ ∑ k, (D s (co k t) - D t (co k s) +
      ∑ i, ∑ j, co i s * co j t * c i j k) • fr k)
    (fun s s' t ↦ by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun k _ ↦ ?_
      rw [← add_smul]
      congr 1
      simp only [map_add, _root_.add_apply, add_mul, Finset.sum_add_distrib]
      abel)
    (fun r s t ↦ by
      rw [Finset.smul_sum]
      refine Finset.sum_congr rfl fun k _ ↦ ?_
      have hco (m : ι) : co m (r • s) = r • co m s :=
        LinearMapClass.map_smul_of_tower (co m) r s
      have hD : D (r • s) = r • D s := LinearMapClass.map_smul_of_tower D r s
      rw [← smul_assoc r _ (fr k)]
      congr 1
      simp only [hD, hco, _root_.smul_apply, Derivation.map_smul, smul_mul_assoc,
        smul_sub, smul_add, Finset.smul_sum])
    (fun s t t' ↦ by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun k _ ↦ ?_
      rw [← add_smul]
      congr 1
      simp only [map_add, _root_.add_apply, mul_add, add_mul, Finset.sum_add_distrib]
      abel)
    (fun r s t ↦ by
      rw [Finset.smul_sum]
      refine Finset.sum_congr rfl fun k _ ↦ ?_
      have hco (m : ι) : co m (r • t) = r • co m t :=
        LinearMapClass.map_smul_of_tower (co m) r t
      have hD : D (r • t) = r • D t := LinearMapClass.map_smul_of_tower D r t
      rw [← smul_assoc r _ (fr k)]
      congr 1
      simp only [hD, hco, _root_.smul_apply, Derivation.map_smul, mul_smul_comm,
        smul_mul_assoc, smul_sub, smul_add, Finset.smul_sum])

private theorem ofLocalFrameBracket_coeff (ρ : ι → Cₛ^∞⟮I; E, (TangentSpace I : U → Type _)⟯)
    (c : ι → ι → ι → C^∞⟮I, U; ℝ⟯)
    (s t : Cₛ^∞⟮I; F, (⟨Subtype.val, continuous_subtype_val⟩ : C(U, M)) *ᵖ V⟯) (m : ι) :
    e.openLocalFrameCoeff I ∞ b hU m (ofLocalFrameBracket e b hU ρ c s t) =
      ofLocalFrameDeriv e b hU ρ s (e.openLocalFrameCoeff I ∞ b hU m t) -
        ofLocalFrameDeriv e b hU ρ t (e.openLocalFrameCoeff I ∞ b hU m s) +
        ∑ i, ∑ j, e.openLocalFrameCoeff I ∞ b hU i s *
          e.openLocalFrameCoeff I ∞ b hU j t * c i j m := by
  classical
  rw [ofLocalFrameBracket, LinearMap.mk₂_apply, map_sum]
  simp only [ContinuousMap.coe_mk, LinearMap.map_smul,
    Bundle.Trivialization.openLocalFrameCoeff_openLocalFrameSection,
    smul_eq_mul, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte]

private theorem ofLocalFrameBracket_openLocalFrameSection
    (ρ : ι → Cₛ^∞⟮I; E, (TangentSpace I : U → Type _)⟯) (c : ι → ι → ι → C^∞⟮I, U; ℝ⟯)
    (i j : ι) :
    ofLocalFrameBracket e b hU ρ c
        (e.openLocalFrameSection I ∞ b hU i) (e.openLocalFrameSection I ∞ b hU j) =
      ∑ k, c i j k • e.openLocalFrameSection I ∞ b hU k := by
  classical
  rw [ofLocalFrameBracket, LinearMap.mk₂_apply]
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  congr 1
  have hconst (D : Derivation ℝ C^∞⟮I, U; ℝ⟯ C^∞⟮I, U; ℝ⟯) (p q : ι) :
      D (e.openLocalFrameCoeff I ∞ b hU p (e.openLocalFrameSection I ∞ b hU q)) = 0 := by
    rw [Bundle.Trivialization.openLocalFrameCoeff_openLocalFrameSection]
    split_ifs
    · exact D.map_one_eq_zero
    · exact D.map_zero
  rw [hconst, hconst, sub_self, zero_add]
  dsimp only [ContinuousMap.coe_mk]
  simp_rw [Bundle.Trivialization.openLocalFrameCoeff_openLocalFrameSection, mul_assoc,
    ite_mul, one_mul, zero_mul]
  have hinner (p : ι) : (∑ q, if p = i then if q = j then c p q k else 0 else 0) =
      if p = i then c p j k else 0 := by
    split_ifs <;> simp
  simp_rw [hinner]
  simp

private theorem ofLocalFrameBracket_self (ρ : ι → Cₛ^∞⟮I; E, (TangentSpace I : U → Type _)⟯)
    (c : ι → ι → ι → C^∞⟮I, U; ℝ⟯) (hc_swap : ∀ i j k, c i j k = -c j i k)
    (s : Cₛ^∞⟮I; F, (⟨Subtype.val, continuous_subtype_val⟩ : C(U, M)) *ᵖ V⟯) :
    ofLocalFrameBracket e b hU ρ c s s = 0 := by
  rw [ofLocalFrameBracket, LinearMap.mk₂_apply]
  refine Finset.sum_eq_zero fun k _ ↦ ?_
  have hsum : ∑ i, ∑ j, e.openLocalFrameCoeff I ∞ b hU i s *
      e.openLocalFrameCoeff I ∞ b hU j s * c i j k = 0 := by
    ext x
    simp only [ContMDiffMap.coe_sum, ContMDiffMap.coe_zero, Pi.zero_apply, Finset.sum_apply,
      ContMDiffMap.coe_mul, Pi.mul_apply]
    have hneg : (∑ i, ∑ j, e.openLocalFrameCoeff I ∞ b hU i s x *
        e.openLocalFrameCoeff I ∞ b hU j s x * c i j k x) =
        -(∑ i, ∑ j, e.openLocalFrameCoeff I ∞ b hU i s x *
          e.openLocalFrameCoeff I ∞ b hU j s x * c i j k x) := by
      conv_lhs => rw [Finset.sum_comm]
      rw [← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun i _ ↦ ?_
      rw [← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun j _ ↦ ?_
      have hc := congrFun (congrArg DFunLike.coe (hc_swap j i k)) x
      rw [ContMDiffMap.coe_neg, Pi.neg_apply] at hc
      rw [hc]
      ring
    linarith
  rw [sub_self, zero_add, hsum, zero_smul]

private theorem ofLocalFrameBracket_swap (ρ : ι → Cₛ^∞⟮I; E, (TangentSpace I : U → Type _)⟯)
    (c : ι → ι → ι → C^∞⟮I, U; ℝ⟯) (hc_swap : ∀ i j k, c i j k = -c j i k)
    (s t : Cₛ^∞⟮I; F, (⟨Subtype.val, continuous_subtype_val⟩ : C(U, M)) *ᵖ V⟯) :
    ofLocalFrameBracket e b hU ρ c s t = -ofLocalFrameBracket e b hU ρ c t s := by
  rw [ofLocalFrameBracket, LinearMap.mk₂_apply, LinearMap.mk₂_apply, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  rw [← neg_smul]
  congr 1
  have hsum : (∑ i, ∑ j, e.openLocalFrameCoeff I ∞ b hU i s *
      e.openLocalFrameCoeff I ∞ b hU j t * c i j k) =
      -(∑ i, ∑ j, e.openLocalFrameCoeff I ∞ b hU i t *
        e.openLocalFrameCoeff I ∞ b hU j s * c i j k) := by
    conv_lhs => rw [Finset.sum_comm]
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    rw [hc_swap j i k]
    ring
  rw [hsum]
  ring

private theorem ofLocalFrameBracket_smul_right
    (ρ : ι → Cₛ^∞⟮I; E, (TangentSpace I : U → Type _)⟯) (c : ι → ι → ι → C^∞⟮I, U; ℝ⟯)
    (s t : Cₛ^∞⟮I; F, (⟨Subtype.val, continuous_subtype_val⟩ : C(U, M)) *ᵖ V⟯)
    (f : C^∞⟮I, U; ℝ⟯) :
    ofLocalFrameBracket e b hU ρ c s (f • t) =
      f • ofLocalFrameBracket e b hU ρ c s t + ofLocalFrameDeriv e b hU ρ s f • t := by
  let D := ofLocalFrameDeriv e b hU ρ
  let co := e.openLocalFrameCoeff I ∞ b hU
  let fr := e.openLocalFrameSection I ∞ b hU
  have hterm : ofLocalFrameBracket e b hU ρ c s (f • t) =
      ∑ k, (f * (D s (co k t) - D t (co k s) + ∑ i, ∑ j, co i s * co j t * c i j k) +
        D s f * co k t) • fr k := by
    rw [ofLocalFrameBracket, LinearMap.mk₂_apply]
    refine Finset.sum_congr rfl fun k _ ↦ ?_
    congr 1
    simp only [LinearMap.map_smul, smul_eq_mul, Derivation.leibniz, _root_.smul_apply]
    have hmul : (∑ i, ∑ j, co i s * (f * co j t) * c i j k) =
        f * ∑ i, ∑ j, co i s * co j t * c i j k := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ ↦ by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun j _ ↦ by ring
    rw [hmul]
    ring
  rw [hterm]
  simp_rw [add_smul, mul_smul]
  rw [Finset.sum_add_distrib]
  congr 1
  · rw [ofLocalFrameBracket, LinearMap.mk₂_apply, Finset.smul_sum]
  · rw [← Finset.smul_sum, ← e.eq_sum_openLocalFrameCoeff_smul b hU t]

private theorem ofLocalFrameDeriv_bracket_frame [CompleteSpace E]
    (ρ : ι → Cₛ^∞⟮I; E, (TangentSpace I : U → Type _)⟯) (c : ι → ι → ι → C^∞⟮I, U; ℝ⟯)
    (hρ_bracket : ∀ i j (x : U), mlieBracket I (ρ i) (ρ j) x = ∑ k, c i j k x • ρ k x)
    (i j : ι) :
    ⁅ofLocalFrameDeriv e b hU ρ (e.openLocalFrameSection I ∞ b hU i),
        ofLocalFrameDeriv e b hU ρ (e.openLocalFrameSection I ∞ b hU j)⁆ -
      ofLocalFrameDeriv e b hU ρ
        (ofLocalFrameBracket e b hU ρ c
          (e.openLocalFrameSection I ∞ b hU i) (e.openLocalFrameSection I ∞ b hU j)) = 0 := by
  have : IsManifold I (minSmoothness ℝ 2) U := IsManifold.of_le (n := ∞) (by simp)
  ext f x
  simp only [ofLocalFrameDeriv_openLocalFrameSection,
    ofLocalFrameBracket_openLocalFrameSection, map_sum, LinearMap.map_smul,
    _root_.sub_apply, Derivation.commutator_apply, _root_.zero_apply,
    ContMDiffMap.coe_sub, ContMDiffMap.coe_zero, Pi.sub_apply, Pi.zero_apply, sub_eq_zero,
    _root_.sum_apply, _root_.smul_apply, smul_eq_mul, ContMDiffMap.coe_sum, Finset.sum_apply]
  have hmlie := _root_.mvfderiv_mlieBracket (I := I) (x := x)
    (f.contMDiff.contMDiffAt) (by simp)
    ((ρ i).contMDiff.mdifferentiableAt (by simp))
    ((ρ j).contMDiff.mdifferentiableAt (by simp))
  rw [hρ_bracket i j x, map_sum] at hmlie
  have hvf (k : ι) : ⇑(vectorFieldDerivation (ρ k) f) = fun y ↦ mvfderiv I f y (ρ k y) :=
    funext fun y ↦ ContMDiffSection.vectorFieldDerivation_apply_apply (ρ k) f y
  rw [ContMDiffSection.vectorFieldDerivation_apply_apply,
    ContMDiffSection.vectorFieldDerivation_apply_apply, hvf j, hvf i, ← hmlie]
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  rw [map_smul, smul_eq_mul, ContMDiffMap.coe_mul, Pi.mul_apply,
    ContMDiffSection.vectorFieldDerivation_apply_apply]

private theorem ofLocalFrameDeriv_bracket [CompleteSpace E]
    (ρ : ι → Cₛ^∞⟮I; E, (TangentSpace I : U → Type _)⟯) (c : ι → ι → ι → C^∞⟮I, U; ℝ⟯)
    (hc_swap : ∀ i j k, c i j k = -c j i k)
    (hρ_bracket : ∀ i j (x : U), mlieBracket I (ρ i) (ρ j) x = ∑ k, c i j k x • ρ k x)
    (s t : Cₛ^∞⟮I; F, (⟨Subtype.val, continuous_subtype_val⟩ : C(U, M)) *ᵖ V⟯) :
    ofLocalFrameDeriv e b hU ρ (ofLocalFrameBracket e b hU ρ c s t) =
      ⁅ofLocalFrameDeriv e b hU ρ s, ofLocalFrameDeriv e b hU ρ t⁆ := by
  let D := ofLocalFrameDeriv e b hU ρ
  let B := ofLocalFrameBracket e b hU ρ c
  let Δ (u v : Cₛ^∞⟮I; F, _⟯) : Derivation ℝ C^∞⟮I, U; ℝ⟯ C^∞⟮I, U; ℝ⟯ := ⁅D u, D v⁆ - D (B u v)
  have hΔ_smul_r (u v : Cₛ^∞⟮I; F, _⟯) (f : C^∞⟮I, U; ℝ⟯) : Δ u (f • v) = f • Δ u v := by
    dsimp only [Δ, B]
    rw [D.map_smul f v, derivation_commutator_smul_right,
      ofLocalFrameBracket_smul_right e b hU ρ c u v f, map_add, D.map_smul, D.map_smul, smul_sub]
    abel
  have hΔ_swap (u v : Cₛ^∞⟮I; F, _⟯) : Δ u v = -Δ v u := by
    dsimp only [Δ, B]
    rw [← lie_skew (D u) (D v), ofLocalFrameBracket_swap e b hU ρ c hc_swap u v, map_neg]
    abel
  have hΔ_smul_l (u v : Cₛ^∞⟮I; F, _⟯) (f : C^∞⟮I, U; ℝ⟯) : Δ (f • u) v = f • Δ u v := by
    rw [hΔ_swap (f • u) v, hΔ_smul_r v u f, hΔ_swap v u]
    ext g; simp only [_root_.neg_apply, _root_.smul_apply, smul_eq_mul, mul_neg, neg_neg]
  suffices h0 : Δ s t = 0 from (sub_eq_zero.1 h0).symm
  conv_lhs => rw [e.eq_sum_openLocalFrameCoeff_smul b hU s]
  let φ := AddMonoidHom.mk' (fun u ↦ Δ u t) fun u₁ u₂ ↦ by
    ext g; dsimp only [Δ]
    simp only [map_add, LinearMap.add_apply, _root_.sub_apply, _root_.add_apply,
      Derivation.commutator_apply]; abel_nf
  have hφ := map_sum φ
    (fun i ↦ e.openLocalFrameCoeff I ∞ b hU i s • e.openLocalFrameSection I ∞ b hU i) Finset.univ
  simp only [φ, AddMonoidHom.mk'_apply] at hφ
  rw [hφ]; refine Finset.sum_eq_zero fun i _ ↦ ?_
  rw [hΔ_smul_l]; conv_lhs => rw [e.eq_sum_openLocalFrameCoeff_smul b hU t]
  let ψ := AddMonoidHom.mk' (fun v ↦ Δ (e.openLocalFrameSection I ∞ b hU i) v) fun v₁ v₂ ↦ by
    ext g; dsimp only [Δ]
    simp only [map_add, _root_.sub_apply, _root_.add_apply, Derivation.commutator_apply]; abel_nf
  have hψ := map_sum ψ
    (fun j ↦ e.openLocalFrameCoeff I ∞ b hU j t • e.openLocalFrameSection I ∞ b hU j) Finset.univ
  simp only [ψ, AddMonoidHom.mk'_apply] at hψ
  rw [hψ, Finset.smul_sum]; exact Finset.sum_eq_zero fun j _ ↦ by
    rw [hΔ_smul_r]; dsimp only [Δ, D, B]
    rw [ofLocalFrameDeriv_bracket_frame e b hU ρ c hρ_bracket i j, smul_zero, smul_zero]

private theorem ofLocalFrameJacobi_frame
    (ρ : ι → Cₛ^∞⟮I; E, (TangentSpace I : U → Type _)⟯) (c : ι → ι → ι → C^∞⟮I, U; ℝ⟯)
    (hc_jacobi : ∀ i j k m,
      vectorFieldDerivation (ρ i) (c j k m) +
        vectorFieldDerivation (ρ j) (c k i m) +
        vectorFieldDerivation (ρ k) (c i j m) +
        ∑ l, (c j k l * c i l m + c k i l * c j l m + c i j l * c k l m) = 0)
    (i j k : ι) :
    ofLocalFrameBracket e b hU ρ c (e.openLocalFrameSection I ∞ b hU i)
        (ofLocalFrameBracket e b hU ρ c (e.openLocalFrameSection I ∞ b hU j)
          (e.openLocalFrameSection I ∞ b hU k)) +
      ofLocalFrameBracket e b hU ρ c (e.openLocalFrameSection I ∞ b hU j)
        (ofLocalFrameBracket e b hU ρ c (e.openLocalFrameSection I ∞ b hU k)
          (e.openLocalFrameSection I ∞ b hU i)) +
      ofLocalFrameBracket e b hU ρ c (e.openLocalFrameSection I ∞ b hU k)
        (ofLocalFrameBracket e b hU ρ c (e.openLocalFrameSection I ∞ b hU i)
          (e.openLocalFrameSection I ∞ b hU j)) = 0 := by
  classical
  have hterm (p q r : ι) :
      ofLocalFrameBracket e b hU ρ c (e.openLocalFrameSection I ∞ b hU p)
        (ofLocalFrameBracket e b hU ρ c (e.openLocalFrameSection I ∞ b hU q)
          (e.openLocalFrameSection I ∞ b hU r)) =
      ∑ m, (vectorFieldDerivation (ρ p) (c q r m) + ∑ l, c q r l * c p l m) •
        e.openLocalFrameSection I ∞ b hU m := by
    rw [ofLocalFrameBracket_openLocalFrameSection, map_sum]
    simp_rw [ofLocalFrameBracket_smul_right, ofLocalFrameDeriv_openLocalFrameSection,
      ofLocalFrameBracket_openLocalFrameSection, Finset.smul_sum, ← mul_smul]
    rw [Finset.sum_add_distrib, Finset.sum_comm, add_comm]
    simp_rw [add_smul]
    rw [Finset.sum_add_distrib]
    congr 1
    exact Finset.sum_congr rfl fun m _ ↦ Finset.sum_smul.symm
  rw [hterm i j k, hterm j k i, hterm k i j, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_eq_zero fun m _ ↦ ?_
  rw [← add_smul, ← add_smul]
  have hsum : (∑ l, c j k l * c i l m) + (∑ l, c k i l * c j l m) + (∑ l, c i j l * c k l m) =
      ∑ l, (c j k l * c i l m + c k i l * c j l m + c i j l * c k l m) := by
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
  have heq : (vectorFieldDerivation (ρ i) (c j k m) + ∑ l, c j k l * c i l m) +
      (vectorFieldDerivation (ρ j) (c k i m) + ∑ l, c k i l * c j l m) +
      (vectorFieldDerivation (ρ k) (c i j m) + ∑ l, c i j l * c k l m) = 0 := by
    linear_combination hc_jacobi i j k m + hsum
  rw [heq, zero_smul]

private theorem ofLocalFrameJacobi_smul_right [CompleteSpace E]
    (ρ : ι → Cₛ^∞⟮I; E, (TangentSpace I : U → Type _)⟯) (c : ι → ι → ι → C^∞⟮I, U; ℝ⟯)
    (hc_swap : ∀ i j k, c i j k = -c j i k)
    (hρ_bracket : ∀ i j (x : U), mlieBracket I (ρ i) (ρ j) x = ∑ k, c i j k x • ρ k x)
    (x y z : Cₛ^∞⟮I; F, (⟨Subtype.val, continuous_subtype_val⟩ : C(U, M)) *ᵖ V⟯)
    (f : C^∞⟮I, U; ℝ⟯) :
    ofLocalFrameBracket e b hU ρ c x (ofLocalFrameBracket e b hU ρ c y (f • z)) +
      ofLocalFrameBracket e b hU ρ c y (ofLocalFrameBracket e b hU ρ c (f • z) x) +
      ofLocalFrameBracket e b hU ρ c (f • z) (ofLocalFrameBracket e b hU ρ c x y) =
      f • (ofLocalFrameBracket e b hU ρ c x (ofLocalFrameBracket e b hU ρ c y z) +
        ofLocalFrameBracket e b hU ρ c y (ofLocalFrameBracket e b hU ρ c z x) +
        ofLocalFrameBracket e b hU ρ c z (ofLocalFrameBracket e b hU ρ c x y)) := by
  let B := ofLocalFrameBracket e b hU ρ c
  let D := ofLocalFrameDeriv e b hU ρ
  have h1 : B x (B y (f • z)) =
      f • B x (B y z) + D x f • B y z + D y f • B x z + D x (D y f) • z := by
    dsimp only [B, D]
    rw [ofLocalFrameBracket_smul_right, map_add, ofLocalFrameBracket_smul_right,
      ofLocalFrameBracket_smul_right]
    abel
  have h2 : B y (B (f • z) x) =
      f • B y (B z x) - D y f • B x z - D x f • B y z - D y (D x f) • z := by
    dsimp only [B, D]
    rw [ofLocalFrameBracket_swap e b hU ρ c hc_swap (f • z) x, map_neg,
      ofLocalFrameBracket_smul_right, map_add, ofLocalFrameBracket_smul_right,
      ofLocalFrameBracket_smul_right, ofLocalFrameBracket_swap e b hU ρ c hc_swap x z,
      map_neg, smul_neg]
    abel
  have h3 : B (f • z) (B x y) = f • B z (B x y) - D (B x y) f • z := by
    dsimp only [B, D]
    rw [ofLocalFrameBracket_swap e b hU ρ c hc_swap (f • z) _,
      ofLocalFrameBracket_smul_right,
      ofLocalFrameBracket_swap e b hU ρ c hc_swap _ z, smul_neg]
    abel
  have hDB : D (B x y) f = D x (D y f) - D y (D x f) := by
    have h := congrFun (congrArg DFunLike.coe
      (ofLocalFrameDeriv_bracket e b hU ρ c hc_swap hρ_bracket x y)) f
    rwa [Derivation.commutator_apply] at h
  dsimp only [B] at h1 h2 h3 hDB
  rw [h1, h2, h3, hDB, sub_smul, smul_add, smul_add]
  abel

private theorem ofLocalFrameBracket_jacobi [CompleteSpace E]
    (ρ : ι → Cₛ^∞⟮I; E, (TangentSpace I : U → Type _)⟯) (c : ι → ι → ι → C^∞⟮I, U; ℝ⟯)
    (hc_swap : ∀ i j k, c i j k = -c j i k)
    (hρ_bracket : ∀ i j (x : U), mlieBracket I (ρ i) (ρ j) x = ∑ k, c i j k x • ρ k x)
    (hc_jacobi : ∀ i j k m,
      vectorFieldDerivation (ρ i) (c j k m) +
        vectorFieldDerivation (ρ j) (c k i m) +
        vectorFieldDerivation (ρ k) (c i j m) +
        ∑ l, (c j k l * c i l m + c k i l * c j l m + c i j l * c k l m) = 0)
    (s t u : Cₛ^∞⟮I; F, (⟨Subtype.val, continuous_subtype_val⟩ : C(U, M)) *ᵖ V⟯) :
    ofLocalFrameBracket e b hU ρ c s (ofLocalFrameBracket e b hU ρ c t u) =
      ofLocalFrameBracket e b hU ρ c (ofLocalFrameBracket e b hU ρ c s t) u +
        ofLocalFrameBracket e b hU ρ c t (ofLocalFrameBracket e b hU ρ c s u) := by
  let B := ofLocalFrameBracket e b hU ρ c
  let fr := e.openLocalFrameSection I ∞ b hU
  let J : Cₛ^∞⟮I; F, _⟯ → Cₛ^∞⟮I; F, _⟯ → Cₛ^∞⟮I; F, _⟯ → Cₛ^∞⟮I; F, _⟯ :=
    fun x y z ↦ B x (B y z) + B y (B z x) + B z (B x y)
  have hJ_cyc (x y z : Cₛ^∞⟮I; F, _⟯) : J x y z = J y z x := by simp only [J]; abel
  have hJ_smul₃ (x y z : Cₛ^∞⟮I; F, _⟯) (f : C^∞⟮I, U; ℝ⟯) : J x y (f • z) = f • J x y z :=
    ofLocalFrameJacobi_smul_right e b hU ρ c hc_swap hρ_bracket x y z f
  have hJ_smul₁ (x y z : Cₛ^∞⟮I; F, _⟯) (f : C^∞⟮I, U; ℝ⟯) : J (f • x) y z = f • J x y z := by
    rw [hJ_cyc (f • x) y z, hJ_smul₃, ← hJ_cyc x y z]
  have hJ_smul₂ (x y z : Cₛ^∞⟮I; F, _⟯) (f : C^∞⟮I, U; ℝ⟯) : J x (f • y) z = f • J x y z := by
    rw [hJ_cyc x (f • y) z, hJ_smul₁, ← hJ_cyc x y z]
  have hJ0 : J s t u = 0 := by
    conv_lhs => rw [e.eq_sum_openLocalFrameCoeff_smul b hU s]
    let φ₁ : Cₛ^∞⟮I; F, _⟯ →+ Cₛ^∞⟮I; F, _⟯ := AddMonoidHom.mk' (fun x ↦ J x t u) fun x₁ x₂ ↦ by
      simp only [J, map_add, LinearMap.add_apply]; abel
    have h₁ := map_sum φ₁ (fun i ↦ e.openLocalFrameCoeff I ∞ b hU i s • fr i) Finset.univ
    simp only [φ₁, AddMonoidHom.mk'_apply] at h₁
    rw [h₁]
    refine Finset.sum_eq_zero fun i _ ↦ ?_
    rw [hJ_smul₁]
    conv_lhs => rw [e.eq_sum_openLocalFrameCoeff_smul b hU t]
    let φ₂ : Cₛ^∞⟮I; F, _⟯ →+ Cₛ^∞⟮I; F, _⟯ :=
      AddMonoidHom.mk' (fun y ↦ J (fr i) y u) fun y₁ y₂ ↦ by
        simp only [J, map_add, LinearMap.add_apply]; abel
    have h₂ := map_sum φ₂ (fun j ↦ e.openLocalFrameCoeff I ∞ b hU j t • fr j) Finset.univ
    simp only [φ₂, AddMonoidHom.mk'_apply] at h₂
    rw [h₂, Finset.smul_sum]
    refine Finset.sum_eq_zero fun j _ ↦ ?_
    rw [hJ_smul₂]
    conv_lhs => rw [e.eq_sum_openLocalFrameCoeff_smul b hU u]
    let φ₃ : Cₛ^∞⟮I; F, _⟯ →+ Cₛ^∞⟮I; F, _⟯ :=
      AddMonoidHom.mk' (fun z ↦ J (fr i) (fr j) z) fun z₁ z₂ ↦ by
        simp only [J, map_add, LinearMap.add_apply]; abel
    have h₃ := map_sum φ₃ (fun k ↦ e.openLocalFrameCoeff I ∞ b hU k u • fr k) Finset.univ
    simp only [φ₃, AddMonoidHom.mk'_apply] at h₃
    rw [h₃, Finset.smul_sum, Finset.smul_sum]
    exact Finset.sum_eq_zero fun k _ ↦ by
      rw [hJ_smul₃]
      dsimp only [J, B, fr]
      rw [ofLocalFrameJacobi_frame e b hU ρ c hc_jacobi i j k, smul_zero, smul_zero, smul_zero]
  dsimp only [J, B] at hJ0
  rw [ofLocalFrameBracket_swap e b hU ρ c hc_swap u s, map_neg,
    ofLocalFrameBracket_swap e b hU ρ c hc_swap u _] at hJ0
  rw [← sub_eq_zero, ← hJ0]
  abel

/-- **Converse local-frame construction of a Lie algebroid.** Let `U : Opens M` lie in `e.baseSet`,
let `ρ i` be smooth vector fields on `U`, and let `c i j k` be smooth functions on `U` satisfying:
* skew-symmetry `c i j k = -c j i k`;
* the anchor-bracket equation `[ρ i, ρ j] = ∑ k, c i j k • ρ k`;
* the Jacobi structure equation.

Then `V|_U` carries a canonical Lie algebroid structure with anchor `ofLocalFrameAnchor` and
local-frame bracket determined by `(ρ, c)`. -/
def ofLocalFrame [CompleteSpace E]
    (ρ : ι → Cₛ^∞⟮I; E, (TangentSpace I : U → Type _)⟯)
    (c : ι → ι → ι → C^∞⟮I, U; ℝ⟯)
    (hc_swap : ∀ i j k, c i j k = -c j i k)
    (hρ_bracket : ∀ i j (x : U), mlieBracket I (ρ i) (ρ j) x = ∑ k, c i j k x • ρ k x)
    (hc_jacobi : ∀ i j k m,
      vectorFieldDerivation (ρ i) (c j k m) +
        vectorFieldDerivation (ρ j) (c k i m) +
        vectorFieldDerivation (ρ k) (c i j m) +
        ∑ l, (c j k l * c i l m + c k i l * c j l m + c i j l * c k l m) = 0) :
    LieAlgebroid I F ((⟨Subtype.val, continuous_subtype_val⟩ : C(U, M)) *ᵖ V) where
  anchor := ofLocalFrameAnchor e b hU ρ
  bracket := ofLocalFrameBracket e b hU ρ c
  bracket_self := ofLocalFrameBracket_self e b hU ρ c hc_swap
  bracket_bracket := ofLocalFrameBracket_jacobi e b hU ρ c hc_swap hρ_bracket hc_jacobi
  bracket_smul_apply s t f x := by
    rw [ofLocalFrameBracket_smul_right, ContMDiffSection.coe_add, Pi.add_apply,
      ContMDiffSection.smul_apply, ContMDiffSection.smul_apply, ofLocalFrameDeriv_apply_apply]

@[simp]
theorem ofLocalFrame_anchor_apply [CompleteSpace E]
    (ρ : ι → Cₛ^∞⟮I; E, (TangentSpace I : U → Type _)⟯)
    (c : ι → ι → ι → C^∞⟮I, U; ℝ⟯)
    (hc_swap : ∀ i j k, c i j k = -c j i k)
    (hρ_bracket : ∀ i j (x : U), mlieBracket I (ρ i) (ρ j) x = ∑ k, c i j k x • ρ k x)
    (hc_jacobi : ∀ i j k m,
      vectorFieldDerivation (ρ i) (c j k m) +
        vectorFieldDerivation (ρ j) (c k i m) +
        vectorFieldDerivation (ρ k) (c i j m) +
        ∑ l, (c j k l * c i l m + c k i l * c j l m + c i j l * c k l m) = 0)
    (x : U) (v : ((⟨Subtype.val, continuous_subtype_val⟩ : C(U, M)) *ᵖ V) x) :
    dsimp% only [ContinuousMap.coe_mk]
      ((ofLocalFrame e b hU ρ c hc_swap hρ_bracket hc_jacobi).anchor x v =
        ∑ i, e.localFrameCoeff I b i (x : M) v • ρ i x) :=
  ofLocalFrameAnchor_apply e b hU ρ x v

/-- Evaluating the anchor field of `ofLocalFrame` on the `i`-th frame section recovers `ρ i`. -/
@[simp]
theorem ofLocalFrame_anchorField_openLocalFrameSection [CompleteSpace E]
    (ρ : ι → Cₛ^∞⟮I; E, (TangentSpace I : U → Type _)⟯)
    (c : ι → ι → ι → C^∞⟮I, U; ℝ⟯)
    (hc_swap : ∀ i j k, c i j k = -c j i k)
    (hρ_bracket : ∀ i j (x : U), mlieBracket I (ρ i) (ρ j) x = ∑ k, c i j k x • ρ k x)
    (hc_jacobi : ∀ i j k m,
      vectorFieldDerivation (ρ i) (c j k m) +
        vectorFieldDerivation (ρ j) (c k i m) +
        vectorFieldDerivation (ρ k) (c i j m) +
        ∑ l, (c j k l * c i l m + c k i l * c j l m + c i j l * c k l m) = 0)
    (i : ι) :
    dsimp% only [ContinuousMap.coe_mk]
      ((ofLocalFrame e b hU ρ c hc_swap hρ_bracket hc_jacobi).anchorField
        (e.openLocalFrameSection I ∞ b hU i) = ρ i) :=
  show (ofLocalFrame e b hU ρ c hc_swap hρ_bracket hc_jacobi).anchorField
      (e.openLocalFrameSection I ∞ b hU i) = ρ i by
    ext x
    rw [anchorField_apply]
    exact ofLocalFrameAnchor_localFrame e b hU ρ i x

/-- Taking the `k`-th frame coefficient of the bracket of frame sections in `ofLocalFrame` recovers
`c i j k`. -/
theorem ofLocalFrame_coeff_bracket_openLocalFrameSection [CompleteSpace E]
    (ρ : ι → Cₛ^∞⟮I; E, (TangentSpace I : U → Type _)⟯)
    (c : ι → ι → ι → C^∞⟮I, U; ℝ⟯)
    (hc_swap : ∀ i j k, c i j k = -c j i k)
    (hρ_bracket : ∀ i j (x : U), mlieBracket I (ρ i) (ρ j) x = ∑ k, c i j k x • ρ k x)
    (hc_jacobi : ∀ i j k m,
      vectorFieldDerivation (ρ i) (c j k m) +
        vectorFieldDerivation (ρ j) (c k i m) +
        vectorFieldDerivation (ρ k) (c i j m) +
        ∑ l, (c j k l * c i l m + c k i l * c j l m + c i j l * c k l m) = 0)
    (i j k : ι) :
    e.openLocalFrameCoeff I ∞ b hU k
      ((ofLocalFrame e b hU ρ c hc_swap hρ_bracket hc_jacobi).bracket
        (e.openLocalFrameSection I ∞ b hU i) (e.openLocalFrameSection I ∞ b hU j)) =
      c i j k := by
  classical
  rw [ofLocalFrame, ofLocalFrameBracket_openLocalFrameSection, map_sum]
  simp only [ContinuousMap.coe_mk, LinearMap.map_smul,
    Bundle.Trivialization.openLocalFrameCoeff_openLocalFrameSection,
    smul_eq_mul, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte]

private theorem eq_ofLocalFrame_anchor
    (ρ : ι → Cₛ^∞⟮I; E, (TangentSpace I : U → Type _)⟯)
    {B : LieAlgebroid I F ((⟨Subtype.val, continuous_subtype_val⟩ : C(U, M)) *ᵖ V)}
    (hρ : ∀ i, B.anchorField (e.openLocalFrameSection I ∞ b hU i) = ρ i)
    (x : U) (v : ((⟨Subtype.val, continuous_subtype_val⟩ : C(U, M)) *ᵖ V) x) :
    B.anchor x v = ofLocalFrameAnchor e b hU ρ x v := by
  let vM : V (x : M) := v
  have hexp := eq_sum_localFrameCoeff_smul_at I e b (hU x.2) vM
  have hv : v = ∑ i, e.localFrameCoeff I b i (x : M) vM • e.openLocalFrameSection I ∞ b hU i x :=
    hexp.trans (Finset.sum_congr rfl fun i _ ↦
      congrArg (e.localFrameCoeff I b i (x : M) vM • ·)
        (e.openLocalFrameSection_apply (I := I) (n := ∞) b hU i x).symm)
  conv_lhs => rw [hv]
  rw [map_sum, ofLocalFrameAnchor_apply]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [map_smul, ← B.anchorField_apply, hρ i]

/-- **Uniqueness of `ofLocalFrame`.** Any Lie algebroid on `V|_U` whose anchor fields and frame
bracket coefficients on `e.openLocalFrameSection` agree with `(ρ, c)` equals `ofLocalFrame`. -/
theorem eq_ofLocalFrame [CompleteSpace E]
    (ρ : ι → Cₛ^∞⟮I; E, (TangentSpace I : U → Type _)⟯)
    (c : ι → ι → ι → C^∞⟮I, U; ℝ⟯)
    (hc_swap : ∀ i j k, c i j k = -c j i k)
    (hρ_bracket : ∀ i j (x : U), mlieBracket I (ρ i) (ρ j) x = ∑ k, c i j k x • ρ k x)
    (hc_jacobi : ∀ i j k m,
      vectorFieldDerivation (ρ i) (c j k m) +
        vectorFieldDerivation (ρ j) (c k i m) +
        vectorFieldDerivation (ρ k) (c i j m) +
        ∑ l, (c j k l * c i l m + c k i l * c j l m + c i j l * c k l m) = 0)
    {B : LieAlgebroid I F ((⟨Subtype.val, continuous_subtype_val⟩ : C(U, M)) *ᵖ V)}
    (hρ : ∀ i, B.anchorField (e.openLocalFrameSection I ∞ b hU i) = ρ i)
    (hc : ∀ i j k, e.openLocalFrameCoeff I ∞ b hU k
      (B.bracket (e.openLocalFrameSection I ∞ b hU i) (e.openLocalFrameSection I ∞ b hU j)) =
        c i j k) :
    B = ofLocalFrame e b hU ρ c hc_swap hρ_bracket hc_jacobi := by
  have hB_anchor := eq_ofLocalFrame_anchor e b hU ρ hρ
  ext1
  · exact ContMDiffSection.ext fun x ↦ ContinuousLinearMap.ext (hB_anchor x)
  · ext s t : 2
    have hD (u : Cₛ^∞⟮I; F, _⟯) (f : C^∞⟮I, U; ℝ⟯) :
        B.anchorDeriv u f = ofLocalFrameDeriv e b hU ρ u f := by
      have : ContMDiffVectorBundle ∞ F
          ((⟨Subtype.val, continuous_subtype_val⟩ : C(U, M)) *ᵖ V) I :=
        ContMDiffVectorBundle.restrictOpen U
      ext x
      rw [anchorDeriv_apply, hB_anchor, ofLocalFrameDeriv_apply_apply]
    dsimp only [ofLocalFrame]
    rw [bracket_eq_sum_openLocalFrame e b hU B s t, ofLocalFrameBracket, LinearMap.mk₂_apply]
    exact Finset.sum_congr rfl fun k _ ↦ by simp only [hD, hc]

/-- Reconstructing `A.restrict U` from its `anchorFrameField` and `structureFunction` recovers
`A.restrict U`. -/
@[simp]
theorem ofLocalFrame_anchorFrameField_structureFunction [FiniteDimensional ℝ E] [T2Space M]
    (A : LieAlgebroid I F V) :
    ofLocalFrame e b hU (A.anchorFrameField e b hU) (A.structureFunction e b hU)
      (A.structureFunction_swap e b hU) (A.mlieBracket_anchorFrameField e b hU)
      (A.jacobi_structureFunction e b hU) = A.restrict U :=
  (eq_ofLocalFrame e b hU _ _ _ _ _
    (fun i ↦ (A.anchorFrameField_eq e b hU i).symm)
    (fun i j k ↦ (A.structureFunction_eq e b hU i j k).symm)).symm

end OfLocalFrame

/-! ### Gluing local-frame data over an open cover -/

section OfLocalFrameCover

variable [ContMDiffVectorBundle ∞ F V I] [CompleteSpace E]

omit [IsManifold I ∞ M] [FiniteDimensional ℝ F] [ContMDiffVectorBundle ∞ F V I]
  [CompleteSpace E] in
private theorem mvfderiv_open_congr {U₁ U₂ : Opens M} {f₁ : C^∞⟮I, U₁; ℝ⟯} {f₂ : C^∞⟮I, U₂; ℝ⟯}
    {x : M} (h₁ : x ∈ U₁) (h₂ : x ∈ U₂)
    (hf : ∀ y (hy₁ : y ∈ U₁) (hy₂ : y ∈ U₂), f₁ ⟨y, hy₁⟩ = f₂ ⟨y, hy₂⟩)
    {v₁ : TangentSpace I (⟨x, h₁⟩ : U₁)} {v₂ : TangentSpace I (⟨x, h₂⟩ : U₂)}
    (hv : Manifold.tangentSpaceOpenEquiv (I := I) ⟨x, h₁⟩ v₁ =
      Manifold.tangentSpaceOpenEquiv (I := I) ⟨x, h₂⟩ v₂) :
    mvfderiv I f₁ ⟨x, h₁⟩ v₁ = mvfderiv I f₂ ⟨x, h₂⟩ v₂ := by
  let W : Opens M := U₁ ⊓ U₂
  let z : W := ⟨x, ⟨h₁, h₂⟩⟩
  let j₁ : W → U₁ := fun y ↦ ⟨y.1, y.2.1⟩
  let j₂ : W → U₂ := fun y ↦ ⟨y.1, y.2.2⟩
  have hj₁ : CMDiff ∞ j₁ := (TauCeti.ContMDiff.subtypeVal_comp_iff U₁ j₁).mp contMDiff_subtype_val
  have hj₂ : CMDiff ∞ j₂ := (TauCeti.ContMDiff.subtypeVal_comp_iff U₂ j₂).mp contMDiff_subtype_val
  let w : TangentSpace I z :=
    (Manifold.tangentSpaceOpenEquiv (I := I) z).symm
      (Manifold.tangentSpaceOpenEquiv (I := I) ⟨x, h₁⟩ v₁)
  have hsubW := DFunLike.congr_fun (Manifold.mfderiv_subtype_val (I := I) z) w
  have hw₁ : mfderiv% j₁ z w = v₁ := by
    apply (Manifold.tangentSpaceOpenEquiv (I := I) (⟨x, h₁⟩ : U₁)).injective
    have hsub₁ := DFunLike.congr_fun
      (Manifold.mfderiv_subtype_val (I := I) (⟨x, h₁⟩ : U₁)) (mfderiv% j₁ z w)
    have hcomp₁ := DFunLike.congr_fun (mfderiv_comp z
      ((contMDiff_subtype_val (n := ∞)).mdifferentiableAt (by simp))
      (hj₁.mdifferentiableAt (by simp))) w
    exact hsub₁.symm.trans (hcomp₁.symm.trans
      (hsubW.trans ((Manifold.tangentSpaceOpenEquiv (I := I) z).apply_symm_apply _)))
  have hw₂ : mfderiv% j₂ z w = v₂ := by
    apply (Manifold.tangentSpaceOpenEquiv (I := I) (⟨x, h₂⟩ : U₂)).injective
    have hsub₂ := DFunLike.congr_fun
      (Manifold.mfderiv_subtype_val (I := I) (⟨x, h₂⟩ : U₂)) (mfderiv% j₂ z w)
    have hcomp₂ := DFunLike.congr_fun (mfderiv_comp z
      ((contMDiff_subtype_val (n := ∞)).mdifferentiableAt (by simp))
      (hj₂.mdifferentiableAt (by simp))) w
    exact hsub₂.symm.trans (hcomp₂.symm.trans (hsubW.trans
      (((Manifold.tangentSpaceOpenEquiv (I := I) z).apply_symm_apply _).trans hv)))
  have hfeq : (⇑f₁ ∘ j₁ : W → ℝ) = ⇑f₂ ∘ j₂ := funext fun y ↦ hf y.1 y.2.1 y.2.2
  have hc₁ := mvfderiv_comp_apply (I := I) (I' := I) z (g := f₁) (f := j₁)
    (f₁.contMDiff.mdifferentiableAt (by simp)) (hj₁.mdifferentiableAt (by simp)) w
  have hc₂ := mvfderiv_comp_apply (I := I) (I' := I) z (g := f₂) (f := j₂)
    (f₂.contMDiff.mdifferentiableAt (by simp)) (hj₂.mdifferentiableAt (by simp)) w
  rw [hw₁] at hc₁
  rw [hw₂, ← hfeq] at hc₂
  exact hc₁.symm.trans hc₂

omit [CompleteSpace E] in
private theorem ofLocalFrameCover_anchor_compat {α : Type*} (U : α → Opens M)
    (e : α → Trivialization F (π F V)) [∀ a, MemTrivializationAtlas (e a)]
    {ι : α → Type*} [∀ a, Fintype (ι a)] (b : ∀ a, Basis (ι a) ℝ F)
    (hU : ∀ a, (U a : Set M) ⊆ (e a).baseSet)
    (ρ : ∀ a, ι a → Cₛ^∞⟮I; E, (TangentSpace I : U a → Type _)⟯)
    (hρ_change : ∀ (a a' : α) (z : (U a ⊓ U a' : Opens M)) (i' : ι a'),
      Manifold.tangentSpaceOpenEquiv (I := I) ⟨z.1, z.2.2⟩ (ρ a' i' ⟨z.1, z.2.2⟩) =
        ∑ p : ι a,
          (e a).localFrameCoeff I (b a) p z.1 ((e a').localFrame (b a') i' z.1) •
            Manifold.tangentSpaceOpenEquiv (I := I) ⟨z.1, z.2.1⟩ (ρ a p ⟨z.1, z.2.1⟩))
    (a a' : α) (x : M) (ha : x ∈ U a) (ha' : x ∈ U a') (v : V x) :
    Manifold.tangentSpaceOpenEquiv (I := I) ⟨x, ha⟩
        (ofLocalFrameAnchor (e a) (b a) (hU a) (ρ a) ⟨x, ha⟩ v) =
      Manifold.tangentSpaceOpenEquiv (I := I) ⟨x, ha'⟩
        (ofLocalFrameAnchor (e a') (b a') (hU a') (ρ a') ⟨x, ha'⟩ v) := by
  have ha_eq : Manifold.tangentSpaceOpenEquiv (I := I) ⟨x, ha⟩
      (ofLocalFrameAnchor (e a) (b a) (hU a) (ρ a) ⟨x, ha⟩ v) =
      ∑ p, (e a).localFrameCoeff I (b a) p x v •
        Manifold.tangentSpaceOpenEquiv (I := I) ⟨x, ha⟩ (ρ a p ⟨x, ha⟩) := by
    let va : ((⟨Subtype.val, continuous_subtype_val⟩ : C(U a, M)) *ᵖ V) ⟨x, ha⟩ := v
    exact (congrArg (Manifold.tangentSpaceOpenEquiv (I := I) ⟨x, ha⟩)
      (ofLocalFrameAnchor_apply (e a) (b a) (hU a) (ρ a) ⟨x, ha⟩ va)).trans
        ((map_sum _ _ _).trans (Finset.sum_congr rfl fun p _ ↦ map_smul _ _ _))
  have ha'_eq : Manifold.tangentSpaceOpenEquiv (I := I) ⟨x, ha'⟩
      (ofLocalFrameAnchor (e a') (b a') (hU a') (ρ a') ⟨x, ha'⟩ v) =
      ∑ i', (e a').localFrameCoeff I (b a') i' x v •
        Manifold.tangentSpaceOpenEquiv (I := I) ⟨x, ha'⟩ (ρ a' i' ⟨x, ha'⟩) := by
    let va' : ((⟨Subtype.val, continuous_subtype_val⟩ : C(U a', M)) *ᵖ V) ⟨x, ha'⟩ := v
    exact (congrArg (Manifold.tangentSpaceOpenEquiv (I := I) ⟨x, ha'⟩)
      (ofLocalFrameAnchor_apply (e a') (b a') (hU a') (ρ a') ⟨x, ha'⟩ va')).trans
        ((map_sum _ _ _).trans (Finset.sum_congr rfl fun i' _ ↦ map_smul _ _ _))
  have hρ' (i' : ι a') := hρ_change a a' ⟨x, ⟨ha, ha'⟩⟩ i'
  dsimp only at hρ'
  refine ha_eq.trans (Eq.trans ?_ ha'_eq.symm)
  simp_rw [hρ', Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun p _ ↦ ?_
  rw [← Finset.sum_smul]
  congr 1
  have hexp := eq_sum_localFrameCoeff_smul_at I (e a') (b a') (hU a' ha') v
  conv_lhs => rw [hexp]
  rw [map_sum]
  exact Finset.sum_congr rfl fun i' _ ↦ map_smul ((e a).localFrameCoeff I (b a) p x) _ _

omit [IsManifold I ∞ M] [CompleteSpace E] in
private theorem ofLocalFrameCover_coeff_sum {α : Type*} (U : α → Opens M)
    (e : α → Trivialization F (π F V)) [∀ a, MemTrivializationAtlas (e a)]
    {ι : α → Type*} [∀ a, Fintype (ι a)] (b : ∀ a, Basis (ι a) ℝ F)
    (hU : ∀ a, (U a : Set M) ⊆ (e a).baseSet)
    (a a' : α) (m : ι a) (u : Cₛ^∞⟮I; F, V⟯) (y : M) (hya : y ∈ U a) (hya' : y ∈ U a') :
    (e a).openLocalFrameCoeff I ∞ (b a) (hU a) m (u.restrict (U a)) ⟨y, hya⟩ =
      ∑ r : ι a',
        (e a').openLocalFrameCoeff I ∞ (b a') (hU a') r (u.restrict (U a')) ⟨y, hya'⟩ *
          localFrameTransition I (e a) (b a) (hU a) (e a') (b a') (hU a') r m ⟨y, ⟨hya, hya'⟩⟩ := by
  have hlhs : (e a).openLocalFrameCoeff I ∞ (b a) (hU a) m (u.restrict (U a)) ⟨y, hya⟩ =
      (e a).localFrameCoeff I (b a) m y (u y) :=
    ((e a).openLocalFrameCoeff_apply (I := I) (n := ∞) (b a) (hU a) m
      (u.restrict (U a)) ⟨y, hya⟩).trans
      (congrArg ((e a).localFrameCoeff I (b a) m y) (u.restrict_apply (U a) ⟨y, hya⟩))
  rw [hlhs]
  have hexp := (e a').eq_sum_localFrameCoeff_smul (I := I) (b := b a') (s := u) (hU a' hya')
  conv_lhs => rw [hexp]
  rw [map_sum]
  refine Finset.sum_congr rfl fun r _ ↦ ?_
  rw [map_smul, smul_eq_mul, localFrameTransition_apply]
  refine congrArg (· * (e a).localFrameCoeff I (b a) m y ((e a').localFrame (b a') r y)) ?_
  exact (((e a').openLocalFrameCoeff_apply (I := I) (n := ∞) (b a') (hU a') r
    (u.restrict (U a')) ⟨y, hya'⟩).trans
      (congrArg ((e a').localFrameCoeff I (b a') r y) (u.restrict_apply (U a') ⟨y, hya'⟩))).symm

omit [CompleteSpace E] in
private theorem ofLocalFrameCover_deriv_coeff {α : Type*} (U : α → Opens M)
    (e : α → Trivialization F (π F V)) [∀ a, MemTrivializationAtlas (e a)]
    {ι : α → Type*} [∀ a, Fintype (ι a)] (b : ∀ a, Basis (ι a) ℝ F)
    (hU : ∀ a, (U a : Set M) ⊆ (e a).baseSet)
    (ρ : ∀ a, ι a → Cₛ^∞⟮I; E, (TangentSpace I : U a → Type _)⟯)
    (hρ_change : ∀ (a a' : α) (z : (U a ⊓ U a' : Opens M)) (i' : ι a'),
      Manifold.tangentSpaceOpenEquiv (I := I) ⟨z.1, z.2.2⟩ (ρ a' i' ⟨z.1, z.2.2⟩) =
        ∑ p : ι a,
          (e a).localFrameCoeff I (b a) p z.1 ((e a').localFrame (b a') i' z.1) •
            Manifold.tangentSpaceOpenEquiv (I := I) ⟨z.1, z.2.1⟩ (ρ a p ⟨z.1, z.2.1⟩))
    (a a' : α) (m : ι a) (u v : Cₛ^∞⟮I; F, V⟯) (x : M) (ha : x ∈ U a) (ha' : x ∈ U a') :
    let z : (U a ⊓ U a' : Opens M) := ⟨x, ⟨ha, ha'⟩⟩
    let g := localFrameTransition I (e a) (b a) (hU a) (e a') (b a') (hU a')
    let co' := fun r (w : Cₛ^∞⟮I; F, V⟯) ↦
      (e a').openLocalFrameCoeff I ∞ (b a') (hU a') r (w.restrict (U a'))
    ofLocalFrameDeriv (e a) (b a) (hU a) (ρ a) (u.restrict (U a))
        ((e a).openLocalFrameCoeff I ∞ (b a) (hU a) m (v.restrict (U a))) ⟨x, ha⟩ =
      ∑ r : ι a',
        (ofLocalFrameDeriv (e a') (b a') (hU a') (ρ a') (u.restrict (U a')) (co' r v) ⟨x, ha'⟩ *
            g r m z +
          co' r v ⟨x, ha'⟩ * ∑ i' : ι a', co' i' u ⟨x, ha'⟩ *
            mvfderiv I (g r m) z ((Manifold.tangentSpaceOpenEquiv (I := I) z).symm
              (Manifold.tangentSpaceOpenEquiv (I := I) ⟨x, ha'⟩ (ρ a' i' ⟨x, ha'⟩)))) := by
  intro z g co'
  let jW : C^∞⟮I, (U a ⊓ U a' : Opens M); I, U a'⟯ :=
    ⟨fun y ↦ ⟨y.1, y.2.2⟩, (TauCeti.ContMDiff.subtypeVal_comp_iff (U a')
      (fun y : (U a ⊓ U a' : Opens M) ↦ ⟨y.1, y.2.2⟩)).mp contMDiff_subtype_val⟩
  rw [ofLocalFrameDeriv_apply_apply]
  let v_a := ofLocalFrameAnchor (e a) (b a) (hU a) (ρ a) ⟨x, ha⟩ (u.restrict (U a) ⟨x, ha⟩)
  let v_a' := ofLocalFrameAnchor (e a') (b a') (hU a') (ρ a') ⟨x, ha'⟩ (u.restrict (U a') ⟨x, ha'⟩)
  let v_W : TangentSpace I z := (Manifold.tangentSpaceOpenEquiv (I := I) z).symm
    (Manifold.tangentSpaceOpenEquiv (I := I) ⟨x, ha'⟩ v_a')
  have hv_eq : Manifold.tangentSpaceOpenEquiv (I := I) ⟨x, ha⟩ v_a =
      Manifold.tangentSpaceOpenEquiv (I := I) z v_W := by
    dsimp only [v_a, v_a', v_W]
    rw [congrArg (ofLocalFrameAnchor (e a) (b a) (hU a) (ρ a) ⟨x, ha⟩) (u.restrict_apply _ _),
      ofLocalFrameCover_anchor_compat U e b hU ρ hρ_change a a' x ha ha' (u x),
      ← congrArg (ofLocalFrameAnchor (e a') (b a') (hU a') (ρ a') ⟨x, ha'⟩) (u.restrict_apply _ _)]
    exact ((Manifold.tangentSpaceOpenEquiv (I := I) z).apply_symm_apply _).symm
  have hfeq_W (y : M) (hy₁ : y ∈ U a) (hy₂ : y ∈ (U a ⊓ U a' : Opens M)) :
      (e a).openLocalFrameCoeff I ∞ (b a) (hU a) m (v.restrict (U a)) ⟨y, hy₁⟩ =
        (∑ r : ι a', (co' r v).comp jW * g r m) ⟨y, hy₂⟩ := by
    rw [ContMDiffMap.coe_sum, Finset.sum_apply]
    exact (ofLocalFrameCover_coeff_sum U e b hU a a' m v y hy₁ hy₂.2).trans rfl
  rw [mvfderiv_open_congr ha z.2 hfeq_W hv_eq, mvfderiv_sum_contMDiffMap_apply]
  refine Finset.sum_congr rfl fun r _ ↦ ?_
  have hm := congr($(mvfderiv_mul
    (((co' r v).comp jW).contMDiff.mdifferentiableAt (by simp))
    ((g r m).contMDiff.mdifferentiableAt (by simp)) (x := z)) v_W)
  simp only [_root_.add_apply, _root_.smul_apply, smul_eq_mul] at hm
  have hcomp : mvfderiv I ((co' r v).comp jW) z v_W =
      ofLocalFrameDeriv (e a') (b a') (hU a') (ρ a') (u.restrict (U a')) (co' r v) ⟨x, ha'⟩ := by
    rw [ofLocalFrameDeriv_apply_apply]
    exact mvfderiv_open_congr z.2 ha' (fun _ _ _ ↦ rfl)
      ((Manifold.tangentSpaceOpenEquiv (I := I) z).apply_symm_apply _)
  have hg_exp : mvfderiv I (g r m) z v_W = ∑ i' : ι a', co' i' u ⟨x, ha'⟩ *
      mvfderiv I (g r m) z ((Manifold.tangentSpaceOpenEquiv (I := I) z).symm
        (Manifold.tangentSpaceOpenEquiv (I := I) ⟨x, ha'⟩ (ρ a' i' ⟨x, ha'⟩))) := by
    have hvW : v_W = ∑ i' : ι a', co' i' u ⟨x, ha'⟩ •
        (Manifold.tangentSpaceOpenEquiv (I := I) z).symm
          (Manifold.tangentSpaceOpenEquiv (I := I) ⟨x, ha'⟩ (ρ a' i' ⟨x, ha'⟩)) := by
      simp only [ContinuousMap.coe_mk, v_W, v_a', ofLocalFrameAnchor_apply, map_sum, map_smul]
      exact Finset.sum_congr rfl fun i' _ ↦ congrArg (· • _)
        ((e a').openLocalFrameCoeff_apply (I := I) (n := ∞) (b a') (hU a') i'
          (u.restrict (U a')) ⟨x, ha'⟩).symm
    rw [hvW, map_sum]; exact Finset.sum_congr rfl fun _ _ ↦ by rw [map_smul, smul_eq_mul]
  rw [show mvfderiv I (⇑((co' r v).comp jW * g r m)) z v_W =
      mvfderiv I (⇑((co' r v).comp jW) * ⇑(g r m)) z v_W from rfl, hm, hcomp,
    show ((co' r v).comp jW) z = co' r v ⟨x, ha'⟩ from rfl, hg_exp]
  ring

omit [IsManifold I ∞ M] [CompleteSpace E] in
private theorem ofLocalFrameCover_quad_eq {α : Type*} (U : α → Opens M)
    (e : α → Trivialization F (π F V)) [∀ a, MemTrivializationAtlas (e a)]
    {ι : α → Type*} [∀ a, Fintype (ι a)] (b : ∀ a, Basis (ι a) ℝ F)
    (hU : ∀ a, (U a : Set M) ⊆ (e a).baseSet)
    (c : ∀ a, ι a → ι a → ι a → C^∞⟮I, U a; ℝ⟯)
    (a a' : α) (s t : Cₛ^∞⟮I; F, V⟯) (x : M) (ha : x ∈ U a) (ha' : x ∈ U a') (m : ι a) :
    let z : (U a ⊓ U a' : Opens M) := ⟨x, ⟨ha, ha'⟩⟩
    let g := localFrameTransition I (e a) (b a) (hU a) (e a') (b a') (hU a')
    let co' := fun r (u : Cₛ^∞⟮I; F, V⟯) ↦
      (e a').openLocalFrameCoeff I ∞ (b a') (hU a') r (u.restrict (U a'))
    (∑ p : ι a, ∑ q : ι a,
        (e a).openLocalFrameCoeff I ∞ (b a) (hU a) p (s.restrict (U a)) ⟨x, ha⟩ *
          (e a).openLocalFrameCoeff I ∞ (b a) (hU a) q (t.restrict (U a)) ⟨x, ha⟩ *
          c a p q m ⟨x, ha⟩) =
      ∑ i' : ι a', ∑ j' : ι a', co' i' s ⟨x, ha'⟩ * co' j' t ⟨x, ha'⟩ *
        (∑ p : ι a, ∑ q : ι a, g i' p z * g j' q z * c a p q m ⟨x, ha⟩) := by
  intro z g co'
  have hs (p : ι a) :
      (e a).openLocalFrameCoeff I ∞ (b a) (hU a) p (s.restrict (U a)) ⟨x, ha⟩ =
        ∑ i' : ι a', co' i' s ⟨x, ha'⟩ * g i' p z :=
    ofLocalFrameCover_coeff_sum U e b hU a a' p s x ha ha'
  have ht (q : ι a) :
      (e a).openLocalFrameCoeff I ∞ (b a) (hU a) q (t.restrict (U a)) ⟨x, ha⟩ =
        ∑ j' : ι a', co' j' t ⟨x, ha'⟩ * g j' q z :=
    ofLocalFrameCover_coeff_sum U e b hU a a' q t x ha ha'
  have hquad (u' v' : ι a' → ℝ) (G : ι a' → ι a → ℝ) (C : ι a → ι a → ℝ) :
      (∑ p : ι a, ∑ q : ι a,
          (∑ i' : ι a', u' i' * G i' p) * (∑ j' : ι a', v' j' * G j' q) * C p q) =
        ∑ i' : ι a', ∑ j' : ι a', u' i' * v' j' *
          (∑ p : ι a, ∑ q : ι a, G i' p * G j' q * C p q) := by
    have step1 (p q : ι a) :
        (∑ i' : ι a', u' i' * G i' p) * (∑ j' : ι a', v' j' * G j' q) * C p q =
          ∑ i' : ι a', ∑ j' : ι a', u' i' * v' j' * (G i' p * G j' q * C p q) := by
      rw [Finset.sum_mul, Finset.sum_mul]
      refine Finset.sum_congr rfl fun i' _ ↦ ?_
      rw [Finset.mul_sum, Finset.sum_mul]
      exact Finset.sum_congr rfl fun j' _ ↦ by ring
    refine (Finset.sum_congr rfl fun p _ ↦ Finset.sum_congr rfl fun q _ ↦ step1 p q).trans ?_
    refine (Finset.sum_congr rfl fun p _ ↦ Finset.sum_comm).trans (Finset.sum_comm.trans ?_)
    refine Finset.sum_congr rfl fun i' _ ↦
      (Finset.sum_congr rfl fun p _ ↦ Finset.sum_comm).trans (Finset.sum_comm.trans ?_)
    exact Finset.sum_congr rfl fun j' _ ↦ by simp only [Finset.mul_sum]
  refine (Finset.sum_congr rfl fun p _ ↦ Finset.sum_congr rfl fun q _ ↦ ?_).trans
    (hquad (fun i' ↦ co' i' s ⟨x, ha'⟩) (fun j' ↦ co' j' t ⟨x, ha'⟩)
      (fun r k ↦ g r k z) (fun p q ↦ c a p q m ⟨x, ha⟩))
  rw [hs p, ht q]

omit [CompleteSpace E] in
private theorem ofLocalFrameCover_bracket_rhs {α : Type*} (U : α → Opens M)
    (e : α → Trivialization F (π F V)) [∀ a, MemTrivializationAtlas (e a)]
    {ι : α → Type*} [∀ a, Fintype (ι a)] (b : ∀ a, Basis (ι a) ℝ F)
    (hU : ∀ a, (U a : Set M) ⊆ (e a).baseSet)
    (ρ : ∀ a, ι a → Cₛ^∞⟮I; E, (TangentSpace I : U a → Type _)⟯)
    (c : ∀ a, ι a → ι a → ι a → C^∞⟮I, U a; ℝ⟯)
    (a a' : α) (s t : Cₛ^∞⟮I; F, V⟯) (x : M) (ha : x ∈ U a) (ha' : x ∈ U a') (m : ι a) :
    let z : (U a ⊓ U a' : Opens M) := ⟨x, ⟨ha, ha'⟩⟩
    let g := localFrameTransition I (e a) (b a) (hU a) (e a') (b a') (hU a')
    let co' := fun r (u : Cₛ^∞⟮I; F, V⟯) ↦
      (e a').openLocalFrameCoeff I ∞ (b a') (hU a') r (u.restrict (U a'))
    (e a).localFrameCoeff I (b a) m x
        (ofLocalFrameBracket (e a') (b a') (hU a') (ρ a') (c a')
          (s.restrict (U a')) (t.restrict (U a')) ⟨x, ha'⟩) =
      ∑ k' : ι a', (ofLocalFrameDeriv (e a') (b a') (hU a') (ρ a') (s.restrict (U a'))
          (co' k' t) ⟨x, ha'⟩ -
        ofLocalFrameDeriv (e a') (b a') (hU a') (ρ a') (t.restrict (U a'))
          (co' k' s) ⟨x, ha'⟩ +
        ∑ i' : ι a', ∑ j' : ι a', co' i' s ⟨x, ha'⟩ * co' j' t ⟨x, ha'⟩ *
          c a' i' j' k' ⟨x, ha'⟩) * g k' m z := by
  intro z g co'
  let br' := ofLocalFrameBracket (e a') (b a') (hU a') (ρ a') (c a')
    (s.restrict (U a')) (t.restrict (U a'))
  have hexp' := congrArg (fun u ↦ u ⟨x, ha'⟩)
    ((e a').eq_sum_openLocalFrameCoeff_smul (b a') (hU a') br')
  let ιV := ContMDiffSection.coeAddHom I F ∞
    ((⟨Subtype.val, continuous_subtype_val⟩ : C(U a', M)) *ᵖ V)
  have hsum' := congrFun (map_sum ιV
    (fun k' ↦ (e a').openLocalFrameCoeff I ∞ (b a') (hU a') k' br' •
      (e a').openLocalFrameSection I ∞ (b a') (hU a') k') Finset.univ) ⟨x, ha'⟩
  simp only [ιV, ContMDiffSection.coeAddHom_apply, Finset.sum_apply,
    ContMDiffSection.smul_apply] at hsum'
  have hval : (br' ⟨x, ha'⟩ : V x) = ∑ k' : ι a',
      (e a').openLocalFrameCoeff I ∞ (b a') (hU a') k' br' ⟨x, ha'⟩ •
        (e a').localFrame (b a') k' x := by
    refine (hexp'.trans hsum').trans (Finset.sum_congr rfl fun k' _ ↦ ?_)
    exact congrArg (_ • ·)
      ((e a').openLocalFrameSection_apply (I := I) (n := ∞) (b a') (hU a') k' ⟨x, ha'⟩)
  rw [hval, map_sum]
  refine Finset.sum_congr rfl fun k' _ ↦ ?_
  rw [map_smul, smul_eq_mul, ofLocalFrameBracket_coeff]
  simp only [g, z, co', localFrameTransition_apply, ContMDiffMap.coe_add, ContMDiffMap.coe_sub,
    ContMDiffMap.coe_sum, ContMDiffMap.coe_mul, Pi.add_apply, Pi.sub_apply, Finset.sum_apply,
    Pi.mul_apply]

omit [CompleteSpace E] in
private theorem ofLocalFrameCover_bracket_coeff_eq {α : Type*} (U : α → Opens M)
    (e : α → Trivialization F (π F V)) [∀ a, MemTrivializationAtlas (e a)]
    {ι : α → Type*} [∀ a, Fintype (ι a)] (b : ∀ a, Basis (ι a) ℝ F)
    (hU : ∀ a, (U a : Set M) ⊆ (e a).baseSet)
    (ρ : ∀ a, ι a → Cₛ^∞⟮I; E, (TangentSpace I : U a → Type _)⟯)
    (c : ∀ a, ι a → ι a → ι a → C^∞⟮I, U a; ℝ⟯)
    (hρ_change : ∀ (a a' : α) (z : (U a ⊓ U a' : Opens M)) (i' : ι a'),
      Manifold.tangentSpaceOpenEquiv (I := I) ⟨z.1, z.2.2⟩ (ρ a' i' ⟨z.1, z.2.2⟩) =
        ∑ p : ι a,
          (e a).localFrameCoeff I (b a) p z.1 ((e a').localFrame (b a') i' z.1) •
            Manifold.tangentSpaceOpenEquiv (I := I) ⟨z.1, z.2.1⟩ (ρ a p ⟨z.1, z.2.1⟩))
    (hc_change : ∀ (a a' : α) (z : (U a ⊓ U a' : Opens M)) (i' j' : ι a') (m : ι a),
      let g := localFrameTransition I (e a) (b a) (hU a) (e a') (b a') (hU a')
      ∑ k' : ι a', c a' i' j' k' ⟨z.1, z.2.2⟩ * g k' m z =
        mvfderiv I (g j' m) z
            ((Manifold.tangentSpaceOpenEquiv (I := I) z).symm
              (Manifold.tangentSpaceOpenEquiv (I := I) ⟨z.1, z.2.2⟩ (ρ a' i' ⟨z.1, z.2.2⟩))) -
          mvfderiv I (g i' m) z
            ((Manifold.tangentSpaceOpenEquiv (I := I) z).symm
              (Manifold.tangentSpaceOpenEquiv (I := I) ⟨z.1, z.2.2⟩ (ρ a' j' ⟨z.1, z.2.2⟩))) +
          ∑ p : ι a, ∑ q : ι a, g i' p z * g j' q z * c a p q m ⟨z.1, z.2.1⟩)
    (a a' : α) (s t : Cₛ^∞⟮I; F, V⟯) (x : M) (ha : x ∈ U a) (ha' : x ∈ U a') (m : ι a) :
    (e a).localFrameCoeff I (b a) m x
        (ofLocalFrameBracket (e a) (b a) (hU a) (ρ a) (c a)
          (s.restrict (U a)) (t.restrict (U a)) ⟨x, ha⟩) =
      (e a).localFrameCoeff I (b a) m x
        (ofLocalFrameBracket (e a') (b a') (hU a') (ρ a') (c a')
          (s.restrict (U a')) (t.restrict (U a')) ⟨x, ha'⟩) := by
  let z : (U a ⊓ U a' : Opens M) := ⟨x, ⟨ha, ha'⟩⟩
  let g := localFrameTransition I (e a) (b a) (hU a) (e a') (b a') (hU a')
  let co' := fun r (u : Cₛ^∞⟮I; F, V⟯) ↦
    (e a').openLocalFrameCoeff I ∞ (b a') (hU a') r (u.restrict (U a'))
  let dg (r i' : ι a') : ℝ := mvfderiv I (g r m) z
    ((Manifold.tangentSpaceOpenEquiv (I := I) z).symm
      (Manifold.tangentSpaceOpenEquiv (I := I) ⟨x, ha'⟩ (ρ a' i' ⟨x, ha'⟩)))
  have lhs := congrFun (congrArg DFunLike.coe
    (ofLocalFrameBracket_coeff (e a) (b a) (hU a) (ρ a) (c a)
      (s.restrict (U a)) (t.restrict (U a)) m)) ⟨x, ha⟩
  rw [Bundle.Trivialization.openLocalFrameCoeff_apply] at lhs
  simp only [ContMDiffMap.coe_add, ContMDiffMap.coe_sub, ContMDiffMap.coe_sum,
    ContMDiffMap.coe_mul, Pi.add_apply, Pi.sub_apply, Finset.sum_apply, Pi.mul_apply] at lhs
  have hd₁ : ∑ r : ι a', co' r t ⟨x, ha'⟩ * (∑ i' : ι a', co' i' s ⟨x, ha'⟩ * dg r i') =
      ∑ i' : ι a', ∑ j' : ι a', co' i' s ⟨x, ha'⟩ * co' j' t ⟨x, ha'⟩ * dg j' i' := by
    simp_rw [Finset.mul_sum]; rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun _ _ ↦ Finset.sum_congr rfl fun _ _ ↦ by ring
  have hd₂ : ∑ r : ι a', co' r s ⟨x, ha'⟩ * (∑ j' : ι a', co' j' t ⟨x, ha'⟩ * dg r j') =
      ∑ i' : ι a', ∑ j' : ι a', co' i' s ⟨x, ha'⟩ * co' j' t ⟨x, ha'⟩ * dg i' j' := by
    simp_rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun _ _ ↦ Finset.sum_congr rfl fun _ _ ↦ by ring
  have hc' (i' j' : ι a') : ∑ k' : ι a', c a' i' j' k' ⟨x, ha'⟩ * g k' m z =
      dg j' i' - dg i' j' + ∑ p : ι a, ∑ q : ι a, g i' p z * g j' q z * c a p q m ⟨x, ha⟩ :=
    hc_change a a' z i' j' m
  have hc_sum : ∑ k' : ι a', (∑ i' : ι a', ∑ j' : ι a', co' i' s ⟨x, ha'⟩ * co' j' t ⟨x, ha'⟩ *
        c a' i' j' k' ⟨x, ha'⟩) * g k' m z =
      (∑ i' : ι a', ∑ j' : ι a', co' i' s ⟨x, ha'⟩ * co' j' t ⟨x, ha'⟩ * dg j' i') -
        (∑ i' : ι a', ∑ j' : ι a', co' i' s ⟨x, ha'⟩ * co' j' t ⟨x, ha'⟩ * dg i' j') +
        ∑ i' : ι a', ∑ j' : ι a', co' i' s ⟨x, ha'⟩ * co' j' t ⟨x, ha'⟩ *
          (∑ p : ι a, ∑ q : ι a, g i' p z * g j' q z * c a p q m ⟨x, ha⟩) := by
    trans ∑ i' : ι a', ∑ j' : ι a', co' i' s ⟨x, ha'⟩ * co' j' t ⟨x, ha'⟩ *
        (∑ k' : ι a', c a' i' j' k' ⟨x, ha'⟩ * g k' m z)
    · simp_rw [Finset.sum_mul, Finset.mul_sum]; rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun i' _ ↦ Finset.sum_comm.trans ?_
      exact Finset.sum_congr rfl fun j' _ ↦ Finset.sum_congr rfl fun k' _ ↦ by ring
    · simp_rw [hc', mul_add, mul_sub, Finset.sum_add_distrib, Finset.sum_sub_distrib]
  rw [lhs, ofLocalFrameCover_deriv_coeff U e b hU ρ hρ_change a a' m s t x ha ha',
    ofLocalFrameCover_deriv_coeff U e b hU ρ hρ_change a a' m t s x ha ha',
    ofLocalFrameCover_quad_eq U e b hU c a a' s t x ha ha' m,
    ofLocalFrameCover_bracket_rhs U e b hU ρ c a a' s t x ha ha' m]
  dsimp only [z, g, co', dg] at hd₁ hd₂ hc_sum
  simp only [Finset.sum_add_distrib, add_mul, sub_mul, Finset.sum_sub_distrib]
  rw [hd₁, hd₂, hc_sum]
  ring

omit [CompleteSpace E] in
private theorem ofLocalFrameCover_bracket_compat {α : Type*} (U : α → Opens M)
    (e : α → Trivialization F (π F V)) [∀ a, MemTrivializationAtlas (e a)]
    {ι : α → Type*} [∀ a, Fintype (ι a)] (b : ∀ a, Basis (ι a) ℝ F)
    (hU : ∀ a, (U a : Set M) ⊆ (e a).baseSet)
    (ρ : ∀ a, ι a → Cₛ^∞⟮I; E, (TangentSpace I : U a → Type _)⟯)
    (c : ∀ a, ι a → ι a → ι a → C^∞⟮I, U a; ℝ⟯)
    (hρ_change : ∀ (a a' : α) (z : (U a ⊓ U a' : Opens M)) (i' : ι a'),
      Manifold.tangentSpaceOpenEquiv (I := I) ⟨z.1, z.2.2⟩ (ρ a' i' ⟨z.1, z.2.2⟩) =
        ∑ p : ι a,
          (e a).localFrameCoeff I (b a) p z.1 ((e a').localFrame (b a') i' z.1) •
            Manifold.tangentSpaceOpenEquiv (I := I) ⟨z.1, z.2.1⟩ (ρ a p ⟨z.1, z.2.1⟩))
    (hc_change : ∀ (a a' : α) (z : (U a ⊓ U a' : Opens M)) (i' j' : ι a') (m : ι a),
      let g := localFrameTransition I (e a) (b a) (hU a) (e a') (b a') (hU a')
      ∑ k' : ι a', c a' i' j' k' ⟨z.1, z.2.2⟩ * g k' m z =
        mvfderiv I (g j' m) z
            ((Manifold.tangentSpaceOpenEquiv (I := I) z).symm
              (Manifold.tangentSpaceOpenEquiv (I := I) ⟨z.1, z.2.2⟩ (ρ a' i' ⟨z.1, z.2.2⟩))) -
          mvfderiv I (g i' m) z
            ((Manifold.tangentSpaceOpenEquiv (I := I) z).symm
              (Manifold.tangentSpaceOpenEquiv (I := I) ⟨z.1, z.2.2⟩ (ρ a' j' ⟨z.1, z.2.2⟩))) +
          ∑ p : ι a, ∑ q : ι a, g i' p z * g j' q z * c a p q m ⟨z.1, z.2.1⟩)
    (a a' : α) (s t : Cₛ^∞⟮I; F, V⟯) (x : M) (ha : x ∈ U a) (ha' : x ∈ U a') :
    ofLocalFrameBracket (e a) (b a) (hU a) (ρ a) (c a)
        (s.restrict (U a)) (t.restrict (U a)) ⟨x, ha⟩ =
      ofLocalFrameBracket (e a') (b a') (hU a') (ρ a') (c a')
        (s.restrict (U a')) (t.restrict (U a')) ⟨x, ha'⟩ := by
  let v₁ : V x := ofLocalFrameBracket (e a) (b a) (hU a) (ρ a) (c a)
    (s.restrict (U a)) (t.restrict (U a)) ⟨x, ha⟩
  let v₂ : V x := ofLocalFrameBracket (e a') (b a') (hU a') (ρ a') (c a')
    (s.restrict (U a')) (t.restrict (U a')) ⟨x, ha'⟩
  have he₁ := eq_sum_localFrameCoeff_smul_at I (e a) (b a) (hU a ha) v₁
  have he₂ := eq_sum_localFrameCoeff_smul_at I (e a) (b a) (hU a ha) v₂
  refine he₁.trans ((Finset.sum_congr rfl fun m _ ↦ ?_).trans he₂.symm)
  exact congrArg (· • (e a).localFrame (b a) m x)
    (ofLocalFrameCover_bracket_coeff_eq U e b hU ρ c hρ_change hc_change a a' s t x ha ha' m)

/-- **Gluing local-frame Lie algebroid data over an open cover.** Given an open cover `U a` of `M`
with trivializations `e a` (`U a ⊆ (e a).baseSet`), model bases `b a`, anchor vector fields `ρ a`
and structure functions `c a` satisfying skew-symmetry, anchor-bracket, and Jacobi on each `U a`,
together with the anchor and structure-function transformation laws on overlaps `U a ⊓ U a'`, there
is a global Lie algebroid on `V` gluing the local Lie algebroids `ofLocalFrame`. -/
def ofLocalFrameCover {α : Type*} (U : α → Opens M) (hcover : ∀ x : M, ∃ a, x ∈ U a)
    (e : α → Trivialization F (π F V)) [∀ a, MemTrivializationAtlas (e a)]
    {ι : α → Type*} [∀ a, Fintype (ι a)] (b : ∀ a, Basis (ι a) ℝ F)
    (hU : ∀ a, (U a : Set M) ⊆ (e a).baseSet)
    (ρ : ∀ a, ι a → Cₛ^∞⟮I; E, (TangentSpace I : U a → Type _)⟯)
    (c : ∀ a, ι a → ι a → ι a → C^∞⟮I, U a; ℝ⟯)
    (hc_swap : ∀ a i j k, c a i j k = -c a j i k)
    (hρ_bracket : ∀ a i j (x : U a), mlieBracket I (ρ a i) (ρ a j) x = ∑ k, c a i j k x • ρ a k x)
    (hc_jacobi : ∀ a i j k m,
      vectorFieldDerivation (ρ a i) (c a j k m) +
        vectorFieldDerivation (ρ a j) (c a k i m) +
        vectorFieldDerivation (ρ a k) (c a i j m) +
        ∑ l, (c a j k l * c a i l m + c a k i l * c a j l m + c a i j l * c a k l m) = 0)
    (hρ_change : ∀ (a a' : α) (z : (U a ⊓ U a' : Opens M)) (i' : ι a'),
      Manifold.tangentSpaceOpenEquiv (I := I) ⟨z.1, z.2.2⟩ (ρ a' i' ⟨z.1, z.2.2⟩) =
        ∑ p : ι a,
          (e a).localFrameCoeff I (b a) p z.1 ((e a').localFrame (b a') i' z.1) •
            Manifold.tangentSpaceOpenEquiv (I := I) ⟨z.1, z.2.1⟩ (ρ a p ⟨z.1, z.2.1⟩))
    (hc_change : ∀ (a a' : α) (z : (U a ⊓ U a' : Opens M)) (i' j' : ι a') (m : ι a),
      let g := localFrameTransition I (e a) (b a) (hU a) (e a') (b a') (hU a')
      ∑ k' : ι a', c a' i' j' k' ⟨z.1, z.2.2⟩ * g k' m z =
        mvfderiv I (g j' m) z
            ((Manifold.tangentSpaceOpenEquiv (I := I) z).symm
              (Manifold.tangentSpaceOpenEquiv (I := I) ⟨z.1, z.2.2⟩ (ρ a' i' ⟨z.1, z.2.2⟩))) -
          mvfderiv I (g i' m) z
            ((Manifold.tangentSpaceOpenEquiv (I := I) z).symm
              (Manifold.tangentSpaceOpenEquiv (I := I) ⟨z.1, z.2.2⟩ (ρ a' j' ⟨z.1, z.2.2⟩))) +
          ∑ p : ι a, ∑ q : ι a, g i' p z * g j' q z * c a p q m ⟨z.1, z.2.1⟩) :
    LieAlgebroid I F V :=
  glueOpenCover U hcover
    (fun a ↦ ofLocalFrame (e a) (b a) (hU a) (ρ a) (c a)
      (hc_swap a) (hρ_bracket a) (hc_jacobi a))
    (ofLocalFrameCover_anchor_compat U e b hU ρ hρ_change)
    (ofLocalFrameCover_bracket_compat U e b hU ρ c hρ_change hc_change)

/-- Restricting `ofLocalFrameCover` to `U a` recovers `ofLocalFrame` on `U a`. -/
@[simp]
theorem ofLocalFrameCover_restrict [FiniteDimensional ℝ E] [T2Space M]
    {α : Type*} (U : α → Opens M) (hcover : ∀ x : M, ∃ a, x ∈ U a)
    (e : α → Trivialization F (π F V)) [∀ a, MemTrivializationAtlas (e a)]
    {ι : α → Type*} [∀ a, Fintype (ι a)] (b : ∀ a, Basis (ι a) ℝ F)
    (hU : ∀ a, (U a : Set M) ⊆ (e a).baseSet)
    (ρ : ∀ a, ι a → Cₛ^∞⟮I; E, (TangentSpace I : U a → Type _)⟯)
    (c : ∀ a, ι a → ι a → ι a → C^∞⟮I, U a; ℝ⟯)
    (hc_swap : ∀ a i j k, c a i j k = -c a j i k)
    (hρ_bracket : ∀ a i j (x : U a), mlieBracket I (ρ a i) (ρ a j) x = ∑ k, c a i j k x • ρ a k x)
    (hc_jacobi : ∀ a i j k m,
      vectorFieldDerivation (ρ a i) (c a j k m) +
        vectorFieldDerivation (ρ a j) (c a k i m) +
        vectorFieldDerivation (ρ a k) (c a i j m) +
        ∑ l, (c a j k l * c a i l m + c a k i l * c a j l m + c a i j l * c a k l m) = 0)
    (hρ_change : ∀ (a a' : α) (z : (U a ⊓ U a' : Opens M)) (i' : ι a'),
      Manifold.tangentSpaceOpenEquiv (I := I) ⟨z.1, z.2.2⟩ (ρ a' i' ⟨z.1, z.2.2⟩) =
        ∑ p : ι a,
          (e a).localFrameCoeff I (b a) p z.1 ((e a').localFrame (b a') i' z.1) •
            Manifold.tangentSpaceOpenEquiv (I := I) ⟨z.1, z.2.1⟩ (ρ a p ⟨z.1, z.2.1⟩))
    (hc_change : ∀ (a a' : α) (z : (U a ⊓ U a' : Opens M)) (i' j' : ι a') (m : ι a),
      let g := localFrameTransition I (e a) (b a) (hU a) (e a') (b a') (hU a')
      ∑ k' : ι a', c a' i' j' k' ⟨z.1, z.2.2⟩ * g k' m z =
        mvfderiv I (g j' m) z
            ((Manifold.tangentSpaceOpenEquiv (I := I) z).symm
              (Manifold.tangentSpaceOpenEquiv (I := I) ⟨z.1, z.2.2⟩ (ρ a' i' ⟨z.1, z.2.2⟩))) -
          mvfderiv I (g i' m) z
            ((Manifold.tangentSpaceOpenEquiv (I := I) z).symm
              (Manifold.tangentSpaceOpenEquiv (I := I) ⟨z.1, z.2.2⟩ (ρ a' j' ⟨z.1, z.2.2⟩))) +
          ∑ p : ι a, ∑ q : ι a, g i' p z * g j' q z * c a p q m ⟨z.1, z.2.1⟩)
    (a : α) :
    (ofLocalFrameCover U hcover e b hU ρ c hc_swap hρ_bracket hc_jacobi
      hρ_change hc_change).restrict (U a) =
      ofLocalFrame (e a) (b a) (hU a) (ρ a) (c a) (hc_swap a) (hρ_bracket a) (hc_jacobi a) :=
  glueOpenCover_restrict U hcover _ _ _ a

/-- **Uniqueness of `ofLocalFrameCover`.** Any global Lie algebroid whose anchor fields and
structure functions on every `U a` agree with `(ρ a, c a)` equals `ofLocalFrameCover`. -/
theorem eq_ofLocalFrameCover [FiniteDimensional ℝ E] [T2Space M]
    {α : Type*} (U : α → Opens M) (hcover : ∀ x : M, ∃ a, x ∈ U a)
    (e : α → Trivialization F (π F V)) [∀ a, MemTrivializationAtlas (e a)]
    {ι : α → Type*} [∀ a, Fintype (ι a)] (b : ∀ a, Basis (ι a) ℝ F)
    (hU : ∀ a, (U a : Set M) ⊆ (e a).baseSet)
    (ρ : ∀ a, ι a → Cₛ^∞⟮I; E, (TangentSpace I : U a → Type _)⟯)
    (c : ∀ a, ι a → ι a → ι a → C^∞⟮I, U a; ℝ⟯)
    (hc_swap : ∀ a i j k, c a i j k = -c a j i k)
    (hρ_bracket : ∀ a i j (x : U a), mlieBracket I (ρ a i) (ρ a j) x = ∑ k, c a i j k x • ρ a k x)
    (hc_jacobi : ∀ a i j k m,
      vectorFieldDerivation (ρ a i) (c a j k m) +
        vectorFieldDerivation (ρ a j) (c a k i m) +
        vectorFieldDerivation (ρ a k) (c a i j m) +
        ∑ l, (c a j k l * c a i l m + c a k i l * c a j l m + c a i j l * c a k l m) = 0)
    (hρ_change : ∀ (a a' : α) (z : (U a ⊓ U a' : Opens M)) (i' : ι a'),
      Manifold.tangentSpaceOpenEquiv (I := I) ⟨z.1, z.2.2⟩ (ρ a' i' ⟨z.1, z.2.2⟩) =
        ∑ p : ι a,
          (e a).localFrameCoeff I (b a) p z.1 ((e a').localFrame (b a') i' z.1) •
            Manifold.tangentSpaceOpenEquiv (I := I) ⟨z.1, z.2.1⟩ (ρ a p ⟨z.1, z.2.1⟩))
    (hc_change : ∀ (a a' : α) (z : (U a ⊓ U a' : Opens M)) (i' j' : ι a') (m : ι a),
      let g := localFrameTransition I (e a) (b a) (hU a) (e a') (b a') (hU a')
      ∑ k' : ι a', c a' i' j' k' ⟨z.1, z.2.2⟩ * g k' m z =
        mvfderiv I (g j' m) z
            ((Manifold.tangentSpaceOpenEquiv (I := I) z).symm
              (Manifold.tangentSpaceOpenEquiv (I := I) ⟨z.1, z.2.2⟩ (ρ a' i' ⟨z.1, z.2.2⟩))) -
          mvfderiv I (g i' m) z
            ((Manifold.tangentSpaceOpenEquiv (I := I) z).symm
              (Manifold.tangentSpaceOpenEquiv (I := I) ⟨z.1, z.2.2⟩ (ρ a' j' ⟨z.1, z.2.2⟩))) +
          ∑ p : ι a, ∑ q : ι a, g i' p z * g j' q z * c a p q m ⟨z.1, z.2.1⟩)
    {A : LieAlgebroid I F V}
    (hρ : ∀ a i, A.anchorFrameField (e a) (b a) (hU a) i = ρ a i)
    (hc : ∀ a i j k, A.structureFunction (e a) (b a) (hU a) i j k = c a i j k) :
    A = ofLocalFrameCover U hcover e b hU ρ c hc_swap hρ_bracket hc_jacobi hρ_change hc_change :=
  eq_glueOpenCover U hcover _ _ _ fun a ↦
    eq_ofLocalFrame (e a) (b a) (hU a) (ρ a) (c a) (hc_swap a) (hρ_bracket a) (hc_jacobi a)
      (fun i ↦ (A.anchorFrameField_eq (e a) (b a) (hU a) i).symm.trans (hρ a i))
      (fun i j k ↦ (A.structureFunction_eq (e a) (b a) (hU a) i j k).symm.trans (hc a i j k))

end OfLocalFrameCover

end LieAlgebroid

end TauCeti
