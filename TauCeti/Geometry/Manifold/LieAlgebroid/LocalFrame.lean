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

Over `U : Opens M` in `e.baseSet` for an atlas trivialization `e` of a finite-rank smooth real
vector bundle `V → M` and basis `b : Basis ι ℝ F`, smooth vector fields `ρ i` and skew-symmetric
`c i j k` satisfying `[ρ i, ρ j] = ∑ k, c i j k • ρ k` and the Jacobi structure equation determine a
unique Lie algebroid `ofLocalFrame` on `V|_U` (`ofLocalFrameAnchor`, `eq_ofLocalFrame`,
`ofLocalFrame_anchorFrameField_structureFunction`), and glue across open covers to
`ofLocalFrameCover` (`ofLocalFrameCover_restrict`, `eq_ofLocalFrameCover`; Mackenzie 2005, §3.3).
-/

public noncomputable section

open Bundle Manifold Module TopologicalSpace VectorField
open scoped ContDiff Topology

namespace TauCeti.LieAlgebroid

private theorem mvfderiv_sum_contMDiffMap_apply {E H : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {N : Type*} [TopologicalSpace N] [ChartedSpace H N]
    {γ : Type*} (S : Finset γ) (f : γ → C^∞⟮I, N; ℝ⟯) (z : N) (w : TangentSpace I z) :
    mvfderiv I (∑ r ∈ S, f r : C^∞⟮I, N; ℝ⟯) z w = ∑ r ∈ S, mvfderiv I (f r) z w := by
  classical
  induction S using Finset.induction_on with
  | empty => simp only [Finset.sum_empty, ContMDiffMap.coe_zero, mvfderiv_zero, _root_.zero_apply]
  | insert r₀ S hr₀ ih =>
    simp only [Finset.sum_insert hr₀]
    rw [show (⇑(f r₀ + ∑ r ∈ S, f r) : N → ℝ) = ⇑(f r₀) + ⇑(∑ r ∈ S, f r) from rfl,
      mvfderiv_add ((f r₀).contMDiff.mdifferentiableAt (by simp))
        ((∑ r ∈ S, f r).contMDiff.mdifferentiableAt (by simp)), _root_.add_apply, ih]

private theorem derivation_commutator_smul_right {R : Type*} [CommRing R] [Algebra ℝ R]
    (D₁ D₂ : Derivation ℝ R R) (f : R) : ⁅D₁, f • D₂⁆ = f • ⁅D₁, D₂⁆ + (D₁ f) • D₂ := by
  ext g
  simp only [Derivation.commutator_apply, _root_.add_apply, _root_.smul_apply, smul_eq_mul,
    Derivation.leibniz]; ring

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M]

local notation "τOpen" => Manifold.tangentSpaceOpenEquiv (I := I)

omit [IsManifold I ∞ M] in
private theorem mvfderiv_open_congr {U₁ U₂ : Opens M} {f₁ : C^∞⟮I, U₁; ℝ⟯} {f₂ : C^∞⟮I, U₂; ℝ⟯}
    {x : M} (h₁ : x ∈ U₁) (h₂ : x ∈ U₂)
    (hf : ∀ y (hy₁ : y ∈ U₁) (hy₂ : y ∈ U₂), f₁ ⟨y, hy₁⟩ = f₂ ⟨y, hy₂⟩)
    {v₁ : TangentSpace I (⟨x, h₁⟩ : U₁)} {v₂ : TangentSpace I (⟨x, h₂⟩ : U₂)}
    (hv : τOpen ⟨x, h₁⟩ v₁ = τOpen ⟨x, h₂⟩ v₂) :
    mvfderiv I f₁ ⟨x, h₁⟩ v₁ = mvfderiv I f₂ ⟨x, h₂⟩ v₂ := by
  let W : Opens M := U₁ ⊓ U₂; let z : W := ⟨x, ⟨h₁, h₂⟩⟩
  let j₁ : W → U₁ := fun y ↦ ⟨y.1, y.2.1⟩; let j₂ : W → U₂ := fun y ↦ ⟨y.1, y.2.2⟩
  have hj₁ : CMDiff ∞ j₁ := (TauCeti.ContMDiff.subtypeVal_comp_iff U₁ j₁).mp contMDiff_subtype_val
  have hj₂ : CMDiff ∞ j₂ := (TauCeti.ContMDiff.subtypeVal_comp_iff U₂ j₂).mp contMDiff_subtype_val
  let w : TangentSpace I z := (τOpen z).symm (τOpen ⟨x, h₁⟩ v₁)
  have hsubW := DFunLike.congr_fun (Manifold.mfderiv_subtype_val (I := I) z) w
  have hw₁ : mfderiv% j₁ z w = v₁ := (τOpen (⟨x, h₁⟩ : U₁)).injective <|
    (DFunLike.congr_fun (Manifold.mfderiv_subtype_val (I := I) (⟨x, h₁⟩ : U₁)) _).symm.trans <|
      (DFunLike.congr_fun (mfderiv_comp z ((contMDiff_subtype_val (n := ∞)).mdifferentiableAt
        (by simp)) (hj₁.mdifferentiableAt (by simp))) w).symm.trans <|
        hsubW.trans ((τOpen z).apply_symm_apply _)
  have hw₂ : mfderiv% j₂ z w = v₂ := (τOpen (⟨x, h₂⟩ : U₂)).injective <|
    (DFunLike.congr_fun (Manifold.mfderiv_subtype_val (I := I) (⟨x, h₂⟩ : U₂)) _).symm.trans <|
      (DFunLike.congr_fun (mfderiv_comp z ((contMDiff_subtype_val (n := ∞)).mdifferentiableAt
        (by simp)) (hj₂.mdifferentiableAt (by simp))) w).symm.trans <|
        hsubW.trans (((τOpen z).apply_symm_apply _).trans hv)
  have hc₁ := mvfderiv_comp_apply (I := I) (I' := I) z (g := f₁) (f := j₁)
    (f₁.contMDiff.mdifferentiableAt (by simp)) (hj₁.mdifferentiableAt (by simp)) w
  have hc₂ := mvfderiv_comp_apply (I := I) (I' := I) z (g := f₂) (f := j₂)
    (f₂.contMDiff.mdifferentiableAt (by simp)) (hj₂.mdifferentiableAt (by simp)) w
  rw [hw₁] at hc₁
  rw [hw₂, ← show (⇑f₁ ∘ j₁ : W → ℝ) = ⇑f₂ ∘ j₂ from funext fun y ↦ hf y.1 y.2.1 y.2.2] at hc₂
  exact hc₁.symm.trans hc₂

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {V : M → Type*} [TopologicalSpace (TotalSpace F V)] [∀ x, AddCommGroup (V x)]
  [∀ x, Module ℝ (V x)] [∀ x, TopologicalSpace (V x)] [FiberBundle F V] [VectorBundle ℝ F V]
  [ContMDiffVectorBundle ∞ F V I]

local notation "V|[" U "]" => ((ContinuousMap.mk Subtype.val continuous_subtype_val : C(U, M)) *ᵖ V)

omit [IsManifold I ∞ M] [FiniteDimensional ℝ F] in
variable (I) in
private theorem localFrameCoeff_eq_coord (e : Trivialization F (π F V)) [MemTrivializationAtlas e]
    {ι : Type*} (b : Basis ι ℝ F) {x : M} (hx : x ∈ e.baseSet) (v : V x) (i : ι) :
    e.localFrameCoeff I b i x v = b.coord i (e.continuousLinearMapAt ℝ x v) := by
  have h := e.localFrameCoeff_eq_coeff (I := I) (b := b) (s := FiberBundle.extend F v) hx (i := i)
  have hv : FiberBundle.extend F v x = v := by simp
  rwa [hv, show (T% (FiberBundle.extend F v)) x = ⟨x, v⟩ from congrArg (TotalSpace.mk' F x) hv,
    ← e.continuousLinearMapAt_apply_of_mem (R := ℝ) hx v, ← b.coord_apply] at h

omit [IsManifold I ∞ M] [FiniteDimensional ℝ F] in
variable (I) in
private theorem eq_sum_localFrameCoeff_smul_at (e : Trivialization F (π F V))
    [MemTrivializationAtlas e] {ι : Type*} [Fintype ι] (b : Basis ι ℝ F) {x : M}
    (hx : x ∈ e.baseSet) (v : V x) : v = ∑ i, e.localFrameCoeff I b i x v • e.localFrame b i x := by
  simpa only [FiberBundle.extend_apply_self] using
    e.eq_sum_localFrameCoeff_smul (I := I) (b := b) (s := FiberBundle.extend F v) hx

section OfLocalFrame
variable (e : Trivialization F (π F V)) [MemTrivializationAtlas e]
  {ι : Type*} [Fintype ι] (b : Basis ι ℝ F) {U : Opens M} (hU : (U : Set M) ⊆ e.baseSet)
local notation "frSection" => e.openLocalFrameSection I ∞ b hU
local notation "frCoeff" => e.openLocalFrameCoeff I ∞ b hU
include e b hU
variable (ρ : ι → Cₛ^∞⟮I; E, (TangentSpace I : U → Type _)⟯) (c : ι → ι → ι → C^∞⟮I, U; ℝ⟯)

private def ofLocalFrameAnchorTerm (i : ι) :
    Cₛ^∞⟮I; F →L[ℝ] E, fun x : U ↦ (V|[U] x) →L[ℝ] TangentSpace I x⟯ where
  toFun x := ((LinearMap.toContinuousLinearMap (b.coord i)).comp
    (e.continuousLinearMapAt ℝ (x : M))).smulRight (ρ i x)
  contMDiff_toFun := by
    let ιU : C(U, M) := ⟨Subtype.val, continuous_subtype_val⟩
    have hcoord : ContMDiff (I.prod 𝓘(ℝ, F)) 𝓘(ℝ, F) ∞
        (fun p : TotalSpace F (ιU *ᵖ V) ↦ (e (Pullback.lift ιU p)).2) :=
      ((e.contMDiff_iff fun p ↦ e.mem_source.2 (hU p.proj.2)).1
        (Bundle.Pullback.contMDiff_lift ιU contMDiff_subtype_val)).2
    have ha := ((LinearMap.toContinuousLinearMap (b.coord i)).contMDiff.comp hcoord).congr fun p ↦
      congrArg (b.coord i)
        (e.continuousLinearMapAt_apply_of_mem (R := ℝ) (hU p.proj.2) (p.2 : V (p.proj : M)))
    exact (TauCeti.contMDiff_hom_bundle_iff (E₁ := (ιU *ᵖ V)) _).2
      (ha.smul_totalSpace ((ρ i).contMDiff.comp (Bundle.contMDiff_proj (ιU *ᵖ V))))

/-- The smooth anchor bundle map on `V|_U` sending the `i`-th local-frame vector to `ρ i`. -/
def ofLocalFrameAnchor : Cₛ^∞⟮I; F →L[ℝ] E, fun x : U ↦ (V|[U] x) →L[ℝ] TangentSpace I x⟯ :=
  ∑ i, ofLocalFrameAnchorTerm e b hU ρ i

@[simp] theorem ofLocalFrameAnchor_apply (x : U) (v : V|[U] x) :
    dsimp% only [ContinuousMap.coe_mk]
      (ofLocalFrameAnchor e b hU ρ x v = ∑ i, e.localFrameCoeff I b i (x : M) v • ρ i x) := by
  have hsum := congrFun (map_sum (ContMDiffSection.coeAddHom I (F →L[ℝ] E) ∞
    (fun y : U ↦ (V|[U] y) →L[ℝ] TangentSpace I y))
      (fun i ↦ ofLocalFrameAnchorTerm e b hU ρ i) Finset.univ) x
  simp only [ContMDiffSection.coeAddHom_apply, Finset.sum_apply] at hsum
  rw [ofLocalFrameAnchor, hsum, _root_.sum_apply]; exact Finset.sum_congr rfl fun i _ ↦
    congrArg (· • ρ i x) (localFrameCoeff_eq_coord I e b (hU x.2) (v : V (x : M)) i).symm

theorem ofLocalFrameAnchor_localFrame (i : ι) (x : U) :
    ofLocalFrameAnchor e b hU ρ x (frSection i x) = ρ i x := by
  classical
  rw [ofLocalFrameAnchor_apply]
  have h (j : ι) : e.localFrameCoeff I b j (x : M) (frSection i x) = if j = i then 1 else 0 := by
    rw [e.openLocalFrameSection_apply, TauCeti.Manifold.localFrameCoeff_localFrame b (hU x.2)]
  simp only [h, ite_smul, one_smul, zero_smul, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]

private def ofLocalFrameDeriv :
    Cₛ^∞⟮I; F, V|[U]⟯ →ₗ[C^∞⟮I, U; ℝ⟯] Derivation ℝ C^∞⟮I, U; ℝ⟯ C^∞⟮I, U; ℝ⟯ where
  toFun s := ∑ i, frCoeff i s • vectorFieldDerivation (ρ i)
  map_add' _ _ := by simp only [map_add, add_smul, Finset.sum_add_distrib]
  map_smul' _ _ := by
    simp only [LinearMap.map_smul, RingHom.id_apply, Finset.smul_sum, smul_smul, smul_eq_mul]

private theorem ofLocalFrameDeriv_apply_apply (s : Cₛ^∞⟮I; F, V|[U]⟯) (f : C^∞⟮I, U; ℝ⟯) (x : U) :
    ofLocalFrameDeriv e b hU ρ s f x = mvfderiv I f x (ofLocalFrameAnchor e b hU ρ x (s x)) := by
  rw [ofLocalFrameDeriv, LinearMap.coe_mk, AddHom.coe_mk, _root_.sum_apply, ContMDiffMap.coe_sum,
    Finset.sum_apply, ofLocalFrameAnchor_apply, map_sum]
  exact Finset.sum_congr rfl fun _ _ ↦ by
    rw [_root_.smul_apply, smul_eq_mul, ContMDiffMap.coe_mul, Pi.mul_apply,
      e.openLocalFrameCoeff_apply, ContMDiffSection.vectorFieldDerivation_apply_apply,
      map_smul, smul_eq_mul]

private theorem ofLocalFrameDeriv_openLocalFrameSection (i : ι) :
    ofLocalFrameDeriv e b hU ρ (frSection i) = vectorFieldDerivation (ρ i) := by
  classical
  simp [ContinuousMap.coe_mk, ofLocalFrameDeriv,
    Bundle.Trivialization.openLocalFrameCoeff_openLocalFrameSection]

private def ofLocalFrameBracket :
    Cₛ^∞⟮I; F, V|[U]⟯ →ₗ[ℝ] Cₛ^∞⟮I; F, V|[U]⟯ →ₗ[ℝ] Cₛ^∞⟮I; F, V|[U]⟯ :=
  let D := ofLocalFrameDeriv e b hU ρ
  LinearMap.mk₂ ℝ
    (fun s t ↦ ∑ k, (D s (frCoeff k t) - D t (frCoeff k s) +
      ∑ i, ∑ j, frCoeff i s * frCoeff j t * c i j k) • frSection k)
    (fun _ _ _ ↦ by rw [← Finset.sum_add_distrib]; refine Finset.sum_congr rfl fun k _ ↦ ?_; (
      rw [← add_smul]; congr 1
      simp only [map_add, _root_.add_apply, add_mul, Finset.sum_add_distrib]; abel))
    (fun r s _ ↦ by rw [Finset.smul_sum]; refine Finset.sum_congr rfl fun k _ ↦ ?_; (
      have hco (m : ι) := LinearMapClass.map_smul_of_tower (frCoeff m) r s
      have hD := LinearMapClass.map_smul_of_tower D r s
      rw [← smul_assoc r _ (frSection k)]; congr 1
      simp only [hD, hco, _root_.smul_apply, Derivation.map_smul, smul_mul_assoc, smul_sub,
        smul_add, Finset.smul_sum]))
    (fun _ _ _ ↦ by rw [← Finset.sum_add_distrib]; refine Finset.sum_congr rfl fun k _ ↦ ?_; (
      rw [← add_smul]; congr 1
      simp only [map_add, _root_.add_apply, mul_add, add_mul, Finset.sum_add_distrib]; abel))
    (fun r _ t ↦ by rw [Finset.smul_sum]; refine Finset.sum_congr rfl fun k _ ↦ ?_; (
      have hco (m : ι) := LinearMapClass.map_smul_of_tower (frCoeff m) r t
      have hD := LinearMapClass.map_smul_of_tower D r t
      rw [← smul_assoc r _ (frSection k)]; congr 1
      simp only [hD, hco, _root_.smul_apply, Derivation.map_smul, mul_smul_comm, smul_mul_assoc,
        smul_sub, smul_add, Finset.smul_sum]))

private theorem ofLocalFrameBracket_coeff (s t : Cₛ^∞⟮I; F, V|[U]⟯) (m : ι) :
    frCoeff m (ofLocalFrameBracket e b hU ρ c s t) =
      ofLocalFrameDeriv e b hU ρ s (frCoeff m t) - ofLocalFrameDeriv e b hU ρ t (frCoeff m s) +
        ∑ i, ∑ j, frCoeff i s * frCoeff j t * c i j m := by
  classical
  rw [ofLocalFrameBracket, LinearMap.mk₂_apply, map_sum]
  simp [ContinuousMap.coe_mk, Bundle.Trivialization.openLocalFrameCoeff_openLocalFrameSection,
    Finset.sum_ite_eq]

private theorem ofLocalFrameBracket_openLocalFrameSection (i j : ι) :
    ofLocalFrameBracket e b hU ρ c (frSection i) (frSection j) = ∑ k, c i j k • frSection k := by
  classical
  rw [ofLocalFrameBracket, LinearMap.mk₂_apply]
  refine Finset.sum_congr rfl fun k _ ↦ congrArg (· • _) ?_
  have hconst (D : Derivation ℝ C^∞⟮I, U; ℝ⟯ C^∞⟮I, U; ℝ⟯) (p q : ι) :
      D (frCoeff p (frSection q)) = 0 := by
    rw [Bundle.Trivialization.openLocalFrameCoeff_openLocalFrameSection]
    split_ifs; exacts [D.map_one_eq_zero, D.map_zero]
  rw [hconst, hconst, sub_self, zero_add]; dsimp only [ContinuousMap.coe_mk]
  simp_rw [Bundle.Trivialization.openLocalFrameCoeff_openLocalFrameSection, mul_assoc,
    ite_mul, one_mul, zero_mul]
  have hinner (p : ι) : (∑ q, if p = i then if q = j then c p q k else 0 else 0) =
      if p = i then c p j k else 0 := by split_ifs <;> simp
  simp [hinner]

private theorem ofLocalFrameBracket_swap (hc_swap : ∀ i j k, c i j k = -c j i k)
    (s t : Cₛ^∞⟮I; F, V|[U]⟯) :
    ofLocalFrameBracket e b hU ρ c s t = -ofLocalFrameBracket e b hU ρ c t s := by
  rw [ofLocalFrameBracket, LinearMap.mk₂_apply, LinearMap.mk₂_apply, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  rw [← neg_smul]; congr 1
  have hsum : (∑ i, ∑ j, frCoeff i s * frCoeff j t * c i j k) =
      -(∑ i, ∑ j, frCoeff i t * frCoeff j s * c i j k) := by
    conv_lhs => rw [Finset.sum_comm]
    simp_rw [← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ by rw [hc_swap j i k]; ring
  rw [hsum]; ring

private theorem ofLocalFrameBracket_self (hc_swap : ∀ i j k, c i j k = -c j i k)
    (s : Cₛ^∞⟮I; F, V|[U]⟯) : ofLocalFrameBracket e b hU ρ c s s = 0 := by
  rw [← inv_smul_smul₀ (two_ne_zero : (2 : ℝ) ≠ 0) (ofLocalFrameBracket e b hU ρ c s s),
    two_smul, add_eq_zero_iff_eq_neg.2 (ofLocalFrameBracket_swap e b hU ρ c hc_swap s s), smul_zero]

private theorem ofLocalFrameBracket_smul_right (s t : Cₛ^∞⟮I; F, V|[U]⟯) (f : C^∞⟮I, U; ℝ⟯) :
    ofLocalFrameBracket e b hU ρ c s (f • t) =
      f • ofLocalFrameBracket e b hU ρ c s t + ofLocalFrameDeriv e b hU ρ s f • t := by
  let D := ofLocalFrameDeriv e b hU ρ
  have hterm : ofLocalFrameBracket e b hU ρ c s (f • t) =
      ∑ k, (f * (D s (frCoeff k t) - D t (frCoeff k s) +
        ∑ i, ∑ j, frCoeff i s * frCoeff j t * c i j k) + D s f * frCoeff k t) • frSection k := by
    rw [ofLocalFrameBracket, LinearMap.mk₂_apply]
    refine Finset.sum_congr rfl fun k _ ↦ congrArg (· • frSection k) ?_
    simp only [LinearMap.map_smul, smul_eq_mul, Derivation.leibniz, _root_.smul_apply]
    have hmul : (∑ i, ∑ j, frCoeff i s * (f * frCoeff j t) * c i j k) =
        f * ∑ i, ∑ j, frCoeff i s * frCoeff j t * c i j k := by
      simp_rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun _ _ ↦ Finset.sum_congr rfl fun _ _ ↦ by ring
    rw [hmul]; ring
  rw [hterm]; simp_rw [add_smul, mul_smul]; rw [Finset.sum_add_distrib]
  exact congrArg₂ (· + ·) (by rw [ofLocalFrameBracket, LinearMap.mk₂_apply, Finset.smul_sum])
    (by rw [← Finset.smul_sum, ← e.eq_sum_openLocalFrameCoeff_smul b hU t])

omit [IsManifold I ∞ M] [Fintype ι] in
private theorem eq_zero_of_openLocalFrame [Finite ι] {N : Type*} [AddCommGroup N]
    [Module C^∞⟮I, U; ℝ⟯ N] (Φ : Cₛ^∞⟮I; F, V|[U]⟯ → N) (hadd : ∀ x y, Φ (x + y) = Φ x + Φ y)
    (hsmul : ∀ (f : C^∞⟮I, U; ℝ⟯) x, Φ (f • x) = f • Φ x)
    (hfr : ∀ i, Φ (frSection i) = 0) (s : Cₛ^∞⟮I; F, V|[U]⟯) : Φ s = 0 := by
  cases nonempty_fintype ι; conv_lhs => rw [e.eq_sum_openLocalFrameCoeff_smul b hU s]
  refine (map_sum (AddMonoidHom.mk' Φ hadd) _ _).trans (Finset.sum_eq_zero fun i _ ↦ ?_)
  rw [AddMonoidHom.mk'_apply, hsmul, hfr i, smul_zero]

section BuildAlgebroid
variable [CompleteSpace E] (hc_swap : ∀ i j k, c i j k = -c j i k)
  (hρ_bracket : ∀ i j (x : U), mlieBracket I (ρ i) (ρ j) x = ∑ k, c i j k x • ρ k x)
  (hc_jacobi : ∀ i j k m,
    vectorFieldDerivation (ρ i) (c j k m) + vectorFieldDerivation (ρ j) (c k i m) +
      vectorFieldDerivation (ρ k) (c i j m) +
      ∑ l, (c j k l * c i l m + c k i l * c j l m + c i j l * c k l m) = 0)

include hc_swap hρ_bracket in
private theorem ofLocalFrameDeriv_bracket (s t : Cₛ^∞⟮I; F, V|[U]⟯) :
    ofLocalFrameDeriv e b hU ρ (ofLocalFrameBracket e b hU ρ c s t) =
      ⁅ofLocalFrameDeriv e b hU ρ s, ofLocalFrameDeriv e b hU ρ t⁆ := by
  have : IsManifold I (minSmoothness ℝ 2) U := IsManifold.of_le (n := ∞) (by simp)
  let D := ofLocalFrameDeriv e b hU ρ; let B := ofLocalFrameBracket e b hU ρ c
  let Δ (u v : Cₛ^∞⟮I; F, V|[U]⟯) : Derivation ℝ C^∞⟮I, U; ℝ⟯ C^∞⟮I, U; ℝ⟯ := ⁅D u, D v⁆ - D (B u v)
  have hΔ_r (u v : Cₛ^∞⟮I; F, V|[U]⟯) (f : C^∞⟮I, U; ℝ⟯) : Δ u (f • v) = f • Δ u v := by
    dsimp only [Δ, B]; rw [D.map_smul f v, derivation_commutator_smul_right,
      ofLocalFrameBracket_smul_right e b hU ρ c u v f, map_add, D.map_smul, D.map_smul, smul_sub]
    abel
  have hΔ_swap (u v : Cₛ^∞⟮I; F, V|[U]⟯) : Δ u v = -Δ v u := by
    dsimp only [Δ, B]; rw [← lie_skew (D u) (D v),
      ofLocalFrameBracket_swap e b hU ρ c hc_swap u v, map_neg]; abel
  have hΔ_l (f : C^∞⟮I, U; ℝ⟯) (u v : Cₛ^∞⟮I; F, V|[U]⟯) : Δ (f • u) v = f • Δ u v := by
    rw [hΔ_swap (f • u) v, hΔ_r v u f, hΔ_swap v u]; ext g; simp [smul_eq_mul]
  suffices h0 : Δ s t = 0 from (sub_eq_zero.1 h0).symm
  refine eq_zero_of_openLocalFrame e b hU (fun u ↦ Δ u t)
    (fun _ _ ↦ by ext g; simp only [Δ, map_add, LinearMap.add_apply, _root_.sub_apply,
      _root_.add_apply, Derivation.commutator_apply]; abel_nf)
    (fun f u ↦ hΔ_l f u t) (fun i ↦ eq_zero_of_openLocalFrame e b hU (Δ (frSection i))
      (fun _ _ ↦ by ext g; simp only [Δ, map_add, _root_.sub_apply, _root_.add_apply,
        Derivation.commutator_apply]; abel_nf)
      (fun f v ↦ hΔ_r _ v f) (fun j ↦ ?_) t) s
  ext f x; dsimp only [Δ, D, B]
  simp only [ofLocalFrameDeriv_openLocalFrameSection, ofLocalFrameBracket_openLocalFrameSection,
    map_sum, LinearMap.map_smul, _root_.sub_apply, Derivation.commutator_apply, _root_.zero_apply,
    ContMDiffMap.coe_sub, ContMDiffMap.coe_zero, Pi.sub_apply, Pi.zero_apply, sub_eq_zero,
    _root_.sum_apply, _root_.smul_apply, smul_eq_mul, ContMDiffMap.coe_sum, Finset.sum_apply]
  have hmlie := _root_.mvfderiv_mlieBracket (I := I) (x := x) (f.contMDiff.contMDiffAt) (by simp)
    ((ρ i).contMDiff.mdifferentiableAt (by simp)) ((ρ j).contMDiff.mdifferentiableAt (by simp))
  rw [hρ_bracket i j x, map_sum] at hmlie
  have hvf (k : ι) : ⇑(vectorFieldDerivation (ρ k) f) = fun y ↦ mvfderiv I f y (ρ k y) :=
    funext fun y ↦ ContMDiffSection.vectorFieldDerivation_apply_apply (ρ k) f y
  rw [ContMDiffSection.vectorFieldDerivation_apply_apply,
    ContMDiffSection.vectorFieldDerivation_apply_apply, hvf j, hvf i, ← hmlie]
  exact Finset.sum_congr rfl fun _ _ ↦ by rw [map_smul, smul_eq_mul, ContMDiffMap.coe_mul,
    Pi.mul_apply, ContMDiffSection.vectorFieldDerivation_apply_apply]

omit [CompleteSpace E] in
include hc_jacobi in
private theorem ofLocalFrameJacobi_frame (i j k : ι) :
    let B := ofLocalFrameBracket e b hU ρ c
    B (frSection i) (B (frSection j) (frSection k)) +
      B (frSection j) (B (frSection k) (frSection i)) +
      B (frSection k) (B (frSection i) (frSection j)) = 0 := by
  classical
  intro B; have hterm (p q r : ι) : B (frSection p) (B (frSection q) (frSection r)) =
      ∑ m, (vectorFieldDerivation (ρ p) (c q r m) + ∑ l, c q r l * c p l m) • frSection m := by
    dsimp only [B]; rw [ofLocalFrameBracket_openLocalFrameSection, map_sum]
    simp_rw [ofLocalFrameBracket_smul_right, ofLocalFrameDeriv_openLocalFrameSection,
      ofLocalFrameBracket_openLocalFrameSection, Finset.smul_sum, ← mul_smul]
    rw [Finset.sum_add_distrib, Finset.sum_comm, add_comm]
    simp_rw [add_smul]; rw [Finset.sum_add_distrib]
    exact congrArg (_ + ·) (Finset.sum_congr rfl fun _ _ ↦ Finset.sum_smul.symm)
  rw [hterm i j k, hterm j k i, hterm k i j, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_eq_zero fun m _ ↦ ?_; rw [← add_smul, ← add_smul]
  have hsum : (∑ l, c j k l * c i l m) + (∑ l, c k i l * c j l m) + (∑ l, c i j l * c k l m) =
      ∑ l, (c j k l * c i l m + c k i l * c j l m + c i j l * c k l m) := by
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
  rw [show (vectorFieldDerivation (ρ i) (c j k m) + ∑ l, c j k l * c i l m) +
    (vectorFieldDerivation (ρ j) (c k i m) + ∑ l, c k i l * c j l m) +
    (vectorFieldDerivation (ρ k) (c i j m) + ∑ l, c i j l * c k l m) = 0 by
      linear_combination hc_jacobi i j k m + hsum, zero_smul]

include hc_swap hρ_bracket hc_jacobi in
private theorem ofLocalFrameBracket_jacobi (s t u : Cₛ^∞⟮I; F, V|[U]⟯) :
    ofLocalFrameBracket e b hU ρ c s (ofLocalFrameBracket e b hU ρ c t u) =
      ofLocalFrameBracket e b hU ρ c (ofLocalFrameBracket e b hU ρ c s t) u +
        ofLocalFrameBracket e b hU ρ c t (ofLocalFrameBracket e b hU ρ c s u) := by
  let B := ofLocalFrameBracket e b hU ρ c; let D := ofLocalFrameDeriv e b hU ρ
  let J (x y z : Cₛ^∞⟮I; F, V|[U]⟯) := B x (B y z) + B y (B z x) + B z (B x y)
  have hJ_cyc (x y z : Cₛ^∞⟮I; F, V|[U]⟯) : J x y z = J y z x := by simp only [J]; abel
  have hJ_smul₃ (x y z : Cₛ^∞⟮I; F, V|[U]⟯) (f : C^∞⟮I, U; ℝ⟯) : J x y (f • z) = f • J x y z := by
    have h1 : B x (B y (f • z)) =
        f • B x (B y z) + D x f • B y z + D y f • B x z + D x (D y f) • z := by
      dsimp only [B, D]; rw [ofLocalFrameBracket_smul_right, map_add,
        ofLocalFrameBracket_smul_right, ofLocalFrameBracket_smul_right]; abel
    have h2 : B y (B (f • z) x) =
        f • B y (B z x) - D y f • B x z - D x f • B y z - D y (D x f) • z := by
      dsimp only [B, D]; rw [ofLocalFrameBracket_swap e b hU ρ c hc_swap (f • z) x, map_neg,
        ofLocalFrameBracket_smul_right, map_add, ofLocalFrameBracket_smul_right,
        ofLocalFrameBracket_smul_right, ofLocalFrameBracket_swap e b hU ρ c hc_swap x z,
        map_neg, smul_neg]; abel
    have h3 : B (f • z) (B x y) = f • B z (B x y) - D (B x y) f • z := by
      dsimp only [B, D]; rw [ofLocalFrameBracket_swap e b hU ρ c hc_swap (f • z) _,
        ofLocalFrameBracket_smul_right, ofLocalFrameBracket_swap e b hU ρ c hc_swap _ z,
        smul_neg]; abel
    have hDB : D (B x y) f = D x (D y f) - D y (D x f) := by
      simpa [Derivation.commutator_apply] using
        congr($(ofLocalFrameDeriv_bracket e b hU ρ c hc_swap hρ_bracket x y) f)
    dsimp only [J]; rw [h1, h2, h3, hDB, sub_smul, smul_add, smul_add]; abel
  have hJ_smul₁ (f : C^∞⟮I, U; ℝ⟯) (x y z : Cₛ^∞⟮I; F, V|[U]⟯) : J (f • x) y z = f • J x y z := by
    rw [hJ_cyc (f • x) y z, hJ_smul₃, ← hJ_cyc x y z]
  have hJ_smul₂ (f : C^∞⟮I, U; ℝ⟯) (x y z : Cₛ^∞⟮I; F, V|[U]⟯) : J x (f • y) z = f • J x y z := by
    rw [hJ_cyc x (f • y) z, hJ_smul₁, ← hJ_cyc x y z]
  have hJ0 : J s t u = 0 :=
    eq_zero_of_openLocalFrame e b hU (fun x ↦ J x t u)
      (fun _ _ ↦ by simp only [J, map_add, LinearMap.add_apply]; abel) (fun f x ↦ hJ_smul₁ f x t u)
      (fun i ↦ eq_zero_of_openLocalFrame e b hU (fun y ↦ J _ y u)
        (fun _ _ ↦ by simp only [J, map_add, LinearMap.add_apply]; abel)
        (fun f y ↦ hJ_smul₂ f _ y u) (fun j ↦ eq_zero_of_openLocalFrame e b hU (J _ _)
          (fun _ _ ↦ by simp only [J, map_add, LinearMap.add_apply]; abel)
          (fun f z ↦ hJ_smul₃ _ _ z f)
          (fun k ↦ ofLocalFrameJacobi_frame e b hU ρ c hc_jacobi i j k) u) t) s
  dsimp only [J, B] at hJ0
  rw [ofLocalFrameBracket_swap e b hU ρ c hc_swap u s, map_neg,
    ofLocalFrameBracket_swap e b hU ρ c hc_swap u _] at hJ0
  rw [← sub_eq_zero, ← hJ0]; abel

/-- **Converse local-frame construction of a Lie algebroid** on `V|_U` from `(ρ, c)`. -/
def ofLocalFrame : LieAlgebroid I F V|[U] where
  anchor := ofLocalFrameAnchor e b hU ρ
  bracket := ofLocalFrameBracket e b hU ρ c
  bracket_self := ofLocalFrameBracket_self e b hU ρ c hc_swap
  bracket_bracket := ofLocalFrameBracket_jacobi e b hU ρ c hc_swap hρ_bracket hc_jacobi
  bracket_smul_apply s t f x := by
    rw [ofLocalFrameBracket_smul_right, ContMDiffSection.coe_add, Pi.add_apply,
      ContMDiffSection.smul_apply, ContMDiffSection.smul_apply, ofLocalFrameDeriv_apply_apply]

@[simp] theorem ofLocalFrame_anchor_apply (x : U) (v : V|[U] x) :
    dsimp% only [ContinuousMap.coe_mk]
      ((ofLocalFrame e b hU ρ c hc_swap hρ_bracket hc_jacobi).anchor x v =
        ∑ i, e.localFrameCoeff I b i (x : M) v • ρ i x) := by
  exact ofLocalFrameAnchor_apply e b hU ρ x v

@[simp] theorem ofLocalFrame_anchorField_openLocalFrameSection (i : ι) :
    dsimp% only [ContinuousMap.coe_mk]
      ((ofLocalFrame e b hU ρ c hc_swap hρ_bracket hc_jacobi).anchorField (frSection i) = ρ i) :=
  show (ofLocalFrame e b hU ρ c hc_swap hρ_bracket hc_jacobi).anchorField (frSection i) = ρ i by
    ext x; rw [anchorField_apply]; exact ofLocalFrameAnchor_localFrame e b hU ρ i x

theorem ofLocalFrame_coeff_bracket_openLocalFrameSection (i j k : ι) :
    frCoeff k ((ofLocalFrame e b hU ρ c hc_swap hρ_bracket hc_jacobi).bracket
      (frSection i) (frSection j)) = c i j k := by
  classical
  rw [ofLocalFrame, ofLocalFrameBracket_openLocalFrameSection, map_sum]
  simp [ContinuousMap.coe_mk, Bundle.Trivialization.openLocalFrameCoeff_openLocalFrameSection,
    Finset.sum_ite_eq]

/-- **Uniqueness of `ofLocalFrame`.** -/
theorem eq_ofLocalFrame {B : LieAlgebroid I F V|[U]}
    (hρ : ∀ i, B.anchorField (frSection i) = ρ i)
    (hc : ∀ i j k, frCoeff k (B.bracket (frSection i) (frSection j)) = c i j k) :
    B = ofLocalFrame e b hU ρ c hc_swap hρ_bracket hc_jacobi := by
  have hB_anchor (x : U) (v : V|[U] x) : B.anchor x v = ofLocalFrameAnchor e b hU ρ x v := by
    let vM : V (x : M) := v
    have hv : v = ∑ i, e.localFrameCoeff I b i (x : M) vM • frSection i x :=
      (eq_sum_localFrameCoeff_smul_at I e b (hU x.2) vM).trans (Finset.sum_congr rfl fun i _ ↦
        congrArg (e.localFrameCoeff I b i (x : M) vM • ·)
          (e.openLocalFrameSection_apply (I := I) (n := ∞) b hU i x).symm)
    conv_lhs => rw [hv]
    rw [map_sum, ofLocalFrameAnchor_apply]
    exact Finset.sum_congr rfl fun i _ ↦ by rw [map_smul, ← B.anchorField_apply, hρ i]
  refine LieAlgebroid.ext (ContMDiffSection.ext fun x ↦ ContinuousLinearMap.ext (hB_anchor x))
    (LinearMap.ext₂ fun s t ↦ ?_)
  have : ContMDiffVectorBundle ∞ F V|[U] I := ContMDiffVectorBundle.restrictOpen U
  have hD (u : Cₛ^∞⟮I; F, V|[U]⟯) (f : C^∞⟮I, U; ℝ⟯) :
      B.anchorDeriv u f = ofLocalFrameDeriv e b hU ρ u f := by
    ext x; rw [anchorDeriv_apply, hB_anchor, ofLocalFrameDeriv_apply_apply]
  dsimp only [ofLocalFrame]; rw [bracket_eq_sum_openLocalFrame e b hU B s t, ofLocalFrameBracket,
    LinearMap.mk₂_apply]; exact Finset.sum_congr rfl fun _ _ ↦ by simp only [hD, hc]
end BuildAlgebroid

/-- Reconstructing `A.restrict U` from its `anchorFrameField` and `structureFunction`. -/
@[simp] theorem ofLocalFrame_anchorFrameField_structureFunction [FiniteDimensional ℝ E] [T2Space M]
    (A : LieAlgebroid I F V) :
    ofLocalFrame e b hU (A.anchorFrameField e b hU) (A.structureFunction e b hU)
      (A.structureFunction_swap e b hU) (A.mlieBracket_anchorFrameField e b hU)
      (A.jacobi_structureFunction e b hU) = A.restrict U :=
  (eq_ofLocalFrame e b hU _ _ _ _ _ (fun i ↦ (A.anchorFrameField_eq e b hU i).symm)
    (fun i j k ↦ (A.structureFunction_eq e b hU i j k).symm)).symm
end OfLocalFrame

section OfLocalFrameCover
variable {α : Type*} (U : α → Opens M) (hcover : ∀ x : M, ∃ a, x ∈ U a)
  (e : α → Trivialization F (π F V)) [∀ a, MemTrivializationAtlas (e a)]
  {ι : α → Type*} [∀ a, Fintype (ι a)] (b : ∀ a, Basis (ι a) ℝ F)
  (hU : ∀ a, (U a : Set M) ⊆ (e a).baseSet)
  (ρ : ∀ a, ι a → Cₛ^∞⟮I; E, (TangentSpace I : U a → Type _)⟯)
  (c : ∀ a, ι a → ι a → ι a → C^∞⟮I, U a; ℝ⟯)
  (hc_swap : ∀ a i j k, c a i j k = -c a j i k)
  (hρ_bracket : ∀ a i j (x : U a), mlieBracket I (ρ a i) (ρ a j) x = ∑ k, c a i j k x • ρ a k x)
  (hc_jacobi : ∀ a i j k m,
    vectorFieldDerivation (ρ a i) (c a j k m) + vectorFieldDerivation (ρ a j) (c a k i m) +
      vectorFieldDerivation (ρ a k) (c a i j m) +
      ∑ l, (c a j k l * c a i l m + c a k i l * c a j l m + c a i j l * c a k l m) = 0)
  (hρ_change : ∀ (a a' : α) (z : (U a ⊓ U a' : Opens M)) (i' : ι a'),
    Manifold.tangentSpaceOpenEquiv (I := I) ⟨z.1, z.2.2⟩ (ρ a' i' ⟨z.1, z.2.2⟩) =
      ∑ p : ι a, (e a).localFrameCoeff I (b a) p z.1 ((e a').localFrame (b a') i' z.1) •
        Manifold.tangentSpaceOpenEquiv (I := I) ⟨z.1, z.2.1⟩ (ρ a p ⟨z.1, z.2.1⟩))
  (hc_change : ∀ (a a' : α) (z : (U a ⊓ U a' : Opens M)) (i' j' : ι a') (m : ι a),
    let g := localFrameTransition I (e a) (b a) (hU a) (e a') (b a') (hU a')
    ∑ k' : ι a', c a' i' j' k' ⟨z.1, z.2.2⟩ * g k' m z =
      mvfderiv I (g j' m) z ((Manifold.tangentSpaceOpenEquiv (I := I) z).symm
        (Manifold.tangentSpaceOpenEquiv (I := I) ⟨z.1, z.2.2⟩ (ρ a' i' ⟨z.1, z.2.2⟩))) -
      mvfderiv I (g i' m) z ((Manifold.tangentSpaceOpenEquiv (I := I) z).symm
        (Manifold.tangentSpaceOpenEquiv (I := I) ⟨z.1, z.2.2⟩ (ρ a' j' ⟨z.1, z.2.2⟩))) +
        ∑ p : ι a, ∑ q : ι a, g i' p z * g j' q z * c a p q m ⟨z.1, z.2.1⟩)

local notation "frCoeffAt" => fun a ↦
  Bundle.Trivialization.openLocalFrameCoeff I ∞ (e a) (b a) (hU a)
local notation "frAnchorAt" => fun a ↦ ofLocalFrameAnchor (e a) (b a) (hU a) (ρ a)
local notation "frDerivAt" => fun a ↦ ofLocalFrameDeriv (e a) (b a) (hU a) (ρ a)
local notation "frBracketAt" => fun a ↦ ofLocalFrameBracket (e a) (b a) (hU a) (ρ a) (c a)

include hρ_change in
private theorem ofLocalFrameCover_anchor_compat
    (a a' : α) (x : M) (ha : x ∈ U a) (ha' : x ∈ U a') (v : V x) :
    τOpen ⟨x, ha⟩ (frAnchorAt a ⟨x, ha⟩ v) = τOpen ⟨x, ha'⟩ (frAnchorAt a' ⟨x, ha'⟩ v) := by
  have hexp (a₀ : α) (ha₀ : x ∈ U a₀) : τOpen ⟨x, ha₀⟩ (frAnchorAt a₀ ⟨x, ha₀⟩ v) =
      ∑ p, (e a₀).localFrameCoeff I (b a₀) p x v • τOpen ⟨x, ha₀⟩ (ρ a₀ p ⟨x, ha₀⟩) := by
    let va₀ : V|[U a₀] ⟨x, ha₀⟩ := v
    exact (congrArg (τOpen ⟨x, ha₀⟩)
      (ofLocalFrameAnchor_apply (e a₀) (b a₀) (hU a₀) (ρ a₀) ⟨x, ha₀⟩ va₀)).trans
        ((map_sum _ _ _).trans (Finset.sum_congr rfl fun _ _ ↦ map_smul _ _ _))
  have hρ' (i' : ι a') := hρ_change a a' ⟨x, ⟨ha, ha'⟩⟩ i'
  dsimp only at hρ'; refine (hexp a ha).trans (Eq.trans ?_ (hexp a' ha').symm)
  simp_rw [hρ', Finset.smul_sum, smul_smul]; rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun p _ ↦ ?_; rw [← Finset.sum_smul]; congr 1
  conv_lhs => rw [eq_sum_localFrameCoeff_smul_at I (e a') (b a') (hU a' ha') v]
  rw [map_sum]; exact Finset.sum_congr rfl fun _ _ ↦ map_smul _ _ _

omit [IsManifold I ∞ M] in
private theorem ofLocalFrameCover_coeff_sum
    (a a' : α) (m : ι a) (u : Cₛ^∞⟮I; F, V⟯) (y : M) (hya : y ∈ U a) (hya' : y ∈ U a') :
    frCoeffAt a m (u.restrict (U a)) ⟨y, hya⟩ = ∑ r : ι a',
      frCoeffAt a' r (u.restrict (U a')) ⟨y, hya'⟩ *
        localFrameTransition I (e a) (b a) (hU a) (e a') (b a') (hU a') r m ⟨y, ⟨hya, hya'⟩⟩ := by
  rw [((e a).openLocalFrameCoeff_apply (I := I) (n := ∞) (b a) (hU a) m _ ⟨y, hya⟩).trans
    (congrArg ((e a).localFrameCoeff I (b a) m y) (u.restrict_apply (U a) ⟨y, hya⟩))]
  conv_lhs => rw [(e a').eq_sum_localFrameCoeff_smul (I := I) (b := b a') (s := u) (hU a' hya')]
  rw [map_sum]; refine Finset.sum_congr rfl fun r _ ↦ ?_
  rw [map_smul, smul_eq_mul, localFrameTransition_apply]
  exact congrArg (· * _) (((e a').openLocalFrameCoeff_apply (I := I) (n := ∞) (b a') (hU a') r
    (u.restrict (U a')) ⟨y, hya'⟩).trans
      (congrArg ((e a').localFrameCoeff I (b a') r y) (u.restrict_apply (U a') ⟨y, hya'⟩))).symm

include hρ_change in
private theorem ofLocalFrameCover_deriv_coeff
    (a a' : α) (m : ι a) (u v : Cₛ^∞⟮I; F, V⟯) (x : M) (ha : x ∈ U a) (ha' : x ∈ U a') :
    let z : (U a ⊓ U a' : Opens M) := ⟨x, ⟨ha, ha'⟩⟩
    let g := localFrameTransition I (e a) (b a) (hU a) (e a') (b a') (hU a')
    let co' := fun r (w : Cₛ^∞⟮I; F, V⟯) ↦ frCoeffAt a' r (w.restrict (U a'))
    frDerivAt a (u.restrict (U a)) (frCoeffAt a m (v.restrict (U a))) ⟨x, ha⟩ =
      ∑ r : ι a', (frDerivAt a' (u.restrict (U a')) (co' r v) ⟨x, ha'⟩ * g r m z +
        co' r v ⟨x, ha'⟩ * ∑ i' : ι a', co' i' u ⟨x, ha'⟩ *
          mvfderiv I (g r m) z ((τOpen z).symm (τOpen ⟨x, ha'⟩ (ρ a' i' ⟨x, ha'⟩)))) := by
  intro z g co'
  let jW : C^∞⟮I, (U a ⊓ U a' : Opens M); I, U a'⟯ :=
    ⟨fun y ↦ ⟨y.1, y.2.2⟩, (TauCeti.ContMDiff.subtypeVal_comp_iff (U a')
      (fun y : (U a ⊓ U a' : Opens M) ↦ ⟨y.1, y.2.2⟩)).mp contMDiff_subtype_val⟩
  rw [ofLocalFrameDeriv_apply_apply]
  let v_a := frAnchorAt a ⟨x, ha⟩ (u.restrict (U a) ⟨x, ha⟩)
  let v_a' := frAnchorAt a' ⟨x, ha'⟩ (u.restrict (U a') ⟨x, ha'⟩)
  let v_W : TangentSpace I z := (τOpen z).symm (τOpen ⟨x, ha'⟩ v_a')
  have hv_eq : τOpen ⟨x, ha⟩ v_a = τOpen z v_W := by
    dsimp only [v_a, v_a', v_W]; rw [congrArg (frAnchorAt a ⟨x, ha⟩) (u.restrict_apply _ _),
      ofLocalFrameCover_anchor_compat U e b hU ρ hρ_change a a' x ha ha' (u x),
      ← congrArg (frAnchorAt a' ⟨x, ha'⟩) (u.restrict_apply _ _)]
    exact ((τOpen z).apply_symm_apply _).symm
  have hfeq_W (y : M) (hy₁ : y ∈ U a) (hy₂ : y ∈ (U a ⊓ U a' : Opens M)) :
      frCoeffAt a m (v.restrict (U a)) ⟨y, hy₁⟩ =
        (∑ r : ι a', (co' r v).comp jW * g r m) ⟨y, hy₂⟩ := by
    rw [ContMDiffMap.coe_sum, Finset.sum_apply]
    exact ofLocalFrameCover_coeff_sum U e b hU a a' m v y hy₁ hy₂.2
  rw [mvfderiv_open_congr ha z.2 hfeq_W hv_eq, mvfderiv_sum_contMDiffMap_apply]
  refine Finset.sum_congr rfl fun r _ ↦ ?_
  have hm := congr($(mvfderiv_mul (((co' r v).comp jW).contMDiff.mdifferentiableAt (by simp))
    ((g r m).contMDiff.mdifferentiableAt (by simp)) (x := z)) v_W)
  simp only [_root_.add_apply, _root_.smul_apply, smul_eq_mul] at hm
  have hcomp : mvfderiv I ((co' r v).comp jW) z v_W =
      frDerivAt a' (u.restrict (U a')) (co' r v) ⟨x, ha'⟩ := by
    rw [ofLocalFrameDeriv_apply_apply]
    exact mvfderiv_open_congr z.2 ha' (fun _ _ _ ↦ rfl) ((τOpen z).apply_symm_apply _)
  have hvW : v_W = ∑ i' : ι a', co' i' u ⟨x, ha'⟩ •
      (τOpen z).symm (τOpen ⟨x, ha'⟩ (ρ a' i' ⟨x, ha'⟩)) := by
    simp only [ContinuousMap.coe_mk, v_W, v_a', ofLocalFrameAnchor_apply, map_sum, map_smul]
    exact Finset.sum_congr rfl fun i' _ ↦ congrArg (· • _)
      ((e a').openLocalFrameCoeff_apply (I := I) (n := ∞) (b a') (hU a') i' _ ⟨x, ha'⟩).symm
  have hg_exp : mvfderiv I (g r m) z v_W = ∑ i' : ι a', co' i' u ⟨x, ha'⟩ *
      mvfderiv I (g r m) z ((τOpen z).symm (τOpen ⟨x, ha'⟩ (ρ a' i' ⟨x, ha'⟩))) := by
    rw [hvW, map_sum]; exact Finset.sum_congr rfl fun _ _ ↦ by rw [map_smul, smul_eq_mul]
  rw [show mvfderiv I (⇑((co' r v).comp jW * g r m)) z v_W =
      mvfderiv I (⇑((co' r v).comp jW) * ⇑(g r m)) z v_W from rfl, hm, hcomp,
    show ((co' r v).comp jW) z = co' r v ⟨x, ha'⟩ from rfl, hg_exp]; ring

include hρ_change hc_change in
private theorem ofLocalFrameCover_bracket_compat
    (a a' : α) (s t : Cₛ^∞⟮I; F, V⟯) (x : M) (ha : x ∈ U a) (ha' : x ∈ U a') :
    frBracketAt a (s.restrict (U a)) (t.restrict (U a)) ⟨x, ha⟩ =
      frBracketAt a' (s.restrict (U a')) (t.restrict (U a')) ⟨x, ha'⟩ := by
  let v₁ : V x := frBracketAt a (s.restrict (U a)) (t.restrict (U a)) ⟨x, ha⟩
  let v₂ : V x := frBracketAt a' (s.restrict (U a')) (t.restrict (U a')) ⟨x, ha'⟩
  refine (eq_sum_localFrameCoeff_smul_at I (e a) (b a) (hU a ha) v₁).trans
    ((Finset.sum_congr rfl fun m _ ↦ congrArg (· • (e a).localFrame (b a) m x) ?_).trans
      (eq_sum_localFrameCoeff_smul_at I (e a) (b a) (hU a ha) v₂).symm)
  let z : (U a ⊓ U a' : Opens M) := ⟨x, ⟨ha, ha'⟩⟩
  let g := localFrameTransition I (e a) (b a) (hU a) (e a') (b a') (hU a')
  let co' := fun r (u : Cₛ^∞⟮I; F, V⟯) ↦ frCoeffAt a' r (u.restrict (U a'))
  let dg (r i' : ι a') := mvfderiv I (g r m) z ((τOpen z).symm (τOpen ⟨x, ha'⟩ (ρ a' i' ⟨x, ha'⟩)))
  have lhs := congr($(ofLocalFrameBracket_coeff (e a) (b a) (hU a) (ρ a) (c a)
    (s.restrict (U a)) (t.restrict (U a)) m) ⟨x, ha⟩)
  rw [Bundle.Trivialization.openLocalFrameCoeff_apply] at lhs
  simp only [ContMDiffMap.coe_add, ContMDiffMap.coe_sub, ContMDiffMap.coe_sum,
    ContMDiffMap.coe_mul, Pi.add_apply, Pi.sub_apply, Finset.sum_apply, Pi.mul_apply] at lhs
  have hquad : (∑ p : ι a, ∑ q : ι a, frCoeffAt a p (s.restrict (U a)) ⟨x, ha⟩ *
      frCoeffAt a q (t.restrict (U a)) ⟨x, ha⟩ * c a p q m ⟨x, ha⟩) =
      ∑ i' : ι a', ∑ j' : ι a', co' i' s ⟨x, ha'⟩ * co' j' t ⟨x, ha'⟩ *
        (∑ p : ι a, ∑ q : ι a, g i' p z * g j' q z * c a p q m ⟨x, ha⟩) := by
    have hs (p : ι a) : frCoeffAt a p (s.restrict (U a)) ⟨x, ha⟩ =
        ∑ i' : ι a', co' i' s ⟨x, ha'⟩ * g i' p z :=
      ofLocalFrameCover_coeff_sum U e b hU a a' p s x ha ha'
    have ht (q : ι a) : frCoeffAt a q (t.restrict (U a)) ⟨x, ha⟩ =
        ∑ j' : ι a', co' j' t ⟨x, ha'⟩ * g j' q z :=
      ofLocalFrameCover_coeff_sum U e b hU a a' q t x ha ha'
    have step (p q : ι a) : (∑ i' : ι a', co' i' s ⟨x, ha'⟩ * g i' p z) *
        (∑ j' : ι a', co' j' t ⟨x, ha'⟩ * g j' q z) * c a p q m ⟨x, ha⟩ =
        ∑ i' : ι a', ∑ j' : ι a', co' i' s ⟨x, ha'⟩ * co' j' t ⟨x, ha'⟩ *
          (g i' p z * g j' q z * c a p q m ⟨x, ha⟩) := by
      rw [Finset.sum_mul, Finset.sum_mul]; refine Finset.sum_congr rfl fun _ _ ↦ ?_
      rw [Finset.mul_sum, Finset.sum_mul]; exact Finset.sum_congr rfl fun _ _ ↦ by ring
    simp_rw [hs, ht, step]
    refine (Finset.sum_congr rfl fun _ _ ↦ Finset.sum_comm).trans (Finset.sum_comm.trans ?_)
    refine Finset.sum_congr rfl fun _ _ ↦
      (Finset.sum_congr rfl fun _ _ ↦ Finset.sum_comm).trans (Finset.sum_comm.trans ?_)
    exact Finset.sum_congr rfl fun _ _ ↦ by simp only [Finset.mul_sum]
  have hrhs : (e a).localFrameCoeff I (b a) m x v₂ =
      ∑ k' : ι a', (frDerivAt a' (s.restrict (U a')) (co' k' t) ⟨x, ha'⟩ -
        frDerivAt a' (t.restrict (U a')) (co' k' s) ⟨x, ha'⟩ +
        ∑ i' : ι a', ∑ j' : ι a', co' i' s ⟨x, ha'⟩ * co' j' t ⟨x, ha'⟩ *
          c a' i' j' k' ⟨x, ha'⟩) * g k' m z := by
    let br' := frBracketAt a' (s.restrict (U a')) (t.restrict (U a'))
    have hsum' := congrFun (map_sum (ContMDiffSection.coeAddHom I F ∞ V|[U a'])
      (fun k' ↦ frCoeffAt a' k' br' • (e a').openLocalFrameSection I ∞ (b a') (hU a') k')
        Finset.univ) ⟨x, ha'⟩
    simp only [ContMDiffSection.coeAddHom_apply, Finset.sum_apply,
      ContMDiffSection.smul_apply] at hsum'
    have hval : v₂ = ∑ k' : ι a', frCoeffAt a' k' br' ⟨x, ha'⟩ • (e a').localFrame (b a') k' x :=
      ((congrArg (· ⟨x, ha'⟩) ((e a').eq_sum_openLocalFrameCoeff_smul (b a') (hU a') br')).trans
        hsum').trans (Finset.sum_congr rfl fun k' _ ↦ congrArg (_ • ·)
          ((e a').openLocalFrameSection_apply (I := I) (n := ∞) (b a') (hU a') k' ⟨x, ha'⟩))
    rw [hval, map_sum]; refine Finset.sum_congr rfl fun _ _ ↦ ?_
    rw [map_smul, smul_eq_mul, ofLocalFrameBracket_coeff]
    simp [g, z, co', localFrameTransition_apply]
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
      exact Finset.sum_congr rfl fun _ _ ↦ Finset.sum_comm.trans
        (Finset.sum_congr rfl fun _ _ ↦ Finset.sum_congr rfl fun _ _ ↦ by ring)
    · simp_rw [hc', mul_add, mul_sub, Finset.sum_add_distrib, Finset.sum_sub_distrib]
  dsimp only [v₁]; rw [lhs, ofLocalFrameCover_deriv_coeff U e b hU ρ hρ_change a a' m s t x ha ha',
    ofLocalFrameCover_deriv_coeff U e b hU ρ hρ_change a a' m t s x ha ha', hquad, hrhs]
  dsimp only [z, g, co', dg] at hd₁ hd₂ hc_sum
  simp only [Finset.sum_add_distrib, add_mul, sub_mul, Finset.sum_sub_distrib]
  rw [hd₁, hd₂, hc_sum]; ring

/-- **Gluing local-frame Lie algebroid data over an open cover.** -/
def ofLocalFrameCover [CompleteSpace E] : LieAlgebroid I F V :=
  glueOpenCover U hcover
    (fun a ↦ ofLocalFrame (e a) (b a) (hU a) (ρ a) (c a) (hc_swap a) (hρ_bracket a) (hc_jacobi a))
    (ofLocalFrameCover_anchor_compat U e b hU ρ hρ_change)
    (ofLocalFrameCover_bracket_compat U e b hU ρ c hρ_change hc_change)

@[simp] theorem ofLocalFrameCover_restrict [FiniteDimensional ℝ E] [T2Space M] (a : α) :
    (ofLocalFrameCover U hcover e b hU ρ c hc_swap hρ_bracket hc_jacobi
      hρ_change hc_change).restrict (U a) =
      ofLocalFrame (e a) (b a) (hU a) (ρ a) (c a) (hc_swap a) (hρ_bracket a) (hc_jacobi a) :=
  glueOpenCover_restrict U hcover _ _ _ a

/-- **Uniqueness of `ofLocalFrameCover`.** -/
theorem eq_ofLocalFrameCover [FiniteDimensional ℝ E] [T2Space M] {A : LieAlgebroid I F V}
    (hρ : ∀ a i, A.anchorFrameField (e a) (b a) (hU a) i = ρ a i)
    (hc : ∀ a i j k, A.structureFunction (e a) (b a) (hU a) i j k = c a i j k) :
    A = ofLocalFrameCover U hcover e b hU ρ c hc_swap hρ_bracket hc_jacobi hρ_change hc_change :=
  eq_glueOpenCover U hcover _ _ _ fun a ↦
    eq_ofLocalFrame (e a) (b a) (hU a) (ρ a) (c a) (hc_swap a) (hρ_bracket a) (hc_jacobi a)
      (fun i ↦ (A.anchorFrameField_eq (e a) (b a) (hU a) i).symm.trans (hρ a i))
      (fun i j k ↦ (A.structureFunction_eq (e a) (b a) (hU a) i j k).symm.trans (hc a i j k))

end OfLocalFrameCover
end TauCeti.LieAlgebroid
