/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Manifold.AlmostComplex.ContMDiff
public import Mathlib.Geometry.Manifold.VectorBundle.Pullback
public import TauCeti.Topology.VectorBundle.Pullback
import TauCeti.Geometry.Manifold.VectorBundle.Pullback

/-!
# Domain-dependent almost complex structures of finite regularity

A domain-dependent structure acts on the target tangent fibre at every pair of a domain point
and a target point. Its regularity is joint, as a native section of the endomorphism bundle of
the vertical pullback tangent bundle. It is not an endomorphism of the whole product tangent
bundle. The order includes zero and infinity.

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, second edition,
  Appendix B (finite-regularity domain-dependent almost complex structures).
-/

public noncomputable section

open Bundle
open scoped ContDiff Manifold

namespace TauCeti

variable {E H M EP HP P : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [NormedAddCommGroup EP] [NormedSpace ℝ EP] [TopologicalSpace HP]
  {IP : ModelWithCorners ℝ EP HP} [TopologicalSpace P] [ChartedSpace HP P]

/-- The target tangent bundle pulled back to the product of the domain and target manifolds. -/
abbrev verticalTangentBundle (I : ModelWithCorners ℝ E H) (M : Type*)
    [TopologicalSpace M] [ChartedSpace H M] (IP : ModelWithCorners ℝ EP HP) (P : Type*)
    [TopologicalSpace P] [ChartedSpace HP P] :=
  ((ContMDiffMap.snd : C^∞⟮IP.prod I, P × M; I, M⟯) : P × M → M) *ᵖ (TangentSpace I)

/-- A jointly `Cⁿ` vertical tangent endomorphism with square minus the identity at every pair
of a domain point and a target point. -/
structure ContMDiffAlmostComplexStructureFamily (I : ModelWithCorners ℝ E H) (M : Type*)
    [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    (IP : ModelWithCorners ℝ EP HP) (P : Type*) [TopologicalSpace P] [ChartedSpace HP P]
    (n : ℕ∞) where
  /-- The native section of the vertical tangent endomorphism bundle. -/
  toEndomorphism : Cₛ^n⟮IP.prod I; E →L[ℝ] E,
    fun q : P × M ↦ verticalTangentBundle I M IP P q →L[ℝ] verticalTangentBundle I M IP P q⟯
  /-- The fibrewise square identity is imposed on the whole product. -/
  square_neg (q : P × M) :
    (toEndomorphism q).comp (toEndomorphism q) = -ContinuousLinearMap.id ℝ _

namespace ContMDiffAlmostComplexStructureFamily

variable {n m : ℕ∞}

instance : CoeFun (ContMDiffAlmostComplexStructureFamily I M IP P n) fun _ ↦
    (q : P × M) → verticalTangentBundle I M IP P q → verticalTangentBundle I M IP P q :=
  ⟨fun J q ↦ J.toEndomorphism q⟩

/-- The pointwise almost complex structure on the target tangent fibre. -/
def almostComplexStructureAt (J : ContMDiffAlmostComplexStructureFamily I M IP P n)
    (q : P × M) : AlmostComplexStructure (verticalTangentBundle I M IP P q) where
  toLinearMap := (J.toEndomorphism q).toLinearMap
  square_neg := by
    ext v
    exact congrArg (fun A : verticalTangentBundle I M IP P q →L[ℝ]
      verticalTangentBundle I M IP P q ↦ A v) (J.square_neg q)

@[simp]
theorem almostComplexStructureAt_toLinearMap
    (J : ContMDiffAlmostComplexStructureFamily I M IP P n) (q : P × M) :
    (J.almostComplexStructureAt q).toLinearMap = (J.toEndomorphism q).toLinearMap := (rfl)

/-- Applying the structure twice negates the target tangent vector. -/
@[simp]
theorem apply_apply (J : ContMDiffAlmostComplexStructureFamily I M IP P n) (q : P × M)
    (v : verticalTangentBundle I M IP P q) : J q (J q v) = -v :=
  (J.almostComplexStructureAt q).apply_apply v

/-- Equality is detected by evaluation on the vertical tangent fibres. -/
@[ext]
theorem ext {J K : ContMDiffAlmostComplexStructureFamily I M IP P n}
    (h : ∀ q v, J q v = K q v) : J = K := by
  cases J
  cases K
  congr 1
  ext q v
  exact h q v

/-- Forget higher regularity, retaining every vertical endomorphism. -/
def ofLE (J : ContMDiffAlmostComplexStructureFamily I M IP P n) (hmn : m ≤ n) :
    ContMDiffAlmostComplexStructureFamily I M IP P m where
  toEndomorphism := ⟨J.toEndomorphism, J.toEndomorphism.contMDiff.of_le (by exact_mod_cast hmn)⟩
  square_neg := J.square_neg

@[simp]
theorem ofLE_toEndomorphism_apply (J : ContMDiffAlmostComplexStructureFamily I M IP P n)
    (hmn : m ≤ n) (q : P × M) :
    (J.ofLE hmn).toEndomorphism q = J.toEndomorphism q := (rfl)

/-- Negation preserves finite regularity on the native vertical endomorphism section. -/
instance : Neg (ContMDiffAlmostComplexStructureFamily I M IP P n) :=
  ⟨fun J ↦ { toEndomorphism := -J.toEndomorphism
             square_neg := by intro q; ext v; simp }⟩

@[simp]
theorem neg_toEndomorphism (J : ContMDiffAlmostComplexStructureFamily I M IP P n) :
    (-J).toEndomorphism = -J.toEndomorphism := (rfl)

/-- Forgetting no regularity leaves the family unchanged. -/
@[simp]
theorem ofLE_refl (J : ContMDiffAlmostComplexStructureFamily I M IP P n) :
    J.ofLE le_rfl = J := by
  ext q v
  simp only [ofLE_toEndomorphism_apply]

/-- Successive regularity downgrades compose. -/
@[simp]
theorem ofLE_ofLE {l : ℕ∞} (J : ContMDiffAlmostComplexStructureFamily I M IP P n)
    (hmn : m ≤ n) (hlm : l ≤ m) : (J.ofLE hmn).ofLE hlm = J.ofLE (hlm.trans hmn) := by
  ext q v
  simp only [ofLE_toEndomorphism_apply]

/-- Negation is involutive on domain-dependent structures. -/
@[simp]
theorem neg_neg (J : ContMDiffAlmostComplexStructureFamily I M IP P n) : -(-J) = J := by
  ext q v
  simp only [neg_toEndomorphism, _root_.neg_neg]

/-- Negation commutes with forgetting regularity. -/
@[simp]
theorem ofLE_neg (J : ContMDiffAlmostComplexStructureFamily I M IP P n) (hmn : m ≤ n) :
    (-J).ofLE hmn = -(J.ofLE hmn) := by
  ext q v
  simp only [ofLE_toEndomorphism_apply, neg_toEndomorphism, ContMDiffSection.coe_neg,
    Pi.neg_apply, neg_apply]

/-- Read the vertical section as an endomorphism of the original target tangent space.
This explicit bridge keeps the original and pulled-back fibre instances separate in coordinates. -/
def tangentEndomorphism (J : ContMDiffAlmostComplexStructureFamily I M IP P n) (q : P × M) :
    TangentSpace I q.2 →L[ℝ] TangentSpace I q.2 :=
  J.toEndomorphism q

/-- The original-target and vertical-bundle presentations have the same action on vectors. -/
theorem tangentEndomorphism_apply (J : ContMDiffAlmostComplexStructureFamily I M IP P n)
    (q : P × M) (v : TangentSpace I q.2) : J.tangentEndomorphism q v = J q v := (rfl)

/-- The original-target tangent endomorphism squares to minus the identity. -/
@[simp]
theorem tangentEndomorphism_apply_apply
    (J : ContMDiffAlmostComplexStructureFamily I M IP P n) (q : P × M)
    (v : TangentSpace I q.2) : J.tangentEndomorphism q (J.tangentEndomorphism q v) = -v := by
  exact J.apply_apply q v

/-- Joint regularity of the family as a map into the original target endomorphism bundle. -/
theorem contMDiff (J : ContMDiffAlmostComplexStructureFamily I M IP P n) :
    ContMDiff (IP.prod I) (I.prod 𝓘(ℝ, E →L[ℝ] E)) n
      (fun q : P × M ↦ TotalSpace.mk' (E →L[ℝ] E)
        (E := fun x : M ↦ TangentSpace I x →L[ℝ] TangentSpace I x) q.2
        (J.toEndomorphism q)) :=
  (Pullback.contMDiff_hom_section_iff
    (ContMDiffMap.snd : C^∞⟮IP.prod I, P × M; I, M⟯) contMDiff_snd _).mp
      J.toEndomorphism.contMDiff

/-- The field in original target tangent spaces has the same joint regularity. -/
theorem contMDiff_tangentEndomorphism
    (J : ContMDiffAlmostComplexStructureFamily I M IP P n) :
    ContMDiff (IP.prod I) (I.prod 𝓘(ℝ, E →L[ℝ] E)) n
      (fun q : P × M ↦ TotalSpace.mk' (E →L[ℝ] E)
        (E := fun x : M ↦ TangentSpace I x →L[ℝ] TangentSpace I x) q.2
        (J.tangentEndomorphism q)) := by
  exact J.contMDiff.congr fun _ ↦ rfl

/-- Construct a domain-dependent structure from its actual jointly regular vertical field. -/
def ofContMDiff (A : ∀ q : P × M, TangentSpace I q.2 →L[ℝ] TangentSpace I q.2)
    (hA : ContMDiff (IP.prod I) (I.prod 𝓘(ℝ, E →L[ℝ] E)) n
      (fun q : P × M ↦ TotalSpace.mk' (E →L[ℝ] E)
        (E := fun x : M ↦ TangentSpace I x →L[ℝ] TangentSpace I x) q.2 (A q)))
    (hsq : ∀ q v, A q (A q v) = -v) :
    ContMDiffAlmostComplexStructureFamily I M IP P n where
  toEndomorphism := ⟨A, (Pullback.contMDiff_hom_section_iff
    (ContMDiffMap.snd : C^∞⟮IP.prod I, P × M; I, M⟯) contMDiff_snd A).mpr hA⟩
  square_neg q := by ext v; exact hsq q v

@[simp]
theorem ofContMDiff_toEndomorphism_apply
    (A : ∀ q : P × M, TangentSpace I q.2 →L[ℝ] TangentSpace I q.2)
    (hA : ContMDiff (IP.prod I) (I.prod 𝓘(ℝ, E →L[ℝ] E)) n
      (fun q : P × M ↦ TotalSpace.mk' (E →L[ℝ] E)
        (E := fun x : M ↦ TangentSpace I x →L[ℝ] TangentSpace I x) q.2 (A q)))
    (hsq : ∀ q v, A q (A q v) = -v) (q : P × M) :
    (ofContMDiff A hA hsq).toEndomorphism q = A q := (rfl)

section Model

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- A jointly regular operator field on a model target defines a native vertical family.
The domain may be an arbitrary charted manifold and the target may have infinite dimension. -/
def ofModel (A : P × V → V →L[ℝ] V)
    (hA : ContMDiff (IP.prod 𝓘(ℝ, V)) 𝓘(ℝ, V →L[ℝ] V) n A)
    (hsq : ∀ q v, A q (A q v) = -v) :
    ContMDiffAlmostComplexStructureFamily 𝓘(ℝ, V) V IP P n :=
  ofContMDiff A (fun q ↦ by
    rw [contMDiffAt_hom_bundle]
    refine ⟨contMDiffAt_snd, ?_⟩
    simpa only [inCoordinates_tangent_bundle_core_model_space] using hA q) hsq

@[simp]
theorem ofModel_toEndomorphism_apply (A : P × V → V →L[ℝ] V)
    (hA : ContMDiff (IP.prod 𝓘(ℝ, V)) 𝓘(ℝ, V →L[ℝ] V) n A)
    (hsq : ∀ q v, A q (A q v) = -v) (q : P × V) :
    (ofModel A hA hsq).toEndomorphism q = A q := by
  unfold ofModel
  exact ofContMDiff_toEndomorphism_apply _ _ _ q

end Model

/-- Freeze the domain point, obtaining a native `Cⁿ` almost complex structure on the target. -/
def freeze (J : ContMDiffAlmostComplexStructureFamily I M IP P n) (p : P) :
    ContMDiffAlmostComplexStructure I n M where
  toEndomorphism := ⟨fun x ↦ J.toEndomorphism (p, x),
    J.contMDiff.comp (contMDiff_const.prodMk contMDiff_id)⟩
  square_neg x := by ext v; exact J.apply_apply (p, x) v

@[simp]
theorem freeze_toEndomorphism_apply (J : ContMDiffAlmostComplexStructureFamily I M IP P n)
    (p : P) (x : M) : (J.freeze p).toEndomorphism x = J.toEndomorphism (p, x) := (rfl)

/-- A frozen structure acts by the original-target tangent endomorphism of the family. -/
theorem freeze_apply (J : ContMDiffAlmostComplexStructureFamily I M IP P n)
    (p : P) (x : M) (v : TangentSpace I x) :
    J.freeze p x v = J.tangentEndomorphism (p, x) v :=
  (DFunLike.congr_fun (J.freeze_toEndomorphism_apply p x) v).trans
    (J.tangentEndomorphism_apply (p, x) v).symm

/-- A target structure defines a domain-independent family at the same regularity. -/
def const (J : ContMDiffAlmostComplexStructure I n M) :
    ContMDiffAlmostComplexStructureFamily I M IP P n :=
  ofContMDiff (fun q ↦ J.toEndomorphism q.2)
    (J.toEndomorphism.contMDiff.comp contMDiff_snd) (fun q v ↦ J.apply_apply q.2 v)

@[simp]
theorem const_toEndomorphism_apply (J : ContMDiffAlmostComplexStructure I n M) (q : P × M) :
    (const (IP := IP) (P := P) J).toEndomorphism q = J.toEndomorphism q.2 := (rfl)

/-- Freezing a domain-independent family recovers its target structure. -/
@[simp]
theorem freeze_const (J : ContMDiffAlmostComplexStructure I n M) (p : P) :
    (const (IP := IP) J).freeze p = J := by
  ext x v
  simp only [freeze_toEndomorphism_apply, const_toEndomorphism_apply]

/-- Forgetting regularity commutes with freezing a domain point. -/
@[simp]
theorem freeze_ofLE (J : ContMDiffAlmostComplexStructureFamily I M IP P n)
    (hmn : m ≤ n) (p : P) : (J.ofLE hmn).freeze p = (J.freeze p).ofLE hmn := by
  ext x v
  simp only [freeze_toEndomorphism_apply, ofLE_toEndomorphism_apply,
    ContMDiffAlmostComplexStructure.ofLE_toEndomorphism_apply]

/-- Domain-independent inclusion commutes with forgetting regularity. -/
@[simp]
theorem const_ofLE (J : ContMDiffAlmostComplexStructure I n M) (hmn : m ≤ n) :
    const (IP := IP) (P := P) (J.ofLE hmn) = (const (IP := IP) (P := P) J).ofLE hmn := by
  ext q v
  simp only [const_toEndomorphism_apply, ofLE_toEndomorphism_apply,
    ContMDiffAlmostComplexStructure.ofLE_toEndomorphism_apply]

/-- At infinite regularity, freezing gives the existing smooth target structure. -/
def freezeSmooth (J : ContMDiffAlmostComplexStructureFamily I M IP P ⊤) (p : P) :
    SmoothAlmostComplexStructure I M :=
  (J.freeze p).toSmooth

@[simp]
theorem freezeSmooth_toEndomorphism (J : ContMDiffAlmostComplexStructureFamily I M IP P ⊤)
    (p : P) : (J.freezeSmooth p).toEndomorphism = (J.freeze p).toEndomorphism :=
  ContMDiffAlmostComplexStructure.toSmooth_toEndomorphism _

/-- Freezing a domain-independent smooth family recovers the existing smooth carrier. -/
@[simp]
theorem freezeSmooth_const (J : SmoothAlmostComplexStructure I M) (p : P) :
    (const (IP := IP) (P := P) (J.toContMDiff ⊤)).freezeSmooth p = J := by
  rw [freezeSmooth, freeze_const, SmoothAlmostComplexStructure.toContMDiff_toSmooth]

/-- Freezing commutes with negation. -/
@[simp]
theorem freeze_neg (J : ContMDiffAlmostComplexStructureFamily I M IP P n) (p : P) :
    (-J).freeze p = -(J.freeze p) := by
  ext x v
  simp only [freeze_toEndomorphism_apply, neg_toEndomorphism,
    ContMDiffAlmostComplexStructure.neg_toEndomorphism, ContMDiffSection.coe_neg,
    Pi.neg_apply]
  -- Freezing identifies the original and pulled-back tangent-fibre instances.
  rfl

/-- The domain-independent inclusion commutes with negation. -/
@[simp]
theorem const_neg (J : ContMDiffAlmostComplexStructure I n M) :
    const (IP := IP) (P := P) (-J) = -(const (IP := IP) (P := P) J) := by
  ext q v
  simp only [const_toEndomorphism_apply, neg_toEndomorphism,
    ContMDiffAlmostComplexStructure.neg_toEndomorphism, ContMDiffSection.coe_neg,
    Pi.neg_apply]
  -- The domain-independent field inherits the same fibre negation through its pullback.
  rfl

section Comp

variable {EQ HQ Q : Type*} [NormedAddCommGroup EQ] [NormedSpace ℝ EQ]
  [TopologicalSpace HQ] {IQ : ModelWithCorners ℝ EQ HQ} [TopologicalSpace Q] [ChartedSpace HQ Q]

/-- Domain reparametrization is composition of a vertical field and costs no derivative. -/
def comp (J : ContMDiffAlmostComplexStructureFamily I M IP P n)
    (g : C^n⟮IQ, Q; IP, P⟯) : ContMDiffAlmostComplexStructureFamily I M IQ Q n :=
  ofContMDiff (fun q ↦ J.toEndomorphism (g q.1, q.2))
    (J.contMDiff.comp ((g.contMDiff.comp contMDiff_fst).prodMk contMDiff_snd))
    (fun q v ↦ J.apply_apply (g q.1, q.2) v)

@[simp]
theorem comp_toEndomorphism_apply (J : ContMDiffAlmostComplexStructureFamily I M IP P n)
    (g : C^n⟮IQ, Q; IP, P⟯) (q : Q × M) :
    (J.comp g).toEndomorphism q = J.toEndomorphism (g q.1, q.2) := (rfl)

/-- Freezing a reparametrized family freezes the original family at the image domain point. -/
@[simp]
theorem freeze_comp (J : ContMDiffAlmostComplexStructureFamily I M IP P n)
    (g : C^n⟮IQ, Q; IP, P⟯) (q : Q) : (J.comp g).freeze q = J.freeze (g q) := by
  ext x v
  simp only [freeze_toEndomorphism_apply, comp_toEndomorphism_apply]

/-- Domain composition preserves domain-independent families. -/
@[simp]
theorem comp_const (J : ContMDiffAlmostComplexStructure I n M) (g : C^n⟮IQ, Q; IP, P⟯) :
    (const (IP := IP) (P := P) J).comp g = const (IP := IQ) (P := Q) J := by
  ext q v
  simp only [comp_toEndomorphism_apply, const_toEndomorphism_apply]

/-- Reparametrization by the identity leaves a family unchanged. -/
@[simp]
theorem comp_id (J : ContMDiffAlmostComplexStructureFamily I M IP P n) :
    J.comp (ContMDiffMap.id : C^n⟮IP, P; IP, P⟯) = J := by
  ext q v
  simp only [comp_toEndomorphism_apply]
  -- The bundled identity and the pair reconstructed from its projections are definitionally equal.
  rfl

variable {ER HR R : Type*} [NormedAddCommGroup ER] [NormedSpace ℝ ER]
  [TopologicalSpace HR] {IR : ModelWithCorners ℝ ER HR} [TopologicalSpace R] [ChartedSpace HR R]

/-- Successive domain reparametrizations are composition of their native maps. -/
theorem comp_comp (J : ContMDiffAlmostComplexStructureFamily I M IP P n)
    (g : C^n⟮IQ, Q; IP, P⟯) (h : C^n⟮IR, R; IQ, Q⟯) :
    (J.comp g).comp h = J.comp (g.comp h) := by
  ext q v
  simp only [comp_toEndomorphism_apply, ContMDiffMap.comp_apply]

end Comp

end ContMDiffAlmostComplexStructureFamily

end TauCeti
