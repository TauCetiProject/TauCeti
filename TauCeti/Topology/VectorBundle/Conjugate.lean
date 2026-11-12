/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.FiberBundle.Constructions
public import Mathlib.Topology.VectorBundle.Basic
public import TauCeti.Analysis.Normed.Module.Conjugate

/-!
# The conjugate of a complex vector bundle

For a complex vector bundle `E` with model fibre `F`, the conjugate bundle
`TauCeti.ConjugateBundle E` has fibres `Conjugate (E x)`: the same real vector spaces with complex
scalars acting through complex conjugation. Its total space carries the topology of the total space
of `E`, and its trivializations are those of `E`, read with model fibre `Conjugate F`
(`Trivialization.conjugate`). Every trivialization of `E` that is complex-linear stays
complex-linear for the conjugated actions, and the coordinate changes become their conjugates
(`Trivialization.coordChangeL_conjugate`), so the conjugate is again a complex vector bundle
(`TauCeti.ConjugateBundle.instVectorBundleComplex`). Its real vector bundle structure is that of
`E` (`TauCeti.ConjugateBundle.instVectorBundleReal`).

The identity of total spaces is a homeomorphism `TotalSpace F E ≃ₜ TotalSpace (Conjugate F) _`
covering the identity of the base, conjugate-linear on each fibre
(`TauCeti.ConjugateBundle.toConjHomeomorph`). Conjugating twice gives back `E`, by a homeomorphism
that is complex-linear on each fibre (`TauCeti.ConjugateBundle.doubleConjugateHomeomorph`), and
the conjugate of a direct sum is the direct sum of the conjugates
(`TauCeti.ConjugateBundle.prodHomeomorph`).

The conjugate bundle is the second piece of the doubled bundle of a bundle pair over a bordered
Riemann surface: `E` over the surface is glued to its conjugate over the reflected copy, along the
complex-linear identification `LinearMap.toConjugate` of the conjugation fixing the totally real
boundary condition.

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, 2nd ed., AMS
  Colloquium Publications **52**, 2012, Appendix C.3.
-/

public section

noncomputable section

open Bundle FiberBundle TauCeti.Conjugate

namespace TauCeti

variable {B : Type*}

/-- The conjugate of a bundle of complex vector spaces: the fibre over `x` is `Conjugate (E x)`. -/
abbrev ConjugateBundle (E : B → Type*) (x : B) : Type _ := Conjugate (E x)

namespace ConjugateBundle

variable (F : Type*) (E : B → Type*) [TopologicalSpace (TotalSpace F E)]

/-- The total space of the conjugate bundle carries the topology of the total space of `E`. -/
instance instTopologicalSpaceTotalSpace :
    TopologicalSpace (TotalSpace (Conjugate F) (ConjugateBundle E)) :=
  ‹TopologicalSpace (TotalSpace F E)›

/-- The identity of total spaces, `E → ConjugateBundle E`, as a homeomorphism covering the
identity of the base. -/
def toConjHomeomorph :
    TotalSpace F E ≃ₜ TotalSpace (Conjugate F) (ConjugateBundle E) where
  toFun p := ⟨p.proj, toConj p.2⟩
  invFun p := ⟨p.proj, ofConj p.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := continuous_id
  continuous_invFun := continuous_id

variable {F E}

@[simp] theorem toConjHomeomorph_apply (p : TotalSpace F E) :
    toConjHomeomorph F E p = ⟨p.proj, toConj p.2⟩ := (rfl)

@[simp] theorem toConjHomeomorph_symm_apply (p : TotalSpace (Conjugate F) (ConjugateBundle E)) :
    (toConjHomeomorph F E).symm p = ⟨p.proj, ofConj p.2⟩ := (rfl)

theorem proj_toConjHomeomorph (p : TotalSpace F E) :
    (toConjHomeomorph F E p).proj = p.proj := (rfl)

/-- On each fibre, the identity `E → ConjugateBundle E` is the conjugate-linear equivalence
`TauCeti.Conjugate.toConjL`. -/
theorem toConjHomeomorph_mk [∀ x, AddCommGroup (E x)] [∀ x, Module ℂ (E x)]
    [∀ x, TopologicalSpace (E x)] (x : B) (v : E x) :
    toConjHomeomorph F E ⟨x, v⟩ = ⟨x, toConjL v⟩ := by
  rw [toConjHomeomorph_apply, coe_toConjL]

end ConjugateBundle

/-! ### Trivializations -/

namespace ConjugateBundle

variable [TopologicalSpace B] {F : Type*} [TopologicalSpace F] {E : B → Type*}
  [TopologicalSpace (TotalSpace F E)]

/-- A trivialization of `E`, read as a trivialization of the conjugate bundle with model fibre
`Conjugate F`. -/
def _root_.Bundle.Trivialization.conjugate (e : Trivialization F (π F E)) :
    Trivialization (Conjugate F) (π (Conjugate F) (ConjugateBundle E)) :=
  e

@[simp] theorem _root_.Bundle.Trivialization.baseSet_conjugate (e : Trivialization F (π F E)) :
    e.conjugate.baseSet = e.baseSet := (rfl)

@[simp] theorem _root_.Bundle.Trivialization.source_conjugate (e : Trivialization F (π F E)) :
    e.conjugate.source = toConjHomeomorph F E '' e.source :=
  (Equiv.image_eq_preimage_symm _ _).symm ▸ rfl

/-- Evaluation of a conjugated trivialization: apply the trivialization of `E` and read the fibre
coordinate in `Conjugate F`. -/
theorem _root_.Bundle.Trivialization.conjugate_apply (e : Trivialization F (π F E))
    (p : TotalSpace (Conjugate F) (ConjugateBundle E)) :
    e.conjugate p =
      ((e ((toConjHomeomorph F E).symm p)).1, toConj (e ((toConjHomeomorph F E).symm p)).2) :=
  (rfl)

/-- Evaluation of the inverse of a conjugated trivialization: read the fibre coordinate in `F`,
apply the inverse of the trivialization of `E`, and read the result in the conjugate bundle. -/
theorem _root_.Bundle.Trivialization.conjugate_symm_apply (e : Trivialization F (π F E))
    (q : B × Conjugate F) :
    e.conjugate.toOpenPartialHomeomorph.symm q =
      toConjHomeomorph F E (e.toOpenPartialHomeomorph.symm (q.1, ofConj q.2)) :=
  (rfl)

theorem _root_.Bundle.Trivialization.conjugate_injective :
    Function.Injective (Trivialization.conjugate : Trivialization F (π F E) → _) :=
  fun _ _ h ↦ h

/-- Every trivialization of the conjugate bundle is the conjugate of a trivialization of `E`. -/
theorem _root_.Bundle.Trivialization.exists_conjugate_eq
    (e : Trivialization (Conjugate F) (π (Conjugate F) (ConjugateBundle E))) :
    ∃ e' : Trivialization F (π F E), e'.conjugate = e :=
  ⟨e, rfl⟩

variable [∀ x, TopologicalSpace (E x)] [FiberBundle F E]

variable (F E) in
/-- The conjugate bundle is a fibre bundle with model fibre `Conjugate F`, with the trivializations
of `E`. -/
instance instFiberBundle : FiberBundle (Conjugate F) (ConjugateBundle E) :=
  inferInstanceAs (FiberBundle F E)

@[simp] theorem trivializationAt_eq (x : B) :
    trivializationAt (Conjugate F) (ConjugateBundle E) x = (trivializationAt F E x).conjugate :=
  (rfl)

@[simp] theorem conjugate_mem_trivializationAtlas_iff {e : Trivialization F (π F E)} :
    e.conjugate ∈ trivializationAtlas (Conjugate F) (ConjugateBundle E) ↔
      e ∈ trivializationAtlas F E :=
  Iff.rfl

instance instMemTrivializationAtlasConjugate (e : Trivialization F (π F E))
    [MemTrivializationAtlas e] : MemTrivializationAtlas e.conjugate :=
  ⟨conjugate_mem_trivializationAtlas_iff.mpr (MemTrivializationAtlas.out (e := e))⟩

end ConjugateBundle

/-! ### Linear structure -/

namespace ConjugateBundle

variable [TopologicalSpace B] {E : B → Type*} [∀ x, AddCommGroup (E x)] [∀ x, Module ℂ (E x)]

section TopologicalModule

variable {F : Type*} [AddCommGroup F] [Module ℂ F] [TopologicalSpace F]
  [TopologicalSpace (TotalSpace F E)]

/-- A complex-linear trivialization of `E` is complex-linear for the conjugated actions. -/
instance _root_.Bundle.Trivialization.instIsLinearConjugate (e : Trivialization F (π F E))
    [e.IsLinear ℂ] : e.conjugate.IsLinear ℂ where
  linear b hb :=
    { map_add v w := (e.linear ℂ hb).map_add (ofConj v) (ofConj w)
      map_smul c v := by
        simp only [Trivialization.conjugate_apply, toConjHomeomorph_symm_apply, ofConj_smul,
          (e.linear ℂ hb).map_smul, toConj_smul, Complex.conj_conj] }

/-- The coordinate changes of the conjugate bundle are the conjugates of those of `E`. -/
theorem _root_.Bundle.Trivialization.coordChangeL_conjugate (e e' : Trivialization F (π F E))
    [e.IsLinear ℂ] [e'.IsLinear ℂ] {b : B} (hb : b ∈ e.baseSet ∩ e'.baseSet) :
    (Trivialization.coordChangeL ℂ e.conjugate e'.conjugate b :
        Conjugate F →L[ℂ] Conjugate F) =
      (Trivialization.coordChangeL ℂ e e' b : F →L[ℂ] F).conjugate := by
  ext v
  rw [ContinuousLinearEquiv.coe_coe, Trivialization.coordChangeL_apply e.conjugate e'.conjugate hb,
    ContinuousLinearMap.conjugate_apply, ContinuousLinearEquiv.coe_coe,
    Trivialization.coordChangeL_apply _ _ hb]
  rfl

end TopologicalModule

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F] [TopologicalSpace (TotalSpace F E)]
  [∀ x, TopologicalSpace (E x)] [FiberBundle F E]

variable (F E) in
/-- The conjugate of a complex vector bundle is a complex vector bundle. -/
instance instVectorBundleComplex [VectorBundle ℂ F E] :
    VectorBundle ℂ (Conjugate F) (ConjugateBundle E) where
  trivialization_linear' e he := by
    obtain ⟨e, rfl⟩ := e.exists_conjugate_eq
    have : MemTrivializationAtlas e := he
    infer_instance
  continuousOn_coordChange' e₁ e₂ he₁ he₂ := by
    obtain ⟨e₁, rfl⟩ := e₁.exists_conjugate_eq
    obtain ⟨e₂, rfl⟩ := e₂.exists_conjugate_eq
    have : MemTrivializationAtlas e₁ := he₁
    have : MemTrivializationAtlas e₂ := he₂
    exact (ContinuousLinearMap.continuous_conjugate.comp_continuousOn
      (continuousOn_coordChange ℂ e₁ e₂)).congr fun b hb ↦
        Trivialization.coordChangeL_conjugate e₁ e₂ hb

variable [NormedSpace ℝ F] [∀ x, Module ℝ (E x)]

variable (F E) in
/-- The real vector bundle structure of the conjugate bundle is that of `E`. -/
instance instVectorBundleReal [VectorBundle ℝ F E] :
    VectorBundle ℝ (Conjugate F) (ConjugateBundle E) :=
  inferInstanceAs (VectorBundle ℝ F E)

end ConjugateBundle

/-! ### Double conjugates and direct sums -/

namespace ConjugateBundle

section DoubleConjugate

variable (F : Type*) (E : B → Type*) [TopologicalSpace (TotalSpace F E)]

/-- Conjugating a bundle twice gives back the bundle. -/
def doubleConjugateHomeomorph :
    TotalSpace (Conjugate (Conjugate F)) (ConjugateBundle (ConjugateBundle E)) ≃ₜ
      TotalSpace F E where
  toFun p := ⟨p.proj, ofConj (ofConj p.2)⟩
  invFun p := ⟨p.proj, toConj (toConj p.2)⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := continuous_id
  continuous_invFun := continuous_id

variable {F E}

@[simp] theorem doubleConjugateHomeomorph_apply
    (p : TotalSpace (Conjugate (Conjugate F)) (ConjugateBundle (ConjugateBundle E))) :
    doubleConjugateHomeomorph F E p = ⟨p.proj, ofConj (ofConj p.2)⟩ := (rfl)

@[simp] theorem doubleConjugateHomeomorph_symm_apply (p : TotalSpace F E) :
    (doubleConjugateHomeomorph F E).symm p = ⟨p.proj, toConj (toConj p.2)⟩ := (rfl)

/-- On each fibre, the identification of the double conjugate with `E` is the complex-linear
equivalence `TauCeti.Conjugate.doubleConjugateL`. -/
theorem doubleConjugateHomeomorph_mk [∀ x, AddCommGroup (E x)] [∀ x, Module ℂ (E x)]
    [∀ x, TopologicalSpace (E x)] (x : B) (v : Conjugate (Conjugate (E x))) :
    doubleConjugateHomeomorph F E ⟨x, v⟩ = ⟨x, doubleConjugateL v⟩ := by
  rw [doubleConjugateHomeomorph_apply, doubleConjugateL_apply]

end DoubleConjugate

section Prod

variable (F₁ : Type*) (E₁ : B → Type*) [TopologicalSpace (TotalSpace F₁ E₁)]
  (F₂ : Type*) (E₂ : B → Type*) [TopologicalSpace (TotalSpace F₂ E₂)]

/-- The conjugate of the direct sum of two bundles is the direct sum of their conjugates. -/
def prodHomeomorph :
    TotalSpace (Conjugate (F₁ × F₂)) (ConjugateBundle (E₁ ×ᵇ E₂)) ≃ₜ
      TotalSpace (Conjugate F₁ × Conjugate F₂) (ConjugateBundle E₁ ×ᵇ ConjugateBundle E₂) where
  toFun p := ⟨p.proj, (toConj (ofConj p.2).1, toConj (ofConj p.2).2)⟩
  invFun p := ⟨p.proj, toConj (ofConj p.2.1, ofConj p.2.2)⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := continuous_id
  continuous_invFun := continuous_id

variable {F₁ E₁ F₂ E₂}

@[simp] theorem prodHomeomorph_apply
    (p : TotalSpace (Conjugate (F₁ × F₂)) (ConjugateBundle (E₁ ×ᵇ E₂))) :
    prodHomeomorph F₁ E₁ F₂ E₂ p = ⟨p.proj, (toConj (ofConj p.2).1, toConj (ofConj p.2).2)⟩ :=
  (rfl)

@[simp] theorem prodHomeomorph_symm_apply
    (p : TotalSpace (Conjugate F₁ × Conjugate F₂) (ConjugateBundle E₁ ×ᵇ ConjugateBundle E₂)) :
    (prodHomeomorph F₁ E₁ F₂ E₂).symm p = ⟨p.proj, toConj (ofConj p.2.1, ofConj p.2.2)⟩ := (rfl)

/-- On each fibre, the identification of the conjugate of a direct sum is the complex-linear
equivalence `TauCeti.Conjugate.prodL`. -/
theorem prodHomeomorph_mk [∀ x, AddCommGroup (E₁ x)] [∀ x, Module ℂ (E₁ x)]
    [∀ x, TopologicalSpace (E₁ x)] [∀ x, AddCommGroup (E₂ x)] [∀ x, Module ℂ (E₂ x)]
    [∀ x, TopologicalSpace (E₂ x)] (x : B) (v : Conjugate (E₁ x × E₂ x)) :
    prodHomeomorph F₁ E₁ F₂ E₂ ⟨x, v⟩ = ⟨x, prodL v⟩ := by
  rw [prodHomeomorph_apply, prodL_apply]

end Prod

end ConjugateBundle

end TauCeti
