/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.Augment
public import Mathlib.CategoryTheory.Abelian.Projective.Resolution
public import TauCeti.Algebra.Homology.ChainComplex.Exact

/-!
# Construction and comparison of projective resolutions

Mathlib compares two projective resolutions `P` and `Q` of the same object `X` by the lift of the
identity of `X` (`CategoryTheory.ProjectiveResolution.homotopyEquiv`), which it constructs
abstractly from the projectivity of the terms. Often one has an explicit chain map
`f : P.complex ⟶ Q.complex` instead, compatible with the augmentations. Such an `f` is itself a
lift of the identity of `X`, so it is homotopic to Mathlib's comparison
(`CategoryTheory.ProjectiveResolution.homotopyOfComm`) and is a homotopy equivalence
(`CategoryTheory.ProjectiveResolution.homotopyEquivOfComm`).

`ChainComplex.toProjectiveResolution` packages an augmented projective chain complex `K`
which is exact in positive degrees, with an epimorphic augmentation `ε : K.X 0 ⟶ X` exact at
`K.X 0`. That the chain map induced by `ε` from `K` to `X` placed in degree `0` is a
quasi-isomorphism, which needs no projectivity, is `ChainComplex.quasiIso_toSingle₀Equiv_symm`.

A complex of projectives whose differentials factor through short exact sequences
`0 ⟶ A (p + 1) ⟶ K.X p ⟶ A p ⟶ 0` is a projective resolution of `A 0`
(`CategoryTheory.ProjectiveResolution.splice`), by the splicing lemmas of
`TauCeti.Algebra.Homology.ChainComplex.Exact`.

One can also transport a projective resolution across an object isomorphism
(`CategoryTheory.ProjectiveResolution.ofIso`), extract its degree-zero augmentation map and
cokernel property (`CategoryTheory.ProjectiveResolution.augZero`,
`CategoryTheory.ProjectiveResolution.isColimitCokernelCoforkAugZero`), and prepend a short exact
sequence `0 ⟶ K ⟶ F ⟶ M ⟶ 0` with `F` projective (`CategoryTheory.ProjectiveResolution.cons`,
with augmentation equation `CategoryTheory.ProjectiveResolution.cons_augZero`).
-/

public section

noncomputable section

namespace ChainComplex

open CategoryTheory CategoryTheory.Limits

variable {C : Type*} [Category* C] [Abelian C] {X : C}


/-- An augmented complex of projectives, exact in positive degrees and at its epimorphic
augmentation, is a projective resolution. -/
-- The body is exposed so the augmentation's domain in `toProjectiveResolution_π` is the
-- supplied complex.
@[expose]
def toProjectiveResolution (K : ChainComplex C ℕ) (ε : K.X 0 ⟶ X) (hε : K.d 1 0 ≫ ε = 0)
    (hP : ∀ n, Projective (K.X n)) [Epi ε]
    (h₀ : (ShortComplex.mk (K.d 1 0) ε hε).Exact)
    (h : ∀ n, K.ExactAt (n + 1)) : ProjectiveResolution X where
  complex := K
  projective := hP
  π := (ChainComplex.toSingle₀Equiv _ _).symm ⟨ε, hε⟩
  quasiIso := quasiIso_toSingle₀Equiv_symm K ε hε h₀ h

/-- The exact-complex construction retains the given complex. -/
@[simp] theorem toProjectiveResolution_complex (K : ChainComplex C ℕ) (ε : K.X 0 ⟶ X) (hε)
    (hP : ∀ n, Projective (K.X n)) [Epi ε] (h₀) (h) :
    (K.toProjectiveResolution ε hε hP h₀ h).complex = K := (rfl)

/-- The exact-complex construction uses the chain map induced by the given augmentation. -/
@[simp] theorem toProjectiveResolution_π (K : ChainComplex C ℕ) (ε : K.X 0 ⟶ X) (hε)
    (hP : ∀ n, Projective (K.X n)) [Epi ε] (h₀) (h) :
    (K.toProjectiveResolution ε hε hP h₀ h).π =
      (ChainComplex.toSingle₀Equiv _ _).symm ⟨ε, hε⟩ := (rfl)


end ChainComplex

namespace CategoryTheory.ProjectiveResolution

section Splice

variable {C : Type*} [Category* C] [Abelian C] {K : ChainComplex C ℕ} [∀ p, Projective (K.X p)]
  {A : ℕ → C} (ι : ∀ p, A (p + 1) ⟶ K.X p) (ε : ∀ p, K.X p ⟶ A p) (w : ∀ p, ι p ≫ ε p = 0)
  (hS : ∀ p, (ShortComplex.mk _ _ (w p)).ShortExact) (hd : ∀ p, K.d (p + 1) p = ε (p + 1) ≫ ι p)

/-- **Splicing short exact sequences into a projective resolution.** A complex of projectives
whose differentials factor as `K.X (p + 1) ⟶ A (p + 1) ⟶ K.X p` through short exact sequences
`0 ⟶ A (p + 1) ⟶ K.X p ⟶ A p ⟶ 0` is a projective resolution of `A 0`, with augmentation
`ε 0`. -/
-- The body is exposed so that the complex of the resolution is `K` itself.
@[expose]
def splice : ProjectiveResolution (A 0) :=
  have : Epi (ε 0) := (hS 0).epi_g
  K.toProjectiveResolution (ε 0) (ChainComplex.d_one_zero_comp_of_shortExact ι ε w hd)
    inferInstance (ChainComplex.exact_d_one_zero_of_shortExact ι ε w hS hd)
    (ChainComplex.exactAt_succ_of_shortExact ι ε w hS hd)

/-- The spliced resolution has the given complex `K` as its complex. -/
@[simp]
lemma splice_complex : (splice ι ε w hS hd).complex = K := (rfl)

/-- In degree `0`, the augmentation of the spliced resolution is `ε 0`. -/
@[simp]
lemma splice_π_f_zero : (splice ι ε w hS hd).π.f 0 = ε 0 :=
  ChainComplex.toSingle₀Equiv_symm_apply_f_zero (ε 0) _

end Splice


section Homotopy

variable {C : Type*} [Category* C] [Abelian C] {X : C} (P Q : ProjectiveResolution X)
  (f : P.complex ⟶ Q.complex) (hf : f ≫ Q.π = P.π)

/-- A chain map between projective resolutions of `X` compatible with the augmentations is
homotopic to the comparison `(homotopyEquiv P Q).hom`, the lift of the identity of `X`. -/
def homotopyOfComm : Homotopy f (homotopyEquiv P Q).hom :=
  liftHomotopy (𝟙 X) _ _ (by simp [hf]) (by simp)

/-- A chain map between projective resolutions of `X` compatible with the augmentations is a
homotopy equivalence; its homotopy inverse is the lift of the identity of `X`. -/
def homotopyEquivOfComm : HomotopyEquiv P.complex Q.complex :=
  (homotopyEquiv P Q).copy (homotopyOfComm P Q f hf).symm

/-- The forward map of the homotopy equivalence is the given chain map. -/
@[simp]
theorem homotopyEquivOfComm_hom : (homotopyEquivOfComm P Q f hf).hom = f :=
  (rfl)

/-- The homotopy inverse is the lift of the identity from `Q` to `P`. -/
@[simp]
theorem homotopyEquivOfComm_inv : (homotopyEquivOfComm P Q f hf).inv = lift (𝟙 X) Q P :=
  (rfl)

end Homotopy

section Constructions

open CategoryTheory.Limits

variable {C : Type*} [Category* C] [Abelian C]

/-- Transport a projective resolution across an isomorphism of the resolved object. -/
def ofIso {M N : C} (P : ProjectiveResolution M) (e : M ≅ N) : ProjectiveResolution N where
  complex := P.complex
  projective := P.projective
  π := P.π ≫ (ChainComplex.single₀ _).map e.hom
  quasiIso := by
    have : IsIso ((ChainComplex.single₀ C).map e.hom) :=
      inferInstanceAs (IsIso (((ChainComplex.single₀ C).mapIso e).hom))
    infer_instance

/-- Transporting a projective resolution across an isomorphism preserves its complex. -/
@[simp]
theorem ofIso_complex {M N : C} (P : ProjectiveResolution M) (e : M ≅ N) :
    (P.ofIso e).complex = P.complex :=
  (rfl)

/-- Transporting a projective resolution across an isomorphism composes its augmentation with the
isomorphism. -/
@[simp]
theorem ofIso_π {M N : C} (P : ProjectiveResolution M) (e : M ≅ N) :
    (P.ofIso e).π = eqToHom (ofIso_complex P e) ≫ P.π ≫ (ChainComplex.single₀ _).map e.hom := by
  dsimp only [ofIso]
  exact (Category.id_comp _).symm

/-- The degree-zero augmentation morphism `P.complex.X 0 ⟶ X` of a projective resolution. -/
def augZero {X : C} (P : ProjectiveResolution X) : P.complex.X 0 ⟶ X :=
  P.π.f 0 ≫ (HomologicalComplex.singleObjXSelf (.down ℕ) 0 X).hom

/-- Unfolds `CategoryTheory.ProjectiveResolution.augZero`. -/
theorem augZero_def {X : C} (P : ProjectiveResolution X) :
    P.augZero = P.π.f 0 ≫ (HomologicalComplex.singleObjXSelf (.down ℕ) 0 X).hom :=
  (rfl)

/-- The degree-zero augmentation morphism of a projective resolution is an epimorphism. -/
instance epi_augZero {X : C} (P : ProjectiveResolution X) : Epi P.augZero := by
  rw [augZero_def]
  infer_instance

/-- The differential `d 1 0` of a projective resolution composes with `augZero` to zero. -/
@[reassoc (attr := simp)]
theorem d_one_zero_comp_augZero {X : C} (P : ProjectiveResolution X) :
    P.complex.d 1 0 ≫ P.augZero = 0 := by
  rw [augZero_def, ← Category.assoc, P.complex_d_comp_π_f_zero, zero_comp]

/-- The pair `(P.complex.d 1 0, P.augZero)` is exact. -/
theorem exact_d_one_zero_augZero {X : C} (P : ProjectiveResolution X) :
    (ShortComplex.mk (P.complex.d 1 0) P.augZero P.d_one_zero_comp_augZero).Exact := by
  refine (ShortComplex.exact_iff_of_iso ?_).2 P.exact₀
  exact ShortComplex.isoMk (Iso.refl _) (Iso.refl _)
    (HomologicalComplex.singleObjXSelf (.down ℕ) 0 X) (by simp) (by simp [augZero_def])

/-- The degree-zero augmentation `P.augZero` exhibits `X` as the cokernel of `P.complex.d 1 0`. -/
def isColimitCokernelCoforkAugZero {X : C} (P : ProjectiveResolution X) :
    IsColimit (CokernelCofork.ofπ P.augZero P.d_one_zero_comp_augZero) :=
  IsColimit.ofIsoColimit P.isColimitCokernelCofork <|
    Cofork.ext (HomologicalComplex.singleObjXSelf (.down ℕ) 0 X) (by simp [augZero_def])

/-- Transporting a projective resolution across `e : M ≅ N` composes `augZero` with `e.hom`. -/
@[simp]
theorem ofIso_augZero {M N : C} (P : ProjectiveResolution M) (e : M ≅ N) :
    (P.ofIso e).augZero =
      eqToHom (congrFun (congrArg HomologicalComplex.X (ofIso_complex P e)) 0) ≫
        P.augZero ≫ e.hom := by
  simp [augZero_def, ofIso_π]

/-- Prepending a short exact sequence `0 ⟶ K --i--> F --p--> M ⟶ 0` with `F` projective to a
projective resolution `Q` of `K` gives a projective resolution of `M`. -/
def cons {K F M : C} (Q : ProjectiveResolution K) [Projective F] {i : K ⟶ F} {p : F ⟶ M}
    {hip : i ≫ p = 0} (hS : (ShortComplex.mk i p hip).ShortExact) :
    ProjectiveResolution M :=
  let hw : Q.complex.d 1 0 ≫ Q.augZero ≫ i = 0 := by
    rw [← Category.assoc, Q.d_one_zero_comp_augZero, zero_comp]
  let A := _root_.ChainComplex.augment Q.complex (Q.augZero ≫ i) hw
  have hp₀ : A.d 1 0 ≫ p = 0 := by
    dsimp [A]
    simp [hip]
    rfl
  @_root_.ChainComplex.toProjectiveResolution C _ _ M A p hp₀
    (fun
      | 0 => by rw [_root_.ChainComplex.augment_X_zero]; exact ‹Projective F›
      | k + 1 => by rw [_root_.ChainComplex.augment_X_succ]; exact Q.projective k)
    hS.epi_g
    (by
      let α : ShortComplex.mk (A.d 1 0) p hp₀ ⟶ ShortComplex.mk i p hip :=
        { τ₁ := Q.augZero, τ₂ := 𝟙 F, τ₃ := 𝟙 M
          comm₁₂ := by dsimp [A]; simp }
      have : Epi α.τ₁ := Q.epi_augZero
      have : IsIso α.τ₂ := inferInstanceAs (IsIso (𝟙 F))
      have : Mono α.τ₃ := inferInstanceAs (Mono (𝟙 M))
      exact (ShortComplex.exact_iff_of_epi_of_isIso_of_mono α).2 hS.exact)
    (fun
      | 0 => by
        rw [HomologicalComplex.exactAt_iff' _ 2 1 0 (by simp) (by simp)]
        let α : ShortComplex.mk (Q.complex.d 1 0) Q.augZero Q.d_one_zero_comp_augZero ⟶
            A.sc' 2 1 0 :=
          { τ₁ := 𝟙 _, τ₂ := 𝟙 _, τ₃ := i
            comm₁₂ := by dsimp [A]; simp
            comm₂₃ := by dsimp [A]; simp }
        have : Epi α.τ₁ := inferInstanceAs (Epi (𝟙 (Q.complex.X 1)))
        have : IsIso α.τ₂ := inferInstanceAs (IsIso (𝟙 (Q.complex.X 0)))
        have : Mono α.τ₃ := hS.mono_f
        exact (ShortComplex.exact_iff_of_epi_of_isIso_of_mono α).1 Q.exact_d_one_zero_augZero
      | k + 1 => by
        rw [HomologicalComplex.exactAt_iff' _ (k + 3) (k + 2) (k + 1) (by simp) (by simp)]
        let e : A.sc' (k + 3) (k + 2) (k + 1) ≅
            ShortComplex.mk (Q.complex.d (k + 2) (k + 1)) (Q.complex.d (k + 1) k)
              (Q.complex.d_comp_d _ _ _) :=
          ShortComplex.isoMk (Iso.refl _) (Iso.refl _) (Iso.refl _)
            (by dsimp [A]; simp)
            (by dsimp [A]; simp)
        exact (ShortComplex.exact_iff_of_iso e).2 (Q.exact_succ k))

/-- The complex of `ProjectiveResolution.cons` augments `Q.complex` with `Q.augZero ≫ i`. -/
@[simp]
theorem cons_complex {K F M : C} (Q : ProjectiveResolution K) [Projective F] {i : K ⟶ F}
    {p : F ⟶ M} {hip : i ≫ p = 0} (hS : (ShortComplex.mk i p hip).ShortExact) :
    (Q.cons hS).complex = _root_.ChainComplex.augment Q.complex (Q.augZero ≫ i)
      (by rw [← Category.assoc, Q.d_one_zero_comp_augZero, zero_comp]) :=
  (rfl)

/-- The degree-zero term of `Q.cons hS` is `F`. -/
theorem cons_complex_X_zero {K F M : C} (Q : ProjectiveResolution K) [Projective F] {i : K ⟶ F}
    {p : F ⟶ M} {hip : i ≫ p = 0} (hS : (ShortComplex.mk i p hip).ShortExact) :
    (Q.cons hS).complex.X 0 = F := by
  rw [cons_complex, _root_.ChainComplex.augment_X_zero]

/-- In positive degrees, the terms of `Q.cons hS` are those of `Q`. -/
theorem cons_complex_X_succ {K F M : C} (Q : ProjectiveResolution K) [Projective F] {i : K ⟶ F}
    {p : F ⟶ M} {hip : i ≫ p = 0} (hS : (ShortComplex.mk i p hip).ShortExact) (k : ℕ) :
    (Q.cons hS).complex.X (k + 1) = Q.complex.X k := by
  rw [cons_complex, _root_.ChainComplex.augment_X_succ]

/-- The first differential of `Q.cons hS` is `Q.augZero ≫ i`, up to the object identifications
`(Q.cons hS).complex.X 1 = Q.complex.X 0` and `(Q.cons hS).complex.X 0 = F`. -/
@[simp]
theorem cons_complex_d_one_zero {K F M : C} (Q : ProjectiveResolution K) [Projective F] {i : K ⟶ F}
    {p : F ⟶ M} {hip : i ≫ p = 0} (hS : (ShortComplex.mk i p hip).ShortExact) :
    (Q.cons hS).complex.d 1 0 =
      eqToHom (Q.cons_complex_X_succ hS 0) ≫ Q.augZero ≫ i ≫
        eqToHom (Q.cons_complex_X_zero hS).symm := by
  rw [← Category.assoc Q.augZero i]
  refine (conj_eqToHom_iff_heq _ (Q.augZero ≫ i) (Q.cons_complex_X_succ hS 0)
    (Q.cons_complex_X_zero hS)).2 ?_
  rw [Q.cons_complex hS, _root_.ChainComplex.augment_d_one_zero]
  rfl

/-- In positive degrees, the differentials of `Q.cons hS` are those of `Q`, up to the object
identifications `(Q.cons hS).complex.X (k + 1) = Q.complex.X k`. -/
@[simp]
theorem cons_complex_d_succ_succ {K F M : C} (Q : ProjectiveResolution K) [Projective F]
    {i : K ⟶ F} {p : F ⟶ M} {hip : i ≫ p = 0} (hS : (ShortComplex.mk i p hip).ShortExact)
    (j k : ℕ) :
    (Q.cons hS).complex.d (j + 1) (k + 1) =
      eqToHom (Q.cons_complex_X_succ hS j) ≫ Q.complex.d j k ≫
        eqToHom (Q.cons_complex_X_succ hS k).symm := by
  refine (conj_eqToHom_iff_heq _ _ (Q.cons_complex_X_succ hS j)
    (Q.cons_complex_X_succ hS k)).2 ?_
  rw [Q.cons_complex hS, _root_.ChainComplex.augment_d_succ_succ]
  rfl

/-- The degree-zero augmentation of `Q.cons hS` is `p`, up to `(Q.cons hS).complex.X 0 = F`. -/
@[simp]
theorem cons_augZero {K F M : C} (Q : ProjectiveResolution K) [Projective F] {i : K ⟶ F}
    {p : F ⟶ M} {hip : i ≫ p = 0} (hS : (ShortComplex.mk i p hip).ShortExact) :
    (Q.cons hS).augZero = eqToHom (Q.cons_complex_X_zero hS) ≫ p := by
  rw [augZero_def, _root_.ChainComplex.single₀ObjXSelf, Iso.refl_hom, Category.comp_id]
  have hpi :
      ((_root_.ChainComplex.toSingle₀Equiv (Q.cons hS).complex M).symm
        ⟨eqToHom (Q.cons_complex_X_zero hS) ≫ p, by simp [hip]⟩).f 0 =
        eqToHom (Q.cons_complex_X_zero hS) ≫ p :=
    _root_.ChainComplex.toSingle₀Equiv_symm_apply_f_zero
      (eqToHom (Q.cons_complex_X_zero hS) ≫ p) _
  refine Eq.trans ?_ hpi
  dsimp only [cons, _root_.ChainComplex.toProjectiveResolution,
    _root_.ChainComplex.toSingle₀Equiv]
  congr 2
  exact Subtype.ext (Category.id_comp p).symm

/-- Truncating `ProjectiveResolution.cons` recovers `Q.complex`. -/
def consTruncateIso {K F M : C} (Q : ProjectiveResolution K) [Projective F] {i : K ⟶ F}
    {p : F ⟶ M} {hip : i ≫ p = 0} (hS : (ShortComplex.mk i p hip).ShortExact) :
    _root_.ChainComplex.truncate.obj (Q.cons hS).complex ≅ Q.complex :=
  _root_.ChainComplex.truncate.mapIso (eqToIso (Q.cons_complex hS)) ≪≫
    _root_.ChainComplex.truncateAugment Q.complex (Q.augZero ≫ i)
      (by rw [← Category.assoc, Q.d_one_zero_comp_augZero, zero_comp])

end Constructions

end CategoryTheory.ProjectiveResolution
