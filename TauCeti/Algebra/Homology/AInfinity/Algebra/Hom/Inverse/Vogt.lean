/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.AInfinity.Algebra.Hom.Inverse.Right
public import TauCeti.Algebra.Homology.AInfinity.Algebra.Hom.Transformation
import TauCeti.Algebra.Homology.AInfinity.Algebra.BarDifferential
import Mathlib.Tactic.Abel

/-!
# Vogt's lemma and the ring-level homotopy-equivalence criterion for A-infinity morphisms

Suppose `f : A ⟶ B` and `g : B ⟶ A` are morphisms of `A∞` algebras equipped with a right `A∞`
homotopy `H_B : f ∘ g ⇒ id_B` and a homogeneous degree-`-1` chain homotopy `h_A` witnessing
`g₁ ∘ f₁ - id_A = d_A ∘ h_A + h_A ∘ d_A`.  Higher arities couple `H_B ∘ F` and `F ∘ H_A`, so we
upgrade `h_A` coherently in `TauCeti.AInfinityHom.reducedTransformationCochains`:

1. Replacing `h_A` by `h_A' = h_A ∘ (1 - g₁ ∘ f₁) + g₁ ∘ h_B ∘ f₁` preserves the chain-homotopy
   identity for `g₁ ∘ f₁ - id_A` and makes `h_B ∘ f₁ - f₁ ∘ h_A'` exact via the degree-`-2` map
   `m₁ = h_B ∘ f₁ ∘ h_A - f₁ ∘ h_A² - h_B² ∘ f₁`.
2. Inductively along `filtration`, we extend `h_A'` and `m₁` to a degree-`-1` transformation `H_A`
   bounding `G ∘ F - id` and a degree-`-2` transformation `M` bounding `H_B ∘ F - F ∘ H_A`: at
   filtration `k + 1`, `δ² = 0` makes the top-arity residual `q` closed and forces `d_B ∘ s +
   s ∘ b₁ = f₁ ∘ q`, cancelled by `δξ = g₁ ∘ s - h_A' ∘ q` and
   `δμ = -(h_B ∘ (s - f₁ ∘ δξ) + f₁ ∘ h_A' ∘ δξ)`.

Combining `homotopyOfRightHomotopy` with `Inverse.Right` upgrades any `LinearHomotopyInverse f` to a
two-sided `HomotopyEquiv AA BB` and proves `f.IsHomotopyEquiv ↔ Nonempty (LinearHomotopyInverse f)`.

## Main definitions

* `TauCeti.AInfinityHom.homotopyOfRightHomotopy`: Vogt upgrade to `Homotopy (g.comp f) (id AA)`.
* `TauCeti.AInfinityHom.LinearHomotopyInverse.homotopyEquiv`, `HomotopyEquiv.trans`, and
  `TauCeti.AInfinityHom.IsHomotopyEquiv`: bundled and unbundled `A∞` homotopy equivalences.

## Main results

* `TauCeti.AInfinityHom.isHomotopyEquiv_iff_nonempty_linearHomotopyInverse`: over any commutative
  ring, `f.IsHomotopyEquiv ↔ Nonempty (LinearHomotopyInverse f)`.
* `TauCeti.AInfinityHom.IsIso.isHomotopyEquiv`, `IsHomotopyEquiv.isQuasiIso`,
  `Homotopy.isHomotopyEquiv_iff`, and `IsHomotopyEquiv.comp`.

## References

* R. M. Vogt, *Homotopy limits and colimits*, Math. Z. 134 (1973), 11--52.
* K. Lefèvre-Hasegawa, *Sur les A-infini catégories*, thèse de doctorat, Université Paris 7
  (2003), Chapter 1, Theorem 1.3.1.2.
-/

public section

namespace TauCeti

open ReducedTensorWords

universe uR uA uB uC

namespace AInfinityHom

variable {R : Type uR} [CommRing R]

/-! ### Vogt upgrading of right homotopies to left homotopies -/

section Vogt

variable {A : Type uA} {B : Type uB} [AddCommGroup A] [Module R A] [AddCommGroup B] [Module R B]
  {AA : AInfinityAlgebra R A} {BB : AInfinityAlgebra R B}

/-- Construct a reduced transformation of degree `p` from its homogeneous Taylor map. -/
private noncomputable def cochainOfTaylor (u v : AInfinityHom AA BB) (p : ℤ)
    (φ : ReducedTensorWords R A →ₗ[R] B)
    (hφ : LinearMap.IsHomogeneous φ (gradedPiece (AA.grading.shift 1))
      (BB.grading.shift 1).piece p) : reducedTransformationCochains u v p :=
  ⟨gradedCoderivAlong (AA.grading.shift 1) p u.barMap v.barMap φ,
    mem_reducedTransformationCochains_iff.2
      ⟨isGradedCoderivationAlong_gradedCoderivAlong _ p u.isCoalgHom_barMap v.isCoalgHom_barMap φ,
        isHomogeneous_gradedCoderivAlong (taylor_def u ▸ u.isHomogeneous_taylor)
          v.isHomogeneous_barMap hφ⟩⟩

private theorem taylor_cochainOfTaylor (u v : AInfinityHom AA BB) (p : ℤ)
    (φ : ReducedTensorWords R A →ₗ[R] B) (hφ) :
    reducedTransformationCochains.taylor (cochainOfTaylor u v p φ hφ) = φ := by
  rw [reducedTransformationCochains.taylor_def]
  exact letter_comp_gradedCoderivAlong _ p _ _ φ

private theorem cochainOfTaylor_add (u v : AInfinityHom AA BB) (p : ℤ)
    (φ₁ φ₂ : ReducedTensorWords R A →ₗ[R] B) (h₁ h₂) :
    cochainOfTaylor u v p (φ₁ + φ₂) (h₁.add h₂) =
      cochainOfTaylor u v p φ₁ h₁ + cochainOfTaylor u v p φ₂ h₂ :=
  Subtype.ext (gradedCoderivAlong_add _ p _ _ φ₁ φ₂)

private theorem taylor_sub_cochain {u v : AInfinityHom AA BB} {p : ℤ}
    (D D' : reducedTransformationCochains u v p) :
    reducedTransformationCochains.taylor (D - D') =
      reducedTransformationCochains.taylor D - reducedTransformationCochains.taylor D' := by
  apply eq_sub_of_add_eq
  rw [← reducedTransformationCochains.taylor_add, sub_add_cancel]

private noncomputable def diffTo (u v : AInfinityHom AA BB) (p q : ℤ) (hpq : p + 1 = q) :
    reducedTransformationCochains u v p →ₗ[R] reducedTransformationCochains u v q :=
  hpq ▸ reducedTransformationDifferential u v p

private theorem coe_diffTo {u v : AInfinityHom AA BB} (p q : ℤ) (hpq : p + 1 = q)
    (D : reducedTransformationCochains u v p) :
    ((diffTo u v p q hpq D : reducedTransformationCochains u v q) :
      ReducedTensorWords R A →ₗ[R] ReducedTensorWords R B) =
      reducedTransformationDifferential u v p D := by subst hpq; rfl

private theorem taylor_diffTo {u v : AInfinityHom AA BB} (p q : ℤ) (hpq : p + 1 = q)
    (D : reducedTransformationCochains u v p) :
    reducedTransformationCochains.taylor (diffTo u v p q hpq D) =
      reducedTransformationCochains.taylor (reducedTransformationDifferential u v p D) := by
  subst hpq; rfl

private theorem differential_diffTo {u v : AInfinityHom AA BB} {p q : ℤ} {hpq : p + 1 = q}
    (D : reducedTransformationCochains u v p) :
    reducedTransformationDifferential u v q (diffTo u v p q hpq D) = 0 := by
  subst hpq; exact reducedTransformationDifferential_reducedTransformationDifferential p D

private theorem diffTo_diffTo {u v : AInfinityHom AA BB} {p q r : ℤ} {hpq : p + 1 = q}
    {hqr : q + 1 = r} (D : reducedTransformationCochains u v p) :
    diffTo u v q r hqr (diffTo u v p q hpq D) = 0 := by
  subst hpq; subst hqr
  exact reducedTransformationDifferential_reducedTransformationDifferential p D

private theorem diffTo_compRight {C : Type uC} [AddCommGroup C] [Module R C]
    {CC : AInfinityAlgebra R C} {u v : AInfinityHom AA BB} (m : AInfinityHom BB CC)
    {p q : ℤ} {hpq : p + 1 = q} (D : reducedTransformationCochains u v p) :
    diffTo (m.comp u) (m.comp v) p q hpq (reducedTransformationCochains.compRight m p D) =
      reducedTransformationCochains.compRight m q (diffTo u v p q hpq D) := by
  subst hpq; exact reducedTransformationDifferential_compRight m D

private theorem cochain_apply_eq_zero_of_mem_filtration {u v : AInfinityHom AA BB} {p : ℤ}
    (D : reducedTransformationCochains u v p) {k : ℕ}
    (hl : ∀ w ∈ filtration R A k, reducedTransformationCochains.taylor D w = 0)
    {w : ReducedTensorWords R A} (hw : w ∈ filtration R A k) :
    (D : ReducedTensorWords R A →ₗ[R] ReducedTensorWords R B) w = 0 :=
  (reducedTransformationCochains.isGradedCoderivationAlong D).apply_eq_of_mem_filtration
    (isGradedCoderivationAlong_zero _ p _ _) (fun _ _ ↦ rfl) (fun _ _ ↦ rfl)
    (fun z hz ↦ by
      simpa only [← LinearMap.comp_apply (letter R B), ← reducedTransformationCochains.taylor_def,
        LinearMap.zero_apply, map_zero] using hl z hz) hw

/-- Top-arity differential formula in the complex of reduced transformations: if `D` vanishes on
`filtration k`, its differential on length `k + 1` is the linear commutator with the unary
differentials. -/
private theorem taylor_differential_comp_lengthProj {u v : AInfinityHom AA BB} {p : ℤ}
    (D : reducedTransformationCochains u v p) {k : ℕ}
    (hl : ∀ w ∈ filtration R A k, reducedTransformationCochains.taylor D w = 0) :
    reducedTransformationCochains.taylor (reducedTransformationDifferential u v p D) ∘ₗ
        lengthProj R A ⟨k + 1, k.succ_pos⟩ =
      BB.differential ∘ₗ
          (reducedTransformationCochains.taylor D ∘ₗ lengthProj R A ⟨k + 1, k.succ_pos⟩) -
        p.negOnePow • ((reducedTransformationCochains.taylor D ∘ₗ
          lengthProj R A ⟨k + 1, k.succ_pos⟩) ∘ₗ AA.unaryBarDifferential) := by
  refine LinearMap.ext fun w ↦ ?_
  set pr := lengthProj R A ⟨k + 1, k.succ_pos⟩
  have hpz : pr w ∈ filtration R A (k + 1) :=
    lengthProj_mem_filtration R A ⟨k + 1, k.succ_pos⟩ w
  have hl' : ∀ u ∈ filtration R A k,
      (letter R B ∘ₗ (D : ReducedTensorWords R A →ₗ[R] ReducedTensorWords R B)) u = 0 :=
    fun u hu ↦ by rw [← reducedTransformationCochains.taylor_def]; exact hl u hu
  have hD : (D : ReducedTensorWords R A →ₗ[R] ReducedTensorWords R B) (pr w) =
      ofLetter R B (reducedTransformationCochains.taylor D (pr w)) := by
    rw [reducedTransformationCochains.taylor_def, LinearMap.comp_apply]
    have hc := reducedTransformationCochains.isGradedCoderivationAlong D
    exact hc.apply_eq_ofLetter_of_mem_filtration hl' hpz
  have hhi : reducedTransformationCochains.taylor D (AA.higherBarDifferential (pr w)) = 0 :=
    hl _ (AA.higherBarDifferential_filtration k ⟨pr w, hpz, rfl⟩)
  have hun : AA.unaryBarDifferential (pr w) ∈ filtration R A (k + 1) :=
    AA.unaryBarDifferential_filtration (k + 1) ⟨pr w, hpz, rfl⟩
  have hpu : reducedTransformationCochains.taylor D (AA.unaryBarDifferential (pr w)) =
      reducedTransformationCochains.taylor D (pr (AA.unaryBarDifferential w)) := by
    rw [← apply_lengthProj_of_mem_filtration R A hl hun]
    have hc := LinearMap.congr_fun (AA.lengthProj_comp_unaryBarDifferential ⟨k + 1, k.succ_pos⟩) w
    simp only [LinearMap.comp_apply] at hc
    simp only [pr, ← hc, lengthProj_lengthProj]
  have hd := LinearMap.congr_fun
    (reducedTransformationCochains.taylor_reducedTransformationDifferential D) (pr w)
  simp only [LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.comp_apply,
    AA.barDifferential_eq_unary_add_higher, LinearMap.add_apply, map_add, hhi, add_zero, hD,
    AInfinityAlgebra.taylor_ofLetter, ← AInfinityAlgebra.differential_apply, hpu] at hd
  exact hd

private theorem taylor_compRight_comp_lengthProj {C : Type uC} [AddCommGroup C] [Module R C]
    {CC : AInfinityAlgebra R C} {u v : AInfinityHom AA BB} {p : ℤ}
    (m : AInfinityHom BB CC) (D : reducedTransformationCochains u v p) {k : ℕ}
    (hl : ∀ w ∈ filtration R A k, reducedTransformationCochains.taylor D w = 0) :
    reducedTransformationCochains.taylor (reducedTransformationCochains.compRight m p D) ∘ₗ
        lengthProj R A ⟨k + 1, k.succ_pos⟩ =
      m.linearPart ∘ₗ
        (reducedTransformationCochains.taylor D ∘ₗ lengthProj R A ⟨k + 1, k.succ_pos⟩) := by
  refine LinearMap.ext fun w ↦ ?_
  set pr := lengthProj R A ⟨k + 1, k.succ_pos⟩
  have hpz : pr w ∈ filtration R A (k + 1) :=
    lengthProj_mem_filtration R A ⟨k + 1, k.succ_pos⟩ w
  have hl' : ∀ u ∈ filtration R A k,
      (letter R B ∘ₗ (D : ReducedTensorWords R A →ₗ[R] ReducedTensorWords R B)) u = 0 :=
    fun u hu ↦ by rw [← reducedTransformationCochains.taylor_def]; exact hl u hu
  have hD : (D : ReducedTensorWords R A →ₗ[R] ReducedTensorWords R B) (pr w) =
      ofLetter R B (reducedTransformationCochains.taylor D (pr w)) := by
    rw [reducedTransformationCochains.taylor_def, LinearMap.comp_apply]
    have hc := reducedTransformationCochains.isGradedCoderivationAlong D
    exact hc.apply_eq_ofLetter_of_mem_filtration hl' hpz
  simp only [reducedTransformationCochains.taylor_compRight, LinearMap.comp_apply, hD,
    linearPart_apply]

/-- Vogt's adjoint linear chain homotopy `h_A' = h_A ∘ (1 - g₁ ∘ f₁) + g₁ ∘ h_B ∘ f₁`. -/
private noncomputable def adjointHomotopy (f : AInfinityHom AA BB) (g : AInfinityHom BB AA)
    (hB : B →ₗ[R] B) (hA : A →ₗ[R] A) : A →ₗ[R] A :=
  hA ∘ₗ (LinearMap.id - g.linearPart ∘ₗ f.linearPart) + g.linearPart ∘ₗ hB ∘ₗ f.linearPart

private theorem isHomogeneous_adjointHomotopy (f : AInfinityHom AA BB) (g : AInfinityHom BB AA)
    (hR : Homotopy (f.comp g) (AInfinityHom.id BB)) {hA : A →ₗ[R] A}
    (hhA : LinearMap.IsHomogeneous hA AA.grading.piece AA.grading.piece (-1)) :
    LinearMap.IsHomogeneous (adjointHomotopy f g hR.linearHomotopy hA) AA.grading.piece
      AA.grading.piece (-1) := by
  have hgf₀ : LinearMap.IsHomogeneous (g.linearPart ∘ₗ f.linearPart)
      AA.grading.piece AA.grading.piece 0 := by
    simpa only [add_zero] using g.isHomogeneous_linearPart.comp f.isHomogeneous_linearPart
  have h₁ : LinearMap.IsHomogeneous (hA ∘ₗ (LinearMap.id - g.linearPart ∘ₗ f.linearPart))
      AA.grading.piece AA.grading.piece (-1) := by
    simpa only [zero_add] using hhA.comp ((LinearMap.isHomogeneous_id _).sub hgf₀)
  have h₂ : LinearMap.IsHomogeneous (g.linearPart ∘ₗ hR.linearHomotopy ∘ₗ f.linearPart)
      AA.grading.piece AA.grading.piece (-1) := by
    simpa only [add_zero, zero_add] using g.isHomogeneous_linearPart.comp
      (hR.isHomogeneous_linearHomotopy.comp f.isHomogeneous_linearPart)
  exact h₁.add h₂

private theorem diff_apply_of_chain_eq {M : Type*} [AddCommGroup M] [Module R M]
    {d f' h : M →ₗ[R] M} (heq : f' - LinearMap.id = d ∘ₗ h + h ∘ₗ d) (x : M) :
    d (h x) = f' x - x - h (d x) := by
  have hx := LinearMap.congr_fun heq x
  simp only [LinearMap.sub_apply, LinearMap.add_apply, LinearMap.comp_apply, LinearMap.id_apply]
    at hx
  exact eq_sub_of_add_eq hx.symm

private theorem adjointHomotopy_chain_eq (f : AInfinityHom AA BB) (g : AInfinityHom BB AA)
    (hR : Homotopy (f.comp g) (AInfinityHom.id BB)) {hA : A →ₗ[R] A}
    (hhA_eq : g.linearPart ∘ₗ f.linearPart - LinearMap.id =
      AA.differential ∘ₗ hA + hA ∘ₗ AA.differential) :
    g.linearPart ∘ₗ f.linearPart - LinearMap.id =
      AA.differential ∘ₗ adjointHomotopy f g hR.linearHomotopy hA +
        adjointHomotopy f g hR.linearHomotopy hA ∘ₗ AA.differential := by
  ext a
  have hBeq : f.linearPart ∘ₗ g.linearPart - LinearMap.id =
      BB.differential ∘ₗ hR.linearHomotopy + hR.linearHomotopy ∘ₗ BB.differential := by
    simpa only [linearPart_comp, linearPart_id] using hR.linearPart_sub_linearPart_eq
  have hdf : ∀ x, BB.differential (f.linearPart x) = f.linearPart (AA.differential x) :=
    LinearMap.congr_fun f.differential_comp_linearPart
  have hdg : ∀ b, AA.differential (g.linearPart b) = g.linearPart (BB.differential b) :=
    LinearMap.congr_fun g.differential_comp_linearPart
  simp only [adjointHomotopy, LinearMap.add_apply, LinearMap.sub_apply, LinearMap.comp_apply,
    LinearMap.id_apply, diff_apply_of_chain_eq hhA_eq, hdg, diff_apply_of_chain_eq hBeq, hdf,
    map_sub, map_add]
  abel

/-- Vogt's linear 2-homotopy `m₁ = h_B ∘ f₁ ∘ h_A - f₁ ∘ h_A² - h_B² ∘ f₁` witnessing
`d_B ∘ m₁ - m₁ ∘ d_A = h_B ∘ f₁ - f₁ ∘ h_A'`. -/
private noncomputable def vogtTwoHomotopy (f : AInfinityHom AA BB) (hB : B →ₗ[R] B)
    (hA : A →ₗ[R] A) : A →ₗ[R] B :=
  hB ∘ₗ f.linearPart ∘ₗ hA - f.linearPart ∘ₗ hA ∘ₗ hA - hB ∘ₗ hB ∘ₗ f.linearPart

private theorem isHomogeneous_vogtTwoHomotopy (f : AInfinityHom AA BB) {g : AInfinityHom BB AA}
    (hR : Homotopy (f.comp g) (AInfinityHom.id BB)) {hA : A →ₗ[R] A}
    (hhA : LinearMap.IsHomogeneous hA AA.grading.piece AA.grading.piece (-1)) :
    LinearMap.IsHomogeneous (vogtTwoHomotopy f hR.linearHomotopy hA) AA.grading.piece
      BB.grading.piece (-2) := by
  have hneg2 : (-1 : ℤ) + -1 = -2 := by decide
  have hB := hR.isHomogeneous_linearHomotopy
  have hf₁ := f.isHomogeneous_linearPart
  have t₁ : LinearMap.IsHomogeneous (hR.linearHomotopy ∘ₗ f.linearPart ∘ₗ hA)
      AA.grading.piece BB.grading.piece (-2) := by
    simpa only [add_zero, hneg2] using hB.comp (hf₁.comp hhA)
  have t₂ : LinearMap.IsHomogeneous (f.linearPart ∘ₗ hA ∘ₗ hA)
      AA.grading.piece BB.grading.piece (-2) := by
    have hhAA : LinearMap.IsHomogeneous (hA ∘ₗ hA) AA.grading.piece AA.grading.piece (-2) := by
      simpa only [hneg2] using hhA.comp hhA
    simpa only [add_zero] using hf₁.comp hhAA
  have t₃ : LinearMap.IsHomogeneous (hR.linearHomotopy ∘ₗ hR.linearHomotopy ∘ₗ f.linearPart)
      AA.grading.piece BB.grading.piece (-2) := by
    have hhBf : LinearMap.IsHomogeneous (hR.linearHomotopy ∘ₗ f.linearPart)
        AA.grading.piece BB.grading.piece (-1) := by
      simpa only [zero_add] using hB.comp hf₁
    simpa only [hneg2] using hB.comp hhBf
  exact (t₁.sub t₂).sub t₃

private theorem vogtTwoHomotopy_diff_eq (f : AInfinityHom AA BB) (g : AInfinityHom BB AA)
    (hR : Homotopy (f.comp g) (AInfinityHom.id BB)) {hA : A →ₗ[R] A}
    (hhA_eq : g.linearPart ∘ₗ f.linearPart - LinearMap.id =
      AA.differential ∘ₗ hA + hA ∘ₗ AA.differential) :
    BB.differential ∘ₗ vogtTwoHomotopy f hR.linearHomotopy hA -
        vogtTwoHomotopy f hR.linearHomotopy hA ∘ₗ AA.differential =
      hR.linearHomotopy ∘ₗ f.linearPart -
        f.linearPart ∘ₗ adjointHomotopy f g hR.linearHomotopy hA := by
  ext a
  have hBeq : f.linearPart ∘ₗ g.linearPart - LinearMap.id =
      BB.differential ∘ₗ hR.linearHomotopy + hR.linearHomotopy ∘ₗ BB.differential := by
    simpa only [linearPart_comp, linearPart_id] using hR.linearPart_sub_linearPart_eq
  have hdf : ∀ x, BB.differential (f.linearPart x) = f.linearPart (AA.differential x) :=
    LinearMap.congr_fun f.differential_comp_linearPart
  simp only [vogtTwoHomotopy, adjointHomotopy, LinearMap.sub_apply, LinearMap.add_apply,
    LinearMap.comp_apply, LinearMap.id_apply, diff_apply_of_chain_eq hBeq, hdf,
    diff_apply_of_chain_eq hhA_eq, map_sub, map_add]
  abel

/-- `h_R.barHomotopy ∘ f.barMap` packaged as a degree-`-1` reduced transformation from
`f.comp (g.comp f)` to `f.comp (AInfinityHom.id AA)`. -/
private noncomputable def rightHomotopyCompF (f : AInfinityHom AA BB) (g : AInfinityHom BB AA)
    (hR : Homotopy (f.comp g) (AInfinityHom.id BB)) :
    reducedTransformationCochains (f.comp (g.comp f)) (f.comp (AInfinityHom.id AA)) (-1) :=
  ⟨hR.barHomotopy ∘ₗ f.barMap, mem_reducedTransformationCochains_iff.2 <| by
    have hc := hR.isGradedCoderivationAlong_barHomotopy.comp_isCoalgHom f.isCoalgHom_barMap
      f.isHomogeneous_barMap
    simp only [barMap_comp, barMap_id, LinearMap.id_comp, LinearMap.comp_assoc] at hc
    refine ⟨isGradedCoderivationAlong_neg_iff.2 ?_,
      by simpa only [zero_add] using hR.isHomogeneous_barHomotopy.comp f.isHomogeneous_barMap⟩
    simpa only [barMap_comp, barMap_id, LinearMap.comp_id, LinearMap.comp_assoc] using hc⟩

private theorem coe_rightHomotopyCompF (f : AInfinityHom AA BB) (g : AInfinityHom BB AA)
    (hR : Homotopy (f.comp g) (AInfinityHom.id BB)) :
    (rightHomotopyCompF f g hR : ReducedTensorWords R A →ₗ[R] ReducedTensorWords R B) =
      hR.barHomotopy ∘ₗ f.barMap := (rfl)

private theorem diffTo_rightHomotopyCompF (f : AInfinityHom AA BB) (g : AInfinityHom BB AA)
    (hR : Homotopy (f.comp g) (AInfinityHom.id BB)) :
    diffTo (f.comp (g.comp f)) (f.comp (AInfinityHom.id AA)) (-1) 0 (by decide)
        (rightHomotopyCompF f g hR) =
      ⟨(f.comp (g.comp f)).barMap - (f.comp (AInfinityHom.id AA)).barMap,
        barMap_sub_barMap_mem_reducedTransformationCochains _ _⟩ := by
  apply Subtype.ext
  refine LinearMap.ext fun z ↦ ?_
  have hRz := hR.barMap_sub_barMap_apply (f.barMap z)
  simp only [coe_diffTo, coe_reducedTransformationDifferential_neg_one, coe_rightHomotopyCompF,
    LinearMap.add_apply, LinearMap.sub_apply, LinearMap.comp_apply, barMap_comp, barMap_id,
    LinearMap.id_apply, ← f.barDifferential_barMap] at hRz ⊢
  exact hRz.symm

/-- Inductive state at filtration `k` for Vogt's left-homotopy upgrading. -/
private structure VogtStep (f : AInfinityHom AA BB) (g : AInfinityHom BB AA)
    (hR : Homotopy (f.comp g) (AInfinityHom.id BB)) (k : ℕ) where
  ξ : ReducedTensorWords R A →ₗ[R] A
  μ : ReducedTensorWords R A →ₗ[R] B
  isHomogeneous_ξ :
    LinearMap.IsHomogeneous ξ (gradedPiece (AA.grading.shift 1)) (AA.grading.shift 1).piece (-1)
  isHomogeneous_μ :
    LinearMap.IsHomogeneous μ (gradedPiece (AA.grading.shift 1)) (BB.grading.shift 1).piece (-2)
  vanishes_Q : ∀ w ∈ filtration R A k,
    reducedTransformationCochains.taylor
      (⟨(g.comp f).barMap - (AInfinityHom.id AA).barMap,
          barMap_sub_barMap_mem_reducedTransformationCochains _ _⟩ -
        diffTo (g.comp f) (AInfinityHom.id AA) (-1) 0 (by decide)
          (cochainOfTaylor (g.comp f) (AInfinityHom.id AA) (-1) ξ isHomogeneous_ξ)) w = 0
  vanishes_S : ∀ w ∈ filtration R A k,
    reducedTransformationCochains.taylor
      (rightHomotopyCompF f g hR -
        reducedTransformationCochains.compRight f (-1)
          (cochainOfTaylor (g.comp f) (AInfinityHom.id AA) (-1) ξ isHomogeneous_ξ) -
        diffTo (f.comp (g.comp f)) (f.comp (AInfinityHom.id AA)) (-2) (-1) (by decide)
          (cochainOfTaylor (f.comp (g.comp f)) (f.comp (AInfinityHom.id AA)) (-2) μ
            isHomogeneous_μ)) w = 0

namespace VogtStep

variable {f : AInfinityHom AA BB} {g : AInfinityHom BB AA}
  {hR : Homotopy (f.comp g) (AInfinityHom.id BB)} {k : ℕ}

private noncomputable def cochainQ (V : VogtStep f g hR k) :
    reducedTransformationCochains (g.comp f) (AInfinityHom.id AA) 0 :=
  ⟨(g.comp f).barMap - (AInfinityHom.id AA).barMap,
      barMap_sub_barMap_mem_reducedTransformationCochains _ _⟩ -
    diffTo (g.comp f) (AInfinityHom.id AA) (-1) 0 (by decide)
      (cochainOfTaylor (g.comp f) (AInfinityHom.id AA) (-1) V.ξ V.isHomogeneous_ξ)

private noncomputable def cochainS (V : VogtStep f g hR k) :
    reducedTransformationCochains (f.comp (g.comp f)) (f.comp (AInfinityHom.id AA)) (-1) :=
  rightHomotopyCompF f g hR -
    reducedTransformationCochains.compRight f (-1)
      (cochainOfTaylor (g.comp f) (AInfinityHom.id AA) (-1) V.ξ V.isHomogeneous_ξ) -
    diffTo (f.comp (g.comp f)) (f.comp (AInfinityHom.id AA)) (-2) (-1) (by decide)
      (cochainOfTaylor (f.comp (g.comp f)) (f.comp (AInfinityHom.id AA)) (-2) V.μ
        V.isHomogeneous_μ)

private noncomputable def topQ (V : VogtStep f g hR k) : ReducedTensorWords R A →ₗ[R] A :=
  reducedTransformationCochains.taylor V.cochainQ ∘ₗ lengthProj R A ⟨k + 1, k.succ_pos⟩

private noncomputable def topS (V : VogtStep f g hR k) : ReducedTensorWords R A →ₗ[R] B :=
  reducedTransformationCochains.taylor V.cochainS ∘ₗ lengthProj R A ⟨k + 1, k.succ_pos⟩

private theorem differential_cochainQ (V : VogtStep f g hR k) :
    reducedTransformationDifferential (g.comp f) (AInfinityHom.id AA) 0 V.cochainQ = 0 := by
  rw [cochainQ, map_sub, reducedTransformationDifferential_barMap_sub_barMap,
    differential_diffTo, sub_self]

private theorem differential_cochainS (V : VogtStep f g hR k) :
    diffTo (f.comp (g.comp f)) (f.comp (AInfinityHom.id AA)) (-1) 0 (by decide) V.cochainS =
      reducedTransformationCochains.compRight f 0 V.cochainQ := by
  rw [cochainS, map_sub, map_sub, diffTo_rightHomotopyCompF, diffTo_compRight,
    diffTo_diffTo, sub_zero, cochainQ, map_sub]
  congr 1
  apply Subtype.ext
  simp only [reducedTransformationCochains.coe_compRight, barMap_comp, LinearMap.comp_sub]

private theorem topQ_closed (V : VogtStep f g hR k) :
    AA.differential ∘ₗ V.topQ = V.topQ ∘ₗ AA.unaryBarDifferential := by
  have h := taylor_differential_comp_lengthProj V.cochainQ V.vanishes_Q
  rw [V.differential_cochainQ, reducedTransformationCochains.taylor_zero, LinearMap.zero_comp,
    Int.negOnePow_zero, one_smul] at h
  exact sub_eq_zero.1 h.symm

private theorem topS_diff_eq (V : VogtStep f g hR k) :
    BB.differential ∘ₗ V.topS + V.topS ∘ₗ AA.unaryBarDifferential =
      f.linearPart ∘ₗ V.topQ := by
  have h := taylor_differential_comp_lengthProj V.cochainS V.vanishes_S
  rw [← taylor_diffTo (u := f.comp (g.comp f)) (v := f.comp (AInfinityHom.id AA)) (-1) 0
      (by decide) V.cochainS, V.differential_cochainS,
    taylor_compRight_comp_lengthProj f V.cochainQ V.vanishes_Q, Int.negOnePow_neg,
    Int.negOnePow_one, Units.neg_smul, one_smul, sub_neg_eq_add] at h
  exact h.symm

private noncomputable def deltaXi (V : VogtStep f g hR k) (hA' : A →ₗ[R] A) :
    ReducedTensorWords R A →ₗ[R] A :=
  g.linearPart ∘ₗ V.topS - hA' ∘ₗ V.topQ

private noncomputable def deltaMu (V : VogtStep f g hR k) (hA' : A →ₗ[R] A) :
    ReducedTensorWords R A →ₗ[R] B :=
  -(hR.linearHomotopy ∘ₗ (V.topS - f.linearPart ∘ₗ V.deltaXi hA') +
    f.linearPart ∘ₗ hA' ∘ₗ V.deltaXi hA')

private theorem isHomogeneous_deltaXi (V : VogtStep f g hR k) {hA' : A →ₗ[R] A}
    (hhA' : LinearMap.IsHomogeneous hA' AA.grading.piece AA.grading.piece (-1)) :
    LinearMap.IsHomogeneous (V.deltaXi hA') (gradedPiece (AA.grading.shift 1))
      (AA.grading.shift 1).piece (-1) := by
  have hq : LinearMap.IsHomogeneous V.topQ (gradedPiece (AA.grading.shift 1))
      (AA.grading.shift 1).piece 0 := by
    simpa only [topQ, add_zero] using
      (reducedTransformationCochains.isHomogeneous_taylor V.cochainQ).comp
        (isHomogeneous_lengthProj (AA.grading.shift 1) _)
  have hs : LinearMap.IsHomogeneous V.topS (gradedPiece (AA.grading.shift 1))
      (BB.grading.shift 1).piece (-1) := by
    simpa only [topS, zero_add] using
      (reducedTransformationCochains.isHomogeneous_taylor V.cochainS).comp
        (isHomogeneous_lengthProj (AA.grading.shift 1) _)
  have hg₁ := (LinearMap.isHomogeneous_shift_piece_iff (c := 1)).2 g.isHomogeneous_linearPart
  have hhA₁ := (LinearMap.isHomogeneous_shift_piece_iff (c := 1)).2 hhA'
  have h₁ : LinearMap.IsHomogeneous (g.linearPart ∘ₗ V.topS)
      (gradedPiece (AA.grading.shift 1)) (AA.grading.shift 1).piece (-1) := by
    simpa only [add_zero] using hg₁.comp hs
  have h₂ : LinearMap.IsHomogeneous (hA' ∘ₗ V.topQ)
      (gradedPiece (AA.grading.shift 1)) (AA.grading.shift 1).piece (-1) := by
    simpa only [zero_add] using hhA₁.comp hq
  exact h₁.sub h₂

private theorem isHomogeneous_deltaMu (V : VogtStep f g hR k) {hA' : A →ₗ[R] A}
    (hhA' : LinearMap.IsHomogeneous hA' AA.grading.piece AA.grading.piece (-1)) :
    LinearMap.IsHomogeneous (V.deltaMu hA') (gradedPiece (AA.grading.shift 1))
      (BB.grading.shift 1).piece (-2) := by
  have hneg2 : (-1 : ℤ) + -1 = -2 := by decide
  have hs : LinearMap.IsHomogeneous V.topS (gradedPiece (AA.grading.shift 1))
      (BB.grading.shift 1).piece (-1) := by
    simpa only [topS, zero_add] using
      (reducedTransformationCochains.isHomogeneous_taylor V.cochainS).comp
        (isHomogeneous_lengthProj (AA.grading.shift 1) _)
  have hf₁ := (LinearMap.isHomogeneous_shift_piece_iff (c := 1)).2 f.isHomogeneous_linearPart
  have hhA₁ := (LinearMap.isHomogeneous_shift_piece_iff (c := 1)).2 hhA'
  have hhB₁ :=
    (LinearMap.isHomogeneous_shift_piece_iff (c := 1)).2 hR.isHomogeneous_linearHomotopy
  have hdξ := V.isHomogeneous_deltaXi hhA'
  have hfdξ : LinearMap.IsHomogeneous (f.linearPart ∘ₗ V.deltaXi hA')
      (gradedPiece (AA.grading.shift 1)) (BB.grading.shift 1).piece (-1) := by
    simpa only [add_zero] using hf₁.comp hdξ
  have h₁ : LinearMap.IsHomogeneous
      (hR.linearHomotopy ∘ₗ (V.topS - f.linearPart ∘ₗ V.deltaXi hA'))
      (gradedPiece (AA.grading.shift 1)) (BB.grading.shift 1).piece (-2) := by
    simpa only [hneg2] using hhB₁.comp (hs.sub hfdξ)
  have h₂ : LinearMap.IsHomogeneous (f.linearPart ∘ₗ hA' ∘ₗ V.deltaXi hA')
      (gradedPiece (AA.grading.shift 1)) (BB.grading.shift 1).piece (-2) := by
    have hhAdξ : LinearMap.IsHomogeneous (hA' ∘ₗ V.deltaXi hA')
        (gradedPiece (AA.grading.shift 1)) (AA.grading.shift 1).piece (-2) := by
      simpa only [hneg2] using hhA₁.comp hdξ
    simpa only [add_zero] using hf₁.comp hhAdξ
  simpa only [deltaMu, neg_one_smul R] using (h₁.add h₂).smul (-1 : R)

private theorem differential_deltaXi_add (V : VogtStep f g hR k) {hA' : A →ₗ[R] A}
    (hhA'_eq : g.linearPart ∘ₗ f.linearPart - LinearMap.id =
      AA.differential ∘ₗ hA' + hA' ∘ₗ AA.differential) :
    AA.differential ∘ₗ V.deltaXi hA' + V.deltaXi hA' ∘ₗ AA.unaryBarDifferential =
      V.topQ := by
  refine LinearMap.ext fun z ↦ ?_
  have hqz := LinearMap.congr_fun V.topQ_closed z
  have hsz := congrArg g.linearPart (LinearMap.congr_fun V.topS_diff_eq z)
  have hg₁ := LinearMap.congr_fun g.differential_comp_linearPart (V.topS z)
  have hAz := LinearMap.congr_fun hhA'_eq (V.topQ z)
  simp only [deltaXi, LinearMap.sub_apply, LinearMap.add_apply, LinearMap.comp_apply,
    LinearMap.id_apply, map_sub, map_add] at hqz hsz hg₁ hAz ⊢
  rw [← hg₁] at hsz
  rw [hqz] at hAz
  refine sub_eq_zero.1 (Eq.trans ?_ (sub_eq_zero.2 (congrArg₂ (· + ·) hsz hAz)))
  abel

private theorem differential_deltaMu_sub (V : VogtStep f g hR k) {hA' : A →ₗ[R] A}
    (hhA'_eq : g.linearPart ∘ₗ f.linearPart - LinearMap.id =
      AA.differential ∘ₗ hA' + hA' ∘ₗ AA.differential) :
    BB.differential ∘ₗ V.deltaMu hA' - V.deltaMu hA' ∘ₗ AA.unaryBarDifferential =
      V.topS - f.linearPart ∘ₗ V.deltaXi hA' := by
  set dξ := V.deltaXi hA'
  set s' := V.topS - f.linearPart ∘ₗ dξ
  have hdξ := V.differential_deltaXi_add hhA'_eq
  have hs'_anti : s' ∘ₗ AA.unaryBarDifferential = -(BB.differential ∘ₗ s') := by
    refine LinearMap.ext fun z ↦ ?_
    have hsz := LinearMap.congr_fun V.topS_diff_eq z
    have hxz := congrArg f.linearPart (LinearMap.congr_fun hdξ z)
    have hf₁ := LinearMap.congr_fun f.differential_comp_linearPart (dξ z)
    simp only [s', dξ, LinearMap.sub_apply, LinearMap.add_apply, LinearMap.neg_apply,
      LinearMap.comp_apply, map_sub, map_add] at hsz hxz hf₁ ⊢
    rw [← hf₁] at hxz
    refine sub_eq_zero.1 (Eq.trans ?_ (sub_eq_zero.2 (congrArg₂ (· + ·) hsz hxz.symm)))
    abel
  have hgs' : f.linearPart ∘ₗ g.linearPart ∘ₗ s' =
      f.linearPart ∘ₗ hA' ∘ₗ dξ ∘ₗ AA.unaryBarDifferential -
        BB.differential ∘ₗ (f.linearPart ∘ₗ hA' ∘ₗ dξ) := by
    have hg : g.linearPart ∘ₗ s' = hA' ∘ₗ V.topQ -
        (g.linearPart ∘ₗ f.linearPart - LinearMap.id) ∘ₗ dξ := by
      refine LinearMap.ext fun z ↦ ?_
      simp only [s', dξ, deltaXi, LinearMap.sub_apply, LinearMap.comp_apply, LinearMap.id_apply,
        map_sub]
      abel
    rw [hg, hhA'_eq, ← hdξ]
    refine LinearMap.ext fun z ↦ ?_
    have hf₁ := LinearMap.congr_fun f.differential_comp_linearPart (hA' (dξ z))
    simp only [LinearMap.sub_apply, LinearMap.add_apply, LinearMap.comp_apply, map_sub, map_add]
      at hf₁ ⊢
    rw [← hf₁]
    abel
  have hBeq : f.linearPart ∘ₗ g.linearPart - LinearMap.id =
      BB.differential ∘ₗ hR.linearHomotopy + hR.linearHomotopy ∘ₗ BB.differential := by
    simpa only [linearPart_comp, linearPart_id] using hR.linearPart_sub_linearPart_eq
  refine LinearMap.ext fun z ↦ ?_
  have hBz := LinearMap.congr_fun hBeq (s' z)
  have hrc := LinearMap.congr_fun hs'_anti z
  have hgz := LinearMap.congr_fun hgs' z
  simp only [deltaMu, s', dξ, LinearMap.sub_apply, LinearMap.add_apply, LinearMap.neg_apply,
    LinearMap.comp_apply, LinearMap.id_apply, map_neg, map_add] at hBz hrc hgz ⊢
  rw [hrc, map_neg]
  refine sub_eq_zero.1 (Eq.trans ?_ (sub_eq_zero.2 (congrArg₂ (· + ·) hBz hgz.symm)))
  abel

private theorem deltaXi_eq_zero_of_mem_filtration (V : VogtStep f g hR k) (hA' : A →ₗ[R] A)
    {w : ReducedTensorWords R A} (hw : w ∈ filtration R A k) : V.deltaXi hA' w = 0 := by
  have hp := lengthProj_apply_eq_zero_of_mem_filtration R A (n := ⟨k + 1, k.succ_pos⟩)
    (Nat.lt_succ_self k) hw
  simp only [deltaXi, topQ, topS, LinearMap.sub_apply, LinearMap.comp_apply, hp, map_zero, sub_self]

private theorem deltaMu_eq_zero_of_mem_filtration (V : VogtStep f g hR k) (hA' : A →ₗ[R] A)
    {w : ReducedTensorWords R A} (hw : w ∈ filtration R A k) : V.deltaMu hA' w = 0 := by
  have hp := lengthProj_apply_eq_zero_of_mem_filtration R A (n := ⟨k + 1, k.succ_pos⟩)
    (Nat.lt_succ_self k) hw
  have hd := V.deltaXi_eq_zero_of_mem_filtration hA' hw
  simp only [deltaMu, topS, LinearMap.neg_apply, LinearMap.add_apply, LinearMap.sub_apply,
    LinearMap.comp_apply, hp, hd, map_zero, sub_zero, add_zero, neg_zero]

private theorem deltaXi_comp_lengthProj (V : VogtStep f g hR k) (hA' : A →ₗ[R] A) :
    V.deltaXi hA' ∘ₗ lengthProj R A ⟨k + 1, k.succ_pos⟩ = V.deltaXi hA' :=
  LinearMap.ext fun z ↦ by
    simp only [deltaXi, topQ, topS, LinearMap.sub_apply, LinearMap.comp_apply,
      lengthProj_lengthProj]

private theorem deltaMu_comp_lengthProj (V : VogtStep f g hR k) (hA' : A →ₗ[R] A) :
    V.deltaMu hA' ∘ₗ lengthProj R A ⟨k + 1, k.succ_pos⟩ = V.deltaMu hA' :=
  LinearMap.ext fun z ↦ by
    simp only [deltaMu, topS, deltaXi, topQ, LinearMap.neg_apply, LinearMap.add_apply,
      LinearMap.sub_apply, LinearMap.comp_apply, lengthProj_lengthProj]

private theorem next_vanishes_Q (V : VogtStep f g hR k) {hA' : A →ₗ[R] A}
    (hhA' : LinearMap.IsHomogeneous hA' AA.grading.piece AA.grading.piece (-1))
    (hhA'_eq : g.linearPart ∘ₗ f.linearPart - LinearMap.id =
      AA.differential ∘ₗ hA' + hA' ∘ₗ AA.differential) {z : ReducedTensorWords R A}
    (hz : z ∈ filtration R A (k + 1)) :
    reducedTransformationCochains.taylor
      (⟨(g.comp f).barMap - (AInfinityHom.id AA).barMap,
          barMap_sub_barMap_mem_reducedTransformationCochains _ _⟩ -
        diffTo (g.comp f) (AInfinityHom.id AA) (-1) 0 (by decide)
          (cochainOfTaylor (g.comp f) (AInfinityHom.id AA) (-1) (V.ξ + V.deltaXi hA')
            (V.isHomogeneous_ξ.add (V.isHomogeneous_deltaXi hhA')))) z = 0 := by
  set u := g.comp f
  set v := AInfinityHom.id AA
  set Dξ := cochainOfTaylor u v (-1) (V.deltaXi hA') (V.isHomogeneous_deltaXi hhA')
  have hlξ : ∀ w ∈ filtration R A k, reducedTransformationCochains.taylor Dξ w = 0 :=
    fun w hw ↦ by rw [taylor_cochainOfTaylor]; exact V.deltaXi_eq_zero_of_mem_filtration hA' hw
  have hQ' : ⟨u.barMap - v.barMap, barMap_sub_barMap_mem_reducedTransformationCochains u v⟩ -
      diffTo u v (-1) 0 (by decide)
        (cochainOfTaylor u v (-1) (V.ξ + V.deltaXi hA')
          (V.isHomogeneous_ξ.add (V.isHomogeneous_deltaXi hhA'))) =
      V.cochainQ - diffTo u v (-1) 0 (by decide) Dξ := by
    rw [cochainOfTaylor_add, map_add, sub_add_eq_sub_sub]; rfl
  rw [hQ']
  have hlow : ∀ w ∈ filtration R A k,
      reducedTransformationCochains.taylor
        (V.cochainQ - diffTo u v (-1) 0 (by decide) Dξ) w = 0 := fun w hw ↦ by
    rw [taylor_sub_cochain, LinearMap.sub_apply, cochainQ, V.vanishes_Q w hw, zero_sub,
      neg_eq_zero, reducedTransformationCochains.taylor_def, LinearMap.comp_apply, coe_diffTo,
      coe_reducedTransformationDifferential_neg_one, LinearMap.add_apply, LinearMap.comp_apply,
      LinearMap.comp_apply, cochain_apply_eq_zero_of_mem_filtration Dξ hlξ hw,
      cochain_apply_eq_zero_of_mem_filtration Dξ hlξ (AA.barDifferential_mem_filtration hw),
      map_zero, add_zero, map_zero]
  have htop : reducedTransformationCochains.taylor
      (V.cochainQ - diffTo u v (-1) 0 (by decide) Dξ) ∘ₗ
        lengthProj R A ⟨k + 1, k.succ_pos⟩ = 0 := by
    rw [taylor_sub_cochain, LinearMap.sub_comp, taylor_diffTo,
      taylor_differential_comp_lengthProj Dξ hlξ, taylor_cochainOfTaylor,
      V.deltaXi_comp_lengthProj hA', Int.negOnePow_neg, Int.negOnePow_one, Units.neg_smul,
      one_smul, sub_neg_eq_add, V.differential_deltaXi_add hhA'_eq]
    exact sub_self V.topQ
  rw [← apply_lengthProj_of_mem_filtration R A hlow hz, ← LinearMap.comp_apply, htop,
    LinearMap.zero_apply]

private theorem next_vanishes_S (V : VogtStep f g hR k) {hA' : A →ₗ[R] A}
    (hhA' : LinearMap.IsHomogeneous hA' AA.grading.piece AA.grading.piece (-1))
    (hhA'_eq : g.linearPart ∘ₗ f.linearPart - LinearMap.id =
      AA.differential ∘ₗ hA' + hA' ∘ₗ AA.differential) {z : ReducedTensorWords R A}
    (hz : z ∈ filtration R A (k + 1)) :
    reducedTransformationCochains.taylor
      (rightHomotopyCompF f g hR -
        reducedTransformationCochains.compRight f (-1)
          (cochainOfTaylor (g.comp f) (AInfinityHom.id AA) (-1) (V.ξ + V.deltaXi hA')
            (V.isHomogeneous_ξ.add (V.isHomogeneous_deltaXi hhA'))) -
        diffTo (f.comp (g.comp f)) (f.comp (AInfinityHom.id AA)) (-2) (-1) (by decide)
          (cochainOfTaylor (f.comp (g.comp f)) (f.comp (AInfinityHom.id AA)) (-2)
            (V.μ + V.deltaMu hA')
            (V.isHomogeneous_μ.add (V.isHomogeneous_deltaMu hhA')))) z = 0 := by
  set u := g.comp f
  set v := AInfinityHom.id AA
  set Dξ := cochainOfTaylor u v (-1) (V.deltaXi hA') (V.isHomogeneous_deltaXi hhA')
  set Dμ := cochainOfTaylor (f.comp u) (f.comp v) (-2) (V.deltaMu hA')
    (V.isHomogeneous_deltaMu hhA')
  have hlξ : ∀ w ∈ filtration R A k, reducedTransformationCochains.taylor Dξ w = 0 :=
    fun w hw ↦ by rw [taylor_cochainOfTaylor]; exact V.deltaXi_eq_zero_of_mem_filtration hA' hw
  have hlμ : ∀ w ∈ filtration R A k, reducedTransformationCochains.taylor Dμ w = 0 :=
    fun w hw ↦ by rw [taylor_cochainOfTaylor]; exact V.deltaMu_eq_zero_of_mem_filtration hA' hw
  have hS' : rightHomotopyCompF f g hR -
      reducedTransformationCochains.compRight f (-1)
        (cochainOfTaylor u v (-1) (V.ξ + V.deltaXi hA')
          (V.isHomogeneous_ξ.add (V.isHomogeneous_deltaXi hhA'))) -
      diffTo (f.comp u) (f.comp v) (-2) (-1) (by decide)
        (cochainOfTaylor (f.comp u) (f.comp v) (-2) (V.μ + V.deltaMu hA')
          (V.isHomogeneous_μ.add (V.isHomogeneous_deltaMu hhA'))) =
      V.cochainS - reducedTransformationCochains.compRight f (-1) Dξ -
        diffTo (f.comp u) (f.comp v) (-2) (-1) (by decide) Dμ := by
    rw [cochainOfTaylor_add u v (-1) V.ξ (V.deltaXi hA') V.isHomogeneous_ξ
        (V.isHomogeneous_deltaXi hhA'),
      cochainOfTaylor_add (f.comp u) (f.comp v) (-2) V.μ (V.deltaMu hA') V.isHomogeneous_μ
        (V.isHomogeneous_deltaMu hhA'),
      map_add, map_add, sub_add_eq_sub_sub, sub_add_eq_sub_sub,
      sub_right_comm _ (reducedTransformationCochains.compRight f (-1) Dξ)]
    rfl
  rw [hS']
  set S' := V.cochainS - reducedTransformationCochains.compRight f (-1) Dξ -
    diffTo (f.comp u) (f.comp v) (-2) (-1) (by decide) Dμ
  have hlow : ∀ w ∈ filtration R A k, reducedTransformationCochains.taylor S' w = 0 :=
    fun w hw ↦ by
      rw [taylor_sub_cochain, taylor_sub_cochain, LinearMap.sub_apply, LinearMap.sub_apply,
        cochainS, V.vanishes_S w hw, reducedTransformationCochains.taylor_compRight,
        LinearMap.comp_apply, cochain_apply_eq_zero_of_mem_filtration Dξ hlξ hw, map_zero, sub_self,
        zero_sub, neg_eq_zero, reducedTransformationCochains.taylor_def, LinearMap.comp_apply,
        coe_diffTo, coe_reducedTransformationDifferential, LinearMap.sub_apply,
        LinearMap.smul_apply, LinearMap.comp_apply, LinearMap.comp_apply,
        cochain_apply_eq_zero_of_mem_filtration Dμ hlμ hw,
        cochain_apply_eq_zero_of_mem_filtration Dμ hlμ (AA.barDifferential_mem_filtration hw),
        map_zero, smul_zero, sub_self, map_zero]
  have hneg2 : (-2 : ℤ).negOnePow = 1 := by decide
  have htop : reducedTransformationCochains.taylor S' ∘ₗ
      lengthProj R A ⟨k + 1, k.succ_pos⟩ = 0 := by
    rw [taylor_sub_cochain, taylor_sub_cochain, LinearMap.sub_comp, LinearMap.sub_comp,
      taylor_compRight_comp_lengthProj f Dξ hlξ, taylor_diffTo,
      taylor_differential_comp_lengthProj Dμ hlμ, taylor_cochainOfTaylor, taylor_cochainOfTaylor,
      V.deltaXi_comp_lengthProj hA', V.deltaMu_comp_lengthProj hA', hneg2, one_smul,
      V.differential_deltaMu_sub hhA'_eq]
    exact sub_self _
  rw [← apply_lengthProj_of_mem_filtration R A hlow hz, ← LinearMap.comp_apply, htop,
    LinearMap.zero_apply]

/-- Inductive step from filtration `k` to filtration `k + 1` in Vogt's upgrading. -/
private noncomputable def next (V : VogtStep f g hR k) {hA' : A →ₗ[R] A}
    (hhA' : LinearMap.IsHomogeneous hA' AA.grading.piece AA.grading.piece (-1))
    (hhA'_eq : g.linearPart ∘ₗ f.linearPart - LinearMap.id =
      AA.differential ∘ₗ hA' + hA' ∘ₗ AA.differential) : VogtStep f g hR (k + 1) where
  ξ := V.ξ + V.deltaXi hA'
  μ := V.μ + V.deltaMu hA'
  isHomogeneous_ξ := V.isHomogeneous_ξ.add (V.isHomogeneous_deltaXi hhA')
  isHomogeneous_μ := V.isHomogeneous_μ.add (V.isHomogeneous_deltaMu hhA')
  vanishes_Q _ hz := V.next_vanishes_Q hhA' hhA'_eq hz
  vanishes_S _ hz := V.next_vanishes_S hhA' hhA'_eq hz

end VogtStep

private noncomputable def vogtBase (f : AInfinityHom AA BB) (g : AInfinityHom BB AA)
    (hR : Homotopy (f.comp g) (AInfinityHom.id BB)) {hA : A →ₗ[R] A}
    (hhA : LinearMap.IsHomogeneous hA AA.grading.piece AA.grading.piece (-1))
    (hhA_eq : g.linearPart ∘ₗ f.linearPart - LinearMap.id =
      AA.differential ∘ₗ hA + hA ∘ₗ AA.differential) : VogtStep f g hR 1 := by
  have hξ : LinearMap.IsHomogeneous (adjointHomotopy f g hR.linearHomotopy hA ∘ₗ letter R A)
      (gradedPiece (AA.grading.shift 1)) (AA.grading.shift 1).piece (-1) := by
    simpa only [zero_add] using
      (LinearMap.isHomogeneous_shift_piece_iff.2
        (isHomogeneous_adjointHomotopy f g hR hhA)).comp (isHomogeneous_letter (AA.grading.shift 1))
  have hμ : LinearMap.IsHomogeneous (vogtTwoHomotopy f hR.linearHomotopy hA ∘ₗ letter R A)
      (gradedPiece (AA.grading.shift 1)) (BB.grading.shift 1).piece (-2) := by
    simpa only [zero_add] using
      (LinearMap.isHomogeneous_shift_piece_iff.2
        (isHomogeneous_vogtTwoHomotopy f hR hhA)).comp (isHomogeneous_letter (AA.grading.shift 1))
  refine ⟨_, _, hξ, hμ, ?_, ?_⟩
  · simp only [taylor_sub_cochain, taylor_diffTo]
    apply apply_eq_zero_of_mem_filtration_one R A
    refine LinearMap.ext fun a ↦ ?_
    have ha := LinearMap.congr_fun (adjointHomotopy_chain_eq f g hR hhA_eq) a
    simp only [reducedTransformationCochains.taylor_def,
      coe_reducedTransformationDifferential_neg_one, cochainOfTaylor, LinearMap.comp_apply,
      LinearMap.sub_apply, LinearMap.add_apply, LinearMap.zero_apply, barMap_comp, barMap_id,
      LinearMap.id_apply, f.barMap_ofLetter, g.barMap_ofLetter, gradedCoderivAlong_ofLetter,
      AInfinityAlgebra.barDifferential_ofLetter, ← AInfinityAlgebra.differential_apply,
      map_sub, map_add, letter_ofLetter] at ha ⊢
    exact sub_eq_zero.2 ha
  · simp only [taylor_sub_cochain, taylor_diffTo]
    apply apply_eq_zero_of_mem_filtration_one R A
    refine LinearMap.ext fun a ↦ ?_
    have ha := LinearMap.congr_fun (vogtTwoHomotopy_diff_eq f g hR hhA_eq) a
    have hneg2 : (-2 : ℤ).negOnePow = 1 := by decide
    simp only [reducedTransformationCochains.taylor_def,
      reducedTransformationCochains.coe_compRight, coe_reducedTransformationDifferential, hneg2,
      one_smul, coe_rightHomotopyCompF, cochainOfTaylor, LinearMap.comp_apply, LinearMap.sub_apply,
      LinearMap.zero_apply, f.barMap_ofLetter, hR.barHomotopy_ofLetter, gradedCoderivAlong_ofLetter,
      AInfinityAlgebra.barDifferential_ofLetter, ← AInfinityAlgebra.differential_apply, map_sub,
      letter_ofLetter] at ha ⊢
    exact sub_eq_zero.2 ha.symm

private noncomputable def vogtSeq (f : AInfinityHom AA BB) (g : AInfinityHom BB AA)
    (hR : Homotopy (f.comp g) (AInfinityHom.id BB)) {hA : A →ₗ[R] A}
    (hhA : LinearMap.IsHomogeneous hA AA.grading.piece AA.grading.piece (-1))
    (hhA_eq : g.linearPart ∘ₗ f.linearPart - LinearMap.id =
      AA.differential ∘ₗ hA + hA ∘ₗ AA.differential) : (k : ℕ) → VogtStep f g hR k
  | 0 =>
      let b := vogtBase f g hR hhA hhA_eq
      ⟨b.ξ, b.μ, b.isHomogeneous_ξ, b.isHomogeneous_μ,
        fun w hw ↦ b.vanishes_Q w (filtration_monotone R A (Nat.zero_le 1) hw),
        fun w hw ↦ b.vanishes_S w (filtration_monotone R A (Nat.zero_le 1) hw)⟩
  | 1 => vogtBase f g hR hhA hhA_eq
  | k + 2 =>
      (vogtSeq f g hR hhA hhA_eq (k + 1)).next (isHomogeneous_adjointHomotopy f g hR hhA)
        (adjointHomotopy_chain_eq f g hR hhA_eq)

private noncomputable def vogtTaylor (f : AInfinityHom AA BB) (g : AInfinityHom BB AA)
    (hR : Homotopy (f.comp g) (AInfinityHom.id BB)) {hA : A →ₗ[R] A}
    (hhA : LinearMap.IsHomogeneous hA AA.grading.piece AA.grading.piece (-1))
    (hhA_eq : g.linearPart ∘ₗ f.linearPart - LinearMap.id =
      AA.differential ∘ₗ hA + hA ∘ₗ AA.differential) : ReducedTensorWords R A →ₗ[R] A :=
  DirectSum.toModule R _ _ fun k ↦ (vogtSeq f g hR hhA hhA_eq k.1).ξ ∘ₗ of R A k

private theorem vogtTaylor_apply_of_mem_filtration (f : AInfinityHom AA BB) (g : AInfinityHom BB AA)
    (hR : Homotopy (f.comp g) (AInfinityHom.id BB)) {hA : A →ₗ[R] A}
    (hhA : LinearMap.IsHomogeneous hA AA.grading.piece AA.grading.piece (-1))
    (hhA_eq : g.linearPart ∘ₗ f.linearPart - LinearMap.id =
      AA.differential ∘ₗ hA + hA ∘ₗ AA.differential) {n : ℕ} {z : ReducedTensorWords R A}
    (hz : z ∈ filtration R A n) :
    vogtTaylor f g hR hhA hhA_eq z = (vogtSeq f g hR hhA hhA_eq n).ξ z := by
  let seq := vogtSeq f g hR hhA hhA_eq
  have hstab : ∀ m, ∀ w ∈ filtration R A m, (seq (m + 1)).ξ w = (seq m).ξ w := by
    intro m w hw
    cases m with
    | zero => rfl
    | succ m =>
        simp only [seq, vogtSeq, VogtStep.next, LinearMap.add_apply,
          (seq (m + 1)).deltaXi_eq_zero_of_mem_filtration _ hw, add_zero]
  have hle : ∀ {j m : ℕ}, j ≤ m →
      ∀ w ∈ filtration R A j, (seq m).ξ w = (seq j).ξ w := by
    intro j m hjm
    induction m, hjm using Nat.le_induction with
    | base => intro _ _; rfl
    | succ m hjm ih =>
        intro w hw
        rw [hstab m w (filtration_monotone R A hjm hw), ih w hw]
  have heq : filtration R A n ≤ LinearMap.eqLocus (vogtTaylor f g hR hhA hhA_eq) (seq n).ξ := by
    rw [filtration_le_iff]
    rintro k hk _ ⟨x, rfl⟩
    rw [LinearMap.mem_eqLocus, vogtTaylor, toModule_of, LinearMap.comp_apply,
      hle hk _ (of_mem_filtration R A le_rfl x)]
  exact heq hz

/-- **Vogt's lemma for `A∞` algebras.**  If `g : BB ⟶ AA` is a right `A∞` homotopy inverse of
`f : AA ⟶ BB` and `g₁ ∘ f₁` is chain-homotopic to `id_A` via a homogeneous degree-`-1` map
`hA`, then `g` is also a left `A∞` homotopy inverse of `f`. -/
noncomputable def homotopyOfRightHomotopy (f : AInfinityHom AA BB) (g : AInfinityHom BB AA)
    (hR : Homotopy (f.comp g) (AInfinityHom.id BB)) {hA : A →ₗ[R] A}
    (hhA : LinearMap.IsHomogeneous hA AA.grading.piece AA.grading.piece (-1))
    (hhA_eq : g.linearPart ∘ₗ f.linearPart - LinearMap.id =
      AA.differential ∘ₗ hA + hA ∘ₗ AA.differential) :
    Homotopy (g.comp f) (AInfinityHom.id AA) := by
  let seq := vogtSeq f g hR hhA hhA_eq
  have hξ_hom : LinearMap.IsHomogeneous (vogtTaylor f g hR hhA hhA_eq)
      (gradedPiece (AA.grading.shift 1)) (AA.grading.shift 1).piece (-1) :=
    LinearMap.isHomogeneous_def.2 fun _ z hz ↦ by
      obtain ⟨n, hn⟩ := exists_mem_filtration R A z
      rw [vogtTaylor_apply_of_mem_filtration f g hR hhA hhA_eq hn]
      exact (seq n).isHomogeneous_ξ.map_mem hz
  let Hinf := cochainOfTaylor (g.comp f) (AInfinityHom.id AA) (-1)
    (vogtTaylor f g hR hhA hhA_eq) hξ_hom
  let B₀ : reducedTransformationCochains (g.comp f) (AInfinityHom.id AA) 0 :=
    ⟨(g.comp f).barMap - (AInfinityHom.id AA).barMap,
      barMap_sub_barMap_mem_reducedTransformationCochains _ _⟩
  have hB₀ : diffTo (g.comp f) (AInfinityHom.id AA) (-1) 0 (by decide) Hinf = B₀ := by
    refine (sub_eq_zero.1 (reducedTransformationCochains.ext ?_)).symm
    rw [reducedTransformationCochains.taylor_zero, taylor_sub_cochain]
    refine LinearMap.ext fun z ↦ ?_
    obtain ⟨n, hn⟩ := exists_mem_filtration R A z
    let Hn := cochainOfTaylor (g.comp f) (AInfinityHom.id AA) (-1) (seq n).ξ (seq n).isHomogeneous_ξ
    have hHn : ∀ w ∈ filtration R A n,
        (Hinf : ReducedTensorWords R A →ₗ[R] ReducedTensorWords R A) w =
        (Hn : ReducedTensorWords R A →ₗ[R] ReducedTensorWords R A) w := fun w hw ↦
      (reducedTransformationCochains.isGradedCoderivationAlong Hinf).apply_eq_of_mem_filtration
        (reducedTransformationCochains.isGradedCoderivationAlong Hn) (fun _ _ ↦ rfl) (fun _ _ ↦ rfl)
        (fun u hu ↦ by
          simp only [← LinearMap.comp_apply (letter R A),
            ← reducedTransformationCochains.taylor_def, Hinf, Hn, seq, taylor_cochainOfTaylor,
            vogtTaylor_apply_of_mem_filtration f g hR hhA hhA_eq hu]) hw
    have ht : reducedTransformationCochains.taylor
          (diffTo (g.comp f) (AInfinityHom.id AA) (-1) 0 (by decide) Hinf) z =
        reducedTransformationCochains.taylor
          (diffTo (g.comp f) (AInfinityHom.id AA) (-1) 0 (by decide) Hn) z := by
      rw [taylor_diffTo, taylor_diffTo]
      simp only [reducedTransformationCochains.taylor_def,
        coe_reducedTransformationDifferential_neg_one, LinearMap.comp_apply, LinearMap.add_apply,
        hHn z hn, hHn _ (AA.barDifferential_mem_filtration hn)]
    have hQ0 := (seq n).vanishes_Q z hn
    rw [taylor_sub_cochain, LinearMap.sub_apply] at hQ0
    rw [LinearMap.sub_apply, LinearMap.zero_apply, ht]
    exact hQ0
  exact Homotopy.equivCochains.symm
    ⟨Hinf, (coe_diffTo (-1) 0 (by decide) Hinf).symm.trans (congrArg Subtype.val hB₀)⟩

namespace LinearHomotopyInverse

/-- The left `A∞` homotopy from `L.homotopyInverse.comp f` to `AInfinityHom.id AA`. -/
noncomputable def homotopyHomotopyInverseComp {f : AInfinityHom AA BB}
    (L : LinearHomotopyInverse f) :
    Homotopy (L.homotopyInverse.comp f) (AInfinityHom.id AA) :=
  homotopyOfRightHomotopy f L.homotopyInverse L.homotopyCompHomotopyInverse
    L.isHomogeneous_homotopyLeft (by
      rw [L.linearPart_homotopyInverse]
      exact L.inv_comp_linearPart_sub_id)

/-- Bundled two-sided `A∞` homotopy equivalence associated to linear chain-homotopy inverse data
for `f.linearPart`. -/
noncomputable def homotopyEquiv {f : AInfinityHom AA BB} (L : LinearHomotopyInverse f) :
    HomotopyEquiv AA BB where
  hom := f
  inv := L.homotopyInverse
  homotopyInvCompHom := L.homotopyHomotopyInverseComp
  homotopyHomCompInv := L.homotopyCompHomotopyInverse

@[simp]
theorem homotopyEquiv_hom {f : AInfinityHom AA BB} (L : LinearHomotopyInverse f) :
    L.homotopyEquiv.hom = f := (rfl)

@[simp]
theorem homotopyEquiv_inv {f : AInfinityHom AA BB} (L : LinearHomotopyInverse f) :
    L.homotopyEquiv.inv = L.homotopyInverse := (rfl)

@[simp]
theorem barHomotopy_homotopyEquiv_homotopyInvCompHom {f : AInfinityHom AA BB}
    (L : LinearHomotopyInverse f) :
    L.homotopyEquiv.homotopyInvCompHom.barHomotopy =
      L.homotopyHomotopyInverseComp.barHomotopy := (rfl)

@[simp]
theorem barHomotopy_homotopyEquiv_homotopyHomCompInv {f : AInfinityHom AA BB}
    (L : LinearHomotopyInverse f) :
    L.homotopyEquiv.homotopyHomCompInv.barHomotopy =
      L.homotopyCompHomotopyInverse.barHomotopy := (rfl)

end LinearHomotopyInverse

end Vogt

/-! ### Composition of homotopy equivalences and the `IsHomotopyEquiv` predicate -/

namespace HomotopyEquiv

variable {A : Type uA} {B : Type uB} {C : Type uC} [AddCommGroup A] [Module R A]
  [AddCommGroup B] [Module R B] [AddCommGroup C] [Module R C]
  {AA : AInfinityAlgebra R A} {BB : AInfinityAlgebra R B} {CC : AInfinityAlgebra R C}

/-- Transitivity of `A∞` homotopy equivalences, with forward morphism `e₂.hom.comp e₁.hom`. -/
noncomputable def trans (e₁ : HomotopyEquiv AA BB) (e₂ : HomotopyEquiv BB CC) :
    HomotopyEquiv AA CC :=
  (e₂.linearHomotopyInverse.comp e₁.linearHomotopyInverse).homotopyEquiv

@[simp]
theorem trans_hom (e₁ : HomotopyEquiv AA BB) (e₂ : HomotopyEquiv BB CC) :
    (e₁.trans e₂).hom = e₂.hom.comp e₁.hom := (rfl)

@[simp]
theorem linearPart_trans_inv (e₁ : HomotopyEquiv AA BB) (e₂ : HomotopyEquiv BB CC) :
    (e₁.trans e₂).inv.linearPart = e₁.inv.linearPart ∘ₗ e₂.inv.linearPart := by
  simp only [trans, LinearHomotopyInverse.homotopyEquiv_inv,
    LinearHomotopyInverse.linearPart_homotopyInverse, LinearHomotopyInverse.comp_inv,
    linearHomotopyInverse_inv]

end HomotopyEquiv

section IsHomotopyEquiv

section Pair

variable {A : Type uA} {B : Type uB} [AddCommGroup A] [Module R A] [AddCommGroup B] [Module R B]
  {AA : AInfinityAlgebra R A} {BB : AInfinityAlgebra R B}

/-- An `A∞` morphism is a **homotopy equivalence** when it admits an `A∞` morphism in the
reverse direction whose left and right composites with it are homotopic to the identities. -/
def IsHomotopyEquiv (f : AInfinityHom AA BB) : Prop :=
  ∃ g : AInfinityHom BB AA,
    Nonempty (Homotopy (g.comp f) (AInfinityHom.id AA)) ∧
      Nonempty (Homotopy (f.comp g) (AInfinityHom.id BB))

/-- The body of `IsHomotopyEquiv` as a reusable `Iff`. -/
theorem isHomotopyEquiv_def (f : AInfinityHom AA BB) :
    f.IsHomotopyEquiv ↔
      ∃ g : AInfinityHom BB AA,
        Nonempty (Homotopy (g.comp f) (AInfinityHom.id AA)) ∧
          Nonempty (Homotopy (f.comp g) (AInfinityHom.id BB)) :=
  Iff.rfl

/-- The forward morphism of a `HomotopyEquiv` satisfies `IsHomotopyEquiv`. -/
theorem HomotopyEquiv.isHomotopyEquiv_hom (e : HomotopyEquiv AA BB) : e.hom.IsHomotopyEquiv :=
  ⟨e.inv, ⟨e.homotopyInvCompHom⟩, ⟨e.homotopyHomCompInv⟩⟩

/-- The inverse morphism of a `HomotopyEquiv` satisfies `IsHomotopyEquiv`. -/
theorem HomotopyEquiv.isHomotopyEquiv_inv (e : HomotopyEquiv AA BB) : e.inv.IsHomotopyEquiv :=
  ⟨e.hom, ⟨e.homotopyHomCompInv⟩, ⟨e.homotopyInvCompHom⟩⟩

/-- **Over any commutative ring, an `A∞` morphism is a homotopy equivalence if and only if its
linear part admits a homogeneous chain-homotopy inverse.** -/
theorem isHomotopyEquiv_iff_nonempty_linearHomotopyInverse (f : AInfinityHom AA BB) :
    f.IsHomotopyEquiv ↔ Nonempty (LinearHomotopyInverse f) :=
  ⟨fun ⟨g, ⟨hL⟩, ⟨hR⟩⟩ ↦ ⟨(HomotopyEquiv.mk f g hL hR).linearHomotopyInverse⟩,
    fun ⟨L⟩ ↦ L.homotopyEquiv.isHomotopyEquiv_hom⟩

/-- An `A∞` isomorphism is a homotopy equivalence. -/
theorem IsIso.isHomotopyEquiv {f : AInfinityHom AA BB} (hf : f.IsIso) : f.IsHomotopyEquiv := by
  obtain ⟨g, hg₁, hg₂⟩ := (isIso_def f).1 hf
  exact ⟨g, ⟨Homotopy.ofEq hg₁⟩, ⟨Homotopy.ofEq hg₂⟩⟩

/-- An `A∞` homotopy equivalence is a quasi-isomorphism. -/
theorem IsHomotopyEquiv.isQuasiIso {f : AInfinityHom AA BB} (hf : f.IsHomotopyEquiv) :
    f.IsQuasiIso := by
  obtain ⟨g, ⟨hL⟩, ⟨hR⟩⟩ := (isHomotopyEquiv_def f).1 hf
  exact (HomotopyEquiv.mk f g hL hR).isQuasiIso_hom

/-- Homotopic `A∞` morphisms are homotopy equivalences together. -/
theorem Homotopy.isHomotopyEquiv_iff {f g : AInfinityHom AA BB} (h : Homotopy f g) :
    f.IsHomotopyEquiv ↔ g.IsHomotopyEquiv := by
  rw [isHomotopyEquiv_iff_nonempty_linearHomotopyInverse,
    isHomotopyEquiv_iff_nonempty_linearHomotopyInverse]
  exact ⟨fun ⟨L⟩ ↦ ⟨h.linearHomotopyInverse L⟩, fun ⟨L⟩ ↦ ⟨h.linearHomotopyInverseSymm L⟩⟩

end Pair

/-- The identity `A∞` morphism is a homotopy equivalence. -/
@[simp]
theorem isHomotopyEquiv_id {A : Type uA} [AddCommGroup A] [Module R A]
    (AA : AInfinityAlgebra R A) : (AInfinityHom.id AA).IsHomotopyEquiv :=
  ⟨AInfinityHom.id AA, ⟨Homotopy.ofEq (comp_id _)⟩, ⟨Homotopy.ofEq (comp_id _)⟩⟩

/-- `A∞` homotopy equivalences are closed under composition. -/
theorem IsHomotopyEquiv.comp {A : Type uA} {B : Type uB} {C : Type uC} [AddCommGroup A]
    [Module R A] [AddCommGroup B] [Module R B] [AddCommGroup C] [Module R C]
    {AA : AInfinityAlgebra R A} {BB : AInfinityAlgebra R B} {CC : AInfinityAlgebra R C}
    {g : AInfinityHom BB CC} {f : AInfinityHom AA BB} (hg : g.IsHomotopyEquiv)
    (hf : f.IsHomotopyEquiv) : (g.comp f).IsHomotopyEquiv := by
  obtain ⟨Lg⟩ := (isHomotopyEquiv_iff_nonempty_linearHomotopyInverse g).1 hg
  obtain ⟨Lf⟩ := (isHomotopyEquiv_iff_nonempty_linearHomotopyInverse f).1 hf
  exact (isHomotopyEquiv_iff_nonempty_linearHomotopyInverse _).2 ⟨Lg.comp Lf⟩

end IsHomotopyEquiv

end AInfinityHom

end TauCeti
