/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.Algebra.Homology.HomologicalComplex
public import TauCeti.Algebra.Homology.AInfinity.Bimodule.Hom.Basic

/-!
# The morphism complex of A-infinity bimodules

A degree-`p` cochain between two bimodules over fixed algebras is a homogeneous
map of their two-sided bar bicomodules. It respects the right coaction and
respects the left coaction with the Koszul twist `(-1)^(p * |w|)` on the left
word. The differential is `δF = b_N F - (-1)^p F b_M`. The coalgebra terms
cancel on both sides, so this is again a bicomodule cochain, of degree `p + 1`.

We construct the cochain complex, identify its zero-cocycles with bimodule
morphisms, and supply bilinear composition with its graded Leibniz rule. These
are the chain-level operations needed for the DG category of bimodules.

The construction parallels `AInfinityRightModule.homComplex`, but retains the
signed left coaction. The conventions follow Lyubashenko--Manzyuk,
*A-infinity-bimodules and Serre A-infinity-functors*, and Getzler--Jones,
*A-infinity algebras and the cyclic bar complex*, Sections 1--2.
-/

public section

open CategoryTheory
open scoped TensorProduct

namespace TauCeti

universe uR uA uB uM uN uP

variable {R : Type uR} {A : Type uA} {B : Type uB}
  [CommRing R] [AddCommGroup A] [Module R A] [AddCommGroup B] [Module R B]
  {AA : AInfinityAlgebra R A} {BB : AInfinityAlgebra R B}
  {M : Type uM} {N : Type uN} {P : Type uP}
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  [AddCommGroup P] [Module R P]

attribute [local instance] Comodule.cofree

namespace AInfinityBimodule

variable (MM : AInfinityBimodule AA BB M) (NN : AInfinityBimodule AA BB N)

/-- Homogeneous two-sided bar maps of degree `p`. The left coaction is twisted by
`p`, while the right coaction is preserved without a twist. -/
noncomputable def homCochains (p : ℤ) :
    Submodule R (((TensorWords R A ⊗[R] M) ⊗[R] TensorWords R B) →ₗ[R]
      (TensorWords R A ⊗[R] N) ⊗[R] TensorWords R B) where
  carrier := {F |
    TensorProduct.map F LinearMap.id ∘ₗ
        Comodule.coact (R := R) (C := TensorWords R B)
          (M := (TensorWords R A ⊗[R] M) ⊗[R] TensorWords R B) =
      Comodule.coact (R := R) (C := TensorWords R B)
        (M := (TensorWords R A ⊗[R] N) ⊗[R] TensorWords R B) ∘ₗ F ∧
    Comodule.leftCoactRTensor (TensorWords R B)
        (Comodule.leftCofreeCoact R (TensorWords R A) N) ∘ₗ F =
      TensorProduct.map ((TensorWords.grading (AA.grading.shift 1)).koszulTwist p) F ∘ₗ
        Comodule.leftCoactRTensor (TensorWords R B)
          (Comodule.leftCofreeCoact R (TensorWords R A) M) ∧
    LinearMap.IsHomogeneous F (barGrading AA BB MM.grading).piece
      (barGrading AA BB NN.grading).piece p}
  zero_mem' := ⟨by simp, by simp, LinearMap.isHomogeneous_zero _ _ _⟩
  add_mem' hF hG := by
    rcases hF with ⟨hFr, hFl, hFh⟩
    rcases hG with ⟨hGr, hGl, hGh⟩
    refine ⟨?_, ?_, hFh.add hGh⟩
    · rw [TensorProduct.map_add_left, LinearMap.add_comp, LinearMap.comp_add, hFr, hGr]
    · rw [LinearMap.comp_add, TensorProduct.map_add_right, LinearMap.add_comp, hFl, hGl]
  smul_mem' r F hF := by
    rcases hF with ⟨hFr, hFl, hFh⟩
    refine ⟨?_, ?_, hFh.smul r⟩
    · rw [TensorProduct.map_smul_left, LinearMap.smul_comp, LinearMap.comp_smul, hFr]
    · rw [LinearMap.comp_smul, TensorProduct.map_smul_right, LinearMap.smul_comp, hFl]

variable {MM NN}

/-- Membership in the cochains requires right compatibility, signed left compatibility,
and homogeneity for the total suspended gradings. -/
theorem mem_homCochains_iff {p : ℤ} {F :
    ((TensorWords R A ⊗[R] M) ⊗[R] TensorWords R B) →ₗ[R]
      (TensorWords R A ⊗[R] N) ⊗[R] TensorWords R B} :
    F ∈ homCochains MM NN p ↔
      TensorProduct.map F LinearMap.id ∘ₗ
          Comodule.coact (R := R) (C := TensorWords R B)
            (M := (TensorWords R A ⊗[R] M) ⊗[R] TensorWords R B) =
        Comodule.coact (R := R) (C := TensorWords R B)
          (M := (TensorWords R A ⊗[R] N) ⊗[R] TensorWords R B) ∘ₗ F ∧
      Comodule.leftCoactRTensor (TensorWords R B)
          (Comodule.leftCofreeCoact R (TensorWords R A) N) ∘ₗ F =
        TensorProduct.map ((TensorWords.grading (AA.grading.shift 1)).koszulTwist p) F ∘ₗ
          Comodule.leftCoactRTensor (TensorWords R B)
            (Comodule.leftCofreeCoact R (TensorWords R A) M) ∧
      LinearMap.IsHomogeneous F (barGrading AA BB MM.grading).piece
        (barGrading AA BB NN.grading).piece p := Iff.rfl

/-- The signed extension of a Taylor map of degree `p` is a bimodule cochain. -/
theorem cofreeLift_mem_homCochains {p : ℤ}
    {φ : (TensorWords R A ⊗[R] M) ⊗[R] TensorWords R B →ₗ[R] N}
    (hφ : LinearMap.IsHomogeneous φ (barGrading AA BB MM.grading).piece
      (NN.grading.shift 1).piece p) :
    (Comodule.Hom.cofreeLift
      (TensorProduct.map ((TensorWords.grading (AA.grading.shift 1)).koszulTwist p) φ ∘ₗ
        Comodule.leftCoactRTensor (TensorWords R B)
          (Comodule.leftCofreeCoact R (TensorWords R A) M))).toLinearMap ∈
      homCochains MM NN p := by
  let W := TensorWords.grading (AA.grading.shift 1)
  let V := TensorWords.grading (BB.grading.shift 1)
  let τ := W.koszulTwist p
  let δ := Comodule.leftCoactRTensor (TensorWords R B)
    (Comodule.leftCofreeCoact R (TensorWords R A) M)
  let L := TensorProduct.map τ φ ∘ₗ δ
  -- The coalgebra twist makes the left extension respect the signed left coaction.
  have hτ : Coalgebra.comul ∘ₗ τ = TensorProduct.map τ τ ∘ₗ Coalgebra.comul := by
    dsimp only [τ, W]
    rw [TensorWords.koszulTwist_grading, TensorWords.comul_eq_deconcatenation,
      TensorWords.deconcatenation_natural]
  have hL : Comodule.leftCofreeCoact R (TensorWords R A) N ∘ₗ L =
      TensorProduct.map τ L ∘ₗ δ := by
    dsimp only [L, δ]
    rw [← LinearMap.comp_assoc, Comodule.leftCofreeCoact_comp_map hτ,
      LinearMap.comp_assoc, Comodule.leftCofreeCoact_comp_leftCoactRTensor_leftCofreeCoact]
    simp only [LinearMap.lTensor_def, ← LinearMap.comp_assoc, ← TensorProduct.map_comp,
      LinearMap.comp_id]
  refine (mem_homCochains_iff).2 ⟨(Comodule.Hom.cofreeLift L).map_coact, ?_, ?_⟩
  · rw [Comodule.Hom.cofreeLift_toLinearMap, Comodule.cofree_coact]
    rw [← LinearMap.comp_assoc, Comodule.leftCoactRTensor_comp_rTensor, hL]
    simpa only [Comodule.cofreeCoact_def, LinearMap.comp_assoc] using
      Comodule.assoc_comp_rTensor_comp_cofreeCoact
        (Comodule.leftCofreeCoact R (TensorWords R A) M) τ L
  · -- Both coactions and the twist have degree zero; only the Taylor map raises degree.
    simp only [barGrading_def] at hφ
    have hτh : LinearMap.IsHomogeneous τ W.piece W.piece 0 := by
      rw [LinearMap.isHomogeneous_def]
      intro q x hx
      simpa only [add_zero] using W.koszulTwist_mem_piece hx p
    have hR := isHomogeneous_rightCoact AA BB MM.grading
    have hδ := isHomogeneous_leftCoact AA BB MM.grading
    simp only [barGrading_def] at hR hδ
    have h := (((hτh.tensorProduct hφ).comp hδ).tensorProduct
      (LinearMap.isHomogeneous_id V.piece)).comp hR
    simpa only [Comodule.Hom.cofreeLift_toLinearMap, Comodule.cofree_coact,
      Comodule.cofreeCoact_def, LinearMap.rTensor_def, barGrading_def, zero_add, add_zero,
      W, V, τ, L, δ] using h

namespace homCochains

variable {p : ℤ}

/-- The right-comodule morphism underlying a bimodule cochain. -/
def toComoduleHom (F : homCochains MM NN p) :
    Comodule.Hom R (TensorWords R B)
      ((TensorWords R A ⊗[R] M) ⊗[R] TensorWords R B)
      ((TensorWords R A ⊗[R] N) ⊗[R] TensorWords R B) where
  toLinearMap := F
  map_coact := (mem_homCochains_iff.mp F.2).1

@[simp]
theorem toComoduleHom_toLinearMap (F : homCochains MM NN p) :
    (toComoduleHom F).toLinearMap = F := (rfl)

/-- A cochain raises total suspended degree by its cochain degree. -/
theorem isHomogeneous (F : homCochains MM NN p) :
    LinearMap.IsHomogeneous (F : _ →ₗ[R] _) (barGrading AA BB MM.grading).piece
      (barGrading AA BB NN.grading).piece p := (mem_homCochains_iff.mp F.2).2.2

/-- The left coaction passes a cochain with the Koszul twist on the left word. -/
theorem leftCoact_comp (F : homCochains MM NN p) :
    Comodule.leftCoactRTensor (TensorWords R B)
        (Comodule.leftCofreeCoact R (TensorWords R A) N) ∘ₗ (F : _ →ₗ[R] _) =
      TensorProduct.map ((TensorWords.grading (AA.grading.shift 1)).koszulTwist p)
        (F : _ →ₗ[R] _) ∘ₗ Comodule.leftCoactRTensor (TensorWords R B)
          (Comodule.leftCofreeCoact R (TensorWords R A) M) := (mem_homCochains_iff.mp F.2).2.1

/-- The two-counit component of a homogeneous bimodule cochain. -/
noncomputable def taylor (F : homCochains MM NN p) :
    (TensorWords R A ⊗[R] M) ⊗[R] TensorWords R B →ₗ[R] N :=
  taylorProj R A B N ∘ₗ (F : _ →ₗ[R] _)

/-- The Taylor map is obtained by removing both output words. -/
theorem taylor_def (F : homCochains MM NN p) :
    taylor F = taylorProj R A B N ∘ₗ (F : _ →ₗ[R] _) := (rfl)

/-- A cochain's Taylor map has the same degree in the suspended target grading. -/
theorem isHomogeneous_taylor (F : homCochains MM NN p) :
    LinearMap.IsHomogeneous (taylor F) (barGrading AA BB MM.grading).piece
      (NN.grading.shift 1).piece p :=
  isHomogeneous_taylorProj_comp (isHomogeneous F)

/-- The signed left extension and right cofree lift recover a cochain from its Taylor map. -/
theorem eq_cofreeLift (F : homCochains MM NN p) :
    (F : (TensorWords R A ⊗[R] M) ⊗[R] TensorWords R B →ₗ[R]
      (TensorWords R A ⊗[R] N) ⊗[R] TensorWords R B) = (Comodule.Hom.cofreeLift
      (TensorProduct.map ((TensorWords.grading (AA.grading.shift 1)).koszulTwist p)
        (taylor F) ∘ₗ Comodule.leftCoactRTensor (TensorWords R B)
          (Comodule.leftCofreeCoact R (TensorWords R A) M))).toLinearMap := by
  have h := (toComoduleHom F).eq_cofreeLift_of_leftCoact _ (leftCoact_comp F)
  simpa only [toComoduleHom_toLinearMap, taylor_def, taylorProj_def,
    LinearMap.comp_assoc] using congrArg Comodule.Hom.toLinearMap h

/-- Cochains of a fixed degree are determined by their two-counit components. -/
theorem ext_taylor {F G : homCochains MM NN p} (h : taylor F = taylor G) : F = G := by
  apply Subtype.ext
  rw [eq_cofreeLift F, eq_cofreeLift G, h]

end homCochains

/-- The graded commutator with the bar differentials is a cochain of degree `p + 1`. -/
theorem sub_negOnePow_smul_mem_homCochains {p : ℤ} (F : homCochains MM NN p) :
    NN.barDifferential ∘ₗ (F : _ →ₗ[R] _) -
      (((p.negOnePow : ℤ) : R)) • ((F : _ →ₗ[R] _) ∘ₗ MM.barDifferential) ∈
        homCochains MM NN (p + 1) := by
  have hF : LinearMap.IsHomogeneous (homCochains.toComoduleHom F).toLinearMap
      (barGrading AA BB MM.grading).piece (barGrading AA BB NN.grading).piece p := by
    rw [homCochains.toComoduleHom_toLinearMap]
    exact homCochains.isHomogeneous F
  let K := (homCochains.toComoduleHom F).coderivationComm (r := p) (q := 1)
    (b := BB.coaugmentedBarDifferential) (barGrading AA BB MM.grading)
    (barGrading AA BB NN.grading) hF MM.barDifferential
    NN.barDifferential
    MM.isGradedCoderivation_barDifferential NN.isGradedCoderivation_barDifferential
  have hKdef : K.toLinearMap = NN.barDifferential ∘ₗ (F : _ →ₗ[R] _) -
      (((p.negOnePow : ℤ) : R)) • ((F : _ →ₗ[R] _) ∘ₗ MM.barDifferential) := by
    dsimp only [K]
    rw [Comodule.Hom.coderivationComm_toLinearMap, one_mul,
      homCochains.toComoduleHom_toLinearMap]
  have hK := K.map_coact
  rw [hKdef] at hK
  rw [mem_homCochains_iff]
  refine ⟨hK, ?_, ?_⟩
  · simpa only [mul_one] using
      MM.isLeftGradedCoderivation_barDifferential.commutator_coact
        NN.isLeftGradedCoderivation_barDifferential
        (by simpa only [TensorWords.grading_piece] using
          AA.isHomogeneous_coaugmentedBarDifferential)
        (F : _ →ₗ[R] _) (homCochains.leftCoact_comp F)
  · have h₁ := NN.isHomogeneous_barDifferential.comp (homCochains.isHomogeneous F)
    have h₂ := (homCochains.isHomogeneous F).comp MM.isHomogeneous_barDifferential
    rw [add_comm 1 p] at h₂
    exact h₁.sub (h₂.smul _)

variable (MM NN) in
/-- The differential `δF = b_N F - (-1)^p F b_M` of bimodule cochains. -/
noncomputable def homDifferential (p : ℤ) :
    homCochains MM NN p →ₗ[R] homCochains MM NN (p + 1) where
  toFun F := ⟨_, sub_negOnePow_smul_mem_homCochains F⟩
  map_add' F G := by
    apply Subtype.ext
    simp only [Submodule.coe_add, LinearMap.comp_add, LinearMap.add_comp,
      smul_add]
    abel
  map_smul' r F := by
    apply Subtype.ext
    simp only [SetLike.val_smul, LinearMap.comp_smul, LinearMap.smul_comp, RingHom.id_apply,
      smul_sub, smul_comm r (((p.negOnePow : ℤ) : R))]

/-- The cochain differential on underlying bar maps. -/
@[simp]
theorem coe_homDifferential (p : ℤ) (F : homCochains MM NN p) :
    (homDifferential MM NN p F : _ →ₗ[R] _) =
      NN.barDifferential ∘ₗ (F : _ →ₗ[R] _) -
        (((p.negOnePow : ℤ) : R)) • ((F : _ →ₗ[R] _) ∘ₗ MM.barDifferential) := (rfl)

/-- The bimodule cochain differential squares to zero. -/
@[simp]
theorem homDifferential_homDifferential (p : ℤ) (F : homCochains MM NN p) :
    homDifferential MM NN (p + 1) (homDifferential MM NN p F) = 0 := by
  have hN : NN.barDifferential ∘ₗ NN.barDifferential ∘ₗ
      (F : ((TensorWords R A ⊗[R] M) ⊗[R] TensorWords R B) →ₗ[R]
        (TensorWords R A ⊗[R] N) ⊗[R] TensorWords R B) = 0 := by
    rw [← LinearMap.comp_assoc, NN.barDifferential_sq, LinearMap.zero_comp]
  ext : 1
  simp only [coe_homDifferential, LinearMap.comp_sub, LinearMap.sub_comp, LinearMap.comp_smul,
    LinearMap.smul_comp, LinearMap.comp_assoc, MM.barDifferential_sq, hN, LinearMap.comp_zero,
    smul_zero, Int.negOnePow_succ, Units.val_neg, Int.cast_neg,
    ZeroMemClass.coe_zero, sub_zero, zero_sub]
  module

/-- The bimodule cochain differential composed with itself is zero. -/
theorem homDifferential_comp_homDifferential (p : ℤ) :
    homDifferential MM NN (p + 1) ∘ₗ homDifferential MM NN p = 0 :=
  LinearMap.ext (homDifferential_homDifferential p)

/-- Degree-zero cochains are closed precisely when they commute with the bar differentials. -/
theorem homDifferential_zero_eq_zero_iff (F : homCochains MM NN 0) :
    homDifferential MM NN 0 F = 0 ↔
      NN.barDifferential ∘ₗ (F : _ →ₗ[R] _) = (F : _ →ₗ[R] _) ∘ₗ MM.barDifferential := by
  rw [← Subtype.coe_inj, coe_homDifferential, ZeroMemClass.coe_zero, Int.negOnePow_zero,
    Units.val_one, Int.cast_one, one_smul, sub_eq_zero]

section Composition

variable {PP : AInfinityBimodule AA BB P}

namespace homCochains

variable (MM) in
/-- The identity bar map, regarded as a degree-zero cochain. -/
noncomputable def id : homCochains MM MM 0 :=
  ⟨LinearMap.id, (mem_homCochains_iff).2 ⟨by simp,
    by simp [InternalGrading.koszulTwist_zero], LinearMap.isHomogeneous_id _⟩⟩

/-- The identity cochain is the identity on bar carriers. -/
@[simp]
theorem coe_id :
    (id MM : ((TensorWords R A ⊗[R] M) ⊗[R] TensorWords R B) →ₗ[R]
      (TensorWords R A ⊗[R] M) ⊗[R] TensorWords R B) = LinearMap.id := (rfl)

/-- Composition of homogeneous bicomodule maps is homogeneous, with degrees added. -/
theorem comp_mem {p q : ℤ} (G : homCochains NN PP p) (F : homCochains MM NN q) :
    (G : ((TensorWords R A ⊗[R] N) ⊗[R] TensorWords R B) →ₗ[R]
      (TensorWords R A ⊗[R] P) ⊗[R] TensorWords R B) ∘ₗ
        (F : ((TensorWords R A ⊗[R] M) ⊗[R] TensorWords R B) →ₗ[R]
          (TensorWords R A ⊗[R] N) ⊗[R] TensorWords R B) ∈ homCochains MM PP (p + q) := by
  rw [mem_homCochains_iff]
  refine ⟨?_, ?_, ?_⟩
  · have h := ((toComoduleHom G).comp (toComoduleHom F)).map_coact
    simpa only [Comodule.Hom.comp_toLinearMap, toComoduleHom_toLinearMap] using h
  · rw [← LinearMap.comp_assoc, leftCoact_comp G, LinearMap.comp_assoc, leftCoact_comp F]
    simp only [← LinearMap.comp_assoc, ← TensorProduct.map_comp,
      InternalGrading.koszulTwist_comp]
  · simpa only [add_comm q p] using (isHomogeneous G).comp (isHomogeneous F)

/-- Bilinear composition in Keller order: `G` after `F` is their composite bar map. -/
noncomputable def comp {p q n : ℤ} (h : p + q = n) :
    homCochains NN PP p →ₗ[R] homCochains MM NN q →ₗ[R] homCochains MM PP n :=
  LinearMap.mk₂ R (fun G F ↦ ⟨
      (G : ((TensorWords R A ⊗[R] N) ⊗[R] TensorWords R B) →ₗ[R]
        (TensorWords R A ⊗[R] P) ⊗[R] TensorWords R B) ∘ₗ
      (F : ((TensorWords R A ⊗[R] M) ⊗[R] TensorWords R B) →ₗ[R]
        (TensorWords R A ⊗[R] N) ⊗[R] TensorWords R B),
      by subst h; exact comp_mem G F⟩)
    (fun _ _ _ ↦ Subtype.ext (LinearMap.add_comp _ _ _))
    (fun _ _ _ ↦ Subtype.ext (LinearMap.smul_comp _ _ _))
    (fun _ _ _ ↦ Subtype.ext (LinearMap.comp_add _ _ _))
    (fun _ _ _ ↦ Subtype.ext (LinearMap.comp_smul _ _ _))

/-- Composition of cochains is composition of the underlying bar maps. -/
@[simp]
theorem coe_comp {p q n : ℤ} (h : p + q = n) (G : homCochains NN PP p)
    (F : homCochains MM NN q) :
    (comp h G F : ((TensorWords R A ⊗[R] M) ⊗[R] TensorWords R B) →ₗ[R]
      (TensorWords R A ⊗[R] P) ⊗[R] TensorWords R B) =
        (G : ((TensorWords R A ⊗[R] N) ⊗[R] TensorWords R B) →ₗ[R]
          (TensorWords R A ⊗[R] P) ⊗[R] TensorWords R B) ∘ₗ
        (F : ((TensorWords R A ⊗[R] M) ⊗[R] TensorWords R B) →ₗ[R]
          (TensorWords R A ⊗[R] N) ⊗[R] TensorWords R B) := (rfl)

/-- The identity cochain is a right unit. -/
@[simp]
theorem comp_id {p : ℤ} (F : homCochains MM NN p) : comp (add_zero p) F (id MM) = F :=
  Subtype.ext (by simp)

/-- The identity cochain is a left unit. -/
@[simp]
theorem id_comp {p : ℤ} (F : homCochains MM NN p) : comp (zero_add p) (id NN) F = F :=
  Subtype.ext (by simp)

/-- Composition of bimodule cochains is associative. -/
theorem comp_assoc {Q : Type*} [AddCommGroup Q] [Module R Q]
    {QQ : AInfinityBimodule AA BB Q} {r q p rq qp n : ℤ}
    (hrq : r + q = rq) (hqp : q + p = qp) (h : rq + p = n) (h' : r + qp = n)
    (K : homCochains PP QQ r) (G : homCochains NN PP q) (F : homCochains MM NN p) :
    comp h (comp hrq K G) F = comp h' K (comp hqp G F) :=
  Subtype.ext (by simp only [coe_comp, LinearMap.comp_assoc])

end homCochains

/-- The identity cochain is closed. -/
@[simp]
theorem homDifferential_id : homDifferential MM MM 0 (homCochains.id MM) = 0 := by
  ext : 1
  simp only [coe_homDifferential, homCochains.coe_id, LinearMap.id_comp, LinearMap.comp_id,
    Int.negOnePow_zero, Units.val_one, Int.cast_one, one_smul, sub_self, ZeroMemClass.coe_zero]

/-- Composition satisfies the graded Leibniz rule, with the sign on the outer factor. -/
theorem homDifferential_comp {p q n : ℤ} (h : p + q = n) (G : homCochains NN PP p)
    (F : homCochains MM NN q) :
    homDifferential MM PP n (homCochains.comp h G F) =
      homCochains.comp (by omega) (homDifferential NN PP p G) F +
        (((p.negOnePow : ℤ) : R)) •
          homCochains.comp (by omega) G (homDifferential MM NN q F) := by
  subst h
  ext : 1
  simp only [coe_homDifferential, homCochains.coe_comp, Submodule.coe_add,
    SetLike.val_smul, LinearMap.sub_comp, LinearMap.smul_comp, LinearMap.comp_sub,
    LinearMap.comp_smul, LinearMap.comp_assoc, smul_sub, smul_smul, Int.negOnePow_add,
    Units.val_mul, Int.cast_mul]
  module

end Composition

variable (MM NN)

-- The terms must reduce to cochain modules to typecheck `homComplex_d` and composition.
/-- The Hom complex of two A-infinity bimodules over fixed algebras. -/
@[expose]
noncomputable def homComplex : CochainComplex (ModuleCat R) ℤ :=
  CochainComplex.of (fun p ↦ ModuleCat.of R (homCochains MM NN p))
    (fun p ↦ ModuleCat.ofHom (homDifferential MM NN p))
    (fun p ↦ ModuleCat.hom_ext (homDifferential_comp_homDifferential p))

/-- The terms of the Hom complex are the homogeneous bicomodule maps. -/
@[simp]
theorem homComplex_X (p : ℤ) :
    (homComplex MM NN).X p = ModuleCat.of R (homCochains MM NN p) := (rfl)

/-- The differential of the Hom complex is the graded commutator. -/
@[simp]
theorem homComplex_d (p : ℤ) :
    (homComplex MM NN).d p (p + 1) = ModuleCat.ofHom (homDifferential MM NN p) := by
  apply CochainComplex.of_d

/-- The degree-`p` term of the Hom complex is linearly equivalent to the cochains of degree `p`. -/
noncomputable def homComplexXEquiv (p : ℤ) :
    (homComplex MM NN).X p ≃ₗ[R] homCochains MM NN p :=
  (eqToIso (homComplex_X MM NN p)).toLinearEquiv

/-- Under `homComplexXEquiv`, the Hom complex differential is `homDifferential`. -/
theorem homComplexXEquiv_d (p : ℤ) (F : (homComplex MM NN).X p) :
    homComplexXEquiv MM NN (p + 1) (((homComplex MM NN).d p (p + 1)).hom F) =
      homDifferential MM NN p (homComplexXEquiv MM NN p F) := by
  rw [homComplex_d]
  -- Both equivalences are eqToHom of an equality of a module with itself.
  rfl

end AInfinityBimodule

namespace AInfinityBimoduleHom

open AInfinityBimodule

variable {MM : AInfinityBimodule AA BB M} {NN : AInfinityBimodule AA BB N}

/-- A bimodule morphism is a degree-zero bar cochain. -/
theorem barMap_mem_homCochains (f : AInfinityBimoduleHom MM NN) :
    f.barMap ∈ homCochains MM NN 0 := by
  rw [mem_homCochains_iff]
  refine ⟨f.barHom.map_coact, ?_, f.isHomogeneous_barMap⟩
  simpa only [InternalGrading.koszulTwist_zero, ← LinearMap.lTensor_def] using
    f.leftCoact_comp_barMap

/-- Bimodule morphisms are exactly the zero-cocycles of the Hom complex. -/
noncomputable def equivZeroCocycles :
    AInfinityBimoduleHom MM NN ≃ LinearMap.ker (homDifferential MM NN 0) where
  toFun f := ⟨⟨f.barMap, f.barMap_mem_homCochains⟩,
    (homDifferential_zero_eq_zero_iff _).2 f.barDifferential_comp_barMap⟩
  invFun F :=
    { barHom := homCochains.toComoduleHom F.1
      leftCoact_comp_barMap := by
        simpa only [InternalGrading.koszulTwist_zero, ← LinearMap.lTensor_def,
          homCochains.toComoduleHom_toLinearMap] using homCochains.leftCoact_comp F.1
      isHomogeneous_barMap := homCochains.isHomogeneous F.1
      barDifferential_comp_barMap := (homDifferential_zero_eq_zero_iff F.1).1 F.2 }
  left_inv _ := (rfl)
  right_inv _ := (rfl)

/-- The cochain associated to a bimodule morphism is its bar map. -/
@[simp]
theorem coe_equivZeroCocycles (f : AInfinityBimoduleHom MM NN) :
    ((equivZeroCocycles f : homCochains MM NN 0) : _ →ₗ[R] _) = f.barMap := (rfl)

/-- The morphism associated to a zero-cocycle has the prescribed bar map. -/
@[simp]
theorem barMap_equivZeroCocycles_symm (F : LinearMap.ker (homDifferential MM NN 0)) :
    (equivZeroCocycles.symm F).barMap = ((F : homCochains MM NN 0) : _ →ₗ[R] _) := (rfl)

/-- The zero-cocycle of the identity morphism is the identity cochain. -/
@[simp]
theorem equivZeroCocycles_id (MM : AInfinityBimodule AA BB M) :
    (equivZeroCocycles (AInfinityBimoduleHom.id MM)).val = homCochains.id MM :=
  Subtype.ext ((coe_equivZeroCocycles _).trans (by simp))

/-- The zero-cocycle identification respects composition. -/
@[simp]
theorem equivZeroCocycles_comp {PP : AInfinityBimodule AA BB P}
    (g : AInfinityBimoduleHom NN PP) (f : AInfinityBimoduleHom MM NN) :
    (equivZeroCocycles (g.comp f)).val =
      homCochains.comp (zero_add 0) (equivZeroCocycles g).val (equivZeroCocycles f).val := by
  apply Subtype.ext
  rw [homCochains.coe_comp]
  exact (coe_equivZeroCocycles _).trans ((barMap_comp g f).trans
    (congrArg₂ LinearMap.comp (coe_equivZeroCocycles g).symm (coe_equivZeroCocycles f).symm))

end AInfinityBimoduleHom

end TauCeti
