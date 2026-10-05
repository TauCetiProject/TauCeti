/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.Algebra.Homology.HomologicalComplex
public import TauCeti.Algebra.Homology.AInfinity.Module.Right.Hom.Homotopy

/-!
# The morphism complex of right A-infinity modules

Let `M` and `N` be right `A∞` modules over an `A∞` algebra `A`, with module bar differentials
`b_M` and `b_N` on the cofree bar comodules `sM ⊗ Tᶜ(sA)` and `sN ⊗ Tᶜ(sA)`.  A cochain of
degree `p` from `M` to `N` is a morphism of these cofree comodules which is homogeneous of degree
`p` for the total suspended gradings.  The differential of a cochain is its graded commutator with
the module bar differentials,

`δF = b_N ∘ F - (-1)^p F ∘ b_M`.

Both bar differentials are coderivations over the same algebra bar differential, so the commutator
is again a comodule morphism (`TauCeti.Comodule.Hom.coderivationComm`); it has degree `p + 1`, and
`δ² = 0` because `b_M² = 0` and `b_N² = 0`.  This file packages these cochains and their
differential as a cochain complex of modules over the ground ring.  Composition of cochains adds
degrees and satisfies the graded Leibniz rule, with the sign carried by the outer factor, so these
complexes are the Hom complexes of a DG category of right `A∞` modules.

The two existing notions of maps between modules sit inside this complex.  Morphisms of right
`A∞` modules are exactly the closed cochains of degree zero, and a homotopy from `f` to `g` is
exactly a cochain of degree `-1` whose differential is the difference of their bar maps.  As for
module morphisms and homotopies, the differential of a cochain is detected by its Taylor map,
`TauCeti.AInfinityRightModule.homCochains.taylor_homDifferential`.

## Main definitions

* `TauCeti.AInfinityRightModule.homCochains`: the homogeneous comodule morphisms of degree `p`
  between the cofree bar comodules.
* `TauCeti.AInfinityRightModule.homDifferential`: the graded commutator with the module bar
  differentials.
* `TauCeti.AInfinityRightModule.homComplex`: the morphism complex.
* `TauCeti.AInfinityRightModule.homCochains.id`, `TauCeti.AInfinityRightModule.homCochains.comp`:
  the identity cochain, and the bilinear composition of cochains, which adds degrees.
* `TauCeti.AInfinityRightModuleHom.equivZeroCocycles`: module morphisms are the closed
  degree-zero cochains.
* `TauCeti.AInfinityRightModuleHom.Homotopy.equivCochains`: homotopies are the degree-`-1`
  cochains bounding the difference of two morphisms.

## Main results

* `TauCeti.AInfinityRightModule.homDifferential_homDifferential`: the differential squares to
  zero.
* `TauCeti.AInfinityRightModule.homCochains.taylor_homDifferential`: the Taylor map of the
  differential of a cochain.
* `TauCeti.AInfinityRightModule.homDifferential_comp`: the graded Leibniz rule for composition of
  cochains.

## Implementation notes

`TauCeti.AInfinityRightModule.homComplex` is exposed so that its terms remain definitionally the
cochain modules `homCochains MM NN p`: the statement of `homComplex_d` already needs this to
type-check, and so do downstream constructions which feed `homCochains.comp` and
`homCochains.id` to the Hom complexes.

## References

* B. Keller, *Introduction to A-infinity algebras and modules*, Section 4.
-/

public section

open CategoryTheory
open scoped TensorProduct

namespace TauCeti

universe uR uA uM uN uP

variable {R : Type uR} {A : Type uA} [CommRing R] [AddCommGroup A] [Module R A]
  {AA : AInfinityAlgebra R A}
  {M : Type uM} {N : Type uN} {P : Type uP}
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N] [AddCommGroup P] [Module R P]

attribute [local instance] Comodule.cofree

namespace AInfinityRightModule

variable (MM : AInfinityRightModule AA M) (NN : AInfinityRightModule AA N)

/-- The cochains of degree `p` from `MM` to `NN`: the linear maps between the cofree bar comodules
`sM ⊗ Tᶜ(sA)` and `sN ⊗ Tᶜ(sA)` which commute with the coactions and raise the total suspended
degree by `p`. -/
def homCochains (p : ℤ) :
    Submodule R ((M ⊗[R] TensorWords R A) →ₗ[R] N ⊗[R] TensorWords R A) where
  carrier := {F |
    TensorProduct.map F LinearMap.id ∘ₗ
        Comodule.coact (R := R) (C := TensorWords R A) (M := M ⊗[R] TensorWords R A) =
      Comodule.coact (R := R) (C := TensorWords R A) (M := N ⊗[R] TensorWords R A) ∘ₗ F ∧
    LinearMap.IsHomogeneous F (barGrading AA MM.grading).piece (barGrading AA NN.grading).piece p}
  zero_mem' := ⟨by rw [TensorProduct.map_zero_left, LinearMap.zero_comp, LinearMap.comp_zero],
    LinearMap.isHomogeneous_zero _ _ _⟩
  add_mem' {F G} hF hG := ⟨by
    rw [TensorProduct.map_add_left, LinearMap.add_comp, LinearMap.comp_add, hF.1, hG.1],
    hF.2.add hG.2⟩
  smul_mem' r F hF := ⟨by
    rw [TensorProduct.map_smul_left, LinearMap.smul_comp, LinearMap.comp_smul, hF.1],
    hF.2.smul r⟩

variable {MM NN}

/-- Membership in the cochains of degree `p`: commuting with the coactions and having degree
`p`. -/
theorem mem_homCochains_iff {p : ℤ} {F : (M ⊗[R] TensorWords R A) →ₗ[R] N ⊗[R] TensorWords R A} :
    F ∈ homCochains MM NN p ↔
      TensorProduct.map F LinearMap.id ∘ₗ
          Comodule.coact (R := R) (C := TensorWords R A) (M := M ⊗[R] TensorWords R A) =
        Comodule.coact (R := R) (C := TensorWords R A) (M := N ⊗[R] TensorWords R A) ∘ₗ F ∧
      LinearMap.IsHomogeneous F (barGrading AA MM.grading).piece
        (barGrading AA NN.grading).piece p :=
  Iff.rfl

/-- A homogeneous comodule morphism of degree `p` is a cochain of degree `p`. -/
theorem toLinearMap_mem_homCochains {p : ℤ}
    (F : Comodule.Hom R (TensorWords R A) (M ⊗[R] TensorWords R A) (N ⊗[R] TensorWords R A))
    (hF : LinearMap.IsHomogeneous F.toLinearMap (barGrading AA MM.grading).piece
      (barGrading AA NN.grading).piece p) :
    F.toLinearMap ∈ homCochains MM NN p :=
  ⟨F.map_coact, hF⟩

namespace homCochains

variable {p : ℤ}

/-- A cochain as a morphism of the cofree bar comodules. -/
def toComoduleHom (F : homCochains MM NN p) :
    Comodule.Hom R (TensorWords R A) (M ⊗[R] TensorWords R A) (N ⊗[R] TensorWords R A) where
  toLinearMap := F
  map_coact := F.2.1

@[simp]
theorem toComoduleHom_toLinearMap (F : homCochains MM NN p) :
    (toComoduleHom F).toLinearMap = F :=
  (rfl)

/-- A cochain of degree `p` raises the total suspended degree by `p`. -/
theorem isHomogeneous (F : homCochains MM NN p) :
    LinearMap.IsHomogeneous (F : (M ⊗[R] TensorWords R A) →ₗ[R] N ⊗[R] TensorWords R A)
      (barGrading AA MM.grading).piece (barGrading AA NN.grading).piece p :=
  F.2.2

/-- Cochains are determined by their Taylor maps, the components obtained by applying the
coalgebra counit. -/
theorem ext_taylor {F G : homCochains MM NN p}
    (h : (TensorProduct.rid R N).toLinearMap ∘ₗ
        (Coalgebra.counit (R := R) (A := TensorWords R A)).lTensor N ∘ₗ
          (F : (M ⊗[R] TensorWords R A) →ₗ[R] N ⊗[R] TensorWords R A) =
      (TensorProduct.rid R N).toLinearMap ∘ₗ
        (Coalgebra.counit (R := R) (A := TensorWords R A)).lTensor N ∘ₗ
          (G : (M ⊗[R] TensorWords R A) →ₗ[R] N ⊗[R] TensorWords R A)) :
    F = G := by
  have hFG : toComoduleHom F = toComoduleHom G :=
    (Comodule.Hom.cofreeEquiv (R := R) (C := TensorWords R A) (M := N)
      (P := M ⊗[R] TensorWords R A)).injective (by
        rw [Comodule.Hom.cofreeEquiv_apply, Comodule.Hom.cofreeEquiv_apply]
        exact h)
  exact Subtype.ext (congrArg Comodule.Hom.toLinearMap hFG)

end homCochains

/-- The graded commutator of a homogeneous comodule morphism with the module bar differentials
commutes with the coactions. -/
private theorem map_coact_gradedCommutator {p : ℤ}
    (F : Comodule.Hom R (TensorWords R A) (M ⊗[R] TensorWords R A) (N ⊗[R] TensorWords R A))
    (hF : LinearMap.IsHomogeneous F.toLinearMap (barGrading AA MM.grading).piece
      (barGrading AA NN.grading).piece p) :
    TensorProduct.map (NN.barDifferential ∘ₗ F.toLinearMap -
          (((p.negOnePow : ℤ) : R)) • (F.toLinearMap ∘ₗ MM.barDifferential)) LinearMap.id ∘ₗ
        Comodule.coact (R := R) (C := TensorWords R A) (M := M ⊗[R] TensorWords R A) =
      Comodule.coact (R := R) (C := TensorWords R A) (M := N ⊗[R] TensorWords R A) ∘ₗ
        (NN.barDifferential ∘ₗ F.toLinearMap -
          (((p.negOnePow : ℤ) : R)) • (F.toLinearMap ∘ₗ MM.barDifferential)) := by
  let K := F.coderivationComm (r := p) (q := 1) (b := AA.coaugmentedBarDifferential)
    (barGrading AA MM.grading) (barGrading AA NN.grading) hF MM.barDifferential
    NN.barDifferential MM.isGradedCoderivation_barDifferential
    NN.isGradedCoderivation_barDifferential
  have hK : K.toLinearMap = NN.barDifferential ∘ₗ F.toLinearMap -
      (((p.negOnePow : ℤ) : R)) • (F.toLinearMap ∘ₗ MM.barDifferential) := by
    rw [Comodule.Hom.coderivationComm_toLinearMap, one_mul]
  rw [← hK]
  exact K.map_coact

/-- The graded commutator of a cochain of degree `p` with the module bar differentials,
`b_N ∘ F - (-1)^p F ∘ b_M`, is a cochain of degree `p + 1`. -/
theorem sub_negOnePow_smul_mem_homCochains {p : ℤ} {F : (M ⊗[R] TensorWords R A) →ₗ[R]
    N ⊗[R] TensorWords R A} (hF : F ∈ homCochains MM NN p) :
    NN.barDifferential ∘ₗ F - p.negOnePow • (F ∘ₗ MM.barDifferential) ∈
      homCochains MM NN (p + 1) := by
  rw [Units.smul_def, ← Int.cast_smul_eq_zsmul R]
  have hK := map_coact_gradedCommutator (homCochains.toComoduleHom ⟨F, hF⟩) hF.2
  refine ⟨hK, ?_⟩
  have h₁ : LinearMap.IsHomogeneous (NN.barDifferential ∘ₗ F)
      (barGrading AA MM.grading).piece (barGrading AA NN.grading).piece (p + 1) :=
    NN.isHomogeneous_barDifferential.comp hF.2
  have h₂ : LinearMap.IsHomogeneous (F ∘ₗ MM.barDifferential)
      (barGrading AA MM.grading).piece (barGrading AA NN.grading).piece (p + 1) := by
    rw [add_comm p 1]
    exact hF.2.comp MM.isHomogeneous_barDifferential
  exact h₁.sub (h₂.smul _)

variable (MM NN) in
/-- The differential of the morphism complex: a cochain `F` of degree `p` is sent to its graded
commutator `b_N ∘ F - (-1)^p F ∘ b_M` with the module bar differentials. -/
def homDifferential (p : ℤ) : homCochains MM NN p →ₗ[R] homCochains MM NN (p + 1) where
  toFun F := ⟨_, sub_negOnePow_smul_mem_homCochains F.2⟩
  map_add' F G := by
    apply Subtype.ext
    simp only [Submodule.coe_add, LinearMap.comp_add, LinearMap.add_comp, smul_add]
    abel
  map_smul' r F := by
    apply Subtype.ext
    simp only [SetLike.val_smul, LinearMap.comp_smul, LinearMap.smul_comp, RingHom.id_apply,
      smul_sub, smul_comm r p.negOnePow]

/-- The differential of a cochain is its graded commutator with the module bar differentials. -/
@[simp]
theorem coe_homDifferential (p : ℤ) (F : homCochains MM NN p) :
    (homDifferential MM NN p F : (M ⊗[R] TensorWords R A) →ₗ[R] N ⊗[R] TensorWords R A) =
      NN.barDifferential ∘ₗ F - p.negOnePow • ((F : _ →ₗ[R] _) ∘ₗ MM.barDifferential) :=
  (rfl)

/-- The differential of the morphism complex squares to zero. -/
@[simp]
theorem homDifferential_homDifferential (p : ℤ) (F : homCochains MM NN p) :
    homDifferential MM NN (p + 1) (homDifferential MM NN p F) = 0 := by
  have hN : NN.barDifferential ∘ₗ NN.barDifferential ∘ₗ
      (F : (M ⊗[R] TensorWords R A) →ₗ[R] N ⊗[R] TensorWords R A) = 0 := by
    rw [← LinearMap.comp_assoc, NN.barDifferential_sq, LinearMap.zero_comp]
  ext : 1
  simp only [coe_homDifferential, LinearMap.comp_sub, LinearMap.sub_comp, LinearMap.comp_smul,
    LinearMap.smul_comp, LinearMap.comp_assoc, MM.barDifferential_sq, hN, LinearMap.comp_zero,
    smul_zero, Int.negOnePow_succ, Units.neg_smul, ZeroMemClass.coe_zero, sub_zero, zero_sub,
    sub_neg_eq_add, neg_add_cancel]

/-- The differential of the morphism complex composed with itself is zero. -/
theorem homDifferential_comp_homDifferential (p : ℤ) :
    homDifferential MM NN (p + 1) ∘ₗ homDifferential MM NN p = 0 :=
  LinearMap.ext (homDifferential_homDifferential p)

/-- The Taylor map of the differential of a cochain: the counit component of
`b_N ∘ F - (-1)^p F ∘ b_M` is `taylor_N ∘ F - (-1)^p taylor(F) ∘ b_M`. -/
theorem homCochains.taylor_homDifferential {p : ℤ} (F : homCochains MM NN p) :
    (TensorProduct.rid R N).toLinearMap ∘ₗ
        (Coalgebra.counit (R := R) (A := TensorWords R A)).lTensor N ∘ₗ
          (homDifferential MM NN p F : (M ⊗[R] TensorWords R A) →ₗ[R] N ⊗[R] TensorWords R A) =
      NN.taylor ∘ₗ F - p.negOnePow •
        (((TensorProduct.rid R N).toLinearMap ∘ₗ
          (Coalgebra.counit (R := R) (A := TensorWords R A)).lTensor N ∘ₗ
            (F : (M ⊗[R] TensorWords R A) →ₗ[R] N ⊗[R] TensorWords R A)) ∘ₗ
          MM.barDifferential) := by
  simp only [coe_homDifferential, LinearMap.comp_sub, LinearMap.comp_smul, taylor_def,
    LinearMap.comp_assoc]

/-- A cochain of degree zero is closed exactly when it intertwines the module bar
differentials. -/
theorem homDifferential_zero_eq_zero_iff (F : homCochains MM NN 0) :
    homDifferential MM NN 0 F = 0 ↔
      NN.barDifferential ∘ₗ (F : (M ⊗[R] TensorWords R A) →ₗ[R] N ⊗[R] TensorWords R A) =
        (F : (M ⊗[R] TensorWords R A) →ₗ[R] N ⊗[R] TensorWords R A) ∘ₗ MM.barDifferential := by
  rw [← Subtype.coe_inj, coe_homDifferential, ZeroMemClass.coe_zero, Int.negOnePow_zero,
    one_smul, sub_eq_zero]

/-- For a cochain of degree `-1`, the differential is `b_N ∘ H + H ∘ b_M`. -/
theorem coe_homDifferential_neg_one (H : homCochains MM NN (-1)) :
    (homDifferential MM NN (-1) H : (M ⊗[R] TensorWords R A) →ₗ[R] N ⊗[R] TensorWords R A) =
      NN.barDifferential ∘ₗ H + (H : (M ⊗[R] TensorWords R A) →ₗ[R] N ⊗[R] TensorWords R A) ∘ₗ
        MM.barDifferential := by
  rw [coe_homDifferential, Int.negOnePow_neg, Int.negOnePow_one, Units.neg_smul, one_smul,
    sub_neg_eq_add]

/-! ### Composition -/

section Composition

variable {PP : AInfinityRightModule AA P}

/-- The identity of the cofree bar comodule is a cochain of degree zero. -/
theorem id_mem_homCochains : LinearMap.id ∈ homCochains MM MM 0 :=
  toLinearMap_mem_homCochains (Comodule.Hom.id R (TensorWords R A) (M ⊗[R] TensorWords R A))
    (LinearMap.isHomogeneous_id _)

/-- The composite of a cochain of degree `p` after a cochain of degree `q` is a cochain of degree
`p + q`. -/
theorem comp_mem_homCochains {p q : ℤ}
    {G : (N ⊗[R] TensorWords R A) →ₗ[R] P ⊗[R] TensorWords R A} (hG : G ∈ homCochains NN PP p)
    {F : (M ⊗[R] TensorWords R A) →ₗ[R] N ⊗[R] TensorWords R A} (hF : F ∈ homCochains MM NN q) :
    G ∘ₗ F ∈ homCochains MM PP (p + q) := by
  refine toLinearMap_mem_homCochains
    ((homCochains.toComoduleHom ⟨G, hG⟩).comp (homCochains.toComoduleHom ⟨F, hF⟩)) ?_
  rw [add_comm p q]
  exact hG.2.comp hF.2

namespace homCochains

variable (MM) in
/-- The identity cochain of degree zero: the identity of the cofree bar comodule. -/
def id : homCochains MM MM 0 :=
  ⟨LinearMap.id, id_mem_homCochains⟩

/-- The identity cochain is the identity map. -/
@[simp]
theorem coe_id :
    (id MM : (M ⊗[R] TensorWords R A) →ₗ[R] M ⊗[R] TensorWords R A) = LinearMap.id :=
  (rfl)

/-- Composition of cochains, in Keller's order: a cochain `G` of degree `p` after a cochain `F` of
degree `q` is the cochain `G ∘ F` of degree `n = p + q`.  It is bilinear in `G` and `F`. -/
def comp {p q n : ℤ} (h : p + q = n) :
    homCochains NN PP p →ₗ[R] homCochains MM NN q →ₗ[R] homCochains MM PP n :=
  LinearMap.mk₂ R (fun G F ↦ ⟨(G : (N ⊗[R] TensorWords R A) →ₗ[R] P ⊗[R] TensorWords R A) ∘ₗ
      (F : (M ⊗[R] TensorWords R A) →ₗ[R] N ⊗[R] TensorWords R A),
      by subst h; exact comp_mem_homCochains G.2 F.2⟩)
    (fun _ _ _ ↦ Subtype.ext (LinearMap.add_comp _ _ _))
    (fun _ _ _ ↦ Subtype.ext (LinearMap.smul_comp _ _ _))
    (fun _ _ _ ↦ Subtype.ext (LinearMap.comp_add _ _ _))
    (fun _ _ _ ↦ Subtype.ext (LinearMap.comp_smul _ _ _))

/-- The composite of two cochains is the composite of the underlying maps. -/
@[simp]
theorem coe_comp {p q n : ℤ} (h : p + q = n) (G : homCochains NN PP p)
    (F : homCochains MM NN q) :
    (comp h G F : (M ⊗[R] TensorWords R A) →ₗ[R] P ⊗[R] TensorWords R A) =
      (G : (N ⊗[R] TensorWords R A) →ₗ[R] P ⊗[R] TensorWords R A) ∘ₗ
        (F : (M ⊗[R] TensorWords R A) →ₗ[R] N ⊗[R] TensorWords R A) :=
  (rfl)

/-- Composing with the identity cochain on the right changes nothing. -/
@[simp]
theorem comp_id {p : ℤ} (G : homCochains MM NN p) : comp (add_zero p) G (id MM) = G :=
  (rfl)

/-- Composing with the identity cochain on the left changes nothing. -/
@[simp]
theorem id_comp {p : ℤ} (F : homCochains MM NN p) : comp (zero_add p) (id NN) F = F :=
  (rfl)

/-- Composition of cochains is associative. -/
theorem comp_assoc {Q : Type*} [AddCommGroup Q] [Module R Q] {QQ : AInfinityRightModule AA Q}
    {r q p rq qp n : ℤ} (hrq : r + q = rq) (hqp : q + p = qp) (h : rq + p = n) (h' : r + qp = n)
    (K : homCochains PP QQ r) (G : homCochains NN PP q) (F : homCochains MM NN p) :
    comp h (comp hrq K G) F = comp h' K (comp hqp G F) :=
  (rfl)

end homCochains

/-- The identity cochain is closed. -/
@[simp]
theorem homDifferential_id : homDifferential MM MM 0 (homCochains.id MM) = 0 := by
  ext : 1
  simp only [coe_homDifferential, homCochains.coe_id, LinearMap.id_comp, LinearMap.comp_id,
    Int.negOnePow_zero, one_smul, sub_self, ZeroMemClass.coe_zero]

/-- The graded Leibniz rule: for cochains `G` of degree `p` and `F` of degree `q`,
`δ(G ∘ F) = δG ∘ F + (-1)^p G ∘ δF`.  The sign is carried by the outer factor, as in Keller's
composition order. -/
theorem homDifferential_comp {p q n : ℤ} (h : p + q = n) (G : homCochains NN PP p)
    (F : homCochains MM NN q) :
    homDifferential MM PP n (homCochains.comp h G F) =
      homCochains.comp (by omega) (homDifferential NN PP p G) F +
        p.negOnePow • homCochains.comp (by omega) G (homDifferential MM NN q F) := by
  subst h
  ext : 1
  simp only [coe_homDifferential, homCochains.coe_comp, Submodule.coe_add,
    Submodule.coe_smul_of_tower, LinearMap.sub_comp, LinearMap.smul_comp, LinearMap.comp_sub,
    LinearMap.comp_smul, LinearMap.comp_assoc, smul_sub, smul_smul, Int.negOnePow_add]
  abel

end Composition

variable (MM NN)

/-- The morphism complex between two right `A∞` modules.  Its degree-`p` term is the module of
cochains of degree `p`, and its differential is the graded commutator with the module bar
differentials. -/
@[expose]
def homComplex : CochainComplex (ModuleCat R) ℤ :=
  CochainComplex.of (fun p ↦ ModuleCat.of R (homCochains MM NN p))
    (fun p ↦ ModuleCat.ofHom (homDifferential MM NN p))
    (fun p ↦ ModuleCat.hom_ext (homDifferential_comp_homDifferential p))

/-- The degree-`p` term of the morphism complex is the module of cochains of degree `p`. -/
@[simp]
theorem homComplex_X (p : ℤ) :
    (homComplex MM NN).X p = ModuleCat.of R (homCochains MM NN p) :=
  (rfl)

/-- The differential of the morphism complex is induced by `homDifferential`. -/
@[simp]
theorem homComplex_d (p : ℤ) :
    (homComplex MM NN).d p (p + 1) = ModuleCat.ofHom (homDifferential MM NN p) := by
  apply CochainComplex.of_d

end AInfinityRightModule

namespace AInfinityRightModuleHom

open AInfinityRightModule

variable {MM : AInfinityRightModule AA M} {NN : AInfinityRightModule AA N}

/-- The bar map of a module morphism is a cochain of degree zero. -/
theorem barMap_mem_homCochains (f : AInfinityRightModuleHom MM NN) :
    f.barMap ∈ homCochains MM NN 0 :=
  toLinearMap_mem_homCochains f.barHom f.isHomogeneous_barMap

/-- Morphisms of right `A∞` modules are exactly the closed cochains of degree zero in the
morphism complex. -/
def equivZeroCocycles :
    AInfinityRightModuleHom MM NN ≃ LinearMap.ker (homDifferential MM NN 0) where
  toFun f := ⟨⟨f.barMap, f.barMap_mem_homCochains⟩,
    (homDifferential_zero_eq_zero_iff _).2 f.barDifferential_comp_barMap⟩
  invFun F :=
    { barHom := homCochains.toComoduleHom F.1
      isHomogeneous_barMap := homCochains.isHomogeneous F.1
      barDifferential_comp_barMap := (homDifferential_zero_eq_zero_iff F.1).1 F.2 }
  left_inv _ := (rfl)
  right_inv _ := (rfl)

/-- The closed cochain of a module morphism is its bar map. -/
@[simp]
theorem coe_equivZeroCocycles (f : AInfinityRightModuleHom MM NN) :
    ((equivZeroCocycles f : homCochains MM NN 0) :
      (M ⊗[R] TensorWords R A) →ₗ[R] N ⊗[R] TensorWords R A) = f.barMap :=
  (rfl)

/-- The module morphism of a closed cochain has that cochain as its bar map. -/
@[simp]
theorem barMap_equivZeroCocycles_symm (F : LinearMap.ker (homDifferential MM NN 0)) :
    (equivZeroCocycles.symm F).barMap =
      ((F : homCochains MM NN 0) : (M ⊗[R] TensorWords R A) →ₗ[R] N ⊗[R] TensorWords R A) :=
  (rfl)

namespace Homotopy

variable {f g : AInfinityRightModuleHom MM NN}

/-- The bar homotopy of a module homotopy is a cochain of degree `-1`. -/
theorem barMap_mem_homCochains (h : Homotopy f g) : h.barMap ∈ homCochains MM NN (-1) :=
  toLinearMap_mem_homCochains h.barHomotopy h.isHomogeneous_barHomotopy

/-- Homotopies from `f` to `g` are exactly the cochains of degree `-1` whose differential is the
difference of the bar maps of `f` and `g`. -/
def equivCochains :
    Homotopy f g ≃ {H : homCochains MM NN (-1) //
      (homDifferential MM NN (-1) H :
        (M ⊗[R] TensorWords R A) →ₗ[R] N ⊗[R] TensorWords R A) = f.barMap - g.barMap} where
  toFun h := ⟨⟨h.barMap, h.barMap_mem_homCochains⟩, by
    rw [coe_homDifferential_neg_one]
    exact h.barMap_sub_barMap.symm⟩
  invFun H :=
    { barHomotopy := homCochains.toComoduleHom H.1
      isHomogeneous_barHomotopy := homCochains.isHomogeneous H.1
      barMap_sub_barMap := H.2.symm.trans (coe_homDifferential_neg_one H.1) }
  left_inv _ := (rfl)
  right_inv _ := (rfl)

/-- The cochain of a homotopy is its bar homotopy. -/
@[simp]
theorem coe_equivCochains (h : Homotopy f g) :
    ((equivCochains h : homCochains MM NN (-1)) :
      (M ⊗[R] TensorWords R A) →ₗ[R] N ⊗[R] TensorWords R A) = h.barMap :=
  (rfl)

/-- The homotopy of a bounding cochain has that cochain as its bar homotopy. -/
@[simp]
theorem barMap_equivCochains_symm (H : {H : homCochains MM NN (-1) //
      (homDifferential MM NN (-1) H :
        (M ⊗[R] TensorWords R A) →ₗ[R] N ⊗[R] TensorWords R A) = f.barMap - g.barMap}) :
    (equivCochains.symm H).barMap =
      ((H : homCochains MM NN (-1)) : (M ⊗[R] TensorWords R A) →ₗ[R] N ⊗[R] TensorWords R A) :=
  (rfl)

end Homotopy

end AInfinityRightModuleHom

end TauCeti
