/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.AInfinity.Algebra.Transfer.Cohomology
public import TauCeti.Algebra.Homology.AInfinity.Algebra.Transfer.Homotopy

/-!
# Homotopy equivalences and homotopy inverses of A-infinity algebras

Over any commutative ring `R`, an `A∞` morphism `f : A ⟶ B` is a homotopy equivalence
(`TauCeti.AInfinityHom.IsHomotopyEquiv`) iff `f.linearPart` admits a homogeneous chain-homotopy
inverse (`TauCeti.AInfinityHom.isHomotopyEquiv_iff_exists_linearHomotopyInverse`), constructed by
`TauCeti.AInfinityHomotopyEquiv.ofLinearHomotopyInverse`. Over a field, every `A∞` algebra is
homotopy equivalent to its minimal model on cohomology
(`TauCeti.AInfinityAlgebra.minimalModelHomotopyEquiv`), and homotopy equivalences coincide with
quasi-isomorphisms (`TauCeti.AInfinityHom.isHomotopyEquiv_iff_isQuasiIso`,
`TauCeti.AInfinityHom.IsQuasiIso.homotopyEquiv`).

## References

* K. Lefèvre-Hasegawa, *Sur les A-infini catégories*, Theorem 1.3.1.2 and Appendix B.2.
* B. Keller, *Introduction to A-infinity algebras and modules*, Section 3.7.
* A. Prouté, *A-infinity structures*, Reprints TAC 21 (2011), Theorem 4.8.
-/

public section

open scoped TensorProduct

namespace TauCeti

universe uR uK uA uB uC

section CommRing

variable {R : Type uR} {A : Type uA} {B : Type uB} [CommRing R]
  [AddCommGroup A] [Module R A] [AddCommGroup B] [Module R B]

/-! ### Explicit homotopy equivalences of `A∞` algebras -/

/-- A **homotopy equivalence** between `A∞` algebras `AA` and `BB`: morphisms `toHom : AA ⟶ BB` and
`invHom : BB ⟶ AA` with homotopies `invHom ∘ toHom ~ id_AA` and `toHom ∘ invHom ~ id_BB`. -/
structure AInfinityHomotopyEquiv (AA : AInfinityAlgebra R A) (BB : AInfinityAlgebra R B) where
  /-- The forward `A∞` morphism. -/
  toHom : AInfinityHom AA BB
  /-- The homotopy-inverse `A∞` morphism. -/
  invHom : AInfinityHom BB AA
  /-- The homotopy from `invHom ∘ toHom` to the identity of `AA`. -/
  leftHomotopy : AInfinityHom.Homotopy (invHom.comp toHom) (AInfinityHom.id AA)
  /-- The homotopy from `toHom ∘ invHom` to the identity of `BB`. -/
  rightHomotopy : AInfinityHom.Homotopy (toHom.comp invHom) (AInfinityHom.id BB)

namespace AInfinityHomotopyEquiv

variable {C : Type uC} [AddCommGroup C] [Module R C]
  {AA : AInfinityAlgebra R A} {BB : AInfinityAlgebra R B} {CC : AInfinityAlgebra R C}

/-- The identity homotopy equivalence of an `A∞` algebra. -/
def refl (AA : AInfinityAlgebra R A) : AInfinityHomotopyEquiv AA AA where
  toHom := AInfinityHom.id AA
  invHom := AInfinityHom.id AA
  leftHomotopy := (AInfinityHom.Homotopy.refl _).copy (AInfinityHom.comp_id _).symm rfl
  rightHomotopy := (AInfinityHom.Homotopy.refl _).copy (AInfinityHom.comp_id _).symm rfl

@[simp] theorem toHom_refl (AA : AInfinityAlgebra R A) :
    (refl AA).toHom = AInfinityHom.id AA := (rfl)
@[simp] theorem invHom_refl (AA : AInfinityAlgebra R A) :
    (refl AA).invHom = AInfinityHom.id AA := (rfl)

/-- The inverse homotopy equivalence, swapping forward and inverse morphisms. -/
def symm (e : AInfinityHomotopyEquiv AA BB) : AInfinityHomotopyEquiv BB AA :=
  ⟨e.invHom, e.toHom, e.rightHomotopy, e.leftHomotopy⟩

@[simp] theorem toHom_symm (e : AInfinityHomotopyEquiv AA BB) : e.symm.toHom = e.invHom := (rfl)
@[simp] theorem invHom_symm (e : AInfinityHomotopyEquiv AA BB) : e.symm.invHom = e.toHom := (rfl)
@[simp] theorem symm_symm (e : AInfinityHomotopyEquiv AA BB) : e.symm.symm = e := (rfl)

/-- Composition of homotopy equivalences of `A∞` algebras. -/
noncomputable def trans (e₁ : AInfinityHomotopyEquiv AA BB) (e₂ : AInfinityHomotopyEquiv BB CC) :
    AInfinityHomotopyEquiv AA CC where
  toHom := e₂.toHom.comp e₁.toHom
  invHom := e₁.invHom.comp e₂.invHom
  leftHomotopy := (((e₂.leftHomotopy.compLeft e₁.toHom).compRight e₁.invHom).copy
    (by simp only [AInfinityHom.comp_assoc]) (by rw [AInfinityHom.id_comp])).trans e₁.leftHomotopy
  rightHomotopy := (((e₁.rightHomotopy.compLeft e₂.invHom).compRight e₂.toHom).copy
    (by simp only [AInfinityHom.comp_assoc]) (by rw [AInfinityHom.id_comp])).trans e₂.rightHomotopy

@[simp] theorem toHom_trans (e₁ : AInfinityHomotopyEquiv AA BB)
    (e₂ : AInfinityHomotopyEquiv BB CC) : (e₁.trans e₂).toHom = e₂.toHom.comp e₁.toHom := (rfl)
@[simp] theorem invHom_trans (e₁ : AInfinityHomotopyEquiv AA BB)
    (e₂ : AInfinityHomotopyEquiv BB CC) : (e₁.trans e₂).invHom = e₁.invHom.comp e₂.invHom := (rfl)

/-- Replace `toHom` by a homotopic morphism `f`, keeping the same homotopy inverse. -/
noncomputable def replaceToHom (e : AInfinityHomotopyEquiv AA BB) {f : AInfinityHom AA BB}
    (hf : AInfinityHom.Homotopy f e.toHom) : AInfinityHomotopyEquiv AA BB :=
  ⟨f, e.invHom, (hf.compRight e.invHom).trans e.leftHomotopy,
    (hf.compLeft e.invHom).trans e.rightHomotopy⟩

@[simp] theorem toHom_replaceToHom (e : AInfinityHomotopyEquiv AA BB) {f : AInfinityHom AA BB}
    (hf : AInfinityHom.Homotopy f e.toHom) : (e.replaceToHom hf).toHom = f := (rfl)
@[simp] theorem invHom_replaceToHom (e : AInfinityHomotopyEquiv AA BB) {f : AInfinityHom AA BB}
    (hf : AInfinityHom.Homotopy f e.toHom) : (e.replaceToHom hf).invHom = e.invHom := (rfl)

/-- An `A∞` morphism with bijective linear part yields a homotopy equivalence via `f.inverse`. -/
noncomputable def ofLinearPartBijective (f : AInfinityHom AA BB)
    (hf : Function.Bijective f.linearPart) : AInfinityHomotopyEquiv AA BB where
  toHom := f
  invHom := f.inverse hf
  leftHomotopy := (AInfinityHom.Homotopy.refl _).copy (f.inverse_comp_cancel hf).symm rfl
  rightHomotopy := (AInfinityHom.Homotopy.refl _).copy (f.comp_inverse_cancel hf).symm rfl

@[simp] theorem toHom_ofLinearPartBijective (f : AInfinityHom AA BB)
    (hf : Function.Bijective f.linearPart) : (ofLinearPartBijective f hf).toHom = f := (rfl)
@[simp] theorem invHom_ofLinearPartBijective (f : AInfinityHom AA BB)
    (hf : Function.Bijective f.linearPart) :
    (ofLinearPartBijective f hf).invHom = f.inverse hf := (rfl)

/-- Two-sided homotopy equivalence from right homotopy inverses `f ∘ g ~ id` and `g ∘ f' ~ id`. -/
noncomputable def ofRightHomotopyInverses {f f' : AInfinityHom AA BB} {g : AInfinityHom BB AA}
    (hfg : AInfinityHom.Homotopy (f.comp g) (AInfinityHom.id BB))
    (hgf' : AInfinityHom.Homotopy (g.comp f') (AInfinityHom.id AA)) :
    AInfinityHomotopyEquiv AA BB where
  toHom := f
  invHom := g
  leftHomotopy :=
    let hff' := ((hgf'.symm.compRight f).copy (AInfinityHom.comp_id f)
      (AInfinityHom.comp_assoc f g f').symm).trans
      ((hfg.compLeft f').copy rfl (AInfinityHom.id_comp f'))
    (hff'.compRight g).trans hgf'
  rightHomotopy := hfg

@[simp] theorem toHom_ofRightHomotopyInverses {f f' : AInfinityHom AA BB} {g : AInfinityHom BB AA}
    (hfg : AInfinityHom.Homotopy (f.comp g) (AInfinityHom.id BB))
    (hgf' : AInfinityHom.Homotopy (g.comp f') (AInfinityHom.id AA)) :
    (ofRightHomotopyInverses hfg hgf').toHom = f := (rfl)
@[simp] theorem invHom_ofRightHomotopyInverses {f f' : AInfinityHom AA BB} {g : AInfinityHom BB AA}
    (hfg : AInfinityHom.Homotopy (f.comp g) (AInfinityHom.id BB))
    (hgf' : AInfinityHom.Homotopy (g.comp f') (AInfinityHom.id AA)) :
    (ofRightHomotopyInverses hfg hgf').invHom = g := (rfl)

/-- The forward morphism of a homotopy equivalence is a quasi-isomorphism. -/
theorem isQuasiIso_toHom (e : AInfinityHomotopyEquiv AA BB) : e.toHom.IsQuasiIso := by
  rw [AInfinityHom.isQuasiIso_def]
  refine Function.bijective_iff_has_inverse.2 ⟨e.invHom.cohomologyMap, fun x ↦ ?_, fun y ↦ ?_⟩
  · have h := DFunLike.congr_fun e.leftHomotopy.cohomologyMap_eq x
    rwa [AInfinityHom.cohomologyMap_comp, AInfinityHom.cohomologyMap_id,
      NonUnitalAlgHom.comp_apply, NonUnitalAlgHom.coe_id, id_eq] at h
  · have h := DFunLike.congr_fun e.rightHomotopy.cohomologyMap_eq y
    rwa [AInfinityHom.cohomologyMap_comp, AInfinityHom.cohomologyMap_id,
      NonUnitalAlgHom.comp_apply, NonUnitalAlgHom.coe_id, id_eq] at h

theorem isQuasiIso_invHom (e : AInfinityHomotopyEquiv AA BB) : e.invHom.IsQuasiIso :=
  e.symm.isQuasiIso_toHom

end AInfinityHomotopyEquiv

/-! ### The homotopy-equivalence predicate on `A∞` morphisms -/

namespace AInfinityHom

variable {C : Type uC} [AddCommGroup C] [Module R C]
  {AA : AInfinityAlgebra R A} {BB : AInfinityAlgebra R B} {CC : AInfinityAlgebra R C}

/-- An `A∞` morphism `f : AA ⟶ BB` is a **homotopy equivalence** when it admits a two-sided
inverse up to homotopy. -/
def IsHomotopyEquiv (f : AInfinityHom AA BB) : Prop :=
  ∃ g : AInfinityHom BB AA,
    (g.comp f).Homotopic (AInfinityHom.id AA) ∧ (f.comp g).Homotopic (AInfinityHom.id BB)

theorem isHomotopyEquiv_def (f : AInfinityHom AA BB) :
    f.IsHomotopyEquiv ↔ ∃ g : AInfinityHom BB AA,
      (g.comp f).Homotopic (AInfinityHom.id AA) ∧ (f.comp g).Homotopic (AInfinityHom.id BB) :=
  Iff.rfl
theorem _root_.TauCeti.AInfinityHomotopyEquiv.isHomotopyEquiv_toHom
    (e : AInfinityHomotopyEquiv AA BB) : e.toHom.IsHomotopyEquiv :=
  ⟨e.invHom, e.leftHomotopy.homotopic, e.rightHomotopy.homotopic⟩
theorem _root_.TauCeti.AInfinityHomotopyEquiv.isHomotopyEquiv_invHom
    (e : AInfinityHomotopyEquiv AA BB) : e.invHom.IsHomotopyEquiv := e.symm.isHomotopyEquiv_toHom

/-- `f` is a homotopy equivalence iff `f` is `e.toHom` for some `AInfinityHomotopyEquiv`. -/
theorem isHomotopyEquiv_iff_exists_homotopyEquiv (f : AInfinityHom AA BB) :
    f.IsHomotopyEquiv ↔ ∃ e : AInfinityHomotopyEquiv AA BB, e.toHom = f := by
  refine ⟨fun ⟨g, hL, hR⟩ ↦ ?_, fun ⟨e, h⟩ ↦ h ▸ e.isHomotopyEquiv_toHom⟩
  obtain ⟨HL⟩ := (homotopic_def _ _).1 hL; obtain ⟨HR⟩ := (homotopic_def _ _).1 hR
  exact ⟨⟨f, g, HL, HR⟩, rfl⟩

@[simp] theorem isHomotopyEquiv_id (AA : AInfinityAlgebra R A) :
    (AInfinityHom.id AA).IsHomotopyEquiv := (AInfinityHomotopyEquiv.refl AA).isHomotopyEquiv_toHom
theorem IsHomotopyEquiv.comp {g : AInfinityHom BB CC} {f : AInfinityHom AA BB}
    (hg : g.IsHomotopyEquiv) (hf : f.IsHomotopyEquiv) : (g.comp f).IsHomotopyEquiv := by
  obtain ⟨eg, rfl⟩ := (isHomotopyEquiv_iff_exists_homotopyEquiv g).1 hg
  obtain ⟨ef, rfl⟩ := (isHomotopyEquiv_iff_exists_homotopyEquiv f).1 hf
  exact (ef.trans eg).isHomotopyEquiv_toHom
theorem Homotopic.isHomotopyEquiv_iff {f g : AInfinityHom AA BB} (h : f.Homotopic g) :
    f.IsHomotopyEquiv ↔ g.IsHomotopyEquiv := by
  have aux {u v : AInfinityHom AA BB} (huv : u.Homotopic v) (hv : v.IsHomotopyEquiv) :
      u.IsHomotopyEquiv := by
    obtain ⟨H⟩ := (homotopic_def u v).1 huv
    obtain ⟨e, rfl⟩ := (isHomotopyEquiv_iff_exists_homotopyEquiv v).1 hv
    exact (e.replaceToHom H).isHomotopyEquiv_toHom
  exact ⟨aux h.symm, aux h⟩
theorem Homotopy.isHomotopyEquiv_iff {f g : AInfinityHom AA BB} (h : Homotopy f g) :
    f.IsHomotopyEquiv ↔ g.IsHomotopyEquiv := h.homotopic.isHomotopyEquiv_iff
theorem isHomotopyEquiv_of_left_and_right {f : AInfinityHom AA BB}
    (hL : ∃ k : AInfinityHom BB AA, (k.comp f).Homotopic (AInfinityHom.id AA))
    (hR : ∃ g : AInfinityHom BB AA, (f.comp g).Homotopic (AInfinityHom.id BB)) :
    f.IsHomotopyEquiv := by
  obtain ⟨k, hk⟩ := hL; obtain ⟨g, hg⟩ := hR
  obtain ⟨Hk⟩ := (homotopic_def _ _).1 hk; obtain ⟨Hg⟩ := (homotopic_def _ _).1 hg
  exact (AInfinityHomotopyEquiv.ofRightHomotopyInverses Hk Hg).isHomotopyEquiv_invHom
theorem IsIso.isHomotopyEquiv {f : AInfinityHom AA BB} (hf : f.IsIso) : f.IsHomotopyEquiv :=
  (AInfinityHomotopyEquiv.ofLinearPartBijective f hf.linearPart_bijective).isHomotopyEquiv_toHom

/-- Every homotopy equivalence of `A∞` algebras is a quasi-isomorphism. -/
theorem IsHomotopyEquiv.isQuasiIso {f : AInfinityHom AA BB} (hf : f.IsHomotopyEquiv) :
    f.IsQuasiIso := by
  obtain ⟨e, rfl⟩ := (isHomotopyEquiv_iff_exists_homotopyEquiv f).1 hf; exact e.isQuasiIso_toHom

/-- Between minimal `A∞` algebras, homotopy equivalences coincide with strict `A∞` isomorphisms. -/
theorem isHomotopyEquiv_iff_isIso (hA : AA.IsMinimal) (hB : BB.IsMinimal)
    (f : AInfinityHom AA BB) : f.IsHomotopyEquiv ↔ f.IsIso :=
  ⟨fun hf ↦ hf.isQuasiIso.isIso hA hB, IsIso.isHomotopyEquiv⟩

end AInfinityHom

/-! ### Obstruction lifting from a linear chain-homotopy inverse -/

section ObstructionLifting

open ReducedTensorWords

variable {AA : AInfinityAlgebra R A} {BB : AInfinityAlgebra R B}

private abbrev Words := ReducedTensorWords
private abbrev BG (BB : AInfinityAlgebra R B) := BB.grading.shift 1
private noncomputable abbrev BW (BB : AInfinityAlgebra R B) := gradedPiece (BG BB)
private abbrev AP (AA : AInfinityAlgebra R A) := (AA.grading.shift 1).piece
private abbrev BP (BB : AInfinityAlgebra R B) := (BG BB).piece

private structure LinInv (f : AInfinityHom AA BB) (g₀ : B →ₗ[R] A)
    (hA : A →ₗ[R] A) (hB : B →ₗ[R] B) : Prop where
  hg₀ : LinearMap.IsHomogeneous g₀ BB.grading.piece AA.grading.piece 0
  hg₀_diff : AA.differential ∘ₗ g₀ = g₀ ∘ₗ BB.differential
  hhA : LinearMap.IsHomogeneous hA AA.grading.piece AA.grading.piece (-1)
  hhA_eq : LinearMap.id - g₀ ∘ₗ f.linearPart = AA.differential ∘ₗ hA + hA ∘ₗ AA.differential
  hhB : LinearMap.IsHomogeneous hB BB.grading.piece BB.grading.piece (-1)
  hhB_eq : LinearMap.id - f.linearPart ∘ₗ g₀ = BB.differential ∘ₗ hB + hB ∘ₗ BB.differential

private noncomputable def coneDiff {W : Type*} [AddCommGroup W] [Module R W]
    (f : AInfinityHom AA BB) (hA : A →ₗ[R] A) (hB : B →ₗ[R] B)
    (Φ : W →ₗ[R] A) (Ψ : W →ₗ[R] B) : W →ₗ[R] B :=
  Ψ - (f.linearPart ∘ₗ hA - hB ∘ₗ f.linearPart) ∘ₗ Φ

private noncomputable def coneLiftG {W : Type*} [AddCommGroup W] [Module R W]
    (f : AInfinityHom AA BB) (g₀ : B →ₗ[R] A) (hA : A →ₗ[R] A) (hB : B →ₗ[R] B)
    (Φ : W →ₗ[R] A) (Ψ : W →ₗ[R] B) : W →ₗ[R] A :=
  hA ∘ₗ Φ + g₀ ∘ₗ coneDiff f hA hB Φ Ψ

private noncomputable def coneLiftH {W : Type*} [AddCommGroup W] [Module R W]
    (f : AInfinityHom AA BB) (hA : A →ₗ[R] A) (hB : B →ₗ[R] B)
    (Φ : W →ₗ[R] A) (Ψ : W →ₗ[R] B) : W →ₗ[R] B :=
  hB ∘ₗ coneDiff f hA hB Φ Ψ

private theorem isHomogeneous_coneLift {f : AInfinityHom AA BB} {g₀ : B →ₗ[R] A}
    {hA : A →ₗ[R] A} {hB : B →ₗ[R] B} (hi : LinInv f g₀ hA hB)
    {Φ : Words R B →ₗ[R] A} {Ψ : Words R B →ₗ[R] B}
    (hΦ : LinearMap.IsHomogeneous Φ (BW BB) (AP AA) 1)
    (hΨ : LinearMap.IsHomogeneous Ψ (BW BB) (BP BB) 0) :
    LinearMap.IsHomogeneous (coneLiftG f g₀ hA hB Φ Ψ) (BW BB) (AP AA) 0 ∧
      LinearMap.IsHomogeneous (coneLiftH f hA hB Φ Ψ) (BW BB) (BP BB) (-1) := by
  have hf₁ := (LinearMap.isHomogeneous_shift_piece_iff (c := 1)).2 f.isHomogeneous_linearPart
  have hg₀' := (LinearMap.isHomogeneous_shift_piece_iff (c := 1)).2 hi.hg₀
  have hhA' := (LinearMap.isHomogeneous_shift_piece_iff (c := 1)).2 hi.hhA
  have hhB' := (LinearMap.isHomogeneous_shift_piece_iff (c := 1)).2 hi.hhB
  have hΔ : LinearMap.IsHomogeneous (f.linearPart ∘ₗ hA - hB ∘ₗ f.linearPart)
      (AP AA) (BP BB) (-1) :=
    LinearMap.IsHomogeneous.sub (by simpa using hf₁.comp hhA') (by simpa using hhB'.comp hf₁)
  have hd : LinearMap.IsHomogeneous (coneDiff f hA hB Φ Ψ) (BW BB) (BP BB) 0 :=
    hΨ.sub (by simpa using hΔ.comp hΦ)
  exact ⟨LinearMap.IsHomogeneous.add (by simpa using hhA'.comp hΦ) (by simpa using hg₀'.comp hd),
    by simpa [coneLiftH] using hhB'.comp hd⟩

private theorem coneLift_coboundary {W : Type*} [AddCommGroup W] [Module R W]
    {f : AInfinityHom AA BB} {g₀ : B →ₗ[R] A} {hA : A →ₗ[R] A} {hB : B →ₗ[R] B}
    (hi : LinInv f g₀ hA hB) {dW : W →ₗ[R] W} {Φ : W →ₗ[R] A} {Ψ : W →ₗ[R] B} {w : W}
    (hΦ : AA.differential (Φ w) + Φ (dW w) = 0)
    (hΨ : BB.differential (Ψ w) - Ψ (dW w) = f.linearPart (Φ w)) :
    AA.differential (coneLiftG f g₀ hA hB Φ Ψ w) - coneLiftG f g₀ hA hB Φ Ψ (dW w) = Φ w ∧
      f.linearPart (coneLiftG f g₀ hA hB Φ Ψ w) +
        BB.differential (coneLiftH f hA hB Φ Ψ w) + coneLiftH f hA hB Φ Ψ (dW w) = Ψ w := by
  have hf_diff (a) : BB.differential (f.linearPart a) = f.linearPart (AA.differential a) := by
    rw [BB.differential_apply, AA.differential_apply, f.linearPart_m_one]
  have hg₀_d (b) : AA.differential (g₀ b) = g₀ (BB.differential b) :=
    LinearMap.congr_fun hi.hg₀_diff b
  have hhA' (a) := (LinearMap.congr_fun hi.hhA_eq a).symm
  have hhB' (b) := (LinearMap.congr_fun hi.hhB_eq b).symm
  set Δh : A →ₗ[R] B := f.linearPart ∘ₗ hA - hB ∘ₗ f.linearPart with hΔh_def
  have hΔh (a) : BB.differential (Δh a) + Δh (AA.differential a) = 0 := by
    have eA := congrArg f.linearPart (hhA' a); have eB := hhB' (f.linearPart a)
    simp only [hΔh_def, LinearMap.sub_apply, LinearMap.add_apply, LinearMap.id_apply,
      LinearMap.comp_apply, map_sub, map_add, hf_diff] at eA eB ⊢
    calc _ = (f.linearPart (AA.differential (hA a)) + f.linearPart (hA (AA.differential a))) -
        (BB.differential (hB (f.linearPart a)) + hB (f.linearPart (AA.differential a))) := by abel
      _ = 0 := by rw [eA, eB]; abel
  have hΦ' : Φ (dW w) = -AA.differential (Φ w) := eq_neg_of_add_eq_zero_right hΦ
  set Ψ' := coneDiff f hA hB Φ Ψ with hΨ'_def
  have hΨ' : Ψ' (dW w) = BB.differential (Ψ' w) - f.linearPart (Φ w) := by
    have eΔ := eq_neg_of_add_eq_zero_left (hΔh (Φ w))
    have eΨ : Ψ (dW w) = BB.differential (Ψ w) - f.linearPart (Φ w) := by rw [← hΨ]; abel
    simp only [hΨ'_def, coneDiff, ← hΔh_def, LinearMap.sub_apply, LinearMap.comp_apply,
      map_sub, hΦ', map_neg, eΔ, eΨ]; abel
  simp only [LinearMap.sub_apply, LinearMap.add_apply, LinearMap.id_apply, LinearMap.comp_apply]
    at hhA' hhB'
  refine ⟨?_, ?_⟩
  · rw [coneLiftG, ← hΨ'_def]
    simp only [LinearMap.add_apply, LinearMap.comp_apply, map_add, hg₀_d, hΦ', hΨ', map_neg,
      map_sub]
    calc _ = (AA.differential (hA (Φ w)) + hA (AA.differential (Φ w))) +
        g₀ (f.linearPart (Φ w)) := by abel
      _ = Φ w := by rw [hhA']; abel
  · rw [coneLiftG, coneLiftH, ← hΨ'_def]
    simp only [LinearMap.add_apply, LinearMap.comp_apply, map_add, hΨ']
    calc _ = (BB.differential (hB (Ψ' w)) + hB (BB.differential (Ψ' w))) +
        f.linearPart (g₀ (Ψ' w)) + Δh (Φ w) := by
          simp only [map_sub, hΔh_def, LinearMap.sub_apply, LinearMap.comp_apply]; abel
      _ = Ψ w := by rw [hhB', hΨ'_def, coneDiff, ← hΔh_def]; simp

private noncomputable def morphError (AA : AInfinityAlgebra R A) (BB : AInfinityAlgebra R B)
    (γ : Words R B →ₗ[R] A) : Words R B →ₗ[R] Words R A :=
  AA.barDifferential ∘ₗ coalgHom R γ - coalgHom R γ ∘ₗ BB.barDifferential

private noncomputable def homotopyError (f : AInfinityHom AA BB) (γ : Words R B →ₗ[R] A)
    (η : Words R B →ₗ[R] B) : Words R B →ₗ[R] Words R B :=
  let H := gradedCoderivAlong (BG BB) 1 LinearMap.id (f.barMap ∘ₗ coalgHom R γ) η
  LinearMap.id - f.barMap ∘ₗ coalgHom R γ - (BB.barDifferential ∘ₗ H + H ∘ₗ BB.barDifferential)

private theorem coalgHom_add_apply_of_mem_filtration_succ {γ δg : Words R B →ₗ[R] A} {n : ℕ}
    (hδg : ∀ u ∈ filtration R B n, δg u = 0) {z : Words R B} (hz : z ∈ filtration R B (n + 1)) :
    coalgHom R (γ + δg) z = coalgHom R γ z + ofLetter R A (δg z) := by
  have hγeq : ∀ u ∈ filtration R B n, (γ + δg) u = γ u := fun u hu ↦ by simp [hδg u hu]
  have hGeq : ∀ u ∈ filtration R B n, coalgHom R (γ + δg) u = coalgHom R γ u := fun u hu ↦
    (isCoalgHom_coalgHom _).apply_eq_of_mem_filtration (isCoalgHom_coalgHom _)
      (fun w hw ↦ by
        simpa only [← LinearMap.comp_apply (letter R A), letter_comp_coalgHom] using hγeq w hw) hu
  have eq1 := LinearMap.congr_fun (isCoalgHom_coalgHom (γ + δg)).eq_ofLetter_add_cutPrepend z
  have eq2 := LinearMap.congr_fun (isCoalgHom_coalgHom γ).eq_ofLetter_add_cutPrepend z
  simp only [letter_comp_coalgHom, LinearMap.add_apply, LinearMap.comp_apply, map_add] at eq1 eq2
  rw [eq1, eq2, cutPrepend_congr_of_mem_filtration_succ hγeq hGeq hz]; abel

private theorem gradedCoderivAlong_add_apply_of_mem_filtration_succ (f : AInfinityHom AA BB)
    {γ δg : Words R B →ₗ[R] A} {η δh : Words R B →ₗ[R] B} {n : ℕ}
    (hδg : ∀ u ∈ filtration R B n, δg u = 0) (hδh : ∀ u ∈ filtration R B n, δh u = 0)
    {z : Words R B} (hz : z ∈ filtration R B (n + 1)) :
    gradedCoderivAlong (BG BB) 1 LinearMap.id (f.barMap ∘ₗ coalgHom R (γ + δg)) (η + δh) z =
      gradedCoderivAlong (BG BB) 1 LinearMap.id (f.barMap ∘ₗ coalgHom R γ) η z +
        ofLetter R B (δh z) := by
  have hηeq : ∀ u ∈ filtration R B n, (η + δh) u = η u := fun u hu ↦ by simp [hδh u hu]
  have hFeq : ∀ u ∈ filtration R B n,
      (f.barMap ∘ₗ coalgHom R (γ + δg)) u = (f.barMap ∘ₗ coalgHom R γ) u := fun u hu ↦ by
    rcases n with _ | m
    · rw [filtration_zero, Submodule.mem_bot] at hu; simp [hu]
    · simp only [LinearMap.comp_apply, coalgHom_add_apply_of_mem_filtration_succ
        (fun w hw ↦ hδg w (filtration_monotone R B m.le_succ hw)) hu, hδg u hu, map_zero, add_zero]
  have hc1 := isGradedCoderivationAlong_gradedCoderivAlong (G := BG BB) 1
    (isCoalgHom_id B) (f.isCoalgHom_barMap.comp (isCoalgHom_coalgHom (γ + δg))) (η + δh)
  have hc2 := isGradedCoderivationAlong_gradedCoderivAlong (G := BG BB) 1
    (isCoalgHom_id B) (f.isCoalgHom_barMap.comp (isCoalgHom_coalgHom γ)) η
  have hHeq : ∀ u ∈ filtration R B n,
      gradedCoderivAlong (BG BB) 1 LinearMap.id (f.barMap ∘ₗ coalgHom R (γ + δg)) (η + δh) u =
      gradedCoderivAlong (BG BB) 1 LinearMap.id (f.barMap ∘ₗ coalgHom R γ) η u := fun u hu ↦
    hc1.apply_eq_of_mem_filtration hc2 (fun _ _ _ _ ↦ rfl)
      (fun _ hk w hw ↦ hFeq w (filtration_monotone R B hk.le hw))
      (fun w hw ↦ by
        simpa only [← LinearMap.comp_apply (letter R B), letter_comp_gradedCoderivAlong] using
          hηeq w hw) hu
  have eq1 := LinearMap.congr_fun (gradedCoderivAlong_eq (BG BB) 1 LinearMap.id
    (f.barMap ∘ₗ coalgHom R (γ + δg)) (η + δh)) z
  have eq2 := LinearMap.congr_fun (gradedCoderivAlong_eq (BG BB) 1 LinearMap.id
    (f.barMap ∘ₗ coalgHom R γ) η) z
  simp only [LinearMap.add_apply] at eq1 eq2
  rw [eq1, eq2, LinearMap.comp_apply, LinearMap.comp_apply, LinearMap.add_apply, map_add,
    cutPrepend_congr_of_mem_filtration_succ hηeq hFeq hz,
    cutPrepend_congr_of_mem_filtration_succ (fun _ _ ↦ rfl) hHeq hz]; abel

private theorem morphError_eq_ofLetter {γ : Words R B →ₗ[R] A}
    (hγ : LinearMap.IsHomogeneous γ (BW BB) (AP AA) 0) {n : ℕ}
    (hEG : ∀ u ∈ filtration R B n, morphError AA BB γ u = 0) {z : Words R B}
    (hz : z ∈ filtration R B (n + 1)) :
    morphError AA BB γ z = ofLetter R A (letter R A (morphError AA BB γ z)) := by
  have hG := isCoalgHom_coalgHom γ
  have hcod : IsGradedCoderivationAlong (BG BB) 1 (coalgHom R γ) (coalgHom R γ)
      (morphError AA BB γ) := by
    rw [show morphError AA BB γ =
      AA.barDifferential ∘ₗ coalgHom R γ + (-1 : R) • (coalgHom R γ ∘ₗ BB.barDifferential) by
      ext; simp [morphError, sub_eq_add_neg]]
    exact (AA.isGradedCoderivation_barDifferential.comp_isCoalgHom hG
      (isHomogeneous_coalgHom hγ)).add
      ((hG.comp_isGradedCoderivation BB.isGradedCoderivation_barDifferential).smul (-1 : R))
  refine eq_of_deconcatenation_eq_of_letter_eq R A ?_ (letter_ofLetter R A _).symm
  obtain ⟨w, hw⟩ := map_deconcatenation_filtration_succ_le R B n ⟨z, hz, rfl⟩
  rw [deconcatenation_ofLetter, hcod.deconcatenation_apply, ← hw]; clear hw
  induction w using TensorProduct.inductionOn with
  | tmul u v => simp only [TensorProduct.mapIncl, TensorProduct.map_tmul, Submodule.coe_subtype,
      LinearMap.rTensor_tmul, hEG _ u.2, hEG _ v.2, TensorProduct.zero_tmul,
      TensorProduct.tmul_zero, add_zero]
  | add _ _ hu hv => simp only [map_add] at hu hv ⊢; rw [add_add_add_comm, hu, hv, add_zero]

private theorem homotopyError_eq_ofLetter (f : AInfinityHom AA BB) {γ : Words R B →ₗ[R] A}
    {η : Words R B →ₗ[R] B} (hγ : LinearMap.IsHomogeneous γ (BW BB) (AP AA) 0)
    (hη : LinearMap.IsHomogeneous η (BW BB) (BP BB) (-1)) {n : ℕ}
    (hEG : ∀ u ∈ filtration R B n, morphError AA BB γ u = 0)
    (hEH : ∀ u ∈ filtration R B n, homotopyError f γ η u = 0) {z : Words R B}
    (hz : z ∈ filtration R B (n + 1)) :
    homotopyError f γ η z = ofLetter R B (letter R B (homotopyError f γ η z)) := by
  set G := coalgHom R γ with hG_def
  set H := gradedCoderivAlong (BG BB) 1 LinearMap.id (f.barMap ∘ₗ G) η with hH_def
  set bB := BB.barDifferential with hbB_def
  set τB := map R ((BG BB).koszulTwist 1) with hτB_def
  have hFG : IsCoalgHom R (f.barMap ∘ₗ G) := f.isCoalgHom_barMap.comp (isCoalgHom_coalgHom γ)
  have hH := isGradedCoderivationAlong_gradedCoderivAlong (G := BG BB) 1 (isCoalgHom_id B) hFG η
  have hFG_hom : LinearMap.IsHomogeneous (f.barMap ∘ₗ G) (BW BB) (BW BB) 0 := by
    simpa using f.isHomogeneous_barMap.comp (isHomogeneous_coalgHom hγ)
  have hH₁ := isHomogeneous_gradedCoderivAlong (q := 1) (LinearMap.isHomogeneous_id _) hFG_hom hη
  have hτH (w) : τB (H w) = -H (τB w) := by
    simpa only [show ((1 : ℤ) * (-1)).negOnePow = -1 by decide, Units.val_neg, Units.val_one,
      Int.cast_neg, Int.cast_one, neg_one_smul, LinearMap.comp_apply, LinearMap.smul_apply] using
      LinearMap.congr_fun (hH₁.map_koszulTwist_comp 1) w
  have hτb (w) : τB (bB w) = -bB (τB w) := by
    simpa only [show ((1 : ℤ) * 1).negOnePow = -1 by decide, Units.val_neg, Units.val_one,
      Int.cast_neg, Int.cast_one, neg_one_smul, LinearMap.comp_apply, LinearMap.smul_apply] using
      LinearMap.congr_fun (BB.isHomogeneous_barDifferential.map_koszulTwist_comp 1) w
  have hττ (w) : τB (τB w) = w := by
    rw [hτB_def, ← LinearMap.comp_apply, ← map_comp, InternalGrading.koszulTwist_comp_self,
      map_id, LinearMap.id_apply]
  have hFGb : ∀ v ∈ filtration R B n, bB (f.barMap (G v)) = f.barMap (G (bB v)) := fun v hv ↦ by
    rw [hbB_def, f.barDifferential_barMap, hG_def]
    exact congrArg f.barMap (sub_eq_zero.1 (hEG v hv))
  refine eq_of_deconcatenation_eq_of_letter_eq R B ?_ (letter_ofLetter R B _).symm
  obtain ⟨w, hw⟩ := map_deconcatenation_filtration_succ_le R B n ⟨z, hz, rfl⟩
  have hsub := ((isCoalgHom_id B).isGradedCoderivationAlong_sub
    (G := BG BB) hFG).deconcatenation_apply z
  rw [InternalGrading.koszulTwist_zero, map_id, LinearMap.rTensor_id] at hsub
  have heh_def : homotopyError f γ η = LinearMap.id - f.barMap ∘ₗ G - (bB ∘ₗ H + H ∘ₗ bB) := rfl
  rw [deconcatenation_ofLetter, heh_def, LinearMap.sub_apply, LinearMap.add_apply,
    LinearMap.comp_apply, LinearMap.comp_apply, map_sub, map_add, hsub,
    BB.isGradedCoderivation_barDifferential.deconcatenation_apply, hH.deconcatenation_apply,
    hH.deconcatenation_apply, BB.isGradedCoderivation_barDifferential.deconcatenation_apply,
    ← hH_def, ← hbB_def, ← hτB_def, ← hw]; clear hw hsub
  induction w using TensorProduct.inductionOn with
  | tmul u v =>
      have eu := hEH u.1 u.2; have ev := hEH v.1 v.2; rw [heh_def] at eu ev
      simp only [LinearMap.sub_apply, LinearMap.add_apply, LinearMap.id_apply,
        LinearMap.comp_apply] at eu ev
      simp only [TensorProduct.mapIncl, TensorProduct.map_tmul, Submodule.coe_subtype, map_add,
        LinearMap.rTensor_tmul, LinearMap.lTensor_tmul, LinearMap.sub_apply, LinearMap.id_apply,
        LinearMap.comp_apply]
      simp only [hτH, hτb, hττ, hFGb v.1 v.2, TensorProduct.neg_tmul]
      refine Eq.trans ?_
        (by rw [eu, ev, TensorProduct.zero_tmul, TensorProduct.tmul_zero, add_zero] :
          (u.1 - f.barMap (G u.1) - (bB (H u.1) + H (bB u.1))) ⊗ₜ[R] f.barMap (G v.1) +
            u.1 ⊗ₜ[R] (v.1 - f.barMap (G v.1) - (bB (H v.1) + H (bB v.1))) = 0)
      simp only [TensorProduct.sub_tmul, TensorProduct.tmul_sub, TensorProduct.add_tmul,
        TensorProduct.tmul_add]; abel
  | add _ _ hu hv =>
      simp only [map_add] at hu hv ⊢; convert congrArg₂ (· + ·) hu hv using 1 <;> abel

private theorem cocycle_of_errors_zero (f : AInfinityHom AA BB) {γ : Words R B →ₗ[R] A}
    {η : Words R B →ₗ[R] B} (hγ : LinearMap.IsHomogeneous γ (BW BB) (AP AA) 0)
    (hη : LinearMap.IsHomogeneous η (BW BB) (BP BB) (-1)) {n : ℕ}
    (hEG : ∀ u ∈ filtration R B n, morphError AA BB γ u = 0)
    (hEH : ∀ u ∈ filtration R B n, homotopyError f γ η u = 0) {z : Words R B}
    (hz : z ∈ filtration R B (n + 1)) :
    AA.differential (-(letter R A (morphError AA BB γ z))) +
        (-(letter R A (morphError AA BB γ (BB.barDifferential z)))) = 0 ∧
      BB.differential (letter R B (homotopyError f γ η z)) -
        letter R B (homotopyError f γ η (BB.barDifferential z)) =
          f.linearPart (-(letter R A (morphError AA BB γ z))) := by
  have hbz := BB.barDifferential_mem_filtration hz
  have hbA_sq (w) : AA.barDifferential (AA.barDifferential w) = 0 :=
    LinearMap.congr_fun AA.barDifferential_sq w
  have hbB_sq (w) : BB.barDifferential (BB.barDifferential w) = 0 :=
    LinearMap.congr_fun BB.barDifferential_sq w
  refine ⟨?_, ?_⟩
  · have h0' := congrArg (letter R A) (show AA.barDifferential (morphError AA BB γ z) +
        morphError AA BB γ (BB.barDifferential z) = 0 by simp [morphError, hbA_sq, hbB_sq])
    rw [morphError_eq_ofLetter hγ hEG hz, morphError_eq_ofLetter hγ hEG hbz, map_add,
      AInfinityAlgebra.barDifferential_ofLetter, letter_ofLetter, letter_ofLetter, map_zero,
      ← AA.differential_apply] at h0'
    rw [map_neg, ← neg_add, h0', neg_zero]
  · have h1' := congrArg (letter R B) (show BB.barDifferential (homotopyError f γ η z) -
        homotopyError f γ η (BB.barDifferential z) = -f.barMap (morphError AA BB γ z) by
      simp only [homotopyError, morphError, LinearMap.sub_apply, LinearMap.add_apply,
        LinearMap.id_apply, LinearMap.comp_apply, map_sub, map_add, hbB_sq, map_zero,
        f.barDifferential_barMap]; abel)
    rwa [homotopyError_eq_ofLetter f hγ hη hEG hEH hz,
      homotopyError_eq_ofLetter f hγ hη hEG hEH hbz, morphError_eq_ofLetter hγ hEG hz,
      map_sub, map_neg, AInfinityAlgebra.barDifferential_ofLetter, f.barMap_ofLetter,
      letter_ofLetter, letter_ofLetter, letter_ofLetter, ← BB.differential_apply, ← map_neg] at h1'

private noncomputable def liftPairSeq (f : AInfinityHom AA BB)
    (g₀ : B →ₗ[R] A) (hA : A →ₗ[R] A) (hB : B →ₗ[R] B) :
    ℕ → (Words R B →ₗ[R] A) × (Words R B →ₗ[R] B)
  | 0 => (g₀ ∘ₗ letter R B, hB ∘ₗ letter R B)
  | n + 1 =>
    let p := liftPairSeq f g₀ hA hB n
    let Φ := -(letter R A ∘ₗ morphError AA BB p.1); let Ψ := letter R B ∘ₗ homotopyError f p.1 p.2
    (p.1 + coneLiftG f g₀ hA hB Φ Ψ, p.2 + coneLiftH f hA hB Φ Ψ)

private theorem liftPairSeq_invariant {f : AInfinityHom AA BB} {g₀ : B →ₗ[R] A}
    {hA : A →ₗ[R] A} {hB : B →ₗ[R] B} (hi : LinInv f g₀ hA hB) (n : ℕ) :
    LinearMap.IsHomogeneous (liftPairSeq f g₀ hA hB n).1 (BW BB) (AP AA) 0 ∧
      LinearMap.IsHomogeneous (liftPairSeq f g₀ hA hB n).2 (BW BB) (BP BB) (-1) ∧
      (∀ z ∈ filtration R B (n + 1), morphError AA BB (liftPairSeq f g₀ hA hB n).1 z = 0) ∧
      (∀ z ∈ filtration R B (n + 1),
        homotopyError f (liftPairSeq f g₀ hA hB n).1 (liftPairSeq f g₀ hA hB n).2 z = 0) := by
  induction n with
  | zero =>
      have hγ₀ : LinearMap.IsHomogeneous (liftPairSeq f g₀ hA hB 0).1 (BW BB) (AP AA) 0 := by
        simpa [liftPairSeq] using ((LinearMap.isHomogeneous_shift_piece_iff (c := 1)).2
          hi.hg₀).comp (isHomogeneous_letter _)
      have hη₀ : LinearMap.IsHomogeneous (liftPairSeq f g₀ hA hB 0).2 (BW BB) (BP BB) (-1) := by
        simpa [liftPairSeq] using ((LinearMap.isHomogeneous_shift_piece_iff (c := 1)).2
          hi.hhB).comp (isHomogeneous_letter _)
      refine ⟨hγ₀, hη₀, apply_eq_zero_of_mem_filtration_one R B (LinearMap.ext fun b ↦ ?_),
        apply_eq_zero_of_mem_filtration_one R B (LinearMap.ext fun b ↦ ?_)⟩
      · have hg : AA.differential (g₀ b) = g₀ (BB.differential b) :=
          LinearMap.congr_fun hi.hg₀_diff b
        simp only [liftPairSeq, morphError, LinearMap.comp_apply, LinearMap.sub_apply,
          LinearMap.zero_apply, coalgHom_ofLetter, letter_ofLetter,
          AInfinityAlgebra.barDifferential_ofLetter, ← AA.differential_apply,
          ← BB.differential_apply, hg, sub_self]
      · have hb := LinearMap.congr_fun hi.hhB_eq b
        simp only [LinearMap.sub_apply, LinearMap.id_apply, LinearMap.comp_apply,
          LinearMap.add_apply] at hb
        simp only [liftPairSeq, homotopyError, LinearMap.comp_apply, LinearMap.sub_apply,
          LinearMap.add_apply, LinearMap.id_apply, LinearMap.zero_apply, coalgHom_ofLetter,
          letter_ofLetter, f.barMap_ofLetter, AInfinityAlgebra.barDifferential_ofLetter,
          gradedCoderivAlong_ofLetter, ← BB.differential_apply, ← map_add, ← hb, map_sub, sub_self]
  | succ n ih =>
      obtain ⟨hγ, hη, hEG, hEH⟩ := ih
      set γ := (liftPairSeq f g₀ hA hB n).1; set η := (liftPairSeq f g₀ hA hB n).2
      set Φ := -(letter R A ∘ₗ morphError AA BB γ); set Ψ := letter R B ∘ₗ homotopyError f γ η
      set δg := coneLiftG f g₀ hA hB Φ Ψ; set δh := coneLiftH f hA hB Φ Ψ
      have hG₀ := isHomogeneous_coalgHom hγ
      have hEG₁ : LinearMap.IsHomogeneous (morphError AA BB γ) (BW BB) (BW AA) 1 :=
        LinearMap.IsHomogeneous.sub (by simpa using AA.isHomogeneous_barDifferential.comp hG₀)
          (by simpa using hG₀.comp BB.isHomogeneous_barDifferential)
      have hFG₀ : LinearMap.IsHomogeneous (f.barMap ∘ₗ coalgHom R γ) (BW BB) (BW BB) 0 := by
        simpa using f.isHomogeneous_barMap.comp hG₀
      have hH₁ := isHomogeneous_gradedCoderivAlong (q := 1)
        (LinearMap.isHomogeneous_id _) hFG₀ hη
      have hEH₀ : LinearMap.IsHomogeneous (homotopyError f γ η) (BW BB) (BW BB) 0 :=
        ((LinearMap.isHomogeneous_id _).sub hFG₀).sub (LinearMap.IsHomogeneous.add
          (by simpa using BB.isHomogeneous_barDifferential.comp hH₁)
          (by simpa using hH₁.comp BB.isHomogeneous_barDifferential))
      have hΦ : LinearMap.IsHomogeneous Φ (BW BB) (AP AA) 1 :=
        LinearMap.IsHomogeneous.neg (by simpa using (isHomogeneous_letter _).comp hEG₁)
      have hΨ : LinearMap.IsHomogeneous Ψ (BW BB) (BP BB) 0 := by
        simpa [Ψ] using (isHomogeneous_letter _).comp hEH₀
      obtain ⟨hdG, hdH⟩ := isHomogeneous_coneLift hi hΦ hΨ
      have hδg0 : ∀ u ∈ filtration R B (n + 1), δg u = 0 := fun u hu ↦ by
        simp [δg, coneLiftG, coneDiff, Φ, Ψ, hEG u hu, hEH u hu]
      have hδh0 : ∀ u ∈ filtration R B (n + 1), δh u = 0 := fun u hu ↦ by
        simp [δh, coneLiftH, coneDiff, Φ, Ψ, hEG u hu, hEH u hu]
      have hstep : ∀ z ∈ filtration R B (n + 2),
          morphError AA BB (γ + δg) z = 0 ∧ homotopyError f (γ + δg) (η + δh) z = 0 := fun z hz ↦ by
        have hbz := BB.barDifferential_mem_filtration hz
        obtain ⟨hcG, hcH⟩ := cocycle_of_errors_zero f hγ hη hEG hEH hz
        obtain ⟨heqG, heqH⟩ := coneLift_coboundary hi (dW := BB.barDifferential)
          (Φ := Φ) (Ψ := Ψ) hcG hcH
        refine ⟨?_, ?_⟩
        · rw [morphError, LinearMap.sub_apply, LinearMap.comp_apply, LinearMap.comp_apply,
            coalgHom_add_apply_of_mem_filtration_succ hδg0 hz,
            coalgHom_add_apply_of_mem_filtration_succ hδg0 hbz, map_add,
            AInfinityAlgebra.barDifferential_ofLetter, ← AA.differential_apply]
          calc _ = morphError AA BB γ z +
              ofLetter R A (AA.differential (δg z) - δg (BB.barDifferential z)) := by
                rw [morphError, LinearMap.sub_apply, LinearMap.comp_apply, LinearMap.comp_apply,
                  map_sub]; abel
            _ = 0 := by rw [morphError_eq_ofLetter hγ hEG hz, heqG]; simp [Φ]
        · rw [homotopyError, LinearMap.sub_apply, LinearMap.sub_apply, LinearMap.id_apply,
            LinearMap.comp_apply, LinearMap.add_apply, LinearMap.comp_apply, LinearMap.comp_apply,
            coalgHom_add_apply_of_mem_filtration_succ hδg0 hz,
            gradedCoderivAlong_add_apply_of_mem_filtration_succ f hδg0 hδh0 hz,
            gradedCoderivAlong_add_apply_of_mem_filtration_succ f hδg0 hδh0 hbz,
            map_add, map_add, f.barMap_ofLetter, AInfinityAlgebra.barDifferential_ofLetter,
            ← BB.differential_apply]
          calc _ = homotopyError f γ η z -
              ofLetter R B (f.linearPart (δg z) + BB.differential (δh z) +
                δh (BB.barDifferential z)) := by
                rw [homotopyError, LinearMap.sub_apply, LinearMap.sub_apply, LinearMap.id_apply,
                  LinearMap.comp_apply, LinearMap.add_apply, LinearMap.comp_apply,
                  LinearMap.comp_apply, map_add, map_add]; abel
            _ = 0 := by rw [homotopyError_eq_ofLetter f hγ hη hEG hEH hz, heqH]; simp [Ψ]
      exact ⟨hγ.add hdG, hη.add hdH, fun z hz ↦ (hstep z hz).1, fun z hz ↦ (hstep z hz).2⟩

private noncomputable def rightHomotopyInverse (f : AInfinityHom AA BB)
    (g₀ : B →ₗ[R] A) (hA : A →ₗ[R] A) (hB : B →ₗ[R] B) (hi : LinInv f g₀ hA hB) :
    Σ' g : AInfinityHom BB AA, g.linearPart = g₀ ∧
      Nonempty (AInfinityHom.Homotopy (f.comp g) (AInfinityHom.id BB)) := by
  have hinv := liftPairSeq_invariant hi
  let γSeq := fun n ↦ (liftPairSeq f g₀ hA hB n).1
  let ηSeq := fun n ↦ (liftPairSeq f g₀ hA hB n).2
  have hstab : ∀ n, ∀ z ∈ filtration R B (n + 1),
      γSeq (n + 1) z = γSeq n z ∧ ηSeq (n + 1) z = ηSeq n z := fun n z hz ↦ by
    simp [γSeq, ηSeq, liftPairSeq, coneLiftG, coneLiftH, coneDiff,
      (hinv n).2.2.1 z hz, (hinv n).2.2.2 z hz]
  have hγ_stab : ∀ n, ∀ z ∈ filtration R B n, γSeq (n + 1) z = γSeq n z :=
    fun n z hz ↦ (hstab n z (filtration_monotone R B n.le_succ hz)).1
  have hη_stab : ∀ n, ∀ z ∈ filtration R B n, ηSeq (n + 1) z = ηSeq n z :=
    fun n z hz ↦ (hstab n z (filtration_monotone R B n.le_succ hz)).2
  let γ := filtrationLimit γSeq; let η := filtrationLimit ηSeq
  have hγ_hom := isHomogeneous_filtrationLimit hγ_stab fun n ↦ (hinv n).1
  have hη_hom := isHomogeneous_filtrationLimit hη_stab fun n ↦ (hinv n).2.1
  have hG_eq : ∀ n, ∀ z ∈ filtration R B n, coalgHom R γ z = coalgHom R (γSeq n) z :=
    fun _ z hz ↦ (isCoalgHom_coalgHom _).apply_eq_of_mem_filtration (isCoalgHom_coalgHom _)
      (fun w hw ↦ by
        simpa only [← LinearMap.comp_apply (letter R A), letter_comp_coalgHom] using
          filtrationLimit_apply_of_mem_filtration hγ_stab hw) hz
  have hγ_eq : AA.taylor ∘ₗ coalgHom R γ = γ ∘ₗ BB.barDifferential := by
    refine LinearMap.ext fun z ↦ ?_; obtain ⟨n, hn⟩ := exists_mem_filtration R B z
    have h0 := congrArg (letter R A) ((hinv n).2.2.1 z (filtration_monotone R B n.le_succ hn))
    rw [morphError, LinearMap.sub_apply, LinearMap.comp_apply, LinearMap.comp_apply,
      map_sub, map_zero, sub_eq_zero, ← LinearMap.comp_apply (letter R A) AA.barDifferential,
      AA.letter_comp_barDifferential, ← LinearMap.comp_apply (letter R A) (coalgHom R _),
      letter_comp_coalgHom] at h0
    rw [LinearMap.comp_apply, LinearMap.comp_apply, hG_eq n z hn, h0,
      filtrationLimit_apply_of_mem_filtration hγ_stab (BB.barDifferential_mem_filtration hn)]
  let g : AInfinityHom BB AA := AInfinityHom.ofTaylor γ hγ_hom hγ_eq
  have hg_bar : g.barMap = coalgHom R γ := AInfinityHom.barMap_ofTaylor γ hγ_hom hγ_eq
  have hg_lin : g.linearPart = g₀ := by
    ext b; have hb := ofLetter_mem_filtration R B b
    rw [AInfinityHom.linearPart_apply, AInfinityHom.taylor_ofTaylor,
      filtrationLimit_apply_of_mem_filtration hγ_stab hb, (hstab 0 _ hb).1]
    simp [γSeq, liftPairSeq]
  have hH_eq : ∀ n, ∀ z ∈ filtration R B n,
      gradedCoderivAlong (BG BB) 1 LinearMap.id (f.barMap ∘ₗ g.barMap) η z =
      gradedCoderivAlong (BG BB) 1 LinearMap.id (f.barMap ∘ₗ coalgHom R (γSeq n)) (ηSeq n) z :=
    fun n z hz ↦
      (isGradedCoderivationAlong_gradedCoderivAlong (G := BG BB) 1 (isCoalgHom_id B)
        (f.isCoalgHom_barMap.comp g.isCoalgHom_barMap) η).apply_eq_of_mem_filtration
        (isGradedCoderivationAlong_gradedCoderivAlong (G := BG BB) 1 (isCoalgHom_id B)
          (f.isCoalgHom_barMap.comp (isCoalgHom_coalgHom (γSeq n))) (ηSeq n))
        (fun _ _ _ _ ↦ rfl)
        (fun _ hk w hw ↦ by
          rw [LinearMap.comp_apply, LinearMap.comp_apply, hg_bar,
            hG_eq n w (filtration_monotone R B hk.le hw)])
        (fun w hw ↦ by
          simpa only [← LinearMap.comp_apply (letter R B), letter_comp_gradedCoderivAlong] using
            filtrationLimit_apply_of_mem_filtration hη_stab hw) hz
  have hη_eq : (AInfinityHom.id BB).taylor - (f.comp g).taylor =
      BB.taylor ∘ₗ gradedCoderivAlong (BG BB) 1 (AInfinityHom.id BB).barMap (f.comp g).barMap η +
        η ∘ₗ BB.barDifferential := by
    refine LinearMap.ext fun z ↦ ?_; obtain ⟨n, hn⟩ := exists_mem_filtration R B z
    have h0 := congrArg (letter R B) ((hinv n).2.2.2 z (filtration_monotone R B n.le_succ hn))
    rw [homotopyError, LinearMap.sub_apply, LinearMap.sub_apply, LinearMap.id_apply,
      LinearMap.comp_apply, LinearMap.add_apply, LinearMap.comp_apply, LinearMap.comp_apply,
      map_sub, map_sub, map_add, map_zero, sub_eq_zero,
      ← LinearMap.comp_apply (letter R B) f.barMap, ← f.taylor_def,
      ← LinearMap.comp_apply (letter R B) BB.barDifferential, BB.letter_comp_barDifferential,
      ← LinearMap.comp_apply (letter R B) (gradedCoderivAlong ..),
      letter_comp_gradedCoderivAlong] at h0
    simp only [AInfinityHom.taylor_id, AInfinityHom.taylor_comp, AInfinityHom.barMap_id,
      AInfinityHom.barMap_comp, LinearMap.sub_apply, LinearMap.add_apply, LinearMap.comp_apply]
    rwa [hH_eq n z hn, hg_bar, hG_eq n z hn,
      filtrationLimit_apply_of_mem_filtration hη_stab (BB.barDifferential_mem_filtration hn)]
  exact ⟨g, hg_lin, ⟨(AInfinityHom.Homotopy.ofTaylor η hη_hom hη_eq).symm⟩⟩

/-- **Homotopy-inverse lifting over a commutative ring.**  Given an `A∞` morphism `f : AA ⟶ BB`
and a homogeneous chain-homotopy inverse `(g₀, hA, hB)` of `f.linearPart`, construct an explicit
`AInfinityHomotopyEquiv AA BB` extending `f` whose inverse has linear part `g₀`. -/
noncomputable def AInfinityHomotopyEquiv.ofLinearHomotopyInverse (f : AInfinityHom AA BB)
    (g₀ : B →ₗ[R] A) (hg₀ : LinearMap.IsHomogeneous g₀ BB.grading.piece AA.grading.piece 0)
    (hg₀_diff : AA.differential ∘ₗ g₀ = g₀ ∘ₗ BB.differential)
    (hA : A →ₗ[R] A) (hhA : LinearMap.IsHomogeneous hA AA.grading.piece AA.grading.piece (-1))
    (hhA_eq : LinearMap.id - g₀ ∘ₗ f.linearPart = AA.differential ∘ₗ hA + hA ∘ₗ AA.differential)
    (hB : B →ₗ[R] B) (hhB : LinearMap.IsHomogeneous hB BB.grading.piece BB.grading.piece (-1))
    (hhB_eq : LinearMap.id - f.linearPart ∘ₗ g₀ = BB.differential ∘ₗ hB + hB ∘ₗ BB.differential) :
    AInfinityHomotopyEquiv AA BB := by
  let r₁ := rightHomotopyInverse f g₀ hA hB ⟨hg₀, hg₀_diff, hhA, hhA_eq, hhB, hhB_eq⟩
  have hf_diff : BB.differential ∘ₗ f.linearPart = f.linearPart ∘ₗ AA.differential := by
    ext a; rw [LinearMap.comp_apply, LinearMap.comp_apply, BB.differential_apply,
      AA.differential_apply, f.linearPart_m_one]
  let r₂ := rightHomotopyInverse r₁.1 f.linearPart hB hA
    ⟨f.isHomogeneous_linearPart, hf_diff, hhB, by rwa [r₁.2.1], hhA, by rwa [r₁.2.1]⟩
  exact AInfinityHomotopyEquiv.ofRightHomotopyInverses
    (Classical.choice r₁.2.2) (Classical.choice r₂.2.2)

@[simp] theorem AInfinityHomotopyEquiv.toHom_ofLinearHomotopyInverse (f : AInfinityHom AA BB)
    (g₀ hg₀ hg₀_diff hA hhA hhA_eq hB hhB hhB_eq) :
    (AInfinityHomotopyEquiv.ofLinearHomotopyInverse f g₀ hg₀ hg₀_diff hA hhA hhA_eq
      hB hhB hhB_eq).toHom = f := (rfl)
@[simp] theorem AInfinityHomotopyEquiv.linearPart_invHom_ofLinearHomotopyInverse
    (f : AInfinityHom AA BB) (g₀ hg₀ hg₀_diff hA hhA hhA_eq hB hhB hhB_eq) :
    (AInfinityHomotopyEquiv.ofLinearHomotopyInverse f g₀ hg₀ hg₀_diff hA hhA hhA_eq
      hB hhB hhB_eq).invHom.linearPart = g₀ :=
  (rightHomotopyInverse f g₀ hA hB ⟨hg₀, hg₀_diff, hhA, hhA_eq, hhB, hhB_eq⟩).2.1

/-- **Homological Whitehead criterion over a commutative ring.**  An `A∞` morphism `f : AA ⟶ BB`
is a homotopy equivalence iff `f.linearPart` admits a homogeneous chain-homotopy inverse. -/
theorem AInfinityHom.isHomotopyEquiv_iff_exists_linearHomotopyInverse (f : AInfinityHom AA BB) :
    f.IsHomotopyEquiv ↔
      ∃ (g₀ : B →ₗ[R] A) (hA : A →ₗ[R] A) (hB : B →ₗ[R] B),
        LinearMap.IsHomogeneous g₀ BB.grading.piece AA.grading.piece 0 ∧
        AA.differential ∘ₗ g₀ = g₀ ∘ₗ BB.differential ∧
        LinearMap.IsHomogeneous hA AA.grading.piece AA.grading.piece (-1) ∧
        LinearMap.id - g₀ ∘ₗ f.linearPart = AA.differential ∘ₗ hA + hA ∘ₗ AA.differential ∧
        LinearMap.IsHomogeneous hB BB.grading.piece BB.grading.piece (-1) ∧
        LinearMap.id - f.linearPart ∘ₗ g₀ = BB.differential ∘ₗ hB + hB ∘ₗ BB.differential := by
  refine ⟨fun hf ↦ ?_, fun ⟨g₀, hA, hB, hg₀, hg₀_diff, hhA, hhA_eq, hhB, hhB_eq⟩ ↦
    (AInfinityHomotopyEquiv.ofLinearHomotopyInverse f g₀ hg₀ hg₀_diff hA hhA hhA_eq
      hB hhB hhB_eq).isHomotopyEquiv_toHom⟩
  obtain ⟨e, rfl⟩ := f.isHomotopyEquiv_iff_exists_homotopyEquiv.1 hf
  refine ⟨e.invHom.linearPart, e.leftHomotopy.symm.linearHomotopy,
    e.rightHomotopy.symm.linearHomotopy, e.invHom.isHomogeneous_linearPart, ?_, ?_, ?_, ?_, ?_⟩
  · ext b; rw [LinearMap.comp_apply, LinearMap.comp_apply, AA.differential_apply,
      BB.differential_apply, e.invHom.linearPart_m_one]
  · rw [LinearMap.isHomogeneous_def]; exact fun _ _ ha ↦ e.leftHomotopy.symm.linearHomotopy_mem ha
  · ext a; simpa only [LinearMap.sub_apply, LinearMap.id_apply, LinearMap.comp_apply,
      LinearMap.add_apply, AInfinityHom.linearPart_id, AInfinityHom.linearPart_comp,
      AA.differential_apply] using e.leftHomotopy.symm.linearPart_sub_linearPart a
  · rw [LinearMap.isHomogeneous_def]; exact fun _ _ hb ↦ e.rightHomotopy.symm.linearHomotopy_mem hb
  · ext b; simpa only [LinearMap.sub_apply, LinearMap.id_apply, LinearMap.comp_apply,
      LinearMap.add_apply, AInfinityHom.linearPart_id, AInfinityHom.linearPart_comp,
      BB.differential_apply] using e.rightHomotopy.symm.linearPart_sub_linearPart b

end ObstructionLifting

end CommRing

/-! ### Minimal-model homotopy equivalence and quasi-isomorphism inversion over a field -/

section Field

variable {K : Type uK} {A : Type uA} {B : Type uB} [Field K]
  [AddCommGroup A] [Module K A] [AddCommGroup B] [Module K B]

/-- The homotopy from `id_𝒜` to `minimalModelInclusion ∘ minimalModelProjection` over a field. -/
noncomputable def AInfinityAlgebra.minimalModelHomotopy (𝒜 : AInfinityAlgebra K A) :
    AInfinityHom.Homotopy (AInfinityHom.id 𝒜)
      (𝒜.minimalModelInclusion.comp 𝒜.minimalModelProjection) :=
  (𝒜.transferHomotopy 𝒜.cohomologyContraction 𝒜.isHomogeneous_cohomologyContraction_homotopy
    𝒜.isHomogeneous_cohomologyContraction_incl 𝒜.isHomogeneous_cohomologyContraction_proj).copy
    rfl 𝒜.minimalModelInclusion_comp_minimalModelProjection.symm

@[simp] theorem AInfinityAlgebra.linearHomotopy_minimalModelHomotopy (𝒜 : AInfinityAlgebra K A) :
    𝒜.minimalModelHomotopy.linearHomotopy = 𝒜.cohomologyContraction.homotopy := by
  simp [AInfinityAlgebra.minimalModelHomotopy]

/-- Over a field, every `A∞` algebra is homotopy equivalent to its minimal model on cohomology. -/
noncomputable def AInfinityAlgebra.minimalModelHomotopyEquiv (𝒜 : AInfinityAlgebra K A) :
    AInfinityHomotopyEquiv 𝒜.minimalModel 𝒜 where
  toHom := 𝒜.minimalModelInclusion
  invHom := 𝒜.minimalModelProjection
  leftHomotopy := (AInfinityHom.Homotopy.refl _).copy
    𝒜.minimalModelProjection_comp_minimalModelInclusion.symm rfl
  rightHomotopy := 𝒜.minimalModelHomotopy.symm

@[simp] theorem AInfinityAlgebra.toHom_minimalModelHomotopyEquiv (𝒜 : AInfinityAlgebra K A) :
    𝒜.minimalModelHomotopyEquiv.toHom = 𝒜.minimalModelInclusion := (rfl)
@[simp] theorem AInfinityAlgebra.invHom_minimalModelHomotopyEquiv (𝒜 : AInfinityAlgebra K A) :
    𝒜.minimalModelHomotopyEquiv.invHom = 𝒜.minimalModelProjection := (rfl)

namespace AInfinityHom

variable {AA : AInfinityAlgebra K A} {BB : AInfinityAlgebra K B}

/-- **Inversion of `A∞` quasi-isomorphisms up to homotopy over a field.** -/
noncomputable def IsQuasiIso.homotopyEquiv {f : AInfinityHom AA BB} (hf : f.IsQuasiIso) :
    AInfinityHomotopyEquiv AA BB := by
  let φ := (BB.minimalModelProjection.comp f).comp AA.minimalModelInclusion
  have hφ := (((BB.isQuasiIso_minimalModelProjection.comp hf).comp
    AA.isQuasiIso_minimalModelInclusion).isIso
    AA.isMinimal_minimalModel BB.isMinimal_minimalModel).linearPart_bijective
  let e := (AA.minimalModelHomotopyEquiv.symm.trans
    (AInfinityHomotopyEquiv.ofLinearPartBijective φ hφ)).trans BB.minimalModelHomotopyEquiv
  have h1 : Homotopy f (BB.minimalModelInclusion.comp (BB.minimalModelProjection.comp f)) :=
    (BB.minimalModelHomotopy.compLeft f).copy (id_comp f)
      (comp_assoc BB.minimalModelInclusion BB.minimalModelProjection f)
  have h2 : Homotopy (BB.minimalModelProjection.comp f) (φ.comp AA.minimalModelProjection) :=
    (AA.minimalModelHomotopy.compRight (BB.minimalModelProjection.comp f)).copy
      (comp_id _) (comp_assoc (BB.minimalModelProjection.comp f)
        AA.minimalModelInclusion AA.minimalModelProjection).symm
  exact e.replaceToHom (h1.trans (h2.compRight BB.minimalModelInclusion))

@[simp] theorem IsQuasiIso.toHom_homotopyEquiv {f : AInfinityHom AA BB} (hf : f.IsQuasiIso) :
    hf.homotopyEquiv.toHom = f := (rfl)

theorem IsQuasiIso.isHomotopyEquiv {f : AInfinityHom AA BB} (hf : f.IsQuasiIso) :
    f.IsHomotopyEquiv := hf.homotopyEquiv.isHomotopyEquiv_toHom

/-- **Whitehead theorem for `A∞` algebras over a field.** -/
theorem isHomotopyEquiv_iff_isQuasiIso (f : AInfinityHom AA BB) :
    f.IsHomotopyEquiv ↔ f.IsQuasiIso := ⟨IsHomotopyEquiv.isQuasiIso, IsQuasiIso.isHomotopyEquiv⟩

end AInfinityHom

end Field

end TauCeti
