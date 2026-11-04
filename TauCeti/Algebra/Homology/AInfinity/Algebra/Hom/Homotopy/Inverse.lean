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
def refl (AA : AInfinityAlgebra R A) : AInfinityHomotopyEquiv AA AA :=
  ⟨AInfinityHom.id AA, AInfinityHom.id AA,
    (AInfinityHom.Homotopy.refl _).copy (AInfinityHom.comp_id _).symm rfl,
    (AInfinityHom.Homotopy.refl _).copy (AInfinityHom.comp_id _).symm rfl⟩

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
    (hf : Function.Bijective f.linearPart) : AInfinityHomotopyEquiv AA BB :=
  ⟨f, f.inverse hf, (AInfinityHom.Homotopy.refl _).copy (f.inverse_comp_cancel hf).symm rfl,
    (AInfinityHom.Homotopy.refl _).copy (f.comp_inverse_cancel hf).symm rfl⟩

@[simp] theorem toHom_ofLinearPartBijective (f : AInfinityHom AA BB)
    (hf : Function.Bijective f.linearPart) : (ofLinearPartBijective f hf).toHom = f := (rfl)
@[simp] theorem invHom_ofLinearPartBijective (f : AInfinityHom AA BB)
    (hf : Function.Bijective f.linearPart) :
    (ofLinearPartBijective f hf).invHom = f.inverse hf := (rfl)

/-- Two-sided homotopy equivalence from right homotopy inverses `f ∘ g ~ id` and `g ∘ f' ~ id`. -/
noncomputable def ofRightHomotopyInverses {f f' : AInfinityHom AA BB} {g : AInfinityHom BB AA}
    (hfg : AInfinityHom.Homotopy (f.comp g) (AInfinityHom.id BB))
    (hgf' : AInfinityHom.Homotopy (g.comp f') (AInfinityHom.id AA)) :
    AInfinityHomotopyEquiv AA BB :=
  ⟨f, g, (((hgf'.symm.compRight f).copy (AInfinityHom.comp_id f)
      (AInfinityHom.comp_assoc f g f').symm).trans
      ((hfg.compLeft f').copy rfl (AInfinityHom.id_comp f')) |>.compRight g).trans hgf', hfg⟩

@[simp] theorem toHom_ofRightHomotopyInverses {f f' : AInfinityHom AA BB} {g : AInfinityHom BB AA}
    (hfg : AInfinityHom.Homotopy (f.comp g) (AInfinityHom.id BB))
    (hgf' : AInfinityHom.Homotopy (g.comp f') (AInfinityHom.id AA)) :
    (ofRightHomotopyInverses hfg hgf').toHom = f := (rfl)
@[simp] theorem invHom_ofRightHomotopyInverses {f f' : AInfinityHom AA BB} {g : AInfinityHom BB AA}
    (hfg : AInfinityHom.Homotopy (f.comp g) (AInfinityHom.id BB))
    (hgf' : AInfinityHom.Homotopy (g.comp f') (AInfinityHom.id AA)) :
    (ofRightHomotopyInverses hfg hgf').invHom = g := (rfl)

/-- The forward morphism of a homotopy equivalence is a quasi-isomorphism. -/
theorem isQuasiIso_toHom (e : AInfinityHomotopyEquiv AA BB) : e.toHom.IsQuasiIso :=
  (AInfinityHom.isQuasiIso_def _).2 <| Function.bijective_iff_has_inverse.2
    ⟨e.invHom.cohomologyMap,
      fun x ↦ by simpa [AInfinityHom.cohomologyMap_comp, AInfinityHom.cohomologyMap_id] using
        DFunLike.congr_fun e.leftHomotopy.cohomologyMap_eq x,
      fun y ↦ by simpa [AInfinityHom.cohomologyMap_comp, AInfinityHom.cohomologyMap_id] using
        DFunLike.congr_fun e.rightHomotopy.cohomologyMap_eq y⟩

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
theorem isHomotopyEquiv_def (f : AInfinityHom AA BB) : f.IsHomotopyEquiv ↔ ∃ g : AInfinityHom BB AA,
    (g.comp f).Homotopic (AInfinityHom.id AA) ∧ (f.comp g).Homotopic (AInfinityHom.id BB) := Iff.rfl
theorem _root_.TauCeti.AInfinityHomotopyEquiv.isHomotopyEquiv_toHom
    (e : AInfinityHomotopyEquiv AA BB) : e.toHom.IsHomotopyEquiv :=
  ⟨e.invHom, e.leftHomotopy.homotopic, e.rightHomotopy.homotopic⟩
theorem _root_.TauCeti.AInfinityHomotopyEquiv.isHomotopyEquiv_invHom
    (e : AInfinityHomotopyEquiv AA BB) : e.invHom.IsHomotopyEquiv := e.symm.isHomotopyEquiv_toHom

/-- `f` is a homotopy equivalence iff `f` is `e.toHom` for some `AInfinityHomotopyEquiv`. -/
theorem isHomotopyEquiv_iff_exists_homotopyEquiv (f : AInfinityHom AA BB) :
    f.IsHomotopyEquiv ↔ ∃ e : AInfinityHomotopyEquiv AA BB, e.toHom = f :=
  ⟨fun ⟨g, hL, hR⟩ ↦ let ⟨HL⟩ := (homotopic_def _ _).1 hL; let ⟨HR⟩ := (homotopic_def _ _).1 hR
    ⟨⟨f, g, HL, HR⟩, rfl⟩, fun ⟨e, h⟩ ↦ h ▸ e.isHomotopyEquiv_toHom⟩

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

/-- Between minimal `A∞` algebras, homotopy equivalences coincide with `A∞` isomorphisms. -/
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
    (f : AInfinityHom AA BB) (hA : A →ₗ[R] A) (hB : B →ₗ[R] B) (Φ : W →ₗ[R] A) (Ψ : W →ₗ[R] B) :
    W →ₗ[R] B := Ψ - (f.linearPart ∘ₗ hA - hB ∘ₗ f.linearPart) ∘ₗ Φ
private noncomputable def coneLiftG {W : Type*} [AddCommGroup W] [Module R W]
    (f : AInfinityHom AA BB) (g₀ : B →ₗ[R] A) (hA : A →ₗ[R] A) (hB : B →ₗ[R] B)
    (Φ : W →ₗ[R] A) (Ψ : W →ₗ[R] B) : W →ₗ[R] A := hA ∘ₗ Φ + g₀ ∘ₗ coneDiff f hA hB Φ Ψ
private noncomputable def coneLiftH {W : Type*} [AddCommGroup W] [Module R W]
    (f : AInfinityHom AA BB) (hA : A →ₗ[R] A) (hB : B →ₗ[R] B) (Φ : W →ₗ[R] A) (Ψ : W →ₗ[R] B) :
    W →ₗ[R] B := hB ∘ₗ coneDiff f hA hB Φ Ψ
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
  have hf_d (a) : BB.differential (f.linearPart a) = f.linearPart (AA.differential a) := by
    rw [BB.differential_apply, AA.differential_apply, f.linearPart_m_one]
  have hg_d (b) : AA.differential (g₀ b) = g₀ (BB.differential b) :=
    LinearMap.congr_fun hi.hg₀_diff b
  have hhA' (a) : AA.differential (hA a) = a - g₀ (f.linearPart a) - hA (AA.differential a) := by
    simpa using eq_sub_of_add_eq (LinearMap.congr_fun hi.hhA_eq a).symm
  have hhB' (b) : BB.differential (hB b) = b - f.linearPart (g₀ b) - hB (BB.differential b) := by
    simpa using eq_sub_of_add_eq (LinearMap.congr_fun hi.hhB_eq b).symm
  set Δh : A →ₗ[R] B := f.linearPart ∘ₗ hA - hB ∘ₗ f.linearPart with hΔh_def
  have hΔh (a) : BB.differential (Δh a) + Δh (AA.differential a) = 0 := by
    simp only [hΔh_def, LinearMap.sub_apply, LinearMap.comp_apply, map_sub, hf_d, hhA', hhB']; abel
  have hΦ' : Φ (dW w) = -AA.differential (Φ w) := eq_neg_of_add_eq_zero_right hΦ
  set Ψ' := coneDiff f hA hB Φ Ψ with hΨ'_def
  have hΨ' : Ψ' (dW w) = BB.differential (Ψ' w) - f.linearPart (Φ w) := by
    have eΔ := eq_neg_of_add_eq_zero_left (hΔh (Φ w))
    have eΨ : Ψ (dW w) = BB.differential (Ψ w) - f.linearPart (Φ w) := by rw [← hΨ]; abel
    simp only [hΨ'_def, coneDiff, ← hΔh_def, LinearMap.sub_apply, LinearMap.comp_apply,
      map_sub, hΦ', map_neg, eΔ, eΨ]; abel
  refine ⟨?_, ?_⟩
  · rw [coneLiftG, ← hΨ'_def]
    simp only [LinearMap.add_apply, LinearMap.comp_apply, map_add, hg_d, hΦ', hΨ', map_neg,
      map_sub, hhA']; abel
  · rw [coneLiftG, coneLiftH, ← hΨ'_def]
    simp only [LinearMap.add_apply, LinearMap.comp_apply, map_add, hhB', hΨ']
    simp only [hΨ'_def, coneDiff, LinearMap.sub_apply, LinearMap.comp_apply, map_sub]; abel
private noncomputable def morphError (AA : AInfinityAlgebra R A) (BB : AInfinityAlgebra R B)
    (γ : Words R B →ₗ[R] A) : Words R B →ₗ[R] Words R A :=
  AA.barDifferential ∘ₗ coalgHom R γ - coalgHom R γ ∘ₗ BB.barDifferential
private noncomputable abbrev candHomotopy (f : AInfinityHom AA BB) (γ : Words R B →ₗ[R] A)
    (η : Words R B →ₗ[R] B) : Words R B →ₗ[R] Words R B :=
  gradedCoderivAlong (BG BB) 1 LinearMap.id (f.barMap ∘ₗ coalgHom R γ) η
private noncomputable def homotopyError (f : AInfinityHom AA BB) (γ : Words R B →ₗ[R] A)
    (η : Words R B →ₗ[R] B) : Words R B →ₗ[R] Words R B :=
  let H := candHomotopy f γ η
  LinearMap.id - f.barMap ∘ₗ coalgHom R γ - (BB.barDifferential ∘ₗ H + H ∘ₗ BB.barDifferential)

/-- Two coalgebra morphisms agree on `filtration R B n` whenever their Taylor maps agree there. -/
private theorem coalgHom_congr_of_mem_filtration {γ₁ γ₂ : Words R B →ₗ[R] A} {n : ℕ}
    (hγ : ∀ w ∈ filtration R B n, γ₁ w = γ₂ w) {z : Words R B} (hz : z ∈ filtration R B n) :
    coalgHom R γ₁ z = coalgHom R γ₂ z :=
  (isCoalgHom_coalgHom γ₁).apply_eq_of_mem_filtration (isCoalgHom_coalgHom γ₂)
    (fun w hw ↦ by simpa [← LinearMap.comp_apply (letter R A)] using hγ w hw) hz

/-- Two candidate bar homotopies agree on `filtration R B n` when `γ₁ = γ₂` on strictly shorter
words and `η₁ = η₂` on `filtration R B n`. -/
private theorem candHomotopy_congr_of_mem_filtration (f : AInfinityHom AA BB)
    {γ₁ γ₂ : Words R B →ₗ[R] A} {η₁ η₂ : Words R B →ₗ[R] B} {n : ℕ}
    (hγ : ∀ k < n, ∀ w ∈ filtration R B k, γ₁ w = γ₂ w)
    (hη : ∀ w ∈ filtration R B n, η₁ w = η₂ w) {z : Words R B} (hz : z ∈ filtration R B n) :
    candHomotopy f γ₁ η₁ z = candHomotopy f γ₂ η₂ z :=
  (isGradedCoderivationAlong_gradedCoderivAlong (G := BG BB) 1 (isCoalgHom_id B)
    (f.isCoalgHom_barMap.comp (isCoalgHom_coalgHom γ₁)) η₁).apply_eq_of_mem_filtration
    (isGradedCoderivationAlong_gradedCoderivAlong (G := BG BB) 1 (isCoalgHom_id B)
      (f.isCoalgHom_barMap.comp (isCoalgHom_coalgHom γ₂)) η₂) (fun _ _ _ _ ↦ rfl)
    (fun k hk _ hw ↦ congrArg f.barMap (coalgHom_congr_of_mem_filtration (hγ k hk) hw))
    (fun w hw ↦ by simpa [← LinearMap.comp_apply (letter R B)] using hη w hw) hz
private theorem coalgHom_add_apply_of_mem_filtration_succ {γ δg : Words R B →ₗ[R] A} {n : ℕ}
    (hδg : ∀ u ∈ filtration R B n, δg u = 0) {z : Words R B} (hz : z ∈ filtration R B (n + 1)) :
    coalgHom R (γ + δg) z = coalgHom R γ z + ofLetter R A (δg z) := by
  have hγeq : ∀ u ∈ filtration R B n, (γ + δg) u = γ u := fun u hu ↦ by simp [hδg u hu]
  have eq1 := LinearMap.congr_fun (isCoalgHom_coalgHom (γ + δg)).eq_ofLetter_add_cutPrepend z
  have eq2 := LinearMap.congr_fun (isCoalgHom_coalgHom γ).eq_ofLetter_add_cutPrepend z
  simp only [letter_comp_coalgHom, LinearMap.add_apply, LinearMap.comp_apply, map_add] at eq1 eq2
  rw [eq1, eq2, cutPrepend_congr_of_mem_filtration_succ hγeq
    (fun _ hu ↦ coalgHom_congr_of_mem_filtration hγeq hu) hz]; abel
private theorem candHomotopy_add_apply_of_mem_filtration_succ (f : AInfinityHom AA BB)
    {γ δg : Words R B →ₗ[R] A} {η δh : Words R B →ₗ[R] B} {n : ℕ}
    (hδg : ∀ u ∈ filtration R B n, δg u = 0) (hδh : ∀ u ∈ filtration R B n, δh u = 0)
    {z : Words R B} (hz : z ∈ filtration R B (n + 1)) :
    candHomotopy f (γ + δg) (η + δh) z = candHomotopy f γ η z + ofLetter R B (δh z) := by
  have hγeq : ∀ u ∈ filtration R B n, (γ + δg) u = γ u := fun u hu ↦ by simp [hδg u hu]
  have hηeq : ∀ u ∈ filtration R B n, (η + δh) u = η u := fun u hu ↦ by simp [hδh u hu]
  have hFeq : ∀ u ∈ filtration R B n,
      (f.barMap ∘ₗ coalgHom R (γ + δg)) u = (f.barMap ∘ₗ coalgHom R γ) u :=
    fun _ hu ↦ congrArg f.barMap (coalgHom_congr_of_mem_filtration hγeq hu)
  have eq1 := LinearMap.congr_fun (gradedCoderivAlong_eq (BG BB) 1 LinearMap.id
    (f.barMap ∘ₗ coalgHom R (γ + δg)) (η + δh)) z
  have eq2 := LinearMap.congr_fun (gradedCoderivAlong_eq (BG BB) 1 LinearMap.id
    (f.barMap ∘ₗ coalgHom R γ) η) z
  simp only [LinearMap.add_apply] at eq1 eq2
  rw [candHomotopy, eq1, eq2, LinearMap.comp_apply, LinearMap.comp_apply, LinearMap.add_apply,
    map_add, cutPrepend_congr_of_mem_filtration_succ hηeq hFeq hz,
    cutPrepend_congr_of_mem_filtration_succ (fun _ _ ↦ rfl) (fun _ hu ↦
      candHomotopy_congr_of_mem_filtration f
        (fun _ hk _ hw ↦ hγeq _ (filtration_monotone R B hk.le hw)) hηeq hu) hz]; abel
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
  | tmul u v => simp [TensorProduct.mapIncl, hEG _ u.2, hEG _ v.2]
  | add _ _ hu hv => simp only [map_add] at hu hv ⊢; rw [add_add_add_comm, hu, hv, add_zero]
private theorem isHomogeneous_candHomotopy (f : AInfinityHom AA BB) {γ : Words R B →ₗ[R] A}
    {η : Words R B →ₗ[R] B} (hγ : LinearMap.IsHomogeneous γ (BW BB) (AP AA) 0)
    (hη : LinearMap.IsHomogeneous η (BW BB) (BP BB) (-1)) :
    LinearMap.IsHomogeneous (candHomotopy f γ η) (BW BB) (BW BB) (-1) :=
  isHomogeneous_gradedCoderivAlong (q := 1) (LinearMap.isHomogeneous_id _)
    (by simpa using f.isHomogeneous_barMap.comp (isHomogeneous_coalgHom hγ)) hη
private theorem homotopyError_eq_ofLetter (f : AInfinityHom AA BB) {γ : Words R B →ₗ[R] A}
    {η : Words R B →ₗ[R] B} (hγ : LinearMap.IsHomogeneous γ (BW BB) (AP AA) 0)
    (hη : LinearMap.IsHomogeneous η (BW BB) (BP BB) (-1)) {n : ℕ}
    (hEG : ∀ u ∈ filtration R B n, morphError AA BB γ u = 0)
    (hEH : ∀ u ∈ filtration R B n, homotopyError f γ η u = 0) {z : Words R B}
    (hz : z ∈ filtration R B (n + 1)) :
    homotopyError f γ η z = ofLetter R B (letter R B (homotopyError f γ η z)) := by
  set G := coalgHom R γ with hG_def
  set H := gradedCoderivAlong (BG BB) 1 LinearMap.id (f.barMap ∘ₗ G) η with hH_def
  set bB := BB.barDifferential with hbB_def; set τB := map R ((BG BB).koszulTwist 1) with hτB_def
  have hFG : IsCoalgHom R (f.barMap ∘ₗ G) := f.isCoalgHom_barMap.comp (isCoalgHom_coalgHom γ)
  have hH := isGradedCoderivationAlong_gradedCoderivAlong (G := BG BB) 1 (isCoalgHom_id B) hFG η
  have hH₁ : LinearMap.IsHomogeneous H (BW BB) (BW BB) (-1) := isHomogeneous_candHomotopy f hγ hη
  have hτH (w) : τB (H w) = -H (τB w) := by
    simpa [show ((1 : ℤ) * -1).negOnePow = -1 by decide, ← hτB_def] using
      LinearMap.congr_fun (hH₁.map_koszulTwist_comp 1) w
  have hτb (w) : τB (bB w) = -bB (τB w) := by
    simpa [show ((1 : ℤ) * 1).negOnePow = -1 by decide, ← hτB_def, ← hbB_def] using
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
      have eu : bB (H u.1) = u.1 - f.barMap (G u.1) - H (bB u.1) := by
        simpa [heh_def] using eq_sub_of_add_eq (sub_eq_zero.1 (hEH u.1 u.2)).symm
      have ev : bB (H v.1) = v.1 - f.barMap (G v.1) - H (bB v.1) := by
        simpa [heh_def] using eq_sub_of_add_eq (sub_eq_zero.1 (hEH v.1 v.2)).symm
      simp only [TensorProduct.mapIncl, TensorProduct.map_tmul, Submodule.coe_subtype, map_add,
        LinearMap.rTensor_tmul, LinearMap.lTensor_tmul, LinearMap.sub_apply, LinearMap.id_apply,
        LinearMap.comp_apply]
      simp only [hτH, hτb, hττ, hFGb v.1 v.2, eu, ev, TensorProduct.neg_tmul,
        TensorProduct.sub_tmul, TensorProduct.tmul_sub]; abel
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

/-- Single obstruction-correction step: given candidate Taylor maps `(γ, η)`, add the mapping-cone
coboundary lift killing their letter-level morphism and homotopy obstructions. -/
private noncomputable def liftPairStep (f : AInfinityHom AA BB) (g₀ : B →ₗ[R] A) (hA : A →ₗ[R] A)
    (hB : B →ₗ[R] B) (p : (Words R B →ₗ[R] A) × (Words R B →ₗ[R] B)) :
    (Words R B →ₗ[R] A) × (Words R B →ₗ[R] B) :=
  let Φ := -(letter R A ∘ₗ morphError AA BB p.1); let Ψ := letter R B ∘ₗ homotopyError f p.1 p.2
  (p.1 + coneLiftG f g₀ hA hB Φ Ψ, p.2 + coneLiftH f hA hB Φ Ψ)
private theorem liftPairStep_eq_of_errors_zero {f : AInfinityHom AA BB} {g₀ : B →ₗ[R] A}
    {hA : A →ₗ[R] A} {hB : B →ₗ[R] B} {p : (Words R B →ₗ[R] A) × (Words R B →ₗ[R] B)}
    {z : Words R B} (hEG : morphError AA BB p.1 z = 0) (hEH : homotopyError f p.1 p.2 z = 0) :
    (liftPairStep f g₀ hA hB p).1 z = p.1 z ∧ (liftPairStep f g₀ hA hB p).2 z = p.2 z := by
  simp [liftPairStep, coneLiftG, coneLiftH, coneDiff, hEG, hEH]

/-- `liftPairStep` preserves shifted total degrees `(0, -1)` of the candidate Taylor pair. -/
private theorem isHomogeneous_liftPairStep {f : AInfinityHom AA BB} {g₀ : B →ₗ[R] A}
    {hA : A →ₗ[R] A} {hB : B →ₗ[R] B} (hi : LinInv f g₀ hA hB)
    {p : (Words R B →ₗ[R] A) × (Words R B →ₗ[R] B)}
    (hγ : LinearMap.IsHomogeneous p.1 (BW BB) (AP AA) 0)
    (hη : LinearMap.IsHomogeneous p.2 (BW BB) (BP BB) (-1)) :
    LinearMap.IsHomogeneous (liftPairStep f g₀ hA hB p).1 (BW BB) (AP AA) 0 ∧
      LinearMap.IsHomogeneous (liftPairStep f g₀ hA hB p).2 (BW BB) (BP BB) (-1) := by
  have hG₀ := isHomogeneous_coalgHom hγ
  have hEG₁ : LinearMap.IsHomogeneous (morphError AA BB p.1) (BW BB) (BW AA) 1 :=
    LinearMap.IsHomogeneous.sub (by simpa using AA.isHomogeneous_barDifferential.comp hG₀)
      (by simpa using hG₀.comp BB.isHomogeneous_barDifferential)
  have hH₁ := isHomogeneous_candHomotopy f hγ hη
  have hEH₀ : LinearMap.IsHomogeneous (homotopyError f p.1 p.2) (BW BB) (BW BB) 0 :=
    ((LinearMap.isHomogeneous_id _).sub (by simpa using f.isHomogeneous_barMap.comp hG₀)).sub
      (LinearMap.IsHomogeneous.add (by simpa using BB.isHomogeneous_barDifferential.comp hH₁)
        (by simpa using hH₁.comp BB.isHomogeneous_barDifferential))
  obtain ⟨hdG, hdH⟩ := isHomogeneous_coneLift hi
    (LinearMap.IsHomogeneous.neg (by simpa using (isHomogeneous_letter _).comp hEG₁))
    (by simpa using (isHomogeneous_letter _).comp hEH₀)
  exact ⟨hγ.add hdG, hη.add hdH⟩

/-- Obstruction-correction lemma: if `(p.1, p.2)` has vanishing morphism and homotopy errors on
`filtration R B m`, then `liftPairStep f g₀ hA hB p` kills both errors on
`filtration R B (m + 1)`. -/
private theorem liftPairStep_errors_eq_zero {f : AInfinityHom AA BB} {g₀ : B →ₗ[R] A}
    {hA : A →ₗ[R] A} {hB : B →ₗ[R] B} (hi : LinInv f g₀ hA hB)
    {p : (Words R B →ₗ[R] A) × (Words R B →ₗ[R] B)}
    (hγ : LinearMap.IsHomogeneous p.1 (BW BB) (AP AA) 0)
    (hη : LinearMap.IsHomogeneous p.2 (BW BB) (BP BB) (-1)) {m : ℕ}
    (hEG : ∀ u ∈ filtration R B m, morphError AA BB p.1 u = 0)
    (hEH : ∀ u ∈ filtration R B m, homotopyError f p.1 p.2 u = 0)
    {z : Words R B} (hz : z ∈ filtration R B (m + 1)) :
    morphError AA BB (liftPairStep f g₀ hA hB p).1 z = 0 ∧
      homotopyError f (liftPairStep f g₀ hA hB p).1 (liftPairStep f g₀ hA hB p).2 z = 0 := by
  set Φ := -(letter R A ∘ₗ morphError AA BB p.1); set Ψ := letter R B ∘ₗ homotopyError f p.1 p.2
  set δg := coneLiftG f g₀ hA hB Φ Ψ; set δh := coneLiftH f hA hB Φ Ψ
  -- Both corrections vanish on `filtration R B m`, so `coalgHom` and `candHomotopy` change on
  -- `filtration R B (m + 1)` only by the primitive `ofLetter` terms of `δg` and `δh`.
  have hδg0 : ∀ u ∈ filtration R B m, δg u = 0 := fun u hu ↦ by
    simp [δg, coneLiftG, coneDiff, Φ, Ψ, hEG u hu, hEH u hu]
  have hδh0 : ∀ u ∈ filtration R B m, δh u = 0 := fun u hu ↦ by
    simp [δh, coneLiftH, coneDiff, Φ, Ψ, hEG u hu, hEH u hu]
  have hbz := BB.barDifferential_mem_filtration hz
  -- On `filtration R B (m + 1)`, the errors are primitive mapping-cone cocycles, and `(δg, δh)`
  -- solves the coboundary equations cancelling them.
  obtain ⟨hcG, hcH⟩ := cocycle_of_errors_zero f hγ hη hEG hEH hz
  obtain ⟨heqG, heqH⟩ := coneLift_coboundary hi (dW := BB.barDifferential)
    (Φ := Φ) (Ψ := Ψ) hcG hcH
  refine ⟨?_, ?_⟩
  · change morphError AA BB (p.1 + δg) z = 0
    rw [morphError, LinearMap.sub_apply, LinearMap.comp_apply, LinearMap.comp_apply,
      coalgHom_add_apply_of_mem_filtration_succ hδg0 hz,
      coalgHom_add_apply_of_mem_filtration_succ hδg0 hbz, map_add,
      AInfinityAlgebra.barDifferential_ofLetter, ← AA.differential_apply]
    calc _ = morphError AA BB p.1 z +
          ofLetter R A (AA.differential (δg z) - δg (BB.barDifferential z)) := by
          rw [morphError, LinearMap.sub_apply, LinearMap.comp_apply, LinearMap.comp_apply, map_sub]
          abel
      _ = 0 := by rw [morphError_eq_ofLetter hγ hEG hz, heqG]; simp [Φ]
  · change homotopyError f (p.1 + δg) (p.2 + δh) z = 0
    rw [homotopyError, LinearMap.sub_apply, LinearMap.sub_apply, LinearMap.id_apply,
      LinearMap.comp_apply, LinearMap.add_apply, LinearMap.comp_apply, LinearMap.comp_apply,
      coalgHom_add_apply_of_mem_filtration_succ hδg0 hz,
      candHomotopy_add_apply_of_mem_filtration_succ f hδg0 hδh0 hz,
      candHomotopy_add_apply_of_mem_filtration_succ f hδg0 hδh0 hbz,
      map_add, map_add, f.barMap_ofLetter, AInfinityAlgebra.barDifferential_ofLetter,
      ← BB.differential_apply]
    calc _ = homotopyError f p.1 p.2 z - ofLetter R B (f.linearPart (δg z) +
          BB.differential (δh z) + δh (BB.barDifferential z)) := by
          rw [homotopyError, LinearMap.sub_apply, LinearMap.sub_apply, LinearMap.id_apply,
            LinearMap.comp_apply, LinearMap.add_apply, LinearMap.comp_apply,
            LinearMap.comp_apply, map_add, map_add]; abel
      _ = 0 := by rw [homotopyError_eq_ofLetter f hγ hη hEG hEH hz, heqH]; simp [Ψ]
private noncomputable def liftPairSeq (f : AInfinityHom AA BB) (g₀ : B →ₗ[R] A) (hA : A →ₗ[R] A)
    (hB : B →ₗ[R] B) : ℕ → (Words R B →ₗ[R] A) × (Words R B →ₗ[R] B)
  | 0 => (g₀ ∘ₗ letter R B, hB ∘ₗ letter R B)
  | n + 1 => liftPairStep f g₀ hA hB (liftPairSeq f g₀ hA hB n)

/-- Stage `n` of `liftPairSeq` is homogeneous of shifted degrees `(0, -1)` and has vanishing
morphism and homotopy errors on words of length at most `n + 1`. -/
private theorem liftPairSeq_invariant {f : AInfinityHom AA BB} {g₀ : B →ₗ[R] A}
    {hA : A →ₗ[R] A} {hB : B →ₗ[R] B} (hi : LinInv f g₀ hA hB) (n : ℕ) :
    LinearMap.IsHomogeneous (liftPairSeq f g₀ hA hB n).1 (BW BB) (AP AA) 0 ∧
      LinearMap.IsHomogeneous (liftPairSeq f g₀ hA hB n).2 (BW BB) (BP BB) (-1) ∧
      (∀ z ∈ filtration R B (n + 1), morphError AA BB (liftPairSeq f g₀ hA hB n).1 z = 0) ∧
      (∀ z ∈ filtration R B (n + 1),
        homotopyError f (liftPairSeq f g₀ hA hB n).1 (liftPairSeq f g₀ hA hB n).2 z = 0) := by
  induction n with
  | zero =>
      -- At stage 0, `(g₀ ∘ π, hB ∘ π)` satisfies the morphism and homotopy equations on single
      -- letters `filtration R B 1` directly from the chain-map and chain-homotopy hypotheses.
      refine ⟨by simpa [liftPairSeq] using ((LinearMap.isHomogeneous_shift_piece_iff (c := 1)).2
          hi.hg₀).comp (isHomogeneous_letter _),
        by simpa [liftPairSeq] using ((LinearMap.isHomogeneous_shift_piece_iff (c := 1)).2
          hi.hhB).comp (isHomogeneous_letter _),
        apply_eq_zero_of_mem_filtration_one R B (LinearMap.ext fun b ↦ ?_),
        apply_eq_zero_of_mem_filtration_one R B (LinearMap.ext fun b ↦ ?_)⟩
      · have hg := LinearMap.congr_fun hi.hg₀_diff b
        simp only [LinearMap.comp_apply] at hg
        simp only [liftPairSeq, morphError, LinearMap.comp_apply, LinearMap.sub_apply,
          LinearMap.zero_apply, coalgHom_ofLetter, letter_ofLetter,
          AInfinityAlgebra.barDifferential_ofLetter, ← AA.differential_apply,
          ← BB.differential_apply, hg, sub_self]
      · have hb := LinearMap.congr_fun hi.hhB_eq b
        simp only [LinearMap.sub_apply, LinearMap.id_apply, LinearMap.comp_apply,
          LinearMap.add_apply] at hb
        simp only [liftPairSeq, homotopyError, candHomotopy, LinearMap.comp_apply,
          LinearMap.sub_apply, LinearMap.add_apply, LinearMap.id_apply, LinearMap.zero_apply,
          coalgHom_ofLetter, letter_ofLetter, f.barMap_ofLetter,
          AInfinityAlgebra.barDifferential_ofLetter, gradedCoderivAlong_ofLetter,
          ← BB.differential_apply, ← map_add, ← hb, map_sub, sub_self]
  | succ n ih =>
      -- At stage `n + 1`, `liftPairStep` preserves degrees and extends vanishing of both errors
      -- from `filtration R B (n + 1)` to `filtration R B (n + 2)`.
      obtain ⟨hγ, hη, hEG, hEH⟩ := ih; obtain ⟨hdG, hdH⟩ := isHomogeneous_liftPairStep hi hγ hη
      exact ⟨hdG, hdH, fun _ hz ↦ (liftPairStep_errors_eq_zero hi hγ hη hEG hEH hz).1,
        fun _ hz ↦ (liftPairStep_errors_eq_zero hi hγ hη hEG hEH hz).2⟩

/-- Because the stage-`n` errors already vanish on `filtration R B (n + 1)`, stage `n + 1` of
`liftPairSeq` agrees with stage `n` on `filtration R B (n + 1)`. -/
private theorem liftPairSeq_stabilises {f : AInfinityHom AA BB} {g₀ : B →ₗ[R] A}
    {hA : A →ₗ[R] A} {hB : B →ₗ[R] B} (hi : LinInv f g₀ hA hB) (n : ℕ)
    {z : Words R B} (hz : z ∈ filtration R B (n + 1)) :
    (liftPairSeq f g₀ hA hB (n + 1)).1 z = (liftPairSeq f g₀ hA hB n).1 z ∧
      (liftPairSeq f g₀ hA hB (n + 1)).2 z = (liftPairSeq f g₀ hA hB n).2 z :=
  liftPairStep_eq_of_errors_zero ((liftPairSeq_invariant hi n).2.2.1 z hz)
    ((liftPairSeq_invariant hi n).2.2.2 z hz)

/-- Passage to the filtration limit for the morphism Taylor equation: if `γSeq` stabilises on the
conilpotence filtration and `morphError AA BB (γSeq n)` vanishes on `filtration R B (n + 1)`, then
`filtrationLimit γSeq` satisfies the `A∞` morphism component identity. -/
private theorem taylor_eq_of_filtrationLimit {γSeq : ℕ → Words R B →ₗ[R] A}
    (hγ_stab : ∀ n, ∀ z ∈ filtration R B n, γSeq (n + 1) z = γSeq n z)
    (hEG : ∀ n, ∀ z ∈ filtration R B (n + 1), morphError AA BB (γSeq n) z = 0) :
    AA.taylor ∘ₗ coalgHom R (filtrationLimit γSeq) =
      filtrationLimit γSeq ∘ₗ BB.barDifferential := by
  refine LinearMap.ext fun z ↦ ?_; obtain ⟨n, hn⟩ := exists_mem_filtration R B z
  have h0 := congrArg (letter R A) (hEG n z (filtration_monotone R B n.le_succ hn))
  rw [morphError, LinearMap.sub_apply, LinearMap.comp_apply, LinearMap.comp_apply, map_sub,
    map_zero, sub_eq_zero, ← LinearMap.comp_apply (letter R A) AA.barDifferential,
    AA.letter_comp_barDifferential, ← LinearMap.comp_apply (letter R A) (coalgHom R _),
    letter_comp_coalgHom] at h0
  rw [LinearMap.comp_apply, LinearMap.comp_apply,
    coalgHom_congr_of_mem_filtration
      (fun _ hw ↦ filtrationLimit_apply_of_mem_filtration hγ_stab hw) hn, h0,
    filtrationLimit_apply_of_mem_filtration hγ_stab (BB.barDifferential_mem_filtration hn)]

/-- Passage to the filtration limit for the homotopy Taylor equation: if `γSeq` and `ηSeq`
stabilise and `homotopyError f (γSeq n) (ηSeq n)` vanishes on `filtration R B (n + 1)`, then
`filtrationLimit ηSeq` satisfies the `A∞` homotopy component identity between `id BB` and
`f ∘ g`. -/
private theorem homotopy_taylor_eq_of_filtrationLimit (f : AInfinityHom AA BB)
    {g : AInfinityHom BB AA} {γSeq : ℕ → Words R B →ₗ[R] A} {ηSeq : ℕ → Words R B →ₗ[R] B}
    (hγ_stab : ∀ n, ∀ z ∈ filtration R B n, γSeq (n + 1) z = γSeq n z)
    (hη_stab : ∀ n, ∀ z ∈ filtration R B n, ηSeq (n + 1) z = ηSeq n z)
    (hg_bar : g.barMap = coalgHom R (filtrationLimit γSeq))
    (hEH : ∀ n, ∀ z ∈ filtration R B (n + 1), homotopyError f (γSeq n) (ηSeq n) z = 0) :
    (AInfinityHom.id BB).taylor - (f.comp g).taylor =
      BB.taylor ∘ₗ gradedCoderivAlong (BG BB) 1 (AInfinityHom.id BB).barMap (f.comp g).barMap
          (filtrationLimit ηSeq) +
        filtrationLimit ηSeq ∘ₗ BB.barDifferential := by
  refine LinearMap.ext fun z ↦ ?_; obtain ⟨n, hn⟩ := exists_mem_filtration R B z
  have h0 := congrArg (letter R B) (hEH n z (filtration_monotone R B n.le_succ hn))
  rw [homotopyError, LinearMap.sub_apply, LinearMap.sub_apply, LinearMap.id_apply,
    LinearMap.comp_apply, LinearMap.add_apply, LinearMap.comp_apply, LinearMap.comp_apply,
    map_sub, map_sub, map_add, map_zero, sub_eq_zero,
    ← LinearMap.comp_apply (letter R B) f.barMap, ← f.taylor_def,
    ← LinearMap.comp_apply (letter R B) BB.barDifferential, BB.letter_comp_barDifferential,
    ← LinearMap.comp_apply (letter R B) (candHomotopy ..), letter_comp_gradedCoderivAlong] at h0
  simp only [AInfinityHom.taylor_id, AInfinityHom.taylor_comp, AInfinityHom.barMap_id,
    AInfinityHom.barMap_comp, LinearMap.sub_apply, LinearMap.add_apply, LinearMap.comp_apply,
    hg_bar]
  rwa [candHomotopy_congr_of_mem_filtration f
      (fun _ hk _ hw ↦ filtrationLimit_apply_of_mem_filtration hγ_stab
        (filtration_monotone R B hk.le hw))
      (fun _ hw ↦ filtrationLimit_apply_of_mem_filtration hη_stab hw) hn,
    coalgHom_congr_of_mem_filtration
      (fun _ hw ↦ filtrationLimit_apply_of_mem_filtration hγ_stab hw) hn,
    filtrationLimit_apply_of_mem_filtration hη_stab (BB.barDifferential_mem_filtration hn)]

private noncomputable def rightHomotopyInverse (f : AInfinityHom AA BB)
    (g₀ : B →ₗ[R] A) (hA : A →ₗ[R] A) (hB : B →ₗ[R] B) (hi : LinInv f g₀ hA hB) :
    Σ' g : AInfinityHom BB AA, g.linearPart = g₀ ∧
      Nonempty (AInfinityHom.Homotopy (f.comp g) (AInfinityHom.id BB)) := by
  -- Pass the stabilising stage-by-stage lifts `(γSeq, ηSeq)` to their filtration limits `(γ, η)`.
  have hinv := liftPairSeq_invariant hi
  let γSeq := fun n ↦ (liftPairSeq f g₀ hA hB n).1; let ηSeq := fun n ↦ (liftPairSeq f g₀ hA hB n).2
  have hγ_stab : ∀ n, ∀ z ∈ filtration R B n, γSeq (n + 1) z = γSeq n z :=
    fun n _ hz ↦ (liftPairSeq_stabilises hi n (filtration_monotone R B n.le_succ hz)).1
  have hη_stab : ∀ n, ∀ z ∈ filtration R B n, ηSeq (n + 1) z = ηSeq n z :=
    fun n _ hz ↦ (liftPairSeq_stabilises hi n (filtration_monotone R B n.le_succ hz)).2
  let γ := filtrationLimit γSeq; let η := filtrationLimit ηSeq
  have hγ_hom := isHomogeneous_filtrationLimit hγ_stab fun n ↦ (hinv n).1
  have hη_hom := isHomogeneous_filtrationLimit hη_stab fun n ↦ (hinv n).2.1
  -- Assemble the `A∞` morphism `g` from `γ`; on letters it agrees with stage `0`, hence `g₀`.
  have hγ_eq := taylor_eq_of_filtrationLimit hγ_stab fun n ↦ (hinv n).2.2.1
  let g : AInfinityHom BB AA := AInfinityHom.ofTaylor γ hγ_hom hγ_eq
  have hg_lin : g.linearPart = g₀ := by
    ext b; have hb := ofLetter_mem_filtration R B b
    rw [AInfinityHom.linearPart_apply, AInfinityHom.taylor_ofTaylor,
      filtrationLimit_apply_of_mem_filtration hγ_stab hb, (liftPairSeq_stabilises hi 0 hb).1]
    simp [liftPairSeq]
  -- Assemble the homotopy `id BB ~ f ∘ g` from `η` and reverse it via `Homotopy.symm`.
  have hη_eq := homotopy_taylor_eq_of_filtrationLimit f hγ_stab hη_stab
    (AInfinityHom.barMap_ofTaylor γ hγ_hom hγ_eq) fun n ↦ (hinv n).2.2.2
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
    e.rightHomotopy.symm.linearHomotopy, e.invHom.isHomogeneous_linearPart, ?_,
    LinearMap.isHomogeneous_def.2 fun _ _ ↦ e.leftHomotopy.symm.linearHomotopy_mem, ?_,
    LinearMap.isHomogeneous_def.2 fun _ _ ↦ e.rightHomotopy.symm.linearHomotopy_mem, ?_⟩
  · ext; simp [AA.differential_apply, BB.differential_apply, e.invHom.linearPart_m_one]
  · ext a; simpa only [LinearMap.sub_apply, LinearMap.id_apply, LinearMap.comp_apply,
      LinearMap.add_apply, AInfinityHom.linearPart_id, AInfinityHom.linearPart_comp,
      AA.differential_apply] using e.leftHomotopy.symm.linearPart_sub_linearPart a
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
    AInfinityHomotopyEquiv 𝒜.minimalModel 𝒜 :=
  ⟨𝒜.minimalModelInclusion, 𝒜.minimalModelProjection,
    (AInfinityHom.Homotopy.refl _).copy 𝒜.minimalModelProjection_comp_minimalModelInclusion.symm
      rfl, 𝒜.minimalModelHomotopy.symm⟩

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
