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

An `A∞` morphism `f : A ⟶ B` is a *homotopy equivalence* (`TauCeti.AInfinityHom.IsHomotopyEquiv`)
when there exists an `A∞` morphism `g : B ⟶ A` such that `g ∘ f` is homotopic to `id_A` and `f ∘ g`
is homotopic to `id_B`; `TauCeti.AInfinityHomotopyEquiv` packages `f` and `g` together with explicit
left and right homotopies.

Over an arbitrary commutative ring `R`, an `A∞` morphism `f` is a homotopy equivalence if and only
if its linear part `f₁` admits a homogeneous chain-homotopy inverse between the underlying unary
complexes `(A, m₁)` and `(B, m₁)`
(`TauCeti.AInfinityHom.isHomotopyEquiv_iff_exists_linearHomotopyInverse`).  Given such a
chain-homotopy inverse `(g₀, h_A, h_B)`, `TauCeti.AInfinityHomotopyEquiv.ofLinearHomotopyInverse`
lifts `g₀` to a two-sided `A∞` homotopy inverse `g` with `g.linearPart = g₀`.

Over a field `K`, every `A∞` algebra is homotopy equivalent to its minimal model on cohomology
(`TauCeti.AInfinityAlgebra.minimalModelHomotopyEquiv`), and an `A∞` morphism is a homotopy
equivalence if and only if it is a quasi-isomorphism
(`TauCeti.AInfinityHom.isHomotopyEquiv_iff_isQuasiIso`): every `A∞` quasi-isomorphism over a field
admits an explicit two-sided `A∞` inverse up to homotopy
(`TauCeti.AInfinityHom.IsQuasiIso.homotopyEquiv`).

## Main definitions

* `TauCeti.AInfinityHomotopyEquiv`: an explicit homotopy equivalence between `A∞` algebras.
* `TauCeti.AInfinityHom.IsHomotopyEquiv`: the predicate that an `A∞` morphism has a two-sided
  inverse up to homotopy.
* `TauCeti.AInfinityHomotopyEquiv.ofLinearHomotopyInverse`: lifts a homogeneous chain-homotopy
  inverse of `f.linearPart` over any commutative ring to an `A∞` homotopy equivalence extending `f`.
* `TauCeti.AInfinityAlgebra.minimalModelHomotopyEquiv`: the homotopy equivalence between the
  minimal model on cohomology and the original `A∞` algebra over a field.
* `TauCeti.AInfinityHom.IsQuasiIso.homotopyEquiv`: a two-sided `A∞` homotopy equivalence extending
  any `A∞` quasi-isomorphism over a field.

## Main results

* `TauCeti.AInfinityHom.isHomotopyEquiv_iff_exists_linearHomotopyInverse`: over any commutative
  ring, an `A∞` morphism is a homotopy equivalence iff its linear part admits a homogeneous
  chain-homotopy inverse.
* `TauCeti.AInfinityHom.isHomotopyEquiv_iff_isQuasiIso`: over a field, an `A∞` morphism is a
  homotopy equivalence iff it is a quasi-isomorphism.
* `TauCeti.AInfinityHom.isHomotopyEquiv_iff_isIso`: between minimal `A∞` algebras over any
  commutative ring, homotopy equivalences coincide with strict `A∞` isomorphisms.

## References

* K. Lefèvre-Hasegawa, *Sur les A-infini catégories*, thèse de doctorat, Université Paris 7
  (2003), Theorem 1.3.1.2 and Appendix B.2.
* B. Keller, *Introduction to A-infinity algebras and modules*, Section 3.7.
* A. Prouté, *A-infinity structures: modèles minimaux de Baues--Lemaire et Kadeishvili et homologie
  des fibrations*, Reprints in Theory and Applications of Categories 21 (2011), Theorem 4.8.
-/

public section

open scoped TensorProduct

namespace TauCeti

universe uR uK uA uB uC

section CommRing

variable {R : Type uR} {A : Type uA} {B : Type uB} {C : Type uC} [CommRing R]
  [AddCommGroup A] [Module R A] [AddCommGroup B] [Module R B] [AddCommGroup C] [Module R C]

/-! ### Explicit homotopy equivalences of `A∞` algebras -/

/-- A **homotopy equivalence** between `A∞` algebras `AA` and `BB`: a pair of `A∞` morphisms
`toHom : AA ⟶ BB` and `invHom : BB ⟶ AA` equipped with homotopies from `invHom ∘ toHom` to
`id_AA` and from `toHom ∘ invHom` to `id_BB`. -/
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

variable {AA : AInfinityAlgebra R A} {BB : AInfinityAlgebra R B} {CC : AInfinityAlgebra R C}

/-- The identity homotopy equivalence of an `A∞` algebra. -/
def refl (AA : AInfinityAlgebra R A) : AInfinityHomotopyEquiv AA AA where
  toHom := AInfinityHom.id AA
  invHom := AInfinityHom.id AA
  leftHomotopy := (AInfinityHom.Homotopy.refl (AInfinityHom.id AA)).copy
    (AInfinityHom.comp_id _).symm rfl
  rightHomotopy := (AInfinityHom.Homotopy.refl (AInfinityHom.id AA)).copy
    (AInfinityHom.comp_id _).symm rfl

@[simp]
theorem toHom_refl (AA : AInfinityAlgebra R A) : (refl AA).toHom = AInfinityHom.id AA := (rfl)

@[simp]
theorem invHom_refl (AA : AInfinityAlgebra R A) : (refl AA).invHom = AInfinityHom.id AA := (rfl)

/-- The inverse homotopy equivalence, swapping forward and inverse morphisms. -/
def symm (e : AInfinityHomotopyEquiv AA BB) : AInfinityHomotopyEquiv BB AA where
  toHom := e.invHom
  invHom := e.toHom
  leftHomotopy := e.rightHomotopy
  rightHomotopy := e.leftHomotopy

@[simp]
theorem toHom_symm (e : AInfinityHomotopyEquiv AA BB) : e.symm.toHom = e.invHom := (rfl)

@[simp]
theorem invHom_symm (e : AInfinityHomotopyEquiv AA BB) : e.symm.invHom = e.toHom := (rfl)

@[simp]
theorem symm_symm (e : AInfinityHomotopyEquiv AA BB) : e.symm.symm = e := (rfl)

/-- Composition of homotopy equivalences of `A∞` algebras. -/
noncomputable def trans (e₁ : AInfinityHomotopyEquiv AA BB) (e₂ : AInfinityHomotopyEquiv BB CC) :
    AInfinityHomotopyEquiv AA CC where
  toHom := e₂.toHom.comp e₁.toHom
  invHom := e₁.invHom.comp e₂.invHom
  leftHomotopy :=
    (((e₂.leftHomotopy.compLeft e₁.toHom).compRight e₁.invHom).copy
      (by simp only [AInfinityHom.comp_assoc])
      (by rw [AInfinityHom.id_comp])).trans e₁.leftHomotopy
  rightHomotopy :=
    (((e₁.rightHomotopy.compLeft e₂.invHom).compRight e₂.toHom).copy
      (by simp only [AInfinityHom.comp_assoc])
      (by rw [AInfinityHom.id_comp])).trans e₂.rightHomotopy

@[simp]
theorem toHom_trans (e₁ : AInfinityHomotopyEquiv AA BB) (e₂ : AInfinityHomotopyEquiv BB CC) :
    (e₁.trans e₂).toHom = e₂.toHom.comp e₁.toHom := (rfl)

@[simp]
theorem invHom_trans (e₁ : AInfinityHomotopyEquiv AA BB) (e₂ : AInfinityHomotopyEquiv BB CC) :
    (e₁.trans e₂).invHom = e₁.invHom.comp e₂.invHom := (rfl)

/-- Replace the forward morphism of a homotopy equivalence by a homotopic morphism `f`, keeping the
same homotopy inverse. -/
noncomputable def replaceToHom (e : AInfinityHomotopyEquiv AA BB) {f : AInfinityHom AA BB}
    (hf : AInfinityHom.Homotopy f e.toHom) : AInfinityHomotopyEquiv AA BB where
  toHom := f
  invHom := e.invHom
  leftHomotopy := (hf.compRight e.invHom).trans e.leftHomotopy
  rightHomotopy := (hf.compLeft e.invHom).trans e.rightHomotopy

@[simp]
theorem toHom_replaceToHom (e : AInfinityHomotopyEquiv AA BB) {f : AInfinityHom AA BB}
    (hf : AInfinityHom.Homotopy f e.toHom) : (e.replaceToHom hf).toHom = f := (rfl)

@[simp]
theorem invHom_replaceToHom (e : AInfinityHomotopyEquiv AA BB) {f : AInfinityHom AA BB}
    (hf : AInfinityHom.Homotopy f e.toHom) : (e.replaceToHom hf).invHom = e.invHom := (rfl)

/-- An `A∞` morphism with bijective linear part yields a homotopy equivalence with zero homotopies,
whose inverse is `AInfinityHom.inverse`. -/
noncomputable def ofLinearPartBijective (f : AInfinityHom AA BB)
    (hf : Function.Bijective f.linearPart) : AInfinityHomotopyEquiv AA BB where
  toHom := f
  invHom := f.inverse hf
  leftHomotopy := (AInfinityHom.Homotopy.refl (AInfinityHom.id AA)).copy
    (f.inverse_comp_cancel hf).symm rfl
  rightHomotopy := (AInfinityHom.Homotopy.refl (AInfinityHom.id BB)).copy
    (f.comp_inverse_cancel hf).symm rfl

@[simp]
theorem toHom_ofLinearPartBijective (f : AInfinityHom AA BB)
    (hf : Function.Bijective f.linearPart) : (ofLinearPartBijective f hf).toHom = f := (rfl)

@[simp]
theorem invHom_ofLinearPartBijective (f : AInfinityHom AA BB)
    (hf : Function.Bijective f.linearPart) :
    (ofLinearPartBijective f hf).invHom = f.inverse hf := (rfl)

/-- If `g` is a right homotopy inverse of `f` and `f'` is a right homotopy inverse of `g`, then `g`
is a two-sided homotopy inverse of `f`. -/
noncomputable def ofRightHomotopyInverses {f f' : AInfinityHom AA BB} {g : AInfinityHom BB AA}
    (hfg : AInfinityHom.Homotopy (f.comp g) (AInfinityHom.id BB))
    (hgf' : AInfinityHom.Homotopy (g.comp f') (AInfinityHom.id AA)) :
    AInfinityHomotopyEquiv AA BB where
  toHom := f
  invHom := g
  leftHomotopy :=
    let hff' : AInfinityHom.Homotopy f f' :=
      ((hgf'.symm.compRight f).copy (AInfinityHom.comp_id f)
        (AInfinityHom.comp_assoc f g f').symm).trans
        ((hfg.compLeft f').copy rfl (AInfinityHom.id_comp f'))
    (hff'.compRight g).trans hgf'
  rightHomotopy := hfg

@[simp]
theorem toHom_ofRightHomotopyInverses {f f' : AInfinityHom AA BB} {g : AInfinityHom BB AA}
    (hfg : AInfinityHom.Homotopy (f.comp g) (AInfinityHom.id BB))
    (hgf' : AInfinityHom.Homotopy (g.comp f') (AInfinityHom.id AA)) :
    (ofRightHomotopyInverses hfg hgf').toHom = f := (rfl)

@[simp]
theorem invHom_ofRightHomotopyInverses {f f' : AInfinityHom AA BB} {g : AInfinityHom BB AA}
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

/-- The inverse morphism of a homotopy equivalence is a quasi-isomorphism. -/
theorem isQuasiIso_invHom (e : AInfinityHomotopyEquiv AA BB) : e.invHom.IsQuasiIso :=
  e.symm.isQuasiIso_toHom

end AInfinityHomotopyEquiv

/-! ### The homotopy-equivalence predicate on `A∞` morphisms -/

namespace AInfinityHom

variable {AA : AInfinityAlgebra R A} {BB : AInfinityAlgebra R B} {CC : AInfinityAlgebra R C}

/-- An `A∞` morphism `f : AA ⟶ BB` is a **homotopy equivalence** when it admits a two-sided
inverse up to homotopy. -/
def IsHomotopyEquiv (f : AInfinityHom AA BB) : Prop :=
  ∃ g : AInfinityHom BB AA,
    (g.comp f).Homotopic (AInfinityHom.id AA) ∧ (f.comp g).Homotopic (AInfinityHom.id BB)

-- The body of `IsHomotopyEquiv` is not exposed, so later modules can neither destructure an
-- `IsHomotopyEquiv` hypothesis nor build one by anonymous constructor; this restatement is their
-- access to it.
/-- An `A∞` morphism is a homotopy equivalence exactly when it has a two-sided homotopy inverse. -/
theorem isHomotopyEquiv_def (f : AInfinityHom AA BB) :
    f.IsHomotopyEquiv ↔ ∃ g : AInfinityHom BB AA,
      (g.comp f).Homotopic (AInfinityHom.id AA) ∧ (f.comp g).Homotopic (AInfinityHom.id BB) :=
  Iff.rfl

/-- An explicit `AInfinityHomotopyEquiv` witnesses that its forward morphism is a homotopy
equivalence. -/
theorem _root_.TauCeti.AInfinityHomotopyEquiv.isHomotopyEquiv_toHom
    (e : AInfinityHomotopyEquiv AA BB) : e.toHom.IsHomotopyEquiv :=
  ⟨e.invHom, e.leftHomotopy.homotopic, e.rightHomotopy.homotopic⟩

/-- An explicit `AInfinityHomotopyEquiv` witnesses that its inverse morphism is a homotopy
equivalence. -/
theorem _root_.TauCeti.AInfinityHomotopyEquiv.isHomotopyEquiv_invHom
    (e : AInfinityHomotopyEquiv AA BB) : e.invHom.IsHomotopyEquiv :=
  e.symm.isHomotopyEquiv_toHom

/-- An `A∞` morphism `f` is a homotopy equivalence if and only if it is the forward morphism of an
`AInfinityHomotopyEquiv`. -/
theorem isHomotopyEquiv_iff_exists_homotopyEquiv (f : AInfinityHom AA BB) :
    f.IsHomotopyEquiv ↔ ∃ e : AInfinityHomotopyEquiv AA BB, e.toHom = f := by
  constructor
  · rintro ⟨g, hL, hR⟩
    obtain ⟨HL⟩ := (homotopic_def _ _).1 hL
    obtain ⟨HR⟩ := (homotopic_def _ _).1 hR
    exact ⟨⟨f, g, HL, HR⟩, rfl⟩
  · rintro ⟨e, rfl⟩
    exact e.isHomotopyEquiv_toHom

/-- The identity `A∞` morphism is a homotopy equivalence. -/
@[simp]
theorem isHomotopyEquiv_id (AA : AInfinityAlgebra R A) : (AInfinityHom.id AA).IsHomotopyEquiv :=
  (AInfinityHomotopyEquiv.refl AA).isHomotopyEquiv_toHom

/-- Homotopy equivalences of `A∞` algebras are closed under composition. -/
theorem IsHomotopyEquiv.comp {g : AInfinityHom BB CC} {f : AInfinityHom AA BB}
    (hg : g.IsHomotopyEquiv) (hf : f.IsHomotopyEquiv) : (g.comp f).IsHomotopyEquiv := by
  obtain ⟨eg, rfl⟩ := (isHomotopyEquiv_iff_exists_homotopyEquiv g).1 hg
  obtain ⟨ef, rfl⟩ := (isHomotopyEquiv_iff_exists_homotopyEquiv f).1 hf
  exact (ef.trans eg).isHomotopyEquiv_toHom

/-- Homotopic `A∞` morphisms are homotopy equivalences together. -/
theorem Homotopic.isHomotopyEquiv_iff {f g : AInfinityHom AA BB} (h : f.Homotopic g) :
    f.IsHomotopyEquiv ↔ g.IsHomotopyEquiv := by
  have aux : ∀ {u v : AInfinityHom AA BB}, u.Homotopic v → v.IsHomotopyEquiv →
      u.IsHomotopyEquiv := by
    intro u v huv hv
    obtain ⟨H⟩ := (homotopic_def u v).1 huv
    obtain ⟨e, rfl⟩ := (isHomotopyEquiv_iff_exists_homotopyEquiv v).1 hv
    exact (e.replaceToHom H).isHomotopyEquiv_toHom
  exact ⟨aux h.symm, aux h⟩

/-- Any explicit homotopy between `f` and `g` identifies `f.IsHomotopyEquiv` with
`g.IsHomotopyEquiv`. -/
theorem Homotopy.isHomotopyEquiv_iff {f g : AInfinityHom AA BB} (h : Homotopy f g) :
    f.IsHomotopyEquiv ↔ g.IsHomotopyEquiv :=
  h.homotopic.isHomotopyEquiv_iff

/-- An `A∞` morphism admitting both a left homotopy inverse and a right homotopy inverse is a
homotopy equivalence. -/
theorem isHomotopyEquiv_of_left_and_right {f : AInfinityHom AA BB}
    (hL : ∃ k : AInfinityHom BB AA, (k.comp f).Homotopic (AInfinityHom.id AA))
    (hR : ∃ g : AInfinityHom BB AA, (f.comp g).Homotopic (AInfinityHom.id BB)) :
    f.IsHomotopyEquiv := by
  obtain ⟨k, hk⟩ := hL
  obtain ⟨g, hg⟩ := hR
  obtain ⟨Hk⟩ := (homotopic_def _ _).1 hk
  obtain ⟨Hg⟩ := (homotopic_def _ _).1 hg
  have hkg : Homotopy k g :=
    ((Hg.symm.compRight k).copy (comp_id k) (comp_assoc k f g).symm).trans
      ((Hk.compLeft g).copy rfl (id_comp g))
  exact ⟨g, ((hkg.symm.compLeft f).trans Hk).homotopic, Hg.homotopic⟩

/-- Every isomorphism of `A∞` algebras is a homotopy equivalence. -/
theorem IsIso.isHomotopyEquiv {f : AInfinityHom AA BB} (hf : f.IsIso) : f.IsHomotopyEquiv :=
  (AInfinityHomotopyEquiv.ofLinearPartBijective f hf.linearPart_bijective).isHomotopyEquiv_toHom

/-- Every homotopy equivalence of `A∞` algebras is a quasi-isomorphism. -/
theorem IsHomotopyEquiv.isQuasiIso {f : AInfinityHom AA BB} (hf : f.IsHomotopyEquiv) :
    f.IsQuasiIso := by
  obtain ⟨e, rfl⟩ := (isHomotopyEquiv_iff_exists_homotopyEquiv f).1 hf
  exact e.isQuasiIso_toHom

/-- Between minimal `A∞` algebras, an `A∞` morphism is a homotopy equivalence if and only if it is
an `A∞` isomorphism. -/
theorem isHomotopyEquiv_iff_isIso (hA : AA.IsMinimal) (hB : BB.IsMinimal)
    (f : AInfinityHom AA BB) : f.IsHomotopyEquiv ↔ f.IsIso :=
  ⟨fun hf ↦ hf.isQuasiIso.isIso hA hB, IsIso.isHomotopyEquiv⟩

end AInfinityHom

/-! ### Obstruction lifting from a linear chain-homotopy inverse -/

section ObstructionLifting

open ReducedTensorWords

variable {AA : AInfinityAlgebra R A} {BB : AInfinityAlgebra R B}

/-- The morphism-component lift of a mapping-cone cocycle `(Φ, Ψ)` using a chain-homotopy inverse
`(g₀, hA, hB)` of `f.linearPart`. -/
private noncomputable def coneLiftG {W : Type*} [AddCommGroup W] [Module R W]
    (f : AInfinityHom AA BB) (g₀ : B →ₗ[R] A) (hA : A →ₗ[R] A) (hB : B →ₗ[R] B)
    (Φ : W →ₗ[R] A) (Ψ : W →ₗ[R] B) : W →ₗ[R] A :=
  hA ∘ₗ Φ + g₀ ∘ₗ (Ψ - (f.linearPart ∘ₗ hA - hB ∘ₗ f.linearPart) ∘ₗ Φ)

/-- The homotopy-component lift of a mapping-cone cocycle `(Φ, Ψ)` using a chain-homotopy inverse
`(g₀, hA, hB)` of `f.linearPart`. -/
private noncomputable def coneLiftH {W : Type*} [AddCommGroup W] [Module R W]
    (f : AInfinityHom AA BB) (hA : A →ₗ[R] A) (hB : B →ₗ[R] B)
    (Φ : W →ₗ[R] A) (Ψ : W →ₗ[R] B) : W →ₗ[R] B :=
  hB ∘ₗ (Ψ - (f.linearPart ∘ₗ hA - hB ∘ₗ f.linearPart) ∘ₗ Φ)

private theorem coneLiftG_eq_zero {W : Type*} [AddCommGroup W] [Module R W]
    (f : AInfinityHom AA BB) (g₀ : B →ₗ[R] A) (hA : A →ₗ[R] A) (hB : B →ₗ[R] B)
    {Φ : W →ₗ[R] A} {Ψ : W →ₗ[R] B} {w : W} (hΦ : Φ w = 0) (hΨ : Ψ w = 0) :
    coneLiftG f g₀ hA hB Φ Ψ w = 0 := by
  simp only [coneLiftG, LinearMap.add_apply, LinearMap.comp_apply, LinearMap.sub_apply, hΦ, hΨ,
    map_zero, sub_zero, add_zero]

private theorem coneLiftH_eq_zero {W : Type*} [AddCommGroup W] [Module R W]
    (f : AInfinityHom AA BB) (hA : A →ₗ[R] A) (hB : B →ₗ[R] B)
    {Φ : W →ₗ[R] A} {Ψ : W →ₗ[R] B} {w : W} (hΦ : Φ w = 0) (hΨ : Ψ w = 0) :
    coneLiftH f hA hB Φ Ψ w = 0 := by
  simp only [coneLiftH, LinearMap.comp_apply, LinearMap.sub_apply, hΦ, hΨ, map_zero, sub_zero]

private theorem isHomogeneous_coneLiftG (f : AInfinityHom AA BB)
    {g₀ : B →ₗ[R] A} (hg₀ : LinearMap.IsHomogeneous g₀ BB.grading.piece AA.grading.piece 0)
    {hA : A →ₗ[R] A} (hhA : LinearMap.IsHomogeneous hA AA.grading.piece AA.grading.piece (-1))
    {hB : B →ₗ[R] B} (hhB : LinearMap.IsHomogeneous hB BB.grading.piece BB.grading.piece (-1))
    {Φ : ReducedTensorWords R B →ₗ[R] A} {Ψ : ReducedTensorWords R B →ₗ[R] B}
    (hΦ : LinearMap.IsHomogeneous Φ (gradedPiece (BB.grading.shift 1)) (AA.grading.shift 1).piece 1)
    (hΨ : LinearMap.IsHomogeneous Ψ (gradedPiece (BB.grading.shift 1))
      (BB.grading.shift 1).piece 0) :
    LinearMap.IsHomogeneous (coneLiftG f g₀ hA hB Φ Ψ) (gradedPiece (BB.grading.shift 1))
      (AA.grading.shift 1).piece 0 := by
  have hf₁ := (LinearMap.isHomogeneous_shift_piece_iff (c := 1)).2 f.isHomogeneous_linearPart
  have hg₀' := (LinearMap.isHomogeneous_shift_piece_iff (c := 1)).2 hg₀
  have hhA' := (LinearMap.isHomogeneous_shift_piece_iff (c := 1)).2 hhA
  have hhB' := (LinearMap.isHomogeneous_shift_piece_iff (c := 1)).2 hhB
  have h1 : LinearMap.IsHomogeneous (f.linearPart ∘ₗ hA)
      (AA.grading.shift 1).piece (BB.grading.shift 1).piece (-1) := by simpa using hf₁.comp hhA'
  have h2 : LinearMap.IsHomogeneous (hB ∘ₗ f.linearPart)
      (AA.grading.shift 1).piece (BB.grading.shift 1).piece (-1) := by simpa using hhB'.comp hf₁
  have hΔ := h1.sub h2
  have hΔΦ : LinearMap.IsHomogeneous ((f.linearPart ∘ₗ hA - hB ∘ₗ f.linearPart) ∘ₗ Φ)
      (gradedPiece (BB.grading.shift 1)) (BB.grading.shift 1).piece 0 := by
    simpa using hΔ.comp hΦ
  have hΨ' := hΨ.sub hΔΦ
  have hterm₁ : LinearMap.IsHomogeneous (hA ∘ₗ Φ)
      (gradedPiece (BB.grading.shift 1)) (AA.grading.shift 1).piece 0 := by
    simpa using hhA'.comp hΦ
  have hterm₂ : LinearMap.IsHomogeneous
      (g₀ ∘ₗ (Ψ - (f.linearPart ∘ₗ hA - hB ∘ₗ f.linearPart) ∘ₗ Φ))
      (gradedPiece (BB.grading.shift 1)) (AA.grading.shift 1).piece 0 := by
    simpa using hg₀'.comp hΨ'
  exact hterm₁.add hterm₂

private theorem isHomogeneous_coneLiftH (f : AInfinityHom AA BB)
    {hA : A →ₗ[R] A} (hhA : LinearMap.IsHomogeneous hA AA.grading.piece AA.grading.piece (-1))
    {hB : B →ₗ[R] B} (hhB : LinearMap.IsHomogeneous hB BB.grading.piece BB.grading.piece (-1))
    {Φ : ReducedTensorWords R B →ₗ[R] A} {Ψ : ReducedTensorWords R B →ₗ[R] B}
    (hΦ : LinearMap.IsHomogeneous Φ (gradedPiece (BB.grading.shift 1)) (AA.grading.shift 1).piece 1)
    (hΨ : LinearMap.IsHomogeneous Ψ (gradedPiece (BB.grading.shift 1))
      (BB.grading.shift 1).piece 0) :
    LinearMap.IsHomogeneous (coneLiftH f hA hB Φ Ψ) (gradedPiece (BB.grading.shift 1))
      (BB.grading.shift 1).piece (-1) := by
  have hf₁ := (LinearMap.isHomogeneous_shift_piece_iff (c := 1)).2 f.isHomogeneous_linearPart
  have hhA' := (LinearMap.isHomogeneous_shift_piece_iff (c := 1)).2 hhA
  have hhB' := (LinearMap.isHomogeneous_shift_piece_iff (c := 1)).2 hhB
  have h1 : LinearMap.IsHomogeneous (f.linearPart ∘ₗ hA)
      (AA.grading.shift 1).piece (BB.grading.shift 1).piece (-1) := by simpa using hf₁.comp hhA'
  have h2 : LinearMap.IsHomogeneous (hB ∘ₗ f.linearPart)
      (AA.grading.shift 1).piece (BB.grading.shift 1).piece (-1) := by simpa using hhB'.comp hf₁
  have hΔ := h1.sub h2
  have hΔΦ : LinearMap.IsHomogeneous ((f.linearPart ∘ₗ hA - hB ∘ₗ f.linearPart) ∘ₗ Φ)
      (gradedPiece (BB.grading.shift 1)) (BB.grading.shift 1).piece 0 := by
    simpa using hΔ.comp hΦ
  have hΨ' := hΨ.sub hΔΦ
  rw [coneLiftH]
  simpa using hhB'.comp hΨ'

private theorem coneLift_coboundary {W : Type*} [AddCommGroup W] [Module R W]
    (f : AInfinityHom AA BB) {g₀ : B →ₗ[R] A}
    (hg₀_diff : AA.differential ∘ₗ g₀ = g₀ ∘ₗ BB.differential)
    {hA : A →ₗ[R] A}
    (hhA_eq : LinearMap.id - g₀ ∘ₗ f.linearPart = AA.differential ∘ₗ hA + hA ∘ₗ AA.differential)
    {hB : B →ₗ[R] B}
    (hhB_eq : LinearMap.id - f.linearPart ∘ₗ g₀ = BB.differential ∘ₗ hB + hB ∘ₗ BB.differential)
    {dW : W →ₗ[R] W} {Φ : W →ₗ[R] A} {Ψ : W →ₗ[R] B} {w : W}
    (hΦ : AA.differential (Φ w) + Φ (dW w) = 0)
    (hΨ : BB.differential (Ψ w) - Ψ (dW w) = f.linearPart (Φ w)) :
    AA.differential (coneLiftG f g₀ hA hB Φ Ψ w) - coneLiftG f g₀ hA hB Φ Ψ (dW w) = Φ w ∧
      f.linearPart (coneLiftG f g₀ hA hB Φ Ψ w) +
        BB.differential (coneLiftH f hA hB Φ Ψ w) + coneLiftH f hA hB Φ Ψ (dW w) = Ψ w := by
  have hf_diff : ∀ a, BB.differential (f.linearPart a) = f.linearPart (AA.differential a) :=
    fun a ↦ by rw [BB.differential_apply, AA.differential_apply, f.linearPart_m_one]
  have hg_diff : ∀ b, AA.differential (g₀ b) = g₀ (BB.differential b) :=
    LinearMap.congr_fun hg₀_diff
  have hhA' : ∀ a, AA.differential (hA a) + hA (AA.differential a) = a - g₀ (f.linearPart a) :=
    fun a ↦ (LinearMap.congr_fun hhA_eq a).symm
  have hhB' : ∀ b, BB.differential (hB b) + hB (BB.differential b) = b - f.linearPart (g₀ b) :=
    fun b ↦ (LinearMap.congr_fun hhB_eq b).symm
  set Δh : A →ₗ[R] B := f.linearPart ∘ₗ hA - hB ∘ₗ f.linearPart with hΔh_def
  have hΔh : ∀ a, BB.differential (Δh a) + Δh (AA.differential a) = 0 := fun a ↦ by
    have eA := congrArg f.linearPart (hhA' a)
    have eB := hhB' (f.linearPart a)
    simp only [hΔh_def, LinearMap.sub_apply, LinearMap.comp_apply, map_sub, map_add, hf_diff]
      at eA eB ⊢
    calc f.linearPart (AA.differential (hA a)) - BB.differential (hB (f.linearPart a)) +
          (f.linearPart (hA (AA.differential a)) - hB (f.linearPart (AA.differential a)))
        = (f.linearPart (AA.differential (hA a)) + f.linearPart (hA (AA.differential a))) -
            (BB.differential (hB (f.linearPart a)) + hB (f.linearPart (AA.differential a))) := by
          abel
      _ = 0 := by rw [eA, eB]; abel
  have hΦ' : Φ (dW w) = -AA.differential (Φ w) := eq_neg_of_add_eq_zero_right hΦ
  set Ψ' : W →ₗ[R] B := Ψ - Δh ∘ₗ Φ with hΨ'_def
  have hΨ' : Ψ' (dW w) = BB.differential (Ψ' w) - f.linearPart (Φ w) := by
    have eΔ := eq_neg_of_add_eq_zero_left (hΔh (Φ w))
    have eΨ : Ψ (dW w) = BB.differential (Ψ w) - f.linearPart (Φ w) := by
      calc Ψ (dW w) = BB.differential (Ψ w) - (BB.differential (Ψ w) - Ψ (dW w)) := by abel
        _ = _ := by rw [hΨ]
    simp only [hΨ'_def, LinearMap.sub_apply, LinearMap.comp_apply, map_sub, hΦ', map_neg, eΔ, eΨ]
    abel
  constructor
  · rw [coneLiftG, ← hΔh_def, ← hΨ'_def]
    simp only [LinearMap.add_apply, LinearMap.comp_apply, map_add, hg_diff, hΦ', hΨ',
      map_neg, map_sub]
    calc AA.differential (hA (Φ w)) + g₀ (BB.differential (Ψ' w)) -
          (-hA (AA.differential (Φ w)) + (g₀ (BB.differential (Ψ' w)) - g₀ (f.linearPart (Φ w))))
        = (AA.differential (hA (Φ w)) + hA (AA.differential (Φ w))) +
            g₀ (f.linearPart (Φ w)) := by abel
      _ = Φ w := by rw [hhA']; abel
  · rw [coneLiftG, coneLiftH, ← hΔh_def, ← hΨ'_def]
    simp only [LinearMap.add_apply, LinearMap.comp_apply, map_add, hΨ']
    calc f.linearPart (hA (Φ w)) + f.linearPart (g₀ (Ψ' w)) + BB.differential (hB (Ψ' w)) +
          hB (BB.differential (Ψ' w) - f.linearPart (Φ w))
        = (BB.differential (hB (Ψ' w)) + hB (BB.differential (Ψ' w))) +
            f.linearPart (g₀ (Ψ' w)) + Δh (Φ w) := by
          simp only [map_sub, hΔh_def, LinearMap.sub_apply, LinearMap.comp_apply]; abel
      _ = Ψ w := by
          rw [hhB', hΨ'_def, LinearMap.sub_apply, LinearMap.comp_apply]
          abel

/-- The bar-level morphism error `b_A ∘ coalgHom γ - coalgHom γ ∘ b_B`. -/
private noncomputable def morphError (AA : AInfinityAlgebra R A) (BB : AInfinityAlgebra R B)
    (γ : ReducedTensorWords R B →ₗ[R] A) :
    ReducedTensorWords R B →ₗ[R] ReducedTensorWords R A :=
  AA.barDifferential ∘ₗ coalgHom R γ - coalgHom R γ ∘ₗ BB.barDifferential

/-- The bar-level homotopy error `id - F ∘ coalgHom γ - (b_B ∘ H + H ∘ b_B)`. -/
private noncomputable def homotopyError (f : AInfinityHom AA BB)
    (γ : ReducedTensorWords R B →ₗ[R] A) (η : ReducedTensorWords R B →ₗ[R] B) :
    ReducedTensorWords R B →ₗ[R] ReducedTensorWords R B :=
  let H := gradedCoderivAlong (BB.grading.shift 1) 1 LinearMap.id (f.barMap ∘ₗ coalgHom R γ) η
  LinearMap.id - f.barMap ∘ₗ coalgHom R γ - (BB.barDifferential ∘ₗ H + H ∘ₗ BB.barDifferential)

private theorem coalgHom_add_apply_of_mem_filtration_succ
    {γ δg : ReducedTensorWords R B →ₗ[R] A} {n : ℕ}
    (hδg : ∀ u ∈ filtration R B n, δg u = 0) {z : ReducedTensorWords R B}
    (hz : z ∈ filtration R B (n + 1)) :
    coalgHom R (γ + δg) z = coalgHom R γ z + ofLetter R A (δg z) := by
  have heq : ∀ u ∈ filtration R B n, coalgHom R (γ + δg) u = coalgHom R γ u := fun u hu ↦
    (isCoalgHom_coalgHom _).apply_eq_of_mem_filtration (isCoalgHom_coalgHom _)
      (fun w hw ↦ by
        rw [← LinearMap.comp_apply (letter R A), letter_comp_coalgHom,
          ← LinearMap.comp_apply (letter R A), letter_comp_coalgHom, LinearMap.add_apply,
          hδg w hw, add_zero]) hu
  refine eq_of_deconcatenation_eq_of_letter_eq R A ?_ ?_
  · obtain ⟨w, hw⟩ := map_deconcatenation_filtration_succ_le R B n ⟨z, hz, rfl⟩
    rw [map_add, deconcatenation_ofLetter, add_zero,
      (isCoalgHom_coalgHom _).deconcatenation_apply,
      (isCoalgHom_coalgHom _).deconcatenation_apply, ← hw]
    clear hw
    induction w using TensorProduct.inductionOn with
    | tmul u v =>
        simp only [TensorProduct.mapIncl, TensorProduct.map_tmul, Submodule.coe_subtype,
          heq _ u.2, heq _ v.2]
    | add u v hu hv => simp only [map_add, hu, hv]
  · rw [map_add, letter_ofLetter, ← LinearMap.comp_apply (letter R A), letter_comp_coalgHom,
      ← LinearMap.comp_apply (letter R A), letter_comp_coalgHom, LinearMap.add_apply]

private theorem gradedCoderivAlong_add_apply_of_mem_filtration_succ (f : AInfinityHom AA BB)
    {γ δg : ReducedTensorWords R B →ₗ[R] A} {η δh : ReducedTensorWords R B →ₗ[R] B} {n : ℕ}
    (hδg : ∀ u ∈ filtration R B n, δg u = 0) (hδh : ∀ u ∈ filtration R B n, δh u = 0)
    {z : ReducedTensorWords R B} (hz : z ∈ filtration R B (n + 1)) :
    gradedCoderivAlong (BB.grading.shift 1) 1 LinearMap.id
        (f.barMap ∘ₗ coalgHom R (γ + δg)) (η + δh) z =
      gradedCoderivAlong (BB.grading.shift 1) 1 LinearMap.id
        (f.barMap ∘ₗ coalgHom R γ) η z + ofLetter R B (δh z) := by
  have hGeq : ∀ u ∈ filtration R B n, coalgHom R (γ + δg) u = coalgHom R γ u := fun u hu ↦
    (isCoalgHom_coalgHom _).apply_eq_of_mem_filtration (isCoalgHom_coalgHom _)
      (fun w hw ↦ by
        rw [← LinearMap.comp_apply (letter R A), letter_comp_coalgHom,
          ← LinearMap.comp_apply (letter R A), letter_comp_coalgHom, LinearMap.add_apply,
          hδg w hw, add_zero]) hu
  have hcod₁ := isGradedCoderivationAlong_gradedCoderivAlong (G := BB.grading.shift 1) 1
    (isCoalgHom_id B) (f.isCoalgHom_barMap.comp (isCoalgHom_coalgHom (γ + δg))) (η + δh)
  have hcod₂ := isGradedCoderivationAlong_gradedCoderivAlong (G := BB.grading.shift 1) 1
    (isCoalgHom_id B) (f.isCoalgHom_barMap.comp (isCoalgHom_coalgHom γ)) η
  have hHeq : ∀ u ∈ filtration R B n,
      gradedCoderivAlong (BB.grading.shift 1) 1 LinearMap.id
        (f.barMap ∘ₗ coalgHom R (γ + δg)) (η + δh) u =
      gradedCoderivAlong (BB.grading.shift 1) 1 LinearMap.id
        (f.barMap ∘ₗ coalgHom R γ) η u := fun u hu ↦
    hcod₁.apply_eq_of_mem_filtration hcod₂ (fun _ _ _ _ ↦ rfl)
      (fun k hk w hw ↦ by
        rw [LinearMap.comp_apply, LinearMap.comp_apply,
          hGeq w (filtration_monotone R B hk.le hw)])
      (fun w hw ↦ by
        rw [← LinearMap.comp_apply (letter R B), letter_comp_gradedCoderivAlong,
          ← LinearMap.comp_apply (letter R B), letter_comp_gradedCoderivAlong, LinearMap.add_apply,
          hδh w hw, add_zero]) hu
  refine eq_of_deconcatenation_eq_of_letter_eq R B ?_ ?_
  · obtain ⟨w, hw⟩ := map_deconcatenation_filtration_succ_le R B n ⟨z, hz, rfl⟩
    rw [map_add, deconcatenation_ofLetter, add_zero, hcod₁.deconcatenation_apply,
      hcod₂.deconcatenation_apply, ← hw]
    clear hw
    induction w using TensorProduct.inductionOn with
    | tmul u v =>
        simp only [TensorProduct.mapIncl, TensorProduct.map_tmul, Submodule.coe_subtype,
          LinearMap.rTensor_tmul, LinearMap.comp_apply, hHeq _ u.2, hHeq _ v.2, hGeq _ v.2]
    | add u v hu hv =>
        simp only [map_add] at hu hv ⊢
        rw [add_add_add_comm, hu, hv, add_add_add_comm]
  · rw [map_add, letter_ofLetter, ← LinearMap.comp_apply (letter R B),
      letter_comp_gradedCoderivAlong, ← LinearMap.comp_apply (letter R B),
      letter_comp_gradedCoderivAlong, LinearMap.add_apply]

private theorem morphError_eq_ofLetter {γ : ReducedTensorWords R B →ₗ[R] A}
    (hγ : LinearMap.IsHomogeneous γ (gradedPiece (BB.grading.shift 1)) (AA.grading.shift 1).piece 0)
    {n : ℕ} (hEG : ∀ u ∈ filtration R B n, morphError AA BB γ u = 0)
    {z : ReducedTensorWords R B} (hz : z ∈ filtration R B (n + 1)) :
    morphError AA BB γ z = ofLetter R A (letter R A (morphError AA BB γ z)) := by
  have hG : IsCoalgHom R (coalgHom R γ) := isCoalgHom_coalgHom γ
  have hcod : IsGradedCoderivationAlong (BB.grading.shift 1) 1 (coalgHom R γ) (coalgHom R γ)
      (morphError AA BB γ) := by
    have h1 := AA.isGradedCoderivation_barDifferential.comp_isCoalgHom hG
      (isHomogeneous_coalgHom hγ)
    have h2 := (hG.comp_isGradedCoderivation BB.isGradedCoderivation_barDifferential).smul (-1 : R)
    have heq : morphError AA BB γ =
        AA.barDifferential ∘ₗ coalgHom R γ + (-1 : R) • (coalgHom R γ ∘ₗ BB.barDifferential) := by
      ext
      simp [morphError, sub_eq_add_neg]
    rw [heq]
    exact h1.add h2
  refine eq_of_deconcatenation_eq_of_letter_eq R A ?_ (letter_ofLetter R A _).symm
  obtain ⟨w, hw⟩ := map_deconcatenation_filtration_succ_le R B n ⟨z, hz, rfl⟩
  rw [deconcatenation_ofLetter, hcod.deconcatenation_apply, ← hw]
  clear hw
  induction w using TensorProduct.inductionOn with
  | tmul u v =>
      simp only [TensorProduct.mapIncl, TensorProduct.map_tmul, Submodule.coe_subtype,
        LinearMap.rTensor_tmul, hEG _ u.2, hEG _ v.2, TensorProduct.zero_tmul,
        TensorProduct.tmul_zero, add_zero]
  | add u v hu hv =>
      simp only [map_add] at hu hv ⊢
      rw [add_add_add_comm, hu, hv, add_zero]

private theorem homotopyError_eq_ofLetter (f : AInfinityHom AA BB)
    {γ : ReducedTensorWords R B →ₗ[R] A} {η : ReducedTensorWords R B →ₗ[R] B}
    (hγ : LinearMap.IsHomogeneous γ (gradedPiece (BB.grading.shift 1)) (AA.grading.shift 1).piece 0)
    (hη : LinearMap.IsHomogeneous η (gradedPiece (BB.grading.shift 1))
      (BB.grading.shift 1).piece (-1))
    {n : ℕ} (hEG : ∀ u ∈ filtration R B n, morphError AA BB γ u = 0)
    (hEH : ∀ u ∈ filtration R B n, homotopyError f γ η u = 0)
    {z : ReducedTensorWords R B} (hz : z ∈ filtration R B (n + 1)) :
    homotopyError f γ η z = ofLetter R B (letter R B (homotopyError f γ η z)) := by
  set G := coalgHom R γ with hG_def
  set H := gradedCoderivAlong (BB.grading.shift 1) 1 LinearMap.id (f.barMap ∘ₗ G) η with hH_def
  set bB := BB.barDifferential with hbB_def
  set τB := map R ((BB.grading.shift 1).koszulTwist 1) with hτB_def
  have hFG : IsCoalgHom R (f.barMap ∘ₗ G) := f.isCoalgHom_barMap.comp (isCoalgHom_coalgHom γ)
  have hH : IsGradedCoderivationAlong (BB.grading.shift 1) 1 LinearMap.id (f.barMap ∘ₗ G) H :=
    isGradedCoderivationAlong_gradedCoderivAlong 1 (isCoalgHom_id B) hFG η
  have hFG_hom : LinearMap.IsHomogeneous (f.barMap ∘ₗ G)
      (gradedPiece (BB.grading.shift 1)) (gradedPiece (BB.grading.shift 1)) 0 := by
    simpa using f.isHomogeneous_barMap.comp (isHomogeneous_coalgHom hγ)
  have hH₁ : LinearMap.IsHomogeneous H (gradedPiece (BB.grading.shift 1))
      (gradedPiece (BB.grading.shift 1)) (-1) :=
    isHomogeneous_gradedCoderivAlong (LinearMap.isHomogeneous_id _) hFG_hom hη
  have hτH : ∀ w, τB (H w) = -H (τB w) := fun w ↦ by
    have hpow : ((1 : ℤ) * (-1)).negOnePow = -1 := by decide
    simpa only [hpow, Units.val_neg, Units.val_one, Int.cast_neg, Int.cast_one, neg_one_smul,
      LinearMap.comp_apply, LinearMap.smul_apply] using
      LinearMap.congr_fun (hH₁.map_koszulTwist_comp 1) w
  have hτb : ∀ w, τB (bB w) = -bB (τB w) := fun w ↦ by
    have hpow : ((1 : ℤ) * 1).negOnePow = -1 := by decide
    simpa only [hpow, Units.val_neg, Units.val_one, Int.cast_neg, Int.cast_one, neg_one_smul,
      LinearMap.comp_apply, LinearMap.smul_apply] using
      LinearMap.congr_fun (BB.isHomogeneous_barDifferential.map_koszulTwist_comp 1) w
  have hττ : ∀ w, τB (τB w) = w := fun w ↦ by
    rw [hτB_def, ← LinearMap.comp_apply, ← map_comp, InternalGrading.koszulTwist_comp_self,
      map_id, LinearMap.id_apply]
  have hFGb : ∀ v ∈ filtration R B n, bB (f.barMap (G v)) = f.barMap (G (bB v)) := fun v hv ↦ by
    have e := sub_eq_zero.1 (hEG v hv)
    rw [hbB_def, f.barDifferential_barMap, hG_def]
    exact congrArg f.barMap e
  refine eq_of_deconcatenation_eq_of_letter_eq R B ?_ (letter_ofLetter R B _).symm
  obtain ⟨w, hw⟩ := map_deconcatenation_filtration_succ_le R B n ⟨z, hz, rfl⟩
  have hsub := ((isCoalgHom_id B).isGradedCoderivationAlong_sub
    (G := BB.grading.shift 1) hFG).deconcatenation_apply z
  rw [InternalGrading.koszulTwist_zero, map_id, LinearMap.rTensor_id] at hsub
  have heh_def : homotopyError f γ η = LinearMap.id - f.barMap ∘ₗ G - (bB ∘ₗ H + H ∘ₗ bB) := rfl
  rw [deconcatenation_ofLetter, heh_def, LinearMap.sub_apply, LinearMap.add_apply,
    LinearMap.comp_apply, LinearMap.comp_apply, map_sub, map_add, hsub,
    BB.isGradedCoderivation_barDifferential.deconcatenation_apply, hH.deconcatenation_apply,
    hH.deconcatenation_apply, BB.isGradedCoderivation_barDifferential.deconcatenation_apply,
    ← hbB_def, ← hτB_def, ← hw]
  clear hw hsub
  induction w using TensorProduct.inductionOn with
  | tmul u v =>
      have eu := hEH u.1 u.2
      have ev := hEH v.1 v.2
      rw [heh_def] at eu ev
      simp only [LinearMap.sub_apply, LinearMap.add_apply, LinearMap.id_apply,
        LinearMap.comp_apply] at eu ev
      simp only [TensorProduct.mapIncl, TensorProduct.map_tmul, Submodule.coe_subtype,
        map_add, LinearMap.rTensor_tmul, LinearMap.lTensor_tmul, LinearMap.sub_apply,
        LinearMap.id_apply, LinearMap.comp_apply]
      simp only [hτH, hτb, hττ, hFGb v.1 v.2, TensorProduct.neg_tmul]
      refine Eq.trans ?_
        (by rw [eu, ev, TensorProduct.zero_tmul, TensorProduct.tmul_zero, add_zero] :
          (u.1 - f.barMap (G u.1) - (bB (H u.1) + H (bB u.1))) ⊗ₜ[R] f.barMap (G v.1) +
            u.1 ⊗ₜ[R] (v.1 - f.barMap (G v.1) - (bB (H v.1) + H (bB v.1))) = 0)
      simp only [TensorProduct.sub_tmul, TensorProduct.tmul_sub, TensorProduct.add_tmul,
        TensorProduct.tmul_add]
      abel
  | add u v hu hv =>
      simp only [map_add] at hu hv ⊢
      convert congrArg₂ (· + ·) hu hv using 1 <;> abel

private theorem cocycle_of_errors_zero (f : AInfinityHom AA BB)
    {γ : ReducedTensorWords R B →ₗ[R] A} {η : ReducedTensorWords R B →ₗ[R] B}
    (hγ : LinearMap.IsHomogeneous γ (gradedPiece (BB.grading.shift 1)) (AA.grading.shift 1).piece 0)
    (hη : LinearMap.IsHomogeneous η (gradedPiece (BB.grading.shift 1))
      (BB.grading.shift 1).piece (-1))
    {n : ℕ} (hEG : ∀ u ∈ filtration R B n, morphError AA BB γ u = 0)
    (hEH : ∀ u ∈ filtration R B n, homotopyError f γ η u = 0)
    {z : ReducedTensorWords R B} (hz : z ∈ filtration R B (n + 1)) :
    AA.differential (-(letter R A (morphError AA BB γ z))) +
        (-(letter R A (morphError AA BB γ (BB.barDifferential z)))) = 0 ∧
      BB.differential (letter R B (homotopyError f γ η z)) -
        letter R B (homotopyError f γ η (BB.barDifferential z)) =
          f.linearPart (-(letter R A (morphError AA BB γ z))) := by
  have hbz : BB.barDifferential z ∈ filtration R B (n + 1) := BB.barDifferential_mem_filtration hz
  have eGz := morphError_eq_ofLetter hγ hEG hz
  have eGbz := morphError_eq_ofLetter hγ hEG hbz
  have eHz := homotopyError_eq_ofLetter f hγ hη hEG hEH hz
  have eHbz := homotopyError_eq_ofLetter f hγ hη hEG hEH hbz
  have hbA_sq : ∀ w, AA.barDifferential (AA.barDifferential w) = 0 := fun w ↦ by
    simpa only [LinearMap.comp_apply, LinearMap.zero_apply] using
      LinearMap.congr_fun AA.barDifferential_sq w
  have hbB_sq : ∀ w, BB.barDifferential (BB.barDifferential w) = 0 := fun w ↦ by
    simpa only [LinearMap.comp_apply, LinearMap.zero_apply] using
      LinearMap.congr_fun BB.barDifferential_sq w
  constructor
  · have h0 : AA.barDifferential (morphError AA BB γ z) +
        morphError AA BB γ (BB.barDifferential z) = 0 := by
      simp only [morphError, LinearMap.sub_apply, LinearMap.comp_apply, map_sub, hbA_sq, hbB_sq,
        map_zero, zero_sub, sub_zero, neg_add_cancel]
    have h0' := congrArg (letter R A) h0
    rw [eGz, eGbz, map_add, AInfinityAlgebra.barDifferential_ofLetter, letter_ofLetter,
      letter_ofLetter, map_zero, ← AA.differential_apply] at h0'
    rw [map_neg, ← neg_add, h0', neg_zero]
  · have h1 : BB.barDifferential (homotopyError f γ η z) -
        homotopyError f γ η (BB.barDifferential z) = -f.barMap (morphError AA BB γ z) := by
      simp only [homotopyError, morphError, LinearMap.sub_apply, LinearMap.add_apply,
        LinearMap.id_apply, LinearMap.comp_apply, map_sub, map_add, hbB_sq, map_zero,
        f.barDifferential_barMap]
      abel
    have h1' := congrArg (letter R B) h1
    rw [eHz, eHbz, eGz, map_sub, map_neg, AInfinityAlgebra.barDifferential_ofLetter,
      f.barMap_ofLetter, letter_ofLetter, letter_ofLetter, letter_ofLetter,
      ← BB.differential_apply, ← map_neg] at h1'
    exact h1'

private theorem stepLift_errors_zero (f : AInfinityHom AA BB)
    {g₀ : B →ₗ[R] A} (hg₀_diff : AA.differential ∘ₗ g₀ = g₀ ∘ₗ BB.differential)
    {hA : A →ₗ[R] A}
    (hhA_eq : LinearMap.id - g₀ ∘ₗ f.linearPart = AA.differential ∘ₗ hA + hA ∘ₗ AA.differential)
    {hB : B →ₗ[R] B}
    (hhB_eq : LinearMap.id - f.linearPart ∘ₗ g₀ = BB.differential ∘ₗ hB + hB ∘ₗ BB.differential)
    {γ : ReducedTensorWords R B →ₗ[R] A} {η : ReducedTensorWords R B →ₗ[R] B}
    (hγ : LinearMap.IsHomogeneous γ (gradedPiece (BB.grading.shift 1)) (AA.grading.shift 1).piece 0)
    (hη : LinearMap.IsHomogeneous η (gradedPiece (BB.grading.shift 1))
      (BB.grading.shift 1).piece (-1))
    {n : ℕ} (hEG : ∀ u ∈ filtration R B n, morphError AA BB γ u = 0)
    (hEH : ∀ u ∈ filtration R B n, homotopyError f γ η u = 0) :
    let Φ := -(letter R A ∘ₗ morphError AA BB γ)
    let Ψ := letter R B ∘ₗ homotopyError f γ η
    let δg := coneLiftG f g₀ hA hB Φ Ψ
    let δh := coneLiftH f hA hB Φ Ψ
    (∀ u ∈ filtration R B n, δg u = 0) ∧
      (∀ u ∈ filtration R B n, δh u = 0) ∧
      (∀ z ∈ filtration R B (n + 1), morphError AA BB (γ + δg) z = 0) ∧
      (∀ z ∈ filtration R B (n + 1), homotopyError f (γ + δg) (η + δh) z = 0) := by
  intro Φ Ψ δg δh
  have hΦ0 : ∀ u ∈ filtration R B n, Φ u = 0 := fun u hu ↦ by
    simp only [Φ, LinearMap.neg_apply, LinearMap.comp_apply, hEG u hu, map_zero, neg_zero]
  have hΨ0 : ∀ u ∈ filtration R B n, Ψ u = 0 := fun u hu ↦ by
    simp only [Ψ, LinearMap.comp_apply, hEH u hu, map_zero]
  have hδg0 : ∀ u ∈ filtration R B n, δg u = 0 :=
    fun u hu ↦ coneLiftG_eq_zero f g₀ hA hB (hΦ0 u hu) (hΨ0 u hu)
  have hδh0 : ∀ u ∈ filtration R B n, δh u = 0 :=
    fun u hu ↦ coneLiftH_eq_zero f hA hB (hΦ0 u hu) (hΨ0 u hu)
  refine ⟨hδg0, hδh0, fun z hz ↦ ?_, fun z hz ↦ ?_⟩
  · have hbz : BB.barDifferential z ∈ filtration R B (n + 1) := BB.barDifferential_mem_filtration hz
    obtain ⟨hcG, hcH⟩ := cocycle_of_errors_zero f hγ hη hEG hEH hz
    obtain ⟨heqG, _⟩ := coneLift_coboundary f hg₀_diff hhA_eq hhB_eq (dW := BB.barDifferential)
      (Φ := Φ) (Ψ := Ψ) hcG hcH
    rw [morphError, LinearMap.sub_apply, LinearMap.comp_apply, LinearMap.comp_apply,
      coalgHom_add_apply_of_mem_filtration_succ hδg0 hz,
      coalgHom_add_apply_of_mem_filtration_succ hδg0 hbz, map_add,
      AInfinityAlgebra.barDifferential_ofLetter, ← AA.differential_apply]
    have hme : AA.barDifferential (coalgHom R γ z) - coalgHom R γ (BB.barDifferential z) =
        morphError AA BB γ z := rfl
    calc AA.barDifferential (coalgHom R γ z) + ofLetter R A (AA.differential (δg z)) -
          (coalgHom R γ (BB.barDifferential z) + ofLetter R A (δg (BB.barDifferential z)))
        = (AA.barDifferential (coalgHom R γ z) - coalgHom R γ (BB.barDifferential z)) +
            ofLetter R A (AA.differential (δg z) - δg (BB.barDifferential z)) := by
          rw [map_sub]; abel
      _ = 0 := by
          rw [hme, morphError_eq_ofLetter hγ hEG hz, heqG]
          simp only [Φ, LinearMap.neg_apply, LinearMap.comp_apply, map_neg, add_neg_cancel]
  · have hbz : BB.barDifferential z ∈ filtration R B (n + 1) := BB.barDifferential_mem_filtration hz
    obtain ⟨hcG, hcH⟩ := cocycle_of_errors_zero f hγ hη hEG hEH hz
    obtain ⟨_, heqH⟩ := coneLift_coboundary f hg₀_diff hhA_eq hhB_eq (dW := BB.barDifferential)
      (Φ := Φ) (Ψ := Ψ) hcG hcH
    rw [homotopyError, LinearMap.sub_apply, LinearMap.sub_apply, LinearMap.id_apply,
      LinearMap.comp_apply, LinearMap.add_apply, LinearMap.comp_apply, LinearMap.comp_apply,
      coalgHom_add_apply_of_mem_filtration_succ hδg0 hz,
      gradedCoderivAlong_add_apply_of_mem_filtration_succ f hδg0 hδh0 hz,
      gradedCoderivAlong_add_apply_of_mem_filtration_succ f hδg0 hδh0 hbz,
      map_add, map_add, f.barMap_ofLetter, AInfinityAlgebra.barDifferential_ofLetter,
      ← BB.differential_apply]
    have hhe : z - f.barMap (coalgHom R γ z) -
        (BB.barDifferential (gradedCoderivAlong (BB.grading.shift 1) 1 LinearMap.id
            (f.barMap ∘ₗ coalgHom R γ) η z) +
          gradedCoderivAlong (BB.grading.shift 1) 1 LinearMap.id
            (f.barMap ∘ₗ coalgHom R γ) η (BB.barDifferential z)) =
        homotopyError f γ η z := rfl
    calc z - (f.barMap (coalgHom R γ z) + ofLetter R B (f.linearPart (δg z))) -
          (BB.barDifferential (gradedCoderivAlong (BB.grading.shift 1) 1 LinearMap.id
              (f.barMap ∘ₗ coalgHom R γ) η z) +
            ofLetter R B (BB.differential (δh z)) +
            (gradedCoderivAlong (BB.grading.shift 1) 1 LinearMap.id
              (f.barMap ∘ₗ coalgHom R γ) η (BB.barDifferential z) +
              ofLetter R B (δh (BB.barDifferential z))))
        = (z - f.barMap (coalgHom R γ z) -
            (BB.barDifferential (gradedCoderivAlong (BB.grading.shift 1) 1 LinearMap.id
              (f.barMap ∘ₗ coalgHom R γ) η z) +
              gradedCoderivAlong (BB.grading.shift 1) 1 LinearMap.id
                (f.barMap ∘ₗ coalgHom R γ) η (BB.barDifferential z))) -
            ofLetter R B (f.linearPart (δg z) + BB.differential (δh z) +
              δh (BB.barDifferential z)) := by
          rw [map_add, map_add]; abel
      _ = 0 := by
          rw [hhe, homotopyError_eq_ofLetter f hγ hη hEG hEH hz, heqH]
          exact sub_self _

/-- Recursive sequence of partial Taylor pairs `(γ_n, η_n)` lifting `(g₀, hB)` along the
conilpotence filtration. -/
private noncomputable def liftPairSeq (f : AInfinityHom AA BB)
    (g₀ : B →ₗ[R] A) (hA : A →ₗ[R] A) (hB : B →ₗ[R] B) :
    ℕ → (ReducedTensorWords R B →ₗ[R] A) × (ReducedTensorWords R B →ₗ[R] B)
  | 0 => (g₀ ∘ₗ letter R B, hB ∘ₗ letter R B)
  | 1 => (g₀ ∘ₗ letter R B, hB ∘ₗ letter R B)
  | n + 2 =>
    let p := liftPairSeq f g₀ hA hB (n + 1)
    let Φ := -(letter R A ∘ₗ morphError AA BB p.1)
    let Ψ := letter R B ∘ₗ homotopyError f p.1 p.2
    (p.1 + coneLiftG f g₀ hA hB Φ Ψ, p.2 + coneLiftH f hA hB Φ Ψ)

private theorem isHomogeneous_morphError_letter
    {γ : ReducedTensorWords R B →ₗ[R] A}
    (hγ : LinearMap.IsHomogeneous γ (gradedPiece (BB.grading.shift 1))
      (AA.grading.shift 1).piece 0) :
    LinearMap.IsHomogeneous (-(letter R A ∘ₗ morphError AA BB γ))
      (gradedPiece (BB.grading.shift 1)) (AA.grading.shift 1).piece 1 := by
  rw [morphError]
  have hG₀ := isHomogeneous_coalgHom hγ
  have h1 : LinearMap.IsHomogeneous (AA.barDifferential ∘ₗ coalgHom R γ)
      (gradedPiece (BB.grading.shift 1)) (gradedPiece (AA.grading.shift 1)) 1 := by
    simpa using AA.isHomogeneous_barDifferential.comp hG₀
  have h2 : LinearMap.IsHomogeneous (coalgHom R γ ∘ₗ BB.barDifferential)
      (gradedPiece (BB.grading.shift 1)) (gradedPiece (AA.grading.shift 1)) 1 := by
    simpa using hG₀.comp BB.isHomogeneous_barDifferential
  have h3 : LinearMap.IsHomogeneous
      (letter R A ∘ₗ (AA.barDifferential ∘ₗ coalgHom R γ - coalgHom R γ ∘ₗ BB.barDifferential))
      (gradedPiece (BB.grading.shift 1)) (AA.grading.shift 1).piece 1 := by
    simpa using (isHomogeneous_letter (AA.grading.shift 1)).comp (h1.sub h2)
  exact h3.neg

private theorem isHomogeneous_homotopyError_letter (f : AInfinityHom AA BB)
    {γ : ReducedTensorWords R B →ₗ[R] A} {η : ReducedTensorWords R B →ₗ[R] B}
    (hγ : LinearMap.IsHomogeneous γ (gradedPiece (BB.grading.shift 1))
      (AA.grading.shift 1).piece 0)
    (hη : LinearMap.IsHomogeneous η (gradedPiece (BB.grading.shift 1))
      (BB.grading.shift 1).piece (-1)) :
    LinearMap.IsHomogeneous (letter R B ∘ₗ homotopyError f γ η)
      (gradedPiece (BB.grading.shift 1)) (BB.grading.shift 1).piece 0 := by
  rw [homotopyError]
  have hFG₀ : LinearMap.IsHomogeneous (f.barMap ∘ₗ coalgHom R γ)
      (gradedPiece (BB.grading.shift 1)) (gradedPiece (BB.grading.shift 1)) 0 := by
    simpa using f.isHomogeneous_barMap.comp (isHomogeneous_coalgHom hγ)
  have hH₁ : LinearMap.IsHomogeneous
      (gradedCoderivAlong (BB.grading.shift 1) 1 LinearMap.id (f.barMap ∘ₗ coalgHom R γ) η)
      (gradedPiece (BB.grading.shift 1)) (gradedPiece (BB.grading.shift 1)) (-1) :=
    isHomogeneous_gradedCoderivAlong (LinearMap.isHomogeneous_id _) hFG₀ hη
  have hc₁ : LinearMap.IsHomogeneous
      (BB.barDifferential ∘ₗ gradedCoderivAlong (BB.grading.shift 1) 1 LinearMap.id
        (f.barMap ∘ₗ coalgHom R γ) η)
      (gradedPiece (BB.grading.shift 1)) (gradedPiece (BB.grading.shift 1)) 0 := by
    simpa using BB.isHomogeneous_barDifferential.comp hH₁
  have hc₂ : LinearMap.IsHomogeneous
      (gradedCoderivAlong (BB.grading.shift 1) 1 LinearMap.id
        (f.barMap ∘ₗ coalgHom R γ) η ∘ₗ BB.barDifferential)
      (gradedPiece (BB.grading.shift 1)) (gradedPiece (BB.grading.shift 1)) 0 := by
    simpa using hH₁.comp BB.isHomogeneous_barDifferential
  have hEH₀ := ((LinearMap.isHomogeneous_id _).sub hFG₀).sub (hc₁.add hc₂)
  simpa using (isHomogeneous_letter (BB.grading.shift 1)).comp hEH₀

private theorem liftPairSeq_invariant (f : AInfinityHom AA BB)
    {g₀ : B →ₗ[R] A} (hg₀ : LinearMap.IsHomogeneous g₀ BB.grading.piece AA.grading.piece 0)
    (hg₀_diff : AA.differential ∘ₗ g₀ = g₀ ∘ₗ BB.differential)
    {hA : A →ₗ[R] A} (hhA : LinearMap.IsHomogeneous hA AA.grading.piece AA.grading.piece (-1))
    (hhA_eq : LinearMap.id - g₀ ∘ₗ f.linearPart = AA.differential ∘ₗ hA + hA ∘ₗ AA.differential)
    {hB : B →ₗ[R] B} (hhB : LinearMap.IsHomogeneous hB BB.grading.piece BB.grading.piece (-1))
    (hhB_eq : LinearMap.id - f.linearPart ∘ₗ g₀ = BB.differential ∘ₗ hB + hB ∘ₗ BB.differential) :
    ∀ n : ℕ,
      LinearMap.IsHomogeneous (liftPairSeq f g₀ hA hB n).1
        (gradedPiece (BB.grading.shift 1)) (AA.grading.shift 1).piece 0 ∧
      LinearMap.IsHomogeneous (liftPairSeq f g₀ hA hB n).2
        (gradedPiece (BB.grading.shift 1)) (BB.grading.shift 1).piece (-1) ∧
      (∀ z ∈ filtration R B n, morphError AA BB (liftPairSeq f g₀ hA hB n).1 z = 0) ∧
      (∀ z ∈ filtration R B n,
        homotopyError f (liftPairSeq f g₀ hA hB n).1 (liftPairSeq f g₀ hA hB n).2 z = 0) ∧
      (∀ z ∈ filtration R B n,
        (liftPairSeq f g₀ hA hB (n + 1)).1 z = (liftPairSeq f g₀ hA hB n).1 z ∧
        (liftPairSeq f g₀ hA hB (n + 1)).2 z = (liftPairSeq f g₀ hA hB n).2 z) := by
  have hg₀_hom : LinearMap.IsHomogeneous (g₀ ∘ₗ letter R B)
      (gradedPiece (BB.grading.shift 1)) (AA.grading.shift 1).piece 0 := by
    simpa using ((LinearMap.isHomogeneous_shift_piece_iff (c := 1)).2 hg₀).comp
      (isHomogeneous_letter (BB.grading.shift 1))
  have hhB_hom : LinearMap.IsHomogeneous (hB ∘ₗ letter R B)
      (gradedPiece (BB.grading.shift 1)) (BB.grading.shift 1).piece (-1) := by
    simpa using ((LinearMap.isHomogeneous_shift_piece_iff (c := 1)).2 hhB).comp
      (isHomogeneous_letter (BB.grading.shift 1))
  have hbase_EG : ∀ z ∈ filtration R B 1, morphError AA BB (g₀ ∘ₗ letter R B) z = 0 :=
    apply_eq_zero_of_mem_filtration_one R B <| LinearMap.ext fun b ↦ by
      simp only [morphError, LinearMap.comp_apply, LinearMap.sub_apply, LinearMap.zero_apply,
        coalgHom_ofLetter, letter_ofLetter, AInfinityAlgebra.barDifferential_ofLetter,
        ← AA.differential_apply, ← BB.differential_apply]
      rw [← LinearMap.comp_apply AA.differential g₀, hg₀_diff, LinearMap.comp_apply, sub_self]
  have hbase_EH : ∀ z ∈ filtration R B 1,
      homotopyError f (g₀ ∘ₗ letter R B) (hB ∘ₗ letter R B) z = 0 :=
    apply_eq_zero_of_mem_filtration_one R B <| LinearMap.ext fun b ↦ by
      simp only [homotopyError, LinearMap.comp_apply, LinearMap.sub_apply, LinearMap.add_apply,
        LinearMap.id_apply, LinearMap.zero_apply, coalgHom_ofLetter, letter_ofLetter,
        f.barMap_ofLetter, AInfinityAlgebra.barDifferential_ofLetter, gradedCoderivAlong_ofLetter,
        ← BB.differential_apply]
      have hb := LinearMap.congr_fun hhB_eq b
      simp only [LinearMap.sub_apply, LinearMap.id_apply, LinearMap.comp_apply,
        LinearMap.add_apply] at hb
      rw [← map_add, ← hb, map_sub, sub_self]
  intro n
  induction n with
  | zero =>
      refine ⟨hg₀_hom, hhB_hom, fun z hz ↦ ?_, fun z hz ↦ ?_, fun z _ ↦ ⟨rfl, rfl⟩⟩ <;>
      · rw [filtration_zero, Submodule.mem_bot] at hz
        simp [hz]
  | succ m ih =>
      rcases m with _ | k
      · obtain ⟨hδg0, hδh0, _, _⟩ :=
          stepLift_errors_zero f hg₀_diff hhA_eq hhB_eq hg₀_hom hhB_hom hbase_EG hbase_EH
        refine ⟨hg₀_hom, hhB_hom, hbase_EG, hbase_EH, fun z hz ↦ ?_⟩
        simp only [liftPairSeq, LinearMap.add_apply, hδg0 z hz, hδh0 z hz, add_zero, and_self]
      · obtain ⟨hγk, hηk, hEGk, hEHk, _⟩ := ih
        obtain ⟨hδg_prev, hδh_prev, hEG_succ, hEH_succ⟩ :=
          stepLift_errors_zero f hg₀_diff hhA_eq hhB_eq hγk hηk hEGk hEHk
        have hγ_succ : LinearMap.IsHomogeneous (liftPairSeq f g₀ hA hB (k + 2)).1
            (gradedPiece (BB.grading.shift 1)) (AA.grading.shift 1).piece 0 :=
          hγk.add (isHomogeneous_coneLiftG f hg₀ hhA hhB
            (isHomogeneous_morphError_letter hγk) (isHomogeneous_homotopyError_letter f hγk hηk))
        have hη_succ : LinearMap.IsHomogeneous (liftPairSeq f g₀ hA hB (k + 2)).2
            (gradedPiece (BB.grading.shift 1)) (BB.grading.shift 1).piece (-1) :=
          hηk.add (isHomogeneous_coneLiftH f hhA hhB
            (isHomogeneous_morphError_letter hγk) (isHomogeneous_homotopyError_letter f hγk hηk))
        obtain ⟨hδg_next, hδh_next, _, _⟩ :=
          stepLift_errors_zero f hg₀_diff hhA_eq hhB_eq hγ_succ hη_succ hEG_succ hEH_succ
        refine ⟨hγ_succ, hη_succ, hEG_succ, hEH_succ, fun z hz ↦ ?_⟩
        have hstep : liftPairSeq f g₀ hA hB (k + 3) =
            let p := liftPairSeq f g₀ hA hB (k + 2)
            let Φ := -(letter R A ∘ₗ morphError AA BB p.1)
            let Ψ := letter R B ∘ₗ homotopyError f p.1 p.2
            (p.1 + coneLiftG f g₀ hA hB Φ Ψ, p.2 + coneLiftH f hA hB Φ Ψ) := rfl
        rw [hstep]
        simp only [LinearMap.add_apply, hδg_next z hz, hδh_next z hz, add_zero, and_self]

/-- Construct a right `A∞` homotopy inverse `g : BB ⟶ AA` of `f` with `g.linearPart = g₀` from a
homogeneous chain-homotopy inverse `(g₀, hA, hB)` of `f.linearPart`. -/
private noncomputable def rightHomotopyInverse (f : AInfinityHom AA BB)
    (g₀ : B →ₗ[R] A) (hg₀ : LinearMap.IsHomogeneous g₀ BB.grading.piece AA.grading.piece 0)
    (hg₀_diff : AA.differential ∘ₗ g₀ = g₀ ∘ₗ BB.differential)
    (hA : A →ₗ[R] A) (hhA : LinearMap.IsHomogeneous hA AA.grading.piece AA.grading.piece (-1))
    (hhA_eq : LinearMap.id - g₀ ∘ₗ f.linearPart = AA.differential ∘ₗ hA + hA ∘ₗ AA.differential)
    (hB : B →ₗ[R] B) (hhB : LinearMap.IsHomogeneous hB BB.grading.piece BB.grading.piece (-1))
    (hhB_eq : LinearMap.id - f.linearPart ∘ₗ g₀ = BB.differential ∘ₗ hB + hB ∘ₗ BB.differential) :
    Σ' g : AInfinityHom BB AA, g.linearPart = g₀ ∧
      Nonempty (AInfinityHom.Homotopy (f.comp g) (AInfinityHom.id BB)) := by
  have hinv := liftPairSeq_invariant f hg₀ hg₀_diff hhA hhA_eq hhB hhB_eq
  let γSeq : ℕ → (ReducedTensorWords R B →ₗ[R] A) := fun n ↦ (liftPairSeq f g₀ hA hB n).1
  let ηSeq : ℕ → (ReducedTensorWords R B →ₗ[R] B) := fun n ↦ (liftPairSeq f g₀ hA hB n).2
  have hγ_stab : ∀ n, ∀ z ∈ filtration R B n, γSeq (n + 1) z = γSeq n z :=
    fun n z hz ↦ ((hinv n).2.2.2.2 z hz).1
  have hη_stab : ∀ n, ∀ z ∈ filtration R B n, ηSeq (n + 1) z = ηSeq n z :=
    fun n z hz ↦ ((hinv n).2.2.2.2 z hz).2
  let γ := filtrationLimit γSeq
  let η := filtrationLimit ηSeq
  have hγ_hom : LinearMap.IsHomogeneous γ
      (gradedPiece (BB.grading.shift 1)) (AA.grading.shift 1).piece 0 :=
    isHomogeneous_filtrationLimit hγ_stab fun n ↦ (hinv n).1
  have hη_hom : LinearMap.IsHomogeneous η
      (gradedPiece (BB.grading.shift 1)) (BB.grading.shift 1).piece (-1) :=
    isHomogeneous_filtrationLimit hη_stab fun n ↦ (hinv n).2.1
  have hG_eq : ∀ n, ∀ z ∈ filtration R B n, coalgHom R γ z = coalgHom R (γSeq n) z :=
    fun n z hz ↦ (isCoalgHom_coalgHom _).apply_eq_of_mem_filtration (isCoalgHom_coalgHom _)
      (fun w hw ↦ by
        rw [← LinearMap.comp_apply (letter R A), letter_comp_coalgHom,
          ← LinearMap.comp_apply (letter R A), letter_comp_coalgHom,
          filtrationLimit_apply_of_mem_filtration hγ_stab hw]) hz
  have hγ_eq : AA.taylor ∘ₗ coalgHom R γ = γ ∘ₗ BB.barDifferential := by
    refine LinearMap.ext fun z ↦ ?_
    obtain ⟨n, hn⟩ := exists_mem_filtration R B z
    have hEG := (hinv n).2.2.1 z hn
    have h0 := congrArg (letter R A) hEG
    rw [morphError, LinearMap.sub_apply, LinearMap.comp_apply, LinearMap.comp_apply,
      map_sub, map_zero, sub_eq_zero, ← LinearMap.comp_apply (letter R A) AA.barDifferential,
      AA.letter_comp_barDifferential, ← LinearMap.comp_apply (letter R A) (coalgHom R _),
      letter_comp_coalgHom] at h0
    rw [LinearMap.comp_apply, LinearMap.comp_apply, hG_eq n z hn, h0,
      filtrationLimit_apply_of_mem_filtration hγ_stab (BB.barDifferential_mem_filtration hn)]
  let g : AInfinityHom BB AA := AInfinityHom.ofTaylor γ hγ_hom hγ_eq
  have hg_bar : g.barMap = coalgHom R γ := AInfinityHom.barMap_ofTaylor γ hγ_hom hγ_eq
  have hg_lin : g.linearPart = g₀ := by
    ext b
    rw [AInfinityHom.linearPart_apply, AInfinityHom.taylor_ofTaylor,
      filtrationLimit_apply_of_mem_filtration hγ_stab (ofLetter_mem_filtration R B b)]
    simp only [γSeq, liftPairSeq, LinearMap.comp_apply, letter_ofLetter]
  have hH_eq : ∀ n, ∀ z ∈ filtration R B n,
      gradedCoderivAlong (BB.grading.shift 1) 1 LinearMap.id (f.barMap ∘ₗ g.barMap) η z =
      gradedCoderivAlong (BB.grading.shift 1) 1 LinearMap.id (f.barMap ∘ₗ coalgHom R (γSeq n))
        (ηSeq n) z := by
    intro n z hz
    have hc1 := isGradedCoderivationAlong_gradedCoderivAlong (G := BB.grading.shift 1) 1
      (isCoalgHom_id B) (f.isCoalgHom_barMap.comp g.isCoalgHom_barMap) η
    have hc2 := isGradedCoderivationAlong_gradedCoderivAlong (G := BB.grading.shift 1) 1
      (isCoalgHom_id B) (f.isCoalgHom_barMap.comp (isCoalgHom_coalgHom (γSeq n))) (ηSeq n)
    exact hc1.apply_eq_of_mem_filtration hc2 (fun _ _ _ _ ↦ rfl)
      (fun k hk w hw ↦ by
        rw [LinearMap.comp_apply, LinearMap.comp_apply, hg_bar,
          hG_eq n w (filtration_monotone R B hk.le hw)])
      (fun w hw ↦ by
        rw [← LinearMap.comp_apply (letter R B), letter_comp_gradedCoderivAlong,
          ← LinearMap.comp_apply (letter R B), letter_comp_gradedCoderivAlong,
          filtrationLimit_apply_of_mem_filtration hη_stab hw]) hz
  have hη_eq : (AInfinityHom.id BB).taylor - (f.comp g).taylor =
      BB.taylor ∘ₗ gradedCoderivAlong (BB.grading.shift 1) 1 (AInfinityHom.id BB).barMap
        (f.comp g).barMap η + η ∘ₗ BB.barDifferential := by
    refine LinearMap.ext fun z ↦ ?_
    obtain ⟨n, hn⟩ := exists_mem_filtration R B z
    have hEH := (hinv n).2.2.2.1 z hn
    have h0 := congrArg (letter R B) hEH
    rw [homotopyError, LinearMap.sub_apply, LinearMap.sub_apply, LinearMap.id_apply,
      LinearMap.comp_apply, LinearMap.add_apply, LinearMap.comp_apply, LinearMap.comp_apply,
      map_sub, map_sub, map_add, map_zero, sub_eq_zero,
      ← LinearMap.comp_apply (letter R B) f.barMap, ← f.taylor_def,
      ← LinearMap.comp_apply (letter R B) BB.barDifferential, BB.letter_comp_barDifferential,
      ← LinearMap.comp_apply (letter R B) (gradedCoderivAlong ..),
      letter_comp_gradedCoderivAlong] at h0
    simp only [AInfinityHom.taylor_id, AInfinityHom.taylor_comp, AInfinityHom.barMap_id,
      AInfinityHom.barMap_comp, LinearMap.sub_apply, LinearMap.add_apply, LinearMap.comp_apply]
    rw [hH_eq n z hn, hg_bar, hG_eq n z hn,
      filtrationLimit_apply_of_mem_filtration hη_stab (BB.barDifferential_mem_filtration hn)]
    exact h0
  exact ⟨g, hg_lin, ⟨(AInfinityHom.Homotopy.ofTaylor η hη_hom hη_eq).symm⟩⟩

/-- **Homotopy-inverse lifting over a commutative ring.**  Given an `A∞` morphism `f : AA ⟶ BB`
and a homogeneous chain-homotopy inverse `(g₀, hA, hB)` of `f.linearPart` between `(A, m₁)` and
`(B, m₁)`, construct an explicit `AInfinityHomotopyEquiv AA BB` whose forward morphism is `f` and
whose inverse morphism has linear part `g₀`. -/
noncomputable def AInfinityHomotopyEquiv.ofLinearHomotopyInverse (f : AInfinityHom AA BB)
    (g₀ : B →ₗ[R] A) (hg₀ : LinearMap.IsHomogeneous g₀ BB.grading.piece AA.grading.piece 0)
    (hg₀_diff : AA.differential ∘ₗ g₀ = g₀ ∘ₗ BB.differential)
    (hA : A →ₗ[R] A) (hhA : LinearMap.IsHomogeneous hA AA.grading.piece AA.grading.piece (-1))
    (hhA_eq : LinearMap.id - g₀ ∘ₗ f.linearPart = AA.differential ∘ₗ hA + hA ∘ₗ AA.differential)
    (hB : B →ₗ[R] B) (hhB : LinearMap.IsHomogeneous hB BB.grading.piece BB.grading.piece (-1))
    (hhB_eq : LinearMap.id - f.linearPart ∘ₗ g₀ = BB.differential ∘ₗ hB + hB ∘ₗ BB.differential) :
    AInfinityHomotopyEquiv AA BB := by
  let r₁ := rightHomotopyInverse f g₀ hg₀ hg₀_diff hA hhA hhA_eq hB hhB hhB_eq
  let g := r₁.1
  have hg_lin : g.linearPart = g₀ := r₁.2.1
  have hf_diff : BB.differential ∘ₗ f.linearPart = f.linearPart ∘ₗ AA.differential := by
    ext a
    rw [LinearMap.comp_apply, LinearMap.comp_apply, BB.differential_apply, AA.differential_apply,
      f.linearPart_m_one]
  let r₂ := rightHomotopyInverse g f.linearPart f.isHomogeneous_linearPart hf_diff
    hB hhB (by rwa [hg_lin]) hA hhA (by rwa [hg_lin])
  exact AInfinityHomotopyEquiv.ofRightHomotopyInverses
    (Classical.choice r₁.2.2) (Classical.choice r₂.2.2)

@[simp]
theorem AInfinityHomotopyEquiv.toHom_ofLinearHomotopyInverse (f : AInfinityHom AA BB)
    (g₀ hg₀ hg₀_diff hA hhA hhA_eq hB hhB hhB_eq) :
    (AInfinityHomotopyEquiv.ofLinearHomotopyInverse f g₀ hg₀ hg₀_diff hA hhA hhA_eq
      hB hhB hhB_eq).toHom = f := (rfl)

@[simp]
theorem AInfinityHomotopyEquiv.linearPart_invHom_ofLinearHomotopyInverse (f : AInfinityHom AA BB)
    (g₀ hg₀ hg₀_diff hA hhA hhA_eq hB hhB hhB_eq) :
    (AInfinityHomotopyEquiv.ofLinearHomotopyInverse f g₀ hg₀ hg₀_diff hA hhA hhA_eq
      hB hhB hhB_eq).invHom.linearPart = g₀ :=
  (rightHomotopyInverse f g₀ hg₀ hg₀_diff hA hhA hhA_eq hB hhB hhB_eq).2.1

/-- **Homological Whitehead criterion over a commutative ring.**  An `A∞` morphism `f : AA ⟶ BB`
over an arbitrary commutative ring `R` is a homotopy equivalence if and only if its linear part
`f.linearPart` admits a homogeneous chain-homotopy inverse between `(A, AA.differential)` and
`(B, BB.differential)`. -/
theorem AInfinityHom.isHomotopyEquiv_iff_exists_linearHomotopyInverse (f : AInfinityHom AA BB) :
    f.IsHomotopyEquiv ↔
      ∃ (g₀ : B →ₗ[R] A) (hA : A →ₗ[R] A) (hB : B →ₗ[R] B),
        LinearMap.IsHomogeneous g₀ BB.grading.piece AA.grading.piece 0 ∧
        AA.differential ∘ₗ g₀ = g₀ ∘ₗ BB.differential ∧
        LinearMap.IsHomogeneous hA AA.grading.piece AA.grading.piece (-1) ∧
        LinearMap.id - g₀ ∘ₗ f.linearPart = AA.differential ∘ₗ hA + hA ∘ₗ AA.differential ∧
        LinearMap.IsHomogeneous hB BB.grading.piece BB.grading.piece (-1) ∧
        LinearMap.id - f.linearPart ∘ₗ g₀ = BB.differential ∘ₗ hB + hB ∘ₗ BB.differential := by
  constructor
  · intro hf
    obtain ⟨e, rfl⟩ := (f.isHomotopyEquiv_iff_exists_homotopyEquiv).1 hf
    refine ⟨e.invHom.linearPart, e.leftHomotopy.symm.linearHomotopy,
      e.rightHomotopy.symm.linearHomotopy, e.invHom.isHomogeneous_linearPart, ?_, ?_, ?_, ?_, ?_⟩
    · ext b
      rw [LinearMap.comp_apply, LinearMap.comp_apply, AA.differential_apply, BB.differential_apply,
        e.invHom.linearPart_m_one]
    · rw [LinearMap.isHomogeneous_def]
      exact fun _ _ ha ↦ e.leftHomotopy.symm.linearHomotopy_mem ha
    · ext a
      simpa only [LinearMap.sub_apply, LinearMap.id_apply, LinearMap.comp_apply,
        LinearMap.add_apply, AInfinityHom.linearPart_id, AInfinityHom.linearPart_comp,
        AA.differential_apply] using e.leftHomotopy.symm.linearPart_sub_linearPart a
    · rw [LinearMap.isHomogeneous_def]
      exact fun _ _ hb ↦ e.rightHomotopy.symm.linearHomotopy_mem hb
    · ext b
      simpa only [LinearMap.sub_apply, LinearMap.id_apply, LinearMap.comp_apply,
        LinearMap.add_apply, AInfinityHom.linearPart_id, AInfinityHom.linearPart_comp,
        BB.differential_apply] using e.rightHomotopy.symm.linearPart_sub_linearPart b
  · rintro ⟨g₀, hA, hB, hg₀, hg₀_diff, hhA, hhA_eq, hhB, hhB_eq⟩
    exact (AInfinityHomotopyEquiv.ofLinearHomotopyInverse f g₀ hg₀ hg₀_diff hA hhA hhA_eq
      hB hhB hhB_eq).isHomotopyEquiv_toHom

end ObstructionLifting

end CommRing

/-! ### Minimal-model homotopy equivalence and quasi-isomorphism inversion over a field -/

section Field

variable {K : Type uK} {A : Type uA} {B : Type uB} [Field K]
  [AddCommGroup A] [Module K A] [AddCommGroup B] [Module K B]

/-- The homotopy from the identity of an `A∞` algebra over a field to the inclusion of its minimal
model after the projection onto its minimal model. -/
noncomputable def AInfinityAlgebra.minimalModelHomotopy (𝒜 : AInfinityAlgebra K A) :
    AInfinityHom.Homotopy (AInfinityHom.id 𝒜)
      (𝒜.minimalModelInclusion.comp 𝒜.minimalModelProjection) :=
  (𝒜.transferHomotopy 𝒜.cohomologyContraction
    𝒜.isHomogeneous_cohomologyContraction_homotopy
    𝒜.isHomogeneous_cohomologyContraction_incl
    𝒜.isHomogeneous_cohomologyContraction_proj).copy
    rfl 𝒜.minimalModelInclusion_comp_minimalModelProjection.symm

/-- The linear component of the minimal-model homotopy is the chosen cohomology contraction
homotopy. -/
@[simp]
theorem AInfinityAlgebra.linearHomotopy_minimalModelHomotopy (𝒜 : AInfinityAlgebra K A) :
    𝒜.minimalModelHomotopy.linearHomotopy = 𝒜.cohomologyContraction.homotopy := by
  simp [AInfinityAlgebra.minimalModelHomotopy]

/-- Over a field, every `A∞` algebra is homotopy equivalent to its minimal model on cohomology. -/
noncomputable def AInfinityAlgebra.minimalModelHomotopyEquiv (𝒜 : AInfinityAlgebra K A) :
    AInfinityHomotopyEquiv 𝒜.minimalModel 𝒜 where
  toHom := 𝒜.minimalModelInclusion
  invHom := 𝒜.minimalModelProjection
  leftHomotopy := (AInfinityHom.Homotopy.refl (AInfinityHom.id 𝒜.minimalModel)).copy
    𝒜.minimalModelProjection_comp_minimalModelInclusion.symm rfl
  rightHomotopy := 𝒜.minimalModelHomotopy.symm

@[simp]
theorem AInfinityAlgebra.toHom_minimalModelHomotopyEquiv (𝒜 : AInfinityAlgebra K A) :
    𝒜.minimalModelHomotopyEquiv.toHom = 𝒜.minimalModelInclusion := (rfl)

@[simp]
theorem AInfinityAlgebra.invHom_minimalModelHomotopyEquiv (𝒜 : AInfinityAlgebra K A) :
    𝒜.minimalModelHomotopyEquiv.invHom = 𝒜.minimalModelProjection := (rfl)

namespace AInfinityHom

variable {AA : AInfinityAlgebra K A} {BB : AInfinityAlgebra K B}

/-- **Inversion of `A∞` quasi-isomorphisms up to homotopy over a field.**
Every `A∞` quasi-isomorphism `f : AA ⟶ BB` over a field extends to an explicit
`AInfinityHomotopyEquiv AA BB` with forward morphism `f`. -/
noncomputable def IsQuasiIso.homotopyEquiv {f : AInfinityHom AA BB} (hf : f.IsQuasiIso) :
    AInfinityHomotopyEquiv AA BB := by
  let φ : AInfinityHom AA.minimalModel BB.minimalModel :=
    (BB.minimalModelProjection.comp f).comp AA.minimalModelInclusion
  have hφ : Function.Bijective φ.linearPart :=
    (((BB.isQuasiIso_minimalModelProjection.comp hf).comp
      AA.isQuasiIso_minimalModelInclusion).isIso
      AA.isMinimal_minimalModel BB.isMinimal_minimalModel).linearPart_bijective
  let e : AInfinityHomotopyEquiv AA BB :=
    (AA.minimalModelHomotopyEquiv.symm.trans
      (AInfinityHomotopyEquiv.ofLinearPartBijective φ hφ)).trans
      BB.minimalModelHomotopyEquiv
  have hfe : Homotopy f e.toHom := by
    have h1 : Homotopy f (BB.minimalModelInclusion.comp (BB.minimalModelProjection.comp f)) :=
      (BB.minimalModelHomotopy.compLeft f).copy (id_comp f)
        (comp_assoc BB.minimalModelInclusion BB.minimalModelProjection f)
    have h2 : Homotopy (BB.minimalModelProjection.comp f)
        (φ.comp AA.minimalModelProjection) :=
      (AA.minimalModelHomotopy.compRight (BB.minimalModelProjection.comp f)).copy
        (comp_id _) (comp_assoc (BB.minimalModelProjection.comp f)
          AA.minimalModelInclusion AA.minimalModelProjection).symm
    exact h1.trans (h2.compRight BB.minimalModelInclusion)
  exact e.replaceToHom hfe

@[simp]
theorem IsQuasiIso.toHom_homotopyEquiv {f : AInfinityHom AA BB} (hf : f.IsQuasiIso) :
    hf.homotopyEquiv.toHom = f := (rfl)

/-- Over a field, every `A∞` quasi-isomorphism is a homotopy equivalence. -/
theorem IsQuasiIso.isHomotopyEquiv {f : AInfinityHom AA BB} (hf : f.IsQuasiIso) :
    f.IsHomotopyEquiv :=
  hf.homotopyEquiv.isHomotopyEquiv_toHom

/-- **Whitehead theorem for `A∞` algebras over a field.**  Over a field, an `A∞` morphism is a
homotopy equivalence if and only if it is a quasi-isomorphism. -/
theorem isHomotopyEquiv_iff_isQuasiIso (f : AInfinityHom AA BB) :
    f.IsHomotopyEquiv ↔ f.IsQuasiIso :=
  ⟨IsHomotopyEquiv.isQuasiIso, IsQuasiIso.isHomotopyEquiv⟩

end AInfinityHom

end Field

end TauCeti
