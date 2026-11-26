/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.Ring.Basic
public import Mathlib.LinearAlgebra.Finsupp.LinearCombination
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.Jacobson.Ideal
public import TauCeti.RingTheory.DeltaRing.Basic
public import TauCeti.RingTheory.Ideal.Span

/-!
# Frames

Fix a natural number `p` (in applications a prime). A *frame* is a quadruple `(S, I, φ, φ₁)`
consisting of a commutative ring `S`, an ideal `I` of `S` with `I + p S` contained in the
Jacobson radical of `S`, a ring endomorphism `φ` of `S` lifting the `p`-th power map modulo `p`,
and a `φ`-semilinear map `φ₁ : I → S` whose image generates the unit ideal of `S`. Frames are the
coefficient rings of windows and displays: the Witt vectors of a perfect ring with the inverse of
the Verschiebung, the Breuil–Kisin ring `W(k)⟦u⟧` with `φ₁ (p a) = φ a`, and Zink's subring of
the Witt vectors of a complete local ring are frames, and a display over a frame is a module with
a Frobenius-semilinear structure modelled on `(φ, φ₁)`.

Because the image of `φ₁` generates `S`, there is a unique *frame constant* `θ ∈ S` with
`φ a = θ * φ₁ a` for every `a ∈ I` (`TauCeti.DisplayFrame.constant`,
`TauCeti.DisplayFrame.frobenius_eq_constant_mul`): writing `1 = ∑ sᵢ φ₁ aᵢ`, it is
`θ = ∑ sᵢ φ aᵢ`. A *`p`-frame* is a frame with `θ = p`. For `p = 2` the Zink frame of `ℤ₂` has
`θ = 2 - [4] ≠ 2`, which is why the frame constant is not fixed in the definition.

A *strict homomorphism* of frames is a ring homomorphism carrying the ideal into the ideal and
commuting with `φ` and with `φ₁` (`TauCeti.DisplayFrame.Hom`). It carries the frame constant to the
frame constant (`TauCeti.DisplayFrame.Hom.map_constant`) and induces a ring homomorphism of
residue rings `S ⧸ I → S' ⧸ I'` (`TauCeti.DisplayFrame.Hom.residueMap`). Frames and strict
homomorphisms form a category (`TauCeti.DisplayFrameCat`), with a residue-ring functor to
commutative rings (`TauCeti.DisplayFrameCat.residueFunctor`). Homomorphisms multiplying the
divided Frobenius by a unit are not included.

## Main definitions

* `TauCeti.DisplayFrame p I`: the frame structures `(φ, φ₁)` on a fixed ring `S` and ideal `I`.
* `TauCeti.DisplayFrame.constant`: the frame constant `θ`.
* `TauCeti.DisplayFrame.IsPFrame`: the frame constant is `p`.
* `TauCeti.DisplayFrame.Hom`: strict homomorphisms of frames, with `id` and `comp`.
* `TauCeti.DisplayFrame.Hom.residueMap`: the induced map `S ⧸ I →+* S' ⧸ I'`.
* `TauCeti.DisplayFrameCat p`: the category of frames and strict homomorphisms.
* `TauCeti.DisplayFrameCat.residueFunctor`: the functor `(S, I, φ, φ₁) ↦ S ⧸ I`.

## Main results

* `TauCeti.DisplayFrame.ext`: two frame structures on `(S, I)` with the same `φ` and `φ₁` are
  equal.
* `TauCeti.DisplayFrame.eq_of_forall_mul_divFrobenius_eq`: an element of `S` is determined by its
  products with the values of `φ₁`.
* `TauCeti.DisplayFrame.frobenius_eq_constant_mul`, `TauCeti.DisplayFrame.eq_constant_iff`: the
  frame constant is the unique `θ` with `φ a = θ * φ₁ a` on `I`.
* `TauCeti.DisplayFrame.Hom.map_constant`: strict homomorphisms preserve the frame constant.

## References

* E. Lau, *Relations between Dieudonné displays and crystalline Dieudonné theory*, Algebra Number
  Theory 8 (2014), §2A, p. 2214, and Lemma 2.5, p. 2217.
* M. Kisin, G. Pappas and R. Zhou, *Integral models of Shimura varieties with parahoric level
  structure, II*, §5.1.1–5.1.2.
-/

public section

universe u v w

open CategoryTheory

namespace TauCeti

/-- A *frame* structure on a commutative ring `S` and an ideal `I`: a ring endomorphism `φ` of `S`
lifting the `p`-th power map modulo `p`, and a `φ`-semilinear map `φ₁ : I → S` (the *divided
Frobenius*) whose image generates the unit ideal, such that `I + p S` lies in the Jacobson radical
of `S` (Lau, §2A). Fixing `S` and `I` as parameters makes a frame structure determined by `φ` and
`φ₁` (`TauCeti.DisplayFrame.ext`). -/
structure DisplayFrame (p : ℕ) {S : Type u} [CommRing S] (I : Ideal S) where
  /-- The Frobenius lift `φ : S → S`. -/
  frobenius : S →+* S
  /-- The divided Frobenius `φ₁ : I → S`, semilinear over `φ`. -/
  divFrobenius : I →ₛₗ[frobenius] S
  /-- `φ` lifts the `p`-th power map modulo `p`. -/
  isFrobeniusLift : DeltaRing.IsFrobeniusLift p frobenius
  /-- `I + p S` lies in the Jacobson radical of `S`. -/
  sup_span_le_jacobson : I ⊔ Ideal.span {(p : S)} ≤ Ring.jacobson S
  /-- The image of `φ₁` generates the unit ideal of `S`. -/
  span_range_divFrobenius : Ideal.span (Set.range divFrobenius) = ⊤

namespace DisplayFrame

variable {p : ℕ} {S : Type u} [CommRing S] {I : Ideal S} (F : DisplayFrame p I)

/-- Two frame structures on `(S, I)` with the same Frobenius and divided Frobenius are equal. -/
@[ext]
theorem ext {G : DisplayFrame p I} (h : F.frobenius = G.frobenius)
    (h₁ : ∀ a, F.divFrobenius a = G.divFrobenius a) : F = G := by
  obtain ⟨φ, φ₁, _, _, _⟩ := F
  obtain ⟨ψ, ψ₁, _, _, _⟩ := G
  obtain rfl : φ = ψ := h
  obtain rfl : φ₁ = ψ₁ := LinearMap.ext h₁
  rfl

/-- `φ₁ (s • a) = φ s * φ₁ a`. -/
theorem divFrobenius_smul (s : S) (a : I) :
    F.divFrobenius (s • a) = F.frobenius s * F.divFrobenius a :=
  F.divFrobenius.map_smulₛₗ s a

/-- The ideal of a frame lies in the Jacobson radical. -/
theorem ideal_le_jacobson (F : DisplayFrame p I) : I ≤ Ring.jacobson S :=
  le_sup_left.trans F.sup_span_le_jacobson

/-- `p` lies in the Jacobson radical of the ring of a frame. -/
theorem natCast_mem_jacobson (F : DisplayFrame p I) : (p : S) ∈ Ring.jacobson S :=
  F.sup_span_le_jacobson (Ideal.mem_sup_right (Ideal.subset_span rfl))

/-- An element of `S` is determined by its products with the values of `φ₁`. -/
theorem eq_of_forall_mul_divFrobenius_eq {s t : S}
    (h : ∀ a, s * F.divFrobenius a = t * F.divFrobenius a) : s = t :=
  Ideal.eq_of_forall_mul_eq_of_span_eq_top F.span_range_divFrobenius (Set.forall_mem_range.mpr h)

/-- There is a unique `θ` with `φ a = θ * φ₁ a` for every `a ∈ I`: writing `1 = ∑ sᵢ φ₁ aᵢ`, it is
`θ = ∑ sᵢ φ aᵢ`. -/
theorem exists_unique_constant : ∃! θ : S, ∀ a : I, F.frobenius a = θ * F.divFrobenius a := by
  obtain ⟨c, hc⟩ := Finsupp.mem_span_range_iff_exists_finsupp.mp
    (F.span_range_divFrobenius ▸ Submodule.mem_top (x := (1 : S)))
  have h : ∀ a : I, F.frobenius a = (c.sum fun b s ↦ s * F.frobenius b) * F.divFrobenius a := by
    intro a
    rw [← mul_one (F.frobenius a), ← hc, Finsupp.mul_sum, Finsupp.sum_mul]
    refine Finsupp.sum_congr fun b _ ↦ ?_
    have h₁ := F.divFrobenius_smul (a : S) b
    have h₂ := F.divFrobenius_smul (b : S) a
    rw [show (a : S) • b = (b : S) • a from Subtype.ext (mul_comm _ _)] at h₁
    rw [smul_eq_mul]
    linear_combination (c b) * (h₂ - h₁)
  exact ⟨_, h, fun θ hθ ↦ F.eq_of_forall_mul_divFrobenius_eq fun a ↦ by rw [← hθ, ← h]⟩

/-- The *frame constant* `θ ∈ S`, the unique element with `φ a = θ * φ₁ a` for every `a ∈ I`
(`TauCeti.DisplayFrame.frobenius_eq_constant_mul`, `TauCeti.DisplayFrame.eq_constant_iff`). -/
noncomputable def constant : S :=
  F.exists_unique_constant.exists.choose

/-- The frame constant satisfies `φ a = θ * φ₁ a` for every `a ∈ I`. -/
theorem frobenius_eq_constant_mul (a : I) : F.frobenius a = F.constant * F.divFrobenius a :=
  F.exists_unique_constant.exists.choose_spec a

/-- The frame constant is the unique `θ` with `φ a = θ * φ₁ a` for every `a ∈ I`. -/
theorem eq_constant_iff {θ : S} :
    θ = F.constant ↔ ∀ a : I, F.frobenius a = θ * F.divFrobenius a :=
  ⟨fun h ↦ h ▸ F.frobenius_eq_constant_mul, fun h ↦
    F.eq_of_forall_mul_divFrobenius_eq fun a ↦ by rw [← h, frobenius_eq_constant_mul]⟩

/-- A frame is a *`p`-frame* if its frame constant is `p`. -/
def IsPFrame : Prop :=
  F.constant = p

/-- A frame is a `p`-frame iff its frame constant is `p`. -/
theorem isPFrame_iff_constant_eq : F.IsPFrame ↔ F.constant = p :=
  Iff.rfl

/-- A frame is a `p`-frame iff `φ a = p * φ₁ a` for every `a ∈ I`. -/
theorem isPFrame_iff : F.IsPFrame ↔ ∀ a : I, F.frobenius a = p * F.divFrobenius a := by
  rw [IsPFrame, eq_comm, eq_constant_iff]

/-- A *strict homomorphism* of frames `(S, I, φ, φ₁) → (S', I', φ', φ₁')`: a ring homomorphism
`f : S → S'` with `f I ⊆ I'`, `f ∘ φ = φ' ∘ f` and `f ∘ φ₁ = φ₁' ∘ f` on `I`. -/
structure Hom {S' : Type v} [CommRing S'] {I' : Ideal S'} (F : DisplayFrame p I)
    (F' : DisplayFrame p I') extends S →+* S' where
  /-- `f` carries `I` into `I'`. -/
  map_mem' : ∀ a ∈ I, toRingHom a ∈ I'
  /-- `f ∘ φ = φ' ∘ f`. -/
  map_frobenius' (s : S) : toRingHom (F.frobenius s) = F'.frobenius (toRingHom s)
  /-- `f ∘ φ₁ = φ₁' ∘ f` on `I`. -/
  map_divFrobenius' (a : I) :
    F'.divFrobenius ⟨toRingHom a, map_mem' a a.property⟩ = toRingHom (F.divFrobenius a)

namespace Hom

variable {F} {S' : Type v} [CommRing S'] {I' : Ideal S'} {F' : DisplayFrame p I'}
  {S'' : Type w} [CommRing S''] {I'' : Ideal S''} {F'' : DisplayFrame p I''}

instance : FunLike (Hom F F') S S' where
  coe f := f.toFun
  coe_injective f g h := by
    obtain ⟨⟨_, _⟩, _, _, _⟩ := f
    obtain ⟨⟨_, _⟩, _, _, _⟩ := g
    congr
    exact DFunLike.coe_injective h

instance : RingHomClass (Hom F F') S S' where
  map_add f := f.map_add'
  map_mul f := f.map_mul'
  map_zero f := f.map_zero'
  map_one f := f.map_one'

@[simp]
theorem coe_toRingHom (f : Hom F F') : ⇑f.toRingHom = f :=
  (rfl)

@[simp]
theorem coe_mk (f : S →+* S') (h₁ h₂ h₃) : ⇑(Hom.mk f h₁ h₂ h₃ : Hom F F') = f :=
  (rfl)

@[ext]
theorem ext {f g : Hom F F'} (h : ∀ s, f s = g s) : f = g :=
  DFunLike.ext _ _ h

theorem map_mem (f : Hom F F') {a : S} (ha : a ∈ I) : f a ∈ I' :=
  f.map_mem' a ha

theorem le_comap (f : Hom F F') : I ≤ I'.comap (f : S →+* S') :=
  fun _ ↦ f.map_mem

@[simp]
theorem map_frobenius (f : Hom F F') (s : S) : f (F.frobenius s) = F'.frobenius (f s) :=
  f.map_frobenius' s

theorem map_divFrobenius (f : Hom F F') (a : I) :
    F'.divFrobenius ⟨f a, f.map_mem a.property⟩ = f (F.divFrobenius a) :=
  f.map_divFrobenius' a

/-- A strict homomorphism carries the frame constant to the frame constant. -/
@[simp]
theorem map_constant (f : Hom F F') : f F.constant = F'.constant := by
  have hspan :
      Ideal.span (Set.range fun a : I ↦ F'.divFrobenius ⟨f a, f.map_mem a.property⟩) = ⊤ := by
    have := congrArg (Ideal.map (f : S →+* S')) F.span_range_divFrobenius
    rw [Ideal.map_span, Ideal.map_top, ← Set.range_comp] at this
    rwa [show (fun a : I ↦ F'.divFrobenius ⟨f a, f.map_mem a.property⟩) = f ∘ F.divFrobenius from
      funext f.map_divFrobenius]
  refine Ideal.eq_of_forall_mul_eq_of_span_eq_top hspan (Set.forall_mem_range.mpr fun a ↦ ?_)
  have h₁ := F'.frobenius_eq_constant_mul ⟨f a, f.map_mem a.property⟩
  have h₂ := congrArg f (F.frobenius_eq_constant_mul a)
  rw [map_mul, map_frobenius, ← map_divFrobenius] at h₂
  linear_combination h₁ - h₂

variable (F) in
/-- The identity strict homomorphism. -/
protected def id : Hom F F where
  toRingHom := RingHom.id S
  map_mem' _ ha := ha
  map_frobenius' _ := rfl
  map_divFrobenius' _ := rfl

variable (F) in
@[simp]
theorem id_apply (s : S) : Hom.id F s = s :=
  (rfl)

/-- The composite of two strict homomorphisms. -/
def comp (g : Hom F' F'') (f : Hom F F') : Hom F F'' where
  toRingHom := (g : S' →+* S'').comp f
  map_mem' _ ha := g.map_mem (f.map_mem ha)
  map_frobenius' s := by simp
  map_divFrobenius' a := by
    simpa [map_divFrobenius] using g.map_divFrobenius ⟨f a, f.map_mem a.property⟩

@[simp]
theorem comp_apply (g : Hom F' F'') (f : Hom F F') (s : S) : g.comp f s = g (f s) :=
  (rfl)

@[simp]
theorem comp_id (f : Hom F F') : f.comp (Hom.id F) = f :=
  (rfl)

@[simp]
theorem id_comp (f : Hom F F') : (Hom.id F').comp f = f :=
  (rfl)

theorem comp_assoc {S''' : Type*} [CommRing S'''] {I''' : Ideal S'''} {F''' : DisplayFrame p I'''}
    (h : Hom F'' F''') (g : Hom F' F'') (f : Hom F F') : (h.comp g).comp f = h.comp (g.comp f) :=
  (rfl)

/-- The ring homomorphism `S ⧸ I →+* S' ⧸ I'` induced by a strict homomorphism. -/
noncomputable def residueMap (f : Hom F F') : S ⧸ I →+* S' ⧸ I' :=
  Ideal.quotientMap I' (f : S →+* S') f.le_comap

@[simp]
theorem residueMap_mk (f : Hom F F') (s : S) :
    f.residueMap (Ideal.Quotient.mk I s) = Ideal.Quotient.mk I' (f s) :=
  (rfl)

variable (F) in
@[simp]
theorem residueMap_id : (Hom.id F).residueMap = RingHom.id (S ⧸ I) :=
  Ideal.Quotient.ringHom_ext rfl

@[simp]
theorem residueMap_comp (g : Hom F' F'') (f : Hom F F') :
    (g.comp f).residueMap = g.residueMap.comp f.residueMap :=
  Ideal.Quotient.ringHom_ext rfl

end Hom

end DisplayFrame

/-- The category of frames: a commutative ring `S` with an ideal `I` and a frame structure on
`(S, I)`. Its morphisms are the strict homomorphisms `TauCeti.DisplayFrame.Hom`. -/
structure DisplayFrameCat (p : ℕ) where
  /-- The underlying ring `S`. -/
  carrier : Type u
  [commRing : CommRing carrier]
  /-- The ideal `I`. -/
  ideal : Ideal carrier
  /-- The frame structure on `(S, I)`. -/
  frame : DisplayFrame p ideal

attribute [instance] DisplayFrameCat.commRing

namespace DisplayFrameCat

variable {p : ℕ}

instance : CoeSort (DisplayFrameCat.{u} p) (Type u) :=
  ⟨carrier⟩

/-- The object of `DisplayFrameCat p` given by a frame structure on `(S, I)`. -/
abbrev of {S : Type u} [CommRing S] {I : Ideal S} (F : DisplayFrame p I) : DisplayFrameCat.{u} p :=
  ⟨S, I, F⟩

/-- A morphism in `DisplayFrameCat p`: a strict homomorphism of the underlying frames. -/
@[ext]
structure Hom (X Y : DisplayFrameCat.{u} p) where
  /-- The underlying strict homomorphism of frames. -/
  hom : DisplayFrame.Hom X.frame Y.frame

instance : Category (DisplayFrameCat.{u} p) where
  Hom := Hom
  id X := ⟨DisplayFrame.Hom.id X.frame⟩
  comp f g := ⟨g.hom.comp f.hom⟩

@[simp]
theorem hom_id (X : DisplayFrameCat.{u} p) : (𝟙 X : X ⟶ X).hom = DisplayFrame.Hom.id X.frame :=
  (rfl)

@[simp]
theorem hom_comp {X Y Z : DisplayFrameCat.{u} p} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (f ≫ g).hom = g.hom.comp f.hom :=
  (rfl)

@[ext]
theorem hom_ext {X Y : DisplayFrameCat.{u} p} {f g : X ⟶ Y} (h : f.hom = g.hom) : f = g :=
  Hom.ext h

/-- The morphism of `DisplayFrameCat p` given by a strict homomorphism of frames. -/
abbrev ofHom {S S' : Type u} [CommRing S] [CommRing S'] {I : Ideal S} {I' : Ideal S'}
    {F : DisplayFrame p I} {F' : DisplayFrame p I'} (f : DisplayFrame.Hom F F') : of F ⟶ of F' :=
  ⟨f⟩

@[simp]
theorem hom_ofHom {S S' : Type u} [CommRing S] [CommRing S'] {I : Ideal S} {I' : Ideal S'}
    {F : DisplayFrame p I} {F' : DisplayFrame p I'} (f : DisplayFrame.Hom F F') :
    (ofHom f).hom = f :=
  (rfl)

@[simp]
theorem ofHom_hom {X Y : DisplayFrameCat.{u} p} (f : X ⟶ Y) : ofHom f.hom = f :=
  (rfl)

@[simp]
theorem ofHom_id {S : Type u} [CommRing S] {I : Ideal S} (F : DisplayFrame p I) :
    ofHom (DisplayFrame.Hom.id F) = 𝟙 (of F) :=
  (rfl)

@[simp]
theorem ofHom_comp {S S' S'' : Type u} [CommRing S] [CommRing S'] [CommRing S''] {I : Ideal S}
    {I' : Ideal S'} {I'' : Ideal S''} {F : DisplayFrame p I} {F' : DisplayFrame p I'}
    {F'' : DisplayFrame p I''} (f : DisplayFrame.Hom F F') (g : DisplayFrame.Hom F' F'') :
    ofHom (g.comp f) = ofHom f ≫ ofHom g :=
  (rfl)

/-- The residue-ring functor `(S, I, φ, φ₁) ↦ S ⧸ I`. -/
@[expose, simps]
noncomputable def residueFunctor : DisplayFrameCat.{u} p ⥤ CommRingCat.{u} where
  obj X := CommRingCat.of (X ⧸ X.ideal)
  map f := CommRingCat.ofHom f.hom.residueMap
  map_id X := by
    ext : 1
    simp
  map_comp f g := by
    ext : 1
    simp

end DisplayFrameCat

end TauCeti
