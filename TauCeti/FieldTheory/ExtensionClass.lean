/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import TauCeti.FieldTheory.Galois.Restriction
import Mathlib.GroupTheory.Index
import TauCeti.Algebra.Algebra.Equiv
import TauCeti.RingTheory.Finiteness.Basic

/-!
# Isomorphism classes of finite field extensions and transport of structure

For a field `K` in `Type u`, a finite field extension `L/K` in an arbitrary universe embeds over
`K` into `AlgebraicClosure K` with image a finite intermediate field, uniquely up to `K`-algebra
isomorphism. Taking the quotient of the finite intermediate fields of `AlgebraicClosure K` by
`K`-algebra equivalence therefore yields a small carrier `TauCeti.FiniteExtensionClass K : Type u`
representing all `K`-isomorphism classes of finite extensions of `K`, separable or inseparable.

Beyond the intrinsic invariants of a class (degree, separability, and automorphism count) and
restriction of scalars along a finite extension `F/K`, any ring isomorphism `e : F₁ ≃+* F₂` of base
fields induces a bijection `FiniteExtensionClass.mapEquiv e` by transport of structure: the image of
`[L₁]` is the `F₂`-isomorphism class of `L₁` with `F₂` acting through `e⁻¹`, characterized by
`mapEquiv e [L₁] = [L₂]` if and only if there is a ring isomorphism `φ : L₁ ≃+* L₂` intertwining
`algebraMap` with `e`. In particular, for any commutative semiring `R` and `R`-algebra `F`, the
automorphism group `F ≃ₐ[R] F` acts on `FiniteExtensionClass F` on the left.

When `F/K` is a normal extension of fields and `L/F` is finite, the stabilizer of `[L]` in
`F ≃ₐ[K] F` consists of the automorphisms of `F/K` that extend to `L`, namely the image of
`AlgEquiv.restrictNormalHom F : (L ≃ₐ[K] L) →* (F ≃ₐ[K] F)`. Since the kernel of restriction is
`L ≃ₐ[F] L`, the automorphism counts satisfy `#Aut_K(L) = #Aut_F(L) · #Stab([L])`.

## Main definitions

* `TauCeti.FiniteExtensionClass K`: the type of `K`-isomorphism classes of finite field extensions
  of `K`.
* `TauCeti.FiniteExtensionClass.mk K L`: the `K`-isomorphism class of a finite extension `L/K`.
* `TauCeti.FiniteExtensionClass.self K`: the trivial class `[K/K]`.
* `TauCeti.FiniteExtensionClass.lift`: universal property of `FiniteExtensionClass K` for
  isomorphism-invariant functions on `Type u` extensions.
* `TauCeti.FiniteExtensionClass.finrank`, `TauCeti.FiniteExtensionClass.IsSeparable`,
  `TauCeti.FiniteExtensionClass.natCardAut`: degree, separability, and `#Aut_K(L)` of a class.
* `TauCeti.FiniteExtensionClass.restrictScalars K`: restriction of scalars from
  `FiniteExtensionClass F` to `FiniteExtensionClass K` for `F/K` finite.
* `TauCeti.FiniteExtensionClass.mapEquiv e`: bijection `FiniteExtensionClass F₁ ≃
  FiniteExtensionClass F₂` induced by a ring isomorphism `e : F₁ ≃+* F₂`, giving the left
  `MulAction (F ≃ₐ[R] F) (FiniteExtensionClass F)`.

## Main results

* `TauCeti.FiniteExtensionClass.mk_eq_mk_iff`: `mk K L₁ = mk K L₂ ↔ Nonempty (L₁ ≃ₐ[K] L₂)`.
* `TauCeti.FiniteExtensionClass.mapEquiv_mk_eq_mk_iff` and
  `TauCeti.FiniteExtensionClass.smul_mk_eq_mk_iff`: transport of structure characterized by
  semilinear ring or `K`-algebra isomorphisms.
* `TauCeti.FiniteExtensionClass.restrictScalars_eq_restrictScalars_iff`: when `F/K` is finite and
  normal, `c₁.restrictScalars K = c₂.restrictScalars K ↔ ∃ τ : F ≃ₐ[K] F, τ • c₁ = c₂`.
* `TauCeti.FiniteExtensionClass.mem_stabilizer_mk_iff` and
  `TauCeti.FiniteExtensionClass.range_restrictNormalHom_eq_stabilizer_mk`: the stabilizer of
  `mk F L` in `F ≃ₐ[K] F` consists of the extendable automorphisms, and equals the range of
  `AlgEquiv.restrictNormalHom F` when `F/K` is normal.
* `TauCeti.FiniteExtensionClass.natCard_algEquiv_eq_mul_natCard_stabilizer_mk` and
  `TauCeti.FiniteExtensionClass.natCardAut_restrictScalars`:
  `#Aut_K(L) = #Aut_F(L) · #Stab([L])` for normal `F/K`.
-/

public section
noncomputable section

universe u v w

namespace TauCeti

/-- Setoid of `K`-algebra isomorphism on finite intermediate fields of `AlgebraicClosure K`. -/
private def finiteIntermediateFieldSetoid (K : Type u) [Field K] :
    Setoid {M : IntermediateField K (AlgebraicClosure K) // Module.Finite K M} where
  r M₁ M₂ := Nonempty (M₁.val ≃ₐ[K] M₂.val)
  iseqv := ⟨fun _ ↦ ⟨.refl⟩, fun ⟨e⟩ ↦ ⟨e.symm⟩, fun ⟨e₁⟩ ⟨e₂⟩ ↦ ⟨e₁.trans e₂⟩⟩

/-- The type of `K`-isomorphism classes of finite field extensions of `K`, realized as the quotient
of the finite intermediate fields of `AlgebraicClosure K` by `K`-algebra equivalence. -/
def FiniteExtensionClass (K : Type u) [Field K] : Type u :=
  Quotient (finiteIntermediateFieldSetoid K)

namespace FiniteExtensionClass

section Core

variable {K : Type u} [Field K]

variable (K) in
/-- The `K`-isomorphism class of a finite field extension `L/K` in any universe. -/
def mk (L : Type v) [Field L] [Algebra K L] [Module.Finite K L] : FiniteExtensionClass K :=
  let ι : L →ₐ[K] AlgebraicClosure K := IsAlgClosed.lift
  Quotient.mk (finiteIntermediateFieldSetoid K)
    ⟨ι.fieldRange, Module.Finite.equiv ι.equivFieldRange.toLinearEquiv⟩

variable (K) in
/-- The trivial `K`-isomorphism class `[K/K]`. -/
def self : FiniteExtensionClass K := mk K K

variable (K) in
/-- Defining formula of `FiniteExtensionClass.self`: the class of `K` over itself. -/
theorem self_def : self K = mk K K := (rfl)

instance : Inhabited (FiniteExtensionClass K) := ⟨self K⟩

/-- **Equality of finite extension classes.** Two finite extensions of `K` determine the same class
if and only if they are `K`-isomorphic. -/
@[simp]
theorem mk_eq_mk_iff (L₁ : Type v) (L₂ : Type w)
    [Field L₁] [Algebra K L₁] [Module.Finite K L₁]
    [Field L₂] [Algebra K L₂] [Module.Finite K L₂] :
    mk K L₁ = mk K L₂ ↔ Nonempty (L₁ ≃ₐ[K] L₂) := by
  let ι₁ : L₁ →ₐ[K] AlgebraicClosure K := IsAlgClosed.lift
  let ι₂ : L₂ →ₐ[K] AlgebraicClosure K := IsAlgClosed.lift
  refine Quotient.eq.trans ⟨fun ⟨e⟩ ↦ ⟨ι₁.equivFieldRange.trans (e.trans ι₂.equivFieldRange.symm)⟩,
    fun ⟨e⟩ ↦ ⟨ι₁.equivFieldRange.symm.trans (e.trans ι₂.equivFieldRange)⟩⟩

/-- Induction principle for `FiniteExtensionClass K` in terms of finite intermediate fields of
`AlgebraicClosure K`. -/
@[elab_as_elim]
theorem induction_on_intermediateField {motive : FiniteExtensionClass K → Prop}
    (c : FiniteExtensionClass K)
    (h : ∀ (M : IntermediateField K (AlgebraicClosure K)) [Module.Finite K M], motive (mk K M)) :
    motive c := by
  refine Quotient.inductionOn c fun ⟨M, hM⟩ ↦ ?_
  let ι : M →ₐ[K] AlgebraicClosure K := IsAlgClosed.lift
  have hmk : Quotient.mk (finiteIntermediateFieldSetoid K) ⟨M, hM⟩ = mk K M :=
    Quotient.sound ⟨ι.equivFieldRange⟩
  exact hmk ▸ @h M hM

/-- Induction principle for `FiniteExtensionClass K` in terms of finite field extensions in
`Type u`. -/
@[elab_as_elim]
theorem induction_on {motive : FiniteExtensionClass K → Prop} (c : FiniteExtensionClass K)
    (h : ∀ (L : Type u) [Field L] [Algebra K L] [Module.Finite K L], motive (mk K L)) :
    motive c :=
  c.induction_on_intermediateField fun M _ ↦ h M

/-- Every finite extension class over `K : Type u` is represented by a finite extension in
`Type u`. -/
theorem exists_mk (c : FiniteExtensionClass K) :
    ∃ (L : Type u) (_ : Field L) (_ : Algebra K L) (_ : Module.Finite K L), c = mk K L :=
  c.induction_on fun L _ _ _ ↦ ⟨L, inferInstance, inferInstance, inferInstance, rfl⟩

/-- Universal property of `FiniteExtensionClass K`: a function on finite extensions of `K` in
`Type u` that is invariant under `K`-algebra equivalence descends to `FiniteExtensionClass K`. -/
def lift {α : Sort*}
    (f : ∀ (L : Type u) [Field L] [Algebra K L] [Module.Finite K L], α)
    (hf : ∀ (L₁ L₂ : Type u) [Field L₁] [Algebra K L₁] [Module.Finite K L₁]
      [Field L₂] [Algebra K L₂] [Module.Finite K L₂], (L₁ ≃ₐ[K] L₂) → f L₁ = f L₂)
    (c : FiniteExtensionClass K) : α :=
  Quotient.liftOn c (fun M ↦ @f M.val _ _ M.property) fun M₁ M₂
      ⟨e⟩ ↦ @hf M₁.val M₂.val _ _ M₁.property _ _ M₂.property e

/-- Evaluating `FiniteExtensionClass.lift` on `mk K L` recovers the value on `L`. -/
@[simp]
theorem lift_mk {α : Sort*}
    (f : ∀ (L : Type u) [Field L] [Algebra K L] [Module.Finite K L], α)
    (hf : ∀ (L₁ L₂ : Type u) [Field L₁] [Algebra K L₁] [Module.Finite K L₁]
      [Field L₂] [Algebra K L₂] [Module.Finite K L₂], (L₁ ≃ₐ[K] L₂) → f L₁ = f L₂)
    (L : Type u) [Field L] [Algebra K L] [Module.Finite K L] :
    (mk K L).lift f hf = f L := by
  let ι : L →ₐ[K] AlgebraicClosure K := IsAlgClosed.lift
  have : Module.Finite K ι.fieldRange := Module.Finite.equiv ι.equivFieldRange.toLinearEquiv
  exact hf ι.fieldRange L ι.equivFieldRange.symm

end Core

section Invariants

variable {K : Type u} [Field K]

/-- The degree `[L : K]` of a finite extension class `[L]`. -/
def finrank (c : FiniteExtensionClass K) : ℕ :=
  c.lift (fun L _ _ _ ↦ Module.finrank K L) fun _ _ _ _ _ _ _ _ e ↦ e.toLinearEquiv.finrank_eq

/-- The degree of `mk K L` is `Module.finrank K L`. -/
@[simp]
theorem finrank_mk (L : Type v) [Field L] [Algebra K L] [Module.Finite K L] :
    (mk K L).finrank = Module.finrank K L := by
  obtain ⟨M, _, _, _, hM⟩ := exists_mk (mk K L)
  obtain ⟨e⟩ := (mk_eq_mk_iff L M).1 hM
  rw [hM, finrank, lift_mk, e.toLinearEquiv.finrank_eq]

/-- Every finite extension class has positive degree. -/
theorem finrank_pos (c : FiniteExtensionClass K) : 0 < c.finrank :=
  c.induction_on fun L _ _ _ ↦ by rw [finrank_mk]; exact Module.finrank_pos

/-- The degree of a finite extension class is nonzero. -/
@[simp]
theorem finrank_ne_zero (c : FiniteExtensionClass K) : c.finrank ≠ 0 :=
  c.finrank_pos.ne'

/-- The trivial extension class `self K` has degree `1`. -/
@[simp]
theorem finrank_self : (self K).finrank = 1 := by
  rw [self, finrank_mk, Module.finrank_self]

/-- A finite extension class has degree `1` if and only if it is the trivial class `self K`. -/
@[simp]
theorem finrank_eq_one_iff {c : FiniteExtensionClass K} :
    c.finrank = 1 ↔ c = self K := by
  induction c using induction_on_intermediateField with | h M =>
  rw [finrank_mk, IntermediateField.finrank_eq_one_iff, self, mk_eq_mk_iff]
  refine ⟨fun h ↦ ⟨h ▸ IntermediateField.botEquiv K (AlgebraicClosure K)⟩, fun ⟨e⟩ ↦ ?_⟩
  exact IntermediateField.finrank_eq_one_iff.1
    (e.toLinearEquiv.finrank_eq.trans (Module.finrank_self K))

/-- Whether a finite extension class `[L]` is separable over `K`. -/
def IsSeparable (c : FiniteExtensionClass K) : Prop :=
  c.lift (fun L _ _ _ ↦ Algebra.IsSeparable K L) fun _ _ _ _ _ _ _ _ e ↦
    propext (AlgEquiv.Algebra.isSeparable_iff e)

/-- `mk K L` is separable if and only if `L/K` is separable. -/
@[simp]
theorem isSeparable_mk_iff (L : Type v) [Field L] [Algebra K L] [Module.Finite K L] :
    (mk K L).IsSeparable ↔ Algebra.IsSeparable K L := by
  obtain ⟨M, _, _, _, hM⟩ := exists_mk (mk K L)
  obtain ⟨e⟩ := (mk_eq_mk_iff L M).1 hM
  rw [hM, IsSeparable, lift_mk]
  exact (AlgEquiv.Algebra.isSeparable_iff e).symm

/-- The trivial extension class `self K` is separable. -/
@[simp]
theorem isSeparable_self : (self K).IsSeparable := by
  rw [self, isSeparable_mk_iff]; infer_instance

/-- The cardinality `#Aut_K(L)` of the `K`-automorphism group of a representative `L` of `c`. -/
def natCardAut (c : FiniteExtensionClass K) : ℕ :=
  c.lift (fun L _ _ _ ↦ Nat.card (L ≃ₐ[K] L)) fun _ _ _ _ _ _ _ _ e ↦
    Nat.card_congr (AlgEquiv.autCongr e).toEquiv

/-- The automorphism count of `mk K L` is `Nat.card (L ≃ₐ[K] L)`. -/
@[simp]
theorem natCardAut_mk (L : Type v) [Field L] [Algebra K L] [Module.Finite K L] :
    (mk K L).natCardAut = Nat.card (L ≃ₐ[K] L) := by
  obtain ⟨M, _, _, _, hM⟩ := exists_mk (mk K L)
  obtain ⟨e⟩ := (mk_eq_mk_iff L M).1 hM
  rw [hM, natCardAut, lift_mk]
  exact Nat.card_congr (AlgEquiv.autCongr e.symm).toEquiv

/-- Every finite extension class has positive automorphism count. -/
theorem natCardAut_pos (c : FiniteExtensionClass K) : 0 < c.natCardAut :=
  c.induction_on fun L _ _ _ ↦ by rw [natCardAut_mk]; exact Nat.card_pos

/-- The automorphism count of a finite extension class is nonzero. -/
@[simp]
theorem natCardAut_ne_zero (c : FiniteExtensionClass K) : c.natCardAut ≠ 0 :=
  c.natCardAut_pos.ne'

/-- The trivial extension class `self K` has automorphism count `1`. -/
@[simp]
theorem natCardAut_self : (self K).natCardAut = 1 := by
  rw [self, natCardAut_mk, Nat.card_unique]

end Invariants

section RestrictScalars

variable (K : Type u) {F : Type v} [Field K] [Field F] [Algebra K F] [Module.Finite K F]

/-- Elimination principle for `FiniteExtensionClass F` over a finite base extension `F/K`: every
class is `mk F L` for a finite extension `L : Type v` equipped with the induced `K/F/L`
scalar-tower instances. -/
@[elab_as_elim]
theorem induction_on_tower {motive : FiniteExtensionClass F → Prop}
    (c : FiniteExtensionClass F)
    (h : ∀ (L : Type v) [Field L] [Algebra K L] [Algebra F L] [IsScalarTower K F L]
      [Module.Finite F L] [Module.Finite K L], motive (mk F L)) : motive c := by
  induction c using induction_on with | h L =>
  let : Algebra K L := RingHom.toAlgebra ((algebraMap F L).comp (algebraMap K F))
  have : IsScalarTower K F L := IsScalarTower.of_algebraMap_eq' rfl
  have : Module.Finite K L := Module.Finite.trans F L
  exact h L

/-- Restriction of scalars on finite extension classes: viewing a finite extension `L/F` as a
finite extension `L/K`. -/
def restrictScalars (c : FiniteExtensionClass F) : FiniteExtensionClass K :=
  c.lift
    (fun L _ _ _ ↦
      letI : Algebra K L := RingHom.toAlgebra ((algebraMap F L).comp (algebraMap K F))
      haveI : IsScalarTower K F L := IsScalarTower.of_algebraMap_eq' rfl
      haveI : Module.Finite K L := Module.Finite.trans F L
      mk K L)
    fun L₁ L₂ _ _ _ _ _ _ e ↦ by
      let : Algebra K L₁ := RingHom.toAlgebra ((algebraMap F L₁).comp (algebraMap K F))
      let : Algebra K L₂ := RingHom.toAlgebra ((algebraMap F L₂).comp (algebraMap K F))
      have : IsScalarTower K F L₁ := IsScalarTower.of_algebraMap_eq' rfl
      have : IsScalarTower K F L₂ := IsScalarTower.of_algebraMap_eq' rfl
      have : Module.Finite K L₁ := Module.Finite.trans F L₁
      have : Module.Finite K L₂ := Module.Finite.trans F L₂
      exact (mk_eq_mk_iff L₁ L₂).2 ⟨e.restrictScalars K⟩

/-- Restricting scalars of `mk F L` along a scalar tower `K/F/L` yields `mk K L`. -/
@[simp]
theorem restrictScalars_mk (L : Type w) [Field L] [Algebra K L] [Algebra F L]
    [IsScalarTower K F L] [Module.Finite F L] :
    haveI : Module.Finite K L := Module.Finite.trans F L
    (mk F L).restrictScalars K = mk K L := by
  obtain ⟨M, _, _, _, hM⟩ := exists_mk (mk F L)
  obtain ⟨e⟩ := (mk_eq_mk_iff L M).1 hM
  rw [hM, restrictScalars, lift_mk]
  let : Algebra K M := RingHom.toAlgebra ((algebraMap F M).comp (algebraMap K F))
  have : IsScalarTower K F M := IsScalarTower.of_algebraMap_eq' rfl
  have : Module.Finite K M := Module.Finite.trans F M
  have : Module.Finite K L := Module.Finite.trans F L
  exact (mk_eq_mk_iff M L).2 ⟨(e.restrictScalars K).symm⟩

/-- Restricting scalars of the trivial class `self F` down to `K` gives `mk K F`. -/
@[simp]
theorem restrictScalars_self : (self F).restrictScalars K = mk K F :=
  restrictScalars_mk K F

/-- **Multiplicativity of degree under restriction of scalars.** -/
@[simp]
theorem finrank_restrictScalars (c : FiniteExtensionClass F) :
    (c.restrictScalars K).finrank = Module.finrank K F * c.finrank :=
  induction_on_tower K c fun L _ _ _ _ _ _ ↦ by
    rw [restrictScalars_mk (F := F) K L, finrank_mk, finrank_mk, Module.finrank_mul_finrank K F L]

/-- **Tower law for separability of finite extension classes.** `c.restrictScalars K` is separable
over `K` if and only if both `F/K` and `c` are separable. -/
theorem isSeparable_restrictScalars_iff (c : FiniteExtensionClass F) :
    (c.restrictScalars K).IsSeparable ↔ Algebra.IsSeparable K F ∧ c.IsSeparable :=
  induction_on_tower K c fun L _ _ _ _ _ _ ↦ by
    rw [restrictScalars_mk (F := F) K L, isSeparable_mk_iff, isSeparable_mk_iff]
    exact ⟨fun _ ↦ ⟨Algebra.isSeparable_tower_bot_of_isSeparable K F L,
        Algebra.isSeparable_tower_top_of_isSeparable K F L⟩,
      fun ⟨_, _⟩ ↦ Algebra.IsSeparable.trans K F L⟩

end RestrictScalars

section Transport

variable {F₁ : Type u} {F₂ : Type v} [Field F₁] [Field F₂]

/-- Auxiliary pushforward of finite extension classes along a ring isomorphism `e : F₁ ≃+* F₂`. -/
private def mapAux (e : F₁ ≃+* F₂) (c : FiniteExtensionClass F₁) : FiniteExtensionClass F₂ :=
  c.lift
    (fun L _ _ _ ↦
      letI : Algebra F₂ L := Algebra.compHom L e.symm.toRingHom
      haveI : Module.Finite F₂ L := .compHom_of_surjective e.symm.toRingHom e.symm.surjective
      mk F₂ L)
    fun L₁ L₂ _ _ _ _ _ _ eL ↦ by
      let : Algebra F₂ L₁ := Algebra.compHom L₁ e.symm.toRingHom
      let : Algebra F₂ L₂ := Algebra.compHom L₂ e.symm.toRingHom
      have : Module.Finite F₂ L₁ := .compHom_of_surjective e.symm.toRingHom e.symm.surjective
      have : Module.Finite F₂ L₂ := .compHom_of_surjective e.symm.toRingHom e.symm.surjective
      exact (mk_eq_mk_iff L₁ L₂).2
        ⟨AlgEquiv.ofRingEquiv (f := eL.toRingEquiv) fun b ↦ by
          simp [Algebra.compHom_algebraMap_apply, eL.commutes]⟩

private theorem mapAux_mk_eq_mk_iff (e : F₁ ≃+* F₂)
    {L₁ L₂ : Type*} [Field L₁] [Algebra F₁ L₁] [Module.Finite F₁ L₁]
    [Field L₂] [Algebra F₂ L₂] [Module.Finite F₂ L₂] :
    mapAux e (mk F₁ L₁) = mk F₂ L₂ ↔
      ∃ φ : L₁ ≃+* L₂, ∀ a : F₁, φ (algebraMap F₁ L₁ a) = algebraMap F₂ L₂ (e a) := by
  obtain ⟨M₁, _, _, _, hM₁⟩ := exists_mk (mk F₁ L₁)
  obtain ⟨α⟩ := (mk_eq_mk_iff L₁ M₁).1 hM₁
  rw [hM₁, mapAux, lift_mk]
  let : Algebra F₂ M₁ := Algebra.compHom M₁ e.symm.toRingHom
  have : Module.Finite F₂ M₁ := .compHom_of_surjective e.symm.toRingHom e.symm.surjective
  rw [mk_eq_mk_iff]
  constructor
  · rintro ⟨β⟩
    refine ⟨α.toRingEquiv.trans β.toRingEquiv, fun a ↦ ?_⟩
    simp only [RingEquiv.trans_apply, AlgEquiv.coe_toRingEquiv]
    calc β (α (algebraMap F₁ L₁ a))
        = β (algebraMap F₂ M₁ (e a)) := by simp [Algebra.compHom_algebraMap_apply, α.commutes]
      _ = algebraMap F₂ L₂ (e a) := β.commutes (e a)
  · rintro ⟨φ, hφ⟩
    refine ⟨AlgEquiv.ofRingEquiv (f := α.symm.toRingEquiv.trans φ) fun b ↦ ?_⟩
    simp [Algebra.compHom_algebraMap_apply, hφ]

private theorem mapAux_refl {F : Type u} [Field F] (c : FiniteExtensionClass F) :
    mapAux (RingEquiv.refl F) c = c := by
  induction c using induction_on with | h L =>
  exact (mapAux_mk_eq_mk_iff (RingEquiv.refl F)).2 ⟨RingEquiv.refl L, fun _ ↦ by simp⟩

private theorem mapAux_trans {F₃ : Type w} [Field F₃] (e₁ : F₁ ≃+* F₂) (e₂ : F₂ ≃+* F₃)
    (c : FiniteExtensionClass F₁) :
    mapAux (e₁.trans e₂) c = mapAux e₂ (mapAux e₁ c) := by
  induction c using induction_on with | h L₁ =>
  obtain ⟨L₂, _, _, _, hL₂⟩ := exists_mk (mapAux e₁ (mk F₁ L₁))
  obtain ⟨L₃, _, _, _, hL₃⟩ := exists_mk (mapAux e₂ (mk F₂ L₂))
  obtain ⟨φ₁, hφ₁⟩ := (mapAux_mk_eq_mk_iff e₁).1 hL₂
  obtain ⟨φ₂, hφ₂⟩ := (mapAux_mk_eq_mk_iff e₂).1 hL₃
  rw [hL₂, hL₃]
  exact (mapAux_mk_eq_mk_iff (e₁.trans e₂)).2 ⟨φ₁.trans φ₂, fun a ↦ by simp [hφ₁, hφ₂]⟩

/-- **Transport of structure on finite extension classes.** A ring isomorphism `e : F₁ ≃+* F₂` of
base fields induces a bijection between their finite extension classes, sending `[L₁]` to the
`F₂`-class of `L₁` with `F₂` acting through `e⁻¹`. -/
def mapEquiv (e : F₁ ≃+* F₂) : FiniteExtensionClass F₁ ≃ FiniteExtensionClass F₂ where
  toFun := mapAux e
  invFun := mapAux e.symm
  left_inv c := by rw [← mapAux_trans, e.self_trans_symm, mapAux_refl]
  right_inv c := by rw [← mapAux_trans, e.symm_trans_self, mapAux_refl]

/-- **Characterization of `mapEquiv` on classes.** `mapEquiv e (mk F₁ L₁) = mk F₂ L₂` if and only
if there is a ring isomorphism `L₁ ≃+* L₂` intertwining `algebraMap` with `e`. -/
theorem mapEquiv_mk_eq_mk_iff (e : F₁ ≃+* F₂)
    {L₁ L₂ : Type*} [Field L₁] [Algebra F₁ L₁] [Module.Finite F₁ L₁]
    [Field L₂] [Algebra F₂ L₂] [Module.Finite F₂ L₂] :
    mapEquiv e (mk F₁ L₁) = mk F₂ L₂ ↔
      ∃ φ : L₁ ≃+* L₂, ∀ a : F₁, φ (algebraMap F₁ L₁ a) = algebraMap F₂ L₂ (e a) :=
  mapAux_mk_eq_mk_iff e

/-- Transport along the identity ring equivalence is the identity on `FiniteExtensionClass F`. -/
@[simp]
theorem mapEquiv_refl {F : Type u} [Field F] :
    mapEquiv (RingEquiv.refl F) = Equiv.refl (FiniteExtensionClass F) :=
  Equiv.ext mapAux_refl

/-- The inverse of `mapEquiv e` is `mapEquiv e.symm`. -/
@[simp]
theorem mapEquiv_symm (e : F₁ ≃+* F₂) : (mapEquiv e).symm = mapEquiv e.symm := (rfl)

/-- Transport of finite extension classes is functorial under composition of ring equivalences. -/
theorem mapEquiv_trans {F₃ : Type w} [Field F₃] (e₁ : F₁ ≃+* F₂) (e₂ : F₂ ≃+* F₃) :
    mapEquiv (e₁.trans e₂) = (mapEquiv e₁).trans (mapEquiv e₂) :=
  Equiv.ext (mapAux_trans e₁ e₂)

/-- Transport along `e : F₁ ≃+* F₂` sends the trivial class `self F₁` to `self F₂`. -/
@[simp]
theorem mapEquiv_self (e : F₁ ≃+* F₂) : mapEquiv e (self F₁) = self F₂ :=
  (mapEquiv_mk_eq_mk_iff e).2 ⟨e, fun _ ↦ by simp⟩

/-- Transport of structure along a ring equivalence preserves extension degree. -/
@[simp]
theorem finrank_mapEquiv (e : F₁ ≃+* F₂) (c : FiniteExtensionClass F₁) :
    (mapEquiv e c).finrank = c.finrank := by
  induction c using induction_on with | h L₁ =>
  obtain ⟨L₂, _, _, _, hL₂⟩ := exists_mk (mapEquiv e (mk F₁ L₁))
  obtain ⟨φ, hφ⟩ := (mapEquiv_mk_eq_mk_iff e).1 hL₂
  rw [hL₂, finrank_mk, finrank_mk]
  exact (Algebra.finrank_eq_of_equiv_equiv e φ (RingHom.ext fun a ↦ (hφ a).symm)).symm

/-- Transport of structure along a ring equivalence preserves and reflects separability. -/
@[simp]
theorem isSeparable_mapEquiv_iff (e : F₁ ≃+* F₂) (c : FiniteExtensionClass F₁) :
    (mapEquiv e c).IsSeparable ↔ c.IsSeparable := by
  induction c using induction_on with | h L₁ =>
  obtain ⟨L₂, _, _, _, hL₂⟩ := exists_mk (mapEquiv e (mk F₁ L₁))
  obtain ⟨φ, hφ⟩ := (mapEquiv_mk_eq_mk_iff e).1 hL₂
  rw [hL₂, isSeparable_mk_iff, isSeparable_mk_iff]
  exact (Algebra.IsSeparable.iff_of_equiv_equiv e φ (RingHom.ext fun a ↦ (hφ a).symm)).symm

/-- Transport of structure along a ring equivalence preserves the automorphism count. -/
@[simp]
theorem natCardAut_mapEquiv (e : F₁ ≃+* F₂) (c : FiniteExtensionClass F₁) :
    (mapEquiv e c).natCardAut = c.natCardAut := by
  induction c using induction_on with | h L₁ =>
  obtain ⟨L₂, _, _, _, hL₂⟩ := exists_mk (mapEquiv e (mk F₁ L₁))
  obtain ⟨φ, hφ⟩ := (mapEquiv_mk_eq_mk_iff e).1 hL₂
  rw [hL₂, natCardAut_mk, natCardAut_mk]
  exact (Nat.card_congr (e.algAutCongr φ hφ).toEquiv).symm

end Transport

section MulAction

variable {R : Type*} {F : Type u} [CommSemiring R] [Field F] [Algebra R F]

/-- Left action of `F ≃ₐ[R] F` on `FiniteExtensionClass F` by transport of structure: `τ • [L]` is
`mapEquiv (τ : F ≃+* F) [L]`, the `F`-isomorphism class of `L` with `F` acting through `τ⁻¹`. -/
instance instMulActionAlgEquiv : MulAction (F ≃ₐ[R] F) (FiniteExtensionClass F) where
  smul τ c := mapEquiv (τ : F ≃+* F) c
  one_smul c := by
    dsimp only [HSMul.hSMul]
    rw [AlgEquiv.toRingEquiv_one, mapEquiv_refl, Equiv.refl_apply]
  mul_smul τ₁ τ₂ c := by
    dsimp only [HSMul.hSMul]
    rw [AlgEquiv.toRingEquiv_mul, mapEquiv_trans, Equiv.trans_apply]

/-- The action of `τ : F ≃ₐ[R] F` on `FiniteExtensionClass F` is `mapEquiv (τ : F ≃+* F)`. -/
theorem smul_def (τ : F ≃ₐ[R] F) (c : FiniteExtensionClass F) :
    τ • c = mapEquiv (τ : F ≃+* F) c := (rfl)

/-- Every `R`-algebra automorphism of `F` fixes the trivial class `self F`. -/
@[simp]
theorem smul_self (τ : F ≃ₐ[R] F) : τ • self F = self F := mapEquiv_self _

/-- The action of `F ≃ₐ[R] F` preserves extension degree. -/
@[simp]
theorem finrank_smul (τ : F ≃ₐ[R] F) (c : FiniteExtensionClass F) :
    (τ • c).finrank = c.finrank := finrank_mapEquiv _ c

/-- The action of `F ≃ₐ[R] F` preserves and reflects separability. -/
@[simp]
theorem isSeparable_smul_iff (τ : F ≃ₐ[R] F) (c : FiniteExtensionClass F) :
    (τ • c).IsSeparable ↔ c.IsSeparable := isSeparable_mapEquiv_iff _ c

/-- The action of `F ≃ₐ[R] F` preserves the automorphism count. -/
@[simp]
theorem natCardAut_smul (τ : F ≃ₐ[R] F) (c : FiniteExtensionClass F) :
    (τ • c).natCardAut = c.natCardAut := natCardAut_mapEquiv _ c

/-- Over an `R`-algebra `F`, `τ • mk F L₁ = mk F L₂` if and only if there is an `R`-algebra
isomorphism `L₁ ≃ₐ[R] L₂` intertwining the `F`-actions via `τ`. -/
theorem smul_mk_eq_mk_iff (τ : F ≃ₐ[R] F) {L₁ L₂ : Type*}
    [Field L₁] [Algebra R L₁] [Algebra F L₁] [IsScalarTower R F L₁] [Module.Finite F L₁]
    [Field L₂] [Algebra R L₂] [Algebra F L₂] [IsScalarTower R F L₂] [Module.Finite F L₂] :
    τ • mk F L₁ = mk F L₂ ↔
      ∃ e : L₁ ≃ₐ[R] L₂, ∀ a : F, e (algebraMap F L₁ a) = algebraMap F L₂ (τ a) := by
  rw [smul_def, mapEquiv_mk_eq_mk_iff]
  refine ⟨fun ⟨φ, hφ⟩ ↦ ⟨AlgEquiv.ofRingEquiv (f := φ) fun r ↦ ?_, hφ⟩,
    fun ⟨e, he⟩ ↦ ⟨e.toRingEquiv, he⟩⟩
  rw [IsScalarTower.algebraMap_apply R F L₁, hφ, AlgEquiv.coe_toRingEquiv, τ.commutes,
    ← IsScalarTower.algebraMap_apply R F L₂]

/-- **Stabilizer characterization.** An automorphism `τ : F ≃ₐ[R] F` fixes `mk F L` if and only if
it extends to an `R`-algebra automorphism of `L`. -/
theorem mem_stabilizer_mk_iff (τ : F ≃ₐ[R] F) {L : Type*}
    [Field L] [Algebra R L] [Algebra F L] [IsScalarTower R F L] [Module.Finite F L] :
    τ ∈ MulAction.stabilizer (F ≃ₐ[R] F) (mk F L) ↔
      ∃ σ : L ≃ₐ[R] L, ∀ a : F, σ (algebraMap F L a) = algebraMap F L (τ a) :=
  MulAction.mem_stabilizer_iff.trans (smul_mk_eq_mk_iff τ)

end MulAction

section NormalTower

variable {K : Type u} {F : Type v} [Field K] [Field F] [Algebra K F]

/-- Transport of structure by `Gal(F/K)` preserves the underlying `K`-isomorphism class. -/
@[simp]
theorem restrictScalars_smul [Module.Finite K F] (τ : F ≃ₐ[K] F) (c : FiniteExtensionClass F) :
    (τ • c).restrictScalars K = c.restrictScalars K := by
  generalize hc : τ • c = c'
  revert hc
  refine induction_on_tower K c fun L₁ _ _ _ _ _ _ ↦
    induction_on_tower K c' fun L₂ _ _ _ _ _ _ hc ↦ ?_
  obtain ⟨e, -⟩ := (smul_mk_eq_mk_iff τ).1 hc
  rw [restrictScalars_mk (F := F) K L₂, restrictScalars_mk (F := F) K L₁]
  exact (mk_eq_mk_iff L₂ L₁).2 ⟨e.symm⟩

/-- **Orbit characterization of `restrictScalars` over a normal intermediate field.** When `F/K` is
finite and normal, two finite extension classes of `F` induce the same `K`-extension class if and
only if they lie in the same `(F ≃ₐ[K] F)`-orbit. -/
theorem restrictScalars_eq_restrictScalars_iff [Module.Finite K F] [Normal K F]
    (c₁ c₂ : FiniteExtensionClass F) :
    c₁.restrictScalars K = c₂.restrictScalars K ↔ ∃ τ : F ≃ₐ[K] F, τ • c₁ = c₂ :=
  induction_on_tower K c₁ fun L₁ _ _ _ _ _ _ ↦
    induction_on_tower K c₂ fun L₂ _ _ _ _ _ _ ↦ by
      refine ⟨fun h ↦ ?_, fun ⟨τ, hτ⟩ ↦ by rw [← hτ, restrictScalars_smul]⟩
      rw [restrictScalars_mk (F := F) K L₁, restrictScalars_mk (F := F) K L₂, mk_eq_mk_iff] at h
      obtain ⟨φ⟩ := h
      obtain ⟨τ, hτ⟩ := AlgHom.exists_comp_eq_of_normal (IsScalarTower.toAlgHom K F L₂)
        (φ.toAlgHom.comp (IsScalarTower.toAlgHom K F L₁))
      exact ⟨τ, (smul_mk_eq_mk_iff τ).2 ⟨φ, fun a ↦ (AlgHom.congr_fun hτ a).symm⟩⟩

/-- **Image of restriction to a normal intermediate field.** When `F/K` is normal and `L/F` is
finite, the image of `AlgEquiv.restrictNormalHom F : (L ≃ₐ[K] L) →* (F ≃ₐ[K] F)` is the stabilizer
of `mk F L` in `F ≃ₐ[K] F`. -/
theorem range_restrictNormalHom_eq_stabilizer_mk (K : Type u) (F : Type v) (L : Type w)
    [Field K] [Field F] [Algebra K F] [Normal K F] [Field L]
    [Algebra K L] [Algebra F L] [IsScalarTower K F L] [Module.Finite F L] :
    (AlgEquiv.restrictNormalHom (F := K) (K₁ := L) F).range =
      MulAction.stabilizer (F ≃ₐ[K] F) (mk F L) := by
  ext τ
  rw [MonoidHom.mem_range, mem_stabilizer_mk_iff]
  refine exists_congr fun σ ↦ ?_
  rw [← AlgHom.restrictNormalHom_toAlgHom (F := K) (M := F) (K := L),
    AlgHom.restrictNormalHom_eq_iff]
  simp only [IsScalarTower.toAlgHom_apply]

/-- **Automorphism count in a tower with normal bottom step.** When `F/K` is normal and `L/F` is
finite, `#Aut_K(L) = #Aut_F(L) · #Stab_{Gal(F/K)}([L])`. -/
theorem natCard_algEquiv_eq_mul_natCard_stabilizer_mk (K : Type u) (F : Type v) (L : Type w)
    [Field K] [Field F] [Algebra K F] [Normal K F] [Field L]
    [Algebra K L] [Algebra F L] [IsScalarTower K F L] [Module.Finite F L] :
    Nat.card (L ≃ₐ[K] L) =
      Nat.card (L ≃ₐ[F] L) * Nat.card (MulAction.stabilizer (F ≃ₐ[K] F) (mk F L)) := by
  rw [← Subgroup.card_ker_mul_card_range (AlgEquiv.restrictNormalHom (F := K) (K₁ := L) F),
    ← AlgEquiv.range_restrictScalarsHom_eq_ker_restrictNormalHom K F L,
    range_restrictNormalHom_eq_stabilizer_mk K F L,
    Nat.card_congr (MonoidHom.ofInjective (AlgEquiv.restrictScalarsHom_injective K)).toEquiv]

/-- **Class-level automorphism count for restriction of scalars.** When `F/K` is finite and normal,
the automorphism count of `c.restrictScalars K` is `c.natCardAut` times the size of the stabilizer
of `c` in `F ≃ₐ[K] F`. -/
theorem natCardAut_restrictScalars [Module.Finite K F] [Normal K F]
    (c : FiniteExtensionClass F) :
    (c.restrictScalars K).natCardAut =
      c.natCardAut * Nat.card (MulAction.stabilizer (F ≃ₐ[K] F) c) :=
  induction_on_tower K c fun L _ _ _ _ _ _ ↦ by
    rw [restrictScalars_mk (F := F) K L, natCardAut_mk, natCardAut_mk,
      natCard_algEquiv_eq_mul_natCard_stabilizer_mk K F L]

end NormalTower

end FiniteExtensionClass

end TauCeti
