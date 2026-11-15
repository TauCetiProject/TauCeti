/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.LocalField.FiniteExtension.Class
public import TauCeti.NumberTheory.LocalField.MassFormula.Representative
import Mathlib.FieldTheory.IsSepClosed
import TauCeti.GroupTheory.GroupAction.Orbit.ENNReal
import TauCeti.NumberTheory.LocalField.Unramified.Factorization
import TauCeti.NumberTheory.LocalField.Unramified.Reduction

/-!
# Classification of finite local-field extensions by their unramified part

Every finite extension `L/K` of a nonarchimedean local field `K` of degree `n` has a unique maximal
unramified subextension `L₀/K`, of degree `f = f(L/K)` dividing `n`, over which `L` is totally
ramified of degree `e = n / f`. Up to `K`-isomorphism, `L₀` is the unique unramified extension `F`
of `K` of degree `f`.

Fix an unramified extension `F/K` (writing `f = [F : K]`) and a degree `e : ℕ`, and let
`TotallyRamifiedClass F e` be the type of `F`-isomorphism classes of totally ramified extensions of
`F` of degree `e`. Transport of structure gives a left action of `F ≃ₐ[K] F` on
`TotallyRamifiedClass F e`, and forgetting the `F`-algebra structure down to `K` sends a class `x`
to `x.restrictScalars K : FiniteExtensionClass K`.

This file proves that `restrictScalars K` descends to a bijection from the Galois orbit space
`MulAction.orbitRel.Quotient (F ≃ₐ[K] F) (TotallyRamifiedClass F e)` onto the `K`-isomorphism
classes of extensions of `K` of degree `f * e` and residue degree `f`, and establishes the
accompanying stabilizer, orbit-size, automorphism-count, and `ℝ≥0∞` weighted class-sum identities:

* for `x : TotallyRamifiedClass F e`, `#Orb(x) · #Stab(x) = [F : K]` and
  `#Aut_K(x.restrictScalars K) = #Aut_F(x) · #Stab(x)`;
* consequently, summing `w(c) / #Aut_K(c)` over the `K`-isomorphism classes of degree `f * e` and
  residue degree `f` gives `[F : K]⁻¹ · ∑' x : TotallyRamifiedClass F e, w(x.restrictScalars K) /
  #Aut_F(x)`.

Separability is preserved and reflected by `restrictScalars K` over an unramified base, so the
same classification restricts to separable extension classes, where `{x : TotallyRamifiedClass F e
// x.IsSeparable}` is canonically equivalent to any `IsRepresentativeSet e R` inside
`totallyRamifiedOfDegree F e`.

## Main definitions

* `TauCeti.TotallyRamifiedClass F e`: `F`-isomorphism classes of totally ramified extensions of a
  nonarchimedean local field `F` of degree `e`.
* `TauCeti.TotallyRamifiedClass.ofExtension`: class of an explicit totally ramified extension `L/F`
  of degree `e`.
* `TauCeti.TotallyRamifiedClass.ofTotallyRamifiedOfDegree`: canonical surjection from
  `totallyRamifiedOfDegree F e` onto `{x : TotallyRamifiedClass F e // x.IsSeparable}`.
* `TauCeti.IsRepresentativeSet.equivSeparableTotallyRamifiedClass`: canonical equivalence between a
  set of representatives `R` of `σ_F(e)` and `{x : TotallyRamifiedClass F e // x.IsSeparable}`.
* `TauCeti.TotallyRamifiedClass.restrictScalars`: restriction of scalars from `F` to `K`.
* `TauCeti.totallyRamifiedOrbitEquiv` and `TauCeti.totallyRamifiedOrbitEquivOfDvd`: the orbit-space
  classification of `K`-extension classes of fixed degree and residue degree.
* `TauCeti.separableTotallyRamifiedOrbitEquiv` and
  `TauCeti.separableTotallyRamifiedOrbitEquivOfDvd`: the separable restriction of the orbit-space
  classification.
* `TauCeti.extensionClassFinrankEquivSigma` and
  `TauCeti.separableExtensionClassFinrankEquivSigma`: decomposition of degree-`n` extension classes
  by their residue degree `f ∣ n`.

## Main results

* `TauCeti.TotallyRamifiedClass.restrictScalars_eq_restrictScalars_iff`: two totally ramified
  `F`-extension classes have the same underlying `K`-class if and only if they lie in the same
  `(F ≃ₐ[K] F)`-orbit.
* `TauCeti.exists_totallyRamifiedClass_restrictScalars_eq`: every `K`-extension class of degree
  `[F : K] * e` and residue degree `[F : K]` arises by restricting scalars from
  `TotallyRamifiedClass F e`.
* `TauCeti.TotallyRamifiedClass.natCard_orbit_mul_natCard_stabilizer` and
  `TauCeti.TotallyRamifiedClass.natCardAut_restrictScalars`: orbit-stabilizer and automorphism-count
  formulas in the unramified--totally ramified tower.
* `TauCeti.tsum_extensionClass_inertiaDegree_div_natCardAut` and
  `TauCeti.tsum_separable_extensionClass_inertiaDegree_div_natCardAut`: `ℝ≥0∞` weighted class-sum
  reductions from `K`-extension classes of residue degree `[F : K]` to `TotallyRamifiedClass F e`.

## References

* M. Bhargava, *Mass formulae for extensions of local fields, and conjectures on the density of
  number field discriminants*, IMRN **2007**, rnm052, §2.
* K. S. Kedlaya, *Mass formulas for local Galois representations*, IMRN **2007**, rnm021.
* [J.-P. Serre, *Corps Locaux*][serre1968], Chapter I, §4 and Chapter III, §5.
-/

public section

noncomputable section

open ValuativeRel
open scoped ENNReal

namespace TauCeti

universe u v w

/-- `TotallyRamifiedClass F e` is the type of `F`-algebra isomorphism classes of totally ramified
extensions of degree `e` of a nonarchimedean local field `F`. -/
@[ext]
structure TotallyRamifiedClass (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] (e : ℕ) : Type u where
  /-- The underlying `F`-isomorphism class of finite field extensions. -/
  toExtensionClass : FiniteExtensionClass F
  /-- The extension has degree `e` over `F`. -/
  finrank_eq : toExtensionClass.finrank = e
  /-- The extension is totally ramified over `F`. -/
  isTotallyRamified : toExtensionClass.IsTotallyRamified

namespace TotallyRamifiedClass

section Basic

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F] {e : ℕ}

theorem toExtensionClass_injective :
    Function.Injective (toExtensionClass (F := F) (e := e)) :=
  fun _ _ ↦ TotallyRamifiedClass.ext

@[simp]
theorem inertiaDegree_toExtensionClass (x : TotallyRamifiedClass F e) :
    x.toExtensionClass.inertiaDegree = 1 :=
  FiniteExtensionClass.isTotallyRamified_iff_inertiaDegree_eq_one.1 x.isTotallyRamified

@[simp]
theorem ramificationIndex_toExtensionClass (x : TotallyRamifiedClass F e) :
    x.toExtensionClass.ramificationIndex = e :=
  (FiniteExtensionClass.isTotallyRamified_iff_ramificationIndex_eq_finrank.1
    x.isTotallyRamified).trans x.finrank_eq

theorem pos (x : TotallyRamifiedClass F e) : 0 < e :=
  x.finrank_eq ▸ x.toExtensionClass.finrank_pos

theorem ne_zero (x : TotallyRamifiedClass F e) : e ≠ 0 :=
  x.pos.ne'

instance isEmpty_zero : IsEmpty (TotallyRamifiedClass F 0) :=
  ⟨fun x ↦ x.ne_zero rfl⟩

/-- The trivial totally ramified class of degree `1`, represented by `F` itself. -/
def self (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] : TotallyRamifiedClass F 1 :=
  ⟨FiniteExtensionClass.self F, FiniteExtensionClass.finrank_self,
    FiniteExtensionClass.isTotallyRamified_self⟩

@[simp]
theorem toExtensionClass_self : (self F).toExtensionClass = FiniteExtensionClass.self F :=
  (rfl)

instance instUniqueOne : Unique (TotallyRamifiedClass F 1) where
  default := self F
  uniq x := TotallyRamifiedClass.ext
    ((FiniteExtensionClass.finrank_eq_one_iff.1 x.finrank_eq).trans toExtensionClass_self.symm)

/-- The `TotallyRamifiedClass F e` of an explicit compatible totally ramified extension `L/F` of
degree `e`. -/
def ofExtension (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] {e : ℕ} (L : Type v) [Field L] [ValuativeRel L]
    [TopologicalSpace L] [IsNonarchimedeanLocalField L] [Algebra F L] [ValuativeExtension F L]
    (he : Module.finrank F L = e) (hL : IsTotallyRamified F L) : TotallyRamifiedClass F e :=
  haveI : Module.Finite F L := finite_of_valuativeExtension F L
  ⟨FiniteExtensionClass.mk F L, (FiniteExtensionClass.finrank_mk L).trans he,
    (FiniteExtensionClass.isTotallyRamified_mk_iff L).2 hL⟩

@[simp]
theorem toExtensionClass_ofExtension (L : Type v) [Field L] [ValuativeRel L]
    [TopologicalSpace L] [IsNonarchimedeanLocalField L] [Algebra F L] [ValuativeExtension F L]
    [Module.Finite F L] (he : Module.finrank F L = e) (hL : IsTotallyRamified F L) :
    (ofExtension F L he hL).toExtensionClass = FiniteExtensionClass.mk F L :=
  (rfl)

theorem ofExtension_eq_ofExtension_iff (L₁ : Type v) (L₂ : Type w)
    [Field L₁] [ValuativeRel L₁] [TopologicalSpace L₁] [IsNonarchimedeanLocalField L₁]
    [Algebra F L₁] [ValuativeExtension F L₁]
    [Field L₂] [ValuativeRel L₂] [TopologicalSpace L₂] [IsNonarchimedeanLocalField L₂]
    [Algebra F L₂] [ValuativeExtension F L₂]
    (he₁ : Module.finrank F L₁ = e) (hL₁ : IsTotallyRamified F L₁)
    (he₂ : Module.finrank F L₂ = e) (hL₂ : IsTotallyRamified F L₂) :
    ofExtension F L₁ he₁ hL₁ = ofExtension F L₂ he₂ hL₂ ↔ Nonempty (L₁ ≃ₐ[F] L₂) := by
  have : Module.Finite F L₁ := finite_of_valuativeExtension F L₁
  have : Module.Finite F L₂ := finite_of_valuativeExtension F L₂
  rw [TotallyRamifiedClass.ext_iff, toExtensionClass_ofExtension, toExtensionClass_ofExtension,
    FiniteExtensionClass.mk_eq_mk_iff]

/-- Elimination principle for `TotallyRamifiedClass F e`: every class is `ofExtension F L he hL`
for a compatible totally ramified local-field extension `L : Type u` of degree `e`. -/
@[elab_as_elim]
theorem induction_on {motive : TotallyRamifiedClass F e → Prop} (x : TotallyRamifiedClass F e)
    (h : ∀ (L : Type u) [Field L] [ValuativeRel L] [TopologicalSpace L]
      [IsNonarchimedeanLocalField L] [Algebra F L] [ValuativeExtension F L] [Module.Finite F L]
      (he : Module.finrank F L = e) (hL : IsTotallyRamified F L),
      motive (ofExtension F L he hL)) :
    motive x := by
  obtain ⟨c, hc_deg, hc_tot⟩ := x
  induction c using FiniteExtensionClass.induction_on_localField with | h L =>
  rw [FiniteExtensionClass.finrank_mk] at hc_deg
  rw [FiniteExtensionClass.isTotallyRamified_mk_iff] at hc_tot
  exact h L hc_deg hc_tot

/-- A totally ramified extension class is separable over `F` when its underlying extension class is
separable. -/
def IsSeparable (x : TotallyRamifiedClass F e) : Prop :=
  x.toExtensionClass.IsSeparable

theorem isSeparable_def (x : TotallyRamifiedClass F e) :
    x.IsSeparable ↔ x.toExtensionClass.IsSeparable :=
  (Iff.rfl)

@[simp]
theorem isSeparable_ofExtension_iff (L : Type v) [Field L] [ValuativeRel L]
    [TopologicalSpace L] [IsNonarchimedeanLocalField L] [Algebra F L] [ValuativeExtension F L]
    (he : Module.finrank F L = e) (hL : IsTotallyRamified F L) :
    (ofExtension F L he hL).IsSeparable ↔ Algebra.IsSeparable F L := by
  have : Module.Finite F L := finite_of_valuativeExtension F L
  rw [isSeparable_def, toExtensionClass_ofExtension, FiniteExtensionClass.isSeparable_mk_iff]

/-- The cardinality `#Aut_F(L)` of the `F`-automorphism group of any representative of `x`. -/
def natCardAut (x : TotallyRamifiedClass F e) : ℕ :=
  x.toExtensionClass.natCardAut

theorem natCardAut_def (x : TotallyRamifiedClass F e) :
    x.natCardAut = x.toExtensionClass.natCardAut :=
  (rfl)

@[simp]
theorem natCardAut_ofExtension (L : Type v) [Field L] [ValuativeRel L]
    [TopologicalSpace L] [IsNonarchimedeanLocalField L] [Algebra F L] [ValuativeExtension F L]
    (he : Module.finrank F L = e) (hL : IsTotallyRamified F L) :
    (ofExtension F L he hL).natCardAut = Nat.card (L ≃ₐ[F] L) := by
  have : Module.Finite F L := finite_of_valuativeExtension F L
  rw [natCardAut_def, toExtensionClass_ofExtension, FiniteExtensionClass.natCardAut_mk]

theorem natCardAut_pos (x : TotallyRamifiedClass F e) : 0 < x.natCardAut :=
  x.toExtensionClass.natCardAut_pos

theorem natCardAut_ne_zero (x : TotallyRamifiedClass F e) : x.natCardAut ≠ 0 :=
  x.natCardAut_pos.ne'

end Basic

section SeparableClosure

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F] {e : ℕ}

/-- Canonical map sending a member `L` of `σ_F(e) = totallyRamifiedOfDegree F e` to its separable
totally ramified `F`-isomorphism class. -/
def ofTotallyRamifiedOfDegree (L : totallyRamifiedOfDegree F e) :
    {x : TotallyRamifiedClass F e // x.IsSeparable} :=
  let hL := mem_totallyRamifiedOfDegree_iff.1 L.2
  haveI : Module.Finite F L.1 := hL.2.finite
  letI : ValuativeRel L.1 := finiteIntermediateFieldValuativeRel F (SeparableClosure F) L.1
  letI : TopologicalSpace L.1 := finiteIntermediateFieldTopology F (SeparableClosure F) L.1
  haveI : IsNonarchimedeanLocalField L.1 :=
    finiteIntermediateField_isNonarchimedeanLocalField F (SeparableClosure F) L.1
  haveI : ValuativeExtension F L.1 :=
    finiteIntermediateField_valuativeExtension F (SeparableClosure F) L.1
  ⟨ofExtension F L.1 hL.1 ((L.1.isTotallyRamified_iff).1 hL.2),
    (isSeparable_ofExtension_iff L.1 hL.1 ((L.1.isTotallyRamified_iff).1 hL.2)).2
      (Algebra.isSeparable_tower_bot_of_isSeparable F L.1 (SeparableClosure F))⟩

@[simp]
theorem toExtensionClass_ofTotallyRamifiedOfDegree (L : totallyRamifiedOfDegree F e) :
    haveI : Module.Finite F L.1 := (mem_totallyRamifiedOfDegree_iff.1 L.2).2.finite
    (ofTotallyRamifiedOfDegree L).1.toExtensionClass = FiniteExtensionClass.mk F L.1 :=
  (rfl)

@[simp]
theorem natCardAut_ofTotallyRamifiedOfDegree (L : totallyRamifiedOfDegree F e) :
    (ofTotallyRamifiedOfDegree L).1.natCardAut = Nat.card (L.1 ≃ₐ[F] L.1) := by
  have : Module.Finite F L.1 := (mem_totallyRamifiedOfDegree_iff.1 L.2).2.finite
  rw [natCardAut_def, toExtensionClass_ofTotallyRamifiedOfDegree,
    FiniteExtensionClass.natCardAut_mk]

theorem ofTotallyRamifiedOfDegree_eq_iff (L M : totallyRamifiedOfDegree F e) :
    ofTotallyRamifiedOfDegree L = ofTotallyRamifiedOfDegree M ↔ Nonempty (L.1 ≃ₐ[F] M.1) := by
  have : Module.Finite F L.1 := (mem_totallyRamifiedOfDegree_iff.1 L.2).2.finite
  have : Module.Finite F M.1 := (mem_totallyRamifiedOfDegree_iff.1 M.2).2.finite
  rw [Subtype.ext_iff, TotallyRamifiedClass.ext_iff, toExtensionClass_ofTotallyRamifiedOfDegree,
    toExtensionClass_ofTotallyRamifiedOfDegree, FiniteExtensionClass.mk_eq_mk_iff]

theorem ofTotallyRamifiedOfDegree_surjective :
    Function.Surjective (ofTotallyRamifiedOfDegree (F := F) (e := e)) := by
  rintro ⟨x, hx⟩
  induction x using induction_on with | h L he hL =>
  have : Algebra.IsSeparable F L := (isSeparable_ofExtension_iff L he hL).1 hx
  let ι : L →ₐ[F] SeparableClosure F := IsSepClosed.lift
  let φ : L ≃ₐ[F] ι.fieldRange := AlgEquiv.ofInjectiveField ι
  have : Module.Finite F ι.fieldRange := Module.Finite.equiv φ.toLinearEquiv
  have hdeg : Module.finrank F ι.fieldRange = e := φ.toLinearEquiv.finrank_eq.symm.trans he
  have htot : ι.fieldRange.IsTotallyRamified := by
    rw [IntermediateField.isTotallyRamified_iff]
    let : ValuativeRel ι.fieldRange :=
      finiteIntermediateFieldValuativeRel F (SeparableClosure F) ι.fieldRange
    let : TopologicalSpace ι.fieldRange :=
      finiteIntermediateFieldTopology F (SeparableClosure F) ι.fieldRange
    have : IsNonarchimedeanLocalField ι.fieldRange :=
      finiteIntermediateField_isNonarchimedeanLocalField F (SeparableClosure F) ι.fieldRange
    have : ValuativeExtension F ι.fieldRange :=
      finiteIntermediateField_valuativeExtension F (SeparableClosure F) ι.fieldRange
    rw [isTotallyRamified_iff_inertiaDegree_eq_one, ← inertiaDegree_eq_of_algEquiv F L _ φ]
    exact hL.inertiaDegree_eq_one
  refine ⟨⟨ι.fieldRange, mem_totallyRamifiedOfDegree_iff.2 ⟨hdeg, htot⟩⟩, ?_⟩
  apply Subtype.ext
  apply TotallyRamifiedClass.ext
  rw [toExtensionClass_ofTotallyRamifiedOfDegree, toExtensionClass_ofExtension]
  exact (FiniteExtensionClass.mk_eq_mk_iff _ _).2 ⟨φ.symm⟩

end SeparableClosure

end TotallyRamifiedClass

/-- Any set of representatives `R` of the `F`-isomorphism classes in `σ_F(e)` is canonically
equivalent to the separable classes in `TotallyRamifiedClass F e`. -/
def IsRepresentativeSet.equivSeparableTotallyRamifiedClass {F : Type u} [Field F] [ValuativeRel F]
    [TopologicalSpace F] [IsNonarchimedeanLocalField F] {e : ℕ}
    {R : Set (IntermediateField F (SeparableClosure F))} (hR : IsRepresentativeSet e R) :
    R ≃ {x : TotallyRamifiedClass F e // x.IsSeparable} :=
  Equiv.ofBijective (fun M ↦ TotallyRamifiedClass.ofTotallyRamifiedOfDegree ⟨M.1, hR.subset M.2⟩)
    ⟨fun M₁ M₂ h ↦ by
      obtain ⟨e₁₂⟩ := (TotallyRamifiedClass.ofTotallyRamifiedOfDegree_eq_iff _ _).1 h
      obtain ⟨_, -, huniq⟩ := hR.existsUnique (hR.subset M₁.2)
      exact Subtype.ext ((huniq M₁.1 ⟨M₁.2, ⟨AlgEquiv.refl⟩⟩).trans
        (huniq M₂.1 ⟨M₂.2, ⟨e₁₂⟩⟩).symm),
      fun y ↦ by
      obtain ⟨L, rfl⟩ := TotallyRamifiedClass.ofTotallyRamifiedOfDegree_surjective y
      obtain ⟨M, ⟨hM, ⟨eLM⟩⟩, -⟩ := hR.existsUnique L.2
      exact ⟨⟨M, hM⟩,
        (TotallyRamifiedClass.ofTotallyRamifiedOfDegree_eq_iff ⟨M, hR.subset hM⟩ L).2
          ⟨eLM.symm⟩⟩⟩

@[simp]
theorem IsRepresentativeSet.equivSeparableTotallyRamifiedClass_apply {F : Type u} [Field F]
    [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] {e : ℕ}
    {R : Set (IntermediateField F (SeparableClosure F))} (hR : IsRepresentativeSet e R) (M : R) :
    hR.equivSeparableTotallyRamifiedClass M =
      TotallyRamifiedClass.ofTotallyRamifiedOfDegree ⟨M.1, hR.subset M.2⟩ :=
  (rfl)

namespace TotallyRamifiedClass

section ActionAndRestrictScalars

variable {K : Type u} {F : Type v}
  [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [Algebra K F] [ValuativeExtension K F] {e : ℕ}

/-- Transport of structure gives a left action of `F ≃ₐ[K] F` on `TotallyRamifiedClass F e`. -/
instance instMulActionAlgEquiv : MulAction (F ≃ₐ[K] F) (TotallyRamifiedClass F e) where
  smul τ x :=
    ⟨τ • x.toExtensionClass,
      (FiniteExtensionClass.finrank_smul τ x.toExtensionClass).trans x.finrank_eq,
      (FiniteExtensionClass.isTotallyRamified_smul_iff τ x.toExtensionClass).2 x.isTotallyRamified⟩
  one_smul x := TotallyRamifiedClass.ext (one_smul (F ≃ₐ[K] F) x.toExtensionClass)
  mul_smul τ₁ τ₂ x := TotallyRamifiedClass.ext (mul_smul τ₁ τ₂ x.toExtensionClass)

@[simp]
theorem toExtensionClass_smul (τ : F ≃ₐ[K] F) (x : TotallyRamifiedClass F e) :
    (τ • x).toExtensionClass = τ • x.toExtensionClass :=
  (rfl)

@[simp]
theorem isSeparable_smul_iff (τ : F ≃ₐ[K] F) (x : TotallyRamifiedClass F e) :
    (τ • x).IsSeparable ↔ x.IsSeparable := by
  rw [isSeparable_def, isSeparable_def, toExtensionClass_smul,
    FiniteExtensionClass.isSeparable_smul_iff]

@[simp]
theorem natCardAut_smul (τ : F ≃ₐ[K] F) (x : TotallyRamifiedClass F e) :
    (τ • x).natCardAut = x.natCardAut := by
  rw [natCardAut_def, natCardAut_def, toExtensionClass_smul, FiniteExtensionClass.natCardAut_smul]

theorem stabilizer_eq_stabilizer_toExtensionClass (x : TotallyRamifiedClass F e) :
    MulAction.stabilizer (F ≃ₐ[K] F) x =
      MulAction.stabilizer (F ≃ₐ[K] F) x.toExtensionClass := by
  ext τ
  simp [MulAction.mem_stabilizer_iff, TotallyRamifiedClass.ext_iff]

/-- Restriction of scalars sends a totally ramified `F`-extension class to its underlying
`K`-extension class. -/
def restrictScalars (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] [Algebra K F] [ValuativeExtension K F]
    (x : TotallyRamifiedClass F e) : FiniteExtensionClass K :=
  haveI : Module.Finite K F := finite_of_valuativeExtension K F
  x.toExtensionClass.restrictScalars K

theorem restrictScalars_def [Module.Finite K F] (x : TotallyRamifiedClass F e) :
    x.restrictScalars K = x.toExtensionClass.restrictScalars K :=
  (rfl)

@[simp]
theorem restrictScalars_ofExtension (L : Type w) [Field L] [ValuativeRel L]
    [TopologicalSpace L] [IsNonarchimedeanLocalField L] [Algebra K L] [Algebra F L]
    [IsScalarTower K F L] [ValuativeExtension F L] [Module.Finite K L]
    (he : Module.finrank F L = e) (hL : IsTotallyRamified F L) :
    (ofExtension F L he hL).restrictScalars K = FiniteExtensionClass.mk K L := by
  have : Module.Finite K F := finite_of_valuativeExtension K F
  have : Module.Finite F L := finite_of_valuativeExtension F L
  rw [restrictScalars_def, toExtensionClass_ofExtension,
    FiniteExtensionClass.restrictScalars_mk (F := F) K L]

@[simp]
theorem finrank_restrictScalars (x : TotallyRamifiedClass F e) :
    (x.restrictScalars K).finrank = Module.finrank K F * e := by
  have : Module.Finite K F := finite_of_valuativeExtension K F
  rw [restrictScalars_def, FiniteExtensionClass.finrank_restrictScalars, x.finrank_eq]

@[simp]
theorem restrictScalars_smul (τ : F ≃ₐ[K] F) (x : TotallyRamifiedClass F e) :
    (τ • x).restrictScalars K = x.restrictScalars K := by
  have : Module.Finite K F := finite_of_valuativeExtension K F
  rw [restrictScalars_def, restrictScalars_def, toExtensionClass_smul,
    FiniteExtensionClass.restrictScalars_smul]

/-- Transport of structure by `F ≃ₐ[K] F` restricts to the subtype of separable totally ramified
classes. -/
instance instMulActionSeparable :
    MulAction (F ≃ₐ[K] F) {x : TotallyRamifiedClass F e // x.IsSeparable} where
  smul τ x := ⟨τ • x.1, (isSeparable_smul_iff τ x.1).2 x.2⟩
  one_smul x := Subtype.ext (one_smul (F ≃ₐ[K] F) x.1)
  mul_smul τ₁ τ₂ x := Subtype.ext (mul_smul τ₁ τ₂ x.1)

@[simp]
theorem coe_smul_separable (τ : F ≃ₐ[K] F) (x : {x : TotallyRamifiedClass F e // x.IsSeparable}) :
    (τ • x).1 = τ • x.1 :=
  (rfl)

theorem stabilizer_separable_eq (x : {x : TotallyRamifiedClass F e // x.IsSeparable}) :
    MulAction.stabilizer (F ≃ₐ[K] F) x = MulAction.stabilizer (F ≃ₐ[K] F) x.1 := by
  ext τ
  simp [MulAction.mem_stabilizer_iff, Subtype.ext_iff]

end ActionAndRestrictScalars

section UnramifiedBase

variable {K : Type u} {F : Type v}
  [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [Algebra K F] [ValuativeExtension K F] [IsUnramified K F] {e : ℕ}

@[simp]
theorem inertiaDegree_restrictScalars (x : TotallyRamifiedClass F e) :
    (x.restrictScalars K).inertiaDegree = Module.finrank K F := by
  have : Module.Finite K F := finite_of_valuativeExtension K F
  rw [restrictScalars_def, FiniteExtensionClass.inertiaDegree_restrictScalars,
    x.inertiaDegree_toExtensionClass, mul_one, IsUnramified.inertiaDegree_eq_finrank]

@[simp]
theorem ramificationIndex_restrictScalars (x : TotallyRamifiedClass F e) :
    (x.restrictScalars K).ramificationIndex = e := by
  have : Module.Finite K F := finite_of_valuativeExtension K F
  rw [restrictScalars_def, FiniteExtensionClass.ramificationIndex_restrictScalars,
    IsUnramified.ramificationIndex_eq_one, one_mul, x.ramificationIndex_toExtensionClass]

@[simp]
theorem isSeparable_restrictScalars_iff (x : TotallyRamifiedClass F e) :
    (x.restrictScalars K).IsSeparable ↔ x.IsSeparable := by
  have : Module.Finite K F := finite_of_valuativeExtension K F
  have hG : IsGalois K F := IsUnramified.isGalois K F
  rw [restrictScalars_def, FiniteExtensionClass.isSeparable_restrictScalars_iff, isSeparable_def,
    and_iff_right hG.to_isSeparable]

/-- **Orbit characterization of `restrictScalars` over an unramified base.** Two totally ramified
`F`-extension classes induce the same `K`-extension class if and only if they lie in the same
`(F ≃ₐ[K] F)`-orbit. -/
theorem restrictScalars_eq_restrictScalars_iff (x y : TotallyRamifiedClass F e) :
    x.restrictScalars K = y.restrictScalars K ↔ ∃ τ : F ≃ₐ[K] F, τ • x = y := by
  have : Module.Finite K F := finite_of_valuativeExtension K F
  have := IsUnramified.isGalois K F
  rw [restrictScalars_def, restrictScalars_def,
    FiniteExtensionClass.restrictScalars_eq_restrictScalars_iff]
  simp [TotallyRamifiedClass.ext_iff]

/-- **Orbit-stabilizer identity for `TotallyRamifiedClass F e`.** For an unramified extension
`F/K`, the orbit size of `x` under `F ≃ₐ[K] F` times its stabilizer size equals `[F : K]`. -/
theorem natCard_orbit_mul_natCard_stabilizer (x : TotallyRamifiedClass F e) :
    Nat.card (MulAction.orbit (F ≃ₐ[K] F) x) *
      Nat.card (MulAction.stabilizer (F ≃ₐ[K] F) x) = Module.finrank K F := by
  have : FiniteDimensional K F := finite_of_valuativeExtension K F
  have := IsUnramified.isGalois K F
  rw [← Nat.card_prod, Nat.card_congr (MulAction.orbitProdStabilizerEquivGroup (F ≃ₐ[K] F) x),
    IsGalois.card_aut_eq_finrank K F]

/-- **Automorphism count in the unramified--totally ramified tower.** For `x : TotallyRamifiedClass
F e` over an unramified extension `F/K`, `#Aut_K(x.restrictScalars K) = #Aut_F(x) · #Stab(x)`. -/
theorem natCardAut_restrictScalars (x : TotallyRamifiedClass F e) :
    (x.restrictScalars K).natCardAut =
      x.natCardAut * Nat.card (MulAction.stabilizer (F ≃ₐ[K] F) x) := by
  have : Module.Finite K F := finite_of_valuativeExtension K F
  have := IsUnramified.isGalois K F
  rw [restrictScalars_def, FiniteExtensionClass.natCardAut_restrictScalars, natCardAut_def,
    stabilizer_eq_stabilizer_toExtensionClass]

end UnramifiedBase

end TotallyRamifiedClass

section Classification

variable (K : Type u) (F : Type v)
  [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [Algebra K F] [ValuativeExtension K F] [IsUnramified K F]

/-- **Surjectivity of `TotallyRamifiedClass.restrictScalars`.** Every `K`-extension class `c` of
degree `[F : K] * e` and residue degree `[F : K]` is `x.restrictScalars K` for some
`x : TotallyRamifiedClass F e`. -/
theorem exists_totallyRamifiedClass_restrictScalars_eq {e : ℕ} {c : FiniteExtensionClass K}
    (hdeg : c.finrank = Module.finrank K F * e)
    (hinert : c.inertiaDegree = Module.finrank K F) :
    ∃ x : TotallyRamifiedClass F e, x.restrictScalars K = c := by
  induction c using FiniteExtensionClass.induction_on_localField with | h L =>
  rw [FiniteExtensionClass.finrank_mk] at hdeg
  rw [FiniteExtensionClass.inertiaDegree_mk] at hinert
  let L₀ : IntermediateField K L := unramifiedExtension K L (inertiaDegree K L)
  let : ValuativeRel L₀ := finiteIntermediateFieldValuativeRel K L L₀
  let : TopologicalSpace L₀ := finiteIntermediateFieldTopology K L L₀
  have : IsNonarchimedeanLocalField L₀ :=
    finiteIntermediateField_isNonarchimedeanLocalField K L L₀
  have : ValuativeExtension K L₀ := finiteIntermediateField_valuativeExtension K L L₀
  have : IsUnramified K L₀ := isUnramified_unramifiedExtension_inertiaDegree K L
  obtain ⟨ψ⟩ : Nonempty (F ≃ₐ[K] L₀) :=
    IsUnramified.nonempty_algEquiv_of_finrank_eq
      (hinert.symm.trans (finrank_unramifiedExtension_inertiaDegree K L).symm)
  have hψ_vle (a b : F) : ψ a ≤ᵥ ψ b ↔ a ≤ᵥ b := by
    have := finite_of_valuativeExtension K F
    exact (ψ.toAlgHom : F →ₐ[K] L₀).valuativeExtension.vle_iff_vle
  let : Algebra F L := RingHom.toAlgebra ((algebraMap L₀ L).comp ψ.toRingHom)
  have : IsScalarTower K F L :=
    IsScalarTower.of_algebraMap_eq fun k ↦ by
      simp [RingHom.algebraMap_toAlgebra, AlgEquiv.commutes]
  have : ValuativeExtension F L :=
    ⟨fun {a b} ↦ by
      simp only [RingHom.algebraMap_toAlgebra, RingHom.coe_comp, Function.comp_apply]
      exact ValuativeExtension.vle_iff_vle.trans (hψ_vle a b)⟩
  have htot_L₀ : IsTotallyRamified L₀ L := isTotallyRamified_unramifiedExtension_inertiaDegree K L
  have htot_F : IsTotallyRamified F L := by
    rw [isTotallyRamified_iff_inertiaDegree_eq_one,
      inertiaDegree_eq_of_vle_iff ψ.toRingEquiv hψ_vle (RingEquiv.refl L) (fun _ ↦ rfl)]
    exact htot_L₀.inertiaDegree_eq_one
  have he_L₀ : Module.finrank L₀ L = e := by
    rw [finrank_unramifiedExtension_inertiaDegree_eq_ramificationIndex]
    apply Nat.eq_of_mul_eq_mul_right (inertiaDegree_pos (K := K) (L := L))
    rw [ramificationIndex_mul_inertiaDegree, hdeg, hinert, mul_comm]
  have he_F : Module.finrank F L = e :=
    (Algebra.finrank_eq_of_equiv_equiv ψ.toRingEquiv (RingEquiv.refl L) rfl).trans he_L₀
  exact ⟨TotallyRamifiedClass.ofExtension F L he_F htot_F,
    TotallyRamifiedClass.restrictScalars_ofExtension L he_F htot_F⟩

/-- **Classification of finite extensions by their unramified part.** Over an unramified extension
`F/K`, restricting scalars induces an equivalence from the `(F ≃ₐ[K] F)`-orbits on
`TotallyRamifiedClass F e` onto the `K`-extension classes of degree `[F : K] * e` and residue
degree `[F : K]`. -/
def totallyRamifiedOrbitEquiv (e : ℕ) :
    MulAction.orbitRel.Quotient (F ≃ₐ[K] F) (TotallyRamifiedClass F e) ≃
      {c : FiniteExtensionClass K //
        c.finrank = Module.finrank K F * e ∧ c.inertiaDegree = Module.finrank K F} :=
  Equiv.ofBijective
    (Quotient.lift
      (fun x ↦ ⟨x.restrictScalars K, x.finrank_restrictScalars, x.inertiaDegree_restrictScalars⟩)
      fun x y hxy ↦ by
        obtain ⟨τ, rfl⟩ := hxy
        exact Subtype.ext (TotallyRamifiedClass.restrictScalars_smul τ y))
    ⟨Quotient.ind₂ fun x y h ↦ Quotient.sound <| by
        obtain ⟨τ, hτ⟩ :=
          (TotallyRamifiedClass.restrictScalars_eq_restrictScalars_iff y x).1
            (congrArg Subtype.val h).symm
        exact ⟨τ, hτ⟩,
      fun ⟨c, hdeg, hinert⟩ ↦ by
        obtain ⟨x, rfl⟩ := exists_totallyRamifiedClass_restrictScalars_eq K F hdeg hinert
        exact ⟨⟦x⟧, rfl⟩⟩

@[simp]
theorem coe_totallyRamifiedOrbitEquiv_mk {e : ℕ} (x : TotallyRamifiedClass F e) :
    (totallyRamifiedOrbitEquiv K F e ⟦x⟧).1 = x.restrictScalars K :=
  (rfl)

/-- Divisibility-form of `totallyRamifiedOrbitEquiv` for a target degree `n` divisible by
`[F : K]`. -/
def totallyRamifiedOrbitEquivOfDvd {n : ℕ} (hn : Module.finrank K F ∣ n) :
    MulAction.orbitRel.Quotient (F ≃ₐ[K] F)
        (TotallyRamifiedClass F (n / Module.finrank K F)) ≃
      {c : FiniteExtensionClass K //
        c.finrank = n ∧ c.inertiaDegree = Module.finrank K F} :=
  (totallyRamifiedOrbitEquiv K F (n / Module.finrank K F)).trans
    (Equiv.subtypeEquivRight fun c ↦ by
      rw [Nat.mul_div_cancel' hn])

@[simp]
theorem coe_totallyRamifiedOrbitEquivOfDvd_mk {n : ℕ} (hn : Module.finrank K F ∣ n)
    (x : TotallyRamifiedClass F (n / Module.finrank K F)) :
    (totallyRamifiedOrbitEquivOfDvd K F hn ⟦x⟧).1 = x.restrictScalars K :=
  (rfl)

/-- **Classification of separable finite extensions by their unramified part.** Restricting scalars
along an unramified extension `F/K` identifies the `(F ≃ₐ[K] F)`-orbits on separable classes in
`TotallyRamifiedClass F e` with the separable `K`-extension classes of degree `[F : K] * e` and
residue degree `[F : K]`. -/
def separableTotallyRamifiedOrbitEquiv (e : ℕ) :
    MulAction.orbitRel.Quotient (F ≃ₐ[K] F)
        {x : TotallyRamifiedClass F e // x.IsSeparable} ≃
      {c : FiniteExtensionClass K //
        c.IsSeparable ∧
          c.finrank = Module.finrank K F * e ∧ c.inertiaDegree = Module.finrank K F} :=
  Equiv.ofBijective
    (Quotient.lift
      (fun x ↦ ⟨x.1.restrictScalars K,
        (x.1.isSeparable_restrictScalars_iff).2 x.2,
        x.1.finrank_restrictScalars, x.1.inertiaDegree_restrictScalars⟩)
      fun x y hxy ↦ by
        obtain ⟨τ, rfl⟩ := hxy
        exact Subtype.ext (TotallyRamifiedClass.restrictScalars_smul τ y.1))
    ⟨Quotient.ind₂ fun x y h ↦ Quotient.sound <| by
        obtain ⟨τ, hτ⟩ :=
          (TotallyRamifiedClass.restrictScalars_eq_restrictScalars_iff y.1 x.1).1
            (congrArg Subtype.val h).symm
        exact ⟨τ, Subtype.ext hτ⟩,
      fun ⟨c, hsep, hdeg, hinert⟩ ↦ by
        obtain ⟨x, rfl⟩ := exists_totallyRamifiedClass_restrictScalars_eq K F hdeg hinert
        exact ⟨⟦⟨x, (x.isSeparable_restrictScalars_iff).1 hsep⟩⟧, rfl⟩⟩

@[simp]
theorem coe_separableTotallyRamifiedOrbitEquiv_mk {e : ℕ}
    (x : {x : TotallyRamifiedClass F e // x.IsSeparable}) :
    (separableTotallyRamifiedOrbitEquiv K F e ⟦x⟧).1 = x.1.restrictScalars K :=
  (rfl)

/-- Divisibility-form of `separableTotallyRamifiedOrbitEquiv` for a target degree `n` divisible by
`[F : K]`. -/
def separableTotallyRamifiedOrbitEquivOfDvd {n : ℕ} (hn : Module.finrank K F ∣ n) :
    MulAction.orbitRel.Quotient (F ≃ₐ[K] F)
        {x : TotallyRamifiedClass F (n / Module.finrank K F) // x.IsSeparable} ≃
      {c : FiniteExtensionClass K //
        c.IsSeparable ∧ c.finrank = n ∧ c.inertiaDegree = Module.finrank K F} :=
  (separableTotallyRamifiedOrbitEquiv K F (n / Module.finrank K F)).trans
    (Equiv.subtypeEquivRight fun c ↦ by
      rw [Nat.mul_div_cancel' hn])

@[simp]
theorem coe_separableTotallyRamifiedOrbitEquivOfDvd_mk {n : ℕ} (hn : Module.finrank K F ∣ n)
    (x : {x : TotallyRamifiedClass F (n / Module.finrank K F) // x.IsSeparable}) :
    (separableTotallyRamifiedOrbitEquivOfDvd K F hn ⟦x⟧).1 = x.1.restrictScalars K :=
  (rfl)

end Classification

section DecompositionAndWeightedSums

variable (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]

/-- Every degree-`n` extension class of `K` has a unique residue degree `f ∣ n`, partitioning the
degree-`n` classes into fibres over `{f : ℕ // f ∣ n}`. -/
def extensionClassFinrankEquivSigma (n : ℕ) :
    {c : FiniteExtensionClass K // c.finrank = n} ≃
      Σ f : {f : ℕ // f ∣ n},
        {c : FiniteExtensionClass K // c.finrank = n ∧ c.inertiaDegree = f.1} where
  toFun c :=
    ⟨⟨c.1.inertiaDegree, c.1.inertiaDegree_dvd_finrank.trans (dvd_of_eq c.2)⟩, ⟨c.1, c.2, rfl⟩⟩
  invFun p := ⟨p.2.1, p.2.2.1⟩
  left_inv _ := rfl
  right_inv p := by
    rcases p with ⟨⟨f, hf⟩, ⟨c, hdeg, hinert⟩⟩
    dsimp only at hinert ⊢
    subst hinert
    rfl

/-- Partition of the separable degree-`n` extension classes of `K` by their residue degree
`f ∣ n`. -/
def separableExtensionClassFinrankEquivSigma (n : ℕ) :
    {c : FiniteExtensionClass K // c.IsSeparable ∧ c.finrank = n} ≃
      Σ f : {f : ℕ // f ∣ n},
        {c : FiniteExtensionClass K //
          c.IsSeparable ∧ c.finrank = n ∧ c.inertiaDegree = f.1} where
  toFun c :=
    ⟨⟨c.1.inertiaDegree, c.1.inertiaDegree_dvd_finrank.trans (dvd_of_eq c.2.2)⟩,
      ⟨c.1, c.2.1, c.2.2, rfl⟩⟩
  invFun p := ⟨p.2.1, p.2.2.1, p.2.2.2.1⟩
  left_inv _ := rfl
  right_inv p := by
    rcases p with ⟨⟨f, hf⟩, ⟨c, hsep, hdeg, hinert⟩⟩
    dsimp only at hinert ⊢
    subst hinert
    rfl

variable (F : Type v) [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F] [Algebra K F] [ValuativeExtension K F] [IsUnramified K F]

/-- **Weighted class-sum reduction along the unramified part.** For any `ℝ≥0∞`-valued invariant `w`
on `FiniteExtensionClass K`, summing `w(c) / #Aut_K(c)` over the `K`-extension classes of degree
`[F : K] * e` and residue degree `[F : K]` equals `[F : K]⁻¹` times the sum of
`w(x.restrictScalars K) / #Aut_F(x)` over `TotallyRamifiedClass F e`. -/
theorem tsum_extensionClass_inertiaDegree_div_natCardAut (e : ℕ)
    (w : FiniteExtensionClass K → ℝ≥0∞) :
    ∑' c : {c : FiniteExtensionClass K //
        c.finrank = Module.finrank K F * e ∧ c.inertiaDegree = Module.finrank K F},
        w c.1 / (c.1.natCardAut : ℝ≥0∞) =
      (Module.finrank K F : ℝ≥0∞)⁻¹ *
        ∑' x : TotallyRamifiedClass F e,
          w (x.restrictScalars K) / (x.natCardAut : ℝ≥0∞) := by
  have : FiniteDimensional K F := finite_of_valuativeExtension K F
  have := IsUnramified.isGalois K F
  conv_rhs =>
    rw [← IsGalois.card_aut_eq_finrank K F,
      MulAction.inv_natCard_mul_tsum_eq_tsum_div_natCard_stabilizer
        (G := F ≃ₐ[K] F) (fun x : TotallyRamifiedClass F e ↦
          w (x.restrictScalars K) / (x.natCardAut : ℝ≥0∞))
        (fun τ x ↦ by
          rw [TotallyRamifiedClass.restrictScalars_smul, TotallyRamifiedClass.natCardAut_smul])]
  rw [← (totallyRamifiedOrbitEquiv K F e).tsum_eq]
  refine tsum_congr fun ω ↦ ?_
  have hω : (totallyRamifiedOrbitEquiv K F e ω).1 = ω.out.restrictScalars K := by
    conv_lhs => rw [← Quotient.out_eq' ω]
    rfl
  rw [hω, ω.out.natCardAut_restrictScalars, Nat.cast_mul, div_eq_mul_inv,
    ENNReal.mul_inv (.inr (ENNReal.natCast_ne_top _)) (.inl (ENNReal.natCast_ne_top _)),
    ← mul_assoc, ← div_eq_mul_inv, ← div_eq_mul_inv]

/-- Divisibility-form of `tsum_extensionClass_inertiaDegree_div_natCardAut` for `n` divisible by
`[F : K]`. -/
theorem tsum_extensionClass_inertiaDegree_div_natCardAut_of_dvd {n : ℕ}
    (hn : Module.finrank K F ∣ n) (w : FiniteExtensionClass K → ℝ≥0∞) :
    ∑' c : {c : FiniteExtensionClass K //
        c.finrank = n ∧ c.inertiaDegree = Module.finrank K F},
        w c.1 / (c.1.natCardAut : ℝ≥0∞) =
      (Module.finrank K F : ℝ≥0∞)⁻¹ *
        ∑' x : TotallyRamifiedClass F (n / Module.finrank K F),
          w (x.restrictScalars K) / (x.natCardAut : ℝ≥0∞) := by
  rw [← (Equiv.subtypeEquivRight (fun c : FiniteExtensionClass K ↦ by
      rw [Nat.mul_div_cancel' hn] :
      ∀ c : FiniteExtensionClass K,
        (c.finrank = Module.finrank K F * (n / Module.finrank K F) ∧
          c.inertiaDegree = Module.finrank K F) ↔
        (c.finrank = n ∧ c.inertiaDegree = Module.finrank K F))).tsum_eq]
  exact tsum_extensionClass_inertiaDegree_div_natCardAut K F (n / Module.finrank K F) w

/-- **Separable weighted class-sum reduction along the unramified part.** -/
theorem tsum_separable_extensionClass_inertiaDegree_div_natCardAut (e : ℕ)
    (w : FiniteExtensionClass K → ℝ≥0∞) :
    ∑' c : {c : FiniteExtensionClass K //
        c.IsSeparable ∧
          c.finrank = Module.finrank K F * e ∧ c.inertiaDegree = Module.finrank K F},
        w c.1 / (c.1.natCardAut : ℝ≥0∞) =
      (Module.finrank K F : ℝ≥0∞)⁻¹ *
        ∑' x : {x : TotallyRamifiedClass F e // x.IsSeparable},
          w (x.1.restrictScalars K) / (x.1.natCardAut : ℝ≥0∞) := by
  have : FiniteDimensional K F := finite_of_valuativeExtension K F
  have := IsUnramified.isGalois K F
  conv_rhs =>
    rw [← IsGalois.card_aut_eq_finrank K F,
      MulAction.inv_natCard_mul_tsum_eq_tsum_div_natCard_stabilizer
        (G := F ≃ₐ[K] F) (fun x : {x : TotallyRamifiedClass F e // x.IsSeparable} ↦
          w (x.1.restrictScalars K) / (x.1.natCardAut : ℝ≥0∞))
        (fun τ x ↦ by
          rw [TotallyRamifiedClass.coe_smul_separable, TotallyRamifiedClass.restrictScalars_smul,
            TotallyRamifiedClass.natCardAut_smul])]
  rw [← (separableTotallyRamifiedOrbitEquiv K F e).tsum_eq]
  refine tsum_congr fun ω ↦ ?_
  have hω : (separableTotallyRamifiedOrbitEquiv K F e ω).1 = ω.out.1.restrictScalars K := by
    conv_lhs => rw [← Quotient.out_eq' ω]
    rfl
  rw [hω, TotallyRamifiedClass.stabilizer_separable_eq, ω.out.1.natCardAut_restrictScalars,
    Nat.cast_mul, div_eq_mul_inv,
    ENNReal.mul_inv (.inr (ENNReal.natCast_ne_top _)) (.inl (ENNReal.natCast_ne_top _)),
    ← mul_assoc, ← div_eq_mul_inv, ← div_eq_mul_inv]

/-- Divisibility-form of `tsum_separable_extensionClass_inertiaDegree_div_natCardAut` for `n`
divisible by `[F : K]`. -/
theorem tsum_separable_extensionClass_inertiaDegree_div_natCardAut_of_dvd {n : ℕ}
    (hn : Module.finrank K F ∣ n) (w : FiniteExtensionClass K → ℝ≥0∞) :
    ∑' c : {c : FiniteExtensionClass K //
        c.IsSeparable ∧ c.finrank = n ∧ c.inertiaDegree = Module.finrank K F},
        w c.1 / (c.1.natCardAut : ℝ≥0∞) =
      (Module.finrank K F : ℝ≥0∞)⁻¹ *
        ∑' x : {x : TotallyRamifiedClass F (n / Module.finrank K F) // x.IsSeparable},
          w (x.1.restrictScalars K) / (x.1.natCardAut : ℝ≥0∞) := by
  rw [← (Equiv.subtypeEquivRight (fun c : FiniteExtensionClass K ↦ by
      rw [Nat.mul_div_cancel' hn] :
      ∀ c : FiniteExtensionClass K,
        (c.IsSeparable ∧ c.finrank = Module.finrank K F * (n / Module.finrank K F) ∧
          c.inertiaDegree = Module.finrank K F) ↔
        (c.IsSeparable ∧ c.finrank = n ∧ c.inertiaDegree = Module.finrank K F))).tsum_eq]
  exact tsum_separable_extensionClass_inertiaDegree_div_natCardAut K F (n / Module.finrank K F) w

end DecompositionAndWeightedSums

end TauCeti

end
