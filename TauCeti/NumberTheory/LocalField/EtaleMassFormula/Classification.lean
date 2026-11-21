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

* `TauCeti.TotallyRamifiedClass.restrictScalars_eq_restrictScalars_iff`: over a normal extension
  `F/K`, two totally ramified `F`-extension classes have the same underlying `K`-class if and only
  if they lie in the same `(F ≃ₐ[K] F)`-orbit.
* `TauCeti.exists_totallyRamifiedClass_restrictScalars_eq`: every `K`-extension class of degree
  `[F : K] * e` and residue degree `[F : K]` arises by restricting scalars from
  `TotallyRamifiedClass F e`.
* `TauCeti.TotallyRamifiedClass.natCard_orbit_mul_natCard_stabilizer_eq_finrank` and
  `TauCeti.TotallyRamifiedClass.natCardAut_restrictScalars`: orbit-stabilizer (for Galois `F/K`)
  and automorphism-count (for normal `F/K`) formulas for totally ramified extension classes.
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

attribute [simp] TotallyRamifiedClass.finrank_eq TotallyRamifiedClass.isTotallyRamified

namespace TotallyRamifiedClass

section Basic

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F] {e : ℕ}

/-- A totally ramified extension class is uniquely determined by its underlying
`FiniteExtensionClass F`. -/
theorem toExtensionClass_injective :
    Function.Injective (toExtensionClass (F := F) (e := e)) :=
  fun _ _ ↦ TotallyRamifiedClass.ext

/-- Every class in `TotallyRamifiedClass F e` has residue degree `1` over `F`. -/
@[simp]
theorem inertiaDegree_toExtensionClass (x : TotallyRamifiedClass F e) :
    x.toExtensionClass.inertiaDegree = 1 :=
  FiniteExtensionClass.isTotallyRamified_iff_inertiaDegree_eq_one.1 x.isTotallyRamified

/-- Every class in `TotallyRamifiedClass F e` has ramification index `e` over `F`. -/
@[simp]
theorem ramificationIndex_toExtensionClass (x : TotallyRamifiedClass F e) :
    x.toExtensionClass.ramificationIndex = e :=
  (FiniteExtensionClass.isTotallyRamified_iff_ramificationIndex_eq_finrank.1
    x.isTotallyRamified).trans x.finrank_eq

/-- If `TotallyRamifiedClass F e` is nonempty, then `0 < e`. -/
theorem pos (x : TotallyRamifiedClass F e) : 0 < e :=
  x.finrank_eq ▸ x.toExtensionClass.finrank_pos

/-- If `TotallyRamifiedClass F e` is nonempty, then `e ≠ 0`. -/
theorem ne_zero (x : TotallyRamifiedClass F e) : e ≠ 0 :=
  x.pos.ne'

/-- There are no totally ramified extension classes of degree `0`. -/
instance isEmpty_zero : IsEmpty (TotallyRamifiedClass F 0) :=
  ⟨fun x ↦ x.ne_zero rfl⟩

variable (F) in
/-- The trivial totally ramified class of degree `1`, represented by `F` itself. -/
def self : TotallyRamifiedClass F 1 :=
  ⟨FiniteExtensionClass.self F, FiniteExtensionClass.finrank_self,
    FiniteExtensionClass.isTotallyRamified_self⟩

/-- The underlying `FiniteExtensionClass F` of `TotallyRamifiedClass.self F` is
`FiniteExtensionClass.self F`. -/
@[simp]
theorem toExtensionClass_self : (self F).toExtensionClass = FiniteExtensionClass.self F := (rfl)

/-- `TotallyRamifiedClass.self F` is the unique totally ramified extension class of degree `1`. -/
instance instUniqueOne : Unique (TotallyRamifiedClass F 1) where
  default := self F
  uniq x := TotallyRamifiedClass.ext
    ((FiniteExtensionClass.finrank_eq_one_iff.1 x.finrank_eq).trans toExtensionClass_self.symm)

variable (F) in
/-- The `TotallyRamifiedClass F e` of an explicit compatible totally ramified extension `L/F` of
degree `e`. -/
def ofExtension (L : Type v) [Field L] [ValuativeRel L] [TopologicalSpace L]
    [IsNonarchimedeanLocalField L] [Algebra F L] [ValuativeExtension F L]
    (he : Module.finrank F L = e) (hL : IsTotallyRamified F L) : TotallyRamifiedClass F e :=
  haveI : Module.Finite F L := finite_of_valuativeExtension F L
  ⟨FiniteExtensionClass.mk F L, (FiniteExtensionClass.finrank_mk L).trans he,
    (FiniteExtensionClass.isTotallyRamified_mk_iff L).2 hL⟩

/-- The underlying `FiniteExtensionClass F` of `ofExtension F L he hL` is
`FiniteExtensionClass.mk F L`. -/
@[simp]
theorem toExtensionClass_ofExtension (L : Type v) [Field L] [ValuativeRel L]
    [TopologicalSpace L] [IsNonarchimedeanLocalField L] [Algebra F L] [ValuativeExtension F L]
    (he : Module.finrank F L = e) (hL : IsTotallyRamified F L) :
    haveI : Module.Finite F L := finite_of_valuativeExtension F L
    (ofExtension F L he hL).toExtensionClass = FiniteExtensionClass.mk F L := (rfl)

/-- Two degree-`e` totally ramified extensions of `F` define the same `TotallyRamifiedClass F e`
if and only if they are `F`-isomorphic. -/
@[simp]
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
      motive (ofExtension F L he hL)) : motive x := by
  obtain ⟨c, hc_deg, hc_tot⟩ := x
  induction c using FiniteExtensionClass.induction_on_localField with | h L =>
  rw [FiniteExtensionClass.finrank_mk] at hc_deg
  rw [FiniteExtensionClass.isTotallyRamified_mk_iff] at hc_tot
  exact h L hc_deg hc_tot

/-- A totally ramified extension class is separable over `F` when its underlying extension class is
separable. -/
def IsSeparable (x : TotallyRamifiedClass F e) : Prop :=
  x.toExtensionClass.IsSeparable

/-- Definitional unfolding of `TotallyRamifiedClass.IsSeparable` via `toExtensionClass`. -/
theorem isSeparable_def (x : TotallyRamifiedClass F e) :
    x.IsSeparable ↔ x.toExtensionClass.IsSeparable := (Iff.rfl)

/-- `ofExtension F L he hL` is separable if and only if `L/F` is separable. -/
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

/-- Definitional unfolding of `TotallyRamifiedClass.natCardAut` via `toExtensionClass`. -/
theorem natCardAut_def (x : TotallyRamifiedClass F e) :
    x.natCardAut = x.toExtensionClass.natCardAut := (rfl)

/-- The automorphism count of `ofExtension F L he hL` is `Nat.card (L ≃ₐ[F] L)`. -/
@[simp]
theorem natCardAut_ofExtension (L : Type v) [Field L] [ValuativeRel L]
    [TopologicalSpace L] [IsNonarchimedeanLocalField L] [Algebra F L] [ValuativeExtension F L]
    (he : Module.finrank F L = e) (hL : IsTotallyRamified F L) :
    (ofExtension F L he hL).natCardAut = Nat.card (L ≃ₐ[F] L) := by
  have : Module.Finite F L := finite_of_valuativeExtension F L
  rw [natCardAut_def, toExtensionClass_ofExtension, FiniteExtensionClass.natCardAut_mk]

/-- Every totally ramified extension class has positive automorphism count. -/
theorem natCardAut_pos (x : TotallyRamifiedClass F e) : 0 < x.natCardAut :=
  x.toExtensionClass.natCardAut_pos

/-- The automorphism count of a totally ramified extension class is nonzero. -/
@[simp]
theorem natCardAut_ne_zero (x : TotallyRamifiedClass F e) : x.natCardAut ≠ 0 :=
  x.natCardAut_pos.ne'

section SeparableClosure

/-- Canonical map sending a member `L` of `σ_F(e) = totallyRamifiedOfDegree F e` to its separable
totally ramified `F`-isomorphism class. -/
def ofTotallyRamifiedOfDegree (L : totallyRamifiedOfDegree F e) :
    {x : TotallyRamifiedClass F e // x.IsSeparable} :=
  let hL := mem_totallyRamifiedOfDegree_iff.1 L.property
  haveI : Module.Finite F L.val := hL.2.finite
  letI := finiteIntermediateFieldValuativeRel F (SeparableClosure F) L.val
  letI := finiteIntermediateFieldTopology F (SeparableClosure F) L.val
  haveI := finiteIntermediateField_isNonarchimedeanLocalField F (SeparableClosure F) L.val
  haveI := finiteIntermediateField_valuativeExtension F (SeparableClosure F) L.val
  ⟨ofExtension F L.val hL.1 ((L.val.isTotallyRamified_iff).1 hL.2),
    (isSeparable_ofExtension_iff L.val hL.1 ((L.val.isTotallyRamified_iff).1 hL.2)).2
      (Algebra.isSeparable_tower_bot_of_isSeparable F L.val (SeparableClosure F))⟩

/-- For `L : totallyRamifiedOfDegree F e`, the underlying `FiniteExtensionClass F` of
`ofTotallyRamifiedOfDegree L` is `mk F L.1`. -/
@[simp]
theorem toExtensionClass_ofTotallyRamifiedOfDegree (L : totallyRamifiedOfDegree F e) :
    haveI : Module.Finite F L.val := (mem_totallyRamifiedOfDegree_iff.1 L.property).2.finite
    (ofTotallyRamifiedOfDegree L).val.toExtensionClass = FiniteExtensionClass.mk F L.val := (rfl)

/-- The automorphism count of `ofTotallyRamifiedOfDegree L` is `Nat.card (L.1 ≃ₐ[F] L.1)`.

Not a `simp` lemma: on the right-hand side, `simp` tries `Nat.card_eq_fintype_card`, whose
`Fintype` search on the automorphism group times out in large environments. -/
theorem natCardAut_ofTotallyRamifiedOfDegree (L : totallyRamifiedOfDegree F e) :
    (ofTotallyRamifiedOfDegree L).val.natCardAut = Nat.card (L.val ≃ₐ[F] L.val) := by
  have : Module.Finite F L.val := (mem_totallyRamifiedOfDegree_iff.1 L.property).2.finite
  rw [natCardAut_def, toExtensionClass_ofTotallyRamifiedOfDegree,
    FiniteExtensionClass.natCardAut_mk]

/-- Two members of `totallyRamifiedOfDegree F e` map to the same separable `TotallyRamifiedClass F
e` if and only if they are `F`-isomorphic. -/
@[simp]
theorem ofTotallyRamifiedOfDegree_eq_iff (L M : totallyRamifiedOfDegree F e) :
    ofTotallyRamifiedOfDegree L = ofTotallyRamifiedOfDegree M ↔ Nonempty (L.val ≃ₐ[F] M.val) := by
  have : Module.Finite F L.val := (mem_totallyRamifiedOfDegree_iff.1 L.property).2.finite
  have : Module.Finite F M.val := (mem_totallyRamifiedOfDegree_iff.1 M.property).2.finite
  rw [Subtype.ext_iff, TotallyRamifiedClass.ext_iff, toExtensionClass_ofTotallyRamifiedOfDegree,
    toExtensionClass_ofTotallyRamifiedOfDegree, FiniteExtensionClass.mk_eq_mk_iff]

/-- Every separable class in `TotallyRamifiedClass F e` arises from an intermediate field in
`totallyRamifiedOfDegree F e` inside `SeparableClosure F`. -/
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
    let := finiteIntermediateFieldValuativeRel F (SeparableClosure F) ι.fieldRange
    let := finiteIntermediateFieldTopology F (SeparableClosure F) ι.fieldRange
    have := finiteIntermediateField_isNonarchimedeanLocalField F (SeparableClosure F) ι.fieldRange
    have := finiteIntermediateField_valuativeExtension F (SeparableClosure F) ι.fieldRange
    rw [isTotallyRamified_iff_inertiaDegree_eq_one, ← inertiaDegree_eq_of_algEquiv F L _ φ]
    exact hL.inertiaDegree_eq_one
  refine ⟨⟨ι.fieldRange, mem_totallyRamifiedOfDegree_iff.2 ⟨hdeg, htot⟩⟩, Subtype.ext ?_⟩
  rw [TotallyRamifiedClass.ext_iff, toExtensionClass_ofTotallyRamifiedOfDegree,
    toExtensionClass_ofExtension, FiniteExtensionClass.mk_eq_mk_iff]
  exact ⟨φ.symm⟩

end SeparableClosure

end Basic

end TotallyRamifiedClass

section RepresentativeSet

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F] {e : ℕ} {R : Set (IntermediateField F (SeparableClosure F))}

/-- Any set of representatives `R` of the `F`-isomorphism classes in `σ_F(e)` is canonically
equivalent to the separable classes in `TotallyRamifiedClass F e`. -/
def IsRepresentativeSet.equivSeparableTotallyRamifiedClass (hR : IsRepresentativeSet e R) :
    R ≃ {x : TotallyRamifiedClass F e // x.IsSeparable} :=
  Equiv.ofBijective
    (fun M ↦ TotallyRamifiedClass.ofTotallyRamifiedOfDegree ⟨M.val, hR.subset M.property⟩)
    ⟨fun M₁ M₂ h ↦ by
      obtain ⟨e₁₂⟩ := (TotallyRamifiedClass.ofTotallyRamifiedOfDegree_eq_iff _ _).1 h
      obtain ⟨_, -, huniq⟩ := hR.existsUnique (hR.subset M₁.property)
      exact Subtype.ext ((huniq M₁.val ⟨M₁.property, ⟨AlgEquiv.refl⟩⟩).trans
        (huniq M₂.val ⟨M₂.property, ⟨e₁₂⟩⟩).symm),
      fun y ↦ by
      obtain ⟨L, rfl⟩ := TotallyRamifiedClass.ofTotallyRamifiedOfDegree_surjective y
      obtain ⟨M, ⟨hM, ⟨eLM⟩⟩, -⟩ := hR.existsUnique L.property
      exact ⟨⟨M, hM⟩,
        (TotallyRamifiedClass.ofTotallyRamifiedOfDegree_eq_iff ⟨M, hR.subset hM⟩ L).2
          ⟨eLM.symm⟩⟩⟩

/-- Evaluating `hR.equivSeparableTotallyRamifiedClass` on `M : R` sends it to
`TotallyRamifiedClass.ofTotallyRamifiedOfDegree ⟨M.1, hR.subset M.2⟩`. -/
@[simp]
theorem IsRepresentativeSet.equivSeparableTotallyRamifiedClass_apply
    (hR : IsRepresentativeSet e R) (M : R) :
    hR.equivSeparableTotallyRamifiedClass M =
      TotallyRamifiedClass.ofTotallyRamifiedOfDegree ⟨M.val, hR.subset M.property⟩ := (rfl)

end RepresentativeSet

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

/-- `toExtensionClass` is equivariant for the `(F ≃ₐ[K] F)`-action. -/
@[simp]
theorem toExtensionClass_smul (τ : F ≃ₐ[K] F) (x : TotallyRamifiedClass F e) :
    (τ • x).toExtensionClass = τ • x.toExtensionClass := (rfl)

/-- The `(F ≃ₐ[K] F)`-action on `TotallyRamifiedClass F e` preserves and reflects separability. -/
@[simp]
theorem isSeparable_smul_iff (τ : F ≃ₐ[K] F) (x : TotallyRamifiedClass F e) :
    (τ • x).IsSeparable ↔ x.IsSeparable := by
  rw [isSeparable_def, isSeparable_def, toExtensionClass_smul,
    FiniteExtensionClass.isSeparable_smul_iff]

/-- The `(F ≃ₐ[K] F)`-action on `TotallyRamifiedClass F e` preserves the `F`-automorphism count. -/
@[simp]
theorem natCardAut_smul (τ : F ≃ₐ[K] F) (x : TotallyRamifiedClass F e) :
    (τ • x).natCardAut = x.natCardAut := by
  rw [natCardAut_def, natCardAut_def, toExtensionClass_smul, FiniteExtensionClass.natCardAut_smul]

/-- The stabilizer of `x : TotallyRamifiedClass F e` in `F ≃ₐ[K] F` coincides with the stabilizer
of `x.toExtensionClass`. -/
theorem stabilizer_eq_stabilizer_toExtensionClass (x : TotallyRamifiedClass F e) :
    MulAction.stabilizer (F ≃ₐ[K] F) x =
      MulAction.stabilizer (F ≃ₐ[K] F) x.toExtensionClass := by
  ext τ; simp [MulAction.mem_stabilizer_iff, TotallyRamifiedClass.ext_iff]

variable (K) in
/-- Restriction of scalars sends a totally ramified `F`-extension class to its underlying
`K`-extension class. -/
def restrictScalars (x : TotallyRamifiedClass F e) : FiniteExtensionClass K :=
  haveI : Module.Finite K F := finite_of_valuativeExtension K F
  x.toExtensionClass.restrictScalars K

/-- Definitional unfolding of `TotallyRamifiedClass.restrictScalars` via `toExtensionClass`. -/
theorem restrictScalars_def (x : TotallyRamifiedClass F e) :
    haveI : Module.Finite K F := finite_of_valuativeExtension K F
    x.restrictScalars K = x.toExtensionClass.restrictScalars K := (rfl)

/-- Restricting scalars of `ofExtension F L he hL` along a tower `K/F/L` gives
`FiniteExtensionClass.mk K L`. -/
@[simp]
theorem restrictScalars_ofExtension (L : Type w) [Field L] [ValuativeRel L]
    [TopologicalSpace L] [IsNonarchimedeanLocalField L] [Algebra K L] [Algebra F L]
    [IsScalarTower K F L] [ValuativeExtension F L]
    (he : Module.finrank F L = e) (hL : IsTotallyRamified F L) :
    haveI : Module.Finite K F := finite_of_valuativeExtension K F
    haveI : Module.Finite F L := finite_of_valuativeExtension F L
    haveI : Module.Finite K L := Module.Finite.trans F L
    (ofExtension F L he hL).restrictScalars K = FiniteExtensionClass.mk K L := by
  have : Module.Finite K F := finite_of_valuativeExtension K F
  have : Module.Finite F L := finite_of_valuativeExtension F L
  rw [restrictScalars_def, toExtensionClass_ofExtension,
    FiniteExtensionClass.restrictScalars_mk (F := F) K L]

/-- Restricting scalars of `x : TotallyRamifiedClass F e` down to `K` produces a `K`-extension
class of degree `[F : K] * e`. -/
@[simp]
theorem finrank_restrictScalars (x : TotallyRamifiedClass F e) :
    (x.restrictScalars K).finrank = Module.finrank K F * e := by
  have : Module.Finite K F := finite_of_valuativeExtension K F
  rw [restrictScalars_def, FiniteExtensionClass.finrank_restrictScalars, x.finrank_eq]

/-- Restricting scalars from `F` to `K` is invariant under the `(F ≃ₐ[K] F)`-action on
`TotallyRamifiedClass F e`. -/
@[simp]
theorem restrictScalars_smul (τ : F ≃ₐ[K] F) (x : TotallyRamifiedClass F e) :
    (τ • x).restrictScalars K = x.restrictScalars K := by
  have : Module.Finite K F := finite_of_valuativeExtension K F
  rw [restrictScalars_def, restrictScalars_def, toExtensionClass_smul,
    FiniteExtensionClass.restrictScalars_smul]

/-- **Tower law for separability of totally ramified extension classes.** `x.restrictScalars K` is
separable over `K` if and only if both `F/K` and `x` are separable. -/
theorem isSeparable_restrictScalars_iff (x : TotallyRamifiedClass F e) :
    (x.restrictScalars K).IsSeparable ↔ Algebra.IsSeparable K F ∧ x.IsSeparable := by
  have : Module.Finite K F := finite_of_valuativeExtension K F
  rw [restrictScalars_def, FiniteExtensionClass.isSeparable_restrictScalars_iff, isSeparable_def]

/-- **Orbit characterization of `restrictScalars` over a normal base.** When `F/K` is normal, two
totally ramified `F`-extension classes induce the same `K`-extension class if and only if they lie
in the same `(F ≃ₐ[K] F)`-orbit. -/
theorem restrictScalars_eq_restrictScalars_iff [Normal K F] (x y : TotallyRamifiedClass F e) :
    x.restrictScalars K = y.restrictScalars K ↔ ∃ τ : F ≃ₐ[K] F, τ • x = y := by
  have : Module.Finite K F := finite_of_valuativeExtension K F
  rw [restrictScalars_def, restrictScalars_def,
    FiniteExtensionClass.restrictScalars_eq_restrictScalars_iff]
  simp [TotallyRamifiedClass.ext_iff]

/-- **Orbit-stabilizer identity for `TotallyRamifiedClass F e`.** For a Galois extension `F/K`, the
orbit size of `x` under `F ≃ₐ[K] F` times its stabilizer size equals `[F : K]`. -/
theorem natCard_orbit_mul_natCard_stabilizer_eq_finrank [IsGalois K F]
    (x : TotallyRamifiedClass F e) :
    Nat.card (MulAction.orbit (F ≃ₐ[K] F) x) *
      Nat.card (MulAction.stabilizer (F ≃ₐ[K] F) x) = Module.finrank K F := by
  have : FiniteDimensional K F := finite_of_valuativeExtension K F
  rw [← Nat.card_prod, Nat.card_congr (MulAction.orbitProdStabilizerEquivGroup (F ≃ₐ[K] F) x),
    IsGalois.card_aut_eq_finrank K F]

/-- **Automorphism count in a tower with normal bottom step.** For `x : TotallyRamifiedClass F e`
over a normal extension `F/K`, `#Aut_K(x.restrictScalars K) = #Aut_F(x) · #Stab(x)`. -/
theorem natCardAut_restrictScalars [Normal K F] (x : TotallyRamifiedClass F e) :
    (x.restrictScalars K).natCardAut =
      x.natCardAut * Nat.card (MulAction.stabilizer (F ≃ₐ[K] F) x) := by
  have : Module.Finite K F := finite_of_valuativeExtension K F
  rw [restrictScalars_def, FiniteExtensionClass.natCardAut_restrictScalars, natCardAut_def,
    stabilizer_eq_stabilizer_toExtensionClass]

/-- Transport of structure by `F ≃ₐ[K] F` restricts to the subtype of separable totally ramified
classes. -/
instance instMulActionSeparable :
    MulAction (F ≃ₐ[K] F) {x : TotallyRamifiedClass F e // x.IsSeparable} where
  smul τ x := ⟨τ • x.val, (isSeparable_smul_iff τ x.val).2 x.property⟩
  one_smul x := Subtype.ext (one_smul (F ≃ₐ[K] F) x.val)
  mul_smul τ₁ τ₂ x := Subtype.ext (mul_smul τ₁ τ₂ x.val)

/-- Coercion from separable totally ramified classes to `TotallyRamifiedClass F e` is
`(F ≃ₐ[K] F)`-equivariant. -/
@[simp]
theorem coe_smul_separable (τ : F ≃ₐ[K] F) (x : {x : TotallyRamifiedClass F e // x.IsSeparable}) :
    (τ • x).val = τ • x.val := (rfl)

/-- The stabilizer of a separable totally ramified class in `F ≃ₐ[K] F` equals the stabilizer of
its underlying `TotallyRamifiedClass F e`. -/
theorem stabilizer_separable_eq (x : {x : TotallyRamifiedClass F e // x.IsSeparable}) :
    MulAction.stabilizer (F ≃ₐ[K] F) x = MulAction.stabilizer (F ≃ₐ[K] F) x.val := by
  ext τ; simp [MulAction.mem_stabilizer_iff, Subtype.ext_iff]

section UnramifiedBase

variable [IsUnramified K F]

/-- Over an unramified base `F/K`, restricting scalars of `x : TotallyRamifiedClass F e` yields a
`K`-extension class of residue degree `[F : K]`. -/
@[simp]
theorem inertiaDegree_restrictScalars (x : TotallyRamifiedClass F e) :
    (x.restrictScalars K).inertiaDegree = Module.finrank K F := by
  have : Module.Finite K F := finite_of_valuativeExtension K F
  rw [restrictScalars_def, FiniteExtensionClass.inertiaDegree_restrictScalars,
    x.inertiaDegree_toExtensionClass, mul_one, IsUnramified.inertiaDegree_eq_finrank]

/-- Over an unramified base `F/K`, restricting scalars of `x : TotallyRamifiedClass F e` yields a
`K`-extension class of ramification index `e`. -/
@[simp]
theorem ramificationIndex_restrictScalars (x : TotallyRamifiedClass F e) :
    (x.restrictScalars K).ramificationIndex = e := by
  have : Module.Finite K F := finite_of_valuativeExtension K F
  rw [restrictScalars_def, FiniteExtensionClass.ramificationIndex_restrictScalars,
    IsUnramified.ramificationIndex_eq_one, one_mul, x.ramificationIndex_toExtensionClass]

end UnramifiedBase

end ActionAndRestrictScalars

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
  have := finite_of_valuativeExtension K F
  rw [FiniteExtensionClass.finrank_mk] at hdeg
  rw [FiniteExtensionClass.inertiaDegree_mk] at hinert
  let L₀ : IntermediateField K L := unramifiedExtension K L (inertiaDegree K L)
  let := finiteIntermediateFieldValuativeRel K L L₀
  let := finiteIntermediateFieldTopology K L L₀
  have := finiteIntermediateField_isNonarchimedeanLocalField K L L₀
  have := finiteIntermediateField_valuativeExtension K L L₀
  have := isUnramified_unramifiedExtension_inertiaDegree K L
  obtain ⟨ψ⟩ : Nonempty (F ≃ₐ[K] L₀) := IsUnramified.nonempty_algEquiv_of_finrank_eq
    (hinert.symm.trans (finrank_unramifiedExtension_inertiaDegree K L).symm)
  let := RingHom.toAlgebra ((algebraMap L₀ L).comp ψ.toRingHom)
  have : IsScalarTower K F L := IsScalarTower.of_algebraMap_eq fun k ↦ by
    simp [RingHom.algebraMap_toAlgebra, AlgEquiv.commutes]
  have : ValuativeExtension F L := ValuativeExtension.of_isScalarTower (K := K)
  have : Module.Finite F L := finite_of_valuativeExtension F L
  have htot_F : IsTotallyRamified F L :=
    (IsUnramified.isTotallyRamified_iff_finrank_eq K F L).2 hinert.symm
  have he_F : Module.finrank F L = e :=
    Nat.eq_of_mul_eq_mul_left Module.finrank_pos ((Module.finrank_mul_finrank K F L).trans hdeg)
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
  haveI := IsUnramified.isGalois K F
  Equiv.ofBijective
    (Quotient.lift
      (fun x ↦ ⟨x.restrictScalars K, x.finrank_restrictScalars, x.inertiaDegree_restrictScalars⟩)
      fun _ y ⟨τ, hτ⟩ ↦ Subtype.ext (hτ ▸ TotallyRamifiedClass.restrictScalars_smul τ y))
    ⟨Quotient.ind₂ fun x y h ↦ Quotient.sound <|
        (TotallyRamifiedClass.restrictScalars_eq_restrictScalars_iff y x).1
          (congrArg Subtype.val h).symm,
      fun ⟨_, hdeg, hinert⟩ ↦
        let ⟨x, hx⟩ := exists_totallyRamifiedClass_restrictScalars_eq K F hdeg hinert
        ⟨⟦x⟧, Subtype.ext hx⟩⟩

/-- On the orbit `⟦x⟧`, `totallyRamifiedOrbitEquiv K F e` evaluates to `x.restrictScalars K`. -/
@[simp]
theorem coe_totallyRamifiedOrbitEquiv_mk {e : ℕ} (x : TotallyRamifiedClass F e) :
    (totallyRamifiedOrbitEquiv K F e ⟦x⟧).val = x.restrictScalars K := (rfl)

/-- Divisibility-form of `totallyRamifiedOrbitEquiv` for a target degree `n` divisible by
`[F : K]`. -/
def totallyRamifiedOrbitEquivOfDvd {n : ℕ} (hn : Module.finrank K F ∣ n) :
    MulAction.orbitRel.Quotient (F ≃ₐ[K] F)
        (TotallyRamifiedClass F (n / Module.finrank K F)) ≃
      {c : FiniteExtensionClass K //
        c.finrank = n ∧ c.inertiaDegree = Module.finrank K F} :=
  (totallyRamifiedOrbitEquiv K F (n / Module.finrank K F)).trans
    (Equiv.subtypeEquivRight fun _ ↦ by rw [Nat.mul_div_cancel' hn])

/-- On the orbit `⟦x⟧`, `totallyRamifiedOrbitEquivOfDvd K F hn` evaluates to
`x.restrictScalars K`. -/
@[simp]
theorem coe_totallyRamifiedOrbitEquivOfDvd_mk {n : ℕ} (hn : Module.finrank K F ∣ n)
    (x : TotallyRamifiedClass F (n / Module.finrank K F)) :
    (totallyRamifiedOrbitEquivOfDvd K F hn ⟦x⟧).val = x.restrictScalars K := (rfl)

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
  haveI := IsUnramified.isGalois K F
  Equiv.ofBijective
    (Quotient.lift
      (fun x ↦ ⟨x.val.restrictScalars K,
        (x.val.isSeparable_restrictScalars_iff).2 ⟨inferInstance, x.property⟩,
        x.val.finrank_restrictScalars, x.val.inertiaDegree_restrictScalars⟩)
      fun _ y ⟨τ, hτ⟩ ↦ Subtype.ext (hτ ▸ TotallyRamifiedClass.restrictScalars_smul τ y.val))
    ⟨Quotient.ind₂ fun x y h ↦ Quotient.sound <| by
        obtain ⟨τ, hτ⟩ :=
          (TotallyRamifiedClass.restrictScalars_eq_restrictScalars_iff y.val x.val).1
          (congrArg Subtype.val h).symm
        exact ⟨τ, Subtype.ext hτ⟩,
      fun ⟨_, hsep, hdeg, hinert⟩ ↦ by
        obtain ⟨x, rfl⟩ := exists_totallyRamifiedClass_restrictScalars_eq K F hdeg hinert
        exact ⟨⟦⟨x, ((x.isSeparable_restrictScalars_iff).1 hsep).2⟩⟧, rfl⟩⟩

/-- On the orbit `⟦x⟧`, `separableTotallyRamifiedOrbitEquiv K F e` evaluates to
`x.1.restrictScalars K`. -/
@[simp]
theorem coe_separableTotallyRamifiedOrbitEquiv_mk {e : ℕ}
    (x : {x : TotallyRamifiedClass F e // x.IsSeparable}) :
    (separableTotallyRamifiedOrbitEquiv K F e ⟦x⟧).val = x.val.restrictScalars K := (rfl)

/-- Divisibility-form of `separableTotallyRamifiedOrbitEquiv` for a target degree `n` divisible by
`[F : K]`. -/
def separableTotallyRamifiedOrbitEquivOfDvd {n : ℕ} (hn : Module.finrank K F ∣ n) :
    MulAction.orbitRel.Quotient (F ≃ₐ[K] F)
        {x : TotallyRamifiedClass F (n / Module.finrank K F) // x.IsSeparable} ≃
      {c : FiniteExtensionClass K //
        c.IsSeparable ∧ c.finrank = n ∧ c.inertiaDegree = Module.finrank K F} :=
  (separableTotallyRamifiedOrbitEquiv K F (n / Module.finrank K F)).trans
    (Equiv.subtypeEquivRight fun _ ↦ by rw [Nat.mul_div_cancel' hn])

/-- On the orbit `⟦x⟧`, `separableTotallyRamifiedOrbitEquivOfDvd K F hn` evaluates to
`x.1.restrictScalars K`. -/
@[simp]
theorem coe_separableTotallyRamifiedOrbitEquivOfDvd_mk {n : ℕ} (hn : Module.finrank K F ∣ n)
    (x : {x : TotallyRamifiedClass F (n / Module.finrank K F) // x.IsSeparable}) :
    (separableTotallyRamifiedOrbitEquivOfDvd K F hn ⟦x⟧).val = x.val.restrictScalars K := (rfl)

end Classification

section DecompositionAndWeightedSums

variable (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]

/-- Every degree-`n` extension class of `K` has a unique residue degree `f ∣ n`, partitioning the
degree-`n` classes into fibres over `{f : ℕ // f ∣ n}`. -/
def extensionClassFinrankEquivSigma (n : ℕ) :
    {c : FiniteExtensionClass K // c.finrank = n} ≃
      Σ f : {f : ℕ // f ∣ n},
        {c : FiniteExtensionClass K // c.finrank = n ∧ c.inertiaDegree = f.val} where
  toFun c :=
    ⟨⟨c.val.inertiaDegree, c.val.inertiaDegree_dvd_finrank.trans (dvd_of_eq c.property)⟩, ⟨c.val,
        c.property, rfl⟩⟩
  invFun p := ⟨p.2.val, p.2.property.1⟩
  left_inv _ := rfl
  right_inv := fun ⟨⟨_, _⟩, ⟨_, _, rfl⟩⟩ ↦ rfl

/-- Evaluating `extensionClassFinrankEquivSigma K n` tags a class with its residue degree. -/
@[simp]
theorem extensionClassFinrankEquivSigma_apply (n : ℕ)
    (c : {c : FiniteExtensionClass K // c.finrank = n}) :
    extensionClassFinrankEquivSigma K n c =
      ⟨⟨c.val.inertiaDegree, c.val.inertiaDegree_dvd_finrank.trans (dvd_of_eq c.property)⟩,
        ⟨c.val, c.property, rfl⟩⟩ := (rfl)

/-- The inverse of `extensionClassFinrankEquivSigma K n` forgets the residue-degree fibre tag. -/
@[simp]
theorem extensionClassFinrankEquivSigma_symm_apply (n : ℕ)
    (p : Σ f : {f : ℕ // f ∣ n},
      {c : FiniteExtensionClass K // c.finrank = n ∧ c.inertiaDegree = f.val}) :
    (extensionClassFinrankEquivSigma K n).symm p = ⟨p.2.val, p.2.property.1⟩ := (rfl)

/-- Partition of the separable degree-`n` extension classes of `K` by their residue degree
`f ∣ n`. -/
def separableExtensionClassFinrankEquivSigma (n : ℕ) :
    {c : FiniteExtensionClass K // c.IsSeparable ∧ c.finrank = n} ≃
      Σ f : {f : ℕ // f ∣ n},
        {c : FiniteExtensionClass K //
          c.IsSeparable ∧ c.finrank = n ∧ c.inertiaDegree = f.val} where
  toFun c :=
    ⟨⟨c.val.inertiaDegree, c.val.inertiaDegree_dvd_finrank.trans (dvd_of_eq c.property.2)⟩,
      ⟨c.val, c.property.1, c.property.2, rfl⟩⟩
  invFun p := ⟨p.2.val, p.2.property.1, p.2.property.2.1⟩
  left_inv _ := rfl
  right_inv := fun ⟨⟨_, _⟩, ⟨_, _, _, rfl⟩⟩ ↦ rfl

/-- Evaluating `separableExtensionClassFinrankEquivSigma K n` tags a separable class with its
residue degree. -/
@[simp]
theorem separableExtensionClassFinrankEquivSigma_apply (n : ℕ)
    (c : {c : FiniteExtensionClass K // c.IsSeparable ∧ c.finrank = n}) :
    separableExtensionClassFinrankEquivSigma K n c =
      ⟨⟨c.val.inertiaDegree, c.val.inertiaDegree_dvd_finrank.trans (dvd_of_eq c.property.2)⟩,
        ⟨c.val, c.property.1, c.property.2, rfl⟩⟩ := (rfl)

/-- The inverse of `separableExtensionClassFinrankEquivSigma K n` forgets the residue-degree fibre
tag. -/
@[simp]
theorem separableExtensionClassFinrankEquivSigma_symm_apply (n : ℕ)
    (p : Σ f : {f : ℕ // f ∣ n},
      {c : FiniteExtensionClass K // c.IsSeparable ∧ c.finrank = n ∧ c.inertiaDegree = f.val}) :
    (separableExtensionClassFinrankEquivSigma K n).symm p = ⟨p.2.val, p.2.property.1,
        p.2.property.2.1⟩ := (rfl)

variable (F : Type v) [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F] [Algebra K F] [ValuativeExtension K F] [IsUnramified K F]

/-- Common orbit-stabilizer reduction for weighted `ℝ≥0∞` sums over `K`-extension classes
classified as `(F ≃ₐ[K] F)`-orbits on a class type `X` via a restriction map `r`. -/
private theorem tsum_extensionClass_div_natCardAut_of_orbitEquiv
    {X : Type*} [MulAction (F ≃ₐ[K] F) X] {P : FiniteExtensionClass K → Prop}
    (r : X → FiniteExtensionClass K) (aut : X → ℕ)
    (haut_smul : ∀ (τ : F ≃ₐ[K] F) (x : X), aut (τ • x) = aut x)
    (haut_restrict : ∀ x : X,
      (r x).natCardAut = aut x * Nat.card (MulAction.stabilizer (F ≃ₐ[K] F) x))
    (equiv : MulAction.orbitRel.Quotient (F ≃ₐ[K] F) X ≃ {c : FiniteExtensionClass K // P c})
    (hequiv : ∀ x : X, (equiv ⟦x⟧).val = r x)
    (w : FiniteExtensionClass K → ℝ≥0∞) :
    ∑' c : {c : FiniteExtensionClass K // P c}, w c.val / (c.val.natCardAut : ℝ≥0∞) =
      (Module.finrank K F : ℝ≥0∞)⁻¹ * ∑' x : X, w (r x) / (aut x : ℝ≥0∞) := by
  have : FiniteDimensional K F := finite_of_valuativeExtension K F
  have := IsUnramified.isGalois K F
  have hr_smul (τ : F ≃ₐ[K] F) (x : X) : r (τ • x) = r x := by
    rw [← hequiv, ← hequiv, Quotient.sound (⟨τ, rfl⟩ : MulAction.orbitRel (F ≃ₐ[K] F) X _ _)]
  conv_rhs =>
    rw [← IsGalois.card_aut_eq_finrank K F,
      MulAction.inv_natCard_mul_tsum_eq_tsum_div_natCard_stabilizer
        (G := F ≃ₐ[K] F) (fun x : X ↦ w (r x) / (aut x : ℝ≥0∞))
        (fun τ x ↦ by rw [hr_smul, haut_smul])]
  rw [← equiv.tsum_eq]
  refine tsum_congr fun ω ↦ ?_
  have hω : (equiv ω).val = r ω.out := by rw [← hequiv, Quotient.out_eq]
  rw [hω, haut_restrict, Nat.cast_mul, div_eq_mul_inv,
    ENNReal.mul_inv (.inr (ENNReal.natCast_ne_top _)) (.inl (ENNReal.natCast_ne_top _)),
    ← mul_assoc, ← div_eq_mul_inv, ← div_eq_mul_inv]

/-- **Weighted class-sum reduction along the unramified part.** For any `ℝ≥0∞`-valued invariant `w`
on `FiniteExtensionClass K`, summing `w(c) / #Aut_K(c)` over the `K`-extension classes of degree
`[F : K] * e` and residue degree `[F : K]` equals `[F : K]⁻¹` times the sum of
`w(x.restrictScalars K) / #Aut_F(x)` over `TotallyRamifiedClass F e`. -/
theorem tsum_extensionClass_inertiaDegree_div_natCardAut (e : ℕ)
    (w : FiniteExtensionClass K → ℝ≥0∞) :
    ∑' c : {c : FiniteExtensionClass K //
        c.finrank = Module.finrank K F * e ∧ c.inertiaDegree = Module.finrank K F},
        w c.val / (c.val.natCardAut : ℝ≥0∞) =
      (Module.finrank K F : ℝ≥0∞)⁻¹ *
        ∑' x : TotallyRamifiedClass F e, w (x.restrictScalars K) / (x.natCardAut : ℝ≥0∞) :=
  haveI := IsUnramified.isGalois K F
  tsum_extensionClass_div_natCardAut_of_orbitEquiv K F
    (TotallyRamifiedClass.restrictScalars K) TotallyRamifiedClass.natCardAut
    TotallyRamifiedClass.natCardAut_smul TotallyRamifiedClass.natCardAut_restrictScalars
    (totallyRamifiedOrbitEquiv K F e) (coe_totallyRamifiedOrbitEquiv_mk K F) w

/-- Divisibility-form of `tsum_extensionClass_inertiaDegree_div_natCardAut` for `n` divisible by
`[F : K]`. -/
theorem tsum_extensionClass_inertiaDegree_div_natCardAut_of_dvd {n : ℕ}
    (hn : Module.finrank K F ∣ n) (w : FiniteExtensionClass K → ℝ≥0∞) :
    ∑' c : {c : FiniteExtensionClass K // c.finrank = n ∧ c.inertiaDegree = Module.finrank K F},
        w c.val / (c.val.natCardAut : ℝ≥0∞) =
      (Module.finrank K F : ℝ≥0∞)⁻¹ *
        ∑' x : TotallyRamifiedClass F (n / Module.finrank K F),
          w (x.restrictScalars K) / (x.natCardAut : ℝ≥0∞) := by
  have h := tsum_extensionClass_inertiaDegree_div_natCardAut K F (n / Module.finrank K F) w
  rwa [Nat.mul_div_cancel' hn] at h

/-- **Separable weighted class-sum reduction along the unramified part.** For any `ℝ≥0∞`-valued
invariant `w` on `FiniteExtensionClass K`, summing `w(c) / #Aut_K(c)` over the separable
`K`-extension classes of degree `[F : K] * e` and residue degree `[F : K]` equals `[F : K]⁻¹`
times the sum of `w(x.1.restrictScalars K) / #Aut_F(x.1)` over separable classes in
`TotallyRamifiedClass F e`. -/
theorem tsum_separable_extensionClass_inertiaDegree_div_natCardAut (e : ℕ)
    (w : FiniteExtensionClass K → ℝ≥0∞) :
    ∑' c : {c : FiniteExtensionClass K //
        c.IsSeparable ∧
          c.finrank = Module.finrank K F * e ∧ c.inertiaDegree = Module.finrank K F},
        w c.val / (c.val.natCardAut : ℝ≥0∞) =
      (Module.finrank K F : ℝ≥0∞)⁻¹ *
        ∑' x : {x : TotallyRamifiedClass F e // x.IsSeparable},
          w (x.val.restrictScalars K) / (x.val.natCardAut : ℝ≥0∞) :=
  haveI := IsUnramified.isGalois K F
  tsum_extensionClass_div_natCardAut_of_orbitEquiv K F
    (fun x : {x : TotallyRamifiedClass F e // x.IsSeparable} ↦ x.val.restrictScalars K)
    (fun x ↦ x.val.natCardAut) (fun τ x ↦ TotallyRamifiedClass.natCardAut_smul τ x.val)
    (fun x ↦ by rw [TotallyRamifiedClass.stabilizer_separable_eq, x.val.natCardAut_restrictScalars])
    (separableTotallyRamifiedOrbitEquiv K F e) (coe_separableTotallyRamifiedOrbitEquiv_mk K F) w

/-- Divisibility-form of `tsum_separable_extensionClass_inertiaDegree_div_natCardAut` for `n`
divisible by `[F : K]`. -/
theorem tsum_separable_extensionClass_inertiaDegree_div_natCardAut_of_dvd {n : ℕ}
    (hn : Module.finrank K F ∣ n) (w : FiniteExtensionClass K → ℝ≥0∞) :
    ∑' c : {c : FiniteExtensionClass K //
        c.IsSeparable ∧ c.finrank = n ∧ c.inertiaDegree = Module.finrank K F},
        w c.val / (c.val.natCardAut : ℝ≥0∞) =
      (Module.finrank K F : ℝ≥0∞)⁻¹ *
        ∑' x : {x : TotallyRamifiedClass F (n / Module.finrank K F) // x.IsSeparable},
          w (x.val.restrictScalars K) / (x.val.natCardAut : ℝ≥0∞) := by
  have h := tsum_separable_extensionClass_inertiaDegree_div_natCardAut K F
    (n / Module.finrank K F) w
  rwa [Nat.mul_div_cancel' hn] at h

end DecompositionAndWeightedSums

end TauCeti

end
