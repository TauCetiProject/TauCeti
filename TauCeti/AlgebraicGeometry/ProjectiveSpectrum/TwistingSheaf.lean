/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import TauCeti.AlgebraicGeometry.ProjectiveSpectrum.Basic

/-!
# The twisting sheaves `𝒪(n)` on `Proj`

Let `A = ⨁ᵢ 𝒜 i` be an `ℕ`-graded commutative ring and `n ∈ ℤ`. The *twisting sheaf* `𝒪(n)` on
`Proj A` is the sheaf of `𝒪_{Proj A}`-modules associated with the shifted graded module `A(n)`,
`A(n)ᵢ = A_{n + i}`. Following the construction of the structure sheaf of `Proj` in Mathlib
(`AlgebraicGeometry.Proj.structureSheaf`), we realise it concretely: a section of `𝒪(n)` over an
open `U` is a dependent function sending each point `x ∈ U` to an element of the localization
`A_x` of `A` at the homogeneous prime `x`, which is locally a fraction `r / s` with `r` and `s`
homogeneous, `s` invertible nearby, and `deg r = deg s + n`. For `n = 0` this recovers the
structure sheaf (`AlgebraicGeometry.Proj.unitIsoTwistingSheafZero`).

The twisting sheaves are the input of the graded map `A → ⨁ₙ Γ(Proj A, 𝒪(n))` sending a
homogeneous element `r` of degree `j` to the global section `r / 1` of `𝒪(j)`
(`AlgebraicGeometry.Proj.toTwistingSheaf`), and of the multiplication maps
`𝒪(m) × 𝒪(n) → 𝒪(m + n)` (`AlgebraicGeometry.Proj.twistingSheaf.mul`), which underlie
`𝒪(n) ≅ 𝒪(1)^{⊗ n}` when `A` is generated in degree one. The twisting sheaves of a relative `Proj`
restrict to these sheaves on its charts `Proj A(U)`.

## Main definitions

* `AlgebraicGeometry.ProjectiveSpectrum.TwistingSheaf.isLocallyFraction 𝒜 n`: the local predicate
  of being locally a fraction of degree `n`.
* `AlgebraicGeometry.Proj.twistingSheaf 𝒜 n`: the twisting sheaf `𝒪(n)` as an
  `𝒪_{Proj A}`-module.
* `AlgebraicGeometry.Proj.twistingSheaf.const`: the section `r / s` of `𝒪(n)` over an open on
  which the homogeneous element `s` does not vanish.
* `AlgebraicGeometry.Proj.toTwistingSheaf`: the map `A_j → Γ(U, 𝒪(n))`, `r ↦ r / 1`, for
  `j = n`.
* `AlgebraicGeometry.Proj.twistingSheaf.mul`: the `Γ(U, 𝒪)`-bilinear multiplication
  `Γ(U, 𝒪(m)) × Γ(U, 𝒪(n)) → Γ(U, 𝒪(m + n))`.
* `AlgebraicGeometry.Proj.unitIsoTwistingSheafZero`: the isomorphism `𝒪_{Proj A} ≅ 𝒪(0)`.

## References

* R. Hartshorne, *Algebraic Geometry*, Section II.5, the definition of `𝒪_X(n)`.
* [Stacks, Section 27.8, Proj of a graded ring](https://stacks.math.columbia.edu/tag/01M3)
-/

@[expose] public section

noncomputable section

namespace AlgebraicGeometry

open TopCat TopologicalSpace CategoryTheory Opposite

universe u

variable {A : Type u} {σ : Type*} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
variable (𝒜 : ℕ → σ) [GradedRing 𝒜]

namespace ProjectiveSpectrum

namespace TwistingSheaf

/-- The localization of `A` at the homogeneous prime ideal of a point of `Proj A`: the stalks of
all twisting sheaves embed into it. -/
abbrev Localizations (x : ProjectiveSpectrum 𝒜) : Type u :=
  Localization.AtPrime x.asHomogeneousIdeal.toIdeal

variable {𝒜} in
/-- A dependent function on an open `U` is a *fraction of degree `n`* if it is a fixed fraction
`r / s` with `r` and `s` homogeneous, `deg r = deg s + n` and `s` outside every point of `U`. -/
def IsFraction (n : ℤ) {U : Opens (ProjectiveSpectrum.top 𝒜)}
    (f : ∀ x : U, Localizations 𝒜 x.1) : Prop :=
  ∃ (i j : ℕ) (_ : (j : ℤ) = i + n) (r : 𝒜 j) (s : 𝒜 i)
    (s_nin : ∀ x : U, (s : A) ∉ x.1.asHomogeneousIdeal.toIdeal),
    ∀ x : U, f x = Localization.mk (r : A) ⟨s, s_nin x⟩

/-- Being a fraction of degree `n` is preserved by restriction to smaller opens. -/
def isFractionPrelocal (n : ℤ) :
    PrelocalPredicate fun x : ProjectiveSpectrum.top 𝒜 ↦ Localizations 𝒜 x where
  pred f := IsFraction n f
  res := by rintro V U i f ⟨a, b, h, r, s, hs, w⟩; exact ⟨a, b, h, r, s, (hs <| i ·), (w <| i ·)⟩

/-- The local predicate of being locally a fraction of degree `n`; the sections of the twisting
sheaf `𝒪(n)` are the dependent functions satisfying it. -/
def isLocallyFraction (n : ℤ) :
    LocalPredicate fun x : ProjectiveSpectrum.top 𝒜 ↦ Localizations 𝒜 x :=
  (isFractionPrelocal 𝒜 n).sheafify

variable {𝒜}

/-- The zero function is locally a fraction of every degree. -/
theorem isLocallyFraction_zero (n : ℤ) (U : Opens (ProjectiveSpectrum.top 𝒜)) :
    (isLocallyFraction 𝒜 n).pred (0 : ∀ x : U, Localizations 𝒜 x.1) := fun x ↦ by
  -- the denominator must have degree at least `-n`, so that the numerator `0` has degree `≥ 0`
  obtain ⟨i, hi, s, hs, hsx⟩ := x.1.exists_le_mem_notMem (-n).toNat
  refine ⟨U ⊓ ProjectiveSpectrum.basicOpen 𝒜 s, ⟨x.2, hsx⟩, homOfLE inf_le_left, i,
    (i + n).toNat, by omega, 0, ⟨s, hs⟩, fun y ↦ y.2.2, fun y ↦ ?_⟩
  exact (Localization.mk_zero _).symm

theorem isLocallyFraction_add {n : ℤ} {U : Opens (ProjectiveSpectrum.top 𝒜)}
    {f g : ∀ x : U, Localizations 𝒜 x.1} (hf : (isLocallyFraction 𝒜 n).pred f)
    (hg : (isLocallyFraction 𝒜 n).pred g) : (isLocallyFraction 𝒜 n).pred (f + g) := by
  intro x
  obtain ⟨Va, ma, ia, ia', ja, hja, ra, sa, hsa, wa⟩ := hf x
  obtain ⟨Vb, mb, ib, ib', jb, hjb, rb, sb, hsb, wb⟩ := hg x
  refine ⟨Va ⊓ Vb, ⟨ma, mb⟩, Opens.infLELeft _ _ ≫ ia, ia' + ib', ja + ib', by push_cast; omega,
    ⟨sb * ra + sa * rb, add_mem (by simpa [add_comm] using SetLike.mul_mem_graded sb.2 ra.2)
      (by convert SetLike.mul_mem_graded sa.2 rb.2 using 2; omega)⟩,
    ⟨sa * sb, SetLike.mul_mem_graded sa.2 sb.2⟩,
    fun y h ↦ (y.1.isPrime.mem_or_mem h).elim (hsa ⟨y.1, y.2.1⟩) (hsb ⟨y.1, y.2.2⟩),
    fun y ↦ ?_⟩
  refine (congrArg₂ (· + ·) (wa ⟨y.1, y.2.1⟩) (wb ⟨y.1, y.2.2⟩)).trans ?_
  rw [Localization.add_mk, add_comm]
  rfl

theorem isLocallyFraction_neg {n : ℤ} {U : Opens (ProjectiveSpectrum.top 𝒜)}
    {f : ∀ x : U, Localizations 𝒜 x.1} (hf : (isLocallyFraction 𝒜 n).pred f) :
    (isLocallyFraction 𝒜 n).pred (-f) := by
  intro x
  obtain ⟨V, m, i, a, b, h, r, s, hs, w⟩ := hf x
  exact ⟨V, m, i, a, b, h, -r, s, hs, fun y ↦
    (congrArg Neg.neg (w y)).trans (Localization.neg_mk _ _)⟩

/-- The product of a local fraction of degree `m` and a local fraction of degree `n` is a local
fraction of degree `m + n`. -/
theorem isLocallyFraction_mul {m n : ℤ} {U : Opens (ProjectiveSpectrum.top 𝒜)}
    {f g : ∀ x : U, Localizations 𝒜 x.1} (hf : (isLocallyFraction 𝒜 m).pred f)
    (hg : (isLocallyFraction 𝒜 n).pred g) : (isLocallyFraction 𝒜 (m + n)).pred (f * g) := by
  intro x
  obtain ⟨Va, ma, ia, ia', ja, hja, ra, sa, hsa, wa⟩ := hf x
  obtain ⟨Vb, mb, ib, ib', jb, hjb, rb, sb, hsb, wb⟩ := hg x
  refine ⟨Va ⊓ Vb, ⟨ma, mb⟩, Opens.infLELeft _ _ ≫ ia, ia' + ib', ja + jb, by push_cast; omega,
    ⟨ra * rb, SetLike.mul_mem_graded ra.2 rb.2⟩, ⟨sa * sb, SetLike.mul_mem_graded sa.2 sb.2⟩,
    fun y h ↦ (y.1.isPrime.mem_or_mem h).elim (hsa ⟨y.1, y.2.1⟩) (hsb ⟨y.1, y.2.2⟩),
    fun y ↦ ?_⟩
  exact (congrArg₂ (· * ·) (wa ⟨y.1, y.2.1⟩) (wb ⟨y.1, y.2.2⟩)).trans (Localization.mk_mul ..)

/-- Sections of the structure sheaf of `Proj`, viewed in the localizations, are local fractions
of degree `0`. -/
theorem isLocallyFraction_val {U : Opens (ProjectiveSpectrum.top 𝒜)} (a : Γ(Proj 𝒜, U)) :
    (isLocallyFraction 𝒜 0).pred fun x ↦ (a.1 x).val := by
  intro x
  obtain ⟨V, m, i, j, r, s, hs, w⟩ := a.2 x
  exact ⟨V, m, i, j, j, by simp, r, s, hs, fun y ↦
    (congrArg HomogeneousLocalization.val (w y)).trans (HomogeneousLocalization.val_mk _)⟩

/-- Conversely, a local fraction of degree `0` takes values in the homogeneous localizations. -/
theorem exists_val_eq {U : Opens (ProjectiveSpectrum.top 𝒜)}
    {f : ∀ x : U, Localizations 𝒜 x.1} (hf : (isLocallyFraction 𝒜 0).pred f) (x : U) :
    ∃ a : HomogeneousLocalization 𝒜 _, a.val = f x := by
  obtain ⟨V, m, i, a, b, h, r, s, hs, w⟩ := hf x
  obtain rfl : b = a := by omega
  exact ⟨.mk ⟨b, r, s, hs ⟨x, m⟩⟩, (HomogeneousLocalization.val_mk _).trans (w ⟨x, m⟩).symm⟩

variable (𝒜) in
/-- The local fractions of degree `n` on `U`, as an additive subgroup of all dependent functions
into the localizations. -/
def sectionsAddSubgroup (n : ℤ) (U : Opens (ProjectiveSpectrum.top 𝒜)) :
    AddSubgroup (∀ x : U, Localizations 𝒜 x.1) where
  carrier := {f | (isLocallyFraction 𝒜 n).pred f}
  zero_mem' := isLocallyFraction_zero n U
  add_mem' := isLocallyFraction_add
  neg_mem' := isLocallyFraction_neg

/-- Sections of the structure sheaf of `Proj` act on local fractions of degree `n` pointwise,
through the inclusions `A_{(x)} → A_x` of the homogeneous localizations. -/
instance sectionsAddSubgroup.smul (n : ℤ) (U : Opens (ProjectiveSpectrum.top 𝒜)) :
    SMul Γ(Proj 𝒜, U) (sectionsAddSubgroup 𝒜 n U) where
  smul a f := ⟨fun x ↦ (a.1 x).val * f.1 x, by
    have := isLocallyFraction_mul (isLocallyFraction_val a) f.2
    rw [zero_add] at this
    exact this⟩

/-- The local fractions of degree `n` on `U` form a module over the sections of the structure
sheaf of `Proj` on `U`. -/
instance sectionsAddSubgroup.module (n : ℤ) (U : Opens (ProjectiveSpectrum.top 𝒜)) :
    Module Γ(Proj 𝒜, U) (sectionsAddSubgroup 𝒜 n U) where
  one_smul f := Subtype.ext <| funext fun x ↦
    (congrArg (· * f.1 x) HomogeneousLocalization.val_one).trans (one_mul _)
  mul_smul _ _ f := Subtype.ext <| funext fun x ↦
    (congrArg (· * f.1 x) (HomogeneousLocalization.val_mul _ _)).trans (mul_assoc _ _ _)
  smul_zero _ := Subtype.ext <| funext fun _ ↦ mul_zero _
  smul_add _ _ _ := Subtype.ext <| funext fun _ ↦ mul_add _ _ _
  add_smul _ _ f := Subtype.ext <| funext fun x ↦
    (congrArg (· * f.1 x) (HomogeneousLocalization.val_add _ _)).trans (add_mul _ _ _)
  zero_smul f := Subtype.ext <| funext fun x ↦
    (congrArg (· * f.1 x) HomogeneousLocalization.val_zero).trans (zero_mul _)

variable (𝒜)

/-- The twisting sheaf `𝒪(n)` as a sheaf of types: the subsheaf of dependent functions into the
localizations which are locally fractions of degree `n`. -/
def twistingSheafInType (n : ℤ) : Sheaf (Type u) (ProjectiveSpectrum.top 𝒜) :=
  subsheafToTypes (isLocallyFraction 𝒜 n)

/-- The twisting sheaf `𝒪(n)` as a presheaf of abelian groups. -/
def twistingPresheafInAb (n : ℤ) : (Opens (ProjectiveSpectrum.top 𝒜))ᵒᵖ ⥤ Ab.{u} where
  obj U := AddCommGrpCat.of (sectionsAddSubgroup 𝒜 n U.unop)
  map i := AddCommGrpCat.ofHom
    { toFun f := ⟨fun x ↦ f.1 (i.unop x), (isLocallyFraction 𝒜 n).res i.unop f.1 f.2⟩
      map_zero' := rfl
      map_add' _ _ := rfl }
  map_id _ := rfl
  map_comp _ _ := rfl

/-- The presheaf of abelian groups `𝒪(n)` has the sheaf of types `𝒪(n)` as underlying presheaf
of types. -/
def twistingPresheafInAbCompForget (n : ℤ) :
    twistingPresheafInAb 𝒜 n ⋙ forget Ab ≅ (twistingSheafInType 𝒜 n).obj :=
  NatIso.ofComponents (fun _ ↦ Iso.refl _) fun _ ↦ rfl

/-- The twisting sheaf `𝒪(n)` as a presheaf of modules over the structure sheaf of `Proj`. -/
def twistingPresheaf (n : ℤ) : PresheafOfModules.{u} (Proj 𝒜).ringCatSheaf.obj :=
  letI (U : (Proj 𝒜).Opensᵒᵖ) :
      Module ((Proj 𝒜).ringCatSheaf.obj.obj U) ((twistingPresheafInAb 𝒜 n).obj U) :=
    sectionsAddSubgroup.module n U.unop
  .ofPresheaf (twistingPresheafInAb 𝒜 n) fun _ _ _ _ _ ↦ rfl

end TwistingSheaf

end ProjectiveSpectrum

open ProjectiveSpectrum.TwistingSheaf

namespace Proj

/-- The **twisting sheaf** `𝒪(n)` on `Proj A`, for `n ∈ ℤ`: the sheaf of `𝒪_{Proj A}`-modules
whose sections over `U` are the dependent functions `x ↦ f x ∈ A_x` on `U` which are locally
fractions `r / s` of homogeneous elements with `deg r = deg s + n`. -/
def twistingSheaf (n : ℤ) : (Proj 𝒜).Modules where
  val := twistingPresheaf 𝒜 n
  isSheaf := (TopCat.Presheaf.isSheaf_iff_isSheaf_comp (forget AddCommGrpCat) _).2
    (TopCat.Presheaf.isSheaf_of_iso (twistingPresheafInAbCompForget 𝒜 n).symm
      (twistingSheafInType 𝒜 n).2)

namespace twistingSheaf

variable {𝒜} {n : ℤ} {U V : (Proj 𝒜).Opens}

/-- A section of `𝒪(n)` is determined by its values in the localizations. -/
@[ext]
theorem ext {s t : Γ(twistingSheaf 𝒜 n, U)} (h : ∀ x, s.1 x = t.1 x) : s = t :=
  Subtype.ext (funext h)

@[simp]
theorem res_apply (i : V ⟶ U) (s : Γ(twistingSheaf 𝒜 n, U)) (x : V) :
    ((twistingSheaf 𝒜 n).presheaf.map i.op s).1 x = s.1 (i x) :=
  (rfl)

@[simp]
theorem zero_apply (x : U) : (0 : Γ(twistingSheaf 𝒜 n, U)).1 x = 0 :=
  (rfl)

@[simp]
theorem add_apply (s t : Γ(twistingSheaf 𝒜 n, U)) (x : U) : (s + t).1 x = s.1 x + t.1 x :=
  (rfl)

@[simp]
theorem neg_apply (s : Γ(twistingSheaf 𝒜 n, U)) (x : U) : (-s).1 x = -s.1 x :=
  (rfl)

@[simp]
theorem sub_apply (s t : Γ(twistingSheaf 𝒜 n, U)) (x : U) : (s - t).1 x = s.1 x - t.1 x :=
  (rfl)

/-- Sections of the structure sheaf act on sections of `𝒪(n)` pointwise, through the inclusions
`A_{(x)} → A_x` of the homogeneous localizations. -/
@[simp]
theorem smul_apply (a : Γ(Proj 𝒜, U)) (s : Γ(twistingSheaf 𝒜 n, U)) (x : U) :
    (a • s).1 x = (a.1 x).val * s.1 x :=
  (rfl)

/-- The section `r / s` of `𝒪(n)` on an open `U` on which the homogeneous element `s` does not
vanish, for homogeneous `r` and `s` with `deg r = deg s + n`. -/
def const {i j : ℕ} (h : (j : ℤ) = i + n) (r s : A) (hr : r ∈ 𝒜 j) (hs : s ∈ 𝒜 i)
    (U : (Proj 𝒜).Opens) (hU : U ≤ basicOpen 𝒜 s) : Γ(twistingSheaf 𝒜 n, U) :=
  ⟨fun x ↦ Localization.mk r ⟨s, hU x.2⟩, fun x ↦ ⟨U, x.2, 𝟙 U, i, j, h, ⟨r, hr⟩, ⟨s, hs⟩,
    fun y ↦ hU y.2, fun _ ↦ rfl⟩⟩

@[simp]
theorem const_apply {i j : ℕ} (h : (j : ℤ) = i + n) (r s : A) (hr : r ∈ 𝒜 j) (hs : s ∈ 𝒜 i)
    (hU : U ≤ basicOpen 𝒜 s) (x : U) :
    (const h r s hr hs U hU).1 x = Localization.mk r ⟨s, hU x.2⟩ :=
  (rfl)

@[simp]
theorem res_const {i j : ℕ} (h : (j : ℤ) = i + n) (r s : A) (hr : r ∈ 𝒜 j) (hs : s ∈ 𝒜 i)
    (hU : U ≤ basicOpen 𝒜 s) (iVU : V ⟶ U) :
    (twistingSheaf 𝒜 n).presheaf.map iVU.op (const h r s hr hs U hU) =
      const h r s hr hs V (iVU.le.trans hU) :=
  (rfl)

/-- Every section of `𝒪(n)` is locally of the form `r / s`. -/
theorem exists_const (s : Γ(twistingSheaf 𝒜 n, U)) (x : Proj 𝒜) (hx : x ∈ U) :
    ∃ (V : (Proj 𝒜).Opens) (_ : x ∈ V) (iVU : V ⟶ U) (i j : ℕ) (h : (j : ℤ) = i + n)
      (r t : A) (hr : r ∈ 𝒜 j) (ht : t ∈ 𝒜 i) (hV : V ≤ basicOpen 𝒜 t),
      (twistingSheaf 𝒜 n).presheaf.map iVU.op s = const h r t hr ht V hV := by
  obtain ⟨V, hxV, iVU, i, j, h, r, t, ht, w⟩ := s.2 ⟨x, hx⟩
  exact ⟨V, hxV, iVU, i, j, h, r, t, r.2, t.2, fun y hy ↦ ht ⟨y, hy⟩, ext fun y ↦ w y⟩

variable (𝒜 U) in
/-- The multiplication `Γ(U, 𝒪(m)) × Γ(U, 𝒪(n)) → Γ(U, 𝒪(m + n))`, bilinear over the sections of
the structure sheaf: sections are multiplied pointwise in the localizations. -/
def mul (m n : ℤ) :
    Γ(twistingSheaf 𝒜 m, U) →ₗ[Γ(Proj 𝒜, U)] Γ(twistingSheaf 𝒜 n, U) →ₗ[Γ(Proj 𝒜, U)]
      Γ(twistingSheaf 𝒜 (m + n), U) :=
  LinearMap.mk₂ Γ(Proj 𝒜, U) (fun s t ↦ ⟨s.1 * t.1, isLocallyFraction_mul s.2 t.2⟩)
    (fun _ _ _ ↦ ext fun _ ↦ add_mul _ _ _)
    (fun _ _ _ ↦ ext fun _ ↦ mul_assoc _ _ _)
    (fun _ _ _ ↦ ext fun _ ↦ mul_add _ _ _)
    (fun _ _ _ ↦ ext fun _ ↦ mul_left_comm _ _ _)

@[simp]
theorem mul_apply {m : ℤ} (s : Γ(twistingSheaf 𝒜 m, U)) (t : Γ(twistingSheaf 𝒜 n, U)) (x : U) :
    (mul 𝒜 U m n s t).1 x = s.1 x * t.1 x :=
  (rfl)

/-- The multiplication of sections of twisting sheaves commutes with restriction. -/
@[simp]
theorem res_mul {m : ℤ} (i : V ⟶ U) (s : Γ(twistingSheaf 𝒜 m, U))
    (t : Γ(twistingSheaf 𝒜 n, U)) :
    (twistingSheaf 𝒜 (m + n)).presheaf.map i.op (mul 𝒜 U m n s t) =
      mul 𝒜 V m n ((twistingSheaf 𝒜 m).presheaf.map i.op s)
        ((twistingSheaf 𝒜 n).presheaf.map i.op t) :=
  (rfl)

@[simp]
theorem mul_const {m : ℤ} {i j i' j' : ℕ} (h : (j : ℤ) = i + m) (h' : (j' : ℤ) = i' + n)
    (r s r' s' : A) (hr : r ∈ 𝒜 j) (hs : s ∈ 𝒜 i) (hr' : r' ∈ 𝒜 j') (hs' : s' ∈ 𝒜 i')
    (hU : U ≤ basicOpen 𝒜 s) (hU' : U ≤ basicOpen 𝒜 s') :
    mul 𝒜 U m n (const h r s hr hs U hU) (const h' r' s' hr' hs' U hU') =
      const (by push_cast; omega) (r * r') (s * s') (SetLike.mul_mem_graded hr hr')
        (SetLike.mul_mem_graded hs hs') U
        (fun x hx ↦ by simpa [basicOpen_mul] using And.intro (hU hx) (hU' hx)) :=
  ext fun _ ↦ Localization.mk_mul ..

end twistingSheaf

open twistingSheaf

variable {𝒜} {n : ℤ} {U V : (Proj 𝒜).Opens}

variable (𝒜) in
/-- The map `r ↦ r / 1` from the homogeneous elements of degree `j` to the sections of `𝒪(n)`,
for `j = n`. Over `U = ⊤`, these are the components of the graded map
`A → ⨁ₙ Γ(Proj A, 𝒪(n))`. -/
def toTwistingSheaf {j : ℕ} (h : (j : ℤ) = n) (U : (Proj 𝒜).Opens) :
    𝒜 j →+ Γ(twistingSheaf 𝒜 n, U) where
  toFun r := twistingSheaf.const (i := 0) (by omega) (r : A) 1 r.2 SetLike.GradedOne.one_mem U
    (by simp [basicOpen_one])
  map_zero' := twistingSheaf.ext fun _ ↦ Localization.mk_zero _
  map_add' r r' := twistingSheaf.ext fun _ ↦ (Localization.add_mk_self _ _ _).symm

@[simp]
theorem toTwistingSheaf_apply_apply {j : ℕ} (h : (j : ℤ) = n) (U : (Proj 𝒜).Opens) (r : 𝒜 j)
    (x : U) : (toTwistingSheaf 𝒜 h U r).1 x = Localization.mk (r : A) 1 :=
  (rfl)

/-- The sections `r / 1` are compatible with restriction. -/
@[simp]
theorem res_toTwistingSheaf {j : ℕ} (h : (j : ℤ) = n) (i : V ⟶ U) (r : 𝒜 j) :
    (twistingSheaf 𝒜 n).presheaf.map i.op (toTwistingSheaf 𝒜 h U r) =
      toTwistingSheaf 𝒜 h V r :=
  (rfl)

/-- The map `A → ⨁ₙ Γ(U, 𝒪(n))` is multiplicative. -/
@[simp]
theorem mul_toTwistingSheaf {m : ℤ} {i j : ℕ} (hi : (i : ℤ) = m) (hj : (j : ℤ) = n)
    (U : (Proj 𝒜).Opens) (r : 𝒜 i) (r' : 𝒜 j) :
    mul 𝒜 U m n (toTwistingSheaf 𝒜 hi U r) (toTwistingSheaf 𝒜 hj U r') =
      toTwistingSheaf 𝒜 (by push_cast; omega) U ⟨r * r', SetLike.mul_mem_graded r.2 r'.2⟩ :=
  twistingSheaf.ext fun _ ↦ (Localization.mk_mul ..).trans (congrArg _ (Subtype.ext (mul_one 1)))

variable (𝒜) in
/-- Over every open `U`, the sections of the structure sheaf of `Proj` are the sections of
`𝒪(0)`: the inclusions `A_{(x)} → A_x` identify the local fractions of degree `0` in the
homogeneous localizations with those in the localizations. -/
def sectionsLinearEquivTwistingSheafZero (U : (Proj 𝒜).Opens) :
    Γ(Proj 𝒜, U) ≃ₗ[Γ(Proj 𝒜, U)] Γ(twistingSheaf 𝒜 0, U) where
  toFun a := ⟨fun x ↦ (a.1 x).val, isLocallyFraction_val a⟩
  map_add' a b := twistingSheaf.ext fun x ↦ HomogeneousLocalization.val_add _ _
  map_smul' a b := twistingSheaf.ext fun x ↦ HomogeneousLocalization.val_mul _ _
  invFun f := ⟨fun x ↦ (exists_val_eq f.2 x).choose, fun x ↦ by
    obtain ⟨V, m, iVU, i, j, h, r, s, hs, w⟩ := f.2 x
    obtain rfl : j = i := by omega
    refine ⟨V, m, iVU, j, r, s, hs, fun y ↦ HomogeneousLocalization.val_injective _ ?_⟩
    rw [HomogeneousLocalization.val_mk]
    exact (exists_val_eq f.2 (iVU y)).choose_spec.trans (w y)⟩
  left_inv a := Subtype.ext <| funext fun x ↦ HomogeneousLocalization.val_injective _
    (exists_val_eq (isLocallyFraction_val a) x).choose_spec
  right_inv f := twistingSheaf.ext fun x ↦ (exists_val_eq f.2 x).choose_spec

@[simp]
theorem sectionsLinearEquivTwistingSheafZero_apply_apply (U : (Proj 𝒜).Opens) (a : Γ(Proj 𝒜, U))
    (x : U) : (sectionsLinearEquivTwistingSheafZero 𝒜 U a).1 x = (a.1 x).val :=
  (rfl)

variable (𝒜) in
/-- **The twisting sheaf `𝒪(0)` is the structure sheaf of `Proj`.** -/
def unitIsoTwistingSheafZero : SheafOfModules.unit (Proj 𝒜).ringCatSheaf ≅ twistingSheaf 𝒜 0 :=
  (SheafOfModules.fullyFaithfulForget _).preimageIso <| PresheafOfModules.isoMk
    (fun U ↦ (sectionsLinearEquivTwistingSheafZero 𝒜 U.unop).toModuleIso) fun _ _ _ ↦ rfl

@[simp]
theorem unitIsoTwistingSheafZero_hom_app_apply (U : (Proj 𝒜).Opens) (a : Γ(Proj 𝒜, U)) :
    Scheme.Modules.Hom.app (unitIsoTwistingSheafZero 𝒜).hom U a =
      sectionsLinearEquivTwistingSheafZero 𝒜 U a :=
  (rfl)

@[simp]
theorem unitIsoTwistingSheafZero_inv_app_apply (U : (Proj 𝒜).Opens)
    (f : Γ(twistingSheaf 𝒜 0, U)) :
    Scheme.Modules.Hom.app (unitIsoTwistingSheafZero 𝒜).inv U f =
      (sectionsLinearEquivTwistingSheafZero 𝒜 U).symm f :=
  (rfl)

end Proj

end AlgebraicGeometry
