/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Points.Equalizer
public import TauCeti.Algebra.AlgebraicGroup.Smooth.CommHopfAlgCat
public import TauCeti.RingTheory.Invariant.FixedPointIdeal

/-!
# Fixed-point subgroup schemes and Edixhoven's smoothness theorem

A family of endomorphisms `f : ι → (H ⟶ H)` of a commutative Hopf algebra `H` over `R` represents,
contravariantly, a family of endomorphisms of the affine group scheme `Spec H`. The supremum
`fixedPointHopfIdeal f = ⨆ i, equalizerHopfIdeal (f i) (𝟙 H)` is a Hopf ideal of `H` whose quotient
cuts out the simultaneous fixed-point closed subgroup scheme: its `A`-points are the `A`-points of
`H` fixed by `BialgHom.mapDomain (f i).hom` for every `i`.

When a finite group `Θ` of order invertible in `k` acts on a commutative Hopf algebra `H` over `k`
by group-scheme automorphisms (`ρ : Θ →* CategoryTheory.Aut H`), the underlying ideal of
`fixedPointHopfIdeal` coincides with `TauCeti.MulSemiringAction.fixedPointIdeal Θ H`. Applying
`TauCeti.MulSemiringAction.smooth_quotient_fixedPointIdeal_of_isUnit` gives **Edixhoven's
smoothness theorem for group-scheme fixed points**
(`CommHopfAlgCat.smoothCommHopfAlgProperty_quotient_fixedPointHopfIdeal`,
`FiniteTypeCommHopfAlgCat.smooth_fixedPoints`): if `H` is smooth over `k`, then `H^Θ` is
represented by a smooth closed subgroup scheme (of finite type when `H` is of finite type).

Diagonalizable-group fixed-point calculations (including `(𝔾ₘ)^{inv} ≅ μ₂` and
`(𝔾ₘ²)^{swap} ≅ 𝔾ₘ`) are developed in
`TauCeti.Algebra.AlgebraicGroup.DiagonalizableGroup.FixedPoints`.

## Main declarations

* `TauCeti.CommHopfAlgCat.fixedPointHopfIdeal`: the Hopf ideal cutting out the simultaneous fixed
  locus of a family of endomorphisms `f : ι → (H ⟶ H)`, with
  `TauCeti.CommHopfAlgCat.fixedPointHopfIdeal_toIdeal`,
  `TauCeti.CommHopfAlgCat.fixedPointHopfIdeal_le_iff`,
  `TauCeti.CommHopfAlgCat.fixedPointHopfIdeal_le_ker_iff`,
  `TauCeti.CommHopfAlgCat.mem_quotientPointsSubgroup_fixedPointHopfIdeal_iff`, and
  `TauCeti.CommHopfAlgCat.range_mapDomain_mkQuotient_fixedPointHopfIdeal`.
* `TauCeti.CommHopfAlgCat.autActionToAlgEquiv`,
  `TauCeti.CommHopfAlgCat.fixedPointHopfIdeal_aut_toIdeal_eq_mulSemiringActionFixedPointIdeal`, and
  `TauCeti.CommHopfAlgCat.smoothCommHopfAlgProperty_quotient_fixedPointHopfIdeal`: the algebra
  action, ideal comparison, and smoothness theorem for `ρ : Θ →* CategoryTheory.Aut H` in
  `CommHopfAlgCat`.
* `TauCeti.FiniteTypeCommHopfAlgCat.fixedPointHopfIdeal`: the fixed-point Hopf ideal of an action
  `ρ : Θ →* CategoryTheory.Aut H` in `FiniteTypeCommHopfAlgCat`, with
  `TauCeti.FiniteTypeCommHopfAlgCat.autActionToAlgEquiv`,
  `TauCeti.FiniteTypeCommHopfAlgCat.quotientFixedPointHopfIdealIsoOfEqOne` for trivial actions, and
  `TauCeti.FiniteTypeCommHopfAlgCat.smoothCommHopfAlgProperty_quotient_fixedPointHopfIdeal`.
* `TauCeti.FiniteTypeCommHopfAlgCat.smooth_fixedPoints`: Edixhoven's theorem that fixed points of a
  finite group of invertible order acting on a smooth finite-type affine group scheme form a smooth
  closed subgroup scheme.

## References

* B. Edixhoven, *Néron models and tame ramification*, Compositio Math. 81 (1992), Proposition 3.1
  (p. 293) and Proposition 3.4 (pp. 294–295).
* J. S. Milne, *Algebraic Groups* (2017), §1.h.
-/

public noncomputable section

open _root_.CommHopfAlgCat _root_.CommHopfAlgCat.Hom
open CategoryTheory WithConv

namespace TauCeti

universe u v w x

namespace CommHopfAlgCat

variable {R : Type u} [CommRing R] {H : _root_.CommHopfAlgCat.{v} R}

/-- The **fixed-point Hopf ideal** of a family of endomorphisms `f : ι → (H ⟶ H)` of a commutative
Hopf algebra: the join `⨆ i, equalizerHopfIdeal (f i) (𝟙 H)`.

Contravariantly, the quotient `H ⧸ fixedPointHopfIdeal f` is the coordinate Hopf algebra of the
closed subgroup scheme of `Spec H` fixed simultaneously by every endomorphism in the family. -/
def fixedPointHopfIdeal {ι : Sort w} (f : ι → (H ⟶ H)) : HopfIdeal R H :=
  ⨆ i, equalizerHopfIdeal (f i) (𝟙 H)

/-- Definition of `fixedPointHopfIdeal` as a supremum of equalizer Hopf ideals. -/
theorem fixedPointHopfIdeal_def {ι : Sort w} (f : ι → (H ⟶ H)) :
    fixedPointHopfIdeal f = ⨆ i, equalizerHopfIdeal (f i) (𝟙 H) :=
  (rfl)

/-- Universal property among Hopf ideals: `fixedPointHopfIdeal f` is the smallest Hopf ideal
containing every displacement `(f i).hom a - a`. -/
theorem fixedPointHopfIdeal_le_iff {ι : Sort w} {f : ι → (H ⟶ H)} {J : HopfIdeal R H} :
    fixedPointHopfIdeal f ≤ J ↔ ∀ i (a : H), (f i).hom a - a ∈ J := by
  rw [← HopfIdeal.toIdeal_le_toIdeal, fixedPointHopfIdeal_def, HopfIdeal.iSup_toIdeal, iSup_le_iff]
  refine forall_congr' fun i ↦ ?_
  rw [HopfIdeal.toIdeal_le_toIdeal, equalizerHopfIdeal_le_iff]
  simp

/-- Every displacement `(f i).hom a - a` lies in `fixedPointHopfIdeal f`. -/
theorem sub_mem_fixedPointHopfIdeal {ι : Sort w} (f : ι → (H ⟶ H)) (i : ι) (a : H) :
    (f i).hom a - a ∈ fixedPointHopfIdeal f :=
  (fixedPointHopfIdeal_le_iff.mp le_rfl) i a

/-- The underlying ideal of `fixedPointHopfIdeal f` is the ideal generated by all displacements
`(f i).hom y - y`. -/
theorem fixedPointHopfIdeal_toIdeal {ι : Sort w} (f : ι → (H ⟶ H)) :
    (fixedPointHopfIdeal f).toIdeal = Ideal.span {x : H | ∃ i y, (f i).hom y - y = x} := by
  apply le_antisymm
  · rw [fixedPointHopfIdeal_def, HopfIdeal.iSup_toIdeal, iSup_le_iff]
    intro i
    rw [equalizerHopfIdeal_toIdeal, HopfIdeal.equalizerIdeal_le_iff]
    intro y
    exact Ideal.subset_span ⟨i, y, rfl⟩
  · rw [Ideal.span_le]
    rintro _ ⟨i, y, rfl⟩
    exact HopfIdeal.mem_toIdeal.mpr (sub_mem_fixedPointHopfIdeal f i y)

/-- A ring homomorphism out of `H` kills `fixedPointHopfIdeal f` if and only if it equalizes each
`f i` with the identity. -/
theorem fixedPointHopfIdeal_le_ker_iff {ι : Sort w} {A : Type*} [Ring A] (f : ι → (H ⟶ H))
    (φ : H →+* A) :
    (fixedPointHopfIdeal f).toIdeal ≤ RingHom.ker φ ↔ ∀ i (a : H), φ ((f i).hom a) = φ a := by
  rw [fixedPointHopfIdeal_def, HopfIdeal.iSup_toIdeal, iSup_le_iff]
  refine forall_congr' fun i ↦ ?_
  rw [equalizerHopfIdeal_le_ker_iff]
  simp

/-- A morphism out of `H` kills `fixedPointHopfIdeal f` if and only if it coequalizes every `f i`
with `𝟙 H`. -/
theorem fixedPointHopfIdeal_toIdeal_le_ker_iff {ι : Sort w} {T : _root_.CommHopfAlgCat.{v} R}
    (f : ι → (H ⟶ H)) (p : H ⟶ T) :
    (fixedPointHopfIdeal f).toIdeal ≤ RingHom.ker p.hom.toAlgHom.toRingHom ↔
      ∀ i, f i ≫ p = p := by
  rw [fixedPointHopfIdeal_def, HopfIdeal.iSup_toIdeal, iSup_le_iff]
  refine forall_congr' fun i ↦ ?_
  rw [equalizerHopfIdeal_toIdeal_le_ker_iff, Category.id_comp]

/-- `fixedPointHopfIdeal f` vanishes if and only if every `f i` is the identity morphism. -/
@[simp]
theorem fixedPointHopfIdeal_eq_bot_iff {ι : Sort w} (f : ι → (H ⟶ H)) :
    fixedPointHopfIdeal f = ⊥ ↔ ∀ i, f i = 𝟙 H := by
  refine ⟨fun h i ↦ (equalizerHopfIdeal_eq_bot_iff (f i) (𝟙 H)).mp (le_bot_iff.mp ?_),
    fun h ↦ le_bot_iff.mp ?_⟩
  · rw [← HopfIdeal.toIdeal_le_toIdeal, ← h, fixedPointHopfIdeal_def, HopfIdeal.iSup_toIdeal]
    exact le_iSup (fun j ↦ (equalizerHopfIdeal (f j) (𝟙 H)).toIdeal) i
  · rw [← HopfIdeal.toIdeal_le_toIdeal, fixedPointHopfIdeal_def, HopfIdeal.iSup_toIdeal,
      iSup_le_iff]
    intro i
    rw [(equalizerHopfIdeal_eq_bot_iff (f i) (𝟙 H)).mpr (h i)]

/-- The quotient morphism `mkQuotient H (fixedPointHopfIdeal f)` coequalizes every `f i` with the
identity. -/
@[reassoc (attr := simp)]
theorem comp_mkQuotient_fixedPointHopfIdeal {ι : Sort w} (f : ι → (H ⟶ H)) (i : ι) :
    f i ≫ mkQuotient H (fixedPointHopfIdeal f) = mkQuotient H (fixedPointHopfIdeal f) :=
  ((fixedPointHopfIdeal_toIdeal_le_ker_iff f (mkQuotient H (fixedPointHopfIdeal f))).mp
    (mkQuotient_ker H _).ge) i

/-- **Points of the fixed-point subgroup.** An `A`-point of `H` lies in the subgroup cut out by
`fixedPointHopfIdeal f` if and only if it is fixed by `BialgHom.mapDomain (f i).hom` for every
`i`. -/
theorem mem_quotientPointsSubgroup_fixedPointHopfIdeal_iff {ι : Sort w} (f : ι → (H ⟶ H))
    (A : CommAlgCat.{x} R) (g : HopfAlgebra.points (R := R) (H := H) A) :
    g ∈ quotientPointsSubgroup H (fixedPointHopfIdeal f) A ↔
      ∀ i, BialgHom.mapDomain (f i).hom g = g := by
  have hle (I : HopfIdeal R H) :
      g ∈ quotientPointsSubgroup H I A ↔
        I.toIdeal ≤ RingHom.ker (g.ofConv : H →ₐ[R] A).toRingHom := by
    rw [mem_quotientPointsSubgroup_iff]
    exact ⟨fun h _ hx ↦ RingHom.mem_ker.mpr (h _ (HopfIdeal.mem_toIdeal.mp hx)),
      fun h _ hx ↦ RingHom.mem_ker.mp (h (HopfIdeal.mem_toIdeal.mpr hx))⟩
  have hid : BialgHom.mapDomain (_root_.CommHopfAlgCat.Hom.hom (𝟙 H)) g = g := by
    change BialgHom.mapDomain (BialgHom.id R H) g = g
    rw [BialgHom.mapDomain_id, MonoidHom.id_apply]
  rw [hle, fixedPointHopfIdeal_def, HopfIdeal.iSup_toIdeal, iSup_le_iff]
  refine forall_congr' fun i ↦ ?_
  rw [← hle, mem_quotientPointsSubgroup_equalizerHopfIdeal_iff, hid]

/-- **Image on points of `mkQuotient H (fixedPointHopfIdeal f)`.** For every commutative
`R`-algebra `A`, the image of `A`-points of the quotient `H ⧸ fixedPointHopfIdeal f` inside the
`A`-points of `H` is the set of points fixed by every `f i`. -/
theorem range_mapDomain_mkQuotient_fixedPointHopfIdeal {ι : Sort w} (f : ι → (H ⟶ H))
    (A : Type x) [CommRing A] [Algebra R A] :
    Set.range (BialgHom.mapDomain (A := A) (mkQuotient H (fixedPointHopfIdeal f)).hom) =
      {g | ∀ i, BialgHom.mapDomain (A := A) (f i).hom g = g} := by
  ext g
  have hhom :
      (quotientPointsHom H (fixedPointHopfIdeal f) (CommAlgCat.of R A)).hom =
        BialgHom.mapDomain (A := A) (mkQuotient H (fixedPointHopfIdeal f)).hom :=
    ConcreteCategory.hom_ofHom _
  rw [Set.mem_range, ← MonoidHom.mem_range, ← hhom]
  exact mem_quotientPointsSubgroup_fixedPointHopfIdeal_iff f (CommAlgCat.of R A) g

section AutAction

/-- Monoid homomorphism `Θ →* (H ≃ₐ[R] H)` induced by a categorical action
`ρ : Θ →* CategoryTheory.Aut H` on a commutative Hopf algebra. -/
def autActionToAlgEquiv {Θ : Type w} [Monoid Θ] (ρ : Θ →* CategoryTheory.Aut H) :
    Θ →* (H ≃ₐ[R] H) where
  toFun θ := (_root_.CommHopfAlgCat.ofIso (ρ θ).asIso).toAlgEquiv
  map_one' := AlgEquiv.ext fun x ↦ by simp [_root_.CommHopfAlgCat.ofIso_apply]
  map_mul' θ₁ θ₂ := AlgEquiv.ext fun x ↦ by simp [_root_.CommHopfAlgCat.ofIso_apply]

/-- `autActionToAlgEquiv ρ θ` acts on elements via the underlying bialgebra morphism of `ρ θ`. -/
@[simp]
theorem autActionToAlgEquiv_apply {Θ : Type w} [Monoid Θ] (ρ : Θ →* CategoryTheory.Aut H)
    (θ : Θ) (x : H) :
    autActionToAlgEquiv ρ θ x = (ρ θ).asIso.hom.hom x :=
  _root_.CommHopfAlgCat.ofIso_apply (ρ θ).asIso x

/-- For a categorical action `ρ : Θ →* CategoryTheory.Aut H`, the underlying ideal of
`fixedPointHopfIdeal (fun θ ↦ (ρ θ).asIso.hom)` coincides with
`TauCeti.MulSemiringAction.fixedPointIdeal Θ H`. -/
theorem fixedPointHopfIdeal_aut_toIdeal_eq_mulSemiringActionFixedPointIdeal {Θ : Type w} [Monoid Θ]
    (ρ : Θ →* CategoryTheory.Aut H) :
    letI : _root_.MulSemiringAction Θ H :=
      _root_.MulSemiringAction.compHom H (autActionToAlgEquiv ρ)
    (fixedPointHopfIdeal fun θ ↦ (ρ θ).asIso.hom).toIdeal =
      TauCeti.MulSemiringAction.fixedPointIdeal Θ H := by
  let _ : _root_.MulSemiringAction Θ H :=
    _root_.MulSemiringAction.compHom H (autActionToAlgEquiv ρ)
  rw [fixedPointHopfIdeal_toIdeal, TauCeti.MulSemiringAction.fixedPointIdeal_def]
  simp only [MulAction.compHom_smul_def, AlgEquiv.smul_def, autActionToAlgEquiv_apply]

/-- **Smoothness of `H ⧸ fixedPointHopfIdeal`** (Edixhoven, Proposition 3.4): if `H` is a smooth
commutative Hopf algebra over `R` and `Θ` is a finite group of order invertible in `R` acting on
`H` by Hopf-algebra automorphisms, then the fixed-point quotient Hopf algebra is smooth over
`R`. -/
theorem smoothCommHopfAlgProperty_quotient_fixedPointHopfIdeal
    (H : _root_.CommHopfAlgCat.{v} R) (hH : smoothCommHopfAlgProperty R H)
    {Θ : Type w} [Group Θ] [Finite Θ] (ρ : Θ →* CategoryTheory.Aut H)
    (hΘ : IsUnit (Nat.card Θ : R)) :
    smoothCommHopfAlgProperty R (quotient H (fixedPointHopfIdeal fun θ ↦ (ρ θ).asIso.hom)) := by
  rw [smoothCommHopfAlgProperty_iff] at hH ⊢
  let _ : Algebra.Smooth R H := hH
  let _ : _root_.MulSemiringAction Θ H :=
    _root_.MulSemiringAction.compHom H (autActionToAlgEquiv ρ)
  have _ : SMulCommClass Θ R H := ⟨fun θ r x ↦ by
    rw [MulAction.compHom_smul_def, MulAction.compHom_smul_def]
    exact map_smul (autActionToAlgEquiv ρ θ) r x⟩
  have hsmooth : Algebra.Smooth R (H ⧸ TauCeti.MulSemiringAction.fixedPointIdeal Θ H) :=
    TauCeti.MulSemiringAction.smooth_quotient_fixedPointIdeal_of_isUnit hΘ
  exact Algebra.Smooth.of_equiv
    (Ideal.quotientEquivAlgOfEq R
      (fixedPointHopfIdeal_aut_toIdeal_eq_mulSemiringActionFixedPointIdeal ρ)).symm

end AutAction

end CommHopfAlgCat

/-! ### Finite-type affine group schemes and Edixhoven's smoothness theorem -/

namespace FiniteTypeCommHopfAlgCat

variable {k : Type u} [CommRing k]

/-- The **fixed-point Hopf ideal** of a monoid action `ρ : Θ →* CategoryTheory.Aut H` on a
finite-type commutative Hopf algebra `H`. -/
def fixedPointHopfIdeal {H : FiniteTypeCommHopfAlgCat.{u, v} k} {Θ : Type w} [Monoid Θ]
    (ρ : Θ →* CategoryTheory.Aut H) : HopfIdeal k H :=
  CommHopfAlgCat.fixedPointHopfIdeal (fun θ ↦ (ρ θ).asIso.hom.hom)

/-- Explicit formula for `FiniteTypeCommHopfAlgCat.fixedPointHopfIdeal` in terms of
`CommHopfAlgCat.fixedPointHopfIdeal`. -/
theorem fixedPointHopfIdeal_def {H : FiniteTypeCommHopfAlgCat.{u, v} k} {Θ : Type w} [Monoid Θ]
    (ρ : Θ →* CategoryTheory.Aut H) :
    fixedPointHopfIdeal ρ = CommHopfAlgCat.fixedPointHopfIdeal (fun θ ↦ (ρ θ).asIso.hom.hom) :=
  (rfl)

/-- The finite-type quotient morphism `mkQuotient H (fixedPointHopfIdeal ρ)` coequalizes every
automorphism `ρ θ` with the identity. -/
@[reassoc (attr := simp)]
theorem comp_mkQuotient_fixedPointHopfIdeal {H : FiniteTypeCommHopfAlgCat.{u, v} k}
    {Θ : Type w} [Monoid Θ] (ρ : Θ →* CategoryTheory.Aut H) (θ : Θ) :
    (ρ θ).asIso.hom ≫ mkQuotient H (fixedPointHopfIdeal ρ) =
      mkQuotient H (fixedPointHopfIdeal ρ) := by
  apply ObjectProperty.hom_ext
  exact CommHopfAlgCat.comp_mkQuotient_fixedPointHopfIdeal (fun θ ↦ (ρ θ).asIso.hom.hom) θ

/-- `fixedPointHopfIdeal ρ` vanishes if and only if `ρ` is the trivial action `1`. -/
@[simp]
theorem fixedPointHopfIdeal_eq_bot_iff {H : FiniteTypeCommHopfAlgCat.{u, v} k}
    {Θ : Type w} [Monoid Θ] {ρ : Θ →* CategoryTheory.Aut H} :
    fixedPointHopfIdeal ρ = ⊥ ↔ ρ = 1 := by
  rw [fixedPointHopfIdeal_def, CommHopfAlgCat.fixedPointHopfIdeal_eq_bot_iff, DFunLike.ext_iff]
  refine forall_congr' fun θ ↦ ?_
  rw [Aut.ext_iff, Iso.ext_iff, ObjectProperty.hom_ext_iff]
  simp

/-- The trivial action `1 : Θ →* CategoryTheory.Aut H` has vanishing fixed-point Hopf ideal. -/
@[simp]
theorem fixedPointHopfIdeal_one {H : FiniteTypeCommHopfAlgCat.{u, v} k} {Θ : Type w} [Monoid Θ] :
    fixedPointHopfIdeal (1 : Θ →* CategoryTheory.Aut H) = ⊥ :=
  fixedPointHopfIdeal_eq_bot_iff.mpr rfl

/-- A trivial automorphism action `ρ = 1` has vanishing fixed-point Hopf ideal. -/
theorem fixedPointHopfIdeal_eq_bot_of_eq_one {H : FiniteTypeCommHopfAlgCat.{u, v} k}
    {Θ : Type w} [Monoid Θ] {ρ : Θ →* CategoryTheory.Aut H} (hρ : ρ = 1) :
    fixedPointHopfIdeal ρ = ⊥ :=
  fixedPointHopfIdeal_eq_bot_iff.mpr hρ

/-- For a trivial automorphism action `ρ = 1`, the fixed-point quotient is isomorphic in
`FiniteTypeCommHopfAlgCat k` to `H` itself. -/
def quotientFixedPointHopfIdealIsoOfEqOne {H : FiniteTypeCommHopfAlgCat.{u, v} k}
    {Θ : Type w} [Monoid Θ] {ρ : Θ →* CategoryTheory.Aut H} (hρ : ρ = 1) :
    quotient H (fixedPointHopfIdeal ρ) ≅ H :=
  eqToIso (congrArg (quotient H) (fixedPointHopfIdeal_eq_bot_of_eq_one hρ)) ≪≫ quotientBotIso H

/-- The inverse of `quotientFixedPointHopfIdealIsoOfEqOne hρ` is `mkQuotient`. -/
@[simp]
theorem quotientFixedPointHopfIdealIsoOfEqOne_inv {H : FiniteTypeCommHopfAlgCat.{u, v} k}
    {Θ : Type w} [Monoid Θ] {ρ : Θ →* CategoryTheory.Aut H} (hρ : ρ = 1) :
    (quotientFixedPointHopfIdealIsoOfEqOne hρ).inv = mkQuotient H (fixedPointHopfIdeal ρ) := by
  simp only [quotientFixedPointHopfIdealIsoOfEqOne, Iso.trans_inv, quotientBotIso_inv, eqToIso.inv]
  exact mkQuotient_comp_eqToHom (fixedPointHopfIdeal_eq_bot_of_eq_one hρ)

/-- Composing `mkQuotient` with `(quotientFixedPointHopfIdealIsoOfEqOne hρ).hom` gives `𝟙 H`. -/
@[reassoc (attr := simp)]
theorem mkQuotient_comp_quotientFixedPointHopfIdealIsoOfEqOne_hom
    {H : FiniteTypeCommHopfAlgCat.{u, v} k} {Θ : Type w} [Monoid Θ]
    {ρ : Θ →* CategoryTheory.Aut H} (hρ : ρ = 1) :
    mkQuotient H (fixedPointHopfIdeal ρ) ≫ (quotientFixedPointHopfIdealIsoOfEqOne hρ).hom =
      𝟙 H := by
  rw [← quotientFixedPointHopfIdealIsoOfEqOne_inv hρ, Iso.inv_hom_id]

/-- Monoid homomorphism `Θ →* (H ≃ₐ[k] H)` induced by a categorical action
`ρ : Θ →* CategoryTheory.Aut H`. -/
def autActionToAlgEquiv {H : FiniteTypeCommHopfAlgCat.{u, v} k} {Θ : Type w} [Monoid Θ]
    (ρ : Θ →* CategoryTheory.Aut H) : Θ →* (H ≃ₐ[k] H) :=
  CommHopfAlgCat.autActionToAlgEquiv
    (((forget₂ (FiniteTypeCommHopfAlgCat.{u, v} k)
      (_root_.CommHopfAlgCat.{v} k)).mapAut H).comp ρ)

/-- `autActionToAlgEquiv ρ θ` acts on elements via the underlying bialgebra morphism of `ρ θ`. -/
@[simp]
theorem autActionToAlgEquiv_apply {H : FiniteTypeCommHopfAlgCat.{u, v} k}
    {Θ : Type w} [Monoid Θ] (ρ : Θ →* CategoryTheory.Aut H) (θ : Θ) (x : H) :
    autActionToAlgEquiv ρ θ x = toBialgHom (ρ θ).asIso.hom x := by
  simp [autActionToAlgEquiv, Functor.mapAut]

/-- The underlying ideal of `FiniteTypeCommHopfAlgCat.fixedPointHopfIdeal ρ` coincides with the
invariant-theoretic `TauCeti.MulSemiringAction.fixedPointIdeal Θ H`. -/
theorem fixedPointHopfIdeal_toIdeal_eq_mulSemiringActionFixedPointIdeal
    {H : FiniteTypeCommHopfAlgCat.{u, v} k} {Θ : Type w} [Monoid Θ]
    (ρ : Θ →* CategoryTheory.Aut H) :
    letI : _root_.MulSemiringAction Θ H :=
      _root_.MulSemiringAction.compHom H (autActionToAlgEquiv ρ)
    (fixedPointHopfIdeal ρ).toIdeal = TauCeti.MulSemiringAction.fixedPointIdeal Θ H :=
  CommHopfAlgCat.fixedPointHopfIdeal_aut_toIdeal_eq_mulSemiringActionFixedPointIdeal
    (((forget₂ (FiniteTypeCommHopfAlgCat.{u, v} k)
      (_root_.CommHopfAlgCat.{v} k)).mapAut H).comp ρ)

/-- **Smoothness of `H ⧸ fixedPointHopfIdeal ρ`** (Edixhoven, Proposition 3.4): if `H` is a smooth
finite-type commutative Hopf algebra over `k` and `Θ` is a finite group of order invertible in `k`
acting on `H` by Hopf-algebra automorphisms, then the fixed-point quotient Hopf algebra is smooth
over `k`. -/
theorem smoothCommHopfAlgProperty_quotient_fixedPointHopfIdeal
    (H : FiniteTypeCommHopfAlgCat.{u, v} k) (hH : smoothCommHopfAlgProperty k H.obj)
    {Θ : Type w} [Group Θ] [Finite Θ] (ρ : Θ →* CategoryTheory.Aut H)
    (hΘ : IsUnit (Nat.card Θ : k)) :
    smoothCommHopfAlgProperty k (quotient H (fixedPointHopfIdeal ρ)).obj :=
  CommHopfAlgCat.smoothCommHopfAlgProperty_quotient_fixedPointHopfIdeal H.obj hH
    (((forget₂ (FiniteTypeCommHopfAlgCat.{u, v} k)
      (_root_.CommHopfAlgCat.{v} k)).mapAut H).comp ρ)
    hΘ

/-- **Edixhoven's smoothness theorem for fixed points of affine group schemes**
(Edixhoven, Propositions 3.1 and 3.4): fixed points of a finite group `Θ` of order invertible in
`k` acting on a smooth finite-type affine group scheme over `k` are represented by a smooth closed
subgroup scheme of finite type over `k`. -/
theorem smooth_fixedPoints (H : FiniteTypeCommHopfAlgCat.{u, v} k)
    (hH : smoothCommHopfAlgProperty k H.obj) (Θ : Type w) [Group Θ] [Finite Θ]
    (ρ : Θ →* CategoryTheory.Aut H) (hΘ : IsUnit (Nat.card Θ : k)) :
    ∃ (H' : FiniteTypeCommHopfAlgCat.{u, v} k) (f : H ⟶ H'),
      smoothCommHopfAlgProperty k H'.obj ∧ Function.Surjective f.hom.hom ∧
      ∀ (R : Type x) [CommRing R] [Algebra k R],
        Set.range (BialgHom.mapDomain (A := R) (f.hom.hom : (H : Type v) →ₐc[k] H')) =
          {g | ∀ θ : Θ,
            BialgHom.mapDomain (A := R) ((ρ θ).asIso.hom.hom.hom : (H : Type v) →ₐc[k] H) g = g} :=
  ⟨quotient H (fixedPointHopfIdeal ρ), mkQuotient H (fixedPointHopfIdeal ρ),
    smoothCommHopfAlgProperty_quotient_fixedPointHopfIdeal H hH ρ hΘ,
    CommHopfAlgCat.mkQuotient_surjective H.obj (fixedPointHopfIdeal ρ),
    fun R _ _ ↦ CommHopfAlgCat.range_mapDomain_mkQuotient_fixedPointHopfIdeal
      (fun θ ↦ (ρ θ).asIso.hom.hom) R⟩

end FiniteTypeCommHopfAlgCat

end TauCeti
