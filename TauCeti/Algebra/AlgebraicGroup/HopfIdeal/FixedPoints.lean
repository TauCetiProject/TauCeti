/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.MonoidAlgebra.NoZeroDivisors
public import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Points.Equalizer
public import TauCeti.Algebra.AlgebraicGroup.RootsOfUnity.Inclusion
public import TauCeti.Algebra.AlgebraicGroup.Smooth.CommHopfAlgCat
public import TauCeti.Algebra.MonoidAlgebra.MapDomain
public import TauCeti.RingTheory.Idempotents.Connected.Spectrum
public import TauCeti.RingTheory.Invariant.FixedPointIdeal
import TauCeti.Algebra.Bialgebra.MonoidAlgebra.Augmentation
import TauCeti.Algebra.MonoidAlgebra.Exactness

/-!
# Fixed-point subgroup schemes and Edixhoven's smoothness theorem

A family of endomorphisms `f : ι → (H ⟶ H)` of a commutative Hopf algebra `H` over `R` represents,
contravariantly, a family of endomorphisms of the affine group scheme `Spec H`. The supremum
`fixedPointHopfIdeal f = ⨆ i, equalizerHopfIdeal (f i) (𝟙 H)` is a Hopf ideal of `H` whose quotient
cuts out the simultaneous fixed-point closed subgroup scheme: its `A`-points are the `A`-points of
`H` fixed by `BialgHom.mapDomain (f i).hom` for every `i`.

When a finite group `Θ` of order invertible in `k` acts on a finite-type commutative Hopf algebra
`H` over `k` by group-scheme automorphisms (`ρ : Θ →* CategoryTheory.Aut H`), the underlying ideal
of `fixedPointHopfIdeal` coincides with `TauCeti.MulSemiringAction.fixedPointIdeal Θ H`. Applying
`TauCeti.MulSemiringAction.smooth_quotient_fixedPointIdeal_of_isUnit` gives **Edixhoven's
smoothness theorem for group-scheme fixed points** (`FiniteTypeCommHopfAlgCat.smooth_fixedPoints`):
if `H` is smooth over `k`, then `H^Θ` is represented by a smooth closed subgroup scheme of finite
type over `k`.

Smoothness does *not* imply connectedness of `H^Θ`, even when `H` is a split torus:
* Under inversion on `𝔾ₘ = D(Multiplicative ℤ)`, the fixed-point subgroup scheme is `μ₂`
  (`DiagonalizableGroup.fixedPointInversionIso`), which has two `k`-points `{1, -1}` over any
  domain of characteristic not `2`
  (`DiagonalizableGroup.natCard_points_quotient_fixedPointInversion`) and disconnected prime
  spectrum over any nontrivial ring in which `2` is invertible
  (`DiagonalizableGroup.not_connectedSpace_primeSpectrum_quotient_fixedPointInversion`).
* Under factor swap on `𝔾ₘ² = D(Multiplicative (ℤ × ℤ))`, the fixed-point subgroup scheme is the
  diagonal `𝔾ₘ` (`DiagonalizableGroup.fixedPointSwapIso`), which has connected prime spectrum over
  every integral domain
  (`DiagonalizableGroup.connectedSpace_primeSpectrum_quotient_fixedPointSwap`).

## Main declarations

* `TauCeti.CommHopfAlgCat.fixedPointHopfIdeal`: the Hopf ideal cutting out the simultaneous fixed
  locus of a family of endomorphisms `f : ι → (H ⟶ H)`, with
  `TauCeti.CommHopfAlgCat.fixedPointHopfIdeal_toIdeal`,
  `TauCeti.CommHopfAlgCat.fixedPointHopfIdeal_le_iff`,
  `TauCeti.CommHopfAlgCat.fixedPointHopfIdeal_le_ker_iff`,
  `TauCeti.CommHopfAlgCat.mem_quotientPointsSubgroup_fixedPointHopfIdeal_iff`, and
  `TauCeti.CommHopfAlgCat.range_mapDomain_mkQuotient_fixedPointHopfIdeal`.
* `TauCeti.FiniteTypeCommHopfAlgCat.fixedPointHopfIdeal`: the fixed-point Hopf ideal of an action
  `ρ : Θ →* CategoryTheory.Aut H`, with `TauCeti.FiniteTypeCommHopfAlgCat.autActionToAlgEquiv`,
  `TauCeti.FiniteTypeCommHopfAlgCat.quotientFixedPointHopfIdealOfEqOneIso` for trivial actions, and
  `TauCeti.FiniteTypeCommHopfAlgCat.smoothCommHopfAlgProperty_quotient_fixedPointHopfIdeal`.
* `TauCeti.FiniteTypeCommHopfAlgCat.smooth_fixedPoints`: Edixhoven's theorem that fixed points of a
  finite group of invertible order acting on a smooth finite-type affine group scheme form a smooth
  closed subgroup scheme.
* `TauCeti.DiagonalizableGroup.fixedPointCoordinateIsoOfSurjective`: for a diagonalizable group
  `D(G)` with character endomorphisms `φ : ι → (G →* G)`, any surjective character quotient
  `q : G →* Q` with `q.ker = Subgroup.closure {φ i g * g⁻¹}` identifies `D(G)^φ ≅ D(Q)`.
* `TauCeti.DiagonalizableGroup.fixedPointInversionIso` and
  `TauCeti.DiagonalizableGroup.fixedPointSwapIso`: the worked calculations `(𝔾ₘ)^{inv} ≅ μ₂` and
  `(𝔾ₘ²)^{swap} ≅ 𝔾ₘ`.

## References

* B. Edixhoven, *Néron models and tame ramification*, Compositio Math. 81 (1992), Proposition 3.1
  (p. 293) and Proposition 3.4 (pp. 294–295).
* J. S. Milne, *Algebraic Groups* (2017), §1.h and Theorem 12.9.
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
  rfl

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
  rfl

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
  rw [mem_quotientPointsSubgroup_iff]
  have hker : (∀ h ∈ fixedPointHopfIdeal f, g.ofConv h = 0) ↔
      (fixedPointHopfIdeal f).toIdeal ≤ RingHom.ker (g.ofConv : H →ₐ[R] A).toRingHom :=
    ⟨fun h _ hy ↦ RingHom.mem_ker.mpr (h _ (HopfIdeal.mem_toIdeal.mp hy)),
      fun h _ hy ↦ RingHom.mem_ker.mp (h (HopfIdeal.mem_toIdeal.mpr hy))⟩
  rw [hker, fixedPointHopfIdeal_le_ker_iff]
  refine forall_congr' fun i ↦ ⟨fun h ↦ ?_, fun h a ↦ ?_⟩
  · apply ofConv_injective
    ext a
    simpa only [BialgHom.mapDomain_apply_apply, AlgHom.toRingHom_eq_coe,
      AlgHom.coe_toRingHom] using h a
  · simpa only [BialgHom.mapDomain_apply_apply, AlgHom.toRingHom_eq_coe,
      AlgHom.coe_toRingHom] using congrArg (fun m : WithConv (H →ₐ[R] A) ↦ m.ofConv a) h

/-- **Image on points of `mkQuotient H (fixedPointHopfIdeal f)`.** For every commutative
`R`-algebra `A`, the image of `A`-points of the quotient `H ⧸ fixedPointHopfIdeal f` inside the
`A`-points of `H` is the set of points fixed by every `f i`. -/
theorem range_mapDomain_mkQuotient_fixedPointHopfIdeal {ι : Sort w} (f : ι → (H ⟶ H))
    (A : Type x) [CommRing A] [Algebra R A] :
    Set.range (BialgHom.mapDomain (A := A) (mkQuotient H (fixedPointHopfIdeal f)).hom) =
      {g | ∀ i, BialgHom.mapDomain (A := A) (f i).hom g = g} := by
  ext g
  refine ⟨?_, ?_⟩
  · rintro ⟨q, rfl⟩ i
    apply ofConv_injective
    ext h
    have hcomp : ((mkQuotient H (fixedPointHopfIdeal f)).hom : H →ₐc[R] _) ((f i).hom h) =
        (mkQuotient H (fixedPointHopfIdeal f)).hom h := by
      simpa using congrArg (fun m : H ⟶ _ ↦ m.hom h)
        (comp_mkQuotient_fixedPointHopfIdeal f i)
    simp only [BialgHom.mapDomain_apply_apply, hcomp]
  · intro hg
    have hg_kill : ∀ x ∈ fixedPointHopfIdeal f, g.ofConv x = 0 :=
      (mem_quotientPointsSubgroup_iff H (fixedPointHopfIdeal f) (CommAlgCat.of R A) g).mp
        ((mem_quotientPointsSubgroup_fixedPointHopfIdeal_iff f (CommAlgCat.of R A) g).mpr hg)
    refine ⟨liftQuotientPoint H (fixedPointHopfIdeal f) (CommAlgCat.of R A) g hg_kill, ?_⟩
    apply ofConv_injective
    ext h
    rw [BialgHom.mapDomain_apply_apply, mkQuotient_apply, Ideal.Quotient.mkₐ_eq_mk,
      liftQuotientPoint_mk]

end CommHopfAlgCat

/-! ### Finite-type affine group schemes and Edixhoven's smoothness theorem -/

namespace FiniteTypeCommHopfAlgCat

variable {k : Type u} [CommRing k]

/-- The **fixed-point Hopf ideal** of a group action `ρ : Θ →* CategoryTheory.Aut H` on a
finite-type commutative Hopf algebra `H`. -/
def fixedPointHopfIdeal {H : FiniteTypeCommHopfAlgCat.{u, v} k} {Θ : Type w} [Monoid Θ]
    (ρ : Θ →* CategoryTheory.Aut H) : HopfIdeal k H :=
  CommHopfAlgCat.fixedPointHopfIdeal (fun θ ↦ (ρ θ).asIso.hom.hom)

/-- A trivial automorphism action has vanishing fixed-point Hopf ideal. -/
@[simp]
theorem fixedPointHopfIdeal_eq_bot_of_eq_one {H : FiniteTypeCommHopfAlgCat.{u, v} k}
    {Θ : Type w} [Monoid Θ] {ρ : Θ →* CategoryTheory.Aut H} (hρ : ρ = 1) :
    fixedPointHopfIdeal ρ = ⊥ := by
  subst hρ
  rw [fixedPointHopfIdeal, CommHopfAlgCat.fixedPointHopfIdeal_eq_bot_iff]
  intro θ
  rfl

/-- For a trivial automorphism action `ρ = 1`, the fixed-point quotient is isomorphic in
`FiniteTypeCommHopfAlgCat k` to `H` itself. -/
def quotientFixedPointHopfIdealOfEqOneIso {H : FiniteTypeCommHopfAlgCat.{u, v} k}
    {Θ : Type w} [Monoid Θ] {ρ : Θ →* CategoryTheory.Aut H} (hρ : ρ = 1) :
    quotient H (fixedPointHopfIdeal ρ) ≅ H :=
  eqToIso (congrArg (quotient H) (fixedPointHopfIdeal_eq_bot_of_eq_one hρ)) ≪≫ quotientBotIso H

/-- Monoid homomorphism `Θ →* (H ≃ₐ[k] H)` induced by a categorical action
`ρ : Θ →* CategoryTheory.Aut H`. -/
def autActionToAlgEquiv {H : FiniteTypeCommHopfAlgCat.{u, v} k} {Θ : Type w} [Monoid Θ]
    (ρ : Θ →* CategoryTheory.Aut H) : Θ →* (H ≃ₐ[k] H) where
  toFun θ :=
    (CommHopfAlgCat.ofIso
      ((forget₂ (FiniteTypeCommHopfAlgCat.{u, v} k) (_root_.CommHopfAlgCat.{v} k)).mapIso
        (ρ θ).asIso)).toAlgEquiv
  map_one' := AlgEquiv.ext fun x ↦ by
    simp only [map_one, Aut.one_asIso, Functor.mapIso_refl, AlgEquiv.one_apply]
    rfl
  map_mul' θ₁ θ₂ := AlgEquiv.ext fun x ↦ by
    simp only [map_mul, Aut.mul_asIso, Functor.mapIso_trans, AlgEquiv.mul_apply]
    rfl

/-- `autActionToAlgEquiv ρ θ` acts on elements via the underlying bialgebra morphism of `ρ θ`. -/
@[simp]
theorem autActionToAlgEquiv_apply {H : FiniteTypeCommHopfAlgCat.{u, v} k}
    {Θ : Type w} [Monoid Θ] (ρ : Θ →* CategoryTheory.Aut H) (θ : Θ) (x : H) :
    autActionToAlgEquiv ρ θ x = toBialgHom (ρ θ).asIso.hom x :=
  (rfl)

/-- The underlying ideal of `FiniteTypeCommHopfAlgCat.fixedPointHopfIdeal ρ` coincides with the
invariant-theoretic `TauCeti.MulSemiringAction.fixedPointIdeal Θ H`. -/
theorem fixedPointHopfIdeal_toIdeal_eq_mulSemiringAction {H : FiniteTypeCommHopfAlgCat.{u, v} k}
    {Θ : Type w} [Monoid Θ] (ρ : Θ →* CategoryTheory.Aut H) :
    letI : _root_.MulSemiringAction Θ H :=
      _root_.MulSemiringAction.compHom H (autActionToAlgEquiv ρ)
    (fixedPointHopfIdeal ρ).toIdeal = TauCeti.MulSemiringAction.fixedPointIdeal Θ H := by
  let _ : _root_.MulSemiringAction Θ H :=
    _root_.MulSemiringAction.compHom H (autActionToAlgEquiv ρ)
  rw [fixedPointHopfIdeal, CommHopfAlgCat.fixedPointHopfIdeal_toIdeal,
    TauCeti.MulSemiringAction.fixedPointIdeal_def]
  rfl

/-- **Smoothness of `H ⧸ fixedPointHopfIdeal ρ`** (Edixhoven, Proposition 3.4): if `H` is a smooth
finite-type commutative Hopf algebra over `k` and `Θ` is a finite group of order invertible in `k`
acting on `H` by Hopf-algebra automorphisms, then the fixed-point quotient Hopf algebra is smooth
over `k`. -/
theorem smoothCommHopfAlgProperty_quotient_fixedPointHopfIdeal
    (H : FiniteTypeCommHopfAlgCat.{u, v} k) (hH : smoothCommHopfAlgProperty k H.obj)
    {Θ : Type w} [Group Θ] [Finite Θ] (ρ : Θ →* CategoryTheory.Aut H)
    (hΘ : IsUnit (Nat.card Θ : k)) :
    smoothCommHopfAlgProperty k (quotient H (fixedPointHopfIdeal ρ)).obj := by
  rw [smoothCommHopfAlgProperty_iff] at hH ⊢
  let _ : Algebra.Smooth k H := hH
  let _ : _root_.MulSemiringAction Θ H :=
    _root_.MulSemiringAction.compHom H (autActionToAlgEquiv ρ)
  have _ : SMulCommClass Θ k H := ⟨fun θ r x ↦ map_smul (autActionToAlgEquiv ρ θ) r x⟩
  have hsmooth : Algebra.Smooth k (H ⧸ TauCeti.MulSemiringAction.fixedPointIdeal Θ H) :=
    TauCeti.MulSemiringAction.smooth_quotient_fixedPointIdeal_of_isUnit hΘ
  exact Algebra.Smooth.of_equiv
    (Ideal.quotientEquivAlgOfEq k (fixedPointHopfIdeal_toIdeal_eq_mulSemiringAction ρ)).symm

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

/-! ### Fixed points of diagonalizable groups and worked examples -/

namespace DiagonalizableGroup

section General

variable (R : Type u) [CommRing R]

/-- For a family of character endomorphisms `φ : ι → (G →* G)` and a monoid homomorphism
`q : G →* Q` whose kernel is generated by the displacements `φ i g * g⁻¹`, the fixed-point Hopf
ideal on `R[G]` has underlying ideal `ker (mapDomainRingHom R q)`. -/
theorem fixedPointHopfIdeal_mapDomainBialgHom_toIdeal {G : Type v} {Q : Type x}
    [CommGroup G] [Monoid Q] {ι : Sort w} (φ : ι → (G →* G))
    (q : G →* Q) (hq_ker : q.ker = Subgroup.closure {x : G | ∃ i g, φ i g * g⁻¹ = x}) :
    (CommHopfAlgCat.fixedPointHopfIdeal
      (fun i ↦ CommHopfAlgCat.ofHom (MonoidAlgebra.mapDomainBialgHom R (φ i)))).toIdeal =
        RingHom.ker (MonoidAlgebra.mapDomainRingHom R q) := by
  apply le_antisymm
  · rw [CommHopfAlgCat.fixedPointHopfIdeal_le_ker_iff]
    intro i x
    induction x using MonoidAlgebra.induction_linear with
    | zero => simp
    | add x y hx hy => rw [map_add, map_add, map_add, hx, hy]
    | single g r =>
      have hmem : φ i g * g⁻¹ ∈ q.ker := by
        rw [hq_ker]
        exact Subgroup.subset_closure ⟨i, g, rfl⟩
      have hqg : q (φ i g) = q g := by
        calc
          q (φ i g) = q (φ i g * g⁻¹ * g) := by rw [inv_mul_cancel_right]
          _ = q (φ i g * g⁻¹) * q g := map_mul q _ _
          _ = q g := by rw [MonoidHom.mem_ker.mp hmem, one_mul]
      simp [hqg]
  · rw [TauCeti.MonoidAlgebra.ker_mapDomainRingHom_eq_span R q, Ideal.span_le]
    rintro _ ⟨k, rfl⟩
    have hk : (k : G) ∈ Subgroup.closure {x : G | ∃ i g, φ i g * g⁻¹ = x} := hq_ker ▸ k.property
    refine Ideal.span_le.mpr ?_ (TauCeti.MonoidAlgebra.single_sub_one_mem_span_of_mem_closure R hk)
    rintro _ ⟨_, ⟨i, g, rfl⟩, rfl⟩
    have hsub : MonoidAlgebra.single (φ i g) (1 : R) - MonoidAlgebra.single g 1 ∈
        (CommHopfAlgCat.fixedPointHopfIdeal
          (fun i ↦ CommHopfAlgCat.ofHom (MonoidAlgebra.mapDomainBialgHom R (φ i)))).toIdeal := by
      simpa using
        HopfIdeal.mem_toIdeal.mpr (CommHopfAlgCat.sub_mem_fixedPointHopfIdeal
          (fun i ↦ CommHopfAlgCat.ofHom (MonoidAlgebra.mapDomainBialgHom R (φ i))) i
          (MonoidAlgebra.single g 1))
    have hmul := Ideal.mul_mem_right (MonoidAlgebra.single g⁻¹ (1 : R)) _ hsub
    exact SetLike.mem_coe.mpr (by
      simpa only [sub_mul, MonoidAlgebra.single_mul_single, one_mul, mul_inv_cancel,
        MonoidAlgebra.one_def] using hmul)

/-- Surjectivity of `MonoidAlgebra.mapDomainBialgHom R q` for surjective `q`, proved via
`mapDomainRingHom_apply` without unfolding `BialgHom` coercions in `whnf`. -/
private theorem mapDomainBialgHom_surjective {G : Type v} {Q : Type x} [Monoid G] [Monoid Q]
    {q : G →* Q} (hq : Function.Surjective q) :
    Function.Surjective (MonoidAlgebra.mapDomainBialgHom R q) := by
  rw [← BialgHom.coe_toAlgHom, ← RingHom.coe_coe,
    TauCeti.MonoidAlgebra.mapDomainBialgHom_toRingHom]
  exact fun y ↦ (MonoidAlgebra.mapDomain_surjective hq y).imp fun x hx ↦
    (MonoidAlgebra.mapDomainRingHom_apply R q x).trans hx

/-- **Fixed-point coordinate algebra of a diagonalizable group.** If `q : G →* Q` is surjective with
kernel generated by `{φ i g * g⁻¹}`, then `D(G)^φ ≅ D(Q)` in `CommHopfAlgCat R`. -/
def fixedPointCoordinateIsoOfSurjective {G Q : Type v} [CommGroup G] [CommGroup Q]
    {ι : Sort w} (φ : ι → (G →* G)) (q : G →* Q) (hq_surj : Function.Surjective q)
    (hq_ker : q.ker = Subgroup.closure {x : G | ∃ i g, φ i g * g⁻¹ = x}) :
    CommHopfAlgCat.quotient (CommHopfAlgCat.of R (MonoidAlgebra R G))
        (CommHopfAlgCat.fixedPointHopfIdeal
          (fun i ↦ CommHopfAlgCat.ofHom (MonoidAlgebra.mapDomainBialgHom R (φ i)))) ≅
      CommHopfAlgCat.of R (MonoidAlgebra R Q) :=
  CommHopfAlgCat.Hom.quotientIsoOfKerOfSurjectiveEq
    (CommHopfAlgCat.ofHom (MonoidAlgebra.mapDomainBialgHom R q))
    (by rw [_root_.CommHopfAlgCat.hom_ofHom]; exact mapDomainBialgHom_surjective R hq_surj) <| by
      ext x
      rw [← HopfIdeal.mem_toIdeal, ← HopfIdeal.mem_toIdeal,
        HopfIdeal.kerOfSurjective_toIdeal, _root_.CommHopfAlgCat.hom_ofHom,
        fixedPointHopfIdeal_mapDomainBialgHom_toIdeal R φ q hq_ker]
      rfl

end General

/-! #### Worked example 1: inversion on `𝔾ₘ` gives `μ₂` (smooth for `2 ∈ Rˣ`, disconnected) -/

section Inversion

private theorem mem_ker_toMultiplicativeZMod_two_iff (x : Multiplicative ℤ) :
    RootsOfUnityGroup.toMultiplicativeZMod 2 x = 1 ↔
      ∃ k : ℤ, Multiplicative.ofAdd (-k + -k) = x := by
  rw [← MonoidHom.mem_ker, RootsOfUnityGroup.ker_toMultiplicativeZMod, Subgroup.mem_zpowers_iff]
  refine ⟨fun ⟨k, hk⟩ ↦ ⟨-k, ?_⟩, fun ⟨k, hk⟩ ↦ ⟨-k, ?_⟩⟩
  · rw [← hk]
    apply Multiplicative.toAdd.injective
    simp only [toAdd_ofAdd, toAdd_zpow]
    ring
  · rw [← hk]
    apply Multiplicative.toAdd.injective
    simp only [toAdd_zpow, toAdd_ofAdd]
    ring

/-- **Fixed points of inversion on `𝔾ₘ` are `μ₂`:** over every commutative ring `R`, the
fixed-point quotient of `𝔾ₘ = D(Multiplicative ℤ)` under inversion is isomorphic in
`CommHopfAlgCat R` to `μ₂ = D(Multiplicative (ZMod 2))`. -/
def fixedPointInversionIso (R : Type u) [CommRing R] :
    CommHopfAlgCat.quotient (CommHopfAlgCat.of R (MonoidAlgebra R (Multiplicative ℤ)))
        (CommHopfAlgCat.fixedPointHopfIdeal
          (fun _ : Unit ↦ CommHopfAlgCat.ofHom
            (MonoidAlgebra.mapDomainBialgHom R (invMonoidHom : Multiplicative ℤ →* _)))) ≅
      CommHopfAlgCat.of R (MonoidAlgebra R (Multiplicative (ZMod 2))) :=
  CommHopfAlgCat.Hom.quotientIsoOfKerOfSurjectiveEq
    (CommHopfAlgCat.ofHom
      (MonoidAlgebra.mapDomainBialgHom R (RootsOfUnityGroup.toMultiplicativeZMod 2)))
    (by
      rw [_root_.CommHopfAlgCat.hom_ofHom]
      exact mapDomainBialgHom_surjective R (RootsOfUnityGroup.toMultiplicativeZMod_surjective 2)) <|
    by
      ext x
      rw [← HopfIdeal.mem_toIdeal, ← HopfIdeal.mem_toIdeal,
        HopfIdeal.kerOfSurjective_toIdeal, _root_.CommHopfAlgCat.hom_ofHom,
        fixedPointHopfIdeal_mapDomainBialgHom_toIdeal R (fun _ : Unit ↦ invMonoidHom)
          (RootsOfUnityGroup.toMultiplicativeZMod 2) <| by
            apply le_antisymm
            · intro y hy
              obtain ⟨k, rfl⟩ := (mem_ker_toMultiplicativeZMod_two_iff y).mp hy
              exact Subgroup.subset_closure ⟨(), Multiplicative.ofAdd k, rfl⟩
            · rw [Subgroup.closure_le]
              rintro _ ⟨⟨⟩, g, rfl⟩
              exact (mem_ker_toMultiplicativeZMod_two_iff _).mpr ⟨g.toAdd, rfl⟩]
      rfl

/-- Over an integral domain `k` with `(2 : k) ≠ 0`, the `k`-points of `(𝔾ₘ)^{inv}` have cardinality
`2` (corresponding to `{1, -1}`). -/
theorem natCard_points_quotient_fixedPointInversion (k : Type u) [CommRing k] [IsDomain k]
    (h2 : (2 : k) ≠ 0) :
    Nat.card (HopfAlgebra.points (R := k)
      (H := CommHopfAlgCat.quotient (CommHopfAlgCat.of k (MonoidAlgebra k (Multiplicative ℤ)))
        (CommHopfAlgCat.fixedPointHopfIdeal
          (fun _ : Unit ↦ CommHopfAlgCat.ofHom
            (MonoidAlgebra.mapDomainBialgHom k (invMonoidHom : Multiplicative ℤ →* _)))))
      (CommAlgCat.of k k)) = 2 := by
  let eIso := fixedPointInversionIso k
  let ePts : HopfAlgebra.points (R := k) (H := _) (CommAlgCat.of k k) ≃
      rootsOfUnity 2 k :=
    { toFun p := RootsOfUnityGroup.pointsMulEquiv 2 (BialgHom.mapDomain eIso.inv.hom p)
      invFun ζ := BialgHom.mapDomain eIso.hom.hom ((RootsOfUnityGroup.pointsMulEquiv 2).symm ζ)
      left_inv p := by
        dsimp only
        rw [MulEquiv.symm_apply_apply, ← MonoidHom.comp_apply, ← BialgHom.mapDomain_comp]
        have hcomp : eIso.inv.hom.comp eIso.hom.hom = BialgHom.id k _ :=
          congrArg CommHopfAlgCat.Hom.hom eIso.hom_inv_id
        simp [hcomp]
      right_inv ζ := by
        dsimp only
        apply (RootsOfUnityGroup.pointsMulEquiv (R := k) (A := k) 2).symm.injective
        rw [MulEquiv.symm_apply_apply, ← MonoidHom.comp_apply, ← BialgHom.mapDomain_comp]
        have hcomp : eIso.hom.hom.comp eIso.inv.hom = BialgHom.id k _ :=
          congrArg CommHopfAlgCat.Hom.hom eIso.inv_hom_id
        simp [hcomp] }
  rw [Nat.card_congr ePts]
  let oneRoot : rootsOfUnity 2 k := 1
  let negOneRoot : rootsOfUnity 2 k := ⟨-1, (mem_rootsOfUnity 2 (-1 : kˣ)).mpr (by ext; simp)⟩
  have hne : oneRoot ≠ negOneRoot := fun h ↦ h2 <| by
    have hval : (1 : k) = -1 := congrArg (fun z : rootsOfUnity 2 k ↦ ((z : kˣ) : k)) h
    linear_combination hval
  have hbij : Function.Bijective (fun b : Bool ↦ if b then oneRoot else negOneRoot) := by
    refine ⟨fun b₁ b₂ hb ↦ ?_, fun ζ ↦ ?_⟩
    · cases b₁ <;> cases b₂ <;> simp_all
    · have hsq : ((ζ : kˣ) : k) ^ 2 = 1 := by
        rw [← Units.val_pow_eq_pow_val, (mem_rootsOfUnity 2 (ζ : kˣ)).mp ζ.2, Units.val_one]
      rcases sq_eq_one_iff.mp hsq with h1 | hm1
      · refine ⟨true, ?_⟩
        ext
        exact h1.symm
      · refine ⟨false, ?_⟩
        ext
        exact hm1.symm
  exact (Nat.card_congr (Equiv.ofBijective _ hbij).symm).trans (Nat.card_eq_fintype_card.trans rfl)

/-- **Non-example for connectedness:** over any nontrivial ring `R` in which `2` is invertible,
`(𝔾ₘ)^{inv}` is smooth by Edixhoven's theorem yet its prime spectrum is disconnected. -/
theorem not_connectedSpace_primeSpectrum_quotient_fixedPointInversion (R : Type u) [CommRing R]
    [Nontrivial R] [Invertible (2 : R)] :
    ¬ ConnectedSpace (PrimeSpectrum
      (CommHopfAlgCat.quotient (CommHopfAlgCat.of R (MonoidAlgebra R (Multiplicative ℤ)))
        (CommHopfAlgCat.fixedPointHopfIdeal
          (fun _ : Unit ↦ CommHopfAlgCat.ofHom
            (MonoidAlgebra.mapDomainBialgHom R (invMonoidHom : Multiplicative ℤ →* _)))))) := by
  rw [(PrimeSpectrum.homeomorphOfRingEquiv
    (CommHopfAlgCat.ofIso (fixedPointInversionIso R)).toAlgEquiv.toRingEquiv).connectedSpace_iff]
  intro hconn
  let g := RootsOfUnityGroup.generator 2
  let e : MonoidAlgebra R (Multiplicative (ZMod 2)) :=
    ⅟(2 : R) • (1 + MonoidAlgebra.single g (1 : R))
  have hg2 : MonoidAlgebra.single g (1 : R) * MonoidAlgebra.single g (1 : R) = 1 := by
    simpa only [sq] using RootsOfUnityGroup.single_generator_pow_eq_one (R := R) 2
  have he : IsIdempotentElem e := by
    dsimp only [IsIdempotentElem, e]
    rw [smul_mul_smul_comm, add_mul, one_mul, mul_add, mul_one, hg2]
    have hsum : (1 : MonoidAlgebra R (Multiplicative (ZMod 2))) + MonoidAlgebra.single g 1 +
        (MonoidAlgebra.single g 1 + 1) = (2 : R) • (1 + MonoidAlgebra.single g 1) := by
      rw [two_smul]
      abel
    rw [hsum, smul_smul, mul_assoc, invOf_mul_self, mul_one]
  have hg_ne : (1 : Multiplicative (ZMod 2)) ≠ g := by decide
  have he_coeff : e.coeff g = ⅟(2 : R) := by
    simp only [e, MonoidAlgebra.coeff_smul, MonoidAlgebra.coeff_add, MonoidAlgebra.one_def,
      MonoidAlgebra.coeff_single, Finsupp.smul_apply, Finsupp.add_apply,
      Finsupp.single_eq_of_ne' hg_ne, Finsupp.single_eq_same, zero_add, smul_eq_mul, mul_one]
  have hinv_ne : ⅟(2 : R) ≠ 0 := fun h0 ↦
    one_ne_zero (by rw [← mul_invOf_self (2 : R), h0, mul_zero])
  rcases he.eq_zero_or_eq_one_of_preconnectedSpace with h0 | h1
  · rw [h0, MonoidAlgebra.coeff_zero, Finsupp.zero_apply] at he_coeff
    exact hinv_ne he_coeff.symm
  · rw [h1, MonoidAlgebra.one_def, MonoidAlgebra.coeff_single,
      Finsupp.single_eq_of_ne' hg_ne] at he_coeff
    exact hinv_ne he_coeff.symm

end Inversion

/-! #### Worked example 2: factor swap on `𝔾ₘ²` gives the connected diagonal `𝔾ₘ` -/

section Swap

/-- The coordinate-swap automorphism of the character group `Multiplicative (ℤ × ℤ)` of `𝔾ₘ²`. -/
def swapCharHom : Multiplicative (ℤ × ℤ) →* Multiplicative (ℤ × ℤ) :=
  AddMonoidHom.toMultiplicative (AddEquiv.prodComm : ℤ × ℤ ≃+ ℤ × ℤ).toAddMonoidHom

private def sumCharHom : Multiplicative (ℤ × ℤ) →* Multiplicative ℤ :=
  AddMonoidHom.toMultiplicative (AddMonoidHom.fst ℤ ℤ + AddMonoidHom.snd ℤ ℤ)

private theorem sumCharHom_surjective : Function.Surjective sumCharHom := fun y ↦
  ⟨Multiplicative.ofAdd (y.toAdd, 0), Multiplicative.toAdd.injective (by simp [sumCharHom])⟩

private theorem ker_sumCharHom :
    sumCharHom.ker =
      Subgroup.closure
        {x : Multiplicative (ℤ × ℤ) |
          ∃ (_ : Unit) (g : Multiplicative (ℤ × ℤ)), swapCharHom g * g⁻¹ = x} := by
  apply le_antisymm
  · intro x hx
    rw [MonoidHom.mem_ker] at hx
    have hx' : x.toAdd.1 + x.toAdd.2 = 0 := congrArg Multiplicative.toAdd hx
    refine Subgroup.subset_closure ⟨(), Multiplicative.ofAdd (0, x.toAdd.1), ?_⟩
    apply Multiplicative.toAdd.injective
    ext <;> simp [swapCharHom]; omega
  · rw [Subgroup.closure_le]
    rintro _ ⟨⟨⟩, g, rfl⟩
    rw [SetLike.mem_coe, MonoidHom.mem_ker]
    induction g using Multiplicative.rec with
    | ofAdd p =>
      rcases p with ⟨a, b⟩
      apply Multiplicative.toAdd.injective
      simp [sumCharHom, swapCharHom]

/-- **Fixed points of factor swap on `𝔾ₘ²` are the diagonal `𝔾ₘ`:** over every commutative ring `R`,
the fixed-point quotient of `𝔾ₘ² = D(Multiplicative (ℤ × ℤ))` under `swapCharHom` is isomorphic in
`CommHopfAlgCat R` to `𝔾ₘ = D(Multiplicative ℤ)`. -/
def fixedPointSwapIso (R : Type u) [CommRing R] :
    CommHopfAlgCat.quotient
        (CommHopfAlgCat.of R (MonoidAlgebra R (Multiplicative (ℤ × ℤ))))
        (CommHopfAlgCat.fixedPointHopfIdeal
          (fun _ : Unit ↦ CommHopfAlgCat.ofHom (MonoidAlgebra.mapDomainBialgHom R swapCharHom))) ≅
      CommHopfAlgCat.of R (MonoidAlgebra R (Multiplicative ℤ)) :=
  fixedPointCoordinateIsoOfSurjective R (fun _ : Unit ↦ swapCharHom) sumCharHom
    sumCharHom_surjective ker_sumCharHom

/-- Over every integral domain `R`, the fixed-point subgroup scheme `(𝔾ₘ²)^{swap}` has connected
prime spectrum. -/
theorem connectedSpace_primeSpectrum_quotient_fixedPointSwap (R : Type u) [CommRing R]
    [IsDomain R] :
    ConnectedSpace (PrimeSpectrum
      (CommHopfAlgCat.quotient
        (CommHopfAlgCat.of R (MonoidAlgebra R (Multiplicative (ℤ × ℤ))))
        (CommHopfAlgCat.fixedPointHopfIdeal
          (fun _ : Unit ↦
            CommHopfAlgCat.ofHom (MonoidAlgebra.mapDomainBialgHom R swapCharHom))))) :=
  (PrimeSpectrum.homeomorphOfRingEquiv
    (CommHopfAlgCat.ofIso (fixedPointSwapIso R)).toAlgEquiv.toRingEquiv).connectedSpace_iff.mpr
      inferInstance

end Swap

end DiagonalizableGroup

end TauCeti
