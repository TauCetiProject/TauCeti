/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.Scheme.Geom.BaseChange.Points
public import TauCeti.AlgebraicGeometry.EllipticCurve.Scheme.Geom.NaiveLevel
public import TauCeti.AlgebraicGeometry.EllipticCurve.Scheme.Geom.Torsion
public import Mathlib.CategoryTheory.Subfunctor.Basic
import TauCeti.AlgebraicGeometry.EllipticCurve.Scheme.Geom.Torsion.Equalizer
import TauCeti.AlgebraicGeometry.EqualizerCarrier
import TauCeti.AlgebraicGeometry.RationalPoint.Basic

/-!
# Points of naive exact order `N` on an elliptic curve

Let `E` be an elliptic curve over a scheme `S` and `x` a point of `E` with values in a scheme `Z`
over `S`. Following Katz and Mazur, `x` has **naive exact order `N`** when it is a point of the
`N`-torsion `E[N]`, that is `Nx = 0`, and for every divisor `d ≠ N` of `N` the point `dx` meets
the zero section nowhere: the equalizer of `dx` and `0`, the closed subscheme of `Z` on which the
two agree, is empty (`EllipticCurveGeom.IsOfNaiveExactOrder`). Over a field this says that `x`
has order exactly `N` in the group of points
(`EllipticCurveGeom.isOfNaiveExactOrder_iff_orderOf_eq`); in general it is the scheme-theoretic
form of asking that `x` have order exactly `N` in every geometric fibre.

An `S`-point of naive exact order `N` is a *naive `[Γ₁(N)]`-structure* on `E`: an `S`-point `Q`
has empty equalizer with the zero section exactly when it meets the zero section at no point of
`S` (`EllipticCurveGeom.isEmpty_equalizer_one_iff`), so a homomorphism `φ : ℤ/Nℤ →* E(S)` is
injective on every fibre, the condition defining `ModuliProblem.gammaOneNaive`, exactly when
`φ 1` has naive exact order `N`
(`EllipticCurveGeom.isFiberwiseInjective_iff_isOfNaiveExactOrder`).

Unlike the Drinfeld notion `EllipticCurveGeom.IsOfExactOrder`, which works over every base, the
naive notion behaves poorly where `N` is not invertible: over a field of characteristic `p`, a
supersingular curve has no point of naive exact order `p`, while its zero section has exact order
`p` in Drinfeld's sense. The open and closed representability construction below accordingly
requires `N` to be invertible on `S`. Points of naive exact order `N` are stable under base
change, both along morphisms `Z' ⟶ Z` (`EllipticCurveGeom.IsOfNaiveExactOrder.comp`) and along
base change of the elliptic curve (`EllipticCurveGeom.IsOfNaiveExactOrder.pointsPullback`).

A point of `E[N]` with values in `Z` has naive exact order `N` exactly when it maps `Z` into the
set `EllipticCurveGeom.naiveExactOrderLocus E N` of points of `E[N]` at which no `d`-th multiple
of the universal point, for a divisor `d ≠ N` of `N`, meets the zero section
(`EllipticCurveGeom.isOfNaiveExactOrder_comp_torsionι_iff`). When `N` is invertible on `S`, this
set is open and closed in `E[N]` (`EllipticCurveGeom.isClopen_naiveExactOrderLocus`), since two
points killed by `N` agree on an open and closed subscheme. The corresponding open subscheme of
`E[N]` therefore represents the functor of points of naive exact order `N`
(`EllipticCurveGeom.naiveExactOrderRepresentableBy`).

Following `EllipticCurveGeom.mulBy`, the group law on points of `E` is written multiplicatively:
`x ^ d` is the point `dx`, and `1` is the zero section.

## Main definitions

* `TauCeti.AlgebraicGeometry.EllipticCurveGeom.IsOfNaiveExactOrder E x N`: the point `x` has
  naive exact order `N`.
* `TauCeti.AlgebraicGeometry.EllipticCurveGeom.naiveExactOrderSubfunctor E N`: the points of `E`
  of naive exact order `N`, as a subfunctor of the functor of points of `E`.
* `TauCeti.AlgebraicGeometry.EllipticCurveGeom.naiveExactOrderLocus E N`: the set of points of
  `E[N]` over which the universal point of `E[N]` has naive exact order `N`.
* `TauCeti.AlgebraicGeometry.EllipticCurveGeom.naiveExactOrderOpens E hN`: that set as an open
  subscheme of `E[N]`, when `N` is invertible on `S`, with inclusion
  `TauCeti.AlgebraicGeometry.EllipticCurveGeom.naiveExactOrderι E hN`.

## Main results

* `TauCeti.AlgebraicGeometry.EllipticCurveGeom.isOfNaiveExactOrder_iff_orderOf_eq`: over a field,
  a point has naive exact order `N` exactly when its order in the group of points is `N`.
* `TauCeti.AlgebraicGeometry.EllipticCurveGeom.IsOfNaiveExactOrder.pointsPullback`: points of
  naive exact order `N` are stable under base change of the elliptic curve.
* `TauCeti.AlgebraicGeometry.EllipticCurveGeom.isOfNaiveExactOrder_pointsBaseChangeEquiv_iff`:
  identifying points of a base change with points valued in the new base preserves and reflects
  naive exact order.
* `TauCeti.AlgebraicGeometry.EllipticCurveGeom.exists_isOfNaiveExactOrder_over`: over each
  separably closed field point where `N` is invertible, there is a point of naive exact order `N`.
* `TauCeti.AlgebraicGeometry.EllipticCurveGeom.isFiberwiseInjective_iff_isOfNaiveExactOrder`: a
  homomorphism `ℤ/Nℤ →* E(S)` is a naive `[Γ₁(N)]`-structure exactly when the image of `1` has naive
  exact order `N`.
* `TauCeti.AlgebraicGeometry.EllipticCurveGeom.isOfNaiveExactOrder_comp_torsionι_iff`: a point of
  `E[N]` has naive exact order `N` exactly when it lands in `naiveExactOrderLocus E N`.
* `TauCeti.AlgebraicGeometry.EllipticCurveGeom.isClopen_naiveExactOrderLocus`: if `N` is
  invertible on `S`, that locus is open and closed in `E[N]`.
* `TauCeti.AlgebraicGeometry.EllipticCurveGeom.naiveExactOrderRepresentableBy`: if `N` is
  invertible on `S`, the open subscheme `naiveExactOrderOpens E hN` of `E[N]` represents the
  points of `E` of naive exact order `N`.

## References

* N. M. Katz and B. Mazur, *Arithmetic Moduli of Elliptic Curves*, 1.4.4 and §3.7 (naive level
  structures).
* D. Loeffler, *Modular Curves*, lecture notes, §3.8.
-/

public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory AlgebraicGeometry MonObj
  Opposite

universe u

namespace TauCeti.AlgebraicGeometry

namespace EllipticCurveGeom

variable {S : Scheme.{u}} (E : EllipticCurveGeom S)

/-- **Points of naive exact order `N`.** A point `x` of an elliptic curve `E` over `S`, with values
in a scheme `Z` over `S`, has naive exact order `N` when `Nx = 0` and, for every divisor `d ≠ N`
of `N`, the point `dx` meets the zero section nowhere: the equalizer of `dx` and `0` is empty.
Over a field this says that `x` has order exactly `N` (`isOfNaiveExactOrder_iff_orderOf_eq`).
For `N = 0` every `d ≥ 1` divides `N`, so this asks that `x` have infinite order in every fibre. -/
def IsOfNaiveExactOrder {Z : Over S} (x : Z ⟶ Over.mk E.structureMap) (N : ℕ) : Prop :=
  x ^ N = 1 ∧ ∀ d : ℕ, d ∣ N → d ≠ N → IsEmpty (equalizer (x ^ d) 1).left

variable {E} {Z : Over S} {x : Z ⟶ Over.mk E.structureMap} {N : ℕ}

/-- The defining property of a point of naive exact order `N`. -/
theorem isOfNaiveExactOrder_iff :
    E.IsOfNaiveExactOrder x N ↔
      x ^ N = 1 ∧ ∀ d : ℕ, d ∣ N → d ≠ N → IsEmpty (equalizer (x ^ d) 1).left :=
  Iff.rfl

/-- A point of naive exact order `N` is killed by `N`. -/
theorem IsOfNaiveExactOrder.pow_eq_one (h : E.IsOfNaiveExactOrder x N) : x ^ N = 1 :=
  h.1

/-- A point of naive exact order `N` is killed by multiplication by `N`, so it is a point of the
`N`-torsion `E[N]` (`EllipticCurveGeom.exists_comp_torsionι_iff`). -/
theorem IsOfNaiveExactOrder.comp_mulBy_eq_one (h : E.IsOfNaiveExactOrder x N) :
    x ≫ E.mulBy N = 1 := by
  rw [comp_mulBy, zpow_natCast, h.pow_eq_one]

/-- If `x` has naive exact order `N`, then for every divisor `d ≠ N` of `N` the point `dx` meets
the zero section nowhere. -/
theorem IsOfNaiveExactOrder.isEmpty_equalizer (h : E.IsOfNaiveExactOrder x N) {d : ℕ}
    (hd : d ∣ N) (hdN : d ≠ N) : IsEmpty (equalizer (x ^ d) 1).left :=
  h.2 d hd hdN

/-- **Points of naive exact order `N` pull back**: if `x` has naive exact order `N`, then so has
its composite with any morphism `k : Z' ⟶ Z` of schemes over `S`. -/
theorem IsOfNaiveExactOrder.comp {Z' : Over S} (h : E.IsOfNaiveExactOrder x N) (k : Z' ⟶ Z) :
    E.IsOfNaiveExactOrder (k ≫ x) N := by
  refine ⟨by rw [← comp_pow, h.pow_eq_one, comp_one], fun d hd hdN ↦ ?_⟩
  have := h.isEmpty_equalizer hd hdN
  rw [isEmpty_equalizer_congr (comp_pow x d k).symm (comp_one k).symm,
    isEmpty_equalizer_comp_iff]
  simp [Set.range_eq_empty]

/-- The only point of naive exact order one is the zero section. -/
@[simp]
theorem isOfNaiveExactOrder_one_iff : E.IsOfNaiveExactOrder x 1 ↔ x = 1 := by
  refine ⟨fun h ↦ by simpa using h.pow_eq_one, ?_⟩
  rintro rfl
  exact ⟨one_pow 1, fun d hd hd1 ↦ absurd (Nat.dvd_one.mp hd) hd1⟩

/-! ### Over a field -/

section Field

variable {K : Type u} [Field K] {E : EllipticCurveGeom (Spec (.of K))}

/-- **Naive exact order over a field.** A `K`-point of an elliptic curve over a field `K` has naive
exact order `N` exactly when its order in the group of `K`-points is `N`. -/
theorem isOfNaiveExactOrder_iff_orderOf_eq
    {P : 𝟙_ (Over (Spec (.of K))) ⟶ Over.mk E.structureMap} :
    E.IsOfNaiveExactOrder P N ↔ orderOf P = N := by
  simp only [isOfNaiveExactOrder_iff, isEmpty_equalizer_iff_ne]
  refine ⟨fun ⟨h₁, h₂⟩ ↦ ?_, ?_⟩
  · by_contra hne
    exact h₂ _ (orderOf_dvd_of_pow_eq_one h₁) hne (pow_orderOf_eq_one P)
  · rintro rfl
    exact ⟨pow_orderOf_eq_one P, fun d hd hdN hP ↦
      hdN (Nat.dvd_antisymm hd (orderOf_dvd_of_pow_eq_one hP))⟩

end Field

/-! ### Base change -/

section BaseChange

variable {S' : Scheme.{u}} {E' : EllipticCurveGeom S'} {g : E'.carrier ⟶ E.carrier}
  {f : S' ⟶ S} (hg : IsPullback g E'.structureMap E.structureMap f)
  (h0 : E'.zero ≫ g = f ≫ E.zero)

/-- **Points of naive exact order `N` are stable under base change**: if an `S`-point `P` of `E`
has naive exact order `N`, then so does its base change, the `S'`-point `P'` of `E'`. -/
theorem IsOfNaiveExactOrder.pointsPullback {P : 𝟙_ (Over S) ⟶ Over.mk E.structureMap}
    (h : E.IsOfNaiveExactOrder P N) : E'.IsOfNaiveExactOrder (pointsPullback hg h0 P) N := by
  refine ⟨by rw [← map_pow, h.pow_eq_one, map_one], fun d hd hdN ↦ ?_⟩
  have := h.isEmpty_equalizer hd hdN
  rw [isEmpty_equalizer_congr (map_pow _ P d).symm rfl]
  -- the equalizer of `P' ^ d` and `1`, viewed over `S`, maps to the equalizer of `P ^ d` and `1`
  let ι' := equalizer.ι (EllipticCurveGeom.pointsPullback hg h0 (P ^ d)) 1
  let V : Over S := Over.mk (ι'.left ≫ f)
  have hV : (toUnit V).left = ι'.left ≫ f := by simp [V]
  have hι : (equalizer (EllipticCurveGeom.pointsPullback hg h0 (P ^ d)) 1).hom = ι'.left := by
    simpa using (Over.w ι').symm
  have hc := congrArg CommaMorphism.left
    (equalizer.condition (EllipticCurveGeom.pointsPullback hg h0 (P ^ d)) 1)
  have hv : toUnit V ≫ P ^ d = toUnit V ≫ 1 := by
    ext1
    simp only [Over.comp_left, comp_one, hom_one_left, hV, Category.assoc] at hc ⊢
    rw [← pointsPullback_left_comp hg h0, reassoc_of% hc, hι, h0]
    simp [V]
  exact Function.isEmpty (equalizer.lift (toUnit V) hv).left

/-- Under the group equivalence identifying points of a base change with points valued in
the new base, naive exact order is preserved and reflected. -/
theorem isOfNaiveExactOrder_pointsBaseChangeEquiv_iff
    {P : 𝟙_ (Over S') ⟶ Over.mk E'.structureMap} :
    E.IsOfNaiveExactOrder (pointsBaseChangeEquiv hg h0 P) N ↔ E'.IsOfNaiveExactOrder P N := by
  simp only [isOfNaiveExactOrder_iff, ← map_pow, ← map_one (pointsBaseChangeEquiv hg h0),
    (pointsBaseChangeEquiv hg h0).injective.eq_iff]
  refine and_congr Iff.rfl (forall_congr' fun d ↦ ?_)
  refine imp_congr_right fun _ ↦ imp_congr_right fun _ ↦ ?_
  exact (isEmpty_equalizer_iff_of_isPullback hg (P ^ d) 1 _ _
    (pointsBaseChangeEquiv_left hg h0 _).symm
    (pointsBaseChangeEquiv_left hg h0 _).symm).symm

end BaseChange

/-! ### Comparison with injectivity on fibres -/

/-- **Where an `S`-point meets the zero section.** For an `S`-point `Q` of `E`, the image of the
equalizer of `Q` and the zero section is the set of points of `S` at which `Q` meets the zero
section. -/
theorem range_equalizer_ι_left_one (Q : 𝟙_ (Over S) ⟶ Over.mk E.structureMap) :
    Set.range (equalizer.ι Q 1).left = {s | Q.left s = E.zero s} := by
  rw [range_equalizer_ι_left_of_section, hom_one_left]
  rfl

/-- An `S`-point `Q` of `E` has empty equalizer with the zero section exactly when it meets the
zero section at no point of `S`. -/
theorem isEmpty_equalizer_one_iff (Q : 𝟙_ (Over S) ⟶ Over.mk E.structureMap) :
    IsEmpty (equalizer Q 1).left ↔ ∀ s, Q.left s ≠ E.zero s := by
  simp [isEmpty_equalizer_iff_forall_ne, hom_one_left]

/-- **Naive `[Γ₁(N)]`-structures are the `S`-points of naive exact order `N`.** A homomorphism
`φ : ℤ/Nℤ →* E(S)` is injective on every fibre, that is, it is a naive `[Γ₁(N)]`-structure
(`ModuliProblem.gammaOneNaive`), exactly when the `S`-point `φ 1` has naive exact order `N`. -/
theorem isFiberwiseInjective_iff_isOfNaiveExactOrder
    {φ : Multiplicative (ZMod N) →* (𝟙_ (Over S) ⟶ Over.mk E.structureMap)} :
    E.IsFiberwiseInjective φ ↔ E.IsOfNaiveExactOrder (φ (.ofAdd 1)) N := by
  have hφ (k : ℕ) : φ (.ofAdd 1) ^ k = φ (.ofAdd (k : ZMod N)) := by
    rw [← map_pow, ← ofAdd_nsmul, nsmul_one]
  have hN : φ (.ofAdd 1) ^ N = 1 := by simp [hφ]
  simp only [isFiberwiseInjective_iff, isOfNaiveExactOrder_iff, hN, true_and,
    isEmpty_equalizer_one_iff]
  refine ⟨fun h d hd hdN s hs ↦ hdN ?_, fun h a ha s hs ↦ ha ?_⟩
  · have h1 := by_contra fun h1 ↦ h _ h1 s (hφ d ▸ hs)
    rw [← ofAdd_zero, Multiplicative.ofAdd.injective.eq_iff, ZMod.natCast_eq_zero_iff] at h1
    exact Nat.dvd_antisymm hd h1
  -- restricted to the fibre over `κ(s)`, the point `φ 1` has order `N`
  let ψ := (pointsPullback (E.isPullback_baseChange (S.fromSpecResidueField s)) (by simp)).comp φ
  obtain ⟨p⟩ : Nonempty (Spec (S.residueField s)) := inferInstance
  have hψ (b : Multiplicative (ZMod N)) : ψ b = 1 ↔ (φ b).left s = E.zero s :=
    (eq_one_iff_left_apply_eq_zero _ _ p).trans <|
      (pointsPullback_left_apply_eq_zero_iff _ _ _ p).trans
        (by rw [Scheme.fromSpecResidueField_apply])
  have hord : orderOf (ψ (.ofAdd 1)) = N := by
    refine by_contra fun hne ↦ h _ (orderOf_dvd_of_pow_eq_one ?_) hne s ?_
    · rw [← map_pow, MonoidHom.comp_apply, map_pow, hN, map_one]
    · rw [← map_pow, ← hψ, map_pow, pow_orderOf_eq_one]
  -- `a` is `c • 1` for the integer `c` lifting `a`, and `ψ a = 1` forces `N ∣ c`
  have hc : a = .ofAdd 1 ^ (ZMod.cast a.toAdd : ℤ) := by
    rw [← ofAdd_zsmul, zsmul_one, ZMod.intCast_zmod_cast, ofAdd_toAdd]
  have ha := (hψ a).mpr hs
  rw [hc, map_zpow, ← orderOf_dvd_iff_zpow_eq_one, hord, ← ZMod.intCast_zmod_eq_zero_iff_dvd,
    ZMod.intCast_zmod_cast] at ha
  exact toAdd_eq_zero.mp ha

/-! ### Existence over separably closed fields -/

variable (E)

section SepClosed

variable {K : Type u} [Field K] [IsSepClosed K]
  (E : EllipticCurveGeom (Spec (.of K)))

/-- Over a separably closed field where `N` is invertible, an elliptic curve has a point of
naive exact order `N`. -/
theorem exists_isOfNaiveExactOrder (hN : (N : K) ≠ 0) :
    ∃ P : 𝟙_ (Over (Spec (.of K))) ⟶ Over.mk E.structureMap, E.IsOfNaiveExactOrder P N := by
  obtain ⟨φ, hφ⟩ := E.exists_isFiberwiseInjective hN
  let i : Multiplicative (ZMod N) →* Multiplicative (ZMod N × ZMod N) :=
    (AddMonoidHom.inl (ZMod N) (ZMod N)).toMultiplicative
  have hi : Function.Injective i := fun a b h ↦
    Multiplicative.toAdd.injective (congrArg Prod.fst (congrArg Multiplicative.toAdd h))
  exact ⟨_, E.isFiberwiseInjective_iff_isOfNaiveExactOrder.mp (hφ.comp hi)⟩

end SepClosed

/-- For a geometric point of the base in a characteristic prime to `N`, there is a point
of naive exact order `N` above it, valued in the same separably closed field. -/
theorem exists_isOfNaiveExactOrder_over {K : Type u} [Field K] [IsSepClosed K]
    (t : Spec (.of K) ⟶ S) (hN : (N : K) ≠ 0) :
    ∃ P : Over.mk t ⟶ Over.mk E.structureMap, E.IsOfNaiveExactOrder P N := by
  obtain ⟨P, hP⟩ := (E.baseChange t).exists_isOfNaiveExactOrder hN
  let hg := E.isPullback_baseChange t
  have h0 : (E.baseChange t).zero ≫ (E.baseChangeIso t).hom ≫
      pullback.fst E.structureMap t = t ≫ E.zero := by simp
  exact ⟨pointsBaseChangeEquiv hg h0 P,
    (isOfNaiveExactOrder_pointsBaseChangeEquiv_iff hg h0).mpr hP⟩

variable {E}

/-! ### The functor of points of naive exact order `N` -/

variable (E N) in
/-- **The functor of points of naive exact order `N`**: the subfunctor of the functor of points
`Z ↦ (Z ⟶ E)` of `E`, on schemes over `S`, whose values at `Z` are the points of naive exact
order `N` with values in `Z`. -/
def naiveExactOrderSubfunctor : Subfunctor (yoneda.obj (Over.mk E.structureMap)) where
  obj _ := {x | E.IsOfNaiveExactOrder x N}
  map k _ hx := hx.comp k.unop

/-- The values of `naiveExactOrderSubfunctor E N` are the points of naive exact order `N`. -/
@[simp]
theorem mem_naiveExactOrderSubfunctor_obj {Z : (Over S)ᵒᵖ}
    {x : Z.unop ⟶ Over.mk E.structureMap} :
    x ∈ (E.naiveExactOrderSubfunctor N).obj Z ↔ E.IsOfNaiveExactOrder x N :=
  Iff.rfl

/-! ### The locus of naive exact order `N` in `E[N]` -/

variable (E N) in
/-- **The locus of naive exact order `N` in `E[N]`**: the set of points of the `N`-torsion `E[N]`
at which, for no divisor `d ≠ N` of `N`, the `d`-th multiple of the inclusion `E[N] ⟶ E` agrees
with the zero section. -/
def naiveExactOrderLocus : Set (E.torsion N).X.left :=
  {e | ∀ d : ℕ, d ∣ N → d ≠ N → e ∉ Set.range (equalizer.ι (E.torsionι N ^ d) 1).left}

/-- A point of `E[N]` lies in the locus of naive exact order `N` when, for every divisor `d ≠ N`
of `N`, it is not in the equalizer of the `d`-th multiple of the inclusion `E[N] ⟶ E` and the
zero section. -/
theorem mem_naiveExactOrderLocus_iff {e : (E.torsion N).X.left} :
    e ∈ E.naiveExactOrderLocus N ↔
      ∀ d : ℕ, d ∣ N → d ≠ N → e ∉ Set.range (equalizer.ι (E.torsionι N ^ d) 1).left :=
  Iff.rfl

/-- **Points of `E[N]` of naive exact order `N`.** A point `y` of the `N`-torsion `E[N]` with
values in `Z` has naive exact order `N`, as a point of `E`, exactly when it maps `Z` into
`naiveExactOrderLocus E N`. -/
theorem isOfNaiveExactOrder_comp_torsionι_iff (y : Z ⟶ (E.torsion N).X) :
    E.IsOfNaiveExactOrder (y ≫ E.torsionι N) N ↔
      Set.range y.left ⊆ E.naiveExactOrderLocus N := by
  have h₁ : (y ≫ E.torsionι N) ^ N = 1 := by
    simpa using E.comp_torsionι_zpow N y
  refine ⟨fun h ↦ ?_, fun h ↦ ⟨h₁, fun d hd hdN ↦ ?_⟩⟩
  · rintro _ ⟨t, rfl⟩ d hd hdN
    have := h.isEmpty_equalizer hd hdN
    rw [isEmpty_equalizer_congr (comp_pow _ d y).symm (comp_one y).symm,
      isEmpty_equalizer_comp_iff] at this
    exact Set.disjoint_left.mp this ⟨t, rfl⟩
  · rw [isEmpty_equalizer_congr (comp_pow _ d y).symm (comp_one y).symm,
      isEmpty_equalizer_comp_iff]
    exact Set.disjoint_left.mpr fun e he he' ↦ h he d hd hdN he'

/-- **The locus of naive exact order `N` is open and closed** in `E[N]` when `N` is invertible in
every residue field of `S`. Each of the finitely many conditions `dx ≠ 0` cuts out the complement
of the set where two points killed by `N` agree, which is open and closed
(`EllipticCurveGeom.isClopen_range_equalizer_ι_left_of_mulBy_eq_one`). -/
theorem isClopen_naiveExactOrderLocus (hN : ∀ s : S, (N : S.residueField s) ≠ 0) :
    IsClopen (E.naiveExactOrderLocus N) := by
  rcases eq_or_ne N 0 with rfl | hN₀
  · -- `0` is invertible on no nonempty scheme, so `S`, and with it `E[0]`, is empty
    have : IsEmpty S := ⟨fun s ↦ hN s Nat.cast_zero⟩
    have : IsEmpty (E.torsion (0 : ℕ)).X.left := Function.isEmpty (E.torsion (0 : ℕ)).X.hom
    rw [Set.eq_empty_of_isEmpty (E.naiveExactOrderLocus 0)]
    exact isClopen_empty
  have key : E.naiveExactOrderLocus N =
      ⋂ d ∈ N.properDivisors, (Set.range (equalizer.ι (E.torsionι N ^ d) 1).left)ᶜ := by
    ext e
    simp only [mem_naiveExactOrderLocus_iff, Set.mem_iInter, Set.mem_compl_iff,
      Nat.mem_properDivisors]
    exact ⟨fun h d hd ↦ h d hd.1 hd.2.ne, fun h d hd hdN ↦
      h d ⟨hd, (Nat.le_of_dvd (Nat.pos_of_ne_zero hN₀) hd).lt_of_ne hdN⟩⟩
  rw [key]
  refine isClopen_biInter_finset fun d _ ↦
    (E.isClopen_range_equalizer_ι_left_of_mulBy_eq_one (n := N) (fun s ↦ ?_) ?_ (by simp)).compl
  · exact_mod_cast hN s
  · rw [comp_mulBy, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, torsionι_zpow, one_zpow]

variable (E) in
/-- **The scheme of points of naive exact order `N`**: when `N` is invertible in every residue
field of `S`, the open subscheme of the `N`-torsion `E[N]` with underlying set
`naiveExactOrderLocus E N`. -/
def naiveExactOrderOpens (hN : ∀ s : S, (N : S.residueField s) ≠ 0) :
    (E.torsion N).X.left.Opens :=
  ⟨E.naiveExactOrderLocus N, (E.isClopen_naiveExactOrderLocus hN).isOpen⟩

/-- The underlying set of `naiveExactOrderOpens E hN` is the locus of naive exact order `N`. -/
@[simp]
theorem coe_naiveExactOrderOpens (hN : ∀ s : S, (N : S.residueField s) ≠ 0) :
    (E.naiveExactOrderOpens hN : Set (E.torsion N).X.left) = E.naiveExactOrderLocus N :=
  (rfl)

section Representable

variable (hN : ∀ s : S, (N : S.residueField s) ≠ 0)

variable (E) in
/-- The inclusion of the open subscheme `naiveExactOrderOpens E hN` into `E[N]`, as a morphism of
schemes over `S`. -/
noncomputable def naiveExactOrderι :
    Over.mk ((E.naiveExactOrderOpens hN).ι ≫ (E.torsion N).X.hom) ⟶ (E.torsion N).X :=
  Over.homMk (E.naiveExactOrderOpens hN).ι rfl

/-- The morphism of schemes underlying `naiveExactOrderι E hN` is the open immersion. -/
@[simp]
theorem naiveExactOrderι_left : (E.naiveExactOrderι hN).left = (E.naiveExactOrderOpens hN).ι :=
  (rfl)

/-- The inclusion of `naiveExactOrderOpens E hN` into `E[N]` is a monomorphism. -/
instance mono_naiveExactOrderι : Mono (E.naiveExactOrderι hN) :=
  Over.mono_homMk _

private theorem isOfNaiveExactOrder_comp_naiveExactOrderι
    (u : Z ⟶ Over.mk ((E.naiveExactOrderOpens hN).ι ≫ (E.torsion N).X.hom)) :
    E.IsOfNaiveExactOrder (u ≫ E.naiveExactOrderι hN ≫ E.torsionι N) N := by
  rw [← Category.assoc, isOfNaiveExactOrder_comp_torsionι_iff]
  rintro _ ⟨t, rfl⟩
  rw [← coe_naiveExactOrderOpens hN, ← Scheme.Opens.range_ι]
  exact ⟨u.left t, rfl⟩

-- The point of the open subscheme `naiveExactOrderOpens E hN` given by a point of `E` of naive
-- exact order `N`: the point of `E[N]` it defines lands in the locus of naive exact order `N`.
private noncomputable def naiveExactOrderLift (hx : E.IsOfNaiveExactOrder x N) :
    Z ⟶ Over.mk ((E.naiveExactOrderOpens hN).ι ≫ (E.torsion N).X.hom) :=
  Over.homMk (IsOpenImmersion.lift (E.naiveExactOrderOpens hN).ι
      (torsionLift x hx.comp_mulBy_eq_one).left (by
        rw [Scheme.Opens.range_ι, coe_naiveExactOrderOpens,
          ← isOfNaiveExactOrder_comp_torsionι_iff, torsionLift_torsionι]
        exact hx))
    ((IsOpenImmersion.lift_fac_assoc _ _ _ _).trans (Over.w _))

private theorem naiveExactOrderLift_naiveExactOrderι (hx : E.IsOfNaiveExactOrder x N) :
    naiveExactOrderLift hN hx ≫ E.naiveExactOrderι hN = torsionLift x hx.comp_mulBy_eq_one := by
  ext1
  simp [naiveExactOrderLift]

/-- **The scheme of points of naive exact order `N` represents them.** When `N` is invertible in
every residue field of `S`, morphisms over `S` from `Z` to the open subscheme
`naiveExactOrderOpens E hN` of `E[N]` correspond, by composing with the inclusions into `E[N]` and
into `E`, to the points of `E` of naive exact order `N` with values in `Z`, naturally in `Z`. -/
noncomputable def naiveExactOrderRepresentableBy :
    (E.naiveExactOrderSubfunctor N).toFunctor.RepresentableBy
      (Over.mk ((E.naiveExactOrderOpens hN).ι ≫ (E.torsion N).X.hom)) where
  homEquiv :=
    { toFun u := ⟨u ≫ E.naiveExactOrderι hN ≫ E.torsionι N,
        isOfNaiveExactOrder_comp_naiveExactOrderι hN u⟩
      invFun x := naiveExactOrderLift hN (mem_naiveExactOrderSubfunctor_obj.mp x.2)
      left_inv u := by
        -- both sides are morphisms into an open subscheme of `E[N]`, a monomorphism into `E`
        refine (cancel_mono (E.naiveExactOrderι hN ≫ E.torsionι N)).mp ?_
        rw [reassoc_of% naiveExactOrderLift_naiveExactOrderι, torsionLift_torsionι]
      right_inv x := Subtype.ext <| by
        simp [reassoc_of% naiveExactOrderLift_naiveExactOrderι] }
  homEquiv_comp _ _ := Subtype.ext (Category.assoc _ _ _)

/-- The point of naive exact order `N` corresponding to a morphism `u` into the open subscheme
`naiveExactOrderOpens E hN` of `E[N]` is the composite of `u` with the inclusions into `E[N]` and
into `E`. -/
theorem coe_naiveExactOrderRepresentableBy_homEquiv
    (u : Z ⟶ Over.mk ((E.naiveExactOrderOpens hN).ι ≫ (E.torsion N).X.hom)) :
    ((E.naiveExactOrderRepresentableBy hN).homEquiv u : Z ⟶ Over.mk E.structureMap) =
      u ≫ E.naiveExactOrderι hN ≫ E.torsionι N :=
  (rfl)

end Representable

end EllipticCurveGeom

end TauCeti.AlgebraicGeometry
