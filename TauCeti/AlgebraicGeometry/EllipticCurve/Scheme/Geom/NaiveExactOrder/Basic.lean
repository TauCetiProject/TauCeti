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
`p` in Drinfeld's sense. Accordingly the scheme of points of naive exact order `N` below is open in
`E[N]` for every `N ≠ 0`, and it is closed in `E[N]`, and so finite over `S`, whenever
`N` is invertible; closedness need not hold over an arbitrary base. Points of naive exact order `N`
are stable under base change, both along morphisms `Z' ⟶ Z`
(`EllipticCurveGeom.IsOfNaiveExactOrder.comp`) and along base change of the elliptic curve
(`EllipticCurveGeom.IsOfNaiveExactOrder.pointsPullback`).

A point of `E[N]` with values in `Z` has naive exact order `N` exactly when it maps `Z` into the
naive locus `EllipticCurveGeom.naiveLocus (E.torsionPointHom N)` of the universal point `P` of
`E[N]`: the set of points of `E[N]` at which no multiple `aP` with `a ≠ 0` meets the zero section
(`EllipticCurveGeom.isOfNaiveExactOrder_comp_torsionι_iff`). For `N ≠ 0` this set is open
(`EllipticCurveGeom.isOpen_naiveLocus`), and the corresponding open subscheme
`EllipticCurveGeom.naiveLocusOver (E.torsionPointHom N)` of `E[N]`, which also represents the naive
moduli problem `[Γ₁(N)]` over `Ell/B` (`ModuliProblem.gammaOneNaiveRelRepData`), represents the
functor of points of naive exact order `N` (`EllipticCurveGeom.naiveExactOrderRepresentableBy`).
Pulling it back along an `S`-point `P` gives the locus of `S` over which `P` has naive exact order
`N` (`EllipticCurveGeom.naiveExactOrderPreimage`): a morphism `T ⟶ S` factors through it exactly
when the base change of `P` to `T` has naive exact order `N`
(`EllipticCurveGeom.exists_lift_naiveExactOrderPreimageι_iff`). Where `N` is invertible on `S`,
the naive locus is closed in `E[N]` as well (`EllipticCurveGeom.isClopen_naiveLocus`), so this
locus is a closed subscheme of `S` (`EllipticCurveGeom.isClosedImmersion_naiveExactOrderPreimageι`).

Following `EllipticCurveGeom.mulBy`, the group law on points of `E` is written multiplicatively:
`x ^ d` is the point `dx`, and `1` is the zero section.

## Main definitions

* `TauCeti.AlgebraicGeometry.EllipticCurveGeom.IsOfNaiveExactOrder E x N`: the point `x` has
  naive exact order `N`.
* `TauCeti.AlgebraicGeometry.EllipticCurveGeom.naiveExactOrderSubfunctor E N`: the points of `E`
  of naive exact order `N`, as a subfunctor of the functor of points of `E`.
* `TauCeti.AlgebraicGeometry.EllipticCurveGeom.naiveExactOrderPreimage N P`: the locus of `S`
  over which an `S`-point `P` has naive exact order `N ≠ 0`, with inclusion
  `TauCeti.AlgebraicGeometry.EllipticCurveGeom.naiveExactOrderPreimageι N P`.

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
* `TauCeti.AlgebraicGeometry.EllipticCurveGeom.isOfNaiveExactOrder_iff_forall_lt`: a point `x` has
  naive exact order `N` exactly when `Nx = 0` and `kx` meets the zero section nowhere for
  `0 < k < N`.
* `TauCeti.AlgebraicGeometry.EllipticCurveGeom.isOfNaiveExactOrder_comp_torsionι_iff`: a point of
  `E[N]` has naive exact order `N` exactly when it lands in the naive locus of the universal point
  of `E[N]`.
* `TauCeti.AlgebraicGeometry.EllipticCurveGeom.naiveExactOrderRepresentableBy`: for `N ≠ 0`, the
  naive locus of the universal point of `E[N]`, an open subscheme of `E[N]`, represents the points
  of `E` of naive exact order `N`.
* `TauCeti.AlgebraicGeometry.EllipticCurveGeom.exists_lift_naiveExactOrderPreimageι_iff`: a
  morphism `T ⟶ S` factors through the locus where `P` has naive exact order `N` exactly when the
  base change of `P` to `T` has naive exact order `N`.
* `TauCeti.AlgebraicGeometry.EllipticCurveGeom.isClosedImmersion_naiveExactOrderPreimageι`: where
  `N` is invertible on `S`, the locus where `P` has naive exact order `N` is a closed subscheme
  of `S`.

## References

* N. M. Katz and B. Mazur, *Arithmetic Moduli of Elliptic Curves*, 1.4.4 and §3.7 (naive level
  structures).
* P. Deligne and M. Rapoport, *Les schémas de modules de courbes elliptiques*, LNM 349, IV,
  Construction 4.8 (a naive `[Γ₁(N)]`-structure as a section everywhere of exact order `N`).
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

/-- Under the group equivalence identifying points of a base change with points valued in
the new base, naive exact order is preserved and reflected. -/
theorem isOfNaiveExactOrder_pointsBaseChangeEquiv_iff
    {P : 𝟙_ (Over S') ⟶ Over.mk E'.structureMap} :
    E.IsOfNaiveExactOrder (pointsBaseChangeEquiv hg h0 P) N ↔ E'.IsOfNaiveExactOrder P N := by
  simp only [isOfNaiveExactOrder_iff, ← map_pow, ← map_one (pointsBaseChangeEquiv hg h0),
    (pointsBaseChangeEquiv hg h0).injective.eq_iff]
  refine and_congr Iff.rfl (forall_congr' fun d ↦ ?_)
  refine imp_congr_right fun _ ↦ imp_congr_right fun _ ↦ ?_
  exact (isEmpty_equalizer_iff_of_isPullback hg (Category.id_comp f) (P ^ d) 1 _ _
    (pointsBaseChangeEquiv_left hg h0 _).symm
    (pointsBaseChangeEquiv_left hg h0 _).symm).symm

/-- **Points of naive exact order `N` are stable under base change**: if an `S`-point `P` of `E`
has naive exact order `N`, then so does its base change, the `S'`-point `P'` of `E'`. -/
theorem IsOfNaiveExactOrder.pointsPullback {P : 𝟙_ (Over S) ⟶ Over.mk E.structureMap}
    (h : E.IsOfNaiveExactOrder P N) : E'.IsOfNaiveExactOrder (pointsPullback hg h0 P) N := by
  apply (isOfNaiveExactOrder_pointsBaseChangeEquiv_iff hg h0).mp
  have hP : pointsBaseChangeEquiv hg h0 (EllipticCurveGeom.pointsPullback hg h0 P) =
      toUnit (Over.mk f) ≫ P := by
    ext1
    simp
  rw [hP]
  exact h.comp (toUnit (Over.mk f))

end BaseChange

/-! ### Comparison with injectivity on fibres -/

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

section Locus

variable [NeZero N]

/-- **Naive exact order among the multiples below `N`.** A point `x` of `E` with values in `Z` has
naive exact order `N ≠ 0` exactly when `Nx = 0` and, for every `0 < k < N`, the point `kx` meets the
zero section nowhere: where `kx` and `Nx` meet the zero section, so does `gcd(k, N) x`, a proper
multiple. -/
theorem isOfNaiveExactOrder_iff_forall_lt :
    E.IsOfNaiveExactOrder x N ↔
      x ^ N = 1 ∧ ∀ k : ℕ, 0 < k → k < N → IsEmpty (equalizer (x ^ k) 1).left := by
  refine and_congr_right fun hN ↦ ⟨fun h k hk hkN ↦ ?_, fun h d hd hdN ↦ ?_⟩
  · -- the equalizer of `kx` and `0` maps to that of `gcd(k, N) x` and `0`, which is empty
    have hg : k.gcd N ≠ N := fun hg ↦ (Nat.le_of_dvd hk (hg ▸ Nat.gcd_dvd_left k N)).not_gt hkN
    have := h _ (Nat.gcd_dvd_right k N) hg
    refine Function.isEmpty
      (equalizer.lift (equalizer.ι (x ^ k) 1) (f := x ^ (k.gcd N)) (g := 1) ?_).left
    rw [comp_pow, comp_one, pow_gcd_eq_one, ← comp_pow, ← comp_pow, equalizer.condition, comp_one,
      hN, comp_one]
    exact ⟨rfl, rfl⟩
  · have hN₀ := Nat.pos_of_ne_zero (NeZero.ne N)
    exact h d (Nat.pos_of_dvd_of_pos hd hN₀) ((Nat.le_of_dvd hN₀ hd).lt_of_ne hdN)

/-- **Points of `E[N]` of naive exact order `N`.** A point `y` of the `N`-torsion `E[N]` with
values in `Z` has naive exact order `N`, as a point of `E`, exactly when it maps `Z` into the naive
locus of the universal point `P` of `E[N]` (`EllipticCurveGeom.torsionPointHom`), the set of points
of `E[N]` at which no multiple `aP` with `a ≠ 0` meets the zero section. -/
theorem isOfNaiveExactOrder_comp_torsionι_iff (y : Z ⟶ (E.torsion N).X) :
    E.IsOfNaiveExactOrder (y ≫ E.torsionι N) N ↔
      Set.range y.left ⊆ naiveLocus (E.torsionPointHom N) := by
  have h₁ : (y ≫ E.torsionι N) ^ N = 1 := by
    simpa using E.comp_torsionι_zpow N y
  have hk (k : ℕ) : IsEmpty (equalizer ((y ≫ E.torsionι N) ^ k) 1).left ↔
      ∀ t, (y ≫ E.torsionι N ^ k).left t ≠ E.zero (Z.hom t) := by
    rw [← Set.range_eq_empty_iff, range_equalizer_ι_left_one, Set.eq_empty_iff_forall_notMem,
      comp_pow]
    exact Iff.rfl
  simp only [isOfNaiveExactOrder_iff_forall_lt, h₁, true_and, hk,
    range_left_subset_naiveLocus_iff]
  -- every `a ≠ 0` in `ℤ/Nℤ` is `k • 1` for a unique `0 < k < N`
  refine ⟨fun h a ha ↦ ?_, fun h k hk hkN ↦ ?_⟩
  · have hval : a.toAdd.val ≠ 0 := by
      rwa [Ne, ZMod.val_eq_zero, ← ofAdd_eq_one, ofAdd_toAdd]
    have := h _ (Nat.pos_of_ne_zero hval) (ZMod.val_lt a.toAdd)
    rwa [← torsionPointHom_ofAdd, ofAdd_toAdd] at this
  · have := h (.ofAdd (k : ZMod N)) (by
      rw [Ne, ofAdd_eq_one, ZMod.natCast_eq_zero_iff]
      exact Nat.not_dvd_of_pos_of_lt hk hkN)
    rwa [torsionPointHom_ofAdd, ZMod.val_natCast, Nat.mod_eq_of_lt hkN] at this

private theorem isOfNaiveExactOrder_comp_naiveLocusι
    (u : Z ⟶ naiveLocusOver (E.torsionPointHom N)) :
    E.IsOfNaiveExactOrder (u ≫ naiveLocusι (E.torsionPointHom N) ≫ E.torsionι N) N := by
  rw [← Category.assoc, isOfNaiveExactOrder_comp_torsionι_iff]
  rintro _ ⟨t, rfl⟩
  rw [Over.comp_left, Scheme.Hom.comp_apply, naiveLocusι_left, ← coe_naiveLocusOpens,
    ← Scheme.Opens.range_ι]
  exact ⟨u.left t, rfl⟩

-- The point of the naive locus of the universal point of `E[N]` given by a point of `E` of naive
-- exact order `N`: the point of `E[N]` it defines lands in the naive locus.
private noncomputable def naiveExactOrderLift (hx : E.IsOfNaiveExactOrder x N) :
    Z ⟶ naiveLocusOver (E.torsionPointHom N) :=
  Over.homMk (IsOpenImmersion.lift (naiveLocusOpens (E.torsionPointHom N)).ι
      (torsionLift x hx.comp_mulBy_eq_one).left (by
        rw [Scheme.Opens.range_ι, coe_naiveLocusOpens, ← isOfNaiveExactOrder_comp_torsionι_iff,
          torsionLift_torsionι]
        exact hx))
    ((IsOpenImmersion.lift_fac_assoc _ _ _ _).trans (Over.w _))

private theorem naiveExactOrderLift_naiveLocusι (hx : E.IsOfNaiveExactOrder x N) :
    naiveExactOrderLift hx ≫ naiveLocusι (E.torsionPointHom N) =
      torsionLift x hx.comp_mulBy_eq_one := by
  ext1
  simp [naiveExactOrderLift]

variable (E N) in
/-- **The scheme of points of naive exact order `N` represents them.** For `N ≠ 0`, morphisms over
`S` from `Z` to the naive locus of the universal point of `E[N]`, the open subscheme of `E[N]`
representing the naive moduli problem `[Γ₁(N)]`, correspond, by composing with the inclusions into
`E[N]` and into `E`, to the points of `E` of naive exact order `N` with values in `Z`, naturally
in `Z`. -/
noncomputable def naiveExactOrderRepresentableBy :
    (E.naiveExactOrderSubfunctor N).toFunctor.RepresentableBy
      (naiveLocusOver (E.torsionPointHom N)) where
  homEquiv :=
    { toFun u := ⟨u ≫ naiveLocusι (E.torsionPointHom N) ≫ E.torsionι N,
        isOfNaiveExactOrder_comp_naiveLocusι u⟩
      invFun x := naiveExactOrderLift (mem_naiveExactOrderSubfunctor_obj.mp x.2)
      left_inv u := by
        -- both sides are morphisms into an open subscheme of `E[N]`, a monomorphism into `E`
        refine (cancel_mono (naiveLocusι (E.torsionPointHom N) ≫ E.torsionι N)).mp ?_
        rw [reassoc_of% naiveExactOrderLift_naiveLocusι, torsionLift_torsionι]
      right_inv x := Subtype.ext <| by
        simp [reassoc_of% naiveExactOrderLift_naiveLocusι] }
  homEquiv_comp _ _ := Subtype.ext (Category.assoc _ _ _)

/-- The point of naive exact order `N` corresponding to a morphism `u` into the naive locus of the
universal point of `E[N]` is the composite of `u` with the inclusions into `E[N]` and into `E`. -/
theorem coe_naiveExactOrderRepresentableBy_homEquiv (u : Z ⟶ naiveLocusOver (E.torsionPointHom N)) :
    ((E.naiveExactOrderRepresentableBy N).homEquiv u : Z ⟶ Over.mk E.structureMap) =
      u ≫ naiveLocusι (E.torsionPointHom N) ≫ E.torsionι N :=
  (rfl)

/-! ### The locus where an `S`-point has naive exact order `N` -/

variable (N) (P : 𝟙_ (Over S) ⟶ Over.mk E.structureMap)

/-- **The locus where an `S`-point has naive exact order `N`**: for `N ≠ 0`, the preimage under
the `S`-point `P` of the naive locus of the universal point of `E[N]`, the open subscheme of `E[N]`
of points of naive exact order `N`. A morphism `t : T ⟶ S` factors through it exactly when the base
change of `P` along `t` has naive exact order `N` (`exists_lift_naiveExactOrderPreimageι_iff`). -/
noncomputable def naiveExactOrderPreimage : Scheme.{u} :=
  pullback P.left ((naiveLocusOpens (E.torsionPointHom N)).ι ≫ (E.torsionι N).left)

/-- The inclusion of the locus where `P` has naive exact order `N` into `S`. -/
noncomputable def naiveExactOrderPreimageι : naiveExactOrderPreimage N P ⟶ S :=
  pullback.fst _ _

/-- The inclusion of the locus where `P` has naive exact order `N` into `S` is a monomorphism. -/
instance mono_naiveExactOrderPreimageι : Mono (naiveExactOrderPreimageι N P) :=
  inferInstanceAs (Mono (pullback.fst _ _))

/-- The restriction of `P` to the locus where `P` has naive exact order `N`, as a point of the
naive locus of the universal point of `E[N]`, the scheme of points of naive exact order `N`. -/
noncomputable def naiveExactOrderPreimagePoint :
    naiveExactOrderPreimage N P ⟶ naiveLocusOpens (E.torsionPointHom N) :=
  pullback.snd _ _

/-- The locus where `P` has naive exact order `N` is the preimage under `P` of the naive locus of
the universal point of `E[N]`. -/
theorem isPullback_naiveExactOrderPreimage :
    IsPullback (naiveExactOrderPreimageι N P) (naiveExactOrderPreimagePoint N P) P.left
      ((naiveLocusOpens (E.torsionPointHom N)).ι ≫ (E.torsionι N).left) :=
  .of_hasPullback _ _

/-- **The universal property of the locus where `P` has naive exact order `N`.** Let `x` be the
point of `E` with values in a scheme `Z` over `S` given by the base change of `P`, that is
`x = P ∘ (Z ⟶ S)`. Then `Z ⟶ S` factors through the locus where `P` has naive exact order `N`
exactly when `x` has naive exact order `N`. -/
theorem exists_lift_naiveExactOrderPreimageι_iff {x : Z ⟶ Over.mk E.structureMap}
    (hx : x.left = Z.hom ≫ P.left) :
    (∃ l : Z.left ⟶ naiveExactOrderPreimage N P, l ≫ naiveExactOrderPreimageι N P = Z.hom) ↔
      E.IsOfNaiveExactOrder x N := by
  have hP := isPullback_naiveExactOrderPreimage N P
  refine ⟨fun ⟨l, hl⟩ ↦ ?_, fun h ↦ ?_⟩
  · -- `x` factors through the scheme of points of naive exact order `N`
    let u : Z ⟶ naiveLocusOver (E.torsionPointHom N) :=
      Over.homMk (l ≫ naiveExactOrderPreimagePoint N P) (by
        have h := hP.w =≫ E.structureMap
        simp only [Category.assoc, left_comp_structureMap, Category.comp_id] at h
        simpa [← torsionι_left_structureMap, ← h] using hl)
    have hux : u ≫ naiveLocusι (E.torsionPointHom N) ≫ E.torsionι N = x := by
      ext1
      simp [u, hx, ← hl, hP.w]
    rw [← hux, ← coe_naiveExactOrderRepresentableBy_homEquiv u]
    exact ((E.naiveExactOrderRepresentableBy N).homEquiv u).2
  · -- conversely, the point of the scheme of points of naive exact order `N` given by `x` lifts
    -- `Z ⟶ S`
    let u := (E.naiveExactOrderRepresentableBy N).homEquiv.symm ⟨x, h⟩
    have hux : u ≫ naiveLocusι (E.torsionPointHom N) ≫ E.torsionι N = x := by
      rw [← coe_naiveExactOrderRepresentableBy_homEquiv u, Equiv.apply_symm_apply]
    refine ⟨hP.lift Z.hom u.left ?_, hP.lift_fst _ _ _⟩
    rw [← hx, ← hux]
    simp

/-- **The locus where `P` has naive exact order `N` is closed where `N` is invertible.** If `N` is
invertible in every residue field of `S`, the naive locus of the universal point of `E[N]` is closed
in `E[N]` (`EllipticCurveGeom.isClopen_naiveLocus`), so its preimage under `P` is a closed subscheme
of `S`. -/
theorem isClosedImmersion_naiveExactOrderPreimageι (hN : ∀ s : S, (N : S.residueField s) ≠ 0) :
    IsClosedImmersion (naiveExactOrderPreimageι N P) := by
  have := isClosedImmersion_naiveLocusι_left (E.torsionPointHom N) hN fun a ↦ by
    have ha : a ^ N = 1 := Multiplicative.toAdd.injective (by simp)
    rw [← map_pow, ha, map_one]
  rw [naiveLocusι_left] at this
  exact MorphismProperty.of_isPullback (isPullback_naiveExactOrderPreimage N P).flip inferInstance

end Locus

end EllipticCurveGeom

end TauCeti.AlgebraicGeometry
