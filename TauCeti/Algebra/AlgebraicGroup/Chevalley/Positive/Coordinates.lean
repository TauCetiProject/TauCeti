/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Chevalley.OrderedProduct
public import TauCeti.Algebra.AlgebraicGroup.Chevalley.Positive.Collection
import Mathlib.SetTheory.Cardinal.Finite

/-!
# Positive-root coordinates on the positive subgroup of a Chevalley datum

For **any** Chevalley datum `D` of **any** valid Dynkin type and **any** commutative ring `A`,
every duplicate-free enumeration `l` of the positive roots determines a canonical coordinate
bijection between `(posRoots (t.rationalRootSystem ht) (t.rationalBase ht) → A)` and
`D.positivePoints A` (`ChevalleyDatum.positivePointsEquiv`), sending each coordinate family to its
ordered positive-root product (`ChevalleyDatum.positivePointsProd`).

In particular, every element of `D.positivePoints A` admits a **unique** ordered product
representation along `l`, the positive point subgroup over a finite commutative ring `A` is finite,
and `Nat.card (D.positivePoints A) = Nat.card A ^ (posRoots ...).ncard` unconditionally. For a
field `k`, this realizes the unipotent subgroup `U(k) = D.positivePoints k` with its full root-data
coordinate parameterization across all isogeny types and characteristics.

## Main definitions

* `TauCeti.DynkinType.ChevalleyDatum.positivePointsProd`: the ordered positive-root product map
  `({γ // γ ∈ l} → A) → D.positivePoints A` along any list `l` of positive roots.
* `TauCeti.DynkinType.ChevalleyDatum.positivePointsEquiv`: the coordinate bijection
  `(posRoots (t.rationalRootSystem ht) (t.rationalBase ht) → A) ≃ D.positivePoints A` determined by
  a duplicate-free enumeration `l` of the positive roots.

## Main results

* `TauCeti.DynkinType.ChevalleyDatum.positivePointsProd_injective` and
  `TauCeti.DynkinType.ChevalleyDatum.positivePointsProd_surjective`: ordered positive-root products
  along a duplicate-free positive-root list are injective, and surjective when the list covers all
  positive roots.
* `TauCeti.DynkinType.ChevalleyDatum.map_positivePointsEquiv` and
  `TauCeti.DynkinType.ChevalleyDatum.positivePointsEquiv_symm_map`: positive-root coordinates
  commute with scalar change along any ring homomorphism.
* `TauCeti.DynkinType.ChevalleyDatum.card_positivePoints`: the cardinality of `D.positivePoints A`
  is `Nat.card A ^ (posRoots (t.rationalRootSystem ht) (t.rationalBase ht)).ncard`.

## References

* R. Steinberg, *Lectures on Chevalley Groups*, Chapter 3, Lemma 17 and Corollary.
* R. W. Carter, *Simple Groups of Lie Type*, Theorem 5.3.3.
-/

public section

namespace TauCeti.DynkinType.ChevalleyDatum

universe v v'

variable {t : DynkinType} {ht : t.Valid} (D : ChevalleyDatum t ht)

/-- The ordered product of positive root elements of `D` with coordinates `u : {γ // γ ∈ l} → A`
along a list `l` of positive roots, valued in `D.positivePoints A`. -/
noncomputable def positivePointsProd {l : List (Fin t.numRoots)}
    (hpos : ∀ γ ∈ l, γ ∈ posRoots (t.rationalRootSystem ht) (t.rationalBase ht))
    (A : Type v) [CommRing A] (u : {γ // γ ∈ l} → A) : D.positivePoints A :=
  ⟨(l.attach.map fun γ => D.rootSubgroupPoints γ.1 A (Multiplicative.ofAdd (u γ))).prod,
    Subgroup.list_prod_mem _ fun x hx => by
      obtain ⟨γ, _, rfl⟩ := List.mem_map.mp hx
      exact D.rootSubgroupPoints_mem_positivePoints A (hpos γ.1 γ.2) _⟩

/-- Coercing `positivePointsProd` to `D.points A` gives the underlying attached list product. -/
@[simp]
theorem coe_positivePointsProd {l : List (Fin t.numRoots)}
    (hpos : ∀ γ ∈ l, γ ∈ posRoots (t.rationalRootSystem ht) (t.rationalBase ht))
    (A : Type v) [CommRing A] (u : {γ // γ ∈ l} → A) :
    (D.positivePointsProd hpos A u : D.points A) =
      (l.attach.map fun γ => D.rootSubgroupPoints γ.1 A (Multiplicative.ofAdd (u γ))).prod := by
  rfl

/-- Evaluating `positivePointsProd` on restricted full-root coordinates gives the unattached list
product. -/
theorem coe_positivePointsProd_comp {l : List (Fin t.numRoots)}
    (hpos : ∀ γ ∈ l, γ ∈ posRoots (t.rationalRootSystem ht) (t.rationalBase ht))
    (A : Type v) [CommRing A] (u : Fin t.numRoots → A) :
    (D.positivePointsProd hpos A (fun γ => u γ.1) : D.points A) =
      (l.map fun γ => D.rootSubgroupPoints γ A (Multiplicative.ofAdd (u γ))).prod := by
  rw [coe_positivePointsProd]
  conv_rhs => rw [← l.attach_map_subtype_val, List.map_map]
  rfl

/-- Zero coordinates evaluate to the identity element of `D.positivePoints A`. -/
@[simp]
theorem positivePointsProd_zero {l : List (Fin t.numRoots)}
    (hpos : ∀ γ ∈ l, γ ∈ posRoots (t.rationalRootSystem ht) (t.rationalBase ht))
    (A : Type v) [CommRing A] :
    D.positivePointsProd hpos A 0 = 1 := by
  ext1
  rw [coe_positivePointsProd, Subgroup.coe_one]
  exact List.prod_eq_one fun x hx => by
    obtain ⟨γ, _, rfl⟩ := List.mem_map.mp hx
    simp

/-- Ring homomorphisms commute with ordered positive-root products on datum points. -/
theorem map_positivePointsProd {l : List (Fin t.numRoots)}
    (hpos : ∀ γ ∈ l, γ ∈ posRoots (t.rationalRootSystem ht) (t.rationalBase ht))
    {A : Type v} {B : Type v'} [CommRing A] [CommRing B] (f : A →+* B)
    (u : {γ // γ ∈ l} → A) :
    ((D.pointsPresentation A).map (D.pointsPresentation B) f)
        (D.positivePointsProd hpos A u : D.points A) =
      (D.positivePointsProd hpos B (f ∘ u) : D.points B) := by
  simp only [coe_positivePointsProd, map_list_prod, List.map_map, Function.comp_def,
    D.map_rootSubgroupPoints, toAdd_ofAdd]

/-- Ordered positive-root products along any duplicate-free list of positive roots are injective
over every commutative ring. -/
theorem positivePointsProd_injective {l : List (Fin t.numRoots)} (hl : l.Nodup)
    (hpos : ∀ γ ∈ l, γ ∈ posRoots (t.rationalRootSystem ht) (t.rationalBase ht))
    (A : Type v) [CommRing A] :
    Function.Injective (D.positivePointsProd hpos A) := by
  classical
  intro u v huv
  let u' : Fin t.numRoots → A := fun γ => if h : γ ∈ l then u ⟨γ, h⟩ else 0
  let v' : Fin t.numRoots → A := fun γ => if h : γ ∈ l then v ⟨γ, h⟩ else 0
  have hu' : (fun γ : {γ // γ ∈ l} => u' γ.1) = u := funext fun ⟨γ, hγ⟩ => by simp [u', hγ]
  have hv' : (fun γ : {γ // γ ∈ l} => v' γ.1) = v := funext fun ⟨γ, hγ⟩ => by simp [v', hγ]
  have hprod : (l.map fun γ => D.rootSubgroupPoints γ A (Multiplicative.ofAdd (u' γ))).prod =
      (l.map fun γ => D.rootSubgroupPoints γ A (Multiplicative.ofAdd (v' γ))).prod := by
    rw [← D.coe_positivePointsProd_comp hpos A u', ← D.coe_positivePointsProd_comp hpos A v',
      hu', hv', huv]
  have heq := (D.list_prod_map_rootSubgroupPoints_inj A hl hpos).mp hprod
  funext ⟨γ, hγ⟩
  simpa only [u', v', hγ, ↓reduceDIte] using heq γ hγ

/-- When `l` enumerates all positive roots without repetition, ordered positive-root products cover
`D.positivePoints A`. -/
theorem positivePointsProd_surjective (l : List (Fin t.numRoots)) (hl : l.Nodup)
    (hcover : ∀ γ, γ ∈ l ↔ γ ∈ posRoots (t.rationalRootSystem ht) (t.rationalBase ht))
    (A : Type v) [CommRing A] :
    Function.Surjective (D.positivePointsProd (fun γ hγ => (hcover γ).mp hγ) A) := by
  rintro ⟨g, hg⟩
  obtain ⟨u, hu⟩ := (D.mem_positivePoints_iff_exists_prod l hl hcover A g).mp hg
  refine ⟨fun γ => u γ.1, Subtype.ext ?_⟩
  rw [D.coe_positivePointsProd_comp, hu]

/-- The coordinate bijection between functions on the positive roots with values in `A` and the
positive point subgroup `D.positivePoints A`, determined by a duplicate-free enumeration `l` of all
positive roots. -/
noncomputable def positivePointsEquiv (l : List (Fin t.numRoots)) (hl : l.Nodup)
    (hcover : ∀ γ, γ ∈ l ↔ γ ∈ posRoots (t.rationalRootSystem ht) (t.rationalBase ht))
    (A : Type v) [CommRing A] :
    (posRoots (t.rationalRootSystem ht) (t.rationalBase ht) → A) ≃ D.positivePoints A :=
  (Equiv.piCongrLeft' (fun _ => A) (Equiv.subtypeEquivRight hcover)).symm.trans
    (Equiv.ofBijective (D.positivePointsProd (fun γ hγ => (hcover γ).mp hγ) A)
      ⟨D.positivePointsProd_injective hl _ A, D.positivePointsProd_surjective l hl hcover A⟩)

/-- Evaluating `positivePointsEquiv` restricts the positive-root coordinates to `l` and takes their
ordered product. -/
theorem positivePointsEquiv_apply (l : List (Fin t.numRoots)) (hl : l.Nodup)
    (hcover : ∀ γ, γ ∈ l ↔ γ ∈ posRoots (t.rationalRootSystem ht) (t.rationalBase ht))
    (A : Type v) [CommRing A]
    (u : posRoots (t.rationalRootSystem ht) (t.rationalBase ht) → A) :
    D.positivePointsEquiv l hl hcover A u =
      D.positivePointsProd (fun γ hγ => (hcover γ).mp hγ) A
        (fun γ => u ⟨γ.1, (hcover γ.1).mp γ.2⟩) := by
  rfl

/-- Coercing `positivePointsEquiv` to `D.points A` gives the attached ordered root product. -/
@[simp]
theorem coe_positivePointsEquiv_apply (l : List (Fin t.numRoots)) (hl : l.Nodup)
    (hcover : ∀ γ, γ ∈ l ↔ γ ∈ posRoots (t.rationalRootSystem ht) (t.rationalBase ht))
    (A : Type v) [CommRing A]
    (u : posRoots (t.rationalRootSystem ht) (t.rationalBase ht) → A) :
    (D.positivePointsEquiv l hl hcover A u : D.points A) =
      (l.attach.map fun γ => D.rootSubgroupPoints γ.1 A
        (Multiplicative.ofAdd (u ⟨γ.1, (hcover γ.1).mp γ.2⟩))).prod := by
  rfl

/-- Evaluating `positivePointsEquiv` on restricted full-root coordinates gives the unattached
ordered root product. -/
theorem coe_positivePointsEquiv_comp (l : List (Fin t.numRoots)) (hl : l.Nodup)
    (hcover : ∀ γ, γ ∈ l ↔ γ ∈ posRoots (t.rationalRootSystem ht) (t.rationalBase ht))
    (A : Type v) [CommRing A] (u : Fin t.numRoots → A) :
    (D.positivePointsEquiv l hl hcover A (fun γ => u γ.1) : D.points A) =
      (l.map fun γ => D.rootSubgroupPoints γ A (Multiplicative.ofAdd (u γ))).prod :=
  D.coe_positivePointsProd_comp (fun γ hγ => (hcover γ).mp hγ) A u

/-- If an ordered positive-root product equals `g`, the inverse of `positivePointsEquiv` recovers
its positive-root coordinates. -/
theorem positivePointsEquiv_symm_of_prod_eq (l : List (Fin t.numRoots)) (hl : l.Nodup)
    (hcover : ∀ γ, γ ∈ l ↔ γ ∈ posRoots (t.rationalRootSystem ht) (t.rationalBase ht))
    (A : Type v) [CommRing A] {u : Fin t.numRoots → A} {g : D.positivePoints A}
    (hg : (l.map fun γ => D.rootSubgroupPoints γ A (Multiplicative.ofAdd (u γ))).prod = g) :
    (D.positivePointsEquiv l hl hcover A).symm g = fun γ => u γ.1 := by
  apply (D.positivePointsEquiv l hl hcover A).injective
  rw [Equiv.apply_symm_apply]
  exact Subtype.ext ((D.coe_positivePointsEquiv_comp l hl hcover A u).trans hg).symm

/-- Ring homomorphisms commute with `positivePointsEquiv` on datum points. -/
theorem map_positivePointsEquiv (l : List (Fin t.numRoots)) (hl : l.Nodup)
    (hcover : ∀ γ, γ ∈ l ↔ γ ∈ posRoots (t.rationalRootSystem ht) (t.rationalBase ht))
    {A : Type v} {B : Type v'} [CommRing A] [CommRing B] (f : A →+* B)
    (u : posRoots (t.rationalRootSystem ht) (t.rationalBase ht) → A) :
    ((D.pointsPresentation A).map (D.pointsPresentation B) f)
        (D.positivePointsEquiv l hl hcover A u : D.points A) =
      (D.positivePointsEquiv l hl hcover B (f ∘ u) : D.points B) :=
  D.map_positivePointsProd (fun γ hγ => (hcover γ).mp hγ) f
    (fun γ => u ⟨γ.1, (hcover γ.1).mp γ.2⟩)

/-- Extracting positive-root coordinates after scalar change applies the ring homomorphism
coordinatewise. In particular, coordinates are natural under reduction modulo an ideal. -/
@[simp]
theorem positivePointsEquiv_symm_map (l : List (Fin t.numRoots)) (hl : l.Nodup)
    (hcover : ∀ γ, γ ∈ l ↔ γ ∈ posRoots (t.rationalRootSystem ht) (t.rationalBase ht))
    {A : Type v} {B : Type v'} [CommRing A] [CommRing B] (f : A →+* B)
    (g : D.positivePoints A) :
    (D.positivePointsEquiv l hl hcover B).symm
        ⟨((D.pointsPresentation A).map (D.pointsPresentation B) f) (g : D.points A),
          D.map_positivePoints_le f (Subgroup.mem_map.mpr ⟨g, g.2, rfl⟩)⟩ =
      f ∘ (D.positivePointsEquiv l hl hcover A).symm g := by
  apply (D.positivePointsEquiv l hl hcover B).injective
  rw [Equiv.apply_symm_apply]
  apply Subtype.ext
  rw [← D.map_positivePointsEquiv l hl hcover f, Equiv.apply_symm_apply]

/-- Zero positive-root coordinates map to the identity element of `D.positivePoints A`. -/
@[simp]
theorem positivePointsEquiv_zero (l : List (Fin t.numRoots)) (hl : l.Nodup)
    (hcover : ∀ γ, γ ∈ l ↔ γ ∈ posRoots (t.rationalRootSystem ht) (t.rationalBase ht))
    (A : Type v) [CommRing A] :
    D.positivePointsEquiv l hl hcover A 0 = 1 := by
  rw [positivePointsEquiv_apply]
  exact D.positivePointsProd_zero (fun γ hγ => (hcover γ).mp hγ) A

/-- The identity element of `D.positivePoints A` has all positive-root coordinates equal to zero.
-/
@[simp]
theorem positivePointsEquiv_symm_one (l : List (Fin t.numRoots)) (hl : l.Nodup)
    (hcover : ∀ γ, γ ∈ l ↔ γ ∈ posRoots (t.rationalRootSystem ht) (t.rationalBase ht))
    (A : Type v) [CommRing A] :
    (D.positivePointsEquiv l hl hcover A).symm 1 = 0 :=
  (D.positivePointsEquiv l hl hcover A).symm_apply_eq.mpr
    (D.positivePointsEquiv_zero l hl hcover A).symm

/-- Over a finite commutative ring, the positive point subgroup of a Chevalley datum is finite. -/
instance finite_positivePoints (A : Type v) [CommRing A] [Finite A] :
    Finite (D.positivePoints A) := by
  classical
  let l := (List.finRange t.numRoots).filter
    (· ∈ posRootsFinset (t.rationalRootSystem ht) (t.rationalBase ht))
  have hl : l.Nodup := (List.nodup_finRange _).filter _
  have hcover : ∀ γ, γ ∈ l ↔ γ ∈ posRoots (t.rationalRootSystem ht) (t.rationalBase ht) := by
    intro γ
    simp [l]
  exact Finite.of_equiv _ (D.positivePointsEquiv l hl hcover A)

/-- The cardinality of the positive point subgroup of a Chevalley datum is `|A| ^ |Φ⁺|` over every
commutative ring `A`. -/
theorem card_positivePoints (A : Type v) [CommRing A] :
    Nat.card (D.positivePoints A) =
      Nat.card A ^ (posRoots (t.rationalRootSystem ht) (t.rationalBase ht)).ncard := by
  classical
  let l := (List.finRange t.numRoots).filter
    (· ∈ posRootsFinset (t.rationalRootSystem ht) (t.rationalBase ht))
  have hl : l.Nodup := (List.nodup_finRange _).filter _
  have hcover : ∀ γ, γ ∈ l ↔ γ ∈ posRoots (t.rationalRootSystem ht) (t.rationalBase ht) := by
    intro γ
    simp [l]
  rw [Nat.card_congr (D.positivePointsEquiv l hl hcover A).symm, Nat.card_fun, Nat.card_coe_set_eq]

end TauCeti.DynkinType.ChevalleyDatum
