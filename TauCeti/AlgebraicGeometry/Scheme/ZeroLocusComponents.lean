/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.FunctionField
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Stalk
public import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
public import TauCeti.AlgebraicGeometry.Scheme.CodimensionOnePoint
public import TauCeti.AlgebraicGeometry.Scheme.GenericPoint

/-!
# Irreducible components of the zero locus of a global function

Let `X` be an integral locally Noetherian scheme and `a` a nonzero global function on `X`. This
file identifies the irreducible components of the closed subset `V(a)` where `a` vanishes: their
generic points, which are the points of `V(a)` maximal for the specialization order among the
points of `V(a)`, are exactly the codimension-one points of `X` lying in `V(a)`. This is Krull's
principal ideal theorem read on the scheme: at a generic point `x` of a component of `V(a)`, the
maximal ideal of the local ring `𝒪_{X, x}` is a minimal prime over the germ of `a`, so it has
height at most one, and it has height at least one because `a` is a unit at the generic point of
`X`, which therefore does not lie in `V(a)`.

The points of the spectrum of the local ring `𝒪_{X, x}` are the generizations of `x`, and the
germ of `a` lies in the prime corresponding to a generization `y` exactly when `a` vanishes at
`y`; this is `TauCeti.AlgebraicGeometry.Scheme.fromSpecStalk_mem_basicOpen_iff`, which is what
turns maximality of `x` in `V(a)` into minimality of the maximal ideal over the germ of `a`.

Conversely a codimension-one point of `V(a)` is maximal there, since its only proper generization
is the generic point of `X`. Every point of `V(a)` specializes from such a maximal point, because
coheights in a locally Noetherian scheme are finite and a generization inside `V(a)` of least
coheight is maximal.

The application is to the special fibre of a scheme over a discrete valuation ring: the special
fibre is the zero locus of a uniformizer, so its irreducible components are the codimension-one
points of the total space at which the uniformizer vanishes.

## Main results

* `TauCeti.AlgebraicGeometry.Scheme.fromSpecStalk_mem_basicOpen_iff`: a point of the spectrum of
  a local ring of `X` lies in the basic open of a section exactly when the germ of that section
  is outside the corresponding prime ideal;
* `TauCeti.AlgebraicGeometry.Scheme.germ_mem_maximalIdeal_of_mem_zeroLocus` and
  `TauCeti.AlgebraicGeometry.Scheme.maximalIdeal_mem_minimalPrimes_of_maximal`: at a point of the
  zero locus of a global function the germ of the function lies in the maximal ideal of the local
  ring, and at a maximal point of the zero locus the maximal ideal is a minimal prime over the germ;
* `TauCeti.AlgebraicGeometry.Scheme.coheight_lt_top`: coheights are finite on a locally
  Noetherian scheme;
* `TauCeti.AlgebraicGeometry.Scheme.genericPoint_notMem_zeroLocus`: a nonzero global function on
  an integral scheme does not vanish at the generic point;
* `TauCeti.AlgebraicGeometry.Scheme.coheight_eq_one_of_maximal_mem_zeroLocus`: a maximal point
  of the zero locus of a nonzero global function has coheight one;
* `TauCeti.AlgebraicGeometry.Scheme.maximal_mem_zeroLocus_iff`: the maximal points of that zero
  locus are exactly its codimension-one points;
* `TauCeti.AlgebraicGeometry.Scheme.exists_maximal_mem_zeroLocus_specializes`: every point of
  the zero locus specializes from a maximal point of it.

## References

* [The Stacks Project, Lemma 10.60.11](https://stacks.math.columbia.edu/tag/00KV), Krull's
  principal ideal theorem.
* R. Hartshorne, *Algebraic Geometry*, Proposition II.6.1 and the discussion preceding it.
-/

public section

open AlgebraicGeometry CategoryTheory Order TopologicalSpace

namespace TauCeti

namespace AlgebraicGeometry

namespace Scheme

universe u

variable {X : Scheme.{u}}

/-- A point of the spectrum of the local ring of `X` at `x`, that is, a generization of `x`,
lies in the basic open of a section `f` exactly when the germ of `f` at `x` lies outside the
corresponding prime ideal. -/
theorem fromSpecStalk_mem_basicOpen_iff {U : X.Opens} {x : X} (hxU : x ∈ U) (f : Γ(X, U))
    (q : Spec (X.presheaf.stalk x)) :
    X.fromSpecStalk x q ∈ X.basicOpen f ↔ X.presheaf.germ U x hxU f ∉ q.asIdeal := by
  have hq : X.fromSpecStalk x q ∈ U := by
    have hqx : X.fromSpecStalk x q ⤳ x :=
      ((IsLocalRing.specializes_closedPoint q).map (X.fromSpecStalk x).continuous).trans
        (specializes_of_eq Scheme.fromSpecStalk_closedPoint)
    exact hqx.mem_open U.isOpen hxU
  rw [← Scheme.Hom.mem_preimage, Scheme.preimage_basicOpen, Scheme.fromSpecStalk_app hxU,
    CommRingCat.comp_apply, CommRingCat.comp_apply, Scheme.basicOpen_res, Opens.mem_inf,
    Scheme.Hom.mem_preimage, AlgebraicGeometry.basicOpen_eq_of_affine, and_iff_right hq]
  exact PrimeSpectrum.mem_basicOpen _ _

/-- The germ of a global function at a point of its zero locus lies in the maximal ideal of the
local ring there. -/
theorem germ_mem_maximalIdeal_of_mem_zeroLocus {a : Γ(X, ⊤)} {x : X}
    (hx : x ∈ X.zeroLocus {a}) :
    X.presheaf.germ ⊤ x trivial a ∈ IsLocalRing.maximalIdeal (X.presheaf.stalk x) := by
  rw [Scheme.zeroLocus_singleton, Set.mem_compl_iff, SetLike.mem_coe,
    Scheme.mem_basicOpen_top] at hx
  exact (IsLocalRing.mem_maximalIdeal _).mpr hx

/-- At a maximal point `x` of the zero locus of a global function `a`, the maximal ideal of the
local ring is a minimal prime over the germ of `a`: a smaller prime containing the germ would be
a generization of `x` inside the zero locus. -/
theorem maximalIdeal_mem_minimalPrimes_of_maximal {a : Γ(X, ⊤)} {x : X}
    (hx : Maximal (· ∈ X.zeroLocus {a}) x) :
    IsLocalRing.maximalIdeal (X.presheaf.stalk x) ∈
      (Ideal.span {X.presheaf.germ ⊤ x trivial a}).minimalPrimes := by
  refine ⟨⟨inferInstance, (Ideal.span_singleton_le_iff_mem _).mpr
    (germ_mem_maximalIdeal_of_mem_zeroLocus hx.prop)⟩, ?_⟩
  rintro q ⟨hq, hαq⟩ -
  -- The prime `q` is a point `p` of `Spec 𝒪_{X, x}`, whose image `y` is a generization of `x`.
  set p : Spec (X.presheaf.stalk x) := ⟨q, hq⟩ with hp_def
  have hyx : X.fromSpecStalk x p ⤳ x :=
    ((IsLocalRing.specializes_closedPoint p).map (X.fromSpecStalk x).continuous).trans
      (specializes_of_eq Scheme.fromSpecStalk_closedPoint)
  -- The germ of `a` lies in `q`, so `a` vanishes at `y`.
  have hyZ : X.fromSpecStalk x p ∈ X.zeroLocus {a} := by
    rw [Scheme.zeroLocus_singleton, Set.mem_compl_iff, SetLike.mem_coe,
      fromSpecStalk_mem_basicOpen_iff (U := ⊤) trivial, not_not]
    exact (Ideal.span_singleton_le_iff_mem _).mp hαq
  -- Maximality of `x` in the zero locus forces `y = x`, so `p` is the closed point.
  have hxy : x ⤳ X.fromSpecStalk x p := hx.2 hyZ hyx
  have hyx_eq : X.fromSpecStalk x p = x :=
    Inseparable.eq (inseparable_iff_specializes_and.mpr ⟨hyx, hxy⟩)
  have hp_eq : p = IsLocalRing.closedPoint _ :=
    (X.fromSpecStalk x).isEmbedding.injective (hyx_eq.trans Scheme.fromSpecStalk_closedPoint.symm)
  exact (congrArg PrimeSpectrum.asIdeal hp_eq).ge

section Integral

variable [IsIntegral X]

/-- A nonzero global function on an integral scheme is a unit at the generic point. -/
theorem genericPoint_mem_basicOpen {a : Γ(X, ⊤)} (ha : a ≠ 0) :
    genericPoint X ∈ X.basicOpen a := by
  rw [Scheme.mem_basicOpen_top]
  -- The stalk at the generic point is the function field, a field, so a nonzero germ is a unit.
  have hne : X.presheaf.germ ⊤ (genericPoint X) trivial a ≠ 0 := fun h ↦
    ha (germ_injective_of_isIntegral X (U := ⊤) (genericPoint X) trivial
      (h.trans (map_zero _).symm))
  exact isUnit_iff_ne_zero.mpr hne

/-- A nonzero global function on an integral scheme does not vanish at the generic point. -/
theorem genericPoint_notMem_zeroLocus {a : Γ(X, ⊤)} (ha : a ≠ 0) :
    genericPoint X ∉ X.zeroLocus {a} := by
  rw [Scheme.zeroLocus_singleton, Set.mem_compl_iff, SetLike.mem_coe, not_not]
  exact genericPoint_mem_basicOpen ha

end Integral

variable [IsLocallyNoetherian X]

/-- On a locally Noetherian scheme every point has finite coheight: the coheight is the Krull
dimension of the Noetherian local ring at the point. -/
theorem coheight_lt_top (x : X) : coheight x < ⊤ := by
  have h := ringKrullDim_lt_top (R := X.presheaf.stalk x)
  rwa [ringKrullDim_stalk_eq_coheight, ← WithBot.coe_top, WithBot.coe_lt_coe] at h

/-- Every point of the zero locus of a global function on a locally Noetherian scheme lies on an
irreducible component of that zero locus: it specializes from a maximal point of the zero locus. -/
theorem exists_maximal_mem_zeroLocus_specializes {a : Γ(X, ⊤)} {x : X}
    (hx : x ∈ X.zeroLocus {a}) :
    ∃ y, Maximal (· ∈ X.zeroLocus {a}) y ∧ y ⤳ x := by
  -- Among the generizations of `x` inside the zero locus, one of least coheight is maximal.
  set S : Set ℕ∞ := coheight '' {y : X | y ∈ X.zeroLocus {a} ∧ y ⤳ x} with hS
  have hSne : S.Nonempty := ⟨coheight x, x, ⟨hx, specializes_refl x⟩, rfl⟩
  obtain ⟨_, ⟨y, ⟨hyZ, hyx⟩, rfl⟩, hy⟩ := (wellFounded_lt (α := ℕ∞)).has_min S hSne
  refine ⟨y, ⟨hyZ, fun z hzZ (hzy : z ⤳ y) ↦ ?_⟩, hyx⟩
  by_contra hyz
  have hlt : y < z := ⟨hzy, hyz⟩
  have h := coheight_strictAnti hlt (coheight_lt_top z)
  exact hy (coheight z) ⟨z, ⟨hzZ, hzy.trans hyx⟩, rfl⟩ h

variable [IsIntegral X]

/-- **Krull's principal ideal theorem on a scheme.** A maximal point of the zero locus of a
nonzero global function on an integral locally Noetherian scheme, that is, the generic point of
an irreducible component of that zero locus, has coheight one. -/
theorem coheight_eq_one_of_maximal_mem_zeroLocus {a : Γ(X, ⊤)} (ha : a ≠ 0) {x : X}
    (hx : Maximal (· ∈ X.zeroLocus {a}) x) : coheight x = 1 := by
  -- Krull's principal ideal theorem bounds the dimension of the local ring by one.
  have h₁ : (IsLocalRing.maximalIdeal (X.presheaf.stalk x)).height ≤ 1 :=
    Ideal.height_le_one_of_isPrincipal_of_mem_minimalPrimes _ _
      (maximalIdeal_mem_minimalPrimes_of_maximal hx)
  have h₁' : ((IsLocalRing.maximalIdeal (X.presheaf.stalk x)).height : WithBot ℕ∞) ≤ 1 := by
    exact_mod_cast h₁
  rw [IsLocalRing.maximalIdeal_height_eq_ringKrullDim, ringKrullDim_stalk_eq_coheight] at h₁'
  have hle : coheight x ≤ 1 := by exact_mod_cast h₁'
  -- The generic point of `X` is not in the zero locus, so `x` is not the generic point.
  have hmax : ¬ IsMax x := fun h ↦
    genericPoint_notMem_zeroLocus ha (eq_genericPoint_of_isMax h ▸ hx.prop)
  exact le_antisymm hle (Order.one_le_iff_pos.mpr (coheight_pos.mpr hmax))

/-- The maximal points of the zero locus of a nonzero global function on an integral locally
Noetherian scheme are exactly the codimension-one points of the scheme lying in it. -/
theorem maximal_mem_zeroLocus_iff {a : Γ(X, ⊤)} (ha : a ≠ 0) {x : X} :
    Maximal (· ∈ X.zeroLocus {a}) x ↔ x ∈ X.zeroLocus {a} ∧ coheight x = 1 := by
  refine ⟨fun hx ↦ ⟨hx.prop, coheight_eq_one_of_maximal_mem_zeroLocus ha hx⟩, fun ⟨hxZ, hx⟩ ↦
    ⟨hxZ, fun y hyZ hyx ↦ ?_⟩⟩
  -- A strict generization of a codimension-one point has coheight zero, so it is the generic
  -- point, which is outside the zero locus.
  by_contra hxy
  have hlt : x < y := ⟨hyx, hxy⟩
  have h := coheight_add_one_le hlt
  rw [hx] at h
  have hy : coheight y = 0 :=
    Order.lt_one_iff.mp ((ENat.add_one_le_iff (coheight_lt_top y).ne).mp h)
  exact genericPoint_notMem_zeroLocus ha
    (eq_genericPoint_of_isMax (coheight_eq_zero.mp hy) ▸ hyZ)

end Scheme

end AlgebraicGeometry

end TauCeti
