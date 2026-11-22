/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.RingTheory.Valuation.LocalSubring
public import Mathlib.SetTheory.Cardinal.Basic
public import TauCeti.RingTheory.IntegralClosure.AbsolutelyIntegrallyClosed

import Mathlib.Algebra.GCDMonoid.IntegrallyClosed
import TauCeti.FieldTheory.IsAlgClosed.Cardinal

/-!
# Absolutely integrally closed valuation rings

Absolutely integrally closed valuation domains are the test objects for descent in the v- and
arc-topologies. This file shows that there are enough of them, and that they can be chosen small:

* every local domain, in particular every valuation domain, has an injective local homomorphism
  `V →+* W` to an absolutely integrally closed valuation domain `W` in the same universe;
* every subset `s` of an absolutely integrally closed valuation domain `V` lies in an absolutely
  integrally closed valuation subring `V₀ ⊆ V` of cardinality at most `max #s ℵ₀` whose inclusion
  into `V` is a local homomorphism; so every ring homomorphism `A →+* V` factors through such a
  `V₀` with `#V₀ ≤ max #A ℵ₀`.

The second result bounds the size of the test valuation rings, which keeps quantification over
them within a fixed universe.

The subring `V₀` is the trace `V ∩ L` of `V` on an algebraically closed subfield `L` of the
fraction field of `V`. For any subfield `L` of a field containing `V`, this trace is a valuation
ring whose inclusion into `V` is local, and it is absolutely integrally closed when `L` is
algebraically closed and contained in the fraction field; the last fact only uses that `V` is
integrally closed.

## Main results

* `ValuationSubring.isAbsolutelyIntegrallyClosed`: a valuation subring of an algebraically closed
  field is absolutely integrally closed.
* `Subfield.valuationRing_comap`, `Subfield.isLocalHom_subtype_comap`,
  `Subfield.isAbsolutelyIntegrallyClosed_comap`: the trace of a ring on a subfield of a field
  containing it.
* `TauCeti.exists_injective_isLocalHom_isAbsolutelyIntegrallyClosed`: every local domain has an
  injective local homomorphism to an absolutely integrally closed valuation domain.
* `TauCeti.exists_subset_valuationRing_subring_mk_le`: a small absolutely integrally closed
  valuation subring containing a given subset.
* `RingHom.exists_range_le_valuationRing_subring_lift_mk_le`: the factorization of a ring
  homomorphism through a small absolutely integrally closed valuation subring.

## References

* B. Bhatt, A. Mathew, *The arc-topology*, Forum Math. Pi 9 (2021), Lemmas 3.28 and 3.29.
-/

public section

open Cardinal Polynomial

universe u v

namespace ValuationSubring

/-- A valuation subring of an algebraically closed field is absolutely integrally closed: it is
integrally closed, and its fraction field is the ambient field. -/
instance isAbsolutelyIntegrallyClosed {K : Type*} [Field K] [IsAlgClosed K]
    (A : ValuationSubring K) : TauCeti.IsAbsolutelyIntegrallyClosed A :=
  .of_isIntegrallyClosed_of_isAlgClosed K

end ValuationSubring

namespace Subfield

variable {V K : Type*} [CommRing V] [Field K] [Algebra V K] (L : Subfield K)

/-- If `a * c = b` in `V` with `a ≠ 0`, and `a` and `b` lie in the trace of `V` on a subfield `L` of
a field containing `V`, then so does `c`. -/
private theorem mem_comap_of_mul_eq [FaithfulSMul V K] {a b c : V}
    (ha : a ∈ L.toSubring.comap (algebraMap V K)) (hb : b ∈ L.toSubring.comap (algebraMap V K))
    (ha0 : a ≠ 0) (h : a * c = b) : c ∈ L.toSubring.comap (algebraMap V K) := by
  have ha0' : algebraMap V K a ≠ 0 :=
    (map_ne_zero_iff _ (FaithfulSMul.algebraMap_injective V K)).mpr ha0
  have hc : algebraMap V K c = algebraMap V K b / algebraMap V K a := by
    rw [eq_div_iff ha0', ← h, map_mul, mul_comm]
  simpa [Subring.mem_comap, hc] using L.div_mem hb ha

/-- The trace `V ∩ L` of a valuation ring `V` on a subfield `L` of a field containing `V` is a
valuation ring. -/
instance valuationRing_comap [IsDomain V] [ValuationRing V] [FaithfulSMul V K] :
    ValuationRing (L.toSubring.comap (algebraMap V K)) where
  cond' a b := by
    obtain ⟨c, hc | hc⟩ := ValuationRing.cond (a : V) b
    · by_cases ha : (a : V) = 0
      · exact ⟨0, .inl (Subtype.ext (by simp [← hc, ha]))⟩
      · exact ⟨⟨c, mem_comap_of_mul_eq L a.property b.property ha hc⟩, .inl (Subtype.ext hc)⟩
    · by_cases hb : (b : V) = 0
      · exact ⟨0, .inr (Subtype.ext (by simp [← hc, hb]))⟩
      · exact ⟨⟨c, mem_comap_of_mul_eq L b.property a.property hb hc⟩, .inr (Subtype.ext hc)⟩

/-- The inclusion into `V` of the trace `V ∩ L` of `V` on a subfield `L` of a field `K` is a local
homomorphism: an element of `V ∩ L` invertible in `V` has its inverse in `L`. -/
theorem isLocalHom_subtype_comap : IsLocalHom (L.toSubring.comap (algebraMap V K)).subtype where
  map_nonunit x hx := by
    obtain ⟨y, hy⟩ := isUnit_iff_exists_inv.mp hx
    have hy' : algebraMap V K y = (algebraMap V K x)⁻¹ :=
      eq_inv_of_mul_eq_one_right (by simpa using congrArg (algebraMap V K) hy)
    have hyL : y ∈ L.toSubring.comap (algebraMap V K) := by
      simpa [Subring.mem_comap, hy'] using L.inv_mem x.property
    exact isUnit_iff_exists_inv.mpr ⟨⟨y, hyL⟩, Subtype.ext hy⟩

/-- The trace `V ∩ L` of an integrally closed domain `V`, for instance a valuation ring, on an
algebraically closed subfield `L` of its fraction field is absolutely integrally closed. -/
instance isAbsolutelyIntegrallyClosed_comap [IsIntegrallyClosed V] [IsFractionRing V K]
    [IsAlgClosed L] :
    TauCeti.IsAbsolutelyIntegrallyClosed (L.toSubring.comap (algebraMap V K)) where
  exists_root p hp hdeg := by
    -- A root of `p` in `L` is integral over `V`, hence lies in `V`, hence in `V ∩ L`.
    set φ : L.toSubring.comap (algebraMap V K) →+* K :=
      (algebraMap V K).comp (L.toSubring.comap (algebraMap V K)).subtype
    let g : L.toSubring.comap (algebraMap V K) →+* L :=
      φ.codRestrict L.toSubring fun x ↦ x.property
    obtain ⟨y, hy⟩ := IsAlgClosed.exists_root (p.map g)
      (natDegree_pos_iff_degree_pos.mp ((hp.natDegree_map g).symm ▸ hdeg)).ne'
    have hy' : p.eval₂ φ (y : K) = 0 := by
      rw [IsRoot, eval_map] at hy
      have := congrArg L.subtype hy
      rwa [hom_eval₂, map_zero] at this
    obtain ⟨v, hv⟩ := IsIntegrallyClosed.isIntegral_iff.mp
      (⟨p.map (L.toSubring.comap (algebraMap V K)).subtype, hp.map _, by
        rwa [eval₂_map]⟩ : IsIntegral V (y : K))
    have hφinj : Function.Injective φ :=
      (IsFractionRing.injective V K).comp Subtype.val_injective
    refine ⟨⟨v, by simp [Subring.mem_comap, hv]⟩, hφinj ?_⟩
    rw [map_zero, ← eval₂_at_apply]
    rwa [← hv] at hy'

end Subfield

namespace TauCeti

/-- Every local domain `V`, in particular every valuation domain, has an injective local
homomorphism `V →+* W` to an absolutely integrally closed valuation domain `W` in the same
universe. One can take for `W` a valuation subring of an algebraic closure of the fraction field of
`V` dominating `V`. -/
theorem exists_injective_isLocalHom_isAbsolutelyIntegrallyClosed (V : Type u) [CommRing V]
    [IsDomain V] [IsLocalRing V] :
    ∃ (W : Type u) (_ : CommRing W) (_ : IsDomain W) (_ : ValuationRing W)
      (_ : IsAbsolutelyIntegrallyClosed W) (e : V →+* W), Function.Injective e ∧ IsLocalHom e := by
  let f := algebraMap V (AlgebraicClosure (FractionRing V))
  have hf : Function.Injective f :=
    (algebraMap (FractionRing V) _).injective.comp (IsFractionRing.injective V _)
  obtain ⟨W, hW, hloc⟩ := IsLocalRing.exists_factor_valuationRing f
  exact ⟨W, inferInstance, inferInstance, inferInstance, inferInstance,
    f.codRestrict W.toSubring hW, fun x y h ↦ hf congr(($h).val), hloc⟩

/-- Every subset `s` of an absolutely integrally closed valuation domain `V` lies in an absolutely
integrally closed valuation subring `V₀` of `V` with `#V₀ ≤ max #s ℵ₀`, whose inclusion into `V` is
a local homomorphism. The subring is the trace of `V` on an algebraically closed subfield of the
fraction field of `V` containing `s`. -/
theorem exists_subset_valuationRing_subring_mk_le (V : Type*) [CommRing V] [IsDomain V]
    [ValuationRing V] [IsAbsolutelyIntegrallyClosed V] (s : Set V) :
    ∃ V₀ : Subring V, s ⊆ V₀ ∧ ValuationRing V₀ ∧ IsAbsolutelyIntegrallyClosed V₀ ∧
      IsLocalHom V₀.subtype ∧ #V₀ ≤ max #s ℵ₀ := by
  let K := FractionRing V
  have := IsAbsolutelyIntegrallyClosed.isAlgClosed (A := V) K
  obtain ⟨L, hsL, hL, hcard⟩ := exists_isAlgClosed_subfield_mk_le K (algebraMap V K '' s)
  refine ⟨L.toSubring.comap (algebraMap V K), fun x hx ↦ hsL ⟨x, hx, rfl⟩, inferInstance,
    inferInstance, L.isLocalHom_subtype_comap, ?_⟩
  -- `V ∩ L` embeds into `L`, whose cardinality is bounded by that of `s`.
  calc #(L.toSubring.comap (algebraMap V K)) ≤ #L :=
        mk_le_of_injective (f := fun x ↦ (⟨algebraMap V K x, x.property⟩ : L)) fun x y h ↦
          Subtype.ext (IsFractionRing.injective V K congr(($h).val))
    _ ≤ max #(algebraMap V K '' s) ℵ₀ := hcard
    _ ≤ max #s ℵ₀ := max_le_max_right ℵ₀ mk_image_le

end TauCeti

namespace RingHom

open TauCeti

/-- Every ring homomorphism `f : A →+* V` to an absolutely integrally closed valuation domain
factors through an absolutely integrally closed valuation subring `V₀` of `V` with
`#V₀ ≤ max #A ℵ₀`, whose inclusion into `V` is a local homomorphism. -/
theorem exists_range_le_valuationRing_subring_lift_mk_le {A : Type u} {V : Type v} [CommRing A]
    [CommRing V] [IsDomain V] [ValuationRing V] [IsAbsolutelyIntegrallyClosed V] (f : A →+* V) :
    ∃ V₀ : Subring V, f.range ≤ V₀ ∧ ValuationRing V₀ ∧ IsAbsolutelyIntegrallyClosed V₀ ∧
      IsLocalHom V₀.subtype ∧ lift.{u} #V₀ ≤ max (lift.{v} #A) ℵ₀ := by
  obtain ⟨V₀, hs, h₁, h₂, h₃, hcard⟩ := exists_subset_valuationRing_subring_mk_le V (Set.range f)
  refine ⟨V₀, fun x hx ↦ hs (f.mem_range.mp hx), h₁, h₂, h₃, ?_⟩
  calc lift.{u} #V₀ ≤ lift.{u} (max #(Set.range f) ℵ₀) := lift_le.mpr hcard
    _ ≤ max (lift.{v} #A) ℵ₀ := by
        rw [lift_max, lift_aleph0]
        exact max_le_max_right ℵ₀ mk_range_le_lift

end RingHom
