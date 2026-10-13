/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.Scheme.Geom.ExactOrder.Subgroup
public import TauCeti.AlgebraicGeometry.EllipticCurve.Scheme.Geom.NaiveLevel
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
import TauCeti.AlgebraicGeometry.EllipticCurve.Scheme.Geom.Torsion.Etale.Locus
import TauCeti.AlgebraicGeometry.Morphisms.Etale
import TauCeti.AlgebraicGeometry.RationalPoint.Basic
import TauCeti.AlgebraicGeometry.ResidueField

/-!
# Points of exact order `N` where `N` is invertible

Let `E` be an elliptic curve over a scheme `S` and `P` an `S`-point of `E` of exact order `N` in
the sense of Drinfeld (`EllipticCurveGeom.IsOfExactOrder`): the divisor
`D = [P] + [2P] + ⋯ + [NP]` is a subgroup scheme of `E`. This file shows that if `N` is invertible
in every residue field of `S`, then `P` also has exact order `N` in the naive sense: none of
`P, 2P, …, (N - 1)P` meets the zero section, so `P` has order exactly `N` in every geometric
fibre. This is one half of the comparison between Drinfeld and naive `[Γ₁(N)]`-structures where
`N` is invertible. It fails in characteristic `p` dividing `N`, where the zero section can have
exact order `p` in the sense of Drinfeld.

The subgroup scheme `D` lies in `E[N]` (`EllipticCurveGeom.IsOfExactOrder.ker_torsionι_le`), which
is étale over `S` where `N` is invertible. Being flat and finitely presented, the closed subscheme
`D` is then itself étale over `S` (`EllipticCurveGeom.IsOfExactOrder.etale_multiplesDivisor`).
Over a separably closed field, `D` therefore has exactly `N` points, its rank. But every point of
`D` is one of `P, 2P, …, NP`, since the support of `D` is the union of their images; so these `N`
points are pairwise distinct, and `P` has order `N`. The general case reduces to this one by base
change to the algebraic closures of the residue fields of `S`.

## Main results

* `TauCeti.AlgebraicGeometry.EllipticCurveGeom.IsOfExactOrder.etale_multiplesDivisor`: where `N`
  is invertible, the divisor of a point of exact order `N` is finite étale over the base.
* `TauCeti.AlgebraicGeometry.EllipticCurveGeom.IsOfExactOrder.pow_left_apply_ne_zero`: on a fibre
  where `N` is invertible, none of `P, 2P, …, (N - 1)P` meets the zero section.
* `TauCeti.AlgebraicGeometry.EllipticCurveGeom.IsOfExactOrder.orderOf_eq`: over a field in which
  `N` is invertible, a point of exact order `N` has order `N`.
* `TauCeti.AlgebraicGeometry.EllipticCurveGeom.IsOfExactOrder.isFiberwiseInjective`: where `N` is
  invertible, the homomorphism `ℤ/Nℤ →* E(S)` of a point of exact order `N` is injective on every
  fibre, that is, a naive `[Γ₁(N)]`-structure.

## References

* N. M. Katz and B. Mazur, *Arithmetic Moduli of Elliptic Curves*, §1.4 (points of exact order
  `N`) and §3.7 (comparison with naive level structures where `N` is invertible).
-/

public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory AlgebraicGeometry MonObj

universe u

namespace TauCeti.AlgebraicGeometry.EllipticCurveGeom

section Base

variable {S : Scheme.{u}} {E : EllipticCurveGeom S} {P : 𝟙_ (Over S) ⟶ Over.mk E.structureMap}
  {N : ℕ}

/-- **The subgroup divisor of a point of exact order `N` is étale where `N` is invertible.** If `P`
has exact order `N` and `N` is invertible in every residue field of `S`, then the divisor
`[P] + ⋯ + [NP]` is étale over `S`. It is also finite over `S`, so it is finite étale. -/
theorem IsOfExactOrder.etale_multiplesDivisor (h : E.IsOfExactOrder P N)
    (hN : ∀ s : S, (N : S.residueField s) ≠ 0) :
    Etale ((E.multiplesDivisor P N).subschemeι ≫ E.structureMap) := by
  let I := E.multiplesDivisor P N
  -- the inclusion of `V(I)` into `E` factors through the closed immersion `E[N] ⟶ E`
  have hle : (E.torsionι N).left.ker ≤ I.subschemeι.ker := by
    rw [Scheme.IdealSheafData.ker_subschemeι]
    exact h.ker_torsionι_le
  let j := IsClosedImmersion.lift (E.torsionι N).left I.subschemeι hle
  have hj : j ≫ (E.torsionι N).left = I.subschemeι := IsClosedImmersion.lift_fac _ _ _
  have : Etale (E.torsion N).X.hom :=
    E.etale_torsion_hom_of_forall_intCast_ne_zero fun s ↦ by exact_mod_cast hN s
  have : FormallyUnramified (j ≫ (E.torsionι N).left) := by rw [hj]; infer_instance
  have : FormallyUnramified j := .of_comp j (E.torsionι N).left
  have : FormallyUnramified (I.subschemeι ≫ E.structureMap) := by
    rw [← hj, Category.assoc, torsionι_left_structureMap]
    exact MorphismProperty.comp_mem _ _ _ inferInstance inferInstance
  exact .of_formallyUnramified_of_flat _

end Base

section Field

variable {K : Type u} [Field K] {E : EllipticCurveGeom (Spec (.of K))}
  {P : 𝟙_ (Over (Spec (.of K))) ⟶ Over.mk E.structureMap} {N : ℕ}

/-- Over a field, every point of `E` on the divisor `[P] + ⋯ + [NP]` is one of `P, 2P, …, NP`. -/
private theorem exists_eq_pow_of_mem_support (x : 𝟙_ (Over (Spec (.of K))) ⟶ Over.mk E.structureMap)
    (p : Spec (.of K)) (hx : x.left p ∈ ((E.multiplesDivisor P N).support : Set E.carrier)) :
    ∃ a < N, x = P ^ (a + 1) := by
  rw [coe_support_multiplesDivisor] at hx
  simp only [Set.mem_iUnion, Set.mem_range] at hx
  obtain ⟨a, ha, q, hq⟩ := hx
  rw [Subsingleton.elim (α := Spec (.of K)) q p] at hq
  refine ⟨a, ha, Over.OverMorphism.ext ?_⟩
  simpa using (comp_eq_comp_iff_of_section (f := E.structureMap) (s₁ := x.left)
    (s₂ := (P ^ (a + 1)).left) (by simp) (by simp) (𝟙 _) p).mpr (by simpa using hq.symm)

/-- Over a separably closed field in which `N` is invertible, a point of exact order `N` has order
`N`: its divisor `[P] + ⋯ + [NP]` is étale of rank `N`, so it has `N` points, all among
`P, …, NP`. -/
private theorem IsOfExactOrder.pow_ne_one_of_isSepClosed [IsSepClosed K] (h : E.IsOfExactOrder P N)
    (hN : ∀ s : Spec (.of K), (N : (Spec (.of K)).residueField s) ≠ 0) {k : ℕ} (hk : 0 < k)
    (hkN : k < N) : P ^ k ≠ 1 := by
  intro hPk
  classical
  let I := E.multiplesDivisor P N
  let f := I.subschemeι ≫ E.structureMap
  obtain ⟨p⟩ : Nonempty (Spec (.of K)) := inferInstance
  have : Etale f := h.etale_multiplesDivisor hN
  have hcard := f.natCard_eq_finrank_of_etale p
  simp only [f, I, finrank_multiplesDivisor] at hcard
  -- the points of `V(I)` with values in `K` inject into the set of the points `P, …, NP`
  let g (y : 𝟙_ (Over (Spec (.of K))) ⟶ Over.mk f) :
      𝟙_ (Over (Spec (.of K))) ⟶ Over.mk E.structureMap :=
    y ≫ Over.homMk I.subschemeι
  have hmem (y) : g y ∈ (Finset.range N).image (fun a ↦ P ^ (a + 1)) := by
    obtain ⟨a, ha, hy⟩ := exists_eq_pow_of_mem_support (g y) p (by
      rw [← Scheme.IdealSheafData.range_subschemeι]
      exact ⟨y.left p, by simp [g, I]⟩)
    exact Finset.mem_image.mpr ⟨a, Finset.mem_range.mpr ha, hy.symm⟩
  have : Mono (Over.homMk I.subschemeι : Over.mk f ⟶ Over.mk E.structureMap) :=
    Over.mono_of_mono_left _
  have hle : N ≤ ((Finset.range N).image (fun a ↦ P ^ (a + 1))).card := by
    rw [← Nat.card_eq_finsetCard]
    exact hcard.symm.le.trans <| Nat.card_le_card_of_injective (fun y ↦ ⟨g y, hmem y⟩)
      fun y y' hyy' ↦ (cancel_mono _).mp (congrArg Subtype.val hyy')
  -- but `kP = 0 = NP` with `k ≠ N`, so that set has fewer than `N` elements
  have hne : ((Finset.range N).image (fun a ↦ P ^ (a + 1))).card ≠ (Finset.range N).card := by
    rw [Ne, Finset.card_image_iff]
    intro hinj
    have := hinj (Finset.mem_coe.mpr (Finset.mem_range.mpr (by omega : k - 1 < N)))
      (Finset.mem_coe.mpr (Finset.mem_range.mpr (by omega : N - 1 < N)))
      (by simp only [Nat.sub_add_cancel hk, Nat.sub_add_cancel (hk.trans hkN), hPk,
        h.pow_eq_one])
    omega
  have := Finset.card_image_le (s := Finset.range N) (f := fun a ↦ P ^ (a + 1))
  rw [Finset.card_range] at this hne
  omega

end Field

section Base

variable {S : Scheme.{u}} {E : EllipticCurveGeom S} {P : 𝟙_ (Over S) ⟶ Over.mk E.structureMap}
  {N : ℕ}

/-- **A point of exact order `N` has exact order `N` on every fibre where `N` is invertible.** If
`P` has exact order `N` in the sense of Drinfeld and `N` is invertible in the residue field at
`s`, then none of `P, 2P, …, (N - 1)P` meets the zero section at `s`. -/
theorem IsOfExactOrder.pow_left_apply_ne_zero (h : E.IsOfExactOrder P N) {s : S}
    (hN : (N : S.residueField s) ≠ 0) {k : ℕ} (hk : 0 < k) (hkN : k < N) :
    (P ^ k).left s ≠ E.zero s := by
  -- the base change `E'` of `E` to an algebraic closure `L` of the residue field at `s`
  let L := AlgebraicClosure (S.residueField s)
  let t : Spec (.of L) ⟶ S :=
    Spec.map (CommRingCat.ofHom (algebraMap (S.residueField s) L)) ≫ S.fromSpecResidueField s
  let E' := E.baseChange t
  have hg := E.isPullback_baseChange t
  have h0 : E'.zero ≫ (E.baseChangeIso t).hom ≫ pullback.fst _ _ = t ≫ E.zero := by simp [E']
  have htp (p : Spec (.of L)) : t p = s := Scheme.fromSpecResidueField_apply s _
  have h' := (h.pointsPullback hg h0).pow_ne_one_of_isSepClosed
    (fun p ↦ t.natCast_residueField_ne_zero (by rwa [htp p])) hk hkN
  obtain ⟨p⟩ : Nonempty (Spec (.of L)) := inferInstance
  intro hs
  apply h'
  rw [E'.eq_one_iff_left_apply_eq_zero _ p, ← map_pow,
    pointsPullback_left_apply_eq_zero_iff hg h0 _ p, htp p]
  exact hs

/-- **A point of exact order `N` gives a naive `[Γ₁(N)]`-structure where `N` is invertible.** If
`N` is invertible in every residue field of `S` and `φ : ℤ/Nℤ →* E(S)` sends `1` to a point of
exact order `N`, then `φ` is injective on every fibre of `E` over `S`. -/
theorem IsOfExactOrder.isFiberwiseInjective [NeZero N]
    {φ : Multiplicative (ZMod N) →* (𝟙_ (Over S) ⟶ Over.mk E.structureMap)}
    (h : E.IsOfExactOrder (φ (.ofAdd 1)) N) (hN : ∀ s : S, (N : S.residueField s) ≠ 0) :
    E.IsFiberwiseInjective φ :=
  isFiberwiseInjective_zmod_iff.mpr fun _ hk hkN s ↦ h.pow_left_apply_ne_zero (hN s) hk hkN

end Base

section Field

variable {K : Type u} [Field K] {E : EllipticCurveGeom (Spec (.of K))}
  {P : 𝟙_ (Over (Spec (.of K))) ⟶ Over.mk E.structureMap} {N : ℕ}

/-- **Over a field in which `N` is invertible, a point of exact order `N` has order `N`.** -/
theorem IsOfExactOrder.orderOf_eq (h : E.IsOfExactOrder P N) (hN : (N : K) ≠ 0) :
    orderOf P = N := by
  obtain ⟨p⟩ : Nonempty (Spec (.of K)) := inferInstance
  refine (orderOf_eq_iff (Nat.pos_of_ne_zero fun h0 ↦ hN (by simp [h0]))).mpr
    ⟨h.pow_eq_one, fun k hkN hk hPk ↦
      h.pow_left_apply_ne_zero (Spec.natCast_residueField_ne_zero hN p) hk hkN ?_⟩
  rw [← E.eq_one_iff_left_apply_eq_zero _ p]
  exact hPk

end Field

end TauCeti.AlgebraicGeometry.EllipticCurveGeom
