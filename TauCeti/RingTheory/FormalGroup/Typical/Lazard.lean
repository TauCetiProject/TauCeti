/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.FormalGroup.CoordinateChange.Lazard
public import TauCeti.RingTheory.FormalGroup.LazardRing.Localization
public import TauCeti.RingTheory.FormalGroup.Typical
public import TauCeti.RingTheory.GradedAlgebra.Localization
import TauCeti.RingTheory.GradedAlgebra.Basic

/-!
# Quillen's `p`-typicalization idempotent on the localized Lazard ring

Let `L = TauCeti.LazardRing`, let `p` be a prime, and let `S` be any localization of `L` at
`TauCeti.LazardRing.coprimeSubmonoid p` (`L_{(p)} = L ⊗ ℤ_{(p)}`). Every prime `q ≠ p` is a unit in
`S`, so the base change `F_S` of the universal formal group law admits Cartier–Quillen's canonical
`p`-typicalization `F_S.pTypicalFormalGroup p _`, classified by **Quillen's `p`-typicalization
idempotent** `TauCeti.LazardRing.typicalIdempotent p S : S →+* S`. Precomposing a classifying map
with `e_p` classifies the canonical `p`-typicalization, so `f ∘ e_p = f` iff the classified law is
`p`-typical and `e_p ∘ e_p = e_p`. Restricting `F_S` along `(typicalIdempotent p S).rangeRestrict`
yields the universal `p`-typical formal group law `TauCeti.LazardRing.typicalFormalGroup p S` over
`(typicalIdempotent p S).range` (`TauCeti.LazardRing.typicalLocalizedLift`). The canonical
coordinate `F_S.pTypicalCoordinate p _` gives
`TauCeti.LazardRing.typicalCoordinateHom : L[b₁, b₂, …] →+* S` intertwining `η_L` with
`algebraMap L S` and `η_R` with `e_p ∘ algebraMap L S`, and `e_p` preserves compatible
`ℕ`-gradings on `S`.

## Main definitions and results

* `TauCeti.LazardRing.typicalIdempotent`, `TauCeti.LazardRing.localizedLift_comp_typicalIdempotent`,
  `TauCeti.LazardRing.comp_typicalIdempotent_eq_self_iff`,
  `TauCeti.LazardRing.typicalIdempotent_comp_typicalIdempotent`: Quillen's idempotent `e_p`.
* `TauCeti.LazardRing.typicalFormalGroup`, `TauCeti.LazardRing.typicalLocalizedLift`: the universal
  `p`-typical formal group law over `(typicalIdempotent p S).range` and its universal property.
* `TauCeti.LazardRing.typicalCoordinateHom`, `TauCeti.LazardRing.typicalCoordinateHom_comp_C`,
  `TauCeti.LazardRing.map_typicalCoordinateHom_universalStrictCoordinate`,
  `TauCeti.LazardRing.typicalCoordinateHom_comp_rightUnit`: compatibility with `(L, L[b₁, b₂, …])`.
* `TauCeti.LazardRing.typicalIdempotent_mem_graded`, `TauCeti.LazardRing.gradedTypicalIdempotent`:
  grading preservation and graded endomorphism packaging.

## References

* P. Cartier, *Modules associés à un groupe formel commutatif. Courbes typiques*, C. R. Acad. Sci.
  Paris Sér. A-B 265 (1967), A129–A132.
* D. Quillen, *On the formal group laws of unoriented and complex cobordism theory*, Bull. Amer.
  Math. Soc. 75 (1969), 1293–1298.
* [M. Hazewinkel, *Formal Groups and Applications*][hazewinkel1978], Chapter III, §16.
* D. C. Ravenel, *Complex Cobordism and Stable Homotopy Groups of Spheres* (1986), Ch. 4 §1, A2.1.
-/

public section

noncomputable section

open MvPolynomial

namespace TauCeti.LazardRing

section Localization

variable (p : ℕ) [hp : Fact p.Prime]

/-- For a prime `p`, if every prime `q ∤ p` is a unit in `R`, then so is every prime `q ≠ p`. -/
theorem isUnit_prime_ne_of_forall_not_dvd {R : Type*} [CommRing R]
    (hunit : ∀ q : ℕ, q.Prime → ¬ q ∣ p → IsUnit (q : R)) (q : ℕ) (hq : q.Prime) (hqp : q ≠ p) :
    IsUnit (q : R) :=
  hunit q hq fun h ↦ hqp ((Nat.prime_dvd_prime_iff_eq hq hp.out).mp h)

variable (S : Type*) [CommRing S] [Algebra LazardRing S] [IsLocalization (coprimeSubmonoid p) S]

/-- For a prime `p`, every prime `q ≠ p` is invertible in any localization `S` of `LazardRing` at
`coprimeSubmonoid p`. -/
theorem isUnit_prime_ne_of_isLocalization (q : ℕ) (hq : q.Prime) (hqp : q ≠ p) :
    IsUnit (q : S) :=
  isUnit_prime_ne_of_forall_not_dvd p (isUnit_prime_of_isLocalization p S) q hq hqp

/-! ### Quillen's `p`-typicalization idempotent and its fixed subring -/

/-- **Quillen's `p`-typicalization idempotent** `e_p : S →+* S`: the endomorphism classifying
Cartier's canonical `p`-typicalization of `formalGroup.map (algebraMap LazardRing S)`. -/
def typicalIdempotent : S →+* S :=
  localizedLift p S (isUnit_prime_of_isLocalization p S)
    ⟨(formalGroup.map (algebraMap LazardRing S)).pTypicalFormalGroup p
      (isUnit_prime_ne_of_isLocalization p S), inferInstance⟩

/-- Base-changing `formalGroup.map (algebraMap LazardRing S)` along `typicalIdempotent p S` gives
its canonical `p`-typicalization. -/
theorem map_typicalIdempotent :
    (formalGroup.map (algebraMap LazardRing S)).map (typicalIdempotent p S) =
      (formalGroup.map (algebraMap LazardRing S)).pTypicalFormalGroup p
        (isUnit_prime_ne_of_isLocalization p S) := map_localizedLift p S _ _

/-- Restricting `typicalIdempotent p S` along `algebraMap LazardRing S` classifies the
`p`-typicalization of `formalGroup.map (algebraMap LazardRing S)`. -/
@[simp]
theorem typicalIdempotent_comp_algebraMap :
    (typicalIdempotent p S).comp (algebraMap LazardRing S) =
      lift ⟨(formalGroup.map (algebraMap LazardRing S)).pTypicalFormalGroup p
        (isUnit_prime_ne_of_isLocalization p S), inferInstance⟩ :=
  localizedLift_comp_algebraMap p S _ _

/-- The formal group law classified by `typicalIdempotent p S` is `p`-typical. -/
theorem isPTypical_map_typicalIdempotent :
    ((formalGroup.map (algebraMap LazardRing S)).map (typicalIdempotent p S)).IsPTypical p := by
  rw [FormalGroup.isPTypical_congr (map_typicalIdempotent p S)]
  exact (formalGroup.map (algebraMap LazardRing S)).isPTypical_pTypicalFormalGroup p _

/-- Precomposing the classifying map of `F` with `typicalIdempotent p S` classifies the canonical
`p`-typicalization of `F`. -/
theorem localizedLift_comp_typicalIdempotent {R : Type*} [CommRing R]
    (hunit : ∀ q : ℕ, q.Prime → ¬ q ∣ p → IsUnit (q : R)) (F : FormalGroup R) [F.IsComm] :
    (localizedLift p S hunit ⟨F, inferInstance⟩).comp (typicalIdempotent p S) =
      localizedLift p S hunit
        ⟨F.pTypicalFormalGroup p (isUnit_prime_ne_of_forall_not_dvd p hunit), inferInstance⟩ :=
  localizedHom_ext p <| by
    rw [← FormalGroup.map_comp, map_typicalIdempotent,
      (formalGroup.map (algebraMap LazardRing S)).map_pTypicalFormalGroup _ p _,
      FormalGroup.pTypicalFormalGroup_congr (map_localizedLift p S hunit ⟨F, inferInstance⟩) p _,
      map_localizedLift]

/-- `f ∘ typicalIdempotent p S = f` iff the formal group law classified by `f` is `p`-typical. -/
@[simp]
theorem comp_typicalIdempotent_eq_self_iff {R : Type*} [CommRing R] (f : S →+* R) :
    f.comp (typicalIdempotent p S) = f ↔
      ((formalGroup.map (algebraMap LazardRing S)).map f).IsPTypical p := by
  have hunit := isUnit_prime_of_ringHom p S f
  rw [← (localizedLift p S hunit).symm.injective.eq_iff, Subtype.ext_iff, coe_localizedLift_symm,
    coe_localizedLift_symm, ← FormalGroup.map_comp, map_typicalIdempotent,
    (formalGroup.map (algebraMap LazardRing S)).map_pTypicalFormalGroup f p _,
    FormalGroup.pTypicalFormalGroup_eq_self_iff]

/-- **Quillen's `p`-typicalization endomorphism is idempotent.** -/
@[simp]
theorem typicalIdempotent_comp_typicalIdempotent :
    (typicalIdempotent p S).comp (typicalIdempotent p S) = typicalIdempotent p S :=
  (comp_typicalIdempotent_eq_self_iff p S (typicalIdempotent p S)).mpr
    (isPTypical_map_typicalIdempotent p S)

/-- Evaluating `typicalIdempotent p S` twice is the same as evaluating it once. -/
@[simp]
theorem typicalIdempotent_typicalIdempotent (x : S) :
    typicalIdempotent p S (typicalIdempotent p S x) = typicalIdempotent p S x :=
  RingHom.congr_fun (typicalIdempotent_comp_typicalIdempotent p S) x

/-- An element of `S` is fixed by `typicalIdempotent p S` iff it lies in its range. -/
theorem typicalIdempotent_eq_self_iff_mem_range {x : S} :
    typicalIdempotent p S x = x ↔ x ∈ (typicalIdempotent p S).range :=
  ⟨fun hx ↦ ⟨x, hx⟩, fun ⟨y, hy⟩ ↦ hy ▸ typicalIdempotent_typicalIdempotent p S y⟩

/-- `(typicalIdempotent p S).rangeRestrict` retracts the subtype inclusion of the range. -/
@[simp]
theorem typicalIdempotent_rangeRestrict_comp_subtype :
    (typicalIdempotent p S).rangeRestrict.comp (typicalIdempotent p S).range.subtype =
      RingHom.id (typicalIdempotent p S).range := by
  ext ⟨_, ⟨y, rfl⟩⟩
  exact typicalIdempotent_typicalIdempotent p S y

private theorem typicalIdempotent_subtype_comp_rangeRestrict :
    (typicalIdempotent p S).range.subtype.comp (typicalIdempotent p S).rangeRestrict =
      typicalIdempotent p S := RingHom.ext (RingHom.coe_rangeRestrict (typicalIdempotent p S))

/-- The **universal `p`-typical formal group law** over `(typicalIdempotent p S).range`. -/
def typicalFormalGroup : FormalGroup (typicalIdempotent p S).range :=
  (formalGroup.map (algebraMap LazardRing S)).map (typicalIdempotent p S).rangeRestrict

/-- Unfold `typicalFormalGroup p S` as base change along `(typicalIdempotent p S).rangeRestrict`. -/
theorem typicalFormalGroup_def : typicalFormalGroup p S =
    (formalGroup.map (algebraMap LazardRing S)).map (typicalIdempotent p S).rangeRestrict := (rfl)

instance : (typicalFormalGroup p S).IsComm :=
  inferInstanceAs
    (((formalGroup.map (algebraMap LazardRing S)).map (typicalIdempotent p S).rangeRestrict).IsComm)

/-- Extending `typicalFormalGroup p S` from `(typicalIdempotent p S).range` to `S` gives
`(formalGroup.map (algebraMap LazardRing S)).pTypicalFormalGroup p _`. -/
@[simp]
theorem map_subtype_typicalFormalGroup :
    (typicalFormalGroup p S).map (typicalIdempotent p S).range.subtype =
      (formalGroup.map (algebraMap LazardRing S)).pTypicalFormalGroup p
        (isUnit_prime_ne_of_isLocalization p S) := by
  rw [typicalFormalGroup_def, FormalGroup.map_comp, typicalIdempotent_subtype_comp_rangeRestrict,
    map_typicalIdempotent]

/-- The formal group law `typicalFormalGroup p S` is `p`-typical. -/
@[simp]
theorem isPTypical_typicalFormalGroup : (typicalFormalGroup p S).IsPTypical p := by
  rw [← FormalGroup.isPTypical_map_iff (F := typicalFormalGroup p S)
      (φ := (typicalIdempotent p S).range.subtype) Subtype.val_injective,
    FormalGroup.isPTypical_congr (map_subtype_typicalFormalGroup p S)]
  exact (formalGroup.map (algebraMap LazardRing S)).isPTypical_pTypicalFormalGroup p _

/-- Ring homomorphisms out of `(typicalIdempotent p S).range` are determined by the base change of
`typicalFormalGroup p S` along them. -/
theorem typicalLocalizedHom_ext {S : Type*} [CommRing S] [Algebra LazardRing S]
    [IsLocalization (coprimeSubmonoid p) S] {R : Type*} [CommRing R]
    {f g : (typicalIdempotent p S).range →+* R}
    (h : (typicalFormalGroup p S).map f = (typicalFormalGroup p S).map g) : f = g := by
  have hcomp : f.comp (typicalIdempotent p S).rangeRestrict =
      g.comp (typicalIdempotent p S).rangeRestrict := by
    refine localizedHom_ext p ?_
    rwa [← FormalGroup.map_comp, ← FormalGroup.map_comp]
  simpa only [RingHom.comp_assoc, typicalIdempotent_rangeRestrict_comp_subtype, RingHom.comp_id]
    using congrArg (fun k ↦ k.comp (typicalIdempotent p S).range.subtype) hcomp

section TypicalLift

variable {R : Type*} [CommRing R] (hunit : ∀ q : ℕ, q.Prime → ¬ q ∣ p → IsUnit (q : R))
include hunit

/-- **Universal property of `(typicalIdempotent p S).range`**: for any commutative ring `R` in which
every prime `q ∤ p` is invertible, `p`-typical commutative formal group laws over `R` correspond
bijectively to ring homomorphisms `(typicalIdempotent p S).range →+* R`. -/
def typicalLocalizedLift :
    {F : FormalGroup R // ∃ (_ : F.IsComm), F.IsPTypical p} ≃
      ((typicalIdempotent p S).range →+* R) where
  toFun F := (localizedLift p S hunit ⟨F.val, F.property.1⟩).comp
      (typicalIdempotent p S).range.subtype
  invFun g :=
    ⟨(typicalFormalGroup p S).map g, ⟨inferInstance, (isPTypical_typicalFormalGroup p S).map g⟩⟩
  left_inv F := Subtype.ext <| by
    have : F.val.IsComm := F.property.1
    dsimp only
    rw [← FormalGroup.map_comp, map_subtype_typicalFormalGroup,
      (formalGroup.map (algebraMap LazardRing S)).map_pTypicalFormalGroup _ p _,
      FormalGroup.pTypicalFormalGroup_congr (map_localizedLift p S hunit ⟨F.val, F.property.1⟩) p _,
      F.val.pTypicalFormalGroup_eq_self_of_isPTypical p _ F.property.2]
  right_inv g := typicalLocalizedHom_ext p <| by
    dsimp only
    rw [← FormalGroup.map_comp, map_subtype_typicalFormalGroup,
      (formalGroup.map (algebraMap LazardRing S)).map_pTypicalFormalGroup _ p _,
      FormalGroup.pTypicalFormalGroup_congr
        (map_localizedLift p S hunit ⟨(typicalFormalGroup p S).map g, inferInstance⟩) p _,
      FormalGroup.pTypicalFormalGroup_eq_self_of_isPTypical _ p _
        ((isPTypical_typicalFormalGroup p S).map g)]

/-- Base-changing `typicalFormalGroup p S` along `typicalLocalizedLift p S hunit F` recovers `F`. -/
@[simp]
theorem map_typicalLocalizedLift (F : {F : FormalGroup R // ∃ (_ : F.IsComm), F.IsPTypical p}) :
    (typicalFormalGroup p S).map (typicalLocalizedLift p S hunit F) = F.val :=
  Subtype.ext_iff.mp ((typicalLocalizedLift p S hunit).left_inv F)

/-- The `p`-typical law classified by `g` is `(typicalFormalGroup p S).map g`. -/
@[simp]
theorem coe_typicalLocalizedLift_symm (g : (typicalIdempotent p S).range →+* R) :
    ((typicalLocalizedLift p S hunit).symm g).val = (typicalFormalGroup p S).map g := (rfl)

/-- On elements of `(typicalIdempotent p S).range`, `typicalLocalizedLift` agrees with
`localizedLift`. -/
theorem typicalLocalizedLift_apply (F : {F : FormalGroup R // ∃ (_ : F.IsComm), F.IsPTypical p})
    (x : (typicalIdempotent p S).range) :
    typicalLocalizedLift p S hunit F x = localizedLift p S hunit ⟨F.val, F.property.1⟩ x := (rfl)

/-- Extending `typicalLocalizedLift p S hunit F` along `(typicalIdempotent p S).rangeRestrict`
recovers `localizedLift p S hunit ⟨F.1, F.2.1⟩`. -/
@[simp]
theorem typicalLocalizedLift_comp_rangeRestrict
    (F : {F : FormalGroup R // ∃ (_ : F.IsComm), F.IsPTypical p}) :
    (typicalLocalizedLift p S hunit F).comp (typicalIdempotent p S).rangeRestrict =
      localizedLift p S hunit ⟨F.val, F.property.1⟩ := by
  have : F.val.IsComm := F.property.1
  rw [typicalLocalizedLift, Equiv.coe_fn_mk, RingHom.comp_assoc,
    typicalIdempotent_subtype_comp_rangeRestrict]
  exact (comp_typicalIdempotent_eq_self_iff p S _).mpr <|
    (FormalGroup.isPTypical_congr (map_localizedLift p S hunit ⟨F.val,
        F.property.1⟩) p).mpr F.property.2

/-- On images of `(typicalIdempotent p S).rangeRestrict`, `typicalLocalizedLift` agrees with
`localizedLift`. -/
@[simp]
theorem typicalLocalizedLift_rangeRestrict
    (F : {F : FormalGroup R // ∃ (_ : F.IsComm), F.IsPTypical p}) (x : S) :
    typicalLocalizedLift p S hunit F ((typicalIdempotent p S).rangeRestrict x) =
      localizedLift p S hunit ⟨F.val, F.property.1⟩ x :=
  RingHom.congr_fun (typicalLocalizedLift_comp_rangeRestrict p S hunit F) x

end TypicalLift

/-! ### Compatibility with `(L, L[b₁, b₂, …])` and with grading -/

/-- The homomorphism `L[b₁, b₂, …] →+* S` classifying `F_S` together with its canonical
`p`-typicalization coordinate. -/
def typicalCoordinateHom : MvPolynomial ℕ+ LazardRing →+* S :=
  coordinateChangeLift
    (⟨formalGroup.map (algebraMap LazardRing S), inferInstance⟩,
      ⟨(formalGroup.map (algebraMap LazardRing S)).pTypicalCoordinate p
        (isUnit_prime_ne_of_isLocalization p S),
        (formalGroup.map (algebraMap LazardRing S)).pTypicalCoordinate_mem_ker_linearCoeff p _⟩)

/-- Along `η_L = C`, `typicalCoordinateHom p S` restricts to `algebraMap LazardRing S`. -/
@[simp]
theorem typicalCoordinateHom_comp_C :
    (typicalCoordinateHom p S).comp C = algebraMap LazardRing S :=
  (coordinateChangeLift_comp_C _).trans (hom_ext (map_lift _))

/-- On constants from `LazardRing`, `typicalCoordinateHom p S` equals `algebraMap LazardRing S`. -/
@[simp]
theorem typicalCoordinateHom_C (r : LazardRing) :
    typicalCoordinateHom p S (C r) = algebraMap LazardRing S r :=
  RingHom.congr_fun (typicalCoordinateHom_comp_C p S) r

/-- `typicalCoordinateHom p S` sends `bᵢ` to `coeff (i + 1)` of the canonical `p`-typicalization
coordinate of `F_S`. -/
@[simp]
theorem typicalCoordinateHom_X (i : ℕ+) :
    typicalCoordinateHom p S (X i) = PowerSeries.coeff (i + 1)
      ((formalGroup.map (algebraMap LazardRing S)).pTypicalCoordinate p
        (isUnit_prime_ne_of_isLocalization p S)).toPowerSeries := coordinateChangeLift_X _ i

/-- `typicalCoordinateHom p S` specializes `universalStrictCoordinate` to the canonical
`p`-typicalization coordinate of `F_S`. -/
@[simp]
theorem map_typicalCoordinateHom_universalStrictCoordinate :
    FormalCoordinate.map (typicalCoordinateHom p S) FormalCoordinate.universalStrictCoordinate =
      (formalGroup.map (algebraMap LazardRing S)).pTypicalCoordinate p
        (isUnit_prime_ne_of_isLocalization p S) :=
  map_coordinateChangeLift_universalStrictCoordinate _

/-- Along `η_R`, `typicalCoordinateHom p S` restricts to `e_p ∘ algebraMap LazardRing S`. -/
@[simp]
theorem typicalCoordinateHom_comp_rightUnit :
    (typicalCoordinateHom p S).comp rightUnit =
      (typicalIdempotent p S).comp (algebraMap LazardRing S) := by
  rw [typicalCoordinateHom, coordinateChangeLift_comp_rightUnit, typicalIdempotent_comp_algebraMap]
  exact hom_ext <| by
    rw [map_lift, map_lift]
    exact (FormalGroup.pTypicalFormalGroup_def _ _ _).symm

section Graded

variable {τ : Type*} [SetLike τ S] [AddSubgroupClass τ S] {ℬ : ℕ → τ} [GradedRing ℬ]
  (halg : ∀ ⦃k : ℕ⦄ ⦃x : LazardRing⦄, x ∈ grading k → algebraMap LazardRing S x ∈ ℬ k)
include halg

/-- **Quillen's `p`-typicalization idempotent preserves homogeneous degrees** for any compatible
`ℕ`-grading `ℬ` on `S`. -/
theorem typicalIdempotent_mem_graded {k : ℕ} {b : S} (hb : b ∈ ℬ k) :
    typicalIdempotent p S b ∈ ℬ k := by
  let f : grading →+*ᵍ ℬ := ⟨algebraMap LazardRing S, fun hx ↦ halg hx⟩
  have halg_inst : f.toRingHom.toAlgebra = ‹Algebra LazardRing S› :=
    Algebra.algebra_ext _ _ fun _ ↦ rfl
  have hloc : letI := f.toRingHom.toAlgebra; IsLocalization (coprimeSubmonoid p) S :=
    halg_inst.symm ▸ ‹IsLocalization (coprimeSubmonoid p) S›
  obtain ⟨a, ha, m, hbm⟩ := f.exists_mem_mul_eq_of_isLocalization hloc
    (fun _ hm ↦ coprimeSubmonoid_subset_grading_zero p hm) hb
  have hm_fix : typicalIdempotent p S (algebraMap LazardRing S m) = algebraMap LazardRing S m := by
    obtain ⟨n, _, _, hn⟩ := mem_coprimeSubmonoid_iff.mp m.property
    rw [← hn, map_natCast, map_natCast]
  have hlift_alg : lift ⟨formalGroup.map (algebraMap LazardRing S), inferInstance⟩ =
      algebraMap LazardRing S := hom_ext (map_lift _)
  have hcoeff : ∀ d : Fin 2 →₀ ℕ,
      MvPowerSeries.coeff d (formalGroup.map (algebraMap LazardRing S)).toPowerSeries ∈
        ℬ (2 * (d.degree - 1)) :=
    (lift_mem_iff (.id ℕ) ⟨formalGroup.map (algebraMap LazardRing S), inferInstance⟩).mp
      fun _ _ hx ↦ by simpa only [hlift_alg, AddMonoidHom.id_apply] using halg hx
  have ha' : typicalIdempotent p S (algebraMap LazardRing S a) ∈ ℬ k := by
    rw [← RingHom.comp_apply, typicalIdempotent_comp_algebraMap]
    exact (lift_mem_iff (.id ℕ) _).mpr
      ((formalGroup.map (algebraMap LazardRing S)).coeff_pTypicalFormalGroup_mem 2 p _ hcoeff) ha
  have hmul : typicalIdempotent p S b * algebraMap LazardRing S m ∈ ℬ k := by
    rw [← hm_fix, ← map_mul]
    exact hbm ▸ ha'
  exact GradedAlgebra.mem_of_mul_mem_add_of_isLeftRegular ℬ
    (halg (coprimeSubmonoid_subset_grading_zero p m.property))
    (IsLocalization.map_units S m).isRegular.left (by rw [zero_add, mul_comm]; exact hmul)

/-- `typicalIdempotent p S` bundled as a graded ring endomorphism `ℬ →+*ᵍ ℬ`. -/
def gradedTypicalIdempotent : ℬ →+*ᵍ ℬ where
  toRingHom := typicalIdempotent p S
  map_mem hx := typicalIdempotent_mem_graded p S halg hx

/-- The underlying ring homomorphism of `gradedTypicalIdempotent` is `typicalIdempotent`. -/
@[simp]
theorem toRingHom_gradedTypicalIdempotent :
    (gradedTypicalIdempotent p S halg).toRingHom = typicalIdempotent p S := (rfl)

/-- Coercing `gradedTypicalIdempotent p S halg` to a function gives `typicalIdempotent p S`. -/
@[simp]
theorem coe_gradedTypicalIdempotent :
    ⇑(gradedTypicalIdempotent p S halg) = typicalIdempotent p S := (rfl)

/-- `gradedTypicalIdempotent p S halg` is idempotent as a graded ring endomorphism. -/
@[simp]
theorem gradedTypicalIdempotent_comp_gradedTypicalIdempotent :
    (gradedTypicalIdempotent p S halg).comp (gradedTypicalIdempotent p S halg) =
      gradedTypicalIdempotent p S halg :=
  GradedRingHom.ext fun x ↦ typicalIdempotent_typicalIdempotent p S x

end Graded

end Localization

end TauCeti.LazardRing
