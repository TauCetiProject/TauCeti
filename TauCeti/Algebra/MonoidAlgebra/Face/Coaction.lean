/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.RingTheory.Bialgebra.MonoidAlgebra
public import Mathlib.RingTheory.KrullDimension.Basic
public import TauCeti.Algebra.Group.Submonoid.Saturation
public import TauCeti.Algebra.MonoidAlgebra.Face.Basic
public import TauCeti.Algebra.MonoidAlgebra.GroupCompletion
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.RingTheory.FiniteType
import TauCeti.Algebra.Group.UniqueProds.TorsionFree
import TauCeti.RingTheory.KrullDimension.FiniteType

/-!
# Orbit localizations, torus coactions, and Krull dimensions of semigroup algebras

Let `S` be an additive submonoid of an abelian group `G` and `F : SaturatedAddSubmonoid S` a face
of `S`.

1. **Orbit localizations.** Inverting all coefficient-one monomials of `R[F]` yields
   `R[F.faceSubgroup]` (`SaturatedAddSubmonoid.isLocalization_addMonoidAlgebra_faceSubgroup`). When
   `S.FG`, both `R[AddSubgroup.closure S]` over `R[S]` and `R[F.faceSubgroup]` over `R[F]` are
   principal localizations `IsLocalization.Away (single u 1)` at an interior monomial. Composing
   face restriction with `F.toFaceSubgroup` gives `F.orbitMap R : R[S] →ₐ[R] R[F.faceSubgroup]`
   with kernel `F.toAddSubmonoid.faceIdeal R` (`SaturatedAddSubmonoid.ker_orbitMap`).
2. **Grading and torus coaction.** Any `w : M →+ L` induces `AddMonoidAlgebra.gradedCoaction R w :
   R[M] →ₐ[R] R[L] ⊗[R] R[M]`, satisfying counit and coassociativity with Mathlib's `Bialgebra` on
   `R[L]`. For `w = S.toGroupClosure`, `S.torusCoaction R` is the native coaction of
   `Spec R[AddSubgroup.closure S]` on `Spec R[S]`, for which face restriction, `F.orbitMap R`, and
   normalization are equivariant.
3. **Krull dimensions.** Over a field `k` and torsion-free `G`, for `S.FG` we prove
   `ringKrullDim k[S] = Module.finrank ℤ (AddSubgroup.closure S)` and
   `ringKrullDim k[F] = ringKrullDim k[F.faceSubgroup] = Module.finrank ℤ F.faceSubgroup`, strictly
   monotone in `F`.

## Main declarations

* `AddSubmonoid.FG.exists_isLocalization_away_addMonoidAlgebra_groupClosure` and
  `SaturatedAddSubmonoid.exists_isLocalization_away_faceSubgroup`: interior-monomial localizations.
* `SaturatedAddSubmonoid.orbitMap` and `SaturatedAddSubmonoid.ker_orbitMap`: orbit coordinate hom.
* `AddMonoidAlgebra.gradedCoaction` and `AddSubmonoid.torusCoaction`: native torus coaction.
* `AddMonoidAlgebra.ringKrullDim_of_free`, `AddSubmonoid.FG.ringKrullDim_addMonoidAlgebra`,
  `SaturatedAddSubmonoid.ringKrullDim_closedFace`, `SaturatedAddSubmonoid.ringKrullDim_orbit`, and
  `SaturatedAddSubmonoid.finrank_faceSubgroup_strictMono`: Krull dimensions.

## References

* W. Bruns and J. Gubeladze, *Polytopes, Rings, and K-Theory*, Chapters 2 and 4.
* E. Miller and B. Sturmfels, *Combinatorial Commutative Algebra*, Chapter 7.
* W. Fulton, *Introduction to Toric Varieties*, §§1.3 and 3.1.
-/

public section

open scoped TensorProduct
open AddMonoidAlgebra

private theorem isLocalization_mapDomain_of_single {M H R : Type*} [AddCommMonoid M]
    [AddCommGroup H] [CommSemiring R] {f : M →+ H} (hf : Function.Injective f)
    {T : Submonoid (AddMonoidAlgebra R M)}
    (hunits : ∀ s : T, IsUnit (mapDomain f s.1))
    (hsurj : ∀ g : H, ∃ (a : M) (s : T), single g (1 : R) * mapDomain f s.1 = single (f a) 1) :
    letI := (mapDomainRingHom R f).toAlgebra
    IsLocalization T (AddMonoidAlgebra R H) := by
  let := (mapDomainRingHom R f).toAlgebra
  have halg (p : AddMonoidAlgebra R M) :
      algebraMap _ (AddMonoidAlgebra R H) p = mapDomain f p := by
    rw [RingHom.algebraMap_toAlgebra, mapDomainRingHom_apply]
  refine ⟨⟨fun s ↦ halg s.1 ▸ hunits s, fun p ↦ ?_, fun {_ _} hab ↦ ?_⟩⟩
  · induction p using AddMonoidAlgebra.induction_on with
    | of g =>
      obtain ⟨a, s, hs⟩ := hsurj g
      exact ⟨⟨single a 1, s⟩, by simpa [halg, mapDomain_single] using hs⟩
    | add p q hp hq =>
      obtain ⟨⟨a, s⟩, ha⟩ := hp
      obtain ⟨⟨b, t⟩, hb⟩ := hq
      refine ⟨⟨a * t + b * s, s * t⟩, ?_⟩
      simp only [map_add, map_mul, Submonoid.coe_mul]
      rw [← ha, ← hb]; ring
    | smul r p hp =>
      obtain ⟨⟨a, s⟩, ha⟩ := hp
      exact ⟨⟨r • a, s⟩, by
        rw [smul_mul_assoc, ha]
        exact ((mapDomainAlgHom R R f).toLinearMap.map_smul r a).symm⟩
  · rw [halg, halg] at hab
    exact ⟨1, by simp [mapDomain_injective hf hab]⟩

namespace AddSubmonoid

section InteriorLocalization

/-- Every finitely generated additive submonoid `S` possesses an element `u : S` whose multiples
absorb every element of `S` by addition. -/
theorem FG.exists_forall_exists_add_eq_nsmul {M : Type*} [AddCommMonoid M] {S : AddSubmonoid M}
    (hS : S.FG) :
    ∃ u : S, ∀ b : S, ∃ (n : ℕ) (c : S), b + c = n • u := by
  classical
  obtain ⟨t, ht⟩ := isAddFG_iff.1 hS
  let gen : t → S := fun a ↦ ⟨a.1, ht ▸ subset_closure a.2⟩
  refine ⟨∑ a : t, gen a, fun ⟨y, hyS⟩ ↦ ?_⟩
  have hy : y ∈ closure (t : Set M) := ht.symm ▸ hyS
  induction hy using closure_induction with
  | mem z hz =>
    exact ⟨1, ∑ a ∈ Finset.univ.erase ⟨z, hz⟩, gen a, by
      rw [one_nsmul]; exact Finset.add_sum_erase Finset.univ gen (Finset.mem_univ ⟨z, hz⟩)⟩
  | zero => exact ⟨0, 0, by simp⟩
  | add x w hx hw ihx ihw =>
    obtain ⟨n₁, c₁, hc₁⟩ := ihx (ht ▸ hx)
    obtain ⟨n₂, c₂, hc₂⟩ := ihw (ht ▸ hw)
    have hcomm : (⟨x + w, hyS⟩ : S) + (c₁ + c₂) = (⟨x, ht ▸ hx⟩ + c₁) + (⟨w, ht ▸ hw⟩ + c₂) :=
      Subtype.ext (by simp only [coe_add]; abel)
    exact ⟨n₁ + n₂, c₁ + c₂, by rw [hcomm, hc₁, hc₂, add_nsmul]⟩

/-- If `f : M →+ H` is an injective additive homomorphism from a finitely generated additive monoid
`M` into an abelian group `H` such that every element of `H` can be shifted into `f '' M`, then
`R[H]` is a localization of `R[M]` away from a single coefficient-one monomial. -/
theorem _root_.AddMonoidAlgebra.exists_isLocalization_away_of_exists_add_eq {M H : Type*}
    [AddCommMonoid M] [AddMonoid.FG M] [AddCommGroup H] {f : M →+ H} (hf : Function.Injective f)
    (hshift : ∀ g : H, ∃ a b : M, g + f b = f a) (R : Type*) [CommSemiring R] :
    ∃ u : M,
      letI := (mapDomainRingHom R f).toAlgebra
      IsLocalization.Away (single u (1 : R)) (AddMonoidAlgebra R H) := by
  have htop : (⊤ : AddSubmonoid M).FG := (AddMonoid.fg_iff_addSubmonoid_fg ⊤).1 inferInstance
  obtain ⟨u, hu⟩ := htop.exists_forall_exists_add_eq_nsmul
  refine ⟨u.1, isLocalization_mapDomain_of_single hf (fun s ↦ ?_) (fun g ↦ ?_)⟩
  · obtain ⟨n, hn⟩ := s.2
    dsimp only at hn
    rw [← hn, single_pow, one_pow, mapDomain_single]
    exact (Group.isUnit (Multiplicative.ofAdd (f (n • u.1)))).map (of R H)
  · obtain ⟨a, b, hab⟩ := hshift g
    obtain ⟨n, c, hbc⟩ := hu ⟨b, trivial⟩
    have hnu : g + n • f u.1 = f (a + c.1) := by
      have hbc' : b + c.1 = n • u.1 := congrArg Subtype.val hbc
      rw [← map_nsmul, ← hbc', map_add, ← add_assoc, hab, ← map_add]
    exact ⟨a + c.1, ⟨single u.1 (1 : R) ^ n, n, rfl⟩, by
      simp [single_pow, single_mul_single, hnu]⟩

/-- When `S` is finitely generated, `R[AddSubgroup.closure S]` is the localization of `R[S]` away
from a single interior monomial `single u 1`. -/
theorem FG.exists_isLocalization_away_addMonoidAlgebra_groupClosure {G : Type*} [AddCommGroup G]
    {S : AddSubmonoid G} (hS : S.FG) (R : Type*) [CommSemiring R] :
    ∃ u : S,
      letI := (mapDomainRingHom R S.toGroupClosure).toAlgebra
      IsLocalization.Away (single u (1 : R))
        (AddMonoidAlgebra R (AddSubgroup.closure (S : Set G))) := by
  have : AddMonoid.FG S := (AddMonoid.fg_iff_addSubmonoid_fg S).2 hS
  exact exists_isLocalization_away_of_exists_add_eq S.toGroupClosure_injective
    S.exists_add_toGroupClosure_eq R

end InteriorLocalization

end AddSubmonoid

namespace SaturatedAddSubmonoid

section OrbitMap

variable {G : Type*} [AddCommGroup G] {S : AddSubmonoid G} (F : SaturatedAddSubmonoid S)

/-- For any face `F` of `S`, `R[F.faceSubgroup]` is the localization of `R[F]` at all
coefficient-one monomials along `F.toFaceSubgroup`. -/
theorem isLocalization_addMonoidAlgebra_faceSubgroup (R : Type*) [CommSemiring R] :
    letI := (mapDomainRingHom R F.toFaceSubgroup).toAlgebra
    IsLocalization (MonoidHom.mrange (of R F)) (AddMonoidAlgebra R F.faceSubgroup) :=
  isLocalization_mapDomain_of_single F.toFaceSubgroup_injective
    (fun s ↦ by
      obtain ⟨m, hm⟩ := s.2
      rw [← hm, of_apply, mapDomain_single]
      exact (Group.isUnit (Multiplicative.ofAdd (F.toFaceSubgroup m.toAdd))).map
        (of R F.faceSubgroup))
    (fun g ↦ by
      obtain ⟨a, b, hab⟩ := F.exists_add_toFaceSubgroup_eq g
      exact ⟨a, ⟨of R F (Multiplicative.ofAdd b), _, rfl⟩, by simp [of_apply, hab]⟩)

/-- When `S` is finitely generated, `R[F.faceSubgroup]` is a localization of the closed face
algebra `R[F]` away from a single monomial `single u 1`. -/
theorem exists_isLocalization_away_faceSubgroup (hS : S.FG) (R : Type*) [CommSemiring R] :
    ∃ u : F,
      letI := (mapDomainRingHom R F.toFaceSubgroup).toAlgebra
      IsLocalization.Away (single u (1 : R)) (AddMonoidAlgebra R F.faceSubgroup) := by
  have : AddMonoid.FG S := (AddMonoid.fg_iff_addSubmonoid_fg S).2 hS
  exact exists_isLocalization_away_of_exists_add_eq F.toFaceSubgroup_injective
    F.exists_add_toFaceSubgroup_eq R

/-- Coordinate-ring homomorphism of the torus orbit associated to a face `F` of `S`, obtained by
restricting `R[S]` to `R[F]` and localizing along `F.toFaceSubgroup : F →+ F.faceSubgroup`. -/
noncomputable def orbitMap (R : Type*) [CommSemiring R] :
    AddMonoidAlgebra R S →ₐ[R] AddMonoidAlgebra R F.faceSubgroup :=
  (mapDomainAlgHom R R F.toFaceSubgroup).comp (F.toAddSubmonoid.faceRestriction F.addSaturated R)

/-- Explicit definition of `SaturatedAddSubmonoid.orbitMap`. -/
theorem orbitMap_def (R : Type*) [CommSemiring R] :
    F.orbitMap R = (mapDomainAlgHom R R F.toFaceSubgroup).comp
      (F.toAddSubmonoid.faceRestriction F.addSaturated R) := (rfl)

/-- On a monomial in `F`, `F.orbitMap R` sends `single a r` to `single (F.toFaceSubgroup a) r`. -/
@[simp]
theorem orbitMap_single_mem (R : Type*) [CommSemiring R] (a : F) (r : R) :
    F.orbitMap R (single (a : S) r) = single (F.toFaceSubgroup a) r := by
  rw [orbitMap_def, AlgHom.comp_apply]
  have hmem : single (a : S) r = single (↑(⟨a.1, a.2⟩ : F.toAddSubmonoid)) r := rfl
  rw [hmem, F.toAddSubmonoid.faceRestriction_single_mem F.addSaturated, mapDomainAlgHom_apply,
    mapDomain_single]
  rfl

/-- On a monomial outside `F`, `F.orbitMap R` vanishes. -/
@[simp]
theorem orbitMap_single_of_notMem (R : Type*) [CommSemiring R] {s : S} (hs : s ∉ F) (r : R) :
    F.orbitMap R (single s r) = 0 := by
  simp [orbitMap, F.toAddSubmonoid.faceRestriction_single_of_notMem F.addSaturated hs]

/-- Over any commutative semiring `R`, the kernel of `F.orbitMap R` is `F.faceIdeal R`. -/
@[simp]
theorem ker_orbitMap (R : Type*) [CommSemiring R] :
    RingHom.ker (F.orbitMap R) = F.toAddSubmonoid.faceIdeal R := by
  ext p
  rw [RingHom.mem_ker, orbitMap_def, AlgHom.comp_apply, ← F.toAddSubmonoid.ker_faceRestriction
    F.addSaturated, RingHom.mem_ker]
  exact ⟨fun h ↦ mapDomain_injective F.toFaceSubgroup_injective (by simpa using h),
    fun h ↦ by simp [h]⟩

end OrbitMap

end SaturatedAddSubmonoid

namespace AddMonoidAlgebra

section Coaction

variable (R : Type*) [CommSemiring R]

/-- For an additive monoid homomorphism `w : M →+ L`, `gradedCoaction R w` is the `R`-algebra
comodule map `R[M] →ₐ[R] R[L] ⊗[R] R[M]` sending `single m r` to `single (w m) 1 ⊗ₜ single m r`. -/
noncomputable def gradedCoaction {M L : Type*} [AddCommMonoid M] [AddCommMonoid L] (w : M →+ L) :
    AddMonoidAlgebra R M →ₐ[R] AddMonoidAlgebra R L ⊗[R] AddMonoidAlgebra R M :=
  (Algebra.TensorProduct.map (mapDomainAlgHom R R w) (AlgHom.id R _)).comp
    (Bialgebra.comulAlgHom R (AddMonoidAlgebra R M))

/-- `gradedCoaction R w` sends `single m r` to `single (w m) 1 ⊗ₜ single m r`. -/
@[simp]
theorem gradedCoaction_single {M L : Type*} [AddCommMonoid M] [AddCommMonoid L] (w : M →+ L)
    (m : M) (r : R) :
    gradedCoaction R w (single m r) = single (w m) 1 ⊗ₜ[R] single m r := by simp [gradedCoaction]

/-- For the identity homomorphism, `gradedCoaction` recovers the bialgebra comultiplication. -/
@[simp]
theorem gradedCoaction_id (L : Type*) [AddCommMonoid L] :
    gradedCoaction R (AddMonoidHom.id L) = Bialgebra.comulAlgHom R (AddMonoidAlgebra R L) := by
  ext; simp

/-- Counit axiom for `gradedCoaction`: applying the counit of `R[L]` on the left recovers the
identity on `R[M]`. -/
@[simp]
theorem lid_comp_map_counit_gradedCoaction {M L : Type*} [AddCommMonoid M] [AddCommMonoid L]
    (w : M →+ L) :
    (Algebra.TensorProduct.lid R (AddMonoidAlgebra R M)).toAlgHom.comp
      ((Algebra.TensorProduct.map (Bialgebra.counitAlgHom R (AddMonoidAlgebra R L))
        (AlgHom.id R _)).comp (gradedCoaction R w)) = AlgHom.id R (AddMonoidAlgebra R M) := by
  ext; simp

/-- Coassociativity of `gradedCoaction` with respect to the comultiplication of `R[L]`. -/
theorem assoc_comp_map_gradedCoaction {M L : Type*} [AddCommMonoid M] [AddCommMonoid L]
    (w : M →+ L) :
    (Algebra.TensorProduct.assoc R R R (AddMonoidAlgebra R L) (AddMonoidAlgebra R L)
      (AddMonoidAlgebra R M)).toAlgHom.comp
      ((Algebra.TensorProduct.map (Bialgebra.comulAlgHom R (AddMonoidAlgebra R L))
        (AlgHom.id R _)).comp (gradedCoaction R w)) =
      (Algebra.TensorProduct.map (AlgHom.id R _) (gradedCoaction R w)).comp
        (gradedCoaction R w) := by
  ext; simp

/-- Naturality of `gradedCoaction` under compatible additive monoid homomorphisms. -/
theorem map_mapDomain_comp_gradedCoaction {M₁ M₂ L₁ L₂ : Type*} [AddCommMonoid M₁]
    [AddCommMonoid M₂] [AddCommMonoid L₁] [AddCommMonoid L₂] {w₁ : M₁ →+ L₁} {w₂ : M₂ →+ L₂}
    {g : L₁ →+ L₂} {f : M₁ →+ M₂} (h : w₂.comp f = g.comp w₁) :
    (Algebra.TensorProduct.map (mapDomainAlgHom R R g) (mapDomainAlgHom R R f)).comp
      (gradedCoaction R w₁) = (gradedCoaction R w₂).comp (mapDomainAlgHom R R f) := by
  ext m
  have hm : w₂ (f m) = g (w₁ m) := DFunLike.congr_fun h m
  simp [hm]

/-- Restriction to a face `F` is equivariant with respect to `gradedCoaction`. -/
theorem map_faceRestriction_comp_gradedCoaction {M L : Type*} [AddCommMonoid M] [AddCommMonoid L]
    (w : M →+ L) (F : SaturatedAddSubmonoid M) :
    (Algebra.TensorProduct.map (AlgHom.id R (AddMonoidAlgebra R L))
      (F.toAddSubmonoid.faceRestriction F.addSaturated R)).comp (gradedCoaction R w) =
      (gradedCoaction R (w.comp F.toAddSubmonoid.subtype)).comp
        (F.toAddSubmonoid.faceRestriction F.addSaturated R) := by
  ext m
  by_cases hm : m ∈ F
  · have hmem : single m (1 : R) = single (↑(⟨m, hm⟩ : F.toAddSubmonoid)) (1 : R) := rfl
    rw [AlgHom.comp_apply, AlgHom.comp_apply, gradedCoaction_single, Algebra.TensorProduct.map_tmul,
      AlgHom.id_apply, hmem, F.toAddSubmonoid.faceRestriction_single_mem F.addSaturated]
    simp
  · simp [F.toAddSubmonoid.faceRestriction_single_of_notMem F.addSaturated hm]

end Coaction

end AddMonoidAlgebra

namespace AddSubmonoid

section TorusCoaction

variable {G : Type*} [AddCommGroup G] (S : AddSubmonoid G) (R : Type*) [CommSemiring R]

/-- The native coaction of the dense torus algebra `R[AddSubgroup.closure S]` on `R[S]`. -/
noncomputable def torusCoaction :
    AddMonoidAlgebra R S →ₐ[R]
      AddMonoidAlgebra R (AddSubgroup.closure (S : Set G)) ⊗[R] AddMonoidAlgebra R S :=
  gradedCoaction R S.toGroupClosure

/-- Explicit definition of `AddSubmonoid.torusCoaction`. -/
theorem torusCoaction_def : S.torusCoaction R = gradedCoaction R S.toGroupClosure := (rfl)

/-- `S.torusCoaction R` sends `single s r` to `single (S.toGroupClosure s) 1 ⊗ₜ single s r`. -/
@[simp]
theorem torusCoaction_single (s : S) (r : R) :
    S.torusCoaction R (single s r) = single (S.toGroupClosure s) 1 ⊗ₜ[R] single s r :=
  gradedCoaction_single R S.toGroupClosure s r

/-- For any face `F` of `S`, `F.orbitMap R` is equivariant for the ambient torus coaction of
`R[AddSubgroup.closure S]`. -/
theorem map_orbitMap_comp_torusCoaction (F : SaturatedAddSubmonoid S) :
    (Algebra.TensorProduct.map (AlgHom.id R _) (F.orbitMap R)).comp (S.torusCoaction R) =
      (gradedCoaction R F.faceSubgroup.subtype).comp (F.orbitMap R) := by
  ext s
  by_cases hs : s ∈ F
  · have hmem : single s (1 : R) = single (↑(⟨s, hs⟩ : F)) (1 : R) := rfl
    rw [AlgHom.comp_apply, AlgHom.comp_apply, torusCoaction_single, Algebra.TensorProduct.map_tmul,
      AlgHom.id_apply, hmem, F.orbitMap_single_mem, gradedCoaction_single,
      AddSubgroup.coe_subtype, F.coe_toFaceSubgroup]
  · simp [F.orbitMap_single_of_notMem R hs]

/-- The normalization map from `R[S]` to `R[S.nsmulSaturation ⊓ AddSubgroup.closure S]` is
equivariant for the ambient torus `R[AddSubgroup.closure S]`. -/
theorem map_inclusion_nsmulSaturation_comp_torusCoaction :
    (Algebra.TensorProduct.map (AlgHom.id R _)
      (mapDomainAlgHom R R
        (inclusion (le_inf S.le_nsmulSaturation AddSubgroup.subset_closure)))).comp
      (S.torusCoaction R) =
      (gradedCoaction R S.nsmulSaturationInfClosureToGroupClosure).comp
        (mapDomainAlgHom R R
          (inclusion (le_inf S.le_nsmulSaturation AddSubgroup.subset_closure))) := by
  simpa [torusCoaction] using map_mapDomain_comp_gradedCoaction R (g := .id _)
    (AddMonoidHom.ext fun s ↦ S.nsmulSaturationInfClosureToGroupClosure_inclusion_apply s)

end TorusCoaction

end AddSubmonoid

namespace AddMonoidAlgebra

section KrullDimension

/-- Over a field `k`, the Laurent group algebra `k[L]` of a finitely generated free abelian group
`L` has Krull dimension `Module.finrank ℤ L`. -/
theorem ringKrullDim_of_free (k L : Type*) [Field k] [AddCommGroup L] [Module.Finite ℤ L]
    [Module.Free ℤ L] :
    ringKrullDim (AddMonoidAlgebra k L) = Module.finrank ℤ L := by
  classical
  let b := Module.Free.chooseBasis ℤ L
  let ι := Module.Free.ChooseBasisIndex ℤ L
  let castHom : (ι →₀ ℕ) →+ (ι →₀ ℤ) := Finsupp.mapRange.addMonoidHom (Nat.castAddMonoidHom ℤ)
  have hcast_inj : Function.Injective castHom :=
    Finsupp.mapRange_injective (Nat.castAddMonoidHom ℤ) (map_zero _) Nat.cast_injective
  have hshift (g : ι →₀ ℤ) : ∃ a c : ι →₀ ℕ, g + castHom c = castHom a := by
    refine ⟨g.mapRange (fun z ↦ z.toNat) rfl, g.mapRange (fun z ↦ (-z).toNat) rfl, ?_⟩
    ext i
    simp only [Finsupp.add_apply, castHom, Finsupp.mapRange.addMonoidHom_apply,
      Finsupp.mapRange_apply, Nat.coe_castAddMonoidHom]
    lia
  have : AddMonoid.FG (ι →₀ ℕ) := AddMonoid.fg_iff.2
    ⟨Set.range fun i : ι ↦ Finsupp.single i 1, eq_top_iff.2 fun f _ ↦ by
      refine f.induction_linear (zero_mem _) (fun _ _ ↦ add_mem) fun i n ↦ ?_
      have hn : Finsupp.single i n = n • Finsupp.single i 1 := by ext j; simp [Finsupp.single_apply]
      exact hn ▸ nsmul_mem (AddSubmonoid.subset_closure (Set.mem_range_self i)) n,
      Set.finite_range _⟩
  obtain ⟨u, hu⟩ := exists_isLocalization_away_of_exists_add_eq hcast_inj hshift k
  let := (mapDomainRingHom k castHom).toAlgebra
  have hdim : ringKrullDim (AddMonoidAlgebra k (ι →₀ ℤ)) = Nat.card ι := by
    rw [TauCeti.ringKrullDim_localization_away (A := MvPolynomial ι k) k
      (single_ne_zero.2 (one_ne_zero : (1 : k) ≠ 0) : (single u (1 : k) : MvPolynomial ι k) ≠ 0)
      (AddMonoidAlgebra k (ι →₀ ℤ)),
      MvPolynomial.ringKrullDim_of_isNoetherianRing_of_finite, ringKrullDim_eq_zero_of_field,
      zero_add]
  rw [ringKrullDim_eq_of_ringEquiv (domCongr k k b.repr.toAddEquiv).toRingEquiv, hdim,
    Module.finrank_eq_nat_card_basis b]

end KrullDimension

end AddMonoidAlgebra

namespace AddSubmonoid

/-- Over a field `k`, the semigroup algebra `k[S]` of a finitely generated submonoid `S` of a
torsion-free abelian group `G` has Krull dimension `Module.finrank ℤ (AddSubgroup.closure S)`. -/
theorem FG.ringKrullDim_addMonoidAlgebra {G : Type*} [AddCommGroup G] [HasUniqueDiv G]
    {S : AddSubmonoid G} (hS : S.FG) (k : Type*) [Field k] :
    ringKrullDim (AddMonoidAlgebra k S) =
      Module.finrank ℤ (AddSubgroup.closure (S : Set G)) := by
  let L := AddSubgroup.closure (S : Set G)
  have : AddMonoid.FG S := (AddMonoid.fg_iff_addSubmonoid_fg S).2 hS
  have : Algebra.FiniteType k (AddMonoidAlgebra k S) := AddMonoidAlgebra.finiteType_of_fg k S
  have : UniqueSums S := .of_injective_addHom S.subtype.toAddHom S.subtype_injective inferInstance
  have : Module.Finite ℤ L := Module.Finite.iff_addGroup_fg.2
    ((AddGroup.fg_iff_addSubgroup_fg L).2 hS.addSubgroupClosure)
  obtain ⟨u, _⟩ := hS.exists_isLocalization_away_addMonoidAlgebra_groupClosure k
  let := (mapDomainRingHom k S.toGroupClosure).toAlgebra
  rw [← TauCeti.ringKrullDim_localization_away k
    (single_ne_zero.2 (one_ne_zero : (1 : k) ≠ 0) : single u (1 : k) ≠ 0)
    (AddMonoidAlgebra k L), AddMonoidAlgebra.ringKrullDim_of_free k L]

end AddSubmonoid

namespace SaturatedAddSubmonoid

variable {G : Type*} [AddCommGroup G] [HasUniqueDiv G] {S : AddSubmonoid G}

/-- Over a field `k`, the localized orbit coordinate algebra `k[F.faceSubgroup]` of a face `F` of a
finitely generated submonoid `S` has Krull dimension `Module.finrank ℤ F.faceSubgroup`. -/
theorem ringKrullDim_orbit (hS : S.FG) (F : SaturatedAddSubmonoid S) (k : Type*) [Field k] :
    ringKrullDim (AddMonoidAlgebra k F.faceSubgroup) = Module.finrank ℤ F.faceSubgroup := by
  have : AddMonoid.FG S := (AddMonoid.fg_iff_addSubmonoid_fg S).2 hS
  have : Module.Finite ℤ F.faceSubgroup := Module.Finite.iff_addGroup_fg.2
    ((AddGroup.fg_iff_addSubgroup_fg F.faceSubgroup).2 (F.fg_faceSubgroup F.fg_toAddSubmonoid))
  have : HasUniqueDiv F.faceSubgroup := Function.Injective.hasUniqueDiv
    ((AddSubgroup.closure (S : Set G)).subtype.comp F.faceSubgroup.subtype)
    ((AddSubgroup.closure (S : Set G)).subtype_injective.comp F.faceSubgroup.subtype_injective)
  exact AddMonoidAlgebra.ringKrullDim_of_free k F.faceSubgroup

/-- Over a field `k`, the closed face algebra `k[F]` of a face `F` of a finitely generated
submonoid `S` has Krull dimension `Module.finrank ℤ F.faceSubgroup`. -/
theorem ringKrullDim_closedFace (hS : S.FG) (F : SaturatedAddSubmonoid S) (k : Type*) [Field k] :
    ringKrullDim (AddMonoidAlgebra k F) = Module.finrank ℤ F.faceSubgroup := by
  have : AddMonoid.FG S := (AddMonoid.fg_iff_addSubmonoid_fg S).2 hS
  have : Algebra.FiniteType k (AddMonoidAlgebra k F) := AddMonoidAlgebra.finiteType_of_fg k F
  have : UniqueSums F := .of_injective_addHom (S.subtype.comp F.toAddSubmonoid.subtype).toAddHom
    (S.subtype_injective.comp F.toAddSubmonoid.subtype_injective) inferInstance
  obtain ⟨u, _⟩ := F.exists_isLocalization_away_faceSubgroup hS k
  let := (mapDomainRingHom k F.toFaceSubgroup).toAlgebra
  rw [← TauCeti.ringKrullDim_localization_away k
    (single_ne_zero.2 (one_ne_zero : (1 : k) ≠ 0) : single u (1 : k) ≠ 0)
    (AddMonoidAlgebra k F.faceSubgroup), F.ringKrullDim_orbit hS k]

/-- Strict inclusion of faces of a finitely generated submonoid `S` of a torsion-free abelian group
strictly increases the rank of `F.faceSubgroup`. -/
theorem finrank_faceSubgroup_strictMono (hS : S.FG) :
    StrictMono (fun F : SaturatedAddSubmonoid S ↦ Module.finrank ℤ F.faceSubgroup) := by
  intro F₁ F₂ hlt
  obtain ⟨s, hs₂, hs₁⟩ := IsConcreteLE.exists_of_lt hlt
  let F₁' : SaturatedAddSubmonoid F₂ := F₁.comap F₂.toAddSubmonoid.subtype
  let e : F₁' ≃+ F₁ :=
    { toFun x := ⟨x.1, SaturatedAddSubmonoid.mem_comap.1 x.2⟩
      invFun y := ⟨⟨y.1, hlt.le y.2⟩, SaturatedAddSubmonoid.mem_comap.2 y.2⟩
      left_inv _ := rfl, right_inv _ := rfl, map_add' _ _ := rfl }
  let g : AddMonoidAlgebra ℚ F₂ →+* AddMonoidAlgebra ℚ F₁ :=
    (domCongr ℚ ℚ e).toRingEquiv.toRingHom.comp
      (F₁'.toAddSubmonoid.faceRestriction F₁'.addSaturated ℚ).toRingHom
  have hsurj : Function.Surjective g := (domCongr ℚ ℚ e).surjective.comp
    (F₁'.toAddSubmonoid.faceRestriction_surjective F₁'.addSaturated)
  have : UniqueSums F₂ := .of_injective_addHom (S.subtype.comp F₂.toAddSubmonoid.subtype).toAddHom
    (S.subtype_injective.comp F₂.toAddSubmonoid.subtype_injective) inferInstance
  have hs_nzd : single (⟨s, hs₂⟩ : F₂) (1 : ℚ) ∈ nonZeroDivisors (AddMonoidAlgebra ℚ F₂) :=
    mem_nonZeroDivisors_of_ne_zero (single_ne_zero.2 one_ne_zero)
  have hs_ker : g (single (⟨s, hs₂⟩ : F₂) (1 : ℚ)) = 0 := by
    have hnot : (⟨s, hs₂⟩ : F₂) ∉ F₁' := fun h ↦ hs₁ (SaturatedAddSubmonoid.mem_comap.1 h)
    simp [g, F₁'.toAddSubmonoid.faceRestriction_single_of_notMem F₁'.addSaturated hnot]
  have hdim := ringKrullDim_succ_le_of_surjective g hsurj hs_nzd hs_ker
  rw [F₁.ringKrullDim_closedFace hS ℚ, F₂.ringKrullDim_closedFace hS ℚ] at hdim
  exact_mod_cast hdim

end SaturatedAddSubmonoid
