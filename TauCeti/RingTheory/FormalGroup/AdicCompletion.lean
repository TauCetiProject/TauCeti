/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.FormalGroup.LazardRing.Basic
public import TauCeti.RingTheory.AdicCompletion.AlgHom

/-!
# Formal group laws over adic inverse limits

A compatible system of commutative formal group laws over `R ⧸ I ^ n` determines a
unique commutative law over `AdicCompletion I R`. If `R` is `I`-adically complete,
this gives a law over `R` itself, with exactly the prescribed reductions.

`TauCeti.FormalGroupAdicSystem.completionEquiv` and
`TauCeti.FormalGroupAdicSystem.completeEquiv` express these assertions as equivalences.
The construction uses the classifying maps from the Lazard ring and Mathlib's
`AdicCompletion.liftRingHom`, so compatibility of the full formal group laws, not
just their truncations in the coordinate variables, is retained. No finite-generation,
Noetherian, local-ring, or torsion-freeness hypothesis is required.

This is the fixed-coordinate inverse-limit comparison used when constructing formal
moduli over complete local rings. It does not identify orbit sets of laws under
coordinate changes with inverse limits of orbit sets.

## References

* J. Lubin and J. Tate, *Formal moduli for one-parameter formal Lie groups*,
  Bull. Soc. Math. France 94 (1966).
-/

public section

noncomputable section

namespace FormalGroup

variable {R : Type*} [CommRing R] {I : Ideal R}

/-- Equality of laws over the completion can be tested on all coefficient reductions. -/
theorem ext_adicCompletion {F G : FormalGroup (AdicCompletion I R)}
    (h : ∀ n, F.map (AdicCompletion.evalₐ I n).toRingHom =
      G.map (AdicCompletion.evalₐ I n).toRingHom) : F = G := by
  apply FormalGroup.ext
  apply MvPowerSeries.ext
  intro d
  apply AdicCompletion.ext_evalₐ
  intro n
  have hd := congrArg (fun H : FormalGroup (R ⧸ I ^ n) ↦
    MvPowerSeries.coeff d H.toPowerSeries) (h n)
  simpa only [FormalGroup.map_toPowerSeries, MvPowerSeries.coeff_map,
    AlgHom.toRingHom_eq_coe, RingHom.coe_coe] using hd

/-- Laws over an adically Hausdorff ring are determined by all their reductions. -/
theorem ext_adic [IsHausdorff I R] {F G : FormalGroup R}
    (h : ∀ n, F.map (Ideal.Quotient.mk (I ^ n)) = G.map (Ideal.Quotient.mk (I ^ n))) :
    F = G := by
  apply FormalGroup.ext
  apply MvPowerSeries.ext
  intro d
  exact congrFun (IsHausdorff.funext' I (f := fun d ↦ MvPowerSeries.coeff d F.toPowerSeries)
    (g := fun d ↦ MvPowerSeries.coeff d G.toPowerSeries) fun n e ↦ by
      simpa only [FormalGroup.map_toPowerSeries, MvPowerSeries.coeff_map] using
        congrArg (fun H : FormalGroup (R ⧸ I ^ n) ↦
          MvPowerSeries.coeff e H.toPowerSeries) (h n)) d

end FormalGroup

namespace TauCeti

variable {R : Type*} [CommRing R]

/-- Commutative formal group laws over all the quotients `R ⧸ I ^ n`, compatible
with coefficient reduction. -/
structure FormalGroupAdicSystem (I : Ideal R) where
  /-- The law at the indicated power of the ideal. -/
  formalGroup (n : ℕ) : FormalGroup (R ⧸ I ^ n)
  /-- Each law is commutative. -/
  isComm (n : ℕ) : (formalGroup n).IsComm
  /-- Reduction from a higher power gives the law at a lower power. -/
  map_eq {m n : ℕ} (h : m ≤ n) :
    (formalGroup n).map (Ideal.Quotient.factorPow I h) = formalGroup m

attribute [instance] FormalGroupAdicSystem.isComm

namespace FormalGroupAdicSystem

variable {I : Ideal R}

/-- A compatible system is determined by its formal group laws. -/
@[ext]
theorem ext {F G : FormalGroupAdicSystem I}
    (h : ∀ n, F.formalGroup n = G.formalGroup n) : F = G := by
  cases F
  cases G
  congr
  exact funext h

/-- Reduce a commutative law over the completion at every power of the ideal. -/
def ofCompletion (I : Ideal R) (F : FormalGroup (AdicCompletion I R)) [F.IsComm] :
    FormalGroupAdicSystem I where
  formalGroup n := F.map (AdicCompletion.evalₐ I n).toRingHom
  isComm _ := inferInstance
  map_eq h := by
    rw [FormalGroup.map_comp]
    congr 1
    ext x
    exact AdicCompletion.factor_evalₐ h x

/-- The law at level `n` is coefficient reduction from the completion. -/
@[simp]
theorem formalGroup_ofCompletion (I : Ideal R)
    (F : FormalGroup (AdicCompletion I R)) [F.IsComm] (n : ℕ) :
    (ofCompletion I F).formalGroup n = F.map (AdicCompletion.evalₐ I n).toRingHom := (rfl)

/-- The classifying maps of a compatible system are compatible ring homomorphisms. -/
private theorem classifyingMap_compatible (F : FormalGroupAdicSystem I)
    {m n : ℕ} (h : m ≤ n) :
    (Ideal.Quotient.factorPow I h).comp (LazardRing.lift ⟨F.formalGroup n, inferInstance⟩) =
      LazardRing.lift ⟨F.formalGroup m, inferInstance⟩ := by
  rw [← LazardRing.lift_map]
  exact congrArg LazardRing.lift (Subtype.ext (F.map_eq h))

/-- The commutative formal group law over the completion realizing a compatible system. -/
def limit (F : FormalGroupAdicSystem I) : FormalGroup (AdicCompletion I R) :=
  LazardRing.formalGroup.map (AdicCompletion.liftRingHom I
    (fun n ↦ LazardRing.lift ⟨F.formalGroup n, inferInstance⟩)
    (fun h ↦ F.classifyingMap_compatible h))

/-- The inverse-limit law is commutative. -/
instance (F : FormalGroupAdicSystem I) : F.limit.IsComm :=
  inferInstanceAs (LazardRing.formalGroup.map _).IsComm

/-- The inverse-limit law has precisely the prescribed reduction at every power. -/
@[simp]
theorem map_limit (F : FormalGroupAdicSystem I) (n : ℕ) :
    F.limit.map (AdicCompletion.evalₐ I n) = F.formalGroup n := by
  rw [limit, FormalGroup.map_comp]
  have h := AdicCompletion.evalₐ_comp_liftRingHom I
    (fun n ↦ LazardRing.lift ⟨F.formalGroup n, inferInstance⟩)
    (fun h ↦ F.classifyingMap_compatible h) n
  exact (congrArg (LazardRing.formalGroup.map) h).trans (LazardRing.map_lift _)

/-- Reducing the inverse-limit law recovers the original system. -/
@[simp]
theorem ofCompletion_limit (F : FormalGroupAdicSystem I) : ofCompletion I F.limit = F := by
  apply ext
  intro n
  exact F.map_limit n

/-- The inverse limit of the reductions of a law over the completion is that law. -/
@[simp]
theorem limit_ofCompletion (F : FormalGroup (AdicCompletion I R)) [F.IsComm] :
    (ofCompletion I F).limit = F :=
  FormalGroup.ext_adicCompletion fun n ↦ (ofCompletion I F).map_limit n

/-- Commutative laws over the adic completion are equivalent to compatible systems of
commutative laws over the quotient rings. -/
def completionEquiv (I : Ideal R) :
    {F : FormalGroup (AdicCompletion I R) // F.IsComm} ≃ FormalGroupAdicSystem I where
  toFun F := have := F.2; ofCompletion I F.1
  invFun F := ⟨F.limit, inferInstance⟩
  left_inv F := by
    have := F.2
    exact Subtype.ext (limit_ofCompletion F.1)
  right_inv := ofCompletion_limit

/-- The equivalence to systems reduces coefficients at each power. -/
@[simp]
theorem formalGroup_completionEquiv (I : Ideal R)
    (F : {F : FormalGroup (AdicCompletion I R) // F.IsComm}) (n : ℕ) :
    (completionEquiv I F).formalGroup n = F.1.map (AdicCompletion.evalₐ I n).toRingHom := (rfl)

/-- The inverse of the equivalence is the inverse-limit law. -/
@[simp]
theorem completionEquiv_symm_coe (F : FormalGroupAdicSystem I) :
    ((completionEquiv I).symm F).1 = F.limit := (rfl)

section BaseChange

variable {S T : Type*} [CommRing S] [CommRing T] {J : Ideal S} {K : Ideal T}

/-- Extend coefficients in a system along a ring homomorphism carrying `I` into `J`. -/
def map (F : FormalGroupAdicSystem I) (f : R →+* S) (hf : I ≤ J.comap f) :
    FormalGroupAdicSystem J where
  formalGroup n := (F.formalGroup n).map (Ideal.quotientMap (J ^ n) f
    ((Ideal.pow_right_mono hf n).trans (Ideal.le_comap_pow _ n)))
  isComm _ := inferInstance
  map_eq h := by
    rw [FormalGroup.map_comp, ← F.map_eq h, FormalGroup.map_comp]
    congr 1
    apply Ideal.Quotient.ringHom_ext
    ext x
    simp

/-- Base change of a system acts levelwise on coefficients. -/
@[simp]
theorem formalGroup_map (F : FormalGroupAdicSystem I) (f : R →+* S)
    (hf : I ≤ J.comap f) (n : ℕ) :
    (F.map f hf).formalGroup n = (F.formalGroup n).map (Ideal.quotientMap (J ^ n) f
      ((Ideal.pow_right_mono hf n).trans (Ideal.le_comap_pow _ n))) := (rfl)

/-- Extending coefficients by the identity does not change a system. -/
@[simp]
theorem map_id (F : FormalGroupAdicSystem I) :
    F.map (RingHom.id R) (J := I) (by simp) = F := by
  apply ext
  intro n
  rw [formalGroup_map, ← FormalGroup.map_id (F.formalGroup n)]
  congr 1
  apply Ideal.Quotient.ringHom_ext
  ext x
  simp

/-- Successive coefficient extensions of systems agree with their composite. -/
@[simp]
theorem map_comp (F : FormalGroupAdicSystem I) (f : R →+* S) (hf : I ≤ J.comap f)
    (g : S →+* T) (hg : J ≤ K.comap g) :
    (F.map f hf).map g hg = F.map (g.comp f) (hf.trans (Ideal.comap_mono hg)) := by
  apply ext
  intro n
  simp only [formalGroup_map, FormalGroup.map_comp]
  congr 1
  apply Ideal.Quotient.ringHom_ext
  ext x
  simp

/-- Taking inverse limits commutes with coefficient extension to adic completions. -/
theorem limit_map (F : FormalGroupAdicSystem I) (f : R →+* S) (hf : I ≤ J.comap f) :
    (F.map f hf).limit =
      F.limit.map (AdicCompletion.mapₐ f.toIntAlgHom
        (by simpa only [Ideal.comap, RingHom.toIntAlgHom_coe] using hf)).toRingHom := by
  apply FormalGroup.ext_adicCompletion
  intro n
  simp only [AlgHom.toRingHom_eq_coe]
  rw [map_limit, formalGroup_map, FormalGroup.map_comp]
  have h : (AdicCompletion.evalₐ J n).toRingHom.comp
      (AdicCompletion.mapₐ f.toIntAlgHom
        (by simpa only [Ideal.comap, RingHom.toIntAlgHom_coe] using hf)).toRingHom =
      (Ideal.quotientMap (J ^ n) f
        ((Ideal.pow_right_mono hf n).trans (Ideal.le_comap_pow _ n))).comp
        (AdicCompletion.evalₐ I n).toRingHom := by
    ext x
    exact AdicCompletion.evalₐ_mapₐ f.toIntAlgHom
      (by simpa only [Ideal.comap, RingHom.toIntAlgHom_coe] using hf) n x
  simp only [AlgHom.toRingHom_eq_coe] at h
  rw [h, ← FormalGroup.map_comp, map_limit]

end BaseChange

section Complete

variable [IsAdicComplete I R]

/-- Realize a compatible system over an adically complete coefficient ring itself. -/
def realize (F : FormalGroupAdicSystem I) : FormalGroup R :=
  F.limit.map (AdicCompletion.ofAlgEquiv I).symm.toRingHom

/-- The realization is commutative. -/
instance (F : FormalGroupAdicSystem I) : F.realize.IsComm :=
  inferInstanceAs (F.limit.map _).IsComm

/-- Reduction of the realization gives the specified law. -/
@[simp]
theorem map_realize (F : FormalGroupAdicSystem I) (n : ℕ) :
    F.realize.map (Ideal.Quotient.mk (I ^ n)) = F.formalGroup n := by
  rw [realize, FormalGroup.map_comp]
  convert F.map_limit n using 2
  ext x
  exact AdicCompletion.mk_ofAlgEquiv_symm I n x

/-- Realization over complete coefficient rings commutes with coefficient extension. -/
theorem realize_map {S : Type*} [CommRing S] {J : Ideal S} [IsAdicComplete J S]
    (F : FormalGroupAdicSystem I) (f : R →+* S) (hf : I ≤ J.comap f) :
    (F.map f hf).realize = F.realize.map f := by
  apply FormalGroup.ext_adic (I := J)
  intro n
  rw [map_realize, formalGroup_map, FormalGroup.map_comp]
  rw [← Ideal.quotientMap_comp_mk
    ((Ideal.pow_right_mono hf n).trans (Ideal.le_comap_pow _ n)),
    ← FormalGroup.map_comp, map_realize]

/-- Over a complete coefficient ring, compatible quotient laws have a unique realization. -/
theorem existsUnique_realization (F : FormalGroupAdicSystem I) :
    ∃! G : FormalGroup R, ∀ n, G.map (Ideal.Quotient.mk (I ^ n)) = F.formalGroup n := by
  refine ⟨F.realize, F.map_realize, fun G hG ↦ FormalGroup.ext_adic (I := I) fun n ↦ ?_⟩
  rw [hG n, F.map_realize]

/-- Over an adically complete ring, commutative laws are equivalent to compatible systems
of commutative quotient laws. -/
def completeEquiv (I : Ideal R) [IsAdicComplete I R] :
    {F : FormalGroup R // F.IsComm} ≃ FormalGroupAdicSystem I where
  toFun F := have := F.2; ofCompletion I
    (F.1.map (algebraMap R (AdicCompletion I R)))
  invFun F := ⟨F.realize, inferInstance⟩
  left_inv F := Subtype.ext (FormalGroup.ext_adic (I := I) fun n ↦ by
    rw [map_realize, formalGroup_ofCompletion, FormalGroup.map_comp]
    exact congrArg F.1.map (RingHom.ext fun x ↦ AdicCompletion.evalₐ_of I n x))
  right_inv F := by
    apply ext
    intro n
    rw [formalGroup_ofCompletion, FormalGroup.map_comp]
    have h : (AdicCompletion.evalₐ I n).toRingHom.comp
        (algebraMap R (AdicCompletion I R)) = Ideal.Quotient.mk (I ^ n) := by
      ext x
      exact AdicCompletion.evalₐ_of I n x
    rw [h, map_realize]

/-- The complete-ring equivalence sends a law to its coefficient reductions. -/
@[simp]
theorem formalGroup_completeEquiv (I : Ideal R) [IsAdicComplete I R]
    (F : {F : FormalGroup R // F.IsComm}) (n : ℕ) :
    (completeEquiv I F).formalGroup n = F.1.map (Ideal.Quotient.mk (I ^ n)) := by
  simp [completeEquiv, FormalGroup.map_comp]

/-- The inverse complete-ring equivalence realizes the compatible system. -/
@[simp]
theorem completeEquiv_symm_coe (F : FormalGroupAdicSystem I) :
    ((completeEquiv I).symm F).1 = F.realize := (rfl)

end Complete

end FormalGroupAdicSystem

end TauCeti
