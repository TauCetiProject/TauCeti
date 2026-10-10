/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.NumberField.Global.Adeles.Norm.Continuity
public import TauCeti.NumberTheory.NumberField.Global.Ideles.Extension
public import TauCeti.RingTheory.Norm.Units
public import TauCeti.Topology.Algebra.ContinuousMonoidHom.Basic

/-!
# The norm map of ideles and idele classes

Let `L / K` be an extension of number fields. The norm map of adeles `adeleNorm` is
multiplicative and continuous, so it restricts to a continuous homomorphism of idele groups

`ideleNormMap K L : 𝕀_L →ₜ* 𝕀_K`.

Its coordinate at a place `v` of `K` is the product, over the places `w ∣ v` of `L`, of the local
norms `N_{L_w/K_v}` of the coordinates at `w`. It sends the principal idele of `x ∈ Lˣ` to the
principal idele of `N_{L/K}(x)`, so it descends to a continuous homomorphism of idele class groups

`ideleClassNormMap K L : C_L →ₜ* C_K`.

Composed with extension of ideles from `K` to `L`, both maps are the `[L : K]`-th power map.

This is the norm in the direction `L → K`, opposite to the extension maps `ideleExtension` and
`ideleClassExtension`. It is not to be confused with the absolute idele norm `ideleNorm`, a
homomorphism to `ℝ≥0ˣ`.

## Main definitions

* `TauCeti.GlobalNumberFields.ideleNormMap`: the norm map `𝕀_L →ₜ* 𝕀_K` of idele groups.
* `TauCeti.GlobalNumberFields.ideleClassNormMap`: the induced norm map `C_L →ₜ* C_K` of idele
  class groups.

## Main results

* `TauCeti.GlobalNumberFields.continuous_ideleNormMap`,
  `TauCeti.GlobalNumberFields.continuous_ideleClassNormMap`: the relative norm maps are continuous.
* `TauCeti.GlobalNumberFields.ideleFiniteCoord_ideleNormMap`,
  `TauCeti.GlobalNumberFields.ideleInfiniteCoord_ideleNormMap`: the coordinate of the norm of an
  idele at a place `v` of `K` is the product of the local norms of its coordinates at the places
  above `v`.
* `TauCeti.GlobalNumberFields.ideleNormMap_ofCompletion`,
  `TauCeti.GlobalNumberFields.ideleClassNormMap_ofCompletion`: the norm of an idele, or of an
  idele class, concentrated at one infinite place `w` is concentrated at the place below `w`,
  with the local norm as coordinate.
* `TauCeti.GlobalNumberFields.ideleNormMap_unitEmbedding`: the norm of a principal idele is the
  principal idele of the global norm.
* `TauCeti.GlobalNumberFields.ideleNormMap_ideleExtension`,
  `TauCeti.GlobalNumberFields.ideleClassNormMap_ideleClassExtension`: the norm of an idele, or of
  an idele class, extended from `K` is its `[L : K]`-th power.
* `TauCeti.GlobalNumberFields.ideleNormMap_comp`,
  `TauCeti.GlobalNumberFields.ideleClassNormMap_comp`: norm maps compose in towers.

## References

* [J. Neukirch, *Algebraic Number Theory*][Neukirch1992], Chapter VI, §2.
-/

public section
noncomputable section

open IsDedekindDomain NumberField NumberField.InfinitePlace
open scoped AdicCompletionExtension NumberField.LiesOver

namespace TauCeti.GlobalNumberFields

variable (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

/-- **The norm map of ideles** `N_{L/K} : 𝕀_L →ₜ* 𝕀_K`, the restriction of the multiplicative
norm map of adeles `adeleNorm` to units. -/
def ideleNormMap : IdeleGroup (𝓞 L) L →ₜ* IdeleGroup (𝓞 K) K where
  toMonoidHom := Units.map (adeleNorm K L)
  continuous_toFun := (continuous_adeleNorm K L).units_map _

variable {K L} in
/-- The underlying adele of the norm of an idele is the adele norm of its underlying adele. -/
@[simp]
theorem coe_ideleNormMap (x : IdeleGroup (𝓞 L) L) :
    (ideleNormMap K L x : AdeleRing (𝓞 K) K) = adeleNorm K L x :=
  (rfl)

/-- The relative idele norm is continuous for the units topology, which controls both an
adele and its inverse. -/
@[continuity, fun_prop]
theorem continuous_ideleNormMap : Continuous (ideleNormMap K L) :=
  (ideleNormMap K L).continuous

variable {K L} in
/-- **The finite coordinates of the idele norm.** The coordinate of `N_{L/K}(x)` at a finite place
`v` of `K` is the product over the places `w ∣ v` of `N_{L_w/K_v}(x_w)`. -/
@[simp]
theorem ideleFiniteCoord_ideleNormMap (v : HeightOneSpectrum (𝓞 K)) (x : IdeleGroup (𝓞 L) L) :
    v.ideleFiniteCoord (ideleNormMap K L x) =
      ∏ᶠ w : {w : HeightOneSpectrum (𝓞 L) // w.asIdeal.LiesOver v.asIdeal},
        Algebra.normUnits (v.adicCompletion K) (w.1.ideleFiniteCoord x) := by
  apply Units.ext
  rw [← Units.coeHom_apply, ← Units.coeHom_apply, map_finprod _ (Set.toFinite _)]
  simp

variable {K L} in
/-- **The infinite coordinates of the idele norm.** The coordinate of `N_{L/K}(x)` at an infinite
place `v` of `K` is the product over the places `w ∣ v` of `N_{L_w/K_v}(x_w)`. -/
@[simp]
theorem ideleInfiniteCoord_ideleNormMap (v : InfinitePlace K) (x : IdeleGroup (𝓞 L) L) :
    v.ideleInfiniteCoord (ideleNormMap K L x) =
      ∏ᶠ w : {w : InfinitePlace L // w.LiesOver v},
        Algebra.normUnits v.Completion (w.1.ideleInfiniteCoord x) := by
  apply Units.ext
  rw [← Units.coeHom_apply, ← Units.coeHom_apply, map_finprod _ (Set.toFinite _)]
  simp

variable {K L} in
/-- **The norm of an idele concentrated at one infinite place.** If `w` lies over `v`, the norm
of the idele that is `u` at `w` and `1` elsewhere is the idele that is `N_{L_w/K_v}(u)` at `v`
and `1` elsewhere. -/
theorem ideleNormMap_ofCompletion (v : InfinitePlace K) (w : InfinitePlace L) [w.LiesOver v]
    (u : w.Completionˣ) :
    ideleNormMap K L (IdeleGroup.ofCompletion (𝓞 L) L w u) =
      IdeleGroup.ofCompletion (𝓞 K) K v (Algebra.normUnits v.Completion u) := by
  refine IdeleGroup.ext (fun v' ↦ ?_) (fun v' ↦ ?_)
  · rw [ideleInfiniteCoord_ideleNormMap]
    by_cases hv : v' = v
    · subst hv
      rw [InfinitePlace.ideleInfiniteCoord_ofCompletion_self, finprod_eq_single _ ⟨w, ‹_›⟩]
      · rw [InfinitePlace.ideleInfiniteCoord_ofCompletion_self]
      · rintro ⟨w', hw'⟩ hne
        rw [InfinitePlace.ideleInfiniteCoord_ofCompletion_of_ne w' fun h ↦ hne (Subtype.ext h),
          map_one]
    · -- No place above `v'` is `w`, so every factor is trivial.
      rw [InfinitePlace.ideleInfiniteCoord_ofCompletion_of_ne v' hv]
      refine finprod_eq_one_of_forall_eq_one fun w' ↦ ?_
      have hne : w'.1 ≠ w := by
        rintro h
        apply hv
        rw [← LiesOver.comap_eq w'.1 v', ← LiesOver.comap_eq w v, h]
      rw [InfinitePlace.ideleInfiniteCoord_ofCompletion_of_ne w'.1 hne, map_one]
  · simp only [ideleFiniteCoord_ideleNormMap,
      HeightOneSpectrum.ideleFiniteCoord_ofCompletion, map_one, finprod_one]

/-- The norm of a principal idele is the principal idele of the norm of `L / K`. -/
@[simp]
theorem ideleNormMap_unitEmbedding (x : Lˣ) :
    ideleNormMap K L (IdeleGroup.unitEmbedding (𝓞 L) L x) =
      IdeleGroup.unitEmbedding (𝓞 K) K (Algebra.normUnits K x) := by
  apply Units.ext
  simp

/-- The norm of an idele extended from `K` is its `[L : K]`-th power. -/
@[simp]
theorem ideleNormMap_ideleExtension (x : IdeleGroup (𝓞 K) K) :
    ideleNormMap K L (ideleExtension K L x) = x ^ Module.finrank K L := by
  apply Units.ext
  simp

/-- Norm maps of ideles compose in a tower of number fields. -/
@[simp]
theorem ideleNormMap_comp (M : Type*) [Field M] [NumberField M] [Algebra L M]
    [Algebra K M] [IsScalarTower K L M] :
    (ideleNormMap K L).comp (ideleNormMap L M) = ideleNormMap K M := by
  apply ContinuousMonoidHom.ext
  intro x
  apply Units.ext
  simpa only [ContinuousMonoidHom.coe_comp, Function.comp_apply, MonoidHom.comp_apply,
    coe_ideleNormMap] using
    DFunLike.congr_fun (adeleNorm_comp K L M) (x : AdeleRing (𝓞 M) M)

/-- The norm map of ideles sends principal ideles to principal ideles. -/
theorem principalSubgroup_le_comap_ideleNormMap :
    IdeleGroup.principalSubgroup (𝓞 L) L ≤
      (IdeleGroup.principalSubgroup (𝓞 K) K).comap (ideleNormMap K L).toMonoidHom := by
  rintro _ ⟨x, rfl⟩
  exact ⟨Algebra.normUnits K x, (ideleNormMap_unitEmbedding K L x).symm⟩

/-- **The norm map of idele classes** `N_{L/K} : C_L →ₜ* C_K`, induced by the norm map of
ideles. -/
def ideleClassNormMap : IdeleClassGroup (𝓞 L) L →ₜ* IdeleClassGroup (𝓞 K) K :=
  ContinuousMonoidHom.quotientLift (IdeleGroup.principalSubgroup (𝓞 L) L)
    ((ContinuousMonoidHom.quotientMk (IdeleGroup.principalSubgroup (𝓞 K) K)).comp
      (ideleNormMap K L)) (by
        intro x hx
        simpa using principalSubgroup_le_comap_ideleNormMap K L hx)

variable {K L} in
/-- On an idele class, the norm is represented by the norm of a representing idele. -/
@[simp]
theorem ideleClassNormMap_mk (x : IdeleGroup (𝓞 L) L) :
    ideleClassNormMap K L (x : IdeleClassGroup (𝓞 L) L) =
      (ideleNormMap K L x : IdeleClassGroup (𝓞 K) K) := by
  simp [ideleClassNormMap]

variable {K L} in
/-- **The norm of an idele class concentrated at one infinite place.** If `w` lies over `v`, the
norm of the class of the idele that is `u` at `w` is the class of the idele that is
`N_{L_w/K_v}(u)` at `v`. -/
theorem ideleClassNormMap_ofCompletion (v : InfinitePlace K) (w : InfinitePlace L)
    [w.LiesOver v] (u : w.Completionˣ) :
    ideleClassNormMap K L (IdeleClassGroup.ofCompletion (𝓞 L) L w u) =
      IdeleClassGroup.ofCompletion (𝓞 K) K v (Algebra.normUnits v.Completion u) := by
  rw [IdeleClassGroup.ofCompletion_apply, ideleClassNormMap_mk, ideleNormMap_ofCompletion v w,
    ← IdeleClassGroup.ofCompletion_apply]

/-- The idele-class norm group `N_{L/K}(C_L)` is normal in `C_K`, which is commutative, so the
norm quotient `C_K / N_{L/K}(C_L)` is a group. -/
instance normal_range_ideleClassNormMap :
    (ideleClassNormMap K L : IdeleClassGroup (𝓞 L) L →* IdeleClassGroup (𝓞 K) K).range.Normal :=
  ⟨fun n hn g ↦ by rwa [mul_comm g, mul_inv_cancel_right]⟩

/-- The relative norm on idele classes is continuous for the quotient topology. -/
@[continuity, fun_prop]
theorem continuous_ideleClassNormMap : Continuous (ideleClassNormMap K L) :=
  (ideleClassNormMap K L).continuous

/-- The norm of an idele class extended from `K` is its `[L : K]`-th power. -/
@[simp]
theorem ideleClassNormMap_ideleClassExtension (x : IdeleClassGroup (𝓞 K) K) :
    ideleClassNormMap K L (ideleClassExtension K L x) = x ^ Module.finrank K L := by
  induction x using QuotientGroup.induction_on with
  | H x => simp [← QuotientGroup.mk_pow]

/-- Norm maps of idele classes compose in a tower of number fields. -/
@[simp]
theorem ideleClassNormMap_comp (M : Type*) [Field M] [NumberField M] [Algebra L M]
    [Algebra K M] [IsScalarTower K L M] :
    (ideleClassNormMap K L).comp (ideleClassNormMap L M) = ideleClassNormMap K M := by
  apply ContinuousMonoidHom.ext
  intro x
  induction x using QuotientGroup.induction_on with
  | H x =>
    simpa only [ContinuousMonoidHom.coe_comp, Function.comp_apply, ideleClassNormMap_mk] using
      congrArg (fun y : IdeleGroup (𝓞 K) K ↦ (y : IdeleClassGroup (𝓞 K) K))
        (DFunLike.congr_fun (ideleNormMap_comp K L M) x)

end TauCeti.GlobalNumberFields
