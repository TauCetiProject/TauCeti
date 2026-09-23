/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.NumberField.Global.Adeles.Away
public import TauCeti.NumberTheory.NumberField.Global.Approximation.Weak
public import TauCeti.NumberTheory.NumberField.Global.Ideles.FiniteIdeal
public import TauCeti.NumberTheory.NumberField.Global.Ideles.Ray.Subgroup
public import TauCeti.NumberTheory.NumberField.Global.RayClass.Basic

/-!
# The ray class group as a quotient of the idele class group

Let `K` be a number field and `𝔪` a modulus.  This file constructs the surjective homomorphism
```
rayClassQuotient 𝔪 : IdeleClassGroup (𝓞 K) K →* RayClassGroup 𝔪
```
and identifies its kernel with the ray subgroup `raySubgroup 𝔪`, so that the ray class group is
the quotient of the idele class group by the image of the idele congruence subgroup.

The map is described on the ideles congruent to one modulo `𝔪` (`ideleCongrOneSubgroup 𝔪`): such
an idele is a unit at every finite divisor of `𝔪`, so the fractional ideal of its finite component
is prime to `𝔪`, and the idele is sent to the ray class of that ideal
(`rayClassQuotient_mk_of_mem`).  By weak approximation at the places of `𝔪`, every idele becomes
congruent to one after multiplication by a principal idele
(`exists_unitEmbedding_mul_mem_ideleCongrOneSubgroup`), and a principal idele that is congruent to
one comes from an element of `Kˣ` congruent to one, whose principal ideal lies in the ray.  So the
description determines a well-defined homomorphism on idele classes.

## Main definitions

* `TauCeti.GlobalNumberFields.rayClassQuotient`: the homomorphism from the idele class group onto
  the ray class group of `𝔪`.

## Main results

* `TauCeti.GlobalNumberFields.exists_unitEmbedding_mul_mem_ideleCongrOneSubgroup`: every idele is
  congruent to one modulo `𝔪` after multiplication by a principal idele.
* `TauCeti.GlobalNumberFields.rayClassQuotient_mk_of_mem`: the image of the class of an idele
  congruent to one is the ray class of the fractional ideal of its finite component.
* `TauCeti.GlobalNumberFields.rayClassQuotient_surjective`: the map is surjective.
* `TauCeti.GlobalNumberFields.ker_rayClassQuotient`: its kernel is `raySubgroup 𝔪`.
* `TauCeti.GlobalNumberFields.classMap_comp_rayClassQuotient`: the maps are compatible with the
  transition maps between ray class groups.

## References

* J. Neukirch, *Algebraic Number Theory*, Chapter VI, §1, Proposition 1.9.
-/

public section
noncomputable section

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum IsDedekindDomain.FiniteAdeleRing
  NumberField
open scoped NumberField

namespace TauCeti.GlobalNumberFields

variable {K : Type*} [Field K] [NumberField K] {𝔪 : Modulus K}

/-! ### Representatives congruent to one -/

/-- **Every idele is congruent to one after multiplication by a principal idele.**  This is weak
approximation at the finite divisors and the real places of `𝔪`: an element of `K` close enough to
the inverse of the idele at those places makes the product a principal unit of the prescribed level
at each finite divisor and positive at each selected real place. -/
theorem exists_unitEmbedding_mul_mem_ideleCongrOneSubgroup (𝔪 : Modulus K)
    (x : IdeleGroup (𝓞 K) K) :
    ∃ α : Kˣ, IdeleGroup.unitEmbedding (𝓞 K) K α * x ∈ ideleCongrOneSubgroup 𝔪 := by
  -- The components of `x` at the real places of `𝔪`, read in `ℝ`; they are nonzero.
  set r : 𝔪.infinitePart → ℝ := fun w ↦
    InfinitePlace.Completion.extensionEmbeddingOfIsReal w.1.2
      (w.1.1.ideleInfiniteCoord x : w.1.1.Completion) with hr_def
  have hr (w : 𝔪.infinitePart) : r w ≠ 0 :=
    (map_ne_zero _).mpr (w.1.1.ideleInfiniteCoord x).ne_zero
  -- The open set of targets at the places of `𝔪` for which the product is congruent to one.
  let U : Set ((∀ v : 𝔪.support, v.1.adicCompletion K) × (∀ w : 𝔪.infinitePart, ℝ)) :=
    {p | (∀ v : 𝔪.support, Valued.v (p.1 v * (v.1.ideleFiniteCoord x : v.1.adicCompletion K) - 1)
        ≤ WithZero.exp (-(𝔪.exponent v.1 : ℤ))) ∧ ∀ w : 𝔪.infinitePart, 0 < p.2 w * r w}
  have hU : IsOpen U := by
    simp only [U, Set.ofPred_and, Set.ofPred_forall]
    refine (isOpen_iInter_of_finite fun v ↦ ?_).inter (isOpen_iInter_of_finite fun w ↦ ?_)
    · exact (v.1.isOpen_setOf_valued_le (K := K) WithZero.exp_ne_zero).preimage
        (f := fun p : (∀ v : 𝔪.support, v.1.adicCompletion K) × (∀ w : 𝔪.infinitePart, ℝ) ↦
          p.1 v * (v.1.ideleFiniteCoord x : v.1.adicCompletion K) - 1) (by fun_prop)
    · exact isOpen_lt continuous_const (by fun_prop)
  have hp₀ : ((fun v : 𝔪.support ↦
      (((v.1.ideleFiniteCoord x)⁻¹ : (v.1.adicCompletion K)ˣ) : v.1.adicCompletion K)),
        fun w ↦ (r w)⁻¹) ∈ U :=
    ⟨fun v ↦ by simp only [Units.inv_mul, sub_self, map_zero, zero_le],
      fun w ↦ by simp [inv_mul_cancel₀ (hr w)]⟩
  obtain ⟨α, hαf, hαi⟩ := (denseRange_algebraMap_embedding_of_isReal 𝔪.support
    𝔪.infinitePart).exists_mem_open hU ⟨_, hp₀⟩
  -- An element of `Kˣ` meeting the targets makes the product congruent to one.
  have key (β : Kˣ)
      (hf : ∀ v : 𝔪.support, Valued.v (algebraMap K (v.1.adicCompletion K) (β : K) *
        (v.1.ideleFiniteCoord x : v.1.adicCompletion K) - 1) ≤
          WithZero.exp (-(𝔪.exponent v.1 : ℤ)))
      (hi : ∀ w : 𝔪.infinitePart, 0 < InfinitePlace.embedding_of_isReal w.1.2 (β : K) * r w) :
      IdeleGroup.unitEmbedding (𝓞 K) K β * x ∈ ideleCongrOneSubgroup 𝔪 := by
    refine mem_ideleCongrOneSubgroup_iff.mpr ⟨fun v hv ↦ ?_, fun w hw ↦ ?_⟩
    · rw [map_mul, Units.val_mul, HeightOneSpectrum.ideleFiniteCoord_unitEmbedding,
        Units.coe_map]
      simpa using hf ⟨v, (Modulus.mem_support_iff 𝔪 v).mpr hv⟩
    · rw [map_mul, Units.val_mul, map_mul, InfinitePlace.ideleInfiniteCoord_unitEmbedding]
      simpa [hr_def] using hi ⟨w, hw⟩
  by_cases hα : α = 0
  · -- Then `𝔪` has no finite divisor and no real place, since `0` meets none of the targets.
    subst hα
    refine ⟨1, key 1 (fun v ↦ absurd (𝔪.valued_eq_one_of_valued_sub_one_le
      ((Modulus.mem_support_iff 𝔪 v.1).mp v.2) (hαf v)) ?_) fun w ↦ absurd (hαi w) ?_⟩ <;>
      simp
  · exact ⟨Units.mk0 α hα, key _ hαf hαi⟩

/-! ### The ray class of an idele congruent to one -/

/-- **The fractional ideal of an idele congruent to one is prime to the modulus**: such an idele is
a unit at every finite divisor of `𝔪`. -/
theorem toFractionalIdeal_toFiniteIdele_mem_idealsPrimeTo {x : IdeleGroup (𝓞 K) K}
    (hx : x ∈ ideleCongrOneSubgroup 𝔪) :
    toFractionalIdeal (IdeleGroup.toFiniteIdele (𝓞 K) K x) ∈ idealsPrimeTo 𝔪 :=
  (toFractionalIdeal_mem_idealsAway_iff _ _).mpr fun v hv ↦ by
    rw [adicOrd_eq_zero_iff, IdeleGroup.coe_toFiniteIdele, ← HeightOneSpectrum.coe_ideleFiniteCoord]
    exact ideleCongrOneSubgroup.valued_ideleFiniteCoord_eq_one hx
      ((Modulus.mem_support_iff 𝔪 v).mp hv)

/-- The ray class of an idele congruent to one: the class of the fractional ideal of its finite
component. -/
private def ideleRayClass (𝔪 : Modulus K) : ideleCongrOneSubgroup 𝔪 →* RayClassGroup 𝔪 :=
  (rayClassMk 𝔪).comp <| MonoidHom.codRestrict
    ((toFractionalIdeal.comp (IdeleGroup.toFiniteIdele (𝓞 K) K)).comp
      (ideleCongrOneSubgroup 𝔪).subtype) (idealsPrimeTo 𝔪)
    fun x ↦ toFractionalIdeal_toFiniteIdele_mem_idealsPrimeTo x.2

private theorem ideleRayClass_apply (x : ideleCongrOneSubgroup 𝔪) :
    ideleRayClass 𝔪 x = rayClassMk 𝔪
      ⟨toFractionalIdeal (IdeleGroup.toFiniteIdele (𝓞 K) K x),
        toFractionalIdeal_toFiniteIdele_mem_idealsPrimeTo x.2⟩ :=
  (rfl)

/-- A principal idele congruent to one has trivial ray class: its generator is congruent to one,
so its principal ideal lies in the ray. -/
private theorem ideleRayClass_unitEmbedding (β : Kˣ)
    (hβ : IdeleGroup.unitEmbedding (𝓞 K) K β ∈ ideleCongrOneSubgroup 𝔪) :
    ideleRayClass 𝔪 ⟨_, hβ⟩ = 1 := by
  rw [ideleRayClass_apply, rayClassMk_eq_one_iff, mem_ray_iff]
  exact ⟨β, unitEmbedding_mem_ideleCongrOneSubgroup_iff.mp hβ, by simp⟩

/-- Two representatives of one idele class that are both congruent to one have the same ray
class. -/
private theorem ideleRayClass_eq {x : IdeleGroup (𝓞 K) K} (α β : Kˣ)
    (hα : IdeleGroup.unitEmbedding (𝓞 K) K α * x ∈ ideleCongrOneSubgroup 𝔪)
    (hβ : IdeleGroup.unitEmbedding (𝓞 K) K β * x ∈ ideleCongrOneSubgroup 𝔪) :
    ideleRayClass 𝔪 ⟨_, hα⟩ = ideleRayClass 𝔪 ⟨_, hβ⟩ := by
  have hγ : IdeleGroup.unitEmbedding (𝓞 K) K (α * β⁻¹) ∈ ideleCongrOneSubgroup 𝔪 := by
    convert (ideleCongrOneSubgroup 𝔪).mul_mem hα ((ideleCongrOneSubgroup 𝔪).inv_mem hβ) using 1
    rw [map_mul, map_inv]
    group
  have hsplit : (⟨_, hα⟩ : ideleCongrOneSubgroup 𝔪) = ⟨_, hγ⟩ * ⟨_, hβ⟩ :=
    Subtype.ext (by simp only [Subgroup.coe_mul, map_mul, map_inv]; group)
  rw [hsplit, map_mul, ideleRayClass_unitEmbedding, one_mul]

/-- The ray class of an idele, computed on a representative congruent to one. -/
private def ideleToRayClassFun (𝔪 : Modulus K) (x : IdeleGroup (𝓞 K) K) : RayClassGroup 𝔪 :=
  ideleRayClass 𝔪 ⟨_, (exists_unitEmbedding_mul_mem_ideleCongrOneSubgroup 𝔪 x).choose_spec⟩

private theorem ideleToRayClassFun_eq {x : IdeleGroup (𝓞 K) K} (α : Kˣ)
    (hα : IdeleGroup.unitEmbedding (𝓞 K) K α * x ∈ ideleCongrOneSubgroup 𝔪) :
    ideleToRayClassFun 𝔪 x = ideleRayClass 𝔪 ⟨_, hα⟩ :=
  ideleRayClass_eq _ _ _ hα

/-- The ray class of an idele, as a homomorphism on the idele group. -/
private def ideleToRayClass (𝔪 : Modulus K) : IdeleGroup (𝓞 K) K →* RayClassGroup 𝔪 where
  toFun := ideleToRayClassFun 𝔪
  map_one' := by
    rw [ideleToRayClassFun_eq 1 (by simp)]
    exact (congrArg (ideleRayClass 𝔪) (Subtype.ext (by simp))).trans (map_one _)
  map_mul' x y := by
    obtain ⟨α, hα⟩ := exists_unitEmbedding_mul_mem_ideleCongrOneSubgroup 𝔪 x
    obtain ⟨β, hβ⟩ := exists_unitEmbedding_mul_mem_ideleCongrOneSubgroup 𝔪 y
    have hmul : IdeleGroup.unitEmbedding (𝓞 K) K (α * β) * (x * y) =
        IdeleGroup.unitEmbedding (𝓞 K) K α * x * (IdeleGroup.unitEmbedding (𝓞 K) K β * y) := by
      rw [map_mul, mul_mul_mul_comm]
    have hαβ : IdeleGroup.unitEmbedding (𝓞 K) K (α * β) * (x * y) ∈ ideleCongrOneSubgroup 𝔪 :=
      hmul ▸ (ideleCongrOneSubgroup 𝔪).mul_mem hα hβ
    rw [ideleToRayClassFun_eq _ hαβ, ideleToRayClassFun_eq _ hα, ideleToRayClassFun_eq _ hβ,
      ← map_mul]
    exact congrArg (ideleRayClass 𝔪) (Subtype.ext hmul)

private theorem ideleToRayClass_apply (x : IdeleGroup (𝓞 K) K) :
    ideleToRayClass 𝔪 x = ideleToRayClassFun 𝔪 x :=
  (rfl)

/-! ### The ray class of an idele class -/

/-- **The ray class of an idele class.**  The class of an idele `x` is sent to the ray class of the
fractional ideal of the finite component of `α x`, for any `α ∈ Kˣ` making `α x` congruent to one
modulo `𝔪`; the result does not depend on the choice of `α`. -/
def rayClassQuotient (𝔪 : Modulus K) : IdeleClassGroup (𝓞 K) K →* RayClassGroup 𝔪 :=
  QuotientGroup.lift _ (ideleToRayClass 𝔪) <| by
    rintro _ ⟨β, rfl⟩
    rw [MonoidHom.mem_ker, ideleToRayClass_apply,
      ideleToRayClassFun_eq β⁻¹ (by simp)]
    exact (congrArg (ideleRayClass 𝔪) (Subtype.ext (by simp))).trans (map_one _)

/-- **The ray class of the class of an idele congruent to one** is the ray class of the fractional
ideal of its finite component. -/
theorem rayClassQuotient_mk_of_mem {x : IdeleGroup (𝓞 K) K} (hx : x ∈ ideleCongrOneSubgroup 𝔪) :
    rayClassQuotient 𝔪 x = rayClassMk 𝔪
      ⟨toFractionalIdeal (IdeleGroup.toFiniteIdele (𝓞 K) K x),
        toFractionalIdeal_toFiniteIdele_mem_idealsPrimeTo hx⟩ := by
  rw [rayClassQuotient, QuotientGroup.lift_mk, ideleToRayClass_apply,
    ideleToRayClassFun_eq 1 (by simpa using hx), ideleRayClass_apply]
  simp_rw [map_one, one_mul]

/-- The class of an idele is the class of its product with a principal idele. -/
private theorem mk_eq_mk_unitEmbedding_mul (x : IdeleGroup (𝓞 K) K) (α : Kˣ) :
    (x : IdeleClassGroup (𝓞 K) K) =
      (IdeleGroup.unitEmbedding (𝓞 K) K α * x : IdeleGroup (𝓞 K) K) := by
  rw [mul_comm, QuotientGroup.mk_mul_of_mem x (MonoidHom.mem_range.mpr ⟨α, rfl⟩)]

/-- **The ray class map is surjective.**  An invertible fractional ideal prime to `𝔪` is the ideal
of a finite idele that is a unit at every finite divisor of `𝔪`; replacing its components there by
`1`, and taking `1` at every infinite place, gives an idele congruent to one with the same ideal. -/
theorem rayClassQuotient_surjective (𝔪 : Modulus K) :
    Function.Surjective (rayClassQuotient 𝔪) := by
  classical
  intro c
  obtain ⟨I, rfl⟩ := rayClassMk_surjective 𝔪 c
  obtain ⟨⟨a, ha⟩, rfl⟩ := toIdealsAway_surjective 𝔪.support I
  -- The idele with finite component `a` and trivial infinite components.
  set x := IdeleGroup.ofFiniteIdele (𝓞 K) K a with hx_def
  -- The correction at the finite divisors of `𝔪`, and the corrected idele.
  set z : IdeleGroup (𝓞 K) K :=
    ∏ v ∈ 𝔪.support, IdeleGroup.ofAdicCompletion (𝓞 K) K v (v.ideleFiniteCoord x)⁻¹ with hz_def
  have hzf (v : HeightOneSpectrum (𝓞 K)) :
      v.ideleFiniteCoord z = if v ∈ 𝔪.support then (v.ideleFiniteCoord x)⁻¹ else 1 :=
    v.ideleFiniteCoord_prod_ofAdicCompletion 𝔪.support _
  have hzi (w : InfinitePlace K) : w.ideleInfiniteCoord z = 1 := by
    simp [hz_def, map_prod]
  have hmem : x * z ∈ ideleCongrOneSubgroup 𝔪 := by
    refine mem_ideleCongrOneSubgroup_iff.mpr ⟨fun v hv ↦ ?_, fun w _ ↦ ?_⟩
    · rw [map_mul, hzf, ite_eq_left ((Modulus.mem_support_iff 𝔪 v).mpr hv), mul_inv_cancel]
      simp
    · simp [hx_def, hzi]
  -- The correction is a unit at every finite place, so it does not change the ideal.
  have hz : toFractionalIdeal (IdeleGroup.toFiniteIdele (𝓞 K) K z) = 1 := by
    refine toFractionalIdeal_toFiniteIdele_eq_one_iff.mpr fun v ↦ ?_
    rw [hzf]
    split_ifs with hv
    · rw [Units.val_inv_eq_inv_val, map_inv₀, inv_eq_one, HeightOneSpectrum.coe_ideleFiniteCoord,
        ← IdeleGroup.coe_toFiniteIdele, hx_def, IdeleGroup.toFiniteIdele_ofFiniteIdele]
      exact adicOrd_eq_zero_iff.mp ((mem_adicOrdAway_iff _ a).mp ha v hv)
    · simp
  refine ⟨x * z, (rayClassQuotient_mk_of_mem hmem).trans (congrArg _ (Subtype.ext ?_))⟩
  rw [Subgroup.coe_mk, toIdealsAway_apply, map_mul, map_mul, hz, mul_one, hx_def,
    IdeleGroup.toFiniteIdele_ofFiniteIdele]

/-- The class of an idele congruent to one has trivial ray class exactly when it lies in the ray
subgroup: its ideal is generated by an element congruent to one exactly when dividing by that
element leaves an idele congruent to one that is a unit at every finite place. -/
private theorem rayClassQuotient_mk_eq_one_iff_of_mem {y : IdeleGroup (𝓞 K) K}
    (hy : y ∈ ideleCongrOneSubgroup 𝔪) :
    rayClassQuotient 𝔪 y = 1 ↔ (y : IdeleClassGroup (𝓞 K) K) ∈ raySubgroup 𝔪 := by
  rw [rayClassQuotient_mk_of_mem hy, rayClassMk_eq_one_iff, mem_ray_iff]
  dsimp only
  constructor
  · rintro ⟨β, hβ, hβy⟩
    have hβ' : IdeleGroup.unitEmbedding (𝓞 K) K β⁻¹ ∈ ideleCongrOneSubgroup 𝔪 := by
      rw [map_inv]
      exact (ideleCongrOneSubgroup 𝔪).inv_mem (unitEmbedding_mem_ideleCongrOneSubgroup_iff.mpr hβ)
    have hunit : IdeleGroup.unitEmbedding (𝓞 K) K β⁻¹ * y ∈
        ideleCongruenceSubgroup (Modulus.one K) := by
      refine mem_ideleCongruenceSubgroup_one_iff.mpr
        (toFractionalIdeal_toFiniteIdele_eq_one_iff.mp ?_)
      rw [map_mul, map_mul, IdeleGroup.toFiniteIdele_unitEmbedding,
        toFractionalIdeal_unitEmbedding, ← hβy, ← map_mul, inv_mul_cancel, map_one]
    refine mem_raySubgroup_iff.mpr ⟨IdeleGroup.unitEmbedding (𝓞 K) K β⁻¹ * y, ?_, ?_⟩
    · rw [← ideleCongrOneSubgroup_inf_ideleCongruenceSubgroup_one]
      exact ⟨(ideleCongrOneSubgroup 𝔪).mul_mem hβ' hy, hunit⟩
    · rw [QuotientGroup.mk'_apply, ← mk_eq_mk_unitEmbedding_mul]
  · intro hc
    obtain ⟨z, hz, hzy⟩ := mem_raySubgroup_iff.mp hc
    obtain ⟨β, hβ⟩ : z⁻¹ * y ∈ IdeleGroup.principalSubgroup (𝓞 K) K :=
      QuotientGroup.eq.mp hzy
    have hyz : y = z * IdeleGroup.unitEmbedding (𝓞 K) K β := by rw [hβ, mul_inv_cancel_left]
    refine ⟨β, unitEmbedding_mem_ideleCongrOneSubgroup_iff.mp ?_, ?_⟩
    · rw [hβ]
      exact (ideleCongrOneSubgroup 𝔪).mul_mem ((ideleCongrOneSubgroup 𝔪).inv_mem
        (ideleCongruenceSubgroup_le_ideleCongrOneSubgroup 𝔪 hz)) hy
    · have hz1 : toFractionalIdeal (IdeleGroup.toFiniteIdele (𝓞 K) K z) = 1 :=
        toFractionalIdeal_toFiniteIdele_eq_one_iff.mpr
          (ideleCongruenceSubgroup.valued_ideleFiniteCoord_eq_one hz)
      rw [hyz, map_mul, map_mul, hz1, one_mul, IdeleGroup.toFiniteIdele_unitEmbedding,
        toFractionalIdeal_unitEmbedding]

/-- **The kernel of the ray class map is the ray subgroup.**  The ray class of an idele congruent
to one is trivial exactly when its ideal is generated by an element congruent to one; dividing by
that element leaves an idele congruent to one that is a unit at every finite place, that is, an
element of the idele congruence subgroup. -/
theorem ker_rayClassQuotient (𝔪 : Modulus K) : (rayClassQuotient 𝔪).ker = raySubgroup 𝔪 := by
  ext c
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective c
  obtain ⟨α, hα⟩ := exists_unitEmbedding_mul_mem_ideleCongrOneSubgroup 𝔪 x
  rw [mk_eq_mk_unitEmbedding_mul x α, MonoidHom.mem_ker]
  exact rayClassQuotient_mk_eq_one_iff_of_mem hα

/-- **The ray class maps are compatible with the transition maps**: for `𝔪 ∣ 𝔫`, the ray class of
an idele class modulo `𝔫`, carried to the ray class group of `𝔪`, is its ray class modulo `𝔪`. -/
theorem classMap_comp_rayClassQuotient {𝔪 𝔫 : Modulus K} (h : 𝔪 ∣ 𝔫) :
    (classMap h).comp (rayClassQuotient 𝔫) = rayClassQuotient 𝔪 := by
  refine MonoidHom.ext fun c ↦ ?_
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective c
  obtain ⟨α, hα⟩ := exists_unitEmbedding_mul_mem_ideleCongrOneSubgroup 𝔫 x
  rw [mk_eq_mk_unitEmbedding_mul x α, MonoidHom.comp_apply, rayClassQuotient_mk_of_mem hα,
    rayClassQuotient_mk_of_mem (ideleCongrOneSubgroup_antitone h hα), classMap_rayClassMk]
  exact congrArg _ (Subtype.ext (by simp [NumberFieldArithmetic.coe_idealsAwayInclusion]))

/-- **The ray class maps are compatible with the transition maps.** -/
@[simp] theorem classMap_rayClassQuotient {𝔪 𝔫 : Modulus K} (h : 𝔪 ∣ 𝔫)
    (c : IdeleClassGroup (𝓞 K) K) :
    classMap h (rayClassQuotient 𝔫 c) = rayClassQuotient 𝔪 c := by
  rw [← MonoidHom.comp_apply, classMap_comp_rayClassQuotient]

end TauCeti.GlobalNumberFields
