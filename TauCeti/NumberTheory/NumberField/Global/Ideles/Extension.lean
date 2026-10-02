/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.NumberField.Global.Adeles.Extension
public import TauCeti.NumberTheory.NumberField.Global.Ideles.Norm.One
public import TauCeti.NumberTheory.NumberField.Global.Places.Extension
public import TauCeti.NumberTheory.NumberField.LocalGlobal.Norm

/-!
# Extension of ideles and its global norm

Extension of adeles induces a continuous homomorphism on units, with the units topology,
and carries principal ideles to principal ideles. It therefore descends to idele classes.
Both maps compose in towers and raise the global norm to the field degree. This is extension
of scalars, not the norm map in the opposite direction.

The norm formula combines the local degree formulas for finite and infinite completions,
regrouping the local factors by the place below. In particular, a complex place above a real
place contributes degree two. No Galois hypothesis is used.

## References

* [J. Neukirch, *Algebraic Number Theory*][Neukirch1992], Chapter VI, §1.
-/

public section
noncomputable section

open IsDedekindDomain NumberField
open scoped NumberField.LiesOver AdicCompletionExtension

namespace TauCeti.GlobalNumberFields

variable (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

/-- Extension of ideles along a number-field extension, induced by extension of adeles. -/
def ideleExtension : IdeleGroup (𝓞 K) K →* IdeleGroup (𝓞 L) L :=
  Units.map (NumberField.adeleExtension (𝓞 K) K (𝓞 L) L).toMonoidHom

/-- The underlying adele of the extended idele is the extended adele. -/
@[simp]
theorem coe_ideleExtension (x : IdeleGroup (𝓞 K) K) :
    (ideleExtension K L x : AdeleRing (𝓞 L) L) =
      NumberField.adeleExtension (𝓞 K) K (𝓞 L) L x :=
  (rfl)

/-- Extension is continuous for the units topology on ideles. -/
@[continuity, fun_prop]
theorem continuous_ideleExtension : Continuous (ideleExtension K L) :=
  (NumberField.continuous_adeleExtension (𝓞 K) K (𝓞 L) L).units_map _

/-- Extension carries a principal idele to the principal idele of the same element in `L`. -/
@[simp]
theorem ideleExtension_unitEmbedding (x : Kˣ) :
    ideleExtension K L (IdeleGroup.unitEmbedding (𝓞 K) K x) =
      IdeleGroup.unitEmbedding (𝓞 L) L (Units.map (algebraMap K L).toMonoidHom x) := by
  apply Units.ext
  simp

/-- Extension of ideles along the identity extension is the identity. -/
@[simp]
theorem ideleExtension_self : ideleExtension K K = MonoidHom.id _ := by
  apply MonoidHom.ext
  intro x
  apply Units.ext
  rw [coe_ideleExtension, MonoidHom.id_apply]
  -- Match the ring-of-integers algebra used by `ideleExtension` to avoid the self-algebra diamond.
  let : Algebra (𝓞 K) (𝓞 K) := NumberField.inst_ringOfIntegersAlgebra K K
  exact RingHom.congr_fun (NumberField.adeleExtension_self (𝓞 K) K) _

/-- Extension of ideles composes in a tower. -/
@[simp]
theorem ideleExtension_comp (M : Type*) [Field M] [NumberField M] [Algebra L M]
    [Algebra K M] [IsScalarTower K L M] :
    (ideleExtension L M).comp (ideleExtension K L) = ideleExtension K M := by
  unfold ideleExtension
  rw [← Units.map_comp]
  exact congrArg (fun f ↦ Units.map f.toMonoidHom)
    (NumberField.adeleExtension_comp (𝓞 K) K (𝓞 L) L (𝓞 M) M)

/-- The infinite coordinate of an extended idele is the image of the source coordinate at the
place below under the completion map. -/
@[simp]
theorem ideleInfiniteCoord_ideleExtension (w : InfinitePlace L) (x : IdeleGroup (𝓞 K) K) :
    w.ideleInfiniteCoord (ideleExtension K L x) =
      Units.map (LiesOver.completionMap (v := w.comap (algebraMap K L)) (w := w)).toMonoidHom
        ((w.comap (algebraMap K L)).ideleInfiniteCoord x) := by
  apply Units.ext
  simp only [InfinitePlace.coe_ideleInfiniteCoord, coe_ideleExtension,
    NumberField.adeleExtension_fst, NumberField.infiniteAdeleExtension_apply, Units.coe_map,
    RingHom.toMonoidHom_eq_coe, MonoidHom.coe_ofClass]

/-- The finite coordinate of an extended idele is the image of the source coordinate at the
place below under the adic completion extension. -/
@[simp]
theorem ideleFiniteCoord_ideleExtension (w : HeightOneSpectrum (𝓞 L))
    (x : IdeleGroup (𝓞 K) K) :
    w.ideleFiniteCoord (ideleExtension K L x) =
      Units.map (HeightOneSpectrum.adicCompletionExtension K L (w.under (𝓞 K)) w).toMonoidHom
        ((w.under (𝓞 K)).ideleFiniteCoord x) := by
  apply Units.ext
  simp only [HeightOneSpectrum.coe_ideleFiniteCoord, coe_ideleExtension,
    NumberField.adeleExtension_snd, finiteAdeleExtension_apply, Units.coe_map,
    RingHom.toMonoidHom_eq_coe, MonoidHom.coe_ofClass]

variable {K L}

private theorem prod_infiniteFactors_ideleExtension (x : IdeleGroup (𝓞 K) K) :
    (∏ w, infiniteCompletionNormalizedAbsValue w (w.ideleInfiniteCoord (ideleExtension K L x))) =
      (∏ v, infiniteCompletionNormalizedAbsValue v (v.ideleInfiniteCoord x)) ^
        Module.finrank K L := by
  classical
  rw [← Fintype.prod_fiberwise (fun w : InfinitePlace L ↦ w.comap (algebraMap K L))]
  have h (v : InfinitePlace K) :
      (∏ w : {w : InfinitePlace L // w.comap (algebraMap K L) = v},
        infiniteCompletionNormalizedAbsValue w.1
          (w.1.ideleInfiniteCoord (ideleExtension K L x))) =
        infiniteCompletionNormalizedAbsValue v (v.ideleInfiniteCoord x) ^
          Module.finrank K L := by
    let e : {w : InfinitePlace L // w.comap (algebraMap K L) = v} ≃
        {w : InfinitePlace L // w.LiesOver v} := Equiv.subtypeEquivRight fun w ↦
      ⟨fun hw ↦ hw ▸ inferInstance, fun _ ↦ InfinitePlace.LiesOver.comap_eq w v⟩
    rw [← prod_infiniteCompletionNormalizedAbsValue_completionMap v (v.ideleInfiniteCoord x)]
    apply Fintype.prod_equiv e
    rintro ⟨w, hw⟩
    simp only [e, Equiv.subtypeEquivRight_apply]
    have hw' : w.comap (algebraMap K L) = v := hw
    subst v
    rw [ideleInfiniteCoord_ideleExtension, Units.coe_map,
      RingHom.toMonoidHom_eq_coe, MonoidHom.coe_ofClass]
    -- The subtype equivalence preserves the place; its lies-over witnesses are proof-irrelevant.
    rfl
  simp_rw [h]
  exact Finset.prod_pow _ _ _

private theorem prod_finiteFactors_ideleExtension (x : IdeleGroup (𝓞 K) K) :
    (∏ᶠ w : HeightOneSpectrum (𝓞 L),
        ‖(w.ideleFiniteCoord (ideleExtension K L x) : w.adicCompletion L)‖) =
      (∏ᶠ v : HeightOneSpectrum (𝓞 K), ‖(v.ideleFiniteCoord x : v.adicCompletion K)‖) ^
        Module.finrank K L := by
  classical
  rw [← TauCeti.finprod_fiberwise (HeightOneSpectrum.under (𝓞 K)) _
    (hasFiniteMulSupport_norm_ideleFiniteCoord (ideleExtension K L x))]
  have h (v : HeightOneSpectrum (𝓞 K)) :
      (∏ᶠ w : {w : HeightOneSpectrum (𝓞 L) // w.under (𝓞 K) = v},
        ‖(w.1.ideleFiniteCoord (ideleExtension K L x) : w.1.adicCompletion L)‖) =
        ‖(v.ideleFiniteCoord x : v.adicCompletion K)‖ ^ Module.finrank K L := by
    let e : {w : HeightOneSpectrum (𝓞 L) // w.under (𝓞 K) = v} ≃
        {w : HeightOneSpectrum (𝓞 L) // w.asIdeal.LiesOver v.asIdeal} :=
      Equiv.subtypeEquivRight fun w ↦
        ⟨fun hw ↦ hw ▸ inferInstance,
          fun hw ↦ HeightOneSpectrum.asIdeal_injective hw.over.symm⟩
    let _ : Fintype {w : HeightOneSpectrum (𝓞 L) // w.asIdeal.LiesOver v.asIdeal} :=
      Fintype.ofFinite _
    rw [← TauCeti.prod_norm_adicCompletionExtension_eq_norm_pow L v (v.ideleFiniteCoord x),
      ← finprod_eq_prod_of_fintype]
    rw [← finprod_comp_equiv e]
    apply finprod_congr
    rintro ⟨w, hw⟩
    have hw' : w.under (𝓞 K) = v := hw
    subst v
    simp [e, HeightOneSpectrum.coe_ideleFiniteCoord]
  simp_rw [h]
  exact (finprod_pow (hasFiniteMulSupport_norm_ideleFiniteCoord x) _).symm

/-- Extension of ideles raises the global norm to the field degree. -/
@[simp]
theorem ideleNorm_ideleExtension (x : IdeleGroup (𝓞 K) K) :
    ideleNorm (ideleExtension K L x) = ideleNorm x ^ Module.finrank K L := by
  apply Units.ext
  apply NNReal.eq
  simp only [Units.val_pow_eq_pow_val, NNReal.coe_pow, coe_ideleNorm]
  rw [prod_infiniteFactors_ideleExtension, prod_finiteFactors_ideleExtension, mul_pow]

variable (K L)

/-- Extension sends the principal subgroup into the principal subgroup. -/
theorem principalSubgroup_le_comap_ideleExtension :
    IdeleGroup.principalSubgroup (𝓞 K) K ≤
      (IdeleGroup.principalSubgroup (𝓞 L) L).comap (ideleExtension K L) := by
  rintro _ ⟨x, rfl⟩
  exact ⟨Units.map (algebraMap K L).toMonoidHom x, (ideleExtension_unitEmbedding K L x).symm⟩

/-- The map on idele classes induced by extension of ideles. -/
def ideleClassExtension : IdeleClassGroup (𝓞 K) K →* IdeleClassGroup (𝓞 L) L :=
  QuotientGroup.map _ _ (ideleExtension K L) (principalSubgroup_le_comap_ideleExtension K L)

/-- On an idele class, extension is represented by the extended idele. -/
@[simp]
theorem ideleClassExtension_mk (x : IdeleGroup (𝓞 K) K) :
    ideleClassExtension K L (x : IdeleClassGroup (𝓞 K) K) =
      (ideleExtension K L x : IdeleClassGroup (𝓞 L) L) :=
  (rfl)

/-- The extension map on idele classes is continuous. -/
@[continuity, fun_prop]
theorem continuous_ideleClassExtension : Continuous (ideleClassExtension K L) :=
  (QuotientGroup.isQuotientMap_mk _).continuous_iff.mpr
    (continuous_quot_mk.comp (continuous_ideleExtension K L))

/-- Extension of idele classes along the identity extension is the identity. -/
@[simp]
theorem ideleClassExtension_self : ideleClassExtension K K = MonoidHom.id _ := by
  unfold ideleClassExtension
  simp only [ideleExtension_self, QuotientGroup.map_id]

/-- Extension of idele classes composes in a tower. -/
@[simp]
theorem ideleClassExtension_comp (M : Type*) [Field M] [NumberField M] [Algebra L M]
    [Algebra K M] [IsScalarTower K L M] :
    (ideleClassExtension L M).comp (ideleClassExtension K L) = ideleClassExtension K M := by
  unfold ideleClassExtension
  simpa only [ideleExtension_comp] using
    QuotientGroup.map_comp_map (IdeleGroup.principalSubgroup (𝓞 K) K)
      (IdeleGroup.principalSubgroup (𝓞 L) L) (IdeleGroup.principalSubgroup (𝓞 M) M)
      (ideleExtension K L) (ideleExtension L M)
      (principalSubgroup_le_comap_ideleExtension K L)
      (principalSubgroup_le_comap_ideleExtension L M)

variable {K L}

/-- Extension of idele classes raises the class norm to the field degree. -/
@[simp]
theorem ideleClassNorm_ideleClassExtension (x : IdeleClassGroup (𝓞 K) K) :
    ideleClassNorm (ideleClassExtension K L x) = ideleClassNorm x ^ Module.finrank K L := by
  induction x using Quotient.inductionOn with
  | h x => simp

end TauCeti.GlobalNumberFields
