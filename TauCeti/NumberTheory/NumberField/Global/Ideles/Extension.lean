/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.NumberField.Global.Adeles.Extension
public import TauCeti.NumberTheory.NumberField.Global.Ideles.Norm.One
public import TauCeti.NumberTheory.NumberField.InfinitePlace.Completion.Extension
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

An idele or idele class concentrated at a single finite or infinite place extends to the product
over the places above it of the single-place elements carrying the images of the local component
(`ideleExtension_ofAdicCompletion`, `ideleClassExtension_ofAdicCompletion`,
`ideleExtension_ofCompletion`, `ideleClassExtension_ofCompletion`).

## References

* [J. Neukirch, *Algebraic Number Theory*][Neukirch1992], Chapter VI, §1.
-/

public section
noncomputable section

open IsDedekindDomain NumberField NumberField.InfinitePlace
open scoped AdicCompletionExtension
attribute [local instance] AbsoluteValue.Completion.algebraOfLiesOver

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
      Units.map (AbsoluteValue.Completion.map (w.comap (algebraMap K L)).val w.val).toMonoidHom
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

/-- Taking the finite component commutes with extension of ideles. -/
@[simp]
theorem toFiniteIdele_ideleExtension (x : IdeleGroup (𝓞 K) K) :
    IdeleGroup.toFiniteIdele (𝓞 L) L (ideleExtension K L x) =
      Units.map (finiteAdeleExtension (𝓞 K) K (𝓞 L) L).toMonoidHom
        (IdeleGroup.toFiniteIdele (𝓞 K) K x) := by
  apply Units.ext
  ext w
  simp [IdeleGroup.coe_toFiniteIdele, ← HeightOneSpectrum.coe_ideleFiniteCoord]

private theorem prod_infiniteFactors_ideleExtension (x : IdeleGroup (𝓞 K) K) :
    (∏ w, completionNormalizedAbsValue w (w.ideleInfiniteCoord (ideleExtension K L x))) =
      (∏ v, completionNormalizedAbsValue v (v.ideleInfiniteCoord x)) ^
        Module.finrank K L := by
  classical
  rw [← Fintype.prod_fiberwise (fun w : InfinitePlace L ↦ w.comap (algebraMap K L))]
  have h (v : InfinitePlace K) :
      (∏ w : {w : InfinitePlace L // w.comap (algebraMap K L) = v},
        completionNormalizedAbsValue w.val
          (w.val.ideleInfiniteCoord (ideleExtension K L x))) =
        completionNormalizedAbsValue v (v.ideleInfiniteCoord x) ^
          Module.finrank K L := by
    let e : {w : InfinitePlace L // w.comap (algebraMap K L) = v} ≃
        {w : InfinitePlace L // w.LiesOver v} := Equiv.subtypeEquivRight fun w ↦
      ⟨fun hw ↦ hw ▸ inferInstance, fun _ ↦ InfinitePlace.LiesOver.comap_eq w v⟩
    rw [← prod_completionNormalizedAbsValue_completionMap v (v.ideleInfiniteCoord x)]
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
        ‖(w.val.ideleFiniteCoord (ideleExtension K L x) : w.val.adicCompletion L)‖) =
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

/-! ### Extension of ideles and idele classes concentrated at a single place -/

variable (K L)

/-- **Extension of an idele concentrated at a finite place.** Extending `ofAdicCompletion v u` from
`K` to `L` decomposes it as the product over the finite places `w` of `L` above `v` of
`ofAdicCompletion w` applied to the image of `u` in `L_wˣ`. -/
theorem ideleExtension_ofAdicCompletion (v : HeightOneSpectrum (𝓞 K))
    (u : (v.adicCompletion K)ˣ) :
    ideleExtension K L (IdeleGroup.ofAdicCompletion (𝓞 K) K v u) =
      ∏ᶠ w : {w : HeightOneSpectrum (𝓞 L) // w.asIdeal.LiesOver v.asIdeal},
        IdeleGroup.ofAdicCompletion (𝓞 L) L w.val
          (Units.map (HeightOneSpectrum.adicCompletionExtension K L v w.val).toMonoidHom u) := by
  classical
  let _ : Fintype {w : HeightOneSpectrum (𝓞 L) // w.asIdeal.LiesOver v.asIdeal} :=
    Fintype.ofFinite _
  rw [finprod_eq_prod_of_fintype]
  refine IdeleGroup.ext (fun w ↦ ?_) (fun w ↦ ?_)
  · simp [ideleInfiniteCoord_ideleExtension, map_prod]
  · rw [ideleFiniteCoord_ideleExtension, map_prod]
    by_cases hw : w.asIdeal.LiesOver v.asIdeal
    · have hv : w.under (𝓞 K) = v := HeightOneSpectrum.asIdeal_injective hw.over.symm
      rw [Finset.prod_eq_single ⟨w, hw⟩
        (fun w' _ hw' ↦ w.ideleFiniteCoord_ofAdicCompletion_of_ne (fun h ↦ hw' (Subtype.ext h.symm))
          _)
        (fun h ↦ (h (Finset.mem_univ _)).elim),
        w.ideleFiniteCoord_ofAdicCompletion_self]
      subst hv
      simp only [HeightOneSpectrum.ideleFiniteCoord_ofAdicCompletion_self]
    · have hne : w.under (𝓞 K) ≠ v := fun h ↦ hw (h ▸ inferInstance)
      rw [HeightOneSpectrum.ideleFiniteCoord_ofAdicCompletion_of_ne _ hne, map_one,
        Finset.prod_eq_one fun w' _ ↦
          w.ideleFiniteCoord_ofAdicCompletion_of_ne (fun h ↦ hw (h ▸ w'.property)) _]

/-- **Extension of an idele class concentrated at a finite place.** Extending
`IdeleClassGroup.ofAdicCompletion v u` from `K` to `L` decomposes it into the product over the
finite places `w` of `L` above `v`. -/
theorem ideleClassExtension_ofAdicCompletion (v : HeightOneSpectrum (𝓞 K))
    (u : (v.adicCompletion K)ˣ) :
    ideleClassExtension K L (IdeleClassGroup.ofAdicCompletion (𝓞 K) K v u) =
      ∏ᶠ w : {w : HeightOneSpectrum (𝓞 L) // w.asIdeal.LiesOver v.asIdeal},
        IdeleClassGroup.ofAdicCompletion (𝓞 L) L w.val
          (Units.map (HeightOneSpectrum.adicCompletionExtension K L v w.val).toMonoidHom u) := by
  classical
  let _ : Fintype {w : HeightOneSpectrum (𝓞 L) // w.asIdeal.LiesOver v.asIdeal} :=
    Fintype.ofFinite _
  rw [IdeleClassGroup.ofAdicCompletion_apply, ideleClassExtension_mk,
    ideleExtension_ofAdicCompletion, finprod_eq_prod_of_fintype, finprod_eq_prod_of_fintype,
    ← QuotientGroup.mk'_apply, map_prod]
  simp only [QuotientGroup.mk'_apply, IdeleClassGroup.ofAdicCompletion_apply]

/-- **Extension of an idele concentrated at an infinite place.** Extending `ofCompletion v u` from
`K` to `L` decomposes it as the product over the infinite places `w` of `L` above `v` of
`ofCompletion w` applied to the image of `u` in `L_wˣ`. -/
theorem ideleExtension_ofCompletion (v : InfinitePlace K) (u : v.Completionˣ) :
    ideleExtension K L (IdeleGroup.ofCompletion (𝓞 K) K v u) =
      ∏ᶠ w : {w : InfinitePlace L // w.LiesOver v},
        IdeleGroup.ofCompletion (𝓞 L) L w.val
          (Units.map (AbsoluteValue.Completion.map v.val w.val.val).toMonoidHom u) := by
  classical
  let _ : Fintype {w : InfinitePlace L // w.LiesOver v} := Fintype.ofFinite _
  rw [finprod_eq_prod_of_fintype]
  refine IdeleGroup.ext (fun w ↦ ?_) (fun w ↦ ?_)
  · rw [ideleInfiniteCoord_ideleExtension, map_prod]
    by_cases hw : w.LiesOver v
    · have hv : w.comap (algebraMap K L) = v := InfinitePlace.LiesOver.comap_eq w v
      rw [Finset.prod_eq_single ⟨w, hw⟩
        (fun w' _ hw' ↦ w.ideleInfiniteCoord_ofCompletion_of_ne (fun h ↦ hw' (Subtype.ext h.symm))
          _)
        (fun h ↦ (h (Finset.mem_univ _)).elim),
        w.ideleInfiniteCoord_ofCompletion_self]
      subst hv
      simp only [InfinitePlace.ideleInfiniteCoord_ofCompletion_self]
    · have hne : w.comap (algebraMap K L) ≠ v := fun h ↦ hw (h ▸ inferInstance)
      rw [InfinitePlace.ideleInfiniteCoord_ofCompletion_of_ne _ hne, map_one,
        Finset.prod_eq_one fun w' _ ↦
          w.ideleInfiniteCoord_ofCompletion_of_ne (fun h ↦ hw (h ▸ w'.property)) _]
  · simp [ideleFiniteCoord_ideleExtension, map_prod]

/-- **Extension of an idele class concentrated at an infinite place.** Extending
`IdeleClassGroup.ofCompletion v u` from `K` to `L` decomposes it into the product over the infinite
places `w` of `L` above `v`. -/
theorem ideleClassExtension_ofCompletion (v : InfinitePlace K) (u : v.Completionˣ) :
    ideleClassExtension K L (IdeleClassGroup.ofCompletion (𝓞 K) K v u) =
      ∏ᶠ w : {w : InfinitePlace L // w.LiesOver v},
        IdeleClassGroup.ofCompletion (𝓞 L) L w.val
          (Units.map (AbsoluteValue.Completion.map v.val w.val.val).toMonoidHom u) := by
  classical
  let _ : Fintype {w : InfinitePlace L // w.LiesOver v} := Fintype.ofFinite _
  rw [IdeleClassGroup.ofCompletion_apply, ideleClassExtension_mk,
    ideleExtension_ofCompletion, finprod_eq_prod_of_fintype, finprod_eq_prod_of_fintype,
    ← QuotientGroup.mk'_apply, map_prod]
  simp only [QuotientGroup.mk'_apply, IdeleClassGroup.ofCompletion_apply]

end TauCeti.GlobalNumberFields
