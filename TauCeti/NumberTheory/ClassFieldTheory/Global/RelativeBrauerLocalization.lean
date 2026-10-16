/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ClassFieldTheory.Global.InvariantSum
public import TauCeti.NumberTheory.ClassFieldTheory.Global.PlacewiseCohomology
public import TauCeti.RepresentationTheory.Homological.GroupCohomology.Shapiro

/-!
# The localizations of a relative Brauer class and the cohomology of the ideles

Let `L/K` be a finite Galois extension of number fields with Galois group `G`, embedded in `Kˢ`
by `σ`. A class `x ∈ H²(G, Lˣ)` gives the Brauer class `relBrInfl K L σ x ∈ Br K`, whose
localization at a place `v` of `K` is its base change to the completion `K_v`. It also gives,
through the principal ideles `Lˣ → I_L` (`unitsToIdeles`), a class of `H²(G, I_L)`, which has a
semi-local component in `H²(G, (K_v ⊗[K] L)ˣ)` at every place `v`, finite
(`idelesToSemilocalUnits`) or infinite (`idelesToInfiniteSemilocalUnits`). This file shows that
the two families carry the same information: the semi-local component of `x` at `v` vanishes
exactly when the localization of its Brauer class at `v` does. Hence the image of `x` in
`H²(G, I_L)` vanishes exactly when every localization of its Brauer class vanishes
(`map_unitsToIdeles_eq_zero_iff_brLocalization_eq_zero`).

This is the idelic half of the injectivity of `Br K → ⨁_v Br K_v` (Albert–Brauer–Hasse–Noether):
a split class with trivial localizations dies in `H²(G, I_L)`, so by the exact sequence
`1 → Lˣ → I_L → C_L → 1` it comes from `H¹(G, C_L)`.

The comparison at a place `v` goes through Shapiro's lemma. For a place `w` of `L` above `v`, the
semi-local units are coinduced from the units of the completion `L_w` as a representation of the
decomposition group `D_w` (`semilocalUnitsCoindIso`, `infiniteSemilocalUnitsCoindIso`), so the
semi-local component of `x` is determined by its restriction to `D_w`, read in `L_wˣ`
(`groupCohomology.map_id_eq_zero_iff_of_comp_eq_resCoindToHom`). The decomposition group is
the Galois group of `L_w/K_v` (`decompositionHom`), and there the restriction is the map
`H²(Gal(L/K), Lˣ) → H²(Gal(L_w/K_v), L_wˣ)` along restriction of automorphisms and the inclusion
`Lˣ → L_wˣ` (`map_unitsToIdeles_idelesToSemilocalUnits_eq_zero_iff`). That map is how base change
to `K_v` acts on inflated Brauer classes (`brBaseChange_relBrInfl`), and inflation into `Br K_v` is
injective (`relBrInfl_injective`).

## Main results

* `TauCeti.ClassFieldTheory.map_unitsToIdeles_idelesToSemilocalUnits_eq_zero_iff`,
  `TauCeti.ClassFieldTheory.map_unitsToIdeles_idelesToInfiniteSemilocalUnits_eq_zero_iff`: in every
  degree, the semi-local component of a class of `Hⁿ(G, Lˣ)` at a finite or infinite place `v`
  vanishes exactly when its image in `Hⁿ(Gal(L_w/K_v), L_wˣ)` does.
* `map_unitsToIdeles_idelesToSemilocalUnits_eq_zero_iff_brBaseChange_eq_zero`,
  `map_unitsToIdeles_idelesToInfiniteSemilocalUnits_eq_zero_iff_brBaseChange_eq_zero`: in degree
  two, it vanishes exactly when the localization at `v` of the Brauer class does.
* `TauCeti.ClassFieldTheory.map_unitsToIdeles_eq_zero_iff_brLocalization_eq_zero`: the image of
  `x ∈ H²(G, Lˣ)` in `H²(G, I_L)` vanishes exactly when every localization of `relBrInfl K L σ x`
  vanishes.

## References

* J. S. Milne, *Class Field Theory*, Chapter VII, Lemma 2.4 and Proposition 2.5, and Chapter VIII,
  §4.
* J. Tate, *Global class field theory*, in J. W. S. Cassels and A. Fröhlich (eds.),
  *Algebraic Number Theory*, Chapter VII, §§6–7.
-/

public section
noncomputable section

open CategoryTheory IsDedekindDomain IsDedekindDomain.HeightOneSpectrum NumberField
open scoped AdicCompletionExtension Pointwise TensorProduct

namespace TauCeti.ClassFieldTheory

variable {K : Type} [Field K] [NumberField K] {L : Type} [Field L] [NumberField L] [Algebra K L]

section Finite

variable (v : HeightOneSpectrum (𝓞 K)) (w : HeightOneSpectrum (𝓞 L)) [w.asIdeal.LiesOver v.asIdeal]

/-- The inclusion `Lˣ → L_wˣ`, as a morphism of representations of the decomposition group of
`w`. -/
private def unitsToDecompositionUnits :
    Rep.res (MulAction.stabilizer (L ≃ₐ[K] L) w.asIdeal).subtype
        (Rep.ofMulDistribMulAction (L ≃ₐ[K] L) Lˣ) ⟶ decompositionUnitsRep v w :=
  Rep.ofHom <| LinearMap.intertwiningMap_of_isIntertwiningMap _ _
    (Units.map (algebraMap L (w.adicCompletion L) : L →* _)).toAdditive.toIntLinearMap
    fun d a ↦ Additive.toMul.injective <| Units.ext <|
      (decompositionHom_algebraMap (v := v) d (Additive.toMul a : Lˣ)).symm

/-- `unitsToDecompositionUnits` sends `a ∈ Lˣ` to its image in `L_w`. -/
private theorem coe_unitsToDecompositionUnits_hom_apply (a : Additive Lˣ) :
    ((Additive.toMul ((unitsToDecompositionUnits v w).hom a) : (w.adicCompletion L)ˣ) :
      w.adicCompletion L) = algebraMap L (w.adicCompletion L) (Additive.toMul a : Lˣ) :=
  rfl

/-- The semi-local component at `v` of the principal idele of `a ∈ Lˣ` is `1 ⊗ a`. -/
private theorem coe_unitsToIdeles_idelesToSemilocalUnits_hom_apply
    (a : Additive Lˣ) :
    ((Additive.toMul (α := (v.adicCompletion K ⊗[K] L)ˣ)
      ((unitsToIdeles K L ≫ idelesToSemilocalUnits L v).hom a) : (v.adicCompletion K ⊗[K] L)ˣ) :
        v.adicCompletion K ⊗[K] L) = 1 ⊗ₜ[K] ((Additive.toMul a : Lˣ) : L) := by
  have h : (unitsToIdeles K L ≫ idelesToSemilocalUnits L v).hom a =
      Additive.ofMul (finiteIdeleSemilocalHom L v
        (FiniteAdeleRing.unitEmbedding (𝓞 L) L (Additive.toMul a))) :=
    (congrArg (idelesToSemilocalUnits L v).hom (unitsToIdeles_hom_apply (K := K) L a)).trans
      ((idelesToSemilocalUnits_hom_apply L v _).trans
        (congrArg (fun z ↦ Additive.ofMul (finiteIdeleSemilocalHom L v z))
          (IdeleGroup.toFiniteIdele_unitEmbedding (𝓞 L) L _)))
  rw [h, toMul_ofMul, coe_finiteIdeleSemilocalHom, FiniteAdeleRing.unitEmbedding_apply,
    finiteAdeleSemilocalHom_algebraMap]

/-- The principal ideles followed by the semi-local component at `v` and the coinduction map of
the semi-local units are the adjunct of the inclusion `Lˣ → L_wˣ`. -/
private theorem unitsToIdeles_comp_semilocalUnitsToCoind :
    unitsToIdeles K L ≫ idelesToSemilocalUnits L v ≫ semilocalUnitsToCoind v w =
      Rep.resCoindToHom _ _ _ (unitsToDecompositionUnits v w) := by
  ext (a : Additive Lˣ) g
  refine (Additive.toMul (α := (w.adicCompletion L)ˣ)).injective (Units.ext ?_)
  refine (semilocalUnitsToCoind_apply v w (Additive.toMul (α := (v.adicCompletion K ⊗[K] L)ˣ)
    ((unitsToIdeles K L ≫ idelesToSemilocalUnits L v).hom a)) g).trans ?_
  rw [coe_unitsToIdeles_idelesToSemilocalUnits_hom_apply,
    Algebra.TensorProduct.baseChangeAutHom_tmul, semilocalEquiv_tmul, map_one, one_mul]
  rw [Representation.IntertwiningMap.coe_toLinearMap]
  refine Eq.trans ?_ ((congrArg (fun z ↦ Units.val (Additive.toMul z : (w.adicCompletion L)ˣ))
    (Rep.resCoindToHom_hom_apply_coe _ _ _ (unitsToDecompositionUnits v w) a g)).trans <|
      (coe_unitsToDecompositionUnits_hom_apply v w _).trans <| congrArg (algebraMap L _) <|
        congrArg (fun z ↦ Units.val (Additive.toMul z : Lˣ))
          (Rep.ofMulDistribMulAction_ρ_apply_apply g a)).symm
  rw [toMul_ofMul, AlgEquiv.smul_units_def, Units.coe_map, MonoidHom.coe_ofClass]

variable [IsGalois K L]

/-- **The semi-local component of a class of `Hⁿ(Gal(L/K), Lˣ)` at a finite place** `v` vanishes
exactly when the class vanishes in `Hⁿ(Gal(L_w/K_v), L_wˣ)`, for any place `w` of `L` above `v`,
along restriction of automorphisms and the inclusion `Lˣ → L_wˣ`. -/
theorem map_unitsToIdeles_idelesToSemilocalUnits_eq_zero_iff (n : ℕ)
    (x : groupCohomology (Rep.ofMulDistribMulAction (L ≃ₐ[K] L) Lˣ) n) :
    groupCohomology.map (MonoidHom.id _) (unitsToIdeles K L ≫ idelesToSemilocalUnits L v) n x = 0 ↔
      groupCohomology.map ((AlgEquiv.restrictNormalHom L).comp (AlgEquiv.restrictScalarsHom K))
        (unitsBaseChangeHom K L (v.adicCompletion K) (w.adicCompletion L)) n x = 0 :=
  groupCohomology.map_id_eq_zero_iff_of_comp_eq_resCoindToHom _
    ⟨decompositionHom_injective v w, decompositionHom_surjective v w⟩
    restrictNormalHom_restrictScalarsHom_decompositionHom _ (unitsToDecompositionUnits v w)
    -- both are the inclusion `Lˣ → L_wˣ`
    (LinearMap.ext fun a ↦ (unitsBaseChangeHom_apply K L (v.adicCompletion K)
      (w.adicCompletion L) (Additive.toMul a)).symm)
    _ (semilocalUnitsCoindIso v w)
    (by rw [semilocalUnitsCoindIso_hom, Category.assoc,
      unitsToIdeles_comp_semilocalUnitsToCoind]) n x

variable {v} in
/-- **The semi-local component of a class of `H²(Gal(L/K), Lˣ)` at a finite place** `v` vanishes
exactly when the localization at `v` of its Brauer class vanishes. -/
theorem map_unitsToIdeles_idelesToSemilocalUnits_eq_zero_iff_brBaseChange_eq_zero
    (σ : L →ₐ[K] SeparableClosure K)
    (x : groupCohomology (Rep.ofMulDistribMulAction (L ≃ₐ[K] L) Lˣ) 2) :
    groupCohomology.map (MonoidHom.id _) (unitsToIdeles K L ≫ idelesToSemilocalUnits L v) 2 x = 0 ↔
      brBaseChange K (v.adicCompletion K) (relBrInfl K L σ x) = 0 := by
  obtain ⟨w, hw⟩ := under_surjective (𝓞 K) (𝓞 L) v
  have : w.asIdeal.LiesOver v.asIdeal := ⟨congrArg HeightOneSpectrum.asIdeal hw.symm⟩
  rw [map_unitsToIdeles_idelesToSemilocalUnits_eq_zero_iff v w,
    brBaseChange_relBrInfl K (v.adicCompletion K) L (w.adicCompletion L) σ IsSepClosed.lift,
    map_eq_zero_iff _ (relBrInfl_injective _ _ _)]

end Finite

section Infinite

open NumberField.InfinitePlace GlobalNumberFields
open scoped NumberField.LiesOver

variable (v : InfinitePlace K) (w : InfinitePlace L) [w.LiesOver v]

/-- The inclusion `Lˣ → L_wˣ` at an infinite place `w`, as a morphism of representations of the
decomposition group of `w`. -/
private def unitsToInfiniteDecompositionUnits :
    Rep.res (MulAction.stabilizer (L ≃ₐ[K] L) w).subtype
        (Rep.ofMulDistribMulAction (L ≃ₐ[K] L) Lˣ) ⟶ infiniteDecompositionUnitsRep v w :=
  Rep.ofHom <| LinearMap.intertwiningMap_of_isIntertwiningMap _ _
    (Units.map (algebraMap L w.Completion : L →* _)).toAdditive.toIntLinearMap
    fun d a ↦ Additive.toMul.injective <| Units.ext <|
      (decompositionHom_algebraMap (v := v) d ((Additive.toMul a : Lˣ) : L)).symm

omit [NumberField K] [NumberField L] in
/-- `unitsToInfiniteDecompositionUnits` sends `a ∈ Lˣ` to its image in `L_w`. -/
private theorem coe_unitsToInfiniteDecompositionUnits_hom_apply (a : Additive Lˣ) :
    ((Additive.toMul ((unitsToInfiniteDecompositionUnits v w).hom a) : w.Completionˣ) :
      w.Completion) = algebraMap L w.Completion (Additive.toMul a : Lˣ) :=
  rfl

/-- The semi-local component at the infinite place `v` of the principal idele of `a ∈ Lˣ` is
`1 ⊗ a`. -/
private theorem coe_unitsToIdeles_idelesToInfiniteSemilocalUnits_hom_apply
    (a : Additive Lˣ) :
    ((Additive.toMul (α := (v.Completion ⊗[K] L)ˣ)
      ((unitsToIdeles K L ≫ idelesToInfiniteSemilocalUnits L v).hom a) : (v.Completion ⊗[K] L)ˣ) :
        v.Completion ⊗[K] L) = 1 ⊗ₜ[K] ((Additive.toMul a : Lˣ) : L) :=
  (coe_idelesToInfiniteSemilocalUnits_hom_apply L v _).trans <|
    (congrArg (fun z : Additive (IdeleGroup (𝓞 L) L) ↦
      infiniteAdeleSemilocalHom L v ((Additive.toMul z : IdeleGroup (𝓞 L) L) : AdeleRing (𝓞 L) L).1)
      (unitsToIdeles_hom_apply (K := K) L a)).trans
    (infiniteAdeleSemilocalHom_algebraMap (L := L) (v := v) _)

/-- The principal ideles followed by the semi-local component at the infinite place `v` and the
coinduction map of the semi-local units are the adjunct of the inclusion `Lˣ → L_wˣ`. -/
private theorem unitsToIdeles_comp_infiniteSemilocalUnitsToCoind :
    unitsToIdeles K L ≫ idelesToInfiniteSemilocalUnits L v ≫ infiniteSemilocalUnitsToCoind v w =
      Rep.resCoindToHom _ _ _ (unitsToInfiniteDecompositionUnits v w) := by
  ext (a : Additive Lˣ) g
  refine (Additive.toMul (α := w.Completionˣ)).injective (Units.ext ?_)
  refine (infiniteSemilocalUnitsToCoind_apply v w (Additive.toMul (α := (v.Completion ⊗[K] L)ˣ)
    ((unitsToIdeles K L ≫ idelesToInfiniteSemilocalUnits L v).hom a)) g).trans ?_
  rw [coe_unitsToIdeles_idelesToInfiniteSemilocalUnits_hom_apply,
    Algebra.TensorProduct.baseChangeAutHom_tmul, infiniteSemilocalEquiv_tmul, map_one, one_mul]
  rw [Representation.IntertwiningMap.coe_toLinearMap]
  refine Eq.trans ?_ ((congrArg (fun z ↦ Units.val (Additive.toMul z : w.Completionˣ))
    (Rep.resCoindToHom_hom_apply_coe _ _ _ (unitsToInfiniteDecompositionUnits v w) a g)).trans <|
      (coe_unitsToInfiniteDecompositionUnits_hom_apply v w _).trans <| congrArg (algebraMap L _) <|
        congrArg (fun z ↦ Units.val (Additive.toMul z : Lˣ))
          (Rep.ofMulDistribMulAction_ρ_apply_apply g a)).symm
  rw [toMul_ofMul, AlgEquiv.smul_units_def, Units.coe_map, MonoidHom.coe_ofClass]

variable [IsGalois K L]

/-- **The semi-local component of a class of `Hⁿ(Gal(L/K), Lˣ)` at an infinite place** `v`
vanishes exactly when the class vanishes in `Hⁿ(Gal(L_w/K_v), L_wˣ)`, for any place `w` of `L`
above `v`, along restriction of automorphisms and the inclusion `Lˣ → L_wˣ`. -/
theorem map_unitsToIdeles_idelesToInfiniteSemilocalUnits_eq_zero_iff (n : ℕ)
    (x : groupCohomology (Rep.ofMulDistribMulAction (L ≃ₐ[K] L) Lˣ) n) :
    groupCohomology.map (MonoidHom.id _) (unitsToIdeles K L ≫ idelesToInfiniteSemilocalUnits L v) n
        x = 0 ↔
      groupCohomology.map ((AlgEquiv.restrictNormalHom L).comp (AlgEquiv.restrictScalarsHom K))
        (unitsBaseChangeHom K L v.Completion w.Completion) n x = 0 :=
  groupCohomology.map_id_eq_zero_iff_of_comp_eq_resCoindToHom _
    ⟨decompositionHom_injective v w, decompositionHom_surjective v w⟩
    InfinitePlace.restrictNormalHom_restrictScalarsHom_decompositionHom _
    (unitsToInfiniteDecompositionUnits v w)
    -- both are the inclusion `Lˣ → L_wˣ`
    (LinearMap.ext fun a ↦ (unitsBaseChangeHom_apply K L v.Completion w.Completion
      (Additive.toMul a)).symm)
    _ (infiniteSemilocalUnitsCoindIso v w)
    (by rw [infiniteSemilocalUnitsCoindIso_hom, Category.assoc,
      unitsToIdeles_comp_infiniteSemilocalUnitsToCoind]) n x

variable {v} in
/-- **The semi-local component of a class of `H²(Gal(L/K), Lˣ)` at an infinite place** `v`
vanishes exactly when the localization at `v` of its Brauer class vanishes. -/
theorem map_unitsToIdeles_idelesToInfiniteSemilocalUnits_eq_zero_iff_brBaseChange_eq_zero
    (σ : L →ₐ[K] SeparableClosure K)
    (x : groupCohomology (Rep.ofMulDistribMulAction (L ≃ₐ[K] L) Lˣ) 2) :
    groupCohomology.map (MonoidHom.id _) (unitsToIdeles K L ≫ idelesToInfiniteSemilocalUnits L v) 2
        x = 0 ↔
      brBaseChange K v.Completion (relBrInfl K L σ x) = 0 := by
  obtain ⟨w, _⟩ : ∃ w : InfinitePlace L, w.LiesOver v := by
    obtain ⟨w, rfl⟩ := comap_surjective (K := L) v
    exact ⟨w, inferInstance⟩
  have := isGalois_completion v w
  rw [map_unitsToIdeles_idelesToInfiniteSemilocalUnits_eq_zero_iff v w,
    brBaseChange_relBrInfl K v.Completion L w.Completion σ IsSepClosed.lift,
    map_eq_zero_iff _ (relBrInfl_injective _ _ _)]

end Infinite

/-! ### All places together -/

variable [IsGalois K L]

/-- **A split Brauer class has trivial localizations exactly when it dies in the cohomology of the
ideles.** For `L/K` finite Galois, embedded in `Kˢ` by `σ`, a class `x ∈ H²(Gal(L/K), Lˣ)` maps to
zero in `H²(Gal(L/K), I_L)` under the principal ideles exactly when every localization of the
Brauer class `relBrInfl K L σ x`, at the finite and at the infinite places, vanishes. -/
theorem map_unitsToIdeles_eq_zero_iff_brLocalization_eq_zero (σ : L →ₐ[K] SeparableClosure K)
    (x : groupCohomology (Rep.ofMulDistribMulAction (L ≃ₐ[K] L) Lˣ) 2) :
    groupCohomology.map (MonoidHom.id _) (unitsToIdeles K L) 2 x = 0 ↔
      brLocalization K (relBrInfl K L σ x) = 0 := by
  set y := groupCohomology.map (MonoidHom.id _) (unitsToIdeles K L) 2 x
  -- the semi-local components of `y` are those of `x`
  have hfin (v : HeightOneSpectrum (𝓞 K)) :
      groupCohomology.map (MonoidHom.id _) (idelesToSemilocalUnits L v) 2 y = 0 ↔
        brBaseChange K (v.adicCompletion K) (relBrInfl K L σ x) = 0 := by
    rw [← map_unitsToIdeles_idelesToSemilocalUnits_eq_zero_iff_brBaseChange_eq_zero σ x,
      groupCohomology.map_id_comp, ModuleCat.comp_apply]
  have hinf (w : InfinitePlace K) :
      groupCohomology.map (MonoidHom.id _) (idelesToInfiniteSemilocalUnits L w) 2 y = 0 ↔
        brBaseChange K w.Completion (relBrInfl K L σ x) = 0 := by
    rw [← map_unitsToIdeles_idelesToInfiniteSemilocalUnits_eq_zero_iff_brBaseChange_eq_zero σ x,
      groupCohomology.map_id_comp, ModuleCat.comp_apply]
  constructor
  · intro hy
    refine Prod.ext (DFinsupp.ext fun v ↦ ?_) (funext fun w ↦ ?_)
    · rw [brLocalization_fst_apply, Prod.fst_zero, DFinsupp.zero_apply, ← hfin, hy, map_zero]
    · rw [brLocalization_snd_apply, Prod.snd_zero, Pi.zero_apply, ← hinf, hy, map_zero]
  · intro hx
    -- `y` is detected by its semi-local components, read in Tate cohomology
    let e := (_root_.TateCohomology.isoGroupCohomology (R := ℤ) (G := L ≃ₐ[K] L) 2)
    have h {Y : Rep ℤ (L ≃ₐ[K] L)} (f : idelesRep K L ⟶ Y)
        (hf : groupCohomology.map (MonoidHom.id _) f 2 y = 0) :
        ((tateCohomologyFunctor ((2 : ℕ) : ℤ)).map f).hom (e.inv.app _ y) = 0 :=
      calc ((tateCohomologyFunctor ((2 : ℕ) : ℤ)).map f).hom (e.inv.app _ y)
          _ = (e.inv.app _ ≫ (tateCohomologyFunctor ((2 : ℕ) : ℤ)).map f).hom y :=
            (ModuleCat.comp_apply _ _ y).symm
          _ = ((groupCohomology.functor ℤ (L ≃ₐ[K] L) 2).map f ≫ e.inv.app _).hom y := by
            rw [e.inv.naturality]
          _ = (e.inv.app _).hom (groupCohomology.map (MonoidHom.id _) f 2 y) := by
            rw [groupCohomology.functor_map]
            exact ModuleCat.comp_apply _ _ y
          _ = 0 := by rw [hf]; exact map_zero _
    suffices e.inv.app _ y = 0 from
      (e.app _).symm.toLinearEquiv.injective (this.trans (map_zero _).symm)
    exact eq_zero_of_forall_map_semilocal_eq_zero L 2
      (fun v ↦ h _ ((hfin v).2 (by simpa using congrArg (fun z ↦ z.1 v) hx)))
      (fun w ↦ h _ ((hinf w).2 (by simpa using congrArg (fun z ↦ z.2 w) hx)))

end TauCeti.ClassFieldTheory
