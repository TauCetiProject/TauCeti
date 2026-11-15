/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.MonoidAlgebra.MapDomain
public import Mathlib.RingTheory.Finiteness.Projective
public import Mathlib.RingTheory.TensorProduct.Maps
public import Mathlib.Topology.Algebra.Group.OpenMapping
public import Mathlib.Topology.Algebra.Module.ModuleTopology
public import TauCeti.Topology.Algebra.Group.Profinite.CompletedGroupAlgebra.Basic

/-!
# Coefficient maps and base change of the completed group algebra

An additive homomorphism or ring homomorphism of commutative coefficient rings acts levelwise on
the quotients `R[Γ ⧸ U]` of a topological group `Γ`, and compatibility with the transition maps
`R[Γ ⧸ U] → R[Γ ⧸ V]` assembles these levelwise maps into maps between completed group algebras:
`mapAddMonoidHom`, `mapRingHom`, and `mapRingEquiv`. Each is continuous for the inverse-limit
topologies whenever the underlying coefficient map is continuous.

For any commutative `R`-algebra `O`, multiplication in `O[[Γ]]` together with `mapRingHom` along
`algebraMap R O` defines a canonical `O`-algebra homomorphism
`scalarTensorAlgHom R O Γ : O ⊗[R] R[[Γ]] →ₐ[O] O[[Γ]]`. Because infinite inverse limits do not
commute with arbitrary tensor products, this map need not be an isomorphism in general:
* without finite generation (`O = 𝔽_p[T]` over `R = 𝔽_p` and `Γ = ℤ_p`), elements of
  `O ⊗[R] R[[Γ]]` have bounded `T`-degree across all open normal quotients whereas `O[[Γ]]`
  contains power series of unbounded `T`-degree;
* without projectivity (`R = 𝔽_p⟦x_0, x_1, …⟧`, `O = 𝔽_p`, `Γ = ℤ_p`), an infinite series whose
  coefficients lie in varying generators of the augmentation ideal maps to `0` in `O[[Γ]]` while
  remaining nonzero in `O ⊗[R] R[[Γ]]`.

When `O` is finitely generated and projective over `R`, choosing a finite dual pair from
`Module.Finite.exists_comp_eq_id_of_projective` supplies a levelwise inverse, upgrading the
comparison to an `O`-algebra isomorphism `scalarTensorEquiv R O Γ : O ⊗[R] R[[Γ]] ≃ₐ[O] O[[Γ]]`.
When `O` carries the `R`-module topology and admits a finite `R`-basis `b`, taking `b`-coordinates
of levelwise coefficients yields a topological additive isomorphism
`coordContinuousAddEquiv Γ b : O[[Γ]] ≃ₜ+ (ι → R[[Γ]])` for the inverse-limit topologies.

## Main definitions

* `TauCeti.completedGroupAlgebra.mapAddMonoidHom`: the additive homomorphism `S[[Γ]] →+ T[[Γ]]`
  induced levelwise by `f : S →+ T`.
* `TauCeti.completedGroupAlgebra.mapRingHom`, `TauCeti.completedGroupAlgebra.mapRingEquiv`: the
  ring homomorphism `R[[Γ]] →+* S[[Γ]]` and ring isomorphism `R[[Γ]] ≃+* S[[Γ]]` induced levelwise
  by a ring homomorphism or isomorphism.
* `TauCeti.completedGroupAlgebra.scalarTensorAlgHom`: the canonical `O`-algebra map
  `O ⊗[R] R[[Γ]] →ₐ[O] O[[Γ]]`.
* `TauCeti.completedGroupAlgebra.scalarTensorEquiv`: the `O`-algebra isomorphism
  `O ⊗[R] R[[Γ]] ≃ₐ[O] O[[Γ]]` for finite projective `O` over `R`.
* `TauCeti.completedGroupAlgebra.coordContinuousAddEquiv`: the topological additive equivalence
  `O[[Γ]] ≃ₜ+ (ι → R[[Γ]])` attached to a finite `R`-basis of `O` when `O` carries the `R`-module
  topology.

## Main results

* `TauCeti.completedGroupAlgebra.continuous_mapAddMonoidHom`,
  `TauCeti.completedGroupAlgebra.continuous_mapRingHom`: continuity for the inverse-limit
  topologies from continuity on coefficients.
* `TauCeti.completedGroupAlgebra.mapAddMonoidHom_injective`,
  `TauCeti.completedGroupAlgebra.mapRingHom_injective`: injectivity from injectivity on
  coefficients.
* `TauCeti.completedGroupAlgebra.scalarTensorEquiv_tmul`,
  `TauCeti.completedGroupAlgebra.scalarTensorEquiv_tmul_of`,
  `TauCeti.completedGroupAlgebra.scalarTensorEquiv_self`: explicit formulas and normalization of
  finite projective base change.

## References

* L. Ribes and P. Zalesskii, *Profinite Groups*, Section 5.3.
* J. Rodrigues Jacinto and C. Williams, *An introduction to p-adic L-functions*, Section 3.3.
-/

public noncomputable section

open TensorProduct

namespace TauCeti.completedGroupAlgebra

section AddMonoidHom

variable {S T V : Type*} [CommRing S] [CommRing T] [CommRing V]
  (Γ : Type*) [Group Γ] [TopologicalSpace Γ]

private theorem mapDomain_map_addMonoidHom {M N : Type*} (g : M → N) (f : S →+ T)
    (x : MonoidAlgebra S M) :
    MonoidAlgebra.mapDomain g (MonoidAlgebra.map f x) =
      MonoidAlgebra.map f (MonoidAlgebra.mapDomain g x) := by
  classical
  apply MonoidAlgebra.coeff_injective
  rw [MonoidAlgebra.coeff_mapDomain, MonoidAlgebra.coeff_map, MonoidAlgebra.coeff_map,
    MonoidAlgebra.coeff_mapDomain]
  induction x.coeff using Finsupp.induction with
  | zero => simp
  | @single_add a s c _ _ ih => simp [Finsupp.mapDomain_add, Finsupp.mapRange_add (map_add f), ih]

/-- An additive homomorphism `f : S →+ T` between commutative coefficient rings induces an additive
homomorphism `S[[Γ]] →+ T[[Γ]]` by applying `MonoidAlgebra.map f` at every open normal quotient
`Γ ⧸ U`. -/
def mapAddMonoidHom (f : S →+ T) : completedGroupAlgebra S Γ →+ completedGroupAlgebra T Γ where
  toFun x := mk T Γ (fun U ↦ MonoidAlgebra.map f (proj S Γ U x)) fun U V hUV ↦ by
    rw [mapDomain_map_addMonoidHom, mapDomain_mapOfLE_proj hUV]
  map_zero' := ext fun U ↦ by simp [proj_mk]
  map_add' x y := ext fun U ↦ by
    simp [proj_mk, MonoidAlgebra.map_add]

variable {Γ}

/-- The projection of `mapAddMonoidHom Γ f x` at level `U` is `MonoidAlgebra.map f` applied to the
projection of `x`. -/
@[simp]
theorem proj_mapAddMonoidHom (f : S →+ T) (U : OpenNormalSubgroup Γ)
    (x : completedGroupAlgebra S Γ) :
    proj T Γ U (mapAddMonoidHom Γ f x) = MonoidAlgebra.map f (proj S Γ U x) := by
  simp [mapAddMonoidHom]

/-- Every coefficient of `mapAddMonoidHom Γ f x` is `f` applied to the corresponding coefficient of
`x`. -/
theorem coeff_proj_mapAddMonoidHom (f : S →+ T) (U : OpenNormalSubgroup Γ)
    (x : completedGroupAlgebra S Γ) (g : Γ ⧸ U.toSubgroup) :
    (proj T Γ U (mapAddMonoidHom Γ f x)).coeff g = f ((proj S Γ U x).coeff g) := by
  simp

/-- Applying `mapAddMonoidHom Γ f` to a group element multiplies the target group element by
`f 1`. -/
@[simp]
theorem mapAddMonoidHom_of (f : S →+ T) (γ : Γ) :
    mapAddMonoidHom Γ f (of S Γ γ) = f 1 • of T Γ γ :=
  ext fun U ↦ by
    rw [proj_mapAddMonoidHom, proj_of, MonoidAlgebra.map_single, map_smul, proj_of,
      MonoidAlgebra.smul_single', mul_one]

@[simp]
theorem mapAddMonoidHom_id :
    mapAddMonoidHom Γ (AddMonoidHom.id S) = AddMonoidHom.id (completedGroupAlgebra S Γ) :=
  AddMonoidHom.ext fun x ↦ ext fun U ↦ MonoidAlgebra.coeff_injective <| Finsupp.ext fun g ↦ by
    simp

@[simp]
theorem mapAddMonoidHom_comp (g : T →+ V) (f : S →+ T) :
    mapAddMonoidHom Γ (g.comp f) = (mapAddMonoidHom Γ g).comp (mapAddMonoidHom Γ f) :=
  AddMonoidHom.ext fun x ↦ ext fun U ↦ MonoidAlgebra.coeff_injective <| Finsupp.ext fun q ↦ by
    simp

/-- `mapAddMonoidHom Γ f` is injective whenever `f` is injective. -/
theorem mapAddMonoidHom_injective {f : S →+ T} (hf : Function.Injective f) :
    Function.Injective (mapAddMonoidHom Γ f) := fun _ _ h ↦
  ext fun U ↦ MonoidAlgebra.coeff_injective <| Finsupp.ext fun g ↦ hf <| by
    simpa only [coeff_proj_mapAddMonoidHom] using congrArg (fun z ↦ (proj T Γ U z).coeff g) h

/-- If `f` is continuous, `mapAddMonoidHom Γ f` is continuous for the inverse-limit topologies. -/
theorem continuous_mapAddMonoidHom [TopologicalSpace S] [TopologicalSpace T] {f : S →+ T}
    (hf : Continuous f) : Continuous (mapAddMonoidHom Γ f) := by
  refine continuous_iff.mpr fun U g ↦ ?_
  simp only [coeff_proj_mapAddMonoidHom]
  exact hf.comp (continuous_coeff_proj S Γ U g)

end AddMonoidHom

section RingHom

variable {R S T : Type*} [CommRing R] [CommRing S] [CommRing T]
  (Γ : Type*) [Group Γ] [TopologicalSpace Γ]

/-- A ring homomorphism `f : R →+* S` induces a ring homomorphism `R[[Γ]] →+* S[[Γ]]` by applying
`MonoidAlgebra.mapRingHom` at every open normal quotient `Γ ⧸ U`. -/
def mapRingHom (f : R →+* S) : completedGroupAlgebra R Γ →+* completedGroupAlgebra S Γ where
  toFun x := mk S Γ (fun U ↦ MonoidAlgebra.mapRingHom (Γ ⧸ U.toSubgroup) f (proj R Γ U x))
    fun U V hUV ↦ by
      have := RingHom.congr_fun
        (MonoidAlgebra.mapRingHom_comp_mapDomainRingHom f (QuotientGroup.mapOfLE hUV))
        (proj R Γ U x)
      simpa only [RingHom.comp_apply, MonoidAlgebra.mapDomainRingHom_apply,
        mapDomain_mapOfLE_proj] using this.symm
  map_one' := ext fun U ↦ by simp [proj_mk]
  map_mul' x y := ext fun U ↦ by simp [proj_mk]
  map_zero' := ext fun U ↦ by simp [proj_mk]
  map_add' x y := ext fun U ↦ by simp [proj_mk]

variable {Γ}

/-- The underlying additive homomorphism of `mapRingHom Γ f` is `mapAddMonoidHom Γ f`. -/
theorem toAddMonoidHom_mapRingHom (f : R →+* S) :
    (mapRingHom Γ f).toAddMonoidHom = mapAddMonoidHom Γ f.toAddMonoidHom :=
  AddMonoidHom.ext fun x ↦ ext fun U ↦ MonoidAlgebra.coeff_injective <| Finsupp.ext fun g ↦ by
    simp [mapRingHom]

@[simp]
theorem coe_toAddMonoidHom_mapRingHom (f : R →+* S) :
    (mapRingHom Γ f : completedGroupAlgebra R Γ →+ completedGroupAlgebra S Γ) =
      mapAddMonoidHom Γ (f : R →+ S) :=
  toAddMonoidHom_mapRingHom f

/-- The projection of `mapRingHom Γ f x` at level `U` is `MonoidAlgebra.mapRingHom` applied to the
projection of `x`. -/
@[simp]
theorem proj_mapRingHom (f : R →+* S) (U : OpenNormalSubgroup Γ)
    (x : completedGroupAlgebra R Γ) :
    proj S Γ U (mapRingHom Γ f x) =
      MonoidAlgebra.mapRingHom (Γ ⧸ U.toSubgroup) f (proj R Γ U x) := by
  simp [mapRingHom]

/-- Every coefficient of `mapRingHom Γ f x` is `f` applied to the corresponding coefficient of
`x`. -/
theorem coeff_proj_mapRingHom (f : R →+* S) (U : OpenNormalSubgroup Γ)
    (x : completedGroupAlgebra R Γ) (g : Γ ⧸ U.toSubgroup) :
    (proj S Γ U (mapRingHom Γ f x)).coeff g = f ((proj R Γ U x).coeff g) := by
  simp

/-- `mapRingHom Γ f` preserves the group elements inside the completed group algebra. -/
@[simp]
theorem mapRingHom_of (f : R →+* S) (γ : Γ) :
    mapRingHom Γ f (of R Γ γ) = of S Γ γ :=
  ext fun U ↦ by simp

/-- `mapRingHom Γ f` intertwines the scalar embeddings from `R` and `S`. -/
@[simp]
theorem mapRingHom_algebraMap (f : R →+* S) (r : R) :
    mapRingHom Γ f (algebraMap R (completedGroupAlgebra R Γ) r) =
      algebraMap S (completedGroupAlgebra S Γ) (f r) :=
  ext fun U ↦ by
    simp [Algebra.algebraMap_eq_smul_one, MonoidAlgebra.one_def]

/-- `mapRingHom Γ f` is semilinear with respect to `f`. -/
@[simp]
theorem mapRingHom_smul (f : R →+* S) (r : R) (x : completedGroupAlgebra R Γ) :
    mapRingHom Γ f (r • x) = f r • mapRingHom Γ f x := by
  rw [Algebra.smul_def, map_mul, mapRingHom_algebraMap, ← Algebra.smul_def]

@[simp]
theorem mapRingHom_id :
    mapRingHom Γ (RingHom.id R) = RingHom.id (completedGroupAlgebra R Γ) :=
  RingHom.ext fun x ↦ ext fun U ↦ by simp

@[simp]
theorem mapRingHom_comp (g : S →+* T) (f : R →+* S) :
    mapRingHom Γ (g.comp f) = (mapRingHom Γ g).comp (mapRingHom Γ f) :=
  RingHom.ext fun x ↦ ext fun U ↦ by simp

/-- `mapRingHom Γ f` is injective whenever `f` is injective. -/
theorem mapRingHom_injective {f : R →+* S} (hf : Function.Injective f) :
    Function.Injective (mapRingHom Γ f) :=
  mapAddMonoidHom_injective hf

/-- If `f` is continuous, `mapRingHom Γ f` is continuous for the inverse-limit topologies. -/
theorem continuous_mapRingHom [TopologicalSpace R] [TopologicalSpace S] {f : R →+* S}
    (hf : Continuous f) : Continuous (mapRingHom Γ f) :=
  continuous_mapAddMonoidHom hf

variable (Γ) in
/-- A ring isomorphism `e : R ≃+* S` induces a ring isomorphism `R[[Γ]] ≃+* S[[Γ]]`. -/
def mapRingEquiv (e : R ≃+* S) :
    completedGroupAlgebra R Γ ≃+* completedGroupAlgebra S Γ :=
  RingEquiv.ofRingHom (mapRingHom Γ e.toRingHom) (mapRingHom Γ e.symm.toRingHom)
    (RingHom.ext fun x ↦ ext fun U ↦ MonoidAlgebra.coeff_injective <| Finsupp.ext fun q ↦ by simp)
    (RingHom.ext fun x ↦ ext fun U ↦ MonoidAlgebra.coeff_injective <| Finsupp.ext fun q ↦ by simp)

@[simp]
theorem coe_mapRingEquiv (e : R ≃+* S) :
    ⇑(mapRingEquiv Γ e) = mapRingHom Γ e.toRingHom :=
  (rfl)

@[simp]
theorem mapRingEquiv_symm (e : R ≃+* S) :
    (mapRingEquiv Γ e).symm = mapRingEquiv Γ e.symm :=
  (rfl)

@[simp]
theorem mapRingEquiv_of (e : R ≃+* S) (γ : Γ) :
    mapRingEquiv Γ e (of R Γ γ) = of S Γ γ :=
  mapRingHom_of e.toRingHom γ

end RingHom

section BaseChange

variable (R O : Type*) [CommRing R] [CommRing O] [Algebra R O]
  (Γ : Type*) [Group Γ] [TopologicalSpace Γ]

/-- The canonical `O`-algebra homomorphism `O ⊗[R] R[[Γ]] →ₐ[O] O[[Γ]]` sending `a ⊗ₜ x` to
`a • mapRingHom Γ (algebraMap R O) x`. No finiteness or projectivity hypothesis on `O` is needed to
construct this map. -/
def scalarTensorAlgHom :
    O ⊗[R] completedGroupAlgebra R Γ →ₐ[O] completedGroupAlgebra O Γ :=
  letI : Module R (completedGroupAlgebra O Γ) :=
    Module.compHom (completedGroupAlgebra O Γ) (algebraMap R O)
  letI : IsScalarTower R O (completedGroupAlgebra O Γ) :=
    IsScalarTower.of_compHom R O (completedGroupAlgebra O Γ)
  let mapLin : completedGroupAlgebra R Γ →ₗ[R] completedGroupAlgebra O Γ :=
    { toFun := mapRingHom Γ (algebraMap R O)
      map_add' := map_add _
      map_smul' := fun r x ↦ mapRingHom_smul (algebraMap R O) r x }
  Algebra.TensorProduct.algHomOfLinearMapTensorProduct
    (LinearMap.liftBaseChange O mapLin)
    (fun a₁ a₂ x₁ x₂ ↦ by
      simp only [LinearMap.liftBaseChange_tmul, mapLin, LinearMap.coe_mk, AddHom.coe_mk]
      rw [Algebra.smul_def, Algebra.smul_def, Algebra.smul_def, map_mul, map_mul]
      simp only [mul_assoc]
      congr 1
      rw [← mul_assoc, Algebra.commutes a₂, mul_assoc])
    (by simp [mapLin])

variable {R O Γ}

@[simp]
theorem scalarTensorAlgHom_tmul (a : O) (x : completedGroupAlgebra R Γ) :
    scalarTensorAlgHom R O Γ (a ⊗ₜ[R] x) = a • mapRingHom Γ (algebraMap R O) x :=
  (rfl)

theorem scalarTensorAlgHom_tmul_of (a : O) (γ : Γ) :
    scalarTensorAlgHom R O Γ (a ⊗ₜ[R] of R Γ γ) = a • of O Γ γ := by
  simp

@[simp]
theorem proj_scalarTensorAlgHom (U : OpenNormalSubgroup Γ)
    (z : O ⊗[R] completedGroupAlgebra R Γ) :
    proj O Γ U (scalarTensorAlgHom R O Γ z) =
      LinearMap.liftBaseChange O
        (MonoidAlgebra.mapAlgHom (Γ ⧸ U.toSubgroup) (Algebra.ofId R O)).toLinearMap
        (LinearMap.lTensor O (proj R Γ U).toLinearMap z) := by
  induction z using TensorProduct.inductionOn with
  | tmul a x =>
    simp only [scalarTensorAlgHom_tmul, map_smul, proj_mapRingHom, LinearMap.lTensor_tmul,
      AlgHom.toLinearMap_apply, LinearMap.liftBaseChange_tmul]
    rfl
  | add z₁ z₂ hz₁ hz₂ => simp [hz₁, hz₂]

private theorem mapAddMonoidHom_smul_mapRingHom (ℓ : O →ₗ[R] R) (a : O)
    (x : completedGroupAlgebra R Γ) :
    mapAddMonoidHom Γ ℓ.toAddMonoidHom (a • mapRingHom Γ (algebraMap R O) x) = ℓ a • x :=
  ext fun U ↦ MonoidAlgebra.coeff_injective <| Finsupp.ext fun g ↦ by
    simp only [coeff_proj_mapAddMonoidHom, map_smul, MonoidAlgebra.coeff_smul_apply,
      coeff_proj_mapRingHom, LinearMap.toAddMonoidHom_coe, smul_eq_mul]
    rw [mul_comm, ← Algebra.smul_def, map_smul, smul_eq_mul, mul_comm]

section Projective

variable [Module.Projective R O] [Module.Finite R O]

private def projDualN : ℕ :=
  (Module.Finite.exists_comp_eq_id_of_projective R O).choose

private def projDualF : (Fin (projDualN (R := R) (O := O)) → R) →ₗ[R] O :=
  (Module.Finite.exists_comp_eq_id_of_projective R O).choose_spec.choose

private def projDualG : O →ₗ[R] Fin (projDualN (R := R) (O := O)) → R :=
  (Module.Finite.exists_comp_eq_id_of_projective R O).choose_spec.choose_spec.choose

private theorem projDual_sum (a : O) :
    ∑ i : Fin (projDualN (R := R) (O := O)),
      projDualG a i • projDualF (R := R) (Pi.single i 1) = a := by
  have ha := LinearMap.congr_fun
    (Module.Finite.exists_comp_eq_id_of_projective R O).choose_spec.choose_spec.choose_spec.2.2 a
  change projDualF (projDualG a) = a at ha
  have hsingle : projDualG (R := R) a =
      ∑ i : Fin (projDualN (R := R) (O := O)), projDualG a i • Pi.single i 1 := by
    ext j
    simp [Pi.single_apply]
  rw [hsingle, map_sum] at ha
  simpa only [map_smul] using ha

private def scalarTensorInvFun (y : completedGroupAlgebra O Γ) :
    O ⊗[R] completedGroupAlgebra R Γ :=
  ∑ i : Fin (projDualN (R := R) (O := O)),
    projDualF (R := R) (Pi.single i 1) ⊗ₜ[R]
      mapAddMonoidHom Γ ((LinearMap.proj i).comp (projDualG (R := R))).toAddMonoidHom y

private theorem scalarTensorInvFun_leftInverse :
    Function.LeftInverse (scalarTensorInvFun (R := R) (O := O) (Γ := Γ))
      (scalarTensorAlgHom R O Γ) := by
  have hadd : ∀ u v : completedGroupAlgebra O Γ,
      scalarTensorInvFun (R := R) (u + v) = scalarTensorInvFun u + scalarTensorInvFun v :=
    fun u v ↦ by simp [scalarTensorInvFun, tmul_add, Finset.sum_add_distrib]
  intro z
  induction z using TensorProduct.inductionOn with
  | tmul a x =>
    simp only [scalarTensorAlgHom_tmul, scalarTensorInvFun, mapAddMonoidHom_smul_mapRingHom,
      LinearMap.comp_apply, LinearMap.proj_apply, ← smul_tmul, ← sum_tmul]
    exact congrArg (· ⊗ₜ[R] x) (projDual_sum a)
  | add z₁ z₂ hz₁ hz₂ =>
    rw [map_add, hadd, hz₁, hz₂]

private theorem scalarTensorInvFun_rightInverse :
    Function.RightInverse (scalarTensorInvFun (R := R) (O := O) (Γ := Γ))
      (scalarTensorAlgHom R O Γ) := by
  intro y
  rw [scalarTensorInvFun, map_sum]
  refine ext fun U ↦ MonoidAlgebra.coeff_injective <| Finsupp.ext fun q ↦ ?_
  simp only [scalarTensorAlgHom_tmul, map_sum, MonoidAlgebra.coeff_sum, Finsupp.finsetSum_apply,
    map_smul, MonoidAlgebra.coeff_smul_apply, coeff_proj_mapRingHom, coeff_proj_mapAddMonoidHom,
    LinearMap.toAddMonoidHom_coe, LinearMap.comp_apply, LinearMap.proj_apply, smul_eq_mul]
  have hcomm : ∀ b : O, ∀ r : R, b * algebraMap R O r = r • b :=
    fun b r ↦ by rw [Algebra.smul_def, mul_comm]
  simp_rw [hcomm]
  exact projDual_sum ((proj O Γ U y).coeff q)

variable (R O Γ) in
/-- **Base change of the completed group algebra.** When `O` is finitely generated and projective
over `R`, extending coefficients from `R[[Γ]]` to `O[[Γ]]` identifies `O ⊗[R] R[[Γ]]` with `O[[Γ]]`
as an `O`-algebra. -/
def scalarTensorEquiv :
    O ⊗[R] completedGroupAlgebra R Γ ≃ₐ[O] completedGroupAlgebra O Γ :=
  { scalarTensorAlgHom R O Γ with
    invFun := scalarTensorInvFun
    left_inv := scalarTensorInvFun_leftInverse
    right_inv := scalarTensorInvFun_rightInverse }

@[simp]
theorem coe_scalarTensorEquiv :
    ⇑(scalarTensorEquiv R O Γ) = scalarTensorAlgHom R O Γ :=
  (rfl)

@[simp]
theorem toAlgHom_scalarTensorEquiv :
    (scalarTensorEquiv R O Γ).toAlgHom = scalarTensorAlgHom R O Γ :=
  (rfl)

@[simp]
theorem scalarTensorEquiv_tmul (a : O) (x : completedGroupAlgebra R Γ) :
    scalarTensorEquiv R O Γ (a ⊗ₜ[R] x) = a • mapRingHom Γ (algebraMap R O) x :=
  (rfl)

theorem scalarTensorEquiv_tmul_of (a : O) (γ : Γ) :
    scalarTensorEquiv R O Γ (a ⊗ₜ[R] of R Γ γ) = a • of O Γ γ :=
  scalarTensorAlgHom_tmul_of a γ

theorem proj_scalarTensorEquiv (U : OpenNormalSubgroup Γ)
    (z : O ⊗[R] completedGroupAlgebra R Γ) :
    proj O Γ U (scalarTensorEquiv R O Γ z) =
      LinearMap.liftBaseChange O
        (MonoidAlgebra.mapAlgHom (Γ ⧸ U.toSubgroup) (Algebra.ofId R O)).toLinearMap
        (LinearMap.lTensor O (proj R Γ U).toLinearMap z) :=
  proj_scalarTensorAlgHom U z

@[simp]
theorem scalarTensorEquiv_symm_mapRingHom (x : completedGroupAlgebra R Γ) :
    (scalarTensorEquiv R O Γ).symm (mapRingHom Γ (algebraMap R O) x) = 1 ⊗ₜ[R] x := by
  apply (scalarTensorEquiv R O Γ).injective
  simp

@[simp]
theorem scalarTensorEquiv_symm_of (γ : Γ) :
    (scalarTensorEquiv R O Γ).symm (of O Γ γ) = 1 ⊗ₜ[R] of R Γ γ := by
  rw [← mapRingHom_of (algebraMap R O), scalarTensorEquiv_symm_mapRingHom]

/-- Base change from `R` to `R` itself recovers `Algebra.TensorProduct.lid`. -/
@[simp]
theorem scalarTensorEquiv_self :
    scalarTensorEquiv R R Γ = Algebra.TensorProduct.lid R (completedGroupAlgebra R Γ) := by
  apply AlgEquiv.coe_toAlgHom_injective
  ext x
  simp

end Projective

section Coordinates

variable (Γ) {ι : Type*} [Fintype ι] (b : Module.Basis ι R O)
  [TopologicalSpace R] [TopologicalSpace O] [IsModuleTopology R O]

/-- Given a finite `R`-basis `b` of `O`, when `O` carries the `R`-module topology, taking the
`b`-coordinates of every levelwise coefficient identifies `O[[Γ]]` with `ι → R[[Γ]]` as a
topological additive group. -/
def coordContinuousAddEquiv [IsTopologicalRing R] [ContinuousAdd O] :
    completedGroupAlgebra O Γ ≃ₜ+ (ι → completedGroupAlgebra R Γ) where
  toFun y i := mapAddMonoidHom Γ (b.coord i).toAddMonoidHom y
  invFun c := ∑ i : ι, b i • mapRingHom Γ (algebraMap R O) (c i)
  left_inv y := ext fun U ↦ MonoidAlgebra.coeff_injective <| Finsupp.ext fun q ↦ by
    simp only [map_sum, MonoidAlgebra.coeff_sum, Finsupp.finsetSum_apply, map_smul,
      MonoidAlgebra.coeff_smul_apply, coeff_proj_mapRingHom, coeff_proj_mapAddMonoidHom,
      LinearMap.toAddMonoidHom_coe, Module.Basis.coord_apply, smul_eq_mul]
    have hcomm : ∀ x : O, ∀ r : R, x * algebraMap R O r = r • x :=
      fun x r ↦ by rw [Algebra.smul_def, mul_comm]
    simp_rw [hcomm]
    exact b.sum_repr ((proj O Γ U y).coeff q)
  right_inv c := funext fun i ↦ by
    classical
    dsimp only
    simp [mapAddMonoidHom_smul_mapRingHom, b.repr_self]
  map_add' x y := funext fun i ↦ map_add _ x y
  continuous_toFun := continuous_pi fun i ↦
    continuous_mapAddMonoidHom (IsModuleTopology.continuous_of_linearMap (b.coord i))
  continuous_invFun := by
    have := IsModuleTopology.toContinuousSMul R O
    refine continuous_iff.mpr fun U q ↦ ?_
    simp only [map_sum, MonoidAlgebra.coeff_sum, Finsupp.finsetSum_apply, map_smul,
      MonoidAlgebra.coeff_smul_apply, coeff_proj_mapRingHom, smul_eq_mul]
    have hcomm : ∀ x : O, ∀ r : R, x * algebraMap R O r = r • x :=
      fun x r ↦ by rw [Algebra.smul_def, mul_comm]
    simp_rw [hcomm]
    exact continuous_finsetSum _ fun i _ ↦
      ((continuous_coeff_proj R Γ U q).comp (continuous_apply i)).smul continuous_const

variable {Γ}

@[simp]
theorem coordContinuousAddEquiv_apply [IsTopologicalRing R] [ContinuousAdd O]
    (y : completedGroupAlgebra O Γ) (i : ι) :
    coordContinuousAddEquiv Γ b y i = mapAddMonoidHom Γ (b.coord i).toAddMonoidHom y :=
  (rfl)

@[simp]
theorem coordContinuousAddEquiv_symm_apply [IsTopologicalRing R] [ContinuousAdd O]
    (c : ι → completedGroupAlgebra R Γ) :
    (coordContinuousAddEquiv Γ b).symm c =
      ∑ i : ι, b i • mapRingHom Γ (algebraMap R O) (c i) :=
  (rfl)

end Coordinates

end BaseChange

end TauCeti.completedGroupAlgebra
