/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Finiteness.Projective
public import Mathlib.RingTheory.TensorProduct.Maps
public import Mathlib.Topology.Algebra.Module.ModuleTopology
public import TauCeti.Algebra.MonoidAlgebra.MapDomain
public import TauCeti.Topology.Algebra.Group.Profinite.CompletedGroupAlgebra.Basic
import TauCeti.LinearAlgebra.Dual.FiniteProjective

/-!
# Change of coefficients and base change for the completed group algebra

An additive homomorphism `f : R →+ S` applies coefficientwise at every open-normal quotient level
`R[Γ ⧸ U] → S[Γ ⧸ U]`, and compatibility along the quotient maps `Γ ⧸ U → Γ ⧸ V` assembles these
level maps into an additive homomorphism
`completedGroupAlgebra.mapAddMonoidHom Γ f : R[[Γ]] →+ S[[Γ]]`. For a ring homomorphism
`f : R →+* S` (or isomorphism `e : R ≃+* S`) this upgrades to a ring homomorphism
`completedGroupAlgebra.mapRingHom Γ f : R[[Γ]] →+* S[[Γ]]` (and
`mapRingEquiv Γ e : R[[Γ]] ≃+* S[[Γ]]`) sending each group element `of R Γ γ` to `of S Γ γ`. Each
is continuous for the inverse-limit topologies whenever the underlying coefficient map is
continuous.

When `S` is an `R`-algebra, scalar multiplication on the left combines with
`mapRingHom Γ (algebraMap R S)` into an `S`-algebra homomorphism
`completedGroupAlgebra.baseChange R S Γ : S ⊗[R] R[[Γ]] →ₐ[S] S[[Γ]]`. Because infinite inverse
limits do not commute with arbitrary tensor products, this map need not be an isomorphism in
general:
* without finite generation (`S = 𝔽_p[T]` over `R = 𝔽_p` and `Γ = ℤ_p`), elements of
  `S ⊗[R] R[[Γ]]` have bounded `T`-degree across all open normal quotients whereas `S[[Γ]]`
  contains power series of unbounded `T`-degree;
* without projectivity (`R = 𝔽_p⟦x_0, x_1, …⟧`, `S = 𝔽_p`, `Γ = ℤ_p`), an infinite series whose
  coefficients lie in varying generators of the augmentation ideal maps to `0` in `S[[Γ]]` while
  remaining nonzero in `S ⊗[R] R[[Γ]]`.

When `S` is finitely generated and projective over `R`, a finite dual basis from
`TauCeti.exists_sum_dual_smul_eq` supplies a two-sided inverse, upgrading `baseChange R S Γ` to an
`S`-algebra isomorphism
`completedGroupAlgebra.baseChangeEquiv R S Γ : S ⊗[R] R[[Γ]] ≃ₐ[S] S[[Γ]]`: `R` and `S` carry no
topology, while `Γ` requires no topological-group or compactness/finite-quotient hypotheses beyond
`[Group Γ] [TopologicalSpace Γ]`. When `S` admits a finite `R`-basis `b`, taking `b`-coordinates of
levelwise coefficients yields an additive isomorphism `coordAddEquiv Γ b : S[[Γ]] ≃+ (ι → R[[Γ]])`,
which upgrades to a topological additive isomorphism
`coordContinuousAddEquiv Γ b : S[[Γ]] ≃ₜ+ (ι → R[[Γ]])` for the inverse-limit topologies when `R`
is a topological ring and `S` carries the `R`-module topology.

## Main definitions

* `TauCeti.completedGroupAlgebra.mapAddMonoidHom Γ f`: the additive homomorphism
  `R[[Γ]] →+ S[[Γ]]` applying `f : R →+ S` to every level coefficient.
* `TauCeti.completedGroupAlgebra.mapRingHom Γ f`,
  `TauCeti.completedGroupAlgebra.mapRingEquiv Γ e`: the ring homomorphism `R[[Γ]] →+* S[[Γ]]` and
  ring isomorphism `R[[Γ]] ≃+* S[[Γ]]` induced coefficientwise by `f : R →+* S` or `e : R ≃+* S`.
* `TauCeti.completedGroupAlgebra.baseChange R S Γ`: the canonical `S`-algebra homomorphism
  `S ⊗[R] R[[Γ]] →ₐ[S] S[[Γ]]`.
* `TauCeti.completedGroupAlgebra.baseChangeEquiv R S Γ`: the `S`-algebra isomorphism
  `S ⊗[R] R[[Γ]] ≃ₐ[S] S[[Γ]]` when `S` is finitely generated and projective over `R`.
* `TauCeti.completedGroupAlgebra.coordAddEquiv`,
  `TauCeti.completedGroupAlgebra.coordContinuousAddEquiv`: the additive equivalence
  `S[[Γ]] ≃+ (ι → R[[Γ]])` attached to a finite `R`-basis of `S`, upgraded to
  `S[[Γ]] ≃ₜ+ (ι → R[[Γ]])` when `S` carries the `R`-module topology.

## Main results

* `TauCeti.completedGroupAlgebra.proj_mapAddMonoidHom`,
  `TauCeti.completedGroupAlgebra.mapAddMonoidHom_of`,
  `TauCeti.completedGroupAlgebra.mapAddMonoidHom_smul_of`,
  `TauCeti.completedGroupAlgebra.mapAddMonoidHom_smul_one`: levelwise, group-element, and
  linear-form formulas for `mapAddMonoidHom`, together with `mapAddMonoidHom_one`,
  `mapAddMonoidHom_algebraMap`, `mapAddMonoidHom_zero`, `mapAddMonoidHom_add`,
  `mapAddMonoidHom_neg`, `mapAddMonoidHom_id`, `mapAddMonoidHom_comp`,
  `mapAddMonoidHom_toAddMonoidHom`, `mapAddMonoidHom_injective`, and `continuous_mapAddMonoidHom`.
* `TauCeti.completedGroupAlgebra.proj_mapRingHom`,
  `TauCeti.completedGroupAlgebra.coeff_proj_mapRingHom`,
  `TauCeti.completedGroupAlgebra.mapRingHom_of`,
  `TauCeti.completedGroupAlgebra.mapRingHom_smul`: levelwise, group-element, and semilinearity
  formulas for `mapRingHom`, together with `mapRingHom_id`, `mapRingHom_comp`,
  `mapRingHom_injective`, and `continuous_mapRingHom`.
* `TauCeti.completedGroupAlgebra.baseChange_bijective`: `baseChange R S Γ` is bijective whenever
  `S` is finitely generated and projective over `R`.
* `TauCeti.completedGroupAlgebra.baseChange_self`,
  `TauCeti.completedGroupAlgebra.baseChangeEquiv_self`,
  `TauCeti.completedGroupAlgebra.baseChangeEquiv_symm_baseChange`,
  `TauCeti.completedGroupAlgebra.baseChange_baseChangeEquiv_symm`,
  `TauCeti.completedGroupAlgebra.baseChangeEquiv_symm_mapRingHom`,
  `TauCeti.completedGroupAlgebra.baseChangeEquiv_symm_of`,
  `TauCeti.completedGroupAlgebra.baseChangeEquiv_symm_apply_of_dual`,
  `TauCeti.completedGroupAlgebra.baseChangeEquiv_symm_apply`: inverse cancellation, self-base-change
  normalization, pure-tensor and generator normal forms, and dual-family and basis decompositions
  of `(baseChangeEquiv R S Γ).symm`.

## References

* L. Ribes and P. Zalesskii, *Profinite Groups*, Section 5.3.
* J. Rodrigues Jacinto and C. Williams, *An introduction to p-adic L-functions*, Section 3.3,
  Proposition 3.16.
-/

public noncomputable section

open scoped TensorProduct

namespace TauCeti

namespace completedGroupAlgebra

universe u v w z

section MapCoefficients

variable {R : Type u} [CommRing R] {S : Type w} [CommRing S] {T : Type z} [CommRing T]
  (Γ : Type v) [Group Γ] [TopologicalSpace Γ]

/-- Applying an additive homomorphism `f : R →+ S` to every coefficient at every open-normal
quotient level defines an additive homomorphism `R[[Γ]] →+ S[[Γ]]`. For coordinate forms of a
finite basis or dual pair, this extracts the scalar coordinates of an element of `S[[Γ]]`. -/
def mapAddMonoidHom (f : R →+ S) : completedGroupAlgebra R Γ →+ completedGroupAlgebra S Γ where
  toFun x := mk S Γ (fun U ↦ MonoidAlgebra.map f (proj R Γ U x)) fun U V hUV ↦ by
    rw [MonoidAlgebra.mapDomain_map, mapDomain_mapOfLE_proj hUV]
  map_zero' := ext fun U ↦ by simp [proj_mk]
  map_add' x y := ext fun U ↦ by simp [proj_mk, MonoidAlgebra.map_add]

variable {Γ}

/-- At level `U`, `mapAddMonoidHom Γ f` applies `MonoidAlgebra.map f` to the projection at `U`. -/
@[simp]
theorem proj_mapAddMonoidHom (f : R →+ S) (U : OpenNormalSubgroup Γ)
    (x : completedGroupAlgebra R Γ) :
    proj S Γ U (mapAddMonoidHom Γ f x) = MonoidAlgebra.map f (proj R Γ U x) := by
  rw [mapAddMonoidHom, AddMonoidHom.coe_mk, ZeroHom.coe_mk, proj_mk]

/-- Each coefficient of `mapAddMonoidHom Γ f x` at level `U` is `f` applied to the corresponding
coefficient of `x`. -/
theorem coeff_proj_mapAddMonoidHom (f : R →+ S) (U : OpenNormalSubgroup Γ)
    (x : completedGroupAlgebra R Γ) (a : Γ ⧸ U.toSubgroup) :
    (proj S Γ U (mapAddMonoidHom Γ f x)).coeff a = f ((proj R Γ U x).coeff a) := by
  simp [proj_mapAddMonoidHom]

/-- Additive coefficient change sends the group element `of R Γ γ` to `f 1 • of S Γ γ`. -/
@[simp]
theorem mapAddMonoidHom_of (f : R →+ S) (γ : Γ) :
    mapAddMonoidHom Γ f (of R Γ γ) = f 1 • of S Γ γ :=
  ext fun U ↦ by simp [proj_of, MonoidAlgebra.smul_single]

/-- Additive coefficient change sends `1 : R[[Γ]]` to `f 1 • 1`. -/
@[simp]
theorem mapAddMonoidHom_one (f : R →+ S) :
    mapAddMonoidHom Γ f 1 = f 1 • 1 :=
  ext fun U ↦ by simp [MonoidAlgebra.one_def, MonoidAlgebra.smul_single]

/-- Additive coefficient change sends `algebraMap R R[[Γ]] r` to `f r • 1`. -/
@[simp]
theorem mapAddMonoidHom_algebraMap (f : R →+ S) (r : R) :
    mapAddMonoidHom Γ f (algebraMap R (completedGroupAlgebra R Γ) r) = f r • 1 :=
  ext fun U ↦ by
    simp [Algebra.algebraMap_eq_smul_one, MonoidAlgebra.one_def, MonoidAlgebra.smul_single]

variable (Γ) in
/-- Additive coefficient change along the zero homomorphism is the zero homomorphism. -/
@[simp]
theorem mapAddMonoidHom_zero :
    mapAddMonoidHom Γ (0 : R →+ S) = 0 :=
  AddMonoidHom.ext fun x ↦ ext fun U ↦ MonoidAlgebra.coeff_injective <| Finsupp.ext fun a ↦ by
    simp

/-- Additive coefficient change distributes over addition of additive homomorphisms. -/
@[simp]
theorem mapAddMonoidHom_add (f g : R →+ S) :
    mapAddMonoidHom Γ (f + g) = mapAddMonoidHom Γ f + mapAddMonoidHom Γ g :=
  AddMonoidHom.ext fun x ↦ ext fun U ↦ MonoidAlgebra.coeff_injective <| Finsupp.ext fun a ↦ by
    simp

/-- Additive coefficient change commutes with negation of additive homomorphisms. -/
@[simp]
theorem mapAddMonoidHom_neg (f : R →+ S) :
    mapAddMonoidHom Γ (-f) = -mapAddMonoidHom Γ f :=
  AddMonoidHom.ext fun x ↦ ext fun U ↦ MonoidAlgebra.coeff_injective <| Finsupp.ext fun a ↦ by
    simp

variable (Γ) in
/-- Additive coefficient change along the identity homomorphism is the identity. -/
@[simp]
theorem mapAddMonoidHom_id :
    mapAddMonoidHom Γ (AddMonoidHom.id R) = AddMonoidHom.id (completedGroupAlgebra R Γ) :=
  AddMonoidHom.ext fun x ↦ ext fun U ↦ by simp

/-- Additive coefficient change is functorial under composition of additive homomorphisms. -/
@[simp]
theorem mapAddMonoidHom_comp (g : S →+ T) (f : R →+ S) :
    mapAddMonoidHom Γ (g.comp f) = (mapAddMonoidHom Γ g).comp (mapAddMonoidHom Γ f) :=
  AddMonoidHom.ext fun x ↦ ext fun U ↦ by simp

/-- Additive coefficient change along an injective additive homomorphism is injective. -/
theorem mapAddMonoidHom_injective {f : R →+ S} (hf : Function.Injective f) :
    Function.Injective (mapAddMonoidHom Γ f) := fun x y h ↦
  ext fun U ↦ MonoidAlgebra.coeff_injective <| Finsupp.ext fun a ↦ hf <| by
    simpa only [coeff_proj_mapAddMonoidHom] using
      congrArg (fun z ↦ (proj S Γ U z).coeff a) h

/-- When `f : R →+ S` is continuous, `mapAddMonoidHom Γ f` is continuous for the inverse-limit
topologies. -/
theorem continuous_mapAddMonoidHom [TopologicalSpace R] [TopologicalSpace S] {f : R →+ S}
    (hf : Continuous f) : Continuous (mapAddMonoidHom Γ f) :=
  continuous_iff.mpr fun U a ↦ by
    simp only [coeff_proj_mapAddMonoidHom]
    exact hf.comp (continuous_coeff_proj R Γ U a)

variable (Γ) in
/-- **Change of coefficients of the completed group algebra.** A ring homomorphism `f : R →+* S`
induces a ring homomorphism `R[[Γ]] →+* S[[Γ]]` by applying `f` to every coefficient at every
open-normal quotient level (`proj_mapRingHom`, `coeff_proj_mapRingHom`). -/
def mapRingHom (f : R →+* S) : completedGroupAlgebra R Γ →+* completedGroupAlgebra S Γ where
  toFun := mapAddMonoidHom Γ f.toAddMonoidHom
  map_one' := ext fun U ↦ by simp
  map_mul' x y := ext fun U ↦ by simp
  map_zero' := (mapAddMonoidHom Γ f.toAddMonoidHom).map_zero
  map_add' := (mapAddMonoidHom Γ f.toAddMonoidHom).map_add

/-- Applying `mapAddMonoidHom` to a ring homomorphism `f : R →+* S` coerced to `R →+ S` agrees with
`mapRingHom Γ f` coerced to `R[[Γ]] →+ S[[Γ]]`. -/
@[simp]
theorem mapAddMonoidHom_toAddMonoidHom (f : R →+* S) :
    mapAddMonoidHom Γ (f : R →+ S) =
      (mapRingHom Γ f : completedGroupAlgebra R Γ →+ completedGroupAlgebra S Γ) :=
  (rfl)

/-- At level `U`, `mapRingHom Γ f` applies `MonoidAlgebra.mapRingHom` to the projection at `U`. -/
@[simp]
theorem proj_mapRingHom (f : R →+* S) (U : OpenNormalSubgroup Γ) (x : completedGroupAlgebra R Γ) :
    proj S Γ U (mapRingHom Γ f x) =
      MonoidAlgebra.mapRingHom (Γ ⧸ U.toSubgroup) f (proj R Γ U x) := by
  rw [← AddMonoidHom.coe_ofClass (mapRingHom Γ f), ← mapAddMonoidHom_toAddMonoidHom,
    proj_mapAddMonoidHom, ← MonoidAlgebra.coe_mapRingHom]

/-- Each coefficient of `mapRingHom Γ f x` at level `U` is `f` applied to the corresponding
coefficient of `x`. -/
theorem coeff_proj_mapRingHom (f : R →+* S) (U : OpenNormalSubgroup Γ)
    (x : completedGroupAlgebra R Γ) (a : Γ ⧸ U.toSubgroup) :
    (proj S Γ U (mapRingHom Γ f x)).coeff a = f ((proj R Γ U x).coeff a) := by
  simp [proj_mapRingHom]

/-- Coefficient change sends the group element `γ` in `R[[Γ]]` to `γ` in `S[[Γ]]`. -/
@[simp]
theorem mapRingHom_of (f : R →+* S) (γ : Γ) :
    mapRingHom Γ f (of R Γ γ) = of S Γ γ :=
  ext fun U ↦ by simp [proj_of]

/-- Coefficient change intertwines the scalar embeddings `R → R[[Γ]]` and `S → S[[Γ]]`. -/
@[simp]
theorem mapRingHom_algebraMap (f : R →+* S) (r : R) :
    mapRingHom Γ f (algebraMap R (completedGroupAlgebra R Γ) r) =
      algebraMap S (completedGroupAlgebra S Γ) (f r) :=
  ext fun U ↦ by
    simp [Algebra.algebraMap_eq_smul_one, MonoidAlgebra.one_def, MonoidAlgebra.smul_single]

/-- `mapRingHom Γ f` is semilinear with respect to `f`. -/
@[simp]
theorem mapRingHom_smul (f : R →+* S) (r : R) (x : completedGroupAlgebra R Γ) :
    mapRingHom Γ f (r • x) = f r • mapRingHom Γ f x := by
  rw [Algebra.smul_def, map_mul, mapRingHom_algebraMap, ← Algebra.smul_def]

variable (Γ) in
/-- Coefficient change along the identity ring homomorphism is the identity. -/
@[simp]
theorem mapRingHom_id :
    mapRingHom Γ (RingHom.id R) = RingHom.id (completedGroupAlgebra R Γ) :=
  RingHom.ext fun x ↦ ext fun U ↦ by simp

/-- Coefficient change is functorial under composition of ring homomorphisms. -/
@[simp]
theorem mapRingHom_comp (g : S →+* T) (f : R →+* S) :
    mapRingHom Γ (g.comp f) = (mapRingHom Γ g).comp (mapRingHom Γ f) :=
  RingHom.ext fun x ↦ ext fun U ↦ by simp

/-- Coefficient change along an injective ring homomorphism is injective. -/
theorem mapRingHom_injective {f : R →+* S} (hf : Function.Injective f) :
    Function.Injective (mapRingHom Γ f) := by
  simpa only [mapAddMonoidHom_toAddMonoidHom, AddMonoidHom.coe_ofClass] using
    mapAddMonoidHom_injective (Γ := Γ) (f := (f : R →+ S))
      (by simpa only [AddMonoidHom.coe_ofClass] using hf)

/-- Coefficient change along a continuous ring homomorphism is continuous for the inverse-limit
topologies. -/
theorem continuous_mapRingHom [TopologicalSpace R] [TopologicalSpace S] {f : R →+* S}
    (hf : Continuous f) : Continuous (mapRingHom Γ f) := by
  simpa only [mapAddMonoidHom_toAddMonoidHom, AddMonoidHom.coe_ofClass] using
    continuous_mapAddMonoidHom (Γ := Γ) (f := (f : R →+ S))
      (by simpa only [AddMonoidHom.coe_ofClass] using hf)

variable (Γ) in
/-- A ring isomorphism `e : R ≃+* S` induces a ring isomorphism `R[[Γ]] ≃+* S[[Γ]]`. -/
def mapRingEquiv (e : R ≃+* S) :
    completedGroupAlgebra R Γ ≃+* completedGroupAlgebra S Γ :=
  RingEquiv.ofRingHom (mapRingHom Γ (e : R →+* S)) (mapRingHom Γ (e.symm : S →+* R))
    (by simp [← mapRingHom_comp]) (by simp [← mapRingHom_comp])

@[simp]
theorem coe_mapRingEquiv (e : R ≃+* S) :
    ⇑(mapRingEquiv Γ e) = mapRingHom Γ (e : R →+* S) :=
  (rfl)

@[simp]
theorem toRingHom_mapRingEquiv (e : R ≃+* S) :
    (mapRingEquiv Γ e : completedGroupAlgebra R Γ →+* completedGroupAlgebra S Γ) =
      mapRingHom Γ (e : R →+* S) :=
  (rfl)

@[simp]
theorem mapRingEquiv_symm (e : R ≃+* S) :
    (mapRingEquiv Γ e).symm = mapRingEquiv Γ e.symm :=
  (rfl)

@[simp]
theorem mapRingEquiv_refl :
    mapRingEquiv Γ (RingEquiv.refl R) = RingEquiv.refl (completedGroupAlgebra R Γ) :=
  RingEquiv.ext fun x ↦ by simp

@[simp]
theorem mapRingEquiv_trans (e₁ : R ≃+* S) (e₂ : S ≃+* T) :
    mapRingEquiv Γ (e₁.trans e₂) = (mapRingEquiv Γ e₁).trans (mapRingEquiv Γ e₂) :=
  RingEquiv.ext fun x ↦ by simp

end MapCoefficients

section BaseChange

variable (R : Type u) [CommRing R] (S : Type w) [CommRing S] [Algebra R S]
  (Γ : Type v) [Group Γ] [TopologicalSpace Γ]

variable {R S Γ} in
/-- Applying an `R`-linear form `g : S →ₗ[R] R` coefficientwise to an element extended from
`R[[Γ]]` and scaled by `s : S` multiplies the original element by `g s`. -/
@[simp]
theorem mapAddMonoidHom_smul_mapRingHom (g : S →ₗ[R] R) (s : S) (x : completedGroupAlgebra R Γ) :
    mapAddMonoidHom Γ g.toAddMonoidHom (s • mapRingHom Γ (algebraMap R S) x) = g s • x :=
  ext fun U ↦ MonoidAlgebra.coeff_injective <| Finsupp.ext fun a ↦ by
    simp only [coeff_proj_mapAddMonoidHom, map_smul, MonoidAlgebra.coeff_smul,
      Finsupp.smul_apply, coeff_proj_mapRingHom, LinearMap.toAddMonoidHom_coe, smul_eq_mul]
    rw [mul_comm s, ← Algebra.smul_def, map_smul, smul_eq_mul, mul_comm]

variable {R S Γ} in
/-- Applying an `R`-linear form `g : S →ₗ[R] R` coefficientwise to `mapRingHom Γ (algebraMap R S) x`
multiplies `x` by `g 1`. -/
@[simp]
theorem mapAddMonoidHom_mapRingHom (g : S →ₗ[R] R) (x : completedGroupAlgebra R Γ) :
    mapAddMonoidHom Γ g.toAddMonoidHom (mapRingHom Γ (algebraMap R S) x) = g 1 • x := by
  simpa using mapAddMonoidHom_smul_mapRingHom g 1 x

variable {R S Γ} in
/-- Applying an `R`-linear form `g : S →ₗ[R] R` coefficientwise to `s • of S Γ γ` gives
`g s • of R Γ γ`. -/
@[simp]
theorem mapAddMonoidHom_smul_of (g : S →ₗ[R] R) (s : S) (γ : Γ) :
    mapAddMonoidHom Γ g.toAddMonoidHom (s • of S Γ γ) = g s • of R Γ γ := by
  rw [← mapRingHom_of (algebraMap R S) γ, mapAddMonoidHom_smul_mapRingHom]

variable {R S Γ} in
/-- Applying an `R`-linear form `g : S →ₗ[R] R` coefficientwise to `s • (1 : S[[Γ]])` gives
`g s • 1`. -/
@[simp]
theorem mapAddMonoidHom_smul_one (g : S →ₗ[R] R) (s : S) :
    mapAddMonoidHom Γ g.toAddMonoidHom (s • 1) = g s • 1 := by
  rw [← map_one (mapRingHom Γ (algebraMap R S)), mapAddMonoidHom_smul_mapRingHom]

/-- **Scalar extension to the completed group algebra.** The canonical `S`-algebra homomorphism
`S ⊗[R] R[[Γ]] →ₐ[S] S[[Γ]]` sending `s ⊗ₜ x` to `s • mapRingHom Γ (algebraMap R S) x`. -/
def baseChange : S ⊗[R] completedGroupAlgebra R Γ →ₐ[S] completedGroupAlgebra S Γ :=
  letI : Algebra R (completedGroupAlgebra S Γ) :=
    Algebra.compHom (completedGroupAlgebra S Γ) (algebraMap R S)
  haveI : IsScalarTower R S (completedGroupAlgebra S Γ) :=
    IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  AlgHom.liftEquiv R S (completedGroupAlgebra R Γ) (completedGroupAlgebra S Γ)
    { mapRingHom Γ (algebraMap R S) with
      commutes' := mapRingHom_algebraMap (algebraMap R S) }

variable {R S Γ}

/-- `baseChange R S Γ` sends a pure tensor `s ⊗ₜ x` to `s • mapRingHom Γ (algebraMap R S) x`. -/
@[simp]
theorem baseChange_tmul (s : S) (x : completedGroupAlgebra R Γ) :
    baseChange R S Γ (s ⊗ₜ[R] x) = s • mapRingHom Γ (algebraMap R S) x :=
  (rfl)

/-- Self-base-change on the completed group algebra recovers `Algebra.TensorProduct.lid`. -/
@[simp]
theorem baseChange_self :
    baseChange R R Γ =
      (Algebra.TensorProduct.lid R (completedGroupAlgebra R Γ)).toAlgHom := by
  ext x
  simp

/-- Projecting `baseChange R S Γ z` at an open normal subgroup `U` recovers levelwise base change
of `proj R Γ U`. -/
@[simp]
theorem proj_baseChange (U : OpenNormalSubgroup Γ)
    (z : S ⊗[R] completedGroupAlgebra R Γ) :
    proj S Γ U (baseChange R S Γ z) =
      LinearMap.liftBaseChange S
        (MonoidAlgebra.mapAlgHom (Γ ⧸ U.toSubgroup) (Algebra.ofId R S)).toLinearMap
        (LinearMap.lTensor S (proj R Γ U).toLinearMap z) := by
  induction z using TensorProduct.inductionOn with
  | tmul s x =>
    simp only [baseChange_tmul, map_smul, proj_mapRingHom, LinearMap.lTensor_tmul,
      AlgHom.toLinearMap_apply, LinearMap.liftBaseChange_tmul]
    ext g
    simp
  | add z₁ z₂ hz₁ hz₂ => simp [hz₁, hz₂]

section FiniteProjective

variable (R S Γ)

private theorem baseChange_bijective_of_dual [Module.Projective R S] [Module.Finite R S] :
    Function.Bijective (baseChange R S Γ) := by
  obtain ⟨n, b, φ, hsum⟩ := TauCeti.exists_sum_dual_smul_eq (R := R) (M := S)
  let inv (y : completedGroupAlgebra S Γ) : S ⊗[R] completedGroupAlgebra R Γ :=
    ∑ i : Fin n, b i ⊗ₜ[R] mapAddMonoidHom Γ (φ i).toAddMonoidHom y
  refine Function.bijective_iff_has_inverse.mpr ⟨inv, ?_, ?_⟩
  · have hadd : ∀ u v : completedGroupAlgebra S Γ, inv (u + v) = inv u + inv v :=
      fun u v ↦ by simp [inv, TensorProduct.tmul_add, Finset.sum_add_distrib]
    intro z
    induction z using TensorProduct.inductionOn with
    | tmul s x =>
      simp only [baseChange_tmul, inv, mapAddMonoidHom_smul_mapRingHom, ← TensorProduct.smul_tmul,
        ← TensorProduct.sum_tmul]
      exact congrArg (· ⊗ₜ[R] x) (hsum s)
    | add z₁ z₂ hz₁ hz₂ => rw [map_add, hadd, hz₁, hz₂]
  · intro y
    dsimp only [inv]
    rw [map_sum]
    refine ext fun U ↦ MonoidAlgebra.coeff_injective <| Finsupp.ext fun a ↦ ?_
    simp only [baseChange_tmul, map_sum, map_smul, MonoidAlgebra.coeff_sum,
      MonoidAlgebra.coeff_smul, Finsupp.finsetSum_apply, Finsupp.smul_apply, coeff_proj_mapRingHom,
      coeff_proj_mapAddMonoidHom, LinearMap.toAddMonoidHom_coe, smul_eq_mul, mul_comm (b _),
      ← Algebra.smul_def]
    exact hsum ((proj S Γ U y).coeff a)

variable [Module.Projective R S] [Module.Finite R S]

/-- **Finite projective base change of the completed group algebra.** When `S` is finitely
generated and projective over `R`, `baseChange R S Γ : S ⊗[R] R[[Γ]] →ₐ[S] S[[Γ]]` is
bijective. -/
theorem baseChange_bijective : Function.Bijective (baseChange R S Γ) :=
  baseChange_bijective_of_dual R S Γ

/-- **Finite projective base-change equivalence for the completed group algebra.** When `S` is
finitely generated and projective as an `R`-module, `S ⊗[R] R[[Γ]]` is canonically isomorphic as an
`S`-algebra to `S[[Γ]]`. -/
def baseChangeEquiv : S ⊗[R] completedGroupAlgebra R Γ ≃ₐ[S] completedGroupAlgebra S Γ :=
  AlgEquiv.ofBijective (baseChange R S Γ) (baseChange_bijective R S Γ)

variable {R S Γ}

/-- The forward map of `baseChangeEquiv R S Γ` is `baseChange R S Γ`. -/
@[simp]
theorem coe_baseChangeEquiv : ⇑(baseChangeEquiv R S Γ) = baseChange R S Γ :=
  (rfl)

/-- Forgetting invertibility of `baseChangeEquiv R S Γ` gives `baseChange R S Γ`. -/
@[simp]
theorem toAlgHom_baseChangeEquiv : (baseChangeEquiv R S Γ).toAlgHom = baseChange R S Γ :=
  (rfl)

/-- `baseChangeEquiv R S Γ` sends `s ⊗ₜ x` to `s • mapRingHom Γ (algebraMap R S) x`. -/
@[simp]
theorem baseChangeEquiv_tmul (s : S) (x : completedGroupAlgebra R Γ) :
    baseChangeEquiv R S Γ (s ⊗ₜ[R] x) = s • mapRingHom Γ (algebraMap R S) x :=
  (rfl)

/-- `(baseChangeEquiv R S Γ).symm` is a left inverse to `baseChange R S Γ`. -/
@[simp]
theorem baseChangeEquiv_symm_baseChange (z : S ⊗[R] completedGroupAlgebra R Γ) :
    (baseChangeEquiv R S Γ).symm (baseChange R S Γ z) = z :=
  (baseChangeEquiv R S Γ).symm_apply_apply z

/-- `baseChange R S Γ` is a right inverse to `(baseChangeEquiv R S Γ).symm`. -/
@[simp]
theorem baseChange_baseChangeEquiv_symm (y : completedGroupAlgebra S Γ) :
    baseChange R S Γ ((baseChangeEquiv R S Γ).symm y) = y :=
  (baseChangeEquiv R S Γ).apply_symm_apply y

/-- `(baseChangeEquiv R S Γ).symm` sends an element extended along `algebraMap R S` to `1 ⊗ₜ x`. -/
@[simp]
theorem baseChangeEquiv_symm_mapRingHom (x : completedGroupAlgebra R Γ) :
    (baseChangeEquiv R S Γ).symm (mapRingHom Γ (algebraMap R S) x) = 1 ⊗ₜ[R] x := by
  apply (baseChangeEquiv R S Γ).injective
  simp

/-- `(baseChangeEquiv R S Γ).symm` sends the group element `of S Γ γ` to `1 ⊗ₜ of R Γ γ`. -/
@[simp]
theorem baseChangeEquiv_symm_of (γ : Γ) :
    (baseChangeEquiv R S Γ).symm (of S Γ γ) = 1 ⊗ₜ[R] of R Γ γ := by
  rw [← mapRingHom_of (algebraMap R S) γ, baseChangeEquiv_symm_mapRingHom]

/-- Given a finite dual family `(b, φ)` for `S` over `R` satisfying
`∀ s, ∑ i, φ i s • b i = s`, `(baseChangeEquiv R S Γ).symm y` decomposes as
`∑ i, b i ⊗ₜ mapAddMonoidHom Γ (φ i).toAddMonoidHom y`. -/
theorem baseChangeEquiv_symm_apply_of_dual {ι : Type*} [Fintype ι]
    {b : ι → S} {φ : ι → Module.Dual R S} (hsum : ∀ s : S, ∑ i, φ i s • b i = s)
    (y : completedGroupAlgebra S Γ) :
    (baseChangeEquiv R S Γ).symm y =
      ∑ i : ι, b i ⊗ₜ[R] mapAddMonoidHom Γ (φ i).toAddMonoidHom y := by
  apply (baseChangeEquiv R S Γ).injective
  rw [AlgEquiv.apply_symm_apply, coe_baseChangeEquiv, map_sum]
  refine ext fun U ↦ MonoidAlgebra.coeff_injective <| Finsupp.ext fun a ↦ ?_
  simp only [baseChange_tmul, map_sum, map_smul, MonoidAlgebra.coeff_sum, MonoidAlgebra.coeff_smul,
    Finsupp.finsetSum_apply, Finsupp.smul_apply, coeff_proj_mapRingHom,
    coeff_proj_mapAddMonoidHom, LinearMap.toAddMonoidHom_coe, smul_eq_mul, mul_comm (b _),
    ← Algebra.smul_def]
  exact (hsum ((proj S Γ U y).coeff a)).symm

/-- In any finite `R`-basis `b` of `S`, `(baseChangeEquiv R S Γ).symm y` decomposes as
`∑ i, b i ⊗ₜ mapAddMonoidHom Γ (b.coord i).toAddMonoidHom y`. -/
theorem baseChangeEquiv_symm_apply {ι : Type*} [Fintype ι] (b : Module.Basis ι R S)
    (y : completedGroupAlgebra S Γ) :
    (baseChangeEquiv R S Γ).symm y =
      ∑ i : ι, b i ⊗ₜ[R] mapAddMonoidHom Γ (b.coord i).toAddMonoidHom y :=
  baseChangeEquiv_symm_apply_of_dual (b := b) (φ := b.coord) (fun s ↦ b.sum_repr s) y

/-- Base change from `R` to `R` itself recovers `Algebra.TensorProduct.lid`. -/
@[simp]
theorem baseChangeEquiv_self :
    baseChangeEquiv R R Γ = Algebra.TensorProduct.lid R (completedGroupAlgebra R Γ) :=
  AlgEquiv.coe_toAlgHom_injective (by simp)

end FiniteProjective

end BaseChange

section Coordinates

variable {R : Type u} [CommRing R] {S : Type w} [CommRing S] [Algebra R S]
  (Γ : Type v) [Group Γ] [TopologicalSpace Γ] {ι : Type*} (b : Module.Basis ι R S)

/-- Given a finite `R`-basis `b` of `S`, taking the `b`-coordinates of every levelwise coefficient
identifies `S[[Γ]]` with `ι → R[[Γ]]` as an additive group. -/
def coordAddEquiv [Finite ι] :
    completedGroupAlgebra S Γ ≃+ (ι → completedGroupAlgebra R Γ) where
  toFun y i := mapAddMonoidHom Γ (b.coord i).toAddMonoidHom y
  invFun c :=
    let _ := Fintype.ofFinite ι
    ∑ i : ι, b i • mapRingHom Γ (algebraMap R S) (c i)
  left_inv y := by
    let _ := Fintype.ofFinite ι
    refine ext fun U ↦ MonoidAlgebra.coeff_injective <| Finsupp.ext fun q ↦ ?_
    simp only [map_sum, MonoidAlgebra.coeff_sum, Finsupp.finsetSum_apply, map_smul,
      MonoidAlgebra.coeff_smul_apply, coeff_proj_mapRingHom, coeff_proj_mapAddMonoidHom,
      LinearMap.toAddMonoidHom_coe, Module.Basis.coord_apply, smul_eq_mul, mul_comm (b _),
      ← Algebra.smul_def]
    exact b.sum_repr ((proj S Γ U y).coeff q)
  right_inv c := by
    classical
    let _ := Fintype.ofFinite ι
    exact funext fun i ↦ by simp [b.repr_self]
  map_add' x y := funext fun i ↦ map_add _ x y

variable {Γ}

@[simp]
theorem coordAddEquiv_apply [Finite ι]
    (y : completedGroupAlgebra S Γ) (i : ι) :
    coordAddEquiv Γ b y i = mapAddMonoidHom Γ (b.coord i).toAddMonoidHom y :=
  (rfl)

@[simp]
theorem coordAddEquiv_symm_apply [Fintype ι]
    (c : ι → completedGroupAlgebra R Γ) :
    (coordAddEquiv Γ b).symm c =
      ∑ i : ι, b i • mapRingHom Γ (algebraMap R S) (c i) := by
  simp only [coordAddEquiv, AddEquiv.symm_apply_eq]
  ext i
  classical
  simp [b.repr_self]

variable [TopologicalSpace R] [IsTopologicalRing R] [TopologicalSpace S] [IsModuleTopology R S]

variable (Γ) in
/-- Given a finite `R`-basis `b` of `S`, when `S` carries the `R`-module topology, taking the
`b`-coordinates of every levelwise coefficient identifies `S[[Γ]]` with `ι → R[[Γ]]` as a
topological additive group. -/
def coordContinuousAddEquiv [Finite ι] :
    completedGroupAlgebra S Γ ≃ₜ+ (ι → completedGroupAlgebra R Γ) where
  __ := coordAddEquiv Γ b
  continuous_toFun := continuous_pi fun i ↦
    continuous_mapAddMonoidHom (IsModuleTopology.continuous_of_linearMap (b.coord i))
  continuous_invFun := by
    let _ : ContinuousAdd S := IsModuleTopology.toContinuousAdd R S
    have := IsModuleTopology.toContinuousSMul R S
    let _ := Fintype.ofFinite ι
    refine continuous_iff.mpr fun U q ↦ ?_
    simp only [AddEquiv.invFun_eq_symm, coordAddEquiv_symm_apply, map_sum,
      MonoidAlgebra.coeff_sum, Finsupp.finsetSum_apply, map_smul,
      MonoidAlgebra.coeff_smul_apply, coeff_proj_mapRingHom, smul_eq_mul, mul_comm (b _),
      ← Algebra.smul_def]
    exact continuous_finsetSum _ fun i _ ↦
      ((continuous_coeff_proj R Γ U q).comp (continuous_apply i)).smul continuous_const

@[simp]
theorem toAddEquiv_coordContinuousAddEquiv [Finite ι] :
    (coordContinuousAddEquiv Γ b :
      completedGroupAlgebra S Γ ≃+ (ι → completedGroupAlgebra R Γ)) =
        coordAddEquiv Γ b :=
  (rfl)

@[simp]
theorem coordContinuousAddEquiv_apply [Finite ι]
    (y : completedGroupAlgebra S Γ) (i : ι) :
    coordContinuousAddEquiv Γ b y i = mapAddMonoidHom Γ (b.coord i).toAddMonoidHom y :=
  (rfl)

@[simp]
theorem coordContinuousAddEquiv_symm_apply [Fintype ι]
    (c : ι → completedGroupAlgebra R Γ) :
    (coordContinuousAddEquiv Γ b).symm c =
      ∑ i : ι, b i • mapRingHom Γ (algebraMap R S) (c i) := by
  rw [ContinuousAddEquiv.symm_apply_eq, ← coordAddEquiv_symm_apply]
  ext i
  rw [coordContinuousAddEquiv_apply, ← coordAddEquiv_apply, AddEquiv.apply_symm_apply]

end Coordinates

end completedGroupAlgebra

end TauCeti
