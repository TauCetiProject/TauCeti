/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.FreeModule.Finite.Basic
public import Mathlib.RingTheory.TensorProduct.Basic
public import TauCeti.Topology.Algebra.Group.Profinite.CompletedGroupAlgebra.Basic

/-!
# Change of coefficients for the completed group algebra

An additive homomorphism `f : R →+ S` applies coefficientwise at every finite-quotient level
`R[Γ ⧸ U] → S[Γ ⧸ U]`, and compatibility along the quotient maps `Γ ⧸ U → Γ ⧸ V` assembles these
level maps into an additive homomorphism
`completedGroupAlgebra.mapAddMonoidHom Γ f : R[[Γ]] →+ S[[Γ]]`. For a ring homomorphism
`f : R →+* S` this upgrades to a ring homomorphism
`completedGroupAlgebra.mapRingHom Γ f : R[[Γ]] →+* S[[Γ]]` sending each group element `of R Γ γ`
to `of S Γ γ`. When `S` is an `R`-algebra, scalar multiplication on the left combines with
`mapRingHom Γ (algebraMap R S)` into an `S`-algebra homomorphism
`completedGroupAlgebra.baseChange R S Γ : S ⊗[R] R[[Γ]] →ₐ[S] S[[Γ]]`.

In general an inverse limit does not commute with tensor products. When `S` is finite and free as
an `R`-module, however, choosing a finite `R`-basis `(b_i)` of `S` splits every coefficient in
`S[Γ ⧸ U]` into finitely many `R`-coordinates. Each coordinate linear form `b.coord i : S →ₗ[R] R`
acts levelwise on `S[[Γ]]` through `mapAddMonoidHom`, and reassembling along `(b_i)` furnishes the
two-sided inverse to `baseChange R S Γ`. Thus
`completedGroupAlgebra.baseChangeEquiv R S Γ : S ⊗[R] R[[Γ]] ≃ₐ[S] S[[Γ]]` is an isomorphism of
`S`-algebras without any topological or finiteness assumption on `Γ` or `R`.

## Main definitions

* `TauCeti.completedGroupAlgebra.mapAddMonoidHom Γ f`: the additive homomorphism
  `R[[Γ]] →+ S[[Γ]]` applying `f : R →+ S` to every level coefficient.
* `TauCeti.completedGroupAlgebra.mapRingHom Γ f`: the ring homomorphism `R[[Γ]] →+* S[[Γ]]`
  induced coefficientwise by `f : R →+* S`.
* `TauCeti.completedGroupAlgebra.baseChange R S Γ`: the canonical `S`-algebra homomorphism
  `S ⊗[R] R[[Γ]] →ₐ[S] S[[Γ]]`.
* `TauCeti.completedGroupAlgebra.baseChangeEquiv R S Γ`: the `S`-algebra isomorphism
  `S ⊗[R] R[[Γ]] ≃ₐ[S] S[[Γ]]` when `S` is finite and free over `R`.

## Main results

* `TauCeti.completedGroupAlgebra.proj_mapRingHom`,
  `TauCeti.completedGroupAlgebra.coeff_proj_mapRingHom`,
  `TauCeti.completedGroupAlgebra.mapRingHom_of`: levelwise and group-element formulas for
  `mapRingHom`, together with `mapRingHom_id`, `mapRingHom_comp`, `mapRingHom_injective`, and
  `continuous_mapRingHom`.
* `TauCeti.completedGroupAlgebra.baseChange_bijective`: `baseChange R S Γ` is bijective whenever
  `S` is finite and free over `R`.
* `TauCeti.completedGroupAlgebra.baseChangeEquiv_symm_apply`: explicit decomposition of
  `(baseChangeEquiv R S Γ).symm` in any finite `R`-basis of `S`.

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
finite basis, this extracts the scalar coordinates of an element of `S[[Γ]]`. -/
def mapAddMonoidHom (f : R →+ S) : completedGroupAlgebra R Γ →+ completedGroupAlgebra S Γ where
  toFun x := mk S Γ
    (fun U ↦ MonoidAlgebra.map f (proj R Γ U x))
    fun U V hUV ↦ by
      apply MonoidAlgebra.coeff_injective
      rw [MonoidAlgebra.coeff_mapDomain, MonoidAlgebra.coeff_map, MonoidAlgebra.coeff_map,
        ← mapDomain_mapOfLE_proj hUV x, MonoidAlgebra.coeff_mapDomain]
      exact Finsupp.mapDomain_mapRange (QuotientGroup.mapOfLE hUV) (proj R Γ U x).coeff f
        (map_zero f) (map_add f)
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
  map_one' := ext fun U ↦ by simp [proj_mapAddMonoidHom]
  map_mul' x y := ext fun U ↦ by simp [proj_mapAddMonoidHom]
  map_zero' := (mapAddMonoidHom Γ f.toAddMonoidHom).map_zero
  map_add' := (mapAddMonoidHom Γ f.toAddMonoidHom).map_add

/-- Forgetting multiplication on `mapRingHom Γ f` recovers `mapAddMonoidHom Γ f.toAddMonoidHom`. -/
theorem toAddMonoidHom_mapRingHom (f : R →+* S) :
    (mapRingHom Γ f).toAddMonoidHom = mapAddMonoidHom Γ f.toAddMonoidHom :=
  (rfl)

/-- At level `U`, `mapRingHom Γ f` applies `MonoidAlgebra.mapRingHom` to the projection at `U`. -/
@[simp]
theorem proj_mapRingHom (f : R →+* S) (U : OpenNormalSubgroup Γ) (x : completedGroupAlgebra R Γ) :
    proj S Γ U (mapRingHom Γ f x) =
      MonoidAlgebra.mapRingHom (Γ ⧸ U.toSubgroup) f (proj R Γ U x) :=
  proj_mapAddMonoidHom f.toAddMonoidHom U x

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
    Function.Injective (mapRingHom Γ f) := fun x y h ↦
  ext fun U ↦ MonoidAlgebra.coeff_injective <| Finsupp.ext fun a ↦ hf <| by
    simpa only [coeff_proj_mapRingHom] using
      congrArg (fun z ↦ (proj S Γ U z).coeff a) h

/-- Coefficient change along a continuous ring homomorphism is continuous for the inverse-limit
topologies. -/
theorem continuous_mapRingHom [TopologicalSpace R] [TopologicalSpace S] {f : R →+* S}
    (hf : Continuous f) : Continuous (mapRingHom Γ f) :=
  continuous_mapAddMonoidHom hf

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
    rw [coeff_proj_mapAddMonoidHom, map_smul, MonoidAlgebra.coeff_smul, Finsupp.smul_apply,
      coeff_proj_mapRingHom, smul_eq_mul, mul_comm, ← Algebra.smul_def,
      LinearMap.toAddMonoidHom_coe, map_smul, map_smul, MonoidAlgebra.coeff_smul,
      Finsupp.smul_apply, smul_eq_mul, mul_comm, smul_eq_mul]

/-- Additive bilinear lift underlying `baseChange`. -/
private def baseChangeAddHom : S ⊗[R] completedGroupAlgebra R Γ →+ completedGroupAlgebra S Γ :=
  TensorProduct.liftAddHom
    { toFun s :=
        { toFun x := s • mapRingHom Γ (algebraMap R S) x
          map_zero' := by simp
          map_add' x y := by simp [smul_add] }
      map_zero' := by ext; simp
      map_add' s t := by ext; simp [add_smul] }
    fun r s x ↦ by
      simp only [AddMonoidHom.coe_mk, ZeroHom.coe_mk, Algebra.smul_def, map_mul,
        mapRingHom_algebraMap]
      rw [← map_mul, mul_comm, map_mul, mul_assoc]

/-- **Scalar extension to the completed group algebra.** The canonical `S`-algebra homomorphism
`S ⊗[R] R[[Γ]] →ₐ[S] S[[Γ]]` sending `s ⊗ₜ x` to `s • mapRingHom Γ (algebraMap R S) x`. -/
def baseChange : S ⊗[R] completedGroupAlgebra R Γ →ₐ[S] completedGroupAlgebra S Γ where
  toFun := baseChangeAddHom R S Γ
  map_one' := by
    rw [Algebra.TensorProduct.one_def]
    simp [baseChangeAddHom]
  map_mul' z w := by
    refine TensorProduct.inductionOn z ?_ fun z₁ z₂ hz₁ hz₂ ↦ by
      rw [add_mul, map_add, map_add, add_mul, hz₁, hz₂]
    intro s₁ x₁
    refine TensorProduct.inductionOn w ?_ fun w₁ w₂ hw₁ hw₂ ↦ by
      rw [mul_add, map_add, map_add, mul_add, hw₁, hw₂]
    intro s₂ x₂
    simp [baseChangeAddHom, smul_smul, mul_comm s₁ s₂]
  map_zero' := (baseChangeAddHom R S Γ).map_zero
  map_add' := (baseChangeAddHom R S Γ).map_add
  commutes' s := by
    rw [Algebra.TensorProduct.algebraMap_apply]
    simp [baseChangeAddHom, Algebra.algebraMap_eq_smul_one]

variable {R S Γ}

/-- `baseChange R S Γ` sends a pure tensor `s ⊗ₜ x` to `s • mapRingHom Γ (algebraMap R S) x`. -/
@[simp]
theorem baseChange_tmul (s : S) (x : completedGroupAlgebra R Γ) :
    baseChange R S Γ (s ⊗ₜ[R] x) = s • mapRingHom Γ (algebraMap R S) x :=
  (rfl)

/-- `baseChange R S Γ` sends `1 ⊗ₜ x` to `mapRingHom Γ (algebraMap R S) x`. -/
theorem baseChange_one_tmul (x : completedGroupAlgebra R Γ) :
    baseChange R S Γ ((1 : S) ⊗ₜ[R] x) = mapRingHom Γ (algebraMap R S) x := by
  simp

/-- `baseChange R S Γ` sends `s ⊗ₜ of R Γ γ` to `s • of S Γ γ`. -/
theorem baseChange_tmul_of (s : S) (γ : Γ) :
    baseChange R S Γ (s ⊗ₜ[R] of R Γ γ) = s • of S Γ γ := by
  simp

/-- At level `U`, the `a`-th coefficient of `baseChange R S Γ (s ⊗ₜ x)` is `s` times the image of
the `a`-th coefficient of `x`. -/
theorem coeff_proj_baseChange_tmul (s : S) (x : completedGroupAlgebra R Γ)
    (U : OpenNormalSubgroup Γ) (a : Γ ⧸ U.toSubgroup) :
    (proj S Γ U (baseChange R S Γ (s ⊗ₜ[R] x))).coeff a =
      s * algebraMap R S ((proj R Γ U x).coeff a) := by
  simp

section FiniteFree

variable (R S Γ)

/-- Coordinate decomposition map `S[[Γ]] →+ S ⊗[R] R[[Γ]]` associated to a finite `R`-basis of `S`,
used to invert `baseChange R S Γ`. -/
private def baseChangeInvAux {ι : Type*} [Fintype ι] (b : Module.Basis ι R S) :
    completedGroupAlgebra S Γ →+ S ⊗[R] completedGroupAlgebra R Γ where
  toFun y := ∑ i : ι, b i ⊗ₜ[R] mapAddMonoidHom Γ (b.coord i).toAddMonoidHom y
  map_zero' := by simp
  map_add' y z := by simp [TensorProduct.tmul_add, Finset.sum_add_distrib]

private theorem baseChangeInvAux_comp_baseChange {ι : Type*} [Fintype ι]
    (b : Module.Basis ι R S) (z : S ⊗[R] completedGroupAlgebra R Γ) :
    baseChangeInvAux R S Γ b (baseChange R S Γ z) = z := by
  refine TensorProduct.inductionOn z ?_ ?_
  · intro s x
    simp only [baseChange_tmul, baseChangeInvAux, AddMonoidHom.coe_mk, ZeroHom.coe_mk,
      mapAddMonoidHom_smul_mapRingHom]
    simp_rw [← TensorProduct.smul_tmul, ← TensorProduct.sum_tmul, Module.Basis.coord_apply,
      b.sum_repr]
  · intro z₁ z₂ hz₁ hz₂
    rw [map_add, map_add, hz₁, hz₂]

private theorem baseChange_comp_baseChangeInvAux {ι : Type*} [Fintype ι]
    (b : Module.Basis ι R S) (y : completedGroupAlgebra S Γ) :
    baseChange R S Γ (baseChangeInvAux R S Γ b y) = y := by
  simp only [baseChangeInvAux, AddMonoidHom.coe_mk, ZeroHom.coe_mk, map_sum, baseChange_tmul]
  apply ext
  intro U
  apply MonoidAlgebra.coeff_injective
  ext a
  simp only [map_sum, map_smul, MonoidAlgebra.coeff_sum, MonoidAlgebra.coeff_smul,
    Finsupp.finsetSum_apply, Finsupp.smul_apply, coeff_proj_mapRingHom,
    coeff_proj_mapAddMonoidHom, LinearMap.toAddMonoidHom_coe, Module.Basis.coord_apply,
    smul_eq_mul, mul_comm (b _), ← Algebra.smul_def]
  exact b.sum_repr ((proj S Γ U y).coeff a)

variable [Module.Free R S] [Module.Finite R S]

/-- **Finite free base change of the completed group algebra.** When `S` is finite and free over
`R`, `baseChange R S Γ : S ⊗[R] R[[Γ]] →ₐ[S] S[[Γ]]` is bijective. -/
theorem baseChange_bijective : Function.Bijective (baseChange R S Γ) :=
  let b := Module.Free.chooseBasis R S
  ⟨Function.LeftInverse.injective (baseChangeInvAux_comp_baseChange R S Γ b),
    Function.RightInverse.surjective (baseChange_comp_baseChangeInvAux R S Γ b)⟩

/-- **Finite free base-change equivalence for the completed group algebra.** When `S` is finite and
free as an `R`-module, `S ⊗[R] R[[Γ]]` is canonically isomorphic as an `S`-algebra to `S[[Γ]]`. -/
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

/-- `baseChangeEquiv R S Γ` sends `s ⊗ₜ of R Γ γ` to `s • of S Γ γ`. -/
theorem baseChangeEquiv_tmul_of (s : S) (γ : Γ) :
    baseChangeEquiv R S Γ (s ⊗ₜ[R] of R Γ γ) = s • of S Γ γ :=
  baseChange_tmul_of s γ

/-- In any finite `R`-basis `b` of `S`, `(baseChangeEquiv R S Γ).symm y` decomposes as
`∑ i, b i ⊗ₜ mapAddMonoidHom Γ (b.coord i).toAddMonoidHom y`. -/
theorem baseChangeEquiv_symm_apply {ι : Type*} [Fintype ι] (b : Module.Basis ι R S)
    (y : completedGroupAlgebra S Γ) :
    (baseChangeEquiv R S Γ).symm y =
      ∑ i : ι, b i ⊗ₜ[R] mapAddMonoidHom Γ (b.coord i).toAddMonoidHom y := by
  apply (baseChangeEquiv R S Γ).injective
  rw [AlgEquiv.apply_symm_apply, coe_baseChangeEquiv]
  exact (baseChange_comp_baseChangeInvAux R S Γ b y).symm

end FiniteFree

/-! Over `S = R`, scalar extension recovers the left identity of the tensor product. -/

example (R : Type u) [CommRing R] (Γ : Type v) [Group Γ] [TopologicalSpace Γ] :
    baseChangeEquiv R R Γ = Algebra.TensorProduct.lid R (completedGroupAlgebra R Γ) :=
  AlgEquiv.ext fun z ↦
    TensorProduct.inductionOn z (fun r x ↦ by simp) fun z₁ z₂ hz₁ hz₂ ↦ by
      rw [map_add, map_add, hz₁, hz₂]

end BaseChange

end completedGroupAlgebra

end TauCeti
