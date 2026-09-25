/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Algebra.Pi
public import Mathlib.Algebra.Algebra.Subalgebra.Basic
public import Mathlib.Algebra.MonoidAlgebra.Basic
public import Mathlib.Topology.Algebra.IsUniformGroup.Constructions
public import Mathlib.Topology.Algebra.OpenSubgroup
public import Mathlib.Topology.Algebra.Ring.Basic
public import TauCeti.Algebra.MonoidAlgebra.Basic
public import TauCeti.GroupTheory.QuotientGroup.Map
public import TauCeti.Topology.Algebra.Group.Profinite.Basic

/-!
# The completed group algebra of a profinite group

For a topological group `Γ` and a commutative ring `R`, the **completed group algebra**
`R[[Γ]]` is the inverse limit of the group algebras `R[Γ ⧸ U]`
over the open normal subgroups `U` of `Γ`: an element is a family of elements of the group
algebras `R[Γ ⧸ U]`, compatible along the ring homomorphisms `R[Γ ⧸ U] → R[Γ ⧸ V]` induced by
the quotient maps `Γ ⧸ U → Γ ⧸ V` for `U ≤ V`. The index set is the open *normal* subgroups,
because `Γ ⧸ U` has to be a group for `R[Γ ⧸ U]` to be a group algebra. For `R = ℤ_[p]` and
`Γ` a profinite group this is the Iwasawa algebra `ℤ_p[[Γ]]`, the ring over which the relation
modules in Labute's classification of Demushkin groups are studied.

It is an `R`-algebra; each group element `γ` gives an element `of R Γ γ`, the family of its
classes, and each open normal subgroup `U` gives the projection `proj R Γ U` onto `R[Γ ⧸ U]`,
which is surjective. Two elements with the same projections are equal, and these two facts are
the inverse-limit description of the algebra. Its universal property is `lift`: a compatible
family of `R`-algebra homomorphisms into the levels `R[Γ ⧸ U]` assembles into an `R`-algebra
homomorphism into `R[[Γ]]`, unique with the prescribed projections (`algHom_ext`).

When `R` is a topological ring, the completed group algebra carries the inverse-limit topology:
the coarsest topology making every coefficient of every projection continuous. Scalar
multiplication by `R` is continuous when multiplication in `R` is. When every open normal
quotient `Γ ⧸ U` is finite, as it is for a compact `Γ` with separately continuous
multiplication, the completed algebra is a topological ring, and it is compact when `R` is
compact Hausdorff. It is totally disconnected when `R` is, and the map from `Γ` is continuous.
It is commutative when `Γ` is, stated as the `IsMulCommutative` mixin and as a `CommRing`
structure extending the ring structure, so that no second multiplication is installed.

For a general topological group `Γ` the map `of R Γ` need not be injective and the algebra may be
commutative without `Γ` being so (both happen for an indiscrete `Γ`, whose only open normal
subgroup is `Γ` itself). When `Γ` is profinite its open normal subgroups separate the points, so
over a nontrivial `R` the group elements are distinct in `R[[Γ]]` (`of_injective`), the map
`of R Γ` is a closed embedding for Hausdorff `R` (`isClosedEmbedding_of`), and the algebra is
commutative exactly when `Γ` is (`isMulCommutative_iff`).

## Main definitions

* `TauCeti.completedGroupAlgebra R Γ`: the completed group algebra `R[[Γ]]`.
* `TauCeti.completedGroupAlgebra.proj R Γ U`: the projection onto `R[Γ ⧸ U]`.
* `TauCeti.completedGroupAlgebra.of R Γ`: the group elements inside `R[[Γ]]`.
* `TauCeti.completedGroupAlgebra.mk`: an element from a compatible family of elements
  of the group algebras `R[Γ ⧸ U]`.
* `TauCeti.completedGroupAlgebra.lift`: the `R`-algebra homomorphism into `R[[Γ]]` assembled
  from a compatible family of `R`-algebra homomorphisms into the group algebras `R[Γ ⧸ U]`.
* `TauCeti.completedGroupAlgebra.coeffFamily R Γ`: all coefficients of all projections, the map
  along which the topology is induced.

## Main results

* `TauCeti.completedGroupAlgebra.ext`, `TauCeti.completedGroupAlgebra.proj_surjective`: the
  inverse-limit description.
* `TauCeti.completedGroupAlgebra.proj_lift`, `TauCeti.completedGroupAlgebra.algHom_ext`: the
  universal property, an algebra homomorphism into `R[[Γ]]` is determined by its compositions
  with the projections and `lift` has the prescribed ones.
* `TauCeti.completedGroupAlgebra.proj_of`: a group element projects to the corresponding basis
  element of the quotient group algebra.
* `TauCeti.completedGroupAlgebra.isEmbedding_coeffFamily`,
  `TauCeti.completedGroupAlgebra.isClosedEmbedding_coeffFamily`: the topology is the
  inverse-limit topology, and the compatible families form a closed subset of the product.
* `TauCeti.completedGroupAlgebra.continuous_of`: the group elements depend continuously on the
  group element.
* `TauCeti.completedGroupAlgebra.exists_mem_span_range_of_proj_eq`,
  `TauCeti.completedGroupAlgebra.dense_span_range_of`: every element agrees at any given level
  with an `R`-linear combination of group elements, so the span of the group elements is dense.
* `TauCeti.completedGroupAlgebra.isUniformInducing_coeffFamily`: over a uniform coefficient ring,
  the uniformity of the completed group algebra is the one induced along the coefficient map,
  and the algebra is a uniform additive group when `R` is.
* `TauCeti.completedGroupAlgebra.of_injective`,
  `TauCeti.completedGroupAlgebra.isClosedEmbedding_of`,
  `TauCeti.completedGroupAlgebra.isMulCommutative_iff`: for profinite `Γ` over a nontrivial `R`,
  the group elements are distinct, form a closed copy of `Γ` when `R` is Hausdorff, and the
  algebra is commutative exactly when `Γ` is.
* The instances `IsTopologicalRing`, `ContinuousSMul R`, `CompactSpace`,
  `TotallyDisconnectedSpace`, `T2Space`, `UniformSpace` and `IsUniformAddGroup`, and the
  `IsMulCommutative` and `CommRing` instances for commutative `Γ`.

## References

* L. Ribes and P. Zalesskii, *Profinite Groups*, Section 5.3.
* J. P. Labute, *Classification of Demushkin groups*, Canad. J. Math. 19 (1967), Section 1.5.
-/

public section

namespace TauCeti

open Topology

universe u v

variable (R : Type u) [CommRing R] (Γ : Type v) [Group Γ] [TopologicalSpace Γ]

namespace completedGroupAlgebra

/-- The families of elements of the group algebras `R[Γ ⧸ U]`, `U` ranging over the open normal
subgroups of `Γ`, that are compatible along the maps induced by the quotient maps `Γ ⧸ U → Γ ⧸ V`
for `U ≤ V`, as a subalgebra of the product of the `R[Γ ⧸ U]`. This is the implementation of
`completedGroupAlgebra`; it is private, and the public interface is `proj`, `mk` and `ext`. -/
private def subalgebra :
    Subalgebra R (∀ U : OpenNormalSubgroup Γ, MonoidAlgebra R (Γ ⧸ U.toSubgroup)) where
  carrier := {x | ∀ ⦃U V : OpenNormalSubgroup Γ⦄ (hUV : U ≤ V),
    MonoidAlgebra.mapDomain (QuotientGroup.mapOfLE hUV) (x U) = x V}
  mul_mem' {x y} hx hy _ _ hUV := by
    rw [Pi.mul_apply, Pi.mul_apply, MonoidAlgebra.mapDomain_mul, hx hUV, hy hUV]
  one_mem' _ _ hUV := by
    rw [Pi.one_apply, Pi.one_apply, MonoidAlgebra.mapDomain_one]
  add_mem' {x y} hx hy _ _ hUV := by
    rw [Pi.add_apply, Pi.add_apply, MonoidAlgebra.mapDomain_add, hx hUV, hy hUV]
  zero_mem' _ _ hUV := by
    rw [Pi.zero_apply, Pi.zero_apply, MonoidAlgebra.mapDomain_zero]
  algebraMap_mem' r _ _ hUV := by
    rw [Pi.algebraMap_apply, Pi.algebraMap_apply, Algebra.algebraMap_eq_smul_one,
      Algebra.algebraMap_eq_smul_one, MonoidAlgebra.mapDomain_smul, MonoidAlgebra.mapDomain_one]

end completedGroupAlgebra

/-- The **completed group algebra** `R[[Γ]]` of a topological group `Γ` over a commutative
ring `R`: the inverse limit of the group algebras `R[Γ ⧸ U]` over the open normal subgroups `U`
of `Γ`, along the maps induced by the quotient maps. For `R = ℤ_[p]` and `Γ` profinite this is
the Iwasawa algebra `ℤ_p[[Γ]]`.

Its elements are accessed through the projections `completedGroupAlgebra.proj R Γ U` onto the
levels `R[Γ ⧸ U]`, which determine them (`completedGroupAlgebra.ext`), and constructed from
compatible families of elements of the levels by `completedGroupAlgebra.mk`. The representation
as a subalgebra of the product of the levels is private to this file and is not part of the
public interface. -/
def completedGroupAlgebra : Type (max u v) := completedGroupAlgebra.subalgebra R Γ

namespace completedGroupAlgebra

/-! The ring and algebra structures are transported from the private subalgebra; the instances
are `@[no_expose]`, which is what lets their bodies name the private constant. -/

@[no_expose] noncomputable instance : Ring (completedGroupAlgebra R Γ) :=
  inferInstanceAs (Ring (subalgebra R Γ))

@[no_expose] noncomputable instance : Algebra R (completedGroupAlgebra R Γ) :=
  inferInstanceAs (Algebra R (subalgebra R Γ))

/-- The projection of the completed group algebra onto the group algebra `R[Γ ⧸ U]` of the
quotient by the open normal subgroup `U`, as an `R`-algebra homomorphism. It is
surjective (`proj_surjective`), and the projections jointly determine an element (`ext`). -/
noncomputable def proj (U : OpenNormalSubgroup Γ) :
    completedGroupAlgebra R Γ →ₐ[R] MonoidAlgebra R (Γ ⧸ U.toSubgroup) :=
  (Pi.evalAlgHom R (fun U : OpenNormalSubgroup Γ ↦ MonoidAlgebra R (Γ ⧸ U.toSubgroup)) U).comp
    (subalgebra R Γ).val

variable {R Γ}

/-- The projections at `U ≤ V` are compatible along the ring homomorphism
`R[Γ ⧸ U] → R[Γ ⧸ V]` induced by the quotient map. -/
@[simp]
theorem mapDomain_mapOfLE_proj {U V : OpenNormalSubgroup Γ} (hUV : U ≤ V)
    (x : completedGroupAlgebra R Γ) :
    MonoidAlgebra.mapDomain (QuotientGroup.mapOfLE hUV) (proj R Γ U x) = proj R Γ V x :=
  x.2 hUV

/-- Two elements of the completed group algebra with the same projections at every
level are equal. -/
@[ext]
theorem ext {x y : completedGroupAlgebra R Γ} (h : ∀ U, proj R Γ U x = proj R Γ U y) : x = y :=
  Subtype.ext (funext h)

variable (R Γ)

/-- The element of the completed group algebra with a prescribed compatible family of
projections onto the levels `R[Γ ⧸ U]`. -/
noncomputable def mk (x : ∀ U : OpenNormalSubgroup Γ, MonoidAlgebra R (Γ ⧸ U.toSubgroup))
    (hx : ∀ ⦃U V : OpenNormalSubgroup Γ⦄ (hUV : U ≤ V),
      MonoidAlgebra.mapDomain (QuotientGroup.mapOfLE hUV) (x U) = x V) :
    completedGroupAlgebra R Γ :=
  ⟨x, hx⟩

/-- The projections of `mk x hx` are the prescribed family `x`. -/
@[simp]
theorem proj_mk (x : ∀ U : OpenNormalSubgroup Γ, MonoidAlgebra R (Γ ⧸ U.toSubgroup))
    (hx : ∀ ⦃U V : OpenNormalSubgroup Γ⦄ (hUV : U ≤ V),
      MonoidAlgebra.mapDomain (QuotientGroup.mapOfLE hUV) (x U) = x V)
    (U : OpenNormalSubgroup Γ) :
    proj R Γ U (mk R Γ x hx) = x U :=
  (rfl)

section Lift

variable {A : Type*} [Semiring A] [Algebra R A]

/-- The universal property of the completed group algebra: a family of `R`-algebra
homomorphisms `f U : A →ₐ[R] R[Γ ⧸ U]`, compatible along the maps induced by the quotient maps
`Γ ⧸ U → Γ ⧸ V` for `U ≤ V`, assembles into an `R`-algebra homomorphism `A →ₐ[R] R[[Γ]]`
whose projection at `U` is `f U` (`proj_lift`). It is the unique such homomorphism
(`algHom_ext`). -/
noncomputable def lift (f : ∀ U : OpenNormalSubgroup Γ, A →ₐ[R] MonoidAlgebra R (Γ ⧸ U.toSubgroup))
    (hf : ∀ ⦃U V : OpenNormalSubgroup Γ⦄ (hUV : U ≤ V) (a : A),
      MonoidAlgebra.mapDomain (QuotientGroup.mapOfLE hUV) (f U a) = f V a) :
    A →ₐ[R] completedGroupAlgebra R Γ where
  toFun a := mk R Γ (fun U ↦ f U a) fun _ _ hUV ↦ hf hUV a
  map_one' := ext fun U ↦ by simp
  map_mul' a b := ext fun U ↦ by simp
  map_zero' := ext fun U ↦ by simp
  map_add' a b := ext fun U ↦ by simp
  commutes' r := ext fun U ↦ by simp

/-- The projection of the lift of a compatible family `f` at `U` is `f U`. -/
@[simp]
theorem proj_lift (f : ∀ U : OpenNormalSubgroup Γ, A →ₐ[R] MonoidAlgebra R (Γ ⧸ U.toSubgroup))
    (hf : ∀ ⦃U V : OpenNormalSubgroup Γ⦄ (hUV : U ≤ V) (a : A),
      MonoidAlgebra.mapDomain (QuotientGroup.mapOfLE hUV) (f U a) = f V a)
    (U : OpenNormalSubgroup Γ) (a : A) :
    proj R Γ U (lift R Γ f hf a) = f U a :=
  (rfl)

/-- The lift of a compatible family `f` composed with the projection at `U` is `f U`. -/
@[simp]
theorem proj_comp_lift
    (f : ∀ U : OpenNormalSubgroup Γ, A →ₐ[R] MonoidAlgebra R (Γ ⧸ U.toSubgroup))
    (hf : ∀ ⦃U V : OpenNormalSubgroup Γ⦄ (hUV : U ≤ V) (a : A),
      MonoidAlgebra.mapDomain (QuotientGroup.mapOfLE hUV) (f U a) = f V a)
    (U : OpenNormalSubgroup Γ) :
    (proj R Γ U).comp (lift R Γ f hf) = f U :=
  AlgHom.ext fun a ↦ proj_lift R Γ f hf U a

variable {R Γ} in
/-- Two `R`-algebra homomorphisms into the completed group algebra with the same compositions
with every projection are equal; this is the uniqueness half of the universal property. -/
theorem algHom_ext {g₁ g₂ : A →ₐ[R] completedGroupAlgebra R Γ}
    (h : ∀ U, (proj R Γ U).comp g₁ = (proj R Γ U).comp g₂) : g₁ = g₂ :=
  AlgHom.ext fun a ↦ ext fun U ↦ AlgHom.congr_fun (h U) a

end Lift

/-- The group elements inside the completed group algebra: `γ` goes to the family of the basis
elements at its classes in the quotients `Γ ⧸ U`. This is the analogue of `MonoidAlgebra.of`;
its values are units, as it is a homomorphism from a group. -/
noncomputable def of : Γ →* completedGroupAlgebra R Γ where
  toFun γ := mk R Γ (fun U ↦ MonoidAlgebra.of R (Γ ⧸ U.toSubgroup) (γ : Γ ⧸ U.toSubgroup))
    fun _ _ _ ↦ by simp
  map_one' := ext fun U ↦ by simp [← MonoidAlgebra.one_def]
  map_mul' γ δ := ext fun U ↦ by simp

/-- A group element projects to the basis element of `R[Γ ⧸ U]` at its class. -/
@[simp]
theorem proj_of (U : OpenNormalSubgroup Γ) (γ : Γ) :
    proj R Γ U (of R Γ γ) = MonoidAlgebra.single (γ : Γ ⧸ U.toSubgroup) 1 := by
  simp [of]

/-- Every projection is surjective. -/
theorem proj_surjective (U : OpenNormalSubgroup Γ) : Function.Surjective (proj R Γ U) := by
  intro y
  induction y using MonoidAlgebra.induction_on with
  | of m =>
    obtain ⟨γ, rfl⟩ := QuotientGroup.mk_surjective m
    exact ⟨of R Γ γ, by simp⟩
  | add x y hx hy =>
    obtain ⟨x', rfl⟩ := hx
    obtain ⟨y', rfl⟩ := hy
    exact ⟨x' + y', map_add _ _ _⟩
  | smul r x hx =>
    obtain ⟨x', rfl⟩ := hx
    exact ⟨r • x', map_smul _ _ _⟩

/-- Every element of the completed group algebra agrees at any given level `V` with a finite
`R`-linear combination of group elements. -/
theorem exists_mem_span_range_of_proj_eq (x : completedGroupAlgebra R Γ)
    (V : OpenNormalSubgroup Γ) :
    ∃ y ∈ Submodule.span R (Set.range (of R Γ)), proj R Γ V y = proj R Γ V x := by
  refine ⟨(proj R Γ V x).coeff.sum fun q c ↦ c • of R Γ (Quotient.out q), ?_, ?_⟩
  · exact Submodule.sum_mem _ fun q _ ↦ Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, rfl⟩)
  · rw [map_finsuppSum]
    simp only [map_smul, proj_of, QuotientGroup.out_eq', MonoidAlgebra.smul_single', mul_one]
    exact MonoidAlgebra.sum_coeff_single _

instance [Nontrivial R] : Nontrivial (completedGroupAlgebra R Γ) :=
  (proj R Γ { toOpenSubgroup := ⟨⊤, isOpen_univ⟩ }).toRingHom.domain_nontrivial

/-- The completed group algebra of a commutative group is commutative. -/
instance [IsMulCommutative Γ] : IsMulCommutative (completedGroupAlgebra R Γ) where
  is_comm.comm x y := ext fun U ↦ by
    have : IsMulCommutative (Γ ⧸ U.toSubgroup) :=
      (QuotientGroup.mk'_surjective U.toSubgroup).isMulCommutative inferInstance
    rw [map_mul, map_mul, (isMulCommutative_iff.mp inferInstance) (proj R Γ U x)]

/-- The completed group algebra of a commutative group, as a commutative ring: the bundled form of
the `IsMulCommutative` instance, obtained from Mathlib's scoped construction. The ring structure is
the existing one, so this installs no second multiplication. -/
noncomputable instance [IsMulCommutative Γ] : CommRing (completedGroupAlgebra R Γ) :=
  open scoped IsMulCommutative in inferInstance

section Profinite

variable [IsTopologicalGroup Γ] [CompactSpace Γ] [TotallyDisconnectedSpace Γ] [Nontrivial R]

/-- Over a nontrivial coefficient ring, distinct elements of a profinite group are distinct
inside its completed group algebra: the open normal subgroups separate the points. -/
theorem of_injective : Function.Injective (of R Γ) := fun γ δ h ↦ by
  rw [← inv_mul_eq_one]
  refine Subgroup.eq_one_of_mem_iInf_openNormalSubgroup fun U ↦ QuotientGroup.eq.mp ?_
  have := congrArg (proj R Γ U) h
  rwa [proj_of, proj_of, MonoidAlgebra.single_left_inj one_ne_zero] at this

/-- Over a nontrivial coefficient ring, the completed group algebra of a profinite group is
commutative exactly when the group is. -/
theorem isMulCommutative_iff : IsMulCommutative (completedGroupAlgebra R Γ) ↔ IsMulCommutative Γ :=
  ⟨fun h ↦ ⟨⟨fun γ δ ↦ of_injective R Γ (by rw [map_mul, map_mul, h.is_comm.comm])⟩⟩,
    fun _ ↦ inferInstance⟩

end Profinite

/-- The coefficient of a product at a class `g` of a finite quotient is the sum, over the classes
`h` of that quotient, of the products of the coefficients of the factors at `h` and `h⁻¹ * g`. -/
theorem coeff_proj_mul (x y : completedGroupAlgebra R Γ) (U : OpenNormalSubgroup Γ)
    [Fintype (Γ ⧸ U.toSubgroup)] (g : Γ ⧸ U.toSubgroup) :
    (proj R Γ U (x * y)).coeff g =
      ∑ h : Γ ⧸ U.toSubgroup, (proj R Γ U x).coeff h * (proj R Γ U y).coeff (h⁻¹ * g) := by
  rw [map_mul, MonoidAlgebra.coeff_mul_apply_left, Finsupp.sum_fintype]
  intro
  simp

/-! ### The inverse-limit topology -/

/-- All coefficients of all projections, as one additive map into a product of
copies of `R`. The topology of the completed group algebra is the one induced along this map:
the coarsest topology making every coefficient of every projection continuous. -/
noncomputable def coeffFamily :
    completedGroupAlgebra R Γ →+ ∀ U : OpenNormalSubgroup Γ, Γ ⧸ U.toSubgroup → R where
  toFun x U := ⇑(proj R Γ U x).coeff
  map_zero' := funext fun U ↦ by simp
  map_add' x y := funext fun U ↦ by
    simp only [Pi.add_apply, map_add, MonoidAlgebra.coeff_add, Finsupp.coe_add]

/-- The coefficients of an element at a quotient are those of its projection. -/
@[simp]
theorem coeffFamily_apply (x : completedGroupAlgebra R Γ) (U : OpenNormalSubgroup Γ) :
    coeffFamily R Γ x U = ⇑(proj R Γ U x).coeff :=
  (rfl)

/-- An element is determined by the coefficients of its projections. -/
theorem coeffFamily_injective : Function.Injective (coeffFamily R Γ) := fun _ _ h ↦
  ext fun U ↦ MonoidAlgebra.coeff_injective (DFunLike.coe_injective (congrFun h U))

section TopologicalSpace

variable [TopologicalSpace R]

/-- The inverse-limit topology on the completed group algebra: the topology induced along the
coefficient map `coeffFamily R Γ` into the product of copies of `R`. -/
noncomputable instance : TopologicalSpace (completedGroupAlgebra R Γ) :=
  .induced (coeffFamily R Γ) inferInstance

/-- The topology of the completed group algebra is induced along the coefficient map. -/
theorem isInducing_coeffFamily : IsInducing (coeffFamily R Γ) := ⟨rfl⟩

/-- The completed group algebra embeds topologically into the product, over the open normal
subgroups `U` and the elements of `Γ ⧸ U`, of copies of `R`. -/
theorem isEmbedding_coeffFamily : IsEmbedding (coeffFamily R Γ) :=
  ⟨isInducing_coeffFamily R Γ, coeffFamily_injective R Γ⟩

/-- Every coefficient of every projection is continuous. -/
theorem continuous_coeff_proj (U : OpenNormalSubgroup Γ) (g : Γ ⧸ U.toSubgroup) :
    Continuous fun x : completedGroupAlgebra R Γ ↦ (proj R Γ U x).coeff g :=
  (continuous_apply g).comp ((continuous_apply U).comp (isInducing_coeffFamily R Γ).continuous)

variable {R Γ} in
/-- A map into the completed group algebra is continuous exactly when every coefficient of every
projection of its values is. -/
theorem continuous_iff {X : Type*} [TopologicalSpace X] {f : X → completedGroupAlgebra R Γ} :
    Continuous f ↔ ∀ (U : OpenNormalSubgroup Γ) (g : Γ ⧸ U.toSubgroup),
      Continuous fun x ↦ (proj R Γ U (f x)).coeff g :=
  (isInducing_coeffFamily R Γ).continuous_iff.trans <| by
    simp only [continuous_pi_iff]
    exact Iff.rfl

instance [T2Space R] : T2Space (completedGroupAlgebra R Γ) :=
  (isEmbedding_coeffFamily R Γ).t2Space

instance [TotallyDisconnectedSpace R] : TotallyDisconnectedSpace (completedGroupAlgebra R Γ) :=
  ⟨(isEmbedding_coeffFamily R Γ).isTotallyDisconnected
    (isTotallyDisconnected_of_totallyDisconnectedSpace _)⟩

instance [IsTopologicalAddGroup R] : IsTopologicalAddGroup (completedGroupAlgebra R Γ) :=
  (isInducing_coeffFamily R Γ).isTopologicalAddGroup (coeffFamily R Γ)

/-- Scalar multiplication by the coefficient ring is continuous: it multiplies every coefficient
of every projection by the scalar. -/
instance [ContinuousMul R] : ContinuousSMul R (completedGroupAlgebra R Γ) where
  continuous_smul := by
    refine continuous_iff.mpr fun U g ↦ ?_
    simp only [map_smul, MonoidAlgebra.coeff_smul_apply, smul_eq_mul]
    exact continuous_fst.mul ((continuous_coeff_proj R Γ U g).comp continuous_snd)

/-- The group elements of the completed group algebra depend continuously on the group
element. -/
theorem continuous_of [SeparatelyContinuousMul Γ] : Continuous (of R Γ) := by
  refine continuous_iff.mpr fun U g ↦ ?_
  simp only [proj_of]
  exact (continuous_of_discreteTopology
    (f := fun q : Γ ⧸ U.toSubgroup ↦ (MonoidAlgebra.single q (1 : R)).coeff g)).comp
    (QuotientGroup.continuous_mk (N := U.toSubgroup))

/-! ### Density of the group elements -/

/-- **The group elements span a dense subspace.** The `R`-span of the group elements is dense in
the completed group algebra. -/
theorem dense_span_range_of :
    Dense (Submodule.span R (Set.range (of R Γ)) : Set (completedGroupAlgebra R Γ)) := by
  classical
  refine (isInducing_coeffFamily R Γ).dense_iff.mpr fun x ↦ mem_closure_iff_nhds.mpr fun t ht ↦ ?_
  rw [nhds_pi, Filter.mem_pi'] at ht
  obtain ⟨I, s, hs, hst⟩ := ht
  -- A level `V` below every level in the finite set `I`.
  obtain ⟨V, hV⟩ : ∃ V : OpenNormalSubgroup Γ, ∀ U ∈ I, V ≤ U := by
    clear hst
    induction I using Finset.induction_on with
    | empty => exact ⟨openNormalSubgroupTop Γ, by simp⟩
    | insert U I _ ih =>
      obtain ⟨V, hV⟩ := ih
      exact ⟨V ⊓ U, by
        simp only [Finset.mem_insert, forall_eq_or_imp]
        exact ⟨inf_le_right, fun W hW ↦ inf_le_left.trans (hV W hW)⟩⟩
  obtain ⟨y, hy, hyx⟩ := exists_mem_span_range_of_proj_eq R Γ x V
  refine ⟨coeffFamily R Γ y, hst fun U hU ↦ ?_, Set.mem_image_of_mem _ hy⟩
  have : proj R Γ U y = proj R Γ U x := by
    rw [← mapDomain_mapOfLE_proj (hV U hU) y, hyx, mapDomain_mapOfLE_proj]
  rw [coeffFamily_apply, this, ← coeffFamily_apply]
  exact mem_of_mem_nhds (hs U)

section FiniteQuotients

/-! The results of this section assume that every open normal quotient `Γ ⧸ U` is finite, so
that each coefficient of a product at `U` is a finite sum of products of coefficients
(`coeff_proj_mul`). For a compact `Γ` with separately continuous multiplication this hypothesis
is Mathlib's instance `Finite (Γ ⧸ U.toSubgroup)` for open subgroups `U`, so the instances
below apply to compact groups without further assumptions. -/

variable [∀ U : OpenNormalSubgroup Γ, Finite (Γ ⧸ U.toSubgroup)]

/-- When every open normal quotient of `Γ` is finite, multiplication in the completed group
algebra is continuous: each coefficient of a product is a finite sum of products of
coefficients. -/
instance [IsTopologicalSemiring R] : ContinuousMul (completedGroupAlgebra R Γ) where
  continuous_mul := by
    refine continuous_iff.mpr fun U g ↦ ?_
    let _ := Fintype.ofFinite (Γ ⧸ U.toSubgroup)
    simp only [coeff_proj_mul]
    exact continuous_finsetSum _ fun h _ ↦
      ((continuous_coeff_proj R Γ U h).comp continuous_fst).mul
        ((continuous_coeff_proj R Γ U _).comp continuous_snd)

/-- When every open normal quotient of `Γ` is finite, the completed group algebra over a
topological ring is a topological ring. -/
instance [IsTopologicalRing R] : IsTopologicalRing (completedGroupAlgebra R Γ) where

/-- The compatible coefficient families form a closed subset of the product of copies of `R`,
so the completed group algebra is a closed embedding into it. -/
theorem isClosedEmbedding_coeffFamily [T2Space R] [ContinuousAdd R] :
    IsClosedEmbedding (coeffFamily R Γ) := by
  refine ⟨isEmbedding_coeffFamily R Γ, ?_⟩
  classical
  -- The range is the set of families whose level `V` is the image of their level `U` under the
  -- map induced by the quotient map, for every `U ≤ V`.
  have hrange : Set.range (coeffFamily R Γ) =
      ⋂ (U : OpenNormalSubgroup Γ) (V : OpenNormalSubgroup Γ) (hUV : U ≤ V),
        {f | ⇑(Finsupp.mapDomain (QuotientGroup.mapOfLE hUV)
          (Finsupp.equivFunOnFinite.symm (f U))) = f V} := by
    ext f
    simp only [Set.mem_range, Set.mem_iInter, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨x, rfl⟩ U V hUV
      rw [coeffFamily_apply, coeffFamily_apply, Finsupp.equivFunOnFinite_symm_coe,
        ← MonoidAlgebra.coeff_mapDomain, mapDomain_mapOfLE_proj]
    · intro hf
      refine ⟨mk R Γ (fun U ↦ .ofCoeff (Finsupp.equivFunOnFinite.symm (f U))) fun U V hUV ↦ ?_,
        funext fun U ↦ ?_⟩
      · apply MonoidAlgebra.coeff_injective
        rw [MonoidAlgebra.coeff_mapDomain, MonoidAlgebra.coeff_ofCoeff,
          MonoidAlgebra.coeff_ofCoeff]
        exact DFunLike.coe_injective
          ((hf U V hUV).trans (Finsupp.coe_equivFunOnFinite_symm _).symm)
      · rw [coeffFamily_apply, proj_mk, MonoidAlgebra.coeff_ofCoeff,
          Finsupp.coe_equivFunOnFinite_symm]
  rw [hrange]
  refine isClosed_iInter fun U ↦ isClosed_iInter fun V ↦ isClosed_iInter fun hUV ↦ ?_
  let _ := Fintype.ofFinite (Γ ⧸ U.toSubgroup)
  refine isClosed_eq (continuous_pi fun b ↦ ?_) (continuous_apply V)
  -- Each coefficient of the image is the finite sum of the coefficients over the fibre.
  simp only [Finsupp.equivFunOnFinite_symm_eq_sum, Finsupp.mapDomain_finsetSum,
    Finsupp.mapDomain_single, Finsupp.finsetSum_apply, Finsupp.single_apply]
  exact continuous_finsetSum _ fun a _ ↦ by
    split_ifs
    · exact (continuous_apply a).comp (continuous_apply U)
    · exact continuous_const

/-- When every open normal quotient of `Γ` is finite, the completed group algebra over a
compact Hausdorff ring with continuous addition is compact. -/
instance [T2Space R] [CompactSpace R] [ContinuousAdd R] :
    CompactSpace (completedGroupAlgebra R Γ) :=
  (isClosedEmbedding_coeffFamily R Γ).compactSpace

end FiniteQuotients

/-- Over a nontrivial Hausdorff coefficient ring, the group elements of a profinite group form a
closed subset of the completed group algebra homeomorphic to the group. -/
theorem isClosedEmbedding_of [IsTopologicalGroup Γ] [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    [Nontrivial R] [T2Space R] : IsClosedEmbedding (of R Γ) :=
  (continuous_of R Γ).isClosedEmbedding (of_injective R Γ)

end TopologicalSpace

section UniformSpace

/-! ### The inverse-limit uniformity -/

variable [UniformSpace R]

/-- The inverse-limit uniformity on the completed group algebra: the uniformity induced along the
coefficient map `coeffFamily R Γ` into the product of copies of `R`. Its topology is the
inverse-limit topology. -/
noncomputable instance : UniformSpace (completedGroupAlgebra R Γ) :=
  (UniformSpace.comap (coeffFamily R Γ) inferInstance).replaceTopology rfl

/-- The uniformity of the completed group algebra is induced along the coefficient map. -/
theorem isUniformInducing_coeffFamily : IsUniformInducing (coeffFamily R Γ) := ⟨rfl⟩

/-- The coefficient map is a uniform embedding of the completed group algebra into the product,
over the open normal subgroups `U` and the elements of `Γ ⧸ U`, of copies of `R`. -/
theorem isUniformEmbedding_coeffFamily : IsUniformEmbedding (coeffFamily R Γ) :=
  ⟨isUniformInducing_coeffFamily R Γ, coeffFamily_injective R Γ⟩

instance [IsUniformAddGroup R] : IsUniformAddGroup (completedGroupAlgebra R Γ) :=
  (isUniformInducing_coeffFamily R Γ).isUniformAddGroup (coeffFamily R Γ)

end UniformSpace

end completedGroupAlgebra

end TauCeti
