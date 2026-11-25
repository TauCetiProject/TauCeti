/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.DeRham.HomologyPeriod
public import TauCeti.Geometry.Manifold.Morse.CWModel
public import TauCeti.AlgebraicTopology.Cellular.EulerCharacteristic.FiniteCWType
public import TauCeti.LinearAlgebra.Dual.Lemmas

/-!
# Period coordinates on the first de Rham cohomology

A de Rham class `x ∈ H¹_dR(M)` is determined by its periods `⟨x, c⟩` on the classes
`c ∈ H₁(M; ℤ)` of the first integral singular homology group
(`TauCeti.deRhamCohomology.homologyPeriod_injective`). This file turns this into finite
coordinates.

For a family `c : ι → H₁(M; ℤ)` of classes, the periods on it form a linear map
`H¹_dR(M) → ℝ^ι` (`TauCeti.deRhamCohomology.homologyPeriods`). When the `c i` generate
`H₁(M; ℤ)`, it is injective. So if `H₁(M; ℤ)` is finitely generated, then `H¹_dR(M)` is
finite-dimensional. This is the case for every compact boundaryless manifold, which has the
homotopy type of a finite CW complex (`TauCeti.FiniteCWType.of_isManifold`, from a Morse
function).

When `H¹_dR(M)` is finite-dimensional, of dimension `b`, there are integral classes
`c₁, …, c_b ∈ H₁(M; ℤ)` (`TauCeti.deRhamCohomology.periodHomologyClass`) on which the periods
are coordinates: `x ↦ (⟨x, c₁⟩, …, ⟨x, c_b⟩)` is a linear isomorphism `H¹_dR(M) ≃ ℝ^b`
(`TauCeti.deRhamCohomology.homologyPeriods_periodHomologyClass_bijective`). Its inverse sends
the standard basis to the **period-dual basis** `θ₁, …, θ_b` of `H¹_dR(M)`
(`TauCeti.deRhamCohomology.periodDualBasis`), characterized by `⟨θ_i, c_j⟩ = δ_ij`.
The classes `c_j` are chosen among all integral classes: the periods on all of `H₁(M; ℤ)` have
no common zero but `0`, and `b` of them form coordinates
(`Module.Dual.exists_bijective_pi_of_iInf_ker_eq_bot`).

On closed forms, the **class coordinates** `α ↦ (∫_{c₁} α, …, ∫_{c_b} α)`
(`TauCeti.deRhamCohomology.classCoordinates`) form a surjective linear map onto `ℝ^b` whose kernel
is the space of exact forms. With closed representatives `θ_i` of the period-dual basis
(`TauCeti.deRhamCohomology.periodDualForm`), every closed form is

`α = Σ_i (∫_{c_i} α) θ_i + (an exact form)`

(`TauCeti.deRhamCohomology.sub_sum_classCoordinates_smul_periodDualForm_mem_exactForms`).
These are the finite coordinates in which the flux of a symplectic isotopy, a class in
`H¹_dR(M)`, is written, and the `θ_i` are the closed one-forms whose symplectic duals generate the
corresponding finitely many symplectic flows.

## Main declarations

* `TauCeti.deRhamCohomology.homologyPeriods c`: the periods on a family `c` of classes of
  `H₁(M; ℤ)`, as a linear map `H¹_dR(M) → ℝ^ι`.
* `TauCeti.deRhamCohomology.homologyPeriods_injective`: it is injective when the family generates
  `H₁(M; ℤ)`.
* `TauCeti.deRhamCohomology.finiteDimensional_of_addGroupFG`: if `H₁(M; ℤ)` is finitely
  generated, then `H¹_dR(M)` is finite-dimensional.
* `TauCeti.addGroupFG_homology_one`: `H₁(M; ℤ)` is finitely generated for a compact boundaryless
  manifold.
* The instance `FiniteDimensional ℝ (deRhamCohomology I M 1)` for a compact boundaryless manifold.
* `TauCeti.deRhamCohomology.periodHomologyClass`, `TauCeti.deRhamCohomology.periodDualBasis`:
  integral classes on which the periods are coordinates, and the dual basis of `H¹_dR(M)`.
* `TauCeti.deRhamCohomology.periodDualForm`: closed representatives of the period-dual basis.
* `TauCeti.deRhamCohomology.classCoordinates`: the coordinates of the class of a closed form.

## References

* M. Farber, *Topology of Closed One-Forms*, Mathematical Surveys and Monographs 108, AMS, 2004,
  Section 1.1 (the homomorphism of periods `H₁(M; ℤ) → ℝ` of a closed one-form).
* D. McDuff and D. Salamon, *Introduction to Symplectic Topology*, 3rd ed., Oxford University
  Press, 2017, Section 10.2 (the flux homomorphism with values in `H¹(M; ℝ)`).
-/

public section

noncomputable section

open Module
open scoped ContDiff Manifold

namespace TauCeti

namespace deRhamCohomology

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} {M : Type} [TopologicalSpace M] [ChartedSpace H M]
  [FiniteDimensional ℝ E] [T2Space M] [IsManifold I ∞ M]

/-! ### Periods on a family of integral classes -/

section Periods

variable {ι : Type*}

variable (I) in
/-- The **periods of a de Rham class on a family `c` of integral classes** of `H₁(M; ℤ)`, as a
linear map `H¹_dR(M) → ℝ^ι`. -/
def homologyPeriods (c : ι → ((singularChains ℤ).obj (.of M)).homology 1) :
    deRhamCohomology I M 1 →ₗ[ℝ] ι → ℝ where
  toFun x i := homologyPeriod x (c i)
  map_add' x y := funext fun i ↦ by simp
  map_smul' a x := funext fun i ↦ by simp

/-- The `i`-th coordinate of `homologyPeriods I c x` is the period of `x` on `c i`. -/
@[simp]
theorem homologyPeriods_apply (c : ι → ((singularChains ℤ).obj (.of M)).homology 1)
    (x : deRhamCohomology I M 1) (i : ι) :
    homologyPeriods I c x i = homologyPeriod x (c i) :=
  (rfl)

/-- **Periods on generators determine the class.** If the classes `c i` generate `H₁(M; ℤ)`, a
de Rham class of degree one is determined by its periods on them. -/
theorem homologyPeriods_injective {c : ι → ((singularChains ℤ).obj (.of M)).homology 1}
    (hc : AddSubgroup.closure (Set.range c) = ⊤) :
    Function.Injective (homologyPeriods I c) := by
  refine (injective_iff_map_eq_zero _).mpr fun x hx ↦ homologyPeriod_injective ?_
  rw [map_zero]
  refine AddMonoidHom.eq_of_eqOn_dense hc ?_
  rintro _ ⟨i, rfl⟩
  exact congrFun hx i

/-- **Finite dimensionality from finite generation.** If the first integral singular homology
group of `M` is finitely generated, the first de Rham cohomology of `M` is finite-dimensional. -/
theorem finiteDimensional_of_addGroupFG
    [AddGroup.FG (((singularChains ℤ).obj (.of M)).homology 1)] :
    FiniteDimensional ℝ (deRhamCohomology I M 1) := by
  obtain ⟨S, hS, hfin⟩ := AddGroup.fg_iff.mp ‹_›
  have : Finite S := hfin.to_subtype
  have hc : AddSubgroup.closure (Set.range (Subtype.val : S → _)) = ⊤ := by
    rwa [Subtype.range_val]
  exact Module.Finite.of_injective _ (homologyPeriods_injective (I := I) hc)

end Periods

/-! ### Compact manifolds -/

section Compact

variable [I.Boundaryless] [CompactSpace M]

variable (I) in
include I in
omit [FiniteDimensional ℝ E] in
/-- **The first integral singular homology group of a compact boundaryless manifold is finitely
generated**, since the manifold has the homotopy type of a finite CW complex. -/
theorem _root_.TauCeti.addGroupFG_homology_one :
    AddGroup.FG (((singularChains ℤ).obj (.of M)).homology 1) := by
  have := FiniteCWType.of_isManifold (I := I) M
  have h := finite_singularHomology_of_finiteCWType (k := ℤ) M (ModuleCat.of ℤ ℤ) 1
  rw [singularHomologyFunctor_obj_obj] at h
  -- `h` uses the `ℤ`-module structure of `ModuleCat ℤ`; the two `ℤ`-module structures agree.
  exact Module.Finite.iff_addGroup_fg.mp (by convert h; exact Subsingleton.elim _ _)

/-- **The first de Rham cohomology of a compact boundaryless manifold is finite-dimensional.**
Its first integral singular homology group is finitely generated
(`TauCeti.addGroupFG_homology_one`). -/
instance : FiniteDimensional ℝ (deRhamCohomology I M 1) :=
  have := addGroupFG_homology_one I (M := M)
  finiteDimensional_of_addGroupFG

end Compact

/-! ### The period-dual basis -/

section PeriodDualBasis

variable [FiniteDimensional ℝ (deRhamCohomology I M 1)]

/-- **Period coordinates.** There are `b = dim H¹_dR(M)` integral classes `c₁, …, c_b` of
`H₁(M; ℤ)` on which the periods are coordinates on `H¹_dR(M)`. -/
theorem exists_bijective_homologyPeriods :
    ∃ c : Fin (finrank ℝ (deRhamCohomology I M 1)) →
        ((singularChains ℤ).obj (.of M)).homology 1,
      Function.Bijective (homologyPeriods I c) := by
  -- The periods on all of `H₁(M; ℤ)` have no common zero but `0`.
  have h : ⨅ c : ((singularChains ℤ).obj (.of M)).homology 1,
      LinearMap.ker (LinearMap.proj c ∘ₗ homologyPeriods I id) = ⊥ := by
    refine eq_bot_iff.mpr fun x hx ↦
      homologyPeriods_injective (I := I) (c := id) (by simp) (funext fun c ↦ ?_)
    simpa using (Submodule.mem_iInf _).mp hx c
  obtain ⟨c, hc⟩ := Dual.exists_bijective_pi_of_iInf_ker_eq_bot _ h
  exact ⟨c, by convert hc using 2; ext; simp⟩

variable (I M) in
/-- **Period classes**: integral classes `c₁, …, c_b` of `H₁(M; ℤ)`, `b = dim H¹_dR(M)`, on
which the periods are coordinates on `H¹_dR(M)`. -/
def periodHomologyClass :
    Fin (finrank ℝ (deRhamCohomology I M 1)) → ((singularChains ℤ).obj (.of M)).homology 1 :=
  (exists_bijective_homologyPeriods (I := I) (M := M)).choose

/-- The periods on the period classes are a linear isomorphism `H¹_dR(M) ≃ ℝ^b`. -/
theorem homologyPeriods_periodHomologyClass_bijective :
    Function.Bijective (homologyPeriods I (periodHomologyClass I M)) :=
  (exists_bijective_homologyPeriods (I := I) (M := M)).choose_spec

variable (I M) in
/-- The **period-dual basis** of `H¹_dR(M)`: the basis `θ₁, …, θ_b` whose periods on the period
classes are `⟨θ_i, c_j⟩ = δ_ij`. Its coordinates are the periods on the period classes
(`TauCeti.deRhamCohomology.periodDualBasis_repr_apply`). -/
def periodDualBasis :
    Basis (Fin (finrank ℝ (deRhamCohomology I M 1))) ℝ (deRhamCohomology I M 1) :=
  .ofEquivFun (.ofBijective _ homologyPeriods_periodHomologyClass_bijective)

/-- The coordinates of a class in the period-dual basis are its periods on the period classes. -/
@[simp]
theorem periodDualBasis_repr_apply (x : deRhamCohomology I M 1)
    (i : Fin (finrank ℝ (deRhamCohomology I M 1))) :
    (periodDualBasis I M).repr x i = homologyPeriod x (periodHomologyClass I M i) :=
  Basis.ofEquivFun_repr_apply _ x i

/-- The period-dual basis is dual to the period classes: `⟨θ_i, c_j⟩ = δ_ij`. -/
@[simp]
theorem homologyPeriod_periodDualBasis_periodHomologyClass
    (i j : Fin (finrank ℝ (deRhamCohomology I M 1))) :
    homologyPeriod (periodDualBasis I M i) (periodHomologyClass I M j) =
      if i = j then 1 else 0 := by
  rw [← periodDualBasis_repr_apply, Basis.repr_self, Finsupp.single_apply]

variable (I M) in
/-- Closed representatives `θ₁, …, θ_b` of the period-dual basis: closed one-forms whose
integrals on the period classes are `∫_{c_j} θ_i = δ_ij`. -/
def periodDualForm (i : Fin (finrank ℝ (deRhamCohomology I M 1))) : closedForms I M 1 :=
  (mk_surjective I 1 (periodDualBasis I M i)).choose

/-- The class of `periodDualForm I M i` is the `i`-th vector of the period-dual basis. -/
@[simp]
theorem mk_periodDualForm (i : Fin (finrank ℝ (deRhamCohomology I M 1))) :
    mk I 1 (periodDualForm I M i) = periodDualBasis I M i :=
  (mk_surjective I 1 (periodDualBasis I M i)).choose_spec

/-- The integrals of the representatives of the period-dual basis on the period classes are
`∫_{c_j} θ_i = δ_ij`. -/
@[simp]
theorem homologyPeriodHom_periodDualForm_periodHomologyClass
    (i j : Fin (finrank ℝ (deRhamCohomology I M 1))) :
    homologyPeriodHom ((periodDualForm I M i).val : RoughForm I M ℝ 1)
        (periodHomologyClass I M j) = if i = j then 1 else 0 := by
  rw [← homologyPeriod_mk, mk_periodDualForm, homologyPeriod_periodDualBasis_periodHomologyClass]

/-! ### Class coordinates of closed forms -/

variable (I M) in
/-- The **class coordinates** of a closed one-form `α`: its integrals
`(∫_{c₁} α, …, ∫_{c_b} α)` on the period classes, the coordinates of its de Rham class in the
period-dual basis. -/
def classCoordinates :
    closedForms I M 1 →ₗ[ℝ] Fin (finrank ℝ (deRhamCohomology I M 1)) → ℝ :=
  (periodDualBasis I M).equivFun.toLinearMap ∘ₗ mk I 1

/-- The class coordinates of a closed form are its integrals on the period classes. -/
@[simp]
theorem classCoordinates_apply (α : closedForms I M 1)
    (i : Fin (finrank ℝ (deRhamCohomology I M 1))) :
    classCoordinates I M α i =
      homologyPeriodHom (α.val : RoughForm I M ℝ 1) (periodHomologyClass I M i) := by
  simp [classCoordinates]

/-- The class coordinates of a closed form are the coordinates of its class in the period-dual
basis. -/
theorem classCoordinates_eq_repr (α : closedForms I M 1) :
    classCoordinates I M α = (periodDualBasis I M).repr (mk I 1 α) := by
  ext i
  simp

/-- The representatives of the period-dual basis have the standard basis vectors as class
coordinates. -/
@[simp]
theorem classCoordinates_periodDualForm (i : Fin (finrank ℝ (deRhamCohomology I M 1))) :
    classCoordinates I M (periodDualForm I M i) = Pi.single i 1 := by
  ext j
  simp [homologyPeriodHom_periodDualForm_periodHomologyClass, Pi.single_apply, eq_comm]

/-- Every vector of `ℝ^b` is the class coordinates of a closed form. -/
theorem classCoordinates_surjective : Function.Surjective (classCoordinates I M) :=
  (periodDualBasis I M).equivFun.surjective.comp (mk_surjective I 1)

/-- **The kernel of the class coordinates.** A closed one-form is exact exactly when its integrals
on the period classes vanish. -/
theorem classCoordinates_eq_zero_iff (α : closedForms I M 1) :
    classCoordinates I M α = 0 ↔ α.val ∈ exactForms I M 1 := by
  rw [← mk_eq_zero_iff, classCoordinates, LinearMap.comp_apply, LinearEquiv.coe_coe,
    LinearEquiv.map_eq_zero_iff]

/-- Two closed one-forms are cohomologous exactly when they have the same class coordinates. -/
theorem classCoordinates_eq_classCoordinates_iff (α β : closedForms I M 1) :
    classCoordinates I M α = classCoordinates I M β ↔ α.val - β.val ∈ exactForms I M 1 := by
  rw [← sub_eq_zero, ← map_sub, classCoordinates_eq_zero_iff, Submodule.coe_sub]

/-- **Decomposition of a closed form.** A closed one-form differs from the combination of the
representatives of the period-dual basis with its class coordinates as coefficients by an exact
form: `α - Σ_i (∫_{c_i} α) θ_i` is exact. -/
theorem sub_sum_classCoordinates_smul_periodDualForm_mem_exactForms (α : closedForms I M 1) :
    α.val - ∑ i, classCoordinates I M α i • (periodDualForm I M i).val ∈ exactForms I M 1 := by
  have h := (classCoordinates_eq_classCoordinates_iff α
    (∑ i, classCoordinates I M α i • periodDualForm I M i)).mp ?_
  · simpa using h
  · simp only [map_sum, map_smul, classCoordinates_periodDualForm]
    ext j
    simp [Pi.single_apply]

end PeriodDualBasis

end deRhamCohomology

end TauCeti
